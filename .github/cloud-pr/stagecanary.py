#!/usr/bin/env python3
"""stagecanary.py (P2c, Lead 20:56 UTC 27 Nov): the opener side of gate-staged PR heads on the real runner.
The w12 gate pushed, in ONE multi-ref push, for each unit i a ready commit stagecanary/<tag>/r<i> (ready/<mod>.lean, the
message with "Staged-Head: <head> <parent> <time> <nonce>") and the staged head stagecanary/<tag>/h<i>. Unit 3's ready
file differs from its head's file (a tamper case). Each unit runs through the real submit() from a cold blobless clone
of upstream main as drain.py makes it; push_branch raises (the staged path must never push) and create_pr is a
recorder (no PR, nothing upstream). Units 1-2 must reach the create with the head rebuilt bit for bit; unit 3 must be
refused. Then a fresh FULL clone of every staged head: fsck --full, one commit on an upstream base, diff = the file.
Prints STAGECANARY lines and "STAGECANARY PASS" or "STAGECANARY FAIL: ...". Exit 0 iff PASS. Env: W, PC_TAG, PR_TOKEN."""
import base64, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
W = os.environ["W"]; TAG = os.environ["PC_TAG"]
FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
UP = "https://github.com/open-goat/pequalnp-proofs.git"
SPARSE = ["/.github/", "/STOP", "/CONTRIBUTING.md", "/lean/PEqualNP/", "!/lean/PEqualNP/Outside/"]   # as drain.py
HDR = "AUTHORIZATION: basic " + base64.b64encode(f"x-access-token:{os.environ.get('PR_TOKEN', '')}".encode()).decode()
AUTH = ["-c", f"http.https://github.com/.extraheader={HDR}"]


def sh(*a, **k):
    return subprocess.run(list(a), capture_output=True, text=True, **k)


CHILD = r'''
import json, os, sys, time
sys.path.insert(0, os.environ["PC_SRC"])
import submit as S
S.create_pr = lambda g, l: (None, "no create (stagecanary)")
def nopush(c, g):
    raise AssertionError("push_branch called in the staged path")
S.push_branch = nopush
t = time.time()
try:
    url, why = S.submit(os.environ["PC_HEAD"], None)
except AssertionError as e:
    why = "PUSHED: " + str(e)
print("PCRESULT " + json.dumps(dict(why=why, submit_s=round(time.time() - t, 3), stg={k: v for k, v in S.STG.items()})))
'''


def main():
    os.makedirs(W, exist_ok=True)
    base = os.path.join(W, "upstream-base")
    t = time.time()
    ok = (sh("git", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout", "--single-branch", "--branch", "main",
             UP, base).returncode == 0 and sh("git", "-C", base, "sparse-checkout", "set", "--no-cone", *SPARSE).returncode == 0
          and sh("git", "-C", base, "checkout", "-q", "main").returncode == 0)
    if not ok:
        print("STAGECANARY FAIL: upstream clone"); return 1
    base_sha = sh("git", "-C", base, "rev-parse", "HEAD").stdout.strip()
    print(f"STAGECANARY clone {time.time() - t:.1f}s base {base_sha[:12]}", flush=True)
    url = f"https://github.com/{FORK}.git"
    refs = dict((l.split()[1], l.split()[0]) for l in sh("git", *AUTH, "ls-remote", url, f"refs/heads/stagecanary/{TAG}/*").stdout.splitlines())
    print(f"STAGECANARY refs {len(refs)}", flush=True)
    rb = os.path.join(W, "ready.git"); sh("git", "init", "-q", "--bare", rb)
    procs, bad = [], []
    for i in (1, 2, 3):
        rr, hr = f"refs/heads/stagecanary/{TAG}/r{i}", f"refs/heads/stagecanary/{TAG}/h{i}"
        if rr not in refs or hr not in refs:
            bad.append(f"unit {i}: refs missing"); continue
        if sh("git", *AUTH, "-C", rb, "fetch", "-q", "--depth=1", url, f"+{rr}:refs/r{i}").returncode:
            bad.append(f"unit {i}: ready fetch failed"); continue
        files = [x for x in sh("git", "-C", rb, "ls-tree", "-r", "--name-only", f"refs/r{i}", "ready/").stdout.split()
                 if re.fullmatch(r"ready/[A-Za-z0-9_]+\.lean", x)]
        if len(files) != 1:
            bad.append(f"unit {i}: ready/ holds {len(files)} files"); continue
        wd, tree = os.path.join(W, f"w{i}"), os.path.join(W, f"u{i}")
        os.makedirs(wd, exist_ok=True); sh("cp", "-a", base, tree)
        proof = os.path.join(wd, "proof.lean")
        open(proof, "w").write(sh("git", "-C", rb, "show", f"refs/r{i}:{files[0]}").stdout)   # as drain.py one()
        msg = sh("git", "-C", rb, "log", "-1", "--format=%B", f"refs/r{i}").stdout
        mod = os.path.basename(files[0])[:-5]
        env = dict(os.environ, PC_SRC=HERE, PC_HEAD=f"stagecanary/{TAG}/h{i}", ID=f"L-drill-sc-{i}", MOD=mod, PROOF=proof,
                   TREE=tree, W=wd, DRY="0", READY_MSG=msg, GITHUB_OUTPUT=os.path.join(wd, "out"))
        procs.append((i, mod, refs[hr], subprocess.Popen([sys.executable, "-c", CHILD], env=env, stdout=subprocess.PIPE,
                                                         stderr=subprocess.STDOUT, text=True)))
    for i, mod, head, p in procs:
        out, _ = p.communicate(timeout=900)
        m = re.search(r"^PCRESULT (.*)$", out, re.M)
        for l in out.splitlines():
            if "STAGED" in l:
                print(f"STAGECANARY log {i}: {l[:220]}")
        if not m:
            bad.append(f"unit {i}: submit crashed: " + " | ".join(out.strip().splitlines()[-3:])); continue
        r = json.loads(m.group(1))
        print(f"STAGECANARY unit {i} submit_s={r['submit_s']} staged_s={r['stg'].get('staged')} why={r['why'][:110]}", flush=True)
        if i < 3 and r["why"] != "no create (stagecanary)":
            bad.append(f"unit {i}: did not reach the create: {r['why'][:120]}")
        if i == 3 and not r["why"].startswith("staged head refused: "):
            bad.append(f"unit 3 (tampered): not refused: {r['why'][:120]}")
        if r["why"].startswith("PUSHED"):
            bad.append(f"unit {i}: pushed")
        if i == 3:
            continue
        v = os.path.join(W, f"v{i}"); tv = time.time()
        c = sh("git", *AUTH, "clone", "-q", "--no-local", "--single-branch", "--branch", f"stagecanary/{TAG}/h{i}", url, v)
        if c.returncode:
            bad.append(f"unit {i}: fresh clone failed: {c.stderr.strip()[:120]}"); continue
        tip = sh("git", "-C", v, "rev-parse", "HEAD").stdout.strip()
        par = sh("git", "-C", v, "rev-parse", "HEAD~1").stdout.strip()
        np_ = len(sh("git", "-C", v, "rev-list", "--parents", "-n", "1", "HEAD").stdout.split()) - 1
        fs = sh("git", "-C", v, "fsck", "--full", "--no-dangling")
        diff = sh("git", "-C", v, "diff", "--name-only", "HEAD~1", "HEAD").stdout.split()
        upb = sh("git", *AUTH, "ls-remote", url, f"refs/heads/upbase/{par[:8]}").stdout.split()[:1]
        au = sh("git", "-C", v, "log", "-1", "--format=%an <%ae> | %cn <%ce>").stdout.strip()
        print(f"STAGECANARY verify {i} verify_s={time.time() - tv:.1f} tip={tip[:12]} parents={np_} parent={par[:12]} "
              f"upbase={'yes' if upb == [par] else 'no'} fsck_rc={fs.returncode} diff={diff} author={au}", flush=True)
        if tip != head: bad.append(f"unit {i}: tip moved")
        if np_ != 1: bad.append(f"unit {i}: {np_} parents")
        if upb != [par] and par != base_sha: bad.append(f"unit {i}: parent {par[:12]} not an upstream base")
        if fs.returncode: bad.append(f"unit {i}: fsck: {(fs.stdout + fs.stderr).strip()[:160]}")
        if diff != [f"lean/PEqualNP/Outside/{mod}.lean"]: bad.append(f"unit {i}: diff {diff}")
        if "Leg0shii <46093332+Leg0shii@users.noreply.github.com> | Leg0shii" not in au: bad.append(f"unit {i}: author {au}")
    print("STAGECANARY PASS" if not bad else "STAGECANARY FAIL: " + "; ".join(bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
