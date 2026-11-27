#!/usr/bin/env python3
"""pushcanary.py (W6, Lead 08:50): the REAL branch push of submit() on the real runner, DRY nothing else.
3 L-drill units, each through the real submit() (fork_head, commit build by mktree --missing, push_branch) from a
cold blobless clone of upstream main as drain.py makes it (one shared base, a cp -a copy per unit). The head branch
is pushcanary/<tag>/<id> on the FORK. create_pr is replaced by a recorder: no PR, no create call, nothing upstream.
Then a fresh FULL clone of every pushed branch: git fsck --full, and the diff to its parent (upstream main) must be
exactly the unit's file. Prints PUSHCANARY lines and "PUSHCANARY PASS" or "PUSHCANARY FAIL: ...". Exit 0 iff PASS.
Env: W, PC_TAG, PR_TOKEN, READ_TOKEN, GITHUB_REPOSITORY. The workflow deletes the branches after."""
import json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
W = os.environ["W"]; TAG = os.environ["PC_TAG"]; N = int(os.environ.get("PC_UNITS", "3"))
FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
UP = "https://github.com/open-goat/pequalnp-proofs.git"
SPARSE = ["/.github/", "/STOP", "/CONTRIBUTING.md", "/lean/PEqualNP/", "!/lean/PEqualNP/Outside/"]   # as drain.py


def sh(*a, **k):
    return subprocess.run(list(a), capture_output=True, text=True, **k)


CHILD = r'''
import json, os, sys, time
sys.path.insert(0, os.environ["PC_SRC"])
import submit as S
S.create_pr = lambda g, l: (None, "no create (pushcanary)")
real = S.push_branch
T = {}
def pb(c, g):
    t = time.time(); e = real(c, g); T["push_s"] = round(time.time() - t, 3); T["commit"] = c; return e
S.push_branch = pb
t = time.time()
url, why = S.submit(os.environ["PC_HEAD"], None)
T.update(why=why, submit_s=round(time.time() - t, 3), stg={k: v for k, v in S.STG.items()})
print("PCRESULT " + json.dumps(T))
'''


def main():
    os.makedirs(W, exist_ok=True)
    base = os.path.join(W, "upstream-base")
    t = time.time()
    ok = (sh("git", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout", "--single-branch", "--branch", "main",
             UP, base).returncode == 0 and sh("git", "-C", base, "sparse-checkout", "set", "--no-cone", *SPARSE).returncode == 0
          and sh("git", "-C", base, "checkout", "-q", "main").returncode == 0)
    if not ok:
        print("PUSHCANARY FAIL: upstream clone"); return 1
    base_sha = sh("git", "-C", base, "rev-parse", "HEAD").stdout.strip()
    print(f"PUSHCANARY clone {time.time() - t:.1f}s base {base_sha[:12]}", flush=True)
    procs = []
    for i in range(1, N + 1):
        gid = f"L-drill-{TAG}-{i}"
        mod = gid.replace("-", "_")
        tree, wd = os.path.join(W, f"u{i}"), os.path.join(W, f"w{i}")
        sh("cp", "-a", base, tree); os.makedirs(wd, exist_ok=True)
        proof = os.path.join(wd, mod + ".lean")
        open(proof, "w").write(f"import PEqualNP.Defs\n\n-- push canary {TAG} unit {i} (fork only, never a PR)\n")
        env = dict(os.environ, PC_SRC=HERE, PC_HEAD=f"pushcanary/{TAG}/{gid}", ID=gid, MOD=mod, PROOF=proof, TREE=tree, W=wd,
                   DRY="0", GITHUB_OUTPUT=os.path.join(wd, "out"))
        procs.append((gid, mod, subprocess.Popen([sys.executable, "-c", CHILD], env=env, stdout=subprocess.PIPE,
                                                 stderr=subprocess.STDOUT, text=True)))
    res, bad = [], []
    for gid, mod, p in procs:
        out, _ = p.communicate(timeout=900)
        m = re.search(r"^PCRESULT (.*)$", out, re.M)
        if not m:
            bad.append(f"{gid}: submit crashed: " + " | ".join(out.strip().splitlines()[-3:])); continue
        r = json.loads(m.group(1)); r["gid"], r["mod"] = gid, mod
        print(f"PUSHCANARY unit {gid} push_s={r.get('push_s')} submit_s={r['submit_s']} why={r['why'][:100]} stg={r['stg']}", flush=True)
        if r["why"] != "no create (pushcanary)":
            bad.append(f"{gid}: submit ended before the create: {r['why'][:120]}")
        res.append(r)
    for r in res:
        if "commit" not in r:
            continue
        v = os.path.join(W, "v-" + r["gid"])
        head = f"pushcanary/{TAG}/{r['gid']}"
        import base64
        hdr = "AUTHORIZATION: basic " + base64.b64encode(f"x-access-token:{os.environ['PR_TOKEN']}".encode()).decode()
        c = sh("git", "-c", f"http.https://github.com/.extraheader={hdr}", "clone", "-q", "--no-local", "--depth", "2",
               "--branch", head, f"https://github.com/{FORK}.git", v)
        if c.returncode:
            bad.append(f"{r['gid']}: fresh clone failed: {c.stderr.strip()[:120]}"); continue
        tip = sh("git", "-C", v, "rev-parse", "HEAD").stdout.strip()
        par = sh("git", "-C", v, "rev-parse", "HEAD~1").stdout.strip()
        fs = sh("git", "-C", v, "fsck", "--full", "--no-dangling")
        diff = sh("git", "-C", v, "diff", "--name-only", "HEAD~1", "HEAD").stdout.split()
        want = [f"lean/PEqualNP/Outside/{r['mod']}.lean"]
        line = f"tip={tip[:12]} pushed={r['commit'][:12]} parent={par[:12]} fsck_rc={fs.returncode} diff={diff}"
        print(f"PUSHCANARY verify {r['gid']} {line}", flush=True)
        if tip != r["commit"]:
            bad.append(f"{r['gid']}: branch tip is not the pushed commit")
        if par != base_sha:
            bad.append(f"{r['gid']}: parent is not upstream main {base_sha[:12]}")
        if fs.returncode:
            bad.append(f"{r['gid']}: fsck: {(fs.stdout + fs.stderr).strip()[:160]}")
        if diff != want:
            bad.append(f"{r['gid']}: diff {diff} != {want}")
    ps = sorted(r["push_s"] for r in res if r.get("push_s") is not None)
    if ps:
        print(f"PUSHCANARY push p50={ps[len(ps) // 2]:.2f}s p95={ps[-1]:.2f}s n={len(ps)}")
    if len(ps) < N:
        bad.append(f"{N - len(ps)} of {N} pushes missing")
    if ps and ps[-1] > 3.0:
        print(f"PUSHCANARY SLOW push max {ps[-1]:.1f}s > 3 s")
    print("PUSHCANARY PASS" if not bad else "PUSHCANARY FAIL: " + "; ".join(bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
