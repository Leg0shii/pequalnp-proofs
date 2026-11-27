#!/usr/bin/env python3
"""pushbatch_canary.py (W6, Lead 09:10, lane pushbatch RC-c): REAL batched pushes on the real runner, fork only.
PC_UNITS (60) L-drill units arrive one per PC_ARRIVE_S (1 s), each its own process through the real submit() with
PUSH_BATCH_S (10) and one shared PR_GATE_DIR, as in a drain; head branches pushcanary/<tag>/<id>; create_pr is a
recorder (no PR, no create call). Unit PC_PRE (7) has its head made beforehand at the base: it must be rejected alone.
The upbase ref is made by REST first, then PC_QUIET_S (61 s) pass so the rate window is clean; the head of unit PC_PRE
is made by REST while that unit waits in the push queue (fork_head saw no head: a rival opener in between).
Pass: every other head is on the fork at its pushed commit (0 lost), the pre-existing one is rejected alone and still
at the base, at most PC_MAX_PER_MIN (7) ref writes (pushes + REST creates) in any 60 s, one fresh full clone of all
heads passes git fsck --full and each head's diff to upstream main is exactly its unit file. Prints the wait p50/p95.
Env: W, PC_TAG, PR_TOKEN, READ_TOKEN, GITHUB_REPOSITORY. The workflow deletes the branches after (one push)."""
import base64, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
W = os.environ["W"]; TAG = os.environ["PC_TAG"]
N = int(os.environ.get("PC_UNITS", "60")); ARRIVE = float(os.environ.get("PC_ARRIVE_S", "1"))
PRE = int(os.environ.get("PC_PRE", "7")); QUIET = float(os.environ.get("PC_QUIET_S", "61"))
BURST = int(os.environ.get("PC_BURST", "126")); WORKERS = int(os.environ.get("PC_WORKERS", "14"))
MAXPM = int(os.environ.get("PC_MAX_PER_MIN", "7")); BATCH = os.environ.get("PUSH_BATCH_S", "10")
FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
URL = f"https://github.com/{FORK}.git"
UP = "https://github.com/open-goat/pequalnp-proofs.git"
SPARSE = ["/.github/", "/STOP", "/CONTRIBUTING.md", "/lean/PEqualNP/", "!/lean/PEqualNP/Outside/"]   # as drain.py
HDR = "http.https://github.com/.extraheader=AUTHORIZATION: basic " + base64.b64encode(
    f"x-access-token:{os.environ.get('PR_TOKEN', '')}".encode()).decode()


def sh(*a, **k):
    return subprocess.run(list(a), capture_output=True, text=True, **k)


CHILD = r'''
import json, os, sys, time
sys.path.insert(0, os.environ["PC_SRC"])
import submit as S
S.create_pr = lambda g, l: (None, "no create (pushcanary)")
S.UNLEASED_TEST = True            # the unit's queue ref is utest/<id> (no workflow runs on utest pushes), not ready/
real = S.push_branch
T = {}
def pb(c, g):
    t = time.time(); T["commit"] = c; e = real(c, g); T["push_s"] = round(time.time() - t, 3); T["err"] = e
    T["landed"] = time.time(); return e
S.push_branch = pb
t = time.time()
url, why = S.submit(os.environ["PC_HEAD"], None)
if why == "no create (pushcanary)":
    S.delete_ready()              # as finish() does after a create: queued for the next batch push
T.update(why=why, submit_s=round(time.time() - t, 3), stg={k: v for k, v in S.STG.items()})
print("PCRESULT " + json.dumps(T))
'''


def rest_ref(ref, sha):
    r = sh("gh", "api", "-X", "POST", f"repos/{FORK}/git/refs", "-f", f"ref={ref}", "-f", f"sha={sha}",
           env=dict(os.environ, GH_TOKEN=os.environ["PR_TOKEN"]))
    return r.returncode == 0, (r.stderr or r.stdout).strip()[:150]


def pct(xs, q):
    xs = sorted(x for x in xs if x is not None)
    return xs[min(len(xs) - 1, int(q * len(xs)))] if xs else None


def git_push(base, *refspecs):
    r = sh("git", "-c", HDR, "-C", base, "push", "-q", URL, *refspecs)
    return r.returncode == 0, r.stderr.strip()[:200]


def scenario(name, base, bsha, units, arrive, workers, pre, t_writes):
    """units L-drill-<tag><name>-<i> through the real submit() with batched pushes; returns (bad, results, gate)"""
    gate = os.path.join(W, "gate-" + name); os.makedirs(gate, exist_ok=True)
    open(os.path.join(gate, f"upbase-{bsha[:12]}.ok"), "w").write("canary\n")
    # lane movingmain (RC-c3): inside a drain submit() reads the drain's newest base note W/upbase.json (fail closed
    # without it); the canary's shared base is the drain's
    json.dump({"sha": bsha, "t": time.time(), "dir": base, "adopted": bsha, "adopted_fetch_t": time.time()},
              open(os.path.join(gate, "upbase.json"), "w"))
    fenv = dict(os.environ, ID="pushflush", MOD="pushflush", PROOF=os.devnull, TREE=W, W=os.path.join(W, "pf-" + name),
                DRY="0", PR_GATE_DIR=gate, RIVAL_SNAP_DIR=gate, GITHUB_OUTPUT=os.devnull, PUSH_BATCH_S=BATCH)
    os.makedirs(fenv["W"], exist_ok=True)
    fl = subprocess.Popen([sys.executable, "-I", os.path.join(HERE, "submit.py"), "--pushflush"], env=fenv,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    gids = [f"L-drill-{TAG}{name}-{i}" for i in range(1, units + 1)]
    if pre:
        import threading
        pg = gids[pre - 1]

        def rival():
            f = os.path.join(gate, "pushq", re.sub(r"[^A-Za-z0-9_.-]", "_", f"pushcanary/{TAG}/{pg}") + ".req")
            for _ in range(6000):
                if os.path.exists(f):
                    ok, why = rest_ref(f"refs/heads/pushcanary/{TAG}/{pg}", bsha); t_writes.append(time.time())
                    print(f"PUSHBATCH {name} rival head made while queued: ok={ok} {'' if ok else why}", flush=True)
                    return
                time.sleep(0.05)
        threading.Thread(target=rival, daemon=True).start()
    t0 = time.time()
    ready = {g: t0 + (i * arrive) for i, g in enumerate(gids)}
    todo, run_, res, bad = list(gids), [], {}, []
    while todo or run_:
        now = time.time()
        while todo and len(run_) < workers and ready[todo[0]] <= now:
            gid = todo.pop(0); mod = gid.replace("-", "_")
            tree, wd = os.path.join(W, "u-" + gid), os.path.join(W, "w-" + gid)
            sh("cp", "-a", base, tree); os.makedirs(wd, exist_ok=True)
            proof = os.path.join(wd, mod + ".lean")
            open(proof, "w").write(f"import PEqualNP.Defs\n\n-- push batch canary {TAG} {gid} (fork only, never a PR)\n")
            env = dict(os.environ, PC_SRC=HERE, PC_HEAD=f"pushcanary/{TAG}/{gid}", ID=gid, MOD=mod, PROOF=proof, TREE=tree,
                       W=wd, DRY="0", GITHUB_OUTPUT=os.path.join(wd, "out"), PR_GATE_DIR=gate, RIVAL_SNAP_DIR=gate,
                       PUSH_BATCH_S=BATCH, GITHUB_REF_NAME=f"utest/{gid}")
            run_.append((gid, mod, subprocess.Popen([sys.executable, "-c", CHILD], env=env,
                                                    stdout=open(os.path.join(wd, "child.log"), "w"), stderr=subprocess.STDOUT)))
        for x in list(run_):
            gid, mod, p = x
            if p.poll() is None:
                continue
            run_.remove(x)
            out = open(os.path.join(W, "w-" + gid, "child.log")).read()
            m = re.search(r"^PCRESULT (.*)$", out, re.M)
            if not m:
                bad.append(f"{gid}: crashed: " + " | ".join(out.strip().splitlines()[-3:])); continue
            r = json.loads(m.group(1)); r["gid"], r["mod"] = gid, mod
            r["ready_to_landed"] = round(r["landed"] - ready[gid], 3) if r.get("landed") else None
            res[gid] = r
        time.sleep(0.05)
    span = time.time() - t0
    open(os.path.join(gate, "pushq", "flush.stop"), "w").close()
    fo, _ = fl.communicate(timeout=120)
    print(f"PUSHBATCH {name} flusher: {(fo.strip().splitlines() or [''])[-1][:160]}", flush=True)
    try:
        log = [l.split() for l in open(os.path.join(gate, "pushq", "pushes.log")).read().splitlines()]
    except OSError:
        log = []
    print(f"PUSHBATCH {name} pushes (t, heads, s, ok, deletes): "
          f"{[(round(float(x[0]) - t0, 1), int(x[1]), float(x[2]), x[3], int(x[4]) if len(x) > 4 else 0) for x in log]}", flush=True)
    for x in log:
        t_writes.append(float(x[0]))
    w = [r.get("stg", {}).get("push_wait") for g, r in res.items() if g != (gids[pre - 1] if pre else None)]
    rl = [r.get("ready_to_landed") for g, r in res.items() if g != (gids[pre - 1] if pre else None)]
    print(f"PUSHBATCH {name} units={units} arrive_s={arrive} workers={workers} span={span:.0f}s pushes={len(log)} "
          f"push_wait p50={pct(w, .5)} p95={pct(w, .95)} max={pct(w, 1)} | ready_to_landed p50={pct(rl, .5)} "
          f"p95={pct(rl, .95)} max={pct(rl, 1)} | deletes={sum(int(x[4]) for x in log if len(x) > 4)}", flush=True)
    return bad, res, gids


def main():
    os.makedirs(W, exist_ok=True)
    base = os.path.join(W, "upstream-base")
    t = time.time()
    ok = (sh("git", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout", "--single-branch", "--branch", "main",
             UP, base).returncode == 0 and sh("git", "-C", base, "sparse-checkout", "set", "--no-cone", *SPARSE).returncode == 0
          and sh("git", "-C", base, "checkout", "-q", "main").returncode == 0)
    if not ok:
        print("PUSHBATCH FAIL: upstream clone"); return 1
    bsha = sh("git", "-C", base, "rev-parse", "HEAD").stdout.strip()
    print(f"PUSHBATCH clone {time.time() - t:.1f}s base {bsha[:12]} batch_s {BATCH}", flush=True)
    SC = [("a", N, ARRIVE, WORKERS, PRE), ("b", BURST, 0.0, WORKERS, 0)]
    writes = []
    ok, why = rest_ref(f"refs/heads/upbase/{bsha[:8]}", bsha); writes.append(time.time())
    print(f"PUSHBATCH rest create upbase/{bsha[:8]} ok={ok} {'' if ok else why}", flush=True)
    if not ok:
        print("PUSHBATCH FAIL: REST ref create"); return 1
    # every unit's queue ref utest/<id> (stands in for ready/<id>: no workflow runs on utest pushes), in ONE push
    allg = [f"L-drill-{TAG}{n}-{i}" for n, u, _, _, _ in SC for i in range(1, u + 1)]
    ok, why = git_push(base, *[f"{bsha}:refs/heads/utest/{g}" for g in allg]); writes.append(time.time())
    print(f"PUSHBATCH queue refs utest/* x{len(allg)} in one push ok={ok} {why}", flush=True)
    if not ok:
        print("PUSHBATCH FAIL: queue refs"); return 1
    time.sleep(QUIET)
    bad, allres = [], {}
    for k, (name, units, arrive, workers, pre) in enumerate(SC):
        if k:
            time.sleep(QUIET)                      # each scenario in its own clean minute
        b, res, gids = scenario(name, base, bsha, units, arrive, workers, pre, writes)
        bad += b; allres.update({g: (r, name, pre and g == gids[pre - 1]) for g, r in res.items()})
        if len(res) < units:
            bad.append(f"{name}: {units - len(res)} units without a result")
    ev = sorted(writes)
    per_min = max(sum(1 for e in ev if s <= e < s + 60) for s in ev) if ev else 0
    heads, qrefs = {}, []
    for l in sh("git", "-c", HDR, "ls-remote", URL).stdout.splitlines():
        p = l.split("\t")
        if len(p) == 2 and p[1].startswith(f"refs/heads/pushcanary/{TAG}/"):
            heads[p[1].rsplit("/", 1)[1]] = p[0]
        if len(p) == 2 and p[1].startswith(f"refs/heads/utest/L-drill-{TAG}"):
            qrefs.append(p[1])
    lost, rival_ok = [], None
    for g, (r, name, is_pre) in sorted(allres.items()):
        if is_pre:
            rival_ok = (r.get("why") or "").startswith("push: rejected") and heads.get(g) == bsha
            continue
        if r.get("why") != "no create (pushcanary)" or heads.get(g) != r.get("commit"):
            lost.append(f"{g}({(r.get('why') or '')[:60]})")
    v = os.path.join(W, "verify"); tv = time.time()
    good = [g for g, (r, _, is_pre) in sorted(allres.items()) if not is_pre and heads.get(g)]
    fs_rc, diffbad = None, []
    if good:
        c = sh("git", "-c", HDR, "clone", "-q", "--no-local", "--single-branch", "--branch", f"pushcanary/{TAG}/{good[0]}", URL, v)
        f = sh("git", "-c", HDR, "-C", v, "fetch", "-q", "origin", *[f"refs/heads/pushcanary/{TAG}/{g}:refs/remotes/pc/{g}" for g in good])
        fs = sh("git", "-C", v, "fsck", "--full", "--no-dangling")
        fs_rc = fs.returncode if not (c.returncode or f.returncode) else f"clone/fetch rc {c.returncode}/{f.returncode}"
        for g in good:
            ref = f"refs/remotes/pc/{g}"
            par = sh("git", "-C", v, "rev-parse", ref + "~1").stdout.strip()
            dif = sh("git", "-C", v, "diff", "--name-only", ref + "~1", ref).stdout.split()
            if par != bsha or dif != [f"lean/PEqualNP/Outside/{g.replace('-', '_')}.lean"]:
                diffbad.append(f"{g} parent={par[:12]} diff={dif}")
        if fs_rc != 0:
            bad.append(f"fsck: {fs_rc}")
    print(f"PUSHBATCH verify heads={len(heads)} fsck_rc={fs_rc} diff_bad={diffbad[:3]} queue_refs_left={len(qrefs)} "
          f"verify_s={time.time() - tv:.1f}")
    print(f"PUSHBATCH fork ref writes (REST upbase + rival, queue-ref setup push, batch pushes) max in any 60 s = {per_min}; "
          "the drain state saver and alerts push to the toolkit repository, not the fork")
    print(f"PUSHBATCH rival head rejected alone: {rival_ok}")
    if lost:
        bad.append(f"{len(lost)} lost: {' '.join(lost[:5])}")
    if PRE and not rival_ok:
        bad.append("rival head not rejected alone")
    if per_min > MAXPM:
        bad.append(f"{per_min} fork ref writes in 60 s > {MAXPM}")
    if diffbad:
        bad.append(f"{len(diffbad)} heads with a wrong parent/diff")
    if qrefs:
        bad.append(f"{len(qrefs)} queue refs not deleted")
    print("PUSHBATCH PASS" if not bad else "PUSHBATCH FAIL: " + "; ".join(bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
