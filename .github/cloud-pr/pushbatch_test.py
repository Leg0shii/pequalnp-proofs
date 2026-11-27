#!/usr/bin/env python3
"""pushbatch_test.py [dir of submit.py]: lane pushbatch (W6, Lead 09:10, RC-c) on a LOCAL bare remote (git url
insteadOf, no network). Each unit is its own process with its own tree copy, as in drain.py.
  B1 30 units arriving over 3 s, PUSH_BATCH_S=1: every head lands with its commit, batches <= ceil(span/1)+1,
     batch pushes at least 1 s apart, one pre-existing ref rejected alone (the others land)
  B2 the first batch push answers HTTP 429: a push refusal (w9: PR_GATE_DIR/stall + pushrefusals=1), nothing lost, the heads
     land after the stall
  B3 PUSH_BATCH_S=0: the per-unit push as before (one push per unit)
  B5 halted drain (R3, a fresh halt read before every head push): no head pushed, every waiting unit gets "halted:"
  B4 25 units that also delete their ready/ ref: every delete rides in a batch push (heads or the --pushflush
     flusher), no ready ref left, no extra pushes (at most one per PUSH_BATCH_S)
Prints one line per case and "PUSHBATCH PASS <sha>" or "PUSHBATCH FAIL <sha>: <cases>". Exit 0 iff PASS."""
import json, os, subprocess, sys, tempfile, time

SRC = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
FAKE_URL = "https://github.com/test/fork.git"

CHILD = r'''
import json, os, sys, time
sys.path.insert(0, os.environ["PB_SRC"])
import submit as S
S.upbase_ref = lambda b: "upbase/x"
S.filing_halted = (lambda *a, **k: (True, "drill halt")) if os.environ.get("PB_HALT") else (lambda *a, **k: (False, ""))
S.log = lambda *a: print(*a, flush=True)
if os.environ.get("PB_429"):
    real = S.run
    def run(cmd, timeout=300, env=None, cwd=None):
        if "push" in cmd and "--porcelain" in cmd and not os.path.exists(os.environ["PB_429"]):
            open(os.environ["PB_429"], "w").write("1")
            return S.subprocess.CompletedProcess(cmd, 128, "", "fatal: unable to access 'x': The requested URL returned error: 429")
        return real(cmd, timeout=timeout, env=env, cwd=cwd)
    S.run = run
t = time.time()
e = S.push_branch(os.environ["PB_C"], os.environ["PB_HEAD"])
if os.environ.get("PB_DEL"):
    S.delete_ready()
print("PBRESULT " + json.dumps({"err": e, "s": round(time.time() - t, 3), "wait": S.STG.get("push_wait"), "n": S.STG.get("push_batch")}))
'''


def sh(*a, cwd=None, env=None):
    return subprocess.run(list(a), capture_output=True, text=True, cwd=cwd, env=env)


def setup(d):
    base, remote = os.path.join(d, "base"), os.path.join(d, "remote.git")
    sh("git", "init", "-q", "-b", "main", base)
    os.makedirs(os.path.join(base, "lean", "PEqualNP", "Outside"))
    for i in range(50):
        open(os.path.join(base, "lean", "PEqualNP", "Outside", f"L_old_{i}.lean"), "w").write(f"-- {i}\n")
    ge = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    sh("git", "-C", base, "add", "-A"); sh("git", "-C", base, "commit", "-qm", "base", env=ge)
    sh("git", "clone", "-q", "--bare", base, remote)
    bsha = sh("git", "-C", base, "rev-parse", "HEAD").stdout.strip()
    sh("git", "-C", remote, "update-ref", "refs/heads/upbase/x", bsha)
    cfg = os.path.join(d, "gitconfig")
    open(cfg, "w").write(f'[url "{remote}"]\n\tinsteadOf = {FAKE_URL}\n[user]\n\tname = t\n\temail = t@t\n')
    return base, remote, bsha, cfg, ge


def unit(d, base, i, ge):
    tree = os.path.join(d, f"u{i}")
    sh("cp", "-a", base, tree)
    f = os.path.join(tree, "lean", "PEqualNP", "Outside", f"L_drill_{i}.lean")
    open(f, "w").write(f"-- unit {i}\n")
    sh("git", "-C", tree, "add", "-A"); sh("git", "-C", tree, "commit", "-qm", f"unit {i}", env=ge)
    return tree, sh("git", "-C", tree, "rev-parse", "HEAD").stdout.strip()


def run_case(n, batch_s, pre=None, p429=False, stagger=0.1, dels=False, halt=False):
    d = tempfile.mkdtemp(prefix="pushbatch-")
    base, remote, bsha, cfg, ge = setup(d)
    gate = os.path.join(d, "gate"); os.makedirs(gate)
    if pre:
        sh("git", "-C", remote, "update-ref", f"refs/heads/pb/L-drill-{pre}", bsha)
    units = [(i,) + unit(d, base, i, ge) for i in range(1, n + 1)]
    procs = []
    fl = None
    if dels:
        for i in range(1, n + 1):
            sh("git", "-C", remote, "update-ref", f"refs/heads/ready/L-drill-{i}", bsha)
        fenv = dict(os.environ, TREE=d, W=os.path.join(d, "wf"), PR_GATE_DIR=gate, RIVAL_SNAP_DIR=gate, PUSH_BATCH_S=str(batch_s),
                    GITHUB_REPOSITORY="test/fork", GIT_CONFIG_GLOBAL=cfg, PR_TOKEN="drill", READ_TOKEN="drill", ID="pushflush",
                    MOD="pushflush", PROOF="/dev/null", DRY="0", GITHUB_OUTPUT=os.devnull)
        fenv.pop("GITHUB_ACTIONS", None)
        os.makedirs(fenv["W"], exist_ok=True)
        fl = subprocess.Popen([sys.executable, "-I", os.path.join(SRC, "submit.py"), "--pushflush"], env=fenv,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    for i, tree, c in units:
        env = dict(os.environ, PB_SRC=SRC, PB_C=c, PB_HEAD=f"pb/L-drill-{i}", TREE=tree, W=os.path.join(d, f"w{i}"),
                   PR_GATE_DIR=gate, RIVAL_SNAP_DIR=gate, PUSH_BATCH_S=str(batch_s), GITHUB_REPOSITORY="test/fork",
                   GIT_CONFIG_GLOBAL=cfg, PR_TOKEN="drill", READ_TOKEN="drill", ID=f"L-drill-{i}", MOD=f"L_drill_{i}",
                   PROOF="/dev/null", DRY="0", GITHUB_OUTPUT=os.devnull)
        if p429:
            env["PB_429"] = os.path.join(d, "429-done")
        if dels:
            env.update(PB_DEL="1", GITHUB_REF_NAME=f"ready/L-drill-{i}")
        if halt:
            env["PB_HALT"] = "1"
        for k in ("GITHUB_ACTIONS",):
            env.pop(k, None)
        os.makedirs(env["W"], exist_ok=True)
        procs.append((i, c, subprocess.Popen([sys.executable, "-c", CHILD], env=env, stdout=subprocess.PIPE,
                                             stderr=subprocess.STDOUT, text=True)))
        time.sleep(stagger)
        if p429 and os.path.exists(os.path.join(gate, "stall")):
            open(os.path.join(gate, "stall"), "w").write(str(time.time() + 1.5))   # shorten the 60 s stall for the test
    if p429:
        for _ in range(100):
            if os.path.exists(os.path.join(gate, "stall")):
                open(os.path.join(gate, "stall"), "w").write(str(time.time() + 1.5)); break
            time.sleep(0.1)
    res = {}
    for i, c, p in procs:
        out, _ = p.communicate(timeout=300)
        line = [l for l in out.splitlines() if l.startswith("PBRESULT ")]
        res[i] = json.loads(line[-1][9:]) if line else {"err": "crash: " + " | ".join(out.strip().splitlines()[-3:])}
        res[i]["c"] = c
    if fl:
        open(os.path.join(gate, "pushq", "flush.stop"), "w").close()
        fl.communicate(timeout=120)
    left = sh("git", "-C", remote, "for-each-ref", "--format=%(refname)", "refs/heads/ready/").stdout.split()
    refs = dict(reversed(l.split()) for l in sh("git", "-C", remote, "for-each-ref", "--format=%(objectname) %(refname)",
                                                   "refs/heads/pb/").stdout.splitlines())
    try:
        log = [l.split() for l in open(os.path.join(gate, "pushq", "pushes.log")).read().splitlines()]
    except OSError:
        log = []
    rf = os.path.join(gate, "pushrefusals")             # w9's push refusal counter (never the create giveup)
    refusals = open(rf).read().strip() if os.path.exists(rf) else "0"
    return (res, refs, log, bsha, refusals, left) if dels else (res, refs, log, bsha, refusals)


def pct(xs, q):
    xs = sorted(x for x in xs if x is not None)
    return xs[min(len(xs) - 1, int(q * len(xs)))] if xs else None


def main():
    sha = subprocess.run(["git", "-C", SRC, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    fails = []
    # B1
    res, refs, log, bsha, _ = run_case(30, 1.0, pre=7)
    lost = [i for i, r in res.items() if i != 7 and (r["err"] or refs.get(f"refs/heads/pb/L-drill-{i}") != r["c"])]
    pre_ok = bool(res[7]["err"]) and refs.get("refs/heads/pb/L-drill-7") == bsha
    ts = [float(x[0]) for x in log]
    gaps = [b - a for a, b in zip(ts, ts[1:])]
    ok = not lost and pre_ok and len(log) <= 6 and all(g >= 0.99 for g in gaps) and sum(int(x[1]) for x in log) == 30
    w = [r.get("wait") for r in res.values()]
    print(("ok   " if ok else "FAIL ") + f"B1 | lost={lost} pre7_rejected_alone={pre_ok} ({(res[7]['err'] or '')[:60]}) "
          f"batches={[int(x[1]) for x in log]} min_gap={min(gaps) if gaps else '-'} wait p50={pct(w, .5)} p95={pct(w, .95)}")
    if not ok:
        fails.append("B1")
    # B2
    res, refs, log, bsha, k = run_case(8, 0.5, p429=True, stagger=0.05)
    lost = [i for i, r in res.items() if r["err"] or refs.get(f"refs/heads/pb/L-drill-{i}") != r["c"]]
    ok = not lost and k == "1" and log and log[0][3] == "fail" and any(x[3] == "ok" for x in log)
    print(("ok   " if ok else "FAIL ") + f"B2 | lost={lost} refusals={k} log={[(x[1], x[3]) for x in log]}")
    if not ok:
        fails.append("B2")
    # B3
    res, refs, log, bsha, _ = run_case(4, 0, stagger=0.05)
    lost = [i for i, r in res.items() if r["err"] or refs.get(f"refs/heads/pb/L-drill-{i}") != r["c"]]
    ok = not lost and not log and all(r.get("n") is None for r in res.values())
    print(("ok   " if ok else "FAIL ") + f"B3 | lost={lost} batch_log={log}")
    if not ok:
        fails.append("B3")
    # B4
    res, refs, log, bsha, _, left = run_case(25, 1.0, stagger=0.1, dels=True)
    lost = [i for i, r in res.items() if r["err"] or refs.get(f"refs/heads/pb/L-drill-{i}") != r["c"]]
    nd = sum(int(x[4]) for x in log if len(x) > 4)
    ts = [float(x[0]) for x in log]
    gaps = [b - a for a, b in zip(ts, ts[1:])]
    ok = not lost and not left and nd == 25 and all(g >= 0.99 for g in gaps) and len(log) <= 6
    print(("ok   " if ok else "FAIL ") + f"B4 ready deletes ride along | lost={lost} ready_left={left[:3]} deletes={nd} "
          f"pushes={len(log)} {[(int(x[1]), int(x[4])) for x in log]} min_gap={min(gaps) if gaps else '-'}")
    if not ok:
        fails.append("B4")
    # B5
    res, refs, log, bsha, _ = run_case(5, 0.5, stagger=0.05, halt=True)
    ok = all((r["err"] or "").startswith("halted:") for r in res.values()) and not refs and not log
    print(("ok   " if ok else "FAIL ") + f"B5 halted drain pushes no head | errs={[ (r['err'] or '')[:20] for r in res.values()][:2]} refs={len(refs)} pushes={len(log)}")
    if not ok:
        fails.append("B5")
    print(f"PUSHBATCH PASS {sha}" if not fails else f"PUSHBATCH FAIL {sha}: " + " ".join(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
