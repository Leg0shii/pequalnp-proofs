#!/usr/bin/env python3
"""guardpar_test.py [dir of submit.py]: lane guards (W6, Lead 08:40, RC-c). The guards (checkcore.sh) run in a thread
beside the race check, the commit build and the branch push. Cases, each a fresh process running the real main()
with GitHub, the desk and the guard faked (timed events):
  G1 slow FAILING guard, push already done: no create, the pushed head branch is deleted, result formatfail
  G2 as G1 but a PR of ours is on the branch: branch kept, no create
  G3 guard fails BEFORE the push point: no push, no create, formatfail
  G4 slow PASSING guard: the push starts before the guard ends, the create only after it
  G5 DRY, slow failing guard: no WOULD-CREATE, formatfail
  G6 DRY, slow passing guard: WOULD-CREATE only after the guard ended
  G7 takeover (our head branch exists, no PR) and a failing guard: no create
  G8 our PR already open AND the unit held by another agent: "exists", as before (order of the old exits kept)
Prints one line per case and "GUARDPAR PASS <sha>" or "GUARDPAR FAIL <sha>: <cases>". Exit 0 iff PASS."""
import json, os, re, subprocess, sys, tempfile, time

SRC = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 and sys.argv[1] != "--child" else os.path.dirname(os.path.abspath(__file__)))

CHILD = r'''
import json, os, subprocess, sys, time
sys.path.insert(0, os.environ["GP_SRC"])
import submit as S
c = json.loads(os.environ["GP_CASE"])
EV = []
T0 = time.time()
def ev(x):
    EV.append([x, round(time.time() - T0, 3)])
cp = lambda o="", rc=0, e="": subprocess.CompletedProcess([], rc, o, e)
S.filing_halted = lambda *a, **k: (False, "")
S.stopped = lambda: False
S.gaps_json = lambda *a, **k: {"gaps": [{"id": S.ID, "holders_now": c.get("held", 0)}]}
S.open_pr_for_branch = lambda g: c.get("our_pr")
S.fork_head = lambda g: c.get("head")
S.our_prs_on_branch = lambda g, st: (["https://github.com/x/y/pull/7"] if c.get("pr_on_branch") and st == "open" else [])
def race_ok(g):
    time.sleep(c.get("race_s", 0.05)); ev("race"); return True, "free", None
S.race_ok = race_ok
def push_branch(cm, g):
    ev("push"); time.sleep(0.05); return None
S.push_branch = push_branch
def create_pr(g, lease):
    ev("create"); return "https://github.com/x/y/pull/8", "ok"
S.create_pr = create_pr
for f in ("release", "free_slot", "delete_ready"):
    setattr(S, f, lambda *a, **k: None)
class D:
    def lease_of(self, g): return None
S.dg = lambda: D()
real_log = S.log
def log(*a):
    if a and str(a[0]).startswith("WOULD-CREATE"): ev("would-create")
    real_log(*a)
S.log = log
def git(*a, env=None, timeout=300):
    a = list(a)
    return {"rev-parse": cp("base0\n"), "cat-file": cp(rc=1), "hash-object": cp("blob0\n"), "write-tree": cp("tree0\n"),
            "diff-tree": cp(S.REL + "\n"), "commit-tree": cp("commit0\n")}.get(a[0], cp())
S.git = git
S.treebuild.tree_with_file = lambda *a, **k: "tree0"
def run(cmd, timeout=300, env=None, cwd=None):
    if len(cmd) > 1 and cmd[0] == "bash" and cmd[1].endswith("checkcore.sh"):
        time.sleep(c.get("guard_s", 0.0)); ev("guard-end")
        return cp("guards ok\n") if c.get("guard_ok", True) else cp("FAIL: guard imports/format\n", 1)
    if "push" in cmd and "--delete" in cmd:
        ev("delete " + cmd[-1]); return cp()
    return cp()
S.run = run
try:
    S.main()
except SystemExit:
    pass
res = dict(l.split("=", 1) for l in open(os.environ["GITHUB_OUTPUT"]).read().splitlines() if "=" in l)
print("GPRESULT " + json.dumps({"ev": EV, "result": res.get("result"), "why": res.get("why", "")[:120]}))
'''

CASES = {
    "G1": ({"guard_s": 0.6, "guard_ok": False}, False),
    "G2": ({"guard_s": 0.6, "guard_ok": False, "pr_on_branch": True}, False),
    "G3": ({"guard_s": 0.0, "guard_ok": False, "race_s": 0.4}, False),
    "G4": ({"guard_s": 0.6, "guard_ok": True}, False),
    "G5": ({"guard_s": 0.6, "guard_ok": False}, True),
    "G6": ({"guard_s": 0.6, "guard_ok": True}, True),
    "G7": ({"guard_s": 0.6, "guard_ok": False, "head": "abc123"}, False),
    "G8": ({"guard_s": 0.0, "our_pr": "https://github.com/x/y/pull/5", "held": 1}, False),
}


def child(case, dry):
    d = tempfile.mkdtemp(prefix="guardpar-")
    proof = os.path.join(d, "L_meta_1.lean")
    open(proof, "w").write("import PEqualNP.Defs\n")
    env = dict(os.environ, GP_SRC=SRC, GP_CASE=json.dumps(case), ID="L-meta-1", MOD="L_meta_1", PROOF=proof, TREE=d, W=d,
               GITHUB_OUTPUT=os.path.join(d, "out"), PR_TOKEN="drill", READ_TOKEN="drill", DRY="1" if dry else "0",
               RIVAL_SNAP_DIR=os.path.join(d, "snap"), GHCOND_DIR=os.path.join(d, "gc"), READY_MSG="")
    for k in ("GITHUB_ACTIONS", "FILING_FIXTURE", "GUARDS_INLINE"):
        env.pop(k, None)
    r = subprocess.run([sys.executable, "-c", CHILD], env=env, capture_output=True, text=True, timeout=120, cwd=d)
    m = re.search(r"^GPRESULT (.*)$", r.stdout, re.M)
    return json.loads(m.group(1)) if m else {"crash": (r.stderr or r.stdout).strip().splitlines()[-3:], "ev": []}


def t_of(evs, name):
    return next((t for e, t in evs if e.startswith(name)), None)


def judge(k, r):
    if "crash" in r:
        return False, "crash " + " | ".join(r["crash"])
    ev, res = r["ev"], r["result"]
    names = [e for e, _ in ev]
    push, create, wc, gend = t_of(ev, "push"), t_of(ev, "create"), t_of(ev, "would-create"), t_of(ev, "guard-end")
    dele = [e for e in names if e.startswith("delete")]
    info = f"result={res} events={' '.join(f'{e}@{t}' for e, t in ev)}"
    if k == "G1":
        return (res == "formatfail" and create is None and push is not None and dele == ["delete refs/heads/L-meta-1"]), info
    if k == "G2":
        return (res == "formatfail" and create is None and not dele), info
    if k == "G3":
        return (res == "formatfail" and push is None and create is None), info
    if k == "G4":
        return (create is not None and gend is not None and push is not None and push < gend <= create), info
    if k == "G5":
        return (res == "formatfail" and wc is None), info
    if k == "G6":
        return (res == "dry" and wc is not None and gend is not None and gend <= wc), info
    if k == "G7":
        return (res == "formatfail" and create is None and push is None), info
    if k == "G8":
        return (res == "exists" and create is None and push is None), info
    return False, "?"


def main():
    sha = subprocess.run(["git", "-C", SRC, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    fails = []
    for k, (case, dry) in CASES.items():
        ok, info = judge(k, child(case, dry))
        print(("ok   " if ok else "FAIL ") + k + " | " + info[:240])
        if not ok:
            fails.append(k)
    print(f"GUARDPAR PASS {sha}" if not fails else f"GUARDPAR FAIL {sha}: " + " ".join(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
