#!/usr/bin/env python3
"""upbase_test.py [dir of submit.py]: red team R2 (Lead 09:22). upbase_ref() with faked git/gh, in a fresh process:
  U1 REST create answers 403: returns None, NO push of the base, upbase.lock free within 1 s, the unit's push goes on
     by the fork-tip path (ls-remote L-* + fetch)
  U2 a second unit within UPBASE_RETRY_S after the refusal: None at once, no REST call
  U3 REST create ok: the ref name, mark written; a later unit makes no call at all
  U4 "Reference already exists": the ref name
Prints one line per case and "UPBASE PASS <sha>" or "UPBASE FAIL <sha>: <cases>". Exit 0 iff PASS."""
import json, os, subprocess, sys, tempfile

SRC = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
CHILD = r'''
import fcntl, json, os, sys, time
sys.path.insert(0, os.environ["UB_SRC"])
import submit as S
mode = os.environ["UB_MODE"]
CALLS = []
cp = lambda o="", rc=0, e="": S.subprocess.CompletedProcess([], rc, o, e)
def run(cmd, timeout=300, env=None, cwd=None):
    CALLS.append(" ".join(cmd[:6] if cmd[0] != "git" else [x for x in cmd if not x.startswith("http.")][:6]))
    if cmd[0] == "gh":
        if mode == "403":
            return cp(rc=1, e="gh: Resource not accessible by integration (HTTP 403)")
        if mode == "exists":
            return cp(rc=1, e="gh: Reference already exists (HTTP 422)")
        return cp("{}")
    if "ls-remote" in cmd:
        return cp("")
    if "push" in cmd:
        return cp()
    return cp()
S.run = run
out = {}
t = time.time(); out["r1"] = S.upbase_ref("a" * 40); out["t1"] = round(time.time() - t, 3)
lk = open(os.path.join(S.SNAP_DIR, "upbase.lock"), "w")
t = time.time()
try:
    fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB); out["lock_free"] = True
except OSError:
    out["lock_free"] = False
lk.close()
out["calls1"] = list(CALLS); CALLS.clear()
out["r2"] = S.upbase_ref("a" * 40); out["calls2"] = list(CALLS); CALLS.clear()
if mode == "403":
    S.push_branch.__globals__["git"] = lambda *a, env=None, timeout=300: (CALLS.append("git " + " ".join(a[:3])), cp("f" * 40 + "\trefs/heads/L-meta-5\n" if a[0] == "ls-remote" else ""))[1]
    S.push_branch("c" * 40, "L-meta-1")
    out["calls_push"] = list(CALLS)
print("UBRESULT " + json.dumps(out))
'''


def child(mode):
    d = tempfile.mkdtemp(prefix="upbase-")
    env = dict(os.environ, UB_SRC=SRC, UB_MODE=mode, W=d, TREE=d, RIVAL_SNAP_DIR=d, PR_TOKEN="drill", READ_TOKEN="drill",
               ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", GITHUB_OUTPUT=os.devnull, DRY="0", PUSH_BATCH_S="0")
    env.pop("GITHUB_ACTIONS", None)
    r = subprocess.run([sys.executable, "-c", CHILD], env=env, capture_output=True, text=True, timeout=60)
    line = [l for l in r.stdout.splitlines() if l.startswith("UBRESULT ")]
    return json.loads(line[-1][9:]) if line else {"crash": (r.stderr or r.stdout).strip().splitlines()[-3:]}


def main():
    sha = subprocess.run(["git", "-C", SRC, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    fails = []
    a = child("403")
    pushed_base = any("push" in c for c in a.get("calls1", []) + a.get("calls2", []))
    ok = "crash" not in a and a["r1"] is None and not pushed_base and a["lock_free"] and a["t1"] < 1.0
    print(("ok   " if ok else "FAIL ") + f"U1 | {json.dumps({k: a.get(k) for k in ('r1', 't1', 'lock_free', 'calls1', 'crash')})[:300]}")
    fails += [] if ok else ["U1"]
    ok = "crash" not in a and a["r2"] is None and not a["calls2"]
    print(("ok   " if ok else "FAIL ") + f"U2 | r2={a.get('r2')} calls2={a.get('calls2')}")
    fails += [] if ok else ["U2"]
    fb = a.get("calls_push", [])
    ok = any("ls-remote" in c for c in fb) and any("fetch" in c for c in fb)
    print(("ok   " if ok else "FAIL ") + f"U1b fork-tip path on refusal | calls={fb}")
    fails += [] if ok else ["U1b"]
    b = child("ok")
    ok = "crash" not in b and b["r1"] == "upbase/aaaaaaaa" and b["r2"] == "upbase/aaaaaaaa" and not b["calls2"]
    print(("ok   " if ok else "FAIL ") + f"U3 | r1={b.get('r1')} r2={b.get('r2')} calls2={b.get('calls2')}")
    fails += [] if ok else ["U3"]
    c = child("exists")
    ok = "crash" not in c and c["r1"] == "upbase/aaaaaaaa"
    print(("ok   " if ok else "FAIL ") + f"U4 | r1={c.get('r1')}")
    fails += [] if ok else ["U4"]
    print(f"UPBASE PASS {sha}" if not fails else f"UPBASE FAIL {sha}: " + " ".join(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
