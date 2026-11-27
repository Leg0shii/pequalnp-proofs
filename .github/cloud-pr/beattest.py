#!/usr/bin/env python3
"""beattest.py [SRC]: Lead 07:53 (closer heartbeat silent 8 min in run 45958164455). Runs SRC's dupclose.py:
 H1 a network call whose helper keeps the pipe open (git -> git-remote-https; here bash + a background sleep) returns
    within timeout + 6 s (subprocess.run's timeout kills only the child and then waits for the pipe);
 H2 while the main loop is stuck in one 12 s call, the beat thread keeps beating (>= 4 beats at 2 s) and the
    beats show loop=STUCK once past STUCK_S, naming the call;
 H3 after the call returns, the beat shows the loop alive again (loop=<small>).
Prints BEATTEST OK <sha16> (exit 0) or BEATTEST FAIL ... (exit 1). No network."""
import hashlib, importlib.util, os, sys, threading, time
SRC = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), "..", ".."))
P = os.path.join(SRC, ".github", "cloud-pr", "dupclose.py")
os.environ.update(DRY="0", MINUTES="1")
spec = importlib.util.spec_from_file_location("dupclose_bt", P)
D = importlib.util.module_from_spec(spec)
sys.path.insert(0, os.path.dirname(P))
spec.loader.exec_module(D)
fails = []
t = time.time()
r = D.sh("bash", "-c", "sleep 25 & sleep 25", timeout=2)
dt = time.time() - t
print(("ok   " if dt < 8 else "FAIL ") + f"H1 hung helper: call returned after {dt:.1f}s (timeout 2 s), rc={r.returncode}")
if dt >= 8:
    fails.append("H1")
beats = []
if not hasattr(D, "beat_loop"):
    print("FAIL H2 no beat thread: the beat is pushed only between passes (none while a call hangs)")
    fails += ["H2", "H3"]
else:
    D.STUCK_S = 5
    stop = [False]
    D.heartbeat("0", "0", True)
    th = threading.Thread(target=D.beat_loop, kwargs={"stop": lambda: stop[0], "every": 2, "push": beats.append}, daemon=True)
    th.start()
    D.sh("bash", "-c", "sleep 12", timeout=60)           # the main loop is in one long call
    n_hang = len(beats)
    stuck = [b for b in beats if "loop=STUCK" in b and "step=bash" in b]
    D.heartbeat("0", "0", True)
    time.sleep(2.5)
    stop[0] = True
    ok2 = n_hang >= 4 and stuck
    print(("ok   " if ok2 else "FAIL ") + f"H2 {n_hang} beats while one call hung 12 s, {len(stuck)} say loop=STUCK: "
          + (stuck[0][:90] if stuck else "-"))
    if not ok2:
        fails.append("H2")
    last = beats[-1] if beats else ""
    ok3 = " loop=" in last and "STUCK" not in last.split(" loop=")[1].split()[0]
    print(("ok   " if ok3 else "FAIL ") + f"H3 loop alive again: {last[:60]}")
    if not ok3:
        fails.append("H3")
sha = hashlib.sha256(open(P, "rb").read()).hexdigest()[:16]
print(("BEATTEST OK " if not fails else f"BEATTEST FAIL {fails} ") + sha)
sys.exit(1 if fails else 0)
