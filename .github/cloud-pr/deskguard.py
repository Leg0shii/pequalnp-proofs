#!/usr/bin/env python3
"""deskguard.py: the one gate every desk call with our handle must pass. Works ACROSS machines (PC watcher, cloud opener,
mirrors, workers) because the lock is a git ref on a remote they all push to; no shared disk needed.

Why: 2026-11-25 18:20 UTC the desk paused our handle for an hour. PC, cloud opener and two mirrors each claimed and
released the same steps; each had its own in-memory 'claimed' set, so none saw the others.

Rules it enforces (PIPELINE.md 4b):
  1. one claim per step, ever, for the whole team: `acquire(step)` creates refs/heads/claim/<step> on the remote with
     --force-with-lease=<ref>: (the ref must not exist). Git makes that atomic: exactly one machine wins, the rest get False.
  2. shared pause: `pause(epoch)` creates refs/heads/deskpause/<epoch>; `acquire` refuses while any such epoch is in the future.
  3. local rate limit: at least GAP seconds between desk calls and at most BUDGET calls per 10 min on this machine.
  4. fail closed: remote unreachable, git error, anything unclear -> False (no desk call). An unheld step still gets its PR.

Use:  from deskguard import acquire, pause, note_call
      if acquire("L-meta-14074"): ...ONE desk request...; note_call()
      answer mentions pause / 429 / 'again and again' -> pause(time.time() + 3600 or the time the desk names)
CLI:  deskguard.py acquire L-meta-N | pause EPOCH | status        (exit 0 = allowed)
Env:  DESKGUARD_REPO = path of a clone whose `origin` is the shared remote (default ~/farm/tk or $WATCH_TK),
      DESKGUARD_GAP (5), DESKGUARD_BUDGET (20), DESKGUARD_HOME (~/.deskguard)."""
import os, sys, time, json, subprocess, socket

REPO = os.environ.get("DESKGUARD_REPO") or os.environ.get("WATCH_TK") or os.path.expanduser("~/farm/tk")
REMOTE = os.environ.get("DESKGUARD_REMOTE", "origin")
GAP = float(os.environ.get("DESKGUARD_GAP", "5")); BUDGET = int(os.environ.get("DESKGUARD_BUDGET", "20"))
HOME = os.environ.get("DESKGUARD_HOME", os.path.expanduser("~/.deskguard")); os.makedirs(HOME, exist_ok=True)
CALLS = os.path.join(HOME, "calls.json")


def _git(*a, timeout=40):
    return subprocess.run(["git", "-C", REPO] + list(a), capture_output=True, text=True, timeout=timeout)


def _marker(msg):
    """A fresh, unique commit (empty tree) to hang a lock ref on. Unique, so pushing onto an existing ref can never be a no-op."""
    t = subprocess.run(["git", "-C", REPO, "mktree"], input="", capture_output=True, text=True, timeout=20).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="deskguard", GIT_AUTHOR_EMAIL="deskguard@localhost", GIT_COMMITTER_NAME="deskguard", GIT_COMMITTER_EMAIL="deskguard@localhost")
    r = subprocess.run(["git", "-C", REPO, "commit-tree", t, "-m", f"{msg} {socket.gethostname()} {time.time()} {os.getpid()} {os.urandom(4).hex()}"],
                       capture_output=True, text=True, timeout=20, env=env)
    if r.returncode != 0 or not r.stdout.strip(): raise RuntimeError("commit-tree failed: " + r.stderr.strip()[:100])
    return r.stdout.strip()


def _calls():
    try: return [t for t in json.load(open(CALLS)) if time.time() - t < 600]
    except Exception: return []


def note_call():
    """Record one desk request made on this machine (for the rate limit). Call it after every desk request."""
    c = _calls() + [time.time()]
    with open(CALLS + ".tmp", "w") as f: json.dump(c, f)
    os.replace(CALLS + ".tmp", CALLS)


def paused_until():
    """Newest shared pause epoch (0 if none). Raises on git failure: callers fail closed."""
    r = _git("ls-remote", REMOTE, "refs/heads/deskpause/*")
    if r.returncode != 0: raise RuntimeError("ls-remote failed: " + r.stderr.strip()[:120])
    ep = [float(l.rsplit("/", 1)[1]) for l in r.stdout.split("\n") if "/deskpause/" in l and l.rsplit("/", 1)[1].replace(".", "").isdigit()]
    return max(ep or [0])


def pause(until_epoch):
    """Tell every machine: no desk call before until_epoch. Safe to call twice."""
    until_epoch = int(until_epoch)
    r = _git("push", REMOTE, f"{_marker('pause')}:refs/heads/deskpause/{until_epoch}")
    return r.returncode == 0 or "rejected" in r.stderr      # rejected = another machine already set the same epoch


def acquire(step, why=None):
    """True = this machine may make ONE desk request for this step. False = somebody already did, we are paused,
    over budget, or the lock remote is unreachable. `why` (a list) receives the reason."""
    def no(msg):
        if why is not None: why.append(msg)
        return False
    try:
        c = _calls()
        if len(c) >= BUDGET: return no(f"budget: {len(c)} desk calls in 10 min on this machine")
        if c and time.time() - max(c) < GAP: time.sleep(GAP - (time.time() - max(c)))
        pu = paused_until()
        if time.time() < pu: return no("desk paused until " + time.strftime("%H:%M:%S UTC", time.gmtime(pu)))
        ref = f"refs/heads/claim/{step}"
        r = _git("push", f"--force-with-lease={ref}:", REMOTE, f"{_marker('claim ' + step)}:{ref}")
        if r.returncode != 0:
            return no("claimed before by another machine or this one" if "stale info" in r.stderr or "rejected" in r.stderr
                      else "lock remote error: " + r.stderr.strip()[-120:])
        if why is not None: why.append("acquired on " + socket.gethostname())
        return True
    except Exception as e:
        return no("guard error (fail closed): " + repr(e)[:120])


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["acquire"] and len(a) == 2:
        w = []; ok = acquire(a[1], w); print("OK" if ok else "NO", a[1], w[0]); sys.exit(0 if ok else 1)
    if a[:1] == ["pause"] and len(a) == 2:
        sys.exit(0 if pause(float(a[1])) else 1)
    if a[:1] == ["status"]:
        pu = paused_until(); print("paused until", time.strftime("%H:%M:%S UTC", time.gmtime(pu)) if time.time() < pu else "-", "| calls last 10 min here:", len(_calls()), "of", BUDGET); sys.exit(0)
    print(__doc__); sys.exit(2)
