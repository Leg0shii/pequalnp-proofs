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
import os, re, sys, time, json, subprocess, socket

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


# ---- 2026-11-26 audit (owner: never be paused again; Lead review of the cloud lease patch) ----
SLOTS = int(os.environ.get("DESKGUARD_SLOTS", "4"))       # team-wide max held leases (handle cap is 5)
SLOT_STALE_S = 600
HARMLESS = re.compile(r"proved first|already proved|held by another|another handle|at most one handle|cap reached|"
                      r"too many held|limit of \d+ held|"
                      # 10:08 UTC 26 Nov, first real one: {"gap": null, "note": "Another agent was handed this step 1 minutes
                      # ago and gets a head start. Bring your proof back after ..."} = an ordinary refusal, not a pause
                      r"gets a head start|was handed this step|bring your proof back", re.I)


def _ref_sha(ref):
    r = _git("ls-remote", REMOTE, ref)
    if r.returncode != 0: raise RuntimeError("ls-remote failed: " + r.stderr.strip()[:120])
    return (r.stdout.split() or [None])[0]


def _ref_msg(ref):
    r = _git("fetch", "-q", REMOTE, f"+{ref}:refs/dgtmp/x")
    if r.returncode != 0: return None
    return _git("log", "-1", "--format=%ct %B", "refs/dgtmp/x").stdout.strip()


def record_lease(step, lid, terms=None):
    """Write the lease id into claim/<step> (D): a retry or the fallback opener reuses it, never a second claim.
    terms (the grant's level / kind / points / race) go into the same message as compact JSON (Lead 14:36 grants.tsv)."""
    ref = f"refs/heads/claim/{step}"
    try:
        sha = _ref_sha(ref)
        if not sha: return False
        t = (" terms " + json.dumps(terms, separators=(",", ":"))) if isinstance(terms, dict) and terms else ""
        r = _git("push", f"--force-with-lease={ref}:{sha}", REMOTE, f"{_marker('claim ' + step + ' lease ' + str(lid) + t)}:{ref}")
        return r.returncode == 0
    except Exception:
        return False


def lease_of(step):
    """The lease id recorded on claim/<step> (None if none was recorded)."""
    m = _ref_msg(f"refs/heads/claim/{step}")
    mm = re.search(r" lease (\S+)", m or "")
    return mm.group(1) if mm else None


def slot_take(owner, wait=45):
    """One of SLOTS team-wide lease slots (refs/heads/leaseslot/<k>), waiting up to `wait` s (no desk call while
    waiting); a slot older than SLOT_STALE_S is taken over. Returns the ref or None (= PR without a lease)."""
    t0 = time.time()
    while True:
        for k in range(SLOTS):
            ref = f"refs/heads/leaseslot/{k}"
            try:
                if _git("push", f"--force-with-lease={ref}:", REMOTE, f"{_marker('slot ' + owner)}:{ref}").returncode == 0:
                    return ref
            except Exception:
                return None
        for k in range(SLOTS):
            ref = f"refs/heads/leaseslot/{k}"
            m = _ref_msg(ref)
            if m and m.split()[0].isdigit() and time.time() - int(m.split()[0]) > SLOT_STALE_S:
                sha = _git("rev-parse", "refs/dgtmp/x").stdout.strip()
                if _git("push", f"--force-with-lease={ref}:{sha}", REMOTE, f"{_marker('slot ' + owner)}:{ref}").returncode == 0:
                    return ref
        if time.time() - t0 >= wait: return None
        time.sleep(5)


def slot_free(ref):
    if ref:
        try: _git("push", "-q", REMOTE, f":{ref}")
        except Exception: pass


RATE_DEFAULT = int(os.environ.get("DESKGUARD_RATE", "4"))     # team-wide claims per minute (owner pick 09:48 UTC 26 Nov)


def rate():
    """Team-wide claim rate (claims per minute): the newest toolkit ref leaserate/<epoch>_<n> wins (n = 0 stops all
    claims); none = RATE_DEFAULT. Fails closed to RATE_DEFAULT."""
    try:
        r = _git("ls-remote", REMOTE, "refs/heads/leaserate/*")
        best = None
        for l in r.stdout.split("\n"):
            m = re.search(r"/leaserate/(\d+)_(\d+)$", l)
            if m and (best is None or int(m.group(1)) > best[0]):
                best = (int(m.group(1)), int(m.group(2)))
        return best[1] if best else RATE_DEFAULT
    except Exception:
        return RATE_DEFAULT


def rate_take(owner, wait=45, prio=2):
    """One team-wide claim token (cloud opener, PC, backup watcher): tokens are refs ratetok/<minute>/<k>, k < rate(),
    created atomically, so at most rate() claims start in any wall-clock minute across all machines. Token k opens at
    second k * 60 / rate() of its minute (Lead 14:40, join.txt "one request every few seconds at most": 8 a minute =
    one claim start every 7.5 s team-wide, never a burst at the top of the minute). Waits up to `wait` s (no desk call
    meanwhile), then False = PR without a lease. prio 2 (high weight, no rival PR) tries each open token at once,
    prio 1 after 3 s, prio 0 after 6 s, so the better steps get them first. Best effort cleanup of refs over 10 min old."""
    t0 = time.time(); R = rate()
    if R <= 0:
        return False
    step = 60.0 / R
    while True:
        now = time.time(); minute = int(now // 60); into = now - minute * 60
        kc = int(into // step)                       # the slot of this moment; a missed slot is gone (no catch-up burst)
        delay = min({2: 0, 1: 3, 0: 6}.get(prio, 6), step * 0.8)   # inside the slot: prio 2 first, then 1, then 0
        for k in ([kc] if kc < R and into - kc * step >= delay else []):
            ref = f"refs/heads/ratetok/{minute}/{k}"
            try:
                if _git("push", f"--force-with-lease={ref}:", REMOTE, f"{_marker('rate ' + owner)}:{ref}").returncode == 0:
                    _rate_clean(minute)
                    return True
            except Exception:
                return False
        k_next = kc + 1 if into - kc * step >= delay else kc
        nxt = minute * 60 + k_next * step + delay if k_next < R else (minute + 1) * 60 + delay
        if nxt - t0 > wait:
            return False
        time.sleep(max(0.2, nxt - time.time()))


def _rate_clean(minute):
    try:
        r = _git("ls-remote", REMOTE, "refs/heads/ratetok/*")
        old = [l.split()[1] for l in r.stdout.split("\n") if l.strip()
               and re.search(r"/ratetok/(\d+)/", l) and int(re.search(r"/ratetok/(\d+)/", l).group(1)) < minute - 10]
        if old:
            _git("push", "-q", REMOTE, *[":" + x for x in old[:50]])
    except Exception:
        pass


def check_answer(d, what="claim"):
    """Fail closed (A): a desk answer that is a pause/429, or a claim with no lease that is not a known harmless
    refusal, or a non-200 release/beat, sets the shared pause for 15 min. Returns True if the answer was fine."""
    code = str(d.get("_http", "")) if isinstance(d, dict) else ""
    if isinstance(d, dict) and d.get("lease"):
        # a granted lease: only non-empty top-level fields other than the step itself can carry a warning
        # (a good answer with "warnings": [] or a statement text mentioning "repeat" must not pause the team)
        txt = json.dumps({k: v for k, v in d.items() if k not in ("gap", "statement", "title", "lease", "_http")
                          and v not in (None, "", [], {}, 0, False)})
    else:
        txt = json.dumps(d) if not isinstance(d, str) else d
    bad = code == "429" or bool(re.search(r"paus|again and again|repeat|same proof|warn|abuse|slow down", txt, re.I))
    if not bad and what == "claim":
        le = d.get("lease") if isinstance(d, dict) else None
        bad = not le and code != "410" and not HARMLESS.search(txt)
    if not bad and what in ("release", "beat"):
        bad = code not in ("", "200", "410")
    if bad:
        pause(time.time() + 900)
    return not bad


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["acquire"] and len(a) == 2:
        w = []; ok = acquire(a[1], w); print("OK" if ok else "NO", a[1], w[0]); sys.exit(0 if ok else 1)
    if a[:1] == ["pause"] and len(a) == 2:
        sys.exit(0 if pause(float(a[1])) else 1)
    if a[:1] == ["status"]:
        pu = paused_until(); print("paused until", time.strftime("%H:%M:%S UTC", time.gmtime(pu)) if time.time() < pu else "-", "| calls last 10 min here:", len(_calls()), "of", BUDGET); sys.exit(0)
    print(__doc__); sys.exit(2)
