#!/usr/bin/env python3
"""oneopener.py (HARDENING section 14, W11, red team V6, fixture Y8): ONE OPENER per unit, cloud drain or PC fallback.

Rule. The PC files ready/<ID> only when
  (1) the fork branch drain-state does not hold <ID> (no seen.txt line for <ID>, any result, the "inflight" line too), AND
  (2) the drain heartbeat is dead: the fork ref drain-beat has not changed for DEAD_S seconds of the PC's OWN monotonic
      clock (the writer's clock is never read, so V5 clock drift cannot decide), AND
  (3) the PC wins the create-only lock refs/heads/oneopener/<ID> on the fork (git decides, no timer).
The drain takes the same lock before the PR. Whoever holds the lock is the one opener of <ID>.

Refs (all on the fork, one channel, one ls-remote per PC evaluation):
  refs/heads/drain-state        seen.txt "step sha result epoch". NEW: the drain writes "step sha inflight epoch" at
                                START, before the claim and the PR, so a slow unit is held from its first second.
  refs/heads/drain-beat         one new commit every BEAT_S (10 s) while a drain run lives (message "beat <run> <n>").
  refs/heads/oneopener/<ID>     create-only (push --force-with-lease=<ref>: = expect absent); message
                                "<kind> <run-or-host> <nonce>", kind = cloud | pc.

Timeout. DEAD_S = 40 s (4 missed beats; GitHub push latency is 1-3 s), so a dead cloud still meets I1 (PR within 60 s). A PC that has just started, or has not seen
drain-beat change yet, starts its own timer at the first reading, so a restart never sees "dead" at once.

Failure modes (each is a case in oneopener_test.py):
  Y8   drain needs 45 s for <ID>: held (inflight) and beat alive -> the PC waits -> one PR.
  Q1   no drain run (runner queue 4 min): not held, beat dead after DEAD_S -> the PC takes the lock and files; the
       drain run that starts later finds the lock (kind pc) and skips -> one PR, filed about DEAD_S + 3 s after the push (I1: under 60 s).
  R1   PC and drain decide in the same instant: the create-only lock lets exactly one through.
  K1   drain killed after "inflight": held, beat dies -> the PC does NOT file (held). The next drain run re-runs
       inflight lines of a dead run: it takes over a lock of kind cloud from another run only with
       --force-with-lease=<ref>:<old sha> and only when no PR of ours exists (exact head lookup) -> one PR.
  U1   drain-state or drain-beat unreadable at the PC -> no filing (fail closed toward the cloud), logged.
  S1   PC host sleep / monotonic jump makes the beat look dead while the drain lives: (1) still holds, and the lock
       stops a second PR even when (1) is missed.
  O1   lock taken, opener died before the PR: the lock stays; a later opener of the SAME kind takes it over as in K1,
       the other kind never does (Lead decides) -> never two PRs, at worst one unit late (alarm: lock without PR > 10 min).
"""
import os, subprocess, time, uuid

STATE_REF = "refs/heads/drain-state"
BEAT_REF = "refs/heads/drain-beat"
LOCK_PREFIX = "refs/heads/oneopener/"
BEAT_S = float(os.environ.get("ONEOPENER_BEAT_S", "10"))
DEAD_S = float(os.environ.get("ONEOPENER_DEAD_S", "40"))


def _git(*a, cwd=None, timeout=60, input=None):
    return subprocess.run(["git", *a], cwd=cwd, capture_output=True, text=True, timeout=timeout, input=input)


def held(seen_txt, sid):
    """drain-state holds <sid>: any seen.txt line for it (inflight, pr, race, failed ...)."""
    return any(l.split()[:1] == [sid] for l in (seen_txt or "").splitlines())


class BeatWatch:
    """Judges drain-beat by the reader's own monotonic clock: dead = the ref value has not changed for DEAD_S since
    this reader first saw that value. None (unreadable) never counts as dead."""

    def __init__(self, dead_s=DEAD_S, clock=time.monotonic):
        self.dead_s, self.clock, self.val, self.since = dead_s, clock, object(), None

    def observe(self, sha):
        now = self.clock()
        if sha is None:
            return
        if sha != self.val:
            self.val, self.since = sha, now

    def dead(self):
        return self.since is not None and self.clock() - self.since >= self.dead_s


def pc_may_file(sid, seen_txt, beat):
    """(ok, why). seen_txt None = drain-state unreadable."""
    if seen_txt is None:
        return False, "drain-state unreadable (fail closed)"
    if held(seen_txt, sid):
        return False, "held by drain-state"
    if not beat.dead():
        return False, "drain heartbeat alive"
    return True, "not held, heartbeat dead"


def read_refs(url, cwd):
    """ONE ls-remote for drain-state + drain-beat + oneopener/*: {ref: sha} or None when unreadable."""
    r = _git("ls-remote", url, STATE_REF, BEAT_REF, LOCK_PREFIX + "*", cwd=cwd)
    if r.returncode:
        return None
    return {ref: sha for sha, ref in (l.split() for l in r.stdout.splitlines() if l.strip())}


def read_seen(url, cwd):
    """seen.txt of drain-state, "" when the branch does not exist, None when unreadable."""
    f = _git("fetch", "-q", "--depth", "1", url, f"+{STATE_REF}:refs/oneopener/state", cwd=cwd)
    if f.returncode:
        r = _git("ls-remote", url, STATE_REF, cwd=cwd)
        return "" if r.returncode == 0 and not r.stdout.strip() else None
    s = _git("show", "refs/oneopener/state:seen.txt", cwd=cwd)
    return s.stdout if s.returncode == 0 else ""


def _commit(cwd, msg):
    tree = _git("mktree", cwd=cwd, input="").stdout.strip()
    env_msg = ["-c", "user.name=Leg0shii", "-c", "user.email=46093332+Leg0shii@users.noreply.github.com"]
    return _git(*env_msg, "commit-tree", tree, "-m", msg, cwd=cwd).stdout.strip()


def acquire(url, cwd, sid, kind, who, over=None):
    """Create refs/heads/oneopener/<sid> (create-only), or take over the exact commit `over`. True = we are the opener."""
    c = _commit(cwd, f"{kind} {who} {uuid.uuid4().hex[:12]}")
    lease = f"--force-with-lease={LOCK_PREFIX}{sid}:{over or ''}"
    r = _git("push", "-q", lease, url, f"{c}:{LOCK_PREFIX}{sid}", cwd=cwd)
    return r.returncode == 0


def lock_owner(url, cwd, sid):
    """(sha, kind, who) of the lock, None when absent, False when unreadable."""
    r = _git("ls-remote", url, LOCK_PREFIX + sid, cwd=cwd)
    if r.returncode:
        return False
    if not r.stdout.strip():
        return None
    sha = r.stdout.split()[0]
    _git("fetch", "-q", url, f"+{LOCK_PREFIX}{sid}:refs/oneopener/lock", cwd=cwd)
    msg = _git("log", "-1", "--format=%s", "refs/oneopener/lock", cwd=cwd).stdout.split()
    return sha, (msg[0] if msg else "?"), (msg[1] if len(msg) > 1 else "?")


def beat(url, cwd, run, n):
    """one heartbeat: a new commit on drain-beat (force; one writer per run, a newer run simply overwrites)."""
    c = _commit(cwd, f"beat {run} {n}")
    return _git("push", "-q", "-f", url, f"{c}:{BEAT_REF}", cwd=cwd).returncode == 0


def drain_take(url, cwd, sid, run, our_pr_exists):
    """Drain side, right before the claim/PR of <sid>: (go, why)."""
    if acquire(url, cwd, sid, "cloud", run):
        return True, "lock taken"
    o = lock_owner(url, cwd, sid)
    if o is False:
        return False, "lock unreadable (fail closed)"
    if o is None:
        return (acquire(url, cwd, sid, "cloud", run), "lock retried")
    sha, kind, who = o
    if kind == "cloud" and who != run and not our_pr_exists(sid):
        return (acquire(url, cwd, sid, "cloud", run, over=sha), "took over lock of dead run " + who)
    return False, f"lock held by {kind} {who}"
