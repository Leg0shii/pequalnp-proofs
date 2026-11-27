#!/usr/bin/env python3
"""oneopener_test.py (HARDENING 14, W11, red team V6, fixture Y8): one PR of ours per unit with two openers (cloud drain
and PC fallback). Fake world: a local bare git repo is the fork (drain-state, drain-beat and oneopener/<ID> are REAL
refs pushed with real git, so create-only and force-with-lease are decided by git), a fake PR list, a virtual clock.
Nothing leaves the box. Every case runs twice:
  CURRENT  PC: READY_GRACE 30 s from first sighting, then files unless its exact-head lookup sees our PR (watch.py
           1607-1616). Drain: own-PR check at the start of submit.py (open_pr_for_branch, gated by the taken list,
           published TL_LAG s late), PR after D s.
  NEW      oneopener.py: drain writes "inflight" at START, beats every BEAT_S, takes oneopener/<ID> before the PR;
           PC files only when drain-state does not hold <ID>, drain-beat is dead for DEAD_S of its own clock, and it
           wins the lock.
Each line: "<case> <mode> PASS|FAIL prs=<n> ... reads=<PC git reads per tick>". Exit 0 when every NEW case passes.
  python3 oneopener_test.py [--current-only]"""
import os, shutil, subprocess, sys, tempfile, threading

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oneopener as oo

TL_LAG = 60.0      # taken list publisher lag (status/taken)
VIS = 2.0          # our PR is visible to an exact-head lookup 2 s after creation
PR_S = 3.0         # gh pr create takes 3 s
TICK = 5.0         # PC watcher round
GRACE = 30.0       # WATCH_READY_GRACE today
END = 600.0


class World:
    def __init__(self):
        self.d = tempfile.mkdtemp(prefix="oneopener-")
        self.url = os.path.join(self.d, "fork.git")
        subprocess.run(["git", "init", "-q", "--bare", self.url], check=True)
        self.cwd = {}
        for who in ("pc", "cloud", "cloud2"):
            p = os.path.join(self.d, who); os.makedirs(p)
            subprocess.run(["git", "init", "-q", p], check=True)
            self.cwd[who] = p
        self.prs = []           # (sid, opener, created_t)
        self.now = 0.0
        self.reads = 0

    def close(self):
        shutil.rmtree(self.d, ignore_errors=True)

    def create_pr(self, sid, who, t):
        self.prs.append((sid, who, t + PR_S))

    def visible_exact(self, sid, t):                  # PC: exact head lookup
        return any(s == sid and c + VIS <= t for s, _, c in self.prs)

    def visible_taken(self, sid, t):                  # drain: open_pr_for_branch is skipped unless the taken list has it
        return any(s == sid and c + VIS + TL_LAG <= t for s, _, c in self.prs)

    def n(self, sid):
        return sum(1 for s, _, _ in self.prs if s == sid)

    # ---- drain-state written like drain.save_seen (one writer, force) ----
    def push_seen(self, who, lines):
        cwd = self.cwd[who]
        blob = subprocess.run(["git", "hash-object", "-w", "--stdin"], cwd=cwd, input="".join(l + "\n" for l in lines),
                              capture_output=True, text=True).stdout.strip()
        tree = subprocess.run(["git", "mktree"], cwd=cwd, input=f"100644 blob {blob}\tseen.txt\n", capture_output=True,
                              text=True).stdout.strip()
        c = subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", "commit-tree", tree, "-m", "drain state"],
                           cwd=cwd, capture_output=True, text=True).stdout.strip()
        subprocess.run(["git", "push", "-q", "-f", self.url, f"{c}:{oo.STATE_REF}"], cwd=cwd, check=True, capture_output=True)


# ------------------------------------------------------------------ actors

class Drain:
    """one drain run: starts at t0, works on sid for D s, PR at t0 + D (unless killed at kill_t)."""

    def __init__(self, w, mode, sid, t0, D, run="run1", who="cloud", kill_t=None, kill_after_lock=False):
        self.w, self.mode, self.sid, self.t0, self.D, self.run, self.who = w, mode, sid, t0, D, run, who
        self.kill_t, self.kill_after_lock = kill_t, kill_after_lock
        self.state, self.n, self.next_beat, self.skip = "wait", 0, t0, False

    def alive(self, t):
        return self.t0 <= t and (self.kill_t is None or t < self.kill_t) and self.state != "done"

    def step(self, t):
        w = self.w
        if self.state == "wait" and t >= self.t0:
            self.state = "work"
            if self.mode == "current":
                self.skip = w.visible_taken(self.sid, t)
            else:
                w.push_seen(self.who, [f"{self.sid} sha1 inflight 0"])
                if self.kill_after_lock:
                    oo.acquire(w.url, w.cwd[self.who], self.sid, "cloud", self.run)
        if self.mode == "new" and self.alive(t) and t >= self.next_beat:
            oo.beat(w.url, w.cwd[self.who], self.run, self.n); self.n += 1; self.next_beat = t + oo.BEAT_S
        if self.kill_t is not None and t >= self.kill_t and self.state == "work":
            self.state = "dead"
            return
        if self.state == "work" and t >= self.t0 + self.D:
            self.state = "done"
            if self.mode == "current":
                if not self.skip:
                    w.create_pr(self.sid, self.who, t)
            else:
                go, why = oo.drain_take(w.url, w.cwd[self.who], self.sid, self.run,
                                        lambda s: w.visible_exact(s, t))
                if go:
                    w.create_pr(self.sid, self.who, t)
                w.push_seen(self.who, [f"{self.sid} sha1 {'pr' if go else 'skip'} 0"])


class PC:
    def __init__(self, w, mode, sid, t_seen, url=None, jump_at=None, jump=0.0):
        self.w, self.mode, self.sid, self.t_seen = w, mode, sid, t_seen
        self.url = url or w.url
        self.first, self.done, self.filed_t = None, False, None
        self.jump_at, self.jump, self.offset = jump_at, jump, 0.0
        self.beat = oo.BeatWatch(clock=lambda: self.w.now + self.offset)
        self.state_sha, self.seen = object(), None
        self.reads_ticks = []

    def tick(self, t):
        if self.done or t < self.t_seen:
            return
        if self.jump_at is not None and t >= self.jump_at and not self.offset:
            self.offset = self.jump            # host sleep: monotonic clock leaps
        if self.mode == "current":
            self.first = self.first if self.first is not None else t
            if t - self.first < GRACE:
                return
            if not self.w.visible_exact(self.sid, t):
                self.w.create_pr(self.sid, "pc", t); self.filed_t = t
            self.done = True
            return
        reads = 1
        refs = oo.read_refs(self.url, self.w.cwd["pc"])
        if refs is None:
            self.beat.observe(None); self.seen = None
        else:
            self.beat.observe(refs.get(oo.BEAT_REF, "absent"))
            st = refs.get(oo.STATE_REF)
            if st != self.state_sha:                       # fetch seen.txt only when drain-state moved
                self.seen = oo.read_seen(self.url, self.w.cwd["pc"]) if st else ""; reads += 1
                self.state_sha = st
            if oo.LOCK_PREFIX + self.sid in refs:          # someone is the opener already
                self.done = True
        self.reads_ticks.append(reads)
        if self.done:
            return
        ok, why = oo.pc_may_file(self.sid, self.seen, self.beat)
        if ok and oo.acquire(self.url, self.w.cwd["pc"], self.sid, "pc", "pc-host"):
            self.w.create_pr(self.sid, "pc", t); self.filed_t = t; self.done = True


def simulate(w, drains, pc):
    t = 0.0
    while t <= END:
        w.now = t
        for d in drains:
            d.step(t)
        if t % TICK == 0:
            pc.tick(t)
        t += 1.0


# ------------------------------------------------------------------ cases

def case_Y8(mode):
    """cloud drain takes 45 s for U, PC fallback grace 30 s -> exactly ONE PR of ours on U"""
    w = World(); d = Drain(w, mode, "L-u-1", 0, 45); pc = PC(w, mode, "L-u-1", 0)
    simulate(w, [d], pc); return w, pc, w.n("L-u-1") == 1, ""


def case_Q1(mode):
    """no drain run for 240 s (runner queue), then a 10 s run -> one PR, and filed within DEAD_S + 10 s (I1/I8)"""
    w = World(); d = Drain(w, mode, "L-u-2", 240, 10); pc = PC(w, mode, "L-u-2", 0)
    simulate(w, [d], pc)
    first = min([c for s, _, c in w.prs if s == "L-u-2"] or [1e9])
    return w, pc, w.n("L-u-2") == 1 and first <= oo.DEAD_S + 10 + PR_S, f"first_pr_t={first:.0f}"


def case_R1(mode):
    """drain reaches the PR in the very round the PC decides -> one PR"""
    w = World()
    t_dec = GRACE if mode == "current" else oo.DEAD_S
    d = Drain(w, mode, "L-u-3", t_dec - 1, 1); pc = PC(w, mode, "L-u-3", 0)
    if mode == "new":                    # make both openers race for the lock in two threads at the same instant
        res = []
        th = [threading.Thread(target=lambda k=k: res.append(oo.acquire(w.url, w.cwd[k], "L-u-3", k, k))) for k in ("pc", "cloud")]
        [x.start() for x in th]; [x.join() for x in th]
        for k, ok in zip(("a", "b"), res):
            if ok:
                w.create_pr("L-u-3", k, 0)
        return w, pc, w.n("L-u-3") == 1, f"lock_winners={sum(res)}"
    simulate(w, [d], pc); return w, pc, w.n("L-u-3") == 1, ""


def case_K1(mode, after_lock=False):
    """drain killed 20 s into U (before the PR), next drain run at 300 s -> one PR, none from a second opener"""
    w = World()
    d1 = Drain(w, mode, "L-u-4", 0, 45, run="run1", kill_t=20, kill_after_lock=after_lock)
    d2 = Drain(w, mode, "L-u-4", 300, 10, run="run2", who="cloud2")
    pc = PC(w, mode, "L-u-4", 0)
    simulate(w, [d1, d2], pc)
    return w, pc, w.n("L-u-4") == 1, ""


def case_U1(mode):
    """drain-state and drain-beat unreadable at the PC while the drain works -> the PC files nothing"""
    w = World(); d = Drain(w, mode, "L-u-5", 0, 45)
    pc = PC(w, mode, "L-u-5", 0, url=os.path.join(w.d, "missing.git"))
    simulate(w, [d], pc)
    return w, pc, not any(o == "pc" for s, o, _ in w.prs if s == "L-u-5"), ""


def case_S1(mode):
    """PC monotonic clock leaps 1 h at t=20 while the drain needs 45 s -> one PR"""
    w = World(); d = Drain(w, mode, "L-u-6", 5, 45); pc = PC(w, mode, "L-u-6", 0, jump_at=20, jump=3600)
    simulate(w, [d], pc); return w, pc, w.n("L-u-6") == 1, ""


def case_R15(mode):
    """14 drain workers + the PC go for the same unit in the same instant -> exactly one lock winner, one PR"""
    w = World(); pc = PC(w, mode, "L-u-7", 0)
    if mode == "current":                 # no lock exists today: nothing to replay
        return w, pc, None, "no lock in the current code"
    for k in range(15):
        p = os.path.join(w.d, f"o{k}"); os.makedirs(p); subprocess.run(["git", "init", "-q", p], check=True); w.cwd[f"o{k}"] = p
    res = {}
    th = [threading.Thread(target=lambda k=k: res.__setitem__(k, oo.acquire(w.url, w.cwd[f"o{k}"], "L-u-7", "cloud", f"o{k}"))) for k in range(15)]
    [x.start() for x in th]; [x.join() for x in th]
    for k, ok in res.items():
        if ok:
            w.create_pr("L-u-7", f"o{k}", 0)
    return w, pc, w.n("L-u-7") == 1 and sum(res.values()) == 1, f"lock_winners={sum(res.values())}"


CASES = [("Y8", case_Y8), ("Q1", case_Q1), ("R1", case_R1), ("K1", case_K1),
         ("K1-lock", lambda m: case_K1(m, after_lock=True)), ("U1", case_U1), ("S1", case_S1), ("R15", case_R15)]


def main():
    modes = ["current"] if "--current-only" in sys.argv else ["current", "new"]
    bad_new = []
    for name, fn in CASES:
        for mode in modes:
            w, pc, ok, extra = fn(mode)
            rt = pc.reads_ticks
            reads = f"reads={sum(rt) / len(rt):.2f}/tick max={max(rt)}" if rt else "reads=0"
            who = ",".join(f"{o}@{c:.0f}" for s, o, c in w.prs)
            print(f"{name:8s} {mode:7s} {'N/A' if ok is None else 'PASS' if ok else 'FAIL'} prs={len(w.prs)} [{who}] {extra} {reads}".rstrip(), flush=True)
            if mode == "new" and not ok:
                bad_new.append(name)
            w.close()
    if "new" in modes:
        print("ONEOPENER", "PASS" if not bad_new else "FAIL " + " ".join(bad_new))
    sys.exit(1 if bad_new else 0)


if __name__ == "__main__":
    main()
