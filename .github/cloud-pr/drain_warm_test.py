#!/usr/bin/env python3
"""drain_warm_test.py (RC-c ALWAYS-WARM DRAIN, W11): the REAL drain.py main()/_loop on a virtual clock, its GitHub and
git calls faked (no network). A scheduler plays GitHub Actions: one drain at a time in group cloud-pr-drain, one
pending run (a newer one replaces it), a cold start of COLD_S (12 s) from trigger to the drain's first poll.
  python3 drain_warm_test.py [CLOUD_PR_DIR]      (default: this directory; pass today's gateway-v1 copy for "before")
Before = today's code: default linger 30 s, or (cases 4, 5) the only way to be warm today, DRAIN_LINGER=1200.
Cases:
  W1 a ready/ ref pushed 60 s into an idle wait gets START within 3 s
  W2 a stop ref during the linger: the drain ends with no START and no re-arm
  W3 two arm dispatches at once: one drain runs (the other waits in the group), one START per unit; every job that
     runs drain.py is in group cloud-pr-drain, and a dispatchable arm path exists
  W4 an idle wave-window hour: warm at least 3300 of 3600 s, counted reads N at most 200 (304s on unchanged pages)
  W5 the window end or the fork ref warm/off (live) ends the chain within 35 s; the variable WARM=0 reaches only the
     next job (variables are fixed at job start), so it ends the chain within one job length
  W6 a 10:00-14:00 window with WARM_MAX_S 5 h and WARM_HANDOVER 1200: two jobs, the one handover at 12:00
  W7 HANDOVER NOW: a new ref warm/handover-<n> ends the job after its in-flight units, the next job runs the new main
  W8 HALT HOLD (Lead 10:13): filing/stop 100 s into a 5 h job, filing/go 60 s later: the job stays up (one run, no
     dispatch), files nothing during the halt, the unit queued during the halt and a unit pushed after the go START
     within 5 s of the go / of their push; a job started DURING a halt holds the same way; warm/off during a hold
     ends it within 35 s. The real drain.halted() runs (its own read cadence) over a faked toolkit ls-remote"""
import importlib, os, shutil, sys, tempfile, threading, types

CODE = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
COLD_S, REFRESH_S, DAY = 12.0, 0.8, 1795737600.0          # DAY = a midnight UTC
T_WIN0 = DAY + 10 * 3600 + 45 * 60                           # window 10:45-14:00 UTC
WINDOW = "1045-1400"


class Clock:
    def __init__(self, t):
        self.t = t
        self.real = importlib.import_module("time")

    def time(self):
        return self.t

    def sleep(self, s):
        self.t += max(s, 0.001)

    def __getattr__(self, k):                     # strftime, gmtime, ...
        return getattr(self.real, k)


class Sim:
    """the world: ready/ pushes, stop refs, refresher accounting, dispatches"""

    def __init__(self, t0, env):
        self.clock = Clock(t0)
        self.pushes = []          # (t, sid)
        self.stop_at = None
        self.started = []         # (t, sid)
        self.rf_live = 0.0; self.rf_on = None
        self.dispatches = 0; self.runs = []      # (start, end, trigger)
        self.env = env
        self.env_at = []          # (t, key, value): variable changes (take effect at the next job start only)
        self.off_at = None        # fork ref warm/off pushed at this time (live stop)
        self.refs_at = []         # (t, name) other warm/* refs (warm/handover-<n>)
        self.mains = []           # (job start, main version the job checked out)
        self.main_v = [(0, "v1")] # (t, version) fork main moves (a hotfix)
        self.d = tempfile.mkdtemp(prefix="warmtest-")
        self.filing = None        # W8: [(t, "filing/stop/<n>" | "filing/go/<n>")] = the real halted() reads these
        self.reads = []           # W8: (t, kind) of the drain's own reads (halt ls-remote, ready/ listing)

    def apply_env(self):
        pass                      # Actions variables are resolved at job start (run_drain), never inside a running job

    def env_at_start(self):
        for t, k, v in self.env_at:
            if self.clock.t >= t:
                os.environ[k] = v

    def run_drain(self, trigger):
        """one drain job: import the real drain.py fresh, fake its outside calls, run main()"""
        for m in ("drain", "warm", "haltrule"):
            sys.modules.pop(m, None)
        os.environ.update(self.env); self.env_at_start()
        os.environ.update(SRC=self.d, W=os.path.join(self.d, "w"), DRAIN_DRY="0", DRAIN_REFRESHER="1", PR_TOKEN="x")
        sys.path.insert(0, CODE)
        try:
            D = importlib.import_module("drain")
        finally:
            sys.path.remove(CODE)
        sim, ck = self, self.clock
        D.time = ck; D.T0 = ck.t
        W = sys.modules.get("warm")
        if W:
            W.clock = ck.time
            W.time = ck
            W.T_START[0] = ck.t
            W.off_ls = lambda url, ref: "".join(f"x\trefs/heads/{n}\n" for t, n in self.refs_at if ck.t >= t) + \
                ("x\trefs/heads/warm/off\n" if self.off_at is not None and ck.t >= self.off_at else "")
            def disp():
                sim.dispatches += 1
                return True
            W.dispatch_fn = disp
        def dlog(*a):                              # START is logged by _loop at submit time (the virtual clock's now)
            if a and a[0] == "START":
                self.started.append((ck.t, a[1]))
        D.log = dlog
        def fsh(*a, **k):
            if self.filing is not None and "refs/heads/filing/*" in a:
                self.reads.append((ck.t, "halt"))
                return types.SimpleNamespace(returncode=0, stdout="".join(f"{'a' * 40}\trefs/heads/{n}\n"
                                                                           for t, n in self.filing if ck.t >= t), stderr="")
            return types.SimpleNamespace(returncode=0, stdout="", stderr="")
        D.sh = fsh
        D.load_seen = lambda: None
        D.linkedin_file = lambda: ""
        D.paused = lambda: False
        D.site_closed = lambda: False
        D.stall_tick = lambda n: None
        D.creates_tick = lambda now=None: None

        def halted():
            self.apply_env()
            h = self.stop_at is not None and ck.t >= self.stop_at
            D._FH[:] = [ck.t, h, "stop ref" if h else ""]
            return h
        if self.filing is None:
            D.halted = halted
        done = set(sid for _, sid in self.started)

        def pending():
            self.apply_env()
            self.reads.append((ck.t, "ready"))
            done.update(sid for _, sid in self.started)
            return [(sid, "a" * 40) for t, sid in self.pushes if t <= ck.t and sid not in done]
        D.pending = pending

        def work(sid, sha):
            return "pr"
        D.work = work

        def rf_start():
            self.rf_on = ck.t
            return object()

        def rf_stop(p):
            if self.rf_on is not None:
                self.rf_live += ck.t - self.rf_on; self.rf_on = None
        D.refresher_start = rf_start; D.refresher_stop = rf_stop
        t_start = ck.t
        self.mains.append((t_start, [v for t, v in self.main_v if t <= t_start][-1]))
        D.main()
        rf_stop(None)
        self.runs.append((t_start, ck.t, trigger))
        return D

    def actions(self, t_end, first_trigger=None):
        """GitHub Actions in one concurrency group: each trigger (dispatch, ready/ push while nothing runs) starts a
        drain COLD_S later; a trigger during a run makes it pending (one pending; the newest replaces it)."""
        q = [(first_trigger, "arm")] if first_trigger is not None else []
        seen_push = set()
        while True:
            ck = self.clock
            # ready/ pushes while no run is active trigger a run (cloud-pr.yml on push)
            for t, sid in self.pushes:
                if sid not in seen_push and t >= ck.t and (not q or t < q[0][0]):
                    q.append((t, "push")); seen_push.add(sid)
            q.sort()
            if not q or q[0][0] > t_end:
                break
            t, why = q.pop(0)
            ck.t = max(ck.t, t) + COLD_S
            d0 = self.dispatches
            self.run_drain(why)
            for t2, sid in self.pushes:            # pushes during this run: their runs were pending, now one starts
                if t2 < ck.t and sid not in seen_push:
                    seen_push.add(sid); q.append((ck.t, "push(pending)"))
            if self.dispatches > d0:
                q.append((ck.t, "dispatch(pending)"))
            q = sorted(set(q))[:1] if q and all(x[0] <= ck.t for x in q) else sorted(set(q))
        shutil.rmtree(self.d, ignore_errors=True)


def env_for(mode, linger=None):
    e = {"WARM": "1", "WARM_WINDOW": WINDOW, "WARM_LINGER": "1200", "DRAIN_MAX_S": "1200", "DRAIN_LINGER": "30"}
    if linger:
        e["DRAIN_LINGER"] = str(linger)
    return e


def line(case, mode, ok, note):
    print(f"{case:3s} {mode:6s} {'PASS' if ok else 'FAIL'} {note}", flush=True)
    return ok


def w1(mode):
    s = Sim(T_WIN0 + 600, env_for(mode))
    s.pushes = [(s.clock.t + 1, "L-meta-1"), (s.clock.t + 13 + 30 + 60, "L-meta-2")]   # 2nd: 60 s after the idle wait began
    s.actions(T_WIN0 + 1200, first_trigger=None)
    st = dict((sid, t) for t, sid in s.started)
    lag = st.get("L-meta-2", 1e9) - s.pushes[1][0]
    return line("W1", mode, lag <= 3, f"push->START {lag:.1f} s (runs {len(s.runs)}: {[r[2] for r in s.runs]})")


def w2(mode):
    s = Sim(T_WIN0 + 600, env_for(mode))
    t = s.clock.t
    s.stop_at = t + 100
    s.pushes = [(t + 110, "L-meta-3")]
    s.actions(t + 400, first_trigger=t)
    started = [sid for _, sid in s.started]
    ends = [round(r[1] - t) for r in s.runs]
    return line("W2", mode, not started and s.dispatches == 0,
                f"starts={started} dispatches={s.dispatches} runs end at +{ends} s (stop at +100)")


def w3(mode):
    import re
    wf = os.path.join(os.path.dirname(os.path.dirname(CODE)), ".github", "workflows")
    jobs, arm = [], False
    for f in sorted(os.listdir(wf)):
        txt = open(os.path.join(wf, f)).read()
        if "drain.py" not in txt:
            continue
        for m in re.finditer(r"group:\s*(\S+)", txt):
            jobs.append((f, m.group(1)))
        disp = "workflow_dispatch" in txt
        if disp and "group: cloud-pr-drain" in txt and f != "cloud-pr.yml":   # cloud-pr's dispatch goes to its `submit` job
            arm = True
    bad = [j for j in jobs if j[1] != "cloud-pr-drain" and "loadtest" not in j[0] and "loadcanary" not in j[0]
           and j[0] in ("cloud-pr.yml", "warm.yml") and "drain" in j[1]]
    s = Sim(T_WIN0 + 600, env_for(mode))
    t = s.clock.t
    s.pushes = [(t + 20, "L-meta-4")]
    s.actions(t + 200, first_trigger=t)            # arm 1; arm 2 at the same instant waits in the group (one pending)
    n4 = sum(1 for _, sid in s.started if sid == "L-meta-4")
    overlap = any(a[0] < b[1] and b[0] < a[1] for i, a in enumerate(s.runs) for b in s.runs[i + 1:])
    return line("W3", mode, arm and not bad and n4 == 1 and not overlap,
                f"arm_path={arm} drain_groups={sorted(set(g for _, g in jobs))} starts(L-meta-4)={n4} overlapping_drains={overlap}")


def w4(mode):
    """idle wave-window hour: REST requests and COUNTED reads (16.7a: an unchanged page is a 304, not counted). Counted =
    each run's first page read (a new job has no ETag yet) + one per rival-page change (CHANGES_H, assumed) + dispatches."""
    s = Sim(T_WIN0 + 900, env_for(mode, linger=1200 if mode == "before" else None))
    t = s.clock.t
    s.actions(t + 3600, first_trigger=t)
    up = sum(min(r[1], t + 3600) - r[0] for r in s.runs)
    req = int(s.rf_live / REFRESH_S) + s.dispatches
    counted = len(s.runs) + s.dispatches
    gaps = [round(b[0] - a[1], 1) for a, b in zip(s.runs, s.runs[1:])]
    return line("W4", mode, up >= 3300 and counted <= 200,
                f"idle hour: warm {up:.0f} of 3600 s, runs {len(s.runs)}, cold gaps {gaps} s; REST requests {req}, "
                f"counted N={counted} + 1 per changed rival page (budget 16.7: fork under 3,000/h)")


def w5(mode):
    out = []
    for kind in ("window-end", "warm/off ref", "WARM=0 variable"):
        s = Sim(DAY + 13 * 3600 + 30 * 60, env_for(mode, linger=1200 if mode == "before" else None))
        t = s.clock.t
        end = DAY + 14 * 3600
        if kind == "warm/off ref":
            end = t + 600; s.off_at = end
        if kind == "WARM=0 variable":
            end = t + 600; s.env_at = [(end, "WARM", "0")]
        s.actions(t + 7200, first_trigger=t)
        after = [r for r in s.runs if r[0] > end + 1]
        last_end = max(r[1] for r in s.runs) - end
        lim = 1200 + COLD_S if kind == "WARM=0 variable" else 35     # a variable reaches only the next job
        n_ok = len(after) <= (1 if kind == "WARM=0 variable" else 0)   # the job already armed starts, sees WARM=0, ends
        out.append((n_ok and last_end <= lim, f"{kind}: runs after={len(after)} last run ends {last_end:+.0f} s"))
        os.environ["WARM"] = "1"
    return line("W5", mode, all(o for o, _ in out), "; ".join(n for _, n in out))


def w6(mode):
    """one job covers a 10:00-14:00 window: WARM_MAX_S 5 h, WARM_HANDOVER 1200 = exactly one handover, at 12:00"""
    e = env_for(mode, linger=18000 if mode == "before" else None)
    e.update(WARM_WINDOW="1000-1400", WARM_MAX_S="18000", DRAIN_MAX_S="18000", WARM_LINGER="18000", WARM_HANDOVER="1200")
    s = Sim(DAY + 10 * 3600, e)
    t = s.clock.t
    s.actions(DAY + 14 * 3600 + 600, first_trigger=t)
    ho = [round((r[1] - DAY) / 3600, 2) for r in s.runs[:-1]]
    up = sum(min(r[1], DAY + 14 * 3600) - r[0] for r in s.runs)
    os.environ.pop("WARM_HANDOVER", None); os.environ.pop("WARM_MAX_S", None)
    ok = len(s.runs) == 2 and abs(s.runs[0][1] - (DAY + 12 * 3600)) <= 3 and max(r[1] for r in s.runs) <= DAY + 14 * 3600 + 35
    return line("W6", mode, ok, f"runs {len(s.runs)}, handovers at {ho} h UTC, warm {up:.0f} of 14400 s")


def w7(mode):
    """HANDOVER NOW: a hotfix lands on main at +600 s of a 5 h job while units stream in (one every 7 s); a new ref
    warm/handover-1 at +610 s: the job takes no new unit, the next job (new main, same window) starts at once and takes
    the rest; no unit twice, none lost, the old warm/handover-0 (there at the job start) is ignored"""
    e = env_for(mode, linger=18000 if mode == "before" else None)
    e.update(WARM_WINDOW="1000-1500", WARM_MAX_S="18000", DRAIN_MAX_S="18000", WARM_LINGER="18000")
    s = Sim(DAY + 10 * 3600, e)
    t = s.clock.t
    s.refs_at = [(0, "warm/handover-0"), (t + 610, "warm/handover-1")]
    s.main_v = [(0, "v1"), (t + 600, "v2-hotfix")]
    s.pushes = [(t + 20 + 7 * k, f"L-meta-{9000 + k}") for k in range(200)]
    s.actions(t + 1800, first_trigger=t)
    by = {}
    for ts, sid in s.started:
        by.setdefault(sid, []).append(ts)
    twice = [k for k, v in by.items() if len(v) > 1]
    lost = [sid for tp, sid in s.pushes if tp <= t + 1700 and sid not in by]
    after = [sid for tp, sid in s.pushes if tp > t + 640 and sid in by]
    j2 = [m for m in s.mains[1:2]]
    last1 = max([ts for ts, _ in s.started if ts <= s.runs[0][1]] or [t]) - t   # job 1's last START (in-flight end varies with threads)
    ok = len(s.runs) >= 2 and last1 <= 610 + 30 + 2 and j2 and j2[0][1] == "v2-hotfix" and not twice and not lost
    os.environ.pop("WARM_MAX_S", None)
    return line("W7", mode, ok, f"job1 last START +{last1:.0f} s, ends +{s.runs[0][1] - t:.0f} s, next job main={j2[0][1] if j2 else '-'}, runs {len(s.runs)}, "
                f"units started {len(by)} (twice {len(twice)}, lost {len(lost)}), after the handover {len(after)}")


def w8(mode):
    e = env_for(mode, linger=18000 if mode == "before" else None)
    e.update(WARM_WINDOW="1000-1500", WARM_MAX_S="18000", DRAIN_MAX_S="18000", WARM_LINGER="18000")
    notes, ok = [], True
    # (a) halt in the middle of a job
    s = Sim(DAY + 10 * 3600, e)
    t = s.clock.t
    stop, go = t + 100, t + 160
    s.filing = [(0, "filing/go/1"), (stop, "filing/stop/2"), (go, "filing/go/3")]
    s.pushes = [(t + 40, "L-meta-8001"), (t + 120, "L-meta-8002"), (go + 3, "L-meta-8003")]
    s.actions(t + 600, first_trigger=t)
    st = dict((sid, ts) for ts, sid in s.started)
    in_halt = [sid for ts, sid in s.started if stop + 12 <= ts < go]
    a_lag, b_lag = st.get("L-meta-8002", 1e9) - go, st.get("L-meta-8003", 1e9) - (go + 3)
    hold = [x for x in s.reads if stop + 12 <= x[0] < go]
    hr = sum(1 for x in hold if x[1] == "halt") * 3600 / max(1, go - stop - 12)
    rr = sum(1 for x in hold if x[1] == "ready") * 3600 / max(1, go - stop - 12)
    a = len(s.runs) == 1 and s.dispatches == 0 and not in_halt and 0 <= a_lag < 5 and 0 <= b_lag < 5
    ok &= a
    notes.append(f"(a) runs {len(s.runs)} dispatches {s.dispatches}, STARTs during the halt {in_halt}, queued unit START "
                 f"go{a_lag:+.1f} s, pushed-after-go unit START push{b_lag:+.1f} s; own reads while holding: halt ls-remote "
                 f"{hr:.0f}/h, ready/ listing {rr:.0f}/h")
    # (b) a job started during a halt
    s = Sim(DAY + 10 * 3600, e)
    t = s.clock.t
    go = t + 100
    s.filing = [(0, "filing/go/1"), (0, "filing/stop/2"), (go, "filing/go/3")]
    s.pushes = [(go + 2, "L-meta-8101")]
    s.actions(t + 400, first_trigger=t)
    st = dict((sid, ts) for ts, sid in s.started)
    lag = st.get("L-meta-8101", 1e9) - (go + 2)
    b = len(s.runs) == 1 and 0 <= lag < 5
    ok &= b
    notes.append(f"(b) started in a halt: runs {len(s.runs)}, unit after the go START push{lag:+.1f} s")
    # (c) warm/off during a hold ends the job
    s = Sim(DAY + 10 * 3600, e)
    t = s.clock.t
    s.filing = [(0, "filing/go/1"), (t + 50, "filing/stop/2")]
    s.off_at = t + 200
    s.actions(t + 900, first_trigger=t)
    end = max(r[1] for r in s.runs) - s.off_at
    c = len(s.runs) == 1 and end <= 35 and not s.started
    ok &= c
    notes.append(f"(c) warm/off during the hold: job ends off{end:+.0f} s")
    return line("W8", mode, ok, "; ".join(notes))


if __name__ == "__main__":
    mode = os.environ.get("WARM_TEST_MODE", "rules")
    res = [f(mode) for f in (w1, w2, w3, w4, w5, w6, w7, w8)]
    print("WARMDRAIN", mode, "PASS" if all(res) else "FAIL " + " ".join(f"W{i + 1}" for i, r in enumerate(res) if not r))
    sys.exit(0 if all(res) else 1)
