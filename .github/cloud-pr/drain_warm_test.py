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
  W5 the window end, or WARM=0, ends the chain: no run after it, the last run ends within 35 s"""
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
        self.env_at = []          # (t, key, value): variable changes
        self.d = tempfile.mkdtemp(prefix="warmtest-")

    def apply_env(self):
        for t, k, v in self.env_at:
            if self.clock.t >= t:
                os.environ[k] = v

    def run_drain(self, trigger):
        """one drain job: import the real drain.py fresh, fake its outside calls, run main()"""
        for m in ("drain", "warm", "haltrule"):
            sys.modules.pop(m, None)
        os.environ.update(self.env); self.apply_env()
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
            def disp():
                sim.dispatches += 1
                return True
            W.dispatch_fn = disp
        def dlog(*a):                              # START is logged by _loop at submit time (the virtual clock's now)
            if a and a[0] == "START":
                self.started.append((ck.t, a[1]))
        D.log = dlog
        D.sh = lambda *a, **k: types.SimpleNamespace(returncode=0, stdout="", stderr="")
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
        D.halted = halted
        done = set(sid for _, sid in self.started)

        def pending():
            self.apply_env()
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
    for kind in ("window-end", "WARM=0"):
        s = Sim(DAY + 13 * 3600 + 30 * 60, env_for(mode, linger=1200 if mode == "before" else None))
        t = s.clock.t
        end = DAY + 14 * 3600
        if kind == "WARM=0":
            end = t + 600; s.env_at = [(end, "WARM", "0")]
        s.actions(t + 7200, first_trigger=t)
        after = [r for r in s.runs if r[0] > end + 1]
        last_end = max(r[1] for r in s.runs) - end
        out.append((not after and last_end <= 35, f"{kind}: runs after={len(after)} last run ends {last_end:+.0f} s"))
        os.environ["WARM"] = "1"
    return line("W5", mode, all(o for o, _ in out), "; ".join(n for _, n in out))


if __name__ == "__main__":
    mode = os.environ.get("WARM_TEST_MODE", "rules")
    res = [f(mode) for f in (w1, w2, w3, w4, w5)]
    print("WARMDRAIN", mode, "PASS" if all(res) else "FAIL " + " ".join(f"W{i + 1}" for i, r in enumerate(res) if not r))
    sys.exit(0 if all(res) else 1)
