#!/usr/bin/env python3
"""warm.py (RC-c ALWAYS-WARM DRAIN, Lead 08:10 UTC 27 Nov; SPEED FIRST10.md section c): during the wave window a drain
job is always running and waiting on ready/ refs, so a new ready/ push meets a started job (no 12 s cold start).

drain.py calls four hooks (nothing else changes: same concurrency group cloud-pr-drain, same halt / site / pause
checks before every START, every create still re-checks halt in submit.py, head lock 16.5 unchanged):
  linger(default, idle)      idle seconds before the drain ends: inside the window up to WARM_LINGER (dispatch input,
                             at most 1200) and never past the window end; outside the window the old 30 s.
  poll(default)              idle poll of the ready/ listing: 2 s inside the window (git ls-remote, not a REST read).
  tick(busy, idle, t0, max_s, halted)
                             re-arm: once per run, REARM_S before this run ends (DRAIN_MAX_S or its linger), when
                                 the window is still open after that and filing is not halted, dispatch warm.yml (PR_TOKEN, as backup.yml).
                                 The new run waits in the group and starts when this one ends. A ready/ push run that
                                 replaces it in the group is a drain too and re-arms the same way.
                             The refresher keeps running while the drain waits (rival snapshot and halt copy fresh).
  stop_refresher()           at drain end.
Switches (Actions variables): WARM=0 turns all of it off at once; WARM_WINDOW "HHMM-HHMM" UTC (empty = off).
The chain ends by itself at the window end, on WARM=0, on a halt (no re-arm), and when a dispatch fails (the next
ready/ push restarts it). Reads while idle: the ready/ listing and halt refs are git (not REST); the refresher's newest
page every 0.8 s is a 304 unless it changed (16.7a); one dispatch call per run. Only a ready/ drain re-arms.""" 
import os, subprocess, time

MAX_LINGER = 1200.0
REARM_S = float(os.environ.get("WARM_REARM_S", "90"))
POLL_S = float(os.environ.get("WARM_POLL_S", "2"))
clock = time.time                              # the fixture swaps the clock
ST = {"rearmed": False, "dispatches": 0, "rf": None, "stop": None, "log": print}


def window(now=None):
    """(start, end) epoch of today's window containing now, or None (off, malformed, or outside)."""
    if os.environ.get("WARM", "1") == "0":
        return None
    w = os.environ.get("WARM_WINDOW", "").strip()
    try:
        a, b = w.split("-")
        sa, sb = int(a[:2]) * 3600 + int(a[2:]) * 60, int(b[:2]) * 3600 + int(b[2:]) * 60
    except ValueError:
        return None
    now = clock() if now is None else now
    day = now - now % 86400
    if sb <= sa or not (day + sa <= now < day + sb):
        return None
    return day + sa, day + sb


def active():
    return window() is not None


def linger(default, idle_since=None):
    """idle seconds allowed, counted from idle_since (the drain's idle start): never past the window end"""
    w = window()
    if not w:
        return default
    want = min(MAX_LINGER, max(default, float(os.environ.get("WARM_LINGER", "1200") or 1200)))
    return max(default, min(want, w[1] - (idle_since or clock())))


def poll(default):
    return POLL_S if active() else default


def track(rf, start, stop, log=print):
    ST.update(rf=rf, stop=stop, log=log)
    return rf


def stop_refresher():
    if ST["rf"] is not None and ST["stop"]:
        ST["stop"](ST["rf"])
    ST["rf"] = None


def dispatch():
    """warm.yml on main, through PR_TOKEN (the run token cannot start runs without actions: write)."""
    tok = os.environ.get("PR_TOKEN", "")
    if not tok or os.environ.get("DRAIN_DRY") == "1" or os.environ.get("DRAIN_PREFIX", "ready") != "ready":
        return False
    repo = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
    for k in range(3):
        r = subprocess.run(["gh", "workflow", "run", "warm.yml", "--repo", repo, "--ref", "main",
                            "-f", f"linger={int(float(os.environ.get('WARM_LINGER', '1200') or 1200))}"],
                           env=dict(os.environ, GH_TOKEN=tok), capture_output=True, text=True, timeout=60)
        if r.returncode == 0:
            return True
        time.sleep(3 * (k + 1))
    return False


def tick(busy, idle, t0, max_s, halted, default_linger=30.0):
    """re-arm once per run, REARM_S before DRAIN_MAX_S, inside the window, not halted. The refresher (rival snapshot and
    halt copy) keeps running while the drain waits (Lead 08:17): the first unit meets ready copies; unchanged pages are
    304s (16.7a), so an idle hour costs only the pages that changed."""
    now = clock()
    w = window(now)
    ends = t0 + max_s if not idle else min(t0 + max_s, idle + linger(default_linger, idle))   # this run's end
    if w and not halted and not ST["rearmed"] and ends - now <= REARM_S and w[1] - ends > 30:
        ST["rearmed"] = True
        ok = dispatch_fn()
        ST["dispatches"] += 1
        ST["log"]("WARM-REARM", "next warm run dispatched" if ok else "no dispatch (failed, or a test prefix): the next ready/ push restarts the chain")


dispatch_fn = dispatch
