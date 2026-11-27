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
Switches: Actions variables WARM (0 = off), WARM_WINDOW "HHMM-HHMM" UTC (empty = off), WARM_MAX_S (a job's length, up to
18000 = 5 h; the job limit is 6 h), WARM_HANDOVER "HHMM" (the one chosen handover: the job ends at its first idle moment
after it). Variables are fixed at job start, so the LIVE stop is the fork ref warm/off (git ls-remote every 30 s): it
ends the linger within 30 s idle and stops the re-arm. HANDOVER NOW: push a new fork ref warm/handover-<n>: the job
takes no new unit, dispatches the next job (new main, same window) and ends when its in-flight units are done.
The chain ends by itself at the window end, on WARM=0, on a halt (no re-arm), and when a dispatch fails (the next
ready/ push restarts it). Reads while idle: the ready/ listing and halt refs are git (not REST); the refresher's newest
page every 0.8 s is a 304 unless it changed (16.7a); one dispatch call per run. Only a ready/ drain re-arms.""" 
import os, re, subprocess, time

MAX_LINGER = float(os.environ.get("WARM_MAX_S") or 1200)  # Lead 08:26: one job may cover up to 5 h (job limit 6 h)
OFF_EVERY_S = float(os.environ.get("WARM_OFF_EVERY_S", "30"))
REARM_S = float(os.environ.get("WARM_REARM_S", "90"))
POLL_S = float(os.environ.get("WARM_POLL_S", "2"))
clock = time.time                              # the fixture swaps the clock
ST = {"rearmed": False, "dispatches": 0, "rf": None, "stop": None, "log": print, "off_t": -1e18, "off": False,
      "names": None, "ho_seen": None, "handover": False}


def _refs():
    """the fork's refs/heads/warm/* names (one git ls-remote, not a REST read, at most every OFF_EVERY_S).
    None = unreadable."""
    now = clock()
    if now - ST["off_t"] >= OFF_EVERY_S:
        ST["off_t"] = now
        repo = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
        try:
            r = off_ls(f"https://github.com/{repo}.git", "refs/heads/warm/*")
        except Exception:
            r = None
        ST["names"] = None if r is None else {l.split()[1][len("refs/heads/"):] for l in r.splitlines() if len(l.split()) == 2}
        if ST["ho_seen"] is None and ST["names"] is not None:
            ST["ho_seen"] = {n for n in ST["names"] if n.startswith("warm/handover-")}   # old ones: never a handover
    return ST["names"]


def off_ref():
    """fork ref warm/off exists = warm is off NOW. Unreadable counts as off (fail closed toward the old 30 s drain)."""
    n = _refs()
    off = n is None or "warm/off" in n
    if off and not ST["off"]:
        ST["log"]("WARM-OFF", "ref warm/off is set (or warm/* unreadable): no linger past 30 s, no re-arm")
    ST["off"] = off
    return off


def handover_now():
    """HANDOVER NOW (Lead 08:31): a NEW fork ref warm/handover-<anything> (one this job did not see at its start; a seen
    set, no clock compare) makes the job take no new unit, dispatch the next warm job at once (it checks out the
    new main and keeps this job's window) and end when its in-flight units are done."""
    if ST["handover"]:
        return True
    n = _refs()
    if n is None or ST["ho_seen"] is None:
        return False
    new = sorted(x for x in n if x.startswith("warm/handover-") and x not in ST["ho_seen"])
    if new:
        ST["handover"] = True
        ok = dispatch_fn() if not ST["rearmed"] else True
        ST["rearmed"] = True; ST["dispatches"] += 1
        ST["log"]("WARM-HANDOVER", new[0], "no new unit; next warm job", "dispatched" if ok else "dispatch FAILED",
                  "; this job ends when its in-flight units are done")
    return ST["handover"]


def _ls(url, ref):
    r = subprocess.run(["git", "ls-remote", url, ref], capture_output=True, text=True, timeout=30)
    return r.stdout if r.returncode == 0 else None


off_ls = _ls


def handover(now):
    """WARM_HANDOVER "HHMM" UTC: the job hands over at its first idle moment after that time (one chosen handover)."""
    h = os.environ.get("WARM_HANDOVER", "").strip()
    if not re.fullmatch(r"\d{4}", h):
        return None
    t = now - now % 86400 + int(h[:2]) * 3600 + int(h[2:]) * 60
    return t if T_START[0] < t else None


T_START = [time.time()]


def window(now=None):
    """(start, end) epoch of today's window containing now, or None (off, malformed, or outside)."""
    if os.environ.get("WARM", "1") == "0" or off_ref():
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
    t = idle_since or clock()
    end = w[1]
    ho = handover(t)
    if ho is not None:
        end = min(end, ho)
    return max(default, min(want, end - t))


def poll(default):
    return POLL_S if active() else default


def track(rf, start, stop, log=print):
    ST.update(rf=rf, stop=stop, log=log)
    T_START[0] = clock()
    _refs()                                     # the warm/handover-* refs that exist now are old ones
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
                            "-f", f"linger={int(float(os.environ.get('WARM_LINGER', '1200') or 1200))}",
                            "-f", f"window={os.environ.get('WARM_WINDOW', '')}"],      # the next job keeps this window
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
    idle_flag(bool(w) and not busy and bool(idle) and now - idle > IDLE_FLAG_S)


IDLE_FLAG_S = float(os.environ.get("WARM_IDLE_FLAG_S", "10"))


def idle_flag(on):
    """W/refresh.idle exists while the drain has waited idle over IDLE_FLAG_S: a hint for the refresher (submit.py,
    lane alive) to read the rival pages every REFRESH_IDLE_S instead of 0.8 s and to answer a waiter's ask at once.
    Removed at the first START. A refresher that ignores it is unchanged."""
    f = os.path.join(os.environ.get("W", "/tmp"), "refresh.idle")
    try:
        if on and not os.path.exists(f):
            open(f, "w").close(); ST["log"]("WARM-IDLE refresh.idle set (refresher may slow down)")
        elif not on and os.path.exists(f):
            os.remove(f); ST["log"]("WARM-IDLE refresh.idle cleared (work arrived)")
    except OSError:
        pass


dispatch_fn = dispatch
