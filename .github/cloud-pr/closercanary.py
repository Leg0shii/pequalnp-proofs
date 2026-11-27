#!/usr/bin/env python3
"""closercanary.py (Lead 08:17, red team UNTESTED row 2): DRY closer passes on the real runner against the real
upstream open list. Closes nothing, pushes nothing (DRY=1: every write in dupclose.py is behind DRY). Prints per pass
loop time and counted REST reads, then `CLOSERCANARY ...` with reads per hour and the token limit.
Env: PASSES (default 12), PR_TOKEN (toolkit reads), READ_TOKEN (the run's token: list reads)."""
import json, os, sys, time
os.environ["DRY"] = "1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dupclose as D

CNT = {"rest": 0, "git": 0, "slow": 0}
real_sh = D.sh


def sh(*a, **k):
    s = " ".join(map(str, a))
    if a[0] == "gh" and "rate_limit" not in s:
        CNT["rest"] += 1
    elif a[0] == "git" and any(x in a for x in ("ls-remote", "fetch", "push")):
        CNT["git"] += 1
    t = time.time()
    r = real_sh(*a, **k)
    if time.time() - t > 10:
        CNT["slow"] += 1
    return r
D.sh = sh


def rl(env):
    r = real_sh("gh", "api", "rate_limit", "--jq", r'.resources.core | "\(.remaining) \(.limit) \(.reset)"', env=env, timeout=20)
    p = r.stdout.split()
    return (int(p[0]), int(p[1])) if len(p) >= 2 and p[0].isdigit() else (None, None)


n = int(os.environ.get("PASSES", "12"))
r0, lim = rl(D.rdenv())
t0 = time.time()
dts, reads = [], []
for i in range(n):
    a, b = time.time(), CNT["rest"]
    D.one_pass()
    dts.append(time.time() - a); reads.append(CNT["rest"] - b)
    allp = D.OPEN.get("prs") or {}
    ours = sum(1 for p in allp.values() if p.get("author") == D.HANDLE)
    print(f"pass {i + 1}: {dts[-1]:.1f}s reads={reads[-1]} open={len(allp)} ours={ours} pages={D.OPEN.get('pages', '-')} "
          f"src={D.OPEN.get('src', '-')} why={D.OPENLIST.get('why', '-')}", flush=True)
    if i < n - 1:
        time.sleep(20)
el = time.time() - t0
r1, _ = rl(D.rdenv())
ph = CNT["rest"] / el * 3600
print(f"CLOSERCANARY passes={n} loop_avg={sum(dts) / n:.1f}s loop_max={max(dts):.1f}s rest={CNT['rest']} git={CNT['git']} "
      f"slow_calls={CNT['slow']} per_hour={ph:.0f} tok=read rl={r1}/{lim} used_by_run={(r0 - r1) if r0 is not None and r1 is not None else '?'} "
      f"open={len(D.OPEN.get('prs') or {})} elapsed={el:.0f}s", flush=True)
