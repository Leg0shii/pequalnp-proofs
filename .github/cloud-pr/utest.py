#!/usr/bin/env python3
"""utest.py: UNLEASED-TEST opener (Lead 16:14 UTC 26 Nov). Off by default: it runs only while the toolkit ref
refs/heads/utest/on exists, and only from workflow unleased-test.yml (workflow_dispatch, one concurrency group).

Queue: fork branches utest/<ID> (same layout as ready/<ID>: one file ready/<module>.lean on fork main), newest step
first, ONE at a time, at most UTEST_PER_MIN (2) PRs a minute, 4 after 15 min with the pause frozen (Lead 16:24). Each goes through submit.py with UNLEASED_TEST=1: a PR
only if gaps.json (static data host) shows the unit free right then (no pr_open, no pr_numbers, no holder); no lease
and ZERO requests to the desk host of any kind.
Auto-stop, checked before every PR and every 20 s: our paused_until in gaps.json moved after the test began, or our
handle has a new entry in gaps.json "paused" -> the run deletes utest/on and stops (the infra box publishes the bus
alert "STOP unleased-test" when it sees the ref gone). Ends when the queue is empty, after MINUTES, or when the
pause ends (our handle no longer listed as paused).
Env: SRC, W, PR_TOKEN, READ_TOKEN, GITHUB_REPOSITORY (as drain.py)."""
import json, os, runpy, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
D = runpy.run_path(os.path.join(HERE, "drain.py"), run_name="utest")
sh, auth, log, URL = D["sh"], D["auth"], D["log"], D["URL"]
TK = "https://github.com/Leg0shii/pnp-toolkit.git"
ON_REF = "refs/heads/utest/on"
HANDLE = "Leg0shii"
PER_MIN = float(os.environ.get("UTEST_PER_MIN", "2"))
END = time.time() + float(os.environ.get("MINUTES", "50")) * 60
T_START = time.time()
SKIP = set()
RAMP_S = float(os.environ.get("UTEST_RAMP_S", "900")); RAMP_TO = float(os.environ.get("UTEST_RAMP_TO", "4"))


def gaps():
    r = sh("curl", "-sS", "-m", "30", f"https://data.pequalnp.com/data/desk/gaps.json?t={int(time.time())}", timeout=40)
    return json.loads(r.stdout)


def our_pause(gj):
    return next((p.get("paused_until") for p in gj.get("paused") or [] if p.get("handle") == HANDLE), None)


def on():
    r = sh("git", *auth(), "ls-remote", TK, ON_REF, timeout=60)
    return r.returncode == 0 and bool(r.stdout.strip())


def switch_off(why):
    log("STOP unleased-test:", why)
    sh("git", *auth(), "push", "-q", TK, "--delete", ON_REF, timeout=60)


def queue():
    r = sh("git", "ls-remote", URL, "refs/heads/utest/*", timeout=60)
    out = [l.split()[1][len("refs/heads/utest/"):] for l in r.stdout.splitlines() if "\t" in l and "/utest/L-" in l]
    sha = {l.split()[1][len("refs/heads/utest/"):]: l.split()[0] for l in r.stdout.splitlines() if "\t" in l}
    return sorted(((x, sha[x]) for x in out), key=lambda x: -int(x[0].rsplit("-", 1)[1]) if x[0].rsplit("-", 1)[1].isdigit() else 0)


def main():
    os.makedirs(D["W"], exist_ok=True)
    if not on():
        log("utest/on is not set: the unleased test is off, nothing to do")
        return
    gj = gaps()
    base = our_pause(gj)
    log("unleased test start; our paused_until in gaps.json:", base, "(export", gj.get("updated_at"), ")")
    if base is None:
        log("our handle is not paused: the test is for the pause only, nothing to do")
        return
    n, last_pr = 0, 0.0
    # Lead 16:29: start before the freeze. The "moved" auto-stop arms only once our paused_until is the same on two
    # different exports (the first freeze); from then on any move switches the test off.
    armed, prev, last_exp = False, base, gj.get("updated_at")
    while time.time() < END:
        gj = gaps()
        now_p = our_pause(gj)
        if now_p is None:
            log("our handle is no longer paused (export", gj.get("updated_at"), "): test ends,", n, "PRs")
            return
        if gj.get("updated_at") != last_exp:
            last_exp = gj.get("updated_at")
            if not armed and now_p == prev:
                armed, base = True, now_p
                log("FROZEN our paused_until", now_p, "at export", last_exp, "after", n, "PRs: auto-stop armed")
            elif armed and now_p != base:
                switch_off(f"our paused_until moved {base} -> {now_p} at export {last_exp} after {n} PRs")
                return
            prev = now_p
        if not on():
            log("utest/on removed: test stopped after", n, "PRs")
            return
        q = [x for x in queue() if x[0] not in SKIP]
        if not q:
            time.sleep(20)              # the infra box feeds utest/ branches as w12's list refreshes
            continue
        # Lead 16:24: frozen for 15 min of filing -> 4 a minute
        per_min = PER_MIN if time.time() - T_START < RAMP_S else max(PER_MIN, RAMP_TO)
        wait = last_pr + 60.0 / per_min - time.time()
        if wait > 0:
            time.sleep(min(wait, 20))
            continue
        sid, sha = q[0]
        res, why = D["one"](sid, sha, prefix="utest", extra={"UNLEASED_TEST": "1", "NO_LEASE_NO_PR": "0", "LATE_LEASE": "0"})
        log("DONE", sid, res, why)
        if res == "submitted":
            n += 1; last_pr = time.time()
        elif res in ("race", "unleased", "formatfail", "gone"):
            # not free, lost race or a bad file: drop this branch from the queue so the next one runs
            sh("git", *auth(), "push", "-q", URL, "--delete", f"utest/{sid}", timeout=60)
        else:
            SKIP.add(sid)               # error or anything else: keep the branch, skip it in this run
    log("time limit: test ends after", n, "PRs")


if __name__ == "__main__":
    main()
