#!/usr/bin/env python3
"""qdelay (HARDENING 14 W8, BLINDSPOTS B13): Actions queue delay and concurrency, measured, never blocking.

  qdelay.py run            last step of a job (if: always(), so it adds nothing to the filing path): prints
                             QDELAY run=<id> job=<name> queued_to_started=<s>s concurrent_runs=<n> queued_runs=<m>
                           and "QDELAY ALERT ..." plus a ::warning:: when the delay is over QDELAY_ALERT_S (default 60).
                           Exit 0 always (a measurement must never stop filing). Needs `permissions: actions: read`;
                           without it the line says reads=denied (the wiring check below fails on that).
                           GitHub reads: 3 (own run's jobs, in_progress count, queued count). Desk 0. Data host 0.
  qdelay.py wired [ROOT]   offline: every job of the workflows on the filing path (cloud-pr, dupclose, ready-wait, taken,
                           backup, unleased-test, wave) has a "qdelay.py ... run" step with if: always() and actions: read.
                           -> "QDELAY-WIRED OK" or "QDELAY-WIRED FAIL <list>"
  qdelay.py history [N]    from any box: the last N runs of the fork (default 100), queued->started per job, p50 p90 max,
                           count over 60 s, highest number of jobs running at once. GitHub reads: 1 + N/100 + N.
"""
import json, os, re, subprocess, sys, time, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
API = "https://api.github.com/repos/" + FORK
ALERT_S = float(os.environ.get("QDELAY_ALERT_S", "60"))
FILING = ("cloud-pr.yml", "dupclose.yml", "ready-wait.yml", "taken.yml", "backup.yml", "unleased-test.yml", "wave.yml")
READS = [0]


def get(url, tok=None):
    READS[0] += 1
    h = {"Accept": "application/vnd.github+json", "User-Agent": "qdelay"}
    if tok:
        h["Authorization"] = "Bearer " + tok
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=30) as r:
            return r.status, json.loads(r.read())
    except urllib.error.HTTPError as e:
        return e.code, None
    except Exception:
        return 0, None


def ts(v):
    return time.mktime(time.strptime(v[:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone if v else None


def run_mode():
    tok = os.environ.get("GITHUB_TOKEN") or ""
    rid, me = os.environ.get("GITHUB_RUN_ID", ""), os.environ.get("RUNNER_NAME", "")
    st, d = get("%s/actions/runs/%s/jobs?per_page=100" % (API, rid), tok)
    if st != 200:
        print("QDELAY run=%s queued_to_started=unknown reads=denied http=%s (needs permissions: actions: read)" % (rid, st))
        print("::warning::QDELAY unknown for run %s (http %s)" % (rid, st))
        return 0
    jobs = d.get("jobs") or []
    jk = os.environ.get("GITHUB_JOB", "")
    j = next((x for x in jobs if me and x.get("runner_name") == me), None) or \
        next((x for x in jobs if x.get("name") == jk), None) or \
        next((x for x in jobs if x.get("status") == "in_progress"), None) or (jobs[0] if jobs else {})
    c, s = ts(j.get("created_at")), ts(j.get("started_at"))
    delay = (s - c) if (c is not None and s is not None) else None
    _, a = get("%s/actions/runs?status=in_progress&per_page=1" % API, tok)
    _, q = get("%s/actions/runs?status=queued&per_page=1" % API, tok)
    na, nq = (a or {}).get("total_count", "?"), (q or {}).get("total_count", "?")
    line = "QDELAY run=%s job=%s queued_to_started=%s concurrent_runs=%s queued_runs=%s reads=%d" % (
        rid, j.get("name", "?"), ("%.0fs" % delay) if delay is not None else "unknown", na, nq, READS[0])
    print(line)
    if delay is None or delay > ALERT_S:
        print("QDELAY ALERT run=%s queued_to_started=%s over %.0f s" % (rid, delay, ALERT_S))
        print("::warning::QDELAY ALERT queued %s s before start (limit %.0f s), %s runs in progress" % (delay, ALERT_S, na))
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
            f.write(line + "\n")
    return 0


def wired(root):
    import yaml
    bad, ok = [], []
    wfd = os.path.join(root, ".github", "workflows")
    for fn in FILING:
        p = os.path.join(wfd, fn)
        if not os.path.isfile(p):
            continue
        wf = yaml.safe_load(open(p)) or {}
        wperm = wf.get("permissions") or {}
        for jn, job in (wf.get("jobs") or {}).items():
            perm = job.get("permissions", wperm) or {}
            steps = [st for st in (job.get("steps") or []) if st.get("run")]
            if not steps:
                continue
            q = [st for st in steps if re.search(r"qdelay\.py\S*\s+(-\s+)?run\b", st["run"])]
            if not q:
                bad.append("%s:%s no qdelay.py run step" % (fn, jn))
            elif not any("always()" in str(st.get("if", "")) for st in q):
                bad.append("%s:%s qdelay step without if: always()" % (fn, jn))
            elif not (perm == "read-all" or (isinstance(perm, dict) and perm.get("actions") in ("read", "write"))):
                bad.append("%s:%s no actions: read" % (fn, jn))
            else:
                ok.append("%s:%s" % (fn, jn))
    for b in bad:
        print("FAIL", b)
    print("QDELAY-WIRED %s jobs_ok=%d jobs_bad=%d" % ("OK" if not bad else "FAIL", len(ok), len(bad)))
    return 0 if not bad else 1


def pct(v, p):
    v = sorted(v)
    return v[min(len(v) - 1, int(p * len(v)))] if v else None


def history(n):
    tok = os.environ.get("GITHUB_TOKEN") or ""
    runs = []
    for pg in range(1, (n + 99) // 100 + 1):
        st, d = get("%s/actions/runs?per_page=%d&page=%d" % (API, min(100, n), pg), tok)
        if st != 200:
            print("QDELAY-HISTORY FAIL runs list http", st); return 1
        runs += d.get("workflow_runs") or []
    runs = runs[:n]
    per_wf, spans = {}, []
    for r in runs:
        st, d = get("%s/actions/runs/%d/jobs?per_page=100" % (API, r["id"]), tok)
        for j in (d or {}).get("jobs") or []:
            c, s, e = ts(j.get("created_at")), ts(j.get("started_at")), ts(j.get("completed_at"))
            if j.get("conclusion") == "skipped" or c is None or s is None:
                continue
            per_wf.setdefault(r["name"], []).append(s - c)
            spans.append((s, e or time.time()))
    allv = [x for v in per_wf.values() for x in v]
    for name, v in sorted(per_wf.items()):
        print("wf %-14s jobs=%3d p50=%4.0fs p90=%4.0fs max=%4.0fs over60=%d" % (name, len(v), pct(v, .5), pct(v, .9), max(v),
                                                                                  sum(1 for x in v if x > 60)))
    ev = sorted([(s, 1) for s, e in spans] + [(e, -1) for s, e in spans])
    cur = peak = 0; peak_t = None
    for t, k in ev:
        cur += k
        if cur > peak:
            peak, peak_t = cur, t
    t0 = min((s for s, e in spans), default=None)
    print("QDELAY-HISTORY runs=%d jobs=%d window=%s..%s p50=%s p90=%s max=%s over60=%d peak_concurrent_jobs=%d at %s reads=%d" % (
        len(runs), len(allv), time.strftime("%H:%M", time.gmtime(t0)) if t0 else "-",
        runs[0]["created_at"][11:16] if runs else "-", *(("%.0fs" % x) if x is not None else "-" for x in
                                                          (pct(allv, .5), pct(allv, .9), max(allv) if allv else None)),
        sum(1 for x in allv if x > 60), peak, time.strftime("%H:%M:%S", time.gmtime(peak_t)) if peak_t else "-", READS[0]))
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["run"]:
        sys.exit(run_mode())
    if a[:1] == ["wired"]:
        sys.exit(wired(os.path.abspath(a[1]) if len(a) > 1 else os.path.dirname(os.path.dirname(HERE))))
    if a[:1] == ["history"]:
        sys.exit(history(int(a[1]) if len(a) > 1 else 100))
    print(__doc__); sys.exit(2)
