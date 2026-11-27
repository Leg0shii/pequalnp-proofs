#!/usr/bin/env python3
"""lcsummary (lane ci, W8, Lead 08:17 UTC 27 Nov): ONE line a lane pastes into its board file, from a loadcanary drain log.

  lcsummary.py DRAIN_LOG [--sha S] [--head H] [--workers N] [--slots M] [--warm S] [--run ID] [--reads-run A,B] [--reads-pr A,B]
  -> LANE-CI <sha8> head=<h8> w<N>x<M> warm=<S>s first_would_push=<s>s after release, dry=<n>/<done> race_p95=<s>s
     guards_p95=<s>s tree_p95=<s>s total_p95=<s>s results=<res:n,...> alerts=<KIND:n,...|none> reads run=<n> pr=<n> run=<id> verdict=<ok|SLOW|BAD>

first_would_push: the first "DONE ... would push" line, counted from the release ("units released now", WARM_S) or, when
the drain logs no release, from START (the same rule SPEED's parse.py uses). race/guards/tree/total: p95 over the dry
units' TIMES lines ("-" when the stage is not logged). alerts: every ALERT kind with its count. reads: GitHub core used,
from the run token and PR_TOKEN rate_limit before and after the drain (both are upper bounds: the run token's limit is
shared by every job of the repo running meanwhile, PR_TOKEN's by the whole account). tree: the TIMES key tree=, else commit=.
verdict: BAD = a lost unit (fewer would-push than units) or REFRESHER-DEAD / PR-STALL; SLOW = first_would_push or race_p95
worse than the signed baseline (team/infra/preflight.baseline, line "canary first_would_push=<s> race_p95=<s>") by more
than 15% (+1 s); otherwise ok. The baseline is read only when --baseline FILE is given (preflight.sh does that).
"""
import argparse, re, sys

BAD_ALERTS = ("REFRESHER-DEAD", "PR-STALL")


def pct(v, q):
    v = sorted(v)
    return v[min(len(v) - 1, int(q * len(v)))] if v else None


def main(a):
    L = [re.sub(r"^\S+Z ", "", l.rstrip("\n")) for l in open(a.log, errors="replace")]
    L = [l for l in L if "\x1b[36;1m" not in l]                       # the workflow's own script echo
    off = lambda l: int(re.search(r" \+(\d+)s ", l).group(1))
    start = [off(l) for l in L if re.search(r" \+\d+s START ", l)]
    rel = [off(l) for l in L if re.search(r" \+\d+s ", l) and "units released now" in l]
    t0 = rel[0] if rel else (min(start) if start else 0)
    dry = [l for l in L if " would push " in l and " DONE " in l and re.search(r" \+\d+s ", l)]
    T = {}
    for l in L:
        if " TIMES " in l:
            u = re.search(r"TIMES (\S+)", l).group(1)
            T[u] = {k: float(v) for k, v in re.findall(r"(\w+)=([\d.]+)", l)}
    du = [re.search(r"DONE (\S+)", l).group(1) for l in dry]
    g = lambda k: [T[u][k] for u in du if u in T and k in T[u]]
    tree = g("tree") or g("commit")     # submit.py logs the tree build (read-tree of the upstream tree) as commit=
    first = (min(off(l) for l in dry) - t0) if dry else None
    res = {}
    for l in L:
        m = re.search(r" \+\d+s DONE (\S+) (\S+)", l)
        if m:
            res[m.group(2)] = res.get(m.group(2), 0) + 1
    units = sum(res.values())
    if not a.units:                 # released units: the first START line says "(<n> pending)"
        m = next((re.search(r" START \S+ \S+ \((\d+) pending\)", l) for l in L if " START " in l and "pending)" in l), None)
        a.units = m.group(1) if m else None
    al, seen = {}, set()
    for l in L:                     # an alert line: "<hh:mm:ss> +<n>s <KIND> ..." (drain alert(), pushed as a ref too)
        m = re.search(r"^(\d\d:\d\d:\d\d \+\d+s) (?:ALERT )?(REFRESHER-DEAD|PR-STALL-GIVEUP|PR-STALL|SNAP-SLOW|HALT-SLOW|SITE-STATUS-STALE|SITE-CLOSED)\b", l)
        if m and (m.group(1), m.group(2)) not in seen:
            seen.add((m.group(1), m.group(2))); al[m.group(2)] = al.get(m.group(2), 0) + 1
    f = lambda x: "-" if x is None else "%.1fs" % x
    def used(s):
        try:
            b, e = [int(x) for x in s.split(",")]
            return str(b - e) if b >= e else "reset"
        except Exception:
            return "?"
    verdict, why = "ok", []
    if a.units and units < int(a.units):
        verdict = "BAD"; why.append("lost %d of %s (no DONE line)" % (int(a.units) - units, a.units))
    if any(k.startswith(b) for k in al for b in BAD_ALERTS):
        verdict = "BAD"; why.append("alert " + ",".join(k for k in al if k.startswith(BAD_ALERTS)))
    if not dry:
        verdict = "BAD"; why.append("no would-push at all")
    if a.baseline and verdict == "ok":
        try:
            bl = [l for l in open(a.baseline) if l.startswith("canary ")][-1]
            bf = float(re.search(r"first_would_push=([\d.]+)", bl).group(1))
            br = float(re.search(r"race_p95=([\d.]+)", bl).group(1))
            rp = pct(g("race"), .95)
            if first is not None and first > bf * 1.15 + 1:
                verdict = "SLOW"; why.append("first %.0f s > 1.15x%.0f+1" % (first, bf))
            if rp is not None and rp > br * 1.15 + 1:
                verdict = "SLOW"; why.append("race p95 %.1f s > 1.15x%.1f+1" % (rp, br))
        except Exception:
            why.append("no canary baseline")
    line = ("LANE-CI %s head=%s w%sx%s warm=%ss first_would_push=%ss after %s, dry=%d/%d race_p95=%s guards_p95=%s "
            "tree_p95=%s total_p95=%s results=%s alerts=%s reads run=%s pr=%s left=%s reset=%s run=%s verdict=%s%s") % (
        (a.sha or "?")[:8], (a.head or a.sha or "?")[:8], a.workers or "?", a.slots or "?", a.warm or "0",
        "-" if first is None else first, "release" if rel else "START", len(du), units, f(pct(g("race"), .95)),
        f(pct(g("guards"), .95)), f(pct(tree, .95)), f(pct(g("total"), .95)),
        ",".join("%s:%d" % kv for kv in sorted(res.items())) or "none",
        ",".join("%s:%d" % kv for kv in sorted(al.items())) or "none", used(a.reads_run), used(a.reads_pr), a.left or "?", a.reset or "?", a.run or "?",
        verdict, (" (" + "; ".join(why) + ")") if why else "")
    print(line)
    return 0 if verdict == "ok" else 1


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("log"); p.add_argument("--sha"); p.add_argument("--head"); p.add_argument("--workers"); p.add_argument("--slots")
    p.add_argument("--warm"); p.add_argument("--run"); p.add_argument("--reads-run", default=""); p.add_argument("--reads-pr", default="")
    p.add_argument("--left"); p.add_argument("--reset"); p.add_argument("--baseline"); p.add_argument("--units", help="units released (loadtest refs), for the lost check")
    sys.exit(main(p.parse_args()))
