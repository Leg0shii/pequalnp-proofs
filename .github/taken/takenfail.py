#!/usr/bin/env python3
"""takenfail (HARDENING section 14, W6, Lead 06:16): failure cases for the taken-list publisher takenpub.py.
Runs the REAL takenpub.py of a checkout (one_pass / State / main) against a fake GitHub REST with a fake clock.
Nothing leaves the box.

Reader rule (submit.py _build_snapshot, A19): a reader trusts the list for every PR created before header - 30 s and
reads the open PRs created after that itself. So a published list is SOUND when every unit touched (title, branch or
file path) by an open PR created before header - 30 s is a row of the list.

Cases (B6 clock skew, B7 consistency, B9 partial failures, B10 process death):
  T1 head-moved        an open rival PR (no unit id) adds a file for unit U after the first pass; the next list is sound
  T2 page-shift        a PR on page 1 closes between the reads of page 1 and page 2 of the open list; the list is sound
  T3 clock-ahead       publisher clock 60 s ahead of GitHub; a PR created 5 s after the pass started is covered
  T4 poison-files      one open PR whose file list always fails (HTTP 422): the list is still published within 3 passes
                       (or that PR is flagged), filing does not stop for every unit
  T5 poison-created    one PR without created_at (B15 drift): the list is still published within 3 passes
  T6 write-fails-once  the output write fails once (mount hiccup): the publisher keeps running, the next pass writes
  T7 killed-mid-pass   the process dies during a pass: the old file stays whole (no truncated list)
  T8 restart-backfill  after a restart (HOURS_BACK 3) an open no-id PR 5 h old is still listed by its file
  python3 takenfail.py [SRC]  -> one line per case, then "TAKENFAIL PASS <sha>" (exit 0) or "TAKENFAIL FAIL <sha>: ..."
"""
import importlib.util, json, os, re, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
T0 = 1795700000.0
REAL_TIME, REAL_SLEEP = time.time, time.sleep     # takenpub uses the global time module: restored after every case


def iso(t):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))


def load(src, out):
    os.environ["TAKEN_OUT"] = out
    spec = importlib.util.spec_from_file_location("takenpub_%d" % time.time_ns(), os.path.join(src, ".github", "taken", "takenpub.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


class World:
    """fake GitHub REST: PRs with state, created_at (GitHub clock), head sha, files; hooks between page reads"""
    def __init__(self, prs):
        self.prs = prs
        self.hook = None            # f(path, page) called after a page is served
        self.files_fail = {}        # number -> message (always fails)
        self.reads = 0

    def __call__(self, path):
        self.reads += 1
        m = re.search(r"pulls/(\d+)/files", path)
        if m:
            n = int(m.group(1))
            if n in self.files_fail:
                raise TP.ReadFail(self.files_fail[n])
            p = next(x for x in self.prs if x["number"] == n)
            return [{"filename": f} for f in p["files"]]
        st = re.search(r"state=(\w+)", path).group(1)
        pg = int(re.search(r"[?&]page=(\d+)", path).group(1))
        rows = sorted([x for x in self.prs if st == "all" or x["state"] == st],
                      key=lambda x: (x.get("created_at") or "", x["number"]), reverse=True)
        out = [{k: v for k, v in x.items() if k != "files"} for x in rows[(pg - 1) * 100:pg * 100]]
        if self.hook:
            self.hook(st, pg)
        return out


def pr(n, created, files=(), title=None, who="rival1", state="open", sha="s0", ref="patch-1"):
    p = {"number": n, "title": title or "Batch of proofs %d" % n, "user": {"login": who}, "head": {"ref": ref, "sha": sha},
         "state": state, "created_at": iso(created), "files": list(files)}
    return p


def fpath(u):
    return "lean/PEqualNP/Outside/%s.lean" % u.replace("-", "_")


def parse(txt):
    lines = txt.splitlines()
    h = lines[0].split()
    return int(h[2]), {l.split()[0]: l.split() for l in lines[1:]}


def unsound(txt, world, unit_of):
    """units an open PR created before header - 30 s touches that the list lacks"""
    hdr, rows = parse(txt)
    miss = []
    for p in world.prs:
        if p["state"] != "open" or not p.get("created_at"):
            continue
        c = TP.ts(p["created_at"])
        if c >= hdr - 30:
            continue
        us = {u for u in (unit_of(f) for f in p["files"]) if u}
        for u in us:
            if u not in rows:
                miss.append(f"{u} (#{p['number']}, {hdr - c:.0f} s before the header)")
    return miss


def clock(m, gh_t, skew=0.0):
    m.time.time = lambda: gh_t[0] + skew


TP = None


def case_T1(src, d):
    m = load(src, os.path.join(d, "t.txt")); globals()["TP"] = m
    g = [T0]; clock(m, g)
    newer = [pr(2000 + i, T0 - 1300 + 10 * i, [fpath("L-meta-%d" % (95100 + i))]) for i in range(120)]   # busy: #600 on page 2
    w = World([pr(600, T0 - 2000, [fpath("L-meta-95001")], sha="a")] + newer)
    m.FAKE = w
    st = m.State(3 * 3600)
    t1 = m.one_pass(st)
    p = w.prs[0]; p["files"].append(fpath("L-meta-95002")); p["head"]["sha"] = "b"   # rival pushes one more file
    g[0] = T0 + 18
    t2 = m.one_pass(st)
    bad = unsound(t2, w, m.unit_of_file) if t2 else ["no list"]
    return bad, f"reads={w.reads}"


def case_T2(src, d):
    m = load(src, os.path.join(d, "t.txt")); globals()["TP"] = m
    g = [T0]; clock(m, g)
    prs = [pr(1000 + i, T0 - 5000 + i * 10, [fpath("L-meta-%d" % (96000 + i))]) for i in range(150)]
    w = World(prs)
    m.FAKE = w
    st = m.State(3 * 3600)
    m.one_pass(st)
    newest_first = sorted(prs, key=lambda x: x["created_at"], reverse=True)
    victim = newest_first[40]                        # on page 1 of the open list

    def hook(stt, pg):
        if stt == "open" and pg == 1 and victim["state"] == "open":
            victim["state"] = "closed"               # closed (not merged) between the page reads
    w.hook = hook
    g[0] = T0 + 61                                   # the next full open scan
    t2 = m.one_pass(st)
    w.hook = None
    bad = unsound(t2, w, m.unit_of_file) if t2 else ["no list"]
    return bad, f"reads={w.reads}"


def case_T3(src, d):
    m = load(src, os.path.join(d, "t.txt")); globals()["TP"] = m
    g = [T0]; clock(m, g, skew=60.0)                 # publisher's clock 60 s ahead of GitHub
    w = World([pr(700, T0 - 900, [fpath("L-meta-97001")])])
    late = pr(701, T0 + 5, [fpath("L-meta-97002")])  # created 5 s after the pass started (GitHub time), listed by
    m.FAKE = w                                       # REST only after the pass read its pages
    st = m.State(3 * 3600)
    g[0] = T0
    t = m.one_pass(st)
    w.prs.append(late)
    bad = unsound(t, w, m.unit_of_file) if t else ["no list"]
    return bad, "skew=+60s"


def case_poison(src, d, kind):
    m = load(src, os.path.join(d, "t.txt")); globals()["TP"] = m
    g = [T0]; clock(m, g)
    prs = [pr(800, T0 - 300, [fpath("L-meta-98001")]), pr(801, T0 - 200, [fpath("L-meta-98002")])]
    if kind == "files":
        w = World(prs); w.files_fail[801] = "http=422 diff too large"
    else:
        prs[1]["created_at"] = None
        w = World(prs)
    m.FAKE = w
    st = m.State(3 * 3600)
    got = []
    for k in range(3):
        g[0] = T0 + 61 * k
        got.append(m.one_pass(st))
    if all(x is None for x in got):
        return ["3 passes, no list: one PR stops the list (and all filing) for every unit"], f"reads={w.reads}"
    t = [x for x in got if x][-1]
    return unsound(t, w, m.unit_of_file), f"reads={w.reads}"


def run_main(m, g, passes):
    """the real main() for a few passes on the fake clock; returns (exception or None)"""
    def slp(s):
        g[0] += s
    m.time.sleep = slp
    m.END = T0 + passes * m.PASS_S + 1
    os.environ["TAKEN_MINUTES"] = "1"
    sys.argv = ["takenpub.py", "3"]
    try:
        m.main()
        return None
    except BaseException as e:
        return e
    finally:
        os.environ.pop("TAKEN_MINUTES", None)


def case_T6(src, d):
    out = os.path.join(d, "t.txt")
    m = load(src, out); globals()["TP"] = m
    g = [T0]; clock(m, g)
    w = World([pr(900, T0 - 300, [fpath("L-meta-99001")])])
    m.FAKE = w
    real_write = m.write
    n = {"w": 0}

    def write(txt):
        n["w"] += 1
        if n["w"] == 2:
            raise OSError(5, "Input/output error (mount)")
        real_write(txt)
    m.write = write
    w.prs.append(pr(901, T0 + 30, [fpath("L-meta-99002")]))     # appears after the failed write
    e = run_main(m, g, 4)
    bad = []
    if e is not None:
        bad.append(f"publisher died on one failed write: {type(e).__name__}: {str(e)[:60]}")
    txt = open(out).read() if os.path.exists(out) else ""
    if "L-meta-99002" not in txt:
        bad.append("no later list with L-meta-99002 (stale until a restart)")
    return bad, f"writes={n['w']}"


def case_T7(src, d):
    out = os.path.join(d, "t.txt")
    open(out, "w").write("# updated %d 00:00:00 steps 1\nL-meta-99100 1 rival1 00:00:00\n" % int(T0 - 10))
    before = open(out).read()
    m = load(src, out); globals()["TP"] = m
    g = [T0]; clock(m, g)
    w = World([pr(950 + i, T0 - 300 + i, [fpath("L-meta-%d" % (99200 + i))]) for i in range(5)])
    calls = {"n": 0}
    base = w.__call__

    class Killed(BaseException):
        pass

    def fake(path):
        calls["n"] += 1
        if calls["n"] == 4:
            raise Killed()                          # SIGKILL in the middle of the pass
        return base(path)
    m.FAKE = fake
    st = m.State(3 * 3600)
    try:
        t = m.one_pass(st)
        if t is not None:
            m.write(t)
    except Killed:
        pass
    after = open(out).read()
    bad = [] if after == before else ["file changed by a killed pass"]
    if os.path.exists(out + ".tmp") and after != before:
        bad.append("partial tmp file")
    return bad, "killed at read 4"


def case_T8(src, d):
    m = load(src, os.path.join(d, "t.txt")); globals()["TP"] = m
    g = [T0]; clock(m, g)
    w = World([pr(960, T0 - 5 * 3600, [fpath("L-meta-99301")])])
    m.FAKE = w
    st = m.State(3 * 3600)                           # a fresh process (restart): backfill of 3 h
    t = m.one_pass(st)
    bad = unsound(t, w, m.unit_of_file) if t else ["no list"]
    return bad, f"reads={w.reads}"


CASES = [("T1-head-moved", case_T1), ("T2-page-shift", case_T2), ("T3-clock-ahead", case_T3),
         ("T4-poison-files", lambda s, d: case_poison(s, d, "files")),
         ("T5-poison-created", lambda s, d: case_poison(s, d, "created")),
         ("T6-write-fails-once", case_T6), ("T7-killed-mid-pass", case_T7), ("T8-restart-backfill", case_T8)]


def main():
    src = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(HERE))
    sha = subprocess.run(["git", "-C", src, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    fails = []
    t = REAL_TIME()
    import io, contextlib
    for name, f in CASES:
        d = tempfile.mkdtemp(prefix="takenfail-")
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf):
                bad, info = f(src, d)
        except Exception as e:
            bad, info = [f"crash {type(e).__name__}: {str(e)[:100]}"], ""
        finally:
            time.time, time.sleep = REAL_TIME, REAL_SLEEP
        print(("ok  " if not bad else "FAIL"), name, "; ".join(bad[:3]) or "sound", "|", info)
        if bad:
            fails.append(name)
    print(f"{REAL_TIME() - t:.0f}s")
    if fails:
        print(f"TAKENFAIL FAIL {sha}: " + ", ".join(fails))
        return 1
    print(f"TAKENFAIL PASS {sha}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
