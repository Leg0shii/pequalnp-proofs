#!/usr/bin/env python3
"""TAKEN LIST publisher (A19, 27 Nov; W6 fixes T1-T6, R2 and HARDENING 16.7): which units already have a PR from anyone,
from the REST pulls API (no search API: its index lags minutes). taken.yml publishes taken.txt and open.json on toolkit
branch status/taken. takenpub is the ONE reader of upstream's open list (16.7 b): openers and the closer read its files.

taken.txt line 1: '# updated <epoch> <HH:MM:SS> steps N [partial <epoch>] [skipped <n>,<n>] rl <remaining> <reset>',
then one line per unit '<unit> <first PR number> <author> <created HH:MM:SS>' (the lowest PR number that touches the unit).
Readers use split()[2] and 'steps N' only, so the extra tokens are safe.
  <epoch>   GitHub's Date header of the first answer of the pass, minus 1 s (not the local clock, T3): every PR created
            before it is in the list (REST has no lag), so a reader needs only the PRs created after it.
  partial   after a restart with more new PRs than MAX_PAGES pages (R2), CLOSED PRs created before <epoch> may be missing
            (open PRs are always complete); later passes catch up CATCHUP_PAGES pages each and drop the token.
  skipped   PRs whose data could not be read in full (files 422/404/410, bad json, no created_at): the units known for them
            (title, branch, readable files) are still listed; one bad PR never stops the list (T4, T5).
  rl        the token's remaining reads and reset epoch from the last answer (16.7 d).
open.json: {"t": header epoch, "full_t": GitHub time of the last full open sweep, "rl": remaining, "skipped": [n],
"prs": [[n, author, head sha, created epoch, [units]], ...]} for every open PR.

A PR touches a unit when its title or branch names the unit id as a whole token, or when it adds or changes the file
lean/PEqualNP/Outside/<unit with _>.lean (or V_<...>__k<K>.lean of a value step). File paths are read for EVERY open
PR, cached per PR number and head sha (and seeded from the last open.json after a restart: TAKEN_SEED). Closed and merged
PRs from the last HOURS_BACK hours count by title and branch.

Reads (every list page is conditional, If-None-Match: an unchanged page answers 304 and costs nothing):
  every pass   page 1 of state=all by update (new PRs, new heads T1, closes, merges; more pages only after a burst) and
               page 1 of state=all by creation;
  every SWEEP_S (300 s)  all open pages, oldest first, after the pass is published; an open PR missing from the sweep is
               read by number before it is dropped (page shift, T2); the first sweep is read twice and compared.
FAIL CLOSED: a failed list read in a pass means the list is not rewritten that pass, so its header goes stale and every
reader stops filing by itself. A failed write is retried and never stops the publisher (T6).
Token: GH_SEARCH_TOKEN (the run's GITHUB_TOKEN). Run: python3 takenpub.py [HOURS_BACK=3]   selftest: takenpub.py selftest"""
import calendar, email.utils, json, os, re, subprocess, sys, time

UP = "open-goat/pequalnp-proofs"
OUT = os.environ.get("TAKEN_OUT", "/mnt/project-files/team/lead/taken.txt")
OPEN_OUT = os.environ.get("TAKEN_OPEN_OUT") or os.path.join(os.path.dirname(OUT) or ".", "open.json")
SEED = os.environ.get("TAKEN_SEED", "")
TOKEN = os.environ.get("GH_SEARCH_TOKEN", "")
END = time.time() + float(os.environ.get("TAKEN_MINUTES", "0") or 0) * 60   # 0 = forever
PASS_S = 18
SWEEP_S = float(os.environ.get("TAKEN_SWEEP_S", "300"))
MAX_PAGES, CATCHUP_PAGES, OPEN_PAGES, UPD_PAGES, MARGIN = 30, 10, 150, 30, 120
TOKEN_RX = re.compile(r"(?<![A-Za-z0-9_-])(L-[a-z0-9]+(?:-[a-z0-9]+)*-\d+)(?![A-Za-z0-9_-])")
FILE_RX = re.compile(r"lean/PEqualNP/Outside/(L_[a-z0-9]+(?:_[a-z0-9]+)*_\d+|V_[a-z0-9]+(?:_[a-z0-9]+)*_\d+__k\d+)\.lean")
READS = {"n": 0, "req": 0}          # n: counted reads (a 304 is free), req: all requests
RL = {"rem": None, "reset": None}
LAST = {"date": None}               # GitHub Date of the newest answer
PASS = {"date": None}               # GitHub Date of the first answer of the current pass
ETAGS = {}                          # list path -> (etag, rows)
FAKE = None                         # tests: FAKE(path) -> rows, or FAKE.cond(path, etag) -> (code, rows, etag)
FAKE_DATE = None                    # tests: GitHub's clock
SKIP_CODES = {404, 410, 422}


def log(*a):
    print(time.strftime("%H:%M:%S", time.gmtime()), *a, flush=True)


class ReadFail(Exception):
    def __init__(self, msg, code=None):
        super().__init__(msg)
        if code is None:
            m = re.search(r"http=(\d{3})", str(msg))
            code = int(m.group(1)) if m else 0
        self.code = code


class Skip(Exception):
    """one PR's data cannot be read (named in the header, never stops the list)"""


def _date(t):
    LAST["date"] = t
    if PASS["date"] is None:
        PASS["date"] = t


def api(path):
    """GET https://api.github.com/<path>; raises ReadFail on any error (fail closed). List pages are conditional."""
    READS["req"] += 1
    cache = "/files" not in path
    old = ETAGS.get(path) if cache else None
    if FAKE:
        if hasattr(FAKE, "cond"):
            code, rows, tag = FAKE.cond(path, old[0] if old else None)
        else:
            code, rows, tag = 200, FAKE(path), None
        _date(FAKE_DATE() if FAKE_DATE else time.time())
        if code == 304 and old:
            return old[1]
        READS["n"] += 1
        RL["rem"], RL["reset"] = 5000 - READS["n"], 0
        if cache and tag:
            ETAGS[path] = (tag, rows)
        return rows
    r = subprocess.run(["curl", "-sS", "-m", "25", "-w", "\n%{http_code}\t%header{etag}\t%header{date}\t"
                        "%header{x-ratelimit-remaining}\t%header{x-ratelimit-reset}", "-H", "Accept: application/vnd.github+json"]
                       + (["-H", "Authorization: Bearer " + TOKEN] if TOKEN else [])
                       + (["-H", "If-None-Match: " + old[0]] if old else []) + ["https://api.github.com/" + path],
                       capture_output=True, text=True)
    body, _, tail = r.stdout.rpartition("\n")
    f = tail.split("\t")
    if r.returncode or len(f) < 5:
        raise ReadFail(f"{path[:60]} -> rc={r.returncode}")
    code = f[0]
    if f[3].isdigit():
        RL["rem"], RL["reset"] = int(f[3]), int(f[4]) if f[4].isdigit() else 0
    if code == "304" and old:
        rows = old[1]
    elif code == "200":
        READS["n"] += 1
        try:
            rows = json.loads(body)
        except ValueError:
            raise ReadFail(f"{path[:60]} -> bad json", -1)
        if cache and f[1]:
            ETAGS[path] = (f[1], rows)
    else:
        raise ReadFail(f"{path[:60]} -> http={code}", int(code) if code.isdigit() else 0)
    try:
        _date(email.utils.parsedate_to_datetime(f[2]).timestamp())
    except (TypeError, ValueError, IndexError):
        raise ReadFail(f"{path[:60]} -> no Date header")
    return rows


def ts(v):
    return calendar.timegm(time.strptime(v[:19], "%Y-%m-%dT%H:%M:%S"))


def ts_or_none(v):
    try:
        return ts(v)
    except (TypeError, ValueError):
        return None


def unit_of_file(f):
    m = FILE_RX.fullmatch(f or "")
    if not m:
        return None
    s = m.group(1)
    if s.startswith("V_"):
        s = "L_" + s[2:].split("__k")[0]
    return s.replace("_", "-")


def units_named(p):
    t = p.get("title")
    r = (p.get("head") or {}).get("ref")
    return set(TOKEN_RX.findall(t if isinstance(t, str) else "")) | \
        set(TOKEN_RX.findall((r if isinstance(r, str) else "").replace("_", "-")))


FILES = {}      # (number, head sha) -> [units by file path], or ("skip", reason)


def file_units(p):
    k = (p["number"], (p.get("head") or {}).get("sha") or "")
    if k not in FILES:
        us, pg = set(), 1
        try:
            while True:
                fs = api(f"repos/{UP}/pulls/{p['number']}/files?per_page=100&page={pg}")
                if not isinstance(fs, list):
                    raise ReadFail(f"files of #{p['number']}: not a list", -1)
                us |= {u for u in (unit_of_file(f.get("filename")) for f in fs if isinstance(f, dict)) if u}
                if len(fs) < 100 or pg >= 30:            # GitHub lists at most 3000 files per PR
                    break
                pg += 1
        except ReadFail as e:
            if e.code not in SKIP_CODES and e.code != -1:
                raise                                    # 403/429/5xx/timeouts: the pass fails (fail closed)
            FILES[k] = ("skip", str(e)[:80])
        else:
            FILES[k] = sorted(us)
    v = FILES[k]
    if isinstance(v, tuple):
        raise Skip(v[1])
    return v


def listpage(state, sort, pg, direction="desc"):
    rows = api(f"repos/{UP}/pulls?state={state}&sort={sort}&direction={direction}&per_page=100&page={pg}")
    if not isinstance(rows, list):
        raise ReadFail(f"pulls?state={state}&sort={sort}: not a list")
    return rows


def oldest(rows, key, fallback=None):
    vs = [v for v in (ts_or_none(p.get(key) or (p.get(fallback) if fallback else None))
                      for p in rows if isinstance(p, dict)) if v is not None]
    return min(vs) if vs else None


class State:
    def __init__(self, back_s):
        self.since = time.time() - back_s
        self.seen = {}          # number -> {"n", "who", "sha", "created", "units" (title/branch)}
        self.open = {}          # number -> units by file path (open PRs only)
        self.bad = {}           # number -> why its data is incomplete (named in the header)
        self.backfilled = False
        self.mark = None        # GitHub time of the last by-update scan (the next one reads back to mark - MARGIN)
        self.cpg = None         # next by-creation page to catch up (R2), None when complete
        self.cover = None       # oldest creation time read so far by the catch-up
        self.full_t = None      # GitHub time of the last full open sweep
        self.sweep_local = 0.0
        self.seed()

    def seed(self):
        """file units of open PRs from the last open.json (TAKEN_SEED): a restart re-reads only the heads that moved"""
        if not SEED:
            return
        try:
            d = json.load(open(SEED))
            bad = set(d.get("skipped") or [])
            k = 0
            for n, who, sha, created, units in d.get("prs") or []:
                if isinstance(n, int) and sha and n not in bad and isinstance(units, list):
                    FILES[(n, sha)] = sorted(u for u in units if isinstance(u, str))
                    k += 1
            log("seeded", k, "heads from", SEED)
        except (OSError, ValueError, TypeError) as e:
            log("seed ignored:", str(e)[:80])

    def take(self, p):
        """one row of a list page (or one PR read by number); newest read wins"""
        if not isinstance(p, dict) or not isinstance(p.get("number"), int):
            log("row without a PR number ignored")
            return
        n = p["number"]
        self.bad.pop(n, None)
        c = ts_or_none(p.get("created_at"))
        if c is None:
            self.bad[n] = "no created_at"
        is_open = p.get("state") == "open"
        if c is None or c >= self.since or is_open:
            u = p.get("user")
            who = u.get("login") if isinstance(u, dict) else None
            self.seen[n] = {"n": n, "who": who if isinstance(who, str) and who else "?",
                            "sha": (p.get("head") or {}).get("sha") or "", "created": c, "units": units_named(p)}
        if is_open:
            try:
                self.open[n] = file_units(p)
            except Skip as e:
                self.bad[n] = str(e)
                self.open.setdefault(n, [])
        else:
            self.open.pop(n, None)
            if c is not None:
                self.bad.pop(n, None)

    def scan_updated(self):
        """state=all by update, newest first, back to the previous scan (minus MARGIN): new PRs, new head shas, closes.
        A PR updated while the pages are read moves up to page 1 (seen next pass); nothing moves down past a read page."""
        stop = self.mark - MARGIN
        start = None
        for pg in range(1, UPD_PAGES + 1):
            rows = listpage("all", "updated", pg)
            if start is None:
                start = LAST["date"]
            for p in rows:
                self.take(p)
            o = oldest(rows, "updated_at", "created_at")
            if len(rows) < 100 or (o is not None and o < stop):
                self.mark = start
                return
        raise ReadFail(f"over {UPD_PAGES} pages of updates")

    def scan_created(self, first, pages):
        """state=all by creation, newest first, pages first..; returns the next page to read, or None once it reached
        HOURS_BACK (new PRs push rows down: a later page overlaps, never skips)"""
        for pg in range(first, first + pages):
            rows = listpage("all", "created", pg)
            for p in rows:
                self.take(p)
            o = oldest(rows, "created_at")
            if len(rows) < 100 or (o is not None and o < self.since):
                return None
            if o is not None:
                self.cover = o
        return first + pages

    def _list_open(self):
        got, t = {}, None
        for pg in range(1, OPEN_PAGES + 1):
            rows = listpage("open", "created", pg, "asc")      # oldest first: a new PR changes only the last page
            t = t or LAST["date"]
            for p in rows:
                if isinstance(p, dict) and isinstance(p.get("number"), int):
                    got[p["number"]] = p
            if len(rows) < 100:
                return got, t
        raise ReadFail(f"over {OPEN_PAGES} pages of open PRs")

    def sweep(self, twice=False):
        """every open PR (all pages). Key by number (T2): a PR we hold as open that the sweep did not list is read by
        number and dropped only if that read says closed or gone."""
        got, t = self._list_open()
        doubt = set(self.open) - set(got)
        if twice:
            again = self._list_open()[0]
            doubt |= set(got) ^ set(again)
            got.update(again)
        for p in got.values():
            self.take(p)
        for n in sorted(doubt - set(got)):
            try:
                self.take(api(f"repos/{UP}/pulls/{n}"))
            except ReadFail as e:
                if e.code not in (404, 410):
                    raise
                self.open.pop(n, None)
        self.full_t = t
        self.sweep_local = time.time()

    def rows(self):
        first = {}
        for v in self.seen.values():
            for u in set(v["units"]) | set(self.open.get(v["n"], ())):
                if u not in first or v["n"] < first[u]["n"]:
                    first[u] = v
        return first


def render(st, t_hdr):
    first = st.rows()

    def key(u):
        m = re.fullmatch(r"(.*)-(\d+)", u)
        return (m.group(1), int(m.group(2))) if m else (u, 0)
    h = f"# updated {int(t_hdr)} {time.strftime('%H:%M:%S', time.gmtime(t_hdr))} steps {len(first)}"
    if st.cpg:
        h += f" partial {int(st.cover or st.since)}"
    bad = sorted(n for n in st.bad if n in st.seen or n in st.open)
    if bad:
        h += " skipped " + ",".join(map(str, bad[:50])) + (",+%d" % (len(bad) - 50) if len(bad) > 50 else "")
    h += f" rl {RL['rem'] if RL['rem'] is not None else -1} {RL['reset'] or 0}"
    out = [h]
    for u in sorted(first, key=key):
        v = first[u]
        c = time.strftime('%H:%M:%S', time.gmtime(v['created'])) if v['created'] is not None else "00:00:00"
        out.append(f"{u} {v['n']} {v['who']} {c}")
    return "\n".join(out) + "\n"


def open_json(st, t_hdr):
    prs = []
    for n in sorted(st.open):
        v = st.seen.get(n) or {"who": "?", "sha": "", "created": None, "units": set()}
        prs.append([n, v["who"], v["sha"], v["created"], sorted(set(v["units"]) | set(st.open[n]))])
    return json.dumps({"t": int(t_hdr), "full_t": int(st.full_t) if st.full_t else None, "rl": RL["rem"],
                       "skipped": sorted(n for n in st.bad if n in st.open), "prs": prs}, separators=(",", ":")) + "\n"


def one_pass(st):
    """the new file text, or None (a list read failed: no rewrite, so the header goes stale and readers stop).
    The first pass is the backfill: the full open sweep (read twice) and up to MAX_PAGES pages by creation."""
    PASS["date"] = None
    try:
        if not st.backfilled:
            st.sweep(twice=True)
            st.cpg = st.scan_created(1, MAX_PAGES)
            st.mark = PASS["date"]
            st.backfilled = True
        else:
            st.scan_updated()
            st.scan_created(1, 1)
            if st.cpg:
                st.cpg = st.scan_created(st.cpg, CATCHUP_PAGES)
        t_hdr = PASS["date"] - 1
        st.last_open_json = open_json(st, t_hdr)
        return render(st, t_hdr)
    except Exception as e:          # fail closed on anything (a bad row must not kill the publisher)
        log("read failed, list not refreshed:", type(e).__name__, str(e)[:120])
        return None


def sweep_pass(st):
    """the full open sweep when due, after the pass was published (keeps the header young); its result goes out with
    the next pass. A failed sweep is retried at the next pass."""
    if time.time() - st.sweep_local < SWEEP_S:
        return
    PASS["date"] = None
    try:
        st.sweep()
    except Exception as e:
        log("sweep failed (retried next pass):", type(e).__name__, str(e)[:120])


def write_file(path, txt):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        f.write(txt)
    os.replace(tmp, path)


def write(txt):
    write_file(OUT, txt)


def publish(st, txt):
    """open.json, then taken.txt; a failed write is retried (mount hiccup) and never stops the publisher (T6)"""
    for i in range(3):
        try:
            if getattr(st, "last_open_json", None):
                write_file(OPEN_OUT, st.last_open_json)
            write(txt)
            return True
        except Exception as e:
            log("write failed, retry", i + 1, type(e).__name__, str(e)[:80])
            time.sleep(2)
    return False


def main():
    back = float(sys.argv[1]) if len(sys.argv) > 1 else 3
    st = State(back * 3600)
    while True:                                  # first full list (backfill); nothing is written until it works
        txt = one_pass(st)
        if txt is not None:
            break
        if os.environ.get("TAKEN_MINUTES") and time.time() > END:
            return
        time.sleep(20)
    publish(st, txt)
    log("backfill", txt.split("\n", 1)[0], "reads", READS["n"], "requests", READS["req"])
    k = 0
    while not (os.environ.get("TAKEN_MINUTES") and time.time() > END):
        time.sleep(PASS_S)
        txt = one_pass(st)
        if txt is not None:
            publish(st, txt)
        sweep_pass(st)
        k += 1
        if k % 50 == 0:
            log("pass", k, "reads", READS["n"], "requests", READS["req"], "rl", RL["rem"])


def selftest():
    """X12 batch PR titled with another unit, X13 failed file read = no refresh, X14 a rival 300 s old is listed,
    no-id PR by file path, value file, closed PR by title, header count = rows, steady pass = no counted read.
    The failure cases are in takenfail.py (T1-T12)."""
    global FAKE
    now = time.time()
    iso = lambda t: time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))
    prs = [
        {"number": 501, "title": "Prove L-meta-90002", "user": {"login": "rival1"}, "head": {"ref": "p1", "sha": "a"},
         "state": "open", "created_at": iso(now - 40),
         "files": ["lean/PEqualNP/Outside/L_meta_90001.lean", "lean/PEqualNP/Outside/L_meta_90002.lean"]},
        {"number": 502, "title": "Batch of proofs", "user": {"login": "rival2"}, "head": {"ref": "patch-1", "sha": "b"},
         "state": "open", "created_at": iso(now - 300), "files": ["lean/PEqualNP/Outside/L_meta_90003.lean"]},
        {"number": 503, "title": "value", "user": {"login": "rival3"}, "head": {"ref": "x", "sha": "c"},
         "state": "open", "created_at": iso(now - 900), "files": ["lean/PEqualNP/Outside/V_meta_90004__k5.lean"]},
        {"number": 499, "title": "L-meta-90005", "user": {"login": "Leg0shii"}, "head": {"ref": "L-meta-90005", "sha": "d"},
         "state": "closed", "created_at": iso(now - 1200), "files": []},
        {"number": 504, "title": "R-L-meta-90006-2 reduction", "user": {"login": "rival4"}, "head": {"ref": "r", "sha": "e"},
         "state": "open", "created_at": iso(now - 100), "files": []},
    ]
    fail = set()

    def fake(path):
        m = re.search(r"pulls/(\d+)/files", path)
        if m:
            if int(m.group(1)) in fail:
                raise ReadFail("http=403")
            p = next(x for x in prs if x["number"] == int(m.group(1)))
            return [{"filename": f} for f in p["files"]]
        st_ = re.search(r"state=(\w+)", path).group(1)
        pg = int(re.search(r"[?&]page=(\d+)", path).group(1))
        rows = sorted([x for x in prs if st_ == "all" or x["state"] == st_], key=lambda x: x["created_at"], reverse=True)
        return [dict(x) for x in rows[(pg - 1) * 100:pg * 100]]
    class Cond:
        def __call__(self, path):
            return fake(path)

        def cond(self, path, etag):
            rows = fake(path)
            tag = str(hash(json.dumps(rows, sort_keys=True)))
            return (304 if etag == tag else 200), rows, tag
    FAKE = Cond()
    st = State(3 * 3600)
    txt = one_pass(st)
    rows = {l.split()[0]: l.split() for l in txt.splitlines()[1:]}
    hdr = txt.splitlines()[0].split()
    g = lambda u, i: (rows.get(u) or [None] * 4)[i]
    c = {"X12 90001 by file of a PR titled 90002": g("L-meta-90001", 2) == "rival1",
         "title unit 90002": g("L-meta-90002", 1) == "501",
         "X14 no-id PR 300 s old by file": g("L-meta-90003", 2) == "rival2",
         "value file -> L-meta-90004": "L-meta-90004" in rows,
         "closed PR by title": g("L-meta-90005", 2) == "Leg0shii",
         "R-L-meta-90006-2 is not L-meta-90006": "L-meta-90006" not in rows,
         "header count = rows": int(hdr[5]) == len(rows),
         "header epoch = pass start": abs(int(hdr[2]) - now) < 5}
    prs.append({"number": 505, "title": "more", "user": {"login": "rival5"}, "head": {"ref": "q", "sha": "f"},
                "state": "open", "created_at": iso(now - 1), "files": ["lean/PEqualNP/Outside/L_meta_90007.lean"]})
    fail.add(505)
    st.open_t = 0
    c["X13 failed file read: no new list"] = one_pass(st) is None
    fail.clear()
    t2 = one_pass(st)
    c["next pass once reads work"] = t2 is not None and "L-meta-90007 505 rival5" in t2
    r0 = READS["n"]
    one_pass(st)
    c["steady pass: no counted read (304s), files cached"] = READS["n"] - r0 == 0
    bad = [k for k, v in c.items() if not v]
    print("TAKENPUB SELFTEST", "OK" if not bad else "FAIL", f"{len(c) - len(bad)}/{len(c)}", *bad)
    return 0 if not bad else 1


if __name__ == "__main__":
    if sys.argv[1:2] == ["selftest"]:
        sys.exit(selftest())
    main()
