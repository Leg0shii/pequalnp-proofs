#!/usr/bin/env python3
"""TAKEN LIST publisher (A19, 27 Nov): which units already have a PR from anyone, from the REST pulls API (no search
API: its index lags minutes). taken.yml publishes the file as taken.txt on toolkit branch status/taken.

Format (unchanged): line 1 '# updated <epoch> <HH:MM:SS> steps N', then one line per unit
'<unit> <first PR number> <author> <created HH:MM:SS>' (the lowest PR number that touches the unit).
<epoch> is the START of the pass that produced the list: every PR created before it is in the list (REST has no lag),
so a reader needs only the PRs created after it. Readers reject a list older than 180 s or whose row count differs
from N (truncated).

A PR touches a unit when its title or branch names the unit id as a whole token, or when it adds or changes the file
lean/PEqualNP/Outside/<unit with _>.lean (or V_<...>__k<K>.lean of a value step). File paths are read for EVERY open
PR (a batch PR titled with one unit can carry others), cached per PR number and head sha. Closed and merged PRs from
the last HOURS_BACK hours count by title and branch (a merged file is on upstream main, which readers check).
FAIL CLOSED: any failed read in a pass means the list is not rewritten that pass, so its header goes stale and every
reader stops filing by itself until reads work again.

Reads per pass: 1 page of all PRs by creation (more only after a burst), the open PRs every OPEN_EVERY s, and the
files of open PRs that are new or have a new head sha. Token: GH_SEARCH_TOKEN (the run's GITHUB_TOKEN).
Run: python3 takenpub.py [HOURS_BACK=3]    selftest: python3 takenpub.py selftest"""
import calendar, json, os, re, subprocess, sys, time

UP = "open-goat/pequalnp-proofs"
OUT = os.environ.get("TAKEN_OUT", "/mnt/project-files/team/lead/taken.txt")
TOKEN = os.environ.get("GH_SEARCH_TOKEN", "")
END = time.time() + float(os.environ.get("TAKEN_MINUTES", "0") or 0) * 60   # 0 = forever
PASS_S, OPEN_EVERY, MAX_PAGES = 18, 60, 30
TOKEN_RX = re.compile(r"(?<![A-Za-z0-9_-])(L-[a-z0-9]+(?:-[a-z0-9]+)*-\d+)(?![A-Za-z0-9_-])")
FILE_RX = re.compile(r"lean/PEqualNP/Outside/(L_[a-z0-9]+(?:_[a-z0-9]+)*_\d+|V_[a-z0-9]+(?:_[a-z0-9]+)*_\d+__k\d+)\.lean")
READS = {"n": 0}
FAKE = None


class ReadFail(Exception):
    pass


def api(path):
    """GET https://api.github.com/<path>; raises ReadFail on any error (fail closed)."""
    READS["n"] += 1
    if FAKE:
        return FAKE(path)
    r = subprocess.run(["curl", "-sS", "-m", "25", "-w", "\n%{http_code}", "-H", "Accept: application/vnd.github+json"]
                       + (["-H", "Authorization: Bearer " + TOKEN] if TOKEN else []) + ["https://api.github.com/" + path],
                       capture_output=True, text=True)
    body, _, code = r.stdout.rpartition("\n")
    if r.returncode or code != "200":
        raise ReadFail(f"{path[:60]} -> rc={r.returncode} http={code}")
    try:
        return json.loads(body)
    except ValueError:
        raise ReadFail(f"{path[:60]} -> bad json")


def ts(v):
    return calendar.timegm(time.strptime(v[:19], "%Y-%m-%dT%H:%M:%S"))


def unit_of_file(f):
    m = FILE_RX.fullmatch(f or "")
    if not m:
        return None
    s = m.group(1)
    if s.startswith("V_"):
        s = "L_" + s[2:].split("__k")[0]
    return s.replace("_", "-")


def units_named(p):
    return set(TOKEN_RX.findall(p.get("title") or "")) | \
        set(TOKEN_RX.findall(((p.get("head") or {}).get("ref") or "").replace("_", "-")))


FILES = {}      # (number, head sha) -> [units by file path]


def file_units(p):
    k = (p["number"], (p.get("head") or {}).get("sha") or "")
    if k not in FILES:
        us, pg = set(), 1
        while True:
            fs = api(f"repos/{UP}/pulls/{p['number']}/files?per_page=100&page={pg}")
            if not isinstance(fs, list):
                raise ReadFail(f"files of #{p['number']}: not a list")
            us |= {u for u in (unit_of_file(f.get("filename")) for f in fs) if u}
            if len(fs) < 100 or pg >= 30:            # GitHub lists at most 3000 files per PR
                break
            pg += 1
        FILES[k] = sorted(us)
    return FILES[k]


class State:
    def __init__(self, back_s):
        self.since = time.time() - back_s
        self.seen = {}          # number -> {"n", "who", "created", "units" (title/branch)}
        self.open = {}          # number -> units by file path (open PRs only)
        self.open_t = 0.0

    def _see(self, p):
        self.seen[p["number"]] = {"n": p["number"], "who": (p.get("user") or {}).get("login") or "?",
                                  "created": ts(p["created_at"]), "units": units_named(p)}

    def scan_all(self):
        """PRs of any state created since the last scan, newest first, until the page reaches older ones."""
        newest = max([v["created"] for v in self.seen.values()] + [self.since])
        for pg in range(1, MAX_PAGES + 1):
            rows = api(f"repos/{UP}/pulls?state=all&sort=created&direction=desc&per_page=100&page={pg}")
            if not isinstance(rows, list):
                raise ReadFail("pulls?state=all: not a list")
            for p in rows:
                if ts(p["created_at"]) >= self.since:
                    self._see(p)
                    if p.get("state") == "open":
                        self.open[p["number"]] = file_units(p)
            if len(rows) < 100 or ts(rows[-1]["created_at"]) < newest - 120:
                return
        raise ReadFail(f"over {MAX_PAGES} pages of new PRs")

    def scan_open(self):
        """every open PR (a head sha may have moved: new files), all pages"""
        now_open = {}
        for pg in range(1, MAX_PAGES + 1):
            rows = api(f"repos/{UP}/pulls?state=open&sort=created&direction=desc&per_page=100&page={pg}")
            if not isinstance(rows, list):
                raise ReadFail("pulls?state=open: not a list")
            for p in rows:
                now_open[p["number"]] = file_units(p)
                if p["number"] not in self.seen:
                    self._see(p)
            if len(rows) < 100:
                break
        else:
            raise ReadFail(f"over {MAX_PAGES} pages of open PRs")
        self.open = now_open
        self.open_t = time.time()

    def rows(self):
        first = {}
        for v in self.seen.values():
            for u in set(v["units"]) | set(self.open.get(v["n"], ())):
                if u not in first or v["n"] < first[u]["n"]:
                    first[u] = v
        return first


def render(first, t_start):
    def key(u):
        m = re.fullmatch(r"(.*)-(\d+)", u)
        return (m.group(1), int(m.group(2))) if m else (u, 0)
    out = [f"# updated {int(t_start)} {time.strftime('%H:%M:%S', time.gmtime(t_start))} steps {len(first)}"]
    for u in sorted(first, key=key):
        v = first[u]
        out.append(f"{u} {v['n']} {v['who']} {time.strftime('%H:%M:%S', time.gmtime(v['created']))}")
    return "\n".join(out) + "\n"


def one_pass(st):
    """the new file text, or None (a read failed: no rewrite, so the header goes stale and readers stop)"""
    t_start = time.time()
    try:
        if time.time() - st.open_t >= OPEN_EVERY:
            st.scan_open()
        st.scan_all()
    except (ReadFail, KeyError, ValueError, TypeError) as e:
        print(time.strftime("%H:%M:%S", time.gmtime()), "read failed, list not refreshed:", str(e)[:120], flush=True)
        return None
    return render(st.rows(), t_start)


def write(txt):
    tmp = OUT + ".tmp"
    with open(tmp, "w") as f:
        f.write(txt)
    os.replace(tmp, OUT)


def main():
    back = float(sys.argv[1]) if len(sys.argv) > 1 else 3
    st = State(back * 3600)
    while True:                                  # first full list (backfill); nothing is written until it works
        txt = one_pass(st)
        if txt is not None:
            break
        time.sleep(20)
    write(txt)
    print(time.strftime("%H:%M:%S", time.gmtime()), "backfill", txt.split("\n", 1)[0], "reads", READS["n"], flush=True)
    k = 0
    while not (os.environ.get("TAKEN_MINUTES") and time.time() > END):
        time.sleep(PASS_S)
        txt = one_pass(st)
        if txt is not None:
            write(txt)
        k += 1
        if k % 50 == 0:
            print(time.strftime("%H:%M:%S", time.gmtime()), "pass", k, "reads", READS["n"], flush=True)


def selftest():
    """X12 batch PR titled with another unit, X13 failed file read = no refresh, X14 a rival 300 s old is listed,
    no-id PR by file path, value file, closed PR by title, header count = rows, steady pass = 1 read."""
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
    FAKE = fake
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
    c["steady pass: 1 read, files cached"] = READS["n"] - r0 == 1
    bad = [k for k, v in c.items() if not v]
    print("TAKENPUB SELFTEST", "OK" if not bad else "FAIL", f"{len(c) - len(bad)}/{len(c)}", *bad)
    return 0 if not bad else 1


if __name__ == "__main__":
    if sys.argv[1:2] == ["selftest"]:
        sys.exit(selftest())
    main()
