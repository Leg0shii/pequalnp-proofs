# selftest_rcb.py [dir of submit.py]: RC-b cases (Lead 06:22/06:25, 27 Nov), in-process with GitHub faked.
#   R3       the rival snapshot is stamped at build START (a slow page read must not make it look younger)
#   16.1     filing_halted: tie = halted, non-digit stop = halted, non-digit go ignored, unreadable = halted
#   HALT-SH  a fresh shared halt.json answers with no ls-remote; a stale one is read inline (never trusted)
#   NOWAIT   a worker with a fresh snapshot never waits on the snapshot lock (a build in progress elsewhere)
#   REFRESH  the refresher keeps halt.json and rival_snap.json at most 2 s old
#   DEAD     refresher dead: a stale snapshot is rebuilt inline, never used
#   16.7     one hour at wave scale: 5,100 open PRs, a rival PR every 10 s (half without a unit id), each updated once
#            60 s later, a snapshot every 0.8 s: counted GitHub reads of the openers under 1,000
# Prints one line per case and "RCB SELFTEST OK <n>" or "RCB SELFTEST FAIL <cases>". Exit 0 iff OK.
import hashlib, json, os, subprocess, sys, tempfile, threading, time

SNAPD = tempfile.mkdtemp()
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), RIVAL_SNAP_DIR=SNAPD,
                  GHCOND_DIR=tempfile.mkdtemp())
os.environ.pop("FILING_FIXTURE", None)
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S

res = []


def case(name, ok, why=""):
    res.append((name, bool(ok)))
    print(("ok   " if ok else "FAIL ") + f"rcb/{name} {why}")


def cp(out="", rc=0, err=""):
    return subprocess.CompletedProcess([], rc, out, err)


REAL_TIME = S.time.time
REAL_SLEEP = S.time.sleep
CLK = [1_800_000_000.0]
PULLS = []            # newest first: {"number","user":{"login"},"title","head":{"ref","sha"},"created_at","updated_at","files"}
CNT = {"counted": 0, "304": 0, "files": 0, "lsremote": 0}
LS = {"txt": "", "rc": 0}


def iso(t):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))


def fake_gh(args, write=False, timeout=120):
    a = list(args)
    path = a[1]
    if "/files" in path:
        CNT["files"] += 1; CNT["counted"] += 1
        n = int(path.split("/pulls/")[1].split("/")[0])
        p = next((x for x in PULLS if x["number"] == n), {})
        return cp(json.dumps([{"filename": f} for f in p.get("files", [])]))
    if "/pulls?" in path:
        q = dict(x.split("=", 1) for x in path.split("?", 1)[1].split("&"))
        pp, pg = int(q.get("per_page", 30)), int(q.get("page", 1))
        vis = [p for p in PULLS if p["_c"] <= CLK[0]]
        page = [{k: v for k, v in p.items() if not k.startswith("_") and k != "files"} | {"updated_at": iso(p["_u"](CLK[0]))}
                for p in vis[(pg - 1) * pp:pg * pp]]
        body = json.dumps(page)
        etag = 'W/"%s"' % hashlib.sha1(body.encode()).hexdigest()[:16]
        if "-i" not in a:                         # an unconditional read (old code)
            CNT["counted"] += 1
            return cp(body)
        if "-H" in a and a[a.index("-H") + 1] == "If-None-Match: " + etag:
            CNT["304"] += 1
            return cp("HTTP/2.0 304 Not Modified\nX-Ratelimit-Remaining: 4000\n\n", 1, "gh: HTTP 304")
        CNT["counted"] += 1
        return cp(f"HTTP/2.0 200 OK\nEtag: {etag}\nX-Ratelimit-Remaining: 4000\n\n{body}")
    raise RuntimeError("unexpected gh " + " ".join(a[:2]))


def fake_run(cmd, timeout=300, env=None, cwd=None):
    if cmd[0] == "gh":                     # the real submit.gh() over a faked process (304 = exit 1, like gh api -i)
        return fake_gh(cmd[1:])
    if cmd[0] == "git" and "ls-remote" in cmd:
        CNT["lsremote"] += 1
        return cp(LS["txt"], LS["rc"], "" if LS["rc"] == 0 else "fatal")
    raise RuntimeError("unexpected run " + " ".join(cmd[:3]))


class DG:
    REPO = "/nonexistent"


REAL_GH = S.gh
S.gh = fake_gh
S.run = fake_run
S.dg = lambda: DG()
TL_ROWS = {"L-meta-5": "rival9"}


def fake_taken():
    S.TL_HDR[0] = int(CLK[0]) - 20
    return dict(TL_ROWS)


S._taken_list = fake_taken
S.time.time = lambda: CLK[0]
S.time.sleep = lambda s: CLK.__setitem__(0, CLK[0] + s)
S.log = lambda *a: None


def reset_snap():
    for f in os.listdir(SNAPD):
        os.remove(os.path.join(SNAPD, f))
    S._TL.clear(); S.TL_T[0] = 0.0


def add_pr(n, t, title, files=(), login="rival1", upd=60):
    PULLS.insert(0, {"number": n, "user": {"login": login}, "title": title, "head": {"ref": "patch-%d" % n, "sha": "s%d" % n},
                     "created_at": iso(t), "files": list(files), "_c": t,
                     "_u": (lambda now, t=t, upd=upd: t + upd if now >= t + upd else t)})


def RN(gid, age):
    """the create-time check (16.14: final=True; older code has no final)"""
    try:
        return S.rival_now(gid, age, final=True)
    except TypeError:
        return S.rival_now(gid, age)


# ---- R3: a page read that takes 3 s
reset_snap()
add_pr(70001, CLK[0] - 5, "Prove L-meta-70001")
orig = S.gh
def slow_gh(args, write=False, timeout=120):
    if "/pulls?" in args[1]:
        CLK[0] += 1.5
    return orig(args, write, timeout)
S.gh = slow_gh
t_start = CLK[0]
try:
    snap = S.rival_snapshot(0)
    case("R3-stamp-at-start", abs(snap["t"] - t_start) < 0.01, f"(t - start of the page read = {snap['t'] - t_start:.1f} s, read took 1.5 s)")
except Exception as e:
    case("R3-stamp-at-start", False, repr(e)[:100])
S.gh = orig

# ---- FRESH-AT-CREATE (Lead 06:52, w12 mintload: 124 of 237 creates on a snapshot over 2 s): reads take time (taken
# list 1.5 s, each page 1.5 s, each files read 1.0 s); the snapshot rival_now hands to the create must be at most 2 s
# old counted from the start of its first open-pulls page request
reset_snap(); PULLS.clear()
for k in range(3):
    add_pr(71000 + k, CLK[0] - 2 - k, "Batch of proofs", files=["lean/PEqualNP/Outside/L_meta_%d.lean" % (71000 + k)])
REQ = []
def lat_gh(args, write=False, timeout=120):
    if "/pulls?" in args[1]:
        if "page=1" in args[1].split("&")[-1] or args[1].endswith("page=1"):
            REQ.append(CLK[0])
        CLK[0] += 1.5
    elif "/files" in args[1]:
        CLK[0] += 1.0
    return orig(args, write, timeout)
def lat_taken():
    CLK[0] += 1.5
    return fake_taken()
S.gh = lat_gh; S._taken_list = lat_taken
try:
    r = RN("L-meta-71999", 2)
    sa = S.STG.get("snap_age")
    honest = CLK[0] - max([t for t in REQ if t <= CLK[0] - (sa or 0) + 1e-6] or [0])
    case("FRESH-AT-CREATE-2s", r is None and sa is not None and sa <= 2.0 and abs(honest - sa) < 0.01,
         f"(snap_age {sa}, since its page-1 request {honest:.1f} s, page-1 requests {len(REQ)}, rival={r})")
except Exception as e:
    case("FRESH-AT-CREATE-2s", False, repr(e)[:100])
S.gh = orig; S._taken_list = fake_taken

# ---- 304-REAL-GH (w12 07:02): with submit's real gh() (which raises on exit 1) an unchanged page answers 304 = exit 1;
# the snapshot must use the cached page, not fail the rival check
reset_snap(); PULLS.clear()
add_pr(72001, CLK[0] - 5, "Prove L-meta-72001")
S.gh = REAL_GH
os.environ["READ_TOKEN"] = "x"; S.READ_TOKEN = "x"
try:
    r1 = S.rival_now("L-meta-72999", 0.0001); CLK[0] += 1
    n304 = CNT["304"]
    reset_snap()
    r2 = S.rival_now("L-meta-72999", 0.0001)
    case("304-REAL-GH-cached-page", r1 is None and r2 is None and CNT["304"] > n304, f"(first {r1}, second {r2}, 304s {CNT['304'] - n304})")
except Exception as e:
    case("304-REAL-GH-cached-page", False, repr(e)[:100])
S.gh = fake_gh

# ---- 16.1 through the real filing_halted (inline: no drain dir for these)
del os.environ["RIVAL_SNAP_DIR"]
for name, txt, rc, exp in (("16.1-tie", "0\trefs/heads/filing/stop/200\n0\trefs/heads/filing/go/200\n", 0, True),
                           ("16.1-nondigit-stop", "0\trefs/heads/filing/stop/100\n0\trefs/heads/filing/stop/now\n0\trefs/heads/filing/go/900\n", 0, True),
                           ("16.1-nondigit-go-ignored", "0\trefs/heads/filing/stop/100\n0\trefs/heads/filing/go/999x\n", 0, True),
                           ("16.1-go-newer", "0\trefs/heads/filing/stop/100\n0\trefs/heads/filing/go/200\n", 0, False),
                           ("16.1-unreadable", "", 128, True)):
    LS.update(txt=txt, rc=rc)
    try:
        h = S.filing_halted()[0]
    except Exception as e:
        h = repr(e)[:60]
    case(name, h == exp, f"(halted={h})")
os.environ["RIVAL_SNAP_DIR"] = SNAPD

# ---- 16.1 rule table on haltrule.verdict (the one rule file, w9's, used by submit, drain and the closer)
try:
    import haltrule
except ImportError:
    haltrule = None
R = lambda *names: "".join(f"0123\trefs/heads/filing/{n}\n" for n in names)
for name, txt, rc, exp in (("unreadable", "", 128, True), ("no refs", R(), 0, False), ("only go", R("go/100"), 0, False),
                           ("stop newer", R("stop/200", "go/100"), 0, True), ("go newer", R("stop/100", "go/200"), 0, False),
                           ("tie", R("stop/200", "go/200"), 0, True), ("stop, no go", R("stop/100"), 0, True),
                           ("non-digit stop under newer go", R("stop/100", "stop/now", "go/999"), 0, True),
                           ("non-digit go ignored", R("stop/100", "go/100x", "go/next"), 0, True),
                           ("non-digit go ignored, digit go newer", R("stop/100", "go/zz", "go/101"), 0, False),
                           ("nested stop name", R("stop/100/a", "go/200"), 0, True),
                           ("unicode digits", R("stop/\u0661\u0662", "go/200"), 0, True),
                           ("other refs", "0\trefs/heads/filing/x\n0\trefs/heads/main\n", 0, False)):
    got = haltrule.verdict(txt, rc)[0] if haltrule and hasattr(haltrule, "verdict") else "no haltrule.verdict"
    if got != exp:
        case("16.1-table-" + name.replace(" ", "-"), False, f"(halted={got}, want {exp})")
case("16.1-table-13", not [1 for n, ok in res if n.startswith("16.1-table-") and not ok], "(13 rule rows on haltrule.verdict)")

# ---- HALT-SH: fresh shared state = no read; stale = inline read
LS.update(txt="0\trefs/heads/filing/go/200\n", rc=0)
reset_snap()
json.dump({"t": CLK[0] - 1, "halted": False, "why": ""}, open(os.path.join(SNAPD, "halt.json"), "w"))
n0 = CNT["lsremote"]; S.filing_halted()
case("HALT-SH-fresh-no-read", CNT["lsremote"] == n0, f"(ls-remote calls {CNT['lsremote'] - n0}, want 0)")
json.dump({"t": CLK[0] - 3, "halted": False, "why": ""}, open(os.path.join(SNAPD, "halt.json"), "w"))
LS.update(txt="0\trefs/heads/filing/stop/300\n0\trefs/heads/filing/go/200\n", rc=0)
n0 = CNT["lsremote"]; h = S.filing_halted()[0]
case("HALT-SH-stale-read-inline", CNT["lsremote"] == n0 + 1 and h is True, f"(reads {CNT['lsremote'] - n0}, halted={h})")

# ---- NOWAIT: a builder holds the snapshot lock; the fresh file must still answer at once
reset_snap()
json.dump({"t": CLK[0] - 0.5, "hdr": CLK[0] - 20, "taken": {}, "recent": [], "files": {}},
          open(os.path.join(SNAPD, "rival_snap.json"), "w"))
import fcntl
lk = open(os.path.join(SNAPD, "rival_snap.lock"), "w"); fcntl.flock(lk, fcntl.LOCK_EX)
out = {}
th = threading.Thread(target=lambda: out.setdefault("r", S.rival_now("L-meta-9", 2)), daemon=True)
w0 = REAL_TIME(); th.start(); th.join(1.0)
waited = REAL_TIME() - w0
case("NOWAIT-fresh-snapshot-no-lock-wait", "r" in out and waited < 0.3, f"(answered={'r' in out}, waited {waited:.2f} s)")
fcntl.flock(lk, fcntl.LOCK_UN); lk.close(); th.join(2)

# ---- DEAD: a 5 s old snapshot (no refresher) is rebuilt, not used
reset_snap()
json.dump({"t": CLK[0] - 5, "hdr": CLK[0] - 20, "taken": {"L-meta-77": "Leg0shii"}, "recent": [], "files": {}},
          open(os.path.join(SNAPD, "rival_snap.json"), "w"))
TL_ROWS["L-meta-77"] = "rival3"
r = S.rival_now("L-meta-77", 2)
case("DEAD-stale-snapshot-rebuilt", bool(r), f"(rival={r})")
TL_ROWS.pop("L-meta-77")

# ---- REFRESH: the real refresher loop (real time) keeps both files <= 2 s old
if hasattr(S, "refresher"):
    S.time.time = REAL_TIME; S.time.sleep = REAL_SLEEP
    reset_snap()
    stopf = os.path.join(SNAPD, "refresh.stop")
    th = threading.Thread(target=S.refresher, daemon=True); th.start()
    REAL_SLEEP(0.5)
    ages, t_end, err = [], REAL_TIME() + 2.5, ''
    while REAL_TIME() < t_end:
        try:
            ages.append(max(REAL_TIME() - json.load(open(os.path.join(SNAPD, "halt.json")))["t"],
                            REAL_TIME() - json.load(open(os.path.join(SNAPD, "rival_snap.json")))["t"]))
        except Exception as e:
            ages.append(99); err = repr(e)[:80]
        REAL_SLEEP(0.1)
    open(stopf, "w").close(); th.join(3)
    case("REFRESH-max-age-2s", ages and max(ages) <= 2.0 and not th.is_alive(), f"(max age {max(ages):.2f} s over {len(ages)} samples, stopped={not th.is_alive()}) {err}")
    S.time.time = lambda: CLK[0]; S.time.sleep = lambda s: CLK.__setitem__(0, CLK[0] + s)
else:
    case("REFRESH-max-age-2s", False, "(no refresher in this submit.py)")

# ---- 16.7: one hour at wave scale
PULLS.clear(); reset_snap()
for k in range(5100):                                        # 5,100 open PRs, all older than the header
    add_pr(100000 + k, CLK[0] - 7200 + k, "Prove L-meta-%d" % (100000 + k), upd=10 ** 9)
PULLS.sort(key=lambda p: -p["number"])
t0 = CLK[0]; nxt = t0; n = 200000; builds = 0
CNT.update(counted=0, files=0); c304 = CNT["304"]
while CLK[0] < t0 + 3600:
    while nxt <= CLK[0]:
        n += 1
        add_pr(n, nxt, ("Prove L-meta-%d" % n) if n % 2 else "Batch of proofs", files=["lean/PEqualNP/Outside/L_meta_%d.lean" % n])
        nxt += 10
    try:
        S.rival_snapshot(0); builds += 1
    except Exception as e:
        print("  snapshot failed:", str(e)[:100]); break
    CLK[0] += 0.8
case("16.7-wave-hour-opener-reads", builds >= 4400 and CNT["counted"] < 1000,
     f"(builds {builds}, counted {CNT['counted']} (files {CNT['files']}), 304s {CNT['304'] - c304}, limit < 1,000)")

# ---- 6 PR-STALL by name within 60 s (drain.py stall_alerts / stall_tick)
os.environ.setdefault("SRC", "/tmp")
try:
    import drain as D
    if hasattr(D, "_SV"):
        D._SV["final"] = True          # imported for tests: no drain-state save at exit (w12 fix 1 atexit hook)
    have = hasattr(D, "stall_alerts")
except Exception as e:
    have, D = False, None
if have:
    D.ALERTED.clear()
    a1 = D.stall_alerts(1000.0, 3, 900.0, 800.0, 1060.0)
    case("6-PR-STALL-bucket-at-once", any(k == "prstall-bucket" and m.startswith("PR-STALL") for k, m in a1), f"({a1})")
    case("6-PR-STALL-noprogress-61s", any(k == "prstall-noprogress" for k, m in D.stall_alerts(1000.0, 3, 939.0, 800.0, 0)), "")
    case("6-no-alert-at-59s", not D.stall_alerts(1000.0, 3, 941.0, 800.0, 0), "")
    case("6-no-alert-when-idle", not D.stall_alerts(1000.0, 0, 100.0, 50.0, 0), "")
    if "last_idle" in D.stall_alerts.__code__.co_varnames:   # Lead 09:02 (r3): 14 units, 60 s nothing, 97 units = no PR-STALL
        case("6-idle-gap-no-stall", not D.stall_alerts(1000.0, 97, 900.0, 800.0, 0, 998.0), "")
        case("6-stuck-after-gap-alerts", any(k == "prstall-noprogress" for k, m in D.stall_alerts(1000.0, 97, 900.0, 800.0, 0, 935.0)), "")
    else:
        case("6-idle-gap-no-stall", bool(D.stall_alerts(1000.0, 97, 900.0, 800.0, 0)) is False, "(old drain: the idle gap counts as a stall)")
    sent = []
    D.alert_ref = lambda m, k: sent.append((k, m)) or True
    D.W = tempfile.mkdtemp(); open(os.path.join(D.W, "stall"), "w").write(str(time.time() + 60))   # time = the case clock
    D.LAST_DONE[0] = time.time(); D.T0 = time.time()
    D.ALERTED.clear(); D.stall_tick(2); D.stall_tick(2)
    case("6-PR-STALL-ref-once-per-5-min", [k for k, m in sent] == ["prstall-bucket"], f"(sent {sent})")
else:
    case("6-PR-STALL-alerts", False, "(no stall_alerts in this drain.py)")

# ---- 16.11 site status (drain.site_verdict, drain.site_closed, submit.site_closed_now)
if D is not None and hasattr(D, "site_verdict"):
    now = 2_000_000_000.0
    F = lambda age, code=200: json.dumps({"epoch": now - age, "http": code})
    ST = lambda acc: json.dumps({"submissions": {"proof": {"accepting": acc, "retry_after_s": 120}, "lease": {"accepting": True}}})
    v = D.site_verdict(ST(False), F(30), now)
    case("16.11-not-accepting-holds", v[0] is True and v[2] is None, f"({v[1]})")
    v = D.site_verdict(ST(True), F(30), now)
    case("16.11-accepting-files", v[0] is False and v[2] is None, f"({v[1]})")
    v = D.site_verdict(ST(False), F(200), now)
    case("16.11-stale-copy-files-with-alert", v[0] is False and (v[2] or "").startswith("SITE-STATUS-STALE"), f"({v[1]})")
    v = D.site_verdict("{not json", F(30), now)
    case("16.11-malformed-json-files-with-alert", v[0] is False and (v[2] or "").startswith("SITE-STATUS-STALE"), f"({v[1]})")
    v = D.site_verdict(ST(False), "garbage", now)
    case("16.11-malformed-fetched-files-with-alert", v[0] is False and (v[2] or "").startswith("SITE-STATUS-STALE"), f"({v[1]})")
    v = D.site_verdict(ST(False), F(30, 503), now)
    case("16.11-http-failure-files-with-alert", v[0] is False and v[2], f"({v[1]})")
    v = D.site_verdict(None, None, now)
    case("16.11-no-ref-dark", v[0] is False and v[2] is None, f"({v[1]})")
    # hold and resume through site_closed() with the shared copy, and one alert per 5 min when stale
    seq = [(ST(False), F(10)), (ST(True), F(10)), (ST(False), F(500)), (ST(False), F(500))]
    D._site_read = lambda: (lambda x: (x[0], x[1].replace(str(2_000_000_000.0 - 10), str(time.time() - 10)).replace(str(2_000_000_000.0 - 500), str(time.time() - 500))))(seq.pop(0))
    sent.clear(); D.ALERTED.clear(); D._SITE["t"] = 0
    D.SITE_EVERY_S = 0
    a = D.site_closed(); w1 = json.load(open(os.path.join(D.W, "site.json")))
    os.environ["RIVAL_SNAP_DIR"] = D.W; S.SNAP_DIR = D.W
    sc = S.site_closed_now()
    b = D.site_closed()
    sc2 = S.site_closed_now()
    c = D.site_closed(); d = D.site_closed()
    case("16.11-hold-then-resume", a is True and bool(sc) and b is False and sc2 is None and w1["closed"] is True, f"(closed {a} -> {b}, opener saw {sc!r} then {sc2!r})")
    case("16.11-stale-one-alert", c is False and d is False and [k for k, m in sent] == ["sitestale"], f"(alerts {sent})")
    os.environ["RIVAL_SNAP_DIR"] = SNAPD; S.SNAP_DIR = SNAPD
    dr = open(os.path.join(os.path.dirname(D.__file__), "drain.py")).read()
    case("16.11-site-closed-not-marked-seen", '"paused", "halted", "site-closed"' in dr, "")
else:
    case("16.11-site-status", False, "(no site_verdict in this drain.py)")

# ---- 16.12 (Lead 07:18): fresh = the newest-page read started at most max(2 s, d + 1 s) ago, d <= 6 s
def page_lat(sec):
    def g(args, write=False, timeout=120):
        if "/pulls?" in args[1]:
            REQ.append(CLK[0]); CLK[0] += sec
        return orig(args, write, timeout)
    return g
reset_snap(); PULLS.clear(); add_pr(73001, CLK[0] - 5, "Prove L-meta-73001")
REQ = []; S.gh = page_lat(3.0)
try:
    r = RN("L-meta-73999", 2)
    case("16.12-3s-read-files-once", r is None and len(REQ) == 1, f"(rival={r}, page reads {len(REQ)})")
except Exception as e:
    case("16.12-3s-read-files-once", False, repr(e)[:100])
reset_snap(); REQ.clear(); S.gh = page_lat(0.5)
json.dump({"t": CLK[0] - 4.5, "d": 3.0, "hdr": CLK[0] - 20, "taken": {}, "recent": [], "files": {}},
          open(os.path.join(SNAPD, "rival_snap.json"), "w"))
RN("L-meta-73999", 2)
case("16.12-never-on-read-older-than-d+1", len(REQ) >= 1, f"(a 3 s read started 4.5 s ago was read again: {len(REQ)} reads)")
reset_snap(); REQ.clear(); S.gh = page_lat(7.0)
r = RN("L-meta-73999", 2)
slow = os.path.exists(os.path.join(SNAPD, "snapslow"))
case("16.12-7s-read-files-nothing", bool(r) and r.startswith("rival check failed") and slow, f"(rival={str(r)[:60]}, snapslow file {slow})")
S.gh = orig
if have and hasattr(D, "stall_tick"):
    sent.clear(); D.ALERTED.clear(); D.W = SNAPD; D.LAST_DONE[0] = time.time(); D.T0 = time.time()
    D.stall_tick(0); D.stall_tick(0)
    case("16.12-SNAP-SLOW-alert-once", [k for k, m in sent] == ["snapslow"], f"(alerts {sent})")

# ---- 16.13 (Lead 07:25): GitHub's refusal protocol for creates
if hasattr(S, "bucket_refusal") and hasattr(S, "parse_create"):
    G = tempfile.mkdtemp(); now = 3_000_000_000.0
    k, w, r = S.bucket_refusal(G, {"retry-after": "30"}, "secondary rate limit", now)
    case("16.13-retry-after-honoured", (k, w, r) == (1, 30.0, 35) and S.bucket_wait(G, now + 29) > 0 and S.bucket_wait(G, now + 30.5) == 0,
         f"(refusal {k} wait {w} rate {r})")
    G = tempfile.mkdtemp()
    k, w, r = S.bucket_refusal(G, {"x-ratelimit-remaining": "0", "x-ratelimit-reset": str(int(now) + 200)}, "", now)
    case("16.13-ratelimit-reset-when-remaining-0", k == 1 and 200 <= w <= 202, f"(wait {w})")
    G = tempfile.mkdtemp()
    seq = [S.bucket_refusal(G, {}, "", now + i * 1000) for i in range(3)]
    case("16.13-doubling-60-120-240", [x[1] for x in seq] == [60.0, 120.0, 240.0], f"({[x[1] for x in seq]})")
    case("16.13-rate-halved-70-35-17", [x[2] for x in seq] == [35, 17, 10], f"(rates {[x[2] for x in seq]})")
    k4 = S.bucket_refusal(G, {}, "", now + 4000)
    case("16.13-fourth-refusal-gives-up", k4[0] == 4 and S.bucket_wait(G, now + 99999) == float("inf"), f"({k4})")
    # through create_pr: a REST 403 with headers stops ALL creates (no second request while limited) and is logged
    Gd = tempfile.mkdtemp(); creates = []; logs = []
    os.environ["PR_GATE_DIR"] = Gd; os.environ["PR_GATE_N"] = "2"
    R403 = "HTTP/2.0 403 Forbidden\r\nRetry-After: 45\r\nX-Ratelimit-Remaining: 4000\r\nX-Ratelimit-Limit: 5000\r\n\r\n" \
        '{"message":"You have exceeded a secondary rate limit"}'
    R201 = "HTTP/2.0 201 Created\r\nX-Ratelimit-Remaining: 3999\r\n\r\n" + '{"html_url":"https://github.com/open-goat/pequalnp-proofs/pull/7","number":7}'
    sv = (S.run, S.filing_halted, S.rival_now, S.stopped, S.site_closed_now, S.log, S.pr_body)
    CL = [now]
    S.time.time = lambda: CL[0]
    S.time.sleep = lambda x: CL.__setitem__(0, CL[0] + x)
    def frun(cmd, timeout=300, env=None, cwd=None):
        creates.append(CL[0])
        return cp(R403 if len(creates) == 1 else R201, 1 if len(creates) == 1 else 0, "gh: (HTTP 403)" if len(creates) == 1 else "")
    S.run = frun; S.filing_halted = lambda *a: (False, ""); S.rival_now = lambda *a: None; S.stopped = lambda: False
    S.site_closed_now = lambda: None; S.log = lambda *a: logs.append(" ".join(map(str, a))); S.pr_body = lambda l: "body"
    try:
        url, why = S.create_pr("L-meta-1", "lease-x")
        gap = creates[1] - creates[0] if len(creates) > 1 else 0
        case("16.13-no-request-while-limited", url and len(creates) == 2 and gap >= 45, f"(creates {len(creates)}, second {gap:.0f} s after the 403)")
        ln = next((l for l in logs if l.startswith("CREATE ")), "")
        case("16.13-non-2xx-logged-with-headers", "http 403" in ln and "retry-after=45" in ln and "x-ratelimit-remaining=4000" in ln, f"({ln[:120]})")
        case("16.13-new-rate-logged", any("rate now 35/min" in l for l in logs), "")
        acc = open(os.path.join(Gd, "accepted.log")).read().split() if os.path.exists(os.path.join(Gd, "accepted.log")) else []
        case("07:27-accepted-create-recorded", len(acc) == 1, f"({acc})")
        for i in range(3):
            S.bucket_refusal(Gd, {}, "", CL[0])
        creates.clear()
        url, why = S.create_pr("L-meta-2", "lease-y")
        case("16.13-giveup-no-create", url is None and why.startswith("stall-giveup") and not creates, f"({why[:60]}, creates {len(creates)})")
    finally:
        S.run, S.filing_halted, S.rival_now, S.stopped, S.site_closed_now, S.log, S.pr_body = sv
        S.time.time, S.time.sleep = REAL_TIME, REAL_SLEEP
        os.environ.pop("PR_GATE_DIR", None)
    if D is not None:
        sent.clear(); D.ALERTED.clear(); D.W = Gd; D.LAST_DONE[0] = time.time(); D.T0 = time.time()
        D.stall_tick(0); D.stall_tick(0)
        dr = open(os.path.join(os.path.dirname(D.__file__), "drain.py")).read()
        case("16.13-PR-STALL-GIVEUP-alert-once", [k for k, m in sent if k == "prstall-giveup"] == ["prstall-giveup"], f"({[k for k, m in sent]})")
        case("16.13-giveup-units-unseen", '"site-closed", "stall-giveup"' in dr, "")
        if hasattr(D, "creates_tick"):
            Gc = tempfile.mkdtemp(); D.W = Gc; D._CW[0] = 0.0; t0 = 3_000_000_000.0
            open(os.path.join(Gc, "accepted.log"), "w").write("".join(f"{t0 + i * 0.9:.3f}\n" for i in range(12)))
            l1 = D.creates_tick(t0 + 15); l2 = D.creates_tick(t0 + 16); l3 = D.creates_tick(t0 + 25)
            case("07:27-creates-per-10s-logged", l1 and "accepted 12" in l1 and l2 is None and l3 is None, f"({l1})")
        else:
            case("07:27-creates-per-10s-logged", False, "(no creates_tick)")
else:
    case("16.13-refusal-protocol", False, "(no bucket_refusal in this submit.py)")

# ---- 16.14 (Lead 07:43): ONE READER, NO CONVOY. Real time, threads: a refresher reading back to back (newest page 3 s,
# then 1.5 s of files reads for a new PR every read), 20 workers asking at once with a 2 s bound: no worker reads
if True:                                   # runs on older code too (the convoy shows as worker reads)
    S.time.time, S.time.sleep = REAL_TIME, REAL_SLEEP
    if hasattr(S, "IS_REFRESHER"):
        S.IS_REFRESHER[0] = False              # the REFRESH case above ran the refresher in this process
    reset_snap(); PULLS.clear(); CLK[0] = REAL_TIME()
    tl = threading.local(); RD = {"ref": 0, "worker": 0}; nxt = [75000]; stop = threading.Event()
    def rt_gh(args, write=False, timeout=120):
        CLK[0] = REAL_TIME()
        if "/pulls?" in args[1]:
            RD["ref" if getattr(tl, "ref", False) else "worker"] += 1
            REAL_SLEEP(3.0); CLK[0] = REAL_TIME()
            nxt[0] += 1; add_pr(nxt[0], CLK[0] - 0.5, "Batch of proofs", files=["lean/PEqualNP/Outside/L_meta_%d.lean" % nxt[0]])
        elif "/files" in args[1]:
            REAL_SLEEP(1.5)
        return orig(args, write, timeout)
    S.gh = rt_gh
    json.dump({"t": REAL_TIME() - 30, "d": 0.5, "hdr": REAL_TIME() - 40, "taken": {}, "recent": [], "files": {}},
              open(os.path.join(SNAPD, "rival_snap.json"), "w"))
    def put_hb(t):                  # two threads write it: one tmp name per thread (a shared one raced: the loser's
        tmp = os.path.join(SNAPD, f"refresh.hb.t{threading.get_ident()}")   # os.replace raised and killed fake_refresher)
        open(tmp, "w").write(f"{t:.1f} 0 0 0 0\n")
        os.replace(tmp, os.path.join(SNAPD, "refresh.hb"))
    def fake_refresher():
        tl.ref = True
        while not stop.is_set():
            put_hb(REAL_TIME())
            try:
                S.rival_snapshot(0)
            except Exception as e:
                print("  refresher build failed:", repr(e)[:160])
    def hb():
        while not stop.is_set():
            put_hb(REAL_TIME()); REAL_SLEEP(0.5)
    ths = [threading.Thread(target=fake_refresher, daemon=True), threading.Thread(target=hb, daemon=True)]
    [x.start() for x in ths]
    REAL_SLEEP(0.2)
    out = []; r0 = dict(RD); t0 = REAL_TIME()
    def w():
        out.append((S.rival_now("L-meta-74999", 2), REAL_TIME() - t0))
    ws = [threading.Thread(target=w) for _ in range(20)]
    [x.start() for x in ws]; [x.join(60) for x in ws]
    reads_window = RD["ref"] - r0["ref"]
    stop.set(); REAL_SLEEP(0.1)
    took = max([x[1] for x in out] or [99])
    case("16.14-20-waiters-no-worker-read", len(out) == 20 and RD["worker"] == 0 and all(x[0] is None for x in out),
         f"(worker reads {RD['worker']}, answers {len(out)}, rivals {[x[0] for x in out if x[0]][:2]})")
    case("16.14-20-waiters-at-most-2-reads", reads_window <= 2 and took < 12, f"(refresher reads while they waited {reads_window}, all answered in {took:.1f} s)")
    # refresher dead (heartbeat 10 s old): one inline read and REFRESHER-DEAD
    for x in ths:
        x.join(15)
    put_hb(REAL_TIME() - 10)
    sn = json.load(open(os.path.join(SNAPD, "rival_snap.json"))); sn["t"] = REAL_TIME() - 30
    json.dump(sn, open(os.path.join(SNAPD, "rival_snap.json"), "w"))
    S.gh = orig; RD["worker"] = 0
    try:
        os.remove(os.path.join(SNAPD, "refdead"))
    except OSError:
        pass
    if hasattr(S, "WREADS"):
        S.WREADS["snap"] = 0
        S.rival_now("L-meta-74999", 2)
        case("16.14-dead-refresher-inline-and-alert", S.WREADS["snap"] == 1 and os.path.exists(os.path.join(SNAPD, "refdead")),
             f"(inline reads {S.WREADS['snap']})")
    else:
        case("16.14-dead-refresher-inline-and-alert", False, "(no REFRESHER-DEAD in this submit.py)")
    os.remove(os.path.join(SNAPD, "refresh.hb"))
    S.time.time = lambda: CLK[0]
    S.time.sleep = lambda s: CLK.__setitem__(0, CLK[0] + s)
    if D is not None and hasattr(D, "stall_tick"):
        dr = open(os.path.join(os.path.dirname(D.__file__), "drain.py")).read()
        case("16.14-REFRESHER-DEAD-alert-in-drain", "REFRESHER-DEAD" in dr, "")

# ---- 16.14 gaps.json (canary a43dfbe0: the same convoy on the shared 7 MB gaps copy): 20 waiters, a pull of 2 s
S.time.time, S.time.sleep = REAL_TIME, REAL_SLEEP
GD = tempfile.mkdtemp(); os.environ["RIVAL_SNAP_DIR"] = GD
PULLS_G = [0]; sv_curl = S.curl_json
def slow_curl(url, timeout=60):
    PULLS_G[0] += 1; REAL_SLEEP(2.0)
    return {"gaps": [{"id": "L-meta-1"}], "n": PULLS_G[0]}
S.curl_json = slow_curl
open(os.path.join(GD, "gaps.t"), "w").write(str(REAL_TIME() - 60)); json.dump({"gaps": []}, open(os.path.join(GD, "gaps.json"), "w"))
outg = []
ws = [threading.Thread(target=lambda: outg.append(S.gaps_json())) for _ in range(20)]
t0 = REAL_TIME(); [x.start() for x in ws]; [x.join(120) for x in ws]
case("16.14-gaps-20-waiters-at-most-2-pulls", len(outg) == 20 and PULLS_G[0] <= 2 and REAL_TIME() - t0 < 8,
     f"(pulls {PULLS_G[0]}, answered {len(outg)} in {REAL_TIME() - t0:.1f} s)")
S.curl_json = sv_curl; os.environ["RIVAL_SNAP_DIR"] = SNAPD
S.time.time = lambda: CLK[0]
S.time.sleep = lambda s: CLK.__setitem__(0, CLK[0] + s)

# ---- Lead 07:31: sight-to-create per created PR
if hasattr(S, "sight_line"):
    os.environ["READY_MSG"] = "ready L-meta-1\n\nSight: 1800000000\n"; os.environ["READY_T"] = "1800000020"
    l = S.sight_line("L-meta-1", 1800000041.5)
    os.environ["READY_MSG"] = ""; os.environ["READY_T"] = ""
    l2 = S.sight_line("L-meta-1", 1800000041.5)
    case("07:31-sight-to-create-logged", "sight->create 41.5 s" in l and "ready->create 21.5 s" in l and "n/a" in l2, f"({l})")
else:
    case("07:31-sight-to-create-logged", False, "(no sight_line)")

# ---- Lead 09:10: a refused head push (429/403) is a 16.13 refusal (stall for every worker, alert), then pushed again
if hasattr(S, "push_branch"):
    PD = tempfile.mkdtemp(); svd = os.environ.get("PR_GATE_DIR"); os.environ["PR_GATE_DIR"] = PD
    sv = (S.run, S.git, getattr(S, "upbase_ref", None))
    calls = []
    def prun(a, **k):
        if "push" in a:
            calls.append(1)
            if len(calls) == 1:
                return subprocess.CompletedProcess(a, 1, "", "remote: error: Too Many Requests (429)\nfatal: unable to access")
        return subprocess.CompletedProcess(a, 0, "", "")
    S.run = prun; S.git = lambda *a, **k: subprocess.CompletedProcess(a, 0, "abc\n", "")
    if sv[2]:
        S.upbase_ref = lambda b: "upbase/x"
    t0c = CLK[0]
    e = S.push_branch("c" * 40, "L-meta-1")
    # Lead 09:22 R1: a push refusal has its own counter (pushrefusals) and never counts toward the create giveup
    k = int(open(os.path.join(PD, "pushrefusals")).read()) if os.path.exists(os.path.join(PD, "pushrefusals")) else 0
    k = k if not os.path.exists(os.path.join(PD, "refusals")) else -1
    case("09:10-push-429-is-a-refusal", e is None and len(calls) == 2 and k == 1 and CLK[0] - t0c >= 59,
         f"(err {e}, pushes {len(calls)}, refusals {k}, waited {CLK[0] - t0c:.0f} s)")
    S.run, S.git = sv[0], sv[1]
    if sv[2]:
        S.upbase_ref = sv[2]
    if svd is None:
        os.environ.pop("PR_GATE_DIR", None)
    else:
        os.environ["PR_GATE_DIR"] = svd
else:
    case("09:10-push-429-is-a-refusal", False, "(no push_branch)")

# ---- Lead 09:29: RUN-TOKEN-EMPTY: a read refused for the run token's primary limit goes to PR_TOKEN until its reset
if hasattr(S, "runtoken_empty"):
    RD = tempfile.mkdtemp(); svd = os.environ.get("RIVAL_SNAP_DIR"); os.environ["RIVAL_SNAP_DIR"] = RD
    svr, svt = S.run, (S.READ_TOKEN, S.PR_TOKEN)
    S.READ_TOKEN, S.PR_TOKEN = "RT", "PT"
    used = []
    def rrun(a, **k):
        tok = (k.get("env") or {}).get("GH_TOKEN")
        if a[:3] == ["gh", "api", "rate_limit"]:
            return subprocess.CompletedProcess(a, 0, str(int(REAL_TIME()) + 900), "")
        used.append(tok)
        if tok == "RT" and "sec" in a:
            return subprocess.CompletedProcess(a, 1, "", "HTTP 403: You have exceeded a secondary rate limit")
        if tok == "RT":
            return subprocess.CompletedProcess(a, 1, "", "HTTP 403: API rate limit exceeded for installation ID 1")
        return subprocess.CompletedProcess(a, 0, "[]", "")
    S.run = rrun; svgh = S.gh; S.gh = REAL_GH
    svtime = S.time.time; S.time.time = REAL_TIME
    try:
        r1 = S.gh(["api", "repos/x/pulls"]); u1 = list(used); used.clear()
        r2 = S.gh(["api", "repos/x/pulls"]); u2 = list(used); used.clear()
        S.gh(["api", "repos/x/w"], write=True); u3 = list(used); used.clear()
        os.remove(os.path.join(RD, "runtoken-empty"))
        try:
            S.gh(["api", "sec"]); u4 = list(used)
        except RuntimeError:
            u4 = list(used)
        sec_ok = not os.path.exists(os.path.join(RD, "runtoken-empty")) and "PT" not in u4
    finally:
        S.run = svr; S.gh = svgh; S.READ_TOKEN, S.PR_TOKEN = svt; S.time.time = svtime
        if svd is None:
            os.environ.pop("RIVAL_SNAP_DIR", None)
        else:
            os.environ["RIVAL_SNAP_DIR"] = svd
    S.run = lambda a, **k: (used.append((k.get("env") or {}).get("GH_TOKEN")) or subprocess.CompletedProcess(
        a, 0, "HTTP/2.0 200 OK\nX-Ratelimit-Remaining: 150\nX-Ratelimit-Reset: %d\n\n[]" % (int(REAL_TIME()) + 900), ""))
    S.gh = REAL_GH; S.READ_TOKEN, S.PR_TOKEN = "RT", "PT"; os.environ["RIVAL_SNAP_DIR"] = RD; S.time.time = REAL_TIME
    used.clear(); S.gh(["api", "-i", "p"]); S.gh(["api", "-i", "p"]); u5 = list(used)
    S.run = svr; S.gh = svgh; S.READ_TOKEN, S.PR_TOKEN = svt; S.time.time = svtime
    if svd is None:
        os.environ.pop("RIVAL_SNAP_DIR", None)
    else:
        os.environ["RIVAL_SNAP_DIR"] = svd
    case("09:34-runtoken-under-200-switches", u5 == ["RT", "PT"], f"({u5})")
    def lrun(a, **k):
        tok = (k.get("env") or {}).get("GH_TOKEN"); used.append(tok)
        if tok == "RT":
            return subprocess.CompletedProcess(a, 1, "", "HTTP 403: API rate limit exceeded for installation ID 1")
        return subprocess.CompletedProcess(a, 0, "HTTP/2.0 200 OK\nX-Ratelimit-Remaining: 1200\nX-Ratelimit-Reset: %d\n\n[]"
                                           % (int(REAL_TIME()) + 900), "")
    RD2 = tempfile.mkdtemp(); os.environ["RIVAL_SNAP_DIR"] = RD2
    S.run = lrun; S.gh = REAL_GH; S.READ_TOKEN, S.PR_TOKEN = "RT", "PT"; S.time.time = REAL_TIME
    used.clear(); S.gh(["api", "-i", "p"])
    try:
        S.gh(["api", "-i", "p"]); second = "read"
    except RuntimeError:
        second = "refused"
    u6 = list(used)
    S.run = svr; S.gh = svgh; S.READ_TOKEN, S.PR_TOKEN = svt; S.time.time = svtime
    if svd is None:
        os.environ.pop("RIVAL_SNAP_DIR", None)
    else:
        os.environ["RIVAL_SNAP_DIR"] = svd
    case("09:46-prtoken-under-1500-no-reads", u6 == ["RT", "RT", "PT"] and second == "refused", f"({u6}, second read {second})")
    case("09:29-runtoken-empty-reads-go-to-PR_TOKEN", u1 == ["RT", "PT"] and u2 == ["PT"] and u3 == ["PT"] and sec_ok,
         f"(first {u1}, next {u2}, write {u3}, secondary {u4})")
else:
    case("09:29-runtoken-empty-reads-go-to-PR_TOKEN", False, "(no fallback: an empty run token = every read fails closed)")

# ---- Lead 09:40 (lane movingmain, part 2): a rival PR that left the open list (merged or closed) holds its unit 60 s
if hasattr(S, "RIVAL_GONE_S"):
    S.time.time = lambda: CLK[0]
    S.time.sleep = lambda s: CLK.__setitem__(0, CLK[0] + s)
    S.gh = orig
    reset_snap(); PULLS.clear(); TL_ROWS.pop("L-meta-76999", None)
    add_pr(76001, CLK[0] - 5, "Prove L-meta-76999")
    r0 = RN("L-meta-76999", 2)
    PULLS.clear(); CLK[0] += 3; t_g = CLK[0]           # the rival PR merged: gone from the open list
    rg = RN("L-meta-76999", 2)                          # the first build that misses it (t)
    out = {}
    for dt in (1, 59, 61):
        CLK[0] = t_g + dt
        out[dt] = RN("L-meta-76999", 2)
    case("09:40-gone-rival-held-60s", bool(r0) and bool(rg) and "left the open list" in (rg or "") and bool(out[1]) and bool(out[59])
         and out[61] is None, f"(open {r0}, t {rg}, t+1 {out[1]}, t+59 {out[59]}, t+61 {out[61]})")
    TL_ROWS["L-meta-76999"] = "rival9"; S._TL.clear(); S.TL_T[0] = 0.0
    CLK[0] = t_g + 62
    rt = RN("L-meta-76999", 2)
    TL_ROWS.pop("L-meta-76999", None)
    case("09:40-gone-after-60s-taken-list-still-rules", bool(rt) and rt.startswith("taken list"), f"({rt})")
    reset_snap(); PULLS.clear(); add_pr(76002, CLK[0] - 5, "Prove L-meta-76998")
    RN("L-meta-76998", 2); CLK[0] += 3
    add_pr(76003, CLK[0] - 1, "Prove L-meta-76997")
    rr = RN("L-meta-76998", 2)                          # still open: the open PR rules, nothing gone
    case("09:40-open-rival-not-gone", (rr or "").startswith("#76002"), f"({rr})")
    PULLS.clear(); reset_snap()
else:
    case("09:40-gone-rival-held-60s", False, "(no RIVAL_GONE_S in this submit.py)")

bad = [n for n, ok in res if not ok]
print(f"RCB SELFTEST OK {len(res)}" if not bad else "RCB SELFTEST FAIL " + " ".join(bad))
sys.exit(1 if bad else 0)
