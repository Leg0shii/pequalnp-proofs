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
    if cmd[0] == "git" and "ls-remote" in cmd:
        CNT["lsremote"] += 1
        return cp(LS["txt"], LS["rc"], "" if LS["rc"] == 0 else "fatal")
    raise RuntimeError("unexpected run " + " ".join(cmd[:3]))


class DG:
    REPO = "/nonexistent"


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


# ---- R3: a page read that takes 3 s
reset_snap()
add_pr(70001, CLK[0] - 5, "Prove L-meta-70001")
orig = S.gh
def slow_gh(args, write=False, timeout=120):
    if "/pulls?" in args[1]:
        CLK[0] += 3
    return orig(args, write, timeout)
S.gh = slow_gh
t_start = CLK[0]
try:
    snap = S.rival_snapshot(0)
    case("R3-stamp-at-start", abs(snap["t"] - t_start) < 0.01, f"(t - start = {snap['t'] - t_start:.1f} s, read took 3 s)")
except Exception as e:
    case("R3-stamp-at-start", False, repr(e)[:100])
S.gh = orig

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
import haltrule
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
    got = haltrule.verdict(txt, rc)[0]
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

bad = [n for n, ok in res if not ok]
print(f"RCB SELFTEST OK {len(res)}" if not bad else "RCB SELFTEST FAIL " + " ".join(bad))
sys.exit(1 if bad else 0)
