# headstest.py [dir of submit.py]: fork_head from one shared read per second (Lead 08:17, 16.14), GitHub faked.
#   F1  refresher alive: fork_head answers from the refresher's heads copy whose read started after the ask (an older
#       copy is never used), no own ls-remote, no sleep of 1 s or more
#   F2  a copy whose read failed raises (callers fail closed)
#   F3  refresher dead: one inline read, REFRESHER-DEAD marker written
#   F4  no drain (RIVAL_SNAP_DIR unset): inline read, no sleep between tries
#   F5  heads_reader: one ls-remote per pass, heads.json {t at read start, ok, heads}
#   F6  28 workers asking at once while the reader runs: one ls-remote per HEADS_S, not one per ask
# Prints one line per case and "HEADS SELFTEST OK <n>" or "HEADS SELFTEST FAIL <cases>". Exit 0 iff OK.
import json, os, subprocess, sys, tempfile, threading, time

SNAPD = tempfile.mkdtemp()
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), RIVAL_SNAP_DIR=SNAPD,
                  GHCOND_DIR=tempfile.mkdtemp())
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S

res = []


def case(name, ok, why=""):
    res.append((name, bool(ok)))
    print(("ok   " if ok else "FAIL ") + f"heads/{name} {why}")


LS = {"n": 0, "rc": 0, "delay": 0.0}
HEADS = {"L-meta-1": "1" * 40, "L-meta-2": "2" * 40}


def fake_run(cmd, timeout=300, env=None, cwd=None):
    if "ls-remote" in cmd:
        LS["n"] += 1
        if LS["delay"]:
            time.sleep(LS["delay"])
        pat = cmd[-1]
        rows = [f"{v}\trefs/heads/{k}" for k, v in HEADS.items() if pat == "refs/heads/L-*" or pat == f"refs/heads/{k}"]
        return subprocess.CompletedProcess(cmd, LS["rc"], "\n".join(rows) + "\n", "")
    raise AssertionError(f"unexpected run {cmd}")


S.run = fake_run
SLEEPS = []
real_sleep = S.time.sleep


def rec_sleep(s):
    SLEEPS.append(s)
    real_sleep(s)


S.time.sleep = rec_sleep
HB = os.path.join(SNAPD, "refresh.hb")
HF = os.path.join(SNAPD, "heads.json")


def hb(age=0.0):                       # written like the refresher does (tmp + replace)
    open(HB + ".t", "w").write(f"{time.time() - age:.1f} 1 0 0 0\n")
    os.replace(HB + ".t", HB)


def copy(t, ok=True, heads=None):
    json.dump({"t": t, "ok": ok, "heads": HEADS if heads is None else heads}, open(HF + ".t", "w"))
    os.replace(HF + ".t", HF)


# F1: an older copy is ignored; the newer one answers; no own read
hb()
copy(time.time() - 0.5, heads={"L-meta-1": "0" * 40})          # stale: says another sha
LS["n"] = 0
SLEEPS.clear()
threading.Timer(0.3, lambda: (hb(), copy(time.time()))).start()
t0 = time.time()
h = S.fork_head("L-meta-1")
dt = time.time() - t0
threading.Timer(0.2, lambda: (hb(), copy(time.time()))).start()
none = S.fork_head("L-meta-9")
case("F1-copy", h == "1" * 40 and none is None and LS["n"] == 0 and not [s for s in SLEEPS if s >= 1],
     f"sha {h[:8] if h else h} after {dt:.2f} s (stale copy ignored), missing branch -> {none}, own ls-remote {LS['n']}, "
     f"sleeps >= 1 s: {[s for s in SLEEPS if s >= 1]}")

# F2: failed shared read raises
hb()
threading.Timer(0.2, lambda: (hb(), copy(time.time(), ok=False, heads={}))).start()
try:
    S.fork_head("L-meta-1")
    case("F2-unreadable", False, "no raise")
except RuntimeError as e:
    case("F2-unreadable", True, f"raises: {e}")

# F3: refresher dead
hb(age=60)
try:
    os.remove(os.path.join(SNAPD, "refdead"))
except OSError:
    pass
LS["n"] = 0
h = S.fork_head("L-meta-2")
rd = open(os.path.join(SNAPD, "refdead")).read().strip() if os.path.exists(os.path.join(SNAPD, "refdead")) else ""
case("F3-dead", h == "2" * 40 and LS["n"] == 1 and "heads" in rd, f"inline read {LS['n']}, refdead: {rd}")

# F4: no drain, inline; a failed try is retried at once, then raises
os.environ.pop("RIVAL_SNAP_DIR")
LS.update(n=0, rc=128)
SLEEPS.clear()
try:
    S.fork_head("L-meta-1")
    raised = False
except RuntimeError:
    raised = True
LS["rc"] = 0
ok4 = S.fork_head("L-meta-1") == "1" * 40
os.environ["RIVAL_SNAP_DIR"] = SNAPD
case("F4-nodrain", raised and ok4 and LS["n"] == 3 and not SLEEPS, f"tries {LS['n']}, sleeps {SLEEPS}")

# F5 + F6: the reader and 28 concurrent askers
os.remove(HF)
LS.update(n=0, delay=0.4)
stop = [False]
S.REAL_SLEEP = real_sleep
rt = threading.Thread(target=S.heads_reader, args=(lambda: stop[0],), daemon=True)
hbt = threading.Thread(target=lambda: [(hb(), real_sleep(0.5)) for _ in range(40)], daemon=True)
hbt.start()
rt.start()
out, t0 = [], time.time()


def worker(i):
    for _ in range(5):
        out.append(S.fork_head("L-meta-1" if i % 2 else "L-meta-404"))


ws = [threading.Thread(target=worker, args=(i,)) for i in range(28)]
[w.start() for w in ws]
[w.join() for w in ws]
el = time.time() - t0
stop[0] = True
rt.join(3)
c = json.load(open(HF))
case("F5-copy", c["ok"] and c["heads"] == HEADS and c["t"] <= time.time(), f"heads.json {len(c['heads'])} heads, ok={c['ok']}")
want = el / S.HEADS_S + 2
case("F6-one-read-per-s", len(out) == 140 and out.count("1" * 40) == 70 and out.count(None) == 70 and LS["n"] <= want,
     f"140 asks by 28 workers in {el:.1f} s: {LS['n']} ls-remote (bound {want:.0f})")

bad = [n for n, ok in res if not ok]
print(f"HEADS SELFTEST OK {len(res)}" if not bad else f"HEADS SELFTEST FAIL {bad}")
sys.exit(1 if bad else 0)
