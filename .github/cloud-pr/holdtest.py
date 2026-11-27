# holdtest.py [dir of submit.py]: the closer HOLD (Lead ruling 08:27, 27 Nov), in-process with GitHub faked.
#   H1  beat 299 s old = creates go; 301 s = hold
#   H2  a fresh beat after a hold lifts it within one refresher pass (one halt read + one reader step)
#   H3  an unreadable beat (ref missing from the halt read, or its message unreadable) holds only after 300 s
#   H4  loop=STUCK299 = go, loop=STUCK301 = hold
#   H5  the halt read carries status/dupclose in the same ls-remote; the stop/go verdict is unchanged by it
#   H6  workers: filing_halted() holds on the refresher's closer copy, the refresher's own read (max_age 0) never
#       does, a dead reader (copy not advancing) holds after 300 s, no drain (RIVAL_SNAP_DIR unset) never holds
#   H7  a hold logs "HOLD closer-stale age=<s>" once and alerts CLOSER-STALE once per 5 min (3 alerts in 700 s)
#   H8  only one fetch of the beat message per new sha (no read per pass)
# Prints one line per case and "HOLD SELFTEST OK <n>" or "HOLD SELFTEST FAIL <cases>". Exit 0 iff OK.
import json, os, sys, tempfile, time

SNAPD = tempfile.mkdtemp()
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), RIVAL_SNAP_DIR=SNAPD,
                  GHCOND_DIR=tempfile.mkdtemp())
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S

res = []


def case(name, ok, why=""):
    res.append((name, bool(ok)))
    print(("ok   " if ok else "FAIL ") + f"hold/{name} {why}")


T0 = 1_800_000_000.0
MSG = {"n": 0}
real_msg = S._closer_msg


def msg_counting():
    MSG["n"] += 1
    return real_msg()


S._closer_msg = msg_counting


def fresh():
    S._CS.update(sha=None, sha_t=0.0, hold=False, alerted=0.0)
    return {"ok": T0, "cb": None, "cs": 0, "seen_sha": None, "seen_t": 0.0}


def ls(sha, extra="", t=None):
    """what the refresher's halt read sees at time t: filing refs plus status/dupclose at sha (None = missing)"""
    txt = "a" * 40 + "\trefs/heads/filing/go/100\n" + extra + (f"{sha}\trefs/heads/status/dupclose\n" if sha else "")
    os.environ["FILING_FIXTURE"] = txt
    real = S.time.time
    S.time.time = lambda: t
    try:
        return S._filing_halted_read()
    finally:
        S.time.time = real


def beat(epoch, stuck=None):
    os.environ["CLOSER_BEAT_FIXTURE"] = f"dupclose {int(epoch)} " + (f"loop=STUCK{stuck} in={stuck}s" if stuck else "loop=3") + " step=list"


# H1: 299 s go, 301 s hold
for age, want in ((299, False), (301, True)):
    st = fresh()
    beat(T0)
    ls("b" * 40, t=T0 + age)
    h, why = S.closer_step(st, T0 + age)
    case(f"H1-age{age}", h == want, why or "go")

# H2: hold, then a fresh beat on the next halt read lifts it in one step
st = fresh()
beat(T0)
ls("b" * 40, t=T0 + 301)
h1, w1 = S.closer_step(st, T0 + 301)
beat(T0 + 330)
ls("c" * 40, t=T0 + 331)                     # one refresher pass: the halt read sees the new sha
h2, w2 = S.closer_step(st, T0 + 331.2)       # one reader step (0.2 s)
case("H2-resume", h1 and not h2, f"held ({w1}), then {w2 or 'go'} 0.2 s after the halt read saw the new beat")

# H3: unreadable holds only after 300 s
for label, sha, m in (("ref-missing", None, None), ("msg-unreadable", "d" * 40, "")):
    st = fresh()
    out = []
    for dt in (1, 150, 299, 301):
        if m is not None:
            os.environ["CLOSER_BEAT_FIXTURE"] = m
        ls(sha, t=T0 + dt)
        out.append(S.closer_step(st, T0 + dt)[0])
    case(f"H3-{label}", out == [False, False, False, True], f"hold at 1/150/299/301 s of failed reads = {out}")
# a read failing after a good one: judged on the beat's age at the last good read, holds after 300 s of failures
st = fresh()
beat(T0 + 900)
ls("e" * 40, t=T0 + 950)
S.closer_step(st, T0 + 950)
S._CS.update(sha=None, sha_t=T0 + 1100)          # the ref vanished / later reads fail
a = S.closer_step(st, T0 + 1200)[0]
b = S.closer_step(st, T0 + 1251)[0]
case("H3-fail-after-good", (a, b) == (False, True), f"250 s of failed reads {a}, 301 s {b}")

# H4: STUCK
for s_, want in ((299, False), (301, True)):
    st = fresh()
    beat(T0, stuck=s_)
    ls("f" * 40, t=T0 + 10)
    h, why = S.closer_step(st, T0 + 10)
    case(f"H4-stuck{s_}", h == want, why or "go")

# H5: same ls-remote, verdict unchanged
v1 = ls("b" * 40, t=T0)
v2 = ls(None, t=T0)
v3 = ls("b" * 40, extra="9" * 40 + "\trefs/heads/filing/stop/200\n", t=T0)
src = open(S.__file__).read()
one = '"refs/heads/filing/*",\n                         "refs/heads/status/dupclose"]' in src
case("H5-one-read", v1 == v2 and v1[0] is False and v3[0] is True and S._CS["sha"] == "b" * 40 and one,
     f"go/go/stop = {v1[0]}/{v2[0]}/{v3[0]}, dupclose sha taken from the halt ls-remote")
os.environ.pop("FILING_FIXTURE", None)

# H6: workers read the copy
now = time.time()
json.dump({"t": now, "halted": False, "why": ""}, open(os.path.join(SNAPD, "halt.json"), "w"))
cf = os.path.join(SNAPD, "closer.json")
json.dump({"t": now, "ok": now, "cb": now - 301, "cs": 0, "hold": True, "why": ""}, open(cf, "w"))
w_hold = S.filing_halted()
os.environ["FILING_FIXTURE"] = "a" * 40 + "\trefs/heads/filing/go/100\n"     # refs say go (no network read here)
ref_own = S.filing_halted(0)
os.environ.pop("FILING_FIXTURE")
json.dump({"t": time.time(), "halted": False, "why": ""}, open(os.path.join(SNAPD, "halt.json"), "w"))
json.dump({"t": now, "ok": now, "cb": now - 20, "cs": 0, "hold": False, "why": ""}, open(cf, "w"))
w_go = S.filing_halted()
json.dump({"t": now - 301, "ok": now - 301, "cb": now - 320, "cs": 0}, open(cf, "w"))
dead299 = S.closer_hold_now(now - 2)[0]
dead301 = S.closer_hold_now(now)[0]
os.environ.pop("RIVAL_SNAP_DIR")
nodrain = S.closer_hold_now()[0]
os.environ["RIVAL_SNAP_DIR"] = SNAPD
case("H6-workers", w_hold[0] and w_hold[1].startswith("HOLD closer-stale age=") and not w_go[0] and not dead299 and dead301
     and not nodrain and not ref_own[0],
     f"stale copy -> {w_hold}, fresh -> {w_go[0]}, refresher's own read -> {ref_own[0]}, dead reader 299/301 s -> "
     f"{dead299}/{dead301}, no drain -> {nodrain}")

# H7 + H8: the reader loop under a fake clock, 700 s held
CLK = [T0]
logs, alerts = [], []
real_time, real_sleep, real_log, real_alert = S.time.time, S.REAL_SLEEP, S.log, S._closer_alert
S.time.time = lambda: CLK[0]
S.REAL_SLEEP = lambda s: CLK.__setitem__(0, CLK[0] + s)
S.log = lambda *a: logs.append(" ".join(str(x) for x in a))
S._closer_alert = lambda m: alerts.append(m) or True
fresh()
beat(T0 - 400)
S._CS.update(sha="1" * 40, sha_t=T0)
MSG["n"] = 0
passes = [0]


def stop():
    passes[0] += 1
    S._CS["sha_t"] = CLK[0]                  # the halt read sees the same sha every pass
    return CLK[0] - T0 >= 700


try:
    S.closer_reader(stop)
finally:
    S.time.time, S.REAL_SLEEP, S.log, S._closer_alert = real_time, real_sleep, real_log, real_alert
holdlog = [l for l in logs if l.startswith("HOLD closer-stale age=")]
case("H7-log-alert", len(holdlog) == 1 and len(alerts) == 3 and all(a.startswith("CLOSER-STALE HOLD closer-stale") for a in alerts),
     f"{passes[0]} passes, hold log lines {len(holdlog)} ({holdlog[:1]}), alerts {len(alerts)}")
case("H8-one-fetch", MSG["n"] == 1, f"beat message reads over {passes[0]} passes of one sha: {MSG['n']}")
c = json.load(open(cf))
case("H7-copy", c.get("hold") is True and c.get("cb") == int(T0 - 400), f"closer.json {c}")

bad = [n for n, ok in res if not ok]
print(f"HOLD SELFTEST OK {len(res)}" if not bad else f"HOLD SELFTEST FAIL {bad}")
sys.exit(1 if bad else 0)
