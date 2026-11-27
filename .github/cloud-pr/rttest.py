# rttest.py [dir of dupclose.py]: RUN-TOKEN-EMPTY in the closer (Lead 09:38, incident 09:27 UTC: run token at 0, every
# closed-PR read failed 3 passes in a row, the closer pushed BLIND stop filing/stop/1795771628). In-process, network faked
# at dupclose._sh (the one door every call goes through).
#   T1  rl=150 from the beat's rate_limit read: reads go to PR_TOKEN at once, alert RUN-TOKEN-EMPTY once, back to the run
#       token after its reset; rl=250 changes nothing
#   T2  rl=0 with 403 "API rate limit exceeded": that read is sent again with PR_TOKEN and succeeds, the next reads go to
#       PR_TOKEN directly, one alert in 5 min however many reads, back to the run token after the reset
#   T3  the incident: run token refuses with 403, 3 rej_burst passes -> no blind stop (every pass scanned with PR_TOKEN)
#   T4  both tokens refused: 3 rej_burst passes -> the BLIND stop, as today
#   T5  429 "Too Many Requests" (no rate-limit words) -> PR_TOKEN; a secondary limit and a permission 403 do NOT switch
#   T6  RUNTOKEN_FALLBACK=0 or no READ_TOKEN: no switch (old behaviour)
# Prints one line per case and "RT SELFTEST OK <n>" or "RT SELFTEST FAIL <cases>". Exit 0 iff OK.
import os, subprocess, sys, tempfile, time

os.environ.update(PR_TOKEN="PT", READ_TOKEN="RT", W=tempfile.mkdtemp(), MINUTES="1", DRY="0")
for k in ("FIXTURE", "FIXTURE_OPEN", "FIXTURE_MERGED", "FIXTURE_CLOSED", "FIXTURE_FILING", "RUNTOKEN_FALLBACK"):
    os.environ.pop(k, None)
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import dupclose as D

res, LOG, ALERTS, STOPS, CALLS = [], [], [], [], []
D.log = lambda *a: LOG.append(" ".join(map(str, a)))
D.alert_ref = lambda msg, kind: ALERTS.append((kind, msg)) or True
D.filing_stop = lambda msg: STOPS.append(msg) or True
D.filing_go = lambda: 1795756649
D.halted_now = lambda: False
D.stop_listed = lambda: set()

E403 = "gh: API rate limit exceeded for installation ID 123456. (HTTP 403)"
E429 = "HTTP 429: Too Many Requests (https://api.github.com/repos/open-goat/pequalnp-proofs/pulls)"
ESEC = "gh: You have exceeded a secondary rate limit. Please wait a few minutes before you try again. (HTTP 403)"
EPERM = "gh: Resource not accessible by integration (HTTP 403)"
ST = {"rt": "ok", "pt": "ok", "reset": 0.0}


def fake(*a, timeout=120, env=None):
    tok = (env or {}).get("GH_TOKEN", "")
    CALLS.append((tok, " ".join(a[:3])))
    if a[0] != "gh":
        return subprocess.CompletedProcess(a, 0, "", "")
    if "rate_limit" in a:                                  # free, answers at 0
        return subprocess.CompletedProcess(a, 0, f"{ST['reset']:.0f}\n", "")
    err = {"rt": ST["rt"], "pt": ST["pt"]}["rt" if tok == "RT" else "pt"]
    if err != "ok":
        return subprocess.CompletedProcess(a, 1, "", err)
    return subprocess.CompletedProcess(a, 0, "[]", "")


def reset(rt="ok", pt="ok", reset_in=2.0):
    if hasattr(D, "RT"):
        D.RT.update(until=0.0, alert_t=0.0, why="", n=0)
    ST.update(rt=rt, pt=pt, reset=time.time() + reset_in)
    LOG.clear(); ALERTS.clear(); STOPS.clear(); CALLS.clear()
    D.REJ.clear(); D.REJ.update(t=0.0, alerted=0.0); D.HALTED.clear()


def case(name, ok, why=""):
    res.append((name, bool(ok)))
    print(("ok   " if ok else "FAIL ") + f"rt/{name} {why}")


def read():
    return D.sh("gh", "api", "repos/open-goat/pequalnp-proofs/pulls?state=closed", env=D.rdenv(), timeout=60)


if hasattr(D, "_sh"):
    D._sh = fake
else:                                                     # old code: no door, fake its sh
    D.sh = fake


def c0():
    # T1 rl=150
    reset()
    D.rt_rl("250", ST["reset"])
    a0 = D.rdenv()["GH_TOKEN"]
    D.rt_rl("150", ST["reset"])
    a1 = D.rdenv()["GH_TOKEN"]
    D.rt_rl("120", ST["reset"])
    n_al = len([x for x in ALERTS if x[0] == "runtokenempty"])
    time.sleep(2.7)  # reset epochs are whole seconds (rate_limit), rounded
    a2 = D.rdenv()["GH_TOKEN"]
    case("T1-rl150", a0 == "RT" and a1 == "PT" and a2 == "RT" and n_al == 1,
         f"rl=250 -> {a0}, rl=150 -> {a1}, after reset -> {a2}, alerts {n_al}")


def c1():
    # T2 rl=0 with 403
    reset(rt=E403)
    r1 = read()
    first = [c[0] for c in CALLS if "pulls" in c[1]]
    CALLS.clear()
    rs = [read() for _ in range(20)]
    nxt = sorted({c[0] for c in CALLS if "pulls" in c[1]})
    n_al = len([x for x in ALERTS if x[0] == "runtokenempty"])
    time.sleep(2.7)  # reset epochs are whole seconds (rate_limit), rounded
    ST["rt"] = "ok"
    CALLS.clear()
    read()
    back = [c[0] for c in CALLS if "pulls" in c[1]]
    case("T2-rl0-403", r1.returncode == 0 and first == ["RT", "PT"] and nxt == ["PT"] and all(x.returncode == 0 for x in rs)
         and n_al == 1 and back == ["RT"] and any(l.startswith("RUN-TOKEN-EMPTY") for l in LOG),
         f"first read {first} rc={r1.returncode}, next 20 reads {nxt}, alerts {n_al}, after reset {back}")


def c2():
    # T3 the incident: 3 passes, run token refused, PR_TOKEN fine -> no blind stop
    reset(rt=E403, reset_in=600)
    for _ in range(3):
        D.REJ["t"] = 0.0
        D.rej_burst()
    case("T3-incident-no-blind", not STOPS and D.REJ.get("scan") == "ok" and D.REJ.get("full") is True,
         f"stops {STOPS}, scan {D.REJ.get('scan')!r}")


def c3():
    # T4 both tokens refused -> the blind stop as today
    reset(rt=E403, pt=E403, reset_in=600)
    for _ in range(3):
        D.REJ["t"] = 0.0
        D.rej_burst()
    case("T4-both-dead-blind", len(STOPS) == 1 and STOPS[0].startswith(D.BLIND_TAG) and "3 passes in a row" in STOPS[0],
         f"stops {[s[:70] for s in STOPS]}")


def c4():
    # T5 kinds
    out = {}
    for nm, e in (("429", E429), ("secondary", ESEC), ("perm403", EPERM)):
        reset(rt=e)
        r = read()
        out[nm] = ([c[0] for c in CALLS if "pulls" in c[1]], r.returncode, D.rdenv()["GH_TOKEN"])
    case("T5-kinds", out["429"] == (["RT", "PT"], 0, "PT") and out["secondary"] == (["RT"], 1, "RT")
         and out["perm403"] == (["RT"], 1, "RT"), f"{out}")


def c5():
    # T6 switch off
    reset(rt=E403)
    os.environ["RUNTOKEN_FALLBACK"] = "0"
    r = read(); D.rt_rl("10", ST["reset"])
    off = ([c[0] for c in CALLS if "pulls" in c[1]], r.returncode, D.rdenv()["GH_TOKEN"])
    os.environ.pop("RUNTOKEN_FALLBACK")
    reset(rt=E403)
    D.RTOK = D.TOK
    r = read()
    same = ([c[0] for c in CALLS if "pulls" in c[1]], r.returncode)
    D.RTOK = "RT"
    case("T6-off", off == (["RT"], 1, "RT") and same == (["PT"], 0), f"RUNTOKEN_FALLBACK=0 {off}, no READ_TOKEN {same}")


for f in (c0, c1, c2, c3, c4, c5):
    try:
        f()
    except Exception as e:                                 # old code has no RT / rt_rl: that case fails
        case(f.__name__ + "-error", False, repr(e)[:120])

bad = [n for n, ok in res if not ok]
print(f"RT SELFTEST OK {len(res)}" if not bad else f"RT SELFTEST FAIL {bad}")
sys.exit(1 if bad else 0)
