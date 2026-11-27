# accttest.py [dir of submit.py]: BURST account caps (Lead 20:15 UTC 27 Nov), in-process, search faked.
#   A1 account at 399 PRs in the hour -> create now; at 400 -> wait   A2 account 60 in the last minute -> wait
#   A3 search failing for over 300 s -> the drain's own counts alone   A4 ACCT_CAP unset -> no search read at all
#   A5 the read is cached for ACCT_EVERY_S (one search per 20 s, not per create)
import os, sys, tempfile, time
os.environ.update(ID="L-meta-3", MOD="L_meta_3", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), DRY="1",
                  RIVAL_SNAP_DIR=tempfile.mkdtemp(), GHCOND_DIR=tempfile.mkdtemp(), PR_PER_MIN="60", PR_PER_HOUR="400")
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S
res = []
def case(n, ok, why=""):
    res.append(ok); print(("ok   " if ok else "FAIL ") + f"acct/{n} {why}")
calls = [0]; val = [(0, 0)]
def fake(now):
    calls[0] += 1
    return val[0]
S._acct_read = fake
os.environ["ACCT_CAP"] = "1"
def fresh():
    d = tempfile.mkdtemp(); return d
now = time.time()
d = fresh(); val[0] = (0, 399); w = S.bucket_wait(d, now); case("A1-399-create", w == 0, f"wait {w}")
d = fresh(); val[0] = (0, 400); w = S.bucket_wait(d, now); case("A1-400-wait", w > 0, f"wait {w}")
d = fresh(); val[0] = (60, 100); w = S.bucket_wait(d, now); case("A2-minute-wait", w > 0, f"wait {w}")
d = fresh(); val[0] = (0, 400); S.bucket_wait(d, now); val[0] = None
w = S.bucket_wait(d, now + 301); case("A3-stale-own-counts", w == 0, f"wait {w}")
os.environ["ACCT_CAP"] = "0"; c0 = calls[0]; d = fresh(); val[0] = (60, 400)
w = S.bucket_wait(d, now); case("A4-off", w == 0 and calls[0] == c0, f"wait {w} reads {calls[0] - c0}")
os.environ["ACCT_CAP"] = "1"; d = fresh(); val[0] = (0, 10); c0 = calls[0]
for k in range(30): S.bucket_wait(d, now + k * 0.5)
case("A5-cached", calls[0] - c0 == 1, f"reads {calls[0] - c0} for 30 creates in 15 s")
print("ACCT SELFTEST", "OK" if all(res) else "FAIL", len(res)); sys.exit(0 if all(res) else 1)
