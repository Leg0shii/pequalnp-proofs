# selftest_bucket.py [dir of submit.py]: the PR-create token bucket (Lead 06:12): 70 a minute, 480 an hour, a stall after a 403/429 blocks every worker.
import os, sys, tempfile
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), PR_PER_MIN="70", PR_PER_HOUR="480")
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))); import submit as S
d = tempfile.mkdtemp(); now = 1000.0
r = [S.bucket_wait(d, now + i * 0.01) for i in range(70)]
a = all(x == 0 for x in r)
w71 = S.bucket_wait(d, now + 0.8); b = 59 < w71 <= 60.1
c = S.bucket_wait(d, now + 60.1) == 0
open(os.path.join(d, "stall"), "w").write(str(now + 200))
e = S.bucket_wait(d, now + 100) > 99
d2 = tempfile.mkdtemp(); t = 0.0; n = 0
while n < 480:
    if S.bucket_wait(d2, t) == 0: n += 1
    else: t += 1
f = S.bucket_wait(d2, t + 1) > 0
print("BUCKET SELFTEST", "OK" if a and b and c and e and f else "FAIL", a, b, c, e, f, f"(480 creates took {t:.0f} s at 70/min)")
