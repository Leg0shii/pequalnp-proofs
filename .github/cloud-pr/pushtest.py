# pushtest.py [dir of submit.py]: PUSH REFUSAL (Lead 09:08, HARDENING 16.13 extended), in-process, git faked.
#   U1  ladder: a refusal waits 60, 120, 240 s (1st, 2nd, 3rd), the 4th gives up (same as a create refusal)
#   U2  push_refused: the 429 text of 08:49:57 and the 403 texts are refusals; "ref exists" / stale-info rejections and
#       a 500 are not; the old TRANSIENT pattern did not even see the 429 text (it was treated as a hard failure)
#   P1  429 inside a burst of 28 workers: exactly one stall, 0 pushes start during it, creates wait during it and
#       until the refused unit has pushed, the refused unit pushes FIRST after it (once), 0 units lost
#   P2  the same with the 403 text
#   P3  a push rejected because the ref exists: no stall, no refusal, the error goes back to the caller
#   P4  the retry after the stall is refused too: a second refusal, the unit returns an error (the drain retries it),
#       the push-first token is cleared and the other workers go on
# The stall length is scaled down for the run (refusal_wait patched to 1.5 s * 2^(k-1)); U1 checks the real ladder.
# Prints one line per case and "PUSH SELFTEST OK <n>" or "PUSH SELFTEST FAIL <cases>". Exit 0 iff OK.
import os, subprocess, sys, tempfile, threading, time

GATE = tempfile.mkdtemp()
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), RIVAL_SNAP_DIR=GATE,
                  PR_GATE_DIR=GATE, GHCOND_DIR=tempfile.mkdtemp(), PR_TOKEN="x")
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S

res = []


def case(name, ok, why=""):
    res.append((name, bool(ok)))
    print(("ok   " if ok else "FAIL ") + f"push/{name} {why}")


T429 = "fatal: unable to access 'https://github.com/Leg0shii/pequalnp-proofs-fork/': The requested URL returned error: 429"
T403 = "error: RPC failed; HTTP 403 curl 22 The requested URL returned error: 403\nsend-pack: unexpected disconnect"
TEXISTS = " ! [rejected]        L-meta-7 -> L-meta-7 (stale info)\nerror: failed to push some refs"

# U1
lad = [S.refusal_wait(k, {}, 0) for k in (1, 2, 3)]
d1 = tempfile.mkdtemp()
ks = [S.bucket_refusal(d1, {}, "t", now=1000.0 + i)[0] for i in range(4)]
case("U1-ladder", lad == [60.0, 120.0, 240.0] and ks == [1, 2, 3, 4] and os.path.exists(os.path.join(d1, "giveup")),
     f"waits {lad}, 4th refusal -> giveup")

# U2
tab = [(T429, True), (T403, True), ("remote: HTTP 429 Too Many Requests", True), (TEXISTS, False),
       ("fatal: the remote end hung up; HTTP 500", False), ("", False)]
bad = [t[:30] for t, want in tab if S.push_refused(t) != want]
case("U2-texts", not bad and not S.TRANSIENT.search(T429), f"misread {bad}; old TRANSIENT saw the 429 text: {bool(S.TRANSIENT.search(T429))}")

REAL_WAIT = S.refusal_wait
S.refusal_wait = lambda k, hdr, now: 1.5 * 2 ** (k - 1)
S.log = lambda *a: LOG.append(" ".join(map(str, a)))
LOG = []
LK = threading.Lock()


def reset():
    for f in os.listdir(GATE):
        os.remove(os.path.join(GATE, f))
    LOG.clear()


def scenario(refuse_text, refuse_at=5, refuse_twice=False, n=28):
    """n workers push one unit each (staggered 30 ms); push number refuse_at answers refuse_text (and, with refuse_twice,
    that unit's retry too). Returns the push log [(start, gid, rc)], the results, and the creates check."""
    reset()
    st = {"n": 0, "refused": None}
    pushes = []

    def fake_run(cmd, timeout=300, env=None, cwd=None):
        if "push" in cmd:
            gid = cmd[-1].split("refs/heads/")[-1]
            with LK:
                st["n"] += 1
                k = st["n"]
                t = time.time()
                rc, err = 0, ""
                if k == refuse_at or (refuse_twice and gid == st["refused"]):
                    rc, err = 128, refuse_text
                    st["refused"] = gid
                elif refuse_text == TEXISTS and k == refuse_at:
                    rc, err = 1, TEXISTS
                pushes.append((t, gid, rc))
            time.sleep(0.05)
            return subprocess.CompletedProcess(cmd, rc, "", err)
        return subprocess.CompletedProcess(cmd, 0, "", "")

    S.run = fake_run
    out = {}
    creates = []

    def creator():                                   # a worker that would create: asks bucket_wait every 50 ms
        t_end = time.time() + 6
        while time.time() < t_end:
            creates.append((time.time(), S.bucket_wait(GATE, time.time())))
            time.sleep(0.05)

    def w(i):
        time.sleep(0.03 * i)
        out[f"L-meta-{i}"] = S.push_branch("c" * 40, f"L-meta-{i}")

    ths = [threading.Thread(target=w, args=(i,)) for i in range(n)] + [threading.Thread(target=creator)]
    [t.start() for t in ths]
    [t.join(60) for t in ths]
    return pushes, out, creates, st


def judge(name, text):
    pushes, out, creates, st = scenario(text)
    ref = [p for p in pushes if p[2]]
    t_ref = ref[0][0] if ref else 0
    until = t_ref + 0.05 + 1.5
    during = [p for p in pushes if t_ref + 0.06 < p[0] < until - 0.05]
    after = [p for p in pushes if p[0] >= until - 0.05]
    first_after = after[0][1] if after else None
    ok_units = [g for g, e in out.items() if e is None]
    refused_retry = [p for p in pushes if p[1] == st["refused"]]
    blocked = [c for c in creates if t_ref + 0.06 < c[0] < until - 0.05]
    k = S.refusals(GATE)
    case(name, len(ref) == 1 and k == 1 and not during and first_after == st["refused"] and len(refused_retry) == 2
         and len(ok_units) == 28 and blocked and all(b[1] > 0 for b in blocked) and not os.path.exists(os.path.join(GATE, "pushfirst"))
         and any(l.startswith("PUSH-REFUSED") for l in LOG) and os.path.exists(os.path.join(GATE, "pushrefused")),
         f"stalls {k}, pushes during the stall {len(during)}, first push after it {first_after} (refused {st['refused']}), "
         f"its pushes {len(refused_retry)}, units pushed {len(ok_units)}/28, creates held during it {len(blocked)} checks "
         f"(all waiting: {all(b[1] > 0 for b in blocked)})")


judge("P1-429-burst", T429)
judge("P2-403-burst", T403)

# P3 ref exists: not a refusal
reset()
S.run = lambda cmd, timeout=300, env=None, cwd=None: subprocess.CompletedProcess(cmd, 1 if "push" in cmd else 0, "",
                                                                                  TEXISTS if "push" in cmd else "")
e = S.push_branch("c" * 40, "L-meta-7")
case("P3-ref-exists", e and "rejected" in e and S.refusals(GATE) == 0 and not os.path.exists(os.path.join(GATE, "stall")),
     f"returned {e[:40]!r}, refusals {S.refusals(GATE)}")

# P4 refused twice
pushes, out, creates, st = scenario(T429, refuse_twice=True)
e = out.get(st["refused"]) or ""
others = [g for g, x in out.items() if g != st["refused"] and x is None]
case("P4-refused-twice", e.startswith("PUSH-REFUSED twice") and S.refusals(GATE) == 2 and len(others) == 27
     and not os.path.exists(os.path.join(GATE, "pushfirst")),
     f"unit {st['refused']} -> {e[:30]!r}, refusals {S.refusals(GATE)}, other units pushed {len(others)}/27")

S.refusal_wait = REAL_WAIT
bad = [n for n, ok in res if not ok]
print(f"PUSH SELFTEST OK {len(res)}" if not bad else f"PUSH SELFTEST FAIL {bad}")
sys.exit(1 if bad else 0)
