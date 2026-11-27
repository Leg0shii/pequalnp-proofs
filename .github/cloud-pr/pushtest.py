# pushtest.py [dir of submit.py]: PUSH REFUSAL (Lead 09:08/09:22, HARDENING 16.13 extended, red team R1 R3 R5),
# in-process, git faked, 28 workers per scenario.
#   U1  ladders: a PUSH refusal waits 60, 120, 240, 240 s and never gives up; a CREATE refusal keeps 60/120/240 + giveup
#   U2  texts: the 429 of 08:49:57, the bare 403 of r5, "Too Many Requests (429)", "secondary rate limit" = refused;
#       a 403 naming a permission = denied; ref-exists (also on unit L-meta-403/429), a 500, a 403 with remote: lines
#       and no permission word = neither
#   P1  429 in a burst: one stall, 0 pushes and 0 creates during it, the refused unit pushes first after it (once),
#       28/28 pushed, the push counter is 1 and the create counter 0
#   P2  the same with the bare 403
#   P3  ref exists (L-meta-7 and L-meta-403): no stall, no refusal
#   P4  the retry after the stall is refused too: 2 push refusals, the unit returns an error (the drain retries it),
#       the token is cleared, the other 27 push
#   P5  R1: 4 push refusals in one drain: no giveup, creates still possible, create counter 0, rate halved to the floor,
#       0 pushes during any stall, 28/28 pushed
#   P6  R3: a giveup file = no push at all; a halt = no push ("halted: "); a halt set DURING a stall = the refused unit
#       and everyone else push nothing after it
#   P7  R5: a permission 403 on one unit: no stall, PUSH-DENIED for that unit after one push, the other 27 push at once
# Stalls are scaled down (push_refusal_wait patched to 0.6 s * 2^(k-1)); U1 checks the real ladders.
# Prints one line per case and "PUSH SELFTEST OK <n>" or "PUSH SELFTEST FAIL <cases>". Exit 0 iff OK.
import os, subprocess, sys, tempfile, threading, time

GATE = tempfile.mkdtemp()
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), RIVAL_SNAP_DIR=GATE,
                  PR_GATE_DIR=GATE, GHCOND_DIR=tempfile.mkdtemp(), PR_TOKEN="x")
GO = "a" * 40 + "\trefs/heads/filing/go/100\n"
STOP = GO + "b" * 40 + "\trefs/heads/filing/stop/200\n"
os.environ["FILING_FIXTURE"] = GO
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S

res = []


def case(name, ok, why=""):
    res.append((name, bool(ok)))
    print(("ok   " if ok else "FAIL ") + f"push/{name} {why}")


T429 = "fatal: unable to access 'https://github.com/Leg0shii/pequalnp-proofs-fork/': The requested URL returned error: 429"
T403 = "error: RPC failed; HTTP 403 curl 22 The requested URL returned error: 403\nsend-pack: unexpected disconnect while reading sideband packet"
TDEN = ("remote: Permission to Leg0shii/pequalnp-proofs-fork.git denied to someone.\n"
        "fatal: unable to access 'https://github.com/Leg0shii/pequalnp-proofs-fork/': The requested URL returned error: 403")
TEXISTS = " ! [rejected]        L-meta-7 -> L-meta-7 (stale info)\nerror: failed to push some refs"
TEX403 = " ! [rejected]        L-meta-403 -> L-meta-403 (stale info)\nerror: failed to push some refs"
TEX429 = " ! [rejected]        L-drill-rr1-429 -> L-drill-rr1-429 (stale info)\nerror: failed to push some refs"

# U1
plad = [S.push_refusal_wait(k) for k in (1, 2, 3, 4)]
d1 = tempfile.mkdtemp()
pk = [S.push_bucket_refusal(d1, "t", now=1000.0 + i)[0] for i in range(5)]
clad = [S.refusal_wait(k, {}, 0) for k in (1, 2, 3)]
d2 = tempfile.mkdtemp()
ck = [S.bucket_refusal(d2, {}, "t", now=1000.0 + i)[0] for i in range(4)]
case("U1-ladders", plad == [60.0, 120.0, 240.0, 240.0] and pk == [1, 2, 3, 4, 5] and not os.path.exists(os.path.join(d1, "giveup"))
     and S.refusals(d1) == 0 and clad == [60.0, 120.0, 240.0] and os.path.exists(os.path.join(d2, "giveup")),
     f"push waits {plad} (5 refusals, giveup {os.path.exists(os.path.join(d1, 'giveup'))}), create waits {clad} (4th = giveup)")

# U2
tab = [(T429, "refused"), (T403, "refused"), ("remote: error: Too Many Requests (429)", "refused"),
       ("remote: You have exceeded a secondary rate limit", "refused"), (TDEN, "denied"),
       ("error: The requested URL returned error: 403 Forbidden: access denied", "denied"),
       (TEXISTS, None), (TEX403, None), (TEX429, None), ("fatal: the remote end hung up; HTTP 500", None),
       ("remote: something else\nfatal: The requested URL returned error: 403", None), ("", None)]
bad = [(t[:40], S.push_refusal_kind(t)) for t, want in tab if S.push_refusal_kind(t) != want]
case("U2-texts", not bad, f"{len(tab)} texts, misread {bad}")

S.push_refusal_wait = lambda k: 0.6 * 2 ** (min(k, 3) - 1)
LOG = []
S.log = lambda *a: LOG.append(" ".join(map(str, a)))
LK = threading.Lock()


def reset():
    for f in os.listdir(GATE):
        os.remove(os.path.join(GATE, f))
    LOG.clear()
    os.environ["FILING_FIXTURE"] = GO


def scenario(answers, n=28, during_stall=None):
    """n workers push one unit each (staggered 30 ms); answers = {push number: stderr} (push numbers count every push
    call, retries included); "twice" in answers = the refused unit's retry is refused too. during_stall(): called once
    shortly after the first refusal. Returns pushes [(start, gid, rc)], results {gid: err}, creates [(t, wait)], state."""
    reset()
    st = {"n": 0, "refused": [], "twice": answers.pop("twice", None), "hook": during_stall}
    pushes = []

    def fake_run(cmd, timeout=300, env=None, cwd=None):
        if "push" in cmd:
            gid = cmd[-1].split("refs/heads/")[-1]
            with LK:
                st["n"] += 1
                k, t, rc, err = st["n"], time.time(), 0, ""
                if k in answers:
                    rc, err = 128, answers[k]
                    if S.push_refused(err):
                        st["refused"].append(gid)
                elif st["twice"] and gid in st["refused"]:
                    rc, err = 128, st["twice"]
                pushes.append((t, gid, rc))
            time.sleep(0.03)
            if rc and st["hook"] and S.push_refused(err):
                h, st["hook"] = st["hook"], None
                threading.Timer(0.1, h).start()
            return subprocess.CompletedProcess(cmd, rc, "", err)
        return subprocess.CompletedProcess(cmd, 0, "", "")

    S.run = fake_run
    out, creates = {}, []

    def creator():
        t_end = time.time() + 5
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


def stall_windows(pushes):
    """[(start, end)] of every stall from the rate-refused pushes (the stall starts when the refused push returns)"""
    ws, k = [], 0
    for t, g, rc in pushes:
        if rc:
            k += 1
            ws.append((t + 0.03, t + 0.03 + 0.6 * 2 ** (min(k, 3) - 1)))
    return ws


def inside(t, ws, m=0.05):
    return any(a + m < t < b - m for a, b in ws)


def judge(name, text):
    pushes, out, creates, st = scenario({5: text})
    ws = stall_windows(pushes)
    during = [p for p in pushes if inside(p[0], ws)]
    after = [p for p in pushes if ws and p[0] >= ws[0][1] - 0.05]
    held = [c for c in creates if inside(c[0], ws)]
    ok_units = [g for g, e in out.items() if e is None]
    ref = st["refused"][0] if st["refused"] else None
    case(name, len(ws) == 1 and S.push_refusals(GATE) == 1 and S.refusals(GATE) == 0 and not during and after
         and after[0][1] == ref and len([p for p in pushes if p[1] == ref]) == 2 and len(ok_units) == 28
         and held and all(c[1] > 0 for c in held) and not os.path.exists(os.path.join(GATE, "pushfirst"))
         and any(l.startswith("PUSH-REFUSED") for l in LOG),
         f"stalls {len(ws)}, push/create counters {S.push_refusals(GATE)}/{S.refusals(GATE)}, pushes during it {len(during)}, "
         f"creates held {len(held)} checks, first after it {after[0][1] if after else None} (refused {ref}), "
         f"units pushed {len(ok_units)}/28")


judge("P1-429-burst", T429)
judge("P2-bare-403-burst", T403)

# P3
ok3 = []
for g, t in (("L-meta-7", TEXISTS), ("L-meta-403", TEX403)):
    reset()
    S.run = lambda cmd, timeout=300, env=None, cwd=None, t=t: subprocess.CompletedProcess(cmd, 1 if "push" in cmd else 0, "",
                                                                                         t if "push" in cmd else "")
    e = S.push_branch("c" * 40, g)
    ok3.append(bool(e) and "rejected" in e and S.push_refusals(GATE) == 0 and S.refusals(GATE) == 0
               and not os.path.exists(os.path.join(GATE, "stall")))
case("P3-ref-exists", all(ok3), f"L-meta-7 / L-meta-403: no refusal, no stall = {ok3}")

# P4
pushes, out, creates, st = scenario({5: T429, "twice": T429})
ref = st["refused"][0]
others = [g for g, x in out.items() if g != ref and x is None]
case("P4-refused-twice", (out.get(ref) or "").startswith("PUSH-REFUSED twice") and S.push_refusals(GATE) == 2
     and S.refusals(GATE) == 0 and len(others) == 27 and not os.path.exists(os.path.join(GATE, "pushfirst")),
     f"unit {ref} -> {(out.get(ref) or '')[:26]!r}, push refusals {S.push_refusals(GATE)}, other units pushed {len(others)}/27")

# P5 R1: four push refusals, no giveup
pushes, out, creates, st = scenario({3: T429, 9: T403, 16: T429, 23: T403})
ws = stall_windows(pushes)
during = [p for p in pushes if inside(p[0], ws)]
try:                                               # after the last stall, with no create in the log yet: creates go
    time.sleep(max(0.0, float(open(os.path.join(GATE, "stall")).read()) - time.time()) + 0.1)
    os.remove(os.path.join(GATE, "creates.log"))
except OSError:
    pass
late = [(time.time(), S.bucket_wait(GATE, time.time()))]
n_ok = len([e for e in out.values() if e is None])
case("P5-R1-no-giveup", S.push_refusals(GATE) == 4 and S.refusals(GATE) == 0 and not os.path.exists(os.path.join(GATE, "giveup"))
     and S.gate_rate(GATE) == S.PR_RATE_FLOOR and not during and n_ok == 28
     and all(c[1] != float("inf") for c in creates) and any(c[1] == 0 for c in late),
     f"push refusals {S.push_refusals(GATE)}, create refusals {S.refusals(GATE)}, giveup {os.path.exists(os.path.join(GATE, 'giveup'))}, "
     f"rate {S.gate_rate(GATE)}/min, pushes during the {len(ws)} stalls {len(during)}, units pushed {n_ok}/28, "
     f"a create possible after them {any(c[1] == 0 for c in late)}")

# P6 R3
reset()
calls = []
S.run = lambda cmd, timeout=300, env=None, cwd=None: (calls.append(1) if "push" in cmd else None) or subprocess.CompletedProcess(cmd, 0, "", "")
open(os.path.join(GATE, "giveup"), "w").write("1 t")
e1 = S.push_branch("c" * 40, "L-meta-1")
os.remove(os.path.join(GATE, "giveup"))
os.environ["FILING_FIXTURE"] = STOP
e2 = S.push_branch("c" * 40, "L-meta-2")
n_before = len(calls)
pushes, out, creates, st = scenario({5: T429}, during_stall=lambda: os.environ.__setitem__("FILING_FIXTURE", STOP))
ws = stall_windows(pushes)
after = [p for p in pushes if ws and p[0] > ws[0][0] + 0.1]
halted = [g for g, x in out.items() if (x or "").startswith("halted: ")]
case("P6-R3-giveup-halt", (e1 or "").startswith("stall-giveup") and (e2 or "").startswith("halted: ") and n_before == 0
     and not after and st["refused"] and st["refused"][0] in halted and len(halted) + len([x for x in out.values() if x is None]) == 28,
     f"giveup -> {(e1 or '')[:20]!r}, halt -> {(e2 or '')[:20]!r}, pushes made {n_before}; halt set during the stall: pushes "
     f"after it {len(after)}, halted units {len(halted)} (refused unit among them {bool(st['refused']) and st['refused'][0] in halted})")

# P7 R5
pushes, out, creates, st = scenario({5: TDEN})
den = [g for g, x in out.items() if (x or "").startswith("PUSH-DENIED")]
ok7 = [g for g, x in out.items() if x is None]
case("P7-R5-denied", len(den) == 1 and len([p for p in pushes if p[1] == den[0]]) == 1 and len(ok7) == 27
     and S.push_refusals(GATE) == 0 and S.refusals(GATE) == 0 and not os.path.exists(os.path.join(GATE, "stall"))
     and os.path.exists(os.path.join(GATE, "pushdenied")) and any(l.startswith("PUSH-DENIED") for l in LOG),
     f"denied units {den}, their pushes {len([p for p in pushes if den and p[1] == den[0]])}, others pushed {len(ok7)}/27, "
     f"stall {os.path.exists(os.path.join(GATE, 'stall'))}, alert file {os.path.exists(os.path.join(GATE, 'pushdenied'))}")

bad = [n for n, ok in res if not ok]
print(f"PUSH SELFTEST OK {len(res)}" if not bad else f"PUSH SELFTEST FAIL {bad}")
sys.exit(1 if bad else 0)
