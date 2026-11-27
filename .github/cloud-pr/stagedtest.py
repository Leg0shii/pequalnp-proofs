# stagedtest.py [dir of submit.py]: P2c staged heads (Lead 20:56 UTC 27 Nov), in-process, a local git upstream, GitHub faked.
# The "gate" commit is built here exactly as w12 lemmaready stage_head() builds it (read-tree, update-index, write-tree
# --missing-ok, commit-tree with fixed dates, Leg0shii). The opener's staged_check() must rebuild it bit for bit.
#   S1 valid head -> ""            S2 proof changed -> refused     S3 no Staged-Head line -> None (old paths)
#   S4 line names another head -> None                             S5 time off by one -> refused
#   S6 parent not an upstream base -> refused                      S7 file already on the parent -> refused
#   S8 submit(): no PR -> create from the staged head, no push     S9 open PR -> that PR   S10 closed PR -> I5, no create
#   S11 open_pr_for_branch: fresh taken list, valid staged head -> no API call
# Prints one line per case and "STAGED SELFTEST OK <n>" or "STAGED SELFTEST FAIL <cases>". Exit 0 iff OK.
import os, subprocess, sys, tempfile, time
T = tempfile.mkdtemp()
def g(*a, cwd=None, env=None, inp=None):
    r = subprocess.run(["git"] + list(a), cwd=cwd, env=env, input=inp, capture_output=True, text=True)
    if r.returncode: raise SystemExit("git %s: %s" % (a, r.stderr))
    return r.stdout.strip()
up = os.path.join(T, "up"); os.makedirs(os.path.join(up, "lean/PEqualNP/Outside")); os.makedirs(os.path.join(up, ".github"))
open(os.path.join(up, "lean/PEqualNP/Outside/A.lean"), "w").write("-- a\n")
open(os.path.join(up, ".github/x"), "w").write("x\n")
cE = dict(os.environ, GIT_AUTHOR_NAME="u", GIT_AUTHOR_EMAIL="u@x", GIT_COMMITTER_NAME="u", GIT_COMMITTER_EMAIL="u@x")
g("init", "-q", "-b", "main", up); g("add", "-A", cwd=up); g("commit", "-q", "-m", "p", cwd=up, env=cE)
P = g("rev-parse", "HEAD", cwd=up)
open(os.path.join(up, "lean/PEqualNP/Outside/L_meta_7.lean"), "w").write("-- other\n")
g("add", "-A", cwd=up); g("commit", "-q", "-m", "p3", cwd=up, env=cE); P3 = g("rev-parse", "HEAD", cwd=up)
g("reset", "-q", "--hard", P, cwd=up)
tree = os.path.join(T, "tree"); g("clone", "-q", up, tree); g("-C", tree, "fetch", "-q", "origin", P3)
proof = os.path.join(T, "proof.lean"); open(proof, "w").write("import PEqualNP.Defs\n\ntheorem t : True := trivial\n")
REL = "lean/PEqualNP/Outside/L_meta_7.lean"

def gate(parent, f, ts, nonce, gid="L-meta-7"):
    G = os.path.join(T, "gate.git")
    if not os.path.isdir(G): g("init", "-q", "--bare", G)
    env = dict(os.environ, GIT_INDEX_FILE=os.path.join(T, "hidx"), GIT_ALTERNATE_OBJECT_DIRECTORIES=os.path.join(up, ".git/objects"))
    b = g("-C", G, "hash-object", "-w", f)
    g("-C", G, "read-tree", parent, env=env)
    g("-C", G, "update-index", "--add", "--cacheinfo", "100644,%s,%s" % (b, REL), env=env)
    tr = g("-C", G, "write-tree", "--missing-ok", env=env)
    cenv = dict(env, GIT_AUTHOR_NAME="Leg0shii", GIT_COMMITTER_NAME="Leg0shii",
                GIT_AUTHOR_EMAIL="46093332+Leg0shii@users.noreply.github.com", GIT_COMMITTER_EMAIL="46093332+Leg0shii@users.noreply.github.com",
                GIT_AUTHOR_DATE="%d +0000" % ts, GIT_COMMITTER_DATE="%d +0000" % ts)
    msg = "%s\n\nGate-Staged: w12-%s\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n" % (gid, nonce)
    c = g("-C", G, "commit-tree", tr, "-p", parent, "-m", msg, env=cenv)
    os.unlink(os.path.join(T, "hidx"))
    return c, "Staged-Head: %s %s %d %s" % (c, parent, ts, nonce)

os.environ.update(ID="L-meta-7", MOD="L_meta_7", PROOF=proof, TREE=tree, W=tempfile.mkdtemp(), DRY="0", PR_TOKEN="",
                  GHCOND_DIR=tempfile.mkdtemp())
for k in ("RIVAL_SNAP_DIR", "PR_GATE_DIR", "FILING_FIXTURE"): os.environ.pop(k, None)
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S
assert S.REL == REL, S.REL
res = []
def case(name, got, want):
    ok = (got == want) if not isinstance(want, str) or want == "" else (isinstance(got, str) and want in got)
    res.append((name, ok)); print(("ok   " if ok else "FAIL ") + f"staged/{name} -> {got!r}")
def chk(head, line, proofc=None):
    S.STAGED.clear()
    os.environ["READY_MSG"] = "ready L-meta-7 (lemma)\n\nSight: 1.0\n\n" + line + "\n" if line else "ready L-meta-7\n"
    if proofc is not None:
        p2 = os.path.join(T, "p2.lean"); open(p2, "w").write(proofc); S.PROOF = p2
    else:
        S.PROOF = proof
    return S.staged_check("L-meta-7", head)
ts = int(time.time())
H, L = gate(P, proof, ts, "0123456789ab")
case("S1-valid", chk(H, L), "")
case("S2-proof-changed", chk(H, L, proofc="import PEqualNP.Defs\n-- changed\n"), "differs")
case("S3-no-line", chk(H, None), None)
case("S4-other-head", chk("f" * 40, L), None)
case("S5-time-off", chk(H, L.replace(" %d " % ts, " %d " % (ts + 1))), "differs")
real_run = S.run
S.run = lambda cmd, **k: (subprocess.CompletedProcess(cmd, 0, "", "") if "ls-remote" in cmd else real_run(cmd, **k))
H6, L6 = gate(P3, proof, ts, "0123456789ac")   # P3 is not the unit's base and has no upbase ref (faked empty)
case("S6-parent-not-upstream", chk(H6, L6), "not an upstream base")
S.run = lambda cmd, **k: (subprocess.CompletedProcess(cmd, 0, P3 + "\trefs/heads/upbase/" + P3[:8] + "\n", "") if "ls-remote" in cmd else real_run(cmd, **k))
case("S7-file-on-parent", chk(H6, L6), "file already on the staged parent")
S.run = real_run
# S8-S10: submit() end to end with the GitHub calls faked
calls = {"gh": [], "create": 0}
S.fork_head = lambda gid: H
S.create_pr = lambda gid, lease: (calls.__setitem__("create", calls["create"] + 1), ("https://github.com/x/pull/1", "created"))[1]
S.push_branch = lambda c, gid: (_ for _ in ()).throw(AssertionError("no push in the staged path"))
def fake_gh(out):
    def f(args, write=False, timeout=120):
        calls["gh"].append(args); return subprocess.CompletedProcess(args, 0, out, "")
    return f
for name, out, want, wc in (("S8-no-pr-create", "", "https://github.com/x/pull/1", 1),
                            ("S9-open-pr", "open https://github.com/up/pull/9\n", "https://github.com/up/pull/9", 0),
                            ("S10-closed-pr-I5", "closed https://github.com/up/pull/8\n", None, 0)):
    calls.update(gh=[], create=0); S.gh = fake_gh(out); chk(H, L); S.STAGED.clear()
    url, why = S.submit("L-meta-7", None)
    good = url == want and calls["create"] == wc and len(calls["gh"]) == 1 and (want or "I5" in why)
    res.append((name, good)); print(("ok   " if good else "FAIL ") + f"staged/{name} -> {url} {why[:70]} gh={len(calls['gh'])} create={calls['create']}")
calls.update(gh=[]); S.gh = fake_gh(""); S.taken_list = lambda: {}
os.environ["READY_MSG"] = "ready\n\n" + L + "\n"; S.STAGED.clear()
r = S.open_pr_for_branch("L-meta-7")
case("S11-no-api-call", (r, len(calls["gh"])), (None, 0))
bad = [n for n, ok in res if not ok]
print(f"STAGED SELFTEST OK {len(res)}" if not bad else "STAGED SELFTEST FAIL " + " ".join(bad))
sys.exit(1 if bad else 0)
