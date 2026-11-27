# claimtest.py [dir of submit.py]: the live claim list (lane leases L1, Lead 10:17 UTC 27 Nov). Real git, a local bare
# "toolkit" with refs claim/allow-<epoch>; no network.
#   K1 no ref at all = empty (the code default: no claim through the list)
#   K2 "CLAIM-ALLOW v1 L-a-1,L-b-2" = those ids (comma or whitespace, header line or the lines below)
#   K3 newest epoch wins (an older ref with other ids is ignored), whatever the ref order in ls-remote
#   K4 "CLAIM-ALLOW v1 off" newest = empty (off)
#   K5 odd: other header, a token that is not a unit id, header with no ids, too many ids = empty (fail closed)
#   K6 unreadable toolkit (remote missing) = empty
#   K7 shared copy: a second call within CLAIM_ALLOW_MAX_AGE_S makes no git read; after it, one fresh read
# Prints one line per case and "CLAIMLIST SELFTEST OK <n>" or "CLAIMLIST SELFTEST FAIL <cases>". Exit 0 iff OK.
import os, subprocess, sys, tempfile

SNAP = tempfile.mkdtemp()
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(),
                  RIVAL_SNAP_DIR=SNAP, PR_TOKEN="")
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S

RES, FAILS = [], []


def case(name, ok, info=""):
    RES.append(name)
    print(("ok   " if ok else "FAIL ") + name + " " + info)
    if not ok:
        FAILS.append(name)


def git(*a, cwd=None):
    env = dict(os.environ, GIT_AUTHOR_NAME="drill", GIT_AUTHOR_EMAIL="drill@example.invalid",
               GIT_COMMITTER_NAME="drill", GIT_COMMITTER_EMAIL="drill@example.invalid")
    return subprocess.run(["git", *a], cwd=cwd, capture_output=True, text=True, env=env, check=True).stdout.strip()


TK = tempfile.mkdtemp()
git("init", "-q", "--bare", TK)
WT = tempfile.mkdtemp()
git("init", "-q", WT)
LOCAL = tempfile.mkdtemp()
git("init", "-q", "--bare", LOCAL)
git("-C", LOCAL, "remote", "add", "origin", TK)


class DG:
    REPO = LOCAL


S.dg = lambda: DG()
READS = [0]
_run = S.run


def counting_run(a, **k):
    if "ls-remote" in a:
        READS[0] += 1
    return _run(a, **k)


S.run = counting_run


def put(epoch, msg):
    git("-C", WT, "commit", "-q", "--allow-empty", "-m", msg)
    git("-C", WT, "push", "-q", TK, f"HEAD:refs/heads/claim/allow-{epoch}")


def fresh():
    try:
        os.remove(os.path.join(SNAP, "claim-allow.json"))
    except FileNotFoundError:
        pass
    return S.claim_ids()


ids = fresh()
case("K1-no-ref-empty", ids == set(), str(ids))
put(1000, "CLAIM-ALLOW v1 L-meta-1,L-meta-2\nL-tl6c-17 L-meta-3")
ids = fresh()
case("K2-list", ids == {"L-meta-1", "L-meta-2", "L-tl6c-17", "L-meta-3"}, str(sorted(ids)))
put(900, "CLAIM-ALLOW v1 L-meta-99")          # older epoch pushed later: ignored
put(1100, "CLAIM-ALLOW v1 L-meta-5")
ids = fresh()
case("K3-newest-epoch-wins", ids == {"L-meta-5"}, str(sorted(ids)))
put(1200, "CLAIM-ALLOW v1 off")
ids = fresh()
case("K4-off", ids == set(), str(ids))
for k, msg in (("header", "CLAIM-ALLOW v2 L-meta-1"), ("token", "CLAIM-ALLOW v1 L-meta-1, rm -rf"),
               ("empty", "CLAIM-ALLOW v1"), ("toomany", "CLAIM-ALLOW v1 " + ",".join("L-meta-%d" % i for i in range(S.CLAIM_ALLOW_MAX_IDS + 1)))):
    put(1300 + len(RES), msg)
    ids = fresh()
    case("K5-odd-" + k, ids == set(), str(sorted(ids))[:60])
put(2000, "CLAIM-ALLOW v1 L-meta-7")
ids = fresh()
case("K5b-good-again", ids == {"L-meta-7"}, str(sorted(ids)))
pure = S.claim_allow_newest("%s\trefs/heads/claim/allow-30\n%s\trefs/heads/claim/allow-200\n%s\trefs/heads/claim/allow-7\n" % ("a" * 40, "b" * 40, "c" * 40))
case("K3b-newest-pure", pure == ("b" * 40, 200), str(pure))
# K7 shared copy
READS[0] = 0
fresh()
S.claim_ids(); S.claim_ids()
r1 = READS[0]
c = os.path.join(SNAP, "claim-allow.json")
import json
d = json.load(open(c)); d["t"] -= S.CLAIM_ALLOW_MAX_AGE_S + 1; json.dump(d, open(c, "w"))
ids = S.claim_ids()
case("K7-shared-copy", r1 == 1 and READS[0] == 2 and ids == {"L-meta-7"}, f"(reads {r1} then {READS[0]})")
# K6 unreadable toolkit
git("-C", LOCAL, "remote", "set-url", "origin", os.path.join(TK, "missing"))
ids = fresh()
case("K6-unreadable-empty", ids == set(), str(ids))

print(("CLAIMLIST SELFTEST OK %d" % len(RES)) if not FAILS else ("CLAIMLIST SELFTEST FAIL " + " ".join(FAILS)))
sys.exit(0 if not FAILS else 1)
