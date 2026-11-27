# claimtest.py [dir of submit.py]: the live claim list (lane leases L1, Lead 10:17/10:33 UTC 27 Nov, red team N1-N4).
# Real git: a local bare "toolkit" with refs claimallow/<n>, read through drain.py's own reader (drain.claimlist_reader,
# TK pointed at the local repo) into W/claim-allow.json, and submit.py's claim_list() reading that copy. No network.
#   K1  no ref at all = no list, ok, and the reader fetches nothing (one ls-remote per pass)
#   K2  "CLAIM-ALLOW v1 <ids>" = those ids (comma or whitespace, header line or below); fetched once per new ref
#   K3  the highest number wins (a lower number pushed later is ignored)
#   K4  "CLAIM-ALLOW v1 off" = off
#   K5  odd (other header, a non-id token, no ids, too many, a trailer line) = off
#   K6  N1: toolkit unreadable after a good list = ok false, the LAST GOOD ids kept; submit sees (ids, False)
#   K7  N1: the reader stops (copy over 30 s old) = submit sees (last ids, False)
#   K8  TTL: a list whose commit time is over 2 h old = off; commit time over 5 min in the future = off
#   K9  N4: deleting the newest ref = off (below the highest number seen), also when an older list remains; a new ref
#       above every number seen turns it on again
#   K10 N3: a ref with a far-future NUMBER is beaten by the writer's next "off" (haltrule.next_ref_epoch numbering)
#   K11 N2: submit.claim_list() makes no git call at all; no copy (no reader) = no list
# Prints one line per case and "CLAIMLIST SELFTEST OK <n>" or "CLAIMLIST SELFTEST FAIL <cases>". Exit 0 iff OK.
import json, os, subprocess, sys, tempfile, time

W = tempfile.mkdtemp()
os.environ.update(ID="L-meta-1", MOD="L_meta_1", PROOF="/dev/null", TREE="/tmp", W=W, RIVAL_SNAP_DIR=W, PR_TOKEN="x",
                  PR_GATE_DIR=W, GITHUB_REPOSITORY="drill/drill", SRC=W)
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import claimallow as C
import haltrule
import submit as S
import drain as D

RES, FAILS = [], []


def case(name, ok, info=""):
    RES.append(name)
    print(("ok   " if ok else "FAIL ") + name + " " + str(info)[:120])
    if not ok:
        FAILS.append(name)


def git(*a, date=None):
    env = dict(os.environ, GIT_AUTHOR_NAME="drill", GIT_AUTHOR_EMAIL="drill@example.invalid",
               GIT_COMMITTER_NAME="drill", GIT_COMMITTER_EMAIL="drill@example.invalid")
    if date is not None:
        env.update(GIT_AUTHOR_DATE="@%d +0000" % date, GIT_COMMITTER_DATE="@%d +0000" % date)
    return subprocess.run(["git", *a], capture_output=True, text=True, env=env, check=True).stdout.strip()


TK = tempfile.mkdtemp()
git("init", "-q", "--bare", TK)
WT = tempfile.mkdtemp()
git("init", "-q", WT)
D.TK = TK
CALLS = {"ls-remote": 0, "fetch": 0}
_sh = D.sh


def counting_sh(*a, **k):
    for x in CALLS:
        if x in a:
            CALLS[x] += 1
    return _sh(*a, **k)


D.sh = counting_sh
RD = D.claimlist_reader()
N0 = 1_000_000          # ref numbers are plain numbers (order only); commit times are real


def put(n, msg, date=None):
    git("-C", WT, "commit", "-q", "--allow-empty", "-m", msg, date=int(time.time()) if date is None else date)
    git("-C", WT, "push", "-q", TK, f"HEAD:refs/heads/claimallow/{N0 + n}")


def rm(n):
    git("-C", TK, "update-ref", "-d", f"refs/heads/claimallow/{N0 + n}")


def calls():
    c = dict(CALLS)
    for x in CALLS:
        CALLS[x] = 0
    return c


def step():
    c = RD.refresh()
    ids, ok, why = S.claim_list()
    return c, ids, ok, why


calls()
c, ids, ok, why = step()
k = calls()
case("K1-no-ref-no-list", ids == set() and ok and "no claimallow ref" in why and k == {"ls-remote": 1, "fetch": 0}, (why, k))
put(10, "CLAIM-ALLOW v1 L-meta-1,L-meta-2\nL-tl6c-17 L-meta-3")
c, ids, ok, why = step()
k1 = calls()
step()
k2 = calls()
case("K2-list", ids == {"L-meta-1", "L-meta-2", "L-tl6c-17", "L-meta-3"} and ok and k1["fetch"] == 1 and k2 == {"ls-remote": 1, "fetch": 0},
     (sorted(ids), k1, k2))
put(5, "CLAIM-ALLOW v1 L-meta-99")             # lower number pushed later: ignored
put(20, "CLAIM-ALLOW v1 L-meta-5")
c, ids, ok, why = step()
case("K3-highest-number-wins", ids == {"L-meta-5"} and ok, sorted(ids))
put(30, "CLAIM-ALLOW v1 off")
c, ids, ok, why = step()
case("K4-off", ids == set() and ok and "off" in why, why)
for i, (k, msg) in enumerate((("header", "CLAIM-ALLOW v2 L-meta-1"), ("token", "CLAIM-ALLOW v1 L-meta-1, rm -rf"),
                              ("empty", "CLAIM-ALLOW v1"),
                              ("toomany", "CLAIM-ALLOW v1 " + ",".join("L-meta-%d" % i for i in range(C.MAX_IDS + 1))),
                              ("trailer", "CLAIM-ALLOW v1 L-meta-1\n\nCo-Authored-By: x <x@example.invalid>"))):
    put(40 + i, msg)
    c, ids, ok, why = step()
    case("K5-odd-" + k, ids == set() and ok, why)
put(50, "CLAIM-ALLOW v1 L-meta-7")
c, ids, ok, why = step()
case("K5b-good-again", ids == {"L-meta-7"} and ok, why)
# K6 unreadable toolkit: last good kept, not confirmed
D.TK = os.path.join(TK, "missing")
c, ids, ok, why = step()
case("K6-unreadable-keeps-last-good", ids == {"L-meta-7"} and not ok, (sorted(ids), ok, why))
D.TK = TK
c, ids, ok, why = step()
case("K6b-readable-again", ids == {"L-meta-7"} and ok, why)
# K7 reader dead: the copy goes stale
f = os.path.join(W, C.FILE)
d = json.load(open(f)); d["t"] -= C.STALE_S + 1; json.dump(d, open(f, "w"))
ids, ok, why = S.claim_list()
case("K7-stale-copy-not-confirmed", ids == {"L-meta-7"} and not ok, why)
# K8 TTL on the commit time (liveness only)
put(60, "CLAIM-ALLOW v1 L-meta-8", date=int(time.time()) - C.TTL_S - 60)
c, ids, ok, why = step()
case("K8-older-than-2h-off", ids == set() and ok and "old" in why, why)
put(61, "CLAIM-ALLOW v1 L-meta-8", date=int(time.time()) + 3600)
c, ids, ok, why = step()
case("K8b-future-commit-time-off", ids == set() and ok and "future" in why, why)
# K9 N4: delete the newest ref; an older list (60/61 are off, 50 is a good list) must not come back
put(70, "CLAIM-ALLOW v1 L-meta-9")
c, ids, ok, why = step()
ok_a = ids == {"L-meta-9"}
for n in (70, 61, 60):
    rm(n)
c, ids, ok, why = step()
case("K9-delete-newest-off", ok_a and ids == set() and ok and "deleted" in why, why)
put(71, "CLAIM-ALLOW v1 L-meta-10")
c, ids, ok, why = step()
case("K9b-new-ref-above-turns-on", ids == {"L-meta-10"} and ok, why)
# K10 N3: a far-future number; the writer numbers the next ref with next_ref_epoch over the refs it read
put(9_000_000_000 - N0, "CLAIM-ALLOW v1 L-meta-11")
c, ids, ok, why = step()
ok_a = ids == {"L-meta-11"}
ls = git("ls-remote", TK, C.PREFIX + "*")
nums = [int(l.rsplit("/", 1)[1]) for l in ls.splitlines()]
nxt = haltrule.next_ref_epoch(time.time(), nums, [])
git("-C", WT, "commit", "-q", "--allow-empty", "-m", "CLAIM-ALLOW v1 off")
git("-C", WT, "push", "-q", TK, f"HEAD:refs/heads/claimallow/{nxt}")
c, ids, ok, why = step()
case("K10-future-number-beaten-by-next-off", ok_a and nxt == 9_000_000_001 and ids == set() and ok and "off" in why, (nxt, why))
# K11 N2: claim_list() makes no git call; no copy = no list
calls()
for _ in range(50):
    S.claim_list()
k = calls()
os.remove(f)
ids, ok, why = S.claim_list()
case("K11-unit-read-is-local", k == {"ls-remote": 0, "fetch": 0} and ids == set() and ok and "no claim list copy" in why, (k, why))
pure = C.newest("%s\trefs/heads/claimallow/30\n%s\trefs/heads/claimallow/200\n%s\trefs/heads/claim/allow-900\n%s\trefs/heads/claimallow/7\n"
                % ("a" * 40, "b" * 40, "d" * 40, "c" * 40))
case("K12-newest-pure-ignores-other-prefixes", pure == ("b" * 40, 200), pure)

print(("CLAIMLIST SELFTEST OK %d" % len(RES)) if not FAILS else ("CLAIMLIST SELFTEST FAIL " + " ".join(FAILS)))
sys.stdout.flush()
os._exit(0 if not FAILS else 1)          # skip drain.py's atexit state saver (no drain ran here)
