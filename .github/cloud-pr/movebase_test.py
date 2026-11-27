#!/usr/bin/env python3
"""movebase_test.py (lane movingmain, W7): drain.py's shared upstream base under a moving main, locally.
A local bare depth-1 clone of upstream (UPSTREAM arg: a repo or URL, BRANCH) moves every MOVE_S (movemain.py);
N units (threads, as drain workers) take upstream_tree() copies over DURATION s. Pass if: 0 failed, 1 clone, the
refresher fetched and moved, every copy is at a sha main had at most BASE_MAX_S before the copy, and a stuck refresher
(base older than BASE_MAX_S) is refreshed inline, and with the upstream gone and the base too old: fail closed.
  python3 movebase_test.py [UPSTREAM [BRANCH]] (default: the current directory's repo, its HEAD) -> "MOVEBASE PASS" / "MOVEBASE FAIL: <why>" """
import os, subprocess, sys, tempfile, threading, time

here = os.path.dirname(os.path.abspath(__file__))
src = sys.argv[1] if len(sys.argv) > 1 else "."                          # infra 10:27: no argument = this checkout
br = sys.argv[2] if len(sys.argv) > 2 else ""                              # no BRANCH: the source's HEAD (CI checkout)
d = tempfile.mkdtemp(prefix="movebase-")
up = os.path.join(d, "up.git")
url = src if "://" in src else "file://" + os.path.abspath(src)
subprocess.run(["git", "clone", "-q", "--bare", "--depth", "1", "--single-branch"] + (["--branch", br] if br else []) + [url, up],
               check=True)
head = subprocess.run(["git", "-C", up, "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
subprocess.run(["git", "-C", up, "update-ref", "refs/heads/main", head], check=True)
subprocess.run(["git", "-C", up, "symbolic-ref", "HEAD", "refs/heads/main"], check=True)
for k, v in (("uploadpack.allowFilter", "true"), ("uploadpack.allowAnySHA1InWant", "true")):
    subprocess.run(["git", "-C", up, "config", k, v], check=True)
MOVE_S, N, DUR, ADOPT_S = 1.0, 30, 20.0, 5.0
os.environ.update(SRC=d, W=os.path.join(d, "w"), DRAIN_UPSTREAM="file://" + up, DRAIN_BASE_FETCH_S="0.5", DRAIN_BASE_MAX_S="60",
                  DRAIN_BASE_ADOPT_S=str(ADOPT_S))
os.makedirs(os.environ["W"])
sys.path.insert(0, here)
sys.argv = ["drain.py"]
import drain as D
D.log = lambda *a: print("  drain:", *a, flush=True)
mv = subprocess.Popen([sys.executable, os.path.join(here, "movemain.py"), up, str(MOVE_S)], stdout=subprocess.PIPE, text=True)
moves = {}                                   # sha -> epoch it became main
def rd():
    for l in mv.stdout:
        p = l.split()
        if len(p) == 4 and p[0] == "MOVE":
            moves[p[2]] = float(p[3])
threading.Thread(target=rd, daemon=True).start()
moves[subprocess.run(["git", "-C", up, "rev-parse", "main"], capture_output=True, text=True).stdout.strip()[:12]] = time.time()
out, bad = [], []
def unit(i):
    time.sleep(i * DUR / N)
    t = os.path.join(d, f"u{i}")
    why = D.upstream_tree(t, [])
    sha = subprocess.run(["git", "-C", t, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip() if not why else ""
    out.append((i, why, sha[:12], time.time(), os.path.isfile(os.path.join(t, ".github", "movetest.txt")) if not why else None))
ths = [threading.Thread(target=unit, args=(i,)) for i in range(N)]
[x.start() for x in ths]; [x.join(120) for x in ths]
mv.terminate()
fails = [o for o in out if o[1]]
if fails or len(out) != N:
    bad.append(f"{len(fails)} failed of {len(out)}: {fails[:2]}")
if D._BASE["clones"] != 1:
    bad.append(f"clones {D._BASE['clones']}")
if D._BASE["seen"] < 10 or D._BASE["fetches"] < 10:
    bad.append(f"refresher fetches {D._BASE['fetches']} main moves seen {D._BASE['seen']}")
if not 2 <= D._BASE["moves"] <= DUR / ADOPT_S + 2:      # Lead 09:59: a new base for the copies at most every ADOPT_S
    bad.append(f"bases adopted {D._BASE['moves']} in {DUR:.0f} s (adopt every {ADOPT_S:.0f} s at most)")

# age of each copy: the copied sha was main at some time; the NEXT move after it is when it stopped being main
order = sorted(moves.items(), key=lambda kv: kv[1])
def superseded(sha):
    for k, (s, t) in enumerate(order):
        if s == sha:
            return order[k + 1][1] if k + 1 < len(order) else None
    return "unknown"
lags = []
for i, why, sha, t, mt in out:
    if not why:
        sup = superseded(sha)
        if sup == "unknown":
            bad.append(f"unit {i} copied {sha}, never main"); continue
        lags.append(0.0 if sup is None or sup > t else t - sup)
nbj = __import__("json").load(open(os.path.join(os.environ["W"], "upbase.json")))
if nbj["sha"][:12] not in [x for x, _ in order[-3:]]:     # the path check reads the NEWEST sha, not the adopted one
    bad.append(f"upbase.json newest {nbj['sha'][:12]} is not among the last 3 moves of main")
if lags and max(lags) > ADOPT_S + 2:
    bad.append(f"a copy {max(lags):.1f} s behind main (adopt {ADOPT_S:.0f} s + fetch)")
print(f"units {len(out)}, failed {len(fails)}, clones {D._BASE['clones']}, copies redone {D._BASE.get('copy_retry', 0)}, fetches {D._BASE['fetches']}, moves seen "
      f"{D._BASE['seen']} of {len(moves) - 1}, bases adopted {D._BASE['moves']}, copy lag behind main p50 {sorted(lags)[len(lags) // 2]:.2f} s max {max(lags):.2f} s")
# stuck refresher: base 61 s old -> one inline fetch, unit gets the newest
D.BASE_FETCH_S = D.BASE_IDLE_S = 3600; time.sleep(1.5)        # the refresher thread now sleeps for an hour (stuck)
D._BASE["t"] -= 61; n0 = D._BASE["fetches"]
why = D.upstream_tree(os.path.join(d, "stuck"), [])
if why or D._BASE["fetches"] != n0 + 1:
    bad.append(f"stuck refresher: {why!r}, inline fetches {D._BASE['fetches'] - n0}")
# upstream gone and base too old: fail closed
subprocess.run(["git", "-C", D._BASE["dir"], "remote", "set-url", "origin", "file:///nonexistent-movebase"])
D._BASE["t"] -= 61
why = D.upstream_tree(os.path.join(d, "gone"), [])
if not why or "fail closed" not in why:
    bad.append(f"upstream gone + old base gave a tree: {why!r}")
else:
    print("fail closed:", why)
# the path check submit.py makes on the newest base (W/upbase.json): trees only, works with the remote cut
import json
nb = json.load(open(os.path.join(os.environ["W"], "upbase.json")))
names = subprocess.run(["git", "-C", nb["dir"], "ls-tree", "--name-only", nb["sha"], "lean/PEqualNP/Outside/"],
                       capture_output=True, text=True).stdout.split()
mvf = sorted(x for x in names if "/L_move_" in x)
hit = subprocess.run(["git", "-C", nb["dir"], "ls-tree", "--name-only", nb["sha"], "--", mvf[-1]], capture_output=True, text=True) if mvf else None
miss = subprocess.run(["git", "-C", nb["dir"], "ls-tree", "--name-only", nb["sha"], "--", "lean/PEqualNP/Outside/L_meta_999999.lean"],
                      capture_output=True, text=True)
if not (hit and hit.returncode == 0 and hit.stdout.strip() == mvf[-1] and miss.returncode == 0 and not miss.stdout.strip()):
    bad.append(f"newest-base path check: hit {hit and hit.stdout.strip()!r} miss {miss.stdout.strip()!r} {miss.stderr[:80]!r}")
else:
    print(f"newest-base path check: {mvf[-1]} found on {nb['sha'][:12]}, an absent path not found (remote cut)")
subprocess.run(["rm", "-rf", d])
print("MOVEBASE PASS" if not bad else "MOVEBASE FAIL: " + "; ".join(bad), flush=True)
os._exit(1 if bad else 0)          # no drain.py atexit lines after the verdict (mintdrill reads the last line)
