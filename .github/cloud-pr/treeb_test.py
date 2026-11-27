#!/usr/bin/env python3
"""treeb_test.py [dir of submit.py]: lane tree-b (W6, Lead 08:29). The unit commit's tree, built the way submit() does,
in a BLOBLESS shallow clone like the drain's upstream checkout (--depth 1 --filter=blob:none), here of a local
upstream with 15,000 files in lean/PEqualNP/Outside.
  SAME      5 units, 5 processes at once: tree sha = read-tree + update-index + write-tree in a full clone
  NOFETCH   no blob is fetched from the promisor while the trees are built (the cause of commit= 59.5 s: a plain
            write-tree checks, so fetches, every blob of each directory it rewrites)
  PRIVATE   one base index per base sha, never changed by a unit (each unit works on its own copy)
  FAST      write-tree p95 under 1 s
A submit.py without build_tree() is run as the old submit() did it (read-tree into its own index, write-tree).
Prints one line per case and "TREEB PASS <sha>" or "TREEB FAIL <sha>: <cases>". Exit 0 iff PASS."""
import json, os, subprocess, sys, tempfile, time

SRC = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
N_OUT, UNITS = 15000, [f"L-meta-9{70000 + i}" for i in range(5)]


def sh(*a, cwd=None, env=None):
    r = subprocess.run(list(a), cwd=cwd, env=env, capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f"setup failed: {' '.join(a[:4])}: {r.stderr[:200]}")
    return r.stdout.strip()


def upstream(d):
    """a bare upstream with one commit: 15,000 proof files plus a few others, allowing blob:none clones"""
    up, wk = os.path.join(d, "up.git"), os.path.join(d, "mk")
    sh("git", "init", "-q", "--bare", up)
    sh("git", "init", "-q", wk)
    env = dict(os.environ, GIT_INDEX_FILE=os.path.join(d, "mk.idx"))
    lines = []
    p = subprocess.run(["git", "-C", wk, "hash-object", "-w", "--stdin-paths"], input="".join(
        _w(os.path.join(d, "f%d.lean" % i), "theorem t%d : True := trivial\n" % i) + "\n" for i in range(N_OUT)),
        capture_output=True, text=True)
    for i, sha in enumerate(p.stdout.split()):
        lines.append(f"100644 {sha}\tlean/PEqualNP/Outside/L_meta_{100000 + i}.lean")
    rd = sh("git", "-C", wk, "hash-object", "-w", _w(os.path.join(d, "readme"), "upstream\n"))
    lines.append(f"100644 {rd}\tREADME.md")
    subprocess.run(["git", "-C", wk, "update-index", "--add", "--index-info"], input="\n".join(lines) + "\n",
                   env=env, capture_output=True, text=True, check=True)
    tree = sh("git", "-C", wk, "write-tree", env=env)
    c = sh("git", "-C", wk, "-c", "user.name=u", "-c", "user.email=u@x", "commit-tree", tree, "-m", "base")
    sh("git", "-C", wk, "push", "-q", up, f"{c}:refs/heads/main")
    sh("git", "-C", up, "config", "uploadpack.allowFilter", "true")
    return up, c


def _w(path, txt):
    with open(path, "w") as f:
        f.write(txt)
    return path


def blobless(up, dst):
    sh("git", "-c", "protocol.file.allow=always", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout",
       "--single-branch", "file://" + up, dst)
    sh("git", "-C", dst, "config", "protocol.file.allow", "always")
    return dst


def in_pack(repo):
    out = sh("git", "-C", repo, "count-objects", "-v")
    return sum(int(l.split()[1]) for l in out.splitlines() if l.startswith("in-pack:"))   # a lazy fetch lands as a pack


UNIT = r'''
import json, os, sys, time
sys.path.insert(0, os.environ["SUBMIT_DIR"])
import submit as S
base, gid = sys.argv[1], sys.argv[2]
rel = "lean/PEqualNP/Outside/%s.lean" % gid.replace("-", "_")
blob = S.git("hash-object", "-w", S.PROOF).stdout.strip()
t = time.time()
if hasattr(S, "build_tree"):
    tree, why = S.build_tree(base, blob, rel)
else:                                    # the old submit(): its own index, read-tree of the whole base, write-tree
    env = dict(os.environ, GIT_INDEX_FILE=os.path.join(S.W, "submit.idx"))
    S.git("read-tree", base, env=env)
    S.git("update-index", "--add", "--cacheinfo", "100644,%s,%s" % (blob, rel), env=env)
    t_w = time.time()
    tree = S.git("write-tree", env=env).stdout.strip()
    S.STG["cm_wt"] = round(time.time() - t_w, 3)
print(json.dumps({"tree": tree, "wt": S.STG.get("cm_wt"), "total": round(time.time() - t, 3)}))
'''


def main():
    sha = subprocess.run(["git", "-C", SRC, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    d = tempfile.mkdtemp(prefix="treeb-")
    up, base = upstream(d)
    full = os.path.join(d, "full")
    sh("git", "clone", "-q", "--no-checkout", up, full)
    part = blobless(up, os.path.join(d, "part"))
    snap = os.path.join(d, "snap"); os.makedirs(snap)
    want, procs = {}, []
    sh("git", "-C", part, "ls-tree", "-r", "-t", base)      # the trees, as a GitHub blobless clone has them already
    p0 = in_pack(part)
    for k, gid in enumerate(UNITS):
        proof = _w(os.path.join(d, f"{gid}.lean"), f"theorem {gid.replace('-', '_')} : True := trivial -- {k}\n")
        # expected: the classic build in a FULL clone (nothing to fetch there)
        env = dict(os.environ, GIT_INDEX_FILE=os.path.join(d, f"exp{k}.idx"))
        b = sh("git", "-C", full, "hash-object", "-w", proof)
        sh("git", "-C", full, "read-tree", base, env=env)
        sh("git", "-C", full, "update-index", "--add", "--cacheinfo",
           f"100644,{b},lean/PEqualNP/Outside/{gid.replace('-', '_')}.lean", env=env)
        want[gid] = sh("git", "-C", full, "write-tree", env=env)
        w = os.path.join(d, f"w{k}"); os.makedirs(w)
        uenv = dict(os.environ, SUBMIT_DIR=SRC, ID=gid, MOD=gid.replace("-", "_"), PROOF=proof, TREE=part, W=w,
                    RIVAL_SNAP_DIR=snap, GHCOND_DIR=tempfile.mkdtemp(), DRY="1")
        uenv.pop("FILING_FIXTURE", None)
        procs.append((gid, subprocess.Popen([sys.executable, "-c", UNIT, base, gid], env=uenv, cwd=d,
                                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)))
    idx_before = None
    got = {}
    for gid, p in procs:
        out, err = p.communicate(timeout=600)
        try:
            got[gid] = json.loads(out.strip().splitlines()[-1])
        except Exception:
            got[gid] = {"tree": "", "err": (err or out)[-200:]}
    fetched = in_pack(part) - p0
    idxs = [f for f in os.listdir(os.path.join(snap, "baseidx"))] if os.path.isdir(os.path.join(snap, "baseidx")) else []
    if idxs:
        idx_before = subprocess.run(["sha256sum", os.path.join(snap, "baseidx", base + ".idx")], capture_output=True, text=True).stdout
    res = {}
    bad = [g for g in UNITS if got[g].get("tree") != want[g]]
    res["SAME"] = (not bad, f"{5 - len(bad)}/5 trees equal the full-clone build" + (f"; {bad[0]}: {got[bad[0]]}" if bad else ""))
    res["NOFETCH"] = (fetched == 0, f"{fetched} objects fetched from the promisor while building")
    pri = [f for f in idxs if f.endswith(".idx")]
    if pri:
        # a unit run after the five must find the same base index, unchanged
        w = os.path.join(d, "w9"); os.makedirs(w)
        proof = _w(os.path.join(d, "L-meta-979999.lean"), "theorem late : True := trivial\n")
        uenv = dict(os.environ, SUBMIT_DIR=SRC, ID="L-meta-979999", MOD="L_meta_979999", PROOF=proof, TREE=part, W=w,
                    RIVAL_SNAP_DIR=snap, GHCOND_DIR=tempfile.mkdtemp(), DRY="1")
        subprocess.run([sys.executable, "-c", UNIT, base, "L-meta-979999"], env=uenv, cwd=d, capture_output=True, text=True)
        after = subprocess.run(["sha256sum", os.path.join(snap, "baseidx", base + ".idx")], capture_output=True, text=True).stdout
        res["PRIVATE"] = (len(pri) == 1 and after == idx_before, f"{len(pri)} base index for 1 base, unchanged by 6 units: {after == idx_before}")
    else:
        res["PRIVATE"] = (False, "no shared base index (every unit read the whole tree into its own index)")
    wts = sorted(float(got[g].get("wt") or 99) for g in UNITS)
    res["FAST"] = (wts[-1] < 1.0, "write-tree s: " + " ".join(f"{x:.3f}" for x in wts))
    fails = [k for k, (ok, _) in res.items() if not ok]
    for k, (ok, info) in res.items():
        print(("ok   " if ok else "FAIL ") + k + " | " + info)
    print(f"TREEB PASS {sha}" if not fails else f"TREEB FAIL {sha}: " + ", ".join(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
