#!/usr/bin/env python3
"""treeprime_test (W7, 27 Nov, infra/Lead 10:58): treebuild.tree_from_prime (the drain primes the trees along
lean/PEqualNP/Outside once per adopted base; units write their trees in-process) gives the SAME tree sha as
tree_with_file (mktree) and the old index path, in a blobless depth-1 clone like the drain's base, including git's
order edge cases (a name that is a prefix of another, a directory sorting as name + '/', a replaced file, the new
entry first and last), and refuses what it must (another base, another directory, a directory where a file goes, a
truncated prime file). Prints the in-process time against tree_with_file. Exit 0 and TREEPRIME PASS when all hold."""
import os, subprocess, sys, tempfile, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import treebuild as T

N = int(os.environ.get("TREEPRIME_N", "20000"))
fails = []


def sh(*a, cwd=None, inp=None):
    r = subprocess.run(list(a), cwd=cwd, input=inp, capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(" ".join(a[:3]) + ": " + r.stderr[-300:])
    return r.stdout.strip()


def check(name, ok, info=""):
    print(("ok   " if ok else "FAIL ") + name + (" (" + info + ")" if info else ""), flush=True)
    if not ok:
        fails.append(name)


tmp = tempfile.mkdtemp(prefix="treeprime-")
src = os.path.join(tmp, "src"); os.makedirs(os.path.join(src, "lean", "PEqualNP", "Outside", "L_meta_dir"))
sh("git", "init", "-q", "-b", "main", src)
o = os.path.join(src, "lean", "PEqualNP", "Outside")
for i in range(N):
    open(os.path.join(o, f"L_meta_{i}.lean"), "w").write(f"-- {i}\n")
open(os.path.join(o, "L_meta_dir", "x"), "w").write("a dir named like a file\n")   # never happens upstream; order edge
for n in ("A.lean", "L_meta_1", "L_meta_1.lean-", "L_meta_1-", "zz.lean"):
    open(os.path.join(o, n), "w").write(n)
os.makedirs(os.path.join(src, "lean", "PEqualNP", "Inside")); open(os.path.join(src, "lean", "PEqualNP", "Inside", "a"), "w").write("i")
os.makedirs(os.path.join(src, ".github")); open(os.path.join(src, ".github", "movetest.txt"), "w").write("0")
os.chmod(os.path.join(o, "zz.lean"), 0o755)
sh("git", "add", "-A", cwd=src)
sh("git", "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "init", cwd=src)
up = os.path.join(tmp, "up.git")
sh("git", "clone", "-q", "--bare", "--depth", "1", "file://" + src, up)
sh("git", "-C", up, "config", "uploadpack.allowFilter", "true")
base_dir = os.path.join(tmp, "base")
sh("git", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout", "--single-branch", "--branch", "main", "file://" + up, base_dir)
base = sh("git", "-C", base_dir, "rev-parse", "HEAD")
t = time.time(); data = T.prime(base_dir, base); t_prime = time.time() - t
pf = os.path.join(tmp, "prime.bin"); T.write_prime(pf, data)
pd = T.load_prime(pf, base)
check("prime: 4 levels, %d bytes" % len(data), len(pd[1]) == 4, "%.3f s" % t_prime)

names = ["L_meta_new.lean", "A.lean", "0first.lean", "zzz_last.lean", "L_meta_1.lean", "L_meta_10.lean0", "L_meta_dir.lean", "L_meta_dir0", "L_meta_di",
         "L_meta_1-.x"]
for nm in names:
    rel = "lean/PEqualNP/Outside/" + nm
    cp = os.path.join(tmp, "cp-" + nm); sh("cp", "-a", base_dir, cp)
    blob = sh("git", "-C", cp, "hash-object", "-w", "--stdin", inp="proof " + nm)
    t = time.time(); a = T.tree_from_prime(cp, pd, rel, blob); ta = time.time() - t
    t = time.time(); b = T.tree_with_file(cp, base, rel, blob); tb = time.time() - t
    c = T.tree_by_index(cp, base, rel, blob, os.path.join(tmp, "idx-" + nm))
    ch = sh("git", "-C", cp, "diff-tree", "--name-only", "-r", base, a).split()
    fsck = subprocess.run(["git", "-C", cp, "cat-file", "-p", a], capture_output=True).returncode
    check("same tree sha for " + nm, a == b == c and ch == [rel] and fsck == 0,
          "prime %.3f s, mktree %.3f s%s" % (ta, tb, "" if a == b == c else f" {a[:8]} {b[:8]} {c[:8]}"))
    sh("rm", "-rf", cp)

cp = os.path.join(tmp, "cp-refuse"); sh("cp", "-a", base_dir, cp)
blob = sh("git", "-C", cp, "hash-object", "-w", "--stdin", inp="x")


def raises(f):
    try:
        f(); return False
    except Exception:
        return True


check("refuses a directory where the file goes", raises(lambda: T.tree_from_prime(cp, pd, "lean/PEqualNP/Outside/L_meta_dir", blob)))
check("refuses a path outside the primed directory", raises(lambda: T.tree_from_prime(cp, pd, "lean/PEqualNP/Inside/b", blob)))
check("refuses a prime of another base", raises(lambda: T.load_prime(pf, "f" * 40)))
open(pf + ".cut", "wb").write(data[:-7])
check("refuses a truncated prime file", raises(lambda: T.load_prime(pf + ".cut", base)))
check("refuses a missing prime file", raises(lambda: T.load_prime(pf + ".none", base)))
sh("rm", "-rf", tmp)
print("TREEPRIME FAIL " + ", ".join(fails) if fails else "TREEPRIME PASS")
sys.exit(1 if fails else 0)
