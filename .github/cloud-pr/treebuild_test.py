#!/usr/bin/env python3
"""treebuild_test (lane "tree", W7): the mktree path gives the SAME tree sha as the old read-tree/write-tree path.
Cases on a blobless clone of upstream main (as the drain's shared checkout): 5 new unit files, one replaced file, a
path whose directory does not exist yet. The clone's remote is cut first, so any lazy blob fetch fails the case.
Also the full commit: commit-tree on both trees with a fixed date and message gives the same commit sha.
Times: per unit, old (read-tree + update-index + write-tree) and new (ls-tree/mktree along the path).

  python3 treebuild_test.py [UPSTREAM_REPO [BRANCH]]   default: this checkout's upstream remote URL, else the current repo
  -> one line per case, then "TREEBUILD PASS" (exit 0) or "TREEBUILD FAIL: <cases>" (exit 1)"""
import os, subprocess, sys, tempfile, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import treebuild as T


def g(repo, *a, inp=None, env=None):
    r = subprocess.run(["git", "-C", repo] + list(a), input=inp, capture_output=True, text=True, env=env)
    if r.returncode:
        raise RuntimeError(" ".join(a) + ": " + r.stderr[-300:])
    return r.stdout.strip()


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    d = tempfile.mkdtemp(prefix="treebuild-")
    repo = os.path.join(d, "up")
    env = dict(os.environ, GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="uploadpack.allowFilter", GIT_CONFIG_VALUE_0="true")
    url = src if "://" in src else "file://" + os.path.abspath(src)
    br = ["--branch", sys.argv[2]] if len(sys.argv) > 2 else []
    r = subprocess.run(["git", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout"] + br + [url, repo], env=env,
                       capture_output=True, text=True)
    if r.returncode:
        print("TREEBUILD FAIL: clone", r.stderr[-200:]); sys.exit(1)
    g(repo, "remote", "set-url", "origin", "file:///nonexistent-mintcross-no-fetch")    # a lazy fetch now fails
    base = g(repo, "rev-parse", "HEAD")
    n_out = len(g(repo, "ls-tree", "--name-only", base, "lean/PEqualNP/Outside/").split())
    print(f"base {base[:12]}, {n_out} files in lean/PEqualNP/Outside/, blobless clone, remote cut", flush=True)
    cases = [("new-%d" % k, "lean/PEqualNP/Outside/L_meta_99999%d.lean" % k, "theorem t%d : True := trivial\n" % k) for k in range(5)]
    ex = g(repo, "ls-tree", "--name-only", base, "lean/PEqualNP/Outside/").split()
    if ex:
        cases.append(("replace", ex[len(ex) // 2], "-- replaced\n"))
    cases.append(("newdir", "lean/PEqualNP/OutsideX/Y/L_meta_1.lean", "-- new directory\n"))
    bad, t_old, t_new = [], [], []
    cenv = dict(os.environ, GIT_AUTHOR_NAME="Leg0shii", GIT_COMMITTER_NAME="Leg0shii",
                GIT_AUTHOR_EMAIL="46093332+Leg0shii@users.noreply.github.com", GIT_COMMITTER_EMAIL="46093332+Leg0shii@users.noreply.github.com",
                GIT_AUTHOR_DATE="1795700000 +0000", GIT_COMMITTER_DATE="1795700000 +0000")
    for name, rel, body in cases:
        blob = g(repo, "hash-object", "-w", "--stdin", inp=body)
        t = time.time()
        old = T.tree_by_index(repo, base, rel, blob, os.path.join(d, "idx-" + name))
        t_old.append(time.time() - t)
        t = time.time()
        new = T.tree_with_file(repo, base, rel, blob)
        t_new.append(time.time() - t)
        changed = g(repo, "diff-tree", "--name-only", "-r", base, new).split()
        c_old = g(repo, "commit-tree", old, "-p", base, "-m", "L-meta-x", env=cenv)
        c_new = g(repo, "commit-tree", new, "-p", base, "-m", "L-meta-x", env=cenv)
        ok = old == new and c_old == c_new and changed == [rel]
        print(f"{'PASS' if ok else 'FAIL'} {name}: old {old[:12]} new {new[:12]} commit {c_old[:12]}/{c_new[:12]} changed={changed} "
              f"old={t_old[-1]:.3f}s new={t_new[-1]:.3f}s", flush=True)
        if not ok:
            bad.append(name)
    print(f"times per unit: old median {sorted(t_old)[len(t_old) // 2]:.3f}s max {max(t_old):.3f}s; new median "
          f"{sorted(t_new)[len(t_new) // 2]:.3f}s max {max(t_new):.3f}s", flush=True)
    subprocess.run(["rm", "-rf", d])
    print("TREEBUILD PASS" if not bad else "TREEBUILD FAIL: " + " ".join(bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
