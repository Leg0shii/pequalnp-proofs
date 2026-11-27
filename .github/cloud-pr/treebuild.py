#!/usr/bin/env python3
"""treebuild (lane "tree", W7, 27 Nov): the unit's tree = the base tree plus ONE path, built with git ls-tree / git
mktree along that path only (one ls-tree and one mktree per directory level: lean, lean/PEqualNP, lean/PEqualNP/Outside,
then the root). The old path (read-tree of the whole upstream tree into a fresh index, update-index, write-tree) is kept
here only as the reference for the equivalence case: git trees are canonical, so the same entries give the same sha.

mktree runs with --missing: in a blobless clone the sibling blobs are not local, and mktree must neither verify nor
lazily fetch them (the trees along the path are local; nothing is read from the network)."""
import subprocess


def _git(repo, *a, inp=None, env=None):
    return subprocess.run(["git", "-C", repo] + list(a), input=inp, capture_output=True, env=env, timeout=120)


def _ls(repo, tree):
    """entries of one tree object (not recursive), raw bytes per entry: b'<mode> <type> <sha>\\t<name>'"""
    if tree is None:
        return []
    r = _git(repo, "ls-tree", "-z", tree)
    if r.returncode:
        raise RuntimeError("ls-tree %s: %s" % (tree, r.stderr.decode(errors="replace")[-200:]))
    return [e for e in r.stdout.split(b"\0") if e]


def _mktree(repo, entries):
    r = _git(repo, "mktree", "-z", "--missing", inp=b"".join(e + b"\0" for e in entries))
    sha = r.stdout.decode().strip()
    if r.returncode or not sha:
        raise RuntimeError("mktree: " + r.stderr.decode(errors="replace")[-200:])
    return sha


def tree_with_file(repo, base, rel, blob, mode="100644"):
    """sha of the tree of commit `base` with blob `blob` added (or replaced) at path `rel`. Raises on any git error."""
    parts = rel.split("/")
    r = _git(repo, "rev-parse", base + "^{tree}")
    root = r.stdout.decode().strip()
    if r.returncode or not root:
        raise RuntimeError("no tree for " + base)
    chain = [root]                                   # tree sha at each directory level (None = does not exist yet)
    for name in parts[:-1]:
        cur, nxt = chain[-1], None
        for e in _ls(repo, cur):
            meta, n = e.split(b"\t", 1)
            if n.decode() == name:
                m, t, s = meta.split()
                if t != b"tree":
                    raise RuntimeError("%s is a %s, not a directory" % (name, t.decode()))
                nxt = s.decode()
                break
        chain.append(nxt)
    new = ("%s blob %s\t%s" % (mode, blob, parts[-1])).encode()
    for level in range(len(parts) - 1, -1, -1):      # innermost directory first, the root last
        ents = [e for e in _ls(repo, chain[level]) if e.split(b"\t", 1)[1].decode() != parts[level]]
        sha = _mktree(repo, ents + [new])
        if level:
            new = ("040000 tree %s\t%s" % (sha, parts[level - 1])).encode()
    return sha


def tree_by_index(repo, base, rel, blob, idx):
    """the OLD path (reference only): read-tree of the whole base tree into a fresh index, update-index, write-tree"""
    import os
    env = dict(os.environ, GIT_INDEX_FILE=idx)
    if _git(repo, "read-tree", base, env=env).returncode:
        raise RuntimeError("read-tree failed")
    _git(repo, "update-index", "--add", "--cacheinfo", "100644,%s,%s" % (blob, rel), env=env)
    return _git(repo, "write-tree", env=env).stdout.decode().strip()
