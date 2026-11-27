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


# ---- tree prime (W7, infra/Lead 10:58 UTC 27 Nov: SPEED r9 tree 11.4/20.9 s under move4 against 2.3/3.7 s quiet) ----
# The drain reads the trees along the units' common directory ONCE per adopted base (prime(), 4 ls-tree in the shared
# base) and writes them to one file; each unit then builds its 4 new trees in-process (tree_from_prime(): no git
# process, the trees written as loose objects into the unit's copy), the same sha as tree_with_file (treeprime_test.py).
# Any problem (no file, other base, other directory, a bad file) is a miss and the unit takes tree_with_file as before.
import hashlib, json, os, zlib

PRIME_DIR = "lean/PEqualNP/Outside"


def prime(repo, base, dirpath=PRIME_DIR, extra=None):
    """header + raw `ls-tree -z` bytes of the tree at each level of dirpath (root first) in commit `base`; `extra` goes
    into the header (the drain: t = start of the fetch that brought this base)"""
    parts = dirpath.split("/")
    r = _git(repo, "rev-parse", base + "^{tree}")
    root = r.stdout.decode().strip()
    if r.returncode or not root:
        raise RuntimeError("no tree for " + base)
    shas, raws = [root], []
    for level in range(len(parts) + 1):
        r = _git(repo, "ls-tree", "-z", shas[level])
        if r.returncode:
            raise RuntimeError("ls-tree %s: %s" % (shas[level], r.stderr.decode(errors="replace")[-200:]))
        raws.append(r.stdout)
        if level < len(parts):
            nxt = None
            for e in r.stdout.split(b"\0"):
                if e:
                    meta, n = e.split(b"\t", 1)
                    if n == parts[level].encode():
                        m, t, s = meta.split()
                        if t != b"tree":
                            raise RuntimeError("%s is a %s, not a directory" % (parts[level], t.decode()))
                        nxt = s.decode()
                        break
            if nxt is None:
                raise RuntimeError("no directory %s in %s" % ("/".join(parts[:level + 1]), base))
            shas.append(nxt)
    head = dict(extra or {}, v=1, base=base, dir=dirpath, trees=shas, lens=[len(x) for x in raws])
    return json.dumps(head).encode() + b"\n" + b"".join(raws)


def write_prime(path, data):
    tmp = "%s.%d.t" % (path, os.getpid())
    with open(tmp, "wb") as o:
        o.write(data)
    os.replace(tmp, path)


def load_prime(path, base):
    """(header, [raw level bytes]) for base, else raises (the caller counts a miss)"""
    with open(path, "rb") as f:
        data = f.read()
    nl = data.index(b"\n")
    head = json.loads(data[:nl])
    if head.get("v") != 1 or head.get("base") != base:
        raise RuntimeError("prime is for another base")
    raws, off = [], nl + 1
    for n in head["lens"]:
        raws.append(data[off:off + n]); off += n
    if off != len(data) or len(raws) != len(head["trees"]):
        raise RuntimeError("prime file is truncated")
    return head, raws


def _objdir(repo):
    d = os.path.join(repo, ".git", "objects")
    return d if os.path.isdir(d) else os.path.join(repo, "objects")


def _write_tree(objdir, body):
    """git's loose tree object for `body`; returns its sha (hex)"""
    obj = b"tree %d\0" % len(body) + body
    sha = hashlib.sha1(obj).hexdigest()
    d = os.path.join(objdir, sha[:2]); p = os.path.join(d, sha[2:])
    if not os.path.exists(p):
        os.makedirs(d, exist_ok=True)
        tmp = "%s.%d.t" % (p, os.getpid())
        with open(tmp, "wb") as o:
            o.write(zlib.compress(obj, 1))
        os.replace(tmp, p)
    return sha


def _body_with(raw, name, kind, sha_hex, mode):
    """tree body of the ls-tree -z entries `raw` with entry `name` added or replaced, in git's order (a tree sorts as
    name + '/'). Refuses to replace a directory by a file or the reverse."""
    key = name.encode() + (b"/" if kind == b"tree" else b"")
    new = b"%s %s\0" % (mode.encode(), name.encode()) + bytes.fromhex(sha_hex)
    out, placed = [], False
    for e in raw.split(b"\0"):
        if not e:
            continue
        meta, n = e.split(b"\t", 1)
        m, t, s = meta.split()
        if n == name.encode():
            if t != kind:
                raise RuntimeError("%s is a %s in the base" % (name, t.decode()))
            continue
        k = n + (b"/" if t == b"tree" else b"")
        if not placed and k > key:
            out.append(new); placed = True
        out.append(b"%s %s\0" % (m.lstrip(b"0"), n) + bytes.fromhex(s.decode()))
    if not placed:
        out.append(new)
    return b"".join(out)


def tree_from_prime(repo, prime_data, rel, blob, mode="100644"):
    """the same sha as tree_with_file(repo, base, rel, blob), from the drain's prime of that base; rel must be a file
    directly in the primed directory. Raises on anything else (the caller falls back to tree_with_file)."""
    head, raws = prime_data
    d, fname = rel.rsplit("/", 1)
    if d != head["dir"]:
        raise RuntimeError("path %s is not in the primed directory %s" % (rel, head["dir"]))
    parts = d.split("/")
    od = _objdir(repo)
    sha = _write_tree(od, _body_with(raws[-1], fname, b"blob", blob, mode))
    for level in range(len(parts) - 1, -1, -1):
        sha = _write_tree(od, _body_with(raws[level], parts[level], b"tree", sha, "40000"))
    return sha
