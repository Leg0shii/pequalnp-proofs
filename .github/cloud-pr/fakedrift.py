#!/usr/bin/env python3
"""fakedrift (HARDENING 14 W8, BLINDSPOTS B15): do the replay fakes still look like the real GitHub answers?

  fakedrift.py capture OUT.json     one real response per endpoint the fork scripts use (read-only, public data):
        E1 pulls open   repos/open-goat/pequalnp-proofs/pulls?state=open&sort=created&direction=desc&per_page=100
        E2 pulls closed repos/open-goat/pequalnp-proofs/pulls?state=closed&sort=updated&direction=desc&per_page=100
        E3 pulls/files  repos/open-goat/pequalnp-proofs/pulls/<newest open>/files?per_page=100
        E4 comments     repos/open-goat/pequalnp-proofs/issues/<closed PR>/comments?per_page=30 (first non-empty of 3)
        E5 ls-remote    git ls-remote https://github.com/<fork> refs/heads/main
      GitHub reads: 6 at most (5 REST + 1 git). Desk 0. Data host 0.
  fakedrift.py diff REAL.json [ROOT]  field sets of the real capture against the field sets the replay fakes serve
      (mintdrill.py of ROOT: its worlds' open/closed pulls, served pulls/files and comments, its ls-remote lines).
      A field counts when the code reads it from that endpoint (table USED, each entry anchored to its function):
        D1 FAKE-ONLY  the fake serves a field the real API never sends (tests can pass on data live never has)
        D2 NULLABLE   the real API sends null or omits it, the fake never does (the "PR without created_at" case)
        D3 TYPE       the types differ
        D4 UNTESTED   the real API sends it, the code reads it, the fake never sends it
        D5 shape      ls-remote line shape differs (sha column; info while the faked callers read ref names only)
        D6 ABSENT     the code reads a field the real response does not have
      -> "FAKEDRIFT OK ..." (exit 0) or "FAKEDRIFT FAIL ..." (exit 1)
  fakedrift.py daily DIR [ROOT]     capture into DIR/real-YYYYMMDD.json unless one is under 24 h old, then diff.
"""
import glob, json, os, re, subprocess, sys, time, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
UP = "open-goat/pequalnp-proofs"
FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
READS = [0]


def get(path):
    READS[0] += 1
    h = {"Accept": "application/vnd.github+json", "User-Agent": "fakedrift"}
    if os.environ.get("GITHUB_TOKEN"):
        h["Authorization"] = "Bearer " + os.environ["GITHUB_TOKEN"]
    try:
        with urllib.request.urlopen(urllib.request.Request("https://api.github.com/" + path, headers=h), timeout=60) as r:
            return json.loads(r.read())
    except urllib.error.HTTPError as e:
        if e.code not in (401, 403) or "Authorization" not in h:
            raise
        h.pop("Authorization")                       # a token scoped to other repos: public data needs none
        with urllib.request.urlopen(urllib.request.Request("https://api.github.com/" + path, headers=h), timeout=60) as r:
            return json.loads(r.read())


def capture(out):
    t0 = time.time()
    cap = {"at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "E": {}}
    op = get(f"repos/{UP}/pulls?state=open&sort=created&direction=desc&per_page=100")
    cl = get(f"repos/{UP}/pulls?state=closed&sort=updated&direction=desc&per_page=100")
    cap["E"]["E1"], cap["E"]["E2"] = op, cl
    cap["E"]["E3"] = get(f"repos/{UP}/pulls/{op[0]['number']}/files?per_page=100") if op else []
    cap["E"]["E4"] = []
    for p in [x for x in cl if not x.get("merged_at")][:3]:
        c = get(f"repos/{UP}/issues/{p['number']}/comments?per_page=30")
        if c:
            cap["E"]["E4"] = c; break
    READS[0] += 1
    r = subprocess.run(["git", "ls-remote", f"https://github.com/{FORK}", "refs/heads/main"], capture_output=True, text=True, timeout=60)
    cap["E"]["E5"] = r.stdout.splitlines()
    cap["reads"] = READS[0]
    with open(out + ".tmp", "w") as f:
        json.dump(cap, f)
    os.replace(out + ".tmp", out)
    print("FAKEDRIFT capture %s E1=%d E2=%d E3=%d E4=%d E5=%d reads=%d sec=%.1f" % (
        out, len(op), len(cl), len(cap["E"]["E3"]), len(cap["E"]["E4"]), len(cap["E"]["E5"]), READS[0], time.time() - t0))
    return 0


def tname(v):
    return "null" if v is None else {bool: "bool", int: "int", float: "float", str: "str", dict: "dict", list: "list"}.get(type(v), "?")


def fields(items):
    """path -> {"types": set, "n": items with the path, "of": items}; top-level item keys and nested dict keys"""
    acc = {}

    def walk(v, path, seen):
        if isinstance(v, dict):
            for k, x in v.items():
                p = path + "." + k
                seen.add(p)
                acc.setdefault(p, {"types": set(), "n": 0})["types"].add(tname(x))
                walk(x, p, seen)
        elif isinstance(v, list):
            for x in v[:50]:
                walk(x, path + "[]", seen)
    for it in items:
        seen = set()
        walk(it, "", seen)
        for p in seen:
            acc[p]["n"] += 1
    for p in acc:
        acc[p]["of"] = len(items)
    return acc


# The fields the code reads from each endpoint, anchored to the function that reads them. An anchor whose function no
# longer names the key fails the run ("anchor stale"), so this table cannot silently fall behind the code.
USED = {
    "E1": {"number": ["submit.py:_build_snapshot", "dupclose.py:_row"], "created_at": ["submit.py:_build_snapshot", "dupclose.py:_row"],
           "title": ["submit.py:_build_snapshot", "dupclose.py:_row"], "user.login": ["submit.py:_build_snapshot", "dupclose.py:_row"],
           "head.ref": ["submit.py:_build_snapshot", "dupclose.py:_row"], "head.sha": ["submit.py:_build_snapshot"],
           "body": ["dupclose.py:_row"]},
    "E2": {"number": ["dupclose.py:merged_fill", "dupclose.py:rej_burst"], "title": ["dupclose.py:merged_fill", "dupclose.py:rej_burst"],
           "merged_at": ["dupclose.py:merged_fill", "dupclose.py:rej_burst"], "closed_at": ["dupclose.py:rej_burst"],
           "user.login": ["dupclose.py:merged_fill", "dupclose.py:rej_burst"]},
    "E3": {"filename": ["submit.py:pr_files"]},
    "E4": {"body": ["dupclose.py:rej_burst"], "user.login": ["dupclose.py:rej_burst"]},
}


def code_keys(root):
    """{endpoint: {path: "file:function"}} and the stale anchors"""
    import ast
    srcs, stale, ks = {}, [], {}
    for e, d in USED.items():
        for path, anchors in d.items():
            leaf = path.rsplit(".", 1)[-1]
            for a in anchors:
                fn, func = a.split(":")
                if fn not in srcs:
                    fp = os.path.join(root, ".github", "cloud-pr", fn)
                    txt = open(fp).read() if os.path.isfile(fp) else ""
                    srcs[fn] = (txt, ast.parse(txt) if txt else None)
                txt, tree = srcs[fn]
                node = next((n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == func), None) if tree else None
                body = ast.get_source_segment(txt, node) if node else ""
                if not re.search(r"""["']%s["']""" % re.escape(leaf), body or ""):
                    stale.append("%s %s at %s" % (e, path, a))
                else:
                    ks.setdefault(e, {}).setdefault(path, a)
    return ks, stale


def fakes(root):
    """the objects mintdrill's fakes serve, per endpoint; None + reason when the fake code is not the one we model"""
    src_p = os.path.join(root, ".github", "cloud-pr", "mintdrill.py")
    src = open(src_p).read()
    need = {"E3": ['json.dumps([{"filename": f} for f in p.get("files") or []])'],
            "E4": ['json.dumps(p.get("comments", []))', 'json.dumps(cmts(p))'],          # cmts: Y3 comments by created_at
            "E5": ['"".join(f"0\\t{r}\\n" for r in refs)', '"".join(f"{h}\\t{r}\\n" for h, r in rows']}
    miss = [k for k, alts in need.items() if not any(x in src for x in alts)]
    sys.path.insert(0, os.path.dirname(src_p))
    import mintdrill as M
    cs, _ = M.cases()
    op, cl = [], []
    for c in cs:
        w = c[2]
        op += w.get("open_pulls", []); cl += w.get("closed_pulls", [])
    allp = op + cl
    return {"E1": op, "E2": cl, "E3": [{"filename": f} for p in allp for f in (p.get("files") or [])],
            "E4": [c for p in allp for c in (p.get("comments") or [])],
            "E5": ["0\trefs/heads/x"]}, miss, len(cs)


def diff(real_p, root):
    t0 = time.time()
    real = json.load(open(real_p))
    age_h = (time.time() - (time.mktime(time.strptime(real["at"][:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone)) / 3600
    fk, miss, ncases = fakes(root)
    ck, stale = code_keys(root)
    bad, info = [], []
    for k in miss:
        bad.append("%s fake source not found in mintdrill.py (fakedrift models an older fake: update it)" % k)
    for st in stale:
        bad.append("ANCHOR stale: %s no longer names the key (update USED in fakedrift.py)" % st)
    for e in ("E1", "E2", "E3", "E4"):
        R, F = fields(real["E"][e]), fields(fk[e])
        if not real["E"][e]:
            info.append("%s real sample empty" % e); continue
        if not fk[e]:
            bad.append("%s no fake object at all" % e); continue
        used = ck.get(e, {})
        for p in sorted(set(R) | set(F)):
            q = p.lstrip(".")
            r, f = R.get(p), F.get(p)
            tag = "%s %s" % (e, q)
            at = used.get(q)
            if r is None and f is not None:
                if at:
                    bad.append("D1 FAKE-ONLY %s: the code reads it (%s), the real API never sends it" % (tag, at))
                elif "." not in q:
                    info.append("D1 fake-only %s (not read from this endpoint)" % tag)
                continue
            if not at:
                continue
            if f is None:
                bad.append("D4 UNTESTED %s (real %s) read in %s, the fake never sends it" % (tag, "/".join(sorted(r["types"])), at))
                continue
            rnull, rmiss = "null" in r["types"], r["n"] < r["of"]
            fnull, fmiss = "null" in f["types"], f["n"] < f["of"]
            if (rnull and not fnull) or (rmiss and not fmiss):
                bad.append("D2 NULLABLE %s real %s, fake never (read in %s)" % (
                    tag, ("null" if rnull else "") + (" missing in %d of %d" % (r["of"] - r["n"], r["of"]) if rmiss else ""), at))
            rt, ft = r["types"] - {"null"}, f["types"] - {"null"}
            if rt and ft and rt != ft:
                bad.append("D3 TYPE %s real %s fake %s (read in %s)" % (tag, "/".join(sorted(rt)), "/".join(sorted(ft)), at))
        for q, at in used.items():
            if "." + q not in R:
                bad.append("D6 ABSENT %s: read in %s, not in the real response" % (e + " " + q, at))
    rl = real["E"]["E5"]
    rs = {re.sub(r"^[0-9a-f]{40}\t", "SHA40\t", x).split("\t")[0] for x in rl}
    fs = {re.sub(r"^[0-9a-f]{40}\t", "SHA40\t", x).split("\t")[0] for x in fk["E5"]}
    if rs != fs:
        # the faked ls-remote callers (dupclose filing_go, v2_on) read ref names only; drain.py reads the sha but is
        # not driven by these fakes. Listed so a new sha reader gets a fixture with real 40-hex shas.
        info.append("D5 shape E5 ls-remote sha column real %s fake %s (faked callers read ref names only)" % (sorted(rs), sorted(fs)))
    for b in bad:
        print("FAIL", b)
    for i in info:
        print("info", i)
    sha = subprocess.run(["git", "-C", root, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    kinds = sorted({b.split()[0] + " " + b.split()[1] for b in bad if b.startswith("D")})
    print("FAKEDRIFT %s %s real=%s age=%.1fh fake_cases=%d used_fields=%d fail=%d info=%d sec=%.1f%s" % (
        "OK" if not bad else "FAIL", sha, real["at"], age_h, ncases, sum(len(v) for v in ck.values()), len(bad), len(info), time.time() - t0,
        (": " + ", ".join(kinds)) if bad else ""))
    if age_h > 26:
        print("FAKEDRIFT FAIL capture older than 26 h"); return 1
    return 0 if not bad else 1


def daily(d, root):
    os.makedirs(d, exist_ok=True)
    caps = sorted(glob.glob(os.path.join(d, "real-*.json")))
    fresh = caps and time.time() - os.path.getmtime(caps[-1]) < 24 * 3600
    p = caps[-1] if fresh else os.path.join(d, "real-%s.json" % time.strftime("%Y%m%d-%H%M", time.gmtime()))
    if not fresh:
        capture(p)
    return diff(p, root)


if __name__ == "__main__":
    a = sys.argv[1:]
    root_d = os.path.dirname(os.path.dirname(HERE))
    if a[:1] == ["capture"] and len(a) == 2:
        sys.exit(capture(a[1]))
    if a[:1] == ["diff"] and len(a) >= 2:
        sys.exit(diff(a[1], os.path.abspath(a[2]) if len(a) > 2 else root_d))
    if a[:1] == ["daily"] and len(a) >= 2:
        sys.exit(daily(a[1], os.path.abspath(a[2]) if len(a) > 2 else root_d))
    print(__doc__); sys.exit(2)
