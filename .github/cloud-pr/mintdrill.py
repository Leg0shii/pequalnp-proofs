#!/usr/bin/env python3
"""mintdrill (HARDENING T1, Lead 05:15 UTC 27 Nov): replay suite for the opener (submit.py), the drain halt check
(drain.py) and the closer (dupclose.py). Every case runs the REAL code of the given checkout in a child process with
a fake world: fake mirror (gaps.json), fake GitHub (open/closed pulls, comments, pr create/close), fake taken list,
fake upstream main, fake gate and fake toolkit refs. Nothing leaves the box: any call the fakes do not know is logged
as UNEXPECTED and fails the case.

Cases:
  recorded/F3-*    the 26 Nov 21:52-21:53 tl6c mint (111 provable units free at first sight, gate open, every claim
                   answered "held"): each must get our PR (I1) with no desk claim
  recorded/F4      our 12 leased PRs on the 19:21 slice and yifgu's later merged "Prove L-meta-N": all closed (I3)
  recorded/I4      one maker close of ours -> filing/stop pushed; then the opener files nothing (I4)
  recorded/I7-*    our handle on the mirror pause list / halt set: zero desk requests (I7)
  hostile/X1..X11  the red team's fixtures (team/redteam/FIXTURES.md), each "no PR" or "PR closed"
Invariants checked on every opener case: I2 (no PR next to another author's open/merged PR, a file on upstream main,
or a holder that is not us) and I7 (no desk request while paused or halted).

  python3 mintdrill.py [SRC]       SRC = checkout whose .github/cloud-pr/*.py run (default: this file's checkout)
  -> one line per case, then "PREFLIGHT PASS <sha>" (exit 0) or "PREFLIGHT FAIL <sha>: <cases>" (exit 1)
"""
import contextlib, copy, json, os, re, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "mintdrill")
HANDLE = "Leg0shii"
T0 = 1795700000.0                      # fixed clock of every case (no wall time in the results)


def iso(t):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))


def reltime(v, now):
    """fixture times: "T", "T-60s", "T+5s" or None"""
    if v in (None, ""):
        return None
    m = re.fullmatch(r"T([+-]\d+)s?", v) if v != "T" else None
    return iso(now + (int(m.group(1)) if m else 0))


def norm_pull(p, now, k):
    q = dict(p)
    q.setdefault("user", {"login": "rival1"})
    q.setdefault("head", {"ref": "patch-1"})
    q.setdefault("body", "")
    q.setdefault("files", [])
    q["created_at"] = reltime(p.get("created_at"), now) or iso(now - 600 + k)
    q["merged_at"] = reltime(p.get("merged_at"), now) if p.get("merged_at") else None
    q["closed_at"] = reltime(p.get("closed_at"), now) if p.get("closed_at") else None
    return q


def unit_rec(g):
    gid = g["id"]
    r = {"pr_numbers": [], "pr_open": 0, "held_now": False, "holders_now": 0, "statement": "S(" + gid + ")",
         "file": "lean/PEqualNP/Outside/%s.lean" % gid.replace("-", "_"), "module": "PEqualNP.Outside." + gid.replace("-", "_"),
         "imports": ["PEqualNP.Defs"], "weight": 1, "lane": "main"}
    r.update(g)
    return r


# ---------------------------------------------------------------------------------------------------------------
# child: one opener case (real submit.py main())
# ---------------------------------------------------------------------------------------------------------------
def child_submit(src, w):
    sys.path.insert(0, os.path.join(src, ".github", "cloud-pr"))
    import submit as S
    gid = w["gid"]
    rel = "lean/PEqualNP/Outside/%s.lean" % gid.replace("-", "_")
    out = {"prs": [], "desk": [], "unexpected": [], "gaps_reads": 0}
    reads = [0]

    def gaps_now():
        k = reads[0]; reads[0] += 1
        seq = w.get("gaps_seq") or [w["gaps"]]
        gl = seq[min(k, len(seq) - 1)]
        return {"gaps": copy.deepcopy(gl), "paused": [{"handle": h, "paused_until": iso(T0 + 3600)} for h in w.get("paused", [])],
                "withdrawn": {}, "checked": [], "updated_at": iso(T0)}

    def curl_json(url, timeout=60):
        out["gaps_reads"] += 1
        if "gaps.json" not in url:
            out["unexpected"].append("curl " + url); raise RuntimeError("unexpected url")
        return gaps_now()
    S.curl_json = curl_json

    pulls_open = sorted(w.get("open_pulls", []), key=lambda p: -p["number"])
    pulls_closed = sorted(w.get("closed_pulls", []), key=lambda p: -p["number"])

    def cp(stdout="", rc=0, err=""):
        return subprocess.CompletedProcess([], rc, stdout, err)

    def gh(args, write=False, timeout=120):
        a = list(args)
        if a[0] == "api" and "/pulls?" in a[1]:
            q = dict(x.split("=", 1) for x in a[1].split("?", 1)[1].split("&"))
            if "head" in q:                          # open_pr_for_branch: our own open PR on fork branch <gid>
                h = q["head"].split(":", 1)[-1]
                return cp("".join("https://github.com/open-goat/pequalnp-proofs/pull/%d\n" % p["number"] for p in pulls_open
                                  if p["user"]["login"] == HANDLE and (p.get("head") or {}).get("ref") == h))
            src_l = pulls_open if q.get("state") == "open" else pulls_closed
            pp, pg = int(q.get("per_page", 30)), int(q.get("page", 1))
            return cp(json.dumps(src_l[(pg - 1) * pp:pg * pp]))
        m = re.search(r"/pulls/(\d+)/files", a[1]) if a[0] == "api" else None
        if m:
            p = next((x for x in pulls_open + pulls_closed if x["number"] == int(m.group(1))), {})
            return cp(json.dumps([{"filename": f} for f in p.get("files") or []]))
        if a[:2] == ["pr", "list"]:
            n = a[a.index("--search") + 1]
            res = []
            for p in pulls_open + pulls_closed:
                if n in (p.get("title") or "") or any(n in f for f in p.get("files") or []):
                    st = "OPEN" if not p.get("closed_at") else ("MERGED" if p.get("merged_at") else "CLOSED")
                    res.append({"number": p["number"], "state": st, "title": p.get("title"), "author": p["user"],
                                "files": [{"path": f} for f in p.get("files") or []]})
            return cp(json.dumps(res))
        if a[:2] == ["pr", "view"]:
            n = int(a[2])
            p = next((x for x in pulls_open + pulls_closed if x["number"] == n), None)
            if "author" in " ".join(a):
                return cp((p or {}).get("user", {}).get("login", "rival1") + "\n")
            if "comments" in " ".join(a):
                return cp("")
            if "files" in " ".join(a):
                return cp(json.dumps({"files": [{"path": f, "additions": 10} for f in (p or {}).get("files") or []]}))
        out["unexpected"].append("gh " + " ".join(a[:3]))
        raise RuntimeError("unexpected gh call")
    S.gh = gh

    def git(*a, env=None, timeout=300):
        a = list(a)
        if a[0] == "rev-parse":
            return cp("base0\n")
        if a[0] == "cat-file":
            return cp(rc=0 if a[-1] == "base0:" + rel and rel in w.get("main_files", []) else 1)
        if a[0] in ("hash-object",):
            return cp("blob0\n")
        if a[0] in ("read-tree", "update-index", "clean"):
            return cp()
        if a[0] == "write-tree":
            return cp("tree0\n")
        if a[0] == "diff-tree":
            return cp(rel + "\n")
        if a[0] == "commit-tree":
            return cp("commit0\n")
        out["unexpected"].append("git " + " ".join(a[:2]))
        return cp(rc=1)
    S.git = git

    def run(cmd, timeout=300, env=None, cwd=None):
        if cmd[:3] == ["gh", "pr", "create"]:
            out["prs"].append({"gid": gid, "lease": "Lease:" in cmd[cmd.index("--body") + 1]})
            return cp("https://github.com/open-goat/pequalnp-proofs/pull/99999\n")
        if len(cmd) > 1 and cmd[0] == "bash" and cmd[1].endswith("checkcore.sh"):
            ps = w.get("proof_statement")
            if ps is not None:                       # the real guard compares the file with the listed statement
                g = next((x for x in gaps_now()["gaps"] if x["id"] == gid), {})
                reads[0] -= 1
                if g.get("statement") and g["statement"] != ps:
                    return cp("FAIL: statement differs from gaps.json\n", 1)
            return cp("guards ok\n")
        out["unexpected"].append("run " + " ".join(cmd[:3]))
        return cp(rc=1, err="unexpected")
    S.run = run

    tl = w.get("taken", {})
    S._taken_list = lambda: (None if tl is None else dict(tl))
    S._TL.clear()

    class DG:
        REPO = "/nonexistent"
        def lease_of(self, g): return None
        def acquire(self, g, why=None): return True
        def record_lease(self, *a, **k): return None
        def _marker(self, m): return "marker0"
    S.dg = lambda: DG()
    S.claim_lock = lambda g: True
    S.take_slot = lambda g: True
    S.free_slot = lambda: None
    S.stopped = lambda: False
    S.push_branch = lambda c, g: None
    S.delete_ready = lambda: None
    S.pr_gate = contextlib.nullcontext
    S.release = lambda lid, why: out["desk"].append("release " + str(lid)) if lid else None
    S.time.sleep = lambda s: None
    S.time.time = lambda: T0                # the fixtures' clock (created_at of the pulls is relative to T0)

    def gate_open_now():
        gj = S.LAST_GJ[0] or {}
        if any((p.get("handle") if isinstance(p, dict) else p) == HANDLE for p in gj.get("paused") or []):
            return False, "paused in the mirror"
        return (True, "open ref") if w.get("gate_open", True) else (False, "no open ref")
    S.gate_open_now = gate_open_now

    def gate_claim(g):
        out["desk"].append("claim " + g)
        ans = (w.get("gate_answers") or {}).get(g) or (w.get("gate_answers") or {}).get("*", "ok")
        return (ans, "lease-x1") if ans == "ok" else (ans, None)
    S.gate_claim = gate_claim
    if hasattr(S, "filing_halted"):
        S.filing_halted = lambda: ((True, "filing halted (drill)") if w.get("halted") else (False, ""))
    elif w.get("halted"):
        out["unexpected"].append("no filing_halted in this checkout")
    try:
        S.main()
    except SystemExit:
        pass
    res = dict(l.split("=", 1) for l in open(os.environ["GITHUB_OUTPUT"]).read().splitlines() if "=" in l) \
        if os.path.exists(os.environ["GITHUB_OUTPUT"]) else {}
    out["result"], out["why"] = res.get("result", "?"), res.get("why", "")[:160]
    return out


# ---------------------------------------------------------------------------------------------------------------
# child: one closer case (real dupclose.py one_pass(), at clock times w["passes"])
# ---------------------------------------------------------------------------------------------------------------
def child_close(src, w):
    sys.path.insert(0, os.path.join(src, ".github", "cloud-pr"))
    clock = [T0]
    real_time = time.time
    import dupclose as D
    D.time.time = lambda: clock[0]
    D.time.sleep = lambda s: None
    out = {"closed": [], "pushes": [], "unexpected": []}

    def visible(p):                       # a PR exists from created_at on
        return D.time.mktime(time.strptime(p["created_at"][:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone <= clock[0]

    def tt(v):
        return D.time.mktime(time.strptime(v[:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone if v else None

    def state_at(p):
        q = dict(p)
        c = tt(p.get("closed_at"))
        if c is not None and c > clock[0]:
            q["closed_at"] = None; q["merged_at"] = None
        if p["number"] in out["closed"]:
            q["closed_at"] = iso(clock[0])
        return q
    allp = [x for x in w.get("open_pulls", []) + w.get("closed_pulls", [])]

    def page(k):
        cur = [state_at(p) for p in allp if visible(p)]
        cur = sorted([p for p in cur if not p.get("closed_at")], key=lambda p: -p["number"])
        return cur[(k - 1) * 100:k * 100]
    D._page = page

    def sh(*a, timeout=120, env=None):
        a = list(a)
        s = " ".join(a)
        if a[0] == "gh" and "state=closed" in s:
            cur = [state_at(p) for p in allp if visible(p)]
            cur = sorted([p for p in cur if p.get("closed_at")], key=lambda p: -tt(p["closed_at"]))
            return subprocess.CompletedProcess(a, 0, json.dumps(cur[:100]), "")
        if a[0] == "gh" and "/comments" in s:
            n = int(re.search(r"issues/(\d+)/comments", s).group(1))
            p = next((x for x in allp if x["number"] == n), {})
            return subprocess.CompletedProcess(a, 0, json.dumps(p.get("comments", [])), "")
        if a[0] == "gh" and a[1:3] == ["pr", "close"]:
            out["closed"].append(int(a[3])); return subprocess.CompletedProcess(a, 0, "", "")
        if a[0] == "gh" and "rate_limit" in s:
            return subprocess.CompletedProcess(a, 0, "5000", "")
        if a[0] == "git" and "push" in a:
            out["pushes"].append(a[-1].split(":", 1)[-1]); return subprocess.CompletedProcess(a, 0, "", "")
        if a[0] == "git" and "ls-remote" in a:
            refs = [r for r in w.get("toolkit_refs", []) if any(r.startswith(x.split("*")[0]) for x in a if x.startswith("refs/"))]
            return subprocess.CompletedProcess(a, 0, "".join(f"0\t{r}\n" for r in refs), "")
        if a[0] == "git" and "init" in a:
            return subprocess.run(a, capture_output=True, text=True)
        if a[0] == "git" and "fetch" in a and "pequalnp-proofs" in s:
            return subprocess.CompletedProcess(a, 0, "", "")
        if a[0] == "git" and "ls-tree" in a:
            fs = [f for f, t in w.get("main_files_at", {}).items() if tt(t) <= clock[0]] + list(w.get("main_files", []))
            return subprocess.CompletedProcess(a, 0, "\n".join(fs), "")
        if a[0] == "git" and "fetch" in a:                   # toolkit refs (v2_on etc.): absent
            return subprocess.CompletedProcess(a, 1, "", "absent")
        out["unexpected"].append(s[:80])
        return subprocess.CompletedProcess(a, 1, "", "unexpected")
    D.sh = sh
    D.auth = lambda: []
    D.taken = lambda: w.get("taken_map")
    for k in ("FIXTURE", "FIXTURE_OPEN", "FIXTURE_MERGED", "FIXTURE_CLOSED", "FIXTURE_FILING"):
        os.environ.pop(k, None)
    D.DRY = False
    for t in w["passes"]:
        clock[0] = T0 + t
        D.REJ["t"] = 0
        try:
            D.one_pass()
        except Exception as e:
            out["unexpected"].append("one_pass: " + repr(e)[:120])
    out["closed_at"] = {}
    return out


# ---------------------------------------------------------------------------------------------------------------
# parent: build the cases, run each in a child, judge
# ---------------------------------------------------------------------------------------------------------------
def spawn(kind, src, w):
    d = tempfile.mkdtemp(prefix="mintdrill-")
    proof = os.path.join(d, "proof.lean")
    open(proof, "w").write("import PEqualNP.Defs\n-- drill\n")
    env = dict(os.environ, ID=w.get("gid", "L-meta-1"), MOD=w.get("gid", "L-meta-1").replace("-", "_"), PROOF=proof,
               TREE=d, W=d, GITHUB_OUTPUT=os.path.join(d, "out"), PR_TOKEN="drill", READ_TOKEN="drill", DRY="0",
               GITHUB_REF_NAME="drill", READY_MSG="", MD_KIND=kind, MD_SRC=src)
    env.pop("GITHUB_ACTIONS", None)
    r = subprocess.run([sys.executable, os.path.abspath(__file__), "--child"], input=json.dumps(w), capture_output=True,
                       text=True, env=env, timeout=120, cwd=d)
    m = re.search(r"^MDRESULT (.*)$", r.stdout, re.M)
    if not m:
        return {"crash": (r.stderr or r.stdout).strip().splitlines()[-3:]}
    return json.loads(m.group(1))


def rival_on(w, gid):
    """I2 oracle: another author's open or merged PR touching the unit (title token, branch or file path), a file on
    upstream main, or a holder that is not us."""
    fn = "lean/PEqualNP/Outside/%s.lean" % gid.replace("-", "_")
    tok = re.compile(r"(?<![A-Za-z0-9_-])%s(?![A-Za-z0-9_-])" % re.escape(gid))
    for p in w.get("open_pulls", []) + w.get("closed_pulls", []):
        if p["user"]["login"] == HANDLE or (p.get("closed_at") and not p.get("merged_at")):
            continue
        if tok.search(p.get("title") or "") or tok.search((p.get("head") or {}).get("ref", "").replace("_", "-")) or fn in (p.get("files") or []):
            return "PR #%d" % p["number"]
    if fn in w.get("main_files", []):
        return "file on main"
    for gl in (w.get("gaps_seq") or [w.get("gaps", [])]):
        g = next((x for x in gl if x["id"] == gid), None)
        if g and (g.get("held_now") or (g.get("holders_now") or 0) > 0):
            return "holder"
    return None


def judge_submit(name, w, r, expect):
    """expect: "PR" | "no PR" | "halted" | "no PR or closed" (the closer case decides the second half)"""
    if "crash" in r:
        return False, "crash " + " | ".join(r["crash"])
    if r["unexpected"]:
        return False, "unexpected calls " + ", ".join(r["unexpected"][:3])
    got = "PR" if r["prs"] else "no PR"
    bad = []
    rv = rival_on(w, w["gid"])
    if r["prs"] and rv:
        bad.append(f"I2 PR next to {rv}")
    if (w.get("paused") or w.get("halted")) and r["desk"]:
        bad.append(f"I7 desk requests while paused/halted: {r['desk']}")
    if expect == "PR" and got != "PR":
        bad.append("I1 no PR (" + r["result"] + ": " + r["why"][:90] + ")")
    if expect == "PR" and w.get("gate_answers", {}).get("*") == "held" and any(x.startswith("claim") for x in r["desk"]):
        bad.append("claim sent on a held mint")
    if expect in ("no PR", "halted") and got == "PR":
        bad.append("PR opened (" + r["why"][:80] + ")")
    if expect == "halted" and r["result"] != "halted":
        bad.append("not halted: " + r["result"])
    return (not bad), "; ".join(bad) or f"{got} ({r['result']}: {r['why'][:70]})"


def judge_close(name, w, r, must_close, must_keep=(), must_push=None, no_push=False):
    if r.get("crash"):
        return False, "crash " + " | ".join(r["crash"])
    bad = []
    if r["unexpected"]:
        bad.append("unexpected " + ", ".join(r["unexpected"][:3]))
    miss = [n for n in must_close if n not in r["closed"]]
    if miss:
        bad.append(f"I3 not closed {miss}")
    wrong = [n for n in must_keep if n in r["closed"]]
    if wrong:
        bad.append(f"closed wrongly {wrong}")
    if must_push and not any(p.startswith(must_push) for p in r["pushes"]):
        bad.append(f"I4 no {must_push} push")
    if no_push and any("filing/stop" in p for p in r["pushes"]):
        bad.append("false halt")
    return (not bad), "; ".join(bad) or f"closed {sorted(r['closed'])}"


def unit(gid, tpl="tl6c-not-search", **k):
    return unit_rec(dict({"id": gid, "faithful_by_template": {"template": tpl}, "offerable_now": True}, **k))


def our_pr(n, gid, lease=False, created=-300, title=None):
    return {"number": n, "title": title or gid, "user": {"login": HANDLE}, "head": {"ref": gid}, "files": [],
            "body": "desc" + ("\n\nLease: lid-%d" % n if lease else ""), "created_at": iso(T0 + created),
            "merged_at": None, "closed_at": None}


def rival_pr(n, title, created=-100, merged=None, closed=None, login="rival1", files=(), ref="patch-1"):
    return {"number": n, "title": title, "user": {"login": login}, "head": {"ref": ref}, "files": list(files), "body": "",
            "created_at": iso(T0 + created), "merged_at": iso(T0 + merged) if merged is not None else None,
            "closed_at": iso(T0 + (closed if closed is not None else merged)) if (closed is not None or merged is not None) else None}


def cases():
    rec = json.load(open(os.path.join(DATA, "recorded.json")))
    out = []
    # F3: the held mint. Every provable unit free at first sight must get our PR, no claim.
    for u in [x for x in rec["f3_units"] if x["meet"]]:
        w = {"gid": u["id"], "gaps": [unit(u["id"], u["template"])], "taken": {"L-meta-1": "someone"}, "gate_open": True,
             "gate_answers": {"*": rec["f3_gate_answer"]}}
        out.append(("recorded/F3-" + u["id"], "submit", w, "PR"))
    # F4: yifgu's later merged "Prove L-meta-N" settles our 12 leased PRs: all closed in the first pass
    ours = [our_pr(n, g, lease=l, created=-12000) for n, g, l in rec["f4_ours"]]
    riv = [rival_pr(40000 + i, rec["f4_title"].format(gid=g), created=-9000, merged=-8000, login=rec["f4_rival"])
           for i, (n, g, l) in enumerate(rec["f4_ours"])]
    out.append(("recorded/F4", "close", {"open_pulls": ours, "closed_pulls": riv, "passes": [0]},
                {"must_close": [n for n, g, l in rec["f4_ours"]]}))
    # I4: one maker close of ours with an unknown text halts (filing/stop pushed), and then the opener files nothing
    rj = our_pr(36900, "L-meta-24999", created=-900)
    rj.update(closed_at=iso(T0 - 30), comments=[{"body": "REJECTED: statement does not hold", "user": {"login": "makers-bot"}}])
    out.append(("recorded/I4-halt", "close", {"open_pulls": [], "closed_pulls": [rj], "passes": [0]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    out.append(("recorded/I4-opener", "submit", {"gid": "L-meta-25001", "gaps": [unit("L-meta-25001")], "taken": {"L-meta-1": "someone"}, "halted": True}, "halted"))
    # I7: paused in the mirror -> no desk request at all (the opener may still file bare)
    out.append(("recorded/I7-paused", "submit", {"gid": "L-meta-25002", "gaps": [unit("L-meta-25002", "d11-res2-php-length")],
                                                  "taken": {"L-meta-1": "someone"}, "paused": [HANDLE], "gate_answers": {"*": "ok"}}, "any"))
    out.append(("recorded/I7-halted", "submit", {"gid": "L-meta-25003", "gaps": [unit("L-meta-25003", "d11-res2-php-length")],
                                                  "taken": {"L-meta-1": "someone"}, "halted": True, "gate_answers": {"*": "ok"}}, "halted"))
    # hostile fixtures (red team T7)
    hx = {x["id"]: x for x in json.load(open(os.path.join(DATA, "hostile.json")))}
    for k in ("X1", "X2", "X3", "X3b", "X4", "X8"):
        x = hx[k]
        gl = [unit_rec(g) for g in x["gaps"]]
        tk = x.get("taken", {})
        if tk == {} and k != "X3b":                  # a real taken list always has rows: other units' first PRs
            tk = {"L-meta-1": "someone"}
        ops = x.get("open_pulls", [])
        if k == "X2":                                # a mint burst: the 101 rival PRs all came in the last 60 s
            ops = [dict(p, created_at="T-%ds" % (60 - i // 2)) for i, p in enumerate(sorted(ops, key=lambda p: p["number"]))]
        w = {"gid": gl[0]["id"], "gaps": gl, "taken": tk,
             "open_pulls": [norm_pull(p, T0, i) for i, p in enumerate(ops)],
             "closed_pulls": [norm_pull(p, T0, i) for i, p in enumerate(x.get("closed_pulls", []))]}
        if k == "X4":                                # listed at the first reads, gone at the fresh holder check
            w["gaps_seq"] = [gl, gl, []]
        if k == "X8":
            w["proof_statement"] = x["proof_statement"]
        out.append(("hostile/" + k, "submit", w, "no PR" if k != "X3b" else "no PR or closed"))
    # X3b second half: if the opener filed, the closer must close within 60 s (title "Prove L-meta-90001", merged T-120s)
    x = hx["X3b"]
    out.append(("hostile/X3b-close", "close", {"open_pulls": [our_pr(50050, "L-meta-90001", created=0)],
                                               "closed_pulls": [norm_pull(p, T0, 0) for p in x["closed_pulls"]], "passes": [10, 40]},
                {"must_close": [50050]}))
    # X5: rival opens at +2 s and merges at +3 s, our PR at +5 s: closed by the pass at +25 s, no halt
    out.append(("hostile/X5", "close", {"open_pulls": [our_pr(50060, "L-meta-90001", created=5)],
                                        "closed_pulls": [rival_pr(50004, "L-meta-90001", created=2, merged=3)], "passes": [5, 25, 45]},
                {"must_close": [50060], "no_push": True}))
    # X6: the file lands on upstream main at +10 s with a rival title "Batch of 40 proofs": closed by +70 s (I3 60 s)
    out.append(("hostile/X6", "close", {"open_pulls": [our_pr(50010, "L-meta-90001", created=-600)],
                                        "closed_pulls": [rival_pr(50005, "Batch of 40 proofs", created=-300, merged=10,
                                                                  files=["lean/PEqualNP/Outside/L_meta_90001.lean"])],
                                        "main_files_at": {"lean/PEqualNP/Outside/L_meta_90001.lean": iso(T0 + 10)},
                                        "passes": [0, 30, 50, 70]}, {"must_close": [50010]}))
    # X7: two open PRs of our own on one unit: the younger one closed, the older kept
    out.append(("hostile/X7", "close", {"open_pulls": [our_pr(50011, "L-meta-90001", created=-120),
                                                        our_pr(50012, "L-meta-90001", created=-90, title="Prove L-meta-90001")],
                                        "passes": [0, 30]}, {"must_close": [50012], "must_keep": [50011]}))
    # X9: makers close ours with a text that is not "proved first": halt
    x = hx["X9"]["ours_closed"][0]
    c = our_pr(x["number"], x["gid"], created=-900)
    c.update(closed_at=iso(T0 - 20), comments=[{"body": x["comment"], "user": {"login": x["by"]}}])
    out.append(("hostile/X9", "close", {"closed_pulls": [c], "passes": [0]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # X10: templates without "search" (and none at all), every claim "held": both filed, no claim
    for g in hx["X10"]["gaps"]:
        out.append(("hostile/X10-" + g["id"], "submit", {"gid": g["id"], "gaps": [unit_rec(g)], "taken": {"L-meta-1": "someone"},
                                                        "gate_answers": {"*": "held"}}, "PR"))
    return out, hx


def main():
    if sys.argv[1:2] == ["--child"]:
        w = json.loads(sys.stdin.read())
        f = child_submit if os.environ["MD_KIND"] == "submit" else child_close
        r = f(os.environ["MD_SRC"], w)
        print("MDRESULT " + json.dumps(r))
        return 0
    src = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(HERE))
    sha = subprocess.run(["git", "-C", src, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    t = time.time()
    cs, hx = cases()
    fails, n_f3, ok_f3 = [], 0, 0
    for name, kind, w, exp in cs:
        r = spawn(kind, src, w)
        if kind == "submit":
            ok, why = judge_submit(name, w, r, exp)
        else:
            ok, why = judge_close(name, w, r, **exp)
        if name.startswith("recorded/F3-"):
            n_f3 += 1; ok_f3 += ok
            if not ok and len([f for f in fails if f.startswith("recorded/F3-")]) < 3:
                print("FAIL", name, why)
            if not ok:
                fails.append(name)
            continue
        print("ok  " if ok else "FAIL", name, why)
        if not ok:
            fails.append(name)
    print(f"recorded/F3 {ok_f3}/{n_f3} provable units of the 21:52-21:53 mint filed")
    print("SKIP hostile/X11 mirror export order (team/mirror/mirror.py) and gate stop refs: gate v1.2.1 (T11), not fork code")
    f3 = [f for f in fails if f.startswith("recorded/F3-")]
    short = [f for f in fails if not f.startswith("recorded/F3-")] + ([f"recorded/F3 ({len(f3)} of {n_f3})"] if f3 else [])
    print(f"{time.time() - t:.0f}s")
    if fails:
        print(f"PREFLIGHT FAIL {sha}: " + ", ".join(short))
        return 1
    print(f"PREFLIGHT PASS {sha}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
