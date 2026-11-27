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
TOKEN_RX_D = re.compile(r"(?<![A-Za-z0-9_-])(L-[a-z0-9]+(?:-[a-z0-9]+)*-\d+)(?![A-Za-z0-9_-])")   # the publisher's rules,
FILE_RX_D = re.compile(r"lean/PEqualNP/Outside/(L_[a-z0-9]+(?:_[a-z0-9]+)*_\d+)\.lean")              # written out here
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
    q["head"] = dict({"sha": "%040x" % (int(q.get("number") or 0) + 0xb15)}, **q["head"])   # B15: real heads carry a sha
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

    now_c = T0 + w.get("t", 0)
    CLK = [now_c]                           # the case clock; S.time.sleep advances it (retries, backoffs)
    vis = lambda p: time.mktime(time.strptime(p["created_at"][:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone <= CLK[0]
    pulls_open = sorted(w.get("open_pulls", []), key=lambda p: -p["number"])      # filtered by vis() at each read
    pulls_closed = sorted(w.get("closed_pulls", []), key=lambda p: -p["number"])
    out["reads"] = 0

    def cp(stdout="", rc=0, err=""):
        return subprocess.CompletedProcess([], rc, stdout, err)

    def gh(args, write=False, timeout=120):
        a = list(args)
        out["reads"] += 1
        if a[0] == "api" and "/pulls?" in a[1]:
            q = dict(x.split("=", 1) for x in a[1].split("?", 1)[1].split("&"))
            if "head" in q:                          # open_pr_for_branch: our own open (or closed) PR on fork branch <gid>
                h = q["head"].split(":", 1)[-1]
                src_h = pulls_open if q.get("state", "open") == "open" else pulls_closed
                return cp("".join("https://github.com/open-goat/pequalnp-proofs/pull/%d\n" % p["number"] for p in src_h
                                  if p["user"]["login"] == HANDLE and (p.get("head") or {}).get("ref") == h))
            src_l = [p for p in (pulls_open if q.get("state") == "open" else pulls_closed) if vis(p)]
            pp, pg = int(q.get("per_page", 30)), int(q.get("page", 1))
            return cp(json.dumps(src_l[(pg - 1) * pp:pg * pp]))
        m = re.search(r"/pulls/(\d+)/files", a[1]) if a[0] == "api" else None
        if m:
            if int(m.group(1)) in (w.get("files_fail") or []):
                return cp("", 1, "HTTP 403: secondary rate limit")
            p = next((x for x in pulls_open + pulls_closed if x["number"] == int(m.group(1))), {})
            return cp(json.dumps([{"filename": f} for f in p.get("files") or []]))
        if a[:2] == ["pr", "list"]:
            n = a[a.index("--search") + 1]
            res = []
            for p in [x for x in pulls_open + pulls_closed if vis(x)]:
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
        if (cmd[:3] == ["gh", "pr", "create"] or (cmd[:2] == ["gh", "api"] and "POST" in cmd and any(str(x).endswith("/pulls") for x in cmd))):
            out["creates"] = out.get("creates", 0) + 1
            if out["creates"] <= w.get("create_fail", 0):  # a0: GitHub refuses the first attempts (secondary limit)
                return cp("", 1, "HTTP 403: You have exceeded a secondary rate limit")
            body = cmd[cmd.index("--body") + 1] if "--body" in cmd else next(x[5:] for x in cmd if str(x).startswith("body="))
            out["prs"].append({"gid": gid, "lease": "Lease:" in body, "body": body})
            return cp("https://github.com/open-goat/pequalnp-proofs/pull/99999\n")
        if len(cmd) > 1 and cmd[0] == "bash" and cmd[1].endswith("checkcore.sh"):
            ps = w.get("proof_statement")
            if ps is not None:                       # the real guard compares the file with the listed statement
                g = next((x for x in gaps_now()["gaps"] if x["id"] == gid), {})
                reads[0] -= 1
                if g.get("statement") and g["statement"] != ps:
                    return cp("FAIL: statement differs from gaps.json\n", 1)
            return cp("guards ok\n")
        if w.get("gate_refs") is not None and cmd[0] == "git" and "ls-remote" in cmd and any("deskgate" in x for x in cmd):
            if w["gate_refs"] == "fail":                       # Y2: the toolkit refs cannot be read
                return cp("", 128, "fatal: unable to access")
            return cp("".join(f"0\t{r}\n" for r in w["gate_refs"]))
        if "taken_text" in w and cmd[0] == "git":            # the real _taken_list: init, fetch, show of status/taken
            if "init" in cmd or "fetch" in cmd:
                return cp()
            if "show" in cmd and cmd[-1].endswith(":taken.txt"):
                return cp(w["taken_text"].replace("{T}", str(int(T0) - 20)))
        out["unexpected"].append("run " + " ".join(cmd[:3]))
        return cp(rc=1, err="unexpected")
    S.run = run

    tl = w.get("taken", {})
    if "taken_text" not in w:
        def fake_taken():
            if tl is None:
                return None
            hdr = int(now_c) - 20
            if hasattr(S, "TL_HDR"):
                S.TL_HDR[0] = hdr
            if hasattr(S, "TL_COMPLETE"):
                S.TL_COMPLETE[0] = True
            rows = {}
            for p in sorted(pulls_open + pulls_closed, key=lambda p: -p["number"]):
                if time.mktime(time.strptime(p["created_at"][:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone >= hdr:
                    continue
                us = set(TOKEN_RX_D.findall(p.get("title") or "")) | \
                    set(TOKEN_RX_D.findall((p.get("head") or {}).get("ref", "").replace("_", "-")))
                if not p.get("closed_at"):
                    us |= {m.group(1).replace("_", "-") for m in map(FILE_RX_D.fullmatch, p.get("files") or []) if m}
                for u in us:
                    rows[u] = p["user"]["login"]
            rows.update(tl)
            return rows
        S._taken_list = fake_taken
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
    if hasattr(S, "fork_head"):              # fork branches of ours that exist already (W6 create-only head)
        S.fork_head = lambda g: (w.get("fork_heads") or {}).get(g)
    if hasattr(S, "gate_answer_lease"):
        S.gate_answer_lease = lambda g: (w.get("gate_answers_ref") or {}).get(g)
    out["li_reads"] = 0

    def fake_li():                          # config/linkedin.txt in the toolkit (Lead 05:50): None = unreadable
        out["li_reads"] += 1
        return w.get("li_file") or ""
    S.li_from_toolkit = fake_li
    S.release = lambda lid, why: out["desk"].append("release " + str(lid)) if lid else None
    S.time.sleep = lambda s: CLK.__setitem__(0, CLK[0] + s)
    S.time.time = lambda: CLK[0]            # the fixtures' clock (created_at of the pulls is relative to T0)

    def gate_open_now():
        gj = S.LAST_GJ[0] or {}
        if any((p.get("handle") if isinstance(p, dict) else p) == HANDLE for p in gj.get("paused") or []):
            return False, "paused in the mirror"
        return (True, "open ref") if w.get("gate_open", True) else (False, "no open ref")
    if w.get("gate_refs") is None:                # else the real gate_open_now reads the (fake) toolkit refs
        S.gate_open_now = gate_open_now

    def gate_claim(g):
        out["desk"].append("claim " + g)
        ans = (w.get("gate_answers") or {}).get(g) or (w.get("gate_answers") or {}).get("*", "ok")
        return (ans, "lease-x1") if ans == "ok" else (ans, None)
    S.gate_claim = gate_claim
    if hasattr(S, "filing_halted"):          # halt_at: a stop ref appears at that case time (seconds after T0 + t)
        S.filing_halted = lambda: ((True, "filing halted (drill)") if w.get("halted") or
                                   (w.get("halt_at") is not None and CLK[0] >= now_c + w["halt_at"]) else (False, ""))
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
class Die(BaseException):
    """B10: the dupclose process dies at a step boundary (not an Exception, so no handler in the code swallows it)."""


def child_close(src, w):
    sys.path.insert(0, os.path.join(src, ".github", "cloud-pr"))
    sys.path.append(HERE)                  # haltrule.py of the drill (judge) when src has none
    clock = [T0]
    real_time = time.time
    import importlib
    import dupclose as D
    D.time.time = lambda: clock[0]
    D.time.sleep = lambda s: None
    out = {"closed": [], "pushes": [], "unexpected": [], "deaths": 0, "restarts": 0}
    DIE = {"left": 1 if w.get("die_stop") else 0}
    GHOST = {"left": w.get("stop_push_ghost", 0)}
    PASS = [0]
    PUSHED = {}                            # ref -> commit sha (pushed by the code under test)
    FIXREFS = [r if isinstance(r, str) else r["ref"] for r in w.get("toolkit_refs", [])]
    FIXSHA = {r["ref"]: "f%039d" % i for i, r in enumerate(w.get("toolkit_refs", [])) if not isinstance(r, str)}
    FIXMSG = {FIXSHA[r["ref"]]: r.get("msg", "") for r in w.get("toolkit_refs", []) if not isinstance(r, str)}
    FIXBORN = {r["ref"]: T0 + r["born"] for r in w.get("toolkit_refs", []) if not isinstance(r, str) and "born" in r}

    def live_refs():                       # toolkit refs that exist now (fixture refs from their birth, pushed refs)
        b = lambda r: FIXBORN[r] if r in FIXBORN else (int(re.search(r"/(\d+)$", r).group(1)) if re.search(r"/(\d{9,})$", r) else 0)
        return [r for r in FIXREFS if b(r) <= clock[0]] + list(PUSHED)

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
    def counted_page(k):
        out["open_reads"] = out.get("open_reads", 0) + 1
        return page(k)
    D._page = counted_page

    def cmts(p):                          # Y3: a comment exists from its created_at on
        return [c for c in p.get("comments", []) if not c.get("created_at") or tt(c["created_at"]) <= clock[0]]

    def updated(p):
        return max([tt(p["closed_at"]) or 0] + [tt(c["created_at"]) for c in cmts(p) if c.get("created_at")])

    FORKB = {}                            # 16.5 rule 4: fork head branches <ID> -> sha (each of our PRs' head, newest wins)
    for p in sorted(allp, key=lambda p: p["number"]):
        if p["user"]["login"] == HANDLE and (p.get("head") or {}).get("sha"):
            FORKB[p["head"]["ref"]] = p["head"]["sha"]
    FORKB.update(w.get("fork_branches", {}))
    out["deleted"] = []

    def sh(*a, timeout=120, env=None):
        a = list(a)
        s = " ".join(a)
        if a[0] == "git" and "pequalnp-proofs-fork" in s and "ls-remote" in a:
            ref = a[-1].replace("refs/heads/", "")
            return subprocess.CompletedProcess(a, 0, f"{FORKB[ref]}\trefs/heads/{ref}\n" if ref in FORKB else "", "")
        if a[0] == "git" and "pequalnp-proofs-fork" in s and "push" in a:
            ref = a[-1].split(":refs/heads/", 1)[1]
            lease = next((x.split(":", 1)[1] for x in a if x.startswith("--force-with-lease=")), None)
            if not a[-1].startswith(":") or lease is None or FORKB.get(ref) != lease:
                return subprocess.CompletedProcess(a, 1, "", "! [rejected] (stale info)")
            FORKB.pop(ref)
            out["deleted"].append(ref)
            for p in allp:                     # GitHub closes an open PR whose head branch is deleted
                if (p.get("head") or {}).get("ref") == ref and not state_at(p).get("closed_at"):
                    out.setdefault("closed_by_delete", []).append(p["number"])
            return subprocess.CompletedProcess(a, 0, "", "")
        if a[0] == "gh" and "state=all&head=" in s:
            ref = re.search(r"head=Leg0shii:([^&\s]+)", s).group(1)
            rc = w.get("race_create", {}).get(ref)
            if rc and ref not in out.setdefault("raced", []):   # an opener pushes + creates right after our read
                out["raced"].append(ref)
                res = [state_at(p) for p in allp if visible(p) and (p.get("head") or {}).get("ref") == ref]
                FORKB[ref] = rc["sha"]
                allp.append(dict(our_pr(rc["n"], ref, created=0), head={"ref": ref, "sha": rc["sha"],
                                 "repo": {"full_name": "Leg0shii/pequalnp-proofs-fork"}}, created_at=iso(clock[0])))
                return subprocess.CompletedProcess(a, 0, json.dumps(res), "")
            res = [state_at(p) for p in allp if visible(p) and (p.get("head") or {}).get("ref") == ref]
            return subprocess.CompletedProcess(a, 0, json.dumps(res), "")
        if a[0] == "gh" and "state=closed" in s:
            out["closed_reads"] = out.get("closed_reads", 0) + 1
            if PASS[0] in w.get("closed_fail_passes", []):
                return subprocess.CompletedProcess(a, 1, "", "HTTP 502")
            cur = [state_at(p) for p in allp if visible(p)]
            cur = sorted([dict(p, updated_at=iso(updated(p))) for p in cur if p.get("closed_at")], key=lambda p: -tt(p["updated_at"]))
            k = int((re.search(r"[?&]page=(\d+)", s) or [0, 1])[1])            # Y4: real pagination
            return subprocess.CompletedProcess(a, 0, json.dumps(cur[(k - 1) * 100:k * 100]), "")
        if a[0] == "gh" and "/comments" in s:
            out["comment_reads"] = out.get("comment_reads", 0) + 1
            n = int(re.search(r"issues/(\d+)/comments", s).group(1))
            p = next((x for x in allp if x["number"] == n), {})
            return subprocess.CompletedProcess(a, 0, json.dumps(cmts(p)), "")
        if a[0] == "gh" and re.search(r"issues/(\d+)(\s|$)", s):              # Y5: closed_by from the issues API
            out["issue_reads"] = out.get("issue_reads", 0) + 1
            n = int(re.search(r"issues/(\d+)", s).group(1))
            p = next((x for x in allp if x["number"] == n), {})
            by = HANDLE if n in out["closed"] else p.get("closed_by")
            if "--jq" in a:
                return subprocess.CompletedProcess(a, 0, (by or "") + "\n", "")
            return subprocess.CompletedProcess(a, 0, json.dumps({"number": n, "closed_by": {"login": by} if by else None}), "")
        if a[0] == "gh" and a[1:3] == ["pr", "close"]:
            n = int(a[3])
            if n not in out["closed"]:
                out["closed"].append(n)
            else:
                out.setdefault("reclosed", []).append(n)
            if n in w.get("close_timeout", []):                              # B9: the close happened, the call timed out
                return subprocess.CompletedProcess(a, 1, "", "timeout")
            return subprocess.CompletedProcess(a, 0, "", "")
        if a[0] == "gh" and "rate_limit" in s:
            return subprocess.CompletedProcess(a, 0, "5000", "")
        if a[0] == "git" and "push" in a:
            sha, ref = a[-1].split(":", 1) if ":" in a[-1] else ("0", a[-1])
            if "filing/stop/" in ref and out.setdefault("stop_fails", 0) < w.get("stop_push_fail", 0):
                out["stop_fails"] += 1                                       # Y6: the stop push fails
                return subprocess.CompletedProcess(a, 1, "", "remote rejected")
            if "filing/stop/" in ref and DIE["left"] and w.get("die_stop") == "before":
                DIE["left"] = 0; raise Die("killed before the stop push")
            if ref in live_refs() and "-f" not in a:                          # Y7c: a ref name that exists is refused
                out.setdefault("push_collisions", []).append(ref)
                return subprocess.CompletedProcess(a, 1, "", "! [rejected] (already exists)")
            out["pushes"].append(ref); PUSHED[ref] = sha
            if "filing/stop/" in ref:
                g = a[a.index("-C") + 1] if "-C" in a else None
                out.setdefault("stop_msgs", []).append(subprocess.run(["git", "-C", g, "log", "-1", "--format=%B", sha],
                                                                      capture_output=True, text=True).stdout.strip() if g else "?")
                if DIE["left"] and w.get("die_stop") == "after":
                    DIE["left"] = 0; raise Die("killed after the stop push")
                if GHOST["left"]:                                            # B9: the push landed, the answer was an error
                    GHOST["left"] -= 1
                    return subprocess.CompletedProcess(a, 1, "", "unexpected disconnect")
            return subprocess.CompletedProcess(a, 0, "", "")
        if a[0] == "git" and "fetch" in a and "status/taken" in s and "taken_hdr_age" in w:      # TAKEN-STALE drill
            ok = w["taken_hdr_age"] is not None
            return subprocess.CompletedProcess(a, 0 if ok else 1, "", "" if ok else "fatal: couldn't find remote ref")
        if a[0] == "git" and "show" in a and "open.json" in s:              # 16.7: takenpub's open list (W6 format + lease, ref)
            oj = w.get("open_json")
            if not oj or PASS[0] in oj.get("missing_passes", []):
                return subprocess.CompletedProcess(a, 128, "", "fatal: path 'open.json' does not exist")
            cur = [state_at(p) for p in allp if visible(p)]
            rows = [[p["number"], p["user"]["login"], (p.get("head") or {}).get("sha", ""), int(tt(p["created_at"])),
                     sorted({u for u in [D.title_unit(p.get("title"))] if u}), int(bool(re.search(r"(?m)^Lease:\s*\S", p.get("body") or ""))),
                     (p.get("head") or {}).get("ref", "")][:oj.get("width", 7)] for p in cur if not p.get("closed_at")]
            return subprocess.CompletedProcess(a, 0, json.dumps({"t": int(clock[0] - oj.get("age", 10)),
                                                                 "full_t": int(clock[0] - oj.get("full_age", 100)), "prs": rows}), "")
        if a[0] == "git" and "fetch" in a and "status/taken" in s and "open_json" in w and "taken_hdr_age" not in w:
            return subprocess.CompletedProcess(a, 0, "", "")
        if a[0] == "git" and "show" in a and "status/taken" in s and "taken_hdr_age" in w:
            tail = {"complete": " complete 0 rl 5000 0", "partial": " partial %d rl 5000 0" % int(clock[0] - 50), "old": ""}[w.get("taken_hdr_state", "complete")]
            return subprocess.CompletedProcess(a, 0, f"# updated {int(clock[0] - w['taken_hdr_age'])} 05:00:00 steps 0{tail}\n", "")
        if a[0] == "git" and "ls-remote" in a and PASS[0] in w.get("tk_lsremote_fail_passes", []):
            return subprocess.CompletedProcess(a, 128, "", "fatal: unable to access")   # 16.8 S1: toolkit refs unreadable
        if a[0] == "git" and "ls-remote" in a:                  # fixture refs ("ref" or {"ref", "msg"}) + what was pushed
            pats = [x.split("*")[0] for x in a if x.startswith("refs/")]
            born = lambda r: FIXBORN[r] if r in FIXBORN else (int(re.search(r"/(\d+)$", r).group(1)) if re.search(r"/(\d{9,})$", r) else 0)
            rows = [(FIXSHA.get(r, "0"), r) for r in FIXREFS if born(r) <= clock[0]] + [(v, k) for k, v in PUSHED.items()]
            return subprocess.CompletedProcess(a, 0, "".join(f"{h}\t{r}\n" for h, r in rows if any(r.startswith(x) for x in pats)), "")
        if a[0] == "git" and "fetch" in a and any("filing/stop/" in x for x in a):      # Y4j: a stop ref's commit
            return subprocess.CompletedProcess(a, 1 if w.get("unreadable_stops") else 0, "", "fetch failed" if w.get("unreadable_stops") else "")
        if a[0] == "git" and "log" in a:
            h = a[-1]
            if h in FIXMSG:
                return subprocess.CompletedProcess(a, 1 if w.get("unreadable_stops") else 0, "" if w.get("unreadable_stops") else FIXMSG[h] + "\n", "")
            if w.get("unreadable_stops"):
                return subprocess.CompletedProcess(a, 128, "", "bad object")
            return subprocess.run(a, capture_output=True, text=True)
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
    def patch(D):
        D._page = counted_page
        D.sh = sh
        D.auth = lambda: []
        if "taken_hdr_age" not in w:
            D.taken = lambda: w.get("taken_map")
        D.DRY = False
    for k in ("FIXTURE", "FIXTURE_OPEN", "FIXTURE_MERGED", "FIXTURE_CLOSED", "FIXTURE_FILING"):
        os.environ.pop(k, None)
    patch(D)
    dead = False
    for i, t in enumerate(w["passes"]):
        PASS[0] = i
        clock[0] = T0 + t
        if dead or i in w.get("restart_at", []):        # B10/B11: a new process (chain restart): all module state fresh
            D = importlib.reload(D); patch(D); out["restarts"] += 1; dead = False
        D.REJ["t"] = 0
        try:
            D.one_pass()
        except Die:
            out["deaths"] += 1; dead = True
        except Exception as e:
            out["unexpected"].append("one_pass: " + repr(e)[:120])
    if "taken_hdr_age" in w:
        out["taken_ok"] = D.taken() is not None
    out["caches"] = {k: len(getattr(D, k)) for k in ("CMT", "CLOSER", "MERGED", "MSGS", "HALTED", "CLOSED") if hasattr(D, k)}
    out["closed_at"] = {}
    import haltrule                        # Lead 16.1: the drill judges with the one rule (tie halted, odd names halted)
    out["halted"] = haltrule.verdict("".join(f"0\t{r}\n" for r in live_refs()))[0]
    try:
        out["self_halted"] = D.halted_now()   # what the closer itself believes from the same refs
    except Exception as e:
        out["self_halted"] = "crash " + repr(e)[:60]
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
    for k in ("PNP_LINKEDIN", "CLAIM_FIRST", "FILE_FIRST"):
        env.pop(k, None)
    env.update(w.get("env") or {})
    if w.get("snap"):                                # one drain: every worker shares the rival snapshot directory
        os.makedirs(w["snap"], exist_ok=True)
        env["RIVAL_SNAP_DIR"] = w["snap"]
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
    if r["prs"] and rv and expect != "no PR or closed":
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
    if w.get("body_expect") is not None:
        bad += body_bad(r["prs"], w["body_expect"])
    if w.get("expect_claim") is not None and any(x.startswith("claim") for x in r["desk"]) != w["expect_claim"]:
        bad.append(f"Y2 desk claims {r['desk']} (want {'a claim' if w['expect_claim'] else 'none'})")
    if w.get("li_reads") is not None and r.get("li_reads") != w["li_reads"]:
        bad.append(f"credit file read {r.get('li_reads')} times (want {w['li_reads']})")
    return (not bad), "; ".join(bad) or f"{got} ({r['result']}: {r['why'][:70]})"


# PR body as the makers' template wants it (Lead 05:27, owner ask 05:22). Written out here, not imported, so a change
# of submit.py's constants fails the drill.
B_DESC = "Proof written by an AI worker."
B_FOOT = "\n\n\U0001F916 Generated with [Claude Code](https://claude.com/claude-code)"
B_LI = "https://www.linkedin.com/in/drill-placeholder/"          # placeholder, not anyone's address


def body_bad(prs, ex):
    """ex = {"li": bool, "lease": lease id or None}: exact body, one Lease line at most, footer last."""
    if len(prs) != 1:
        return [f"body: {len(prs)} PRs"]
    b, bad = prs[0]["body"], []
    want = B_DESC + (f"\n\n**LinkedIn profile**: {B_LI}" if ex["li"] else "") + \
        (f"\n\nLease: {ex['lease']}" if ex["lease"] else "") + B_FOOT
    if b != want:
        bad.append("body differs: " + repr(b[:140]))
    if b.count("Lease:") != (1 if ex["lease"] else 0):
        bad.append(f"{b.count('Lease:')} Lease lines")
    if not b.endswith(B_FOOT):
        bad.append("footer not last")
    if b.count("linkedin.com") != (1 if ex["li"] else 0):
        bad.append(f"{b.count('linkedin.com')} credit lines")
    return bad


def judge_close(name, w, r, must_close, must_keep=(), must_push=None, no_push=False, max_reads=None, go_count=None, last_stop=None, halted=None, stop_count=None, cache_max=None, self_halted=None, must_delete=None, keep_branch=(), push_count=None, max_open_reads=None, max_reads_all=None, taken_ok=None):
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
    if stop_count is not None:
        ns = sum(1 for p in r["pushes"] if "filing/stop/" in p)
        if ns != stop_count:
            bad.append(f"{ns} filing/stop pushes (want {stop_count})")
    if cache_max:
        big = {k: v for k, v in (r.get("caches") or {}).items() if v > cache_max.get(k, 10 ** 9)}
        if big:
            bad.append(f"caches over cap {big}")
    if halted is not None and r.get("halted") != halted:
        bad.append("filing " + ("NOT halted" if halted else "still halted") + " at the end")
    if taken_ok is not None and r.get("taken_ok") != taken_ok:
        bad.append(f"taken() {'gave no list' if taken_ok else 'trusted a list it must not'}")
    if max_open_reads is not None and r.get("open_reads", 0) > max_open_reads:
        bad.append(f"{r.get('open_reads', 0)} open-list page reads (cap {max_open_reads})")
    if max_reads_all is not None:
        tot = r.get("open_reads", 0) + r.get("closed_reads", 0) + r.get("comment_reads", 0) + r.get("issue_reads", 0)
        if tot > max_reads_all:
            bad.append(f"{tot} GitHub reads in all (cap {max_reads_all})")
    for pre, want in (push_count or {}).items():
        got = sum(1 for p in r["pushes"] if p.startswith(pre))
        if got != want:
            bad.append(f"{got} pushes of {pre} (want {want})")
    if must_delete is not None and sorted(r.get("deleted") or []) != sorted(must_delete):
        bad.append(f"deleted branches {r.get('deleted')} (want {must_delete})")
    kb = [b for b in keep_branch if b in (r.get("deleted") or [])]
    if kb:
        bad.append(f"deleted a kept branch {kb}")
    if r.get("closed_by_delete"):
        bad.append(f"a branch delete closed open PR(s) {r['closed_by_delete']}")
    if self_halted is not None and r.get("self_halted") != self_halted:
        bad.append(f"closer halted_now() = {r.get('self_halted')} (want {self_halted})")
    if r.get("push_collisions"):
        bad.append(f"push to an existing ref {r['push_collisions'][:2]}")
    if go_count is not None:
        ng = sum(1 for p in r["pushes"] if "filing/go/" in p)
        if ng != go_count:
            bad.append(f"{ng} filing/go pushes (want {go_count})")
    if last_stop is not None:
        sm = r.get("stop_msgs") or [""]
        if last_stop not in sm[-1]:
            bad.append(f"newest stop {sm[-1][:60]!r}, want {last_stop!r}")
    if max_reads is not None:
        nr = r.get("closed_reads", 0) + r.get("comment_reads", 0) + r.get("issue_reads", 0)
        if nr > max_reads:
            bad.append(f"{nr} GitHub reads (cap {max_reads})")
    reads = "" if "closed_reads" not in r else f" reads={r.get('closed_reads', 0)}+{r.get('comment_reads', 0)}+{r.get('issue_reads', 0)} open={r.get('open_reads', 0)}"
    gos = sum(1 for p in r["pushes"] if "filing/go/" in p)
    reads += "" if not r.get("caches") or not cache_max else " caches=" + ",".join(f"{k}:{v}" for k, v in r["caches"].items())
    return (not bad), "; ".join(bad) or f"closed {sorted(r['closed'])}" + (" halt" if any("filing/stop" in p for p in r["pushes"]) else "") + (f" go={gos}" if gos else "") + reads


def unit(gid, tpl="tl6c-not-search", **k):
    return unit_rec(dict({"id": gid, "faithful_by_template": {"template": tpl}, "offerable_now": True}, **k))


def our_pr(n, gid, lease=False, created=-300, title=None):
    return {"number": n, "title": title or gid, "user": {"login": HANDLE}, "head": {"ref": gid, "sha": "%040x" % n,
                                                                              "repo": {"full_name": "Leg0shii/pequalnp-proofs-fork"}}, "files": [],
            "body": "desc" + ("\n\nLease: lid-%d" % n if lease else ""), "created_at": iso(T0 + created),
            "merged_at": None, "closed_at": None}


def rival_pr(n, title, created=-100, merged=None, closed=None, login="rival1", files=(), ref="patch-1"):
    return {"number": n, "title": title, "user": {"login": login}, "head": {"ref": ref, "sha": "%040x" % n}, "files": list(files), "body": "",
            "created_at": iso(T0 + created), "merged_at": iso(T0 + merged) if merged is not None else None,
            "closed_at": iso(T0 + (closed if closed is not None else merged)) if (closed is not None or merged is not None) else None}


def upstream_world(t_end, new_every=30, base=60000):
    """81 open PRs as upstream at 05:40 27 Nov (41 with no unit id in title or branch, files of other units), all older
    than the mint, plus one new no-id rival PR every new_every s during the mint (they need file reads)."""
    ws = [rival_pr(base + i, "Prove L-meta-%d" % (70000 + i), created=-7200 + i, login="r%d" % (i % 7),
                   files=["lean/PEqualNP/Outside/L_meta_%d.lean" % (70000 + i)]) for i in range(40)]
    ws += [rival_pr(base + 40 + i, "Batch %d of circuit proofs" % i, created=-7000 + i, login="b%d" % (i % 5),
                    files=["lean/PEqualNP/Outside/L_meta_%d.lean" % (71000 + i)]) for i in range(41)]
    ws += [rival_pr(base + 200 + j, "more proofs %d" % j, created=j * new_every, login="late%d" % j,
                    files=["lean/PEqualNP/Outside/L_meta_%d.lean" % (72000 + j)]) for j in range(int(t_end // new_every) + 1)]
    return ws


SNAPS = tempfile.mkdtemp(prefix="mintdrill-snap-")


def cases():
    rec = json.load(open(os.path.join(DATA, "recorded.json")))
    out = []
    # F3: the held mint. Every provable unit free at first sight must get our PR, no claim.
    # A19: the upstream world of 05:40 (81 open PRs, 41 without an id) and one drain: units 3 s apart, one snapshot dir
    f3u = [x for x in rec["f3_units"] if x["meet"]]
    wf3 = upstream_world(3 * len(f3u))
    gf3 = [unit(u["id"], u["template"]) for u in f3u]          # one export for the whole drain (B2 shares it)
    for i, u in enumerate(f3u):
        w = {"gid": u["id"], "gaps": gf3, "taken": {"L-meta-1": "someone"}, "gate_open": True,
             "gate_answers": {"*": rec["f3_gate_answer"]}, "open_pulls": wf3, "t": 3 * i, "snap": SNAPS + "/f3"}
        out.append(("recorded/F3-" + u["id"], "submit", w, "PR"))
    # A19 budget: a 400-unit mint drained at 20 units a minute against the same world; every unit free
    w400 = upstream_world(3 * 400, base=80000)
    g400 = [unit("L-meta-%d" % (93000 + i)) for i in range(400)]
    for i in range(400):
        g = "L-meta-%d" % (93000 + i)
        out.append(("budget/M400-" + g, "submit", {"gid": g, "gaps": g400, "taken": {"L-meta-1": "someone"},
                                                    "open_pulls": w400, "t": 3 * i, "snap": SNAPS + "/m400"}, "PR"))
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
            w["env"] = {"GAPS_MAX_AGE_S": "0"}       # B2: the shared copy expired between the reads
        if k == "X8":
            w["proof_statement"] = x["proof_statement"]
        if k == "X3b":                               # Lead 05:32 A20: "steps 0" is legitimate; the closer half decides
            w.pop("taken"); w["taken_text"] = "# updated {T} 05:00:00 steps 0 complete 0 rl 4000 0\n"
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
    # B15 (fakedrift): real PRs can have body null. A rival's open PR on our unit with body null: no PR from us, and the
    # closer still closes our later PR on that unit (it reads body for the Lease line)
    rb = rival_pr(50201, "Prove L-meta-90201", created=-60); rb["body"] = None
    out.append(("hostile/B15-body-null", "submit", {"gid": "L-meta-90201", "gaps": [unit("L-meta-90201")], "taken": {"L-meta-1": "someone"},
                                                     "open_pulls": [rb]}, "no PR"))
    rb2 = dict(rb, merged_at=iso(T0 - 30), closed_at=iso(T0 - 30))
    out.append(("hostile/B15-body-null-close", "close", {"open_pulls": [our_pr(50202, "L-meta-90201", created=-20)],
                                                          "closed_pulls": [rb2], "passes": [0, 30]}, {"must_close": [50202]}))
    # X9: makers close ours with a text that is not "proved first": halt
    x = hx["X9"]["ours_closed"][0]
    c = our_pr(x["number"], x["gid"], created=-900)
    c.update(closed_at=iso(T0 - 20), comments=[{"body": x["comment"], "user": {"login": x["by"]}}])
    out.append(("hostile/X9", "close", {"closed_pulls": [c], "passes": [0]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # Y3-Y6 (red team V3/V4, team/redteam/CHANNELS.md): the halt detector in dupclose.rej_burst / filing_stop
    def ours_closed(n, gid, closed, by=None, comments=()):
        c = our_pr(n, gid, created=closed - 900)
        c.update(closed_at=iso(T0 + closed), comments=[dict(x, created_at=iso(T0 + x["at"])) for x in comments])
        if by:
            c["closed_by"] = by
        return c
    pf = [{"body": "Closed: this unit was proved first by another PR.", "user": {"login": "makers-bot"}, "at": 4}]
    # Y3: closed at T, checker comment at T+4 s, passes at T+1 s and T+61 s -> halt by the second pass
    out.append(("hostile/Y3", "close", {"closed_pulls": [ours_closed(50100, "L-meta-93001", 0, by="makers-bot", comments=pf)],
                                        "passes": [1, 61]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # Y3b: the same, but the issues API gives no closer: only the late comment can show it
    out.append(("hostile/Y3b", "close", {"closed_pulls": [ours_closed(50101, "L-meta-93002", 0, comments=pf)],
                                         "passes": [1, 61]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # Y4: ours rejected at T-300 s, then 120 other closes/merges up to T-10 s -> our rejection is on page 2, still found
    many = [rival_pr(51000 + i, "Prove L-meta-%d" % (94000 + i), created=-900, merged=-290 + 2 * i) for i in range(120)]
    rj = ours_closed(50102, "L-meta-93003", -300, by="makers-bot", comments=[{"body": "REJECTED", "user": {"login": "makers-bot"}, "at": -299}])
    out.append(("hostile/Y4", "close", {"closed_pulls": [rj] + many, "passes": [0]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # Y4b: 120 closes in the window and no rejection of ours: no halt, and a bounded number of reads
    out.append(("hostile/Y4b", "close", {"closed_pulls": many, "passes": [0, 60]}, {"must_close": [], "no_push": True, "max_reads": 8}))
    # Y4c: 1,100 closes in 10 min (more than 10 pages): the detector cannot see the window -> fail closed (halt)
    huge = [rival_pr(60000 + i, "Prove L-meta-%d" % (95000 + i), created=-900, merged=-550 + i // 2) for i in range(1100)]
    out.append(("hostile/Y4c", "close", {"closed_pulls": huge, "passes": [0]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # Y4d: one failed read of the closed list is retried, not a halt; three failed passes in a row halt
    out.append(("hostile/Y4d", "close", {"closed_pulls": many[:5], "closed_fail_passes": [0], "passes": [0, 60]},
                {"must_close": [], "no_push": True}))
    out.append(("hostile/Y4e", "close", {"closed_pulls": many[:5], "closed_fail_passes": [0, 1, 2], "passes": [0, 60, 120]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # Y4f: read cost in a mint: 300 rival closes/merges in 10 min plus 30 of ours closed by us -> bounded reads
    m300 = [rival_pr(70000 + i, "Prove L-meta-%d" % (96000 + i), created=-900, merged=-590 + 2 * i) for i in range(300)]
    o30 = [ours_closed(52000 + i, "L-meta-%d" % (97000 + i), -400 + 10 * i, by=HANDLE) for i in range(30)]
    out.append(("hostile/Y4f", "close", {"closed_pulls": m300 + o30, "passes": [0, 60]}, {"must_close": [], "no_push": True, "max_reads": 50}))
    # Y4g-j (Lead 05:50): blind halts lift themselves after two clean full scans; rejection halts never do
    five = many[:5]
    out.append(("hostile/Y4g", "close", {"closed_pulls": five, "closed_fail_passes": [0, 1, 2], "passes": [0, 60, 120, 180, 240, 300, 360]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/", "go_count": 1}))
    rj_old = ours_closed(50105, "L-meta-93006", -590, by="makers-bot", comments=[{"body": "REJECTED", "user": {"login": "makers-bot"}, "at": -589}])
    out.append(("hostile/Y4h", "close", {"closed_pulls": five + [rj_old], "passes": [0, 60, 120, 180]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/", "go_count": 0, "last_stop": "filing stop: REJ-HALT"}))
    rj_new = ours_closed(50106, "L-meta-93007", 200, by="makers-bot", comments=[{"body": "REJECTED", "user": {"login": "makers-bot"}, "at": 201}])
    out.append(("hostile/Y4i", "close", {"closed_pulls": five + [rj_new], "closed_fail_passes": [0, 1, 2], "passes": [0, 60, 120, 180, 240, 300, 360]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/", "go_count": 0, "last_stop": "filing stop: REJ-HALT"}))
    out.append(("hostile/Y4j", "close", {"closed_pulls": five, "closed_fail_passes": [0, 1, 2], "passes": [0, 60, 120, 180, 240, 300],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/stop/%d" % (T0 + 130), "msg": "filing stop: Lead by hand"}]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/", "go_count": 0}))
    # Y4k (Lead 05:58): REJ-HALT at T, blind condition at T+900 s, clean scans from T+1100 s -> no go, REJ-HALT stays newest
    rj_k = ours_closed(50107, "L-meta-93008", -30, by="makers-bot", comments=[{"body": "REJECTED", "user": {"login": "makers-bot"}, "at": -29}])
    out.append(("hostile/Y4k", "close", {"closed_pulls": five + [rj_k], "closed_fail_passes": [2, 3, 4],
                                         "passes": [0, 60, 900, 960, 1020, 1100, 1160, 1220, 1280]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/", "go_count": 0, "last_stop": "filing stop: REJ-HALT"}))
    out.append(("hostile/Y4j2", "close", {"closed_pulls": five, "closed_fail_passes": [0, 1, 2], "passes": [0, 60, 120, 180, 240, 300],
                                          "unreadable_stops": True}, {"must_close": [], "must_push": "refs/heads/filing/stop/", "go_count": 0}))
    # Y7 (red team V5, Lead 06:02): stop/go order without trusting clocks
    rj7 = lambda n, at: ours_closed(n, "L-meta-%d" % (93100 + n % 100), at, by="makers-bot",
                                    comments=[{"body": "REJECTED", "user": {"login": "makers-bot"}, "at": at + 1}])
    out.append(("hostile/Y7a", "close", {"closed_pulls": five + [rj7(50110, -10)], "passes": [0],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/go/%d" % (T0 + 600), "msg": "filing go: fast clock", "born": -5}]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/", "halted": True}))
    out.append(("hostile/Y7b", "close", {"closed_pulls": five + [rj7(50111, -120)], "passes": [0, 60],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/stop/%d" % (T0 + 600), "msg": "filing stop: REJ-HALT 1 50111", "born": -100},
                                                          {"ref": "refs/heads/filing/go/%d" % (T0 + 601), "msg": "filing go: Lead", "born": 30}]},
                {"must_close": [], "no_push": True, "halted": False}))
    out.append(("hostile/Y7c", "close", {"closed_pulls": five + [rj7(50112, -5)], "passes": [0],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/stop/%d" % T0, "msg": "filing stop: REJ-HALT 1 49999", "born": -1}]},
                {"must_close": [], "must_push": "refs/heads/filing/stop/", "halted": True, "last_stop": "50112"}))
    # Y7d (Lead 06:12): 30 rejections -> one stop naming all 30; restart; the Lead's go -> no second halt
    r30 = [rj7(50200 + i, -100 + i) for i in range(30)]
    out.append(("hostile/Y7d", "close", {"closed_pulls": five + r30, "passes": [0, 60, 120], "restart_at": [1],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/go/%d" % (T0 + 40), "msg": "filing go: Lead", "born": 30}]},
                {"must_close": [], "stop_count": 1, "halted": False}))
    # 16.1 (Lead 06:22): one rule. R6 (red team): stop == go from one snapshot stays halted
    out.append(("hostile/R6a", "close", {"closed_pulls": five, "passes": [0, 60],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/stop/%d" % (T0 - 100), "msg": "filing stop: REJ-HALT 1 49998", "born": -100},
                                                          {"ref": "refs/heads/filing/go/%d" % (T0 - 100), "msg": "filing go: Lead", "born": -90}]},
                {"must_close": [], "no_push": True, "go_count": 0, "halted": True, "self_halted": True}))
    # R6b: a blind stop of ours tied with a go: halted, so two clean scans lift it with go = stop + 1
    out.append(("hostile/R6b", "close", {"closed_pulls": five, "passes": [0, 60, 120, 180],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/stop/%d" % (T0 - 100), "msg": "filing stop: BLIND closed-read go=0", "born": -100},
                                                          {"ref": "refs/heads/filing/go/%d" % (T0 - 100), "msg": "filing go: other writer", "born": -90}]},
                {"must_close": [], "no_push": True, "go_count": 1, "halted": False, "self_halted": False}))
    # R6c: tie + a blind scan: already halted, so no blind stop on top of it
    out.append(("hostile/R6c", "close", {"closed_pulls": five, "closed_fail_passes": [0, 1, 2], "passes": [0, 60, 120],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/stop/%d" % (T0 - 100), "msg": "filing stop: REJ-HALT 1 49997", "born": -100},
                                                          {"ref": "refs/heads/filing/go/%d" % (T0 - 100), "msg": "filing go: Lead", "born": -90}]},
                {"must_close": [], "no_push": True, "go_count": 0, "halted": True, "self_halted": True}))
    # R7: a stop named <n>-blind (not plain digits) newer go: halted until deleted; never lifted by the closer
    for nm, extra in (("R7a", {}), ("R7b", {"closed_fail_passes": [0, 1, 2]})):
        out.append(("hostile/" + nm, "close", dict({"closed_pulls": five, "passes": [0, 60, 120, 180, 240],
                                                    "toolkit_refs": [{"ref": "refs/heads/filing/stop/%d-blind" % (T0 - 100), "msg": "filing stop: BLIND closed-read go=0", "born": -100},
                                                                     {"ref": "refs/heads/filing/go/%d" % (T0 - 50), "msg": "filing go: Lead", "born": -50}]}, **extra),
                    {"must_close": [], "no_push": True, "go_count": 0, "halted": True, "self_halted": True}))
    # 16.5 rule 4 + 16.8 O3/O7 (Lead 06:26): head branch <ID> deleted only when MERGED or closed BY US, never while open
    mg = our_pr(50400, "L-meta-93400", created=-900); mg.update(merged_at=iso(T0 - 100), closed_at=iso(T0 - 100))
    out.append(("hostile/D1", "close", {"closed_pulls": [ours_closed(50401, "L-meta-93401", -60, by="makers-bot", comments=pf)], "passes": [0, 60, 120]},
                {"must_close": [], "must_delete": [], "keep_branch": ["L-meta-93401"]}))
    out.append(("hostile/D2", "close", {"closed_pulls": [mg, ours_closed(50402, "L-meta-93402", -60, by=HANDLE)], "passes": [0, 60, 120]},
                {"must_close": [], "no_push": True, "must_delete": ["L-meta-93400", "L-meta-93402"]}))
    out.append(("hostile/D3", "close", {"closed_pulls": [ours_closed(50403, "L-meta-93403", -60, by=HANDLE)], "passes": [0, 60, 120],
                                        "race_create": {"L-meta-93403": {"sha": "f" * 40, "n": 50490}}},
                {"must_close": [], "no_push": True, "must_delete": [], "keep_branch": ["L-meta-93403"]}))
    # D4: our close, but an earlier PR on the same head was closed by the makers -> the never-again mark stays
    old_mk = ours_closed(50404, "L-meta-93404", -3000, by="makers-bot"); old_mk["head"] = dict(old_mk["head"], sha="%040x" % 50405)
    out.append(("hostile/D4", "close", {"closed_pulls": [old_mk, ours_closed(50405, "L-meta-93404", -60, by=HANDLE)], "passes": [0, 60, 120]},
                {"must_close": [], "no_push": True, "must_delete": [], "keep_branch": ["L-meta-93404"]}))
    # D5: our duplicate closed by the closer itself this run (behind a rival's lower PR) -> its branch deleted next pass
    r5, o5 = rival_pr(50406, "L-meta-93406", created=-400), our_pr(50407, "L-meta-93406", created=-300)
    out.append(("hostile/D5", "close", {"open_pulls": [r5, o5], "taken_map": {"L-meta-93406": (50406, "rival1")}, "passes": [0, 60, 120, 180]},
                {"must_close": [50407], "no_push": True, "must_delete": ["L-meta-93406"]}))
    # 16.8 S1: toolkit refs unreadable at a rejection, a far-future go exists -> the stop gets a NON-DIGIT name (halted)
    out.append(("hostile/S1", "close", {"closed_pulls": five + [rj7(50501, -20)], "passes": [0, 60, 120], "restart_at": [1],
                                        "tk_lsremote_fail_passes": [0],
                                        "toolkit_refs": [{"ref": "refs/heads/filing/go/%d" % (T0 + 10 ** 6), "msg": "filing go: far future", "born": -50}]},
                {"must_close": [], "stop_count": 1, "halted": True, "self_halted": True, "must_push": "refs/heads/filing/stop/rej-50501",
                 "last_stop": "REJ-HALT 1 50501"}))
    # 16.8 S4: a stop ref with a bad name -> HALT-BADREF alert by name, once per 5 min
    out.append(("hostile/S4", "close", {"closed_pulls": five, "passes": [0, 60, 120, 180, 240, 320],
                                        "toolkit_refs": [{"ref": "refs/heads/filing/stop/now", "msg": "filing stop: by hand", "born": -50}]},
                {"must_close": [], "no_push": True, "halted": True, "self_halted": True,
                 "push_count": {"refs/heads/alert/haltbadref-": 2}, "go_count": 0}))
    # TAKEN-STALE (Lead 06:22): taken header over 60 s old or unreadable -> alert by name once per 5 min
    for nm, age, want in (("TS1", 90, 2), ("TS2", 10, 0), ("TS3", None, 2)):
        out.append(("hostile/" + nm, "close", {"closed_pulls": five, "taken_hdr_age": age, "passes": [0, 20, 60, 120, 300, 320]},
                    {"must_close": [], "no_push": True, "push_count": {"refs/heads/alert/takenstale-": want}}))
    # 16.7 (Lead 06:40): 5,100 open PRs for one hour; the closer reads takenpub's open.json + its newest page
    w51 = [rival_pr(60000 + i, "Prove L-meta-%d" % (90000 + i), created=-7200 + i) for i in range(5100)]
    hour = list(range(0, 3601, 20))
    out.append(("hostile/OL1", "close", {"open_pulls": w51, "closed_pulls": five, "passes": hour, "open_json": {"age": 15}},
                {"must_close": [], "no_push": True, "max_reads_all": 600, "push_count": {"refs/heads/alert/openliststale-": 0}}))
    # OL2: open.json stale (header 300 s old) -> own sweep + OPENLIST-STALE once per 5 min; OL3: missing; OL4: old format
    for nm, oj in (("OL2", {"age": 300}), ("OL3", {"missing_passes": list(range(40))}), ("OL4", {"age": 15, "width": 5})):
        out.append(("hostile/" + nm, "close", {"open_pulls": w51[:300], "closed_pulls": five, "passes": list(range(0, 601, 20)), "open_json": oj},
                    {"must_close": [], "no_push": True, "push_count": {"refs/heads/alert/openliststale-": 3}}))
    # OL5: our duplicate behind a rival's lower PR is still closed when the rows come from open.json (rival not on the newest page)
    r55 = rival_pr(61000, "Prove L-meta-91999", created=-7000)
    o55 = our_pr(61001, "L-meta-91999", created=-60)
    out.append(("hostile/OL5", "close", {"open_pulls": [r55] + w51[:150] + [o55], "closed_pulls": five, "passes": [0, 20, 40],
                                         "open_json": {"age": 15}, "taken_map": {"L-meta-91999": (61000, "rival1")}},
                {"must_close": [61001], "no_push": True, "push_count": {"refs/heads/alert/openliststale-": 0}}))
    # W6 43099ec6 / Lead ruling A3: the closer trusts taken.txt alone only when header h[6] == "complete"
    for nm, hs, ok_ in (("TK1", "complete", True), ("TK2", "partial", False), ("TK3", "old", False)):
        out.append(("hostile/" + nm, "close", {"closed_pulls": five, "taken_hdr_age": 10, "taken_hdr_state": hs, "passes": [0, 20]},
                    {"must_close": [], "no_push": True, "taken_ok": ok_}))
    # B9 partial failures. B9a: gh pr close times out AFTER the close happened (our own duplicate, CI comment) -> no halt
    d1, d2 = our_pr(50300, "L-meta-93300", created=-200), our_pr(50301, "L-meta-93300", created=-100)
    d2["comments"] = [{"body": "CI: build started", "user": {"login": "ci-bot"}, "created_at": iso(T0 - 50)}]
    out.append(("hostile/B9a", "close", {"open_pulls": [d1, d2], "close_timeout": [50301], "passes": [0, 20, 60, 120]},
                {"must_close": [50301], "must_keep": [50300], "no_push": True}))
    # B9b: the stop push lands but answers an error -> next pass sees the stop names the PR: exactly one stop, halted
    out.append(("hostile/B9b", "close", {"closed_pulls": five + [rj7(50302, -20)], "stop_push_ghost": 1, "passes": [0, 60, 120]},
                {"must_close": [], "stop_count": 1, "halted": True}))
    # B10: the process dies right before / right after the stop push; the next process converges on one stop, halted
    out.append(("hostile/B10a", "close", {"closed_pulls": five + [rj7(50303, -20)], "die_stop": "before", "passes": [0, 60, 120]},
                {"must_close": [], "stop_count": 1, "halted": True}))
    out.append(("hostile/B10b", "close", {"closed_pulls": five + [rj7(50304, -20)], "die_stop": "after", "passes": [0, 60, 120]},
                {"must_close": [], "stop_count": 1, "halted": True}))
    # B11: 2 h timeline, a pass every 20 s, chain restart at 58 min. 240 rival merges; own duplicates closed by us at
    # 50-57 min with CI comments (CLOSED lost at the restart); rejections at 30 min and 100 min; the Lead's go at 40 min.
    tl = [rival_pr(80000 + i, "Prove L-meta-%d" % (98000 + i), created=30 * i - 60, merged=30 * i) for i in range(240)]
    dd = []
    for i in range(8):
        a_, b_ = our_pr(81000 + 2 * i, "L-meta-%d" % (98500 + i), created=3000 + 50 * i), our_pr(81001 + 2 * i, "L-meta-%d" % (98500 + i), created=3010 + 50 * i)
        b_["comments"] = [{"body": "CI: build passed", "user": {"login": "ci-bot"}, "created_at": iso(T0 + 3100 + 50 * i)}]
        dd += [a_, b_]
    rja, rjb = rj7(81100, 1800), rj7(81101, 6000)
    for x in (rja, rjb):
        x["created_at"] = iso(tt_ := T0 + 1000)
    out.append(("hostile/B11", "close", {"open_pulls": dd, "closed_pulls": tl + [rja, rjb], "passes": list(range(0, 7201, 20)),
                                         "restart_at": [174],
                                         "toolkit_refs": [{"ref": "refs/heads/filing/go/%d" % (T0 + 2400), "msg": "filing go: Lead", "born": 2400}]},
                {"must_close": [81001 + 2 * i for i in range(8)], "must_keep": [81000 + 2 * i for i in range(8)], "stop_count": 2,
                 "halted": True, "go_count": 0, "cache_max": {"CMT": 40, "CLOSER": 40, "MERGED": 400, "MSGS": 10}}))
    # Y5: a new dupclose job (empty CLOSED); our PR closed BY US 3 min ago, a CI-bot comment on it -> no halt
    out.append(("hostile/Y5", "close", {"closed_pulls": [ours_closed(50103, "L-meta-93004", -180, by=HANDLE,
                                                                     comments=[{"body": "build passed", "user": {"login": "ci-bot"}, "at": -170}])],
                                        "passes": [0, 60]}, {"must_close": [], "no_push": True}))
    # Y6: the filing/stop push fails once -> retried at the next pass until the ref exists
    out.append(("hostile/Y6", "close", {"closed_pulls": [ours_closed(50104, "L-meta-93005", -30, by="makers-bot", comments=pf)],
                                        "stop_push_fail": 1, "passes": [0, 60]}, {"must_close": [], "must_push": "refs/heads/filing/stop/"}))
    # X10: templates without "search" (and none at all), every claim "held": both filed, no claim
    for g in hx["X10"]["gaps"]:
        out.append(("hostile/X10-" + g["id"], "submit", {"gid": g["id"], "gaps": [unit_rec(g)], "taken": {"L-meta-1": "someone"},
                                                        "gate_answers": {"*": "held"}}, "PR"))
    # X12: a batch PR titled with ANOTHER unit carries our unit's file; recent (opener reads files) and old (publisher)
    for k, cr in (("X12-recent", -10), ("X12-old", -600)):
        out.append(("hostile/" + k, "submit", {"gid": "L-meta-90101", "gaps": [unit("L-meta-90101")], "taken": {"L-meta-1": "someone"},
                    "open_pulls": [rival_pr(50101, "Prove L-meta-90102", created=cr, files=["lean/PEqualNP/Outside/L_meta_90101.lean",
                                                                                             "lean/PEqualNP/Outside/L_meta_90102.lean"])]}, "no PR"))
    # X13: the files read of a recent no-id PR fails (403 secondary limit): no PR
    out.append(("hostile/X13", "submit", {"gid": "L-meta-90103", "gaps": [unit("L-meta-90103")], "taken": {"L-meta-1": "someone"},
                "open_pulls": [rival_pr(50103, "Batch of proofs", created=-10, files=["lean/PEqualNP/Outside/L_meta_90103.lean"])],
                "files_fail": [50103]}, "no PR"))
    # A3 (W6 43099ec6, Lead ruling): a partial (or old-format) taken list is not the authority: a rival PR older than the
    # header that the list missed must still block (full open sweep); with no rival the unit is still filed
    out.append(("hostile/A3-partial-rival", "submit", {"gid": "L-meta-92301", "gaps": [unit("L-meta-92301")],
                "taken_text": "# updated {T} 05:00:00 steps 1 partial 1795700000 rl 4000 0\nL-meta-5 1 someone 04:00:00\n",
                "open_pulls": [rival_pr(50301, "Batch of proofs", created=-3000, files=["lean/PEqualNP/Outside/L_meta_92301.lean"])]}, "no PR"))
    out.append(("hostile/A3-oldformat-rival", "submit", {"gid": "L-meta-92302", "gaps": [unit("L-meta-92302")],
                "taken_text": "# updated {T} 05:00:00 steps 1\nL-meta-5 1 someone 04:00:00\n",
                "open_pulls": [rival_pr(50302, "Batch of proofs", created=-3000, files=["lean/PEqualNP/Outside/L_meta_92302.lean"])]}, "no PR"))
    out.append(("hostile/A3-partial-free", "submit", {"gid": "L-meta-92303", "gaps": [unit("L-meta-92303")],
                "taken_text": "# updated {T} 05:00:00 steps 1 partial 1795700000 rl 4000 0\nL-meta-5 1 someone 04:00:00\n",
                "open_pulls": [rival_pr(50303, "Batch of proofs", created=-3000, files=["lean/PEqualNP/Outside/L_meta_5.lean"])]}, "PR"))
    # a0 (w12 stall drill): the first create gets a 403 and backs off 30 s; meanwhile a rival opens (at +5 s) or a stop
    # ref appears (at +5 s): the retry must re-check both (rival snapshot at most 2 s old, halt) and open nothing
    out.append(("hostile/a0-rival", "submit", {"gid": "L-meta-92201", "gaps": [unit("L-meta-92201")], "taken": {"L-meta-1": "someone"},
                "create_fail": 1, "open_pulls": [rival_pr(50201, "Batch of proofs", created=5,
                                                          files=["lean/PEqualNP/Outside/L_meta_92201.lean"])]}, "no PR"))
    out.append(("hostile/a0-halt", "submit", {"gid": "L-meta-92202", "gaps": [unit("L-meta-92202")], "taken": {"L-meta-1": "someone"},
                "create_fail": 1, "halt_at": 5}, "no PR"))
    out.append(("hostile/a0-clear", "submit", {"gid": "L-meta-92203", "gaps": [unit("L-meta-92203")], "taken": {"L-meta-1": "someone"},
                "create_fail": 1}, "PR"))
    # Y2: the opener's gate check with the real gate_open_now. Refs unreadable = closed (no claim; the closed-gate rule
    # then files bare as GATEWAY 4 says); open newer than stop = claim; stop newer = no claim
    for k, refs, claim in (("Y2-unreadable", "fail", False),
                           ("Y2-open", ["refs/heads/deskgate/open/200", "refs/heads/deskgate/stop/100"], True),
                           ("Y2-stopped", ["refs/heads/deskgate/open/100", "refs/heads/deskgate/stop/200"], False)):
        g = "L-meta-%d" % (92100 + len(k))
        out.append(("hostile/" + k, "submit", {"gid": g, "gaps": [unit(g)], "taken": {"L-meta-1": "someone"},
                                               "env": {"CLAIM_FIRST": "tl6c-not-search"}, "gate_answers": {"*": "ok"},
                                               "gate_refs": refs, "expect_claim": claim}, "PR"))
    # A20: the real taken-list parser. Header count differs from the rows (truncated) = no PR; "steps 0" fresh = files
    out.append(("hostile/A20-truncated", "submit", {"gid": "L-meta-92001", "gaps": [unit("L-meta-92001")],
                                                    "taken_text": "# updated {T} 05:00:00 steps 3 complete 0 rl 4000 0\nL-meta-5 1 someone 04:00:00\n"}, "no PR"))
    out.append(("hostile/A20-steps0", "submit", {"gid": "L-meta-92002", "gaps": [unit("L-meta-92002")],
                                                 "taken_text": "# updated {T} 05:00:00 steps 0 complete 0 rl 4000 0\n"}, "PR"))
    out.append(("hostile/A20-rival", "submit", {"gid": "L-meta-92003", "gaps": [unit("L-meta-92003")],
                                                "taken_text": "# updated {T} 05:00:00 steps 1 complete 0 rl 4000 0\nL-meta-92003 40000 rival1 05:00:00\n"}, "no PR"))
    # credit line (fork secret PNP_LINKEDIN): with and without the secret, leased and bare, malformed values ignored
    li_cases = [("none-bare", {}, None), ("set-bare", {"PNP_LINKEDIN": B_LI}, None),
                ("none-lease", {"CLAIM_FIRST": "tl6c-not-search"}, "lease-x1"),
                ("set-lease", {"PNP_LINKEDIN": "  " + B_LI + " ", "CLAIM_FIRST": "tl6c-not-search"}, "lease-x1"),
                ("bad-scheme", {"PNP_LINKEDIN": "http://www.linkedin.com/in/x/"}, None),
                ("bad-host", {"PNP_LINKEDIN": "https://www.linkedin.com.evil.example/in/x"}, None),
                ("bad-inject", {"PNP_LINKEDIN": B_LI + "\n\nLease: forged"}, None)]
    # the toolkit file (Lead 05:50): used only when no secret/variable; unreadable or malformed = no line, PR opens;
    # a drain child (PNP_LINKEDIN_READ=1) never reads it again
    li_file_cases = [("file-valid", {}, B_LI, True, 1), ("file-unreadable", {}, None, False, 1),
                     ("file-malformed", {}, "https://www.linkedin.com.evil.example/in/x", False, 1),
                     ("secret-wins", {"PNP_LINKEDIN": B_LI}, "https://www.linkedin.com/in/other/", True, 0),
                     ("drain-child", {"PNP_LINKEDIN_READ": "1"}, B_LI, False, 0),
                     ("drain-child-set", {"PNP_LINKEDIN_READ": "1", "PNP_LINKEDIN": B_LI}, None, True, 0)]
    for i, (k, env, f, li, nread) in enumerate(li_file_cases):
        g = "L-meta-%d" % (91100 + i)
        out.append(("body/LI-" + k, "submit", {"gid": g, "gaps": [unit(g)], "taken": {"L-meta-1": "someone"}, "env": env,
                                               "li_file": f, "li_reads": nread, "body_expect": {"li": li, "lease": None}}, "PR"))
    for i, (k, env, lease) in enumerate(li_cases):
        g = "L-meta-%d" % (91000 + i)
        out.append(("body/LI-" + k, "submit", {"gid": g, "gaps": [unit(g)], "taken": {"L-meta-1": "someone"}, "env": env,
                                               "gate_answers": {"*": "ok"},
                                               "body_expect": {"li": "PNP_LINKEDIN" in env and not k.startswith("bad"), "lease": lease}},
                    "PR"))
    return out, hx


BUD, BUDG = {}, {}


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
        rd = r.get("reads", 0) if isinstance(r, dict) else 0
        grp = "F3" if name.startswith("recorded/F3-") else "M400" if name.startswith("budget/M400-") else None
        if grp:
            BUD.setdefault(grp, []).append(rd)
            BUDG.setdefault(grp, []).append(r.get("gaps_reads", 0) if isinstance(r, dict) else 0)
        if name.startswith("budget/M400-"):
            if not ok:
                fails.append(name)
                if len([f for f in fails if f.startswith("budget/")]) <= 3:
                    print("FAIL", name, why)
            continue
        if name.startswith("recorded/F3-"):
            n_f3 += 1; ok_f3 += ok
            if not ok and len([f for f in fails if f.startswith("recorded/F3-")]) < 3:
                print("FAIL", name, why)
            if not ok:
                fails.append(name)
            continue
        print("ok  " if ok else "FAIL", name, why, f"reads={rd}")
        if not ok:
            fails.append(name)
    for tool, args in (("haltrule.py", []), ("lift.py", ["selftest"]), ("beattest.py", [src])):     # 16.1 / 16.8 S3: pure rule + lift tool
        tp = os.path.join(src, ".github", "cloud-pr", tool)
        if os.path.exists(tp):
            rr = subprocess.run([sys.executable, tp] + args, capture_output=True, text=True, timeout=300)
            last = (rr.stdout.strip().splitlines() or ["no output"])[-1]
            print(("ok   " if rr.returncode == 0 else "FAIL ") + f"selftest/{tool} {last}")
            if rr.returncode:
                fails.append(f"selftest/{tool}")
        else:
            print(f"FAIL selftest/{tool} missing")
            fails.append(f"selftest/{tool}")
    print(f"recorded/F3 {ok_f3}/{n_f3} provable units of the 21:52-21:53 mint filed")
    # Lead 06:12 fact fix: the run token's hourly limit is read from rate_limit (about 5,000), not assumed 1,000
    lim_h, lim_src = 5000, "default, rate_limit not readable here"
    if os.environ.get("GH_TOKEN"):
        try:
            rl = subprocess.run(["gh", "api", "rate_limit", "--jq", ".resources.core.limit"], capture_output=True, text=True, timeout=20)
            if rl.returncode == 0 and rl.stdout.strip().isdigit():
                lim_h, lim_src = int(rl.stdout.strip()), "rate_limit of this run's token"
        except Exception:
            pass
    print(f"info budget/token hourly limit {lim_h} ({lim_src})")
    for grp, lim_avg, lim_tot in (("F3", 2.0, None), ("M400", 2.0, min(800, lim_h // 5))):
        v = BUD.get(grp) or [0]
        tot, avg = sum(v), sum(v) / len(v)
        okb = avg <= lim_avg and (lim_tot is None or tot < lim_tot)
        print(("ok  " if okb else "FAIL"), f"budget/{grp} GitHub reads total {tot} over {len(v)} units, avg {avg:.2f}/unit, "
              f"max {max(v)}, {100 * tot / lim_h:.1f}% of the hourly limit (limit avg {lim_avg}" +
              (f", total < {lim_tot})" if lim_tot else ")"))
        if not okb:
            fails.append(f"budget/{grp}")
        g = BUDG.get(grp) or [0]
        okg = sum(g) / len(g) <= 0.5
        print(("ok  " if okg else "FAIL"), f"budget/{grp}-mirror gaps.json pulls total {sum(g)}, avg {sum(g) / len(g):.2f}/unit "
              f"(limit 0.5; one shared copy per drain, at most 10 s old)")
        if not okg:
            fails.append(f"budget/{grp}-mirror")
    m4 = [f for f in fails if f.startswith("budget/M400-")]
    if m4:
        print(f"FAIL budget/M400 {len(m4)} of 400 units not filed")
    bt = os.path.join(src, ".github", "cloud-pr", "selftest_bucket.py")
    if os.path.exists(bt):
        rb = subprocess.run([sys.executable, "-I", bt, os.path.dirname(bt)], capture_output=True, text=True, timeout=120)
        line = (rb.stdout.strip().splitlines() or ["BUCKET SELFTEST crashed " + rb.stderr.strip()[-120:]])[-1]
    else:
        line = "BUCKET SELFTEST FAIL: no selftest_bucket.py in this checkout"
    print(("ok   " if " OK " in line else "FAIL ") + "rate/" + line)
    if " OK " not in line:
        fails.append("rate/bucket")
    # RC-b (Lead 06:22/06:25): shared halt state, refresher, R3 stamp, rule 16.1 (opener and drain), 16.7 read budget
    for tool, args, okw, tag in (("selftest_rcb.py", [], "RCB SELFTEST OK", "rcb"), ("haltrule.py", ["selftest"], "HALTRULE OK", "16.1"),
                                 ("ghcond.py", ["selftest"], "GHCOND SELFTEST OK", "16.7")):
        tp = os.path.join(src, ".github", "cloud-pr", tool)
        if os.path.exists(tp):
            rr = subprocess.run([sys.executable, "-I", tp] + (args or [os.path.dirname(tp)]), capture_output=True, text=True, timeout=600)
            for l in rr.stdout.strip().splitlines()[:-1]:
                if l.startswith("FAIL"):
                    print("  " + l)
            line = (rr.stdout.strip().splitlines() or [f"{tag} crashed " + rr.stderr.strip()[-120:]])[-1]
        else:
            line = f"{okw.split()[0]} FAIL: no {tool} in this checkout"
        print(("ok   " if line.startswith(okw) else "FAIL ") + f"{tag}/" + line)
        if not line.startswith(okw):
            fails.append(f"{tag}/{tool}")
    dr = open(os.path.join(src, ".github", "cloud-pr", "drain.py")).read()
    okd = "haltrule.verdict" in dr and re.search(r'DRAIN_PR_SLOTS", "6"', dr)
    print(("ok   " if okd else "FAIL ") + "rcb/drain uses haltrule.verdict (rule 16.1) and DRAIN_PR_SLOTS defaults to 6")
    if not okd:
        fails.append("rcb/drain")
    print("SKIP hostile/X11 mirror export order (team/mirror/mirror.py) and gate stop refs: gate v1.2.1 (T11), not fork code")
    f3 = [f for f in fails if f.startswith("recorded/F3-")]
    short = [f for f in fails if not f.startswith(("recorded/F3-", "budget/M400-"))] + \
        ([f"recorded/F3 ({len(f3)} of {n_f3})"] if f3 else []) + ([f"budget/M400 ({len(m4)} of 400)"] if m4 else [])
    print(f"{time.time() - t:.0f}s")
    if fails:
        print(f"PREFLIGHT FAIL {sha}: " + ", ".join(short))
        return 1
    print(f"PREFLIGHT PASS {sha}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
