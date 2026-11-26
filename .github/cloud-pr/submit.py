#!/usr/bin/env python3
"""cloud-pr: open the upstream PR for one finished proof file, from GitHub Actions (no PC needed).

Started by .github/workflows/cloud-pr.yml when a worker pushes branch ready/<step id> to this fork
(pnp-toolkit worker/ready.sh does that next to its toolkit ready/<ID> push).

This is a port of pnp-toolkit watch/watch.py (handle_file, race_ok, submit, claim, release) and
survey/survey.py (race_check, pr_accepted, pr_oversized). Keep the rules in step with those files:
  1. guards: CI's own outside-guard.mjs (gap, imports/format, closure) + CONTRIBUTING rules (checkcore.sh --quick)
  2. race check right before the push. BACKUP SUBMIT: only a rival direct PR that PASSED CI (last intake verdict
     ACCEPTED, file within 524288 bytes) or MERGED blocks; pending, failed, refused or oversized rivals do not.
     Our own open PR on the step blocks (no duplicates with the PC watcher). Held step: claim with have=proof,
     no lease = no PR. Any error = no PR.
  3. the file already in upstream main = lost race.
  4. one commit (only the proof file) on current upstream main, pushed to this fork as branch <step id>, then
     `gh pr create` with retries on GitHub errors (an existing PR for that branch counts as success).
No personal names anywhere: identity is the login Leg0shii and its noreply address only.

Environment: ID, MOD (L_meta_N or V_meta_N__kK), PROOF (file), TREE (shallow clone of upstream main), W (work dir),
READ_TOKEN (the run's GITHUB_TOKEN, for reads), PR_TOKEN (secret, for the push and the PR), DRY=1 (no claim, no
push, no PR, no branch delete). Prints RESULT=<...> and writes result=<...> to $GITHUB_OUTPUT.
"""
import base64, fcntl, json, os, re, subprocess, sys, tempfile, time

UP = "open-goat/pequalnp-proofs"
GAPS = "https://data.pequalnp.com/data/desk/gaps.json"
HANDLE = "Leg0shii"
EMAIL = "46093332+Leg0shii@users.noreply.github.com"
SIZE_LIMIT = 524288
DESC = "Proof written by an AI worker."
FOOTER = "\n\n\U0001F916 Generated with [Claude Code](https://claude.com/claude-code)"

ID = os.environ["ID"]; MOD = os.environ["MOD"]; PROOF = os.environ["PROOF"]; TREE = os.environ["TREE"]
W = os.environ.get("W", tempfile.mkdtemp())
FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
DRY = os.environ.get("DRY", "0") == "1"
READ_TOKEN = os.environ.get("READ_TOKEN", ""); PR_TOKEN = os.environ.get("PR_TOKEN", "")
REL = f"lean/PEqualNP/Outside/{MOD}.lean"
KIND = ""          # gaps.json kind of the step (set by race_ok)
MASK_RE = re.compile(r"PEqualNP\.Represents\.Represents \(fun u v : Fin \d+ => \(\d+ : ℕ\)\.testBit")
# Lead 15:59 (desk pause incident): lease rule cases 2 and 3 suspended, NO LEASE, NO PR, until the Lead's written word
# lifts it (then set NO_LEASE_NO_PR=0 here). With it on there is no PR-first late lease either.
# GATEWAY v1 section 4 (Lead 16:50): replaced by the filing rule in race_ok (lease within 60 s, else unleased if no
# rival PR and no holder, else skip). Off by default.
NO_LEASE_NO_PR = os.environ.get("NO_LEASE_NO_PR", "0") == "1"
# Lead 16:14 UNLEASED-TEST (set only by .github/cloud-pr/utest.py): a free unit (gaps.json: no PR, no holder) gets a PR
# with NO lease and ZERO desk-host requests of any kind (no next, status, step, release), to learn whether PRs alone
# move our pause.
UNLEASED_TEST = os.environ.get("UNLEASED_TEST", "0") == "1"
if UNLEASED_TEST:
    NO_LEASE_NO_PR = False
# Lead 21:59 UTC 26 Nov FILE_FIRST: units whose mirror template contains this word (kind search: tl6c-not-search,
# rect46-andor-search, ...) skip the claim and take the bare path (rival_now and the mirror holder check stay).
# Empty or 0 = off.
FILE_FIRST = os.environ.get("FILE_FIRST", "search").strip()
if FILE_FIRST == "0":
    FILE_FIRST = ""
LATE_LEASE = False     # GATEWAY v1: no late lease (claims only for finished proofs, before the PR)   # unheld: open the PR, then claim
# Lead 14:36: LEASE-FIRST (the ready commit message holds the word lease-first): claim BEFORE any PR (a claim after our
# own PR paid 31 with race: true instead of 110); a grant opens the PR with the Lease line, a refusal or a held step
# opens NO PR (result unleased, branch kept)
LEASE_FIRST = "lease-first" in os.environ.get("READY_MSG", "").lower()
TERMS = [{}]       # points / race of the claim answer (for grants.tsv)
PRIO = [1]
LEASE = [None]     # the lease the PR carries (held: race_ok; unheld: claimed right before gh pr create)
TRANSIENT = re.compile(r"HTTP (408|429|5\d\d)|Something went wrong|secondary rate limit|submitted too quickly|"
                       r"timed? ?out|connection reset|EOF|Internal Server Error|unexpected disconnect|RPC failed|"
                       r"unable to write file|unable to rename temporary|remote: fatal|remote: error", re.I)


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def run(cmd, timeout=300, env=None, cwd=None):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env, cwd=cwd)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(cmd, 1, "", "timeout")


def _desk_host(url):
    """GATEWAY v1: this opener never contacts the desk host (deskgate on the PC is the one door); data mirror only."""
    h = re.sub(r"^https?://([^/:]+).*", r"\1", url or "")
    return h.endswith("pequalnp.com") and h != "data.pequalnp.com"


def curl_json(url, timeout=60):
    if _desk_host(url):
        raise RuntimeError("GATEWAY v1: no desk-host request from the opener")
    for att in range(3):
        r = run(["curl", "-sSf", "--max-time", str(timeout), url], timeout=timeout + 10)
        if r.returncode == 0:
            return json.loads(r.stdout)
        time.sleep(3 * (att + 1))
    raise RuntimeError(f"curl {url}: {r.stderr.strip()[:200]}")


GATE_WAIT_S = float(os.environ.get("GATE_WAIT_S", "60"))   # GATEWAY 4: lease ok within 60 s


def _gate(req, gid, wait):
    """Ref fallback of deskgate (GATEWAY 1): push toolkit ref gatereq/<gid> whose commit message is the request, then
    wait for a NEW toolkit ref lease/<gid> (sha differs from before the request); its message is the desk-rep line
    `lease <gid> ok <lease>` | `lease <gid> held|refused|nobudget|closed|gone|released`. None = no answer in time."""
    m = dg(); g = m.REPO
    ref, ans = f"refs/heads/gatereq/{gid}", f"refs/heads/lease/{gid}"

    def sha_of(r):
        o = run(["git", "-C", g, "ls-remote", "origin", r], timeout=30).stdout.split()
        return o[0] if o else None
    before = sha_of(ans)
    r = run(["git", "-C", g, "push", "-f", "origin", f"{m._marker(req)}:{ref}"], timeout=60)
    if r.returncode:
        log("gate request push failed:", r.stderr.strip()[-120:])
        return None
    t_end = time.time() + wait
    while time.time() < t_end:
        time.sleep(3)
        now = sha_of(ans)
        if now and now != before:
            run(["git", "-C", g, "fetch", "-q", "origin", f"+{ans}:refs/gate-ans"], timeout=60)
            line = run(["git", "-C", g, "log", "-1", "--format=%s", "refs/gate-ans"], timeout=30).stdout.strip()
            if line.startswith(f"lease {gid} "):
                return line
    run(["git", "-C", g, "push", "-q", "origin", f":{ref}"], timeout=60)     # unanswered: withdraw the request
    return None


STG = {}          # Lead 19:14: seconds per stage per unit (guards, race, gate, push, pr), printed as one TIMES line
LAST_GJ = [None]  # the gaps.json read of the race check (mirror pause check of gate_open_now)


def gate_open_now():
    """Lead 19:14: (open, why) without a gate round trip. Closed at once when the toolkit has no deskgate/open/<epoch>
    ref newer than the newest deskgate/stop/<epoch> ref (if any), or the mirror lists our handle as paused. Then no
    claim is sent (and the one-claim lock is not used up). A git error = unknown -> ask the gate as before."""
    gj = LAST_GJ[0] or {}
    if any((p.get("handle") if isinstance(p, dict) else p) == HANDLE for p in gj.get("paused") or []):
        return False, "paused in the mirror"
    try:
        r = run(["git", "-C", dg().REPO, "ls-remote", "origin", "refs/heads/deskgate/open/*", "refs/heads/deskgate/stop/*"], timeout=30)
    except Exception:
        return True, "unknown"
    if r.returncode:
        return True, "unknown"
    ep = lambda k: [int(m.group(1)) for m in re.finditer(rf"/deskgate/{k}/(\d+)$", r.stdout, re.M)]
    op, st = ep("open"), ep("stop")
    if not op or max(op) <= max(st or [0]):
        return False, "no open ref" + (" newer than the stop" if op else "")
    return True, "open ref " + str(max(op))


def gate_claim(gid):
    """(class, lease id or None): ok / held / refused / nobudget / closed / gone / timeout."""
    line = _gate(f"claim {gid} cloud", gid, GATE_WAIT_S)
    p = (line or "").split()
    cls = p[2] if len(p) >= 3 else "timeout"
    return cls, (p[3] if cls == "ok" and len(p) >= 4 else None)


def gh(args, write=False, timeout=120):
    """gh with the run's own token for reads (falls back to PR_TOKEN), PR_TOKEN for writes. Retries transient errors."""
    # reads use the run's own GITHUB_TOKEN only: never fall back to PR_TOKEN, whose API limit the PC and every PR
    # creation share (20:27 UTC: the account hit its limit and gh pr create failed on a wave)
    toks = [PR_TOKEN] if write else [READ_TOKEN or ("" if os.environ.get("GITHUB_ACTIONS") else PR_TOKEN)]
    r = None
    for t in [x for x in toks if x]:
        for att in range(3):
            r = run(["gh"] + args, timeout=timeout, env=dict(os.environ, GH_TOKEN=t))
            if r.returncode == 0:
                return r
            if not TRANSIENT.search(r.stderr + r.stdout):
                break
            time.sleep(5 * (att + 1))
    raise RuntimeError("gh " + " ".join(args[:3]) + ": " + (r.stderr.strip()[:200] if r else "no token"))


# ---- survey.py port -------------------------------------------------------------------------------------------
def step_file_re(step_id):
    mod = step_id.replace("-", "_")
    return re.compile(r"lean/PEqualNP/Outside/(%s|V%s__k\d+)\.lean" % (re.escape(mod), re.escape(mod[1:])))


def pr_accepted(number):
    """True = this rival PR holds the step. Owner 2026-11-25 19:35 (BACKUP SUBMIT, replaces 17:04): no blind backup PRs,
    so a rival holds unless the intake bot's LAST verdict marks it invalid (REJECTED / REFUSED / FAULT); pending and
    accepted rivals both hold (oversized ones are released by pr_oversized). Any doubt = True (it blocks)."""
    try:
        out = gh(["pr", "view", str(number), "--repo", UP, "--json", "comments", "--jq",
                  "[.comments[].body | select(test(\"ACCEPTED|REJECTED|REFUSED|FAULT\"))] | last // \"\""]).stdout
        return not re.search(r"REJECTED|REFUSED|FAULT", out)
    except Exception:
        return True


def pr_oversized(number, step_id):
    """Every file of the PR that proves the step is over the CI size limit. Any doubt = False (it blocks)."""
    try:
        out = gh(["api", "--paginate", f"repos/{UP}/pulls/{number}/files", "--jq", ".[].filename"]).stdout.split()
        paths = [x for x in out if step_file_re(step_id).fullmatch(x)]
        if not paths:
            return False
        for x in paths:
            sz = gh(["api", f"repos/{UP}/contents/{x}?ref=refs/pull/{number}/head", "--jq", ".size"]).stdout.strip()
            if int(sz) <= SIZE_LIMIT:
                return False
        return True
    except Exception:
        return False


_OWN = {}


def own_pr(n):
    if n not in _OWN:
        try:
            _OWN[n] = gh(["pr", "view", str(n), "--repo", UP, "--json", "author", "--jq", ".author.login"]).stdout.strip() == HANDLE
        except Exception:
            _OWN[n] = True
    return _OWN[n]


TAKEN_REF = "refs/heads/status/taken"


_TL = []


def taken_list():
    if not _TL:
        _TL.append(_taken_list())
    return _TL[0]


def _taken_list():
    """The team's live taken list (fork workflow taken.yml -> toolkit status/taken, ~20 s fresh): {step: author} of
    the first PR per step from anyone. None when missing or older than 180 s. A git fetch, no API call."""
    g = os.path.join(W, "taken.git")
    run(["git", "init", "-q", "--bare", g])
    if run(["git"] + (auth_cfg() if PR_TOKEN else []) + ["-C", g, "fetch", "-q", "--depth=1", TK_URL, f"+{TAKEN_REF}:{TAKEN_REF}"],
           timeout=60).returncode:
        return None
    t = run(["git", "-C", g, "show", f"{TAKEN_REF}:taken.txt"]).stdout.splitlines()
    try:
        if not t or time.time() - int(t[0].split()[2]) > 180:
            return None
    except (IndexError, ValueError):
        return None
    return {l.split()[0]: l.split()[2] for l in t[1:] if len(l.split()) >= 3}


def race_check(step_id):
    """Blocking PRs. A step not on the fresh taken list has no PR from anyone: no API call at all. Otherwise (on the
    list, or the list is stale) the GitHub search below, on the run's own token."""
    _TL.clear()                          # fresh copy right before the push
    tl = taken_list()
    if tl is not None and step_id not in tl:
        log("race check: not on the taken list (no API call)")
        return []
    if tl is not None and tl.get(step_id) == HANDLE:
        return [{"number": "?", "state": "OPEN", "ours": True, "why": "our PR on the taken list"}]
    n = step_id.split("-")[-1]
    mod = step_id.replace("-", "_")
    out = gh(["pr", "list", "--repo", UP, "--state", "all", "--search", n, "--limit", "200",
              "--json", "number,state,files,title,author"]).stdout
    direct = []
    for p in json.loads(out):
        paths = [f["path"] for f in p["files"]]
        if any(step_file_re(step_id).fullmatch(x) for x in paths):
            direct.append({"number": p["number"], "state": p["state"],
                           "ours": (p.get("author") or {}).get("login") == HANDLE})
    for d in direct:
        if d["state"] == "OPEN" and not d["ours"]:
            d["accepted"] = pr_accepted(d["number"])
            d["oversized"] = pr_oversized(d["number"], step_id) if d["accepted"] else None
    return [d for d in direct if d["state"] == "MERGED" or (d["state"] == "OPEN" and d["ours"]) or
            (d["state"] == "OPEN" and d.get("accepted") and not d.get("oversized"))]


# ---- watch.py port --------------------------------------------------------------------------------------------
_DESK_T = [0.0]


DESK_MODEL = os.environ.get("DESK_MODEL", "unknown")     # owner 15:40:27 UTC "Yes to both": &model= on every desk call


PAUSED = [False]
NO_DESK_UNTIL = 0               # owner 08:12 UTC 26 Nov "Leases on: cloud and PC" (Lead d46): the shared deskguard pause is the switch
LEASES_ON = True                # d46: claim EVERY step we open (held or unheld), Lease line in the body, release when submitted
LEASE_MAX = 4                   # team-wide (PC, cloud, backup): deskguard.SLOTS leaseslot/<k> refs, 4 of the handle's 5
SLOT_WAIT_S = 45                # slots busy: wait up to 45 s (no desk call), then PR without a lease
LEASE_QUOTA = 1                 # rollout default: total leased claims (leasequota/<k> refs); the toolkit ref leasecap/<n> (highest n)
                                # overrides it without a fork commit: leasecap/6 after the first PR checks out, leasecap/0 is never used
SLOT_STALE_S = 600              # a lease slot older than this belongs to a dead run: taken over
PAUSE_MIN_S = 900               # 4b.5: on a pause or repetition answer, no desk call for at least 15 min
PAUSE_RE = re.compile(r"paus|again and again|repeat|same proof", re.I)
TK_URL = "https://github.com/Leg0shii/pnp-toolkit.git"
TK_PAUSE_REF = "refs/heads/status/desk-pause"   # toolkit: file DESK-PAUSE (until epoch, reason) for every claimer


def set_pause(until, why=""):
    """Shared deskguard pause (every machine of the team) and DESK-PAUSE on the toolkit (Lead rules 4b.5, 4c.6)."""
    if DRY or not PR_TOKEN:
        return
    try:
        log("deskguard pause until", time.strftime("%H:%M:%S", time.gmtime(until)), "UTC:", "ok" if dg().pause(until) else "FAILED")
    except Exception as e:
        log("deskguard pause failed:", repr(e)[:120])
    g = os.path.join(W, "pause.git")
    run(["git", "init", "-q", "--bare", g])
    cenv = dict(os.environ, GIT_AUTHOR_NAME=HANDLE, GIT_COMMITTER_NAME=HANDLE, GIT_AUTHOR_EMAIL=EMAIL, GIT_COMMITTER_EMAIL=EMAIL)
    txt = (f"DESK-PAUSE until {until} {time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime(until))} UTC\n"
           f"written {time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime())} UTC by the cloud opener ({os.environ.get('GITHUB_RUN_ID', '?')})\n"
           f"desk answer: {why[:300]}\n")
    blob = subprocess.run(["git", "-C", g, "hash-object", "-w", "--stdin"], input=txt, capture_output=True, text=True).stdout.strip()
    tree = subprocess.run(["git", "-C", g, "mktree"], input=f"100644 blob {blob}\tDESK-PAUSE\n", capture_output=True, text=True).stdout.strip()
    c = run(["git", "-C", g, "commit-tree", tree, "-m", f"DESK-PAUSE until {until}"], env=cenv).stdout.strip()
    r = run(["git"] + auth_cfg() + ["-C", g, "push", "-q", "-f", TK_URL, f"{c}:{TK_PAUSE_REF}"], timeout=60)
    log("DESK-PAUSE on toolkit", TK_PAUSE_REF, "ok" if r.returncode == 0 else "(push failed)")


_DG = []


def dg():
    """The team's desk gate (Lead's team/lead/deskguard.py, PIPELINE 4c): one git ref claim/<step> per step on the
    toolkit, created atomically (exactly one machine of the whole team gets through), shared pause refs
    deskpause/<epoch>, fails closed. The lock remote is the private toolkit (PR_TOKEN can push there)."""
    if _DG:
        return _DG[0]
    g = os.path.join(W, "dg.git")
    run(["git", "init", "-q", "--bare", g])
    run(["git", "-C", g, "remote", "add", "origin", os.environ.get("DESKGUARD_URL") or TK_URL])
    if PR_TOKEN:
        run(["git", "-C", g, "config", "http.https://github.com/.extraheader",
             "AUTHORIZATION: basic " + base64.b64encode(f"x-access-token:{PR_TOKEN}".encode()).decode()])
    os.environ.update(DESKGUARD_REPO=g, DESKGUARD_REMOTE="origin", DESKGUARD_HOME=os.path.join(W, "dg-home"))
    import importlib.util
    spec = importlib.util.spec_from_file_location("deskguard", os.path.join(os.path.dirname(os.path.abspath(__file__)), "deskguard.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    _DG.append(m)
    return m


def read_pause():
    """Shared pause (deskguard refs deskpause/<epoch> on the toolkit). Unreadable = paused for this run (fail closed)."""
    try:
        return dg().paused_until()
    except Exception as e:
        log("deskguard pause read failed, no desk calls in this run:", repr(e)[:120])
        return time.time() + 3600


def claim_lock(gid):
    """At most ONE desk claim per step, ever, for the whole team: deskguard.acquire (ref claim/<gid> on the toolkit)."""
    if DRY or not PR_TOKEN:
        return False
    w = []
    ok = dg().acquire(gid, w)
    log("deskguard", gid, "OK" if ok else "NO", w[0] if w else "")
    LOCK_WHY[0] = w[0] if w else ""
    return ok


LOCK_WHY = [""]


def _ref_create(ref, msg):
    """create toolkit ref (must not exist); True if this run created it"""
    m = dg(); g = m.REPO
    r = run(["git", "-C", g, "push", f"--force-with-lease={ref}:", "origin", f"{m._marker(msg)}:{ref}"], timeout=60)
    return r.returncode == 0


SLOT = [None]


def take_slot(gid):
    """one of the team-wide lease slots (deskguard.slot_take: PC and backup watcher share them), waiting up to 45 s"""
    dg().SLOTS = LEASE_MAX
    SLOT[0] = dg().slot_take(f"cloud {gid}", wait=SLOT_WAIT_S)
    log("lease slot", SLOT[0] or f"none free after {SLOT_WAIT_S} s: PR without a lease")
    return SLOT[0] is not None


def free_slot():
    if SLOT[0]:
        dg().slot_free(SLOT[0]); log("freed", SLOT[0]); SLOT[0] = None


def quota():
    """rollout cap from the toolkit: highest n of refs leasecap/<n> (n >= 999999 = no cap); none = LEASE_QUOTA"""
    try:
        r = run(["git", "-C", dg().REPO, "ls-remote", "origin", "refs/heads/leasecap/*"], timeout=60)
        ns = [int(l.rsplit("/", 1)[1]) for l in r.stdout.split("\n") if "/leasecap/" in l and l.rsplit("/", 1)[1].isdigit()]
        return max(ns) if ns else LEASE_QUOTA
    except Exception:
        return LEASE_QUOTA


def take_quota(gid):
    q = quota()
    if q >= 999999:
        return True
    for k in range(q):
        if _ref_create(f"refs/heads/leasequota/{k}", f"quota {gid}"):
            log("lease quota", k + 1, "of", q); return True
    return False


RATE_WAIT_S = 45


def rate_prio(backup, points):
    """Lead 09:50 queue order for the team-wide claim tokens: no rival PR and desk price >= 100 first (2), other fresh
    steps (1), backups onto an invalid rival PR last (0)"""
    return 0 if backup else (2 if (points or 0) >= 100 else 1)


def claim_unheld(gid, prio=1):
    """d46: lease for an unheld step right before the push. Any refusal = PR without a lease (an unheld step still
    gets its PR); a pause answer stops all desk calls (claim -> set_pause)."""
    if not LEASES_ON or DRY or not PR_TOKEN:
        return None, "no lease (dry run or no token)"
    if not take_slot(gid):
        return None, f"no lease: {LEASE_MAX} lease slots busy"
    lid, why = claim(gid, prio)
    if not lid:
        free_slot()
    return lid, why


def claim(gid, prio=1):
    """No desk request at all once the desk said the handle is paused: every request while paused extends the pause.
    One claim per step ever (claim_lock); a 410 (proved first) is final. Order: a lease recorded on claim/<gid> is
    reused (no token, no desk call); else one team-wide rate token (toolkit ref leaserate/<epoch>_<n>, PC and backup
    watcher share it), the rollout quota, then the one claim lock. No token or quota = 'no lease:' (PR without one)."""
    if PAUSED[0]:
        return None, "claim skipped: handle paused by the desk"
    if time.time() < NO_DESK_UNTIL:
        return None, "claim skipped: desk off until 07:00 UTC (Lead desk policy; held step skipped, paused)"
    if DRY or not PR_TOKEN:
        return None, "claim skipped: dry run"
    old = dg().lease_of(gid)
    if old:
        return old, "reused the lease recorded on claim/" + gid
    t = time.time()
    op, owhy = gate_open_now()
    STG["gatecheck"] = round(time.time() - t, 1)
    if not op:                             # Lead 19:14: a closed gate costs 0 s, not 60 s of waiting for an answer
        log("gate:", gid, "closed at once:", owhy, f"{time.time() - t:.1f}s")
        return None, f"no lease: gate closed ({owhy})"
    # GATEWAY v1: no caller rate token or quota (the budget lives in deskgate); one claim per step stays (claim_lock)
    if not claim_lock(gid):
        old = None if DRY or not PR_TOKEN else dg().lease_of(gid)
        if old:      # D: our own earlier claim (retry or the other opener): reuse its lease, never claim twice
            return old, "reused the lease recorded on claim/" + gid
        return None, "claim skipped: this step was claimed once already"
    t = time.time()
    cls, lid = gate_claim(gid)
    STG["gate"] = round(time.time() - t, 1)
    log("gate:", gid, cls, lid or "", f"{time.time() - t:.0f}s")
    if cls == "gone":
        return None, "gone (410): proved first (gate)"
    if cls in ("held", "refused"):         # Lead 18:53: with the gate open, held or refused = NO PR
        return None, f"claim refused: {cls} by the desk (gate)"
    if cls != "ok" or not lid:
        return None, f"no lease: gate {cls}"
    dg().record_lease(gid, lid, {})
    return str(lid), "claimed (gate)"


LF_WAIT_S = float(os.environ.get("LF_WAIT_S", "15"))      # GATEWAY 4: slot wait short, the gate answers within 60 s      # owner 15:17:26 lease rule: wait up to 3 min for a token
_LF_HELD = re.compile(r"gets a head start|was handed this step|bring your proof back|held by another|another handle|"
                      r"at most one handle|retry_after", re.I)


def lf_case(why):
    """GATEWAY 4: held (another agent holds it) = no PR; final (proved first) = no PR; anything else (gate closed,
    paused, no budget, refused, no answer in 60 s) = bare: PR without a lease if no rival PR and no holder."""
    w = why or ""
    if w.startswith("claim refused") and (_LF_HELD.search(w) or "(gate)" in w):
        return "held"
    if "dry run" in w:
        return "stop"
    if "410" in w or "proved first" in w:
        return "final"
    return "bare"


def rival_now(gid):
    """Lead 18:53: right before gh pr create on the unleased branch. One REST call (no search index lag): the newest 100
    open upstream PRs; a PR of another author whose title or head branch names the unit -> its number. Then the fresh
    taken list (first PR of another author). Fixture for tests: RIVAL_FIXTURE (the pulls JSON). Error -> rival (skip)."""
    try:
        if os.environ.get("RIVAL_FIXTURE"):
            pulls = json.load(open(os.environ["RIVAL_FIXTURE"]))
        else:
            pulls = json.loads(gh(["api", f"repos/{UP}/pulls?state=open&sort=created&direction=desc&per_page=100"]).stdout)
        pat = re.compile(r"(?<![A-Za-z0-9])(%s|%s)(?![0-9])" % (re.escape(gid), re.escape(gid.replace("-", "_"))))
        for p in pulls:
            if (p.get("user") or {}).get("login") != HANDLE and (pat.search(p.get("title") or "") or pat.search((p.get("head") or {}).get("ref") or "")):
                return f"#{p.get('number')} by {(p.get('user') or {}).get('login')}"
    except Exception as e:
        return "rival check failed: " + repr(e)[:80]
    tl = None if os.environ.get("RIVAL_FIXTURE") else taken_list()
    if tl is not None and tl.get(gid) not in (None, HANDLE):
        return f"taken list: first PR by {tl.get(gid)}"
    return None


def rival_open(gid):
    """A PR from someone else is on the step: the taken list (first PR per step), else the PR search; fail closed."""
    try:
        tl = taken_list()
        if tl is not None:
            return gid in tl and tl.get(gid) != HANDLE
        out = gh(["pr", "list", "--repo", UP, "--state", "open", "--search", gid.split("-")[-1], "--limit", "100",
                  "--json", "number,files,author"]).stdout
        return any((p.get("author") or {}).get("login") != HANDLE and any(step_file_re(gid).fullmatch(f["path"]) for f in p["files"])
                   for p in json.loads(out))
    except Exception as e:
        log("rival check failed (no PR without a lease):", repr(e)[:120])
        return True


def claim_retry(gid, prio=1):
    return claim(gid, prio)            # one claim per step, ever: no retries (the desk pauses handles that repeat)


def release(lid, reason):
    """GATEWAY v1: release(submitted) through the gate's ref fallback; no wait (the gate drains releases after claims)."""
    if lid and not DRY and reason == "submitted":
        m = dg()
        r = run(["git", "-C", m.REPO, "push", "-f", "origin", f"{m._marker(f'release {ID} {lid} cloud')}:refs/heads/gatereq/{ID}"], timeout=60)
        log("gate release request", lid, "ok" if r.returncode == 0 else "push failed")


def pr_list(g):
    pn = g.get("pr_numbers") or []
    if isinstance(pn, str):
        try:
            pn = json.loads(pn or "[]")
        except Exception:
            pn = [pn]
    return pn


def race_ok(gid):
    """(ok, why, lease). have=proof always: we hold a finished file."""
    try:
        gj = curl_json(GAPS, 60)
        LAST_GJ[0] = gj
        if gid in (gj.get("withdrawn") or {}):
            return False, "withdrawn: " + str(gj["withdrawn"][gid])[:120], None
        g = next((x for x in gj["gaps"] if x["id"] == gid), None)
        if g is None:
            return False, "not posted", None
        global KIND
        KIND = g.get("kind") or ""
        # intake rule: a listed PR blocks only if it is ours or passed CI within the size limit (backup rule)
        live = [n for n in pr_list(g) if own_pr(n) or (pr_accepted(n) and not pr_oversized(n, gid))]
        if live:
            return False, f"PR already open {live}", None
        if UNLEASED_TEST:
            if (g.get("pr_open") or 0) or g.get("pr_numbers") or (g.get("holders_now") or 0) or g.get("held_now"):
                return False, "unleased test: not free in gaps.json (pr_open / pr_numbers / holder)", None
            b = race_check(gid)
            return (not b), (f"blocking PRs {b}" if b else "clear (unleased test: free in gaps.json, no desk request)"), None
        if g.get("kind") == "value":            # value steps (lane atlas) are not desk steps
            b = race_check(gid)
            return (not b), (f"blocking PRs {b}" if b else "clear"), None
        # 16:00 pause (Lead condition 2): no desk/status or desk/step read; gaps.json (static export) carries
        # held_now / holders_now / offerable_now for every listed step
        prio = rate_prio(bool(pr_list(g)), g.get("points") or g.get("weight") or 0)
        is_h = bool(g.get("held_now")) or (g.get("holders_now") or 0) > 0
        if not is_h and g.get("offerable_now") is False:
            return False, "not offerable on the desk now (gaps.json)", None
        b = race_check(gid)
        if b:
            return False, f"blocking PRs {b}", None
        if DRY:
            return True, "clear (dry run: no gate request)", None
        # GATEWAY v1 section 4 (Lead 16:50 UTC 26 Nov), in code: finished proof -> ask deskgate for the lease. Lease ok
        # within 60 s -> PR with the lease. Else, if GitHub shows no rival PR now and the mirror shows no holder -> PR
        # without a lease. Else skip (no backup PRs). Gate closed or paused -> the unleased branch.
        old = dg().lease_of(gid)
        if old:
            return True, "clear (our recorded lease reused)", old
        tpl = str((g.get("faithful_by_template") or {}).get("template") or "")
        if FILE_FIRST and FILE_FIRST in tpl:
            # Lead 21:59 FILE_FIRST: no claim (open-gate claims on a fresh slice all came back held = no PR); the bare
            # path below decides: PR without a lease when no rival PR and no holder in the mirror. Late lease later.
            why = f"no lease: file first ({tpl})"
            log("gate:", gid, "skipped: file first", tpl)
        else:
            global SLOT_WAIT_S
            SLOT_WAIT_S = LF_WAIT_S
            lid, why = claim_unheld(gid, 2)
            if lid:
                return True, "clear, " + why, lid
        case = lf_case(why)
        if case == "bare" and rival_open(gid):
            case = "rival PR"
        if case == "bare":
            try:
                g2 = next((x for x in curl_json(GAPS, 60)["gaps"] if x["id"] == gid), None)
            except Exception:
                g2 = {"held_now": True}          # cannot tell: treat as held (fail closed)
            if g2 and (g2.get("held_now") or (g2.get("holders_now") or 0) > 0):
                case = "held in the mirror"
        if case != "bare":
            return False, f"lease-first: {case} (" + why[:120] + "), no PR", None
        TERMS[0] = {"bare": why[:160]}
        return True, "clear, no lease (" + why[:100] + "): PR without a lease (GATEWAY 4)", None
    except Exception as e:
        return False, f"race check error {e}", None


STOP_URL = "https://raw.githubusercontent.com/open-goat/pequalnp-proofs/main/STOP"


def stopped():
    """Owner's kill switch (Lead D7, same as watch.py stopped()): while upstream main has a STOP file, no PR and no
    lease. True if the fresh upstream clone has it or the raw URL answers 200."""
    if os.path.exists(os.path.join(TREE, "STOP")):
        return True
    r = run(["curl", "-sS", "-o", "/dev/null", "-w", "%{http_code}", "--max-time", "10", STOP_URL], timeout=20)
    return r.stdout.strip() == "200"


def open_pr_for_branch(gid):
    """Our own open PR whose head is this fork's branch <gid> (exact, no search index lag). Skipped (no API call) when
    the fresh taken list has no PR at all for the step."""
    tl = taken_list()
    if tl is not None and gid not in tl:
        return None
    out = gh(["api", f"repos/{UP}/pulls?head={HANDLE}:{gid}&state=open", "--jq", ".[].html_url"]).stdout.split()
    return out[0] if out else None


def git(*a, env=None, timeout=300):
    return run(["git", "-C", TREE] + list(a), env=env, timeout=timeout)


def auth_cfg():
    b = base64.b64encode(f"x-access-token:{PR_TOKEN}".encode()).decode()
    return ["-c", f"http.https://github.com/.extraheader=AUTHORIZATION: basic {b}"]


def push_branch(c, gid):
    url = f"https://github.com/{FORK}.git"
    # a recent fork branch as negotiation base, so the push sends only the new objects (not the whole tree)
    refs = git("ls-remote", url, "refs/heads/L-*", timeout=120).stdout.split("\n")
    nums = sorted(((int(m.group(1)), m.group(0)) for l in refs for m in [re.search(r"refs/heads/L-meta-(\d+)$", l)] if m),
                  reverse=True)
    if nums:
        git("fetch", "-q", "--depth=1", url, f"{nums[0][1]}:refs/fork/tip", timeout=180)
    for att in range(4):
        r = run(["git"] + auth_cfg() + ["-C", TREE, "push", "-q", "-f", url, f"{c}:refs/heads/{gid}"], timeout=600)
        if r.returncode == 0 or not TRANSIENT.search(r.stderr):
            return r.stderr.strip()[:300] if r.returncode else None
        log("push retry", r.stderr.strip()[:150].replace("\n", " | "))
        time.sleep(5 * (att + 1))
    return r.stderr.strip()[:300]


class pr_gate:
    """Drain mode (drain.py, many submit.py at once on one runner): at most PR_GATE_N (2) PR creations in flight,
    by flock on PR_GATE_DIR/slot<k> (GitHub refuses PR-creation bursts). No PR_GATE_DIR (one run per branch): no gate."""
    def __enter__(self):
        self.f = None
        d = os.environ.get("PR_GATE_DIR")
        while d:
            for k in range(int(os.environ.get("PR_GATE_N", "2"))):
                f = open(os.path.join(d, f"slot{k}"), "w")
                try:
                    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB); self.f = f; return self
                except OSError:
                    f.close()
            time.sleep(0.2)
        return self

    def __exit__(self, *a):
        if self.f:
            self.f.close()


def submit(gid, lease):
    base = git("rev-parse", "HEAD").stdout.strip()
    if not base:
        return None, "no upstream main"
    if git("cat-file", "-e", f"{base}:{REL}").returncode == 0:
        return None, "file already in upstream main"
    idx = os.path.join(W, "submit.idx")
    env = dict(os.environ, GIT_INDEX_FILE=idx)
    blob = git("hash-object", "-w", PROOF).stdout.strip()
    if git("read-tree", base, env=env).returncode:
        return None, "read-tree failed"
    git("update-index", "--add", "--cacheinfo", f"100644,{blob},{REL}", env=env)
    tree = git("write-tree", env=env).stdout.strip()
    changed = git("diff-tree", "--name-only", "-r", base, tree).stdout.split()
    if changed != [REL]:
        return None, f"unexpected changed files {changed}"
    msg = gid + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n"
    cenv = dict(os.environ, GIT_AUTHOR_NAME=HANDLE, GIT_COMMITTER_NAME=HANDLE, GIT_AUTHOR_EMAIL=EMAIL, GIT_COMMITTER_EMAIL=EMAIL)
    c = git("commit-tree", tree, "-p", base, "-m", msg, env=cenv).stdout.strip()
    if not c:
        return None, "commit-tree failed"
    if DRY:
        return "dry-run", f"would push {c[:12]} as {FORK}:{gid} and open the PR"
    t = time.time()
    err = push_branch(c, gid)
    STG["push"] = round(time.time() - t, 1)
    if err:
        return None, "push: " + err
    log("pushed", c[:12], "to", f"{FORK}:{gid}")
    r = None
    t_pr = time.time()
    if not lease:
        rv = rival_now(gid)               # Lead 18:53: no unleased PR next to a rival's (2-108 s behind them today)
        if rv:
            log("SKIP", gid, "unleased PR not opened, rival", rv)
            return None, "rival PR open: " + rv
    for att in range(5):
        if stopped():                    # STOP may appear while this PR waited for a retry
            return None, "STOP file on upstream main"
        body = DESC + (f"\n\nLease: {lease}" if lease else "") + FOOTER
        with pr_gate():
            r = run(["gh", "pr", "create", "--repo", UP, "--head", f"{HANDLE}:{gid}", "--base", "main",
                     "--title", gid, "--body", body], timeout=120, env=dict(os.environ, GH_TOKEN=PR_TOKEN))
        if re.search(r"https://\S+", r.stdout) or "already exists" in r.stderr:
            break                                   # an existing PR for our branch is a success
        if not TRANSIENT.search(r.stderr + r.stdout) or att == 4:
            break
        log("PR retry in", 30 * 2 ** att, "s:", r.stderr.strip()[:150])
        time.sleep(30 * 2 ** att)
    url = (re.findall(r"https://github\.com/\S+/pull/\d+", r.stdout + r.stderr) or [None])[0]
    STG["pr"] = round(time.time() - t_pr, 1)
    LEASE[0] = lease
    return url, ("ok" if url else r.stderr.strip()[:300])


def delete_ready():
    pre = "utest" if UNLEASED_TEST else "ready"
    if DRY or os.environ.get("GITHUB_REF_NAME") != f"{pre}/{ID}":     # push, or a dispatch on the ready/ branch
        return
    r = run(["git"] + auth_cfg() + ["-C", TREE, "push", "-q", f"https://github.com/{FORK}.git", "--delete", f"{pre}/{ID}"], timeout=120)
    log(f"deleted {pre}/" + ID if r.returncode == 0 else f"could not delete {pre}/" + ID + ": " + r.stderr.strip()[:120])


def finish(result, why, url=None):
    log("TIMES", ID, " ".join(f"{k}={v}" for k, v in STG.items()), f"total={time.time() - T_START:.1f}")
    log(f"RESULT={result}", ID, url or "", why)
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            f.write(f"result={result}\nwhy={why[:300].replace(chr(10), ' ')}\nurl={url or ''}\n"
                    f"lease={LEASE[0] or ''}\npoints={TERMS[0].get('points', '')}\nrace={TERMS[0].get('race', '')}\n"
                    f"leasefirst={int(LEASE_FIRST)}\nterms={json.dumps(TERMS[0])}\n")
    if result in ("submitted", "race", "exists", "formatfail"):
        delete_ready()
    sys.exit(1 if result in ("submitfail", "formatfail", "error", "stopped") else 0)


T_START = time.time()


def main():
    t0 = time.time()
    if not re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*", ID) or len(ID) > 64:
        finish("error", f"bad step id {ID!r}")
    if not (MOD == ID.replace("-", "_") or re.fullmatch(r"V%s__k\d+" % re.escape(ID.replace("-", "_")[1:]), MOD)):
        finish("error", f"file name {MOD}.lean does not belong to {ID}")
    if os.path.getsize(PROOF) > SIZE_LIMIT:
        finish("formatfail", f"file is {os.path.getsize(PROOF)} bytes, over the CI limit {SIZE_LIMIT}")
    if not DRY and not PR_TOKEN:
        finish("skipped", "no PR_TOKEN secret: the PC watcher takes this file from pnp-toolkit ready/ instead")
    try:
        url = open_pr_for_branch(ID)
    except Exception as e:
        finish("error", f"PR lookup failed: {e}")
    if url and DRY:
        log("dry run: our PR is already open, testing the rest anyway:", url)
    elif url:
        finish("exists", "our PR for this branch is already open (PC watcher or an earlier run)", url)
    # 1. guards (= formatscan on the PC)
    env = dict(os.environ, NODE=subprocess.run(["sh", "-c", "command -v node"], capture_output=True, text=True).stdout.strip())
    if MOD != ID.replace("-", "_"):
        env["REL_OVERRIDE"] = REL
    # 12:19 UTC 26 Nov (L-meta-19447): a file for a proposed, not yet listed step failed the gap guard as formatfail and
    # its ready/ branch was deleted, so the ready-wait path never ran. Unlisted: guards in prestage mode (no gap guard,
    # the file's own imports), then keep the branch; ready-wait.yml dispatches this job again at listing.
    unlisted = False
    try:
        gj0 = curl_json(GAPS, 60)
        unlisted = not any(x.get("id") == ID for x in gj0.get("gaps") or []) and ID not in (gj0.get("withdrawn") or {}) \
            and not any((x.get("id") if isinstance(x, dict) else x) == ID for x in gj0.get("checked") or [])
        # Lead 14:22 SAFETY: no new PR on a step another agent holds (holders_now above 0) unless we hold its lease
        hn = next((x.get("holders_now") or 0 for x in gj0.get("gaps") or [] if x.get("id") == ID), 0)
        if hn > 0 and os.environ.get("HELD_SKIP", "1") == "1":
            old = None
            try:
                old = dg().lease_of(ID) if PR_TOKEN else None
            except Exception:
                pass
            if not old:
                finish("unleased" if LEASE_FIRST else "race",
                       f"held by {hn} other agent(s) at the desk and no lease of ours: no new PR (Lead 14:22)")
    except Exception as e:
        log("gaps.json read failed, full guards:", repr(e)[:120])
    if unlisted:
        imps = re.findall(r"^import\s+(\S+)", open(PROOF, errors="replace").read(), re.M) or ["PEqualNP.Defs"]
        env["PRESTAGE_IMPORTS"] = json.dumps(imps)
        log("not listed yet: prestage guards (imports", imps, ")")
    r = run(["bash", os.path.join(os.path.dirname(os.path.abspath(__file__)), "checkcore.sh"), PROOF, ID, TREE,
             os.path.join(W, "guard"), "--quick"], env=env, timeout=600)
    print(r.stdout[-3000:], r.stderr[-2000:], sep="\n", flush=True)
    git("clean", "-q", "-f", "--", "lean/PEqualNP/Outside/")          # the closure guard copied the file in
    if r.returncode:
        finish("formatfail", "guards: " + ((r.stdout + r.stderr).strip().splitlines() or ["?"])[-1][:200])
    log(f"guards passed ({time.time() - t0:.0f}s)")
    STG["guards"] = round(time.time() - t0, 1)
    if unlisted:
        finish("waiting", "not posted: prestage guards passed, branch kept for ready-wait")
    # GATEWAY v1 section 4: a pause never stops filing (the gate answers closed and the unleased branch decides)
    if not DRY and stopped():
        finish("stopped", "STOP file on upstream main: no PR, no lease (branch kept; re-run the job once STOP is gone)")
    # 2. race check right before the push
    t_rc = time.time()
    ok, why, lease = race_ok(ID)
    STG["race"] = round(time.time() - t_rc, 1)
    if not ok:
        # an error or the desk's lease cap is not a lost race: keep the branch (re-run the job), the PC still has its copy
        if why in ("not posted", "not on the desk"):
            # pre-generated file for a step the desk has not listed yet: keep ready/<ID>; ready-wait.yml dispatches
            # this workflow again for the branch the moment the step is listed
            finish("waiting", why + ": branch kept for ready-wait")
        if why.startswith("lease-first"):
            free_slot()
            finish("unleased", why)       # Lead 14:36: no PR, branch kept, the id goes to team/lead/wave8/unleased.txt
        finish("error" if why.startswith("race check error") or "most one handle may hold" in why or "paused" in why
               else "race", why)          # a 410 or an earlier claim of this step ends here as a lost race
    if NO_LEASE_NO_PR and not lease and not DRY:
        free_slot()
        finish("unleased", "no lease, no PR (Lead 15:59, cases 2 and 3 suspended): " + why[:120])
    log("race check:", why)
    # 3.+4. commit on upstream main, push, PR
    late = lease == "LATE"
    if late:
        lease = None
    LEASE[0] = lease
    url, why2 = submit(ID, lease)
    if late and url and url != "dry-run":
        # late lease (Lead 13:37 probe): one claim through deskguard now that the PR is open; on a grant the PR body
        # gets the Lease line by edit, then the lease is released as for any submitted PR. Refused = PR stays as is.
        lid, lwhy = claim_unheld(ID, PRIO[0])
        log("late lease:", lwhy)
        if lid:
            body = DESC + f"\n\nLease: {lid}" + FOOTER
            r = run(["gh", "pr", "edit", url, "--body", body], timeout=60, env=dict(os.environ, GH_TOKEN=PR_TOKEN))
            log("late lease: Lease line added" if r.returncode == 0 else "late lease: PR edit failed: " + r.stderr.strip()[:150])
            LEASE[0] = lid
            why2 += f"; late lease {lid}" + ("" if r.returncode == 0 else " (body edit failed)")
        else:
            why2 += "; no late lease (" + lwhy[:80] + ")"
    if url and url != "dry-run":
        release(LEASE[0], "submitted")
    elif LEASE[0]:     # D: failed PR create: keep the lease (recorded on claim/<id>; the retry or PC reuses it, expires 45 min)
        log("PR not opened: lease", LEASE[0], "kept for the retry")
    free_slot()
    if url == "dry-run":
        finish("dry", why2)
    if not url and (why2 == "file already in upstream main" or why2.startswith("rival PR open")):
        finish("race", why2)
    if not url and why2.startswith("STOP"):
        finish("stopped", why2 + " (branch kept)")
    finish("submitted" if url else "submitfail", f"{why2}; {time.time() - t0:.0f}s after start", url)


if __name__ == "__main__":
    main()
