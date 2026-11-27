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
import base64, fcntl, json, os, re, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor
REAL_SLEEP = time.sleep      # 16.14 refresher heartbeat thread (tests patch time.sleep)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # drain runs submit.py with -I (no script dir on the path)
import ghcond, haltrule                                              # RC-b: 16.7 conditional reads, 16.1 halt rule
import treebuild                                                     # lane tree (W7): the unit's tree along one path

UP = "open-goat/pequalnp-proofs"
GAPS = "https://data.pequalnp.com/data/desk/gaps.json"
HANDLE = "Leg0shii"
EMAIL = "46093332+Leg0shii@users.noreply.github.com"
SIZE_LIMIT = 524288
DESC = "Proof written by an AI worker."
FOOTER = "\n\n\U0001F916 Generated with [Claude Code](https://claude.com/claude-code)"
# Owner 05:22 UTC 27 Nov: the makers' optional credit line (PULL_REQUEST_TEMPLATE.md, tools/pnp.sh PNP_LINKEDIN). The address
# comes from the fork secret or variable PNP_LINKEDIN, else (Lead 05:50, signed) from config/linkedin.txt in the private
# toolkit, read ONCE per drain by drain.py (children get PNP_LINKEDIN_READ=1 and never read it again) or once by a
# single-unit run. Unset, unreadable, slow (20 s) or malformed = no line, and the body is then byte for byte what it was
# before; the PR opens either way. The Lease paragraph and the footer keep their place and form. Never logged.
LI_RX = r"https://www\.linkedin\.com/in/[A-Za-z0-9%._-]+/?"
_LIV = []


def li_from_toolkit():
    """config/linkedin.txt on toolkit main: one authenticated blobless shallow fetch, 20 s in all; '' on any failure."""
    if not os.environ.get("PR_TOKEN"):
        return ""
    import shutil
    g = tempfile.mkdtemp(prefix="li-")
    try:
        a = auth_cfg()
        subprocess.run(["git", "init", "-q", "--bare", g], capture_output=True, timeout=10)
        subprocess.run(["git", "-C", g, "remote", "add", "origin", TK_URL], capture_output=True, timeout=10)
        t = time.time()
        r = subprocess.run(["git", *a, "-C", g, "fetch", "-q", "--depth=1", "--filter=blob:none", "origin", "main"],
                           capture_output=True, text=True, timeout=20)
        if r.returncode:
            return ""
        r = subprocess.run(["git", *a, "-C", g, "show", "FETCH_HEAD:config/linkedin.txt"], capture_output=True, text=True,
                           timeout=max(1.0, 20 - (time.time() - t)))
        return r.stdout.strip() if r.returncode == 0 else ""
    except Exception:
        return ""
    finally:
        shutil.rmtree(g, ignore_errors=True)


def li_line():
    if not _LIV:
        v = os.environ.get("PNP_LINKEDIN", "").strip()
        if not v and os.environ.get("PNP_LINKEDIN_READ") != "1":
            v = li_from_toolkit()
        _LIV.append(f"\n\n**LinkedIn profile**: {v}" if re.fullmatch(LI_RX, v) else "")
    return _LIV[0]


def pr_body(lease):
    return DESC + li_line() + (f"\n\nLease: {lease}" if lease else "") + FOOTER

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
# mintdrill B1 (red team 27 Nov): keying on the word "search" repeats F3 for any new or empty template name. Default
# now "*" = every unit files first; CLAIM_FIRST = comma list of templates that still claim first (allow-list, empty).
FILE_FIRST = os.environ.get("FILE_FIRST", "*").strip()
if FILE_FIRST == "0":
    FILE_FIRST = ""
CLAIM_FIRST = {x.strip() for x in os.environ.get("CLAIM_FIRST", "").split(",") if x.strip()}
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


GAPS_MAX_AGE_S = float(os.environ.get("GAPS_MAX_AGE_S", "10"))


# REHEARSAL (Lead 08:33): in a -drill run the drill driver force-pushes the fork ref DRILL_GAPS_REF (a commit whose
# tree holds gaps.json, same record shape as the desk's, drill units only) at each of its exports. Every pull of the
# real gaps.json (same 7 MB, same GAPS_MAX_AGE_S cache, so the listing lag stays real) appends those records, so an
# L-drill unit is LISTED and runs guards, race, halt, commit build and WOULD-CREATE like a real one. Never set in
# cloud-pr.yml (only loadcanary.yml sets it, and only with DRY on).
DRILL_GAPS_REF = os.environ.get("DRILL_GAPS_REF", "")
DRILL_NOTE = [0]


def drill_merge(gj):
    try:
        r = gh(["api", "-H", "Accept: application/vnd.github.raw",
                f"repos/{FORK}/contents/gaps.json?ref={DRILL_GAPS_REF}"], timeout=30)
        dg_ = json.loads(r.stdout)
        drill = [x for x in (dg_.get("gaps") or []) if str(x.get("id", "")).startswith("L-drill-")]
    except Exception as e:
        if DRILL_NOTE[0] < 3:
            DRILL_NOTE[0] += 1
            log(f"drill gaps {DRILL_GAPS_REF}: not read ({str(e)[:100]}), drill units unlisted this pull")
        return gj
    have = {x.get("id") for x in drill}
    gj = dict(gj)
    gj["gaps"] = [x for x in (gj.get("gaps") or []) if x.get("id") not in have] + drill
    return gj


def gaps_json():
    """B2 (27 Nov): one gaps.json copy per drain, shared by every worker and read again only when older than
    GAPS_MAX_AGE_S (7 MB a pull; it was 3 to 4 pulls per unit). The copy is also what the guards read (GAPS_FILE)."""
    d = os.environ.get("RIVAL_SNAP_DIR") or os.environ.get("PR_GATE_DIR") or W
    os.makedirs(d, exist_ok=True)
    f, tf = os.path.join(d, "gaps.json"), os.path.join(d, "gaps.t")
    ask = time.time()

    def stamp():
        try:
            return float(open(tf).read())
        except (OSError, ValueError):
            return None
    s0 = stamp()                         # 16.14 (no convoy): a fresh copy is parsed without the lock
    if s0 is not None and 0 <= time.time() - s0 < GAPS_MAX_AGE_S:
        try:
            return json.load(open(f))
        except Exception:
            pass
    with open(os.path.join(d, "gaps.lock"), "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        s1 = stamp()                     # a pull that STARTED after we asked answers us: no age re-check after the wait
        fresh = s1 is not None and (s1 > ask or 0 <= time.time() - s1 < GAPS_MAX_AGE_S)
        if not fresh:
            t = time.time()
            gj = curl_json(GAPS, 60)
            if DRILL_GAPS_REF:
                gj = drill_merge(gj)
            with open(f + ".tmp", "w") as o:
                json.dump(gj, o)
            os.replace(f + ".tmp", f)
            with open(tf + ".tmp", "w") as o:
                o.write(str(t))          # stamped at pull START
            os.replace(tf + ".tmp", tf)
            return gj
    return json.load(open(f))            # parsed outside the lock


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


def gate_answer_lease(gid):
    """the lease id in the gate's last answer ref lease/<gid> ("lease <gid> ok <lease>"), else None"""
    try:
        g = dg().REPO
        if run(["git", "-C", g, "fetch", "-q", "origin", f"+refs/heads/lease/{gid}:refs/gate-ans"], timeout=60).returncode:
            return None
        m = re.fullmatch(rf"lease {re.escape(gid)} ok (\S+)",
                         run(["git", "-C", g, "log", "-1", "--format=%s", "refs/gate-ans"], timeout=30).stdout.strip())
        return m.group(1) if m else None
    except Exception:
        return None


STG = {}          # Lead 19:14: seconds per stage per unit (guards, race, gate, push, pr), printed as one TIMES line
LAST_GJ = [None]  # the gaps.json read of the race check (mirror pause check of gate_open_now)


def gate_open_now():
    """Lead 19:14: (open, why) without a gate round trip. Closed at once when the toolkit has no deskgate/open/<epoch>
    ref newer than the newest deskgate/stop/<epoch> ref (if any), or the mirror lists our handle as paused. Then no
    claim is sent (and the one-claim lock is not used up). Red team Y2 (Lead 05:35): refs unreadable after 3 tries
    2 s apart = CLOSED (was "unknown" = open, and the claim went out)."""
    gj = LAST_GJ[0] or {}
    if any((p.get("handle") if isinstance(p, dict) else p) == HANDLE for p in gj.get("paused") or []):
        return False, "paused in the mirror"
    r = None
    for k in range(3):
        try:
            r = run(["git", "-C", dg().REPO, "ls-remote", "origin", "refs/heads/deskgate/open/*", "refs/heads/deskgate/stop/*"], timeout=30)
            if r.returncode == 0:
                break
        except Exception:
            r = None
        time.sleep(2)
    if r is None or r.returncode:
        return False, "gate refs unreadable (closed, fail closed)"
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


# Lead 09:29 (RUN-TOKEN-EMPTY, RC-b): the run token's hourly limit is per REPOSITORY (5000 here), shared by every run of
# the fork (canaries, lane-ci, the closer). At 0 every read failed closed = zero filing at mint time. Now a read refused
# for the PRIMARY rate limit is sent again with PR_TOKEN, and until the run token's reset epoch every read of the drain
# goes to PR_TOKEN directly (shared file SNAP_DIR/runtoken-empty: "<reset epoch> <when> <what>"); drain.py alerts
# RUN-TOKEN-EMPTY. Writes and the create path are unchanged; RUNTOKEN_FALLBACK=0 turns it off.
def primary_rl(r):
    """the run token's PRIMARY rate limit refused this call (not a secondary limit, not a 304 at 0 remaining)"""
    t = (r.stdout or "") + "\n" + (r.stderr or "")
    if "secondary" in t.lower():
        return False
    if re.search(r"API rate limit exceeded", t, re.I):
        return True
    return bool(re.match(r"HTTP/\S+\s+(403|429)\b", r.stdout or "")
                and re.search(r"^x-ratelimit-remaining:\s*0\s*$", r.stdout or "", re.I | re.M))


RUNTOKEN_FLOOR = int(os.environ.get("RUNTOKEN_FLOOR", "200"))


def _rt_empty_file():
    return os.path.join(os.environ.get("RIVAL_SNAP_DIR") or os.environ.get("PR_GATE_DIR") or W, "runtoken-empty")


def runtoken_empty(now=None):
    try:
        return (time.time() if now is None else now) < float(open(_rt_empty_file()).read().split()[0])
    except (OSError, ValueError, IndexError):
        return False


def _mark_runtoken_empty(r, args):
    reset = None
    m = re.search(r"^x-ratelimit-reset:\s*(\d+)", r.stdout or "", re.I | re.M)
    if m:
        reset = float(m.group(1))
    if reset is None:
        try:                                   # rate_limit is free and answers even at 0
            q = run(["gh", "api", "rate_limit", "--jq", ".resources.core.reset"], timeout=20,
                    env=dict(os.environ, GH_TOKEN=READ_TOKEN))
            reset = float(q.stdout.strip())
        except (ValueError, Exception):
            reset = time.time() + 600
    try:
        f = _rt_empty_file()
        os.makedirs(os.path.dirname(f), exist_ok=True)
        with open(f + ".%d.tmp" % os.getpid(), "w") as o:
            o.write(f"{reset:.0f} {time.time():.0f} {' '.join(args[:2])[:80]}\n")
        os.replace(f + ".%d.tmp" % os.getpid(), f)
    except OSError:
        pass
    log(f"RUN-TOKEN-EMPTY: run token at its hourly limit until {time.strftime('%H:%M:%S', time.gmtime(reset))} UTC; "
        "reads go to PR_TOKEN")


def gh(args, write=False, timeout=120):
    """gh with the run's own token for reads, PR_TOKEN for writes. Retries transient errors. A read refused for the
    run token's primary rate limit goes to PR_TOKEN (RUN-TOKEN-EMPTY above)."""
    # reads use the run's own GITHUB_TOKEN: PR_TOKEN's API limit is shared by the PC and every PR creation (20:27 UTC
    # 26 Nov: the account hit its limit and gh pr create failed on a wave), so it takes reads only while the run token is
    # empty
    fb = not write and READ_TOKEN and PR_TOKEN and os.environ.get("RUNTOKEN_FALLBACK", "1") != "0"
    if write:
        toks = [PR_TOKEN]
    elif fb and runtoken_empty():
        toks = [PR_TOKEN]
    else:
        toks = [READ_TOKEN or ("" if os.environ.get("GITHUB_ACTIONS") else PR_TOKEN)]
    r = None
    toks = [x for x in toks if x]
    i = 0
    while i < len(toks):                        # a list that can grow by PR_TOKEN (run token empty)
        t = toks[i]; i += 1
        for att in range(3):
            r = run(["gh"] + args, timeout=timeout, env=dict(os.environ, GH_TOKEN=t))
            if fb and t == READ_TOKEN and (r.stdout or "").startswith("HTTP/"):   # Lead 09:34: under the floor = switch
                m = re.search(r"^x-ratelimit-remaining:\s*(\d+)\s*$", r.stdout, re.I | re.M)   # before it is empty
                if m and int(m.group(1)) < RUNTOKEN_FLOOR and not runtoken_empty():
                    _mark_runtoken_empty(r, args)
            if r.returncode == 0:
                return r
            if fb and t == READ_TOKEN and primary_rl(r):
                _mark_runtoken_empty(r, args)
                toks.append(PR_TOKEN)
                break
            if not TRANSIENT.search(r.stderr + r.stdout):
                break
            time.sleep(5 * (att + 1))
    LAST_GH[0] = r
    raise RuntimeError("gh " + " ".join(args[:3]) + ": " + (r.stderr.strip()[:200] if r else "no token"))


LAST_GH = [None]


def gh_cond(args, timeout=60):
    """for ghcond.get: the CompletedProcess even when gh exits non-zero (w12 07:02: `gh api -i` exits 1 on a 304, which
    gh() raises on); ghcond reads the status line and decides (304 = cached body, anything else non-2xx = fail closed)"""
    LAST_GH[0] = None
    try:
        return gh(args, timeout=timeout)
    except RuntimeError as e:
        if LAST_GH[0] is not None:
            return LAST_GH[0]
        return subprocess.CompletedProcess(args, 1, "", str(e))


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
TL_HDR = [None]          # header epoch of the last taken list read: every PR created before it is in the list (A19)
TL_COMPLETE = [True]     # W6 43099ec6 (Lead ruling A3): header field 7 "complete"; partial or old format = not the authority


TL_T = [0.0]


def taken_list():
    if not _TL:
        _TL.append(_taken_list())
        TL_T[0] = time.time()
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
        age = time.time() - int(t[0].split()[2])
        if not t or age > 180:
            log("taken list: stale or missing header (fail closed)")
            return None
    except (IndexError, ValueError):
        log("taken list: unreadable header (fail closed)")
        return None
    rows = {l.split()[0]: l.split()[2] for l in t[1:] if len(l.split()) >= 3}
    # Lead 05:32 A20: a fresh list whose header says "steps 0" is a legitimate empty list; reject only a list whose row
    # count differs from its header (truncated) or a header without the count
    m = re.search(r"\bsteps (\d+)\b", t[0])
    if not m or int(m.group(1)) != len(rows):
        log(f"taken list: header says {m.group(1) if m else 'no count'}, {len(rows)} rows (truncated, fail closed)")
        return None
    h = t[0].split()
    TL_COMPLETE[0] = len(h) > 7 and h[6] == "complete"
    log(f"taken list: fresh, steps {len(rows)}, {age:.0f} s old" +
        ("" if TL_COMPLETE[0] else ", PARTIAL (or old format): every open PR is read by the snapshot"))
    TL_HDR[0] = int(t[0].split()[2])
    return rows


def race_check(step_id):
    """Blocking PRs. A step not on the fresh taken list has no PR from anyone: no API call at all. Otherwise (on the
    list, or the list is stale) the GitHub search below, on the run's own token."""
    _TL.clear()                          # fresh copy right before the push
    tl = taken_list()
    if tl is not None and not TL_COMPLETE[0]:     # A3: a partial list proves nothing about absent units
        rv = rival_now(step_id, SNAP_MAX_AGE_S)
        log("race check: taken list partial, full open sweep:", rv or "clear")
        if rv:
            return [{"number": "?", "state": "OPEN", "ours": False, "why": rv}]
        return []
    if tl is not None and step_id not in tl:
        log("race check: not on the taken list (no API call)")
        return []
    if tl is not None and tl.get(step_id) == HANDLE:
        return [{"number": "?", "state": "OPEN", "ours": True, "why": "our PR on the taken list"}]
    if tl is not None and step_id in tl:      # A19: another author's PR on the list is a rival; no search, no file reads
        return [{"number": "?", "state": "OPEN", "ours": False, "why": f"taken list: first PR by {tl[step_id]}"}]
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
        rec = gate_answer_lease(gid)     # W6 B10: the earlier run died after the grant, before record_lease
        if rec:
            dg().record_lease(gid, rec)
            return rec, "recovered the lease from the gate's answer lease/" + gid
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


RIVAL_WINDOW_S = 180     # the taken list (authority for older PRs) is accepted up to 180 s old: scan newer open PRs
RIVAL_MAX_PAGES = 10
UNIT_TOKEN = re.compile(r"(?<![A-Za-z0-9_-])L-[a-z0-9]+(?:-[a-z0-9]+)*-\d+(?![A-Za-z0-9_-])")
_FILES = {}


def pr_files(n):
    """changed file paths of an upstream PR (all pages). Raises on any read error: a failed read is never "no files"
    (red team X13)."""
    if n not in _FILES:
        fs, pg = [], 1
        while True:
            r = gh(["api", f"repos/{UP}/pulls/{n}/files?per_page=100&page={pg}"])
            if r.returncode:
                raise RuntimeError(f"files of #{n}: rc={r.returncode} {r.stderr.strip()[:80]}")
            got = json.loads(r.stdout)
            if not isinstance(got, list):
                raise RuntimeError(f"files of #{n}: not a list")
            fs += [f.get("filename") for f in got]
            if len(got) < 100 or pg >= 30:
                break
            pg += 1
        _FILES[n] = fs
    return _FILES[n]


SNAP_MAX_AGE_S = 5       # A19: one snapshot shared by every drain worker
SNAP_CREATE_AGE_S = float(os.environ.get("SNAP_CREATE_AGE_S", "2"))   # Lead 06:12: at gh pr create at most 2 s old
SNAP_DIR = os.environ.get("RIVAL_SNAP_DIR") or os.environ.get("PR_GATE_DIR") or W
SNAP_PAGE, SNAP_MAX_PAGES = 100, 10     # w12 07:16: 100 a page = one read per build in a wave (40 PRs a minute); 304 when unchanged
FILE_UNIT_RX = re.compile(r"lean/PEqualNP/Outside/(L_[a-z0-9]+(?:_[a-z0-9]+)*_\d+|V_[a-z0-9]+(?:_[a-z0-9]+)*_\d+__k\d+)\.lean")


def file_unit(f):
    m = FILE_UNIT_RX.fullmatch(f or "")
    if not m:
        return None
    u = m.group(1)
    return ("L_" + u[2:].split("__k")[0] if u.startswith("V_") else u).replace("_", "-")


def _build_snapshot(files):
    """taken list (fresh fetch) + every open PR created after its header minus 30 s, with its units by title, branch
    and changed files. Older PRs are in the taken list (takenpub.py maps every open PR by file path). Raises on any
    failed read (fail closed)."""
    t_build = None    # R3 + Lead 06:52: stamped right before the FIRST open-pulls page request (the read that sees new
    # PRs); the taken list is reused up to 10 s and is covered by the header-30 s window, so it does not age the snapshot
    if time.time() - TL_T[0] > 10:          # canary A2: a list fetched in the last 10 s is reused (1 s a fetch)
        _TL.clear()
    tl = taken_list()
    if tl is None:
        raise RuntimeError("taken list missing, older than 180 s or truncated (fail closed)")
    full = not TL_COMPLETE[0]               # A3: partial list -> every open PR (100 a page), not only the newest
    cut = -1e18 if full else TL_HDR[0] - 30
    size, maxp = (100, 60) if full else (SNAP_PAGE, SNAP_MAX_PAGES)
    recent, seen_n = [], set()
    dur = {}
    t_b0 = time.time(); nfr = [0]

    def page(k):
        # 16.7: read with If-None-Match: an unchanged page is a 304 and costs nothing of the run token's hourly
        # limit; any failed read raises (fail closed)
        t_rd = time.time()
        try:
            pulls, counted, rem = ghcond.get(f"repos/{UP}/pulls?state=open&sort=created&direction=desc&per_page={size}&page={k}",
                                             gh=gh_cond)
            dur[k] = time.time() - t_rd
        except ghcond.ReadFail as e:
            raise RuntimeError(f"open pulls page {k}: {e}")
        if not isinstance(pulls, list):
            raise RuntimeError(f"open pulls page {k}: not a list")
        old = False
        for p in pulls:
            c = time.mktime(time.strptime(p["created_at"][:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone
            if c < cut:
                old = True
                continue
            who = (p.get("user") or {}).get("login") or "?"
            if who == HANDLE or p["number"] in seen_n:
                continue
            seen_n.add(p["number"])
            us = set(UNIT_TOKEN.findall(p.get("title") or "")) | \
                set(UNIT_TOKEN.findall(((p.get("head") or {}).get("ref") or "").replace("_", "-")))
            key = f"{p['number']}:{(p.get('head') or {}).get('sha') or ''}"
            todo.append((p["number"], who, us, key))
        return old or len(pulls) < size

    def fill():
        """canary 51e630d7: a cold file cache cost 82 serial files reads = 36.7 s on the first build of a drain;
        the missing file lists are read 8 at a time, any failure raises (fail closed)"""
        need = sorted({(n, key) for n, _, _, key in todo if key not in files})
        if need:
            nfr[0] += len(need)
            with ThreadPoolExecutor(min(8, len(need))) as ex:
                got = list(ex.map(lambda nk: (nk[1], sorted({u for u in map(file_unit, pr_files(nk[0])) if u})), need))
            files.update(dict(got))
        for n, who, us, key in todo:
            recent.append({"n": n, "who": who, "units": sorted(us | set(files[key])), "by_file": sorted(set(files[key]) - us)})
        todo.clear()

    todo = []
    for k in range(1, maxp + 1):
        if k == 1:
            t_build = time.time()
        last = page(k)
        fill()
        if last:
            if k > 1:           # w12 07:16: several pages took time; page 1 (the newest PRs) is read again last and
                t_build = time.time()     # the snapshot is stamped at THAT request (usually a 304)
                page(1)
                fill()
            return {"t": t_build, "d": round(dur.get(1, 0.0), 3), "hdr": TL_HDR[0], "taken": tl, "recent": recent,
                    "files": files, "rl": ghcond.STATS["remaining"], "full": full,
                    "b": round(time.time() - t_b0, 2), "pages": len(dur), "fr": nfr[0]}
    raise RuntimeError(f"more than {maxp} pages of open PRs since the taken list (fail closed)")


SNAP_READ_MAX_S = 6.0    # HARDENING 16.12: a newest-page read slower than this is thrown away (SNAP-SLOW)


def snap_fresh(snap, bound, now=None):
    """HARDENING 16.12 (Lead 07:18): what must be fresh is the newest-page read (the taken list covers everything before
    its header). Fresh = that read STARTED at most max(bound, d + 1 s) ago, d its own duration, and d <= 6 s."""
    now = time.time() if now is None else now
    d = float(snap.get("d") or 0.0)
    return d <= SNAP_READ_MAX_S and 0 <= now - snap["t"] <= max(bound, d + 1.0)


def _snap_note(snap):
    """one line per build in SNAP_DIR/snapd.log (newest-page read duration), read by drain.py for the per-drain
    p50/p95/max; a read over 6 s also leaves SNAP_DIR/snapslow for the drain's SNAP-SLOW alert"""
    try:
        with open(os.path.join(SNAP_DIR, "snapd.log"), "a") as o:
            o.write(f"{snap['t']:.1f} {snap.get('d', 0):.3f}\n")
        if float(snap.get("d") or 0) > SNAP_READ_MAX_S:
            with open(os.path.join(SNAP_DIR, "snapslow"), "w") as o:
                o.write(f"{time.time():.0f} {snap.get('d', 0):.1f}\n")
    except OSError:
        pass


# HARDENING 16.14 (Lead 07:43, ONE READER, NO CONVOY): while the drain's refresher is alive (heartbeat at most
# REFRESHER_HB_S old) it is the ONLY reader of the halt refs and the rival pages; a worker waits for the refresher's
# next copy and never reads itself. A check is satisfied by a copy whose read STARTED after the worker asked (no age
# re-check after a wait). The 16.12 bound is checked only right before the create (final=True): on a miss the worker
# waits for the next refresher copy, at most 3 times, then SNAP-SLOW and no PR (unit unseen, retried). Refresher dead
# (its heartbeat went stale): one inline read under the lock, alert REFRESHER-DEAD. No refresher at all (one run per
# branch, drills): inline reads as before, still without the age re-check after a lock wait.
REFRESHER_HB_S = float(os.environ.get("REFRESHER_HB_S", "5"))
COPY_WAIT_S = float(os.environ.get("COPY_WAIT_S", "90"))   # Lead 08:12: a cold first build (36 s seen) is waited for
REFRESHER_STUCK_S = float(os.environ.get("REFRESHER_STUCK_S", "90"))  # a refresher loop with no finished pass this long = dead
IS_REFRESHER = [False]
WREADS = {"snap": 0, "halt": 0}          # GitHub reads made by THIS process outside the refresher (16.14 case)


def _hb_age(now=None):
    try:
        return (time.time() if now is None else now) - float(open(os.path.join(SNAP_DIR, "refresh.hb")).read().split()[0])
    except (OSError, ValueError, IndexError):
        return None


def refresher_alive():
    a = _hb_age()
    return not IS_REFRESHER[0] and a is not None and -1 <= a <= REFRESHER_HB_S


def _refdead(what):
    """the refresher ran in this drain (heartbeat file) but went stale: the drain alerts REFRESHER-DEAD"""
    if IS_REFRESHER[0] or _hb_age() is None:
        return
    try:
        with open(os.path.join(SNAP_DIR, "refdead"), "w") as o:
            o.write(f"{time.time():.0f} {what} heartbeat {_hb_age():.0f} s old\n")
    except OSError:
        pass


def _load(f):
    try:
        return json.load(open(f))
    except Exception:
        return None


def wait_copy(f, ok, timeout=None):
    """16.14: wait (file reads only, no lock, no GitHub read) for a copy of the shared file f with ok(copy); None when
    the refresher dies or nothing comes within timeout"""
    t_end = time.time() + (COPY_WAIT_S if timeout is None else timeout)
    while time.time() < t_end:
        c = _load(f)
        if c is not None and ok(c):
            return c
        if not refresher_alive():
            return None
        time.sleep(0.1)
    return None


def rival_snapshot(max_age=None, final=False):
    """the shared snapshot (16.14 above): max_age 0 = the refresher's own forced read (written whatever its age);
    final = the last check before a create, judged by snap_fresh(max_age) (16.12)"""
    ask = time.time()
    max_age = SNAP_MAX_AGE_S if max_age is None else max_age
    os.makedirs(SNAP_DIR, exist_ok=True)
    f = os.path.join(SNAP_DIR, "rival_snap.json")
    old = _load(f)
    if max_age > 0 and old and snap_fresh(old, max_age):
        return old                     # lock-free: a fresh copy answers every check, the final one too
    if max_age > 0 and refresher_alive():
        if final:
            last = old["t"] if old else 0.0
            for k in range(3):
                c = wait_copy(f, lambda c: c["t"] > last)
                if c is None:
                    break                              # refresher died while we waited: inline below
                if snap_fresh(c, max_age):
                    return c
                last = c["t"]
            else:
                try:
                    with open(os.path.join(SNAP_DIR, "snapslow"), "w") as o:
                        o.write(f"{time.time():.0f} {float(c.get('d') or 0):.1f}\n")
                except OSError:
                    pass
                raise RuntimeError(f"SNAP-SLOW: 3 refresher copies in a row missed the 16.12 bound max({max_age}, d + 1) "
                                   f"(last read {float(c.get('d') or 0):.1f} s)")
        else:
            c = wait_copy(f, lambda c: c["t"] > ask)
            if c is not None:
                return c
        _refdead("rival snapshot")
    elif max_age > 0:
        _refdead("rival snapshot")
    with open(os.path.join(SNAP_DIR, "rival_snap.lock"), "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        old = _load(f) or {}
        if max_age > 0 and old.get("t") and (snap_fresh(old, max_age) or (not final and old["t"] > ask)):
            return old                 # 16.14 (2): a read that started after we asked, no age re-check
        if not IS_REFRESHER[0]:
            WREADS["snap"] += 1
        snap = _build_snapshot(dict(old.get("files") or {}))
        _snap_note(snap)
        if final:                      # inline (no live refresher): the 16.12 bound before the create
            for _ in range(3):
                if snap_fresh(snap, max_age):
                    break
                WREADS["snap"] += 1
                snap = _build_snapshot(dict(snap.get("files") or {}))
                _snap_note(snap)
            else:
                if not snap_fresh(snap, max_age):
                    raise RuntimeError(f"snapshot {time.time() - snap['t']:.1f} s old, newest-page read {snap.get('d', 0):.1f} s, "
                                       f"after 4 builds (16.12 bound max({max_age}, d + 1), d <= {SNAP_READ_MAX_S:.0f})")
        with open(f + ".tmp", "w") as o:
            json.dump(snap, o)
        os.replace(f + ".tmp", f)
        log(f"rival snapshot: taken {len(snap['taken'])} rows (header {time.time() - snap['hdr']:.0f} s old), "
            f"{len(snap['recent'])} open PRs since, file cache {len(snap['files'])}, build {snap.get('b')} s, "
            f"{snap.get('pages')} page reads, {snap.get('fr')} files reads, full sweep {snap.get('full')}")
        return snap


def rival_now(gid, max_age=None, final=False):
    """Another author's PR on the unit, right before we decide and again right before gh pr create (A19 design, Lead
    05:40): the taken list is the authority for every PR created before its header (REST publisher, units by title,
    branch AND changed files of every open PR); open PRs created after the header minus 30 s are read here, with their
    file paths, once per snapshot shared by all drain workers. Any failed read = rival (no PR)."""
    try:
        snap = rival_snapshot(max_age, final)
    except Exception as e:
        return "rival check failed: " + str(e)[:120]
    STG["snap_age"] = round(time.time() - snap["t"], 1)
    who = snap["taken"].get(gid)
    if who not in (None, HANDLE):
        return f"taken list: first PR by {who}"
    for p in snap["recent"]:
        if gid in p["units"]:
            return f"#{p['n']} by {p['who']}" + (" (file path)" if gid in p.get("by_file", []) else "")
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
        gj = gaps_json()
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
            # Lead 05:32 canary A: the dry run makes the same live reads as the bare path (taken list, open pulls,
            # files, fresh export) so a read that fails only inside the Action shows here, with no claim and no PR
            t_d = time.time()
            rv = rival_now(gid)
            STG["dry_rival"] = round(time.time() - t_d, 1)
            log("dry run: rival_now:", rv or "clear")
            if rv:
                return False, "dry run: rival: " + rv, None
            t_d = time.time()
            try:
                g2 = next((x for x in gaps_json()["gaps"] if x["id"] == gid), None)
            except Exception as e:
                return False, "dry run: fresh gaps read failed " + repr(e)[:80], None
            STG["dry_gaps"] = round(time.time() - t_d, 1)
            if g2 is None or g2.get("held_now") or (g2.get("holders_now") or 0) > 0:
                return False, "dry run: " + ("unit missing from the fresh gaps export" if g2 is None else "held in the mirror"), None
            log("dry run: fresh export lists", gid, "unheld")
            return True, "clear (dry run: no gate request; rival_now clear; fresh export unheld)", None
        # GATEWAY v1 section 4 (Lead 16:50 UTC 26 Nov), in code: finished proof -> ask deskgate for the lease. Lease ok
        # within 60 s -> PR with the lease. Else, if GitHub shows no rival PR now and the mirror shows no holder -> PR
        # without a lease. Else skip (no backup PRs). Gate closed or paused -> the unleased branch.
        old = dg().lease_of(gid)
        if old:
            return True, "clear (our recorded lease reused)", old
        tpl = str((g.get("faithful_by_template") or {}).get("template") or "")
        if FILE_FIRST and tpl not in CLAIM_FIRST and (FILE_FIRST == "*" or FILE_FIRST in tpl):
            # Lead 21:59 FILE_FIRST: no claim (open-gate claims on a fresh slice all came back held = no PR); the bare
            # path below decides: PR without a lease when no rival PR and no holder in the mirror. Late lease later.
            why = f"no lease: file first ({tpl})"
            log("gate:", gid, "skipped: file first", tpl or "(no template)")
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
            rv = rival_now(gid)                  # mintdrill A1/A2/A3/A4: file path, all recent pages, taken list usable
            if rv:
                case = "rival: " + rv
        if case == "bare":
            try:
                g2 = next((x for x in gaps_json()["gaps"] if x["id"] == gid), None)
            except Exception:
                g2 = {"held_now": True}          # cannot tell: treat as held (fail closed)
            if g2 is None:
                case = "unit missing from the fresh gaps export"     # mintdrill A5: settled or withdrawn = no PR
            elif g2.get("held_now") or (g2.get("holders_now") or 0) > 0:
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


def fork_head(gid):
    """sha of this fork's branch <gid> (the PR head), None when it does not exist. A git read, no API call. Raises when
    unreadable (callers fail closed: no push, no PR)."""
    for k in range(3):
        r = run(["git"] + (auth_cfg() if PR_TOKEN else []) + ["ls-remote", f"https://github.com/{FORK}.git", f"refs/heads/{gid}"],
                timeout=60)
        if r.returncode == 0:
            o = r.stdout.split()
            return o[0] if o else None
        time.sleep(2)
    raise RuntimeError("fork branch unreadable")


def our_prs_on_branch(gid, state):
    out = gh(["api", f"repos/{UP}/pulls?head={HANDLE}:{gid}&state={state}", "--jq", ".[].html_url"])
    if out.returncode:
        raise RuntimeError(f"PR lookup failed rc={out.returncode}")
    return out.stdout.split()


def open_pr_for_branch(gid):
    """Our own open PR whose head is this fork's branch <gid> (exact, no search index lag). No API call when neither
    the fresh taken list nor the fork has anything for the step (W6 mintfail: a PR younger than the taken list header
    was missed and a re-run pushed onto it)."""
    tl = taken_list()
    if tl is not None and gid not in tl and fork_head(gid) is None:
        return None
    out = our_prs_on_branch(gid, "open")
    return out[0] if out else None


def git(*a, env=None, timeout=300):
    return run(["git", "-C", TREE] + list(a), env=env, timeout=timeout)


def auth_cfg():
    b = base64.b64encode(f"x-access-token:{PR_TOKEN}".encode()).decode()
    return ["-c", f"http.https://github.com/.extraheader=AUTHORIZATION: basic {b}"]


UPBASE_RETRY_S = float(os.environ.get("UPBASE_RETRY_S", "60"))


def upbase_ref(base):
    """W6 push canary + infra (08:50 UTC 27 Nov): the push sends only the new objects when the fork ADVERTISES a ref at
    the commit's parent (the upstream base): git push then leaves out everything reachable from it (about 500 bytes).
    A fork tip based on an older upstream left the whole tree in the pack (182-228 MB per unit, and lazy blob fetches
    in a blobless clone). One ref refs/heads/upbase/<base sha8> per base, made once (REST create of a ref at the
    upstream sha: a fork shares its objects with upstream), shared by the drain's workers through SNAP_DIR.
    Returns the ref name, or None (then the old fork-tip base is used)."""
    name = f"upbase/{base[:8]}"
    mark = os.path.join(SNAP_DIR, f"upbase-{base[:12]}.ok")
    nomark = os.path.join(SNAP_DIR, f"upbase-{base[:12]}.no")     # red team R2: a refused create is not retried per unit
    if os.path.exists(mark):
        return name
    url = f"https://github.com/{FORK}.git"
    try:
        if time.time() - os.path.getmtime(nomark) < UPBASE_RETRY_S:
            return None
    except OSError:
        pass
    try:
        os.makedirs(SNAP_DIR, exist_ok=True)
        with open(os.path.join(SNAP_DIR, "upbase.lock"), "w") as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            if os.path.exists(mark):
                return name
            try:
                if time.time() - os.path.getmtime(nomark) < UPBASE_RETRY_S:
                    return None
            except OSError:
                pass
            r = run(["git"] + auth_cfg() + ["ls-remote", url, f"refs/heads/{name}"], timeout=15)
            have = r.returncode == 0 and r.stdout.split()[:1] == [base]
            if not have:
                r = run(["gh", "api", "-X", "POST", f"repos/{FORK}/git/refs", "-f", f"ref=refs/heads/{name}", "-f", f"sha={base}"],
                        timeout=15, env=dict(os.environ, GH_TOKEN=PR_TOKEN))
                have = r.returncode == 0 or "Reference already exists" in (r.stdout + r.stderr)
                # red team R2 (Lead 09:22): NEVER push the whole base instead (182-228 MB under this lock, every worker
                # waiting): a refused create means the old fork-tip base for UPBASE_RETRY_S
            if have:
                open(mark, "w").write(f"{time.time():.0f}\n")
                return name
            open(nomark, "w").write(f"{time.time():.0f}\n")
            log("upbase: no ref at the base (fork-tip base for this unit):", (r.stderr or r.stdout or "").strip()[:150])
    except Exception as e:
        log("upbase failed:", repr(e)[:150])
    return None


PUSH_REFUSED = re.compile(r"\b(429|403)\b|Too Many Requests|rate limit|secondary rate", re.I)


def push_branch(c, gid):
    url = f"https://github.com/{FORK}.git"
    t = time.time()
    base = git("rev-parse", f"{c}^").stdout.strip()
    ub = upbase_ref(base) if base else None
    STG["upbase"] = round(time.time() - t, 3)
    if not ub:
        # fallback: a recent fork branch as negotiation base (its own base may be far behind: a large pack)
        refs = git("ls-remote", url, "refs/heads/L-*", timeout=120).stdout.split("\n")
        nums = sorted(((int(m.group(1)), m.group(0)) for l in refs for m in [re.search(r"refs/heads/L-meta-(\d+)$", l)] if m),
                      reverse=True)
        if nums:
            git("fetch", "-q", "--depth=1", url, f"{nums[0][1]}:refs/fork/tip", timeout=180)
    for att in range(4):
        # create-only (Lead 06:12): the ref must not exist yet; an existing head is never rewritten
        r = run(["git"] + auth_cfg() + ["-C", TREE, "push", "-q", f"--force-with-lease=refs/heads/{gid}:", url,
                                        f"{c}:refs/heads/{gid}"], timeout=600)
        if r.returncode == 0:
            return None
        d = os.environ.get("PR_GATE_DIR")
        if d and PUSH_REFUSED.search(r.stderr):
            # Lead 09:10 (W5 PUSH-429 at 08:49:57; GitHub's repository limit: about 6 pushes a minute): a refused head
            # push is a refusal under 16.13 like a refused create: every worker stops for refusal_wait(), rate halved,
            # the 4th ends the drain's creates; this unit waits out the stall, then pushes again
            k, wait, rate = bucket_refusal(d, {}, "push: " + r.stderr.strip()[:200])
            if os.path.exists(os.path.join(d, "giveup")):
                return "push refused, creates given up: " + r.stderr.strip()[:200]
            try:
                until = float(open(os.path.join(d, "stall")).read())
            except (OSError, ValueError):
                until = time.time() + wait
            time.sleep(max(0.0, until - time.time()))
            continue
        if not TRANSIENT.search(r.stderr):
            return r.stderr.strip()[:300]
        log("push retry", r.stderr.strip()[:150].replace("\n", " | "))
        time.sleep(5 * (att + 1))
    return r.stderr.strip()[:300]


PR_PER_MIN = int(os.environ.get("PR_PER_MIN", "70"))       # Lead 06:12: GitHub documents 80/min and 500/hour per token
PR_PER_HOUR = int(os.environ.get("PR_PER_HOUR", "480"))


def bucket_wait(d, now):
    """PR-create budget shared by every worker of a drain (file PR_GATE_DIR/creates.log under flock): 0 = take a
    create now (recorded), else the seconds to wait. A stall (PR_GATE_DIR/stall: epoch until) after a 403/429 blocks
    every worker until it ends."""
    with open(os.path.join(d, "creates.lock"), "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            until = float(open(os.path.join(d, "stall")).read())
        except Exception:
            until = 0.0
        if now < until:
            return until - now
        f = os.path.join(d, "creates.log")
        try:
            ts = [float(x) for x in open(f).read().split() if now - float(x) < 3600]
        except Exception:
            ts = []
        if os.path.exists(os.path.join(d, "giveup")):
            return float("inf")                      # 16.13: four refusals in this drain: no create any more
        last_min = [t for t in ts if now - t < 60]
        if len(last_min) >= gate_rate(d):
            return 60 - (now - min(last_min)) + 0.05
        if len(ts) >= PR_PER_HOUR:
            return 3600 - (now - min(ts)) + 0.05
        ts.append(now)
        with open(f + ".tmp", "w") as o:
            o.write("\n".join(f"{t:.3f}" for t in ts))
        os.replace(f + ".tmp", f)
        return 0.0


PR_RATE_FLOOR = 10
RL_HDRS = ("retry-after", "x-ratelimit-limit", "x-ratelimit-remaining", "x-ratelimit-used", "x-ratelimit-reset",
           "x-ratelimit-resource")


def refusals(d):
    try:
        return int(open(os.path.join(d, "refusals")).read().strip() or 0)
    except (OSError, ValueError):
        return 0


def gate_rate(d):
    """HARDENING 16.13 (Lead 07:25) (2): the drain's create rate, halved after every refusal (70, 35, 17, floor 10)"""
    k = refusals(d)
    return max(PR_RATE_FLOOR, PR_PER_MIN >> k) if k else PR_PER_MIN


def refusal_wait(k, hdr, now):
    """16.13 (1): retry-after if present, else until x-ratelimit-reset when x-ratelimit-remaining is 0, else 60 s;
    the k-th refusal of a drain waits at least 60 * 2^(k-1) s (60, 120, 240)"""
    ra, rem, rs = (str(hdr.get(x) or "").strip() for x in ("retry-after", "x-ratelimit-remaining", "x-ratelimit-reset"))
    if ra.isdigit():
        base = float(ra)
    elif rem == "0" and rs.isdigit():
        base = max(0.0, float(rs) - now) + 1.0
    else:
        base = 60.0
    return max(base, 60.0 * 2 ** (k - 1)) if k > 1 else base


def bucket_refusal(d, hdr, why, now=None):
    """16.13: GitHub refused a create (403/429/secondary limit). Every worker of the drain stops creating for
    refusal_wait(); the rate is halved; the 4th refusal ends the drain's creates (PR_GATE_DIR/giveup, PR-STALL-GIVEUP).
    Returns (k, wait, rate)."""
    now = time.time() if now is None else now
    with open(os.path.join(d, "creates.lock"), "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        k = refusals(d) + 1
        with open(os.path.join(d, "refusals"), "w") as o:
            o.write(str(k))
        wait = refusal_wait(k, hdr, now)
        try:
            until = float(open(os.path.join(d, "stall")).read())
        except Exception:
            until = 0.0
        with open(os.path.join(d, "stall"), "w") as o:
            o.write(str(max(until, now + wait)))
        if k >= 4:
            with open(os.path.join(d, "giveup"), "w") as o:
                o.write(f"{now:.0f} {why[:200]}".replace("\n", " "))
    rate = gate_rate(d)
    hs = " ".join(f"{x}={hdr.get(x, '')}" for x in RL_HDRS)
    if k >= 4:
        log(f"PR-STALL-GIVEUP refusal {k} in this drain: no more creates in this drain (units stay unseen) ({hs})")
    else:
        log(f"PR-STALL refusal {k}/4: every worker stops creating for {wait:.0f} s, rate now {rate}/min ({hs})")
    return k, wait, rate


def bucket_stall(d, seconds, why):
    """after a 403/429 on a create: no worker creates for `seconds` (the retry-after, else 60 s)"""
    with open(os.path.join(d, "creates.lock"), "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        with open(os.path.join(d, "stall"), "w") as o:
            o.write(str(time.time() + seconds))
    log(f"PR-STALL {seconds:.0f}s: every worker stops creating PRs ({why[:100]})")


class pr_gate:
    """Drain mode (drain.py, many submit.py at once on one runner): at most PR_GATE_N PR creations in flight (flock on
    PR_GATE_DIR/slot<k>; drain.py sets it from DRAIN_PR_SLOTS), and at most PR_PER_MIN creates a minute and
    PR_PER_HOUR an hour for the whole drain (bucket_wait). No PR_GATE_DIR (one run per branch): no gate."""
    def __enter__(self):
        self.f = None
        d = os.environ.get("PR_GATE_DIR")
        while d:
            for k in range(int(os.environ.get("PR_GATE_N", "2"))):
                f = open(os.path.join(d, f"slot{k}"), "w")
                try:
                    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB); self.f = f
                    break
                except OSError:
                    f.close()
            if self.f:
                break
            time.sleep(0.2)
        t0 = time.time()
        self.giveup = False
        while d:
            w = bucket_wait(d, time.time())
            if w == float("inf"):
                self.giveup = True               # 16.13: four refusals: this drain creates nothing more
                break
            if w <= 0:
                break
            time.sleep(min(w, 5))
        if d and time.time() - t0 > 0.5:
            STG["bucket_wait"] = round(time.time() - t0, 1)
        return self

    def __exit__(self, *a):
        if self.f:
            self.f.close()


def submit(gid, lease):
    # Lead 06:12 (W6 mintfail): the head branch Leg0shii:<ID> is created once with a create-only push and never
    # forced. If it exists: our open PR on it = done; our closed PR on it = stop (nothing reopens, I5); neither = the
    # earlier run died between push and create: open the PR from the existing commit.
    t_hd = time.time()
    try:
        head = fork_head(gid)
        STG["head"] = round(time.time() - t_hd, 3)
        if head:
            op = our_prs_on_branch(gid, "open")
            if op:
                return op[0], "ok (our PR on the existing branch)"
            if our_prs_on_branch(gid, "closed"):
                return None, "our PR on this branch was closed: no reopen (I5)"
            log("branch", gid, "exists at", head[:12], "with no PR: opening the PR from it (no push)")
            return create_pr(gid, lease)
    except RuntimeError as e:
        return None, "head check failed (fail closed): " + str(e)[:120]
    t_cm = time.time()
    t = time.time()
    base = git("rev-parse", "HEAD").stdout.strip()
    STG["g_revparse"] = round(time.time() - t, 3)
    if not base:
        return None, "no upstream main"
    t = time.time()
    if git("cat-file", "-e", f"{base}:{REL}").returncode == 0:
        return None, "file already in upstream main"
    STG["g_catfile"] = round(time.time() - t, 3)
    t = time.time()
    blob = git("hash-object", "-w", PROOF).stdout.strip()
    STG["g_hashobj"] = round(time.time() - t, 3)
    # lane tree (W7, 08:20 UTC 27 Nov): no index. The base tree's sub-trees along REL are read with ls-tree and the new
    # trees written bottom-up with mktree --missing (treebuild.py); the same tree sha as read-tree/update-index/write-tree
    # (treebuild_test.py). Was: read-tree of the whole upstream tree per unit, 59.5 s p50 at w28.
    t = time.time()
    try:
        tree = treebuild.tree_with_file(TREE, base, REL, blob)
        STG["tree_src"] = "mktree"
    except Exception as e:                   # never blocks a unit: the old index path, logged
        log("treebuild failed, index path:", str(e)[:120])
        idx = os.path.join(W, "submit.idx")
        env = dict(os.environ, GIT_INDEX_FILE=idx)
        if git("read-tree", base, env=env).returncode:
            return None, "read-tree failed"
        git("update-index", "--add", "--cacheinfo", f"100644,{blob},{REL}", env=env)
        tree = git("write-tree", env=env).stdout.strip()
        STG["tree_src"] = "index"
    STG["tree"] = round(time.time() - t, 3)
    t = time.time()
    changed = git("diff-tree", "--name-only", "-r", base, tree).stdout.split()
    STG["g_difftree"] = round(time.time() - t, 3)
    if changed != [REL]:
        return None, f"unexpected changed files {changed}"
    # rule 16.5 (2): a per-opener nonce, so two openers never build the same sha
    msg = gid + f"\n\nOpener-Nonce: cloud-{os.environ.get('GITHUB_RUN_ID', 'x')}-{os.urandom(6).hex()}" \
        "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n"
    cenv = dict(os.environ, GIT_AUTHOR_NAME=HANDLE, GIT_COMMITTER_NAME=HANDLE, GIT_AUTHOR_EMAIL=EMAIL, GIT_COMMITTER_EMAIL=EMAIL)
    t = time.time()
    c = git("commit-tree", tree, "-p", base, "-m", msg, env=cenv).stdout.strip()
    STG["g_committree"] = round(time.time() - t, 3)
    if not c:
        return None, "commit-tree failed"
    STG["commit"] = round(time.time() - t_cm, 3)     # whole stage, rev-parse to commit-tree (same span as before)
    # drain.py cuts each unit line at 200 chars, so the long TIMES line loses these: one short line of its own
    log("COMMIT-STAGES", gid, " ".join(f"{k}={STG[k]}" for k in ("commit", "tree", "tree_src", "head", "halt2", "g_revparse",
                                                               "g_catfile", "g_hashobj", "g_difftree", "g_committree") if k in STG))
    if DRY:
        tw = time.time()                 # rehearsal (Lead 08:12): the would-create time per unit, epoch to 0.001 s
        log(f"WOULD-CREATE {gid} {tw:.3f}"); log(sight_line(gid, tw))
        return "dry-run", f"would push {c[:12]} as {FORK}:{gid} and open the PR"
    t = time.time()
    err = push_branch(c, gid)
    STG["push"] = round(time.time() - t, 1)
    if err:
        return None, "push: " + err
    log("pushed", c[:12], "to", f"{FORK}:{gid}")
    return create_pr(gid, lease)


def pr_create_cmd(gid, body):
    """16.13 (3): the create through REST with the response headers (gh api -i), so a refusal's retry-after and
    x-ratelimit headers are seen and logged (gh pr create shows neither)"""
    return ["gh", "api", "-i", "-X", "POST", f"repos/{UP}/pulls", "-f", f"title={gid}", "-f", f"head={HANDLE}:{gid}",
            "-f", "base=main", "-f", f"body={body}"]


def parse_create(r):
    """(code, headers, url, text) from a create's CompletedProcess: `gh api -i` output (status line, headers, JSON),
    or the plain shape (a URL on stdout, "HTTP 403: ..." / "already exists" on stderr). Never the request body."""
    out, err = r.stdout or "", r.stderr or ""
    hdr, code, url, text = {}, 0, None, ""
    if out.startswith("HTTP/"):
        head, _, body = out.replace("\r\n", "\n").partition("\n\n")
        m = re.match(r"HTTP/\S+ (\d{3})", head)
        code = int(m.group(1)) if m else 0
        for ln in head.split("\n")[1:]:
            k, _, v = ln.partition(":")
            if k.strip().lower() in RL_HDRS:
                hdr[k.strip().lower()] = v.strip()
        try:
            j = json.loads(body)
            url = j.get("html_url") if 200 <= code < 300 else None
            text = " ".join([str(j.get("message", ""))] + [str(e.get("message", e) if isinstance(e, dict) else e)
                                                         for e in (j.get("errors") or [])])
        except Exception:
            text = body.strip()[:200]
    else:
        url = (re.findall(r"https://github\.com/\S+/pull/\d+", out) or [None])[0] if r.returncode == 0 else None
        m = re.search(r"HTTP (\d{3})", err + out)
        code = 201 if url else (int(m.group(1)) if m else (422 if "already exists" in err + out else 0))
        text = err.strip()[:300]
        for x in RL_HDRS:
            mm = re.search(r"(?i)%s:?\s*(\d+|\w+)" % re.escape(x), err + out)
            if mm:
                hdr[x] = mm.group(1)
        if code == 422 and not url:
            url = (re.findall(r"https://github\.com/\S+/pull/\d+", err + out) or [None])[0]
    return code, hdr, url, (text + " " + err.strip()[:120]).strip()


REFUSED = re.compile(r"secondary rate limit|submitted too quickly|abuse detection", re.I)


def sight_line(gid, now):
    """Lead 07:31: seconds from sight to create for every created PR. Sight = a "Sight: <epoch>" line in the ready
    commit message (the builder's first sight of the unit) when present; the ready commit time (READY_T) always."""
    m = re.search(r"(?mi)^Sight:\s*(\d{9,}(?:\.\d+)?)\s*$", os.environ.get("READY_MSG", ""))
    rt = os.environ.get("READY_T", "")
    sight = f"sight->create {now - float(m.group(1)):.1f} s" if m else "sight->create n/a (no Sight: line)"
    ready = f"ready->create {now - float(rt):.1f} s" if rt.isdigit() else "ready->create n/a"
    return f"SIGHT-TO-CREATE {gid} {sight}, {ready}, opener start->create {now - T_START:.1f} s"


def create_pr(gid, lease):
    r = None
    t_pr = time.time()
    url, ctext = None, ""
    for att in range(5):
        if stopped():                    # STOP may appear while this PR waited for a retry
            return None, "STOP file on upstream main"
        sc = site_closed_now()
        if sc:
            log("site-closed:", gid, sc, f"(before create attempt {att + 1}): held, retried when it reopens")
            return None, "site-closed: " + sc
        body = pr_body(lease)
        with pr_gate() as g:
            if getattr(g, "giveup", False):
                log("PR-STALL-GIVEUP:", gid, "no create (four refusals in this drain): unit stays unseen")
                return None, "stall-giveup: four create refusals in this drain"
            # Lead 06:12 a0 (w12 stall drill): before EVERY attempt, after any slot, bucket or backoff wait: the halt
            # switch, and for an unleased PR a rival snapshot at most SNAP_CREATE_AGE_S old (Lead 18:53)
            h, hwhy = filing_halted()
            if h:
                log("halted:", gid, hwhy, f"(before create attempt {att + 1})")
                return None, "halted: " + hwhy
            if not lease:
                rv = rival_now(gid, SNAP_CREATE_AGE_S, final=True)     # 16.14 (3): the 16.12 bound, last line
                if rv and rv.startswith("rival check failed"):     # a failed or late read: no PR now, the drain
                    log("SKIP", gid, f"no PR (attempt {att + 1}):", rv)  # retries (submitfail), the branch is kept
                    return None, rv
                if rv:
                    log("SKIP", gid, f"unleased PR not opened (attempt {att + 1}), rival", rv)
                    return None, "rival PR open: " + rv
            t_c = time.time()
            r = run(pr_create_cmd(gid, body), timeout=120, env=dict(os.environ, GH_TOKEN=PR_TOKEN))
        lat = time.time() - t_c
        code, hdr, url, ctext = parse_create(r)
        if url and code == 201:
            log(sight_line(gid, time.time()))
        if url and code == 201 and os.environ.get("PR_GATE_DIR"):
            try:                                    # Lead 07:27: accepted creates, counted per 10 s by drain.py
                with open(os.path.join(os.environ["PR_GATE_DIR"], "accepted.log"), "a") as o:
                    o.write(f"{time.time():.3f}\n")
            except OSError:
                pass
        if url:
            break                                   # created, or GitHub named our existing PR
        if code == 422 and "already exists" in ctext:
            try:                                    # REST does not name the existing PR: look it up (READ_TOKEN)
                op = our_prs_on_branch(gid, "open")
            except RuntimeError:
                op = []
            url = op[0] if op else None
            if url:
                break                               # an existing PR for our branch is a success
        hs = " ".join(f"{x}={hdr.get(x, '')}" for x in RL_HDRS)
        log(f"CREATE {gid} attempt {att + 1}: http {code} latency {lat:.2f} s {hs} {ctext[:160]!r}")
        refused = code in (403, 429) or (not 200 <= code < 300 and REFUSED.search(ctext))
        if refused and os.environ.get("PR_GATE_DIR"):
            k, wait, rate = bucket_refusal(os.environ["PR_GATE_DIR"], hdr, ctext)
            if k >= 4:
                STG["pr"] = round(time.time() - t_pr, 1)
                return None, "stall-giveup: four create refusals in this drain"
            if att == 4:
                break
            continue                                # the next attempt waits in pr_gate until the stall ends
        if not (refused or TRANSIENT.search(ctext)) or att == 4:
            break
        log("PR retry in", 30 * 2 ** att, "s:", ctext[:150])
        time.sleep(30 * 2 ** att)
    STG["pr"] = round(time.time() - t_pr, 1)
    LEASE[0] = lease
    return url, ("ok" if url else (ctext or (r.stderr if r else "")).strip()[:300])


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


HALT_MAX_AGE_S = float(os.environ.get("HALT_MAX_AGE_S", "2"))


def site_closed_now():
    """16.11: the drain's shared copy W/site.json (drain.py site_closed, at most 30 s old): why, or None. Missing or
    older than 120 s = None (a dead reader never stops filing)."""
    try:
        d = json.load(open(os.path.join(SNAP_DIR, "site.json")))
        if d.get("closed") and 0 <= time.time() - float(d["t"]) <= 120:
            return d.get("why") or "site not accepting"
    except Exception:
        pass
    return None


def filing_halted(max_age=None):
    """RC-b 1 (Lead 06:22): the halt switch, shared by every drain worker like the rival snapshot: one read at most
    HALT_MAX_AGE_S old in SNAP_DIR/halt.json (stamped at read START), kept fresh by the drain's refresher. A fresh copy
    is read without the lock; a stale or missing one (refresher dead, or no drain) means an inline read under the
    lock, never a stale answer. Anything unreadable = halted."""
    max_age = HALT_MAX_AGE_S if max_age is None else max_age
    if not os.environ.get("RIVAL_SNAP_DIR") or os.environ.get("FILING_FIXTURE") is not None:
        return _filing_halted_read()                 # one run per branch (no drain) or a fixture: inline
    f = os.path.join(SNAP_DIR, "halt.json")
    ask = time.time()
    h = _load(f)
    try:
        if h and 0 <= time.time() - h["t"] <= max_age:
            return bool(h["halted"]), h["why"]
    except Exception:
        pass
    if max_age > 0 and refresher_alive():          # 16.14 (4): the refresher's next copy, no own read
        c = wait_copy(f, lambda c: c["t"] > ask)
        if c is not None:
            return bool(c["halted"]), c["why"]
        _refdead("halt")
    elif max_age > 0:
        _refdead("halt")
    try:
        os.makedirs(SNAP_DIR, exist_ok=True)
        with open(os.path.join(SNAP_DIR, "halt.lock"), "w") as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            try:
                h = json.load(open(f))
                if 0 <= time.time() - h["t"] <= max_age or (max_age > 0 and h["t"] > ask):   # 16.14 (2)
                    return bool(h["halted"]), h["why"]
            except Exception:
                pass
            if not IS_REFRESHER[0]:
                WREADS["halt"] += 1
            t = time.time()
            hv, why = _filing_halted_read()
            with open(f + ".tmp", "w") as o:
                json.dump({"t": t, "halted": hv, "why": why}, o)
            os.replace(f + ".tmp", f)
            return hv, why
    except Exception as e:
        return True, "halt state error (fail closed): " + repr(e)[:100]


def _filing_halted_read():
    """Lead 05:10 HALT ON ONE REJECTION, rule 16.1 (haltrule.py): (halted, why) from the toolkit filing/stop/<n> and
    filing/go/<n> refs; unreadable = halted. FILING_FIXTURE = ls-remote text."""
    if os.environ.get("FILING_FIXTURE") is not None:
        txt, rc = os.environ["FILING_FIXTURE"], 0
    else:
        # live test 05:13: an anonymous ls-remote of the (private) toolkit fails in the Action -> read it like
        # gate_open_now, through the deskguard clone's authenticated origin; 3 tries 2 s apart (Lead 05:13)
        txt, rc = "", 1
        for k in range(3):
            try:
                r = run(["git", "-C", dg().REPO, "ls-remote", "origin", "refs/heads/filing/*"], timeout=30)
                txt, rc = r.stdout, r.returncode
            except Exception:
                txt, rc = "", 1
            if rc == 0:
                break
            time.sleep(2)
    return haltrule.verdict(txt, rc)


T_START = time.time()


def main():
    t0 = time.time()
    h, hwhy = filing_halted()             # Lead 05:10: before anything else (no guards, no desk, no PR); branch kept
    STG["halt1"] = round(time.time() - t0, 3)              # lane tree: guards split (halt1, prlookup, gaps, checkcore)
    if h:
        log("halted:", ID, hwhy)
        finish("halted", hwhy)
    if not re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*", ID) or len(ID) > 64:
        finish("error", f"bad step id {ID!r}")
    if not (MOD == ID.replace("-", "_") or re.fullmatch(r"V%s__k\d+" % re.escape(ID.replace("-", "_")[1:]), MOD)):
        finish("error", f"file name {MOD}.lean does not belong to {ID}")
    if os.path.getsize(PROOF) > SIZE_LIMIT:
        finish("formatfail", f"file is {os.path.getsize(PROOF)} bytes, over the CI limit {SIZE_LIMIT}")
    if not DRY and not PR_TOKEN:
        finish("skipped", "no PR_TOKEN secret: the PC watcher takes this file from pnp-toolkit ready/ instead")
    t_pl = time.time()
    try:
        url = open_pr_for_branch(ID)
    except Exception as e:
        finish("error", f"PR lookup failed: {e}")
    STG["prlookup"] = round(time.time() - t_pl, 3)
    if url and DRY:
        log("dry run: our PR is already open, testing the rest anyway:", url)
    elif url:
        old = None
        try:
            old = dg().lease_of(ID) if PR_TOKEN else None
        except Exception:
            pass
        if old:                          # W6: the earlier run died before its release; the PR is open, so release now
            release(old, "submitted")
        finish("exists", "our PR for this branch is already open (PC watcher or an earlier run)"
               + (f"; lease {old} released" if old else ""), url)
    # 1. guards (= formatscan on the PC)
    env = dict(os.environ, NODE=subprocess.run(["sh", "-c", "command -v node"], capture_output=True, text=True).stdout.strip())
    if MOD != ID.replace("-", "_"):
        env["REL_OVERRIDE"] = REL
    # 12:19 UTC 26 Nov (L-meta-19447): a file for a proposed, not yet listed step failed the gap guard as formatfail and
    # its ready/ branch was deleted, so the ready-wait path never ran. Unlisted: guards in prestage mode (no gap guard,
    # the file's own imports), then keep the branch; ready-wait.yml dispatches this job again at listing.
    unlisted = False
    t_gj = time.time()
    try:
        gj0 = gaps_json()
        env["GAPS_FILE"] = os.path.join(os.environ.get("RIVAL_SNAP_DIR") or os.environ.get("PR_GATE_DIR") or W, "gaps.json")
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
    STG["gaps"] = round(time.time() - t_gj, 3)
    if unlisted:
        imps = re.findall(r"^import\s+(\S+)", open(PROOF, errors="replace").read(), re.M) or ["PEqualNP.Defs"]
        env["PRESTAGE_IMPORTS"] = json.dumps(imps)
        log("not listed yet: prestage guards (imports", imps, ")")
    t_cc = time.time()
    r = run(["bash", os.path.join(os.path.dirname(os.path.abspath(__file__)), "checkcore.sh"), PROOF, ID, TREE,
             os.path.join(W, "guard"), "--quick"], env=env, timeout=600)
    STG["checkcore"] = round(time.time() - t_cc, 3)
    print(r.stdout[-3000:], r.stderr[-2000:], sep="\n", flush=True)
    git("clean", "-q", "-f", "--", "lean/PEqualNP/Outside/")          # the closure guard copied the file in
    if r.returncode:
        finish("formatfail", "guards: " + ((r.stdout + r.stderr).strip().splitlines() or ["?"])[-1][:200])
    log(f"guards passed ({time.time() - t0:.0f}s)")
    STG["guards"] = round(time.time() - t0, 1)
    STG["start"] = round(t0 - T_START, 1)      # opener start -> guards start (halt check, gaps read, setup)
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
    t_h2 = time.time()
    h, hwhy = filing_halted()             # Lead 05:10: again right before the PR (a stop may have come meanwhile)
    STG["halt2"] = round(time.time() - t_h2, 3)
    if h and not DRY:
        free_slot()
        log("halted:", ID, hwhy, "(before the PR)")
        finish("halted", hwhy + (f"; lease {lease} kept on claim/{ID}" if lease else ""))
    url, why2 = submit(ID, lease)
    if late and url and url != "dry-run":
        # late lease (Lead 13:37 probe): one claim through deskguard now that the PR is open; on a grant the PR body
        # gets the Lease line by edit, then the lease is released as for any submitted PR. Refused = PR stays as is.
        lid, lwhy = claim_unheld(ID, PRIO[0])
        log("late lease:", lwhy)
        if lid:
            body = pr_body(lid)
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
    if not url and why2.startswith("stall-giveup: "):
        finish("stall-giveup", why2[14:] + " (branch kept, unit unseen)")
    if not url and why2.startswith("site-closed: "):
        finish("site-closed", why2[13:] + " (branch kept)")
    if not url and why2.startswith("halted: "):
        finish("halted", why2[8:] + (f"; lease {LEASE[0]} kept on claim/{ID}" if LEASE[0] else ""))
    finish("submitted" if url else "submitfail", f"{why2}; {time.time() - t0:.0f}s after start", url)


REFRESH_S = float(os.environ.get("REFRESH_S", "0.8"))


def refresher():
    """RC-b 1 (Lead 06:22): `submit.py --refresh` (started by drain.py, one per drain): re-reads the halt switch and
    rebuilds the rival snapshot every REFRESH_S, so a worker holding a PR slot only reads files (no GitHub read inside
    the slot). It stops when its parent drain is gone or SNAP_DIR/refresh.stop exists. Each pass writes
    SNAP_DIR/refresh.hb; a dead refresher is harmless: the workers then read inline (never a stale check)."""
    ppid = os.getppid()
    n = 0
    IS_REFRESHER[0] = True
    prog = [time.time()]
    hprog = [time.time()]
    done = [False]

    def beat():                         # 16.14 + Lead 08:12: alive = this process runs and both loops finished a pass in the
        # last REFRESHER_STUCK_S (90 s): a refresher in its (cold) first build is alive, workers wait for its first copy
        while not done[0]:
            if time.time() - prog[0] < REFRESHER_STUCK_S and time.time() - hprog[0] < REFRESHER_STUCK_S:
                try:
                    with open(os.path.join(SNAP_DIR, "refresh.hb.tmp"), "w") as o:
                        o.write(f"{time.time():.1f} {n} {ghcond.STATS['counted']} {ghcond.STATS['not_modified']} "
                                f"{ghcond.STATS['remaining']}\n")
                    os.replace(os.path.join(SNAP_DIR, "refresh.hb.tmp"), os.path.join(SNAP_DIR, "refresh.hb"))
                except OSError:
                    pass
            REAL_SLEEP(1.0)
    threading.Thread(target=beat, daemon=True).start()

    def halts():                        # 16.14 (4): the halt copy has its own reader, never behind a slow page build
        while os.getppid() == ppid and not os.path.exists(os.path.join(SNAP_DIR, "refresh.stop")):
            t = time.time()
            try:
                filing_halted(0)
            except Exception as e:
                log("refresher: halt read failed", repr(e)[:100])
            hprog[0] = time.time()
            REAL_SLEEP(max(0.05, REFRESH_S - (time.time() - t)))
    threading.Thread(target=halts, daemon=True).start()
    while os.getppid() == ppid and not os.path.exists(os.path.join(SNAP_DIR, "refresh.stop")):
        t = time.time()
        try:
            rival_snapshot(0)
        except Exception as e:
            log("refresher: snapshot failed (workers read inline)", str(e)[:120])
        n += 1
        prog[0] = time.time()
        # Lead 09:37: on PR_TOKEN (run token empty) the refresher reads at most once a second (304s are free, but the
        # account limit is shared by the PC and every create)
        time.sleep(max(0.05, (max(REFRESH_S, 1.0) if runtoken_empty() else REFRESH_S) - (time.time() - t)))
    done[0] = True


if __name__ == "__main__":
    refresher() if sys.argv[1:2] == ["--refresh"] else main()
