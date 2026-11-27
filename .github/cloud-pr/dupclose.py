#!/usr/bin/env python3
"""dupclose.py: close our own duplicate PRs before the desk's checker rejects them (Lead 17:55 UTC 26 Nov,
team/lead/PAUSE-CAUSE.md: bursts of our PRs rejected as second proofs start the pauses).

Rule: one of OUR open PRs upstream whose body has no Lease line, at least 20 s old, on a unit whose first PR (toolkit
taken list, about 20 s fresh) is another author's with a LOWER number -> close it at once (no comment). Every 20 s
over all our open PRs (covers the +20 s and +3 min opener checks and the 5-min sweep). A pass that finds 3 or more
duplicates open pushes toolkit ref alert/dupopen-<epoch> with message `DUP-OPEN n` (the infra box relays it to the
bus alert channel). Taken list stale (over 180 s): per-PR file search for PRs under 10 min old, else skip.
Env: PR_TOKEN (close, toolkit push), MINUTES (58), DRY=1 (no close, no push), FIXTURE (json list of our PRs, tests).
"""
import base64, json, os, re, subprocess, sys, tempfile, time

UP = "open-goat/pequalnp-proofs"
TK = "https://github.com/Leg0shii/pnp-toolkit.git"
HANDLE = "Leg0shii"
TOK = os.environ.get("PR_TOKEN", "")
RTOK = os.environ.get("READ_TOKEN", "") or TOK     # reads: their own token (PR_TOKEN's limit is shared with PR creation)
DRY = os.environ.get("DRY", "0") == "1"
END = time.time() + float(os.environ.get("MINUTES", "58")) * 60
W = os.environ.get("W") or tempfile.mkdtemp()
CLOSED = set()
CMT = {}          # PR number -> (final, comments); re-read until the PR has been closed for CMT_FINAL_S (Y3)
CMT_FINAL_S = 120
CLOSER = {}       # PR number -> login that closed it (issues API closed_by; never changes)
REJ_MAX_PAGES = 10
REJ_FAIL_MAX = 3   # failed closed-PR reads in a row before the detector counts itself blind (halt)
FIRST = []
REJ = {"t": 0.0, "alerted": 0.0}
REJ_EVERY, REJ_WIN, REJ_MIN = 60, 600, 3      # Lead 18:42: REJ-BURST n at 3 or more in 10 min, once per 10 min
HALTED = set()     # Lead 05:10: PRs that already pushed a filing/stop ref


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def sh(*a, timeout=120, env=None):
    try:
        return subprocess.run(a, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(a, 1, "", "timeout")


def auth():
    return ["-c", "http.https://github.com/.extraheader=AUTHORIZATION: basic "
            + base64.b64encode(f"x-access-token:{TOK}".encode()).decode()] if TOK else []


def ghenv():
    return dict(os.environ, GH_TOKEN=TOK) if TOK else None


def rdenv():
    return dict(os.environ, GH_TOKEN=RTOK) if RTOK else None


# ---- v2 (Lead 19:30, team/lead/DUPCLOSE-V2.md): an earlier PR number does NOT win; a holder's later PR beats our
# earlier unleased one. REST only (no search API): one full sweep of upstream open PRs every FULL_S, the newest pages
# every pass. Map unit -> every open PR (number, author, Lease line).
FULL_S, NEW_PAGES = 600, 1
ID_RX = re.compile(r"(?<![A-Za-z0-9])(L-[a-z]+(?:-[a-z0-9]+)*-\d+)(?![0-9])")
LEASE_RX = re.compile(r"(?m)^Lease:\s*\S")
OPEN = {"t": 0.0, "prs": {}}       # number -> {"n", "gid", "author", "lease", "created"}
EXPO = {"alerted": 0.0}
V2_REF = "refs/heads/dupclose/v2_on"
MERGED = {}                            # v2.1: unit -> (number, author) of another author's MERGED PR (closed list)   # close rule v2 only while this toolkit ref exists (infra pushes it on the Lead's word)


def _page(k):
    if os.environ.get("FIXTURE_OPEN"):
        d = json.load(open(os.environ["FIXTURE_OPEN"]))
        return d[(k - 1) * 100:k * 100]
    r = sh("gh", "api", f"repos/{UP}/pulls?state=open&sort=created&direction=desc&per_page=100&page={k}", env=rdenv(), timeout=60)
    if r.returncode:
        raise RuntimeError("pulls page %d: %s" % (k, r.stderr.strip()[-120:]))
    return json.loads(r.stdout or "[]")


def _row(x):
    t = x.get("title") or ""
    m = ID_RX.search(t) or ID_RX.search(((x.get("head") or {}).get("ref") or "").replace("_", "-"))
    return {"n": x["number"], "gid": m.group(1) if m else None, "author": (x.get("user") or {}).get("login"),
            "lease": bool(LEASE_RX.search(x.get("body") or "")), "createdAt": x.get("created_at") or "", "title": t,
            "body": x.get("body") or ""}


def open_prs():
    """{number: row} of all open upstream PRs: full sweep every FULL_S (drops closed ones), else the newest pages."""
    full = time.time() - OPEN["t"] >= OPEN.get("every", FULL_S)
    got, k = {}, 1
    while True:
        pg = _page(k)
        for x in pg:
            got[x["number"]] = _row(x)
        if len(pg) < 100 or (not full and k >= NEW_PAGES):
            break
        k += 1
    if full:
        OPEN["prs"], OPEN["t"] = got, time.time()
        OPEN["every"] = 600 if k > 25 else FULL_S      # Lead 19:33: over 25 pages -> full sweep every 600 s
        OPEN["pages"] = k
    else:
        OPEN["prs"].update(got)
    return OPEN["prs"]


UNIT_RX = re.compile(r"L-[a-z0-9]+(-[a-z0-9]+)*-\d+")
MFILL = {"n": 0}
# Lead 22:55: a unit id as a whole token in a title ("Prove L-meta-24990" yes; "R-L-meta-582-317 ..." no)
TOKEN_RX = re.compile(r"(?<![A-Za-z0-9_-])(L-[a-z0-9]+(?:-[a-z0-9]+)*-\d+)(?![A-Za-z0-9_-])")


def title_unit(t):
    """the one unit id a title names as a whole token, else None (none or several)."""
    u = set(TOKEN_RX.findall(t or ""))
    return u.pop() if len(u) == 1 else None


MAINF = {"t": 0.0}
MAIN_EVERY = 40          # mintdrill A8 / I3: settled-to-closed within 60 s (was 300 s)


def main_settled():
    """Lead 22:55: units whose file is on upstream main (shallow git fetch every MAIN_EVERY s, no API) are settled."""
    if time.time() - MAINF["t"] < MAIN_EVERY or os.environ.get("FIXTURE_MERGED"):
        return
    MAINF["t"] = time.time()
    g = os.path.join(W, "up.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    if sh("git", "-C", g, "fetch", "-q", "--depth=1", f"https://github.com/{UP}", "+main:refs/heads/main", timeout=300).returncode:
        log("upstream main fetch failed"); return
    for f in sh("git", "-C", g, "ls-tree", "--name-only", "main", "lean/PEqualNP/Outside/").stdout.split():
        u = os.path.basename(f)[:-5].replace("_", "-") if f.endswith(".lean") else ""
        if UNIT_RX.fullmatch(u):
            MERGED.setdefault(u, (0, "upstream-main"))


def merged_fill():
    """Lead 19:58: every pass (20 s) read the most recently updated closed upstream PRs and record units another author's
    MERGED PR (title exactly the unit id) settled. First pass after a start: 3 pages (300 PRs), then 1 page."""
    pages = 3 if MFILL["n"] == 0 else 1
    MFILL["n"] += 1
    for k in range(1, pages + 1):
        if os.environ.get("FIXTURE_MERGED"):
            pg = json.load(open(os.environ["FIXTURE_MERGED"]))[(k - 1) * 100:k * 100]
        else:
            r = sh("gh", "api", f"repos/{UP}/pulls?state=closed&sort=updated&direction=desc&per_page=100&page={k}", env=rdenv(), timeout=60)
            if r.returncode:
                log("closed list failed:", r.stderr.strip()[-100:])
                return
            pg = json.loads(r.stdout or "[]")
        for x in pg:
            t = title_unit(x.get("title"))
            if x.get("merged_at") and (x.get("user") or {}).get("login") != HANDLE and t:
                MERGED.setdefault(t, (x["number"], (x.get("user") or {}).get("login")))
        if len(pg) < 100:
            return


def v2_on():
    g = os.path.join(W, "taken.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    r = sh("git", *auth(), "-C", g, "ls-remote", TK, V2_REF, timeout=30)
    return r.returncode == 0 and V2_REF in r.stdout


def exposure(prs):
    """Lead 19:30 item 2: our open PRs that share the unit with another author's open PR, split by rival number
    lower/higher and rival Lease yes/no; ours with a Lease line counted apart. Returns (split dict, close list,
    exposed list)."""
    by = {}
    for p in prs.values():
        if p["gid"]:
            by.setdefault(p["gid"], []).append(p)
    sp = {"ours": 0, "ours_lease": 0, "shared": 0, "lowL": 0, "low": 0, "highL": 0, "high": 0}
    close, exposed = [], []
    for p in prs.values():
        if p["author"] != HANDLE or not p["gid"]:
            continue
        sp["ours"] += 1
        if p["lease"]:
            sp["ours_lease"] += 1
            continue
        riv = [r for r in by.get(p["gid"], []) if r["author"] != HANDLE]
        if not riv:
            continue
        sp["shared"] += 1
        low = [r for r in riv if r["n"] < p["n"]]
        leased = [r for r in riv if r["lease"]]
        key = ("low" if low else "high") + ("L" if leased else "")
        sp[key] += 1
        if low or leased:
            close.append((p["n"], p["gid"], (low or leased)[0]["author"], (low or leased)[0]["n"], bool(leased)))
        else:
            exposed.append((p["n"], p["gid"]))
    return sp, close, exposed


def taken():
    """{step: (first PR number, author)} or None when missing or stale."""
    g = os.path.join(W, "taken.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    if sh("git", *auth(), "-C", g, "fetch", "-q", "--depth=1", TK, "+refs/heads/status/taken:refs/heads/status/taken").returncode:
        return None
    t = sh("git", "-C", g, "show", "refs/heads/status/taken:taken.txt").stdout.splitlines()
    try:
        if not t or time.time() - int(t[0].split()[2]) > 180:
            return None
    except (IndexError, ValueError):
        return None
    out = {}
    for l in t[1:]:
        p = l.split()
        if len(p) >= 3 and p[1].isdigit():
            out[p[0]] = (int(p[1]), p[2])
    return out


def ours():
    if os.environ.get("FIXTURE"):
        return json.load(open(os.environ["FIXTURE"]))
    r = sh("gh", "pr", "list", "--repo", UP, "--author", HANDLE, "--state", "open", "--limit", "300",
           "--json", "number,title,body,createdAt", env=ghenv())
    return json.loads(r.stdout or "[]") if r.returncode == 0 else []


def age(p):
    try:
        return time.time() - time.mktime(time.strptime(p["createdAt"][:19], "%Y-%m-%dT%H:%M:%S")) + time.timezone
    except Exception:
        return 0


def rival_lower(gid, num):
    """Fallback without the taken list: a lower-numbered PR of another author touching the unit's file."""
    r = sh("gh", "pr", "list", "--repo", UP, "--state", "all", "--search", gid.split("-")[-1], "--limit", "50",
           "--json", "number,author,files,state", env=ghenv())
    try:
        fn = gid.replace("-", "_") + ".lean"
        return any(x["number"] < num and (x.get("author") or {}).get("login") != HANDLE and x.get("state") in ("OPEN", "MERGED")
                   and any(f["path"].endswith("/" + fn) for f in x.get("files") or []) for x in json.loads(r.stdout or "[]"))
    except Exception:
        return False


def filing_go():
    """epoch of the newest toolkit filing/go/<epoch> (0 if none or unreadable)."""
    if os.environ.get("FIXTURE_FILING") is not None:
        txt = os.environ["FIXTURE_FILING"]
    else:
        txt = sh("git", *auth(), "ls-remote", TK, "refs/heads/filing/go/*", timeout=60).stdout
    return max([int(x) for x in re.findall(r"/filing/go/(\d+)$", txt, re.M)] or [0])


def next_ref_epoch(now, stop_epochs, go_epochs):
    """Ref number for a new filing/stop/<n> or filing/go/<n> (red team V5, Lead 06:02): max(now, every existing
    filing/stop + 1, every existing filing/go + 1). A new ref is then greater than every ref that existed when it was
    written, so ref order = write order whatever the writers' clocks say (a fast clock cannot outrank a later write,
    two writes in one second cannot collide). Pure: now = int(time.time()), the epochs read right before the push.
    Copy unchanged into every writer of these refs (PC, Lead, infra)."""
    return max([int(now)] + [int(e) + 1 for e in stop_epochs] + [int(e) + 1 for e in go_epochs])


def filing_stop(msg):
    """push toolkit ref filing/stop/<n> (the opener files nothing while it is newer than every filing/go); n by
    next_ref_epoch over the refs read right before the push; refs unreadable -> n = now (a stop is still pushed)."""
    sts, gos = all_refs("filing/stop"), all_refs("filing/go")
    n = next_ref_epoch(time.time(), [e for e, _ in sts or []], [e for e, _ in gos or []]) if sts is not None and gos is not None \
        else int(time.time())
    g = os.path.join(W, "taken.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    tree = subprocess.run(["git", "-C", g, "mktree"], input="", capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="dupclose", GIT_AUTHOR_EMAIL="dupclose@localhost",
               GIT_COMMITTER_NAME="dupclose", GIT_COMMITTER_EMAIL="dupclose@localhost")
    c = subprocess.run(["git", "-C", g, "commit-tree", tree, "-m", msg], capture_output=True, text=True, env=env).stdout.strip()
    return sh("git", *auth(), "-C", g, "push", "-q", TK, f"{c}:refs/heads/filing/stop/{n}").returncode == 0


BLIND_TAG = "filing stop: BLIND"


def all_refs(pattern):
    """[(epoch, sha)] of the toolkit refs refs/heads/<pattern>/<epoch>, newest first; None if unreadable."""
    r = sh("git", *auth(), "ls-remote", TK, f"refs/heads/{pattern}/*", timeout=60)
    if r.returncode:
        return None
    return sorted(((int(e), h) for h, e in re.findall(r"^(\S+)\s+refs/heads/" + re.escape(pattern) + r"/(\d+)$", r.stdout, re.M)),
                  reverse=True)


def halted_now():
    """True if the newest filing/stop is newer than every filing/go, False if not, None if unreadable."""
    st, go = all_refs("filing/stop"), all_refs("filing/go")
    if st is None or go is None:
        return None
    return bool(st) and st[0][0] > (go[0][0] if go else 0)


def ref_message(sha, ref):
    """commit message of a toolkit ref, fetched from the remote (None if it cannot be read)."""
    g = os.path.join(W, "taken.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    if sh("git", *auth(), "-C", g, "fetch", "-q", TK, ref, timeout=60).returncode:
        return None
    r = sh("git", "-C", g, "log", "-1", "--format=%B", sha, timeout=30)
    return r.stdout.strip() if r.returncode == 0 else None


MSGS = {}          # stop ref sha -> commit message (immutable, so cached; bounded by the number of stop refs)


def stop_listed():
    """PR numbers named by our REJ-HALT stop refs (any age): a rejection already halted for, lifted or not. Clock-free
    replacement of 'closed after the newest filing/go' (V5). None if the stop refs cannot be read."""
    sts = all_refs("filing/stop")
    if sts is None:
        return None
    got = set()
    for e, h in sts:
        if h not in MSGS:
            m = ref_message(h, f"refs/heads/filing/stop/{e}")
            if m is None:
                continue                              # unreadable: its PRs count as not halted for (fail closed)
            MSGS[h] = m
        m = re.match(r"filing stop: REJ-HALT \d+ ([\d ]+)", MSGS[h])
        if m:
            got.update(int(x) for x in m.group(1).split())
    return got


def blind_lift():
    """push filing/go/<epoch> + alert BLIND-LIFT if the newest filing/stop is our blind stop and newer than every go."""
    sts, gos = all_refs("filing/stop"), all_refs("filing/go")
    if sts is None or gos is None:
        return False                                  # unreadable
    g0 = gos[0][0] if gos else 0
    live = [(e, h) for e, h in sts if e > g0]         # every stop the newest go has not lifted
    if not live:
        return False                                  # no stop, or already lifted
    for e, h in live:                                 # Lead 05:58: lift only if EVERY live stop is a blind one of ours
        msg = ref_message(h, f"refs/heads/filing/stop/{e}")
        if not msg or not msg.startswith(BLIND_TAG):
            return False                              # a rejection halt, a foreign stop, or unreadable: only the Lead lifts
    st = live[0]
    g = os.path.join(W, "taken.git")
    tree = subprocess.run(["git", "-C", g, "mktree"], input="", capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="dupclose", GIT_AUTHOR_EMAIL="dupclose@localhost",
               GIT_COMMITTER_NAME="dupclose", GIT_COMMITTER_EMAIL="dupclose@localhost")
    c = subprocess.run(["git", "-C", g, "commit-tree", tree, "-m", f"filing go: BLIND-LIFT of stop {st[0]} (two full scans, no rejection)"],
                       capture_output=True, text=True, env=env).stdout.strip()
    n = next_ref_epoch(time.time(), [e for e, _ in sts], [e for e, _ in gos])
    ok = sh("git", *auth(), "-C", g, "push", "-q", TK, f"{c}:refs/heads/filing/go/{n}").returncode == 0
    if ok:
        alert_ref(f"BLIND-LIFT stop {st[0]}", "blindlift")
        REJ["clean"] = 0
    log("BLIND-LIFT", st[0], "go pushed" if ok else "go PUSH FAILED, retry next pass")
    return ok


def alert_ref(msg, kind):
    g = os.path.join(W, "taken.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    tree = subprocess.run(["git", "-C", g, "mktree"], input="", capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="dupclose", GIT_AUTHOR_EMAIL="dupclose@localhost",
               GIT_COMMITTER_NAME="dupclose", GIT_COMMITTER_EMAIL="dupclose@localhost")
    c = subprocess.run(["git", "-C", g, "commit-tree", tree, "-m", msg], capture_output=True, text=True, env=env).stdout.strip()
    return sh("git", *auth(), "-C", g, "push", "-q", TK, f"{c}:refs/heads/alert/{kind}-{int(time.time())}").returncode == 0


HB = {"t": 0.0}


SPLIT = {"txt": ""}


def heartbeat(n, d, fresh):
    """Lead 18:45: liveness. Force-push toolkit ref status/dupclose every 30 s; message
    `dupclose <epoch> open=N dups=D closed=C taken=fresh|stale run=<id>`. The infra box alerts DUPCLOSE-DEAD when the
    newest one is older than 2 min and dispatches the workflow once."""
    if DRY or time.time() - HB["t"] < 30:
        return
    HB["t"] = time.time()
    g = os.path.join(W, "taken.git")
    tree = subprocess.run(["git", "-C", g, "mktree"], input="", capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="dupclose", GIT_AUTHOR_EMAIL="dupclose@localhost",
               GIT_COMMITTER_NAME="dupclose", GIT_COMMITTER_EMAIL="dupclose@localhost")
    rl = sh("gh", "api", "rate_limit", "--jq", ".resources.core.remaining", env=rdenv(), timeout=30).stdout.strip() or "?"
    # 19:50: PR_TOKEN (Leg0shii, shared with PR creation and the PC) hit 0; rate_limit calls are free
    rlp = sh("gh", "api", "rate_limit", "--jq", r'"\(.resources.core.remaining)/\(.resources.core.reset)"', env=ghenv(), timeout=30).stdout.strip() or "?"
    msg = (f"dupclose {int(time.time())} open={n} dups={d} closed={len(CLOSED)} taken={'fresh' if fresh else 'stale'} "
           f"{SPLIT['txt']} pages={OPEN.get('pages', '-')} rej10={REJ.get('n', '-')} rl={rl} rl_pr={rlp} tok={'read' if os.environ.get('READ_TOKEN') else 'pr'} "
           f"run={os.environ.get('GITHUB_RUN_ID', '-')}")
    c = subprocess.run(["git", "-C", g, "commit-tree", tree, "-m", msg], capture_output=True, text=True, env=env).stdout.strip()
    sh("git", *auth(), "-C", g, "push", "-q", "-f", TK, f"{c}:refs/heads/status/dupclose", timeout=60)


def rej_burst():
    """Lead 18:42 (PAUSE-CAUSE.md addendum 18:40): our PRs closed UNMERGED in the last 10 min whose comments carry the
    checker text 'proved first'. 3 or more -> REJ-BURST n (alert ref, relayed to the bus), once per 10 min. GitHub
    only; it alerts, it never stops filing. Returns the count (None = not checked this pass)."""
    if time.time() - REJ["t"] < REJ_EVERY:
        return None
    REJ["t"] = time.time()
    if os.environ.get("FIXTURE_CLOSED"):
        prs = json.load(open(os.environ["FIXTURE_CLOSED"]))
    else:
        # REST, no search API (Lead 19:30): closed PRs by update time, newest first, every page back to the window
        # (Y4: a mint can close or merge over 100 PRs in 10 min), ours closed unmerged in the window, then for those
        # only: who closed it (Y5: our own close is never a rejection, whichever job or box closed it) and the
        # comments, re-read while the close is younger than CMT_FINAL_S (Y3: the checker comments seconds later)
        rows, scan = [], "ok"
        for k in range(1, REJ_MAX_PAGES + 1):
            r = sh("gh", "api", f"repos/{UP}/pulls?state=closed&sort=updated&direction=desc&per_page=100&page={k}",
                   env=rdenv(), timeout=60)
            if r.returncode:
                scan = "closed-PR read failed"
                break
            pg = json.loads(r.stdout or "[]")
            rows += pg
            try:
                oldest = min(time.mktime(time.strptime((x.get("updated_at") or x.get("closed_at") or "")[:19],
                                                       "%Y-%m-%dT%H:%M:%S")) - time.timezone for x in pg) if pg else 0
            except ValueError:
                oldest = 0
            if len(pg) < 100 or time.time() - oldest > REJ_WIN:
                break
        else:
            scan = f"over {REJ_MAX_PAGES} pages of closed PRs in {REJ_WIN} s"
        # a failed read is retried next pass; REJ_FAIL_MAX failed passes in a row (or over REJ_MAX_PAGES pages) = blind
        REJ["full"] = scan == "ok"                    # this pass saw every close in the window (blind-lift input)
        REJ["fails"] = REJ.get("fails", 0) + 1 if scan == "closed-PR read failed" else 0
        if scan == "closed-PR read failed" and REJ["fails"] < REJ_FAIL_MAX:
            REJ["t"] = 0
            scan = "ok"
        elif scan == "closed-PR read failed":
            scan = f"closed-PR read failed {REJ['fails']} passes in a row"
        REJ["scan"] = scan
        prs = []
        for x in rows:
            if x.get("merged_at") and (x.get("user") or {}).get("login") != HANDLE:
                t = title_unit(x.get("title"))         # v2.1 + Lead 22:55: unit id as a whole token in the title
                if t:                                  # (not R-L-meta-582-317)
                    MERGED.setdefault(t, (x["number"], (x.get("user") or {}).get("login")))
                continue
            if (x.get("user") or {}).get("login") != HANDLE or x.get("merged_at") or not x.get("closed_at"):
                continue
            ca = x["closed_at"]
            try:
                if time.time() - (time.mktime(time.strptime(ca[:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone) > REJ_WIN:
                    continue
            except Exception:
                continue
            if x["number"] in CLOSED:
                continue                              # closed by us (dupclose), not a checker rejection
            n_ = x["number"]
            if n_ not in CLOSER:
                c = sh("gh", "api", f"repos/{UP}/issues/{n_}", "--jq", ".closed_by.login // empty", env=rdenv(), timeout=60)
                if c.returncode == 0 and c.stdout.strip():
                    CLOSER[n_] = c.stdout.strip()
            if CLOSER.get(n_) == HANDLE:
                continue                              # our own close (this job, an earlier job, or the PC)
            if not (CMT.get(n_) or (False,))[0]:
                c = sh("gh", "api", f"repos/{UP}/issues/{n_}/comments?per_page=30", env=rdenv(), timeout=60)
                if c.returncode == 0:
                    try:
                        closed_s = time.time() - (time.mktime(time.strptime(ca[:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone)
                    except ValueError:
                        closed_s = 0
                    CMT[n_] = (closed_s > CMT_FINAL_S, json.loads(c.stdout or "[]"))
            prs.append({"number": n_, "closedAt": ca, "mergedAt": None, "comments": (CMT.get(n_) or (False, []))[1],
                        "closedBy": CLOSER.get(n_)})
    now = time.time()

    def t(x):
        try:
            return time.mktime(time.strptime(x[:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone
        except Exception:
            return 0
    n = sum(1 for p in prs if not p.get("mergedAt") and p.get("closedAt") and now - t(p["closedAt"]) <= REJ_WIN
            and any("proved first" in (c.get("body") or "").lower() for c in p.get("comments") or []))
    # Lead 05:10 HALT ON ONE REJECTION: one of our PRs closed unmerged (not by dupclose) with a "proved first" comment
    # or any comment by another login, not yet named by one of our stops (Y7: no clock compare) -> filing/stop + REJ-HALT
    go = filing_go()
    # closed by another login (closedBy known) = a maker's close = a rejection, comment or not (Y3)
    hit = [p["number"] for p in prs if not p.get("mergedAt") and p.get("closedAt") and now - t(p["closedAt"]) <= REJ_WIN
           and p["number"] not in HALTED
           and ((p.get("closedBy") not in (None, HANDLE))
                or any("proved first" in (c.get("body") or "").lower() or ((c.get("user") or {}).get("login") or HANDLE) != HANDLE
                       for c in p.get("comments") or []))]
    if hit:                                           # Y7: already halted for (named by one of our stops) -> not new
        listed = stop_listed() or set()
        HALTED.update(x for x in hit if x in listed)
        hit = [x for x in hit if x not in listed]
    scan = REJ.get("scan", "ok")
    blind = False
    if scan != "ok" and not hit and f"scan@{go}" not in HALTED:
        if not DRY and halted_now():                  # Lead 05:58: filing already halted -> no blind stop on top of it
            HALTED.add(f"scan@{go}")                  # (unreadable refs -> None -> push the blind stop: fail closed)
            log("blind scan while already halted, no stop pushed:", scan)
        else:
            hit = [f"scan@{go}"]                      # cannot see every close in the window: fail closed (once per go)
            blind = True
    if hit:
        if not DRY:
            why = " ".join(map(str, hit[:20])) + ("" if scan == "ok" else f" ({scan})")
            # BLIND_TAG marks a stop pushed only because the detector could not see; blind_lift() may lift only those
            ok = filing_stop(f"{BLIND_TAG} {scan} go={go}" if blind else f"filing stop: REJ-HALT {len(hit)} {why}")
            if ok:                                    # Y6: marked done only once the stop ref exists
                HALTED.update(hit)
                alert_ref(f"REJ-HALT {len(hit)} {' '.join(map(str, hit[:10]))}", "rejhalt")
                log("REJ-HALT", hit, "stop ref pushed")
            else:
                REJ["t"] = 0                          # retry on the next pass
                log("REJ-HALT", hit, "stop ref PUSH FAILED, retry next pass")
        else:
            log("REJ-HALT (dry)", hit)
    # Lead 05:50 BLIND HALTS LIFT THEMSELVES: two full scans in a row with no rejection of ours anywhere in the window
    # (HALTED and filing/go ignored) -> if the newest filing/stop ref is a blind stop of ours (its commit message read
    # from the remote, so a chain restart changes nothing) and newer than every filing/go: push filing/go + BLIND-LIFT
    rej_any = [p["number"] for p in prs if not p.get("mergedAt") and p.get("closedAt") and now - t(p["closedAt"]) <= REJ_WIN
               and ((p.get("closedBy") not in (None, HANDLE))
                    or any("proved first" in (c.get("body") or "").lower() or ((c.get("user") or {}).get("login") or HANDLE) != HANDLE
                           for c in p.get("comments") or []))]
    REJ["clean"] = REJ.get("clean", 0) + 1 if (REJ.get("full") and not rej_any and not hit) else 0
    if REJ["clean"] >= 2 and not DRY:
        blind_lift()
    REJ["n"] = n                                      # 20:10: rej10=<n> in the heartbeat (late-lease loop tripwire)
    if n >= REJ_MIN and now - REJ["alerted"] >= REJ_WIN:
        REJ["alerted"] = now
        if not DRY:
            alert_ref(f"REJ-BURST {n}", "rejburst")
        log("REJ-BURST", n, "(dry)" if DRY else "")
    return n


OU = {"t": 0.0, "txt": None}


def ours_unleased(allp):
    """Lead 21:59: feed for the late-lease loop (infra box). Every 60 s force-push toolkit ref status/ours-unleased,
    file ours_unleased.tsv: `n<TAB>gid<TAB>created<TAB>lowest` for each of OUR open PRs without a Lease line, oldest
    first; lowest=1 when no other author's open PR on the unit has a lower number. Only on change."""
    if DRY or time.time() - OU["t"] < 60:
        return
    OU["t"] = time.time()
    low = {}
    for q in allp.values():
        if q["gid"] and q["author"] != HANDLE:
            low[q["gid"]] = min(low.get(q["gid"], 10 ** 9), q["n"])
    rows = sorted((p for p in allp.values() if p["author"] == HANDLE and p["gid"] and not p["lease"] and p["n"] not in CLOSED),
                  key=lambda p: (p["createdAt"], p["n"]))
    txt = "".join(f"{p['n']}\t{p['gid']}\t{p['createdAt']}\t{int(low.get(p['gid'], 10 ** 9) > p['n'])}\n" for p in rows)
    if txt == OU["txt"]:
        return
    g = os.path.join(W, "taken.git")
    blob = subprocess.run(["git", "-C", g, "hash-object", "-w", "--stdin"], input=txt, capture_output=True, text=True).stdout.strip()
    tree = subprocess.run(["git", "-C", g, "mktree"], input=f"100644 blob {blob}\tours_unleased.tsv\n", capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="dupclose", GIT_AUTHOR_EMAIL="dupclose@localhost",
               GIT_COMMITTER_NAME="dupclose", GIT_COMMITTER_EMAIL="dupclose@localhost")
    c = subprocess.run(["git", "-C", g, "commit-tree", tree, "-m", f"ours-unleased {int(time.time())} n={len(rows)}"],
                       capture_output=True, text=True, env=env).stdout.strip()
    if sh("git", *auth(), "-C", g, "push", "-q", "-f", TK, f"{c}:refs/heads/status/ours-unleased", timeout=60).returncode == 0:
        OU["txt"] = txt


def one_pass():
    allp = None
    try:
        allp = open_prs()
    except Exception as e:
        log("open PR list failed:", repr(e)[:120])
    if allp is not None and not os.environ.get("FIXTURE"):
        prs = [{"number": p["n"], "title": p["title"], "body": p["body"], "createdAt": p["createdAt"]}
               for p in allp.values() if p["author"] == HANDLE and p["n"] not in CLOSED]
    else:                                             # REST list failed: nothing this pass (no search API fallback)
        prs = [p for p in ours() if p["number"] not in CLOSED] if os.environ.get("FIXTURE") else []
    tk = taken()
    dups = []
    v2 = False
    if allp is not None:
        sp, close2, exposed = exposure({k: v for k, v in allp.items() if k not in CLOSED})
        SPLIT["txt"] = (f"exposed={len(exposed)} shared={sp['shared']} rlow={sp['low']} rlowL={sp['lowL']} "
                        f"rhigh={sp['high']} rhighL={sp['highL']} ours_lease={sp['ours_lease']} v2={'on' if v2_on() else 'off'}")
        v2 = "v2=on" in SPLIT["txt"]
        if len(exposed) >= 15 and time.time() - EXPO["alerted"] >= 600 and not DRY:
            EXPO["alerted"] = time.time()
            alert_ref(f"EXPOSED {len(exposed)}", "exposed")
            log("EXPOSED", len(exposed))
        try:
            ours_unleased({k: v for k, v in allp.items() if k not in CLOSED})
        except Exception as e:
            log("ours-unleased feed failed:", repr(e)[:120])
        merged_fill()                                # Lead 19:58: the MERGED close runs ALWAYS (not behind v2_on)
        try:
            main_settled()
        except Exception as e:
            log("main settled check failed:", repr(e)[:120])
        if True:                                     # v2.1: unit already settled by another author's merged PR
            for p in allp.values():
                if (p["author"] == HANDLE and p["gid"] in MERGED and p["n"] not in CLOSED      # Lead 22:55: leased too
                        and age({"createdAt": p["createdAt"]}) >= 20):
                    dups.append((p["n"], p["gid"], int(age({"createdAt": p["createdAt"]}))))
                    log("MERGED-RIVAL", p["n"], p["gid"], "settled by", *MERGED[p["gid"]])
        own = {}                                     # mintdrill A9: two open PRs of OUR OWN on one unit
        for p in allp.values():
            if p["author"] == HANDLE and p["gid"] and p["n"] not in CLOSED:
                own.setdefault(p["gid"], []).append(p)
        for gid, ps in own.items():
            for p in sorted(ps, key=lambda q: q["n"])[1:]:      # keep the lowest number (first in line), close younger
                if not any(x[0] == p["n"] for x in dups) and age({"createdAt": p["createdAt"]}) >= 20:
                    dups.append((p["n"], gid, int(age({"createdAt": p["createdAt"]}))))
                    log("OWN-DUP", p["n"], gid, "younger than", sorted(ps, key=lambda q: q["n"])[0]["n"])
        if v2:                                       # rule v2: rival lower number OR rival with a Lease line
            for n, gid, ra, rn, rl in close2:
                if any(x[0] == n for x in dups):
                    continue
                p = allp.get(n)
                if p and age({"createdAt": p["createdAt"]}) >= 20:
                    dups.append((n, gid, int(age({"createdAt": p["createdAt"]}))))
    for p in prs:
        gid = (p.get("title") or "").strip()
        if not re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*-\d+", gid) or re.search(r"(?m)^Lease:\s*\S", p.get("body") or ""):
            continue                                  # not a step PR, or we hold its lease: keep
        a = age(p)
        if a < 20 or any(x[0] == p["number"] for x in dups):
            continue
        if tk is not None:
            first = tk.get(gid)
            dup = bool(first and first[1] != HANDLE and first[0] < p["number"])
        else:
            dup = False                               # Lead 19:30: no search API in any loop (was rival_lower)
        if dup:
            dups.append((p["number"], gid, int(a)))
    for n, gid, a in dups:
        if DRY:
            log("DRY would close", n, gid, f"age {a}s")
            continue
        r = sh("gh", "pr", "close", str(n), "--repo", UP, env=ghenv())
        log("CLOSED" if r.returncode == 0 else "close failed", n, gid, f"age {a}s", r.stderr.strip()[-120:])
        if r.returncode == 0:
            CLOSED.add(n)
    if len(dups) >= 3 and not DRY:
        alert_ref(f"DUP-OPEN {len(dups)}", "dupopen")
        log("DUP-OPEN", len(dups))
    rb = rej_burst()
    if rb:
        log("rejections of ours in the last 10 min:", rb)
    return len(prs), len(dups), tk is not None


if __name__ == "__main__" and sys.argv[1:2] == ["selftest-merged"]:
    # Lead 19:46 fixture: a merged reduction PR titled "R-L-meta-1-2 ..." must NOT mark L-meta-1 settled; a merged PR
    # titled exactly "L-meta-1" must
    m = lambda t: {"number": 9, "title": t, "user": {"login": "riv"}, "merged_at": "2026-11-26T19:40:00Z",
                   "closed_at": "2026-11-26T19:40:00Z", "body": "", "head": {"ref": "x"}}
    fx = [m("R-L-meta-1-2 reduction")]
    real = sh
    sh = lambda *a, **k: subprocess.CompletedProcess(a, 0, json.dumps(fx), "") if "state=closed" in str(a) else real(*a, **k)
    REJ["t"] = 0; rej_burst(); a = "L-meta-1" not in MERGED
    fx[:] = [m("L-meta-1")]; REJ["t"] = 0; rej_burst(); b = "L-meta-1" in MERGED
    MERGED.clear(); fx[:] = [m("Prove L-meta-24990")]; REJ["t"] = 0; rej_burst(); c = "L-meta-24990" in MERGED
    MERGED.clear(); fx[:] = [m("L-meta-1 and L-meta-2")]; REJ["t"] = 0; rej_burst(); d = not MERGED
    print("MERGED SELFTEST", "OK" if a and b and c and d else "FAIL", a, b, c, d)
    sys.exit(0 if a and b and c and d else 1)
if __name__ == "__main__" and sys.argv[1:2] == ["selftest-halt"]:
    # Lead 05:10 fixture: one "proved first" rejection -> one filing/stop push + REJ-HALT; the same PR again -> nothing;
    # a close with only our own comment -> nothing; a rejection closed before the newest filing/go -> nothing
    import tempfile as _tf
    now_s = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    old_s = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - 120))
    pr = lambda n, body, who="checker", ca=now_s: {"number": n, "closedAt": ca, "mergedAt": None,
                                                  "comments": [{"body": body, "user": {"login": who}}]}
    pushes = []
    real = sh
    def fake(*a, **k):
        if "push" in a:
            pushes.append(a[-1]); return subprocess.CompletedProcess(a, 0, "", "")
        return real(*a, **k)
    sh = fake
    DRY = False
    def case(prs, go_epoch):
        f = _tf.NamedTemporaryFile("w", suffix=".json", delete=False); json.dump(prs, f); f.close()
        os.environ["FIXTURE_CLOSED"] = f.name
        os.environ["FIXTURE_FILING"] = f"x\trefs/heads/filing/go/{go_epoch}\n" if go_epoch else ""
        n0 = len(pushes); REJ["t"] = 0; rej_burst()
        return [x for x in pushes[n0:]]
    r1 = case([pr(101, "This step was proved first by #99")], 0)
    a = sum("filing/stop/" in x for x in r1) == 1 and sum("alert/rejhalt-" in x for x in r1) == 1
    b = case([pr(101, "This step was proved first by #99")], 0) == []
    c = case([pr(102, "closing my duplicate", who=HANDLE)], 0) == []
    d = case([pr(103, "any maker comment")], 0) != []
    e = case([pr(104, "proved first", ca=old_s)], int(time.time()) - 30) == []
    print("HALT SELFTEST", "OK" if all((a, b, c, d, e)) else "FAIL", a, b, c, d, e)
    sys.exit(0 if all((a, b, c, d, e)) else 1)
if __name__ == "__main__" and sys.argv[1:2] == ["measure"]:
    # Lead 19:30 item 2: one full sweep, print the split and what rule v2 would close; closes nothing
    sp, close2, exposed = exposure(open_prs())
    print(json.dumps(sp))
    for n, gid, ra, rn, rl in sorted(close2):
        print("V2 WOULD CLOSE", n, gid, "rival", ra, rn, "lease" if rl else "lower")
    print("EXPOSED", len(exposed), " ".join(f"{n}:{g}" for n, g in sorted(exposed)[:40]))
    sys.exit(0)
if __name__ == "__main__":
    once = sys.argv[1:2] == ["once"]
    while True:
        try:
            n, d, fresh = one_pass()
            heartbeat(n, d, fresh)
            if d or once or not FIRST:
                FIRST.append(1)
                log("pass:", n, "open PRs of ours,", d, "duplicates", "(taken list fresh)" if fresh else "(taken list stale: file search)")
        except Exception as e:
            log("error", repr(e)[:160])
        if once or time.time() > END:
            break
        time.sleep(20)
