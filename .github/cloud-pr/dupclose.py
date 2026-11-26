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
DRY = os.environ.get("DRY", "0") == "1"
END = time.time() + float(os.environ.get("MINUTES", "58")) * 60
W = os.environ.get("W") or tempfile.mkdtemp()
CLOSED = set()
REJ = {"t": 0.0, "alerted": 0.0}
REJ_EVERY, REJ_WIN, REJ_MIN = 60, 600, 3      # Lead 18:42: REJ-BURST n at 3 or more in 10 min, once per 10 min


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


def alert_ref(msg, kind):
    g = os.path.join(W, "taken.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    tree = subprocess.run(["git", "-C", g, "mktree"], input="", capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="dupclose", GIT_AUTHOR_EMAIL="dupclose@localhost",
               GIT_COMMITTER_NAME="dupclose", GIT_COMMITTER_EMAIL="dupclose@localhost")
    c = subprocess.run(["git", "-C", g, "commit-tree", tree, "-m", msg], capture_output=True, text=True, env=env).stdout.strip()
    return sh("git", *auth(), "-C", g, "push", "-q", TK, f"{c}:refs/heads/alert/{kind}-{int(time.time())}").returncode == 0


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
        r = sh("gh", "pr", "list", "--repo", UP, "--author", HANDLE, "--state", "closed", "--limit", "60",
               "--json", "number,closedAt,mergedAt,comments", env=ghenv())
        prs = json.loads(r.stdout or "[]") if r.returncode == 0 else []
    now = time.time()

    def t(x):
        try:
            return time.mktime(time.strptime(x[:19], "%Y-%m-%dT%H:%M:%S")) - time.timezone
        except Exception:
            return 0
    n = sum(1 for p in prs if not p.get("mergedAt") and p.get("closedAt") and now - t(p["closedAt"]) <= REJ_WIN
            and any("proved first" in (c.get("body") or "").lower() for c in p.get("comments") or []))
    if n >= REJ_MIN and now - REJ["alerted"] >= REJ_WIN:
        REJ["alerted"] = now
        if not DRY:
            alert_ref(f"REJ-BURST {n}", "rejburst")
        log("REJ-BURST", n, "(dry)" if DRY else "")
    return n


def one_pass():
    prs = [p for p in ours() if p["number"] not in CLOSED]
    tk = taken()
    dups = []
    for p in prs:
        gid = (p.get("title") or "").strip()
        if not re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*-\d+", gid) or re.search(r"(?m)^Lease:\s*\S", p.get("body") or ""):
            continue                                  # not a step PR, or we hold its lease: keep
        a = age(p)
        if a < 20:
            continue
        if tk is not None:
            first = tk.get(gid)
            dup = bool(first and first[1] != HANDLE and first[0] < p["number"])
        else:
            dup = a < 600 and rival_lower(gid, p["number"])
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


if __name__ == "__main__":
    once = sys.argv[1:2] == ["once"]
    while True:
        try:
            n, d, fresh = one_pass()
            if d or once:
                log("pass:", n, "open PRs of ours,", d, "duplicates", "(taken list fresh)" if fresh else "(taken list stale: file search)")
        except Exception as e:
            log("error", repr(e)[:160])
        if once or time.time() > END:
            break
        time.sleep(20)
