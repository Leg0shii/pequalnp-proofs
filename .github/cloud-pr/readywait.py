#!/usr/bin/env python3
"""ready-wait: restart cloud-pr for kept ready/<ID> branches the moment the desk lists the step (re-push on current
fork main, so the run uses today's opener code).

cloud-pr ends 'waiting' and keeps ready/<ID> when the step is not listed yet (pre-generated waves). This loop polls the
listing (data.pequalnp.com gaps.json only since the 16:00 pause; no desk-host read, no handle, no claim) and the fork's
ready/ branches, and re-pushes each listed one on current fork main once per step per job. A branch must be at
least MIN_AGE s old, so the push run of a fresh branch is never doubled. Dispatches are paced (GitHub allows about
2 PR creations in parallel; cloud-pr retries refusals)."""
import json, os, re, subprocess, sys, threading, time

FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
END = time.time() + float(os.environ.get("MINUTES", "58")) * 60
MIN_AGE = 60
PACE = float(os.environ.get("PACE_S", "4"))
G = os.path.join(os.environ.get("W", "/tmp"), "rw.git")
FORK_URL = os.environ.get("FORK_URL", f"https://github.com/{FORK}.git")   # test: a local bare repo
first_seen, done = {}, set()
TRIES = {}      # gid -> (re-pushes, last epoch): a run that ended "waiting" (gaps.json behind desk/status) keeps the
RETRY_S, MAX_TRIES = 60, 4   # branch; it is re-pushed again after RETRY_S, at most MAX_TRIES times per job
NO_RUN_WAIT = float(os.environ.get("NO_RUN_WAIT", "15"))   # Lead 18:53: no cloud-pr run this long after a round -> BATCH-NO-RUN


def run(cmd, timeout=60):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        return subprocess.CompletedProcess(cmd, 124, "", "timeout")


def log(*a):
    print(time.strftime("%H:%M:%S", time.gmtime()), *a, flush=True)


def listed():
    ids = set()
    # 16:00 pause (Lead condition 2): gaps.json only, never a desk-host read (desk/status every 10 s here kept our
    # handle in the pause window until 16:06)
    for url, key in (("https://data.pequalnp.com/data/desk/gaps.json", "gaps"),):
        r = run(["curl", "-sS", "-m", "30", url], 40)
        try:
            ids |= {g["id"] for g in json.loads(r.stdout)[key]}
        except Exception:
            pass
    return ids


TK = os.environ.get("TOOLKIT_URL", "https://github.com/Leg0shii/pnp-toolkit.git")
SIG_REF = "refs/heads/status/listed"     # Lead 12:33: the PC publishes its earliest listing signal here (listed.txt:
SIG = {"sha": None, "ids": set()}        # one "L-meta-N <first-seen epoch> <source>" per line); read by ref sha, no API


def signal():
    """ids the PC saw listed first (desk/status, gaps.json or feed, whichever is earliest): one ls-remote, a fetch only
    when the ref moved. Missing ref or any error: the old set (this source is an addition, never the only one)."""
    r = run(["git", "ls-remote", TK, SIG_REF], 30)
    sha = (r.stdout.split() or [None])[0] if r.returncode == 0 else None
    if sha and sha != SIG["sha"]:
        if run(["git", "-C", G, "fetch", "-q", "--depth=1", TK, f"+{SIG_REF}:refs/sig"], 60).returncode == 0:
            txt = run(["git", "-C", G, "show", "refs/sig:listed.txt"]).stdout
            SIG["ids"] = {l.split()[0] for l in txt.splitlines() if l.strip() and not l.startswith("#")}
            SIG["sha"] = sha
            log("SIGNAL", sha[:8], len(SIG["ids"]), "ids")
    return SIG["ids"]


def branches():
    r = run(["git", "ls-remote", f"https://github.com/{FORK}.git", "refs/heads/ready/*"])
    out = {}
    for l in r.stdout.splitlines():
        sha, ref = l.split("\t")
        out[ref[len("refs/heads/ready/"):]] = sha
    return out


def ready_file(gid, sha):
    if run(["git", "-C", G, "fetch", "-q", "--depth=1", "--filter=blob:none", f"https://github.com/{FORK}.git", sha], 90).returncode:
        return None
    f = [x for x in run(["git", "-C", G, "ls-tree", "-r", "--name-only", sha, "ready/"]).stdout.split() if re.fullmatch(r"ready/[A-Za-z0-9_]+\.lean", x)]
    return f[0] if len(f) == 1 else None


def repush(gid, sha, f):
    """Re-push the file as ready/<gid> on CURRENT fork main: the push starts cloud-pr with today's code (dispatching
    the old commit would run the opener code it was built on)."""
    url = f"https://github.com/{FORK}.git"
    r = run(["git", "-C", G, "fetch", "-q", "--depth=1", "--filter=blob:none", url, "+refs/heads/main:refs/heads/main"], 120)
    if r.returncode:
        return r
    blob = run(["git", "-C", G, "rev-parse", f"{sha}:{f}"]).stdout.strip()
    idx = os.path.join(os.environ.get("W", "/tmp"), "rw.idx"); env = dict(os.environ, GIT_INDEX_FILE=idx)
    subprocess.run(["git", "-C", G, "read-tree", "main"], env=env)
    subprocess.run(["git", "-C", G, "update-index", "--add", "--cacheinfo", f"100644,{blob},{f}"], env=env)
    tree = subprocess.run(["git", "-C", G, "write-tree"], env=env, capture_output=True, text=True).stdout.strip()
    cenv = dict(os.environ, GIT_AUTHOR_NAME="Leg0shii", GIT_COMMITTER_NAME="Leg0shii",
                GIT_AUTHOR_EMAIL="46093332+Leg0shii@users.noreply.github.com", GIT_COMMITTER_EMAIL="46093332+Leg0shii@users.noreply.github.com")
    # Lead 15:10: a lease-first branch stays lease-first on its re-push (else the opener takes the PR-first path)
    lf = " lease-first" if "lease-first" in run(["git", "-C", G, "log", "-1", "--format=%B", sha]).stdout.lower() else ""
    c = subprocess.run(["git", "-C", G, "commit-tree", tree, "-p", "main", "-m", f"ready {gid} (ready-wait: listed{lf})"],
                       env=cenv, capture_output=True, text=True).stdout.strip()
    if not c:
        return subprocess.CompletedProcess([], 1, "", "commit-tree failed")
    return run(["git", "-C", G, "push", "-q", "-f", url, f"{c}:refs/heads/ready/{gid}"], 180)


TAKEN_REF = "refs/heads/status/taken"


def taken():
    """Lead 18:52: the team taken list (toolkit status/taken, about 20 s fresh): {step: author of its first PR}. Read
    right before every batch push. Stale (over 180 s) or unreadable -> None (then the opener's own checks decide)."""
    if run(["git", "-C", G, "fetch", "-q", "--depth=1", TK, f"+{TAKEN_REF}:refs/taken"], 60).returncode:
        return None
    t = run(["git", "-C", G, "show", "refs/taken:taken.txt"]).stdout.splitlines()
    try:
        if not t or time.time() - int(t[0].split()[2]) > 180:
            return None
    except (IndexError, ValueError):
        return None
    return {l.split()[0]: l.split()[2] for l in t[1:] if len(l.split()) >= 3}


def batch_push(items):
    """Lead 18:52: one fetch of fork main and all the branch commits, one push for the whole batch (was one unit per
    about 7 s). items: [(gid, sha)]. Units the fresh taken list shows with a PR are dropped (branch deleted) instead.
    Returns (pushed ids, dropped ids, failed ids)."""
    url = FORK_URL
    if run(["git", "-C", G, "fetch", "-q", "--depth=1", "--filter=blob:none", url, "+refs/heads/main:refs/heads/main",
            *[s for _, s in items]], 180).returncode:
        return [], [], [g for g, _ in items]
    tk = taken()
    refs, pushed, dropped, failed = [], [], [], []
    idx = os.path.join(os.environ.get("W", "/tmp"), "rw.idx"); env = dict(os.environ, GIT_INDEX_FILE=idx)
    cenv = dict(os.environ, GIT_AUTHOR_NAME="Leg0shii", GIT_COMMITTER_NAME="Leg0shii",
                GIT_AUTHOR_EMAIL="46093332+Leg0shii@users.noreply.github.com", GIT_COMMITTER_EMAIL="46093332+Leg0shii@users.noreply.github.com")
    for gid, sha in items:
        if tk is not None and gid in tk:
            refs.append(f":refs/heads/ready/{gid}"); dropped.append(gid)
            log("DROP", gid, "taken list: first PR by", tk[gid], "(no re-push, branch deleted)")
            continue
        fs = [x for x in run(["git", "-C", G, "ls-tree", "-r", "--name-only", sha, "ready/"]).stdout.split() if re.fullmatch(r"ready/[A-Za-z0-9_]+\.lean", x)]
        if len(fs) != 1:
            failed.append(gid); log("SKIP", gid, "no single ready/ file"); continue
        f = fs[0]
        blob = run(["git", "-C", G, "rev-parse", f"{sha}:{f}"]).stdout.strip()
        subprocess.run(["git", "-C", G, "read-tree", "main"], env=env)
        subprocess.run(["git", "-C", G, "update-index", "--add", "--cacheinfo", f"100644,{blob},{f}"], env=env)
        tree = subprocess.run(["git", "-C", G, "write-tree"], env=env, capture_output=True, text=True).stdout.strip()
        lf = " lease-first" if "lease-first" in run(["git", "-C", G, "log", "-1", "--format=%B", sha]).stdout.lower() else ""
        c = subprocess.run(["git", "-C", G, "commit-tree", tree, "-p", "main", "-m", f"ready {gid} (ready-wait: listed{lf})"],
                           env=cenv, capture_output=True, text=True).stdout.strip()
        if not c:
            failed.append(gid); continue
        refs.append(f"+{c}:refs/heads/ready/{gid}"); pushed.append(gid)
    # Lead 18:53: GitHub may create no push event for a many-branch push and the drain starts only on one, so the FIRST
    # re-push of the round goes alone (sure event: starts or queues the drain), then the rest in chunks of 50
    ups = [x for x in refs if not x.startswith(":")]
    chunks = ([ups[:1]] if ups else []) + [c for c in ([x for x in refs if x not in ups[:1]][k:k + 50]
                                                       for k in range(0, len(refs) - len(ups[:1]), 50)) if c]
    for ch in chunks:
        r = run(["git", "-C", G, "push", "-q", url, *ch], 180)
        if r.returncode:
            log("BATCH-PUSH-FAIL", (r.stderr or "").strip()[-150:])
            bad = {x.rsplit("/", 1)[1] for x in ch}
            failed += [g for g in pushed if g in bad]; pushed = [g for g in pushed if g not in bad]
    if pushed:
        # in a thread: the next round never waits for this check
        threading.Thread(target=no_run_check, args=(pushed[0], {g: c for g, c in ((x.rsplit("/", 1)[1], x[1:].split(":")[0]) for x in ups)}),
                         daemon=True).start()
    return pushed, dropped, failed


def drain_runs():
    """cloud-pr runs in progress or queued (None if the API cannot say)."""
    n = 0
    for st in ("in_progress", "queued"):
        r = run(["gh", "api", f"repos/{FORK}/actions/workflows/cloud-pr.yml/runs?status={st}&per_page=1", "--jq", ".total_count"], 30)
        if r.returncode or not r.stdout.strip().isdigit():
            return None
        n += int(r.stdout.strip())
    return n


def no_run_check(gid, commits, wait=None):
    """Lead 18:53: 15 s after a round with re-pushes, no cloud-pr run in progress or queued -> re-push one ref (a new
    commit, so the push is a real change and creates an event) and log BATCH-NO-RUN."""
    time.sleep(NO_RUN_WAIT if wait is None else wait)
    if drain_runs() != 0:
        return False
    c = commits.get(gid)
    cenv = dict(os.environ, GIT_AUTHOR_NAME="Leg0shii", GIT_COMMITTER_NAME="Leg0shii",
                GIT_AUTHOR_EMAIL="46093332+Leg0shii@users.noreply.github.com", GIT_COMMITTER_EMAIL="46093332+Leg0shii@users.noreply.github.com")
    tree = run(["git", "-C", G, "rev-parse", f"{c}^{{tree}}"]).stdout.strip() if c else ""
    msg = run(["git", "-C", G, "log", "-1", "--format=%B", c]).stdout.strip() if c else ""
    c2 = subprocess.run(["git", "-C", G, "commit-tree", tree, "-p", "main", "-m", msg + " (no-run re-push)"],
                        env=cenv, capture_output=True, text=True).stdout.strip() if tree else ""
    r = run(["git", "-C", G, "push", "-q", "-f", FORK_URL, f"{c2}:refs/heads/ready/{gid}"], 120) if c2 else None
    log("BATCH-NO-RUN", gid, "no cloud-pr run 15 s after the round: re-pushed it", "ok" if r is not None and not r.returncode else "FAILED")
    return True


run(["git", "init", "-q", "--bare", G])
n = 0; last_l = 0; ids = set()
T0 = time.time(); listed_at = {}     # gid -> first time seen listed in this job (ids listed at the start count as old)

# GATEWAY 4 (Lead 16:50): a pause never stops filing, so ready-wait no longer idles on the shared pause refs
while time.time() < END:
    br = branches()
    now = time.time()
    for gid, sha in br.items():
        first_seen.setdefault((gid, sha), now)
    if now - last_l >= 10:
        ids = listed() or ids; last_l = now
    ids = ids | signal()
    for g in ids:
        listed_at.setdefault(g, T0 if now - T0 < 15 else now)
    for g in list(done):      # still there RETRY_S after our re-push = that run waited or failed: allow another
        k, t = TRIES.get(g, (0, 0))
        if g in br and k < MAX_TRIES and now - t >= RETRY_S:
            done.discard(g)
    todo = [(g, s) for g, s in br.items() if g not in done and g in ids and now - first_seen[(g, s)] >= MIN_AGE
            and re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*", g)]
    todo.sort(key=lambda x: (-listed_at.get(x[0], T0), first_seen[x]))
    if todo:
        t1 = time.time()
        pushed, dropped, failed = batch_push(todo[:100])
        for g in pushed:
            done.add(g); TRIES[g] = (TRIES.get(g, (0, 0))[0] + 1, time.time())
        for g in dropped:
            done.add(g); TRIES[g] = (MAX_TRIES, 0)
        for g in failed:          # retried after RETRY_S while the branch is still there, at most MAX_TRIES times
            done.add(g); TRIES[g] = (TRIES.get(g, (0, 0))[0] + 1, time.time())
        n += len(pushed)
        log("BATCH", len(pushed), "re-pushed,", len(dropped), "dropped (taken),", len(failed), "failed in", f"{time.time() - t1:.1f}s:",
            ",".join(pushed[:10]))
    if time.time() >= END:
        break
    time.sleep(5)
log("end:", n, "re-pushes;", len(br), "ready/ branches;", len([g for g in br if g in ids]), "listed")
