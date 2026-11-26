#!/usr/bin/env python3
"""ready-wait: restart cloud-pr for kept ready/<ID> branches the moment the desk lists the step (re-push on current
fork main, so the run uses today's opener code).

cloud-pr ends 'waiting' and keeps ready/<ID> when the step is not listed yet (pre-generated waves). This loop polls the
listing (data.pequalnp.com gaps.json and pequalnp.com/desk/status: plain reads, no handle, no claim) and the fork's
ready/ branches, and re-pushes each listed one on current fork main once per step per job. A branch must be at
least MIN_AGE s old, so the push run of a fresh branch is never doubled. Dispatches are paced (GitHub allows about
2 PR creations in parallel; cloud-pr retries refusals)."""
import json, os, re, subprocess, sys, time

FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
END = time.time() + float(os.environ.get("MINUTES", "58")) * 60
MIN_AGE = 60
PACE = float(os.environ.get("PACE_S", "4"))
G = os.path.join(os.environ.get("W", "/tmp"), "rw.git")
first_seen, done = {}, set()
TRIES = {}      # gid -> (re-pushes, last epoch): a run that ended "waiting" (gaps.json behind desk/status) keeps the
RETRY_S, MAX_TRIES = 60, 4   # branch; it is re-pushed again after RETRY_S, at most MAX_TRIES times per job


def run(cmd, timeout=60):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        return subprocess.CompletedProcess(cmd, 124, "", "timeout")


def log(*a):
    print(time.strftime("%H:%M:%S", time.gmtime()), *a, flush=True)


def listed():
    ids = set()
    for url, key in (("https://data.pequalnp.com/data/desk/gaps.json", "gaps"), ("https://pequalnp.com/desk/status", "gaps")):
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
    c = subprocess.run(["git", "-C", G, "commit-tree", tree, "-p", "main", "-m", f"ready {gid} (ready-wait: listed)"],
                       env=cenv, capture_output=True, text=True).stdout.strip()
    if not c:
        return subprocess.CompletedProcess([], 1, "", "commit-tree failed")
    return run(["git", "-C", G, "push", "-q", "-f", url, f"{c}:refs/heads/ready/{gid}"], 180)


run(["git", "init", "-q", "--bare", G])
n = 0; last_l = 0; ids = set()
while time.time() < END:
    br = branches()
    now = time.time()
    for gid, sha in br.items():
        first_seen.setdefault((gid, sha), now)
    if now - last_l >= 10:
        ids = listed() or ids; last_l = now
    ids = ids | signal()
    # once per step per job (a re-push changes the sha, so the step id is the key)
    for g in list(done):      # still there RETRY_S after our re-push = that run waited or failed: allow another
        k, t = TRIES.get(g, (0, 0))
        if g in br and k < MAX_TRIES and now - t >= RETRY_S:
            done.discard(g)
    todo = [(g, s) for g, s in br.items() if g not in done and g in ids and now - first_seen[(g, s)] >= MIN_AGE]
    for gid, sha in sorted(todo, key=lambda x: first_seen[x]):
        if not re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*", gid):
            done.add(gid); TRIES[gid] = (MAX_TRIES, 0); continue
        f = ready_file(gid, sha)
        done.add(gid)
        if not f:
            TRIES[gid] = (MAX_TRIES, 0)
            log("SKIP", gid, "no single ready/ file"); continue
        r = repush(gid, sha, f)
        n += 1; TRIES[gid] = (TRIES.get(gid, (0, 0))[0] + 1, time.time())
        log("REPUSH" if r.returncode == 0 else "REPUSH-FAIL", gid, f, (r.stderr or "").strip()[:150])
        if r.returncode:
            done.discard(gid)
        time.sleep(PACE)
        if time.time() >= END:
            break
    time.sleep(5)
log("end:", n, "re-pushes;", len(br), "ready/ branches;", len([g for g in br if g in ids]), "listed")
