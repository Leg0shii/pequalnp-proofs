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
import base64, json, os, re, subprocess, sys, tempfile, time

UP = "open-goat/pequalnp-proofs"
GAPS = "https://data.pequalnp.com/data/desk/gaps.json"
STATUS = "https://pequalnp.com/desk/status"
STEP = "https://pequalnp.com/desk/step?gap="
DESK = "https://pequalnp.com/desk/"
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


def curl_json(url, timeout=60):
    # the desk refuses python urllib (Cloudflare), so curl, like the PC watcher
    for att in range(3):
        r = run(["curl", "-sSf", "--max-time", str(timeout), url], timeout=timeout + 10)
        if r.returncode == 0:
            return json.loads(r.stdout)
        time.sleep(3 * (att + 1))
    raise RuntimeError(f"curl {url}: {r.stderr.strip()[:200]}")


def gh(args, write=False, timeout=120):
    """gh with the run's own token for reads (falls back to PR_TOKEN), PR_TOKEN for writes. Retries transient errors."""
    toks = [PR_TOKEN] if write else [READ_TOKEN, PR_TOKEN]
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
    """Last intake verdict on the PR is ACCEPTED. Any doubt = True (it blocks)."""
    try:
        out = gh(["pr", "view", str(number), "--repo", UP, "--json", "comments", "--jq",
                  "[.comments[].body | select(test(\"ACCEPTED|REJECTED|REFUSED|FAULT\"))] | last // \"\""]).stdout
        return "ACCEPTED" in out
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


def race_check(step_id):
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


def desk(path, post=False):
    time.sleep(max(0, _DESK_T[0] + 3 - time.time()))      # the desk asks for one request every few seconds
    r = run(["curl", "-sS", "--max-time", "30", "-w", "\n%{http_code}"] + (["-X", "POST"] if post else []) + [DESK + path], timeout=40)
    _DESK_T[0] = time.time()
    body, _, code = r.stdout.rpartition("\n")
    try:
        d = json.loads(body)
    except Exception:
        d = {"error": (body or r.stderr).strip()[:200]}
    if isinstance(d, dict):
        d["_http"] = code.strip()
    return d


PAUSED = [False]
PAUSE_REF = "refs/heads/status/desk-pause"     # on this fork: unix time until which no run may ask the desk


def set_pause(until):
    """Record the desk's pause on this fork, so later runs make no desk request at all until it is over."""
    if DRY or not PR_TOKEN:
        return
    g = os.path.join(W, "pause.git")
    run(["git", "init", "-q", "--bare", g])
    blob = subprocess.run(["git", "-C", g, "hash-object", "-w", "--stdin"], input=f"{until}\n", capture_output=True, text=True).stdout.strip()
    tree = subprocess.run(["git", "-C", g, "mktree"], input=f"100644 blob {blob}\tuntil.txt\n", capture_output=True, text=True).stdout.strip()
    cenv = dict(os.environ, GIT_AUTHOR_NAME=HANDLE, GIT_COMMITTER_NAME=HANDLE, GIT_AUTHOR_EMAIL=EMAIL, GIT_COMMITTER_EMAIL=EMAIL)
    c = run(["git", "-C", g, "commit-tree", tree, "-m", f"desk pause until {until}"], env=cenv).stdout.strip()
    r = run(["git"] + auth_cfg() + ["-C", g, "push", "-q", "-f", f"https://github.com/{FORK}.git", f"{c}:{PAUSE_REF}"], timeout=60)
    log("desk pause recorded until", time.strftime("%H:%M:%S", time.gmtime(until)), "UTC" if r.returncode == 0 else "(push failed)")


def read_pause():
    g = os.path.join(W, "pause.git")
    run(["git", "init", "-q", "--bare", g])
    if run(["git", "-C", g, "fetch", "-q", "--depth=1", f"https://github.com/{FORK}.git", f"+{PAUSE_REF}:{PAUSE_REF}"], timeout=60).returncode:
        return 0
    try:
        return int(run(["git", "-C", g, "show", f"{PAUSE_REF}:until.txt"]).stdout.strip() or 0)
    except ValueError:
        return 0


def claim_lock(gid):
    """At most ONE desk claim per step, ever, across all runs (Lead/coordinator 18:26 after the desk paused the handle
    for repeated claims): tag claim/<gid> on this fork is created without force, so only the first run gets it."""
    if DRY or not PR_TOKEN:
        return False
    g = os.path.join(W, "pause.git")
    run(["git", "init", "-q", "--bare", g])
    tree = subprocess.run(["git", "-C", g, "mktree"], input="", capture_output=True, text=True).stdout.strip()
    cenv = dict(os.environ, GIT_AUTHOR_NAME=HANDLE, GIT_COMMITTER_NAME=HANDLE, GIT_AUTHOR_EMAIL=EMAIL, GIT_COMMITTER_EMAIL=EMAIL,
                GIT_AUTHOR_DATE="2026-01-01T00:00:00Z", GIT_COMMITTER_DATE="2026-01-01T00:00:00Z")
    c = run(["git", "-C", g, "commit-tree", tree, "-m", "desk claim lock"], env=cenv).stdout.strip()
    r = run(["git"] + auth_cfg() + ["-C", g, "push", "-q", f"https://github.com/{FORK}.git", f"{c}:refs/tags/claim/{gid}"], timeout=60)
    return r.returncode == 0


def claim(gid):
    """No desk request at all once the desk said the handle is paused: every request while paused extends the pause.
    One claim per step ever (claim_lock); a 410 (proved first) is final."""
    if PAUSED[0]:
        return None, "claim skipped: handle paused by the desk"
    if not claim_lock(gid):
        return None, "claim skipped: this step was claimed once already"
    d = desk(f"next?handle={HANDLE}&gap={gid}&have=proof&another=1")
    if d.get("_http") == "410":
        return None, "gone (410): proved first " + json.dumps(d)[:120]
    if "paused" in str(d.get("error", "")):
        PAUSED[0] = True
        try:
            set_pause(int(time.time()) + int(d.get("retry_after_s") or 3600))
        except Exception as e:
            log("could not record the desk pause:", e)
        return None, "claim refused: handle paused: " + str(d.get("error"))[:160]
    le = d.get("lease"); gp = d.get("gap") or {}
    lid = le.get("id") if isinstance(le, dict) else le
    if not lid or (isinstance(gp, dict) and gp.get("id") not in (None, gid)):
        return None, "claim refused: " + json.dumps(d)[:200]
    return str(lid), "claimed" + (" (race)" if isinstance(le, dict) and (le.get("terms") or {}).get("race") else "")


def claim_retry(gid):
    return claim(gid)            # one claim per step, ever: no retries (the desk pauses handles that repeat)


def release(lid, reason):
    if lid and not DRY:
        log("desk release", reason, json.dumps(desk(f"release?lease={lid}&reason={reason}", post=True))[:120])


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
        if g.get("kind") == "value":            # value steps (lane atlas) are not desk steps
            b = race_check(gid)
            return (not b), (f"blocking PRs {b}" if b else "clear"), None
        held = {x["id"]: x.get("held", 0) for x in curl_json(STATUS, 60)["gaps"]}
        if gid not in held:
            return False, "not on the desk", None
        is_h = held[gid] != 0
        if not is_h:
            st = curl_json(STEP + gid, 30)
            if st.get("state") not in ("open", "pr_open"):
                return False, f"desk state {st.get('state')}", None
        b = race_check(gid)
        if b:
            return False, f"blocking PRs {b}", None
        if not is_h:     # unheld: the lease is taken right before gh pr create (watch.py submit, Lead D4)
            return True, "clear", None
        if DRY:
            return True, "clear (dry run: held, no claim)", None
        lid, why = claim_retry(gid)      # held by someone else: our have=proof lease is required before the push
        if not lid:
            return False, why, None
        return True, "clear, " + why, lid
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
    """Our own open PR whose head is this fork's branch <gid> (exact, no search index lag)."""
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
    err = push_branch(c, gid)
    if err:
        return None, "push: " + err
    log("pushed", c[:12], "to", f"{FORK}:{gid}")
    own = None                                      # a lease claimed here is released by main() (submitted / other)
    r = None
    for att in range(5):
        if stopped():                    # STOP may appear while this PR waited for a retry
            return None, "STOP file on upstream main"
        if not lease and KIND != "value":
            lid, cwhy = claim(gid)
            if cwhy.startswith("gone (410)"):
                return None, "file already in upstream main"      # proved first: final, a lost race
            if lid:
                lease = own = lid
            else:
                log("desk claim failed (PR goes anyway, unheld step):", cwhy[:160])
        body = DESC + (f"\n\nLease: {lease}" if lease else "") + FOOTER
        r = run(["gh", "pr", "create", "--repo", UP, "--head", f"{HANDLE}:{gid}", "--base", "main",
                 "--title", gid, "--body", body], timeout=120, env=dict(os.environ, GH_TOKEN=PR_TOKEN))
        if re.search(r"https://\S+", r.stdout) or "already exists" in r.stderr:
            break                                   # an existing PR for our branch is a success
        if not TRANSIENT.search(r.stderr + r.stdout) or att == 4:
            break
        log("PR retry in", 30 * 2 ** att, "s:", r.stderr.strip()[:150])
        time.sleep(30 * 2 ** att)
    url = (re.findall(r"https://github\.com/\S+/pull/\d+", r.stdout + r.stderr) or [None])[0]
    LEASE[0] = lease
    return url, ("ok" if url else r.stderr.strip()[:300])


def delete_ready():
    if DRY or os.environ.get("GITHUB_EVENT_NAME") != "push":
        return
    r = run(["git"] + auth_cfg() + ["-C", TREE, "push", "-q", f"https://github.com/{FORK}.git", "--delete", f"ready/{ID}"], timeout=120)
    log("deleted ready/" + ID if r.returncode == 0 else "could not delete ready/" + ID + ": " + r.stderr.strip()[:120])


def finish(result, why, url=None):
    log(f"RESULT={result}", ID, url or "", why)
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            f.write(f"result={result}\nwhy={why[:300].replace(chr(10), ' ')}\nurl={url or ''}\n")
    if result in ("submitted", "race", "exists", "formatfail"):
        delete_ready()
    sys.exit(1 if result in ("submitfail", "formatfail", "error", "stopped") else 0)


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
    r = run(["bash", os.path.join(os.path.dirname(os.path.abspath(__file__)), "checkcore.sh"), PROOF, ID, TREE,
             os.path.join(W, "guard"), "--quick"], env=env, timeout=600)
    print(r.stdout[-3000:], r.stderr[-2000:], sep="\n", flush=True)
    git("clean", "-q", "-f", "--", "lean/PEqualNP/Outside/")          # the closure guard copied the file in
    if r.returncode:
        finish("formatfail", "guards: " + ((r.stdout + r.stderr).strip().splitlines() or ["?"])[-1][:200])
    log(f"guards passed ({time.time() - t0:.0f}s)")
    pu = read_pause()
    if pu > time.time():
        PAUSED[0] = True
        log("the desk paused this handle until", time.strftime("%H:%M:%S", time.gmtime(pu)), "UTC: no desk requests in this run")
    if not DRY and stopped():
        finish("stopped", "STOP file on upstream main: no PR, no lease (branch kept; re-run the job once STOP is gone)")
    # 2. race check right before the push
    ok, why, lease = race_ok(ID)
    if not ok:
        # an error or the desk's lease cap is not a lost race: keep the branch (re-run the job), the PC still has its copy
        finish("error" if why.startswith("race check error") or "most one handle may hold" in why or "paused" in why
               else "race", why)          # a 410 or an earlier claim of this step ends here as a lost race
    log("race check:", why)
    # 3.+4. commit on upstream main, push, PR
    LEASE[0] = lease
    url, why2 = submit(ID, lease)
    release(LEASE[0], "submitted" if url else "other")
    if url == "dry-run":
        finish("dry", why2)
    if not url and why2 == "file already in upstream main":
        finish("race", why2)
    if not url and why2.startswith("STOP"):
        finish("stopped", why2 + " (branch kept)")
    finish("submitted" if url else "submitfail", f"{why2}; {time.time() - t0:.0f}s after start", url)


if __name__ == "__main__":
    main()
