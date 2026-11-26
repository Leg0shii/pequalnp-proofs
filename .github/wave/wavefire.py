#!/usr/bin/env python3
"""wavefire: open the PRs of a pre-staged wave the moment the desk lists it (Lead order 19:09 UTC).

Pre-staged: fork branch L-meta-<id> = upstream main + the store file, one per store hit of the wave. At listing this
job only calls `gh pr create` for its share (id % MOD == REM), highest id first (rivals sweep upward), skipping ids on
the taken list (toolkit status/taken, ignored when older than 180 s). The posted statement is checked against the staged
file when gaps.json has it; a different numeral spelling of the same table is re-spelled and re-pushed first.
PRs only, never a desk call. GitHub content creation is shared with the PC (about 80/min, 500/h per account): at most
RATE PRs per minute here, PAR at a time, and a secondary-rate-limit answer backs off (60 s, doubling to 10 min)
instead of stopping. STOP file on upstream main = stop. Prints PRs per minute."""
import json, os, re, subprocess, sys, threading, time

UP = "open-goat/pequalnp-proofs"; FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
HANDLE = "Leg0shii"; EMAIL = "46093332+Leg0shii@users.noreply.github.com"
BODY = "Proof written by an AI worker.\n\n\U0001F916 Generated with [Claude Code](https://claude.com/claude-code)"
LIST = os.environ.get("WAVE_LIST", ".github/wave/wave6c-all.txt")
MOD, REM = int(os.environ.get("WAVE_MOD", "4")), int(os.environ.get("WAVE_REM", "3"))
RATE, PAR = float(os.environ.get("WAVE_RATE", "30")), int(os.environ.get("WAVE_PAR", "2"))
END = time.time() + float(os.environ.get("MINUTES", "120")) * 60
W = os.environ.get("W", "/tmp/wave"); os.makedirs(W, exist_ok=True); G = os.path.join(W, "g.git")
TK = "https://github.com/Leg0shii/pnp-toolkit.git"
lock = threading.Lock(); state = {"backoff_until": 0, "backoff": 60, "stop": False}
created, done, failed, skipped = [], set(), {}, {}


def run(cmd, timeout=120, inp=None, env=None):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, input=inp, env=env)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(cmd, 124, "", "timeout")


def log(*a):
    print(time.strftime("%H:%M:%S", time.gmtime()), *a, flush=True)


def norm(s):
    return " ".join((s or "").split())


ids = {}
for l in open(LIST):
    if l.startswith("#") or not l.strip():
        continue
    gid, hx, dec, A, B = l.split()
    if int(gid.split("-")[-1]) % MOD == REM:
        ids[gid] = (int(dec), f"{A} * 2 ^ 32 + {B}")


def staged():
    r = run(["git", "ls-remote", f"https://github.com/{FORK}.git", "refs/heads/L-meta-*"])
    return {l.split("\t")[1][11:]: l.split("\t")[0] for l in r.stdout.splitlines() if "\t" in l}


def gaps():
    r = run(["curl", "-sS", "-m", "30", f"https://data.pequalnp.com/data/desk/gaps.json?t={int(time.time())}"], 40)
    try:
        return {g["id"]: g for g in json.loads(r.stdout)["gaps"]}
    except Exception:
        return None


def status_ids():
    # 16:00 pause (Lead condition 2): no desk-host read from any Action; the static gaps.json is the only listing
    return set()


def taken():
    if run(["git", "-C", G, "fetch", "-q", "--depth=1", TK, "+refs/heads/status/taken:refs/taken"], 60).returncode:
        return None
    t = run(["git", "-C", G, "show", "refs/taken:taken.txt"]).stdout.splitlines()
    if not t or not t[0].startswith("# updated") or time.time() - int(t[0].split()[2]) > 120:
        return None
    return {l.split()[0]: l.split()[2] for l in t[1:] if l.strip()}


def stopped():
    r = run(["curl", "-sS", "-o", "/dev/null", "-w", "%{http_code}", "-m", "10",
             f"https://raw.githubusercontent.com/{UP}/main/STOP"], 20)
    return r.stdout.strip() == "200"


def check_statement(gid, sha, posted):
    """True if the staged file states exactly the posted statement; re-spells the numeral (same table) and re-pushes
    when only the spelling differs. False = do not open (mismatch we cannot fix here)."""
    mod = gid.replace("-", "_"); rel = f"lean/PEqualNP/Outside/{mod}.lean"
    if run(["git", "-C", G, "fetch", "-q", "--depth=2", f"https://github.com/{FORK}.git", sha], 120).returncode:
        return None
    txt = run(["git", "-C", G, "show", f"{sha}:{rel}"]).stdout
    m = re.search(rf"^theorem PEqualNP\.Outside\.{mod} :(.*?):=", txt, re.M | re.S)
    if m and norm(m.group(1)) == norm(posted):
        return True
    num_p = re.findall(r"Nat\.testBit \(([0-9 *+^]+)\)", posted)
    T, mine = ids[gid]
    if not num_p or len(set(norm(x) for x in num_p)) != 1:
        return False
    newnum = norm(num_p[0])
    try:
        if eval(newnum.replace("^", "**"), {"__builtins__": {}}) != T:
            return False
    except Exception:
        return False
    txt2 = txt.replace(f"Nat.testBit ({mine})", f"Nat.testBit ({newnum})")
    m = re.search(rf"^theorem PEqualNP\.Outside\.{mod} :(.*?):=", txt2, re.M | re.S)
    if not m or norm(m.group(1)) != norm(posted):
        return False
    parent = run(["git", "-C", G, "rev-parse", f"{sha}^"]).stdout.strip()
    blob = run(["git", "-C", G, "hash-object", "-w", "--stdin"], inp=txt2).stdout.strip()
    idx = os.path.join(W, f"{gid}.idx"); env = dict(os.environ, GIT_INDEX_FILE=idx)
    run(["git", "-C", G, "read-tree", parent], env=env)
    run(["git", "-C", G, "update-index", "--add", "--cacheinfo", f"100644,{blob},{rel}"], env=env)
    tree = run(["git", "-C", G, "write-tree"], env=env).stdout.strip()
    cenv = dict(os.environ, GIT_AUTHOR_NAME=HANDLE, GIT_COMMITTER_NAME=HANDLE, GIT_AUTHOR_EMAIL=EMAIL, GIT_COMMITTER_EMAIL=EMAIL)
    c = run(["git", "-C", G, "commit-tree", tree, "-p", parent, "-m",
             gid + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n"], env=cenv).stdout.strip()
    r = run(["git", "-C", G, "push", "-q", "-f", f"https://github.com/{FORK}.git", f"{c}:refs/heads/{gid}"], 300)
    log("RESPELL", gid, mine, "->", newnum, "ok" if r.returncode == 0 else r.stderr.strip()[:120])
    return r.returncode == 0


def open_pr(gid):
    for att in range(12):
        while time.time() < state["backoff_until"]:
            time.sleep(1)
        with lock:                                  # pace: at most RATE creations per rolling minute
            while len([t for t in created if time.time() - t[0] < 60]) >= RATE:
                lock.release(); time.sleep(0.5); lock.acquire()
        r = run(["gh", "pr", "create", "--repo", UP, "--head", f"{HANDLE}:{gid}", "--base", "main",
                 "--title", gid, "--body", BODY], 120)
        out = r.stdout + r.stderr
        url = (re.findall(r"https://github\.com/\S+/pull/\d+", out) or [None])[0]
        if url or "already exists" in out:
            with lock:
                created.append((time.time(), gid))
                state["backoff"] = 60
            log("PR", gid, url or "already exists")
            return True
        if re.search(r"secondary rate limit|submitted too quickly|abuse|HTTP 403|HTTP 429|was submitted too", out, re.I):
            with lock:
                if time.time() >= state["backoff_until"]:
                    state["backoff_until"] = time.time() + state["backoff"]
                    log("BACKOFF", state["backoff"], "s:", out.strip()[:150].replace("\n", " "))
                    state["backoff"] = min(600, state["backoff"] * 2)
            continue
        if re.search(r"HTTP 5\d\d|timeout|Something went wrong|connection|EOF", out, re.I) and att < 11:
            time.sleep(5 * (att + 1)); continue
        log("PR-FAIL", gid, out.strip()[:200].replace("\n", " "))
        failed[gid] = out.strip()[:200]
        return False
    failed[gid] = "gave up after retries"
    return False


run(["git", "init", "-q", "--bare", G])
log(f"wavefire: {len(ids)} ids with id % {MOD} == {REM}, rate {RATE}/min, {PAR} parallel, until",
    time.strftime("%H:%M", time.gmtime(END)))
queue = []; qlock = threading.Condition(); t_first = [None]; tk = {}; tk_t = 0; st = {}; st_t = 0; last_s = 0; sids = set()


ORDER = os.environ.get("WAVE_ORDER", "high")


def prio(n):
    """high: highest id first. middle (Lead 19:25): 15100-15799, then the 15800s, 15900s, 16000s, then the rest; inside
    a block highest first (rivals sweep upward from the bottom)."""
    if ORDER != "middle":
        return (0, -n)
    blocks = [(15100, 15799), (15800, 15899), (15900, 15999), (16000, 16099)]
    for i, (a, b) in enumerate(blocks):
        if a <= n <= b:
            return (i, -n)
    return (len(blocks), -n)


def worker():
    while True:
        with qlock:
            while not queue and not state["stop"]:
                qlock.wait(2)
                if time.time() > END:
                    return
            if state["stop"] and not queue:
                return
            queue.sort(key=lambda x: prio(int(x[0].split("-")[-1])))
            gid, sha, posted = queue.pop(0)
        if gid in tk:                       # a PR from anyone (ours included: opened by an earlier job or the PC)
            skipped[gid] = "taken by " + tk[gid]; log("SKIP", gid, skipped[gid]); continue
        if posted is not None:
            ok = check_statement(gid, sha, posted)
            if ok is False:
                skipped[gid] = "statement mismatch"; log("SKIP", gid, "statement mismatch"); continue
        if t_first[0] is None:
            t_first[0] = time.time()
        open_pr(gid)


ths = [threading.Thread(target=worker, daemon=True) for _ in range(PAR)]
for t in ths:
    t.start()
last_stop = 0
while time.time() < END:
    now = time.time()
    if now - last_stop > 30:
        last_stop = now
        if stopped():
            log("STOP file on upstream main: no more PRs"); state["stop"] = True; break
    if now - st_t > 60:
        st = staged(); st_t = now
    if now - tk_t > 20:
        tk = taken() or tk; tk_t = now
    g = gaps() or {}
    if now - last_s > 15:
        sids = status_ids(); last_s = now
    new = [gid for gid in ids if gid not in done and (gid in g or gid in sids) and gid in st]
    if new:
        with qlock:
            for gid in new:
                done.add(gid)
                queue.append((gid, st[gid], (g.get(gid) or {}).get("statement")))
            qlock.notify_all()
        log("LISTED", len(new), "new, e.g.", ", ".join(sorted(new, key=lambda x: -int(x[7:]))[:5]))
    if t_first[0] and len(done) == len([x for x in ids if x in st]) and not queue:
        time.sleep(30)
        if not queue:
            break
    time.sleep(5)
state["stop"] = True
with qlock:
    qlock.notify_all()
for t in ths:
    t.join(timeout=900)
span = (max(t for t, _ in created) - min(t for t, _ in created)) if len(created) > 1 else 0
log(f"END: {len(created)} PRs, {len(skipped)} skipped, {len(failed)} failed;",
    f"{len(created) / (span / 60):.1f} PRs/min over {span:.0f} s" if span else "")
for k, v in sorted(failed.items()):
    log("FAILED", k, v)
