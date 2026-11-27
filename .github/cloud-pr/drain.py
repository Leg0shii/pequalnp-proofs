#!/usr/bin/env python3
"""drain.py: cloud-pr DRAIN MODE (Lead 14:10 UTC 26 Nov). On the 8x8 wave 323 one-branch runs waited about 4 min each
for a runner (job 11 s), oldest first. Now every ready/ push starts the same job in ONE concurrency group: one run
works, one waits, GitHub cancels the rest. The working run takes every pending ready/ branch, NEWEST STEP FIRST
(re-listed after every finished branch, so a fresh push jumps the line), DRAIN_WORKERS (4) at once, each through the
unchanged single-branch path (.github/cloud-pr/submit.py: guards, race check, deskguard claim, PR). PR creations are
gated to 2 in flight (submit.py pr_gate, PR_GATE_DIR). Each (branch, commit) is done once: the record is the fork
branch drain-state (seen.txt "step sha result epoch", one writer because one run works at a time); a ready-wait
re-push is a new commit and runs again. A run stops after DRAIN_MAX_S (1200) or when nothing is pending for 30 s.
Env: SRC (fork main checkout), W, PR_TOKEN, READ_TOKEN, GITHUB_REPOSITORY."""
import base64, os, re, subprocess, sys, tempfile, threading, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import haltrule                                        # rule 16.1: the same halt rule as submit.py filing_halted()
from concurrent.futures import ThreadPoolExecutor

SRC = os.environ["SRC"]; W = os.environ.get("W") or tempfile.mkdtemp()
FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
URL = f"https://github.com/{FORK}.git"
PR_TOKEN = os.environ.get("PR_TOKEN", "")
PR_SLOTS = int(os.environ.get("DRAIN_PR_SLOTS", "6"))   # Lead 06:22 RC-b: 6 PR creations in flight (w12 load drill)
WORKERS = int(os.environ.get("DRAIN_WORKERS", "14"))   # Lead 17:17: 14 workers = about 10 leased + 10 unleased a minute with the gate open
MAX_S = float(os.environ.get("DRAIN_MAX_S", "1200")); LINGER = float(os.environ.get("DRAIN_LINGER", "30"))
UPSTREAM = os.environ.get("DRAIN_UPSTREAM", "https://github.com/open-goat/pequalnp-proofs.git")
DRY = os.environ.get("DRAIN_DRY", "0") == "1"       # test: everything but submit.py (prints what it would run)
T0 = time.time()
LOCK = threading.Lock(); FETCH = threading.Lock()
SEEN = {}            # (step, sha) -> (result, epoch)
GRANTS = []          # lines "step\tPR url\tpoints\trace\tUTC\tpath\tterms json" (Lead 14:36: what each path pays)
UNLEASED = []        # lines "step\tUTC\twhy" (lease-first refused or held: no PR)
STATS = {}


def log(*a):
    print(time.strftime("%H:%M:%S"), f"+{time.time() - T0:.0f}s", *a, flush=True)


def sh(*a, timeout=300, env=None, cwd=None, input=None):
    return subprocess.run(list(a), capture_output=True, text=True, timeout=timeout, env=env, cwd=cwd, input=input)


def auth():
    b = base64.b64encode(f"x-access-token:{PR_TOKEN}".encode()).decode()
    return ["-c", f"http.https://github.com/.extraheader=AUTHORIZATION: basic {b}"]


def linkedin_file():
    """config/linkedin.txt on toolkit main: one authenticated blobless shallow fetch, 20 s in all; '' on any failure."""
    if not PR_TOKEN:
        return ""
    import shutil
    g = tempfile.mkdtemp(prefix="li-")
    try:
        sh("git", "init", "-q", "--bare", g, timeout=10)
        sh("git", "-C", g, "remote", "add", "origin", "https://github.com/Leg0shii/pnp-toolkit.git", timeout=10)
        t = time.time()
        if sh("git", *auth(), "-C", g, "fetch", "-q", "--depth=1", "--filter=blob:none", "origin", "main", timeout=20).returncode:
            return ""
        r = sh("git", *auth(), "-C", g, "show", "FETCH_HEAD:config/linkedin.txt", timeout=max(1.0, 20 - (time.time() - t)))
        return r.stdout.strip() if r.returncode == 0 else ""
    except Exception:
        return ""
    finally:
        shutil.rmtree(g, ignore_errors=True)


def load_seen():
    if sh("git", "-C", SRC, "fetch", "-q", "--depth", "1", URL, "+refs/heads/drain-state:refs/drain/state").returncode:
        return
    for l in sh("git", "-C", SRC, "show", "refs/drain/state:seen.txt").stdout.splitlines():
        p = l.split()
        if len(p) == 4 and time.time() - float(p[3]) < 6 * 3600:
            SEEN[(p[0], p[1])] = (p[2], float(p[3]))
    GRANTS.extend(l for l in sh("git", "-C", SRC, "show", "refs/drain/state:grants.tsv").stdout.splitlines() if l.strip())
    UNLEASED.extend(l for l in sh("git", "-C", SRC, "show", "refs/drain/state:unleased.txt").stdout.splitlines() if l.strip())


def save_seen():
    """one commit with seen.txt on drain-state (force: this run is the only writer)"""
    txt = "".join(f"{k[0]} {k[1]} {v[0]} {v[1]:.0f}\n" for k, v in sorted(SEEN.items(), key=lambda kv: kv[1][1]))
    blob = sh("git", "-C", SRC, "hash-object", "-w", "--stdin", input=txt).stdout.strip()
    ents = f"100644 blob {blob}\tseen.txt\n"
    for name, lines in (("grants.tsv", GRANTS[-5000:]), ("unleased.txt", UNLEASED[-5000:])):
        b = sh("git", "-C", SRC, "hash-object", "-w", "--stdin", input="".join(l + "\n" for l in lines)).stdout.strip()
        ents += f"100644 blob {b}\t{name}\n"
    tree = sh("git", "-C", SRC, "mktree", input=ents).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="Leg0shii", GIT_COMMITTER_NAME="Leg0shii",
               GIT_AUTHOR_EMAIL="46093332+Leg0shii@users.noreply.github.com",
               GIT_COMMITTER_EMAIL="46093332+Leg0shii@users.noreply.github.com")
    c = sh("git", "-C", SRC, "commit-tree", tree, "-m", f"drain state {len(SEEN)}", env=env).stdout.strip()
    if c and not DRY:
        sh("git", *auth(), "-C", SRC, "push", "-q", "-f", URL, f"{c}:refs/heads/drain-state", timeout=120)


RETRYABLE = ("failed", "submitfail", "error")     # W6 mintfail: a child that died or failed half way is tried again
RETRY_MAX = 3
RETRY_WAIT = (0, 60, 300)                         # seconds after the 1st, 2nd, 3rd failure


def attempts(v):
    """(result, failures so far) of a SEEN value 'result' or 'result#n'"""
    if not v:
        return None, 0
    r, _, n = v[0].partition("#")
    return r, (int(n) if n.isdigit() else (1 if r in RETRYABLE else 0))


def retry_due(v):
    if v is None:
        return True
    r, n = attempts(v)
    # seen.txt rounds the time to whole seconds: allow 1 s
    return r in RETRYABLE and n < RETRY_MAX and time.time() - v[1] >= RETRY_WAIT[min(n, len(RETRY_WAIT)) - 1] - 1


def pending():
    r = sh("git", "ls-remote", URL, "refs/heads/ready/*", timeout=60)
    out = []
    for l in r.stdout.splitlines():
        sha, ref = l.split()
        sid = ref[len("refs/heads/ready/"):]
        if re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*", sid) and retry_due(SEEN.get((sid, sha))):
            out.append((sid, sha))
    def num(s):
        m = re.search(r"(\d+)$", s)
        return int(m.group(1)) if m else 0
    return sorted(out, key=lambda x: -num(x[0]))          # newest step first


T_ONE = {}


def one(sid, sha, prefix="ready", extra=None):
    T_ONE[sid] = time.time()
    d = tempfile.mkdtemp(prefix=sid + "-", dir=W)
    lref = f"refs/drain/{sid}"
    with FETCH:                                           # one shallow fetch at a time in the shared checkout
        f = sh("git", "-C", SRC, "fetch", "-q", "--depth", "1", URL, f"+refs/heads/{prefix}/{sid}:{lref}", timeout=120)
    if f.returncode:
        return "gone", "branch gone before the fetch"
    got = sh("git", "-C", SRC, "rev-parse", lref).stdout.strip()
    files = [x for x in sh("git", "-C", SRC, "ls-tree", "-r", "--name-only", lref, "ready/").stdout.split()
             if re.fullmatch(r"ready/[A-Za-z0-9_]+\.lean", x)]
    if len(files) != 1:
        return "error", f"ready/ must hold exactly one .lean file, found {len(files)}"
    proof = os.path.join(d, "proof.lean")
    open(proof, "w").write(sh("git", "-C", SRC, "show", f"{lref}:{files[0]}").stdout)
    mod = os.path.basename(files[0])[:-5]
    msg = sh("git", "-C", SRC, "log", "-1", "--format=%B", lref).stdout
    outs = [re.sub(r"\.", "/", m) for m in re.findall(r"(?m)^import (PEqualNP\.Outside\.[A-Za-z0-9_.]+)", open(proof).read())]
    tree = os.path.join(d, "tree")
    for att in range(3):
        ok = (sh("git", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout", "--single-branch",
                 "--branch", "main", UPSTREAM, tree, timeout=180).returncode == 0
              and sh("git", "-C", tree, "sparse-checkout", "set", "--no-cone", "/.github/", "/STOP", "/CONTRIBUTING.md",
                     "/lean/PEqualNP/", "!/lean/PEqualNP/Outside/", *[f"/lean/{o}.lean" for o in outs]).returncode == 0
              and sh("git", "-C", tree, "checkout", "-q", "main", timeout=180).returncode == 0)
        if ok:
            break
        sh("rm", "-rf", tree); time.sleep(5 * (att + 1))
    if not os.path.isdir(os.path.join(tree, ".github", "scripts")):
        return "error", "upstream checkout failed"
    os.makedirs(os.path.join(tree, "lean", "PEqualNP", "Outside"), exist_ok=True)
    outp = os.path.join(d, "out")
    env = dict(os.environ, ID=sid, MOD=mod, PROOF=proof, TREE=tree, W=d, DRY="0", GITHUB_REF_NAME=f"{prefix}/{sid}",
               GITHUB_OUTPUT=outp, PR_GATE_DIR=W, PR_GATE_N=str(PR_SLOTS), READY_MSG=msg, RIVAL_SNAP_DIR=W)
    env.update(extra or {})
    if DRY:
        return "dry", f"would run submit.py for {sid} {mod} ({os.path.getsize(proof)} bytes, sha {got[:8]})"
    t_sub = time.time()
    r = sh(sys.executable, "-I", os.path.join(SRC, ".github", "cloud-pr", "submit.py"), env=env, timeout=900)
    # Lead 19:14: the per-stage seconds of every unit in the drain log (prep = fetch of the ready commit + upstream
    # checkout before submit.py starts)
    for l in (r.stdout or "").splitlines():
        if " TIMES " in l or " gate: " in l or " SKIP " in l or " halted: " in l:
            log(sid, l.strip()[:200], f"prep={t_sub - T_ONE.get(sid, t_sub):.1f}" if " TIMES " in l else "")
    res = dict(l.split("=", 1) for l in open(outp).read().splitlines() if "=" in l) if os.path.exists(outp) else {}
    tail = (r.stdout + r.stderr).strip().splitlines()[-1:] or [""]
    now = time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime())
    with LOCK:
        if res.get("lease"):
            GRANTS.append("\t".join([sid, res.get("url", ""), res.get("points", ""), res.get("race", ""), now,
                                      "lease-first" if res.get("leasefirst") == "1" else "cloud", res.get("terms", "{}")]))
        if res.get("result") == "unleased":
            UNLEASED.append("\t".join([sid, now, res.get("why", "")[:160]]))
    return res.get("result", "failed"), (res.get("url") or res.get("why") or tail[0])[:200]


def work(sid, sha):
    t = time.time()
    try:
        res, why = one(sid, sha)
    except Exception as e:
        res, why = "error", repr(e)[:200]
    with LOCK:
        if res not in ("paused", "halted") and not (res == "unleased" and "desk off or paused" in why):
            if res in RETRYABLE:                           # W6: retried up to RETRY_MAX times (submit.py is idempotent:
                n = attempts(SEEN.get((sid, sha)))[1] + 1  # create-only head, our PR found, lease recovered)
                SEEN[(sid, sha)] = (f"{res}#{n}", time.time())
                if n >= RETRY_MAX:
                    log("GIVE-UP", sid, f"{res} {n} times:", why[:120])
            else:
                SEEN[(sid, sha)] = (res, time.time())      # paused ones run again after the pause
        STATS[res] = STATS.get(res, 0) + 1
        try:
            save_seen()
        except Exception as e:
            log("state save failed", repr(e)[:120])
    log("DONE", sid, res, f"{time.time() - t:.0f}s", why)
    return sid


_PZ = [0.0, 0.0]          # (checked at, paused until)
_FH = [0.0, False, ""]    # Lead 05:10: (checked at, halted, why) of the toolkit filing/stop vs filing/go refs


def halted():
    """rule 16.1 (haltrule.decide): newest filing/stop/<n> >= newest filing/go/<n> = halted (a tie too), a stop name
    that is not plain digits = halted, a go name that is not plain digits is ignored, unreadable = halted. Read at
    most every 10 s here (new branches only); every PR create re-checks within 2 s (submit.py filing_halted)."""
    if time.time() - _FH[0] > 10:
        for k in range(3):                    # live test 05:13: the toolkit needs auth; 3 tries 2 s apart
            r = sh("git", *auth(), "ls-remote", "https://github.com/Leg0shii/pnp-toolkit.git", "refs/heads/filing/*", timeout=60)
            if r.returncode == 0:
                break
            time.sleep(2)
        h, why = haltrule.decide(r.stdout, r.returncode == 0)
        _FH[:] = [time.time(), h, why]
    return _FH[1]


def paused():
    """GATEWAY v1 section 4 (Lead 16:50 UTC 26 Nov): a pause never stops filing. The opener asks deskgate for the lease
    and goes to the unleased branch when the gate is closed, so the drain never idles on a pause."""
    return False


def _paused_old():
    """(before GATEWAY v1) Shared deskguard pause (toolkit refs deskpause/<epoch>), read at most every 20 s."""
    if time.time() - _PZ[0] > 20:
        r = sh("git", *auth(), "ls-remote", "https://github.com/Leg0shii/pnp-toolkit.git", "refs/heads/deskpause/*", timeout=60)
        if r.returncode:
            _PZ[:] = [time.time(), time.time() + 60]
        else:
            ts = [int(l.rsplit("/", 1)[1]) for l in r.stdout.splitlines() if l.rsplit("/", 1)[-1].isdigit()]
            _PZ[:] = [time.time(), max(ts or [0])]
    return time.time() < _PZ[1]


def main():
    os.makedirs(W, exist_ok=True)
    if paused():                 # Lead 15:58: while the desk pause runs, the drain touches nothing (branches stay queued)
        log("shared desk pause until", time.strftime("%H:%M:%S", time.gmtime(_PZ[1])), "UTC: drain does nothing")
        return
    if halted():                 # Lead 05:10: one rejection halts all filing until the Lead's filing/go
        log("halted: drain files nothing,", _FH[2])
        return
    # Lead 05:50 (signed): the credit line from config/linkedin.txt in the toolkit when neither the secret nor the
    # variable gives one; read ONCE per drain, passed to every submit child; a failure means no line. Never logged.
    if not os.environ.get("PNP_LINKEDIN", "").strip():
        os.environ["PNP_LINKEDIN"] = linkedin_file()
    os.environ["PNP_LINKEDIN_READ"] = "1"
    load_seen()
    log("drain start,", len(SEEN), "branches already done in the last 6 h",
        "(credit line set)" if os.environ["PNP_LINKEDIN"] else "(no credit line)")
    inflight = {}; idle = None
    rf = refresher_start()
    try:
        _loop(inflight, idle)
    finally:
        refresher_stop(rf)
    log("drain end", STATS)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
            f.write(f"### drain: {sum(STATS.values())} branches\n{STATS}\n")


def refresher_start():
    """RC-b 1 (Lead 06:22): one background `submit.py --refresh` per drain keeps W/halt.json and W/rival_snap.json at
    most 2 s old, so no worker reads GitHub while it holds a PR slot. If it dies, workers read inline (never stale)."""
    if DRY or os.environ.get("DRAIN_REFRESHER", "0") != "1":     # on in cloud-pr.yml (var DRAIN_REFRESHER, kill switch);
        return None                                               # off in drills that run the real drain.py
    env = dict(os.environ, ID="refresher", MOD="refresher", PROOF=os.devnull, TREE=W, W=os.path.join(W, "refresher"),
               DRY="0", PR_GATE_DIR=W, PR_GATE_N=str(PR_SLOTS), RIVAL_SNAP_DIR=W, GITHUB_OUTPUT=os.devnull)
    os.makedirs(env["W"], exist_ok=True)
    try:
        os.remove(os.path.join(W, "refresh.stop"))
    except OSError:
        pass
    out = open(os.path.join(W, "refresher.log"), "a")
    p = subprocess.Popen([sys.executable, "-I", os.path.join(SRC, ".github", "cloud-pr", "submit.py"), "--refresh"],
                         env=env, stdout=out, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    log("refresher started, pid", p.pid)
    return p


def refresher_stop(p):
    if not p:
        return
    open(os.path.join(W, "refresh.stop"), "w").close()
    try:
        p.wait(timeout=10)
    except subprocess.TimeoutExpired:
        p.kill()
    hb = ""
    try:
        hb = open(os.path.join(W, "refresh.hb")).read().strip()
    except OSError:
        pass
    log("refresher stopped, rc", p.returncode, "last heartbeat (epoch passes counted not_modified remaining):", hb)


def _loop(inflight, idle):
    with ThreadPoolExecutor(WORKERS) as ex:
        while time.time() - T0 < MAX_S:
            for k in [k for k, fu in inflight.items() if fu.done()]:
                inflight.pop(k)
            if halted():
                log("halted: no new branch, in-flight ones stop before their PR,", _FH[2]); todo = []
                if not inflight:
                    break
            elif paused():
                log("shared desk pause started: no new branch, in-flight ones finish"); todo = []
                if not inflight:
                    break
            else:
                todo = [x for x in pending() if x not in inflight] if len(inflight) < WORKERS else []
            for x in todo[:WORKERS - len(inflight)]:
                inflight[x] = ex.submit(work, *x)
                log("START", x[0], x[1][:8], f"({len(todo)} pending)")
            if not inflight and not todo:
                idle = idle or time.time()
                if time.time() - idle > LINGER:
                    break
            else:
                idle = None
            time.sleep(1 if inflight else 3)


if __name__ == "__main__":
    main()
