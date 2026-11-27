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
import base64, json, os, re, subprocess, sys, tempfile, threading, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import haltrule                                        # rule 16.1 (w9's haltrule.py): the same rule as submit.py and the closer
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
# Lead 06:30 LIVE DRY LOAD CANARY (loadcanary.yml): DRAIN_PREFIX=loadtest drains refs loadtest/<ID> with every submit.py
# in DRY mode (guards, race check, no claim, no push, no PR) and keeps its own state branch. Only "ready" ever files.
PREFIX = os.environ.get("DRAIN_PREFIX", "ready")
if not re.fullmatch(r"ready|loadtest", PREFIX):
    sys.exit(f"DRAIN_PREFIX {PREFIX!r}: only ready or loadtest")
CHILD_DRY = "0" if PREFIX == "ready" else "1"
STATE_REF = "drain-state" if PREFIX == "ready" else f"drain-state-{PREFIX}"
if PREFIX == "loadtest" and os.environ.get("GITHUB_RUN_ID"):
    # infra 09:02 (r3 45968532320): parallel canaries force-pushed the one drain-state-loadtest ref (3 failed pushes in a row,
    # job red) and each run loaded the others' seen units at start. A loadtest drain keeps its own state per run attempt.
    STATE_REF += f"-{os.environ['GITHUB_RUN_ID']}-{os.environ.get('GITHUB_RUN_ATTEMPT', '1')}"
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
    if PREFIX != "ready":          # load canary: every run drains every loadtest/ ref again (its state is write-only)
        return
    if sh("git", "-C", SRC, "fetch", "-q", "--depth", "1", URL, f"+refs/heads/{STATE_REF}:refs/drain/state").returncode:
        return
    for l in sh("git", "-C", SRC, "show", "refs/drain/state:seen.txt").stdout.splitlines():
        p = l.split()
        if len(p) == 4 and time.time() - float(p[3]) < 6 * 3600:
            SEEN[(p[0], p[1])] = (p[2], float(p[3]))
    GRANTS.extend(l for l in sh("git", "-C", SRC, "show", "refs/drain/state:grants.tsv").stdout.splitlines() if l.strip())
    UNLEASED.extend(l for l in sh("git", "-C", SRC, "show", "refs/drain/state:unleased.txt").stdout.splitlines() if l.strip())


def save_seen(seen=None, grants=None, unleased=None):
    """one commit with seen.txt on drain-state (force: this run is the only writer). w12 speed fix 1: called by the
    saver thread with copies taken under LOCK (never while LOCK is held); raises when the push fails."""
    seen = SEEN if seen is None else seen
    grants = GRANTS if grants is None else grants
    unleased = UNLEASED if unleased is None else unleased
    txt = "".join(f"{k[0]} {k[1]} {v[0]} {v[1]:.0f}\n" for k, v in sorted(seen.items(), key=lambda kv: kv[1][1]))
    blob = sh("git", "-C", SRC, "hash-object", "-w", "--stdin", input=txt).stdout.strip()
    ents = f"100644 blob {blob}\tseen.txt\n"
    for name, lines in (("grants.tsv", grants[-5000:]), ("unleased.txt", unleased[-5000:])):
        b = sh("git", "-C", SRC, "hash-object", "-w", "--stdin", input="".join(l + "\n" for l in lines)).stdout.strip()
        ents += f"100644 blob {b}\t{name}\n"
    tree = sh("git", "-C", SRC, "mktree", input=ents).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="Leg0shii", GIT_COMMITTER_NAME="Leg0shii",
               GIT_AUTHOR_EMAIL="46093332+Leg0shii@users.noreply.github.com",
               GIT_COMMITTER_EMAIL="46093332+Leg0shii@users.noreply.github.com")
    c = sh("git", "-C", SRC, "commit-tree", tree, "-m", f"drain state {len(seen)}", env=env).stdout.strip()
    if not c:
        raise RuntimeError("state commit failed")
    if not DRY:
        r = sh("git", *auth(), "-C", SRC, "push", "-q", "-f", URL, f"{c}:refs/heads/{STATE_REF}", timeout=120)
        if r.returncode:
            raise RuntimeError("state push rc=%d %s" % (r.returncode, " | ".join(r.stderr.strip().splitlines())[-300:]))


# w12 speed fix 1 (Lead 06:30): the drain-state push (2-5 s) ran inside LOCK once per finished unit, so every worker
# queued on it: about 17 units a minute whatever DRAIN_WORKERS said (mintload, dc6a46de 28x6: 18.1 a minute; with the
# push free: 41.3). Now ONE saver thread pushes at most every SAVE_EVERY_S from copies taken under LOCK; a final save
# runs at drain end (atexit) and on SIGTERM/SIGINT. A failed push is logged and retried at the next tick; 3 failures
# in a row or a dead saver raise an ::error:: annotation; workers never wait for a push and filing continues. A unit
# finished after the last save runs again in the next drain: submit.py is idempotent there (create-only head; our
# open PR on the existing branch = "exists", W6 23cf0eb9).
SAVE_EVERY_S = float(os.environ.get("DRAIN_SAVE_EVERY_S", "10"))
_SV = {"dirty": False, "fails": 0, "saves": 0, "restarts": 0, "thread": None, "stop": threading.Event(), "final": False}
_SAVE_ONE = threading.Lock()          # one push at a time (saver tick, final save)


def _alert(msg):
    log("ALERT", msg)
    print(f"::error::drain {msg}", flush=True)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        try:
            with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
                f.write(f"**drain ALERT**: {msg}\n")
        except Exception:
            pass


def save_now(why="tick"):
    """take copies under LOCK, push outside it; True when saved or nothing to save"""
    with _SAVE_ONE:
        with LOCK:
            if not _SV["dirty"]:
                return True
            snap = (dict(SEEN), list(GRANTS), list(UNLEASED)); _SV["dirty"] = False
        try:
            save_seen(*snap)
            _SV["fails"] = 0; _SV["saves"] += 1
            return True
        except Exception as e:
            with LOCK:
                _SV["dirty"] = True                   # retried at the next tick
            _SV["fails"] += 1
            log("state save failed", f"({why}, {_SV['fails']} in a row)", repr(e)[:400])
            if _SV["fails"] == 3:
                _alert("drain-state push failed 3 times in a row (filing continues; a re-run is idempotent)")
            return False


def _saver():
    try:
        while not _SV["stop"].wait(SAVE_EVERY_S):
            save_now()
    except BaseException as e:                        # never silent: the next work() sees it and restarts the saver
        _alert("state saver died: " + repr(e)[:120])


def saver_ensure():
    """start the saver on first use; restart it (at most 3 times) if it died. Called from work()."""
    t = _SV["thread"]
    if (t is not None and t.is_alive()) or _SV["stop"].is_set():   # stopped by the final save: no restart
        return
    if t is not None:
        if _SV["restarts"] >= 3:
            return
        _SV["restarts"] += 1
        _alert(f"state saver not running: restart {_SV['restarts']} of 3")
    _SV["thread"] = threading.Thread(target=_saver, name="drain-state-saver", daemon=True)
    _SV["thread"].start()


def saver_final(why="drain end"):
    if _SV["final"]:
        return
    _SV["final"] = True
    _SV["stop"].set()
    for k in range(3):
        if save_now(why):
            break
        time.sleep(2)
    log("state saver:", _SV["saves"], "saves,", why)


def _on_term(signum, frame):
    saver_final(f"signal {signum}")
    signal.signal(signum, signal.SIG_DFL)
    os.kill(os.getpid(), signum)


import atexit, signal
atexit.register(saver_final)
for _sig in (signal.SIGTERM, signal.SIGINT):
    try:
        signal.signal(_sig, _on_term)
    except ValueError:                                 # imported off the main thread (tests): atexit still saves
        pass


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


MATCH = os.environ.get("DRAIN_MATCH", "")


def pending():
    r = sh("git", "ls-remote", URL, f"refs/heads/{PREFIX}/*", timeout=60)
    out = []
    for l in r.stdout.splitlines():
        sha, ref = l.split()
        sid = ref[len(f"refs/heads/{PREFIX}/"):]
        if MATCH and not re.fullmatch(MATCH, sid):        # rehearsal: only the drill units (DRAIN_MATCH)
            continue
        if re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*", sid) and retry_due(SEEN.get((sid, sha))):
            out.append((sid, sha))
    def num(s):
        m = re.search(r"(\d+)$", s)
        return int(m.group(1)) if m else 0
    return sorted(out, key=lambda x: -num(x[0]))          # newest step first


T_ONE = {}

# w12 speed fix 2 (Lead 06:30): every unit fetched its ready commit alone under FETCH (0.5-2 s each), so with 28
# workers the fetches queued one behind the other. Now group commit: a unit queues its refspec; whoever finds no
# fetch running takes the whole queue and fetches it in ONE `git fetch` (at most FETCH_BATCH refs); the others wait
# for that result. A ref deleted between the listing and the fetch fails the whole batch in git, so on a failure the
# refs are listed again (one ls-remote) and the ones still there are fetched again: only the missing ref ends "gone".
FETCH_BATCH = int(os.environ.get("DRAIN_FETCH_BATCH", "50"))
_FQ = []                                  # waiting entries {"spec", "ref", "ok"}
_FQC = threading.Condition()
_FBUSY = [False]
FSTATS = {"fetches": 0, "refs": 0, "fallbacks": 0}


def _fetch_specs(specs):
    FSTATS["fetches"] += 1
    return sh("git", "-C", SRC, "fetch", "-q", "--depth", "1", URL, *specs, timeout=120 + 2 * len(specs)).returncode == 0


def _fetch_batch(batch, prefix):
    """True/False per entry: fetched, or the ref is gone (or unreadable: fail closed, the unit runs in a later drain)"""
    FSTATS["refs"] += len(batch)
    if _fetch_specs([m["spec"] for m in batch]):
        return [True] * len(batch)
    FSTATS["fallbacks"] += 1
    r = sh("git", "ls-remote", URL, f"refs/heads/{prefix}/*", timeout=60)
    if r.returncode:
        log("ready fetch: batch of", len(batch), "failed and the listing failed too: none fetched")
        return [False] * len(batch)
    live = {l.split()[1] for l in r.stdout.splitlines() if len(l.split()) == 2}
    keep = [m for m in batch if m["ref"] in live]
    log("ready fetch: batch of", len(batch), "failed;", len(batch) - len(keep), "ref(s) gone, fetching", len(keep), "again")
    ok = {}
    if keep and _fetch_specs([m["spec"] for m in keep]):
        ok = {id(m): True for m in keep}
    elif keep:                                           # still failing: one ref at a time (rare; bounded by the batch)
        ok = {id(m): _fetch_specs([m["spec"]]) for m in keep}
    return [ok.get(id(m), False) for m in batch]


atexit.register(lambda: FSTATS["refs"] and log("ready fetches:", FSTATS))


def fetch_ready(sid, prefix, lref):
    me = {"spec": f"+refs/heads/{prefix}/{sid}:{lref}", "ref": f"refs/heads/{prefix}/{sid}", "ok": None}
    with _FQC:
        _FQ.append(me)
        while me["ok"] is None and _FBUSY[0]:
            _FQC.wait()
        if me["ok"] is not None:
            return me["ok"]
        _FBUSY[0] = True                                  # leader: take the queue (my entry included)
        _FQ.remove(me)
        batch = [me] + _FQ[:FETCH_BATCH - 1]; del _FQ[:FETCH_BATCH - 1]
    res = [False] * len(batch)
    try:
        with FETCH:                                       # the shared checkout: still one fetch at a time
            res = _fetch_batch(batch, prefix)
    except Exception as e:
        log("ready fetch error", repr(e)[:120])
    finally:
        with _FQC:
            for m, o in zip(batch, res):
                m["ok"] = o
            _FBUSY[0] = False
            _FQC.notify_all()
    return me["ok"]


# w12 speed fix 3 (Lead 06:30): every unit cloned upstream main and checked out the sparse tree (about 13 MB, 1-6 s,
# 28 at once on the runner). Now ONE shared checkout per drain (W/upstream-base) at the live main sha: one
# `ls-remote main` shared by all workers for MAIN_CHECK_S; when main moved, or the base is older than BASE_MAX_S, it is
# cloned again under BASE_LOCK before any unit copies it (workers wait, nobody copies a base behind live main). Each
# unit gets its own copy (cp -a) and adds its Outside imports to the copy's sparse set. Fail closed: main unreadable,
# or the base cannot be brought to the live sha = no tree, the unit is "error" (retried by the drain).
# Guards: submit.py's checks (cat-file -e HEAD:<file>, the commit's parent, checkcore.sh) read the copy, i.e. main as
# of at most MAIN_CHECK_S before the copy, the same as a fresh clone was (its clone ran 1-6 s before the copy point).
BASE_MAX_S = float(os.environ.get("DRAIN_BASE_MAX_S", "60"))
MAIN_CHECK_S = float(os.environ.get("DRAIN_MAIN_CHECK_S", "5"))
SPARSE = ["/.github/", "/STOP", "/CONTRIBUTING.md", "/lean/PEqualNP/", "!/lean/PEqualNP/Outside/"]
BASE_LOCK = threading.Lock(); _MAIN_LOCK = threading.Lock()
_BASE = {"dir": None, "t": 0.0, "sha": None, "main_t": 0.0, "main": None, "clones": 0, "copies": 0}


def _clone_upstream(tree, outs=()):
    for att in range(3):
        ok = (sh("git", "clone", "-q", "--depth", "1", "--filter=blob:none", "--no-checkout", "--single-branch",
                 "--branch", "main", UPSTREAM, tree, timeout=180).returncode == 0
              and sh("git", "-C", tree, "sparse-checkout", "set", "--no-cone", *SPARSE,
                     *[f"/lean/{o}.lean" for o in outs]).returncode == 0
              and sh("git", "-C", tree, "checkout", "-q", "main", timeout=180).returncode == 0)
        if ok:
            return True
        sh("rm", "-rf", tree); time.sleep(5 * (att + 1))
    return False


def main_sha():
    """the live upstream main sha, read at most every MAIN_CHECK_S for all workers; None when unreadable"""
    with _MAIN_LOCK:
        if _BASE["main"] and time.time() - _BASE["main_t"] < MAIN_CHECK_S:
            return _BASE["main"]
        t = time.time()
        r = sh("git", "ls-remote", UPSTREAM, "refs/heads/main", timeout=60)
        o = r.stdout.split() if r.returncode == 0 else []
        _BASE["main"], _BASE["main_t"] = (o[0], t) if o else (None, 0.0)
        return _BASE["main"]


def upstream_tree(tree, outs):
    """copy of the shared checkout at the live main into `tree`; '' when done, else why not (fail closed)"""
    live = main_sha()
    if not live:
        return "upstream main unreadable (no tree, fail closed)"
    with BASE_LOCK:
        b = _BASE["dir"]
        if b is None or _BASE["sha"] != live or time.time() - _BASE["t"] > BASE_MAX_S:
            nb = os.path.join(W, "upstream-base-%d" % (_BASE["clones"] + 1))
            t = time.time()
            if not _clone_upstream(nb):
                return "upstream checkout failed (shared base)"
            got = sh("git", "-C", nb, "rev-parse", "HEAD").stdout.strip()
            if got != live:                               # main moved during the clone: accept only the live sha
                with _MAIN_LOCK:
                    _BASE["main_t"] = 0.0
                live = main_sha()
                if got != live:
                    log("upstream base", got[:12], "is not live main", (live or "?")[:12], "(no tree, fail closed)")
                    sh("rm", "-rf", nb)
                    return "upstream base behind live main"
            _BASE.update(dir=nb, t=t, sha=got, clones=_BASE["clones"] + 1)
            if b:
                sh("rm", "-rf", b)                        # no copy is made from the old one any more
            b = nb
        r = sh("cp", "-a", b, tree, timeout=120)
        _BASE["copies"] += 1
    if r.returncode:
        return "copy of the upstream base failed"
    if outs and sh("git", "-C", tree, "sparse-checkout", "add", *[f"/lean/{o}.lean" for o in outs], timeout=180).returncode:
        return "sparse-checkout add of the Outside imports failed"
    return ""


atexit.register(lambda: _BASE["copies"] and log("upstream base:", _BASE["clones"], "clones for", _BASE["copies"], "units"))


def one(sid, sha, prefix=None, extra=None):
    prefix = prefix or PREFIX
    T_ONE[sid] = time.time()
    d = tempfile.mkdtemp(prefix=sid + "-", dir=W)
    lref = f"refs/drain/{sid}"
    if not fetch_ready(sid, prefix, lref):                # w12 fix 2: one batched fetch for every waiting unit
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
    ready_t = sh("git", "-C", SRC, "log", "-1", "--format=%ct", lref).stdout.strip()   # Lead 07:31: ready push time
    outs = [re.sub(r"\.", "/", m) for m in re.findall(r"(?m)^import (PEqualNP\.Outside\.[A-Za-z0-9_.]+)", open(proof).read())]
    tree = os.path.join(d, "tree")
    why = upstream_tree(tree, outs)                       # w12 fix 3: a copy of the shared checkout at live main
    if why:
        return "error", why
    if not os.path.isdir(os.path.join(tree, ".github", "scripts")):
        return "error", "upstream checkout failed"
    os.makedirs(os.path.join(tree, "lean", "PEqualNP", "Outside"), exist_ok=True)
    outp = os.path.join(d, "out")
    env = dict(os.environ, ID=sid, MOD=mod, PROOF=proof, TREE=tree, W=d, DRY=CHILD_DRY, GITHUB_REF_NAME=f"{prefix}/{sid}",
               GITHUB_OUTPUT=outp, PR_GATE_DIR=W, PR_GATE_N=str(PR_SLOTS), READY_MSG=msg, RIVAL_SNAP_DIR=W,
               READY_T=ready_t if ready_t.isdigit() else "")
    env.update(extra or {})
    if DRY:
        return "dry", f"would run submit.py for {sid} {mod} ({os.path.getsize(proof)} bytes, sha {got[:8]})"
    t_sub = time.time()
    r = sh(sys.executable, "-I", os.path.join(SRC, ".github", "cloud-pr", "submit.py"), env=env, timeout=900)
    # Lead 19:14: the per-stage seconds of every unit in the drain log (prep = fetch of the ready commit + upstream
    # checkout before submit.py starts)
    for l in (r.stdout or "").splitlines():
        if " TIMES " in l or " gate: " in l or " SKIP " in l or " halted: " in l or "WOULD-CREATE " in l or "SIGHT-TO-CREATE " in l or "COMMIT-STAGES" in l:
            log(sid, l.strip()[:900], f"prep={t_sub - T_ONE.get(sid, t_sub):.1f}" if " TIMES " in l else "")
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
        if res not in ("paused", "halted", "site-closed", "stall-giveup") and not (res == "unleased" and "desk off or paused" in why):
            if res in RETRYABLE:                           # W6: retried up to RETRY_MAX times (submit.py is idempotent:
                n = attempts(SEEN.get((sid, sha)))[1] + 1  # create-only head, our PR found, lease recovered)
                SEEN[(sid, sha)] = (f"{res}#{n}", time.time())
                if n >= RETRY_MAX:
                    log("GIVE-UP", sid, f"{res} {n} times:", why[:120])
            else:
                SEEN[(sid, sha)] = (res, time.time())      # paused ones run again after the pause
        STATS[res] = STATS.get(res, 0) + 1
        _SV["dirty"] = True                            # w12 fix 1: the saver thread pushes it (no push under LOCK)
    saver_ensure()
    log("DONE", sid, res, f"{time.time() - t:.0f}s", why)
    return sid


_PZ = [0.0, 0.0]          # (checked at, paused until)
_FH = [0.0, False, ""]    # Lead 05:10: (checked at, halted, why) of the toolkit filing/stop vs filing/go refs


def halted():
    """rule 16.1 (haltrule.verdict): newest filing/stop/<n> >= newest filing/go/<n> = halted (a tie too), a stop name
    that is not plain digits = halted, a go name that is not plain digits is ignored, unreadable = halted. Read at
    most every 10 s here (new branches only); every PR create re-checks within 2 s (submit.py filing_halted)."""
    if time.time() - _FH[0] > 10:
        for k in range(3):                    # live test 05:13: the toolkit needs auth; 3 tries 2 s apart
            r = sh("git", *auth(), "ls-remote", "https://github.com/Leg0shii/pnp-toolkit.git", "refs/heads/filing/*", timeout=60)
            if r.returncode == 0:
                break
            time.sleep(2)
        h, why = haltrule.verdict(r.stdout, r.returncode)
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
    try:                                   # 16.13: the run token's core limit, once per drain (docs: 1,000/h for GITHUB_TOKEN)
        rl = sh("gh", "api", "rate_limit", "--jq", '.resources.core | "\\(.limit) \\(.remaining)"', timeout=30,
                env=dict(os.environ, GH_TOKEN=os.environ.get("READ_TOKEN", "")))
        log("RUN-TOKEN rate_limit core limit/remaining:", rl.stdout.strip() or ("rc %d" % rl.returncode))
    except Exception as e:
        log("RUN-TOKEN rate_limit unreadable:", repr(e)[:80])
    inflight = {}; idle = None
    rf = refresher_start()
    warm = float(os.environ.get("DRAIN_WARM_S", "0") or 0)
    if rf and warm > 0:                    # Lead 08:12 (b): units are released only after the refresher's first copies
        t_w = time.time()                  # exist (or WARM_S passed), so the cold first build is not on any unit's path
        while time.time() - t_w < warm and not all(os.path.exists(os.path.join(W, x)) for x in ("rival_snap.json", "halt.json")):
            time.sleep(0.5)
        log(f"WARM {time.time() - t_w:.1f} s: refresher copies", "ready" if all(os.path.exists(os.path.join(W, x))
            for x in ("rival_snap.json", "halt.json")) else "NOT ready (released anyway)", "- units released now")
        if PREFIX == "loadtest" and os.environ.get("DRILL_GAPS_REF"):   # rehearsal marker for the builder: toolkit ref
            # drill/warm-<epoch>, only in -drill runs (W8 08:36: a lane canary with warm must not look like a rehearsal)
            ok = alert_ref(f"WARM drain run {os.environ.get('GITHUB_RUN_ID', '?')} released units at {time.time():.0f}",
                           "warm", prefix="drill")
            log("WARM marker ref drill/warm-*", "pushed" if ok else "push FAILED")
    try:
        _loop(inflight, idle)
    finally:
        refresher_stop(rf)
    try:                                   # 16.12: live newest-page read duration of this drain
        ds = sorted(float(l.split()[1]) for l in open(os.path.join(W, "snapd.log")) if len(l.split()) == 2)
        if ds:
            log(f"SNAP-READ newest-page read over {len(ds)} builds: p50 {ds[len(ds) // 2]:.2f} s, "
                f"p95 {ds[min(len(ds) - 1, int(.95 * len(ds)))]:.2f} s, max {ds[-1]:.2f} s")
    except OSError:
        pass
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


TK = "https://github.com/Leg0shii/pnp-toolkit.git"
STALL_S = float(os.environ.get("PR_STALL_S", "60"))
ALERTED = {}             # kind -> epoch of the last alert (at most one per kind per 5 min)
LAST_DONE = [0.0]


def stall_alerts(now, n_inflight, last_done, t_start, stall_until):
    """RC-b 6 (Lead 06:22): PR-STALL by name within 60 s. (kind, message) list for this drain loop tick:
    prstall-bucket   GitHub refused a create (403/429): every worker stops creating until stall_until
    prstall-noprogress  units in flight and none finished for STALL_S seconds (the drain is stuck)"""
    out = []
    if stall_until > now:
        out.append(("prstall-bucket", f"PR-STALL bucket: GitHub refused a create, no PR for {stall_until - now:.0f} s"))
    if n_inflight and now - max(last_done, t_start) > STALL_S:
        out.append(("prstall-noprogress", f"PR-STALL no unit finished for {now - max(last_done, t_start):.0f} s, {n_inflight} in flight"))
    return [(k, m) for k, m in out if now - ALERTED.get(k, 0) >= 300]


def alert_ref(msg, kind, prefix="alert"):
    """toolkit ref alert/<kind>-<epoch> (an empty commit whose message is the alert), the same channel as the closer's
    TAKEN-STALE; the Lead's audit and the infra box read alert/*"""
    g = os.path.join(W, "alert.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    tree = subprocess.run(["git", "-C", g, "mktree"], input="", capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME="drain", GIT_AUTHOR_EMAIL="drain@localhost",
               GIT_COMMITTER_NAME="drain", GIT_COMMITTER_EMAIL="drain@localhost")
    c = subprocess.run(["git", "-C", g, "commit-tree", tree, "-m", msg], capture_output=True, text=True, env=env).stdout.strip()
    return bool(c) and sh("git", *auth(), "-C", g, "push", "-q", TK, f"{c}:refs/heads/{prefix}/{kind}-{int(time.time())}",
                          timeout=60).returncode == 0


def stall_tick(n_inflight):
    try:                                   # 16.12: a newest-page read over 6 s (thrown away by submit.py)
        sl = open(os.path.join(W, "snapslow")).read().split()
        if time.time() - ALERTED.get("snapslow", 0) >= 300 and time.time() - float(sl[0]) < 300:
            ALERTED["snapslow"] = time.time()
            m = f"SNAP-SLOW newest-page read took {sl[1]} s (over 6 s): thrown away, no PR on it"
            ok = DRY or alert_ref(m, "snapslow")
            log(m, "(alert ref pushed)" if ok else "(alert ref push FAILED)")
    except (OSError, ValueError, IndexError):
        pass
    try:
        su = float(open(os.path.join(W, "stall")).read())
    except (OSError, ValueError):
        su = 0.0
    try:                                   # 16.14: the refresher's heartbeat went stale, workers read inline
        rd = open(os.path.join(W, "refdead")).read().split()
        if time.time() - ALERTED.get("refdead", 0) >= 300 and time.time() - float(rd[0]) < 300:
            ALERTED["refdead"] = time.time()
            m = "REFRESHER-DEAD " + " ".join(rd[1:])[:120] + ": workers read inline (one reader per check)"
            ok = DRY or alert_ref(m, "refdead")
            log(m, "(alert ref pushed)" if ok else "(alert ref push FAILED)")
    except (OSError, ValueError, IndexError):
        pass
    try:                                   # 16.13: four create refusals ended this drain's creates
        gv = open(os.path.join(W, "giveup")).read().strip()
        if not ALERTED.get("prstall-giveup"):
            ALERTED["prstall-giveup"] = time.time()
            m = f"PR-STALL-GIVEUP four create refusals in this drain: no more creates, units stay unseen ({gv[:120]})"
            ok = DRY or alert_ref(m, "prstall-giveup")
            log(m, "(alert ref pushed)" if ok else "(alert ref push FAILED)")
    except OSError:
        pass
    for kind, msg in stall_alerts(time.time(), n_inflight, LAST_DONE[0], T0, su):
        ALERTED[kind] = time.time()
        ok = DRY or alert_ref(msg, kind)
        log(msg.split(":")[0] if kind == "prstall-bucket" else "PR-STALL", msg, "(alert ref pushed)" if ok else "(alert ref push FAILED)")


# HARDENING 16.11 (Lead 07:03): the site's own status (pequalnp.com/status.json), fetched by the PC gate once a minute
# and published on toolkit ref status/site (status.json as received, fetched.json {"epoch", "http"}). We never contact
# the site. Read here at most every SITE_EVERY_S, shared by all workers through W/site.json (submit.py checks it before
# every create). Any submissions.<cause>.accepting false in a copy at most SITE_MAX_AGE_S old = hold (no new unit,
# result "site-closed", not marked seen, retried when it reopens). A stale, unparseable or http-failed copy is IGNORED
# (filing goes on) with one SITE-STATUS-STALE alert per 5 min; no ref at all = dark (nothing, no alert).
SITE_REF = "refs/heads/status/site"
SITE_EVERY_S = float(os.environ.get("SITE_EVERY_S", "30"))
SITE_MAX_AGE_S = float(os.environ.get("SITE_MAX_AGE_S", "180"))
_SITE = {"t": 0.0, "closed": False, "why": ""}


def site_verdict(status_txt, fetched_txt, now):
    """(closed, why, alert) from the two files of status/site; None texts = no ref (dark). Pure."""
    if status_txt is None and fetched_txt is None:
        return False, "no status/site ref (dark)", None
    try:
        f = json.loads(fetched_txt or "")
        ep = float(f["epoch"])
        code = int(f.get("http", f.get("http_code", f.get("code", 0))))
    except (ValueError, KeyError, TypeError):
        return False, "fetched.json unreadable", "SITE-STATUS-STALE fetched.json unreadable: filing as usual"
    if not 0 <= now - ep <= SITE_MAX_AGE_S:
        return False, f"copy {now - ep:.0f} s old", f"SITE-STATUS-STALE copy {now - ep:.0f} s old (over {SITE_MAX_AGE_S:.0f} s): filing as usual"
    if code != 200:
        return False, f"site answered http {code}", f"SITE-STATUS-STALE last fetch http {code}: filing as usual"
    try:
        st = json.loads(status_txt or "")
        subs = st["submissions"]
        if not isinstance(subs, dict):
            raise TypeError("submissions is not an object")
        closed = sorted(k for k, v in subs.items() if isinstance(v, dict) and v.get("accepting") is False)
    except (ValueError, KeyError, TypeError) as e:
        return False, "status.json unparseable", f"SITE-STATUS-STALE status.json unparseable ({str(e)[:60]}): filing as usual"
    if closed:
        ra = max([int(subs[k].get("retry_after_s") or 0) for k in closed if str(subs[k].get("retry_after_s") or 0).isdigit()] or [0])
        return True, f"site not accepting {','.join(closed)[:80]} (retry_after_s {ra})", None
    return False, "site accepting", None


def _site_read():
    """(status.json text, fetched.json text), (None, None) when the ref does not exist; raises on a failed fetch"""
    g = os.path.join(W, "site.git")
    if not os.path.isdir(g):
        sh("git", "init", "-q", "--bare", g)
    ls = sh("git", *auth(), "ls-remote", TK, SITE_REF, timeout=60)
    if ls.returncode:
        raise RuntimeError("ls-remote status/site failed")
    if not ls.stdout.strip():
        return None, None
    if sh("git", *auth(), "-C", g, "fetch", "-q", "--depth=1", TK, f"+{SITE_REF}:{SITE_REF}", timeout=60).returncode:
        raise RuntimeError("fetch status/site failed")
    show = lambda n: (lambda r: r.stdout if r.returncode == 0 else "")(sh("git", "-C", g, "show", f"{SITE_REF}:{n}"))
    return show("status.json"), show("fetched.json")


def site_closed():
    if time.time() - _SITE["t"] >= SITE_EVERY_S:
        try:
            stx, ftx = _site_read()
            closed, why, alert = site_verdict(stx, ftx, time.time())
        except Exception as e:
            closed, why, alert = False, "status/site unreadable", f"SITE-STATUS-STALE status/site unreadable ({str(e)[:60]}): filing as usual"
        _SITE.update(t=time.time(), closed=closed, why=why)
        try:
            with open(os.path.join(W, "site.json.tmp"), "w") as o:
                json.dump({"t": time.time(), "closed": closed, "why": why}, o)
            os.replace(os.path.join(W, "site.json.tmp"), os.path.join(W, "site.json"))
        except OSError:
            pass
        if alert and time.time() - ALERTED.get("sitestale", 0) >= 300:
            ALERTED["sitestale"] = time.time()
            ok = DRY or alert_ref(alert, "sitestale")
            log(alert, "(alert ref pushed)" if ok else "(alert ref push FAILED)")
    return _SITE["closed"]


_CW = [0.0]


def creates_tick(now=None):
    """Lead 07:27: accepted creates per 10 s window (W/accepted.log, written by submit.py on every 201), so the first
    live minute shows the real create rate. One line per finished window that had a create; returns it."""
    now = time.time() if now is None else now
    ws = (now // 10) * 10 - 10
    if ws <= _CW[0]:
        return None
    _CW[0] = ws
    try:
        ts = [float(x) for x in open(os.path.join(W, "accepted.log")).read().split()]
    except (OSError, ValueError):
        return None
    n = sum(1 for t in ts if ws <= t < ws + 10)
    if not n:
        return None
    try:
        k = int(open(os.path.join(W, "refusals")).read().strip() or 0)
    except (OSError, ValueError):
        k = 0
    cap = max(10, int(os.environ.get("PR_PER_MIN", "70")) >> k) if k else int(os.environ.get("PR_PER_MIN", "70"))
    m = (f"CREATES-10S {time.strftime('%H:%M:%S', time.gmtime(ws))} accepted {n} ({n * 6}/min), "
         f"last 60 s {sum(1 for t in ts if ws - 50 <= t < ws + 10)}, drain total {len(ts)}, cap {cap}/min, refusals {k}")
    log(m)
    return m


def _loop(inflight, idle):
    with ThreadPoolExecutor(WORKERS) as ex:
        while time.time() - T0 < MAX_S:
            for k in [k for k, fu in inflight.items() if fu.done()]:
                inflight.pop(k)
                LAST_DONE[0] = time.time()
            stall_tick(len(inflight))
            creates_tick()
            if os.path.exists(os.path.join(W, "giveup")):     # 16.13: no new unit; in-flight ones end unseen
                todo = []
                if not inflight:
                    log("PR-STALL-GIVEUP: drain ends, remaining units stay for the next drain or the PC")
                    break
            elif halted():
                log("halted: no new branch, in-flight ones stop before their PR,", _FH[2]); todo = []
                if not inflight:
                    break
            elif paused():
                log("shared desk pause started: no new branch, in-flight ones finish"); todo = []
                if not inflight:
                    break
            elif site_closed():                 # 16.11: hold, never end the drain on it (it reopens)
                if not _SITE.get("logged"):
                    log("site-closed: no new branch,", _SITE["why"]); _SITE["logged"] = True
                todo = []
            else:
                _SITE["logged"] = False
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
            time.sleep(1 if inflight else float(os.environ.get("DRAIN_IDLE_POLL_S", "3")))


if __name__ == "__main__":
    main()
