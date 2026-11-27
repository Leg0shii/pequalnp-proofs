#!/usr/bin/env python3
"""mintcross (HARDENING section 14, W7; BLINDSPOTS B5 + B16): the COMBINED case. The cloud opener (submit.py main()),
the PC watcher (watch.py submit()) and the late-lease feeder (feed.py) run their REAL code against ONE fake world:

  toolkit, upstream and fork are local bare git repos (git url.insteadOf, GIT_ALLOW_PROTOCOL=file): refs such as
  filing/stop, deskgate/open, claim/<gid>, gatereq/<gid>, status/taken are real refs with real create-only pushes;
  an update hook logs every ref push. GitHub is a fake `gh` (one shared PR list; GitHub's rule "one open PR per head
  branch" included), the data host is a fake `curl` (mirror gaps.json, STOP = 404), the comms bus is a fake bus.py.
  HTTP(S)_PROXY points at a closed port: nothing leaves the box. Any call the fakes do not know is UNEXPECTED.

Desk requests = gatereq/* ref pushes (deskgate's ref door) + bus desk-req publishes + any desk-host curl.

Cases (each must hold for ALL THREE components):
  H1 halt     newest toolkit filing/stop newer than filing/go: 0 PRs, 0 desk requests, 0 claim locks (I4, I7, V7, V14)
  H2 paused   our handle on the mirror pause list: 0 desk requests (I7, V8)
  H3 halt-mid filing/stop pushed while the feeder runs: no claim after the stop (V7, Y9)
  H4 16.1     rule 16.1 shapes (tie = halted, non-digit stop name = halted; filing/* and deskgate/*): 0 desk requests
  O1 one-pr   cloud opener and PC watcher both file unit U: exactly one PR of ours on U (B5, V6)
  O2 grace    the drain holds U (drain-state inflight, fresh drain-beat, claim/U taken, no PR yet) and the PC's ready/
              intake is past READY_GRACE: the PC files nothing on U (Y8, V6; W11's rule)
  B1 lostrep  the gate takes the claim but its answer is lost (bus desk-rep dropped / no lease ref): no PR without
              a Lease line on a unit the gate granted us (B16, Y11)
Every case prints its GitHub calls, desk requests and data-host reads (I12).

  python3 mintcross.py [CLOUD_CHECKOUT]
     env MINTCROSS_PC   dir with the PC watcher sources (watch.py + deskguard.py, or the red team copies
                        watch_watch.py + watch_deskguard.py); default /mnt/project-files/team/redteam/src
     env MINTCROSS_FEED feed.py path; default /mnt/project-files/team/infra/gateway/feed.py
     env MINTCROSS_ONLY comma list of cases
  -> one line per case and component, then "MINTCROSS PASS <sha>" (exit 0) or "MINTCROSS FAIL <sha>: <cases>" (exit 1)
"""
import json, os, re, shutil, stat, subprocess, sys, tempfile, textwrap, time

HERE = os.path.dirname(os.path.abspath(__file__))
HANDLE = "Leg0shii"
TK_URL = "https://github.com/Leg0shii/pnp-toolkit"
UP_URL = "https://github.com/open-goat/pequalnp-proofs"
FORK_URL = "https://github.com/Leg0shii/pequalnp-proofs-fork"
PC_DEF = "/mnt/project-files/team/redteam/src"
FEED_DEF = "/mnt/project-files/team/infra/gateway/feed.py"
GID = "L-meta-900001"
STMT = "S(L-meta-900001)"


def sh(*a, cwd=None, env=None, inp=None, check=True):
    r = subprocess.run(a, cwd=cwd, env=env, input=inp, capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError(" ".join(a) + ": " + r.stderr[-300:])
    return r


# ---------------------------------------------------------------------------------------------------------------
# fake executables (written into WORLD/bin, first on PATH of every child)
# ---------------------------------------------------------------------------------------------------------------
FAKE_GH = r'''#!/usr/bin/env python3
import fcntl, json, os, re, sys, time
W = os.environ["MX_WORLD"]; a = sys.argv[1:]
lk = open(os.path.join(W, "gh.lock"), "a"); fcntl.flock(lk, fcntl.LOCK_EX)
st = json.load(open(os.path.join(W, "github.json")))
def save(): json.dump(st, open(os.path.join(W, "github.json"), "w"))
def logc(kind): open(os.path.join(W, "calls.log"), "a").write(f"{time.time():.3f}\tgh\t{os.environ.get('MX_WHO','?')}\t{kind}\t{' '.join(a)[:300]}\n")
def opt(k, d=None): return a[a.index(k) + 1] if k in a else d
def emit(obj):
    jq = opt("--jq")
    if jq is None: print(json.dumps(obj)); return
    if jq == ".[].html_url": print("".join(p["html_url"] + "\n" for p in obj), end=""); return
    if jq in (".[].number", ".[] | .number"): print("".join(f"{p['number']}\n" for p in obj), end=""); return
    if jq == "length": print(len(obj)); return
    if jq.startswith(".items[]") and isinstance(obj, dict) and not obj.get("items"): return
    logc("UNEXPECTED-jq"); print(json.dumps(obj))
def pulls(state): return [p for p in st["pulls"] if (p["state"] == "open") == (state == "open")] if state != "all" else st["pulls"]
if a[:2] == ["pr", "create"]:
    head = opt("--head"); body = opt("--body", ""); title = opt("--title", "")
    h = head.split(":", 1)[-1]
    old = [p for p in st["pulls"] if p["state"] == "open" and p["user"]["login"] == head.split(":")[0] and p["head"]["ref"] == h]
    if old:                                  # GitHub: one open PR per head branch
        logc("pr-create-exists"); sys.stderr.write(f"a pull request for branch \"{head}\" into branch \"main\" already exists:\n{old[0]['html_url']}\n"); sys.exit(1)
    n = st["next"]; st["next"] += 1
    p = {"number": n, "state": "open", "title": title, "body": body, "user": {"login": head.split(":")[0]}, "head": {"ref": h},
         "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "merged_at": None, "closed_at": None,
         "html_url": f"https://github.com/open-goat/pequalnp-proofs/pull/{n}", "by": os.environ.get("MX_WHO", "?"),
         "files": [f"lean/PEqualNP/Outside/{h.replace('-', '_')}.lean"]}
    st["pulls"].append(p); save(); logc("pr-create"); print(p["html_url"]); sys.exit(0)
if a[:2] == ["pr", "edit"]:
    n = int(re.findall(r"(\d+)$", a[2])[0]); body = opt("--body")
    for p in st["pulls"]:
        if p["number"] == n and body is not None: p["body"] = body
    save(); logc("pr-edit"); sys.exit(0)
if a[:2] == ["pr", "list"]:
    q = opt("--search", ""); res = []
    for p in st["pulls"]:
        if q in p["title"] or any(q in f for f in p["files"]) or q.replace("-", "_") in " ".join(p["files"]):
            res.append({"number": p["number"], "state": p["state"].upper(), "title": p["title"], "author": p["user"],
                        "files": [{"path": f} for f in p["files"]], "headRefName": p["head"]["ref"], "url": p["html_url"],
                        "createdAt": p["created_at"]})
    logc("pr-list"); emit(res); sys.exit(0)
if a[:2] == ["pr", "view"]:
    n = int(re.findall(r"(\d+)$", a[2])[0]); p = next((x for x in st["pulls"] if x["number"] == n), None)
    logc("pr-view")
    if p is None: sys.stderr.write("no pull requests found\n"); sys.exit(1)
    emit({"number": n, "state": p["state"].upper(), "author": p["user"], "title": p["title"], "body": p["body"],
          "files": [{"path": f, "additions": 10} for f in p["files"]], "comments": [], "headRefName": p["head"]["ref"]}); sys.exit(0)
if a and a[0] == "api":
    path = next((x for x in a[1:] if not x.startswith("-") and "/" in x), "")
    fields = {}
    for i, x in enumerate(a):
        if x in ("-f", "-F") and i + 1 < len(a) and "=" in a[i + 1]: k, v = a[i + 1].split("=", 1); fields[k] = v
    q = dict(x.split("=", 1) for x in path.split("?", 1)[1].split("&")) if "?" in path else {}
    q.update(fields)
    m = re.search(r"/pulls/(\d+)/files", path)
    if m:
        p = next((x for x in st["pulls"] if x["number"] == int(m.group(1))), {"files": []}); logc("api-files")
        emit([{"filename": f, "additions": 10} for f in p["files"]]); sys.exit(0)
    m = re.search(r"/issues/(\d+)/comments", path)
    if m: logc("api-comments"); emit([]); sys.exit(0)
    m = re.search(r"/pulls/(\d+)$", path.split("?")[0])
    if m:
        p = next((x for x in st["pulls"] if x["number"] == int(m.group(1))), None); logc("api-pull")
        if p is None: sys.stderr.write("HTTP 404\n"); sys.exit(1)
        emit(p); sys.exit(0)
    if re.search(r"repos/[^/]+/[^/]+/pulls$", path.split("?")[0]):
        res = pulls(q.get("state", "open"))
        if "head" in q:
            o, h = q["head"].split(":", 1); res = [p for p in res if p["user"]["login"] == o and p["head"]["ref"] == h]
        res = sorted(res, key=lambda p: -p["number"]); pp, pg = int(q.get("per_page", 30)), int(q.get("page", 1))
        logc("api-pulls"); emit(res[(pg - 1) * pp:pg * pp]); sys.exit(0)
    if "search/issues" in path:
        logc("api-search"); emit({"total_count": 0, "items": []}); sys.exit(0)
    if path.startswith("rate_limit"):
        logc("api-rate"); emit({"resources": {"core": {"remaining": 5000, "reset": int(time.time()) + 3600}}}); sys.exit(0)
logc("UNEXPECTED"); sys.stderr.write("mintcross fake gh: unexpected call\n"); sys.exit(1)
'''

FAKE_CURL = r'''#!/usr/bin/env python3
import json, os, re, sys, time
W = os.environ["MX_WORLD"]; a = sys.argv[1:]
url = next((x for x in a if x.startswith("http")), "")
host = re.sub(r"^https?://([^/:]+).*", r"\1", url)
def logc(kind): open(os.path.join(W, "calls.log"), "a").write(f"{time.time():.3f}\tcurl\t{os.environ.get('MX_WHO','?')}\t{kind}\t{url[:200]}\n")
out = a[a.index("-o") + 1] if "-o" in a else None
wfmt = a[a.index("-w") + 1] if "-w" in a else None
def reply(body, code=200):
    if out and out != "/dev/null": open(out, "w").write(body)
    elif not out: sys.stdout.write(body)
    if wfmt: sys.stdout.write(wfmt.replace("%{http_code}", str(code)))
    sys.exit(0 if code < 400 or not ("-f" in a or "-sSf" in a or "-fsS" in a) else 22)
if host == "data.pequalnp.com" and "gaps.json" in url:
    logc("data-gaps"); reply(open(os.path.join(W, "gaps.json")).read())
if host == "data.pequalnp.com":
    logc("data-other"); reply("{}", 404)
if host.endswith("pequalnp.com"):
    logc("DESK"); reply('{"error":"mintcross: desk host"}', 403)
if host == "raw.githubusercontent.com" and url.endswith("/STOP"):
    logc("stop"); reply("", 404)
if host == "api.github.com":
    logc("UNEXPECTED-api"); reply("[]", 200)
logc("UNEXPECTED"); sys.stderr.write("mintcross fake curl: unexpected url\n"); sys.exit(7)
'''

FAKE_BUS = r'''"""mintcross fake comms bus (watch.py imports bus from TK/watch)."""
import json, os, time
W = os.environ["MX_WORLD"]
def _log(kind, ch, msg): open(os.path.join(W, "bus.log"), "a").write(f"{time.time():.3f}\t{os.environ.get('MX_WHO','?')}\t{kind}\t{ch}\t{msg}\n")
def pub(ch, msg, *a, **k):
    _log("pub", ch, msg)
    if ch == "desk-req":
        p = str(msg).split()
        if len(p) >= 2 and p[0] == "claim" and os.path.exists(os.path.join(W, "grant_lost")):
            open(os.path.join(W, "granted.txt"), "a").write(p[1] + " bus\n")   # the gate took it; desk-rep is lost
    return True
class _Empty:
    def __init__(self, t): self.t = time.time() + min(float(t or 3), 3)
    def __iter__(self): return self
    def __next__(self):
        if time.time() > self.t: raise StopIteration
        time.sleep(0.2); return b": keepalive\n"
def _req(path, stream=False, timeout=None, **k):
    _log("req", path, "")
    if path.startswith("/subscribe/"): return _Empty(timeout)
    return {}
def __getattr__(name):
    def f(*a, **k): _log("call", name, json.dumps([str(x)[:80] for x in a])); return None
    return f
'''

HOOK = r'''#!/bin/sh
# mintcross: log every ref update of this bare repo (ref, new sha); gatereq/* = a desk request at deskgate's door
echo "$(date +%s.%N) $1 $3 ${MX_WHO:-?}" >> "$MX_WORLD/refs.log"
case "$1" in refs/heads/gatereq/*) [ -f "$MX_WORLD/grant_lost" ] && [ "$3" != 0000000000000000000000000000000000000000 ] && echo "${1#refs/heads/gatereq/} ref" >> "$MX_WORLD/granted.txt" ;; esac
exit 0
'''


# ---------------------------------------------------------------------------------------------------------------
# world
# ---------------------------------------------------------------------------------------------------------------
class World:
    def __init__(self, case, cfg):
        self.d = tempfile.mkdtemp(prefix="mintcross-%s-" % case)
        self.cfg = cfg
        d = self.d
        os.makedirs(os.path.join(d, "bin"))
        for n, src in (("gh", FAKE_GH), ("curl", FAKE_CURL)):
            p = os.path.join(d, "bin", n); open(p, "w").write(src); os.chmod(p, 0o755)
        self.gitcfg = os.path.join(d, "gitconfig")
        self.tk, self.up, self.fork = (os.path.join(d, x + ".git") for x in ("tk", "up", "fork"))
        rules = []
        for url, path in ((TK_URL, self.tk), (UP_URL, self.up), (FORK_URL, self.fork)):
            rules += [f'[url "{path}"]', f"\tinsteadOf = {url}.git", f"\tinsteadOf = {url}"]
        open(self.gitcfg, "w").write("\n".join(rules + ["[user]", "\tname = mintcross", "\temail = mx@localhost",
                                                        "[init]", "\tdefaultBranch = main", "[protocol]", "\tallow = always"]) + "\n")
        env = self.env("setup")
        for g in (self.tk, self.up, self.fork):
            sh("git", "init", "-q", "--bare", g, env=env)
            hp = os.path.join(g, "hooks", "update"); open(hp, "w").write(HOOK); os.chmod(hp, 0o755)
        # upstream main: one commit with the Outside dir (a file of another unit) and STOP absent
        seed = os.path.join(d, "seed"); sh("git", "init", "-q", seed, env=env)
        os.makedirs(os.path.join(seed, "lean/PEqualNP/Outside"))
        open(os.path.join(seed, "lean/PEqualNP/Outside/L_meta_1.lean"), "w").write("-- other unit\n")
        open(os.path.join(seed, "README.md"), "w").write("fake upstream\n")
        sh("git", "-C", seed, "add", "-A", env=env); sh("git", "-C", seed, "commit", "-q", "-m", "base", env=env)
        sh("git", "-C", seed, "push", "-q", self.up, "HEAD:refs/heads/main", env=env)
        sh("git", "-C", seed, "push", "-q", self.fork, "HEAD:refs/heads/main", env=env)
        self.seed = seed
        # proof file of unit GID
        self.proof = os.path.join(d, GID.replace("-", "_") + ".lean")
        open(self.proof, "w").write("import PEqualNP.Defs\n\ntheorem PEqualNP.Outside.%s : True := trivial\n" % GID.replace("-", "_"))
        now = int(time.time())
        self.now = now
        # GitHub, mirror, toolkit refs
        json.dump({"pulls": cfg.get("pulls", []), "next": 50001}, open(os.path.join(d, "github.json"), "w"))
        self.write_gaps(cfg.get("paused", []))
        self.ref("deskgate/open/%d" % (now - 600), "deskgate open")
        if cfg.get("halt"):
            self.ref("filing/go/%d" % (now - 3600), "go")
            self.ref("filing/stop/%d" % (now - 60), "stop: maker rejection (mintcross)")
        for name, msg in cfg.get("refs", []):
            self.ref(name.replace("{OPEN}", str(now - 600)).replace("{NOW}", str(now)), msg)
        self.blob_ref("status/taken", "taken.txt", "# updated %d %s steps 0 mintcross\n" % (now - 5, time.strftime("%H:%M:%S", time.gmtime())))
        self.ref("status/dupclose", "dupclose %d pass ok rej10=0" % now)
        if cfg.get("grant_lost"):
            open(os.path.join(d, "grant_lost"), "w").write("1\n")
        for f in ("refs.log", "calls.log", "bus.log", "granted.txt"):
            open(os.path.join(d, f), "a").close()
        open(os.path.join(d, "refs.log"), "w").close()       # setup pushes are not counted

    def write_gaps(self, paused):
        g = {"id": GID, "statement": STMT, "file": "lean/PEqualNP/Outside/%s.lean" % GID.replace("-", "_"),
             "module": "PEqualNP.Outside." + GID.replace("-", "_"), "imports": ["PEqualNP.Defs"], "weight": 60,
             "lane": "main", "kind": "", "pr_numbers": [], "pr_open": 0, "held_now": False, "holders_now": 0,
             "title": "mintcross unit", "dead": []}
        js = {"gaps": [g], "paused": [{"handle": h, "paused_until": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() + 3600))} for h in paused],
              "withdrawn": {}, "checked": [], "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        open(os.path.join(self.d, "gaps.json"), "w").write(json.dumps(js))

    def env(self, who, extra=None):
        e = dict(os.environ)
        for k in list(e):
            if k.startswith(("GH_", "GITHUB_", "GIT_")) or k in ("PR_TOKEN", "READ_TOKEN"):
                e.pop(k)
        e.update(MX_WORLD=self.d, MX_WHO=who, PATH=os.path.join(self.d, "bin") + ":" + os.environ["PATH"],
                 GIT_CONFIG_GLOBAL=self.gitcfg, GIT_CONFIG_NOSYSTEM="1", GIT_ALLOW_PROTOCOL="file",
                 GIT_TERMINAL_PROMPT="0", HTTPS_PROXY="http://127.0.0.1:9", HTTP_PROXY="http://127.0.0.1:9",
                 https_proxy="http://127.0.0.1:9", http_proxy="http://127.0.0.1:9", NO_PROXY="", no_proxy="",
                 HOME=os.path.join(self.d, "home-" + who))
        os.makedirs(e["HOME"], exist_ok=True)
        e.update(extra or {})
        return e

    def _commit(self, msg, tree=None):
        env = self.env("setup")
        t = tree or sh("git", "-C", self.tk, "hash-object", "-t", "tree", "-w", "--stdin", inp="", env=env).stdout.strip()
        return sh("git", "-C", self.tk, "commit-tree", t, "-m", msg, env=env).stdout.strip()

    def ref(self, name, msg):
        c = self._commit(msg)
        sh("git", "-C", self.tk, "update-ref", "refs/heads/" + name, c, env=self.env("setup"))

    def blob_ref(self, name, fname, text):
        env = self.env("setup")
        b = sh("git", "-C", self.tk, "hash-object", "-w", "--stdin", inp=text, env=env).stdout.strip()
        t = sh("git", "-C", self.tk, "mktree", inp=f"100644 blob {b}\t{fname}\n", env=env).stdout.strip()
        sh("git", "-C", self.tk, "update-ref", "refs/heads/" + name, self._commit(name, t), env=env)

    def push_stop(self):
        """filing/stop pushed by dupclose (a maker rejection) while the components run"""
        e = self.env("dupclose")
        c = sh("git", "-C", self.tk, "commit-tree", sh("git", "-C", self.tk, "hash-object", "-t", "tree", "-w", "--stdin", inp="", env=e).stdout.strip(),
               "-m", "stop: rejection", env=e).stdout.strip()
        sh("git", "-C", self.tk, "update-ref", "refs/heads/filing/stop/%d" % int(time.time()), c, env=e)
        open(os.path.join(self.d, "stop_at"), "w").write("%.3f\n" % time.time())

    # ---- measurements
    def prs(self):
        return [p for p in json.load(open(os.path.join(self.d, "github.json")))["pulls"] if p["user"]["login"] == HANDLE]

    def lines(self, f):
        return [l.rstrip("\n").split("\t") if "\t" in l else l.split() for l in open(os.path.join(self.d, f)) if l.strip()]

    def desk(self, who=None):
        out = []
        for l in self.lines("refs.log"):
            if len(l) >= 4 and l[1].startswith("refs/heads/gatereq/") and not l[2].startswith("0000000") and (who is None or l[3] == who):
                out.append(("gatereq", float(l[0]), l[1].rsplit("/", 1)[-1]))
        for l in self.lines("bus.log"):
            if len(l) >= 5 and l[2] == "pub" and l[3] == "desk-req" and (who is None or l[1] == who):
                out.append(("bus", float(l[0]), l[4]))
        for l in self.lines("calls.log"):
            if len(l) >= 4 and l[0:1] and l[3] == "DESK" and (who is None or l[2] == who):
                out.append(("deskhost", float(l[0]), l[4] if len(l) > 4 else ""))
        return out

    def claims(self, who=None):
        return [l for l in self.lines("refs.log") if len(l) >= 4 and l[1].startswith("refs/heads/claim/")
                and not l[2].startswith("0000000") and (who is None or l[3] == who)]

    def calls(self, who):
        c = [l for l in self.lines("calls.log") if len(l) >= 4 and l[2] == who]
        return {"gh": sum(1 for l in c if l[1] == "gh"), "data": sum(1 for l in c if l[3].startswith("data-")),
                "unexpected": [l[3] + " " + (l[4] if len(l) > 4 else "") for l in c if l[3].startswith("UNEXPECTED")]}

    def granted(self):
        return {l[0] for l in self.lines("granted.txt") if l}


# ---------------------------------------------------------------------------------------------------------------
# component runners (each a child process; the child imports the real code)
# ---------------------------------------------------------------------------------------------------------------
def run_cloud(w, cloud_src, extra=None, timeout=120):
    tree = os.path.join(w.d, "cloud-tree")
    if not os.path.isdir(tree):
        sh("git", "clone", "-q", UP_URL + ".git", tree, env=w.env("cloud"))
    out = os.path.join(w.d, "cloud.out")
    if os.path.exists(out):
        os.remove(out)
    env = w.env("cloud", dict(ID=GID, MOD=GID.replace("-", "_"), PROOF=w.proof, TREE=tree, W=os.path.join(w.d, "cloud-w"),
                              GITHUB_REPOSITORY="Leg0shii/pequalnp-proofs-fork", PR_TOKEN="mintcross-fake", READ_TOKEN="",
                              GH_TOKEN="mintcross-fake", DESKGUARD_URL=w.tk, GITHUB_OUTPUT=out, GATE_WAIT_S="6",
                              FILE_FIRST="", **(extra or {})))
    os.makedirs(env["W"], exist_ok=True)
    r = subprocess.run([sys.executable, os.path.abspath(__file__), "--child-cloud", cloud_src], env=env, capture_output=True,
                       text=True, timeout=timeout)
    res = dict(l.split("=", 1) for l in open(out).read().splitlines() if "=" in l) if os.path.exists(out) else {}
    return res.get("result", "?"), (res.get("why", "") or (r.stdout + r.stderr).strip()[-200:])[:160], r


def child_cloud(src):
    sys.path.insert(0, os.path.join(src, ".github", "cloud-pr"))
    import submit as S
    real_run = S.run

    def run(cmd, timeout=300, env=None, cwd=None):
        if len(cmd) > 1 and cmd[0] == "bash" and cmd[1].endswith("checkcore.sh"):
            return subprocess.CompletedProcess(cmd, 0, "guards ok (mintcross: guard not under test)\n", "")
        return real_run(cmd, timeout=timeout, env=env, cwd=cwd)
    S.run = run
    try:
        S.main()
    except SystemExit:
        pass


def pc_tk(w, pc_src):
    """a toolkit dir laid out as on the PC: TK/watch/{watch,deskguard,bus}.py"""
    tk = os.path.join(w.d, "pc-tk"); wd = os.path.join(tk, "watch")
    if os.path.isdir(wd):
        return tk
    env = w.env("pc")
    sh("git", "clone", "-q", TK_URL + ".git", tk, env=env)        # TK is the PC's toolkit clone (origin = toolkit)
    os.makedirs(wd)
    for name, alts in (("watch.py", ("watch.py", "watch_watch.py")), ("deskguard.py", ("deskguard.py", "watch_deskguard.py"))):
        p = next((os.path.join(pc_src, a) for a in alts if os.path.exists(os.path.join(pc_src, a))), None)
        if not p:
            raise RuntimeError(f"no {name} in {pc_src}")
        shutil.copy(p, os.path.join(wd, name))
    open(os.path.join(wd, "bus.py"), "w").write(FAKE_BUS)
    open(os.path.join(tk, "formatscan.sh"), "w").write("#!/bin/sh\necho ok\n")
    # the PC clone: origin = fork, upstream = upstream; the deskguard clone of the toolkit
    sh("git", "clone", "-q", "-o", "origin", FORK_URL + ".git", os.path.join(w.d, "pc-repo"), env=env)
    sh("git", "-C", os.path.join(w.d, "pc-repo"), "remote", "add", "upstream", UP_URL + ".git", env=env)
    sh("git", "clone", "-q", TK_URL + ".git", os.path.join(w.d, "pc-dg"), env=env)
    return tk


def run_pc(w, pc_src, extra=None, timeout=150, ready=False):
    tk = pc_tk(w, pc_src)
    home = os.path.join(w.d, "pc-home"); os.makedirs(os.path.join(home, "out"), exist_ok=True)
    env = w.env("pc", dict(WATCH_HOME=home, PNP_REPO=os.path.join(w.d, "pc-repo"), DESKGUARD_REPO=os.path.join(w.d, "pc-dg"),
                           DESKGUARD_REMOTE="origin", DESKGUARD_HOME=os.path.join(w.d, "pc-dgh"), WATCH_TK=os.path.join(w.d, "pc-dg"),
                           WATCH_FETCH_LOCK=os.path.join(w.d, "pc-fetch.lock"), WATCH_GATE_WAIT="3", WATCH_LF_WAIT="3",
                           WATCH_SLOT_WAIT="3", WATCH_BUS="1", WATCH_BUS_PY=os.path.join(tk, "watch", "bus.py"),
                           PNP_SESSION_URL="", **(extra or {})))
    r = subprocess.run([sys.executable, os.path.abspath(__file__), "--child-pc" + ("-ready" if ready else ""), tk, w.proof],
                       env=env, capture_output=True, text=True, timeout=timeout)
    m = re.findall(r"^MXPC (.*)$", r.stdout, re.M)
    return (m[-1] if m else "crash: " + (r.stdout + r.stderr).strip()[-200:]), r


def child_pc_ready(tk, proof):
    """the PC's ready/ intake (intake_ready, the READY_GRACE path) with the grace already elapsed; handle_file is
    replaced by the real submit() so that the filing decision is intake_ready's own"""
    sys.path.insert(0, os.path.join(tk, "watch"))
    sys.argv = [os.path.join(tk, "watch", "watch.py")]
    import importlib.util
    spec = importlib.util.spec_from_file_location("watch", os.path.join(tk, "watch", "watch.py"))
    W = importlib.util.module_from_spec(spec)
    sys.modules["watch"] = W
    spec.loader.exec_module(W)
    gj = W.curl_json_fresh(W.GAPS, 60)
    gaps_by_id = {g["id"]: g for g in gj.get("gaps") or []}
    for g in gaps_by_id.values():
        W._HOLDERS[g["id"]] = g.get("holders_now") or 0
    held = {gid: 0 for gid in gaps_by_id}
    out = W.run(["git", "-C", W.TK, "ls-remote", "origin", "refs/heads/ready/*"], timeout=60).stdout
    state = {"done": {}, "seen": {}, "ready_first": {}}
    for line in out.splitlines():           # first sighting READY_GRACE + 1 s ago
        sha, ref = line.split()
        state["ready_first"][f"ready:{ref.split('refs/heads/ready/')[1]}:{sha}"] = time.time() - W.READY_GRACE - 1
    filed = []

    def handle_file(g, fam, args, st, path, t0=None):
        url, why = W.submit(g["id"], path, "Proof written by an AI worker.")
        filed.append({"gid": g["id"], "url": url, "why": str(why)[:120]})
        return "submitted" if url else "submitfail"
    W.handle_file = handle_file
    try:
        W.intake_ready(types_ns(), state, gaps_by_id, held, None)
        res = {"filed": filed, "done": state["done"], "grace": W.READY_GRACE}
    except Exception as e:
        res = {"filed": filed, "exception": repr(e)[:160]}
    print("MXPC", json.dumps(res), flush=True)
    os._exit(0)


def types_ns():
    import types
    return types.SimpleNamespace(dry_run=False, observe=False, once=True)


def child_pc(tk, proof):
    sys.path.insert(0, os.path.join(tk, "watch"))
    sys.argv = [os.path.join(tk, "watch", "watch.py")]
    import importlib.util
    spec = importlib.util.spec_from_file_location("watch", os.path.join(tk, "watch", "watch.py"))
    W = importlib.util.module_from_spec(spec)
    sys.modules["watch"] = W
    spec.loader.exec_module(W)
    # the gaps.json mirror read of the PC round fills the holders table (as in the watcher's loop)
    try:
        gj = W.curl_json_fresh(W.GAPS, 60)
        for g in gj.get("gaps") or []:
            W._HOLDERS[g["id"]] = g.get("holders_now") or 0
    except Exception as e:
        print("MXPC-NOTE gaps read failed", repr(e)[:120], flush=True)
    dst = os.path.join(W.HOME, "out", os.path.basename(proof)); shutil.copy(proof, dst)
    try:
        url, why = W.submit(GID, dst, "Proof written by an AI worker.")
    except Exception as e:
        url, why = None, "exception " + repr(e)[:160]
    print("MXPC", json.dumps({"url": url, "why": str(why)[:160]}), flush=True)
    os._exit(0)                        # daemon threads (late release) must not keep the child alive


FEED_SUBS = None


def run_feed(w, feed_src, sim_s=150, stop_after_claim=False, timeout=120):
    """feed.py's real source, run with its constants pointed into the world and a simulated clock (sleep advances it)"""
    g = os.path.join(w.d, "feed-g")
    if not os.path.isdir(g):
        sh("git", "clone", "-q", TK_URL + ".git", g, env=w.env("feed"))
    dd = os.path.join(w.d, "feed-d"); os.makedirs(dd, exist_ok=True)
    # one candidate for the feeder: our open unleased PR on GID, 10 min old, lowest
    n = 50000
    st = json.load(open(os.path.join(w.d, "github.json")))
    if not any(p["number"] == n for p in st["pulls"]):
        st["pulls"].append({"number": n, "state": "open", "title": GID, "body": "no lease", "user": {"login": HANDLE},
                            "head": {"ref": GID}, "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - 600)),
                            "merged_at": None, "closed_at": None, "html_url": f"https://github.com/open-goat/pequalnp-proofs/pull/{n}",
                            "by": "setup", "files": ["lean/PEqualNP/Outside/%s.lean" % GID.replace("-", "_")]})
        json.dump(st, open(os.path.join(w.d, "github.json"), "w"))
    created = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - 600))
    w.blob_ref("status/ours-unleased", "ours_unleased.tsv", f"{n}\t{GID}\t{created}\t1\n")
    env = w.env("feed", dict(MX_FEED_SRC=feed_src, MX_G=g, MX_D=dd, MX_SIM=str(sim_s), MX_STOP_AFTER_CLAIM="1" if stop_after_claim else ""))
    r = subprocess.run([sys.executable, os.path.abspath(__file__), "--child-feed"], env=env, capture_output=True, text=True, timeout=timeout)
    m = re.findall(r"^MXFEED (.*)$", r.stdout, re.M)
    return (m[-1] if m else "crash: " + (r.stdout + r.stderr).strip()[-200:]), r


class FakeTime:
    """the feeder's clock: time() starts at the real time; sleep() advances it; past MX_SIM simulated seconds the run ends"""
    def __init__(self, sim, hook=None):
        import time as _t
        self._t, self.now, self.end, self.hook = _t, _t.time(), _t.time() + sim, hook
        self.timezone, self.altzone = _t.timezone, _t.altzone

    def time(self):
        return self.now

    def sleep(self, s):
        self.now += max(float(s), 0.0)
        if self.hook:
            self.hook(self)
        if self.now > self.end:
            raise SystemExit("MXSIM-END")

    def __getattr__(self, k):
        return getattr(self._t, k)


def child_feed():
    src = open(os.environ["MX_FEED_SRC"]).read()
    W, G, D = os.environ["MX_WORLD"], os.environ["MX_G"], os.environ["MX_D"]
    subs = [  # (old, new): every outside path or URL of the feeder points into the world
        ('TK = "https://github.com/Leg0shii/pnp-toolkit.git"', f'TK = {os.path.join(W, "tk.git")!r}'),
        ('G = "/tmp/claude-0/w/ask-wt"', f"G = {G!r}"),
        ('D = "/tmp/claude-0/w/ll"', f"D = {D!r}"),
        ('ROWS = "/mnt/project-files/team/infra/gateway/lease_edit.txt"', f'ROWS = {os.path.join(D, "rows.txt")!r}'),
        ('ELOG = "/mnt/project-files/team/infra/gateway/lease_edit.log"', f'ELOG = {os.path.join(D, "elog.txt")!r}'),
        ('MIRROR_F = "/mnt/project-files/team/mirror/gaps.json"', f'MIRROR_F = {os.path.join(W, "gaps.json")!r}'),
        ('FLOG = "/mnt/project-files/team/infra/gateway/feed.log"', f'FLOG = {os.path.join(D, "feed.log")!r}'),
        ('"/mnt/project-files/team/comms/bus.py"', repr(os.path.join(D, "nomail.py"))),
        ("import json, os, re, subprocess, sys, time\n", "import json, os, re, subprocess, sys\ntime = __MX_TIME__\n"),
    ]
    miss = [o for o, _ in subs if o not in src]
    for o, n in subs:
        src = src.replace(o, n)
    left = sorted(set(re.findall(r"/mnt/project-files[^\s\"']*|https?://[^\s\"']+", src)) - {"https://github.com/open-goat/pequalnp-proofs"})
    if miss or left:
        print("MXFEED", json.dumps({"error": "feed.py shape changed: refusing to run", "missing": miss[:4], "outside": left[:6]}), flush=True)
        os._exit(0)
    open(os.path.join(D, "nomail.py"), "w").write("import sys, os, time\nopen(os.path.join(os.environ['MX_WORLD'], 'mail.log'), 'a')"
                                                  ".write(time.strftime('%H:%M:%S ') + ' '.join(sys.argv[1:]) + ' ' + sys.stdin.read()[:200].replace(chr(10), ' ') + chr(10))\n")
    gaps = os.path.join(W, "gaps.json")
    sent_stop = [False]

    def hook(ft):                      # the live mirror keeps its mtime fresh; the dupclose heartbeat too
        try:
            os.utime(gaps, (ft.now, ft.now))
        except OSError:
            pass
        if os.environ.get("MX_STOP_AFTER_CLAIM") and not sent_stop[0]:
            refs = subprocess.run(["git", "-C", os.path.join(W, "tk.git"), "for-each-ref", "--format=%(refname)", "refs/heads/claim/"],
                                  capture_output=True, text=True).stdout
            if refs.strip():
                sent_stop[0] = True
                e = dict(os.environ, MX_WHO="dupclose")
                tk = os.path.join(W, "tk.git")
                t = subprocess.run(["git", "-C", tk, "hash-object", "-t", "tree", "-w", "--stdin"], input="", capture_output=True, text=True, env=e).stdout.strip()
                c = subprocess.run(["git", "-C", tk, "commit-tree", t, "-m", "stop"], capture_output=True, text=True, env=e).stdout.strip()
                subprocess.run(["git", "-C", tk, "update-ref", "refs/heads/filing/stop/%d" % int(ft.now), c], env=e)
                open(os.path.join(W, "stop_at"), "w").write("%.3f\n" % time.time())
                # a fresh go-less stop; the claim lock is released so the feeder could claim again
                subprocess.run(["git", "-C", tk, "update-ref", "-d", subprocess.run(["git", "-C", tk, "for-each-ref", "--format=%(refname)", "refs/heads/claim/"], capture_output=True, text=True).stdout.split()[0]], env=e)
                with open(os.path.join(D, "done.txt"), "w"):
                    pass
        if sent_stop[0]:               # deskgate consumed the request (it answers nothing here): the door is free again
            for r in subprocess.run(["git", "-C", os.path.join(W, "tk.git"), "for-each-ref", "--format=%(refname)", "refs/heads/gatereq/"],
                                    capture_output=True, text=True).stdout.split():
                subprocess.run(["git", "-C", os.path.join(W, "tk.git"), "update-ref", "-d", r])
    ft = FakeTime(float(os.environ["MX_SIM"]), hook)
    # the dupclose heartbeat epoch must be fresh on the feeder's clock
    g = {"__name__": "__main__", "__MX_TIME__": ft, "__file__": os.environ["MX_FEED_SRC"]}
    why = "loop ended"
    try:
        exec(compile(src, "feed.py", "exec"), g)
    except SystemExit as e:
        why = "exit " + str(e.code)
    except Exception as e:
        why = "exception " + repr(e)[:160]
    print("MXFEED", json.dumps({"why": why, "sim_s": round(ft.now - (ft.end - float(os.environ["MX_SIM"])), 1)}), flush=True)
    os._exit(0)


# ---------------------------------------------------------------------------------------------------------------
# cases
# ---------------------------------------------------------------------------------------------------------------
def cost(w, who):
    c = w.calls(who)
    return f"gh={c['gh']} desk={len(w.desk(who))} data={c['data']}" + (f" UNEXPECTED={c['unexpected'][:3]}" if c["unexpected"] else "")


def verdict(name, comp, ok, detail, w, who):
    line = f"{'PASS' if ok else 'FAIL'} {name} {comp}: {detail} [{cost(w, who)}]"
    print(line, flush=True)
    return ok and not w.calls(who)["unexpected"]


def case_halt(a):
    w = World("H1", {"halt": True})
    res = []
    r, why, _ = run_cloud(w, a.cloud)
    p, d, c = [x for x in w.prs() if x["by"] == "cloud"], w.desk("cloud"), w.claims("cloud")
    res.append(verdict("H1-halt", "cloud", not p and not d and not c, f"result={r} prs={len(p)} desk={len(d)} claims={len(c)} ({why[:70]})", w, "cloud"))
    o, _ = run_pc(w, a.pc)
    p, d, c = [x for x in w.prs() if x["by"] == "pc"], w.desk("pc"), w.claims("pc")
    res.append(verdict("H1-halt", "pc", not p and not d and not c, f"prs={len(p)} desk={len(d)} claims={len(c)} {o[:90]}", w, "pc"))
    w3 = World("H1c", {"halt": True})                # a fresh world: the PC's claim lock must not hide the feeder's
    o, _ = run_feed(w3, a.feed, sim_s=90)
    d, c = w3.desk("feed"), w3.claims("feed")
    res.append(verdict("H1-halt", "feed", not d and not c, f"desk={len(d)} claims={len(c)} {o[:90]}", w3, "feed"))
    return all(res), w


def case_paused(a):
    w = World("H2", {"paused": [HANDLE]})
    res = []
    r, why, _ = run_cloud(w, a.cloud)
    d = w.desk("cloud")
    res.append(verdict("H2-paused", "cloud", not d, f"result={r} desk={len(d)} prs={len([x for x in w.prs() if x['by'] == 'cloud'])} ({why[:70]})", w, "cloud"))
    w2 = World("H2b", {"paused": [HANDLE]})          # a fresh world per component: the cloud's PR must not hide the PC's step
    o, _ = run_pc(w2, a.pc)
    d = w2.desk("pc")
    res.append(verdict("H2-paused", "pc", not d, f"desk={len(d)} {o[:100]}", w2, "pc"))
    o, _ = run_feed(w2, a.feed, sim_s=90)
    d = w2.desk("feed")
    res.append(verdict("H2-paused", "feed", not d, f"desk={len(d)} {o[:90]}", w2, "feed"))
    return all(res), w


def case_halt_mid(a):
    w = World("H3", {})
    o, _ = run_feed(w, a.feed, sim_s=150, stop_after_claim=True)
    try:
        t_stop = float(open(os.path.join(w.d, "stop_at")).read())
    except OSError:
        t_stop = None
    d = w.desk("feed"); c = w.claims("feed")
    after = [x for x in c if t_stop and float(x[0]) > t_stop]
    ok = t_stop is not None and not after
    return verdict("H3-halt-mid", "feed", ok, f"claims={len(c)} after_stop={len(after)} desk={len(d)} stop={'set' if t_stop else 'never (no first claim)'} {o[:80]}", w, "feed"), w


def case_rule161(a):
    """HARDENING 16.1 shapes, feeder: a tie is halted, a non-digit stop name is halted, for filing/* and deskgate/*"""
    res, w = [], None
    for tag, refs in (("filing-tie", [("filing/go/{NOW}", "go"), ("filing/stop/{NOW}", "stop")]),
                      ("filing-nondigit", [("filing/stop/now", "stop now"), ("filing/go/{NOW}", "go")]),
                      ("deskgate-tie", [("deskgate/stop/{OPEN}", "stop")]),
                      ("deskgate-nondigit", [("deskgate/stop/now", "stop now")])):
        w = World("H4-" + tag, {"refs": refs})
        o, _ = run_feed(w, a.feed, sim_s=60)
        d, c = w.desk("feed"), w.claims("feed")
        res.append(verdict("H4-rule16.1", "feed " + tag, not d and not c, f"desk={len(d)} claims={len(c)} {o[:70]}", w, "feed"))
    return all(res), w


def case_one_pr(a):
    w = World("O1", {})
    r, why, _ = run_cloud(w, a.cloud)
    o, _ = run_pc(w, a.pc)
    p = [x for x in w.prs() if x["head"]["ref"] == GID and x["state"] == "open"]
    ok1 = verdict("O1-one-pr", "cloud-then-pc", len(p) == 1, f"our open PRs on U={len(p)} by={[x['by'] for x in p]} cloud={r} pc={o[:60]}", w, "pc")
    w2 = World("O1b", {})
    o2, _ = run_pc(w2, a.pc)
    r2, why2, _ = run_cloud(w2, a.cloud)
    p2 = [x for x in w2.prs() if x["head"]["ref"] == GID and x["state"] == "open"]
    ok2 = verdict("O1-one-pr", "pc-then-cloud", len(p2) == 1, f"our open PRs on U={len(p2)} by={[x['by'] for x in p2]} pc={o2[:50]} cloud={r2}", w2, "cloud")
    return ok1 and ok2, w


def case_lost_answer(a):
    res = []
    w = World("B1", {"grant_lost": True})
    r, why, _ = run_cloud(w, a.cloud, timeout=180)
    bare = [x for x in w.prs() if x["by"] == "cloud" and "Lease:" not in x["body"] and GID in w.granted()]
    res.append(verdict("B1-lost-answer", "cloud", not bare, f"result={r} granted={sorted(w.granted())} bare_prs={len(bare)} desk={len(w.desk('cloud'))} ({why[:60]})", w, "cloud"))
    w2 = World("B1b", {"grant_lost": True})
    o, _ = run_pc(w2, a.pc)
    bare = [x for x in w2.prs() if x["by"] == "pc" and "Lease:" not in x["body"] and GID in w2.granted()]
    res.append(verdict("B1-lost-answer", "pc", not bare, f"granted={sorted(w2.granted())} bare_prs={len(bare)} desk={len(w2.desk('pc'))} {o[:70]}", w2, "pc"))
    return all(res), w


def case_ready_grace(a):
    """Y8/V6: the cloud drain works on U (drain-state seen.txt has U inflight, drain-beat fresh, claim/U and gatereq/U
    pushed by the cloud, no PR yet). The PC's ready/ intake past READY_GRACE must not file U while the drain holds it."""
    w = World("O2", {})
    env = w.env("cloud")
    mod = GID.replace("-", "_")
    # toolkit ready/<gid> with the file (what worker ready.sh pushes); the fork's ready/<gid> too
    body = open(w.proof).read()
    b = sh("git", "-C", w.tk, "hash-object", "-w", "--stdin", inp=body, env=env).stdout.strip()
    t1 = sh("git", "-C", w.tk, "mktree", inp=f"100644 blob {b}\t{mod}.lean\n", env=env).stdout.strip()
    t2 = sh("git", "-C", w.tk, "mktree", inp=f"040000 tree {t1}\tready\n", env=env).stdout.strip()
    c = sh("git", "-C", w.tk, "commit-tree", t2, "-m", "ready " + GID, env=env).stdout.strip()
    sh("git", "-C", w.tk, "update-ref", "refs/heads/ready/" + GID, c, env=env)
    # the drain run: seen.txt "<step> <sha> inflight <epoch>" on fork drain-state, a fresh fork drain-beat
    fb = sh("git", "-C", w.fork, "hash-object", "-w", "--stdin", inp=f"{GID} {c} inflight {int(time.time())}\n", env=env).stdout.strip()
    ft = sh("git", "-C", w.fork, "mktree", inp=f"100644 blob {fb}\tseen.txt\n", env=env).stdout.strip()
    sh("git", "-C", w.fork, "update-ref", "refs/heads/drain-state", sh("git", "-C", w.fork, "commit-tree", ft, "-m", "drain state 1", env=env).stdout.strip(), env=env)
    et = sh("git", "-C", w.fork, "hash-object", "-t", "tree", "-w", "--stdin", inp="", env=env).stdout.strip()
    sh("git", "-C", w.fork, "update-ref", "refs/heads/drain-beat", sh("git", "-C", w.fork, "commit-tree", et, "-m", "beat %d" % int(time.time()), env=env).stdout.strip(), env=env)
    # the drain's submit.py has taken the team claim lock and asked the gate (its PR comes when the answer does)
    w.ref("claim/" + GID, "claim " + GID + " cloud drain")
    w.ref("gatereq/" + GID, "claim " + GID + " cloud")
    o, _ = run_pc(w, a.pc, ready=True)
    p = [x for x in w.prs() if x["by"] == "pc"]
    return verdict("O2-ready-grace", "pc", not p, f"pc PRs while the drain holds U={len(p)} lease_in_body={[('Lease:' in x['body']) for x in p]} {o[:110]}", w, "pc"), w


CASES = [("H1", case_halt), ("H2", case_paused), ("H3", case_halt_mid), ("H4", case_rule161), ("O1", case_one_pr), ("O2", case_ready_grace), ("B1", case_lost_answer)]


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--child-cloud":
        return child_cloud(sys.argv[2])
    if len(sys.argv) > 1 and sys.argv[1] == "--child-pc-ready":
        return child_pc_ready(sys.argv[2], sys.argv[3])
    if len(sys.argv) > 1 and sys.argv[1] == "--child-pc":
        return child_pc(sys.argv[2], sys.argv[3])
    if len(sys.argv) > 1 and sys.argv[1] == "--child-feed":
        return child_feed()

    class A:
        pass
    a = A()
    a.cloud = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(HERE))
    a.pc = os.environ.get("MINTCROSS_PC", PC_DEF)
    a.feed = os.environ.get("MINTCROSS_FEED", FEED_DEF)
    only = {x.strip() for x in os.environ.get("MINTCROSS_ONLY", "").split(",") if x.strip()}
    sha = subprocess.run(["git", "-C", a.cloud, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    print(f"mintcross: cloud {a.cloud} ({sha}), pc {a.pc}, feed {a.feed}", flush=True)
    bad, t0 = [], time.time()
    for name, fn in CASES:
        if only and name not in only:
            continue
        t1 = time.time()
        try:
            ok, w = fn(a)
        except Exception as e:
            print(f"FAIL {name}: harness error {e!r}"[:300], flush=True); ok, w = False, None
        print(f"  {name} {time.time() - t1:.0f}s world {w.d if w else '-'}", flush=True)
        if not ok:
            bad.append(name)
        elif w and os.environ.get("MINTCROSS_KEEP") != "1":
            shutil.rmtree(w.d, ignore_errors=True)
    print(f"MINTCROSS {'PASS' if not bad else 'FAIL'} {sha}" + (": " + " ".join(bad) if bad else "") + f" ({time.time() - t0:.0f}s)", flush=True)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
