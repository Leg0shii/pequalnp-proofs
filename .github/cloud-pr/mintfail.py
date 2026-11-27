#!/usr/bin/env python3
"""mintfail (HARDENING section 14, W6; red team BLINDSPOTS B9 partial failures and B10 process death, opener side).

Runs the REAL submit.py (and the REAL drain.py work/save_seen bookkeeping) of a checkout on mintdrill's fake world,
with one fault injected in the first run, then a clean next run on the SAME persistent fake state (fork branches,
ready/ branches, upstream PRs, toolkit claim/<id> refs and recorded leases, gate release requests, drain-state).

Faults (first run only):
  pr_timeout_once   gh pr create creates the PR, then the call times out (run() turns it into stderr "timeout")
  pr_timeout_all    every gh pr create creates (or finds) the PR and times out
  push_half         the fork push updates the branch, then the connection drops ("remote end hung up")
  kill_after_claim  the opener dies right after the gate granted the lease (before record_lease)
  kill_after_pr     the opener dies right after gh pr create returned the PR (before release / delete_ready)
  kill_drain_state  the drain runner dies after the child finished, before its drain-state record is pushed
  die_with_child    the whole runner dies with the child (kill_after_pr inside a drain)
Modes: "submit" = the single-branch job (ready/<ID> push or ready-wait dispatch), "drain" = drain.py work() with its
drain-state record (seen.txt), the production path at a mint.

Asserted after the next run, per unit: exactly one open PR of ours (I1, no duplicate), the ready/<ID> branch gone
(clean), at most one desk claim (one claim per step, ever), a lease the gate granted is on the PR or released (no
lost lease), every lease on a PR is released, and the head of an open PR is never rewritten (a force push onto an
open PR is an edit).

  python3 mintfail.py [SRC]   -> one line per case, then "MINTFAIL PASS <sha>" (exit 0) or "MINTFAIL FAIL <sha>: ..."
Nothing leaves the box: every call the fakes do not know is logged as UNEXPECTED and fails the case."""
import json, os, re, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mintdrill as MD                     # the fake world (mirror, GitHub reads, taken list, gate) of the replay suite

HANDLE = MD.HANDLE
UPURL = "https://github.com/open-goat/pequalnp-proofs/pull/%d"


# ---------------------------------------------------------------------------------------------------------------
# persistent fake state (one JSON file per case, shared by every run of the case)
# ---------------------------------------------------------------------------------------------------------------
def st_load():
    return json.load(open(os.environ["MF_STATE"]))


def st_save(s):
    p = os.environ["MF_STATE"]
    json.dump(s, open(p + ".tmp", "w"), indent=1)
    os.replace(p + ".tmp", p)


def st_new(gid, ready_sha="r0"):
    return {"prs": [], "fork": {}, "ready": {gid: ready_sha}, "claims": {}, "leases": {}, "releases": [], "desk": [],
            "seen": None, "next_pr": 99001, "events": [], "commits": 0}


def die(s, why):
    s["events"].append("KILLED " + why)
    st_save(s)
    sys.stdout.flush()
    os._exit(137)


# ---------------------------------------------------------------------------------------------------------------
# child: one submit.py run (mintdrill's child_submit, plus stateful pushes / PRs / claims / releases and faults)
# ---------------------------------------------------------------------------------------------------------------
def child_submit(src, w):
    sys.path.insert(0, os.path.join(src, ".github", "cloud-pr"))
    import submit as S
    real = {k: getattr(S, k) for k in ("main", "claim_lock", "release")}
    faults = set(filter(None, os.environ.get("MF_FAULT", "").split(",")))
    gid = os.environ["ID"]
    cnt = {"pr_create": 0, "push": 0}

    def ours_open():
        return [p for p in st_load()["prs"] if p["head"] == gid and p["state"] == "open"]

    def wrapped_main():
        md_run, md_gh, md_git, md_claim = S.run, S.gh, S.git, S.gate_claim

        def run(cmd, timeout=300, env=None, cwd=None):
            if (cmd[:3] == ["gh", "pr", "create"] or (cmd[:2] == ["gh", "api"] and "POST" in cmd and any(str(x).endswith("/pulls") for x in cmd))):
                cnt["pr_create"] += 1
                s = st_load()
                body = cmd[cmd.index("--body") + 1] if "--body" in cmd else next(x[5:] for x in cmd if str(x).startswith("body="))
                old = [p for p in s["prs"] if p["head"] == gid and p["state"] == "open"]
                if old and "pr_timeout_all" in faults:       # GitHub slow: even the "already exists" answer times out
                    return subprocess.CompletedProcess(cmd, 1, "", "timeout")
                if old:
                    s["events"].append("pr create: already exists #%d" % old[0]["number"]); st_save(s)
                    return subprocess.CompletedProcess(cmd, 1, "", 'a pull request for branch "%s:%s" into branch "main" '
                                                       'already exists:\n%s\n' % (HANDLE, gid, UPURL % old[0]["number"]))
                if gid not in s["fork"]:
                    return subprocess.CompletedProcess(cmd, 1, "", "pull request create failed: GraphQL: Head sha can't be blank")
                n = s["next_pr"]; s["next_pr"] += 1
                lease = (re.findall(r"^Lease: (\S+)$", body, re.M) or [None])[0]
                s["prs"].append({"number": n, "head": gid, "head_sha": s["fork"][gid], "state": "open", "lease": lease,
                                 "user": HANDLE})
                s["events"].append("PR #%d created (lease %s)" % (n, lease))
                st_save(s)
                if "pr_timeout_all" in faults or ("pr_timeout_once" in faults and cnt["pr_create"] == 1):
                    return subprocess.CompletedProcess(cmd, 1, "", "timeout")
                if "kill_after_pr" in faults:
                    die(s, "after gh pr create #%d" % n)
                return subprocess.CompletedProcess(cmd, 0, UPURL % n + "\n", "")
            if cmd[:1] == ["git"] and "push" in cmd and any("refs/heads/gatereq/" in x for x in cmd):
                s = st_load()
                spec = cmd[-1]
                m = re.search(r"release (\S+) (\S+)", " ".join(cmd))
                s["releases"].append(spec.split(":", 1)[-1])
                s["events"].append("gate release request " + spec.split(":", 1)[-1])
                st_save(s)
                return subprocess.CompletedProcess(cmd, 0, "", "")
            return md_run(cmd, timeout=timeout, env=env, cwd=cwd)
        S.run = run

        def gh(args, write=False, timeout=120):
            a = list(args)
            if a[0] == "api" and "/pulls?" in a[1] and "head=" in a[1]:      # open_pr_for_branch: our own PR, exact
                if "state=closed" in a[1]:                                    # (infra 06:30: closed PRs on the head)
                    cl = [p for p in st_load()["prs"] if p["head"] == gid and p["state"] == "closed"]
                    return subprocess.CompletedProcess(a, 0, "".join(UPURL % p["number"] + "\n" for p in cl), "")
                return subprocess.CompletedProcess(a, 0, "".join(UPURL % p["number"] + "\n" for p in ours_open()), "")
            return md_gh(args, write=write, timeout=timeout)
        S.gh = gh

        def git(*a, env=None, timeout=300):
            if a and a[0] == "commit-tree":                # a fresh commit per run (real git: new timestamps, new sha)
                s = st_load(); s["commits"] += 1; st_save(s)
                return subprocess.CompletedProcess(list(a), 0, "commit%d\n" % s["commits"], "")
            return md_git(*a, env=env, timeout=timeout)
        S.git = git

        def push_branch(c, g):
            cnt["push"] += 1
            s = st_load()
            for p in s["prs"]:
                if p["head"] == g and p["state"] == "open" and p["head_sha"] != c:
                    s["events"].append("HEAD REWRITTEN on open PR #%d: %s -> %s" % (p["number"], p["head_sha"], c))
                    p["head_sha"] = c
            s["fork"][g] = c
            st_save(s)
            if "push_half" in faults and cnt["push"] == 1:
                return "fatal: the remote end hung up unexpectedly"
            return None
        S.push_branch = push_branch
        # infra 06:30: the fork branch state (create-only head) and the gate's persistent answer ref lease/<gid>
        S.fork_head = lambda g: st_load()["fork"].get(g)

        def gate_answer_lease(g):
            ok = [x.split()[-1] for x in st_load()["desk"] if x.startswith("claim %s -> ok " % g)]
            return ok[-1] if ok else None
        S.gate_answer_lease = gate_answer_lease

        def delete_ready():
            if os.environ.get("GITHUB_REF_NAME") == f"ready/{gid}":
                s = st_load(); s["ready"].pop(gid, None); s["events"].append("ready/%s deleted" % gid); st_save(s)
        S.delete_ready = delete_ready

        class DG:
            REPO = "/nonexistent"
            SLOTS = 4
            def lease_of(self, g): return st_load()["leases"].get(g)
            def acquire(self, g, why=None):
                s = st_load()
                if g in s["claims"]:
                    if why is not None:
                        why.append("claim/%s exists" % g)
                    return False
                s["claims"][g] = "claimed"; st_save(s)
                return True
            def record_lease(self, g, lid, terms=None):
                s = st_load(); s["leases"][g] = str(lid); st_save(s)
            def _marker(self, m): return "marker0"
            def slot_take(self, who, wait=0): return "slot0"
            def slot_free(self, k): return None
        S.dg = lambda: DG()
        S.claim_lock = real["claim_lock"]           # the real one-claim-per-step lock, on the stateful claim refs
        S.release = real["release"]                 # the real gate release request (git push gatereq/<ID>), recorded

        def gate_claim(g):
            cls, lid = md_claim(g)
            s = st_load(); s["desk"].append("claim %s -> %s %s" % (g, cls, lid)); st_save(s)
            if "kill_after_claim" in faults and cls == "ok":
                die(s, "after the gate granted %s" % lid)
            return cls, lid
        S.gate_claim = gate_claim
        return real["main"]()
    S.main = wrapped_main
    return MD.child_submit(src, w)


# ---------------------------------------------------------------------------------------------------------------
# drain child: the real drain.py work() (one branch) with its drain-state record, git and runner faked
# ---------------------------------------------------------------------------------------------------------------
def child_drain(src, w):
    sys.path.insert(0, os.path.join(src, ".github", "cloud-pr"))
    import drain as D
    faults = set(filter(None, os.environ.get("MF_FAULT", "").split(",")))
    gid = w["gid"]; mod = gid.replace("-", "_")
    blobs, trees, commits = {}, {}, {}
    unexpected = []

    def cp(a, rc=0, out="", err=""):
        return subprocess.CompletedProcess(list(a), rc, out, err)

    def sh(*a, timeout=300, env=None, cwd=None, input=None):
        s = " ".join(a)
        st = st_load()
        if a[0] == sys.executable and a[-1].endswith("submit.py"):
            e = dict(env, MF_FAULT=",".join(x for x in faults if x in ("pr_timeout_once", "pr_timeout_all", "push_half",
                                                                         "kill_after_claim", "kill_after_pr")))
            r = subprocess.run([sys.executable, os.path.abspath(__file__), "--child"], input=json.dumps(w),
                               capture_output=True, text=True, env=e, timeout=120, cwd=env["W"])
            m = re.search(r"^MDRESULT (.*)$", r.stdout, re.M)
            if m:
                res = json.loads(m.group(1))
                if res.get("unexpected"):
                    unexpected.extend(res["unexpected"])
            if r.returncode == 137 and "die_with_child" in faults:
                die(st_load(), "drain runner died with its child")
            return cp(a, r.returncode, r.stdout, r.stderr)
        if a[0] == "git" and "ls-remote" in a and "refs/heads/ready/*" in a:
            return cp(a, 0, "".join(f"{sha}\trefs/heads/ready/{g}\n" for g, sha in st["ready"].items()))
        if a[0] == "git" and "ls-remote" in a and "refs/heads/filing/*" in a:
            return cp(a, 0, "")
        if a[0] == "git" and "fetch" in a and any("drain-state" in x for x in a):
            return cp(a, 0 if st["seen"] is not None else 1)
        if a[0] == "git" and "show" in a and a[-1].startswith("refs/drain/state:"):
            return cp(a, 0, (st["seen"] or "") if a[-1].endswith("seen.txt") else "")
        if a[0] == "git" and "fetch" in a and any("refs/heads/ready/" in x for x in a):
            return cp(a, 0 if gid in st["ready"] else 1)
        if a[0] == "git" and "rev-parse" in a:
            return cp(a, 0, st["ready"].get(gid, "") + "\n")
        if a[0] == "git" and "ls-tree" in a:
            return cp(a, 0, f"ready/{mod}.lean\n")
        if a[0] == "git" and "show" in a and a[-1].endswith(".lean"):
            return cp(a, 0, "import PEqualNP.Defs\n-- drill\n")
        if a[0] == "git" and "log" in a:
            return cp(a, 0, f"ready {gid}\n")
        if a[0] == "git" and "clone" in a:
            t = a[a.index("--branch") + 3]
            os.makedirs(os.path.join(t, ".github", "scripts"), exist_ok=True)
            return cp(a)
        if a[0] == "git" and ("sparse-checkout" in a or "checkout" in a):
            return cp(a)
        if a[0] == "rm":
            return cp(a)
        if a[0] == "git" and "hash-object" in a:
            k = "blob%d" % len(blobs); blobs[k] = input or ""
            return cp(a, 0, k + "\n")
        if a[0] == "git" and "mktree" in a:
            k = "tree%d" % len(trees)
            trees[k] = {l.split("\t")[1]: l.split()[2] for l in (input or "").splitlines() if "\t" in l}
            return cp(a, 0, k + "\n")
        if a[0] == "git" and "commit-tree" in a:
            k = "dcommit%d" % len(commits); commits[k] = a[a.index("commit-tree") + 1]
            return cp(a, 0, k + "\n")
        if a[0] == "git" and "push" in a and a[-1].endswith(":refs/heads/drain-state"):
            if "kill_drain_state" in faults:
                die(st, "drain runner died before the drain-state push")
            c = a[-1].split(":", 1)[0]
            st["seen"] = blobs[trees[commits[c]]["seen.txt"]]
            st["events"].append("drain-state pushed: " + st["seen"].strip().replace("\n", " | ")[:160])
            st_save(st)
            return cp(a)
        unexpected.append("drain: " + s[:90])
        return cp(a, 1, "", "unexpected")
    D.sh = sh
    D.load_seen()
    res = []
    for sid, sha in D.pending():                    # one pass of the drain loop, one worker (deterministic)
        res.append(D.work(sid, sha))
    return {"drained": res, "unexpected": unexpected, "seen": {f"{k[0]} {k[1]}": v[0] for k, v in D.SEEN.items()}}


# ---------------------------------------------------------------------------------------------------------------
# parent
# ---------------------------------------------------------------------------------------------------------------
def spawn(mode, src, w, state, fault, d):
    proof = os.path.join(d, "proof.lean")
    open(proof, "w").write("import PEqualNP.Defs\n-- drill\n")
    gid = w["gid"]
    env = dict(os.environ, ID=gid, MOD=gid.replace("-", "_"), PROOF=proof, TREE=d, W=d,
               GITHUB_OUTPUT=os.path.join(d, "out-%d" % time.time_ns()), PR_TOKEN="drill", READ_TOKEN="drill", DRY="0",
               GITHUB_REF_NAME=f"ready/{gid}", READY_MSG="", MD_KIND="submit", MD_SRC=src, MF_STATE=state, MF_FAULT=fault,
               PNP_LINKEDIN="", PNP_LINKEDIN_READ="1", SRC=src, DRAIN_WORKERS="1")
    env.pop("GITHUB_ACTIONS", None)
    env.pop("CLAIM_FIRST", None); env.pop("FILE_FIRST", None)
    env.update(w.get("env") or {})
    r = subprocess.run([sys.executable, os.path.abspath(__file__), "--drain" if mode == "drain" else "--child"],
                       input=json.dumps(w), capture_output=True, text=True, env=env, timeout=300, cwd=d)
    open(os.path.join(d, "log.txt"), "w").write(r.stdout + "\n--- stderr\n" + r.stderr)
    m = re.search(r"^MDRESULT (.*)$", r.stdout, re.M)
    if r.returncode == 137:
        return {"killed": True}
    if not m:
        return {"crash": (r.stderr or r.stdout).strip().splitlines()[-3:]}
    return json.loads(m.group(1))


def judge(s, runs):
    gid = s["gid"]
    bad = []
    for k, r in enumerate(runs):
        if r.get("crash"):
            bad.append(f"run{k + 1} crash " + " | ".join(r["crash"]))
        if r.get("unexpected"):
            bad.append(f"run{k + 1} unexpected " + ", ".join(r["unexpected"][:3]))
    op = [p for p in s["prs"] if p["head"] == gid and p["state"] == "open"]
    if len(op) != 1:
        bad.append(f"{len(op)} open PRs of ours on the unit (want 1)")
    if gid in s["ready"]:
        bad.append(f"ready/{gid} still there after the next run")
    claims = [x for x in s["desk"] if x.startswith("claim ")]
    if len(claims) > 1:
        bad.append(f"{len(claims)} desk claims (one per step, ever)")
    granted = [x.split()[-1] for x in claims if " -> ok " in x]
    for lid in granted:
        on_pr = any(p["lease"] == lid for p in op)
        rel = any(lid in r or gid in r for r in s["releases"])
        if not on_pr and not rel:
            bad.append(f"granted lease {lid} neither on the PR nor released (lost lease)")
    for p in op:
        if p["lease"] and not any(gid in r for r in s["releases"]):
            bad.append(f"lease {p['lease']} on PR #{p['number']} never released")
    rw = [e for e in s["events"] if e.startswith("HEAD REWRITTEN")]
    if rw:
        bad.append(rw[0])
    return bad


def case_list():
    g0 = 94000
    out = []
    leased = {"CLAIM_FIRST": "tl6c-not-search"}
    spec = [
        ("B9-pr-timeout-once", "pr_timeout_once", {}),
        ("B9-pr-timeout-all", "pr_timeout_all", {}),
        ("B9-push-half", "push_half", {}),
        ("B10-kill-after-claim", "kill_after_claim", leased),
        ("B10-kill-after-pr", "kill_after_pr", {}),
        ("B10-kill-after-pr-leased", "kill_after_pr", leased),
    ]
    k = 0
    for mode in ("submit", "drain"):
        for name, fault, env in spec:
            out.append((f"{mode}/{name}", mode, fault, env, g0 + k)); k += 1
            if fault in ("kill_after_pr", "pr_timeout_all"):   # next run with the taken list already showing our PR
                out.append((f"{mode}/{name}-tlfresh", mode, fault, env, g0 + k)); k += 1
    out.append(("drain/B10-kill-before-drain-state", "drain", "kill_drain_state", {}, g0 + k)); k += 1
    out.append(("drain/B10-runner-dies-with-child", "drain", "kill_after_pr,die_with_child", {}, g0 + k)); k += 1
    return out


def main():
    if sys.argv[1:2] == ["--child"]:
        w = json.loads(sys.stdin.read())
        r = child_submit(os.environ["MD_SRC"], w)
        print("MDRESULT " + json.dumps(r))
        return 0
    if sys.argv[1:2] == ["--drain"]:
        w = json.loads(sys.stdin.read())
        r = child_drain(os.environ["SRC"], w)
        print("MDRESULT " + json.dumps(r))
        return 0
    src = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(HERE))
    sha = subprocess.run(["git", "-C", src, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    t = time.time()
    fails = []
    for name, mode, fault, env, n in case_list():
        fresh = name.endswith("-tlfresh")
        gid = "L-meta-%d" % n
        d = tempfile.mkdtemp(prefix="mintfail-")
        state = os.path.join(d, "state.json")
        json.dump(dict(st_new(gid), gid=gid), open(state, "w"))
        w = {"gid": gid, "gaps": [MD.unit(gid)], "taken": {"L-meta-1": "someone"}, "gate_answers": {"*": "ok"},
             "env": env}
        runs = []
        for k, f in enumerate((fault, "")):            # the faulty run, then the clean next run on the same state
            rd = tempfile.mkdtemp(prefix="run%d-" % (k + 1), dir=d)
            st = json.load(open(state))
            if k == 1 and mode == "submit" and gid not in st["ready"]:
                runs.append({"result": "none (ready/ gone, no re-dispatch)", "unexpected": []})   # nothing triggers a run
                continue
            wk = json.loads(json.dumps(w))
            if k == 1 and fresh and any(p["head"] == gid and p["state"] == "open" for p in st["prs"]):
                wk["taken"][gid] = HANDLE                # the taken list already shows our PR at the next run
            runs.append(spawn(mode, src, wk, state, f, rd))
        s = json.load(open(state))
        bad = judge(s, runs)
        res = []
        for r in runs:
            if r.get("killed"):
                res.append("killed")
            elif "drained" in r:
                res.append("drain:" + ",".join(f"{v}" for v in r["seen"].values()) if r["seen"] else "drain:-")
            else:
                res.append(r.get("result", "?"))
        reads = sum(r.get("reads", 0) for r in runs if isinstance(r, dict))
        line = f"runs={'/'.join(res)} prs={len([p for p in s['prs'] if p['head'] == gid])} desk={len(s['desk'])} reads={reads}"
        print(("ok  " if not bad else "FAIL"), name, "; ".join(bad) or "one PR, clean", "|", line)
        if bad:
            fails.append(name)
    print(f"{time.time() - t:.0f}s")
    if fails:
        print(f"MINTFAIL FAIL {sha}: " + ", ".join(fails))
        return 1
    print(f"MINTFAIL PASS {sha}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
