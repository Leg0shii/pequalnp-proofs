#!/usr/bin/env python3
"""lift.py: THE lift tool (Lead 16.8 S3/S5, 27 Nov). The only code that pushes a go (besides the closer's blind lift)
and the only code that deletes a stop ref.

  python3 lift.py [--family filing|deskgate] [--prs 123,456] [--prune] [--dry] [--remote URL]
  python3 lift.py selftest          (hermetic: local bare repos, prints LIFT SELFTEST OK <sha16>)

1. Reads every refs/heads/<family>/* ref in ONE ls-remote (unreadable: exit 2, nothing pushed).
2. Halting stops = numeric stops >= the newest go (haltrule.family_state, a tie halts) + stops whose name is not plain
   digits. Each one's commit message is read; a rejection halt ("filing stop: REJ-HALT n <PRs>") is lifted only when
   --prs names EVERY PR in it; an unreadable message refuses. Refused: exit 3, nothing pushed.
3. Pushes <family>/go/<next_ref_epoch(now, every stop, newest go)> when a numeric stop halts or when no go exists yet
   (a non-digit stop is deleted only when a go above every numeric stop exists, S5).
4. Deletes the non-digit stops (lease push on their sha). --prune also deletes numeric stops BELOW the newest go.
5. Re-reads and prints the reader verdict: "FILING ALLOWED" (exit 0) or "STILL HALTED by <ref>" (exit 1).
Auth: PR_TOKEN (or LIFT_TOKEN) in the environment, else the caller's git credentials."""
import base64, os, re, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import haltrule

TK = "https://github.com/Leg0shii/pnp-toolkit.git"
LIFTER = {"filing": "filing/go", "deskgate": "deskgate/go"}


def _auth():
    tok = os.environ.get("LIFT_TOKEN") or os.environ.get("PR_TOKEN") or ""
    return ["-c", "http.https://github.com/.extraheader=AUTHORIZATION: basic "
            + base64.b64encode(f"x-access-token:{tok}".encode()).decode()] if tok else []


def git(*a, inp=None, env=None):
    return subprocess.run(["git", *_auth(), *a], capture_output=True, text=True, input=inp, env=env, timeout=120)


def snapshot(remote, family):
    r = git("ls-remote", remote, f"refs/heads/{family}/*")
    return (r.stdout if r.returncode == 0 else None), r.returncode


def message(g, remote, ref, sha):
    if git("-C", g, "fetch", "-q", remote, f"+refs/heads/{ref}:refs/lift/{len(ref)}-{sha[:12]}").returncode:
        return None
    r = git("-C", g, "log", "-1", "--format=%B", sha)
    return r.stdout.strip() if r.returncode == 0 else None


def halting_ref(txt, rc, family):
    """the ref a reader stops on (None = allowed)."""
    h, _ = haltrule.verdict(txt, rc, (family,))
    if not h:
        return None
    if rc or txt is None:
        return "refs-unreadable"
    fs = haltrule.family_state(txt, family)
    return fs["odd"][0] if fs["odd"] else f"{haltrule.FAMILIES[family][0]}/{fs['live'][0][0]}"


def lift(family="filing", prs=(), prune=False, dry=False, remote=TK, now=None, say=print):
    sp, gp = haltrule.FAMILIES[family][0], LIFTER[family]
    txt, rc = snapshot(remote, family)
    if rc:
        say("STILL HALTED by refs-unreadable (nothing pushed)")
        return 2
    fs = haltrule.family_state(txt, family)
    targets = [(f"{sp}/{e}", h) for e, h in fs["live"]] + fs["odd_rows"]
    g = tempfile.mkdtemp(prefix="lift-")
    git("init", "-q", "--bare", g)
    prs = {int(x) for x in prs}
    for ref, h in targets:
        m = message(g, remote, ref, h)
        if m is None:
            say(f"REFUSED {ref}: commit message unreadable (nothing pushed)")
            return 3
        r = re.match(r"\S+ stop: REJ-HALT \d+ ([\d ]+)", m)
        need = {int(x) for x in r.group(1).split()} if r else set()
        if need - prs:
            say(f"REFUSED {ref}: rejection halt for PRs {' '.join(map(str, sorted(need)))}; --prs misses "
                f"{' '.join(map(str, sorted(need - prs)))} (nothing pushed)")
            return 3
    env = dict(os.environ, GIT_AUTHOR_NAME="lift", GIT_AUTHOR_EMAIL="lift@localhost",
               GIT_COMMITTER_NAME="lift", GIT_COMMITTER_EMAIL="lift@localhost")
    tree = git("-C", g, "mktree", inp="").stdout.strip()
    need_go = bool(fs["live"]) or (bool(fs["odd"]) and fs["lift"] == 0)
    if need_go:
        for k in range(3):                            # a name taken meanwhile is refused (no -f): re-read, renumber
            n = haltrule.next_ref_epoch(now if now is not None else time.time(), [e for e, _ in fs["stops"]], [fs["lift"]])
            c = git("-C", g, "commit-tree", tree, "-m", f"{family} go: lift.py n={n} prs={','.join(map(str, sorted(prs))) or '-'} "
                    f"stops={','.join(r_ for r_, _ in targets)}", env=env).stdout.strip()
            if dry:
                say(f"DRY would push {gp}/{n}")
                break
            if git("-C", g, "push", "-q", remote, f"{c}:refs/heads/{gp}/{n}").returncode == 0:
                say(f"pushed {gp}/{n}")
                break
            txt, rc = snapshot(remote, family)
            if rc:
                say("STILL HALTED by refs-unreadable (go push failed)")
                return 2
            fs = haltrule.family_state(txt, family)
        else:
            say("STILL HALTED: go push failed 3 times")
            return 1
    if not dry:
        txt, rc = snapshot(remote, family)
        if rc:
            say("STILL HALTED by refs-unreadable")
            return 2
        fs = haltrule.family_state(txt, family)
        above = fs["lift"] > 0 and not fs["live"]      # S5: a go above every numeric stop exists
        dels = [(name, h) for name, h in fs["odd_rows"] if name in {r_ for r_, _ in targets}] if above else []
        if prune and fs["lift"]:
            dels += [(f"{sp}/{e}", h) for e, h in fs["stops"] if e < fs["lift"]]
        for name, h in dels:
            d = git("-C", g, "push", "-q", f"--force-with-lease=refs/heads/{name}:{h}", remote, f":refs/heads/{name}")
            say(("deleted " if d.returncode == 0 else "delete refused ") + name)
    txt, rc = snapshot(remote, family)
    bad = halting_ref(txt, rc, family)
    say(f"{family.upper()} ALLOWED" if bad is None else f"STILL HALTED by {bad}")
    return 0 if bad is None else 1


def selftest():
    import hashlib, shutil
    root = tempfile.mkdtemp(prefix="liftst-")
    fails = []

    def world(name, refs, hook=None):
        r = os.path.join(root, name + ".git")
        subprocess.run(["git", "init", "-q", "--bare", r], check=True)
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
        tree = subprocess.run(["git", "-C", r, "mktree"], input="", capture_output=True, text=True).stdout.strip()
        for ref, msg in refs:
            c = subprocess.run(["git", "-C", r, "commit-tree", tree, "-m", msg], capture_output=True, text=True, env=env).stdout.strip()
            subprocess.run(["git", "-C", r, "update-ref", "refs/heads/" + ref, c], check=True)
        if hook:
            p = os.path.join(r, "hooks", "post-receive"); open(p, "w").write(hook); os.chmod(p, 0o755)
        return r

    def refs(r):
        return sorted(l.split("\t")[1][11:] for l in subprocess.run(["git", "ls-remote", r], capture_output=True, text=True).stdout.splitlines())

    def run(name, r, want_rc, want_last, **k):
        out = []
        rc = lift(remote=r, say=out.append, now=1000, **k)
        ok = rc == want_rc and out and out[-1].startswith(want_last)
        print(("ok   " if ok else "FAIL ") + f"{name}: rc={rc} {' | '.join(out)}")
        if not ok:
            fails.append(name)
        return out

    os.environ.pop("PR_TOKEN", None); os.environ.pop("LIFT_TOKEN", None)
    r = world("l1", [("filing/stop/500", "filing stop: REJ-HALT 2 101 102")])
    run("L1a REJ-HALT, --prs misses 102 -> refused, nothing pushed", r, 3, "REFUSED filing/stop/500", prs=[101])
    if refs(r) != ["filing/stop/500"]:
        fails.append("L1a pushed")
    run("L1b --prs 101,102 -> go 1000, allowed", r, 0, "FILING ALLOWED", prs=[101, 102])
    r = world("l2", [("filing/stop/1500", "filing stop: Lead by hand"), ("filing/go/1500", "filing go: old")])
    out = run("L2 tie stop == go (R6) -> go 1501, allowed", r, 0, "FILING ALLOWED")
    if "pushed filing/go/1501" not in out:
        fails.append("L2 number")
    r = world("l3", [("filing/stop/rej-55", "filing stop: REJ-HALT 1 55")])
    out = run("L3 rej-55 only, no go -> go pushed, rej-55 deleted, allowed", r, 0, "FILING ALLOWED", prs=[55])
    if "filing/stop/rej-55" in refs(r):
        fails.append("L3 not deleted")
    r = world("l4", [("filing/go/9999999999", "filing go: far future"), ("filing/stop/rej-blind-ab12cd34", "filing stop: BLIND closed-read go=0")])
    out = run("L4 far-future go + odd blind stop -> no new go, odd deleted, allowed", r, 0, "FILING ALLOWED")
    if any(x.startswith("pushed") for x in out):
        fails.append("L4 pushed a go")
    r = world("l5", [("filing/stop/700", "filing stop: BLIND closed-read go=0"), ("filing/go/600", "x")])
    run("L5 blind stop, no --prs -> allowed", r, 0, "FILING ALLOWED")
    run("L6 remote unreadable -> exit 2", os.path.join(root, "missing.git"), 2, "STILL HALTED by refs-unreadable")
    r = world("l7", [("filing/stop/100", "a"), ("filing/stop/200", "b"), ("filing/go/300", "g"), ("filing/stop/400", "c")])
    run("L7 --prune: go 1000, stops 100 200 400 deleted (all below it)", r, 0, "FILING ALLOWED", prune=True)
    if [x for x in refs(r) if "stop" in x]:
        fails.append("L7 prune left " + str(refs(r)))
    hook = "#!/bin/sh\nwhile read o n ref; do case $ref in refs/heads/filing/go/*) git update-ref refs/heads/filing/stop/5000 $n;; esac; done\n"
    r = world("l8", [("filing/stop/900", "filing stop: Lead")], hook=hook)
    run("L8 a stop lands right after the go -> STILL HALTED by it", r, 1, "STILL HALTED by filing/stop/5000")
    r = world("l9", [("deskgate/stop/100", "deskgate stop: nofile"), ("deskgate/open/100", "open")])
    run("L9 deskgate tie stop/open -> deskgate/go 1000, allowed", r, 0, "DESKGATE ALLOWED", family="deskgate")
    r = world("l10", [("filing/stop/100", "filing stop: REJ-HALT 1 7"), ("filing/go/50", "g")])
    run("L10 dry -> nothing pushed", r, 1, "STILL HALTED by filing/stop/100", prs=[7], dry=True)
    if len(refs(r)) != 2:
        fails.append("L10 dry pushed")
    shutil.rmtree(root, ignore_errors=True)
    sha = hashlib.sha256(open(__file__, "rb").read()).hexdigest()[:16]
    print(("LIFT SELFTEST OK " if not fails else f"LIFT SELFTEST FAIL {fails} ") + sha)
    return 0 if not fails else 1


def main(argv):
    if argv[:1] == ["selftest"]:
        return selftest()
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", default="filing", choices=sorted(LIFTER))
    ap.add_argument("--prs", default="")
    ap.add_argument("--prune", action="store_true")
    ap.add_argument("--dry", action="store_true")
    ap.add_argument("--remote", default=TK)
    a = ap.parse_args(argv)
    return lift(a.family, [x for x in re.split(r"[,\s]+", a.prs) if x], a.prune, a.dry, a.remote)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
