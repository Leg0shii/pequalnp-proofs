#!/usr/bin/env python3
"""ready-wait: dispatch cloud-pr for kept ready/<ID> branches the moment the desk lists the step.

cloud-pr ends 'waiting' and keeps ready/<ID> when the step is not listed yet (pre-generated waves). This loop polls the
listing (data.pequalnp.com gaps.json and pequalnp.com/desk/status: plain reads, no handle, no claim) and the fork's
ready/ branches, and dispatches cloud-pr on the branch (dry=false) once per branch sha per job. A branch must be at
least MIN_AGE s old, so the push run of a fresh branch is never doubled. Dispatches are paced (GitHub allows about
2 PR creations in parallel; cloud-pr retries refusals)."""
import json, os, re, subprocess, sys, time

FORK = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
END = time.time() + float(os.environ.get("MINUTES", "58")) * 60
MIN_AGE = 60
PACE = float(os.environ.get("PACE_S", "4"))
G = os.path.join(os.environ.get("W", "/tmp"), "rw.git")
first_seen, done = {}, set()


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


run(["git", "init", "-q", "--bare", G])
n = 0; last_l = 0; ids = set()
while time.time() < END:
    br = branches()
    now = time.time()
    for gid, sha in br.items():
        first_seen.setdefault((gid, sha), now)
    if now - last_l >= 10:
        ids = listed() or ids; last_l = now
    todo = [(g, s) for g, s in br.items() if (g, s) not in done and g in ids and now - first_seen[(g, s)] >= MIN_AGE]
    for gid, sha in sorted(todo, key=lambda x: first_seen[x]):
        if not re.fullmatch(r"L-[a-z0-9]+(-[a-z0-9]+)*", gid):
            done.add((gid, sha)); continue
        f = ready_file(gid, sha)
        done.add((gid, sha))
        if not f:
            log("SKIP", gid, "no single ready/ file"); continue
        r = run(["gh", "workflow", "run", "cloud-pr.yml", "--repo", FORK, "--ref", f"ready/{gid}",
                 "-f", f"step={gid}", "-f", f"file={f}", "-f", "dry=false"])
        n += 1
        log("DISPATCH" if r.returncode == 0 else "DISPATCH-FAIL", gid, f, (r.stderr or "").strip()[:150])
        if r.returncode:
            done.discard((gid, sha))
        time.sleep(PACE)
        if time.time() >= END:
            break
    time.sleep(5)
log("end:", n, "dispatches;", len(br), "ready/ branches;", len([g for g in br if g in ids]), "listed")
