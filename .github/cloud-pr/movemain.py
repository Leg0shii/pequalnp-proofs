#!/usr/bin/env python3
"""movemain.py (lane movingmain, W7, Lead 09:20 UTC 27 Nov): a fake upstream main that moves every S seconds, for the
loadcanary suffix -move<S>. REPO is a local bare depth-1 clone of upstream main (the drain's DRAIN_UPSTREAM points at it
as file://), so the moves cost GitHub nothing. Pushing a fork test ref every 4 s instead would be 15 pushes a minute
on the fork the real filing pushes to (GitHub's repository limit is about 6 a minute, W5 PUSH-429 at 08:49:57).
Each move is one commit on refs/heads/main: a new file lean/PEqualNP/Outside/L_move_<k>.lean (never a unit's path), and
every 5th move also changes .github/movetest.txt (a checked-out file, so the drain's base worktree really moves).
  movemain.py REPO SECONDS [MAX_MOVES]   -> one line per move "MOVE <k> <sha12> <epoch>", until killed or MAX_MOVES"""
import os, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import treebuild as T


def g(repo, *a, inp=None):
    r = subprocess.run(["git", "-C", repo] + list(a), input=inp, capture_output=True, text=True, timeout=60)
    if r.returncode:
        raise RuntimeError(" ".join(a[:2]) + ": " + r.stderr.strip()[-200:])
    return r.stdout.strip()


def move(repo, k):
    base = g(repo, "rev-parse", "refs/heads/main")
    blob = g(repo, "hash-object", "-w", "--stdin", inp=f"-- movemain {k} {time.time():.3f}\n")
    tree = T.tree_with_file(repo, base, f"lean/PEqualNP/Outside/L_move_{k}.lean", blob)
    if k % 5 == 0:
        blob2 = g(repo, "hash-object", "-w", "--stdin", inp=f"movemain {k}\n")
        c0 = g(repo, "commit-tree", tree, "-p", base, "-m", "tmp", inp="")
        tree = T.tree_with_file(repo, c0, ".github/movetest.txt", blob2)
    env = dict(os.environ, GIT_AUTHOR_NAME="movemain", GIT_AUTHOR_EMAIL="movemain@invalid", GIT_COMMITTER_NAME="movemain",
               GIT_COMMITTER_EMAIL="movemain@invalid")
    c = subprocess.run(["git", "-C", repo, "commit-tree", tree, "-p", base, "-m", f"movemain {k}"], input="", capture_output=True,
                       text=True, env=env, timeout=60).stdout.strip()
    g(repo, "update-ref", "refs/heads/main", c, base)
    return c


def main():
    repo, sec = sys.argv[1], float(sys.argv[2])
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
    t_next = time.time() + sec
    for k in range(1, n + 1):
        time.sleep(max(0.0, t_next - time.time()))
        t_next += sec
        try:
            c = move(repo, k)
            print(f"MOVE {k} {c[:12]} {time.time():.3f}", flush=True)
        except Exception as e:
            print(f"MOVE {k} failed: {e}", flush=True)


if __name__ == "__main__":
    main()
