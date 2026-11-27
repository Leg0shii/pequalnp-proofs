# twintest.py [dir of submit.py]: OPENER-TWIN cases (Lead 17:45 UTC 27 Nov), in-process, DRY, GitHub faked.
#   file:      row free, offerable_now false, its twin held with pr_open 0 (twin_of either direction) -> clear
#   refuse:    twin has a PR / row held / rival PR on the row / taken list blocks / no twin at all
# Prints one line per case and "TWIN SELFTEST OK <n>" or "TWIN SELFTEST FAIL <cases>". Exit 0 iff OK.
import os, sys, tempfile
os.environ.update(ID="L-meta-2", MOD="L_meta_2", PROOF="/dev/null", TREE="/tmp", W=tempfile.mkdtemp(), DRY="1",
                  RIVAL_SNAP_DIR=tempfile.mkdtemp(), GHCOND_DIR=tempfile.mkdtemp())
os.environ.pop("FILING_FIXTURE", None)
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import submit as S

res = []
def row(i, **k):
    d = dict(id=i, kind="lemma", weight=5, pr_open=0, pr_numbers=[], held_now=False, holders_now=0, offerable_now=True)
    d.update(k); return d
def run(name, gaps, want, block=None, gid="L-meta-2"):
    gj = {"gaps": gaps}
    S.gaps_json = lambda *a, **k: gj
    S.race_check = lambda *a, **k: (block or [])
    S.rival_now = lambda *a, **k: None
    S.own_pr = lambda n: False
    S.pr_accepted = lambda n: True
    S.pr_oversized = lambda n, g: False
    ok, why, _ = S.race_ok(gid)
    good = ok == want
    res.append((name, good)); print(("ok   " if good else "FAIL ") + f"twin/{name} -> {ok} {why[:90]}")

me = lambda **k: row("L-meta-2", offerable_now=False, twin_of="L-meta-1", **k)
run("twin-held-file", [row("L-meta-1", held_now=True, holders_now=1, offerable_now=False), me()], True)
run("twin-reverse-file", [row("L-meta-3", twin_of="L-meta-2", held_now=True, holders_now=1), row("L-meta-2", offerable_now=False)], True)
run("twin-pr-refuse", [row("L-meta-1", held_now=True, pr_open=1, pr_numbers=[41000]), me()], False)
run("row-held-refuse", [row("L-meta-1", held_now=True), me(held_now=True, holders_now=1)], False)
run("rival-pr-refuse", [row("L-meta-1", held_now=True), me(pr_open=1, pr_numbers=[41001])], False)
run("taken-refuse", [row("L-meta-1", held_now=True), me()], False, block=[{"number": "?", "why": "taken list: first PR by x"}])
run("no-twin-refuse", [row("L-meta-2", offerable_now=False)], False)
run("offerable-unchanged", [row("L-meta-2")], True)
bad = [n for n, g in res if not g]
print(f"TWIN SELFTEST OK {len(res)}" if not bad else "TWIN SELFTEST FAIL " + " ".join(bad))
sys.exit(1 if bad else 0)
