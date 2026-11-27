#!/usr/bin/env python3
"""haltrule.py: THE stop/go rule (Lead 16.1, 27 Nov 06:22 UTC). One implementation for every reader: dupclose.py,
submit.py, drain.py, the PC watcher and deskgate (copy this file unchanged into the toolkit; `python3 haltrule.py`
runs the selftest and prints `HALTRULE OK <sha16>`).

For each ref family, read from ONE ls-remote snapshot:
  halted  iff  the refs are unreadable
          or   any name under the stop prefix is not plain digits (halted until that ref is deleted)
          or   newest stop >= newest lifter                (a tie is halted)
  filing:   stop = filing/stop/<n>     lifter = filing/go/<n>
  deskgate: stop = deskgate/stop/<n>   lifter = deskgate/go/<n> or deskgate/open/<n>
A lifter name that is not plain digits lifts nothing. No go has to name a stop. Nobody compares a ref number with a
clock. Writers number new refs with next_ref_epoch() over the refs read right before the push.
Pure: no I/O, no clock, stdlib only."""
import re

FAMILIES = {"filing": ("filing/stop", ("filing/go",)),
            "deskgate": ("deskgate/stop", ("deskgate/go", "deskgate/open"))}
_ROW = re.compile(r"^(\S+)\s+refs/heads/(\S+)\s*$", re.M)


def rows(ls_remote_text):
    """[(sha, name under refs/heads/)] of an ls-remote listing."""
    return [(h, n) for h, n in _ROW.findall(ls_remote_text or "")]


def _under(name, prefix):
    return name == prefix or name.startswith(prefix + "/")


def _num(name, prefix):
    """<n> of prefix/<n> when <n> is plain digits, else None."""
    rest = name[len(prefix) + 1:] if name.startswith(prefix + "/") else ""
    return int(rest) if rest.isdigit() and rest.isascii() else None


def family_state(ls_remote_text, family="filing"):
    """dict: stops [(n, sha)] newest first, odd [names under the stop prefix that are not plain digits] (odd_rows:
    [(name, sha)]),
    lift = newest lifter number (0 if none), live [(n, sha)] = stops with n >= lift (newest first)."""
    sp, lps = FAMILIES[family]
    stops, odd, odd_rows, lift = [], [], [], 0
    for h, name in rows(ls_remote_text):
        if _under(name, sp):
            n = _num(name, sp)
            if n is None:
                odd.append(name); odd_rows.append((name, h))
            else:
                stops.append((n, h))
        for lp in lps:
            n = _num(name, lp)
            if n is not None:
                lift = max(lift, n)
    stops.sort(reverse=True)
    return {"stops": stops, "odd": sorted(odd), "odd_rows": sorted(odd_rows), "lift": lift,
            "live": [s for s in stops if s[0] >= lift]}


def verdict(ls_remote_text, rc=0, families=("filing",)):
    """(halted, why) from one ls-remote snapshot (rc = its exit code; text None = unreadable)."""
    if rc or ls_remote_text is None:
        return True, "refs unreadable (fail closed)"
    for f in families:
        s = family_state(ls_remote_text, f)
        sp, lps = FAMILIES[f]
        if s["odd"]:
            return True, f"{s['odd'][0]}: stop ref name not plain digits (halted until deleted)"
        if s["live"]:
            return True, f"{sp}/{s['live'][0][0]} >= {lps[0]}/{s['lift'] or '-'} (newest stop not below newest lifter)"
    return False, ""


def next_ref_epoch(now, stop_epochs, go_epochs):
    """Ref number for a new stop or go: max(now, every existing stop + 1, every existing go + 1), over the refs read
    right before the push. A new ref is then greater than every ref that existed when it was written."""
    return max([int(now)] + [int(e) + 1 for e in stop_epochs] + [int(e) + 1 for e in go_epochs])


def closer_verdict(beat_msg, now, max_age=120):
    """16.1 for the closer (Lead 07:53): (halted, why) from the commit message of toolkit ref status/dupclose
    (`dupclose <epoch> loop=<s>|loop=STUCK<s> ...`). Unreadable, older than max_age, or loop=STUCK -> halted for
    creates (a blind closer cannot close our duplicates). The age compares the beat's epoch with the reader's clock:
    the only clock compare allowed here, a liveness age, never an order between refs."""
    m = re.match(r"dupclose (\d+)\b", beat_msg or "")
    if not m:
        return True, "closer beat unreadable"
    age = now - int(m.group(1))
    if age > max_age:
        return True, f"closer beat {int(age)}s old"
    st = re.search(r"\bloop=STUCK(\d+)", beat_msg)
    if st:
        return True, f"closer loop stuck {st.group(1)}s"
    return False, ""


def selftest():
    L = lambda *names: "".join(f"{i:040x}\trefs/heads/{n}\n" for i, n in enumerate(names, 1))
    cases = [
        ("no refs", L(), 0, False),
        ("stop only", L("filing/stop/100"), 0, True),
        ("go newer", L("filing/stop/100", "filing/go/101"), 0, False),
        ("R6 tie from one snapshot", L("filing/stop/100", "filing/go/100"), 0, True),
        ("stop newer", L("filing/go/100", "filing/stop/101"), 0, True),
        ("old rule live refs 06:16", L("filing/stop/1795756420", "filing/go/1795756649"), 0, False),
        ("odd <n>-blind", L("filing/stop/1795756420-blind", "filing/go/1795756649"), 0, True),
        ("odd word", L("filing/stop/now"), 0, True),
        ("odd nested", L("filing/stop/x/100", "filing/go/999"), 0, True),
        ("odd bare prefix", L("filing/stop"), 0, True),
        ("odd unicode digits", L("filing/stop/١٢"), 0, True),
        ("odd go lifts nothing", L("filing/stop/100", "filing/go/999-x"), 0, True),
        ("unreadable", L("filing/go/100"), 128, True),
        ("unreadable None", None, 0, True),
        ("other prefix ignored", L("filing/stopper/1", "filingx/stop/9"), 0, False),
        ("leading zero", L("filing/stop/0100", "filing/go/101"), 0, False),
    ]
    bad = [n for n, t, rc, want in cases if verdict(t, rc)[0] != want]
    dg = [("dg open lifts", L("deskgate/stop/100", "deskgate/open/101"), False),
          ("dg tie open", L("deskgate/stop/100", "deskgate/open/100"), True),
          ("dg go lifts", L("deskgate/stop/100", "deskgate/go/150"), False),
          ("dg odd", L("deskgate/stop/now", "deskgate/open/999"), True),
          ("dg filing stop counts", L("deskgate/open/999", "filing/stop/5"), True)]
    bad += [n for n, t, want in dg if verdict(t, 0, ("deskgate", "filing"))[0] != want]
    s = family_state(L("filing/stop/100", "filing/stop/90", "filing/go/95"))
    if [e for e, _ in s["live"]] != [100]:
        bad.append("live set")
    cv = [(None, 1000, True), ("dupclose 990 loop=3 step=x", 1000, False), ("dupclose 800 loop=3", 1000, True),
          ("dupclose 990 loop=STUCK200 in=200s", 1000, True), ("garbage", 1000, True), ("dupclose 990 open=1", 1000, False)]
    bad += [f"closer {m!r}" for m, now, want in cv if closer_verdict(m, now)[0] != want]
    if next_ref_epoch(50, [100], [100]) != 101 or next_ref_epoch(200, [100], [150]) != 200:
        bad.append("next_ref_epoch")
    return bad


if __name__ == "__main__":
    import hashlib, sys
    b = selftest()
    sha = hashlib.sha256(open(__file__, "rb").read()).hexdigest()[:16]
    print(("HALTRULE OK " if not b else f"HALTRULE FAIL {b} ") + sha)
    sys.exit(1 if b else 0)
