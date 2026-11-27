#!/usr/bin/env python3
"""haltrule.py: HARDENING rule 16.1, the one filing halt rule (27 Nov). Used by submit.py filing_halted() and drain.py
halted(), so the opener and the drain can never disagree.

    halted, why = haltrule.decide(ls_remote_text, readable)

Input: the text of `git ls-remote <toolkit> refs/heads/filing/*` and whether that read worked.
  - unreadable                                   -> halted (fail closed)
  - a filing/stop/<name> whose name is not plain digits -> halted (a stop is never ignored)
  - a filing/go/<name> whose name is not plain digits   -> ignored (a go never counts unless it is exact)
  - newest stop >= newest go (a tie is halted)   -> halted
  - no stop ref at all                           -> not halted
There is no clock compare: the names are compared with each other only.
Selftest: python3 haltrule.py selftest"""
import re, sys

REF = re.compile(r"refs/heads/filing/(stop|go)/(\S+)\s*$")


def decide(txt, readable=True):
    if not readable:
        return True, "filing refs unreadable (fail closed)"
    stops, gos = [], []
    for line in (txt or "").splitlines():
        m = REF.search(line)
        if not m:
            continue
        kind, name = m.groups()
        if kind == "stop":
            if not name.isdigit() or not name.isascii():
                return True, f"filing halted: stop ref filing/stop/{name[:40]} is not plain digits (rule 16.1)"
            stops.append(int(name))
        elif name.isdigit() and name.isascii():
            gos.append(int(name))
    if not stops:
        return False, ""
    st, go = max(stops), max(gos) if gos else None
    if go is None or st >= go:
        return True, f"filing halted: filing/stop/{st} " + ("with no go" if go is None else
                                                            ("equal to" if st == go else "newer than") + f" filing/go/{go}")
    return False, ""


def selftest():
    r = lambda *names: "".join(f"0123\trefs/heads/filing/{n}\n" for n in names)
    cases = [
        ("unreadable", ("", False), True),
        ("no refs", (r(), True), False),
        ("only go", (r("go/100"), True), False),
        ("stop newer", (r("stop/200", "go/100"), True), True),
        ("go newer", (r("stop/100", "go/200"), True), False),
        ("tie is halted", (r("stop/200", "go/200"), True), True),
        ("stop with no go", (r("stop/100"), True), True),
        ("non-digit stop halts even under a newer go", (r("stop/100", "stop/now", "go/999"), True), True),
        ("non-digit go ignored", (r("stop/100", "go/100x", "go/next"), True), True),
        ("non-digit go ignored, digit go newer", (r("stop/100", "go/zz", "go/101"), True), False),
        ("nested stop name halts", (r("stop/100/a", "go/200"), True), True),
        ("unicode digits are not plain digits", (r("stop/١٢", "go/200"), True), True),
        ("other refs ignored", ("0\trefs/heads/filing/x\n0\trefs/heads/main\n", True), False),
    ]
    bad = 0
    for name, args, exp in cases:
        got = decide(*args)[0]
        print(("ok   " if got == exp else "FAIL ") + f"16.1 {name}: halted={got}")
        bad += got != exp
    print("HALTRULE SELFTEST " + ("OK" if not bad else f"FAIL {bad}"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(selftest() if sys.argv[1:] == ["selftest"] else 2)
