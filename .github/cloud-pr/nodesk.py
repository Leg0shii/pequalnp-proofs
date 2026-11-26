#!/usr/bin/env python3
"""nodesk.py: GATEWAY v1 section 3 (Lead 16:50 UTC 26 Nov): fail (exit 1) if any tracked file of ours under .github/
names the desk host or builds a desk action path. deskgate.py on the PC (pnp-toolkit) is the only desk caller; the
fork opener asks it through toolkit refs gatereq/<id> -> lease/<id>. The data mirror (data.pequalnp.com) is fine.
Upstream's own files (tools/, lean/) are not ours and are not scanned."""
import re, subprocess, sys

HOST = re.compile(r"https?://(www\.)?pequalnp\.com(?![\w.-])|(?<![\w.-])(www\.)?pequalnp\.com/desk")
ACT = re.compile(r"[\"'](next\?[^\"']*have=|release\?lease=|beat\?lease=|submit\?)")
files = subprocess.run(["git", "ls-files", ".github"], capture_output=True, text=True, check=True).stdout.split()
bad = []
for f in files:
    try:
        txt = open(f, errors="replace").read()
    except OSError:
        continue
    for i, line in enumerate(txt.splitlines(), 1):
        if HOST.search(line) or ACT.search(line):
            bad.append(f"{f}:{i}: {line.strip()[:120]}")
print(f"nodesk: {len(files)} files under .github, {len(bad)} desk-host finding(s)")
for b in bad:
    print("  DESK", b)
sys.exit(1 if bad else 0)
