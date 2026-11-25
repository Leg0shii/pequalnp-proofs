#!/usr/bin/env python3
"""Publishes which posted steps already have a PR (from anyone), from the GitHub search API.
gaps.json `pr_numbers` lags by many minutes during a wave, so generators that trust it produce late duplicates.
Writes every ~20 s:
  team/lead/taken.txt   one line per step: L-meta-N <first PR number> <author> <created HH:MM:SS>   (line 1: '# updated <epoch> <UTC>')
Readers: treat a step as taken if its id is in the file; ignore the file if 'updated' is older than 120 s.
Run: python3 takenpub.py [HOURS_BACK=3]"""
import json, subprocess, time, re, sys, os, calendar
OUT = os.environ.get("TAKEN_OUT", "/mnt/project-files/team/lead/taken.txt")
TOKEN = os.environ.get("GH_SEARCH_TOKEN", "")   # 30 searches/min with a token, 10 without
END = time.time() + float(os.environ.get("TAKEN_MINUTES", "0") or 0) * 60   # 0 = forever
back = float(sys.argv[1]) if len(sys.argv) > 1 else 3
first = {}   # sid -> (number, author, created)
def q(since, pg):
    r = subprocess.run(["curl", "-sS", "-m", "25"] + (["-H", "Authorization: Bearer " + TOKEN] if TOKEN else []) + ["https://api.github.com/search/issues?q=repo:open-goat/pequalnp-proofs+is:pr+created:>"
                        + since + f"&per_page=100&sort=created&order=asc&page={pg}"], capture_output=True, text=True)
    try: return json.loads(r.stdout)
    except Exception: return {}
def pull(since_epoch):
    """returns (items seen, newest created epoch, hit the 1000-result cap) or None on API failure"""
    since = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(since_epoch)); n = 0; pg = 1; last = since_epoch
    while pg <= 10:
        d = q(since, pg); items = d.get("items")
        if items is None: return None
        for i in items:
            n += 1
            last = max(last, calendar.timegm(time.strptime(i["created_at"], "%Y-%m-%dT%H:%M:%SZ")))
            m = re.search(r"L[-_]meta[-_](\d+)", i.get("title") or "")
            if not m: continue
            s = "L-meta-" + m.group(1)
            if s not in first or i["number"] < first[s][0]:
                first[s] = (i["number"], i["user"]["login"], i["created_at"][11:19])
        if len(items) < 100: return n, last, False
        pg += 1; time.sleep(2.2)
    return n, last, True
def write():
    tmp = OUT + ".tmp"
    with open(tmp, "w") as f:
        f.write(f"# updated {int(time.time())} {time.strftime('%H:%M:%S', time.gmtime())} steps {len(first)}\n")
        for s in sorted(first, key=lambda s: int(s[7:])):
            f.write(f"{s} {first[s][0]} {first[s][1]} {first[s][2]}\n")
    os.replace(tmp, OUT)
t = time.time() - back * 3600
while True:   # backfill; the search API returns at most 1000 results per query
    r = pull(t)
    if r is None: time.sleep(20); continue
    if not r[2]: break
    t = r[1] - 2; time.sleep(2.2)
write(); print("backfill", len(first), flush=True)
while not (os.environ.get("TAKEN_MINUTES") and time.time() > END):
    r = pull(time.time() - 300)
    if r is not None: write()
    else: print(time.strftime('%H:%M:%S', time.gmtime()), "api fail", flush=True)
    time.sleep(18)
