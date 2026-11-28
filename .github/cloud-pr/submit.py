"""ONE-OFF (owner's ask, Lead thread 28 Nov 10:14 UTC): close the listed old open pull requests of our own handle.
Runs in the cloud-pr submit job in place of the opener. Dry run by default: only lists them."""
import json, os, subprocess, sys
UP = "open-goat/pequalnp-proofs"
NUMS = [47823,47820,47818,47808,47806,47805,47800,47792,47788,47779,47776,47774,47763,47756,46463,44652]
KEEP = {54752}
DRY = os.environ.get("DRY", "1") == "1"
env = dict(os.environ, GH_TOKEN=os.environ["PR_TOKEN"])
bad = 0
for n in NUMS:
    if n in KEEP:
        continue
    r = subprocess.run(["gh", "pr", "view", str(n), "--repo", UP, "--json", "number,state,author,title"],
                       capture_output=True, text=True, env=env, timeout=60)
    if r.returncode:
        print(n, "view failed:", r.stderr.strip()[:150], flush=True); bad += 1; continue
    p = json.loads(r.stdout)
    if (p.get("author") or {}).get("login") != "Leg0shii":
        print(n, "not ours, skipped", flush=True); bad += 1; continue
    if p.get("state") != "OPEN":
        print(n, p.get("title"), "already", p.get("state"), flush=True); continue
    if DRY:
        print(n, p.get("title"), "OPEN: would close", flush=True); continue
    c = subprocess.run(["gh", "pr", "close", str(n), "--repo", UP], capture_output=True, text=True, env=env, timeout=60)
    print(n, p.get("title"), "closed" if c.returncode == 0 else "CLOSE FAILED: " + c.stderr.strip()[:150], flush=True)
    bad += c.returncode != 0
print("done, problems:", bad, "dry" if DRY else "live", flush=True)
sys.exit(1 if bad else 0)
