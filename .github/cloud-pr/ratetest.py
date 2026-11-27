#!/usr/bin/env python3
"""CANARY R (Lead 07:23 / 07:24 UTC 27 Nov): the real PR-create rate ceiling of the PR_TOKEN account, measured INSIDE
the fork only (never upstream). A ramp of 30 s steps at 20, 30, 45, 60, 70 creates a minute (capped at MAX_RATE, at
most 115 creates), every create through submit.py's own pr_gate (PR_GATE_N=8 slots) and bucket (PR_PER_MIN=70).
The FIRST 403 or 429 (or "submitted too quickly" / "secondary rate limit") stops the ramp: no retry, no new create.
Heads ratetest/h-NNN and base ratetest/base are parentless scratch commits (no workflows in them, so no pull_request
run). Titles "rate test n", no unit id, no LinkedIn line. Then every PR is closed at 20 a minute and the branches are
deleted in one push.

  python3 ratetest.py ramp      creates (needs PR_TOKEN, FORK, the branches pushed); writes $W/ratetest.json
  python3 ratetest.py cleanup   closes every open PR on base ratetest/base, 3 s apart
  python3 ratetest.py report    the summary lines from $W/ratetest.json
  python3 ratetest.py selftest  the ramp against a fake create (no network)
"""
import json, os, re, subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
W = os.environ.setdefault("W", tempfile.mkdtemp())
GATE = os.path.join(W, "rtgate")
os.makedirs(GATE, exist_ok=True)
for k, v in {"ID": "rate-test", "MOD": "rate_test", "PROOF": os.devnull, "TREE": W, "PR_GATE_DIR": GATE,
             "PR_GATE_N": "8", "PR_PER_MIN": "70", "PR_PER_HOUR": "480"}.items():
    os.environ.setdefault(k, v)
sys.path.insert(0, HERE)
import submit as S                                  # noqa: E402  the opener's own pr_gate and bucket

FORK = os.environ.get("FORK") or os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
assert FORK.lower() != "open-goat/pequalnp-proofs", "never upstream"
BASE = "ratetest/base"
STEPS = [20, 30, 45, 60, 70]
STEP_S = 30.0
MAX_CREATES = 115
MAX_RATE = int(os.environ.get("MAX_RATE", "70"))
OUT = os.path.join(W, "ratetest.json")
HDRS = ("retry-after", "x-ratelimit-limit", "x-ratelimit-remaining", "x-ratelimit-used", "x-ratelimit-reset",
        "x-ratelimit-resource")
REFUSED = re.compile(r"secondary rate limit|submitted too quickly|abuse", re.I)


def plan(max_rate=MAX_RATE):
    """[(t_offset, n)]: each step's creates evenly spaced, rates above max_rate dropped, at most MAX_CREATES"""
    out, t0, n = [], 0.0, 0
    for r in [x for x in STEPS if x <= max_rate] or [max_rate]:
        k = int(round(r * STEP_S / 60))
        for i in range(k):
            if n < MAX_CREATES:
                n += 1
                out.append((t0 + i * STEP_S / k, n))
        t0 += STEP_S
    return out


def gh_api(args, token):
    """(http code, headers dict, body text, latency s) for `gh api -i`"""
    t = time.time()
    r = subprocess.run(["gh", "api", "-i"] + args, capture_output=True, text=True, timeout=120,
                       env=dict(os.environ, GH_TOKEN=token))
    lat = time.time() - t
    txt = r.stdout or ""
    head, _, body = txt.replace("\r\n", "\n").partition("\n\n")
    m = re.match(r"HTTP/\S+ (\d+)", head)
    code = int(m.group(1)) if m else 0
    h = {}
    for ln in head.split("\n")[1:]:
        k, _, v = ln.partition(":")
        if k.strip().lower() in HDRS:
            h[k.strip().lower()] = v.strip()
    return code, h, body + (r.stderr or ""), lat


def real_create(n):
    code, h, body, lat = gh_api(["-X", "POST", f"repos/{FORK}/pulls", "-f", f"title=rate test {n}",
                                 "-f", f"head=ratetest/h-{n:03d}", "-f", f"base={BASE}",
                                 "-f", "body=Canary R: create-rate test inside the fork. Closed within minutes."],
                                S.PR_TOKEN)
    num = None
    try:
        num = json.loads(body.split("\n{", 1)[-1] if not body.lstrip().startswith("{") else body).get("number")
    except Exception:
        pass
    return code, h, body[:300], lat, num


def ramp(create=real_create, max_rate=MAX_RATE, clock=time.time, sleep=time.sleep):
    """runs the plan with 8 threads; returns the list of per-create records"""
    p, recs, lock, stop, nxt = plan(max_rate), [], threading.Lock(), threading.Event(), [0]
    t0 = clock() + 1.0

    def worker():
        while not stop.is_set():
            with lock:
                if nxt[0] >= len(p):
                    return
                off, n = p[nxt[0]]; nxt[0] += 1
            w = t0 + off - clock()
            if w > 0:
                sleep(w)
            if stop.is_set():
                return
            with S.pr_gate():
                if stop.is_set():
                    return
                ts = clock()
                code, h, body, lat, num = create(n)
            rec = {"n": n, "t": round(ts - t0, 3), "planned": round(off, 3), "code": code, "lat": round(lat, 3),
                   "hdr": h, "num": num}
            if code in (403, 429) or (code not in (200, 201) and REFUSED.search(body or "")):
                rec["body"] = (body or "")[:300]
                stop.set()                       # the FIRST refusal stops everything: no retry, no new create
            elif code not in (200, 201):
                rec["body"] = (body or "")[:300]
            with lock:
                recs.append(rec)
                print(f"RT create n={n} t={rec['t']:.2f} code={code} lat={lat:.2f} "
                      f"rem={h.get('x-ratelimit-remaining', '')} ra={h.get('retry-after', '')} pr={num}", flush=True)

    th = [threading.Thread(target=worker) for _ in range(int(os.environ["PR_GATE_N"]))]
    [x.start() for x in th]
    [x.join() for x in th]
    return sorted(recs, key=lambda r: r["t"])


def summary(recs):
    ok = sorted(r["t"] for r in recs if r["code"] in (200, 201))
    best = max([sum(1 for u in ok if t <= u < t + 60) for t in ok] or [0])
    lat = sorted(r["lat"] for r in recs if r["code"] in (200, 201))
    pct = lambda q: lat[min(len(lat) - 1, int(q * len(lat)))] if lat else float("nan")
    ref = next((r for r in recs if r["code"] not in (200, 201)), None)
    return {"creates": len(recs), "accepted": len(ok), "best60": best, "p50": pct(.5), "p95": pct(.95),
            "first_refusal": ref}


def cleanup():
    """close every open PR on base ratetest/base, 20 a minute (a 403/429 on a close waits its retry-after, then
    goes on: the closes must finish)"""
    code, h, body, lat = gh_api(["--paginate", f"repos/{FORK}/pulls?state=open&base={BASE}&per_page=100",
                                 "--jq", ".[].number"], S.PR_TOKEN)
    nums = [int(x) for x in re.findall(r"^\d+$", body, re.M)]
    print(f"RT cleanup {len(nums)} open PRs on {BASE} (list http {code})", flush=True)
    for n in nums:
        for _ in range(5):
            c, hh, b, _l = gh_api(["-X", "PATCH", f"repos/{FORK}/pulls/{n}", "-f", "state=closed"], S.PR_TOKEN)
            if c not in (403, 429):
                break
            wait = float(hh.get("retry-after") or 60)
            print(f"RT close {n} http {c}: waiting {wait:.0f} s", flush=True)
            time.sleep(wait)
        print(f"RT close {n} http {c}", flush=True)
        time.sleep(3.0)


def report():
    d = json.load(open(OUT))
    s = summary(d["recs"])
    print(f"CANARY-R max_rate={d['max_rate']} creates={s['creates']} accepted={s['accepted']} "
          f"best60={s['best60']} latency p50={s['p50']:.2f}s p95={s['p95']:.2f}s")
    rates = [x for x in STEPS if x <= d["max_rate"]] or [d["max_rate"]]
    per = {}
    for r in d["recs"]:
        k = rates[min(len(rates) - 1, int(r["planned"] // STEP_S))]
        a = per.setdefault(k, [0, 0]); a[0] += 1; a[1] += r["code"] in (200, 201)
    print("CANARY-R per step (rate/min: tried/accepted): " + ", ".join(f"{k}: {v[0]}/{v[1]}" for k, v in per.items()))
    f = s["first_refusal"]
    print("CANARY-R first refusal: " + ("none" if not f else
          f"n={f['n']} t={f['t']:.1f}s code={f['code']} hdr={json.dumps(f['hdr'])} body={f.get('body', '')[:160]!r}"))


def selftest():
    import random
    clk = [1000.0]
    lk = threading.Lock()

    def fclock():
        with lk:
            return clk[0]

    def fsleep(s):
        with lk:
            clk[0] += max(s, 0.001)

    real, real_sleep = S.time.time, S.time.sleep
    S.time.time = fclock                 # pr_gate/bucket_wait read time.time(): the fake clock
    S.time.sleep = fsleep
    try:
        assert len(plan(70)) == 112 and len(plan(45)) == 47 and len(plan(20)) == 10, (len(plan(70)), len(plan(45)))
        assert max(n for _, n in plan(500)) <= MAX_CREATES
        for f in os.listdir(GATE):
            os.remove(os.path.join(GATE, f))
        recs = ramp(lambda n: (201, {"x-ratelimit-remaining": "4999"}, "", 0.5 + random.random(), n),
                    70, fclock, fsleep)
        assert len(recs) == 112 and all(r["code"] == 201 for r in recs), len(recs)
        s = summary(recs)
        bl = sorted(float(x) for x in open(os.path.join(GATE, "creates.log")).read().split())
        b60 = max(sum(1 for u in bl if t <= u < t + 60) for t in bl)
        assert len(bl) == 112 and 60 <= b60 <= 70, (len(bl), b60, s)   # the bucket: any 60 s at most 70 creates
        for f in os.listdir(GATE):
            os.remove(os.path.join(GATE, f))
        seen = []

        def refuse(n):
            seen.append(n)
            return (403, {"retry-after": "60"}, "You have exceeded a secondary rate limit", 0.4, None) if n == 30 \
                else (201, {}, "", 0.4, n)
        recs = ramp(refuse, 70, fclock, fsleep)
        assert recs and any(r["code"] == 403 for r in recs)
        late = [n for n in seen if n > 30 + 8]                  # at most the 8 already in their slots go on
        assert not late, late
        assert summary(recs)["first_refusal"]["code"] == 403
    finally:
        S.time.time, S.time.sleep = real, real_sleep
    print("RATETEST SELFTEST OK")


if __name__ == "__main__":
    a = sys.argv[1] if len(sys.argv) > 1 else ""
    if a == "ramp":
        recs = ramp()
        json.dump({"max_rate": MAX_RATE, "recs": recs}, open(OUT, "w"))
        report()
    elif a == "cleanup":
        cleanup()
    elif a == "report":
        report()
    elif a == "selftest":
        selftest()
    else:
        sys.exit(__doc__)
