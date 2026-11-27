#!/usr/bin/env python3
"""runtoken_test.py [dir of takenpub.py]: takenpub on an empty run token (Lead 09:38, RC-b). In-process, faked GitHub.
  R1 run token refused for its PRIMARY limit (403, remaining 0): the same read again with PR_TOKEN, rows returned,
     RUN-TOKEN-EMPTY logged; the next reads go to PR_TOKEN without touching the run token
  R2 after the run token's reset: back to the run token
  R3 run token answers 200 with remaining under 200: this answer is used, the next read goes to PR_TOKEN
  R4 SECONDARY limit 403 on the run token: no fallback, the read fails closed (ReadFail)
  R5 PR_TOKEN under its floor (1000 remaining): no more PR_TOKEN reads, fail closed
  R6 RUN-TOKEN-EMPTY logged at most once per 5 min over many refusals
  R7 RUNTOKEN_FALLBACK=0: the refused read fails closed, PR_TOKEN never used
Prints one line per case and "RUNTOKEN PASS <sha>" or "RUNTOKEN FAIL <sha>: <cases>". Exit 0 iff PASS."""
import io, os, subprocess, sys, time, contextlib

SRC = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
os.environ.update(PR_TOKEN="pr-drill", GH_SEARCH_TOKEN="run-drill", TAKEN_OUT=os.devnull)
sys.path.insert(0, SRC)
import takenpub as T


class Fake:
    def __init__(self, run_answers, pr_rem=4000):
        self.run = list(run_answers)       # per run-token call: (code, rem, reset, body)
        self.calls = []
        self.pr_rem = pr_rem

    def tok_cond(self, path, etag, tok):
        self.calls.append(tok)
        if tok == "pr":
            self.pr_rem -= 1
            return 200, [{"number": 1}], None, self.pr_rem, int(time.time()) + 3000
        code, rem, reset, body = self.run.pop(0) if self.run else (200, 4000, int(time.time()) + 3000, "")
        return code, (body if code != 200 else [{"number": 1}]), None, rem, reset


def fresh(fake):
    T.FAKE = fake; T.FAKE_DATE = None; T.ETAGS.clear()
    T.FB.update(until=0.0, alert=0.0, pr_rem=None, n=0)
    os.environ.pop("RUNTOKEN_FALLBACK", None)


def call():
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        try:
            r, e = T.api("repos/x/y/pulls?state=open&page=1"), None
        except T.ReadFail as ex:
            r, e = None, ex
    return r, e, out.getvalue()


def main():
    sha = subprocess.run(["git", "-C", SRC, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    fails = []
    now = int(time.time())
    if not hasattr(T, "FB"):                # code without the fallback: every refused read fails closed
        print(f"RUNTOKEN FAIL {sha}: R1 R2 R3 R5 R6 (no run-token fallback in takenpub.py)")
        return 1

    def case(k, ok, info):
        print(("ok   " if ok else "FAIL ") + k + " | " + info[:200])
        if not ok:
            fails.append(k)

    f = Fake([(403, 0, now + 30, '{"message":"API rate limit exceeded for installation"}')]); fresh(f)
    r1, e1, o1 = call(); r2, e2, o2 = call()
    case("R1", r1 and e1 is None and f.calls == ["run", "pr", "pr"] and "RUN-TOKEN-EMPTY" in o1 and r2,
         f"calls={f.calls} err={e1} log={o1.strip()[:80]}")
    T.FB["until"] = time.time() - 1
    f.calls.clear(); r3, e3, _ = call()
    case("R2", r3 and f.calls == ["run"], f"calls={f.calls}")
    f = Fake([(200, 150, now + 900, "")]); fresh(f)
    r1, e1, o1 = call(); r2, _, _ = call()
    case("R3", r1 and r2 and f.calls == ["run", "pr"] and "RUN-TOKEN-EMPTY" in o1, f"calls={f.calls}")
    f = Fake([(403, 3000, now + 900, '{"message":"You have exceeded a secondary rate limit"}')]); fresh(f)
    r1, e1, _ = call()
    case("R4", r1 is None and isinstance(e1, T.ReadFail) and f.calls == ["run"], f"calls={f.calls} err={e1}")
    f = Fake([(403, 0, now + 900, '{"message":"API rate limit exceeded"}')] * 3, pr_rem=1000); fresh(f)
    r1, e1, _ = call(); r2, e2, _ = call()
    case("R5", r1 and r2 is None and isinstance(e2, T.ReadFail) and f.calls == ["run", "pr", "run"],
         f"calls={f.calls} err2={e2} pr_rem={T.FB['pr_rem']}")
    f = Fake([(403, 0, now + 1, '{"message":"API rate limit exceeded"}')] * 10); fresh(f)
    logs = ""
    for _ in range(10):
        T.FB["until"] = 0.0                # force the run token every time (as after each reset)
        logs += call()[2]
    case("R6", logs.count("RUN-TOKEN-EMPTY") == 1, f"alerts={logs.count('RUN-TOKEN-EMPTY')}")
    f = Fake([(403, 0, now + 900, '{"message":"API rate limit exceeded"}')]); fresh(f)
    os.environ["RUNTOKEN_FALLBACK"] = "0"
    r1, e1, _ = call()
    case("R7", r1 is None and isinstance(e1, T.ReadFail) and f.calls == ["run"], f"calls={f.calls}")
    os.environ.pop("RUNTOKEN_FALLBACK", None)
    print(f"RUNTOKEN PASS {sha}" if not fails else f"RUNTOKEN FAIL {sha}: " + " ".join(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
