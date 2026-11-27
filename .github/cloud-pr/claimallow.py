"""claimallow.py: the live claim list (lane leases L1, Lead 10:17/10:33 UTC 27 Nov; format red team SIGNABLE 10:32, W5 10:30).

Toolkit refs refs/heads/claimallow/<n>, create-only, written by the PC on the Lead's signed order. The writer numbers a
new ref with haltrule.next_ref_epoch over the refs it just read, so every new ref (an "off" too) is above every ref
that existed. The newest ref is the HIGHEST NUMBER, never a clock compare. Its commit message (exact text, no trailer):
    CLAIM-ALLOW v1 off
    CLAIM-ALLOW v1 <id>,<id> ...      (comma or whitespace separated, same line or the lines below, at most MAX_IDS)
Anything else = odd = no claim (fail closed). Revoke = push "off", never delete.

Readers: ONE per drain (drain.py claimlist thread, 16.14 pattern) writes W/claim-allow.json every EVERY_S; submit.py
only reads that file (no read and no wait per unit). The verdict:
  - no ref at all = no list (claims off), ok
  - newest number below the highest number this reader has seen = a ref was deleted = off until a new ref above it (N4)
  - commit time older than TTL_S (2 h) = off; commit time over 300 s in the future = off (liveness only, N3/W5)
  - a failed read (ls-remote, fetch, log) = ok false and the LAST GOOD ids are kept (N1): a listed id then makes no
    claim and no bare PR (error, retried); every other unit files first
"""
import json, os, re, time

PREFIX = "refs/heads/claimallow/"
EVERY_S = float(os.environ.get("CLAIM_LIST_EVERY_S", "10"))
STALE_S = 30            # submit.py: a copy older than this = not confirmed (ok false, last good ids kept)
TTL_S = 7200            # W5 10:30: a list older than 2 h (commit time) = off
FUTURE_S = 300
MAX_IDS = 2000
UNIT = re.compile(r"L-[a-z0-9]+(?:-[a-z0-9]+)*-\d+")
FILE = "claim-allow.json"


def newest(ls_text):
    """(sha, n) of the highest refs/heads/claimallow/<n> in ls-remote output, or None. Pure."""
    best = None
    for m in re.finditer(r"^([0-9a-f]{40})\trefs/heads/claimallow/(\d+)$", ls_text or "", re.M):
        if best is None or int(m.group(2)) > best[1]:
            best = (m.group(1), int(m.group(2)))
    return best


def parse(msg):
    """(ids, why) from a list commit message. Pure. Odd = empty set."""
    lines = (msg or "").strip().split("\n")
    head = lines[0].split() if lines else []
    if head[:2] != ["CLAIM-ALLOW", "v1"]:
        return set(), "odd claimallow message (no CLAIM-ALLOW v1 header): off"
    if head[2:] == ["off"] and not "".join(lines[1:]).strip():
        return set(), "claim list off"
    toks = [t for t in re.split(r"[\s,]+", " ".join(head[2:] + lines[1:])) if t]
    bad = [t for t in toks if not UNIT.fullmatch(t)]
    if bad or not toks or len(toks) > MAX_IDS:
        return set(), f"odd claimallow list ({len(toks)} ids, bad {bad[:3]}): off"
    return set(toks), f"claim list {len(toks)} ids"


def verdict(ls_text, read_commit, now, hw):
    """(ok, ids, why, n, hw). ls_text None = ls-remote failed. read_commit(sha, n) -> (message, commit epoch) or raises.
    hw = the highest ref number this reader has seen (0 at start)."""
    if ls_text is None:
        return False, set(), "claimallow refs unreadable", None, hw
    nb = newest(ls_text)
    if nb is None:
        return True, set(), ("all claimallow refs gone (deleted): off" if hw else "no claimallow ref: no list"), None, hw
    sha, n = nb
    if n < hw:
        return True, set(), f"newest claimallow/{n} below the highest seen {hw} (a ref was deleted): off", n, hw
    hw = n
    try:
        msg, ct = read_commit(sha, n)
    except Exception as e:
        return False, set(), f"claimallow/{n} unreadable ({str(e)[:60]})", n, hw
    age = now - ct
    if age > TTL_S:
        return True, set(), f"claimallow/{n} is {age:.0f} s old (over {TTL_S} s): off", n, hw
    if age < -FUTURE_S:
        return True, set(), f"claimallow/{n} commit time {-age:.0f} s in the future: off", n, hw
    ids, why = parse(msg)
    return True, ids, f"{why} (claimallow/{n})", n, hw


class Reader:
    """one per drain. ls() -> ls-remote text or None; fetch(n) -> True if refs/heads/claimallow/<n> is now in the
    local repo as refs/claim-allow; show() -> (sha, commit epoch, message) of refs/claim-allow or raises."""

    def __init__(self, d, ls, fetch, show):
        self.d, self.ls, self.fetch, self.show = d, ls, fetch, show
        self.hw, self.last_good, self.cache, self.reads = 0, [], {}, 0

    def _commit(self, sha, n):
        if sha in self.cache:                       # a list is fetched once per new ref, not every pass
            return self.cache[sha]
        if not self.fetch(n):
            raise RuntimeError("fetch failed")
        got, ct, msg = self.show()
        if got != sha:
            raise RuntimeError("ref moved during the read")
        self.cache[sha] = (msg, ct)
        return self.cache[sha]

    def refresh(self, now=None):
        now = time.time() if now is None else now
        self.reads += 1
        try:
            ls = self.ls()
        except Exception:
            ls = None
        ok, ids, why, n, self.hw = verdict(ls, self._commit, now, self.hw)
        if ok:
            self.last_good = sorted(ids)
        c = {"t": now, "ok": ok, "ids": sorted(ids) if ok else self.last_good, "why": why, "n": n, "hw": self.hw}
        tmp = os.path.join(self.d, FILE + ".tmp")
        with open(tmp, "w") as o:
            json.dump(c, o)
        os.replace(tmp, os.path.join(self.d, FILE))
        return c


def read_copy(d, now=None):
    """submit.py side: (ids, ok, why) from d/claim-allow.json. No file = no reader = no list (ids empty, ok).
    Stale (over STALE_S) or unparsable = ok false with the ids it holds (the last good list)."""
    now = time.time() if now is None else now
    f = os.path.join(d, FILE)
    if not os.path.exists(f):
        return set(), True, "no claim list copy (no drain reader): no list"
    try:
        c = json.load(open(f))
        ids = set(c.get("ids") or [])
    except Exception as e:
        return set(), False, f"claim list copy unreadable ({str(e)[:40]})"
    age = now - float(c.get("t") or 0)
    if not 0 <= age <= STALE_S:
        return ids, False, f"claim list copy {age:.0f} s old (reader dead?)"
    return ids, bool(c.get("ok")), str(c.get("why") or "")
