#!/usr/bin/env python3
"""ghcond.py: conditional GitHub REST reads (HARDENING 16.7, 27 Nov). One helper for takenpub, the closer and openers.

    import ghcond
    data, counted, remaining = ghcond.get("repos/o/r/pulls?state=open&per_page=100&page=1")

Sends If-None-Match with the ETag of the last 200 answer for the same path (cache on disk, shared by every process
that uses the same GHCOND_DIR). A 304 answer returns the cached body and counted=False: GitHub does not count it
against the token's hourly limit. remaining = X-RateLimit-Remaining of that answer (None when absent).
FAIL CLOSED: a non-2xx/304 answer, a 304 without a cached body, or JSON that does not parse raises ReadFail.
Env: GHCOND_DIR (default $RIVAL_SNAP_DIR, else /tmp/ghcond). The gh call is injectable (get(path, gh=fn), fn(args)
-> CompletedProcess) so the drills can fake GitHub; a fake that answers without "-i" headers is taken as a counted 200.
Counters for the drills and the heartbeat: STATS = {"counted", "not_modified", "remaining"}.
Selftest: python3 ghcond.py selftest"""
import hashlib, json, os, re, subprocess, sys, tempfile

STATS = {"counted": 0, "not_modified": 0, "remaining": None}


class ReadFail(RuntimeError):
    pass


def _dir():
    d = os.environ.get("GHCOND_DIR") or os.environ.get("RIVAL_SNAP_DIR") or os.path.join(tempfile.gettempdir(), "ghcond")
    os.makedirs(d, exist_ok=True)
    return d


def _gh(args):
    return subprocess.run(["gh"] + args, capture_output=True, text=True, timeout=60)


def parse(out):
    """`gh api -i` text -> (status, {header lower: value}, body). Text without a status line = (200, {}, text)."""
    if not out.startswith("HTTP/"):
        return 200, {}, out
    head, _, body = out.replace("\r\n", "\n").partition("\n\n")
    lines = head.split("\n")
    m = re.match(r"HTTP/\S+\s+(\d{3})", lines[0])
    hdr = {}
    for l in lines[1:]:
        k, _, v = l.partition(":")
        hdr[k.strip().lower()] = v.strip()
    return (int(m.group(1)) if m else 0), hdr, body


def get(path, gh=None, cache_dir=None):
    gh = gh or _gh
    f = os.path.join(cache_dir or _dir(), "c-" + hashlib.sha1(path.encode()).hexdigest()[:20] + ".json")
    cached = None
    try:
        cached = json.load(open(f))
    except Exception:
        pass
    args = ["api", path, "-i"]
    if cached and cached.get("etag"):
        args += ["-H", "If-None-Match: " + cached["etag"]]
    r = gh(args)
    st, hdr, body = parse(r.stdout or "")
    rem = hdr.get("x-ratelimit-remaining")
    rem = int(rem) if rem and rem.isdigit() else None
    if rem is not None:
        STATS["remaining"] = rem
    if st == 304:
        if not cached or "body" not in cached:
            raise ReadFail(f"304 for {path} without a cached body")
        STATS["not_modified"] += 1
        return cached["body"], False, rem
    if r.returncode or not 200 <= st < 300:
        raise ReadFail(f"{path}: rc={r.returncode} status={st} {(r.stderr or '').strip()[:100]}")
    try:
        data = json.loads(body)
    except ValueError as e:
        raise ReadFail(f"{path}: bad JSON ({e})")
    STATS["counted"] += 1
    if hdr.get("etag"):
        tmp = f + ".%d.tmp" % os.getpid()
        with open(tmp, "w") as o:
            json.dump({"etag": hdr["etag"], "body": data}, o)
        os.replace(tmp, f)
    return data, True, rem


def selftest():
    d = tempfile.mkdtemp()
    page = [{"number": 1}]
    seen = []

    def fake(args):
        seen.append(args)
        etag = 'W/"%s"' % hashlib.sha1(json.dumps(page).encode()).hexdigest()[:8]
        if "-H" in args and args[args.index("-H") + 1] == "If-None-Match: " + etag:
            return subprocess.CompletedProcess(args, 1, "HTTP/2.0 304 Not Modified\nX-Ratelimit-Remaining: 4000\n\n", "gh: HTTP 304")
        return subprocess.CompletedProcess(args, 0, "HTTP/2.0 200 OK\nEtag: %s\nX-Ratelimit-Remaining: 3999\n\n%s"
                                           % (etag, json.dumps(page)), "")
    ok = []
    a = get("p", fake, d); ok.append(("first read counted", a == (page, True, 3999)))
    b = get("p", fake, d); ok.append(("unchanged page: 304, not counted, cached body", b == (page, False, 4000)))
    page.append({"number": 2})
    c = get("p", fake, d); ok.append(("changed page counted with the new body", c[1] and len(c[0]) == 2))
    fail = lambda args: subprocess.CompletedProcess(args, 1, "HTTP/2.0 403 Forbidden\n\n{}", "HTTP 403")
    try:
        get("p", fail, d); ok.append(("403 fails closed", False))
    except ReadFail:
        ok.append(("403 fails closed", True))
    try:
        get("q", lambda a: subprocess.CompletedProcess(a, 1, "HTTP/2.0 304 Not Modified\n\n", ""), d)
        ok.append(("304 without cache fails closed", False))
    except ReadFail:
        ok.append(("304 without cache fails closed", True))
    plain = get("r", lambda a: subprocess.CompletedProcess(a, 0, "[1]", ""), d)
    ok.append(("fake without headers = counted 200", plain == ([1], True, None)))
    for n, v in ok:
        print(("ok   " if v else "FAIL ") + n)
    print("GHCOND SELFTEST " + ("OK" if all(v for _, v in ok) else "FAIL"))
    return 0 if all(v for _, v in ok) else 1


if __name__ == "__main__":
    sys.exit(selftest() if sys.argv[1:] == ["selftest"] else 2)
