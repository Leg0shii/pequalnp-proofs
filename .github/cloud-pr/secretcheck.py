#!/usr/bin/env python3
"""secretcheck (HARDENING 14 W8, BLINDSPOTS B13): every secret the fork scripts read exists, is mapped, and is checked.

  secretcheck.py static [ROOT]   offline, on any box. ROOT = fork checkout (default: this file's checkout). Checks:
      S1 UNMAPPED     a credential env name (TOKEN/SECRET/KEY/PASS/LINKEDIN) that a script run by a step reads (with the
                      scripts it starts) is not set in that step's, job's or workflow's env
      S2 UNCHECKED    a secrets.X or vars.X that some workflow uses is not in the live check list (preflight-live.yml env)
      S3 SILENT-SKIP  a step ends with exit 0 (green run) when a secret env is empty: a missing secret must turn the run red
      S4 NO-SOURCE    an env name is mapped from an expression with no secrets./vars./github.token source and no literal
  secretcheck.py live            inside the Action (preflight-live.yml): every name in SECRETCHECK_NAMES is non-empty unless
                      listed in OPTIONAL; PR_TOKEN answers /rate_limit (free), can push the fork and read the toolkit.
  -> one line per finding, then "SECRETCHECK OK ..." (exit 0) or "SECRETCHECK FAIL ..." (exit 1)
GitHub reads: static 0; live 3 (rate_limit is not counted by GitHub, fork repo read, toolkit ls-remote). Desk 0. Data host 0.
"""
import json, os, re, subprocess, sys, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
CRED = re.compile(r"(_TOKEN|_SECRET|_KEY|_PASS|^PNP_LINKEDIN)$")
# names that may be absent on purpose; each with the code that covers the gap (reviewed by the Lead, one line each)
OPTIONAL = {
    "PNP_LINKEDIN": "credit line falls back to toolkit config/linkedin.txt (drain.py linkedin_file, Lead 05:50)",
}
# names the runner or the workflow itself provides (not secrets)
RUNTIME = {"GITHUB_TOKEN", "ACTIONS_RUNTIME_TOKEN", "ACTIONS_ID_TOKEN_REQUEST_TOKEN"}
ENV_READ = re.compile(r"""(?:environ(?:\.get)?\s*(?:\(|\[)\s*|getenv\(\s*)["']([A-Z][A-Z0-9_]*)["']""")
SHELL_EMPTY_EXIT0 = re.compile(r"""\[\s*-n\s+"\$\{?([A-Z][A-Z0-9_]*)(?::-)?\}?"\s*\]\s*\|\|\s*(\{[^}]*exit 0[^}]*\}|exit 0)""")


def load_yaml(path):
    import yaml
    with open(path) as f:
        d = yaml.safe_load(f)
    return d if isinstance(d, dict) else {}


def script_reads(path, seen=None):
    """credential env names a script reads, following the cloud-pr scripts it runs ("x.py" literal or import x: drain -> submit, utest -> drain);
    a name the parent sets for its children itself (NAME="..." / "NAME": ...) is provided, not read from the step"""
    seen = set() if seen is None else seen
    if path in seen or not os.path.isfile(path):
        return set()
    seen.add(path)
    src = open(path, errors="replace").read()
    names = {n for n in ENV_READ.findall(src) if CRED.search(n)}
    d = os.path.dirname(path)
    for other in sorted(os.listdir(d)):
        if other.endswith(".py") and other != os.path.basename(path) and re.search(r"""(["']%s["']|^\s*import\s+%s\b)""" % (re.escape(other), re.escape(other[:-3])), src, re.M):
            names |= {n for n in script_reads(os.path.join(d, other), seen)
                      if not re.search(r"""(\b%s\s*=\s*["']|["']%s["']\s*:)""" % (n, n), src)}
    return names


def scripts_of(run, root):
    out = []
    for m in re.finditer(r"(\.github/[A-Za-z0-9_./-]+\.py)", run or ""):
        p = os.path.join(root, m.group(1))
        if os.path.isfile(p):
            out.append(m.group(1))
    return out


def sources(expr):
    """secret/var names an env value expression draws from"""
    s = str(expr)
    return re.findall(r"secrets\.([A-Za-z0-9_]+)", s), re.findall(r"vars\.([A-Za-z0-9_]+)", s), "github.token" in s


def static(root):
    wfd = os.path.join(root, ".github", "workflows")
    finds, used, checked = [], {}, set()
    for fn in sorted(os.listdir(wfd)):
        if not fn.endswith((".yml", ".yaml")):
            continue
        path = os.path.join(wfd, fn)
        raw = open(path).read()
        for kind, name in re.findall(r"\b(secrets|vars)\.([A-Za-z0-9_]+)", raw):
            if name != "GITHUB_TOKEN":
                used.setdefault(name, set()).add(fn)
        wf = load_yaml(path)
        wenv = wf.get("env") or {}
        for jn, job in (wf.get("jobs") or {}).items():
            jenv = dict(wenv, **(job.get("env") or {}))
            for k, st in enumerate(job.get("steps") or []):
                senv = dict(jenv, **(st.get("env") or {}))
                label = "%s:%s:%s" % (fn, jn, st.get("name") or st.get("id") or k)
                for name, val in senv.items():
                    sec, var, tok = sources(val)
                    if fn == "preflight-live.yml" and name != "GITHUB_TOKEN":
                        checked |= set(sec) | set(var)
                    if "${{" in str(val) and not (sec or var or tok) and CRED.search(name):
                        if not re.search(r"\$\{\{\s*(inputs|github|steps|needs|env|matrix)\.", str(val)):
                            finds.append("S4 NO-SOURCE %s %s=%s" % (label, name, val))
                run = st.get("run") or ""
                for scr in scripts_of(run, root):
                    for name in sorted(script_reads(os.path.join(root, scr))):
                        if name in RUNTIME or name in senv:
                            continue
                        if re.search(r"\b%s=" % re.escape(name), run):       # set inline: NAME=... python3 x.py
                            continue
                        finds.append("S1 UNMAPPED %s %s reads %s" % (label, scr, name) +
                                     (" (optional: %s)" % OPTIONAL[name] if name in OPTIONAL else ""))
                for m in SHELL_EMPTY_EXIT0.finditer(run):
                    name = m.group(1)
                    val = senv.get(name, "")
                    sec, var, tok = sources(val)
                    if (sec or var) and not all(x in OPTIONAL for x in sec + var):
                        finds.append("S3 SILENT-SKIP %s exits 0 (green run) when %s (from %s) is empty" %
                                     (label, name, ",".join("secrets." + x for x in sec) or ",".join("vars." + x for x in var)))
    for name in sorted(used):
        if name not in checked:
            finds.append("S2 UNCHECKED %s used by %s, not in preflight-live.yml" % (name, ",".join(sorted(used[name]))))
    hard = [f for f in finds if "(optional:" not in f]
    for f in finds:
        print(("FAIL " if f in hard else "info ") + f)
    sha = subprocess.run(["git", "-C", root, "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip() or "?"
    tag = "SECRETCHECK %s static %s secrets=%d checked=%d findings=%d" % ("OK" if not hard else "FAIL", sha, len(used),
                                                                          len(checked & set(used)), len(hard))
    print(tag + (": " + ", ".join(sorted({f.split()[0] + " " + f.split()[1] for f in hard})) if hard else ""))
    return 0 if not hard else 1


def api(url, tok):
    req = urllib.request.Request(url, headers={"Authorization": "Bearer " + tok, "Accept": "application/vnd.github+json",
                                               "User-Agent": "secretcheck"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return r.status, dict(r.headers), json.loads(r.read() or b"null")
    except urllib.error.HTTPError as e:
        return e.code, dict(e.headers), None
    except Exception as e:
        return 0, {}, repr(e)[:100]


def live():
    names = [n.strip() for n in os.environ.get("SECRETCHECK_NAMES", "").split(",") if n.strip()]
    bad, notes = [], []
    if not names:
        bad.append("SECRETCHECK_NAMES empty")
    for n in names:
        v = os.environ.get("SC_" + n, "")
        if v.strip():
            notes.append("%s=set(len %d)" % (n, len(v)))
        elif n in OPTIONAL:
            notes.append("%s=absent(optional)" % n)
            print("info %s absent: %s" % (n, OPTIONAL[n]))
        else:
            bad.append("%s missing" % n)
            print("FAIL %s is empty or does not exist" % n)
    tok = os.environ.get("SC_" + "PR_TOKEN", "")     # SC_<name> as for every name in SECRETCHECK_NAMES
    fork = os.environ.get("GITHUB_REPOSITORY", "Leg0shii/pequalnp-proofs-fork")
    if tok:
        st, h, d = api("https://api.github.com/rate_limit", tok)
        if st != 200:
            bad.append("PR_TOKEN rate_limit http %s" % st); print("FAIL PR_TOKEN /rate_limit http", st)
        else:
            core = (d or {}).get("resources", {}).get("core", {})
            scopes = h.get("X-OAuth-Scopes", h.get("x-oauth-scopes", "?"))
            notes.append("PR_TOKEN core=%s/%s scopes=[%s]" % (core.get("remaining"), core.get("limit"), scopes))
            print("info PR_TOKEN core remaining %s of %s, scopes %s" % (core.get("remaining"), core.get("limit"), scopes))
            if core.get("remaining", 0) < 200:
                print("WARN PR_TOKEN core remaining under 200: PR creation and closes will fail (not a secret fault)")
        st, h, d = api("https://api.github.com/repos/" + fork, tok)
        if st != 200 or not ((d or {}).get("permissions") or {}).get("push"):
            bad.append("PR_TOKEN cannot push %s (http %s)" % (fork, st)); print("FAIL PR_TOKEN cannot push", fork, "http", st)
        r = subprocess.run(["git", "-c", "http.extraheader=AUTHORIZATION: basic " + __import__("base64").b64encode(
            ("x-access-token:" + tok).encode()).decode(), "ls-remote", "https://github.com/Leg0shii/pnp-toolkit.git", "HEAD"],
            capture_output=True, text=True, timeout=60)
        if r.returncode != 0:
            bad.append("PR_TOKEN cannot read the toolkit"); print("FAIL PR_TOKEN cannot read the toolkit:", r.stderr.strip()[:120])
    print("SECRETCHECK %s live %s %s" % ("OK" if not bad else "FAIL", os.environ.get("GITHUB_SHA", "?")[:8],
                                         " ".join(notes)) + (": " + "; ".join(bad) if bad else ""))
    return 0 if not bad else 1


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["live"]:
        sys.exit(live())
    if a[:1] == ["static"]:
        sys.exit(static(os.path.abspath(a[1]) if len(a) > 1 else os.path.dirname(os.path.dirname(HERE))))
    print(__doc__); sys.exit(2)
