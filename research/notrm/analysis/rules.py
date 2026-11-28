import itertools, re, sys, glob
from collections import defaultdict
D = {}  # canonical key -> (m, c, Ccirc)
def canon(rows):
    r = len(rows); c = len(rows[0]) if r else 0
    best = None
    for M in ([rows, [''.join(rows[u][v] for u in range(r)) for v in range(c)]] if r and c else [rows]):
        rr = len(M); cc = len(M[0]) if rr else 0
        for p in itertools.permutations(range(cc)):
            k = tuple(sorted(''.join(row[p[i]] for i in range(cc)) for row in M))
            k = (rr, cc, k)
            if best is None or k < best: best = k
    return best
def load_rect(f):
    for line in open(f):
        t = line.rstrip('\n').split('\t')
        rows = t[2].split('/')
        if t[4] != 'true' or t[6] != 'true': continue
        D[canon(rows)] = (int(t[3]), int(t[5]), t[8][3:])
for f in glob.glob('/home/user/notrm/stackres/all_*.tsv'): load_rect(f)
for f in ['/tmp/claude-0/-home-user/eaa636bf-aeab-5049-96fc-5b4d385b37ff/scratchpad/n3_all.tsv', '/home/user/pequalnp-proofs-fork/research/notrm/results/n4_all.tsv']:
    for line in open(f):
        t = line.rstrip('\n').split('\t')
        if '?' in t[2] or '?' in t[3]: continue
        rows = t[1].split('/')
        D[canon(rows)] = (int(t[2][2:]), int(t[3][2:]), t[8][3:])
def val(rows):
    if not rows or not rows[0]: return (0, 0, '')
    return D.get(canon(rows))
def fanout(circ, r, wire):  # wire: ('x',u) or ('y',v)
    name = ('x%d' if wire[0]=='x' else 'y%d') % wire[1]
    return len(re.findall(r'[(,]%s[,)]' % name, circ))
rules = ['fewest_ones','fewest_zeros','max_cdrop','max_fanout','min_mdrop','twin_or_full_first','max_cdrop_then_fewest_ones']
fail_strict = defaultdict(int); fail_opt = defaultdict(int); total = 0; nogood = []
examples = defaultdict(list)
for key,(m,c,circ) in list(D.items()):
    r, cc, rows = key[0], key[1], list(key[2])
    if r < 3 or cc < 3: continue
    gap = m - c
    lines = []
    for u in range(r):
        sub = rows[:u] + rows[u+1:]
        lines.append(('x', u, rows[u], sub))
    cols = [''.join(rows[u][v] for u in range(r)) for v in range(cc)]
    for v in range(cc):
        sub = [row[:v] + row[v+1:] for row in rows]
        lines.append(('y', v, cols[v], sub))
    feats = []
    ok = True
    for (s, i, pat, sub) in lines:
        sv = val(sub)
        if sv is None: ok = False; break
        par = rows if s == 'x' else cols
        twin = par.count(pat) > 1 or set(pat) == {'1'}
        feats.append(dict(good = gap <= (sv[0]-sv[1]) + 1, ones = pat.count('1'), zeros = pat.count('0'), cdrop = c - sv[1], mdrop = m - sv[0], fan = fanout(circ, r, (s, i)), twin = twin, name = '%s%d' % (s, i)))
    if not ok: continue
    total += 1
    if not any(f['good'] for f in feats): nogood.append('/'.join(rows))
    score = {
        'fewest_ones': lambda f: f['ones'], 'fewest_zeros': lambda f: f['zeros'], 'max_cdrop': lambda f: -f['cdrop'],
        'max_fanout': lambda f: -f['fan'], 'min_mdrop': lambda f: f['mdrop'], 'twin_or_full_first': lambda f: (not f['twin'], f['ones']),
        'max_cdrop_then_fewest_ones': lambda f: (-f['cdrop'], f['ones'])}
    for rn in rules:
        b = min(score[rn](f) for f in feats)
        best = [f for f in feats if score[rn](f) == b]
        if not all(f['good'] for f in best):
            fail_strict[rn] += 1
            if len(examples[rn]) < 3: examples[rn].append(('/'.join(rows), m, c, [(f['name'], f['good']) for f in best]))
        if not any(f['good'] for f in best): fail_opt[rn] += 1
print('grids tested (r,c>=3, all sub-grids exact):', total, ' with no good line:', len(nogood), nogood[:5])
for rn in rules: print('%-28s strict-fail %4d   tie-optimistic-fail %4d   e.g. %s' % (rn, fail_strict[rn], fail_opt[rn], examples[rn][:2]))
print()
from collections import Counter
dist = Counter(); hard = []
for key,(m,c,circ) in list(D.items()):
    r, cc, rows = key[0], key[1], list(key[2])
    if r < 3 or cc < 3: continue
    cols = [''.join(rows[u][v] for u in range(r)) for v in range(cc)]
    subs = [rows[:u]+rows[u+1:] for u in range(r)] + [[row[:v]+row[v+1:] for row in rows] for v in range(cc)]
    vs = [val(s) for s in subs]
    if any(v is None for v in vs): continue
    md = [m - v[0] for v in vs]; cd = [c - v[1] for v in vs]
    k = min(md); dist[k] += 1
    if k >= 2: hard.append(('/'.join(rows), m, c, k, [(a, b) for a, b in zip(md, cd)]))
print('min m-drop distribution:', sorted(dist.items()))
for h in hard[:12]: print(h)
