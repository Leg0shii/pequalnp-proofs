// notrm: exact circuit sizes for n x n bipartite graphs on the one-a-side promise.
// Wire functions are bitmasks over the n*n promise points (point p = u*n + v).
// Inputs: wire u (0..n) = x_u (row u), wire n+v = y_v (column v).
// m(A) = least AND/OR fan-in-2 gates, c(A) = least AND/OR/NOT gates (NOT counts).
// L-meta-19158 claims m(A) <= c(A) + 2n - 5 for n >= 3.
use rayon::prelude::*;
use std::collections::HashSet;
use std::io::Write;
use std::sync::Mutex;
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Op {
    And,
    Or,
    Not,
}

#[derive(Clone, Debug)]
struct Gate {
    op: Op,
    a: usize,
    b: usize,
}

fn input_masks(n: usize) -> Vec<u64> {
    let mut w = vec![0u64; 2 * n];
    for u in 0..n {
        for v in 0..n {
            let p = u * n + v;
            w[u] |= 1 << p;
            w[n + v] |= 1 << p;
        }
    }
    w
}

fn full(n: usize) -> u64 {
    if n * n == 64 { !0 } else { (1u64 << (n * n)) - 1 }
}

fn eval(n: usize, gates: &[Gate]) -> u64 {
    let mut w = input_masks(n);
    let f = full(n);
    for g in gates {
        let v = match g.op {
            Op::And => w[g.a] & w[g.b],
            Op::Or => w[g.a] | w[g.b],
            Op::Not => !w[g.a] & f,
        };
        w.push(v);
    }
    *w.last().unwrap()
}

#[derive(Clone, Copy)]
enum L {
    C(bool),
    V(i32),
}
impl L {
    fn neg(self) -> L {
        match self {
            L::C(b) => L::C(!b),
            L::V(x) => L::V(-x),
        }
    }
}

struct Enc {
    s: cadical::Solver<cadical::Timeout>,
    nv: i32,
}
impl Enc {
    fn new_var(&mut self) -> i32 {
        self.nv += 1;
        self.nv
    }
    // add clause over literals with constant folding
    fn clause(&mut self, lits: &[L]) {
        let mut c: Vec<i32> = Vec::with_capacity(lits.len());
        for l in lits {
            match *l {
                L::C(true) => return,
                L::C(false) => {}
                L::V(x) => c.push(x),
            }
        }
        self.s.add_clause(c);
    }
}

/// Is there a circuit with at most k gates (output = last gate, copies allowed) computing target?
/// Returns Some(Some(circuit)) if SAT, Some(None) if UNSAT, None on timeout.
fn find(n: usize, target: u64, k: usize, allow_not: bool, timeout: f32) -> Option<Option<Vec<Gate>>> {
    let ni = 2 * n;
    let np = n * n;
    let inp = input_masks(n);
    if k == 0 {
        return Some(if inp.contains(&target) || target == 0 { Some(vec![]) } else { None });
    }
    let mut e = Enc { s: cadical::Solver::with_config("plain").unwrap_or_else(|_| cadical::Solver::new()), nv: 0 };
    e.s.set_callbacks(Some(cadical::Timeout::new(timeout)));
    // val[w][p]
    let mut val: Vec<Vec<L>> = Vec::new();
    for w in 0..ni {
        val.push((0..np).map(|p| L::C(inp[w] >> p & 1 == 1)).collect());
    }
    let mut opts: Vec<Vec<(i32, Op, usize, usize)>> = Vec::new();
    for g in 0..k {
        let nw = ni + g;
        let row: Vec<L> = if g == k - 1 {
            (0..np).map(|p| L::C(target >> p & 1 == 1)).collect()
        } else {
            (0..np).map(|_| L::V(e.new_var())).collect()
        };
        let mut os = Vec::new();
        for a in 0..nw {
            for b in a..nw {
                // a == b only as a copy (AND), used for padding
                if a == b {
                    if g == 0 { continue; }
                    if b != nw - 1 { continue; }
                    os.push((e.new_var(), Op::And, a, b));
                    continue;
                }
                if a < ni && b < ni && a / n == b / n {
                    // two inputs of the same side: AND is constant false on the promise; OR is fine
                    os.push((e.new_var(), Op::Or, a, b));
                    continue;
                }
                os.push((e.new_var(), Op::And, a, b));
                os.push((e.new_var(), Op::Or, a, b));
            }
            if allow_not {
                os.push((e.new_var(), Op::Not, a, a));
            }
        }
        let alo: Vec<L> = os.iter().map(|o| L::V(o.0)).collect();
        e.clause(&alo);
        for &(s, op, a, b) in &os {
            let sn = L::V(-s);
            for p in 0..np {
                let v = row[p];
                let x = val[a][p];
                let y = val[b][p];
                match op {
                    Op::And => {
                        e.clause(&[sn, x.neg(), y.neg(), v]);
                        e.clause(&[sn, x, v.neg()]);
                        e.clause(&[sn, y, v.neg()]);
                    }
                    Op::Or => {
                        e.clause(&[sn, x, y, v.neg()]);
                        e.clause(&[sn, x.neg(), v]);
                        e.clause(&[sn, y.neg(), v]);
                    }
                    Op::Not => {
                        e.clause(&[sn, x.neg(), v.neg()]);
                        e.clause(&[sn, x, v]);
                    }
                }
            }
        }
        val.push(row);
        opts.push(os);
    }
    // symmetry breaking: adjacent independent gates appear in increasing (a, b, op) order
    let key = |o: &(i32, Op, usize, usize)| -> (usize, usize, usize) { (o.2, o.3, o.1 as usize) };
    for g in 0..k.saturating_sub(1) {
        let w = ni + g;
        for o in &opts[g + 1] {
            if o.2 == w || o.3 == w { continue; }
            let ko = key(o);
            let mut c = vec![L::V(-o.0)];
            for o2 in &opts[g] {
                if key(o2) <= ko { c.push(L::V(o2.0)); }
            }
            e.clause(&c);
        }
    }
    // every gate except the last is read by some later gate
    for g in 0..k - 1 {
        let w = ni + g;
        let mut c = Vec::new();
        for h in g + 1..k {
            for &(s, _, a, b) in &opts[h] {
                if a == w || b == w {
                    c.push(L::V(s));
                }
            }
        }
        e.clause(&c);
    }
    match e.s.solve() {
        None => None,
        Some(false) => Some(None),
        Some(true) => {
            let mut gates = Vec::new();
            for os in &opts {
                let o = os.iter().find(|o| e.s.value(o.0) == Some(true)).unwrap();
                gates.push(Gate { op: o.1, a: o.2, b: o.3 });
            }
            // strip copy padding is not needed; verify
            assert_eq!(eval(n, &gates), target, "decoded circuit wrong");
            Some(Some(gates))
        }
    }
}

/// Least size, searching down from an upper bound. Returns (best size, exact?, circuit).
fn least(n: usize, target: u64, ub: usize, allow_not: bool, timeout: f32, floor: usize) -> (usize, bool, Vec<Gate>) {
    let mut best = ub;
    let mut circ: Vec<Gate> = Vec::new();
    // get a circuit at ub first
    let mut k = ub;
    loop {
        match find(n, target, k, allow_not, timeout) {
            Some(Some(c)) => {
                best = k;
                circ = c;
                if k == 0 || k <= floor { return (best, k == 0, circ); }
                k -= 1;
            }
            Some(None) => {
                if circ.is_empty() && best == k {
                    // ub itself impossible: search up
                    k += 1;
                    best = k;
                    continue;
                }
                return (best, true, circ);
            }
            None => return (best, false, circ),
        }
    }
}

fn mono_ub(n: usize, rows: &[u32]) -> usize {
    // star construction by distinct row patterns, and by distinct column patterns
    let cost = |rs: &[u32]| -> usize {
        let mut pats: Vec<(u32, usize)> = Vec::new();
        for &r in rs {
            if r == 0 { continue; }
            if let Some(x) = pats.iter_mut().find(|x| x.0 == r) { x.1 += 1; } else { pats.push((r, 1)); }
        }
        if pats.is_empty() { return 0; }
        let mut c = 0;
        for &(p, cnt) in &pats {
            c += (cnt - 1) + (p.count_ones() as usize - 1) + 1;
        }
        c + pats.len() - 1
    };
    let cols: Vec<u32> = (0..n).map(|v| (0..n).fold(0, |acc, u| acc | (((rows[u] >> v) & 1) << u))).collect();
    cost(rows).min(cost(&cols))
}

fn to_mask(n: usize, rows: &[u32]) -> u64 {
    let mut m = 0u64;
    for u in 0..n {
        for v in 0..n {
            if rows[u] >> v & 1 == 1 { m |= 1 << (u * n + v); }
        }
    }
    m
}

fn perms(n: usize) -> Vec<Vec<usize>> {
    fn rec(cur: &mut Vec<usize>, used: &mut Vec<bool>, n: usize, out: &mut Vec<Vec<usize>>) {
        if cur.len() == n { out.push(cur.clone()); return; }
        for i in 0..n {
            if !used[i] { used[i] = true; cur.push(i); rec(cur, used, n, out); cur.pop(); used[i] = false; }
        }
    }
    let mut out = Vec::new();
    rec(&mut vec![], &mut vec![false; n], n, &mut out);
    out
}

fn canon(n: usize, rows: &[u32], ps: &[Vec<usize>]) -> u64 {
    let mut best = u64::MAX;
    let cols: Vec<u32> = (0..n).map(|v| (0..n).fold(0, |acc, u| acc | (((rows[u] >> v) & 1) << u))).collect();
    for m in [rows, &cols[..]] {
        for p in ps {
            let mut r: Vec<u32> = m.iter().map(|&x| { let mut y = 0; for v in 0..n { if x >> v & 1 == 1 { y |= 1 << p[v]; } } y }).collect();
            r.sort_unstable();
            let key = r.iter().fold(0u64, |acc, &x| (acc << n) | x as u64);
            best = best.min(key);
        }
    }
    best
}

fn classes(n: usize) -> Vec<Vec<u32>> {
    let ps = perms(n);
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    // rows nondecreasing
    fn rec(n: usize, start: u32, cur: &mut Vec<u32>, f: &mut dyn FnMut(&[u32])) {
        if cur.len() == n { f(cur); return; }
        for r in start..(1u32 << n) { cur.push(r); rec(n, r, cur, f); cur.pop(); }
    }
    rec(n, 0, &mut vec![], &mut |rows: &[u32]| {
        let k = canon(n, rows, &ps);
        if seen.insert(k) {
            let r: Vec<u32> = (0..n).map(|i| ((k >> (n * (n - 1 - i))) & ((1 << n) - 1)) as u32).collect();
            out.push(r);
        }
    });
    out
}

fn fmt_circ(n: usize, c: &[Gate]) -> String {
    let name = |w: usize| -> String { if w < n { format!("x{}", w) } else if w < 2 * n { format!("y{}", w - n) } else { format!("g{}", w - 2 * n) } };
    c.iter().map(|g| match g.op {
        Op::And => format!("and({},{})", name(g.a), name(g.b)),
        Op::Or => format!("or({},{})", name(g.a), name(g.b)),
        Op::Not => format!("not({})", name(g.a)),
    }).collect::<Vec<_>>().join(" ")
}

fn parse_rows(n: usize, s: &str) -> Vec<u32> {
    // rows as n binary strings separated by '/' e.g. 01110/10111/...
    s.split('/').map(|r| { assert_eq!(r.len(), n); r.chars().enumerate().fold(0u32, |acc, (v, ch)| if ch == '1' { acc | 1 << v } else { acc }) }).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("help");
    match mode {
        "classes" => {
            let n: usize = args[2].parse().unwrap();
            let t = Instant::now();
            let cs = classes(n);
            eprintln!("n={} classes={} in {:?}", n, cs.len(), t.elapsed());
        }
        "one" => {
            // one <n> <rows> <timeout>
            let n: usize = args[2].parse().unwrap();
            let rows = parse_rows(n, &args[3]);
            let to: f32 = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(600.0);
            let tgt = to_mask(n, &rows);
            let ub = mono_ub(n, &rows);
            let t = Instant::now();
            let (m, mx, mc) = least(n, tgt, ub, false, to, 0);
            println!("m={} exact={} ({:?}) {}", m, mx, t.elapsed(), fmt_circ(n, &mc));
            let t = Instant::now();
            let (c, cx, cc) = least(n, tgt, m, true, to, 0);
            println!("c={} exact={} ({:?}) {}", c, cx, t.elapsed(), fmt_circ(n, &cc));
        }
        "all" => {
            // all <n> <timeout> <out>: exact m and c for every class
            let n: usize = args[2].parse().unwrap();
            let to: f32 = args[3].parse().unwrap();
            let out = Mutex::new(std::fs::File::create(&args[4]).unwrap());
            let cs = classes(n);
            eprintln!("n={} classes={}", n, cs.len());
            let slack = 2 * n - 5;
            let done = std::sync::atomic::AtomicUsize::new(0);
            cs.par_iter().for_each(|rows| {
                let tgt = to_mask(n, rows);
                let ub = mono_ub(n, rows);
                let t = Instant::now();
                let (m, mx, mc) = least(n, tgt, ub, false, to, 0);
                let (c, cx, cc) = least(n, tgt, m, true, to, 0);
                let gap = m as i64 - c as i64;
                let flag = if gap > slack as i64 { if mx && cx { "BREAK" } else { "CHECK" } } else { "ok" };
                let rs: Vec<String> = rows.iter().map(|&r| (0..n).map(|v| if r >> v & 1 == 1 { '1' } else { '0' }).collect()).collect();
                let line = format!("{}\t{}\tm={}{}\tc={}{}\tgap={}\t{}\t{:.1}s\tM: {}\tC: {}\n", n, rs.join("/"), m, if mx { "" } else { "?" }, c, if cx { "" } else { "?" }, gap, flag, t.elapsed().as_secs_f32(), fmt_circ(n, &mc), fmt_circ(n, &cc));
                out.lock().unwrap().write_all(line.as_bytes()).unwrap();
                let d = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                if d % 100 == 0 { eprintln!("{} / {}", d, cs.len()); }
            });
        }
        "check" => {
            // check <n> <timeout> <out> [lo hi]: m upper bound by SAT, then one UNSAT test that no
            // NOT circuit has <= m_ub - (2n-5) - 1 gates. ok = bound holds for this graph.
            let n: usize = args[2].parse().unwrap();
            let to: f32 = args[3].parse().unwrap();
            let out = Mutex::new(std::fs::File::create(&args[4]).unwrap());
            let mut cs = classes(n);
            if args.len() > 6 { let lo: usize = args[5].parse().unwrap(); let hi: usize = args[6].parse::<usize>().unwrap().min(cs.len()); cs = cs[lo..hi].to_vec(); }
            eprintln!("n={} classes={}", n, cs.len());
            let slack = 2 * n - 5;
            let done = std::sync::atomic::AtomicUsize::new(0);
            cs.par_iter().for_each(|rows| {
                let tgt = to_mask(n, rows);
                let ub = mono_ub(n, rows);
                let t = Instant::now();
                // only need m_ub; stop descending once K would be tiny anyway? descend fully with timeout
                let (m, mx, mc) = least(n, tgt, ub, false, to, 0);
                let mut res = String::new();
                if m <= slack { res.push_str("ok-trivial"); } else {
                    let kk = m - slack - 1;
                    match find(n, tgt, kk, true, to) {
                        Some(None) => res.push_str(&format!("ok c>={}", kk + 1)),
                        None => res.push_str(&format!("TIMEOUT c<= ? at {}", kk)),
                        Some(Some(_)) => {
                            // a NOT circuit of size <= kk exists: get the exact NOT cost, then test mono at c+slack
                            let (s, cx, cc) = least(n, tgt, kk, true, to, 0);
                            if !cx { res.push_str("c-not-exact "); }
                            match find(n, tgt, s + slack, false, to * 4.0) {
                                Some(Some(_)) => res.push_str("ok (m_ub not exact)"),
                                Some(None) => res.push_str(&format!("BREAK s={} C: {}", s, fmt_circ(n, &cc))),
                                None => res.push_str(&format!("CANDIDATE s={} C: {}", s, fmt_circ(n, &cc))),
                            }
                        }
                    }
                }
                let rs: Vec<String> = rows.iter().map(|&r| (0..n).map(|v| if r >> v & 1 == 1 { '1' } else { '0' }).collect()).collect();
                let line = format!("{}\t{}\tm={}{}\t{}\t{:.1}s\tM: {}\n", n, rs.join("/"), m, if mx { "" } else { "?" }, res, t.elapsed().as_secs_f32(), fmt_circ(n, &mc));
                out.lock().unwrap().write_all(line.as_bytes()).unwrap();
                let d = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                if d % 50 == 0 { eprintln!("{} / {}", d, cs.len()); }
            });
        }
        _ => eprintln!("usage: notrm classes <n> | one <n> <rows> [timeout] | all <n> <timeout> <out.tsv>"),
    }
}
