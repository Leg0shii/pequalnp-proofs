// stack: rectangular r x c version of notrm's SAT search, plus the "stacking test".
// For a grid H (r0 x c), S = [H ; not H] (2r0 x c). One-NOT construction gives
// c(S) <= m(H) + 2r0 + 3, so L-meta-19158 (m <= c + r + c - 5) forces m(S) <= m(H) + O(n):
// a NOT-free circuit must compute H and its complement together cheaply.
use rayon::prelude::*;
use std::collections::HashSet;
use std::io::Write;
use std::sync::Mutex;
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Op { And, Or, Not }
#[derive(Clone, Debug)]
struct Gate { op: Op, a: usize, b: usize }

#[derive(Clone, Copy)]
struct Sh { r: usize, c: usize }

fn input_masks(s: Sh) -> Vec<u64> {
    let mut w = vec![0u64; s.r + s.c];
    for u in 0..s.r { for v in 0..s.c { let p = u * s.c + v; w[u] |= 1 << p; w[s.r + v] |= 1 << p; } }
    w
}
fn full(s: Sh) -> u64 { let np = s.r * s.c; if np == 64 { !0 } else { (1u64 << np) - 1 } }
fn eval(s: Sh, gates: &[Gate]) -> u64 {
    let mut w = input_masks(s);
    let f = full(s);
    for g in gates {
        let v = match g.op { Op::And => w[g.a] & w[g.b], Op::Or => w[g.a] | w[g.b], Op::Not => !w[g.a] & f };
        w.push(v);
    }
    *w.last().unwrap()
}

#[derive(Clone, Copy)]
enum L { C(bool), V(i32) }
impl L { fn neg(self) -> L { match self { L::C(b) => L::C(!b), L::V(x) => L::V(-x) } } }
struct Enc { s: cadical::Solver<cadical::Timeout>, nv: i32 }
impl Enc {
    fn new_var(&mut self) -> i32 { self.nv += 1; self.nv }
    fn clause(&mut self, lits: &[L]) {
        let mut c: Vec<i32> = Vec::with_capacity(lits.len());
        for l in lits { match *l { L::C(true) => return, L::C(false) => {}, L::V(x) => c.push(x) } }
        self.s.add_clause(c);
    }
}

fn find(s: Sh, target: u64, k: usize, allow_not: bool, timeout: f32) -> Option<Option<Vec<Gate>>> {
    let ni = s.r + s.c;
    let np = s.r * s.c;
    let inp = input_masks(s);
    if k == 0 { return Some(if inp.contains(&target) || target == 0 { Some(vec![]) } else { None }); }
    let mut e = Enc { s: cadical::Solver::with_config("plain").unwrap_or_else(|_| cadical::Solver::new()), nv: 0 };
    e.s.set_callbacks(Some(cadical::Timeout::new(timeout)));
    let mut val: Vec<Vec<L>> = Vec::new();
    for w in 0..ni { val.push((0..np).map(|p| L::C(inp[w] >> p & 1 == 1)).collect()); }
    let mut opts: Vec<Vec<(i32, Op, usize, usize)>> = Vec::new();
    for g in 0..k {
        let nw = ni + g;
        let row: Vec<L> = if g == k - 1 { (0..np).map(|p| L::C(target >> p & 1 == 1)).collect() } else { (0..np).map(|_| L::V(e.new_var())).collect() };
        let mut os = Vec::new();
        for a in 0..nw {
            for b in a..nw {
                if a == b {
                    if g == 0 || b != nw - 1 { continue; }
                    os.push((e.new_var(), Op::And, a, b));
                    continue;
                }
                if a < ni && b < ni && ((a < s.r) == (b < s.r)) { os.push((e.new_var(), Op::Or, a, b)); continue; }
                os.push((e.new_var(), Op::And, a, b));
                os.push((e.new_var(), Op::Or, a, b));
            }
            if allow_not { os.push((e.new_var(), Op::Not, a, a)); }
        }
        let alo: Vec<L> = os.iter().map(|o| L::V(o.0)).collect();
        e.clause(&alo);
        for &(sv, op, a, b) in &os {
            let sn = L::V(-sv);
            for p in 0..np {
                let v = row[p]; let x = val[a][p]; let y = val[b][p];
                match op {
                    Op::And => { e.clause(&[sn, x.neg(), y.neg(), v]); e.clause(&[sn, x, v.neg()]); e.clause(&[sn, y, v.neg()]); }
                    Op::Or => { e.clause(&[sn, x, y, v.neg()]); e.clause(&[sn, x.neg(), v]); e.clause(&[sn, y.neg(), v]); }
                    Op::Not => { e.clause(&[sn, x.neg(), v.neg()]); e.clause(&[sn, x, v]); }
                }
            }
        }
        val.push(row);
        opts.push(os);
    }
    let key = |o: &(i32, Op, usize, usize)| -> (usize, usize, usize) { (o.2, o.3, o.1 as usize) };
    for g in 0..k.saturating_sub(1) {
        let w = ni + g;
        for o in &opts[g + 1] {
            if o.2 == w || o.3 == w { continue; }
            let ko = key(o);
            let mut c = vec![L::V(-o.0)];
            for o2 in &opts[g] { if key(o2) <= ko { c.push(L::V(o2.0)); } }
            e.clause(&c);
        }
    }
    for g in 0..k - 1 {
        let w = ni + g;
        let mut c = Vec::new();
        for h in g + 1..k { for &(sv, _, a, b) in &opts[h] { if a == w || b == w { c.push(L::V(sv)); } } }
        e.clause(&c);
    }
    match e.s.solve() {
        None => None,
        Some(false) => Some(None),
        Some(true) => {
            let mut gates = Vec::new();
            for os in &opts { let o = os.iter().find(|o| e.s.value(o.0) == Some(true)).unwrap(); gates.push(Gate { op: o.1, a: o.2, b: o.3 }); }
            assert_eq!(eval(s, &gates), target, "decoded circuit wrong");
            Some(Some(gates))
        }
    }
}

/// least size searching down from ub; (size, exact, circuit)
fn least(s: Sh, target: u64, ub: usize, allow_not: bool, timeout: f32) -> (usize, bool, Vec<Gate>) {
    if let Some(Some(c0)) = find(s, target, 0, allow_not, timeout) { return (0, true, c0); }
    let mut best = ub; let mut circ: Vec<Gate> = Vec::new(); let mut k = ub;
    loop {
        match find(s, target, k, allow_not, timeout) {
            Some(Some(c)) => { best = k; circ = c; if k == 0 { return (0, true, circ); } k -= 1; }
            Some(None) => { if circ.is_empty() { k += 1; best = k; continue; } return (best, true, circ); }
            None => { if circ.is_empty() { k += 1; best = k; continue; } return (best, false, circ); }
        }
    }
}

fn star_ub(s: Sh, rows: &[u32]) -> usize {
    let cost = |rs: &[u32]| -> usize {
        let mut pats: Vec<(u32, usize)> = Vec::new();
        for &r in rs { if r == 0 { continue; } if let Some(x) = pats.iter_mut().find(|x| x.0 == r) { x.1 += 1; } else { pats.push((r, 1)); } }
        if pats.is_empty() { return 0; }
        let mut c = 0;
        for &(p, cnt) in &pats { c += (cnt - 1) + (p.count_ones() as usize - 1) + 1; }
        c + pats.len() - 1
    };
    let cols: Vec<u32> = (0..s.c).map(|v| (0..s.r).fold(0, |acc, u| acc | (((rows[u] >> v) & 1) << u))).collect();
    cost(rows).min(cost(&cols))
}
fn to_mask(s: Sh, rows: &[u32]) -> u64 {
    let mut m = 0u64;
    for u in 0..s.r { for v in 0..s.c { if rows[u] >> v & 1 == 1 { m |= 1 << (u * s.c + v); } } }
    m
}
fn perms(n: usize) -> Vec<Vec<usize>> {
    fn rec(cur: &mut Vec<usize>, used: &mut Vec<bool>, n: usize, out: &mut Vec<Vec<usize>>) {
        if cur.len() == n { out.push(cur.clone()); return; }
        for i in 0..n { if !used[i] { used[i] = true; cur.push(i); rec(cur, used, n, out); cur.pop(); used[i] = false; } }
    }
    let mut out = Vec::new(); rec(&mut vec![], &mut vec![false; n], n, &mut out); out
}
/// classes of r x c grids under row and column permutations
fn classes(s: Sh) -> Vec<Vec<u32>> {
    let ps = perms(s.c);
    let mut seen = HashSet::new(); let mut out = Vec::new();
    fn rec(s: Sh, start: u32, cur: &mut Vec<u32>, f: &mut dyn FnMut(&[u32])) {
        if cur.len() == s.r { f(cur); return; }
        for r in start..(1u32 << s.c) { cur.push(r); rec(s, r, cur, f); cur.pop(); }
    }
    rec(s, 0, &mut vec![], &mut |rows: &[u32]| {
        let mut best: Option<Vec<u32>> = None;
        for p in &ps {
            let mut r: Vec<u32> = rows.iter().map(|&x| { let mut y = 0; for v in 0..s.c { if x >> v & 1 == 1 { y |= 1 << p[v]; } } y }).collect();
            r.sort_unstable();
            if best.as_ref().map_or(true, |b| r < *b) { best = Some(r); }
        }
        let b = best.unwrap();
        if seen.insert(b.clone()) { out.push(b); }
    });
    out
}
fn fmt_circ(s: Sh, c: &[Gate]) -> String {
    let name = |w: usize| -> String { if w < s.r { format!("x{}", w) } else if w < s.r + s.c { format!("y{}", w - s.r) } else { format!("g{}", w - s.r - s.c) } };
    c.iter().map(|g| match g.op { Op::And => format!("and({},{})", name(g.a), name(g.b)), Op::Or => format!("or({},{})", name(g.a), name(g.b)), Op::Not => format!("not({})", name(g.a)) }).collect::<Vec<_>>().join(" ")
}
fn rstr(s: Sh, rows: &[u32]) -> String {
    rows.iter().map(|&r| (0..s.c).map(|v| if r >> v & 1 == 1 { '1' } else { '0' }).collect::<String>()).collect::<Vec<_>>().join("/")
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a[1] == "all" {
        // all <r> <c> <timeout> <out>: exact m and c for every class of r x c grids (row/col perms)
        let r: usize = a[2].parse().unwrap(); let c: usize = a[3].parse().unwrap(); let to: f32 = a[4].parse().unwrap();
        let sh = Sh { r, c };
        let out = Mutex::new(std::fs::File::create(&a[5]).unwrap());
        let cs = classes(sh);
        eprintln!("{}x{} classes={}", r, c, cs.len());
        cs.par_iter().for_each(|rows| {
            let t = to_mask(sh, rows);
            let (m, mx, mc) = least(sh, t, star_ub(sh, rows), false, to);
            let (cc, cx, ccirc) = least(sh, t, m, true, to);
            let line = format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\tM: {}\tC: {}\n", r, c, rstr(sh, rows), m, mx, cc, cx, fmt_circ(sh, &mc), fmt_circ(sh, &ccirc));
            out.lock().unwrap().write_all(line.as_bytes()).unwrap();
        });
        return;
    }
    // stack <r0> <c> <timeout> <out.tsv>
    let r0: usize = a[2].parse().unwrap();
    let c: usize = a[3].parse().unwrap();
    let to: f32 = a[4].parse().unwrap();
    let out = Mutex::new(std::fs::File::create(&a[5]).unwrap());
    let sh = Sh { r: r0, c };
    let ss = Sh { r: 2 * r0, c };
    let cs = classes(sh);
    let fullrow = (1u32 << c) - 1;
    let cs: Vec<Vec<u32>> = cs.into_iter().filter(|rs| !rs.iter().all(|&x| x == 0) && !rs.iter().all(|&x| x == fullrow)).collect();
    eprintln!("H {}x{} classes={}", r0, c, cs.len());
    let bound = 2 * r0 + c - 5;
    let done = std::sync::atomic::AtomicUsize::new(0);
    cs.par_iter().for_each(|rows| {
        let t = Instant::now();
        let neg: Vec<u32> = rows.iter().map(|&x| !x & fullrow).collect();
        let (mh, mhx, _) = least(sh, to_mask(sh, rows), star_ub(sh, rows), false, to);
        let (mn, mnx, _) = least(sh, to_mask(sh, &neg), star_ub(sh, &neg), false, to);
        let srows: Vec<u32> = rows.iter().chain(neg.iter()).cloned().collect();
        let st = to_mask(ss, &srows);
        let (ms, msx, msc) = least(ss, st, star_ub(ss, &srows), false, to);
        let cub = ms.min(mh + 2 * r0 + 3);
        let (cs_, csx, csc) = least(ss, st, cub, true, to);
        let gap = ms as i64 - cs_ as i64;
        let flag = if gap > bound as i64 { if msx && csx { "BREAK" } else { "CHECK" } } else { "ok" };
        let line = format!("{}x{}\tH={}\tmH={}{}\tmNotH={}{}\tmS={}{}\tcS={}{}\tdelta={}\tgapS={}\tbound={}\t{}\t{:.1}s\tMS: {}\tCS: {}\n",
            r0, c, rstr(sh, rows), mh, if mhx {""} else {"?"}, mn, if mnx {""} else {"?"}, ms, if msx {""} else {"?"}, cs_, if csx {""} else {"?"},
            ms as i64 - mh as i64, gap, bound, flag, t.elapsed().as_secs_f32(), fmt_circ(ss, &msc), fmt_circ(ss, &csc));
        out.lock().unwrap().write_all(line.as_bytes()).unwrap();
        let d = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
        if d % 20 == 0 { eprintln!("{} / {}", d, cs.len()); }
    });
}
