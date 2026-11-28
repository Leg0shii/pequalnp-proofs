# NOT-gate removal bound: handoff (28 Nov 2026, 19:20 UTC)

Goal (the owner's words): find a real proof, on paper, of the statement below. Points and the site's leaderboard do not matter. A counterexample also counts as a result.

## 1. The statement

The site's step is **L-meta-19158** on pequalnp. It sits on the Meta-complexity front, is marked main line, and has weight 120.

- **Setting ("one-a-side promise").** There is an r×c 0/1 grid A. The inputs are x_1..x_r (rows) and y_1..y_c (columns), and exactly one x and exactly one y are on. A circuit **represents** A if, on input (x_u, y_v), it outputs A[u][v]. There are r·c possible inputs.
- **Circuit costs.** Gates have fan-in 2.
  - **m(A)** is the fewest AND/OR gates (monotone) needed to represent A.
  - **c(A)** is the fewest AND/OR/NOT gates, where each NOT counts as a gate.
  - Under the promise, every wire computes an r×c matrix: x_u is "row u full" and y_v is "column v full". AND is entrywise min, OR is max, NOT is the complement.
- **Claim:** m(A) ≤ c(A) + 2n − 5 for n×n grids with n ≥ 3. The rectangular version is m ≤ c + r + c − 5.
- **Tight examples:**
  - XOR, i.e. [u=0] xor [v=0]: c = 4 and m = 2n − 1.
  - The crown (u ≠ v): c = 2n and m = 4n − 5.
- **Consequences:** it implies the site's steps 25454 and 19384 ("the complement costs at most s + 2n − 4 more"), and refutes the opposite step 19159.

## 2. Literature: why a proof would be new

| Source | What it says |
|---|---|
| Jukna, "Disproving the single level conjecture" (SIAM J. Comput. 2006), **Lemma 3.11** | Exactly this setting. It proves only **m ≤ 2c + O(n)**. Method: double the circuit with De Morgan so that NOTs sit only on inputs, then replace "not x_u" by the OR of the other x's. https://web.vu.lt/mif/s.jukna/ftp/single1.pdf |
| Wegener, *The Complexity of Boolean Functions* (1987), §6.13, Thm 13.5 | Same factor-2 result, C_m = O(C) + O(n) (Berkowitz pseudo-complements). https://web.vu.lt/mif/s.jukna/boolean/blaues_book.pdf |
| Jukna, "Computational Complexity of Graphs", Strong Magnification Lemma (p.17) | A linear loss of about 4n, but only for NOTs at the inputs and a bit-encoded f_G. **Not our model.** |
| Chashkin 1994, cited as Jukna Thm 1.19 | Monotone lower bound: twin-free, no empty or full rows ⇒ m ≥ 2r − 1. |

No source found states factor 1 (additive c + O(n)), the exact 2n − 5, or these tight examples. Not read (paywalled): Pudlák–Rödl–Savický 1988, Lokam 2003, Chashkin 1994 itself.

## 3. Proven so far (by hand, checked)

**Reductions.**
- Merging two equal rows, or deleting a full row (same for columns): c does not grow, and m(A) ≤ m(A') + 1.
- Deleting a line (setting its input to 0) never increases m or c.
- Empty lines are not reducible.

**Count bound.** For a twin-free grid, c ≥ r + c − 3: at most one unread row and one unread column.

**Lemma 1 (complement lemma for block grids).**
- Statement: let G = A_1×B_1 ∪ … ∪ A_k×B_k, with row sets pairwise disjoint and column sets pairwise disjoint. Then m(¬G) ≤ m(G) + r + c − 4.
- Upper bound for ¬G:
  - Let z_i = OR of the x's in A_i and the y's in B_i, at |A_i| + |B_i| − 1 gates.
  - ¬G = "at least two z_i on" OR (row or column outside every block).
  - "At least two" costs 3k − 5 gates by the chain p_1 = z_1; t_i = p_{i−1} ∧ z_i; p_i = p_{i−1} ∨ z_i; output = OR of the t_i.
  - Total: r + c + 2k − 5.
- Lower bound for G: restrict to one row and one column per block. That gives the k×k diagonal, so m ≥ 2k − 1 by Chashkin.

**Lemma A (crown, NOT allowed).**
- Statement: for k ≥ 3, c(crown_k) ≥ 2k.
- Proof by induction. In an optimal circuit, at most one x and one y are unread. Pick i with both x_i and y_i read, and set x_i = y_i = 0.
  - If different gates read x_i and y_i, each of them dies.
  - If one gate reads both, it becomes 0 and its successor dies too.
  - Either way at least 2 gates vanish.
- Base: c(crown_3) = 6, proven by SAT.

**Theorem B (bound holds for block complements).**
- Statement: if ¬H is a disjoint-block union with k blocks, then m(H) ≤ c(H) + r + c − 5.
- Proof:
  - Upper bound: m(H) ≤ r + c + 2k − 5, by Lemma 1's construction.
  - Lower bound: c(H) ≥ 2k, by restricting to the k-crown and using Lemma A.
  - k = 2 (XOR family) uses a SAT-checked fact: every 2-block complement on 6 lines has c ≥ 4.
  - k = 1 is direct.
- Coverage: XOR, every crown, every "all filled except a matching" grid, and every tight case seen so far.

**Complement-lemma induction, the proven step.**
- If G has a line u with exactly one 0, then adding u to ¬G costs 2 gates (x_u ∧ y_v, then OR). Removing u from G saves ≥ 1 gate (gate elimination).
- So m(¬G) ≤ m(G) + r + c − 4 follows by induction from the smaller grid.
- Empty, full and copied lines cost 1 and save 0, so they also work.
- One edge case is open: the 2-gate move needs the circuit for ¬G − u to output 0 when all x are off. This can fail if some column of G has its only 1 in row u.

## 4. Data facts (exact SAT, Rust tool)

- **Exhaustive checks:**
  - Every 3×3 and 4×4 grid is checked. None breaks the bound; 3 of the 4×4 grids are still missing an exact c.
  - Every 3×4 and 3×5 grid passes, and 1,023 of 1,053 4×5 grids.
  - 5×5: 730 of 3,014 checked, with 0 breaks and 116 solver timeouts. Three flagged candidates were all settled (two by hand-built circuits: 13 ≤ 14 and 17 ≤ 19).
- **One NOT is enough in tight cases.** Every tight grid has an optimal NOT circuit with exactly one NOT, shaped "NOT of an OR of disjoint pairs".
- **Line induction (the owner's idea):**
  - On every exact grid, *some* row or column satisfies gap(A) ≤ gap(A − line) + 1, where gap = m − c. "Any line" fails, e.g. 0001/1110/1110/1110.
  - The best simple selection rule is "a copied or full line, else a line with the fewest 1s". It fits 289 of 290 grids.
- **The same induction holds for the complement lemma:**
  - Some line always has [m(¬G) − m(¬G − ℓ)] − [m(G) − m(G − ℓ)] ≤ 1.
  - Up to 4×4, only 7 fully reduced grids have no one-0 line: the 3×3 and 4×4 diagonals, 0001/0010/0100/1001, 0001/0010/0101/1010, 0001/0010/0101/1100, 0001/0011/0110/1100 and 0001/0110/1010/1100.
  - The diagonals are covered by Lemma 1. Each of the other five has a two-0 line whose removal saves ≥ 2 gates. This is not true of *every* two-0 line.
- **Stacking test.** For every 3×3 H, the grid [H ; ¬H] passes (34 grids).

## 5. Open core and ideas

1. **The complement lemma for all G** (= site step 25454): m(¬G) ≤ m(G) + r + c − 4. It gives the bound for every circuit whose only NOT is the last gate.
   - The textbook dual circuit costs about 6n extra, not 2n. The cheap circuits for ¬G look structurally different from G's (matching → crown uses "at least two pairs on").
   - Route (i), line induction: for a two-0 line, prove "removing it saves ≥ 2" for some well-chosen line. The gate-elimination bad case is when x_u is read exactly once, by an OR g = x_u ∨ h. Then G_u = Φ(t = 1, no x on), and G_u ∩ H_w ⊆ G_w for every row w.
   - Route (ii): generalize Lemma 1's "at least two z_i on" from block unions to arbitrary monotone circuits.
2. **Several NOTs.**
   - Either show that some optimal NOT circuit has the shape "monotone → one NOT → monotone" without growing (the owner's PC is testing this on small grids), or handle several NOTs directly.
   - Warning: the bound allows 2n − 5 in total, however many NOTs there are, so the NOTs must share that cost.
3. **The stacking reformulation.** The bound implies that a monotone circuit can compute H and ¬H stacked ([H ; ¬H], a 2r×c grid) for only m(H) + O(n) gates, for *every* H.
   - With one NOT, the stacked grid costs at most m(H) + 2r + 3: replace x_u by x_u ∨ x_{u'}, then (H ∧ X_A) ∨ ¬(H ∨ X_A).
   - For Lupanov-type constructions (group columns by pattern), sharing works, because the stacked grid's column patterns are determined by H's. So random grids are not an obvious counterexample.
4. **Counterexample suspects: complements of cycles.**
   - Take G = the 2n-cycle as an n×n grid (row u = {u, u+1 mod n}) and H = ¬G (each row all but two neighbouring columns).
   - Known: m(G) ≤ 3n − 1, so c(H) ≤ 3n. Restricting to the even rows and columns gives a crown, so c(H) ≥ n.
   - The best monotone construction for H I found is 5n − 7: prefix and suffix ORs of y's, with row u = P_{u−1} ∨ S_{u+2}, and row n−1 = S_1 ∧ P_{n−2} (an AND of two y-sets is their intersection under the promise).
   - If c(H) is really near 2n and m(H) near 5n, the bound breaks for large n. If c(H) is about 3n, the gap is about 2n − 7 and the bound holds.
   - The site's makers probe exactly this family: steps 25655 ("fifteen-gate monotone selector for the complement of the ten-cycle") and 25653 ("sparse-complement circuit violating eleven-tenths bounds").
   - A SAT run of m for the 5×5 cycle and its complement was still running at handoff, in a cloud scratch directory that will be lost. Rerun with: `notrm one 5 11000/01100/00110/00011/10001 600` and `notrm one 5 00111/10011/11001/11100/01110 600`.
5. **The makers' own sketch** (step entry): merge duplicate lines; the count bound gives ≥ r + c − 3; at that budget the circuit is positive; one gate higher, a live NOT forces a tree with one use per wire and one omitted line per bank; "then tackle larger budgets". So their plan is an induction on c minus its minimum.

## 6. Tools and files

- **Rust SAT tool** (CaDiCaL), fork `Leg0shii/pequalnp-proofs-fork`, branch `claude/project-thread-591mll`, folder `research/notrm/`:
  - `src/main.rs`: square n×n. Modes: `one`, `all`, `check`.
  - `src/bin/stack.rs`: rectangles. `all r c timeout out` gives exact m and c per class; `stack r0 c timeout out` runs the stacking test.
  - `analysis/rules.py`: the line-rule tests.
  - `results/`: n4_all.tsv (4×4 exact), n5_check.tsv (5×5 progress), cloud/all_*.tsv (2×2 … 3×4 exact), cloud/s33.tsv (stacking).
- **On the owner's PC** (WSL distro "pequalnp"):
  - `~/notrm-fast` holds the faster v2 checker (rectangles, reductions, count and gate-elimination lower bounds; local only, not on GitHub).
  - `~/notrm-fast/PROOF_NOTES.md` is the PC session's write-up of Lemmas 1–3 and Theorem B.
- **Explainer page** for the owner: https://claude.ai/artifact/4jE5PyAEY3dof9outRc6uk
