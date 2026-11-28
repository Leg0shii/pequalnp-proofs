import PEqualNP.Defs

-- Exhaustion certificate: a kernel-run search over sets of 6-bit wire masks (a set is a Nat
-- bitset), with a soundness proof that every circuit of the statement is covered by the search.

namespace PEqualNP.Outside.L_meta_50199

open PEqualNP.CircuitLowerBounds

def elems (S : Nat) : List Nat := (List.range 64).filter (fun a => S.testBit a)

def aoHas (S v : Nat) : Bool :=
  (elems S).any (fun a => (elems S).any (fun c => (a &&& c == v) || (a ||| c == v)))

def notHas (S v : Nat) : Bool := (elems S).any (fun a => 63 ^^^ a == v)

def hit (A B C S : Nat) : Bool := S.testBit A && S.testBit B && S.testBit C

def miss (A B C S : Nat) : Nat :=
  (if S.testBit A then 0 else 1) + (if S.testBit B then 0 else 1) + (if S.testBit C then 0 else 1)

def reach (A B C : Nat) : Nat → Nat → Nat → Bool
  | 0, _, S => hit A B C S
  | k+1, b, S => hit A B C S || (decide (miss A B C S ≤ k+1) &&
      (reach A B C k b S || (decide (0 < b) && reach A B C k (b-1) S) ||
       (List.range 64).any (fun v => !S.testBit v &&
         ((aoHas S v && reach A B C k b (S ||| 2^v)) ||
          (decide (0 < b) && notHas S v && reach A B C k (b-1) (S ||| 2^v))))))

def body (A B C k b b' S v : Nat) : Bool :=
  !S.testBit v && ((aoHas S v && reach A B C k b (S ||| 2^v)) ||
    (decide (0 < b) && notHas S v && reach A B C k b' (S ||| 2^v)))

theorem reach_succ (A B C k b b' S : Nat) (hb : b' = b - 1) : reach A B C (k+1) b S =
    (hit A B C S || (decide (miss A B C S ≤ k+1) &&
      (reach A B C k b S || (decide (0 < b) && reach A B C k b' S) ||
       (List.range 64).any (body A B C k b b' S)))) := by
  subst hb
  rfl

theorem mem_elems {S a : Nat} : a ∈ elems S ↔ a < 64 ∧ S.testBit a = true := by
  simp [elems, List.mem_filter, List.mem_range]

theorem bits32 : ∀ a < 64, ∀ c < 64, a &&& c < 64 ∧ a ||| c < 64 ∧ 63 ^^^ a < 64 := by
  decide +kernel

theorem uniq32 : ∀ m < 64, ∀ a < 64, (∀ t : Fin 6, m.testBit t.val = a.testBit t.val) → m = a := by
  decide +kernel

theorem t31 : ∀ t : Fin 6, (63 : Nat).testBit t.val = true := by decide

theorem or_pow_self {S v : Nat} (h : S.testBit v = true) : S ||| 2^v = S := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : v = i
  · subst hi; simp [h]
  · simp [hi]

theorem testBit_or_pow (S v x : Nat) : (S ||| 2^v).testBit x = (S.testBit x || decide (v = x)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]

theorem miss_step (A B C S v : Nat) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    miss A B C S ≤ miss A B C (S ||| 2^v) + 1 := by
  unfold miss
  rw [testBit_or_pow, testBit_or_pow, testBit_or_pow]
  by_cases a : S.testBit A = true <;> by_cases b : S.testBit B = true <;>
    by_cases c : S.testBit C = true <;> by_cases x : v = A <;> by_cases y : v = B <;>
    by_cases z : v = C <;> simp_all

theorem miss_of_hit {A B C S : Nat} (h : hit A B C S = true) : miss A B C S = 0 := by
  simp only [hit, Bool.and_eq_true] at h
  simp [miss, h.1.1, h.1.2, h.2]

theorem reach_hit {A B C S : Nat} (k b : Nat) (h : hit A B C S = true) : reach A B C k b S = true := by
  cases k with
  | zero => simpa [reach] using h
  | succ k => simp [reach, h]

theorem reach_miss {A B C S k b : Nat} (h : reach A B C k b S = true) :
    hit A B C S = true ∨ miss A B C S ≤ k := by
  cases k with
  | zero => left; simpa [reach] using h
  | succ k =>
    simp only [reach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem classify (S L : Nat) (W : Fin 6 → List Bool) (g : Gate)
    (h31 : S.testBit 63 = true) (h0 : S.testBit 0 = true)
    (hinv : ∀ i < L, ∃ m, m < 64 ∧ S.testBit m = true ∧ ∀ t, (W t).getD i false = m.testBit t.val)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < L) :
    ∃ v, v < 64 ∧ (∀ t, g.op.eval (g.inputs.map fun i => (W t).getD i false) = v.testBit t.val) ∧
      (S.testBit v = true ∨ (g.op ≠ GateOp.not ∧ aoHas S v = true) ∨
        (g.op = GateOp.not ∧ notHas S v = true)) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hin ⊢
  match ins, hlen, hin with
  | [], _, _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨63, by decide, fun t => by simp [GateOp.eval, t31 t], Or.inl h31⟩
    · exact ⟨0, by decide, fun t => by simp [GateOp.eval], Or.inl h0⟩
    · exact ⟨63, by decide, fun t => by simp [GateOp.eval, t31 t], Or.inl h31⟩
  | [i], _, hin =>
    obtain ⟨m, hm, hS, hw⟩ := hinv i (hin i (by simp))
    rcases hop with rfl | rfl | rfl
    · exact ⟨m, hm, fun t => by simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval], Or.inl hS⟩
    · exact ⟨m, hm, fun t => by simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval], Or.inl hS⟩
    · refine ⟨63 ^^^ m, (bits32 m hm m hm).2.2, fun t => ?_, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval, Nat.testBit_xor, t31 t]
      · simp only [notHas, List.any_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, rfl⟩
  | [i, j], _, hin =>
    obtain ⟨m, hm, hS, hw⟩ := hinv i (hin i (by simp))
    obtain ⟨n, hn, hT, hv⟩ := hinv j (hin j (by simp))
    rcases hop with rfl | rfl | rfl
    · refine ⟨m &&& n, (bits32 m hm n hn).1, fun t => ?_, Or.inr (Or.inl ⟨(fun h => nomatch h), ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t, hv t]; simp [GateOp.eval, Nat.testBit_and]
      · simp only [aoHas, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, n, mem_elems.mpr ⟨hn, hT⟩, Or.inl rfl⟩
    · refine ⟨m ||| n, (bits32 m hm n hn).2.1, fun t => ?_, Or.inr (Or.inl ⟨(fun h => nomatch h), ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t, hv t]; simp [GateOp.eval, Nat.testBit_or]
      · simp only [aoHas, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, n, mem_elems.mpr ⟨hn, hT⟩, Or.inr rfl⟩
    · refine ⟨63 ^^^ m, (bits32 m hm m hm).2.2, fun t => ?_, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval, Nat.testBit_xor, t31 t]
      · simp only [notHas, List.any_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, rfl⟩
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

theorem sound (A B C : Nat) (hA : A < 64) (hB : B < 64) (hC : C < 64)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∀ (gs : List Gate) (W : Fin 6 → List Bool) (L S k b : Nat),
      (∀ t, (W t).length = L) → S.testBit 63 = true → S.testBit 0 = true →
      (∀ i < L, ∃ m, m < 64 ∧ S.testBit m = true ∧ ∀ t, (W t).getD i false = m.testBit t.val) →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + j) →
      gs.length ≤ k → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b →
      ∀ p q r, p < L + gs.length → q < L + gs.length → r < L + gs.length →
      (∀ t : Fin 6, (gs.foldl stepW (W t)).getD p false = A.testBit t.val ∧
        (gs.foldl stepW (W t)).getD q false = B.testBit t.val ∧
        (gs.foldl stepW (W t)).getD r false = C.testBit t.val) →
      reach A B C k b S = true := by
  intro gs
  induction gs with
  | nil =>
    intro W L S k b _ _ _ hinv _ _ _ _ p q r hp hq hr ht
    simp only [List.length_nil, Nat.add_zero, List.foldl_nil] at hp hq hr ht
    apply reach_hit
    obtain ⟨m1, h1, s1, w1⟩ := hinv p hp
    obtain ⟨m2, h2, s2, w2⟩ := hinv q hq
    obtain ⟨m3, h3, s3, w3⟩ := hinv r hr
    have e1 : m1 = A := uniq32 m1 h1 A hA (fun t => by rw [← w1 t, (ht t).1])
    have e2 : m2 = B := uniq32 m2 h2 B hB (fun t => by rw [← w2 t, (ht t).2.1])
    have e3 : m3 = C := uniq32 m3 h3 C hC (fun t => by rw [← w3 t, (ht t).2.2])
    subst e1 e2 e3
    simp [hit, s1, s2, s3]
  | cons g gs ih =>
    intro W L S k b hlen h31 h0 hinv hfan hrb hk hb p q r hp hq hr ht
    have hg := hfan g (by simp)
    have hin : ∀ i ∈ g.inputs, i < L := by
      intro i hi; have := hrb 0 (by simp) i (by simpa using hi); simpa using this
    obtain ⟨v, hv, hval, hcls⟩ := classify S L W g h31 h0 hinv hg.1 hg.2 hin
    let W' : Fin 6 → List Bool := fun t => stepW (W t) g
    have hlen' : ∀ t, (W' t).length = L + 1 := by intro t; simp [W', stepW, hlen t]
    have hinv' : ∀ i < L + 1, ∃ m, m < 64 ∧ (S ||| 2^v).testBit m = true ∧
        ∀ t, (W' t).getD i false = m.testBit t.val := by
      intro i hi
      by_cases hiL : i < L
      · obtain ⟨m, hm, hS, hw⟩ := hinv i hiL
        refine ⟨m, hm, by rw [testBit_or_pow, hS, Bool.true_or], fun t => ?_⟩
        simp only [W', stepW]
        rw [List.getD_append _ _ _ _ (by rw [hlen t]; exact hiL)]
        exact hw t
      · have hiE : i = L := by omega
        subst hiE
        refine ⟨v, hv, by rw [testBit_or_pow]; simp, fun t => ?_⟩
        simp only [W', stepW]
        rw [List.getD_append_right _ _ _ _ (by rw [hlen t]), hlen t, Nat.sub_self]
        exact hval t
    have hfan' : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hrb' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + 1 + j := by
      intro j hj i hi
      have := hrb (j+1) (by simp; omega) i (by simpa using hi)
      omega
    have h31' : (S ||| 2^v).testBit 63 = true := by rw [testBit_or_pow, h31, Bool.true_or]
    have h00' : (S ||| 2^v).testBit 0 = true := by rw [testBit_or_pow, h0, Bool.true_or]
    simp only [List.length_cons] at hk hp hq hr
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have ht' : ∀ t : Fin 6, (gs.foldl stepW (W' t)).getD p false = A.testBit t.val ∧
        (gs.foldl stepW (W' t)).getD q false = B.testBit t.val ∧
        (gs.foldl stepW (W' t)).getD r false = C.testBit t.val := fun t => ht t
    have key : ∀ b', PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b' →
        reach A B C k b' (S ||| 2^v) = true := fun b' hb' =>
      ih W' (L+1) (S ||| 2^v) k b' hlen' h31' h00' hinv' hfan' hrb' (by omega) hb' p q r
        (by omega) (by omega) (by omega) ht'
    have hbn : g.op = GateOp.not →
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b - 1 ∧ 0 < b := by
      intro hn; simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hb ⊢; omega
    have hbo : g.op ≠ GateOp.not →
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b := by
      intro hn; simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hb ⊢; omega
    have miss_ok : ∀ b', reach A B C k b' (S ||| 2^v) = true → miss A B C S ≤ k + 1 := by
      intro b' hR
      have := miss_step A B C S v hAB hAC hBC
      rcases reach_miss hR with hh | hh
      · have := miss_of_hit hh; omega
      · omega
    simp only [reach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    right
    by_cases hn : g.op = GateOp.not
    · have hR := key (b-1) (hbn hn).1
      refine ⟨miss_ok _ hR, ?_⟩
      by_cases hsv : S.testBit v = true
      · rw [or_pow_self hsv] at hR
        exact Or.inl (Or.inr ⟨(hbn hn).2, hR⟩)
      · right
        rw [List.any_eq_true]
        refine ⟨v, List.mem_range.mpr hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        refine ⟨by simpa using hsv, ?_⟩
        rcases hcls with h | ⟨hn', h⟩ | ⟨_, h⟩
        · exact absurd h hsv
        · exact absurd hn hn'
        · exact Or.inr ⟨⟨(hbn hn).2, h⟩, hR⟩
    · have hR := key b (hbo hn)
      refine ⟨miss_ok _ hR, ?_⟩
      by_cases hsv : S.testBit v = true
      · rw [or_pow_self hsv] at hR
        exact Or.inl (Or.inl hR)
      · right
        rw [List.any_eq_true]
        refine ⟨v, List.mem_range.mpr hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        refine ⟨by simpa using hsv, ?_⟩
        rcases hcls with h | ⟨_, h⟩ | ⟨hn', h⟩
        · exact absurd h hsv
        · exact Or.inl ⟨h, hR⟩
        · exact absurd hn' hn

def S0 : Nat := 2^62 ||| 2^60 ||| 2^56 ||| 2^48 ||| 2^32 ||| 2^0 ||| 2^63

theorem c3 : reach 34 36 50 4 2 S0 = false := by decide +kernel

theorem c4 : reach 34 36 50 4 1 S0 = false := by decide +kernel

theorem c5 : reach 34 36 50 4 1 (S0 ||| 2^1) = false := by decide +kernel

theorem c2_d1 : body 34 36 50 4 2 1 S0 1 = false := by
  have e : body 34 36 50 4 2 1 S0 1 = (!(S0).testBit 1 && ((aoHas S0 1 && reach 34 36 50 4 2 (S0 ||| 2^1)) ||
      (decide (0 < 2) && notHas S0 1 && reach 34 36 50 4 1 (S0 ||| 2^1)))) := rfl
  rw [c5] at e
  exact e.trans (by decide +kernel)

theorem c6 : reach 34 36 50 4 1 (S0 ||| 2^3) = false := by decide +kernel

theorem c2_d3 : body 34 36 50 4 2 1 S0 3 = false := by
  have e : body 34 36 50 4 2 1 S0 3 = (!(S0).testBit 3 && ((aoHas S0 3 && reach 34 36 50 4 2 (S0 ||| 2^3)) ||
      (decide (0 < 2) && notHas S0 3 && reach 34 36 50 4 1 (S0 ||| 2^3)))) := rfl
  rw [c6] at e
  exact e.trans (by decide +kernel)

theorem c7 : reach 34 36 50 4 1 (S0 ||| 2^7) = false := by decide +kernel

theorem c2_d7 : body 34 36 50 4 2 1 S0 7 = false := by
  have e : body 34 36 50 4 2 1 S0 7 = (!(S0).testBit 7 && ((aoHas S0 7 && reach 34 36 50 4 2 (S0 ||| 2^7)) ||
      (decide (0 < 2) && notHas S0 7 && reach 34 36 50 4 1 (S0 ||| 2^7)))) := rfl
  rw [c7] at e
  exact e.trans (by decide +kernel)

theorem c8 : reach 34 36 50 4 1 (S0 ||| 2^15) = false := by decide +kernel

theorem c2_d15 : body 34 36 50 4 2 1 S0 15 = false := by
  have e : body 34 36 50 4 2 1 S0 15 = (!(S0).testBit 15 && ((aoHas S0 15 && reach 34 36 50 4 2 (S0 ||| 2^15)) ||
      (decide (0 < 2) && notHas S0 15 && reach 34 36 50 4 1 (S0 ||| 2^15)))) := rfl
  rw [c8] at e
  exact e.trans (by decide +kernel)

theorem c9 : reach 34 36 50 4 1 (S0 ||| 2^31) = false := by decide +kernel

theorem c2_d31 : body 34 36 50 4 2 1 S0 31 = false := by
  have e : body 34 36 50 4 2 1 S0 31 = (!(S0).testBit 31 && ((aoHas S0 31 && reach 34 36 50 4 2 (S0 ||| 2^31)) ||
      (decide (0 < 2) && notHas S0 31 && reach 34 36 50 4 1 (S0 ||| 2^31)))) := rfl
  rw [c9] at e
  exact e.trans (by decide +kernel)

theorem c2_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 31 || !body 34 36 50 4 2 1 S0 v) = true := by decide +kernel

theorem c2_a : ∀ v, v < 64 → body 34 36 50 4 2 1 S0 v = false := by
  intro v hv
  have h := List.all_eq_true.mp c2_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c2_d1
  by_cases h3 : v = 3
  · subst h3; exact c2_d3
  by_cases h7 : v = 7
  · subst h7; exact c2_d7
  by_cases h15 : v = 15
  · subst h15; exact c2_d15
  by_cases h31 : v = 31
  · subst h31; exact c2_d31
  simpa [h1, h3, h7, h15, h31] using h

theorem c2 : reach 34 36 50 5 2 S0 = false := by
  have e := reach_succ 34 36 50 4 2 1 S0 rfl
  have h : (List.range 64).any (body 34 36 50 4 2 1 S0) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c2_a v (List.mem_range.mp hv)]; decide
  rw [c3, c4, h] at e
  exact e.trans (by decide +kernel)

theorem c10 : reach 34 36 50 5 1 S0 = false := by decide +kernel

theorem c12 : reach 34 36 50 4 0 (S0 ||| 2^1) = false := by decide +kernel

theorem c13 : reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^3) = false := by decide +kernel

theorem c11_d3 : body 34 36 50 4 1 0 (S0 ||| 2^1) 3 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 3 = (!((S0 ||| 2^1)).testBit 3 && ((aoHas (S0 ||| 2^1) 3 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 3 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^3)))) := rfl
  rw [c13] at e
  exact e.trans (by decide +kernel)

theorem c14 : reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^7) = false := by decide +kernel

theorem c11_d7 : body 34 36 50 4 1 0 (S0 ||| 2^1) 7 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 7 = (!((S0 ||| 2^1)).testBit 7 && ((aoHas (S0 ||| 2^1) 7 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 7 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^7)))) := rfl
  rw [c14] at e
  exact e.trans (by decide +kernel)

theorem c15 : reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^15) = false := by decide +kernel

theorem c11_d15 : body 34 36 50 4 1 0 (S0 ||| 2^1) 15 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 15 = (!((S0 ||| 2^1)).testBit 15 && ((aoHas (S0 ||| 2^1) 15 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 15 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^15)))) := rfl
  rw [c15] at e
  exact e.trans (by decide +kernel)

theorem c16 : reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^31) = false := by decide +kernel

theorem c11_d31 : body 34 36 50 4 1 0 (S0 ||| 2^1) 31 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 31 = (!((S0 ||| 2^1)).testBit 31 && ((aoHas (S0 ||| 2^1) 31 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 31 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^31)))) := rfl
  rw [c16] at e
  exact e.trans (by decide +kernel)

theorem c17 : reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^33) = false := by decide +kernel

theorem c11_d33 : body 34 36 50 4 1 0 (S0 ||| 2^1) 33 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 33 = (!((S0 ||| 2^1)).testBit 33 && ((aoHas (S0 ||| 2^1) 33 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^33)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 33 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^33)))) := rfl
  rw [c17] at e
  exact e.trans (by decide +kernel)

theorem c18 : reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^49) = false := by decide +kernel

theorem c11_d49 : body 34 36 50 4 1 0 (S0 ||| 2^1) 49 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 49 = (!((S0 ||| 2^1)).testBit 49 && ((aoHas (S0 ||| 2^1) 49 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^49)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 49 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^49)))) := rfl
  rw [c18] at e
  exact e.trans (by decide +kernel)

theorem c19 : reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^57) = false := by decide +kernel

theorem c11_d57 : body 34 36 50 4 1 0 (S0 ||| 2^1) 57 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 57 = (!((S0 ||| 2^1)).testBit 57 && ((aoHas (S0 ||| 2^1) 57 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^57)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 57 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^57)))) := rfl
  rw [c19] at e
  exact e.trans (by decide +kernel)

theorem c20 : reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^61) = false := by decide +kernel

theorem c11_d61 : body 34 36 50 4 1 0 (S0 ||| 2^1) 61 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^1) 61 = (!((S0 ||| 2^1)).testBit 61 && ((aoHas (S0 ||| 2^1) 61 && reach 34 36 50 4 1 ((S0 ||| 2^1) ||| 2^61)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 61 && reach 34 36 50 4 0 ((S0 ||| 2^1) ||| 2^61)))) := rfl
  rw [c20] at e
  exact e.trans (by decide +kernel)

theorem c11_o : (List.range 64).all (fun v => v == 3 || v == 7 || v == 15 || v == 31 || v == 33 || v == 49 || v == 57 || v == 61 || !body 34 36 50 4 1 0 (S0 ||| 2^1) v) = true := by decide +kernel

theorem c11_a : ∀ v, v < 64 → body 34 36 50 4 1 0 (S0 ||| 2^1) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c11_o v (List.mem_range.mpr hv)
  by_cases h3 : v = 3
  · subst h3; exact c11_d3
  by_cases h7 : v = 7
  · subst h7; exact c11_d7
  by_cases h15 : v = 15
  · subst h15; exact c11_d15
  by_cases h31 : v = 31
  · subst h31; exact c11_d31
  by_cases h33 : v = 33
  · subst h33; exact c11_d33
  by_cases h49 : v = 49
  · subst h49; exact c11_d49
  by_cases h57 : v = 57
  · subst h57; exact c11_d57
  by_cases h61 : v = 61
  · subst h61; exact c11_d61
  simpa [h3, h7, h15, h31, h33, h49, h57, h61] using h

theorem c11 : reach 34 36 50 5 1 (S0 ||| 2^1) = false := by
  have e := reach_succ 34 36 50 4 1 0 (S0 ||| 2^1) rfl
  have h : (List.range 64).any (body 34 36 50 4 1 0 (S0 ||| 2^1)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c11_a v (List.mem_range.mp hv)]; decide
  rw [c5, c12, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d1 : body 34 36 50 5 2 1 S0 1 = false := by
  have e : body 34 36 50 5 2 1 S0 1 = (!(S0).testBit 1 && ((aoHas S0 1 && reach 34 36 50 5 2 (S0 ||| 2^1)) ||
      (decide (0 < 2) && notHas S0 1 && reach 34 36 50 5 1 (S0 ||| 2^1)))) := rfl
  rw [c11] at e
  exact e.trans (by decide +kernel)

theorem c22 : reach 34 36 50 4 0 (S0 ||| 2^3) = false := by decide +kernel

theorem c23 : reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^1) = false := by decide +kernel

theorem c21_d1 : body 34 36 50 4 1 0 (S0 ||| 2^3) 1 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 1 = (!((S0 ||| 2^3)).testBit 1 && ((aoHas (S0 ||| 2^3) 1 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 1 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^1)))) := rfl
  rw [c23] at e
  exact e.trans (by decide +kernel)

theorem c25 : reach 34 36 50 3 1 ((S0 ||| 2^3) ||| 2^2) = false := by decide +kernel

theorem c26 : reach 34 36 50 3 0 ((S0 ||| 2^3) ||| 2^2) = false := by decide +kernel

theorem c27 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^1) = false := by decide +kernel

theorem c24_d1 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 1 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 1 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 1 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 1 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 1 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^1)))) := rfl
  rw [c27] at e
  exact e.trans (by decide +kernel)

theorem c28 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^7) = false := by decide +kernel

theorem c24_d7 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 7 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 7 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 7 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 7 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 7 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^7)))) := rfl
  rw [c28] at e
  exact e.trans (by decide +kernel)

theorem c29 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^15) = false := by decide +kernel

theorem c24_d15 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 15 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 15 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 15 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 15 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 15 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^15)))) := rfl
  rw [c29] at e
  exact e.trans (by decide +kernel)

theorem c30 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^31) = false := by decide +kernel

theorem c24_d31 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 31 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 31 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 31 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 31 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 31 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^31)))) := rfl
  rw [c30] at e
  exact e.trans (by decide +kernel)

theorem c32 : reach 34 36 50 2 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) = false := by decide +kernel

theorem c33 : reach 34 36 50 2 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) = false := by decide +kernel

theorem c34 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^1) = false := by decide +kernel

theorem c31_d1 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 1 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 1 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 1 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 1 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 1 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^1)))) := rfl
  rw [c34] at e
  exact e.trans (by decide +kernel)

theorem c35 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^7) = false := by decide +kernel

theorem c31_d7 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 7 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 7 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 7 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 7 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 7 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^7)))) := rfl
  rw [c35] at e
  exact e.trans (by decide +kernel)

theorem c36 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^15) = false := by decide +kernel

theorem c31_d15 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 15 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 15 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 15 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 15 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 15 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^15)))) := rfl
  rw [c36] at e
  exact e.trans (by decide +kernel)

theorem c37 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^29) = false := by decide +kernel

theorem c31_d29 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 29 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 29 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 29 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 29 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^29)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 29 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^29)))) := rfl
  rw [c37] at e
  exact e.trans (by decide +kernel)

theorem c38 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^31) = false := by decide +kernel

theorem c31_d31 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 31 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 31 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 31 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 31 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 31 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^31)))) := rfl
  rw [c38] at e
  exact e.trans (by decide +kernel)

theorem c39 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^35) = false := by decide +kernel

theorem c31_d35 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 35 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 35 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 35 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 35 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^35)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 35 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^35)))) := rfl
  rw [c39] at e
  exact e.trans (by decide +kernel)

theorem c40 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^50) = false := by decide +kernel

theorem c31_d50 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 50 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 50 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 50 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 50 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^50)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 50 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^50)))) := rfl
  rw [c40] at e
  exact e.trans (by decide +kernel)

theorem c41 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^51) = false := by decide +kernel

theorem c31_d51 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 51 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 51 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 51 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 51 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^51)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 51 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^51)))) := rfl
  rw [c41] at e
  exact e.trans (by decide +kernel)

theorem c42 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^58) = false := by decide +kernel

theorem c31_d58 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 58 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 58 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 58 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 58 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^58)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 58 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^58)))) := rfl
  rw [c42] at e
  exact e.trans (by decide +kernel)

theorem c43 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^59) = false := by decide +kernel

theorem c31_d59 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 59 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 59 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 59 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 59 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^59)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 59 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^59)))) := rfl
  rw [c43] at e
  exact e.trans (by decide +kernel)

theorem c44 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^61) = false := by decide +kernel

theorem c31_d61 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 61 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 61 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^34)).testBit 61 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 61 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^61)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^34) 61 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^34) ||| 2^61)))) := rfl
  rw [c44] at e
  exact e.trans (by decide +kernel)

theorem c31_o : (List.range 64).all (fun v => v == 1 || v == 7 || v == 15 || v == 29 || v == 31 || v == 35 || v == 50 || v == 51 || v == 58 || v == 59 || v == 61 || !body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) v) = true := by decide +kernel

theorem c31_a : ∀ v, v < 64 → body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c31_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c31_d1
  by_cases h7 : v = 7
  · subst h7; exact c31_d7
  by_cases h15 : v = 15
  · subst h15; exact c31_d15
  by_cases h29 : v = 29
  · subst h29; exact c31_d29
  by_cases h31 : v = 31
  · subst h31; exact c31_d31
  by_cases h35 : v = 35
  · subst h35; exact c31_d35
  by_cases h50 : v = 50
  · subst h50; exact c31_d50
  by_cases h51 : v = 51
  · subst h51; exact c31_d51
  by_cases h58 : v = 58
  · subst h58; exact c31_d58
  by_cases h59 : v = 59
  · subst h59; exact c31_d59
  by_cases h61 : v = 61
  · subst h61; exact c31_d61
  simpa [h1, h7, h15, h29, h31, h35, h50, h51, h58, h59, h61] using h

theorem c31 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) = false := by
  have e := reach_succ 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34) rfl
  have h : (List.range 64).any (body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c31_a v (List.mem_range.mp hv)]; decide
  rw [c32, c33, h] at e
  exact e.trans (by decide +kernel)

theorem c24_d34 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 34 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 34 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 34 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 34 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^34)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 34 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^34)))) := rfl
  rw [c31] at e
  exact e.trans (by decide +kernel)

theorem c45 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^35) = false := by decide +kernel

theorem c24_d35 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 35 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 35 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 35 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 35 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^35)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 35 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^35)))) := rfl
  rw [c45] at e
  exact e.trans (by decide +kernel)

theorem c47 : reach 34 36 50 2 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) = false := by decide +kernel

theorem c48 : reach 34 36 50 2 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) = false := by decide +kernel

theorem c49 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^1) = false := by decide +kernel

theorem c46_d1 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 1 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 1 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 1 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 1 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 1 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^1)))) := rfl
  rw [c49] at e
  exact e.trans (by decide +kernel)

theorem c50 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^7) = false := by decide +kernel

theorem c46_d7 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 7 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 7 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 7 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 7 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 7 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^7)))) := rfl
  rw [c50] at e
  exact e.trans (by decide +kernel)

theorem c51 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^13) = false := by decide +kernel

theorem c46_d13 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 13 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 13 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 13 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 13 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^13)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 13 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^13)))) := rfl
  rw [c51] at e
  exact e.trans (by decide +kernel)

theorem c52 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^15) = false := by decide +kernel

theorem c46_d15 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 15 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 15 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 15 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 15 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 15 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^15)))) := rfl
  rw [c52] at e
  exact e.trans (by decide +kernel)

theorem c53 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^31) = false := by decide +kernel

theorem c46_d31 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 31 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 31 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 31 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 31 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 31 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^31)))) := rfl
  rw [c53] at e
  exact e.trans (by decide +kernel)

theorem c54 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^34) = false := by decide +kernel

theorem c46_d34 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 34 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 34 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 34 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 34 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^34)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 34 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^34)))) := rfl
  rw [c54] at e
  exact e.trans (by decide +kernel)

theorem c55 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^35) = false := by decide +kernel

theorem c46_d35 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 35 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 35 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 35 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 35 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^35)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 35 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^35)))) := rfl
  rw [c55] at e
  exact e.trans (by decide +kernel)

theorem c56 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^51) = false := by decide +kernel

theorem c46_d51 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 51 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 51 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 51 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 51 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^51)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 51 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^51)))) := rfl
  rw [c56] at e
  exact e.trans (by decide +kernel)

theorem c57 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^58) = false := by decide +kernel

theorem c46_d58 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 58 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 58 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 58 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 58 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^58)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 58 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^58)))) := rfl
  rw [c57] at e
  exact e.trans (by decide +kernel)

theorem c58 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^59) = false := by decide +kernel

theorem c46_d59 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 59 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 59 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 59 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 59 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^59)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 59 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^59)))) := rfl
  rw [c58] at e
  exact e.trans (by decide +kernel)

theorem c59 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^61) = false := by decide +kernel

theorem c46_d61 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 61 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 61 = (!((((S0 ||| 2^3) ||| 2^2) ||| 2^50)).testBit 61 && ((aoHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 61 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^61)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^2) ||| 2^50) 61 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^2) ||| 2^50) ||| 2^61)))) := rfl
  rw [c59] at e
  exact e.trans (by decide +kernel)

theorem c46_o : (List.range 64).all (fun v => v == 1 || v == 7 || v == 13 || v == 15 || v == 31 || v == 34 || v == 35 || v == 51 || v == 58 || v == 59 || v == 61 || !body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) v) = true := by decide +kernel

theorem c46_a : ∀ v, v < 64 → body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c46_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c46_d1
  by_cases h7 : v = 7
  · subst h7; exact c46_d7
  by_cases h13 : v = 13
  · subst h13; exact c46_d13
  by_cases h15 : v = 15
  · subst h15; exact c46_d15
  by_cases h31 : v = 31
  · subst h31; exact c46_d31
  by_cases h34 : v = 34
  · subst h34; exact c46_d34
  by_cases h35 : v = 35
  · subst h35; exact c46_d35
  by_cases h51 : v = 51
  · subst h51; exact c46_d51
  by_cases h58 : v = 58
  · subst h58; exact c46_d58
  by_cases h59 : v = 59
  · subst h59; exact c46_d59
  by_cases h61 : v = 61
  · subst h61; exact c46_d61
  simpa [h1, h7, h13, h15, h31, h34, h35, h51, h58, h59, h61] using h

theorem c46 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) = false := by
  have e := reach_succ 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50) rfl
  have h : (List.range 64).any (body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c46_a v (List.mem_range.mp hv)]; decide
  rw [c47, c48, h] at e
  exact e.trans (by decide +kernel)

theorem c24_d50 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 50 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 50 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 50 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 50 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^50)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 50 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^50)))) := rfl
  rw [c46] at e
  exact e.trans (by decide +kernel)

theorem c60 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^51) = false := by decide +kernel

theorem c24_d51 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 51 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 51 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 51 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 51 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^51)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 51 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^51)))) := rfl
  rw [c60] at e
  exact e.trans (by decide +kernel)

theorem c61 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^58) = false := by decide +kernel

theorem c24_d58 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 58 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 58 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 58 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 58 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^58)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 58 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^58)))) := rfl
  rw [c61] at e
  exact e.trans (by decide +kernel)

theorem c62 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^59) = false := by decide +kernel

theorem c24_d59 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 59 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 59 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 59 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 59 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^59)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 59 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^59)))) := rfl
  rw [c62] at e
  exact e.trans (by decide +kernel)

theorem c63 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^61) = false := by decide +kernel

theorem c24_d61 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 61 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) 61 = (!(((S0 ||| 2^3) ||| 2^2)).testBit 61 && ((aoHas ((S0 ||| 2^3) ||| 2^2) 61 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^2) ||| 2^61)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^2) 61 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^2) ||| 2^61)))) := rfl
  rw [c63] at e
  exact e.trans (by decide +kernel)

theorem c24_o : (List.range 64).all (fun v => v == 1 || v == 7 || v == 15 || v == 31 || v == 34 || v == 35 || v == 50 || v == 51 || v == 58 || v == 59 || v == 61 || !body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) v) = true := by decide +kernel

theorem c24_a : ∀ v, v < 64 → body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c24_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c24_d1
  by_cases h7 : v = 7
  · subst h7; exact c24_d7
  by_cases h15 : v = 15
  · subst h15; exact c24_d15
  by_cases h31 : v = 31
  · subst h31; exact c24_d31
  by_cases h34 : v = 34
  · subst h34; exact c24_d34
  by_cases h35 : v = 35
  · subst h35; exact c24_d35
  by_cases h50 : v = 50
  · subst h50; exact c24_d50
  by_cases h51 : v = 51
  · subst h51; exact c24_d51
  by_cases h58 : v = 58
  · subst h58; exact c24_d58
  by_cases h59 : v = 59
  · subst h59; exact c24_d59
  by_cases h61 : v = 61
  · subst h61; exact c24_d61
  simpa [h1, h7, h15, h31, h34, h35, h50, h51, h58, h59, h61] using h

theorem c24 : reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^2) = false := by
  have e := reach_succ 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2) rfl
  have h : (List.range 64).any (body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^2)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c24_a v (List.mem_range.mp hv)]; decide
  rw [c25, c26, h] at e
  exact e.trans (by decide +kernel)

theorem c21_d2 : body 34 36 50 4 1 0 (S0 ||| 2^3) 2 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 2 = (!((S0 ||| 2^3)).testBit 2 && ((aoHas (S0 ||| 2^3) 2 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^2)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 2 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^2)))) := rfl
  rw [c24] at e
  exact e.trans (by decide +kernel)

theorem c64 : reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^7) = false := by decide +kernel

theorem c21_d7 : body 34 36 50 4 1 0 (S0 ||| 2^3) 7 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 7 = (!((S0 ||| 2^3)).testBit 7 && ((aoHas (S0 ||| 2^3) 7 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 7 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^7)))) := rfl
  rw [c64] at e
  exact e.trans (by decide +kernel)

theorem c65 : reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^15) = false := by decide +kernel

theorem c21_d15 : body 34 36 50 4 1 0 (S0 ||| 2^3) 15 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 15 = (!((S0 ||| 2^3)).testBit 15 && ((aoHas (S0 ||| 2^3) 15 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 15 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^15)))) := rfl
  rw [c65] at e
  exact e.trans (by decide +kernel)

theorem c66 : reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^31) = false := by decide +kernel

theorem c21_d31 : body 34 36 50 4 1 0 (S0 ||| 2^3) 31 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 31 = (!((S0 ||| 2^3)).testBit 31 && ((aoHas (S0 ||| 2^3) 31 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 31 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^31)))) := rfl
  rw [c66] at e
  exact e.trans (by decide +kernel)

theorem c68 : reach 34 36 50 3 1 ((S0 ||| 2^3) ||| 2^35) = false := by decide +kernel

theorem c69 : reach 34 36 50 3 0 ((S0 ||| 2^3) ||| 2^35) = false := by decide +kernel

theorem c70 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^1) = false := by decide +kernel

theorem c67_d1 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 1 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 1 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 1 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 1 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 1 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^1)))) := rfl
  rw [c70] at e
  exact e.trans (by decide +kernel)

theorem c71 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^2) = false := by decide +kernel

theorem c67_d2 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 2 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 2 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 2 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 2 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^2)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 2 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^2)))) := rfl
  rw [c71] at e
  exact e.trans (by decide +kernel)

theorem c72 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^7) = false := by decide +kernel

theorem c67_d7 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 7 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 7 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 7 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 7 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 7 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^7)))) := rfl
  rw [c72] at e
  exact e.trans (by decide +kernel)

theorem c73 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^15) = false := by decide +kernel

theorem c67_d15 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 15 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 15 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 15 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 15 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 15 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^15)))) := rfl
  rw [c73] at e
  exact e.trans (by decide +kernel)

theorem c74 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^28) = false := by decide +kernel

theorem c67_d28 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 28 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 28 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 28 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 28 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^28)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 28 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^28)))) := rfl
  rw [c74] at e
  exact e.trans (by decide +kernel)

theorem c75 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^31) = false := by decide +kernel

theorem c67_d31 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 31 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 31 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 31 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 31 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 31 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^31)))) := rfl
  rw [c75] at e
  exact e.trans (by decide +kernel)

theorem c77 : reach 34 36 50 2 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) = false := by decide +kernel

theorem c78 : reach 34 36 50 2 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) = false := by decide +kernel

theorem c79 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^1) = false := by decide +kernel

theorem c76_d1 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 1 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 1 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 1 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 1 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 1 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^1)))) := rfl
  rw [c79] at e
  exact e.trans (by decide +kernel)

theorem c80 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^2) = false := by decide +kernel

theorem c76_d2 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 2 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 2 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 2 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 2 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^2)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 2 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^2)))) := rfl
  rw [c80] at e
  exact e.trans (by decide +kernel)

theorem c81 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^7) = false := by decide +kernel

theorem c76_d7 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 7 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 7 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 7 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 7 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 7 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^7)))) := rfl
  rw [c81] at e
  exact e.trans (by decide +kernel)

theorem c82 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^15) = false := by decide +kernel

theorem c76_d15 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 15 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 15 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 15 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 15 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 15 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^15)))) := rfl
  rw [c82] at e
  exact e.trans (by decide +kernel)

theorem c83 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^28) = false := by decide +kernel

theorem c76_d28 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 28 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 28 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 28 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 28 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^28)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 28 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^28)))) := rfl
  rw [c83] at e
  exact e.trans (by decide +kernel)

theorem c84 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^29) = false := by decide +kernel

theorem c76_d29 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 29 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 29 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 29 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 29 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^29)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 29 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^29)))) := rfl
  rw [c84] at e
  exact e.trans (by decide +kernel)

theorem c85 : reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^31) = false := by decide +kernel

theorem c76_d31 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 31 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 31 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 31 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 31 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 31 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^31)))) := rfl
  rw [c85] at e
  exact e.trans (by decide +kernel)

theorem c86 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^50) = false := by decide +kernel

theorem c76_d50 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 50 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 50 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 50 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 50 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^50)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 50 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^50)))) := rfl
  rw [c86] at e
  exact e.trans (by decide +kernel)

theorem c87 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^51) = false := by decide +kernel

theorem c76_d51 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 51 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 51 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 51 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 51 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^51)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 51 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^51)))) := rfl
  rw [c87] at e
  exact e.trans (by decide +kernel)

theorem c88 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^58) = false := by decide +kernel

theorem c76_d58 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 58 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 58 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 58 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 58 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^58)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 58 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^58)))) := rfl
  rw [c88] at e
  exact e.trans (by decide +kernel)

theorem c89 : reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^59) = false := by decide +kernel

theorem c76_d59 : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 59 = false := by
  have e : body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 59 = (!((((S0 ||| 2^3) ||| 2^35) ||| 2^34)).testBit 59 && ((aoHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 59 && reach 34 36 50 2 1 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^59)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^3) ||| 2^35) ||| 2^34) 59 && reach 34 36 50 2 0 ((((S0 ||| 2^3) ||| 2^35) ||| 2^34) ||| 2^59)))) := rfl
  rw [c89] at e
  exact e.trans (by decide +kernel)

theorem c76_o : (List.range 64).all (fun v => v == 1 || v == 2 || v == 7 || v == 15 || v == 28 || v == 29 || v == 31 || v == 50 || v == 51 || v == 58 || v == 59 || !body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) v) = true := by decide +kernel

theorem c76_a : ∀ v, v < 64 → body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c76_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c76_d1
  by_cases h2 : v = 2
  · subst h2; exact c76_d2
  by_cases h7 : v = 7
  · subst h7; exact c76_d7
  by_cases h15 : v = 15
  · subst h15; exact c76_d15
  by_cases h28 : v = 28
  · subst h28; exact c76_d28
  by_cases h29 : v = 29
  · subst h29; exact c76_d29
  by_cases h31 : v = 31
  · subst h31; exact c76_d31
  by_cases h50 : v = 50
  · subst h50; exact c76_d50
  by_cases h51 : v = 51
  · subst h51; exact c76_d51
  by_cases h58 : v = 58
  · subst h58; exact c76_d58
  by_cases h59 : v = 59
  · subst h59; exact c76_d59
  simpa [h1, h2, h7, h15, h28, h29, h31, h50, h51, h58, h59] using h

theorem c76 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) = false := by
  have e := reach_succ 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34) rfl
  have h : (List.range 64).any (body 34 36 50 2 1 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c76_a v (List.mem_range.mp hv)]; decide
  rw [c77, c78, h] at e
  exact e.trans (by decide +kernel)

theorem c67_d34 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 34 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 34 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 34 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 34 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^34)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 34 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^34)))) := rfl
  rw [c76] at e
  exact e.trans (by decide +kernel)

theorem c90 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^51) = false := by decide +kernel

theorem c67_d51 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 51 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 51 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 51 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 51 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^51)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 51 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^51)))) := rfl
  rw [c90] at e
  exact e.trans (by decide +kernel)

theorem c91 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^59) = false := by decide +kernel

theorem c67_d59 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 59 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) 59 = (!(((S0 ||| 2^3) ||| 2^35)).testBit 59 && ((aoHas ((S0 ||| 2^3) ||| 2^35) 59 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^35) ||| 2^59)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^35) 59 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^35) ||| 2^59)))) := rfl
  rw [c91] at e
  exact e.trans (by decide +kernel)

theorem c67_o : (List.range 64).all (fun v => v == 1 || v == 2 || v == 7 || v == 15 || v == 28 || v == 31 || v == 34 || v == 51 || v == 59 || !body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) v) = true := by decide +kernel

theorem c67_a : ∀ v, v < 64 → body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c67_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c67_d1
  by_cases h2 : v = 2
  · subst h2; exact c67_d2
  by_cases h7 : v = 7
  · subst h7; exact c67_d7
  by_cases h15 : v = 15
  · subst h15; exact c67_d15
  by_cases h28 : v = 28
  · subst h28; exact c67_d28
  by_cases h31 : v = 31
  · subst h31; exact c67_d31
  by_cases h34 : v = 34
  · subst h34; exact c67_d34
  by_cases h51 : v = 51
  · subst h51; exact c67_d51
  by_cases h59 : v = 59
  · subst h59; exact c67_d59
  simpa [h1, h2, h7, h15, h28, h31, h34, h51, h59] using h

theorem c67 : reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^35) = false := by
  have e := reach_succ 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35) rfl
  have h : (List.range 64).any (body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^35)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c67_a v (List.mem_range.mp hv)]; decide
  rw [c68, c69, h] at e
  exact e.trans (by decide +kernel)

theorem c21_d35 : body 34 36 50 4 1 0 (S0 ||| 2^3) 35 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 35 = (!((S0 ||| 2^3)).testBit 35 && ((aoHas (S0 ||| 2^3) 35 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^35)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 35 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^35)))) := rfl
  rw [c67] at e
  exact e.trans (by decide +kernel)

theorem c93 : reach 34 36 50 3 1 ((S0 ||| 2^3) ||| 2^51) = false := by decide +kernel

theorem c94 : reach 34 36 50 3 0 ((S0 ||| 2^3) ||| 2^51) = false := by decide +kernel

theorem c95 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^1) = false := by decide +kernel

theorem c92_d1 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 1 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 1 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 1 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 1 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 1 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^1)))) := rfl
  rw [c95] at e
  exact e.trans (by decide +kernel)

theorem c96 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^2) = false := by decide +kernel

theorem c92_d2 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 2 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 2 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 2 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 2 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^2)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 2 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^2)))) := rfl
  rw [c96] at e
  exact e.trans (by decide +kernel)

theorem c97 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^7) = false := by decide +kernel

theorem c92_d7 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 7 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 7 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 7 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 7 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 7 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^7)))) := rfl
  rw [c97] at e
  exact e.trans (by decide +kernel)

theorem c98 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^12) = false := by decide +kernel

theorem c92_d12 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 12 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 12 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 12 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 12 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^12)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 12 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^12)))) := rfl
  rw [c98] at e
  exact e.trans (by decide +kernel)

theorem c99 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^15) = false := by decide +kernel

theorem c92_d15 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 15 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 15 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 15 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 15 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 15 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^15)))) := rfl
  rw [c99] at e
  exact e.trans (by decide +kernel)

theorem c100 : reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^31) = false := by decide +kernel

theorem c92_d31 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 31 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 31 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 31 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 31 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 31 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^31)))) := rfl
  rw [c100] at e
  exact e.trans (by decide +kernel)

theorem c101 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^35) = false := by decide +kernel

theorem c92_d35 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 35 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 35 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 35 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 35 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^35)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 35 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^35)))) := rfl
  rw [c101] at e
  exact e.trans (by decide +kernel)

theorem c102 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^50) = false := by decide +kernel

theorem c92_d50 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 50 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 50 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 50 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 50 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^50)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 50 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^50)))) := rfl
  rw [c102] at e
  exact e.trans (by decide +kernel)

theorem c103 : reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^59) = false := by decide +kernel

theorem c92_d59 : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 59 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) 59 = (!(((S0 ||| 2^3) ||| 2^51)).testBit 59 && ((aoHas ((S0 ||| 2^3) ||| 2^51) 59 && reach 34 36 50 3 1 (((S0 ||| 2^3) ||| 2^51) ||| 2^59)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^3) ||| 2^51) 59 && reach 34 36 50 3 0 (((S0 ||| 2^3) ||| 2^51) ||| 2^59)))) := rfl
  rw [c103] at e
  exact e.trans (by decide +kernel)

theorem c92_o : (List.range 64).all (fun v => v == 1 || v == 2 || v == 7 || v == 12 || v == 15 || v == 31 || v == 35 || v == 50 || v == 59 || !body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) v) = true := by decide +kernel

theorem c92_a : ∀ v, v < 64 → body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c92_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c92_d1
  by_cases h2 : v = 2
  · subst h2; exact c92_d2
  by_cases h7 : v = 7
  · subst h7; exact c92_d7
  by_cases h12 : v = 12
  · subst h12; exact c92_d12
  by_cases h15 : v = 15
  · subst h15; exact c92_d15
  by_cases h31 : v = 31
  · subst h31; exact c92_d31
  by_cases h35 : v = 35
  · subst h35; exact c92_d35
  by_cases h50 : v = 50
  · subst h50; exact c92_d50
  by_cases h59 : v = 59
  · subst h59; exact c92_d59
  simpa [h1, h2, h7, h12, h15, h31, h35, h50, h59] using h

theorem c92 : reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^51) = false := by
  have e := reach_succ 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51) rfl
  have h : (List.range 64).any (body 34 36 50 3 1 0 ((S0 ||| 2^3) ||| 2^51)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c92_a v (List.mem_range.mp hv)]; decide
  rw [c93, c94, h] at e
  exact e.trans (by decide +kernel)

theorem c21_d51 : body 34 36 50 4 1 0 (S0 ||| 2^3) 51 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 51 = (!((S0 ||| 2^3)).testBit 51 && ((aoHas (S0 ||| 2^3) 51 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^51)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 51 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^51)))) := rfl
  rw [c92] at e
  exact e.trans (by decide +kernel)

theorem c104 : reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^59) = false := by decide +kernel

theorem c21_d59 : body 34 36 50 4 1 0 (S0 ||| 2^3) 59 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^3) 59 = (!((S0 ||| 2^3)).testBit 59 && ((aoHas (S0 ||| 2^3) 59 && reach 34 36 50 4 1 ((S0 ||| 2^3) ||| 2^59)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 59 && reach 34 36 50 4 0 ((S0 ||| 2^3) ||| 2^59)))) := rfl
  rw [c104] at e
  exact e.trans (by decide +kernel)

theorem c21_o : (List.range 64).all (fun v => v == 1 || v == 2 || v == 7 || v == 15 || v == 31 || v == 35 || v == 51 || v == 59 || !body 34 36 50 4 1 0 (S0 ||| 2^3) v) = true := by decide +kernel

theorem c21_a : ∀ v, v < 64 → body 34 36 50 4 1 0 (S0 ||| 2^3) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c21_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c21_d1
  by_cases h2 : v = 2
  · subst h2; exact c21_d2
  by_cases h7 : v = 7
  · subst h7; exact c21_d7
  by_cases h15 : v = 15
  · subst h15; exact c21_d15
  by_cases h31 : v = 31
  · subst h31; exact c21_d31
  by_cases h35 : v = 35
  · subst h35; exact c21_d35
  by_cases h51 : v = 51
  · subst h51; exact c21_d51
  by_cases h59 : v = 59
  · subst h59; exact c21_d59
  simpa [h1, h2, h7, h15, h31, h35, h51, h59] using h

theorem c21 : reach 34 36 50 5 1 (S0 ||| 2^3) = false := by
  have e := reach_succ 34 36 50 4 1 0 (S0 ||| 2^3) rfl
  have h : (List.range 64).any (body 34 36 50 4 1 0 (S0 ||| 2^3)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c21_a v (List.mem_range.mp hv)]; decide
  rw [c6, c22, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d3 : body 34 36 50 5 2 1 S0 3 = false := by
  have e : body 34 36 50 5 2 1 S0 3 = (!(S0).testBit 3 && ((aoHas S0 3 && reach 34 36 50 5 2 (S0 ||| 2^3)) ||
      (decide (0 < 2) && notHas S0 3 && reach 34 36 50 5 1 (S0 ||| 2^3)))) := rfl
  rw [c21] at e
  exact e.trans (by decide +kernel)

theorem c106 : reach 34 36 50 4 0 (S0 ||| 2^7) = false := by decide +kernel

theorem c107 : reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^1) = false := by decide +kernel

theorem c105_d1 : body 34 36 50 4 1 0 (S0 ||| 2^7) 1 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 1 = (!((S0 ||| 2^7)).testBit 1 && ((aoHas (S0 ||| 2^7) 1 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 1 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^1)))) := rfl
  rw [c107] at e
  exact e.trans (by decide +kernel)

theorem c108 : reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^3) = false := by decide +kernel

theorem c105_d3 : body 34 36 50 4 1 0 (S0 ||| 2^7) 3 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 3 = (!((S0 ||| 2^7)).testBit 3 && ((aoHas (S0 ||| 2^7) 3 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 3 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^3)))) := rfl
  rw [c108] at e
  exact e.trans (by decide +kernel)

theorem c109 : reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^4) = false := by decide +kernel

theorem c105_d4 : body 34 36 50 4 1 0 (S0 ||| 2^7) 4 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 4 = (!((S0 ||| 2^7)).testBit 4 && ((aoHas (S0 ||| 2^7) 4 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^4)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 4 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^4)))) := rfl
  rw [c109] at e
  exact e.trans (by decide +kernel)

theorem c110 : reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^6) = false := by decide +kernel

theorem c105_d6 : body 34 36 50 4 1 0 (S0 ||| 2^7) 6 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 6 = (!((S0 ||| 2^7)).testBit 6 && ((aoHas (S0 ||| 2^7) 6 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^6)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 6 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^6)))) := rfl
  rw [c110] at e
  exact e.trans (by decide +kernel)

theorem c111 : reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^15) = false := by decide +kernel

theorem c105_d15 : body 34 36 50 4 1 0 (S0 ||| 2^7) 15 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 15 = (!((S0 ||| 2^7)).testBit 15 && ((aoHas (S0 ||| 2^7) 15 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 15 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^15)))) := rfl
  rw [c111] at e
  exact e.trans (by decide +kernel)

theorem c112 : reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^31) = false := by decide +kernel

theorem c105_d31 : body 34 36 50 4 1 0 (S0 ||| 2^7) 31 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 31 = (!((S0 ||| 2^7)).testBit 31 && ((aoHas (S0 ||| 2^7) 31 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 31 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^31)))) := rfl
  rw [c112] at e
  exact e.trans (by decide +kernel)

theorem c114 : reach 34 36 50 3 1 ((S0 ||| 2^7) ||| 2^39) = false := by decide +kernel

theorem c115 : reach 34 36 50 3 0 ((S0 ||| 2^7) ||| 2^39) = false := by decide +kernel

theorem c116 : reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^1) = false := by decide +kernel

theorem c113_d1 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 1 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 1 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 1 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 1 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 1 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^1)))) := rfl
  rw [c116] at e
  exact e.trans (by decide +kernel)

theorem c117 : reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^3) = false := by decide +kernel

theorem c113_d3 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 3 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 3 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 3 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 3 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 3 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^3)))) := rfl
  rw [c117] at e
  exact e.trans (by decide +kernel)

theorem c118 : reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) = false := by decide +kernel

theorem c113_d4 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 4 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 4 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 4 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 4 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^4)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 4 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4)))) := rfl
  rw [c118] at e
  exact e.trans (by decide +kernel)

theorem c119 : reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^6) = false := by decide +kernel

theorem c113_d6 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 6 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 6 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 6 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 6 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^6)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 6 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^6)))) := rfl
  rw [c119] at e
  exact e.trans (by decide +kernel)

theorem c120 : reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^15) = false := by decide +kernel

theorem c113_d15 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 15 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 15 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 15 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 15 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 15 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^15)))) := rfl
  rw [c120] at e
  exact e.trans (by decide +kernel)

theorem c121 : reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^24) = false := by decide +kernel

theorem c113_d24 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 24 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 24 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 24 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 24 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^24)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 24 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^24)))) := rfl
  rw [c121] at e
  exact e.trans (by decide +kernel)

theorem c122 : reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^31) = false := by decide +kernel

theorem c113_d31 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 31 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 31 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 31 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 31 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 31 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^31)))) := rfl
  rw [c122] at e
  exact e.trans (by decide +kernel)

theorem c123 : reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^36) = false := by decide +kernel

theorem c113_d36 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 36 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 36 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 36 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 36 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^36)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 36 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^36)))) := rfl
  rw [c123] at e
  exact e.trans (by decide +kernel)

theorem c124 : reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) = false := by decide +kernel

theorem c113_d38 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 38 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 38 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 38 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 38 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^38)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 38 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38)))) := rfl
  rw [c124] at e
  exact e.trans (by decide +kernel)

theorem c125 : reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^55) = false := by decide +kernel

theorem c113_d55 : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 55 = false := by
  have e : body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) 55 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 55 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 55 && reach 34 36 50 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^55)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 55 && reach 34 36 50 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^55)))) := rfl
  rw [c125] at e
  exact e.trans (by decide +kernel)

theorem c113_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 15 || v == 24 || v == 31 || v == 36 || v == 38 || v == 55 || !body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) v) = true := by decide +kernel

theorem c113_a : ∀ v, v < 64 → body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c113_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c113_d1
  by_cases h3 : v = 3
  · subst h3; exact c113_d3
  by_cases h4 : v = 4
  · subst h4; exact c113_d4
  by_cases h6 : v = 6
  · subst h6; exact c113_d6
  by_cases h15 : v = 15
  · subst h15; exact c113_d15
  by_cases h24 : v = 24
  · subst h24; exact c113_d24
  by_cases h31 : v = 31
  · subst h31; exact c113_d31
  by_cases h36 : v = 36
  · subst h36; exact c113_d36
  by_cases h38 : v = 38
  · subst h38; exact c113_d38
  by_cases h55 : v = 55
  · subst h55; exact c113_d55
  simpa [h1, h3, h4, h6, h15, h24, h31, h36, h38, h55] using h

theorem c113 : reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^39) = false := by
  have e := reach_succ 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39) rfl
  have h : (List.range 64).any (body 34 36 50 3 1 0 ((S0 ||| 2^7) ||| 2^39)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c113_a v (List.mem_range.mp hv)]; decide
  rw [c114, c115, h] at e
  exact e.trans (by decide +kernel)

theorem c105_d39 : body 34 36 50 4 1 0 (S0 ||| 2^7) 39 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 39 = (!((S0 ||| 2^7)).testBit 39 && ((aoHas (S0 ||| 2^7) 39 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^39)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 39 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^39)))) := rfl
  rw [c113] at e
  exact e.trans (by decide +kernel)

theorem c126 : reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^55) = false := by decide +kernel

theorem c105_d55 : body 34 36 50 4 1 0 (S0 ||| 2^7) 55 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^7) 55 = (!((S0 ||| 2^7)).testBit 55 && ((aoHas (S0 ||| 2^7) 55 && reach 34 36 50 4 1 ((S0 ||| 2^7) ||| 2^55)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 55 && reach 34 36 50 4 0 ((S0 ||| 2^7) ||| 2^55)))) := rfl
  rw [c126] at e
  exact e.trans (by decide +kernel)

theorem c105_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 15 || v == 31 || v == 39 || v == 55 || !body 34 36 50 4 1 0 (S0 ||| 2^7) v) = true := by decide +kernel

theorem c105_a : ∀ v, v < 64 → body 34 36 50 4 1 0 (S0 ||| 2^7) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c105_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c105_d1
  by_cases h3 : v = 3
  · subst h3; exact c105_d3
  by_cases h4 : v = 4
  · subst h4; exact c105_d4
  by_cases h6 : v = 6
  · subst h6; exact c105_d6
  by_cases h15 : v = 15
  · subst h15; exact c105_d15
  by_cases h31 : v = 31
  · subst h31; exact c105_d31
  by_cases h39 : v = 39
  · subst h39; exact c105_d39
  by_cases h55 : v = 55
  · subst h55; exact c105_d55
  simpa [h1, h3, h4, h6, h15, h31, h39, h55] using h

theorem c105 : reach 34 36 50 5 1 (S0 ||| 2^7) = false := by
  have e := reach_succ 34 36 50 4 1 0 (S0 ||| 2^7) rfl
  have h : (List.range 64).any (body 34 36 50 4 1 0 (S0 ||| 2^7)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c105_a v (List.mem_range.mp hv)]; decide
  rw [c7, c106, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d7 : body 34 36 50 5 2 1 S0 7 = false := by
  have e : body 34 36 50 5 2 1 S0 7 = (!(S0).testBit 7 && ((aoHas S0 7 && reach 34 36 50 5 2 (S0 ||| 2^7)) ||
      (decide (0 < 2) && notHas S0 7 && reach 34 36 50 5 1 (S0 ||| 2^7)))) := rfl
  rw [c105] at e
  exact e.trans (by decide +kernel)

theorem c128 : reach 34 36 50 4 0 (S0 ||| 2^15) = false := by decide +kernel

theorem c129 : reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^1) = false := by decide +kernel

theorem c127_d1 : body 34 36 50 4 1 0 (S0 ||| 2^15) 1 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 1 = (!((S0 ||| 2^15)).testBit 1 && ((aoHas (S0 ||| 2^15) 1 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 1 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^1)))) := rfl
  rw [c129] at e
  exact e.trans (by decide +kernel)

theorem c130 : reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^3) = false := by decide +kernel

theorem c127_d3 : body 34 36 50 4 1 0 (S0 ||| 2^15) 3 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 3 = (!((S0 ||| 2^15)).testBit 3 && ((aoHas (S0 ||| 2^15) 3 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 3 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^3)))) := rfl
  rw [c130] at e
  exact e.trans (by decide +kernel)

theorem c131 : reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^7) = false := by decide +kernel

theorem c127_d7 : body 34 36 50 4 1 0 (S0 ||| 2^15) 7 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 7 = (!((S0 ||| 2^15)).testBit 7 && ((aoHas (S0 ||| 2^15) 7 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 7 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^7)))) := rfl
  rw [c131] at e
  exact e.trans (by decide +kernel)

theorem c132 : reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c127_d8 : body 34 36 50 4 1 0 (S0 ||| 2^15) 8 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 8 = (!((S0 ||| 2^15)).testBit 8 && ((aoHas (S0 ||| 2^15) 8 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^8)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 8 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^8)))) := rfl
  rw [c132] at e
  exact e.trans (by decide +kernel)

theorem c133 : reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c127_d12 : body 34 36 50 4 1 0 (S0 ||| 2^15) 12 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 12 = (!((S0 ||| 2^15)).testBit 12 && ((aoHas (S0 ||| 2^15) 12 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^12)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 12 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^12)))) := rfl
  rw [c133] at e
  exact e.trans (by decide +kernel)

theorem c134 : reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c127_d14 : body 34 36 50 4 1 0 (S0 ||| 2^15) 14 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 14 = (!((S0 ||| 2^15)).testBit 14 && ((aoHas (S0 ||| 2^15) 14 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^14)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 14 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^14)))) := rfl
  rw [c134] at e
  exact e.trans (by decide +kernel)

theorem c135 : reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^31) = false := by decide +kernel

theorem c127_d31 : body 34 36 50 4 1 0 (S0 ||| 2^15) 31 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 31 = (!((S0 ||| 2^15)).testBit 31 && ((aoHas (S0 ||| 2^15) 31 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 31 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^31)))) := rfl
  rw [c135] at e
  exact e.trans (by decide +kernel)

theorem c136 : reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c127_d47 : body 34 36 50 4 1 0 (S0 ||| 2^15) 47 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^15) 47 = (!((S0 ||| 2^15)).testBit 47 && ((aoHas (S0 ||| 2^15) 47 && reach 34 36 50 4 1 ((S0 ||| 2^15) ||| 2^47)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 47 && reach 34 36 50 4 0 ((S0 ||| 2^15) ||| 2^47)))) := rfl
  rw [c136] at e
  exact e.trans (by decide +kernel)

theorem c127_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 14 || v == 31 || v == 47 || !body 34 36 50 4 1 0 (S0 ||| 2^15) v) = true := by decide +kernel

theorem c127_a : ∀ v, v < 64 → body 34 36 50 4 1 0 (S0 ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c127_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c127_d1
  by_cases h3 : v = 3
  · subst h3; exact c127_d3
  by_cases h7 : v = 7
  · subst h7; exact c127_d7
  by_cases h8 : v = 8
  · subst h8; exact c127_d8
  by_cases h12 : v = 12
  · subst h12; exact c127_d12
  by_cases h14 : v = 14
  · subst h14; exact c127_d14
  by_cases h31 : v = 31
  · subst h31; exact c127_d31
  by_cases h47 : v = 47
  · subst h47; exact c127_d47
  simpa [h1, h3, h7, h8, h12, h14, h31, h47] using h

theorem c127 : reach 34 36 50 5 1 (S0 ||| 2^15) = false := by
  have e := reach_succ 34 36 50 4 1 0 (S0 ||| 2^15) rfl
  have h : (List.range 64).any (body 34 36 50 4 1 0 (S0 ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c127_a v (List.mem_range.mp hv)]; decide
  rw [c8, c128, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d15 : body 34 36 50 5 2 1 S0 15 = false := by
  have e : body 34 36 50 5 2 1 S0 15 = (!(S0).testBit 15 && ((aoHas S0 15 && reach 34 36 50 5 2 (S0 ||| 2^15)) ||
      (decide (0 < 2) && notHas S0 15 && reach 34 36 50 5 1 (S0 ||| 2^15)))) := rfl
  rw [c127] at e
  exact e.trans (by decide +kernel)

theorem c138 : reach 34 36 50 4 0 (S0 ||| 2^31) = false := by decide +kernel

theorem c139 : reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^1) = false := by decide +kernel

theorem c137_d1 : body 34 36 50 4 1 0 (S0 ||| 2^31) 1 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 1 = (!((S0 ||| 2^31)).testBit 1 && ((aoHas (S0 ||| 2^31) 1 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 1 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^1)))) := rfl
  rw [c139] at e
  exact e.trans (by decide +kernel)

theorem c140 : reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^3) = false := by decide +kernel

theorem c137_d3 : body 34 36 50 4 1 0 (S0 ||| 2^31) 3 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 3 = (!((S0 ||| 2^31)).testBit 3 && ((aoHas (S0 ||| 2^31) 3 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 3 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^3)))) := rfl
  rw [c140] at e
  exact e.trans (by decide +kernel)

theorem c141 : reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^7) = false := by decide +kernel

theorem c137_d7 : body 34 36 50 4 1 0 (S0 ||| 2^31) 7 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 7 = (!((S0 ||| 2^31)).testBit 7 && ((aoHas (S0 ||| 2^31) 7 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 7 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^7)))) := rfl
  rw [c141] at e
  exact e.trans (by decide +kernel)

theorem c142 : reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^15) = false := by decide +kernel

theorem c137_d15 : body 34 36 50 4 1 0 (S0 ||| 2^31) 15 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 15 = (!((S0 ||| 2^31)).testBit 15 && ((aoHas (S0 ||| 2^31) 15 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 15 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^15)))) := rfl
  rw [c142] at e
  exact e.trans (by decide +kernel)

theorem c143 : reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^16) = false := by decide +kernel

theorem c137_d16 : body 34 36 50 4 1 0 (S0 ||| 2^31) 16 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 16 = (!((S0 ||| 2^31)).testBit 16 && ((aoHas (S0 ||| 2^31) 16 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^16)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 16 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^16)))) := rfl
  rw [c143] at e
  exact e.trans (by decide +kernel)

theorem c144 : reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^24) = false := by decide +kernel

theorem c137_d24 : body 34 36 50 4 1 0 (S0 ||| 2^31) 24 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 24 = (!((S0 ||| 2^31)).testBit 24 && ((aoHas (S0 ||| 2^31) 24 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^24)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 24 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^24)))) := rfl
  rw [c144] at e
  exact e.trans (by decide +kernel)

theorem c145 : reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^28) = false := by decide +kernel

theorem c137_d28 : body 34 36 50 4 1 0 (S0 ||| 2^31) 28 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 28 = (!((S0 ||| 2^31)).testBit 28 && ((aoHas (S0 ||| 2^31) 28 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^28)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 28 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^28)))) := rfl
  rw [c145] at e
  exact e.trans (by decide +kernel)

theorem c146 : reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^30) = false := by decide +kernel

theorem c137_d30 : body 34 36 50 4 1 0 (S0 ||| 2^31) 30 = false := by
  have e : body 34 36 50 4 1 0 (S0 ||| 2^31) 30 = (!((S0 ||| 2^31)).testBit 30 && ((aoHas (S0 ||| 2^31) 30 && reach 34 36 50 4 1 ((S0 ||| 2^31) ||| 2^30)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 30 && reach 34 36 50 4 0 ((S0 ||| 2^31) ||| 2^30)))) := rfl
  rw [c146] at e
  exact e.trans (by decide +kernel)

theorem c137_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 16 || v == 24 || v == 28 || v == 30 || !body 34 36 50 4 1 0 (S0 ||| 2^31) v) = true := by decide +kernel

theorem c137_a : ∀ v, v < 64 → body 34 36 50 4 1 0 (S0 ||| 2^31) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c137_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c137_d1
  by_cases h3 : v = 3
  · subst h3; exact c137_d3
  by_cases h7 : v = 7
  · subst h7; exact c137_d7
  by_cases h15 : v = 15
  · subst h15; exact c137_d15
  by_cases h16 : v = 16
  · subst h16; exact c137_d16
  by_cases h24 : v = 24
  · subst h24; exact c137_d24
  by_cases h28 : v = 28
  · subst h28; exact c137_d28
  by_cases h30 : v = 30
  · subst h30; exact c137_d30
  simpa [h1, h3, h7, h15, h16, h24, h28, h30] using h

theorem c137 : reach 34 36 50 5 1 (S0 ||| 2^31) = false := by
  have e := reach_succ 34 36 50 4 1 0 (S0 ||| 2^31) rfl
  have h : (List.range 64).any (body 34 36 50 4 1 0 (S0 ||| 2^31)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c137_a v (List.mem_range.mp hv)]; decide
  rw [c9, c138, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d31 : body 34 36 50 5 2 1 S0 31 = false := by
  have e : body 34 36 50 5 2 1 S0 31 = (!(S0).testBit 31 && ((aoHas S0 31 && reach 34 36 50 5 2 (S0 ||| 2^31)) ||
      (decide (0 < 2) && notHas S0 31 && reach 34 36 50 5 1 (S0 ||| 2^31)))) := rfl
  rw [c137] at e
  exact e.trans (by decide +kernel)

theorem c1_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 31 || !body 34 36 50 5 2 1 S0 v) = true := by decide +kernel

theorem c1_a : ∀ v, v < 64 → body 34 36 50 5 2 1 S0 v = false := by
  intro v hv
  have h := List.all_eq_true.mp c1_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c1_d1
  by_cases h3 : v = 3
  · subst h3; exact c1_d3
  by_cases h7 : v = 7
  · subst h7; exact c1_d7
  by_cases h15 : v = 15
  · subst h15; exact c1_d15
  by_cases h31 : v = 31
  · subst h31; exact c1_d31
  simpa [h1, h3, h7, h15, h31] using h

theorem c1 : reach 34 36 50 6 2 S0 = false := by
  have e := reach_succ 34 36 50 5 2 1 S0 rfl
  have h : (List.range 64).any (body 34 36 50 5 2 1 S0) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c1_a v (List.mem_range.mp hv)]; decide
  rw [c2, c10, h] at e
  exact e.trans (by decide +kernel)

theorem cert : reach 34 36 50 6 2 S0 = false := c1

theorem init : ∀ i < 7, ∃ m, m < 64 ∧ S0.testBit m = true ∧ ∀ t : Fin 6,
    ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]).getD i false =
      m.testBit t.val := by
  intro i hi
  refine ⟨[62, 60, 56, 48, 32, 0, 63].getD i 0, ?_⟩
  revert i
  decide +kernel

theorem main : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (34 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hf, hr, hn, hs, ht⟩
  have := sound 34 36 50 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    D.gates (fun t => (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])
    7 S0 6 2 (fun t => by simp) (by decide) (by decide) init hf hr hs hn p.val q.val r.val
    p.isLt q.isLt r.isLt (fun t => ht t)
  rw [cert] at this
  exact absurd this (by decide)

end PEqualNP.Outside.L_meta_50199

theorem PEqualNP.Outside.L_meta_50199 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (34 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_50199.main
