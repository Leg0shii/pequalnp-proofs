import PEqualNP.Defs

-- Exhaustion certificate: a kernel-run search over sets of 6-bit wire masks (a set is a Nat
-- bitset), with a soundness proof that every circuit of the statement is covered by the search.

namespace PEqualNP.Outside.L_meta_50261

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

theorem c3 : reach 8 14 45 4 2 S0 = false := by decide +kernel

theorem c4 : reach 8 14 45 4 1 S0 = false := by decide +kernel

theorem c5 : reach 8 14 45 4 1 (S0 ||| 2^1) = false := by decide +kernel

theorem c2_d1 : body 8 14 45 4 2 1 S0 1 = false := by
  have e : body 8 14 45 4 2 1 S0 1 = (!(S0).testBit 1 && ((aoHas S0 1 && reach 8 14 45 4 2 (S0 ||| 2^1)) ||
      (decide (0 < 2) && notHas S0 1 && reach 8 14 45 4 1 (S0 ||| 2^1)))) := rfl
  rw [c5] at e
  exact e.trans (by decide +kernel)

theorem c6 : reach 8 14 45 4 1 (S0 ||| 2^3) = false := by decide +kernel

theorem c2_d3 : body 8 14 45 4 2 1 S0 3 = false := by
  have e : body 8 14 45 4 2 1 S0 3 = (!(S0).testBit 3 && ((aoHas S0 3 && reach 8 14 45 4 2 (S0 ||| 2^3)) ||
      (decide (0 < 2) && notHas S0 3 && reach 8 14 45 4 1 (S0 ||| 2^3)))) := rfl
  rw [c6] at e
  exact e.trans (by decide +kernel)

theorem c7 : reach 8 14 45 4 1 (S0 ||| 2^7) = false := by decide +kernel

theorem c2_d7 : body 8 14 45 4 2 1 S0 7 = false := by
  have e : body 8 14 45 4 2 1 S0 7 = (!(S0).testBit 7 && ((aoHas S0 7 && reach 8 14 45 4 2 (S0 ||| 2^7)) ||
      (decide (0 < 2) && notHas S0 7 && reach 8 14 45 4 1 (S0 ||| 2^7)))) := rfl
  rw [c7] at e
  exact e.trans (by decide +kernel)

theorem c9 : reach 8 14 45 3 1 (S0 ||| 2^15) = false := by decide +kernel

theorem c10 : reach 8 14 45 3 0 (S0 ||| 2^15) = false := by decide +kernel

theorem c11 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^1) = false := by decide +kernel

theorem c8_d1 : body 8 14 45 3 1 0 (S0 ||| 2^15) 1 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 1 = (!((S0 ||| 2^15)).testBit 1 && ((aoHas (S0 ||| 2^15) 1 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 1 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^1)))) := rfl
  rw [c11] at e
  exact e.trans (by decide +kernel)

theorem c12 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^3) = false := by decide +kernel

theorem c8_d3 : body 8 14 45 3 1 0 (S0 ||| 2^15) 3 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 3 = (!((S0 ||| 2^15)).testBit 3 && ((aoHas (S0 ||| 2^15) 3 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 3 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^3)))) := rfl
  rw [c12] at e
  exact e.trans (by decide +kernel)

theorem c13 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^7) = false := by decide +kernel

theorem c8_d7 : body 8 14 45 3 1 0 (S0 ||| 2^15) 7 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 7 = (!((S0 ||| 2^15)).testBit 7 && ((aoHas (S0 ||| 2^15) 7 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 7 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^7)))) := rfl
  rw [c13] at e
  exact e.trans (by decide +kernel)

theorem c14 : reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c8_d8 : body 8 14 45 3 1 0 (S0 ||| 2^15) 8 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 8 = (!((S0 ||| 2^15)).testBit 8 && ((aoHas (S0 ||| 2^15) 8 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^8)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 8 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^8)))) := rfl
  rw [c14] at e
  exact e.trans (by decide +kernel)

theorem c15 : reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c8_d12 : body 8 14 45 3 1 0 (S0 ||| 2^15) 12 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 12 = (!((S0 ||| 2^15)).testBit 12 && ((aoHas (S0 ||| 2^15) 12 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^12)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 12 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^12)))) := rfl
  rw [c15] at e
  exact e.trans (by decide +kernel)

theorem c16 : reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c8_d14 : body 8 14 45 3 1 0 (S0 ||| 2^15) 14 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 14 = (!((S0 ||| 2^15)).testBit 14 && ((aoHas (S0 ||| 2^15) 14 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^14)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 14 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^14)))) := rfl
  rw [c16] at e
  exact e.trans (by decide +kernel)

theorem c17 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^31) = false := by decide +kernel

theorem c8_d31 : body 8 14 45 3 1 0 (S0 ||| 2^15) 31 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 31 = (!((S0 ||| 2^15)).testBit 31 && ((aoHas (S0 ||| 2^15) 31 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 31 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^31)))) := rfl
  rw [c17] at e
  exact e.trans (by decide +kernel)

theorem c18 : reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c8_d47 : body 8 14 45 3 1 0 (S0 ||| 2^15) 47 = false := by
  have e : body 8 14 45 3 1 0 (S0 ||| 2^15) 47 = (!((S0 ||| 2^15)).testBit 47 && ((aoHas (S0 ||| 2^15) 47 && reach 8 14 45 3 1 ((S0 ||| 2^15) ||| 2^47)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 47 && reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^47)))) := rfl
  rw [c18] at e
  exact e.trans (by decide +kernel)

theorem c8_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 14 || v == 31 || v == 47 || !body 8 14 45 3 1 0 (S0 ||| 2^15) v) = true := by decide +kernel

theorem c8_a : ∀ v, v < 64 → body 8 14 45 3 1 0 (S0 ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c8_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c8_d1
  by_cases h3 : v = 3
  · subst h3; exact c8_d3
  by_cases h7 : v = 7
  · subst h7; exact c8_d7
  by_cases h8 : v = 8
  · subst h8; exact c8_d8
  by_cases h12 : v = 12
  · subst h12; exact c8_d12
  by_cases h14 : v = 14
  · subst h14; exact c8_d14
  by_cases h31 : v = 31
  · subst h31; exact c8_d31
  by_cases h47 : v = 47
  · subst h47; exact c8_d47
  simpa [h1, h3, h7, h8, h12, h14, h31, h47] using h

theorem c8 : reach 8 14 45 4 1 (S0 ||| 2^15) = false := by
  have e := reach_succ 8 14 45 3 1 0 (S0 ||| 2^15) rfl
  have h : (List.range 64).any (body 8 14 45 3 1 0 (S0 ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c8_a v (List.mem_range.mp hv)]; decide
  rw [c9, c10, h] at e
  exact e.trans (by decide +kernel)

theorem c2_d15 : body 8 14 45 4 2 1 S0 15 = false := by
  have e : body 8 14 45 4 2 1 S0 15 = (!(S0).testBit 15 && ((aoHas S0 15 && reach 8 14 45 4 2 (S0 ||| 2^15)) ||
      (decide (0 < 2) && notHas S0 15 && reach 8 14 45 4 1 (S0 ||| 2^15)))) := rfl
  rw [c8] at e
  exact e.trans (by decide +kernel)

theorem c19 : reach 8 14 45 4 1 (S0 ||| 2^31) = false := by decide +kernel

theorem c2_d31 : body 8 14 45 4 2 1 S0 31 = false := by
  have e : body 8 14 45 4 2 1 S0 31 = (!(S0).testBit 31 && ((aoHas S0 31 && reach 8 14 45 4 2 (S0 ||| 2^31)) ||
      (decide (0 < 2) && notHas S0 31 && reach 8 14 45 4 1 (S0 ||| 2^31)))) := rfl
  rw [c19] at e
  exact e.trans (by decide +kernel)

theorem c2_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 31 || !body 8 14 45 4 2 1 S0 v) = true := by decide +kernel

theorem c2_a : ∀ v, v < 64 → body 8 14 45 4 2 1 S0 v = false := by
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

theorem c2 : reach 8 14 45 5 2 S0 = false := by
  have e := reach_succ 8 14 45 4 2 1 S0 rfl
  have h : (List.range 64).any (body 8 14 45 4 2 1 S0) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c2_a v (List.mem_range.mp hv)]; decide
  rw [c3, c4, h] at e
  exact e.trans (by decide +kernel)

theorem c21 : reach 8 14 45 4 0 S0 = false := by decide +kernel

theorem c22 : reach 8 14 45 4 0 (S0 ||| 2^1) = false := by decide +kernel

theorem c20_d1 : body 8 14 45 4 1 0 S0 1 = false := by
  have e : body 8 14 45 4 1 0 S0 1 = (!(S0).testBit 1 && ((aoHas S0 1 && reach 8 14 45 4 1 (S0 ||| 2^1)) ||
      (decide (0 < 1) && notHas S0 1 && reach 8 14 45 4 0 (S0 ||| 2^1)))) := rfl
  rw [c22] at e
  exact e.trans (by decide +kernel)

theorem c23 : reach 8 14 45 4 0 (S0 ||| 2^3) = false := by decide +kernel

theorem c20_d3 : body 8 14 45 4 1 0 S0 3 = false := by
  have e : body 8 14 45 4 1 0 S0 3 = (!(S0).testBit 3 && ((aoHas S0 3 && reach 8 14 45 4 1 (S0 ||| 2^3)) ||
      (decide (0 < 1) && notHas S0 3 && reach 8 14 45 4 0 (S0 ||| 2^3)))) := rfl
  rw [c23] at e
  exact e.trans (by decide +kernel)

theorem c24 : reach 8 14 45 4 0 (S0 ||| 2^7) = false := by decide +kernel

theorem c20_d7 : body 8 14 45 4 1 0 S0 7 = false := by
  have e : body 8 14 45 4 1 0 S0 7 = (!(S0).testBit 7 && ((aoHas S0 7 && reach 8 14 45 4 1 (S0 ||| 2^7)) ||
      (decide (0 < 1) && notHas S0 7 && reach 8 14 45 4 0 (S0 ||| 2^7)))) := rfl
  rw [c24] at e
  exact e.trans (by decide +kernel)

theorem c25 : reach 8 14 45 4 0 (S0 ||| 2^15) = false := by decide +kernel

theorem c20_d15 : body 8 14 45 4 1 0 S0 15 = false := by
  have e : body 8 14 45 4 1 0 S0 15 = (!(S0).testBit 15 && ((aoHas S0 15 && reach 8 14 45 4 1 (S0 ||| 2^15)) ||
      (decide (0 < 1) && notHas S0 15 && reach 8 14 45 4 0 (S0 ||| 2^15)))) := rfl
  rw [c25] at e
  exact e.trans (by decide +kernel)

theorem c26 : reach 8 14 45 4 0 (S0 ||| 2^31) = false := by decide +kernel

theorem c20_d31 : body 8 14 45 4 1 0 S0 31 = false := by
  have e : body 8 14 45 4 1 0 S0 31 = (!(S0).testBit 31 && ((aoHas S0 31 && reach 8 14 45 4 1 (S0 ||| 2^31)) ||
      (decide (0 < 1) && notHas S0 31 && reach 8 14 45 4 0 (S0 ||| 2^31)))) := rfl
  rw [c26] at e
  exact e.trans (by decide +kernel)

theorem c20_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 31 || !body 8 14 45 4 1 0 S0 v) = true := by decide +kernel

theorem c20_a : ∀ v, v < 64 → body 8 14 45 4 1 0 S0 v = false := by
  intro v hv
  have h := List.all_eq_true.mp c20_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c20_d1
  by_cases h3 : v = 3
  · subst h3; exact c20_d3
  by_cases h7 : v = 7
  · subst h7; exact c20_d7
  by_cases h15 : v = 15
  · subst h15; exact c20_d15
  by_cases h31 : v = 31
  · subst h31; exact c20_d31
  simpa [h1, h3, h7, h15, h31] using h

theorem c20 : reach 8 14 45 5 1 S0 = false := by
  have e := reach_succ 8 14 45 4 1 0 S0 rfl
  have h : (List.range 64).any (body 8 14 45 4 1 0 S0) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c20_a v (List.mem_range.mp hv)]; decide
  rw [c4, c21, h] at e
  exact e.trans (by decide +kernel)

theorem c28 : reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^3) = false := by decide +kernel

theorem c27_d3 : body 8 14 45 4 1 0 (S0 ||| 2^1) 3 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 3 = (!((S0 ||| 2^1)).testBit 3 && ((aoHas (S0 ||| 2^1) 3 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 3 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^3)))) := rfl
  rw [c28] at e
  exact e.trans (by decide +kernel)

theorem c29 : reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^7) = false := by decide +kernel

theorem c27_d7 : body 8 14 45 4 1 0 (S0 ||| 2^1) 7 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 7 = (!((S0 ||| 2^1)).testBit 7 && ((aoHas (S0 ||| 2^1) 7 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 7 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^7)))) := rfl
  rw [c29] at e
  exact e.trans (by decide +kernel)

theorem c31 : reach 8 14 45 3 0 ((S0 ||| 2^1) ||| 2^15) = false := by decide +kernel

theorem c32 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c30_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 8 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 8 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^8)))) := rfl
  rw [c32] at e
  exact e.trans (by decide +kernel)

theorem c33 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c30_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 12 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 12 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^12)))) := rfl
  rw [c33] at e
  exact e.trans (by decide +kernel)

theorem c34 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c30_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 14 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 14 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^14)))) := rfl
  rw [c34] at e
  exact e.trans (by decide +kernel)

theorem c35 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^33) = false := by decide +kernel

theorem c30_d33 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 33 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 33 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 33 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 33 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^33)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 33 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^33)))) := rfl
  rw [c35] at e
  exact e.trans (by decide +kernel)

theorem c36 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c30_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 47 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 47 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^47)))) := rfl
  rw [c36] at e
  exact e.trans (by decide +kernel)

theorem c37 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^49) = false := by decide +kernel

theorem c30_d49 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 49 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 49 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 49 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 49 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^49)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 49 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^49)))) := rfl
  rw [c37] at e
  exact e.trans (by decide +kernel)

theorem c38 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^57) = false := by decide +kernel

theorem c30_d57 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 57 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 57 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 57 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 57 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^57)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 57 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^57)))) := rfl
  rw [c38] at e
  exact e.trans (by decide +kernel)

theorem c39 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^61) = false := by decide +kernel

theorem c30_d61 : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 61 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) 61 = (!(((S0 ||| 2^1) ||| 2^15)).testBit 61 && ((aoHas ((S0 ||| 2^1) ||| 2^15) 61 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^61)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^1) ||| 2^15) 61 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^15) ||| 2^61)))) := rfl
  rw [c39] at e
  exact e.trans (by decide +kernel)

theorem c30_o : (List.range 64).all (fun v => v == 8 || v == 12 || v == 14 || v == 33 || v == 47 || v == 49 || v == 57 || v == 61 || !body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) v) = true := by decide +kernel

theorem c30_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c30_o v (List.mem_range.mpr hv)
  by_cases h8 : v = 8
  · subst h8; exact c30_d8
  by_cases h12 : v = 12
  · subst h12; exact c30_d12
  by_cases h14 : v = 14
  · subst h14; exact c30_d14
  by_cases h33 : v = 33
  · subst h33; exact c30_d33
  by_cases h47 : v = 47
  · subst h47; exact c30_d47
  by_cases h49 : v = 49
  · subst h49; exact c30_d49
  by_cases h57 : v = 57
  · subst h57; exact c30_d57
  by_cases h61 : v = 61
  · subst h61; exact c30_d61
  simpa [h8, h12, h14, h33, h47, h49, h57, h61] using h

theorem c30 : reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^15) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^1) ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c30_a v (List.mem_range.mp hv)]; decide
  rw [c31, h] at e
  exact e.trans (by decide +kernel)

theorem c27_d15 : body 8 14 45 4 1 0 (S0 ||| 2^1) 15 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 15 = (!((S0 ||| 2^1)).testBit 15 && ((aoHas (S0 ||| 2^1) 15 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 15 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^15)))) := rfl
  rw [c30] at e
  exact e.trans (by decide +kernel)

theorem c40 : reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^31) = false := by decide +kernel

theorem c27_d31 : body 8 14 45 4 1 0 (S0 ||| 2^1) 31 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 31 = (!((S0 ||| 2^1)).testBit 31 && ((aoHas (S0 ||| 2^1) 31 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 31 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^31)))) := rfl
  rw [c40] at e
  exact e.trans (by decide +kernel)

theorem c41 : reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^33) = false := by decide +kernel

theorem c27_d33 : body 8 14 45 4 1 0 (S0 ||| 2^1) 33 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 33 = (!((S0 ||| 2^1)).testBit 33 && ((aoHas (S0 ||| 2^1) 33 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^33)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 33 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^33)))) := rfl
  rw [c41] at e
  exact e.trans (by decide +kernel)

theorem c43 : reach 8 14 45 3 1 ((S0 ||| 2^1) ||| 2^49) = false := by decide +kernel

theorem c44 : reach 8 14 45 3 0 ((S0 ||| 2^1) ||| 2^49) = false := by decide +kernel

theorem c45 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^3) = false := by decide +kernel

theorem c42_d3 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 3 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 3 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 3 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 3 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 3 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^3)))) := rfl
  rw [c45] at e
  exact e.trans (by decide +kernel)

theorem c46 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^7) = false := by decide +kernel

theorem c42_d7 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 7 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 7 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 7 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 7 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 7 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^7)))) := rfl
  rw [c46] at e
  exact e.trans (by decide +kernel)

theorem c47 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^14) = false := by decide +kernel

theorem c42_d14 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 14 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 14 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 14 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 14 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^14)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 14 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^14)))) := rfl
  rw [c47] at e
  exact e.trans (by decide +kernel)

theorem c48 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^15) = false := by decide +kernel

theorem c42_d15 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 15 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 15 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 15 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 15 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 15 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^15)))) := rfl
  rw [c48] at e
  exact e.trans (by decide +kernel)

theorem c49 : reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^31) = false := by decide +kernel

theorem c42_d31 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 31 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 31 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 31 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 31 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 31 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^31)))) := rfl
  rw [c49] at e
  exact e.trans (by decide +kernel)

theorem c50 : reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^33) = false := by decide +kernel

theorem c42_d33 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 33 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 33 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 33 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 33 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^33)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 33 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^33)))) := rfl
  rw [c50] at e
  exact e.trans (by decide +kernel)

theorem c51 : reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^57) = false := by decide +kernel

theorem c42_d57 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 57 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 57 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 57 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 57 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^57)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 57 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^57)))) := rfl
  rw [c51] at e
  exact e.trans (by decide +kernel)

theorem c52 : reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^61) = false := by decide +kernel

theorem c42_d61 : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 61 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) 61 = (!(((S0 ||| 2^1) ||| 2^49)).testBit 61 && ((aoHas ((S0 ||| 2^1) ||| 2^49) 61 && reach 8 14 45 3 1 (((S0 ||| 2^1) ||| 2^49) ||| 2^61)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^1) ||| 2^49) 61 && reach 8 14 45 3 0 (((S0 ||| 2^1) ||| 2^49) ||| 2^61)))) := rfl
  rw [c52] at e
  exact e.trans (by decide +kernel)

theorem c42_o : (List.range 64).all (fun v => v == 3 || v == 7 || v == 14 || v == 15 || v == 31 || v == 33 || v == 57 || v == 61 || !body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) v) = true := by decide +kernel

theorem c42_a : ∀ v, v < 64 → body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c42_o v (List.mem_range.mpr hv)
  by_cases h3 : v = 3
  · subst h3; exact c42_d3
  by_cases h7 : v = 7
  · subst h7; exact c42_d7
  by_cases h14 : v = 14
  · subst h14; exact c42_d14
  by_cases h15 : v = 15
  · subst h15; exact c42_d15
  by_cases h31 : v = 31
  · subst h31; exact c42_d31
  by_cases h33 : v = 33
  · subst h33; exact c42_d33
  by_cases h57 : v = 57
  · subst h57; exact c42_d57
  by_cases h61 : v = 61
  · subst h61; exact c42_d61
  simpa [h3, h7, h14, h15, h31, h33, h57, h61] using h

theorem c42 : reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^49) = false := by
  have e := reach_succ 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49) rfl
  have h : (List.range 64).any (body 8 14 45 3 1 0 ((S0 ||| 2^1) ||| 2^49)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c42_a v (List.mem_range.mp hv)]; decide
  rw [c43, c44, h] at e
  exact e.trans (by decide +kernel)

theorem c27_d49 : body 8 14 45 4 1 0 (S0 ||| 2^1) 49 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 49 = (!((S0 ||| 2^1)).testBit 49 && ((aoHas (S0 ||| 2^1) 49 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^49)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 49 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^49)))) := rfl
  rw [c42] at e
  exact e.trans (by decide +kernel)

theorem c53 : reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^57) = false := by decide +kernel

theorem c27_d57 : body 8 14 45 4 1 0 (S0 ||| 2^1) 57 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 57 = (!((S0 ||| 2^1)).testBit 57 && ((aoHas (S0 ||| 2^1) 57 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^57)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 57 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^57)))) := rfl
  rw [c53] at e
  exact e.trans (by decide +kernel)

theorem c54 : reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^61) = false := by decide +kernel

theorem c27_d61 : body 8 14 45 4 1 0 (S0 ||| 2^1) 61 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^1) 61 = (!((S0 ||| 2^1)).testBit 61 && ((aoHas (S0 ||| 2^1) 61 && reach 8 14 45 4 1 ((S0 ||| 2^1) ||| 2^61)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 61 && reach 8 14 45 4 0 ((S0 ||| 2^1) ||| 2^61)))) := rfl
  rw [c54] at e
  exact e.trans (by decide +kernel)

theorem c27_o : (List.range 64).all (fun v => v == 3 || v == 7 || v == 15 || v == 31 || v == 33 || v == 49 || v == 57 || v == 61 || !body 8 14 45 4 1 0 (S0 ||| 2^1) v) = true := by decide +kernel

theorem c27_a : ∀ v, v < 64 → body 8 14 45 4 1 0 (S0 ||| 2^1) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c27_o v (List.mem_range.mpr hv)
  by_cases h3 : v = 3
  · subst h3; exact c27_d3
  by_cases h7 : v = 7
  · subst h7; exact c27_d7
  by_cases h15 : v = 15
  · subst h15; exact c27_d15
  by_cases h31 : v = 31
  · subst h31; exact c27_d31
  by_cases h33 : v = 33
  · subst h33; exact c27_d33
  by_cases h49 : v = 49
  · subst h49; exact c27_d49
  by_cases h57 : v = 57
  · subst h57; exact c27_d57
  by_cases h61 : v = 61
  · subst h61; exact c27_d61
  simpa [h3, h7, h15, h31, h33, h49, h57, h61] using h

theorem c27 : reach 8 14 45 5 1 (S0 ||| 2^1) = false := by
  have e := reach_succ 8 14 45 4 1 0 (S0 ||| 2^1) rfl
  have h : (List.range 64).any (body 8 14 45 4 1 0 (S0 ||| 2^1)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c27_a v (List.mem_range.mp hv)]; decide
  rw [c5, c22, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d1 : body 8 14 45 5 2 1 S0 1 = false := by
  have e : body 8 14 45 5 2 1 S0 1 = (!(S0).testBit 1 && ((aoHas S0 1 && reach 8 14 45 5 2 (S0 ||| 2^1)) ||
      (decide (0 < 2) && notHas S0 1 && reach 8 14 45 5 1 (S0 ||| 2^1)))) := rfl
  rw [c27] at e
  exact e.trans (by decide +kernel)

theorem c56 : reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^1) = false := by decide +kernel

theorem c55_d1 : body 8 14 45 4 1 0 (S0 ||| 2^3) 1 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 1 = (!((S0 ||| 2^3)).testBit 1 && ((aoHas (S0 ||| 2^3) 1 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 1 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^1)))) := rfl
  rw [c56] at e
  exact e.trans (by decide +kernel)

theorem c57 : reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^2) = false := by decide +kernel

theorem c55_d2 : body 8 14 45 4 1 0 (S0 ||| 2^3) 2 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 2 = (!((S0 ||| 2^3)).testBit 2 && ((aoHas (S0 ||| 2^3) 2 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^2)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 2 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^2)))) := rfl
  rw [c57] at e
  exact e.trans (by decide +kernel)

theorem c58 : reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^7) = false := by decide +kernel

theorem c55_d7 : body 8 14 45 4 1 0 (S0 ||| 2^3) 7 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 7 = (!((S0 ||| 2^3)).testBit 7 && ((aoHas (S0 ||| 2^3) 7 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 7 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^7)))) := rfl
  rw [c58] at e
  exact e.trans (by decide +kernel)

theorem c60 : reach 8 14 45 3 0 ((S0 ||| 2^3) ||| 2^15) = false := by decide +kernel

theorem c61 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^2) = false := by decide +kernel

theorem c59_d2 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 2 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 2 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 2 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 2 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^2)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 2 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^2)))) := rfl
  rw [c61] at e
  exact e.trans (by decide +kernel)

theorem c62 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c59_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 8 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 8 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^8)))) := rfl
  rw [c62] at e
  exact e.trans (by decide +kernel)

theorem c63 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c59_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 12 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 12 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^12)))) := rfl
  rw [c63] at e
  exact e.trans (by decide +kernel)

theorem c64 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c59_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 14 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 14 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^14)))) := rfl
  rw [c64] at e
  exact e.trans (by decide +kernel)

theorem c65 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^35) = false := by decide +kernel

theorem c59_d35 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 35 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 35 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 35 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 35 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^35)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 35 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^35)))) := rfl
  rw [c65] at e
  exact e.trans (by decide +kernel)

theorem c66 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c59_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 47 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 47 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^47)))) := rfl
  rw [c66] at e
  exact e.trans (by decide +kernel)

theorem c67 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^51) = false := by decide +kernel

theorem c59_d51 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 51 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 51 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 51 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 51 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^51)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 51 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^51)))) := rfl
  rw [c67] at e
  exact e.trans (by decide +kernel)

theorem c68 : reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^59) = false := by decide +kernel

theorem c59_d59 : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 59 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) 59 = (!(((S0 ||| 2^3) ||| 2^15)).testBit 59 && ((aoHas ((S0 ||| 2^3) ||| 2^15) 59 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^59)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^3) ||| 2^15) 59 && reach 8 14 45 3 0 (((S0 ||| 2^3) ||| 2^15) ||| 2^59)))) := rfl
  rw [c68] at e
  exact e.trans (by decide +kernel)

theorem c59_o : (List.range 64).all (fun v => v == 2 || v == 8 || v == 12 || v == 14 || v == 35 || v == 47 || v == 51 || v == 59 || !body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) v) = true := by decide +kernel

theorem c59_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c59_o v (List.mem_range.mpr hv)
  by_cases h2 : v = 2
  · subst h2; exact c59_d2
  by_cases h8 : v = 8
  · subst h8; exact c59_d8
  by_cases h12 : v = 12
  · subst h12; exact c59_d12
  by_cases h14 : v = 14
  · subst h14; exact c59_d14
  by_cases h35 : v = 35
  · subst h35; exact c59_d35
  by_cases h47 : v = 47
  · subst h47; exact c59_d47
  by_cases h51 : v = 51
  · subst h51; exact c59_d51
  by_cases h59 : v = 59
  · subst h59; exact c59_d59
  simpa [h2, h8, h12, h14, h35, h47, h51, h59] using h

theorem c59 : reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^15) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^3) ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c59_a v (List.mem_range.mp hv)]; decide
  rw [c60, h] at e
  exact e.trans (by decide +kernel)

theorem c55_d15 : body 8 14 45 4 1 0 (S0 ||| 2^3) 15 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 15 = (!((S0 ||| 2^3)).testBit 15 && ((aoHas (S0 ||| 2^3) 15 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 15 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^15)))) := rfl
  rw [c59] at e
  exact e.trans (by decide +kernel)

theorem c69 : reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^31) = false := by decide +kernel

theorem c55_d31 : body 8 14 45 4 1 0 (S0 ||| 2^3) 31 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 31 = (!((S0 ||| 2^3)).testBit 31 && ((aoHas (S0 ||| 2^3) 31 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 31 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^31)))) := rfl
  rw [c69] at e
  exact e.trans (by decide +kernel)

theorem c70 : reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^35) = false := by decide +kernel

theorem c55_d35 : body 8 14 45 4 1 0 (S0 ||| 2^3) 35 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 35 = (!((S0 ||| 2^3)).testBit 35 && ((aoHas (S0 ||| 2^3) 35 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^35)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 35 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^35)))) := rfl
  rw [c70] at e
  exact e.trans (by decide +kernel)

theorem c71 : reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^51) = false := by decide +kernel

theorem c55_d51 : body 8 14 45 4 1 0 (S0 ||| 2^3) 51 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 51 = (!((S0 ||| 2^3)).testBit 51 && ((aoHas (S0 ||| 2^3) 51 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^51)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 51 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^51)))) := rfl
  rw [c71] at e
  exact e.trans (by decide +kernel)

theorem c72 : reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^59) = false := by decide +kernel

theorem c55_d59 : body 8 14 45 4 1 0 (S0 ||| 2^3) 59 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^3) 59 = (!((S0 ||| 2^3)).testBit 59 && ((aoHas (S0 ||| 2^3) 59 && reach 8 14 45 4 1 ((S0 ||| 2^3) ||| 2^59)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 59 && reach 8 14 45 4 0 ((S0 ||| 2^3) ||| 2^59)))) := rfl
  rw [c72] at e
  exact e.trans (by decide +kernel)

theorem c55_o : (List.range 64).all (fun v => v == 1 || v == 2 || v == 7 || v == 15 || v == 31 || v == 35 || v == 51 || v == 59 || !body 8 14 45 4 1 0 (S0 ||| 2^3) v) = true := by decide +kernel

theorem c55_a : ∀ v, v < 64 → body 8 14 45 4 1 0 (S0 ||| 2^3) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c55_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c55_d1
  by_cases h2 : v = 2
  · subst h2; exact c55_d2
  by_cases h7 : v = 7
  · subst h7; exact c55_d7
  by_cases h15 : v = 15
  · subst h15; exact c55_d15
  by_cases h31 : v = 31
  · subst h31; exact c55_d31
  by_cases h35 : v = 35
  · subst h35; exact c55_d35
  by_cases h51 : v = 51
  · subst h51; exact c55_d51
  by_cases h59 : v = 59
  · subst h59; exact c55_d59
  simpa [h1, h2, h7, h15, h31, h35, h51, h59] using h

theorem c55 : reach 8 14 45 5 1 (S0 ||| 2^3) = false := by
  have e := reach_succ 8 14 45 4 1 0 (S0 ||| 2^3) rfl
  have h : (List.range 64).any (body 8 14 45 4 1 0 (S0 ||| 2^3)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c55_a v (List.mem_range.mp hv)]; decide
  rw [c6, c23, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d3 : body 8 14 45 5 2 1 S0 3 = false := by
  have e : body 8 14 45 5 2 1 S0 3 = (!(S0).testBit 3 && ((aoHas S0 3 && reach 8 14 45 5 2 (S0 ||| 2^3)) ||
      (decide (0 < 2) && notHas S0 3 && reach 8 14 45 5 1 (S0 ||| 2^3)))) := rfl
  rw [c55] at e
  exact e.trans (by decide +kernel)

theorem c74 : reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^1) = false := by decide +kernel

theorem c73_d1 : body 8 14 45 4 1 0 (S0 ||| 2^7) 1 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 1 = (!((S0 ||| 2^7)).testBit 1 && ((aoHas (S0 ||| 2^7) 1 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 1 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^1)))) := rfl
  rw [c74] at e
  exact e.trans (by decide +kernel)

theorem c75 : reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^3) = false := by decide +kernel

theorem c73_d3 : body 8 14 45 4 1 0 (S0 ||| 2^7) 3 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 3 = (!((S0 ||| 2^7)).testBit 3 && ((aoHas (S0 ||| 2^7) 3 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 3 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^3)))) := rfl
  rw [c75] at e
  exact e.trans (by decide +kernel)

theorem c76 : reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^4) = false := by decide +kernel

theorem c73_d4 : body 8 14 45 4 1 0 (S0 ||| 2^7) 4 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 4 = (!((S0 ||| 2^7)).testBit 4 && ((aoHas (S0 ||| 2^7) 4 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^4)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 4 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^4)))) := rfl
  rw [c76] at e
  exact e.trans (by decide +kernel)

theorem c77 : reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^6) = false := by decide +kernel

theorem c73_d6 : body 8 14 45 4 1 0 (S0 ||| 2^7) 6 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 6 = (!((S0 ||| 2^7)).testBit 6 && ((aoHas (S0 ||| 2^7) 6 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^6)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 6 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^6)))) := rfl
  rw [c77] at e
  exact e.trans (by decide +kernel)

theorem c79 : reach 8 14 45 3 0 ((S0 ||| 2^7) ||| 2^15) = false := by decide +kernel

theorem c80 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^4) = false := by decide +kernel

theorem c78_d4 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 4 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 4 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 4 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 4 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^4)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 4 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^4)))) := rfl
  rw [c80] at e
  exact e.trans (by decide +kernel)

theorem c81 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^6) = false := by decide +kernel

theorem c78_d6 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 6 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 6 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 6 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 6 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^6)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 6 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^6)))) := rfl
  rw [c81] at e
  exact e.trans (by decide +kernel)

theorem c82 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c78_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 8 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 8 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^8)))) := rfl
  rw [c82] at e
  exact e.trans (by decide +kernel)

theorem c83 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c78_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 12 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 12 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^12)))) := rfl
  rw [c83] at e
  exact e.trans (by decide +kernel)

theorem c84 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c78_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 14 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 14 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^14)))) := rfl
  rw [c84] at e
  exact e.trans (by decide +kernel)

theorem c85 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^39) = false := by decide +kernel

theorem c78_d39 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 39 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 39 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 39 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 39 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^39)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 39 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^39)))) := rfl
  rw [c85] at e
  exact e.trans (by decide +kernel)

theorem c86 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c78_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 47 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 47 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^47)))) := rfl
  rw [c86] at e
  exact e.trans (by decide +kernel)

theorem c87 : reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^55) = false := by decide +kernel

theorem c78_d55 : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 55 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) 55 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 55 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 55 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^55)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 55 && reach 8 14 45 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^55)))) := rfl
  rw [c87] at e
  exact e.trans (by decide +kernel)

theorem c78_o : (List.range 64).all (fun v => v == 4 || v == 6 || v == 8 || v == 12 || v == 14 || v == 39 || v == 47 || v == 55 || !body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) v) = true := by decide +kernel

theorem c78_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c78_o v (List.mem_range.mpr hv)
  by_cases h4 : v = 4
  · subst h4; exact c78_d4
  by_cases h6 : v = 6
  · subst h6; exact c78_d6
  by_cases h8 : v = 8
  · subst h8; exact c78_d8
  by_cases h12 : v = 12
  · subst h12; exact c78_d12
  by_cases h14 : v = 14
  · subst h14; exact c78_d14
  by_cases h39 : v = 39
  · subst h39; exact c78_d39
  by_cases h47 : v = 47
  · subst h47; exact c78_d47
  by_cases h55 : v = 55
  · subst h55; exact c78_d55
  simpa [h4, h6, h8, h12, h14, h39, h47, h55] using h

theorem c78 : reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^15) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^7) ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c78_a v (List.mem_range.mp hv)]; decide
  rw [c79, h] at e
  exact e.trans (by decide +kernel)

theorem c73_d15 : body 8 14 45 4 1 0 (S0 ||| 2^7) 15 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 15 = (!((S0 ||| 2^7)).testBit 15 && ((aoHas (S0 ||| 2^7) 15 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 15 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^15)))) := rfl
  rw [c78] at e
  exact e.trans (by decide +kernel)

theorem c88 : reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^31) = false := by decide +kernel

theorem c73_d31 : body 8 14 45 4 1 0 (S0 ||| 2^7) 31 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 31 = (!((S0 ||| 2^7)).testBit 31 && ((aoHas (S0 ||| 2^7) 31 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 31 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^31)))) := rfl
  rw [c88] at e
  exact e.trans (by decide +kernel)

theorem c89 : reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^39) = false := by decide +kernel

theorem c73_d39 : body 8 14 45 4 1 0 (S0 ||| 2^7) 39 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 39 = (!((S0 ||| 2^7)).testBit 39 && ((aoHas (S0 ||| 2^7) 39 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^39)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 39 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^39)))) := rfl
  rw [c89] at e
  exact e.trans (by decide +kernel)

theorem c90 : reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^55) = false := by decide +kernel

theorem c73_d55 : body 8 14 45 4 1 0 (S0 ||| 2^7) 55 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^7) 55 = (!((S0 ||| 2^7)).testBit 55 && ((aoHas (S0 ||| 2^7) 55 && reach 8 14 45 4 1 ((S0 ||| 2^7) ||| 2^55)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 55 && reach 8 14 45 4 0 ((S0 ||| 2^7) ||| 2^55)))) := rfl
  rw [c90] at e
  exact e.trans (by decide +kernel)

theorem c73_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 15 || v == 31 || v == 39 || v == 55 || !body 8 14 45 4 1 0 (S0 ||| 2^7) v) = true := by decide +kernel

theorem c73_a : ∀ v, v < 64 → body 8 14 45 4 1 0 (S0 ||| 2^7) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c73_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c73_d1
  by_cases h3 : v = 3
  · subst h3; exact c73_d3
  by_cases h4 : v = 4
  · subst h4; exact c73_d4
  by_cases h6 : v = 6
  · subst h6; exact c73_d6
  by_cases h15 : v = 15
  · subst h15; exact c73_d15
  by_cases h31 : v = 31
  · subst h31; exact c73_d31
  by_cases h39 : v = 39
  · subst h39; exact c73_d39
  by_cases h55 : v = 55
  · subst h55; exact c73_d55
  simpa [h1, h3, h4, h6, h15, h31, h39, h55] using h

theorem c73 : reach 8 14 45 5 1 (S0 ||| 2^7) = false := by
  have e := reach_succ 8 14 45 4 1 0 (S0 ||| 2^7) rfl
  have h : (List.range 64).any (body 8 14 45 4 1 0 (S0 ||| 2^7)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c73_a v (List.mem_range.mp hv)]; decide
  rw [c7, c24, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d7 : body 8 14 45 5 2 1 S0 7 = false := by
  have e : body 8 14 45 5 2 1 S0 7 = (!(S0).testBit 7 && ((aoHas S0 7 && reach 8 14 45 5 2 (S0 ||| 2^7)) ||
      (decide (0 < 2) && notHas S0 7 && reach 8 14 45 5 1 (S0 ||| 2^7)))) := rfl
  rw [c73] at e
  exact e.trans (by decide +kernel)

theorem c93 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^8) = false := by decide +kernel

theorem c92_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 8 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^8)))) := rfl
  rw [c93] at e
  exact e.trans (by decide +kernel)

theorem c94 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^12) = false := by decide +kernel

theorem c92_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 12 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^12)))) := rfl
  rw [c94] at e
  exact e.trans (by decide +kernel)

theorem c95 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^14) = false := by decide +kernel

theorem c92_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 14 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^14)))) := rfl
  rw [c95] at e
  exact e.trans (by decide +kernel)

theorem c96 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^33) = false := by decide +kernel

theorem c92_d33 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 33 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 33 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 33 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 33 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^33)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 33 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^33)))) := rfl
  rw [c96] at e
  exact e.trans (by decide +kernel)

theorem c97 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^47) = false := by decide +kernel

theorem c92_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 47 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^47)))) := rfl
  rw [c97] at e
  exact e.trans (by decide +kernel)

theorem c98 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^49) = false := by decide +kernel

theorem c92_d49 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 49 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 49 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 49 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 49 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^49)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 49 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^49)))) := rfl
  rw [c98] at e
  exact e.trans (by decide +kernel)

theorem c99 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^57) = false := by decide +kernel

theorem c92_d57 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 57 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 57 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 57 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 57 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^57)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 57 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^57)))) := rfl
  rw [c99] at e
  exact e.trans (by decide +kernel)

theorem c100 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^61) = false := by decide +kernel

theorem c92_d61 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 61 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) 61 = (!(((S0 ||| 2^15) ||| 2^1)).testBit 61 && ((aoHas ((S0 ||| 2^15) ||| 2^1) 61 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^61)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^1) 61 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^1) ||| 2^61)))) := rfl
  rw [c100] at e
  exact e.trans (by decide +kernel)

theorem c92_o : (List.range 64).all (fun v => v == 8 || v == 12 || v == 14 || v == 33 || v == 47 || v == 49 || v == 57 || v == 61 || !body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) v) = true := by decide +kernel

theorem c92_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c92_o v (List.mem_range.mpr hv)
  by_cases h8 : v = 8
  · subst h8; exact c92_d8
  by_cases h12 : v = 12
  · subst h12; exact c92_d12
  by_cases h14 : v = 14
  · subst h14; exact c92_d14
  by_cases h33 : v = 33
  · subst h33; exact c92_d33
  by_cases h47 : v = 47
  · subst h47; exact c92_d47
  by_cases h49 : v = 49
  · subst h49; exact c92_d49
  by_cases h57 : v = 57
  · subst h57; exact c92_d57
  by_cases h61 : v = 61
  · subst h61; exact c92_d61
  simpa [h8, h12, h14, h33, h47, h49, h57, h61] using h

theorem c92 : reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^1) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^1)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c92_a v (List.mem_range.mp hv)]; decide
  rw [c11, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d1 : body 8 14 45 4 1 0 (S0 ||| 2^15) 1 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 1 = (!((S0 ||| 2^15)).testBit 1 && ((aoHas (S0 ||| 2^15) 1 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 1 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^1)))) := rfl
  rw [c92] at e
  exact e.trans (by decide +kernel)

theorem c102 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^2) = false := by decide +kernel

theorem c101_d2 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 2 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 2 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 2 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 2 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^2)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 2 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^2)))) := rfl
  rw [c102] at e
  exact e.trans (by decide +kernel)

theorem c103 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^8) = false := by decide +kernel

theorem c101_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 8 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^8)))) := rfl
  rw [c103] at e
  exact e.trans (by decide +kernel)

theorem c104 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^12) = false := by decide +kernel

theorem c101_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 12 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^12)))) := rfl
  rw [c104] at e
  exact e.trans (by decide +kernel)

theorem c105 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^14) = false := by decide +kernel

theorem c101_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 14 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^14)))) := rfl
  rw [c105] at e
  exact e.trans (by decide +kernel)

theorem c106 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^35) = false := by decide +kernel

theorem c101_d35 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 35 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 35 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 35 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 35 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^35)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 35 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^35)))) := rfl
  rw [c106] at e
  exact e.trans (by decide +kernel)

theorem c107 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^47) = false := by decide +kernel

theorem c101_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 47 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^47)))) := rfl
  rw [c107] at e
  exact e.trans (by decide +kernel)

theorem c108 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^51) = false := by decide +kernel

theorem c101_d51 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 51 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 51 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 51 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 51 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^51)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 51 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^51)))) := rfl
  rw [c108] at e
  exact e.trans (by decide +kernel)

theorem c109 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^59) = false := by decide +kernel

theorem c101_d59 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 59 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) 59 = (!(((S0 ||| 2^15) ||| 2^3)).testBit 59 && ((aoHas ((S0 ||| 2^15) ||| 2^3) 59 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^59)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^3) 59 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^3) ||| 2^59)))) := rfl
  rw [c109] at e
  exact e.trans (by decide +kernel)

theorem c101_o : (List.range 64).all (fun v => v == 2 || v == 8 || v == 12 || v == 14 || v == 35 || v == 47 || v == 51 || v == 59 || !body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) v) = true := by decide +kernel

theorem c101_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c101_o v (List.mem_range.mpr hv)
  by_cases h2 : v = 2
  · subst h2; exact c101_d2
  by_cases h8 : v = 8
  · subst h8; exact c101_d8
  by_cases h12 : v = 12
  · subst h12; exact c101_d12
  by_cases h14 : v = 14
  · subst h14; exact c101_d14
  by_cases h35 : v = 35
  · subst h35; exact c101_d35
  by_cases h47 : v = 47
  · subst h47; exact c101_d47
  by_cases h51 : v = 51
  · subst h51; exact c101_d51
  by_cases h59 : v = 59
  · subst h59; exact c101_d59
  simpa [h2, h8, h12, h14, h35, h47, h51, h59] using h

theorem c101 : reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^3) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^3)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c101_a v (List.mem_range.mp hv)]; decide
  rw [c12, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d3 : body 8 14 45 4 1 0 (S0 ||| 2^15) 3 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 3 = (!((S0 ||| 2^15)).testBit 3 && ((aoHas (S0 ||| 2^15) 3 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 3 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^3)))) := rfl
  rw [c101] at e
  exact e.trans (by decide +kernel)

theorem c111 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^4) = false := by decide +kernel

theorem c110_d4 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 4 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 4 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 4 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 4 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^4)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 4 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^4)))) := rfl
  rw [c111] at e
  exact e.trans (by decide +kernel)

theorem c112 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^6) = false := by decide +kernel

theorem c110_d6 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 6 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 6 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 6 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 6 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^6)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 6 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^6)))) := rfl
  rw [c112] at e
  exact e.trans (by decide +kernel)

theorem c113 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^8) = false := by decide +kernel

theorem c110_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 8 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^8)))) := rfl
  rw [c113] at e
  exact e.trans (by decide +kernel)

theorem c114 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^12) = false := by decide +kernel

theorem c110_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 12 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^12)))) := rfl
  rw [c114] at e
  exact e.trans (by decide +kernel)

theorem c115 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^14) = false := by decide +kernel

theorem c110_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 14 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^14)))) := rfl
  rw [c115] at e
  exact e.trans (by decide +kernel)

theorem c116 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^39) = false := by decide +kernel

theorem c110_d39 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 39 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 39 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 39 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 39 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^39)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 39 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^39)))) := rfl
  rw [c116] at e
  exact e.trans (by decide +kernel)

theorem c117 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^47) = false := by decide +kernel

theorem c110_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 47 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^47)))) := rfl
  rw [c117] at e
  exact e.trans (by decide +kernel)

theorem c118 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^55) = false := by decide +kernel

theorem c110_d55 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 55 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) 55 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 55 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 55 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^55)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 55 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^55)))) := rfl
  rw [c118] at e
  exact e.trans (by decide +kernel)

theorem c110_o : (List.range 64).all (fun v => v == 4 || v == 6 || v == 8 || v == 12 || v == 14 || v == 39 || v == 47 || v == 55 || !body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) v) = true := by decide +kernel

theorem c110_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c110_o v (List.mem_range.mpr hv)
  by_cases h4 : v = 4
  · subst h4; exact c110_d4
  by_cases h6 : v = 6
  · subst h6; exact c110_d6
  by_cases h8 : v = 8
  · subst h8; exact c110_d8
  by_cases h12 : v = 12
  · subst h12; exact c110_d12
  by_cases h14 : v = 14
  · subst h14; exact c110_d14
  by_cases h39 : v = 39
  · subst h39; exact c110_d39
  by_cases h47 : v = 47
  · subst h47; exact c110_d47
  by_cases h55 : v = 55
  · subst h55; exact c110_d55
  simpa [h4, h6, h8, h12, h14, h39, h47, h55] using h

theorem c110 : reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^7) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^7)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c110_a v (List.mem_range.mp hv)]; decide
  rw [c13, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d7 : body 8 14 45 4 1 0 (S0 ||| 2^15) 7 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 7 = (!((S0 ||| 2^15)).testBit 7 && ((aoHas (S0 ||| 2^15) 7 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 7 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^7)))) := rfl
  rw [c110] at e
  exact e.trans (by decide +kernel)

theorem c120 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c121 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^1) = false := by decide +kernel

theorem c119_d1 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 1 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 1 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 1 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 1 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 1 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^1)))) := rfl
  rw [c121] at e
  exact e.trans (by decide +kernel)

theorem c122 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^3) = false := by decide +kernel

theorem c119_d3 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 3 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 3 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 3 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 3 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 3 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^3)))) := rfl
  rw [c122] at e
  exact e.trans (by decide +kernel)

theorem c123 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^7) = false := by decide +kernel

theorem c119_d7 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 7 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 7 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 7 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 7 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 7 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^7)))) := rfl
  rw [c123] at e
  exact e.trans (by decide +kernel)

theorem c124 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^12) = false := by decide +kernel

theorem c119_d12 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 12 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 12 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 12 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^12)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^12)))) := rfl
  rw [c124] at e
  exact e.trans (by decide +kernel)

theorem c126 : reach 8 14 45 2 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) = false := by decide +kernel

theorem c127 : reach 8 14 45 2 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) = false := by decide +kernel

theorem c128 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^1) = false := by decide +kernel

theorem c125_d1 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 1 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 1 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 1 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 1 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 1 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^1)))) := rfl
  rw [c128] at e
  exact e.trans (by decide +kernel)

theorem c129 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^3) = false := by decide +kernel

theorem c125_d3 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 3 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 3 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 3 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 3 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 3 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^3)))) := rfl
  rw [c129] at e
  exact e.trans (by decide +kernel)

theorem c130 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^7) = false := by decide +kernel

theorem c125_d7 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 7 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 7 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 7 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 7 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 7 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^7)))) := rfl
  rw [c130] at e
  exact e.trans (by decide +kernel)

theorem c131 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^12) = false := by decide +kernel

theorem c125_d12 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 12 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 12 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 12 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 12 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^12)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 12 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^12)))) := rfl
  rw [c131] at e
  exact e.trans (by decide +kernel)

theorem c132 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^31) = false := by decide +kernel

theorem c125_d31 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 31 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 31 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 31 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 31 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 31 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^31)))) := rfl
  rw [c132] at e
  exact e.trans (by decide +kernel)

theorem c133 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^40) = false := by decide +kernel

theorem c125_d40 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 40 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 40 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 40 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 40 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^40)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 40 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^40)))) := rfl
  rw [c133] at e
  exact e.trans (by decide +kernel)

theorem c134 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^46) = false := by decide +kernel

theorem c125_d46 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 46 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 46 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 46 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 46 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^46)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 46 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^46)))) := rfl
  rw [c134] at e
  exact e.trans (by decide +kernel)

theorem c135 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^47) = false := by decide +kernel

theorem c125_d47 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 47 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 47 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 47 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 47 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^47)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 47 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^47)))) := rfl
  rw [c135] at e
  exact e.trans (by decide +kernel)

theorem c136 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^49) = false := by decide +kernel

theorem c125_d49 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 49 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 49 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 49 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 49 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^49)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 49 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^49)))) := rfl
  rw [c136] at e
  exact e.trans (by decide +kernel)

theorem c137 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^55) = false := by decide +kernel

theorem c125_d55 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 55 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 55 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^14)).testBit 55 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 55 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^14) 55 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^14) ||| 2^55)))) := rfl
  rw [c137] at e
  exact e.trans (by decide +kernel)

theorem c125_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 12 || v == 31 || v == 40 || v == 46 || v == 47 || v == 49 || v == 55 || !body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) v) = true := by decide +kernel

theorem c125_a : ∀ v, v < 64 → body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c125_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c125_d1
  by_cases h3 : v = 3
  · subst h3; exact c125_d3
  by_cases h7 : v = 7
  · subst h7; exact c125_d7
  by_cases h12 : v = 12
  · subst h12; exact c125_d12
  by_cases h31 : v = 31
  · subst h31; exact c125_d31
  by_cases h40 : v = 40
  · subst h40; exact c125_d40
  by_cases h46 : v = 46
  · subst h46; exact c125_d46
  by_cases h47 : v = 47
  · subst h47; exact c125_d47
  by_cases h49 : v = 49
  · subst h49; exact c125_d49
  by_cases h55 : v = 55
  · subst h55; exact c125_d55
  simpa [h1, h3, h7, h12, h31, h40, h46, h47, h49, h55] using h

theorem c125 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) = false := by
  have e := reach_succ 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14) rfl
  have h : (List.range 64).any (body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c125_a v (List.mem_range.mp hv)]; decide
  rw [c126, c127, h] at e
  exact e.trans (by decide +kernel)

theorem c119_d14 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 14 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 14 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 14 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^14)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^14)))) := rfl
  rw [c125] at e
  exact e.trans (by decide +kernel)

theorem c138 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^31) = false := by decide +kernel

theorem c119_d31 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 31 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 31 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 31 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 31 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 31 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^31)))) := rfl
  rw [c138] at e
  exact e.trans (by decide +kernel)

theorem c139 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^40) = false := by decide +kernel

theorem c119_d40 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 40 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 40 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 40 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 40 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^40)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 40 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^40)))) := rfl
  rw [c139] at e
  exact e.trans (by decide +kernel)

theorem c141 : reach 8 14 45 2 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) = false := by decide +kernel

theorem c142 : reach 8 14 45 2 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) = false := by decide +kernel

theorem c143 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^1) = false := by decide +kernel

theorem c140_d1 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 1 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 1 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 1 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 1 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 1 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^1)))) := rfl
  rw [c143] at e
  exact e.trans (by decide +kernel)

theorem c144 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^3) = false := by decide +kernel

theorem c140_d3 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 3 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 3 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 3 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 3 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 3 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^3)))) := rfl
  rw [c144] at e
  exact e.trans (by decide +kernel)

theorem c145 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^7) = false := by decide +kernel

theorem c140_d7 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 7 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 7 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 7 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 7 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 7 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^7)))) := rfl
  rw [c145] at e
  exact e.trans (by decide +kernel)

theorem c146 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^12) = false := by decide +kernel

theorem c140_d12 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 12 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 12 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 12 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 12 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^12)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 12 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^12)))) := rfl
  rw [c146] at e
  exact e.trans (by decide +kernel)

theorem c147 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^14) = false := by decide +kernel

theorem c140_d14 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 14 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 14 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 14 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 14 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^14)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 14 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^14)))) := rfl
  rw [c147] at e
  exact e.trans (by decide +kernel)

theorem c148 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^16) = false := by decide +kernel

theorem c140_d16 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 16 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 16 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 16 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 16 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^16)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 16 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^16)))) := rfl
  rw [c148] at e
  exact e.trans (by decide +kernel)

theorem c149 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^31) = false := by decide +kernel

theorem c140_d31 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 31 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 31 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 31 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 31 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 31 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^31)))) := rfl
  rw [c149] at e
  exact e.trans (by decide +kernel)

theorem c150 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^40) = false := by decide +kernel

theorem c140_d40 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 40 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 40 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 40 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 40 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^40)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 40 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^40)))) := rfl
  rw [c150] at e
  exact e.trans (by decide +kernel)

theorem c151 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^44) = false := by decide +kernel

theorem c140_d44 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 44 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 44 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 44 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 44 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^44)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 44 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^44)))) := rfl
  rw [c151] at e
  exact e.trans (by decide +kernel)

theorem c152 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^46) = false := by decide +kernel

theorem c140_d46 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 46 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 46 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 46 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 46 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^46)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 46 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^46)))) := rfl
  rw [c152] at e
  exact e.trans (by decide +kernel)

theorem c153 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^55) = false := by decide +kernel

theorem c140_d55 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 55 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 55 = (!((((S0 ||| 2^15) ||| 2^8) ||| 2^47)).testBit 55 && ((aoHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 55 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^8) ||| 2^47) 55 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^8) ||| 2^47) ||| 2^55)))) := rfl
  rw [c153] at e
  exact e.trans (by decide +kernel)

theorem c140_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 12 || v == 14 || v == 16 || v == 31 || v == 40 || v == 44 || v == 46 || v == 55 || !body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) v) = true := by decide +kernel

theorem c140_a : ∀ v, v < 64 → body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c140_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c140_d1
  by_cases h3 : v = 3
  · subst h3; exact c140_d3
  by_cases h7 : v = 7
  · subst h7; exact c140_d7
  by_cases h12 : v = 12
  · subst h12; exact c140_d12
  by_cases h14 : v = 14
  · subst h14; exact c140_d14
  by_cases h16 : v = 16
  · subst h16; exact c140_d16
  by_cases h31 : v = 31
  · subst h31; exact c140_d31
  by_cases h40 : v = 40
  · subst h40; exact c140_d40
  by_cases h44 : v = 44
  · subst h44; exact c140_d44
  by_cases h46 : v = 46
  · subst h46; exact c140_d46
  by_cases h55 : v = 55
  · subst h55; exact c140_d55
  simpa [h1, h3, h7, h12, h14, h16, h31, h40, h44, h46, h55] using h

theorem c140 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) = false := by
  have e := reach_succ 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47) rfl
  have h : (List.range 64).any (body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c140_a v (List.mem_range.mp hv)]; decide
  rw [c141, c142, h] at e
  exact e.trans (by decide +kernel)

theorem c119_d47 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 47 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 47 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 47 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^47)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^47)))) := rfl
  rw [c140] at e
  exact e.trans (by decide +kernel)

theorem c154 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^55) = false := by decide +kernel

theorem c119_d55 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 55 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) 55 = (!(((S0 ||| 2^15) ||| 2^8)).testBit 55 && ((aoHas ((S0 ||| 2^15) ||| 2^8) 55 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^8) ||| 2^55)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^8) 55 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^8) ||| 2^55)))) := rfl
  rw [c154] at e
  exact e.trans (by decide +kernel)

theorem c119_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 12 || v == 14 || v == 31 || v == 40 || v == 47 || v == 55 || !body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) v) = true := by decide +kernel

theorem c119_a : ∀ v, v < 64 → body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c119_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c119_d1
  by_cases h3 : v = 3
  · subst h3; exact c119_d3
  by_cases h7 : v = 7
  · subst h7; exact c119_d7
  by_cases h12 : v = 12
  · subst h12; exact c119_d12
  by_cases h14 : v = 14
  · subst h14; exact c119_d14
  by_cases h31 : v = 31
  · subst h31; exact c119_d31
  by_cases h40 : v = 40
  · subst h40; exact c119_d40
  by_cases h47 : v = 47
  · subst h47; exact c119_d47
  by_cases h55 : v = 55
  · subst h55; exact c119_d55
  simpa [h1, h3, h7, h12, h14, h31, h40, h47, h55] using h

theorem c119 : reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^8) = false := by
  have e := reach_succ 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8) rfl
  have h : (List.range 64).any (body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^8)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c119_a v (List.mem_range.mp hv)]; decide
  rw [c14, c120, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d8 : body 8 14 45 4 1 0 (S0 ||| 2^15) 8 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 8 = (!((S0 ||| 2^15)).testBit 8 && ((aoHas (S0 ||| 2^15) 8 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^8)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 8 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^8)))) := rfl
  rw [c119] at e
  exact e.trans (by decide +kernel)

theorem c156 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c157 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^1) = false := by decide +kernel

theorem c155_d1 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 1 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 1 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 1 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 1 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 1 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^1)))) := rfl
  rw [c157] at e
  exact e.trans (by decide +kernel)

theorem c158 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^3) = false := by decide +kernel

theorem c155_d3 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 3 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 3 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 3 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 3 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 3 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^3)))) := rfl
  rw [c158] at e
  exact e.trans (by decide +kernel)

theorem c159 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^7) = false := by decide +kernel

theorem c155_d7 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 7 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 7 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 7 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 7 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 7 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^7)))) := rfl
  rw [c159] at e
  exact e.trans (by decide +kernel)

theorem c160 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^8) = false := by decide +kernel

theorem c155_d8 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 8 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 8 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 8 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^8)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^8)))) := rfl
  rw [c160] at e
  exact e.trans (by decide +kernel)

theorem c161 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^14) = false := by decide +kernel

theorem c155_d14 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 14 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 14 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 14 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^14)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^14)))) := rfl
  rw [c161] at e
  exact e.trans (by decide +kernel)

theorem c162 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^31) = false := by decide +kernel

theorem c155_d31 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 31 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 31 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 31 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 31 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 31 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^31)))) := rfl
  rw [c162] at e
  exact e.trans (by decide +kernel)

theorem c163 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^44) = false := by decide +kernel

theorem c155_d44 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 44 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 44 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 44 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 44 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^44)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 44 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^44)))) := rfl
  rw [c163] at e
  exact e.trans (by decide +kernel)

theorem c164 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^47) = false := by decide +kernel

theorem c155_d47 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 47 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 47 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 47 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^47)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^47)))) := rfl
  rw [c164] at e
  exact e.trans (by decide +kernel)

theorem c165 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^51) = false := by decide +kernel

theorem c155_d51 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 51 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) 51 = (!(((S0 ||| 2^15) ||| 2^12)).testBit 51 && ((aoHas ((S0 ||| 2^15) ||| 2^12) 51 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^12) ||| 2^51)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^12) 51 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^12) ||| 2^51)))) := rfl
  rw [c165] at e
  exact e.trans (by decide +kernel)

theorem c155_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 14 || v == 31 || v == 44 || v == 47 || v == 51 || !body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) v) = true := by decide +kernel

theorem c155_a : ∀ v, v < 64 → body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c155_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c155_d1
  by_cases h3 : v = 3
  · subst h3; exact c155_d3
  by_cases h7 : v = 7
  · subst h7; exact c155_d7
  by_cases h8 : v = 8
  · subst h8; exact c155_d8
  by_cases h14 : v = 14
  · subst h14; exact c155_d14
  by_cases h31 : v = 31
  · subst h31; exact c155_d31
  by_cases h44 : v = 44
  · subst h44; exact c155_d44
  by_cases h47 : v = 47
  · subst h47; exact c155_d47
  by_cases h51 : v = 51
  · subst h51; exact c155_d51
  simpa [h1, h3, h7, h8, h14, h31, h44, h47, h51] using h

theorem c155 : reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^12) = false := by
  have e := reach_succ 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12) rfl
  have h : (List.range 64).any (body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^12)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c155_a v (List.mem_range.mp hv)]; decide
  rw [c15, c156, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d12 : body 8 14 45 4 1 0 (S0 ||| 2^15) 12 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 12 = (!((S0 ||| 2^15)).testBit 12 && ((aoHas (S0 ||| 2^15) 12 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^12)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 12 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^12)))) := rfl
  rw [c155] at e
  exact e.trans (by decide +kernel)

theorem c167 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c168 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^1) = false := by decide +kernel

theorem c166_d1 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 1 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 1 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 1 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 1 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 1 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^1)))) := rfl
  rw [c168] at e
  exact e.trans (by decide +kernel)

theorem c169 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^3) = false := by decide +kernel

theorem c166_d3 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 3 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 3 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 3 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 3 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 3 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^3)))) := rfl
  rw [c169] at e
  exact e.trans (by decide +kernel)

theorem c170 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^7) = false := by decide +kernel

theorem c166_d7 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 7 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 7 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 7 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 7 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 7 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^7)))) := rfl
  rw [c170] at e
  exact e.trans (by decide +kernel)

theorem c172 : reach 8 14 45 2 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) = false := by decide +kernel

theorem c173 : reach 8 14 45 2 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) = false := by decide +kernel

theorem c174 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^1) = false := by decide +kernel

theorem c171_d1 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 1 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 1 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 1 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 1 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 1 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^1)))) := rfl
  rw [c174] at e
  exact e.trans (by decide +kernel)

theorem c175 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^3) = false := by decide +kernel

theorem c171_d3 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 3 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 3 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 3 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 3 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 3 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^3)))) := rfl
  rw [c175] at e
  exact e.trans (by decide +kernel)

theorem c176 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^7) = false := by decide +kernel

theorem c171_d7 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 7 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 7 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 7 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 7 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 7 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^7)))) := rfl
  rw [c176] at e
  exact e.trans (by decide +kernel)

theorem c177 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^12) = false := by decide +kernel

theorem c171_d12 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 12 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 12 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 12 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 12 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^12)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 12 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^12)))) := rfl
  rw [c177] at e
  exact e.trans (by decide +kernel)

theorem c178 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^31) = false := by decide +kernel

theorem c171_d31 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 31 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 31 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 31 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 31 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 31 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^31)))) := rfl
  rw [c178] at e
  exact e.trans (by decide +kernel)

theorem c179 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^40) = false := by decide +kernel

theorem c171_d40 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 40 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 40 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 40 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 40 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^40)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 40 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^40)))) := rfl
  rw [c179] at e
  exact e.trans (by decide +kernel)

theorem c180 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^46) = false := by decide +kernel

theorem c171_d46 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 46 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 46 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 46 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 46 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^46)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 46 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^46)))) := rfl
  rw [c180] at e
  exact e.trans (by decide +kernel)

theorem c181 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^47) = false := by decide +kernel

theorem c171_d47 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 47 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 47 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 47 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 47 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^47)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 47 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^47)))) := rfl
  rw [c181] at e
  exact e.trans (by decide +kernel)

theorem c182 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^49) = false := by decide +kernel

theorem c171_d49 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 49 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 49 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 49 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 49 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^49)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 49 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^49)))) := rfl
  rw [c182] at e
  exact e.trans (by decide +kernel)

theorem c183 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^55) = false := by decide +kernel

theorem c171_d55 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 55 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 55 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^8)).testBit 55 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 55 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^8) 55 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^8) ||| 2^55)))) := rfl
  rw [c183] at e
  exact e.trans (by decide +kernel)

theorem c171_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 12 || v == 31 || v == 40 || v == 46 || v == 47 || v == 49 || v == 55 || !body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) v) = true := by decide +kernel

theorem c171_a : ∀ v, v < 64 → body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c171_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c171_d1
  by_cases h3 : v = 3
  · subst h3; exact c171_d3
  by_cases h7 : v = 7
  · subst h7; exact c171_d7
  by_cases h12 : v = 12
  · subst h12; exact c171_d12
  by_cases h31 : v = 31
  · subst h31; exact c171_d31
  by_cases h40 : v = 40
  · subst h40; exact c171_d40
  by_cases h46 : v = 46
  · subst h46; exact c171_d46
  by_cases h47 : v = 47
  · subst h47; exact c171_d47
  by_cases h49 : v = 49
  · subst h49; exact c171_d49
  by_cases h55 : v = 55
  · subst h55; exact c171_d55
  simpa [h1, h3, h7, h12, h31, h40, h46, h47, h49, h55] using h

theorem c171 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) = false := by
  have e := reach_succ 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8) rfl
  have h : (List.range 64).any (body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c171_a v (List.mem_range.mp hv)]; decide
  rw [c172, c173, h] at e
  exact e.trans (by decide +kernel)

theorem c166_d8 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 8 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 8 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 8 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^8)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^8)))) := rfl
  rw [c171] at e
  exact e.trans (by decide +kernel)

theorem c184 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^12) = false := by decide +kernel

theorem c166_d12 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 12 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 12 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 12 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^12)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^12)))) := rfl
  rw [c184] at e
  exact e.trans (by decide +kernel)

theorem c185 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^31) = false := by decide +kernel

theorem c166_d31 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 31 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 31 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 31 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 31 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 31 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^31)))) := rfl
  rw [c185] at e
  exact e.trans (by decide +kernel)

theorem c187 : reach 8 14 45 2 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) = false := by decide +kernel

theorem c188 : reach 8 14 45 2 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) = false := by decide +kernel

theorem c189 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^1) = false := by decide +kernel

theorem c186_d1 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 1 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 1 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 1 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 1 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 1 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^1)))) := rfl
  rw [c189] at e
  exact e.trans (by decide +kernel)

theorem c190 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^3) = false := by decide +kernel

theorem c186_d3 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 3 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 3 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 3 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 3 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 3 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^3)))) := rfl
  rw [c190] at e
  exact e.trans (by decide +kernel)

theorem c191 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^7) = false := by decide +kernel

theorem c186_d7 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 7 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 7 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 7 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 7 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 7 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^7)))) := rfl
  rw [c191] at e
  exact e.trans (by decide +kernel)

theorem c192 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^8) = false := by decide +kernel

theorem c186_d8 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 8 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 8 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 8 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 8 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^8)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 8 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^8)))) := rfl
  rw [c192] at e
  exact e.trans (by decide +kernel)

theorem c193 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^12) = false := by decide +kernel

theorem c186_d12 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 12 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 12 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 12 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 12 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^12)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 12 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^12)))) := rfl
  rw [c193] at e
  exact e.trans (by decide +kernel)

theorem c194 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^17) = false := by decide +kernel

theorem c186_d17 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 17 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 17 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 17 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 17 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^17)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 17 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^17)))) := rfl
  rw [c194] at e
  exact e.trans (by decide +kernel)

theorem c195 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^31) = false := by decide +kernel

theorem c186_d31 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 31 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 31 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 31 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 31 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 31 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^31)))) := rfl
  rw [c195] at e
  exact e.trans (by decide +kernel)

theorem c196 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^40) = false := by decide +kernel

theorem c186_d40 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 40 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 40 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 40 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 40 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^40)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 40 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^40)))) := rfl
  rw [c196] at e
  exact e.trans (by decide +kernel)

theorem c197 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^44) = false := by decide +kernel

theorem c186_d44 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 44 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 44 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 44 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 44 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^44)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 44 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^44)))) := rfl
  rw [c197] at e
  exact e.trans (by decide +kernel)

theorem c198 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^47) = false := by decide +kernel

theorem c186_d47 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 47 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 47 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 47 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 47 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^47)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 47 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^47)))) := rfl
  rw [c198] at e
  exact e.trans (by decide +kernel)

theorem c199 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^49) = false := by decide +kernel

theorem c186_d49 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 49 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 49 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^46)).testBit 49 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 49 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^49)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^46) 49 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^46) ||| 2^49)))) := rfl
  rw [c199] at e
  exact e.trans (by decide +kernel)

theorem c186_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 17 || v == 31 || v == 40 || v == 44 || v == 47 || v == 49 || !body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) v) = true := by decide +kernel

theorem c186_a : ∀ v, v < 64 → body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c186_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c186_d1
  by_cases h3 : v = 3
  · subst h3; exact c186_d3
  by_cases h7 : v = 7
  · subst h7; exact c186_d7
  by_cases h8 : v = 8
  · subst h8; exact c186_d8
  by_cases h12 : v = 12
  · subst h12; exact c186_d12
  by_cases h17 : v = 17
  · subst h17; exact c186_d17
  by_cases h31 : v = 31
  · subst h31; exact c186_d31
  by_cases h40 : v = 40
  · subst h40; exact c186_d40
  by_cases h44 : v = 44
  · subst h44; exact c186_d44
  by_cases h47 : v = 47
  · subst h47; exact c186_d47
  by_cases h49 : v = 49
  · subst h49; exact c186_d49
  simpa [h1, h3, h7, h8, h12, h17, h31, h40, h44, h47, h49] using h

theorem c186 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) = false := by
  have e := reach_succ 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46) rfl
  have h : (List.range 64).any (body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c186_a v (List.mem_range.mp hv)]; decide
  rw [c187, c188, h] at e
  exact e.trans (by decide +kernel)

theorem c166_d46 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 46 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 46 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 46 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 46 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^46)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 46 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^46)))) := rfl
  rw [c186] at e
  exact e.trans (by decide +kernel)

theorem c201 : reach 8 14 45 2 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) = false := by decide +kernel

theorem c202 : reach 8 14 45 2 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) = false := by decide +kernel

theorem c203 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^1) = false := by decide +kernel

theorem c200_d1 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 1 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 1 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 1 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 1 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 1 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^1)))) := rfl
  rw [c203] at e
  exact e.trans (by decide +kernel)

theorem c204 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^3) = false := by decide +kernel

theorem c200_d3 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 3 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 3 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 3 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 3 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 3 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^3)))) := rfl
  rw [c204] at e
  exact e.trans (by decide +kernel)

theorem c205 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^7) = false := by decide +kernel

theorem c200_d7 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 7 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 7 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 7 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 7 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 7 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^7)))) := rfl
  rw [c205] at e
  exact e.trans (by decide +kernel)

theorem c206 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^8) = false := by decide +kernel

theorem c200_d8 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 8 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 8 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 8 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 8 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^8)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 8 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^8)))) := rfl
  rw [c206] at e
  exact e.trans (by decide +kernel)

theorem c207 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^12) = false := by decide +kernel

theorem c200_d12 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 12 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 12 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 12 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 12 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^12)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 12 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^12)))) := rfl
  rw [c207] at e
  exact e.trans (by decide +kernel)

theorem c208 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^16) = false := by decide +kernel

theorem c200_d16 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 16 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 16 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 16 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 16 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^16)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 16 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^16)))) := rfl
  rw [c208] at e
  exact e.trans (by decide +kernel)

theorem c209 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^31) = false := by decide +kernel

theorem c200_d31 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 31 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 31 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 31 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 31 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 31 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^31)))) := rfl
  rw [c209] at e
  exact e.trans (by decide +kernel)

theorem c210 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^40) = false := by decide +kernel

theorem c200_d40 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 40 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 40 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 40 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 40 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^40)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 40 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^40)))) := rfl
  rw [c210] at e
  exact e.trans (by decide +kernel)

theorem c211 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^44) = false := by decide +kernel

theorem c200_d44 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 44 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 44 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 44 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 44 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^44)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 44 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^44)))) := rfl
  rw [c211] at e
  exact e.trans (by decide +kernel)

theorem c212 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^46) = false := by decide +kernel

theorem c200_d46 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 46 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 46 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 46 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 46 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^46)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 46 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^46)))) := rfl
  rw [c212] at e
  exact e.trans (by decide +kernel)

theorem c213 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^49) = false := by decide +kernel

theorem c200_d49 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 49 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 49 = (!((((S0 ||| 2^15) ||| 2^14) ||| 2^47)).testBit 49 && ((aoHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 49 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^49)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^14) ||| 2^47) 49 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^14) ||| 2^47) ||| 2^49)))) := rfl
  rw [c213] at e
  exact e.trans (by decide +kernel)

theorem c200_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 16 || v == 31 || v == 40 || v == 44 || v == 46 || v == 49 || !body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) v) = true := by decide +kernel

theorem c200_a : ∀ v, v < 64 → body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c200_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c200_d1
  by_cases h3 : v = 3
  · subst h3; exact c200_d3
  by_cases h7 : v = 7
  · subst h7; exact c200_d7
  by_cases h8 : v = 8
  · subst h8; exact c200_d8
  by_cases h12 : v = 12
  · subst h12; exact c200_d12
  by_cases h16 : v = 16
  · subst h16; exact c200_d16
  by_cases h31 : v = 31
  · subst h31; exact c200_d31
  by_cases h40 : v = 40
  · subst h40; exact c200_d40
  by_cases h44 : v = 44
  · subst h44; exact c200_d44
  by_cases h46 : v = 46
  · subst h46; exact c200_d46
  by_cases h49 : v = 49
  · subst h49; exact c200_d49
  simpa [h1, h3, h7, h8, h12, h16, h31, h40, h44, h46, h49] using h

theorem c200 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) = false := by
  have e := reach_succ 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47) rfl
  have h : (List.range 64).any (body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c200_a v (List.mem_range.mp hv)]; decide
  rw [c201, c202, h] at e
  exact e.trans (by decide +kernel)

theorem c166_d47 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 47 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 47 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 47 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^47)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^47)))) := rfl
  rw [c200] at e
  exact e.trans (by decide +kernel)

theorem c214 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^49) = false := by decide +kernel

theorem c166_d49 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 49 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) 49 = (!(((S0 ||| 2^15) ||| 2^14)).testBit 49 && ((aoHas ((S0 ||| 2^15) ||| 2^14) 49 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^14) ||| 2^49)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^14) 49 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^14) ||| 2^49)))) := rfl
  rw [c214] at e
  exact e.trans (by decide +kernel)

theorem c166_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 31 || v == 46 || v == 47 || v == 49 || !body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) v) = true := by decide +kernel

theorem c166_a : ∀ v, v < 64 → body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c166_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c166_d1
  by_cases h3 : v = 3
  · subst h3; exact c166_d3
  by_cases h7 : v = 7
  · subst h7; exact c166_d7
  by_cases h8 : v = 8
  · subst h8; exact c166_d8
  by_cases h12 : v = 12
  · subst h12; exact c166_d12
  by_cases h31 : v = 31
  · subst h31; exact c166_d31
  by_cases h46 : v = 46
  · subst h46; exact c166_d46
  by_cases h47 : v = 47
  · subst h47; exact c166_d47
  by_cases h49 : v = 49
  · subst h49; exact c166_d49
  simpa [h1, h3, h7, h8, h12, h31, h46, h47, h49] using h

theorem c166 : reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^14) = false := by
  have e := reach_succ 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14) rfl
  have h : (List.range 64).any (body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^14)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c166_a v (List.mem_range.mp hv)]; decide
  rw [c16, c167, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d14 : body 8 14 45 4 1 0 (S0 ||| 2^15) 14 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 14 = (!((S0 ||| 2^15)).testBit 14 && ((aoHas (S0 ||| 2^15) 14 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^14)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 14 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^14)))) := rfl
  rw [c166] at e
  exact e.trans (by decide +kernel)

theorem c216 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^8) = false := by decide +kernel

theorem c215_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 8 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^8)))) := rfl
  rw [c216] at e
  exact e.trans (by decide +kernel)

theorem c217 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^12) = false := by decide +kernel

theorem c215_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 12 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^12)))) := rfl
  rw [c217] at e
  exact e.trans (by decide +kernel)

theorem c218 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^14) = false := by decide +kernel

theorem c215_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 14 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^14)))) := rfl
  rw [c218] at e
  exact e.trans (by decide +kernel)

theorem c219 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^16) = false := by decide +kernel

theorem c215_d16 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 16 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 16 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 16 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 16 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^16)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 16 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^16)))) := rfl
  rw [c219] at e
  exact e.trans (by decide +kernel)

theorem c220 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^24) = false := by decide +kernel

theorem c215_d24 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 24 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 24 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 24 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 24 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^24)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 24 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^24)))) := rfl
  rw [c220] at e
  exact e.trans (by decide +kernel)

theorem c221 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^28) = false := by decide +kernel

theorem c215_d28 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 28 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 28 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 28 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 28 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^28)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 28 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^28)))) := rfl
  rw [c221] at e
  exact e.trans (by decide +kernel)

theorem c222 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^30) = false := by decide +kernel

theorem c215_d30 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 30 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 30 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 30 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 30 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^30)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 30 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^30)))) := rfl
  rw [c222] at e
  exact e.trans (by decide +kernel)

theorem c223 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^47) = false := by decide +kernel

theorem c215_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) 47 = (!(((S0 ||| 2^15) ||| 2^31)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^31) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^31) 47 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^31) ||| 2^47)))) := rfl
  rw [c223] at e
  exact e.trans (by decide +kernel)

theorem c215_o : (List.range 64).all (fun v => v == 8 || v == 12 || v == 14 || v == 16 || v == 24 || v == 28 || v == 30 || v == 47 || !body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) v) = true := by decide +kernel

theorem c215_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c215_o v (List.mem_range.mpr hv)
  by_cases h8 : v = 8
  · subst h8; exact c215_d8
  by_cases h12 : v = 12
  · subst h12; exact c215_d12
  by_cases h14 : v = 14
  · subst h14; exact c215_d14
  by_cases h16 : v = 16
  · subst h16; exact c215_d16
  by_cases h24 : v = 24
  · subst h24; exact c215_d24
  by_cases h28 : v = 28
  · subst h28; exact c215_d28
  by_cases h30 : v = 30
  · subst h30; exact c215_d30
  by_cases h47 : v = 47
  · subst h47; exact c215_d47
  simpa [h8, h12, h14, h16, h24, h28, h30, h47] using h

theorem c215 : reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^31) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^15) ||| 2^31)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c215_a v (List.mem_range.mp hv)]; decide
  rw [c17, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d31 : body 8 14 45 4 1 0 (S0 ||| 2^15) 31 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 31 = (!((S0 ||| 2^15)).testBit 31 && ((aoHas (S0 ||| 2^15) 31 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 31 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^31)))) := rfl
  rw [c215] at e
  exact e.trans (by decide +kernel)

theorem c225 : reach 8 14 45 3 0 ((S0 ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c226 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^1) = false := by decide +kernel

theorem c224_d1 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 1 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 1 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 1 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 1 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 1 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^1)))) := rfl
  rw [c226] at e
  exact e.trans (by decide +kernel)

theorem c227 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^3) = false := by decide +kernel

theorem c224_d3 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 3 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 3 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 3 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 3 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 3 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^3)))) := rfl
  rw [c227] at e
  exact e.trans (by decide +kernel)

theorem c228 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^7) = false := by decide +kernel

theorem c224_d7 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 7 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 7 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 7 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 7 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 7 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^7)))) := rfl
  rw [c228] at e
  exact e.trans (by decide +kernel)

theorem c230 : reach 8 14 45 2 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) = false := by decide +kernel

theorem c231 : reach 8 14 45 2 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) = false := by decide +kernel

theorem c232 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^1) = false := by decide +kernel

theorem c229_d1 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 1 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 1 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 1 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 1 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 1 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^1)))) := rfl
  rw [c232] at e
  exact e.trans (by decide +kernel)

theorem c233 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^3) = false := by decide +kernel

theorem c229_d3 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 3 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 3 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 3 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 3 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 3 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^3)))) := rfl
  rw [c233] at e
  exact e.trans (by decide +kernel)

theorem c234 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^7) = false := by decide +kernel

theorem c229_d7 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 7 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 7 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 7 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 7 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 7 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^7)))) := rfl
  rw [c234] at e
  exact e.trans (by decide +kernel)

theorem c235 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^12) = false := by decide +kernel

theorem c229_d12 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 12 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 12 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 12 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 12 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^12)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 12 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^12)))) := rfl
  rw [c235] at e
  exact e.trans (by decide +kernel)

theorem c236 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^14) = false := by decide +kernel

theorem c229_d14 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 14 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 14 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 14 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 14 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^14)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 14 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^14)))) := rfl
  rw [c236] at e
  exact e.trans (by decide +kernel)

theorem c237 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^16) = false := by decide +kernel

theorem c229_d16 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 16 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 16 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 16 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 16 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^16)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 16 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^16)))) := rfl
  rw [c237] at e
  exact e.trans (by decide +kernel)

theorem c238 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^31) = false := by decide +kernel

theorem c229_d31 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 31 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 31 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 31 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 31 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 31 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^31)))) := rfl
  rw [c238] at e
  exact e.trans (by decide +kernel)

theorem c239 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^40) = false := by decide +kernel

theorem c229_d40 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 40 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 40 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 40 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 40 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^40)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 40 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^40)))) := rfl
  rw [c239] at e
  exact e.trans (by decide +kernel)

theorem c240 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^44) = false := by decide +kernel

theorem c229_d44 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 44 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 44 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 44 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 44 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^44)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 44 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^44)))) := rfl
  rw [c240] at e
  exact e.trans (by decide +kernel)

theorem c241 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^46) = false := by decide +kernel

theorem c229_d46 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 46 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 46 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 46 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 46 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^46)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 46 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^46)))) := rfl
  rw [c241] at e
  exact e.trans (by decide +kernel)

theorem c242 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^55) = false := by decide +kernel

theorem c229_d55 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 55 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 55 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^8)).testBit 55 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 55 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^8) 55 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^8) ||| 2^55)))) := rfl
  rw [c242] at e
  exact e.trans (by decide +kernel)

theorem c229_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 12 || v == 14 || v == 16 || v == 31 || v == 40 || v == 44 || v == 46 || v == 55 || !body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) v) = true := by decide +kernel

theorem c229_a : ∀ v, v < 64 → body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c229_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c229_d1
  by_cases h3 : v = 3
  · subst h3; exact c229_d3
  by_cases h7 : v = 7
  · subst h7; exact c229_d7
  by_cases h12 : v = 12
  · subst h12; exact c229_d12
  by_cases h14 : v = 14
  · subst h14; exact c229_d14
  by_cases h16 : v = 16
  · subst h16; exact c229_d16
  by_cases h31 : v = 31
  · subst h31; exact c229_d31
  by_cases h40 : v = 40
  · subst h40; exact c229_d40
  by_cases h44 : v = 44
  · subst h44; exact c229_d44
  by_cases h46 : v = 46
  · subst h46; exact c229_d46
  by_cases h55 : v = 55
  · subst h55; exact c229_d55
  simpa [h1, h3, h7, h12, h14, h16, h31, h40, h44, h46, h55] using h

theorem c229 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) = false := by
  have e := reach_succ 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) rfl
  have h : (List.range 64).any (body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c229_a v (List.mem_range.mp hv)]; decide
  rw [c230, c231, h] at e
  exact e.trans (by decide +kernel)

theorem c224_d8 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 8 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 8 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 8 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^8)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 8 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8)))) := rfl
  rw [c229] at e
  exact e.trans (by decide +kernel)

theorem c243 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^12) = false := by decide +kernel

theorem c224_d12 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 12 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 12 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 12 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^12)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 12 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^12)))) := rfl
  rw [c243] at e
  exact e.trans (by decide +kernel)

theorem c245 : reach 8 14 45 2 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) = false := by decide +kernel

theorem c246 : reach 8 14 45 2 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) = false := by decide +kernel

theorem c247 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^1) = false := by decide +kernel

theorem c244_d1 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 1 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 1 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 1 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 1 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 1 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^1)))) := rfl
  rw [c247] at e
  exact e.trans (by decide +kernel)

theorem c248 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^3) = false := by decide +kernel

theorem c244_d3 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 3 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 3 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 3 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 3 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 3 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^3)))) := rfl
  rw [c248] at e
  exact e.trans (by decide +kernel)

theorem c249 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^7) = false := by decide +kernel

theorem c244_d7 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 7 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 7 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 7 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 7 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^7)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 7 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^7)))) := rfl
  rw [c249] at e
  exact e.trans (by decide +kernel)

theorem c250 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^8) = false := by decide +kernel

theorem c244_d8 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 8 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 8 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 8 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 8 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^8)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 8 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^8)))) := rfl
  rw [c250] at e
  exact e.trans (by decide +kernel)

theorem c251 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^12) = false := by decide +kernel

theorem c244_d12 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 12 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 12 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 12 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 12 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^12)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 12 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^12)))) := rfl
  rw [c251] at e
  exact e.trans (by decide +kernel)

theorem c252 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^16) = false := by decide +kernel

theorem c244_d16 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 16 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 16 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 16 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 16 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^16)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 16 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^16)))) := rfl
  rw [c252] at e
  exact e.trans (by decide +kernel)

theorem c253 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^31) = false := by decide +kernel

theorem c244_d31 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 31 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 31 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 31 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 31 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 31 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^31)))) := rfl
  rw [c253] at e
  exact e.trans (by decide +kernel)

theorem c254 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^40) = false := by decide +kernel

theorem c244_d40 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 40 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 40 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 40 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 40 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^40)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 40 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^40)))) := rfl
  rw [c254] at e
  exact e.trans (by decide +kernel)

theorem c255 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^44) = false := by decide +kernel

theorem c244_d44 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 44 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 44 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 44 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 44 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^44)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 44 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^44)))) := rfl
  rw [c255] at e
  exact e.trans (by decide +kernel)

theorem c256 : reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^46) = false := by decide +kernel

theorem c244_d46 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 46 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 46 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 46 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 46 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^46)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 46 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^46)))) := rfl
  rw [c256] at e
  exact e.trans (by decide +kernel)

theorem c257 : reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^49) = false := by decide +kernel

theorem c244_d49 : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 49 = false := by
  have e : body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 49 = (!((((S0 ||| 2^15) ||| 2^47) ||| 2^14)).testBit 49 && ((aoHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 49 && reach 8 14 45 2 1 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^49)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^15) ||| 2^47) ||| 2^14) 49 && reach 8 14 45 2 0 ((((S0 ||| 2^15) ||| 2^47) ||| 2^14) ||| 2^49)))) := rfl
  rw [c257] at e
  exact e.trans (by decide +kernel)

theorem c244_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 16 || v == 31 || v == 40 || v == 44 || v == 46 || v == 49 || !body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) v) = true := by decide +kernel

theorem c244_a : ∀ v, v < 64 → body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c244_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c244_d1
  by_cases h3 : v = 3
  · subst h3; exact c244_d3
  by_cases h7 : v = 7
  · subst h7; exact c244_d7
  by_cases h8 : v = 8
  · subst h8; exact c244_d8
  by_cases h12 : v = 12
  · subst h12; exact c244_d12
  by_cases h16 : v = 16
  · subst h16; exact c244_d16
  by_cases h31 : v = 31
  · subst h31; exact c244_d31
  by_cases h40 : v = 40
  · subst h40; exact c244_d40
  by_cases h44 : v = 44
  · subst h44; exact c244_d44
  by_cases h46 : v = 46
  · subst h46; exact c244_d46
  by_cases h49 : v = 49
  · subst h49; exact c244_d49
  simpa [h1, h3, h7, h8, h12, h16, h31, h40, h44, h46, h49] using h

theorem c244 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) = false := by
  have e := reach_succ 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) rfl
  have h : (List.range 64).any (body 8 14 45 2 1 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c244_a v (List.mem_range.mp hv)]; decide
  rw [c245, c246, h] at e
  exact e.trans (by decide +kernel)

theorem c224_d14 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 14 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 14 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 14 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^14)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 14 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14)))) := rfl
  rw [c244] at e
  exact e.trans (by decide +kernel)

theorem c258 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^16) = false := by decide +kernel

theorem c224_d16 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 16 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 16 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 16 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 16 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^16)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 16 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^16)))) := rfl
  rw [c258] at e
  exact e.trans (by decide +kernel)

theorem c259 : reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^31) = false := by decide +kernel

theorem c224_d31 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 31 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 31 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 31 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 31 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 31 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^31)))) := rfl
  rw [c259] at e
  exact e.trans (by decide +kernel)

theorem c260 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^40) = false := by decide +kernel

theorem c224_d40 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 40 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 40 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 40 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 40 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^40)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 40 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^40)))) := rfl
  rw [c260] at e
  exact e.trans (by decide +kernel)

theorem c261 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^44) = false := by decide +kernel

theorem c224_d44 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 44 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 44 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 44 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 44 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^44)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 44 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^44)))) := rfl
  rw [c261] at e
  exact e.trans (by decide +kernel)

theorem c262 : reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^46) = false := by decide +kernel

theorem c224_d46 : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 46 = false := by
  have e : body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) 46 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 46 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 46 && reach 8 14 45 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^46)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 46 && reach 8 14 45 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^46)))) := rfl
  rw [c262] at e
  exact e.trans (by decide +kernel)

theorem c224_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 14 || v == 16 || v == 31 || v == 40 || v == 44 || v == 46 || !body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) v) = true := by decide +kernel

theorem c224_a : ∀ v, v < 64 → body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c224_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c224_d1
  by_cases h3 : v = 3
  · subst h3; exact c224_d3
  by_cases h7 : v = 7
  · subst h7; exact c224_d7
  by_cases h8 : v = 8
  · subst h8; exact c224_d8
  by_cases h12 : v = 12
  · subst h12; exact c224_d12
  by_cases h14 : v = 14
  · subst h14; exact c224_d14
  by_cases h16 : v = 16
  · subst h16; exact c224_d16
  by_cases h31 : v = 31
  · subst h31; exact c224_d31
  by_cases h40 : v = 40
  · subst h40; exact c224_d40
  by_cases h44 : v = 44
  · subst h44; exact c224_d44
  by_cases h46 : v = 46
  · subst h46; exact c224_d46
  simpa [h1, h3, h7, h8, h12, h14, h16, h31, h40, h44, h46] using h

theorem c224 : reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^47) = false := by
  have e := reach_succ 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47) rfl
  have h : (List.range 64).any (body 8 14 45 3 1 0 ((S0 ||| 2^15) ||| 2^47)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c224_a v (List.mem_range.mp hv)]; decide
  rw [c18, c225, h] at e
  exact e.trans (by decide +kernel)

theorem c91_d47 : body 8 14 45 4 1 0 (S0 ||| 2^15) 47 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^15) 47 = (!((S0 ||| 2^15)).testBit 47 && ((aoHas (S0 ||| 2^15) 47 && reach 8 14 45 4 1 ((S0 ||| 2^15) ||| 2^47)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 47 && reach 8 14 45 4 0 ((S0 ||| 2^15) ||| 2^47)))) := rfl
  rw [c224] at e
  exact e.trans (by decide +kernel)

theorem c91_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 14 || v == 31 || v == 47 || !body 8 14 45 4 1 0 (S0 ||| 2^15) v) = true := by decide +kernel

theorem c91_a : ∀ v, v < 64 → body 8 14 45 4 1 0 (S0 ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c91_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c91_d1
  by_cases h3 : v = 3
  · subst h3; exact c91_d3
  by_cases h7 : v = 7
  · subst h7; exact c91_d7
  by_cases h8 : v = 8
  · subst h8; exact c91_d8
  by_cases h12 : v = 12
  · subst h12; exact c91_d12
  by_cases h14 : v = 14
  · subst h14; exact c91_d14
  by_cases h31 : v = 31
  · subst h31; exact c91_d31
  by_cases h47 : v = 47
  · subst h47; exact c91_d47
  simpa [h1, h3, h7, h8, h12, h14, h31, h47] using h

theorem c91 : reach 8 14 45 5 1 (S0 ||| 2^15) = false := by
  have e := reach_succ 8 14 45 4 1 0 (S0 ||| 2^15) rfl
  have h : (List.range 64).any (body 8 14 45 4 1 0 (S0 ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c91_a v (List.mem_range.mp hv)]; decide
  rw [c8, c25, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d15 : body 8 14 45 5 2 1 S0 15 = false := by
  have e : body 8 14 45 5 2 1 S0 15 = (!(S0).testBit 15 && ((aoHas S0 15 && reach 8 14 45 5 2 (S0 ||| 2^15)) ||
      (decide (0 < 2) && notHas S0 15 && reach 8 14 45 5 1 (S0 ||| 2^15)))) := rfl
  rw [c91] at e
  exact e.trans (by decide +kernel)

theorem c264 : reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^1) = false := by decide +kernel

theorem c263_d1 : body 8 14 45 4 1 0 (S0 ||| 2^31) 1 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 1 = (!((S0 ||| 2^31)).testBit 1 && ((aoHas (S0 ||| 2^31) 1 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 1 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^1)))) := rfl
  rw [c264] at e
  exact e.trans (by decide +kernel)

theorem c265 : reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^3) = false := by decide +kernel

theorem c263_d3 : body 8 14 45 4 1 0 (S0 ||| 2^31) 3 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 3 = (!((S0 ||| 2^31)).testBit 3 && ((aoHas (S0 ||| 2^31) 3 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 3 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^3)))) := rfl
  rw [c265] at e
  exact e.trans (by decide +kernel)

theorem c266 : reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^7) = false := by decide +kernel

theorem c263_d7 : body 8 14 45 4 1 0 (S0 ||| 2^31) 7 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 7 = (!((S0 ||| 2^31)).testBit 7 && ((aoHas (S0 ||| 2^31) 7 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 7 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^7)))) := rfl
  rw [c266] at e
  exact e.trans (by decide +kernel)

theorem c268 : reach 8 14 45 3 0 ((S0 ||| 2^31) ||| 2^15) = false := by decide +kernel

theorem c269 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c267_d8 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 8 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 8 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 8 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 8 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^8)))) := rfl
  rw [c269] at e
  exact e.trans (by decide +kernel)

theorem c270 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c267_d12 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 12 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 12 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 12 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 12 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^12)))) := rfl
  rw [c270] at e
  exact e.trans (by decide +kernel)

theorem c271 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c267_d14 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 14 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 14 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 14 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 14 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^14)))) := rfl
  rw [c271] at e
  exact e.trans (by decide +kernel)

theorem c272 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^16) = false := by decide +kernel

theorem c267_d16 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 16 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 16 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 16 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 16 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^16)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 16 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^16)))) := rfl
  rw [c272] at e
  exact e.trans (by decide +kernel)

theorem c273 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^24) = false := by decide +kernel

theorem c267_d24 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 24 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 24 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 24 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 24 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^24)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 24 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^24)))) := rfl
  rw [c273] at e
  exact e.trans (by decide +kernel)

theorem c274 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^28) = false := by decide +kernel

theorem c267_d28 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 28 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 28 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 28 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 28 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^28)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 28 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^28)))) := rfl
  rw [c274] at e
  exact e.trans (by decide +kernel)

theorem c275 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^30) = false := by decide +kernel

theorem c267_d30 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 30 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 30 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 30 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 30 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^30)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 30 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^30)))) := rfl
  rw [c275] at e
  exact e.trans (by decide +kernel)

theorem c276 : reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c267_d47 : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 47 = false := by
  have e : body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) 47 = (!(((S0 ||| 2^31) ||| 2^15)).testBit 47 && ((aoHas ((S0 ||| 2^31) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^31) ||| 2^15) 47 && reach 8 14 45 3 0 (((S0 ||| 2^31) ||| 2^15) ||| 2^47)))) := rfl
  rw [c276] at e
  exact e.trans (by decide +kernel)

theorem c267_o : (List.range 64).all (fun v => v == 8 || v == 12 || v == 14 || v == 16 || v == 24 || v == 28 || v == 30 || v == 47 || !body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) v) = true := by decide +kernel

theorem c267_a : ∀ v, v < 64 → body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c267_o v (List.mem_range.mpr hv)
  by_cases h8 : v = 8
  · subst h8; exact c267_d8
  by_cases h12 : v = 12
  · subst h12; exact c267_d12
  by_cases h14 : v = 14
  · subst h14; exact c267_d14
  by_cases h16 : v = 16
  · subst h16; exact c267_d16
  by_cases h24 : v = 24
  · subst h24; exact c267_d24
  by_cases h28 : v = 28
  · subst h28; exact c267_d28
  by_cases h30 : v = 30
  · subst h30; exact c267_d30
  by_cases h47 : v = 47
  · subst h47; exact c267_d47
  simpa [h8, h12, h14, h16, h24, h28, h30, h47] using h

theorem c267 : reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^15) = false := by
  have e := reach_succ 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15) rfl
  have h : (List.range 64).any (body 8 14 45 3 0 0 ((S0 ||| 2^31) ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c267_a v (List.mem_range.mp hv)]; decide
  rw [c268, h] at e
  exact e.trans (by decide +kernel)

theorem c263_d15 : body 8 14 45 4 1 0 (S0 ||| 2^31) 15 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 15 = (!((S0 ||| 2^31)).testBit 15 && ((aoHas (S0 ||| 2^31) 15 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 15 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^15)))) := rfl
  rw [c267] at e
  exact e.trans (by decide +kernel)

theorem c277 : reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^16) = false := by decide +kernel

theorem c263_d16 : body 8 14 45 4 1 0 (S0 ||| 2^31) 16 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 16 = (!((S0 ||| 2^31)).testBit 16 && ((aoHas (S0 ||| 2^31) 16 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^16)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 16 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^16)))) := rfl
  rw [c277] at e
  exact e.trans (by decide +kernel)

theorem c278 : reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^24) = false := by decide +kernel

theorem c263_d24 : body 8 14 45 4 1 0 (S0 ||| 2^31) 24 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 24 = (!((S0 ||| 2^31)).testBit 24 && ((aoHas (S0 ||| 2^31) 24 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^24)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 24 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^24)))) := rfl
  rw [c278] at e
  exact e.trans (by decide +kernel)

theorem c279 : reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^28) = false := by decide +kernel

theorem c263_d28 : body 8 14 45 4 1 0 (S0 ||| 2^31) 28 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 28 = (!((S0 ||| 2^31)).testBit 28 && ((aoHas (S0 ||| 2^31) 28 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^28)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 28 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^28)))) := rfl
  rw [c279] at e
  exact e.trans (by decide +kernel)

theorem c280 : reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^30) = false := by decide +kernel

theorem c263_d30 : body 8 14 45 4 1 0 (S0 ||| 2^31) 30 = false := by
  have e : body 8 14 45 4 1 0 (S0 ||| 2^31) 30 = (!((S0 ||| 2^31)).testBit 30 && ((aoHas (S0 ||| 2^31) 30 && reach 8 14 45 4 1 ((S0 ||| 2^31) ||| 2^30)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 30 && reach 8 14 45 4 0 ((S0 ||| 2^31) ||| 2^30)))) := rfl
  rw [c280] at e
  exact e.trans (by decide +kernel)

theorem c263_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 16 || v == 24 || v == 28 || v == 30 || !body 8 14 45 4 1 0 (S0 ||| 2^31) v) = true := by decide +kernel

theorem c263_a : ∀ v, v < 64 → body 8 14 45 4 1 0 (S0 ||| 2^31) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c263_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c263_d1
  by_cases h3 : v = 3
  · subst h3; exact c263_d3
  by_cases h7 : v = 7
  · subst h7; exact c263_d7
  by_cases h15 : v = 15
  · subst h15; exact c263_d15
  by_cases h16 : v = 16
  · subst h16; exact c263_d16
  by_cases h24 : v = 24
  · subst h24; exact c263_d24
  by_cases h28 : v = 28
  · subst h28; exact c263_d28
  by_cases h30 : v = 30
  · subst h30; exact c263_d30
  simpa [h1, h3, h7, h15, h16, h24, h28, h30] using h

theorem c263 : reach 8 14 45 5 1 (S0 ||| 2^31) = false := by
  have e := reach_succ 8 14 45 4 1 0 (S0 ||| 2^31) rfl
  have h : (List.range 64).any (body 8 14 45 4 1 0 (S0 ||| 2^31)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c263_a v (List.mem_range.mp hv)]; decide
  rw [c19, c26, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d31 : body 8 14 45 5 2 1 S0 31 = false := by
  have e : body 8 14 45 5 2 1 S0 31 = (!(S0).testBit 31 && ((aoHas S0 31 && reach 8 14 45 5 2 (S0 ||| 2^31)) ||
      (decide (0 < 2) && notHas S0 31 && reach 8 14 45 5 1 (S0 ||| 2^31)))) := rfl
  rw [c263] at e
  exact e.trans (by decide +kernel)

theorem c1_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 31 || !body 8 14 45 5 2 1 S0 v) = true := by decide +kernel

theorem c1_a : ∀ v, v < 64 → body 8 14 45 5 2 1 S0 v = false := by
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

theorem c1 : reach 8 14 45 6 2 S0 = false := by
  have e := reach_succ 8 14 45 5 2 1 S0 rfl
  have h : (List.range 64).any (body 8 14 45 5 2 1 S0) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c1_a v (List.mem_range.mp hv)]; decide
  rw [c2, c20, h] at e
  exact e.trans (by decide +kernel)

theorem cert : reach 8 14 45 6 2 S0 = false := c1

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
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (45 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hf, hr, hn, hs, ht⟩
  have := sound 8 14 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    D.gates (fun t => (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])
    7 S0 6 2 (fun t => by simp) (by decide) (by decide) init hf hr hs hn p.val q.val r.val
    p.isLt q.isLt r.isLt (fun t => ht t)
  rw [cert] at this
  exact absurd this (by decide)

end PEqualNP.Outside.L_meta_50261

theorem PEqualNP.Outside.L_meta_50261 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (45 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_50261.main
