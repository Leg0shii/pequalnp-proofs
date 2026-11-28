import PEqualNP.Defs

-- Exhaustion certificate: a kernel-run search over sets of 6-bit wire masks (a set is a Nat
-- bitset), with a soundness proof that every circuit of the statement is covered by the search.

namespace PEqualNP.Outside.L_meta_50269

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

theorem c3 : reach 4 38 40 4 2 S0 = false := by decide +kernel

theorem c4 : reach 4 38 40 4 1 S0 = false := by decide +kernel

theorem c5 : reach 4 38 40 4 1 (S0 ||| 2^1) = false := by decide +kernel

theorem c2_d1 : body 4 38 40 4 2 1 S0 1 = false := by
  have e : body 4 38 40 4 2 1 S0 1 = (!(S0).testBit 1 && ((aoHas S0 1 && reach 4 38 40 4 2 (S0 ||| 2^1)) ||
      (decide (0 < 2) && notHas S0 1 && reach 4 38 40 4 1 (S0 ||| 2^1)))) := rfl
  rw [c5] at e
  exact e.trans (by decide +kernel)

theorem c6 : reach 4 38 40 4 1 (S0 ||| 2^3) = false := by decide +kernel

theorem c2_d3 : body 4 38 40 4 2 1 S0 3 = false := by
  have e : body 4 38 40 4 2 1 S0 3 = (!(S0).testBit 3 && ((aoHas S0 3 && reach 4 38 40 4 2 (S0 ||| 2^3)) ||
      (decide (0 < 2) && notHas S0 3 && reach 4 38 40 4 1 (S0 ||| 2^3)))) := rfl
  rw [c6] at e
  exact e.trans (by decide +kernel)

theorem c8 : reach 4 38 40 3 1 (S0 ||| 2^7) = false := by decide +kernel

theorem c9 : reach 4 38 40 3 0 (S0 ||| 2^7) = false := by decide +kernel

theorem c10 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^1) = false := by decide +kernel

theorem c7_d1 : body 4 38 40 3 1 0 (S0 ||| 2^7) 1 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 1 = (!((S0 ||| 2^7)).testBit 1 && ((aoHas (S0 ||| 2^7) 1 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 1 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^1)))) := rfl
  rw [c10] at e
  exact e.trans (by decide +kernel)

theorem c11 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^3) = false := by decide +kernel

theorem c7_d3 : body 4 38 40 3 1 0 (S0 ||| 2^7) 3 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 3 = (!((S0 ||| 2^7)).testBit 3 && ((aoHas (S0 ||| 2^7) 3 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 3 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^3)))) := rfl
  rw [c11] at e
  exact e.trans (by decide +kernel)

theorem c12 : reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^4) = false := by decide +kernel

theorem c7_d4 : body 4 38 40 3 1 0 (S0 ||| 2^7) 4 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 4 = (!((S0 ||| 2^7)).testBit 4 && ((aoHas (S0 ||| 2^7) 4 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^4)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 4 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^4)))) := rfl
  rw [c12] at e
  exact e.trans (by decide +kernel)

theorem c13 : reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^6) = false := by decide +kernel

theorem c7_d6 : body 4 38 40 3 1 0 (S0 ||| 2^7) 6 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 6 = (!((S0 ||| 2^7)).testBit 6 && ((aoHas (S0 ||| 2^7) 6 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^6)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 6 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^6)))) := rfl
  rw [c13] at e
  exact e.trans (by decide +kernel)

theorem c14 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^15) = false := by decide +kernel

theorem c7_d15 : body 4 38 40 3 1 0 (S0 ||| 2^7) 15 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 15 = (!((S0 ||| 2^7)).testBit 15 && ((aoHas (S0 ||| 2^7) 15 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 15 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^15)))) := rfl
  rw [c14] at e
  exact e.trans (by decide +kernel)

theorem c15 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^31) = false := by decide +kernel

theorem c7_d31 : body 4 38 40 3 1 0 (S0 ||| 2^7) 31 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 31 = (!((S0 ||| 2^7)).testBit 31 && ((aoHas (S0 ||| 2^7) 31 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 31 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^31)))) := rfl
  rw [c15] at e
  exact e.trans (by decide +kernel)

theorem c16 : reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^39) = false := by decide +kernel

theorem c7_d39 : body 4 38 40 3 1 0 (S0 ||| 2^7) 39 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 39 = (!((S0 ||| 2^7)).testBit 39 && ((aoHas (S0 ||| 2^7) 39 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^39)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 39 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^39)))) := rfl
  rw [c16] at e
  exact e.trans (by decide +kernel)

theorem c17 : reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^55) = false := by decide +kernel

theorem c7_d55 : body 4 38 40 3 1 0 (S0 ||| 2^7) 55 = false := by
  have e : body 4 38 40 3 1 0 (S0 ||| 2^7) 55 = (!((S0 ||| 2^7)).testBit 55 && ((aoHas (S0 ||| 2^7) 55 && reach 4 38 40 3 1 ((S0 ||| 2^7) ||| 2^55)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 55 && reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^55)))) := rfl
  rw [c17] at e
  exact e.trans (by decide +kernel)

theorem c7_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 15 || v == 31 || v == 39 || v == 55 || !body 4 38 40 3 1 0 (S0 ||| 2^7) v) = true := by decide +kernel

theorem c7_a : ∀ v, v < 64 → body 4 38 40 3 1 0 (S0 ||| 2^7) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c7_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c7_d1
  by_cases h3 : v = 3
  · subst h3; exact c7_d3
  by_cases h4 : v = 4
  · subst h4; exact c7_d4
  by_cases h6 : v = 6
  · subst h6; exact c7_d6
  by_cases h15 : v = 15
  · subst h15; exact c7_d15
  by_cases h31 : v = 31
  · subst h31; exact c7_d31
  by_cases h39 : v = 39
  · subst h39; exact c7_d39
  by_cases h55 : v = 55
  · subst h55; exact c7_d55
  simpa [h1, h3, h4, h6, h15, h31, h39, h55] using h

theorem c7 : reach 4 38 40 4 1 (S0 ||| 2^7) = false := by
  have e := reach_succ 4 38 40 3 1 0 (S0 ||| 2^7) rfl
  have h : (List.range 64).any (body 4 38 40 3 1 0 (S0 ||| 2^7)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c7_a v (List.mem_range.mp hv)]; decide
  rw [c8, c9, h] at e
  exact e.trans (by decide +kernel)

theorem c2_d7 : body 4 38 40 4 2 1 S0 7 = false := by
  have e : body 4 38 40 4 2 1 S0 7 = (!(S0).testBit 7 && ((aoHas S0 7 && reach 4 38 40 4 2 (S0 ||| 2^7)) ||
      (decide (0 < 2) && notHas S0 7 && reach 4 38 40 4 1 (S0 ||| 2^7)))) := rfl
  rw [c7] at e
  exact e.trans (by decide +kernel)

theorem c18 : reach 4 38 40 4 1 (S0 ||| 2^15) = false := by decide +kernel

theorem c2_d15 : body 4 38 40 4 2 1 S0 15 = false := by
  have e : body 4 38 40 4 2 1 S0 15 = (!(S0).testBit 15 && ((aoHas S0 15 && reach 4 38 40 4 2 (S0 ||| 2^15)) ||
      (decide (0 < 2) && notHas S0 15 && reach 4 38 40 4 1 (S0 ||| 2^15)))) := rfl
  rw [c18] at e
  exact e.trans (by decide +kernel)

theorem c19 : reach 4 38 40 4 1 (S0 ||| 2^31) = false := by decide +kernel

theorem c2_d31 : body 4 38 40 4 2 1 S0 31 = false := by
  have e : body 4 38 40 4 2 1 S0 31 = (!(S0).testBit 31 && ((aoHas S0 31 && reach 4 38 40 4 2 (S0 ||| 2^31)) ||
      (decide (0 < 2) && notHas S0 31 && reach 4 38 40 4 1 (S0 ||| 2^31)))) := rfl
  rw [c19] at e
  exact e.trans (by decide +kernel)

theorem c2_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 31 || !body 4 38 40 4 2 1 S0 v) = true := by decide +kernel

theorem c2_a : ∀ v, v < 64 → body 4 38 40 4 2 1 S0 v = false := by
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

theorem c2 : reach 4 38 40 5 2 S0 = false := by
  have e := reach_succ 4 38 40 4 2 1 S0 rfl
  have h : (List.range 64).any (body 4 38 40 4 2 1 S0) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c2_a v (List.mem_range.mp hv)]; decide
  rw [c3, c4, h] at e
  exact e.trans (by decide +kernel)

theorem c20 : reach 4 38 40 5 1 S0 = false := by decide +kernel

theorem c22 : reach 4 38 40 4 0 (S0 ||| 2^1) = false := by decide +kernel

theorem c23 : reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^3) = false := by decide +kernel

theorem c21_d3 : body 4 38 40 4 1 0 (S0 ||| 2^1) 3 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 3 = (!((S0 ||| 2^1)).testBit 3 && ((aoHas (S0 ||| 2^1) 3 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 3 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^3)))) := rfl
  rw [c23] at e
  exact e.trans (by decide +kernel)

theorem c24 : reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^7) = false := by decide +kernel

theorem c21_d7 : body 4 38 40 4 1 0 (S0 ||| 2^1) 7 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 7 = (!((S0 ||| 2^1)).testBit 7 && ((aoHas (S0 ||| 2^1) 7 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 7 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^7)))) := rfl
  rw [c24] at e
  exact e.trans (by decide +kernel)

theorem c25 : reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^15) = false := by decide +kernel

theorem c21_d15 : body 4 38 40 4 1 0 (S0 ||| 2^1) 15 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 15 = (!((S0 ||| 2^1)).testBit 15 && ((aoHas (S0 ||| 2^1) 15 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 15 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^15)))) := rfl
  rw [c25] at e
  exact e.trans (by decide +kernel)

theorem c26 : reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^31) = false := by decide +kernel

theorem c21_d31 : body 4 38 40 4 1 0 (S0 ||| 2^1) 31 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 31 = (!((S0 ||| 2^1)).testBit 31 && ((aoHas (S0 ||| 2^1) 31 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 31 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^31)))) := rfl
  rw [c26] at e
  exact e.trans (by decide +kernel)

theorem c27 : reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^33) = false := by decide +kernel

theorem c21_d33 : body 4 38 40 4 1 0 (S0 ||| 2^1) 33 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 33 = (!((S0 ||| 2^1)).testBit 33 && ((aoHas (S0 ||| 2^1) 33 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^33)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 33 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^33)))) := rfl
  rw [c27] at e
  exact e.trans (by decide +kernel)

theorem c28 : reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^49) = false := by decide +kernel

theorem c21_d49 : body 4 38 40 4 1 0 (S0 ||| 2^1) 49 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 49 = (!((S0 ||| 2^1)).testBit 49 && ((aoHas (S0 ||| 2^1) 49 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^49)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 49 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^49)))) := rfl
  rw [c28] at e
  exact e.trans (by decide +kernel)

theorem c29 : reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^57) = false := by decide +kernel

theorem c21_d57 : body 4 38 40 4 1 0 (S0 ||| 2^1) 57 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 57 = (!((S0 ||| 2^1)).testBit 57 && ((aoHas (S0 ||| 2^1) 57 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^57)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 57 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^57)))) := rfl
  rw [c29] at e
  exact e.trans (by decide +kernel)

theorem c30 : reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^61) = false := by decide +kernel

theorem c21_d61 : body 4 38 40 4 1 0 (S0 ||| 2^1) 61 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^1) 61 = (!((S0 ||| 2^1)).testBit 61 && ((aoHas (S0 ||| 2^1) 61 && reach 4 38 40 4 1 ((S0 ||| 2^1) ||| 2^61)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^1) 61 && reach 4 38 40 4 0 ((S0 ||| 2^1) ||| 2^61)))) := rfl
  rw [c30] at e
  exact e.trans (by decide +kernel)

theorem c21_o : (List.range 64).all (fun v => v == 3 || v == 7 || v == 15 || v == 31 || v == 33 || v == 49 || v == 57 || v == 61 || !body 4 38 40 4 1 0 (S0 ||| 2^1) v) = true := by decide +kernel

theorem c21_a : ∀ v, v < 64 → body 4 38 40 4 1 0 (S0 ||| 2^1) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c21_o v (List.mem_range.mpr hv)
  by_cases h3 : v = 3
  · subst h3; exact c21_d3
  by_cases h7 : v = 7
  · subst h7; exact c21_d7
  by_cases h15 : v = 15
  · subst h15; exact c21_d15
  by_cases h31 : v = 31
  · subst h31; exact c21_d31
  by_cases h33 : v = 33
  · subst h33; exact c21_d33
  by_cases h49 : v = 49
  · subst h49; exact c21_d49
  by_cases h57 : v = 57
  · subst h57; exact c21_d57
  by_cases h61 : v = 61
  · subst h61; exact c21_d61
  simpa [h3, h7, h15, h31, h33, h49, h57, h61] using h

theorem c21 : reach 4 38 40 5 1 (S0 ||| 2^1) = false := by
  have e := reach_succ 4 38 40 4 1 0 (S0 ||| 2^1) rfl
  have h : (List.range 64).any (body 4 38 40 4 1 0 (S0 ||| 2^1)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c21_a v (List.mem_range.mp hv)]; decide
  rw [c5, c22, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d1 : body 4 38 40 5 2 1 S0 1 = false := by
  have e : body 4 38 40 5 2 1 S0 1 = (!(S0).testBit 1 && ((aoHas S0 1 && reach 4 38 40 5 2 (S0 ||| 2^1)) ||
      (decide (0 < 2) && notHas S0 1 && reach 4 38 40 5 1 (S0 ||| 2^1)))) := rfl
  rw [c21] at e
  exact e.trans (by decide +kernel)

theorem c32 : reach 4 38 40 4 0 (S0 ||| 2^3) = false := by decide +kernel

theorem c33 : reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^1) = false := by decide +kernel

theorem c31_d1 : body 4 38 40 4 1 0 (S0 ||| 2^3) 1 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 1 = (!((S0 ||| 2^3)).testBit 1 && ((aoHas (S0 ||| 2^3) 1 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 1 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^1)))) := rfl
  rw [c33] at e
  exact e.trans (by decide +kernel)

theorem c34 : reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^2) = false := by decide +kernel

theorem c31_d2 : body 4 38 40 4 1 0 (S0 ||| 2^3) 2 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 2 = (!((S0 ||| 2^3)).testBit 2 && ((aoHas (S0 ||| 2^3) 2 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^2)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 2 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^2)))) := rfl
  rw [c34] at e
  exact e.trans (by decide +kernel)

theorem c35 : reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^7) = false := by decide +kernel

theorem c31_d7 : body 4 38 40 4 1 0 (S0 ||| 2^3) 7 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 7 = (!((S0 ||| 2^3)).testBit 7 && ((aoHas (S0 ||| 2^3) 7 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 7 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^7)))) := rfl
  rw [c35] at e
  exact e.trans (by decide +kernel)

theorem c36 : reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^15) = false := by decide +kernel

theorem c31_d15 : body 4 38 40 4 1 0 (S0 ||| 2^3) 15 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 15 = (!((S0 ||| 2^3)).testBit 15 && ((aoHas (S0 ||| 2^3) 15 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 15 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^15)))) := rfl
  rw [c36] at e
  exact e.trans (by decide +kernel)

theorem c37 : reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^31) = false := by decide +kernel

theorem c31_d31 : body 4 38 40 4 1 0 (S0 ||| 2^3) 31 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 31 = (!((S0 ||| 2^3)).testBit 31 && ((aoHas (S0 ||| 2^3) 31 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 31 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^31)))) := rfl
  rw [c37] at e
  exact e.trans (by decide +kernel)

theorem c38 : reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^35) = false := by decide +kernel

theorem c31_d35 : body 4 38 40 4 1 0 (S0 ||| 2^3) 35 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 35 = (!((S0 ||| 2^3)).testBit 35 && ((aoHas (S0 ||| 2^3) 35 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^35)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 35 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^35)))) := rfl
  rw [c38] at e
  exact e.trans (by decide +kernel)

theorem c39 : reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^51) = false := by decide +kernel

theorem c31_d51 : body 4 38 40 4 1 0 (S0 ||| 2^3) 51 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 51 = (!((S0 ||| 2^3)).testBit 51 && ((aoHas (S0 ||| 2^3) 51 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^51)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 51 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^51)))) := rfl
  rw [c39] at e
  exact e.trans (by decide +kernel)

theorem c40 : reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^59) = false := by decide +kernel

theorem c31_d59 : body 4 38 40 4 1 0 (S0 ||| 2^3) 59 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^3) 59 = (!((S0 ||| 2^3)).testBit 59 && ((aoHas (S0 ||| 2^3) 59 && reach 4 38 40 4 1 ((S0 ||| 2^3) ||| 2^59)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^3) 59 && reach 4 38 40 4 0 ((S0 ||| 2^3) ||| 2^59)))) := rfl
  rw [c40] at e
  exact e.trans (by decide +kernel)

theorem c31_o : (List.range 64).all (fun v => v == 1 || v == 2 || v == 7 || v == 15 || v == 31 || v == 35 || v == 51 || v == 59 || !body 4 38 40 4 1 0 (S0 ||| 2^3) v) = true := by decide +kernel

theorem c31_a : ∀ v, v < 64 → body 4 38 40 4 1 0 (S0 ||| 2^3) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c31_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c31_d1
  by_cases h2 : v = 2
  · subst h2; exact c31_d2
  by_cases h7 : v = 7
  · subst h7; exact c31_d7
  by_cases h15 : v = 15
  · subst h15; exact c31_d15
  by_cases h31 : v = 31
  · subst h31; exact c31_d31
  by_cases h35 : v = 35
  · subst h35; exact c31_d35
  by_cases h51 : v = 51
  · subst h51; exact c31_d51
  by_cases h59 : v = 59
  · subst h59; exact c31_d59
  simpa [h1, h2, h7, h15, h31, h35, h51, h59] using h

theorem c31 : reach 4 38 40 5 1 (S0 ||| 2^3) = false := by
  have e := reach_succ 4 38 40 4 1 0 (S0 ||| 2^3) rfl
  have h : (List.range 64).any (body 4 38 40 4 1 0 (S0 ||| 2^3)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c31_a v (List.mem_range.mp hv)]; decide
  rw [c6, c32, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d3 : body 4 38 40 5 2 1 S0 3 = false := by
  have e : body 4 38 40 5 2 1 S0 3 = (!(S0).testBit 3 && ((aoHas S0 3 && reach 4 38 40 5 2 (S0 ||| 2^3)) ||
      (decide (0 < 2) && notHas S0 3 && reach 4 38 40 5 1 (S0 ||| 2^3)))) := rfl
  rw [c31] at e
  exact e.trans (by decide +kernel)

theorem c42 : reach 4 38 40 4 0 (S0 ||| 2^7) = false := by decide +kernel

theorem c43 : reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^1) = false := by decide +kernel

theorem c41_d1 : body 4 38 40 4 1 0 (S0 ||| 2^7) 1 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 1 = (!((S0 ||| 2^7)).testBit 1 && ((aoHas (S0 ||| 2^7) 1 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 1 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^1)))) := rfl
  rw [c43] at e
  exact e.trans (by decide +kernel)

theorem c44 : reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^3) = false := by decide +kernel

theorem c41_d3 : body 4 38 40 4 1 0 (S0 ||| 2^7) 3 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 3 = (!((S0 ||| 2^7)).testBit 3 && ((aoHas (S0 ||| 2^7) 3 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 3 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^3)))) := rfl
  rw [c44] at e
  exact e.trans (by decide +kernel)

theorem c46 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^4) = false := by decide +kernel

theorem c47 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^1) = false := by decide +kernel

theorem c45_d1 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 1 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 1 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 1 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 1 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 1 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^1)))) := rfl
  rw [c47] at e
  exact e.trans (by decide +kernel)

theorem c48 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^3) = false := by decide +kernel

theorem c45_d3 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 3 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 3 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 3 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 3 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 3 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^3)))) := rfl
  rw [c48] at e
  exact e.trans (by decide +kernel)

theorem c50 : reach 4 38 40 2 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) = false := by decide +kernel

theorem c51 : reach 4 38 40 2 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) = false := by decide +kernel

theorem c52 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^1) = false := by decide +kernel

theorem c49_d1 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 1 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 1 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 1 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 1 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 1 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^1)))) := rfl
  rw [c52] at e
  exact e.trans (by decide +kernel)

theorem c53 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^3) = false := by decide +kernel

theorem c49_d3 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 3 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 3 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 3 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 3 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 3 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^3)))) := rfl
  rw [c53] at e
  exact e.trans (by decide +kernel)

theorem c54 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^15) = false := by decide +kernel

theorem c49_d15 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 15 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 15 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 15 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 15 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 15 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^15)))) := rfl
  rw [c54] at e
  exact e.trans (by decide +kernel)

theorem c55 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^31) = false := by decide +kernel

theorem c49_d31 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 31 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 31 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 31 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 31 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 31 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^31)))) := rfl
  rw [c55] at e
  exact e.trans (by decide +kernel)

theorem c56 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^36) = false := by decide +kernel

theorem c49_d36 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 36 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 36 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 36 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 36 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^36)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 36 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^36)))) := rfl
  rw [c56] at e
  exact e.trans (by decide +kernel)

theorem c57 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^38) = false := by decide +kernel

theorem c49_d38 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 38 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 38 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 38 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 38 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^38)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 38 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^38)))) := rfl
  rw [c57] at e
  exact e.trans (by decide +kernel)

theorem c58 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^39) = false := by decide +kernel

theorem c49_d39 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 39 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 39 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 39 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 39 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^39)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 39 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^39)))) := rfl
  rw [c58] at e
  exact e.trans (by decide +kernel)

theorem c59 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^52) = false := by decide +kernel

theorem c49_d52 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 52 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 52 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 52 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 52 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^52)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 52 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^52)))) := rfl
  rw [c59] at e
  exact e.trans (by decide +kernel)

theorem c60 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^54) = false := by decide +kernel

theorem c49_d54 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 54 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 54 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 54 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 54 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^54)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 54 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^54)))) := rfl
  rw [c60] at e
  exact e.trans (by decide +kernel)

theorem c61 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^55) = false := by decide +kernel

theorem c49_d55 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 55 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 55 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 55 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 55 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 55 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^55)))) := rfl
  rw [c61] at e
  exact e.trans (by decide +kernel)

theorem c62 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^57) = false := by decide +kernel

theorem c49_d57 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 57 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 57 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 57 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 57 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^57)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 57 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^57)))) := rfl
  rw [c62] at e
  exact e.trans (by decide +kernel)

theorem c63 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^59) = false := by decide +kernel

theorem c49_d59 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 59 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 59 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^6)).testBit 59 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 59 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^59)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^6) 59 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^6) ||| 2^59)))) := rfl
  rw [c63] at e
  exact e.trans (by decide +kernel)

theorem c49_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 15 || v == 31 || v == 36 || v == 38 || v == 39 || v == 52 || v == 54 || v == 55 || v == 57 || v == 59 || !body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) v) = true := by decide +kernel

theorem c49_a : ∀ v, v < 64 → body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c49_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c49_d1
  by_cases h3 : v = 3
  · subst h3; exact c49_d3
  by_cases h15 : v = 15
  · subst h15; exact c49_d15
  by_cases h31 : v = 31
  · subst h31; exact c49_d31
  by_cases h36 : v = 36
  · subst h36; exact c49_d36
  by_cases h38 : v = 38
  · subst h38; exact c49_d38
  by_cases h39 : v = 39
  · subst h39; exact c49_d39
  by_cases h52 : v = 52
  · subst h52; exact c49_d52
  by_cases h54 : v = 54
  · subst h54; exact c49_d54
  by_cases h55 : v = 55
  · subst h55; exact c49_d55
  by_cases h57 : v = 57
  · subst h57; exact c49_d57
  by_cases h59 : v = 59
  · subst h59; exact c49_d59
  simpa [h1, h3, h15, h31, h36, h38, h39, h52, h54, h55, h57, h59] using h

theorem c49 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) = false := by
  have e := reach_succ 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6) rfl
  have h : (List.range 64).any (body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c49_a v (List.mem_range.mp hv)]; decide
  rw [c50, c51, h] at e
  exact e.trans (by decide +kernel)

theorem c45_d6 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 6 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 6 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 6 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 6 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^6)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 6 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^6)))) := rfl
  rw [c49] at e
  exact e.trans (by decide +kernel)

theorem c64 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^15) = false := by decide +kernel

theorem c45_d15 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 15 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 15 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 15 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 15 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 15 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^15)))) := rfl
  rw [c64] at e
  exact e.trans (by decide +kernel)

theorem c65 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^31) = false := by decide +kernel

theorem c45_d31 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 31 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 31 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 31 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 31 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 31 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^31)))) := rfl
  rw [c65] at e
  exact e.trans (by decide +kernel)

theorem c66 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^36) = false := by decide +kernel

theorem c45_d36 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 36 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 36 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 36 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 36 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^36)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 36 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^36)))) := rfl
  rw [c66] at e
  exact e.trans (by decide +kernel)

theorem c68 : reach 4 38 40 2 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) = false := by decide +kernel

theorem c69 : reach 4 38 40 2 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) = false := by decide +kernel

theorem c70 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^1) = false := by decide +kernel

theorem c67_d1 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 1 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 1 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 1 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 1 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 1 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^1)))) := rfl
  rw [c70] at e
  exact e.trans (by decide +kernel)

theorem c71 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^3) = false := by decide +kernel

theorem c67_d3 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 3 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 3 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 3 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 3 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 3 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^3)))) := rfl
  rw [c71] at e
  exact e.trans (by decide +kernel)

theorem c72 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^6) = false := by decide +kernel

theorem c67_d6 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 6 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 6 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 6 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 6 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^6)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 6 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^6)))) := rfl
  rw [c72] at e
  exact e.trans (by decide +kernel)

theorem c73 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^15) = false := by decide +kernel

theorem c67_d15 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 15 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 15 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 15 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 15 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 15 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^15)))) := rfl
  rw [c73] at e
  exact e.trans (by decide +kernel)

theorem c74 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^24) = false := by decide +kernel

theorem c67_d24 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 24 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 24 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 24 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 24 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^24)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 24 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^24)))) := rfl
  rw [c74] at e
  exact e.trans (by decide +kernel)

theorem c75 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^31) = false := by decide +kernel

theorem c67_d31 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 31 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 31 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 31 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 31 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 31 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^31)))) := rfl
  rw [c75] at e
  exact e.trans (by decide +kernel)

theorem c76 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^36) = false := by decide +kernel

theorem c67_d36 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 36 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 36 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 36 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 36 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^36)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 36 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^36)))) := rfl
  rw [c76] at e
  exact e.trans (by decide +kernel)

theorem c77 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^38) = false := by decide +kernel

theorem c67_d38 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 38 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 38 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 38 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 38 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^38)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 38 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^38)))) := rfl
  rw [c77] at e
  exact e.trans (by decide +kernel)

theorem c78 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^52) = false := by decide +kernel

theorem c67_d52 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 52 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 52 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 52 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 52 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^52)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 52 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^52)))) := rfl
  rw [c78] at e
  exact e.trans (by decide +kernel)

theorem c79 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^55) = false := by decide +kernel

theorem c67_d55 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 55 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 55 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 55 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 55 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 55 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^55)))) := rfl
  rw [c79] at e
  exact e.trans (by decide +kernel)

theorem c80 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^59) = false := by decide +kernel

theorem c67_d59 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 59 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 59 = (!((((S0 ||| 2^7) ||| 2^4) ||| 2^39)).testBit 59 && ((aoHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 59 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^59)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^4) ||| 2^39) 59 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^4) ||| 2^39) ||| 2^59)))) := rfl
  rw [c80] at e
  exact e.trans (by decide +kernel)

theorem c67_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 6 || v == 15 || v == 24 || v == 31 || v == 36 || v == 38 || v == 52 || v == 55 || v == 59 || !body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) v) = true := by decide +kernel

theorem c67_a : ∀ v, v < 64 → body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c67_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c67_d1
  by_cases h3 : v = 3
  · subst h3; exact c67_d3
  by_cases h6 : v = 6
  · subst h6; exact c67_d6
  by_cases h15 : v = 15
  · subst h15; exact c67_d15
  by_cases h24 : v = 24
  · subst h24; exact c67_d24
  by_cases h31 : v = 31
  · subst h31; exact c67_d31
  by_cases h36 : v = 36
  · subst h36; exact c67_d36
  by_cases h38 : v = 38
  · subst h38; exact c67_d38
  by_cases h52 : v = 52
  · subst h52; exact c67_d52
  by_cases h55 : v = 55
  · subst h55; exact c67_d55
  by_cases h59 : v = 59
  · subst h59; exact c67_d59
  simpa [h1, h3, h6, h15, h24, h31, h36, h38, h52, h55, h59] using h

theorem c67 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) = false := by
  have e := reach_succ 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39) rfl
  have h : (List.range 64).any (body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c67_a v (List.mem_range.mp hv)]; decide
  rw [c68, c69, h] at e
  exact e.trans (by decide +kernel)

theorem c45_d39 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 39 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 39 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 39 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 39 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^39)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 39 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^39)))) := rfl
  rw [c67] at e
  exact e.trans (by decide +kernel)

theorem c81 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^52) = false := by decide +kernel

theorem c45_d52 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 52 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 52 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 52 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 52 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^52)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 52 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^52)))) := rfl
  rw [c81] at e
  exact e.trans (by decide +kernel)

theorem c82 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^55) = false := by decide +kernel

theorem c45_d55 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 55 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 55 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 55 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 55 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^55)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 55 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^55)))) := rfl
  rw [c82] at e
  exact e.trans (by decide +kernel)

theorem c83 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^59) = false := by decide +kernel

theorem c45_d59 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 59 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) 59 = (!(((S0 ||| 2^7) ||| 2^4)).testBit 59 && ((aoHas ((S0 ||| 2^7) ||| 2^4) 59 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^4) ||| 2^59)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^4) 59 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^4) ||| 2^59)))) := rfl
  rw [c83] at e
  exact e.trans (by decide +kernel)

theorem c45_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 6 || v == 15 || v == 31 || v == 36 || v == 39 || v == 52 || v == 55 || v == 59 || !body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) v) = true := by decide +kernel

theorem c45_a : ∀ v, v < 64 → body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c45_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c45_d1
  by_cases h3 : v = 3
  · subst h3; exact c45_d3
  by_cases h6 : v = 6
  · subst h6; exact c45_d6
  by_cases h15 : v = 15
  · subst h15; exact c45_d15
  by_cases h31 : v = 31
  · subst h31; exact c45_d31
  by_cases h36 : v = 36
  · subst h36; exact c45_d36
  by_cases h39 : v = 39
  · subst h39; exact c45_d39
  by_cases h52 : v = 52
  · subst h52; exact c45_d52
  by_cases h55 : v = 55
  · subst h55; exact c45_d55
  by_cases h59 : v = 59
  · subst h59; exact c45_d59
  simpa [h1, h3, h6, h15, h31, h36, h39, h52, h55, h59] using h

theorem c45 : reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^4) = false := by
  have e := reach_succ 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4) rfl
  have h : (List.range 64).any (body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^4)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c45_a v (List.mem_range.mp hv)]; decide
  rw [c12, c46, h] at e
  exact e.trans (by decide +kernel)

theorem c41_d4 : body 4 38 40 4 1 0 (S0 ||| 2^7) 4 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 4 = (!((S0 ||| 2^7)).testBit 4 && ((aoHas (S0 ||| 2^7) 4 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^4)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 4 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^4)))) := rfl
  rw [c45] at e
  exact e.trans (by decide +kernel)

theorem c85 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^6) = false := by decide +kernel

theorem c86 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^1) = false := by decide +kernel

theorem c84_d1 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 1 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 1 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 1 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 1 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 1 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^1)))) := rfl
  rw [c86] at e
  exact e.trans (by decide +kernel)

theorem c87 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^3) = false := by decide +kernel

theorem c84_d3 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 3 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 3 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 3 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 3 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 3 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^3)))) := rfl
  rw [c87] at e
  exact e.trans (by decide +kernel)

theorem c89 : reach 4 38 40 2 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) = false := by decide +kernel

theorem c90 : reach 4 38 40 2 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) = false := by decide +kernel

theorem c91 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^1) = false := by decide +kernel

theorem c88_d1 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 1 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 1 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 1 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 1 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 1 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^1)))) := rfl
  rw [c91] at e
  exact e.trans (by decide +kernel)

theorem c92 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^3) = false := by decide +kernel

theorem c88_d3 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 3 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 3 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 3 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 3 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 3 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^3)))) := rfl
  rw [c92] at e
  exact e.trans (by decide +kernel)

theorem c93 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^15) = false := by decide +kernel

theorem c88_d15 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 15 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 15 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 15 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 15 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 15 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^15)))) := rfl
  rw [c93] at e
  exact e.trans (by decide +kernel)

theorem c94 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^31) = false := by decide +kernel

theorem c88_d31 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 31 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 31 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 31 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 31 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 31 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^31)))) := rfl
  rw [c94] at e
  exact e.trans (by decide +kernel)

theorem c95 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^36) = false := by decide +kernel

theorem c88_d36 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 36 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 36 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 36 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 36 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^36)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 36 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^36)))) := rfl
  rw [c95] at e
  exact e.trans (by decide +kernel)

theorem c96 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^38) = false := by decide +kernel

theorem c88_d38 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 38 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 38 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 38 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 38 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^38)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 38 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^38)))) := rfl
  rw [c96] at e
  exact e.trans (by decide +kernel)

theorem c97 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^39) = false := by decide +kernel

theorem c88_d39 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 39 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 39 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 39 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 39 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^39)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 39 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^39)))) := rfl
  rw [c97] at e
  exact e.trans (by decide +kernel)

theorem c98 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^52) = false := by decide +kernel

theorem c88_d52 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 52 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 52 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 52 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 52 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^52)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 52 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^52)))) := rfl
  rw [c98] at e
  exact e.trans (by decide +kernel)

theorem c99 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^54) = false := by decide +kernel

theorem c88_d54 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 54 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 54 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 54 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 54 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^54)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 54 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^54)))) := rfl
  rw [c99] at e
  exact e.trans (by decide +kernel)

theorem c100 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^55) = false := by decide +kernel

theorem c88_d55 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 55 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 55 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 55 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 55 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 55 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^55)))) := rfl
  rw [c100] at e
  exact e.trans (by decide +kernel)

theorem c101 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^57) = false := by decide +kernel

theorem c88_d57 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 57 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 57 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 57 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 57 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^57)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 57 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^57)))) := rfl
  rw [c101] at e
  exact e.trans (by decide +kernel)

theorem c102 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^59) = false := by decide +kernel

theorem c88_d59 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 59 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 59 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^4)).testBit 59 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 59 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^59)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^4) 59 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^4) ||| 2^59)))) := rfl
  rw [c102] at e
  exact e.trans (by decide +kernel)

theorem c88_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 15 || v == 31 || v == 36 || v == 38 || v == 39 || v == 52 || v == 54 || v == 55 || v == 57 || v == 59 || !body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) v) = true := by decide +kernel

theorem c88_a : ∀ v, v < 64 → body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c88_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c88_d1
  by_cases h3 : v = 3
  · subst h3; exact c88_d3
  by_cases h15 : v = 15
  · subst h15; exact c88_d15
  by_cases h31 : v = 31
  · subst h31; exact c88_d31
  by_cases h36 : v = 36
  · subst h36; exact c88_d36
  by_cases h38 : v = 38
  · subst h38; exact c88_d38
  by_cases h39 : v = 39
  · subst h39; exact c88_d39
  by_cases h52 : v = 52
  · subst h52; exact c88_d52
  by_cases h54 : v = 54
  · subst h54; exact c88_d54
  by_cases h55 : v = 55
  · subst h55; exact c88_d55
  by_cases h57 : v = 57
  · subst h57; exact c88_d57
  by_cases h59 : v = 59
  · subst h59; exact c88_d59
  simpa [h1, h3, h15, h31, h36, h38, h39, h52, h54, h55, h57, h59] using h

theorem c88 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) = false := by
  have e := reach_succ 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4) rfl
  have h : (List.range 64).any (body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c88_a v (List.mem_range.mp hv)]; decide
  rw [c89, c90, h] at e
  exact e.trans (by decide +kernel)

theorem c84_d4 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 4 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 4 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 4 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 4 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^4)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 4 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^4)))) := rfl
  rw [c88] at e
  exact e.trans (by decide +kernel)

theorem c103 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^15) = false := by decide +kernel

theorem c84_d15 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 15 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 15 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 15 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 15 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 15 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^15)))) := rfl
  rw [c103] at e
  exact e.trans (by decide +kernel)

theorem c104 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^31) = false := by decide +kernel

theorem c84_d31 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 31 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 31 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 31 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 31 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 31 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^31)))) := rfl
  rw [c104] at e
  exact e.trans (by decide +kernel)

theorem c106 : reach 4 38 40 2 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) = false := by decide +kernel

theorem c107 : reach 4 38 40 2 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) = false := by decide +kernel

theorem c108 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^1) = false := by decide +kernel

theorem c105_d1 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 1 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 1 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 1 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 1 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 1 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^1)))) := rfl
  rw [c108] at e
  exact e.trans (by decide +kernel)

theorem c109 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^3) = false := by decide +kernel

theorem c105_d3 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 3 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 3 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 3 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 3 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 3 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^3)))) := rfl
  rw [c109] at e
  exact e.trans (by decide +kernel)

theorem c110 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^4) = false := by decide +kernel

theorem c105_d4 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 4 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 4 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 4 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 4 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^4)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 4 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^4)))) := rfl
  rw [c110] at e
  exact e.trans (by decide +kernel)

theorem c111 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^15) = false := by decide +kernel

theorem c105_d15 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 15 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 15 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 15 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 15 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 15 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^15)))) := rfl
  rw [c111] at e
  exact e.trans (by decide +kernel)

theorem c112 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^25) = false := by decide +kernel

theorem c105_d25 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 25 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 25 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 25 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 25 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^25)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 25 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^25)))) := rfl
  rw [c112] at e
  exact e.trans (by decide +kernel)

theorem c113 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^31) = false := by decide +kernel

theorem c105_d31 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 31 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 31 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 31 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 31 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 31 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^31)))) := rfl
  rw [c113] at e
  exact e.trans (by decide +kernel)

theorem c114 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^36) = false := by decide +kernel

theorem c105_d36 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 36 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 36 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 36 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 36 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^36)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 36 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^36)))) := rfl
  rw [c114] at e
  exact e.trans (by decide +kernel)

theorem c115 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^39) = false := by decide +kernel

theorem c105_d39 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 39 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 39 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 39 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 39 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^39)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 39 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^39)))) := rfl
  rw [c115] at e
  exact e.trans (by decide +kernel)

theorem c116 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^54) = false := by decide +kernel

theorem c105_d54 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 54 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 54 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 54 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 54 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^54)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 54 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^54)))) := rfl
  rw [c116] at e
  exact e.trans (by decide +kernel)

theorem c117 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^55) = false := by decide +kernel

theorem c105_d55 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 55 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 55 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 55 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 55 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 55 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^55)))) := rfl
  rw [c117] at e
  exact e.trans (by decide +kernel)

theorem c118 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^57) = false := by decide +kernel

theorem c105_d57 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 57 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 57 = (!((((S0 ||| 2^7) ||| 2^6) ||| 2^38)).testBit 57 && ((aoHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 57 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^57)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^6) ||| 2^38) 57 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^6) ||| 2^38) ||| 2^57)))) := rfl
  rw [c118] at e
  exact e.trans (by decide +kernel)

theorem c105_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 15 || v == 25 || v == 31 || v == 36 || v == 39 || v == 54 || v == 55 || v == 57 || !body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) v) = true := by decide +kernel

theorem c105_a : ∀ v, v < 64 → body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c105_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c105_d1
  by_cases h3 : v = 3
  · subst h3; exact c105_d3
  by_cases h4 : v = 4
  · subst h4; exact c105_d4
  by_cases h15 : v = 15
  · subst h15; exact c105_d15
  by_cases h25 : v = 25
  · subst h25; exact c105_d25
  by_cases h31 : v = 31
  · subst h31; exact c105_d31
  by_cases h36 : v = 36
  · subst h36; exact c105_d36
  by_cases h39 : v = 39
  · subst h39; exact c105_d39
  by_cases h54 : v = 54
  · subst h54; exact c105_d54
  by_cases h55 : v = 55
  · subst h55; exact c105_d55
  by_cases h57 : v = 57
  · subst h57; exact c105_d57
  simpa [h1, h3, h4, h15, h25, h31, h36, h39, h54, h55, h57] using h

theorem c105 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) = false := by
  have e := reach_succ 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38) rfl
  have h : (List.range 64).any (body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c105_a v (List.mem_range.mp hv)]; decide
  rw [c106, c107, h] at e
  exact e.trans (by decide +kernel)

theorem c84_d38 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 38 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 38 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 38 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 38 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^38)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 38 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^38)))) := rfl
  rw [c105] at e
  exact e.trans (by decide +kernel)

theorem c119 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^39) = false := by decide +kernel

theorem c84_d39 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 39 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 39 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 39 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 39 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^39)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 39 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^39)))) := rfl
  rw [c119] at e
  exact e.trans (by decide +kernel)

theorem c120 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^54) = false := by decide +kernel

theorem c84_d54 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 54 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 54 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 54 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 54 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^54)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 54 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^54)))) := rfl
  rw [c120] at e
  exact e.trans (by decide +kernel)

theorem c121 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^55) = false := by decide +kernel

theorem c84_d55 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 55 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 55 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 55 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 55 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^55)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 55 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^55)))) := rfl
  rw [c121] at e
  exact e.trans (by decide +kernel)

theorem c122 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^57) = false := by decide +kernel

theorem c84_d57 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 57 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) 57 = (!(((S0 ||| 2^7) ||| 2^6)).testBit 57 && ((aoHas ((S0 ||| 2^7) ||| 2^6) 57 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^6) ||| 2^57)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^6) 57 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^6) ||| 2^57)))) := rfl
  rw [c122] at e
  exact e.trans (by decide +kernel)

theorem c84_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 15 || v == 31 || v == 38 || v == 39 || v == 54 || v == 55 || v == 57 || !body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) v) = true := by decide +kernel

theorem c84_a : ∀ v, v < 64 → body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c84_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c84_d1
  by_cases h3 : v = 3
  · subst h3; exact c84_d3
  by_cases h4 : v = 4
  · subst h4; exact c84_d4
  by_cases h15 : v = 15
  · subst h15; exact c84_d15
  by_cases h31 : v = 31
  · subst h31; exact c84_d31
  by_cases h38 : v = 38
  · subst h38; exact c84_d38
  by_cases h39 : v = 39
  · subst h39; exact c84_d39
  by_cases h54 : v = 54
  · subst h54; exact c84_d54
  by_cases h55 : v = 55
  · subst h55; exact c84_d55
  by_cases h57 : v = 57
  · subst h57; exact c84_d57
  simpa [h1, h3, h4, h15, h31, h38, h39, h54, h55, h57] using h

theorem c84 : reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^6) = false := by
  have e := reach_succ 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6) rfl
  have h : (List.range 64).any (body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^6)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c84_a v (List.mem_range.mp hv)]; decide
  rw [c13, c85, h] at e
  exact e.trans (by decide +kernel)

theorem c41_d6 : body 4 38 40 4 1 0 (S0 ||| 2^7) 6 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 6 = (!((S0 ||| 2^7)).testBit 6 && ((aoHas (S0 ||| 2^7) 6 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^6)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 6 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^6)))) := rfl
  rw [c84] at e
  exact e.trans (by decide +kernel)

theorem c124 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^4) = false := by decide +kernel

theorem c123_d4 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 4 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 4 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 4 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 4 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^4)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 4 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^4)))) := rfl
  rw [c124] at e
  exact e.trans (by decide +kernel)

theorem c125 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^6) = false := by decide +kernel

theorem c123_d6 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 6 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 6 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 6 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 6 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^6)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 6 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^6)))) := rfl
  rw [c125] at e
  exact e.trans (by decide +kernel)

theorem c126 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c123_d8 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 8 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 8 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 8 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 8 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 8 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^8)))) := rfl
  rw [c126] at e
  exact e.trans (by decide +kernel)

theorem c127 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c123_d12 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 12 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 12 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 12 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 12 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 12 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^12)))) := rfl
  rw [c127] at e
  exact e.trans (by decide +kernel)

theorem c128 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c123_d14 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 14 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 14 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 14 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 14 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 14 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^14)))) := rfl
  rw [c128] at e
  exact e.trans (by decide +kernel)

theorem c129 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^39) = false := by decide +kernel

theorem c123_d39 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 39 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 39 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 39 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 39 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^39)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 39 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^39)))) := rfl
  rw [c129] at e
  exact e.trans (by decide +kernel)

theorem c130 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c123_d47 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 47 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 47 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 47 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 47 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 47 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^47)))) := rfl
  rw [c130] at e
  exact e.trans (by decide +kernel)

theorem c131 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^55) = false := by decide +kernel

theorem c123_d55 : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 55 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) 55 = (!(((S0 ||| 2^7) ||| 2^15)).testBit 55 && ((aoHas ((S0 ||| 2^7) ||| 2^15) 55 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^55)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^7) ||| 2^15) 55 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^15) ||| 2^55)))) := rfl
  rw [c131] at e
  exact e.trans (by decide +kernel)

theorem c123_o : (List.range 64).all (fun v => v == 4 || v == 6 || v == 8 || v == 12 || v == 14 || v == 39 || v == 47 || v == 55 || !body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) v) = true := by decide +kernel

theorem c123_a : ∀ v, v < 64 → body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c123_o v (List.mem_range.mpr hv)
  by_cases h4 : v = 4
  · subst h4; exact c123_d4
  by_cases h6 : v = 6
  · subst h6; exact c123_d6
  by_cases h8 : v = 8
  · subst h8; exact c123_d8
  by_cases h12 : v = 12
  · subst h12; exact c123_d12
  by_cases h14 : v = 14
  · subst h14; exact c123_d14
  by_cases h39 : v = 39
  · subst h39; exact c123_d39
  by_cases h47 : v = 47
  · subst h47; exact c123_d47
  by_cases h55 : v = 55
  · subst h55; exact c123_d55
  simpa [h4, h6, h8, h12, h14, h39, h47, h55] using h

theorem c123 : reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^15) = false := by
  have e := reach_succ 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15) rfl
  have h : (List.range 64).any (body 4 38 40 3 0 0 ((S0 ||| 2^7) ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c123_a v (List.mem_range.mp hv)]; decide
  rw [c14, h] at e
  exact e.trans (by decide +kernel)

theorem c41_d15 : body 4 38 40 4 1 0 (S0 ||| 2^7) 15 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 15 = (!((S0 ||| 2^7)).testBit 15 && ((aoHas (S0 ||| 2^7) 15 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 15 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^15)))) := rfl
  rw [c123] at e
  exact e.trans (by decide +kernel)

theorem c132 : reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^31) = false := by decide +kernel

theorem c41_d31 : body 4 38 40 4 1 0 (S0 ||| 2^7) 31 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 31 = (!((S0 ||| 2^7)).testBit 31 && ((aoHas (S0 ||| 2^7) 31 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 31 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^31)))) := rfl
  rw [c132] at e
  exact e.trans (by decide +kernel)

theorem c134 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^39) = false := by decide +kernel

theorem c135 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^1) = false := by decide +kernel

theorem c133_d1 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 1 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 1 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 1 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 1 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 1 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^1)))) := rfl
  rw [c135] at e
  exact e.trans (by decide +kernel)

theorem c136 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^3) = false := by decide +kernel

theorem c133_d3 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 3 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 3 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 3 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 3 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 3 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^3)))) := rfl
  rw [c136] at e
  exact e.trans (by decide +kernel)

theorem c138 : reach 4 38 40 2 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) = false := by decide +kernel

theorem c139 : reach 4 38 40 2 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) = false := by decide +kernel

theorem c140 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^1) = false := by decide +kernel

theorem c137_d1 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 1 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 1 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 1 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 1 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 1 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^1)))) := rfl
  rw [c140] at e
  exact e.trans (by decide +kernel)

theorem c141 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^3) = false := by decide +kernel

theorem c137_d3 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 3 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 3 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 3 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 3 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 3 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^3)))) := rfl
  rw [c141] at e
  exact e.trans (by decide +kernel)

theorem c142 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^6) = false := by decide +kernel

theorem c137_d6 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 6 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 6 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 6 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 6 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^6)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 6 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^6)))) := rfl
  rw [c142] at e
  exact e.trans (by decide +kernel)

theorem c143 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^15) = false := by decide +kernel

theorem c137_d15 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 15 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 15 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 15 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 15 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 15 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^15)))) := rfl
  rw [c143] at e
  exact e.trans (by decide +kernel)

theorem c144 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^24) = false := by decide +kernel

theorem c137_d24 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 24 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 24 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 24 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 24 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^24)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 24 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^24)))) := rfl
  rw [c144] at e
  exact e.trans (by decide +kernel)

theorem c145 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^31) = false := by decide +kernel

theorem c137_d31 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 31 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 31 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 31 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 31 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 31 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^31)))) := rfl
  rw [c145] at e
  exact e.trans (by decide +kernel)

theorem c146 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^36) = false := by decide +kernel

theorem c137_d36 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 36 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 36 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 36 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 36 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^36)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 36 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^36)))) := rfl
  rw [c146] at e
  exact e.trans (by decide +kernel)

theorem c147 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^38) = false := by decide +kernel

theorem c137_d38 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 38 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 38 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 38 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 38 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^38)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 38 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^38)))) := rfl
  rw [c147] at e
  exact e.trans (by decide +kernel)

theorem c148 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^52) = false := by decide +kernel

theorem c137_d52 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 52 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 52 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 52 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 52 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^52)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 52 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^52)))) := rfl
  rw [c148] at e
  exact e.trans (by decide +kernel)

theorem c149 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^55) = false := by decide +kernel

theorem c137_d55 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 55 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 55 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 55 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 55 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 55 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^55)))) := rfl
  rw [c149] at e
  exact e.trans (by decide +kernel)

theorem c150 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^59) = false := by decide +kernel

theorem c137_d59 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 59 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 59 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^4)).testBit 59 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 59 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^59)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^4) 59 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^4) ||| 2^59)))) := rfl
  rw [c150] at e
  exact e.trans (by decide +kernel)

theorem c137_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 6 || v == 15 || v == 24 || v == 31 || v == 36 || v == 38 || v == 52 || v == 55 || v == 59 || !body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) v) = true := by decide +kernel

theorem c137_a : ∀ v, v < 64 → body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c137_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c137_d1
  by_cases h3 : v = 3
  · subst h3; exact c137_d3
  by_cases h6 : v = 6
  · subst h6; exact c137_d6
  by_cases h15 : v = 15
  · subst h15; exact c137_d15
  by_cases h24 : v = 24
  · subst h24; exact c137_d24
  by_cases h31 : v = 31
  · subst h31; exact c137_d31
  by_cases h36 : v = 36
  · subst h36; exact c137_d36
  by_cases h38 : v = 38
  · subst h38; exact c137_d38
  by_cases h52 : v = 52
  · subst h52; exact c137_d52
  by_cases h55 : v = 55
  · subst h55; exact c137_d55
  by_cases h59 : v = 59
  · subst h59; exact c137_d59
  simpa [h1, h3, h6, h15, h24, h31, h36, h38, h52, h55, h59] using h

theorem c137 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) = false := by
  have e := reach_succ 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4) rfl
  have h : (List.range 64).any (body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c137_a v (List.mem_range.mp hv)]; decide
  rw [c138, c139, h] at e
  exact e.trans (by decide +kernel)

theorem c133_d4 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 4 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 4 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 4 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 4 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^4)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 4 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^4)))) := rfl
  rw [c137] at e
  exact e.trans (by decide +kernel)

theorem c151 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^6) = false := by decide +kernel

theorem c133_d6 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 6 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 6 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 6 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 6 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^6)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 6 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^6)))) := rfl
  rw [c151] at e
  exact e.trans (by decide +kernel)

theorem c152 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^15) = false := by decide +kernel

theorem c133_d15 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 15 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 15 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 15 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 15 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 15 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^15)))) := rfl
  rw [c152] at e
  exact e.trans (by decide +kernel)

theorem c153 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^24) = false := by decide +kernel

theorem c133_d24 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 24 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 24 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 24 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 24 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^24)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 24 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^24)))) := rfl
  rw [c153] at e
  exact e.trans (by decide +kernel)

theorem c154 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^31) = false := by decide +kernel

theorem c133_d31 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 31 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 31 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 31 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 31 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 31 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^31)))) := rfl
  rw [c154] at e
  exact e.trans (by decide +kernel)

theorem c155 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^36) = false := by decide +kernel

theorem c133_d36 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 36 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 36 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 36 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 36 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^36)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 36 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^36)))) := rfl
  rw [c155] at e
  exact e.trans (by decide +kernel)

theorem c157 : reach 4 38 40 2 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) = false := by decide +kernel

theorem c158 : reach 4 38 40 2 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) = false := by decide +kernel

theorem c159 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^1) = false := by decide +kernel

theorem c156_d1 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 1 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 1 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 1 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 1 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^1)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 1 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^1)))) := rfl
  rw [c159] at e
  exact e.trans (by decide +kernel)

theorem c160 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^3) = false := by decide +kernel

theorem c156_d3 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 3 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 3 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 3 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 3 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^3)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 3 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^3)))) := rfl
  rw [c160] at e
  exact e.trans (by decide +kernel)

theorem c161 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^4) = false := by decide +kernel

theorem c156_d4 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 4 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 4 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 4 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 4 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^4)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 4 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^4)))) := rfl
  rw [c161] at e
  exact e.trans (by decide +kernel)

theorem c162 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^6) = false := by decide +kernel

theorem c156_d6 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 6 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 6 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 6 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 6 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^6)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 6 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^6)))) := rfl
  rw [c162] at e
  exact e.trans (by decide +kernel)

theorem c163 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^15) = false := by decide +kernel

theorem c156_d15 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 15 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 15 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 15 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 15 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^15)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 15 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^15)))) := rfl
  rw [c163] at e
  exact e.trans (by decide +kernel)

theorem c164 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^24) = false := by decide +kernel

theorem c156_d24 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 24 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 24 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 24 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 24 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^24)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 24 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^24)))) := rfl
  rw [c164] at e
  exact e.trans (by decide +kernel)

theorem c165 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^25) = false := by decide +kernel

theorem c156_d25 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 25 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 25 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 25 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 25 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^25)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 25 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^25)))) := rfl
  rw [c165] at e
  exact e.trans (by decide +kernel)

theorem c166 : reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^31) = false := by decide +kernel

theorem c156_d31 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 31 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 31 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 31 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 31 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^31)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 31 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^31)))) := rfl
  rw [c166] at e
  exact e.trans (by decide +kernel)

theorem c167 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^36) = false := by decide +kernel

theorem c156_d36 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 36 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 36 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 36 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 36 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^36)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 36 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^36)))) := rfl
  rw [c167] at e
  exact e.trans (by decide +kernel)

theorem c168 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^54) = false := by decide +kernel

theorem c156_d54 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 54 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 54 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 54 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 54 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^54)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 54 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^54)))) := rfl
  rw [c168] at e
  exact e.trans (by decide +kernel)

theorem c169 : reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^55) = false := by decide +kernel

theorem c156_d55 : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 55 = false := by
  have e : body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 55 = (!((((S0 ||| 2^7) ||| 2^39) ||| 2^38)).testBit 55 && ((aoHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 55 && reach 4 38 40 2 1 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^55)) ||
      (decide (0 < 1) && notHas (((S0 ||| 2^7) ||| 2^39) ||| 2^38) 55 && reach 4 38 40 2 0 ((((S0 ||| 2^7) ||| 2^39) ||| 2^38) ||| 2^55)))) := rfl
  rw [c169] at e
  exact e.trans (by decide +kernel)

theorem c156_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 15 || v == 24 || v == 25 || v == 31 || v == 36 || v == 54 || v == 55 || !body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) v) = true := by decide +kernel

theorem c156_a : ∀ v, v < 64 → body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c156_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c156_d1
  by_cases h3 : v = 3
  · subst h3; exact c156_d3
  by_cases h4 : v = 4
  · subst h4; exact c156_d4
  by_cases h6 : v = 6
  · subst h6; exact c156_d6
  by_cases h15 : v = 15
  · subst h15; exact c156_d15
  by_cases h24 : v = 24
  · subst h24; exact c156_d24
  by_cases h25 : v = 25
  · subst h25; exact c156_d25
  by_cases h31 : v = 31
  · subst h31; exact c156_d31
  by_cases h36 : v = 36
  · subst h36; exact c156_d36
  by_cases h54 : v = 54
  · subst h54; exact c156_d54
  by_cases h55 : v = 55
  · subst h55; exact c156_d55
  simpa [h1, h3, h4, h6, h15, h24, h25, h31, h36, h54, h55] using h

theorem c156 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) = false := by
  have e := reach_succ 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38) rfl
  have h : (List.range 64).any (body 4 38 40 2 1 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c156_a v (List.mem_range.mp hv)]; decide
  rw [c157, c158, h] at e
  exact e.trans (by decide +kernel)

theorem c133_d38 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 38 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 38 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 38 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 38 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^38)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 38 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^38)))) := rfl
  rw [c156] at e
  exact e.trans (by decide +kernel)

theorem c170 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^55) = false := by decide +kernel

theorem c133_d55 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 55 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) 55 = (!(((S0 ||| 2^7) ||| 2^39)).testBit 55 && ((aoHas ((S0 ||| 2^7) ||| 2^39) 55 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^39) ||| 2^55)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^39) 55 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^39) ||| 2^55)))) := rfl
  rw [c170] at e
  exact e.trans (by decide +kernel)

theorem c133_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 15 || v == 24 || v == 31 || v == 36 || v == 38 || v == 55 || !body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) v) = true := by decide +kernel

theorem c133_a : ∀ v, v < 64 → body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c133_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c133_d1
  by_cases h3 : v = 3
  · subst h3; exact c133_d3
  by_cases h4 : v = 4
  · subst h4; exact c133_d4
  by_cases h6 : v = 6
  · subst h6; exact c133_d6
  by_cases h15 : v = 15
  · subst h15; exact c133_d15
  by_cases h24 : v = 24
  · subst h24; exact c133_d24
  by_cases h31 : v = 31
  · subst h31; exact c133_d31
  by_cases h36 : v = 36
  · subst h36; exact c133_d36
  by_cases h38 : v = 38
  · subst h38; exact c133_d38
  by_cases h55 : v = 55
  · subst h55; exact c133_d55
  simpa [h1, h3, h4, h6, h15, h24, h31, h36, h38, h55] using h

theorem c133 : reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^39) = false := by
  have e := reach_succ 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39) rfl
  have h : (List.range 64).any (body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^39)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c133_a v (List.mem_range.mp hv)]; decide
  rw [c16, c134, h] at e
  exact e.trans (by decide +kernel)

theorem c41_d39 : body 4 38 40 4 1 0 (S0 ||| 2^7) 39 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 39 = (!((S0 ||| 2^7)).testBit 39 && ((aoHas (S0 ||| 2^7) 39 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^39)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 39 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^39)))) := rfl
  rw [c133] at e
  exact e.trans (by decide +kernel)

theorem c172 : reach 4 38 40 3 0 ((S0 ||| 2^7) ||| 2^55) = false := by decide +kernel

theorem c173 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^1) = false := by decide +kernel

theorem c171_d1 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 1 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 1 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 1 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 1 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 1 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^1)))) := rfl
  rw [c173] at e
  exact e.trans (by decide +kernel)

theorem c174 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^3) = false := by decide +kernel

theorem c171_d3 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 3 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 3 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 3 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 3 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 3 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^3)))) := rfl
  rw [c174] at e
  exact e.trans (by decide +kernel)

theorem c175 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^4) = false := by decide +kernel

theorem c171_d4 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 4 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 4 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 4 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 4 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^4)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 4 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^4)))) := rfl
  rw [c175] at e
  exact e.trans (by decide +kernel)

theorem c176 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^6) = false := by decide +kernel

theorem c171_d6 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 6 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 6 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 6 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 6 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^6)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 6 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^6)))) := rfl
  rw [c176] at e
  exact e.trans (by decide +kernel)

theorem c177 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^8) = false := by decide +kernel

theorem c171_d8 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 8 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 8 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 8 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 8 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^8)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 8 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^8)))) := rfl
  rw [c177] at e
  exact e.trans (by decide +kernel)

theorem c178 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^15) = false := by decide +kernel

theorem c171_d15 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 15 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 15 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 15 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 15 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^15)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 15 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^15)))) := rfl
  rw [c178] at e
  exact e.trans (by decide +kernel)

theorem c179 : reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^31) = false := by decide +kernel

theorem c171_d31 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 31 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 31 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 31 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 31 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 31 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^31)))) := rfl
  rw [c179] at e
  exact e.trans (by decide +kernel)

theorem c180 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^39) = false := by decide +kernel

theorem c171_d39 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 39 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 39 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 39 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 39 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^39)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 39 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^39)))) := rfl
  rw [c180] at e
  exact e.trans (by decide +kernel)

theorem c181 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^52) = false := by decide +kernel

theorem c171_d52 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 52 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 52 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 52 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 52 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^52)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 52 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^52)))) := rfl
  rw [c181] at e
  exact e.trans (by decide +kernel)

theorem c182 : reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^54) = false := by decide +kernel

theorem c171_d54 : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 54 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) 54 = (!(((S0 ||| 2^7) ||| 2^55)).testBit 54 && ((aoHas ((S0 ||| 2^7) ||| 2^55) 54 && reach 4 38 40 3 1 (((S0 ||| 2^7) ||| 2^55) ||| 2^54)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^7) ||| 2^55) 54 && reach 4 38 40 3 0 (((S0 ||| 2^7) ||| 2^55) ||| 2^54)))) := rfl
  rw [c182] at e
  exact e.trans (by decide +kernel)

theorem c171_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 8 || v == 15 || v == 31 || v == 39 || v == 52 || v == 54 || !body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) v) = true := by decide +kernel

theorem c171_a : ∀ v, v < 64 → body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c171_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c171_d1
  by_cases h3 : v = 3
  · subst h3; exact c171_d3
  by_cases h4 : v = 4
  · subst h4; exact c171_d4
  by_cases h6 : v = 6
  · subst h6; exact c171_d6
  by_cases h8 : v = 8
  · subst h8; exact c171_d8
  by_cases h15 : v = 15
  · subst h15; exact c171_d15
  by_cases h31 : v = 31
  · subst h31; exact c171_d31
  by_cases h39 : v = 39
  · subst h39; exact c171_d39
  by_cases h52 : v = 52
  · subst h52; exact c171_d52
  by_cases h54 : v = 54
  · subst h54; exact c171_d54
  simpa [h1, h3, h4, h6, h8, h15, h31, h39, h52, h54] using h

theorem c171 : reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^55) = false := by
  have e := reach_succ 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55) rfl
  have h : (List.range 64).any (body 4 38 40 3 1 0 ((S0 ||| 2^7) ||| 2^55)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c171_a v (List.mem_range.mp hv)]; decide
  rw [c17, c172, h] at e
  exact e.trans (by decide +kernel)

theorem c41_d55 : body 4 38 40 4 1 0 (S0 ||| 2^7) 55 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^7) 55 = (!((S0 ||| 2^7)).testBit 55 && ((aoHas (S0 ||| 2^7) 55 && reach 4 38 40 4 1 ((S0 ||| 2^7) ||| 2^55)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^7) 55 && reach 4 38 40 4 0 ((S0 ||| 2^7) ||| 2^55)))) := rfl
  rw [c171] at e
  exact e.trans (by decide +kernel)

theorem c41_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 4 || v == 6 || v == 15 || v == 31 || v == 39 || v == 55 || !body 4 38 40 4 1 0 (S0 ||| 2^7) v) = true := by decide +kernel

theorem c41_a : ∀ v, v < 64 → body 4 38 40 4 1 0 (S0 ||| 2^7) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c41_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c41_d1
  by_cases h3 : v = 3
  · subst h3; exact c41_d3
  by_cases h4 : v = 4
  · subst h4; exact c41_d4
  by_cases h6 : v = 6
  · subst h6; exact c41_d6
  by_cases h15 : v = 15
  · subst h15; exact c41_d15
  by_cases h31 : v = 31
  · subst h31; exact c41_d31
  by_cases h39 : v = 39
  · subst h39; exact c41_d39
  by_cases h55 : v = 55
  · subst h55; exact c41_d55
  simpa [h1, h3, h4, h6, h15, h31, h39, h55] using h

theorem c41 : reach 4 38 40 5 1 (S0 ||| 2^7) = false := by
  have e := reach_succ 4 38 40 4 1 0 (S0 ||| 2^7) rfl
  have h : (List.range 64).any (body 4 38 40 4 1 0 (S0 ||| 2^7)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c41_a v (List.mem_range.mp hv)]; decide
  rw [c7, c42, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d7 : body 4 38 40 5 2 1 S0 7 = false := by
  have e : body 4 38 40 5 2 1 S0 7 = (!(S0).testBit 7 && ((aoHas S0 7 && reach 4 38 40 5 2 (S0 ||| 2^7)) ||
      (decide (0 < 2) && notHas S0 7 && reach 4 38 40 5 1 (S0 ||| 2^7)))) := rfl
  rw [c41] at e
  exact e.trans (by decide +kernel)

theorem c184 : reach 4 38 40 4 0 (S0 ||| 2^15) = false := by decide +kernel

theorem c185 : reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^1) = false := by decide +kernel

theorem c183_d1 : body 4 38 40 4 1 0 (S0 ||| 2^15) 1 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 1 = (!((S0 ||| 2^15)).testBit 1 && ((aoHas (S0 ||| 2^15) 1 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 1 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^1)))) := rfl
  rw [c185] at e
  exact e.trans (by decide +kernel)

theorem c186 : reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^3) = false := by decide +kernel

theorem c183_d3 : body 4 38 40 4 1 0 (S0 ||| 2^15) 3 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 3 = (!((S0 ||| 2^15)).testBit 3 && ((aoHas (S0 ||| 2^15) 3 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 3 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^3)))) := rfl
  rw [c186] at e
  exact e.trans (by decide +kernel)

theorem c188 : reach 4 38 40 3 0 ((S0 ||| 2^15) ||| 2^7) = false := by decide +kernel

theorem c189 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^4) = false := by decide +kernel

theorem c187_d4 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 4 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 4 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 4 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 4 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^4)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 4 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^4)))) := rfl
  rw [c189] at e
  exact e.trans (by decide +kernel)

theorem c190 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^6) = false := by decide +kernel

theorem c187_d6 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 6 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 6 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 6 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 6 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^6)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 6 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^6)))) := rfl
  rw [c190] at e
  exact e.trans (by decide +kernel)

theorem c191 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^8) = false := by decide +kernel

theorem c187_d8 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 8 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 8 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 8 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^8)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 8 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^8)))) := rfl
  rw [c191] at e
  exact e.trans (by decide +kernel)

theorem c192 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^12) = false := by decide +kernel

theorem c187_d12 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 12 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 12 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 12 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^12)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 12 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^12)))) := rfl
  rw [c192] at e
  exact e.trans (by decide +kernel)

theorem c193 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^14) = false := by decide +kernel

theorem c187_d14 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 14 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 14 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 14 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^14)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 14 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^14)))) := rfl
  rw [c193] at e
  exact e.trans (by decide +kernel)

theorem c194 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^39) = false := by decide +kernel

theorem c187_d39 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 39 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 39 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 39 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 39 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^39)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 39 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^39)))) := rfl
  rw [c194] at e
  exact e.trans (by decide +kernel)

theorem c195 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^47) = false := by decide +kernel

theorem c187_d47 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 47 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 47 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 47 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 47 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^47)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 47 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^47)))) := rfl
  rw [c195] at e
  exact e.trans (by decide +kernel)

theorem c196 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^55) = false := by decide +kernel

theorem c187_d55 : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 55 = false := by
  have e : body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) 55 = (!(((S0 ||| 2^15) ||| 2^7)).testBit 55 && ((aoHas ((S0 ||| 2^15) ||| 2^7) 55 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^55)) ||
      (decide (0 < 0) && notHas ((S0 ||| 2^15) ||| 2^7) 55 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^7) ||| 2^55)))) := rfl
  rw [c196] at e
  exact e.trans (by decide +kernel)

theorem c187_o : (List.range 64).all (fun v => v == 4 || v == 6 || v == 8 || v == 12 || v == 14 || v == 39 || v == 47 || v == 55 || !body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) v) = true := by decide +kernel

theorem c187_a : ∀ v, v < 64 → body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c187_o v (List.mem_range.mpr hv)
  by_cases h4 : v = 4
  · subst h4; exact c187_d4
  by_cases h6 : v = 6
  · subst h6; exact c187_d6
  by_cases h8 : v = 8
  · subst h8; exact c187_d8
  by_cases h12 : v = 12
  · subst h12; exact c187_d12
  by_cases h14 : v = 14
  · subst h14; exact c187_d14
  by_cases h39 : v = 39
  · subst h39; exact c187_d39
  by_cases h47 : v = 47
  · subst h47; exact c187_d47
  by_cases h55 : v = 55
  · subst h55; exact c187_d55
  simpa [h4, h6, h8, h12, h14, h39, h47, h55] using h

theorem c187 : reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^7) = false := by
  have e := reach_succ 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7) rfl
  have h : (List.range 64).any (body 4 38 40 3 0 0 ((S0 ||| 2^15) ||| 2^7)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c187_a v (List.mem_range.mp hv)]; decide
  rw [c188, h] at e
  exact e.trans (by decide +kernel)

theorem c183_d7 : body 4 38 40 4 1 0 (S0 ||| 2^15) 7 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 7 = (!((S0 ||| 2^15)).testBit 7 && ((aoHas (S0 ||| 2^15) 7 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 7 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^7)))) := rfl
  rw [c187] at e
  exact e.trans (by decide +kernel)

theorem c197 : reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^8) = false := by decide +kernel

theorem c183_d8 : body 4 38 40 4 1 0 (S0 ||| 2^15) 8 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 8 = (!((S0 ||| 2^15)).testBit 8 && ((aoHas (S0 ||| 2^15) 8 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^8)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 8 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^8)))) := rfl
  rw [c197] at e
  exact e.trans (by decide +kernel)

theorem c198 : reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^12) = false := by decide +kernel

theorem c183_d12 : body 4 38 40 4 1 0 (S0 ||| 2^15) 12 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 12 = (!((S0 ||| 2^15)).testBit 12 && ((aoHas (S0 ||| 2^15) 12 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^12)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 12 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^12)))) := rfl
  rw [c198] at e
  exact e.trans (by decide +kernel)

theorem c199 : reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^14) = false := by decide +kernel

theorem c183_d14 : body 4 38 40 4 1 0 (S0 ||| 2^15) 14 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 14 = (!((S0 ||| 2^15)).testBit 14 && ((aoHas (S0 ||| 2^15) 14 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^14)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 14 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^14)))) := rfl
  rw [c199] at e
  exact e.trans (by decide +kernel)

theorem c200 : reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^31) = false := by decide +kernel

theorem c183_d31 : body 4 38 40 4 1 0 (S0 ||| 2^15) 31 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 31 = (!((S0 ||| 2^15)).testBit 31 && ((aoHas (S0 ||| 2^15) 31 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^31)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 31 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^31)))) := rfl
  rw [c200] at e
  exact e.trans (by decide +kernel)

theorem c202 : reach 4 38 40 3 1 ((S0 ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c203 : reach 4 38 40 3 0 ((S0 ||| 2^15) ||| 2^47) = false := by decide +kernel

theorem c204 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^1) = false := by decide +kernel

theorem c201_d1 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 1 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 1 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 1 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 1 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^1)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 1 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^1)))) := rfl
  rw [c204] at e
  exact e.trans (by decide +kernel)

theorem c205 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^3) = false := by decide +kernel

theorem c201_d3 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 3 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 3 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 3 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 3 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^3)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 3 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^3)))) := rfl
  rw [c205] at e
  exact e.trans (by decide +kernel)

theorem c206 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^7) = false := by decide +kernel

theorem c201_d7 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 7 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 7 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 7 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 7 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^7)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 7 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^7)))) := rfl
  rw [c206] at e
  exact e.trans (by decide +kernel)

theorem c207 : reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^8) = false := by decide +kernel

theorem c201_d8 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 8 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 8 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 8 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 8 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^8)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 8 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^8)))) := rfl
  rw [c207] at e
  exact e.trans (by decide +kernel)

theorem c208 : reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^12) = false := by decide +kernel

theorem c201_d12 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 12 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 12 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 12 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 12 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^12)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 12 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^12)))) := rfl
  rw [c208] at e
  exact e.trans (by decide +kernel)

theorem c209 : reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^14) = false := by decide +kernel

theorem c201_d14 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 14 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 14 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 14 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 14 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^14)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 14 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^14)))) := rfl
  rw [c209] at e
  exact e.trans (by decide +kernel)

theorem c210 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^16) = false := by decide +kernel

theorem c201_d16 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 16 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 16 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 16 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 16 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^16)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 16 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^16)))) := rfl
  rw [c210] at e
  exact e.trans (by decide +kernel)

theorem c211 : reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^31) = false := by decide +kernel

theorem c201_d31 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 31 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 31 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 31 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 31 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^31)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 31 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^31)))) := rfl
  rw [c211] at e
  exact e.trans (by decide +kernel)

theorem c212 : reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^40) = false := by decide +kernel

theorem c201_d40 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 40 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 40 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 40 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 40 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^40)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 40 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^40)))) := rfl
  rw [c212] at e
  exact e.trans (by decide +kernel)

theorem c213 : reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^44) = false := by decide +kernel

theorem c201_d44 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 44 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 44 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 44 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 44 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^44)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 44 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^44)))) := rfl
  rw [c213] at e
  exact e.trans (by decide +kernel)

theorem c214 : reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^46) = false := by decide +kernel

theorem c201_d46 : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 46 = false := by
  have e : body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) 46 = (!(((S0 ||| 2^15) ||| 2^47)).testBit 46 && ((aoHas ((S0 ||| 2^15) ||| 2^47) 46 && reach 4 38 40 3 1 (((S0 ||| 2^15) ||| 2^47) ||| 2^46)) ||
      (decide (0 < 1) && notHas ((S0 ||| 2^15) ||| 2^47) 46 && reach 4 38 40 3 0 (((S0 ||| 2^15) ||| 2^47) ||| 2^46)))) := rfl
  rw [c214] at e
  exact e.trans (by decide +kernel)

theorem c201_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 14 || v == 16 || v == 31 || v == 40 || v == 44 || v == 46 || !body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) v) = true := by decide +kernel

theorem c201_a : ∀ v, v < 64 → body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c201_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c201_d1
  by_cases h3 : v = 3
  · subst h3; exact c201_d3
  by_cases h7 : v = 7
  · subst h7; exact c201_d7
  by_cases h8 : v = 8
  · subst h8; exact c201_d8
  by_cases h12 : v = 12
  · subst h12; exact c201_d12
  by_cases h14 : v = 14
  · subst h14; exact c201_d14
  by_cases h16 : v = 16
  · subst h16; exact c201_d16
  by_cases h31 : v = 31
  · subst h31; exact c201_d31
  by_cases h40 : v = 40
  · subst h40; exact c201_d40
  by_cases h44 : v = 44
  · subst h44; exact c201_d44
  by_cases h46 : v = 46
  · subst h46; exact c201_d46
  simpa [h1, h3, h7, h8, h12, h14, h16, h31, h40, h44, h46] using h

theorem c201 : reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^47) = false := by
  have e := reach_succ 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47) rfl
  have h : (List.range 64).any (body 4 38 40 3 1 0 ((S0 ||| 2^15) ||| 2^47)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c201_a v (List.mem_range.mp hv)]; decide
  rw [c202, c203, h] at e
  exact e.trans (by decide +kernel)

theorem c183_d47 : body 4 38 40 4 1 0 (S0 ||| 2^15) 47 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^15) 47 = (!((S0 ||| 2^15)).testBit 47 && ((aoHas (S0 ||| 2^15) 47 && reach 4 38 40 4 1 ((S0 ||| 2^15) ||| 2^47)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^15) 47 && reach 4 38 40 4 0 ((S0 ||| 2^15) ||| 2^47)))) := rfl
  rw [c201] at e
  exact e.trans (by decide +kernel)

theorem c183_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 8 || v == 12 || v == 14 || v == 31 || v == 47 || !body 4 38 40 4 1 0 (S0 ||| 2^15) v) = true := by decide +kernel

theorem c183_a : ∀ v, v < 64 → body 4 38 40 4 1 0 (S0 ||| 2^15) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c183_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c183_d1
  by_cases h3 : v = 3
  · subst h3; exact c183_d3
  by_cases h7 : v = 7
  · subst h7; exact c183_d7
  by_cases h8 : v = 8
  · subst h8; exact c183_d8
  by_cases h12 : v = 12
  · subst h12; exact c183_d12
  by_cases h14 : v = 14
  · subst h14; exact c183_d14
  by_cases h31 : v = 31
  · subst h31; exact c183_d31
  by_cases h47 : v = 47
  · subst h47; exact c183_d47
  simpa [h1, h3, h7, h8, h12, h14, h31, h47] using h

theorem c183 : reach 4 38 40 5 1 (S0 ||| 2^15) = false := by
  have e := reach_succ 4 38 40 4 1 0 (S0 ||| 2^15) rfl
  have h : (List.range 64).any (body 4 38 40 4 1 0 (S0 ||| 2^15)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c183_a v (List.mem_range.mp hv)]; decide
  rw [c18, c184, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d15 : body 4 38 40 5 2 1 S0 15 = false := by
  have e : body 4 38 40 5 2 1 S0 15 = (!(S0).testBit 15 && ((aoHas S0 15 && reach 4 38 40 5 2 (S0 ||| 2^15)) ||
      (decide (0 < 2) && notHas S0 15 && reach 4 38 40 5 1 (S0 ||| 2^15)))) := rfl
  rw [c183] at e
  exact e.trans (by decide +kernel)

theorem c216 : reach 4 38 40 4 0 (S0 ||| 2^31) = false := by decide +kernel

theorem c217 : reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^1) = false := by decide +kernel

theorem c215_d1 : body 4 38 40 4 1 0 (S0 ||| 2^31) 1 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 1 = (!((S0 ||| 2^31)).testBit 1 && ((aoHas (S0 ||| 2^31) 1 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^1)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 1 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^1)))) := rfl
  rw [c217] at e
  exact e.trans (by decide +kernel)

theorem c218 : reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^3) = false := by decide +kernel

theorem c215_d3 : body 4 38 40 4 1 0 (S0 ||| 2^31) 3 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 3 = (!((S0 ||| 2^31)).testBit 3 && ((aoHas (S0 ||| 2^31) 3 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^3)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 3 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^3)))) := rfl
  rw [c218] at e
  exact e.trans (by decide +kernel)

theorem c219 : reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^7) = false := by decide +kernel

theorem c215_d7 : body 4 38 40 4 1 0 (S0 ||| 2^31) 7 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 7 = (!((S0 ||| 2^31)).testBit 7 && ((aoHas (S0 ||| 2^31) 7 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^7)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 7 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^7)))) := rfl
  rw [c219] at e
  exact e.trans (by decide +kernel)

theorem c220 : reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^15) = false := by decide +kernel

theorem c215_d15 : body 4 38 40 4 1 0 (S0 ||| 2^31) 15 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 15 = (!((S0 ||| 2^31)).testBit 15 && ((aoHas (S0 ||| 2^31) 15 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^15)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 15 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^15)))) := rfl
  rw [c220] at e
  exact e.trans (by decide +kernel)

theorem c221 : reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^16) = false := by decide +kernel

theorem c215_d16 : body 4 38 40 4 1 0 (S0 ||| 2^31) 16 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 16 = (!((S0 ||| 2^31)).testBit 16 && ((aoHas (S0 ||| 2^31) 16 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^16)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 16 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^16)))) := rfl
  rw [c221] at e
  exact e.trans (by decide +kernel)

theorem c222 : reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^24) = false := by decide +kernel

theorem c215_d24 : body 4 38 40 4 1 0 (S0 ||| 2^31) 24 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 24 = (!((S0 ||| 2^31)).testBit 24 && ((aoHas (S0 ||| 2^31) 24 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^24)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 24 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^24)))) := rfl
  rw [c222] at e
  exact e.trans (by decide +kernel)

theorem c223 : reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^28) = false := by decide +kernel

theorem c215_d28 : body 4 38 40 4 1 0 (S0 ||| 2^31) 28 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 28 = (!((S0 ||| 2^31)).testBit 28 && ((aoHas (S0 ||| 2^31) 28 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^28)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 28 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^28)))) := rfl
  rw [c223] at e
  exact e.trans (by decide +kernel)

theorem c224 : reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^30) = false := by decide +kernel

theorem c215_d30 : body 4 38 40 4 1 0 (S0 ||| 2^31) 30 = false := by
  have e : body 4 38 40 4 1 0 (S0 ||| 2^31) 30 = (!((S0 ||| 2^31)).testBit 30 && ((aoHas (S0 ||| 2^31) 30 && reach 4 38 40 4 1 ((S0 ||| 2^31) ||| 2^30)) ||
      (decide (0 < 1) && notHas (S0 ||| 2^31) 30 && reach 4 38 40 4 0 ((S0 ||| 2^31) ||| 2^30)))) := rfl
  rw [c224] at e
  exact e.trans (by decide +kernel)

theorem c215_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 16 || v == 24 || v == 28 || v == 30 || !body 4 38 40 4 1 0 (S0 ||| 2^31) v) = true := by decide +kernel

theorem c215_a : ∀ v, v < 64 → body 4 38 40 4 1 0 (S0 ||| 2^31) v = false := by
  intro v hv
  have h := List.all_eq_true.mp c215_o v (List.mem_range.mpr hv)
  by_cases h1 : v = 1
  · subst h1; exact c215_d1
  by_cases h3 : v = 3
  · subst h3; exact c215_d3
  by_cases h7 : v = 7
  · subst h7; exact c215_d7
  by_cases h15 : v = 15
  · subst h15; exact c215_d15
  by_cases h16 : v = 16
  · subst h16; exact c215_d16
  by_cases h24 : v = 24
  · subst h24; exact c215_d24
  by_cases h28 : v = 28
  · subst h28; exact c215_d28
  by_cases h30 : v = 30
  · subst h30; exact c215_d30
  simpa [h1, h3, h7, h15, h16, h24, h28, h30] using h

theorem c215 : reach 4 38 40 5 1 (S0 ||| 2^31) = false := by
  have e := reach_succ 4 38 40 4 1 0 (S0 ||| 2^31) rfl
  have h : (List.range 64).any (body 4 38 40 4 1 0 (S0 ||| 2^31)) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c215_a v (List.mem_range.mp hv)]; decide
  rw [c19, c216, h] at e
  exact e.trans (by decide +kernel)

theorem c1_d31 : body 4 38 40 5 2 1 S0 31 = false := by
  have e : body 4 38 40 5 2 1 S0 31 = (!(S0).testBit 31 && ((aoHas S0 31 && reach 4 38 40 5 2 (S0 ||| 2^31)) ||
      (decide (0 < 2) && notHas S0 31 && reach 4 38 40 5 1 (S0 ||| 2^31)))) := rfl
  rw [c215] at e
  exact e.trans (by decide +kernel)

theorem c1_o : (List.range 64).all (fun v => v == 1 || v == 3 || v == 7 || v == 15 || v == 31 || !body 4 38 40 5 2 1 S0 v) = true := by decide +kernel

theorem c1_a : ∀ v, v < 64 → body 4 38 40 5 2 1 S0 v = false := by
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

theorem c1 : reach 4 38 40 6 2 S0 = false := by
  have e := reach_succ 4 38 40 5 2 1 S0 rfl
  have h : (List.range 64).any (body 4 38 40 5 2 1 S0) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rw [c1_a v (List.mem_range.mp hv)]; decide
  rw [c2, c20, h] at e
  exact e.trans (by decide +kernel)

theorem cert : reach 4 38 40 6 2 S0 = false := c1

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
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hf, hr, hn, hs, ht⟩
  have := sound 4 38 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    D.gates (fun t => (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])
    7 S0 6 2 (fun t => by simp) (by decide) (by decide) init hf hr hs hn p.val q.val r.val
    p.isLt q.isLt r.isLt (fun t => ht t)
  rw [cert] at this
  exact absurd this (by decide)

end PEqualNP.Outside.L_meta_50269

theorem PEqualNP.Outside.L_meta_50269 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_50269.main
