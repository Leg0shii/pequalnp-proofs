import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_23962

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [ih, step]; omega

theorem fold_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [step]; omega)]
    simp only [step]
    exact List.getD_append _ _ _ _ hi

theorem fold_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length)
    (hin : ∀ i ∈ gs[k].inputs, i < w.length + k) :
    (gs.foldl step w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (gs.foldl step w).getD i false) := by
  have hsplit : gs = gs.take k ++ [gs[k]] ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
  set w0 := (gs.take k).foldl step w with hw0
  have hl0 : w0.length = w.length + k := by
    rw [hw0, fold_len]; simp; omega
  have hW : gs.foldl step w = (gs.drop (k + 1)).foldl step (step w0 gs[k]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append]
    rfl
  have hpre : ∀ i, i < w.length + k + 1 → (gs.foldl step w).getD i false = (step w0 gs[k]).getD i false := by
    intro i hi
    rw [hW, fold_prefix _ _ i (by simp [step]; omega)]
  rw [hpre _ (by omega)]
  have hmap : (gs[k].inputs.map fun i => (gs.foldl step w).getD i false) =
      (gs[k].inputs.map fun i => w0.getD i false) := by
    apply List.map_congr_left
    intro i hi
    rw [hpre i (by have := hin i hi; omega)]
    simp only [step]
    exact List.getD_append _ _ _ _ (by have := hin i hi; omega)
  rw [hmap]
  simp only [step]
  rw [← hl0, List.getD_append_right _ _ _ _ le_rfl]
  simp

end PEqualNP.Outside.L_meta_23962

theorem PEqualNP.Outside.L_meta_23962 :
    ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ (p : List ℕ) (i2 i3 qa qb qc : ℕ) (Pa Pb Pc : Finset ℕ),
  0 < i2 → i2 < i3 → i3 < p.length →
  (∀ k < p.length, p.getD k 0 < C.size) →
  (∀ k, k + 1 < p.length →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + m + p.getD k 0) = 1 ∧
    C.output ≠ n + m + p.getD k 0 ∧
    n + m + p.getD k 0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD (k + 1) 0)).inputs) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  qa ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).inputs →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [n + m + p.getD (i2 - 1) 0, qb] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [qb, n + m + p.getD (i2 - 1) 0]) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [n + m + p.getD (i3 - 1) 0, qc] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [qc, n + m + p.getD (i3 - 1) 0]) →
  Disjoint Pa Pb → Disjoint Pa Pc → Disjoint Pb Pc →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qa false = true →
    (u : ℕ) ∈ Pa ∨ n + (v : ℕ) ∈ Pa) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qb false = true →
    (u : ℕ) ∈ Pb ∨ n + (v : ℕ) ∈ Pb) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qc false = true →
    (u : ℕ) ∈ Pc ∨ n + (v : ℕ) ∈ Pc) →
  False := by
  intro n C hC hn ho hg
  obtain ⟨g, hg, hop⟩ := hg
  have hk : C.output - n < C.gates.length := by
    simp only [Circuit.size] at ho; omega
  have hgk : C.gates[C.output - n] = g := by
    rw [List.getElem?_eq_getElem hk] at hg
    exact Option.some.inj hg
  have hlen2 : g.inputs.length = 2 := hC.2.2 g (hgk ▸ List.getElem_mem hk)
  have hrb : ∀ i ∈ g.inputs, i < n + (C.output - n) := by
    intro i hi
    have := hC.2.1 (C.output - n) hk i
    apply this
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, Option.getD_some, hgk]
    exact hi
  obtain ⟨i, j, hij⟩ : ∃ i j, g.inputs = [i, j] := by
    match h : g.inputs, hlen2 with
    | [i, j], _ => exact ⟨i, j, rfl⟩
  have hi : i < n + (C.output - n) := hrb i (by simp [hij])
  have hj : j < n + (C.output - n) := hrb j (by simp [hij])
  refine ⟨i, j, by omega, by omega, ?_⟩
  intro x hx
  have key := PEqualNP.Outside.L_meta_23962.fold_gate C.gates x (C.output - n) hk (by
    rw [hgk, hx]; exact hrb)
  rw [hx, show n + (C.output - n) = C.output by omega, hgk, hij, hop] at key
  show (C.gates.foldl PEqualNP.Outside.L_meta_23962.step x).getD C.output false = _
  rw [key]
  simp [GateOp.eval]
  rfl
