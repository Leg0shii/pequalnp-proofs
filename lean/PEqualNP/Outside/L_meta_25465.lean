import PEqualNP.Defs

set_option maxHeartbeats 20000 in
theorem PEqualNP.Outside.L_meta_25465 :
    ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (p q h h' : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ w : ℕ, ((List.range C.gates.length).map (fun r => (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs.count w)).sum ≤ 1) → p < C.gates.length → q < C.gates.length → p ≠ q → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.head? = some (n + m + h) → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).inputs.head? = some (n + m + h') → h < p → h' < q → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p ∨ j = q) → ¬ (p = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C p h') → ¬ (q = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C q h) → (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + h) false = true → (∃ i : ℕ, (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ u.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs) ∧ (∃ i : ℕ, (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ (n + v.val) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs)) → (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + h') false = true → (∃ i : ℕ, (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h') ∧ u.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs) ∧ (∃ i : ℕ, (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h') ∧ (n + v.val) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 ≤ s ∧ PEqualNP.Represents.Represents A D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧ (∀ w : ℕ, ((List.range D.gates.length).map (fun r => (PEqualNP.MetaComplexity.NestedCover.gateAt D r).inputs.count w)).sum ≤ 1) ∧ (∀ j < D.gates.length, ∀ j' < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt D j').op = PEqualNP.CircuitLowerBounds.GateOp.not → j = j') := by
  first
  | solve | rfl
  | solve | intros; assumption
  | solve | intro prior; intros; apply prior <;> first | assumption | exact le_rfl | omega
  | solve | dsimp only; intros; grind only
  | solve | intros; omega
  | solve | simp_all
  | solve | tauto
  | solve | norm_num
  | solve | aesop
  | solve | decide +revert +kernel
  | solve | decide +kernel
