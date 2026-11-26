import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20815

theorem minex (Q : PEqualNP.CircuitLowerBounds.Circuit → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hC : Q C) : ∃ D, Q D ∧ D.size ≤ C.size ∧ ∀ D', Q D' → D.size ≤ D'.size := by
  classical
  have hex : ∃ s, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Q D ∧ D.size = s := ⟨_, C, hC, rfl⟩
  obtain ⟨D, hD, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, ?_, ?_⟩
  · rw [hs]; exact Nat.find_min' hex ⟨C, hC, rfl⟩
  · intro D' hD'
    rw [hs]; exact Nat.find_min' hex ⟨D', hD', rfl⟩

end PEqualNP.Outside.L_meta_20815

theorem PEqualNP.Outside.L_meta_20815 :
    ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ j < C.size, ¬ PEqualNP.Represents.Represents A
    (⟨C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ :
      PEqualNP.CircuitLowerBounds.Circuit) := by
  intro n m R _ C _ hC hf
  obtain ⟨D, ⟨h1, h2⟩, hle, hmin⟩ := PEqualNP.Outside.L_meta_20815.minex
    (fun D => PEqualNP.TopForm.IsAO2 (n + m) D ∧ PEqualNP.MetaComplexity.circuitFun (n + m) D = _) C ⟨hC, hf⟩
  exact ⟨D, h1, h2, hle, fun D' h1' h2' => hmin D' ⟨h1', h2'⟩⟩
