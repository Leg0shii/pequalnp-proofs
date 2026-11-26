import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25447

theorem minex (Q : PEqualNP.CircuitLowerBounds.Circuit → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hC : Q C) : ∃ D, Q D ∧ D.size ≤ C.size ∧ ∀ D', Q D' → D.size ≤ D'.size := by
  classical
  have hex : ∃ s, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Q D ∧ D.size = s := ⟨_, C, hC, rfl⟩
  obtain ⟨D, hD, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, ?_, ?_⟩
  · rw [hs]; exact Nat.find_min' hex ⟨C, hC, rfl⟩
  · intro D' hD'
    rw [hs]; exact Nat.find_min' hex ⟨D', hD', rfl⟩

end PEqualNP.Outside.L_meta_25447

theorem PEqualNP.Outside.L_meta_25447 :
    ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (s : ℕ), PEqualNP.Represents.RepSizeAtMost A s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C ∧ ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + k) false = true → A u v = true := by
  intro n m R _ C _ hC hf
  obtain ⟨D, ⟨h1, h2⟩, hle, hmin⟩ := PEqualNP.Outside.L_meta_25447.minex
    (fun D => PEqualNP.TopForm.IsAO2 (n + m) D ∧ PEqualNP.MetaComplexity.circuitFun (n + m) D = _) C ⟨hC, hf⟩
  exact ⟨D, h1, h2, hle, fun D' h1' h2' => hmin D' ⟨h1', h2'⟩⟩
