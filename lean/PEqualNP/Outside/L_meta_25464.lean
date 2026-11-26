import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25464

theorem minex (Q : PEqualNP.CircuitLowerBounds.Circuit → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hC : Q C) : ∃ D, Q D ∧ D.size ≤ C.size ∧ ∀ D', Q D' → D.size ≤ D'.size := by
  classical
  have hex : ∃ s, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Q D ∧ D.size = s := ⟨_, C, hC, rfl⟩
  obtain ⟨D, hD, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, ?_, ?_⟩
  · rw [hs]; exact Nat.find_min' hex ⟨C, hC, rfl⟩
  · intro D' hD'
    rw [hs]; exact Nat.find_min' hex ⟨D', hD', rfl⟩

end PEqualNP.Outside.L_meta_25464

theorem PEqualNP.Outside.L_meta_25464 :
    ∀ (n m n0 m0 s t : ℕ) (Q : Fin n0 → Fin m0 → Bool) (f : Fin n → Fin n0) (g : Fin m → Fin m0), Function.Surjective f → Function.Surjective g → (PEqualNP.Represents.RepSizeAtMost Q s → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) (s + (n - n0) + (m - m0))) ∧ ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ t ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) C) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ t ∧ PEqualNP.Represents.Represents Q C') := by
  intro n m R _ C _ hC hf
  obtain ⟨D, ⟨h1, h2⟩, hle, hmin⟩ := PEqualNP.Outside.L_meta_25464.minex
    (fun D => PEqualNP.TopForm.IsAO2 (n + m) D ∧ PEqualNP.MetaComplexity.circuitFun (n + m) D = _) C ⟨hC, hf⟩
  exact ⟨D, h1, h2, hle, fun D' h1' h2' => hmin D' ⟨h1', h2'⟩⟩
