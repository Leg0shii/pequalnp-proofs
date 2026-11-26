import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20643 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7373824 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
