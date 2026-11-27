import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_25762 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 21 ∧ PEqualNP.Represents.Represents (fun (u : Fin 8) (v : Fin 6) => (187576881878421 : ℕ).testBit (6 * u.val + v.val)) C := by
  refine ⟨⟨[
    ⟨.or, [5, 12]⟩,
    ⟨.or, [9, 0]⟩,
    ⟨.or, [13, 2]⟩,
    ⟨.or, [1, 15]⟩,
    ⟨.or, [15, 6]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.or, [6, 19]⟩,
    ⟨.or, [14, 21]⟩,
    ⟨.and, [24, 17]⟩,
    ⟨.or, [21, 16]⟩,
    ⟨.or, [1, 19]⟩,
    ⟨.or, [20, 16]⟩,
    ⟨.and, [27, 18]⟩,
    ⟨.and, [26, 22]⟩,
    ⟨.or, [30, 25]⟩,
    ⟨.and, [23, 28]⟩,
    ⟨.or, [29, 31]⟩,
    ⟨.or, [32, 33]⟩], 34⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
