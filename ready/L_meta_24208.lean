import PEqualNP.Defs

-- LOAD CANARY (infra, 27 Nov): placeholder for a DRY drain run, never filed.

theorem PEqualNP.Outside.L_meta_24208 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583195 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide
