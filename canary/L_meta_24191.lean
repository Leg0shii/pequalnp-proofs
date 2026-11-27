import PEqualNP.Defs

-- CANARY A (infra, 27 Nov): dry-run input for the cloud opener's live reads. Placeholder proof, never filed.

theorem PEqualNP.Outside.L_meta_24191 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34634582463 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide
