import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

theorem PEqualNP.Outside.L_meta_50445 : (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (36 : Nat).testBit t.val ∧
    w.getD q.val false = (52 : Nat).testBit t.val ∧
    w.getD r.val false = (58 : Nat).testBit t.val) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [8, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [11, 0]⟩], 12⟩,
    ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack
    decide
  · decide
  · decide
  · decide
