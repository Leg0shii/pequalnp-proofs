import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19787

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 8]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [27, 28]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [30, 31]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 19]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [22, 24]⟩, ⟨.and, [26, 29]⟩, ⟨.and, [32, 36]⟩, ⟨.and, [37, 8]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 43]⟩], 44⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_drill_rr10_19787

theorem PEqualNP.Outside.L_drill_rr10_19787 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15451209511025767005 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19787.C_, PEqualNP.Outside.L_drill_rr10_19787.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19787.C_ (by decide +kernel), by decide, by decide +kernel⟩
