import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19757

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 2]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [9, 0]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [23, 11]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [27, 4]⟩, ⟨.or, [30, 28]⟩, ⟨.or, [4, 19]⟩, ⟨.and, [31, 25]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [21, 17]⟩, ⟨.and, [28, 35]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [37, 36]⟩, ⟨.and, [32, 18]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19757

theorem PEqualNP.Outside.L_drill_rr10_19757 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9891717104032518705 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19757.C_, PEqualNP.Outside.L_drill_rr10_19757.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19757.C_ (by decide +kernel), by decide, by decide +kernel⟩
