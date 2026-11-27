import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19745

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 14]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [25, 24]⟩, ⟨.and, [23, 20]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [30, 24]⟩, ⟨.and, [32, 22]⟩, ⟨.or, [2, 19]⟩, ⟨.and, [34, 26]⟩, ⟨.or, [33, 35]⟩, ⟨.and, [31, 27]⟩, ⟨.or, [28, 37]⟩, ⟨.or, [29, 36]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19745

theorem PEqualNP.Outside.L_drill_rr10_19745 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10692751789718129190 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19745.C_, PEqualNP.Outside.L_drill_rr10_19745.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19745.C_ (by decide +kernel), by decide, by decide +kernel⟩
