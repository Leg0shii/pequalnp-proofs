import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19795

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 9]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [1, 20]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [26, 19]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [28, 16]⟩, ⟨.or, [29, 21]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [31, 22]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [33, 19]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [35, 23]⟩, ⟨.and, [24, 25]⟩, ⟨.and, [27, 30]⟩, ⟨.and, [32, 34]⟩, ⟨.and, [23, 11]⟩, ⟨.and, [36, 8]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 41]⟩], 45⟩

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

end PEqualNP.Outside.L_drill_rr10_19795

theorem PEqualNP.Outside.L_drill_rr10_19795 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14662300726579244910 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19795.C_, PEqualNP.Outside.L_drill_rr10_19795.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19795.C_ (by decide +kernel), by decide, by decide +kernel⟩
