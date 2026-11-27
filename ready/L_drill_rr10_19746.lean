import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19746

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 8]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [24, 21]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [28, 20]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [30, 20]⟩, ⟨.or, [5, 17]⟩, ⟨.or, [32, 21]⟩, ⟨.and, [16, 19]⟩, ⟨.and, [22, 25]⟩, ⟨.and, [27, 29]⟩, ⟨.and, [31, 33]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19746

theorem PEqualNP.Outside.L_drill_rr10_19746 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2183461428884851875 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19746.C_, PEqualNP.Outside.L_drill_rr10_19746.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19746.C_ (by decide +kernel), by decide, by decide +kernel⟩
