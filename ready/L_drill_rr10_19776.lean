import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19776

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [24, 15]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [29, 19]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [31, 17]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [34, 11]⟩, ⟨.and, [21, 23]⟩, ⟨.and, [25, 28]⟩, ⟨.and, [30, 32]⟩, ⟨.and, [33, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [41, 39]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19776

theorem PEqualNP.Outside.L_drill_rr10_19776 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17357271221525121870 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19776.C_, PEqualNP.Outside.L_drill_rr10_19776.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19776.C_ (by decide +kernel), by decide, by decide +kernel⟩
