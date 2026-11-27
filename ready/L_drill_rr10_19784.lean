import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19784

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 14]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [22, 26]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [24, 29]⟩, ⟨.or, [18, 29]⟩, ⟨.or, [24, 23]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [28, 32]⟩, ⟨.and, [26, 25]⟩, ⟨.and, [20, 27]⟩, ⟨.and, [31, 21]⟩, ⟨.and, [33, 30]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19784

theorem PEqualNP.Outside.L_drill_rr10_19784 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19784.C_, PEqualNP.Outside.L_drill_rr10_19784.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19784.C_ (by decide +kernel), by decide, by decide +kernel⟩
