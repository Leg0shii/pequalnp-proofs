import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19748

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 11]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [13, 24]⟩, ⟨.and, [23, 21]⟩, ⟨.and, [26, 25]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [29, 31]⟩, ⟨.and, [27, 32]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [34, 22]⟩, ⟨.or, [16, 32]⟩, ⟨.and, [28, 36]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [30, 37]⟩, ⟨.or, [39, 38]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19748

theorem PEqualNP.Outside.L_drill_rr10_19748 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8124800356567354635 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19748.C_, PEqualNP.Outside.L_drill_rr10_19748.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19748.C_ (by decide +kernel), by decide, by decide +kernel⟩
