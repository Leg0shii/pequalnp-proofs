import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19825

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 4]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [21, 26]⟩, ⟨.or, [24, 1]⟩, ⟨.and, [22, 25]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [25, 24]⟩, ⟨.and, [20, 32]⟩, ⟨.or, [16, 27]⟩, ⟨.and, [17, 29]⟩, ⟨.or, [28, 30]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.and, [34, 31]⟩, ⟨.or, [39, 38]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19825

theorem PEqualNP.Outside.L_drill_rr10_19825 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1432153032174414900 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19825.C_, PEqualNP.Outside.L_drill_rr10_19825.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19825.C_ (by decide +kernel), by decide, by decide +kernel⟩
