import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19812

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 11]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [13, 22]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [16, 26]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [27, 31]⟩, ⟨.or, [29, 18]⟩, ⟨.or, [21, 15]⟩, ⟨.or, [29, 24]⟩, ⟨.and, [28, 35]⟩, ⟨.or, [24, 15]⟩, ⟨.or, [23, 36]⟩, ⟨.or, [38, 32]⟩, ⟨.and, [30, 34]⟩, ⟨.and, [37, 33]⟩, ⟨.or, [39, 41]⟩, ⟨.or, [42, 40]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19812

theorem PEqualNP.Outside.L_drill_rr10_19812 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16443534311632980495 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19812.C_, PEqualNP.Outside.L_drill_rr10_19812.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19812.C_ (by decide +kernel), by decide, by decide +kernel⟩
