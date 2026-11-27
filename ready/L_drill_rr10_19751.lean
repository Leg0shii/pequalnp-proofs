import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19751

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 12]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [1, 18]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [22, 8]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [7, 25]⟩, ⟨.or, [24, 1]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [28, 18]⟩, ⟨.and, [31, 26]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [30, 9]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [29, 36]⟩, ⟨.or, [36, 13]⟩, ⟨.and, [21, 35]⟩, ⟨.or, [39, 32]⟩, ⟨.and, [17, 37]⟩, ⟨.and, [27, 38]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [43, 41]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19751

theorem PEqualNP.Outside.L_drill_rr10_19751 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19751.C_, PEqualNP.Outside.L_drill_rr10_19751.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19751.C_ (by decide +kernel), by decide, by decide +kernel⟩
