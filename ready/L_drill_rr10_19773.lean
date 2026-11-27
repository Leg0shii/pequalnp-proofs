import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19773

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [23, 4]⟩, ⟨.or, [12, 24]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [23, 20]⟩, ⟨.or, [27, 22]⟩, ⟨.or, [1, 19]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [15, 10]⟩, ⟨.and, [29, 21]⟩, ⟨.or, [30, 10]⟩, ⟨.and, [31, 25]⟩, ⟨.and, [16, 32]⟩, ⟨.and, [26, 17]⟩, ⟨.and, [34, 28]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [33, 39]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [41, 35]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19773

theorem PEqualNP.Outside.L_drill_rr10_19773 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5672340417107567985 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19773.C_, PEqualNP.Outside.L_drill_rr10_19773.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19773.C_ (by decide +kernel), by decide, by decide +kernel⟩
