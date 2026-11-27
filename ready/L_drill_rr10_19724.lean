import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19724

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [22, 2]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [16, 6]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [6, 23]⟩, ⟨.and, [26, 25]⟩, ⟨.and, [28, 27]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [1, 19]⟩, ⟨.or, [31, 30]⟩, ⟨.or, [29, 15]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [35, 24]⟩, ⟨.and, [32, 37]⟩, ⟨.or, [38, 34]⟩, ⟨.and, [36, 20]⟩, ⟨.or, [40, 39]⟩], 41⟩

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

end PEqualNP.Outside.L_drill_rr10_19724

theorem PEqualNP.Outside.L_drill_rr10_19724 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7837978282315423185 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19724.C_, PEqualNP.Outside.L_drill_rr10_19724.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19724.C_ (by decide +kernel), by decide, by decide +kernel⟩
