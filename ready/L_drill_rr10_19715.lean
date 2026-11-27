import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19715

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 13]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [25, 23]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [16, 24]⟩, ⟨.and, [30, 27]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [22, 29]⟩, ⟨.or, [33, 25]⟩, ⟨.or, [32, 31]⟩, ⟨.and, [6, 14]⟩, ⟨.and, [20, 35]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [34, 40]⟩], 41⟩

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

end PEqualNP.Outside.L_drill_rr10_19715

theorem PEqualNP.Outside.L_drill_rr10_19715 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7598353482589123020 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19715.C_, PEqualNP.Outside.L_drill_rr10_19715.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19715.C_ (by decide +kernel), by decide, by decide +kernel⟩
