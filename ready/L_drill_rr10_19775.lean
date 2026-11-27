import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19775

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 7]⟩, ⟨.and, [14, 1]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [1, 18]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [22, 10]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [26, 21]⟩, ⟨.or, [5, 21]⟩, ⟨.and, [24, 29]⟩, ⟨.or, [19, 15]⟩, ⟨.or, [25, 18]⟩, ⟨.or, [20, 4]⟩, ⟨.or, [26, 31]⟩, ⟨.and, [16, 33]⟩, ⟨.and, [27, 34]⟩, ⟨.and, [23, 32]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [30, 38]⟩, ⟨.or, [28, 39]⟩, ⟨.or, [40, 37]⟩], 41⟩

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

end PEqualNP.Outside.L_drill_rr10_19775

theorem PEqualNP.Outside.L_drill_rr10_19775 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7508647934801106060 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19775.C_, PEqualNP.Outside.L_drill_rr10_19775.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19775.C_ (by decide +kernel), by decide, by decide +kernel⟩
