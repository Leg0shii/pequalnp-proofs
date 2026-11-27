import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 15]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [19, 8]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [24, 20]⟩, ⟨.and, [16, 21]⟩, ⟨.or, [15, 25]⟩, ⟨.or, [28, 7]⟩, ⟨.and, [19, 29]⟩, ⟨.or, [1, 26]⟩, ⟨.or, [24, 25]⟩, ⟨.or, [32, 18]⟩, ⟨.and, [33, 17]⟩, ⟨.and, [32, 23]⟩, ⟨.and, [22, 31]⟩, ⟨.or, [36, 34]⟩, ⟨.or, [37, 27]⟩, ⟨.or, [35, 30]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19716

theorem PEqualNP.Outside.L_drill_rr10_19716 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9599430892109718240 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19716.C_, PEqualNP.Outside.L_drill_rr10_19716.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19716.C_ (by decide +kernel), by decide, by decide +kernel⟩
