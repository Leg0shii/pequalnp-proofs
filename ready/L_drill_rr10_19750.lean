import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19750

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 14]⟩, ⟨.and, [13, 6]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [24, 15]⟩, ⟨.or, [6, 25]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [26, 4]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [27, 18]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [26, 22]⟩, ⟨.and, [16, 32]⟩, ⟨.and, [9, 28]⟩, ⟨.and, [23, 29]⟩, ⟨.and, [30, 31]⟩, ⟨.or, [35, 33]⟩, ⟨.or, [34, 37]⟩, ⟨.or, [38, 36]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19750

theorem PEqualNP.Outside.L_drill_rr10_19750 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5360062095110517900 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19750.C_, PEqualNP.Outside.L_drill_rr10_19750.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19750.C_ (by decide +kernel), by decide, by decide +kernel⟩
