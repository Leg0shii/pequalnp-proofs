import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19808

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 11]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [18, 1]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [13, 24]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [23, 1]⟩, ⟨.or, [24, 21]⟩, ⟨.or, [12, 26]⟩, ⟨.or, [30, 21]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [23, 29]⟩, ⟨.and, [27, 33]⟩, ⟨.and, [25, 2]⟩, ⟨.and, [28, 29]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [34, 37]⟩, ⟨.and, [32, 20]⟩, ⟨.and, [31, 38]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19808

theorem PEqualNP.Outside.L_drill_rr10_19808 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6839968994078334435 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19808.C_, PEqualNP.Outside.L_drill_rr10_19808.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19808.C_ (by decide +kernel), by decide, by decide +kernel⟩
