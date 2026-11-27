import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19800

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 1]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [20, 21]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [17, 25]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [26, 5]⟩, ⟨.or, [22, 29]⟩, ⟨.or, [18, 29]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [31, 30]⟩, ⟨.or, [31, 13]⟩, ⟨.or, [11, 32]⟩, ⟨.and, [34, 24]⟩, ⟨.and, [36, 27]⟩, ⟨.or, [17, 32]⟩, ⟨.and, [28, 35]⟩, ⟨.or, [39, 16]⟩, ⟨.or, [24, 41]⟩, ⟨.and, [42, 33]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 45]⟩], 46⟩

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

end PEqualNP.Outside.L_drill_rr10_19800

theorem PEqualNP.Outside.L_drill_rr10_19800 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4317929078742808305 : ℕ).testBit (8 * u.val + v.val)) 37 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19800.C_, PEqualNP.Outside.L_drill_rr10_19800.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19800.C_ (by decide +kernel), by decide, by decide +kernel⟩
