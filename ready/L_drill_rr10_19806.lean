import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19806

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 14]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [18, 8]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [17, 7]⟩, ⟨.or, [24, 8]⟩, ⟨.or, [16, 6]⟩, ⟨.or, [26, 9]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [28, 3]⟩, ⟨.or, [29, 10]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [31, 7]⟩, ⟨.or, [32, 9]⟩, ⟨.and, [22, 23]⟩, ⟨.and, [25, 27]⟩, ⟨.and, [20, 30]⟩, ⟨.and, [21, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19806

theorem PEqualNP.Outside.L_drill_rr10_19806 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5346231350888391705 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19806.C_, PEqualNP.Outside.L_drill_rr10_19806.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19806.C_ (by decide +kernel), by decide, by decide +kernel⟩
