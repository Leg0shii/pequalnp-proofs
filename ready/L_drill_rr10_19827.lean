import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19827

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 14]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [20, 22]⟩, ⟨.and, [18, 26]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [2, 27]⟩, ⟨.or, [27, 0]⟩, ⟨.and, [28, 30]⟩, ⟨.and, [13, 32]⟩, ⟨.and, [9, 31]⟩, ⟨.and, [25, 16]⟩, ⟨.or, [34, 33]⟩, ⟨.or, [35, 29]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [39, 36]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19827

theorem PEqualNP.Outside.L_drill_rr10_19827 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11710863513312518700 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19827.C_, PEqualNP.Outside.L_drill_rr10_19827.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19827.C_ (by decide +kernel), by decide, by decide +kernel⟩
