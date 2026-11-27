import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19796

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 14]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [25, 11]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [28, 9]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [30, 5]⟩, ⟨.or, [31, 10]⟩, ⟨.and, [29, 21]⟩, ⟨.and, [24, 26]⟩, ⟨.and, [27, 23]⟩, ⟨.and, [22, 32]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19796

theorem PEqualNP.Outside.L_drill_rr10_19796 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9928239608072734260 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19796.C_, PEqualNP.Outside.L_drill_rr10_19796.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19796.C_ (by decide +kernel), by decide, by decide +kernel⟩
