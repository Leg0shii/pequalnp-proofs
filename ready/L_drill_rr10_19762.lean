import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19762

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 10]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [20, 7]⟩, ⟨.or, [17, 7]⟩, ⟨.or, [24, 13]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [28, 4]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [30, 0]⟩, ⟨.or, [31, 13]⟩, ⟨.and, [25, 26]⟩, ⟨.and, [23, 27]⟩, ⟨.and, [21, 29]⟩, ⟨.and, [32, 22]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19762

theorem PEqualNP.Outside.L_drill_rr10_19762 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6099045440807847450 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19762.C_, PEqualNP.Outside.L_drill_rr10_19762.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19762.C_ (by decide +kernel), by decide, by decide +kernel⟩
