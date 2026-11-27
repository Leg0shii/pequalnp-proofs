import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19811

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 0]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [24, 6]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [24, 22]⟩, ⟨.and, [21, 10]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [23, 1]⟩, ⟨.or, [30, 14]⟩, ⟨.or, [18, 28]⟩, ⟨.or, [21, 26]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [31, 26]⟩, ⟨.or, [20, 32]⟩, ⟨.or, [12, 27]⟩, ⟨.and, [36, 33]⟩, ⟨.or, [17, 34]⟩, ⟨.and, [37, 35]⟩, ⟨.and, [39, 29]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [38, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19811

theorem PEqualNP.Outside.L_drill_rr10_19811 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6799783216241292135 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19811.C_, PEqualNP.Outside.L_drill_rr10_19811.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19811.C_ (by decide +kernel), by decide, by decide +kernel⟩
