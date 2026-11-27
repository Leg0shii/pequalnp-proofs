import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19737

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [8, 23]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [17, 26]⟩, ⟨.and, [29, 18]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [28, 24]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [30, 34]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [33, 25]⟩, ⟨.and, [24, 33]⟩, ⟨.or, [38, 36]⟩, ⟨.and, [37, 35]⟩, ⟨.or, [27, 40]⟩, ⟨.or, [41, 39]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19737

theorem PEqualNP.Outside.L_drill_rr10_19737 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19737.C_, PEqualNP.Outside.L_drill_rr10_19737.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19737.C_ (by decide +kernel), by decide, by decide +kernel⟩
