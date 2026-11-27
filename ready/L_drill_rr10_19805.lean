import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19805

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 11]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [27, 22]⟩, ⟨.or, [12, 27]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [22, 32]⟩, ⟨.and, [4, 30]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [35, 25]⟩, ⟨.or, [23, 0]⟩, ⟨.and, [31, 24]⟩, ⟨.and, [33, 36]⟩, ⟨.and, [37, 29]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [34, 39]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19805

theorem PEqualNP.Outside.L_drill_rr10_19805 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7871934643211302605 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19805.C_, PEqualNP.Outside.L_drill_rr10_19805.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19805.C_ (by decide +kernel), by decide, by decide +kernel⟩
