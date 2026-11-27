import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19792

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 9]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [10, 20]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [4, 25]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [28, 30]⟩, ⟨.or, [22, 24]⟩, ⟨.and, [23, 26]⟩, ⟨.or, [24, 16]⟩, ⟨.and, [27, 33]⟩, ⟨.and, [18, 31]⟩, ⟨.and, [29, 35]⟩, ⟨.or, [1, 21]⟩, ⟨.or, [37, 34]⟩, ⟨.and, [39, 32]⟩, ⟨.or, [38, 41]⟩, ⟨.or, [40, 42]⟩, ⟨.or, [43, 36]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19792

theorem PEqualNP.Outside.L_drill_rr10_19792 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6572913902839198155 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19792.C_, PEqualNP.Outside.L_drill_rr10_19792.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19792.C_ (by decide +kernel), by decide, by decide +kernel⟩
