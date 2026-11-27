import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19726

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 10]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [29, 20]⟩, ⟨.and, [21, 24]⟩, ⟨.and, [18, 25]⟩, ⟨.and, [19, 20]⟩, ⟨.and, [26, 27]⟩, ⟨.and, [28, 30]⟩, ⟨.or, [31, 32]⟩, ⟨.or, [36, 33]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [38, 35]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19726

theorem PEqualNP.Outside.L_drill_rr10_19726 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3537932711340590220 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19726.C_, PEqualNP.Outside.L_drill_rr10_19726.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19726.C_ (by decide +kernel), by decide, by decide +kernel⟩
