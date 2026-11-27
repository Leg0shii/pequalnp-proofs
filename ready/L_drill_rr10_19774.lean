import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 3]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [22, 15]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [20, 8]⟩, ⟨.or, [19, 2]⟩, ⟨.or, [26, 7]⟩, ⟨.or, [21, 1]⟩, ⟨.or, [28, 10]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [30, 3]⟩, ⟨.or, [31, 10]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [33, 7]⟩, ⟨.or, [34, 8]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [36, 15]⟩, ⟨.and, [24, 32]⟩, ⟨.and, [35, 37]⟩, ⟨.and, [25, 23]⟩, ⟨.and, [27, 29]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19774

theorem PEqualNP.Outside.L_drill_rr10_19774 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13555826764713151335 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19774.C_, PEqualNP.Outside.L_drill_rr10_19774.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19774.C_ (by decide +kernel), by decide, by decide +kernel⟩
