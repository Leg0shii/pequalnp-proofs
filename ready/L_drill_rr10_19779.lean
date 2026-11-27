import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19779

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 15]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [24, 15]⟩, ⟨.or, [25, 21]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [28, 17]⟩, ⟨.or, [29, 21]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [31, 19]⟩, ⟨.or, [32, 20]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [34, 13]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [36, 19]⟩, ⟨.and, [22, 23]⟩, ⟨.and, [26, 27]⟩, ⟨.and, [30, 33]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19779

theorem PEqualNP.Outside.L_drill_rr10_19779 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17455334905265877990 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19779.C_, PEqualNP.Outside.L_drill_rr10_19779.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19779.C_ (by decide +kernel), by decide, by decide +kernel⟩
