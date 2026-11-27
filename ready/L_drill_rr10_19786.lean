import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19786

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 9]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [19, 13]⟩, ⟨.or, [20, 15]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [22, 6]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [24, 14]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [28, 11]⟩, ⟨.or, [29, 14]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [31, 15]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [33, 9]⟩, ⟨.or, [18, 2]⟩, ⟨.or, [35, 5]⟩, ⟨.or, [36, 11]⟩, ⟨.and, [21, 37]⟩, ⟨.and, [23, 25]⟩, ⟨.and, [27, 30]⟩, ⟨.and, [32, 34]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19786

theorem PEqualNP.Outside.L_drill_rr10_19786 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770687136455741005 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19786.C_, PEqualNP.Outside.L_drill_rr10_19786.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19786.C_ (by decide +kernel), by decide, by decide +kernel⟩
