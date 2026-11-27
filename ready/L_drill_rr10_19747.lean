import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19747

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 8]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [26, 5]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [28, 6]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [30, 22]⟩, ⟨.or, [31, 13]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [33, 23]⟩, ⟨.or, [34, 8]⟩, ⟨.and, [20, 16]⟩, ⟨.and, [27, 29]⟩, ⟨.and, [24, 25]⟩, ⟨.and, [32, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19747

theorem PEqualNP.Outside.L_drill_rr10_19747 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14348455746820602255 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19747.C_, PEqualNP.Outside.L_drill_rr10_19747.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19747.C_ (by decide +kernel), by decide, by decide +kernel⟩
