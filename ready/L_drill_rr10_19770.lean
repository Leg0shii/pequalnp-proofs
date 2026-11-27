import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19770

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 0]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [20, 17]⟩, ⟨.or, [22, 9]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [25, 11]⟩, ⟨.or, [7, 26]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [23, 7]⟩, ⟨.or, [29, 24]⟩, ⟨.and, [25, 19]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [32, 31]⟩, ⟨.or, [6, 28]⟩, ⟨.and, [33, 27]⟩, ⟨.or, [30, 10]⟩, ⟨.or, [28, 29]⟩, ⟨.and, [36, 34]⟩, ⟨.or, [16, 37]⟩, ⟨.or, [38, 18]⟩, ⟨.and, [39, 40]⟩, ⟨.or, [35, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19770

theorem PEqualNP.Outside.L_drill_rr10_19770 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19770.C_, PEqualNP.Outside.L_drill_rr10_19770.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19770.C_ (by decide +kernel), by decide, by decide +kernel⟩
