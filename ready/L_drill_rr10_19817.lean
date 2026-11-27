import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19817

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 5]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [16, 0]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [19, 25]⟩, ⟨.and, [22, 20]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [30, 0]⟩, ⟨.and, [29, 27]⟩, ⟨.and, [24, 31]⟩, ⟨.or, [21, 10]⟩, ⟨.or, [34, 17]⟩, ⟨.or, [35, 7]⟩, ⟨.and, [36, 23]⟩, ⟨.or, [33, 32]⟩, ⟨.or, [38, 37]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19817

theorem PEqualNP.Outside.L_drill_rr10_19817 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10102707875972420115 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19817.C_, PEqualNP.Outside.L_drill_rr10_19817.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19817.C_ (by decide +kernel), by decide, by decide +kernel⟩
