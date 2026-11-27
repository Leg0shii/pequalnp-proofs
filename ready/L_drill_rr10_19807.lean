import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19807

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 15]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [1, 25]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [20, 28]⟩, ⟨.or, [30, 29]⟩, ⟨.and, [28, 26]⟩, ⟨.and, [29, 24]⟩, ⟨.and, [31, 22]⟩, ⟨.and, [17, 27]⟩, ⟨.and, [32, 19]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [40, 36]⟩, ⟨.or, [41, 37]⟩, ⟨.or, [42, 38]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19807

theorem PEqualNP.Outside.L_drill_rr10_19807 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10644482476643535765 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19807.C_, PEqualNP.Outside.L_drill_rr10_19807.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19807.C_ (by decide +kernel), by decide, by decide +kernel⟩
