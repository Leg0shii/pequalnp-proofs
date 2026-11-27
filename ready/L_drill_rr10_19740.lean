import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 7]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [24, 11]⟩, ⟨.and, [19, 18]⟩, ⟨.or, [20, 11]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [21, 28]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [30, 12]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [0, 23]⟩, ⟨.and, [32, 31]⟩, ⟨.or, [25, 5]⟩, ⟨.or, [20, 34]⟩, ⟨.and, [37, 36]⟩, ⟨.or, [35, 38]⟩, ⟨.or, [33, 12]⟩, ⟨.and, [40, 29]⟩, ⟨.or, [26, 41]⟩, ⟨.or, [39, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19740

theorem PEqualNP.Outside.L_drill_rr10_19740 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15272338331126939085 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19740.C_, PEqualNP.Outside.L_drill_rr10_19740.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19740.C_ (by decide +kernel), by decide, by decide +kernel⟩
