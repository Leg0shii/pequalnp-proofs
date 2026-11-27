import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19785

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 7]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [13, 6]⟩, ⟨.and, [16, 11]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [12, 21]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [7, 26]⟩, ⟨.or, [9, 22]⟩, ⟨.or, [26, 27]⟩, ⟨.and, [29, 24]⟩, ⟨.or, [0, 25]⟩, ⟨.or, [19, 9]⟩, ⟨.and, [18, 30]⟩, ⟨.or, [20, 22]⟩, ⟨.and, [35, 28]⟩, ⟨.or, [36, 34]⟩, ⟨.and, [32, 33]⟩, ⟨.or, [37, 23]⟩, ⟨.or, [38, 31]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

end PEqualNP.Outside.L_drill_rr10_19785

theorem PEqualNP.Outside.L_drill_rr10_19785 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12147342212780283915 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19785.C_, PEqualNP.Outside.L_drill_rr10_19785.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19785.C_ (by decide +kernel), by decide, by decide +kernel⟩
