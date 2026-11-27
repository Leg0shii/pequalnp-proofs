import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19754

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 6]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [22, 5]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [23, 18]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [15, 27]⟩, ⟨.or, [27, 16]⟩, ⟨.and, [20, 24]⟩, ⟨.and, [26, 31]⟩, ⟨.or, [30, 25]⟩, ⟨.and, [34, 19]⟩, ⟨.or, [33, 28]⟩, ⟨.or, [36, 35]⟩, ⟨.and, [1, 29]⟩, ⟨.or, [37, 32]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19754

theorem PEqualNP.Outside.L_drill_rr10_19754 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14991291321697978680 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19754.C_, PEqualNP.Outside.L_drill_rr10_19754.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19754.C_ (by decide +kernel), by decide, by decide +kernel⟩
