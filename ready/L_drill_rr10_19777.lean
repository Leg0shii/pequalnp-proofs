import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19777

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 6]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [14, 10]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [24, 28]⟩, ⟨.and, [24, 28]⟩, ⟨.and, [27, 29]⟩, ⟨.and, [26, 18]⟩, ⟨.and, [21, 20]⟩, ⟨.and, [25, 23]⟩, ⟨.and, [19, 22]⟩, ⟨.or, [30, 32]⟩, ⟨.or, [35, 33]⟩, ⟨.or, [37, 31]⟩, ⟨.or, [38, 36]⟩, ⟨.or, [34, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19777

theorem PEqualNP.Outside.L_drill_rr10_19777 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14466700110149527140 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19777.C_, PEqualNP.Outside.L_drill_rr10_19777.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19777.C_ (by decide +kernel), by decide, by decide +kernel⟩
