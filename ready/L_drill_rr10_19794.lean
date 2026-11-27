import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19794

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 12]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [1, 15]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [16, 22]⟩, ⟨.and, [25, 20]⟩, ⟨.or, [23, 8]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [21, 28]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [2, 24]⟩, ⟨.or, [28, 32]⟩, ⟨.and, [31, 14]⟩, ⟨.and, [21, 27]⟩, ⟨.or, [17, 9]⟩, ⟨.or, [29, 26]⟩, ⟨.and, [30, 36]⟩, ⟨.and, [37, 33]⟩, ⟨.or, [31, 14]⟩, ⟨.and, [0, 40]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [39, 34]⟩, ⟨.or, [38, 43]⟩, ⟨.or, [44, 42]⟩], 45⟩

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

end PEqualNP.Outside.L_drill_rr10_19794

theorem PEqualNP.Outside.L_drill_rr10_19794 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15289266858240601290 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19794.C_, PEqualNP.Outside.L_drill_rr10_19794.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19794.C_ (by decide +kernel), by decide, by decide +kernel⟩
