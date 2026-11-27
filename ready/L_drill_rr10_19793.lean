import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19793

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 4]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [16, 3]⟩, ⟨.or, [21, 18]⟩, ⟨.and, [8, 17]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [21, 25]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [13, 0]⟩, ⟨.and, [29, 23]⟩, ⟨.or, [22, 19]⟩, ⟨.and, [20, 28]⟩, ⟨.or, [24, 32]⟩, ⟨.or, [30, 33]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [35, 11]⟩, ⟨.and, [27, 31]⟩, ⟨.and, [36, 26]⟩, ⟨.or, [34, 37]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19793

theorem PEqualNP.Outside.L_drill_rr10_19793 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4868853174714768465 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19793.C_, PEqualNP.Outside.L_drill_rr10_19793.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19793.C_ (by decide +kernel), by decide, by decide +kernel⟩
