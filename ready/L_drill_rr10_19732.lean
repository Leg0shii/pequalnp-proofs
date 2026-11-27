import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19732

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 2]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [19, 8]⟩, ⟨.and, [23, 21]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [24, 5]⟩, ⟨.or, [20, 8]⟩, ⟨.or, [24, 14]⟩, ⟨.or, [5, 18]⟩, ⟨.and, [29, 4]⟩, ⟨.and, [30, 31]⟩, ⟨.and, [22, 25]⟩, ⟨.or, [34, 26]⟩, ⟨.and, [27, 28]⟩, ⟨.or, [32, 35]⟩, ⟨.or, [36, 33]⟩, ⟨.or, [38, 37]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19732

theorem PEqualNP.Outside.L_drill_rr10_19732 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8109965352779728530 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19732.C_, PEqualNP.Outside.L_drill_rr10_19732.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19732.C_ (by decide +kernel), by decide, by decide +kernel⟩
