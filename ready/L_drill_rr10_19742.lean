import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19742

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 11]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [1, 18]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [18, 2]⟩, ⟨.or, [8, 22]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [2, 19]⟩, ⟨.or, [6, 15]⟩, ⟨.and, [21, 16]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [27, 25]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [30, 23]⟩, ⟨.or, [27, 22]⟩, ⟨.and, [26, 17]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [35, 28]⟩, ⟨.or, [36, 34]⟩, ⟨.or, [24, 26]⟩, ⟨.and, [20, 38]⟩, ⟨.and, [33, 29]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 39]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19742

theorem PEqualNP.Outside.L_drill_rr10_19742 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15581543385461502840 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19742.C_, PEqualNP.Outside.L_drill_rr10_19742.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19742.C_ (by decide +kernel), by decide, by decide +kernel⟩
