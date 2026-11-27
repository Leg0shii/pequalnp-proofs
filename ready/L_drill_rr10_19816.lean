import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19816

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 0]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [19, 1]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [10, 21]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [11, 22]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [28, 10]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [26, 14]⟩, ⟨.or, [32, 0]⟩, ⟨.or, [29, 19]⟩, ⟨.and, [25, 30]⟩, ⟨.or, [8, 23]⟩, ⟨.or, [36, 21]⟩, ⟨.and, [37, 27]⟩, ⟨.and, [34, 33]⟩, ⟨.and, [31, 24]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [35, 38]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19816

theorem PEqualNP.Outside.L_drill_rr10_19816 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12570512712759991245 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19816.C_, PEqualNP.Outside.L_drill_rr10_19816.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19816.C_ (by decide +kernel), by decide, by decide +kernel⟩
