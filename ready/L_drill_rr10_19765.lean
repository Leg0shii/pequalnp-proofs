import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19765

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [20, 15]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [22, 19]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [29, 12]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [7, 21]⟩, ⟨.and, [23, 25]⟩, ⟨.and, [27, 28]⟩, ⟨.and, [30, 31]⟩, ⟨.and, [32, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19765

theorem PEqualNP.Outside.L_drill_rr10_19765 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11848986063517868310 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19765.C_, PEqualNP.Outside.L_drill_rr10_19765.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19765.C_ (by decide +kernel), by decide, by decide +kernel⟩
