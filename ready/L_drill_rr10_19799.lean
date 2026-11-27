import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19799

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 13]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [25, 20]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [21, 22]⟩, ⟨.and, [24, 26]⟩, ⟨.and, [27, 29]⟩, ⟨.and, [9, 30]⟩, ⟨.and, [31, 32]⟩, ⟨.and, [33, 6]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19799

theorem PEqualNP.Outside.L_drill_rr10_19799 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8660023402198307685 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19799.C_, PEqualNP.Outside.L_drill_rr10_19799.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19799.C_ (by decide +kernel), by decide, by decide +kernel⟩
