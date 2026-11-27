import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19824

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 14]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [2, 24]⟩, ⟨.or, [25, 24]⟩, ⟨.and, [27, 23]⟩, ⟨.or, [7, 19]⟩, ⟨.or, [18, 28]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [30, 10]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [34, 26]⟩, ⟨.or, [20, 26]⟩, ⟨.and, [32, 33]⟩, ⟨.and, [36, 31]⟩, ⟨.or, [38, 29]⟩, ⟨.and, [21, 35]⟩, ⟨.or, [37, 40]⟩, ⟨.or, [41, 39]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19824

theorem PEqualNP.Outside.L_drill_rr10_19824 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8347929566805686415 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19824.C_, PEqualNP.Outside.L_drill_rr10_19824.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19824.C_ (by decide +kernel), by decide, by decide +kernel⟩
