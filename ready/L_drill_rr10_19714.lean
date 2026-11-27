import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19714

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [0, 26]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [28, 23]⟩, ⟨.or, [25, 3]⟩, ⟨.or, [28, 1]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [32, 18]⟩, ⟨.or, [13, 34]⟩, ⟨.and, [29, 27]⟩, ⟨.and, [24, 31]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [0, 17]⟩, ⟨.and, [30, 35]⟩, ⟨.and, [39, 33]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19714

theorem PEqualNP.Outside.L_drill_rr10_19714 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19714.C_, PEqualNP.Outside.L_drill_rr10_19714.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19714.C_ (by decide +kernel), by decide, by decide +kernel⟩
