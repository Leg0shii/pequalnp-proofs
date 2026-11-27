import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19738

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 14]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [23, 4]⟩, ⟨.or, [24, 13]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [26, 7]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [28, 7]⟩, ⟨.or, [29, 8]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [31, 1]⟩, ⟨.or, [32, 11]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [34, 0]⟩, ⟨.or, [35, 8]⟩, ⟨.or, [36, 13]⟩, ⟨.and, [7, 9]⟩, ⟨.and, [22, 30]⟩, ⟨.and, [37, 33]⟩, ⟨.and, [25, 27]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19738

theorem PEqualNP.Outside.L_drill_rr10_19738 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8857115674703410590 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19738.C_, PEqualNP.Outside.L_drill_rr10_19738.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19738.C_ (by decide +kernel), by decide, by decide +kernel⟩
