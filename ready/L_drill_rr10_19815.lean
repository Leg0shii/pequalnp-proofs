import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19815

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 10]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [8, 1]⟩, ⟨.and, [17, 8]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [24, 6]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [23, 18]⟩, ⟨.and, [16, 25]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [21, 29]⟩, ⟨.or, [6, 21]⟩, ⟨.or, [19, 28]⟩, ⟨.or, [30, 22]⟩, ⟨.or, [20, 9]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [35, 33]⟩, ⟨.or, [31, 9]⟩, ⟨.and, [34, 27]⟩, ⟨.and, [37, 26]⟩, ⟨.or, [32, 36]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [39, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19815

theorem PEqualNP.Outside.L_drill_rr10_19815 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10801013263263746985 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19815.C_, PEqualNP.Outside.L_drill_rr10_19815.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19815.C_ (by decide +kernel), by decide, by decide +kernel⟩
