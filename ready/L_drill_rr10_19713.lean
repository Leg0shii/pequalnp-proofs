import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19713

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 14]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [21, 13]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [25, 10]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [23, 9]⟩, ⟨.or, [17, 26]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [20, 5]⟩, ⟨.and, [33, 24]⟩, ⟨.and, [20, 30]⟩, ⟨.and, [34, 10]⟩, ⟨.and, [32, 29]⟩, ⟨.and, [28, 31]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19713

theorem PEqualNP.Outside.L_drill_rr10_19713 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19713.C_, PEqualNP.Outside.L_drill_rr10_19713.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19713.C_ (by decide +kernel), by decide, by decide +kernel⟩
