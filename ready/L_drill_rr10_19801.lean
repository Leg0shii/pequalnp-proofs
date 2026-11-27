import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19801

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 14]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [28, 18]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [31, 18]⟩, ⟨.and, [21, 24]⟩, ⟨.and, [16, 26]⟩, ⟨.and, [27, 29]⟩, ⟨.and, [30, 32]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19801

theorem PEqualNP.Outside.L_drill_rr10_19801 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11624384703659074185 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19801.C_, PEqualNP.Outside.L_drill_rr10_19801.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19801.C_ (by decide +kernel), by decide, by decide +kernel⟩
