import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19741

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 9]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [23, 15]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [25, 15]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [27, 13]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [29, 0]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [31, 5]⟩, ⟨.and, [24, 20]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [30, 21]⟩, ⟨.and, [32, 22]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19741

theorem PEqualNP.Outside.L_drill_rr10_19741 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11683908189968026665 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19741.C_, PEqualNP.Outside.L_drill_rr10_19741.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19741.C_ (by decide +kernel), by decide, by decide +kernel⟩
