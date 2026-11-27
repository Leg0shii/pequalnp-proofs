import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 13]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [20, 2]⟩, ⟨.or, [24, 11]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [19, 3]⟩, ⟨.or, [27, 8]⟩, ⟨.or, [16, 3]⟩, ⟨.or, [29, 11]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [25, 22]⟩, ⟨.and, [21, 32]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [23, 30]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19804

theorem PEqualNP.Outside.L_drill_rr10_19804 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5928307661352831525 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19804.C_, PEqualNP.Outside.L_drill_rr10_19804.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19804.C_ (by decide +kernel), by decide, by decide +kernel⟩
