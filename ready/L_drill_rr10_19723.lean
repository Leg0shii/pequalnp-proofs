import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19723

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 3]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [9, 21]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [24, 23]⟩, ⟨.or, [24, 25]⟩, ⟨.and, [27, 19]⟩, ⟨.and, [26, 18]⟩, ⟨.and, [29, 22]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [32, 30]⟩, ⟨.and, [28, 33]⟩, ⟨.or, [31, 35]⟩, ⟨.or, [20, 3]⟩, ⟨.and, [37, 10]⟩, ⟨.or, [34, 36]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19723

theorem PEqualNP.Outside.L_drill_rr10_19723 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6992850275190006930 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19723.C_, PEqualNP.Outside.L_drill_rr10_19723.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19723.C_ (by decide +kernel), by decide, by decide +kernel⟩
