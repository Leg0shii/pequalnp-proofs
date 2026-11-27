import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19798

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 0]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [15, 1]⟩, ⟨.and, [12, 19]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [13, 23]⟩, ⟨.or, [6, 24]⟩, ⟨.or, [19, 12]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [18, 5]⟩, ⟨.or, [27, 13]⟩, ⟨.or, [14, 4]⟩, ⟨.and, [32, 30]⟩, ⟨.and, [28, 26]⟩, ⟨.or, [25, 19]⟩, ⟨.and, [35, 21]⟩, ⟨.and, [31, 29]⟩, ⟨.or, [36, 33]⟩, ⟨.or, [38, 34]⟩, ⟨.or, [37, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19798

theorem PEqualNP.Outside.L_drill_rr10_19798 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (813692034574725510 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19798.C_, PEqualNP.Outside.L_drill_rr10_19798.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19798.C_ (by decide +kernel), by decide, by decide +kernel⟩
