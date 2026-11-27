import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19710

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 2]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [23, 16]⟩, ⟨.or, [7, 19]⟩, ⟨.or, [23, 12]⟩, ⟨.or, [19, 12]⟩, ⟨.and, [25, 27]⟩, ⟨.and, [28, 21]⟩, ⟨.and, [17, 26]⟩, ⟨.and, [29, 1]⟩, ⟨.and, [24, 30]⟩, ⟨.or, [31, 32]⟩, ⟨.or, [36, 33]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [38, 35]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19710

theorem PEqualNP.Outside.L_drill_rr10_19710 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4081470838034108865 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19710.C_, PEqualNP.Outside.L_drill_rr10_19710.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19710.C_ (by decide +kernel), by decide, by decide +kernel⟩
