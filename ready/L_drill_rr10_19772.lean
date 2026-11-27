import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19772

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 13]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [19, 10]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [26, 12]⟩, ⟨.or, [19, 2]⟩, ⟨.or, [28, 5]⟩, ⟨.or, [29, 8]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [31, 6]⟩, ⟨.or, [32, 12]⟩, ⟨.and, [20, 33]⟩, ⟨.and, [23, 22]⟩, ⟨.and, [21, 30]⟩, ⟨.and, [25, 27]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19772

theorem PEqualNP.Outside.L_drill_rr10_19772 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5496967495809117315 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19772.C_, PEqualNP.Outside.L_drill_rr10_19772.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19772.C_ (by decide +kernel), by decide, by decide +kernel⟩
