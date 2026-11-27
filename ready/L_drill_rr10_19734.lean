import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19734

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 13]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [19, 4]⟩, ⟨.or, [23, 10]⟩, ⟨.or, [18, 1]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [27, 10]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [29, 4]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [31, 3]⟩, ⟨.or, [32, 14]⟩, ⟨.and, [33, 20]⟩, ⟨.and, [21, 30]⟩, ⟨.and, [24, 26]⟩, ⟨.and, [22, 28]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19734

theorem PEqualNP.Outside.L_drill_rr10_19734 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6355890012357600705 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19734.C_, PEqualNP.Outside.L_drill_rr10_19734.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19734.C_ (by decide +kernel), by decide, by decide +kernel⟩
