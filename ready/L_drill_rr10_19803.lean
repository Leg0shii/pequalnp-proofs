import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19803

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 10]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [20, 27]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [1, 29]⟩, ⟨.or, [13, 30]⟩, ⟨.or, [16, 30]⟩, ⟨.or, [15, 32]⟩, ⟨.or, [17, 27]⟩, ⟨.or, [13, 34]⟩, ⟨.and, [18, 33]⟩, ⟨.and, [23, 31]⟩, ⟨.and, [25, 35]⟩, ⟨.and, [24, 28]⟩, ⟨.and, [26, 22]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 40]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19803

theorem PEqualNP.Outside.L_drill_rr10_19803 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15920575138259738475 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19803.C_, PEqualNP.Outside.L_drill_rr10_19803.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19803.C_ (by decide +kernel), by decide, by decide +kernel⟩
