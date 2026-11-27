import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19731

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 13]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [5, 17]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [21, 22]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [25, 16]⟩, ⟨.and, [23, 19]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [25, 2]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [10, 26]⟩, ⟨.and, [28, 29]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [26, 30]⟩, ⟨.or, [32, 30]⟩, ⟨.or, [19, 33]⟩, ⟨.or, [34, 8]⟩, ⟨.and, [36, 37]⟩, ⟨.or, [31, 5]⟩, ⟨.or, [14, 33]⟩, ⟨.or, [35, 40]⟩, ⟨.or, [24, 38]⟩, ⟨.and, [41, 39]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_drill_rr10_19731

theorem PEqualNP.Outside.L_drill_rr10_19731 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19731.C_, PEqualNP.Outside.L_drill_rr10_19731.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19731.C_ (by decide +kernel), by decide, by decide +kernel⟩
