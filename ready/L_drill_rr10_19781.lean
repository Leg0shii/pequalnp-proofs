import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19781

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 10]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [26, 9]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [32, 21]⟩, ⟨.and, [23, 24]⟩, ⟨.and, [22, 4]⟩, ⟨.and, [25, 27]⟩, ⟨.and, [29, 30]⟩, ⟨.and, [31, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19781

theorem PEqualNP.Outside.L_drill_rr10_19781 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19781.C_, PEqualNP.Outside.L_drill_rr10_19781.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19781.C_ (by decide +kernel), by decide, by decide +kernel⟩
