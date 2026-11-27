import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19818

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 10]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [12, 21]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [19, 15]⟩, ⟨.or, [26, 8]⟩, ⟨.or, [2, 18]⟩, ⟨.or, [28, 11]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [6, 20]⟩, ⟨.or, [29, 22]⟩, ⟨.or, [12, 22]⟩, ⟨.or, [0, 34]⟩, ⟨.or, [2, 32]⟩, ⟨.and, [35, 36]⟩, ⟨.and, [31, 25]⟩, ⟨.and, [33, 23]⟩, ⟨.and, [30, 24]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [41, 39]⟩, ⟨.or, [42, 40]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19818

theorem PEqualNP.Outside.L_drill_rr10_19818 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11949254508291828630 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19818.C_, PEqualNP.Outside.L_drill_rr10_19818.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19818.C_ (by decide +kernel), by decide, by decide +kernel⟩
