import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19810

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [18, 1]⟩, ⟨.or, [16, 15]⟩, ⟨.and, [19, 16]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [27, 14]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [26, 30]⟩, ⟨.and, [24, 20]⟩, ⟨.or, [4, 18]⟩, ⟨.and, [30, 29]⟩, ⟨.and, [25, 14]⟩, ⟨.or, [7, 23]⟩, ⟨.or, [9, 36]⟩, ⟨.and, [28, 33]⟩, ⟨.and, [31, 37]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [32, 38]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [42, 41]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19810

theorem PEqualNP.Outside.L_drill_rr10_19810 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10184235645427475370 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19810.C_, PEqualNP.Outside.L_drill_rr10_19810.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19810.C_ (by decide +kernel), by decide, by decide +kernel⟩
