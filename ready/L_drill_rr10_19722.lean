import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19722

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [24, 11]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [26, 14]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [29, 8]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [31, 14]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [20, 21]⟩, ⟨.and, [25, 27]⟩, ⟨.and, [28, 30]⟩, ⟨.and, [32, 33]⟩, ⟨.and, [22, 23]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19722

theorem PEqualNP.Outside.L_drill_rr10_19722 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2119688362457708970 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19722.C_, PEqualNP.Outside.L_drill_rr10_19722.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19722.C_ (by decide +kernel), by decide, by decide +kernel⟩
