import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19778

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 8]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [22, 11]⟩, ⟨.or, [19, 10]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [25, 11]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [27, 10]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [29, 5]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [31, 9]⟩, ⟨.or, [32, 13]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [34, 20]⟩, ⟨.or, [35, 15]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [33, 21]⟩, ⟨.and, [23, 36]⟩, ⟨.and, [24, 30]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19778

theorem PEqualNP.Outside.L_drill_rr10_19778 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14714778660030304590 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19778.C_, PEqualNP.Outside.L_drill_rr10_19778.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19778.C_ (by decide +kernel), by decide, by decide +kernel⟩
