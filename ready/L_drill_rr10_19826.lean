import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19826

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 11]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [16, 12]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [16, 3]⟩, ⟨.or, [27, 24]⟩, ⟨.or, [27, 30]⟩, ⟨.or, [29, 2]⟩, ⟨.and, [22, 32]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [8, 19]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [35, 36]⟩, ⟨.or, [37, 34]⟩, ⟨.and, [33, 31]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [39, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19826

theorem PEqualNP.Outside.L_drill_rr10_19826 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17599756575633361695 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19826.C_, PEqualNP.Outside.L_drill_rr10_19826.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19826.C_ (by decide +kernel), by decide, by decide +kernel⟩
