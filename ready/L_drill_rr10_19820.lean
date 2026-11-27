import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19820

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 9]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [18, 4]⟩, ⟨.or, [23, 11]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [20, 3]⟩, ⟨.or, [26, 15]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [28, 15]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [30, 12]⟩, ⟨.or, [19, 3]⟩, ⟨.or, [32, 11]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [22, 24]⟩, ⟨.and, [25, 27]⟩, ⟨.and, [29, 31]⟩, ⟨.and, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

end PEqualNP.Outside.L_drill_rr10_19820

theorem PEqualNP.Outside.L_drill_rr10_19820 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15116961972522724785 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19820.C_, PEqualNP.Outside.L_drill_rr10_19820.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19820.C_ (by decide +kernel), by decide, by decide +kernel⟩
