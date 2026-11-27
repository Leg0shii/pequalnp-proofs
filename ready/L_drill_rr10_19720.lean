import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19720

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 15]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [21, 14]⟩, ⟨.or, [19, 4]⟩, ⟨.or, [23, 10]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [25, 12]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [29, 10]⟩, ⟨.or, [18, 4]⟩, ⟨.or, [31, 14]⟩, ⟨.or, [20, 7]⟩, ⟨.or, [33, 12]⟩, ⟨.and, [22, 24]⟩, ⟨.and, [26, 27]⟩, ⟨.and, [28, 30]⟩, ⟨.and, [32, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

end PEqualNP.Outside.L_drill_rr10_19720

theorem PEqualNP.Outside.L_drill_rr10_19720 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7582498071666593340 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19720.C_, PEqualNP.Outside.L_drill_rr10_19720.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19720.C_ (by decide +kernel), by decide, by decide +kernel⟩
