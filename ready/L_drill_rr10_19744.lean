import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19744

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 6]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [20, 15]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [1, 24]⟩, ⟨.or, [16, 0]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [4, 27]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [21, 26]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [8, 23]⟩, ⟨.or, [20, 4]⟩, ⟨.and, [19, 33]⟩, ⟨.and, [22, 31]⟩, ⟨.and, [18, 28]⟩, ⟨.and, [32, 29]⟩, ⟨.and, [34, 30]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19744

theorem PEqualNP.Outside.L_drill_rr10_19744 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14215526027697465180 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19744.C_, PEqualNP.Outside.L_drill_rr10_19744.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19744.C_ (by decide +kernel), by decide, by decide +kernel⟩
