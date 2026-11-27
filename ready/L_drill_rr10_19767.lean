import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19767

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 10]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [24, 21]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [19, 9]⟩, ⟨.or, [20, 12]⟩, ⟨.or, [19, 12]⟩, ⟨.or, [11, 22]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [20, 27]⟩, ⟨.or, [23, 26]⟩, ⟨.and, [32, 25]⟩, ⟨.and, [29, 31]⟩, ⟨.and, [7, 28]⟩, ⟨.and, [18, 30]⟩, ⟨.and, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19767

theorem PEqualNP.Outside.L_drill_rr10_19767 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19767.C_, PEqualNP.Outside.L_drill_rr10_19767.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19767.C_ (by decide +kernel), by decide, by decide +kernel⟩
