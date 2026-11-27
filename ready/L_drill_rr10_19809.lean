import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19809

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [22, 4]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [24, 28]⟩, ⟨.or, [23, 6]⟩, ⟨.or, [4, 27]⟩, ⟨.and, [25, 26]⟩, ⟨.or, [30, 16]⟩, ⟨.or, [23, 21]⟩, ⟨.and, [31, 34]⟩, ⟨.and, [18, 33]⟩, ⟨.or, [29, 32]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [38, 35]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19809

theorem PEqualNP.Outside.L_drill_rr10_19809 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3630327413337270285 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19809.C_, PEqualNP.Outside.L_drill_rr10_19809.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19809.C_ (by decide +kernel), by decide, by decide +kernel⟩
