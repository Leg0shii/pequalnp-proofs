import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19782

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 1]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [21, 18]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [17, 24]⟩, ⟨.or, [1, 26]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [31, 25]⟩, ⟨.and, [25, 4]⟩, ⟨.and, [33, 23]⟩, ⟨.and, [34, 22]⟩, ⟨.and, [27, 32]⟩, ⟨.and, [28, 29]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19782

theorem PEqualNP.Outside.L_drill_rr10_19782 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16823704204436992830 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19782.C_, PEqualNP.Outside.L_drill_rr10_19782.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19782.C_ (by decide +kernel), by decide, by decide +kernel⟩
