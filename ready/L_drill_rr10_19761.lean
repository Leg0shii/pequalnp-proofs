import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19761

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 12]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [22, 15]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [24, 11]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [18, 6]⟩, ⟨.or, [27, 14]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [29, 6]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [31, 11]⟩, ⟨.or, [20, 0]⟩, ⟨.or, [33, 3]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [35, 18]⟩, ⟨.and, [30, 26]⟩, ⟨.and, [28, 32]⟩, ⟨.and, [36, 23]⟩, ⟨.and, [34, 21]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19761

theorem PEqualNP.Outside.L_drill_rr10_19761 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12848437582187957865 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19761.C_, PEqualNP.Outside.L_drill_rr10_19761.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19761.C_ (by decide +kernel), by decide, by decide +kernel⟩
