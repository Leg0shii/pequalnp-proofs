import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25009_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 14]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [22, 27]⟩, ⟨.or, [22, 26]⟩, ⟨.or, [25, 29]⟩, ⟨.or, [18, 29]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [18, 24]⟩, ⟨.and, [28, 32]⟩, ⟨.and, [17, 26]⟩, ⟨.and, [23, 21]⟩, ⟨.and, [31, 20]⟩, ⟨.and, [33, 30]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25009_aux

theorem PEqualNP.Outside.L_meta_25009 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_25009_aux.main
