import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20858_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [7, 3]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [4, 2]⟩, ⟨.and, [6, 14]⟩, ⟨.and, [12, 4]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [18, 17]⟩], 19⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27396129 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20858_aux

theorem PEqualNP.Outside.L_meta_20858 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27396129 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20858_aux.main
