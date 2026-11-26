import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20673_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 5]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [12, 10]⟩, ⟨.and, [11, 3]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [15, 14]⟩], 16⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30507008 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20673_aux

theorem PEqualNP.Outside.L_meta_20673 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30507008 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  PEqualNP.Outside.L_meta_20673_aux.main
