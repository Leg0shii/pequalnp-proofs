import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20675_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 4]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [12, 16]⟩], 17⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (9570336 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20675_aux

theorem PEqualNP.Outside.L_meta_20675 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (9570336 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20675_aux.main
