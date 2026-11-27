import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19735

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 1]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [8, 22]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [19, 26]⟩, ⟨.or, [10, 25]⟩, ⟨.or, [14, 23]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [29, 19]⟩, ⟨.and, [32, 24]⟩, ⟨.or, [28, 35]⟩, ⟨.or, [5, 31]⟩, ⟨.and, [30, 34]⟩, ⟨.and, [27, 36]⟩, ⟨.and, [33, 37]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [41, 40]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19735

theorem PEqualNP.Outside.L_drill_rr10_19735 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19735.C_, PEqualNP.Outside.L_drill_rr10_19735.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19735.C_ (by decide +kernel), by decide, by decide +kernel⟩
