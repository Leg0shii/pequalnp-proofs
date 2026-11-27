import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19764

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 14]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [15, 26]⟩, ⟨.or, [27, 28]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [19, 30]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [17, 32]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [9, 34]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [21, 24]⟩, ⟨.and, [25, 29]⟩, ⟨.and, [31, 33]⟩, ⟨.and, [35, 36]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [41, 39]⟩, ⟨.or, [42, 40]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19764

theorem PEqualNP.Outside.L_drill_rr10_19764 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16472541325419705030 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19764.C_, PEqualNP.Outside.L_drill_rr10_19764.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19764.C_ (by decide +kernel), by decide, by decide +kernel⟩
