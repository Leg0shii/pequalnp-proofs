import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19783

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 2]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [19, 1]⟩, ⟨.or, [18, 1]⟩, ⟨.or, [8, 15]⟩, ⟨.and, [24, 18]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [26, 17]⟩, ⟨.and, [29, 20]⟩, ⟨.or, [8, 21]⟩, ⟨.or, [22, 11]⟩, ⟨.or, [27, 30]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [16, 32]⟩, ⟨.and, [34, 31]⟩, ⟨.and, [25, 23]⟩, ⟨.and, [35, 28]⟩, ⟨.or, [38, 33]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [36, 40]⟩], 41⟩

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

end PEqualNP.Outside.L_drill_rr10_19783

theorem PEqualNP.Outside.L_drill_rr10_19783 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8080454460742251720 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19783.C_, PEqualNP.Outside.L_drill_rr10_19783.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19783.C_ (by decide +kernel), by decide, by decide +kernel⟩
