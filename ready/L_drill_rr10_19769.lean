import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19769

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 8]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [23, 5]⟩, ⟨.or, [18, 5]⟩, ⟨.or, [25, 12]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [27, 15]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [29, 12]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [31, 15]⟩, ⟨.and, [24, 20]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [21, 30]⟩, ⟨.and, [22, 32]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩], 39⟩

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

end PEqualNP.Outside.L_drill_rr10_19769

theorem PEqualNP.Outside.L_drill_rr10_19769 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1910587134026600745 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19769.C_, PEqualNP.Outside.L_drill_rr10_19769.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19769.C_ (by decide +kernel), by decide, by decide +kernel⟩
