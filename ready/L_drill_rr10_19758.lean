import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19758

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 1]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [21, 6]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [15, 0]⟩, ⟨.or, [8, 25]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [18, 6]⟩, ⟨.or, [27, 23]⟩, ⟨.or, [8, 22]⟩, ⟨.and, [20, 31]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [33, 28]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [1, 26]⟩, ⟨.and, [35, 30]⟩, ⟨.or, [37, 32]⟩, ⟨.or, [38, 34]⟩, ⟨.or, [5, 29]⟩, ⟨.and, [36, 40]⟩, ⟨.or, [39, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_drill_rr10_19758

theorem PEqualNP.Outside.L_drill_rr10_19758 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7413361890700106610 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19758.C_, PEqualNP.Outside.L_drill_rr10_19758.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19758.C_ (by decide +kernel), by decide, by decide +kernel⟩
