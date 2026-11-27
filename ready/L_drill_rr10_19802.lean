import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19802

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 11]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [20, 5]⟩, ⟨.or, [26, 8]⟩, ⟨.or, [5, 30]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [27, 23]⟩, ⟨.or, [19, 6]⟩, ⟨.and, [24, 31]⟩, ⟨.and, [25, 33]⟩, ⟨.and, [0, 21]⟩, ⟨.and, [28, 34]⟩, ⟨.and, [29, 32]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

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

end PEqualNP.Outside.L_drill_rr10_19802

theorem PEqualNP.Outside.L_drill_rr10_19802 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1700870159931663465 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19802.C_, PEqualNP.Outside.L_drill_rr10_19802.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19802.C_ (by decide +kernel), by decide, by decide +kernel⟩
