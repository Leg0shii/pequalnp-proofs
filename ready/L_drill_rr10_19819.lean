import PEqualNP.Defs

namespace PEqualNP.Outside.L_drill_rr10_19819

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 6]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [25, 21]⟩, ⟨.or, [17, 23]⟩, ⟨.or, [5, 27]⟩, ⟨.or, [17, 9]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [20, 22]⟩, ⟨.and, [19, 17]⟩, ⟨.and, [24, 31]⟩, ⟨.and, [16, 26]⟩, ⟨.and, [30, 28]⟩, ⟨.and, [29, 23]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [39, 36]⟩], 40⟩

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

end PEqualNP.Outside.L_drill_rr10_19819

theorem PEqualNP.Outside.L_drill_rr10_19819 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10543322878649664930 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_drill_rr10_19819.C_, PEqualNP.Outside.L_drill_rr10_19819.monoTwoB_sound PEqualNP.Outside.L_drill_rr10_19819.C_ (by decide +kernel), by decide, by decide +kernel⟩
