import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19794_aux

def witness : Circuit :=
  ⟨[⟨.or, [15, 4]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [5, 17]⟩, ⟨.or, [21, 13]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [22, 26]⟩, ⟨.or, [18, 26]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [27, 14]⟩, ⟨.and, [14, 29]⟩, ⟨.and, [31, 25]⟩, ⟨.or, [7, 27]⟩, ⟨.or, [13, 28]⟩, ⟨.and, [24, 36]⟩, ⟨.and, [23, 19]⟩, ⟨.and, [18, 32]⟩, ⟨.and, [30, 35]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [37, 43]⟩, ⟨.or, [44, 38]⟩], 45⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

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

end PEqualNP.Outside.L_meta_19794_aux

open PEqualNP.Outside.L_meta_19794_aux in
theorem PEqualNP.Outside.L_meta_19794 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
