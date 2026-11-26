import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19718_aux

def witness : Circuit :=
  ⟨[⟨.or, [8, 4]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [20, 12]⟩, ⟨.or, [20, 13]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [22, 8]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [21, 27]⟩, ⟨.or, [1, 25]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [28, 19]⟩, ⟨.or, [32, 23]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [29, 12]⟩, ⟨.and, [24, 17]⟩, ⟨.or, [18, 5]⟩, ⟨.and, [30, 36]⟩, ⟨.and, [38, 35]⟩, ⟨.or, [33, 3]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [34, 26]⟩, ⟨.or, [37, 42]⟩, ⟨.and, [41, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19718_aux

open PEqualNP.Outside.L_meta_19718_aux in
theorem PEqualNP.Outside.L_meta_19718 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
