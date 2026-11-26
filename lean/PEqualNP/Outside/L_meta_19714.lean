import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19714_aux

def witness : Circuit :=
  ⟨[⟨.or, [13, 15]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [8, 22]⟩, ⟨.or, [23, 16]⟩, ⟨.and, [17, 25]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [23, 3]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [24, 15]⟩, ⟨.or, [29, 18]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [1, 27]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [32, 24]⟩, ⟨.and, [33, 28]⟩, ⟨.or, [34, 36]⟩, ⟨.and, [19, 39]⟩, ⟨.or, [31, 27]⟩, ⟨.and, [30, 41]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [38, 43]⟩, ⟨.or, [44, 40]⟩, ⟨.or, [42, 45]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19714_aux

open PEqualNP.Outside.L_meta_19714_aux in
theorem PEqualNP.Outside.L_meta_19714 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
