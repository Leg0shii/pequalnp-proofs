import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19798_aux

def witness : Circuit :=
  ⟨[⟨.or, [8, 6]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [2, 23]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [22, 5]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [26, 20]⟩, ⟨.and, [22, 21]⟩, ⟨.or, [27, 26]⟩, ⟨.and, [33, 19]⟩, ⟨.and, [30, 24]⟩, ⟨.and, [26, 32]⟩, ⟨.and, [25, 28]⟩, ⟨.and, [29, 31]⟩, ⟨.or, [36, 38]⟩, ⟨.or, [34, 37]⟩, ⟨.or, [35, 40]⟩, ⟨.or, [39, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_19798_aux

open PEqualNP.Outside.L_meta_19798_aux in
theorem PEqualNP.Outside.L_meta_19798 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
