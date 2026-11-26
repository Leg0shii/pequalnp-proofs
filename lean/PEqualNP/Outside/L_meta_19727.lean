import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19727_aux

def witness : Circuit :=
  ⟨[⟨.or, [2, 8]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [1, 22]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [9, 28]⟩, ⟨.or, [29, 17]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [31, 30]⟩, ⟨.and, [32, 19]⟩, ⟨.and, [18, 17]⟩, ⟨.or, [7, 27]⟩, ⟨.and, [31, 27]⟩, ⟨.and, [14, 21]⟩, ⟨.and, [10, 35]⟩, ⟨.or, [4, 20]⟩, ⟨.and, [25, 39]⟩, ⟨.or, [37, 36]⟩, ⟨.and, [24, 15]⟩, ⟨.or, [34, 41]⟩, ⟨.or, [42, 43]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [40, 45]⟩, ⟨.or, [46, 38]⟩], 47⟩

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

end PEqualNP.Outside.L_meta_19727_aux

open PEqualNP.Outside.L_meta_19727_aux in
theorem PEqualNP.Outside.L_meta_19727 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
