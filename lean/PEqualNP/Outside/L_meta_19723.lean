import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19723_aux

def witness : Circuit :=
  ⟨[⟨.or, [4, 1]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [7, 16]⟩, ⟨.and, [14, 19]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [22, 23]⟩, ⟨.or, [7, 24]⟩, ⟨.and, [27, 18]⟩, ⟨.or, [26, 25]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [3, 28]⟩, ⟨.or, [9, 30]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [31, 17]⟩, ⟨.and, [33, 29]⟩, ⟨.or, [27, 10]⟩, ⟨.or, [34, 13]⟩, ⟨.or, [36, 1]⟩, ⟨.or, [20, 35]⟩, ⟨.and, [38, 37]⟩, ⟨.or, [40, 39]⟩], 41⟩

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

end PEqualNP.Outside.L_meta_19723_aux

open PEqualNP.Outside.L_meta_19723_aux in
theorem PEqualNP.Outside.L_meta_19723 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
