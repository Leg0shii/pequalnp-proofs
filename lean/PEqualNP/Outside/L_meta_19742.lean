import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19742_aux

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [2, 16]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [17, 1]⟩, ⟨.and, [12, 1]⟩, ⟨.or, [2, 20]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [27, 11]⟩, ⟨.or, [18, 26]⟩, ⟨.or, [18, 8]⟩, ⟨.and, [28, 32]⟩, ⟨.or, [22, 21]⟩, ⟨.and, [25, 23]⟩, ⟨.or, [30, 29]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [30, 17]⟩, ⟨.and, [34, 36]⟩, ⟨.and, [38, 31]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_meta_19742_aux

open PEqualNP.Outside.L_meta_19742_aux in
theorem PEqualNP.Outside.L_meta_19742 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
