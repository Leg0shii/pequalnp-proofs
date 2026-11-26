import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19713_aux

def witness : Circuit :=
  ⟨[⟨.or, [8, 3]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [13, 24]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [22, 1]⟩, ⟨.and, [27, 21]⟩, ⟨.or, [25, 1]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [31, 11]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [4, 28]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [36, 34]⟩, ⟨.and, [33, 18]⟩, ⟨.or, [38, 29]⟩, ⟨.and, [32, 30]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [16, 35]⟩, ⟨.and, [17, 43]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

end PEqualNP.Outside.L_meta_19713_aux

open PEqualNP.Outside.L_meta_19713_aux in
theorem PEqualNP.Outside.L_meta_19713 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
