import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19762_aux

def witness : Circuit :=
  ⟨[⟨.or, [5, 15]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [3, 22]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [25, 9]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [23, 27]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [30, 16]⟩, ⟨.or, [11, 31]⟩, ⟨.or, [33, 31]⟩, ⟨.or, [26, 11]⟩, ⟨.and, [28, 34]⟩, ⟨.and, [35, 32]⟩, ⟨.and, [36, 21]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [29, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_19762_aux

open PEqualNP.Outside.L_meta_19762_aux in
theorem PEqualNP.Outside.L_meta_19762 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
