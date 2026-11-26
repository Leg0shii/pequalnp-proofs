import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19738_aux

def witness : Circuit :=
  ⟨[⟨.or, [12, 4]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [23, 10]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [26, 1]⟩, ⟨.or, [11, 28]⟩, ⟨.or, [13, 21]⟩, ⟨.or, [30, 26]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [31, 6]⟩, ⟨.and, [29, 32]⟩, ⟨.or, [1, 25]⟩, ⟨.and, [33, 35]⟩, ⟨.or, [19, 23]⟩, ⟨.and, [5, 11]⟩, ⟨.and, [37, 14]⟩, ⟨.or, [34, 36]⟩, ⟨.or, [6, 24]⟩, ⟨.and, [17, 16]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [18, 27]⟩, ⟨.and, [41, 44]⟩, ⟨.or, [42, 45]⟩, ⟨.or, [39, 46]⟩, ⟨.or, [47, 43]⟩], 48⟩

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

end PEqualNP.Outside.L_meta_19738_aux

open PEqualNP.Outside.L_meta_19738_aux in
theorem PEqualNP.Outside.L_meta_19738 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
