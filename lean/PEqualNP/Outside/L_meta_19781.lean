import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19781_aux

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [9, 3]⟩, ⟨.and, [19, 6]⟩, ⟨.and, [14, 7]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [3, 23]⟩, ⟨.or, [19, 10]⟩, ⟨.and, [17, 24]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [1, 20]⟩, ⟨.or, [9, 27]⟩, ⟨.or, [11, 25]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [26, 4]⟩, ⟨.or, [11, 33]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [29, 17]⟩, ⟨.and, [28, 30]⟩, ⟨.and, [36, 34]⟩, ⟨.or, [15, 27]⟩, ⟨.and, [39, 32]⟩, ⟨.or, [38, 37]⟩, ⟨.and, [35, 31]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [40, 42]⟩, ⟨.or, [43, 44]⟩, ⟨.or, [45, 41]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19781_aux

open PEqualNP.Outside.L_meta_19781_aux in
theorem PEqualNP.Outside.L_meta_19781 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
