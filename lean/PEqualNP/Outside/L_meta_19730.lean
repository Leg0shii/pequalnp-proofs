import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19730_aux

def witness : Circuit :=
  ⟨[⟨.or, [13, 6]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [14, 7]⟩, ⟨.and, [14, 20]⟩, ⟨.or, [21, 11]⟩, ⟨.and, [17, 23]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [20, 18]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [16, 26]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [16, 29]⟩, ⟨.or, [24, 5]⟩, ⟨.or, [28, 9]⟩, ⟨.or, [21, 34]⟩, ⟨.or, [33, 29]⟩, ⟨.or, [32, 30]⟩, ⟨.or, [18, 37]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [12, 38]⟩, ⟨.and, [36, 39]⟩, ⟨.and, [40, 35]⟩, ⟨.and, [25, 31]⟩, ⟨.or, [42, 43]⟩, ⟨.or, [41, 44]⟩], 45⟩

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

end PEqualNP.Outside.L_meta_19730_aux

open PEqualNP.Outside.L_meta_19730_aux in
theorem PEqualNP.Outside.L_meta_19730 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
