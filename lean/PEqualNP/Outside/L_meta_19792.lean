import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19792_aux

def witness : Circuit :=
  ⟨[⟨.or, [3, 9]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [2, 23]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [13, 22]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [12, 26]⟩, ⟨.or, [15, 14]⟩, ⟨.and, [29, 27]⟩, ⟨.or, [21, 5]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [20, 28]⟩, ⟨.and, [24, 32]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [13, 35]⟩, ⟨.and, [36, 31]⟩, ⟨.and, [1, 28]⟩, ⟨.and, [20, 22]⟩, ⟨.and, [33, 25]⟩, ⟨.or, [34, 39]⟩, ⟨.or, [40, 30]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [44, 38]⟩], 45⟩

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

end PEqualNP.Outside.L_meta_19792_aux

open PEqualNP.Outside.L_meta_19792_aux in
theorem PEqualNP.Outside.L_meta_19792 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
