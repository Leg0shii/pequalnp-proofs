import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19716_aux

def witness : Circuit :=
  ⟨[⟨.or, [15, 5]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [18, 8]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [24, 18]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [21, 22]⟩, ⟨.or, [14, 2]⟩, ⟨.and, [16, 20]⟩, ⟨.or, [1, 25]⟩, ⟨.or, [28, 7]⟩, ⟨.and, [18, 31]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [33, 19]⟩, ⟨.and, [30, 26]⟩, ⟨.and, [34, 17]⟩, ⟨.and, [33, 23]⟩, ⟨.or, [37, 32]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [27, 29]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [41, 40]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_19716_aux

open PEqualNP.Outside.L_meta_19716_aux in
theorem PEqualNP.Outside.L_meta_19716 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
