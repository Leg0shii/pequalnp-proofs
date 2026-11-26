import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19736_aux

def witness : Circuit :=
  ⟨[⟨.or, [12, 2]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [3, 22]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [20, 17]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [24, 8]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [16, 25]⟩, ⟨.or, [12, 22]⟩, ⟨.or, [0, 19]⟩, ⟨.or, [29, 31]⟩, ⟨.or, [27, 11]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [21, 28]⟩, ⟨.or, [34, 32]⟩, ⟨.or, [11, 35]⟩, ⟨.and, [38, 33]⟩, ⟨.or, [30, 35]⟩, ⟨.and, [19, 40]⟩, ⟨.or, [26, 39]⟩, ⟨.or, [41, 36]⟩, ⟨.and, [23, 37]⟩, ⟨.or, [42, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19736_aux

open PEqualNP.Outside.L_meta_19736_aux in
theorem PEqualNP.Outside.L_meta_19736 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
