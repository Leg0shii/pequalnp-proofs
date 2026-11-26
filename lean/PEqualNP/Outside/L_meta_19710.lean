import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19710_aux

def witness : Circuit :=
  ⟨[⟨.or, [9, 7]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [21, 19]⟩, ⟨.and, [6, 17]⟩, ⟨.and, [18, 20]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [10, 23]⟩, ⟨.or, [12, 20]⟩, ⟨.or, [25, 3]⟩, ⟨.and, [29, 26]⟩, ⟨.or, [16, 25]⟩, ⟨.and, [27, 6]⟩, ⟨.and, [28, 31]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [27, 19]⟩, ⟨.or, [22, 34]⟩, ⟨.or, [36, 32]⟩, ⟨.or, [24, 0]⟩, ⟨.or, [35, 38]⟩, ⟨.and, [37, 39]⟩, ⟨.or, [33, 30]⟩, ⟨.or, [40, 41]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_19710_aux

open PEqualNP.Outside.L_meta_19710_aux in
theorem PEqualNP.Outside.L_meta_19710 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
