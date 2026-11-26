import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19737_aux

def witness : Circuit :=
  ⟨[⟨.or, [13, 3]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [23, 14]⟩, ⟨.or, [27, 20]⟩, ⟨.and, [28, 24]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [28, 7]⟩, ⟨.or, [4, 25]⟩, ⟨.and, [32, 22]⟩, ⟨.or, [15, 30]⟩, ⟨.and, [18, 15]⟩, ⟨.and, [31, 10]⟩, ⟨.or, [12, 34]⟩, ⟨.or, [0, 37]⟩, ⟨.or, [35, 29]⟩, ⟨.or, [20, 4]⟩, ⟨.or, [36, 33]⟩, ⟨.and, [38, 40]⟩, ⟨.or, [41, 39]⟩, ⟨.and, [19, 26]⟩, ⟨.or, [44, 43]⟩, ⟨.or, [45, 42]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19737_aux

open PEqualNP.Outside.L_meta_19737_aux in
theorem PEqualNP.Outside.L_meta_19737 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
