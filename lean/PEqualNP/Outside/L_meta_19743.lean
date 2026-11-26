import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19743_aux

def witness : Circuit :=
  ⟨[⟨.and, [14, 5]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [22, 15]⟩, ⟨.or, [6, 21]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [24, 13]⟩, ⟨.or, [6, 23]⟩, ⟨.or, [19, 22]⟩, ⟨.and, [30, 29]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [28, 17]⟩, ⟨.or, [13, 34]⟩, ⟨.or, [0, 26]⟩, ⟨.or, [0, 25]⟩, ⟨.or, [27, 31]⟩, ⟨.or, [18, 28]⟩, ⟨.and, [33, 39]⟩, ⟨.and, [35, 36]⟩, ⟨.and, [37, 38]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [43, 42]⟩, ⟨.or, [41, 44]⟩], 45⟩

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

end PEqualNP.Outside.L_meta_19743_aux

open PEqualNP.Outside.L_meta_19743_aux in
theorem PEqualNP.Outside.L_meta_19743 : @@STATEMENT@@ := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
