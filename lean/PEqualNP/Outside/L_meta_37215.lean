import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37215.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem bRead (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [bRead]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

theorem exeBits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)


end PEqualNP.Outside.L_meta_37215.Model

namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [7, 7, 5, 5, 5, 5].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 50]

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_37215

namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1abc8161e302233800c1a445d2275604eac009871b0c008803e940035c0140012b4a873c009294084c9304a82801628a080000160d24b2000000100417c0ff43fe43be43fd43fc43bc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x230008d41a488c005000000100000068a60000098753b830a8631788c00022e1e4423d04800005f4e8010aa9148014e13002e1629e2113800b40300134b3590ac000e0018800000f15800b949800c00040a84ca9b5216cbcb02d0c41451258009e053700000073f9e8b00000088aa003c03c00003f1902200400640000380015ca5000012c72199f400000a1bd6eaf0014d1e00350010e1200000809c5600092484200000000014000b500000002a00250002c36800000029104480016860861d0d020601b4f800e815002a0000002000d600000000000069a4507c48208e2000007c00ab0000000162ea20cc321305c00685122c6e0000254000033800003a25000b2000011cec8a1b0b95ab60000000004480154000021800990000000271f800008e1c02d2e45018806a9139800889800984000000000d8001f15c0000000ec004d51800f600000000a008000207068100208038080202000000802028040e00008200202018040600010000008028240202008040203010000a02028080402010040203000080e0000002dca521db54a43bb28c87755190e7ca721cf94a43d7294872e5290f5aa521cf94643db28c87365190f6aa321cf542439f298879e5310e7ca421cf944439ea80875e5390abaa7215d94642baa8c853e5390b3ca7214794e42cea9c853e5290a7ca3216d946429b28c85b55190a7aa1214f94c429f29085ae5210a7ca2214f540429f2a6653d54ccb3887995d94732baa8e653e548ca7aa9196b10a32bb28c6575518ca7ea8994f15132ce21a65ac424ca7ea8194f15032e6990655e53906baa720db94a41b6a94833e539073ca720c794e41cea9c833e529075ca520cb94a41d6a94833e519067aa120cf94c419f290833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918db94a31b6a9463b4418c67ea898cf15131ce21a63b4414c67ea818cf15031ea988633e54c867aa990d794f21aea9e43ac42c867ca910cf55221af29c435d53887688310cfd51219e2a243ac42487688290cfd50219e2a043e5210867ca7a04f94b409f28e813d54902bea6a05714d40b7a92816c52502eea2a05d14540cfa9a813c5350338a6a04714d40d7a92813c5250358a4a04b14940dba8a813c5150368a2a04d14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2616f524c2d8a4985dd4530ba28a613e540c27aa8186710c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f55220d6214413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6106b10820bb2884175510827ea9884f153109f2a4213d548436883084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086d10410
  | 1 => 0x1c0000072251e
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x601a9262646a020000704096560a064a5e907a5c363c2a123280008e3ea2a600387c08740e662442760000001c006c9c7e000000000c0000000000442e844e2026541e189852683404004c105086288858a4460000005a0094301600008c488a6ea0223a00782c9e00009a1482720c042010a280010620005000c080020810106040880200400c994a5190f255294643c99495190e8d6294c43a55865310e3661948438b98a5110e2c62540438d1855010f165394642c554e5190b1653546428d9865310a8d6394842a95865210a1e63944428718d5010a346154042c510d51ccb2442546328d987544ca1e63d50328b98b540ca3661d5032c3151320cb0e5394a41c354e529070e5354a418b98a531061e6394841a558e51106a562944418718d501062c6254041c310d52cc72552106318b98b544c61e63d50318b98b540c63661d5031c5151310c70d5310b21c554c418861e63d51218798f540862e62d50218d987540872454484218b98a53d02366194f408798e52d02366194b408798e51d022e6294740c314f525030f5314940c314c525031453d4540c914b51503175314540c514c51503275214540c9148515022e62d53308d98754cc22c62552308d185548c21d6510c30c310d520c31443544308798f54c823661d53208718d548823461552208b594420830d5310820c9109510821e63d53108b98b54c421c63552108b18954842356510410c554c41043255210410
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (5580+((h/62+packedAt s0K4 (5022+(h % 62)*9) 9) % 297)*9) 9
  | 3 => packedAt s0K3 (3388+((h/28+packedAt s0K3 (3192+(h % 28)*7) 7) % 111)*8) 8
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffffffffe07ffffffffffffff87ffff
  | 2 => 0xfc1ffe07e07e07fff8783c1fe0f83e0ffa4e93
  | 3 => 0xffe0fff8007ff81fff803fe0ff003ff07c731c
  | 4 => 0xffffff80001fffffc000ffffc0007f83e0
  | 5 => 0xffff00000000001fffffffff000000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x40002410010000001104821010a0284009425
  | 2 => 0xa94664324aa4ae8e582a151a68d0b42b3a4a92
  | 3 => 0x30caa890d349a2b6aa842748ba4139615c6318
  | 4 => 0xa294d1249a0d34db34ce8210dce590426f03c0
  | 5 => 0xc318e1c71c71c71dc7773b9c1086218c77fc00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0ccccccc0fcccccc0ccccccc0fcccccc0ccccccc0fcccccc0ccccccc0fcccccc0ccccccc0fcccccc0ccccccc0fcccccc0ccccccc0fcccccc0ccccccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37215
namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xe0e5a64000009cc2834ac60d0ea511e26213012a082924694203168401d0050b9f5c0000612287805e010004800010540002c2200d96006807800010c32c31040809ceff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x4b4d1f50a08021c108620016800220700000000009c000252a5c0000002a042561b874a89e589a8d2823097c2a6d002395c0044298200549a895e64240fc8200149dc620000024a22c489d800ad1e800220022000000f2c00158144a81800505189000751c231546b5206800b01aacc6c6e1f25902013390c00000000c380012ae0b62309974004c210ece47900249008d00260f89f3f801142e00118d800198008e0029a3d681905801123a3f13400005b000000a0f95cf62f06878ca401c800a4000c0302c900b800007318000de4f53801287424998d0834cadc002a5580000872a800f01b00000c000500d00000318ac780003a184c004eaa4642038964242d5c800b8b54d9e9424a45a7000002f13964282280c041c64bc00041404083800400008040018140804045c001030241460000084000028180c007800040008040408143000201828002c0000340800000016dca5a1db54b43bb28e877551d0ebca5a1f394b43a729687cd52d0ebca3a1f594743ab28e87d551d0ebaa1a1d794e43af2a0879e5410ebca421d794443aea80875e53d0abaa7a16710f42bb28e857551d0abca7215754e42bb28c85755190abea6a15714d42ce21a85ad4210a7ca9194f55232bb28c6575518cabca91967952328f2a4659d548cab8a9195794a32af28c65d6518caaca3197554632aea84655e540cab8a8195794832e729065ce420cb9a84195794432aea80655e53d06baa7a0e710f41b7296836d52d06bca720d754e41b7294836d52906bea6a0d714d41ce21a83b5411067ca918cf55231b7294636d528c6bca918e7952318f2a4639d548c6b8a918d794a31e7294634e528c79aa518d794631aea84635e540c6b8a818d794831af28863d6510c7ac8218f550431aea80633e54c867aa990d794f21aea9e43cc32c867ca910cf55221af29c435d53887a86310d7d4d21ae29a43cc32487a86290d7d4c21ae29843e521086bca7205754e40ce21c815f53502b8a6a05bd4940b6292817751502e8a2a05794c40aea98819c43102dca4205b54840bb288817551102bca9985715330af296615e51cc2baa7184fd51309e2a2616f524c2d8a4985dd4530ba28a619f544c2bca8985715130ce2a2611c544c39ea4985714930e6292614c524c3aea2985714530ea28a6154514c3b6a0985794c30afa9e415c53c82bca7105754e20e6194413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa610730c820bb288417551082bea7885714f10af29c215d53843a863084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa408750c410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x5836081a000006244e0e00000000767a96469c00006a94887e00260a323e4880305a02520018005c860c4c342c001c00400044909200a410840064000016780038823aa63c222e008a8e562060425e9a1400040000a250627ca06c4a981e9e5400282a0000706e7468006600128c72164c003080000108202810c055000000482007c5005800001d194a51d0f455294743d194951d0e8d6295043a55865410e5661948439398a5110e4c6254043951855010f144354742959875350a566115232c5952518cb155494632c5951518ca56619503287992520ca8d6494832b1586520ca4d6590832b1586420cb0c545083287992510ca1c645403295185500cb0c4354b419398b535064e6215231c3952528c70d5494a31c3951528c64e629503187992520c61e6494431a5592510c6c5629443195596410c6c56290431c5151410c61c645403193189500c70d540cb21c5550318861e64d4d2187993530864e62d4c2195987530874453484219318953902546154e40c310d521031443544409398a54cc25661953308799252cc2566194b308799251cc24e629473087992544c24e629513095986544c30c54d4930c3d50524c30c5414930c5153514c34452d4530c5d50514c3145414530d1d48514c34452145308799353c825661d4f208719153882546154e2093594320830d540c820d10c9510821e64d4f109398b53c421c6454e10931895384255650c410c55503104345520c410
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 63)*7) 7
  | 4 => packedAt s1K4 (5518+((h/62+packedAt s1K4 (5022+(h % 62)*8) 8) % 246)*9) 9
  | 3 => packedAt s1K3 (3388+((h/28+packedAt s1K3 (3192+(h % 28)*7) 7) % 111)*8) 8
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffe07ffffffffffffff87ffff
  | 2 => 0xfc0fc0fe0ffe07fff878383e0f07fe0ffa5273
  | 3 => 0xfff000fff07ff81fff803fc00ff83ff07c639c
  | 4 => 0xffff80001fffffc0000fffc0007f83e0
  | 5 => 0xffffff000000001ffffffffff00000007ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x44100020004000000884042220842420084a5
  | 2 => 0xa92299646528ae8e58321a344546b42d3a5252
  | 3 => 0x30a4aaa8a351a2b6ab042e9089d239a15c6318
  | 4 => 0xa2cb34d14a1d34db35de84212ee710c66f83e0
  | 5 => 0xc30c38e18c61c71dc6673739c0842108777800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaaaa0aaa0faaaaaaaaaa0aaa0faaaaaaaaaa0aaa0faaaaaaaaaa0aaa0faaaaaaaaaa0aaa0faaaaaaaaaa0aaa0faaaaaaaaaa0aaa0faaaaaaaaaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37215
namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 3 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 3 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37215
namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 2 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 2 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37215
namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | 3 => packedAt s4K3 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (17+((h/1+packedAt s4K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc3fffe0ff0ff0f87e1fc3fff0fe0fe0f49f673
  | 1 => 0xfc1c3ff0ff0ff0f8fe1fc383f0ff0ff0b6cb9c
  | 2 => 0xffe03fff000fffff001ffc03ff000fffc70c1f
  | 3 => 0x3ffffff000ffffe00003fffff000f80fe0
  | 5 => 0xffffc000000000fffffffffc00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48400222010010002024048901222222005231
  | 1 => 0x8940446240140110620c4119104a24a212c294
  | 2 => 0x108aa8842aaa88ab1112a822aa04494cc50c0a
  | 3 => 0x32933108a882aacd95422042cc94c044e80d40
  | 5 => 0x231a21ccccccccf6d99b327088188188ffa000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37215
namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | 3 => packedAt s5K3 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s5K3 (17+((h/1+packedAt s5K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc1fc3e1ff0ff0f8fe1fc3f830fe1fe1f5bc673
  | 1 => 0xfe1fffe0ff0ff0f0fe1fc3fff0fe0fe0a4fb9c
  | 2 => 0xffe03fff000fffff001ffc03ff000fffc70c1f
  | 3 => 0x3ffffff000ffffe00003fffff000f80fe0
  | 4 => 0xffffc000000000fffffffffc00000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x5440424641041002602c04990124a24a09c231
  | 1 => 0x84400442001001002204410910442442005294
  | 2 => 0x88aa8882aaa88b51112a822aa084994c60c0a
  | 3 => 0x29933110a882aad995422042cc994084f00d40
  | 4 => 0x311a219ccccccceed99b327088118118ffa000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xeeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0eeeceee0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37215
namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x20004a0184800a83143914d0400fa6a0005800012025b83d06347162843a9401b00009c00201380001e321d41b300241d4160044024808461fbc6549a21508d3107ab890000000000000000011070806085010000406140008e0214000000401ff54007f95001fd54007f15001ff52007f94801fd52007f14801ff42007f90801fd42007f10801fe32007f4c801fc32007fd4405fe51007f54405fc51007fd0405fe41007f50405fc41007fc8405fe21007f48405fc21007fd4003fe50007f54003fc50007fd0003fe40007f50003fc40007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8e4005ff14720007fe8390017fe41c8001fea0e4005ff10720007fe6390017fe31c8001fe98e4005ff0c720027fe4390017fe21c8001fe90e4004ff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff0c32000ffc4190007ee20c8003fd1064001ff0832000fd84190007ff10c8003ff0864001ff04320007feca90002ff6548001bfb2a40009fd9520007fcca90002fe6548001feb2a4000bf59520007f8ca90002fc6548001be32a40009f19520007fec890002ff6448001ff3224000bf99120007fac890002fd6448001fe3224000bf19120007fea890003fe5448001feaa24000ff15120007fec690002ff6348001ff31a4000bf98d20007fac690002fd6348001fe31a4000bf18d20007fea690003fe5348001fea9a4000ff14d20007fe8690003fe4348001fea1a4000ff10d2000dfec490003ff5248001ff2924000fb94920007faa490003ed5248001fe2924000ffd0920007fc8490003fd4248001fe2124000ffcc920007fc6490003ee3248001fe9924000fb4c920007f86490003ff61480017fb0a4003ff98520015fcc290003fd6148007fe30a4002bf18520007fea29000ffe5148001fea8a4003ff14520007fe829000ffe4148001fea0a4003ff10520007fe629000ffe3148001fe98a4003ff0c520007fe429000ffe2148001fe90a4003ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048001fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fd0824001ff04120007feca88002ff6544001ff32a2000bf99510007faca88002fd6544001fe32a2000bf19510007fec888002ff6444001ff3222000bf99110007fac888002fd6444001fe3222000bf19110007fea888003fe5444001feaa22000ff15110007fec488002ff6244001ff3122000bf98910007fac488002fd6244001fe3122000bf18910007fea488003fe5244001fea922000ff14910007fe8488003fe4244001fea122000ff10910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2000fdd0510017fc828800bfd4144005fe20a2002fd10510017fe428800bfe2144005fb10a2002ff48510007ea428800bfc21440037fb022001ffd4110007f6a088007fe5044003fea822001ff1411000ff0a088007ff4044003ff2022001fe9011000ffa8088003f94044003fe2022001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ff9015000ff880a8007fe2054003fe102a001ffc415000ffc20a8007fc1054011ffb2e8000bfd9740007fccba0002fe65d0001feb2e8000bf59740047f8cba0002fc65d00037f3268000ffd5340047fca9a0003be54d0001feaa68000ef55340047f8a9a0023ff62d0001ff3168000bf98b40007fac5a0002fd62d0011fe3168000ffd4b40007fca5a0003fd52d0001fe2968008ffd0b400077e85a0003fe42d0001fea168000ef50b40047f885a0003fe32d0001fe9968000ff0cb40047fec3a001ffe61d00057f30e8000ff58740005fac3a0023fc61d00057e30e8000ffd474003ffca3a0003fd51d000ffe28e8008ffd074003ffc83a001fbe41d0001fea0e8008ff1074003f7883a0003ff21d000fff10e8000ff4874003ff843a0006fd60d0003ffa868001ff9434000ffaa1a0007fc50d0003ff2068001ef9034000ff481a0007fc40d0003de2068001ff8834000ff841a0007ff10d0003ff0868001ff04340007fecaa0002ff6550001bfb2a80009fd9540007fccaa0002fe6550001feb2a8000bf59540007f8caa0002fc6550001be32a80009f1954000dfec8a0003ff5450001ff2a28000ef95140007faa8a0003bd5450001fe2a28000ffd8940005fec4a0003fe6250001feb128000ff18940005f8c4a0003ff5250001ff2928000ff54940007f8a4a0003ff4250001dfa128000ff90940007fa84a0003bd4250001fe2128000ff8c940007fa64a0003fc3250001ffb0a8000bfd8540037fcc2a000afe6150001feb0a8006ff18540015f8c2a0003ff515000dff28a8000ff54540037f8a2a0003ff415000dff20a8006ef90540007fa82a001bfc415000dde20a8000ffc8540037fc42a0003fd215000dfe10a8001bfd814000ffea0a0007fe5050003fea828001ff1414000ffe80a0003fb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ff8814000ff840a0007ff1050003ff0828001fe8414000ff820a0013ff65c80017fb2e4000ff99720005fccb90003fd65c80017eb2e4004ff19720005f8cb90013ff64c80017fb264000ff99320005fcc990003fd64c80017eb264004ff19320005f8c990003ff54c8001ff2a64000ff55320007f8a990013ff63c8001ff31e4000bf98f20007fac790002fd63c8009fe31e4000bf18f20007fea790003fe53c8001fea9e4000ff14f20007fe8790003fe43c8001fea1e4000ff10f2000dfcc590003ff52c8009ff2964000fb94b20007faa590003ed52c8009fe2964000ffd0b20027fc8590003fd42c8009fe2164000ffccb20027fc6590003ee32c8001fe9964000fb4cb20027f86590013ff61c800bff30e4002bf98720007fac390002fd61c8009fe30e4002bf18720007fea390017fe51c8001fea
  | 2 => 0x2106ffca190837fc50c841bff206420dff1032106ffc6190837fc30c841bff1064204ff08321017fe219080bfe10c8405fe0864200ffd9521005feca90803fe65484017f32a4200ff59521005faca90803fc65484017e32a4200ffd9121005fec890803bf64484015fb224200ff99121005fcc890803fd64484017eb224200ff19121005f8c890803bc64484015e3224200ffd5121007fca890803fd5448401fe2a24200ffd8d21005fec690803fe63484017f31a4200ff58d21005fac690803fc63484017e31a4200ffd4d21007fca690803fd5348401fe29a4200ffd0d21007fc8690803fd4348401fe21a4202bfd8921007fea490803fe5248401fea924200ff14921007fe8490803fe4248401f72124200ff50921007da8490803fc4248401ff9924200ff8c921007dc6490803fd3248401f69924200ff0c921015fec29080bff5148405ff28a4202ff54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202ff4c521017f8629080bff2148401fb90a4202ff88521017dc429080bfc2148405f610a4202fd08521007fec090802ff6048419ff3024201bf98121007fac090833fc60484037e302420cff94121067f8a090833fe4048419fe202420cff8c121067f86090833fe2048419fe1024202ffc4121017ee209080bfe1048405fe0824201bf9975005ffec9a8003fe64d40017f326a000ff59350005fac9a802ffc64d4017ffaa6a000ff95350007faa9a802ffc54d4017ffb16a000ff98b50005fcc5a8003fd62d40017eb16a00bff18b5005ffea5a80037f52d4001ff296a000ff54b50006faa5a802ffc52d4001ffa16a000ff90b50007fa85a8003fc42d4001ff196a000ff4cb50007f865a802fff61d4015ff30ea002bf98750007fac3a8002fd61d4017fe30ea002bf1875005ffea3a802bfe51d4001fea8ea00bff14750007fe83a802bfe41d4001fea0ea00aff10750007fe43a802bfe21d4001fe90ea00aff0875000dfac1a8007fe50d4003bf286a001fe9435000ff8a1a80077c50d4003ff206a001ff1035000ffc41a8007fc20d4003ff886a001ff8435000ff421a8007fc10d40037fb2aa000ffd9150005fec8a8003fe6454001feb22a000ff19150005f8c8a8003ff5454001ff2a2a000ff55150007f8a8a8003ff62540017fb12a000ff98950007fac4a8003fc62540017e312a000ffd4950006fea4a8003fe5254001fea92a000df54950007f8a4a8003ff4254001ff212a000ff50950007f884a8003fe3254001fe992a000ff0c950007fec2a8002ff6154013ff30aa002bf98550007fac2a8027fc61540057e30aa000ffd455004ffca2a8003fd5154013fe28aa000ffd055004ffc82a8003fd4154013fe20aa000ffc855004ffc42a8003fd2154013fe10aa001bfd815000ffea0a800
  | 3 => 0xf20aa202ff10551017fc42a880bfc2154401ffb02a200bfd8151087fcc0a8806fe6054401feb02a210ff1815100df8c0a8843fe5054421bf282a210ff14151086f8a0a8843fe4054421fe202a210ff88151087f840a880bff1054405fb882a202ff84151017f820a8823ff65d04017fb2e8200ff99741005fccba0803fd65d04017eb2e8208ff19741005f8cba080afe64d0401ffaa68208ff95341007faa9a0823fc54d0411ffb168200ff98b41005fcc5a0803fd62d04017eb168208ff18b41007fea5a0803fe52d0401fea968200ff14b41047fe85a0803bf42d0401ff2168200ff50b410077a85a0823fc42d0401ff1968200ff4cb41007f865a080afd61d0405ffa8e8202ff94741017faa3a080bfc51d0405ff20e8202ef90741017ec83a080bfc41d0405de20e8202ff88741017f843a0823ff60d041fff3068201bf98341007fac1a0802fd60d0411fe3068201bf1834107ffca1a083ffc50d041fff2068208ff1034107ffc41a083ffc20d0405ff8868202fdc4341017fc21a080bfc10d0401ffb2a8200bfd9541007fccaa0802fe6550401feb2a8200bf59541007f8caa0802fc65504057fb228200ffd5141007fca8a0803fd5450401fe2a28200ffd8941005fec4a0803fe6250401feb128200ff18941005f8c4a0803ff5250401ff2928200ff54941007f8a4a0803ff4250401dfa128200ff90941007fa84a0803bd4250401fe2128200ff8c941007fa64a0803fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd0541007ee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff10a8202ff08541007fec0a0802ff605041dff3028201bf98141007fac0a083bfc60504037e302820eff94141077f8a0a083bfe405041dfe202820eff88141077f840a080bff1050405ff0828202ff04141027fecb90802ff65c8401ff32e4200bf99721007facb90802fd65c8409fe32e4200bf19721027fec990802ff64c8401ff3264200bf99321007fac990802fd64c8409fe3264200bf19321007fea990803fe54c8401feaa64200ff15321027fec790803fe63c84017f31e4200ff58f21005fac790813fc63c84017e31e4200ffd4f21007fca790803fd53c8401fe29e4200ffd0f21007fc8790803fd43c8401fe21e4202bf98b21007fea590813fe52c8401fea964204ff14b21007fe8590813fe42c8401f72164200ff50b21007da8590813fc42c8401ff9964204ff8cb21007dc6590803fd32c8401f69964204ff0cb21015fac39080bff51c8405ff28e4202ff54721017f8a39080bff41c8405ff20e4202ff50721017f8839080bff31c8405ff18e4202ff0c721017fc439080bee21c8405fb10e4202ff08721017d84390813ff60c841bff3064201bf98321007fac190802fd60c8409fe3064201bf183
  | 4 => 0x2ff644c801ff3226400bf99132007fac899002fd644c801fe3226400bf19132007fea899003fe544c801feaa26400ff15132007fea499003ef524c801ff2926400ff54932007f8a499003ec524c801ffa126400fbd0932007fc8499003fd424c801fe2126400fb10932007fc6499003de324c801ffb0a6400bfd85320affcc29900afe614c801feb0a6415ff18532015f8c299057fe514c82bfe28a6415ff905320aff88299057fe214c82bfe10a6400ffd8132005fec099053fe604c8037f3026400ff581320a7f8c099006fc604c829ff2826414ff141320a7fc8099053fc404c829ff1026414ff081320affe2099053fe104c829fe0826404ffd9432005feca19003fe650c8017f3286400ff59432005faca19013fc650c8017e3286404ffd9032005fec819003fe640c8017f3206400ff59032005fac819013fc640c8017e3206400ffd5032007fca819003fd540c801fe2a06400bf98832007fea419013fe520c801fea906404ff14832007fe8419013fe420c801fea106404ff10832027fc6419003ee320c801fe9906400fb4c8320079a6419013ff610c827ff3086402bf98432007fac219002fd610c809fe3086402bf1843209ffca21904ffc510c827ff2086413ff1043209ffc4219013fc210c809ffb006412ff9803200dfcc019003fd600c8017eb006404ff1803200df8c01904bfe500c825fe2806412ff90032097f8801904bfe200c809fe1006413ffc4032097fc201904bfc100c8057f32ea20bffd9351007fcc9a8802fe64d4401feb26a200bf5935105ff8c9a882fff54d4401bfaa6a200ff95351007faa9a88037d54d4417fe2a6a20bffd8b51007fcc5a8802fe62d4401feb16a200bf58b5105ff8c5a882fff52d4401bfa96a200ff94b51007faa5a88037d52d4417fe296a200ffd0b51007fc85a8803fd42d4401fe216a200ff8cb51007fa65a8803fc32d44057eb0ea202ff94751016fca3a880bf651d4405fe28ea202df14751017fc83a880bfc41d4405ff10ea202ff0875105ffec1a8847fe60d44037f306a200ff58351005fac1a882ffc60d44037e306a211ff9435108efca1a882ffc50d4423be286a211ff9035108ff881a8847fe20d4423fe106a202ffc4351017fc21a880bfc10d44057fb2aa200ffd9151005fec8a8803bf64544015fb22a200ff99151007fac8a8803fc64544017e322a200ef1915100578c8a8803ff5454401bfaa2a200ff95151007faa8a88037d5454401fe2a2a200ffd8951005fec4a8803fe6254401feb12a200ff18951005f8c4a8803ff5254401bfa92a200ff94951007faa4a88037d5254401fe292a200ffd0951007fc84a8803fd4254401fe212a200ff8c951007fa64a8803fc32544057fb0aa202ffd4551007eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405f
  | 5 => 0x8d42007f8c6a1002fc6350801ffa9a8400ff94d42007faa6a1003fc5350801ffa1a8400ff90d420077c86a1003fd4350801ffa928400ff94942007faa4a1003fc5250801ffa128400fbd0942007fc84a1003be4250801ffb0a8400bfd85420dffcc2a100afe6150801feb0a841bff18542015f8c2a106ffe5150837fe28a841bff905420dff882a106ffe3150837fe18a841bff885420dff842a1003ff60508017fb02841aff9814200dfcc0a1003fd6050835fe3028401bf181420d7fca0a106bfc5050835ff202841aff101420d7fc60a106bfc3050835ff102841aff081420dffe20a106bfe1050835fe0828404ffd9442005feca21003fe65108017f3288400ff59442005faca21013fc65108017e3288400bf99042007fea821023fe5410801feaa08408ff15042027fec621003fe63108017f3188400ff58c42005fac621013fc6310801ffa988400ff94c42007faa621003fc5310811ffa188400efd0c42007fc8621003fd4310801dea188408ff10c42005fcc421003ff5210809ff2908400ff54842027f8a421023ff4210801dfa108404ff90842007dc8421003fd4210801dea108400fb50842027fec221067fe61108057f3088400ff58442005fac221013fc61108057e3088419ff944420cff8a221067fe4110833df2088408ff104420cf788221067fe3110833fe1888419ff88442027f84221013ff6010831ff3008401bf98042007fac021002fd6010809fe3008401bf180420c7fca021063fc5010831ff2008408ff100420c7fc6021063fc3010831ff1008404ff080420cffe2021063fe1010831fe0808404ffd9632005fecb19003fe658c8017f32c6400df99632004fccb19003fd658c8017eb2c6400df59632004facb19013fc658c8017e32c6404ffd9232005fec919003fe648c8017f3246400ef992320057cc919003fd648c8017eb246400ef592320057ac919013fc648c8017e3246400ffd5232007fca919003fd548c801fe2a46400bf58e32007fea719003fe538c801fea9c6400ff14e32007fe8719003fe438c801fea1c6400ff10e32005fcc519003ff528c801f7a946404ff94a32007faa519013fc528c801f62946400ffd0a32007de8519013fe428c801fea146404ff10a32007d88519003ff328c801f79946404ffd86320bffcc31900afe618c801feb0c6400bf58632027f8c31900afc618c82fff28c6417ff146320bffc831905ffc418c82fff18c6417ff0c6320bffc4319013fc218c809ffb046416ff9823200dfcc119003fd608c8017eb046404ff1823200df8c11905bfe508c82dfe2846416ff902320b7f8811905bfe308c82dfe1846416ff88232027f8411905fff108c82dff0846416ff04232007feca99002ff654c801ff32a6400bf99532007faca99002fd654c801fe32a6400bf19532007fec899
  | 6 => 0x9ffb20a400ff99052005fcc829003fd64148017eb20a404ff1905205ffea829003fe5414801feaa0a40bff15052027fec629003fe63148017f318a400ff58c52005fac629013fc6314817ffa98a400dfd4c52007fca629003fd5314801bea98a40bff14c52005fcc42902fff5214801bfa90a404ff94852007dca429003fd5214801bea90a400fb54852027fec229087fe61148057f308a400ff58452005fac229013fc61148057e308a421ff9445205ff8a229087fe4114843fe208a421ff8c45210ff86229087fe2114809fe108a404ffd8052107fcc029006fe6014801feb00a400bf58052027f8c029006fc6014841ff280a420df9405205ff8a0290837c5014841ff200a420ff10052107fc6029083fc3014841ff100a404ff0805210ffe2029083fe1014841fe080a408ffd9742005fecba1003fe65d08017f32e8400ff59742005facba1023fc65d08017e32e8400ffd53420077ea9a1023fe54d0801feaa68408ff1534200778a9a1023ff63d0801ff31e8400bf98f42007fac7a1002fd63d0811fe31e8400ffd4f42007fca7a1003fd53d0801fe29e8408ffd0f42007fea5a1003fe52d0801fea968400ff14b42047fec3a107ffe61d08057f30e8400ff58742005fac3a1023fc61d08057e30e841fff947420fff8a3a107ffe41d0811fe20e841fff8c7420fff863a107ffe21d083ffe10e8408ffd83420f7fcc1a1006fe60d0801feb068400bf58342047f8c1a1006fc60d083dff286841eff143420f7fc81a1023fc40d083dff186841eff0c3420f7fc41a107bfc20d083fff886841eff843420f7f821a1013ff65908017fb2c8400ff99642005fccb210037e65908013f32c8400ff59642005facb210037d65908013eb2c8404ff19642005f8cb21002fd6490801ffaa48400ff95242007faa921003fc5490809ffb1c8400ff98e42005fcc721003de63908016f31c8400ff58e42005fac721003dd63908016eb1c8404ff18e42007fea721003fe5390801fea9c8400ff14e42007fe8721003bf4390801ff21c8400bf98a42007fea521013fe5290801fea948404ff14a42007fe8521003bf4290801f7a148404ffd86420effcc32100afe6190801feb0c8400bf58642027f8c32100afc619083bff28c841dff146420effc8321077be419083bfe20c841def106420effc6321077fc319083bff10c8404ff08642027fec121073fe60908037f3048400ff58242005fac121013fc60908037e304841cff942420e7f8a121073fe4090839fe204841cff8c2420e7f86121073fe2090809fe104841dffc42420e7fc2121073fc1090801ffb2a8400bfd9542007fccaa1002fe6550801feb2a8400bf59542007f8caa1002fc6550801ffaa28400efd5142007fca8a1003fd5450801fe2a28400ef15142007fec6a1002ff6350801ff31a8400ff5
  | 7 => 0x2a003fd5415001beaa0a800ef55054047fec42a003fe62150017f310a800ff58854005fac42a023fc6215011ffb08a829ff98454015fcc22a003fd61150017eb08a808ff18454015f8c22a0a7fe5115017fe288a829ff9045414f7c822a023fc4115053de208a829ff8845414ff8422a023ff6015051ff300a801bf98054007fac02a002fd6015011fe300a801bf18054147fca02a0a37e5015017fe280a828df14054147fc802a023fc4015051ff100a828ff0805414ffe202a0a3fe1015051fe080a80bffd9352007fcc9a9002fe64d4801feb26a400bf5935205ff8c9a902fff54d4801ff2a6a400df95352007faa9a902ffc54d4801be2a6a40bffd8f52007fcc7a9002fe63d4801feb1ea400bf58f5205ff8c7a902fff53d4817ffb0ea427ff98752015fcc3a9003fd61d48017eb0ea40bff18752015f8c3a909ffe51d4817fe28ea427ff9075213ff883a909ffe31d484ffe18ea427ff8875213ff843a902fff60d484dff306a401bf98352007fac1a9002fd60d4817fe306a401bf18352137fca1a902ffc50d484dff206a426ff10352137fc61a909bfc30d484dff106a426ff0835213ffe21a909bfe10d484dfe086a400bf59652027fec929003fe64948017f324a400ef992520057cc929003fd64948017eb24a400ef592520057ac929013fc6494801ffaa4a400ff95252007faa929003fc5494809ffb1ca400ff98e52005fcc729003de63948016f31ca400ff58e52005fac729003dd63948016eb1ca404ff18e52007fea7290037f5394801ff29ca400bf98a52007fea5290037f5294801f7a94a404ffd865212ffcc32900afe6194801feb0ca400bf58652027f8c32900afc619484bff28ca425ff1465212ffc8329097fc419484bff18ca425ff0c65212ffc4329013fc2194809ffb04a424ff9825200dfcc129003fd60948017eb04a404ff1825200df8c129093fe5094849bf284a424ff14252126f8a129093fe4094849fe204a424ff8c252127f86129093fe2094809fe104a425ffc4252127fc2129093fc1094801ffb22a400bfd9152007fcc8a9003fd6454801fe322a400bf19152007fea8a9003fe5454801bf2a2a400ff55152007f8a8a90037c5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa400bf18d52007fea6a9003fe5354801bf29aa400ff54d52007fea4a9003ef5254801ff292a400df94952007fec2a9002ff6154847ff30aa402bf98552007fac2a908ffc61548057e30aa423ff9455211ff8a2a908ffe4154847fe20aa423ff8c55211ff862a908ffe2154847fe10aa400ffd8152005fec0a908bfe60548037f302a400ff58152117f8c0a9006fc6054845ff282a422ff14152117fc80a908bfc4054845ff182a422ff0c152117fc40a908bfc2054847ff882a422ff84152117f820a9002fe651480
  | 8 => 0x400700800500000200000b02c00100100100000400100301303600201400000e00100600b00500700000300300b01001f00300103e00000500200a00000105400402100901700200100400e00201e00600002600000000c01001200800200000b0360060000030470a101c00000200000000100900300100000500a01101b00b00200000300400000300400200700000200200000002502200300000107800200200d02d00a00200000000000101100000000102600801e00200000200400000201600200000800100000000800000301b02201201300301002200300000400400600000d00100a00100000100400400300000100800000500200400700a00a01200e00b00200000100600000500100700000d00100700a07500500e00000e00702700900200c00100001200901c01800402100000600200100100900300001d00901300101100300400001806f02500900000300d03000001500f00300000b00400100100603900900400204300405100203000000200100000001000200700000200800000e00100300b00000800e00000002500900400500000000c00200000500100400000f00700000000200500300300000300000400100001700005ffec5aa003fe62d50017f316a800ff58b54005fac5aa02ffc62d5017ffb0ea82fff98754015fcc3aa003fd61d50017eb0ea80bff18754015f8c3aa0bffe51d5017fe28ea82fff9075417f7c83aa0bffc41d505fde20ea82fff8875417ff843aa02fff60d505dff306a801bf98354007fac1aa002fd60d5017fe306a801bf18354177fca1aa02ffc50d505dff206a82eff10354177fc41aa0bbfc20d505fff886a82eff84354177f821aa002fd65950017f324a800ffd5254006fea92a003bf54950019faa4a808ffd8a54007fcc52a002fe6295001feb14a800bf58a54047f8c52a023ff619505bff30ca802bf98654007fac32a002fd6195011fe30ca802bf1865416ffca32a0b7fc519505bff20ca808ff1065416ffc432a0b7fc2195011ffb04a82cff9825400dfcc12a003fd60950017eb04a808ff1825400df8c12a0b3fe5095059bf284a82cff14254166f8a12a0b3fe4095011fe204a82cff88254167f8412a0b7ff1095059ff084a82cff04254007fea8aa003bf5455001ff2a2a800df95154007fec4aa002ff6255001ff312a800ff58954007f8c4aa002fc6255001ffb0aa800bfd855415ffcc2aa00afe6155001feb0aa82bff18554015f8c2aa0affe5155057fe28aa82bff9055415ff882aa0affe2155057fe10aa800ffd8154005fec0aa0abfe60550037f302a800ff58154157f8c0aa006fc6055055ff282a82aff14154157fc80aa0abfc4055055ff102a82aff0815415ffe20aa0abfe1055055fe082a800bf99454005fcc82a02fff5415001bfaa0a808ff950540077ca8
  | 9 => 0x4ed6e000da4918000b0400099c000d16b1b5a9a2a4f0830000990000c32551750000a5207b5dce214b4a668825121ee248ad0e54000b0a590000ce40e06e7110e4678db1870d6a6294de0730d686cceb2c4a1f7df6040bf49f742d820b89a2e74d3af0369c3ad8a1c0000ac99686407aa3e719c00412cd4140d18c6a76a9ca0004c22c4a56d50000a6f27262e000c086c9a8a00056b000000000b0c4d1dc23762c07dc5f29da12cd809b062010c321000cba0006e6b02d01c4e20094e000280536ce8000000000b6d6c800024ca6a3ec36c24a000c87000000082513c7655c000b3200074c80385daccb4a9ce604744be8218d883508d45cf95e1a09a29cd69801125f92e5988461e85ba5d623387027a558ddc80d00e02500400d00201000300100300000100000700200200000201a00d00400300900200403200500200301200200002102b02100500700401100000100b00000100400600200100100c00400100000000500100100000000f00100000400500500b00000000000103600700500100100001902c00800000600000000001200000500400000201700701a00801500000000300000500300201300300a00100b00301600102a00800200700800300d00900500300300000500000000202700000402700a02600000000400b01100f00200001a00000500807200100300000100000400000102201200d00100200000000300100300000004000b00701801200005f00000000000502300000200200000200800000d00700200403600100100201400100f00500100002a00000704601101700001200200100001501101700c00000700400000a00100f01300200a00302c00800300000100600b01100602400400000001202100800000c00a00000000100100600400000000100200400101500100500500800c00100300100004901300800400900600d00503200001600b01600100000201b01700500001000900200500200700200202900000002000000900200300001100e00000400100100c00a00100701c00400200700901300200000905c01900300300200100000b00000000000f00702500200f00300202d00100601200300500200600100100101500100002500400600501601c00801900501a00200504101300300400200300800100100000300500000100300200001a02700100300901200200201100302200500500000000300500002101e00001d00400000000401f00804400601401101600a00000300100000000100100001000000201b00500400800004900002b00500c00000b00300300100d01403a00d00200400301500600100100000600500101400500000001d00000000600c00000301a02301200100100000701900500403300000001300200e00000100b01c00a018009014002006000004028000003
  | 10 => 0x50426e48eecb442607894ca9a000038b2c68a785333aa4b466a228d33ec906000001f0a9e0003e4d98705362000000e06d6c00000069300022ac820003cc7919cc4ec00004ccb00005fc00091f44aceedd0067000cc60000000735e44240003a671db74b835610006a4000e84a9c32e000711beab20e0ad665cccdecf2000456000bf50009f454aaa075e54678031f11a9380008f000063e0eb3d273e020e750643b2000ea0906e374303c30000001ae85a9d352a5b43448b0adf0005c207e00000033c70006bb3425a0000158f89a0694000000114afe816606000c060000004e0000cf887d9a8526662d9a793441be0111685d4e88b50f0b4bbec818bcbfa08028fe50ceae405ee0003d659a3c10000002664de000a7c47a1b3b6a14eac87c3713212cf01120002f5dd4bd200014200087629bc705a83ac4ba000000a5ad32cfe5910004780000003f26d837006101416493c84e6e262344200006c65e5b262943cd5809682e49965a51a52261300042a53e17436a5557ca11ee5a000000d750000000001ce00028878a0000000000001d99549d2000346000528358000cf40007ae70a5d8072d7281ea4f45200000040c000000000e9c188eb838e2fce169e300033600019648400000000056a89e000b3cc8ea405482200000000004b3c6e0007e2784da0000c3adb628cbdeb5c33900000000074a7825806a86217a000051cb9e5f06703184cc000a69c566b88cc4983144e480e7041b45e003f1315fa9fe8744fc6481c62167accece1067c61567e3fd37f72c2d74d66c6118d243be1944e22e40ba56616e5a35862a4d2c3ea36830c3fc5c54fa7f812bb56e20aa80002a91ecc36c8aec642f3b10000000008e4702a1861000078e4b08861b669b3e70f48a2129619ec536564de8a8d808484c8108e8933b9882a16965429637e966a511d004e1f914fec22fe000b94ec77a1b700003308fa000db8da20fc87c70ee2ad480006b2c14da691e000000133ae400000028e58a23ea7d4d3cbc8400000000001f300089ce64b1a02e3e600030ee77c225bc05a00f0000e4438000a6b16a3fe3408963806721cc364b1c88c81421562a87a3dc35c0770000ca9046d21387f62b4018eaa3007564cd22c626cfd36600028a02898e922bb234c3e86961f19466d6000000e12b90e24888de90002c695a0c278837b6e0c7860ba59df0292000592978e180dc93261adfe3f92109582c2a0e4233a50004f1b877083e0222c5429800092aa3c4cbce2bca1fbbb677883235e8f49c82a723256e2820464c0000000000000e9600083653212f000000037429e08000000afa000010024000b226426a37709106f4ecace006e872a266ae0de9760b8b8cbce4d53ab8a04b8aa6b160a8d6b000462b6b000a68000000342000e520000c66ee76b00000004a1c0eac5144
  | 11 => 0x95f0000002b0c241fe9e64bcd96000a460006f65000000690000cc5d10714d7000dc90008980004d4124b8bea4a1a7280009b800002a000030b869be0008e2ab84fe0009b25eacacc0b00023814d00047eade7ce07c540c86316dace340009dc77c565538000cb88c80008ae4463c84eaccebfe0eebb07542611080006c2000208000956331b7cc189a4d9c21787958447c0006fc74b550c64d5c8c4720b60150e825d0d0adb20000000001be71c3c5000ae25d2b815c88decc47c000000058e0000008500004c46c7894d5e776bd07d26d01071ba000000a42d08697000102000000000a80721d640004ca1540006f22b2dcfafc213664cc8bee79a660b120949d4b2439c0123d876eb6f17c7362685e96097fab888c06ea568d6256327ca2c0000c50007188b8e14c7f308000000000000e9a14a5be7979b4c584ef5ca7940000700002500001588c6640000e4cad46a0284d9e75cbc8398392e743042ce1cfe62eb409e841e0eb1471423f8488fccd065c06f414998baa1d267a9c7b62c404948e0c6d940d1e611d56bf20920cd658e443f82d48b6a248ba3d4a787f9190a0a3c2d6f45418cba69e14a905273cd30d76e586760002301378acd0c980cfc5dac50bc40006a142737aec0ea9000bb800098c0000000008600002a5dde0000ef594e737cc4ee2beb523f0a0664a9f8a7491c43e921a201aa19526ae7279ce9231add69eb0009202f6ac4c4805645e29c97213cc1a88e5871666178d2bc091624e96e03b578e5cba28fbe8f15c4023a9b9a2acc041ff334e1f61ec10b8519a7e03849d16b66ec0501767a6c38ea8184a125704a86802f1dda760ba8520c2ebdcc2aa4e4333b514b988466a02327000dca33d1b05a126ca22ac67269fa0a266a00c1b79444d9013cd2b00c7c5a6b5071e3bf2cc7e4de6ae146ebc603a1a2d2e807312a085c4740ab4c853a4ec4e8e422964c441f6962e4ea3696a56c2e8000223458e86b9c68d0d849d80b00058f075b4821e0d630a9ec44c91b3ba1b879865680471fcaedd8e901de05c8dacb28b4e7a120dae12a97e57a0ea9fc90a97049ab3843571bc6001e3b7c260022f8638bd6000a62a8e7d00197162f0892931ea7c1e4c68d0b2ed462bcd00ce5a960009196321342ae98a0000005b92111c4b44000000e88000000039dc5c2ca500000008121fa258000000b2ad92dcc30266c00032910e49ca5ec1cebc9e5000d4a0009f000061d8b220ac460a6923a38ab6b717d475a4aa07f000d895b5000000000b0302c3c00064ed8fe20e80cc5ea799c6bf0aa2000602000a54c20ecd2de000e7673a00000032467400042c68f00086acf61823aeb7a576000ad6000cd8df4000801000add32d768b26df24ffca8e7e3a8c9e079000b1e9d8000926000bacc6f000db008a13aae31eac0f55a4500005a
  | 12 => 0x607b8b4ce3961be23ae01417df000000337328d3c2e0a7edba6c4e2e000000b66e56764000000c92e6a7c80000000f30b60009e24284b691a3aa99e8ce000ae50000000001ac2b8b5a00006a7d80007c50000e8608ea277e7de431e383b3530000bd4924000c80d4c30621cdf8af616d0da88d0f87b42a0000c095a400027468e192854e301bf00000088012e000ac00001446fe000000000af44440000003c619e0000f0000000000000270000278e3a00000018a000ecee9e1bb00060c0006789a6d904a583e2a83bb0c952c10bbf71a4af85c6e0c2f34d8d365602e27c4a71dbc23c7bc474425bf6d44b96e551caca65243b492f4322281162da09c39eb924a1bbc000af2ac27c69ae3a75109c2026822d2a066227472628e321a67587beb76132bc28ec8f609094a6d4b8250e1092a10002d93ce1863565526691d394beb6c724e3d2617839a2f27b0394be61486687ffa1e286c340547dd65295c79da55d6aae6152b01d4029318e616e6c69e19176c9344ade793de2621221043b04a4416a32e275f6381c88936948d6007664f3c48686dc017dee9862d81a8a4c1d8534b366e86fa29e60ed22ea61563ff4a02f4805c42bf3448460dcb772bfc7fc2d0cdcd6d57e78925d36303d5cea5817a15ad1a852e1d90cd7ae0598427677aa7308e6446f02dc42e022c3c9c47fd128630440d2884a5b85960e370969fc0d3cab07b0e2d260a554b8edc61d464e2540a0d035627861f42a61d1032928ec89022ef31d9d0612aca00000053cce670fd4263cb8abf892700078f8bea5700085e00070603c0aa65012d000000000e3e618875a16ec9667deb4ac8a6264a6080948a762d1c29f9304ab2a300090041ec6c374dd2e0425c09a3a07a26830e61aba880fe93aecf0000161f8000160b10722000862dcd883950c5232503e0040009522ec000646b3e9123e50005a2ae7b4200026e000d7e0004cf22e486295170de2c12dce36e3ee90ea70dea490198dc819c7900004dcd5489a13e00001a9aa000000000636d8668b6bc4fb87e866000d7014ce4a1f514915933a15eab007d7839606275b647071020c035a53290dec32b88905f0a43bcdaa7039ded736140004e8000c9897a00038692d299e78000404a4469cb58e1edfce60135008000bfbe03b6e4da3da5ac000000890cb60002ea2e60008815fe106ba04e6c7adc72aa4360004963b8000adcc0e7aa59c000de4b72000000ccc00000043be7120fd3aecc99a69172a0be4eb06517e55e08855d9b6908388a000ce242418bb46ac0bc5aa15550c61f78c8a4406a9888a8d600080faff49e000d06000e70a7287bb7f8ea4d05590009aca3082429a1fd5720000005ebbe479e28b2a25de00000050ae8c0000000000007ba00000000096800027e000000a640005d40000ec70ce281e47a8ab2
  | 13 => 0xa14ad274ea8235a51e24443f6be68759ea480009e07ec7f000a1f2000443826c68130e668430009c5bf91b281a4be0005042ee6ca781d71241769734c9a000b7e82c85c0e7d025422040001fcc1600025ed3e7fe0d40d04343b600033b0009e8746c3e63ac7e6e570116c5027e8b4e6344a29ba43ae980008c2335cdaae8b68000000000cd65f48429e700033278758b6c00000000008ca3b9000e7ce259c03231d656474201cbba858ace2fa83a396476c62a5b5ae66661cbe20004379c92607072400004391af00000000058532f236000000b5e0000008440003bd074a7a9f6ce77382460009cf492b6c8773d05f862568925b0000000faaba8e6ebed34c5a00046cd9485bc0ccfa5440b2146b80480000495a760005a700000031c7f400000058321a508695d0e28916883400000008c9142b6000000838982c7483c46878ba6e72e0000005c079b5ec00000003400050680869d23a00070b52e000caa71740e488224390e36000e809e400040a00058ddb47d64f4682320aae000291234e026b487fc8cb6441c136000063e6f4c838c11ce48044e68752518bae310ba4a9434e00035454e802eae1c89cb4f21e2da900000019948cb78cca46406d992a6d45a482516b4062c5e66ce7c23e2a0c360588cffa90a100d5a046860d146a4a61c2bdabd8226c845b0098b068180000001dc126000aee8aaaaa55605e0000009ea0008000007b6d78d8e856becd12bcc624000214180e8d887c7dabc79200097ce940003a271234a73266e48ec024b20f696c32a297974d8b86e589420cc292c000a28b08a84d0480a574d102561da7dadfaa8caf00f22cae1c45c252da8811ca458c19da34ca04f893e3228f200060d000e22000c28690b54c6ba92795c30abe0b0e42a4a6b053a1e6ada0582d68845a09ee4f6c5ceb00ae9474ae3fb202aea4ced8aebad5ad2099400037d0c0a3a0006da348b84cbe000688dbee1aaac88531e699dc491dd747eed827f2b97000000715828000e26a866ba81c7740000009bc0002ba79f64ca5cecbd8ce2ce003f4e5e7b2326c4c000000372000d5200000000000000010a000c9c71a00032c1626aa8069d657c100000aec684c94c66068d7c00092b0c87ea942da787869269a3fa0c40004d243d206382ca2d145821723387a4d84b284005e272468c37c0e241ac0a000410b305e87e604888f1e00620000008a8e3c0006f8e5700060fe6e79900000000038a00086c0003adcc092500e000352dc0b3a0003782c8a6c7963f640800029d42b000de80007666de000afd9f2d381bcc830867488dc000622c960000d200054c0f70
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x77454510005f47454510007b47454510005b47454510007775454510007755454510005f77254510007775254510007755254510007f3705451000df6705451000df47054510087f07054510016f76054510017f36054510087765054510087745054510087f05054510087705054510087f24054510087f2205451000df676d051007ef676d051000cf676d0510005f775d0510005f575d0510015f674d0510017b674d0510006f764d0510007b764d0510006f564d0510007b464d0510005f572d0510007b742d0510007b542d051000df670d051007ff270d0510007f170d051000df470d0510016f760d0510017f360d051007ff050d051007ff240d051007ff220d051000df47648510066f4764851000cf47648510005f77548510005f57548510007b77448510005f67448510005f47448510007b47448510005b47448510005f77348510005f57348510015f77248510017e77248510007e76248510026f66248510026f46248510007e46248510007e64248510007e54248510007e63248510007e53248510007f3704851000df6704851000df47048510067f07048510016f76048510017f36048510067f05048510067f24048510067f23048510067f22048510015fa76d4110056fa76d4110014fa76d411000dfa75d411000f7a75d4110006fb65d41100077b65d4110006f965d41100077865d4110005f974d4110005f972d41100077b52d41100077952d4110015fa71d4110057f271d4110007f171d4110015f871d411000efb61d411000ff361d4110057f251d4110007f151d4110007f341d4110057f041d4110057f221d4110007f121d4110015f87650110036f87650110014f876501100077b7550110005fa7550110005f8755011000778755011000578755011000dfb745011000fbb7450110007bb6450110046fa6450110046f86450110007b86450110007ba5450110007b95450110005fb7250110007bb4250110007b94250110007f37150110015fa7150110015f87150110037f0715011000efb615011000ff36150110037f25150110007f15150110007f34150110037ba4150110037b84150110037f04150110037b04150110037f22150110007f12150110015f8764811001ef87648110014f876481100077b7548110005fa7548110005f87548110007787548110005787548110005fb7448110005f97448110005fb7348110005f9734811000dfb724811000feb7248110007eb6248110026fa6248110026f86248110007e86248110007ea5248110007e95248110007ea3248110007e93248110007f37148110015fa7148110015f8714811001ff0714811000efb614811000ff3614811001ff25148110007f15148110007f3414811001ff0414811001ff23148110007f1314811001ff22148110007f12148110
  | 1 => 0x8910044fe7418910026be7418910004be7418910004fd7418910026bd7418910004bd7418910194fe7318910026de7318910004de7318910004fd7318910026dd7318910004dd7318910024fe7218910026ee721891000cff7118910014fe711891000cfd7118910026f57118910014fc7118910026ef2118910026f6211891018eed2118910014ff701891000cfe7018910014fd7018910026f9701891000cfc7018910026ef2018910026fa2018910186ed201891005cff76d4910004fe76d4910004fd76d491005cfc76d491005e7e65d49100067d65d4910006ef62d4910006ec62d4910015f671d4910005f571d491000df870d4910024ff7694910004fe7694910004fd7694910024fc76949100067f65949100067c6594910005be7494910005bd7494910005de7394910005dd7394910015f67194910005f5719491000dfa7094910005f97094910127785094910004ff7654910004fe7654910004fd7654910004fc76549100067e65549100067d6554910015f67154910005fb705491000df87054910024ff7614910004fe7614910004fd7614910024fc76149100067f651491005e7c6514910006ef6214910026ec6214910015f67114910005f5711491000dfa7014910005f97014910107785014910044ff76d0910004fe76d0910004fd76d0910044fc76d0910046be64d0910006bd64d0910006ef62d0910006ec62d0910015f471d091000dfa70d0910005f970d0910024ff7690910004fe7690910004fd7690910024fc76909100057e75909100057d7590910006bf6490910006bc6490910005de7390910005dd7390910015f67190910005f571909100efb4419091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc7650910006be6450910006bd6450910005f77150910015f4715091000dfa7050910024ff7610910004fe7610910004fd7610910024fc7610910006bf6410910046bc6410910006ef6210910026ec6210910015f67110910005f571109100cfb4411091000dfa7010910005f97010910024ff768c910004fe768c910004fd768c910024fc768c9100057e758c9100057d758c910005be748c910005bd748c910006df638c910006dc638c910026ee628c910006ed628c910015f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910006ee624c910006ed624c910015f6714c91000dfa704c910024ff760c910004fe760c910004fd760c910024fc760c910006ef620c910026ec620c910007cd320c910015f6710c910005f5710c91000dfa700c910005f9700c91000df47654510086f4765451000cf47654510015f7755451001777755451000777655451005ef6655451005ef46554510007746554510007b
  | 2 => 0x7cfd7099110046f97099110046fa40991100057f75591100057c7559110005ef7259110005ec725911007df77159110037b4415911003dfb7059110004ff75591100067f75591100047f755911005cfc75591100067c75591100047c7559110006bf7459110004ff7259110006ef7259110004ef7259110024fc7259110006ec7259110004ec725911007cff7159110006f77159110036be4159110036bc4159110036f44159110074ff7059110006fb70591101bcfe7619110006bd641911005cfe7519110004fd7519110044fe7419110046be7419110024fe7219110004fd721911000cff7119110014fe711911000cfd7119110014fc7119110046bf41191101b6bd4119110014ff701911000cfe7019110014fd7019110046f9701911000cfc7019110046bf4019110046fa40191101aebd401911005cff76d5110004fe76d5110004fd76d511005cfc76d5110006bf64d5110006bc64d5110015f671d5110005f571d511017fb441d511000df870d5110044ff7695110004fe7695110004fd7695110044fc76951100067f65951100067c65951100073f5495110015f4719511000dfa7095110005f97095110167785095110004ff7655110004fe7655110004fd7655110004fc7655110005f77155110015f47155110005fb705511000df87055110044ff7615110004fe7615110004fd7615110044fc76151100067f651511005e7c6515110006bf6415110046bc6415110015f67115110005f5711511014fb4411511000dfa7015110005f9701511014778501511005cfe75d8910004fd75d8910044fe74d8910004fd74d8910194fe73d8910004fd73d891000cff71d891000cfd71d89101a6ef21d89101a6ed21d8910014ff70d8910014fd70d891019eef20d891019eed20d8910064fd7698910006ef6298910065f5719891001df9709891005cfe7598910004fd7598910044fe7498910004fd7498910194fe7398910004fd7398910024fe7298910064fd7198910026f57198910026f6219891006cfd7098910026f97098910026fa20989100057f75589100057c7558910005bf7458910005bc7458910005df7358910005dc735891006df7715891002dfb7058910004ff75589100067f75589100047f755891005cfc75589100067c75589100047c7558910004ff7458910006bf7458910004bf7458910044fc7458910006bc7458910004bc7458910004ff7358910006df7358910004df7358910194fc7358910006dc7358910004dc7358910006ef725891006cff7158910006f77158910064ff7058910006fb705891019cfe76189100057e75189100057d7518910005be7418910005bd7418910005de7318910005dd7318910006ed621891005cfe75189100267e75189100047e7518910004fd75189100267d75189100047d751
  | 3 => 0xd72d45200076d52d4520004ff7654520004fe7654520004fc76545200067f65545200067c6554520005bf7454520005bc74545200076d5254520004fe76d0520004fd76d0520044fc76d05200067f65d05200067c65d0520004ff7650520004fe7650520004fc76505200067f65505200067c6550520004fe76cc520004fd76cc520194fc76cc5200067f65cc5200067c65cc520005ee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c5200067f654c5200067c654c520005bf744c520005bc744c520007cd324c520184fe76c85200067f65c85200067c65c852000df870c852000cfc76485200067f65485200067c6548520005bf7448520005bc7448520006f76148520016f46148520005fb704852000df8704852000dfa76c812000efa76c812000cfa76c81200077b65c81200077865c812000dfa72c812000fea72c812000efb62c812000feb62c8120027ea52c8120007e952c8120027ea32c8120007e932c8120005f971c8120044fe74d9510004fd74d9510024fe72d9510004fd72d951000cff71d951000cfd71d95101e67f51d95101e67d51d9510014ff70d9510014fd70d95101e6f970d95101de7f50d95101de7d50d95101def850d9510084fd76995100067f6599510085f5719951004df9709951008f78509951005cfe7599510044fe7499510004fd7499510024fe7299510004fd7299510084fd719951005ef5719951005ef6519951008cfd709951005ef9709951008e7e509951005e7c5099510005bf7459510005bc7459510005ef7259510005ec725951008df77159510055fb70595100877850595100067f7559510004ff7459510006bf7459510004bf7459510044fc7459510006bc7459510004bc7459510004ff7259510006ef7259510004ef7259510024fc7259510006ec7259510004ec725951008cff7159510006f77159510084ff7059510006fb70595100867e50595100867c5059510086f850595101dcfe76195100067d651951005cfe751951005e7e7519510044fe7419510004fd7419510024fe7219510004fd721951000cff7119510014fe711951000cfd711951005ef57119510014fc711951005e7f511951005ef651195101d67d5119510014ff701951000cfe7019510014fd701951000cfc701951005e7f50195101ce7d501951005cfe75d9110004fd75d9110024fe72d9110004fd72d911000cff71d911000cfd71d91101bef571d91101c6bf41d91101c6bd41d91101c6f441d9110014ff70d9110014fd70d91101bebf40d91101bebd40d9110074fd7699110006bf6499110075f5719911003fb44199110035f9709911005cfe7599110004fd7599110044fe7499110024fe7299110004fd7299110074fd7199110046f5719911003ebe4199110046bc4199110
  | 4 => 0x49200076f655492005eee655492005eec65549200076c65549200076e54549200076c5454920005ef73549200076e53549200076c5354920007eb705492000dee705492000dec7054920117e87054920116ef60549201176f50549201176d5054920117ea1054920124fe76149200067f651492005e7c6514920125ee72149200076d521492000cfe76d092000cfc76d09200067f65d09200067c65d0920006bf64d0920046bc64d092000dfa70d0920005f970d09200c4fe76909200057e75909200057d75909200067f65909200067c6590920005de7390920005dd7390920044ff765092000cfe76509200d4fd765092000cfc76509200067f65509200067c6550920006bf6450920006bc6450920005fb705092000df870509200e4fe76109200067f65109200067c651092000cfe76cc92000cfc76cc9200057e75cc9200057d75cc9200067f65cc9200067c65cc920005be74cc920005bd74cc920006df63cc920196dc63cc92000dfa70cc920005f970cc920094fe768c9200057e758c9200057d758c9200067f658c9200067c658c920005be748c920005bd748c920095ee768c920006ee768c920005ef758c9200076e758c920005ed758c9200076d758c9200056d758c9200076f658c920006ee658c920006ec658c9200076c658c9200066c658c920007ae748c920007ad748c920006ee648c920006ec648c9200a5ed738c920196ee638c920196ec638c92000dee708c92000dec708c920026ef608c9200b7ea108c920194ff764c92000cfe764c9200a4fd764c92000cfc764c9200067f654c9200067c654c920006df634c920006dc634c920005fb704c92000df8704c92000dec764c9200a6ec764c92000cec764c920005ef754c920005ed754c9200076f654c920006ee654c920006ec654c9200076c654c9200066c654c920006ee644c920006ec644c920007cf734c920007cf634c920196ee634c920196ec634c920007cc634c920006cc634c920007cf534c920007cc534c920007cf434c920007cc434c920007eb704c92000dee704c92000dec704c9200a7e8704c9200a6ef604c9200a7cf304c9200a7cd304c9200a7ea104c9200b4fe760c9200067f650c9200067c650c9200b5ee720c920007cd320c920014fe76d85200067f65d85200067c65d852001ef661d852005cfe75d8520004fd75d8520044fe74d8520004fd74d8520194fe73d8520004fd73d852000cfd72d8520014fc72d8520006ee32d8520006ed32d852001ef621d852000cfe70d852000cfc70d852006ef710d85200057f75585200057c75585200067f65585200067c6558520005bf7458520005bc7458520005df7358520005dc735852001ef46158520004fe76d4520004fd76d452005cfc76d45200067f65d452005e7c65d4520005ee72d4520005e
  | 5 => 0x4be7498d20004fd7498d20196bd7498d20004bd7498d20194fe7398d200a4fd7298d20196ed7298d20014fe7198d20004fd7198d20014fc7198d201ecfd7098d20196f97098d200057f7558d200057c7558d200067f6558d200067c6558d201edef7258d20004ff7558d200067f7558d200047f7558d2005cfc7558d200067c7558d200047c7558d20004ff7458d20044fc7458d20006ef7258d20004ff7158d20014fe7158d20014fc7158d200a4ff7058d20006fb7058d200a6fa1058d200b4fe7618d200067f6518d200067c6518d20006dd6318d2005cfe7518d20004fd7518d20044fe7418d20004fd7418d20196de7318d20024fe7218d20196ed7218d20024fc7218d20014fe7118d20004fd7118d20014fc7118d20006de3118d20196dc3118d20024ff7018d20094fd7018d20196df3018d20096dd3018d2005cff76d4d20004fe76d4d20004fd76d4d2005cfc76d4d200067f65d4d2005e7c65d4d20005ee72d4d20005ed72d4d20194ff7694d20004fe7694d20004fd7694d20194fc7694d200067f6594d200067c6594d20005be7494d20005bd7494d200075f5394d20005ee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200067c6554d20194ff7614d20004fe7614d20004fd7614d20194fc7614d200067f6514d2005e7c6514d20005ee7214d20005ed7214d20044ff76d0d20004fe76d0d20004fd76d0d20044fc76d0d200067f65d0d200067c65d0d20006bf64d0d20046bc64d0d20194ff7690d20004fe7690d20004fd7690d20194fc7690d200057e7590d200057d7590d200067f6590d200067c6590d20006df6390d20196dc6390d20005ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d200067c6550d20006bf6450d20006bc6450d20006df6350d20006dc6350d20194ff7610d20004fe7610d20004fd7610d20194fc7610d200067f6510d200067c6510d20005ee7210d20005ed7210d2000cfe76d492000cfc76d49200067f65d492005e7c65d492000dfa70d4920005f970d4920104fe76949201267f65949200067c6594920005be7494920005bd7494920005de7394920005dd7394920105ee7694920006ee7694920115ed75949201276f659492005eee659492005eec65949200076c65949200066c6594920007ae7494920007ad7494920007ce7394920005ed7394920007cd7394920005cd73949200076f53949200076d539492000dee709492000dec7094920026ef60949201276e50949201276c5094920127ea109492005cff765492000cfe7654920114fd765492000cfc76549200067f65549200067c6554920005fb705492000df8705492000dec7654920116ec765492000cec76549200076f755
  | 6 => 0xe41195200067c41195200067e31195200067c31195200067e21195200067c211952005e7f70195201067e70195201067d701952005e7c70195201067f40195201067e40195201067d40195201067c40195201067f30195201067e30195201067d30195201067c30195201067f20195201067e20195201067d20195201067c20195201067f10195201067e10195201067a10195201067d10195201067c10195200067f65d91200067c65d912005cfe75d9120004fd75d9120194fe73d9120004fd73d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120006bc41d9120024ff70d91200e4fd70d91200e6bf40d91200e6bd40d91200e6fa10d91200057e75991200057d75991200067f65991200067c6599120006bf6499120005de7399120005dd73991200d5ed729912005cfe75991200467e75991200047e7599120004fd75991200467d75991200047d7599120044fe7499120194fe7399120046de7399120004de7399120004fd7399120046dd7399120004dd73991200d4fd7299120046ed7299120014fe7199120004fd7199120014fc71991200f4fd7099120046f970991200057f75591200057c75591200067f65591200067c65591200f5ef7259120004ff75591200067f75591200047f755912005cfc75591200067c75591200047c7559120006bf7459120004ff7359120194fc73591200f4ff7259120006ef7259120004ff7159120014fe7159120014fc71591200d4ff7059120006fb70591200d6fa10591200e4fe76191200067f65191200067c6519120006bd641912005cfe7519120004fd7519120046be7419120194fe7319120004fd7319120024fe7219120024fc7219120014fe7119120004fd7119120014fc7119120006be4119120046bc4119120024ff70191200c4fd7019120046bf40191200c6bd401912005cff76d5120004fe76d5120004fd76d512005cfc76d51200067f65d512005e7c65d5120005ee72d5120005ed72d5120044ff7695120004fe7695120004fd7695120044fc76951200067f65951200067c65951200073f5495120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200067c6555120044ff7615120004fe7615120004fd7615120044fc76151200067f651512005e7c6515120005ee7215120005ed72151200067f65d8d200067c65d8d2005cfe75d8d20004fd75d8d20044fe74d8d20004fd74d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d200b6df30d8d200b6fa10d8d200057e7598d200057d7598d200067f6598d200067c6598d20005be7498d20005bd7498d20006df6398d200a5ed7298d2005cfe7598d201967e7598d200047e7598d20004fd7598d201967d7598d200047d7598d20044fe7498d20196be7498d20
  | 7 => 0x4720004fd7654720024fc76547200067e65547200067d6554720005bf7454720005bc74547200076d5254720044ff76d0720024fe76d0720004fd76d0720046be64d0720006bd64d0720004ff7650720004fd7650720024fc7650720006be6450720006bd6450720194ff76cc720024fe76cc720004fd76cc720196de63cc720006dd63cc720025ee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c720024fc764c720005bf744c720005bc744c720006de634c720006dd634c720007cd324c72019cff7648720005bf7448720005bc7448720016f46148720044fe74d9520004fd74d9520194fe73d9520004fd73d9520014fe71d9520004fd71d9520014fc71d95200067e51d95200067c51d9520024ff70d9520124fd70d95201267f50d95201267d50d95201276f72d95200067e61d95200067c61d95201276e20d95201276c20d95201277820d95201277a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95201267f72d95201267d72d95200067f71d95200067e71d95200067d71d95200067c71d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d95201267f70d95201267e70d95201267d70d95201267c70d95201267f40d95201267e40d95201267d40d95201267c40d95201267f30d95201267e30d95201267d30d95201267c30d95201267f20d95201267e20d95201267c20d95201267f10d95201267e10d95201267d10d95201267c10d95200067f6599520115ed729952005cfe75995201047e7599520044fe7499520004fd7499520194fe7399520004fd7399520114fd729952005eed7299520014fe7199520004fd7199520014fc7199520134fd709952005ef97099520136fa1099520135ef72595200067f7559520004ff7459520044fc7459520004ff7359520194fc7359520134ff7259520006ef7259520004ff7159520014fe7159520014fc7159520114ff7059520006fb7059520124fe76195200067d651952005e7e7519520044fe7419520004fd7419520194fe7319520004fd7319520024fe721952005eed7219520024fc7219520014fe7119520004fd7119520014fc71195200067e511952005e7c5119520024ff7019520104fd701952005e7f50195201067d5019520106fa10195201257e76195200067e76195201247e76195201076d72195200067e61195200067c61195201076e20195201076c20195201077820195201077a101952005e7f74195200067e74195200067d741952005e7c741952005e7f73195200067e73195200067d731952005e7c731952005e7f72195201067d72195201066d721952005e7f71195200067e71195200067d711952005e7c71195200067
  | 8 => 0x4fd7614f20024fc7614f2005e7e6514f200067d6514f20196de6314f20006dd6314f20025ee7214f20005ed7214f20044ff76d0f20024fe76d0f20004fd76d0f20006bf64d0f20046bc64d0f20006de63d0f20006dd63d0f20194ff7690f20024fe7690f20004fd7690f20024fc7690f200057e7590f200057d7590f20006be6490f20006bd6490f20025ee7290f20005ed7290f20004ff7650f20004fd7650f20024fc7650f20006bf6450f20006bc6450f20194ff7610f20024fe7610f20004fd7610f20024fc7610f20046be6410f20006bd6410f20196de6310f20006dd6310f20025ee7210f20005ed7210f20114fd76d4b200267f65d4b200267c65d4b2000ded7694b20026ed7694b2000ced7694b2005eee6594b200276e6594b200276d6594b20026ec6594b20027ae7494b20027ad7494b20027ce7394b20005ed7394b20027cd7394b20005cd7394b200076f5394b200076d5394b2000dee7094b20027ea7094b20027e97094b2000dec7094b201276e5094b201276c5094b20134ff7654b200267f6554b200267c6554b200276c5254b20135ef7654b20006ef7654b200276f7554b200276f6554b2005eee6554b2005eec6554b200276c6554b200076e5454b200076c5454b20005ef7354b200076e5354b200076c5354b2000dee7054b2000dec7054b201176f5054b201176d5054b200d4fd76d0b20026bf64d0b20026bc64d0b200f4ff7650b20026bf6450b20026bc6450b200a4fd76ccb200057e75ccb200057d75ccb20005be74ccb20005bd74ccb2000ded768cb20026ed768cb2000ced768cb20025ef758cb200276e758cb20005ed758cb200276d758cb200056d758cb20006ee658cb20026ec658cb20027ae748cb20027ad748cb20006ee648cb20026ec648cb20196ee638cb20027ce638cb20027cd638cb20026ec638cb2000dee708cb20027ea708cb20027e9708cb2000dec708cb201ecff764cb20027cc324cb201edef764cb20006ef764cb20005ef754cb20005ed754cb20006ee654cb20006ec654cb20006ee644cb20006ec644cb20027cf734cb20027cf634cb20196ee634cb20196ec634cb20027cc634cb20006cc634cb20007cf534cb20007cc534cb20007cf434cb20007cc434cb2000dee704cb2000dec704cb200a7cf304cb20014ff7658720005bf7458720005bc7458720026f46158720004ff755872005cfc7558720004ff7458720006bf7458720004bf7458720044fc7458720006bc7458720004bc7458720004ff7358720194fc7358720014fd725872000cfc7258720006ee3258720006ed3258720026f72158720026f42158720066fa2058720066f7105872005cff76d4720024fe76d4720004fd76d472005e7e65d47200067d65d4720025ee72d4720005ed72d47200076d52d4720004ff765
  | 9 => 0xd75d93200267d75d93200047d75d9320194fe73d9320026de73d9320004de73d9320004fd73d9320026dd73d9320004dd73d9320024fe72d9320026ee72d9320014fe71d9320004fd71d9320014fc71d9320006be41d9320006bc41d9320026f970d93200d4fd7699320026bf649932005cfe7599320004fd7599320194fe7399320004fd739932000cfe729932000cfc7299320026be4299320026bc4299320014fe7199320004fd7199320014fc7199320046bf40993200f6bd4099320026bc6459320004ff755932005cfc7559320026bf7459320004ff7359320194fc7359320044ff725932000cfe72593200d4fd725932000cfc7259320026be4259320026bc4259320004ff7159320014fe7159320014fc71593200d6bf40593200d6bd405932005cfe7519320004fd7519320044fe7419320026be7419320194fe7319320004fd7319320024fe7219320026ee7219320014fe7119320004fd7119320014fc7119320006be4119320046bc4119320026f9701932005cff76d5320024fe76d5320004fd76d5320024fc76d5320006be64d5320006bd64d5320025ee72d5320005ed72d5320044ff7695320024fe7695320004fd7695320024fc76953200067e65953200067d65953200073f5495320004ff7655320024fe7655320004fd7655320024fc7655320044ff7615320024fe7615320004fd7615320024fc761532005e7e65153200067d6515320046be6415320006bd6415320025ee7215320005ed72153200057e7598f200057d7598f20005be7498f20005bd7498f20026df6398f2005cfe7598f201967e7598f200047e7598f20004fd7598f201967d7598f200047d7598f20044fe7498f20196be7498f20004be7498f20004fd7498f20196bd7498f20004bd7498f2000cfe7298f20196ee7298f2000cfc7298f20026de3298f20026dc3298f20014fe7198f20004fd7198f20014fc7198f20196df3098f201eedd3098f20026dc6358f20004ff7558f2005cfc7558f20004ff7458f20044fc7458f200a4fd7258f2000cfc7258f20026de3258f20026dc3258f20004ff7158f20014fe7158f20014fc7158f200a6df3058f2005cfe7518f20004fd7518f20044fe7418f20004fd7418f20024fe7218f20026ee7218f20014fe7118f20004fd7118f20014fc7118f20026f97018f2005cff76d4f20024fe76d4f20004fd76d4f200067f65d4f2005e7c65d4f20006de63d4f20006dd63d4f20025ee72d4f20005ed72d4f20194ff7694f20024fe7694f20004fd7694f20024fc7694f200067e6594f200067d6594f20005be7494f20005bd7494f200075f5394f20025ee7294f20005ed7294f20004ff7654f20004fd7654f20024fc7654f200067f6554f200067c6554f20005fb7054f2000df87054f20194ff7614f20024fe7614f20
  | 10 => 0xc940006ec624c940007af424c940004fe760c940004fd760c940024fc760c9400067f650c9400067c650c940005be740c940005bd740c940007cd320c940014fe76d85400067f65d85400067c65d854000dbd74d8540036f661d8540037b641d854005cfe75d8540004fd75d854000cfd74d854007ebd74d854000cbd74d8540014fc74d8540024fe72d8540004fd72d8540006bf42d8540006bd42d8540036be41d8540036f641d8540036bc41d854007ef710d85400057f75585400057c75585400067f65585400067c6558540005ef7258540005ec7258540036f46158540037b44158540004fe76d4540004fd76d454005cfc76d45400067f65d454005e7c65d4540005be74d4540005bd74d45400073d54d4540004ff7654540004fe7654540004fc76545400067f65545400067c6554540005bf7454540005bc74545400073d54545401acfe76d05400067f65d05400067c65d05401adbe74d0540016f661d054000df870d054000cfc76505400067f65505400067c65505401bdbf7450540006f76150540016f46150540037b44150540005fb705054000df87050540004fe76c8540004fd76c8540024fc76c85400067f65c85400067c65c8540005be74c8540005bd74c8540007ad42c8540004ff7648540004fe7648540004fc76485400067f65485400067c6548540005bf7448540005bc7448540007ad424854000dfa76d014000efa76d01400077b65d01400077865d014000dfa74d014000fba74d014000efb64d014000fbb64d0140047ba54d0140007b954d0140047bb42d0140007b942d0140005f971d01401f7ba41d0140047b841d0140044fe74d9720026be74d9720004be74d9720004fd74d9720026bd74d9720004bd74d9720194fe73d9720026de73d9720004de73d9720004fd73d9720026dd73d9720004dd73d9720024fe72d9720026ee72d9720014fe71d9720004fd71d9720014fc71d9720026f970d97201267e50d97201267c50d9720114fd76997200267f6599720044fe7499720004fd7499720194fe7399720004fd739972000cfe729972005eee729972000cfc72997200267e52997200267c5299720014fe7199720004fd7199720014fc719972005e7f50997201367d50997200267c65597200267f7559720004ff7459720044fc7459720004ff7359720194fc735972005cff725972000cfe7259720114fd725972000cfc72597200267e52597200267c5259720004ff7159720014fe7159720014fc71597201167f50597201167d505972005cfe75197200267e7519720044fe7419720004fd7419720194fe7319720004fd7319720024fe7219720026ee7219720014fe7119720004fd7119720014fc7119720026f970197201067e501972005e7c501972005cfe75d93200267e75d93200047e75d9320004f
  | 11 => 0x35bc7155140007bb705514000dbe705514000dbc7055140157b87055140156bf6055140157ba1055140164fe76151400067f651514005e7c6515140165be74151400067f65d89400067c65d894005cfe75d8940004fd75d8940194fe73d8940004fd73d8940014fe71d8940004fd71d8940014fc71d8940006ee21d8940006ec21d89400f6ef20d89400f6fa10d89400057e75989400057d75989400067f65989400067c6598940005de7398940005dd7398940006ef62989400057f75589400057c75589400067f65589400067c65589400067f65189400067c6518940006ed621894005cfe7518940004fd7518940026bd7418940194fe7318940004fd7318940014fe7118940004fd7118940014fc7118940006be4118940006bc4118940006ee2118940026ec2118940026ef20189400c6ed2018940004fe76d4940004fd76d494005cfc76d49400067f65d494005e7c65d4940005be74d4940005bd74d49400073e54d4940004fe7694940004fd7694940024fc76949400067f65949400067c6594940005be7494940005bd7494940005de7394940005dd7394940004ff7654940004fe7654940004fc76549400067f65549400067c65549400073e5454940004fe7614940004fd7614940024fc76149400067f651494005e7c6514940005be7414940005bd74149400c4fe76d09400067f65d09400067c65d09400c5be76d0940006be76d0940005bf75d0940005bd75d09400073f65d0940006be65d0940006bc65d09400073c65d09400063c65d0940005bd73d0940006bc63d0940026bc62d0940035be71d0940035bc71d094000dbe70d094000dbc70d0940046bf60d09400f7ba10d094000cfe76909400057e75909400057d75909400067f65909400067c65909400d5bd7490940005de7390940005dd7390940006ef6290940026ec629094000dfa7090940005f9709094000cfc76509400067f65509400067c6550940006ef6250940006ec6250940005fb705094000df8705094000dbc76509400d6bc765094000cbc7650940005bf7550940005bd75509400073f6550940006be6550940006bc65509400073c65509400063c6550940005bf7350940006bc6350940007af7250940007af6250940026bc6250940007ac6250940006ac6250940035be7150940035bc7150940007bb705094000dbe705094000dbc70509400d7b870509400d6bf60509400d7ba10509400f4fe76109400067f65109400067c65109400f5be7410940004fe768c940004fd768c940024fc768c9400057e758c9400057d758c9400067f658c9400067c658c940005be748c940005bd748c940006ef628c940026ec628c940007af428c940004ff764c940004fe764c940004fc764c9400067f654c9400067c654c940005be744c940005bd744c940006ef624
  | 12 => 0xe40d95401673c40d95401677840d95401677a10d95401667f74d95401667d74d95400067f72d95400067e72d95400067d72d95400067c72d95400067f71d95400067e71d95400067d71d95400067c71d95400067e41d95400067c41d95400067e21d95400067c21d95401667f70d95401667e70d95401667d70d95401667c70d95401667f40d95401667e40d95401667c40d95401667f20d95401667e20d95401667d20d95401667c20d95401667f10d95401667e10d95401667d10d95401667c10d95400067f6599540155bd749954005cfe75995401447e7599540154fd749954005ebd7499540024fe7299540004fd7299540014fe7199540004fd7199540014fc7199540006be4199540006bc4199540174fd709954005ef97099540176fa1099540175bf74595400067f7559540174ff7459540006bf7459540004ff7259540024fc7259540004ff7159540014fe7159540014fc7159540154ff7059540006fb7059540164fe76195400067d651954005e7e7519540044fe741954005ebd7419540044fc7419540024fe7219540004fd7219540014fe7119540004fd7119540014fc71195400067e511954005e7c5119540006be4119540006bc4119540044ff7019540144fd701954005e7f50195401467d5019540146fa10195401657e76195400067e76195401647e76195401473d74195400067e61195400067c61195400073e41195400073c41195401473e40195401473c40195401477840195401477a101954005e7f74195401467d74195401463d741954005e7f72195400067e72195400067d721954005e7c721954005e7f71195400067e71195400067d711954005e7c71195400067e41195400063e41195400067c41195400063c41195400067e21195400067c211954005e7f70195401467e70195401467d701954005e7c70195401467f40195401467e40195401467d40195401467c40195401467f20195401467e20195401467d20195401467c20195401467f10195401467e10195401467a10195401467d10195401467c101954000cfe76d514000cfc76d51400067f65d514005e7c65d514000dfa70d5140005f970d5140144fe76951401667f65951400067c65951400073f5495140145be7695140006be7695140155bd75951401673f659514005ebe659514005ebc65951400073c65951400063c6595140005bd7295140035be7195140035bc719514000dbe709514000dbc7095140046bf60951401673e50951401673c5095140167ba109514005cff765514000cfe7655140154fd765514000cfc76551400067f65551400067c6555140005fb705514000df8705514000dbc7655140156bc765514000cbc76551400073f75551400073f655514005ebe655514005ebc65551400073c6555140005bf7255140035be7155140
  | 13 => 0x8b40014fe7158b40014fc7158b400d6ef2058b4005cff76d4b40044fe76d4b40004fd76d4b400067f65d4b4005e7c65d4b40045be74d4b40005bd74d4b400073e54d4b40006ee62d4b40006ed62d4b40024ff7694b40044fe7694b40004fd7694b400067e6594b400067d6594b40045be7494b40005bd7494b40005de7394b40005dd7394b40004ff7654b40004fd7654b40044fc7654b400067f6554b400067c6554b400073e5454b40024ff7614b40044fe7614b40004fd7614b4005e7e6514b400067d6514b40045be7414b40005bd7414b40026ee6214b40006ed6214b4000dbd76d0b40046bd76d0b4000cbd76d0b40045bf75d0b40005bd75d0b40006be65d0b40046bc65d0b40005bd73d0b40006be63d0b40026be62d0b40047ae62d0b40047ad62d0b4003dbe71d0b40045bc71d0b4000dbe70d0b40047ba70d0b40047b970d0b4000dbc70d0b400d4fd7690b400057e7590b400057d7590b40005de7390b40005dd7390b400e4ff7650b400e5bf7650b40006bf7650b40005bf7550b40005bd7550b40006be6550b40006bc6550b40005bf7350b40006be6350b40047af7250b40026be6250b4003dbe7150b4003dbc7150b4000dbe7050b4000dbc7050b40024ff768cb40044fe768cb40004fd768cb400057e758cb400057d758cb40045be748cb40005bd748cb40006de638cb40006dd638cb40007af428cb40004ff764cb40004fd764cb40044fc764cb40045be744cb40005bd744cb40007af424cb40024ff760cb40044fe760cb40004fd760cb40045be740cb40005bd740cb40026ee620cb40006ed620cb40007cd320cb40014ff765874000dbc7458740046f46158740047b44158740004ff755874005cfc7558740014fd745874000cfc7458740076bc745874000cbc7458740004ff7258740024fc7258740006bf4258740006bd4258740046f7415874003ebe415874003ebc4158740046f44158740076fa4058740076f7105874005cff76d4740044fe76d4740004fd76d474005e7e65d47400067d65d4740045be74d4740005bd74d47400073d54d4740004ff7654740004fd7654740044fc76547400067e65547400067d6554740005bf7454740045bc74547400073d54547401bcff76507401bdbf7450740047b44150740024ff76c8740044fe76c8740004fd76c8740045be74c8740005bd74c8740026ee62c8740006ed62c8740007ad42c8740004ff7648740004fd7648740044fc7648740005bf7448740045bc7448740006ee6248740006ed6248740007ad4248740024fe72d9540004fd72d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400067c51d9540044ff70d9540164fd70d95401667f50d95401667d50d95401673f74d95400067e61d95400067c61d95400073e41d95400073c41d95401673
  | 14 => 0x8ef850d855008ef710d8550005bf7458550005bc7458550005ef7258550005ec725855004ef461585501ccfe76d455008e7f65d455005f7850d455000cfc76545500867f6554550005bf7454550005bc7454550006f76154550016f46154550005fb705455000df87054550087785054550004fe76d0550004fd76d0550044fc76d0550004ff7650550004fe7650550004fc7650550004fe76c8550004fd76c8550024fc76c85500057e75c85500057d75c8550004ff7648550004fe7648550004fc7648550005bf7448550005bc744855000dfa76d415000efa76d415000dfa75d415000f7a75d415000efb65d415000f7b65d415005f7b52d41500077952d4150006fb61d4150044fe74d9740046be74d9740024fe72d9740046ee72d9740004ee72d9740004fd72d9740046ed72d9740004ed72d9740014fe71d9740004fd71d9740014fc71d9740046f970d97401667e50d97401667c50d9740154fd76997400467f659974000cfe749974005ebe749974000cfc74997400467e54997400467c5499740024fe7299740004fd7299740014fe7199740004fd7199740014fc7199740006be4199740006bc419974005e7f50997401767d50997400467c65597400467f755974005cff745974000cfe7459740154fd745974000cfc74597400467e54597400467c5459740004ff7259740024fc7259740004ff7159740014fe7159740014fc71597401567f50597401567d505974005cfe75197400467e7519740044fe7419740046be7419740024fe7219740004fd7219740014fe7119740004fd7119740014fc7119740006be4119740046bc4119740046f970197401467e501974005e7c5019740154fd76d53400473e54d534000dbd7695340046bd769534000cbd769534005ebe65953400473e65953400063e65953400473d6595340046bc6595340005bd729534003dbe7195340045bc719534000dbe7095340047ba7095340047b9709534000dbc70953401673e50953401673c5095340174ff7655340157ba4055340175bf7655340006bf76553400473f755534005ebe655534005ebc6555340005bf725534003dbe715534003dbc715534000dbe705534000dbc70553400057e7598b400057d7598b40005de7398b40005dd7398b40046ef6298b4005cfe7598b400267e7598b400047e7598b40004fd7598b400267d7598b400047d7598b4000cfe7498b40026be7498b40194fe7398b40026de7398b40004de7398b40004fd7398b40026dd7398b40004dd7398b40046ef4298b40026ec4298b40014fe7198b40004fd7198b40014fc7198b40006be4198b40006bc4198b40026ef2098b400e6ed2098b40046ec6258b40004ff7558b4005cfc7558b4000cfc7458b40004ff7358b40194fc7358b40046ef4258b40046ec4258b40004ff715
  | 15 => 0xc41d9150176bf40d9150006bf6499150005ee7299150005ed7299150006bd6419150024fe7219150004fd7219150014fe7119150004fd7119150014fc7119150006be4119150046bc41191501467e50191501467c5019150046bf4019150146bd4019150144fe76d515000cfe76951501667f6595150006bf6495150046bc64951500073f549515000dfa7095150005f9709515000cfc7655150006bf6455150006bc6455150005fb705515000df87055150174fe76151501467f6515150044fe74d8950004fd74d8950194fe73d8950004fd73d8950014fe71d8950004fd71d8950014fc71d8950006ee21d8950006ec21d8950136ef20d8950005be7498950005bd7498950005de7398950005dd7398950006ef6298950006ed62189500267d7518950044fe7418950004fd7418950194fe7318950004fd7318950014fe7118950004fd7118950014fc7118950006ee2118950026ec21189501067e50189501067c5018950026ef2018950106ed2018950104fe76d49501057e76d49500067e76d49501047e76d49500067c64d49500057d73d49500067c63d49500267c62d495000d7e70d495000d7c70d495005e7f60d495000cfe76949501157d75949501267f6594950005be7494950005bd7494950005de7394950005dd7394950006ef6294950026ec629495000dfa7094950005f9709495000cfc7654950006ef6254950006ec6254950005fb705495000df8705495000d7c76549501167c765495000c7c76549500067c64549500057f73549500067c63549500076f72549500076f62549500267c62549500076c62549500077b705495000d7e705495000d7c70549501177870549501167f6054950134fe76149501357e75149501067f65149500076d5214950004fe76d0950004fd76d0950044fc76d0950006bf64d0950046bc64d0950004fe7690950004fd7690950024fc76909500057e75909500057d7590950005de7390950005dd7390950006ef6290950026ec6290950004ff7650950004fe7650950004fc7650950006bf6450950006bc6450950006ef6250950006ec6250950004fe7610950004fd7610950024fc76109500057e75109500057d7510950004fe768c950004fd768c950024fc768c9500057e758c9500057d758c950005be748c950005bd748c950006ef628c950026ec628c9500076f528c950004ff764c950004fe764c950004fc764c9500057e754c9500057d754c950006ef624c950006ec624c9500076f524c950004fe760c950004fd760c950024fc760c9500057e750c9500057d750c950007cd320c950014fe76d855004ef661d855000cfd75d8550014fc75d8550044fe74d8550004fd74d8550024fe72d8550004fd72d85500067f52d85500067d52d855004ef651d855008e7e50d855008e7c50d8550
  | 16 => 0x9350154fd76953501667e659535005f3f5495350164ff76553501577a5055350005be7498b50005bd7498b50005de7398b50005dd7398b5005eef6298b5000cfe7598b500267e7598b50044fe7498b50026be7498b50004be7498b50004fd7498b50026bd7498b50004bd7498b50194fe7398b50026de7398b50004de7398b50004fd7398b50026dd7398b50004dd7398b5005eef5298b50026ec5298b50014fe7198b50004fd7198b50014fc7198b501267e5098b501267c5098b50026ef2098b50126ed2098b5005eec6258b5000cfc7558b50004ff7458b50044fc7458b50004ff7358b50194fc7358b5005eef5258b5005eec5258b50004ff7158b50014fe7158b50014fc7158b50116ef2058b50116fa1058b5000d7d76d4b5005e7d76d4b5000c7d76d4b500067e64d4b500057d73d4b500067e63d4b500267e62d4b5005f6e62d4b5005f6d62d4b5000d7e70d4b5005f7a70d4b5005f7970d4b5000d7c70d4b501377a10d4b50114fd7694b501267e6594b50005be7494b50005bd7494b50005de7394b50005dd7394b50124ff7654b5005f6c5254b501257f7654b500067f7654b501247f7654b500067e6454b500057f7354b500067e6354b5005f6f7254b5005f6f6254b500267e6254b5005f6c6254b5000d7e7054b5000d7c7054b501177a1054b50044ff76d0b5005cfe76d0b50004fd76d0b50024ff7690b5005cfe7690b50004fd7690b5005d7e7590b500057d7590b50005de7390b50005dd7390b50004ff7650b50004fd7650b5005cfc7650b50024ff7610b5005cfe7610b50004fd7610b5005d7e7510b500057d7510b50024ff768cb5005cfe768cb50004fd768cb5005d7e758cb500057d758cb50005be748cb50005bd748cb500076f528cb50004ff764cb50004fd764cb5005cfc764cb5005d7e754cb500057d754cb500076f524cb50005fb704cb5000df8704cb50024ff760cb5005cfe760cb50004fd760cb5005d7e750cb500057d750cb50007cd320cb50014ff7658750005bf7458750005bc745875005ef46158750014fd755875000cfc7558750004ff7458750006bf7458750004bf7458750044fc7458750006bc7458750004bc7458750004ff7258750024fc72587500067f52587500067d525875005ef7515875005ef451587500867e50587500867c5058750086f710587501dcff76547500867e6554750005bf7454750005bc7454750016f4615475000dfa7054750044ff76d075005cfe76d0750004fd76d0750004ff7650750004fd765075005cfc7650750024ff76c875005cfe76c8750004fd76c875005d7e75c87500057d75c8750004ff7648750004fd764875005cfc7648750005bf7448750005bc7448750024fe72d9150004fd72d9150014fe71d9150004fd71d9150014fc71d9150006be41d9150006b
  | 17 => 0x14ec7650921007af7450921007af6450921046ee6450921046ec6450921007ac6450921007af5450921007ac5450921005ef7350921007ae4350921007ac4350921007e77150921015ee7150921015ec71509210dfe471509210deef61509210dfaf41509210dfad41509210dfe710509210ecfe7610921006bf6410921046bc64109210edee7210921007ad4210921014fe76cc921014fc76cc9210057e75cc9210057d75cc921005be74cc921005bd74cc921006bf64cc921006bc64cc921006df63cc921196dc63cc921015f671cc921005f571cc92109cfe768c9210057e758c9210057d758c921005be748c921005bd748c921006bf648c921006bc648c92109dee768c921006ee768c9210076e758c9210076d758c921006ee658c921006ec658c921005ef748c921007ae748c921005ed748c921007ad748c921005ad748c921007af648c921006ee648c921006ec648c921007ac648c921006ac648c9210aded738c921196ee638c921196ec638c921015ee718c921015ec718c921026ef618c9210bfe7108c921194ff764c921014fe764c9210acfd764c921014fc764c921006bf644c921006bc644c921006df634c921006dc634c921005f7714c921015f4714c921015ec764c9210aeec764c921014ec764c921006ee654c921006ec654c921005ef744c921005ed744c921007af644c921006ee644c921006ec644c921007ac644c921006ac644c921007cf734c921007cf634c921196ee634c921196ec634c921007cc634c921006cc634c921007cf534c921007cc534c921007cf434c921007cc434c921007e7714c921015ee714c921015ec714c9210afe4714c9210aeef614c9210afcf314c9210afcd314c9210afe7104c9210bcfe760c921006bf640c921006bc640c9210bdee720c921007cd320c921007b764c8521007b464c8521015f672c8521017e672c8521016f762c8521017e762c8521027e642c8521007e542c8521027e632c8521007e532c8521005f570c852100cfe76d8121006bf64d8121006bc64d8121066fa60d812105cfe75d8121004fd75d8121044fe74d8121004fd74d8121194fe73d8121004fd73d8121014fd72d8121006ee32d8121006ed32d812100cfc71d8121066fa20d8121066fa10d81210057f75581210057c7558121005bf7458121005bc7458121006bf6458121006bc6458121005df7358121005dc7358121066f8605812105ebf649935000cfe759935005ebf5499350046bc5499350024fe7299350004fd7299350014fe7199350004fd7199350014fc71993501667e50993501667c5099350046bf4099350166bd409935005ebc645935000cfc755935005ebf545935005ebc5459350004ff7259350024fc7259350004ff7159350014fe7159350014fc7159350156bf4059350156fa105
  | 18 => 0xf7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d210aef71058d210bcfe7618d21006bf6418d21006bc6418d21006dd6318d2105cfe7518d21004fd7518d21044fe7418d21004fd7418d21196de7318d21196ed7218d21024ff7118d2109cfd7118d21196df3118d2109edd3118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21196dc3018d2105cff76d4d21004fe76d4d21004fd76d4d2105cfc76d4d210067f65d4d2105e7c65d4d21006bf64d4d21006bc64d4d21194ff7694d21004fe7694d21004fd7694d21194fc7694d21005be7494d21005bd7494d21006bf6494d21006bc6494d21006df6394d21196dc6394d210075f5394d21005ee7294d21005ed7294d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210067c6554d21006bf6454d21006bc6454d21006df6354d21006dc6354d21194ff7614d21004fe7614d21004fd7614d21194fc7614d21006bf6414d21006bc6414d21005ee7214d21005ed7214d21044ff76d0d21004fe76d0d21004fd76d0d21044fc76d0d21006bf64d0d21046bc64d0d21005ee72d0d21005ed72d0d21194ff7690d21004fe7690d21004fd7690d21194fc7690d210057e7590d210057d7590d21006bf6490d21006bc6490d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21006bc6450d21194ff7610d21004fe7610d21004fd7610d21194fc7610d21006bf6410d21046bc6410d21005ee7210d21005ed7210d21014fe76d4921014fc76d49210067f65d492105e7c65d4921006bf64d4921006bc64d4921015f671d4921005f571d492110cfe7694921005be7494921005bd7494921006bf6494921006bc6494921005de7394921005dd7394921027e4219492105cff7654921014fe765492111cfd7654921014fc76549210067f65549210067c6554921006bf6454921006bc6454921005f77154921015f4715492111fe4215492112cfe7614921006bf6414921006bc6414921014fe76d0921014fc76d0921006bf64d0921046bc64d0921015f671d0921005f571d09210ccfe76909210057e75909210057d75909210eebf6490921006bc6490921005de7390921005dd73909210cdee7690921006ee76909210076e75909210076d75909210dded74909210efaf6490921046ee6490921046ec6490921007ac6490921006ac6490921007ce7390921005ed7390921007cd7390921005cd7390921007af4390921007ad4390921015ee7190921015ec7190921026ef61909210efae41909210efac41909210efe71090921044ff7650921014fe76509210dcfd7650921014fc7650921006bf6450921006bc6450921005f77150921015f47150921015ec76509210deec7650921
  | 19 => 0x9121004ff755912105cfc7559121006bf7459121004ff7359121194fc73591210fcff7259121006ef72591210dcff7159121006f77159121004ff705912100cfe705912100cfc70591210ecfe7619121006bd641912105cfe7519121004fd7519121046be7419121194fe7319121004fd7319121046ed7219121024ff71191210ccfd7119121046bf41191210cebd411912100cfe7019121004fd701912100cfc7019121006be4019121046bc40191210cef710191210edbe7619121006be76191210ecbe7619121006bf6519121006be6519121006bd6519121006bc65191210cfad72191210cfae21191210cfac21191210cfb42119121006be6019121006bc60191210cfb71019121046bf7519121006be7519121006bd7519121046bc7519121046bf7319121006be7319121006bd7319121046bc7319121046bf72191210cebd72191210cead7219121046bf71191210cebe71191210cebd7119121046bc71191210cebf51191210cebe51191210cebd51191210cebc51191210cebf31191210cebe31191210cebd31191210cebc31191210cebf21191210cebe21191210cebd21191210cebc2119121046bf7019121006be7019121006bd7019121046bc7019121006be5019121006bc5019121006be3019121006bc3019121006be2019121006bc20191210cebf10191210ceb710191210cebe10191210cebd10191210cebc101912105cff76d5121004fe76d5121004fd76d512105cfc76d5121006bf64d5121006bc64d5121044ff7695121004fe7695121004fd7695121044fc7695121006bf6495121046bc64951210073f5495121005ee7295121005ed7295121004ff7655121004fe7655121004fd7655121004fc7655121006bf6455121006bc6455121044ff7615121004fe7615121004fd7615121044fc7615121006bf6415121046bc6415121005ee7215121005ed7215121006bf64d8d21006bc64d8d2105cfe75d8d21004fd75d8d21044fe74d8d21004fd74d8d210bedf31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d210bef710d8d210057e7598d210057d7598d21005be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d210aded7298d2105cfe7598d211967e7598d210047e7598d21004fd7598d211967d7598d210047d7598d21044fe7498d21196be7498d21004be7498d21004fd7498d21196bd7498d21004bd7498d21194fe7398d210acfd7298d21196ed7298d211fcfd7198d21196f57198d2100cfe7098d21004fd7098d2100cfc7098d21005bf7458d21005bc7458d21006bf6458d21006bc6458d211fdef7258d21004ff7558d2105cfc7558d21004ff7458d21006bf7458d21004bf7458d21044fc7458d21006bc7458d21004bc7458d21006ef7258d210acf
  | 20 => 0x47f755832105cfc75583210067c75583210047c7558321004ff7458321044fc7458321004ff7358321194fc7358321014fc7258321006ee3258321006ed325832101ef62158321026fb2058321026f8205832106efa1058321044fe74d9521004fd74d9521194fe73d9521004fd73d9521024ff71d952112cfd71d952112e7f51d952112e7d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210067c50d952112ef710d95210067f6599521005be7499521005bd7499521005de7399521005dd739952111ded729952105cfe7599521044fe749952105ebe7499521004be7499521004fd749952105ebd7499521004bd7499521194fe739952105ede7399521004de7399521004fd739952105edd7399521004dd739952111cfd729952105eed729952113cfd719952105ef5719952100cfe7099521004fd709952100cfc7099521005bf7459521005bc745952113def72595210067f7559521004ff7459521006bf7459521004bf7459521044fc7459521006bc7459521004bc7459521004ff7359521194fc735952113cff7259521006ef725952111cff7159521006f77159521004ff705952100cfe705952100cfc705952111ef7105952112cfe76195210067d651952105e7e7519521044fe7419521004fd7419521194fe7319521004fd7319521024ff711952110cfd711952105e7f511952110e7d511952100cfe7019521004fd701952100cfc70195210067e501952105e7c501952105cfe75d9121004fd75d9121194fe73d9121004fd73d9121024ff71d91210ecfd71d91210eebf41d91210eebd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121006bf65d9121006be65d9121006bd65d9121006bc65d91210efaf72d91210efae21d91210efac21d91210efb421d9121006be60d9121006bc60d91210efb710d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d91210eebf72d91210eebd72d91210eebf71d91210eebe71d91210eebd71d91210eebc71d91210eebf51d91210eebe51d91210eebd51d91210eebc51d91210eebf31d91210eebe31d91210eebd31d91210eebc31d91210eebf21d91210eebe21d91210eebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006be50d9121006bc50d9121006be30d9121006bc30d9121006be20d9121006bc20d91210eebf10d91210eebe10d91210eebd10d91210eebc10d9121006bf64991210dded729912105cfe7599121004fd7599121044fe74991210ccbe7499121194fe7399121004fd73991210dcfd7299121046ed72991210fcfd7199121046f5719912100cfe7099121004fd709912100cfc70991210fef710991210fdef725
  | 21 => 0xc65d4f21006de63d4f21006dd63d4f21194ff7694f21024fe7694f21004fd7694f21024fc7694f210067e6594f210067d6594f21005be7494f21005bd7494f210075f5394f21025ee7294f21005ed7294f21004ff7654f21004fd7654f21024fc7654f210067f6554f210067c6554f21194ff7614f21024fe7614f21004fd7614f21024fc7614f2105e7e6514f210067d6514f21196de6314f21006dd6314f21025ee7214f21005ed7214f21044ff76d0f21024fe76d0f21004fd76d0f21006bf64d0f21046bc64d0f21006de63d0f21006dd63d0f21025ee72d0f21005ed72d0f21194ff7690f21024fe7690f21004fd7690f21024fc7690f210057e7590f210057d7590f21006be6490f21006bd6490f21025ee7290f21005ed7290f21004ff7650f21004fd7650f21024fc7650f21006bf6450f21006bc6450f21005f77150f21015f47150f21194ff7610f21024fe7610f21004fd7610f21024fc7610f21046be6410f21006bd6410f21196de6310f21006dd6310f21025ee7210f21005ed7210f2111cfd76d4b210267f65d4b210267c65d4b2113cff7654b210267f6554b210267c6554b210dcfd76d0b21026bf64d0b21026bc64d0b21015ed7690b21026ed7690b21014ed7690b210276e7590b210276d7590b21046ee6490b21027ae6490b21027ad6490b21026ec6490b21027ce7390b21005ed7390b21027cd7390b21005cd7390b21007af4390b21007ad4390b21015ee7190b21027e67190b21027e57190b21015ec7190b210efae4190b210efac4190b210fcff7650b21026bf6450b21026bc6450b21027ac4250b210fdef7650b21006ef7650b21027af7450b21027af6450b21046ee6450b21046ec6450b21027ac6450b21007af5450b21007ac5450b21005ef7350b21007ae4350b21007ac4350b21015ee7150b21015ec7150b210dfaf4150b210dfad4150b210acfd76ccb210057e75ccb210057d75ccb21005be74ccb21005bd74ccb21015ed768cb21026ed768cb21014ed768cb210276e758cb210276d758cb21006ee658cb21026ec658cb21025ef748cb21027ae748cb21005ed748cb21027ad748cb21005ad748cb21006ee648cb21026ec648cb21196ee638cb21027ce638cb21027cd638cb21026ec638cb21015ee718cb21027e6718cb21027e5718cb21015ec718cb211fcff764cb21027cc324cb211fdef764cb21006ef764cb21006ee654cb21006ec654cb21005ef744cb21005ed744cb21006ee644cb21006ec644cb21027cf734cb21027cf634cb21196ee634cb21196ec634cb21027cc634cb21006cc634cb21007cf534cb21007cc534cb21007cf434cb21007cc434cb21015ee714cb21015ec714cb210afcf314cb2100cff76583210057f75583210057c7558321026f86058321004ff75583210067f7558321
  | 22 => 0x9721014fe7259721014fc72597210267e52597210267c525972111e7f515972111e7d5159721004ff705972100cfe705972100cfc705972105cfe75197210267e7519721044fe7419721004fd7419721194fe7319721004fd7319721024fe7219721026ee7219721026f5711972100cfe7019721004fd701972100cfc70197210067e501972105e7c501972105cfe75d93210267e75d93210047e75d9321004fd75d93210267d75d93210047d75d9321194fe73d9321026de73d9321004de73d9321004fd73d9321026dd73d9321004dd73d9321024fe72d9321026ee72d9321026f571d93210eebe41d93210eebc41d932100cfe70d9321004fd70d932100cfc70d93210dcfd7699321026bf649932105cfe7599321004fd7599321194fe7399321004fd7399321014fe7299321046ee7299321014fc7299321026be4299321026bc4299321046bf41993210febd419932100cfe7099321004fd709932100cfc7099321026bc6459321004ff755932105cfc7559321026bf7459321004ff7359321194fc7359321014fe7259321014fc7259321026be4259321026bc42593210debf41593210debd4159321004ff705932100cfe705932100cfc705932105cfe7519321004fd7519321044fe7419321026be7419321194fe7319321004fd7319321024fe7219321026ee7219321026f571193210cebe4119321046bc411932100cfe7019321004fd701932100cfc701932105cff76d5321024fe76d5321004fd76d5321024fc76d5321006be64d5321006bd64d5321044ff7695321024fe7695321004fd7695321024fc76953210067e65953210067d65953210073f5495321025ee7295321005ed7295321004ff7655321024fe7655321004fd7655321024fc7655321044ff7615321024fe7615321004fd7615321024fc761532105e7e65153210067d6515321046be6415321006bd6415321025ee7215321005ed72153210057e7598f210057d7598f21005be7498f21005bd7498f21026df6398f2105cfe7598f211967e7598f210047e7598f21004fd7598f211967d7598f210047d7598f21044fe7498f21196be7498f21004be7498f21004fd7498f21196bd7498f21004bd7498f21014fe7298f21196ee7298f21014fc7298f21026de3298f21026dc3298f21196df3198f211fedd3198f2100cfe7098f21004fd7098f2100cfc7098f21026dc6358f21004ff7558f2105cfc7558f21004ff7458f21044fc7458f21014fc7258f21026de3258f21026dc3258f210aedf3158f21004ff7058f2100cfe7058f2100cfc7058f2105cfe7518f21004fd7518f21044fe7418f21004fd7418f21024fe7218f21026ee7218f21026f57118f2100cfe7018f21004fd7018f2100cfc7018f2105cff76d4f21024fe76d4f21004fd76d4f210067f65d4f2105e7
  | 23 => 0xceed211894100cfe7018941004fd701894100cfc7018941006ee2018941026ec2018941004fe76d4941004fd76d494105cfc76d49410067f65d494105e7c65d4941004fe7694941004fd7694941024fc7694941005be7494941005bd7494941005de7394941005dd7394941006ef6294941026ec6294941004ff7654941004fe7654941004fc76549410067f65549410067c6554941006ef6254941006ec6254941004fe7614941004fd7614941024fc7614941005be7414941005bd74149410ccfe76d09410cdbe76d0941006be76d09410ccbe76d0941006be65d0941006bc65d0941005bd73d0941006bc63d0941026bc62d0941015be71d0941015bc71d0941046bf61d0941014fe76909410057e75909410057d75909410ddbd74909410eebf6490941005de7390941005dd7390941006ef6290941026ec6290941015f67190941005f57190941014fc7650941006ef6250941006ec6250941005f77150941015f47150941015bc76509410debc7650941014bc7650941006be6550941006bc6550941005bf7350941006bc6350941007af7250941007af6250941026bc6250941007ac6250941007b77150941015be7150941015bc71509410dfb471509410debf61509410fcfe76109410fdbe74109410cebf6410941007ad4210941004fe768c941004fd768c941024fc768c9410057e758c9410057d758c941005be748c941005bd748c941006ef628c941026ec628c941007af428c941004ff764c941004fe764c941004fc764c941005be744c941005bd744c941006ef624c941006ec624c941007af424c941004fe760c941004fd760c941024fc760c941005be740c941005bd740c941007cd320c941015f674d0541017b674d0541016f764d0541017b764d0541047b742d0541007b542d054100cfe76d8141076fa60d814105cfe75d8141004fd75d8141014fd74d8141024fe72d8141004fd72d8141006bf42d8141006bd42d8141006f741d814103ebe41d814103ebc41d814103ef441d8141076fa40d8141076fa10d81410057f75581410057c7558141005ef7258141005ec7258141076f86058141044fe74d9721026be74d9721004be74d9721004fd74d9721026bd74d9721004bd74d9721194fe73d9721026de73d9721004de73d9721004fd73d9721026dd73d9721004dd73d9721024fe72d9721026ee72d9721026f571d972100cfe70d9721004fd70d972100cfc70d97210067e50d97210067c50d972111cfd76997210267f6599721044fe7499721004fd7499721194fe7399721004fd7399721014fe7299721014fc72997210267e52997210267c529972105e7f519972113e7d519972100cfe7099721004fd709972100cfc70997210267c65597210267f7559721004ff7459721044fc7459721004ff7359721194fc735
  | 24 => 0x571d0b41015bc71d0b410ffb710d0b410dcfd7690b410057e7590b410057d7590b410eebe6490b41005de7390b41005dd7390b410ecff7650b41047ac4250b410edbf7650b41006bf7650b410ecbf7650b41006be6550b41006bc6550b41005bf7350b41006be6350b41047af7250b41047af6250b41026be6250b41047ac6250b41015be7150b41015bc7150b410dfb71050b41024ff768cb41044fe768cb41004fd768cb410057e758cb410057d758cb41045be748cb41005bd748cb41007af428cb41004ff764cb41004fd764cb41044fc764cb41045be744cb41005bd744cb41007af424cb41005f7714cb41015f4714cb41024ff760cb41044fe760cb41004fd760cb41045be740cb41005bd740cb41007cd320cb4100cff76583410057f75583410057c7558341046f86058341004ff75583410067f75583410047f755834105cfc75583410067c75583410047c7558341014fc7458341004ff7258341024fc7258341006bf4258341006bd4258341036be4158341036bc4158341046fb4058341046f8405834107efa1058341024fe72d9541004fd72d9541044ff71d954116cfd71d954116e7f51d954116e7d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410067c50d95410067f659954115dbd7499541005ee7299541005ed729954105cfe759954115cfd749954105ebd7499541024fe729954105eee7299541004ee7299541004fd729954105eed7299541004ed729954117cfd719954105ef5719954117ebe419954117ebc419954100cfe7099541004fd709954100cfc709954117dbf74595410067f755954117cff7459541006bf745954117cbf7459541004ff7259541024fc725954115cff7159541006f77159541004ff705954100cfe705954100cfc705954116cfe76195410067d651954105e7e7519541024fe7219541004fd7219541044ff711954114cfd711954105e7f511954114e7d511954114ebe411954114ebc411954100cfe7019541004fd701954100cfc70195410067e501954105e7c5019541014fe76d5141014fc76d51410067f65d514105e7c65d514117ebf64d5141015f671d5141005f571d514114cfe76951410073f5495141047b4419514105cff7655141014fe765514115cfd7655141014fc76551410067f65551410067c6555141005f77155141015f4715514115fb4415514116cfe761514114ebf641514105cfe75d8941004fd75d8941194fe73d8941004fd73d89410feef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d89410057e75989410057d7598941005de7398941005dd7398941006ef6298941006ed621894105cfe7518941004fd7518941026bd7418941194fe7318941004fd73189410cebe41189410cebc4118941026ef2118941
  | 25 => 0x45510077552d4551005f570d45512077650d455105f7450d455100cfe76d81510157d75d8151006bf64d8151006bc64d8151086fa60d81510877a50d8151014fd75d81510867d75d81510147d75d8151044fe74d8151004fd74d8151024fe72d8151004fd72d81510067f52d81510067d52d81510867e50d8151086fa50d81510867c50d8151086fa10d8151005bf7458151005bc7458151006bf6458151006bc6458151005ef7258151005ec7258151086f86058151087785058151044fe74d9741046be74d974114cbe74d9741024fe72d9741004fd72d9741046f571d974100cfe70d9741004fd70d974100cfc70d97410067e50d97410067c50d974116ef710d974115cfd76997410467f6599741014fe7499741014fc74997410467e54997410467c5499741024fe7299741004fd729974105e7f519974117e7d519974117ebe419974117ebc419974100cfe7099741004fd709974100cfc70997410467c65597410467f7559741014fe7459741014fc74597410467e54597410467c5459741004ff7259741024fc725974115e7f515974115e7d5159741004ff705974100cfe705974100cfc705974115ef7105974105cfe75197410467e7519741044fe7419741046be7419741024fe7219741004fd7219741046f5711974114ebe4119741046bc411974100cfe7019741004fd701974100cfc70197410067e501974105e7c501974115cfd76d53410467f65d53410467c65d534117ebe64d53410473e54d534117cff76553410467f65553410467c655534115fb641553410057e7598b410057d7598b41005de7398b41005dd7398b41046ef6298b4105cfe7598b410267e7598b410047e7598b41004fd7598b410267d7598b410047d7598b41014fe7498b41026be7498b41194fe7398b41026de7398b41004de7398b41004fd7398b41026dd7398b41004dd7398b41046ef4298b41026ec4298b410eebe4198b410eebc4198b41026ef2198b410eeed2198b4100cfe7098b41004fd7098b4100cfc7098b41046ec6258b41004ff7558b4105cfc7558b41014fc7458b41004ff7358b41194fc7358b41046ef4258b41046ec4258b410deef2158b41004ff7058b4100cfe7058b4100cfc7058b410def71058b4105cff76d4b41044fe76d4b41004fd76d4b410067f65d4b4105e7c65d4b41024ff7694b41044fe7694b41004fd7694b41045be7494b41005bd7494b41005de7394b41005dd7394b41004ff7654b41004fd7654b41044fc7654b410067f6554b410067c6554b41024ff7614b41044fe7614b41004fd7614b41045be7414b41005bd7414b41015bd76d0b41046bd76d0b41014bd76d0b41006be65d0b41046bc65d0b41005bd73d0b41006be63d0b41026be62d0b41047ae62d0b41047ad62d0b41015be71d0b41047b671d0b41047b
  | 26 => 0x13eef21d895100cfe70d8951004fd70d895100cfc70d8951006ee20d8951006ec20d895113ef710d8951005be7498951005bd7498951006bf6498951006bc6498951005de7398951005dd7398951006ef6298951005bf7458951005bc7458951006bf6458951006bc6458951006bf6418951006bc6418951006ed62189510267d7518951044fe7418951004fd7418951194fe7318951004fd7318951026ef211895110eed211895100cfe7018951004fd701895100cfc70189510067e50189510067c5018951006ee2018951026ec201895110cfe76d4951006bf64d4951006bc64d495110d7e76d49510067e76d49510057d74d49510073f64d49510067c64d49510073c64d49510063c64d49510057d73d49510067c63d49510267c62d49510157e71d49510157c71d495105e7f61d49510857e70d49510857c70d495113f7710d4951014fe769495111d7d7594951005be7494951005bd7494951006bf6494951006bc6494951005de7394951005dd7394951006ef6294951026ec6294951015f67194951005f57194951014fc7654951006bf6454951006bc6454951006ef6254951006ec6254951005f77154951015f471549510157c765495111e7c76549510147c76549510057f74549510073f64549510067c64549510073c64549510063c64549510057f73549510067c63549510076f72549510076f62549510267c62549510076c62549510066c62549510077771549510157e71549510157c715495111f74715495111e7f61549510857e70549510857c705495111f77105495113cfe761495113d7e7514951006bf6414951006bc6414951004fe76d0951004fd76d0951044fc76d09510057e75d09510057d75d0951006bf64d0951046bc64d09510073f54d0951004fe7690951004fd7690951024fc76909510057e75909510057d7590951006bf6490951006bc6490951005de7390951005dd7390951004ff7650951004fe7650951004fc76509510057e75509510057d7550951006bf6450951006bc64509510073f5450951004fe7610951004fd7610951024fc76109510057e75109510057d7510951006bf6410951046bc6410951004fe768c951004fd768c951024fc768c9510057e758c9510057d758c951005be748c951005bd748c951006bf648c951006bc648c951006ef628c951026ec628c9510076f528c951004ff764c951004fe764c951004fc764c9510057e754c9510057d754c951006bf644c951006bc644c951006ef624c951006ec624c9510076f524c951004fe760c951004fd760c951024fc760c9510057e750c9510057d750c951006bf640c951006bc640c951007cd320c951015f675d45510177675d4551016f765d45510177765d4551007b764d4551007b464d455105f7754d45510077554d455105f7752d
  | 27 => 0xc72583510067f52583510067d525835104ef6515835105efb505835108e7e505835108e7c505835105ef8505835108efa1058351024fe72d9151004fd72d915117ebf41d915100cfe70d9151004fd70d915100cfc70d9151006be40d9151006bc40d915117f3f75d915117f3e51d915117f3c51d915117fb451d9151006be60d9151006bc60d91510073e50d91510073c50d915117fb710d915117ebf75d915117ebd75d9151006bf72d9151006be72d9151006bd72d9151006bc72d915117ebf71d915117ebe71d915117ebd71d915117ebc71d915117ebf51d915117ebe51d915117ebc51d915117ebf21d915117ebe21d915117ebd21d915117ebc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d9151006be50d9151006bc50d9151006be20d9151006bc20d915117ebf10d915117ebe10d915117ebd10d915117ebc10d9151006bf6499151006bd64191510467d7519151024fe7219151004fd7219151046bf411915114ebd411915100cfe7019151004fd701915100cfc70191510067e50191510067c5019151006be4019151046bc401915114ef7101915117dbe7619151006be761915114f3d751915114f3e511915114f3c511915114fb45119151006be6019151006bc60191510073e50191510073c501915114fb71019151046bf751915114ebd751915114e3d7519151046bf7219151006be7219151006bd7219151046bc7219151046bf711915114ebe711915114ebd7119151046bc711915114ebf511915114ebe511915114ebd511915114ebc511915114ebf211915114ebe211915114ebd211915114ebc2119151046bf7019151006be7019151006bd7019151046bc7019151006be50191510063e5019151006bc50191510063c5019151006be2019151006bc201915114ebf101915114eb7101915114ebe101915114ebd101915114ebc101915114cfe76d515117ebf64d5151006bc64d515114d7e76d51510067e76d515117f3f64d51510467c64d51510073c64d51510063c64d51510057d72d51510157e71d51510157c71d515105e7f61d515117f3e41d515117f3c41d51510857e70d51510857c70d515117f7710d5151014fe769515115d7d7595151006bf6495151046bc64951510073f5495151015f67195151005f57195151014fc7655151006bf6455151006bc6455151005f77155151015f471551510157c765515115e7c76551510147c76551510073f74551510073f64551510467c64551510073c64551510057f72551510077771551510157e71551510157c715515115f74715515115e7f61551510857e70551510857c705515115f77105515117cfe761515117d7e7515151006bf6415151046bc6415151006bf64d8951006bc64d8951044fe74d8951004fd74d8951194fe73d8951004fd73d8951
  | 28 => 0x935100cfc70593510157d76d535105e7d76d53510147d76d53510467e64d535105f3e64d53510063e64d535105f3d64d53510057d72d53510157e71d535105f7671d535105f7571d53510157c71d535117f3e41d535117f3c41d535108d7e70d535105d7c70d535115cfd769535105f3f549535116cff765535115f76515535116d7f76553510067f765535105f3f74553510467e64553510057f72553510157e71553510157c715535108d7e705535108d7c7055351005be7498b51005bd7498b51005de7398b51005dd7398b5105eef6298b51014fe7598b510267e7598b51044fe7498b51026be7498b51004be7498b51004fd7498b51026bd7498b51004bd7498b51194fe7398b51026de7398b51004de7398b51004fd7398b51026dd7398b51004dd7398b5105eef5298b51026ec5298b51026ef2198b5112eed2198b5100cfe7098b51004fd7098b5100cfc7098b510067e5098b510067c5098b5105eec6258b51014fc7558b51004ff7458b51044fc7458b51004ff7358b51194fc7358b5105eef5258b5105eec5258b5111eef2158b51004ff7058b5100cfe7058b5100cfc7058b510157d76d4b5105e7d76d4b510147d76d4b510057d74d4b510067e64d4b510057d73d4b510067e63d4b510267e62d4b5105f6e62d4b5105f6d62d4b510157e71d4b5105f7671d4b5105f7571d4b510157c71d4b5108d7e70d4b5105d7c70d4b5111cfd7694b51005be7494b51005bd7494b51005de7394b51005dd7394b5112cff7654b5112d7f7654b510067f7654b510057f7454b510067e6454b510057f7354b510067e6354b5105f6f7254b510267e6254b510157e7154b510157c7154b5108d7e7054b5108d7c7054b51044ff76d0b5105cfe76d0b51004fd76d0b5105d7e75d0b510057d75d0b510073f54d0b51006ee62d0b51006ed62d0b51024ff7690b5105cfe7690b51004fd7690b5105d7e7590b510057d7590b51006be6490b51006bd6490b51005de7390b51005dd7390b51004ff7650b51004fd7650b5105cfc7650b5105d7e7550b510057d7550b510073f5450b51024ff7610b5105cfe7610b51004fd7610b5105d7e7510b510057d7510b51046be6410b51006bd6410b51026ee6210b51006ed6210b51024ff768cb5105cfe768cb51004fd768cb5105d7e758cb510057d758cb51005be748cb51005bd748cb51006de638cb51006dd638cb510076f528cb51004ff764cb51004fd764cb5105cfc764cb5105d7e754cb510057d754cb510076f524cb51024ff760cb5105cfe760cb51004fd760cb5105d7e750cb510057d750cb51026ee620cb51006ed620cb51007cd320cb5100cff76583510157c755835105ef8605835105f785058351014fc755835108e7c75583510147c7558351004ff7458351044fc7458351004ff7258351024f
  | 29 => 0x26ec4298832014fe719883200cfe7098832004fd76d48320267f65d48320267c65d4832006ee62d4832004ff76548320267f65548320267c6554832004fd76d0832026bf64d0832026bc64d0832006ee62d0832004ff7650832026bf6450832026bc64508320276e758c8320276d758c832006ee658c832026ec658c832027ae748c832027ad748c832006ee648c832026ec648c832195ed738c832005cd738c832196ee638c832027ce638c832004ff764c832195ef764c832006ef764c832004ef764c832006ee654c832196ec654c832006ee644c832196ec644c832025ef734c832196ee634c832197ce634c832007cf534c832197ce534c832007cd534c832197cc534c832007cf434c832197ce434c832007cd434c832197cc434c832217ce314c832197cc314c83220fce304c832197cc304c832007cf764c832005cf764c832006cf764c832007cf754c832007ce754c832007cd754c832007cc754c832027cf654c832007ce654c832006ce654c832007cd654c832027cc654c832006cc654c832007cf744c832007ce744c832007cd744c832007cc744c832027cf644c832007ce644c832006ce644c832007cd644c832027cc644c832006cc644c832007cf544c832007ce544c832007cd544c832007cc544c832007cf714c832217ce714c832007cd714c832217cc714c832027cf614c832217ce614c832027cc614c832217ce514c832217cc514c832217ce414c832217cc414c832007cf704c83220fce704c832007cd704c83220fcc704c832027cf604c83220fce604c832027cc604c83220fce504c83220fcc504c83220fce404c83220fcc404c832217cf104c83220fce104c83220fcc104c832014ff7658432005bf7458432005bc7458432007cd3258432026f46158432004ff755843205cfc7558432004ff7458432006bf7458432004bf7458432044fc7458432006bc7458432004bc7458432006ee3258432006ed3258432006cd3258432026f72158432026f42158432004ff705843200cfe705843200cfc705843209ef7105843200cff76580320057f75580320057c7558032007cd3258032026f86058032004ff75580320067f75580320047f755803205cfc75580320067c75580320047c7558032004ff7458032044fc7458032006ee3258032006ed3258032006cd3258032004ff7158032014fe7158032014fc7158032026fb2058032026f82058032096fa105803205ebf6499351014fe75993510467e759935105ebf5499351046bc5499351024fe7299351004fd7299351046bf419935116ebd419935100cfe7099351004fd709935100cfc70993510067e50993510067c509935105ebc6459351014fc755935105ebf545935105ebc5459351004ff7259351024fc725935115ebf4159351004ff705935100cfe705
  | 30 => 0xd74d8132014fe71d8132004fd71d8132014fc71d81320a6f850d81320a6fa20d81320057f75581320057c75581320a6f86058132044fe74d9432026be74d9432004be74d9432004fd74d9432026bd74d9432004bd74d9432024fe72d9432026ee72d9432004ee72d9432014fe71d9432004fd71d9432014fc71d943200cfe70d9432004fd70d943200cfc70d94320067e50d94320067c50d9432004fd76994320267f6599432024fe7599432044fe7499432004fd7499432024fe72994320267e52994320267c5299432014fe7199432004fd7199432014fc719943200cfe7099432004fd709943200cfc70994320267c6559432024ff75594320267f7559432004ff7459432044fc7459432024fc72594320267e52594320267c5259432004ff7159432014fe7159432014fc7159432004ff705943200cfe705943200cfc705943205cfe75194320267e7519432044fe7419432004fd7419432024fe7219432026ee7219432014fe7119432004fd7119432014fc711943200cfe7019432004fd701943200cfc70194320067e501943205e7c501943205cfe75d90320267e75d90320047e75d9032004fd75d90320267d75d90320047d75d9032024fe72d9032026ee72d9032004ee72d9032014fe71d9032004fd71d9032014fc71d9032006be41d9032006bc41d903200cfe70d9032004fd70d903200cfc70d9032004fd7699032026bf649903205cfe7599032004fd7599032024fe7499032024fe7299032026be4299032026bc4299032014fe7199032004fd7199032014fc719903200cfe7099032004fd709903200cfc7099032026bc6459032004ff755903205cfc7559032024ff7459032026bf7459032024fc7259032026be4259032026bc4259032004ff7159032014fe7159032014fc7159032004ff705903200cfe705903200cfc705903205cfe7519032004fd7519032044fe7419032026be7419032024fe7219032026ee7219032014fe7119032004fd7119032014fc7119032006be4119032046bc411903200cfe7019032004fd701903200cfc701903205cff76d5032024fe76d5032004fd76d5032024fc76d5032006be64d5032006bd64d5032044ff7695032024fe7695032004fd7695032024fc76950320067e65950320067d65950320073f5495032004ff7655032024fe7655032004fd7655032024fc7655032044ff7615032024fe7615032004fd7615032024fc761503205e7e65150320067d6515032046be6415032006bd6415032025ee7215032005ed7215032024ff759883205cfe75988320267e75988320047e7598832004fd75988320267d75988320047d7598832024fc7598832024ff7498832044fe7498832026be7498832004be7498832004fd7498832026bd7498832004bd7498832024fc7498832026ec5298832
  | 31 => 0x4932005dd73d4932006ee76d4932004ee76d4932006ef65d49320076f65d4932006ed65d49320076c65d4932005ee74d49320076e54d49320076c54d4932195ee73d4932007ce73d4932005ce73d4932007cd73d4932237cf53d4932005ed71d4932005ed70d4932004fe76949320067e65949320067d6594932005be7494932005bd7494932005de7394932005dd73949320075f5394932005ee72949320076f529493205cff7654932004fd7654932004fc76549320067f65549320067c6554932005df7354932005dc7354932004fe761493205e7e65149320067d65149320075f53149320076d5214932005ee7614932006ee7614932005ee75149320076e7514932006ef65149320076e6514932006ed65149320076d6514932005ee7414932027cf7314932195ee7314932027cc73149320076f5314932237cf53149320074f53149320076d5314932237cc5314932005ed7114932005ed701493222f6e501493222f6c5014932004fe76d0932006bf64d0932046bc64d0932005de73d0932005dd73d0932006ee76d0932004ee76d0932005ee75d0932005ec75d0932006ef64d0932007af64d0932006ed64d0932007ac64d0932007af54d0932007ac54d0932195ee73d0932007ce73d0932005ce73d0932007cd73d0932007cf53d0932007cc53d0932227cf43d0932005ed71d0932005ed70d0932004fe76909320057e75909320057d7590932006be6490932006bd6490932005de7390932005dd73909320079f4390932005ee7290932007af4290932044ff7650932004fd7650932004fc7650932006bf6450932006bc6450932005df7350932005dc7350932004fe7610932046be6410932006bd64109320079f4310932007ad4210932005ee7610932006ee7610932005ee7510932005ec7510932005ee7410932007ae7410932006ef6410932007ae6410932006ed6410932007ad6410932027cf7310932195ee7310932027cc7310932007cf5310932007cc5310932007af4310932227cf43109320078f4310932007ad4310932227cc4310932005ed711093221fae411093221fac4110932005ed70109320057e758c9320057d758c932005be748c932005bd748c932005de758c9320275e758c9320055e758c9320275d758c932025dc758c932005de748c9320279e748c9320059e748c9320279d748c932025dc748c932007cf628c932007cf528c932027cc528c932007cf428c932027cc428c932005dd718c932005dd708c932014fe76d85320aef661d853205cfe75d8532004fd75d8532044fe74d8532004fd74d85320aef441d85320aef621d853200cfe70d8532004fd70d853200cfc70d8532005bf7458532005bc74585320aef4615853200cfe76d81320a6fa60d813205cfe75d8132004fd75d8132044fe74d8132004f
  | 32 => 0x67e65582320067d6558232006be6458232006bd6458232026f86058232004ff755823205cfc7558232004ff7458232044fc7458232006df3258232004ff7158232014fe7158232014fc71582320b6fa3058232026fb2058232026f820582320b6fa1058232005be74d9532005bd74d9532044fe74d9532006be74d9532004be74d9532004fd74d9532006bd74d9532004bd74d95320065f53d9532006ed72d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95320067e50d95320067c50d95320067f659953205cfe7599532044fe7499532004fd7499532004fd729953205eed7299532014fe7199532004fd7199532014fc719953200cfe7099532004fd709953200cfc7099532005fb70595320a5f870595320067f7559532004ff7459532044fc7459532004ff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff7059532006fb7059532004fb705953200cfe705953200cfc7059532006f8705953200cf87059532004fe76195320067d651953205e7e7519532044fe7419532004fd7419532014fe7119532004fd7119532014fc711953200cfe7019532004fd701953200cfc70195320067e501953205e7c50195320057e75d91320057d75d913205cfe75d91320067e75d91320047e75d9132004fd75d91320067d75d91320047d75d9132006ed72d9132014fe71d9132004fd71d9132014fc71d9132006be41d9132006bc41d913200cfe70d9132004fd70d913200cfc70d9132006bf649913205cfe7599132004fd7599132044fe7499132004fd7299132046ed7299132014fe7199132004fd7199132014fc719913200cfe7099132004fd709913200cfc7099132005f771591320adf47159132004ff755913205cfc7559132006bf7459132004ff7259132006ef7259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff705913200cfe705913200cfc7059132004fe7619132006bd641913205cfe7519132004fd7519132046be7419132014fe7119132004fd7119132014fc7119132006be4119132046bc411913200cfe7019132004fd701913200cfc701913205cff76d5132004fe76d5132004fd76d513205cfc76d5132006be64d5132006bd64d5132005ee72d5132005ed72d5132044ff7695132004fe7695132004fd7695132044fc76951320067e65951320067d65951320073f5495132005ee7295132005ed7295132004ff7655132004fe7655132004fd7655132004fc7655132005ef7255132005ec7255132044ff7615132004fe7615132004fd7615132044fc761513205e7e65151320067d6515132046be6415132006bd6415132004fe76d49320067f65d493205e7c65d4932005de73d
  | 33 => 0xe6494e32006bd6494e320075f5394e32005ed7294e320067e6554e320067d6554e32006be6454e32006bd6454e32005ef7254e32025ec7254e3205e7e6514e320067d6514e32006be6414e32006bd6414e320067e65d0e320067d65d0e32046be64d0e32006bd64d0e32025ee72d0e32005ed72d0e320057e7590e320057d7590e320067e6590e320067d6590e32006be6490e32006bd6490e32005ed7290e320067e6550e320067d6550e32006be6450e32006bd6450e32005ef7250e32025ec7250e320067e6510e320067d6510e32046be6410e32006bd6410e3205e7e65d4a320067d65d4a32006be64d4a32006bd64d4a320276e52d4a32005ed76d4a32006ed76d4a32006ef65d4a320076e65d4a32006ed65d4a320076d65d4a320066d65d4a32005ee74d4a32007ae64d4a32007ad64d4a320076e54d4a320076c54d4a32195ee73d4a320076e53d4a320076c53d4a32005ed71d4a32005ed70d4a320067e6554a320067d6554a32006be6454a32006bd6454a320276c5254a32025ed7614a32026ed7614a320276e7514a32026ef6514a320276e6514a32006ed6514a320276d6514a32005ee7414a32027ae6414a32027ad6414a32195ee7314a32027ce7314a32005ce7314a32027cd7314a320076f5314a320076d5314a32005ed7114a32005ed7014a322476e5014a322476c5014a320067e65d0a320067d65d0a32046be64d0a32006bd64d0a32027ae42d0a32005ed76d0a32006ed76d0a32005ee75d0a32005ec75d0a320076e65d0a320076d65d0a32006ef64d0a32007ae64d0a32006ed64d0a32007ad64d0a32006ad64d0a32007af54d0a32007ac54d0a32195ee73d0a32007ae43d0a32007ac43d0a32005ed71d0a32005ed70d0a320067e6550a320067d6550a32006be6450a32006bd6450a32027ac4250a32025ed7610a32026ed7610a32005ee7510a32025ec7510a320276e6510a320276d6510a32027ae7410a32026ef6410a32027ae6410a32006ed6410a32027ad6410a32195ee7310a32027ce7310a32027cd7310a32007af4310a32007ad4310a32005ed7110a3223fae4110a3223fac4110a32005ed7010a320067e65cca320067d65cca32006be64cca32006bd64cca32005ed76cca32196ed76cca32005ee75cca321976e75cca320056e75cca321976d75cca32195ec75cca320076e65cca320076d65cca32005ee74cca32197ae74cca32005ae74cca32197ad74cca32195ec74cca32007ae64cca32007ad64cca32197ce53cca32007cd53cca320067e65586320067d6558632006be6458632006bd6458632026f46158632004ff755863205cfc7558632004ff7458632044fc7458632006df32586320bef63158632026f72158632026f42158632004ff705863200cfe705863200cfc70586320bef71058632
  | 34 => 0x9232046bf7399232006bd7399232026be7299232026bc7299232026be5299232026bc5299232026bc3299232046bf7199232006be7199232006bd7199232046bc7199232006be5199232006bc5199232006be3199232006bc3199232026bf2199232006be2199232026bc2199232046bf7099232006be7099232006bd7099232046bc7099232006be5099232006bc5099232006be3099232006bc3099232026bf2099232006be2099232026bc2099232006bf1099232006be1099232006bc10992320067e65592320067d6559232026bc6459232004ff755923205cfc7559232026bf7459232006ec7259232026be4259232026bc4259232004ff7159232014fe7159232014fc7159232006be4159232006bc4159232004ff705923200cfe705923200cfc7059232006be4059232006bc4059232006bf7659232026bf6559232006be65592320273e65592320063e6559232006bd65592320273d65592320063d6559232026bc6559232027ac7259232026bf6159232006be6159232026bc6159232026bf6059232006be6059232026bc6059232006bf7559232006be7559232006bd7559232006bc7559232006bf7359232006bd7359232026be7259232026bc7259232006ac7259232026be5259232026bc5259232026bc3259232006bf7159232006be7159232006bd7159232006bc7159232006be5159232006bc5159232006be3159232006bc3159232026bf2159232006be2159232026bc2159232006bf7059232006be7059232006bd7059232006bc7059232006be5059232006bc5059232006be3059232006bc3059232026bf2059232006be2059232026bc2059232006bf1059232006be1059232006bc105923205cfe75192320267e75192320047e7519232004fd75192320267d75192320047d7519232026be7419232026dd7319232026ee7219232014fe7119232004fd7119232014fc711923200cfe7019232004fd701923200cfc701923205cff76d5232024fe76d5232004fd76d5232024fc76d523205e7e65d52320067d65d5232006be64d5232006bd64d5232025ee72d5232005ed72d5232044ff7695232024fe7695232004fd7695232024fc76952320067e65952320067d6595232046be6495232006bd64952320073f5495232025ee7295232005ed7295232004ff7655232024fe7655232004fd7655232024fc76552320067e65552320067d6555232006be6455232006bd6455232005ef7255232025ec7255232044ff7615232024fe7615232004fd7615232024fc761523205e7e65152320067d6515232046be6415232006bd6415232005de7315232005dd731523205e7e65d4e320067d65d4e32006be64d4e32006bd64d4e32025ee72d4e32005ed72d4e320067e6594e320067d6594e32005be7494e32005bd7494e32006b
  | 35 => 0x267f61996320067e61996320267c61996320267f60996320067e60996320267c609963205e7f74996320067e74996320067d749963205e7c749963205e7f73996320067d73996320267e72996320267c72996320267e42996320267c42996320267c329963205e7f71996320067e71996320067d719963205e7c71996320067e41996320067c41996320067e31996320067c31996320267f21996320067e21996320267c219963205e7f70996320067e70996320067d709963205e7c70996320067e40996320067c40996320067e30996320067c30996320267f20996320067e20996320267c20996320067f10996320067e10996320067c10996320267c65596320267f7559632004ff7459632044fc7459632006ec72596320267e52596320267c5259632004ff7159632014fe7159632014fc71596320067e51596320067c5159632004ff705963200cfe705963200cfc70596320067e50596320067c50596320067f76596320267f64596320267c64596320276c72596320267f61596320067e61596320267c61596320267f60596320067e60596320267c60596320067f74596320067e74596320067d74596320067c74596320067f73596320067d73596320267e72596320267c72596320066c72596320267e42596320267c42596320267c32596320067f71596320067e71596320067d71596320067c71596320067e41596320067c41596320067e31596320067c31596320267f21596320067e21596320267c21596320067f70596320067e70596320067d70596320067c70596320067e40596320067c40596320067e30596320067c30596320267f20596320067e20596320267c20596320067f10596320067e10596320067c10596320267e7519632044fe7419632026be7419632004be7419632004fd7419632026bd7419632004bd7419632026dd7319632026ee7219632014fe7119632004fd7119632014fc711963200cfe7019632004fd701963200cfc701963205cfe75d92320267e75d92320047e75d9232004fd75d92320267d75d92320047d75d9232026dd73d9232026ee72d9232014fe71d9232004fd71d9232014fc71d923200cfe70d9232004fd70d923200cfc70d92320067e65992320067d6599232026bf649923205cfe7599232004fd7599232026be4299232026bc4299232014fe7199232004fd7199232014fc7199232006be4199232046bc419923200cfe7099232004fd709923200cfc7099232006be4099232046bc4099232026bf6599232006be65992320273e65992320063e6599232006bd65992320273d65992320063d6599232026bc6599232027ac7299232026bf6199232006be6199232026bc6199232026bf6099232006be6099232026bc6099232046bf7599232006be7599232006bd7599232046bc759
  | 36 => 0xd7690c420057e7590c420057d7590c42005bd7490c42005ed7290c42004ff7650c42005bf7650c42006bf7650c42004bf7650c42006be6550c42006bc6550c42045bf7350c420479f7350c42196be6350c42005bf7250c42007ae7250c42007ad7250c420cdbe7150c420cdbc7150c42024ff759884205cfe75988420267e75988420047e7598842004fd75988420267d75988420047d7598842024fc7598842026de7398842026dd7398842006bf4398842006bd4398842014fe719884200cfe7098842004fd76d48420267f65d48420267c65d4842004ff76548420267f65548420267c6554842006be65d0842026bc65d0842005bd73d0842006be63d0842025bd72d0842026be62d08420cdbe71d0842045bc71d08420276e75908420276d7590842045ed7490842046ee6490842027ae6490842027ce7390842005ed7390842027cd7390842005cd7390842047af4390842007ad4390842257ae4190842047ac4190842004ff7650842025bf7650842006bf7650842004bf7650842006be6550842026bc6550842005bf7350842006be6350842025bf7250842026be6250842027ae5250842007ad52508420cdbe71508420cdbc715084224fae2050842027ac2050842045ef7650842006ef7650842004ef7650842025ef7450842027af7450842046ee6450842047ae6450842047ae5450842007ad5450842005ef7350842047af4350842007ad435084224fae4050842047ac4050842014ff7658442026f46158442047b44158442004ff755844205cfc7558442004ff7358442194fc7358442006bf4358442006bd4358442006bf4258442006ee4258442006bd4258442006ed4258442046f741584420cebe41584420cebc4158442046f44158442026f72158442026f42158442004ff705844200cfe705844200cfc70584420cef7105844200cff76580420057f75580420057c7558042026f86058042004ff75580420067f75580420047f755804205cfc75580420067c75580420047c7558042004ff7358042194fc7358042006bf4358042006bd4358042006bf4258042006bd4258042004ff7158042014fe7158042014fc7158042006be4158042006bc4158042046fb4058042046f84058042026fb2058042026f820580420c6fa1058042044fe74d9632026be74d9632004be74d9632004fd74d9632026bd74d9632004bd74d9632026dd73d9632026ee72d9632014fe71d9632004fd71d9632014fc71d963200cfe70d9632004fd70d963200cfc70d96320267f6599632044fe7499632004fd74996320267e52996320267c5299632014fe7199632004fd7199632014fc71996320067e519963205e7c519963200cfe7099632004fd709963200cfc70996320067e509963205e7c50996320267f64996320267c64996320276c7299632
  | 37 => 0x8142004fd71d8142014fc71d81420d6fa40d81420d6fa20d81420057f75581420057c75581420d6f86058142044fe74d9442026be74d9442004be74d9442194fe73d9442026de73d9442004de73d9442004fd73d9442026dd73d9442004dd73d9442024fe72d9442026ee72d9442014fe71d9442004fd71d9442014fc71d944200cfe70d9442004fd70d944200cfc70d94420067e50d94420067c50d9442004fd76994420267f6599442024fe7599442044fe74994420467e54994420467c5499442194fe7399442004fd7399442024fe72994420267e52994420267c5299442014fe7199442004fd7199442014fc7199442006be4199442006bc419944200cfe7099442004fd709944200cfc70994420267c6559442024ff75594420267f7559442044fc74594420467e54594420467c5459442004ff7359442194fc7359442024fc72594420267e52594420267c5259442004ff7159442014fe7159442014fc7159442004ff705944200cfe705944200cfc705944205cfe75194420267e7519442044fe7419442026be7419442194fe7319442004fd7319442024fe7219442026ee7219442014fe7119442004fd7119442014fc7119442006be4119442046bc411944200cfe7019442004fd701944200cfc70194420067e501944205e7c5019442044ff759904205cfe7599042004fd7599042044fc7599042046bc5499042014fe719904200cfe7099042004fd76d5042006be64d50420473e54d5042004ff76550420057e7598c420057d7598c42026df6398c4205cfe7598c421967e7598c420047e7598c42004fd7598c421967d7598c420047d7598c42046df4398c42196dc4398c42196ee7298c42026de3298c42026dc3298c42014fe7198c42004fd7198c42014fc7198c42006be4198c42006bc4198c4200cfe7098c42004fd7098c4200cfc7098c42026dc6358c42004ff7558c4205cfc7558c42046df4358c42046dc4358c42026de3258c42026dc3258c42004ff7158c42014fe7158c42014fc7158c42004ff7058c4200cfe7058c4200cfc7058c4205cff76d4c42024fe76d4c42004fd76d4c420067f65d4c4205e7c65d4c42006de63d4c42006dd63d4c42194ff7694c42024fe7694c42004fd7694c420067e6594c420067d6594c42045be7494c42005bd7494c420075f5394c42025ee7294c42005ed7294c42004ff7654c42004fd7654c42024fc7654c420067f6554c420067c6554c42194ff7614c42024fe7614c42004fd7614c4205e7e6514c420067d6514c42045be7414c42005bd7414c42196de6314c42006dd6314c42025ee7214c42005ed7214c42006be65d0c42046bc65d0c42196be63d0c420479e63d0c420069e63d0c420479d63d0c42047ae72d0c42005bd72d0c42047ad72d0c420cdbe71d0c42045bc71d0c42004f
  | 38 => 0x73f5495142004fc76551420067f65551420067c6555142005ef7255142005ec7255142004fe761514205e7e65151420067d65151420073d5415142005be7615142006be7615142005be75151420073e7515142006bf65151420073e6515142006bd65151420073d6515142005be7315142025be7215142005bd711514214ebe611514214ebc6115142005bd70151422673e50151422673c501514205cfe75d8d42004fd75d8d42006bf54d8d42006bc54d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420057e7598d420057d7598d42006df6398d42005f77158d420ddf47158d42006dd6318d4205cfe7518d42004fd7518d42014fe7118d42004fd7118d42014fc7118d4200cfe7018d42004fd7018d4200cfc7018d42004fe76d4d42004fd76d4d4205cfc76d4d420067f65d4d4205e7c65d4d42005be74d4d42005bd74d4d420073c54d4d42005ee72d4d42005ed72d4d42004fe7694d42004fd7694d42194fc7694d42005be7494d42005bd7494d420075f5394d42005ee7294d42005ed7294d42004ff7654d42004fe7654d42004fc7654d420067f6554d420067c6554d42005bf7454d42005bc7454d420073c5454d42004fe7614d42004fd7614d42194fc7614d420057e7590d420057d7590d42006df6390d42196dc6390d420079f4390d42005ee7290d42005ed7290d42005be7590d420073e7590d420053e7590d420073d7590d42005bc7590d42006bf6390d420079f6390d420079c6390d42025be7290d42007ae7290d42005ae7290d42007ad7290d42005bd7190d4225ebe6190d4225ebc6190d42005bd7090d42005ef7250d42005ec7250d42004fe76d49420067f65d494205e7c65d4942005be74d4942005bd74d49420073c54d4942004fe7694942005be7494942005bd7494942005de7394942005dd73949420076f529494205cff7654942004fd7654942004fc76549420067f65549420067c6554942005bf7454942005bc74549420073c5454942004fe76149420076d5214942007af54d0942047ac54d0942006ef63d0942007ae43d0942005ed71d09420057e75909420057d7590942005de7390942005dd7390942005be75909420273e75909420053e75909420273d7590942025bc7590942005be73909420279e73909420059e73909420279d7390942006bf6390942007af6290942005bd71909420eebe61909420eebc6190942005bd7090942014fe76d85420def661d854205cfe75d8542004fd75d8542194fe73d8542004fd73d85420def641d85420def431d85420def621d854200cfe70d8542004fd70d854200cfc70d85420def710d85420def4615854200cfe76d81420d6fa60d814205cfe75d8142004fd75d8142194fe73d8142004fd73d8142014fe71d
  | 39 => 0xe63d0e420079e63d0e420069e63d0e420079d63d0e42005bd72d0e420edbe71d0e420edbc71d0e420067e6590e420067d6590e42025ee7290e42005ed7290e42046bc4198a4205e7e65d4a420067d65d4a42006de63d4a42006dd63d4a420276e52d4a420067e6554a420067d6554a42006de6354a42006dd6354a420276c5254a420067e65d0a420067d65d0a42006de63d0a42006dd63d0a42025bd76d0a42006bd76d0a42006be65d0a420273e65d0a420063e65d0a420273d65d0a42026bc65d0a42005bd73d0a42006be63d0a420279e63d0a420069e63d0a420279d63d0a42027ae52d0a42007ad52d0a420edbe71d0a420edbc71d0a42005ed76d0a42046ed76d0a420076e65d0a420076d65d0a42047ae54d0a42007ad54d0a42007ce63d0a42006ed63d0a42007cd63d0a42006cd63d0a42047af43d0a42005ed71d0a420067e65586420067d6558642006de6358642006dd6358642026f461586420efb64158642004ff755864205cfc7558642004ff7358642194fc7358642006bf4358642006bf42586420eebe41586420eef641586420eebc4158642026f72158642026f42158642004ff705864200cfe705864200cfc70586420eef710586420067e65582420067d6558242006de6358242006dd6358242026f86058242004ff755824205cfc7558242004ff7358242194fc7358242006bf4358242006bf4258242004ff7158242014fe7158242014fc7158242006be4158242006bc41582420e6fa4058242026fb2058242026f820582420e6fa1058242006bd74d9542194fe73d9542004fd73d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95420067e50d95420067c50d95420067f659954205cfe7599542004fd749954205ebd7499542194fe7399542004fd7399542004fd729954205eed7299542014fe7199542004fd7199542014fc719954200cfe7099542004fd709954200cfc70995420067f7559542004ff7459542006bf7459542004ff7359542194fc7359542004ff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc7059542004fe76195420067d651954205e7e7519542194fe7319542004fd7319542014fe7119542004fd7119542014fc711954200cfe7019542004fd701954200cfc70195420067e501954205e7c5019542004fe76d51420067f65d514205e7c65d5142005ee72d5142005ed72d5142006be76d5142004be76d5142006bf65d51420073f65d51420063f65d5142006bd65d51420073c65d5142005be73d5142025be72d5142007ae72d5142005ae72d5142007ad72d5142005bd71d514217ebe61d514217ebc61d5142005bd70d5142004fe76951420067e65951420067d6595142005be7495142
  | 40 => 0x8e420079d7498e42026df6198e42006de6198e42026dc6198e420079e4198e420079c4198e42026df6098e42006de6098e42026dc6098e42196df7598e42006de7598e42006dd7598e42196dc7598e42196df7498e42006df5498e42006de5498e42006dd5498e42006dc5498e42026dc7298e42026de5298e42026dc5298e42026dc4298e42196df7198e42006de7198e42006dd7198e42196dc7198e42006de5198e42006dc5198e42006de4198e420069e4198e42006dc4198e420069c4198e42026df2198e42006de2198e42026dc2198e42196df7098e42006de7098e42006dd7098e42196dc7098e42006de5098e42006dc5098e42006de4098e42006dc4098e42026df2098e42006de2098e42026dc2098e42006df1098e42006de1098e42006dc1098e420067e6558e420067d6558e42026dc6358e42004ff7558e4205cfc7558e42026de3258e42026dc3258e42004ff7158e42014fe7158e42014fc7158e42006de3158e42006dc3158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42006dc3058e42006df7658e42026df6558e42006de6558e420275e6558e420065e6558e42006dd6558e420275d6558e420065d6558e42026dc6558e420079d7458e42026df6158e42006de6158e42026dc6158e420079e4158e420079c4158e42026df6058e42006de6058e42026dc6058e42006df7558e42006de7558e42006dd7558e42006dc7558e42006dd7458e42006df5458e42006de5458e42006dd5458e42006dc5458e42026de7258e42026dc7258e42026de5258e42026dc5258e42026dc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006de5158e42006dc5158e42006de4158e42006dc4158e42026df2158e42006de2158e42026dc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006de5058e42006dc5058e42006de4058e42006dc4058e42026df2058e42006de2058e42026dc2058e42006df1058e42006de1058e42006dc1058e4205cff76d4e42024fe76d4e42004fd76d4e4205e7e65d4e420067d65d4e42006de63d4e42006dd63d4e42025ee72d4e42005ed72d4e42194ff7694e42024fe7694e42004fd7694e420067e6594e420067d6594e42005be7494e42005bd7494e42196de6394e42006dd6394e420075f5394e42025ee7294e42005ed7294e42004ff7654e42004fd7654e42024fc7654e420067e6554e420067d6554e42006de6354e42006dd6354e42194ff7614e42024fe7614e42004fd7614e4205e7e6514e420067d6514e42005be7414e42005bd7414e42196de6314e42006dd6314e420067e65d0e420067d65d0e42006de63d0e42005bd76d0e42006bd76d0e42006be65d0e420073e65d0e420063e65d0e420073d65d0e42006bc65d0e42196b
  | 41 => 0xcfc70996420067e509964205e7c50996420267f63996420267c63996420267f61996420067e61996420267c61996420073e41996420073c41996420267f60996420067e60996420267c609964205e7f74996420067d749964205e7f73996420067e73996420067d739964205e7c73996420267e72996420267c72996420267c42996420267e32996420267c329964205e7f71996420067e71996420067d719964205e7c71996420067e41996420063e41996420067c41996420063c41996420067e31996420067c31996420267f21996420067e21996420267c219964205e7f70996420067e70996420067d709964205e7c70996420067e40996420067c40996420067e30996420067c30996420267f20996420067e20996420267c20996420067f10996420067e10996420067c10996420267c65596420267f7559642004ff7359642194fc73596420267e52596420267c5259642004ff7159642014fe7159642014fc71596420067e51596420067c5159642004ff705964200cfe705964200cfc70596420067e50596420067c50596420067f76596420267f63596420267c63596420267f61596420067e61596420267c61596420073e41596420073c41596420267f60596420067e60596420267c60596420067f74596420067d74596420067f73596420067e73596420067d73596420067c73596420267e72596420267c72596420267c42596420267e32596420267c32596420067f71596420067e71596420067d71596420067c71596420067e41596420067c41596420067e31596420067c31596420267f21596420067e21596420267c21596420067f70596420067e70596420067d70596420067c70596420067e40596420067c40596420067e30596420067c30596420267f20596420067e20596420267c20596420067f10596420067e10596420067c10596420267e7519642026bd7419642194fe7319642026de7319642004de7319642004fd7319642026dd7319642004dd7319642026ee7219642014fe7119642004fd7119642014fc7119642006be4119642006bc411964200cfe7019642004fd701964200cfc701964205e7e65d52420067d65d5242025ee72d5242005ed72d52420067e65952420067d65952420073f54952420067e65552420067d6555242005ef7255242025ec725524205e7e65152420067d65152420067e6598e420067d6598e42026df6398e4205cfe7598e42004fd7598e42026de3298e42026dc3298e42014fe7198e42004fd7198e42014fc7198e42006be4198e42006bc4198e42006de3198e42196dc3198e4200cfe7098e42004fd7098e4200cfc7098e42006de3098e42196dc3098e42026df6598e42006de6598e420275e6598e420065e6598e42006dd6598e420275d6598e420065d6598e42026dc659
  | 42 => 0xc50597420467e7519742046be7419742194fe7319742046de7319742004de7319742004fd7319742046dd7319742004dd7319742046ed7219742014fe7119742004fd7119742014fc711974200cfe7019742004fd701974200cfc70197420473e54d5342005bd76d5342006bd76d5342006bf65d5342006bd65d5342005be73d5342025be72d5342005bd71d534217ebe61d534217ebc61d5342005bd70d53420473c5455342046bd76153420473e7515342046bf65153420473e6515342006bd65153420473d6515342005be7315342025be7215342047ae7215342005ae7215342047ad7215342005bd711534214ebe6115342046bc6115342005bd701534226f3e501534226f3c5015342046df6398f4205cfe7598f42004fd7598f42046df4398f42196dc4398f42014fe7198f42004fd7198f42014fc7198f4200cfe7098f42004fd7098f4200cfc7098f42006de3098f42196dc3098f42046dc6358f42004ff7558f4205cfc7558f42006bf5458f42006bc5458f42046df4358f42046dc4358f42004ff7158f42014fe7158f42014fc7158f42004ff7058f4200cfe7058f4200cfc7058f42006de3058f42006dc3058f4205cff76d4f42044fe76d4f42004fd76d4f4205e7e65d4f420067d65d4f42045be74d4f42005bd74d4f420073c54d4f42194ff7694f42044fe7694f42004fd7694f42045be7494f42005bd7494f42196de6394f42006dd6394f420075f5394f42005ee7294f42005ed7294f42004ff7654f42004fd7654f42044fc7654f420067e6554f420067d6554f42005bf7454f42045bc7454f420073c5454f42006de6354f42006dd6354f42194ff7614f42044fe7614f42004fd7614f42005ee7214f42005ed7214f4205e7e65d4b420067d65d4b42045be74d4b42005bd74d4b420073c54d4b42045be7494b42005bd7494b42005de7394b42005dd7394b420067e6554b420067d6554b42005bf7454b42045bc7454b420073c5454b42046f46158742004ff755874205cfc7558742004ff7358742194fc7358742046f74158742046f441587420fef62158742004ff705874200cfe705874200cfc7058742046f86058342004ff755834205cfc7558342004ff7358342194fc7358342004ff7158342014fe7158342014fc7158342046fb4058342046f840583420f6fa20583420f6fa1058342026bd74d9642194fe73d9642026de73d9642004de73d9642004fd73d9642026dd73d9642004dd73d9642026ee72d9642014fe71d9642004fd71d9642014fc71d964200cfe70d9642004fd70d964200cfc70d96420267f6599642194fe7399642004fd73996420267e52996420267c5299642014fe7199642004fd7199642014fc71996420067e519964205e7c5199642006be4199642006bc419964200cfe7099642004fd7099642
  | 43 => 0x8c520067e64d4c521967e63d4c5205f5e63d4c520065e63d4c5205f5d63d4c5205f6e72d4c520057d72d4c5205f6d72d4c521057e70d4c5205d7c70d4c52004fd7694c520057d7594c52005be7494c52005bd7494c5205f5f5394c52005ed7294c52004ff7654c520057f7654c520067f7654c520047f7654c520067e6454c5205d7f7354c5205f5f7354c521967e6354c520057f7254c520076e7254c520076d7254c521057e7054c521057c7054c52026be7498852026bd7498852026de7398852026dd73988520067f53988520067d5398852014fe719885200cfe70988520067e64d48520057d73d48520067e63d48520257d72d48520267e62d48521057e70d485205d7c70d485205ded759485205eee65948520276e6594852027ae7494852027ad7494852027ce7394852005ed7394852027cd7394852005cd739485205f6f53948520076d539485227f6e509485205f6c5094852004ff76548520257f76548520067f76548520047f76548520067e64548520057f73548520067e63548520257f72548520267e62548522776e21548520276c21548521057e70548521057c705485205def7654852006ef7654852004ef7654852025ef75548520276f755485205eee655485205f6e655485205f6f54548520076d5454852005ef735485205f6f53548520076d53548522776e515485205f6c5154852014ff7658452005bf7458452005bc7458452026f46158452004ff7458452006bf7458452004bf7458452044fc7458452006bc7458452004bc7458452004ff7358452194fc73584520067f53584520067d53584520067f52584520067d525845205ef7515845205ef45158452026f72158452026f42158452004ff705845200cfe705845200cfc70584520067e50584520067c505845210ef7105845200cff7658052026f8605805205f785058052004ff7458052044fc7458052004ff7358052194fc73580520067f53580520067d53580520067f5258052006ee52580520067d5258052006ed5258052004ff7158052014fe7158052014fc715805205efb50580521067e50580521067c505805205ef85058052026fb2058052026f82058052106fa1058052046be74d9742194fe73d9742004fd73d9742046ed72d9742014fe71d9742004fd71d9742014fc71d974200cfe70d9742004fd70d974200cfc70d97420467f65997420467e54997420467c5499742194fe7399742004fd7399742014fe7199742004fd7199742014fc719974200cfe7099742004fd709974200cfc70997420067e509974205e7c50997420467c65597420467f7559742006bc74597420467e54597420467c5459742004ff7359742194fc7359742004ff7159742014fe7159742014fc7159742004ff705974200cfe705974200cfc70597420067e50597420067
  | 44 => 0x1467c6015152044fe74d8d52004fd74d8d520067e54d8d520067c54d8d52014fe71d8d52004fd71d8d52014fc71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52005be7498d52005bd7498d52006df6398d52005fb7058d52115f87058d52006dd6318d52044fe7418d52004fd7418d52014fe7118d52004fd7118d52014fc7118d5200cfe7018d52004fd7018d5200cfc7018d52005be7494d52005bd7494d52006df6394d52196dc6394d520075f5394d52005ee7294d52005ed7294d520057e7494d520073e7494d520053e7494d520073d7494d520067f6394d520075f6394d520065f6394d520075c6394d520257e7294d520076e7294d520056e7294d520076d7294d520057d7194d520057d7094d522867e6094d522867c6094d52005ef7254d52005ec7254d520076e54d495205f6c54d4952006ef63d49520076e53d4952005ed70d4952005be7494952005bd7494952005de7394952005dd73949520057e74949520273e74949520053e74949520273d74949520057e73949520275e73949520055e73949520275d73949520067f63949520076f62949520057d71949520057d70949521267e60949521267c6094952014fe76d855211ef661d8552044fe74d8552004fd74d8552194fe73d8552004fd73d855211ef651d855211ef621d855200cfe70d8552004fd70d855200cfc70d8552005bf7458552005bc745855211ef4615855200cfe76d8152116fa60d8152044fe74d8152004fd74d8152194fe73d8152004fd73d8152014fe71d8152004fd71d8152014fc71d8152116fa50d8152116f830d8152116fa20d8152116fa10d8152116f8605815205e7c5499452014fe719945200cfe7099452026bf649905205ebf5499052046bc5499052194fe7399052004fd7399052026be4299052026bc4299052014fe7199052004fd7199052014fc719905200cfe7099052004fd709905200cfc70990520067e50990520067c5099052026bc645905205ebf545905205ebc5459052004ff7359052194fc7359052026be4259052026bc4259052004ff7159052014fe7159052014fc7159052004ff705905200cfe705905200cfc7059052004fd76950520067e659505205f3f5495052004ff7655052005be7498c52005bd7498c52026df6398c52044fe7498c52196be7498c52004be7498c52004fd7498c52196bd7498c52004bd7498c5205edf5398c52196dc5398c52196ee7298c52026de3298c52026dc3298c52014fe7198c52004fd7198c52014fc7198c5200cfe7098c52004fd7098c5200cfc7098c520067e5098c520067c5098c52026dc6358c52004ff7458c52044fc7458c5205edf5358c5205edc5358c52026de3258c52026dc3258c52004ff7158c52014fe7158c52014fc7158c52004ff7058c5200cfe7058c5200cfc705
  | 45 => 0xf2158e52006de2158e52026dc2158e52006df7058e52006de7058e52006dd7058e52006dc7058e52006de5058e52006dc5058e52006de4058e52006dc4058e52026df2058e52006de2058e52026dc2058e52006df1058e52006de1058e52006dc1058e52006be64d4e52006bd64d4e52006de63d4e520057d76d4e520067d76d4e520067e64d4e520073e64d4e520063e64d4e520073d64d4e521967e63d4e520075e63d4e520065e63d4e520075d63d4e520057d72d4e521257e70d4e521257c70d4e52006be6494e52006bd6494e520075f5394e52025ee7294e52005ed7294e5205e7c5098a52006be64d4a52006bd64d4a52006de63d4a52006dd63d4a520257d76d4a520067d76d4a520067e64d4a520273e64d4a520063e64d4a520273d64d4a520057d73d4a520067e63d4a520275e63d4a520065e63d4a520275d63d4a521257e70d4a521257c70d4a52005ed76d4a5205eed76d4a52007ae64d4a52007ad64d4a5205f6f54d4a520076d54d4a52007ce63d4a52006ed63d4a52007cd63d4a52006cd63d4a5205f6f53d4a52005ed70d4a52006be6458652006bd6458652006de6358652006dd6358652026f46158652004ff7458652044fc7458652004ff7358652194fc73586520067f53586520067f525865212ef65158652026f72158652026f42158652004ff705865200cfe705865200cfc70586520067e50586520067c505865212ef71058652006be6458252006bd6458252006de6358252006dd6358252026f860582521277a5058252004ff7458252044fc7458252004ff7358252194fc73582520067f53582520067f5258252004ff7158252014fe7158252014fc71582521267e5058252126fa50582521267c5058252026fb2058252026f82058252126fa1058252194fe73d9152004fd73d9152014fe71d9152004fd71d9152014fc71d9152006be41d9152006bc41d915200cfe70d9152004fd70d915200cfc70d9152006bf6499152006bd6419152194fe7319152004fd7319152014fe7119152004fd7119152014fc7119152006be4119152046bc411915200cfe7019152004fd701915200cfc7019152004fe76d5152006bf6495152046bc64951520073f5495152005ee7295152005ed72951520057e74951520067f64951520073f64951520063f64951520073c64951520057e73951520257e72951520076e72951520056e72951520076d72951520057d71951520057d70951521667e60951521667c6095152006bf6455152006bc6455152005ef7255152005ec7255152004fe76151520073d54151520057e76151520067e76151520057e74151520073e74151520067f64151520073e64151520073d64151520057e73151520257e72151520057d711515228f3e411515228f3c41151520057d70151521467e6015152
  | 46 => 0x9252026bc3259252006bf7159252006be7159252006bd7159252006bc7159252006be5159252006bc5159252006be3159252006bc3159252026bf2159252006be2159252026bc2159252006bf7059252006be7059252006bd7059252006bc7059252006be5059252006bc5059252006be3059252006bc3059252026bf2059252006be2059252026bc2059252006bf1059252006be1059252006bc1059252006be64d5252046be6495252006bd64952520073f5495252025ee7295252005ed7295252006be6455252006bd6455252005ef7255252025ec7255252006bd6415252006be6498e52006bd6498e52026df6398e52044fe7498e52004fd7498e52026de3298e52026dc3298e52014fe7198e52004fd7198e52014fc7198e52006de3198e52196dc3198e5200cfe7098e52004fd7098e5200cfc7098e520067e5098e520067c5098e52006de3098e52196dc3098e520075d7598e52026df6498e52006de6498e520279e6498e520069e6498e52006dd6498e520279d6498e520069d6498e52026dc6498e52026df6198e52006de6198e52026dc6198e52026df6098e52006de6098e52026dc6098e520075e5098e520075c5098e52196df7598e52196df7498e52006de7498e52006dd7498e52196dc7498e52006df5498e52006de5498e52006dd5498e52006dc5498e52026dc7298e52026dc5298e52026de4298e52026dc4298e52196df7198e52006de7198e52006dd7198e52196dc7198e52006de5198e52006dc5198e52006de4198e52006dc4198e52026df2198e52006de2198e52026dc2198e52196df7098e52006de7098e52006dd7098e52196dc7098e52006de5098e520065e5098e52006dc5098e520065c5098e52006de4098e52006dc4098e52026df2098e52006de2098e52026dc2098e52006df1098e52006de1098e52006dc1098e52006be6458e52006bd6458e52026dc6358e52004ff7458e52044fc7458e52026de3258e52026dc3258e52004ff7158e52014fe7158e52014fc7158e52006de3158e52006dc3158e52004ff7058e5200cfe7058e5200cfc7058e52006de3058e52006dc3058e52006df7658e520075d7558e52026df6458e52006de6458e520279e6458e520069e6458e52006dd6458e520279d6458e520069d6458e52026dc6458e52026df6158e52006de6158e52026dc6158e52026df6058e52006de6058e52026dc6058e520075e5058e520075c5058e52006dd7558e52006df7458e52006de7458e52006dd7458e52006dc7458e52006df5458e52006de5458e52006dd5458e52006dc5458e52026de7258e52026dc7258e52026dc5258e52026de4258e52026dc4258e52006df7158e52006de7158e52006dd7158e52006dc7158e52006de5158e52006dc5158e52006de4158e52006dc4158e52026d
  | 47 => 0x257e72953520057d71953520057d70953521667e60953521667c609535205f3c545535205f3e741535205f3e64153520067d641535205f3d64153520057e73153520257e721535205f6e72153520056e721535205f6d72153520057d71153522973e41153522973c41153520057d70153521467e601535205e7c601535205edf6398f52044fe7498f52004fd7498f5205edf5398f52196dc5398f52014fe7198f52004fd7198f52014fc7198f52006de3198f52196dc3198f5200cfe7098f52004fd7098f5200cfc7098f5205edc6358f52004ff7458f52044fc7458f520067e5458f520067c5458f5205edf5358f5205edc5358f52004ff7158f52014fe7158f52014fc7158f52006de3158f52006dc3158f52004ff7058f5200cfe7058f5200cfc7058f5205ef46158752004ff7458752044fc7458752004ff7358752194fc735875205ef7515875205ef4515875213ef62158752004ff705875200cfe705875200cfc705875213ef7105875205ef86058352004ff7458352044fc7458352004ff7358352194fc7358352004ff7158352014fe7158352014fc715835205efb505835205ef85058352136fa2058352026bf6499252194fe7399252004fd7399252026be4299252026bc4299252014fe7199252004fd7199252014fc7199252006be4199252046bc419925200cfe7099252004fd709925200cfc70992520067e50992520067c5099252006be4099252046bc4099252026bf6399252026bc6399252026bf6199252006be6199252026bc6199252026bf6099252006be6099252026bc60992520073e50992520073c5099252046bf7599252046bf7399252006be7399252006bd7399252046bc7399252026be7299252026bc7299252026bc5299252026be3299252026bc3299252046bf7199252006be7199252006bd7199252046bc7199252006be5199252006bc5199252006be3199252006bc3199252026bf2199252006be2199252026bc2199252046bf7099252006be7099252006bd7099252046bc7099252006be50992520063e5099252006bc50992520063c5099252006be3099252006bc3099252026bf2099252006be2099252026bc2099252006bf1099252006be1099252006bc1099252026bc6459252004ff7359252194fc7359252026be4259252026bc4259252004ff7159252014fe7159252014fc7159252006be4159252006bc4159252004ff705925200cfe705925200cfc7059252006be4059252006bc4059252006bf7659252026bf6359252026bc6359252026bf6159252006be6159252026bc6159252026bf6059252006be6059252026bc60592520073e50592520073c5059252006bd7559252006bf7359252006be7359252006bd7359252006bc7359252026be7259252026bc7259252026bc5259252026be325
  | 48 => 0xc711895400cfe7018954004fd701895400cfc7018954014fe76d855415ef661d8554024fe72d8554004fd72d855415ef651d855415ef641d855400cfe70d8554004fd70d855400cfc70d855415ef710d855415ef4615855400cfe76d8154156fa60d8154024fe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d8154156fa50d8154156fa40d8154156fa10d8154156f86058154014fe719945400cfe7099454014fe719905400cfe70990540457d74d50540467e64d50540057d72d50542a73e41d50540473c41d50541457e70d505405d7c70d505405dbd759505405ebe65950540473e65950540063e6595054005bd729505414dbe7195054045bc719505429f3e509505405f3c5095054004ff76550540457f76550540067f76550540047f76550540457f74550540467e64550540057f72550541457e70550541457c705505405dbf7655054006bf7655054004bf7655054045bf75550540473f755505405ebe655505405f3e6555054005bf725505414dbe715505414dbc7155054005de7398854005dd7398854046ef6298854194fe7398854026de7398854004de7398854004fd7398854026dd7398854004dd739885405eef5298854026ec5298854046ef4298854026ec4298854014fe7198854004fd7198854014fc7198854006be4198854006bc419885400cfe7098854004fd709885400cfc70988540067e50988540067c5098854046ec6258854004ff7358854194fc735885405eef525885405eec5258854046ef4258854046ec4258854004ff7158854014fe7158854014fc7158854004ff705885400cfe705885400cfc7058854014ff7658454046f46158454047b441584540067f54584540067d5458454004ff7258454024fc725845405ef7515845405ef45158454046f7415845414ebe415845414ebc4158454046f4415845414eb44158454004ff705845400cfe705845400cfc70584540067e50584540067c505845414ef7105845400cff7658054046f8605805405f785058054006be5458054006bd5458054004ff7258054024fc7258054004ff7158054014fe7158054014fc7158054006be4158054006bc415805405efb50580541467e50580541467c505805405ef85058054046fb4058054046f84058054146fa105805405ebf649935205ebf5499352046bc5499352194fe7399352004fd7399352014fe7199352004fd7199352014fc7199352006be4199352046bc419935200cfe7099352004fd709935200cfc709935205ebc645935205ebf545935205ebc5459352004ff7359352194fc7359352004ff7159352014fe7159352014fc7159352006be4159352006bc4159352004ff705935200cfe705935200cfc705935205f3f54953520057d76953520067d76953520067d64953520057e7395352
  | 49 => 0x8b54194fc7358b5405eef5258b5405eec5258b54004ff7158b54014fe7158b54014fc7158b54006ee2158b54006ec2158b54004ff7058b5400cfe7058b5400cfc7058b5405ef4615875417fb64158754004ff7258754024fc725875405ef7515875405ef4515875417ebe415875417ef6415875417eb6415875417ebc4158754004ff705875400cfe705875400cfc705875417ef7105875405ef86058354004ff7258354024fc7258354004ff7158354014fe7158354014fc7158354006be4158354006bc415835405efb505835405ef85058354176fa4058354046bc419925405e7c50992540457d76d52540067d76d52540057d72d52542b73e41d52540473c41d52541657e70d52541657c70d52542af3e40d52540473c40d5254005bd76d525405ebd76d525417ebe61d525417ebc61d52542b73e51d525405f3c51d5254005bd70d52542af3e50d525405f3c50d52540073d76d52540053d76d52540063d76d525405f3f72d52540073e72d52540073d72d525405f3c72d52540473f62d52540473c62d525405f3f71d52542b73e71d52540073d71d525405f3c71d52540473f61d52542b73e61d52540473c61d52542b73e21d52542b73c21d525405f3f70d52542af3e70d52540073d70d525405f3c70d52540473f60d52542af3e60d52540473c60d52542af3e20d52542af3c20d52542b73f10d52542af3e10d52542af3c10d52540073f5498a54046ef6298a54194fe7398a54004fd7398a54046ef4298a54026ec4298a54014fe7198a54004fd7198a54014fc7198a5400cfe7098a54004fd7098a5400cfc7098a540067e5098a540067c5098a54006ee2098a54026ec2098a540073f5458a54046ec6258a54006bf5458a54004ff7358a54194fc7358a54046ef4258a54046ec4258a54004ff7158a54014fe7158a54014fc7158a54004ff7058a5400cfe7058a5400cfc7058a54006ee2058a54006ec2058a540073f5458654046f461586540067f5458654004ff7258654024fc725865416ef65158654046f74158654046f44158654004ff705865400cfe705865400cfc70586540067e50586540067c50586540073f5458254046f860582541677a5058254004ff7258254024fc7258254004ff7158254014fe7158254014fc71582541667e5058254166fa50582541667a50582541667c5058254046fb4058254046f84058254166fa105825417ebe61d515417ebc61d5154005bd70d51540073f64951540057d71951541667e60951541667c6095154006bf54d89540067e54d8954194fe73d8954004fd73d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d8954005de7398954005dd7398954006ef6298954006ed6218954194fe7318954004fd7318954014fe7118954004fd7118954014f
  | 50 => 0x100030000004000000100d401d001c01b000c027007400000140130014002003400c0008000000000400b8000000c00200100000004018000c00200000020000002002c000000c00c000000c0028006000000000000180024019000800b00000090000007000c007001000e000c02f0000002000c00e00040210020037000400f0000001001000700140000018000003006800540150000004000400100000000058002018000a0000006005c000000000b0018006000400a000000f00200000004004002000e000c00800280000020000003c006000801200080000004001000c01200000000028000000000200000000020004000800c0000003000001f000400701200040004002001800c00cc002000000b001000100080430044006001400000380050010000001c000001c00200140030000001002800402b0002001000800000010008004000405d000000000100030074003000800000300380008001002c00100000000000005001800200000030000003015400500bc0000008001004800400300090000041000000f0020036002c022001c00000140020004004001c000002800b010c002002c0030000001004c0130010000002400000e800d00180000018001000c000000c01d00080090030000004002c000000400000070014010000000500480030004000001c00000000010000000000c01c000000f00000030020007000800400080030004003000c004006c002002804900000000004000004400d0024008009c008001807600680010010001000c0060008006000000200780000020021001001800040030008003000800d01b0002000402d000000300100030020000004400100040000024030000c00b000001100200020000000000c0060004002000400b00f00190008002000c01c00040000038001004401a008c0280010001007001700040050014009000000e003c012002c00000580000004009000c006000803b00100010014011004c006000001a004c01f00480040000006000c000000000200500000004000015c01600080000008000000800d000400d001000f004400200180010010004000800f0010000006400b0004002000001500040010004023000401300ac0040000037000c002001000e0020003003802e005000100000000010000003002800000090000006001800000100060010017000c0000008000002c000000400600180050030006001c00900040010010003008c066001800a00000000000087000000000040040020001000c00505eef6298b54194fe7398b54004fd7398b5405eef5298b54026ec5298b54014fe7198b54004fd7198b54014fc7198b54006be4198b54006bc4198b54006ee2198b54026ec2198b5400cfe7098b54004fd7098b5400cfc7098b5405eec6258b54004ff735
  | 51 => 0x400c00000010120001000c0000068017003c00c0004004000400001b802d003800701800040000015005801100240010004005000000200380150068011001c007000800400800010000005004800b00100040004006004c00500cc004000401100a000700080050000000000800d000403200080000060001000401400300010000000000c01a008c005006800e0000000003000e002800e00580000008000001800500480000020000000000a00500010010006000c005000402200140000010002000400000000020010010000c0000020001000c00a001000600240000020000001000a001000d0004001000001300280030010000001400c005c000000000100040000028000001400800100020058001008407a00200010048002002c003000c00000040010000007008c002000c0180000004000800000000000004047004400200340000008017001003b0020006000000d0088002002c00a00040020000000002c000008001b00000240030039000c01400000050000002006400200000150028014000001100080140100008002000600200030008004000000600000010070007004c003000c001004400200480040014002002c0050020031007401200180000060002003003900300120000007000400c004c00300f00000000006000400100000000000003002400f0000001000000e001400000240030004008003c000007800100000000000004001801100180000000001001c0020004000000c006002801300000000018014000005a009c00100680210000021000800400100000008002002c0360008009001c0000078000000c004000c0000008003004802c00040020014019006c0000000002004c00c004c0020004002003c001001400000000010004000000000500000170000000000000000040090008013000803700640150004002005800400d0001000800000000000000004001c03d000c009013800400000200018000000c00500080090048004000000d002c0100004000001c00000000000034001004400000700100048011007004d003400b000000c00000000008002003c00000080000000001005c0240000000000400f0000002009c002004c0010044000000c000000000300000020000001001800d0040011001801d00000060000000000400b000c02c0000006002c007002800e00400000014000009c000000004b000000b000002c000400d0070000000400100800060040012001400200680040030007000800d000000700040040008001000c0000000006000c00a0038001000c002000400f00000000030000000400f000000d001401a00500060000003005800000540070018000001c00d000000e0004000009c00600340180008004002001000200000014002002c004000c00000040000014000
  | 52 => 0x8009000e000400400140000048000000800d002000a000000000100010008004000400300180000014005000000000140020030037001c00200100010044002003c00100040070000016006c0030000010001c005008c03200440020008001002000000040000000000000c0000000017009000e0000010000c0010008000003000d00040130004025004400a00140140024001002004100140000020003011800000000090000000007c04800080000000000003400400e0004000c002000c000003000b0000001006400200600020018000000000d003000100100010000012001c00300c00130024011001c00000b000100f8000002400000180030000002003000100240060000000000c05000800010014038000000000080000000001001c0090030002002c00f0000001004800d011400e00b00000000000000c0000018000000400200400010010001001002f0000001003800d000803c003c00000400010000000000800c000000400e00110004000006001a00240030014000009000b007800200180070028007000c0000038037008800400000040034004000400500040000000004002800d00040040078005000000200380020000008005402700000060018002000000000040030040005001400d0000000000401d005c00f0000000000001600b00080000004000403700100020070026000000e0018004000c00000380080114000002c00300000040000001001800d002000200000160038002000001e00080010014000000804d0000003000400100e40060000000000c00000100050014000000800900500020010000000000e0000000001c0090008002002c0010028007006c00500080270040008002800500c40000000000000000500480010064000005400e001c00c0004004006c002000c000003400f000c009000002f000400f004400a003c00f00100130008001002c002006000a00400010130012003400200000010008013000c0080048000000800b001000700080070020007000c000000400d000c006002c000000c02000080020000000010001b0000006002400100040010018011000000b00000020004000001c00500b8003000000d009000b00080020008001001800100d80280004001001801d0050001002c00300140000000000000008900040050010010001800e001004500080000004009001c00d0004003001c0060018000001400300000000000002024c0050000005000801f00b8005000801600200000018000000001b000400500000030098019000000100500480024000000000200040000004005000801000240030004006000c05600000050000005000000a0004006001002e00a000000a001300000000124012000c001001400c00000090030069000000d000000a003c0a0001402200c
  | 53 => 0x5001300480130004000000800d0078021001c0010010005001800c000c0020148003001000d001c01100080000010008004000500300000010012000002b001000900000470014003001c001000802c0000007000c014002800b000001d0000013000c00100640020000029000000000140000018006000000a001000a000000a00880000000001000000b00140000008000000401e0008000000403a008c02a0010006002c005002801000800060000000000c000000000b0060001007800000180060000002000000000c000a00200050004007000c00e002000300000040008006002400800d4004005000100000010010012000401b006400000080000004003000c01900800000014001003800000240000020001001c014003000000100010000007000c001003c002001003b000000b000400c000000d001400300200150000008000403f0004007006800b0004009000c0010000002000801300000000004000000003c000000d000c001002800e008400a0008052006c000000002500000000020000001c0000008000000000100240010004019001001f00040000000004000c01b000001d00000000044009005800200480430000008000400000000000004005000008500000030004000003400400580080014009002000d01fc003018c0020000004001400200280000000004004001c00280080000005026004f000001100000030000005001802700d40010020006013400a007400f0000014005403b000c00000640000000001000c00200b400700240040000012003000a0010000000000d007c00101b40100008006011c0040000000005c002004001800d4002000800000200020000007002c01300140020000028002400100000030004002001800a001c006000c00b0004000007400e0024001000c0060134000000c000002001900140010004008002000700000000018000008800500140000000008009800000000080000001001000900300040000000004401d001c0080008010000800c0000006001c007000801f0000006002400000000010004000000000600180000010001004400000740000064006001800a00040030004051000000a000000200000160000007000c0000074000000c0000044001011800001cc000000400101d00000054001000000a0028003000000b00040000004001000c0060008001002c02f001000b0018001000c007000000300040000004003002000b0040003003000000080120044003001c001001c011006800a001000000180170044008000000400040070044006000c0060028035000800d0024001000000000cc00a0018000002c00d004401800400000020001003000000b800300dc0010004055002c0010020057000401000040010044000002400500040030000016004002
  | 54 => 0x40004000000c000002c000000000d0000009000400d00080000034009002c014000c0110038016004400e000c00300000140004027000007e000800c008401f003402300000000040012001800500240000058007003c042000800c00040080004007000400000080030004000000c017000400900080010014000000800200000000000000003801b0018001004c026000800500ac00f000000b0008000000000900180080000017000000800080000058038000c01f01e401800100020000010001800b000c008004400300100000014000000800200f80040074001001000c000000300000010024015003c000000001f00180030000011000400200380000034007002800100140000078005000c000007400000000020000005000c00a00000000054001004800b00080020004000005800300080010000002006c00300c0000003c02c0004000005000900140050008000000003500000000010000001800000100010034002001000b000c00f001c008002c009000400b001c031005c0090000002000c008000400a00180000000000000000400540040044003000000000000050000004000c001001c0110018003000000100040050010004000000a000000000140080028002001800000000040018000000000200000040004000000c0000014002001c01100040000018009007400000f8014002800400100000000002000000000000000010008001000200500040000033004000100180000054002008c000001c00500440190000001000000300940070068001001c000001400200240020004000000c00f002400100000000000001001801800ac01b001003c001002f00040000000000001000200040190030001000800b003c00f0004001000c00000000000008015001c00c0014016000000e0158001003c015000000500040070000002001000e001800a00d000100380110000007000000900240000004009000c000000001b0000052000c00400100000030002000000100280090000006003400500c801100300090008001000000f00640090000000000000200000020048000009c003000c023001800000080000004002000000001b000400000100000002001c023003000e00680000000000002000500040290004007000000900c40020004028003c00000040000060000001400700840140004000001c002003c003001c00f000c0060054018000801d000400c002000a0038006003c01b000403e000000400000000020001003c0000080000000c0010028014003002300c400a00380090000001003002c00180070004001000000000000010004001002c000000000e00580010010003000800400100000078001001400b000800f0098001002001500000010008057003c00101e0000000400b0004001003404200
  | 55 => 0x7cbc00016c7358525b80669de204f18160000000013d40dece818c9c00000e7c96e91c019d4654006159ad0f3a0000000036a18a5820cd888f2740ec1c7cff0189e21fa5a60b7208e7a2be3cd87680c510e072f9227f0025c2bc22448a41bcc3f5a277447d88110d4878109738d1a1d3c6b74e3c802b2d6830646285ad50b80465085218f832b6011efcd8d10393041d0b951b1b10963eb6ec3a06a35c67cc109606ab1e948060de097242bac4985039917ca16e21f06209bd800941956df40ffa010c2340d2a903c3f2c33be0049ddc1c3a660402f87ed2a785cb8b52043737e4555ccef1c78250a08409eb4005405612dce2ca08187983b84f309b68134c4260ca794620f4076a095619750e4e37b83d24852288a5f39094162d1c2e0e8072787e305217308e49911b37787848f2014a6315335f0e3d0017005c00000080100008016000800d0000002001c0000070017000c004001c002000800b007400000100090030002000401d001401500380250038005002c031000000200040080030000004400000000060110005000000700040040070002001400700040000068001000c000000c01500480070000000003401f001c00d0008000000c000001c000003c00a005c010007c0060018000000c000002000c00300000000005000400b000400200ac011000000a009c003000004b0024005000000000780340004013004800c00100150040007001000400000000004001000c00800c40000008006003400c0094016000c001000400100000010030000001000100000130018001000803c000400f0000002001c0050000003000c00000b4005000c0080000000006400a000c00000000010014000006c00600300010000004004c00100480090000002000c00200140070004004000400b001800e02600000004000001801b00040030000005006c00a000000d00000030000004002000e00200000018007002400a00a400800040170040004002800c00100020034003002c020000c00a0000000000c009003400200380060030007001000300b400f00100000000005000001b0004006001c001000401b002c0030010004005c0590004008001000b0000005009000d00040000040003002001e0000000002000a00000000000004000800000440020024000001405a0000009006800a000000100ac0200008002000800100040040018005005c00100f4011000400f008001d002000100240220014003004c02000040090000003002801100080000008001001000000000000010013000000200000080010010000c000002c027000002e003400400000020004016000800300580050070006000000a0034001002c00b0010049000000200040000008006000400500100020014000000401b000000000540230030014001c00600d00
  | 56 => 0x70b1b2b0d4c4b60ef48b9c237c248876c106b04f814245dc88ce034c765428605fc325000001475bb113ce6f00c6a1fb73134272c8ff829bac505d845fb16a90a460b18a0a92fe175a460103b60bd041241fc2499a6b0ab954cc48b05b11c5a59d89700fe2028844f86590fc9024630d816cc403169010e696493aa308408f0448dcde3fb2857c5b458cd29150834c4848eb3ef60ad470fa053387c558810d9e1f0f78448c1b20ae4362e065004d0ec9014900c809b08891f124048fc180212b122358419e11422827f548e9d473081c4f7070ada681ca505dc9cc853b190f16f4fc2937026302c5006b4260200e0dbcac281b6203843d46f804d9397e3ef45ec00001c185bccb680000184e0000000156780002968000000011e64b086568cf28000187c0001b2c401e6934c6284dc18e0000057c8429054e35dccc19f7700002ddc0000000000000001008c7d00006460b39d679356c000000000002a8c000078d9fed800049280001efc19090000000000000007a7c00008c100006512000000015ca000000000000ee8329000000002199000084dcea33bf05ca400000003e5822e41f20000291000000001a87340a728037b000015f000004ed095f15ea574d0791f5b371e0f1c00011da133a0bf4e149c970c2e26f473480000a7d424ccd58b6337ba21accfa144e9cd482b41df0c5c2fae000066f128b08c042e4000210d389c0000eaf000030221544547031f8bce32d291c9af62c3e20a4000122c1ae000003d494f98e38375000000003c2e3cac21912310de24f747a880000da2553e27e1f2913d800000001a9e1eea00010b28f9e80004b000000000322e00006cc97d52cd26ee0000106fb69412b8b96203b388025700b50f100e406be0a6681e7138a6e18a91959c1f1653c005a0714142b52582b6100424e05eb09f0000040be0fee6d88000000003b82c31d2b08361b10cde8ac3191e2150000214e20742e34c63c781278c6f943c5473a01ee4c400000ec6000067c50a082c0912000002ac8a951d9c60f8a20984b0d7c596800011552de8272402d02070f031e5cbbc028c1c0407389ff061209aa000000000000ba856ac1e28000096c4248c5c8f8826901e382f6000001226d8cb6c0000000048100000c7b16722bf48c600003f2800008a2000020100000b9a9a7b00001a180001a64000042346b1000034b8102c663000000000000a2fd4f83ce61000000208c136a3c18f7c992f1c32000108a4d5002847146089c0001adc5eac00019db17f634c87fa9753252a0000891571c3cfa502600012f589726c1502818100640410a0000000089631b909f0000047c0000192000009d809f80000000182a00000001cf83cc839f0caa0000000000002f19d8002f000009eb968e0000355c1ec832f000032305cf55ef127456e8c8000000
  | 57 => 0xdb8000000000000000000079b8000000045e600000000afb55241d6008417ce68d89f9cb6808be6e5c546890216b60ea41a5149b05a4776cc6196133cea25008158d242db907a4983160619281f760da97df171448d0e62906a2ac277e841a5878338f6aa09980e9da0886c30acf8a423ec077149ce80002c2a553800000000000806c5f0975b289800000000000000000000000bf02e7003eed535ddd18c677308cf000041742b3e82815fc33431fac0000be6978c100400012b4259436946769c8d80000000c5059102d43000000020dc0000000017e1efa35f85ec0afc01323e8a00006e09ab8000000009ea09e439126bec30307340b3a0ed4b9f00000e98000000007170000563d0b0800000000fcc0001e0b8000358508be119be0254a8e8f578d3d504288826125e370e000086c0000000011106e41419357200010258ae82f1e365c6b4824ab77a475adfa8ca4ab7c3b5c8e5806c1cca2ff501684b4000076a47a40000121a6844087979d00005e848daa0a700002f089fb9a152b2c44908e69a720000160070218031bf45e0c0000000000018265739217331c2f4c62b8af1a6c65a80000081a0cd11a3c00004130fa46ce000019aa885753ec82d800041340000c0c5d8b3f348098de50a9112ea0000000000039466a2ca439a7937c05b7c2b4928f095000000d10d8600002f74e6e000021100d841b1953032580a901ddc4df06200000ab700000b8631c27c9401800002288e8000003fce0000000000000004bfcc5894ab03b4511846208200c3121a20000a800000856106905d73a88760903c9924000039ac00008253ca8172046780ce1a420000b6095ee404a00008d3956700006b3cc4e9d8403006b1cc8c858530b0555a0de065c42b809a050798fc102c679ce47124d23c45a2a4a4126228b88308b2516bb0adc7a3871219e012283f501dbddcaaa311c6c2d611922100548010513b0279e50188cb0bb023c0459ad8d044d2df815ac8af17272528335497c166b02583ef82f5091c1b54518c31e02ac27741fc450f091492aa4cfcdb10a052c4264d8db5872c2dd0316638810fa2c3f0820d17204c397c0bfc8c3981d342629285ea18511f6a74fc17013ec0fd83dc8af21c052b4a7a9848b86e62338430c16c4fe429f271202ab87b7198a5ed8e3d915d30fe1c320f584791dd8510226196e60b7c76608c21ba02dd8041d04c212401830078d50de07081a45e0f0a877e1cb44a6820c02872d4e463d076466e10023260bf400fb0e9a54a677d1ef642c467fe6fc9f4725c828502131bba157003c47149f0840ea4af6cb31afd000038c0e3b1c09256a23926d58000153a53f64f199bfa19c572419b989820a43600ce200001afe2264d480a4c3d3c6e089c2997c1ff83fa2cb2852918386b98f4582de16be7a04c65115a30602704
  | 58 => 0x6de18662c4413c8375847302fa03701b98e88087020fc56a0cd620bc228c508884137ae7c9cc859e482850803433200000bdc2a68cd60a17343c4d04000000000004654ce1800010b832688e2925d195c66a6000000025500e385d75d5a0000459c1790f4600006a8e000150da8bc1b2c58044aa00000000179831440c80000c7d8000357e00000001ff039aa2b0851381863cd84960be38d41000000000000ba604567340fee1826161c495200010dc1c740b040d285d022b2478c4a3c6aa03fe00002c7c00000004284a95c0002d86000000000753ee66a500000f0b1bb84ffcff1000000001a940001f3a0f8900000000dd72b1a0c7c00008f539c25ea509d0afe24cc1458000000011ba00000000000000007a67c280001fe607e000010c4159851fc1ea149942072ab086a9bad33160c3c045084c0d365e946b3100d091a70000a80753a74e0000000057b1440041afe88ccf00fe7d744f240002bb00000f8380ab34a629ac4c7171b3f0e00000001f421f7f000012890bf329c358c7bc00003126110efd88cf501a76f547c51d42160472b45f98f4e08246f909c4940f0bfc1e54ee00979094e326c81f85a424a783ec6a694f41fb00360a8b51ca30986702d399542beec2442ce3453121f0658c0b980002a1d1724a7f173008720000000065f000048fd010800040de3a3e0000ac137442e603dfcf422c976adc36618ee1c16014ac6217ea22b682a0522114f00000894f311a3429a4335c3fd06c0000000002b40fee00006fccc1981892c755d5896f80003038191005f1624c0460e6453d895a0eab1a122878c1e26ec4b78c4213db3cd00e68a90530c106503b03fe9425013c83245b009882f7401386af1ee22578761408300001a6e37ac9e70e2c0afe0d4c0000b8e00002014000148600000000f58041d00003c74ed0800027dc4322ecb1d3fb65c000004992521858720800019ed39c40000b9296b80000000024f80011d7042e0526899e0008843c908045c000017ec76a00003b9d72d4a258c762b260000000081e079a21d2d93142e2ce031400f09e8f2af47838a5905f9afc065889e916ad3aba1c3cad1838a0c0637284558a50000064790570801a33640f429a576a2d2e00003e5800000006e7c0001ff832983d90859de350024321651d55278084713cbdc90b6423e13ac47b06762fce25f87520d8730c2090c000000013260000000196f3f786228f010c912c0f5e70f5d0000000011d8ab404590000714400009fa80000000000203d000012489ce0fad0000590e9af9460077856a000000002eea2ff000006e300000001008070601d4015845d1526c0281da899d000018e400005f181823aac0000e1b000035440000000111a2d28000000003968ed002602e30000310c8178250893021503180000000000000000000000f
  | 59 => 0xb8224aa45884ce0000710cf31800027aa788454c960026a031dc0001c1d2d9200004321e1a0000526618e47d10856734c10e98da153644c85e80c481d4a00000001e2905221b24ec89fe108828300f718d8d3aa83298cee0e533b381ca434121511e0201ecb979fdd08806c4ced5120f1c3c1ca017f037900d640081669a440a7e5d8093b0ba531da175404446009ede0478b8b85efc2082a50eeb08b99b46741c0000c2108ba1020e2c0f5240400fe47000c331478154ef9996a6366013a868a831a35801ee0ea313051295846c1411e25031e253cb08c2c915e645f818e9ac82756013c30e800020428431095000000000000000104705a847cd039045a000000002fb40003edc18522b39e861438832c0ba88e10a8c652847d476f1d0763dc9908d0e1812255cfa50b0619a21ab4d230ac021582a5c01b9c9205ca0f540a199c9272a77d08fc987026723608b6b8309414a297430884fb2df06b4ac1f909c167860f0ebc06f31458423050a96660b0770b4b758a5804ac25e0739800021982f58cdf132300002e0400006fb0a6820983a7800000001dec000132527b052b8a6c58b4a823193824a087f03b70000000062700005c34000021f428c33c0ee9d82f000066688110b0123136fc4ca49ac415d210bc012131700004dfcf1a053780000000b600000000068207e4184f2e3a44ccbbc9a490ed741c2b3f44a408d4748cb4682b225a250d40dc937b252469945750eb3929d7ff80231c2e26b84ef452380003aa40000d8016c5927a6b9400007523bfe4fbc16009bf049226f8000000027d00a78db7800000007e7c0000b6112f67cac91b80001084589889c8f2e240b000000000003ca0000042f1695bfe636a0000036615084e6879099710ce822d0c4a00da3872558696840002161592400002f60a40101c00006c60000159000000003454000000012cf80006bcc00000000000000000007ac997b000037800003e6f00000001eb41090000088208af25640000cf90a2f01e034d84ef868823a919e44bf5c07179657f86d20eca32686c90caea0cd2c3441a4736a11217e8543cf44033d1b3861b0a64800000000000ff3131d000000000001e1800005408b0b9932164e825508159ca36286e400001f1700003c80f7513623af85f60000011735e471fc1c106fd2b66476e3b606ff106635184ed98a200003e441e50cab882e3a7c23d86e900fa7d04d5014042c3a61c60000f29218f00001ee000000006cf01910c9e000006c8cd2cbe380000000000000000007680c0f025599022208000164327d6198aa7143503b287bb0d3708e6129a4850786080c1c5e21e87750069950a47d0e8f989cacfa4de0f2996fa355c0000a8e9584164351b892b0000261145a268297fb3d086190b9743bca5f2674c0515505256e5980f03502f00001e9
  | 60 => 0x102a000024f4000107f11d70000633a5b20e78118a07bd09e82933d001374373809b024e0814bb185a1bad42d9413a0213172242447d71b5c144823608251548000000000001fc9233b00001ae054c0000235c3b8107900000000000000000000c8673d9191205400004a49969256c000008d128c03186c9c000005e0f627fb03451623a4fc2e78c82213f166c193c0001cb1000062de000109629957470115db2d00001a78aa097042af00000000010e0e0e04881b880002382300c00018850f761e2c0000ce5000040441e98dd0263605e46120000000008f2000131e134570c88ed56ca01f17a240000000141c181aa82204900ba7904f8d0508261c031415a19ee11452f6874000002a1400006760e6805c85b6864207d7220c0000000000000002c4cdc680000000000013d13fb1f383c900000a673efc2f4413a82c3261646be23e800000000000c88800a00003548e215930173e81703850972336a7694d6b04bd31b871789cf86f708d8000000004ff34063fe4e7e091137cc5c40ee0979214f855450400e59000019d40000a73000083800001d10139f1fe50040000000000007571e018c1a0000248000000005cc4000000010261890a0d19ce238822dce999f92202854ee48089d0a0301190c3b16f72bd238e021456bf197012109ac400001740000cbb95aa219e452cc681e4b0f985a544541cb32b245540133995f19906d90000000002f41fa480f8000289a0000b7882d39bfe4a0a000011d197d00002401383000013b82d780000000000001780132a364990c1c9155a9b65378a4e017441cc48a81980000347600000001158000070280000000391f2e54e7883fc19e2000004582d117c43dc00000000273034f4e72800000003850ce8a146800084c46ec1edd067073b4d7c9668204c4dacad68d5605ae77acd28a02b800051f306d0ff580006e0d067c70c3b4c092d02d8c7c80001470fd9904b0f9e329c6d78d6a000002dc2c71e94354a1a549f8614f16760000ae719df2cba0000f465c6500006d4c9911a7c04420000865905631ce1520000213b349423d06b7800035d2851ec6340000f90150c8bc9aeb09ac576c2eb214341604a189a380003ea0000051986fe3efe48ecdb51b8e20ce630a1d0c3c4317800003d458fa182052085501bed33fc0ec861d800000005866beb07a58000151a0000ef5b71256c49e2137519c051c490c8c5d1f2c000000007711ff043fcb50955539105e148ec800030e63b44e48422830b229983228e6f320e3b08445817b42642e240000f4700007334000014a135c11c10a6800010b47ab467980002648416809440003e18486889419b6a29480e09c0132909f404dc2f48d8e2b160ec4e284f6d0828638465014f2343679783981a830e860000516e0a20000678507700002aaf5bc8389800
  | 61 => 0x5920d0055062a09d210cc4aa400d0132999a4b990a21a2518ca195907686d2135403d2c4694c3091e4b640001521273c254cdef910911cd3698f728000000073d8214119041f017142c40e8c121431a25e71225379609c4dfd984804b24d446961f2d069951c87bb2147205050d6e4e189b28250ba48cc0b4f05ac4e90b451bbe37fe43a0c4c92eb2ff83af0b20959726ba1cb46305e463bcc011a35a9836127e18e8eae09d526c046909439c84249c3ea48b510492a2c6e4478712443a165af85f308d5370080b84d0c10d1e8a64a8aee93ca159a03d400c8c1d2fb26676ca380000cd000008cc8e9200006914626579a2222096c80c9f8f3aa2000000018040e8479a411a80000a4a2cb86ec84152e76114800007c300007ab8463823b12de1a1032980003ea6007cb55036d2a9e712654312e140c476240745e55000045401c9800030a04878a3eda3000005fdc1a3194614965eb49748184345679e041a800033447ad4a77c50e236531083bf97583cae6de48ee014d38d216d8937d86b06ec16d104587fe262440d0ceb00001af02618d0210ad0a7b06480000751000019485fb9df1074610f83f51c02053f080c87597403b4429d84894a382d7b00d21ac1702000000000001171000000009405e1617e224c43fa93ad28426860cc681cf06a271d4889026a262831b0101031200000000000000025c45b300000000053026ece031bd940f861e8bd1833600000000f70188741de0000d0c9b8a122648e8ccbc00020184d94a7e541726cb42cc44f00000000303851d000042921ac0ec9936c2e843162000118eb6866e14e5407e512e6357c5999df606f40000a2f803b0a220000e291d4a3ac005b105314db9c8a66625441180af3640d41f9018715c0731c28d9255a9c482341fa5535c02c75c0cd50dc333d71c78644c38922dc7cd0000000000005568de7103230a41380f6e00003ff459343bedcf927b100d67330683137b6c2400017c000000000000073ba7143d3caf8000000000000fde8000285661f461105a33828516ccf209c6253654a4779177241ce7e240cc0e33af8659b0e30820499787728a4f9fdf3d2e4fccbbfc0001ce424b2fd7171632740584fed9fee38e62fe0dfc9f64000031ac0001bb9000075244b006b114bc0000000000000000000d2e98c6034810b4d431d272f44242c000000023c800008fb82803f9e04c0ee100002f166ea0eeac0003a833c700000000288504069488000000025d80000a22b36060c881b973c281c034c000199eb82a6d40bb61c3f00000000d978894351e7234367125b2df60000f1516ab000000007a8000018000000c0083d127ce0000111953a3d543d2449c000000001b8000000003a6a0000aa180e0295000000000eda000000000000aca16b8526000016b0a4092d3445a990c348200
  | 62 => 0x806c56c8ec05dc0000d6f80002cd3000000000001b2a00009d00d11000051648c6c10f96240000979c00000004dcc5c000003de60000a8c07b60dd46d5c000066700002dd4b62870b8000058cf5915e01e4a82b0ee9411900000001081854a000055d04ac16ce1dac71f00000fe02362000000020b3014c73240000c453fd60000c748708000000009338d2e12892b6060592283ba00c9c00000000aec8344d51898a2a611d6cf0f12a7000034ec0000000000000007c64f69000066447de0aaa2bed5e00b8a95bf0b7627f4e1092f6328609bcda3105a9520784cf9f80000e7a79a880d0a9220a80000000083e13046c3cc231dd2389a1e606801078037c7e8c1310e77b7ac01a0ed81174876821a8b0a10a32cce15de3dad25a0000515000001c401bf55cc0d613030e02708020f80000c2a000036b1cef0c80835c69395fd3f083dec00000003c6e0000c8a172d210c000092080001e2274f000010af396e20d600003ce29703dcc71ac385956259b80000c063472769c9a297bf2da41eb000021159b4e42ec0001f2531ac000029100e7334a70a88a318979fa02bdc5fc99abb5fe0a7c8b314c20c94328c154527d26785a1e92008153bf8000000010ea1b9a819c5f7a01f404804e437ac61303860f8006a886c24ee0cfcdaa119c80004adab52ceb1168a0f98c5082392a973990b04808f37fa0000c1a91c327622f0c00000000c8c0000795000004c80000d858000026a0594bd20909ba0c219c32e800012e04cc4000002a1e3068fc0001c4905130000d6b900a3da220a05d5119f09127a5462f800029de000040f853e112467e09998a14b5747d00d1f1cb9368e72280b8000004b842f4000100f01d57480c6780000000014400002fa32ce549c02480000b47059004b9e0a16ba0c448b58706bbc50bbc0170333162e4af466700003a241178a305b062d746dc10671a8d176f000085e4000090234c1020030400000000e520e3c0c5608580000a3f000004cc86b8000285a000013b800025f670a013283b830445b08c060e8203b80d0c21383a7009a019850e9ace22a22e4c09890f3116623786a60000346609a40000c5a8ae054986131d9b32fd0000595800030264f8c2ed000023ba0000c5c000010ca000000004950000116c67d131311de3f0ca6ccf0a2fc61664eeb5e9634ec67e42cf974423c270acbb69e8d189a770ce1604c4094600007288000000071b04d112be1b3c287c38c05e2205a00006940000000000007749a5e2cfc0654000000000007ea4a85932c0000437400017ae03db26f00001249800073800001d4d80000264e44508402d6698c1784d453c8a0214821cc161f0184b28779bb602964930bf7092f1c247d2041a1a02c273000056900000000157841085f1339067d80124a032280000000021231a2c53ac04600
  | 63 => 0xf722b1502295d5095e25401188694275e188a00013b41758214c5d0c05c41761ce01c69f383d8276e02a38b4b2ae27efc2f3d7d22d2f23e46c20968118600fc91721521f2083f01c813bc0dd81c90a9bdf7d3a76414a5ee4b861ab85672e2289a703fc211ca9f1552c1407be06a986bf14fa6220ea00ccb25ca0000524970909ec75c4b640ab72a705e54e2e037e139b00002f8212530586850d2c907c0a020cb4cd0800000003f6e29b1ba521022c2c1699344047a12e09550ce90000220a000024d14c0000000000000000202011609cc800072589e19c270000773c635d512360800f4ec1800035e20000a8c85242c60000045f0939b49c03f00a40beb0000000009a00003c48150815716d905ce5a04517cef086166dec7d211682698771c000174a23682798f3d13d13ffd3a825a081c200000000a27d70607be4344d1314e5391e373ce404eaf3de4757c35b10a5404439e8e77096c0638383c68c04c2000038c4a84196e013842380001aad000063060001751000066dce601095000062406169762265a06e81b580001ada7f589498662000064200940000097e5a180a70e6e06c07c90d3a042100001b1acf612741f6c115872a9f492e3e5a829bd013b02fe7bf44a1e10b0c965a3c8970a1a1dba702086a143d3a7404009c78ef62bc60114cd7c92e06901748b871cf205142ebd07207160e66691c175ccc0b45871b4a5b400000885ada02d9c959f62336c0ed46e1203c6b1a18bd0e937581e94b0e13e6216221846e480000000042860204712e0061945ff916920ec570ca8a9251000010d849dc0000cbb0f740b398963a425a6400005e298c40b3c000008e129b08fd00918afa21106c058d99033fc874ca7f9156b2a580f6ce48000006025914241034e00005552a21800003ae64f8306480b1452649caba80ad1358842826801383c9e53fc8fb1b982b680000000000038707bac00013a2148a545e5c8dade37c644e60b110d6154228f40000387000024a873a8fab0dae854c10700f831a73560a8300701fcc0458d6596f942100db84db0bc11ff63ebcab691b0a7ec72a44b3087222526e989c584d800007f0c0000e7680007454a120f55114e3b04cdc08582cfe00004d659851a8812c0c05999c0caf73184b3847a3ac833da00000003cac2780000082433726eac0000898000000003c81ecc18bb491ecd31a5a2a266c548de54b42aee2900f5020cf357a00002740f87294b7bb8601000034400d949bb8527265c07b47c004d317cb4160ca69ff08b6e429c585c7fb1b185dc0f5f80002e1400001d2904e00007bb4d00871920dd3bacc189d9a2cb254be01992502a280000b160673065238d878183979308000000007d605f257d0e0c1c4423664fd40001c448f9a00007131e8700003826102cff7997671808481bde3a3c6
  | 64 => 0x3ab0a4481d934164b0c3a81c342f884f9200020bb804e00005368dc41ce21deab83800022762cdc0128eab2c2b48800a2c28fbaf681fc50816e23fb436588fa80003244786c37e131c3a6801209fdc00000001836f1f079318fc39d8ea7a0f91aa87c40064004711484d0c58689d62917790c51c9477072458f1019953200000b8200e8000000006bcb9d0caa30887e1819d030212da140c8ddc27f202a47ac56b92b7bf8c5f2801a00001f7b0000e0f8bc0313500006f8800029e62028000213718865110671969b0be801540001ac90c1219b4000166ab21e000032c82dc90001be4294000014e42a8e67580001f9a2a88000000000006d74eed022f388e0000d739646211460a00001776243600003ef00001f365d7840798d587553d8043accd920aa0000a9d8974000020505f4895d10242990c38826b3f6a2e7665a1cb22b6a3f30000000000007b3c6ba8634000062a06c08f530000091021809de0684676874cc3df940c00001e80000000036ccc5d599f00000000000126b034657c8c2500000000569050498539f022088d60a0a903e27ff4c208ec405d57b98e304aa725760fb4b2e0ba086562848917a0af1ae27130000189e954c06ac74549c321e4504406a0b253c7a174c000195c2c7641b4348109e3b1c5e381a586583e1660d01840877168e0790d188000000045520000f97000074c8f250e010fe00300000098524660000000000000000000a29017621b400000001e2822e8000000007c880000000d9d989b80002a9430c800000000000000000000005106d7d0f6534cc3b300000000000078f03be400041722eacb7e84752ae339dccb59aab9b1e15d408081b325a60866178000003f53ec8c7e800007df5796bb20d4900003faa7fe9c461336629e460ca3c89345e206a187942b5e080104798a592fe1e9ad9f9ba30e6562bc097111436bc000060a19332d312ad2b41018322e7845ad0f928d164c0000a6081583ef83af4000020f074f55d88120fe78ca20000b068cb619882ec2bd980000000440001d0000380253b856d80003bbf000015d9353389100003cd80000000293c0001c7d1fe0504100b899c2a0e550f01f0b9921ca45903e0000019f1173103b861b019e320c736076000005ef8f3d8e7b80006a58b4b4f5905124a04ef19d19217f3f945671e0f154800007380b40024c2fa06469270be1a1f2816645ad000003640000f3b311600003849e27399e24b4c8fd23c1d520a70e689920179a0a3c2e2149a000078180000d6c00004f6622b8ade06cf2bac3ec14ad100410d014287ce000000003fa461841d05860bd8869f41fd54acbbf14c50000489c42540000b74000037a128d8000571c7bc83f100000e041904b98c1b74e403e99ae80a7263fc00015369d0e4434a039f1140746f3cc50039cb262409c8638
  | 65 => 0x18c985e20c6c3e393ae39ae7c8c9b51d160fc237900000e03153e0a18ba192e4970660a42f043ff04247b6c000076e300a04627ba10d3266c2b543678a022bbc05c81db00a91e980f089b797032972050a6f78e16bb9a84806df83c800004f58a8f05e4a08a00000001f28000073a83b99cbc3d20630eb8906ae0f503a44e4d400000005036000089abd360d55005082e3bfc16c881b12ab30320000fa7149d1d6e2396ec505a2a7801e0031b97a62ab275b86b006f517428138d3c0837279825f4eb486d42926715653f0cda3ae62490f1b062f3bce2b980efa047000002b017f40003cca68240f418de286025c47f889872c1e1112c92800032a268a0ef8117b0738217400005cd35981ce4cc200624094244000007232d0835746cd11aa2dca786431c18d2316c29a892416ae00006cdc98c9125217759c81e78e3504440000581916d0f1e5b18bb88000000000009e587e200000c8c74080000ccc074890385491d60067837d02610b8401e20e50465372834989ba0000078921e000010ed31ea0000ee980001cb00000c47147841125f700c7209e0a3a6868ea5422e1cce45fccab1ffabdc832c00688000000030949608c4b2fe40000df5819142ae82e0d0059683a900000ac0839819fd37a43b2082b101c3f2c00000000000834c0000000014a2dd835e12322e22414c576809d3ab203f824d872b2e667b000000000000000000000ce783f44e1e000000002200000898c00033805078112195a2c742fb0f9c8f5b0000000000013c720a900009e850c93820468819889f020168270d1d1a0780001cc80a88a4e05b77fe451800003e2602481b9118383a244984e38000422085206f393a540541e2410f1ad206ae0a586f3129e293542cb0029407a8463f84605074e07426d109fc14d72e562df49440edc000037dce439089000047a00000cdd0000549046697f033355b6ae2e800025a4000026756e0270c79f065980001e0a14789e691630da6268c00006129f801808d9b137d123c111cdd4966a1d4365d84381b330c3411c8afb8ee00ed53e82ae908c6254047e04f08a342fea44405c7987e325630a4b9c920b1578321832d0a27a3e45e80481917032524bb87e118c91c4e617c6f5125c3bc300002f9d5ca8000076d03d87ae3a894b5b00e1c252aa777202b31a42409e58d4dd81aef29b41a0491c1d9f00f43ddc5439563165e2230dcaa0be000049e0ce2d9e800006dd829787f20ef20000a4a9d3816e03e344cc8901afba00008a1086218b40000dc4127b0c1c2c30f221bcd0f575c04dbf800e82673d88bd78a0404935ec8c4080353ee844e09230104178e000069c121f0ea90a347508951000016f0e5e8000208613480001b6c049000010220b4c00003a26b44133741ec480cfc40000155c2d18000000030bc747403b00002840
  | 66 => 0x611380080141222a4a7c3c11b5f08b066c4d301a8c1a3c190c2609ea216f02b6481c929d14820d7c0000cc3036856aa22aa05a00f52994ea2c1fb347a720083a95ec0cde0bfed2f8f8c121811ac84e8ab92724091454b19f380e4306c4960fc730a63ce0ceb89953fd4408c41c80901de02c00f130319025e286059094ca282100000000000000076c4e408000187c000084d8054a30b132000002950c8e5828dfb800003a60000000041000002efc000000004d382742a9000000000000fa592d40754000044cd5bd1418000000018e500000b75002209b000000008180dcb0e8e000091e93fd26da3ea82061c9410c610245319497092c13947b513b73d04828c00000000d6e63c40001e0800622a92153161b2abc80386d09fc40ed27e5ca488fd627f2238ce0680002484538e000046f37a0038d00ea06928547d5c5ad4538110a4184aff965338b77ee08fe18d2884a60f45ba0dfb03763a6b08c14df267c80c83cacd2d0e925280a9888230f60642821e9b4202e27ed0d8e8067315a2f240001d7f0a784384d55025427bd36c8791181a232e1568422004339740490b6e151731386ff8b6a9a481356100877c950c25bf47082778905094c84b4a8844a935b02a280000b520f147ca8c5342cc0f7a224c0001b0d00001314039862602c0000000000000000671c0000000406260946a40ee411785c88b3d00001a040000212400002630000f6c811f18985f2c58a92de81ae297cfb893b220c800004f79281903544e88d400003a67000016c810939fe0000000000000004bd4000073719fc66d8a731013000000000000b87358652ccb6687ff1a1624f854499c8a19a585881716331a7e205c1230eb31bea4ba0b2b833435da3b48ae3050522e433a6509d152274c544e50401c5060c0cf07c9d10231e45f3c18a906e2b762d5cabe14349ea8000087f127c28de28347668b9fac687294000057433410305047212227f40eec00000001c426dd08334ebb3b24367c47510fc035c0c28c3d9ba10236169cdf712ae185058f8d3388502d880b6844b861e41b61b7405c99610a6612acf371faa0000362431992fa056e7bc01de90ca03b074b4eb0859b0c5c24c8af991b616521ec69464ed903ba6e74cd217b2b20205f04878e3700004aa6034941f0a0041c10308dd319be4d0068f97e9187a627e0875df53a225f94c598000146a16880000bcf0b9441040000000390a3d705e608df42327fdc9ed07d91c692885050971e3f9a0058eea566d28527d4501613b9223a6c08c2a8bc4938406b40d380003ea85d740038e9880001588385800010be00008b9800001860000c7ddc1e3f820000b578000316e475400000eb800000006481be9175c7c3cef0083b00003bcefae113c3b1e01846a518f4223e7ef8566c000093216407f158bd00de6fe86e3
  | 67 => 0xa0000000069404fc0000343800009520b2300005e785ef1cb801da1f961be0cc21bc221f80000000282800000001ec600006ca40000c5e8000000000019f50000833063d13942eae3d0400000003d220af03c680000000000012713564280348ce8d1aab0f106bd05f90babafc284d4e609e0c09d23cc877694f4aa34496436f9b67000000003fa000035627f501a60ba2268c7ab000000000000567701480000c9800008a2d7e21f3f3ba2aa3953d1c840000db6888d2aba65e415d2043159016c24d800000000312e46991ef000000004dc9f1f2722785e68080002a962a600000cb113ee0000eb30dec00000000f2499991d571d98ab780001ab23f1800003c883dc1e68bc113b60000587200001a01ad63e48d579c99000060dce7a19c2be066d68000023d80003934d4a8000237a000024581aa18c752049fe0316074450123d78c5600006224a7d400026f84838bae0000132e3a9c00000001bf00000c710cc705a00000000192e0fa0000000000000d12619c0000de300000000ae208fd3f262d7859f0a6e07133398000000026cc1e9857a0fc10000848400019c5128266e8fa79067c0cc0a40aad8bed06bc3c005d00add1dce75b4a9a215603d96a082ad98d90b56000036251533d6256b88739f90342c5dccbc20b2209648134f6c092738660430386d8ca806067a81f61e1416706d584ec164724e42700c828b2420026b144c740b3309a0000272000000000000c1201c627d9000066800002b7276d00bf0b4e23701a9c80181d50000000000001eb817e75e4377000011523688ff2897c0f8a025005cc0001fbe00004c580000000388c0000000000000004601b51000061bc0001525287600000000000258b15f47ed559b0b2a6b161ca82a13f1a80bcfab14c7278414c8a0019ff331e0000d750000272e19dcf8d800000007c54acd0a8338ad716a1151fd81d5b2bbc1cacfe80000662490308e400c60a8e00013c100006438493c5fd384654a200017bb20000948f331545361c7f306f41d9a8000715821bdbaa00007a84000000028046a6c49d40573cfc7b9c53b977a294a39f800000000cfe77dc43700003e3800000fa0453000027282930f82000042a80001ce300000000ab91cdb000000009bc875c33980684000025833de00000b318bb991456008995d8c41ea1f9035a062039547bbcffa861605524380ee48acb05b553a83ac9fb2155e73f8db880001fd45a1600019ef827c03c8918170980000eac1eb5e4d1138000012d08c217182ed4e17840f00003cb47ed9570b9862de44200000080c1e448428000176c03f4c1d19a69d284a988fd1a17010e2d44d42103b19581a8d06a803e214052149799e049b6864585e417f4393a057ca9112363396381c32a82633b562be8318878c29ec377800002d516920000bc80735422
  | 68 => 0x36800001dcf800030449b340f92e42213c88185771d68033b09308861e5e003064480cb24f10940f2f82af1e2a338457600003ff812f8c7f000038e017a236181e631b07da4f11211c0bf43a64151400000007e540401113337b000000020ee89ee4f726840fbf29cf7a2619313f7c1e06e4c4378ae23fe20a381ba0000340c36e86369f183bd073c067a03d60000000005d444200005f6c00021053cda66409218000108a01a8f6290940d746e2c00003fa1bf861d48d3165028027ff6306088a21ee4524cec19923046712a01e0a3b873b0000e0e1b4f04a61a880000000264c24389901ac20a5615e000000001cd700008e8180200000000e7d0a250b340148ddda15906b2158c77e000000002950a1c00002ffe0000c6000002ef65a9ea768000000024cc39f4000000000000000000000000002bf12a100000000af38283000002260001b3d000000002e7149b80000000000000014d2569c279940a415642c848153870000397c91a917d14c202d43fc13f10f840204dbf00222c647f4ce5d8c3424dc21186bd1a320000504ca5a9ab025665d38b54000004220000000038483d847c0c9680000bec4bc0e33037002d2072c72b9494303610c493183832cb629c4a055c589e585664d071f142d6229a0f37864818fd4f7615c8f583d38353c52905d9a5ab0ebcf9084610d403e386eb112d24f31870c5380c20b426df0b438a220aca2d60c9c01122d7a74043bf5a0e961451ecf08a08108746d2cae890a6016c5a8a23b89fb360619a44a59184811a4a866ba073d80007c29049098f3d245d98db083170f6f70580f120f70000221000343f40c0a000053c21151a280000c6580000b1457e4e9718e610e2000009086bb272c2fd6f8b20511a2e31cc3dcdd300f560000bf9841c3f1405682dc843c000057c4e73148a159e6ca011983490a7175d00000000000066c2e2d974833994eec1c5c000410a0ba000000001d2e27a40000b1e14ac0000d11170800000000ddb8b3a22ae000000014e480000000000169a16de0978215000024e20000b0bc000000017ac0c68000000000000001e833daa00006fe84f4392268dce250c173c1284c0814870e20a700001e314d5000000000000f3d0e4a51427679cec07d403580001df2336531fcc90867238c848588a180001038000000010a9316420d80000eb9332618eccf800003c38000068c82e31ca83e26a8898a31d6426bc11ccc7820e2049459e94aa428a3df090a800017a42464cb987460000634ccd00cfd3c984d38632400032043a182d5044c2a1f0000f611c7701c21db400007be24521634b2a9248c16e605d070a0871ec2000000005f50000782c9399e2e146f1c14267800000004cf4302000000006bb848a80002e7e4094a351fff000000000000000162c0000000206c0ec700004f
  | 69 => 0xe41c3137382a04ab6154221065d24aaa0accabea6608b38800012b63164a1303ad29ee1f06b0b56b300000000e1e97930a58503ecab97e437a85fe0a1e107d2410346c2310d88051078ec2510af041d864ec6038ea23f3012e883982c738c67f2c9f445a036e61e642a71f192e9e62b8d441ea40cf035083a004b3354e6290864c51a00723e3d0a11f9c026d81c504120060bd75bfc89b9e593baf120d006027017742d548b120930fe7473c0b786f816f643908ba85a4a1a070c032f0eaa382e8550b859a6f13f24b2c27120aa3c4621a05b6987c3b4653103b18e729a383f385dc0b1c20711088d781f0e217c413cc554fcf3a8a0edcb1e835a373672b02b9943f08455804db00a06a4562de855f118a1a78484c15401b81f446ed41819f5e04985f40803132b3a75125c6dd9c24054675d862f0a0a2d6a81b90831a3c3182046a9dc0cab30ac66f02ab1af6bfa452f8cd9065b342430040329a2f226867f490e8e050bf27fe60000e113ad86e309660eb6000043d8a96a0d423bc6a44b1c80002238625c95c82f8aa9400007420000000062ac0aa800026082fb87dd92c62cbe5ab6000000023df07f00fb80002ca943ec7af0f02000040b004b5abc9c105b8c7890cbc8000294c941150a8e5e784039b1e9a1f260000000013a10f224e3067450b368a1b54d68c7123c1d39703c39289000024f01100d5a39d01a846e917893c5822b8000130a41320a94bfc89f32efe38f43ad023a3f5800005dacb320000000011f4ac7087612b0f4988f81a243b2c3381cf7000012b4d7015dc1a8046b4c4000003bae4fae000128b800074200000df4318e1d287ce91ee375c603d05e019d0e080b142430e1515745608179400000000000cba027d00001d9a1dcdec80a605d48b178f5f0052564031191810b0d0bdc05e1a4b39fa446490c1dbc40323cc4a1388a4b89624d82ef93bf01440000f029ebd08e87b8432dd6e4a28a81742fc09d1a5570000502507e11e9115062d92ba25892e144dd1c0b124a5d140b418120b7e14b834d1b9227920ab4cd397da093003fc5b4a07a3b1a43b8af420864050097419417202ddc186ed4b99151334238060f95882d0613688cd17eb07ca201873e4c2f36021b6c847812b1d3a6794c2d9932a9167dd469c80001b3a2ad02171d2430700000a2e94a22872000008e006432f03aa03da094213ad79601d80eaab93400010450dbd402a5838ef0546b0000571400000001f3c056d03657d116222e20ee708e51092794400000000000554cfeb99c1017a0b60d9900001b7c00004500f5a425e4fd2f8314bd21842dace1d13f210cf53187568000077e6fbc8e2c0d0000016240000000000078e806f11a903101eca35c079e2b9610906fb00003fa0743501a1f8e29c67f38ecf00000ec268910a81dde00000000036800000
  | 70 => 0x6726f70fac0c7c37c280f0964107729626498e57151015605506e879f02146c7a60db91a8e060e6f18cd70c4e0c5a343479d17411b260000706604200006a8a5ac8000000038684ec8e900be620c0c78144e2a173c1cbaf9e0103165bf87b5864920d809c87cc1156326e06a40cd850d15b453b284242188000000017a0f351f0c52bd06f16af800076902b2da7a07d00000b1481962924000c2d71f3704ae0000a24948d0a8046b8e8280000c7c18a864aa0c7373435ec9b38129000c0000c798691019469482b684b500004fbe9ad03003d6c1a74747501d229c5d641fd81f60a7931a4633150088586b3e0fe8fc502da64d43a28f3c01150000b279604363e77642ff929c0aaa5a4400000001fa21c440000e7d1143667ed8b12f413508318e928c72800000006c815cc020771506ee83f8072e2da89c4dd360cc13a540000fac2a6500003ee5e00309244e26c190f43dfe42d04f891c4b0282d9e7ed170f00005c8c2bd4be0168658c488c1e52000072785d899f29100623c2020a431d1a00009505797000000000001c3b06fa5f500000e34244c71c45d4105c38784bdc546167c303e29fc4cb07c92b0c2498058954c8a2e5708554923d8a144ecc4c19a6a000047a446594e42bec4fc0a7e863527f505b81ae8000359a46e42fc4000077200003d682923e3c4e04b2c080906b63f6400008db27b77b783468e9c19a46788b8c1fa7245d532c79420bc8fba3730b67986226db36b0699957f1fe5680833881029a06521103a1fc23aa62fe89a7815e3cd67da109e1bd317fc3ee49f08585822f22380001a772cea7ee80000000269a7bc4000029a36ee0e6c077841e00003fd873000002eee225509d46de000000000001a5838323a14f7f0000120e000104885b00ef01f7063880002a025c14b6882402dea4ac025291878de4278826d8929b4860000a6e800027ab386e8fb4c3529130000000019720405a400001d5804183fb428118d5000030e400007c9ad3a5edce298000115a66ee8859ed2110211f1023136139ba30dcc935abc145a6618b6f110f1fd63154be8d7b500001044d8909813baa729877d9fc73f6c45f0a89532a093800203e3c5a52bb4772cfc00e7f800039d6ed98cbe0cb3514055e91d5b2bc7460820177438c43128da4a0a481040444f1f8b442ae083400001d0226994d50b37837f37b479c02e8928e319c2b40d4c02e8a9784aa24db95d714620ac050c9e4208c67af804419fc25b1720edf509452610248ccea0c521c6d37c900d01520fd030f069d07a3c1313f786f28b05046014f4bff0cba216a2750c0a83210b9e71c8ef28eecad2c51d8c7b123eaaca558a00012011d2621a46315e2d120826802c79663017634d445e80f59846696c39e6059213200002c4c00003e01a6428306af3b74171a3df85453d88802ca
  | 71 => 0x58223eb0000a3209eb271c3370d36926838180bd499d800000000001020496223641ec24768000000000000000fb300001b64479d202159284e0c5fc0e806640000fb59ab7a6e256842b50466289077b838016ef00000000a3d00002af21f6891680002cbc02840448969000000002da82be236e0810eee450700000000000000025b60954aea1a3a800066a2000000002b80000000198b8000678c00013d9086600006d8000000003300382400017b642685ce9f2000a624481d40000331351f08581cb4234a0818000000042120b28d3e8299000000007140378000000006bb0fa600000c78e379c571eac570000000000000000000000002e261ff09c214e8000000001641d5000005f149e94000000079e42ee948304f30000000000032fc22210801c1a209a000064b8c613e082e970ad969f1992000041fd6770a9a7ae0623150d38be646c9a5953525991d54c830d9236d25ff40001cf32eaa000007497c10d2c0000bc6d5d92ca8836492a00002c730000a0482b124d40b08f9e000030868374bc31f6714266058d1c00001e7c67acad80934116415c845503ee0a2613e0f7a8e0b8b064bbcc9c8d8b27151058f7b8a5c04be560cc49077d1ace35c8a20117a36b06f145a50000091c3ad20000ee3166000005de1b0a2ba05fc4a52000000001c0800015b225622c74c1000003a580ec6d65000031191cec170916c27106b4c3a99cca3b7c0b9831b1d5729ea1c881e5869329dd000030adc50225600000000cff0fdc01f90139c6e00005438d13977d1564000103e9be208a06a0104b00003bf21b285d6d1e7136608aa0c28ec8400422e0a789879208c4f9e16e12ea367254a077dca16375e0d1c43690598e1a385e39f9186337616047ca8c10ab945da05fa9ab235122d5096d54f2a99858761f399703a79703ca3a1eca23da6c405da03562f9820642a089460b2408688c35d990e886406f0e9f6c276a61380001ff6054415e68c400000bc21f5040d955f028e62d4aac006e064a85740001f9d257e0000395162e3bbe0000e5580000000507440186828e2a2954d45172835ea0000f10de33078648708e497a8353e79fc8f7558c34c211185942000249263b0dd20a66bda00f848bb91ce3df6652c6929665299e0e100001b2239a454f2adc1691b77e4b5c19a9ce71fd83c5cde4925680e81350a70c0002c04000000003e900007a744f040001b2838ec430124f0000000006614d618645e441e05d7a181e7a1a55a800000805698f5198ef36ea1fbc96bca00024f75ac5410ba7422c748814b8000000027c8fe000001e966d34bb2800027d20000d721c8ca81173d463a9f1d32824d487030b94126a6674571a09f2836056451640002d780414000109c839033281c607f7235e584400d49564009755426b93013fd27fec7ab9d680
  | 72 => 0x1c384304441c00015f8648c2be0aaf8bee1144c5f1dae2e6856d853799bca75834741670000226a4746ccf066a91765ad60900aee07c45d2c9579c41b00047b00000eef2a1200000000e333b6a57983280ef83680845c5584000220f1dd878698d700006812b768000264e0f0409520999e3c2d080001a54000066286da8431800037f84218f4432c8662a3ac038636380000000013d95c200000000000141665e85118a370f422dcd058a11d00005d346950000000000002f1c00005a9244ed0816d4135b7b34d9881bf0000158000002423c2d62d0f528dc51ffc6c6496209c812f475e6176057116f87c88000186a1d4d7438000002c3b76462c32689fe12305030f27078404da2c249e81f4300003590b40083d364266a07290a6896ac0000536113009920724e9dcc491a52632000000000a886500ea3d48f132828b901b004b074828c80e08e7f314a586413b000000003be6c3001f332a63744ea1800003c649e4000051f000076740000fe928440000aac50bc305a0000000024f317e304cb1b00000000000072209372ca45ea8fe2888f95501a70dd398e4281900001a78605a9a22f0e0001b3e1b5a57b40000cf7107d13d4000160c266a046e06397ef000000000000000289400000001948000030ac45f80e3a15c5794edf92dc00005a8cb6952241fa652dc8e88318296c6b629d41a351d2c53b01d318a8a7da7b244e758a28c7e0000000199b3b5a00009e99e99000045347b4089611f431f600000000c585a2483295df1afa32380000f232b3a1bb40000e2220207b7c1ba9c978a6e589a000000004683d000000000242281c03a418ee8000450eeeedc7401461e525ea9ff43a540fdc0000ede000000006ef8000399618002d306ef00004ca0d9a04e70d7a656065e986d131a6020ae5d6612ce84d60515191222444fd00001bc213f70000677000011e0519c0000c2e2a001c74dac927f00000000906a10c8aa620a8d599099a4427b2c41c168ba63e5b9c6739598123e5e9cd3a98ae8d1600000001a9c2c3d5a7073c48cc202c16e0000007726fc0a46eb10b66180a195d0005f4d09c60ae000003fd000000002cb11c6033226fae9b85500000000000009540000000061c1212113e000043da05622101028d6d83b31647780c0000eb5154f21380000d8a000050e80001c350000638c556810300000000079935b26d06114a00c00038ce5a4c4268ca918d41e2e45606d03b2e31a0a028ad6254a79c4643936408f04a8856f99fb1b8e36a496d06c526ae1e48777000031840000000082f00050000b118445000008b400003852a3d3de811c1c682684537051d8be501066f1046e075700005548e6d17b80ca83a2cbcf8afb02165ad8d8383441a1e72843c29531b2da8314e75883a226c4bf00001bb31aca000000000003ade0000
  | 73 => 0xebe8e4e330e2d8882c9bc300000000ff6912700000000a6408b6000000004d912e78000602410b800031d04f4600006e50f38039e8ccc6e40000611c1d5dec3050f0382a74a06829b92dc43361d75172c15e8000014541be83720eb0f16390c11a0000092840590000b52949e0192366014d89dc00e21464f5e180d3a9c4824de3885913680acc1eb92d01a9646ac0001f5f07fc3b146699f522e6459cccd99447280666fcf671b183cb618510421a6913a200001344e983a9f00002a780002b6e51ee1dd18ba0a3001e400016d0ac542c10ea396db1b363a3831811210fbd615cb321d4b32f67e30eb6476291d224ed0870ace951e54d298553552c7e54123d051c71c7e2242abf122302045b1efb1871a00000c30ea749ce26dc68b43f246b3259e00008f30c930000479400021360a282988a1b80961ed838381421aa09d12108cde905d8412844780000af89b6e84acc9c51472ad24364e7481570334000000010bd953c327468500000d30782ab8d08e227264994000080707cd3f621c015601252589502a9df31888132c4f286e227af7dbc6ed0ce407e07e64d0e953f13243a681b607f33a0846c080d9bfc3e4c4646d70964e29580000a6c883106a8810458d12aa829e0290c2e92fd1776858088a5dec2fa61a00a29831330c63ce4b2102321fe8733053a203905f63c2400003da00000000000000000000b92cc4000000005688000000000000000941c000000061c870d8bd700003360da711bc00004584906049109a1351cc1719d5280b0000ab44000285e00000000964176e396ce81dddea9c261a0848cd220a205ac824f116f412012c4bb5a06d411073600ae93a32d1904ea8391c83366a3d98b2156d3000038241fcdab5188e5650a1b0c6ca8301981085dbf02b826b88e8507a3098c47f8c55188dbb0253763a08ef50f4550d0bcc148e220233f2dcf15a925e2562842892801610091ccd483b88d18258c87820a4052b382a4f4121295161cf0fa61db61d400abe0884e0a3b727adc9670cb72fcc390431c8d5101702bd86861a0d425c280ef2d1470a670587865c8bc423a439786041827218c1b043f3051225460180301d4d83ab62710cfb5a9d1f401d2c9f105e83fe41532a199b76a9ce7e989a489081c5c48285e290872d0a3a282ed9105015e1542fbc8d2f05b65d40cfd1dd41ae619f081f0adc35950da0bde0ae4b50a00001409b200ade66bc682112a2c202468314a127073f62da2c380e6000002c8000044a37f003d8000000d0f4e2bfca82cb7f00000098ce314d317332e5cdb312b800007a14f89167b277c1ed499dc9d5800023f00000fc4420e580c000058413126ce8069060a317608643cb066a1b845d4a00fd30900003424b059f6a08dc7aec00015393cb808a42f905788eca110d07508872c801dfed260000
  | 74 => 0x700000000a46088f2bc2651096299ac93f853f0490800015756168000000013487b4c4a192d510207504bd9ccf90000000074041ea86c4398cd4c800016b40000331800034182e080a480382ce53f740000d3e1eff0000000000040c670dc0000000000077969acdaa90000682800019eda31c000051580001baa00005ec800041940000afd04e6075c2274000000021be744c878889a41ac6b70ae6800018b04bb200000e428c236e4676d51f3bc858626441c5a3f1667982a7d49018a6464c06e80001136121c00002bd09780000d16d176000083cc00015d89dca40e08b3d88c00006f6c873000011600000ff417fa00005558000131a323e477c7354de2418836145f21dac22a882c80000c74000030c0742c000339a000010e1747391637803e080000000815c5c2042000000000f5b5d3e9fce4dbb01aa11a2dd45284f3b000000000000000077c0160852c2ca05ecb28a0070d65ce4a3dd02a8c8029c11019b3a6cfb100003524825cf59990d3fbc8530c419c120be900001fd4d3421bc3fdaec81117416a1894f6d19591e6625488a60bdc34ae1aa4b5dc9cf1d801454b8a11893b8855902ec9d1419de39d05d90ee828583bc467e09518b5020b4fd415ac144c5b2e0000cf81342112054e09d0073c2595072807c1f4a273011399b5b7ec3c7c9878b67057e295cb55d6f03330737ca328a4600001280304197d03c076209fb40000bb8000099911fb03a84f902c0db7d40125bd84f700000bca273400012c73da81762d9520111d7c629829a96ac00000fd6fd800001c5600004bb8b0f3708344cdda00002c7000001360f4d11d056f00059d3d16680a5078c9d2936ca693c1c79f7000000000a9b0000000000000001245006700001558ca1255a5d9c00020fd099484040001afe41d22510a191f8224de5154f9e93a90f8177a8000147d34d8405c0000bdf0cca00000000ce202576402000075f000076dc0000e5d07808148709c00028da165c000012699001edb05b179600003b0cafd9de1407e2f28df388733f0244fcd5c5ee934e23e7cbda050411e44a58e8d838b018c286c1fb088e86822328ebb89fa2e6c3294c3480782104384c2d49d48b698324877306d80c64553b00191ac262a62a43aa11948f6448f8f3384f93a2e26409e2978c4002113c61d14a7079255f435c9910a36353e858f9297417e6bb0c5820d8332e0ca80d41fe315266a687d08e3e12560c14c66179441c40000bbe1e600fce759c7d81a5603d432148e98b8b16fc60a861506611236581413c907b20a354bc49c81f20eba18880001bd105f03dfc889c6101f283a3c5d188c915a67320a78d6483080029c00000003ba200000000011209023fc483193c000000005c8001541e2724e9ea49a92af60000fdd9cd91362164c3b594ba224046fc97913df0d0a000
  | 75 => 0x1c1a6a0653238228eb041ded18ce54f6f9a9f462ca26900000000006765d18ea6905f0e7c43b0000000014f45e644cc01b114f245808989cb019e48320a8fd3748c0954dc6459f7219d04fa80c8034003264188c2e182b208432bc8048abb29db19f4836d4d407221f18f848fb7042a6a84d52000032c017785c90fa8000017bc62013d39c645f18b15959e0d9a497c94c082c114c2944b1b8be2aa983c50b855d0926e46ab08d09ada056c7de82a580001c3045f6000095900003e0c4690dc03400000000000001e4c500a71006e8098040e600009f5000000003039f0541d6000000012600000127452c8f3f00a800000de8804000036e0f3a0000000000000710e0fbc1a7d847b896e11b5c589c47880001a6218662a14b2d28ac1630424ddd81dbe0ddc1d7c4ed3f944320a2c18fcb58c573c2cc128430a88554dc0925310912645035956a0a5a44bcbfb0818187e418d0608e431c8c171c8c1857912bc000031419dd29b521f4936a0b4300c62b109a1196ae4c10aaf5c846d1da60104f3b92ed2d2481f8647e08a930055348961c9b114211a4a6020e33e6423688f887ba1dcd24801cb0c961fc651becb51a932c8828a0000000015e44e6ccfc53e6a9c01a5c4dc0eff000077187e90c312bd6595800009ad22181e183bd1ea91d3d1ea80001302087e601cba6183b3d56681c0e3828b26bc1d887ee176938aa14845b70c1805be274c52d9c03042835543560c4f16626af84138efd2a0653e294c83de193233ec072976f078704501ec022632348078b260d9142c84b58dcc9db20c1e086000007b3000074c4000000019500000a67215a000046e812a613300002a9adcb0000382684e40841f9e04dc75ea72602eb0a7480dc71e4ca204f67b5c125150cc1fe7bd0bef052a0de970981a900000000000040e84e12acc000089e9d3e3f56008c0000449119503d0000000000004888000000028fc0000ce81359000006dca0e1097073a7cec2044000000069fc90000000000000000020a380007358e26d45107a423b8000000021800000ea600000ee452ecfd102a039884cd0a7342888000182a0c08856224728040000ddb281618847ea8a7541f4517a000077739440000dbc03eb2a385cf4e720ed51d2d12ec9c34e4716a0683c00017c2046c00000758000259a0670b4f1ca7123a40cc0001c5c800029320001bb200003924b12d25500005e04ac7207823765486000070319821e0c3209faf2b2a7fbcaa000171d8e31bca3489000d1c25844eb8e401d0d64248f6c67e3eca394071c924a917516cc7dd186e19982acc0e0055c3eb408eafb30237061c57a843b14a33d0b0000b5b8000282c000005011d600007430000147526e744580ef1c9f1dc478e4b48441a40263d7475f880d000b39e4000193f2b0e7892ce2467a1d7402a863c924
  | 76 => 0xc40000000064119131f32000000000003d4e706c000000000005546e67059111fc4a400000f8ab8d639846bf1f002c480e502ae800e423c5848e7d884b800024d288700001298457101fc909127b000036d11adb1c02cd4f9f00001a9c34188710a070000602885d0558080a80c082ad7f3805a3f5c00017cd1cac0000f9b1f4428b40080baa0241129c608478d030d163202540a9800000004d283af1d49b6100000217cbb300a00008fbc0f302aa1531600011070477013086d964b37e84f2059f86b21e86073000000003346389455f832c09987594cf49c22099a51e400a15d7b63c4594321200739183030c82573716e41f807b70ba9000000009450000251d00005de987721560cb8c7c88a535ee78c0e4a97c92ab865b00fa90662d161c987d38e4810e847b2c7502ed05c400000a0055416d800003fb13a1271a263018dd0513f723c105274000000000008ea000000002b4458c0e21800027b40000e2a1f4600002f01787014750489419fa40000563f08c52ec1f816650e3f1e383feb5d680000278197f0000cfb81e500007e940541719000050f816200000fbe2aac6b400001e683d9c0001a7e3e6266583610b03b1d632fcfac8ccdc2942e90daa9a622cf05ac0a340bbe1efc74e47069daf23b675c88071caf17d43a98502c4f1262267de4689a230eac25a817519998fb746081b4811520c04634d6a0fb833d105307b18ded339e6fb01f1910a3c5e415c3d104de3bcd5e2802c19a79de633d85ded40832aa39884641dbd2a5c495c0fc991d35a212200e6970c071041bd0b199721dee758c4fb0ef411a80d149ed57c82d7252c0425105d184049d4e9307311dd53c3c3ea98db27185b585900d0732fe1c84b5110c5228918f45adc000312a7f20343826622854c1c8e4108b0d506d6c27e89ff3a5005587ff800027ca5ba47cd000000000b2c6e71591147c735000008f73318791ce2100003c400000b6580001f941804efe962095886832000060b126b0000000048c0000267c0000e1002305680ce102aa33b268a4d6c80000000292000000003eda6d0400000de8ece000004f9eaf3eaa00000000e8c8b38236406d8000000000005630af688fe5a300000000000065080001b6e067c47610949e310000503400012052b217872000000029000628c4888322bc41a480001d860d8e3fdc586e0f40f88216c0f7472e3c644e0803fc83c1efa468cfd0926916584da42b09def0fb6000087c820b29e76748d5d94bf00000000000000003a05fb4a380fef00004f78000066b033e172ca2114d02edc00006ad8b9b110640c4f390d20000009cc21a98d1053a6a0429cdf91173436d8c9e813f3bf62154d531a7000a775f8a361c4128cc5ab2f970f130cf60000c411b48213e52a483d07750b165ef498b06c832a46c8ccc01c0e23fa2c
  | 77 => 0x2c4017907842111098e7e80e97989f40c0492c0a308e703f347301f7855f09e0392ca2b887519a830484b5841902262c405951195a1a45b7460684d13dac1886f2e83c29f0846742f687319af23e2e6f9813c3d1859882cf1a2125c634acc6e9bc8289e2d4cd929e2b2a292528000000018c87010c07126c33e661d0000012d10ae2ad8d5a0780806c0000000000031be000007d0c9f00007a220000fb400000000d680000091429c0000000008ce0000000036733697a28aa200df230a251c8f50000303050c4000000040900000828447e000000001fa932f000032d4000000036f41214bf61b52261a71a800009a526003a0c00000ae00504680cca8c1a3d8e3bf82f320c321c600003cf9607027a3b6c00d8000396c00000000af13368000108100
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd7050dd741440033e100bae828801a3d61f64d0510034dac3ec9a0a20018f787593414403b36f0ea168288002dc21570d0510036d93a2e1a0a20019f280dd52144001ae0a1baa42880063d2197548510004da422ea90a2000cb476dd121440031ed0d3a242880666da12744851000cf9400e890a2000db2401d12144001968ec3a24288067696087448510006d9400e890a2000db1801d1214403396ec03a242880676cd807448510006d8280e890a2000db2301d12144001b64403a24288003748c3734851000c7a432e690a20009b4845cd2144001b48e9b124288002e96106248510006d23a0c490a2000bc5831892144001b48e92124288002f160e4248510014f243a8490a2000ba5848c92144001b48e91924288003691d13248510006d83a6e090a20108f987d9750440212f30fb2ea08800a3ee1d65d4110014f840ae9a82202497b8754b5044021ae4eab8ea088002ec21171d41101dcf9c3aa3a822010d7275547504400176108a8ea0880027c61f41d4110005d842243a822000c7876dd54044001e6083baa808800a3ea1a7550110144bd42ceaa022000db0419d540440053e5023aa80880035c9447550110006d8208eaa022000c78761d54044001ae0e23aa8088003cc10475501101469cc20eaa022000d72811d54044001ae3023aa80880a31ed847550110146b9b08eaa022000d3a411d54044001a70823aa80880035c104755011000698208eaa022000d72211d54044001a70ebb2280880034e1d464501100069c3aca8a022006bb08195140440033710eaa2808801aec2055450110006f110ee4a022000d3875d09404400d76103a1280880034e1d54250110035d840a84a022000d7075dc540440013e10ea8a80880035c1d55150110005d8422a2a022000f3154545404406b3e50fa0a80880035c1d741501101add942682a022000d707548540440017610890a8088003e850921501100063c3b6ea90220028fa869d520440412f50b3aa408800a7ca047548110006b9288ea9022000c78761d52044041ad3043aa40880035ca047548110006b8c08ea9022020c7b611d52044041ae6c23aa40880035c1047548110006b9188ea9022000d72211d520440053e503ba240880036c10774481100147c432e89022000978855d12044001ba463b9a408800a3e2197348110004bc42ae69022000d6875d8920440016d30a31240880035a1d46248110005e4c18c49022000d687594920440017930729240880067a21d5248110005b4c2c649022000d68758c92044001ad0ea99240880035c1d77148110006b83aaa29022000bb0845452044001ec2a4a8a40880035c1d74148110006b83aa629022000bb0844c52044001f826498a4088006bc2192148110016783b2429022000d707548520440017610890a4088013b81892148110
  | 1 => 0x90cb8ca4880035c14171949100147c432e1292200087f855d9524400117f08bb2a4880222f21176549100046fc1aeca9220328dc835d952440011df04bb2a4880021fa1e65549100243e43acaa922000a3c8459552440014b906b2aa4880129b20965549100147d436e0a92200b87c855d8524400117f08bb0a4880222f21176149100046fc1aec29220328dc835d852440091d904bb0a4880021f61f651491000c7a432e229220009b4845c452440099c8c4b88a4880035c14171149100147c432e029220048be849db42440014790ab268488002a720d64d091002556412c9a122000aad8418b424400159b06316848800a3e21970d09100069a20ceb2122000c3e75d92424400187cea324848800327d9273909100064e324e72122000d94419ce42440031e90cb8c848800a3e2197090910006d820ae1212200087f855d942440170f90abb284880022fe1176509100046fc1aeca1220328dc835d942440011df04bb284880022fa1e64509100245e43ac8a122000a3c85591424400153906b228488012ab209645091000c7b436e2a12200087f855d842440170f90abb084880222f21176109100046fc1aec21220328dc835d842440091d904bb084880022f61f641091000c7a432e221220028f8865c042440012f10ab8084880036c105701091002477414ed1922000c5e75d8e324400193ce9b1c6488003179d4638c9100064f3a0c71922000acd8218e32440014d90ab146488002ab211628c9101956641ac519220018f4865c632440051f10cb8464880021fe15764c91005c3e42aec99220008bf845d9324401117908bb264880023be09764c91005c3f428ec992200087d851d9324401117d083b264880022f610764c9100047743cc499220328ec8758932440014d90ab126488002ab211624c9101956641ac4992200087f855d832440170f90abb064880022fe11760c9100445e422ec19220048ec825d832440011db0fb106488002b3a19320c91000566432641922004ccf764c8324400199aec99064880063d219710c910004da422e21922000dc5325c432440051f10cb8064880025e215700c910006e4992e01922000cb476dd15144001e60a1ba2a2880067ca007454510006b8280e8a8a2000db2401d15144001968ec3a2a2880036c1c0745451000798280e8a8a2029d35851d15144001a6eca3a2a2880034d1947454510006d9400e8a8a2000db1801d1514405396ec03a2a2880a76cd8074545100069b280e8a8a2000d34501d15144001b60a03a2a2880034c1407454510006d9100e8a8a2000d3474d5151440216e101aa2a28800a5d21d5454510085b8402a8a8a2000de220dc95144001a68e9a92a288042dc20352545100069a3a2a4a8a2010b70805495144001b60e9b82a2880063da1b75d051014cdb426eba0a2000
  | 2 => 0x572cc520196663b26598a4000e4c654cb31480170fd0bbb262900021f617764c5200445f424ec98a40008bd849d9314800187ecbba262900030f197744c5200061fb28e898a4000c3c651d13148001998ec992629000393195324c520006c63a26498a4000c3f65dd12148001878cbba242900030fd9474485200061e328e890a4024c7a76d9720480178f4ec32e40900034e1407459510006b4280e4b2a2000c3f751d1654400187ca03a2ca880030f140745951000657ba6e4b2a2000cac74dc9654400199ee7b92ca880031bdd4725951000657ba0e4b2a2000cac741c9654400199ee6392ca88003331cc725951000637280e4b2a2000c6c501c965440010ff0eb28ca880028f211651951000536412ca32a2000d34411d56444001b4882392c8880030f90475591100061e208eab222000c3c75dd164440018deebb92c8880031b1d7725911000667b9ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c9644400195c82392c8880032b10472591100045fc3ac83222000a3c85590644400155904b20c8880028f61764d511000c7a432e3aa22000cb7645c7544400147b09b2ca88800a3e21970951100063db2ae12a2200087f855d9544400117f08bb2a8880023be09765511002476412ecaa220018f686dc554440051f50db82a88802e1f21576151100445e422ec2a220008ef825d854440091d904bb0a8880032d105761511000c7a432e22a22008cb4645c45444001ae0a0b88a88800a3e2197015110006d820ae02a220008bf845d7624401117908baec48800237e0d75d89101946e41aebb12200087f855d362440170f90aba6c48800237e0d74d89101946e41ae9b12200087f855cf62440170f90ab9ec4880022fe1173d89100445e422e7b122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6c75dc96244001958e9b92c488003331cf725891000c7d43ee0b122004cce625cc62440011df0eb10c4880029b215621891000556422c43122000acc83588624400199ae6b10c4880131b209751891002637902ea3122000c6d205d4624400995904ba0c4880132bc8574189100065690ae83122004ccc325cc624400999904b98c48801333149731891002666212e63122004ccf215cc624400199a42b98c48801333c81731891000666902e6312200487e859db524400147908b2ea4880029720d65d491002536412cba922000a6d8518b524400159b06316a4880063d21971d49100061fb2ce92922000c3c659d25244001a70a13a4a48800317d9673949100062e32ce72922000d58509ce52440031e
  | 3 => 0xb2124000c5f659ce42480018b8cb39c849000317d9573909200062e32ae7212402487e869d732480410f90cbae64900921fe1f65cc9200043ec3ecb992400b87f8719732480010fb0e32e64900030fd9674cc9200061e32ce99924000c3f655d33248001878caba664900cb2718d74cc9200064eba6c7992400087f87d9632480010fb0fb2c649002e1fe1c658c9200043ec38cb1924000c3f659d23248001878cb3a464900030fd95748c9200061e32ae9192400096d879d632480018d90cbac64900131bd81758c920026b5b02eb1924000d6a105d632480012df0fb2c64900031b5d6658c92000476c38cb1924032ace8319632480012db0e32c64900029be1c658c92000637438cb1924000a6d8719632480018db0e32c64900021b61c658c92000727418cb1924000e4d831963248091cd42032c64900034b5d6748c9200071632ce91924000cae765d23248001a5aeaba464900038b195748c92000476c3cc91924000a6e85992324806559d0732464900831e1c0654c92002566410c69924000c7865dc132480031d90cbaa64900931b1db654c9201947743cca9924058a6e85995324806559d0732a64900031bdd4654c920106363b0ca9924000c6e87195324808b8db0e32a649011b93e0c654c92023726418ca9924045e6870195324808bc9e6032a6490117934c0654c92022f35080ca99240328ee8799132480014dd0b32264900cab3a0e644c92020d67436e69924000b4e85dcd3248001c98cbb9a6490002e3a13734c92019567436c69924000e4c65d8d3248001c9eca31a649000393194634c92000567438c69924032cce8718d324808d59d0a31a6490112b3a10634c92000566c08c69924004acf8018d324808359b0031a649000273a1f534c92000567436a69924000d4f75d4d324808dc98cba9a64900cab3218534c92023726328a69924000ace86d0d3248001c98cba1a6490113a3193434c92019566430869924000e4c6510d3248001cd0cbb8264901231b9c8650c92000727b2a641924000e4c654c832480031f100baec2900021fa1f65585200043f438cab0a4057c6f72195614800187ecbba2c2900030f19774585200061fb28e8b0a4000c3c651d161480018becbb9ac2900031719773585200062fb28e6b0a4000c5c651cd61480050f90abb6a29002f1b19672d4520004e6c1ce5a8a40018ec865cb51480178d8cab96a29002e9b21952d45200445f424eca8a40008bd849d951480050fd0fb2aa2900030fd9774545200061e32ee8a8a4000c3f651d15148001878ca3a2a2900429b2195254520006363b2a4a8a4000d2c7454951480010ff0abb6829002e1f21576d052005c3f42eeca0a400087d85dd941480010ff0abb6629002e1f21576cc520004b6c2ce598a4000c6c659cb31480031d90cb9662900031b19
  | 4 => 0x4480110f90abb6a89002f1b19672d512000c76432e5aa24000a3d84d9654480010ff0abb2a8900221fa1f655512005c3e42aec2a2400bc6c659c8544800139b07390a8900063b219721512005e3632ae42a2400087f855d363480170f90aba6c690002a761031d8d2000566c1063b1a4000ad9800c7634808b8dae432cc6900030fd967498d200061e32ce931a4000c3f655d26348001878caba4c6900cb2718d7498d200064eba6c731a4032c6e329d663480658da653acc6900cb2b8ca7498d2019656994e931a400087e87d9563480010fd0e32ac6900031e8407558d200063c3aee0b1a40008df8758c634800117f08b88c6900222f2117118d201943e42aeda9a400bc6c659cb53480031d90cb96a6900123b20a7694d200052ec1ecb29a4000c3f659d25348001878cb3a4a6900030fd957494d200061e32ae929a4000c6f659ca53480018d8cb394a6900063b2197294d2000637b2ae529a4000c6c655ca53480010ff0abb2a6900023ee017654d201943f43ecaa9a4032a5e83d9553480170f90abb0a69002f1b1967214d2000c76432e429a400bc6c655c853480010ff0abb6869002e1f21576d0d201945e422eda1a40048ec829da43480010ff0abb4869002e1f2157690d201946e41aed21a400087e869d643480010f90cbac86900021fe1f6590d200043ec3ecb21a400b87f8719643480010fb0e32c86900031bd967290d200063632ce521a40018ec865ca43480018decab9486900031b1957290d2000667b1ae521a4032ccc635ca43480170fd0bbb286900021f6177650d200043fc2aeca1a400b87c855d943480011ef02bb2869000a3d2057650d201945f43ec8a1a40088de87d8d43480010ff0abb0869002e1f2157610d20004b6c2ce421a4000c6c659c843480031d90cb9086900031b1957210d200061fb2ce92924000c3c659d2524800187ecaba4a4900030f19574949200062fb2ce72924000c5c659ce52480018becab9ca49000317195739492005d3642ced2924059e6a101965248001c58cb3a4a4900032b9d974949200071632ae92924000e4c659ce52480018d8cab9ca490003339d973949200072632ae72924000d8e745ce5248001b1ae8b9ca49000353d9573949202366732ae72924046ccc655ce5248001a98cab9ca49000313195739492002667b02e72924004dcb605ce5248001b9420b9ca4900029b21953949201263c386caa924024c6c76dd5524800165d09baaa490002d3a0f7554920126b4386eaa924024c6c76d9552480178d8ec32aa4900029ba1a5454920166363b4a8a92400bc6c7615152480014dd0d29aa4901431b1da535492000597424a6a924000d4f7394d52480012dd0e29aa49002f1b1d8535492005d36432a4292400087f87d9642480010fb0fb2c849002e1fe1c65909200043ec38c
  | 5 => 0x2b3a1c634cb2002667438c69964046ace8518d32c808959d0831a6590002b3604634cb2002764c00c69964004ace86d4d32c8001a9eeba9a659011b93197534cb2002566430a69964046e4e6514d32c800959d0da1a6590113a3193434cb2002566430869964044e8e6410d32c801117d0fba2c3900232ba08745872004656c10e8b0e4008cba801d161c8011973003a2c3900032dc4074587200065a880e8b0e4000cac748c961c8001958e8992c3900cb331cd32587200045fc22eca8e40088bc845d951c80050f90eb2aa3900030f99474547200061eb28e8a8e4004c6c7654951c8001a58e8a92a3900022fe1d64d07200045fc22eca0e40008be8799141c80051790eb2283900022fe11764c7200445e422ec98e4000a9d8498d31c8001938e931a639000a3721d634c7200064e3a2c698e4004ccc764c931c8001b18e899263900030f5d074d95200062fb9ce7b2a4000a3e841cf654800147b0839eca90003175cc73d952012536c10e7b2a4000a3e84dc7654800147b09b8eca900929ea0071d95200053cc00e3b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a4000a6e8210765480014db0420eca900929ea0041d95200053cc0083b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4000a6e820c765480014db0418eca900929ea0031d95200053cc0063b2a400087e8708765480010fb0e10eca900028fa1021d95200051ec2043b2a4000a5e8308765480014bb0610eca900929ea0021d95200043fc3aca32a400bc5c535cc654800117f08b88ca900222f21171195200053cc04a232a400bc3f749d065480018dae53a0ca900028fa1273195200051ec24e632a400bc5f739cc654808b4db05398ca900031b5ca731952005e2e39ae632a4020a7a809c465480014f301388ca900028fe1171195200051e422e232a4000c6d725c465480414f501208ca900029e602411952005c3f4388232a400087d8710465480014bd06208ca900029760c4119520005374108232a4000a6d8210465480414f500208ca900029e60041195201053d4046232a4000a79808c465480170fd0e188ca900021f61c31195200051f4206232a4000a3d840c465480014dd04188ca900029b60831195201053d4006232a4000a79800c465480414f501108ca900029e602211952005c3f4384232a400087d87084654800147d08108ca900028f61021195200052f4184232a4000a5d8308465480414f500108ca90002a760c41d912000556c1083b224000ab98010764480b58dae432cc89000317d9673991200062e32ce73224000c5f655ce64480018b8cab9cc89000327d9173991200464e322e73224032ccd829ce64480010fd0fb2ac8900021fa1c65591200063d080eab2240008bf875906
  | 6 => 0x5e1e32ce9a8a80018bc865d35150017878caba6a2a002e8f21954d45400445e420eca8a800287e87d95515000317d0dba2a2a00030fd9774545400061e32ee8a8a8000c3f651d15150001878ca3a2a2a001a4f21d54545400851e432a8a8a8000c3c7655151500b987ce832e82a00038d10765505402de1fba0caa0a803edb041dc141500010ff0abb642a002e1f21576c85400061e32ce990a80018bc865d32150001878caba642a00132b1d942c85400071632a8590a800b87e85dd921500010fb0bbb242a00222f210764854000c5f436e890a8000c3f65dd12150001878cbba242a00030fd9474485400061e328e890a80069ac875092150001958eca1242a00038b19542485401663d3b6cba02802ce3b64d9740500178f4ec32e80a00066e21171d0140046d820ae3a028004c3f529d365c800987aa53a6cb900030f94274d97200061e284e9b2e4004c5f529cf65c80098baa539ecb900031794273d97200062e284e7b2e400487c855d265c800117f08b88cb900222f21171197200261fa14ebb264004c3d429d764c800993e8539ec9900132750a73d93200061f3ac83b264000c9e7390764c800187cea20ec990002a760c41d93200064f39883b264000aad8210764c800917908bacc9900122fe1d64d53200051fc2ac9aa64004cae7259354c80090ff0eb2ca9900028fe11659532019637194eb31e4032c6d329d663c80091b906bacc7900cb1720d7598f201962f982eb31e4000c5d305d663c806595c653a4c7900cb2b4ca7498f200246e41ae931e4032c9c835d263c806593e62ba4c7900222fa137558f200045ec26eab1e400b87e85dd163c80010fb0bba2c7900022fe117118f200445e422e231e403287c855db53c800147d09b2ea7900ca97a0f65d4f200052ec2cc7a9e40048df8758f53c80014bf0ab1ea790013339c963d4f2019476c12ed29e4004c6e7299653c80014bf06b2ca7900131b9c96594f200061f32ce929e4000c3d659d253c80031dd05bb2a7900ca1fa1f6554f200051f426caa9e4032a5e83d9553c80010fd0e32aa7900021fe1d6514f201945e422eda1e4000a3e85d9343c806553d07b268790002a761263d0f200246fc3ac7a1e40328ed825da43c800187ceb32487900132b9ca6490f200061f3aac921e4004cae7259243c80011ef02bb2879000a3d2057650f201945f43ec8a1e4000a3e85d9143c806553d07b2287900022fa1c6450f200045fc3ac821e4046cce655ce52c8009998cab9ca590092da2015394b2002537434a8a964004a6e8694d52c800165d0929aa59000353dce5354b20004b7438a6a964000c6f865d632c80098d90cbac65900031b5d6658cb200053742eec9964000aae84dd932c80033d100baa65900023ba1e654cb201956741cca9964032ace8399132c80011dd0e322659
  | 7 => 0x7f855cf62500170f90ab9ec4a0002ab61021d894000566c1843b128000ae980087625009987ae832cc4a000317d9673989400062e32ce73128000c5f655ce62500018b8cab9cc4a001333189739894000666b9ec5312800087e87d9562500010fd0e32ac4a00023be1d62189400045ec3c8231280008bd87104625000153b06208c4a0002ab608411894005e1e32ce9a9280018bc865d35250009179093b4a4a00030fd9674949400061e32ce929280018bc865d2525000187ecaba4a4a00030f19574949400062fb2ce72928000c5c659ce52500018becab9ca4a000317195739494002537416caa928000c3c769515250017878cb3a0a4a00062f219741494005e1e32ae829280008bd87197425000955d0432e84a00030fa1c65d09400061ec38cba128000e2e821974250001c5b0432e84a00030f9c465d09400061e388cba12804de3a101974250001878cab9e84a00022f61c63d09400064eb98c7a128004aae8218f42500590fd0d3ac84a00a21f21975909401643fc3ecb212800087d87d9642500170ff0e32c84a00021f61c65909400062fb2ce72128000c5c659ce42500018becab9c84a000317195739094002666312e72128000ccd73d8a42500031790cbaa84a00b30f1db65509400245f43ccaa12805da3e85995425000955d0532a84a00030fdd465509401461e3b0caa128000c3e87195425009987b0e32a84a00030f9c465509400061e388caa12804ce3a101954250001878cbb9a84a00022fa1c635094024d57436e4a128000e2c65dc9425000955d0db1284a00038b197625094000717b28c4a128000e2c65189425000155d0e31284a00132ba1c625094000657b98c4a128000aad81189425000195ce231284a00032b1c4625094026e1f3a0ca21280048bc849da32500010ff0abb464a002e1f215768c9400043f434eb192800087c865d632500010ff0fb2c64a00021f61f658c94005c3fc38cb192800087d87196325000187ecb3a464a00030f196748c94000c5e432e91928000c3f655d23250001878caba464a00132b189748c94000656ba6c51928000e2c65d0a32500170fd0bbb264a00021f617764c9400061e32ce899280018bc865d13250001878caba264a001a6d205744c9401956741ec49928000cad741893250001c58cba1264a0003a318f424c9400043fc2aec192800b87c855d83250001878cb3a064a00062f219740c9400061e32ae81928000cce764c83250009998ec99064a000393d95320c9400072632a641928000d8e744c8325005987ae9b2ec2a00038d90765d85401461eba0cbb0a80068bd87d0b615000117f0ea16c2a00021fa1f65585400071a20ecab0a800087e8719561500b787ee832ac2a00031bd9772585400063632ee4b0a8000c6f651c961500018d8ca392c2a000a1f21576d45400
  | 8 => 0xe731e85a0012aba0a63d0b400045f43ccaa168000c3f7599542d000955d0532a85a00022fa1e6350b400051f42cc6a168004aae8298d42d000917b08bb465a00123b209768cb400062f3acc71968008c9e7498e32d000159b0531c65a0003179d5638cb400464f3a2c71968000cad76d0a32d0001d1cc7a1465a002e1fa17764cb400043ec2eec99680018be84dd932d000f36902ba265a0002b3e19320cb4000566c32641968044cce764c832d0089b1ce899065a00022fa1f425874003c5e43a84b0e802f8bf845d951d000317908bb2a3a00230f1d265547400143e43acaa8e8008c3c7459551d00112790eaa2a3a00762fe11764874000c5e422ec90e8008cac7498921d000159b0731243a000a3b21d6248740046563a2c490e80089ac8750921d000127d0e20ecaa0002cb60841d95401659d40083b2a8000c6f729cb655005947b08396caa000297a0c72d95400052ec18e5b2a802ca3d84dc765500594f50038ecaa00029e60071d95400043f43883b2a800087d8710765500014dd0420ecaa00029b60841d95401653d40083b2a800087e8708765500010fb0e10ecaa00028fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa00b29ea0021d95400053cc0043b2a80008bd87906655000196ae320ccaa00028f614419954000556c108332a8055c3f75dd165500010ff0eb28caa002f1b14972195400053cc04a232a8000a3d85904655000117b0e208caa0002ab60841195400065ab888232a8000e3461904655000127b0e208caa0002cb60841195400071b3088232a8028b3a80104655009947b09390caa000297a0e72195400052ec1ce432a800bc6c725c865500514f501388caa00029e60271195402dd1fc22e232a8000c3d745c465500514f501208caa00029e60241195402dd1fc3c8232a8000a3d87904655000147b05208caa01838ea0241195400071cc048232a8060e3a1090465500170fd0e208caa00021f61c4119540005374108232a8000a6d8210465500514f500208caa00030fa1c41195400051ec388232a8000c3d87104655000107b0e208caa00038ba0841195400051ec108232a8000e2d82104655000145b04208caa00038da0441195400071b3888232a8000e357110465500bfc7500208caa00038e60041195402ff1b8808232a805fe3a1010465500bfc6a20208caa00a29ea0221195400053cc044232a800b87e8708465500010fb0e108caa00028fa1021195400051ec204232a8000a5e8308465500014bb06108caa00a29ea0021195400053cc004232a8008a3c84d97545005947d0daa4a8a002e8f21676951400061f388cb2a28000c3c7119654500bdc742032ca8a00030f19572951401663c386caaa2802cc3c76dd55450059a70e1baaa8a00b30f1db655514005e1e3b0caaa280008
  | 9 => 0x75c87500045fc22ec90ea0088bc845d921d400147b0a20ec8a8002ab60841d91500055cc0083b22a000caf645ca6454011958c8b94c8a80022fe1d64191502f51fc2ac8322a008cb4415c464540a747d0daa4a8a80b31ed95709515000536c2843b12a000aad84087625400159b0610ec4a8002ba60021d895002656312e9312a004ccc625ce625400195ae9b14c4a8003335cf629895000477c3ac4312a059a6f85588625400117f08b88c4a80222f21171189500043ec38c7a92a004a6e8218f525400187ecb3a4a4a80132b18974949500062fb2ce7292a004ccc625ce525400195ae9b14a4a8003335cf629495031c3f436e6a92a00087e8718d52540090f90b3b484a80061f219759095002666312e7212a000c6d75d8a425400199ae7b1484a80ca37a0f76509500046ec1eeca12a00087f855d842540010fd0d3a884a80061f21975109500243e42ced192a00187c865d63254009958c4ba464a80031b5d7628c95000656ba6c5192a062a6e86d4a325401117d09bb264a80022f613764c9500043f434ea992a00187c865d532540032f100baa64a80cab3a0f624c9502c537436a4992a000e4c63d4932540010ff0abb064a80021fa1a750c95000c3e432ea192a000cce764c83254009998ec99064a8003539d5320c95030e1fb28e8a8aa040e7050d8551540010ff0abb682a80021fe1576c85500043f434eb90aa00187c865d7215401117d093b242a80022f612764855000637284e5b2e8000c6c509cb65d000117b0f20ccba00028f61641997400065ab8c8332e8000a3d8510665d000155b0420ccba00222f21171197400465a20ae232e8008a3d8799654d001787b0f32ca9a00230fdd7765534022667b12e73168004ccc625ce62d0089b1e84b9cc5a00130fd0a7598b400261ea14eb31680048ec825d662d00098d904bacc5a00131bc817598b4000636902eb3168032c9e849ce62d006593b0939cc5a001327d0a7398b400264ea14e73168004ccc325ce62d0009998a4b9cc5a011333d097398b4002666212e73168004ccf215ce62d000999e40b9cc5a0003334817398b400045ec3c833168000c3e7590662d000193ce720cc5a00022f61c4198b400061f3a8833168000a9d8310662d000193ce620cc5a0002ab6084198b401946f41eeab1680008dd83dd562d00170fd0bb9ac5a00021f6177358b400243e42aeda968000a5e83d9752d00094dd05b2ea5a00029b61662d4b4000566c1cc5a9680088ef8758b52d001195ce8b16a5a00122f6117694b400461f3a4cb2968008c3e7459652d00018bccb39ca5a0003175967394b4000c5f426eca96800487e87d9552d00014bd07b2aa5a00129ba0b6554b400043f438caa968000c3f7695152d00010ff0eb28a5a00030f5d665d0b400045ec3cc7a168000a3e8598f42d000193a
  | 10 => 0x1924200d2e755d23248401a5aeaba464908032b219748c92102657b0ae91924204da7615d23248401b4e20ba464908026be1f648c92100656ba4c919242008ed87192324840135b0e3246490802abe1c648c92100657438c91924200aad87192324840195b0e32464908022b61c648c921007173a8c91924200e2d751923248401d1d063246490803a360c648c92123f53880c91924219cb4711913248401968c9b8a64908ca3ba1e654c92100557424ca9924232ace8399532484051d90cba264908772b1db644c9211947743cc89924266aae84991324846559d0732264908032bdd0644c9210ce563b0c89924200cae87191324848795b0e3226490913a3e0c644c92122746418c89924243ea4711913248487d1e62322649090fa34c4644c92121f53880c89924242ace86dcd324840169d0bb9a6490802e3a13734c92100746326e69924232ace86d8d3248401d18c9b1a6490803a3d90634c92100746320c69924200ace8718d324846599d0e31a649091ab3a14634c92122567420c69924204acf8118d324848559b0231a6490802b3600634c92100567436a69924246e4c65d4d3248401d18c9a9a64908cab3218534c92100746320a699242009ce87d0d324840159d0da1a6490913a3193434c92119566430869924244e8c6410d3248401d48c9b8a649091f2b9c8640c92100747b22641924200e8c644c832484031e902ba6c0908022fa1f64581210061fbaec8b024200c3c75d91604840117d0e322c0908030fdd464581210061e3a8c8b024265caf72191604840193ec9b9ac0908032719373581210064fb20e6b024200c9c641cd604848d99ec4b9cc5a8013331897398b50236a7a92e7316a004c3f529d262d400987aa53a4c5a80030f9427498b500061e284e9316a032c5e859ce62d40658bb0b39cc5a801317d4a7398b500262ea94e7316a000c5e509ce62d40018b8a139cc5a811b33d497398b5002666292e7316a004ccf205ce62d400199a40b9cc5a81421fe1973d4b500043ec3cc7a96a000a3e8498f52d40094dd0531ea5a80030f9967494b500062f32ce7296a000a3e84dd952d40014bd07bb2a5a80129ba0a6454b500043f43cc6a96a000a3e8498d52d40018bee731aa5a80129ba0a6354b500245e422eda16a00487d855da42d40010ff0cba885a80121f615768cb5002476412ed196a000c6d76d4a32d40030fd0bbb265a80222fa13764cb500045ec26ec996a000c5f53dd932d40010ff0cbaa65a80065e201754cb500043fc32ea196a046cce764c832d408da9cea99065a80230fa1474587500461ec28e8b0ea008cba801d161d4011973003a2c3a80030f94074587500061e280e8b0ea000cb7101d161d400196a203a2c3a80030f1d352587500061e3a2a4b0ea004c6c7254961d40c987cca3a2a3a80021fe19
  | 11 => 0x4840117d0fb22c6908022fa1c6458d210065b880e8b1a4200cb474dc563484011bf0eb18c6908021fe157018d2105c3e42ae031a423287c855db534840117f08bb6a6908222f21176d4d210045fc22ed29a42088bc845da53484651b906bb4a6908022fa1a7494d210045e432e929a42008bf87d92534840117b0fb24a6908222fe1c6494d210045ec38c929a4200e1f64d4e5348401c38c9a9ca6908032bd927294d2100656324e529a42028ec865ca534840195ec8b94a6908032b1917294d2100667b1ae529a4232ccc635ca534841117d09bb2a6908022f6137654d210045fc22eca9a42088bc845d953484011f700bb2a6908063e2017654d211943f43ecaa9a420b8de87d8d534840117f08bb0a6908222f2117614d21004d6c24e429a4200cac649c853484051d90cb90a6908032b1917214d211945e422eda1a4208cac649cb43484051d90cb9686908030f9d76490d210061ebaec921a4200c3e75192434840187aea32486908032bd927290d2100656324e521a42028ec865ca434840195ec8b9486908032b1917290d210045fc22eca1a42008f7815d9434846517d0fb2286908caa7a0f6450d210445e422ec21a4208cac649c843484051d90cb9086908232b1917210d210045fc3ec929242008bd87d92524841117f0e324a4908022f61c64949210064fb24e72924200c9c649ce524840193ec8b9ca4908032719173949210061fb24eb2124200c3f645d6424840187cea32484908030f5d464909210064fb24e72124200c9c649ce424840193ec8b9c849080327191739092104556424ed2124200c6e765d64248401c5cea32484908038b5d4649092133f53880c92124200e8c649ce4248401958c8b9c8490803339d97390921006a73aae72124200d4d755ce4248401d18c8b9c849080363d91739092122667322e72124244ccc645ce4248401b18c8b9c849080323191739092102667b0ae72124204dc7615ce4248401b8e20b9c8490802ab21943909210ee5a38ec8a12421dcac76dd1424840165d0bba28490802e3a0f74509210eed238ee8a12421dcac76d914248411958ec3228490802aba1b545092117e563b6a8a124208cac76151424840155d0d21a849092f2b1da43509210059742c86a1242009ae8710d4248411958ec21a8490822ab21942109211962e31aeb992421d8be869d332484331790cba664908762fe1f64cc9210045ec3ec99924200c3e75d93324840187aebb2664908222fe1c64cc9210045ec38c99924200c3e75193324840187aea3266490803175d763cc9210045fc3ec919242008bd87d92324840187cebb2464908030f5d7648c9210445fc38c919242008bd87192324840187cea32464908030f5d4648c921006373b2eb19242008ed87996324840155d0932c64908cab3a0e658c921004d6c3ce9
  | 12 => 0x912b3a10634cb2102762c08c69964200acd8018d32c840959d0da9a659091b93197534cb2102566430a69964246e4e6514d32c840959d0da1a6590913a3193434cb2102566430869964244e8e6410d32c84170fd0fbaac19082f1ba08755832105e36c10eab06420bc76811d560c84178eb023aac1908031e84075583210063c880eab064200c6c758c960c84018d8ea992c1908cb331cd32583210052ec18a1b2a4200a6d8214365484014eb02286ca9080317d95739952105e2e32ae732a4232ccd829ce654840196e203a2ca908021fe1d65195210054f41ccbb224200a9d83997644840187aea3aec89080327dce73d91210051f428e7b224200a3d851cf644843b55b0439ec8908028fa1770d91210051ec2ee1b22421dab6811c3644840156b02386c8908022fa1c50d91210045ec38a1b224200a9e83143644840153b06286c890802aba0850d912100556c10a1b22421dab681143644840156b02286c8908022fa1c30d91210045ec3861b224200a3e850c3644840147b0a186c890802aba0830d912100556c1061b22421dab6810c3644840156b02186c8908022fa1c20d91210051f42841b224200a3d85083644840153d06106c890802a760c20d91210ed5b40841b2242008bf87590644841193886b98c8908021fe15701912105c3e42ae03224200ab581900644840117b0f328c890802a7a0e65191210054ec1cca3224268aad82994644840117f0eb28c8908230fdd6751912100656b94ea3224200a3e859cc644840147b0b398c89090eab60a731912100656b94e63224208c9c735cc644843356d03380c890802ad60670191210051fc2ae03224200a3c855c0644840195ae4b80c890866ada0650191210055ac0ca032242088be87140644840117b0e280c890802a7a0c50191210054ec18a03224200aae82140644840155b04280c890866ada0450191210055ac08a03224219ab6818c0644840156b03180c8908222fa1c30191210045ec38603224200a3e850c0644840147b0a180c890802aba08301912100556c10603224219ab6810c0644840156b02180c890866ada0620191210055ac0c4032242088be87080644840147d0a100c8908028f61420191210054f418403224200a9d83080644843356d02100c8908028f61764d51210445e422ed2a24208cac649ca54484051d90cb94a8908022fe11765512105c5f43ec8aa242088bc845d85448411958c9390a8908027360e721512101476432e42a24208cac645c8544840117f08baec6908222f21175d8d210052ec2861b1a4200acd820c363484015ab02186c6908cb1718d7598d210061f3aec931a4200c3d75d92634840187cea324c6908030f5d46498d2121e56b90c931a4200c5d75d8e63484658dc653acc6908cb1b4ca7598d2119657194e931a4232cad329d263
  | 13 => 0x46f41eeca9282008dd83dd952504171dd0fb12a4a08022fe1176149410045f434e829282028bc865d0525040117b0f32e84a0802a7a0e65d094102557414cba1282008bd8718f425040955d0431e84a08030fd92759094102636312eb2128200c9f649ce4250409998c4b9c84a08031b5d7629094100666b9ec521282048be87995425040153d0732a84a0812aba0a65509413545f436e6a1282008be8718d42504098d8c4bac64a080a2f219748c94100636baec51928200cad74d8a32504d355d0da1464a082e1fa17764c9410043ec2eec99282008be869d132504051790cba264a080a6d205744c9411956741ec49928266aae86d093250401d18c7a1264a08022fe11760c9410045f434e819282028bc865d0325040199cec99064a0813331d9320c941006c73a2641928204c3f529d365c840987aa53a6cb9081317d4a73d97210262ea94e7b2e4200c3e7494365c84018bce7286cb908030f9d050d97210052ec18a1b2e4200c5e7314365c84014db04286cb908121f21574997210261fa14ebb264204c3d429d764c840187c833aec9908030f10675d93210264fa14e7b264204c9d429cf64c840193c8339ec9908032710673d93210245e422eb326420087f855c064c84170f90ab80c9908122fe1d64d53210051fc2ac9aa6420487f8759654c840147f08b2ca9908131b9c9659532119637194eb31e4232c6d329d663c84091b906bacc7908cb1720d7598f211962f982eb31e4232cae329d263c846595a653a4c7908123720d7498f211964e41ae931e4232c9f315d263c840193a62ba4c7908222fa137558f210045ec26eab1e420b87e85dd163c84010fb0bba2c7908021fe157018f2105c3e42ae031e423287c855db53c840147d09b2ea7908ca97a0f65d4f210052ec2cc7a9e42048df8758f53c84014bf0ab1ea7908131b9ca6594f210052fc1acb29e4204c6e7259653c840187ccb3a4a7908030f5967494f210047dc02eca9e42018f8805d953c84650fd0fb2aa7908028fa136554f211952f41ecaa9e420087e8719553c84010ff0eb28a7908ca2f21176d0f210051f42ec9a1e4232a9e83d9343c840153b0931e879081237e1d63d0f2102667392c7a1e4200c3e7599243c840995ce532487908030f9d56490f2102657392c921e42028ee82dd943c846517d0fb2287908028fa176450f211954f41ec8a1e42008be8719143c840117f0eb208790913339917390b2102666322e7216421dba48150e42c840955d0daa28590812aba1a4350b210059742c86a1642009ae8710d42c840195f0cba465908132b219748cb2100656ba4c91964200a6e85dd932c840155d09bb265908cab3a0e654cb2100477438ca99642029e4815d132c84011dd0f32265908cab3a0e644cb2100567438c69964204cce8718d32c848d59d0a31a6590
  | 14 => 0xc865d2325440117f0fb2464a88022f61f648c9510061f3aec9192a200c3d75d92325441117f0e32464a88022f61c648c9510061f3a8c9192a200c3d7519232544018daebb1464a88038b193528c9510445f426ec992a2008bd84dd932544050f90cbaa64a88425e201754c9510061f3a8c8992a200c3d75191325446559d07b1264a88031b5d4624c95100716326a4992a200e4c63d49325440117f08bb064a88222f211760c9510143e432ea192a200c3e75190325440187aea32064a8803339d9320c951026663b264192a200d4e754c83254401d1ec899064a8803a3191320c95117f1bb2ec9a8aa202974855c35154417ae0a0b86a2a88bf0f5d764d81510071d286c9b02a229c3d7519360544210fb0fa96c0a88021fe1d52d81510045f43ec8b02a2008be8719160544c387eea322c0a88032bd93725815100656326e4b02a200caf641c96054401958c8392c0a88031e5c250d97410051ec20a1b2e8200a6d8214365d048999ec4b9cc5a0813331897398b41226c7a12e73168204c3f429d662d040987a853acc5a08030f9067598b410061e20ceb3168232c9e849ce62d046593b0939cc5a081327d0a7398b410264ea14e73168200c9e419ce62d04019388339cc5a091333d097398b4102666212e73168204ccf215ce62d040199a42b9cc5a08222fa137558b410243e42aeda96826da3e84d9752d04090fd0fb2aa5a09b28fa136554b4102537416caa9682008bf865d052d049717f0cb9e85a08022f61e63d0b410051f42cc7a168204aae8298f42d040187cc93ac85a0803279927390b410051f42eeca168200a9e83dd942d040955d0532a85a08022fa1c6550b410045f43cc6a168200a3e8598d42d040955d0531a85a08123b209768cb4100656bb685196820b87e85dd932d04010fb0bbb265a080a2fa13764cb410045fc32e899682029b4815d132d040117f0cba065a0913339d9320cb41226c73a264196820b87e87dd560d041787d083aac1a082f0f610755834105e3b408eab06820bc75811d560d040187c823aac1a08030f10475583410063d080eab068200c79101d560d0401878eba12c1a08030f1d542583410265639284b068200a3d8414365504014db04286caa08029d60450d954100637b2ae532a820bc6c655ca655040995b09394caa08032b90672995410065620ce532a8256c3f75dd165504010ff0eb28caa09ae8fe11651954117e5bb22e3aa28254c3e76d52545045f17f08baec4a08029b61420d894100556c2041b128200acd8308362504015cb02106c4a08131b189759894102666312e73128200c6d75d8a625040199ae7b14c4a08023be1d621894133d57c22c4312820087f855c062504170f90ab80c4a08123b20976949410145e432e92928204ccc625ce525040195ae9b14a4a0803335cf629494119
  | 15 => 0x7390c8a88232b1c9721915114d5b40ce0322a200ab5819c064544c347f0ab80c8a88030f5d5701915114d5b40ca0322a200ab58194064544c347f0f280c8a88028f61e50191510051ec14a0322a26fe36819406454401c6b03280c8a89bf8dc4250191510445f438a0322a200aae82140645440155b04280c8a88a6ada0450191510061f438a0322a200a3d87140645440187b0e280c8a88038ba0850191510051ec10a0322a200e2d82140645440145b04280c8a89bb8da0450191510071ac08a0322a200e3a801406454401c74e0280c8a88038e5c050191513771b880a0322a26ee3a1014064544ddc7220280c8a88a6ada0620191510055ac0c40322a2088be87080645440117b0e100c8a88028fa1420191510051ec2840322a200a9e83080645440153b06100c8a88a6ada0420191510055ac0840322a208a3c849db545440187ce0326a8a88030f1c064d515135f1b880c9aa2a200c3c645cb545445f87cedaa4a8a88bf2d1c7645515117e1e3b6e8aa2a22fd3471dd1545445f878edb22a8a88230f1d864551510045fc22e7b12a2088bc845cf62544014db0a106c4a8802b360c20d895100572c0841b12a251c3d75192625440193ec939cc4a88032719273989510064fb22e7312a200c9c645ce6254409998c4b9cc4a8803335cf62989510045f43ec8b12a2008be8719162544011df0eb10c4a88021f61e50189510052ec18a0312a200a6d8214062544010fb0e326a4a88129ba0864d49510061ec38c9a92a200e2e821935254401c5b04326a4a88030f9c064d49510061e380c9a92a252e37101935254401878c8b9ea4a88021f61c63d49510062eb98c7a92a204a6e8218f525445f17d0d3a4a4a88a62f21974949510045ec3ec9292a2008bd87192525440193ec939ca4a88032719273949510064fb22e7292a200c9c645ce5254409998c4b9ca4a8803335cf629495117e1e3b6c8a92a200c3f741915254453878ec322a4a88030fa1c645495128e1ec38c8a92a200c3e701915254401878e0322a4a89478dc4064549510061e326e6a92a20087e8718d525449d4dd0db92a4a88038b193725495102537436c4a92a200e2c64d895254401c5ec8312a4a88038b190625495100537438c4a92a204c6e8718952544018dee6312a4a88029b600625495100637380c4a92a200c6c701895254411878c93ae84a880a1f21975d09510143e432eb212a200c3e75d92425440187aebb2484a88030f9d464909510061eba8c9212a200c9f649ce4254401938c939c84a880327d9173909510064e322e7212a20287c865d5425440955d05b2284a88030f9d464509510061e3b6a8a12a208c3c649d442544050f90cba884a88230f19175109510045fc22ed192a2088bc845da32544050f90cbac64a88131b189758c9510045f434e9192a2008b
  | 16 => 0x258432226663a264b086400e8c744c9610c801918e8992c219003b1e0532584322176240a64b086442ec7104c9610c80199a65b82c21900353dd53258032006a63aa64b00640b87e87dd5600c8178dd043aac01902f1b60875580320063d080eab006400c6c758c9600c8018d8ea992c0190cbb2cc1325803200667c3a64b006441ccc874c9600c801c9eea992c01911b331d53258032007263aa64b006400c4c754c9600c889998e8992c019003b2e01325803220f6440264b006441eca104c9600c80199a65b8ac0190028f61250993510063cb84a1326a200a3d8414264d44014db04284c9a882e8f61e64d53510461ec3cc9aa6a20bc3f74dd954d448d99ec4b9cc5a8813331897398b51236a7a92e7316a204c3f529d262d440987aa53a4c5a88132bc857498b510065690ae9316a232c5e859ce62d44658bb0b39cc5a881317d4a7398b510262ea94e7316a204ccc325ce62d448d99ea4b9cc5a8813331497398b5102666212e7316a204ccf215ce62d440199a42b9cc5a881333c817398b510061f3a4a1316a200c5e7394262d44010fb0e284c5a88030f9d05098b510052ec18a1316a200c5e7314262d44014db04284c5a88ca37a0f7458b510046ec1ee8b16a2088be84dcd62d440117b09b9ac5a88030f5d264d4b510043ec3cc7a96a200a3e8498f52d44018bae731ea5a88129ba0a63d4b510043f43cc8a96a200c3f7499152d44094dd05322a5a88021fa1e6354b510051f424c6a96a200c5f7398d52d44094dd0531aa5a88122f21176d0b5100556c24c5a16a200acd8398b42d44178dceab1685a882f0f9d66490b5105e1f3aac9216a200c9e649ce42d440193ac939c85a880a1fa177650b510061fbb6a8a16a2048ec825da32d44178bceb31c65a8803279d2638cb5100566c14c7196a20bc5e7558e32d440193ce8b1c65a88031b5db528cb510072731ea5196a20287e85dd932d441117d09bb265a88022f613764cb510062fa9eec996a211978805d532d440159f0c99065a8802b3619320cb51236673b264196a246d4e754c832d44010fd0fa92c1a88461f21d52583510049f438a1b22a200b2d82143645445f66d02286c8a88032bdca72d915117d1ec28e5b22a200a9e831cb645440153b06396c8a88be8f61770d915117d5b408e1b22a200ab5811c3645440117d0e286c8a8802aba0850d915100556c10a1b22a22fab681143645440117d0e106c8a88022f61c20d91510051f42841b22a200a3d85083645440153d06106c8a8802a760c20d915117d5b40841b22a200ab581083645440117f0eb20c8a88232b10972191510051ec24a0322a200a6d82140645440156b03200c8a88038e18250191510049ec38a0322a200b2d82140645445366d02280c8a88038e980501915128d1ec2ce4322a200a9e839c8645440153b0
  | 17 => 0x106400a6d8598b520c80155b09316841902e1fa17764c8320043ec2eec99064088be84dd9320c80117b09bb264190029ba17764c83200557426ec9906400c6e85dd9320c8018db0bbb264190032ba13764c83200656c26ec9906432cce53dd9320c86559d0732a64190cb9394e654c8321972629cca9906432ace83991320c865d1c8732264190cba310e644c8321972632ea69906400acf8654d320c80199eeca9a64190cb93195534c83219746326869906400acf8650d320c865d18c8a1a6419002d3a17764c832005a6c2eec9906400b8e84dd9320c80171b09bb264190033361b764c832006a742eec9906400d4d85dd9320c80999ecbbb2641900363a13764c832006c6c26ec9906404cce87dd9320c88d59d0bbb2641900393a17764c8320052742eec9906400e4d85dd9320c88959d09bb26419003a3a13764c83200547426ec9906400e8d84dd9320c80159b03bb26419002b3603764c83200667bb6ea9906400b8e84dd5320c80171b09baa6419002b361a754c83200567c32ea9906400ccf765d5320c80179700baa6419106f2201754c83202727b2cca9906400ace87995320c88d5990f32a6419012b3a16654c83200727bacca9906446e4c75995320c88959d0932a6419002b3606654c83200566c04ca9906400ccf76595320c809c98cab2a6419002b3a1c654c83202667438ca99064008ce87195320c88d59d0a32a641901393a14654c832237273a8ca9906400e4d75195320c88959d0832a6419002b3604654c83200566c00ca9906400e4e50195320c88dc98a032a6419002d3a17744c832005a6c2ee89906400acd869d1320c80159f0cba26419002f1e05744c832215e240ae89906404e8f64991320c80159d0f3226419112b321e644c8322356742cc89906404ace84991320c801d1ee93226419113a31d2644c83200566c0cc89906400acd80991320c809d18c8b226419002b3a1c644c83202667438c89906446ace85191320c88959d083226419013a3a10644c832227473a0c89906400e8d74191320c80159b023226419003a3904644c83222746208c89906400acd80191320c80959d0daa26419002b361b544c83200747326a89906404ace86951320c80159b0d2a2641900393996544c83200787aa4a89906400acf86551320c8095990caa2641900273a1c544c832004e6c38a89906444acf86151320c8095990c2a2641911b93994544c83222747320a89906400acf865c5320c80171f08b8a6419002e3211714c83200567c32e09906400b4f855c1320c8016990ab82641900363dd13258432006c63a264b0864088be87dd1610c81195d043a2c2190232b60874584320065b880e8b086400cac748c9610c801958e8992c2190cbb1cc5325843200667c3a64b086442ccc874c9610c88d998ea992c219003a3dd13
  | 18 => 0xc801a9ce9a98a4990025be1d5314932235a7c1aa629264009ac845c4524c86539906b88a49900353d4d7114932194e641ae02926400d4f535c0524c80147d0bb2684990ca3ba1875d0932194e7418eba126444acd83d93424c889d1e87b268499002cba1764d0932005c741ea9a126400aae86153424c80139d0d39e84990cb33a1a73d0932234e742ce7a1264009cd819cf424c80139b0139e84990027361f53d0932236a73aea7a126444b8e84d4f424c801e18a9a9e84990ca73e1c53d0932026a6194eb2126404d4c325d6424c80187ceb32484990030f9d564909320ed5a40ac92126400c9e649ce424c80193ac939c8499003279db43909320068f3ae872126400d2e75d0a424c801b1ce7a14849900a3d20576509320051f42ec8a1264008be87191424c8170fd0b3b084990021f61676109320045fc3ac82126419ab481590424c80193ceda1884990026be1d4210932004b742cec21264329ce839d4424c8011dd0c3a88499012b360f6410932005c6c1cc821264008ef87590424c80135f0eb208499002e3e0d641093221dd240ac821264049ce87d4c424c88da98eba98849911b539d45310932225c7420a62126432d8e73d0c424c889d1d0da188499113a361b4310932006c73b6862126444e8e76d0c424c801b1ceba188499113631d74310932004d7c3a862126444b8f8350c424c86539906b88849900363d0d7110932004b642ae021264329cc835c0424c801b1e86b808499013530ca758c932026a6192eb1926404d8c329d2324c809b1864ba464990135314a758c932026a6414eb1926404d4c429d6324c809a9e433ac649901353c82758c932026c6214e91926404d8c829d2324c809b18a53a4649901363c86748c932026c7904e91926400d4e75d8a324c801b1ce9b14649911b539d7528c932006c73a6a51926400d4e75d0a324c889b1ce9a14649901371c85718c932026e5902e119264008fb805d7614c8031f100baec2990021fe1570d853205c3e42ae1b0a6400cb4611d1614c8011ef02ba6c09900a3d20574d81320045fc22e3b0264088bc845c7604c8018f0c03aac0990130fd4a74d94320261ea94e9b286404c6e859cb650c8658dea7396ca190cb1b54e72d94320061f3a4a1b286400c7970943650c80187ce8286ca190029b60850d94320243e42ae932864008bf845c4650c81117908b88ca190130fd0a75d90320261ea14ebb206404cae849cb640c86595e87396c8190cb2b50e72d90320061f3ac83b206400c3e75107640c80155b0420ec8190122f21175990320043fc2ae0320640b87c855c0640c80917f0eb26a8190028fe1564d50320243fc3acb2a06400a3f84596540c8011df0cb90a81901317cca75988320262e994eb3106404c6c825d6620c80993e653a4c419013274ca749883202656412e93
  | 19 => 0x32b59171d0a3202716212caa146404aac82591428c8011df0eb2085190cb639cf4310a32004d7c3a86214640096c855c0428c8010ff0eb2e65190030f9d664cca320061ebacc999464008bf87593328c80187ceab2665190030f5d564cca32024e741ceb9946432d4e539d7328c865a9d073ae65190025be1e65cca3200636bb4cb994640096f87597328c8018daecb2e65190034b99674cca3200696b2ce999464009af87993328c80195aed32665190034b9d664cca32004d7c3ac99946400cad76593328c801a5ceab2665190038b59564cca32006a73aaa79946404ea721591618c8170fd0bb82c3190021f617705863202735902cab0464088be84dc5608c80117b09b8ac1190029761f53d95320062ec3ea7b2a6400e1e74d4f654c801c3ae9a9eca990032b9d172d953200656ba2e5b2a6400ccd735cb654c801c9ea6b96ca990030f9d250d95320052ec1ca1b2a6400c3e74143654c8014db04286ca990028fa1365995320051f426eab2a6400c7b751c1654c8018bea73b0ca990021fe1d65195320053c402ca32a64008bf845c4654c81117908b88ca990031b9d572d913200636baae5b226400ccd735cb644c80187ceb20ec8990030f9d441d913200556c1083b226400a3e85d92644c80147d0bba2c8990032ddd071591320045fc3ac83226400ab481590644c8010ff0ab80c89902e1f21570191320051fc2ac9aa2642fab481593544c80195ac9396a8990ca3b21972d5132194e641ae5aa26400a3f84596544c8594f100b2ca8990031b596729513219476432e52a264329cc835ca544c8010fb0b3b2a8990022f61276551320047bc0aecaa264028f4815d9544c8011f700bb2a8990063e201765513219477436e4aa264329ce83dc9544c8170fd0b3b0a8990222fa1276151321453c402ca2a26429ab481590544c80147d09b2ea49911ab360f65d493223727a9ecba926400b2e84d97524c80169d072a6a4990029ba1854d4932004e7434e7a926432cce869cf524c88939d0939ea4990027360673d4932004e6c04e7a926424a7880596524c80187ccb3a4a4990030f5967494932026c6194e92926404d8c325d2524c8018bccb39ca4990031759673949320062f3b6a72926400d1e74d4e524c801a5ce9a94a499003539cf529493200c7c402eca926400a3e84d95524c8010fd0e32aa49900317d9773549320445f424ec29264008bd849d8524c8010ff0eb28a4990829e20165149320062f3b6a6292640096f87548524c80135d093b0a49901333d8e761493202667b9cec2926404acd83d94524c88dc9ea7b28a499002d360e651493200477c3aca292640096f87594524c80169f06b28a499116da2016514932194e741ce82926432d4e73d4c524c88dc9d0da98a49911b9361b5314932006a73b6a62926446e4e76d4c524
  | 20 => 0x1f42862b246400a3d850c5648c80955d0418ac919002ab60831592320055d40062b246400ab9800c5648c80955d05382c919002ab60a70592320055b40ce0b246400ab5819c1648c80147f0ab82c9190028f215705923202556412e0b2464008be87141648c80117b0e282c919002a7a0c50592320054ec18a0b246404aae82141648c80155b04282c919002ada0450592320055ac08a0b2464008bd870c1648c80147d0a182c9190028f61430592320255741060b246400aad820c1648c80156d02182c919002ad60430592320051f42e20b246400a3d85c41648c80955d05882c919002ab60b10592320045f43c20b2464008bd87841648c80955d04082c919002ab60810592320262f994ea3246404c5d329d4648c80917f0eb26a9190028fe1564d523202657392c9aa4640bc6e655cb548c80195ac8b96a9190121fe1d65952320051fc22cb2a46404c6e72596548c81747f0daa4a9190028f61b54952320461fbb6a92a46400c3d76d52548c8018dacab94a9190232b991729523202476412ecaa4640487c87595548c8091790eb22a9190031b597725523200656b26e4aa464048ec825d8548c8178bccb398a919023279927315232004e6c14e62a464088df865cc548c8178bccab98a9190232799173152321952f41acba9c6404cae72593538c8178dccab96a7190032b59172d4e3202637394cb29c6400c3e659d2538c80187acb3a4a7190030f9957494e320061eb2ae929c64008bd87992538c80995ce5324a7190022fe1d6494e3202657392c929c6400a5d86d4e538c8018baeda9ca719003879935394e320070eb26a729c6400b4d82d4e538c8018dccab94a7190031b5957294e3200657322e529c6400cad645ca538c8018dacbb92a7190131b9c965d0e3200636b2ae5a1c6408cae645cb438c8010fb0f32c87190131b9ca6590e320043fc3acb21c6404c6e72596438c80187ceb32487190030f5d66490e3202657394c921c6400c3e75592438c80187aeab2487190031b9957290e3200636b2ae521c6400cae645ca438c80195ac8b9487190032b5937250e3202717292c9a946400c6d76997528c801c5acb326a5190032b5d964d4a3200716b2ac9a946400a6d86153528c80169d062a6a519002cba1253d4a3200636b2ae1a946404a6c82595528c809c58a4b22a5190023be1d6514a32024e6c34e62946432ccd869cc528c809a9ccb398a519013535967314a32196c7424e62946432d8d849cc528c809b1cc9398a519013635927314a32006a7284e62946400d4c509cc528c865a9ce7a98a5190025be1d5314a32196a739aa629464009ac845c4528c809c5c84b2e85190ca73a0c75d0a3200636bb2cba146400cad76993428c801c5ccab2685190038b59564d0a3200556c30a9a146400b8e83153428c80165d0b21e85190
  | 21 => 0x80105658c8010fb0e18acb190028fa1031596320051ec2062b2c6404a6e820c5658c8014db0418acb190029ea0031596320053cc0062b2c6404a6e829c1658c8014db05382cb190031b1ca705963202536412e0b2c6400a3e841c1658c80147b08382cb1900297a0c70596320052ec18e0b2c6404a6e821c1658c8014db04382cb190031b1c870596320053b408e0b2c6400a75811c1658c8094dd05202cb190029b60a40596320053b40c80b2c6400a7581901658c8094dd04202cb190029b60840596320253741460b2c6400a6d828c1658c8010fb0e182cb190028fa1030596320051ec2060b2c6404a6e820c1658c8014db04182cb190029da0430596320053ac0860b2c640087e87c41658c8010fb0f882cb190028fa1210596320051ec2420b2c6404a6e82841658c8014db05082cb190129ba08105963200536c1020b2c6404c9f329d0658c80993a653a0cb190122f21175992320043fc2ae1324640b87c855c2648c80156d03204c919002ad60640992320270f994cb3246404e1d32996648c809c5904b2cc91901387cc965992320270e992cb3246404e2f20596648c81187eeb3acc919002aea0251992320055cc04a332464088be870c6648c80147d0a18cc9190028f614319923202557410633246400aad820c6648c8015750018cc919002ae60031992320055b40ce13246400ab5819c2648c80147f0ab84c9190028f21570992320445f438a132464008bd87142648c80153d06284c919002a760c509923202557410a13246400aad82142648c80156d02284c919002ad60450992320445f438613246400a3e850c2648c80147b0a184c919012aba08309923200556c10613246400ab6810c2648c80156b02184c9190028fa1710992320051ec2e2132464088be87842648c80117b0f084c9190138b10965592320255741482b246400a3e85105648c80147b0a20ac919002a760c41592320255741082b246400aba80105648c8015730020ac919002ada0640592320055ac0c80b246404e2c72995648c809c3e6532ac919013874ca65592320271790ccab246404e2c52595648c809c5904b2ac9190138b1c9655923202716192cab246404e2f21595648c809c5e40b2ac9190030fdd6755923202557414eab246404aac825d5648c80156f02b9ac919002ad205735923200657b98e4b246400aad811c9648c80955d0538ac919002ab60a715923200656394e2b246404aac825c5648c80147d0a38ac9190028f61471592320054f418e2b246400a9d831c5648c80955d0438ac919002ab608715923200656390e2b246400aba801c5648c8015730038ac919012aba0a515923200556c14a2b246400aba80945648c8015730128ac919012aba08515923200556c10a2b246404aae828c5648c80155b0518ac9190022f61c3159232005
  | 22 => 0xb2aa6210028fa136554c421952f41ecaa98840087e8719553108010ff0eb28a6210022fe197414c420454ec3cc7a188432c9d8798f4310865c3d0b31e86210cb8761663d0c4219747414c7a188408c9f73dd9431080195d05bb286210caa7a0e6550c420045f438caa188400aaf865c9431080195eecb9286210130fd0a75988420261ea14eb3108400c3e75d0e621080187ceaa1cc4210022f61e63d08420051f42cc7a108400c9d7398f4210809d1c6531e8421003636117390842026c7322e72108400d8e415ce4210889b1882b9c8421003635cd439084202657296eca108404cae32dd9421080955d0532a84210138b94a65508420051f42cc6a108400c9f7398d421080195eeca9284210138b1955250842046572a6eca108408caf43dd9421080155f0caa284210032bdd9545084200557c3286a108400caf7650d4210801b1ee6a1a84210022fa1f43584420cc5e43a86b0884198be87d09611083356d03a12c221002b360e42584420475220c84b0884198bc87509611083356902a12c221013a9c85425844204753a0a84b08840b87e87dd5601081787d083aac02102f0f610755804205e37410eab00840bc6d821d560108018f4203aac0210030f1d743580420061e3aa86b008432c9c7350d6010801878eba12c0210030f1d5425804200c5ec26e2b008400c3c759056010801878ea20ac021002a760c415804200556c1082b00840487c855d2658c80117f08b8ccb190222f21171996320053d404a332c6400a7980946658c81787ee93a4cb190029ea0271996320053cc04e332c6400a3f845c6658c80147908b8ccb1902e1fa1c41996320043ec388332c6400a5e83106658c8014bb0620ccb190129ba08419963200536c108332c6400a7a80106658c8014f30020ccb1902e1fa1c31996320051f4206332c6400a3d840c6658c8094dd0418ccb190029b60831996320053d4006332c6400a79800c6658c8014ed03204cb190029d606409963205c3f4386132c6400a3e840c2658c80147b08184cb190129ba08309963200536c106132c6400a76810c2658c8014eb02184cb1902e1fa1f10996320043ec3e2132c6400a3e84842658c80147b09084cb190029ea0251596320053cc04a2b2c6404a6e82941658c80147d08282cb190028f61050596320052ec18a0b2c6404a6e82141658c8014ed02282cb190029d60450596320061fba4e8b2c6404a6e829d1658c8094d904ba2cb190029ee0173596320053c402e6b2c6400c6f731c9658c8014db00392cb190129ba0a715963200536c14e2b2c6400a7a809c5658c8014f30138acb190028fe1171596320051e422e2b2c6404a6c825c5658c8010fd0e20acb190021f61c41596320052f41882b2c6400a5d83105658c8094dd0420acb190029b60841596320053d40082b2c6400a79
  | 23 => 0xd0a420064f38cc7a148400c9c7198f4290801c5ccaa9685210031b5da65d0a4200636bb2cba148400ccd7698f429080199aecb1e85210039399563d0a4200726b2ac7a148400ccd635c74290801c6c82b2ac321013b1c8563586420ec5f43e86b0c841d8be87d09619083b56d03a12c32102e1fa1770586420043ec2ee0b0c8400a9d83105609080155b0420ac1210028f61250d95420051ec20a1b2a8400a5d8314365508014db04286caa10021fe1d65195420051ec3ecbaa28400c3d87d97545080117d0d39ea8a10026ba1a72d514202657434e5aa284009ad819cb545080195cc3396a8a10032b18672d51420045e432e3aa28400a3f8459654508010fd0e32aa8a10021fe1d65151420049fc3aa82a28408caf629d8545080187ced3a8a8a10030f9d765151420061f3b4ca2a28400b2d82994545080117f0eb28a8a10024fe1d651514200597c12ca2a284049ae829cc54508531790cb88a8a10a72d1857115142024d6412e02a28400aae82d53635080153d062a6c6a100237e1d6318d420043fc2ae031a840b87c855c0635080163d062a6a6a10034b15172d4d421952f41ecaa9a8400c3f65dd1535080935d05ba2a6a100333d8d7290d421966631ae521a8400c3e619d64350801878c33ac86a10122fa187590d42024d7410eb21a8400c3e75d8e4350801a5ceb39486a10034b5d67290d42004d7434e521a8404cae869ca435080135b0339486a10032b9867290d420065630ce521a8400d2e755ca43508011790cb8c86a1012cba0854d4942026c6212e72928400d2e74d4a525080187ecbba2a4a10025be1d52149420059742c87a128400e8f6390f4250811b4e82b8e84a10134b1097590942026c6212e72128400c3e619d64250801878c33ac84a10134bc8675909420064f30ce72128400c9c619ce4250809b1e4339c84a10030f9d763909420064f39ec72128400d2e75d8a4250801b1ce7b1484a10762f21971909420ee5a30ae32128404da7215c642508010ff0ab86c2a102e1f21570d854200c5e422e3b028404c3f529d3651080987aa53a6ca2101317d4a73d94420262ea94e7b288400c5e7394365108018f2e1286ca210029760c50d94420062f398a1b288400a6d8214365108090f90ab9cca21002a760c419944200556c108332884088bc845c4651081196882b88ca210cb0fd0e7598c421961ea1ceb3188432c6e329d663108658da653acc6210123720d7598c421962e41aeb3188432c5f305d6631080187ceb20cc621002a760e4198c420045ec38833188400c3e75106631080153b0620cc621002ab6084198c421943e42aeda988400a3e84d9753108654bd07b2ea6210029761663d4c420052fc2ac7a988408c3e7499653108098dce532ca6210230f9d16594c420052fc1acb2988404c6e7259653108650fd0f
  | 24 => 0xc8404e4c429956390809c9e4332ac721013931096558e420272790acab1c8400e1e655d1639080172902ba2c721003879964158e42004cec3882b1c8400a9d861056390801c3cca20ac721002e36084158e420054ec26eab1c8404ace82dd563908018beeb3aac721012b3a0a7558e420056bc0ae8b1c8400ad4815d1639080959d05aa2c721002b360b5458e420070faa4a8b1c8400acf82551639080959904aa2c721012b3a0a7158e4200566c14e2b1c8400a9f845c563908014bd0a38ac721002976147158e420054f420e2b1c8400a9d841c5639080959d0438ac721002b36087158e420056d400e2b1c8400ad9801c5639080959d0528ac721002b360a5158e420056d404a2b1c8400ad980945639080959d0428ac721002b36085158e420256741482b1c8400acd8290563908011bb0e20ac72100297a144158e420052ec2882b1c8404ace82105639080159b0420ac721002b6a004158e420056cc0082b1c8400a5f855c163908014b90ab82c721012b32097058e420052f428e0b1c8400a5d851c1639080153d08382c721002a76107058e4202567410e0b1c8400acd821c163908015ad02382c721002b56047058e420046f438a0b1c84008dd87141639080153d08282c721002a76105058e4202567410a0b1c8400acd8214163908015ad02282c721002b56045058e420256741480b1c8400acd8290163908015ad03202c721002b56064058e420052f42e20b1c8400a5d85c41639080959d05882c721002b360b1058e420054f42420b1c8400a9d84841639080959d04082c721002b36081058e420052fc2ac7a9c8404cce7258f53908178dccab96a7210033358d72d4e4202637394cb29c8400a5f8359653908098dce4b2ca7210030f9967494e420061eb2ce929c8432c9e639d2539080187ccaba4a7210030f5957494e421964f31ae929c8400c9e7458e539080193ae8b1ca721013339c96394e4205d2fc36a729c8400a5d86d4e53908658beeda9ca721003175db5394e420063732ae529c8400c6d655ca539086599cc6b94a7210033358d7294e4205e1f32ce829c8432c9e639d0539081787ccaba0a7210cb2798d7414e420061ebb4cba1c8400c3e719974390801878e332e87210030f5d965d0e421954f418cba1c8400e1e6598f4390801c3acb31e8721003279c663d0e420064e38cc7a1c8400c9d7658f4390801c3ccab1e87210030f99572d0e420064f31ae5a1c840087d8799643908098dce532c87210021fe1d6590e4202637392cb21c8400c6e655ca43908018dacab9487210cb3398d7290e4202727292c7a948404a6c825955290809c98a4b1aa521012aba0a65d0a4202717414cba148404e2e32997429080187ce332e85210030f1c665d0a420061f32ae7a148400c9d7398f429080955d0531e85210032761e63
  | 25 => 0x80147b0939acb2100317dce735964202537414e6b2c8404a6e829c565908014db0538acb210029ea0271596420053cc04e2b2c8400a3f845c565908010fb0e20acb2100297a0c41596420052ec1882b2c8404a6e8210565908014db0420acb210029ea0041596420053cc0082b2c840087e870c565908010fb0e18acb210028fa1031596420051ec2062b2c8404a6e820c565908014db0418acb210029ea0031596420053cc0062b2c8404a6c825c1659080147d08382cb210028f61070596420052f418e0b2c8400a5d831c165908094dd04382cb210029b60870596420053b408e0b2c8400a75811c165908094dd05202cb210029b60a40596420053b40c80b2c8400a758190165908010fd0e182cb210021f61c30596420051f42060b2c8400a3d840c165908094dd04182cb210029b60830596420053b40860b2c8400a75810c165908010fd0f882cb210021f61f10596420051f42420b2c8400a3d8484165908094dd04082cb210029b60810596421964ec24e632c8404c9f429cc659080993a85398cb21003279ce41196420065ab8c8232c8400a9d83104659080193ce6208cb21002ab608411964205e3732ae5aa48400b2d82d5254908018dacbb92a9210022f61e4198e420054ec1c8331c8400a9d83106639080155b0420cc7210021fe157098e4205c3e42ae131c8404e1f429966390809c3a8532cc72101387d096598e420270ea12cb31c8400e1e655d26390801c3acaba4c721003879964198e420070eb2c8331c8400e9661906639080133b0e20cc721002a76184198e420070f3288331c8400e1d65106639080171b0420cc7210cb17dd67598e420070faa4a931c8400a9f845c663908015b50128cc721002b66025198e420054ec3c8331c8400a9d8290663908651bd0e20cc72100297a144198e420052ec288331c8404ace82106639080159b0420cc721002b6a004198e420056cc008331c8400c9e87106639080153b0e20cc7210032761c4198e420070f4288331c8400e1d851066390801d1d0420cc721002a76084198e4200746c108331c8400a8d821066390801d2d0220cc721003a6a004198e420074cc008331c8400a5f855c263908014b90ab84c7210ca37a1c5098e420046ec38a131c8400a9e84142639080153b08284c721012b3a085098e4200566c10a131c8400ad68114263908015ab02284c721002b5a064098e420056ac0c8131c8400a5e85c4263908014bb0b884c721003a51071098e420054f4242131c8400a9d84842639080959d0518ac72100297a143158e420052ec2862b1c8400a9d840c5639080959d0418ac721002b6a003158e420056cc0062b1c8400a5e850c163908014bb0a182c721002a76103058e420256741060b1c8400ad6810c163908015ab02182c72101387d0a6558e420270ea14cab1
  | 26 => 0x31bdd95354852006a7b9aa6a90a408c3e851d1611481187b0a3a2c2290232ba08745845204656c10e8b08a400cb7101d16114801878e9a9ac2290030f1d153584521962e39aa6b08a400c3c74d496114801878e8a92c2290139908552584520143ec2ee0b08a400c3c749416114801878e8282c2290029760c505845200536c10a0b08a40087e87d4d60148410f90ea9ac0290821fa1f52580521053d406a4b00a400acd839496014817cd0a1292c0290821f21d52580521053c402a4b00a404e6b205496014817cd6a0a92c0290228fa1050597420052ec18a0b2e8400a6d8214165d08014eb02282cba10cb3360a7319742024d7414e7aa6842f8bf865c754d085f96cc2b8ea9a10022fe1d65153420045ec34e62a684049ae829cc54d081135b0d390a9a10132b61a7215342026c741ce42a68404d8d839c854d0801a5ca1390a9a10034b14272153420045fc32e22a6840087f855c263d08170f90ab84c7a10030fdd75458f420054f41ea8b1e8400a9e8315163d08014bb0a182c7a1022a7a103058f4200566c1060b1e8400ad5810c163d080163d062a6a7a1002cba0854d4f420464f3a2c729e8432cce635ca53d080199ac6b94a7a1002cba085454f420070e2a2c6a9e84048bc845d853d080135b09390a7a1012cba0854d4b42026c7212e72968404b2e8215152d08170fd0bb82c3a10021f61770587420053d404a332c8400a7980946659080153b0620ccb21002ab60841996420071b30c8332c8400a3d86106659080163b0620ccb21002cb60841996420051ec24e732c840bc5f739ce65908094dd0539ccb210029ea0271996420053cc04e332c8400a3f845c6659080147b0720ccb210028f60a419964205c3f4388332c8400a5e8310665908014bb0620ccb210129ba08419964200536c108332c8400a7a8010665908014f30020ccb210030fa1c41996420061ec388332c8400e1e83106659080147b0620ccb210038760c41996420050ec188332c8400e2e82106659080147b0420ccb210038b608419964200516c108332c8400e36811066590801c750020ccb210038e600419964205c3f4386332c840087d870c6659080147d0818ccb210028f6103199642025374106332c8400a6d820c665908014f50018ccb210029e60031996420053b40c8132c8400a758190265908170fd0e184cb210021f61c30996420051f4206132c8400a3d840c265908094dd04184cb210029b60830996420053b4086132c8400a75810c265908170fd0f884cb210021f61f10996420071a20e2132c8400a3e84842659080147b09084cb210029ea0251596420053cc04a2b2c8400a3d8414165908014bd06282cb210029760c505964202537410a0b2c8400a768114165908014eb02282cb210028f61841596420058ec1882b2c8400b2d821056590
  | 27 => 0xeb9cc7a94a404a6e8298f52948018bb0f31ea529003179c263d4a520062e384c7a94a400cad76993529480195aecb26a529003335da63d4a5200666bb2c7a94a400e8e6458f5294801d1ac8b1ea5290033358d70d4a520052ec18a0b0ca400a6d821416194801c74a0b22c12900396941635825202765902c6b04a42487e87d4d60948490fd0fa92c1290929ea0352582520445f426e2b04a4008bd84dc5609480147b0b20ec8a90028f61441d91520054ec1883b22a400aad82107645480117f0eb20c8a90028f61f64951520061ec3ec92a2a40087e869ce54548012dd0d394a8a90131ba1a7295152004b6c04e52a2a400c6e609ca54548018d8c1394a8a90021f21970951520049fc3aa82a2a40bc6f629d8545480187ced3a0a8a90030f9da641515200596c14c82a2a40093f87590545480165f04b20a8a90125ba0a7315152024b6412e22a2a451d34415c454548510f90cb80a8a90029ba0a54d8d520052f418a9b1aa4008df8758c635480117f08b88c6a90222f2117118d5200667b1ae529aa432ccc635ca535480187cc13a4a6a90030f1827494d520061f3a6c729aa400a5d87d8e53548018bb0fb1ca6a9003879d36394d520070eba6c729aa400d2e749ca5354801a5ae9394a6a900393d8e7294d52004b7434e529aa404c6e869ca53548012db01394a6a90031b9827294d5200636304e529aa400d2e745ca5354801c9ec6b94a6a90021f2197094d5200597424a7a92a400e4f6394f5254817ad6a0b86a4a90134b1497494952026a6292e7292a400c3e609d25254801878c13a4a4a90134bc8274949520062f304e7292a400c5c609ce5254809a9e4139ca4a90030f9d363949520062f39ec7292a400d2e74d8a5254801a9ce7b14a4a90921f21970949521263c302e1292a404d6b205c252548050f90ab86c2a90022fe1171d81520445e422e3b02a4048bc845ce64148014bb06284c8290029b60850990521961fa9ce9318a432c3d539d2631486595c653a4c6290cb2b4ca7498c520246e41ae9318a432c9f315d2631480187ce9284c6290029760e5098c520043ec38a1318a400c3e7414263148014bb06284c6290029b6085098c5205d2ec3cc7a98a432c5d8798f5314865c3d0931ea6290cb8761263d4c5219727414c7a98a446d4f535ca53148178bee7bb2a6290031ba0b7654c521952f41cc8a98a400a6f865c953148018deecb92a6290021f61e63d48520051f424c7a90a400c5d7398f5214809c9c6531ea429003536157394852026a732ae7290a400d4e505ce521488da98a0b9ca429003535cd539485202637216eca90a404c6e32dd95214809c5c85322a4290028fa1263548520062fb9cc6a90a404e4e3298d52148178dea9bb2a42902f1bd4f765485200537c32a8a90a400c6f7655152148014df0ca9aa42900
  | 28 => 0x71426394801c3d08284c729003876105098e5200727410a131ca400a5d821426394801c9b04284c729002936085098e520072b408a131ca400e55811426394801cb500284c729002b5a064098e520056ac0c8131ca400a5e85c4263948014bb0b884c729002a7a121098e520054ec242131ca400e585084263948014bb0a18ac729002a7a103158e520054ec2062b1ca404ace820c563948015b50018ac729002b66003158e520256741460b1ca400a5d850c1639480153d08182c729002a76103058e520256741060b1ca400ad6810c163948015ab02182c729002d62017558e520070ebacc8b1ca404e1f529916394809c3aa5322c729013a314a6458e5202747904c8b1ca404e8c525916394809d1e40b22c729003879925058e52004aec38a0b1ca400a5d861416394801c3cc8282c729002d36085058e520056dc02eab1ca400ad8805d563948014bb0bba2c729012b3a0b7458e5202567414e8b1ca400e1f54951639480959d052a2c729002b360a5458e5200567c12a8b1ca404acc82551639480153f08b8ac729002a72117158e5202566412e2b1ca400a5e851c563948014bb0a38ac729002a7a107158e520054ec20e2b1ca404ace821c5639480159b0438ac729002b6a007158e520056cc00e2b1ca404ace82945639480159b0528ac729002b6a025158e520056cc04a2b1ca4008de8710563948011bb0e20ac72900297a144158e520052ec2882b1ca404ace82105639480159b0420ac729002b6a004158e520056cc0082b1ca404ace829c1639480159b05382c72900297e157058e520052f428e0b1ca400a5d851c1639480153d08382c729002a76107058e5202567410e0b1ca400acd821c163948015ad02382c729002b56047058e5202567414a0b1ca400acd8294163948011bb0e282c729002a7a105058e520054ec20a0b1ca404ace82141639480159b04282c729002b5a045058e520056ac08a0b1ca404ace82901639480159b05202c729002b5a064058e520056ac0c80b1ca404ace82101639480159b04202c72900297a171058e520052ec2e20b1ca400a9e84841639480153b09082c729012b3a0a1058e5200566c1420b1ca404ace82041639480159b04082c7290030f5da64d4e520061f384c9a9ca400c3c70993539480187aecb26a7290038799263d4e520070eb24c7a9ca400c5e7098f53948018b8e131ea729003175d963d4e520070f322c7a9ca400c3e645cb53948018bcc6b96a7290022f61e6494e5202657394c929ca4008bf87592539480995ce4b24a7290029761b5394e520070f326a729ca400e1d64d4e539480195cc8b94a7290032b5917294e521966731ae529ca400d4f535ca53948094dd05326a5290138ba0a64d4a5202717194c9a94a400c3e709935294801878e1326a5290030f99173d4a520062
  | 29 => 0x84c929012aba08509925200556c10a1324a400ab681142649480156b02284c9290030fa1c50992520061ec38a1324a400e1e83142649480147b06284c9290038760c50992520050ec18a1324a400e2e82142649480147b04284c9290038b608509925200516c10a1324a400e36811426494801c6b02284c9290038ea0050992520445f43861324a4008bd870c2649480147d0a184c9290028f61430992520255741061324a400aad820c2649480156d02184c929002ad60430992520051f42e21324a400a3d85c42649481117d0f084c9290022f61e10992520071c28421324a400a3d85105649480153d0620ac929002a760c41592520255741082b24a400aba8010564948015730020ac929002ada0640592520055ac0c80b24a400a3d86141649480163b06282c929002cb60850592520051ec2ce6b24a404aae829cd649480955904b8ac9290028fa1471592520051ec28e2b24a400a9e831c5649480153b0638ac929012aba08715925200556c10e2b24a400aba801c564948015730038ac929012aba0a515925200556c14a2b24a400aba8094564948015730128ac9290022fa1c31592520045ec3862b24a400a3e850c5649480147b0a18ac929012aba08315925200556c1062b24a400aba800c564948015730018ac929012aba0a705925200556c14e0b24a400ab6819c1649480156b03382c9290028fe1570592520045ec38a0b24a400a9e83141649480153b06282c929012aba08505925200556c10a0b24a400ab681141649480156b02282c9290022fa1c30592520045ec3860b24a400a3e850c1649480147b0a182c929012aba08305925200556c1060b24a400ab6810c1649480156b02182c9290028fa1710592520051ec2e20b24a4008be87841649480117b0f082c929012aba08105925200556c1020b24a408cae645ca5494801a5ea8b94a9290032b59372552520045fc22e331ca4088bc845c663948010fb0f284c7290029760e5098e520052ec18a131ca400a6d821426394801c3aeb324c72901387d4a6498e520270ea94c931ca400e1d755926394809c3ea4b24c729013875496498e520070f324a131ca400e1d649426394801cb4c1284c7290025761c5098e520052ec30a131ca400e1e641426394801c3ac8284c729002d36085098e520070faa4a931ca400a9f845c6639480153908b8cc729002b6a025198e520056cc04a331ca4328de8710663948011bb0e20cc72900297a144198e520052ec288331ca404ace82106639480159b0420cc729002b6a004198e520056cc008331ca400a5f855c263948014bb0f284c7290029760a5098e521946f438a131ca400a9e84142639480153b08284c729012b3a085098e5200566c10a131ca400ad68114263948015ab02284c72900317a1c5098e520052ec38a131ca400c5d8
  | 30 => 0x80000050054014002000000c0000000058000000000004800c000006000000c000000000000000c001000801c00000f0008000000000002000000a0000000050000005004001c002001001000400c008000801401200400000000000020000024010008bd8790662d500153b0620cc5aa002ab6084198b5405d3742842b16a800aad8408562d500159b0610ac5aa002ba6002158b540051ec2882b06a800aad8210560d50112790ab86a92a0230fd8976d525405e1fb92edaa4a800c3d765cb54950010fb0f284c52a0029760c5098a5400536c10a1314a800a3d86d5162950014db0a102c52a022aba102058a5400566c1840b14a800ae5810816295011878e9aa2c32a0028f610505865400536c10a0b0ca804ccc625ce625500199ae7b14c4aa0023be1d62189540461fa16ecaa0a808c3f85dd954150178790bbb2a82a02f0fd4b765505422667b12e7310a804ccc625ce621508da9ea4b9cc42a11363d0973988541962f42ce7310a832c5d859ce621506593d0939cc42a0cb2761273988540262fa94e7310a804c5d529ce621500993e8539cc42a0132750a739885402476412e7310a804ccc325ce621508d99ea4b9cc42a01333149739885422667a12e7310a804ccc425ce621500999e42b9cc42a01333c8173988540064f39c83310a800aad82906621500117b0e20cc42a002a760c41988540064f39883310a800aad8210662150018bce7284c42a0029b60a50988540043ec38a1310a800a5d8314262150018bce6284c42a0029b60850988540471a20ea8b08a800cb441dc161150dfc6883282c22a0029b60850584543771a208a0b08a80be3850951601500155b0420ac02a02e8fa1441593520054ec1882b26a400aad8210564d48015730020ac9a90125ba0a73953521643fc32e12a6a42cc7a605c254d48010fb0d398a9a90125ba0a731535205cb6c34e42a6a404c6d869c854d4809a9d07390a9a90135360e72153520069720ce42a6a400d2c419c854d48a5a6882b88a9a90021fe1970153520045fc22e331ea4088bc845c663d480187ee92a2c7a900297a0e5458f520052f418a8b1ea40ba5e850c563d480153b0818ac7a9002b36083158f520056cc0062b1ea4088be84dc560d480117b09b8ac1a90029760c509925200536c10a1324a400ab681902649480156b03204c9290038e98250992520051ec30a1324a400b1d83142649480165b04284c9290028f616739925202557414e7324a400aba8094664948015730128cc9290222fa1c31992520045ec3863324a400a3e850c6649480147b0a18cc929012aba08319925200556c1063324a400aba800c664948015730018cc929002ada0670992520055ac0ce1324a400a3f855c2649480147b07284c9290028f60a50992520445f438a1324a400a9e83142649480153b062
  | 31 => 0x2804800600000280040040010048010002007003004400200000000000080000008020008002003805000000500000000060000008028006004000000c002000001002000000b000800000400200000180000050008000012000000001400e0000000010000002000001c004001004803000200b000000000c0000040008000001000000c014001001000000a000000000000c0020000000008000000000c000000001001c0040000020004006000008800000000100180100000000010010002002000800000200000100000020000020030000000000000000200300180080000010030000004003000802c00e00200180000040000018024000000000801401c001000801400000a00200000080020010008000000003800800c01300080040060000010014000010000001000c00d0048000000001001000000000100000040020000008000004000001000c00200400100000060000008000000000000001401200000b00000020000010004006002000002c00000300200180000170008000000002001800004c002000800800400500080240080040050000002000001805c000003001803c016002000801c0040000000004002006000801c0040020010038004000000000c004001004800000600000000080000000018024004001003000400200100280000000040008010006008000000400200300080000080030040008004000001001c0040030000000006000001800002a00f0138000006000002000400200600800000020000000004006002000003000000300000000000000008010000000001803800400200480000100020020004004000000002400e00000200600040000038024004000003800c0100000010040000004005000000c00700080180020000000000006009001800000e0020008008000000002800800000100b80100040010020010000002000801c004004003001c00000100280180040000000004004000002000c00a0040000000004002002001800c000005800000800100000000060010008000002001000001c0100000000028002000005001000000100c801000e003001800000000200000040100020000020014000000000800200600100100000000018000002016002800000400500000080060020020008004000000000c004002002801000800400600040020030010008004004000000c0000010000000000000004001c0000020000000010007000001800c00c000800400a0000008008002010002000800000000000000380030000000006006003800c00400b0000004000002002800400000b0000030000000001000000a00000300180000070000008000000003800400e001000800800600c000000400e002002803c006000005000001400d000804800e001000000400a003004000c01
  | 32 => 0x5001801000a0030018010002009002000c006000000001c00c002003808800a00c00400180000050018004000000000000000000000480500020030060000004008000000400200500000040020000008000002001002000802e00100480080000030000014004004000000800a000002000c0120030038004002003000000c00000c001002800000800500000020000000004008001003802c01000100480000000010090034000000000001001600600080040080020028014002000000000804000d0040004004002000000000000300000140000090010000000012000801c000001000000c0040000000000002000000001400800c0000000002001004801400a002002000c00200400280240020000070008012015004000c00a001008800000c0010000058002001000000000e000000001400000300100080060000038014002000000800000000900a001400000f000000001600100280040000000000038000000002000002800100700040060010000000004001001800400400900080040000000008008016000000003800000000080000000010000028008000002000000c003001000c000001000801000200b00100040020010000004002002001802800000000000080020000000028000000001002c0000000000000000004007000c0000000000020000003001800000600000000000000110090000006025000800000200e001001000e000000000800a0000008000000000007000400000600000000020010048000000005011802800000000100140000020018004004008000800400800100080040040000018000000000001000c00e008001000000200100780100180000008000002001003001001a0000000000002002000000c0000010010008000003001000400600e0000010002005000001c0060020018004004001003000c002004002800000200500180000000020018000024001003000400200400080000040020000010002003001000c00c0000068000002000000000800400f0020020000001000801c0000140018000000000001800400600800000000000030000004000003000001c00000500000000000020010004000000000800000000000380000000010000044018004000003401000800180000000000030000000013000802800000400080040000050000000004000003000000000100780340000000000024006001000800000000a0000030004005000000801000000000000020000000004002004001000000600000000040000000038004000004000800400e00000000080000020030008004000000000000200200000240000030000000000000001800400c0000030000004005000000801e0000000000000004000804001000000000100000020000000012000001000000401500
  | 33 => 0x1f80000000c0e000151a00000005450000000000063598b6829000038e98d74d00000259000000000000000d9c58d855c00000004e15d900000000000000083d80002e28000156800000004ba43601727b60b5a26d80b80000cf2204a00c1430000000047a0000be65a61f1600012f00000e0000016825ab000078b201812799a2378180a4e58730535094043300004de0594048d12d08a000038451ce8011a0800000005040bec72e884e14c8b244a81b508360ab8585006c63b19790001aa476080000001f2800000000000000287800000013b082d9c10000000046100002550a90000195e02883480001ede33b00004cf8f308560000000004607ce06a35005a800007926b20d2e000000073a800000000000000426510d504000094e000100c24c40006240000000000000000002a4d1744d10cc652a8e7a000124a68800003c8000080891126069e98223000000000000ee800000000000001ef00000000031800000010803c792b400000000000000000000067915c07cc000000014d727e1a4c00009ca3120e460001320000150e3dc967e5da80000c31c02000000009e85b00ca0af4272074e0640000000000000006f400010aa442800000000004f605c2000000010c0000000000000000003e0106c79013eb30a00007be88962ba810c2eb03ae6d913de37300007ed05cc000035200016715608b2c5d512c82191e5274980000460a027af95466638b0c00000000000000000000034598ba3430000256c00000000004a100004fa000033a925b6f700006960e5a0000592000078600000000000ca4024207a000000000019e626396aa6dc023c28f20105788fef000000000000003840de84a886927662144000000000600000040000000020000002000803402e0090000014000000000000c0120010020000000000000801000600000980280180070068010004003002801800000000000040000000000020002003000002400200a013800c0040080050034010003000002000000b0000020000000001800800000000000180020030020014008006000000c01e0040010000000002000800800c00100000000020000078014000000000000000200300480040000010050008004000000000000a00000180000000060040004008001000000c0020040010004000004003001800200100200080080070000008000001000800400000200080000040000000004000004000000c004000000800001200000500000180040030000002001000000000800100000140000060038004002001002800c00e0000028000004000001800c006001001801000a00b00000000040050000008002001004000800000600380040000020088004008001000003400e00700000040020050000010000002005001000800b000800000a00200180000
  | 34 => 0xa0fb8168b164fc1ef8657089804f08b0000083800019c630900000000740000004024800000001668000000000000002f880000000000483800051b08565f6800000013ba0000000702800000000005bb0b0867f000000011d87cd8000000000000006220000e08062400000016ae25789a8711000000008545e8800013ddf345e58f9e0f80a70000000000017f26db88204cb000000018002cb8000000069e00000000000246000000000013c13d882fc0000cf57ab0e7e560157c4cd098c79691f266d17e66b614b80228a0a1a600005de931601280000000fba12fdf7a144945c0cf82603ba918238f8b3c842199a000068951798820000492000122a48800001f800003e800002d28000000000000011bf78304566458e4854200002b09dae85b9aec02908b454e8a7275d5be055500000000000000000080e000047686963770274000181684d0000000000000000000001ff61e780000000000000073272c98cb72a800071a8d420170bf87420b5032d8c5a43706b437b17a814c0000127190a13585760001dcf0000ca0000000000010702d3800000000007528f2a56c16a600b000000000007ee8bf400002060000000000113c8029fe00000ef253889d277d00fa0618f02100820027389026ec9f0e0e9182a5c400000df00000db00001a712d4703932a000000005a86ec00000000000f6b2440000809916d0001db66ce9c7600000003a881f45e28fc80b6800000011a043e0d9600019147a315e0751800000000005ec19fa2f919460000000000189b299000056e00000000b9a00000001368000000000000003042710bbc6bf000000016026320000000102477a80000ba800049e80000001f8a804992814914a31df0000000081c81c00003ef00001e50000000011f18e000000000000000000000000073a1f3e0000000000018200005d400001fe4ff892612694c30000afe00000000001391000000000000000000de23718ac64cf20b07a6800000014a80000b6200010146f7800062f9ee647b80dc000000046019f2426000008a98660000000422800077640000001c5e794000000000001d08ac40411ce20000d56050000026b865233d00002209480000000055580000000ef807b1b807e9000000014320000bf22a0960a000205835d165d00000005a6800000000005bd400025f0000613838c4b3000000000005269d1a0000b52000194e30017e436988224b99c6e0c2109e1db17900001ba200000000000ae2000000002080000001484320125c306a0da000035c68a8000000000000000001fa80a600008dc00017f000016d800015b4000051a3629792000151e0000000557143c2889e5e82a92e8484024c66e17e20b71ff2000102e132156105b177851692442a6119073317b65aa00002218d1235e8dea51f001e3bd0bd1
  | 35 => 0xe0000000445914a52f8ed44d5d4121f10f1241200005318000324d2362021389240000076b00006f19b7c31799d0159104a5f5800021282527d100006ee80007a70000000165400011ae0000da87ec068a00004d2000192a2229a9436f92165d78e0c7201a63000000000000000000000105c0000589f7800005880ce84a605d068c6998000581911c00000000000000775542825f800049edcae00019860000000000000000000000000000000130c00000ca1db8b341fe06e561107b85fd109073fa0ac0f00000824925a0000000000000071811480000e7d18d1b4c00004a8000000000008ec2d08d5e0b79a30213000069090e60001f1a0000000290112b17b1be281d00006c28c341f40000000129a0001cb60000100000000004a96d04799d47519142100018bc4c0179800013d400001f600012866f415520ba20c281909f0740096e3d414174e8c00075c1ed4000209e5d40000215cbf64590000000000000000000001fca853193660c000070e00000000000000089c750000058c00005ff90564e11a6e854851e677a14a1b910be31a8e6e2c7d64e4b804a00aa902280201103839a866ff006e0130ba25d4898a0000000778c4b200000000000000000000032e97a437955f85f1800000000740d3800048fa15a005000000012c00000f8c24a4b7c6529b620000a9e000000058100000688000033800076c80004d4c3a26ba971c6b10096695084200000003a70000000000000007020000000000105a3fb4e58411215c7719fce1c303aa34d0a1a6271fa832f205c20f12e20b5800046f943b650924074600003c01d880000a8c85bdf7e0001a627a89a2c362000084480004d212a6000000059e80001f9015022f800014f02532ca0000000000000004f4000000000014f3000000005b40000000000505898454b80001e9000000000001d3046301c84700779a9a74d84425131f5c5c5913200019207a1819a40780f6000000044d96e40001302000111471a1ea66568e4c470000000b800012f0dba3238ef0000000038b800020c9d1c7369e0e00000000001f9202b0eda00000000c980000000000000143503c0000000013823480001a807ec725945606d17d80f98bfe036801c00013a64c7110c566e0e6207800023e0ccf51d16215be800000006aa4ad9da226dd0b800000003639d0e0ab1bd80000d083c4177c6334fe00000ee800009620f3000000000000001c1600008a468e89da63c935028e0000000158e23f0c250000c9e341844500000001f2c0000000000000177e00001d05760b4c1ab8b3625400000000f463d80e0b00003560000f7a4cc00006c380000001d860000000000000000000bc7121252684000001c000003b93f41ff400051658122ff5e8e82f951056a21641a5c0ba7c2166440380007709f461028398665
  | 36 => 0xd09c63e5864674b0000000155e00016dc63980003ef80000231d8c000081a51801c58090000000000000000006781d2406f00005599c1200000003a100005738000000079c6d5149e000103e00014ba0000582855c0003c180001ec8b8e000066447080000000000000117619c8ede0001760426895266b031003b216d2ce0fec22a96201434cc4415040e2c6007a1f4800021a81641d181e0724000026ac00029e00004eb0000000107a00000000000000343800062104f50f58b686f5199e13083dc0001bf40c90000183800000000005a10a8e000043a0001f800000000315952c59700000000c9f42d1a8844bc000000000034f198d6f013940ea1f0c561120200000002edc00000000000c3c0004ba800074f800000016ef000000033b8a3000013ed0000534791800066f800011f060c0000000084800049f800050993835bf9a7e00000000000000000000030816c828d00006b98000558800000009a400000007f70821000000000000000a70000000000048120f023d1a24000000078092e453605c6002c51851f94986da93fa405952600000007a099324f485520001b88000141c01993c30000efe64b01160001d84000000076a8c6c0001a4e00017dc00000005a280000001b201da91403d70000000113809a1bbe00017065d00bdc44687163a5047e5ba8658270925300f033837400007869baa00011442ee8b4084d9bb615d20e438a00004b181dc81786ea000147a00018180001aa247a039a0001dc45379c7e0001fd2441800024500003c681c60cc80000000028000000075c986500000000b200002a217f8000041480c00001ee80006288000000000035880000000000179975a00011e060c800054280000000b900001e7600007c602c9c5285a000042a193430b86d683c86bd5f488ea56b09ec00000000001c2430993b900000004979b2241a1a727578fe44aa08162c706a24bf8cac12b890413c800025a98103680c990000b76596c17682a0f6600005e82f51c62000000000012d8081217200000007d0040c294917074ca06e6e121200000bd226e98d500011d4410966e000170046699b673c0b102658c320601ed6382616c770000052587b024306ac65f00007551d641e0963479c9b961130b540649c9e000066e0c5000000020c60000000000217100000000000000000000000c135a56f11024140468388c0000000a124550000000000013d9ef40000f36000179a0001ad4666c00019c52dc2881d0600005563badb3857c957a00000007b2800015e800002fa104000000031a00000000000824000082500002309fc2322000000017180000000568c00031b8ff001d80002ab98ca0728efa6cf9b1e000059a34c80001e75ff8601874452800003ea400044915e81124a5e3e40ab46ba00005c380006da0ad10001bc
  | 37 => 0x75a9ece000000000014cc00021740001d5a2ab0b7e6c404220000000000189600000000000000787096c0000c6000002760001edc85f0b5e1dd06da2f000005ad000012d01fa0001de20000fda6b58000000000018c839c4098000368800000000001af00000000e130000a2e0be800000016ba0001dee6168a5400006006408ea441f92c43810000000000000011f64db0000000124e0001a00000000000000002330000280000005321545a78b120001ec4075000008397a618480000001e5600019c80001ae00000000000176e00013a955b800000000001770c4a000088461c000000014fe0000d6438a87a12f420d46a8138c5b28000000140e09880003da15863cf0208000147f000144a000112c6400eaa0000ac881b136253b000051895d439c01b0102000017b83f64b580000000000486000000000005af80000001a5e0000a4418b80006f914a20000acc4dd148b0001e1873806f621e00000000000000000060b000037e1439000000078b87d40000c9800017aa84a000055f8fd6000000032e1aa65ac005400d9ddb6be87d642f085c26800004f3000000000004631aac52d4eb435715e555a862a748861e4da878e2d1000059ec31c0d289d80000000000000000000000000ab07b815360001a5726e0000000000000000001314b78360800060e94d0027889e631000085e832e0108c14511c00000012903a300000001bea09f8e827eb1610672a01e00000004e60fa875fc00055d986a00000000000000710800055c0610000000000001f168e20545309122000166a21c822e00019384ae01d673440000001419000000011603c4000000000005b21afc90657b9c346cd1326577000073f000027f17c24a2018e1ed073609700007ab8000000000000000006ab9e64000165800007f40000000000000000000007b18e9800000006f4800000000000000798155163b00000000000000000000000003202bb8000571000017a80000000000000000000000003700000314000014a800e75f0000000076468504d07771d683ed000077e8000000000000000004c880000d5000000000002a5800000000003040000000094675980006ae000085383b449d1b5823500003a3800023c901f00016c2000054050c000000000000000000000000000000000001cd377dc7dc5630fa65d1179c7e61cac4e18248139164c1fd89bc38d00003e195a132699ba03606442e503be3d0940600000000001b2406900000000000000000000017864219d202f208e4000000047899500001e385d611260001a78687800078f0b607ca8a6a49a07ac48d05365981eb428386dc5cc1e7e40280d659400d000000002870000487000000016e23b7163a6ec000000013c5000165a000000000006ce53a10f20001bac0001f1431916e820c0000000000025
  | 38 => 0xd595c6054916272680002458000713086200000007f180006e6157400005722140ad2000000000013464d955241fc1a6c46a1b1a00313be13a9c187208302408000017c8bce2ea00001600000228988c00000007e5204a62d17c00001d803a588fd1d688b8509cfae1bf9c9827b8000375800004b80007738008579000000000001169be8557c0000000d5a00000000000000000000023b8000261800028a918900000000001fb20000000850906e00002fe000151669a85ce82282cc6bd0ebe0829a7c20920b480686753389bec0000fee80505500e008fe0a983e869499980001e4c00001440000000000000027d15a0589065c000000000019dc5e20bc214f92727df0cb22a9a0722c80000000800008b0000048043e5561e5c0000000000000000015683dd8000089123a0000f4c000000000000000000000381800011800000001834000165250f800050886c0000000049650a6000000000000000000000000000000001e800000001b280000000b750000f920000000000000000000000001b262398296739800061185fe4068aaa0afa03c4b3944b00003781f620065ff0f823a4000062e4000000000073e8000000000000000001511a800d118d40670b1500021650001ac65b69a6400000005bc191e3e3951c0610e36690174645a02504509d785239bbc5219e240599b0c84900000d791aa26782df33f804474e84320000b5c2f0492e5249e922508c2229a024025c194c6dd9bf2838800037e9d3001815ec71f00003a816a200000003b200000000fc22b615ca5649ba048e0b587cb03f22b380e88404fdc10d000000018ee39d000000000006e29d0a57f1c0421d0bea34f8000000197b3e700004b400000001e162320f6a4b6811a00016bc45b100220520621de05d86b4168e1bc08e8552000066045282840ae452b0000000000000000004248be8580c0004850b860000000694000000000006ed191c000045c37d8584593e048000167c00014202a29d7a000000073196e03af00004eac00039098720dc91500788a7f00018e43c5400075d9794000000000000000000cb70000caa0001d605e397727d880004f180000b0117230640a03fadb52620000052c80000000000000000000001243c9a08c382a15000000000000000831000000000005b1036863c4000000091e00000006c020464ec40000000ccc00000000000000000000000013ee34d996200002566698682000066b5a70e8a2ec139c7ac052c00019f0818109633ac000057000008400000000000000012f5221af00c280000000000000000032c000039f00002941f5400008663631eec7c9842c08d9b18567535561a1d340000a662dd04843ec9ec23c85c403988e680000f0e7e702bc3c89abe0000000400062881f98dc607800060d8c0c2c94eb87fd0b223dcc0
  | 39 => 0x61664140006250a8002d8000000161a0000000000000000017c970a00000000fd00000000101129e00000006738000000000000000000000000000007522f154137d20167da800061d000024f8734000146d000000018b14243cf8ff8260567400009cc7e10ec65484000000023e0001ed25ec8c587ad8000819800005c1d560001e66000078027d80003f60222000147d00007280000000000000048c0a2600000000001e6a000109415b800015196a43b90626000000055397b80000cf60001e7c84980000000e180001fe4402000009680000e381e423394fa000005a14860a600015775fb80f80001599176800043c082a52fca920379f4a000021e00000000738a32000000000000004fe0ab60000d60125882e7150000548103600119b20000f14686986c000141a4bc8b6a659e1700979dfc147048c57e87a252bd1520a511c46a1003869c419856280006db029e00000004420c1c597c74a4ac80f2000210e722000077986a80001c9c000000000000000000fea0000ae623592ee0000c4e00008342a7d74c000112a05fc00000019c259c9da6669099a000059e0000642000000017001f800000006a30c8a7c49f9e10913e0220086e02b9e9423fc0004f8c00000008c072100001c789fe610033c23b492c6fb80005c29cbc4998000000050e00020ba000000031f0000731000037f800000000000000e12000000000000000000c7200015220001d9622b00000000000000180e4fc800028e800030e1ca23f3847823c00000001c26000000000006840f38aa01f3400000017fa04386c63858e604800a581128936079800009385e2451965e0000d924359d6c3380ec41f9800046c93326b2875600002c40000000325800018f80002f581602328f74461c0007d0856c000000000000007eb84280000000000000067d9e4e3cb0000000000051602f753a8526242d0521c6009827c8068000000023683e70000c90000000000000007d91b56307972604c800000000000001fa2000000000013b400017845c50a620001444000020c643871a7d30af6745865063a480e00020d00001bda00000004e28dbc75e44f83e50ea35148944000000000018e80000606067543a1528b96736538f0b500004ce800015398a07281a6048480000000d460000000000000000000000001dec014800000011475650de63f290da03080fc2c68000550800000000003ac80000000000000000000000001861b5e65f800000003583058844000000000014230000e1475d05a219f979e00c80002e0800051411cc3b0113024280002ef8a4800004860000d5800000001378e7625585f00dd000009c84e632b8000000000051b9d3800000002599d0c6299da027800000000000000000024d0b8831f9b7e000015a17e800000009787d61d1231d8ecc0001fe22
  | 40 => 0x7a0030d00000003460f9a19d050871607614c21d927bf96cc00000002a680000000c40000095c739071c6f309d067a000047f8802000000068c97ae000000029f15f90000eec00000000000000000000038999f44f2829a00002c209983f40000000000144f000031218d80004ca088e1cb16f87ef00000000213000000000000000000000000061415c041e149e0e000000000000502463800000000004e4000000007a800000000ee00000000c5278182c61a0c57814b800000000000000000199800071c00c004e8000000000065c00000001f9a000215629b83902ea8c444d90ffc7ef9be61d814cd0d00b0e51212ba4539d4c09a9e202b70000000000000012ec0bd91de000154c6e48000352800053d10a06d010c066001023cc80c863397cc53646d001792c20bb01ea000000000012264df18d281080000000afa00012560000ff60ae10d200001c31ce93c4000000063d8000000000016b87c24049c0c00009b05f29bfe00000000028ff4615866a00019184f4213030a982e7e3082c76c00008525a26000141840a932e00005963f120ea58b201c00003cd0000000000000068a1e300000aec776917c1c892ae00000004e08000000000000013da5c100000001e440001780000028e0001b280001dbc7ae9f207f307c0754800085a8000715800000000006f10452700000066ba0dc6cb1820745000000000005d09ca64481d714de9a7a00d1e420000000000200e4461da843502ae00020280001c2240e9006000000018f00004f2400012280000001bca0001d5c1bb94b449411b6285137e0001f4801408282a19ada1450faa7aa1ba4348a0cc4921f107dd01420000000000000018c00004fd9a4400000000f880004661356000047200482ca0ad0e9a00017de0fa87041c0072a3b889e23480a2800002410001ee200002f40000000000068806b807c0002116000000000000000000000000048e096077a00010ac000000000000000001a5c72300000001abc000098016700000000748000174e6c21850000053a756000007f1f0a82f193e0e79fe60000000000000073c8d8048ce1663ad8daa2ff078c7d49c86298142e31182e653eceba7538ce635e00006ca9724472104e00000004ee1a8200005b400000005eb017a23c58e210b80000000c2c4a0da48085120a60521484fa86e01e210ec0df87e80e1068e0001470775000000000006cf1a0254c1bc200014c883b00000000000000000051088eb5368f6e42d82a4101929842700000000000627d06a0d8801a3888000000000000000000000000000086127852ca0000000000000010013380001c7200014810000000566844e00004be2f18b040000000000070612e000084e80001748f986d0800054fc0002120000000107c58013590a40b3073b13c83410fe218094e10001
  | 41 => 0xc0002b5000003800005199f9635386a40001adc00000007c195e900000000908000074891c238171e00000004a700006760cd427900000000aa40000bda266154400000000000000000000000009d40001cb462e07aa1e593420001bf882ba09c69c02d013bc420376212c00007b60000000000000000019917af18db52d9b5a7051e7a0000015665000030d80004d514d625604a2306000000011ea0a192f473500000b94000000000006a119d54c95197da1ac083f93e900020d602a10043b3800070181484d7c00049880000000c9200016a01c91c504fb198276e8a04000159000018f825818aa00000003df01464b486fa8329e6e1bc892485d446a0a01b8e6945cd87068af0407457c53912f876e0f5611b9a560000bb42ee1280396400000000007a594ce545d010663105820e8cc2574889a567dd442918bb61ae800000000004f88000000000038b14ca1c2d3870000f6777e0a5c32d13c0000162a4dd8f2e6a4195274789940d188920710cf065a000000000002d192926268804637db8626d14723301f8804b000000000000000f4a853c00013600003900000000000071d1a5a19a00000000000000159c54f80007690000000000000018da37500003ca030700007fc00008b2120113d1c51c2c197a0ee0000000353000000010c40000000431800000000000000000618126000018920b0419e7ed86403eb1e485cc948536b800077cdfd06bf9540795000040f117e000011c000086c531000015d44e80001490860130400011ba0000000000000012607e23f31f8e429000085e0d1a2db189d0000000475800068f031d724878a132800068d14a612a800000013af1a500002c98ff282807a01ce000000000001cb8e6c0000710000000000000000fe92aa7e801ac7f2032700006765fa92de000177600002ee0000000389da9605b8f8817280003b0832a0561cbe0498000491800052b97667fa15370ffa08e7db809c77309e63171d9a732028803917622028d386bd96d6244a13e2168c4270e80000001e602000c040d68ab23c2dc8a53705c40001924000000016f8000000000000000006831fd66340f5a1a005f481313aa3dc491a015908400019ee57edb9a33e09920ec959671b0b064f596fc2f100001f240000000000000000000000000001f82000000016f000070d88ef00000002e31c300001e1700014c72340000000000000000000000000702064e732c00000021321119e7462a00000001cc2000000056893c21ff8000570800006504d71178000000000004d00005000000000000000000000000e35299552a00000000000ce820d800049300000001128438817c507996c22b8000681843800000001f68dac18ac000000051009b8000000000003d1af2000092200000000000000779008500000004f1c0000001e70
  | 42 => 0x248b06de34003960000000540175c00000001eb9b7405fa0320000e240a8800000000000c1817d83d018c11107cc495000080b878408550603c100002b34ade0001e586d800c44d3058e5fec1cc78c80001ba185c78e80000c0d90c0e2000042fd2940b4800000000000001fea000050a7f6138d6c499aa6a294992fe8000000000003f80000000dfc0001b4845a9074336862472e0d3a84b84667f11e140cd1cf800000004c1800026c8000000106640e00000000faf00018c01c980000001c3200000000be13580000000000025400000005a4000000000000000d2a53f000045300000000000000213c000076204189ea24c212a5cd8aa247d10ce000000012c000012500005b98dc80b912228379de876d0cd000014f24d296f281f21606e5000069d093a0000aba00015ba01618084d8063a0aa0d1c40840004e680006b8808800003a9055a0b26b913ad0001878552934e000000000006160000e5466f0f186788aca821988e30190ea27a17120000000000000000018ea000000047e055867697be39287f253d4fb00000154000038a000110410d96d269d9fc000006d45b1918a0191f220000018000000000003f83b98000000000077495345f4211e000066c0001fd410ce0561dda09a0000d440000000000000036c00004960000000000000011ec00009905ed00004a900000000e7200000000001d9e2d98000000000000000000398cbf00000000000e3c0000000000211c000000063d00003868000000000063f00001cf00000000000000000000000001870000186800000008b900004a4391043c000000004509a274a00005db00004164ba030e8c0280b000061896b8090d66c3d01a9200003bc772124213b9bc8000184a60720a2000084627780001040cdc00000006680000483000049900003678c1100007fa84182924648000000000056f8000000048785884fa00000006e08000000040947721007ea81b6086127c50d07505cd0b0a3b5996e50b0bf07340abe25e984800000000001b78000090e0001ee80ec0000641800025c4840457821a3959ab432f535e0eb1e260001fde7a8122e1790cd204a0000423000000000003f00fa223d8e6484506b209e0bae00000000000000000150657a8000042963852518d878297a000000000000f3a000000020f80000000000000000000000005150000000113b0000968430800014180006d18ba407c97e82e4862058dd1f0195030e53c000006e80000000000000093c0001eea2700000000079b000000051aa0c82b680003f9912e64e80000000000000000003898887c617d40001c785ad9f7667b00005c800001f280265224316000208276f84fc6b480006ad9d6e0000000583036a1319e120000000000123c716800066291d03fe800000000000000894000000037393fc0b4
  | 43 => 0xc122800000000001a121c4800000012ac000000000000223d51d8e2ca832216e12b05e09c5c0000000000000035c127d00020c0851879000000004c600000000000000000002180000001df04e20000000000060900003a18e303df80000000f64000066015800000000e0234c000000811c62161a65026800034b0c0a4e2c5b6590852043f40000001d0920400000000000000000053800000001eb806996120000e20523079f7a104ec000170800002b343800004688000000193c0000db80001738000198408e0000000000000006040b382b500000000000516000000085f80005100eae361087c0000000000000050100000000000236073e000010830f99440000d2800018860c00982274ddd019e13ce7820000000000000000003f798c63fa000024fc000000000084311ca72c108265d946100019605c090ee2931ef649d80003c31bfa024800000000003520000000023a000000000000d40628cc800019641758eac71380002ba00006ac9d4b64200000000000000185206e1ca4218162808c203a00020ce6dc8cd64d491560cc000045e1468407093200016927fe8000000000009c1e4a41020fc577800000000000bc02eb000113e292864800015f612d8dee7794000000164040c88de2d200000040bca4da0dd200000000001a1c6cc88706ea00cc00000000001d100b84000000000000000000000000000161e0000000000000000021402f31cca0001ffe12b000005a00000000b6e00019c44e480000000ef660f800016286cc0001d42000120633380007780dda3fc44fe1741efc0002000000000000018c20000000520992600000000000000321000041900000000000000000046d00000000000394156c00020d2304826c61e8000000000065e14f600006b81c386e200000003f480000001ef265000005ee8000000000044395da36694a4000140a120800010bc3c85540e9242c000056cdb8c1b98c541b600002be000001388c600020780001cee0000000000000000013e43e90e8870f80003d20aa80fb80000001f660000000569a096000067a0000a3b0000a7a62b103046197ce65e98b25a2000078016620001a16586000039e14494c691ac43f000062b8ba64e8211a0000000465191a000000000007ce27b4b3a65212787fb9fec397000000000000f0800019698fa01c48837d597e000014156c199ea0db87ee6089cdc6888a7e2bf000073d841837902e3172000070b96485918000000000078a81a00000cde692928e33613dc6fd841a2af00241d490f67b41768281820277d80000001c4a209928a46f20204c38e381af8000342800056d81d80000ea82018000000000000007bc000172a13c00000000d5000006a643d1d9c613000057400006e99d02182000000000003b49f5a7ff16de7a413b22d9079a0ae8d7
  | 44 => 0x1758a44329ec00000000788800000010c83ce053800019a800000000000000000000030f00000001b9e5581d6241711ed349000007c176400000003e10b9e0000000000000049b80000000888439085e00016261619a040000d546c1172c1df867034980002e119c083e033681493bc000000000014e628d86df6b30a8484400002e0209841c82e9164056a10482207ce8a1816b0000000018828f9e1e37090d000019bf4254b145f200004061f1e691862d655964d47e96ce37c800038701be1a409dc63c1e34610800050a9e3e000000058703f000000006a7021c78a00000000ed000000000000000271400029d800000000005348fb680a99d659e06c20000d680001c2a5cb800017f164a4e880000c6a1760000a421c800003ac0ae00000000617813e0afdfa62968598544980c13803ec619000011d83760001a8e6cb832c000115c0d1c00000000000000000000000008d00000001cc00000ca64379eee000024a73393e6660c0000000d6c4621dd65678a6c7c115645568d5242e85ba1f21ac26d29553581550231e125500000002cc935c0001eaa00a800060e00000001165000140c65601787c0000000000000000c08311c51357f9aaa0448d862530078000000024a000060102b0000000000000004890000000000084e12bc00002443a00000000000061515c86cd8bee03480001ac0f341778efc6860f8a0000d9869ae04474f000036d9e9e5c6800000014ee667076600003b67c0831e000077205393a828300000000c30163189e0001f24070803a000000024616ee00000000001eb200000000001282000038236d08a87dc80000b8000000017c40000dca4a580000001cde00596d4000000000001b21da04e2047800040b087a000000058c982667f8000000000041d9d8a61b844000000002858e9e6c706d20000e5265a800052700007a200002de997400014c580f89722f8126c00015e680d80007db000001a800032700002c7800000000003978000000000050d800000000000000e1e19300005b00342000000064100000000000371000000000000000000318903465c9d2e228000000000000000000444000035d9d940210cca0de8000548d61b000006200000000000000065800060f0000000000042c91588429d042e700002421ade30140000000000000102832bd97537c00001301a0e6a600000001aba00000007e185663db0b095ac8db23d6036000000003d486f800000000000048000000031e800000000006489ea419283181058c8c0000000861160e6aa000048c80000001aee3b6000045680004c4800059d9dfe00016f42670000000000000000002f6085227e92fa5a5173e0b882f2000000000001aa00000006c094f100000000001b3000008a67b92088486800083e800059c000056c800000000ea0d
  | 45 => 0x113a821144611d0fd4846000035b963e000000015a0d900001b903c28000000023200008c400014a11d50a74541c0000f7972828910a2000116000000002b58f0816a8e99000159884880005821f4e0d9a0023c597700e802820d903c66be104c56b58763dc17ec1bfc5f6000000000009b300008180d400004dadc7a7cc80000000000000000063800001350000000000000000000001bf067319b007b9bb819f130a8409a0a43f91a632fa08079a027c1829f604791c6675240000c6c0000c140000000ee066640003a9800000003ca00000000000c8600000001b102a016900005999d2a00008e2000000000000005d5800000013a46ac199027586b667486fc4c79414626050455e198825d85426d983d432a00002b7d0785ef15cc26200001780000000104600001307dc00004e0119c28b2034736d05e000045051e00000000eca56a80005cf05220f918fe56900004d750e858b870a67500000001f3c00000002bc9e6c21a000072391d224e039221f8f5e00018cc2e6075c6b399f868b85006d71a36000000050e09590001336000000000014f90000f78131c0000001fb87ce14f86e71910000000050b588a0001528000144e00000003440bdd0a311a438c9f1c2c080000000000000142b2b0138e0001d500001cf446c046c7b6800045b8000319889064c0c7483a000025680000c25c1e5d282160001bd600011df000000035f80004e796f64a04000000120837780000000000000000081a1b164dc00000000000000054800000000000000000000000009aa00000001dc15d609910fa15880000000b0d47f110077c8d0207218280000000707092a26b1d6157d00002ec91961d783945ce8080516c0000000000000000013714083ee16864878000000014a0d300000a100000001e7885792f6546199278d880c0701a3e3d110ae52f000044780001c20d1e35983d055c9a6800003fc35a8000000000051d9cd60000000000204e00011341338b700000a9c000165600000000000b3e4af963c00016447e4046400000000000a0805795381330fe54db9ca845e842a6d39dca61f05f80e19c3c000000675f8c8286080000000b7200018b002382b272500b400000001ef93244dc800065980b0000000000004c400008b681d9f500250000000000000000000000000000000033e8c4c1a69b4407684620ad992e00000000000ae10000ca2644800000019541a180000001cd200008760000ce43ff8000141c0007a2800056b800023e81365889e0400013b62521f5e4a3205000020406c50b001958d7c5a5908e00000006de8000000000039995f0345000d4678a4e7cb8e4e71904485e314025c31e624bf0000000000016982d800000001b2000000000002b4168000006695c887a600000003bb8f2400013100f60e6a0f4800000000
  | 46 => 0x5a0000126a26f91b8048800032514c0525cf1c70800001151a9e5fd90627fc00005431dde4c500002a5000010702983d382267f69dd87b20a5600000000001d4822e828a1d61bae63790882529ecc15f848861f97482f7980278420b845998c900f8662124136615307de00009a64eb948a000113100003a60000f9d365055e51ac00002a9c4600000005a30cfc0000da45dd03da000000052c00000000000000000054f000031c12700000000000000056218580000fc60
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x152992142749491000552648509ce524400155193141719491000558648505c652440019308414171149100055464c505c452440015619214171149100054564c419d6424400152592106759091000561648419ce424400159193105709091000568648415c242440019308510570109100056464c415c042440015a1921057010910006139d58218e324400188e74608638c91000433261764c8324408d44c955d9320c91022523251764c832440014c4964c9710c91000661211325c432440014c8964c9700c91000652215325c03244001332981437454510005c864850dd15144001561921407454510004cc660501d151440017219214074545100064c615801d151440c94369694074545100044d660501d151440c343696140745451000549648501d151440015a19214074545100064ca60501d151440015319814074545100064c660501d151440c35329614074545100070ca58501d15144001d229214074545100054c648501d15144001d2192140745451000548648501d15144001930801d354545100064c20074d495144001930801d152545100054c65050dd741440015619214375d05100064c9d0855c341440015519314375485100055864850dd5214400153095600744851000668609801d121440011b19814074485100056464c501d121440015a1921407448510004696607418921440019847460c6248510006611d18390921440011a5981d232485100064c9d4845c750440c99327521151d4110004cca6041dd540440017219210775501100054c654419d540440015a19210675501100046c660411d540440015a1921047550110004cc660411d540440017219210475501100064c611811d540440b943a9690475501100044e660411d540440b743a9610475501100054a648411d5404400117198104755011000558648411d540440019329810475501100054c660411d540440019319810475501100044c660411d540440b75329610475501100070ca58411d54044001d229210475501100054c648411d54044001d2192104755011000548648411d54044001930811d654501100064c20475d094044001930811d542501100064c1d484545404400d3309855151501100854c25d5454540440019308755151501102e64ca1075d054044001930752112150110034e8261424854044001d207550921501100054c251811d520440019618260475481100045c660411d5204400155193104754811000558648411d520440015919310774481100056864841dd12044001169981d46248110006521d58318920440019487560e52481100045a660758c920440019307521151481100855825d525452044001b208454951481100064c1d4844c52044001d40754c93148110006e0211324c52044001930752112148110
  | 1 => 0x100629c4187192324840182d879d4648c9210060b61d75192324848948d97a0c648c921224a3e6064dcd3248401a0e85193734c92123493a568718d324848928e94a1c634c921234932558018d324848988c64a1f434c9210050764c509d262d400142d921427498b5000513648509ce62d408d44c954817398b500050b648501d161d400144e969d5320c9500051364c509cb65d000106c984817598b4000513255205ce62d000109f9760c4198b40006079d58310662d000182e756084198b40006239cd8210662d000184e7560a638cb40226239d18298e32d00890cd97e19320cb40226239d3864c832d008988c7460e62487400060ea018710465500018371061c41195400060e84187104655000182d87a0841195400060ba1d82104655000182d87608411954000683a0d821046550001a0d8360841195400068aa01821046550001a271060841195400068a841821046550001a251060841195400058c642811046550001631909c441195400060e61d801046550001a298260041195400050b64871196545000160d93a0865d09400040f66071197425000141d931c465d09400040f66071195425000141d931c465509400052364c71189425000142d97197428c9400060d204655d132500014a4915d0624c94000703196744c832500014369710765585400060da1c41d95615000103c981d954545400060b21c65509215000141d9314274d97200050b648509d365c800144d9214273d9720006079d58310764c800182e7560841d9320006239cd8210764c800105c984c17598f2022623d0e8719132c808d24e95a1c634cb20224a3a528718d32c808928c94604634cb200042b660748c961c800109d981d2634c72000417e61731cf654800182e845ca731952000513e4d729cc654800182c845c9711952023613195839c8544800106d981967210d2000703196745ce5248001c0c655d1739492000712196105ce524800182c76a137554920006131da83dd5524800182c76a1253549200041b66287196324800186a1061c658c9202351365e83196324800142d97196748c9200050b65c655d2324808d84f83a1c654c92023493e6065dcd3248001a0c65a13734c92023493a568718d324808928e94a1c634c920224a32518118d324808d84c65a1f534c92023613195839cb514800182c861d152545200041b660659cb3148001c0c651d1324c5200054a648501d165440015499314072595100050b648501d1654400144d93140725951000549648411d564440015859310472591100050b648411d5644400148d93104725911000558648505c454440015a19210570151100061321573588624400188c845cd62189100041b261205d462440010ac98485741891000523251215cc624400144c9548173189100054664c509d25244
  | 2 => 0xc80118e98d0d711093200643217435c0424c80190e859d3628c9320052c640611d1614c8014719118075581320060b9d182143650c80182e7560841d90320064361584dd9320c801a0e85a13764c8320068361684dd9320c801a0e85613764c8320243366376dd5320c88d44e95dd9754c83200583a5375995320c88d24e95a1c654c832236139d687195320c88928e94a1c654c83223613a5687195320c80188e94a1c654c8320062365287195320c88d84c50a1c654c83200493e6175195320c80184e875d4654c8320059224175195320c88928c94604654c83200613a1e50195320c80160e95dd2644c83223493a5687191320c88928e94a1c644c832226239d287191320c80128f985d0644c832005a124574191320c88d24c95600644c8322243365a87151320c88d84e65a1c544c8322262399287151320c88d44e95e1d325843222523a53874c9610c88948e97dd1325843222623a60744c9610c88988d981d1325843200721204744c9610c801c87101d13258432007211d3814c9610c88d44e95e1d325803222523a53874c9600c88d44e97dd5325803223613a60754c9600c88d84d981d5325803200712200754c9600c801c4a101d53258032007121d7804c9600c80148c944857398b5100417e5d8314262d440181e7460c5098b510060b9d18214262d440184e736085098b51236139d58298e32d440188e7460a638cb512343365f864c832d448d84e75e19320cb510060da0587140645440182d87a0850191510060ba1d82140645440182d87608501915100683a0d821406454401a0d83608501915100689a05821406454401a271060850191510068a841821406454401a291060850191510060d61d811406454401a258260450191510058c646801406454401631919c050191510050b64870193545440160d93a0864d49510040f66070193525440141d931c064d49510040f66070191525440141d931c064549510051364c70189525440142d97193528c9510050e241751913254401468905d4624c951007039d4644c8325440141d931067598b410050b648419d662d040148d921067398b4122523251215ce62d040142d9210475583410042b660419ca655040148d93106729954100523a5a744c8325040181e7460c50d97210060b9d18214365c840184e7360850d97210050764c419d764c840142d9210675d932100523648419cf64c840109c984c57498f2123613d4e8719532c848d24e95a1c634cb21224a3a528718d32c848d24c95600634cb210041b660758c960c840182e855ca73191210060b215725c0644848988c6460e72151210042b660649c85348401c0e751917390921007035d4645ce4248401c8464c4173909210060b1da85dd1424840188c76a0f74509210060b1da8590d42484010ad98a1c648c92
  | 3 => 0x520060761e641416394801a0e646085058e5223493255829c1639488d84c5261c5058e520050b64870993539480144d921c263d4e520051365b535ca5394801c0e64d4d7294e520050764c70993529480144d9318272951520060b9d982990545480141d931827494d520060761d74d8e5354801c0e74d8d7294d520050764c609d2525480105d981827394952006079d183142631480182e746085098c5200493e4d82142631480154890615739485200613e1b7354d521480181c7460c50584520060b1d182141611480112d9814272153420054364c509c854d080181e8760c41996420060761d831066590801a0d83a0841996420060ba1d82106659080182d87608419964200683a0d821066590801a0d8360841996420068660e801066590801a2982a0041996420060e61d801066590801a198360041996420068a6098010665908016159310710996420058964841c42659080188e7360841196420060761e65106639080181d875944198e4200683995821066390801a0d656084198e420060761e85106639080181d876144198e420062361e82106639080188e876084198e420062361d821066390801a0e856084198e420068361582106639080189987a004198e42006a260a801066390801899876004198e4200686615801066390801a89826004198e42005a164841c426390801a16652057458e420060761e651056390801a0e656084158e42224a3251829c5639088988c4261c4158e420050b64871997439080148d921c663d0e420050764c71997429080148d9318672d51420060b9d982994545080141d931867590d420050764c619d6425080109d981867390942006139cd82143651080181e7560c4198c420060b9d582106631080158491611739084200623e1b7350d421080103d981d44158042006071d583105601080182c7560841580420061360c721c1658c80106c9760a30596320062360c721c5648c8010ac9760a315923223613995829cc548c88988e6460a7315232006135d982d4e538c80114d981427314a3200513658509cc528c8010ad962117114a320041b658855c0428c80142f9759564cca320060be1d65593328c80181d875d353d95320051365f535cb654c801c0e74d4d72d95320060b9d182143654c80143a94dd470595320060b9d582107644c80143695dd0715913200529245649cb544c80146890596729513222463a52869cf524c88918c9460673d49320050e241659d2524c80145890596739493223613d4f87594524c80150e949db531493200643213535c4524c80114e98d4d701493223453a56869cf424c88d14c9560273d093200583a5854d4f424c801834819d5649093200525245649ce424c88d84f53a18751093222623d0e861d4424c88988f43e1d641093200543a5676d0c424
  | 4 => 0xdc0a607800e1bda33800000006dc7cc4a8a3e00000000fd294c25928ffb478800419ce923ae25a7635154fc33e720bc1d1d44d014099fef3a5c893ec1771c542f64500aaea44e738c0024a002b8868f4a4a0c7afc40012e031d3000000019e2c1021c4ac0ca042dd60d900000000b43e6af0342c908bc20a443321d9940028698a2237a46cd084dcaa08a9ca0bb8453802d22d956b88e4ae850a826d94c3bbe2960009b844b1a3e0010f96b00630eac2000f30b85212a4034e0a2f46fafa8f54648000239f289b027d208184002a2fc05b8eae7d47ea0e5eec83f8008e2b6001d50710ea7ae413ea80034a6a356000f0ce86c48841e08002d80000000003760002400000848ba00000f80004bc000037400186ac2ebb2ad2cdbca2085428aac1b82c000d6370643f1913a398f60005e10bc600008000d3214472d4ec0000000000280c7842160366e88c319a07427cd6b62002a6000d8001bc000959a8001286800000000c00023ce297c7b000003a00039053dd94c982d1330c9800003605603a000528ec0024de63139a00172002eeba800003aa01151fa9d8d5272021ac25d24b0d968cb52f23b6c81b87180000126003e40f12be000006c06008000000a00c00000040140c00c030100602c000500600c1b00c0a020000000001413020000040001014014030400a0580c024040001d0100000006018060000b024000000b02c0601c070540d0140a00c1300c040000c00400004020000a03c000381101401000020000800c010000100003000000080101c0600c00028040240d01803000010000600810000080300003c0e0200601401004000140006000004080040100003008020240000000000020000003c010140e00403014000040004800014010040002c0000800000030080205000030010000008409004010080800c1402c00090030200104006000020140109f9760c4198854006239cd82106621500105f9760c5098854006139cd821426215001a244160850584540044b660419c854d480150d93106721535200607a1d83142649480181d8760c50992520068360e82142649480182e8760850992520060b61d821426494801a0e8360850992520068360d821426494801a1583a0450992520068960a8114264948018358760450992520068560d811426494801a258260450992520058664c5084264948016299214210992520060761e64142639480181d875905098e5200683991821426394801a0d646085098e520060761e84142639480181d876105098e520061361e82142639480184e876085098e520061361d821426394801a0e846085098e520068361182142639480185587a045098e520069160a811426394801855876045098e5200685611811426394801a45826045098e5200592648508426394801618905d66458e
  | 5 => 0x7e000e4f59f5000000c10a0006a6380016800001dadf0009a0be000cc0028cb5ee627a5063c0000000250000030e0400064d7e60288001cc6712823c0077310088723b13e308e67b9a6aba406d046fbb424f0d215a6c9e800000f90000024a30002c20005c002c155ba600000a5800322b3000000000051de4758000021c003dc0018af78000000012000002a238abe97ada32ba8f499540c803cb50d99f0b1fb85a2703ec0ee8b7a0000089ef254b3cdb30400de02249c951c05da6470ae293800de00000000e511eb5bb2000007d80000252b2c00001045128e3d898da000908007cc00000000005e00236e58a50031aca2747e06618000ee8005a81a58ac4826de26916b30007a30606000842b23fe982d4901392d5b99a688000a8000000000000000e0c8b6e6ca90a11aa9e000103d0223244a4d0ca800ef0005c0003e800932a41e80000000ac716c17c0be5b00016c002aa641fc460006904c19641b60000000000338778007a8008a23a0000062184878a79822d71216001e3d02566b80018b5cbdeec36a06bfa661a4a45f40fdfbbed78009f974fa00041c0022a001439e00000e932ed60b4f19304b1d2000000ed39b829a0013a000534d8ae0003e1c1408830a5280600000003460fe18590a0b380000078ad000003f20f4004e012b9c000e0005ebacb16020df0cda95e598992abc2c515cb729c468008b998cb1d72c4004480021a2c8d2f8b010c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x780001e6c021005a69f12a06cb8c64dd84c58000001c0000048c400000283166800a20553a21c00a0f8000cd746461082204e9300260001d00604008000c800000000000003590025380000180040000008041061810002084681369f936085098c5223409b50cb0a1398a51900304a8724175195320c801640d01023a264b086400b10684801d5325803223409b51c9ae5398ca900031108464c505c4524400189042324282e2292200084c6a48510570109100062210ac9882b80848800312085648415c042440018424b108992e21922000c12258854c9700c91000624331490a03a2a28800312298648501d15144001890cc324280e8a8a2000d40a4d921407454510006a0326c90a03a2a288002921a220074d515144001098d49003a6a4a8a2000a4468c801d3525451000426352400e8a92a288002911a3200745495144001490d14e842ae1a0a2000c48255826007448510005243453a908b8ea08800312198a48411d540440018914c324208eaa022000c48661921047550110006a0526c90823aa808800350193648411d54044001490d11023aca8a02200084c6a4811d7425011000522346408eba128088002131a9204755094044001488d19023aa84a02200084c2a4875515150110006241303aa8490a808800312094609811d520440018904b908a92a29022000e401d4844c93148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x98a
  | 4 => 0x3
  | 5 => 0x150a
  | 6 => 0xa0a
  | 7 => 0x180a
  | 8 => 0x5
  | 9 => 0xa4a
  | 10 => 0x198a
  | 11 => 0x6
  | 12 => 0xb09
  | 13 => 0x1549
  | 14 => 0xb89
  | 15 => 0x1849
  | 16 => 0xbc9
  | 17 => 0x19c9
  | 18 => 0x3c9
  | 19 => 0x3ca
  | 20 => 0xcc9
  | 21 => 0xcca
  | 22 => 0x15c9
  | 23 => 0x15ca
  | 24 => 0x409
  | 25 => 0x40a
  | 26 => 0xd09
  | 27 => 0xd0a
  | 28 => 0x1609
  | 29 => 0x160a
  | 30 => 0x1889
  | 31 => 0x188a
  | 32 => 0x449
  | 33 => 0x44a
  | 34 => 0xd49
  | 35 => 0xd4a
  | 36 => 0x1649
  | 37 => 0x164a
  | 38 => 0x1a09
  | 39 => 0x1a0a
  | 40 => 0x749
  | 41 => 0x74a
  | 42 => 0x1049
  | 43 => 0x104a
  | 44 => 0x1949
  | 45 => 0x194a
  | 46 => 0x1a89
  | 47 => 0x1a8a
  | 48 => 0x209
  | 49 => 0x8a
  | 50 => 0x4
  | 51 => 0x1409
  | 52 => 0x128a
  | 53 => 0x289
  | 54 => 0x10a
  | 55 => 0x1489
  | 56 => 0x130a
  | 57 => 0x2c9
  | 58 => 0x14a
  | 59 => 0x14c9
  | 60 => 0x134a
  | 61 => 0x1709
  | 62 => 0x180a12
  | 63 => 0x170a
  | 64 => 0x19cbd1
  | 65 => 0xcc3d1
  | 66 => 0xcc3d2
  | 67 => 0x40cd2
  | 68 => 0xccd
  | 69 => 0x44cd1
  | 70 => 0xcce
  | 71 => 0x415d2
  | 72 => 0x455d1
  | 73 => 0xd0411
  | 74 => 0x160412
  | 75 => 0x178a
  | 76 => 0x74d11
  | 77 => 0x75891
  | 78 => 0xd4452
  | 79 => 0x164451
  | 80 => 0x17c9
  | 81 => 0x74d52
  | 82 => 0x75a12
  | 83 => 0x194751
  | 84 => 0x1a8752
  | 85 => 0x1a9951
  | 86 => 0x1a9952
  | 87 => 0x45411
  | 88 => 0xcc451
  | 89 => 0x45651
  | 90 => 0x44d11
  | 91 => 0x75491
  | 92 => 0x74291
  | 93 => 0xd0751
  | 94 => 0x75951
  | 95 => 0x28751
  | 96 => 0x148751
  | 97 => 0x75352
  | 98 => 0x15c451
  | 99 => 0x5c9
  | 100 => 0x74152
  | 101 => 0x41292
  | 102 => 0xcc412
  | 103 => 0x41612
  | 104 => 0x40d52
  | 105 => 0x15c412
  | 106 => 0x58a
  | 107 => 0x75a92
  | 108 => 0xd4752
  | 109 => 0x1a0752
  | 110 => 0x14752
  | 111 => 0x134752
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 1896
  | 6 => 8550
  | 5 => 4291
  | 4 => 507
  | 3 => 41
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | 3 => packedAt gbK3 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | 3 => gbHint (packedAt gbK3 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (79704+((h/796+packedAt gbK7 (70152+(h % 796)*12) 12) % 2866)*12) 12
  | 6 => packedAt gbK6 (456250+((h/3275+packedAt gbK6 (410400+(h % 3275)*14) 14) % 11791)*15) 15
  | 5 => packedAt gbK5 (273488+((h/1563+packedAt gbK5 (253169+(h % 1563)*13) 13) % 7487)*14) 14
  | 4 => packedAt gbK4 (37440+((h/195+packedAt gbK4 (35490+(h % 195)*10) 10) % 773)*10) 10
  | 3 => packedAt gbK3 (3440+((h/17+packedAt gbK3 (3321+(h % 17)*7) 7) % 84)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fffe3f83fc1fe0307f81ff03f05349f5bc673
  | 1 => 0xe0e03c3fc1fe0ffff83fe07fc00acb6ca4fb9c
  | 2 => 0xff003fc001fff003ffc0007ffff30c70c70c1f
  | 3 => 0x3ffffe000003ffffff8000fc0f80f80fe0
  | 4 => 0x3ffffffffffc0000000000fff000fff000
  | 5 => 0xffffc000000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x121809802c01219004845108a00100509c231
  | 1 => 0x2042800840420489081241248200412c005294
  | 2 => 0x5a042d421135a022d680824b34730c50c60c0a
  | 3 => 0x8083666b4108042e7259a0104bc0e80f00d40
  | 4 => 0x10113bb739b9c97042010c0218dfb000ffa000
  | 5 => 0x9c9e0004202101808406100c20efeffa000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37215
namespace PEqualNP.Outside.L_meta_37215
open PEqualNP.Outside.L_meta_37215.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_64 : Interval s0Atlas 3 64 20 := block_range (n:=20) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 84 := (concat bs0_3_0 (concat bs0_3_32 bs0_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 186 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 20 := block_range (n:=20) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 84 := (concat bs1_3_0 (concat bs1_3_32 bs1_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 186 := (concat (concat bs1_4_0 (concat bs1_4_32 bs1_4_64)) (concat bs1_4_96 (concat bs1_4_128 bs1_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 41 := (concat bgb_3_0 bgb_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 507 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4291 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))))) (concat (concat (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280))) (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))))) (concat (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824))) (concat (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))))))) (concat (concat (concat (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368))) (concat (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 bgb_5_2496)) (concat (concat bgb_5_2528 bgb_5_2560) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656))))) (concat (concat (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 bgb_5_2784)) (concat (concat bgb_5_2816 bgb_5_2848) (concat bgb_5_2880 bgb_5_2912))) (concat (concat (concat bgb_5_2944 bgb_5_2976) (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)))))) (concat (concat (concat (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328)) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456))) (concat (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)) (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 bgb_5_3808) (concat bgb_5_3840 bgb_5_3872)) (concat (concat bgb_5_3904 bgb_5_3936) (concat bgb_5_3968 bgb_5_4000))) (concat (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 bgb_5_4128)) (concat (concat bgb_5_4160 bgb_5_4192) (concat bgb_5_4224 (concat bgb_5_4256 bgb_5_4288))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2432 : Interval gbAtlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2464 : Interval gbAtlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3776 : Interval gbAtlas 6 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3808 : Interval gbAtlas 6 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8096 : Interval gbAtlas 6 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8128 : Interval gbAtlas 6 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8160 : Interval gbAtlas 6 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8192 : Interval gbAtlas 6 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8224 : Interval gbAtlas 6 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8256 : Interval gbAtlas 6 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8288 : Interval gbAtlas 6 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8320 : Interval gbAtlas 6 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8352 : Interval gbAtlas 6 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8384 : Interval gbAtlas 6 8384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8416 : Interval gbAtlas 6 8416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8448 : Interval gbAtlas 6 8448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8480 : Interval gbAtlas 6 8480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8512 : Interval gbAtlas 6 8512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8544 : Interval gbAtlas 6 8544 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8550 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))))) (concat (concat (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280))) (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568))))) (concat (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824))) (concat (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))))))) (concat (concat (concat (concat (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))) (concat (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)))) (concat (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008)) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)))))) (concat (concat (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296)) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424))) (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712))))) (concat (concat (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968))) (concat (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096)) (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 bgb_6_4384)) (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 bgb_6_4512))) (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768)))) (concat (concat (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 bgb_6_4896)) (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 bgb_6_5024))) (concat (concat (concat bgb_6_5056 bgb_6_5088) (concat bgb_6_5120 bgb_6_5152)) (concat (concat bgb_6_5184 bgb_6_5216) (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312)))))) (concat (concat (concat (concat (concat bgb_6_5344 bgb_6_5376) (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))) (concat (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696)) (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856))))) (concat (concat (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984)) (concat (concat bgb_6_6016 bgb_6_6048) (concat bgb_6_6080 bgb_6_6112))) (concat (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240)) (concat (concat bgb_6_6272 bgb_6_6304) (concat bgb_6_6336 (concat bgb_6_6368 bgb_6_6400))))))) (concat (concat (concat (concat (concat (concat bgb_6_6432 bgb_6_6464) (concat bgb_6_6496 bgb_6_6528)) (concat (concat bgb_6_6560 bgb_6_6592) (concat bgb_6_6624 bgb_6_6656))) (concat (concat (concat bgb_6_6688 bgb_6_6720) (concat bgb_6_6752 bgb_6_6784)) (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912)))) (concat (concat (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040)) (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168))) (concat (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 bgb_6_7296)) (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 (concat bgb_6_7424 bgb_6_7456)))))) (concat (concat (concat (concat (concat bgb_6_7488 bgb_6_7520) (concat bgb_6_7552 bgb_6_7584)) (concat (concat bgb_6_7616 bgb_6_7648) (concat bgb_6_7680 bgb_6_7712))) (concat (concat (concat bgb_6_7744 bgb_6_7776) (concat bgb_6_7808 bgb_6_7840)) (concat (concat bgb_6_7872 bgb_6_7904) (concat bgb_6_7936 (concat bgb_6_7968 bgb_6_8000))))) (concat (concat (concat (concat bgb_6_8032 bgb_6_8064) (concat bgb_6_8096 bgb_6_8128)) (concat (concat bgb_6_8160 bgb_6_8192) (concat bgb_6_8224 bgb_6_8256))) (concat (concat (concat bgb_6_8288 bgb_6_8320) (concat bgb_6_8352 bgb_6_8384)) (concat (concat bgb_6_8416 bgb_6_8448) (concat bgb_6_8480 (concat bgb_6_8512 bgb_6_8544)))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_128 : Interval gbAtlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_160 : Interval gbAtlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_224 : Interval gbAtlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_256 : Interval gbAtlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_320 : Interval gbAtlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_352 : Interval gbAtlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_416 : Interval gbAtlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_448 : Interval gbAtlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_512 : Interval gbAtlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_544 : Interval gbAtlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_608 : Interval gbAtlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_640 : Interval gbAtlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_704 : Interval gbAtlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_736 : Interval gbAtlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_800 : Interval gbAtlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_832 : Interval gbAtlas 7 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_896 : Interval gbAtlas 7 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_928 : Interval gbAtlas 7 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_992 : Interval gbAtlas 7 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1024 : Interval gbAtlas 7 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1088 : Interval gbAtlas 7 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1120 : Interval gbAtlas 7 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1184 : Interval gbAtlas 7 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1216 : Interval gbAtlas 7 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1280 : Interval gbAtlas 7 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1472 : Interval gbAtlas 7 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1896 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672))) (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800)) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928))))) (concat (concat (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152))) (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))) (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_3 i (by omega) hi
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
  · exact allgb_9 i (by omega) hi
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 44, 60),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0feeeeeeaeeeceee0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4008505056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_37215.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[0,5]⟩,⟨.and,[2,6]⟩,⟨.and,[4,5]⟩,⟨.and,[1,4]⟩,⟨.or,[7,10]⟩,⟨.and,[2,9]⟩,⟨.or,[6,12]⟩,⟨.or,[8,11]⟩,⟨.and,[3,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4008505056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4008505056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_37215

open PEqualNP.Outside.L_meta_37215 in
theorem PEqualNP.Outside.L_meta_37215 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4008505056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4008505056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
