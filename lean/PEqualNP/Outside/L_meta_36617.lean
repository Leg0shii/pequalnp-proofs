import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36617.Model
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

def eqF (a b : Sig) : Bool := Nat.beq a.toNat b.toNat
theorem eqF_eq (a b : Sig) : eqF a b = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp [eqF,BitVec.toNat_inj]
noncomputable def anyEq (m d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || ih) l
theorem anyEq_eq (m d : Sig) (l : List Sig) :
    anyEq m d l = (l.map (masked d)).any (fun v => v==m) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || anyEq m d vs) = _
    rw [ih,eqF_eq,List.map_cons,List.any_cons]
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d || anyEq (masked d a) d pool ||
    (u && anyEq (masked d (neg a)) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  simp only [availF,availableB,eqF_eq,anyEq_eq]
noncomputable def allF (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => availF u d pool v && ih) l
theorem allF_eq (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) :
    allF u d pool l = l.all (availableB u d pool) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (availF u d pool v && allF u d pool vs) = _
    rw [ih,availF_eq,List.all_cons]
noncomputable def countF (d : Sig) (l : List Sig) : Nat :=
  @List.rec Sig (fun _ => Nat) 0
    (fun v _ ih => cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ ih) ih) l
theorem countF_eq (d : Sig) (l : List Sig) : countF d l = l.countP (isMaskedConstant d) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ (countF d vs)) (countF d vs) = _
    rw [ih,eqF_eq,eqF_eq,List.countP_cons]
    change _ = _ + if (masked d v == zero || masked d v == d) = true then 1 else 0
    cases (masked d v == zero || masked d v == d) <;> rfl
noncomputable def scalarPoolCutF (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  allF u c.domain c.wires rest &&
    cond (availF u c.domain c.wires (choiceVal op))
      (Nat.blt (k+c.paid) (c.bound+countF c.domain (choiceVal op::rest)))
      (Nat.blt (k+c.paid+1) (c.bound+countF c.domain (choiceVal op::rest)) &&
        (allowedB u op.1 && (availF u c.domain c.wires op.2.1 && availF u c.domain c.wires op.2.2)))
theorem scalarPoolCutF_ok {u : Bool} {c : BoundPool} {k : Nat} {rest : List Sig} {op : Choice}
    (h : scalarPoolCutF u c k rest op = true) : scalarPoolCut u c k rest op = true := by
  simp only [scalarPoolCutF,allF_eq,availF_eq,countF_eq,Bool.and_eq_true] at h
  obtain ⟨hall,hc⟩ := h
  simp only [scalarPoolCut,choiceOK,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  cases hz : availableB u c.domain c.wires (choiceVal op)
  · rw [hz] at hc
    simp only [cond_false,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inr hc.2⟩
    simpa using hc.1
  · rw [hz] at hc
    simp only [cond_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inl (by simp)⟩
    simpa using hc
noncomputable def anyP (f : BoundPool → Bool) (l : List BoundPool) : Bool :=
  @List.rec BoundPool (fun _ => Bool) false (fun p _ ih => f p || ih) l
theorem anyP_eq (f : BoundPool → Bool) (l : List BoundPool) : anyP f l = l.any f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v || anyP f vs) = _
    rw [ih,List.any_cons]
noncomputable def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  anyP (fun p => scalarPoolCutF u p k rest op) pools ||
    (links (keySet (choiceVal op::rest))).any (sameWords (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd (scalarPoolCutF_ok ok)
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
noncomputable def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

noncomputable def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
theorem or_ones_and {n : Nat} (x y z : BitVec n) (h : (x &&& y) ||| z = BitVec.allOnes n) :
    x ||| z = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun w => w.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hi, decide_true] at hb ⊢
  cases hx : x.getLsbD i <;> simp_all
theorem takeTwo_right (c : Cov) (a b : Bits) :
    takeTwo c a b = takeOne c b &&& ~~~((c.2.1 &&& a) ||| (c.2.2 &&& (a &&& b))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo, takeOne, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
def quickPair (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152
  else Nat.blt c.1 (c.2.1+1) &&
    (((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152) &&
     ((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152))
theorem evalMove_cov {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) ≠ BitVec.allOnes 152) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else if (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) != BitVec.allOnes 152 then true else _) = true
  by_cases hlen : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap
  · rw [if_pos hlen]
  · rw [if_neg hlen,if_pos (bne_iff_ne.mpr h)]
theorem evalMove_long {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else _) = true
  rw [if_pos h]
theorem quickPair_ok {c : NodeContext} {a b : Decor} {op : Nat} (h : quickPair c a b op = true) :
    testPair c a b op = true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  unfold quickPair at h
  simp only [testPair,Bool.and_eq_true]
  split at h
  next hlt =>
    have hl : cap < n := by simpa using hlt
    have hf := bne_iff_ne.mp h
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_long (ka:=true) (kb:=false) (by simp <;> omega)⟩,
      evalMove_long (ka:=false) (kb:=true) (by simp <;> omega)⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
  next =>
    simp only [Bool.and_eq_true,Nat.blt_eq,bne_iff_ne,ne_eq] at h
    obtain ⟨hl,hb,ha⟩ := h
    have hf : (takeTwo cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ||| column (!cov.2) (dbin op a b).2) ≠ BitVec.allOnes 152 := by
      intro e
      rw [takeTwo_right] at e
      exact hb (or_ones_and _ _ _ e)
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_cov (ka:=true) (kb:=false) hb⟩,
      evalMove_cov (ka:=false) (kb:=true) ha⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
theorem pairQ {c : NodeContext} {a b : Decor} {op : Nat}
    (h : (quickPair c a b op || testPair c a b op) = true) : testPair c a b op = true := by
  rcases Bool.or_eq_true_iff.mp h with q | t
  · exact quickPair_ok q
  · exact t
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (fun op => quickPair ctx a b op || testPair ctx a b op))
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => pairQ (h.1 b bm d (opsOf_mem hd))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => pairQ (h.1 a haTail d (opsOf_mem hd))
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


end PEqualNP.Outside.L_meta_36617.Model

namespace PEqualNP.Outside.L_meta_36617
open PEqualNP.Outside.L_meta_36617.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 48]

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

noncomputable def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

noncomputable def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_36617

namespace PEqualNP.Outside.L_meta_36617
open PEqualNP.Outside.L_meta_36617.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x7aa29b01405998e5e2489d0fa16004000340740c24c852062d00150c01c000062c036ba001c31a0b80000421c004308200228bff42bf42fe42fd42bd42fc42ff41fe41fd41fc41ff21fe21fd21fc21ff40fe40fd40fc40fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083f660107f8c020fe98041fc30083f060107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43bca7885794f10fea9e217d53c43baa7885754f10fe29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c437e85887f90b10fea1621bd42c43f885887fccb10ff19621fd32c43f865887fd0710ff20e21fd41c43f883887f8c710ff90e21fe21c43ec43887f48710fa90e21fc21c43fe81887f90310fea0621fc40c43fe61887f8c310fe98621fc30c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff428437e85087f90a10fea1421bd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21fe41843fa83087f10610ff98c21fe31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fa40843fa81087e50210fe20421ff30843f661087f8c210fe98421fc30843f061087fc8210ff10421fa20843fa41087e48210fe10421ff10843ee21087ec4210ffaa2217f544437ea8884fd5110ff2a2217e54443faa8885f55110fe2a2217c5444378a8884f15110ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ffa1a21fe43443fa86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221bf42443fc84887f50910dea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21fc41443fe62887f8c510fe98a21ff21443fc42887d88510fe90a21f521443f842887fd0110ff20221fa40443fa80887e50110fe20221ff30443f660887f8c110fe98221fc30443f060887fc8110ff10221fa20443fa40887e48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff420437e84087f90810fea1021bd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd544c3f8a8985f15130ffa92617f524c3fca4987f54930fe292617c524c3fe84986fd0930ff21261fd424c37a84987f10930ffa8a617f514c3fca2987f54530fe28a617c514c3fe82987f90530fea0a61fc414c3fe42987f88530fe90a61fc214c3fe80987f90130fea0261fc404c3fc6098778c130ffaa0617f540c3fca8185f95030feaa0617d540c3f8a8185f15030ffa9061fe520c2fca4187f54830bea9061fc520c3fe84186fd0830ff21061fd420c37a84187f10830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fea0861fc410c3fe42187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187f8c030fd18061fd300c3f26018764c030ffaa6417f54c83fca9905f95320df2a6413e54c83faa9905f55320deaa6413d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7907fd0f20ff21e41fd43c83f887907fd0b20dfa1641fe42c83fa85906f50b20fe21641fe32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fb30c83fc61907f4c320fe18641f830c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7107f94e20bf29c41fd53882faa7107f14e20be29c41ff43883fc87107f50e20fe21c417d52883fe85106fd0a20ff21441fd428837a85107f10a20ff99441fe32883fea3107f94620bf28c41fd51882faa3107f14620ffa0c41fe41883fa83107f10620ff90c41fe21883fa43107f08620bf28441ff40883fc81107f50220fe20441ff30883fc61107e8c220fe98441f930883f861107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20efa9a415f53483fca6905f94d20fea9a417d53483f8a6905f14d20ee29a415c53483fe86907f90d20fea1a41fc43483fe84906fd0920ff21241fd424837a84907f10920ff99241fe32483fa64907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907e8c120fe98241f930483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8106f950209f2a041fd54082faa8106f550209eaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041bf42083fc84107f50820dea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841f651082eca2107f54420bea8841f551082eaa2107f14420ffa0841fe41083fa82107f10420ff90
  | 2 => 0x87fe8510efd0a21ff21443fd428877a8510ff10a21bf28c43ff41887fc8310ff50621fe20c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fe8490efd0921ff21243ee42487fa8490ef50921f6a1243ad42487f88490ffd0521ff20a43fd41487f88290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043be540867ca810ff55021beaa043bd540867aa810ff15021be2a0437e52087fe8410efd0821ff21043fd420877a8410ff10821bf28843ff41087fc8210ff50421fe20843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010fe94021bd28043fd50086faa010fe54021bca8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81ff52d03fca5a05f94b40fea96817d52d03f8a5a07fd0b40dfa1681fe42d03fa85a06f50b40fe21681ff51d03fca3a05f94740fea8e817d51d03f8a3a07fd0740ff20e81fd41d03f883a07fc8740ff10e81fd21d03f843a05f55240ffa9c81fe53902fca7207f54e40bea9c81fc53903fe87207f90e40ffa9481fe52902fca5207f54a40bea9481fc52903fe85206fd0a40ff21481fd429037a85207f10a40ffa8c81fe51902fca3207f54640bea8c81fc51903fe83207f90640df20c81fd41903f883206f10640ff90c81fe21903fa43207f08640bf28481ff409037e81207ed0240ffa9a817f53503fca6a07f54d40fe29a817c53503fe86a07f90d40fea1a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940dfa1281fe42503fa84a06f50940fe21281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540ff20a81fd41503f882a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207f54c40bea9881fc53103fe86207f90c40fea1881fc43103fea4207f94840bf29081fd52102faa4207f14840ffa1081bf42103fc84207f50840dea1081fc42103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30ff21c61fd438c3f887187fd4a30ff294617e528c3faa5185f54a30fe29461ff428c37e85187f90a30fea1461bd428c3f885187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe61187ecc230ffaa2617f544c3fca8985f95130feaa2617
  | 3 => 0x802000000000020200300200c00003c0a00400603c0080501c008028020141a0100000000480000001600800800012008000040000d40180f00a0000100100c01811804006000020210080340000503a00001802002024020050000240601d008018008100020bc0080200601c0180902c02c010110000280300101e0200d0000000240000f02001002803004000000070140140d000058018010140000100080c00e00400800012030098000000080000700a000000080000180080400001c0100300c000010000100180480103a00800009000000008000020380001500600806806012008000000040140300202c0000080e07205c0080f00008c038080180080880100800004800000033fea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0b7ea3a16f94742dea8e85bc51d0b7ea1a16f94342dea8685bc50d0afaa9214f55242bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffa9683fe52d06fca5a0ff54b41bea9683fc52d07fe85a0efd0b41ff21683fd42d077a85a0ff10b41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4a41ff294837e52907faa520df54a41fe29483ff429077e8520ff90a41fea1483bd42907f88520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941dfa1283fe42507fa84a0ef50941fe21283ff41507ee82a0ff90541df20a83ff50506fea0a0ff94141fea8283fc50506f8a0a0df95041ffa9083fe52106fca420fb94841b729083fd52106faa420fb54841b6a9083fc52107fe8420efd0841ff21083fd421077a8420ff10841bf28883ff411077e8220ff90441fb20883fd411077a8220fd50441ffa8083fe50106fca020fe94041bd28083fd50106faa020fe54041bca8083fc50107fea990dfd5321ff2a6437e54c877ca990cf95321feaa6437d54c877aa990cf55321fe2a6437c54c87fe8590efd0b21ff21643ee42c87fa8590ef50b21f6a1643ad42c87f88590ffd0721ff20e43fd41c87f88390ffd4321ff286437e50c87faa190df54321fe28643ff54886fea910ff95221bf2a443fd54886faa910ff15221be2a4437d528
  | 4 => 0x75a0c8bb8000c5203cf11181141d80abc340e4875c2ee04db4000000231c000000000801ca035c12931122012c000001110b4c001470f3cef53e4f680000000000000000018b0ee93f60304f164800149011177c9683ec1c000136c0003321d15bc000e19ec0000020001e20cd1761a99514e280015186ba1d90780dc820fb8b883e0001b05ee80000022f9942198938c88344001d38bd9d48871d30faa280d91e18cc9f98319f71d58d79859258001b60001dd5122328680001afd540001358000001bdc000000e55c11a616b4001679b51559538cf9610ff8000f98771c094fcb6899c000001cc028cc414084690922c0775edc59c2d8b217a0001a500004e00003349f1794000c15c003c00621dc5ac6c18c4000000f4d2d0d2a04179da40000c31748065eeca613380016c4411049ba96190240004740022462d16b90a5ddd8c1906334a1d271949388b9c7a05d42a1ae4c214a963df8d7886080716e0951fe9ee45503915495c5f316a9aa9c91ba1784001ac00014d9030001f41730c09addfd95200000486900000003f41250e83801f84c8001c716980000001e9c21ac8bf9e602b48a06599c235937a2d82294280b9759f7d9004800007840000bc371fc8ee0a916f21a8c5c001bfc9c0248879ae8000a4d575ed4bf0000001564000528ca8358781aecbce189e5200000000096ce1d8946d055dccc394000e2cec85900002422ec0023249b0ef80020e43b2190f5c78c895e40bbc63d2103b4b18dd08c10b4385342100881740d944297aca595c9711555728a00238d20b589287b01a00080f00e0100080200a0000080601c0240480c00000c0100500000c058030020600600c03a00c02813006084050020000000180000001c020030020040b80300000803801026000020030040400000600000c0480a01a0200080300a0040100000c03000000000000028090360080000305a0a8008090020080e80e00e0041680000a014078020080000580c0060001080401c000090030040000000a00000c05005000050030010020180080901e0000700900001002009000010018000060640080000800c0300600a000000040000a4000010040000000200600404004002024040230040081b81000600400800024010020000540080002900e02401019038060018020060000000000000c00002004044050040100041b8020100000080d0080b80383f0000000100800800c00001002008070020000240481108c044008010160040000100c0000100000c00c008150000040080104606001807002050038260000001a0000340181080003c0c8048000000180280300600c040090320080b00500a00400801004004000050000200101102e0000000200001c01807062000050170060000180101000c0000701a01c008040000000d00603a0600
  | 5 => 0xa105204ec000cf40000000002f40b562138490cf91dfdd906680005980001d1768628000fd98b89f8984f600002e19d0da8ef04480005861c07300017b1f904b80014b0d3d2b80021280007e8b507358ac4600000022c86d8d10c814c9318000000001cf00015f8794001a800019d8c2ccc0f24fc1b68fb05d19813602093a13998a9bb8c12350dd91296d14518117660edb822013315cdd6a18c5fc000f3071a300218c60df86c80010c91b9571691a58919a00000824a5d9b5f8477a26464c0583fc252160cf0d9dbb0439248001b5956005c859a6800032077d0700c0fd5848000000e68000000c380011d1654189b486115e0c497a4000361701d88f562b8ba8514699394000935081550530a355d9f50ba5ef89302aa262058ff022c3f1751eba0a1288769ec91794405ec558518000c556e88196b076d9f8660270db96c23113c0000ed4a2591d2d8ca45dc001fe0840388ae01b9e703259d48f0f45ff1dd0099171ab8399260a14ed9bedd0163934990dda191a3214613d504178e0349e9db9279e0897a2905cd950000ac19ddc29a903080500009099b9821e68e087f21e442011ddbd8fd3b8808490ca190a33c720dac1fdd2157cb01e585a882c3d9f943aa218579cc956dd101ed0d1301118301218000001be80014840000000018f8000650fde021ce11f00a0b4838e111c1a0e800039c700d086887c96641600a54e4040001448ad1840c6e1fa1e9c99f80000115804a5000070cd352f000136526830c0022f00005410b062cd40fbdfb07cd9a10098e06a1100efd42def0001af5f107b80817f8470d89321809df00007bd0cc29091dbc9438c703061cd6a41a5dd8ad8958d58989634cb1e280007a84fc0f0ce9b20000010001771868000faceb07ad4e9f084500f566920d9a50680ce0f13e06959897ca2a90ac6217f53f0f22230792279a72099b187f9f21df9bc04b0008f9cdbc5f90f16da33a046368b400012097e4ab85700e2056269ee0001368848508a0c0e50522d62285c5ef4000af819a238295c60a0a0e12c85b9c500021419904a8e6092d8e86494188d15b98f0810e50f0897d8300c8000ac9bd050e15056cb98000f500014814455800008380021380000010b8e0cc3df582818a40004d20cc000001498000000000000000c4c001c40d700005e20c5c89130000001b32299f485f15080000006f80000001d8089628000002209dec998bacee55018a21186fc0021d41ac001a28000b817c0560b1c2e99c40015a0fca028f4000232c0000000002110a2069bf4000269bf8bc80002215992e80007091e51d8001161e912040680000014f0001d6014c00036400007400000014a05c00080c000a186e040013cd30d8d1500012a9299eb1a18c9898c7a565983815de80e3d4d42c858dea01901399aa018df1bf170d8b52b
  | 6 => 0xe4478d613c8739cd8000711670619231c481201011f4000a88001958002149818000db0278ab0000001688f2d6404300004580009a92c1c79420fcc73c46400109c29e13050176cc44000f49cf800162c00031000146992937c0021205e80000015c1a78e81dc8c252e07d8c5956a1a1de0c34e385d87889119c828a17d108da1b7888a0b00000fa1c5d78002050575b89b120d9075b72271200000000002361a21ce86c58d88c95788319adb000fc0000394ec36c5c80021680016fa158bc14e21ec001b99b0810c000df4000fe83145b01784a0acc2ad43cb38de965c3e8001148001af8000000e951e8001650728a80000869a38835b912a0f719b0131d98000d849e0d680000018722419941340011c0000000a2d2901c8000000a3dd503a14105e57d0fe40005f43d0339f00001ca9329ecc0015913ecf5977964d9149d0de0c1984c001924000000000975cbdde8000ce4af0900564001910a70d49589931281df6179d28001e10aa87dd89d138e21a31899371a893dd8290d92508fa181d40dc1aa150d920b5d9cc760e44e004089a15060a80a8e103681f0e722504f90a93f8798200b10da40ad8793ccdb4cd8078fa033c2310991b0961351705e008907e0bd0d01be0260000a79608828be000019cf88001ae2048548000e880008e1d185100014f46b018c00000000224c0000000008d97b8001d097986a94882c0c1d4304f5309199661a49eda185ad80007c00009144d99397907d23419980007c5cc49d89416bc000c29038bb46787d5fb8348108000000aa00000010c40d8ce0568600750000000fb4000991000fc4259da8755c801b12f8f2980d6adcd626d780ec09c97fcf35380170a404ea349fa8dc90c0f016a20d4000000ae8a69ab03788b1f38e4c7498ca2e401969e0c1e315f11ec1b5fd1e7800074d77599c0919f000151d5e8001f280009800000022b0a48000d391903c8001e48001ea91a80019ea2a1ad1c5834d4d1968ba0c00641c6835625df19060419e8a315c391e0b08ea0000a052285bd9e0000b78d54159739e98b60ec400000000155c0000020d0e24000e30d50fe22dcbc4f813748983c46f00010894796309642d1b394017a858837d0286f5ed1325455861cd2010031f60e162580014a15a8948eb80000d42f80000d0000be9ff8edca98554d99f79882170f181195109fd88c2b8e905b4000488e040011690bc5a1cb0029019de4001e393900011fe0717e99be0082f08514b99703e4b541a8c6a0809200020b9cb8000a540005c0001159b283b8351dcd7d8a31db22562898897199794ddd714fa2e10e15b06452384c0e417080020dcb90000a20141680150e7a3189940002fd3d1fc01443281805959616440006e80001540000008b8001fa606079c3f9fa18bc001af00000020f8c900000b0bd51c9bd4
  | 7 => 0x135e038e59cdcf788c4d193a87b58014581e21c8424498375f9c1685818920890f8fa5530638f38000000002175f897f12414c15288e8b720798516000000e9dc2108c784411f8ea8a2972032c0ed058d80ed13e97ec860a39020cb9011bd8002210630b2a331dc42980017e0670001c30b32220001a0a1f1a122e8002308000bb00022495d1db53b09713d91898d1434000000c6538c001f6a090b761e0e98fd11a1ce61b8d2c53908c81ca647407442b16c88a89b86561b1b
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x4320427c650c810af99032042bd640c810bd98432042f5610c810be98032042f9600c8109f992510427d64944109f98e510435e63944109798e510427d6394410d758e510425d63944109f98a510427d6294410cfd0a510433d42944109f597410427f65904109f596410433e5490410cf55241042fa6090410be582410427f65504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410bb98841042ed6210410be98041042f960104109f597310435f53cc4109fd96310427d658c410d794e310435d538c410be98231042f9608c4109fd9531042bf644c410af191310435f534c4109f59431042fa600c410be580310427d65c8410af99321042bd64c8410eb50b210427f65884109f596210436e5288410db54a21043765188410be98221042f960884109fd9521043ad4248410dd945210427f65084109f59421042be6408410af59021042de6308410b758c210436e5208410db54821042fa6008410be580210427e64940109f592500427d63940109f98a500427d6294010cfd0a500433d42940109f586500427d65d00109fd96400427d6590010cf952400433d5490010bd98640042f56190010de942400427f6550010de941400427f65100109f994400427d65100109f194400433e5410010cf55040042f66110010bd584400427d65cc010de943300427f658c0109f596300435e538c010d754e30042f6618c010bd586300427f654c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bd98430042f5610c010de94030043d9300c0109f59720042be64c8010af593200427f65880109f596200436e5288010db54a20042f66188010bd586200437a50880109fd9520042df6348010b718d200437a50480109fd94200427e65080109f594200427c6508010af99020042bd6408010b798c20042dd6308010db948200436d5208010bd98420042f56108010b798f10042dd63c4010dd59710043d663c4010f558f100437752c4010dd54b10043b742c4010ed50b10042f56184010dd94610042f96584010de59610042796584010ded5210043795484010de94e10043785384010ded4a10043795284010eed0a10043b94284010be586100437a5184010fc946100427f6544010afd9110042bc6444010bdd95100437765440109dd9510043b76444010ed19110043775244010dd54910043b74244010ed50910042f76044010dd94110043f34044010fc10110043f23044010fc4c110043f22044010fc48110042fb6544010ded95100427b6544010eed9110043b86444010ded5110043795444010de94d10043785344010ded4910043795244010eed0910043b94244010bed8510043f36144010de94510043f25144010fcd0510043f04144010fc8c510043f13144010fc88510043f12144010
  | 1 => 0x427e64d4c109f593530427e62d4c109f58b530437661d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042f66190c10bd58643042fa6090c10be582430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d430427f6510c109f994430427d6510c109f194430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810af99252042bd6494810dbd4a520427e6494810cf992520423e64948109f592520433d64948108f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433f54d0810cf953420433d54d0810cf153420433f65d0810cf997420433d65d0810cf197420433f53d0810cf94f420433d53d0810cf14f420433f52d0810cf94b420433d52d0810cf14b420427f65908109f996420427d65908109f19642042bd6490810db94a420436d52908109fd95420427e65508109f595420427c6550810cfd51420433e5450810cf551420433c5450810db949420436d5250810bdd8542042f46150810bed8142042f86050810cfd95420433e6550810cf595420433c6550810cfd4d420433e5350810cf54d420433c5350810ebd89420433f5250810cf94942043ae5250810cb949420433d5250810eb549420432d5250810cf14942043b76150810ed18542043bb6050810ee181420427f65108109f994420427d65108109f19442042be64108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f596320427c658c810af99232042bd648c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bed8132042f8604c8109fd94320427e650c8109f59
  | 2 => 0x53cc110be58b304437a52cc110de14b30443bb42cc110ee50b30443db32cc110f64cb30442fa61cc110fc98730442f261cc110fc58730443f221cc110fc487304427e658c110cfd52304433c548c110d794e304435d538c110be982304427d654c110cfd51304433c544c110d7d4d304435c534c110bdd8530442f4614c1109f994304433f540c110cf150304435e530c110f64c030442fa650c110de99430442fb640c110be59030443bb540c110ee15030442fa630c110f698c304437b530c110f694c3044379530c110f654c3044359530c110be588304437a520c110de14830443bb420c110ee50830443da320c110f60c830442fa610c110f6cc430443d9310c110fc88430443f1210c1109f99720442be64c8110af593204433f54c8110cf153204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c5488110be996204437a6588110bed9220442f96488110eed5220443b85488110be98e20442f86388110ded4e20443795388110be58a204437a5288110de14a20443bb4288110ee50a20443f36188110be98620443f06188110fc88620443f121881109fd95204427d65481109f195204433f5448110cf15120442df6348110b718d204436f5248110db14920442f76148110bd18520442f86548110de19520442786548110bed9120442f96448110eed5120443b85448110f6d8d20442fa6348110be18d20443d86348110b618d204437b5348110de54d20443eb6248110fad49204437a5248110de14920443e85248110eed0920443b94248110fcd8520442f86148110fc18520443f22148110fc485204427e6508110af99020442bd6408110cfd50204433c5408110b798c20442dd6308110bd98420442f56108110be980204433f54c4110cf15310442de63c4110b758f10442fb64c4110be59310443bb54c4110ee15310442fa63c4110f698f10442da63c4110f658f10442fb62c4110be58b10443bb42c4110ee50b10443f221c4110fc487104433f5484110cf15210443b75484110ed15210442f76284110bd58a10443b74284110ed50a10443f35084110fc90210443f14084110fccc210443f03084110fc88210443f120841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109e980540
  | 3 => 0x9109f997324427d65cc9109f197324433f54cc910cf153324435e53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910af99232442bd648c910cfd52324433c548c910d7d4e324435c538c910bd98632442f5618c910be98232442f9608c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d794d32442fb604c910be181324427f650c9109f994324427d650c9109f19432442be640c910af590324433f540c910cf150324435f530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414433f5490510cf152414427c6550510cfd51414433c5450510bed8141442f860505109f994414433f5410510cf15041442de6310510b758c41442ee6210510bb58841443b54110510be980414427e65cc510cfd53314433c54cc510d7d4f314435c53cc510be98331442f960cc510cfd52314433c548c510be982314427c654c510cfd51314433c544c510bed8131442f8604c5109f99721442be64c8510af593214433f54c8510cf153214436f52c8510db14b21443ad42c8510be98321442f960c85109f996214433f5488510cf15221442f66588510dd99621443b75488510ed15221443775388510dd54e21442f56288510dd94a21443745288510edd0a21443b54288510fcd8221442f66088510fc182214427c6548510cfd51214433c5448510dbd49214436c5248510eb50921442fb6048510be181214437465485109d19521443b75448510ed15121443775348510dd54d21443e76248510f9d4921443765248510dd14921443e45248510edd0921443e64248510ed50921443e54248510e950921443f36048510bd18121443f060485109f99421442be6408510af590214433f5408510cf15021442de6308510b758c21442f66108510be980214427e65d0110cfd53404433c54d0110bd98740442f561d01109f996404433f5490110cf15240442fa6590110de99640442f96490110eed52404437a5490110de15240443b85490110ce15240442fa6390110be58a40443bb4290110ee50a40442fa6190110ee90640443b84190110fc88640443f121901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540442f86550110de19540442786550110eed9140443bb5450110de95140443785450110ee15140442f86350110bed8940443bb4250110ee50940443f36150110be18540443f06150110bc18540443f22150110fc485404427e6510110cfd50404433c5410110be980404433f54cc110cf153304435f53cc110d714f30442f661cc110bd58730442fa65cc110de99730442fb64cc110be59330443bb54cc110ee153304437b53cc110f6d4f30443d8
  | 4 => 0xf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427c6014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10be98343442f960d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10bdd8543442f46150d10bed8143442f86050d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10bd98443442f56110d10be98043442f96010d10cfd53524433c54d4910cfd93524427e64d49109f593524433c64d49109f98f524427d63d4910af99252442bd6494910cfd52524433c5494910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910cfd51524433c5454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910af99052442bd6414910cfd50524433c5414910b798c52442dd6314910db548524427e6414910cf990524423e64149109f590524433d64149108f590524427e6314910d798c524425e63149109f58c524435d63149109758c524436e62149109f984524437561149109f184524427e6014910de580524427c60149109fd97424427e65d09109f597424427c65d0910cfd53424433e54d0910cf553424433c54d0910be98342442f960d0910cfd9742442be65d0910cf997424423e65d0910cf59742442bc65d0910cf197424423c65d0910cfd4f424433e53d0910cf54f424433c53d0910cfd4b424433e52d0910cf54b424433c52d0910ee98342443b960d09109fd96424427e65909109f596424427c6590910af592424433f5490910cf15242442f66190910bd58642442fa6090910be582424427f65509109f995424427d65509109f195424433f5450910cf951424433d5450910cf151424433f6550910af995424433e65509108f995424433d6550910af195424433c65509108f195424433f5350910cf94d424433d5350910cf14d42443af6250910cfd49424433e5250910cf549424433c5250910ee98142443b960509109fd94424427e65109109f594424427c6510910af990424433f5410910cf15042442f66110910bd58442442fa6010910be580424427f65cc
  | 5 => 0x40843bb4250210ee50940842f86150210cf950408433d5410210bd98440842f56110210be597308437965cc210bed9330842f964cc210de54f30842f962cc210de94b308437852cc210eed0b30843b942cc210f6ccb30843d932cc210be987308435e538c210d754e30842f6618c210bd586308435e530c210d754c30842f6610c210bd58430843d9300c210be5943084379650c210bed9030842f9640c210f698c30843da530c210de54c30843d9530c210d654c30842f9620c210de9483084378520c210eed0830843b9420c210f68c830843d8320c210be98430843f2610c210fc58430843db310c210af99320842bd64c8210db94a208436d5288210bd98620842f56188210be59620843796588210bed9220842f96488210be98e20842f86388210de54e208437a5288210fa94a20843e95288210de14a20843bb4288210ee50a20842fa6188210fc98620843f16188210b7d8d20842dc6348210bed95208437b6548210bed9120842f96448210f6d8d20842fa6348210be18d20843d86348210b618d20843795348210fad89208437a5248210de14920843bb4248210ee50920842f86148210af99020842bd6408210b798c20842dd6308210db948208436d5208210bd98420842f56108210b798f10842dd63c4210bd597108437565c4210f598f10843d563c4210ddd4b108437552c4210edd0b10843b542c4210be597108437965c4210bed9310842f964c4210be98f10843da63c4210b698f10843d963c4210bed8b10842f962c4210eed0b10843b942c42109f98f544427d63d51109f98b544427d62d5110af58b54443bb60d5110cfd8f544433e63d5110cf58f544433c63d5110cfd8b544433e62d5110cf58b544423d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f54951109f992544423e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110cfd91544427f63551109f18d544427f62551109f189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544437960151109f18054442be6515110cf994544423e6515110af58854443b96015110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544423d6215110cf188544433f6115110cf584544433f6015110cf58054443396015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534437960d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6294d109f58a53443756194d10de58253442bf6454d10af191534433f5454d10c
  | 6 => 0x33e5490e10cf55243842f66190e10bd586438427f6550e109f595438427c6550e10bed8143842f86050e109fd94438427e6510e109f594438427c6510e10cf950438433d5410e10d794c438435d5310e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10af99252842bd6494a10dbd4a528427e6494a10cf992528423e6494a109f592528433d6494a108f592528427e6394a109f58e528437a6094a109fd91528427c6454a109fd8d528427c6354a10dbd8952842be6414a10af59052842de6314a10b758c528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433f54d0a10cf953428433d54d0a10cf15342842fa60d0a10be583428433f65d0a10cf997428433d65d0a10cf197428433e53d0a10cf54f428433c53d0a10cfd4b428433e52d0a10cf54b428433c52d0a10ee98342843b960d0a109fd96428427e6590a109f596428427c6590a10be98242842f96090a109fd95428427e6550a109f595428427c6550a10cfd51428433e5450a10cf551428433c5450a10bdd8542842f46150a10cfd95428433e6550a10cf595428433c6550a10cf94d428433d5350a10cf14d42843af6250a10cfd49428433e5250a10cf549428433c5250a10edd8542843b46150a10ee98142843b96050a109fd94428427e6510a109f594428427c6510a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca109fd96328427e658ca109f59632842be648ca10af59232842fa608ca10be582328427f654ca109f595328427c654ca10d794d328435d534ca10bed8132842f8604ca109fd94328427e650ca109f594328427c650ca10af99032842bd640ca10bd98432842f5610ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610b798c41842dd6310610bb98841842ed6210610be58041842fa60cc610be58331842f9608c610af99321842bd64c8610db94b218436d52c8610eb50b21842fa60c8610be583218436e5248610db54921843ad4248610bed8121842f86048610af99021842bd6408610b798c21842dd6308610be580218433e5490210cf55240842f66190210bd58640842f96590210de596408437a5490210ee95240843b95490210de15240842fa6390210be58a40843bb4290210ee50a40842fa6190210fc98640843f16190210ee90640843b84190210bed95408437b6550210eed91408437a5450210de15140842f86350210bed89
  | 7 => 0x18cb109fd9532c427e654cb109f59532c427c654cb10d794d32c435d534cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c42be640cb10af59032c435e530cb10d754c32c42f6610cb10bd58432c42fa600cb10be58032c435e53d0710d754f41c433e5490710cf55241c435e5390710d754e41c42fa6090710be58241c435e5350710d754d41c433e5410710cf55041c42de6310710b758c41c435e5310710d754c41c42ee6210710bb58841c43b54110710be98041c42f96010710be98231c42f9608c710af99321c42bd64c8710d794f21c435d53c8710eb50b21c435e5388710d754e21c436e5288710db54a21c42fa6088710be58221c43756588710ddd4e21c43d65388710dd54e21c43d55388710d554e21c43765288710f994a21c43e55288710dd14a21c43b74288710ed50a21c42f66088710fc98221c43f16088710d794d21c435d5348710eb50921c42f76548710ddd9521c43775348710f594d21c43755348710f554d21c43555348710f9d8921c43765248710dd14921c43b74248710f990921c43b54248710f950921c43a54248710bd18121c42be6408710af59021c42de6308710b758c21c435e5308710d754c21c436e5208710db54821c42fa6008710be58021c433e54d0310cf55340c435e53d0310d754f40c42f661d0310bd58740c433f5490310cf15240c435e5390310d754e40c433e5450310cf55140c435e5350310d754d40c42f76150310bd18540c433f5410310cf15040c435e5310310d754c40c435e53cc310d754f30c42f661cc310bd58730c435e538c310d794d30c435d534c310bdd8530c42f4614c310d754c30c43d9300c310af99320c42bd64c8310d794f20c435d53c8310db94b20c436d52c8310bd98720c42f561c8310d794e20c435d5388310b7d8d20c42dc6348310d794d20c435d5348310db94920c436d5248310bdd8520c42f46148310af99020c42bd6408310b798c20c42dd6308310d794c20c435d5308310bd98420c42f56108310b798f54842dd63d52109f98f548435e63d52109798f548427d63d5210d758f548425d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548437a6095210cfd91548427f63552109f18d548427f62552109f189548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de98054842be64d4e10af593538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e109fd89538427c6254e10de181538435d5314e109f990538427d6414e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438435e53d0e10d754f43842fa60d0e10be583438427f6590e109f996438427d6590e109f1964384
  | 8 => 0x10d7d5253c435e5494f10d755253c435c5494f10d7d9253c435e6494f10d759253c435c6494f10d7d8a53c435e6294f10d758a53c435c6294f10d798653c435c6194f10d7d8253c427f6454f109f19153c435f6354f109fd8953c427c6254f10d7d9553c435f5454f10d795153c435d5454f10d715153c435f6454f10d799153c435d6454f10d719153c435f6254f10d798953c435d6254f10d718953c435e6154f10d718553c435d6054f10d754c53c427f65d0f109f99743c427d65d0f109f19743c435e53d0f10d754f43c427f6590f109f99643c427d6590f10d794e43c435d5390f10be98243c42f96090f109fd9543c427e6550f109f59543c427c6550f10d794d43c435d5350f10bdd8543c42f46150f109fd9443c427e6510f109f59443c435e5310f10d754c43c42f66110f10bd58443c42de63d4b10b758f52c435e53d4b10d754f52c427e64d4b109f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c42be6494b10af59252c435e5394b10d754e52c436f5294b109f99252c433e6494b108f99252c427d6494b10cf59252c423d6494b109f98e52c427d6394b10dd98652c435e5354b10d754d52c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10b798c52c42dd6314b10d794c52c435d5314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cfd5342c433e54d0b10cf55342c433c54d0b10d794f42c435d53d0b10cfd9742c433e65d0b10cf59742c433c65d0b10cfd4f42c433e53d0b10e794f42c431e53d0b10cf54f42c439d53d0b10c754f42c433f52d0b10cf94b42c433d52d0b10cf14b42c427f6590b109f99642c427d6590b109f19642c435e5390b10d754e42c436e5290b10db54a42c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c433f5450b10cf95142c433d5450b10cf15142c435e5350b10d754d42c436e5250b10db54942c42fb6050b10be18142c433f6550b10cf99542c433d6550b10cf19542c433f5350b10cf94d42c439e5350b10c794d42c433d5350b10e754d42c431d5350b10ebd8942c433f5250b10cf94942c43ae5250b10cb94942c433d5250b10eb54942c432d5250b10cf14942c43bb6050b10ee18142c427f6510b109f99442c427d6510b109f19442c435e5310b10d754c42c42f66110b10bd58442c427f65ccb109f99732c427d65ccb10d794f32c435d53ccb109fd9632c427e658cb109f59632c427c658cb10af99232c42bd648cb10d794e32c435d538cb10bd98632c42f56
  | 9 => 0x50b30083db32cc020f64cb30083f251cc020de54730083f151cc020dc547300827f658c0209f596300833e548c020cf552300835e538c020d754e30082ee628c020bb58a3008376518c020dd54630082fa608c020de942300827f654c020cf951300833d544c020d794d300835d534c020dd9453008375514c020de941300827f650c0209f994300827d650c0209f194300833e540c020cf550300835e530c020d754c30082ee620c020bb5883008376510c020dd54430083d9300c020be5943008379650c0209e59430083ba540c020ee55030082fa630c020f698c300837b530c020f694c3008379530c020f654c3008359530c020fa98830082f9620c020fa588300837a520c020eed0830083b9420c020f68c830083d8320c020fc9443008379510c020fc5443008371510c020af99320082bd64c8020cf953200833d54c8020d794f200835d53c8020ebd0b20083ad42c8020dd947200837551c8020eb99320083ad64c8020eb95320083ad54c8020f394f20083cd53c8020f994720083e551c8020facc320083e830c8020cf952200833d5488020d794e200835d5388020bb58a200836e5288020dd94620083755188020ee95220083b95488020be98e20082f86388020ded4e20083da5388020de54e20083d95388020d654e20082f96288020de94a20083ea5288020eed0a20083b94288020fc94620083795188020fc546200837151880209fd95200833e5448020cf55120082df6348020b718d200835e5348020d754d20083af4248020eb50920083765148020dd54520082ef6548020dbd95200826f6548020eb95120083ad5448020f3d8d20083cc6348020f394d20083cd5348020f994520083e55148020bbd81200836e5048020fa90120083e94048020bed95200837b65480209ed9520083ba5448020ee55120083db6348020be98d20082f86348020f618d20082d86348020ded4d20083da5348020de54d20083d95348020d654d20082fb6248020fad89200837a5248020fa94920083bb4248020fa90920083b94248020fa50920083a94248020fc94520083795148020fc54520083715148020b798f54c42dd63d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c42de6315310b758c54c42ee6215310bb58854c433e64153109f98c54c435e63153109798c54c427d6315310d758c54c425d63153109f98854c436e62153109b98854c427d6215310db58854c426d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c435f5394f109f99253c427d6494f109f98a53c427d6294f
  | 10 => 0x1083754294420cd50a51083744294420ddcca51083763294420dd4ca51083743294420dd98251083746094420cf951510833d5454420d794d510835d53544209fd91510827c64544209fd8d510827c6354420cfd09510833d4254420ddd9551083775454420dd95151083b65454420cd95151083755454420ed55151083355454420dd15151083775354420dd94d51083d65354420d594d51083755354420f554d51083555354420dd14d51083b74254420ed50951083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083774354420dd90d51083754354420dd10d51083766254420ddd0951083374254420dd90951083754254420cd50951083744254420ddcc951083763254420dd4c951083743254420dd98151083746054420dd08151082be6414420af590510833e5414420cf55051082de6314420b758c510835e5314420d754c51082f66114420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d0420dd947410837551d04209fd96410827e65904209f596410833e5490420cf552410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420d794d410835d5350420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410833e5410420cf55041082de6310420b758c410835e5310420d754c41082ee6210420bb58841083765110420dd54441082fa6010420be58041082be64c8420af593210833e54c8420cf553210835e53c8420d754f21083ad42c8420dd947210837551c8420be98321082f960c84209f596210833e5488420cf552210835e5388420d754e210837551884209fd95210833e5448420cf551210835e5348420d754d21083ad4248420dd94521082be6408420af590210833e5408420cf55021082de6308420b758c210835e5308420d754c21083765108420dd54421082fa6008420be580210827e64940209f592500827d6394020cfd0a500833d42940209f597400833e54d0020cf553400835e53d0020d754f400837651d0020dd547400827f65900209f596400833e5490020cf552400835e5390020d754e40082ee6290020bb58a40083765190020dd546400827f6550020cf951400833d5450020d794d400835d5350020dd945400837551500209fd94400827e65100209f594400827c6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020dd944400837551100209f597300833e54cc020cf553300835e53cc020d754f300837651cc020dd54730082f965cc020de597300827965cc020ee95330083b954cc020ded4f30083da53cc020de54f30083d953cc020d654f30082f962cc020de94b30083bb42cc020ee
  | 11 => 0x5e6154c20d7585530835c6154c20d7981530835c6054c20d6181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209e980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430835e53d0c20d754f43082ee62d0c20bb58b43082fa60d0c20be583430827f6590c209f996430827d6590c209f196430833e5490c20cf552430835e5390c20d754e430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d43082fb6050c20be181430827f6510c209f994430827d6510c209f194430833e5410c20cf550430835e5310c20d754c430827e6494820cf992520823e64948209f592520833d64948208f592520827e63948209f58e520827d65d0820cfd53420833e54d0820cf553420833c54d0820d794f420835d53d0820af597420833d65d08208f597420833f53d0820cf94f420839e53d0820c794f420833d53d0820e754f420831d53d0820cf14f420833e52d08209fd96420827d6590820af592420833e5490820cf552420835e5390820d754e42082fa6090820be582420827f6550820cfd51420833e5450820cf551420833c5450820d794d420835d5350820afd95420833f65508208fd95420833f5350820cf94d420839e5350820c794d420833d5350820e754d420831d5350820cf14d42083af6250820cf949420827f65108209f59442082be6410820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f32083ad42cc8209fd96320827d658c820af99232082bd648c820cf952320833d548c820d794e320835d538c820be98232082f9608c8209fd95320833e544c820cf551320835e534c820d754d32082fb604c8209f594320833e540c820cf55032083ad420c820be98032082f9600c820af99351082bd64d4420cf953510833d54d4420b798f51082dd63d4420d794f510835d53d4420cf952510833d5494420d794e510835d5394420ddd46510827e64944209f592510827e63944209f58e510833f4294420cf50a51083775494420dd95251083b65494420cd95251083755494420ed55251083355494420dd15251083775394420dd94e51083d65394420d594e51083755394420f554e51083555394420dd14e51083b74294420ed50a51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083774394420dd90e51083754394420dd10e51083746294420ddd0a51083374294420dd90a5
  | 12 => 0x8c120be98a30483bb428c120ee50a30483da328c120be586304827d654c120d7d4d304835c534c120bbd8930482ec624c120f6d8d30483db534c120de94d3048378534c120f614d3048358534c120fad8930482f8624c120fa18930483bb424c120ee50930483db324c120f64c930482fb614c1209f994304835f530c120be98030483d9300c120af99320482bd64c8120d7d4f204835c53c8120ee99320483b964c8120bed8f20482f963c8120f6d4f204837a53c8120de14f20483d853c8120d614f20483bb42c8120ee50b20482f961c8120d7d4e204835c5388120ebd0a20483ad4288120f3d4e20483cc5388120fad4220483ea3088120fa4c220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020cfd8e540833e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833f6555020cfd8d540833e6355020cf58d540833c63550208fd89540833e62550208f589540833c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540823e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c20db98b530827e61d4c20dd987530827661d4c209f587530837561d4c209d587530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d715253083d86094c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c20cf951530833d5454c209fd91530827c6454c20d7d8d530827f6154c209f18553083786054c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d715153083d86054c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d7d8553083
  | 13 => 0xbe582434827f6550d209f995434827d6550d209f195434835f5350d20d714d434827f6510d209f994434827d6510d209f194434835f5310d20d714c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920d7d4f424835c53d0920be98342482f960d0920cfd97424833e65d0920cf597424833c65d0920cfd4f424839f53d0920c7d4f424833e53d0920cf54f424833c53d0920e714f424831c53d0920ee98342483b960d09209f99642482bd6490920d7d4e424835c53909209f195424833f5450920cf151424835f5350920d714d42482fb6050920be181424833f6550920cf995424833d6550920cf195424833f5350920e7d4d424831f5350920cf94d424833d5350920cf14d424839c5350920c714d42483af6250920eed8142483b860509209f99442482be6410920d7d4c424835c53109209f997324835f53cc920d714f32482fa60cc920be58332482be648c920af592324835f538c920d714e32483ad428c9209f19532483ad424c920bed8132482f8604c920d7d4f514835c53d45209f993514827d64d45209f98f514827d63d4520cfd0b514833d42d4520b798e51482dd6394520d7d4e514835c5394520ddd4651482bf6454520af19151482df6354520b718d514835f5354520d714d514835f5314520d714c514837551145209f990514827d64145209f98c514827d6314520cfd08514833d4214520de580514827e65d05209f597414827c65d0520d7d4f414835c53d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e41482fa6090520be582414827f65505209f995414827c6550520d7d4d414835c53505209f994414827d65105209f194414833f5410520cf15041482de6310520b758c414835f5310520d714c41482ee6210520bb58841483775110520dd14441482fa6010520be580414827e65c8520af99321482bd64c8520d7d4f214835c53c8520eb50b214835f5388520d714e21483775188520dd14621482fa6088520be582214835f5348520d714d21483ad4248520ddd4521483745148520bed8121482f860485209f99421482be6408520af59021482de6308520b758c214835f5308520d714c21482fa60085209f997404833f54d0120cf153404835f53d0120d714f40482ee62d0120bb58b404827e6590120cf952404833d5490120d7d4e404835c53901209fd95404827d65501209f195404833f5450120cf151404835f5350120d714d40482ef6250120bb189404827e6510120cf950404833d5410120d7d4c404835c5310120d7d4f304835c53cc120bb98b30482ed62cc1209f996304835f538c120d714e30482fa658c120de996304827a658c120be58e30483db538c120de94e3048378538c120f614e304835853
  | 14 => 0x94418827d6510620cfd50418833c5410620b798c41882dd6310620bb98841882ed6210620be98041882f96010620af99321882bd64c8620eb50b21883765188620dd54621882fa6088620be58221883ad4248620dd94521883755148620bed8121882f86048620af99021882bd6408620b798c21882dd6308620be580218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882ee6210220bb588408835e538c220d754e30882ee628c220bb58a308837a538c220f694e30883d9538c220de14e30882fa628c220fa98a30883e9628c220eed0a30883b9428c220f68ca30882f9618c220bed95308837b654c220f6d8d30883db534c220de94d3088378534c220f614d3088358534c220be18930883bb424c220ee50930883db324c220bed85308835e530c220d754c30882ee620c220bb58830883d9300c220af99320882bd64c8220ebd0b20883ad42c8220bb597208836d65c8220eb99320883ad64c8220be597208837965c8220ee99320883b964c8220bed8f20882f963c8220de94f208837853c8220eed0b20883b942c8220be587208827e63d51209f58f544827e61d51209f587544833f5495120b798e54482dd63951209f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f54d4d20d7953534835d54d4d20d715353483db60d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20d7d4e534827e6494d209f592534836d6294d209f986534827d6194d20de582534827f6454d209f191534827f6254d20dbd89534827f6154d209f185534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6114d209f58453482de6514d20d7994534825e6514d20d7d50534835e5414d20d7550534835c5414d20f6580534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534835f6114d20d7984534835d6114d20d7184534835f6014d20d7480534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434835f5390d20d714e43482fa6090d2
  | 15 => 0xc82de6310720b758c41c82ee6210720bb58841c82fa6010720be58041c82be64c8720af59321c833e54c8720cf55321c83ad42c8720dd94721c837551c8720be98321c82f960c8720cf95221c833d5488720cf95121c833d5448720eb50921c82be6408720af59021c833e5408720cf55021c82de6308720b758c21c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c833e5490320cf55240c833e5450320cf55140c82ef6250320bb18940c833e5410320cf55040c833e54cc320cf55330c835e53cc320d754f30c82ee62cc320bb58b30c83ba54cc320ee55330c83da53cc320de54f30c83d953cc320fa98b30c82f962cc320fa58b30c83bb42cc320ee50b30c837951cc320cf95230c833d548c320d7d4e30c833e544c320cf55130c835e534c320d754d30c82ef624c320bb18930c833e540c320cf55030c83d9300c320be59430c8379650c320ee95030c83b9540c320f698c30c837b530c320f6d4c30c835b530c320de54c30c83d8530c320be58830c83bb420c320ee50830c83da320c320de54430c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de980548835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e209fd85538827c6154e20d754c538827e6414e209f590538836d6214e209f984538827d6114e20de980538827f65d0e209f997438827d65d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438827c6590e20be98243882f96090e209fd95438827d6550e209f195438827f6510e209f994438827d6510e209f19443882fa6010e20be580438833e54d0a20cf55342882fa60d0a20be583428833e65d0a20cf597428833e53d0a20cf54f428833c53d0a20ee98342883b960d0a20cf951428833d5450a20bed8142882f86050a20cfd95428833c6550a20cf94d428833d5350a20cf14d42883af6250a20eed8142883b86050a20eb50b32882fa60cca20be58332882be648ca20af59232882de6394620b758e518837751946209f992518827d64946209f98e518835e63946209798e518827d6394620d758e518825d6394620cfd0a518833d4294620de98251882bf6454620af191518827f6454620cfd91518823f64546209f191518833c64546208f191518827f63546209f18d518833f4254620cf509518837551146209fd97418827e65d06209f597418827f65906209f996418827d6590620cfd52418833c5490620be98241882f960906209fd95418827d65506209f195418827f65106209f9
  | 16 => 0xb424c030e6d09300c3da424c030f6509300c399424c030f6109300c3db614c030b6d85300c3da614c030f6585300c3d8614c030f6d45300c3da514c030f6545300c3d8514c030f6d05300c3da414c030f6505300c3d8414c030f6c85300c3da214c030f6485300c3d8214c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f6395320cf98e54c833d6395320cf18e54c833e6295320cf18a54c833f6195320cf98654c833d6195320cf18654c833f6095320cf58254c833f64553209fd8d54c827c63553209fd8554c827c6155320cfd9554c833f6355320cf98d54c833d6355320cf18d54c833e6255320cf18954c833f6155320cf98554c833d6155320cf18554c833f6055320cf58154c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c82be64d4f20af59353c833e54d4f20cf55353c827e64d4f20cf99353c823e64d4f209f59353c833d64d4f208f59353c836e62d4f209f98753c827d61d4f20cf95253c833d5494f20d7d4e53c827e6494f209f59253c827e6194f209f58653c833e5454f20cf55153c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20cf95053c833d5414f20d754c53c82f66114f20bd58453c827f65d0f209f99743c827d65d0f209f19743c833e54d0f20cf55343c82fa60d0f20be58343c827f6590f209f99643c827d6590f20cf95243c833d5490f209fd9543c827e6550f209f59543c827c6550f20cf95143c833d5450f20bed8143c82f86050f209fd9443c827e6510f209f59443c833e5410f20cf55043c82ee6210f20bb58843c833f54d0b20cf95342c833d54d0b20cf15342c82bd65d0b20cf59742c833f53d0b20cf94f42c833d53d0b20cf95242c833d5490b20be98242c82f96090b20cfd5142c833e5450b20cf55142c833c5450b20afd9542c833f6550b20cfd4d42c833e5350b20cf54d42c83af6250b20cf95042c833d5410b20be98042c82f96010b20cf95232c833d548cb20eb50a32c82fa608cb20be58232c82be64d4720af59351c833e54d4720cf55351c833e5494720cf55251c837751947209f99251c827d64947209f98e51c827d6394720cfd0a51c833d4294720cf95151c833d54547209fd9151c827c64547209fd8d51c827c6354720cfd0951c833d4254720af99051c82bd6414720cf95051c833d5414720b798c51c82dd6314720dd54451c827f65d07209f99741c827d65d0720cf95341c833d54d07209fd9641c827e65907209f59641c833e5490720cf55241c827f65507209f59541c827c6550720cf95141c833d5450720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041
  | 17 => 0x48308f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33f54d0830cf953420c33d54d0830cf153420c2fa60d0830be583420c33f65d0830cf997420c33d65d0830cf197420c33e52d0830cf54b420c3ba60d0830ee583420c27f65908309f996420c27d6590830af592420c36e5290830db54a420c27f65508309f595420c27c6550830cfd51420c33e5450830cf551420c33c5450830db949420c36d5250830bed81420c2f86050830cfd95420c33e6550830cf595420c33c6550830ebd89420c33e5250830eb949420c32e5250830cf549420c3ad5250830cb549420c3bb6050830ee181420c27f65108309f994420c27d6510830af990420c37751944309f992510c27d64944309f98a510c27d6294430cfd0a510c33d4294430afd91510c2bc64544309fd91510c33f64544308fd91510c27c6454430cf191510c23c64544309fd89510c27c6254430cfd09510c33d4254430af990510c2bd6414430bb988510c2ed6214430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d04309fd96410c27e65904309f596410c33f5490430cf152410c3765190430dd546410c2fa6090430be582410c27f65504309f595410c27c6550430cf951410c33d5450430dd945410c37551504309fd94410c27e65104309f594410c33f5410430cf150410c2ee6210430bb588410c2fa6010430be580410c27f65c84309f997210c27d65c8430af993210c2bd64c8430db94b210c36d52c8430eb50b210c27f65884309f996210c27d6588430dd946210c3755188430be982210c2f960884309fd95210c27d65484309f195210c36e5248430db549210c3ad4248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c2be6408430af590210c2fa6008430be580210c27e64940309f592500c33f4294030cf50a500c27d65d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd63900309fd95400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c2f9638c030b658e300c37a538c030f694e300c2fa628c030de54a300c3bb428c030ee50a300c2f9618c0309fd95300c2fb654c030ded95300c27b654c030bed8d300c37a534c030f694d300c3db434c030f690d300c3d9434c030f610d300c2f8624c030de549300c3bb424c030ee509300c2fb614c030f6d95300c2db654c030d6d95300c3db644c030f6991300c3d9644c030f6191300c3db544c030f6951300c3d9544c030f6151300c3db624c030f6989300c3d9624c030f6189300c2d8624c030f6d49300c3da524c030f6549300c359524c030f6149300c3d
  | 18 => 0x9f189544c27f61551309f185544c27f6055130ded81544c27e6515130cf550544c33e64151309f988544c27d62151309f984544c27d61151309f993524c27d64d49309f987524c27d61d4930af992524c2bd6494930dbd4a524c2be6414930af590524c36d5214930bd984524c2f561149309f990524c33e64149308f990524c27d6414930cf590524c23d64149309f984524c37661149309d984524c27d6114930dd584524c27561149309f997424c27d65d09309f197424c33f54d0930cf953424c33d54d0930cf153424c33f65d0930cf997424c33d65d0930cf197424c33f52d0930cf14b424c27e65909309f596424c27c6590930af592424c36f5290930db14a424c2fa6090930be582424c27f65509309f995424c27c6550930cfd51424c33e5450930cf551424c33c5450930dbd49424c36c5250930cfd95424c33e6550930cf595424c33c6550930ebd89424c33f5250930ebd49424c32f5250930cf149424c3ac5250930cb149424c27e65109309f594424c27c6510930af990424c2fa6010930be580424c27e64d45309f593514c27e62d45309f58b514c33f42d4530cf50b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c33f4214530cf508514c27e65d05309f597414c27c65d05309f996414c27d65905309f196414c33f5490530cf152414c27f65505309f995414c27c6550530bed81414c2f860505309f994414c27d65105309f194414c33f5410530cf150414c2ee6210530bb588414c2fa6010530be580414c27e65c85309f597214c27c65c8530af993214c2bd64c8530eb50b214c2fa60c8530be583214c27e65885309f596214c27c6588530dbd4a214c36c52885309fd95214c27e65485309f195214c3ad42485309f994214c27d65085309f194214c2be6408530af590214c36f5208530db148214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc63501309f994404c3b94010130b758a304c35c528c130e7d0a304c39d428c130d7d46304c3db508c1309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d6195030cfd91540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a6015030af992520c2bd6494830dbd4a520c27e6494830cf992520c23e64948309f592520c33d649
  | 19 => 0x7548c35d63d52309f98b548c27d62d52309f987548c37661d52309d987548c27d61d5230dd587548c27561d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e5450e30cf551438c2fb6050e30be181438c2be6494a30af592528c36f5294a309f992528c33e6494a308f992528c27d6494a30cf592528c23d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30af990528c2bd6414a30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cfd53428c33e54d0a30cf553428c33c54d0a30b798f428c2dd63d0a30cfd97428c33e65d0a30cf597428c33c65d0a30e798f428c39d63d0a30cf94b428c33d52d0a309fd96428c27e6590a309f596428c2fa6090a30be582428c27f6550a309f595428c27c6550a30cfd51428c33e5450a30cf551428c33c5450a30b7d8d428c2dc6350a30cfd95428c33e6550a30cf595428c33c6550a30e7d8d428c39c6350a30ebd89428c33e5250a30cf549428c27f6510a309f994428c27d6510a30be980428c2f96010a30af993518c2bd64d4630ddd46518c27e64946309f592518c27e62946309f58a518c33f4294630cf50a518c27f64546309f191518c27f62546309f189518c33f4254630cf509518c37551146309fd97418c27e65d06309f597418c37651d0630dd547418c27f65906309f996418c27d6590630cf952418c33d5490630b798e418c2dd63906309fd95418c27d65506309f195418c2fb6050630be181418c27f65106309f994418c27d6510630cf950418c33d5410630b798c418c2dd6310630bb988418c2ed6210630dd944418c3755110630be980418c2f960106309fd97218c27e65c86309f597218c2be64c8630af593218c3ad42c8630be983218c2f960c86309fd96218c27e65886309f596218c2de6388630b758e218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630eb509218c3765148630dd545218c27f65086309f994218c27d6508630af990218c2bd6408630b798c218c2dd6308630be980218c2f96008630cf952408c33d5490230b798e408c2dd6390230cf950408c33d5410230b798c408c2dd6310230ee500408c2f965cc230de597308c2f962cc230de94b308c3bb42cc230ee50b308c37951cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c2ee6295130bb58a544c27e64951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c27d61951309f582544c3796095130cfd91544c27f6255130
  | 20 => 0x2be6408540af59021502de6308540b758c21503775108540dd14421502fa6008540be58021503bb42d0140ee50b40502f961d0140af58a405033f5290140cf14640503bb5090140d7d4e531027e6294c409f58a531027e6194c409f586531027f6254c409f189531027f6154c409f185531035d5314c40bb98853102ed6214c40bd98453102f56114c40d794f431035d53d0c40be98343102f960d0c409f596431027f6550c40be98043102f96010c40dbd4a521027e63948409f58e521027e61948409f586521033e64548409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521033e54d0840db94b421036d52d0840be98342102f960d0840cf94f421033d53d0840cf94b42103ae52d0840cf54b42103ad52d0840cb54b42102be61d0840ee98342102bd60d0840ee583421027d6590840af592421027f6550840cf95142102bf6550840cfd95421033e5350840cf54d42103af6250840cf94942102bc6150840afd8142102be6410840db948421036d5210840be98042102f96010840ddd46511027e63944409f58e511027e62944409f58a511033f4294440cf50a511027f63544409f18d511027f62544409f189511033f4254440cf50951102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d04409f59641102bd6590440cf596411033e5390440af58a411033d5290440af986411033d5190440af582411027f6550440b798c41102dd6310440bb98841102ed6210440dd94441103755110440be98041102f96010440e798c411039d6310440cf94c41103ae6210440af58841103ad6210440ab588411033d5210440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee580411027f65c84409f997211027d65c8440af99321102bd64c8440db94b211036d52c8440eb50b211027f65884409f996211027d6588440afd9221102bc6488440dd946211037551884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103ad4248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102be6408440af59021102de6308440b758c21102fa6008440be580211033f4294040cf50a501033e4194040cf10650102bd62d0040cf54b40102be61d0040af592401033e5490040be592401037a5490040ee95240103bb4290040ee50a40103795190040ee90640103b841900409fd9540102bf6550040cfd95401023f6550040afd89401033d5250040af18540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040eed0d40103b94350040de54540102f661d5230bd58
  | 21 => 0x63d4640b758f51902de6394640b758e519037751946409f98e519035e63946409798e519027d6394640d758e519025d63946409f98a519027d6294640cfd0a519033d4294640de982519027f63546409f18d519027f62546409f189519033f4254640cf50951903755114640dd94641903755190640be98241902f96090640cf94e41902bd6290640cf54a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902de6310640b758c41902ee6210640bb58841902f96010640af594419033d6510640e798c419039d6310640cf94c41903ae6210640af58841903ad6210640ab588419033d5210640ed984419033d5110640ee98041902bd6010640ee58041902b960106409fd97219027e65c86409f59721902be64c8640af59321903ad42c86409fd96219027e65886409f59621902bf6488640af19221903765188640dd54621902fa6088640be582219027f65486409f595219027c6548640afd9121902bc6448640eb50921903765148640dd545219027f65086409f994219027d6508640af99021902bd6408640b798c21902dd6308640be98021902f96008640af597409033d65d0240af58b409033d52d0240af98740902f965d0240de59740902f961d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502f66194d40bd586535035d5314d409f988535027d6214d409f984535027d6114d40d7d4e435035c5390d40be98243502f96090d40bed8143502f86050d40cfd93525027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940af997425033e65d0940cfd4f425033c53d0940cf14b42502be60d0940af592425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be181425033f5350940cf14d42503af6250940cfd4942503af5250940cbd49425033c5250940eb14942503bb6050940af18142503b860509409f99442502be64109409f98f515027d63d45409f98b515027d62d4540cfd0b515033d42d4540b798e51502dd6394540ddd46515037551145409f98c515027d63145409f988515027d6214540cfd08515033d4214540de580515027e65d0540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f860505409f99441502de6310540b758c41502ee6210540bb58841503b54110540be980415027e65c85409f597215027c65c8540af99321502bd64c8540eb50b215037751c8540dd147215027e65885409f596215027c6588540be98221502f960885409fd95215027e65485409f19521503ad42485409f994215027d65085409f194215
  | 22 => 0x21de94d50087da5354021d694d50087795354021f654d50087595354021eed0950087b94254021fac8550087f22154021fa48550087f12154021ded91500877a6454021de59150087786454021ded8d500877a6354021de58d50087786354021de989500877b4254021ced09500877a4254021de50950087394254021de109500877a6154021ded05500877a4154021de50550087784154021dec85500877a2154021dc88550087792154021dc48550087782154021af99050086bd6414021cf950500873d5414021b798c50086dd6314021d794c500875d5314021be98050087795014021bb98b53d02ed62d4f40d7d4e53d027e6294f409f58a53d027e6194f409f58653d027f6254f409f18953d027f6154f409f18553d035d5314f40be98343d02f960d0f40b798f52d02dd63d4b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d033e6454b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d033e53d0b40cf54f42d033e52d0b40eb94b42d033d52d0b40eb54b42d032d52d0b40af98342d03ba60d0b40ee58342d02bf6550b40cfd9542d033e5350b40cf54d42d03af6250b40cf94942d02bc6050b40db94842d036d5210b40be98042d02f96010b40ddd4651d027e63947409f58e51d027e62947409f58a51d033f4294740cf50a51d027f63547409f18d51d027f62547409f18951d033f4254740cf50951d02de6314740b758c51d02ee6214740bb58851d03755114740dd94741d037551d0740be98341d02f960d0740b798c41d02dd6310740bb98841d02ed6210740dd94441d03755110740ed50441d02fa6010740be58041d027f65c87409f99721d027d65c8740af99321d02bd64c8740db94b21d036d52c8740eb50b21d027f65887409f99621d027d65887409fd9521d027d65487409f19521d036e5248740db54921d03ad4248740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d02fa6008740be58021d02f661d4e40bd587539035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c53902fa6090e40be582439036f5294a409f98e529027d6394a409f986529027d6194a40cf591529027f6354a409f18d529027f6154a409f18552902de6314a40b758c529036d5214a40bd98452902f56114a40af597429033d65d0a40cf94f429033d53d0a40cf94b42902be61d0a40af583429036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be181429033e5350a40cf54d42903af6250a40cf94942903ae5250a40cf54942903ad5250a40cb54942902bc6150a40afd8142903bb6050a40ee18142902de
  | 23 => 0xf581540873c6055021af990540873d5415021be98054086f960150219f990540873e64150218f990540867e6215021db988540866e62150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f992520873e64948218f992520867d6494821cf592520863d64948219f597420873f54d0821cf953420873d54d0821cf15342086bd65d0821cf597420863d65d0821cf94b420867f65908219f59642086bd6490821cf952420873d5490821db94a42086f66190821bd586420867f6550821cfd51420873e5450821cf551420873c5450821db94942086bf6550821cfd95420863f6550821ebd89420873e5250821cb949420867f65108219f59442086be6410821cf950420873d5410821bd98442086f561108219f992510867d6494421cfd0a510873d42944219f597410873e54d0421cf553410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f6550421cf951410873d54504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421ed50441086fa6010421be58041086be64c8421af593210873e54c8421cf55321087af42c8421eb50b21087ae64c8421eb593210876f54c8421eb953210876d54c8421eb553210872d54c8421cf952210873d5488421bb58a210876e5288421ed95221087b55488421bd58a21087765288421f994a21087b74288421ed50a210867f6548421cf951210873d5448421ebd0921087ad4248421bbd95210876f65484219bd95210876f5448421eb951210876d5448421eb551210872d5448421bbd85210876e5148421bdd95210877765484219dd9521087b65448421ed55121086f76248421f9d8921087765248421f994921087b74248421ed50921086be64d4021af593500873e54d4021cf55350086de63d4021b758f500873e5494021cf552500877b50940219f992500867d64940219f98e500867d6394021cfd0a500873d4294021ded52500877a5494021ee952500873a5494021de55250087b95494021ce55250087785494021ded4e500877a5394021f694e500875a5394021eed0a50087b94294021fac8650087f22194021fa48650087f12194021ded92500877a6494021de59250087786494021ded8e500877a6394021de58e50087786394021de18a500877b4294021ced0a500877a4294021de50a50087394294021de10a50087786194021ded06500877a4194021de50650087784194021dec86500877a2194021de486500873e5454021cf551500875e53540219fd91500867c64540219fd8d500867c6354021cfd09500873d4254021dd88550087752154021ded95500877b5454021de95150087ba5454021ce95150087795454021ee55150087395454021de151500877b5354
  | 24 => 0x21887b564c8621edd0b21887b542c8621bd58321886de63d4221b758f508877b50942219f992508867d64942219f98e508867d6394221cfd0a508873d4294221afd9150886bc64542219fd91508873f64542218fd91508867c6454221cf191508863c64542219fd8d508867c6354221cfd09508873d4254221de540508867e60d51219f583544873f54951219f992544867d6295121db58a544867d6195121dd586544867e60951219f58254486fb6055121be181544873f64551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544876d62151219f980544867d60151219f997424873f54d0921cf15342486f661d0921bd587424873f65d0921cf997424873d65d0921cf19742487b661d0921ed587424867e6590921af59242486ee6590921db99642486ed6490921ab592424876e5490921db15242486ee61909219f195424873f5450921cf15142486f76150921bd185424873f6550921cf995424873d6550921cf19542487af6250921edd8542487b46150921db195424866c6550921ebd9142487af5450921db951424876c5450921eb15142487e76150921bb18542487e46150921ebd95424872f6550921eb195424872c6550921ebd8542487a76150921eb98542487ad6150921eb18542487a46150921ebd8142487ae6050921eb58142487ac60509219f99442486be6410921bb98842487ad42109219f997414873f54d0521cf15341486ee62d0521bb58b41487ad42d05219f996414873e5490521cf55241487ad42905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb18941487ad42505219f994414873e5410521cf55041486ee6210521bb58841487ad4210521be98041486f96010521af99321486bd64c8521eb50b21487b664c8521ed59321487b742c8521f990b21487b542c8521f950b21487a542c8521bd58321487af4288521eb50a21486ef6488521bb59221487e75188521eb50b504867e64d41219f593504867e63d41219f58f504873f42d4121cf50b50487ad4294121ded4250486bf6454121af19150486df6354121b718d50487ad4254121eb508504877950141219f990504867d64141219f98c504867d6314121cfd08504873d4214121be98354086f960d50219f98b540876e62d50219f987540877661d50219f983540877a60d50219e983540867d60d5021de583540867960d50219f596540873f54950219f982540867d60950218f596540873e6295021cf18a540873e6195021cf186540873f6095021cf982540873d6095021cf182540873f64550219fd81540867c6055021cfd95540873e6255021cf189540873e6155021cf185540873c2155021cfd81540873e6055021c
  | 25 => 0x6fa6014041de540501076e62d5321dd58754c867e60d53219f58354c873f5495321db98a54c867e60953219f58254c87ae6295321cf98a54c872e6295321cf18a54c873f6195321cf58654c873f6095321cf98254c873d6095321cf18254c873f64553219fd8154c867c6055321cfd9554c87ae6255321cf98954c873c6255321cfd8554c873d6155321cfd8154c873e6055321cf58154c873c6055321cf55054c873e6415321db98854c877561153219f98054c867d6015321cfd5342c873e54d0b21cf55342c873c54d0b21af59742c873d65d0b21cf95242c873d5490b21bd98642c86f56190b21db59642c876e5490b21eb95242c87ad5490b21db15242c86ee6190b21f998642c87e56190b21cfd5142c873e5450b21cf55142c873c5450b21afd9542c873f6550b21ebd8942c86ef6550b21dbd9542c87af6450b21ebd5142c876e5450b21eb95142c872e5450b21eb55142c876c5450b21eb15142c86ec6150b21ebd9542c86af6550b21cbd9542c87af6150b21eb98542c87ad6150b21eb18542c87af6050b21eb98142c87ad6050b21eb18142c873e5410b21cf55042c87ad4210b21bd98442c86f56110b21cf95341c873d54d0721bb98b41c86ed62d0721eb50b41c873e5490721cf55241c87ad4290721cf95141c873d5450721bbd8941c86ec6250721eb50941c873e5410721cf55041c86ee6210721bb58841c87ad4210721ed50441c86fa6010721be58041c86be64d4321af59350c873e54d4321cf55350c87ad42d4321cf95250c873d5494321eb50a50c877b50943219f99250c867d64943219f98e50c867d6394321cfd0a50c873d4294321cf95150c873d5454321b7d8d50c86dc6354321eb50950c867f64543219f19150c867f6354321d7d8d50c865f63543219f18d50c875c63543219718d50c873f4254321cf50950c86be6414321af59050c873e5414321cf55050c86de6314321b758c50c87ad4214321de54050c876d62d5221dd987548867e60d52219f583548873f54952219f982548867d6095221cfd91548867f60552219f181548873d5415221be98054886f96015221cf990548876d6215221dd984548867e6015221de980548867a60152219f580548877960152219e580548873e54d0a21cf55342886f661d0a21bd587428873e65d0a21cf59742887b661d0a21ed587428873e5450a21cf55142886f76150a21bd185428873f6550a21cf19542887af6250a21edd8542887b46150a21cfd53418873c54d0621cf952418873d5490621bb98a41886ed6290621cfd51418873c5450621cf950418873d5410621bb98841886ed6210621be98041886f96010621af99321886bd64c8621ebd0b21887ad42c8621bb597218876d65c8621eb99321887ad64c8621dbd53218876d54c8621bd597218877565c8621ed993
  | 26 => 0x94841db982521076d6094841db182521073e64548419fd81521067c6054841dbd9552107ae6454841db991521072e6454841db985521076c6154841db105521076f6054841db981521076d6054841db18152106ee6214841db54852106fa6014841be580521073e54d0841db94b421076d52d0841bd98742106f561d0841cf94b42107ae52d0841cf54b42107ad52d0841cb54b42107b661d0841af58742107b561d0841ad58742106be60d08419f59642106bd6490841db54a421067f6550841cf951421076e5250841afd95421073f6550841ebd89421073e5250841eb949421072e5250841eb54942106bf6150841af18142106be6410841db948421076d5210841bd98442106f56110841cfd0a511073d4294441db94b411076d52d0441af58b41107ae52d0441cf54b41107ad52d0441cb54b41106be60d0441af592411073e5490441db94a411076d5290441bd59241107765490441ed95241107e65290441f954a41107b74290441ed50a411067f6550441db949411076d5250441afd95411073f65504418fd9541106bf6250441eb949411073d5250441eb549411072d5250441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f994941107e55250441ed90941107b44250441b798f50106dd63d4041bb98b50106ed62d4041db94b501076d52d4041db94a501076d5294041ded42501067e63940419f58e501067e62940419f58a501073f4294041cf50a50107b86494041ded4e501077a5394041f694e501075a5394041ded4a501077a5294041fa94a501076a5294041de54a50107e95294041da54a50107785294041eed0a50107b94294041eed0650107f24194041ee50650107f14194041de192501077b6394041de98e50107796394041de18e501077b6294041de98a50107796294041de18a501077b4294041ced0a501077a4294041de50a50107394294041de10a50107786194041ded06501077a4194041de506501075e5354041db949501076d52540419fd8d501067c63540419fd89501067c6254041cfd09501073d4254041ded9550107b86454041ded4d501077a5354041f694d501075a5354041de54d50107d95354041d654d501077b5254041de94950107ea5254041da94950107795254041fa54950107695254041de14950107bb4254041ee50950107bb4154041fc90550107b94154041fc505501077a6454041ded8d501077a6354041de58d50107786354041ded89501077a6254041de58950107786254041ded09501073b4254041de90950107794254041ce50950107784254041de985501077b4154041de90550107794154041de10550106de6314041b758c501075e5314041d754c50106ee6214041bb588501076e5214041db5485010
  | 27 => 0x429fd954210b3e5450842afd954210b3f65508428fd954210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842cb9514210b775194442cfd0a5110b3d42944429f9825110a7d6094442cfd095110b6e4254442cf5095110b6d42544429fd815110a7c6054442dd5445110afa6014442be5805110b7b50940429f98e5010a7d6394042cfd0a5010b3d42940429f9865010a7d61940429fd8d5010a7c6354042cfd095010b3d42540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010b6f5294b419f98252d067d6094b41cf99152d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41cf94b42d07ae52d0b41cf54b42d07ad52d0b41cb54b42d06be61d0b41ed98742d07b561d0b41afd9542d073f6550b41ebd8942d07af5250b41cf94942d07ac5250b41af18542d076e5210b41db54842d07ad4210b41bd98442d06f56110b41ded4250d067e63943419f58e50d067e62943419f58a50d073f4294341cf50a50d067f63543419f18d50d067f62543419f18950d073f4254341cf50950d07795014341dbd4a529067e6094a419f582529073d6454a419fd81529067c6054a41db54852906fa6014a41be58052906bd65d0a41cf597429073e52d0a41af58742906be60d0a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41ebd89429073e5250a41eb949429072e5250a41cf54942907ad5250a41cb54942906bf6150a41edd8542907b46150a41af18142906bd65d0641cf59741906bd62d0641cf54b41906be60d0641bd597419077565d0641b798f50906dd63d4241ded42509067e63942419f58e509067e62942419f58a509073f4294241cf50a509067f63542419f18d509067f62542419f189509073f4254241cf50950907795014241cfd93525067e60d49419f583525076f5294941bed8152506f86054941db548525067e60149419f580525067e65d0941af997425073e65d0941cf14b42506be61d0941af592425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd18542507af6250941cfd4942507af5250941cbd49425073c5250941eb14942507b76150941af18542507b46150941ad185425067e6510941af99042507ad4210941edd0b41507b542d0541af58a415073f5290541edd46415067e63d41419f58f505067e62d41419f58b505073f42d4141cf50b50506de6394141b758e505077b5094141de540505067e63141419f58c505067e62141419f588505073f4214141cf508505073e4114141be98352106f960d4841dbd4a521067e60948419f58252107ae6494841db192521076e6194841db186521076f6
  | 28 => 0x58851d0b3f5114742ed94451d0b3d5114742ed54451d0b355114742af98051d0bba6014742ae98051d0abd6014742ee58051d0ab96014742af98f50d0b9e63d4342a798f50d0abd63d4342e758f50d0a9d63d4342eb58b50d0abe61d4342af58750d0abe6394342af58e50d0abe6194342af58650d0b3e5194342cf14650d0b3f5094342eed4250d0abf6354342af18d50d0abf6154342af18550d0bbb5054342cf94150d0abe6314342af58c50d0bad6214342af98450d0abd6114342cf94450d0b3c5114342cfd4050d0bba5014342cf54050d0bb95014342af5974290b3d65d0a42bb5974290b6d65d0a42bb5874290b775194642cfd0a5190a7e60946429f5825190b3f42546429fd815190a7c6054642dd5445190afa6014642be5805190b7b50942429f98e5090a7d6394242cfd0a5090a7e61942429f5865090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242bd9845090af56114242de5405090aed61d0942ebd4a4250abe6190942af5864250abe6090942af5824250a7e60d45429f5835150b775194542bed815150af86054542dd5445150afa6014542be5805150a7e6014542de9805150a7a60145429f5805150b7960145429e5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050a7e63141429f58c5050a7e61141429f5845050abe61d4942af5875250abe60d4942af5835250baf61d4942eb9875250bad61d4942ab5875250bac61d4942ebd835250bae60d4942eb5835250bac60d4942ebd8b5150b3f52d4542ebd4b5150abe60d4542af5835150bad6294542ebd4a5150abe6194542cfd465150bb75194542af9825150abd6094542ebd895150baf5254542edd455150b3e5154542afd815150bbb6054542aed815150abc6054542ee1815150ab86054542af9945150bad6214542cfd485150baf5214542cfd445150bb65114542cf5445150bb55114542cd5445150abe6014542ee9805150aba6014542af5805150bb96014542ae5805150abe63d4142af58f5050b3f52d4142ebd4b5050abe61d4142af5875050abe6394142af58e5050bad6294142ebd4a5050abe6194142af5865050b3e5194142cf1465050abe6094142cfd425050bbb5094142afd8d5050b9f6354142a7d8d5050abc6354142e718d5050a9c6354142ebd895050baf5254142afd855050bb76154142add855050abc6154142ed1855050ab46154142eed415050b3e5054142af9945050abe6314142af58c5050b3f5214142ebd485050abe6114142af5845050b3e5114142cf1445050b3f5014142ee9405050b3d5014142ee5405050b3e6195042cf5865410b3e6095042cf5825410abd6490842cf9524210aed6490842db9524210bae54908
  | 29 => 0x2c003001400000200000000001000c001001c000001000f000400000040030008001002802c00080010000000000c00f0004003000c003000000100200000004007000000c00000000008009000c00800000010004003000000000500000018000008800200000040000001000800000400000050000000400f001000200000050010000000400000280030054007000002000640010010001002c0000020000000000300000040000002003000100000000004000000000a0000002001c000000000000000060000001000c00000000000000001000000200040020000000001401a0000000000001500000000004001000800000000000008000002c00100100010004001000c002000400100000010028000000000d0004005000800700500060000002000001a0020004001000100140040004004002400f0020001000c00800080050038005000c00400000010024007000c025000400700040000004004001c0080008004000400600040040000000000c016000000000040060000009000c00000080000014000000000400080000034005002c0000024002000000200080040004001000000400000000010002001c00100000040000002000000500040010038026001000500080050018000000000000280010018000000c0060020001002c00d00040010000000000c001000000a00040090014001001400200100000040005000001400040000004007000000400100030014001000000000400000000000000000500000000000000001800d00000050020010001800c001c005000800100000030000019000000000040030000001003000000000000000001000c001000400500080060060000002c00000000000088001000800c001c0040018006000c003001400b001800900000010000004000000c000000e0000008007800000180000000006003400000080010020002001800000440080004000000c009001400a0038008000c005000000500080000004003006c006002000000000070004000000800000000040000001001800200000000000002000400000140010014000000400000100040000000002000100040070000001000c00e0024000000800a0020003001c0000000000000c003003c005000c00200400070000001002000a000c000000c001000001e0010000001000d0010019000400700000000004001000c001000c002000b7751947429f98251d0a7d60947429fd8151d0a7c6054742dd54451d0afa6014742be58051d0ade63d4342b758f50d0b7b50943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0bad62d4742af98351d0abd60d4742cfd4651d0bb75194742af98251d0abd6094742edd4551d0b3e5154742afd8151d0abc6054742eb
  | 30 => 0x10000009003400200080090004000000c000000000a00100110020006000800d0030005000400400340010020000000000000080030020001000000600280000008006000c000000000200000000000001000800900640030004000000c00000000080004000000400000000010004000001000e00080000014001001c0000000006000000400b80000004000002400d00200060018001000000000000070008000003401b0010000009000a002000d004400200280160000013002800000400040008001002c004000c02900040000000006000c0010030001001801000580030010004000000100000000000007000400200080010000001000000000000000058000000000400100020020000000c002000000f0024000001c00200000040000000000c000000800200740020000013000000e000c00e0000000002800100040020008000000c0350000000000c00b000400000040010000000000800600000010020008000800500180170020000001800400340000008017000c002000c0050010001000400e0000007003c004000000a000400200440000004010003c00900000110008003000c001000800f000c016003c00b000000200080160008000000c000000c00900000000008006000c01500100010008000001000000100020004000000400300040090000000001000800040030000005000400a00000010008004001c001000800500000010004003000800000080010014005000000000240000000001000800000040000010002000000000000000020000001c00100080010020004000000900000020000000000000000400010000001000000800240000000007000c0010004000001c00000040020010000000400000000050004001002c00100200050000001001800000080170004003001000300040000000002001000b00100110044002000000400000010018002001c0060020000005000c000c0040004004000000500280050084002003400700380000014000000400f00080010030007000000a0034009004000400000000018002001c01000000000060002000c000003c0000018000000400100040000018006000400a0000002000000200000010018000000c00c0000002000400800000080018001000000000000080004000000400900040010004000001000b0004001001c006000800000100000004001000c000000000500000010000000000000200080040024004000000000000000000001000000400100040004000000400e00100000000003002c00200080010044001000400d007c016001c007000c0000004000000c0000004001000000b00180000008000000800100280020020002000c000001800a00340050000000001400400080090000002000c000000800600000060004000000400900
  | 31 => 0x400800080010024008000800c00080000008003000c0020010005001800200100030010003004000a0014002000800000740000000002000000300200020000010000c0030000000000c000002000f00000090004001001800a0004009000c0000000007000000000040080004004003400000000090004002004c006003000f000c00000300130000000001c001000800400080000004001000c0000048001001400b0048000000c00000000020018000001800000140030000002000000700040000014004000c0050018000003c00200080000000003000c00d000400000000020008002001000000040000000002000400300000000000000000800f0000001000000000280000000000001001d00100030028003000001400100020014002000800200080000000006007000300300010018000000000100340000000005000400100040030048001001800000440000008006000000400140000008001000800a0000004002000100000000004000000c0010004000002400000040040008000000400a0014000000c00400180010004008000400100040010018000001400500000000000000000c00500000030004001000c01600000040028033001400000180030010000000000500040030000007002400300000050008020000000d00740030008000000400400180000004004000c0000004000002c00800000010004002000c0000030009001c001000800100000000004012001c003001400100100000000007000000c00180000018009000000800000040000001002800200100080000000000c00000000060008000000c00900180000004014002c002002c00d000c000003c00700440050000007007c00300140010000008000000a00000030008001003c0000008003006c01000040030008006000c0000000001007802f000800500240000038005000800e00000010030000003800000040020018001003801b002000000000010018000000c01700000080004004000c001001000800140050018000009c002000400600180030000003000c00400000030004001000400d000800100180080000001000000400080090000002001c0020010001000000e001400400000040008010001800400000000020000008c00c003c00d00080010058001000400a00000010000000000400100000000010003001c0000004003006c00100000000000002000800500000000004009000000a0008004000000000080000004011001000800100010008011000c00d001800700040000008002001800a00940040000001000000700000000004003002000800000010000003001400000000000000003004800800000070040001000c005000800000500000008002000800200080060068004000c009002800e0010000001000400800
  | 32 => 0x10014001000800100040040004005002400100080000020000004000300000020020000004800000100000024002000800300040090000004003c0010024000000000c00180040094000000c006000000400100050014000000001700140060044003000800300200000024002003c0000000000000000000200040008000000c001000400700000000008000000000400040090014011000c000002c005002c001000800100740040010019002400d00000010000000002c0060014007000000000080090014001000800000000030004001000c000003c003000000400200040048002000400200440000000004000400000100000004005003c02800580090004001000000d000c004000000400080020060002000000700280000024003001c0000028007001c02c009400300100000000008000800000000000008001007c0070004000000c00400080010020006000000200180010018003000001e00000010010000000c001000400800040010000007000400f002c00000180000018002000000d001000000040050008001002c003000c00000040010018001000400200140000008015000c00000140030044005001c009000000100040000008005000000700100000008002000000200000000004003001000000040020000002000800200180010008000000000200000030004003004c002000c013001000e000400000200000000010000c004002800000000030004000000000100200050008000000000600040000008000001400700180010004009001800600040090010000000c000000c0020004003001c00b000000100000010024000000000d0018002002c00b000c00100100000004016003c000000c0030004006000000000280000038000000000c001c00200080090040002000400800940010000000004c0060014010000800000000030000002000000b00040000034007000000e000800b00100030004004000000400040090024000002401a00000010050017003800b0000001002400900100190028000000000b0000000002400000100050018015000400400200000000002002000100080060038000000000000040010000013000800800000020000003000c00000140020000006004c005000c00100040010004014000c002000400300040010000008000c010000400200080070008000000000e00040030008000000c001001c01700480000008000000400700080020004003000400300000000010010000000200080000008006000c0000000001000000300000010000008001c0000008004000000800100010004001002401000200010010002002c017003000200180000000000000000200000120018000000000000000000008002000000900340020090002001c0010068001007001400080000
  | 33 => 0x9e4aef624e131e97e944a4c24274500800000025c6000acda10100007a3277c0000000000000000004be8b322616da26e005088ba81f538e6e1950c368a1400000000b48800000019e60002da073a30657c1122c183ccac11980002682b2101fa180489240a632ad062f1abb62bf0ce8000000015e091e40f14f01f313063a605c624f800097485a08e50bc0b7292a261092f0442a0da088a2dd81f9b669969b95000113239900000000000332000071b1aba0002e86a8d2ce89ff000074e14fa894b00c3ed2c40b8d8000259800000000006ea21c4000013f00000000001d27291000000026c654b147470381953780a81b51800089f0257000127891da9a0335187c0002ceea22879400005612f79b020000000116c0000002130c3580008bd0040000000047990ba0000000a5a835611180000000000883800000000000c180004f6d6a5000000000016bc000000000000000000000b3c000003380000002f44b9ea0f300000009ebab5e000216b74418e0000000000021c800000000002a947eca3d6216800006c0000000161f5702f6589380008f626f904e800059609720002b30bed6b3401b033c2b7400087b80002ad25c221a0f0e3870a32001800400000010000002001000300080030000000000800200000000008003001c0030004001000c0010040000000800700000190004018000402200000000000000002000500000080014001006000a000c0000010000000c000001400100200050008001002000100100040024000000400000000050010003000802700040030008001000000500080000024006000000400000090024000000000900000180000003000c00000000040000000000c00000000000014002002400200000080000000003400200040010024002000c00200100070000002000c001000000b000800b006000000000090000002000800000400210010003000400000000060004002000400000180010008007002c00000440020010005000001100040070008003000c004001c00000140060008000000400300240000000004000801400000000028003001000c00000040028001000001600040000080000000000a000000c0034003000800000000040058002001000200040050010000003800100040090008006000000700000000004001001800100040000010001001000100040010048005000000000000010014003000c0000038005001800000040000028004000c002004400100000050008006001c0050000003001c000000800000300000008000000000000040000000000001c0000000004001000200080010038000000000b0000000000000000080030008000000c00200140010000001000000f00040000008000000400000080010004008000400000180020020000001c0080004003001c
  | 34 => 0x9d0db6930251de9a7e14100000002ed64491b203a80a9c98d091201a28f400026dc9948000a350bbb26009fc1be934242699a0bdd8cc587500000000000aab16696620000a50ebdd0001ebf0000cc700000000ec2e9c00000008f509c5000222f2f480002c99aae4c5c0000000000000014c04500002b9131472b9c1432f00002f3213b131ae553b300001b52dd6000000009450485078000b229d420002cae0002fd06a100003f3032a040d14d608000090aa320245000018525da86924a900000000000000b4c21f601c800000026d7000076474a663c000050050600004d600002a6800000000f0000300600000003cd800000000000002d2000011ba0208000a0c8f4e8fe80003a4ae74000256301300007210000000067d000000066a30d800000000000e9c0002bdf0000000bba2b1f1101e8a270dc4002d4808572800000025e80000000682234e57ea53cb712204490a0543ab80002c527ce0002d776ba88de65900008110000000000038d8000aec1e80219af988bd4000a1fc59d2610000000000016696d0bd880000000be0168c7240000000c34a8a383826a887b2ad887821a66e625ce000000007400000b3a8b02ab8dae6a38000b2a8b055091034104ac0abcc8000c211d5c7f329607f7a04a000233e00015e67b0856300000000000e4a00000007cd2050a99912697127e4376177a1c613c804f124eb12cc7d36f1b8e00012e80002383202800077d00006930494a8592c8a679f2a970e2d86786429b80c2a600010e0b7b8dff0000005369a18c000000083f417e4100fd610e90640ed80007b90ac6bfe2e3200017f2c0d677000000002a64000ad700009b38000ad1800054f2f4b21100008d8ac430000000b08e6e26aa8f849d2ad346dca27e00015ce804014700000261fe209170710328f28000000129e0001e8e13f800083b80000001350000000088559165e4a9000002ac800000006e94000000000059e9c180002f1c6eee3fc66328ec609983e7821a100879c2a66d8000670b0127c9a6985f929c213e130e8ab306242d5e4e4f387ecadb9fc20bb8d210000000a2dc0005de5adc464207ab8994ea00000005539b5a6f1270a8b04e18a25c0000000000640000092140008fce932047137c0001ecb87389f905a6ae200000000002d92785000000000007b8072613659576714e3e14a2c455708856000000096f0000000063e0001c460002ad000005192c4505ab6eaffc00020ca55a0abd28289480002904bb72adf0000b800000000000202454c00008479c1e79508327b4204e0002d0e6979f90bca0000000276a0714000065a6f89f00e0412e000077099de5d300001e44000b2d8c9c9491b581050f66256909e000216a00000000000000a7543500001c0047f097a59a979302a00000001954000000000021f203ac151
  | 35 => 0x5b680006ee8000ac61e2e17060de91c6e7f281efe241e05767f982a21ab00001c6e9f00e1a007000076ab3f8b8a149029f3c08000a1e0000c300b382dd854a33de46057ca05800016c20000862000049235429c10002f18bceae751c7043884f163656e00008b780007410cb20000a2aac8cd9e3f1155e6b284a3928887e2898b94c449170b5982f532d8000abea5c0727aab60002b54aedc09f210a4fc00004a4000065052d8a7eaac621d5f8c062137273b51f0ff6c1580000000000000181213e402400000008790324a70e81a0000a6d4f600003f0000000008c800000000000b5cbf62c4c000000058021360000000000263e7169d9ab7e0000025165618097d6000000000026c700000002a90c660001ebb0000000000000000017c8000000031e84623ff000000000000000af827aa10d0000000000000000000000002c3cb249524c0ac00004c2f0c00000005d1ae163c92e5a36f8000c0e0048164863045a07d4922c22c000000021525e4639c000709a4b42fc028800008e65905f6c5ee84d8ac1059c23185269a12ff47bd85e5a0d2a24590c1b517daf833c9a251042800000004eb9d44000320a05fbb4000066180009a58000000175c0001364b74000000016c025a800000000006544000000293f0001f564bb80005cf8b1200000000000000bfe8000000107b3d58000b420028427eb0cbca8f38205c000495800000000000000c08000000000000000170000000000083a000003e163a087400000000003cd15b6b5ea3222ba20d031b9cd3053c846ba425a66728394000045929e80000000185392000000000000000000801000004b5bb80000d2500000002a794b40000d8451615608b68000000000000017f0bafdf1c000000064b6ea63d3117c000000031080000341a1a000060e00000001c158fa5010000000000069ae4b2864285c72700000000000b908000000034641bc0000000000167800000000000000870000000000000004cd40005d49b8c4bdc000760000025380009e02bbe4ea2334000013db4508b200002e6ae8109d3649d284778060978875c0000000577223b93c2b3821416ee0000fe0066000000007e60000000a56aeb874a83d08c74f9400000005048000000302600000009b1400026ec696000213e88fc00024a800026d819e0c0acf57b19f640c3da6f00000000002f8800000000002f8c0000b500cd8000bfc000098011a500030217d20000000294800010a09a90000981000000000000001736061212f0ce000000000000000000c0f80000000000000000026f0000000000000017d000019ba0002af8ae355ac14752bc74c00000002eb0af956140001ed10a60000b7ca7b48a587dc7c82fa64f96f004a31ac90001badbee83628f4238f0002eca5e100bc57fe6af146c0000000ba4bb000ef7fd
  | 36 => 0x251c000141abf82ed975a1098000143e2cd1e98000000072d8078000230a8918000315233c76e89283564a717d030c187a00000001c9a14508a2ba500005ab91b43ac00000000625a12800062607886a098aa7624f987008a3800024e0ab36f80b1f8000a2b8f6a7e980009c200002a340003acaabc11b0c148c580009899eacb9f26d14f29d6446e1e3cbd52adc56791ae7691e4698d9efa189c9ee3590691b694000000000030d80000fa00009e98000b1ba22c739000000000000000000000070f000004a6b910769ef80003b200005d12a6877380009a4000027c24980000aac000000015a00009706e529cc4160b66aed249280000b0800048697d20002a58562800000000003399bdac3a484c32600003838238000133d4a5b1140eb800072f19a2358484e647000088a8e8c7688000000060887e8000000021fc38278643b85ba9fc0d392500698a7ea72e1105990a1120c4000000000000007ec0f123896421a7300008d591374c21a6097a80000002a0090fa29e6e01b08c134000b8725f81e8a620a30800095e82920000dfa1995a547da893c00000d43e915d60002bfc0000e02bb9ee3ec39800000026d81d6082a1b4301b50513c0a14a6a9a93a87d9a08250000000035ee09a0001ca81e184f457a051c9c78f5e42e00006740000b978d8c373c0006d200000002b893f9a08142c9e1648a83f60a6a89d090c2c45178000294eca31581ff0929c0000000de70000129c25216f0000a557bc12d8b53c000ae880000000000000000065283723344d1e79200000000000a601a1e0220d7e00029c4c08c00092704c1000000000000005d52ec800000006210208a3325a700020b60002cbc4ef2c6029f00000002ad4a3618e6935ad0c0f1000056a190e9aec0009b4c67600006758c3945200000003ad6426b7c29b818f645bb36014347f8000a9f1b30000158208d293d6710cdb16002f4085645d62e1d150000c0465a006602d9cd6274131d693c00000001dc4311fa000000000002ecc0002c80000208a000000000000009f20000000000000000005a51df68a714beb3480000002f663188000bd0e01427500007b11f420ea8da882b8ad9649ad519cbd3277b580001a5cb199ee00000000000b37961c0002d88000000054e9e5a00006c8658228c14e906b0002efa2d59b263ca10263af4fba773279e17a0cfeb232d780000e222c3a8180002002000000067f800000000000000adc00020061f8a56c16cc64a8c10ae60cd306b81c40001ed9fae55c9c7c7ad55bc55f09a22672cec10f9f7a1b9d913bea0d6c1df149e4da95a45ba8754352a69c939a0225248c90bec99150ee85963cea601000201800012824470b9e1bb2442a6104309c7cf9600013960ed05a209253fa00000000000000000080950c140800000000000000000000
  | 37 => 0xae67503ea2c40000967063942566183bd8000917a5952542e6752b800052c800000000000000ee8000000050e68763ad2e11bbd5eba8de0ece93126589b586de0002e54b9b4b8895720fc8248ab00882fd67c691e47fe8000912800000028eb0000a006cc9d6e1faa2e011d1b06052653000000008f000000001d58afa83f40000000000000000000000001a640000ab23308000b09c2f30002e120000000c36c19cb168000b4b13240000000b13674600000000000000bc792e281c26b000000001038000000193b0002224112182cc366ee200b970c7a8463200025362d000000000000000000000000000000000b3d00000000000000260e26e276ebe086a3819800082396ba40a0da048880002fc80000db00003ada4d400014a53b60a783028000a6e56ca35c4000433a4de0000000607026b454ab868330a10000000000020989e2269469e968c0000f068d622b24f8d35a0002f5600000f60000fda000048c0000b2800000005aa00000000f3059b92f440910901b1945906a978575c28610000000a231cec49e9b9a2372ae35d54428a4d0000a30c0000a80af90c467d49af27192cdcade34609e53e810a81ec0a94a5065d815b9cde53503c87fb87b4279919e768016416caac352694aca661902799035ab7489c619213980f600003b1999c0001af9a3118c2000234430c800e8ef80000000000b64597a0000000000000000000006004000a440ec200000008a0800027a00000000000000055600000005998000000000064116fc3d90370a0e00005a6af7b00000001650b32468e93600000001f085c0507237cb4600005ac00000001af267d86a2a12635d2f9a80a12f1ca602f67252181326b708c10b5d616ea84e863c19d25400026be000000035c20724c100007ac00008f89ba23c6168184200000000e66431c000000164800000000000b7c91b400000011170000000000156ec3781f6bf307200002c86000000099b0a660002a885fd00000002e440002b8f000121c0b9c64e69c00000000000c32d0f90001c740002c02000162ea5103e400029208218000000227b0e10670423199400000000d624e249c0c4c40e93f28eb8000ae200009cc000000000008eb00006220000bff95d30002d89000000000000000000000000000000000005830000200d76a078000044c284f62dae0a844815e00000000000000000000000014827d1800037bc2587db80007ee292a8f787ca00012d04a621f4b010ee023fa1b00002d90139e4482af0c4a16424a50118cf20270762bc3a5188ed81040000000808267a1e98bb06afe6a55819c869302956af404f296500000a3ac724d293ae0001cfc00000000003054bc685e467f2bb40000000000000046340006f20bda129ac0675680c0c308000c07aa0647cade4a990af00000000000099e00
  | 38 => 0x3c9004c3a9cfea080b0090c9c2e10f06626e9c3d645180201fced96000000000000000001f000000000a7a6031b1fcfce0000000000000000015140d44000a0a00002972d6269380009f29f4a00025af692c8f62b3000000000008fba1782328000209203a2d12c5c444000000018c36a68cc4b1bcc7c91fec1b9906d6c825246444a97ac0a083402d824749aaa27100000009939c3600022f21da297400004d0421ed28b7a80000001fb4b5bc1a55f81b12002114c00000005181dd25442f685b920e29ad8256b1040000001dac29ce69133817dcb9954a6b2846607e68eba2f70000000212c44b000000009980001712b752cb8a7a1701000000000017620000a7599b837a0002a1a612b018c222674406436a6f2c00000015fc0b50c1c14385826920abb9282d407a19dfc3ff91560734000b0900000ada7d80001ccc00000f187f9eca19b88d0108990630f1d881c2916d7502bda2e498a0582a146661189e2f740000000f087f40000bd4cfd43358191000000011c07a85d90d2000000e07acd05075b225cc12a3081bd29e0af0250e0002c7a54d960e63b0c87064309280b400000001566b08d651a025ba16556602cb8c9a00017810002a04374a714b9f9e9442d2ab09f78163ac700008d317a0000185e924a3ce131c81c9d8ae4600010d09a0c00055549340001d4b2cc00001ceeb2aba892582da231f98eafeabb79b84062c2f1a5330da42380002a7d7f690b2106a20826313a094a6c78000b3f00002cf0000238a77600021b8000000056ecd7a4d8118e685970a1fd8000000168263e22a8000130c1ca12b2c219e023980000ac0a0d2b564000afb04bf2e8800000000000000000000000053207d2951000019e423fb8d115069a000096cc5122b22be765b078292c139d675addcaf39ce600000007122b8b8a39818bb9000048612921fc45d6b2060966440d31b928000c38cf2243ea1dc957918451eaa6e8842f6e14f0acab894000037de4400000000e3d0ea00028de5c98d0600000008d98000046ac88147e0380a59de891480003eb9a500000000c429a22b8800001c3a06fb0587e40000000bf480002a8e89e00000003900a7f7d11a7fb7dcfe400000006dd800000000000891a0e00012607fde678509800051c19430001ed7000000000000000002b080000000000022a5e895e20000000b9386cb000148a4bfd38ca9debc267701a97a8c26a13aa4bdbf5e35072c9b596d880003af27157af8cfa078b0d0a24800000013d430a8000000235a0002e2a16a0cee28c159a6fa127e00000007481ccf3a0a065b508d830680000000221e0ef8ff4000000095a8000000110857792be1d0a718b7f49f8c30c000ac88402a42909c00019e2790a2d30000784000101c45884326d4279441c03fe000082800000000001e740002bac00025
  | 39 => 0x28700000000000475a2261d0177500005eaa4327e21e2908400000005911cdc76620687d74000a1080005f680004df816d0000000bbbc000000000000000aa603000000024c20002bf800014965ff00006a540002b4307800014ec36eec9f3d281241cc0e72000073a000000015a80001815ae387e44a0435035ec0c219229ef0b0c3a00000000a6e4488000000209f00000006dba3866d818740000d9f000063c07f8000a0eaa2e000001a81868a800027ba0000000000094c450997226a0b0c593000081f00006450d24673c000223178855980000000000ad90000000270100005ac000000028f019208ec0000001b7a0c58000441a8aa7a900000002ba700000001c780000000000a542171000000000024b9000000000000000000a2000000000001136aa9d1f870d2ef122f059931fcb4a000115e9370e7e8802940000000000020b248b800000000000002b601ac00007b60798a022c0d2b0400002800000002fde5b5000057183cc7ce20aa7b78694229a2b80002704000213a39b8000000000000000000001a995e71d00452ca1e0048c34000000000006caa13106eaa0933a72586e1bde919945e80000001d670002260ae7841c81d042b00004f69bcd4761f78000933a5ca4f7ea0302795f0add8e3800001a83da1238366632468c9d3e00020f2000098e00004a5ab980003a780001b880009468b58860ac1979cab7a96ef0a69b4800000500000001c7e00000006ed800000000009df86f05e78000afa28a00000000000193700029fc6a0de27000223829c800000000000001fc80001c0a4348638b0240c17e72357c2b28844da00001990000b830e5a65ba208761a51e7d60a489930000085a31a20d8ca46918000000279a00014d6000000000021b60000000000191292417737bf17be67bc4db9afda77000000000003b2a11800071100000000bf497d800077416182b9425e000000055300000002b1032e0e2ea0181d6747dcf13319d1cc0410445969ec30000000000000000000000001b0e5805ba4a3e02aa0060dc60c2c06469119db8a18b2a7beccf0a216f40b26972d03a2a8d5ce9c80b44c0009b0000000002ec74640001a094a87b6474c0001d160000000b078000000199971418f05bf980400023800000000b1e06c5000049892f8000000000000004b900013a000000003fc286f00017110000000a9e40000000b5e000223600000005c2dde2bcd823900023e40731b99a6f80002622cac7890000000192c0002c7300000000000000225225759510da2f20092000000000006f893d0902ab4800000000000002e284a980000001a3838f2d5866c0000737667b6a187a050a000068d907ac241892ba201aeaf18000bad1d690002648a6322620001db602fc66c1dc800000000004cd8000000164a75429181fc16794
  | 40 => 0xa4b8fc80002d3c572c00000000003470000000000000000000000000491000035f0c926db2d0400000000000eec0002c826870000a8c130d0001a3e0002eb25648000bdc00000001b7b000000000009e089fd1bcb28800075a8c6a15d103089600000a719d290700006d91f1d000126400026da9680000598ee24c2e13f600000000000ba795c82f257f800000016b30000000000000065d21d8a7704f0000118600000002430000000000000026ab00000709ca302466ca0b00000d743340000000000000000005b584da50c8000a19221800f800005604b1a5e067e8b3987a6c0210436913be0000000ae51d90b3410e20d72f5eb3e0f86c4457aa8fa8000000000000000008a60000000000000023ba00000000000a684fa800013521a2bc040009d5202e00000005d28e203259fce00012fa518811100002c85fa2675336aa904582a6a00000000000000473a2ea00017d10000d82af070aa000000000000000000bbd422400000026140e62e76a3aa1840000000c100000bd32c7b1b11cb037ae62c0000d2fb0c0000000199e2b603f2b0cd7144f1c0000002a705c64c8e00025520001fe00000000000000049b8000b7c4000b299bf44ae0f58a6d8ae7405834204aefec79b10bc010a02a7e4a1f039e1b0a999ac106762cea5309391391a6ea00001ee6b05ee22fb00000000000000000000022120320db2091a7b250b1d569a9982299a85bc44e9ac72242f33c2a0000261800000000000001c600002c3f8f980006388000a78cbe10000d4e1db179a000000041a800046580004b1a0626b9a0fa64fc60667453ac08c462287991cc28609d9b5d21747ce8000588acf27068f749780cd380c0edc035a2c29d01fbe35d863a35e40009ca7004b4fadec944200561307da0001ab2a738b82acbb060894c00000000000000000803ad734cc289400014c60000dd4a2d00008cc82847610000abf87c000000000000000729001e519309a4b7aac2a4695d0b2e8cf648f063723e249a47bc388af5625a95b988c35880000001728000264a5ee1230319067a0000000000186a0000000275c0000002f5c0001f1f00027000001db00001b1a47100002e94000000281ea9eed6a17b4b02824283046a1e2c1cb9dea346ea9a00000007e300003be8000a64000000000000000000bf980000001d7403728950002679b5b400000029c60001c3cb246ebeab82cfa320470230321fca52aacb00002700000efc0002a1218c4000880aefc842e0954469d0232000008daa6ac11d97b6b612eec0000000000000014250d5186800054626eb0405bc021f000045b90d84e5c0000002ba671a80000001d9676981500000000522120892005b51a5617c526047173c2f7904d410b0002ed896ca2e813b800091500000000000c0080007e3db759b409b01aaa6f20000
  | 41 => 0x9161b5db1511e27311626c3709cc67b58062ba80004e50000333e9140b6904e18b847265230f00000116617035f0b900008c30000af3595d4c724a812d800056fc8cc00000000000a243e3a376681000021e80000761fd214280008e42b74bf8e0a7083e8e000000000000000b6b087644397b269ba266439e1940ab8617b592d389c6c6200001afe00026d54bb2c2b000000000000005b8a1560001599c2f9bd833acd6a22824d293a874b8dad93c1ca481a408abde80487d82229f7400028108f800003d012a4682800095d234070494c09489a34b04d83c00009c23b4000096d28c000e2e7200015502cb05ee0dda14e00004a2299dc62979a1671192d7e64d56aab9a11ea0002c46bd40000000082cbbe000018d897096923920f180ba2c34e5c6fe17632ff19629b9e9cf7e8a2cf0778ea843e067f14c1b3e00000009bd0000959151278a0db4259000000006d80710bd014aafbb42990d9877a3c891305ec00026e81f420dc16c5c2c72d2494c40044cbedadce9ea95c837e10a257d88aa000279c96da4380002ff224b9e7678804ba00000009224000a22000000000003122fca12b00005a79d520f500009e30000362219887a868c0000e9a11d46b4a6b902e9859b7464c9c6e08e861885c883c692955c00000e28e7998e2311bee5f0ae3a26682dca151a9216d21cc818ea1437b88b6272238cb7992aa63305d35f99d78068c00000000008ea8000122800000028e873084ec000000000001bc0001ce1a3f00002bc40007490000000182a30e9ed467d00000000000809a1ca8571038817976e9ea115c2a489bf06e8098c0b2bd622d084a48a22d631790ae00012b4bdaaa4458c9f0c65988fa6a8a73a4bdae6644bab40291a2f81d8000093faed440523da5d38000c138000511999a3740f900000c18000000000001d50002a9e64ac95cb1e4000964000019724233119cba373ac8bbcc30f2ad38000a2d414e00006040218000948543c6caa1764c6167715f00006d3000000009da5b1a425bf393a46f09a8c000195e990800043f80006aa1344762ab3a5088f320002aaa520000000000005cbf1090001d091b6a9a600000009add46eb788000ad0aeaa55e8000000148c00012d23282205a9e24849b040002b5a9a22fbe6e930800003d0ac15be880007719998141a922c140e06000000025f832c83c0904bcf0f0000013fb000000060c1154bc428d600000001661ef4708186e6970db0886971a0111dc83ed9d37000116684b46920000000000000000022caa1a4686000164600000007c2161b00000c40000000ab399b896f9e221b4c000b1980003de95049f180003148c569540e24000000050d028a000000034aa72665f8000000006a66940004851072763a82a97d06e04d580003448000292a74f0000f0c00000b30002f9d
  | 42 => 0x3b6a8b422dc06b2281858c22782ebb60231c6cd956c4060ffa3d68000b27992100018b2bede1290000000000149427885d21405db84e02632a472440bc200002d1431c0001586000000000000006ff80007c50ef87260d782b509c984e0a121b0e9ee251aaaf7aa17a8614000092b061c53f2739bee40004208b3e0000000c0d0000ab2919c22e0e3292b64100001e5609e80008d65e9c000049a2d1c18aa794000c12305c000235b0002d5a000210a00000000000148541a0368dcc000000000000000004f840000001d060002ada0001a749a3925c00028bac280000000000055d8b2b97200009228000acc8d236b22bc4673a99a0af002c6d5c9b20000a96548a53960fd872b0f400067c8000000000000000007538d440002b683400df10000f766be8bfa3f4aae494114bc94996f10002ab41c1a118a0480003e98d30be28000863a72a3bba9f600022286df80008464d58000000070c1cd400000000000100a79000025d22680420000aa1dd4a00017420002d8639c074d66b28d0b7e800000012ac3b6d0b08210eaca888cec968e61e000154a22f8000382100e64f800064a000023608f400000000001d220b2a19b59440000000000567000041e69af7648000ad600feb1d15ef4c85d0ac0886840000fe299707b8aa459b497161867b35f760f99f78a82aa4c27b00004628000893258c08f927c154430e77604240000000000219a00013160a40000000000000007467b6800050ae6a7000000005760533f78000000000095600008e100008e38c76950000074154ce00000008ed2f976158178000061100000005408000000000000000000000d340001067000000020949ce0002b1ebe4095800000005f5000028dabb216fa4120d3ae2f51394f43df87115029d605c5b06a00020804dbe8ac0000a5e92b80005c80000afc14720000000000000000010db0de0000c1a00004214000a2c8bb802902db4e8a71a9e880ea0e905dc14d8125084a2be5f32416211e11607c00003e205387e3acc86f4954603ba39c170aa764652720a9e8f1e9a3000052eaaec000131200000006c623606bc4d568548bc44fe302fb57000000000009cac9b4000128a00009fd00000006c1000000000000000000000000029e65787832c9dc1840000000f05575c2f600020002f900007df177400026e6a1998d873f68d513495ae384237d3c100de9e1110221b0ae251726430002be4b6d8000c3ac7c80001d3c231c3261345ada24e824c95a1060000152a4e12bbf2650000000230015b12cc0000d1669b400022100009d6025b000073c1af0c129ab4000000000000014dc48307780002da217500000001ec014080005e86f4a1e3302e000000035500000001f3c00013f0a3c2bdc4b80d690002fa04374000110a69a2e1a4b70002fc906b28d20001315b16
  | 43 => 0xd304c7c2c93000013de25d963e00021da07a0000a4f0000000000000000006bf188e9c3194c0000000962131a000227283fa7162c970e26f38000000000000008497a4000082985bd00001f8a29c11ebd0aaf49dc8ca20002c299a280d8b68d17459391f6a65192f15225deb6c0d93a409aed49a8000366000055200007321d5432300001ae12f2184244e0000e2da5d800000010ca4dca8bc00004d6000000000000001e00e940000bc500027663de0c9e000000031e6968ae682ff0002f8e01e80001c425aa2d39dee00021e23701ccd208a38a77eac470000000000000000000000002ef4aef2cc36d5800000002d2000298e0002e82000062a8d200004d8800000020c8a5480000001cf3b65087263d000000000e4be6b0a3b2a0ddf5341f86c1c2aba63383bc61e015778a40004a68000000029ebb960e63bd30337cba2bc4cb8fbe7840000a3197940000000acdab7e6b80a224bf1f304d99a9411ba2ae82e945657b1b5e5291ff20040d0c34d9f5436a820e64e9db29a817708b8977c49d071a2302656929a32ab52a32e032c49c00002f02ab488600019f84e1455c000086a000005a0001ea6368c7044708cc0654e71c5e081b20000000000000007dcaa20000000bc0dd08b074000b532ae11ccadbeb9ba0081c9e26ebb061b592382b44e1acc42000e2b00022630000232000000000026246e989a10000000559123400000009c5c00013104cf71783545c8966b00000000000a76372a5d429aa872350a4567c88000c22878e68b30642c046247c340000000000000245c94caf600001d14aa9a69eae3947e59f237a5e581ea737ef0217ae81418b2baa23a1bac9ff92503641180a6c09f2297572e0ce965c5d42d027019bbc6f8acc2098aa363fbac890669b922db8e0985600006ff08587dc2534587623e4528d2dbc5000061f800038480004750eb80001fe8b2600000000000807000009922a0000000000003088a680000002da6024000000000008e931080002ee0566000000026c87d88e2800725a26a8230612200008819fac62f8818a36a330222246b365d704962a22b37721ff74e9ef260a0cd8ae319bc00016f6685194e00000713d8ac565a19b2467cc0000000000848ce2a000000064d86a4bf191abb0e1f5e6f580000000a585d5aca00000eb18cda5ec50e1f841c2000051095ba000000000000007fb11400000000ba61706a7400000000d381d5cfa82051c109454bd46c5844e47d2dfcbf9c75e3252c9038c400079f2924647a0d83ee2f0a849671d1279eae84c60f5911a3dc0002e1a8c501c24d785b00816eac000000069a800023b000009867780001d5e782849b000137600000007801f1099f075000000000001e50054c000000217a0f4800000006358a400009169069afeac83857a12e53800002c76592428ee7
  | 44 => 0xb96000006fa96c000000000000007230d2e00000000000a3e0000000129d7ce00001590002e9eaa2d9503dcae9282b0a3a62d670e0e680008e0826704811ac94b13f413384c24f3250a2a186637bf812a3b1de4c00000000000000000000050009ba580a31001d291e9626a806628d0887183907430000000050b67c00004259b05b5caadd6118a5a83de672abacb0642d92903d52bf289a800000008b07d4240e420181ac408000b840b620000000c3909f74eed4100000c580001ab685996b800000000000000000000000006a175200005c1526c0ff190a66900000001ad200024ec2c6800000000000000161000268f59a0000b3000001780cd23a5af350000c6891bc00060512f3650000038c1eaa69e01b7a621bcc000055e8d08000aa18aec5fcce8e5e01a1200002b00ac973230ba60c56420be000014022b13340001d6290b94d8bc19c165c8c0000000f500000000000000000009bd2c0c0000001df873e12663e7219e00030f650d98bf00000002a4146b13dc000086015c4ea9f7200000001e92c7500000c6637ae0624389c4b3593c43b5ab82000163c091239100013b20002e8e0000d5f1d2a3bca8f0d1a380ed8fa579d820002bef0000000000150ac23800055d00005ddec2a5c1c00000000000000000000000000009de67ea042000000000026de84385054692bfe000204d000249f000000056b4000537927900027f699800000000e5073c8000a9407b289c00002ce800018d2528000000000008a4000134ec3b800000025d091b1e6e7f7000021d0000214b0ca0000000000009a00029da1500000000000000004908680000469800062f0000000013490197e2c215bdc0002fbc0000000109807c00000000001d189f480000000000204800000000000000000000282e00000003e4921699d80000000000611011f3e006c20001d9eb8f2be1000211a00000000000000056a3b8abb4a6f0970000000289c0000b6c00000005d78000568800000000000000000329ae607f8842a696cbd336e9daa415800000030cc0000000000105c3fb1d1ba39255a19cc00051324502eb1dd6929173800009feaf2c0e69a35fba8339bae000160800000000002670c19abf40000a1a00009240002856000000000014e60000000984800056d4000bfa000031c80004308000b63873e0000000000248d000137814799389f70000586916a0000816444ef867ea96720000ab8a8800000000e3a0002c7014880000002a26b7be7020002b24a2cc000000000077b0b1c00021750001339b6c8000bf0000000000001eb04fa25793e879806d24834aa9a09804e986800000006ee01d80000002ae84dd400031fb05f2498d6800000000002c55000030a00004b400000000002b926f840000000000000000084a8a98000152686a854489
  | 45 => 0x33657e0e2a239822069e12c9baa91fa8a4a8d60b84f49578900a83e115c53409b28f2b614b0a82823611f19ad87be188600019468dfa90300026686e78e260002d48000000048380000ea285e000000000000001d99ff900000000000c5c0001a585fe600c00000007e20d9c0000000c43000062e800046c90862fe0ea26a208f243d89ac3e0841605528987839fd400000007b4800093191fa4ba8182a1fa7b002116ff05130007b5400093e00002f0c0002958000aac97309a2c000816a26c82146125bd0000abdaea030684cac410b6a7c5839100029bf9bfc00035004a8a2868e200000001f100006b76162b468a340000bea00021bea9f8000000019b000000000018ae5e41952a50af847774b16a9490d38da0b748490e6cbd90000b9a874e8bd8a0461a29ba0be13229bf01a100023f4aa6000039ea938000189c8528000000040c950a81c000000021229ca0000000b4011820001eb1aa8482780ad338093a9aa3a41ffc827ac3441a0af49e422789a8a4ee761d2ae85c14786cd052e5502512aab938875f83e08d28000171307e02c000000000008628000a4e80005e5400000007ae40401720000af60001a986f40189456ae04000000000000006daadcc00006f9000000042280003521c8e72e2d446431169a4207f40000000000000000000008db9b2e3a0000064d266200010368a981b83e32463c0a1852b7828df000151a1b700002272b4a0001b691968f520d4a5664022400af9a0e400011aa5242d796138dec743ae5058e11282e825986008aa089db07469999c00768820a8dcbb259092ba195809b5d74dea3dc1ad47f10c8960b97f8859000088c8ef265a8e2cb7ec0000000ce2732ad36a14307a887c1185bb0000a978f6c000000000009a427854a223f0b1e32c0122ab79450835844a50ab06d0000000393800000000001160000000113962a1f0e000000000018a6000000000000002ed400000000007a82e380002b98b6e039281a800039600006b38000132048673680008fc03a0ac280000001d323858000b5413029bf6f454c6503eb270d57bc494ca9b2400000014a30000000bb180000631da8000199d207800024707174d5108344d03b8744836412b45fe00029f258480008b40a4216986c0488101a00000009fa8e7c53b95a663c8000000000000000000921be600000002a0a59e000225d747ac0f4f704369669cd02422d1c0000000280883e13899d7000000075c8d81000254a6ce80004a70000c0762c49329af67f90000bba8000a788a6017c0000ac5800000000004e7052100020eb852105e00023542401a8a37c80002339b4e64a937329000000002fb01858abe715a52a97fae5c00026d41568000008a6e5ba280005842b6ca6298580000962ba12a3ab53964099f6e0f8bf050883da3640000ea400000
  | 46 => 0x1f8555091a73650dc000026f14616cea6f58db000000000013900002f200000c00aee00008ac21f786b8d329ed9fa81a20000007687c7f58000c160d5c1b9808e8b01bf00b89d1a7e904de196089a97319be748c5e2085170e0001588960ea2ca4a00000158000779ad8d89786beb44a8c568a075a000000014324da65c0000217a3e895c0b989cf21203a20b78951a2e4ad215f4a8faf2c92e30299bed0cc2706f9cbf841e1b1a225bb032ab85b3000099cc00000000002aea750b6f2e965c0106dae4300e00011a22a74d0a0000000c28968e0000bc2a1aadfe6a4049f000000013a650c7b4c0009f31abe5ef1ec10002b0e00001d27998a012cfe66b000000001b848407380009cc95d40001116000000000000000000000b02d246540174800000003441a56666d4f20f29f36000000075999208a886b13829fca8806c6a4526e050be8318740d5583c700009420abf880e5d61c5a242489800056f8dd6bee2b8036280004108f607e2a43c335d0660002bb9a8040007a1000080c80000002f380002654c15c40a5e306f66334000133114ea952b520002064b061aac0000000b1b177613cd6be714800013800000000b22094d2d4000079e2ee800000000008bb969cad5800000000007ba1bb439d211c001b08057762dcc05db8a8f12eb60002686000138ab0200008e208ee7220000000000090d9a2400000000000bce0002d8c00029019bb0353b54800014c95e4000000056000000308000a8327c41d648985cd2f7d6732eba0000000576000032a2c5e7d300000002bf600012c296a0000b8620b450ea8628f4983685a5791a90a67e00000000000bbc74d16e808ba3c9029a0f40002ea84630c6027ec000086857208a2f5848496306f918fc34dc0004948000000054cc338000100000073bc00020bc000be7c00000025ee3f28000000097c02b0cce000000020100002bb8000000034a000000000001ca0002677a58a565656000000008820000000000000000000007c617035a9995a2e40ed400022409ccdc080e9aba476f0caa6a1c0001bf800090930c50e8a23c665c9a622a0a4c9bfa47094f8000a5b83fa125a38d00016a4672174500029fe0002af26bae671ae12a1c33a8b9600103c258a1ee64c29e9a8758f2ebfda62e8bf82ef1baa6805568fb2b1c4ee641328605a5662255490e893d88e0696afe51300df61b5a75c54780000c480005b600007c1803470f9bf287cc00000003ec8aa90ec2a845b833ec240a34400000004683df1890000133c1e4241e4b5aae5000000000000007702a973af8000000252eb98468a0003020000010c26580001e5a74913d5f2800000008c0800095f1832000063b52104821a3a6ed0001d25678ce76000120a00000f49e928b1000152e00000000002b20000088e3088000b06860c0e014f60
  | 47 => 0x634ae9a0f88f6e813c36e88e842e00016f26608ccd0002c52000218800027e0b0a2cd4960ae5f23682720002fcb4bf400000003005f95ad667800000001e3ebe51eb80002ec2000205100000000000a7d3554194a74f0b69d6892006d80000000000000132cc4411ca781abba67a80009b30ab5c1b80000000000000000000000002b12430b8880002938000000306c3830000000000000027680002da8000000005dc0005f280006a900008f748386fb2628a41af3492e9ff8151ab12576ac7c7fd0fc2a2945e71628eda0000fd86b0301a04858d658dc00047000002cd8000be66c3a92ec69a00015440001cd577c16b4000012330c1de000012a025b112037694cf9d3000000000000000128000293eb8b21285f604ae000000025a00000000d2c8b200cc3a19200a9209dc66b92b64a18a743cb0000017ad7cbde1e8220143da5a1146c789a36c997a21b8ce2c314fbc6bd000045e61980999dd2a600000000000194415385af11800002c90000a1c000063505da0000000000000064b95b200030a593600000c1cc6c599042c0000000000000091caf720001ae200016fa3659232198434c05482ba43240000000000457d3593058de6ae8c000080a7420000000bfcec2019d28ee1b383f003f16c4785d1d200000002f5400000016240000e440000000000000000010c063410912b140000000bee79480007f00ee264e51386be0000b62df02000031a0bf090615518484d48a169e08000000037c57f58955280a0c00024f25fb060a8966c504db16897b30fe878481383b10000a5ca0752b486a61a708303218186829201a0af80002a228fa000064c6b2c0009f594400000e1a9e393da4fce4820002b3c0000000278c4fc5ed0000a114000000008a44f800000000000003052000000000000004ee000000000002c60000c11123aabf0dcc6c6ea1099100007192a1e7961e880798000000261c0002a3841d176800000002244ce49bea9c80001ec800000007e5000057ba6b25e9239a000049d000000081fc000a0386e40000000bf21dfe8a1243a68b80000000000000000092f1b5200000000000000c31d27600000000000000255800073d00000002b7d58118c6000000000024626490000a298000997cff819a85cebcfa1016a0066859c14f844522220ca009d000123698180000000000000000000003dc0000000ba91e7e1d200004de8be88c640003aa8826a12d0d65ec135f05985fc3488096b23d7a68fd8211a5c2dd850199e89402a7267a5ddb00000002d32c0073ba62a72289c7af6010907188f30506196080167f37c26b45ab000000019768b1a9bb2a1265014b1eb42d49e920a18000b920000412800000023a200020b74d195d246da6ca32348738850000beb977e73e80003ec032e9770cba1aa1702b0980001ce1ba01efe
  | 48 => 0x91f25840fb80002ea00000000000bab8000000000000029120002103ad42f741e700003cf310d76d04c9abb800004491980000000036800000012f13140588815ae1447706461042b062ea9bb000001e40001f3e54f84fd30e06fd8dd012656d16e0b04800049300000000000000000000006ddb1a70bc72080007df800095d96980000000030c5d038d000034380000b5925e000000000019f7636800000000006e0b0e100015ea59e0ea6000000040000000000af20194000000010e7d70000ac506cf7e7800005f2b8a000125a00013c600000000000000a8080004032661a9890c805a8cdcb095b3c932014d0ae1731573162c207eb262d2eef0435c0009b0a5acb1ad50e00001a67ff800000018f6000000000023f2332565e922000006000001ff90e6000292602fad831bc8c700b7ac6d30198b4545a9a4570c000000128e00000002390520250a07600000ed24b0000137c1620000654955224800014b80001c920000cd54c2e9a8000278a0002bae00000008ae80000001980000181002000007300360bdf12723a284aaa32824a5be530000015aa00000000000b46631c23c54c800013fcf9e0002a5a651c0000002c48b721caa17e800088702ac24600004f2c0008ea2f9600029ac16a946a187800000028e620ba8ce000000096c0000b9580008e2c0b865e00000000000000173c00000006d0a687b089e4a0a30000bbba9c000029b40000a62a7591a000000000000744b7a2cb28c6000000014160ba2fd9a0b0000bdf85cabeb2738000000000000000002a7d000071f5c700004ec051a4462520000000089cc000b56e0c200000005dc80002258000322acb490829300002ce016940000000efea4b000021d5ca299fdb46000108f0002efe0000000000000000000000000000000000083e0000c2b80005111b4a0000000a10068fb339b22000080e6b941a44e7b0c9814988a33f1bbf9ae12c016dd4e209a00006a9a54c000225073180000000a8e6ecab6a0002e8cc0a8731395a97e2e393d6c21d3e634080ecab02c140002fdc0002ce48079ab836d815559d08f0aaa5dc469085422629ac65652d9c46c12888452ba53eaac84af200007fa800007c90943fc8000a83aac47f61e04531000000000000001d460000000000045ca9d0c7880280009b92e814b72a6cad8afd40000f1a655ace668980007138000000290e2d21e389a0448e0002acca2e15c100f03228deccf90689f6600004200000922ad6a64670e0ddea9cc0003450cbeb2f997c9ae888000000005a2000000000000002b4c00000000000408b7d0000bdb0000000139b965951c1ae5d440001fb611e9d36b4596900002b780dfafee0002d7684400000000000b9e00000000ba600000000002a9245b24a333d000023840000000000000065e00001c00002414
  | 49 => 0x12c2c0005612a4aa3d831000000008a52bd36ba2b2c186cd89254a8fe09990a4251041a00000000000000000033e00027f4000000020d000043d0000000227a000000000017863378b0458780000151eb6000039c8c48000c169a18062058e0000000000000032ba25400000004722d2e000000000021ac000067c000000000000000002688b1f6d549bba538a0593920c7800000019179b34aef0000a5069b12ce69c80009f425fcbbde4d51691d7c1ffdb9c602877ec20aa5648fa84d77dc0000000000a970000187d57e7792cc6079d67e12008785f1800069001a700003447381e18a74480c0001cf94430000acf80000000570000000000000001dc000016d80008d94f10000070c0440c840000000000309e1ef99ee6312c362ed9248619016c57461ba98e000068180004fb990843f256014580ae1bfcaaa0000000825c0db12cefda0000aa600000004e6a2301c2689f5152f22400b10e00025ad36e00001d4ca0e77680837da115800000009bc00000000000698800047a02d06bd1b40b1880000000c4400000006d7d69600015205631bfa0d98b7a9f69cd227d00008d1ad7011680000000000224800000000000000000154000028b800000021347ac8000000288915498002ee400005e8f4434f2d8a5fba01679c0b9a9bdec51b9b20a206ad0e463025f2000016f0000000070646800007ba8a2acdc090aa1895213bd000047831d2a3253a31130000a9b177a7ec72f98a2a010dfe000000030a2f520000b542eba03e71601f477c8672680258088d03049022f92542102cbefa3c66e5d2c49bbec0390a1c32419606e93925864078000c260d0406c4000b662df5b9ad64571e916400000001b300009ef1a65b2580008e9956200000006e5a1540000000648847c0002aa0000000000000000000000c0d9616000000019e000000000000001e7a8fe0107000000000000004f400009820000000000000000000000000000000000022b62bf6e0857ad0ac5a02996b015eec4a130c60000000bd20000ac688d400021f517e0bbe79883682b09382359800000000006af2229aa32858000033b4726f2e7b705e659490632582ac615eafe48484dc2c2c8000a34e77a1d589d6a7d07fc4ededb4a9d49920003106bb6c000bb140002a0dd2eb01c0009bc420a0002b004d3016e00000000002d60000000000000009d593705f7a2f0089400000000004b280000000b7e0000d865081ca0000000092d80000000be22a02ec7840aef20ebe41a43c000091100001158000c10800016baacf00008c2000297a0002372ad9ad5655a95b983b05d82d697fe19480000000000b13a16800006a0b574000c23275e1cd23524c8171070900004d700d200014861ada4d00b19b110000406735e15aaaf9d2c145df24adf25f0534af5a000310f9b2de1e000
  | 50 => 0xc6798849ae0000000006f18000000247a00022b40000000000207800000003878ace2642b4468aafbf82729ea646000000000000e3000075e96b20001c224900454c070b3300000000000ecf00008020e7866600001cf00000000ccb07600000000031e2a00000000001d7627a4a050000000000000001480009cdc00000000000000000a45a478ab25b7c4188a527cb20f9b7d800000000000000000be46bdbc2d0ed23f189db4622f2435b940c79e121008420c61a426bdab6cd600aa16a01a0403a052ac943d20000000000000000000000396000086e27cdac40001d8c6a140005bf475d6c70cc38c6dea2272a17e53facb00002f46a6f01060000c3eba00000aea400085415f88b48d2800026b96f81176000172a00010de00026c390607e06b7a60a5be02c9598a6927b38000a0f02ea2bfa82400000006d70000000000023a800009f2132657237fb49000000030f8af5303ac29032079a134d52c1dde0002c1c23588648928ec0000013e56f5b28ae5a50258d00000001e301ba0000b32978eaa29e5c00001f3aa10a6c00001970002d2637946db2042177aa3a8c8a3700000001e6aafb603c00000007240806000000005c05841c89f5254a000000020d4c3f8000000000086700000000bb4000121ec1196200002ee600006f15ea67e6b38a0a82f2a6e1a56059b71e000000000000002100000000000020bc7d680009b8c0005a887e85d601d161003820000000a1ae73457e658d0000000626800071c09f5787240c0000000738d7189244e4c440287ac07c0007978000000105836697c0a6c9b7836e49dd02d2c176a0571e000231585091486e401c8712825a4989f1200011ee5b2000091a8000371000016187ce0000000a1b82600001197a5180003a9c4341588b84c321a9e8122d573f7020696170c4be91e3a6c40c2c000000037880007e08aa85e75a02961c0000a7400060d0000a5f07d669d8d3e78da88680a2fa1478000000000006648000669a9d87e602804ca8a5700000000000fbcaf2447e00024043792883431a51460380007345f9600015960eb09fa51215e05c92bcc39a90460001bd476f80000001fbc00000008af58eab5a16f000000006a59dd40001a20402b107b238000000000024400000000000618800000000000001b1400000003e68ada0cc034854d0000b291c940002c2c84148ae00000000001192000131000000009eb208ca75245f00003ce000072a349c000c1c89d808ac1b47524ae0408133e00000003c3c294b1d800014400000000000524d9ec00000007f680006250000351810219080000000000000182489bc000c258000441120218a58800000f8ab44284727d80002c2061528200009d4abeb0002e2e00007f50002c539cd686d8a016b600024964d21c3a422012eb33105200026f662c1f9
  | 51 => 0x60e00004ca126854e00009eee9640b030d400000009539f320002a46190128000000c788bac643865178aba9b9432222332ad9aefa7e00000000000aaa12b00000000000000000006280000000a168c5ab4eae70000000000000005b494aa380235cae74bcf39a1f4e644400000000000001012c065766679246e111305e2ff91beb83994200000007bb800000001f500000000002aa200027275bcdad0626c0000000bf61590000c3f18b99a240002d98000b9322569e580008fb178a197ca70adcb0ba7866ff56391a0c45c9e6386a111250b5d9c4dd187081823b0a820d2686f27ee157e72200011da20e895409d9307a57158eabc041e6d50626332a7124dbaf9bbc100369cb659bc0f0000736286cb609332bb110be73da4e8798400025b89d263a185a1cb2c4aa7b057e5d800160002370000000000005c80002bee277d1b5106000098c0278b3d91113ba98dc000193d519800039481fc000000061a62c51e486fc88298ee372dc0c000000036af0fa3ade49eafa67486bb0e5e0000000aa15a5242a51d0000294e0002a28471b00ab10a53a958800a5712724a6b673e1ea9e4003c8000beaa264140d49c000000093e8000bf080005a48b9c28b00006f0580847c00003c5ad32a6084b0719813627340009d1d2046ac2328b6b92da3c28eca309800091986ae00000000a90000bed00000000000adc06930000236000000000000007484000b47800014f8d5a30382526f298c8c3d2868aa9000083040000000000385113c481800000023fe52384fb9ef575f58fd76c56c00003d18de80000000af813e24ed181ea03079a00002547770a140000000000085c00c00004ee80007abd3a6567e70647740005cb2a96a26962a8531d170899e9e1392d2a82bd1d80000f3e2428c02b1100000000000000000000009820001dca000209307500008ec95a09cda84e2be87bc3fa9e1a83001e5b67905415980ca00009aa25e2880000000000000000000000202da3a000248c0000a54000000088322d445f80007ba80000002d6e4454d528a48c248e60d8e1d0e38900c800050b9bea41f19300d8c0001864faca2583f855080008c780004aa0000740534073a800000007740001f80af49ce2bb39df54018e1d08b4000713220901be7f883a914400005f4a79a5b81c51ec5a24000007e80000000000000016b00029eb3e8800000000005b780001cd8d6b000000000000000002506980a1b459da80000000004fdd33b6934000000000000000007d82c4f3bc09be848abe2749a32cb98a1444479bbe7c298c56a72fbd5de2848885a9d241b2f268e82d0a1ae87523651a59c0ca1c04ff13e405a299c3f428be8c5c146b0b88cb620a516037586c1911c76870a7c20231c683b791619331dae37f000008c00000000ae92990000459e396b4
  | 52 => 0x41f438e909ce84b0c99960000000000000000012fe90d000078c945a04c98ac0000c40000102a81180005d000003c5000000000000f0070001611ad4be18b76c32992aca1bf6000000039501eb0001bde245820780b06a79d80ee48a205580001d1341f80fa858309c8910ad17af18fea8a84e60000d5e00000000832b7f0002c113c81b44b701b7000000002abc0000000000000002a000000000003de51a27fa3530dac8880ac000030160000bd6b0f9c4205d0000000076e908a76cae7d2f900010aa765205c646871200005f2234ab9ca008a8a72b1c28b80aebc8b9800000000003b14f5c0002dc62f6183a5faa9668c99b2c53305230001ab46bb80002c8119a8bb1f5b5e6000051df031ac95a3009b9a3cc1f0ea95fe80008f3000007b17ae7530000af29f1ec3b00000001fc65eee8b692a8000000000024c8000b77a03433e175a0001d359b12f1666aa8874f091ec4fe6874536860032d1efd5a2ae300000dfb00019ad00000001730000bf100a2000000000000004b9000000000000000000000000000000008430000000000000024af815c000424800000000006e840004ff8000000000071723c2aea0e620000000000233a8c849e4bd3aad6a900e42a77898c0bf98a4000045200013b689b5294999000000006838be9a9300000005559650b9908070c50ccc736c0009901acc9d9018e087204c9ab80000000a8f7010d80a550dc884dc00029448235390000014189600009c09d10f2a0dd046abe3cb8c9d38c4e0c321d0000000012ad57004b2a9c1dda1b200017080000000998ca8c26b80000002c0e114000000000b200027e8671ae1ebd3400078d13e09558204bb6a7f20b818bda6187f773381760000000be78d720b3272c85b2669503a04034e9b8f61526b500028367152d5e1fea1d20000c1e618288e09f80006ce0df4b1dc0009206459984000000000008a90000820800000000000000000000000000000000000b640000d5381b19da0000000000000000028229c4000082b40000001816aa4c8404fb00000001a7c5f10000971c00024d8000a2896e612a40001fba4864b98000b7680009639b880002e407a580008d782d8aa6400000027a061d8000c051af000030080000b721fc800000000000001c725b70a2800000000000000000000059b000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x853671149420429d380a4a1021c954b6150810a6aea30a8408635651854204392a90c2a10214e5d76050810e52a5b028408539751814204394a90c0a1021ac184605081087ce9b28840845e73194420422eb98ca210211d9c465108108f4e0328840847a70997320421f3a0cb990210f5d065cc81087ce9b2c640843d74d96320421f3a0cb190210f5d0658c810c5ac9294640862d6454a320423db82ca990210f9d0654c81087ae832a640847975181320432d298c0990219654c604c810cd4a430264084f171181320421f3a6ca190210f5d3650c8108f2e0b28640843e74194320421eba0ca190211d9c4650c8108eaeb308640843e7498a510421eba4c5288218798f4294410c3ac7a14a20861e6350a510430eb1a85288218b9894294410c5ac4a14a20845e73d96410422eb9ecb208211edd560904108bce7b28820845d73d944104237396ca208211b5cb65104108f2e0b28820861e5458c410430eaa2c6208218b9516210410c5aa8b10820863954980410432d29cc1188219654e608c4108f6eab00620862d6550b210422f39ecb10821175cf6588410aaae728c420847b755822104317b2a8490821555ce5148410e4a8528a420843e74d94210421eba6ca10821179cf65084108bae7b284208479705942104316b24a4108219358e5208410c5ac8a90420864d635482104334a94c0108210f9d2629401087ae9314a00843f74586500421e3a2c328021179cf65900108bae7b2c800863554986400422f398ca20021175cc65100108dce4328800846d72194400421f3a6cb180210f5d3658c010caaa730c600843e74194300421eba0ca180211b9c8650c0108dae432860085597054c30042acb9ca01802156dd5300c0108eeeab0c400865863941200421f3a6ca100210f5d365080108bce7b28400845d73d94200423ab8aca100210f9d0650801087ae8328400845e73194200422eb98ca100218b5925208010c9ac7290400862d645482004326b1aa4100219954a6108010caacab1e200847576d4b1004392a9285880211d5da51840108f2edaa420084797614e100429cba0a7080215a5c853840108f2eda94200863965d0a100431cb2a8508021ca54942840108f2ed28c200855a73946100431bb2ec8880218dd9464440108eceda92200863765d09100425a3b284880218dd954244010e4aa4a12200857175d0110042b9baa6088021d854a2044010ba6e6902200863b65d91100431db28c8880211e9db54440108f4ec29a20085397414d10042b4b90a6880211e9db5244010c76cba1220084b876509100431db2a8488021ca54942440108f4ed28a200855a7394510042e8b9ca2880215c5d44144010e62a820a20085d17310510042f0b9082880215c5d63144010b60e898a2008750534c510043b0a944288021e85092144010
  | 1 => 0x104430e2a4c78822187d5163c4110c38a8b1e20884da73d93104434daa4c788221a615263c41109b4e7b16208869a63d0b104429c3aa8588221a698d42c4110d52c4a1620886d2638871044370b144388221b498d21c4110f428490e20885347550a10442e939ea108221b858a2084110ba0e6904208845d73987540421fbb2a82a021875516315010c5aa8b10a80861e6458c540432731cc42a0219358e6215010c5cc8b10a80864e635885404326b1ac42a0218b9d16215010caac7308a80866562984540432d31cc02a0219658e6015010cd4c5300a80866962980540421f3a4c5a98210f5d262d4c1087ce9314a60843d7498a530421f3a0c4a98210f5d06254c108ece2312a60847a70189530422fbb2a629821875915314c10c9aa6b10a60843d72990530421fb92c8298210f9d26214c1087ae9310a60862e649885304316b24c4298218b9d26214c10c5ae9310a60862e645885304316b22c4298218b9d16214c10c5ae8b10a608635649845304332b14c2298218e5926014c10cd2c5300a60846e721974304236b90cba18211e9c26590c108dce432c860846d72196430423dbaac1218211d9c66550c108dce432a860846d721954304237390ca218211b5c86510c108ece2328860845d739875204317394c9290211e1c1639481087ce831aa40843d7418d520421f3a6c2a90210f5d3615481087ce9b02a40843d74d81520422e39ac0a90211bdd95214810c5ac8a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204316b24c4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c74c9300a40863964980520432d31cc0290219658e60148108bce632e840845d73197420423d380cba1021479cc54d0810a3ae62a6840853a701534204296b96cba1021479cc65d0810a3ae632e840852d72197420429d380cba10210f9d853d081087aec29e840852e7214f4204296b90a7a1021479cc52d0810a3ae629684085367114b420429d380a5a1021179cc65908108bae632c840847671196420423d380cb2102117dcd65508108b8e6b2a840845e73195420422eb98caa10211e9c0655081087cedaa2840852e72d51420428f398a8a1021475cc5450810a5ce42a2840853a7015142042973a4a4a10211d5d46150810c6aa830a840847975d81420423cba8c0a10214b5ca6550810a3ee6b2a840851c735954204297b92caa1021479cc6550810a3ae632a840853a701954204297396a6a10214b5cb535081087cec29a840843d7614d4204297390a6a10214b5c85350810a5aebb12840843e769494204296baca4a10214b9da5250810c5ced292840852e7654942042963b2a4a10214bdc55250810a5ae2a92840843e76149420428f398a4a1021475cc5250810a5ce429284
  | 2 => 0xc0202218d15261cc110c68a8b0e60884f271d93304431d32ea9982218e99454cc1108f2ed29660884797614b30442acb98a5982214e9d742cc110a70eaa16608874852ccb30442ac3aa65982213c9d661cc110ce4eb30e60886b35498730443582a4c3982213c5ca61cc110d668530e60886b1429873044279bb443982213cdd921cc110ae0ea90e60887a14248730442a6392a7182210fdd1654c110878e8b2a608846f725953044236392ca98221179d8534c110e36a89806088718544c0304423d3aec8182213c1c5640c110c74ca2a060885d17194c304423dbb2a6182215a1c9530c1109b6eca98608871b5454c304438c2a2a618221721c9530c110ba6e2a98608855b7654c304432dbb2a618221c6dd1530c110e30e8a98608874b7254c30442ac392a618221d21c9530c110a90e4a98608855b7154c30443a9b8aa6182219654d620c1108f2ed29060884797614830442acb98a4182214e9d7420c110e32a7a10608853875508304438ca9a8418221aa589420c1109b2ed190608855b758c830442e8b8c6418221565d4320c110e90a419060885d1710c830442acbaa6218221d454e210c110ae0ea9086088751534843044370b124218221e8509210c11087ceb326408843c75593204421fbb6a9902210f5db54c811087eec2a6408843d76153204422f39ccb10221175ce6588110a5ae42a440884da7399620442acb9ccb102211e9d764881109e0e2b24408863a6515220442d4b90a9102213c9c663881108f2eda9c408847b7654e204432c31aa7102215a1c95388110ab2e6294408853a75d0a204429c3aa8510221369ce6188110ae4ea30c40885707548620443d0a1243102210f9d3654811087ae9b2a408843f74595204421e3a2ca9022117dcd6548110c3ea9b1a408861c54d8d204430faa0c690221871506348110c98c7a92408864c63149204431a2a6c2902218d15061481108f0eab2240884d873591204427838ac8902218e1975448110c70ca2a2408865865d8d204426d39cc6902213c9c66348110cb0ca31a408865a7518d204432cba8c690221a6d506348110d30a831a408847a76d4d204432c31ea6902211e1d95348110cb0c6a9a40885687254d204436431ea4902219618e52481108f4ec292408855973149204432c318a490221cad505248110d90c6292408853a75d09204431c32e8490221a618f4248110a70eaa12408863865509204434c31a8490221ca1494248110da0c7b0a40886d363185204433832c4290221b418e2148110ae0ea90a408867065485204436831a4290221e8509214811087eedaa0408843d76d50204421fbb0a8102210f5d85408110a5ae42a0408861f5498c204430e2a4c61022187d516308110c38a8b18408863754984204431a2a4c2102218dd516108110c68a8b08408861f5498f
  | 3 => 0xd365cc91087ee8b2e648843c7459732442a6b98a5992210f9d3658c91087ae9b2c648843f74596324421e3a2cb192210f9d0658c91087ae832c648843e75992324421e3aac9192210fddb548c91087aedaa4648843f76152324421ebb0a9192214b5c8548c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c910a5ae42a2648845e7694d324431daa6c0992218e153604c9109e4e3b02648863b54181324431c2a0c0992219694c604c91087ce9b28648843d74d94324423ab8eca192210fdd1650c910878e8b28648843e74194324421eba0ca192211e9c0650c91087ceb320648843c75590324421fbb6a8192210f5db540c91087eec2a0648843d76150324431baa4c2192218d152610c9108e8eab08648863754584324431a2a2c21922195d4d610c910ca8a6b08648866752584324431daa4c0192218e152600c910c76a8b00648863854580324432da9ac0192219614d600c910cd6a4b00648863854983414431daa0c0a0a2187d526310510c38a9318828861f5458c414430e2a2c620a218bd526210510c58a9310828862f5458841443162a2c420a214d1d54110510d4ac4a0882885b070504414431daa4c020a218e1526010510c70a9306628863854583314432c29ac198a218ed52608c510c70a9304628843e76d51314421e3b6a898a210f9d8544c510878ec2a2628843e75993214421e3aac990a210fddb54c851087aedaa6428843f76153214421ebb0a990a214b5c854c8510a5ae8296428852e7550b21442963aa8590a21361cd60c8510c6cca2a442885647254e21442aab98a510a214d9d74288510a68eaa1442885d273d8221442b93a8c110a214b5c85448510a5ae8292428852e7550921442963aa8490a218e1536048510c70a830242885a572151214423a3b2a690a211d9d85248510aaae629242885a574149214429b3ae8490a218d1974248510b4ae9212428853475509214431a32a8490a21c9dd54248510b4ceaa1242885a47550921443923aa8490a21c9d954248510e48caa124288727535092144392a9a8490a21e89c14248510f42e0a1242887a142d8121443d0a10c090a210fddb540851087aedaa0428843f76150214421ebb0a810a2187d526308510c38a9318428861f5458c214430e2a2c610a218ed526008510c70a9300428863454987404431d32ea9202213c9c66390110a70eaa1480886a96250a404426d39cc3202214e9d64190110a74ea20c80885a97210640443d0a1243202218dd506150110c70cbb22808863865d51404423d3b0a8a02218e1945450110c70cba12808853875509404431c32a84a0221aad8942501109e4ea30a8088672751854044359aa0c2a0221ac15061501109e2e430a80886b3421854044358a10c2a02213c1da21501109e0ec90a80887a142485404431c2a4
  | 4 => 0x58a9b12a68862f5418953443162a0c4a9a210f5cb6454d1087ae4322a68862f64d895344316326c4a9a218bdd36254d10c58e9b12a68843e74189534421eba0c4a9a218bd906254d10c58c8312a68862e741895344316ba0c4a9a21995c46254d10cd0c5b02a68845f7654c53442a6392a629a210f9d26214d1087ae9310a68846e72d974344236b96cba1a218e15260d0d109e0e2b06868846f725954344236392caa1a211d9d76150d10c6ea830a868863b541814344237390ca21a211b5c86510d10c68a9308868847475584434431a2a2c221a218e1526010d10c70a8b00868852d72d935244296b90c9a92210f9d263d491087ae931ea48843f7458f524421e3a2c7a9221561cd609491087cedaa2a48843e76151524430faa6c6a9221871536354910c3ea831aa48861c5418d524430fb26c6a9221871936354910c3ec831aa48861c6418d524432631ec4a92218d1936154910c70c9b02a48865863d815244296b96a8292214b5c85414910c3ea9318a48861c5498c524430faa2c6292218715163149108deeca90a48854c73548524430f324c629221875926314910c3cc8b18a48861d6458c5244326392c62922196dc16314910cb0e0b18a48863664584524431ab22c2292219598d6114910caac6b08a48843e74184524421eba0c2292218e9916014910c72c8b00a48865a63580524432cb1ac0292219c585601491087ce8300a48843d74180524422f39ecba1221175cf65d0910c70a9306848847875583424431c2a2c1a12213c1c560d0910a3ce7b2e848851d73d974244296b96cba12214b5c865d0910c5ae432e848863970197424421f3b4a7a12210f5da53d091087eeca9e848843c7654f4244297b92a7a12214b1c953d0910a3ee6a96848851c7354b424428f398a5a1221475cc52d0910c70cb306848853875583424431c32ac1a12216c1c560d09108bce632c848845d73196424431baa4c3212211d1d56190910c76a9304848847875582424422fb9acaa1221171cd65509108eee2b2a848847b70595424421f3b4a8a12210f1d9545091087ceb32a848852d72995424421eb94caa12218b5ca6550910a3ee6b2a848851c735954244297b92caa12214ddc56550910a76e0b2a848863970195424421f3b4a6a12210f5da535091087eeca9a848843c7654d4244297b92a6a12214b1c95350910a5ce429a848852d7214d424421f3b4a4a12210fdd95250910878eca92848851f73549424428e39aa4a12210f9d85250910a3ce6292848851d73149424429d3acc0a12218e1966050910a70eab0284886386558142442cc39ac0a12216c1c5605091087ce8328848845e73194424422eb98ca212210f9d6641091087aedaa0848843f76150424431a2a4c2212211d1d56110910c70a9300848847875580424421f3a6cb992210f5
  | 5 => 0x846f76548528430f324c629421875926314a10c3cc8b18a50861d6458c528432c382c6294218d9916114a10c6ac8b08a50865663584528432ab1ac2294219658e6014a10ce2c3300a50845e73d97428422eb9ecba1421179ce65d0a108bae732e850851e73d53428428eb9ea9a1421479cf65d0a10a3ae7b2e850852d72d97428428f39ccba1421475ce65d0a10a5ae432e850851e7314b428428eb98a5a1421179cc6590a108bae632c850845e73995428422eb9ccaa1421479cf5450a10a3ae7aa28508637541854284278b80c2a1421479ce6550a10a3ae732a850852d729954284297b92caa14214bdc95350a10a58e4a9a850852e7214d4284296b90a6a14210f9da5250a1087cec292850851e73149428428eb98a4a14218d9946150a10b62e030a85086b06198142842cc39ac0a14216c1c56050a108bce6328850845d73194428421f3a4cb994210f5d265cca1087ce9b2c650843d74d96328432d298c0994219654c604ca1087ce9b28650843d74d94328421f3a0ca194210f5d0650ca10a3ce7aa4830843e76951418421ebb6a820c21479cf5410610c5ea8b10830862c545884184296ba4a590c21361cd60c8610a5ae929243086a96250a40842d838a8520421369ce6190210b52e420c810847a761514084355b1284a04218d95161102109e4e3b2661084797694b308423cbb0a598421565cc52cc210caca6b08610855b7654c308432dbb2a618421561c9530c210cb2a6b1061084797694830842acb98a418421c654f420c210e32a6a1061086a962508308426cbb4641842156dd6320c210ab2ea19061085d1710c8308423dbb2a7104219618d5388210ab2e629441084da73986208426c39ac8904213c1c56448210cb6ca31a41086597518d2084369388c690421b45c463482108f0eca9a41086586354d208432c31ca4904211e9d85248210ab2e6292410865863149208434c31e8490421a618d4248210e50a4a12410866552584208432ab2cc7884219559563c42109b4e7b2621086596598f108432cb2ac788421369cf62c4210d34c7a16210869a6350b1084354b128588421669cf60d5110a6ae3b1ea88853970d8f544428f398c5aa221475cc62d5110a6ae2316a8885397018b544428f39ec3aa221475cf61d5110a3ce7b06a88851d73d83544421fbb2a82a2211b9c861151108dae4308a88853970d8c5444297390c62a2214b5c86315110a6ae2318a8885397018c544429cb86c42a221479cc6215110a3ae6310a88853571188544429cb80c42a221479cf6015110a3ae7b00a88852e72d805444296b96c02a2218ed896015110c72c4b00a88843e7498b534421eba4c5a9a210f5ca6494d1087ee4b24a68843e7498a534421eba4c529a218d9916194d10c74c8b04a68843e76d51534421f3b0a8a9a218bd536254d10c
  | 6 => 0x2c42973b4a4a16218b9da5250b10e4ce3292858870e5354942c4386a9aa4a16214b9d95250b10a58eca92858843e7614942c428f398a4a1621475cc5250b10e34a7b02858872952d8142c438d298c0a1621ca5486050b108bce7328858845d7399442c422f398ca21621175cc6510b10caaa730885886555358442c421f3a6cb196210f5d3658cb1087ce832c658843d7419632c430f324a71962187592538cb10c3cc8a9c658861d6454e32c432aa9cc3196219554d618cb10cb4a7b02658865a5318132c432ca98c0996210f9d3650cb1087ae9b28658861e6494c32c430eb24a61962187991530cb10c3ac8a9865886555398432c432b29ac2196219554d610cb10cb4a730065886595398032c432d29ac0196219654d600cb10cb4a7304838865a5358241c422ebacc620e2117dd563107108baed298838845f7654c41c432729cc420e219354e6210710c5ca8b10838862d5458841c432729ac420e219354d6210710e2aa6a0883886a56250441c432d29cc020e219654e6010710c72a8b00838865a5358041c432ca9ac020e219694e608c710cb4a6b04638861e6494f21c430eb24a790e218799153c8710c3ac8a9e438870e5350b21c4386a9a8590e219694e6088710cb4a6b0443887455354a21c42aab98a510e21c554f4288710e2aa6a14438870e5350921c4386a9a8490e21d154f62487108ecec29243885557314921c438aa9e8490e21d154e4248710e2aa6a1243887265250921c43a2a9a8490e21c9dd54248710e48eaa1243886a76550921c4393b2a8490e21c9d4d4248710f0ca6a1243887255350921c43c2a9a8490e21c154d4248710f46e0a1243887a07050921c422ebacc610e2117dd563087108baed298438861e6494c21c430eb24a610e2117dd95308710c3cc8a98438861d6454c21c4316b24a410e218b5915208710cb4a730043886595398021c432d29ac010e219654d6008710cd2a4b00438852d7215240c421f3b4a8a06219554f6150310caaa630a818843d76d5040c4296b90a8206219594d61cc310caaa7b0a618861e6494f20c430eb24a7906218799153c8310c3ac8a9e418862d6494b20c4316b22a5906219554e61c8310caaa6b0e418845d75d8d20c422eba8c690621179da53483108b8eca9a418861e6494c20c430eb24a610621879915308310c3ac8a9841886565398420c432aa9cc2106219594d6108310caaa6b08418865663587548432cb1cc1aa4219c58660d5210a3ce7aa4a90851e73d91548421fbb2a82a421479d35394e1087ce9314a70843d7498a538421f3a0c4a9c210f5d06254e108beeca98a70843e74988538421eba4c429c211b9cb65d0e108dae5b2e8708659539834384278b84c321c211b9c86510e108dae4328870863a64982528431cb24c1294210f9d36354a1087ae9b1aa50
  | 7 => 0x4900419cd965148020da0c728a40107515394520083d0a14a2900419618d5148020e5284a8a40106736554520083992a2a290041cc5515148020da0c6a8a40107525354520083a8a9aa290041e85095148020ea6c6a8a401067263545200833831aa290041d418d5148020ca0c6a8a4010763625452008399a12a290041d89095148020e6284a8a4010761425452008390a12a2900419558e61d5310cb4c6b06a9886726158354c421fbb2a82a6218b5516215310c9cc7310a98864d6398854c4317322c42a6219398d6215310c9ac6b10a98862e7458854c432d31ac02a6219658d6015310cd4c4b00a9886696258054c421f3a4c5a9e210f5d262d4f1087ce9314a78843d7498a53c42a7390a929e21535c85494f10ab2e1b24a7885567119253c428f3a4c529e21475d26294f10ab6e0b14a78851e7418a53c428eba0c529e21559c46294f10ab2e0314a78851e7418653c428eba0c329e21539c86194f10a9ae430ca78851e74d8253c428eba6c129e210f9d06254f1087ae8312a78845e76d5153c422f3b0a8a9e21539c85454f10a9ae42a2a7885547159153c428f3a4c4a9e21475d26254f10aace3312a78855b7058953c428f3a0c4a9e21475d06254f10aace2312a7885597018953c428fba2c0a9e21471d16054f10a9ee4b02a78854c7258153c422fbb2a629e211b9c865d0f108dae432e878865a5398243c432d29ac121e219554f6150f10caaa630a87886565358443c432d31ac1a9621879925394b10c3ac929ca58861e6454e52c430eb22a7296218b9ca6494b10c6cc930ca5886356498652c422ebb4a629621879925314b10c3ac9298a58845f7654c52c430f322a629621875915314b108deeca90a58862d6454852c430f324c629621875926314b10c3cc8b18a58861d6458c52c4316b24c4296219558e6114b10c74c8b00a5886396458052c432d31ac0296219658d6014b10ce4c2b00a58845e7399742c422eb9ccba1621179cc65d0b108bae632e858851e73d5342c428eb9ea9a1621479cc54d0b10a3ae62a6858852d72d9742c428f39ccba1621475ce65d0b10a3ce632e858851d7319742c4296b90cba1621479cf52d0b10a3ae7a96858851e7314b42c428eb98a5a1621179ce6590b108bae732c858845e7319642c422eb98cb216219554e6190b10caaa6b0c858845e7399542c422eb9ccaa1621179cc6550b108bae632a858851e73d5142c428eb9ea8a16214b9cb5450b10a3ce62a2858851d7315142c4297390a8a16214b9d25250b10cb4a7b02858865a5318142c428f39ccaa1621475ce6550b10a5ae532a858852f7259542c428f398caa1621475cc6550b10a5ce5a9a858852d72d4d42c4296baec4a1621c394f6250b10e1aa7b12858851e73d4942c428eb9ea4a16210f9da5250b10e1ca7292858870d539494
  | 8 => 0x7530c020ab2eb29860106596594c300823dbb2a6180419698d530c020cb2caa98601071a5454c300838caa2a61804156dd9530c020cb6eca98601055b7154c300823dbaac4180419654d620c0208f2ed290601053975d08300831cb2e8418041c654f420c020a76eaa10601063965508300838ca9a8418041aa589420c0209b2ed190601055b758c830082acba86418041e2508320c020ce2cb2886010751539443008338b2aa218041cc951510c020e62a8a8860107525354430083a8a9aa218041d49cd510c020ea2e6a8860107526354430083b1312a2180419c589510c020ec2c4a886010733425443008398a12a218041d48c9510c020ea064a88601043d76953200821fbb2a9900418799253c8020c3ac929e401061e6454f200830eb22a790041c354d42c8020c6cc928e401063564947200831b322a3900418d59151c8020e4a84a8e401070d5454f2008392aa2a390041d154d51c80208daed294401057171d4e200823dbb2a7100419698d5388020e34a8a9c40107195454e200832dbb2a710041961d953880208f2ed294401053975d0a200838ca9e85100414edd54288020e32a6a1440107515394620083992a2a310041cc5515188020ea4a6a8c401075153546200833931aa3100419c18d5188020e6684a8c401073142546200830f2a6c690041875536348020c3ca831a401061d5418d200822f3b4a690041171da53480208bceca9a401062f65d092008317b2a8490041a318d4248020e1aa6a12401065763945200832a31ca29004195d8d5148020ca8c6a8a4010725425452008327b9eca90041931cf6548020c5ecb2a2401062f655512008327b2ec69004193d946348020c9ecb29a401064f6554d2008386aa2a69004199d965148020ccecaa8a40107255454520083a2a9aa29004196dcf6548020cb0e7b2a401063b65951200831db2aa89004196d9763480208f2eb31a40104da7398d200832db28c690041965d46348020d34a831a40106995418d200823d3b6a6900419618f5348020ae2e3a9a40104d87694d20082acbaca69004196d9653480208f0eca9a40106586354d200826c3b2a69004196d955348020e34a8a9a40107195454d200832dbb2a690041569d95348020ab0eca9a40106587654d200822c3b2a6900419654f6248020e92a7b1240106586394920082d4ba4a490041b218e5248020a72eba12401063b65d09200834c31e8490041c654f4248020b52e921240106c86390920083a4a9c84900414edd54248020c76caa12401069863509200838ca9a8490041b218d4248020e92a6a1240105ab755092008395baa8490041aad954248020e56caa12401078b63509200835531a8490041aa18d4248020f10c6a124010688635092008395a9a8490041e294d4248020e52a6a124010789535092008384a9a8
  | 9 => 0xae732e821045e73996410822eb9ccb20841179cc65504208bae632a821063954d81410832ca9ec0a08419c5476050420cb2a6302821067151181410822f39eca20841175cf65104208bce7328821045d73994410822ebacc620841879526310420c3aa9318821045f7558c410830f2a2c6208418755163104208beed298821045d7694c410822fbb2a620841175d95310420c5aa9310821064e539884108326a9cc4208418b9516210420c5aa8b10821064e535884108326a9ac4208419598e5110420caac7288821066562944410832b31aa2208419558d5110420cccc4a88821066562544410831d2a4c0208418e5526010420cb4a73008210659539804108338a8cc0208418e9516010420c72a8b00821065a53580410832ca9ac0208419c9456010420ce2a2b00821043d75993210821fbaac9908410f5da54c842087eecaa6421061e6494f210830eb24a7908418799153c8420c3ac8a9e421070e5350b2108386a9a85908418d99251c8420c6ac928e421063664547210831ab22a390841c950951c8420cb2a730642104d873583210832ca9ac190841aa50960c8420ce2a2b06421070e535092108386a9a8490841c950a514842087aeb320421043f75590210821ebb4a8108410fdd954084208baeb318421061e5498c210830eaa4c61084117dd56308420c3ca8b18421061d5458c210822ebb4a610841879925308420c3ac9298421045f7654c210830f322a610841875915308420c6cc9288421063564944210832b31ca2108419558e5108420c6cc8a88421063564544210832b31aa2108419558d5108420c74a9300421063954980210832d29cc0108419654e6008420ce2a3300421063a54580210831caa2c0108419694d6008420cb2a6b004210672515802108316aa2c520041179ce65100208bae7328801045e73194400822eb98ca200419354e6210020c5ca8b10801064d535884008333312a220041995895110020cb4e6b2e601063965953300831cb2aa9980415c5c753cc020cb2cb29e601071a5454f300838caa2a7980419654d62cc020a72eba16601063965d0b300838ca9e85980414edd542cc020c72caa1660107195350b30082acbae65980419659732cc020f1285996601055b754cb300832cb2a65980419c59651cc020ea2a728e60106716554730083992a2a398041cc55151cc020ea4a6a8e6010751535473008338b12a398041ccd0951cc020e6284a8e60107533254730083a8992a3980419354d628c02087ce9328601043d74994300821f3a0ca180410f5d0650c020c5aa9310601062d54588300832729ac41804199989510c020ccac4a88601065b654c0300832cb2a6018041c6951300c020e32a89806010752514c030083a8a8a60180418e596540c020c72caaa060105597598c300832cb2cc6180415c5c
  | 10 => 0x43d76952320821fbb2a9190410f5d9548c820c3cc929c641061d6494e320830f322a71904187591538c820cb2a7304641047b75582320832ca9ac1190418e953604c820c72a9b02641065a53d81320832ca9ec0990410fdda540c82087aed2a0641043f76550320821ebb2a8190418b595420c820c74a9300641063954980320831d2a2c0190418e551600c820cb4a6b006410659535803208354a12c0190418795263d4420c3aa931ea21061e5458f510830eaa2c7a88418799253d4420c3ac929ea21061e6454f510830eb22a7a88414d9d35194420a6ae9a8ca21055673d4651082aab9ea3288410fdd16394420878e8b1ca21055673d5251082aab9ea928841559cc5494420aaae62a4a21053674d4e510829aba6a728841c59525394420e2aa929ca2107165454e510838aaa2a728841d41c15394420a6ce829ca2105357414e510829abae8528841c594f4294420e2aa7a14a2105377550a510838b29a8528841c554d4294420aace6324a2105557319251082b3390c9288415c9c06494420ae4e1b1ca2105377458e510829a3a2c7288414d9d06294420a6ae8314a2105567318a51082aab98c528841c9dc94294420a6ce9194a210535748ca51082b9b8265288411d5d83294420a6ce8194a210535740ca51082b938065288415c5c032944208bce6322a21045d73191510823b3b6a8a8841559cf5454420aaae7aa2a2104767615151082ab398a8a8841555cc54544208eceda9aa21053674d4d510829aba6a6a8841c59525354420e2aa929aa2107507094d510838b2a2a6a8841c55515354420ea0e0a9aa2104767614d510829b3a0a6a88414d5d05354420a6aeba12a21071653d09510838aa9e84a88414ddd54254420e2ca6a12a2107155350951082b8382c8a8841559cc6454420aaae6322a2105667219151082b9380c8a88415c9c36354420a6ee8b1aa2105347458d51082b2392c6a88415c1c16354420acce5a1aa21056572d0d51082b938686a88415c5c34354420ae6e0a1aa2105707050d510829b3a4c4a88414d5d26254420ae4e1212a210571709095108393b9284a8841c99894254420ae4e0212a210571701095108392a1664a88414d9d23254420a6ae9192a210572708c951082b8b8464a88415cdc132544208ecec192a210536740c9510829aba064a8841c95083254420ae4e0192a210571700c9510829b3a040a88414d5d02054420aace6102a21055573081510821ebb4a8288410fdd95414420c3ca9318a21061d5498c510830f2a2c6288418755163144208baed298a21061e6494c510830eb24a62884117dd95314420c3cc8a98a21061d6454c510831b2a4c2288418d5526114420caca7308a21065553984510823bbb2a2288418d9915114420c6ac8a88a21065663544510832ab1aa228841179ce65d04208b
  | 11 => 0x831b324c3a98418d59261d4c20c6cc8b0ea610635645875308338b0cc1a9841479d35394c20a3ae9a9ca61055671d4e53082aab8ea7298410fdd16194c20878e8b0ca61055671d5253082aab8ea929841559c45494c20aaae22a4a61051e7498a530828eba4c529841479d06294c20a3ae8314a6105567118a53082aab88c529841569c26194c20a3ee8b0ca61051c74586530828f3a6c6a9841475d36354c20aace3b1aa61055571d8d530822f3b6a8a9841559c75454c20aaae3aa2a61045e7615153082ab388a8a9841555c45454c20e34a8302a6107195418153082a7394c8a9841569c26454c20ab0e0b22a61051e74989530828eba4c4a9841479d06254c20a3ae8312a6105567118953082aab88c4a9841569c26154c20a3ee8b0aa61051c7458553082a6392c2a9841561c16154c20cb4c4302a61065862181530832db08c0a9841479d02054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a61065553584530821f3a4c4298410f5d26214c20c5ac9310a61063664984530831ab24c2298418d9916114c20c6ac8b08a61066662584530831d324c0298418e5926014c20ce4c3300a61067161980530823b38ccba18411d5c665d0c208ece232e8610475711974308236bacc5a18419354e62d0c20c5ca8b16861064d5358b430823cbacc1a18419654e60d0c20c74a8b06861065953583430823b38ccb218411d5c66590c208ece232c861047571196430823b38ccaa18411d5c66550c208ece232a861047571195430831caa6c0a18419654f6050c208f2ea302861065953181430823b38cca218411d5c66510c208dce4328861047671194430823ab88ca21841479cf54d0820a3ae7aa6841053671d53420829ab8ea9a1041479cc54d0820a3ae62a6841053671153420829ab88a9a10410f5db53d0820a6ce3a9e841053571d4f420830eb2ca7a10418759553d0820e30e0a9e841043d7614f420829b388a7a10414d5c453d0820cb2a7304841063954582420832ca9ac121041479cf5450820a3ae7aa2841053671d51420829ab8ea8a10410f9d85450820a3ce62a2841051d73151420829b388a8a10414d5c45450820a5ee5b2a841043e76d4d420829b38ea6a10414d5c75350820a3aeb29a841061f6594d420830fb2aa6a1041c31c95350820e30e0a9a841043e7614d4208297390a6a10414d9c45350820a6ae229a841053a7014d420838729ec4a1041c354f625082087eecaa0841061e6494c420830f322a6210419654e6010820c74a8b008410659535804208316b2a8599041c354d42cc82087ce9b2c641043d74d96320821ebacc9190410fdd5648c82087eed2a46410
  | 12 => 0xa1241879935310920cb0a7306649065853583324830f326a71924187593538c920c3cc829c649061d6414e324838629a85192418b195424c920cb6a63026490658531813248354a10c099241179ce64d45208bae7326a29045e76d4d514830fb26a6a8a418719353545208bcec29aa29061f6414d514830e320a6a8a411ddd95114520a68e8a88a29045f73597414822e39acba0a4117dcd65905208b8e6b2c829065853982414832c29ac120a41179cf65505208bae7b2a829045f73594414822e39aca20a41179cc65105208bae6328829045e7598c414822e3aac620a4117ddb53105208baeda98829045f7614c414822ebb0a620a4193d4e6210520c98a7310829062f5458841483162a2c420a4193d4d6210520c98a6b10829066562d44414832da9cc020a419614e6010520c76a8b00829065b53580414832c29ac020a419cd456010520c3cc9a9e429061d64d4f214830f320a790a418759053c8520e1ea6a16429070c5350b214832c29cc110a419614d6088520e1ea6a12429070c535092148392a16a290a419614f6048520cb0a630242906a942181214822fbb6a610a41879935308520c3ac9a98429045f7614c214830f320a610a41875905308520cb6a7300429065853980214832629cc5a02419314d62d0120a68e2aa4809045d73d95404822fb9acaa02410f9d8545012087eecaa0809053471550404832629cc59824196dce658c120cb4cba9c60906585398a304831d32e8518241c614f428c120c74caa1460907185350a304832d32c6518241e250a328c120cb0a6b0c609064f5318930482ad3aec6982411e9d8534c120ab4ec29a609065a7614d3048278b88c498241c614f424c120e30a6a1260906a86250930482ac3aa6498241e2509324c120cb0a7b0a609061e64d4f204830eb26a7902418799053c8120c3ac829e40906596314f204832cbb0a790241c699053c8120e32c829e409071853d0b204838c29a85902419614d61c8120e18a6a14409065663987540832ab1cc3aa0419598d61d5020caac6b0ea810659639835408338b0cc1aa041479cf5495020a3ae7aa4a81053671d52540829ab8ea92a0414b9cb6395020a74e1b1ca81051e73186540828eb98c32a0414b9c86195020a74e030ca81051e73d91540828eb9ec8aa0414d9c76455020a6ae3b22a81045e73185540822eb98c2aa0414e1c16355020a70e0b0aa81051e73185540828eb98c2aa0414b9c86155020a74e030aa81043f76550540830eaa4c62a041875516315020c6aa9308a81063554584540830f324c62a041879916315020c9ac7310a81063664984540832b31cc22a0419558e6115020c6cc8b08a81065663584540832ab1ac22a041999896115020cb2c7300a81067161980540831b2a4c3a98418d55261d4c20c6ca8b0ea6106355458753
  | 13 => 0x530c320e34a9a98619071954d4c30c82e5396a618641565db530c320cb2eda98619071a74d4c30c838cba6a618641d29cb530c320ab2e3a9861905ca7214c30c82e8b88a61864196d4d620c320e36a7a10619071b5350830c8354b128418641e250a320c320ab6e6a88619045e73987548822eb9cc3aa4410fdd95415220cd2c5300a91045f7654c538821fba2c229c410f1d16114e208ece3b2c871047571d96438823b388ca21c411d5c46510e20c3cc7a14a31061d63d0a518830f31a8528c418758d4294620cb4c7304a310659639825188296b90c8a8c418b9c86454620c5ae4322a31063a70191518831cb80c8a8c410f9db4254620878eca12a31047776544518822f39ecb20c41175cf65906208bce7b28831045d73d94418829ab88a820c418bd516210620c58a8b10831063b5458041882aab9ca310c41555ce5148620e4a8528a431072542545218821f3b0a8a04410fdd95410220b92e5a9a611047a7614d308826d3b0a698441569d8534c220cb4ec29a61107497214d308832c298c4984413c5c4624c220e30a7a1261107185350930883543128498441e250b324c220cb0a7b0a61106c9624c03088316b2cc9904418b59564c82209b6e6b2e411055873597208831cb2cc9904418e59564c8220cb2c729e411065b6314f208822f39cc3aa241175ce61d5120c9cc6b14a89065a63582544832bb1ec2aa2419518f6155120c6ec830aa89065763185544832a318c2aa2419c5c06155120cb0c7b02a89067061d81544821fbb2a82a2414d1c55415120aaee2aa6a69055471553534828f3a6c3a9a41475d361d4d20caec330ea69055970187534828f3a6c1a9a41475d360d4d208beeca98a69043f74584534821e3a2c229a41175da5414d208beecaa0a6905577155053482aa38aa829a41565c36414d20a9ae4320a6905567119053482aab88c829a41565c06414d20ab2e1b08a69055970984534828fba2c229a41471d16114d20a3ce8308a69051d7418453482a6b90c229a41955846114d20ab2e0308a69051e74d80534828eba6c029a41559c76014d20aaae3b00a69046d72d97434823b38ecb21a411d5c76590d20cb0a7304869065853582434823bb8acaa1a411d1c56550d208ece2328869047571194434832629cc421a411b1d56210d20c98a6b10869065853980434832c29ac021a419614e60d0920cb0a6b06849051e73d97424828eb9ecba12414b5cb65d0920a3ee6b2e849051c73597424829bb8acba12414d1c565d0920e30a7306849071853583424832c29ec0a12419614c6050920a3ce7b2a849051d73d95424828fb9acaa1241471cd6550920a5ee4b2a849052f7254d424828f3a8a6a1241c35c85350920a5cebb12849062c65d894248387a9ec4a1241c314f6250920b54e1b12849071853d81424838c298c0
  | 14 => 0xeab0a601859b74585300c2cc3a2c29806172dc9614c030b90e4b0a60184da76d45300c26d3b4a298061b4d86514c0309b4eca8a601859b74545300c2cc3a2a298061b4d85514c0309b4ec28a601859a74145300c2ccba0a298061729c8514c030b92e428a601875151145300c26d3b48298061365da414c030ab6eaa0a601855875505300c26d3b08298061365d8414c030ab4ea20a601855975105300c2e53908298061725c8414c0309b0ed90a601855a75c85300c2acbae4298061669d3214c030b32e990a601874952c85300c3c4a164298061369da214c0309b2ed10a60186c862885300c26dbb24298061361d9214c030e92a490a601878942485300c26d3b04298061365d8214c030ab4ea10a601855975085300c2cd3a04298061665d0214c030d90c410a601853970d8e54c8297390c72a641479cc6295320a3ae6314a9905367118a54c829ab88c52a641479cc6195320a3ae630ca99052e7218654c831ab08c32a6414e5c06195320a3ce7b04a99051d73d8254c822f398c2aa641175cc6155320a6ee2b1aa9905347158d54c829db82c6aa641479ce6255320a3ae7312a9905367198954c829ab8cc4aa64147dcd6155320a38e6b0aa99053b7058554c828f398c2aa641475cc6155320a5ce430aa9906356118554c829cb80c2aa64147dcd6055320a38e6b02a9905377158154c829a38ac0aa6410fdd95415320cd4c4b00a99062d6498b53c821fba2c329e410f1d16194f2087aed2a0a79043f7655053c822fbb2a629e418d9526114f20c6aa9308a7906365458453c831aaa2c229e419554d6114f20c74a930687904777159543c823a38acaa1e418e5506050f20c5ca8b10879043d76d4f42c831caa4c1216410f9d85450b2087ceda9a859043f7655042c831d2a4c0216410f5da548cb2087eecaa4659043f7458e51c821e3a2c728e410f5da541472087eecaa0a39061e5498c51c830eaa4c628e41879516314720c3aa8b18a3904777654451c832ab1aa228e4117dcd65507208b8e6b2a83905347155141c831caa0c0a0e41179cf65107208bae7b2883905357195041c830f2a4c620e41875526310720c3ca8b18839061d5458c41c8316aa4c420e418b9516210720c5aa8b10839063a5498041c831caa4c020e418e9516010720c72a8b00839043d7599321c821fbaac990e410f5da54c872087eecaa643907254254721c826c39ac190e410f5d6640872087eeab20439043d7695021c821fbb2a810e41879526308720c3aa9318439061e5458c21c830eaa2c610e419558e5108720caac6a88439063a5498021c831caa4c010e418e9516008720c72a8b0043906715158021c83172a2c5a06418b5536250320c5aa9b12619062d5418930c838d2a26018641c6551300c320c72cb2a061906396555030c823cbb6a618641365db
  | 15 => 0x2c76549420c297b8aa4a1061ca54b6050830c72ca302841859973181420c394a90c0a10610f9d2629443087ae9314a21862e6250a510c316b1285288612b5c8645443087ae5b22a21846e72191510c236b90c8a88614b5c86454430c5ce4322a21843d72191510c316b90c8a88610b5c86454430c6ae2322a21863a70191510c31cb80c8a88610f9d0625443087ae8312a21843e76d09510c21e3b684a88610f9d94254430878eca12a21847776544510c31ab22a228861995895114430a5ae42a4821853571152410c29a3a2a320861365ce60904308dce432a821846d72195410c21f3b4a8a08611b9cb65104308dae5b28821843d76d50410c296b90a8208614d5c45410430c5ea8b10821862c54588410c26cb9cc0208610f9d365c843087ae9b2e421852d7494b210c316b24a5908618b59152c8430c5ecaa16421862d6550b210c21fba2cb108610f1d165884309b2e7304421843f74595210c21e3a2ca908610f9d0654843087ae832a421852d74949210c317b2a84908618b5954248430e4a8528a421872542545210c26cb98c0908619c544604843087ce9b28421843d74d94210c26cb9cc0108618755263900308f2ed29c601866a6254a300c394a9285180613c5c4624c030cd0c4a92601863b65d09300c31db2a8498061aa189424c030e52a4a12601865975d95300c26d396ca98061365c7654c030cb4edb2a601855972d95300c2acbacc898061729ca644c030b92e5322601855b75591300c26d3b6a898061369d8544c030e32a82a260185ca72151300c2e4b90a898061749c4544c030ba2e22a2601855975989300c2cd3a4c498061665d2624c030ab6eab12601859a74189300c2ccba0c498061749c4624c030ba2e2312601865975189300c34d3a0c498061a65d0624c030da4e231260184d971189300c368b88c498061345c4624c0309b4eda9260184d876949300c2cd3a4a498061665d2524c030d90c529260184d876549300c364312a498061569d9524c030ab0eca92601865876549300c3a5b12a49806196189524c030e90c4a9260184da76149300c2cd3a0a498061665d0524c030ba4e229260185d171149300c26d3b68498061365db424c030d34eda12601869976d09300c34db2e8498061c6d97424c030d30c5a12601871952d09300c2ad3ac8498061565d6424c030b32e921260186c862909300c3a4a94849806136dd9424c0309b0eca1260186c862509300c3a4a928498061a6dd9424c030d30eca12601869b65509300c38db2a8498061e2dc9424c030f16c4a12601869862509300c3c43128498061a2189424c030f14a4a12601871952509300c3c4a928498061c2549424c030ab4ea212601855975109300c2cd3a08498061369cb614c030cb2a5b0a601869b42d85300c34ca16c298061565d6614c030ab6
  | 16 => 0xc297b92caa14614d9d3519463087ce9314a31843d7498a518c3173128528c618b589429463087ce8312a31843d74189518c23bbb2a228c611b9cb65106308dae5b28831861e5458c418c30eaa2c620c618b9516210630c5aa8b10831865563944418c332b14a220c619558d5110630ccac4a88831863954980418c338a8cc020c610f9d365c863087ae9b2e43184d873583218c21f3a4cb10c610f5d26588630caac728c431872542945218c392a12a290c610f9d3650863087ae9b28431861e5458c408c334b14a5984618bd516295130c5ce8b14a89866a62582544c21fbb2a82a2614b5ca641513087ee8b0ea49843c74587524c316b26a5292611bdd95214930c5ce5320a49863664984524c31ab24c2292618d9916114930c6ac8b08a49852d72d97424c296b90cba12614d9c452d0930a6ae2296849847671196424c23ab88cb21261595c452909309b0e6b04849852e72951424c296392a8a12614b9d05250930acae2292849852d72995424c297b92caa12614ddc56550930a68e2b2a849852e75d89424c2973b6a4a12614b1db5250930a5ae3a92849853671149424c29ab88a4a1261695c45250930a5cec292849862e76149424c393388a4a12614b5c45250930e4ae2292849852571149424c23b388ca212611d5c465109309b0e6b00849846e72993514c236b94c9a8a610f9d262d453087ae9316a29847776544514c21f3a4c428a610f5d26214530c5cc4a10a29862d62508514c237b92cb20a611b1c965905309b4e7b02829846e72194414c236b90ca20a614d5c45410530c5ea8b10829862c54588414c31daa2c020a61361cd601053087ce832e429843d74197214c31732a8590a618b19542c85309b0e6b06429843f74596214c21e3a2cb10a61595c45288530c5ccaa12429862c65509214c21f3a0ca10a610f5d06508530c5ac9a90429862d64148214c26c39ac010a619ad496008530c9ac429460985557114a304c38629285182611b9c861550308dae430aa81843f76550540c316aa2c42a0618d5516115030c5cc8b10a81862e74588540c333314c22a0619958a6115030c6cc8b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81862e72992520c21f3a0c2a90610f5d061548308deeca90a41862d64548520c332a92c2290614d9c454d0830a6ae22a684184d973983420c296b96cba10614b5c865d0830a6ce232e841853571197420c2ccb9cc1a10611ddc565508308e8e2b2a841847671195420c23ab88caa10614b9cb5450830a5ce42a2841853671151420c29ab88a8a10614b9d25250830c72a830284184d973181420c296b94caa10614bdc96550830a6ee2b2a841853471595420c29b388caa10614d5c46550830a5aebb12841852e76949420c3173b4a4a10614b5c65250830a5ceca9284185
  | 17 => 0x8c818758d4294640c5cc4a14a32062d6250a519032d31cc128c819658e60946408bce6312a32045d73189519023bbb2a228c81875956310640a6ae3298832062d65588419034731ac420c81a358d6210640c5aeab10832062e535884190316b12a420c814ddc55210640c5ac4a888320639659804190354b14c020c81a698d6010640d32c6b0083206aa625804190354b12c020c818e5496010640c5acaa16432045e73d96219022eb9ecb10c81179ce65886408bae732c43204b97019221902aab9ca310c812e1d16088640c5acaa124320555739452190392a14a290c81c950951486408bce7b28432045d73d942190316b12a5a048195d4d6194d408beeca98a6a04767198f525023ab8cc7a9281179ce61d49408bae730ea4a046f765485250296b8ea4a1281cad4b6050940e56a430284a065563d46515023bbb2a228a818b9894214540c5ac4a10a2a045f73597215022e39acb90a818b99542c8540e4a85a8e42a063564147215031732a8490a81179cc65085408bae632842a063564d44215032ab1ea210a819558c5108540ce6a2b0042a0670515802150316b16a5202811d9c46254c408eae2312a62045f7654c5310326a9ac4298819554d6114c408ece231aa4204757118d521022f398c2a9081175cc61548408deeca90a42064d635485210332a92c229081ca54a60d0840e52a4b06842052f7254d421031731285288818b58942944408bce6312a22045d73189511029a38a84a88811ddd95114440caac6a88a220665625445110316b12a5208819558e5110440ccac52888220655635444110332b12a2208819c5466010440d1cc6b10822068d6358841103173aac4208818b5d56210440c5ca6b10822062d62548411029abacc220881a958a5110440c5ac4a8882206a562544411029bbb2a2208818ddd95110440e2cc6a888220715635444110393312a2208818d5895110440e4ac4a888220625625444110354b14c020881cc5466010440d32c6b0082206a9625804110398a8ac0208818b99152c8440c68c8a8c422045f73595211022e39aca90881179cc65484408bae632a42204ac765092110392a14a2908818d1915148440e4a84a8a422066952181211022f39eca10881175cf6508440a5ae420ca02062d6254b401021ebb4a9200811e5da5490040b52e420c802043d72d95401021f3b2a4a00818bd895250040caac730ea91865573987548c32cb1cc1aa4619c58660d5230a6ce3aa4a91853671d91548c21fbb2a82a4619658e601523087ce9b0aa51843d74d85528c237bb2a4294611d9c665d0a308eae332e851853671d53428c29ab8ea9a14618795163d0a30a5ae5b2e851853671997428c29ab8ccba14614b5c865d0a30c3ecab1e851853671d51428c29ab8ea8a14614b5ca6550a30a6ce332a851853571995428
  | 18 => 0x448421c5ecb2a24210e2f655512108716aa6c2908438dd965448421c6ecaaa24210f2554949210869abae84908438dd974248421a6eeaa124210e3765509210879329284908438795263d4021c3aa931ea010e1e5458f500870eaa2c7a80434e9d35094021a72e9a84a010d5a73d4250086acb9ea128043569cf5494021ab2e7aa4a010d5a7315250086acb98a9280434e9d35394021a72e9a9ca010f1a5494e500878caa4a7280434e5d74294021e34a7a14a010d3b7550a500878d29a8528043ca5532194021ad6ea90ca010f295448650086b9baa43280439658c6394021a74e8314a010d397418a50086ad398c528043565cc6294021e56e4a14a010c797610650086ad3988328043565cc4194021ad4e420ca010d6972106500869d3a643280434e5d32194021e528590ca010f2942486500863d3b6a8a8043569cf5454021ab2e7aa2a010c7a7615150086ad398a8a8043565cc5454021a74e9a9aa010d3974d4d500878d2a4a6a8043c65525354021e34a8a9aa010f195454d500869cbae84a8043c694f4254021e32a7a12a010d3b75509500878d29a84a8043c654d4254021e52a990aa010f4953c8550087992a442a8043cc5522154021ea4a710aa010f515388550086b5baa42a8043ca5512154021e92a690aa010d737548550087992a242a8043cc5512154021ea4a690aa010f515348550086b838ac8a80435a1c96354021cb2c631aa010d3a74989500869cba4c4a80435c9c64254021ae2e3212a010f2b7250950086b938884a80435c5c44254021ab4e730aa010d5973985500863d3b082a8043569cc4154021ab2e620aa010d6a7210550086b4b9082a8043cc5044154021a74e990aa010d3974c855008794a1642a8043ccd0a2154021e628510aa010f294248550087b1b9242a8043ccd092154021e628490aa010d3a74085500869cba042a8043565cc215402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a628043875915314021c74a9300a010e3954980500872d29cc0280439654e60140218f6eca80a010e3a64540500871cb22a0280439698d5014021cb2c6a80a010d4e72d4e53d022fbb2a629e81539cf5294b408bce630aa5a045d7318552d0237bb2a429681ca54a60d0b40e52a4b0685a052d7294d42d03173128528e818b58942947408eeeca88a3a06715158041d022f39ccb90e81175ce65c8740c5cc8a9643a045e73d9421d022eb9eca10e81559c75394e408ece2312a72047571189539022fbb2a629c814d1c56454a408deeca90a52052f71549429025cb80c2a1481ca54b6050a40e52a4302852055673d46519030fba2c728c81871d16394640c3cc7a14a32061d63d0a519030f31a852
  | 19 => 0x6a80a190f294254050c861fbb2a82a4439698e6015221cd2c5300a910e5a63580548872cb1ac02a4439a5896015221c6aa830a8510cf170185428869d380caa14434e5c06550a21b62e030a8510c3e76151418861fbb2a820c438b9516210621c5aa8b108310e2d659932188716b2ac990c438d59664c8621c6acab264310cd77358321886ad39ea1284438e5c0645422187ceda12a110c3c76509508863dbb2a02844396d8f6055121c76c8302a890e5b63181544872c318c0aa2439cd84605512187eecaa0a890d3870550544871a2a2c3a12434b5cb65d0921a76e0b2e8490d3870597424871a32ac3a12433c5c06150921a5ee4b2a8490d2e75d89424871632ec4a12438d5946150921b62e030a8490c6e7615142486f0b80c2a1243695c76550921a5ae3b2a8490f2571d95424871632ec2a1243a91976150921b4ae1b0a8490d2e7598542486d338cc2a1243a9d866150921b56e0b0a8490da87058542486973a8c2a12436a9c06150921b52e030a8490da67618542487533b0c2a1243699d46150921e4cea30a8490fa27018542486d2b80c2a1243e85c06150921b42e030a8490da67198142486d2b8cc0a124363dcd6050921b18e6b028490da77158142486d238ac0a12438b1946050921b4ce23028490da57118142486963aa85a0a434e1c15490521c5ccaa148290c3e7615141486963aa84a0a438bd954250521a6ae32a08290c3f76550414869c382a820a438b9516210521c5aa8b108290e2e655084148754a14c020a43aa5096010521b4eeca164290ea77650b214866bb9ac190a43a950960c8521d1ec6a12a090e8c63509504863dbb2a0282434e1d15014121ab0e6a80a090f2942540504872d31cc1aa0439698d60d5021cb2c6b06a810e7261583540869d386a92a0434e5c35495021a74e030ca810d3970186540869d386c8aa0434e5c36455021a74e030aa810d3970185540869a38ac0aa0430fdd95415021c72a9300a810e3954580540871d324c02a0439698e6015021cd4c5300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e72615805408717394c9290434e9c354d0821a72e1aa68410d3a70153420869cb80a9a10438d5516190821a5ce5aa28410d3a70d51420869cb86a8a10430f9d85450821a5ce42a28410d3a70151420869cb80a8a10434b9d25250821a5ced2928410c3f76550420871b2a2c2210438b55262904218deeab148210e2d5458a4108716aa4c4208438b9516210421c5aa8b108210e3565504410863cbacc0208438e9526010421c72a93008210c7b75580410871d2a2c0208438e551601042187aed2a64210c3f765532108697bb2a9908431b5da52884218eaed2944210d3575d0a210869bbaa85108434b5d74248421c5ecba124210e2f6550921086373b6a8908434b5d65
  | 20 => 0x95250650106b9baa83280834e9d36394041ae4e3b1ca020e596318e501069d3a4c52808356dcd6294041ab0e6b14a020d3a7418a50106ad398c528083565cc6294041ae4e2314a020f2b7250a501062f398c4a8083175cc6254041a74e1a12a020d6a72d4d50106b4b96a6a8083c61925354041e30c8a9aa020c7a76d4950106ad39ea4a8083565cf5254041e94a7292a020f495394950107953a4a4a8083ca1925254041e94a6a92a020f495354950107953a2a4a8083ca19152540418f4ec292a020d5a7314950106acb98a4a8083c694f4254041e32a7a12a020f2952d0950106d8b8e84a8083c694d4254041e32a6a12a020f2a525095010794a9284a8083c654f4154041e52a5a0aa020f515390550107b0a9482a80834edd54154041e32a6a0aa020f295250550106b9baa82a8083d454d4154041ec2a4a0aa020d3a7498d50106b938cc6a80834e1d16354041cb2c631aa020d3a74989501069c3a2c4a808356dcd6254041ab0e6b12a020d7071589501069d3a0c4a8083569cc6254041ab2e6312a020d7271189501069d3b684a80834e1d94254041e56e4a12a020d727110950106b8b8884a8083569ce6154041ab2e730aa020d597310550106b539082a80835a5c841540418baed298a020c5f7654c501072729cc4280839354e6214041c9ca6b10a020e4d535885010636bb4a4280839398e5214041c9ac7290a020c6f76548501072731aa4280839358d5214041cb4a7300a020e59539805010735294c0280839a54a60140418f6eca80a020e5a63540501072cb1aa0280839a9895014041cd2c4a80a020d3a7018a54c869cb80c52a643479cf6095321a3ae7b04a990d2e72d8254c8697390c12a6434e9c26255321a72e1312a990d3b7058554c869c382c2aa64347dcd6055321a38e6b02a990d377158154c861fbb2a82a6438d5526190b2187cec2a28590da571d5142c8717b2aa8a16431b9d85450b2195cec2a28590e2f65d8542c8717b2ac2a16436adc16150b21b50e0b0a8590ea56118542c86d5380c2a16436a5c06150b21a5aeb3028590d2f7558142c86c7b9ac0a1643631cd6050b21b4ee2b028590da47158142c861fbb2a8216438d9526110b21d4a84b088590e2e5458b41c8716aa6c4a0e43691c54250721c5aa93108390e2e5458841c8716aa2c420e43a95894110721c74a93008390e395498041c8754a14c020e438e9516010721c72a8b008390ea94258041c8657bb285a8643879536354321c3aa9b1aa190e1e5418d50c870eaa0c6a8643a3d8d4254321d18c6a12a190e1f63d0950c870e31e84a864387d8d4254321c38c6a12a190c3d7695050c861fbb2a828643879526314321c3aa9318a190e1e5458c50c870eaa2c6286432bdd94214321d1cc6a10a190e8d6350850c863dbb2a028643561cd5014321cb2c
  | 21 => 0xb55a92c028a85279ce619414293ae730ca0a1539701465050b47b1ec4a8285a318f6254142d1ec7a92a0a168c63d495050b4bb1ec2a8285a518f6154142d4ec5b0aa0a16a772d855050b53a96c2a8285a5d8c6154142d28c630aa0a16a7621855050b52b90c2a8285a9d486154142d62e030aa0a169863d415050b5830ea0a82858d1865054142c6ac2288a0a143f765405050a9a38aa0282852edd95014142b30e6a80a0a15b0715405050a1ebb4a9210851b5da54908428eeeca88a221671515805110a2f39cc328085175ce61940428f6eca80a021659635405010b38b0aa0280851bdd95214b41e4aa530e85a0f255258742d06d2b8ea4a16832b9d85250b41d4a84b0885a0e2d6250a50d0717b1284a86831edd950143418bee6b04a520c5c73582529069c382c8a94831bdd95214a41a5ced2928520e2e769494290792a96c2a1483c95486150a41c5ac4a968320d5a73d42509062f398c4a8483175cc62542418f6eca80a120c5e73983525062eb9cc1a92831bdd95214941e4ea5b0a84a0f2752185425065b3a8c2a12838d9d46150941c6ea430a84a0eb2701854250758b80c2a12838b9954210941c5ac5a9482a0e5963d42505063dbb2a02828317dcd62141418b8e6b10a0a0d347150850506b5386a5290835a5c352948418bee6b04a420c5c7358252106b5380c3290835a5c06194841a5ce9b04a420d4f7358252106a639ac1290834b9d06094841a9ce6304a420d4d7318252106b3388c129083179cc60548418bae6302a420f25719915210697384c8a90835a9c06154841ad2e030aa420d2e74d8152106963a2c0a908353dcd6054841a98e6b02a420d647158152106973a0c0a9083539cc6054841a9ae6302a420d66711815210637bb2a4290839a54a6014841cd2a4b00a420e65525874210792a94c3a10838b54961d0841e4aa4b0e8420cb775587421071bbaac3a1083a994961d0841c6aa4b0e8420ea5525874210712a92c3a10838b54a60d0841c5ecaa928420cb5711814210733292c2210838b58952d0441c5aa53068220c3d76952411063abb4a9208830f5cb6550441c5ecb2928220c3e765494110717b12a4a08838bd955250441c5ceca928220f24715494110716a90c0a088399d965250441ccecaa928220f2654549411069abac84a08832d9d84250441c9cc7296a020e4d6394b501072731aa5a80839358d52d4041ab4e7a84a020d5973d4250106b5396a1280835a5cb50940418bee6b14a020c5c7358a50106b5396a7280835a5cb5394041ab4e7a94a020d5973d4a50107a529ca528083ca9d25294041e94a6a94a020f2a7454a5010794322a528083569cc5294041ab2e6294a020f1a53d0a5010794a9685280836c5c74294041e34a6a14a020f2a5250a5010794a928528083ca54b4194041a76eaa0ca020f2
  | 22 => 0x30000000016000000003400400200080140000000010010016000000003c002001008800000c00100000000080000040004010002000000c000006006802000000100280840020000008008006007000001c00600a0010004000002002002c00200e00000000020000000000002004001000000000a000001400400000500040000000000000004001001000400000300000080040000008028004001000800001c00000280240100050000000000000000800c000000000000401e003003000c00e00100580100060050000018002004000801400800200b000000200100100040000010010018004000000801800400000b000400e007002800c00000700000080040010018000002000000801c000005002000000200a0020010000000004000c0020010000000004000000001800e001003003400400000000040000000010008002000003800c00a000000000c0000050000004008002000800c008002000800c0000020080008000005001800c0100000040040000000000000800000300080000020140010000002002000002000401700180080020070010000004003004002400000800280000000090010018022000002801c00e005004800000200000100040140010010004002000000000c001179cf60547428bae7b02a3a14777654451d0aad39ea128685179ce61943428bae730ca1a147b7654050d0a4f39ec0a8e85275cf605474287eeca88a3a14b77654451d0a9bbb2a228e858ddd95114742e4ac4a88a3a169a6398051d0b54b14c028e85cc5466014742d34c6b00a3a16996358051d0b54b12c028e85cc5456014742d1cc6b16a1a168d6358b50d0a4f39cc328685275ce6194342a72e028ca1a159a73d4250d0acd39ea0a86858d584511434287eeca80a1a14bb7654050d0a3bbb2a228c859c54560146428bce730ca12145d739865090a3dbb2a0284859658d5014242ce2c2a80a12145f735835150a2e39ac1a8a851ddd95114542ae0e0a88a2a165a639805150b2d31ac028a859658d6014542c76e8b00a2a1638745805150a3dbb2a028285561cd5014142ae0e2a80a0a15aa701875250ad4b80c3a9285639cf60d4942b1ae7b06a4a16ab609835250ad2b8ea5a8a8527dcd60d4542938e6b06a2a169b63d815150b55b16c0a8a85aad4b6054542d36c6302a2a1698631815150b55b10c0a8a85aad486054542d66a2302a2a163a511815150a9ab8ea428a85695c7521454287eeca88a2a1538705445150a5bbb2a228a856c1c15114542a6eeca88a2a1637765445150b93b92a228a85c95895114542e66e0a88a2a1534705445150b98382a228a854c1c15114542d34c7300a2a16a9629805150b98a8cc028a858ed4a6014542d56a5300a2a169a635805150b4cb1ac028a85aa5896014542e62a2b00a2a163b525805150
  | 23 => 0x18010000000000c018000000000c000000004800c000000000801000e0000000004000019000000000400c004000c0060020010004000005006800000c000001000000000400300040020050028014004000003801000000d000000800600a003002000400000000000020160018000016002000000000000e001000000c002000805c0020040080000002001000000400001200000000260020008000002000000000001a00800100080020010010048000005000800800c0010010004000000005801800000000000180060020000004030000000000000200800000040080000030004000005005003c024007000800000000400000000020000000008000000001000c004001000801000e006003801800000200400000040020010018000009000000000200e0018004000004000800000800a000000000600400300100400000020020004004001000400e00400100000000000010000014001004001400c00d0038004002001002800800000a002005800000400200000000000000004000008000800400400b001000c004007001000000600200680040180000028010000006003000000000900080100000000098000000004000804000200300000000000020018008000000000000000800300d801400400900080000000020060000000002000000400c0070008000016000000000c002000002000c00200300100000020040048000006000001000800001e0008000016008006000c0000070000008002001001001800000000e0030012003000001c00e0000000050002003001000000400100000000100000050000002000000000c000005003000c0000010008008002007004800400000000200080000040048020000000001000400800100000140020090018024010004001000000e0000000010000000008800401200800200040000000038010026007000800000800900100000020040008004002003009800400000400000200140010048018004003000000c010002003000c002000001003c0080050040018002000000800000201400180340000030000010000004000801400000000080300020010010000006000000000401400b000800400c00500280200000080030004002000001000c0040010000004014002000800000a00600180000020070000000000000000000400000b002800400a00000200200000000000028000000004801000400f00100000100000000000000001008800000a0000010004006002005000000001c00180180000110000010000002003800000400500100000020010008004000003000000801e00100000040040040010074000002000801800c00100a8000000000000800400400100a800000400100a003c0020010008000002009000000c0000000000008004003000000401000
  | 24 => 0x360005dd31100000b038393a4f902ed06c31e40103c355cc0a551e3eb1ff00015f400064940c84dc1e10000001800b7100033d4dd200000013b525e000000251d05b744340275dd26a491b92a00ec20000000000000c108000000a60a41410002b304ad971880001800003df8e018ce1a800000018340000000000dca4763ae8000000b680001de8c68ca40000402000cde6fa8377cb8cfe3b10000a6e00022b642c0000004b7af2400000000027d9cef003000000000300080000080030068000000002001800000a00100000040040000038000010000001800000c0140028004000002000800800c001001000000401f0008000000006000000000000000000080060030008024000003000000c0040080008010004001001002c002001000800000201100080480060030010004002001000000400e0000008008004004005800000e000005800000000400780000000010020014004006000001c00a00300000000000000010000002000000001000200100200080000000010010014000003000c0020060040010000003000003c002000001000c0000050000020004000002804c0020000018000000006002804400c00000000180020100000000004002000005400400000000000080030058000002005007800800000100500040000080000000006007000801400000300000040040000008000002002000002c002003002800000400000b8000000004001001400c004000000000000000000000100000000004000002003001c000001001001800000100780000160010010010002007004800400000f008000000001000000140020050020000000000003000c0040030000010000004007000c0000020030000006000000000002a00900000000000030070000040001000000000200400880040000010038008010001000000001600600880000080050008008002001002000000c00800300000040020030004008008000801c00c0070008018002008002000000400000000280000000010040004002000001c014000000801c0180010008034000011000000400000700080000000000028008000008000001c00000300080000040080008004000000001000000000400100040000000000004000004000800000200500080040000020008008000002000000401000300000040000050058004000000000000000200000000000080020018004002001000800000e000000003c0020020000038002000001800c004000001800000e000000001400000200180040020020010004002007000000000200700000000000040000014000000000001404c00200b00140160030000004000000002800000c00000600040020020040040000001000000000a006000001c00400000280000000090018000000000004800000000100080
  | 25 => 0x19a72283658fb435b00003d0a24000d8de0b9588c560225232a0c00081c000329c0007cc03382f00e05b551c840c1d800030602bd9340c45ba8bd967400032535bc9a8d3317538ac0001ac80004b0000589000000187e9925e3120dbf8e400000000000717b590fe4c505e207e9c11aa07084462a8c000aa500011f8000cdb1f400780000004cdadc9b7400002c8000e7061302d723f45a7635e380019d8d87663b471a88e5109f06d8bcea708001a740000000002d7a0005700001ecc00000000036c40000000001c140000000000dfdbca0000002e540000003c09c4ce4bb57000000029839b00000000006049e70001a6239663138b448ae5d0000bad5ee000000000170ce965a61011146000000000015472b4121308c0ab2212e064dba03ab4cb8e0d2024ec537301d942a57359800132802a80035b200078f00b80013560006948000ed615b6ccc70000027b0672bc8aeeb814b694e00008764328000c780003dd000000031657e0001a2e5a71ce8bc566cbd507a06101864540e683a480250e6ac80000004e31124a5189a00053406e4000000612c000a62e3ef3283650f70004840000000000387038abd20000001c694344eb34bb84c68cb200002d080000006a84000d2c1ef8ac92301b4d5d36236700000000000000f0a0001850c51b1cdb03752804000e4b00004c5bf2ced3ea33393382b236fb97e000a5d2dd99f872f108a221525b6fea7906ac8d9524130000000000dc78000ab1afeea2000000000000012bc00000000000000000000000000001776000754c000000e8124f0001830e321992d257d6915d3029f84ba9494a68000000000583b332632db95729f3c266353100d328c6a0d4650dda8000000026c00092473d1292a5e0d04a60001619a4c83f00030727ae0004439dc936c83d21a120587230456a36fca683e500030300001ea1571ad9d4ab31d48b3d8000be800021788a27d60d8b61600090c0002fb0b56bd900008a8fc623e51900c43f85d63f21b3445a57900017ed060b940cc8000872de90fcb09d5da3a152691bd7bc9fc70d6eb0d866f654c91fd0a25f127da3317b61803b98000a5a00058d35b4ef6b5dc44c96800018c0000000dbc000000381c0000000000000c800002281594000000000272ca9a000000042591c0000001ea0000e862ce17e09660000000000e7600014580002447aa211b46c000d7e000278474848032a99908c40000001ec8000000000000000000044b8000c8c91a00016208aed0360500000008f6037ee243c8000000000000000000029b000000075001c8000d5c0000001b1a2f76cc17bc38806272284b9c2c0006e1335a000000000000002600033eaa7000056d000330c434174932b655d507aa97f9f1c0000004c426a0cf0000000000101c0001e2059c4d916a0000001d
  | 26 => 0x4ab35c1755c207ab00000017f80000000000000000000000000000000000000004430000000f8cdf44f10001d4200013e0c78000c916dac00097a00000032420b700000019c00000000000000000929478b01ac375ae00001d8714abe59409e5b4c0004250000bc35b78000001d5600022500000000000a480000000000003a360003896779f17c760000000000000e7d948a1219d0e3002a824095896248a9eae50a0000002a84f700f721bc0000006ac000343800000000033cc000000000000000000039d6acd92d06b00000013fe6656903a5483e0fbdd9a8a251eaa69b692d1a2cc6d59529dc91ed4e96b4a020869225f2000085c9522ff9174000563015f0b1aabc2438b2f48600b351beaa25cf00005e70110000b5c09d8000342000000000196829c32c0000000000000000000000000000000000648000000000000585884000000003186ca0000002c09f35a1569c3460000000c863868000584b1b00000000000005680000bee3f000029a400000073b4001a1700000000e02d60003d380000000004b0a55c000000368000000071000000000000004d980000000000000000000dfe0000001ad6abc2190f757dc79f0001f116b0a0700000003120001db800086a878efd013e00075e00030557f4ac80000001a22e9f0c731f1c3200065905d93184dc2f41c51a1005336a8ee15f27f46192a6c0208b401980ebc8cc53358b00cfd4000697314734010d00000000ee00000018e5b1d9f43d30de8be4a231d68d6d4bb06e0549d2c36abf855705c06a41e494d20ad80ba815ff92450f088438c13014db64f2a2929469839f0000d58c7684c00000000000001b100009e0000525800000074c1cf327e00000000029280000001d8000000000004b80000002cc001947c00075b5c423a9b5eafb0efad48d1055d5cf9e3050000000000006560004628000e9a000682c001871000000000146a00000000000000000001cc8000a3e73ab3a561ceac69340008426e600006f48b40005549164000b9e38dbacca204be57b603c91635100000006dc00000012c941ac54b1814b80000000002a0800035900000003e6000000028c41200000000017143840002bbda080000000001326000000000187a0000001a2964c788000223c00000001a000117e89600021f59580000ae8854000000598951006cdd25f545843a63b26b6ecec6447a2a92866ea7cdbd996a3e02cd2b300c81c4ca8b5f8000000000db88002d9000000000024d000084900030865400004958000000bbf65375aa4c800059932e4000c3e00003ad9a80002061b8c8904e073507766380005522b895d02c541e347c3a104980032301cb3c80002ec579e1072368fb013098f2354c4c00000000000000000e400000000004690000001582000000070400014d0001f5c2f88130
  | 27 => 0x2d4c4f000000000019000004f18000000c38357800000020f4dfb888f7c26380039540000000000018048d937324ff1a5300019c8baa00000063700b4000d8c0000000080bcb39891dc00035454727b9b8030f00000000004a72f20001a28000000205a72e4736a500012a60f800020680000000001b380000002ad8000000390000000018aa3c45c88154b2835716c0014320000000000f9400000000000006c9027000188f74330b0001abb000000000000094100000017d4a0400021158a74451440000bb21420001ce40000004330001ac219d2e031a4000dda37d80000004470000000e2e7410000000000859000000044e00040c9f4c0001266579fcd13c93b1f90000ecc5753ec0000a3c53613ec0000006e396c8f90f440004f237bc7043350ffb3540000000000d781ab0000000000000000445abb8000d7b74c0eec0008680589c3d63c03d03e9772942a79000000000019462096c91a2b347160000e730006b280012665f389c362596966761980009a0c9e291800091a6d365e36e6a080000002f0c0e6e730001ddc000d9655440000000000000001b5226c3cd925cde677f24f9b3d4a4d4805b00018a80000000000ef05db1fe800000000049c0000000000000097735e57c0638a8c0000000000001a0ead6000000000000000000000006ed21e800000094f394d7b000000000025ec000000000000032ec8d0002b3c6910c900000000006d70000000000000000297c000bdc000261c000cfd000000020200000022f0000ce1ef82c580000006a7a8d17c46513e34000000e4304345b51dcd1964b800053a36a63f8000aec00000000000009141d2b6f13d483a00004903ce3c928881ca0000004cf8420000000543000000004625706fa6510003bec000000c220101ac1130000014c57c038afd539ba9742a000604000000018b4f6b226397d5cb758001b85c50c6c2954a480000000c7d00e036ba72e0d18600000000000000006c20000da22936b5c0018cc49c0000001677000000000000039500000009f000e319819794000030c3240e940003d000000001230002cf85c0000025ad840000002fa978c9ca000426a09592bb445f337256d67801b480000004aa26c9df9a763983ff01358f4d4549ea0896283733cc0000ba400000005492b200001ac0000002861c74000f1ce3d0bcf6d1cc500062598e9a6ca6a0438000aa800000000000000006718001d10c4324eaebd7c0089800000199e0000000e64b99a9727ba2f97c200038cb9a1b22000000070c8f48f218bb84701089300039bd3860a1493800084e8fc26728cc9629d165d238d81c0b4600c0a00584fd12f9b609ac22b408b12395024441b05c984d0c69674934e38950199db8ab9044c30cb2d572600000000007a40b518eb9f1430000452000077e000000034c
  | 28 => 0x8e02355216a3004aae94352c00010700062c07200000000002264bc0000193b214000765000000104c00017c00018f675f1fa8be4e688f05fca07afde61270979346881293148b340000d200011014b60006f933cf8eca5e000048a59077c5bf029c0c730100000007b01574eb045004f608701000000000200000000006a273c800000092199e800000018d4358001a0d6ca724000195ac6b000000000000073c68c21960834d80000000000000323c0000004c5000000073a00004331709de000189cf082c726eb5347c60001b2926454880262e000000000055107480000000000e69ae200056c00000006bf0003174000c5f00000f0000ccd8000000000aad2dea2087460003d280015849ba64530d1c106a00b62b3046600016f33fd9b8e62505a47589006043b800000043c411a2b41dac1b4a2800040c93f000283865c5b4475aafc00029e4d384d17326f15d38001ba62fc1358bb8ad80000000001aec0000000000000871000231800000041c000189200000011580000006eb00000002c13fd80000000dd00000019ced800001334000e2340aa59108e80b5e100000006be00028013ca0000002c4965e5a13c500000000006c4f4d43ac8892ef0000000000151192400000000000011c4000000279c7cecee56e8000000d08bba80000008ec72c13d82d000007e0001841a1f0003ab5d340000000000df200021980019b05da317b54c77ccc509cac2552a52a0002cf0000dad6868000ffa6450000000000000000227d7f60002e8800000000019800001a262400000010d469200006d61645f60000000c986ee000000116659e2e9a5ccfb2e8d0002ed8254c8a800282000000000018b197a000043311a4700004a1aff57fd62a0000001100b1c000000052e00000026040000003c880017d200055389dce6a39417a86b40000005f78000000a6d0002e5c0000002ae1b50afa34b1343309404a2700000008c000000028b8358c2800000000000000cd92ec0008ed0000000bca09539f000028279c416b0240009df00036534480000000000c22925bd80ed1ac829f02137b9853000599a37aa740000000f88000d04a03000000096700011080007f96210000000c5a2f51e2222100000032e600003b0003744c2e61c80011786e80000000000000000000291000000000033aebe80000af00000000002bc0000432b8200035c86f64126ba00018333c04ba8001d68000000000000000028493180000000000a0ec4c000068c00000000000014a5a608298002b7d33c1472fc8cc467c36c6dd78336ce09c6ab80000000005700af834a0000000000fee000000000000000000000000007b700000015e237f8789eec0000ae00000013a60003a81cbd3d83490001a8d0720002160001b2374870f01423c60002520d153c00004e387c4b0e000
  | 29 => 0x75306b03e5120003185af4e0546b90bc2ca00063a80008c8000000000075061442e004b6115c31a6b5198fc5ce0c3188850267c13080018770000000000cd800069408b0000919302d2bc000b843c380c00000006df1cb36a847000003cd69a86e3b8905580f00001339ec778a9e42900019e80005638d7492800000000019605bf731a5940000001de618ca98d346118a34000d000d390f86b01b4c6e16310de4e2431090c0004f900000000000002a40ca581bde24d200002801ce24280019300e5655978574c3262039bbd20e0002d6924c0006fe28cade161000000006e2274c25586f9771fc0007439e4c220270000191c7f40005e50001d060fb23d871db210006cd324c0005a31728001b504522298001c0111700000004c63153378b986800000000000acb00000035c76042410000001d64c0480029be2fa000052171493600061a842cd4d3cf00000003ba3af45a80008960006de40012d60000000b712a21b766680007cc00053b03e64bce4110700014ffe564612072f3a0000000afe8c2c5000000000000000e30000000cf2403081c000000414365000060f51bad2800000030f8000cd2d2f4e09d6e000000717a2a8000d47000000064aaeb00000000000003818000000000000000000000000000019283050000a995b4d81388877a322000251017988e1e54eea4803a92f25748bcc000968470b834c4a00043ca93935482961d6ea17d17c30f118289504260fea9d498800069c80040000000003578c64715b4a8ae9bfae373d4b68c1220000174001a3481e4d4906c000dce6c78c083f07ac00023dc05100047002ea00000000000012f007cf27ba8d8fa39343f23ecc2a6a168aa951a2600031f00005debb00000001ac422154c53909ccc99e41303c71ee7106a846000000035db5f14220db4f928a59616cc35d0b2afec0007570000000cca00029f486e96c3d4db9c000d568001b19ce47de4108001bda94a570a6c400000009e054c10247831c19a0f595f065add1dbe600071f8001372d10448a4b0000b5d0000000c42ad229e00000007a38001f8463066b74e94a18ca0000002c953d600002439a2000bf351100003a22c30000c18ea486d206a4c8bb000052d0000000ea90000abc000217000326a0080005d905e80000005c7acfc14b000000397960ae0db0d40000008968000000000000077a470000e7d0000999102d6e000340f3120850001198a28b380664000e8f0840001d8056a00000019e8000c02446af4c01e8cd470dbf4000d2d4f83298e3a8ab039f5ca6d07865e0ba40f9246e00000002240001d02995a9c9540bc800139c8b13e73abc08244f565af2000067134380000007cb2e800000006028000000d3c0005d01688a7200000000000000000000e21acce2a0001ba0f7abf1f086a3000000021daef
  | 30 => 0xe79e08825a68ed9d047000000000025e0000b1ab50000000123627f00029e1254607346b5c1298dff67d0a58b480000000000000060800060800000000000000000006d2f8800000002ac7536f2a00000000018eb00028b8bb00008571278001b41000674400000041400000000002746599af4c5c0006ef81ea0004d2391a8140007d1504b84478ed28909b3800000000001e8c0000000e780000001d92b502940009a315ea010000d5b1719c00a0a00066436a87a2000000000000000000000003d200020c8000bcc869034c66b988a661d3357bd1eb2d238a68800082a0000b7c00000000000000000002edc000000c2f00032365801bf4dc1c2982010c4fc0001b44000000000000000005c2600000000000000183fb1d0d817f80009e83d788ae0006a70003a080000000000000000ccb00027680009c514d8c0c00015a00023cdd14a85538969400000000038b80004d56b383d8556cee80000012b6ea75d50001c94000000386983a00000000000005c431e800000000069107d58b2e3970f805534c9240003754c401712c706698d06433350034f2c8d3235273c05462305fad98d16b183b400ee4fc5d41e6bad8a0e5f283504fd4acd40e40955a000b5e60c6edd21a9cd5bb80dc04e6e10ec4fed53eacd5aa9cbe000e19dce03f80005cd74b9020000aba00030bbb3f00000000000007c20000d1f75a1696b98000000d436e6b395bc600006f800083acc100000014e46c15d2126859679446433acc0384400030320000005832bf80003ff11e9d452068d200000000000000001d246501200001ad00000000000001bb8de70000172000a6139280000005c93c590453cc8b66e3b42c0000000c7a6b56fa7f00c1ac54a5800055300000009f95be2b9cefa13d472867c9ae8cb000085926000073687a00004362a7800129080d37b8000d8e83b00034f624200054985558d40d000035080004841eab730e7dcb600032240468fa00038e0000c78000276c00010f8000000000e0100000003bf000000000000059d18720d048c5c10000708a0221100018747ee97000034ac0000005320000000ab725c00000007700001c4874d5df6cf000117a70c00000011be00060440014244da0001698aaeb4b8a710e175289c2d039f8a26ab813b27cc7e264d1a7b3a8fda7d57122f60f062cf4380000000000168000000000070325e400000000000015a600003fc000000000000000000058209b932cdfe000000000000093c00000016d8c4a9354001556dd9ec12f00accd053d700009147926320c68000c37da19bf1b4211d000017fc843d960065780ccc831cdc00126a3de638001cd3e5203369154374d9be23349407e27247794ad9f81bc3e8200000000050300000000000bb80012fe00000000004f1e66967000000000
  | 31 => 0xbfabb03c73e16d022804362594ae13a8000bdf0b315800000006e7afd400003a66d0000c7e879f070afd7a2e522638000000c2114f5a616020005800000f0f00000000000002a52b080012040004e50000000d9d8000000e2a23900000000005d71ef8000fd2d520000268d220000002dcc0001d4000000043e0f06eb8001b3ecd780030783663ee00000000005990000000d0800037a0d21947ad523e000021ea3b524342936e0000001be84247592e8e8fc47e2b000000016de04c80000019f20000000000db800049d1fd499e00000000000000003982abc0000000002ac0000c9b800000000000030e21d4000c9f416000000059b12600000c233f6d980010e3c37456312843872e65100005e0000000000089f00000009b4000b9a0b94d280b466224b00001fe3700002a68a1a9ef00039b9b8600064f6fea8447ee21d00006be563c8d60405e80e60000000ae2cd48000000982d374a014559702ca04f0ed40000000001a900000005daeab0000a3d27f0001af0bf20002d885aa00052829bc000bd7758b00e3c1bd600028794a600018884ad8760000000000000000000000000000043601fc000a704591ee4462021096b4f10e40bb3a2a8c54febffb9200015c80000002aece433cb3008c3000096a000000075856b0001c81c74641347000000050c2850000a38dde0002ad485400000000016fee9e04e8f71c8854154e800083059644dae603fc00000000000000000000001bcce1b0000000d4ae15227000163207e2ac0000c0600061b40000000001b880018282ee8a79f47ce500068798b5ae7790114a8b20ca0002d50d8c073000620000000000000000018a26c50288000000a2380036ec000d9b00020bd9386e01e310781820256f239ae000d5437c16400000005ee800000000000002497440000000000000000000365a00000008a838d76900000000003a500000022b92000000c64001a482bb19a026c6587c1385b7105b48eadac92c0232de16267560f2e9062e113cc00089d1d4963c0000cd482800032aa740b0ce1832c04f5e600000000006ad09800006d21918107cc04e82140aa4000b1347a80011926560000f963da8462059e340000000001a400000005603a250ac64e000000000011e0000000e4259860e14218b6521671c0000da00000016e8000000732c001c9c0001648d0446e11154c0cae2140000000000dac0000000000000e120002f9585b2b861d00e5454540000209c00000017d04c9768b7b2f9868cf0dd5f00019d9b4dc4f00036900000000058a9d0f438dda287bca34cce8000a55564d905868001b64e700001ab4cdce0f706192c5c296e0000000e8721e41b891c0002355984001c6607b0000fe00006b900028c178a5cb800322c00000056f00000000004ab2d800000003ac00
  | 32 => 0x119420066332c5927a4719d80000007dd00024b5b814f400000019cc0004cc3750484000000000110600053e2960000000000000000000000000001320006260001b940002811f818790000000000000198da7905c0000000b780013fc0004d70001afa814669a5d93e20000613a3e338c260d31db00000000001548a6a000600a701a540005850000000b9158600000000000000c2c00045f40db99c3e8075301f293cb66024e90000000d4037a80000000002b9908000000000031548b00c8000298937a2250000e70edeeb8000000041031200000004aebb8514020982f60469900019802b125188c958a7ec03b57190623ca8eb8fccbdc9044b937a235cbb56e4d83400000046cb01888c4b65a14000000a45000286c7c00000000001b6c0000001564000000488264547065b0000000a8e5bc00031dc0000004e480000000005b180016520000000000000eb50000000000000000000171ccfb6090f141ea0000f9400192400000016e40000000000001bd600000037753aa00034c951800092600000000000001ba80007d432f000290000035043e00015ec00000025689bc7f13a31ca170a00000000008600007530000718dc89110000d1e7e5235a5f98f10006938001a7e911354ba39b8dc30234272097400013499082968ff0000000098df380000000005be000280db4711f03c8000d0a597239422a480653695d0ad9ee7424be1bc8e7ec6347390411527a43ffaa2c00022f000096c0000000002185064000000000020400000024a0000000409000000000042a80001ac4fa00000000000004ea000190e00002460669e448200000004960000002e41b0c0000002bc00a8e5f2c994f4eece2845d078600012771e31d1a8200056327a44fa686479fa1b5ea8a558786bc6401632688001c4e00035b91e48c900002975a8000bed6ec1bc10e657212c192148400029300490414ff2ca1c9922eccc4b18000000dc64daa58028a00000000fa0005002d7a3980000001350000000cea85600000000006ecb1cd5b600060282507a8de84a10000a7ee4c201b2fd85600000015ba000e8561700000000001de8fd80000001ab8000000361642f78e05e00066e823c0000000002e58000d683913aa24e60000000000000000399a3682dc26f00008316be4b557fb26417a95d2e3998d75c9236076d6d15e4c51720000000000212b7146c00000000518804000000000037000000022c0a160001eb182c000d5623e962d16e35a3b6b2540007276e5a98d44c6b51bc8289c14bfcc3e660c000000752376c000c31dc38000fd60000002d58bdb1d03399bb197c55115a00000001ab0c80000a0601b40280000005910001d508380118000001a7448e0002f68000dae000000076c9586c515bc000173000302c0004980000000000000000299c0000
  | 33 => 0x11665d80000005dd26d80000000002cd29ad8a4c1944d0001696000000398544000071280002346e20000000000d1818480000002710000c40000d2300039500003a79018544784ca58fb800034000002e000000061000002f80000003ed0298e6b00000010a552c00050e00014f62d4000335982c000000061c00005f0000000000075ac92fc5b065a809b0aa1b100002500e49230e1d6b48b5c0000000001cdc00097100000000000000002de40000001ae2cac000b1707416104cb00000003c85fc0de0000000000a16000000000000048b0a40000944000041011b0000002c40ef2e740000001aee20a0002060092000000027a000000070ac859e28e965174247a0000550000000068100000000000006ba80000000000002b9800055e00004700000002618001cd800024819840000000000730d901e65ea3a30774000742000036f1f6000000000000073580000006e473b800146c90970b80005a6b8d2db000055422300036571a070224400000006740a413f021c8e48df011c4904cc395033c05c144055a7ed42e51b08300000006445c905ec0000000002a2050800019d213d7f796651286482e73783cd0b1910b1810000001ac60002eec00095a00046f37124920002338000000000627de84a945a9000000025e0000000000a1e4860f000000000000000000648c2cc30000000000045417292e823a05c918c000bfdf2c80000004e10000551a4f7366a58000000c7200024b81830000000000000000000235800000000000007b61e28000000000aa86d600000000001bb183800051800000000000005a880000000000000000d040002248c1c00000000000000000000003210cb800000039a40001d810c210529cc5643203800000000002a488cdcf0299800000030d00000000009f528e816c0000000002cb8cbc336000212c0002676c35aa000000000036ad91d00a0000000000000401b86080018873206d0460c74a97a2ec330d9772d1b74e80cd12e768ac2bd45c04680f9c7ce49239c00130800000000004a200000001eea9c5b809415b8000c3d80013d40009fa0000e35066022800348400000000000003bc8e81d12b2954b4df0000000000003ae5b97a0007c50000370c000000000000000a24c4aab5c00034e2d8800019400006b8e4414000000039c20000000000724028004b4a231c0000895e200000000003392ef42750000002ee4000d1200000000000000002618952000009e2191281f2059b3899c8000000382c0000000001d91ac05533c4800000005649b8000000000000000111175a2ca950c0000004d080000000ee61b2248000daa80000000001d50000000000b1f3944000000000000000131c5830000000a84487000336588b6590001d9c0000000000000cc006c48700001f20800001590000e096a88
  | 34 => 0xc000ff804a0002ae400000000038a40000006db4b6c3d600042187b00000002db968203a000611c0017c600015b1540f68c778002af4bd3aaa000000000000059380000000000d500000000001b5800000000049a4000000000205098800017d800000000000060f973c000cc0c4728b0bf87b52b3a3059896790000001c089bb00000000000007400000407000000000000000020700007824bf0001dd0afe0000002151378dbd3edae94a440000000000000be70000ee5588db800000000000000002da8000d83e435458eb80165b702e85b000000018c44f4d889490001680a0f43d8ec5b4328a00024c444800012500009e2cc90f8101451c00000011051421dc00000003f40003280b9c0000798000000000e03665c00000088a04f9aac00094b51d00010b63813aaab24000a5eea480017d70007238001c4c2abb4d000000000007d711400000000000000008f911034ff2f49cc00000000000a8341b0a90b43670000000000000168b0e60000000001f980007b10e5a7116820000002cb1a3a00000038d4d78000000000000091e000353000000036d0000000e5746d8001c0385d3a7a3d13b8dea141b26c114e926e400001ce0004be80000007e70001b013a0bab00000000008a20002f4000014a0000bed110b4e00000143dc366000000070a0007551325b24000353000012f3383ab85587161741bbb62c0007530e28330000468b84800000000000027f592cc0f8463a70af42ef800000005f00069626d000005197480000007823524000000000000000000000000000000000000000001aaa00000000000000000002dd000042400000007943872afa8400228958002bd03074656185a258e2000000000000075600018d930a82e0bf2140000aea7282fd000000066fa6955860352a5997d9c200061000000000000001b6509cab61710e6a0000001d5000000000002c0000000000000022cceae7b8003a640008a709a80000008fd11b3884cfe70630d000000072c00032dc0000000d4a84d24ae8b52e26685fb07425bb69545e24e742dfe83642c43b7f294aaa5a5b6d90fc1c4b5a3552de97dd000000276180537c3e000008120180001878d84bfe3cf186c0005b33330ab491201f089857047817857188edcd584200000005ba000000000000000040b00000000000000495b6e00066b80000000002bf30d23a3000000000189c4ef4053274edcbf70000a095a2bcd0000000000bbc0000000000102800000000000012994c8b60000752450c0000004a300012265ed0348000f32df14671fc831452700008a2034c2900024f889ab8b4428f682361852cfb9e96e00005fce8510a6c604338000cb499d66ddf49d6085f6fb00019e500000000000000004424eb8000000304b4f8610e36000000174640f4722e00a769ac4061320000
  | 35 => 0x6831949414744e440df92be2540000d9065400017e925583bbf602ea62c7d2e7f1c72c0c6ded011d8eeae000d0206331b186799525cb69d120a902e635b03448c468600000000000001068686e5369eb66567a2d600011d16900000002004666b3700000003f600074c4ae40000000000000000c0d4cb13b800016273e73e00000456da80005327290000c6d012000000334800000000028a62a0087e518000d5c169a360001a798d414c000067800000000000ae0002ad0001486b47598014905de340000e9c000000000325e0005fd5b48000000b04453000000000014600014980003f41637320585190b17845c28741f0b4800000000018660003cc00030112d21db1d98959224c3c00039a67de57b47a4000d2645b49b000000000065539d99e165d4df00000000000000591bf0606609819171850653d2c9123e00003e21d08ea0b7000364bd22e6380034e00000000158000e3eaf86c5c8104042266a7c000200000510867956220b0000804578000000000000000056704c1ccc58a0e500010fe1da5f808d1622000000022167269b52780000002a10000000aac00000000014180001e980000005d4bfc2a299519770000000fb80001a100000000006f016000005ac5cd9f7c43ad856fb9cf16eca8d68f105812cdbfab41ef0018821d0eb0b400081d4cc80001f4a5105680016da00019bb98212600033b90620000000001da4000b653f115a52420003db00000008d546eb0bf941eb702800000008170002e7521e9c600000018de00000000000001a4000019f87f5fa439cfc62ea5eb00000018ae47200000000009f70000000000ba103c00000000006fd8000000000000000150e0000001770cae000000134c82f105396a6c99a09554e11eb44ea3f44ec8000000000000000000000069577040dec5280000018620003c4f8715688cf4c6b5e4ae800000037d200000000000002c0e001282a509b0c2880000250802e838f000037600000019ecc6e000542139dbd815842c0000000000000000000000010a0e2a000adc5a3000000000000024e400000015b8000000e14218b2b800090a0000000000af32efc0000000006ff
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xb32cc020e096550b32cc020f0142cc951cc020e0953589420c02085b855da320c020d0975508320c020b40825cd510c020e2162509510c020a51868c9510c020f01420c9510c020e04635095148020c50635c75348020c18769515348020c1876551534802085a869d95348020c897418e5248020c197518f4248020a188654f4248020a488654e4248020c1b7518d4248020a188654d4248020a488654d4248020a8a8398d4248020e098518d4248020c8b7518d4248020e0b7518d4248020e0863d4d4248020b2181d4d4248020a888694d4248020b098594d4248020a288654d4248020a888654d4248020e0b8654d4248020b0a8654d4248020b088654d4248020e088654d4248020a088654d4248020a508654e5148020e806350a5148020f015350a5148020e08635095148020e125418d5148020e115418d5148020a508694d5148020a508654d5148020e23655095148020e80635095148020f02535095148020f01535095148020e1063d095148020e40639095148020e10635095148020e40635095148020f03635095148020e22635095148020e20635095148020f00635095148020e00635095148020e05535894110710b05831d54248710a1683d506150a10a16839946150a10a0e83d516210610b088254d420c210e0953589420c2108598718c5248210b09831494248210e08631494248210c25745c46254d10a0d821516314910a298219660d0910c18651cd6050910c30651c56050910a2982150604c910c24755894110510ca1621c1411051082d821d8544c510a298215060485109248754d4248510a248654d4248510b22859c14248510b20855c14248510d20755c14248510b80835c14248510a30855086150110ca1725086150110a498614b32cc110a308550a61cc110ca17250a61cc1108e1821c5640c110d0b541c9530c110d08541c9530c110d0b741c9530c110d08741c9530c110c49861c9530c110d0a841c9530c110d09841c9530c110d41811c9530c11091b8754f420c110b088254f420c1109188754d420c110b088254d420c110e0953589420c110948825d5310c110b408254e210c1109508754d210c110e4153589210c110f0153509210c110c2a655c85488110c48631c95388110c48631c953481108598718c5248110e0b5418c5248110c1a7518f4248110c187518d4248110b09831494248110e08631494248110c507518d2148110b20855092148110d20755092148110e80635092148110a0d821516308110a25821516108110c187598d42c4110c287558942c4110b208550921c4110e826350921c4110a14835946150810c31751846050810e21521846050810d057350a5148410c24765494244010c28765494244010d11545cc4144010d21545c84144010b118414d3144010b418214d3144010
  | 1 => 0x42010101000060f00006000082c1806e21625466014742e11635456014742e21625456014742a8a83d8260d4942c27765895114542d13731c15114542d10731c15114542d21621c15114542930875466014542b10835466014542930875456014542b10835456014542e11635456014542e21625456014542ca1725c06154142c91735c06150941b21801c55250441d21525c74294041d11535c74254041d21525c74254041aa0805846150b21d08735095014321e09635095014321987835c36150921d82735c06150921d81735c06150921985839c66050921c24655c46050921a25819516210521a28805516210521c877350960c8521d08735095014121a488258c6354021a258194d6210640c2562dc55210640d057350a5148640e06635895110440e05635895110440e21625466010440e11635456010440e21625456010440a25811516210530b0581149428c130a30815946050830d09735486050830c25725c46454430c29729c06454430c29725c06454430a25811516210430a6181189524c030aa181189424c030d09545c8544c030d11545c4544c030c19759d0624c030c19755d0624c030c51759c4624c030c51755c4624c030c92745c4624c030c91745c4624c0308d1811da524c030c897418a524c030ac18118a524c030ac181189524c030a5181189524c030b0984189524c030b4181189524c030a918118b424c030e086254b424c030c497518a424c030ac18118a424c030ac181189424c030c4876549424c030a8a86dc9424c030a9181189424c030b8181189424c030a8a87189424c030c8a87189424c030e0985189424c030e8281189424c030a8981189424c030e8181189424c030a8181189424c030a8886949424c030a8886549424c030b0a86549424c030b0886549424c030e0886549424c030e0b76549424c030e0876549424c030e095250b614c030989821d1514c030d1174544514c030d4172544514c0308c8825da414c030949821d5414c030858865d7214c030d097454b214c030c887650b214c030d097550b214c030ac18118a214c030c8876509214c030c4975188214c030c8974188214c030a14835846155320a25819516210720d09549cb530c320d09749cb530c32091987d4f420c32091a87d4d420c320e0b53589420c320c29729c06454620a25811516210620d057350a5148620c50535c4624c220e0853189424c220aa181189424c22090d821d16114d20c15745846114d20c45725846114d20d08539c36250920e0853508604c920e08535086048520e0a6550a328c120aa181189424c120d0875509324c120a51811886054c20b05811c95350820d08721c15350820e0953509600c820d21425c03254420c887350960c8420e095350960c8420c507354560c8420e214254560c8420d097550
  | 2 => 0x280e6104fe0008e4310a0000000000000a90bc3f42c0020c00000f7160ca3c03343a001680003800218283406121c6b800d2000001e88f1888fa6e00000da2b8e92c888ae0ee0009c000f4382002142f914002f80c000502d4190c8e13c4ff3b44c15c6f19c40078360005300000294d6000f80280001c2a338fd800211480006a482e41531c990e4f61cabc3c8e01503c07c6d0081a1aa8d180fe800001d00000000000001d8473940013c000008b000061e00009c912470986cb7134f180000058e20b8a72a8de0009d014000703d0d00010c902507c3906a00000000003f00031000204b441647800000dcaf08c35200a2178ea372b041059254242d85b2288c24e0018c181186927820170ac2e800314000009a0f8a1194313240000000000fa1d40025c0000000000b336c7f21609404bb0510e41c0000017000dc24c66308c31dc6b3cc89420fd208003d4001cc7f84c723ac00000710004a00000000000a4e702000094000006e00000418d800000000000ece3c0c6c25206b342d0c2ec41a703649803426424fb12c5d0acdf40ea421e303440f408fa938791909602d07908cf1f8cc0043a000880e00004037a10df8110d000fbbbca82484932c0000000088d43da1d30455110dd000e84065638cb1000c6298c80447b0000040008b00bf00068000ad00ce4af4d5048d71f4510b0004149b17cab34d0cbe490a7ca3000040d0a8000a05010044800020000a0e038240a04000042e030380802030200804000884c04030083c00050500c1603030000c000301806010081400070000404030000c000304800040b01010000101800000401824040004054000001810020000004
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xe36000003400180005c88c143421e9200014ac5001802000001e2c0072664a8641086de4048e88207c29c1208018200000008c460421d635456014542c1043ac4a8ac028a85a0083589515805150b102e8c08c529260185806446254b424c030c20bab023148498061a0185a0462509300c34030ac08c4a1260184a064486949424c030a044b2eaa16429806140a97d4d6250830c83400a6c08c4a126110540644721c15350820e0039a84a8ac190841a006360753509200824152d432a6a1240105802595350a5148020b004b4a6a12a2900416009654d425452008241330318a4a1241086401d4835c14248510c1042ae4a10c2a0221820855c942987304430130cc20e4a986088610619811c9530c110c80c2302392a6182214089754d625083044260130a9a84908608854025d53509210c110904cc0c62928490221a008518d4248520443800ea31a8490a40886802166350921c4110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3769
  | 3 => 271
  | 2 => 33
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (548+((h/14+packedAt gbK7 (464+(h % 14)*6) 6) % 56)*6) 6
  | 6 => packedAt gbK6 (36338+((h/520+packedAt gbK6 (30618+(h % 520)*11) 11) % 1874)*12) 12
  | 5 => packedAt gbK5 (274972+((h/2587+packedAt gbK5 (238754+(h % 2587)*14) 14) % 11270)*14) 14
  | 4 => packedAt gbK4 (203388+((h/1439+packedAt gbK4 (184681+(h % 1439)*13) 13) % 6897)*13) 13
  | 3 => packedAt gbK3 (17187+((h/103+packedAt gbK3 (16260+(h % 103)*9) 9) % 410)*10) 10
  | 2 => packedAt gbK2 (2415+((h/12+packedAt gbK2 (2343+(h % 12)*6) 6) % 49)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f83fe3c1f8ff1c78f8fc7e071c1f87c3bc4f3
  | 1 => 0x87fc3fffe00ffe380ff1f8fffe01ff80c4f8fc
  | 2 => 0x7ffc03ffff1fffff001ff007ffe3fff070f1f
  | 3 => 0xf800003ffffe003ffffe00007fffc003f80fe0
  | 4 => 0xffffffc00000003fffffffff80000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10a98444c514a2018582c1253044493819c471
  | 1 => 0x311888084320404802904843520893084058b4
  | 2 => 0x4200109108010012100112080490244106010a
  | 3 => 0x20532d22920864acab240012692d0212e80ec0
  | 4 => 0x446230031c4d89374c49a49c00300463b7a000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0feecf8e0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36617
namespace PEqualNP.Outside.L_meta_36617
open PEqualNP.Outside.L_meta_36617.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 33 := (concat bgb_2_0 bgb_2_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 271 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 (concat bgb_3_224 bgb_3_256))))
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
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3769 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 bgb_4_2304)))) (concat (concat (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400)) (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528))) (concat (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656)) (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784))))) (concat (concat (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008))) (concat (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136)) (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat (concat bgb_4_3392 bgb_4_3424) (concat bgb_4_3456 bgb_4_3488))) (concat (concat (concat bgb_4_3520 bgb_4_3552) (concat bgb_4_3584 bgb_4_3616)) (concat (concat bgb_4_3648 bgb_4_3680) (concat bgb_4_3712 bgb_4_3744)))))))
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
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6283 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104))))))) (concat (concat (concat (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296))) (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))))) (concat (concat (concat (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968)) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))) (concat (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672)))))) (concat (concat (concat (concat (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152)) (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248))) (concat (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)) (concat (concat bgb_5_5376 bgb_5_5408) (concat bgb_5_5440 bgb_5_5472))))) (concat (concat (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664))) (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856)))) (concat (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))) (concat (concat bgb_5_6080 (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272))))))))
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
theorem bgb_6_1120 : Interval gbAtlas 6 1120 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1134 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 29 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
  · exact allgb_3 i (by omega) hi
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeecf8e0aaa0a8a0feecf8e0aaa0a8a0feecf8e0aaa0a8a0feecf8e0aaa0a8a0feecf8e0aaa0a8a0feecf8e0aaa0a8a0feecf8e0aaa0a8a0feecf8e0aaa0a8a0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,6,38)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,6,38)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372928 * 2 ^ 32 + 4003523072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36617.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[3,5]⟩,⟨.and,[1,4]⟩,⟨.and,[0,4]⟩,⟨.or,[6,9]⟩,⟨.and,[7,10]⟩,⟨.and,[2,9]⟩,⟨.or,[0,8]⟩,⟨.and,[3,13]⟩,⟨.or,[12,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372928 * 2 ^ 32 + 4003523072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372928 * 2 ^ 32 + 4003523072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36617

open PEqualNP.Outside.L_meta_36617 in
theorem PEqualNP.Outside.L_meta_36617 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372928 * 2 ^ 32 + 4003523072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372928 * 2 ^ 32 + 4003523072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
