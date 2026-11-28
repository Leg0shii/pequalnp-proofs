import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40978.Model
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
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
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
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
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
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
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


end PEqualNP.Outside.L_meta_40978.Model

namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
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

def SBf (j : Nat) : Nat := [7, 4, 7, 6, 5, 8].getD j 0

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

def mirrorSteps : List Move := []

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

end PEqualNP.Outside.L_meta_40978

namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4c0170020c04820000020cb000103542041540140047ff32fe42fc43fd31fe43fc10bf42fe21ff31ff43ff41fd40bc40fe20ff20fc32fd21be40fd42bc41ff42fe30fe10de32fd41fd43fe32fe41fe40be41dc32ff10fc40fc42fe31fd30fc41ff30ff21ff40fd20bd42fd10fd32fc21fc20fc30fc31
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x100010d05032b030002004b140200010600010107000a40041c1003022800000100010b002d0d03010900200004006904090900001a00000008000006000e7701041900710000092ccf29e853d54c867ca320cf940419f286853e54c427ca9905b14931e6a10653d529067ca90857d4d219f2a085ad42ccb5a8419678ca40b6292616f524c27aa5204fd5220bba8a415e520cb986410cf95232ae29a416f524c6f0a098cf95330e7210659e321076ca220d754f429eaa0413c544c3386420730c820ae29a439f428cb70a0a15b149109e2a2215f53443386520ee10320e619441b441086f0a090d7d4d42cf2a4659d420ca7aa9984f95032ba28a613f544867aa9214d145429e282853e54c86bca5194f942419e2a0219d53d0a7ca2206795032e6194438d420ca7aa420cf55331b6a96873c5150a78a898eed4142da20e439c329027ca3204f15120e729065785050a7aa9084fd5130bda82433c548873aa8194f553209faa0215d538867ca1204f55232ae29a213c548827aa810cfd5110ce19083b45150aeea2a15d145209ea90815e538835ea4a167d08329f28883b8400827aa9884f94742bba8a617b5050abca710cfd5221b7296879f5350abca6084f95331cf194835c5350b3c64204f950209f28081385050af6a098e714d42dba8a853e540873aa9196750a32dd280813c54486dea4885d14542aea9c415e53d0abaa6084fd51319eaa065f110042bea6904fd5120
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x218020051504b0c6004880004001443002006000044a3592420ca346154840aa181420caa4615083287d95420ca8e63d49428e594400830d520c841aa18142cca356510421a3592520ca386054841c6d4c5050b0f540ca21c5d4c5150ae06244010a6181420ca4c6254c10e10c8410868c615083287597420cb0f6550832a5185428cb883210020a918542ccb0d520c840a2181420ca8c6050832cc1475050b0f540ca20c614c5050b1453145428d987548822d6215010e2181420ca986050a32e1185420cb0d540c821b418d10042c46150832e2d81420cb305114142e1d85420ca8f6550832b2181420ca8461508328e98354887335114142c355032082946150832
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x200000205a01876050832a14e1aa06510e09650c8400828338ea819441421c1520c841d06c23028419504715483210302b286420843a01846050832
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s0K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/73+packedAt s0K4 (3672+(h % 73)*8) 8) % 136)
  | 3 => 2*((h/30+packedAt s0K3 (1900+(h % 30)*6) 6) % 50)
  | 2 => 2*((h/10+packedAt s0K2 (441+(h % 10)*4) 4) % 9)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ffffffffe03ffffc0ffffffff01fff1ffe3f
  | 2 => 0xf80fffffffffc07ffff03fffffffe03fe3ffc7
  | 3 => 0xfff01fe03fffffffffffc0fc03fffffffc63ff
  | 4 => 0xffffe0003fffff80ffffff0003ffffc0ff83f8
  | 5 => 0xffffffffc0000000fffffffffc000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x409225228a2389122c02cb2d54b10e590dae1b
  | 2 => 0x4e8449451444872454b015569957222a62d6c5
  | 3 => 0x122e1089a689124899554098c26a54b4b4616e
  | 4 => 0x64c89d163912240ee669a603138d9b08db83b0
  | 5 => 0x870f1e183e1c3870fb8e38e3e00e1c30ff7800
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40978
namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffff01f81ffffffffffff000ffff8
  | 2 => 0xfe03fc07f007fffffe0f80f80fe03ffff3333f
  | 3 => 0x3fff80007fffffff000fff0003ffffc3c3f
  | 4 => 0xfffc00000007ffffffffff0000003fffffc03f
  | 5 => 0xfffffffffff8001fffffffffffffc0007fffc0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2a186450a1a011c380318d18d1a38b1a055578
  | 2 => 0x8ca9293146ab224d9606a46a4dc4956ab3331b
  | 3 => 0xa95250a26b354496aad048b6e48926b35c3c2d
  | 4 => 0x306362c58dc6891b4d6b6e04891238dc6fc036
  | 5 => 0xc18383060e070e1c718c70c70e1c00e07aaa80
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40978
namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc02c000600004008000000f00000008100b00020e208200000104fe43fe32fc41ff42ff32ff20fe42be40fe10fe40fc21fe21ff40fd10fc10fc43ff30fc20fd41fd30fc40fc32fd21bc40fc31fd31ec21fd32fe20fd43fd20dc31ff41fe31fc30fe30fc42ff31ee21ff10de31ff43fe41ff21fd40fd42
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x410000cc1831000000201c0030c0030100000040000000c640002020c40000000030038000060002100140009c000011a0c4810600103020400202240012a040000000000080010100041820400006140005b14930baa8e856d52d067ca818e78c440cf2a0636e52d06bea6885754f429e2a2416e520c2eca3a14f15130b7288435e53842d8a4885d14520ae29a83cc31886f6a0a0cfd5130baa8e87ac21903386220750c4219f28481ba501027aa810dbd4931afa9a436f52506e8a2985b54a10f3208437651102bca790f908610f2188436f524c3cca210db14931b629283ae21102f0a0a0f50c721f2108216e52cc73c63204f55031f2a0843d6510c79c6210db54840ae29a216f52442baa7a0db54830baa88816e52d0f5ca810ed94440ceaa0635e530827ca0205dd4530b6a9663d6410c6bca7a0d754c40b7290819c31902bea6a0d794c40e2188435c53482dca310d794f429f2a6613d54c83a863085794431d710c81d5410c7986210f50c410aea98415d538437081884f15110ae29a43b5511027ca810cf55330d6a90819d53102eea2905d14532d7290816d52d0eeca3a1ee10010cf298816e52843ce6210cfd5110d610881ad54086bea6904f95320e6990655d53c879c6310cf55310af28c633e54c42eea2994fd5120
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x208050000400200480138481b1185320cb15540c421e1990310861d650c440e155031087843108440e10c421902546154c2099185520c2a5640c421e19503108746520c610e40c440043255254440b118d41087155354440b1189410c7a02110010d194c2184385640c421b198631086d06050431b8181410862d6508440
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4040a0aeb3206210d05750c42110242bb4a818843815943108440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/36+packedAt s2K5 (736+(h % 36)*6) 6) % 46)
  | 4 => 2*((h/95+packedAt s2K4 (3159+(h % 95)*7) 7) % 117)
  | 3 => 2*((h/22+packedAt s2K3 (912+(h % 22)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s2K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 3 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 1 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 3 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40978
namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x23106101dc31de30de43ec42ef20ef42de31ed20dc30ee21dd43ec21
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2006029585050ec8a2904b15120aa28a8756518c2cca3a1710c421
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s3K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/9+packedAt s3K3 (189+(h % 9)*3) 3) % 7)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffe07ffffffffe07ffffc07fffffff1f8fff
  | 1 => 0xf01fff80fe03fffff83e07ff81f01fffe4f33f
  | 2 => 0x1fffff0003f03fffc007fffe001f80f8fc38
  | 4 => 0xffe000000003fffffffff80000001fffff003f
  | 5 => 0xfffffffffffc003fffffffffffffe000ffffc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x50c1230a1450108600c628c21a51c59509855b
  | 1 => 0x654a45262895251a581a835689624ae664b32d
  | 2 => 0x4a938a144d5a43aeab4125a75c449334b8dc38
  | 4 => 0x831b1c58b1e38a3d35adb03451091c78ff0036
  | 5 => 0xc1c1060c1830c31c631c638618e0040d66a80
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40978
namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe07ffffff01ff81fffff03fffffc07e7e3fc7
  | 1 => 0xfff80fe03ffffffe0f81ffc0f80fffff93ccff
  | 2 => 0xfffff0003ffe07fff001ffff000fff81e3f0f8
  | 3 => 0x3ffffffffffe0000000ffffffc00ff
  | 5 => 0xffffffffc00007fffffffffffff00001ffff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1230a145011c1180318a310d28e2ca2a2615c3
  | 1 => 0x445262895224a29606a0d544b12552cc92cc5d
  | 2 => 0x98a144d5a44875aad04969ae2249ab296370e8
  | 3 => 0xd1c58b1e3891474d6b6c0c28848e3c71fc00b6
  | 5 => 0xe1060c1830e186718c718e30c7003041d9aa00
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeac800c800eaeaeaeac800c800eaeaeaeac800c800eaeaeaeac800c800eaeaeaeac800c800eaeaeaeac800c800eaeaeaeac800c800eaeaeaeac800c800, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40978
namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x5009003001000000007080053086141049041440005000044007fd10ff31ff32fc42fc32fe42ef32ff41fd41ff20fd32fe41ff21ff42ff10fb10fd40fd30ff30fe20fd42fe10ec32fe32fe31fe43ff43ff40fe21fd20f810fd43fd21fc40fc10fc20fc30fc41fd31fe40fe30fc43fc31fc21
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x821df320cbf2a8087bccb21fba0a837e51d0ff6a8085f94841b7294637c524c3f463887b95332fba0c837e53487de40107bccb30fd182417d51c82fea818fbccb41fd204617d50887f660086f10e40bf280836e52106fea8107e88010fca1621ef32883ee4290fbcc921bc282877d5110bf6a090dbd4931fda0821ec32d02eea2987ec8310fc980217f54c43f280987e54043f7a8865f840c43f060085e54032bf28663f031043de4310df95320f799261ec32506fea498fe90410fd884217e548c37c84a17bcca41fda06617e51103f242085f95331fca8683ec32c86f2a021dfd4c20bea98817e54487be65195f94a31bea88877d54482faa1a1dfd4540f7294637f5250efca8187e44010ae29a837d53887d865107e10c10f799221fa53042fca2085f94a10fda0441ec43ccbf0a5885bd4943bda82437d52d0778a898df54732f619661ed4210bde85997e94321b7298657a500cbbe6318de54242bd28421ee21486faa1197e08410beaa061fb400c3de6410fb0cb41bea8665f920082fca6197b0c930bf2a643ec320c3f083885f94640f6a9083ef324caf8a918db54a40be29841f331043f6a7887b0ca41dfa1485dd320cbf261105f15132beaa4617d51103de84905fd5131bea9883ef328c7f685887d48421bea94817f504cafaa898df55021be282657f51483bc6298df95043df21083ec32487f2a6087e0c710bf29e817e53c82f8a9197d14543f628865ec32442f8a810fe90b10fd18621ec430cafaa9087bd4032fd98261df4390ff462085f94421be282877d53d07d8a9997b50b32b7294657d51cc3f4a198fed4810fca0081f431042fca8195f55331ef19265f942042fea8987b0c821bfa9421ec42087f0a4087e4c030bea88657e51d0bf287885f15321f799081fb20042fca5197bccb20dfa1c877f53443dca420df94641bf2a083f840043dca5a1df94f21bf29485bf41107f420085f54f10be2a4437c5350bde65087bcc841ef988637d54487dea4987ecc710bd286437d5010fe8a2986f10a41dea0883fa52c43b88718df94843bea80637d52906fea090df54032bea90617c540c6f8a2a1df94732bfa98217e544c2f8a998df14e21bf290437e54103f460187b0ca31faa08837d5090bd865907e95310bea9621f854c42f8a8087b50832fc206617d54902fca4195f54e32bf280657e52907f082087b10b20bf284217f54843dea8197bd4941bc28243ed20082fca418fbd5332be2a641f820c43de4210fe14143ba28a616e528c2faa8987e14121bf29887ec32103f263887e48310be29e43f610443f684085f54f20fb98821ec32842f8a6887ec8220bea86837d53d03ba6218df15210bea9a417c53042fca5185f94342bfa8a61fa42043f081107b14931be282856f524c2faa9885f55220bea8c81f95090afea8997e0c410
  | 1 => 0xe52103788720fbd4732bf284657e50887d88490770c831bfa9c21df53487f2a7885f14530beaa4857f52043de65885f94830be290217d54886faa720fe88020fda04817e52082faa518fdcc631f7216436d52d0efaa7087b0ca40bf2a4657d52d0efca1207ed0f10bfaa4417d54442d8a4a0df54840bfaa2437d50c86fca00877d0c31bda8287ee52043f2a5886fd0040afa9a437e5310a78a890fd88421bea8c41f930483e88218df54021bf28c657e51082daa518df54b31fca0621f932c43dc40907e94410bf298417e5488678a8987acc810be2a661ee540cbee63085e54341bf280877d518cbeea2a1fb54810fd19621ec5250f7c8620f78c831bfa8a87fb3204278a898ef15130be296217e54882fca2197e90f10f6a9461fa404c3be86a1df54a43de2a2437c52442fca818dfd53329faa2437d5490fdc8490df54231f7994437d53902fca3905f94631bfaa6617b50506faa8105f94030fcaa621ef42086bea6a0fa54032bfa98437f53c42fca610f714d41bfa9221ef5250fee4310fed0310bea86637d544cafca3987e50710bfaa061f9500cafaa8197ed4131dfaa263e832043d865887a94032fd10821fb52c42faa321df15220bfaa2417e50d06fca8105f15230fd28065ef32506fca3185f94242bf290857e544c6fca9986f90d43fc190217f5050ff0a7887bc8520f6a9463bf54486fca9887ec8710bfaa443bc43103de85907b94c32be2a2217e54842faa610fe10810f6280657d50906fea2a17e14131f619443ec42ccafca710df94d10be28283fb30c42f8a7107b94a40bfaa2217d5190afca69077cc230fc986217e53106faa2107e88310beaa463ef4250bf686085f94b10beaa6437d52843de87995f55330fda0e21ee51ccafca010fd4c431bfa9c41fb53043d88510df94e41fc18621ed50ccafca618df54743bf29681be40503f640907e10120fd284857d548cafca121fe90710fca0021f932043f6a0a1fbcc940f799465f843c42faa5a05f94e42f7990217f54c82faa6105f54e42bfa9e43ed21483daa2197e54331fd19021f921c43bc60985f54f42bf2a221bc43107f620887e90c10f6210657c5150bdc87995b94810df214837e5290fd8a4985f54e31bf28441f854043f0a6085b14931fd20081ef430cbd8a3995f95010ee218637e52042f8a9887b94032bd288217c53506fca918db54841bea90637d54c83daa0197e08710fb884217c54482faa1a17b4c832fd29e21ef32d02fea998dfd4142b6a90217d52883f680a06f90e40bea90837e50907ea20085f94f41fb98a637f53482fca1997ed0010f7190657e51883f282085fd4141f619281745150efca7207b0c810e7298657d52042f8a8195b14930eea18877e52442f8a498fbd0a42f799061bd4310feea2985f94040be29a81bf40903dc86195f54c42fd90
  | 2 => 0xf002098020a80a0042200c06020000243b0000e00c0203c000700d08820000000240f6800500c03050030100102c0a00000390020185302c00000210080900000004000000d158010c0301d416000040241c0189600c0502831030260540000da500c1c01400004020005d00010010000001b000000000100de908802108939440200c002dc00000000000109c01088000000600407000011400504c0a56c09000010000025c290080b00c070001204840018018c809074000e00006c00000000200100006000000000c1540000005014030000204c0c040a100852000120000c00001028041301c00001024620000213838048173097002d970703101c00008080281800800058030002c0180100c18104000300502000008000400d0000e004b3040140000327c02120030843100c00f928821ef320c6faa3185f14d20bfa9261f9408c2faa790fe54321f721665ef328c3f460085f55241fd20621ed52d0e7ea898df14f10dfa1887f641106fca118dfd4b10f6aa6656e52902fca5a1ded4131f628665f7410c7d86420dfd4d40fc200617f5350bde8510fed5310fca1821bf544c2fca5985f94442bba8a87ee510cafca5207b50f32be29a4378504c6fea8085e94331beaa021ef524c6f8a2905f54430f7a86657e510c7de64107b0ca30bf280417e5190af8a098df94321f6aa0657e52d06faa818df14e10bf28c87ef420cb7c8720df14943fc100217e530c3ee8398df54243e6194637e5010bd86418df14532bfaa463dc328c7ec6218dfd4e21f721065df300c2d8a4a1df95021fd98821ef32cc6faa0215bd4941fd2a0217e5110efca6207a94810f6908437e508c37a84217790c43f7210857c544c6faa7185fd4941bfa9281df438c6fca220dfd4d21bd28087f850506fca598fb50b21b6a9461ef21c83f661185f94740bca86433f544c2faa3a07e94043f6a18657c54082fea810fe94810bea9443be41506faa5185f54910bf29c41eb32c43f262085f14121f7992637d51843f461107b14941bf298217e54ccafca721f714d21bf28861fa50d07f240087bc8220f799241e952042fea990feccb10beaa6657f548cbf2a4085f54d21f7294617d53443dca1995b94b43bf28c437e53d0afea7907a0cb10fd20021ec32cc6fca7887b0c820f690e417c53087bc6518df54742be2a0617d5210fde65205f14f20bf29c217c51503daa520774c030be294215c53486fea9185f54e20bea9661f710042fea098efd0641bea8083ec324c7da8490dfd4532bca86637f53506fca8215f94031be29281fa21c43e88398ef50040f6a8e65ec540cafca1a1df14941efa9a837c54486f8a8987ed0120bc28283f431842fea8197b0c920fda82837d53042f4a1a0df95132df21881bf4210b986418ef10841fc216217a5090bf065885f15332bf2a2417
  | 3 => 0x197c0004404060111a80a354130000d068050080202ca90000000408018511582704c000002303019010000000002807000071fc000080200007020000080004c3600c2b11c1f074160540000002034020000703809048040082a0049f02004000004f02e000041c8000680000000000160381d07c000001a080001
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xb5150f2d5415032c714e415063e65151219e983548c7d3430c41097d8d5110a5e63d4a10dad95520426e62150319b98b548427b6054d21d614c505066d65cca40d9145214827960150319b58a50cc63e6495121ba58054cca7561d4f20ba98242ccadb6348410bc987530427965c8410ae990530432f540c921ba98a320427b60551319b18d529031f54d4d21bcd85300429c644c431d91485150f6b32d4141ae19121c436852141319b597320432c5490921ba594320426e62d50309e996404c35853d41219ed95430427860547439e583540873960151309e195404c26c6254d108fd91534834e530cb20cb55042c827a6094e419bd89544c2f26114b10bc586300427b6550410da549300426e621502197594430c77051d4143dc583514c27b6055221aed91300437260d45439b98a50cc6b46150c439d587548c36a6294331ba580540caea6215010da0c950cc6f3650c410ba185500ca3f6454c10bc58331043733114131b3986530ca786054443f20ca310436b32543219b597430cae86054432ba98a30482ac6448720cb588544866d6295131d3548328c6e960d50329ed95310426e6394a40f48c8310427960d5331ab990510ca6d65108219ed815110eea6010f32ba58a404c26f650c810b398c540ca6e621531097d8d544836860548109b58b548c66e6215231b398b430c72c5290541ab590510ca6f6254d109e99642043b14110410f10cb410c7e25294410bc987430436a6094810bc18532042f165944109b98b530825f6355121ba98054ccb6a6094a309e582534874e62d4d418fd9152442d86350710bad8943c427a60d52329758c548826d6295130ba98841c436a5248010d30ca510c66c6255110b9584540ca7a6094a31d394c321027a6094841e350c430cae76150f329bd89530426f6255110f10ca310c66e62148109b98b53086e962d5010cdd53514c33854d4131dad4d520423e64d4e109ed8151d0f3854d41219b189544c27861540329e59642042b8644c010f894b31042796094d10dad48505076a650cb109e582538874c53cc9209d98753c82b8644c410d90cb514c2ea62153109b588530427b65500408f59253486796584010ba58841042ae6414332dacc850486796094e41cbd5254ccb3a43141439e181510cae86250710dad4b5050e6e62d5231ba98a30c43696294043cb150324c25e63d52109b197325063e6414c21ba98a31c42bb6448710bad8154ccae9628c0109bd97320426f6255121f8548310423c6454910bc594310427960d5232bc98752c426e62951319e583540ca7a6095231da94a51042e962d0c10ced5350486796015032d614d304826e62d5010b398f540ca7860551319e99443042b86454c109718d54482e9600c921cbd50324c3683294321f294e500ca7b60547429e58252d0e6e6214c10
  | 1 => 0x426e6214540ce151404c26d62d5030dc5973104369650c810f2980328c63c6454432da98a50d067b60553329bd8953d027a60d4543d6d4f505067a6094e219dd85544ca6f6254c20ce95140c426f62553109e98053086f26115310ba597320426c62550319b58b548c2e9628c710ba98321483c5610c831b618d410426d650c821d314c525067565104319d58454c832c54885219b588548c2d8634871097d954310fe33294410ba980324827b60546429e5835150f6b32141418f19153482f36150f10ba988410427a6014c209e59430042786054632d314c324872c54149319b98f525067a6094b43bc984540436b3294321f80c8310426d62d5331f20c9300c36b3294331ba98a30043685214143f8ccb310426f6254d21da94e500ca3c6454d10dacc8504c76852d4131f10c8410c6796094841ab59351ccb6a6094841ba18941043395415010ba583510ca796508010ce150504c67a6094d219e58354c866f65cca40dad95500ca7b6054732f2980320c6e86048720aed9153042eb6250c10bad8954c42796015321b9984540cb6a5354032d5d0c5150e5d63d52109e582544c72d5410832bad94320425e6315010bc18543c426c6254e41da151500ca7a60d5032d314a314c66c6255330cb153324c7706014543ba18931c436b4254032aed9121042ae64d4732ba98a31042e9600ca209e594320436b4254242b398a320c6cc624c431ba98a40c42f260d073197d95300c26c6254c419e59642c434c53d49419e18151cca6d62d5210cbd50524c67661d5230ae1814310f736014543bc98632043d1530c410dacca510436a6094b439b98a5190eea62148109718d544427765440109ed81544866e65cc931f2580320c67a60d5331da58a50d066d650ca40ba588530436852d4143b318d21c826d62d4d10d314c325026d62940439e58053c86eb6254c10ce153304c26c62553109b997325077051cc130cb153524c76a6094a319bd89540c66d65cc841bc98e510432c540c9219b58b530427a6590b109bd8953906796095110cb151424867960d4542d354c32c86f2618c4109b98b53502eb624c7109bd954210b4c530c9419ed95300c26e62d4d41daccb504c6eb6250410f20c831c423d6414e20bad9732042ea60d5032f00c8310431d5310c409e58353c866e6590921dc1445050e6e65cc9309b58854042cd650ca319b994325076b3294341daccb504873b541413197d8d54442ea62d5010da14850507696294331d314e42486f26114810dcd475050e7761551309b98a54cc6e96010c32cbd53324c66d62d4d40d3d4f325067860553329ed81544caf261d53109b98e520426f654c832ba18954c427a6014d42f298c320434c6214d419bd95200826c6255131ad58442106ea6214c10f498c310426e62d4c10dad4b504c69c6350441d914
  | 2 => 0x62d4d41da58252106ea6010c32cbd53324867860551329e994320427960153329bd95210867b60549109e582544874d530c840dacc950cc66d650c820b318d21086f06150c109b994324c23e6494d21bc181310c72f54d4930ba58a30c427a60d5021da54b409023e6515131dcd445050e6d6214540ba58032c865e6315220ba189310426f650ca40ba18143cca6c6254e409d987548caea630c810ba58b43c43683254321bc987520427b6548020ba58242c86b8644c310ba58854c43684254032da0cb50506e960908429b18953042ea6290010bad81430ca7965100308f99052c436960149309e983540832d5290841bc584420427960d45328fd95411074d62d4d21b51854310e6d62d4f109bd8954cc36952d00109bd89544cb345414530bc98453c43e152944109ed81540c6ce62d0e319ed81510caea60150328f59052c42e8624c3108f59353c43695154032ba58351cca6f65cc8419e98054cc6ea60d4432ba980510caea62d0f10b698c540431c54d4d21f20c831042bb644c710bcd85420425f6354910da0c950d067b6054c41d314c32886db63507109e59640042786054c41bad8931042ba6414b109b997424834d530cb419e98254486796014d42d9148514c26d650c8419e582528c66f6550c329b994324c65c6355121da0c8504c6786154043b618d21042e76150c32cb150524c27b60546439ed81544426f6254d20bc98754043696094a319b594420cb4d62d4d419e99443c427a6014f21ba58b53c423d6414c109e181540c74c530c9109798e534865d6395121da0c850486b96414b109e582524432c54d4930ba58b530427a6015030c7d50534866c6254c409b596520436953548109e582548c6786154242ab191510ca7a60150319ed81544c26e65cc921ae59353c42746154c40f1984320c74c5388521f854b31042ac64484219b98b540826e62951309e181544865d63150109b189538436a5454032d354c328427561d5232ced53504c67a6015332ba58a40c4277654c4319b58a50d06e46150c328fd95401026c6254f419b588540c6eb624c3109bd8953d072f54d4931f8948310426c6354810da98a5010f2f54cc9309718d5110b4f6214d41ba588540435b53141218fd91534863d64d4e109b596420cb3b5495310cd153314c66f6254c41ad191310c6746155130ba58242ccb4f6214d21ba18943c42f0614c0309e98354c867a6015032ba98b530427b6544010f410c31042e960909219e9835150b685454810d9ccb514c3675214530cb153324c3695294410ae19121042b8644c0309e18153486ea60d4732d9cc8514c23e6414e209dd85544c6776154c40d394c320826d62946438f19153486ea6394810bc185420427960d5231dc145404c34c5350921d3d4c324866e62d5230d394c32c866d65d0821f10c8310
  | 3 => 0x421bad8151ccb4f53149419758f528434e53cca219d984540cbc4320c610aed91310436b5214143ba980500ca786055221f294d500cb6832943319b98c52506cc63485209dd85534427a65d01209b594320436b52141318f59353c876952c8010da58252d0f6752d4530aed9130c43e032cc410da59432c42e86054732ba58a408c2f36150c109e99432c42ea61940329b194325067965100109bd9432106eb6254f10ab18941107ca630cb10d394c32087705190130cb150324c66c6254f109e596200434c53cc921d3594328c6e96090832da0cb504c7385490130ba596500caeb60544329e9875050e6e62150108f994544c27965d0410cb95142ccb5853d41419b98b54cc66e62d4d10ba58a401023e64d4f108fd9153442e960144329b1895110fe12108410ba58a400434e53cca209dd85544823f64544329798e54486786054442da0ca51042db63487109ed9521042f26110810f40c8310435853141218fd954310f69528c010d3d4f52507726194410bc586320423d64d4a109d18553482e86250c10bad8930042e965948109e594430426d62152319bd89538426c63548418f59353c836752d4543f8cc83104279658c010d90c8514c27b6550f10da54840042b96010e40cd90c5150ead6414332f2580328c6b96414c109d185544826d62d4e10bc597310427a6194032bcd8532042796510f109a594320433454d45309e1815190a6e62940439798f54c86f2630c4109e59432c436852d4141dacc950d066f62544439b98b53c427a6194043ab191214827a6015321bc98453042e860553329b58b540426f62551319718d52443c8328c710cbd50324c75b53d4121bc983410c76832d4121ae99353c427965d0030dad45500cb385414121bc5874304278654c1209b98e52106786054643da994320427860547429e195430434e530cb418f992544c67a60d45329ed81518cb6452d45309e9865090b4f530c9419e98353c866f6254c409758f54c86b8644c120c7150534866e62d4e10ba18953c42766115320bc18530482e96010f329b98a51cc2e863548109e580530866c6550921dc596510432c54cc921ba181430ca3e6414c109b988548c23f65508429b58854c42ea62d4f10ce550400434f530c9109d594310426e65cc9208f99352842e9628c410d394c328436b52d41419b58a54cc65f654c431cbd50524c37160d4543ba982420ca3c6454c109b58a544ca7965cc410ae19131c423e64d4f219e19543c427b60544429ed81534423e64951309d586544c31c548c531b658c5404279601533197d8d544c6766195130b398f54cca7a6114143ba189308825f654c832ced50504874c53cc941b918543cca6d6294730bc18530882d46350441bad8143ccab8644c220bc98753c426e6294341d9d485150ee96210710da0ca50d066d
  | 4 => 0x1c0602c0002c5e1bc1c060060182f0000518801000020f4020003139007000fb02c430340d034011bc130080c0641a004000009f0040304c3900c7801c030341405415000aa010020803306801024058a4010918005800048540000f00400000020480029c4221475dd4b90017a01c1a130020380201c0301c180f42e050880991e0041f0042502c25bb8070c06c15400018de03c1203c09179d3288000c0240102f0b4000000013c0f0080203005040612bc0304404014120cc01000330000007c000000477c055600100413000000080700004000161f8020125237e190000101001008b01303301000028130c800000002ccac0240d024001601ab98000442e1b01b0a014000210180200007010031380d010b1510000441a0d80b002080000000005a281801000000330a00006402008090440008400058140b81812c00114094a4160001d2780407405000170ec060080a038000085d014002300639c07018021e447000520dc4f078010fc2ab8c000b80203804061017547c020010000a025dc0bc000040803c026700b21016000060045306c109bd89539026f6254f109e982544c6ea62d0c109b18953d034e6394c328f99353c827561150329dd9541107375414530da95152042e86254c10f494c31042746155132dcd80514c36832141419799453486db63504108f59053087e03294410d514f415066c6214d20d3d4c325035b5314141abd91510ca776154d20bad8941c42e8624c010b398c54ccb395410220e510c410c6776548
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1c109361d782120c007001400000c0180040000200040051e3c10100102800038f800200000aa2ea1906208469760ca50cc6e139686188214a1d15154032b40e890842086c032983410c634bb06528683981855154032d82c2b006418e88640c9300c2a4ba86518821341cd6110810a92ea19062085c07354831042343b2a4980211a5d66210410a92e62a2a4085147154c4310234bacc5188218a1516090921e82ea190620862464145214830c320a698241895516115032b80e690842085447154c3210314322a4980219214d600c921b20e8a9862085c07254c3104330b2aa418821865516315010a90e6a9260084697699432042c23a2c219063585d432cc410b10e0a1886195c070584320c6a2ba864188211c1c56014d42c90a6b048490d907350441042e13946418821705d4320c410c88c628a429056171151500cb28298c2982411a5d662d0c10e84ea19062085a072504410432431aa6a9021381c5600c921c50a8b14809846975980430cae1ba86418821381c56090921898e6b10a2a05287454d5204360190c298061985885190130ac2ea19062087415354831042a0ba86418821321cd6290130b08e2a1886196285458032486e038ac019063251cd6110841
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x702410151203c41651cd520c410b008454d520c410c40531c56090921c20541c56090921a40835885190130941879d4320c410941859cb430c410c087418d53548108c1870ca60d0431c20541c5600c921c08641cd524c010a8084585600c831c40531c5600c921c08541cd6290130c20741855154032
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | 2 => packedAt s5K2 (i*60) 60
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/35+packedAt s5K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/343+packedAt s5K5 (22140+(h % 343)*10) 10) % 820)
  | 4 => 2*((h/326+packedAt s5K4 (33972+(h % 326)*10) 10) % 894)
  | 3 => 2*((h/43+packedAt s5K3 (3332+(h % 43)*7) 7) % 68)
  | 2 => 2*((h/12+packedAt s5K2 (900+(h % 12)*4) 4) % 15)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf80ff01ffffe03ffc0fc07e0ffffe07ee23fc7
  | 1 => 0xfffffffffffffff0007ffffffffff03ffff
  | 2 => 0xfff0001f80fffc07fffff800fc07ff81fc38f8
  | 3 => 0xffffffe000ffffffffffffff0007ffffffc0ff
  | 4 => 0xffffffffff000007fffffffffff80001ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2aa555548aa23895c02ea1702ea96a6ae21bc3
  | 1 => 0x254860c1144449224b0102a95532b28d00ed5d
  | 2 => 0x306d4a8626689073d555a80899a4db296c38e8
  | 3 => 0x4181831458912244a69a34d202070c70b740b6
  | 4 => 0x860e0c1860e1c38738e3c71ce3c01041dbb600
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800fc88c800, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40978
namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c007ff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08401fe4301ff54805fc52007f10407fd5100ff08001ff4101ff14c03fe2000ff90003fc30007fcc407ff51007f50801fd41007fcc801fc43007f44007fd50007fc4007fc5400ff84007fe51007f8c401fd40007fd0c01fd2001ffd4807fc5101ffd4001fd43007fd0007fd54007fd0801fc3101ff95005fc32007f4c801ff3001ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8a6200bf59330007fac71081afc65cc001fe90a2000ff0c520007fe8320803fd6348403fe206200bff59530017fe41a101afc6590c19ff90e6001ffcc120007fec0a1003fd4310401ff30e8011ff15343037fec52187bfe408c45bff0868202bf58b42007fe84a081aff6510c057e3148201ff4c310037fca698007fa30cc001fe90e6037ff880431effaa6a180afe63cc835ffa8c6202ffd49420dffc80988abfe515042d7eb2c4205bf59510037f865a1807be4050031fe2906200ff4cb4112dfeca2080bef2148049df210823dffd4543067f8a598007fc404804fff28e821dff54d31005fac3a1017fd524400dffa98862eff08741005fac02084bfd65d0001f690a4003bf9962100ffa609009fff54d0413ffa8a4035ff94342007fec488006fe604c41bfea966019ff548310bff820188d3fe5450805ff2926406ff0cb31095fecba00fbfe1090c17fea926000ffd0e41007fa4298003bc439046dfeaa68400ffd0d32015f8c498002fd61cc875ffa868600bfd931001dfcca18803fc6344057fe2848201fe1431017ff8a099007fe4048085fe10e8600ff18d21037fcc121806fc604c403ff0868006ff54e43057f8a498002bc6448403fe0822006bfd9031005fec4988ebff54d0c037f3028206ff19331027f8848809ffc53d044d7f3088209fb5492000df8c11081bfc434c8037fb124011ff18341167fca520813fc624400dffb0e6406ff14f43015f8c51881aff64cc423ffb1e8002f78cb3200ff8219802bfc424c005fe1068400ff582210d5facb1883fff51500017fb162018ff1083113ffea3a081bfd6090c057f3108200bf18542007fc4288033fc42cc003ff2822001bf18031037fcc421803fd644c001fea086200ff0c621007fc63a000efe6548401ff10a6017ff08031007fac690003fd43d0003ff1862001ff8c140005fac3a184bfd53d0001ff31c8200ffd8d21007fc629883efd6550001ff9948200ff88730197f8a999003fd6250005ffa128400ff4c74000ffe408800efc6588401fea0a2001bf98231036facb980cbef52cc801fea0e6000ff58d1000ff8209800bec424802bfe2044200fb88521017fe6499003ff6150c01fea166000ff107101b7faa1a1067fd540c405ee1966424ff90841035fcc69080bfc21cc803ff9066000af191300c7fe4018803fc415000dfe29e6400ffd0731007fac3a107bfe108c405f790c4213ff90121007fc86a00cbff54cc8057e3128611ffd8b41015fcc421803fe6350001ff3188206ff98043137f8a3208effe1050c057f3106202fdc8521017fea499027fd6548003ff1824000ff10e41147f880a080efe6548073ffa808601ff90310007fac918897fe5310449de2108200bfd8121007fa871886ffe104c401efb1a8213ff8c12108ffec3a1807f410c4035fea9c6205ff55110
  | 1 => 0x3fc6488401bfb2a4000ff58931037fa8618853fe5448401ee31a4237ff04043005fec488052ff654843fff214621eff8c231007f88710806fc6010c01ffa162000ffd0940037faa79801bfe61cc001fe98a600fff9454008ff88421803ff3250401feb028406ff18b30037f8a798807be40d0001ff3226001ff84130007fac72081afc6344001fe31e2025ffd4441137fecb2083ffc655003dfe2046202ffc833211ffc802085bfc5188483fe1068600ff58343007fa85a08effc4050c037f30e2000ff8c530005f8c9880dbfe53d080fff28e2000ff18d40015fcc9a100afc62cc455fe28a821bff10131017fea510803ff6290471ff9008600bf5931019ff8a0a1003ff4350801feb168600ff50d301dff8c0a180afc6244061feb2a640bff54d30007bec690803fc4350405de2168402bfd892113ffaa1a08a3fe105040dfeb2e6006ff8c243017fe849001afe630c40dff3266002ffc8742015f8c418807bc40500077f32c8234ff1454219ff8c0a101ffd65c40017e3224209ff94520007fcc888003fe43d000dff30662009f59730017fe84908cbfd54cc8017fb12862cff8ca41037fe879889fff53d0429ff28a423eff90243015fcc4a180bfe324c801dfa0c8202bf1893115ff861208e7ff5410c0dffa9c8600ff90c41005fac898043fc52d0055ffa928201ff8c34000dfec09000bfe20cc801ffb02643aff54343007fac290003fd434c471fe1088606ff0c132017f841990d3fe515086fff2808602ff94942017faa5a1003ff63508017eb1e8001bf98041067fc859801b7d650c481ffa8c8600bf58d10037fccb988e7fd5410c03fb086202dff88341037fc869880efc654c40dffb28623affd4f43037fca79805bfe5488459fe1948240ff54a43007fcc988003de314c403ff2028000f7d0e43005fac398013fe4244001feb024206ff9944313dfecba081bfc30cc403fe2028011ff15341007ea822080bfc324c803ff8822001ff50110057fe4298047fc41d0077ff1828626ff5464100df8c118807fe40d0079ff9028641ff88343187faa29900afe62d0403ff2826001ff501300c7fc84188dffc2010c05fea166403bf19631157fca8a08effe4050c0dff2986200ff0c540177fcc5a0803ec624c46bfe0868401ff50330027f8a488017fe534400ddf21a8606ffd804302ffcca8809fff50d040dfe3008606fecc130007f88318897fd53104017eb168612ffd47400b7fca310803fc31c40017fb128002ff10b42197faa199063ff210c40dfeb0c8602ffd0a2100ffe6188003ff61480037f3068200ff10531007fac3a1802ff605040dffb288600bf18540035f8c998007fd204400dffa9e6439ff54043027fe428804ffc4048401bfb2a200aff909300dffc609888ffe101040dfeb0e6400ff0c52104ef8ca9001bfc6090c3bffa
  | 2 => 0x41167f8432081bff53cc403ff1826000ffd0d211affc21a10fbbc4090c03ff2022002f78c932217f8a5a183fbe5450071ff2108602bf1884309ff8a090823fe52c40017f3222029ff0c94100ffc8198047fc43d0401ff9968202ff90b3201df8cba181ffc65c4001fe2086200bf99132005f8c899003ff3250001fe20e6017ff90031007fec89801aff64cc8017f3246202ffcc92002ffea288003fc414c00ffda862006ffd9330187fea099037ff51cc04dfe2a48202ff9492100f7881a00c3fc544c8017fb226200ffccb1000dfcc0990c3ff544c801fe9948202ff949200cffea21880bfc52d080dff29e641aff946311b7faa7a100efc6590405fe10a6401fd04110007fcc2a109bff5090417fe32a6006bfd943107ffea4a0047fc401045bfe0868202f70c932107fc419883ffc51500557eb248200ffd0a31007fa87a1006fd60d0001ff21a2000ffd093108ff885a080bfd52cc84dffaa48200ff10f10037fa6218803fc4350805ff90e6428ff981411effca2a1807fe404c013fe32a4006ff90f30007fe852081ffc51c4005ff9924200bf58b41137f8cb2089bfc5390483fe0868602ff8c942037fca621877fe514c40def29e6006ff90c31007fe831081aff65cc401ffa0a8209ff145200177c85a1097fe6510467fe182843abfd974305dfaca9802fff514c00bffb2a2000ef90c4101dfccaa0002fd608c4077f32a842effc834108ff885a1803fc4348005fe296640bf794d3000df8c1208e3ff2110c0d7e31a8201bfd8110205facb21802ef625040dfe29a6401bf9822109ff8c090853fc5148401ffa1c4215ff14221017fea490003fc4348403ffa022036ff9974201dfcca8801fff52c405bff2868206ffd8b30005fec71080afd628840dfe314862fff18132007f8c91881afe63c4001ff20e6206ffd8b31015fec290803fc31d0055fe32a8206ff1884315ff8c12081bfe434c071fe2908602ff0c9420a7faca90803fd4110403ffa066000ef50441017fea49083ffe5450023ffb1e84009fd9510007fec720803ff4350401fe31a8406bf98c41217fe41a180bfc42cc8017eb244228ff14141117f8a998803fc6150c73deaa08602bf18941007fac51885ffe100c40dff21c6200ff58943037fac598827fe5448053ff2928202ff94a211cffaa421847ff65d040dfeb286203bf1974203ffca988007fe10cc00dfe98e6031ff0433200ffc2088007fc40d0045ffaa66200bf58740037fc621880bec21d081fffb2a80009f59431007fc6288017fd534405bff3068222ffd43311effacaa181bfd600c47ddf2048601ffd0130037fa6598803fd434400dfea1e6006ff8cb3120ffca1a1897fd651045bfe1068221ff08731037faa61888bfd51cc405f71966406ffd8331007fa628801bfe31cc00dfe3066223ff8c04100df8c19880
  | 3 => 0xe0866200ff58941007fe8698807fc3048023ff2a08202ff8c920047f8c588087fc42cc437fe2826206ff0c73003feca3880d3ff5450801fea0e622bff082410fffca51883ffd5150023fe32e8037ff8404300df8c1a180bfe324847dfe1048600bfd8543017f84099047fc43d0003ff9826036ffd4742007fe6310803fd42904017e3224008ff0cb10007de8510887ff20cc403fe2022006ffd973003ffaa388103ff5290c77ff3028613ff0c12108ff8a821802fd6190c03fe2066006ff10e31097f8a3a0002fd6010c35ff32c6201ff4c1101e7fca4a181bfd5310c23fe32e8400afd912108ffec1a081bfd43cc82ffe2006202ff0c92004ffaa290003fe6488423ffb168602ff5093208ff8cba18c7fe10cc869ffa828405bfd9510037f86298002ff63504037e3048600bf58b10017de41a105bff6588401feb028212bf5974001df8ca90803fe6388405fe1924202bf18940007f8c8988dbff54d0805ff2168401bfd8140037fe6518866fd650c40dff9926200ffd9221037f8c1990aaff6550429fea8a4206ff54f3208ffe8420903fe5490c69ffb2a8426ff54241097fea5a00d2fd65508057fb22843dbf59243187faa099097fe5110401ffa0a8000bfd912008ffec3a101bfc65cc469fe32a8434ff54542017f86599006fc60cc835ffa946201ff10130197fea19901bfd6210c69fe29a8431ff94332007f8c29006bfc518c441ff2866202ff88132177fc85a081bfd4310c01ffb048209ffd95201eff8a2a1806fe60d0c017f3226015ff0c221137fea720802ff614c845feaa66242ff90b43007fac78801bfc434c43bfe28a6230ffd4d32007f8c720803bf644c0037fb0a2000bf5803113ffca7a0803fd62d0423ff2a68000f74c431007fe8388047ff65d0c81ff28c8600bf5884315ffc4120802fd648c401ffa1a802bff98241005b8c6a0803fc614c005ff194420df754f30037fcc598002ef624c425ff28e8020ff0833100dfcc121876fd638c401feb126000ff58d410b7faa31080afc62cc0017f30e6000ff90f42187f8a299007fc5050023ffb188200fbd094217ff880990ebfd54d0c53ff192821dffd9531007fe8788002bf644c44ffeaa68200ff98f41155facaa081bfe300c401ffa0a4000ff50b310effea4988bbff21d0435ff2a46206ff94f43005fac121807fe30cc001feb0a8400ffd0521157faa2a0807fc50c4005ff9944201ff8c110015fcc49880afe6250451fe1828206ffd9332037fec99881bff6590c01fe31c421dff9513105fbaa6980a3fc60504017fb224200ff10510117faa198802fe64cc001ffa1a4002ff0ca21007ee83208bbfc52d041b7eb2e6003bf99541007f8c690047ff42d0003fe2824006fbcc932007f886a000bec21cc87bff2a2860eff94940007fec4a08ebfd52d0c017fb0a8027ff54b
  | 4 => 0x806fc6050c75ffa8e860bffd4930007ba8621802bf644c023ffa188214ffd5121017f8a499107fe40d0c51ff102821cff8c93100dfcc1a1003ff604847bfe32a8606ff0c143037f864a188ffc5010413fe29a4000fbcca21007fec7880c2ff654c853fe10a8216ff5962101dfcca208bffc104c817ff2a26000bf18530007b8871881bfe53cc4057f314822cff10a41137faa520877fd654c401fe3224239f754c431effaa2a1803ff438c4057f3166200ff90f41007fe8598003fd62d0001feb0a8000ffcc710037fec018802fd6110c29fe29a4221ff90b31037f86498802fd6088417ff32a6000ffd091008ff8c1a1802fd63d0401ffa0a6200fdd05410effaa29881bfe30cc87dfe2848606ff0ca31005fec6908affc1090423fe3168000bfd9132007fac2a18d3fd5050849ff2908206ff5903102ffca288003fe6448035fea8c6216ff19621077fc64a001bff65cc401feb226206ff18730015fcc598003ff420c40dffa1c8600bf58d2018ffc8199003fd624407bffa928600ff90621017fa6510803ff3210423fe2188239ffd444306ffca398047ff41d0033ff288623dff99543037fc602180bfc424c82dfe2a44202ff8814213dfacba08ebde53d0c4b7eb288200ff59121005fec8980d7fe60d0865ffa8e6400ff9054110ffe439881bfd620c403fe286801fff98a31007de84900b3ff209040dbf32e6011ff103420d5fcc218802fd60cc401ff98a4016ffd52210b7fea110802fd60904137eb2a401dff995310e7fca49880bfc2188401ffa12602aff1514100fbc619803bfe6250069ffa9a8442ff98b4308ffe87a0006ff634c001ff98a4225ff14441015f8c52182ffe514c0037f3028602bb18931007fcc890803ff418c40dff308863fff94a43005fac9988affe509046fff2008621ff14b31037fcc321807f61044001ffb1a4002ffc8132007fa64a0823fe32c400dfeb288601bfd914000ff04090103fc5190c0dff3148606fd4c431007fa87a080bfb20480017eb224007ff997101affc61a1003fd6310455ffaa28211ffd88410d7fecb1881bfe4350c05fe10a8406ff90f3200778c89885bfc538844d7eb2c8225bf98641007f8c2a1006fe60484017f30e8000bf9844300fbc609808bfd52cc44ffea9e8206bfd933001dfccb2181bff6090c69fe2a28425ffd4841207faa12181bfc6510c0dfb1886239bf5944300ff860a0043fe52d005fff2826402fb0c93220ffc21a180efc654c0057f3162000ffccb40035fcc69001afe6310c01ffa1a8626ff55241167f8c52082fff654c00dfe3166202bf98b4300ff060980abfc5350475fea9e8630ff55132037fc862181bbd4310c03fe1862006ffd8332077f864a001bde5310c7dfe2048600ff0c51000ffe608801afc6510c25df2a6801eff14231037fac5980effc5050c41f
  | 5 => 0x4441015fec4a1006fc60d0803fea824000ffd8d40007fc82a008ffc30104077f32e82039f99730005fac99901bfe65cc001ffa0a6001ff88120147fca0a080bff52d0805f61944203bf1954000ffc41880abfd5450429fea82422fff98132005fac418847fc6210423fe2068600ff18d41005f8c9188dbfd65d086fde2008606ff14e311a5fecaa1003ff434c051fe102823aff99743127f8642085bfe6588401ff98e8004ff949102077ca921827ff53480077e32a6416ff55221037f8a698803fd63d04017eb1c4200bf58b30005f8c299043fe62d0001ff9922018ff94831007fac420803ff608c4177fb2a600cff94b30017de419901bfc65cc829ffa9a4200ff9913200ff8a098083fe10cc401ffb162000ffd8d100077e822081bfe3290c23ff2a68400ff98532037fa8798803ff604c4457eb2e6202ff50a2103dfacb8801fff54c4005fe992403af754f43017f8411080bfe204846bff206840fff1514019ff820a1017fc514400dff98c6206ff10c3108ffec1a1803fe6150c017eb226426ff99641035fcc31881bff320c40dff9926006ff54f31007dec4a081bff32cc001ff30a4002fb94920017f884a101bfc3090c01df20a8201bf981421a7facaa1002fe64c4001ffb246205df19510017fc84990dbfe51d080d7fb2e6400ff10d10057fca49801ffc54c40017e30a8603bf997320a7fcca90827fe6548081fea8c8600ff58342005fac52081afc65cc81bfe28e6027ff5974100778c89081bfc43cc001efa1c6200f7d0d43037bc8621847fc4010c0dff98a6219ffd483118ff88199067fc510c455fea82822cff90a411edfacaa1802ff61480017f30e862cff14a4100dfac188002fd634841fffaa28011ff183421d5facba1803fd3250003ffa828003bf9953216778852081bfc3290c017eb146202ffc814208ff8c020806fd60cc02dfea844210ff8cb40077f842a0003fe634840fffb2e20039f19520007fc8388017ff5244001fe9962002fb14b3200ffea18801afc6350003fe1868000ff9052100dfec09809bfe5390403ffa824006ff1943116ffc81a0806fe64d003fff1946206ff94d32047f84388003fe63d0013fe2a24006efd0e4307ff8a6a001bfc434c00d7fb2e600dffd4b3005ff8a298003fc6444055ffa828214ff1512101dfccba185bff53884037f3048211ffd0441017dc85a10cffe505080d7e31a4200ff9052020ffc61a1803ff6088459ff90c8202ff08520005fec2a1003fe61d0c01ffb028206ff58443005bec6a080bff214c801ffb02860dff95330017fc41108d3fd545080bff2a22007ff14f101e7fc64a180bfc2050829ffa824210ff0cb40017fa64908abff535040dfe1846200ff98d41007788620827ff544800dfe1826212ff54740007fe62a000aec6250401ff3226202ff085210cffca818
  | 6 => 0xdfe3006225ff14c4100ffe40a001bfe320c43b7fb2a6200bfd8d1014ffe42a0847ff42d0401fea0e2015ff98221137fea32080aff624c873fe2888600b718d2100ffca0a0077fd504c461ffa8a6406bf98f41017fc42900f7ff5350c05fe212421bff98131007be6318807ff20c4005ffa966406ff0c031157fca6a0806fc601040dffb106201ff0c33000ffc40a006bff538c401ffb126027ff99741037b88618903fc5490c01ffb126200ffd8940035f8ca1881afe63d08017eb1e8402ff8852101cf8ca8801bfc320c4037e302423aff94743027f8648801bfd64cc43fee1946224ff98841035fcc721903ff5090c01ffb1c4235ff14342007fa8290007ff2048053fe2928200ff90e4102ffaa28810bff21d0c1ffeaa2800aff8c9300dff8c098807fc304c073ffa908600bf58343007fcc7a101bfc32cc003ff2862006ff99732007fa829080bfd524c80dfeb066202ffc8121005fac1a081ffd54c4065ff2a66419ff54431017faa510837fd51cc081ffaa48614bf59521137faa7208a7fc625040dff1866202fd0862108ff8a9a0003fd32d0005ff90a8402ff10a2100ffea1a00dfbe4010c017e3244206ff14d430bff8a018857fc1088403fe1028000bf99332007f8c2a0007fe5048023fe30e8400fed01400aff8c11081bfc324c0077e32e8200ffd9310017d86490047fc6310401ff20e8015ff9422109ffca090827fd544803dff304622aff5494100ff84188047fe5410c017eb188200ff90631005fcc99880bfe52d0823ffb168014ffd95210d7facb188027f6548021fe10e8000bf1911000ff42188003fc41cc425ffaa68014ff5512108ff8c3a182ffd514c0017fb02842dff8c341107fc819887fde328c401fea128024ff8c841017fa849084bfe65d001f7fb2a803cff18943017fe859906bff508c401ffb0a640fff595401a7fccaa1003fc644c83ffe10c6228ff04141037fac521803ef3248003fe1024022ffd473108ff8ca208affe109046dfe28e8400ff50b101a7fca6a100bfd5250801ffa0a2001ff54140197fca3990c3fd534c87bffaa2862fff84132017f8409080bfc5250853fe2128200ff90531097f8a7a0003ff410c435fe2a4623dff1514314ffe40a080bbc42508017eb166206ff593321b5facba10f7ff5050c01feb1e8400ffd0730007fcc2a0077fc544c40d7e31e2000ff50e4101dfcca9801bfe64cc803fea862011ff10f42007fa651880bfd4248001fea1a6400b7d8d2100ff8a198002fd60d0801ffa1a203aff59743007fa831080bff2088479fe10a8639ff94443037fc879881aff6590c01fe992620fffd4d4000ff8a088077ff504c423fe206821affd5231057fcc49801bff430c47bffb2a8606ffd0f300e7f8429881fff53c4059df214821dffd5131005fac818802fd624400ffaa8e2025ff5
  | 7 => 0xa086ffc104c42bff0844201fe10140035f8c6a102ffc544c00dbf3286203bf19543005fec09900afc62d0463fe286642bff102411a7fea2a102bfc214c02dfea9c4206ff14e4302ff8a688073fc424c401ff20a6002bf18b40007fc631083ffe5350005ff2124000ff4c621007fa8710807fe50d0001fe9926011ff18f42005fec4a0826ff6548001df21c8200ff5804100ffea09810bfe52d0c39fe3126206ff14c31015fcc51884bfd54d0001ffb128602fb0852100ffa809001ffe53c400dfe29e6006fdcc631005f8c29001bfd65cc417ffaa26000bf58b40077f8a4a0003fd6050c01fe90a800effc8540007fa86a0803fd418c44bffa988202ff8cb42037fe87990c3ff654c801ff31e2002ff90921007fc86a109ffc51d0401fea0a623bff941431b5fecba1003fd4250439ff9026201ff4831001dfccaa18abfd655040dfe32c8601ff08340017fc84a1023ff21c4047ff1008209ff94d20037fe86218b3fe629043dfe3046229ff9894100dfcc021803fd604c41ffea928002bf989300d7faa918803fd21c4005ff90a4006ff14d3000578c898853fe5348483ff3068602ff0cb4213dfcc8208d7fc30d08017eb1e2000f7d0c31007fec89900bfd2148001ff98a201eff94231047f8a588007f81044001feb222011ff18f400d5fecb18807fc105007ffe10c8637ff140431d7f8a3a18affe3090401ff30a601bff94131007fa85a000bff214843bfe32a623dff551430d7f8cb1880bfe428840dff3166206ffcc431007fac09909fff52d040dff98e6038ff9484308ffe87a106ffe204c43bfeaa26201ff5434008ff8cba080bfe52cc805fea924202ff54920037f8879901bfc6190c05fe2924007ff54b10007fac1208dbfd51d085fff1826406bf18d20047f8858801bff6190c077e32a823abf990431dffc40a186ffc204c477fe102861eff082311f7fc41218ebff52d0c01ee31a8220ff1033115ffc812080efe65cc005fe2924202ff14a2107f7aa8a0003fc644c00dff98a6033ff841420177c84a1017f65144069fea9a842aff99541017e8429086bfd508c423ffb2e8000ff4c841007f8c988002ff6350853ff2128211ff95341077f884a0007fc1048003fe1822000ff90441007fac910806fc6050803fe0862000ff50931007fcc6a101bfc640c425ffa9e8000bf19131007fa82a007bfe208c401fea146200ff88540027fc6488003fd43508077e32e8011ff1504101dfccb1880afe6290c23ff2a68601ff88340007fac988003fe21c4001feb068203bf19520197f8a39904ffc1048423ffb2e8406ff8cb301cf7ca821803fe61d08017f30c8600ff58d4012ffea0208bffe404c83ffe3146226ff5964101df8cb88017fc654400dff21a6402ff1092012ffea820802ff6050c7bfea828624ff084410b7fca71080bff218840
  | 8 => 0xf5973200ffe80900f3fe4250c017e3226032bf5973211ff8202081bfd6590c29fe32a4222ff147310cffaa01881bfe60cc823ffb008233ff10142207faa921807fd50cc001fe3224002ff087420fffe4118847fc54d080bfaa8a2000ffd9120037fec421803fd424c00bffa9a2006ffd4f3013ffaa3a0803fd315000dff29a8601ff84140037f8c41887fff218c405ff1966400bf59121007fec8988c2fd654c8017fb246206ff19332147fc60a081ffd53c40017eb222000ff106210affc811081bff530c405ffa126401ff88110137fca320807fe10c4001fea1a801cff90931037fec8188ebfd51d0c51ff202820fff54d400077ec890802fe64484017f30e6406ff94d31007fa878808bff52cc4057f3168025ff5504100ffaa098003fd31c400dff3286206bf98e210b5fecb10803fe31c402dffa8c4201ff883301edfecaa1803fd61d0025fea96801dff54931005fcc910802fd6290c47ff3008206ff99331005fec690103bd5490c7dfe0848601bf98332007fc6290003fd608c403ff082400aff18930005fec4980c3fc654c83ffe2946200ff4c5211fff88521803fd31480077f32e2001fb88120037fcc4188f3ff2150c55ffa8a8213ff8412105ffea69800efe654c447ff2808211ff18b41007fa8690003fe634400dfe1866422ff9533104ffaa690007fe204c00dfeb066403bf19441005fac72086bfd528c40d7e3266402bf9894008ff885a009aff6590401ff21c4200ffd8540037f86021803fd4348439ff90a6211ffd8342007fac89901bfe3210c017fb24423cff98943005fcc3a10cbfd51cc80dfe990623cff14943037f8c22180afc62d0c39fe2926212ef55340017d884a1007fc10d000dfe30e6400ef19130005fcc89881bfe6590c23fe30e8001bf18141007fc86a0863de320c47fff9048611ffd0f4100ffe41a0003fe41cc061ff32a641eff0423111ff840208cffe405083bffa9a620dff1533000fb86198003fd62904077f32e6206ff0c843015fec69900afc621040d7e320620fff9954002ff8a888007dc304c0017eb108200ff5074001df8ca88003fe4144001ff10e8001ffd4110007fc8218802fd60cc801fe9922033ff8c142007fec298076fd654c45bfe2868201bf98f30117fca398807fa40d000dfe9966000ffd8d410cff8a818803ff42cc401ffb224241ff14343007f62088003fd614c80d7f31e8004ff08510027fcc488067ff500c473fea88863eff94243015f8c588003fd42104077e32a8406bf19331037fcc018863fc210c40bffaa22006efd0c43037ee629881bdc320c401ffb222001ffd43301e7f884a1823fe42c4033ffaa06201ff50310077fc84a0033fc21cc0017eb226206ffd8443157fecaa08bbfe52d040dff3206200ff58f40037fec39807ffc428c423ffb28820dffd5330157faa6
  | 9 => 0x2e01d01c00804400001f19e00400101100110e03700000401c0000150010010010950a400001902d01400004e00100f00201800103c00206102100f00e2ef0ef00a02000200100500e00000900f00501800000000202102000100c08602f00903112000001900500103500200000700201e00600100101200205b02600000b00101100041700f00400201a0f900300209d0150120ab0350000370130040330100bb00303900100302308802d01d00000616e02f01300103701501b00332a02500008800200308a10500300001744c0320471561370e100c02b01a0060023fc00200902342300300000800800000100e19a43400002400001900000d01302000000000200a2fc03804001407703200a00103900654d00000500e0020020070340520130020110044360000df00d03d0720210100be03f02300233300603314700403306900d01c05202000903c02104300400600201c0240000370020080060010000080c201300005a11402200d02e01000400c00202009e00403c00800000c0c12a101a00e02200000004202300002b03303908100600c0370002a500001e13407002300401d00100000800700300400001e00707d03800700300400600d04616b01700700301301500b00603b00000000014300502e004017de4090807fe50cc00dfeb0e6006bf19731127fe40208dbff53d082fff2806203bf99742007dec498883fc50cc40fffa8e2001ffc8130007fa829809bfe5490401fe20a4002bf98621137fea520803f64110423ffb0e8024ffc8441015fac59902ffd544c001f6312823bff04143017fc41a1037fd54cc001ff21e2001bf980311fffc8521802ff6350001fe20a4201ff0811008ff8c5a1803fd6448001dfb226200ff58530035fcc688002fe640c401ffb146233ff98142007fa848801afe6390401ff31a4013ff98121005fec098803fd635080f7fb2e2006ff14c43047fcc588002ff6444049fe290820eff189400a7fea290802ff614c02fff100623fffc864300ff8419800efe65d00077f3288621ff94b31097fca7a0007fc204c00dff9966206ff94e43187fca299057fe308840d7e31c4206ffd9732037f8879880bec4288421ff2168006ff59330037fca7188dbfc53d0805fb90c4200ff50831177fc65a080e7e650c47bfea92861cff98931037f8cb98097fd5210403ffa028006ff580430a7faa6908c3fe544c80bfeb2a2001ff5411016ff861a080afe6244001ff21a4001fb08120217fc65a1803fd21d00037f3066200ffd8542007fac58801bfc30d0c01ff18a4206f7cc431037fcc399043ff21d00017fb1e2036ffd4342007fcc918806fc604c801ff21a4206ff1933012ffaa020807ff40c4001fe30a6411ffd8f4100df8c1a08fffc5290c5dfe1968211ff18f4108ff88420802fe6448001ff18a8006f
  | 10 => 0x3d04a00000006c03600200000900100026901803604f2f40000000000003c300433200802200001300600503900700100201607000306102700200502a00000e0060200320054cb01906f0000820be01b09300200700000b0000000140e929903820a15109200a08407d00d00000100600400000000500a07800b01f00000002301c16400100400208102700000400023a02000c0132d10520b408e00609e00402f00000600400000000202800200b03f00102a00021000000000401900400000000000201844c04400000811900001b0000d006105b04c00500400201400f4df00e0350000021f90001af01b00003a02f0001320d100000000c0071af0041a60050050272ca0d300100400800801401000900000f00901e00000000002c01204b02606e0160170270032db0180050000030000270b600208600200800000001900002315f00a02220506400302100100400800c00000000306102200f02d04710200100800301e2e001200104400000f00000e0030002170000220f500103b1cd02303000103c00000002a00530400401c00301706d00200829002f00200e00b00100000600600103f00106f00009e00000001c01000216d00255200208d0060000190bf0050000fb0010060080a400017903b01a25005a0012bd00002d01404a03f00a00400000000100b15e00d10602302d0000120030891180a706800403b00200000102300c00404800000000000000100000000004905205304500400400102300102d00b0040070390070030fc00225a0300960000023df06a00200000100002205801200700c00000801f00100705a03502a08100200c0000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd764c841144fd7699310005bd740c5402d6bc311913001cfc75d8542004ff75d89312d7bb3019130035dc734873014ebf4259221004fd7558831006de6018d2100cfe70992310f4fd70d8d1001cfe75d9131004ff7558b41034fe7319120007e76148520004fe76ccb100367e3259730046ec6258b101bebe30191300c7cc320c5200ddf57198d1008ebc6410d100e6ec52d8931005ee7618931007e46148520004fe71993300067f6598d20014fe76d8930004fe76d0931005f4715094100cfc7059031124ff7650b410fede52d8d2102e7e76d9510017e661d0a2100df87050d30004ff7558f40007d763d0541034fe73d9120004ff725874300dfa70905200067f6558d10006f72118540007af64d8931036df65d0c31006ee651893101cfc7558f420a67c654851008edf6398c41004fc7158b430067c7459730006bf50d913100cfe7058a310057f7558520006bd641913100cfe70d8e21005f7714cb41004fd7558241004fd75d8141004ff7358841006ec62d8131006de6518d21316be6190c4100cfe764c510006de53d8d4114dee76d8941004fd768854001cfe7558b430defa10d8131036fb30582431bebe1019130275ed75cc920004ff7558e41004fd74d8e21006be6450e3101cfc75590312c67d21d9520006dd6318d4019eef2058b40014fe76d0521004fe7610d41036bf745903100cfc7018542014fc7298443006df6350d40036be435933200cfc70584430067d7459431025ec7258d10006be52d9130016ef60cc920006ec62d8141166bc52d9121006bf6410d10006be531912101cfc75d9120035de73d0a31006ef3218520036df64d0c31004fd7650f10004ff7650b102be7e40d952012e7e6510730007d463d05410e6ef2058732004fc7650f10006ed54d89412f6ec53d8931006be5219131034fe73d8121036f83058043035be74d0d43006bf6499121006bf64d85301f6bc70d9130017e661cca2100dfa708c530004ff715834208edd73991300067e105943108ebc64d0510006bf745913008ef840583420f6f51098730004fe7690f100c7d72118d21005bf744c54008ebe641063108edc6358f42006bc640c521006bf64d8121006bf644c521006bf648c531014fe72d81411aeee76d0920004ff7650d10006df6410e312c67f42d9520004ff75d894108ef84058043004be7619131005ac74485202e67d4059730004fe7690d201b67c65d091000cfe7018542176ec62d05310f4fe7618d10004ff75d913208ebf4299332004ff7058a43006ee60d8941014fe7258343004fd73d912100cfe7099031004ff7598743004fe7119120014fc725804100cfc76cc5102367c10d951018def7258d20006ee43d8941006bd311913101cfe7519221006bc50d9131006de40d8d21006bf75d91210057d7518e21004ff7158f40
  | 1 => 0x9120004fd7690730034fe761073003ef865c4110006bc64905310079c439063101cfe75991210e6ec3258e2101cfe75d8d21006dc6218d41126bd2119121105f77158d1008cfc7599130014fe7259331004ff7598443006bc64589302d6be5319130006dc6310521034fe7399110315be73d06410e6ef20d8931004ff7559120006ec65d8941005dd73d053108cfe76ccb4101cfe751923130dbe7310c41004fd7648740014fc7258241004fc7158b4008ef46158743006f551d85422debf32d9130006bd5319131015ee72105200067f655091014cfd71991210fedc3258a31005bf7458930014fc7299231005bd7498d21006be72d9130006bd545923108cfc7599131005ed720c520006bd53d9121214ff735913213e7e65d0730006ef6250940006ef6290531004fd739874001cfc7558d20166bf20d9121006be401912110cff764c6210367e3159730004bf74589101c6ec6210d41006df70d8d21167b721d9121166ec6258a41014ff7158b1001cfe75d8121006df7358d10004fd76cc520036dc7018d21035df714c43100cfd760c710006bf71d9130014ff760c621006ed64d8931014fe7298643025ec724c510007ac64885212367d71d951001cfe7599131166ee62d8a41006f77159121004fc7688540005df7350521004fc7650e2101cfc7518540005bf744c740004fd729931001cfc75d8121006bf53d9131005f47150d41005ee74cc920005ef72585302be7c72d952004d7e7598520036bf7459331014fe72593300367e30594311567e655073008e7e7599110006de40d8d4101cfc75583310067f7558d10006be32d9131166be4258a41005dc735852008ebc72191310067c6599120006ed52d894130ebd6310c4108cff76d0d2001cfe7599110004fd7690f1001cfc7558443005ed7298d41004fd7518540005dc7350521035de73105300ffcc32d8e21006dd6350e41006de4018d410defa30d8131015ee728c520176ec62d054109eef2058b10004ff7558f41004fd76d0930004fc76885300067f715973002e7e71d9510004ff7258041145f57199110006f671d9310006ef52d8941034fe749874319cff705912016cfd709911000cfe70d9231006be6490f103179e6390e41014fe76d8943036dc634c510005f7714c841036de6318d10006df4398643006ed6250831006df63d0941006df7358e21004fd75593300367c31594310367d3259431016ec62cc910166bf64905210079c6410e31165bc7210e4101cfc75d8e21004fd75583312377610d951001cfc7559110006bf6450931004fd74d8930004fd760c540004ff75d8e212e67f4059730034fc71d8d1000cfc70593320367f735973001cfe7559110255ef7548520316bd7610e41006bc644c930015ee7210d2108eec6258b41006bf2019131006dc63d0941004f
  | 2 => 0x45ec725931001cfe75d923101cfc7558732005ef7258141004fd768c740015ee7290520014fe7258f10006bf6499221005be740c54010ef621d85320067d7059431006ef6210531004ff7058b410079c4310631006bf64105212e67c70597302f6ef30d8931004fd7558841004ff7159330004fe761052008cff7519130004ff7650730126be5219121004ff7688730004fd74d8b10006ef6248710034fc7358041034fc7359110004fd74d8131034fe7319121005bf7448730004fd70984430379e74d0e4308edf4358f4001cfe75d922108ebc64d0d3201cfe7599310004fd71991302efb954d0140006bc64d81313bddf7550c43176ec3258b4108ebc4219110004ff7258f1001cfc7559132006df638c52008ebc64d0930006be7019121016ee6250a412367f70d9510004fd7690e21006bd75d91300fedf32d8d21036dc6350d422debe53d9130006bc7458d10004fe761913108cff7650d32006ed51d8941007cc628c531014fe7258e41006dc40d8d21004fc764ca41176ef2099121167ac42905201f6be70d9130006be60d91210ce7c650c52001cfc75d814101cfe759873204d7e7598d20004fe76d053008ebf42191202367d20d9510006bf70d9121004ff7650b312e67e1059730005f4714ca31015ec724c621034fd76106310067c65d8910005ed7210d21006ed53d8931036f73158643014ff7658b431f6bc30d913001cfc7558b43006bf745891000cfe7058a43005dd7399121036be4399331014fc725931000cfc765054008cfc764cb40126ee3258841004fd7599332167ac4250a41036f6719844301cfe75d894101cfc75d9110004fe7690d21004fd751913200dfa76d0140006ef7258f10006de52d8d4115cfe7610510006ef7259121004fd71d813200ff361c4110006ef62d0b102367e20d9510004bc74589100375d65d0c311e6ec6250d411f5be7619130006f77159120006f5611854008ebf6510c41004f7765044107d7e7598d40005bd740c740004fd75d912000cfa76c4110006dc63d0521005dc7150c430def8605813108cfe74d8e21004ff755823100dfa701053008ebc7119130006bc42d91101f6bf6498d40006dd64d0c31004fd75d8930004fd75d8530025ec7250510004fd72986430067f70594312377771d9510026ec32d8910006bd64d0b1015cff70d911001cfe7558d20006f751d8530004fd7558910004fc7650d20006be62d913108eef4258843005bf7448530006dc63505212e67d7059730006dc62d8d41125f671d9221004fd70d853208ef76198743004fd76ccb40036de6318e41036dc7218d213179c6310e41004fd73d81210c6de4218d21006ef65d894100cfe74987402f7e731d8931036f73158443006df74d8d41034fe761043100cfe76d8121004fc715933001cfc75591211adef725
  | 3 => 0xf42d8d21176bd4299221006cc63d8941006df7358910005ed7088521166bc4258a41316bc31d91310e6ee73d893108cfe7418532004fe7650520006df7650c43006be5219130226ed7218520004ff7358b41006dc73589100b67e6588730016ee61d0a2108edd7319231034fc764873000cfc70588431dcfd7690f40006bc52d9130167ac42d8a41166bc72d912108ebc64d053101cfe7558841146fa40d81410067e7459431006ef425822108e7d7519221014fe72d813110eef2158b31004fe7610d21006bf644c53000cfd72d8d20034fe73d8540006be30d913108cff76d0831007af6290541004fe76d0f10006df75d8d41006ee50d894100cfc7058f42034ff72d9132004ff7458b31004fd7398742005dc7348510004fd74d8d201bebe70191301dcfd7399130004fc769053004d7c755852008eec4258b43006bf64589312be7d30d952009efa10d8121127ac4210520006dc72d8d41014fc7458f42015ec7250621014fc72d8d2007d7e750c540004ff7258443034fe73d8b102acff7650b40036dc6350d21004fe764c940006de5399130005ef7250710006bc6448530006ef62d8131004ff7259131006de648c53108df77450441034fd769063100efa76d01401e6ec6250d31006ee54d8941006bc64505310067c7558d200067f65d8d10004fd72d8530006bf6450521004fd7558342006f461105202debc53d9130006dc70d8d41006bc72d913131edf65d0e3117efa30d813200cff768c7100379f64d0d430367d32597300067d65d0831006ed72d8e21144fd7690740035df7650c43014fc72d8543006ef43d894108cfc76d0f10006ef6318941034fd72d9132006ec6318941034fe73d814101cfc7559332006bf73d9121006be42191310367c3159730034fc7650d41004fd70d8542006f76110520005ef7258f10004fd71191320feec6258a31144fd7650510126ec4218542006de7618d212be7c30d9520004fd7518543005df7348530014fe7650d32036dc6310d210057d750c5210067e4059431005f571d0d3100df87050540034dc735891001cfc755834308ef441587402c67f32d95200367e30597300067c6558d20004fd7559310037d66110e3108fac425084130ebc3219131006be10d913101cfe7519121004ff7058843004df735891000dfa700c540035df764c4310067f72d9510014ff7690621037cc324ca310fedd72d8d2109cfd7648510006ee65d8941006fb70591202be7c40d9520006df7358f10004fd709923108ebe54191322aeed72d91201967c65cc910004fd72991312f6ef63cca21005f47150d1000cfc7099332005ef725813108cff76d0f10006dd53d8d40004fd75583320067f65d9120006bc745891014cff7259121004ff7650d2020cfe7610d40006bf51d9130006ac6418931005ec7448520
  | 4 => 0x9231007af7250441014ec7258f10006bc30191210067e74d9510005ed71cca2108cff7519310004fd7399310036de61d0e31004fd7318540006bf644c931006ec10d894110eef611893100cfe70591310067f7558910026ec42d891008ef6649044101cfe75993300067d71d9520006f76198542035de73906310c6dc4218d2101cfe75d91300067c6598d20005f671d0e31005bc7448530034fc7690e21005dd7610e3108cfc74589101f6bf20d9130247cc63cc920056ee32d89300067c7259431006ee65d8931004ff7259330014fc7258730006bf6410d21006bf64905300fedc52d8d210076f65485200f4ff70d8d10005bf7458d10004ff755913101cfc75d8532006f461d0520034fc735822108ebf4219121006f77159131006df51d8d21004fd768c54008dbc7210c41004ff7650c41006bd71d91301bebe6010e41006f7511853000cfc7058a43006bf64d8d2108ebc7519131014fc7219310004ff75d92311bebd7019130036de5399330005df73505300c6de2118d21005dd7310530006df63d812108cfe74d8131316be53d9131166bc32d91210076f65d0920006bf6490d10006dc3258f41014fd7018520004fd7599131005ef7259110164fe71192210069c639054108ebc4019121006bd7319121005dc744c431006dd630c710005f47150b31004ff7458910126be42588410067f658c510005bd76d064101cfe75d8d20006dd6390e41014fc76d0d32006f421d8530126bf3219121006dd74d8d213bddd7550c43035dc7350530014fe764c521006fb7058d2001cfc75593100957e750c7400e6ee42d893101cfe7558843006bd71d9131036fb3058043006bd64d0e3108ebe741922108efb40580410057f7558141006ee63d8941006bc64d85300057d7598d10006df63cc94101cfe75d891008ebc73191313a6ef32d813230ebd7690c41006e46148520006dd6318d42146f86058141034fe7399310006dc30d8d41196ec65cca21004ff764c941006bd641913000cff7690710006dc53d8d2100cfe701854318efa2058332007cf7348520316be43d92312b6bd42d9120005f471589300057d7598d2000dfa7090540006bf6499132006f65118542004fe71d9130004fd7610d10006df6390d40036fb705803108ebf7319130006ef62d0531036f73158730004fd7099031034ff7658e210047f7558910005f77150d31015ee718852108ebe64d0831006dc40d8d41055f97098d20004ff75d85320befa4058031006be6519131006f410d8542007d671d0e31006dc30d8d21036dc63cc941006dc4018d41036df7218d4108cfc745883101cfe75d9132005ed72d0e21006be65d9121036f731987300e6f62158732006cf63d8941006f76190540006de5218d4100cfc70d894115efa60d8241006ef6250531014fc72580310fed
  | 5 => 0x1367c65905100367f3259431006bc62d9131004ff764cb4100cfc70d8d1008df57490441034fd70d9130006f421185431fcfe7619132006ef7258b100c6dc2018d21006bd73191312367d40d95100067f65d8520166be21d912108cff7519231015ef7148520004fc7158332006ee6018941006be40d9131004ff71583322d6bf3219130034fe73d8941035de73d083101cfe75d9121004ff72592310059c7350441004fd76d0b3000dec7048520006ef62ccb100067c40594311e6ec52d8943004fe719912008cfc76d052001cfc75d8540104ff764c7102f6ec6388521006dd72d8d410e4fd764c521167ac42d922108cff7599121014fe7690d421e6ef20d8943006bf64d0931017eb60d0920006df6390521006df51d8d41014fc72d8f1000cfc7058841036dd7518d4108ebc70191300375e65d0c31006df7359121006bf51191210fedf20d8d21004ff75d852001cfe7519110004fe76cca41004fd719933230ebd6390c41004ff7158a43005ef724c51008cff76d0910006ec75d8941006ed64d0920006ec651893108eec4258b41165bc7290e410379c4350e31014fc7258e412e67e405973008edc4358f4108cfc7610530005ed728c62100cfc70d8543006ec641893100cfd7219120006ed43d8931005f9708c71010dec725073101cfc7558f40014fe7259110035de731073008ef44158743006dc7359121006de72d8d41036dd7518d21006bc6450d31006ec54d894108ebc641053125eec3218520004ff715912001cfc7598732014fe72d8540036dc6310d10006f4614c530035de74d0c31006ed65d89412367e70d9510006f761d0520004ff7558841004fd75590310c6de3218532004ff7559221004fd76ccb1000cfc705922105d7c7558530015ec7250d20006ed651893101cfc7558e210069f6418d21166be6290541006ec7259131004fd75d85422c67e72d952000cfe7099131006df5118d41006de64d8d21006dc6518d210067f654c520006bd53d913000cff76583432b6ec42d9120004fd70d8931006bf6450d2100cfc7098443015ec7250d42004fd7199120036ef3258843006bf64d0521006bd549923101c7e75d8b1008cff7599231004fd72d8f10036de6318e210e5ec725913100cfe70185200067d7259730004ff7358241014fe729903114dec72581410067c6598d1008fb67110c410ee7c654c510216ec2158b4311cfe76905100c6de325883101cfe75d9310006df634c521004fe7199132005bc744c510006bc6418d210067d65d0b300fede3298732005bf74485102f6ec43d8931006f651d853208eec4258b400067f21d9510004ff7259130007eb704852008ef4615874208cff759931008cfe7419120004fd7599231006bc6490d10316bf6490731006ed624c84108cff7650510034ff76ccb40006be545
  | 6 => 0xe725833100cfe7058f4108ef76198740006be42d9130004ff76504310ed7c7558131006bd7519121014fc764c93108eef4258841196ee65cc920014ff7650a410e6ec21587322f7e671cca2117cfd7698d20005df7350a31004bf7458d21006bf7650441166bd72d9121016ee61cca21036dc6310d2000cfc7058c4108ef44158443006df6310521004fe71d91321e6bd4259332125bc7290c4108eed729913101cfe7598643006be52d9131006de5118d21006ef6250941005df73487301acfd7099120004ff7258740006de60d8d210e6ec42d8931004fd7558b43025ec7259110004ff7158243004ff7650d2128eed72d8d20015ee72d0d20006ef3258221004ff725824111efa3058041007cf628c5311f6bf30d91300067f6559110034fe76d0531004fd73d92210067e7259431007ac64d092001cfc75d81311bebd3019130035de7390431006dd5018d213179c439043108ef7415874308ebf75191312f6ec30d8931004fd74d8121005fb704c530005ed71d0920014fd760c621006ec6018941006bc65d912120cfd70991300047f7558d10006bc644c521006f47159120006dd6318f10006bd73d913101cfe759913200cfe70d89430c7cc3218e21004fc765093100cfe7690d40317b731d9131166be72d9121006dc53d8d412be7d72d9520006bd7019131004ff7558b31386bf6590c41036f73158732005ef724c621014fe7258643004fd7099331005bf744c521004ff7558443006bc5319121034fe7399221144fd76d0710004ff7358b4001cfe75587420067f6558910006bd64d083100dfa7010d20125be725044108cfc7458730006dc5218d410367c30594310367d3059431006bf73d9131004ff75d8542006bc64d8121005bf7650441004fd73d8b10034fe7398742004fc7648540006dc52d8d41006f76150540006be7519131005df7350531036dc6390d42004fd7219231006ef725922100cfd74d8940036df7018d4134fb61050441046ee62d8b10005f77150e410c6dc2118d212be7f20d9520006dd6518d21035dc7350531006dd6318e2130ebf6410731006ec51d8941006de65d8d21226f51018520036bf74593300067f6518520034fc76505310067f6590520006dd6410e31006dd53d8d21014fc7298730004fd755912101cfe75d8d10174ff71591211feec6290d41006ed6288710005bc744c621017ce73cc9200057f755911000cfe7358b30034fe71d8d100ffd721d8d21035de73d053100cfe70d913208cff7599332004ff7058a31006bf6410530017eb6048520034fc7610d21014fd7358b30036bc439933008fba54d0140016ee62887100079c648c53122df7715891008ebc4219131007ac74485200067c6518d10004fd76d0b31004fd72d93102bf6c72d952008eec6258b401bebc301913000cfe70d9221
  | 7 => 0x9110004ff7159130006ed73d894108ebf7119121004ff7058b4308cff75991300def71058730006bd53191210367d315943117efa60d8132004fd7558031005ef7258d10005bd74d8f100fede42d8d21006bc52191300ce7c7159431004fd7558f40004ff7258e4100cfc7058a31034ff76cc74005d7c7558930006bd5019131006df6418d210067c7558910006df74d8d2101cfc7558742004fd75d9231006be51191311e6ee42d894301cfe75d8b10046ec2158b10006dc639054100cfc7058b43036f43198732006df75d8d21014fc74d8940014fe7218540004fe768c52008cff76d0a31006dd53d8d41007cc724c4310067f6518d2001cfe75591200f5f67118f10014fd7610621296dd32d8d20006bd72d9130006dd5418d2108ef66450441015ee7290d2001cfe755834308ebe64d0e31004bc7458d10006dd70d8d21005ed7290d20034fc715823108cff759911000cfc70d8943126bf2019121007ae64d0a21166bc21d912108cff76d0d211f6bd73d9130006bd65d9121015ec72cc62108dbe74cc8411c6bd421913208ebe54992310c6cf2018d21035dd76d0e4301cfc7558b41006bf6450530006df64d0e3100cfe7059332006ac64d893101cfc7558730036df7218d21004ff7558643006f671d8b10006df2018d410067f6510520004ff7558031006f55118542005ef7250520005bf7458121004ff73591210076f65cc920006bc2119131006ed75d894108cff7599131004ff75d89400079d4310d403cf9d54d0e4301cfe7558b41004ff7518520006ef51d8931004fd76d07302d6bc5319130006ed75d8931006ef5258b43004ff7558f42006bc6490521317b67190e41005be74cca41126bc42588412be7f30d9520006df7359131016ec6288540004fd7599310005f77150d41006dd75d8d41006dd6318d41036f77158732036dc63cc521004fd75d8540036dc6390d2100cfe70d8941005f97010d100067c7159730006ee20d894100cfc70d923101cfe7558f10006ef624c93008edc6358f4012e7c65105100047d75192210feec2158a31006df20d8d41034fc735912132fe43118931036dd7418d21005ed7290d4200cfc7058d21166bc20d91210fedc32d8e210067e72d9510127ac4219221006bf64d0530006f56118532004fc7158343004fd7650b100ce7f7159431126bc521912101cfc75d922101c7c7558910014fe7258341007b54110431015ee7290d42006bc201913108cff76d0d10006bc72d9130034fc7399031036f77158643004ff75589102367f40d9510006bd64906211857c7558132266f621d85200067e32d951008ebe7419121006bf51191300067c65d9120006ec72593100067f725973025ef62118520036f83058031006bd76d06410f6f81058231014fc7258d10034fe73185422debc32d9130014f
  | 8 => 0x8cfe76cc740004fd75d8d42015ec72d062108cfc759933200cfc7358b30006ee6518941006ec6018931036dc6350d4008edf4358f4208ebc6010c41006be40d913219efa60d814208ef97099130034ff76cc910034ff76cca410c6df5218d2108cfe74d8930006bd541913108fb74250441006f56118542124fe71d9221006bf6418530014fe76d0d32004fd7099332216ec62d0d411f6be6090e410067d75d8b101bebf2019130006bf6450d30005f77159120006bc70d91211b67e65d0831006ef74d893108cff759903124f6c65485200e6ee71d89310367e7359431316bc30d9131005fb704c930014fe76d8941004fe76d0d3108fb57110c411febf42d91321dcff7059130006bc649052009efa60d812100cfc70d8931005df7350441166be42d9221144fd719911001cfe7558342045ec724c710034fc76cc9100c6dd5218d21006bc40d9131004fe76509300067f65d0520004fd73d8940004fd729933000cfc764c9301f6bd10d9130006ee51d893108ebc641052108cfe74d81212367e10d9510005bc74581210367d305973030f9e5310c41004fd761073008edd7399121006ed50d8931005bc744873030ebf3119131017e76188521006ec75d8931006be6019121004fd7558b30004ff76904310067f655052000cfe70d912127f6c65d092000cfc76d051013e7c65d05102debe73d9130006df7358d20006f76198520004ff7458732006bd6519131034ff7658d20007e571d0a210057d75d82212c67c32d952020cff73591300fede72d8d210067f65991101567c6550510004fd7319121004fe7648540006bf64cc521004ff72593100067d6548730006f551d85322c67e42d95202aebd40d912000cfc764c510006bd6410621034fd71d81310feec32d8e21005df7350730036ef7258b30014fe76d8931005f77158142034fc7650831004fc768c540004fd74d8520036f6719864325eec4218520006ee64885210fedf72d8d2101cfe7558a41005dc7350441146f71058740004fd7599132006df630c52008ebf7219130006bc644c5300367c30597301e4fd7399132014fe72991100e6ec20d89310367f325973014dec7258d41006df63d0521004fe7690530174ff765084108cfc7458f10005dd731073015cff7650740006df635052114eec6258941035dc7350730004ff7158b30014fd7158b1000cfe7019110016ee624ca31006be6450b10004ff764ca412e67c4059730006de32d8d10006bd6490710014fe72d8543036df65d0e43034fc760c710004ff7158043006be51d9121004ff7059331004fd764c74008cfc7458331006be651912100cfe76d8143006ef7258d20006bd50d912101cfc75d93103179e5310e41006df735923100dee76cc92000cfc7019131004ff7650f10014fe7219110004fc764853016df7715
  | 9 => 0xf3019130026ee62d891008ebc6410530006ef75d8941016ee62d0940006bd5219131166bf52d9121006bf51d913108cff76d073000efb61c411000cfc7458740004ff7058d210067c65d8520004ff7358b10004fe7650d2016cff76507100d57c75582310069e5319130006df6398d4201cfe75993322f6ef71d8931004fd7519221014fc72d92311ee7c6550d10004ff7648530006cf6318941006f61018532006ed54d8931006bc42d9130006cc63189410067c755823100cfc7359330006ec7258d10014fe72d8d10006bf52191310067c72d9510085fb70591200067c73d9520006ec651894108cfc76d0d20005f47158943004ff7558a3108cff7599221006bd64107102367f71d95101ce7c6510d10006df6350d2119efa20d81420079d64d0e31006df431854308ebc64105200dedd3058f10006df63d0541126bc321912110cff7158d210fede628c531014fc72d81310c6f52118532006bf65d91311debd40593300fddc72d0e310067f2059431034fd7019130004ff75587403479d5410e31006df6398e41066ec32d8132006ef5258a31014fe72d9310005ef7250631005df734851008cfe74d8532004ff7650520004fd71d9132006dd76d0c3108cfe7498730006dd4118d41006f461cc520004fd72993312aebf40d91200067f6510d200067f654c910014fc7258743005de7618d410067f650c510006bf6488530006dc32d8d41014fc764c521007e671d0a21036dc63cc510006bf6498d21006ef54d8941004fc7159120045ec72507100367d7359431004fd75d8d10007b54110521104ff7158d10006de42d8d41014fc72580430a57e750c521006df63d814108cff76d0b10006f761cc520014fc7458742005dc7358540004fd72d8543035de74d0d4301cfe7558831004fd71d9120004fe71d8943006bd531913008ef67119221034fe73d912100cfe76d8142004fd731912008cfc7519110004ff7458d212367e30d951034fb6405044100cfc76d0d3000cff7658231036de638c621106f710d8530004ff7558d10004fd71991321dcfd7650d30034dc73591102f6ef31d89310ee7c654c520006df6310d21036de7518d21006dc63d8141006ed65d89312f6ee43d8931036de6318d2108f9c4350f40037d661cc631016ee624c841005bf744c5300079f6310e41004fd75d8532004ff715884300cfe701912100cfe7098743004fd7558341005f77150d10014fc7258331166ef2058a410067d72d9510004ff7259031006ef73d8931005df7358121214fd7299132006bc6490530006bd54d9121005ef7259310004fd75185301f6be4058243004fd7610520014fc72d853000cfc7648510005dc7358121004fd76905300067d6590431006bc70d9131316bf32d9131006dd71d8d41017eb60cc92030f9c4310431176ec2199121
  | 10 => 0x894100cfc70d913215cfd70d9110006f410d8532006be421913001cfe7558332034fc76cc941014fd7690621006ec6258131006dd539913000cfe70d8d102c67e21d9520014fc7259330076ec6258940006bf649912000cfe70d8931005bd74cc940014fc73d8930014fc7258643007ac725044100cfc7458f400067c651852030fb43119131006de5418d21004fd7099131014fe7218530036dc6350d41006bc52d9131006bd7219130034fc76cc540004ed7299131005dc73487101debf40593300067f7259431004fd7610431014fc72990310fedc42d8d21006de53191301f6bc20d9130005ef725054008ebc6410d2100cfc701911008cfe7418530004fd7558f10035de73d0930034fd71d893108edd76d0e43005dc7358542006ec64d893101cfc75d853000cff7219120006ed651894101c7c7558231006ed52d8931004fd7558a432acfe761912008cff7610431014fe7299131004ef7259121006bc64505210057d75991101367c6590520006bf6490d21005be74d8f10126be7219121006be7519130005bf7458532004ff7688740006ef52d893108ebc64d0521014fc72987400acff7258910034fe7319110006f47159132006df6310d41036be7499332004fd7610d21006f671d922108cfe74987320fdde72d0e31015ee73cca2108cff76d0b30014fe72d9130004fd7519310006ec50d8941006ee75d8941036ef3258b3019cfd729912000dfa7090d40034fe76d8d42005fb7048510004ef7258f100067c6519110004fd75d8910004fc7650910005ef7250e21004fd73d8142037d661d0c31036ec325884300dec70cc92008cfe7419221004ff75d8d41034ff7650e41036dc63d0d21004ff7158d20036dc7018d4108f9e54d0e43036dc6310d41036bc4399332007ac629054108ebf7019121014fc7258740004fd76d0e21036be4399330004ff7518530005ed72cc52123d7e76d9510004fd75d8543006ec65d893108cfc745833200cfc70d8d41006ee6318941034fe73d922101cfe75d8d42004ff75d8f10006df6518d21006be72191300bef51018530006dc63d0541006df6398d2001cfc7598742006bf7458d21004fd72987400367d3159730006dc73591100067d6510431014ec7259310005f47150f100e4fd7698e210367f3059431004fe765053001cfc7559330196ee65cca2108cfc7458d10006be6490431014fc76509410fddf734ca31006df70d8d412be7d10d952008cfc7599031004fd72d9110014fc72d8d41006ed71d8941006dd5118d21006bf64d8931006dd6418d2114eef21d8941004ff72583430057f75581213c6df65d0d43166bd52d9121005df7358542004fd7559332014fc7298743005dd73d073101cfe7558e210067c65d9110006df764c4310fef5219873201cfc75589100067f6550d201beb
  | 11 => 0x1cfe7558231005bc744c7102debf31d9130004fd7650a31006ee6418931004fd751923130ebf3019131215df7359132006ed51d8931004fd7299231005ef7250740126ec5258841005dc7350621014fe7299330034fc7359310214fe7610d42034ff7610f10005de744c431036ef7258843014fe7688710036fb305803108fb44050441005df7350831004fe7650d10006ed64d0a21004fd7598643317b57190e41006bf64d0d21006bf6499310004ff75d8141014fc72993312f5ec74cca21016ec624c930004fd75d91301f6bc4058243004ff7258341004fd76d0d10006ef725913208ef84058041004fc7158243005f7715894301cfe755931002d7c7558d10316bc4398743004fd75d81420367d735973008cfc7599310004fe7610e21006de30d8d42004fd7558041014fe72191312c67c42d95200fedc20d8d21006f451d8530006bf6490531014ff7658b100067f6548510006ef625814101cfe7559221004fd7099121005dc735051000cfe7099132004fd74d8931004fe76cc520004ff7558b1001cfe7559332006bc40d9132006bc6450d21006be51d91300069c6418d21004fd7690d21174fd72991210067c6518d2000cee76cc920006dc75d8d21006df6398d400067d65d043101cfc755822100cfc7099331004ff7258643036bf64d0d43034fe76d8d2126f6c65cc9200057d7599120006bd6410f1000cfe7058d21036dc7518d2100cfe768c530006bd51d912112e7c6510520004fe760c5402367e40d9510166bc42d922108ebc64d053000cff72d8d20034fc7650b3101cfe7558031004ff7458221004fd71d89400367e735973008ebe6410431014fc72d9110006bf745913109cfd72d8b10004fd7558740014fc72d8d10035dc74cc6311afea70d0920004ef7259131006dc75d8d41006bd6419310005bc7448510034fe7399121004fd751854200cfe7019131014fc7650d32006bd511913101cfe759923101cfe75580412f7e431d8931034fc7690d20014ff7658b410079f6418d210067d65504310fcfd72d8d2100cfe7398730006bc52191310067f6598520006df6350d41006f77158d102d6bc3219130006ef50d8941004ff7058f42106f850583310069f64d8d210067f65d0910006dc74d8d21006f421d8540005df735051008cfc7458b10034fc7690d21004ff7259110004fd75987400067d6590730004fd7558b410b67c65885100067e4259431006de5018d21004ff7059121006f77159132006bf745912101cfc751854319ef86058142006bc75d9131006ed62d0b31126be4219221004fd7318520006bc645053000cfc70d9131006bc75d9121006ef64d0a21127b72119121004fc7690520316bc53d913101cfc75d8930046ec32d8b10007cf724c431006bc64d8d210fede21d8d2108ebe7419132006ef651
  | 12 => 0xf7650521006ec60d8931004ff7558f103479e5410e3117ef8605813208cfc76d0930005df735814108edf4358f410feef2058a31004ff7458331006ec74d893109cff70589101bebe4058043007d4414c431004fd7558231014fc72d913108ebc4219221006dc5418d21006bf6410531006df63cc521034fd7158f10006bc6019131006f4619054016ef85058341006be5019131316bf30d91310379e7410e31004fe71d8d40034ff7690e21014fe72582310057d750c5100367d4359431006f42118530014fe7258241006bf65d9121006bd7119130004fd74d8d212c76c32d9520004fd75582210c5de72d0c31034fd74d8143005f47159120016ec6250941004f77159120006f610d8542005ef724c710006bc6418530006bf20d9131006bd70d91311bebd1019130036dc63d0d10014fc7258243005bf7458d212c67c21d952000cfe7058e21034fe7399120004fe7610530014fe725844308fac42d0d4213e7c65d0520006bd54d9130006bc6450d30004fd76cca41036dc6390d40126ef2058841034fe73d9310004ff75d9121014fd70d8520006ee54d8931004fd74d891001cfc75d81421567c6550520006de51d8d210079e64d0e3108cfe7418520015ec7250d32014fc76cc521005be7619131296df32d8d20014fc7258341006ec70d8941056ec6258930006be50d9121004fe71d8d42006dc65d8d210067c7059431006ef73d894108ebc7219121006bc6519131004fd75d8d20006dc4218d41006f41018542006bd75d9121006bf75d91300067d6510730006bd53d9131006cc638852108cfe7688740006dd75d8d21004fd72d8d4108cfc7519120005f47158142015ec724c52000cfe7059031036dd7018d4100cfd7358031006bd649043101cfc75d8d2008cfe74d8530165be7290e41004fd76885302e67f205973001cfe7598740004fd7558343006be65d9130004ff75d8d401557c7558141006ef43d89310367f30597300367c4359431006dc42d8d41006dc1018d21005f9701053000cfe7399330216ec62d0d31036bf74593321f79e30d9130004fd75992211f6bc73d91302be7c20d95201bcfe76d0d4014eee32d8941034fc7358b40004fd75d8121004fd73d8141006bc21d913001cfe7558a43126be21191210e4ff7258d21005bf7448710004fd70d9132026ec325822100cfd768c710006be54d912108cfc76d09100fedc21d8d21004fd7558732016ec6250931014fe72d8d413c6dd65d0d43006de7618d4108ebc73191301e6ec21d894300cfc7058732004fd70d9221006bd7519131004ef725844330ebe73191311f6bd50d9130006ef53d8941006fb5058331004fd72d8d10004ff7359310005bd74ccb40006dd65d8d2116ebd4099310005df735062108ebc6410d2008ebf7219131004fd76d052008ebc64d0d31
  | 13 => 0xd20036f43198443004fd75d8d4108ebc54191310067c7259730004df735912108eec425884302d7e7599110006dd54d8d21007ac6418931006bd70d912102d7e7598d10006de5118d412b6bf42d9120316bc32d913101cfc7558e41224fe71d8b10005bd74d8231006be42d9131126bc211912101cfc75d913101cfc755824100cfc72d8121004fd71d91300367c325973008ebc4219130005ed7290621004ff75d8131014fe725804304d7e75991202f7ce63cca21034fe76d8d10006bf52d91301c4fe76d0d42005fb7050510006bd6519121036fb7058332004ff7559310246ef63cc92001cfe75d854302d7c7559110006df6398d210f6f8605823108cfe7499132036be43993320067f65d8910036ef3258831166ee4258a41006af6418931006dd64d0e31006dc21d8d41006df64d8d21014fc7258443125be7290c410079d6390e41006df638c5400dedf3058f100057d750c621005f77158d20006bc10d9121006bd641043108cfc75991210067f7459730006dc2118d41006ee10d8941036bc4399031005f77150831006bd52d9130006fb5058341036dc7518d41004fd7650531014fc72191311a67e6550b3022cff71589101ce7c6510d20006dc5118d21006bc648853001cfc75582312067c6590d10004fd764c9100ffcc32d8a31004fe764c540006bd701912108cfc76d0e210067d6550730005dd73d0a31035de73d07311167c65cc51000cfc7099231006bf64d813117eef2058b30126bc2019121006bc1019131046ec42d8b10004fd70991320067f65cc520006be645073100cfe70d8532006dc20d8d410fedc628c531006be72d91310079c744c4310b57e7519221006dd50d8d21005ed72d0d2008ebf4299221004fc764c540006bd72d913132eef32185320067e425973001cfc7558341004fd7519131006f45118543034fd74d894301cfc7558f41004ff73580410067d73d9520014fc7259110006de53d8d4208cfc7599231004fd7519121225f671d8b10005fb704c51001cfe7558b10004ff7559031036f4319864301cfe75d8e21034ff7690d200067d74d9520036dd7218d21006ee601893101cfe75d8131005dd7110e3108ebf4099310004ff755822100cfe7058732034ff7610d2101cfc7558743015ee74d0a21006dd5399330006bf64991300079e53d9130005fb705094008ebf731912128edd30d8d20004ff75d8543006df6390d2122ef710d852000cfe7058c4100dfa70d0510014fe72d911001cfe7558910034fc765073003efa65c4110006ef7259310014fe76d8940006ee50d8931006dc2018d41034ff764c51001cfc7558a41006bc651912100dfa70cc510004fd76d0d211f6bc6090c41015ec725052008cfe74d8d10035df7450c430a57c7558121004fd7559331036ef3258b31005f7715894008cf
  | 14 => 0x1cfe7559130014fc72d8d4000dec70d09201966c65cc92008eee7299131006ef624c941006ef6258131005ed71cc9201bebc2019130006df6390541006ee74d8931006ef74d894101cfe7558331146fa10d8141006bc6490d21004ff7159332006de6018d41014fc7258f40006df735912000cfe7058743004ff73582210feec628c531167af20d9121006ee30d894108cff7599132006de60d8d4108edc4358c4108ebf7019131005bd7690c41006bc64cc521006de75d8d41006be65d9131004fd73d8910367b64290441386bd6590c41004ff764c841004ff7558341004fe7690d10014ec7258d102367d30d9510014fe76d891001cfe7558b31004fd7098643006ec54d8931026ec42582210057d75d8b10036dc6398c41014fc715822101cfc75d814300cfe7058b4119ded72991200c5dc72d0c312c77b20d952008ebe5419131005df7350731014fe7259131006bc51191310fedd52d8d21034fc7610d201367e65904310c6de2018d21166be4298742004fd7558742006ef42d8142004ff7650b30004fd7598742106fa1058331005df735911021f7865c41100067f6559120004fd76992310367c4359730125ac72504410aeed20d8910004ff7558742004fd7498732004fd70d91310c6dd2018d21036dc6390d41005bc7458d200067c425943100cfd7218520004ff7258d1008cfe741931000cff7658041004fd765091001cfc75d8f10014fe72d8143034dc7359121006dc60d8d41004fe7650b1008ef67119231006ef52d8943006dd6318e410fedf52d8d21166bf72d9121036fb7058243035de73d0b30004ff745873001cfc75d8520004fd76cc941166bf71d912108cfc7610520006ee75d8931005f4714c931004fc7159332036bc43993310067f65cc91000cfc7058e41014fc76d05212367c30d9510036dc63d0d2001cfc7558b1008efb4058341006bd501912108ebc4299331006be5119121014fe7218543014fe7258743035dc7350731004fd76ccb41007e77250441034fc7358740006ee73d8941006ec10d89310367c3259431036de630c62100cfc7058b3100dfa708c710006bc64581310067d71597300fedd71d8d21006dc6018d41004fd7558743056ec52d8930004fd76d08310c6dd4218d21006dc6418d21006bc54d91212367c40d9510007d7414c43108ebf751912100cfe7099331004ff7058b31034fc7610e21006bf64d0531034ff7610e2109ef86058121004ff75d81320067d65d0730034fe7319221036de7018d41014fc7219231006dd50d8d41036ef7258a43006de51d8d41005dd7390631004fd73991310067f6590d2015cfe7119110037d7618c531346dd6510e31006bf7458d10004ff7258f410c7cf2018d21015ee72d0d320c6cc2118d21004ff7690730004fd74d8532006bf64505311ee7c655
  | 15 => 0xc6490d200067d6588730014fd73d8132034fe73d894000cfc7098743004fe76cc910014fc7258f41004ff745883139ebf6590e4108fb44390441005bd7110e4100cfd72d8520006dd5218d411aefa2058342004ff7558e21006dd51d8d2108ebf4219132006bc75d9130004fd729911000dfa701071008ef9709911000cfe7059231004fd7219130004ff765093000cfe76d0d30005bd7190e4111ebd4019110004fd764cb4112e7e65104310069d5319130004ff7059031036bc4359031005f67110d21004ff755883100cfc7058a41004fc71588430067c7559120245ec7348520005bc744c520035dc7350a31014fe72d9131004fd7199330006bc65d91301f6bf10d91300379c4350d30004fd7610f10036ec3258b30006f721d8530006be70d9131175f77159121006ef70d8931006be54d9130004fd75d8d4008cff7019110006ee70d8941005f970907101bebd5019130004fd70d8d21006bd6490f10006bd721913101cfe7519130006be5119130004ff7559330034fe76887300dcff7058d10004fd73d911000cff7658341005bf744c510004ff764c9400f6dd30d8d10006bf6450d3114cfd76d0a41004fd7558c41166ec2158a41006dd64d8d210067e74d952001cfe7558730004bd74d8f10007e762d05412c76c42d952000cfe7099121006bc6498d21005ed728c5202e67d105973008cfc76d0d1016cff7159110165be74d0a41007b77450441005bf744ca4114df57199121006dd638c62100cff760c710004fd7598732006ec51d8931006bd51d9130006bc21191300057f755853001cfc759864301cfc759874308cfe74d8d2000cfe709933201cfc75d9231004fd764ca4108ebc751912108cfc7519231006dd5418d410067c2159431006bd75d9131006dd6318d10004ff735834101cfe7558b40036df7518d21006bf65d9130004fe76d0d21006bd5419121006f970d8f1008ebc7019121006de4218d41006f7618c530014fe7258c41126af2019121005f57190d41004fc764cb10006bc64509310fdec7250631014fc7299330034fe76d8d2014eee62d8941316bc6490731004ff7648540006be71191300067c65985203979d5310e41006f4615054008ebe7419131004fd72d9131006bc51d912100cfe7648510006df6390d41006ee53d8941004ff75d8943075f97099120004ff7559132005f7714ca31034fc7458743014fe721913008edd7399132034fc7358a41006dd54d8d41004fd75d8f10004fe764c9410367d43597300067c74d95200bcfe768c5100047d759912008df77650441006dd5018d4118eef20d893016ef710d854001cfc751853208fb6649044100cfc73d81310067c205943108cfc7119110004fd7218543316be73d9131004fe76d0930034ff7610d10014fe7259031004fc765093008cfe74d8132
  | 16 => 0x91301567e655043108cfc7458231014fc7218530034fe7318540014ee76d89311e7ac4250d42016ec625094008cfc7519131006dc63589411e4ff725913208ede6450c43006bd5419130005f47158940075ec724c540004fd75587302377471d9510004fd7318542034fd70185300067f65d0d20006df63d0d21004fd7498730004fd72d913037f9d5310c41034fe76d8d400c5de724c431004fd7558b3100cfe7058841005bd7190c41004fd70d8e21006df65d8d41076ec425912000cfe7098732007cf63cc9200c6ef2058831004ff7650530006bc42d9131006bd6419120006f72118543005bd7110c41006ee64d8931004fe71d8d20004fc7159132006dc30d8d42015ee720c621216df32d8d42006df5418d2100cfd72d912000cfe7098643014ff7658b40006bd6419110005f671d0d3101cfc755833209eed2058b1001cfc75d8d40005ef725052128edf30d8d20034fc760c540036f43158443005df73487102be7f70d9520006de54d8d21036be7499331005bc74585302d6be73191300fcff72d8d21004ff71591321d67c65d0d10126bd5219121034fc76cc52015ebf40d9110006ee20d893100cfc7099131075ec72505402f6ee638852101cfe7558341004ff751853208ef970193101bf9e3019130005f4714c841004fd7558d200057f7558d20005ef724c520005bf744c6212bf6c20d9520004ff7159131036dc3158443034fe73d852008edf6398f40006dc65d8d4101cfe75d8132014ee76d8941216ef2099332015ec7210e21004ff75d8d210367f31594310067f6598d10004fe7690520006bf64d8930016ec62d0a4108cfc7599221006ee40d8941004ff73583420367e435943101cfe7558f42014fc7299130014ff768c621005f47150e31004ff7558d210067c4259730004fd7558843004fd7519120126bf5219121014fc72d9130014fc72590310f6fa3058231004ef725931008ef576d06410067f654c510006bf745911008cff7159310017ae74d0a21004f47159120035dc73d0431006dc6518d411e6bf425933208ebc6410731004fd72d8143006ef641893101cfc7559131004fd7558d21166f52198742014fc7259131004fd7199131006de32d8d400ffcc328c621166bd42d9121014fc7299110144fd7159310014fe72d8d20007b76190541006ed76d0a21006df65d8d21034fe7399331004fc7650d10006be4019132005f77150f10006f77650441166bd20d91211bebc4058043006dd52d8d41014fe7219120006df5218d4108cfe74d8b1000cfd7690710006be6519130004fe7650d2115ebd40d91102d6bf31191302be7d70d9520006ef62509310067f7459431005ef7250431316be439874300df8704c530144ff705911008cff76d0b31004fe769053116efa1058341166be20d91210079f648c531006b
  | 17 => 0xcfc7019221004fd7558e41006bf645853008ebc64d0d21005bc7458910196ec65cc920006ef70d894121ff251c4110034fe76d0b3100cfe70d9131034fe7399031007cf63d8941034fe76d0730004fd7610d20006de5418d41007af64d0920004fc765053008edc6358c41005f4714cb41006bf6519121006be201913101cfe7559121085ec7250740006bd521913001cfc7558841036dc63d0d41014fe7299331004ff7558743034de73991212067c6590d2015cfe7619110126ef2019121007cc63d8941006bc20d9131006be4059231036be4399031006bc54d9130006af64d89310bcfe71d8f10004fd75991200067c215973000cfc764c53000dfa76c4110006dc70d8d21004ff7559121004fe76d0a31006dc5018d21004fd74d8f10166bc6290541006de6518d4108ef6711931008edf4358c4100cfc7650510006df6518d4108fb4429044108e7d7599120007ac64d89310fcfe760c521004fd71d8d42014fd71d8121034fd73593301357e7518e41166bd71d912101cfe75d8540006bd511912108fb6645044101cfe75d8141036dc3298732006bf64d0d300079c6418d21006bf521913008eec4258841004ff75d8b10004fd7119130014fc73593320fdde72cc631005be7498d2100cfe70588432be7c70d9520004fd75d9131166bc4298742006bd74d8f1008cfc7519221004ff75d9110126bd7219121004fd70d8941014fc72d85400379e74d0c310c6df2118d21006ec625814108cfe7419231006dd51d8d41004fd74d8d102be7f10d952008f9e6310c411167c65cc520026ef21d89100069c64d8d21005be74d823108ebe64d0b1001cfe75185321f6be50d91300fcfe7618d212367f20d9510004ff705933200cfe7058e410067f755912000df8704c930004fe76cc54014eee52d8941006ee60d89310bdf671d8f10006de5358343036f43158643006bd6419121004ff7458a31006dc6018d211f79c30d9130034fc76ccb10006bd73d9121005ee744852008ebe7419130004fe71d8143146fa60d8141014fd7019120006ef7258d10006dd5118d41005ed7210621014fc7258c410067f65905100067f6518d1008cfc7458031004ff76487301f6bc10d91302e67c205973000cfe735933000cfc709864308eed7299132006df634c5100079f64d8d21034fc7319130034fe76d08310079e5319130004f77158d20036dc638c521006df635894100cfe7018532006df6398d1008ebc7219130004fd7648730005bf745891001c7e7599120004fd76d053014eee7618941004be74d8f10004fd741853008ef4419874013e7e65d043100cfe769054011ef510185402e67f7059730006de50d8d21015ec72cc520004fd7558b1008ebf4019110005f576d0641285ed75d0920036dc6398f42005bf744c84108cfc7648740004fc715
  | 18 => 0xf21d9121036de6318d41006bd5119130126ec215884108eec6258b43296ec32d8d20005ef7258540005dd7390431396bd6510e41004fd7598743006bf6450d32014fc72191200079c6390541006bc60d912108ebc4019132004bc7458d21004fe768c540006bc501913119efa40d8142006f970d8b1001cfc7558342036ec32588312ffd6514c431006de74d8d210367f31597300acff70d891008ef441987430c6ee4258831004ff7158f42006df6310d20005dc73589100057f7558131006dc6358121014fc7219110006dc54d8d21004fd75d8143005dd73d0831004fd7690c4100dec7648520006ef72589100067c6559120004fc7650d3100fbb64d01400365c4359431004ff76509102be7c10d9520006ef75d8931006be501912108cfc764c84108cff7519221006bf5419131006bf72d9131006ef628c53108cff7519132004fd75d8520006df630c540004fd7650d210feee62d8a31006bf211913100df87050510006bc21d9131006de50d8d41006ef54d893101cfc7518520015ec72d0520006f76198530014ee7299131006df5018d21014fc71d8910004fd7599031004fd7219110005bf7458d20004fd7558443006bd50d9131006bf648c521017e77148520005df73589101e5dd739913202d7e750c510004fd7599130004fc768c520006bd751913001cfe75193100079f6390541004ff745823108ebe741911000cfc765094008ebe5419121036fb7058043004fd75d91320067f6510510006df52d8d41006f610185420057d7598520005bc744871008ef57199131004fe76d0d41004fe7690e21036de6350e41006bc51d9130036de6318d422367f30d95101aeef20d89400c5dc724c43100cfe70d8543004ff7598742006bf745923100cfc7018532006de54d8d41006de5018d41004fc764c520006dd5319130006be6019131006dc10d8d21004fe71d814208cfe7499110004ff755923108ef74198740004df7650c43034ff76ccb10034fe76d0b30004ff735912001cfe7558f4108fb443504410079d4310e41005df7350710005bf7458931004fc7158d20007cc6388521005bc7458131036dd76cc631006bf54d91210375d654c43101cfc75d8d41036f43198730005f97090d40005dc73507101defa60d8143004fd76cc940005f97010d20036dc325883108ef57199110306de614c43118fea70cc920034ff7658f10216ee3258b430c6dc3218532014fc72d8141005dc7348540176ef2158b41036ec3258b3108edd7399131006bf649911000cfc7018543034fc7358b411befa2058043006de70d8d41006dd76d0e31006be7619121004fd7598730006bc648c531004bc7458d20036be7499330006f671d8e211bebd7319130004fc7158f40034de76d8d21004fd75d931017cff7058d200067c62d9510004fe7688540
  | 19 => 0x8542004fd7019121004ff7598643006ac6488521004ef7258d210c7cc2118d2101cfe7599120164be76191210fedd42d8d2108cfc7458b30005ef7250d42036de6318d400057f75589100057d750c710036be435903100cfc70d8e2108efb4058342006bc101912100cfe70d89100079f7350441035dc72cc63115ef8105824108e7e7599120034ff7690d10006de62d8d41006bc6519130005df73591210b57e750c621004fd70d8d4200cfc7099132006ef72591100057d7598d40006bf5019131004fd75d8131004fd7399121006be649062100cfc709922108cfe74d8f1000cfe70586430c7d42118d2101cfc75d8d2101cfe7558643036ef3258a43006bf6490520034ff76cc841004fd75d89310067f65d05100067c32d9510007b5411062108ebc64d0d30164fd72d9121004fd7019132034ff76ccb41006dc1018d41016ec624c931006be51d9131014ff701912008ebe5419130004fe764cb10036df7018d21007af6488521004ff75d8d101f6bf70d9130005ef7250530006dd6518d4108f9c4350c41005dc7359121006bd54d9131004fd7650730006f5611853008cfc75991100079c7350441007cd63cca21014fc72d81431f6be20d91300067f6550510006be76191310067f65d8d20006dc7359120004fd71d8d20004fe768853008efb40583430367e435973000cff7658342006f421185400e6ef21d8931004ef7259110004fd73d9310245ef75cc92000cfc7650d400367f435943100dee70485201f6bd20d91300067e42d9510004fd70191311e4fd7650d32006dc51d8d21006ec30d8941004ff7258f40034fc760c520006be74d8f10014fe725873001cfe7558743006bc50d912122cff7648710076ee42d894000cfc70591210ce7d7159431005f97090520004ff7158b43004ff7558b3008cfc76d0d21004fd72185400e6ec6258931014fe72991300067c6558d10006de53d8d40036de7218d210ffcf20d8d21004fe76d0520005f47150831005dc7348740005bc744c5400f6df30d8d100067c73d951008ef57199121006ef62cc941006ec73d8941006f76198532014fe72d8d40004fd73191102f5ee73d0a21316bc73d913101cfe75191311dddd7399130004ff7058841036f4315873000cfc7458b4000cfe7058443006bd65d9131004fd7558a3101cfe7599031004fd74d813208ef8605834101cfe75d8d40006df6398d41006ec40d8941004fd751853200cfc7158b10006bc65d91310fede3258a311bebc6010e4101cfc7558d21126bd7119121004ff73591310057d7518f10006de6218d41034ff7219132034fc735903101cfc7558043004ff764cb40006bf6450930014fc7358732125bc7250441004bf7458d1008cfc7599132005f57110d21006be62d9130004ff7258c41316bf31d9131037d7714c431166b
  | 20 => 0x34fc735824100dee76d092008cff751912100cfe70592210067f74d9510005dd71d0e31006bd52d9131316bc43d9231006dd630c621006de1018d210c6ec3218532035dd76d0c31005f9700c71008ebe6410621006bf6410520004ff768c740006bc62d91300c7cc320c62101cfe75191200079d53d9130004fd70d923108eed7299120006f451d854300cfc70d8532006ec50d8931166be32d9121006dc5418d41006ec53d8941014fe7259231036f8305833225eef21185201f6bc6090e41006bf53d9121005ed72d0d32006be40992311def850d8143004fd76d0931006bd5419132165be72d0641006bf52d913108dbc744c740006dc5118d411d67c65d0d20035dc7350831004fe7650931015ee728c621014fe7258f4138fb651d0641006bf5319131006f610d85320aef8605822108ef761987420067f6510d10004ff755834301cfc75d8931005bf7448740006bc64d8930005fb7050d4008f9d6310c41036dc638c520036dc7418d21004fd7098743005f67190e412bf7820d9520004ff7650a31036de5358043004fd7690d1000cff7688710034fd7219132004fd75d89413af9e4250c430e6dd3258e21036f67198730004fe7610f102c67d42d95200067f74d95201a67c6550910004fd7610530006be321913100cfc70586430c5ec7250431006bc405923108cfc7458d20004fd75d8d2108ebc5419121006ef51d8941164fe7610521247e970cc9200fede20d8d21085ec724c740006ef64d893108edf6398f41216bd4299332004fe76d0e21014fe72d8530006be76191301bebf6410d40004fd7650b30006bd64192312f7e571cca21015ee73cc920006dc32d8d10004ff7558a410057f7558540005de74cc631005ef724c5400fedd20d8d2108cfc7458d21006dd70d8d41005ef7250d20014fc72991310fdf67118e21014fc7259331036f83058331007e47250441006bf7459221034ff7658f40014fe71d8910036fb30583320feee3258a31167b421d91210047f7559110167ae4258a41005bf744854000cfc7019231016ec624c941006dd65d8d41004fe7119130004fd7298443004fd76d0d20006dc54d8d41004fd72d9231006bf6519130036df64d0d43006bf50d9121006dd53d8d42006dc64d8d21005f77158d42007b6439044115efa20582410acfd70d891018eee76cc920004ff75d9221014fe7258041004fd71d893008ef7419874300df87050d401bebf6418d40006bf745913201cfe75d912000cfe76cc510006ef6288530007d571d0e311bebe5019130006bf6458121174ff7650621004fd75586430aefa60d8221004fe76cc940004ff7458f10006de70d8d21004ff75582411bebf101913001cfe7599331006f451185301f6bf73d9130006f77158d21126be421854215ef510987400047f7558d2000cfc70d
  | 21 => 0xf72591310067e71d95200067c105943101cfe7559331005bc744ca41004ff7059131245ec74cc920004fd760c740006ef4218542005df7350520005bc7458132126ac21191210367f4359730034ff764c521004fd7650d20006df7359130164fe7619121004fd7559120006bd51d913101cfe75d81430057f7558d1008ebc5419130034fe73d911000cfc70d92210067e75d8b10004fe7610d101e4fd7690f421a57c7558142006bf75d9131004fd70d894300cfe7058b4308cfc7519121014fc7399332034fe731931001cfc75d854301cfe7558443036dc630c521006ef6288540005dc7350520126bd4219121035de731063100cfc70191210067f6519110015ec724c521006bd641922108ef8405834101cfc7558643004fd76d0f10006bf648c530166ec42d9221004ff7358a4108cfe7499131004fc7158b30006f721d8540006df6310d1001cfe75d8930006bf54d91300067e7159730006f77158d20006bd64d07312be7e20d952000cfd7610710004ff7158343005f77150a41014fe729923100cfc70191320067f6519120005bc7458532004ff7558b40034fc760c621015ee7210621005f47158d2000cfe7650510004fc764c940056ec21d8930006df71d8d4100fba74d0140006ef71d894114eec52d8941004ff7458d10004fe7650f1001cfe7559132006bd6450731006dd6318d2100cff7658221005ef724c74008ef9709912000cfc70d9121006ef50d8931125be72d0441006dd73d92310067c7459431006de5358e41006be425933101cfe75d852000cfe76d8141036f431587320067f73d952000cfc7058b41005ed7299131014ec7258443006f56118520007e462d0541004fe760c52008ef4415874214ebd42592211bef85058043317b431d9131016ec62d0931004fe7610531126f521185421bf9c3019130034fe7319130004fe76d0910006dc6350941167ac21d9121006ef5258841034ff7158f10005df7359120036be7499031036dd7218d410067f7559110004fd739911009efa20d8121004ff755884331edd65d0e310b57e75d82210067f65d9110034fe73d8142045fb7058520316bd6310e41004fd759933001cfe75d8d41006bf6499231006be6219131004ff7058c41004ff7158b402367d10d9510014fe7359332036dd7610e310067f6550d10005f571d0e31005f47158d4221ff151c4110075ec725854000efb64d0140006bc51191210fecc628c531006de65d8d4100df87050940004be749913101cfc7598443006fb50d8143004ff7558732004fd76cc841006dc51d8d41006f77158910004ff7058e41014ec72591100067c7558d10127af201912120ebd40993302be7d20d952011cfd701911010eec4258b310c5f671d8e21005f77158132006dc10d8d41005df7358142004fe71993320079f744c431
  | 22 => 0x9131124fd7219121004fd764cb10006be6219130006bc644c9312be7f72d9520006bf6458d2100cfe7058831014fe7258740004fd72185301f4be7619130216ec2199332004ff7598740014fe7258d10014fe739933208ebf711913108efb4058043004ff7558d200fedf638c521006bc6458931004fc7158043036dc6310e41006be75d91210e6ee32d8931004fd71d8d40357b55450441036f73198732005bf744c710017af64d0942006de20d8d41006df63509411feef2058a43126bc4218542004bf7650441006ed624ca31004fd7319310004ff75d9130006be301913100cfe7059121015ee74d094201cfc7558b4008cff751912000cfc7650d30006be54d9131004fd7558043015ee7290621006df54d8d2100cfc7059231004ff7458b1008edf6398f42006ef725913100dfa74d014008cfc76d0b103179e7310e41006f721d8543005ef7250531004fc7158f4208cff75993311fcff7650f421f6bc50d9130036de638c71002d7c7558910006bd6450b10004ff764c910014fe73987321f7b830d913001cfe759874201cfc75d913200df8704c510006bd54d9132004ff75d8143004ff735874238fb554d0641014fe72d8f10006bc7458d20036de6390e41004fe7610d20035dc7358a31004ff7558332036bc435933110df77158d21004ff72580432e67e7059730005f9708c530006bc51191300fdde7210e31034fc7690d1000cfc7399330005cc7348520006fb7058d1008ef44198742014fc7458342006de75d8d21006bc7458d21035de74d0e31014fc7259231007b64350441004fd755913119cfd7699120014fe76cc521004ff755933204d7c7559120004ff755913008eef4258b43004ff7650e21005bd74cca41006ed63d8941006f7619854032fe73118931006ed72d922108ebf40993300067c42d9510014fc72d931014eec4259221037d431d0d31004ff751854008cff7519110004ff751854200cec7648520006bf21d9130006be10d912114cfd76d0621014fd70d9120006ef6290541004ef7258d1008ebf7219121004ff7558342126be201912114eef20d8941006bf64d0d31006ed70d89312377410d951000cfc70d8d42164fe76d0941126bd201912101cfc75d8d10004ff70592312e67f1059730007b54110731014fc7219130167ac4290621004ff7258243006f65118532005ed720c621004ff73591100067c65d8d1008cff7650d300047d75d8b1001cfe75d85420e6ee62d893108cfc751931020efa3058343004bf7458d20006fb505804301cfe7598443006be1019131016ec62d0941014fc725834300cff765824101cfc7558740357b65150441337d651cc631006de3258f41004ff75d8930036dc638c540005f77150e31006ec7259110006bc64585300067e7459730004ff70592210067f6588510005e
  | 23 => 0xdcfd7698f10007cf631894101cfe755873208ebc751913011df671d9310006df5418d4108ebf7019130034fd72d8132005df73485400e5f57198d21006ef624c93101cfe75d8142006ef6248510006ef64d0920004fe71d8930036dc43986430c6dd2118d210057f7558132036fb70583310067c21d95100057d750c52020ddf7359130004ff75d812100dfa71c41100067e70594310fcde7618d21014ff76485100057f7559120006ee30d893108ef74198443005ed7290520004ff76509312e67c1059730005bd74cc84108ef7419874200cfc7058743014fe72d92312c67f21d9520006de4018d2101cfe759922100dee70d092014cfd7650521005f7715094108eec625884100cfc7099031005dd73d093008ebf71191300067c65d8d20316bf71d9131055ec72585301b67e65d0b302f6ec31d8931005de73991210057d7518e41034fc7610f1001cfe755923104e7e76d95200079c64d8d21005bc7458d21006ef62d0910004f47159132006f671d92311bebe20191301bebe6010c4130ebe531913108eef4258b401f6bf50d9130005ef7250441004fd7219310006dc50d8d21006bf640c521026ec6258910004ff72587302367c20d951009fe87048520006be30d9121007cc631894101cfc75d8940006ef7258d21014fd768c62101cfe7518542036dc6398f4000ff271c41100c6df4218d21006f4618c530005ef7250730034fc7458343015ec7250521006be64907100057f7558142076ec21d8940006ee10d893100cfe7098443127ac421062108f9c4250c4308ebe7419231004fd764cb4008e7e7519221035f6718c53108ebc40992310f6fa60d8231014fe72591301f6fa405824308cff76d0e21006ed6250a41034fe73d8910004f7715913201cfe75582211e6df3258f4201cfe75d9110036f67198732004fd7650e2101cfe75d8530165bc72d064108dbc744c841004ff7058443006f970d9310004ff70588310057d7519221004fc7650d21166bd32d9121005ee74cca21004fd7558f4208f9e7310c41004fe71991301f6bd40d91300067d6550831004fe71191320a67e6548730006f77159110036f771584432ffd5514c431004fd7299130004fd7558d10246ed63cc9201dedf3058f40006dc60d8d210c6ec2158831014fe725824300cfc70987321bebc1019130034fc7359221005dc73581410067f658c520036de7418d21004ff7559110004fd731922101cfc75d9121006ed53d89410067f73d95100067d73d9510005bc7458d10006bf6410d20034fc7359120005f67190d410d67c658c510004fd75d8e212a6bd4219120006bc645093008cff751913100cfc7058831006bd7119131036de7518d41004fe71d813208cfc7599330006bc60d913139ebd6590e4130ebc4318543006be50d913101cfe7558d2130ebc311
  | 24 => 0xd76cc621006bc6019121004fd74d853000cfc7058e21004fe71d91200067c6558910034fc7650b30006bf64581310047d7599110006df7359132006be4019131055ec724c530166bf42d912100efa76c4110034ff7658f42034ff760c7401feee4258a4300cfe70d8d42005dc73591101e6ee62d8943004fd75d8b1008cff7599330004ff74580310079d531913001cfc7558831005f57190e41014fe735833215ef8605824108ebc7019131016ee62d0b31006bd6410631004fd7418532004df735912000cfe709922114ef62158742006bc648c521036dc43590310ffd421d8d210067f6590d10005f970887100069c648c53108ebc64d0931004ff7058732006df54d8d4108fb654d0641014fc7298643004fe76d0d10006df6398e21006bc42593310c6de5218d2108ebe6410710006bc54d913108cff7610730004fe7650910034fc7610431036f73198643006ef62d054101cfe7558243005f9700c520005ed72d0521006de2018d4109ef850d81210dcfd76cc71001cfe7558e41004fd76d04312f6ee53d8931004ff7458d20006df6358121005be74cc94001cfe7558f400067f7558d2001cfc755913008dbc72d04411f6bf6490d40004ff7558c4100cfe70192311befa1058043004fd7558243006bd5458243006be64508312be7d40d9520036bc4359330255ed7548520005ee76189410067f65cc510014fc7218540006f751d8543015ee72cc521396bf6510e41006f421d854301cfc75185421e5ec725854300cfc705874200cee76d092014eec32d8941036ef7258831006bc71d9130036df7418d4114eee42d8941004ff7359221006df50d8d21006ef62d8141034ff735933000cfc70987420375e654c431006bc10d9131004ff7458e210fede32d8e2101cfc755884311cfe71d9310006bf5419121006be32d9130004ff7598730006f4610c520014fe7219310015ee74d0920007af6418931005df7350631034fc7358841006bf53d9130036de7018d2101c7e76d9510006be71d9130004fc7158342034fc7610d1001cfe75590311defa30d8143016ec628853008ef44198443004ff765083108cfc7458e21004fd729873001cfc75582431f6bf40d9130006ef725844308eef4258b41014fe7299310004fd75d8943006bd6490631126ec2119121006df6350d42036fb3058331014ec7259131007cf6388521006f7610c520014fd74d8142006ef53d89312be7e70d952001cfe75d89402367c71d9510005bd749853008edc6358f41036de7218d4101cfe7558d10004fd7599331004fd73d91200fedf21d8d21014fe7259310004ff75580431bebd2019130006ec6488521005f97090540036ef7258b31006ef52d893008ebc43192310067e2059431004ff75d9131004fd76d0a31006f7211853001cfc7559221035dc7350631
  | 25 => 0x8732035de7310431006df50d8d4101cfc75d8943004ff7058743346df6510e311f6be6498f40046ef21d8b10004fd70185320e6ee7618931006bc648c5300379f7450c43006df21d8d41005f97010710005bf745813200cfc70d8d2130fb73119131004fd75d89402e67d2059730004fe764c520014fe7650521017ae74d0942004fd76cc54008fb65450441034fe73987400fedf71d8d211f6be10d9130006df53d8d21004df73591312c67e32d9520036bc4359332036df7518d410077b65c4110014fe7298743006bc6450d32005bc7448540316bd6390e41004fd76887400367c735943108cfe768c740004fd76cc9101c6ef215884300cfd71d8910124be749912133f9e4010e310067c74d9510014fc76505210067e72597300ffcc21d8d21004ff755824301cfe7558043016ef6188521036f77158730006ee40d893101cfe75d8931006ec43d8941006be54d9132006bc5019121006bc51d913103d7e750c71008dbe74ccb4000dfa700c71007d7c7558940086ec42d81421e6ec62589431f4fe7619130165bf7450a41036dd7018d210ffce3258a310067c65191200ffcc328c520005dc735814200cfe70d8d41006be70d9121034fc7358b10034fd70d8930005df735054001c7c7559120006dc5018d41005df7358940004fd760c52008cfc759933118cff7258d2036ebe649044100cfe76d813114eef2058742016ec6248710006f55118532036dc630c520006be75d9130166ac6290541017ce73cca21036dd7118d210067d6550b30035de718c53101cfc7558a31006ef62d0931006bf6498530014ff7610621004ff72593310e5ec7258131004fe76d0d2001cfe751852000dfa70d0d30006df63cc510036dc3199331004fd7558b40004fc764c941004fd7098732006fb70589100fedc72d8d21005dc735054004d7c7558d200067c6559110016ec62d0b10006dc50d8d41006ef725912008ebe74193102bf6e20d95200e6df3258e21004ff7650441034fe769073000dfa7010d10006bd65d913000cfe7019221165be7619121006bf64d0d32014fe7258031004fd76d0b10034dc73590310bef81058031034fc7358342005ef7258d4108cfc764cb41015ee72d0521006fb50d8121004fd7019231005bc744c521004fd75d912101cfc7558a43006ef651893101cfe75d8532357b55150441005df7348740007ad64d0a21126bf2119121006be40d9121337d551cc63108edc4358f401e6ee32d894335ebe615044100cfe70191320067f655852008ef860583430befa2058031016ec62cc941004fd7418520015ec7250e21004fe76d0b1001cfc7558c4108cfc76d093101cfc75d9130006be53d9121006bc6219131004f47158d200defa60d8131285ef75d0920004ff75d8142006bc6219130004fd75d9221036ec3258a430e4f
  | 26 => 0x34ff7610d202debc31d9130006bf5319121004fd72d8141005f970cc510004ff7558a43004ff75d853001cfc75d8941006ef421852000dfa70907100067c6599110005ef724c521006f671d8f100367c7359730006bf5419130004fc764c91003d7e7518f1015df67119310004fe76485302367d70d9510006f7614c530004fd70d85432dfbb30d9130004fd72d8d4001c7e7519221014fc7650d42004fd709874201cfe7559330006bf70d9131004fd73992210057f7558231006de10d8d2108ebe6410f10004fc7650a31006df53d8d4108ef84058343005ef72585431bebc5019130015ee720c52000cfc7058f4129cfe76d09401f6be30d9130004fd7559221006bf644c93017efa20d81322cd7e76d95201def860581430c4fe71d8e21006de32d8d41036df7418d21005df7350740036be4359331006bd6450831017ae74d0920006be6490631006ef62cc910005ef7250510006bf7458d2001cfe7558b30006ec7258f10006be4299331016ee62508310067f7558231036f7618c5310e6ee52d893108ebe64d07310079f6410e310b57e7518e21127b4211912108cfe74d8d21004fd70d9121015ee72d0e212f6ed63cca21006df63d8941006be20d9131005be74985300e5ee76d8931004fd759844308dbf7150441006be7519121146bd4059310006bc6458121005dd71d0c31006ec7258443014fd70d8d20014ff70d9120006dc4018d210067f2159431004ff75185431f6bd70d91300067e73d9510006be545824300cfc705913125ef52118520004ff75d8540004ff725833100cfc705913201cfc755933101cfc755804100cfe7058b31005bf744c520006df6358141165be7210e4101c7c7558d1000cfe76d81321defa40d8143224fe7688510375bd7490441036df618c531006bf2119130034fd72d8532004dd7399121004ff735891001cfe755824100cff761071000cfc701852000cfe7059132034ff7690d21004fd7019221006dd6318d20036f83058243004ff7559331006df6398f10125bf74508413b79d5450c430067d74d9510004ff7558331006be73d9121004fd75591320aef81058221006df5018d41006ed70d8941006bf5019121004fd71d8143165f67119221006dc6358141004fd75d9110245ee7348520266f521d8520316be6110c41034fc73593310c5cc724c431176f621d854200cfe7059331005f67110e2108cfe74d852001cfe7599130006be7319121004ff7598732055ec725053001cfc7558f10014fe74987420065d65d0c31015ec7210d20065fb7058d20166be52d9121006df2118d4100dfa70887100367e3159431005ed71d0a21005f77158930006df63d0d2001cfe75191322e67e205973001cfe7558c412be7f40d9520006ed43d894100cfe7058f42004ff7558b43005dc735912008cfc745
  | 27 => 0xc7059331006bf7459120005bf7458530006fb50d8131005dd76cc63101cfe7558a31005fb7050540014fc72582310067f71d9520014fe7298443004ff7358740016ec62d0910005bf7458520036de6318d20005dd73d0b30014fc73583322bf6f72d952008ebf7519130006ef7258e21316bc6390541004ff705913208cfe760c740004fd739912016cfe7610540006bf6458930016ef604852030ebc3019131005df7358941006df5118d2137ebd6510c410c4fe768c521014fc7258f1014cfd7699221006bf745931001cfc75d891001cfc751853030ebf3219131006dd5358343006f4101853200cff72d9120036dc7218d41004fd7299031004ff764c520006bf649913101cfc7558b31004fd7018542005dc7358941004fd75991100067e73d9520127ac211912108cfc764c740004ff75d8d42034ff7690f1008e7d759911001cfc75d8b10006ed6318941016ee62ccb410fedd32d8d2138fb551d064108ebc4019131036de630c710146bf405931003d7e75d8b1001cfc759874000cfc735873011ef81058041146f850d8141004ff7458b30006df630c52120edf30d8d40004fd7519130034fc735891008dbe7390c41006dc63d894114eec215874208ebf7319131006bd6450e3100cfc7099121216ec5258b43004fd75185201bebf5019130006fb7059130045ec7258f1008cfe74d8931004fd7559130004ff764c7401acff7259120164ff72d9121034fe7359031034fc7458b43004ff7058e21006de30d8d210057f7558940005ed7210520125be7210c41005f970d0d3014dee7298d4134fb41050441005bd7610e41166ec62905310067f6599120005f4715913201cfe751854314eee74d89412be7e10d9520004fd71d894308ef74158742004ff7558041004fd75991210d67c658c5200057d750c54000dee70cc920036dc735903128cfe7618d201f6be6490f40015ee7290e21006ed62ccb41006dd5358e41006ec6148520014ff7658841006df7358d212377810d9510006df72d8d4115cfe71193100047f75591200067e62d9510006be60d9131026ef2158221006bf6490d2000cfe7058a41006bd641913208dbc7448740017e67188521004ff7058742005f47150a41034fd7218532004fd7519110006f7511854330ebe4319231004fd7650d1030ebe431854301cfe7518530005f77159132004fe71d8940006df6390d420def850d8131006bd5458043006ec63d8941016ef60d0920004fd729874308ef7415844308ef8605834208ef860580411f4ff7650f401bfb83019130005dc73507400dcfd764c510035dc7210e31126be32191210e5ec7250531005f7714c931004fd70d8d4101cfc7558b301bcbe7499130034fc7158a31014fe7298740036dc630c540004ff764cb10005bc7458930035dc7348530006dc648c531
  | 28 => 0x43101cfc7559231006bf72d91300e5ee72991311febd42d9132036df7118d410067c75591100379e6450c43005f47158132004fd7558a41004fd7610e211367e659073008cff765053101cfc7558d10005f47150e411a67e655083108cfc751913203e7865c411008cfc76d053000df87048510004fd73d8520014fc725913008ef46158740007d47350441006df63d0d10004fd7219131014fc7299310004fd7650b3100cfc70d8910006fb705911000cfe70d8542326dd65d0c3100cfd73d8930005bc7458520006bf644853015efa405824108cfe76ccb40004fd7690d2008cfc7599120006be75d91310f4fe760c510004df73591100067f2159730004fd7559231004fd73d854201cfe755913100cfe7098742004fd76d09100c6dc5218d21006be3219130034fc7358742034ff70d913014eee71d8941126ec6210531006dc32d8d40037d6614c43108cfe74d8910004fd7690520004fc7650b1008ede7399121004fd73d8540025f9709852001c7c7558d20036f73198443006bf6418d21005f77150b3108cff7219121006bf54d91312f6ed76cca21004fd75d81320aefa2058221004fd7099221005f970d051000cfd76887102367c70d9510036be43593301bebd4019130014fe7258f4001cfe7598743006dc63d8121006be101912108eed7219221014ff7658a41004fd72d8540004fd7688730004fd76cc7400367f735943117ded7298d200057d750c740006bf6519131006bf64d0930216ef2058b43006de1018d41056ec3258d20014ff764ca31006bf531913001c7e76d95200367e3259431005bc7458931006ec40d893133f9c4010e31004fd72d8131034fc7358341006fb50d8141004ff7648740124fe769052114eec20d8941004ff7458332006bc73d9121005bc744c53000cfe70d8d21006de10d8d413cedd65d0e43007cc7348520006ed71d8931016ec62ccb102367f10d9510006f651d8542006de53d8d212c67d32d9520004fd7119120005f9700c540006dd5358043036df7118d2101c7e7599110004ff725803108ebf401913008ebc73191210067d725943108cfc7458b31004fd7559110166bf32d9121004fc7650520006ed6418931006be7019131004ff75d9120006be72191310067f65d0d10005ef7250621036dc6398f410067d745973030dbe73d0441004ff7058a41016ec62485100067f650c520014ff70d8d2008cfe74991211867c654c91009eec764852001cfc75d813208cff75991201f6be6090c4107d7c755854029ebd4019120004ff7558730166ec6290541004fc7158a43006bc40d912101cfc7558031005dd7310631006bc30d912108fac4258841005f47150d31005ed7290e2108ebf4019120034fe73d85422be7e30d95200047f75582312c76f21d952001c7c75591100ce7c650c51000cf
  | 29 => 0x1c00400a06783c80ea00401200009e400100700a0edc00000a801401a0000f380548d2000001809403e00c04a803000c000007000010a00002d800088e00201f08dc00600100200100001db00100b000a04200001901980cd000001000200d0028008008025001000002a04300c01200000030001c3171c5a302f0bc415e9fb000800000c005012007400000001700a000200a58c00440d8220000002400004b000000805e05c000000411603108b81440080090000d7c02a058001001057a01e007010001a01b03b00000060010040000000097025800c0a8001000001017e0060000004002000020800802a03d000078c00c01d14eec6250531005ef7250d32006dc639052131ede61d0c31004ff75d93100fdde7618d21006f5611854308dbe740c7400feec5258a31014ff7658a3108cfc7458221004fd7650831036de6318f10004df764c431006be5458043004fe76cc941005fb7050d30076ee62d8940006df73591100aeef20d891008ef7415874008edc4358f42005dc7358940036dc634c521005bf7458131014fd7458b400c6df2018d21006f47158d20004ff705864301cfe75d8f10006bc64505100067c71d9520006f76198543006bc53d9121004fe764c91030ebc5319131006be4219110006bf511913101cfe7558740006ec70d8931007af7448520005ef7250731005ef724c53008cfe749913000cfe705874201cfe759873008ebe74191200059c744c431004ff764c540006ec60d8941034dc735912008eed7299121034fd70d8530006de30d8d41034fe731852008cfe76cc841006ef65d8931126bd321912101cfc7559120006de6418d21005df7358520014fc7218543056ee62d8930007b54250441006bf64d05100067f6558d20014fe7298730006bc6498530004ff75d891000dfa700c52004d7e750c520016ef64d094208cfe7499120065ec7250730006bd6519130125ec7250441034fc7690f10004fd7558e21004fd73d894101cfe751854001cfc75d8d42006ee70d893111cfe76d0540004ff7258231245ee73d0920006bf21d91311feec2158a43006dd638c7100067e7159431006df634c941006be3019121004ff75d8d20036dd7118d41006bf6450510005df7350431006bf51d912108f9e5450c4300cfe76d0510005f57110e21004fd70185430067c6558520006ed74d8931005df7358540006bc64d8931006ef63d8941004fd768c520007e970d0920007d7735044101cfc7598730034fc76cc940004ff7058f41004fd769043101cfe75d8943036dc634c94108cfc7458a31006ed50d8941006ee51d894100cfe7650d30006bc6458d21006be42d9110004fd71d814208cfc7519130004fe7650e21014fe7219231004fd7558f41005dd7310431034ff70191300057f755893030dbc7350441035dc735
  | 30 => 0x806400b82400661270138008000009000801000402b8db801000a232009002c01a0010058510006006013801c006030005000002200000c80000560c1009001834e05f0078004056000000002400005d004801006200000780101e40060008624024005000000002408f00b008002e00d00a810000200a43100880180c2093800403c02901e001c0120010160000338026159848400002b00a8000004014002004467e004000808c05404a00b8028090002000000c000001000812001002f005013000201100280000c000f00680680be00100b8041b9001c11100080d80000380078062000056019402642d001831004800000c001c002024009854001c003010807c00003d003814c008003000012c00400400480100120011b00858018007000007803402111f801801c00500580e0d2000001180c000002c003805000018b02581282ac048014800c01402401b81000002d2007030000202100d815829403110b80800080070008078004003003012802262400a80407c8000002807031201700014ec00200000480004ea003002000c0180020080024006026013006008200d032063809e04b047001801000900300c4028000003000c016010000009c11400000000700fc000004000001e052064001c03805403180f4030006001800406c000008001400400000080d570604400200b800000e00000685f000101200cc04a02500c00140360000030034006000000008c0c407d0450074008002003000800e000001801c0d000000980201540000348058078003000011805207900b000001a00b01680280000007e100f800a013008808c000000003005005c0c6000017400200b01185a401a009006800000601261c004800000501905000200040010004002006005009809a00c075050442a00d003801806c00b00181240bc10a03a82100580dd00180916624da028804c05600c000310802401000d82e800a0060fa009c0040240028000010001000005411a3b7001000c01e04d01680980000e909e0fb4068033014807c01a00102800000060a4000800c00200d01d0014040009002800001a00509a807401400e0038000086000000800411008b007000001a0100240030008009450041c000000009000002000000283b800405400700080000010008004004005002008c00000402780f0082020018002c000006001802c034327000804800e00000181540220b10108020000004031803c002bf800b80001f804040b004003c00015b801802600e0040000004b2a00104c40000005c900c8000125006804c000000004000000600c007001400c0005e0003c8ea03a02a821c1c200700c800000a029037001c00200403980300ec0000308000092000004808001206b005000c12601802b007000201800d80c400c003000000800002800
  | 31 => 0x4801e40080070008038022147001809000011b009800800a007005015c004027011852c01803e003800007a00000180000020cd00000004ba01700f0be0004001001000009200000b000c0081810020768002144005001865e01c0140040192050000846008e00200300001a8013014002808e008000009800002a00301a003c0636350088022000003810c12e01e00286ec01002c01903641c8044008000003a00300080a802407200c89900004b2008004002e008018800c00400602f809001200101f0074000011005000004e05d00001c806600b000804008600d007005403a018030028402a00006300d400e0ad000002005200400d003400400100f001c002018000002040600200788e005201505e003c032000014001403a1213df803803800000400ac001083010058c0000000fb001c0780a101380b003802b00381d400800e0000024314019070002534e05505e000002ca0300000100f000e03eafb04680000010108038000003000418402400102b80020530b500f00060080000c3800a00200b80d0008000001002004601400180a000000a27c80d0040002000038400e0c6039828859802e0218048fb4002005804c03e000057800c02e0ed00600040180190000008000007000802c1a0000036000400c007831800000209300014b0004015000012001208102c002001200c0010118050004000000000000100e011c006009001004000001c000002800000609b00a801201d025804c1a6aca000000c006014000002401a01501a001c73e0000000174074000012803000c019000000c06000c000024c00601103680042ac00401f0310a5c00300080ec000031000001000000c6e4815c00803a020000c0000070010000062001114000402207e00984ec000004000000024801c00a82c00b4011000005400000000001a400200000f0028024001041804819200d016000403001a00000b40060041a08244014000001002802ae1a028800403000000c0128044000000003c01a5f6000007c02a0321b900147dc00000981ac00e00111600040081cd00000e0002007003806000402f001800418600000080c400c004002000c01009200b002804016100001a00d2000003804005602a00881340cc00200f806c36a022032028404e00363b822001c00600180600042160558000002d87014003402e00104b80d00340130000140004001001800005800120680c4000017008000c03a00e01081f802c023012801c0560000100014034004013000c068017039809081c0900008034000001106802000004600300000140180128028018000004809801800004c000000002a018819400e032001000c012001003012800006600700480020170099d5400000100281cc00003900388d404434000b803c02400000e809c1f40e9009800c0
  | 32 => 0x17006c07c00701980100040200748b600c4026000801c00000300d8044146323009802404400103f000000002a001008c00094805a8034000000009001402e000037801c0160010000094000000006000400200000c002800000100082b800a06d09600080100010060024000093013843c0c0001005804000408c000000800c06a00a8068014000008801c0e2002019806805202c009800c06406730781a400000400a00e00d003005980340aa02a000011804a00c006801402000402c0680000054000006055000a012807c02c05f004003800813800200380b812f13381c4020005003800002200f000005805000200000380040060270094018009019800c0f8007024b87000c02900003a800200500081480e800003d80744d000e0040e940183b70019d50000001000000c00000700180180000da00080740020030000004076019003000001600400001d400a10200f801c00e00700a000810409f4f4007c03e03b000805401c2730030000006005006001000a196089809804c0172bb00180100170009cbc0001a3001001000000f000000001601102c008c02a01b00d00dc0c800003080380080b300200300681bf0be801c0000dd01f81f400003a007815c0000260010020002029000005c0f10c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9c8458c63484010fd0e3aac4880023b60b759873008e4e324e73224200c5f65dcd644800155f04b28c898803a3d90628c53100476c3cc83126200c3f751d1624400153b063aec8988032b1d0625813100c7c402eb3088600af080547614c801968e9b8ac488002aba0850d913100477c3aa7b128200ae4825846150c0159b05306c6a08022fe1d6519130004cec3ec821c6200aad82140644c401d1ec831c429081a2fa1f6450d210047dc02eab1a4218cce7218f4148423958c8b94c8988032dd907158930006c7ba0e498862008dd87d506350401878cbba24288002a760f54d913130d4f418a43226200a9e84dc363484018d8cbb92628800339dc871591200043f43ecab224000c3c751d163480051dd05baec9188063e20175185200063bba8e2b1a4000c5f65dcd214402317d0fba2c4880023ee0175591320063c32ae021a2000aad84997624c47d17d0f2a2c12180237e0d765073001476412eab2220378bc875516010d1b53d09320c690802aee0151d91300071ba8ca3b226224cac7219141484011db05baec6a080e37e1d53d8d420046ec3ec821c62018ec865ca434800b0fb0fb2862880462fa1f53191300065b28eeca088200acd8399762504651d90ea9ec498802b360a4018d2100c7d406ebb246200aad829c0644c43f59904b1c63880022fa1c6458d210061fb28e898a405eace83143624c511d8843288c6908723b21b725813100477c12e9b02620387c855db43440019aeec39a8220802aba0a60d913101476412ec21a2000cd551dd9310c4010fd0e32ac4880032b19372505312de4e39ec890a603ea9d831d7644c0f58eee232ac688002ad60450191210051f420e0b28620387e86dd5624400153b06286c89096aa7a0e751913000556c106032242028ec825d564cc001d18c9b1c4290802b9a0450d89410346e41aeab222000c9f74dcd644843159904b1863880031dd97715912000536c1480b286200aad82040644c40117f0eb28c89880237e1d6418d2100566c14a831a4200acd83d49628c40193ee9b1a629080237e1d6318d2101c5fc3aa9b2262008f787584614c00156f02a98c8988023b61e651893101c3e42aeca1a2000ab88054764484c517d0f3228398802a7a105018d214975210c203224200ace82dc7635040155f04b28c898002a7e116518d210045f438c8b02423ecb870d91434c001958e5b22829800237a1f54d8d410346f41ceca162000e4f65d8f32480b38dae432ec6900022fe1175591300062fbaee6b222007978855c231c400159b04386c6908063ba1b72505200046fc3aca31a8200cac74dc963440019c8e5b8ac8880031e1d77058d100055dc02a2322425e8ef825d843484070fd0bb82c7a08032bd93724c5210054fc1aca32242a0ab78458461508018beebb9ac890003175d753d8d21
  | 1 => 0x100baac898a629760e715943101c3f42eec992201face82dd76348423179083b242a00030fdd46458121006e2398e4a088200c5d65dcd21cc0019a8c638a84a0802ada04501913100556c14cbb226262d1c435d463904011f700baac48800237e1d6318d4000667b9ee4b226200c5c65dcd64440015b100a8ec6a08fa2fe11761053001476412e9b026200ccf76dc9310c401c9ea729ec4a0a031bdc86558d200047dc02ea30a8600aae84d4f62504018f0cab868288226e9209411043100536c16e7b2a20008f6819d942c40018b8ea39ac89000f1d9d651185320055dc02cbb2242018ef8759342480011f700baac6880036a1d370485200147c432e120a40008f681dd763c4001c3aa6a88c89800637a1b73505300061e3aec8b0a6000ace82903635040155904a9ec898862b3a081018d210043fc2aec992200087f855da4148001c5ea92a6c4988022fa1c50d91210046ec1cec90a8000aaf8254c644c527d4842a88c8908022fe117558d100fd67410e1b1a4200a9e83997644840d998c6b94c6a08021fa1c6558d2000733b28c290a4000a9d8499763484015e100a88c2a10029760e40594310062e328e6b2240008fb805d561d0c031dd0db92869000237e1d6318f1000556c14e03224200a9d84148635040153b09b86c6908031b19772505200064eaa6eca188600aac82597644c40155b05080c8909f7a908410191210061e3aec8b026200cb474dc563480019aee7b8ac89000e3d61e51185320062fb28e6b1220008df835d94244113d1842320c6908462f21175191310046fc1aeca1a20008ed82dd461500019c8c438ac49820ea7616531913000477438a1b126259c6d7219461480019ceec392822080327d9173991212f56741cc910a4200c3f75191614c00187cca3a24398002ae60252191300061fbaee8b1a2000c9e611d1310c40159b05baec6a08022fe1175591210047bc3ac230a8000acd83143624c4011e902bb286900023e60375d85420145e43ac8a162000acd8398062504c3b2cc23a262188063ba0a71d813200667b98c4b028218ace86d8e21484018bccbb9a8398003391887150d3100477c12eca1a4211c3f759d4644c40153908b2ec690802b6e016518d2100c76412e9b02422caae821c3644840159f04b18c6a080237e0d75591210061ebaea9b226200a9d84143634840d9b0c6b8086900472b19172105202c537416e9b2a4000c3c651d162440010fd0e32ac89000e1f215701854200574402a3b126200ab880597644c40187ecbba2c690003691d361485200062e32ee6a0a20008ef825d931d00bd95ec53a4c690803399cc61485200043fc2aec21a40008df835d943484014e902b82ca1880e1f215769052001477410e2b00862c8be861d131484014dd04382ca188031bd9772591100070faa4a831a4200
  | 2 => 0xd65d894116556412c920e20008dd87990634853dd4862320c4988032d5907150e310054ec20a031a8237aba80084644c0018d8e5b2ac88800335ddb735044130d4f41ea23226200ab581143644c40153b06280c8908032d1d37158d214656bc0ac831a420087d851d94388401938e9b9ac6900032b19372585300147a432e221a4200ae581994624c4015b100b28c6a08022fa1c64581310054e422c631a2000acf8359762504010fb0b3b285880031e1977048510006363aee4b1a20008bf845d5634850393ee6322c49800317197735912000672390c2a0a8000a74815d1650c4070ff0ebaec5880022fe1d65191210045ec24eca1e2000a9e839946448401998c439ac48800a3b2097558f1000575c02cbb128200c9f64dcd41484018d8ea312c09880327193735052100637ba8e4b1a2000aad82983644c4018d8e5b2ac6880063ea0375d85430064fba6e6b122000e6751947625040157100a88c890803a6e0153191300346e41aeca1220008bf845da214c00187ee93a2ca188032b1d37258d211f54e432a7b226061e1e53d4c644c4c353906a88c89880353d94734852008c6f43ec6a1a425ba9f8458c635000117b093b265880021f617765052001c3e42ae13088661c9c631d1314400d1b906bb08290003a318c629054100578402a3b0a8400acd8290363504235690ca0882908031e197705051000567414c031a82038f787547614c82317d093b26290003331cf725891000556412a632260028dc835db32504010fb0bbb2869000335dcc715913206d2ec1ee8b2e6000a6d821c1650c47d57100a8ec89807f331cb634c5210066b28eec9886200ae880594624c4bd998c7b926290803175d475d8d4112657388c910a4200c3f75d9160484011db053b28298002b360850d8d2100656396c8b0262008be87d91314c0011bb0e280c6908031d1d47158d2000656390c898a6062c9c73d91414c401878cbba2c6900021f6177058f4208c5e422ec21a42008ef825d5644c801968c9b8ac4980030f194744851000477c12ec99620008dd87d536348401958c9b92629080a3ba0b75987303fe36390ca31a4000c3c65dd131480018baeab18c720802bae0165d89310061e328e898a4000aac82597644c0031f100baac8990021fe1570d8d4200557420a1b126200ccc76dcd21480011dd0e086c498803399d061485200054f420a1b1a8203c767594461508c3c3886b2882188021fe1576509102d70e21880b2862028ec825d5640c40153d06280c8908033318973d05310043f438eab1a40018f5861c543c40cb998e6392c2218462fa12764853003476432e421a42008de87d53634840195ec9b92629800333dcf625053142e5bb88c8b0242118bc845d5634400159904b28c6a080387d5254d8d4100636390cab2220008ef825cf60504031f
  | 3 => 0xa3226062a9c83592410c4018beebb9ac48800e1f21570d8d410061eba8ebb2242008de87143634840d1bd0faa0c6a08470fdd6751913001476412eab2262008df835d932440051f301baec890003b1dcc61485200055b40c60322622c8bc87d9131484010ff0ab84c39900237a1c635894101476412eca1a20008bf845d9324400157100b28c89896f8710e40594310043fc2aed21a2006c5c73595420c4031f100baac9990462fa1276ccb100057340ea4b108200abb805946448423938c8b9cc890802ab60a651913108c7cc06ebb0a8000c9f641cd414400187eebb22c49800e1fa1f755823112557414e032242068de8714063504070fd0b3b26588002ab60a40191212d54f418a43226091cb77119163484015c904b08c2a00029760c105943101c3e42aed21a4000acc8258c63504018b8ebb1ac0908062f219740c5400c5674108031a420087f855da4348001878ebba2c6880029b20974594310043fc2aeca1a4000ab481597644c00193ee839ac8909629ba0871d95200053dc02e8b2e6000acd82994635040153b08280c69080339a1c61485200054ec242031a8200ccf63dc941484011df04baac888002ad211611853200746320c518a6200ae58199462504011f700baac3218030fd947458d200347cc06ebb0a60008ef825d5634800159d07300c4a0802a760f54191310054ec26e1b1a82008ef87594624c4654dd0bb166588002a7a132118d4103477c32e521c4200ae880594625047d53b07b8ec8980023ba1c62581310061fb2ee8b122000c9f64dcd60484011df04bb28788003a319063885210063732ee4a086200c7475dc5644805935f0eb2685108031e197704c5100062fb28e6a0a2000c5f651cd21440011ef0eb08c2a1802aba0a65191310062fb28e6b2220018ed82dd7634803159d05a88c6908021fa1f6558d1008c5e422ed10a600087d85dc163884011df04baac8988926b2097110c41006c63a0e498862028ee82dd160cc44955d04180c89080e3de1d51d85420061ebaea9b2260008bd849d9214c0018e8cbb8ac89000a2f21d645083101c3f42eeca12200387e85dd9434403f59d0532462988063720d7650730125574102032242008bf87590644840155d05300c8988029ba1770d894100c7c402ea30a8600e6465185214800159904a9ec6a00021f61671d8d2008e5c322e021a4000a5c835d365480018d8e5b2a8288002a7e0d641912100566c1ea9b128262c9c63dd131484018beca39ac290002b5a0450d8d210070e32aa63226006c5e74597430c40159f06b28c4988032b193725053001c3f43eeab1a4011c9c645cf414c4011ef02baac69015e9b60871d95200064e3a6c698a4200aad84d4f625040187aea3206290a6f8710d74594310066631ae5a0a4200aad82900644c80187aea3aec898002b320
  | 4 => 0x44400117d0fb22c6909629e60371d952001c3e42aed18a40008ed82dcd60d04019c8c438ac4a1a2ba3c8064d8d2100572c08a1b128200ccc761cd21480011db05baec6a016aa7a0f521913008c5f426ec90a6000ab48154c644c4b18d8e5b2a8290002b5a045018d4100477c12eab0886008df835d564480015ab03200c6a08029be09745943100672b90c218a40118be87d4c644c40159904b2ec6a0802a7e116318d210054ec264231a8206c5c7359521cc00153b07908c8988030f1d7645893000656396c8a0a2000c9f74dcd63484010fd0e3aac688002b36085018d410064e3a6e6b122018ccc621cd21440019c8e630a4290003331cf6248710006573b6c831262008f6819d943884f75cd03b92c5880033318873589410045f43ea7b226200ce472185314c0011df04bb28588003331cf62485102363d3b6cb8822000c6c75d89605042317908ba8c89800a3e219700c5200043fc2ae130c86008f7815d932440018f0cab8662880032ddd071591200064fba0e6b2220008df835c8615005955d0db1482a08223ba1c614852008c5e422e630a4000c5f651cd4148001938c839a82880022fe11731852000636baea5b126200c5d731cf65480031bd0db9a429818a2fe11764c7400054fc1aa23226200c6c7259541cc00187ae83a6ca900031b597725043100556c10e1b224200aad828c364484c553d06286c898802aba1265189310054f426a7b1a4200ad483584615080195ee8392c688002a76126518d2100575c02a3b1282008df835d5624400156902b20c8900063b60a76cc5200147743ee4b088600ce4321c56348001878ea3a2c688092aba1264885210043fc2aed98a4000aae82140644c401a98ca39a4290002b3a0e65189410062e32ee6b122000acd82040635040155904b28c898803171d473589100045ec3ea7b2260008bf8759064480051d904bb087880022fe11721853000477c12eca1a2000caf741c9644400199cec318c4a0802abe0953191300045f43ec8b126200a6d82041650c40d8b8e6b2a83980062fa1b744c54001c3e42aec21a40068dc835d061480011bf0eb18c7108022f61c501913100556c24c03128200c3c75191604c42317908ba8c89080e1fa17764c5200045f438a1b226294ea42194464484011ef02bb286908063b219728c5200043fc2aeda122000aae821c3644c40117d0e322c49880333d8d7298d412f56741ea9b1262008bd87d4c64484011f301baec9188032b9cb64991310061fb2ee890a2069ab681dd164c4001988e630a4290002ab60b71d91300043fc2aed18a8000c5c75dcd644800153b07306c8908022f61375d8f1008e5a322e3a1a6200a9c8459463484011bf0eb18c6880029721570d8d2100477c3ac63128200acd83d4962d0c231790e322629081a3720d7610d210055bc0ac
  | 5 => 0x80063b21972d0d2000557c12cbb226000ab481590644c80156b08108c2a180e2fe1d54d912130d4f41c203226200a6f825d165cc00159d07b8ec4a08063b60b75d91200062f3aec618a4200ccc72d8d31440c3938c63a2629080237e1d6318d200064e326e6b024218ccf601cd214800153b09306c69080237e1d6318e410054f420ebb1a42028ec825d9414c40153906b20c890802b360b5118d2114c76c3821b1282018dc865cc414c0014dd0bb86c4988031b997725073001c3e42aec9922000aae829c0644c401c5ecbb268490062b32095118d2100566c14a031a4200acd8214063484070f90ab84c3a1002aba0810d913100477c12ec9922000c6d75d4b6250401938c9b9a4298002a7a105218d410066a39ee2b224200d2f651d121480031d904b9ec09080e3be1d52d894100566c1cca31282118bc845d932440015b100b2ec6a08031dd947158d2001476412eab1c825aa9e83d44644c0019c8e5b0a6298002b360a30d8d41006563b6e890a4000a9e83d5064484051d9043b26290002b620165d8d2100c7c402eab2242008bf845d5644c40d998c6b96629080327ddb744c43100c7c402eab0e645ae1e53d4c644c0010fd0e3aac890002a761050d8d411bd5d404a8b008600c3f651d162440031dd0d3a242900022f61376485300055741481b226200c3d65dd121cc0011e902bb086900033318f72505210fd67410a1b1a420387c855c261cc8051d904baac2218032bddb72504410043fc2ae1b1a4200c3d75d53644840157700a88c89880395d4651d8d210054e41ac8322205ba9e831d7644c00172d03b18872080a3ba0a76505300054f418ebb224200a5c855c3635051dd1e41b20c6908030f1947458d200046f43ec6a0a42008fb805d56110c01958e8392c68800e1fa177650d2008c5f424ec21e20068dc835d843480019c8c438ac4a000317d97735051000666398c290a405aa9f8554c644c00153b06286c8988023ba1e30d89410055c402a3b22622caae828c3644845955904a9ec890802ab61050d89310054f4264031a822ccac72d91314840187ecbba2c2900032b1c864505100366a31ce221a420087f855d831480019aee638ac690002abe09711913000637baec4b028200aac84594624c40159d05306c6a08023ee0175587420045fc22eab12200387e851d943884019c8e5b8ac898802a761075d8d210066639ec4b028261c9c73191414c401878cbba26288002ab209641911008c5e422eab1a40008ee87d89604c401958e4322c0988462f2117558d211bd5c402a63226000c6f75d89604c4011dd0f206c4988031719473585200052fc2ae1b1a42018ec865ca41480051d904baac620802ab60a60191310046f438c6b028200a7581901650c40153d07aa6c890802b9e05641893100637b2ee498a20008df835d56
  | 6 => 0x1477416ebb1a4000a7b805d1650c41d1db0fb268490002ab61260d89310046ec38a1b1a4200ab980084644c0011dd0e286c4a080339d88715094101c3f42ee0b1c4200acd82043635040117f0eb20c89881a97a0c215943100477c12eab1a4200a5d83085650c4231df0cb9687108023de05765091000657ba6c4b0262008bd871406448401878cbba2c68800e2fe1d54d913200566c1ea9b126200aad828c064484231dd0fa92c420802b32096318d100061e32ee8b0a4000c6c65dc94144001958c43a2c48825e9de0570594310047bc0aeab226400c3c75191614c0018bacbb9a83980021f617765091000762398c290a4000c6c655c8414802317908bb0629000237e0d7119120006cbba0e6a088200ce7721c5634800199ee6392c898802ada0450d912100476c3c61b1282068fa87d416010c011df04baac8188032dd9371589300054ec1cea3226224cae7219331484011db0e286c498802aba12641893100673b10e299262118bc87191314c00133b0fb188720802b5a045018d2100656396c8a0a62008be87191314c0018b8ea31ac0908023ba1f62581410064f3a6c731a4200cb7741c563480010ff0ab80c2a10030fdd764585300045f438c8b0a60008ec8754f625040159d06286c4a08022fa1874485300061fb28e890a2000a9d8398064484070f90abb48688002b320953d8d410061fba8c8b026200acd83d4b624c00d4bd07ba2ca18822b9a1c6148520006563a6e4b122091ba48250441cc4014d904ba2cb9815e1f21b755852000c5e422ec98e80298ed8799221484011db0e286c4a08022fe117650d100046ec1ceca0a40008ed82dd763c40018baea3aec6908033318b735053100536c14e2b286200acd82997635040d4bd06382ca188029da04705943112557416a232242028f8865c0434800195ee9b92c690802b3a0810d8d4101477416ebb1a2000ae582043614c80d4bd07202ca188023d20575590310063abaea3b0a8600abb80597644c40d1bd073b28290002a7a1260d8d210063bbaee2b1a40008ed878c3624c40d8bce6b2c821881b171cd65504310054ec26a7b1a426199e849d1310c40d998c6b90869086273a0a744c43100747b18c520a8200c6c65dc9634400dc3ce8b2e8618802b360e651893100c76432e418a4000c3c75dd1624400117d0fb22c0988029b60a715973008e56322e5a0a4200a9d83144644c0031dd0fb124388002ab60a40d91310045fc22eca1a4200c5f65dcd644400155b09328c498802ab60850d91210045fc3ac83244200a9d83d44644c0018b8ca39a8290092e9209411062100656390c8a0a620087d851c563d08015e100a88c2990029ba0a71597300043fc2aec20a4000ce4621c5435040155f08b2ec4988b2aba0810d91210046ec3ea9b1a82118be8714064484051d904bb2839
  | 7 => 0xcf8359462504015cb04086c2a10021fe15709874225d7340ec490e201f9cc825c4438c40187aca3a243980932b188744851000567410a031a8200e2f54953625040159906b28c4a08029ee01715973001c3e42cec18a40008ef825d843440015cd02286c49887e3721f63505210056ac08a1b1a4200cac621d1624c40155d08286c4a081a97a0e205943100c6e432e7a126000c74651c54344023968c93888690802ab20953d91303e762190c218a4000c9c64dcd414c40147b08382ca18802aee01511913008c5e422ec21a20028de87d8d3250401878ca3a2c688046aba1352588410045f43ea7b224290ad58199463484011f700baac99918b6510e7190e4100667b9ee4b224200aae84983624c4334bb07ba2ca18802b5a0450d8d410064fba6c6b024200caf64dc9614c0391db0e086c4988932b1c8644c5210046fc1aeca1a4000acd82dd7634840159b05b8ec6a081a3e2197010d100046f43ec6b128262b9681190438c401958e9b124288092aba0a30191210c763388c710a4267a9f835c4644c0011db0f206c4a0803271d37358d100346f438a031a42008bd8799464484011bf0eb28c69080e1fa1f75589100352e41ae8b286200aae82997644c401a58ca3a24290002aee0151d913100575c02ca312629ca5f835d1650c401878ca3a262880032b9d8641893100556c14803226200ccc63dc96050401d4ee830a429000e1fa147158f420fe66396c6a0a42008de87d8d605040153b07a88c898802ad60450191310062ebaec731a8000c6f65dc931480071bf0ea9cc89820b87141531913000667bb0e498862008f7815d563440018e8ca38ac6900063b60a7610d20006363aee4b222000cb464dc5324c401958e5b2262980472d9537650441006563a6c490e2000a78805d1650c40159b06286c4a0803271d3634c5100346e41ae2322400087f855db32440015b700b28c6a0802b360850d8d4100746412a63226061a9e83140644c4014dd0538aca188023be097558f410062ebaec618a420387c855db324400155b04386c89880e3be1d52d893101476412eab1e8200ae88054762504018daea3aec4a080a3b20975591300054ec24c031a420387c855c3634840117f0eb20c89815e9ea0371d95200056dc02a3b1a42008bf845d9434800187eca3a2c290003351cc715912001c6fc3aa7b1a8200aaf825c4644c40199cedb18c4a08063e20175592210061fba4e8b2e6089e942119063484018becbb9a82900021f617764c52008c5e420ec98a8000ca474185214800159d05186c6a0802abe0953d91210063bba8e2b224000a9d83d50644c00155908b2ec49880297e0d74d95200061e3aec8b024289e9721190634840117b093b262901729e20171597300043e432ea18a40a0da7741c941104010fb0b3b265880023de057650d200
  | 8 => 0xc838ac498002a760f54d91210074a31a8220a4206a5c835c9650c4018b8cbb9a82900030f194745852000556c14a03224200a3f845cf654400153d0932ec69080297e1570d8d412f72729ea7b126200c5d65dcd420c4019aae738ec9189fe9ba1b65cc9200062f32ee690e60118be849d932c400159f04a9ec6a08038d59541104310055b408a03224261d1d651d1310c401c6ea328ec890862b3a0a5018d210061fbaee8b1a40018f8805d561d0c0d1b906baac890847279537650c43506d2210e2a148200c6d751d7624c4015a906b08c29000a3ba0b75185400054f41cc1b2242068dc8718d414840155b05a88c890802b360870d8d410047743821b128200cac645cb3148401b1ee839a429026697e0d725943112556412a23224200d8c73dc941104018becbb9ac4880063e201755844300476c16e8b06627dea442184414803159d04280c69080a2f21176d09310061eba0e9b2a2000ce776dc94110401b18e63928220892ab209531912101c3e42aec21a20028ec825d943c400159f04b28c6a08063ea0375d85420047dc02eab206206cd4639c643504b5938e632242980032b1d362581310063632ee498a4000c5d75d8c315000155d04080c8988462fa1375d8f100046ec1ceca1620028ee82dcd60d04015a902aa0c6a08032d190714c93100557c12c83226257a7a801cf65480018d8cab946290002b560c51185300cc3e432ea18a20038bc87551648c4070fd0dbaac29027ba9cc4641893147e4f3b6c831a4200cac64dc941484b5938e632282980031e1957010d200061e3a8e8b12200087e871d5608c401c3ea729ec890802b3a0a6518d410045ec3ea63226200a3c845cf654400159b07b8ec4a08023be0971191300064fba0e6b122000aad8214064484051dd053b262a000e1f21576cc5200043fc2ae030a6400d8c74dcd214800193eec3a2621881a97a0e42594311245f436e898a42018f8805d561d08070f90ab86c6a10032bdd3725913144f47900c831a420387c855db42440c553d063aec8988031dd9471591200046f43ec6b024200cd7631c5435040117d0fb224298002aba0b71d913000566c1cc1b128257c6e76d9742480011f700baac62080327dd073591200066639ee4b222000dc47318521480010ff0ab86c6a08031bdd7725911001476412eab1a2000aae82900644c401958e830a429000e1fa1671d8d2001c3e42ae030a64028ec825d931d00070f90abb284880031b1d47258d100045f43ec8b126000a9d83140644c40195ec9b92829800333dcf625814101477416ebb1e20008ee871896050401958ec3a24290002bae0165189410055c402a23226211c3f759d464484018e8ebb8ac6900031e5d750d814300556c24ca3128200cac72191614c0cb1dd0db92829887e73e1d63cca210054e41ac83224000a
  | 9 => 0x54d913033e4fb98c8b0a6000c7875dc16244001958e4b2283988021fe157610d102d54f418a23226000cd473dc562440014ed03202ca1886372d80734852000556c24c03126200ea47418521480015b700a88c6908669d60470594310147743ee4b26200387c855c26190c01d1f04a98c8980472719173d09300064eba6c731a4200c6c65dc9644400117d0e32242980023be097558c4101c3f42eeca0a4000c5c751cd64440051dd0fb92c7880462f2117610d2000557c12a63224200cac42dd160884018d8e4b2a821891e9ea1b65c41100346f43ee6b122000e1d53d44644c00517d0fb228498002a760e65d91210064e3a6c6b02422cda6749c74288401ccea328ec49880e1f21576d05200043f438cab2220008bd8714364484014b906ba6ca880022fa1f64581210045ec24ed9962000ace83983625042317908baac488002a72115118d410346e41aeab122018ccc621cd21c403139d0fb9a429000317dd463581410056a40ac631a8411cb4649c7434c4019cee438ac8990023b61e65189410047bc3ac230a84068dc835d5640c40157100b2ec89080e3721d5358e4100c7c402eab1a42008ef87594625040153b07a90c898002a7a0e75191210046fc1aeab2262188de86dcd4148401c9e64328c69000335dcc715912000557c12a7b226000ace8398c62504015ab02280c6a08031719773485100061f3aec818a4200c3c75191604840153d09300c6908023ee0175591100056ac1ea3b0a6000ccc7218d605040147f08b9eca9007eb3a1b628c53130d4f41e4232262489ce839d1214800d938e6b228398803711cf614852000477c12eca12200387c855d94348001998c6b8442908031759573904310045fc3ac832220008ef825d563c40051d904b9ec0a080237e0d761052008c76c16ebb1a8400ec46318b41504018d8ea392c888002bc60021185300c4e743ee49886200aad828c3644c4010ff0abb6869000327d9073581210054f420ebb1a82008ef825d5634400d1b906b90c2a0003175cc73d95100043ec2ee0b1e8200abb80594644c45955d04286c890a7e3be1d53d893100c6e41aec90e6058a79801cf65480070f90abb462a00472b1917210d210364e31ce931a42018f8805d5640c40156f02b2ec89800e1fa177058f420c5674142031a4262e1c43596410c4011bb0f328c690802b5a064018d410065a3a0e2b1a4000c5d75d4f635040153b083aec6a0a5b711cb414c4310366a31ae321a821f8df835d921cc0015b700a88c6a08023de0575591310061fbaec8b026200acd82100634840155d09a9ec498892ab20964107102e53c402e8b2e6024caf601d1214800317d0dba242a000aab20964d0b1008c5e438c890a6000a6d85dc3625040187ecbba26288002b3e095118d2141d4ec1cea3226000c5f75d8d6048401968
  | 10 => 0xb224200a9d84d4f6350401c3ea7298c8908063ba1b724c52000566c1481b1a4200ccf73dc9644400d1b9063b28298002b6e0165d8d210056ac08a031a42008de8718d60484fd8f6e032ac29022b279d86418d210346e41aeab1062618be87991438c40117f08bb243980023d205755913200556c10a1b226261a9e839d4644c42317908bb243981629e60374d95200061fb2ee898a4000caf64dc9414c40193ec9b9a4298002aee0153191304172c282a6b008637ab880544644c00193ee831ac090a0ba620153191300064fbb0e6a088200c9f641cd4148401d18c7b1482a0893a99c464885210fd6741021b1a4200c5e65dcd410c5435af06b08c2990021fe1576d0d100047cc06ebb0a8600c5f751cd644404935d0fb928220803339cb6398d4100567410a1b1a820087f855da31480031ed0db8a86880032719373505300054fc22a231a8200a5d83909650c401958c9b9262980032bdd8725044100672b90c220a40028ec825d564c40018d8e5b2a62880023be09755912108e5a20ae332664028be849db42c400153f06b2ec8908031bdd77258d100045fc22eab1a4000aad82043644c50753b07328c89800e1fa1f75591200055741461b2262008be86dd1214c00195ec9b92c0988031bd977258d1032ee2190e29946200c6c75d89604c4b7c3ca7a9ec8980023ba1f62505310045ec3ea632260028ee82dd763504011bd0e286c6a0802a7a1050d8d210066639ee4b2242008bf87590644c8031f501baec299002b9209611853000477c12eab262000c6f7518960504011f700baac39900317d977358520006363aee4b1a40068bc845db43484018deea392c8880031bdd462581311bd5d404a43226000a7485584614c0010fb0bbb286880030f1d77458d200c666390c6a0a42018ed82dd461480011790fb2242980022fe1d64193100054e41acbb22420087e87d95614800155904b28c8980b26b2097110e4101c6fc3aa7b1a8000a9d83148644c4071bf0ea9ec69080237e1d6318d420054e422c631a4057a7a80dd3654800159b07300c4988023b60b75d8d1000c7c402eab0c8600ccf63dc960504015d100b2ec49880a2fa1f645093108e4e21ae732620008be87191624c00117b0f328c89880a3ba0b75d8d400062e328e6b12201face82903634840d8bcc6ba8c720803331cc725911000476c3c81b126200ace83d53625050dd8843080c69080317dd4735891001c3f43eeab1a2061a9c83590410c4011db0f318c4a08023b60b75d92310046fc1ae830a4000aae86190624c40155904b88c8980031d19471591200054ec18ebb224200e575194763504c517f0eb26871880e1f215760c5200362e31aea18a4200ad88054763484018e8ebb8ac688002ab61353d893101476412eab1e8082e1e5054c644c023179083b2829800e2fe1d
  | 11 => 0x5040117d0fb22c2980030f5d7640c52108c5f43ea632242618be87d9131484051dd05bacc32181a3720d7690d210052fc1ae9b2a2000c3e7519031484011bb0d3a262188031759773504310062e3a8c6b028200cb774dc563480015b700a8ec6a0a3ba30876418d210046ec3cca31a823e8be861d1314c001d18c9b146298802b62015118d410147cc06ebb0a40028ec821d9414800155904b88c8988023d2057558d200346e418ec90a6000c5f651cd644800d4bd07ba2cb9801a3720d7610d100054f424ca31a4200c9c741cd624400187eca3a262880023761f5418d210054ec1ea9b226000c3f75dd162440018eaca38a841880387d5254d8d210065bba0e2b226400a6d85dc3624c4018b8ebb1ac0a08023b60b75d8d21006e439ee090a40618bf8759341cc4010fd0e3aac888002a760e101913112557410a032242018f8805d563104015d100b2ec4a0802a7a135118d410045fc22eca122006c9c7399141cc40156902b28c89821fb10855118d2100656316e8b126200ab88059464484018b8ebb9ac488002a76132018d4100657b22e53226289dc472105310c47d1790fb226298002b920564d092030e8f328e8988625ae1f8554c644c11753d0c320c6908030fdd47458d2000575c02a3b1262118be87140644c4af8dcedb2e64900032d547765044100657ba0e4b2262008ef87590624c43159d052a0c690846aea13505804300636390cab1a208ae8c2119363484f9d8842080c69080363dcc72504410047a40aeab224000c9f649ce644845d1df0cb8e8510802b3e0965d8d410056c402ca31a42028ee87dc964440018b8ca39a82880023de1d6118520006723a0c290a4000c3f75191624c001b48e830a429017b331cf625053100476c10e2b0086008bd87994644c00156d02286c8988dea7219531913000557c12cbb2262008ef825d5644c0011bf0eb18c6a0803331cc62581410063a3a8e2b224059c6d7219764480011f700baac8980021fe15709844300556c20a1b128257a6d82dcf6548001c3ecaa98c89800237e0d76487400054fc22cbb1a4200ab581143644840317908bb243a00021f61f650c5200043f43ecab1a40008ed829d931500431df0cb8e6510802b3a0a65d8d410054f41cc03224200acd82980635040155f08b28c498803271d37358d21006c63a0e690a40018ec865c8414800159d05baec6a0a56ad606651912100537416e7b2a2000c3d751d7644c4051dd0fb92c6880030fd977458d101bc5f436e898a6000c7765dc5634800117b0e286c89880237e0d7558d2100557c22ca3128200c5f751cd6448059958e5b2282908031bd97725051000573c0ac631282008ef825d843c40011df04baac7208023be097558f400047cc06ebb0a645eccc73dc96110c019c8e5b8ac68800e1fa1f75591100055dc02a3
  | 12 => 0x80237a1c63505210063a32ee2a1a2000c6f65dc9414800155904b20c89880e1fa167650b100364e39ac8a106200aac8254c644c4011df04baac998002a760c52191300061e3a8c8b126003c5c7554d60d0c018e8cbb8ac690002aba0a301913100c5e432e99928061d94315c4431040195ee9b92c68800327ddb735044100667b98e4b1a2024cac621d121c40011f700bacc22181a37a0e76485400045fc3ac83246200ad88054463484011db05bacc321802b3a0870d8d410055a422c230a4000a9c8359464484019a8c7b8a84a08029ba0a405943100656396c8b0a6000c6c75189605040159d05200c6a0802b360a4018d412de4e39ec8a0a60008bd87d4f644c40196aa9bb282208023de1d61185321645fc22ec90e800087f87d94314800153d06286c8908022f61f53d91210053741020b28629aa77815d1650c401938e831ac09081b2718d7498d2101476412e232260008f7815d5644c0c372d03b208718802b560450d8d410056a40ac631a4000a9d83d506448401998c5b9ac4a08021f617764c9102be363b6ca90a4000c3c65dd1624400159d0c318c4a0802b3a081018d4100656390c8a0a6000c6d65dc941cc001958c8b84429081a3720d75591200056dc02cbb1a82029e4825c443884051eb0d38887108b23be1d64d0a210045fc22ec18a40008fb805d564484071eb0f288c2a10031b19572d0d200145e422eda126006c5c635d6635007d17d0fa9ec898003171d773591100043ec3cebb162000a9e8414063504018beebb1ac0a08669760c70594310061fba8e8b1a2000ad78155063504015cb02286c49895e9b60b74d95200066a39ee2b224006a5e83041650c4019c88438ac8900029760e2059431124d7424e890a4018cce7118e214840153b073a8c8908021fe1576d05200046ec38a1b1a821f8de861cd4148401c3ea92a0c6a0802b3a0e65d894101c3e42aec20a40068de87d5063484011ef02baac890092aba0a10191210062fba8c6b024200c5c65dcd61480018b8ca39a42880462f21172185300062e328e6b222000acd8284063484b14dd05b9eca900030f99774487300061fb28e8b1a20008fb805d5648840d8b8c6ba862a018a2fa1c644c5210054ec1cca322420087f855d943440018eeebb8ac8900023da06764cb100043f43ecab222058c6c72d95314800195ee8312c098803331cb635814100557c12a23224200aad828c0644c40156b03180c8988023de057610d204ef0e21ce8b286200cac7299141cc40155d09300c4988023ee01755913100636baea5b128600a3c845cf65480011e902baac8980021fa1f655891000477c12eca0e6000cb7641c5434c401b18e9b926218a1335dc463581210064e320e6b024200aae84997624c40155f04a9ec8988021fa1c655852012557414a03224200a9d84d4463
  | 13 => 0x39a0000003e0c2020420000340216c0280020580080805e0000300506a968270250ee0700201103214451853004000000020000cca389100a02403002930f100280808c0081e800004dbc010020024000001707400c438080040040000000201c000010060300602105402f8180007e0000000005013c340890020040101300000003821020148008000000f553800002048678000220000180007a2ec1623d0180fc320cf1780700b0a00020241481d1060001880051c0a00000b15e0085f8010007c40e0471c62ac06023006070a70911b400c0b8000320040180f0000000c02900600c3c80901600809807b260000f8010120000a0ae018128018220180381480d00014000001000528010120180f40f9190020240280c000078e2802cc60582080401a0c80200000009c0201000c03c1482c0b60040000516a040101042b20047180010e959e500302626400005302094088fe0040602500002a26c100000300180003c1007240100a0014ec5500e000000090010160280003809a07c0d00002e0a0be82002a0500b22f00a0680380500000c018050361240480000c00ebe0000020445780200e0003d0090f60780100300002c29ac401a00c0080e0000341281b07a040259a600a07ce4872000010000020040740182103e9600d800000020028000320204000c072014190400046fc009260620000207e01403c560134900480680039e0041680102e88c0704d01e00c118010008281583a0086740701201a02800165046088068030000340082f09e2000084501a0840884c0160140001f1ac5001600116a2cc028010060000699c0000202300000a3980510b058064550000020d006800148168024a700000007081004045420275900244480100c0140993605c000000030001300980c0980080004a000406e303806021c018010700004b84c008008330000000fc05028012004040000043ac020000220b80000a00000c0302e0300540000109e000028301f65e40087b0050e8028160000600000700601c2d80c00002c1e0050180000580000e000038330060b82c19500a015028090580280200200007c0006600607804000018044018060ce7bc1080407400813800028000be8100146a16c03618e0cd7780700887c008790200000004c00600c3d9000681943700a0100180086b0012d03b85216e4f4008280060ec000970043fc3eca18a2000c7875dc16444049b56c03a2429000e1f21576d0d200064e320e6a0a4200ce7321c563480018d8cbb92869000333dcc725911000c7d436e090a200087e87195634400d1b906bb243a0062b3a0a4018d2100656326e4b026200ce472d8541500c5c3ca7a9ec898802a7a121018d410356d41ea0b0086008dd8714063504018eacbb8a8418
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x10000d1818d000111000200c0000721dd0731852148001a1443a0640594310068510c815d1650c401aa0212015119121004a924582940644840121c9460c105943100709194741852148001c84741cc6148520006a22008254c644c001c44651cc6148520006b0084805446348401a24825954110431007211d37318521480014c6939d0614852000709d947418521480014a6949cc61485204168620153544644c001c47651cc6148520004b12458294063485478a6811d362487100068610c805d1650c5458c6811cf6248710
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x6
  | 4 => 0x94b
  | 5 => 0x94e
  | 6 => 0x4
  | 7 => 0x138e
  | 8 => 0x138b
  | 9 => 0x98e
  | 10 => 0x9cb
  | 11 => 0x9ce
  | 12 => 0x168b
  | 13 => 0x168e
  | 14 => 0xa0b
  | 15 => 0xa0e
  | 16 => 0x180b
  | 17 => 0x5
  | 18 => 0x180e
  | 19 => 0xb09
  | 20 => 0xb0e
  | 21 => 0x1409
  | 22 => 0x140e
  | 23 => 0x249
  | 24 => 0x24b
  | 25 => 0x24e
  | 26 => 0x144e
  | 27 => 0xb49
  | 28 => 0xb4b
  | 29 => 0xb4e
  | 30 => 0x1449
  | 31 => 0x144b
  | 32 => 0x16c9
  | 33 => 0x16cb
  | 34 => 0x16ce
  | 35 => 0x289
  | 36 => 0x28b
  | 37 => 0x28e
  | 38 => 0x148e
  | 39 => 0x184e
  | 40 => 0xb89
  | 41 => 0xb8b
  | 42 => 0xb8e
  | 43 => 0x1489
  | 44 => 0x148b
  | 45 => 0x1849
  | 46 => 0x184b
  | 47 => 0xcc9
  | 48 => 0xcce
  | 49 => 0x1709
  | 50 => 0x170e
  | 51 => 0xd09
  | 52 => 0xd0e
  | 53 => 0x1889
  | 54 => 0x188e
  | 55 => 0x589
  | 56 => 0x58b
  | 57 => 0x58e
  | 58 => 0x18ce
  | 59 => 0xe89
  | 60 => 0xe8b
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178b
  | 64 => 0x178e
  | 65 => 0x18c9
  | 66 => 0x18cb
  | 67 => 0x138956
  | 68 => 0x209
  | 69 => 0x1549
  | 70 => 0x14c9
  | 71 => 0x2c9
  | 72 => 0x98c
  | 73 => 0xb0996
  | 74 => 0x98b16
  | 75 => 0x4b
  | 76 => 0x124b
  | 77 => 0x170996
  | 78 => 0x99716
  | 79 => 0x188996
  | 80 => 0x99896
  | 81 => 0x15c9
  | 82 => 0x12cb
  | 83 => 0x409
  | 84 => 0x10b
  | 85 => 0x1609
  | 86 => 0x130b
  | 87 => 0x1649
  | 88 => 0x134b
  | 89 => 0x449
  | 90 => 0x10c
  | 91 => 0x130c
  | 92 => 0xec9
  | 93 => 0x180a16
  | 94 => 0x140c
  | 95 => 0xb4256
  | 96 => 0xb5456
  | 97 => 0x28c
  | 98 => 0x148c
  | 99 => 0x18d456
  | 100 => 0x18c256
  | 101 => 0x20c
  | 102 => 0x16d456
  | 103 => 0x59451
  | 104 => 0x59456
  | 105 => 0xb8291
  | 106 => 0xb8296
  | 107 => 0xb9496
  | 108 => 0x148293
  | 109 => 0x149856
  | 110 => 0x28b96
  | 111 => 0x58296
  | 112 => 0x178296
  | 113 => 0x185496
  | 114 => 0x59496
  | 115 => 0x179496
  | 116 => 0x150c
  | 117 => 0xe8593
  | 118 => 0xe8596
  | 119 => 0x58e96
  | 120 => 0x18ce96
  | 121 => 0x18d796
  | 122 => 0x2d6d1
  | 123 => 0xb0211
  | 124 => 0x4253
  | 125 => 0x4293
  | 126 => 0x15393
  | 127 => 0x14b
  | 128 => 0x45711
  | 129 => 0x595d1
  | 130 => 0xec591
  | 131 => 0x58ed1
  | 132 => 0x25253
  | 133 => 0x29253
  | 134 => 0x124253
  | 135 => 0xbc253
  | 136 => 0x14c253
  | 137 => 0x28253
  | 138 => 0x29453
  | 139 => 0x25493
  | 140 => 0x25853
  | 141 => 0x24293
  | 142 => 0x148253
  | 143 => 0x149453
  | 144 => 0x24bd3
  | 145 => 0x296d3
  | 146 => 0x124293
  | 147 => 0xbc293
  | 148 => 0x14c293
  | 149 => 0x28bd3
  | 150 => 0x184253
  | 151 => 0x25256
  | 152 => 0x24b56
  | 153 => 0x255d6
  | 154 => 0x25856
  | 155 => 0x104c
  | 156 => 0x258d6
  | 157 => 0x194c
  | 158 => 0x28214
  | 159 => 0x3ce
  | 160 => 0x29493
  | 161 => 0x25453
  | 162 => 0x24053
  | 163 => 0x28053
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2112
  | 6 => 5079
  | 5 => 1824
  | 4 => 22
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/718+packedAt gbK7 (78144+(h % 718)*12) 12) % 2112)
  | 6 => 2*((h/1700+packedAt gbK6 (243792+(h % 1700)*13) 13) % 5079)
  | 5 => 2*((h/629+packedAt gbK5 (107616+(h % 629)*11) 11) % 1824)
  | 4 => 2*((h/21+packedAt gbK4 (1540+(h % 21)*5) 5) % 22)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffe07e007e01ffffe01fc0c7cfc7ee23fc7
  | 1 => 0x1f803ff80007fffffffffffc7393279903ffff
  | 2 => 0xe0003ffffff8001f807ffe0383e3c7e1fc38f8
  | 3 => 0x3fffffffffe0007ffffffc03f801ffc0ff
  | 4 => 0x3fffffffffffff800003fffc0001ffff00
  | 5 => 0xffffc0000000000000000003fffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa287ae0162a16205aa9628d404244c2ae21bc3
  | 1 => 0x9b0892580102ad2ad32acb183191259900ed5d
  | 2 => 0xc2111eaaada801131a4d6c5182e2c6e16c38e8
  | 3 => 0x8222534d634d6402071b1e2dc03f800b740b6
  | 4 => 0x104439c71bc71b9c7c0040836ffc0001dbb600
  | 5 => 0x1c7800001c001c0040018103fb5bb354000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40978
namespace PEqualNP.Outside.L_meta_40978
open PEqualNP.Outside.L_meta_40978.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 9 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 50 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 40 := block_range (n:=40) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 136 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 7 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 894 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384))) (concat (concat bs5_4_480 bs5_4_576) (concat bs5_4_672 (concat bs5_4_768 bs5_4_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 820 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := bs5_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 1 := bs5_7_0
theorem alls5 : ∀ k ≤ 7, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 22 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1824 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)))) (concat (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 (concat bgb_5_1152 bgb_5_1248))) (concat (concat bgb_5_1344 bgb_5_1440) (concat bgb_5_1536 (concat bgb_5_1632 bgb_5_1728)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 87 := block_range (n:=87) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5079 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440)) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728))) (concat (concat bgb_6_1824 (concat bgb_6_1920 bgb_6_2016)) (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 bgb_6_2400))))) (concat (concat (concat (concat bgb_6_2496 (concat bgb_6_2592 bgb_6_2688)) (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976))) (concat (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264)) (concat (concat bgb_6_3360 bgb_6_3456) (concat bgb_6_3552 bgb_6_3648)))) (concat (concat (concat bgb_6_3744 (concat bgb_6_3840 bgb_6_3936)) (concat (concat bgb_6_4032 bgb_6_4128) (concat bgb_6_4224 bgb_6_4320))) (concat (concat bgb_6_4416 (concat bgb_6_4512 bgb_6_4608)) (concat (concat bgb_6_4704 bgb_6_4800) (concat bgb_6_4896 bgb_6_4992))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 96 := block_range (n:=96) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2112 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 (concat bgb_7_1344 bgb_7_1440))) (concat (concat bgb_7_1536 (concat bgb_7_1632 bgb_7_1728)) (concat bgb_7_1824 (concat bgb_7_1920 bgb_7_2016)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 34, 38),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800feeaeaeafc88c800
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808426 * 2 ^ 32 + 4236822528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40978.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[1,2]⟩,⟨.or,[0,3]⟩,⟨.and,[1,8]⟩,⟨.or,[6,9]⟩,⟨.and,[3,9]⟩,⟨.and,[4,10]⟩,⟨.or,[5,11]⟩,⟨.or,[0,7]⟩,⟨.and,[13,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236822528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236822528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40978

open PEqualNP.Outside.L_meta_40978 in
theorem PEqualNP.Outside.L_meta_40978 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236822528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236822528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
