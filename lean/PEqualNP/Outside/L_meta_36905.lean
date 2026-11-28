import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36905.Model
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


end PEqualNP.Outside.L_meta_36905.Model

namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
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

def SBf (j : Nat) : Nat := [6, 8, 6, 5, 5, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_36905

namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x9220c351401000e05b040015be43bc43be42bc42ef32de32dc32ec32cc32be41bc41bf40bd40
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x19045001c000020021200358f000ca3ac4000a6a7294658e420cb1884196390c32c6218658f540cb18a8194794e4197294838c32907186420e30cb408e29a812c525031864a04d14540
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x20c80a1987540ca0f650ca418319432503043214540
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (224+((h/4+packedAt s0K4 (208+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s0K3 (457+((h/5+packedAt s0K3 (432+(h % 5)*5) 5) % 26)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffffffffff81fffffffffffff87ffff
  | 2 => 0x1fffffffe07fffffffe07ffffe03fffff8fe3f
  | 3 => 0xe01fe03fff80fe01ffff83e03ffc0fc07f33cc
  | 4 => 0xffe0003fffff0001fffffc003ffff0007fc3f0
  | 5 => 0xffffffc000000001ffffffffc00000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2424228a241224a0500594aa4ac514550354d5
  | 2 => 0x949451443244948a96029549422aaaa38aa2a
  | 3 => 0x5d1189a6890e906b3aaa826627688f035d334c
  | 4 => 0x919d163912481d8dccd34c1839b3c20c6ec3b0
  | 5 => 0x1e1e183e1c70e1f1f71c739f01c30c3077fc00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36905
namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x81fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107bcca20f6194417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f621041ef32083d864105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ec62887d4c510fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e882087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd529077e8520ef50a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0ef90d41de21a837f52506f8a4a0ef90941de21283f7415077c82a0dfd4141be282837e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220ed50441bf280837d50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc7be8798f710f31bf29663ee52cc6dca598df54b31f6a96636d52cc7bc6598f70cb31fb20e63f541cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c63de438c7ba8718df94a31f7294636e528c6faa518fb54a31b6a9463df328c7ba6518df94631fba0c63f4418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f710d31bfa92637c524c7bc6498f70c931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f7cc831ee990637e510c7ec8218fd50431ef98863f6310c7ba6218fd4c431ea988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790fbd0b21f621643ef32c87d86590fd90721faa0e43f631c87ea6390df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52887dc8510fb50a21f719443ed32886fca310fdd0621fa20c43f731887e86310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fbd0921f621243ef32487d86490fdd0521fa20a43f731487e86290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843f641087ea8210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0
  | 2 => 0x18010070160000000000003400800010028000020000000400000a00c0100000c00c0400100000000001006040008070100200280001000c0000600e00c0100000c00000000000038028010560000000104001c0100700601004800018000010050000040100b01000c0000000800400005020004000060000000f00201c01400005006004010060000d8028050180240000b002000020020000001780100a01006800000018048000020000180a000020000070180100000401000003001004000060060000380000000200c000000080b00e80000600004001000034018000080480680c0000040200d01801003801000014020010140240001800a0040000000c0240700301000800003000022fca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e87f651d0eeca3a1df54743faa8e877551d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390b7e87216f50e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42be29a85be4350b7886a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84216b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332efa1e65dc43ccbdc85997b50b32bf28e65f651ccaeca3995f54732faa8e657551ccafca1995f54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c65de438cbba87195f94a32f7a1465ec428cbbe65197bcca32bf28c65f6518caeca3195f54632faa8c6575518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65dc434cbde84997b10932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832e6990657e510cafaa2195f94032bea80657e53d07bca7a0d794f41bea9e83dd53d06baa7a0ef90f41de21e837e52d07dca5a0db94b41bea9683ed52d06daa5a0ef90b41de216837e50d06faa1a0df55241bf29c83de53906bca720df54e41eea9c835d539077e8720ef50e41bf29483ee52906dca520df54a41f6a94836
  | 3 => 0x6434a780500f57299962abd52d00056a5bc1b1221f244440800438000002f41342b4000005da4243728e0000b1582fd000628001720009c40000026c0000024517ca00001a050c9580010a3902dd830005f20006087752c7bd58a890000005827f1fc72d1e0003ec000003003342b916aa85a263577aa211618c300003a05ccd810c57ea2d920010a6320fea043dc9106683929887d60b0d49e4a0ea95e150ce80015006e0009a00d00069c33901000929240170ac0642d238662570c78004840016b0004e8000b20000000005c9e40009c91c8005e60000020e00092cbc0900d6624468005b8000701b418840c002e90cc000b3b2c0000000004c0006508ea6e5be000000e60a80019d96527c001190d13c00218528518600000000000000b1ad039e02d9e1a53462d8f51bc4366d8b602f0866ac2bafc2be8e9940891620000002360a1b0ef80043a99971aec23c8080000017ab0cea12e58c16ce313b2ba000378fb2e0b5c000005c81151b23440cb884b84054297164aff022868958b356c000000001288053a8004920006c9923d2358000d262e0000000058e299740e43fc5a0001d10e46b88b000000a7d730462049f9288001680015b82659494800000064208000bc0007a15f00019e2bca8a6d3bc45ce931d0003252c89900097c002120660000004139206c000006460000021e30c21d181a8000bace100029a26d4caa50000c1160004de000001064aa2ac0926b388024d4af8602145551414f2370bd30430408826907140620ec059266558661244c637d5e19e000704002b4000a1003800184b4d9593040017c52083380b150c800000cc0000000683a0138000fe8ac3295201ca6c7d02d09c220120000005ed642921a80003e0000005200000039c9394bacc0000681700050288886acb4983dd91187000631099c7146000e191f4e62fc8a9e55e4000faacf000000000791ecbec528001f02e03a800152410000001b029d971a6000278ab83a00081d6691421e000428000406e800253000000d910500090c401935fc4c41f0001d48442527a6221e91780f19c178002911588a40a92f000001351cd57a7ac38ad82f2cd047000154b38a29db0005383c0c64ec0000000037680c000000007280006a5dc0003e8002409799b93a1220010a000000000cf9810007300001f44036c1580516a0000021645c6e1938000000019e80028e000aa000280c68000002c2c2d8719d5ce3b4000000000000029331674c001595a439c9c00063e3ac0000000800089803800000004008050160b40180200200401805000000000070000000000300600c018040020100b003002008048040040000480101a0000400d00a004008060080280400100002c0080300a00400004006004030000060000f00600e000010030300080180001800000802004
  | 4 => 0x642c0981add0006b0a120500cc312e8f2294c581e29e5ee4c98996b13e4f4000003f00000025b000000002bb29e8f9891800008a17520944e5d1450e341e525081fb238394128c0000c251aa58130884002a40d0000d98fc48c510eb8954161496aa7c42e000258581fa9401501d11e3b80017c0261852b8922c40e06b83b336109841b13cebd97031e3f81f8ad112000b08000495308dc002f00c4000b00000003c4003382ee00074adb0000000019644a32d9c85d0daa3c000000380016d1665640013b8001fe6453132a628258000004a80000024100024cbb2c400093534a88546000ff8003064388012a44c000939d648e000ac00006aa0c3d8211c25b9198d3580ab0dfb1c410484f329c4c8369413102fa4dc0004f0000014aaba53a828df1bd5bc9a15c1f455cc98b48ec5e26380b11a2da0013e99c47e6b546946028378000c5030768001980006906a85c2303c18c1252966d4000ef00048c28000000c1c63a15142328050b2000000ee97e000154381ed000001928004626dc000e2000000f889c640340000f34d8a9cc29531186e40032d5527c0d08f43c66402397f4800014d224000000220730007c95026565e5c400108052be91d975216000f130f108c6c7a8001440fd8c9d90000c4019a200050c930002206bc960000000000027027e2740018447a1200028c3f2190002ad0003749aa2a5727e808260000acd990000002ecd5000000001069293b8860ca9c52aa7ccf612d0ec0009ca7b4c2b5199b350e8b84fbad932ea408d8ba03caac4316a00456d9480027899d06294446cd80008a50eabc062a63c24
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x252c425e6394b109758e52c42d56390710b958a41c43345450710ad59231c42e5628c710d514d31c42b56488710b558e21c4364524871097d8d548425c63552109bd89548426c62552109798c548425d63152109b988548426d62152108fd91538423c6454e109bd89538426c6254e108f990538423d6414e109b988538426d6214e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10b598f41842e662d0610cdd5041842b664cc610b998b3184357530c610ad99321842d663c8610d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544423e6515110cd584544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766590510cd15241442d56390510d514e41442e56290510d914a41442746550510cd15141443545350510d91494144276658c510ad5923144334548c510d514e31442e5628c510d914a3144274654c510cd1513144354534c510d914931442766588510ad59221443345488510b558e21443545388510d914a21442746548510cd15121443545348510d914921443345484110d514e104436452841109798f540425d63d50109b98b540426d62d50108f596540433461550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043546154c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597410433554d0410b598f410435553d0410b998b410436552d04109d59441043355410410d554c410436552104109d59731042b664cc410cd553310435553cc410b998b310436552cc4109d5943104335540c410d554c3104365520c4109d59721042b664c8410cd55321042d663c8410d554f210436552c84109d59421043355408410d554c21043655208410cd553100435553c4010d954b100427965840109dd9510042b46444010cd55110042d46344010d554d10042e46244010d9549100427b6544010
  | 1 => 0x827661953209d58654c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c82766194f209d58653c82cd6390b20b958642c832c5450b20ab59232c82e5618cb20d314d32c823e64947208f59251c825e63947209758e51c82ad64c8720b358f21c825f63552209718d548827761552209d185548825e63152209758c548827661152209d584548823f6454e208f19153882776154e209d185538823e6414e208f59053882766114e209d58453882ce63d0a20b9987428832f5410a20ab99332882e661cca20d3d4c328823f64546208f191518825f63546209718d51882ae6488620b398e218823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209bd89544827761551209d185544823e6515120cb588544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d20d3588534826e6590920cb15242482cd6390920d314e42482e561909209b195424832c5450920d314d424826e658c920ab592324832c548c920d314e32482e5618c9209b195324832c544c920d314d324833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c51483664214520d950851483663214520d94c8514826e65c8520ab593214832c54c8520b358f214834c53c8520d9147214832c5448520d314d21483645148520cb152204834c5388120d9146204825e63d50209758f540827661d50209d587540823d6595020cb189540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c20d3189530823e6414c208f590530825e6314c209b98853082766114c209d584530826d65d0820cb55342082ce63d0820d354f42082e661d08209b594420832d5410820d354c420826d65cc820ab993320832d54cc820d354f32082e661cc8209b594320832d540c820d354c32083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083674254420d910951083673254420d90c9510826d6588420ab992210832d5488420b398e210834d5388420d9546210832d5408420d354c21083655108420cb553200834d53c8020d9547200826f6548020ab191200832d5448020b318d200834d5348020b9185200836551480209ed95200825e63d53109758f54c426e62d53109b58b54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c426e6294f109b58a53c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59
  | 2 => 0x5310c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840c754e421032d5290840ad986421031d5310840cb54842103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d51103364254440cd109511023d6590440a798e411031d5390440ab98a411032d5290440cd546411031d5310440cb54841103355110440c754f401032d52d0040cd547401023f6550040a718d401031d5350040ab189401032d5250040ad185401033551500409ed95401026e62d53309b58b54cc27661d53309d58754cc26e62953309b58a54cc27661953309d58654cc2cd6290f30b558643cc31c5450f308f99252cc23d6494b309d98652cc2756194b30a759332cc2d561ccb308f99251cc23d64947309b98a51cc26d6294730a759331cc2cd62cc7309bd89548c26c62552309dd85548c27461552309b988548c26d62152309d984548c2756115230b398b438c2d661d0e30c7d50438c23f6454a308f191528c2776154a309d185528c29e648ca30b5986328c23f64546308f191518c26f62546309b189518c29e648c630b398a318c23e64951309b98a544c26d62951309d986544c275619513097d8d544c26f62551309b189544c27761551309d185544c23e6515130c758c544c25e6590d30c7152434c2cd6290d30b5586434c25c6550d30c7151434c32f54d4930cb153524c32f5414930cb150524c34e4314930d350c524c25e65cc930a7593324c31c54cc930d314b324c2d561cc930c7151324c34c524c930cdd53514c33454d4530d9d4b514c36452d4530cdd50514c3345414530d9d48514c3645214530d590c514c3554314530d5cc8514c355321453097997314c29d64cc530c7153314c2cd62cc530d314b314c35451cc530c7151314c34c524c530d5145314c31c548c130d314a304c354518c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c275611503097597430c31d54d0c30b398b430c2d661d0c3097594430c31d5410c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c435483097596320c29e648c830c7552320c34d528c830b5986320c31d540c830d3548320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3563254430d50c9510c25d658c430a7992310c31d548c430b398a310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030b3189300c34d524c030b5185300c355514c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63953209758e54c
  | 3 => 0xa21cd55341886d663d0621d554f41886e662d0621cd55041887555310621e950841886b664cc621cd553318875553cc621b998b3188735540c621d554c31887c5320c621ab593218872e54c8621b358f218874e53c8621ad993218873554c8621b598f218875553c86219798f544865d63d51219798e544865d63951219b58a544867561951218f993534863d64d4d218f992534863d6494d219b58a53486756194d219b99742486ce63d0921b9987424866e6510921cb550424866e65cc921ab99332486e661cc9219b994324874d530c9219d99741486d663d0521b998b41487a442d05219d99441487355410521e9d08414867665cc521ad99331486e662cc521f10cb3148676650c521d554c31487c7320c521ad99321486d663c8521ab99221486ce63885218f990504863d64141219798c504865d63141219798f540865d63d50219b98b540867661d50219798e540865d63950218f993530863d64d4c219b98b530867661d4c218f992530863d6494c218f992520863d64948219798e520865d63948219b59642086cd6390821b9586420866f6550821cb151420866d658c821ab59232086e5618c8219bd95320874c534c8218f992510863d64944219798e510865d63944219d59641086d56390421b958a41087a542904219dd9541087345450421e99094108675658c421ad59231086e5628c421f14ca3108677654c421d514d31087c6324c421ab59321086cd63c8421ad59221086d56388421b958a210866f65484219dd9521086e76548421d9d9521086e76448421b959121087665448421d915121086e76348421b958d21087665348421d914d21086e460484218fd91500863c645402197d8d500865c6354021d9485500866e6294f409b58a53d02766194f409d58653d02ad62d0f40ad58743d025e6394b409758e52d02766194b409d58652d029d63d0b40ad58742d025e63947409758e51d026e62947409b58a51d029d63d0740ab58b41d026f6254e409b18953902776154e409d18553902ae6290e40ad986439025f6354a409718d52902776154a409d185529029e6390a40ad986429025f63546409718d519026f62546409b189519029e6390640ab98a419023e65d0d40c714f43502ad62d0d40ad587435031c5350d40d3d4f525034c53d4940d3d4c525034c5314940cbd0c525032d43149408f997425029d63d0940c714f425032c52d0940ad587425031c5350940cb149425035753d4540d514f515036752d4540d914b51503575314540d514c51503675214540d914851503374314540cd50c51503374214540cd508515023e65d0540a758f415031c53d0540ab58b415032c52d0540cd147415031c5350540cb14941503345150540c714e405032c5290140cd146405023d6590c40c754e43102ae6290c40ad986431031d
  | 4 => 0x718d54cc66e62153319b58854cc71d54d0f31b398b43cc6d661d0f31c755043cc72e5494b31cb55252cc7656194b31cb95152cc72d5454b31d3d0d52cc74c4354b31a799232cc71d548cb31d354a32cc6d6618cb31c755032cc74d520cb31cd95241cc6d56390731e5d0e41cc6e56290731d994a41cc7365450731e510d41cc76652507319b98b548c66d62d5231c758e548c73461552319b988548c66d6215231c7952438c6cd6290e31b5586438c71e5450e31cb952528c72d5494a31d390e528c74d4394a31cb951528c72d5454a31d9185528c69d64cca31c7953328c74e52cca31b5587328c71e544ca31d3949328c73554d0631b598f418c79643d0631b998b418c76552d0631cd550418c7954310631d9548418c69d64cc631c7953318c6cd62cc631d394b318c6b664cc631cd553318c6e662cc631d954b318c66e62d51319b58b544c65d63951319b98a544c66d62951319d586544c65e65d0d31b398b434c6d661d0d3197994434c71d5410d318f993524c63d64d4931a7992324c6d6618c93197994324c67665d0531b598f414c79443d0531b998b414c6766510531cd550414c7974310531ad993314c6e662cc531a7992314c6ce628c5318f990504c63d64141319b988504c66d62141319798f540c66e62d50319b58b540c67661d50319b98a540c66d62950318f992530c63d6494c3197596430c6cd6290c31b5586430c65f6550c31c7151430c63e64948318f592520c69d64cc831b5587320c65f654c8318f992510c63d64944319d596410c6d56390431e550e410c6e562904319dd95410c7345450431e590d410c69d64cc431b358b310c6b5648c431b558e310c6e5628c43197d95310c677654c431b5d95310c757654c431b5d91310c6d5644c431d5951310c754544c431b5d89310c756524c431b5181310c63f64540318f191500c66f62540319b189500c75531540319798f54c865d63d5321cd58654c872c62553219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21d558653c871e5454f21c755153c874c6254f218f99053c863d6414f21cb55342c86ce63d0b21d354f42c86e661d0b21cb55042c874d5310b21ab99332c872d54ccb21d354f32c86e661ccb21cb55032c874d530cb21cd95241c86d56390721d594e41c86e56290721cd95141c87565350721e910941c86b5648c721cd95231c8756538c721b958a31c8736544c721d594d31c87c4324c7219798f548865d63d5221cb58a548873461552219798c548865d63152218f993538863d64d4e21c7952538871d5494e21d358a538871e5454e21c755153887546154e218f990538863d6414e21cb95242886cd6390a21d394e42886e56190a21cb951428874e5350a21ab592328872e548ca21d394e32886e5618ca21cb951328874e534c
  | 5 => 0x43ccad661d0f32c755043ccb2e5490b32b358e42ccb8f4390b32b958642ccb2e5450b32e310d42ccb365494732cd55251ccb664294732d950a51ccb365454732cd55151ccb574354732d510d51cca7661d52329d587548cb1d6395232cb189548ca7661152329d584548cb1e5490e32b358a438cad56190e32c7951438cb2d54d0a32b398f428cb8e43d0a32b9987428cb2d5410a32e350c428ca9d64cca32c7953328cad561cca32ab993328cb2d54cca32b9987328cb365494632cd552518cb564394632d550e518cb573294632cd951518cb355454632d9d09518cb644254632d9cc9518ca7661d51329d587544ca5d63951329b58a544ca7661951329d586544ca5e65d0d32b398b434cad661d0d3297994434cb1d5410d329b997424cace63d0932e310f424cae661d09329b994424cb2d5410932e3d0c424caae64cc932b9987324ca9e648c932b5986324ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca5e63d50329b98b540ca7661d50329d587540ca7661950329d586540ca3e6494c328f592530ca5d6590c32b358a430cad56190c3297d95430cb1c5450c328f992520ca3d64948329b596420cacd6390832e350e420cae561908329bd95420cb2c5450832e390d420ca9d64cc832b5587320caad648c832b358e320cae5618c83297d95320ca6f654c832b3d95320cb4f654c832b3d91320cacd644c832d3951320cb4c544c832b3d85320cacc604c8328f992510ca3d6494432d34ca510ca3f64540328f191500cb4d32540329dd85500ca746154032d558653d071d5390f41ab98a43d06b66190f41c754c43d074e5394b41d354e52d07656194b41d394d52d074d5354b41cb90d52d072c4354b41a798e42d071d5390b41cb54a42d06b66190b41c754c42d072d5210b41d5185539071e53d0e41ab58b43906b561d0e41c794d439074e5394a41d354e529072f4394a41cb50e529074e5354a41d354d52907646154a41a758f429071e53d0a41cb94b42906b561d0a41c794d429072e5250a41a758f419071e53d0641ab58b419072e52d0641b598f419075553d0641b998b419076552d06419b98b535066d62d4d41ab98a43506b66190d418f994435065e63d49419758f525069e6390941ad986425063e6510941b598f41506e662d0541a798e41506ae62905419798c505065d63141419b988505066d62141419b98a531066d6294c41ab58b43106b561d0c418fd95431065e63948419758e521069d63d0841ad587421063f6550841a758f41106ad62d0441ad59241106d56390441b958a411063f65504419dd9541106b76550441cdd9541106b76350441cd94d41106b76250441cd94941106b4605044197d8d501065c63540419bd89501066c6254041cd505501066e62d53319b58b54cc7356195331c
  | 6 => 0x401801000400000000400800800000400400000000000000400000000000000c00000400002c00401401c00c00000002400003800c08804c01400c01000400000800000400400400000401000000000000403c00000800001001801001000000800001800000000c03001400001000c00001400400000400000c00000003000800000800000401001400800c00800400804800000000401400800000000001400002000000402801000c00000800000007800c00400800c01400400000400001001800c00400c00800400802000c00800001001000000400007000000000801800c00800000c00000003000002400002800001401403000000000000000000800000000000400400001400801400000000402c04000000000401000401800c00000c00002000001c04400001c00401400800400c01c00000000000000000000000000000800400001401401000800400000001c01401c02800401400400005402c004058000008004004008000004010004000000008004000000014000000010028008004004000000028000000000004014048014004007665294743d954a51d0f665254743d954951d0ead62d0e43ad5874390ece62d0e43b59874390f2f4394a43d3d0d5290f665294643d954a5190f374394643d99495190f655254643d5d0d5190ece62d0d43b59874350eae6290d43ad9864350e7661d49439d5875250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050ead62d0c43ad5874310e9d6490c43b358a4310ed56190c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9f6150c43a71814310f1d43948439d9865210e756194843c750e5110e6e62944439b58a5110f1d43540439bd895010e6c62540439dd855010e746154043d358a53d0b1d5390f42ab98a43d0ab66190f42c754c43d0b565394742d554e51d0b565354742d554d51d0b364354742cd10d51d0b4c6254e42c794f4390aad62d0e42ad5874390b1e5350e42a758f4290b1e53d0a42ad5874290ace63d0a42d354f4290ae661d0a42d594e5190b555394642cdd0e5190b354394642cdd0a5190b565354642d554d5190b6742546429d9875350a7561d4d42ab98a4350ab66190d428f9944350ace63d0942b99874250a9e6390942ad9864250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050a766194c429d5865310aad62d0c42ad5874310a3f6550c42a758f4210ab561d0842ab5924210acd6390842b95864210a3f65508429bd954210aaf6550842cbd954210aaf6350842cb94d4210aaf6150842ab1814210a5e63944429758e5110b2d429444297d8d5010a5c6354042cb5095010a7761540429d1855010a7661d53329d58754ccb2d6295332c718d54cca7661153329d58454ccb1d54d0f32b398b
  | 7 => 0x18780025a8000000000001bb80025c0000000000000eb0f793400019e27600008d18800000000000000000008126b800000000000000114a4a83002f8748c28000002920c38ac04c0000fe1ef0040000000000c1a4d09415528900017880008288880d00000006d8000c11a19e68060729e000004700018f9a6271000000000000107a20823285a5600020804f1ce8000002528000000000000000000002048ef8000001ba00000000000000011896f800132243a3c8fa9780001388000000002b20001c00002ad800000180062a618001898002ad00000028b00025b8978e915f00000000023b0b2981285000000000005274800000000277aa300000021f2070000001cd8000000000001440002688001a51b28002470a889321316f2a286a22800016e8001cf0000001dc8001198001cc80026780010806380029c0000002b18001048000002a39d68d31d906780000018696b209a301bd2a51b997902b08f05b876a5e0b5842a750000000000001f20fc0fb00024c28d8410000002a82908002178ec8152b380001d8000c32988000229ee80021c8001fb8ba80024d80005880000000003e92799316016115e88480000011da7680000000000010280000022e00000000000b8000690000001740001a0a7e80000000025f821a4e8ce0f10011e40000001490000000000001df00000002e0000001ab8de26c0000a900001c80026a8378000000002448000000000b08d686100028f80000029520d00586b8000ff80000013d8000e285c0000000fc80000000000000000007d8002360000000002b99eb8f4a5a27a8000000000000000000000000000080000000000e193b9a2032800000000156a640001c680000000007e0000000000001c80680001300000958001e5947a8f00000011d20f15300000024a0002288b426497d8b52010002be0000002a707a13c0000000000000002b82982b7a4580000029e81f9fc10d80012d8348000002bb0c9880a9995d801400400000000001800000800802800c00000000800000000402400c00c00803400800800000000800000000400000400000800000801000400001400800c00000c00001401000001001800c01c00000001000c02c00400c00000801000000400000000000000000400400400005802000000400000400000400403000400001801c00001000802402c00000801c00800400c00401000c00000000400000400800800000801000400800800000000800000800800000000000400001800002002000400000400400c00400c02c00000000000001800c00400002800001000001c00c00000000000400000800400800400c00000000c00002800000400000000800403401000000c00000400000800000000c00804400000c00000400000001400800401800000400c00000002c0
  | 8 => 0x202a218380028825b0000b3a7da8d00000000006f0001e31c380000b0001370000000000001af8ce9a992617d02f0362381429f11b21ed8d70001d197010b154a482318d980005613a89b8000000000001618000000001dc00029c8e806b2680949e2aba81400027825383d94991a0800268000108000000a484301f0e99230000a100000000000005da1080000016380000024900013786e8a20000261452240000b79e18000000000000000000002261738002368000000000000830000000000000e10002ab2bf0158901ff0002c481e8d22800238e40c6a6394b1060001851a58b4a510001448002c0066193a322ac07000025d0b81cb8000f9845000221a8897e9a3150800089a4b15d2a900023728700023b80000008c0001bd8000000000000001c500000022f03a00017581d0000000540001d580000000027980027300004d85f8000001d40000000000001ab0a5a700000000000000001c28eaa312840000000000719e080000004689f800000038059a7a0000000698000002af16d04eac41e502a0a9a330b70ef0000002221288a500006f9068110f517c13f00000000021f8000e700000000000000000000011aa9fa2d93923a2b28001650000030a60000000000000000001ee0002c09d88002c300000024f00000000002d9840002b700000000000000012580000008d80000027e0000000000000488000000001252031fda9f1e788500027b21900000025e800117a9d800075864296282a1e20780000018d8000002830001a48001748002a58000000000bb11329b91595e11080013c8002609fc9909de0be8000001f08bd80000000000027f0000d7800000000000000000000000105a600000000420000000f324985280000019d2000000000000000000000002259710000002c580000019280013800000023c0000000002359170de80016606684b8002550342ab81602200000000000000000027f8d400000012e8d5816a620ec0000000000002290001fa89717a80021680025c86e0000539039330000e39859411a39fe1b3926a40aa19c9a6f8000000000001ec1d21b083ba2c80022687116780015f80003700007203e00011121b90f8bc8000000d1134abc0000000000000002a61418000ee1aa9210002c2a9a80000000026d17680000000005e9830000000000000000388000000000000000000000000b992294607401b2171ae00000018a0002428001f88000000000000001d808b8001dd0289001a89140000000001e70002708ea1ba94d26a2c70000000000000001c89590000000000000819e3a912118000000001960001f18201f4077188a8e83116a17289395a8000000000db00012e10b85300008a9b500026d98a80018094b9e601780000022a1f924423f80000007f93127918c878254a0a8c720c9f0000
  | 9 => 0xa9cd0002ae87780016a9468b68001071b30000000fd19980922b0001bf8518001d380025d8002180000000000000dd0000000000001399cb000197aba1ca0000000000338000ad0000bfa0ba690f19f48f70318000bd0000000000000550000001f28da00010c8c61680000001990000000bc00027216590a80000000013a10a0960000000000000000001fb0001da8870c003a80019400e80000022980000000000025700712a0000cf8000000000001e48000000270db8000002930001ea80000006a9328000570f20000000000bb8000af00000012b23d8000248000001a78d60c8000000000000098a808002b680010e1ad8000002238000000000001f99b00a692c17a18f00012a8000000000000001581718e4a0f92d0000000000000f080011380000011014380002980027d13f8a38001f610e951262800130a65000000284a4b8000e783513b000191813a6726b0002042150088000001338308510458f38000000001900000001cf9bf00000000015a00000009d00000000006000000012007b8000001c307d27c9208820000001c4a532110d19de9a680024680018499f95700000228c01802b80000021a2948000001688688650000000e8994a9a0000001b619e88c8001608000000000000002b000000000009c2589d28a78590000000000001b903d1042158001358000002af8000002431e80001b18000001bc8001362228e098b096a8a0000000000001180000000000000a706720b0000000000000000ae8002230000001ac0000000000aa80002a8751c42a68578002598000a829785d00000011b1dd80013e80021a8001fd10100009d80010216e0002a78002018002bea3e2bf8000000002a98002a4a4780000000000018219b1d70d00c50149778e52008cd15b1b88098c79db2542b5a188000b88018d499114a1eb041a0290506580029b0002c18000002b89221efabd8ed9d62038000188000e311e2051e994303c0002c695b8000000000000d90000000000000952a89f3a6129001a2309d31e924108e0001a90618440e5a349be9160568480c20af80021397f836a729f821280009a8002878ab00007e9ed0000000000d38000259030000000000001018002b62aa0000cc8f283999f1d0a452c397701315412b8210000000001f680009c95390d0049480000000000001971b40001e221b16705019a9ea24ca3520e8000582b480021422c20a19c80020c28ca501b80002091a10b323ea3a916800000060955ac205e0d08000b118280000000005a8002568000ed1d48000f60a02811f700000000014e8001ec8002738000000000000000000ee80000019b8000028000000001ad1be02421d8000001518000000001980000000000002aa96294204780025823d019ab50a40000002198460172938a30738b1800000296a
  | 10 => 0x2a022713e0001c19620002398208cba9e0df0a2a2d159a5594d84d0d51a004b00000028226980c06c86c2b318c1ae88691180015c1c08000d89ce07300000000011280000003cab924e1f78409b7900ab400000000010f25183f0bf0000b0152027890884286003835a7ba4600009e9891bc00009920e0000f420d9401292520c888780005f1270c40000000fa1da1750f680000000000000009280021c0cf14580011c18bac60daa8e0000918000000000001bb00000000000000000011200000000000080000000010c0000000000000000000118000000000002b080026c8251d98000000000000000002a106d0520d800007a9aa00007c055800000265996a971b49760000ada0604f8000321fe9b10000001720998620000000000000000000000001730000000ca00007b00017c8dc07c88b2a42252122419b589f1150fda7896c1f50002928f58fb87905480000001a9798001c11649092488120f899da8b8ae0000000000000000001ac82800000000001280022a8d281c000124a9580014fab100013d0000438000000000000000e014c80000000002e8000001578000000000000000000000000000000001d11c208605cac12940838892160000002bca0680000008f9a809a21e91e82c019283a338001922ae0000f000d8eb8001988cd8dca6600000000000019a09200000000008e96b80008a0fe8002992579a28b629d232aac8c480011f8f80f91dba8199c0788000002bd0000000000000630001b714e0002898000000000000000000001ca89e0508001c780000026f00000009805b0001958000000000000a18000000000aa0000e680000000018e8000000000001631690000c0981a66ac500004a01ba919d001e0cc000242121a0880027c0001a70001e124000000022e80000014090884017f00a0dd81022780000007080000024f80022100012984921d0000001c90498001e88000000000001c6123a6e8000760cb00012414a91f1872389950be28697b8001ff8799a418e00016d96c9709641c70df80011ba0200003b0448390000000000000000ca8a089b00018d00008580f22f8c595880000000026e23791c9489b68c90292a08b212f1af15c80000000026300c82c9699cc06484a8001d79df9fa00e2771529318b90aca7582d2bb8068000000e600000000000023f0ab80012f8001d500003f80a93693525f16695600fa100000001c5a3900012c98600017e0001f327185a15011917b10984ca2b8000000002508000002340880000000000ff03300000000012800000014f0000000000000000000000000ba0000002058000000000002740911f5800000000007a590e221494714c04e07f224a8
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x10e166454f2188652ba6ca90843315cf6548421a4ce9b2a4210d4673d952108662b9ec890843199da5448421a8ce72a24210e25641512108652ba6c690843199da5348421a4ce929a4210e456314d2108652ba0c090843315cc6048421c48c890aa010e4463485500870629ac5a1a818514d61d0d40a4ae3a18a4a060d6314b425030a29ac3a12818914961d0940a4ae5a18a2a051573d08515030629ac5a0a818358c52d0540c2ac628e82a0625621474150306a9cc5218818554e6190c40a4ce321aa42060e6354a421030aa9cc3210818954a6190840a4ce521aa220516739095110306a9cc5208818398d5290440c2cc6a8c8220626625464110306a98c4a00818318d5250040c2aa630a802062552185401030a31aa2a0081891895150040c18a8b14869861454586434c2a2b8c8629261075d854cc930c1ac8296649861454587324c322292c399261515ca4314530a2ae9990a29841d76153314c3062a2c598a618359052cc530c2ac828e629864562147314c306aa4c5a18618555261d0c30a8ce3a1aa41841f76552320c307322a51906185552618c830c8aa530c641854672d0d510c28b3a464a886107dd9548c430c1aa9314621860e6454a310c30b322a31886191989518c430838ecaa2601860d54189300c306322a49806185550614c030c8aa430a601861464545300c322312a29806183151639092089aec29c849062454586424832229ac3212410b5d8548c920c1ac829c649062454586324832229ac319241515ce4214520a4ae9190a29042d7615321483062a2c790a41135d853c8520c1ac829e4290625641472148322b18a390a418355263d082089eeca9e8410625549874208322a9cc3a10410bdd954cc820c1cc8a9e6410625549873208322a9cc399041519cf4254420a4ce9992a21042f765522108306aa4c71084113dd95388420c1cc8a9c421062664546210832331aa3108410b1d95448020c1aa831a401044c7654d2008306322a690041895506148020c8aa630a401062464545200832231aa2900418515163905108aaec29c82886245458a414432229ac520a21195d85290510c8ac6294828843576152314430ab20a718a2189151628c510c88a6b1462884657614a3144312b20a518a210d5d85488510c28a8b1c42884557614e214430ab20a710a21895905288510c8ac629442886155498f410422bbb2a7a08218955262d0410c8aa731682084677654b410432331aa5a08210ddd954cc410c2cc8a9e62086255498b3104322a9cc59882119dd952cc410c4cc8a96620843776553210430aaa4c79082115dd953c8410c2cc8a9e42086266454b210432331aa5908210d1d95444010c2aa831a20084547654d100430a322a688021895506244010c8aa63122008464765491004312322a4880219118d5244010
  | 1 => 0x4210a8739ecaa1085499c7655084294ae3b1a842160f6394d4210a9338ca6a1085235cf615084291ae630284214a5711814210b0731a85288858318d4254042c4a8430aa02160d5498b43ccb0aaa4c3a1e65839516390b32c4ca8b0c859948e7610d42ccaa2b9c8528e65519cb4354732c1ca8b14871961654586438cb06aa4c7a14658955261d0a3291eeca18851941d76953328cb0b2a2c3994650bdd954cca32c4aa930e65195457290e518ca8aba66528c65519cf4254632a4ce9992a31950e7510f424cb0732e862126543dd54390832c1ecb21a841948d74d95320ca62b8eca99065439d3654c832a8ce3b2a64194c571d91320ca273b4a89906583d92544c832a8ce32a2641960d64151320ca46ba6c299065235d0604c83298ae2302641960e644ca510cb0632264a8065914c86154032c1aa731487a0e155398643d069338c86a96838398d5290b41c2aa730c85a0e255298642d070729ac5a1c838594d61d0e41a4ae3a1ca520e0d6394b429070b29ac3a14838994961d0a41c1ca6b168320e0d6394b4190722a9cc5a0c839198d52d064192ae7b2a8220ca572d95411068b39ecaa0883499cb655044194ae5b1a8220e176394d4110693394a6a0883255cf6250441a2ce72928220c95731814110652b90c0a08838518d4154041c48c4a0aa020e0d5498b43cc70aaa4c3a1e63519c74354b3183eecaa46598e0e6454a32cc70aaa4c3196639154a618cb31c2ca8b1c8398e265458a41cc632bb4a520e639158e529073192cec21a8398e0e5458a438c70b2a2c321c63515c64394a3183aed2a66518e0d6494b328c70b2a2c3994639194961cca31c2aa931e8318e255498b418c633bb2a5a0c639198d52d063192eeca188318c1d76953318c7072a2c598c638359252cc63186eecaa66318e255498b318c713322a598c63459d443d0531c2ccba188298d177550e410c70bb2c86a0863255d3654c43198ae5b2a6218d1674d95310c6a3396ca98863315cb644c4318aced2a26218e1764951310c6a3394a89886385590544c43192ae9b126218d1674949310c64aba0c098863315c8604c431c28c898aa018e44624c5500c706aa4c7a164313dd953d0b21c4aa930e8590e455398742c8617bb2a9996438399153ccb21c4aa930e6590e455398732c870b2a2c720e43155da5390721c4ca8b148390e465358a41c861abb4a918e4385592538c721c4ca8b146390e465358a31c87072a2c721443135da5390a21c4ca8b0c8510e46535864288616bb4a91944383592538ca21c4ca8b0c6510e4653586328870aaa4c7a0c4315dd953d0621c4aa93168310e455398b418861bbb2a998c438599153cc621c4aa93166310e455398b3188616bb4a990c438395163c862189aed29e4310e0d6494f218861bbb2a990c438555263c86218aeeca9e43
  | 2 => 0x534003d1444c4cc0cd5013c0243c001d50b4ec0d028a9328002b0004f137000d23c0f3578cb0794b125344842a15c3b549140002f000770f8a12d9484cd253b4001f80420c0039c6300000298104a0005881a00000090250d0e2294860006158cc23e9262cc262b8001355c0c8e90006e4440023d3e02c000b101000791cc0c198005905653c112606926c7d3fcfe131454351c1b52026428518d0004ee22cba14116064f245c8a438d1334000f4002d42e4e8be000200512f0d95b0012a188a7574a00fc072a11b4b895371130014148d0c1441f2209e4252c290f6000762496b10800475074e0000705d32400000e84f4e521c0e3642b1c0822c93223400378000000019c0012000400970016801458441023391e000e64fc6b38494115403602705c7402400190005615620149000f1000f955c7151c002dc9a0003c11815000441e03a3d4c43dc00000083b04e1a8123a8410dd220005b2a83100139460df0a5552450450c003e06503c00528000000053167164ab3bd0640d6506d605a4dd380004c0d64d847074962112d2e4234295350806368c8274d42245a12cbd3180328cb1204b017c8c38c6c214e42ec521ec542883830cdb000c73014e57cb4550c1129271e800421055987f24c002fc3504d6a000d3154214d52900022001611a0303ac0047c18058af5688e4645c3f46017890454cf468bc2e0395452b27cc5448ad0b4000000014c001c8430000049000100d5000002706f000d71f0003ecfc564020000400090385c0a00008dc0210058000401000045c0b098082c0200024000000830020b028141a0207800000f0f00016030004804040880c02032b01004000100c1e0e008040000000002e03010642a040380022030000012000000072010c82c0c010201020010080006010600c34010002806020d0200005038000005080180203000440c08a4ae3a1ca521d4671d0d5290e92b968728c87519cb435464391ae5b2a8621c9571d954310e87396caa1887459c76550c4392ae3b128621c8d72d854310e46b90c0a1887255c46050c43a1ee4a1ca421e15439865210e8bb8a87288878350e6294443c1a86312a021e15431855010f06a9cc521e858554e6190f42a4ce521aa3a160e5358b4390b0b29ac3a1c858594d61d0a42c8aa730e852152572d0e5190a8ab9e8528c85519cf425464291ae7b2a84214a571d95
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x880f87590544c83281787590544c431
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 830
  | 4 => 1423
  | 3 => 364
  | 2 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (731+((h/13+packedAt s1K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s1K5 (25446+((h/276+packedAt s1K5 (22410+(h % 276)*11) 11) % 1096)*11) 11
  | 4 => packedAt s1K4 (59762+((h/474+packedAt s1K4 (54074+(h % 474)*12) 12) % 2498)*12) 12
  | 3 => packedAt s1K3 (18925+((h/121+packedAt s1K3 (17836+(h % 121)*9) 9) % 437)*10) 10
  | 2 => packedAt s1K2 (122+((h/1+packedAt s1K2 (120+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffc0ffffffffffffffc3ffff
  | 2 => 0xfc1f03f83e07c0ffff1c1c1f0e0f87c3fd5293
  | 3 => 0xffe003ffc007ff03ffe01fe00ff007fc3e631c
  | 4 => 0x3fffff80003ffffe0000ffff8003f83e0
  | 5 => 0xfffffc0000000003fffffffff00000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x4000008000000000000202100108040000425
  | 2 => 0xa946659194aa95d1cb0d0d1a268d168b9d5292
  | 3 => 0x30caaaa28d353456d56217484ba42738ae6318
  | 4 => 0xa294d34529a1a69b66b742108dce72113783c0
  | 5 => 0xc318e38631c638e3b8db9b9ce10844223bf800
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaaaaaaaa0faaaaaaaaaaaaaa0faaaaaaaaaaaaaa0faaaaaaaaaaaaaa0faaaaaaaaaaaaaa0faaaaaaaaaaaaaa0faaaaaaaaaaaaaa0faaaaaaaaaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36905
namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1800a02c0530828224e0604bf43bd43bf42bd42f731f431f721f421be40bc40f710f510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x480000000001c00020460102019401025aa5a1c754f42b32966395430c6aca790e9508218ea98812d52102a8a6885914910
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s2K3 (285+((h/3+packedAt s2K3 (270+(h % 3)*5) 5) % 22)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 1 => 0x81f03ffc0f83e0ff8f0783e0ffc3c1e0eacecc
  | 3 => 0xfe003ffff003fffff007fc00fffc01fff30f0f
  | 4 => 0x3ffffffc00fffff80000fffffe00fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x84000088200000000108842210044422005055
  | 1 => 0x2c665918e52549658743a34676428d466ac6cc
  | 3 => 0x18aaaa21434a98aab0856908aaa8119cb30b0a
  | 4 => 0x514d34428a60d2d35ad04210cd333808dc0da0
  | 5 => 0x618e38730c731cfc6ce6739c0e222110ffa000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaeeaaaa00eeaaaaaaeeaaaa00eeaaaaaaeeaaaa00eeaaaaaaeeaaaa00eeaaaaaaeeaaaa00eeaaaaaaeeaaaa00eeaaaaaaeeaaaa00eeaaaaaaeeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36905
namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | 3 => packedAt s3K3 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (17+((h/1+packedAt s3K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x83c1ffc1e0ffc3f8f07f8783fc3c1ff0d6cd9c
  | 2 => 0xfc01fffe00ffffff007ff803ffc01fffe70e1f
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80008840000400010900888804444220050b1
  | 1 => 0x2892918c8952052874348519a428c96252c594
  | 2 => 0x1125221052a42253084950224a81128ca50a0a
  | 4 => 0x52b9c4295836ab9dad0c4443733380c4f80f40
  | 5 => 0x633187319cc733e6ce6e667062220308ffa000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36905
namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x9d43
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
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x83c1ffc1e0ffc3f8f07f8783fc3c1ff0d6cd9c
  | 2 => 0xfc01fffe00ffffff007ff803ffc01fffe70e1f
  | 3 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80008840000400010900888804444220050b1
  | 1 => 0x2892918c8952052874348519a428c96252c594
  | 2 => 0x1125221052a42253084950224a81128ca50a0a
  | 3 => 0x52b9c4295836ab9dad0c4443733380c4f80f40
  | 5 => 0x633187319cc733e6ce6e667062220308ffa000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeaeae0eae0eaeaeaeaeae0eae0eaeaeaeaeae0eae0eaeaeaeaeae0eae0eaeaeaeaeae0eae0eaeaeaeaeae0eae0eaeaeaeaeae0eae0eaeaeaeaeae0eae0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36905
namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1c2e29588406c01f4a05680000140000b00184c2d50000000292c91380240068004442870050e86005518c3c887001e68009064000008000212664101010004000020c2801604301ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4638000956541b4c00691a000000006a000030006c002f346d0d3c47244800500c683e21155d16054004396b2026000000491d3b71005b6e0b010003180e0063004a000700006f4f2b006600572d255827101c5c3d735e3302513a00314d00450061282a00430017000f2e000023064e1e225308556500700000133714605a3f00364400321f125241723500624211647419290a0067002c595f4b0080030000020000800080010000020580800180028280010480838700000000000002800b0408e750c43b7290876d5210e7aa9215794e42aea9c85775150ae8a2a16bd4942dba8a85b45150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932bba8a6574514cb9ea49967d0932e7212659d424cb9a84996350932eba8a65d4514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96633e54c867aa990d794f21aea9e43ad428879a6510cf950219eaa0435e53086baa610eb50821e6990437a50086f2a010dd94640baa8c815f53502b8a6a05794c40aea98816e52102daa4205d94440baa888176518c2eaa3184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6415e53c82baa7906b50b20e6996417651882eaa3106b50920e6992413e540827aa8105794c20aea98417651082eaa2106dd0b10daa1621d732c43aa65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d453443cea4887914910dba1221b542443ae6488754c910f9a8221f220443e240885d94410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xe328000a880a499e12e71858a49a0064148a002c000180a900000c350d5210f254214532a3592424cac46150932e1d85424cb846150932e150b514cb854214532c354d420870d544c821ca5095008749325402193588535022d6215130c354d42c830d544cb20e150932c43245414910d114c52442346550910951953244385424c910e850920443c13248110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8000005800a0cebb0a84994877650b514ca823aa849922181195424c910
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (841+((h/15+packedAt s5K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s5K3 (952+((h/8+packedAt s5K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s5K2 (200+((h/1+packedAt s5K2 (196+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfc1e1ff83c3fe1f8ff0fe1c1fc383fe176cd9c
  | 2 => 0xffe01fffc03fffff000ffe01ffc03fff870e1f
  | 3 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 4 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x884001108000200010120244404888440050b1
  | 1 => 0x19442231905402287106208cc41192c432c594
  | 2 => 0x208954420aa91153088954112a822519850a0a
  | 3 => 0x729598852a0d559daaa11021b3270189d80f40
  | 4 => 0x431910e6333199e6cccd993822040611efa000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0eeeaeae0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36905
namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x60078057ac5cac600be9801d28b006051a416c6c00cb1002000062c904cea4437151e505cca21a015598a254a6027e012200139f31000002c54a112da2f4c9c1109a8c020c3810000582000c417021d98e0e0805ff53007f94c01fd53017f14c01fe43007f50c01fc43017fd4801fe52007f54805fc52007fcc801fe32007f4c801fc3200ffd4403fe5100ff54403fc5100ffcc403fe3100ff4c403fc3100ffc8403fe2100ff48403fc21017fd4001fe50007f54005fc50007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4003f71000ff84003fd10007d44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x844003ffcc22001ffc611000ffd3088007fe1844003ffc822001fde4110017fb2088007ff8844003fdc422001ffc211000ffa1088007fe884400afe4422001ff82110003ff65480017fb2a4000dfd9520004feca90027fe65480057f32a4000ff59520005faca90027fc65480057e32a4000df19520014f8ca90003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c690027ff5348001ff29a4000ff54d2004ff8a690003fe4348001fea1a4000ff10d2004ffea490017fe5248001f72924000ff54920007daa490017fc5248001ff9924005ff8c920007dc6490003fd3248001f69924005ff0c920047fec290022ff6148011ff30a4001bf98520047fac290022fd6148011fe30a4001bf18520047fea290023fe5148011fea8a4008ff14520047fe6290023fe3148011fe98a4008ff0c52002ffe4290023fe2148011fe90a4005ff0852004ffea09000ffe5048001fea824003ff14120007fe609000ffe3048001fe9824003ff0c12002ffe4090017fb2048007ff1024003fb88120047fe2090023f71048007ff0824008fe84120047fa2090023f91048007fe0824003ffd942001dfeca1000ffe65080057f3284003df99420014fcca1000ffd65080017eb284003df59420004faca1000ffc65080077e3284003ffd8c2001dfec61000ffe63080017f3184003f798c20005bcc61000ffd63080017eb184003f758c20005bac61000ffc63080077e3184007ffd4c20007fca610003fd530800ffe2984000ff90c20007fa8610003fc430800b7f3104005ffd482002ffca410017fd520800bfe2904005ffcc82002ffc6410017fd320800bfe1904003ffd842001dfec21000ffe61080037f3084003fd9842000decc21000ffd610800d7eb084003fd58420005eac21000ffc61080077e3084006ffd4420037fca21001bfd510800dfe2884006ffcc420037fc621001bfd310800dfe1884005ffc842002ffc4210017fd210800bfe1084003bf9802001ffea01000ffe5008007fea804003ff1402001ffe601000ffe3008007fe9804003ff0c02001ffe401000fef2008007ff1004003fe8802001ffa401000fed200800bfc9004003ffc402001fee201000ffe1008007fe8804003ff04020007eeca88013f66544001fab2a2004fd19510007eec688003f66344001fab1a2000fd18d10027eea688003f65344001faa9a2004fd14d10007ec8688003f54344001fa21a2000fdd8910007ecc488003f56244001fa3122004fdd4910007eca488003f55244009fa2922000fdcc910007ec6488003f53244001fa1922001fdd811000deec088007f36044009fba822003fd94110007eaa08800ff45044001fb9822003fd8c110007ea608800ff43044001fb9022003fd88110007e44088003f52044001f89022003fd08110
  | 1 => 0x2be640c007feb206000bf5903001f7ac818002bd640c007fe3206003bf19030087fea818003fe540c001feaa06010ff1503008dfcc618043ff530c01fff2986000ff54c3007ff8a618003ff430c001efa18600fff90c30007fa861803ffc430c001ee2186003ffd883001ffcc418016fe620c007f73106000bb9883001ffac418002fd620c007f6b106000bb5883001ff8c418043ff520c001ff2906000ff54830087f8a418003ff420c001ff2106000ff50830007f8841803fff320c001ff1906000ff4c83007ff8641800fff610c0077fb086003ff9843000dfcc21800ff6610c0037b3086003ff58430075fac21800ff5610c0017ab086003ff1843001df8c21803bff510c01dff288600eff54430077f8a21803bff410c01dff208600eff50430077f8821803fff310c01dff188600eff4c43007ff8621803bff210c01dff108600eff48430077f8421800efe600c007ffa806003ff9403001ffaa01800ffc500c007ffa006003ff9003001ffa801800ffc400c007ff9806003f7cc03001ffc601800ffa300c007fe9806003f74c030007f2601800fff100c007fb8806003ff8403001ffa201800ffc100c00bffb2e4005bfd972002ffccb9000afe65c800bfeb2e4000bf5972002ff8cb90016fc65c800bffb1e4005bfd8f2002ffcc790002fe63c800bfeb1e4000bf58f2002ff8c790016fc63c801bffa9e4000ff94f20007faa790037fc53c8001ff21e4000ff50f20007f88790017ff52c800bff2964005fb94b2002ffaa590003ed52c800bfe2964005ffccb2002ffc6590017ee32c800bfe9964000fb4cb2002ff86590017ff61c800b7fb0e4005ff9872000dfcc390017fd61c80197eb0e4005ff1872000df8c390033ff51c8019ff28e400cff54720067f8a390033ff31c8019ff18e400cff4c720067f86390017ff21c800bff10e4005ff4872002ff84390037ff50c8007ff2864000ff5432001ff8a190003ff30c8007ff1864000ff4c32001ff86190033ff10c8019fb8864003ff84320067fa219000ffc10c8007ffb2c4003bfd962001ffccb1000afe6588007feb2c4000bf5962001ff8cb1000efc6588007ffb1c4003bfd8e2001ffcc710002fe6388007feb1c4000bf58e2001ff8c71000efc6388017ffa9c4000ff94e20007faa71002ffc5388001ff21c4000ff50e20007f88710022fd6288017ffa944005ff94a20007faa510017fc5288001ff9944005ff8ca20007fa6510017fc3288007ffb0c4003bfd862001ffcc310006fe6188007fb30c4001bd9862001ffac31002afd6188007fab0c4000bd5862001ff8c31000efc6188015ffa8c400aff94620057faa31002bfc5188015ff98c400aff8c620057fa631002bfc318800bff90c400aff88620057fa4310017fc21880077f3044003ffd422001ffca11000ffd5088007fe2
  | 2 => 0x3008ffc4398047fd21cc023fe10e6016ffd433001ffca198003fd50cc007fe2866000ffd033008ffe2198047f710cc007ff0866011ff4433001ff8219800fff658c0077fb2c6003ff99630015fccb1800ffd658c0017eb2c6003ff1963001df8cb1800fff648c0077fb246003ff99230005fcc91800ffd648c0017eb246003ff192300affea918003fe548c001feaa46015ff15230095fac718057ff538c001ff29c6000ff54e300aff8a718003ff438c001efa1c6000ff90e30007fa8718003fc438c001ee21c6003ffd8a3001ffcc518016fe628c007feb146000bf58a3001ff8c518057ff528c001ff2946000ff54a300aff8a518003ff428c001ff2146000ff50a30007f88518003ff328c001ff1946000ff4ca30007f8651800fff618c0077fb0c6003ff9863000dfcc31800ff6618c0037b30c6003ff586300a5fac31800ff5618c0017ab0c6003ff1863001df8c318053ff518c029ff28c6014ff546300a7f8a318053ff418c029ff20c6014ff506300a7f88318053ff318c029ff18c6014ff4c6300a7f86318053ff218c029ff10c6014ff486300a7f8431800efe608c007ffa846003ff9423001ffaa11800ffc508c007ffa046003ff9023001ffe611800fdf308c001fd9846003ffc423001fee211800ffe108c007fe8846003ff04230007feca98002ff654c001bfb2a60009fd953009ffcca9800afe654c001feb2a6000bf5953009ff8ca9800afc654c001be32a60029f19530007fec898002ff644c001dfb226000afd9130007fcc898002fe644c001feb226000bf59130007f8c898002fc644c001de3226000af1913009ffea898003fe544c001feaa26013ff1513009ffea698003fe534c001ef29a6000ff54d30007baa69804ffc534c001ffa1a6000ff90d30007bc8698003fd434c001eea1a6000ff10d30007fec498002ff624c001ff3126000ff58930007f8c498016fc624c027ffa926000ff94930007faa49804ffc524c001ffa126000ff90930007fa8498003fc424c001ff9926000f7cc930007fc6498003fd324c001ee9926000ff0c930097fec29804aff614c025ff30a6001bf98530097fac29804afd614c025fe30a6001bf18530097fea29804bfe514c025fea8a6012ff14530097fe829804bfe414c025fea0a6012ff10530097fe629804bfe314c025fe98a6012ff0c530097fe429804bfe214c025fe90a6012ff0853009ffea09800ffe504c001fea826003ff14130007fe809800ffe404c001fea026000ffcc130007f6609800ffe304c007ef1826012ffc4130097ee209800ffe104c025fe8826003ff0413001ffeca1800eff650c007ff3286002bf9943001efcca1800a7e650c007feb286000bf5943001efaca180027d650c007fe3286003bf1943001ffec81800eff640c007ff3206000bf9903001f7cc81800
  | 3 => 0xf1086405ff4843202ff84219017ff600c80bff3006403bf9803202ffac019002fd600c80bfe300641affd40320d7f8a019067ff100c833fb8806419ff840320cffa2019067fc100c8057eb2ca003ffd8e5001ffcc728002fe6394007feb1ca000bf58e5001ff8c72800bff5394005ff29ca000df94e50017faa72800bfc5394005be29ca000ff90e50007fa8728003fc4394007ffb14a003ff98a5002dfcc52800ffd62940017eb14a003ff18a50017fea52800bfe5294001bf294a002ff54a50017f8a52800b7c5294001ff994a000ff8ca50007fa6528003fc3294007ffb0ca003bfd865001ffcc328006fe6194007fb30ca001bd9865001ffac328062fd6194007fab0ca000bd5865001ff8c32800efc6194005ffa8ca002dfd4650017fca32800bfd5194031bea8ca002ff146500c7fe6328063fe3194031fe98ca018ff0c6500c7fe4328063fe2194031fe90ca018ff0865001dfcc12800fff5094007bfa84a002fed425001ff8a12800ff85094007ff884a003fdc425001ffc212800ffd1094007fe084a003bfd9550007fec6a8002ff6354001ff31aa000ff58d50007f8c6a8002fc6354005ffa9aa002dfd4d50017fca6a800bfd5354001bea9aa002ff14d50007fc86a8003fd4354001fe21aa000ffd8950005fec4a8003fe6254001feb12a000ff1895002df8c4a800bff5254005bfa92a002ff94950017faa4a80037d5254005fe292a000ffcc950007fc64a8003fd3254001fe192a017ffd85500bdfec2a805ffe61540037f30aa017ff585500bdfac2a805ffc61540037e30aa002ffd4550017fca2a800bfd5154005fe28aa017ffcc5500bffc62a805ffd315402ffe18aa017ffc85500bffc42a805ffd215402ffe10aa002bfd8150017fea0a800bfb5054007ff282a003df9415001ff8a0a800f7c5054005fc282a017ffc41500bfee20a800ffe105402ffe882a003ff0415007ffecb98002ff65cc02dff32e6002bf99730007facb98002fd65cc01ffe32e6002bf1973007ffec998003fe64cc0017f3266000ff59330005fac99803ffc64cc0017e3266016ffd5330007fca998003fd54cc02dfe2a66016ffd4f3007ffca798003de53cc001fea9e6000f754f3007ff8a798003ff43cc01fff21e6000f790f30007fa8798003dd43cc01ffe21e600fffd8b30007fcc598016fe62cc001feb166000bf58b3007ff8c59805bff52cc001ff2966000ff54b300b7f8a598003ff42cc001ff2166000ff50b30007f8859803fff32cc001ef9966000ff8cb30007fa6598003dd32cc01ffe196600fffd873008dfec398047fe61cc0037f30e6011ff5873008dfac39803ffc61cc0037e30e6011ffd473008ffca398047fd51cc023fe28e6011ffd073008ffc8398047fd41cc023fe20e600fffcc73008ffc6398047fd31cc01ffe18e6011ffc87
  | 4 => 0x17fe648c8017f3246405ef992320057cc919017fd648c8017eb246405ef592320057ac919017fc648c83fffaa46400ff95232007faa91907ffc548c8397eb1c641fffd4e32007fca719003fd538c83ffe29c6400ffd0e32007fc8719003fd438c801fe21c6405bf98a3202ffea519017fe528c80bfea946405ff14a3202ffe8519017fe428c80bff9946405f7cca32007de6519017ff618c80b7fb0c6405ff9863200dfcc319017fd618c83d7eb0c6405ff1863200df8c31907bff518c83dff28c641eff546320f7f8a31907bff418c83dff20c641eff506320f7f8831907bff318c83dff18c641eff4c6320f7f86319017ff218c80bff10c6405ff4863202ff84319017ff608c80bff3046403bf9823202ffac119002fd608c80bfe304641fffd42320fff8a11907bff108c83dfb884641eff842320f7fa211907bfc108c801ffb2a6400bfd95320effcca9900afe654c801feb2a6400bf595320eff8ca9900afc654c801ffb226400bfd9132007fcc899002fe644c801feb226400bf59132007f8c899002fc644c83bffaa26400ff95132007faa899077fc544c83bffa9a641df7d4d32007fca699003fd534c83bfe29a641df714d32007fe8699003df434c801ff21a6400ff50d32007f88699003dc434c83bffa926405ff94932007faa499017fc524c801ffa126405ff90932007fa8499003ff324c801f79926405ff8c93202fbc6499073ff614c8397fb0a6400fdd8532005eec299073fe614c8037f30a641cff585320e5fac299073fc614c8037e30a641cfd1853200de8c299073ff514c839ff28a641cff545320e7f8a299073ff414c839ff20a641cff505320e7f88299073ff314c839ef98a641cff8c5320e7fa6299073dd314c839fe18a6405ffc85320e7fc4299073fd214c80bfe10a6400ffd8132005fec099003fe604c801feb026400ff1813201df8c099077ff504c83bfe282641cffc41320e7ee2099073fe104c839fe882641cff0413202ffeca19016ff650c80bff3286402bf9943202ffaca19002fd650c80bfe3286405bf1943202ffec819016ff640c80bff3206400bf9903202ffac819002fd640c80bfe3206405bf190320d7fea819003fe540c801feaa0641aff150320ddfcc61906bff530c81fff2986400ff54c3207ff8a619003ff430c81fff2186400ff50c3207ff88619016fe620c80bffa906405ff9483202ffaa419017fc520c80bffa106405ff9083202ffa8419017fc420c80bff9906405f7cc83202ffc6419017ee320c80bfe9906405f74c832007da6419017ff610c80b7fb086405ff9843200dfcc219017fd610c8337eb086405ff1843200df8c219067ff510c833ff2886419ff544320cff8a219067ff410c833ff2086419ff504320cff8821903fff310c833ff1886419ff4c43207ff86219017ff210c80bf
  | 5 => 0x804307ff8c021893ff5010c49fe2808623ffc404311fee202188ffe1010c47fe8808623ff04043015facb29017ff639480bff31ca400bf98e5202fbcc729002de639480bfeb1ca400bf58e5202fbac729002dd639480bfe31ca402ffd4e52016fea72900bfe5394805fea9ca400df54e52017f8a729003fe4394801fea1ca400ff10e5202dfcc529017ff529480bbfa94a402fbd4a5202ff8a529017ec529480bffb0ca405bfd865202ffcc329006fe619480bfeb0ca422bf5865202ff8c329006fc6194805ffa8ca402ff94652017faa32900bfc5194845ff98ca422ff8c652117fa632908bfc319480bff90ca405ff8865202ffa4329017fc219480bffb04a405ff9825201dfcc129017fd60948017eb04a405ff18252017fea12900bfc5094805be284a422ffc4252117ee212908bfe1094845fe884a422ff0425202dfecaa9003ff63548017fb1aa400ff98d52007fac6a9003fc63548017e31aa402ffd4d52017fca6a90037e5354805fea9aa402ff14d52016f8a6a9003fe4354801fea1aa400ff10d52015fec4a900bff5254805f7a92a405ff9495202efca4a9017fc525480bbe292a402fb1495210ffec2a9086ff6154843ff30aa401bf9855210ffac2a9086fd6154843fe30aa401bf18552017fea2a900b7f5154805ff28aa402ff5455210efaa2a900bfc5154843ff98aa421ff8c55210ffa62a9087fc315480bff90aa421ff8855210ffa42a9017fc2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a403bf18152017fea0a900b7f5054805fe282a421ffc415210fee20a9087fe1054843fe882a421ff0415207ffecb99002ff65cc841ff32e6402bf99732006fccb9900a7e65cc801feb2e6400bf59732006facb990027d65cc81ffe32e6402bf1973207ffec999003fe64cc8017f3266400ff59332005fac99903ffc64cc8017e3266420ffd5332007fca999003fd54cc841fe2a66420ffd4f32107bea79903ffe53cc801fea9e640fff14f32107b8a799003ff43cc801efa1e640fff90f32007fa879903ffc43cc801ee21e6420ffd4b3202ffca599003fd52cc80bfe2966400ffd0b3207ffec39906eff61cc837ff30e6401bf987320dffac39906efd61cc81ffe30e6401bf187320dffea39906ffe51cc837fea8e641bff147320dffe839906ffe41cc837fea0e641bff1073207ffe639906fdf31cc837ff18e641bff4c7320dfba639903ffc31cc80bff90e641bff887320dffa4399017fc21cc81fffb066400ff9833201dfcc199003fd60cc8017eb06640fff18332107fea199083fc50cc837ff886641bfdc43320dffc219906ffd10cc837fe0866405ffd963202dfecb19017fe658c8057f32c6405df99632014fccb19017fd658c8017eb2c6405df59632004facb19017fc658c80b7e32c6405ffd923202dfec919
  | 6 => 0x5ffa92a602ff14953016f8a4a98a7ff6154c537fb0aa629ff9855300dfcc2a98a7fd6154c537eb0aa629ff1855300df8c2a980bff5154c05bfa8aa602ff94553017faa2a98a77d5154c05fe28aa629ffd055314ffc82a98a7fd4154c53fe20aa629ffcc55314ffc62a98a7fd3154c53fe18aa629ffc855314ffc42a98a7fd2154c53fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff1815301df8c0a980bff5054c05bfa82a602ff1415314ffe20a98a7f71054c53ff082a629ff4415314ff820a983fff6590c017fb2c8628ff99643015fccb218037e6590c053f32c8600ff59643005facb218037d6590c013eb2c860fff19643015f8cb2189afd6490c51ffaa48600ff952430077ca921803fd5490c01deaa48628ff1524311dfcc7218a3ff5390c1fff29c8600ff54e4307ff8a721803ff4390c01efa1c860fffd8a43007fcc521816fe6290c01feb148600bf58a4307ff8c5218a3ff5290c51fe294860fffd864312dfec321897fe6190c037f30c8625ff5864312dfac32183ffc6190c037e30c8625ffd464312ffca321897fd5190c4bfe28c8625ffd064312ffc8321897fd4190c4bfe20c860fffcc64312ffc6321897fd3190c1ffe18c8625ffc864312ffc4321897fd2190c4bfe10c860fffd8243007fcc12180efe6090c01feb048600bf5824307ff8c1218a3ff5090c51fe2848625ffc424312fee2121897fe1090c4bfe8848625ff04243007fecaa1802ff6550c4fff32a8602bf99543007facaa1802fd6550c4ffe32a8602bf1954313ffea6a1803fe5350c01fea9a8627ff14d43007fc86a1803be4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128605bf1894313ffea4a189ffc5250c4dffb0a8626bfd8543137fcc2a1806fe6150c4dfeb0a8626bf58543137f8c2a1806fc6150c4dffa8a8626ff94543137faa2a189bfc5150c4dff98a8626ff8c543137fa62a189bfc3150c4dff90a8626ff88543137fa42a189bfc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028603bf1814313ffea0a189ffc5050c4dff8828626fdc4143137fc20a189bfd1050c4dfe082860fffd9443005feca21893fe6510c057f3288600ff59443005faca2183ffc6510c057e3288625bf98c43127fea62183ffe5310c01ef2988600ff54c43007baa62183ffc5310c1fff2188600f790c43007fa8621803dd4310c01cea18860fffd8843007fcc421816fe6210c01feb108600bf5884307ff8c421893ff5210c49fe290860fffd844311dfec22188ffe6110c037f3088623ff5844311dfac22183ffc6110c037e3088623ffd444311ffca22188ffd5110c47fe288860fffcc44311ffc622188ffd3110c1ffe1888623ffc844311ffc422188ffd2110c47fe108860fffd8043007fcc02180efe6010c01feb008600bf5
  | 7 => 0x400000000003800001401c01401000000000800000400000001400000000000400c00000c00c00400800000000400c00400400800000000400400001400400000000400001000000400000000800400004000402400000001000000800001c01402001c00000400401400400400000000000400000400400000400002003800000000000000800001c00c02800400002000000800000801c00401c00400800800401400400000000400800c04c00402400803004000800000000000400400800800000000001800000801c00000400001000000002000005402c01401000000400400400000001001000801002000800400800001800000000402800400803401400000c01001800000c01400000001800000c00c01c00000800000400800400000c00000000000000002000000000800800000000c01000000001002000400400800000000800000400400000800800003000000400000002000001000000003801404c02000000403c00400000800000400400000800400001000001000c00400800401800001003403000800000c00000002001000001000000403c00000400800000c00800800000403000000800000801001000001000000000001800000005800000400400800402000000c00001000000000402c01400801400001803800c00000400401001c01c00400400800002401400c03400001400803800400000c00800400c07000400000002403400400400000001c04000c00c00802000000800c00402401002800000400005c000004000004000018000000038000008000000000000018028000030000000000000008000004057eb2ca60fffd9253007fcc929802fe6494c01feb24a600bf5925307ff8c92980bff5494c05bfaa4a602ff95253017f8a92980afe6394c05ffa9ca602dfd4e53017bea72980b5f5394c1ffe29ca602f714e5307ffec529803fe6294c0b7f314a600ff58a53005fac52983ffc6294c05ffa94a602dfd4a53017f8a52983fff6194c557fb0ca62aff9865300dfcc3298abfd6194c557eb0ca60fff1865300df8c32980bff5194c05ff28ca602ff54653017f8a3298abff4194c55ff20ca62aff50653157f8832983fff3194c55ff18ca62aff4c65307ff863298abff2194c55ff10ca62aff48653157f8432983fff6094c01ff304a603bf98253007fac129802fd6094c1ffe304a602ffd4253017f8a12980b7c5094c55ff884a62afdc4253157fc21298abfd1094c55fe084a602bfd9553007fec8a9802ff6454c01ff322a600ff59153007f8c8a9802fc6454c05ffaa2a602ff95153006fca8a980bfd5454c05fe2a2a602df15153015fec6a980bff5354c05efa9aa602ff94d53006fca6a980bfc5354c05be29aa602f714d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a9816fc6254c0
  | 8 => 0x2b00000000000000013c8000000000002f589c8000000000000001b58000000002d7000054400275582a458000000000002190198001280668f28000002c4959d6d8000d9412ebb80000b98f00002dce40000e6862aa78f200000000007c07180000000009800000026b21489e4001490f9000187174800000000000000104600b181ec95c1d2cddb2115e9a61bba402d51e3a95013c3306ba1ba6701d5c51941bf83d876a9e16f72080000000000000000032f9ae0003168002b98001c6a934a500015500019f00000020f050800052b1380011b0000002dc2a280022218da42a340000ec8d11f76380000000002198000000708000002be8000000000000000000001a0a0102b80000031a80000004f0ff80003a0000781c88000ce0000000003130000234000000001dd8000cb800086454800000056e200088003222861fd837c0018ac2780018f86d40000000008b8b4822cda8e88168b800006980009611828f4002ad4002e307484b8003000a8c000002c2137000000000106c5d05005221895fa87aa940023200029005632ca4d2cf0000000e015c80024d5a22d800021b22910558ec6830a0001a72b380027c9688001aa122a67810ce50000000000c2094000180c0027a2bcb0217f80030d2fa08c0b280000000000005b4001130000000000002ed000130c001f9594a2f1cbc1ea212dc8000001acc000450000000002c180000000015700000000002f3019300992968000000000c680000000000000000022b00010030db1e07a0844e48001d8800000000160c854564001cd2e94000000000368ab80000000006d8000000000000001f005e400000000308158a0aaea1028000000001381c296c800000401c00000800000000002000400c00000000c00000400000000000000000000801001000400400400000001800000800400000400000800000c00c03c00000000400400000000400800800800000000000c01400402400001c00800c00000400000400800000000001c00c00400000401000402001000400000000800000400401001001002400000400000401400c00c00000403402c00401000001000400400800c02802000000800802c00400402c00002800402400000000801c00001001400000000800000000003000000802c01c00000000000000800000400400000000800001000000002000400c01400801800400000401800c00402400000400800000000000800400400401000000c00002000000000400401c01400000401000000000c00001c00c00000000000800000801800400000000402c01800000006400400400001c00000c00c0080000000040040100080040000000000080180040000000000000000080200000080440040040080000000040100000000000000040000100140100000000000
  | 9 => 0x2560002a800000000011c0ad07100000000000000013a00020f89ec0000000023f0000000001e40000002cba138000000001089fc80000000027f9c018c314ae42d49f28000481f224406c00000000000022d8ba2252499558000ecc000002ad00c8b92cc000000312ab900a400253047d710000000000000002ab933a388ffc0031e97a000290eb024c0001cf8001e50a4a591f9aadc000c117e80000018800021aa628002f41242049a342e99fa7d8118a40002e4959af0c4c029800167400123a660098000000001188f983a44e0cf00000000001d8000002a501f0000000000000000000550002c76490402399959fe6828000001f40a200000000003d00032a80000000000000000000000000000000fdc20000000000000002fa8000000001bc0002c626c80000008400000018befe8d34000b58fd0000000002df1fb13045680021bc000000000001b01da8b018aad301c8000003260002e6800271cbd11d80128d969800257400000084c09c002260884001321c489380000010040000029de4a9a2ac9222943a9e56927c0a9a9197f203951aab5ba2971316eaab610c1afaf81d7480a9619b8002770000000001b8b198ac8002808000045aaa54800000000000010ac9d6f15b0000002e28001a4c640000002e11c11d18379e800005e2668000001dc8000000002f780000029900017380000000000003a9e7a1c14c2c380019786cc0000003e0001660001e69af00025a8000000000000001494d90001580f50000000001a40a9c0023c8d571729f00000000002cd4115c4000000b3a881138000000000000fe874ed200000023c11531ba310000000000000000745788d3c701d9a74a6802c16306ab2d88365e23b12d1ac57a863a746ab00028d4ef8fd6da25122fe6119d80028c05d9099328a61811b40572d12d9a6301a2c00002e80fb8384d28000281831bd2bced00cf8dd0002b59f5800000000129ade225847a572bc58e8000490000b72f72c86e9c0015a8002b48001a44000000a6c0000025289aaabc001e212b0000000001821068000003060000000000000000758b6800000000274c000000001d80002ef245005a9d0000a311ce791448000001ad91e400025964b3380000000000000b0000002db0000000000000000002e00000bb80004690e80000016a82e6898830000fe00000000715cc002bd8000000000bf8002029ca520839c8fc000001d31901868da0d78c80874a70ae00025e8860220002e5a7512daa406700024fa6883f80003429b25d08800000003c8eb02d80000003727f0631082c800000020633100000000000000014f281000326800332198ca755410f8000976f60271f614e9985462418c9191093096ea0328a740c1901aef98d0a56e88002b108f07380003240000326b93b8000000000001199d6
  | 10 => 0x8720000000000b98000188000003058002fe00000000000000913182611780001b16780000007d0000002f51aed8bafd8c58002d5ac530e80000000027895613e91baf380018ddc42ba11e0000000000f688f8000000000002719ce80027d000054c4e80000000013600000007980000000a00000000017600000000000018cc001ce0000d480000000021780006600021600000000006a0000000000442dda7240000000010b083c000a283ba4321033080005b8000621850000002ff8e900001cc000000002e9000269acf800000193800291417148928a6d00000000000031a0aa8000000240000000000000002eeab41df8000003280000899480000002c8c00000000000149c0000000000000000000000000025c30b0b7c002df89a0d683646920e2579b78002e18000000000cc6941b080006151000000019800014c80000000016a0000000659b140000019a1b984c9f50000ec17da8d0001508000e30d9b2f00006197a61509480009f00000018a400000175957979e6a87b9a38000de8eba9d800174262c000001720000000000b1a5ba46e6249d9e10cd270477833d2fa449620c416f800206a5a0000000000000002fb28e4000000000001f081d00000004a97c80000a8f01610000000000001590000000001a48002158f40001c1800060df7c0000000025000000000028900480022d2c40060fb0678b508e80000010c97b00000004f8000000fe4000000c62f90000000a5c2a20800009f4818a84000001da1058000000002640000002ce25ca11038c0032531caaa4000df4000000000000000000bf29050497e0ccc740fcaaa81e0002b28b88be80018a0000000000000001d08d80003010002a98b1003aa385f00000020c8000001b80002d781de700000002a11ed00000000000000012680000da48c000001311eb800087a0ba80c001d3abc00007dc00046c00234a79800115a80442a8bc000002b097d1a6800000000000278000022800000000000136c4db161cc8001c9df9c0002499e32a0000000003104c00ab1122241210002ec00013b22e24082d0000001b217906100000000012e9f844120180000005e90aeb8800261a91c000000000828000000000002f280000000000015b9a58000001caea72fc16b0380001d92e4e2c8e38820c9cd580000029aa81b0780000000015d82e291008d4980000003b0000001390000003240002d408b08d00000027b9770000001a80002c7abf8000000000000000000000000a380000000000005cdbf25f9340003070001529b628b8001879bea098000aa5650ff0000608001d20000470001b517c0001172c1035c968000019309430001ea80000000015ac000000a10ea20c2659edaec8ed000138c000000000bc0000000000000000000f61f480020b0000003101fa0000000000
  | 11 => 0xcb867300000021f1e58000000000000000000554eb4000002fb9008c785386b0000001ff0000000000120000c52e7ae5000000104e280000cd9a500000000011908a80000000000015000027e199c44ac7e3a12314a22b87e59530994f9668356b21a899945f9ad534aee1e32ca8001478001cc1fdd9280029d4000000b5c000001d345b0000000000000000b080000022040000029cc000002948000d88988000339ec1b040006dc5aab7000000036c8380030908700021f4002850001eb0a070400009e0000002f10530f39160000126379c60edaeba0dab80001394f30000588346e6277a6510a2832350e8151217273ee980028cc0000019b000095020137e928000db2c8b0f8000a680000017000000003013d255303a3f80030500009fb259c39c81c7000a931d49e0aae1b1e58000188a7a8001032bf0002af1ba9ad000000073d6380000003880000000000010f66e0002eb00009c0002a20f48000737189798688fdcb432280004a3048a4c000002d90000001dd1b680000001c4000000e2262227aa0b191e70000002d8a4dc00136ace8002a8b120001108002bbe8f00032c00000000000000000011d2988000002b3172800000181400045abb4fed0709fc0000000000000002471d135003db4a31acb1ee32e823ef881f94d1f5dd28b223b9988af032e21a0530c80016151c8180000000000000001b706f05f40000000000003c0000b30000000d3000000000000090c001b100000007fa014000000a58000000000000001d78000a9224989800000000121aea4bc8002169890002761fe00000014b14180000000012580026f2e8d440ac000035996a5680012e0000f0a2700000000021d80028a00003080027142500026e8002a68000000000000001a100000000000000000000005c80000000010d15200018f59c8ca22468024d944c000002c58000001d580000005ec0000000009640000000000000000012f01172903299e8a95f70cae5380005d495f340ee88d80000024e80001306c8000000040db93d4f70000000f806500000030c2858000001f65deb33000034d730000000000598000d40000000000000f58000000000002130002de8002a5a12a4695a68397680020a051b140d3a5f29bab7b10a232180801b30ebc134e2a090000ed5ee80000018d400000000112800000146a3300028b1918a89cd80014e306aaf8000231999e480004649200032d12bb1192a0053318000001e980000015b55327b3201022cda8a8000001bc8a180000000003940000018fc00000064800004f1f8143150de2e20000000000000eaa6900022693fb1104de6d8000000000000d8e140c3a3900004984d6958002ac45bc0e0e72d18210000f180028fa3e0438000000000510001451c98000000858000001f300000000000000000000022
  | 12 => 0x520000002d280011a9b293a8178191ab0292979608000000002ae8000334000000000000000000000002939e280020d04600000015e00000026a0002a196028b40014d9fc0958001a912c1990ca93d8000000001794000000001f18978002299e18002c09549c08000e6000000261d78c002ac97089e8e183f1caa519f90000000000000592371331401c58002981040000002615b0e588001930b63178001a024b95a0d60001a3c0021d585b2b0000000d007f21a00000028e8000000000000d4c0000020e9bb0f1000000167c000a00000000001d114080000000020206e000132c6f8000002e0887dc78b651f002a41000272c0008680000000000028ca4880008880000000000000013f1ac00031dac31628000000000001c30000000000000fd80015f18380012cb2180011696b9751cf1ae525161af48be2cd0000001aba4f1ef1fba7591eb0e0001248000002a613c2871a98af8bd855a0880011a06d00004b00000001280022380027100001600000031b0001cdc000002a32f68aa0000002f01fe80018c45400012a80000023027fd060000311039ca00000024b28480000000000012918600000027680027f4000998000000001f69050111db89b0df000114184af982380007c8000002924000002ff00012600000024e12fcc28000000000000000000001d00000000000b78002000430000000001b194ab031d4011c8500024216c19605c724855ccc00028ec0003740000024630a8002734ca40000000002d4000000000a091100000000000013980000021e00c07d4000000000c48000000928001843028910a780000003480029a0ae8001e90152f300001a80029f80026c00d1a1b0f00000000000000000032b9cf4000788cb5df1be2474791e88001bd8420ee1b25fd000308800086c321de0000000000035ce4d08a7db380000000025b039000007800000028b2980026fc0000003180000000000029c20700028de3d98e2920000001220002ad89000000023380000023d00000000021ea4ca7292780000000000022fa3280009d00010d9e0000006b27800000000288a2c21093e0890104001d7243ae38081778000000000001ea03e8000001658000761ae8000000000000000cc800180aaac0026008c96416e0002c28002638003238003271200000000f78000000f887ec000000000000001cb8000000000409682db8000001af5fa8000000002497329f463e8e57008000000001270000001d502080005a0002be072815a1ec8487a87b26f8000000dfadd0e995d0000001a7909000171885c00000107ad607707e09de47c6000004d0c318b64a0361f10000002f1800259a358002e700000005790ba0441b8000002ac1efa70c001374148baa1f8100d22ba8000000000000000000000002acec9b0fc000000b6c82c00292
  | 13 => 0x11440000014b9cb0dc19709bac942680000028c4faa122c719a84769caae400223ddc00005c15680000002a80031c1b929e9a31ff800207a11acc937a04000114aca00019d0000c99f7a3600000009057b8000000000002ed8000000000001800d188e00008a01c0003231ac897142a6486e88110e0fc2aa1824001e600013cc6e630a5d8ef0cea2880000005dd119920000000000aac002a92455472471cc4fa1780e12d0a999db1671d684cc001add3598c8000002f080000000000000002f80000026080000e8001634002b5236981a2e9f384c734a3a84180000027200000007306040000000000000021ca54088c000002c6961cadad387532e00000018e40000000022a80011f8e0a8680000000007d8e78002fd2d690f2da989d0b5f4d0100022a00031594220310a8e5a8fc0016e8a64c08000002fcaf203980026f6bb31f0000000000001f88002bd000090800000290809400000273ab18cb0000000000000000001afc000001f800007e8488000000000002b6a84000153800000181c00138a558000218001c92820580020bb0000c705fc000000000000d700000021ce4800000000000000002c800000245c000000c8a5080000000000019c00000000000f80003524791dc0000000000018b0000000000000000d2c000001324000000918001db67e8dc80f0002a480028e16d2708000000000000000000003301458d500021d013990a058914a830b8002
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7734c110007d7634c110007d4634c110007d6534c110007d5534c110007d6434c110007d5434c110005f7724c11015df4724c110007d7324c110007d5324c11001df7704c11001ef7604c110097f3604c11001ff2404c110007f1404c110007f3304c11001fd6304c11001fd4304c11001ff0304c11001ff2204c11000df676c811000df476c811015df775c8110025f675c8110005f575c811015df475c811015df773c8110005f673c8110005f573c811015df473c811001df672c8110007e762c811015fe462c811015fe652c8110007e552c811015fe632c8110007e532c811001df570c811001ef760c8110067f360c811001fe620c811001ff220c811001fe420c811001ff27688110035f2768811001ef2768811001ff3758811001ff2758811001ff1758811001ff07588110007f3658811016ff26588110007f1658811016ff0658811001ff3738811001ff2738811001ff1738811001ff07388110007f36388110007f26388110007f16388110007f0638811016ff35388110007f25388110007f1538811016ff05388110007f24388110007f14388110007f04388110045f17288110057f3628811015ff26288110007f1628811015ff0628811016ff3528811015ff25288110007f1528811015ff05288110007f3328811015ff23288110007f1328811015ff03288110065f7764811000df67648110045f5764811000df47648110005f77548110007777548110005777548110025f67548110005f57548110025f47548110007747548110025747548110005f77348110005f67348110005f57348110005f4734811001df77248110007e76248110007e46248110007e65248110007e55248110007e63248110007e5324811001df7704811001ef76048110047f36048110167f3504811001ff25048110007f1504811001ff05048110007f3304811001ff23048110007f1304811001ff0304811015ff3204811001fe6204811001fe4204811001ff02048110047f2764811000df27648110047f0764811000df07648110007f37548110007737548110167f27548110007f17548110167f07548110007707548110007f36548110167f26548110007f16548110167f06548110007f37348110007f27348110007f17348110007f07348110007f36348110007f26348110007f16348110007f06348110167f35348110007f25348110007f15348110167f05348110007f24348110007f14348110007f0434811001ff3724811001df3724811001fe37248110007f36248110007e3624811015ff26248110047f1624811015ff06248110007e06248110167f3524811015ff25248110007e25248110007f15248110007e1524811015ff05248110007f3324811015ff23248110007e23248110007f13248110007e1324811015ff03248110
  | 1 => 0xc910007e462cc91001df670cc910005f570cc91001df470cc9100def760cc9100dff360cc91015df7768c910005f6768c910005f5768c91015df4768c91015df7758c910025f6758c91015f76758c91002576758c910005f5758c91015f75758c91000575758c91015df4758c91015df7748c910005f6748c91015fb6748c910005b6748c910005f5748c91015fb5748c910005b5748c9100e5f5738c910007d7638c910007d4638c9100cdf6728c91015fd7328c910007e7328c91001df6708c91015ff2708c91001df2708c910005f5708c91015ff1708c910005f1708c91001df4708c9100f6f7608c9100f7f3608c910005f7764c910006f7764c910004f7764c910005f6764c910005f5764c910005f4764c910006f4764c910004f4764c910005f7754c910025f6754c910005f5754c910025f4754c910005f7744c910005f6744c910005f5744c910005f4744c910007d6634c910007d5634c91017fd7534c91017fd4534c910007d7434c910007d4434c910007e7324c91015fd6324c910005f7704c91001df6704c91001df4704c9100e6f7604c9100e7f3604c91015df7760c910005f6760c910005f5760c91015df4760c91015df7750c910025f6750c910005f5750c91015df4750c91015df7740c910005f6740c910005f5740c91015df4740c9100ddf6730c910007d7630c910007d4630c9100f5f6720c910007e7620c91015fe4620c91015fd7320c91015fe6320c91015fd5320c910007e5320c91001df6700c91015ff2700c91001df2700c910005f5700c91015ff1700c910005f1700c91001df4700c9100cef7600c9100cff3600c910175f7765411000df676541100bdf5765411000df4765411001df77554110007776554110027746554110005f77354110005f47354110027775354110007755354110005f7725411015df4725411002777525411000775525411001df7705411001ef760541100bff36054110027f3505411001f76505411001f74505411001ff0505411001ff2205411000df676cc11000df476cc110005f775cc110025f675cc110005f575cc110025f475cc110005f674cc110005f574cc110005f474cc11001df673cc110007d763cc110007d463cc110007d653cc110007d553cc110007d643cc110007d543cc11015df672cc110005f572cc110007d732cc110007d532cc11001df570cc11001ef760cc11008ff360cc11001fd630cc11001ff230cc11001fd430cc11001ff220cc11008df7764c11000df6764c110095f5764c11000df4764c110005f7754c11000777754c11000577754c110025f6754c110005f5754c110025f4754c11000774754c11002574754c110005f7744c110007b7744c110005b7744c110005f6744c110005f5744c110005f4744c110007b4744c110005b4744c11001df
  | 2 => 0x5f57610d10005f47610d10005f77510d10025f67510d10005f57510d10025f47510d1012df67310d10007d76310d10007d46310d10007d65310d10007d55310d10007d64310d10007d54310d10007954310d1015df67210d10005f57210d1001df67010d10007f27010d1001df27010d10005f57010d10007f17010d10005f17010d1001df47010d1011ef76010d1011ff36010d101a7d63010d101a7d43010d10025f675d8910005f575d8910025f475d8910005f673d8910005f573d8910007e752d8910007e452d8910057f370d8910056f760d8910057f360d8910025f67598910005f5759891015df47598910005f67398910005f57398910006f66398910006f46398910035f6729891015ef76298910007e76298910045f5709891015ff17098910045f17098910066f76098910067f36098910005f77558910007777558910005777558910025f67558910025f47558910007747558910025747558910005f77358910007d77358910005d77358910005f47358910007d47358910005d47358910007e7625891015ef66258910065f77058910007f37058910065f37058910046f76058910047f36058910055f67618910025f6751891015f767518910025767518910005f5751891015f75751891000575751891015df47518910005f6731891015fd67318910005d67318910005f5731891015fd57318910005d57318910006f66318910006f4631891015ef7621891015fe6621891015ef56218910007e56218910007e7521891015fe45218910037f17018910036f76018910037f3601891015df77694910005f67694910005f5769491015df4769491010df57594910007776594910027746594910005f6739491015fd67394910005d67394910005f5739491015fd57394910005d5739491002777539491000775539491019df6729491015f775294910027e7529491015fe4529491001df6709491015ff2709491001df27094910005f5709491015ff17094910005f1709491001df47094910116f76094910117f36094910197765094910197745094910005f77654910005f67654910005f57654910005f47654910115f77554910027766554910007756554910005f77354910005f4735491000776535491002774535491018df77254910027e7525491015f76525491015f745254910027e45254910005f7705491001df6705491001df4705491010ef7605491010ff36054910027775054910005f776cc910005f676cc910005f576cc910005f476cc910005f775cc910025f675cc9100077675cc9100257675cc910005f575cc9100077575cc9100057575cc910025f475cc910005f674cc910005f574cc910005f474cc910007d663cc910007d563cc910187d753cc910187d453cc910007d743cc910007d443cc910007e762c
  | 3 => 0x360595101cf7650595101cf745059510025f675d8d10005f575d8d10025f475d8d10005f674d8d10005f574d8d10007d753d8d10007d453d8d1015df672d8d10005f572d8d100a6f760d8d100a7f360d8d10025f67598d10005f57598d10025f47598d10005f67498d10005f57498d10075f67398d10006f76398d10007d76398d1015df67298d10005f57298d10095f57098d10007f17098d10095f17098d1008ef76098d1008ff36098d10005f77558d10007777558d10005777558d10025f67558d10025f47558d10007747558d10025747558d10005f77458d10007b77458d10005b77458d10005f47458d10007b47458d10005b47458d10007d76358d10006f66358d10005f77258d10007e77258d10005e77258d1015df47258d10007e47258d10005e47258d1008df77058d10007f37058d1008df37058d10096f76058d10097f36058d100a5f67618d10025f67518d10007767518d10025767518d10005f57518d10007757518d10005757518d10025f47518d10005f67418d10005f57418d10006f76318d10007d66318d10006f56318d10007d56318d10007d75318d10007d45318d1015df67218d10005f57218d10076f76018d10077f36018d10005f77694d10005f67694d10005f57694d10005f47694d1014df57594d10007776594d10027746594d10005f67494d10005f57494d10027775494d101c5f67394d10027775394d10027d75394d10027575394d10027d45394d1015df67294d10005f57294d10027775294d1001df67094d10005f57094d1001df47094d10156f76094d10157f36094d101bf765094d101bf745094d10005f77654d10005f67654d10005f57654d10005f47654d10155f77554d10027766554d10007756554d10005f77454d10005f47454d10007765454d10027745454d101b5f77354d10027d75354d10007765354d10027745354d10027d45354d10005f77254d1015df47254d10027745254d10005f77054d1001df67054d1001df47054d1014ef76054d1014ff36054d10027775054d10005f77690d10005f67690d10005f57690d10005f47690d10005f77590d10025f67590d10007767590d10025767590d10005f57590d10007757590d10005757590d10025f47590d10135f57490d10007b76490d10007b46490d10007b65490d10007b55490d1011df67390d10007d74390d1015df67290d10005f57290d1001df67090d10005f57090d1001df47090d1012ef76090d1012ff36090d101afb64090d101afb44090d10005f77650d10005f67650d10005f57650d10005f47650d10005f77550d10025f67550d10005f57550d10025f47550d10007b64350d10005f77250d1015df47250d10005f77050d1001df67050d1001df47050d10136f76050d10137f36050d10005f77610d10005f67610d10
  | 4 => 0x8c20006dc4158c2002edf2158c2002ede2158c2002edd2158c2002edc2158c2001edf7058c2001ede7058c2001edd7058c2001edc7058c2001edf5058c2001ede5058c2001edd5058c2001edc5058c2001edf4058c2001ede4058c2001edd4058c2001edc4058c2001edf2058c2001ecf2058c2001ede2058c2001edd2058c2001ecd2058c2001edc2058c2001edf1058c2001ed71058c2001ede1058c2001edd1058c2001ed51058c2001edc1058c2007cff7694c2001cfe7694c20004fd7694c2001cfc7694c200167e6594c200067d6594c20006be6494c20006bd6494c2007ede6394c20006dd6394c2003f5f5394c20156f66194c20004ff7654c2001cfe7654c20004fd7654c2001cfc7654c200167e6554c200067d6554c20006be6454c20006bd6454c20006de6354c20006dd6354c2014ef66154c2007cff7690c2001cfe7690c20004fd7690c2001cfc7690c2003d7e7590c200057d7590c201467e6590c200067d6590c20006be6490c20006bd6490c2007ede6390c20006dd6390c2012ef66190c20004ff7650c2001cfe7650c20004fd7650c2001cfc7650c2013e7e6550c200067d6550c20006de6350c20006dd6350c20136f66150c2007cff7610c2001cfe7610c20004fd7610c2001cfc7610c201267e6510c200067d6510c2007ede6310c20006dd6310c200079d4310c2011ef66110c20006f77558420006f67558420006f57558420006f47558420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f64358420006f54358420006f4435842002ef7725842002ef6725842002ef5725842002ef4725842002ef7525842002ef6525842002ef5525842002ef4525842002ef7325842002ef6325842002ef5325842002ef4325842001ef7705842001cf7705842001ef6705842001ef5705842001cf5705842001ef4705842001ef7505842001ef6505842001ef5505842001ef4505842001ef7305842001ef6305842001ef5305842001ef4305842001ef7205842001ef6205842001ef2205842001ef5205842002ef1205842001ef420584201d5f676d9510026f665d95100277665d95100267665d9510026f465d9510005f673d9510005f573d95100277453d951015df672d9510005f572d95100277452d951001df670d951000df570d95100c6f760d95100c7f360d95100277750d95100c5f77559510007776559510026f66559510026f46559510027746559510005f77359510007d77359510005d77359510005f47359510007d47359510005d47359510027775359510005f77259510007e77259510005e7725951015df47259510007e47259510005e47259510027775259510175f77059510007f37059510175f370595100bef760595100bff
  | 5 => 0x1e7d705942001e7c705942001e7f305942001e7e305942001e7d305942001e7c305942001e7f205942001e6f205942001e7e205942001e7d205942001e6d205942001e7c205942001e7f105942001e77105942001e7e105942001e7d105942001e75105942001e7c1059420014fe7598c20004fd7598c2007cfc7598c201dcfe7498c20004fd7498c2001cfe7398c2001ede7398c20006df5398c2007edc5398c2002cfe7298c2002cfc7298c2002ede3298c2002edc3298c2007cff7198c2000cfe7198c20004fd7198c2000cfc7198c2007edf3198c20006de3198c20006dd3198c2007edc3198c2001cfe7098c2001cfc7098c2001ede3098c2001edc3098c2001ef71098c2001ef51098c2007edf7598c20006de7598c20006dd7598c2007edc7598c2007edf7498c20006de7498c20006dd7498c2007edc7498c20006df5498c20006dc5498c2002edf7298c2002ede7298c2002edd7298c2002edc7298c2002edf5298c2002ede5298c2002edd5298c2002edc5298c2002edf4298c2002ede4298c2002edd4298c2002edc4298c2007edf7198c20006de7198c20006dd7198c2007edc7198c20006df5198c20006de5198c20006dd5198c20006dc5198c20006df4198c20006de4198c20006dd4198c20006dc4198c2002edf2198c2002ede2198c2002edd2198c2002edc2198c2001edf7098c2001ede7098c2001edd7098c2001edc7098c2001edf5098c2001ede5098c2001edd5098c2001edc5098c2001edf4098c2001ede4098c2001edd4098c2001edc4098c2001edf2098c2001ede2098c2001edd2098c2001edc2098c2001edf1098c2001ed71098c2001ede1098c2001edd1098c2001ed51098c2001edc1098c20004ff7558c20014fe7558c20014fc7558c20004ff7458c201dcfc7458c2001cff7358c2001edf7358c20006df5358c20006dc5358c2002cff7258c2002cfe7258c2002cfd7258c2002cfc7258c2002ede3258c2002edc3258c20004ff7158c2000cfe7158c20004fd7158c2000cfc7158c20006df3158c20006de3158c20006dd3158c20006dc3158c2001cff7058c2001cfe7058c2001cfd7058c2001cfc7058c2001ede3058c2001edc3058c2001eef2058c2001eed2058c2001ef71058c2001ef51058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006dc5458c2002edf7258c2002ede7258c2002edd7258c2002edc7258c2002edf5258c2002ede5258c2002edd5258c2002edc5258c2002edf4258c2002ede4258c2002edd4258c2002edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dd5158c20006dc5158c20006df4158c20006de4158c20006dd415
  | 6 => 0xb705492001dee705492001dec7054920007e8705492002eef605492002feb605492004f6f5054920207e71054920207ea1054920207e9105492001cfe76cc92004d7e75cc9200057d75cc9200067f65cc9201067c65cc920006df63cc92007edc63cc92001dfa70cc920005f970cc920005ee768c92002eee768c92002def758c92002f6e758c920005ed758c92002f6d758c9200056d758c9200076f658c9200076c658c92002def748c92002fae748c920005ed748c92002fad748c920005ad748c9201fded738c92007eee638c92007eec638c92001dee708c92001dec708c92002eef608c92002feb608c9201f7e7108c9201f7ea108c9201f7e9108c92001cfc764c9200067f654c9200ee7c654c920006df634c920006dc634c92002fcc324c920005f7714c920045f4714c920005fb704c92001df8704c92001dec764c920006ec764c92001cec764c920005ef754c920005ed754c9200076f654c9200076c654c920005ef744c920005ed744c92002def734c92002fcf734c920007cf634c92007eee634c92007eec634c920007cc634c9201efcf534c9201efcc534c920007cf434c920007cc434c920007e7714c9201e7e4714c9201e7cf314c9201e7cd314c920007eb704c92001dee704c92001dec704c920007e8704c92002eef604c92002feb604c9201e7e7104c9201e7ea104c9201e7e9104c920014ff765412004cfd765412002cfc76541200067f65541200167c6554120005ef725412002dec72541200076d525412002cfe76cc1200067f65cc1200b67c65cc120006df63cc12007edc63cc12002dee72cc120005ed72cc120007cd32cc12007cff764c120004fd764c12002cfc764c1200057f754c12004d7c754c1200067f654c12009e7c654c120005bf744c120005bc744c120006df634c120006dc634c120005ef724c12002dec724c120007cd324c12001cff755942001e7f7559420004ff735942007cfc735942003e7f535942003e7c535942002cff725942002cfe725942002cfd725942002cfc725942002e7e525942002e7c5259420004ff715942000cfe7159420004fd715942000cfc715942003e7f51594200067e51594200067d515942003e7c515942001cff705942001cfe705942001cfd705942001cfc705942001e7e505942001e7c505942001eef205942001eed205942001ef7105942001ef510594200067f73594200067e73594200067d73594200067c735942002e7f725942002e7e725942002e7d725942002e7c725942002e7f325942002e7e325942002e7d325942002e7c32594200067f71594200067e71594200067d71594200067c71594200067f31594200067e31594200067d31594200067c315942002e7f215942002e7e215942002e7d215942002e7c215942001e7f705942001e7e7059420
  | 7 => 0x8d20006dc31d8d20006f710d8d2004d7e7598d200057d7598d200067f6598d200067c6598d20006df6398d20014fe7598d2007e7e7598d200147e7598d20004fd7598d2007e7d7598d200047d7598d2007cfc7598d201dcfe7498d20004fd7498d2007cfe7398d20004fd7298d2007eed7298d2007cff7198d2000cfe7198d20004fd7198d2000cfc7198d20004fd7098d2007ef97098d20006f71098d200057f7558d2004d7c7558d200067f6558d200067c6558d20005bf7458d20005bc7458d20005f77158d20045f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d201dcfc7458d20006bc7458d20004bc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d20004fd7158d2000cfc7158d20006f47158d2000cf47158d20004ff7058d20006fb7058d20006f71058d20004fe7618d200067f6518d200067c6518d20006dd6318d20014fe7518d20004fd7518d2007cfc7518d201dcfe7418d20004fd7418d2007ede7318d2002cfe7218d2007eed7218d2002cfc7218d2007cff7118d2000cfe7118d20004fd7118d2000cfc7118d20006de3118d2007edc3118d2001cfe7018d2001cfc7018d20006f71018d2007cff7694d20004fe7694d20004fd7694d2007cfc7694d200067f6594d200167c6594d2004f5f5394d2002dee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200167c6554d2007cff7690d20004fe7690d20004fd7690d2007cfc7690d2004d7e7590d200057d7590d200067f6590d201467c6590d20006bf6490d20006bc6490d2002dee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2013e7c6550d2007cff7610d20004fe7610d20004fd7610d2007cfc7610d200067f6510d201267c6510d20006df6310d2007edc6310d200079d4310d2002dee7210d20005ed7210d20005ee769492002eee769492004ded75949200076f6594920016ee6594920016ec659492004f6c65949200166c659492002fce7394920005ed739492002fcd7394920005cd739492004f6f53949200076d539492001dee709492001dec709492002eef609492002feb60949201976e50949201976c509492020fe7109492020fea109492020fe9109492001cfc76549200067f65549200167c655492002f6c5254920005fb705492001df8705492001dec7654920016ec765492001cec765492002def755492002f6f75549200076f6554920016ee6554920016ec655492004f6c6554920005ef73549200076e535492004f6c535492004f6f51549202076d5154920007e
  | 8 => 0x7ede63cca20006dd63cca200def661cca2001dfa70cca20005f970cca20006de634ca20006dd634ca20005f7714ca20055f4714ca200e6f6614ca20005fb704ca2001df8704ca20006f77558620006f67558620006f57558620006f47558620006f77358620006f67358620006f57358620006f47358620006f75358620006f65358620006f55358620006f45358620006f64358620006f54358620006f44358620056f77258620056f67258620006f57258620056f47258620006f7525862015ef65258620006f5525862015ef45258620006f7325862015ef63258620006f5325862015ef4325862001ef7705862001ef6705862001ef5705862001ef4705862001ef7505862001ef6505862001ef5505862001ef4505862001ef7305862001ef6305862001ef5305862001ef4305862001ef7205862001ef6205862001ef5205862001ef42058620014fe76d952004e7e65d952007cfe73d9520004fd73d952004e7f53d952004e7c53d952002cfe72d952001cfd72d952002cfc72d952004e7f52d9520004ff71d952000cfe71d9520004fd71d952000cfc71d952004e7f51d95200067e51d95200067d51d952004e7c51d952001cfe70d952002cfd70d952001cfc70d952004e7f50d9520006f710d952004d7e76d95200147e76d95201976f72d95200067f61d95200067e61d95200067d61d95200067c61d95202277b20d95201976e20d95201976c20d95202277820d95200077710d95200077a10d95200077910d95200067f73d95200067e73d95200067d73d95200067c73d95201967f72d95202267e72d95200067d72d95202267c72d95202267e32d95202267c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d95202267f21d95200067e21d95200067d21d95202267c21d95202267f70d95201967e70d95200067d70d95201967c70d95201967e30d95201967c30d95202267f20d95201967e20d95201967c20d95200067f10d95200067710d95201967e10d95200067d10d95201967c10d952004e7c655952004cff75595200067f7559520004ff735952007cfc735952005cff7259520006ef7259520004ff715952000cfe7159520004fd715952000cfc715952006cff7059520006fb7059520006f710595200057e761952004e7e76195200047e761952004f6d721952021e7f62195200067f61195200067e61195200067d61195200067c61195202167f60195202177b201952021f6e201952021f6c20195202177820195200077710195200077a10195200077910195200067f65d8d200067c65d8d20014fe75d8d20004fd75d8d20014fc75d8d201dcfe74d8d20004fd74d8d20004ff71d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d
  | 9 => 0xf7654b2003eef7654b2002f6f7554b2002f6f6554b20016ee6554b2002eec6554b2002f6c6554b20005ef7354b200076e5354b2006f6c5354b2006f6f5154b2023f6d5154b2001dee7054b2001dec7054b2006f6f5054b2023fe71054b2002def764cb20006ef764cb20005ef754cb20005ed754cb20005ef744cb20005ed744cb2002fcf734cb2002fcf634cb2007eee634cb2002eec634cb2002fcc634cb20237cf534cb20237cc534cb20007cf434cb20007cc434cb20007e7714cb2022fe4714cb2022fcf314cb2022fcd314cb2001dee704cb2001dec704cb2022fe7104cb20014ff765432002cfc76543200167e65543200067d6554320005ef725432002dec72543200076d525432001fea205432007ede63cc320006dd63cc32002dee72cc320005ed72cc320007cd32cc3200057f754c32006d7c754c320005bf744c320005bc744c320006de634c320006dd634c320005ef724c32002dec724c320007cd324c32001e7f7559620004ff735962007cfc735962005e7f535962005e7f5259620004ff715962000cfe7159620004fd715962000cfc715962001cfc705962001e7e505962001e7c505962001eef205962001eed205962001ef7105962001ef51059620014fe7598e20004fd7598e2007cfc7598e201dcfe7498e20004fd7498e2001ede7398e2007cff7198e2000cfe7198e20004fd7198e2000cfc7198e2001cfe7098e2001ede3098e2001edc3098e2001ef71098e2001ef51098e20004ff7558e200067f7558e200047f7558e20014fe7558e20014fc7558e200067c7558e200147c7558e20004ff7458e20006bf7458e20004bf7458e201dcfc7458e20006bc7458e20004bc7458e2001edf7358e20004ff7158e2000cfe7158e20004fd7158e2000cfc7158e2001cfc7058e2001ede3058e2001edc3058e2001eef2058e2001eed2058e2001ef71058e2001ef51058e2007cff7694e2001cfe7694e20004fd7694e2001cfc7694e201be7f6594e200167c6594e2007ede6394e20006dd6394e2005f5f5394e20156f66194e20004ff7654e2001cfe7654e20004fd7654e2001cfc7654e200167e6554e200067d6554e20006de6354e20006dd6354e2014ef66154e2007cff7690e2001cfe7690e20004fd7690e2001cfc7690e2005d7e7590e200057d7590e201aebf6490e201aebc6490e2007ede6390e20006dd6390e2012ef66190e20004ff7650e2001cfe7650e20004fd7650e2001cfc7650e20006de6350e20006dd6350e20136f66150e2007cff7610e2001cfe7610e20004fd7610e2001cfc7610e201a6df6310e2007edc6310e200079d4310e2011ef66110e20014ff7654a2001cfc7654a200167e6554a200067d6554a2010ef66154a20005fb7054a2001df87054a2002feb2054a2005d7e75cca200057d75cca20
  | 10 => 0x8430076f7735843007ef67358430076f5735843007ef47358430006f7535843007ef65358430006f5535843007ef45358430006f7435843007ef64358430006f5435843007ef44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f4425843007ef73258430006f63258430006f5325843007ef4325843001ef7705843001ef6705843001ef5705843001ef4705843001ef7505843001ef6505843001ef5505843001ef4505843001ef7405843001ef6405843001ef5405843001ef4405843001ef7305843001ef6305843001ef5305843001ef4305843001ef7205843001ef6205843001ef5205843001ef4205843001dfb764c030006fb764c030004fb764c0300077b754c03000778754c03001f7a654c03001f79654c030007bb744c030007b8744c03001fba644c03001fb9644c03001dfb734c03001fdb734c03007efa634c03001fda634c03001fea624c03001fe9624c03001ff2614c03001ff1614c03002e7f7559720004ff735972007cfc735972006e7c535972001cfc725972002e7e525972002e7c5259720004ff715972000cfe7159720004fd715972000cfc715972006e7f51597200067d515972006e7f5059720006f71059720014fe7598f2007e7e7598f200147e7598f20004fd7598f2007e7d7598f200047d7598f2007cfc7598f201dcfe7498f20004fd7498f2002ede7398f20006df5398f2007edc5398f2001cfe7298f2002eee7298f2001cee7298f2002ede3298f2002eee3298f2002edc3298f2007cff7198f2000cfe7198f20004fd7198f2000cfc7198f2007edf3198f20006dd3198f20006f71098f20004ff7558f20014fe7558f20014fc7558f20004ff7458f201dcfc7458f2002edf7358f20006df5358f20006dc5358f2001cfc7258f2002ede3258f2002edc3258f20004ff7158f20006f77158f20004f77158f2000cfe7158f20004fd7158f2000cfc7158f20006f47158f2000cf47158f20006df3158f20006dd3158f20006f71058f2007cff7694f2002cfe7694f20004fd7694f2002cfc7694f200167e6594f200067d6594f2006f5f5394f2002dee7294f20005ed7294f20004ff7654f2002cfe7654f20004fd7654f2002cfc7654f202467f6554f200167c6554f2002dee7254f202476e5254f2007cff7690f2002cfe7690f20004fd7690f2002cfc7690f2006d7e7590f200057d7590f20006be6490f20006bd6490f2002dee7290f20005ed7290f20004ff7650f2002cfe7650f20004fd7650f2002cfc7650f2002dee7250f2007cff7610f2002cfe7610f20004fd7610f2002cfc7610f2007ede6310f20006dd6310f200079d4310f2002dee7210f20005ed7210f2002de
  | 11 => 0x6ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883007eee7358830006ef535883007eee5358830006ed535883007eec5358830006ef4358830006cf435883007eee4358830006ed435883007eec4358830006cc4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ed5158830006ec5158830006ef4158830006ee4158830006ed4158830006ec415883007eef3158830006ee3158830006ed315883007eec315883001eef705883001eee705883001eec705883001eef505883001eee505883001eed505883001eec505883001eef405883001eee405883001eed405883001eec405883001eef305883001ecf305883001eee305883001eed305883001ecd305883001eec305883001eef105883001ee7105883001eee105883001eed105883001ee5105883001eec105883002cff769483001cfe7694830004fd76948300167e65948300067d6594830005be7494830005bd7494830006be6494830006bd649483007dde7394830005dd739483002eee6294830006ed6294830116f66194830004ff7654830004fd765483001cfc76548300167e65548300067d6554830006be6454830006bd645483002eee6254830006ed625483010ef661548301dcff76d083001cfe76d0830004fd76d08300857e75d08300057d75d083028e7e65d08300067d65d08301debe64d0830006bd64d08300079c43d083002eee62d0830006ed62d0830286f661d083002cff769083001cfe7690830004fd76908300857e75908300057d759083027e7e65908300067d6590830006be6490830006bd649083007dde7390830005dd739083002eee6290830006ed6290830276f66190830004ff7650830004fd765083001cfc765083026e7e65508300067d6550830006be6450830006bd6450830005df735083007ddc73508300079c435083002eee6250830006ed6250830005f77150830075f47150830266f6615083002cff761083001cfe7610830004fd761083025e7e65108300067d65108301debe6410830006bd641083002eee6210830006ed6210830256f66110830004fd768c8300857e758c8300057d758c8300fe7e658c8300067d658c830005be748c830005bd748c830006be648c830006bd648c83002eee628c830006ed628c8300f6f6618c830004ff764c8300ee7e654c8300067d654c830006be644c830006bd644c83024ede634c83002eee624c830005f7714c830075f4714c8300e6f6614c830006f77558430006f67558430006f57558430006f47558430006f77458430006f67458430006f57458430006f47458430006f75458430006f65458430006f55458430006f4545
  | 12 => 0xf735503007ddc73550302b6f661550300b4ff7654c300167e6554c300067d6554c30006be6454c30006bd6454c300b6de6354c3014ef66154c30004fd76d0c300857e75d0c300057d75d0c302ae7e65d0c300067d65d0c301debe64d0c30006bd64d0c302a6f661d0c30295dd76d0c30006dd76d0c30004dd76d0c300075e75d0c300075d75d0c30296df65d0c302975e65d0c30006dd65d0c302975d65d0c300065d65d0c3007dde74d0c30296df64d0c302979e64d0c30006dd64d0c302979d64d0c300069d64d0c30297ce62d0c30297cd62d0c30297d661d0c30297d561d0c30295df70d0c30295dd70d0c30296de60d0c30297da60d0c302979f40d0c302979d40d0c30297d710d0c30004ff7650c3013e7e6550c300067d6550c30006be6450c30006bd6450c3029ede6350c3007f9c4350c30136f66150c3007ddd7610c3007edd7610c30004dd7610c3007edf6510c3007f5e6510c30006dd6510c3007f5d6510c300065d6510c30295de7410c3007f9e7410c3007edf6410c3007f9e6410c30006dd6410c3007f9d6410c300069d6410c300079e5410c300079d5410c3007fce6210c3007fcd6210c3007fd66110c3007fd56110c3007ddf7010c3007fda7010c301a5dd7010c3007fd97010c301a6de6010c3007fda6010c301a79e4010c301a79c4010c301a7d71010c3002eef759883002eee759883002eed759883002eec759883002eef749883002eee749883002eed749883002eec7498830006ef5498830006ee5498830006ed5498830006ec549883002eec7398830006ef539883007eee5398830006ed539883007eec5398830006ef439883007eee4398830006ed439883007eec439883002eef719883002eee719883002eed719883002eec7198830006ef5198830006ee5198830006ed5198830006ec5198830006ef4198830006ee4198830006ed4198830006ec419883007eef3198830006ee3198830006ed319883007eec319883001eef709883001eee709883001eed709883001eec709883001eef509883001eee509883001eed509883001eec509883001eef409883001eee409883001eed409883001eec409883001eef309883001eee309883001eed309883001eec309883001eef109883001ee7109883001eee109883001eed109883001ee5109883001eec1098830004ff7558830014fe7558830014fc7558830004ff74588301dcfc7458830006df4358830006dc435883001eef7258830006ef5258830006ec525883007eef325883007eec3258830004ff715883000cfe7158830004fd715883000cfc7158830006ef2158830006ee2158830006ed2158830006ec215883001cff705883001cfd705883001edf305883001edd305883001eee205883001eec205883001ef7105883001ef51058830006ef7558830
  | 13 => 0x9030006bd41990301debc419903001cfe709903001ebe409903001ebc409903001ef7109903001ef510990301debf7599030006be7599030006bd75990301debc759903007ebe739903007ebc7399030006bf539903007ebe539903007ebc53990301debf7299030006be7299030006bd72990301debc7299030006bf5299030006bc529903007ebf329903007ebc32990301debf7199030006be7199030006bd71990301debc7199030006bf5199030006be5199030006bd5199030006bc519903007ebf3199030006be3199030006bd319903007ebc3199030006bf2199030006be2199030006bd2199030006bc219903001ebf709903001ebe709903001ebd709903001ebc709903001ebf509903001ebe509903001ebd509903001ebc509903001ebf309903001ebe309903001ebd309903001ebc309903001ebf209903001ebe209903001ebd209903001ebc209903001ebf109903001eb7109903001ebe109903001ebd109903001eb5109903001ebc1099030004ff7559030014fe7559030014fc755903001cff745903001ebf7459030006bf5459030006bc54590301dcff735903007cfe7359030134fd735903007cfc7359030006dc735903007ebe435903007ebc4359030004ff725903002cfc7259030004ff715903000cfe7159030004fd715903000cfc7159030006bf4159030006be4159030006bd4159030006bc415903001cfe705903001cfc705903001ebe405903001ebc405903001edf305903001edd305903001ef7105903001ef51059030006bf7559030006be7559030006bd7559030006bc755903007ebe735903007ebc73590300069c7359030006bf535903007ebe535903007ebc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006bc525903007ebf325903007ebc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006bd5159030006bc515903007ebf3159030006be3159030006bd315903007ebc3159030006bf2159030006be2159030006bd2159030006bc215903001ebf705903001ebe705903001ebd705903001ebc705903001ebf505903001ebe505903001ebd505903001ebc505903001ebf305903001e9f305903001ebe305903001ebd305903001e9d305903001ebc305903001ebf205903001ebe205903001ebd205903001ebc205903001ebf105903001eb7105903001ebe105903001ebd105903001eb5105903001ebc10590301dcff769503001cfe7695030004fd769503001cfc76950300167e65950300067d65950301debe6495030006bd64950300873f54950302bef66195030004ff765503001cfe7655030004fd765503001cfc76550300167e65550300067d6555030006be6455030006bd6455030005d
  | 14 => 0x2ede624c93002edc624c930007cc624c930007d7714c9302e7d4714c9302e6df614c9302e6dd614c930007db704c93001dde704c93001ddc704c930007d8704c9302e7d7104c930004fe760c9300067f650c9300d67c650c930006bf640c930006bc640c9302ddde730c930007cd320c930014ff765413009cfd7654130014fc76541300067f65541300167c6554130006bf6454130006bc6454130005df7354130005dc73541300075d5354130004fe76d01300067f65d01302d67c65d0130006bf64d01301debc64d0130005de73d0130005dd73d01300079d43d0130004fd7650130004fc76501300067f65501302ce7c6550130005df7350130005dc73501300079d43501300067f65cc1300b67c65cc130006bf64cc130006bc64cc13001dde73cc13001edf63cc1302c7f310cc13001cfa76cc1300077b65cc1300077865cc130007bb64cc130007b864cc13001dfa73cc13001efb63cc13001fdb63cc13007fda53cc130007d953cc13007fda43cc130007d943cc13007fdb32cc130007d932cc13001cff755943001e7f7559430004ff74594301dcfc74594300867f54594300867c5459430014ff735943007cfe7359430014fd735943007cfc735943007e7e535943007e7c5359430004ff725943002cfc72594300867f52594300867c5259430004ff715943000cfe7159430004fd715943000cfc71594300867f51594300067e51594300067d51594300867c515943001cfe705943001cfc705943001e7e505943001e7c505943001edf305943001edd305943001ef7105943001ef510594300067f74594300067e74594300067d74594300067c74594300867f735943007e7e735943007e7c735943007e7e435943007e7c43594300067f72594300067e72594300067d72594300067c725943007e7f325943007e7c32594300067f71594300067e71594300067d71594300067c71594300067f41594300067e41594300067d41594300067c415943007e7f31594300067e31594300067d315943007e7c31594300067f21594300067e21594300067d21594300067c215943001e7f705943001e7e705943001e7d705943001e7c705943001e7f405943001e7e405943001e7d405943001e7c405943001e7f305943001e5f305943001e7e305943001e7d305943001e5d305943001e7c305943001e7f205943001e7e205943001e7d205943001e7c205943001e7f105943001e77105943001e7e105943001e7d105943001e75105943001e7c1059430014fe7599030004fd75990301dcfc759903001cfe749903001ebe7499030006bf54990301debc549903007cfe739903007cfc739903007ebe439903007ebc439903002cfe7299030004fd72990301dcff719903000cfe7199030004fd719903000cfc71990301debf4199030006be419
  | 15 => 0xe71d8930004fd71d893000cfc71d8930006ee21d8930006ec21d893001cfe70d893001cfc70d8930006f710d893009d7e75989300057d75989300067f65989300067c6598930005be7498930005bd7498930006bf6498930006bc6498930006ef62989300057f755893009d7c75589300067f65589300067c6558930005bf7458930005bc7458930006bf6458930006bc6458930005f77158930095f471589300067f65189300067c6518930006bf6418930006bc641893002eee6218930006ed6218930004fe7694930004fd769493002cfc76949300067f65949300167c6594930005be7494930005bd7494930006bf6494930006bc6494930005de7394930005dd73949300075d5394930004ff7654930004fe7654930004fc76549300067f65549300167c6554930006bf6454930006bc64549300075e5354930004fe76d0930004fd76d09301dcfc76d093009d7e75d09300057d75d09300067f65d093028e7c65d0930006bf64d09301debc64d0930005de73d0930005dd73d09300079e43d0930004fe7690930004fd769093002cfc769093009d7e75909300057d75909300067f659093027e7c6590930006bf6490930006bc6490930005de7390930005dd7390930004ff7650930004fe7650930004fc76509300067f655093026e7c6550930006bf6450930006bc64509300079e4350930005f77150930095f47150930004fe7610930004fd761093002cfc76109300067f651093025e7c6510930006bf64109301debc6410930005de7310930005dd7310930004fe76cc93009d7e75cc9300057d75cc9300067f65cc9301067c65cc930006bf64cc930006bc64cc930005de76cc930006de76cc930005df75cc9300075e75cc930005dd75cc9300075d75cc9300055d75cc9300075f65cc930106de65cc930106dc65cc9300075c65cc9301065c65cc930005df74cc930005dd74cc9300079f64cc930006de64cc930006dc64cc9300079c64cc9300069c64cc93002ede62cc93002edc62cc9302f6df61cc9302f6dd61cc93001dde70cc93001ddc70cc93007edf60cc9302f7d710cc93001cfe768c93009d7e758c9300057d758c9300067f658c9300fe7c658c930005be748c930005bd748c930006bf648c930006bc648c9302eddd738c930006ef628c93002eec628c93001dfa708c930005f9708c93001cfc764c9300067f654c9300ee7c654c930006bf644c930006bc644c930006ef624c93002eec624c930005f7714c930095f4714c930005fb704c93001df8704c93001cdc764c930005df754c930005dd754c9300075f654c9300eede654c9300eedc654c9300075c654c9300ee5c654c930005df744c930005dd744c9300079f644c930006de644c930006dc644c9300079c644c9300069c644c930007cf724c930007cf624c930
  | 16 => 0x91301a6bc2019130006bf1019130006b710191301a6be1019130006bd10191301a6bc10191301dcff7695130004fe7695130004fd76951301dcfc76951300067f65951300167c6595130006bf64951301debc649513009f3f5495130005de7395130005dd7395130004ff7655130004fe7655130004fd7655130004fc76551300067f65551300167c6555130006bf6455130006bc64551300acfe7694d300067f6594d300167c6594d30006bf6494d30006bc6494d3009f5f5394d30005de7694d300aede7694d3009ddd7594d300075f6594d30016de6594d30016dc6594d3009f5c6594d300165c6594d30005dd7494d300079f6494d30006de6494d30006dc6494d300079c6494d300069c6494d3009f5f5494d300075d5494d30005dd7294d3009f5f5294d3001dde7094d3001ddc7094d3007edf6094d301bf5e5094d301bf5c5094d30327d71094d3001cfc7654d300067f6554d300167c6554d30006bf6454d30006bc6454d3009f5c5354d30005fb7054d3001df87054d3001ddc7654d30016dc7654d3001cdc7654d3009ddf7554d300075f7554d300075f6554d30016de6554d30016dc6554d3009f5c6554d30005df7454d300079f6454d30006de6454d30006dc6454d300079c6454d300069c6454d300075e5454d3009f5c5454d30005df7254d3009f5c5254d3009f5f5154d3031f5d5154d30007db7054d3001dde7054d3001ddc7054d30007d87054d3009f5f5054d3031fd71054d3001cfe76d0d3009d7e75d0d300057d75d0d300067f65d0d302ae7c65d0d30006bf64d0d301debc64d0d3001dfa70d0d30005f970d0d30004fe7690d3009d7e7590d300057d7590d300067f6590d301467c6590d30006bf6490d30006bc6490d30005de7690d30006de7690d30004de7690d30005df7590d300075e7590d30005dd7590d300075d7590d300055d7590d300075f6590d300075c6590d30315dd7490d300079f6490d301dede6490d301dedc6490d300079c6490d300069c6490d300079e5490d300079d5490d30005dd7290d3001dde7090d3001ddc7090d3007edf6090d301af9e4090d3030fd71090d3001cfc7650d300067f6550d3013e7c6550d30006bf6450d30006bc6450d30005fb7050d3001df87050d3001cdc7650d30005df7550d30005dd7550d300075f6550d300075c6550d300079f7450d300079f6450d301dede6450d301dedc6450d300079c6450d300069c6450d30005df7250d30007db7050d3001dde7050d3001ddc7050d30007d87050d30307d71050d30004fe7610d300067f6510d301267c6510d30006bf6410d302fdde7310d300079d4310d300067f65d89300067c65d8930006bf64d8930006bc64d8930014fe75d8930004fd75d8930014fc75d89301dcfe74d8930004fd74d8930004ff71d893000cf
  | 17 => 0x6bc75d91301aebf73d9130006bd73d9130006bf53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006bc52d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130006bf31d9130006be31d9130006bd31d9130006bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d9130006bf70d91301aebe70d9130006bd70d91301aebc70d9130006bf50d91301aebe50d91301aebc50d91301aebe30d91301aebc30d91301aebe20d91301aebc20d9130006bf10d9130006b710d91301aebe10d9130006bd10d91301aebc10d913009d7e75991300057d75991300067f65991300067c6599130006bf6499130014fe75991301de7e75991300147e7599130004fd75991301de7d75991300047d75991301dcfc7599130004fd73991301dedd739913002cfe7299130004fd72991301dcff719913000cfe7199130004fd719913000cfc71991301def97099130296de3099130006f710991300057f755913009d7c75591300067f65591300067c6559130004ff75591300067f75591300047f7559130014fe7559130014fc75591300067c75591300147c7559130006df7359130004ff725913002cfc7259130004ff715913000cfe7159130004fd715913000cfc7159130004ff7059130006fb7059130006f71059130004fe76191300067f65191300067c6519130006bd6419130014fe7519130004fd75191301dcfc75191301debe7419130006bf54191301debc541913007cfc731913002cfe7219130004fd72191301dcff711913000cfe7119130004fd711913000cfc71191301debf4119130006be4119130006bd41191301debc41191301a6de30191301a6dc3019130006f71019130005be7619130006be7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c65191300079d7319130006bf6119130006be6119130006bd6119130006bc61191301a79e30191301a79c3019130007b710191301debf7519130006be7519130006bd75191301debc75191301debf7319130006bf5319130006bc53191301debf7219130006be7219130006bd72191301debc7219130006bf5219130006bc52191301debf7119130006be7119130006bd71191301debc7119130006bf5119130006be5119130006bd5119130006bc5119130006bf3119130006be3119130006bd3119130006bc3119130006bf2119130006be2119130006bd2119130006bc21191301debf70191301a6be7019130006bd7019130006bf50191301a6be50191301a6bc50191301a6be30191301a69e3019130006bd30191301a6bc30191301a69c30191301a6be201
  | 18 => 0x7505863001ef6505863001ef5505863001ef4505863001ef7405863001ef6405863001ef5405863001ef4405863001ef7305863001ef6305863001ef5305863001ef4305863001ef7205863001ef6205863001ef5205863001ef4205863001df976cc23007ef976cc23001fda73cc23007fda53cc230007d953cc23001ff261cc23001ff161cc230014fe76d953009e7e65d95301dcfe74d9530004fd74d953009e7f54d953009e7c54d953007cfe73d953001cfd73d953007cfc73d953009e7f53d953002cfe72d9530004fd72d953009e7f52d953009e7c52d9530004ff71d953000cfe71d9530004fd71d953000cfc71d953009e7f51d95300067e51d95300067d51d953009e7c51d953009cfd70d953009e7f50d9530006f710d953009d7e76d95300147e76d95301bf5f73d95300067f61d95300067e61d95300067d61d95300067c61d95301bf5e30d95301bf5c30d95300077710d95300067f74d95300067e74d95300067d74d95300067c74d95301be7f73d953009e7e73d95300067d73d95300067f72d95300067e72d95300067d72d95300067c72d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067f31d95300067e31d95300067d31d95300067c31d95300067f21d95300067e21d95300067d21d95300067c21d95300067f70d95301be7e70d95300067d70d95301be7c70d95301be7e40d95301be7c40d95301be7e30d95301be7c30d95301be7e20d95301be7c20d95300067f10d95300067710d95301be7e10d95300067d10d95301be7c10d953009e7c6559530005bf7459530005bc745953009cff75595300067f7559530004ff7459530006bf7459530004bf74595301dcfc7459530006bc7459530004bc74595300acff7359530006df7359530004ff725953002cfc7259530004ff715953000cfe7159530004fd715953000cfc71595300b4ff7059530006fb7059530006f710595300057e761953009e7e76195300047e761953009f5d731953032e7f63195300067f61195300067e61195300067d61195300067c611953032f5e301953032f5c30195300077710195300067f65d91300067c65d9130014fe75d9130004fd75d9130014fc75d9130006bf54d9130006bc54d913002cfe72d9130004fd72d9130004ff71d913000cfe71d9130004fd71d913000cfc71d9130006bf41d9130006be41d9130006bd41d9130006bc41d9130006f710d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91301af9f73d9130006bf61d9130006be61d9130006bd61d9130006bc61d91301af9e30d91301af9c30d9130007b710d9130006bf75d9130006be75d9130006bd75d9130
  | 19 => 0xe301aebf6490e3012ef66190e30006be6450e30006bd6450e30136f66150e30005fb7050e3001df87050e300079d4310e3011ef66110e301a5dd7610e30006dd7610e301a6df6510e30006dd6510e300079e7410e301a6df6410e301a79f6410e301a69f6410e30006dd6410e301a79c6410e300079e5410e300079d5410e301a7d66110e301a7d56110e301a5df7010e301a5dd7010e301a79e4010e301a7d71010e30004ff7558a300067f7558a300047f7558a30014fe7558a30014fc7558a300067c7558a300147c7558a30004ff7458a301dcfc7458a30006df4358a30006dc4358a3001eef7258a30004ff7158a3000cfe7158a30004fd7158a3000cfc7158a3001edf3058a3001edd3058a3001eee2058a3001eec2058a3001ef71058a3001ef51058a3002cff7694a3001cfe7694a30004fd7694a301967f6594a300167c6594a30005be7494a30005bd7494a30005de7394a30005dd7394a3002eee6294a30006ed6294a30116f66194a30004ff7654a30004fd7654a3001cfc7654a300167e6554a300067d6554a3002eee6254a30006ed6254a3010ef66154a301dcff76d0a3001cfe76d0a30004fd76d0a300ad7e75d0a300057d75d0a301debe64d0a30006bd64d0a300079c43d0a30286f661d0a3002cff7690a3001cfe7690a30004fd7690a300ad7e7590a300057d7590a30005de7390a30005dd7390a3002eee6290a30006ed6290a30276f66190a30004ff7650a30004fd7650a3001cfc7650a30006be6450a30006bd6450a30005df7350a30005dc7350a300079c4350a3002eee6250a30006ed6250a30005f77150a300a5f47150a30266f66150a3002cff7610a3001cfe7610a30004fd7610a30256f66110a300ad7e75cca300057d75cca300def661cca300ad7e758ca300057d758ca30005be748ca30005bd748ca3002eee628ca30006ed628ca300f6f6618ca3001dfa708ca30005f9708ca3002cff764ca3002eee624ca30006ed624ca30005f7714ca300a5f4714ca300e6f6614ca30005fb704ca3001df8704ca300cef6610ca30006f77558630006f67558630006f57558630006f47558630006f77458630006f67458630006f57458630006f47458630006f75458630006f65458630006f55458630006f454586300a6f773586300a6f67358630006f573586300a6f47358630006f75358630006f65358630006f55358630006f45358630006f74358630006f64358630006f54358630006f44358630006f77258630006f67258630006f57258630006f47258630006f75258630006f65258630006f55258630006f45258630006f74258630006f64258630006f54258630006f44258630006f73258630006f63258630006f53258630006f4325863001ef7705863001ef6705863001ef5705863001ef4705863001ef
  | 20 => 0x7f5e75ccb30005dd75ccb3007f5d75ccb300055d75ccb30106de65ccb3007edc65ccb3007ddf74ccb30005dd74ccb30006de64ccb3007edc64ccb3002ede62ccb3007fce62ccb3007fcd62ccb3002edc62ccb3007edf61ccb3033edd61ccb3001dde70ccb3007fda70ccb3007fd970ccb3001ddc70ccb3033fd710ccb300b57e758cb300057d758cb30005be748cb30005bd748cb3002eec628cb3007fcc324cb30005f7714cb3008df4714cb30005df764cb30006df764cb30005df754cb30005dd754cb300eede654cb300eedc654cb30005df744cb30005dd744cb30006de644cb30006dc644cb3007fcf724cb3007fcf624cb3002ede624cb3002edc624cb3007fcc624cb30007d7714cb3024fd4714cb3024edf614cb3024edd614cb3001dde704cb3001ddc704cb3024fd7104cb30014ff765433007cfc76543300167e65543300067d6554330005df735433007ddc73543300075d535433001fda305433007dde73d0330005dd73d03300079d43d033001e7f7559630004ff74596301dcfc74596300ae7f54596300ae7f5359630004ff725963002cfc72596300ae7f5259630004ff715963000cfe7159630004fd715963000cfc715963001cfc705963001e7e505963001e7c505963001edf305963001edd305963001ef7105963001ef51059630014fe7599230004fd75992301dcfc759923001ebe749923002cfe7299230004fd72992301dcff719923000cfe7199230004fd719923000cfc719923001cfe709923001ebe409923001ebc409923001ef7109923001ef51099230004ff75592300067f75592300047f7559230014fe7559230014fc75592300067c75592300147c755923001ebf7459230004ff725923002cfc7259230004ff715923000cfe7159230004fd715923000cfc715923001ebe405923001ebc405923001edf305923001edd305923001ef7105923001ef510592301dcff769523001cfe7695230004fd76952303367f65952300167c65952301debe6495230006bd64952300af3f54952302bef66195230004ff765523001cfe7655230004fd765523001cfc76552300167e65552300067d6555230006be6455230006bd6455230005df7355230005dc73552302b6f6615523009cfd7694e301be7f6594e300167c6594e300af5f5394e30156f66194e30014ff7654e3001cfc7654e300167e6554e300067d6554e3014ef66154e30005fb7054e3001df87054e300ad7e75d0e300057d75d0e301debe64d0e30006bd64d0e302a6f661d0e3001dfa70d0e30005f970d0e300075e75d0e300075d75d0e30296df65d0e30006dd65d0e302979e64d0e30006dd64d0e302979d64d0e30297d661d0e30297d561d0e30297da70d0e30295dd70d0e30007d970d0e302979f40d0e30297d710d0e300ad7e7590e300057d759
  | 21 => 0xf711933000cfe7119330004fd711933000cfc711933007ef97019330006f710193301dcff769533007cfe7695330004fd769533007cfc76953300167e65953300067d65953300b73f549533007dde7395330005dd7395330004ff7655330004fd765533007cfc76553300067f65553300167c655533001ddd7694f3007edd7694f3001cdd7694f30016de6594f3007f5e6594f300165e6594f3007f5d6594f3007edc6594f30005dd7494f30006de6494f3007edc6494f300b75f5494f300075d5494f30005dd7294f300b75f5294f3001dde7094f3007fda7094f3007fd97094f3001ddc7094f301bf5e5094f301bf5c5094f30357d71094f30084ff7654f3007e7f6554f3007e7c6554f3007f5c5354f30005df7654f30086df7654f3007f5f7554f3007f5f6554f30016de6554f30016dc6554f3007f5c6554f30005df7454f30006de6454f30006dc6454f300075e5454f300b75c5454f30005df7254f300b75c5254f300b75f5154f3034f5d5154f3001dde7054f3001ddc7054f300b75f5054f3034fd71054f300b57e75d0f300057d75d0f3001cdd7690f3007ddf7590f3007f5e7590f30005dd7590f3007f5d7590f300055d7590f301dede6490f3007f9e6490f3007f9d6490f3007edc6490f300079e5490f300079d5490f30005dd7290f3001dde7090f3007fda7090f3007fd97090f3001ddc7090f30347d71090f3007f9c4350f30005df7650f30006df7650f30005df7550f30005dd7550f3007f9f7450f3007f9f6450f301dede6450f301dedc6450f3007f9c6450f300069c6450f30005df7250f3001dde7050f3001ddc7050f3029fd71050f300b57e7598b300057d7598b30005be7498b30005bd7498b3007eef6298b3002eec6298b3007eec6258b30005f77158b3008df47158b30004ff7558b30014fe7558b30014fc7558b30004ff7458b301dcfc7458b3001cfc7358b3007eef3258b3007eec3258b30004ff7158b30006f77158b30004f77158b3000cfe7158b30004fd7158b3000cfc7158b30006f47158b3000cf47158b30006f71058b3002cff7694b3007cfe7694b30004fd7694b300167e6594b300067d6594b30005be7494b30005bd7494b3007dde7394b30005dd7394b300075d5394b30004ff7654b30004fd7654b3007cfc7654b300067f6554b300167c6554b300075e5354b301dcff76d0b3007cfe76d0b30004fd76d0b300b57e75d0b300057d75d0b3007dde73d0b30005dd73d0b300079e43d0b3002cff7690b3007cfe7690b30004fd7690b300b57e7590b300057d7590b3007dde7390b30005dd7390b30004ff7650b30004fd7650b3007cfc7650b300079e4350b30005f77150b3008df47150b3002cff7610b3007cfe7610b30004fd7610b3007dde7310b30005dd7310b3001cdd76ccb3007ddf75ccb30
  | 22 => 0x4d50004fe7690d50004fd7690d5007cfc7690d500157e7590d500057d7590d50006bf6490d50006bc6490d500073d5490d50004ff7650d50004fe7650d50004fc7650d500157e7550d500057d7550d50004fe7610d50004fd7610d5007cfc7610d500157e7510d500057d7510d50006df6310d5007edc6310d500075d5310d500079d4310d5001cfd75d895007cfe73d8950004fd73d895005eee52d895005eed52d8950004ff71d895000cfe71d8950004fd71d895000cfc71d8950006ee21d8950006ec21d8950006f710d89501967f6598950005de7398950005dd7398950006ef629895004df9709895006dfb705895021e7f651895002eee6218950006ed621895001c7c76549500057f73549500067c63549500157f72549500176f72549500076f625495002e7e625495002e7c62549500076c625495035e7f615495035e7d61549500077b705495001d7e705495001d7c70549500077870549500167f60549500177b605495035f771054950004fe76cc950004fd76cc95007cfc76cc9500157e75cc9500057d75cc950006df63cc95007edc63cc9501075f53cc950004fe768c950004fd768c95002cfc768c9500157e758c9500057d758c950005be748c950005bd748c950004ff764c950004fe764c950004fc764c9500157e754c9500057d754c950006df634c950006dc634c9500ef5f534c950005f7714c9500bdf4714c950004fe760c950004fd760c95002cfc760c9500157e750c9500057d750c9500b4fd75d97301dcfe74d9730004fd74d97300b67f54d973007ede73d973007e7f53d973002cfe72d9730004fd72d97300b67f52d973007cff71d973000cfe71d9730004fd71d973000cfc71d973007ef970d97301be7e50d97301be7c50d9730006f710d9730014ff765973007e7c655973007e7f7559730004ff74597301dcfc74597300b67c545973001cfc735973007e7e535973007e7c5359730004ff725973002cfc72597300b67c5259730004ff715973000cfe7159730004fd715973000cfc71597300b67f51597300067d51597300b67f5059730006f710597300b57e75993300057d759933007ebf6499330014fe75993301de7e75993300147e7599330004fd75993301de7d75993300047d75993301dcfc759933001cfe739933007ebe439933007ebc439933002cfe7299330004fd72993301dcff719933000cfe7199330004fd719933000cfc7199330296de3099330296dc3099330006f7109933007ebc6459330004ff7559330014fe7559330014fc755933001cfc735933007ebe435933007ebc4359330004ff725933002cfc7259330004ff715933000cfe7159330004fd715933000cfc7159330006f71059330014fe7519330004fd751933007cfc751933007ede731933002cfe7219330004fd721933007cf
  | 23 => 0xcfc7158a5004e7f5158a500067d5158a5001cfc7058a5001e7f5058a5001e7d5058a5001eee2058a5001eec2058a5001ef71058a5001ef51058a500057e7394a502275e7394a500055e7394a502275d7394a500067d6394a500157e7294a500176e7294a501967f6294a501976e6294a502267d6294a501976d6294a502257f7194a5036d7d7194a50197766194a50197756194a501977a7094a501957d7094a50227797094a500167e6094a500177a6094a501976f2094a50197771094a5007cff76cca5001cfe76cca50004fd76cca500157e75cca500057d75cca5007ede63cca50006dd63cca501075c53cca500def661cca5002cff768ca5001cfe768ca50004fd768ca500157e758ca500057d758ca50005be748ca50005bd748ca5002eee628ca50006ed628ca500f6f6618ca50004ff764ca50004fd764ca5001cfc764ca500057f754ca500157c754ca50006de634ca50006dd634ca500ef5c534ca5002eee624ca50006ed624ca50005f7714ca500c5f4714ca500e6f6614ca5002cff760ca5001cfe760ca50004fd760ca502257f750ca500157c750ca500cef6610ca500c6f775586500c6f67558650026f575586500c6f47558650006f77358650006f67358650006f57358650006f47358650026f75358650026f65358650026f55358650026f45358650006f64358650006f54358650006f44358650006f77258650006f67258650006f57258650006f47258650026f75258650026f65258650026f55258650026f45258650006f73258650006f63258650006f53258650006f4325865001ef7705865001ef6705865001ef5705865001ef4705865001ef7505865001ef6505865001ef5505865001ef4505865001ef7305865001ef6305865001ef5305865001ef4305865001ef7205865001ef6205865001ef5205865001ef4205865001cfd75d8d501dcfe74d8d50004fd74d8d500aede53d8d500aedd53d8d5002cfe72d8d50004fd72d8d50004ff71d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50006de31d8d50006dc31d8d50006f710d8d50006df6398d5009df97098d50005bf7458d50005bc7458d500b5fb7058d50006dd6318d5001cfd7518d501dcfe7418d50004fd7418d500867f5418d5007e7f5318d5007ede5318d50086dd5318d5002cfe7218d50004fd7218d500867f5218d5007cff7118d5000cfe7118d50004fd7118d5000cfc7118d50006de3118d5007edc3118d5032e7e5018d5032e7c5018d50006f71018d5001c7c7654d500057f7454d500067c6454d500157f7354d500175f7354d500075f6354d5007e7c6354d500075c6354d500057f7254d502467c6254d503667f6154d503667d6154d500077b7054d5001d7e7054d5001d7c7054d50007787054d500167f6054d500177b6054d5036777105
  | 24 => 0xe7159032004fd715903200cfc7159032006bf4159032006bd4159032004ff705903201cfc7059032006f710590321dcff769503202cfe7695032004fd769503202cfc76950320167e65950320067d65950320d73f5495032004ff765503202cfe7655032004fd765503202cfc765503238e7f65550320167c6555032104ff7654c3207e7f6554c3207e7c6554c32004fd76d0c320d57e75d0c320057d75d0c32386de63d0c32004ff7650c3207f9c4350c3202def764c832006ef764c832004ef764c83202def734c83202fcf734c83207eee634c83202fce634c83207fce534c832007cd534c83207fce434c832007cd434c832007e7714c83237fe4714c83237fce314c83207fcc314c83237fe7104c832004ff75580320067f75580320047f7558032014fe7558032014fc75580320067c75580320147c7558032004ff74580321dcfc745803202edf325803202eee325803202edd3258032006ed3258032004ff715803200cfe7158032004fd715803200cfc715803202efb705803207efb305803207ef8305803202efb205803202ef82058032006f71058032006fa1058032006f910580321dcfe7498e50004fd7498e5001ede7398e5007ede5398e500b6dd5398e5002cfe7298e50004fd7298e5007cff7198e5000cfe7198e50004fd7198e5000cfc7198e5001cfe7098e5001cfc7098e5001ede3098e5001edc3098e5001ef71098e5001ef51098e50004ff7458e50006bf7458e50004bf7458e501dcfc7458e50006bc7458e50004bc7458e5009e7c5458e5001edf7358e5009ede5358e5009edd5358e5009e7c5358e50004ff7258e5002cfc7258e5009e7c5258e50004ff7158e5000cfe7158e50004fd7158e5000cfc7158e5009e7f5158e500067d5158e5001cfc7058e5001e7f5058e5001e7d5058e5001ede3058e5001edc3058e5001ef71058e5001ef51058e500057e7494e500067d6494e500157e7394e500175e7394e501bf5e6394e500067d6394e501bf5d6394e500065d6394e502257e7294e503757f7194e503757d7194e501bf766194e501bf756194e501bf7a7094e501bd7d7094e50007797094e50005797094e500167e6094e500177a6094e501bf771094e5007cff7690e5001cfe7690e50004fd7690e500157e7590e500057d7590e500073e5490e5007ede6390e50006dd6390e5012ef66190e50004ff7650e50004fd7650e5001cfc7650e500057f7550e500157c7550e50006de6350e50006dd6350e50136f66150e5007cff7610e5001cfe7610e50004fd7610e500057f7510e500157c7510e500075e5310e500079d4310e5011ef66110e50004ff7358a5007cfc7358a500067e5358a5004e7c5358a5001eef7258a5004eee5258a5004eed5258a502267c5258a50004ff7158a5000cfe7158a50004fd7158a50
  | 25 => 0x8532006f764d8532006f664d8532006f564d8532006f464d8532397d773d85320e7d473d8532007d753d8532007d453d8532007d743d8532007d443d8532007e732d8532397d632d8532397d432d8532005f570d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d8532396f773d85320e6f673d85320e6f573d85320e6f473d8532006f753d8532006f653d8532006f553d8532006f453d8532006f743d8532006f643d8532006f543d8532006f443d8532006f772d85320e6f672d85320e6f572d85320e6f472d8532006f752d8532396f652d8532006f552d8532396f452d8532006f742d8532396f642d8532006f542d8532396f442d8532006f732d8532396f632d85320e6f532d8532396f432d8532006f770d8532006f670d8532006f570d8532004f570d8532006f470d8532006f750d8532006f450d8532396f720d8532396f420d85320e5f471d8132006f761d8132006f461d8132014fe75d8132004fd75d8132014fc75d81321dcfe74d8132004fd74d8132004ff71d8132006f771d813200cfe71d8132004fd71d813200cfc71d8132006f471d813200cf471d8132006f710d81320e5f67198132005f57198132006f76198132006f46198132006fb60981320057f75581320ed7c7558132005bf7458132005bc7458132005f771581320e5f47158132006f76158132006f461581320ed7e75181320057d7518132005be7418132005bd74181320e5f67118132005f57118132006f76118132006f4611813201efa6018132006f9601813202cff755943202e7f7559432004ff74594321dcfc74594320d67c545943207cfe735943207cfc735943207e7e535943207e7c535943202cfe725943202cfc725943202e7e525943202e7c5259432004ff715943200cfe7159432004fd715943200cfc71594320d67f51594320067d5159432004ff705943201cfc70594320d67f5059432006f71059432014fe75990321de7e75990320147e7599032004fd75990321de7d75990320047d75990321dcfc759903202cfe749903202ebe7499032006bf54990321debc549903207cfe739903207cfc739903207ebe439903207ebc439903202cfe729903202ebe429903202ebc429903202edf329903202edd32990321dcff719903200cfe7199032004fd719903200cfc71990321debf4199032006bd419903201cfe7099032004fd7099032006f71099032004ff7559032014fe7559032014fc755903202cff745903202ebf7459032006bf5459032006bc545903207cfe735903207cfc735903207ebe435903207ebc435903202cfe725903202cfc725903202ebe425903202ebc4259032004ff715903200cf
  | 26 => 0xcfc711913201cfe7019132004fd7019132006f710191321dcff7695132004fe7695132004fd76951321dcfc76951320167e65951320067d6595132006bf64951321debc64951320ef3f5495132005de7395132005dd73951320ef5f539513202dee7295132005ed72951322bef46195132004ff7655132004fe7655132004fd7655132004fc76551320067f65551320167c6555132006bf6455132006bc6455132005df7355132005dc73551320ef5c53551322b6f461551320fcfe7694d320167e6594d320067d6594d320edde7394d320ef5f5394d32156f46194d3202cfc7654d320067f6554d320167c6554d320eddf7354d320ef5c5354d32005ef7254d3202dec7254d3214ef46154d3202cfe76d0d320ed7e75d0d320057d75d0d32006bf64d0d321debc64d0d3202dee72d0d32005ed72d0d322a6f461d0d3202dde76d0d32006de76d0d3202cde76d0d320edde75d0d320075e75d0d320ed5e75d0d320075d75d0d320eddc75d0d32006df65d0d32006dd65d0d32006df64d0d320079f64d0d320079c64d0d3202dde72d0d32007ce72d0d3202dce72d0d32007cd72d0d3202ddc72d0d323bddf71d0d323bddd71d0d323c7d461d0d32005dd70d0d32296dc60d0d323c7d710d0d32004fe7690d320ed7e7590d320057d7590d32006be6490d32006bd6490d323b5de7390d320079f4390d3212ef46190d3202cfc7650d32006bf6450d32006bc6450d32005ef7250d3202dec7250d32136f46150d32004fe7610d321debe6410d320079d4310d3211ef46110d32005de7610d32006de7610d320edde7510d320eddc7510d32006df6510d32006dd6510d323bdde7410d320079e7410d32006df6410d320079e6410d32006dd6410d320079d6410d320069d6410d320079e5410d320079d5410d3202dde7210d3202ddc7210d3207edf6210d323b5df7110d323b5dd7110d323afd46110d32005dd7010d321a6dc6010d323afd71010d32014ff76549320ecfd7654932014fc76549320067f65549320167c6554932005df7354932005dc73549320ef5c535493202fcc325493210ef46154932004fe76d09320ed7e75d09320057d75d0932006bf64d09321debc64d0932005de73d0932005dd73d09320079c43d0932286f461d0932004fd7650932004fc7650932005df7350932005dc73509320079c435093202fcc3250932266f461509320ed7e75cc9320057d75cc93202dde73cc93202edf63cc9320def461cc93207f6e75cc93207f6d75cc93202dee73cc93202eef63cc93202fcf63cc9323a7cf53cc93207fcc53cc932007cf43cc93207fcc43cc93239fe461cc93207fcf31cc93239fcd31cc932005ed70cc93239fe710cc9320e5f676d85320e6f676d853200cf676d8532006f765d8532006f665d8532006f565d8532006f465d
  | 27 => 0xd6450e32005ef7250e3202dec7250e321267e6510e320067d6510e321debe6410e32006bd6410e320079d4310e3202ded76cca3207eed76cca3207f6e75cca3207f6d75cca3202f6e65cca3202f6d65cca3202fae64cca3202fad64cca3202fce73cca3207fce53cca32007cd53cca32005ed70cca323cfe710cca32004ff7558232014fe7558232014fc7558232004ff74582321dcfc745823202edf325823202edd3258232004ff715823200cfe7158232004fd715823200cfc715823202efb705823202efb205823202ef82058232006f71058232006fa1058232006f91058232014fe76d95320ee7e65d953202ddd73d95320ef5f53d9532006f461d95321dcfe74d9532004fd74d95320ee7f54d953202cfd73d95320eedd73d953202cdd73d95320ee7f53d95320eedf53d95320ee5f53d95320eedc53d95320ecfd72d95320ee7f52d9532004ff71d953200cfe71d9532004fd71d953200cfc71d953201cfe70d9532004fd70d95320ee7c50d9532006f710d95320ee7c65595320ef5c5359532005f771595320e5f47159532006f461595320ecff75595320067f7559532004ff74595321dcfc74595320ee7c54595320fcff7359532006df73595320eedf53595320ee7c53595320eedc5359532104ff7259532006ef72595322467e52595322467c5259532004ff7159532006f77159532004f7715953200cfe7159532004fd715953200cfc7159532006f4715953200cf471595320ee7f51595320067d5159532004ff705953201cfc70595320ee7f5059532006f710595320ed7e75d91320057d75d9132006f461d9132014fe75d91320067e75d91320147e75d9132004fd75d91320067d75d91320047d75d9132014fc75d9132006dd73d9132004ff71d913200cfe71d9132004fd71d913200cfc71d913201cfe70d9132004fd70d9132006f710d91320ed7e75991320057d7599132006bf64991320e5f67199132005f57199132006f46199132014fe75991321de7e75991320147e7599132004fd75991321de7d75991320047d75991321dcfc7599132004fd73991321dedd73991321deed72991321dcff719913200cfe71991321def6719913200cf67199132004fd71991321def57199132004f5719913200cfc719913201cfe7099132004fd7099132006f71099132005f771591320e5f47159132006f46159132004ff7559132014fe7559132014fc7559132006df7359132004ff7259132006ef7259132004ff7159132006f77159132004f7715913200cfe7159132004fd715913200cfc7159132006f4715913200cf47159132004ff705913201cfc7059132006f71059132004fe7619132006bd6419132006f46119132014fe7519132004fd75191321dcfc75191321debe74191321dcff711913200cfe7119132004fd7119132
  | 28 => 0x9232006be7599232006bd75992321debc75992321debf7399232006bd7399232006bf5399232006bc539923202ebf729923202ebe729923202ebd729923202ebc729923202ebf529923202ebe529923202ebd529923202ebc529923202ebf329923202e9f329923202ebe329923202ebd329923202e9d329923202ebc32992321debf7199232006be7199232006bd71992321debc7199232006bf5199232006be5199232006bd5199232006bc5199232006bf3199232006be3199232006bd3199232006bc319923202ebf219923202ebe219923202ebd219923202ebc21992321debf7099232006be7099232006bd70992321debc7099232006bf5099232006bc509923202ebf209923202ebe209923202ebd209923202ebc2099232006bf1099232006b71099232006be1099232006bd1099232006bc1099232004ff7559232014fe7559232014fc755923202ebf7459232006bf5459232006bc545923202ebe425923202ebc4259232004ff715923200cfe7159232004fd715923200cfc7159232006bf4159232006be4159232006bd4159232006bc4159232004ff705923201cfc705923202eef2059232006f71059232006bf7559232006be7559232006bd7559232006bc7559232006bd7359232006bf5359232006bc535923202ebf725923202ebe725923202ebc725923202ebf525923202ebe525923202ebd525923202ebc525923202ebf325923202ebe325923202ebd325923202ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc5159232006bf3159232006be3159232006bd3159232006bc315923202ebf215923202ebe215923202ebd215923202ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006bc505923202ebf205923202eaf205923202ebe205923202ebd205923202ebc2059232006bf1059232006b71059232006be1059232006bd1059232006bc10592321dcff769523202cfe7695232004fd76952320167e65952320067d65952321debe6495232006bd64952320ff3f549523202dee7295232005ed7295232004ff765523202cfe7655232004fd765523202cfc76552320167e65552320067d6555232006be6455232006bd64552320ecfd7694e320167e6594e320067d6594e32006be6494e32006bd6494e320ff5f5394e32014ff7654e3202cfc7654e320167e6554e320067d6554e32006be6454e32006bd6454e32005ef7254e3202dec7254e320fd7e75d0e320057d75d0e322ae7e65d0e320067d65d0e321debe64d0e32006bd64d0e3202dee72d0e32005ed72d0e320fd7e7590e320057d7590e321467e6590e320067d6590e32006be6490e3213e7e6550e320067d6550e32006be6450e32006b
  | 29 => 0x105dc75d0f32006df65d0f320075e65d0f32006dd65d0f320075d65d0f320065d65d0f32006dd64d0f3202dde72d0f3202ddc72d0f323e5df71d0f323e5dd71d0f32005dd70d0f32296de60d0f32387d710d0f3213e7e6550f320067d6550f3207f9c4350f3202cdd7610f32105de7510f3207ddc7510f3207edf6510f3207f5e6510f32006dd6510f3207f5d6510f320065d6510f3207f9e7410f3207f9e6410f32006dd6410f3207f9d6410f320069d6410f320079e5410f320079d5410f3202dde7210f3207fce7210f3207fcd7210f3202ddc7210f3207ddf7110f323dddd7110f32005dd7010f321a6de6010f323d7d71010f32014ff7654b3207cfc7654b320167e6554b320067d6554b32005df7354b3207ddc7354b321075c5354b3202fce3254b3228e7e65d0b320067d65d0b3207dde73d0b32005dd73d0b320079c43d0b320067e65983320067d65983320ddf67198332005f5719833207efb609833201ef860983320067e65583320067d655833207ef86058332004ff7558332014fe7558332014fc7558332004ff74583321dcfc745833202cfc7358332004ff715833200cfe7158332004fd715833200cfc715833207efb305833207ef83058332006f7105833202e7f7559632004ff74596321dcfc74596320fe7f54596320fe7c54596320fe7f535963202cfc725963202e7e525963202e7c5259632004ff715963200cfe7159632004fd715963200cfc71596320fe7f51596320067e51596320067d51596320fe7c5159632004ff705963201cfc70596320fe7f50596320fe7c505963202eef2059632006f710596320067f74596320067e74596320067d74596320067c74596320067f73596320067d73596320fe7c735963202e7f725963202e7e725963202e7d725963202e7c725963202e7f425963202e7e425963202e7d425963202e7c425963202e7f325963202e7e325963202e7d325963202e7c32596320067f71596320067e71596320067d71596320067c71596320067f41596320067e41596320067d41596320067c41596320067f31596320067e31596320067d31596320067c315963202e7f215963202e7e215963202e7d215963202e7c21596320067f70596320067e70596320067d70596320067c705963202e7f205963202e6f205963202e7e205963202e7d205963202e7c20596320067f10596320067710596320067e10596320067d10596320067c1059632014fe7599232004fd75992321dcfc759923202ebe7499232006bf54992321debc549923202cfe729923202ebe429923202ebc429923202edf329923202edd32992321dcff719923200cfe7199232004fd719923200cfc71992321debf4199232006be4199232006bd41992321debc419923201cfe7099232004fd7099232006f710992321debf759
  | 30 => 0xf535973207e7e535973207e7c5359732106dc53597321067f5259732004ff715973200cfe7159732004fd715973200cfc71597321067f51597320067e51597320067d51597321067c5159732004ff705973201cfc70597321067f50597321067c5059732006f7105973207d7f76597321067f76597320147f765973207e7f645973207e7c64597321075f735973207f5c73597322475e325973207f5c325973207e7f61597320067e61597320067d615973207e7c615973207f5f31597320075d315973207e7f605973207e7c60597320077710597320067f74597320067e74597320067d74597320067c74597321067f73597321065f735973207e7e735973207e7c73597320065c735973207e7e435973207e7c43597320067f72597322467e72597320067d72597322467c72597322467e42597322467c425973207e7f32597322467e325973207e7c32597320067f71597320067e71597320067d71597320067c71597320067f41597320067e41597320067d41597320067c415973207e7f31597320067e31597320067d315973207e7c31597322467f21597320067e21597320067d21597322467c21597320067f70597320067e70597320067d70597320067c705973207e7f305973207e7c30597322467f20597322467c20597320067f10597320067710597320067e10597320067d10597320067c10597320067e65993320067d659933207ebf6499332014fe7599332004fd75993321dcfc759933202cfe739933207ebe439933207ebc43993321dcff719933200cfe7199332004fd719933200cfc7199332006be41993321debc419933201cfe7099332004fd7099332006f710993320067e65593320067d655933207ebc6459332004ff7559332014fe7559332014fc755933202cfc735933207ebe435933207ebc4359332004ff715933200cfe7159332004fd715933200cfc7159332006be4159332006bc4159332004ff705933201cfc7059332006f71059332014fe751933207e7e75193320147e7519332004fd751933207e7d75193320047d751933207cfc751933207ede731933207eed721933207cff711933200cfe7119332004fd711933200cfc711933201cfe7019332004fd7019332006f710193321dcff769533207cfe7695332004fd769533207cfc76953320167e65953320067d65953321073f549533207dde7395332005dd73953321075f5395332004ff7655332004fd765533207cfc76553320167e65553320067d6555332005df735533207ddc73553321075c53553320d4ff7654f320167e6554f320067d6554f32105df7354f3207f5c5354f321057e75d0f320057d75d0f322ae7e65d0f320067d65d0f3207f9e43d0f32005dd76d0f32006dd76d0f32105de75d0f320075e75d0f321055e75d0f320075d75d0f32
  | 31 => 0xe520157e7510e520057d7510e5207ede6310e52006dd6310e520075d5310e520079d4310e52004ff735825207cfc735825204e7f53582520067d535825202cfc725825202e7f525825202e7d5258252004ff715825200cfe7158252004fd715825200cfc715825202efb705825204efa50582521967c505825202efb205825202ef82058252006f71058252006fa1058252006f91058252005be74d8d52005bd74d8d5202cfd75d8d521dcfe74d8d52006be74d8d52004be74d8d52004fd74d8d52006bd74d8d52004bd74d8d520fe7c54d8d520fede53d8d520fedd53d8d520fe7c53d8d523ee7e52d8d523ee7c52d8d52004ff71d8d5200cfe71d8d52004fd71d8d5200cfc71d8d520fe7f51d8d520067d51d8d5201cfe70d8d52004fd70d8d520fe7f50d8d52006f710d8d52006df6398d521075c5398d520eded7298d520ef5c5358d52105ef7258d52005f77158d5210df47158d52006dd6318d5202cfd7518d521dcfe7418d52004fd7418d5207ede5318d520d6dd5318d5207cff7118d5200cfe7118d52004fd7118d5200cfc7118d5201cfe7018d52004fd7018d52006f71018d5202c7e7694d520057e7494d520067f6494d520157e7394d520175e7394d520067f6394d520075f6394d520065f6394d520075c6394d5202d7e7294d520076e7294d520076d7294d5202d7c7294d520167f6294d520176f6294d523fd7f7194d523fd7d7194d520057d7094d521be7c6094d523f7771094d52004fe7690d52004fd7690d5207cfc7690d520157e7590d520057d7590d520073e5490d52004ff7650d52004fe7650d52004fc7650d520057f7550d520157c7550d52004fe7610d52004fd7610d5207cfc7610d520057f7510d520157c7510d520075e5310d520079d4310d5202cfd75d815207cfe73d8152004fd73d8152004ff71d815200cfe71d8152004fd71d815200cfc71d815206efa50d8152006f710d815210df67198152005f57198152006fb60981521967f6518152005de7318152005dd731815210df67118152005f5711815201efa6018152006f96018152104fd75d97321dcfe74d9732004fd74d973207ede73d9732106df53d973207edc53d973207eed72d973207cff71d973200cfe71d9732004fd71d973200cfc71d973201cfe70d9732004fd70d9732006f710d97320047d769973207e7f649973207e7c64997321075f739973207f5c739973207e7e63997323ef5e329973207f5c329973207e7f61997320067e61997320067d619973207e7c619973207f5f31997320075d319973207e7f609973207e7c6099732007771099732014ff765973207e7c655973202ddc735973207f5c535973207e7f7559732004ff74597321dcfc74597321067f54597321067c545973202cfc7359732106dc735973202cdc7359732106d
  | 32 => 0x6de7498e52006dd7498e5207edc7498e52106df5498e521065f5498e52106de5498e52106dd5498e52106dc5498e5202ede7298e5202edd7298e5202edc7298e5202edf5298e5202e5f5298e5202ede5298e5202edd5298e5202e5d5298e5202edc5298e5202edf4298e5202ede4298e5202edd4298e5202edc4298e5207edf7198e52006de7198e52006dd7198e5207edc7198e52106df5198e52106de5198e52106dd5198e52106dc5198e52006df4198e52006de4198e52006dd4198e52006dc4198e5202edf2198e5202ede2198e5202edd2198e5202edc2198e5207edf7098e52006de7098e52006dd7098e5207edc7098e52106df5098e52106de5098e52106dd5098e52106dc5098e521065c5098e5202edf2098e5202ede2098e5202edd2098e5202edc2098e52006df1098e52006d71098e52006de1098e52006dd1098e52006dc1098e52004ff7458e521dcfc7458e5202edf7358e520eede5358e520eedd5358e5202cfc7258e5202ede3258e5202edc3258e52004ff7158e5200cfe7158e52004fd7158e5200cfc7158e52006df3158e52006de3158e52006dd3158e52006dc3158e52004ff7058e5201cfc7058e5202eef2058e52006f71058e520eede7558e520eedd7558e520eedc7558e52006df7458e52006de7458e52006dd7458e52006dc7458e520eedf5458e520eede5458e520eedd5458e520eedc5458e5202edf7258e5202ede7258e5202edc7258e5202edf5258e5202ede5258e5202edd5258e5202edc5258e5202edf4258e5202ede4258e5202edd4258e5202edc4258e52006df7158e52006de7158e52006dd7158e52006dc7158e520eedf5158e520eede5158e520eedd5158e520eedc5158e52006df4158e52006de4158e52006dd4158e52006dc4158e5202edf2158e5202ede2158e5202edd2158e5202edc2158e52006df7058e52006de7058e52006dd7058e52006dc7058e520eedf5058e520eede5058e520eedd5058e520eedc5058e5202edf2058e5202ecf2058e5202ede2058e5202edd2058e5202edc2058e52006df1058e52006d71058e52006de1058e52006dd1058e52006dc1058e520057f7454e520067e6454e522473e6454e520063e6454e522473d6454e520157f7354e520175f7354e5207e7e6354e522475e6354e520065e6354e522475d6354e522457f7254e520076f7254e522476c7254e520167e6254e520176e6254e522467f6154e524067d6154e521957c7054e52407771054e5207cff7690e5202cfe7690e52004fd7690e520157e7590e520057d7590e52006be6490e52006bd6490e520073d5490e5207ede6390e52006dd6390e52004ff7650e52004fd7650e5202cfc7650e520157e7550e520057d7550e52006de6350e52006dd6350e5207cff7610e5202cfe7610e52004fd761
  | 33 => 0xd7490c431dede6490c4307f9e6490c431df9e5490c430079d5490c43005dd7290c431a5de7090c43427d71090c43004ff7650c431dddf7650c43006df7650c43004df7650c43005df7550c43005dd7550c4307ddf7450c431dede6450c431df9e6450c434179f5450c431df9e5450c430079d5450c431df9c5450c43005df7250c431df9f4150c4340f9e4150c4340f9d4150c431df9c4150c431a5dc7050c4340fd71050c430079f7650c430059f7650c430069f7650c430079f7550c430059f7550c434179e7550c430079d7550c430059d7550c434179c7550c4307f9f6550c434179e6550c430079d6550c4307f9c6550c430079f7250c430059f7250c430079e7250c430079d7250c430079c7250c4307f9f6250c4307f9c6250c434179f5250c434179c5250c4341f9f7150c4340f9e7150c4341f9d7150c4340f9c7150c4307f9f6150c4340f9e6150c4340f9d6150c4307f9c6150c4340f9f5150c4340f9e5150c4340f9d5150c4340f9c5150c4340f9f2150c4340f9e2150c4340f9d2150c4340f9c2150c430079f7050c430079e7050c430079d7050c430079c7050c431a59c7050c4307f9f6050c4307f9c6050c434179f5050c434179c5050c4340f9f1050c4340f971050c4340f9e1050c4340f9d1050c4340f9c1050c431257e75988430057d75988430079d439884307eef629884302eec62988430079d435884307eec6258843005f7715884311df47158843004ff7558843014fe7558843014fc7558843006ef5258843006ec525884307eef325884307eec3258843004ff7158843006f77158843004f7715884300cfe7158843004fd715884300cfc7158843006f4715884300cf47158843006ef2158843006ed2158843004ff705884301cfc7058843006f710588430079d439804311df67198043005f5719804307efb609804301ef860980430057f75580431257c75580430079d435804307ef86058043004ff75580430067f75580430047f7558043014fe7558043014fc75580430067c75580430147c7558043006de5358043006dd5358043006de4358043006dd43580430069d4358043004ff725804302cfc7258043004ff715804300cfe7158043004fd715804300cfc715804307efb305804307ef83058043006f71058043006fa1058043006f910580431dcfe7498e52004fd7498e521067f5498e5202ede7398e5207e7f5398e5207ede5398e52106dd5398e5202cfe7298e5202cfc7298e5202e7f5298e5202e7d5298e5202ede3298e5202edc3298e5207cff7198e5200cfe7198e52004fd7198e5200cfc7198e5207edf3198e52006de3198e52006dd3198e5207edc3198e5201cfe7098e52004fd7098e521067c5098e52006f71098e5207edf7598e52106de7598e521065e7598e5207edc7598e5207edf7498e52
  | 34 => 0x954313e7f51595430067d5159543004ff705954301cfc705954313e7f5059543006f710595432acfe7694d430167e6594d430067d6594d4313f5f5394d43014ff7654d4313cfd7654d43014fc7654d430067f6554d430167c6554d43005bf7454d43005bc7454d4313d7e7590d430057d7590d4307f3e7590d4307f3d7590d43006bf6590d43006bd6590d430079f6390d43005bd7090d43447b71090d4313d7e75d89430057d75d8943014fe75d89430067e75d89430147e75d8943004fd75d89430067d75d89430047d75d8943014fc75d8943006be43d8943004ff71d894300cfe71d8943004fd71d894300cfc71d894301cfe70d8943004fd70d8943006f710d894313d7e75989430057d7598943006ef6298943005f77158943135f4715894302eee6218943006ed6218943014fe75d8143004fd75d8143014fc75d814302cfe72d8143004fd72d8143004ff71d814300cfe71d8143004fd71d814300cfc71d8143006f710d8143135f67198143005f57198143006fb60981430057f755814313d7c755814313d7e75181430057d7518143296df6318143005ee7218143005ed7218143135f67118143005f5711814301efa6018143006f96018143124fd75d944307cfe73d944307ede73d944307e7f53d944302cfe72d944307eee72d944302cee72d9443004fd72d944307eed72d9443004ed72d94431267f52d944307cff71d944300cfe71d9443004fd71d944300cfc71d944301cfe70d9443004fd70d94431267c50d9443006f710d9443014ff765944307e7c655944307cff755944307e7f755944307cfe735944307cfc735944307e7e535944307e7c5359443004ff725944302cfc72594431267c5259443004ff715944300cfe7159443004fd715944300cfc71594431267f51594430067d5159443004ff705944301cfc70594431267f5059443006f7105944307ddd7694c4307edd7694c43014dd7694c43125dd7594c43016de6594c4307f5e6594c430165e6594c4307f5d6594c4307edc6594c4307f9e7494c43005dd7494c4307f9d7494c430059d7494c432aede6494c431275f5494c431279e5494c43005dd7294c431275f5294c431a5de7094c431275c5094c4343fd71094c43144ff7654c4307e7f6554c4307e7c6554c430073e5454c4307f5c5354c43005df7654c43146df7654c4307ddf7554c4307f5f7554c4307f5f6554c43016de6554c43016dc6554c4307f5c6554c43005df7454c430079e7454c430079d7454c432aede6454c434375e5454c431279e5454c430071e5454c431279d5454c434375c5454c43005df7254c431275c5254c431275f5154c4342f5d5154c431a5dc7054c431275f5054c4342fd71054c4307ddf7590c4307f5e7590c43005dd7590c4307f5d7590c430055d7590c431dddd7490c4341d9
  | 35 => 0x67f72596430067e72596430067d72596430067c725964307e7f325964307e7c32596430067f71596430067e71596430067d71596430067c71596430067f41596430067e41596430067d41596430067c415964307e7f31596430067e31596430067d315964307e7c31596430067f21596430067e21596430067d21596430067c21596430067f70596430067e70596430067d70596430067c705964307e7f305964307e7c30596430067f10596430067710596430067e10596430067d10596430067c105964313cfd76952430167e65952430067d65952431473f5495243005bd769524313ebd7695243016be65952431473e65952430163e65952430073d6595243016bc6595243005bd73952431473f5395243005bd72952431473f52952431adbe70952431473c5095243467b71095243014ff765524307cfc76552430167e65552430067d65552431473c5455243005df735524307ddc7355243145bf7655243016bf7655243014bf76552430073f7555243016be65552431473e65552430073d6555243016bc6555243005bf73552430079f73552430079c735524345f3e535524345f3c5355243005bf72552431473c52552431473f51552434573d51552431adbc70552431473f5055243457b71055243124ff7654e430167e6554e430067d6554e430073e5454e432ae7e65d0e430067d65d0e43005dd76d0e431dedd76d0e431df5e75d0e431df5d75d0e43006df65d0e430075e65d0e43006dd65d0e430075d65d0e430065d65d0e431df9e54d0e430079d54d0e43296de60d0e4344fd710d0e430067e6598a430067d6598a4307eef6298a4302eec6298a430067e6558a430067d6558a4307eec6258a43004ff7558a43014fe7558a43014fc7558a43006df4358a4307eef3258a4307eec3258a43004ff7158a4300cfe7158a43004fd7158a4300cfc7158a43006ee2158a43006ec2158a43004ff7058a4301cfc7058a43006f71058a430067e65982430067d659824312df67198243005f5719824307efb609824301ef860982430067e65582430067d655824307ef86058243004ff7558243014fe7558243014fc7558243006be5458243006bd5458243006bf4358243004ff725824302cfc7258243004ff715824300cfe7158243004fd715824300cfc715824307efb305824307ef83058243006f71058243014fe76d954313e7e65d954313cfd73d954313e7f53d954302cfe72d9543004fd72d954313e7f52d9543004ff71d954300cfe71d9543004fd71d954300cfc71d954301cfe70d9543004fd70d954313e7c50d9543006f710d954313e7c655954313cff75595430067f75595432acff7359543006df735954313e7c5359543004ff725954302cfc725954313e7c5259543004ff715954300cfe7159543004fd715954300cfc715
  | 36 => 0xd71d915300cfc71d91531467f51d91530067d51d915301cfe70d9153004fd70d91531467f50d9153006f710d9153006bf649915313ddd73991532addf7359153006bd64191531debe5419153126bd541915302cfe7219153004fd72191531dcff711915300cfe7119153004fd711915300cfc711915301cfe7019153004fd7019153006f710191530157e74951530173e74951530067f64951530073f64951530063f64951530073c649515307d7e73951530075e73951530075d73951530167f63951530175f63951532457e72951534857f71951534857d71951530057d70951533367c609515347f7710951530057e7494d530067f6494d5307d7e7394d5307f5e7394d5307e7f6394d530175f6394d530165f6394d532457e7294d5307d7f7194d534757d7194d530057d7094d5346f771094d531dcfe74d8953004fd74d89530067e54d89531067c54d8953106df53d89530067e53d89531067c53d8953106dc53d8953106ee52d89532467c52d8953004ff71d895300cfe71d8953004fd71d895300cfc71d89531067f51d89530067d51d895301cfe70d8953004fd70d89531067f50d8953006f710d8953005be7498953005bd7498953006ef6298953005f7715895314df4715895302eee6218953006ed62189531dcfe74d8153004fd74d815302cfe72d8153004fd72d8153004ff71d815300cfe71d8153004fd71d815300cfc71d81530b6fa50d8153006f710d815314df67198153005f57198153006fb6098153005bf7458153005bc74581531be7f6518153005be7418153005bd7418153005ee7218153005ed721815314df67118153005f5711815301efa6018153006f96018153144fd75d964307ebd74d964307ede73d964302cfe72d9643004fd72d964307cff71d964300cfe71d9643004fd71d964300cfc71d964301cfe70d9643004fd70d9643006f710d96430047d76996431473d749964307e7e639964307e7f629964307e7c629964307e7f61996430067e61996430067d619964307e7c619964307e7f609964307e7c6099643007771099643014ff765964307e7c655964307e7f75596431467f545964307e7e535964307e7c5359643004ff725964302cfc72596431467f52596431467c5259643004ff715964300cfe7159643004fd715964300cfc71596431467f51596430067e51596430067d51596431467c5159643004ff705964301cfc70596431467f50596431467c5059643006f7105964307d7f76596431467f76596430147f76596430073d745964307e7f625964307e7c625964307e7f61596430067e61596430067d615964307e7c615964307e7f605964307e7c60596430077710596430067f74596430067d74596431467c74596431467f735964307e7e735964307e7c735964307e7e435964307e7c4359643
  | 37 => 0x10014006000000200000000020001001400000100090000004002c00d000001e000400e001000100040060000003000c001001000100000000008010000c008002000c0008002000400100380000000000000c006000c001002c004000000e00000020004000000000500140010048002000000f000c001002000000180120000001000000a0018000000000000000070020002000400200000030004002000c009000000100500010030006001c001000000000080000020003000800200440010000002001000e0004000001c001000400100040070004005000c00b00140000004002000000200000130000001001402d0018000000000100140010018003000000100300030008000001000b0000000000c01600000000010007005c005000c00000680020024001004c000002401f0010000000000000000050008000001c003000000000000000004002001800300040180004000001400300000020004000001000800440000000001001000500000010004002002000000080000000003001800a0000010000c0040014000003400e0000001001c002000400000240030040005000c0000004020000c0000008000000c00f0050003001000007ebf64992532af5f53992531de7f54992531debe54992532aebd549925307cfe739925307cfc73992532ae7f539925307ebe439925307ebc439925302cfe7299253004fd72992532ae7f52992531dcff719925300cfe7199253004fd719925300cfc7199253006be41992531debc419925301cfe7099253004fd70992532ae7c5099253006f7109925307ebc645925313f5f535925313ebe545925307cfc735925313edc735925307ebe435925307ebc4359253004ff725925302cfc7259253004ff715925300cfe7159253004fd715925300cfc7159253006be4159253006bc4159253004ff705925301cfc7059253006f710592530ff5f5398a5307eef6298a5302eec6298a530ef5f5358a5307eec6258a53004ff7458a531dcfc7458a5307cfc7358a530eedf5358a530eedc5358a530eeee5258a5307eef3258a5307eec3258a53004ff7158a5300cfe7158a53004fd7158a5300cfc7158a53006ee2158a53006ec2158a53004ff7058a5301cfc7058a53006f71058a530af5f5398253155f67198253005f5719825307efb609825301ef8609825309f5f535825307ef86058253004ff74582531dcfc745825309e7f545825307cfc735825309e7f5358253004ff725825302cfc725825309e7f5258253004ff715825300cfe7158253004fd715825300cfc715825309efa50582531be7c505825307efb305825307ef83058253006f71058253146be54d91531467c54d9153146dd73d91531467c53d915302cfe72d9153004fd72d91531467c52d9153004ff71d915300cfe71d9153004f
  | 38 => 0x800a000000000000020044002001801000000080010000002c0050004000002400800080030004000001800e000000d00000040020008000400100000000010000000400100000030018004000000600000000008001000c006000000a000c000000000c001c000004c0020004000000400800580000014000000000200040260004001000800000040050000003000c0000000000001000b0018007000000b0000007002400c003400c001000a005800700000000004000000c00100000100008004000c0010044008001000c000000000000010018000008400500240050024002000000000140000064007000400f000400000180040000002000000c0008000000400c000800000200010038001004401000280030014018003c00600000000020005003801100000000004000002400e00000070064006002c000000000800000020000009000000b0000000000400000100060000006007c005007c0000000008000400100240030000000000000000000000000006000000900000000000004010800000000050000000001c0000000006000000200240010004004000c00200040000000003000000000080000038007007000300100120008000000000800100000018001002c00100140050020009000000300100030000001000c0010000000000c001002c00c0004004000000000240060000000000c00c00000000018000000c00200200010004000000800100080060080006000c0010010000001c00000080030008002000801a00000000000002003c0000000010000c0060000003000c00a00400000024000001401500000000008014005c001000400d00140000018000000400a0000004000000100080000000008000800000100010000000000002100080090004002001000300e4003001c000001400c000c00500180000004004000c00b0008000000001d00340000020001000400b00040000050000005c00200240010010000000c0070000001000400100140010008002000800000100000000000002800200e40050040000007c00d000000100000010000000003c0020000005001c0000018003000000500040060008001000c0000004009000c00b0000005003c0010004003000c00e0000002002800200000010000000003c00000000080000005000c0060004000000000000100030000005000c002000000600040010004004000000300040080000001000000a000000300a00170010001002000000040020000002001400000200000004000000001100040010014008000000000000000004001000c00200080040008002000400200040020004007000000000080140014000000c00100000030000016000000f00080000058003000c009000000b002c003000000200000090000000001c00b00040000000
  | 39 => 0x180000010008001400400000100000004002c004002c00d00000050010004000c0080008000001000a0018002000001600180000008001001c01d000000300000040008002000c000000800300100010018001000c00700380010044018001800000000010000002001c001000000b00040030060000001400600000030028002003000500100040010001000000100200080000002001400000140030000000000c010000401b000000400280010004001000000d00000040008001004c00100000000008000000c02b001c0000014000000000300040090014002002000100040000020000000000000080070030008001400100140000028005003c0010004000000c00800000060008009001800e0064002004000c000400c000000000000020000002000000d0004000000c00000000000088006000800600080040010000000c0090008003000000400000000000000005000f000800000180030000006000800b00080070000008000c000002400600840020000019001400000280010000001000000100040080048002002400000000070014000000800500040000000001000000c000000300040150078000000000000040000000002002c01600000000000002000400000280000000002000800000000040014001000800100000010000005000400000000000000000000c00000240020000001001800700200020014006000000100040040010004000000300180010008016000c0010000000000800000140010010002000400000000020008001000000f00200000010003000c0010008000001000100000000014003001c0020000010000000000000000004000000000c0020000001c002000400b00140000000000001c001000c001000c0000008017000400400000190028001000800000040000000008002800b00140150008003001c0010000008001000900080040008014005000100080130024000000c0090010001003c001000c0000000007000800500000000014009000c00200180000000008001000000000000014002000000600000070024003003c003000400100200080004004001000000000010004000000000100580020014000000c0000008000000400000000000008000000000000680000004006003000100000000008001002800000a800600000020014008000400e003000200000000004000000c0010008001001c000000400900440010024010000004600000010020001000000a0014000004000500040000014003003000500000020000000004000700080110004002000801200180030014000004c001004c00100080030008002000400300000000000001006000000000000000003000401d000801a000001900000030008000000000000000020000011001800300000020004008
  | 40 => 0x7003000d000400a001000d0008000001400100200030000019000c001005000d001000100180010004001003800d00000040004000001c0000000000000000b001c00200100020014002000000600300010000000002800100140010030002000c00d0004004006800b000000700280150000005004400000000010024008002c0000034005000800200a80040020000002000a000400000140060000003000c0020014003000400d000400c00140000000002000400a000c0020058010000800500080190004000002001800080020018001000400000000040018000000800a00000000008000000800800000000000002001800100000010024000000800400a800000100120004005000401c00140030004005000000100040000008001000400c000000300340030000000000000000140020018000000000400040000018005000000000000100020001001c00500100000008000001c00700000000004001000000400180000004000005c0020008001008c00000100040000009000000200580170000001000400000000060000004001000500240010000024007c0040004025003c00000000000014001000401300180080000000000c00300000070048000000400e000400700140030000001004c01800100000004002000c0020044000000c0000008000001800f001c00800000040020007000c00f00240090008001000000a00000070004001001c001000000b000400200380020000008001800200000110004003000000600040050000002000c004000400100080010074002008c00000a0002001c0120008001001c002001c000000000700000010018000000001c000000a00180010000007000402900140030018001000000d00000110000007000c00400080040008002000c001000000100b400000040070000001000000b00140010000000000c0000000000000000100040020018000001800300240090008000001400300000000000002001c00e004c0000034000001800300080070004001000000c00040150080000000800400240190000007000400200000020010001003002000000030000000007000200000050018003000400200040010010003000c00400080060000003001c000000c002002c000000c003001c000000c0040008000000400700100070028001004400000000220028000000c000000400a0008002000c00200040150008010000c0090008000000c0030004001000400400d4000000400000400010000000000c00800200010000001006c00400200080000000000001b00180000000000000c006001c000001400200140060048006000c0000020024000000b00040000000005000400100000000014001000000900700010000006000400a00000000014003000000200440000000002000
  | 41 => 0x9582c3d9eca00023f268b10da9fb0a4e71b80007ad00001c81c7a7590000715a2a0a79a28600022ce407800018f00003a7065384a93269cd81881568f84000188828883ae2e2e19ea1d12cc724000059b1ce00bbd506000036e7be0000c2b8000462268cb6f8000ba2cf864020b5a9339890234000008a986283f17b649300000001eba0000000ab1d322a4000005942b2a00000005ea9010000264646d0000b4d00000000ade000000000000000002ff80001bf34fd2ee4000003b4fd88160002f5804d000010d1e8500007f67301b7e00007c898499d08b0a06d00001d82d4b16243068aa89131176822abaa7ca8ca0d5ed9e000000083200000002a8cbd4594a82ea994592157000009e0000094c00024c8020800000000000000000b53f0be47994712bca8f2abd2b3227f8e3846d8c1c000000000ce2e59ce82541cda3c700020aa711a62e4d78b4ab8a1b50b45a0540002a560000016001c0000034001000c001002800200000010018000000c0080040001000400000300010008002000c00200140000000004000c0030004004000000a000000000000060004000001c0040000000002c001000401000000000008002000000100b4006000000100000050004000001400000000010000000003000100000000000012002000c000001c00040030000000001000100140040004000000000200040000000004001c00000140090024006000801400080010018004002c00000080010024001004000500000070028000000c00d000400200d8007002c001000000000000090000002000800200400040000004000c00300100000000001000800d000800d00080180000003000000000000000004000002c00100340000000001001400100000000000000000c0040004001005c008002800300080000004001000c000000c00500100000000001000800200040000004000001000100140000020000000400200040040000008000000800240080004008000000b00000010000000000000000000030030001000c00100000000004000000000b001c0030004003001401700040010000009002400100100000000002000001200000000044000003000000200020004000000c009002c000000401000000000008000000000d00200000000007001c01300000000004004000401b000400b001c006000001400040010024014003400900040010024000000800700000020004007001400000100030000000000400200040020008006000400000040000004004000000e00040000000001001c003000000300000010004001000c0010008002000000800140000000007000000600140000004003008c000000000600040060000004000c00300080070004000000000a0018000000c00400000000004003000800100000000010002000000
  | 42 => 0x8c37f840a3a9846ca3099c2485a20e59b971cb13116202500000000b08487c3212ab181e79c808c96c8000a77aad60000000000017a0000000737ad222c92bbe0000af90000000000000092cab600000100044119075796ee64300000a7400036d2bf600000002079f3faf604e800016f40000000000232c17989fc2179e6200004e40002fe4000234500018920000609000000000000001a1aa8248985308f500928f7217c00007fc0000000513889052f02185db00000000000000000000013be00007a800023a10000000000000000000000002e2c61780000000000776800000023890000000af800003e900004e7995e35f31e600015769e617300ca23cc200a327000095655985ee8e8000000014140000000aa720ca00000000001c2b949000060ca5ae80440548f88f24000240a7d9c00051980000001e3a710032017a89c01702cb46804362b218b882d164b01ac0de09da11943e80bcc7b122f6a3b150000013ad25628d4779839c4caae2a535e1c26361f64000156abcaa34774f275e0001046bb6290a58f00003380000921000000027990000000000000049780000000e3e1da0000000000000000000000b6c0000eec00002262fe95de00000000c301e40000000720000000000000002cae0da0000171800000000000000a0454d8251000320a0ebdb824611c06b568bd4000000046c8000a988a1c000194667620f80002718c6d9386aff05732df827c0000ff06c39d226b14000ae92820af488fea3d8bd060fab3c6a597903aead2c5d42c975522bf01a88216a44803c87c9a645d18fda381a87824727ae5761fe04060f4e00000000001ba20e2000077a17d00000000000245700022dc00014e995c217063811f202d400096b1b2400000000000a280002f9600000002bb8000417b00a000255400000000000e3cae0a1a22b88f580000000ba9048653c000042d40008f39394000000000006c40c4ac24000000000031940002ae22c980006bf019800025462fa0a5a000000000002444400942b5119a0b7681743660456669003a00000005789b2e0001e516d0a1c495d859c2598eac4340140564b15eb34214c1bd1ecc0519de295893f26022d4c477a78a9621d0e31f22f832dabf4b6a1614a3700000000b2800000004f400000000000057e94e882281600010feb4c000000002ed6d7ac40000154aaed0b908810ca65be191200017e43a0260c1d789860000000651000048da938444afb8000229ea02284c0001e20b9d0000030252c00021e4000000074da82cc07b0a6a750000000080d361000078b9f74beaa13cc20cafe9bca8046388000b6995899a2a7cd4938be60000538900256e82617a22589d1c000000021b31c68ec081f3de445e3e98000474000085e9fee5ef22ba699adb42429b6e4f291060ae0000bc69ae032
  | 43 => 0xf04002500a20fa7ee2ec93b873417186790000000000082103ed000000018a8a8c000000041580007be86a656f80ba47485b100000000fd0cbe0002f64000000051b80003ca161200009a69c5800000000000001a1019080000000ad0000000000008ec17d806c42aac269628000ba380000001988b318928c0a29ee1b296d6c7312280000000b4e8786431a0464a1022eb6fe9f6000209e85092200000000000212400013a000000001ff8000084305a3f9a69c7b6243a3c6a258000186a57502455fe000043d800040e95e500007c60001b895c4a8ae1958156a9719dd9e580008c6a7400000e8a723a2be4ce839276a174c5a653e6bec0fdc1c52ef5afb30da365ab1e5282d52278ab8e8980c5267b801a2250b9b8d11f4a7772b560d6400000000007fac00027640000000000a6280003b7000000025f6b8e1784a1f13bb8b81368b10846064803d60002b280001d824751fda00000008d800006a70000000000040a1e847ec800021ad7ec00000008ea00000fa4000000205a0000000ad121400002bac12c993013e82a88d52b3061ca26a3a309c641f911a4d9916a16da3d9390800021500000002c0c0002cc20000000923a0ea8049ca41a42413000000074322b86bb8f394e60d00c4e00002490a40aa8cab633646487b2c3514f62266000302ec1f8bea3066b340000000000000000011e000008ea00008310000000bc0265c00028f421f13da00012c07ee23884b04ef65e6838600000007649efc61512683ed9ce71a097d48c60000672024e5af8000151ac600d12b88182852e521b1303c9e03a000082c97500004bb0000000000000008860002ef090bd0a219c0000942068400000000000adc2796a9900004544442328b68a75a0eac0000002034194152c0a5a33c38740002d900002e81bed43a8000b928c3e00000000001e280001e9c00002fe000166042b86ff68c00003ee000000017d600029e46d222280b5857a000237c0000000b7626a6850c00000000004a500000000000000000084e0a8269680d9c42000000008aa2511be80df849a0001134056a9f8079800094d9ec20001064000000000000009898000bfc800040ba87200028e200005b5968df52546a3f800006fbc4a20960000000000207a00000002fc8000000000093f000000003c10000000000000035e1462aa40d325140000000000000026ee000000030227f20000d82b29800025928a60d680001ca84ca00015fa0000cb03674b1212b959c14b27047749dee7819bfc0000000844045a97a9e5e19f03be4d880000000000b5600000001c15000149000000000001bceba72a3e9c780e414707ce0001076000000080c000000000003538000c20077a0001c863d90b9f0002f5409e314a4ab10c400000001ee23b815bc00000008e64dc4000803ee5618e0b
  | 44 => 0x70297a2af0bbb0e2c67787bc468000000028ea00000000000000b9ab0040540ae43e0800000000000000000000000063509dcae60000696000082e0000a58897851ca47094e2cbc73d0de800000008ef000000000009ad954c1f5800000017e259d0000000000057aa5ec00017fb66f0c566d3258480924ea0000039be42f3800020663f792f00002fc478580000001cfaacd87040002baa364400092f0ad26de0097102000001498d6000029a00030c280600007878a08000257a6748000a3c066e58548720600f076e7254e3c36f068dbb0a0019000002585790002a586930b25bce80000002e2499d203e0002a40b642c980eca46ea2c000000006d06f419900000974000016d000200ab73000023f69269a600007b7b1d6813851e6d3a1d069b090851adc5e372a7b2c700532442027e66c000000010542bd0000ad3800000000004c50000aea29720002af87454000b418d85143800051ea41479f822f5610000b5da15a478936aaa610bb00009540002f4cbe1037cc498bf409c94ba644285cb612f7800012c8b20000048ca122000000000980007b5ac9a0001ea000000000001050783c000c6c80000000000202150a79d1596a10564d0001b9a43381c8544400077d800039f8000001e47e13a93527d956524bb8f94508058238224743091ea601a81cf000000000014a81bc8000016088055b29bc8cb40000002f1600000007a480002b6945600012d24f78000489ced695300000001000000169caa49bc85838e52a738cf200030242b09540000111b00000005e3000000027be0000000247da4049c82f20001d6c472000027d000000000006eb111cb439558c42e5d031891663d4909e0000c5a6dc0dec82681c4a692d1eb94838256b0000000000000031402e340000001a0350e9370422833e0002ecc81a80007aa00000000000bd721d20000000000206ea450000000083247f8000b53400080780000001b1e0000f7600000001a39ceaa64aaa45c3057618ef0102e1eb8c00013b13e61ca669c8f125ee94d200029da0000f5a81e0018b78835e367a6d0b670000b01000000003557f9c000000000045c800000000004de800000000000000000000305217300000000000000000010fe1ce1a29f72c0010eb99008629daade03589e4688904143202de836f02c466618f09dcb0f40000732ba3c26a00000000a09a68c248b36b7d0000a41800000000000378f90000000000012f41ba21cc0000000266c00000000007fd97b20000000c3c07e467959c07c20fb4000175a5fd19eb0001356000000000000005f4ac36035c3c6af9996c06e26a000016bcc4480008319bf45568be4a7c02f827ed132470900e7ce1cd8955919267a06daa0780ce42a04f46a0238643e29a20000b5800010d20000000c3f8a681ca172c11a19fc00010c00
  | 45 => 0x74c44810000000bad2e7f646ed1abdd800001cc5f7000000000000000000000000000000016400002e70a8380003dc1db600009f263031190158fbc5e3961c83d039411c18285512fd2299000037580005b98ec266ca0bc33300000000000c57160c5b09d1e01bc61e3c2000052c800000000000000000a6dc0006ac286aa4b967800018ca073800072482245210dd08c7000028680003479800000000000000000000000af1000000000008bc4000bafaa3a3c700001bd82de6029756b4a1c22238527c457e486bef1fe483d9d884322c7e47c0e625caa694a2299000001b3628994da7ab95a9bed00009842c4501806661dd96d439b93a64252ae800fafea72e8000c50c00000019177ac88a08a89aac85ba7f60000000150ad7e6211c548f42dab000048005c0d8a37cb0cc00017200000ad62f640375691332071800000009400a19d42484800019eb05e000272840b10e675196d83939d623e5943634c000090100450090000ba7802ea0ce0f217b6ade49f8700be8e0d4937953c0000000c38800000000000000d8e2d81ab4115602878d800058c81e8c658a8634088fc00012340000d2c6c89fd019f969600011049be27c86889af500026bc3868000000000000000100000000c380206728dd70174c000b4ecacc0000000000000015a3154383a72e78ca08c00000000002c34a92976a31c000084d80009ee000000000000000d1000000000001a1d00003da7868000158800063ea094939000050e0000c790be22d9b048878825620753c50000fea9c49830b5083809d1159560f0bc270b00008ec90607c080d66a50812387cac45730000aeeb09e1f6921e000000062880002f4cbf600010680000000a1f8000b0c82f36c6031eb54c000b35a6807a740009ea80007e9800002a047e73b071e000079017b000088f14ac00023250002a7c000052009e800000005756d700000000000b7d80003b60e4a7c400000002fd8511000000020ac00000000000bb987a8000000000096d0ff400028480002a100990d1b0000d2000007b070802e280ac16a2bdc31a91b09000001aa202f906a0aca3eebb419f401d2ec07fd218ec2e00000002e8ac230920bc98cbc57d9d147d102cd4428514b9f8aca6f08fee83c0000b0a00000000abc1e09e18b87969000006ce0000000b77800014a000080f400000012f84258000c050000000010475f00008641498000282e4c807348b50ecc7f725d60001a4e00008ee2f480000002a609b7af7588f84643ca5dc400a2fa8964a6a1022218074a000000000000eb00000002e4000027fc3c9affe394033824d00006772a5a32123f63c080000000000c1000007d1984a0002cf800000001a00a9f0d58cdc5688e48a881fa8566000027580004ee9fa400000008ed000091e08137f52c64982a62440e0af81b90
  | 46 => 0xc4800023ae0002a5e1b61f8a0244000b41000086e1f5c0002ca48ed96ac3529da600000000c8c0005c3800020d1cf200018aab7429889f81768836aab61040ca20002e11408219c00010fc00000b4047800000000000000000000000023601fcb960d1a8651d0886eb12cafa94d982c80000000000baa9cb283eac5c71e0000a52916815210ba9ab80164551da200030421c4ad62b0000000f80ec05399c52280800000000000000000b79c2e6668800000029520354ab4933145a7f2241e99825944361ec06ad41064232b041dc91ae0000000bd3cb0648600c20000a8e45731fe6a815945971d3e7db8824322256490700003884000000000023a000009b9ab1be200006e1222a50c0661a540000904800000013840000000b7f0d8000000009a6800000002e07f880009ad06f00002c5406c8d361cb0d7022b0b1400021990000f4a99ca2262d7145e238088e327000085d289ca440000000032f6b9afba0001cc64edd35c00000000678000000306600011e400000006f300000001c05bebb0a20000000000000050f2dc00fba67c0000fac10ba6d2bae4000a5d2776adc00005f0000000000004c01590483000099d80001f80e400000000456ab0c17d4000000000097d1ec60000000000000000022786fe01960e7aab3b168000398147e2292cec0000af00c09499000225a000200c787000000024f05e3d14c0000000000257c033e53278b17528c91fcc92b000065aa71c5c11772b9e27883cd9c2a90f10f0ad7af444c4a9be3d21dd69c09350599015856f02ca89263ed000000021b9a601c5c00000000003971b545c9164a0002000610800037e862f7279baa2d1a2eeacba24c4ff28de64fae5e14e9f0a888800074c93e40000fd2be2649200000000001c7e0a5634600000000000e36000000000000000000000000135400011820e88caa61995526c827a0ba65b3ec36216abaeaf5a00000fc35da71003b085a13812b4846da44590a50645542ae1f62162af5847bbd4cdf06db1d5a000000010a2c1800020c4a6ca0e4018914a000000000000000000000a3827dc0000000000259000000000000000000119e3ac1cb4000070c0000852240aa2400006fa412a121032299e3279bae682dde0481a2688b98000ac800003a5800014dafe2c3000000b61a280002922471a3080000fd450615226f613c88a6a856793ed38845000058288b40000000a828000000000016289b800000005ea0000000000000000000002c629f10b626ed18a03a1000048395128ff80000000000838800000380000000d540001daa0002c0a34e83f19cd00004762294000000000000004670000411148e508800004b881ab339fc0419af66c25800000010d65c200000000000b0e2150b6b9e40ad09a1800003409f998d29c2ac1e0000960c568472000319c
  | 47 => 0x9fe800000000000003141000028c1cc000000004f20000db83088dea3881e2400000009eea53463b800010c000084bb16e3e394ae972261c00021525ec04960001a421744c120000000c5821e8013042a756c66a000000068497700001f2c541c79619bc000c07282539c00002a8129c6cb16720002cca0002134000106e000000093980004e48000000000000014a700008e48b1ade63ea80003c285b000009cc5cf253e5ef82da0000f0ca3680006f198ac21a1e82065400000000000000000109800015381a8000000066f9cd659fa37a00000000002d703799f8e94a00002370ad418b9aec53e983443d082229c059a97c8892979a78c65d9f1a7828d2e2cadd52801265e0000000083eea0c78129a000194ead69cdaa9f8bb71129afa0525a6e8a41ad8c5b29403bd2ec627aa0e03388cde62f94e01ba83fe92788be085277a3ea18fe0be93ceaafaa7084a28bc9cc000000008ae46e05dcac900007bd0418ad200000000746430b1c800012597371a463599a9f000128c7f6240c7a94000350c00051d2f689b6933c0b00ea0000193a12e8b9a6409e9b69e885892811775e819e28069048168997ca9db1a877428120000000a0c800000000000001b806b904f84a2ae428e10c47000110700007e22a6ad780000000976000000000007bb879a0d51a020000000000157f1108000000000058e1f2b00024d4ae500b3371a7d601c00000002380107259aaa02bb044044121aa1c0826305f80000000365263a0eaacb8bb280000000000000000023251a66f6800080d86c213712be9cc84f654fadb688d03c30000000c62a070265c00098d0e88000000040100fa00023906099a3e0001e4e0001d2000000006b794e4000000043e8d4579b9098086448400000006a4ce440000000a1eae30a9a2c9ec49267e8c10d28a19007c00000001658000bf000000000d79000061a18e89de00019f50000000458d56e3b8238d76f04323f595f812a871696c02049d60b4caa684b071315b404b1a17bd882520fe97020002b0ec1dac525090d7439321f8a4c12040a88eda7811be2b7f8b2064da182701f0aca5600003a91a5094611a5a1dad0c00006bcc46800012e08401e617e60001288000000000005f4000032b000065e00000001a68b2c0002fac00000000000000000038e0001f58000000066a00000000378000232a00000008d64000433000000008462bda2a4526cdaaac200007de61867a680004270000584145caf92afa354800000021bc1f28000578000035b2b0a8d28142aa792a408a04a66e981dc7b48a7e277d9229e6cea8341a2ae6f9ac6a00000000002a12000000000000000344000b579f600d29dc81d48036c35938cab229ae45dadceaa19908000093000000000001dc6000028013f159f2a50000000193c9228c7e70b4000000
  | 48 => 0x6a59babb007e3b8a2a68cb80004c08dc00000000000000044a80003aba60052a80000a9115e24796a8b5900008018000a8dad140000ba200000005d98000a5c311000014c000000007969a1171f014eb53a0600001144000230e7f100ca86a00000000a3a0001526037c0939ff8b760002058ad3000000018860001eec251800001baeea118800077600000001a5e3cb8270000000000000004a81e883f08000292157eb898000c160000181944060b80900000000000000000017fa7a4117e2e58458000280a9d520b000000000000000000121c892a71a5208000000000000012e41468d386ec0000000000074100007c700000c980000002b06000000000001ff1e70000c1a93a44ce00000001b4600000000000ce804882ac21a8000c12b1ee1690d488ff15b6add000000000000001ee20000ec63b20000059988c4fa80000000000b24933668000007f28000bcf800000000311f0a75669e65ca0000000000299c4a612aa000035864d20ec7cd8fb03a627b43bf000000009ed00000000000000beda968865800042100000000000b84af4e49d2f8e0000000449e4be9f7882eadd800061000004e2b090b82ab6e0002d5000000009b7000028780000000000000000000000001090d77beca9ea671905c68696d213c1db800211306d01c5a97123a4bfd9f3ebc920ee00019f896d800049b8f740000000000000000000008be986403105c873b8000c4385ae97192480000cae0001c60b2a26f02e4994c9510c64bb48eee0f62e18a60a7b0af7a08200d6f7973e278448c2b5c79edd7e8610e2e3155f9eb3c9aa41d0801c0b3ee66b4f0b6828484c453d826c8645c13ae5901606130ce5f3974a4488c1092720204f18172c610000a311c82309c00063a864eb2eb04402c8000195194800020cc8880000000000000023dd507920a1de18242449d90c0380004ea9d76b156376a0001de0a4a9fe00000000c89fec5032fc2c4602505b10000c342a4c5df800055906d20002ea20000000a399fe6000000000000000001a3425414100140413146113e00000000002f9e21fa9fa00014af7c9d7c8705813e93d1d962109994b85016c2e612109702b6c454aa6c0aa41d300000009f69c1800019aa7a0c8b61d9a36200000000000000ab500000001e540002a340f89c145308000be71dac266800056e999c0000b3500002e418a0000a85121d9f40d86bb6c0001a5800000000000c70000000040e6609c4266b843d0000ce62ca8000707800000000004a8800000009ee0000d4c000000000000003afa6a8b5d2ed650a802f82496ae8daa858a6d175cbcb2c9634880005e7076eb6905de00008002ff000000031f23da0e5665c17fe8cd08cc38607588228d5f04d853c343b17671555a095a1c4b0002a18a78a3586bd8f4da20b102a73c00042e000
  | 49 => 0x14be904b600000000000780912056d650a33866e8000be307644b800040002f5b7c4a116761876cbc6209000003294b40000978800086686a423883c408c83a993b9f5fa4393f05a24d4616dd76ec830c3b78d0dde13397f22fc233052e000006e80000b1a48226d8000b2aa0d24865d4c21d0a1769c0c5e21c0cfc410877040c87d098f9b6a29d174072edf888f0a64c08b1bb631002f418f91ce0b56e960d38000123aa4ec661f4565709a057585b30000000aac683501e86465b20000256c00000000000002cac37d1c3f00003c87c5998ebe81ebc000105aa3183dca109180000261e0001b3a00017980000000c1ca3648bb00000000d5e70baa5000017380000ac1449238e9c38c8653bb18064180000000000bb7705c7dc000018719edc1e80000001b167ac000093eb1dc6bccac01679e64a098c29945830e00000002e84b4e0001fac00004740000000a87aebb9d48f4339f000000000009fa800392040a615600004b29f5e3269e6600023826fc92dcb8f8000adf0da717c72125bf9e7a5cea65200000009e6b032000105892e11fca4fa30a00013faa360b9d5b6888a199242017a1aa8031af02795a3a68ccc0000001ed0655800088b095d0001358000158ec5e8000a24aac286205506bc16766331a3623588df3adae3600000004480000731098a000086404e998c5cc9ac208e8000000047c9020f342f70000bb68000175800019e00000002942a8f17342ff93280001a847fa9b448fa8c4f000000000015a622209d037f239a99c00f037903142908b549671a0e8b0165e33123d814a8c046f595ceba316b6395281a06da10cc6f88bcb9b2fb977e800000010bd06b9c1b8d400005e04694c7412e22f5c000a288000b264000ac0a1023858bc6ba220486bfd3e21088a6093e000057d212c42c0bce23ea0a200019740000c6c88bab72339000034621de3fe2c70c016144bcf2ed434be432c41856e435e2d05c7a16852794bf81030e42650ef04688c2e5bd96aa3da81b40000fba9a89bea8e497d8a641da40000b023a427bc5a7a4da00000006e485002ef0208000000000000006b7000000027e200000000000000bbd8000000069242180005e0934e00026626cc8eaa0001d1663a19380000000322ad9400000000000000000000000000004d085b872d8c4ea18ad9600000001bf0000000000000000000969f6ab1620d80000000000239e7a8a85099e061bc690000c559c709fa40000000000000000009619e60000000000000075807a6001527a000240e98e0be00001fbaa7080009b208c894c0f300000000a7c4e7670e0000849962c0018db216b1c28ada23933fa25dca899620adf97fc000216c05221dc000000036809ec00030bc000000000021e00dc000000000003748ddc0000c4600028a4604066200000000000b385a
  | 50 => 0xfb9510000000000000009ecc000915000000019da000242217c000000014c12a58948a0f8d5c2a890800002010000258e000000000000000000000268985600000006342f0e35fb1ba00020e601d8000672823c6011a3db7114feaf40e6a0ef30b221e80b16669c967bc11e38038d245b31a9b93a2120bdba4306260d603d4dbb38aa9ca092a818c000000072f00004a08f800000d4709186c044b2b904bd8385000221405e31a00a52e6400014fc0000000000000000007066b550e0097000047a800000005dac538d648a2a762a6a8000bb807f56b1c000000140a7045df8297167c9b3a5be4ab8c7a9ed90749562494b8c96cea9110bf14120ce6a0d2f214283ba0000bd610eda829570b3e6ae2f080e62f98999a5de0002f52ab31aea000000000013ee0000000000000008feb54be280000002e500f9a786a282d12a3f000052b437224514de0003150be6973600005a80000b806e40b32000000000000009371dca000268e96300000000f62b931e6a0001a4a4c90cee2645874906800008780000002adc0e2839054606ee00008116e2980608800002aa9814000046a0001c5c920044800000000002ab2ae116b2b63400007ca0749cb198400000002f01628c82137479f29840fb125a716000071280006c20000952ca3290d8000bf31aae00a987a316115839d04a438d000000020d0000932e000003f58d95424c1983a00000000c971eca552e8489f2e040002fa7000235a983a84e2131b023a388563c3e2626bd2e8024e9ba41fead3161a18fcad60a90454f168b0c0da415cac2a3d18b948958f8a5070c3a26627d43d805954aa17ac000294849b1a8e00010e786daad02b61b2a237a15600007de8e0c00000006ae7442c0200017140000000000245339a00000000000000000000000006aa6d0ac13a250bdc4990000000000000000002654000000000011747e68000000000000011c45dda6180000000000000049c03890001b62c06b19215f1d9e00000002cf2ebcc130000bcc800022884ac1498000000260400000000000000bdeae9a0003006733a8940001d38768250a2c122029348b2e03992b610e80000001514452000062b88ba100a42a0001bbc00030ea00000000002db292326500b40000a27a378bb1000000000000000000000000089c26427466a3012d5cf6000288e1a71fbc4ef22e700025c2000244000018c400002ee1c98000a45a99870f568a0abc9188bce92a0002fd03db0d19000081400000000002ac595015044d180007f7a4e0007a9b61d682175321bb200025e00002bd4767064b730ad3d0bb2a2243a000082a000068b897e00013ab000000000002f100007f952fa2df3362ac300022300002dbc0001d3917cc00062024a68190cfe5c98c267a02d02c6e017626900007a58000391989c0002c4e47331
  | 51 => 0x57494100002e10600a462a9d94f13b0a0a00000fe0b7894980007a050f219d2ebd9a4800045001a400010de00000000001f18c5aa5fa7a6041600000006a400003eb80000000000000278e0002e4eb08985a91dac820000000a2e800000000004cd000028b44b98468000abd8000000089aa1280006498df800000000000000954da5c85d8a3e000279c7ea8000886281889b0904bfd090c447968cac51fb07aa91dc92bb10c67e83b696a1ad698216008de686e3ccf09c6bc9f00a810000000264e6f5000031bb18e0000000a3f800000027fd0000bcf64780008dfa446c5f8b5e99ab0f200011da5d81f8000000000001820000000000015dc0a3a4d8864a3c000000003760000526802062c976202f2beeb50000000000004d801f8074896a0e8134c000000000000003ff1e3c000143e0001e0c713800000000005ad1f9091c8eff00000000002a8aa0722540d0a51c6df1c6881786cc3c6ede453d2d610000f7b94ea708914a66c2a7a88842f21314c605900c400f212a0000bfbb17243bebfa1928e66409306c0000000000000052300005de0cc2000000000000000002aca65a0000000230c4b78000000130a00005840001ba000000000000000000113d00011962a2a2d200018e49d29a262f7d6575b296a6375135a06fa7f844a597a00010cd23cacf0039e89a23180000530a6e000234893db17cb1b25a6c26256a6c55b123de8aa400001f600026ec0001bd20000000000000000000000000000238d684af08000000000012705b4409ad2647e8000399000030a00005faa3f7a6599ea00011e1000000004340000002e23b918288275247a00000005918f8c000000028b8ab800000004c30316000000072317aebfa27c0bb099f62aa244e0d42cde00015b80001fe90002104000194036718a87c300006148168000030000029a600000005bc856c0000000343000000000009962bca60680000001c480000d123180d3ca582b1c5341b5aa23000000030a4122ce263870e32172aaa8000009e740a1461361ca8be19f7a8d6dbe4555965aaad000000027940000000000146000000000ca988eb2c0c328f9210a5bc1848c0e000052f5b663bc800062683e40000000943045bbf2906c0000000be1d5bd2e7800000000007df802200000000000000ac98cb2000157c0002160b1bacfa6be0d5d21719961898446157a13000001128e503ce04f0c0abcd800000000000002b405820000000000000021ae1b8800034280000001286000000003600000000000000225c0002d4600002aa00000000002c59000255a681400059a80000001ece70740002070e9293c80782b1937ebdc1a142ec2c0e5b9000000000002eba91c000000000024c226000000000000b58000000011f4000094a0001478000196200000000002b1a05f0000c6200006
  | 52 => 0x43997eb97091619486c855e800000000000001538000000000000000000000b8800006439364000125cbd7913842f887836b27e869d1b1472682668f98676000122a1d00a5200023c80002b102fe0000a8a9a1e0001ed4000000084780000000000b6c0000000000087b000038480008cca26404a000036ba80c00000000000000bdd0000000000000000000000000480800095d000000000005cf9b7459880003cb0000c1c078e49da1f00bf000038c05fc0000884c46c00016c84e22ed68be81f9d1a9452c94b666f72a42038c3af31de00003ad904015c62d83d022980006a3000035cad6ea2dace67c90000000249a08f80006f1288000000002c4e10000000000001abe43b0da80000a36000000000000001da92420000000bded12e00e1df05108000000208046fb10a0000000000214e00000007922df800004c8466056a000000000006240f3601400000000001c0c000138e5f127f00000000403000004981d60000000181c000b61800015918b800023e045f1b8600000007f480000a116875a3800000012e6a179fb417ac00018d24340002c884d00000bddc0006fc19cc6b21f6c0001754bac80002e7177a485c00098880000000000000000000007bec400000c6b8000000000029e00000000c4aaa881025478000a2e29e8000310400000008e5400000040000000000b660e0400000003ae08041d7000000000000000000000140800000004820000a6b064d7b201a065806f8c7885d00002aa06b1000027c25780000000637000099289100002af283580005be8f0ec19000000000000000844000083a2978000aec9c8427108237c5277ea5da5b3a63266829580001841d4a000077e4ba821f0000000203e9a82df01aa0e6ad823cc80000000bd10cb903e2129e76974800091985ef0c10c50306a93c75e8000c3e83e726a8d5600027acbe65480722b09a00021a480e185c231c0007ae20163b52c8e7932cf60001954502cd5066e1924a1543a647e14465d900001ea89fa0000000000000028515e80002d1821380000000000000004411400007838000227800055400000888f669608bb6959df430001c9c9e8800000000000000dba812aca01458b8609799284b6a76e03b8000000296e0002e2203f80001930a844c200009359e4a00000006140000000000000000000a5d0624cc0000581b1b44388000000071a00009d50000000165df2600023ca1880d7fa320e2883a269ec4e80429c5000000000002f54000788800089c8e3a000000000000002f100000002636000095e00011ee6f280004f08a7c00000000000000bfb000000000003b10f6e000233600000002270000000000000000006c0110200022f4000000017a400000028238a1153258680000000000000000074d1e2a0001fce0000000c50af930000000a3b8
  | 53 => 0x2ae400000000001c106459c2f1f486e600000000c1800070d40003c59e6300000005120d92b3f000030827d2000078479129c61739eeac8122e20001f639a0800048fa5480000a4cb84c000000191aa40aabc000122e3e8a2fc31322480ff00000000012c69a3aa5f088d23a19e5cb7a9f5a538c0007a38000000024a1ebade3364037f00000000002598724cda20001cd25d100000000000000249663d8000928a05c0000000000210871d800081100001631ee40000000013a356000213a00024e2000313e9111c04551949629c53e87d22236b5b00005fa30ba74915740000000267800081880000000b340002052aceaf1416fb1d29b31cae000218c00015810000000000028a4758a2c4ba0000a0ac0007fe800000024c68bf80000001b600000000000008e000113740096ec9408000669a07c4f701640000a34a578ffa000302000000008c1a06850a00002ed0000000000069880000001e796e228cc6958000a3e8d58ac882ba000019c08e1ffcb080000021400072f80001d2a686345882d0000ee61110cecaf380000000000627a70c1ee8000000123a0000000ad980a400000009ac29a000029443f6284498f000000029e056789d2960000000005fe9e980000000f5445c195290b0000b6380009bd137200000006c700001c62ca280b9d983c78ba822e31f6b98a5960000cd700025aa58602d22afc8c0000034600000f66a9adac1cf8b110001f2e8ef9d9ab6e09524461d471a602363ce03b889d872e8ba1e613f90abe000273c000189600000000000ac89c890e562d129629b00000de9670a51843eb212c3cb7e800007c03cb000000000026c2027270613498ce2941a329d21a203b90bda9b525f8be170870229950b15addcb348fe099e939a5fdabb613b854a9e752407c8a2d6afc83835ca1a81a7544c0045a24298b0014c481d8a6a223d24101d2ebdf4c0ca758ae8000102ab4b80000000000bdf84005dd297c4728b299d30000ab1a17e76394b022c244c00015c445bab1600000009f7cbee5c031907502fd42670ea257f80b6b49247cbe4abc02ce86d629995f2a4d1f9d97313c4687279e3282bccaf72c72159a1358da2bc8109627a336a57eb371d6e70a58708c9b1cab5dead85e504c68bf4ace95b2b00bf99f97969233ab71aa3815823e3070113a3e694a649a8b728e29a7c15c55aa5d215791231fc6856073a07d03ea50b2813a6e889851b1914a16ae488528bdd86c3036ac4a80189f857836dabfe8800c00884219800014d59d41a410000080b38095f681a6aa5df0000a2b000098a80a29f0d4c60000a80a210000000000093fac2e00000b87f58e7ab8683185ac2d2f000296c173c2ceb6823536de9cfc064a9862d0703a47d83875010cc676eb0188d99cac9108ff618080000001f1e000000000000000000000
  | 54 => 0x2ba0a83c659ad10b38800066489ce4a480d031d92b06181bdc5960c9410d9b269fd0b747c813ae0001792000000000000000001dc0000190a40880006e600000001bec0002aee74c09bc2e0ac781c70000c0300001ed80e099593e0201800028f00000000c062860bc87d989e86a4b022be088f000000009a6c35300024180000000b98294cb4d882800000000002aaa000209c00027421bfb082a8a00ac00280003b42e7a55385ba8a2078a91626cac1880000002f3400000008020cd65c8968280552580001ce20ac1b8e03d1e9e0000000170af203de13d605b8000890254220864c4000215c64700002e9800000000ea0000cfa76d000071b000000018167bd91aa6c28000b6a89fd01a1eda9f1800057681a60000000455893c000000000000000745254c598a720000614000155ea341ae243a4000140b0941fd000050012fe00031c4000233e1420000bca091a3e7800c000144c3199fe59de14d809081ec01794f2b2717c60000cd273f800090180003350a0ca1c265a48011bcb4804a03d1099388c8838c561a8a8f7a5bc30e5c0203768060000ba4741aa720000000000021c2cc2e9800021aac7eb084c2289b4c769edc80aa0dc6af03debae12a50001ce4000000000030c64df26068fcf19a4700a76acfa8d24b1093261308501b523ec5a52b78000251e0000dce0000000000000026b00a0325913c70002d400014160000000000157825a0000000000042d9fa0000058653312bc0000bde8a7178a3f000004980000b0705e404760c0282582c000000000000006a3564c0002aa129a9146608800014f90f1000251a00005246e58000862800000000006b40a30000286c00000003d7ac3e019800090e1ff2000000000022b2be3c00007f8000000000000000001d200009a9000000018da69500000000000000216f00000000000000bff21d81f5032d5f7b086ace04e63f200000001d68ada8f9c0001e12a47971d60d8000b98c000b1213a25b015168e880008f180000000000566c000000000000022b0000000000000001d126b22f290dc629a9780001e6caa50f880002e940256ad26070202a638000a5980000581c6240d00002d09f2d00009380fca7bb74ec000000184673322a89a58a580000f1839b0000c5d000000015ee26100004c780000000000000000080c8000000207600000000000000915b1b0141a1b4000142e5888000c0c1293017050c0002340382800000000470cd00004538000bc12de14869f290000000000000000000005a2df7c90a1a0c5c2800000010cb10b029045e16307ceab2c000000000027660118e2a1e5062c4928e0c00016988750260732242600031acc4d2a2e000000017800009869310000000023e0000a1a1ff015123f40002a841d813ec24ac000000013006f191800016ba3d3090680f
  | 55 => 0x9879ea91affac751e14bc32bc60001f98b369252b8e899278ac000b0402f077aa29268113b604300000dd2ef89e400000001e307350000985a6f60728e004d20b8a3cea4986b3a9fc389263263e10d4c4c87a44e00478c0d1a9e97921a09739f6805fb14c1fb8cba0742ae05e99cb815021647a91b580549c0a65c87ac694a1721f713a857291ec1ad1f844a398de1fc03d218c0000a95000042d069e37b9082280c9ae4148c427b80000b3318c83aca7a8000000032d0000bbb88c425d80007efc0009c816c6000088200020028af2d72c51000019ca0dea481e70b6280000000000aee000000003c0000000000012fa000000012fc14a51f000000000007ca87388bc80005c6acd40001b4aa4ca21a0638000ac60eb475626ac75e2a6eb648ee88698c2a6e5060ec0f044c7801f9455881d4abf14061ec80000002d880aad280b75000000000009f06fd61969e9400014d6b3f99b6563049057019ac28aef6a24985fac2c03ca8c500003f30000000000011eabda51a800000000000002ef47220000a430308351254754aa4ca11d80000000000919254a00000000000a7a7cf1d2a0002b800000d34000066cbbe82cc5f0c000a4e800000000002fb05e2311000095cd23c04a87e8350af6c9ef6b621900f72b8300000001fe39850000000151c000126458902748a6108843b8000000000076f8cc0aab1aca00019d40001150000000092d800000030e64d29dce8f11c64000000000023d60002628bc40a1615dc000000029e000161e0ba8000bf215b01a31ca22a2064167c245e36688b2bb9a312b3900005d457860001bde73a00001f30a0a7fa082f00023c970d8d1c3cf2ec8000277c0000000548000039e29cc000059830094584cb0df63bf80000001092ad296261549266000000000004de78e16a4a21a8b4a33841e522220aa74231e8a3212f000000000020566b24000bd0000076502e800007f2aa6f1f4bab225e00025224238000291912663c800000001089ce00009300000306edc87d893902988268b0b000000011281224000000000062f000000000e869e2337c0f96b8000000000030261e20534c3a00000000e82000000000031860000000000000086c914252dacc8000000000000009128b1c281c00098831ce0001d7485e000074cc0ccc7623acc3b09e9021800000010db0001a86aab80000001bfa000000043ced80000000000007c0000307400018e600000008140848000044e0000000235000012086180000000780800055503eb7e4873c56290a47d303320001a3c2c9c00072c04411ed1580bd29d8c4f31bf624ee52a4f013b23b494f82dc1d126dda6840000000000048803500006b2ee86a41070e8e3000004621c079e23709768d260510348000174279822cc6acdc7477085bcb4212ce19702ada5920c24e704c
  | 56 => 0x5061b0d14000093e000234f8dc820e000274e6f00dda0000876000259e02a80000db000075219e046380006ee31c200013ac6c680000000ccead42a6487d1f5d6920000bbcaba65291316580a6e65e9314600000001f1089644d866860386ec749995a47a26d80cd9c98c4541629ba31780000000943a1ee5791492000136d5fc2cc0aa5800054c00480002d7bad480000000000b8b80009171d5c06400980000000000000000000000001d549dc16045580000109e0aea830000c1bef1e0000000c8400009e094e80000000198ee44b83f02c00b000000000001c6eaf3000000067f8000ae81f4233e24a81fee2f0000000074620a00002602847ec8a00013af000000017e4c341260000000241600000f80d32455ae48c16b4a8000153266484f800000021540000000b2d9d6643fc3f3ad1a6be5272a1687f2a191682efe2abac3a00d16d070d2a1a8dac982bc2a95cb8f29d830f07f73721f619f5c000881aafe7e32f30a8b243ec83b0c882d0437388afbe00004a261f9fae0003054bb3ac906d582be000000055cad7554a297e0000c2ca9e26e200010b261f16e800c23da000136c00028466161c12413ad1c0000000000214800000003340000000000000000000002c500001ee8b11a3ba2c58000000010b0002dcaa3a2ac400000b00002c6600000000001a0a30e0000000000000009720000c0e80880002a4aae60a981e06ce163ac329812106a92c90b93045baa1f618c47a2000308e219d5088439e3e00007100000000000000000005cd813000000000002728000000094e69a9d6a00006321b800001638996a0e080a6f817068220ca40000000954ab9c74b000000000001341b1141ca2ac6adea426710d2a0000604000192e098a0a65b71ada0002fa2012b1ea404adf207e97ca61b96de7a1b12a2a98d04a8c9c729ba8dcc20980003fb00002a7000033c06367d6d24659e8d080001e8a00015244fe0000000000000000001d581b036200000001df40002cee0000000000277426d4b7a0000000010400000000005708da69920afc6c180008e59ab24ff907ab748000bd64f3e00014dcbdf172e6dc8fbea0a8fc60e91d500b0904c60a85f2133000000000002ecccdb5f70000829003d000000000000002928000000000040f27971a209d30000afa038c9c286f9238ae89fa25a0101a0d754d157644bc9d1a2c80464d5a000318200000000001c3e000000049880003f2849e00000000000000656000035ea16500000004b1ade55f828341620e147400c146aea80e56b8c6859100006208000b656e08a73400000030d280a5434ab4512b05500000000000c7e072493b0381000296a3ba892e27e0fe2000077400006be000000000016344b6000067b083c70c0000000136e3238c5c0000000000000000000001ab000056a2c7495
  | 57 => 0x163e31a9402b80af483c425558c012a6ab3824042400008b6ae0033d8000000000063d229600021fea7280000001412034cc92a8000003c5000086b1c0b0af00004de2edc0000000000153a0002424abddab600000000da80000000000be99d8000006a00000000519179e00000000000d8c6c3000000008a831b538219270aa0000000887800001b492c9c927e416aa956c5900008d3a3525a82c5b02deb8670948660471bb74d12e10b5512782dba93626fa08625717883ff97967f099b4461af9400028369db0f202d1dc1f958000076b8000a6e28247e7180200000001b180001aa99d6b6e8ff2c1b8708a77000000006b2be0223a0000000a7103a858ba7cc00013880000000000095a000140fb522a6600010e460318b06b009ba0001ebe3f3b0b6000000076c11148c58000000124432b2ab800014cb87e8000a180194c2d06b670900000c29b34397a4900000000000280500022ca0348000c1e0231c22000020a95889402282b10e6c6c458999000024c9541a16232a4d027d944a713432755a141a04c84d403871222c7ac7a4631c0eaba8efa72a6f426a3c000a9e864499b800075385c40000b1a082811b5858a446b4b0ee8b864688a3819a64ab060a39046629bd75800000007199c1c0002cb27c18762000156b733d6e08ba87ec01c9502000235c0fc1509b3a00007099692a7ae80db572f6007a80e59d82ee8a0c0a2a4b0877c000000013fa21cb15f11c2cdc0004ae080e3b28a101831656000255e8c42238b81ad7c9be800012fa6c084c818a0001838872800035aa3228e61c9400015f10fa1bfe101000000000000001b040002c8c000000000018180000000a25810a000000000027ce46eb1f0378a7262c4130ebad8ef8000000068a87a08f95f41a2a0000ba98edec6aa39951a1b105328bac0269f7877784ec3a500000002d7a00032008858000b55abf87d400008dd4000204000065921668918000bd0c0000002d320002cd8b1114fb89b969d0000492ab010a68b78c74176000000004d6aef30dc000189400000000002d35b402ea81d5000000000000000000000159a45b03d40003050000033a000000000000000000000307a91a3c00e9ebf6aefcb3aa2c4b969c325af40008721c3a4e5b002af8a27432a0f5000000000000bdb57b29d20002a6aa30299a62928d682380006b32a9736c0000b6311ac00000009ae196eb0680000002a080000e9a000000061e30f828380008be400001c4c41184a5a020cdf28876b012a7b02a00d982004c680000001b52000000000000000000000b528000000000000028549cf8000000000000006dc875adc2784079296e1b6857f2a746ee840c3710bbe82f94266e308187429dcc000248800000002a60000918845c3060f2a10f000000000000001e0888493d279485541666f
  | 58 => 0x3763f10c8c77ca3fa5742e72380800094480005f689a8a5694e2000192c6d92f1cb2f9ef200020fe81c80007bfac12b55e46a2d580000d48e1e4a404943c4405a00000000000000000284018640000001e260000000000000077b2cc40002fc6c4f11a46bf860824d800000000004cf9a7b8db206c0000633806f1e86e1d7659169668c15af12bf71ca18fa2898b1296e29d71ac6c378cc851c0000295000080709c8b7c1dfc000000000000009a201ac1c8a9c80002ab05e01aa326229b5000036065e0000aa980000000ece13680005a89c3c198319e0000000c809d3a00005d200010148bbc1e24ee55935f306b87790c54c8530a80001f56bf3800000000008fc000032e264400021c65721710157008300000002c61f7600000005fb922290080000002db753a896c000289000001a270680000002dec39ca83a4852b8a00000dc02ba3429caac060000000000307c00011b00002a069d91250279ad660d6e20c5150f2264c800028e0556b02150e5d38000000000000000000000000531011442805d4ad914a2000000026c81af3d719f24959b3062e9e687264dbe2c32026000300800008da2b985105e44c78a7d2dee42b286600000002c00000b9f2d68afa12242d22eb075cae929b927a43e4827678261e6579af8d2ee0ab28e717b80368921a3e12d42232320bd1883669f98c60001d440d723170adae548b91f0e0b20cf400026fe000092a000000000002980000c900b72cf47ef9dd4b5ab1bc000204200000000000dc24430000b87070a00000009a40a20574af56000252e6ba0f7e00009b3000164e0000e5ab1f2e6812d1eb6514b0467ffac5e34f81da0708000c350aba0734000b7580000001a3a0002d2b56c878c00000000cb000076c8bba00000008448594a041f8763b2b9e40d80006a61ee69c009b06891f4e384199e61d80000ad18444365d8404800000000000c4b8ae00002c140002a5240c090e0001f0482d9e8c53b00000000d400002ada06090ca0fbc00053507f88d76630276a9c097f000020c119a00026c4426800000000007d030fc047cb0a2da952e08d1ba83c1800040703c2c54ae16c1a0000b1dafde00000000001b3c00000007dac0000000a000868f7c000000000007500002e34010d4b49e4aa889b5aee23d08ab067bc48a41c2374b838396b058f4008322b6c81b11e630a4ba71410784628c360212e90265497c0618330894800000000001f98000010037600016660d7d84e72a8580000000028900000a7117aaa940006b51f54000080c8b601cc0000b438d7e7c2bab8d68bf825fea00aa488462106a80845323d8e58036d68671a9f34c7f1b289f6024841f29801fa8364aa396fc00022b48a0096ea870622811c000732a5ba0000000000122c000162a00008692c380000000cca0000000ade80000
  | 59 => 0x15f0000000000000000000000893800073c000027bcaea00000000000c720c9000045909e403883f6a5e857022652d65a206ba7111ff81d381247961116b1a1a7692d31364a7800b2196586000150cbcb80002bb2d9a169800000025f02f61f692e38000084800014883b440180000000000000000000030c4b9b97b400000004ed000000000009480000057a35e000000054d1f960002167bb7888100014767398f562ea80000000000000000007b9b9e0000000000000000012ba0000820000000030c0592000230200000001858000561abae00019ce5719f32bc8a924094ee7d4438b50c0aa92808c10b96228d6e000198000002f604e074c2180000bfc003200000003f42780be5c33c53380004bf25a2000000055704200f3000000000007e0a6ba11b9eac857a51079400007e18000000057e6410000000000000024a4000000019956540000000000245025c08c20000000a6c12b297b97161960b890000a1b3ec8aa1662a8b2790a8229b80cea8470b44a05201323d1a3b00003845251f3007f65720001a3800000002760c980ec26fc00008ce00000000000b22c689a9ac5c198600000007559fb600000001148000000000000005122819dfe80b1e9f10e2852000092250393d400004066ef931c0001160110318c0001432000098e0001aaa0000000000011ab9da34c25ea4602d0175e00006de0002b9a9f2800052280000000000b4fb14846a000000000000000000c059
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb71859cd20440017c30539a4088022bc2197348110005b9c2ae6902202cb70855cd204400176708b9a4088002ec2117348110005f1c12e6902202b9f28798d20440013e30f31a40880473c1da634811015df1414c69022000be18298d20440013e70eb1a40880ae7c21d6348110005b9c2ac6902202cb708558d204400176708b1a4088002ec2116348110005f1c12c6902202bbe08258d204401d9e0ec31a40880b2dca146348110005b8c28c6902202bbe28218d20440017c30431a40880b3d4d4e534811015df1414a69022000be18294d20440596e50b21a4088002dc616434811015df1414869022000be18290d20440013e50e21a40880027c61c4348110007c8a1886902202bbe28210d20440017c30421a40880067ce1f624811001cf843ec4902200acf076d8920440077c50fb12408800ef821f624811015df1436c4902202bee376d892044129dc0edb124088002f86176248110007b1baec49022000f6075d8920440017c307b124088002f8a1c624811015ef1438c49022093be2861892044057dc50c31240880afd8a146248110005f0c28c4902202bf618518920440016c30a3124088003d8dd46248110007b03a8c4902202bfc28318920440017c30631240880aff060c6248110005e0c18c49022000be2879492044057bc50f2924088002f8a1a524811015df0434a49022092be1859492044001ec6eb29240880b3d81d65248110007b1b2ca4902202cf60659492044057f85072924088002f860e524811015fe0c1ca49022000bc1839492044059ec6a72924088003d854e524811015fb0292a49022003be28754920440077c10ea924088002f8a195248110005f0432a4902202bbe3855492044057ec70aa924088003d8dd55248110167b03aaa4902202cf62655492044001ec2caa924088002f8e0d5248110007b129aa4902202cf605354920440596e50b9924088002dc6173248110005f143c64902202bde2878c920440017c50d19240880aef821a324811015df1c2c64902202bf62858c920440017c30b19240880afd86163248110005b0c2c649022000f63758c92044001ec0eb19240880aef8e12324811015fd1424649022000be1848c92044057f43091924088002e861232481101fdf0c1c649022000fc3638c92044001f80c71924088002bce1932481100057843264902202bfc0324c920440077c50e992408800ef821d324811000771c32649022000be2864c920440017c10c9924088003b82193248110005f1c2a649022000be1854c92044001ec6ea9924088003d81d53248110005f1c22649022000be1844c920440577c70699240880aff0e0d3248110007e1b9a649022000fc0734c92044001f84c69924088003f058d324811048fe1a9a649022091fc0534c92044001f86869924088003f010d3248110
  | 1 => 0xd093a260880025de15744c110024ba42ae898220359b6871d13044001a6eea3a260880034d1d4744c1101a6cac18e89822034db2801d13044001b63003a260880d32dd80744c110006d9b00e89822034d96301d13044069b28603a260880d36c880744c110006aa3aec69822000d9474d8d30440016ab0a31a6088003551d4634c110006ca3a0c69822004d547594d3044001b28e929a608800e7521d534c110006ca3a2a69822003bd08054d30440693ad0f21a6088002d5616434c110006ca3a4869822035f924090d30440073a90ea1a6088003651d1434c110005aac2e649822030d5475cc93044001b28e9992608800e7521d324c1100056a43264982202fd54754c93044001b28e899260880027c21d404c110007c8a1a809822004976859cf20440012eb0b39e408800e79a0a73c81100747a432e79022000ae4864cb20440013e70eb2c4088002f4e0d6588110005e841acb1022000be38259620440577c104b2c40880027c61e6388110004f9c3ac71022000b738558e204405b6e10ab1c4088002ece116388110005d8422c71022000be38258e20440577c104b1c40880b6dca146388110005b8c28c7102202df535394e204405b6e50b21c4088002dc616438811001cf94388710220009f18710e2044001f228621c40880067ce1d62881104b6793b2c51022000b738558a204405b6e10ab144088002f4e0d6288110005e841ac5102202db7285cca20440016e30b9944088002bce1932881100057843265102202b9f180dd520440872ed0fbaa40880cb5ca037548110006b8c06ea9022032c7760dd52044001ae6c1baa40880ca5da1c7548110024bb42ce69022000975859cd20440011ef0cb9a40880063d2197348110004bbc2ae69022004974855cd204400136f08b9a40880026d211734811001cf343ec49022000d6475d8920440016cb0a3124088003591d46248110005e2c18c49022004d6475949204400178b07292408800ef8a025248110197b1284a49022032f605094920440073c90ea9240880b3d8d415248110005b2c2c649022000ba5848c920440077c501192408800e7921d32481100057243264902202b9f0875412044001ec2a4a8240880ae7ca1f304811015df1416609022000fc132cc120440573e10e9824088002dce153048110165b842a609022000bb3844c12044001761089824088003f04c93048110165b943eea9022000d7276dd52044001ae0edbaa40880cbd8e0b7548110196b9b96ea9022032f6372dd520440017c704baa4088002dca1c75481104aeb9438ea9022000d72761d52044001ae0ec3aa40880b3d8608754811021eb9b90ea9022043f63721d520440013e70eb2a40880ae7c21d6548110005e9c1aca9022000bd08359520440017c704b2a40880aef82096548110165b942ce69022000
  | 2 => 0xc62cc91001cf8404ed19220009f3805da324412f8eec0bac64880035cd81758c91015eb3902eb192202bd72205d63244057ae240bac64880af65cca748c91015eca994e91922097cb7609d23244001b66c13a464880af6c882748c91015ed8904e91922097cb7605d23244001b66c0ba464880af69c81748c91015ed9102e9192202bdb1205d23244001aacebb1c6488003659d3638c910006ab3a8c71922000d967418e32440033e50cb8464880067c219708c910006e9b1ae11922000dd0635c23244057ba664b8464880af744c9708c910004f8c06ec99220008f580dd932440019e301bb264880023da1a764c910004bbc2aec9922004974855d9324400136f08bb264880026d211764c910004ebc1aec99220009e7825d932440013e700bb264880125da14764c910004bac28ec9922000c76851d932440018eb0a3b264880033560c764c9100066ba98ec9922000cd4531d932440019ac643b26488003350c8764c91015ceac1eea992202fd5753dd532440011ef0cbaa64880023d219754c910024bb42ee8992200097585dd132440011ed0d3a264880023d61a744c910024bb42ce89922000975859d132440011ef0cba264880023d219744c91001cf9400e899220009f1801d132440013ad0f31a6488003351da634c9102e5e8c04c6992202b9d48758d32440019a8ecb1a64880bed5215634c910005ca422c6992202bbc48258d32440937a700b1a64880ae75a1f434c9100066a3b686992202fb5685d0d324405778d05a1a6488003351d8434c910006caba0869922000bd18010d32440019c8ed99264880063d21b704c91001cf8404ec1922000977855d832440092e90abb064880026de11760c910004da422ec192202b9e4825d832440013e700bb064880125da16740c910004bac2ce819220009d587d8c32440013ab0e3186488003b1188630c910004f3c3a641922000ae4864c832440012ef0ab8064880125d215700c91000cf9432e019220019f0865c03244001ae70ab8064880035c215700c910006e9b1ae01922000dd0635c03244001bc6c4b8064880af78189700c91015ee9992e0192202bde2325c03244057ba264b806488003784c9700c9100263bbb6caa8220039748754d50440072e90ea92a0880125da1674cc110004bac2ce99822000b558518f30440073ab0f29e6088013559d653cc11001ceac3c879822000b558590f30440a53af0ea1e6088003651d143cc1100347a432e598220039d587ccb30440016ab0b9966088002b521932cc11032cbb43eea9822037c7760dd53044001ae6c1baa60880df5c883754c110004dbc22ea98220009b4845d5304406f2ed0e3aa60880034ddd7744c1100069a3aee89822035cb760dd13044001b66c1ba260880d76c883744c110024bb42ce89822000975859d1304406936
  | 3 => 0x7b1220009b7845cf624400136908b9ec4880467ce0173d891000572c36a5b122000be18014b62440092ed0b39cc4880025d61673989104a6f0b86c5312200497687dd562440018eec1baac4880035cd837558910006b8906eab122000d5775dcd6244001aa8ebb9ac48800365dd373589100066bb06e6b122000dd360dcd6244001ba241b9ac48800355dd47358910006aa3a8e6b122000d97741cd6244001b28e839ac4880033598873589100066a310e6b122000cd7601cd6244001ba6c039ac488003744807358910006b23aec4b122000dc473d896244001ae6ebb82c4880035c1d77058910006e9b9ee0b122000dd073dc16244135bc6e5b82c4880ae79209751891015eb2412ea3122097c77605d46244001ae6c0ba8c4880af59c81751891015eb9102ea312202bd71205d4624412f9aec1398c48800374d82731891015ee9104e6312202bdd1209cc6244057b8904b98c48825f35d817318910006e9b02e6312202bdc7205cc6244057ba440b98c4880af7448173189100066ab9cc631220009e78758862440016c90ab10c488002f120d62189104cdf1c02c43122000d6575d4862440073e1013b4a4880027ce0176949100063abb6cb2922030d56859ce5244001aaecb39ca4880c3551967394910186abaa4e7292202bd57529ce5244057aaaa539ca48825f35d827394910006e9b04e72922000d56509ce5244061aa8a139ca4880af74882739491015ee8904e72922097cd7605ce5244001ba6c0b9ca4880af71c81739491015ee9102e7292202bdd1205ce5244001a6ce8a9ca488003559cd5394910196b9282e129220019f2865c252440033e10cb84a4880cb5c2157094910006b9b2ae1292202cd70655c25244059ae6a6b84a4880035c54d709491015eb9a92e1292202bd71525c252440013e301bb2a4880025de157654910004ebc1aeca9220009d4835d952440013cf04bb2a4880027ce01765491015cba43acaa922000b548359552440576c904b2aa488262dce016554910004db426e6a9220009b584dcd52440572ed0f29aa48800355dce5354910024bb42eed992200097585ddb324400136d09bb664880026d61376cc910004f8c06ed99220009f3805db32440092ed0a3b664880025d61476cc910004bac3ceb992202b9d4835d732440092ef0ebae64880c355e0d75cc910006aa41aeb9922000c77605d73244001ae6c0bae64880125da1474cc910004bac28e999220039f2801d332440013e3003a664880ae7561e63cc91015de3414c7992205ebd18098f32440616a90ab1e6488002e521163cc91015de2412c79922067bd38058f32440616ad0ba1e6488003555d743cc91015ceac38879922000d557510f3244001b2ae821e6488002f460043cc910006b33aec59922000d667518b324400178b063166488003b198
  | 4 => 0x344001b66e9b82c6880036c1d37058d104f6e9b9ee0b1a2000de372dc16344001bc0e5b82c6880125de1d7518d10006aa41aea31a2000c77605d46344001ae6c0ba8c688276f46026318d100047bc3ac631a2000ae48258c63440013af0eb18c688002d52156318d10005ca422c631a2000bc48258c63441397a700b18c688003555d75318d10005cb426a631a2000ad58614c634400136d09bb4a6880026d6137694d10004eb41eed29a202b9e682dda53440013cb05bb4a6880027c6037694d10004f9c02ed29a2000c7576d9653440016ab07b2ca6880df5c9417094d10004f8c06eca9a2000977855d9534400136f08bb2a6880026d2117654d10004ebc1aeca9a20009e7825d953440573c904bb2a6880027ce017654d10004ba43acaa9a2000b348459553440016a906b2aa688002d92096554d104ddb9c02caa9a2000d37749515344009aaee729aa6880125da177690d10004bac2eed21a202b9e682dda43440013cb05bb486880027c6037690d10004f9c02ed21a2004976851da43440012eb0a3b486880025d61e7590d10024bbc3aeb21a2000c77605d64344001ae6c0bac86880034d9d76490d100059ac28c921a2000d36751924344009a6ceb2a486880126de1d5490d10006aabae8721a20009f180dd943440012ef0abb286880125d2157650d10004ebc1aeca1a20009e7825d943440573c904bb286880027ce017650d10024bb428eca1a2000975851d943440013e700baa868800e7c2017550d10024bb42ee4a1a200097585dc943440013e301bb086880025de157610d10024ba42aec21a20009e7825d843440573c904bb086880027ce017610d10024bb428ec21a2000975851d843440573cd043b08688002796087610d1015cf3416ea21a20009e582dd443440073e501ba886880027c6037510d10004eac38c621a2000b558518c434400172b0831886880127561e5310d10026ab3aca621a2000b958494c4344001e2ca8a988688002d56164310d1041dcac248621a20009d78750c434400172f0ea18868800365e1d4310d10005cb4328621a2000b948650c434400172f0aa188688002e56154310d10005cbc128621a2034b968050c434406972900a188688207a5d814310d1040fc9b028621a20008f7865c843440011e90cb908688003e450e7010d10004bbc2ae021a2004974855c04344001b2a86b8086880d3740c17010d1001cf9c3ae021a2000f91435c043440033e50cb8086880067c2197010d10006b9c2ae021a2000d70855c04344069ba706b80868800374d8d7010d10006e831ae021a2000dd2535c04344001ba2a6b8086880037490d7010d10006e8a1ae021a2000d91435c043440013e704b80868800275e0d75d8910004ea41aebb12202e9f3805d762440253e30139ec4880025de1573d8910024ba42ae
  | 5 => 0x297a167458c200052ec2ce8b184000c9d741d163080011bd0faa2c6100023761f5458c2000567c12e2b184005acc825c563080014bd0a38ac610002976147158c2000567c12a2b184005acc82545630800159f04a0ac610016b32094158c200052f42882b184000a5d8510563080018bea6bb4a61000e1fe1d6594c200052fc1acb2984000e1f539925308001c3ea6b24a61000a97a156394c2001c3e42eeca98400387c8759553080071b90eb1aa61000a1fa157690c200043fc32eb218400fc5e635d643080018ecc2bac86100021fe1d6590c200043ec3acb2184000c3e75992430800187aeb324861000e2fe1d6490c200061f3aac92184000c3d7559243080018bceab1c8610003175d56390c2001c6e41eeca1840038dc8758d430807753908b1a861000e3760d7610c200054fc32862184000a9d8650c430801f93eeca188610003275d94310c204170f32a862184000e1d6550c4308103d2cc2a18861028eb9e09755842002d72412eab0840a2ae7825cd610800b5c904b9ac2100029da1473584200053ac28e6b084000ab684d4d610800156b09a9ac21000395d4e53584200053b42c86b084000a758590d6108001d2a8621ac2100026de1173d9510004da422e7b2a2000d9774dcd65440019aec1b9aca8800374d837359510006cbba0e6b2a2000d94741cd6544001aad0a39aca8800355d947359510006aa328e6b2a2000d57541cd6544001aaea439aca8800335d807359510006e9b00e6b2a2000d56501cd6544001aa8a039aca8800371dcf7259510006e239ee4b2a2000de380dc965440019cec1b92ca8800378d837259510006e3b98e4b2a2000dc4731c96544057acd0a392ca8800359d947259510006b2328e4b2a2000d67531c96544057bc300392ca8825f39d807259510006f1b00e4b2a2000d66501c96544001ac8a0392ca882875cdd77059510006e9b9ee0b2a2000dd073dc16544001bc6e5b82ca88003781cb7059510504f8c04e9b1a2000977855d363440092e90aba6c688002b561b53d8d10006aabaea7b1a2000b9684d4f63440012ef0ab96c6880125d21572d8d10024bb42ce931a2000975859d2634413fba2e1b1cc6880125da1f7558d100063bb06eab1a2000d7360dd56344001a6eebba2c6880034d1d77458d100065bb06e8b1a2000db360dd16344001a6eea3a2c6880034d1d47458d100065bb00e8b1a2000db3601d16344001aa8ebb1ac688003651d36358d10006b3baee4b1a2000d6475dc96344001b4ee9b92c688003691d37258d10006f1c06e4b1a2000ce760dc96344001bc6c1b92c68800359dd47258d10006b23a8e4b1a2000da7741c96344001b48e8392c68800371d8c7258d1000673318e4b1a202bde1801c9634412f9cec0392c68800378d807258d10006b9baee0b1a2000d7075dc16
  | 6 => 0x70fb2a8621a4082e1c6550c43480071d90cb9086900031b1957210d2007e6631ae421a4002a6e86d9652480018dcedb2ca49000353d9573949201eea632ae72924005ccf605ce524800bb96c0b9ca49000371c417394920006e5082e72924000dc9105ce52480014d90ca9ca4900cb1e1c36554920196363b6caa9240009ad84dcd524800b2dd0f29aa49000b1b1da5354920006a7b9ca6a924032d6b751c152480017c302382a49010e1f21975cc9201943fc3ecb992400087d87d97324800b8dec0bac64900175ad81758c920006b3882eb1924000d6a105d63248001ad220bac64900025be1f658c920004b6c38cb1924000d2f655d23248001a58caba464900172bd81748c92002ed5b02e91924000da7105d23248001b5420ba464900036a441748c92022726196ca9924000c7471d9532480019a8e3b1a6490003351c4634c9200063bb2ee29924000c7465dc532480019c8e23b264900167360f754c9201eea7a9eea99240038ec865d532480658d8edb2a649010f1b1d8654c920004b6c2ee899240038ec865d13248001c9eca31a649001673a1f434c92000567436869924052ccc76d0d324807b69d0ba1a649003f331d8434c920006c6ba0869924000ce476dc532480017c30238264901131b1cb655412000637b2ee4a82400396c8754950480074d90ca92a09000eda201525412001d6643265982400087f855d930480050f90abb260900022fe11764c1201dc5e422ec98240008f7815d930480031e902bb2609010a1fa1b754c1200043f43eca982404487c87d95304800187ecbba260900030f197744c1200061fb28e89824000c3c651d13048001938e9b1a6090003271d0634c12001c77436e498240039cc874c930480075990c99260900f7531d5324c120006c63a2649824003bc8804c9304807717d09b9aca100022f613735942002c76412e2b28400387e8794565080070f90ea8aca100169b20951594200051f426e6b284000a3d84dcd65080018bee739aca100029be09715942002d36412e2b284000a6f824c5650800b4d90498aca100021fa1c31594200043ec3862b2840038dc835d663080071b906ba4c61003f2710d7498c2007e2fbaea73184000a9e84d4e630800153b09a9cc61000e3720d7198c2007e2fbaceb3184000a9e849d6630800153b093acc61000297a167498c200052ec2ce9318400fc9c745d2630801f1bd0faa4c6100023761f5498c200052f428833184000a5d8510663080050fd0bba2c6100021f6177458c2001c6f43ea6b184000c5f75d4d630800153d09a9ac610002a76135358c2002c76412e2b1840038de878c563080071b90e98ac610016b32093158c200052f42862b184000a5d850c563080018beeb3aac610002a7a127558c200054ec24eab184000a5e85dd163080014bb0bba2c61
  | 7 => 0xf586dc532880018eeeb3aac310002b5e0d75586200056a41aeab0c4000ae7825d561880575c904baac3100029de1573586200053a42ae6b0c4000ab7845cd618800156908b9ac310002b9e09735862015d72412e6b0c4000a76851cd61880014eb0a39ac310002ada1353586200055ac26a6b0c4000e575394d61880014ed0b21ac3100029d61643586200074aa1886b0c4000a77855c961880014e90ab92c310002b5e0d72586200056a41ae4b0c40a5af3805c96188057ccca5a92c3100029da1732586200053ac2e64b0c40008f4874c9618800117f08b9eca900ee2f21173d952000c3fc3aa3b2a4000a5f8358765480014b906b0eca9010f1d9db10d95202253c43221b2a4000c5f739cf654800147f08b9eca900028f21173d95200051f420e7b2a4000a3d841cf65480018bae639eca900ca9b60873d95201953d400e3b2a4044a79801c765480010fd0e18eca900021f61c31d95202243f43e21b2a400087d87c4365480018ed0f886ca900031d61f10d95200043fc2ae2b2a40008df835c5654801f1b906b8aca900023be0971595200043ec3cc232a400087f8758465480014bf06b08ca900029720d611952000537c12c232a4042a788644065480010ff0aba6c69000a1f21574d8d200047bc0ae531a40018f4815ca63481498eceb884c6900031d5d71098d201943e436eab1a400087e87d9563480018e8e3b2ac6900021fa1c6558d200063a388cab1a4000c3f65dd16348001878cbba2c6900030fd947458d200061e328e8b1a4000c7765dc563480018e8cbb8ac6900030fdd77458d200061e3aee8b1a4000c3f751d16348001878ea3a2c690003271d37358d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200043fc2ae2b1a400287c855c5634800117f08b8ac6900ee2f2117158d200046fc1ae2b1a40008ef825c563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200063bbae20b1a40a4c7475c41634800196ee9882c6900032d1d31058d200046fc3ac631a4000a9c8458c63480015a902b18c69003f2710d7418d2007c6e41ae231a4003ce572c4063480014bb07b2ca6901131b9cb6594d2001c76432e529a4000c6f655ca534800117f08bb2a6900ee2f2117654d200047bc0aeca9a40018f4815d953480050f90a3b2a69003e1fa1f6554d2007d2f41ecaa9a400287c859da43480010ff0abb4869000a1f2157690d200043e432eb21a400087f87d9643480010fb0fb2c869000e3b2197290d200143f42eeca1a400087d85dd943480010ff0abb2869000a1f2157650d200047bc0aeca1a40018f4815d943480010ff0abb0869000a1f2157610d200047bc0aec21a40018f4815d8434800153d0ca188690002a72194310d200
  | 8 => 0xea12c2180023d21d42584300053b42c64b086000a75858c9610c00156d09192c218002ad61232584300047bc3a64b08600e8f4874c9610c0018f70bbb260180031e217764c0300065dc26ec9806000cb884dd9300c0018f6edbaa60180031edd8754c0300065dbb6e89806000cbb761d1300c069b36e63a260180ee2fa1373597200045ec26e6b2e400187c8754565c800b1b906bacc79003f1720d7598f2007e2e21aeb31e400fc5f305d663c800b1b906ba4c79003f2710d7498f200062ebaea731e4000a9e84d4e63c81498eceb884c7900031d5d71098f2001e733962131e400287e85dd163c80010fb0bba2c79001637a1f5358f200062fbaea6b1e4000a9e84d4d63c800b59d05a9ac7900063da1f7158f203947b438e2b1e4001cd471cc563c80031b90e98ac7900023da1f1058f2002c3fc3acb29e4000a5f8359653c801f0fb0bbb2a79000e3ba0b7654f2024637296eca9e40008f7815d953c80031e902bb2a7900028f6166490f200061f3acc921e40058bf8759243c800187ceab2487900172b9c96490f200143f42eeca1e400087d85dd943c80071dd05bb287900023de057650f2000c7a40aeca1e40008f7815d843c80031e902bb08790002a7e194310f200054ec328621e40009ad84dcd52c8001a9ee729aa590003391c7764cb20236a7a9eea996400096d85dd132c800b59d0da1a659011ad3a17434cb20006c6ba086996400396c8754950c80014bb0b31a6190003171d6634c3200064e3a4c69864000c5c7558d30c8001938e8b1a619000e7321d324c320236a63aa649864000d8c744c930c80011bf06b8acb1003e3720d71596200143f43eeab1c4037c6f20dd5638806f8da41baac7100df1dc437558e201be3a886eab1c4000c3f75dd16388001878ebba2c7100d72bc837458e201ae56906e8b1c4035cb710dd1638806b96a21ba2c7100030fdd47458e200061e3a8e8b1c4034c9f731d1638807793b063a2c7100d3278c07458e201a64e180e8b1c4034cb7101d1638806996a203a2c7100021fe157158e200143e42ae2b1c40008bf845c5638807717908b8ac71000a972156394e200054e422c729c403787f855d9538800117f08bb2a7100ee2f2117654e2001c3e43acaa9c40038dc8758d538800153908b1aa71003f1798d7590e200063b30aeb21c40348df8758e43880018baeab1c87100eea72116390e200043fc2aeca1c400287c855d943880a51bf06bb2871014a37a1e6350e2001c6e43ac6a1c403ba9c8458d43880010ff0abb0871000a1f2157610e2007c6e41aec21c4034a9e8650c43880695390ca18871003f27dd94310e200064ebb28621c4081e966150c438801f8bcc6bae65100031d98575cca201052e42ac79944000c5d7558f328800153908b1e651007697215634ca200054e422c699440008
  | 9 => 0x75d08301de1f322eba106071c6e625d7420c0018ecc2bae84180021fe1d65d08300043ec3acba106000c3e75593420c00187aeab268418002a761843d08300064ebb087a106000d1d7510f420c001c3aca21e84180031b9d562d083000636baac5a106000e8c4358b420c0050fd0abb484180163760d76908300043fc32eb2106005c6e625d6420c0018ecc2bac84180021fe1d65908300043ec3acb210600fc5e73596420c00187ceb32484180030f5d6649083007e4f39cc92106000c3e75592420c00187aeab24841803f279cd64908300062f32ae72106000c5d655ce420c00193cc8b9c841800327591739083002e67312e72106000cd6615ce420c0018dceab1484180031b5d5629083007e6739ac52106000ccd7358a420c00717909bb284180063d20776508300047bc0aeca1060018f4815d9420c01f8b8e6b2a84180031d1c565508300065a38cc8a10600fc9c73591420c001968e2b2284180023761b73508300062eb2ee6a106000c9d64dcd420c00153b0c21a8418003275d843508300070eb2886a106000ccf73589420c01f998e6b128418003a310d62508300067238ac4a1060008f586dc5420c0018eccbb8a84180031d59771508300065b326e2a106000cb564dc5420c1539ccc5b8a84180033958b715083001c5ec22ec210600287e855da320c0071db04bb4641807e1fe19758c83002e37312eb1906000c76615d6320c0210ff0eb2c64180021f61d658c8300061f32ce91906000c3d659d2320c00b95cc53a464180032d986748c8300061f32ae91906000c3d655d2320c00b95cc4ba464180032d985748c8301dc5fc3cc919060008bd87992320c00187ceb32464180030f5d6648c8300045fc3ac919060008bd87592320c00187ceab2464180030f5d5648c830006373aac51906000c6d7558a320c00195ce8b1464180032b5d1628c83001c76416ec99060018f481dd9320c0018e8e2b2a64180032d1c6644c8300065a38ac8990601c8f586dc5320c0018eccbb8a64180031d597714c8300065b326e29906000cb564dc5320c0e59ccc5b8a64182a2b5e0d755843007d6a41aeab0860a7ad7835d1610c01f5a906ba2c2180029da1474584300053ac28e8b08600fad683d51610c0015ab07aa2c2180038dd5254584300055b426a6b086000ab584d4d610c01fcaca7a9ac2180029da1743584300053ac2e86b08600fe944350d610c14d5af06b92c21803eb520d72584300053b428e4b086000a75851c9610c00156d08392c218002ad610725843007d6b418e4b08600ead5831c9610c0075e500392c21803abc60072584300055b424a4b086000ab584949610c01f5ad07292c218002b560e52584300053b42e84b086000a7585d09610c0014ed0b212c2180029d616425843007d6b41c84b086000ad583909610c0011ef
  | 10 => 0x218600fc5f70594430c0698bae0b2886180d3879016510c301a70e202ca2186034e5710594430c069caa20b28861814a37e1d6410c302964f3a2c8218600fa9f87590430c0a593f0eb208618002a7e156410c300054fc12c82186034a9e80590430c06953900b20861803f27dc16410c301a64eb82c82186034e9710590430c069d2a20b208618002a761a5410c300064ebb4a82186000e1d65950430c00153b0caa08618003275d95410c300070eb2aa8218600face83d52620c00159b07aa4c4180038bd52549883000557426a73106000aad84d4e620c01fc9ca7a9cc4180029ba17439883000536c2e87310600fe8c4350e620c0014dd0a20cc4180029b61441988301dc5f426eab1060008bd84dd5620c0050fd0bba2c4180021f617745883001c7743c42b1060038ec87485620c01f5990690ac4180029ba14215883000536c2842b106000aae84085620c00155b0810ac41803eb3a0c215883001d7540042b106000aae84dd5620c00155b09baac41803eb3a0f75588300053742ee8b106000a6d85dd1620c01f59d07ba2c4180029ba16745883000536c2ce8b10600facc835d1620c0015cf02ba2c418002b9205745883007d6741ea8b106000acd83d51620c001c5ea92a2c418002b3e0d545883007d6641aa8b106000aae84d4d620c00155b09a9ac41803f9394f53588300053742e86b106000a6d85d0d620c001c9d0ba1ac41800393617435883029567c0686b106052acd80d0d620c0a5d1e81a1ac41814ba350343588302976388686b106052ec510d0d620c01fd1886a1ac41803fa3a104358830007473a086b106000e8d7410d620c001d1ca821ac418003a3550435883007d67c0086b106034acd8010d620c069d1c8021ac4180d3a310043588301a76388086b106034ec51010d620c00159f06b8ac41803eb320d715883000537428e2b106000a6d851c5620c00155d0838ac418002ab610715883007d67418e2b106000acd831c5620c0075d50038ac418002ba600715883000567c1aa2b10600facc83545620c01f59d0720ac418002b360e415883000567c1a82b10600facc83505620c0014dd0a20ac4180029b614415883002c6ec1aed290600fc5e73596520c00117b0d3a4a4181470f99674948300061eb2ce92906005cae629d2520c00196cc33a4a4180022fe19749483026e1f32ae92906000c3d655d2520c00b95cc4ba4a4180032d98574948301dc5fc3cc929060008bd87992520c01f93ce7324a4180022fe1d64948300045ec3ac9290600fc9e73592520c03b8bccab9ca4180031759573948300064f322e72906000c9d645ce520c00b99cc4b9ca418003359857394830006573a2c52906000cad7458a520c01f99ce6b14a418003335cd629483001c3e42eeca9060038ec87589520c0050fd0abb684180021fe19
  | 11 => 0xc0074f50010aca180029e600215943001c5e422eb320603bc3f75d52640c01f53d07aa4c81800e2f21172990300047bc0ae532060018f4815ca640c00717908b8cc8180ef0fdd6759903007d4f41ceb3206000a9d839d6640c07717d0fa9cc8180022f61f539903007f0f29ea73206000a3e859ca640c00147b0b394c81803ea7a0e72990300055bc0ae53206000ab4815ca640c07717d0e10cc8180022f61c21990300051f428433206000a3d85086640c01f53d0610cc818002a760c219903001d5d400433206000ab980086640c00717d0faa2c8180030fdd7545903007d4f41ea8b20600287e85dc9640c0010fb0bb92c81803e3720d715903001c5f43c82b20600fa9e83905640c0071790ea0ac81803ea720d41590300051f42882b206000a3d85105640c00187eeb3aac81803ea7a0e75590300054ec1ceab20600fa9c835d5640c00193eea39ac818003275d473590301a64f380e6b206034c9c701cd640c069d2e2039ac8180022fa1f53590300045ec3ea6b20600fe1e53d4d640c00147d0bb92c8180028f61772590300064e39ee4b206000a3e859c9640c00147b0b392c81803ea7a0e725903007d4e41ae4b206000c9c735c9640c00156f02b92c818002ad205725903007d4f41ce2b206000a9d839c5640c00153f06b8ac81803ea720d71590300051f428e2b206000a3d851c5640c00153f06a8ac81803ea720d51590300054fc1a42b20600fa9c83485640c00117d0e10ac8180022f61c21590300051f42842b206000a3d85085640c01f53d0610ac818002a760c215903001d5d40042b206000ab980085640c00187ea8bb4a81800e1fe1d65950300051fc22cb2a06002a3e85592540c01f1b906bb2a81800e1f21d655503007e2e39acaaa060038bc87591540c01f938e6b22a8180023761b73550300062eb2ee6aa06000c9d64dcd540c0050fd0abb686181561fe1975d0c301de1f322eba186000c76615d7430c0210ff0eb2e86180021f61d65d0c300061f3aac9a186000c3d75593430c01f93ce8bb6861800317a1576d0c300062ec2aeda18600fc9e845db430c0a593b08bb6861814b27d0176d0c302964ea02eda186052cd7105db430c0018baed3ae8618003175d975d0c3045e8f3a2eba186000a5f87597430c0014bb0eb2e861803f179d165d0c302962fb82cba186052c5d70597430c0a5c3e80b2e861814b8750165d0c302972b882cba186052e5510597430c01f1bf0eb26861803f279d164d0c300070f3aac9a186000e1d75593430c0a593ee0b26861814b275c164d0c302974b882c9a186052e9510593430c01fc3886b2a861803ea720e6450c3007d4e41ac8a18600fc9e845d8430c01f93b08bb086180d3279017610c301a64e202ec2186000e1e84594430c001c3b08b28861814b179d16510c3007f0f3a2ca
  | 12 => 0x3475d764cc9300070e32ec99926020a5e85993324c0018baeb3266498003175d464cc9300064eba0c99926000c9e76193324c001a3aea326649800387d9464cc9300070e328c99926000c9e87193324c00193b0e326649800327dd464cc9300070f3a8c99926000c9d75193324c001c3aea3266498003075d464cc93000747410c99926000e8d82193324c06993ce032664980d3271c064cc9300074b880c9992606587c865d6324c0010fb0fb2c64980d62fa1a748c9300061fb2ce91926000c3c659d2324c0691790cba464980030fd95748c9300061e32ae919260008bd87d92324c00187cebb2464980030f5d7648c9300045ec38c91926000c3e75192324c00187aea32464980031d1c7654c9300065a38ec89926000cb471191324c0019c8e3b1264980031dd97714c9300063a32ee29926000cb764dc5324c001968c9b8a649807717197754c93001c6e432ea992601da5e86d95324c06f8b8edb2a6498197171d8654c9301a46f436e8992600095d85dd1324c0071b90cba264980d7271db644c9300070e32ec899260058de87991324c03b4bd0b3226498016b3a0a644c9300064fba0c89926000c9d74191324c069938ec322649800387d94644c9300070e328c89926000c9e87191324c00193eea3226498003275d4644c9300074a388c89926034c9e70191324c069938e03226498003a5c40644c9303a72632ee49926000e8c64dc9324c001c98cbb126498003a3193624c93000727b28c49926000e8f64189324c0e59a8edb8a649800395197714c9300074a326e29926000e4f654c8324c001d1ec8990649800317d9773541300064e326e6a826000c5f651cd504c001938c839aa09800e5721d535413001d2e432a6a826000e1c6454d504c0076b100a9aa0980d237a1a73d0130004aec2ce7a02603bc9c649cf404c077938c8b9e809800ea721943d01300043fc2aeca02600287c855d9404c0050f90a3b280980021fa1f65501300043e43ecaa026000c5f65dcd404c0018b8cbb9a809800317d9473501300062e328e6a026000c9f641cd404c069938c839a809800ea721943501300064e3b286a026003b988050d404c06f8f4edb2e60980df96d8f65cc1300163d3b0cb9826035cba76d93304c0051bb07ba2ca1803e3720d715943001c3f43ca2b28600387c87545650c01f4b906a8aca1803e97a0f74594300852ec1ee8b286000c3f749d1650c01f4b906ba2ca180028fa1272594300051ec24e4b28600fa5e839c9650c0014bf06b8aca1803e9720d715943007d2f41c82b286000a5d83905650c0014bf06a0aca1803e9720d41594300043f43882b28600087d87105650c0014bf0690aca1803e9720d21594300043f43842b28600087d87085650c00147d0810aca180028f610215943007d2f41842b286000a5d8308565
  | 13 => 0x43e42ae9b126000acd83087624c0015d30010ec4980030fd9674989300061e32ce93126000c3f655d2624c001878caba4c4980030f9d764989300061ebaec93126000c3e75192624c00187aea324c4980021fa1f65589300063a38ecab12600087e87195624c0018e8e232ac4980030fd9774589300061e32ee8b126000c3f651d1624c001878ca3a2c4980022fa1f64589300061fbaec8b126000c3c75d91624c001968e3b22c4980022fa1c64589300061fba8c8b126000c3c75191624c001968e2322c4980031dd9771589300063a32ee2b126000cb764dc5624c001968c9b8ac4980023be1d62189300057240ac431260058dc839da524c00117f08bb4a4980ee2f21176949300045f434e92926000c3f659d2524c0a3878cb3a4a4980022f21974949300061fb2ae9292604dc3c655d2524c00117f0fb24a4980022f61f64949301dc5fc38c929260008bd87192524c0018becb39ca4980831719673949300064fb24e72926000c9c649ce524c0018becab9ca4980771719573949300064fb22e72926000c9c645ce524c0054b90ca9ca498003179d953949300068f3a2a72926000e1c6454e524c07717d09bb2a4980022f61376549300062e3b4a6a926000e1c6494d524c0050f90b3b684980021fe1576d09300143e42aeda12600087c865d7424c077878c8bae84980021fe1f65d09300043ec3ecba126000c3e75d93424c00187aebb2684980ef2719273d09301de4e322e7a126000a9e8690f424c001a3aeb21e849800a1f216769093002c6e41ced212600087f855da424c0050f90abb484980021f21975909300043fc3ecb212600087d87d96424c00187cebb2484980030f5d764909300061f3a8c92126000c3d75192424c0018becb39c84980031719673909300064fb24e72126000c9c649ce424c0018becab9c84980031719573909300064fb22e72126000c9c645ce424c0050fd0bbb284980021f617765093000c7b40ceca1260008f5819d9424c0018e8e3b2a8498016aba0b64509300065a38ec8a126000cb471191424c00153d0d21a8498003271da43509300063bb2ee2a126000c7465dc5424c00196ec9b8a84980032d19371509300043fc2aec212600287c855d8424c0012bb0b39884980031719673109301de4e324e62126000c5c655cc424c077938c8b98849800a1f21676cc9301043e432eb992600087f87d97324c0270fb0fb2e64980030f9d764cc9300061ebaec99926000c3e75193324c00187aea32664980831719775cc930004aec3ceb9926020a5c869d7324c0411b90cbae64980829721975cc9301062fc32eb9926020c5c865d7324c0410b90cbae649803f17d8175cc93007eadb02eb9926000d57105d7324c0012bf0fb2e649808297a1b65cc930004aec38cb99260008de86dd3324c0012bb0bba66498
  | 14 => 0xc83440644c00187ea93b4a8980ee2f21176951300051ec26cb2a26002a3c85d92544c0018becb39ca8980ef2719273951300062fb2ae72a2603bc9c645ce544c0011bf06bb2a8980ee1fa1f65551300145f43ec8aa26037a5d83d96534c001c3ea7b24a69800387d4c6494d300152f436cb29a6000c5e76d96534c001c38cbb24a69800a97a166494d300152f428c929a6000c9d74192534c001c3ea8324a698003279d86494d300070fb28c929a6000e1c65192534c00193b0e324a69800387a146494d300070ec28c929a6000e1f52192534c06993ce0324a6980d3271c06494d305570f280c929a60aae1c50192534c001d2e20324a698002972195494d300070e322a929a601dc5c655ca534c001938c8b94a6980df1e1c36554d300070e298c8a9a6002c5c76dd5534c06f8b8edb2aa6980d237a1b7454d301ae4e3b6c8a9a60028de87991534c00193ee8322a69821b871506454d301a64e3b0c8a9a6000e1f65191534c001c38ca322a69800327a1c6454d304370fc28c8a9a6086e1c85191534c001c3eea322a698003871486454d300070fa88c8a9a6000e1d51191534c06993ce0322a6980d3271c06454d300070fa80c8a9a6000e9710191534c0058b8ed2a2a69800347dd25454d304370e324a8a9a6000c9c64dc9534c06fab6ea382a6981961f21975d0d301de1e322eba1a603787f87d97434c0010fb0fb2e86980030f9d764d0d300061ebaec9a1a600287c859da434c0510f90cbac86980021fe1f6590d3009c3ec3ecb21a6000c3e75d92434c00187aebb2486980030f9d46490d300061eba8c921a6000c5f859da434c0018b90b3b486980d327e127690d301a64f204ed21a6034c9c409da434c0699ae213b4869800237a1b7590d30004aec3ceb21a6000c5e769d6434c0018bcecbac869821b179917590d304362e322eb21a600fc5f605d6434c01fab6c0bac869800355c417590d30004afc3ecb21a6000c5e76d96434c0012bb0e32c8698003179d86590d300064f3b6c921a6000d1d75d92434c06993cec3248698003475d46490d300070fb28c921a6000e1c65192434c00193eea3248698003879d46490d300064eba8c921a6000e1d75192434c00183aea32486980d3279c06490d301a64e380c921a6000e9710192434c00193ced2a48698002a72195490d300064f3b2a921a6000c9c645ca434c06b970e1b22869803ea720c6450d3001c6e432eaa1a6037c5c76d95434c0cb8b8ec32a8698002a7a1b7450d301ae4e3b6c8a1a6000e1f65191434c001c38ca3228698002a7a1c6450d301de4f438c8a1a6000c9f75191434c00193aea3228698003a5c406450d30004aec2ee4a1a6000c9c64dc9434c06bb36e8382869800387d954310d304170e32a8621a60008bf845d7624c07717908baec4980021fe1574d893001
  | 15 => 0xa20ec8980038760c65d91300051f42cc3b226000a3d85987644c00147f0ab0ec8980028f21561d913000557c12c3b226000aac82587644c001c6ecb886c8980038d19710d91300061eba8ebb226000a9e831d7644c06b53b063aec8980028fe1573d91300051e42ae7b2260358be87d4f644c00117b0fa9ec898002ada0772d91300055ac0ee5b226000caf729cb644c00147f0ab96c8980028f21572d91300051f428e5b226000a3d851cb644c06b53b06396c8980028fa1671d91300051ec2ce3b226000a3e850c7644c00147b0a18ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec898002a7a0c21d91300054ec1843b226035aba80087644c0015730010ec8980028fa1770d91300051ec2ee1b226035e3a50d43644c00147d0b886c8980028f61710d91300071b42e21b226000e3585c43644c077878c8bacc8980030f9d764991300061ebaec932260a4c7675c42644c0018eaeb884c8980021fa1f65591300043f438cab226000c5f75dcd644c0018b8ebb9ac8980021fe1571591300143e42ae2b2260008df835c5644c0011df04b8ac8980163b20971591300063bbae20b2260a4c7475c41644c00117f0eb20c8980028fe1564191300051e42ac8322603bc3f75d50644c00153b07aa0c8980ef2b10972191300047bc0ae432260018f4815c8644c0079aae7880c8980030f9db65191305670fc1eca32260ace1e30d94644c159c3861b28c8980022f61e65191300045fc3aca3226000c3e76194644c001c3b06328c8982af878c0651913055f0e180ca3226000e1f655cc644c001c38cab98c8980022f61e61191300051f42cc23226000a3d85984644c00117f0eb08c8980028fe1561191300051e42ac23226000aaf82584644c00155904b08c8980038dd9710191300071a32e20322603bc3f759d4644c00153d073a8c898002a760e75191301dc5f43ea632260008bd87d4c644c00147d0b390c8980028f61672191300054ec1ce4322603bcac725c8644c00156f02b90c898002ad20572191300054f41ea43226000a9d83d48644c00153d06290c898002a760c52191300054f41ea23226000a9d83d44644c00153d06288c898002a760c51191300051f428623226000a3d850c4644c00153d07908c898002a760f21191301dc5f4384232260008bd87084644c00147d0a108c8980028f61421191300054f418423226000a9d83084644c06957500108c898002ae60021191300051fc2ae03226000a3c855c0644c00153d07a80c898002a760f50191300051fc2a603226000a3c854c0644c00147d0b880c8980028f61710191300054f41e203226000a9d83c40644c001c6d0b880c8980038d61710191300074b41e203226000e9583c40644c069d2c61880c8980d3a50c310191300054fc1a203226000a9
  | 16 => 0x48ca3002e57312e91946000cb6615d2328c0018daeab1465180032b5d1628ca300047ac36e29946000c77759d5618c00156f08baac318002ad21175586300056bc1aeab0c60b1ad4835d5618c0015cf04baac318002b920975586300053bc2ae8b0c6000a74855d1618c0015af06ba2c3182c2b520d745863000573c12e8b0c6000ae4825d1618c0014ed0a3a2c3180029d61474586300056b41ea8b0c6000ad583d51618c001c6ea92a2c3180029de1573586300053a42ae6b0c6000ab7845cd618c00156908b9ac318002b9e09735863000572412e6b0c60afaf3805cd618c00156d09a9ac318002ad61353586300072ba9ca6b0c6000a7685d0d618c0014eb0ba1ac3180029da1643586300053ac2c86b0c6000e954310d618c0014ef0ab92c3180029d21572586300055bc22e4b0c6000ab4845c9618c0015af06b92c3182bab520d72586300053b428e4b0c6000a75851c9618c00156d08392c318002ad61072586300a56b418e4b0c6000ad5831c9618c0075e500392c318052bc60072586300055b424a4b0c6000ab584949618c0015ad07292c318002b560e52586300053b42e84b0c6000a7585d09618c0014ed0b212c3180029d61642586300056b41c84b0c6000ad583909618c0011ef0ea12c3180023d21d42586300053b42e64b0c6000a7585cc9618c0014ed0b192c3180029d61632586300055b42464b0c6000ab5848c9618c0075e501192c318002bc602325863056c7a43a64b0c600f8dc835d3654c0030ff0ea8eca980028fa1261d95300051ec24c3b2a6000a3f84587654c00147908b0eca980029be0961d953000536412c3b2a6065c7676c43654c0014bf06ba6ca9804e9720d74d95300061eba0e9b2a6037a5d831d3654c0014dd043a6ca980029b60874d95300051fc22e7b2a6000a3c845cf654c00147d08396ca980028f61072d95301bd2ec18e5b2a600087e87107654c0010fb0e20eca980021fa1c31d953009c3ec3863b2a600087e87087654c0010fb0e10eca980028fa1021d95300051ec2043b2a6000a5e83087654c0014bb0610eca980de9ea0021d95300053cc0043b2a6037c78705c3654c0010fd0f886ca980021f61f10d95300063b43e21b2a6000c7587c43654c001878cbba2ca980030f19474595300061fbaee8b2a6000c3f751d1654c001938e9b9aca980021fe1571595300045fc22e2b2a603b8bc845c5654c0011bf06b8aca980023be09715953002c76412e2b2a6000cb774c41654c001968e9882ca980021f61e61195300051f424c232a6000a3d84984654c0010ff0eb08ca980028fe1161195300051e422c232a6000a5f83584654c0014df04b08ca980029b20961195300061ebaea9b226000a9d83d53644c0010ff0ab96c89800a1f21572d913000c5fc3a83b226000a3e85107644c00147b0
  | 17 => 0x1e6000e971019143cc0012bb0bb928798003271937250f300143f42ee8b16600087d85dd162cc0015e30038ac5980023da1f1058b3007e2f39acb2966051c3e659d252cc00187acb3a4a59803f179d95394b300068f3a2a7296603b8be84dd952cc00117b09bb2a59800e37a0f7654b300047bc0aeca9660018f4815d952cc00b0fd0fb2aa59800317dda5354b3002c5e422eda166000d1d7590f42cc0050fd0bbb285980021f6177650b3001c6f41eeca1660008f7815d942cc0031e902bb285980831799575ccb300062fc32eb996600fc5c865d732cc01f8b8c8bae659800355c4175ccb302946fc32e9996600fc9c645d332cc0414bd0b3266598003175d664ccb30004aec2eec996600099d84dd932cc03b4bd0bbb26598002a7a13764cb300066a38eec996601d8dd86dd532cc03b8bccbbaa659800257617744cb300ed2f42cc89966005ace8299132cc00193ae8322659800e5721d53543302946fc32e7a0660008bf845c5658c07717908b8acb180023be09715963002c76412e2b2c60008f7815ca648c0031e902b94c91800a1fa1f75592303362f986eab246066c5d30dd5648c0cd8ee21baac91819b1d44375592300043fc2ae2b24600287c855c5648c0011df04b8ac9180163b20971592300151e42ac92a460038bc87591548c0018bacbb9aa9180ef0f99175d0e300063b30aeba1c6000c3d75593438c0691bf0eb26871800297e1564d0e30006acbaae1a1c6000c76615d6438c103d2cc2a1887180d2e62014310e300052fc2aec21c6000a9f84594438c00163b0b3a087180d2e6a027410e300052fc2ac821c6034a9e86950438c165c3ecb2a087180d2a7a195410e300070eb2aa821c600287e87dd5628c0018bd07baac5180031760f7558a301962f986eab146032c5d30dd5628c0658ee21baac5180cb1d4437558a300062fbae86b146000c5f7510d628c00193ee821ac5180021fe157158a300143e42ae2b1460008bf845c5628c07717908b8ac5180030fd967494a3028e1e32ce92946000cb6619d2528c00b95cc4ba4a5180032d9857494a300062fb2ce72946020c5c659ce528c0019acc339ca518017339897394a300066b30ae72946002a6c8558a528c00195ae8b14a518003335cd6294a3001c7643ac4a94603bc3e645d7428c0018ecc2bae85181468f21564d0a300061ebaac9a146034c9e7610f428c001a3aea21e85180171b9897590a300063b30aeb2146000cd6619ce428c00b99cc4b9c8518003359857390a3000636baac52146000ccd7358a428c0031e903bb285180021fe157650a300143e42aeca1460008f7815d9428c0031e902bb285181368f2156450a300074621ac4a1460008f586dc5428c0010ff0abb0851800a1f2157610a300063b30aeb9946005c6e625d6328c0018ecc2bac65180032d9867
  | 18 => 0x40010fb0d39ca52800317a1a7394a500062ec34e7294a044c5f629ce52940898bac539ca528003559867394a50006aab0ce7294a042c5e609ce5294041ab4c139ca52800355c427394a500043fc3ac7294a000a3f8458e529400187ce8b1ca528003179cd6394a50224ae41aeb994a00fc5e635d732940018ecc2bae6528003175d563cca500054e422c7994a005c6e625d632940018ecc2bac65280032d986748ca5002e57312e9194a000cb6615d232940018daeab1465280032b5d1628ca5000c7a40eec994a0008bf845d9329407717908bb265280023de05764ca5000c7a40aec994a000c5f7558d329400153908b1a65282d39314d624ca500047ac36e2994a000a77855cd61940094e90ab9ac328002ade1173586500055a422e6b0ca000ae7825cd61940015c904b9ac3280629da1473586500053ac28e6b0ca004a768590d61940014eb0b21ac328003a550c43586500053bc2ae4b0ca004a74855c961940015af06b92c328002b520d72586500c53b428e4b0ca000a75851c961940015ad06392c328002b560c725865001d79400e4b0ca018af1801c961940094ed0b992c3280029d61732586500253b42c64b0ca000a75858c9619400156d09192c328002ad61232586500047bc3a64b0ca0008f4874c961940014bb0a18ec6a800237e1d6318d500054e422c631aa00fc9c435d063540078eaeb880c6a82ce1fa1b7454d500043f438c8a9aa000c3f7419153540870fd0db92a6a803e1f2167690d500061ebaec921aa000c3d75192435400527f0eaa486a800e1f2197550d504370e322a621aa000a9e8650c43540015390ca1886a8002c76154310d500045fc22e7b12a03b8bc845cf62540014db0a10ec4a8002ba60021d89502262fb2ce7312a0008ef8758862540cb0fd0db9aa4a80024f61373549503ec3f438c6a92a00f87c859db325400117f08bb664a80ee2f21176cc9500062ebaec7992a00587c859da32540031ed033b264a80023d606764c95001c3e432ea992a005ace82d8d32540019a8e3b1a64a8003351c4634c95000c3e43aa2b2e608bc3f645d664cc077878c8bacc99822f4790d759933045e1f21aeb326603bc3c435d664cc07787e80bacc9982931d9d710993300063abae213266003cd673c4264cc0050fd0bb92c9980021f61772593300047bc0ae432660018f4815c864cc07717908bb4a9980028fe11659533001c6f41eecaa6603b87e87d9554cc0a51bf0cba4a79803f271917494f300152f42cc929e6000a5f8655253cc01f8becbbb2a798002676137654f300068fba4a8a9e6086e1c6495153cc10d8bcc8bac879803f171917590f30006ab882eb21e600095d85dd943cc00153d0e322879803f27a1c6450f300064fba8c8a1e6000c9d7519143cc01fd330032287980d3279c06450f301a64e380c8a
  | 19 => 0x2ad61050d85320056b418a1b0a6400ad583143614c8e55cd04286c299002b960850d85320047bc0aebb0264018f4815d7604c8011ef02ba6c0990063d20574d813200578c06e3b026400af1801c7604c8031ed0db8ac0990723d21b71581320047b43ec2b026400c7775d85604c8018e8ebb0ac0990032ddd361581320065a3a6c2b0264008f687185604c8018eeea30ac0990031d1d461581320065bba0c2b026400cb474185604c8391eb0fb08c0990031d9d761181320063abaec23026400cb674d84604c80196ae9b08c099002bc60361181320063b3a8c23026400c7575184604c80196ce8308c0990032d5d0611813256e6ab98c23026400af180184604c8011f70eb00c09903e37a0f745943200c3e43aa2b2864058bc845d6640c87787908bacc81922f0f90d75990321de1e21aeb320643bc3f405d6640c80187aebaa4c81903ea7a0f54990325263b3ae213206400c7575c42640c80b17d0faa2c8190030fdd7545903207d4f41ea8b2064018bc87505640c80b0ff0eb2ca8190028fe1165950321dc3ec2eecaa0640287e85dd9430c8010fb0bbb2861903f2710f7650c320067238eec9906400c6e85dd9320c8018db0bbb2641903f3394f764c83200673886ec99064b5acf8654d320c80199eeca9a6419002b3e19434c83200673bb6e2990640287e87dd5600c81fd9660992c0190021fe1571580320143e42ae2b0064008bf845c5600c87717908b8ac0190031ddd710580325263a3ae20b0064018f887441600c8011ef02b94c7280063d2057298e500061e2a6e8b1ca000c3e85dd1639400187b0bba2c7280030f14f7458e500061e296e8b1ca000c3f51dd1639406b87ea1ba2c7280d70f5437458e501ae5b886e8b1ca035cb510dd1639406993ee63a2c7280ef2760c7458e500064f298e8b1ca000c9d531d1639406993c603a2c7280d3270c07458e501a65b880e8b1ca034cb5101d1639400117f08b8ac7280ee2f2117158e5000477c12e2b1ca0058ec825c5639400187ee8a8ac7280021f61a7494e500043fc3ac929ca000c3e7459253940014bf06b24a7281961fe1d6394e500051fc22c729ca015a5f8758e53940cb8bf0eb1ca72800387e116394e500070e422c729ca037e571058e539406fcaa20b1ca7280de5ee197094e500063dc32e129ca037d72615c2539406fae2c2b84a72803f1798d7590e500063b30aeb21ca000c3d7695243940691bf0eb1c8728003175d56390e501dd4e422c721ca000e1e5458e43940012f301baa872814a37a1e6350e500062fbaac6a1ca03ba9c8458d43940892dd05ba887280025e6037510e500062ebb4a621ca034a9c8650c439401f93eeca188728003275d94310e500058fc2a8621ca081e966150c43940010fd0f29ac5281129ba0a5358a500046fc1ae2b14a00f8dc835c5629
  | 20 => 0x6fc3acba1a6400a5d85d93434c801a9ceb3968699003535d672d0d3202ce7c3ae5a1a6400d4e755cb434c81fa9864bac86990031d1857590d320051ec2cc921a64008be87191434c8050fd0b3b086990021f6167610d32004cfc3a8621a6481e946150c434c83b2bd0b3b08699003351867610d320052ec2cec21a641d8dd87d94434c83b8bcebb288699002a76136510d320058ec2ce821a6400a5d85d90434c80163b0b3208699002e360a6410d320046fc3ac821a640099f87590434c80171f04b208699003a51856410d320054fc3ac821a6400c9f87590434c80153f0ab208699002a7e096410d3200747c12c821a6400e9781590434c801d2902b2086990d2a72016410d320074b882c821a641d99d87950434c80153b0d2a08699077479d65410d320070eb2ca821a6400b8d82950434c80153b0caa0869900387d955410d321a46e432e021a641d95c855c0434c80193ac8b80869900317d977354932004cf426e6a92643bc3c645d7424c8018e8c2bae84991468fa1764d09320061ebaec9a126400cd4619cf424c877938c8b9e84990033518573d093202ccec3887a126400d1d7510f424c8011ef02bb284990063d205765093200c7a408eca12641d95e85dcd424c80193aec21a8499016e3208435093207ea6192eb9926400c74615d7324c8e969d0ba1e649903f72cc170cc9320047ac3ccbb0a6400ab684997614c80156b0932ec2990023de1d65d85320053b42ec9b0a6400a7585d93614c8011eb0f326c2990029da1664d85320053ac2cc9b0a64008f787593614c8e55ad0da9ec29900395d9753d8532005cb426a7b0a6472bc682d4f614c8e55ad0da1ec299002d5a1743d8532395e341687b0a6400e956410f614c80156d09baec299002ad61375d85325b56b41eebb0a6472ad583dd7614c8e55cd05baec299002b960b75d85320063aba8ebb0a6400a7685dd3614c8014eb0bba6c2991dab5a0f74d85323956ac1ee9b0a6472ae682dd3614c8015cb05ba6c2990029da1674d85320053ac2ce9b0a6400ad683d53614c8015ab07aa6c2990038dd5254d85320055b426a7b0a6400ab584d4f614c801caea729ec2990029da1743d85320053ac2e87b0a6400a768590f614c8014eb0b21ec299003a550c43d85320053b42ee5b0a6400a7585dcb614c80156d09b96c299002ad61372d853237d6b41ee5b0a6472e6652d4b614c8014ed0ba16c2990029d61742d85320047bc3a85b0a64008f48750b614c8014ed0b996c2990029d61732d85320053bc2ae1b0a6400a74855c3614c8018ef0ab86c2990031d21570d85320053b428e1b0a6400a75851c3614c80156d08386c299002ad61070d853224d6b418e1b0a6472ad5831c3614c8e55cd04386c299002b960870d85320047b438a1b0a64008f587143614c80156d08286c2990
  | 21 => 0x824c5648c80147d0a18ac9190028f614315923202d57414e0b246400ab6819c1648c80156b03382c9190028fe1570592320051e42ae0b246400a9f835c1648c80147d0a382c9190028f61470592320054ec18e0b246405aae821c1648c80156d02382c919002ad60470592320045f438a0b2464008bd87141648c80153d06282c919002a760c505923202d57410a0b246400aad82141648c80156d02282c919002ad60450592320051f42e20b246400a3d85c41648c801c6d0b882c9190038d61710592324bf5390620b246405aae82841648c80155b05082c919016aba08105923200556c1020b246400c3f545da548c80b0ff0eb2ca9190028fe1165952320151f42ac92a46400c6d655ca548c87795cc8b94a9190162f21d64552320070fa9cc929c6400e1f53592538c8018dacbb92a7190021fe1975d0e321de1f322eba1c640087f87597438c80187ceab2687190030f5d564d0e321de57322e5a1c642887f865d6438c83f0ff0eb2c87190030f9d66490e320061ebacc921c6400cad64dc9438c905c3ccaa188719003875954310e3200c7c43a20b0464adcd573187654c801caea630eca990ee2fa1371d95320045ec26e3b2a64058dd83dc7654c81f1db05b8eca992df95d4f10d95320072a298c2b2a6400a9e84dcd654c8031ed0fb8aca990023d60371595320047b438e2b2a640187c87545654c8014b906a8aca991229b20951595320047b43e20b2a64018f487c41654c8018ecea30ec8990031d5d461d913256e6ab98c3b226400c5e755cf644c8018baeab9ec89900a1fa1771d91320043ec2ee3b2264058dd83dc7644c81f1db05b8ec8992931d9d710d91320063abae21b22643bc3c645d6644c80187aebb24c8990031d9d461991320063aba8c3322643bc3c435d6644c87787e80bacc8990ef2710d73991320047bc02e332264018f787c42644c8011eb0f884c8992931d9d710991320063abae21322640287e85dc9644c8010fb0bb92c8990023d60371591320047b43e20b2264018f487c41644c8050fd0b3b0c8990022fe1d64191320043fc2ae0322640287c855c0644c87717908bb4a8990023de05769513200c7a40aed2a26400a3f84596544c80547d0bb24a8990033518673951321de4e322e72a26400cd4615ce544c81f1d90cb94a89900339185729513200c7b40eecaa264008f581dd9544c8010fb0b3b2a8990023de05765513200c7a40aecaa264008fb805d9544c8071f100bb2a8990ee1fa1f65551320145f43ec8aa264058de86dcd544c8018becbb9aa89901673a0b735513202c3fc3acb29a641fa5f83596534c83b8bee7b2aa6991d35314f7254d321de1e322eba1a6400c74615d7434c80187aebb2686990033918572d0d320062f3b4eba1a641d95f875d7434c8018bcecbae8699077179d765d0d32004
  | 22 => 0xb8687990031759570d0f3207f0e21acaa1e6420c5e7559443cc8018bf0eb28879903f1721d6510f320070f422ca21e6400e1d8459443cc8018bce8b28879903f879d16510f320072b882ca21e640fa9f8759043cc80193f0eb208799002a7e156410f321a54e402c821e6400e971059043cc84133b0f2a08799002a761a5410f321068f3aca821e6400e1d6595043cc80153b0caa08799003875955410f32104ae42ae021e6400c5d655c043cc80193ac8b8087990169720d6554b320062eb2ee6a96640099e84dcd52cc8010ff0eb2e8599016a761843d0b320070eb2887a166405b8e8210f42cc81f8bce732cc1990031d9c6659833207e2f39acb3066400c767159660cc81fcb660b2cc1990031d99571983320063ab2ae3306640fe5b3059560cc8031ed03ba2c1990023d607745833202c76412e2b2c640587e87945658c8030f90ea8acb190169b20951596320fd2f41ee8b2c6400a5d83dd1658c80187ee93a2cb190169ba0a74596320051f426e6b2c6400a3d84dcd658c8014ef02b9acb190029d205735963200537c12e2b2c6405a6c825c5658c8014df04a0acb190169b20941596320043f43882b2c640087d87105658c8014df0498acb190169b20931596320fc3f43862b2c640087d870c5658c80b4dd05382cb190029da0670596320053ac0ce0b2c6400a3e841c1658c80147b08382cb1907e97a0c70596320052ec18e0b2c6405a6e821c1658c83f4db04382cb190029da0470596320053ac08e0b2c640087e87c41658c8010fb0f882cb190031da1f10596320063ac3e20b2c6497e6720c41658c80b4dd05082cb190029b60a105963202d3741020b2c6400a6d82041658c80b17908bacc9190ef0fdd754992320054ec1ea932464058bc845c6648c8010ff0ab84c91900a1f21570992321de1fbaceb3246400a9e839d6648c80153b073acc9190022f61f53992320054f41ea33246400a9d83d46648c80147d0a18cc9190028f61431992320055b40ce13246400ab5819c2648c80147f0ab84c9190028f21570992320054fc1ae1324643b8be87142648c80117b0e284c919002a7a0c50992320054ec18a13246405aae82142648c80155b04284c919002ada0450992320055ac08a13246400a3e85c42648c80147b0b884c9190038da1710992320071ac2e213246497e9732c42648c92fd2a65884c919002a7e0d10992320054e41a213246400c3f75d51648c80153b07aa2c9190163b209715923200c5e43a82b246405aac82505648c80147d0a20ac9190028f61441592320061fbaceab246400a9e839d5648c80153b073aac919002ade0573592320055a40ae6b2464008be87d4d648c80155f04b8ac919016ab20971592320051f428e2b246400a3d851c5648c80155f04a8ac919016ab209515923200557c1262b246405aac
  | 23 => 0xd8d520061fa82e9b1aa43b8be84dc7635480117b09b8ec6a900a3b60b71d8d520061eba2a3b1aa47da6c82547635480196ce9886c6a90032d5d310d8d520054f426c731aa4008df8758c63549730fd0d3a4a6a90021f61f6494d520052ec1ec929aa41d87d87d8e535480147b09b1ca6a90765761f6394d520058f426c729aa41da5d87d8e53548018bb0fb1ca6a900387a136394d520070ec26c729aa400e5710d8e535483ba9ce6b94a6a910a1f2197094d520061f3b4a921aa4008f7815d843548031e902bb086a90161fa1b7510d5202cb7416ea21aa400c5e7694c435480153f0ca1886a9002c7e154310d520047bc0ae7b02a4018f4815cf60548658becab98c0a90023ee1d601815207e4e21ae9b2e640fc5c835da65cc81f4bd0730ccb990163720d715973207c3f43ca2b2e640187c8754565cc81f4b906a8acb9903e97a0e615973207f2b98cc2b2e6400a5f864c565cc9498eeed882cb9903e97a0f74597321052ec1ee8b2e6400c3f749d165cc81f4bd073a2cb9903e9720d74597320061eba0e8b2e640fc5e871cd65cc8014bd0839acb9900317dd073597320062eba0e6b2e6400a5d801cd65cc8918b8e7b92cb99123171cd72597320053bc0ae4b2e6400a74815c965cc81f4bd0738acb990029760e71597320052fc1ae2b2e640fa5c835c565cc81f4bd0720acb990029760e41597320052fc1a82b2e640fa5c8350565cc8010fd0e20acb990021f61c41597320052fc1a42b2e640fa5c8348565cc81f4bd07382cb990029da0670597320053ac0ce0b2e6400a3f845c165cc80147908b82cb9903e9720d70597320051f420e0b2e6400a3d841c165cc81f4bd06382cb990829760c70597320062e398e0b2e6448a6e821c165cc8014db04382cb990029da0470597320053ac08e0b2e640087e87c4165cc8010fb0f882cb990031da1f10597320063ac3e20b2e64b8e5773c4165cc801ca8e7882cb9903e97a0e10597320052ec1c20b2e640fa5e8304165cc8014bb06082cb9903f8710d659933207c5e422e3326640087f855c264cc8050f90ab84c99903f171ce655933207f0e21ccab26640fc5c7359564cc81fc3886b2ac99903e2fa1e415933207d4f41c82b2664a4c7675c4064cc8018eaeb880c9990028fe1165953320062eb2ae72a6640f87c8759554cc87747908b2aa9991c69720d655533207e2e39acaaa66400c5d65dcd54cc81f4b906b2aa79908317dcd6554f322ac3fc32eba1e642087f8759743cc81fc3c86b2e879908257e1d75d0f3245e8f3a2eba1e6420c5e75d9743cc8412bf0f32e879908237e1d65d0f32104afc3acba1e6400a5f8759743cc8418bf0eb2e879908217e1d65d0f320052ec3acba1e6420c5c8759743cc801c3f08b2e87990038721165d0f3207e2f3a2cba1e6400e571059743cc8a51bf0c
  | 24 => 0x8634ad88050d6010c77d3680a1ac02180327e1d43580431a54e43a86b008600c9c8750d6010c691390ea1ac021802a7e1543580430054ec2a86b008600e1f7550d6010c01c38eaa1ac021802a7e0943580430074dc0286b008634a9e8050d6010c6953900a1ac021803a620143580431a54c40286b00860087f855c56010c050f90ab8ac0218023be09715804302c76412e2b008600c7775c416010d498e8eb882c021803a550f10580430074ca1c20b0086018f8874416010c01d3286882c02183f2710d7498e520045fc22e131ca43b8bc845c263948014bb0b3a4c72903f271d17498e521052f42e8331ca400a5d85d0663948414bd0a20cc729002976144198e520056b40ce131ca400ad5819c263948014bf0ab84c729002a7e117098e520054e422e131ca420a5e85c4263948014bb0b884c7292e395a171098e520072ac2e2131ca4b8e5675c426394971caea9884c72925f95d4b1098e524bf2aa962131ca4b8e5450c4263948014bf0a884c729082972151098e5202c76412e2b1ca4018dc874c5639480b5990498ac729002976143158e520052ec2ee8b1ca400a5d859d1639480193ae83a2c729002b3e097158e5202d66412e2b1ca41da5e851c563948014bb0a38ac729002b3e094158e5202d6641282b1ca41da5e8510563948014bb0a20ac729016b3a0a7058e520056b40ce0b1ca400ad5819c163948014bf0ab82c729002a7e117058e520054e422e0b1ca400a5d851c1639480153d08382c729002a76107058e5202d67410e0b1ca400ad6811c163948015ab02382c72907697a171058e520052ec2e20b1ca4b7e5685c416394801cab0b882c72925fb1c831058e5202d6741420b1ca400acd82841639480b59d04082c729002b36081058e520043ec36e8a9ca40087e87991539480187ee9322a7290030fa1e6454e524370fc1cc8a9ca486e1c8399153948fb87ee7322a72914787dce6454e522461fb94c8a9ca448c3d729915394801878e1322a7290038dc426454e520d52f43cc6a9ca40fc5e8798d539490d4bd0931aa72900317dd26354e520052ec04c6a9ca400c5c7098d5394801cae2131aa72908353dcf7254e5207e2f31aeb21ca451c3e75992439480187aeb32487291370f9d56490e520061ebaac921ca40293f87552439480187aecaa4872922f8798d5490e520ee2f3aac721ca400c5d7558e43948418bceb31a8729003175d66350e521dd4e422c6a1ca40fc5e635d4439481f8beeca98872921b879915310e520054fc328621ca400a9d8650c439481f93eeca188729003275d94310e520058ec2a8621ca40087c8754d60948031f10e882c1290032794e74d8d520064ea9ce9b1aa400c3c545d3635480187f0aba6c6a90030f21574d8d520061e29ae9b1aa400c3e525d36354801878a4ba6c6a90030fd4574
  | 25 => 0xc0153f0cba2a62180b87a1a5454c430170ec34a8a988686d1f769515310c51c3eed2a2a621acb471c25454c435df8b884a8a98860099d84dc95310c01a3ca9b92a621a1b47a117590c430068ec22eb2188686c5e645d64310c1fa3cc8bac862180355c417590c430068ebaaa9218860287e85dd94310c010fb0bbb2862180317a177650c430062ec2eeca18863bc9e54dd94310c7793e85bb2862180335c437650c4307ccec26eaa188682d1f54dd54310c011bf0cbaa8621a1b479517550c434368e2a2eaa188600c9f765514310c01a3eeaaa28621802576177250c434158f42eeca188600b1d85dd94310c0193b0dbb2862180347a177650c43004cec2eeca188600d1d85dd94310c0123b0bbb2862183f27d977650c43004cec16eca18860fc9f62dd94310c6933d01bb2862180365c437650c4307e4f43eeca188600e1e85dd94310c01c3b0bbb28621802a76037650c430074b886eca188600c9f76dd54310d05a3cebbaa8621aea6761b7550c434168f32eeaa18860099d82dd54310d05a3ea5baa86218d267a037550c434168e286eaa188600d9710dd54310c0153f0cbaa862180327dd97550c434168e3aaeaa18860099f865d54310c0193f0cbaa8621aea67e157550c430068fc2aeaa18868bd1f655d54310d17a38cabaa862180267e097550c434168e292eaa188682d1f515d54310c01a3aa2baa86218d2672017550c434168fa82eaa188600d97105d54310c0133d0eb2a8621aea6761d6550c430064fbb2caa188600d1f755954310c0193eedb928621a0ac7a177250c430058ec2ee4a188600d1e85dc94310c0133b0bb928621803476177250c430048ec2ee4a18863499e80dc94310c01b2e21b928621802a761a7250c434158f42ce4a188600b1d859c94310c0153f0cb92862180327dd97250c43005cbc0ae4a188681b94815c94310c0153b0d3828621a06e5a067050c43005cac0ce0a188600a9f865c14310c0163f0ab828621a0ac72157050c434158f428e0a188600b1d851c14310c0171d043828621802e36087050c4340dcb408e0a188600b95811c14310c69b34e0382862180267e1d43988434168f3aa873108600d1d7550e6210c0171f04a1cc42180267e1d43588430054fc3286b108600b8f8250d6210c1fd18c4a1ac421a07651c54358843006caa1ee2b10860face83d496210c011eb01b8ac421802bc600715884300e7238e42b1086018ec874856210c011ed0f882c4218063d21f10588431a4ce43a873008681d967150e6010c6973100a1cc0218036550d71980431a4ce43a86b008600d1f7550d6010d05a38eaa1ac0218d2e620143580430162e3aca6b008600a9d8494d6010c691b90ea9ac0218038795153580431a46f43c86b008600a5d8590d6010c695b50121ac0218efa610243580431a46e43a86b0
  | 26 => 0xa1f61f6494d530061f3a6c929aa60287c865c25354c6f8f0c0b84a6a983f56cc17094d530043ec3ca9b12a60287d8794f6254c914dd0529ec4a98ee2fa1371d89530045ec26e3b12a6028dd83dc76254c014b906a8ec4a99d3335cf629895300477c3ac4312a6008f7815cb6054c031e902b96c0a98df0fd9574181531be37b2ae4302a6008fb875806054c1f1b906b8acb2183e1fa1e515964300c3e43aa2b2c860fa5c835456590d498eeed882cb218a29760f74596430051ec24e4b2c860fa5e839c96590c014bf06b8acb2183e9720d715964307d2f41c82b2c8600a5d839056590c014bf06a0acb2183e9720d41596431443f43882b2c860087d871056590c014bf0690acb2183e9720d21596430043f43842b2c860087d870856590c0147d0810acb218028f610215964307d2f41842b2c8600a5d830856590c014f50010acb218029e600215964307d2f41ce0b2c8600a76819c16590c014eb03382cb218028fe1170596431451f420e0b2c8600a3d841c16590c1f4bd06382cb218a29760c705964300537410e0b2c8600a6d821c16590c014ed02382cb218029d60470596430043f43e20b2c860087d87c416590c018ed0f882cb218031d61f105964307d2f41c20b2c8600a5d838416590c1f4bd06082cb218029760c10596431de4f31aed2a48602a3f865965490c0187aecb2ca9219370f995729524307e2e39acaaa48600c5d65dcd5490c0587eedbaaa9218a30fdd9655524345e8f29ee6aa48600d1f75dcd5490c4987eed2a2a721a1b8798e5454e431443fc3acba1c8600c5d769974390c018baecb2e8721a1a97e1d65d0e434352ec3acba1c8600e57105974390c0155b0810ac52183eb3a0c2158a4300574c0042b14860fc5e739966090c018ece332cc1218031d9c5659824307f2d982cb3048600c76655c66090c018eacab8cc12183f96cc165582431ac5f43ca8b048602c3c759516090c6b17d0fa1ac1218028f61743582431ad5d40686b0486018f681dc96090c011eb03b92c1218ee3760f71d954302c77416e3b2a86008ed82dc76550c030f90ea8acaa18029720d51595431dc3fc3acb29a8655a5f835965350c0187ecbba2a6a183f4710d7590d431ac5e432e121a8635cb8605c24350c1fb3660b8486a180317e0d75d89430062e41aebb128600c3d7590f6250c050fd0bb8ec4a18021f61771d89435263b3ae21b128600c7575c436250c011df0eb10c4a18023de0572d814300c7a40ae5b028652c5f635d46050ca599ec6b90c0a18023ee1d60181434be7339621b288600ce572c436510c030f90ea8aca2180237e197494c4307ccfc32e92988600c9f865d25310c0133f04ba4a6218d2672017494c43006cb882e92988628c3f769515310c1f8becbbb2a62183e576177454c434368f2a6e8a988602a9d869d15310
  | 27 => 0x4000007801003e0160080000002007001802400a010001802c00000b001800402c0020040008012005000800400e00e0008094018001001000800000000080100060280020008002004001000000000d007000801c00c0010000018001006000400a009002000000802a000004001c00000d80100000070008000000002000002802600200000040140010028004000000000000000e0050028040006000002800000200c010800000e001005003c00001501b0004000000002800400400300080000020040008014004001000004800600000100080060000008004002012007000800e001006000003a033003017c000002004801c00a007003800c01400000a000400600100000000000010018004000000000009800000100100040060080068018008001000002c00000b000800800201400e801008a00000080000160000000010000000000000002401f000007801000000600280080030018050014002001804c000002013007400401200980f0002018000800000a00000480b800c00800e802800200600a001400800e0010078000001001000000200100200080020020000094002002000000000c000000802001e007000001c01a00a0078040008004001005000a00000000900000020000004020005003000004c000004800402401d001800004600001a000c022000000800c00602e0050000008008001801000000b0008000000003009000401000c0010000006022000802c04603400a001800000300600000060050088000006001000002001a002000001000a00000f80140040010098000006000000800000c00000380000160020000058006000000800001000a000000400a0000020008000014001000000a000004004c0000000038018018001002000c00e008000819c0160000010004008002002800000a00500180100080010000000000000000000400400300180000000000000000000000002000c00c0010040010000002001000c02e0100000000000001000800000800400d000c02c0000010034000003000801c00600e003000000a008000002801000800080540080050060004002000000000400a000000800401200f005803c0080050048004000004000000401200500203e3720d715925307d4f41c82b24a600a3d851056494d499a8e7882c92983e3720d7158a5300536c2842b14a600aad840856294c1f59d0610ac529802ba6002158a53006aba9ae3304a637e7250c416094c051bb07b8ec8a98163ba0b71d915300476c16e3b22a600a5c835476454c058bae6a8ec8a9a93355cf10d91530045fc3ac8322a6008f7815c86454c031e902b90c8a989e1f61f64951530152ec1ec92a2a627a3d87d925454c0187b0fb24a8a98a38760f64951530071b886c92a2a60087c865c25454c1fa38873a4a6a980
  | 28 => 0x9000c000005013001c04c00000000000000020008004030002000000c0000060000004002000000000c00800e000000800a0050000000000012001803801a01d0018008004001008805000000300180a8004001001003000000400e00040080040010000006002000002c01e0030028008004000000801c02801400200f40000090038010000000001001c000000002000c038004003800c004006004000c030018001001c00c00e000000c000002000005c0120000000000000007000003c000003000004c01400900300040040000070018006000000001000001b000003c006007001000c012000004004000600200000200000040028038016002001000800800d004000c00000e003804401202b0038000000003000801400400900c800c00200d001000800000100e802c01a009000808000c01a003000400e00b000801c00200000400000040010000004000002001003c002002001000000e006000800000c000000000401e001003801800000000280000020010018004002000001001c02200000900680020010008000000000003803000a0170030014000003000000000a0000000034012002000000000400501f800400000b00e8000004004000000c00e001000001800000a00680100560020020000006005001000400200000c800001a007001801000c000000800400a000001001c01000000400000020000008004004012002002c00000100080000020020050034002002001812402400f001806000002100000000040030020070000000000003c008000001000c010005000000c002000000000c00000300e0000012000000802c02c0060018000010003001806c00000400080240040000000008004001001802000c02302d005000200a0000008002008002801c01c00100a809000600300100140040090020004000001000800804a000002000001800e003002001c00400b800400200e000001000a0040078098002000000800400001f018001c000001002001c0080030038050002000002801000000600080100060010050028000000003800000000900000140280000028008020000006802801000d004800000000700100000000000020000000000000000800200300100000020090038010006006001802c00a000002000400e003007000400800c0030020022008000001c00a001003803004c01b008800400200000200000000070008000024002003000c00000a000000800000100600000340030058024012000005000c004001002000000801402380000000120048020008004001005c000000001803c0040000000004000018001802800200000c8030000001000000000000d0168000012002007004c0000030000010000002000001401600d000000001a0150038014000003001004400600c00000600
  | 29 => 0x5040002f200000001522ef30e8000b8200000017b96a40006ceac4400000000019bcdc89ed234e1840007de32400004b4000000079ce9400000000000007852ec325d366ca03250b402f0dff00000000000004b000000000002cc000000068b0f5a56487fd4604c9e585ff5c70000148000c25ccf000095c00035a00000000000000000bba00000000000002230000000000d29000000099365180000003c20001d023ccaca46a2658e8559cba24478001854d270000000858ae22a0aa7cad08820f500013605c42b1b064000000000055d98891a59d252c00060c000008d2ae0000000000000a023452e9400007f0002ff92e2000126800010e2732693315858c10331b4726d4d92712a9bc2a5158a808000000b3674c09020000330001ce0000cd51e49a18d900850002d68cc83754b600000006230148ec1c800005652c3974c16509a80000000000000000d3a90256410d600056a75703f01d2c4100020b9b90e0261d33ccdbea224230f94ed6d0f26493517d477a129910d8d20004271779afe0000000c010bc1f372dd2e00000000960000a56b7a000000151016d00026680006800001c80b3a4fa00006f04d6d12638ea4d28ce4d6559024635222220acc80000d600000009d80ce6f28a3c21f00047280013c83104e880010346b3af93954ecc0002e6a96c1a10001e5a2ddad8a1f000145523641d98c179ec569b472808291b20003ab0f0957e00044c84a49f8b4f601aab1326c95394db5cb1850f0be9df1cea89f410151b8388af3b10775cd26d027cb4d93e264c2c312d4df475a71a396d4d67685b48000e848ee0002d9fa68d09000300800000000019950245664bd80007ded4d00023b142c3575ce8a58d960e3448ac20c828375aa2a2466c15d4b590500160000001cb00002714f296b9d7e0000004006000000807c000000000000c018005000000c00c001000001800000400180440340000040008014004000800000c007000001000c0060020038008009000808c00000200f8004006001001000401a000000817c03a001005003004c000000003c0080000058000006000003001800a004000002000000a005006001a025004000000a0000040004002001003001c000001000002000800e0010030002001000000003401a0048000014006014801400000000000080000000058000000003001800001c04e00c8004000014000802800000100000000160070008000010009002001803a000003002c08600200000040060000090000004005008001801c01a0078000000009000003400000b00d001c00000000c00dc0040030068008002005004000400e0010018010010003000000401a00600000500000190010044002007009003801c003002803400200000280000060010008000002002000000000000100000000000030
  | 30 => 0x4305e2000000394861c00000000000000a5304b018f2a00000001f8000a4c54930f98a8d230330259a1c93361b00000000000c2ab08000cc815b06f8000653e660000000606611721597628ed7b387903ce896a436240000004cba895a7669c00008180792cb608800043e000478b4f89fe00047335646f4c9c71e8f19a82000087a1e915a000000369a9a681f30c4000f3e0006f7b1f9a3419b2e483a37e41080000b101cc0006c6000000000023205f19743d00000f49553e7b000225839f71d7562c9c46d60d04e32b13541b93668fd07514684fd3098b50e4113d145957866c5d9a4887d220c6d687a105e73a4312878094e39b830ed110243252298c4af86e00b8101922c2036db07d212ac610d083c44ece8421e39956b04d575233fd69ae5aed7333cf983601f5037c998a395fc81c9bf454226f0e99a2a61137331e050668557d130577ad9f570267d134034220541c3ab2ac15fae65074b5d0f6366cece0700f68d04be673c54d1c34d2a82b29b8789632ae157983717e6af9649a13d4e69b610a87900005a147495641e4d8e59090295767211df95d05df00063d03509449660adb4e943062400034c8c2e23d6bdabf0160abe0639668a3ecde267800000039871a4ea4000888000398d2e88214a9baacbe20b700036e0000436ba201b0e7dde43fe2848676cc33b182503a621900028c80004cd3b4a06c9362590d9a2308cc6983f032cd71e8fe1a387d55ba1df7502d5e85a5f80001cb40002075901518efe2f393680019180000000d400000005a09aad6fc7e509200015eacb962f20a8bd0301000e92193acd830d248cb4e29401f58e5a0ae265060fb47220004f08000bc63f568883086410004db800073a00000026ececad690000b1906c000757baedc66b1c10b846ba5400055700000008d2000094853084050d867800074f225000050172f130a548d7aca265f1559af8bb64f19924b544d92af1ea0eb8c0474f369099027b271aac10c0bb40c0a91c260d7453c30e5a04787552b73db42a40454273cfec00029e85b0a6c46100003a16462a95bb800120662d8180001c42467800000000000000003840000005b680000000000001bec00000075505800006e54eb10a4ac9000085a6b4c7000005120d436400035f05117700001d98bc0000da600009d484c63647ab92cf4656257fae5d006df67110000000b5ed51b37c13e255800000137800009935b800042f53700015367100ae08bcb2e90f54682dfa7202c6de9fc0d54d49622b658dc47d7148145cdac0ad3cf2499bac152102a5c973843d08e2d27c793eb05225bcb2c61f1cf3a642503e46e28ee40000cb05d01585940006728000c4e65700012c0000b6347faaa115c0006122ba0c1065414100000004bc000395800000059e000000000075300005d49dd1430
  | 31 => 0x866044032a000000013c00011c45883250004a6c00000000073906a800087d4c3a0f024489f80000006e42670d8b6c4a94bc14e3846039637c58b38a59ee6c2243af253e871c0002fa4bd83f90000000e3e2f6155b8010f037f59f048c126a74059b004cbcd8f12504e019a00052f58b04b7199722151cb0e7b510bc1669d695f1bd882e93ce462a921fc7ee46f5ed0000a860000000fa0e7666743422f00008051720000000a3059b800000060060c0000e547f13f638b9d22c5900004814c241b239af700002b00000001c500003618001cf400014f00000000000002028dce4df0ec86e968c7360000274fb2000112a8f000037e00029a0000000198b3f17ae00025a08d6000b731f39cf4042bd80562cfcda48c5013f77c5025e216f02b9644ea95276fa15a000000000000001ab4081854a3a0000001f50000a57a738001c6e0000a700000000003468000a047e16a78fcd04ab92374116d79a27d4d185bd9b4bfa0a5ae8c1189be7452eb83449cb2dc13158b6dd90aa236d0ce3f12eb13cd0be37173ca28c35004bb5101e443413a61ab4d4000bc350980015b200075f25e8bda000116b97685461968a228297c3990001ae41f40006dd00018a43aa000238dbb80000001e0c522000000393c77008e80027cc00063c1fb27bb45cbcb3028001c0c00016a8ead0ec2e000000010e00000b31a4cab900000024dc000000017622cf8ab073fd39dcdf800060d00008c4b601bb355c81a0001b6b861058c6e4e7000042caf229213748b8ea84e31488266a3830c386d502e2b000112052600034b1eb6f9683412f2bc45a8b293dd1edc5c5c5815a0b0d2eacf90001699c0e7ac654b094d985355f8000000000046893bc000bdb078330926a040c330000225e600269e212c65ac5a400000000004b0875c3acab60001780bf2ac502a2c0ce90b8e1d18001a368145932728958eb30001964000906034a4fd75649a74097f4000d7867321b15865820e013a8232a98427d65511478070b346400000000037a0000bb95ef8001bd8dc4508a125b583f0668ac09348adc0000d857405d1596326c48ad654148438300d133be97c1ca2652cb706d58769609fe800043ccfd0000000000000000191a0000004e65f4c000000226a9f48a0e0a0003a00afa0005e10728130a03157800000000049db1b400003500023415748c409080000005d26b9850ce4a5be2ca000091c5b551d2f280000006e7000177c94442e19e90e80473c480016dc0004a40af48169940b5ba2da7ee2372395dcb3e0cc4351c9873e1506f5955066a28d5a9b912000453456092c4e03dd52780f081035c5f89c4c09e2f558d1908b6e1882b396d1c750003349e18b7200042db1b039ce5837f14bdcded6405915b8c886ad38d882ad94dd072180000daa9600000000000004920000004
  | 32 => 0x619c3db056022c94f000047400030b0001f0133847c00000000000001be8000000086000209191c00072f51e42c292b6a22325d0648449c8000000000000026c5b4e0bc850000000da80003802000a4f8003a350de0000d4a2d1492ad516b0a1d8262c91f120440007f261fab2540e572000171978a6f85848001cf00655c49f8847047e72e1f1d9024824059b4d3aa26a1340c3092000075a8001c18a015a2000000098026c00000001770000000deae01cec2e84000bb70000000000ade3eb1dd084200041e92917fed5f00008855da78d000311c04338d1d118f9cbe85640e0e4c5ce0000e31ec87780103310b39bf00d94a2a2700443c73099c360003654fb2dc469cba4432a1cd44ed6f4194d242a65f620f8877448b5a89e2752e527c339580e99302ead3f17fd6660066b90000e9be6e00382fc9e8d251c380019620004a08e2c00000002e00014fe3a40000ce489c6123d73902206bb2085357933a12a6a883b83268b50458c5817a0d22f38000b085fdaefb8fc7808445a676a90f579974e80000000006b8b1700003b117680000000000000d7809b0001fe00000007d044f400008c8896173a5dd42ce044236688456e953cb39c00071a5b92f380001362a008ed30a31f51887f849ea7569678d52946ba73e0d191fa6de4948410704b4a29417394f82260b49ea5a06bef3a39038cfce0d20d1eec54ea9e47916c419407d00000013e44ce00014e6ee684c4f41b380000001c26fb465657969684edaba70809f218d3520881e1800161e00040a8001314dfe684000000000000010e847800058009f8a62a18e3780017ba0004880000a9a21b00883680009db2e11879ab80004679e7522400066480000008396341c615b4e7164790080e23045a01a7fc487d52f8400000000000032457060003c080009f088336a22c539d00074b14312eb00027095b5b0007600012309e4cd6000297c0000000001a5ccf6be7000385081e84327e800121c610062809c6c60bc120ae050f2174701d4481b00c10000744db25ca00033ecb402146a132480003701a996b44ae8ed12e04953f0292068175c83ac070e3ab99cd68b95438f540000001cd825d34c24955c94d0000000322b3d916078b000117cf1c92e19680000000000000000000000000000000000000000000008b83f507d85b000039f1c3d1424b35880001cd03e053024819e2833a4aa309c1d00050cc001156000000000081800000018816d6c88c2092f4ca159e000000000014f5ae31c09cc8ce14d09bc00011a5738c14b9849600019c00000500003849726b050000000ff02a321a09411a600071d8000d349b20000c78a1200022c9c0195a74036d0e489fc9e7643f4620962a864181dccd01b600011492aa00011f8f5800029b11c845400000011b89dc0001cd5cb1e60cbe00031f
  | 33 => 0xd9d55c78000302239da455e900033184dc000084984e3403ac6f525916285d440b8b5c00000022c20180000007100b094205b3295000169f8516fa09fd4b430a222ab5c51079ff5ca3bdbcc4053f380000003903c79ec15ca00000031c80c83110001b70b74210301824800022e05c8cf0af400000000000000000000001a4100027821a44b6000278a9a84a847d30780019c47cf5101d2593f3442a98000d327071b38001bf200045d229d6978da01140003a01e922118f4000b28676a88d382a8401b953c33a2327399e9c026ceb10711a41bce0e304d429acc57607d8a9057c45493a37092ec42062e44518d45511d70b3597a0a029328340001950002b4c0006db60ba074f660006143158000ab20f7800000000000018d5afa3bd00000000001dc20b000000052e5b940017d600046b24e0000ac64cb36511d055f49f2e01358278665911cdd81e56a000017f00d35719a7c2ec77e05a97a8dd4d8717fac604006608cd00000000005bf90485e677132e23700dc2136c50000ab45bb00000000005750001c9c01d46d724a8a80004c76579ea8000b2aab172f1a087776e49f5bb7e8e1191249ca5a28964c928dcfca8322326bb722bba759339149ccb517404c446abac4ae0777496de04470d64c4ae903480000866a6d3bb140c68aa441679d391a880800034340000004d1400020c23674d08f8000aa617e6e55c533621501ee1d1e52947b84f4ae62c571cb22478a3c422591d49daa1d666b7f7b98a940120bb009caf839400e4500327017d111312d0a0d300005d6d5b15c000069a17b0002530000de3665162cdfe9582ed9100000afd0a88f6c0000000276635bf6a9100028d41ca000083800032d00013c944d5be0411cb2d6d5a800834711c98e2e5e4e90b21818d4a0700000000df25cd2f88916000120225d1bebcc35b0001bf95064d7b400f2041120806f4000887000000117e0006231060b4aad64b95954000000000000184e0e7b560391bfa3cf1a12839950d8b360b14d380bd34fb90d96e856032d9cfd1d403f602a964b1ed90576290c0001f157501240000002a6e30534e00047742ac000d7528288c0000a5043d800030880e00e05c85b2000380acee0006f222d1cea000e7636b5c45934a2938b34c40000000018001c3eb7d00000000003333d6b8b5bbc1f03a08001c658cb6831f99a2cd996cbabf884acea1608cb8d3d234000316e54200011d1bb9bda5d500033b000069258099d3002000089266c0001fa119ce9cf7a6660002e0972800032697ac5fa00047103240c20c600004377ea3b71a900007a61bb0000000edc00026110ec68035100000f500e0000002de7736df10001299b4ae151909e9522a4830001444e1c00017740012a000000012e55987b9257615567b49c0bf873a0000002f2000163c0006d59bd0ce
  | 34 => 0x702110000000dba93d0000a70952653560800035c07b0bd20cc0009115c5913142a76a2a5929c000c734a00000b20a332fa8d69cd40535858981c32e1d000166d48458500000019a4602145af50000dca475aaddb5e09a2de000178e847112000132a87c4b514e87b269e1f90000000000598b9b11c8a6907c9dc03db00000000000000000000b704d20003fa000103236800000000000631f0800078f0003153100000000000000000000000000000000002d8000038a9340c132dc0000002380d7c7fe000000302138397c00028bc34a00000000000008181588000dda99924fb530d42e19919a43140cbbb3c100006ba9492ab800000083f2ae00014ccc98f331d818be246000000000043100000008430000471bc40000003b900000889705f338c876a465000000000022752dd8d195c000000358869e752566a9dd3fe000000000123a35864413dc0127e932830ac79ae5463e1d4065deb736326f4000000000000000000002640000000004f526400003189e43a478cc000000082c4308c868f8000018e33ede2ac48c67035c68b89afcc9471827ec6260001df276597e0005411f440000004252140410ac42b628dc7a200001307996c10004f606594ca4155b600004e7d948000000000da936389f000090139ca7f5618b340e90c981507c9319ad8eebc70a520b90800002f0002fb0a404815f19221ce80001592a88f08b7b538b10800000000026e531000028733d0000b251b9a6480800003180000000a0a100b80470c00075197e200000000025b53867322ad97f36e9b2d6aa1e80eb2ea547e069c0001d4325a3e4f8c9000ec00000008590ca20888ba38419f80002c6b6223d241c0000006a90001cb2000758a95c0000002c000001ae000000000052e00000000019e400000000010704b666e0dd17ca75d4a880b8000ca300015fd8d60005428000d494572bf2e20e68000000168c0006f33a6946cf9a62f6eda0ec6dcb9ebdf87fd25019052980001008be053865dd3e0002ce25ee80ec38082a7acf220006ed2f000004da0001e4c000a8a0ea40002b20001aa1e980002b926b9460b48000000000000000052a2d1cc76a8e5e7a420d1e92500fb52d2b601e358895841291971271d0ed8272497a609aec0ff0a321b590490900032c80000004e9aec40514e5000247c00024424c80010600006c428727b4de73b7800052a51e0001370a661f84390404000000000315d3b800000028d914c00000025787bc9c40358000c36da30623820cb40000000001c9400031d000154000027003740004a83f9afecc42ebc0b50000000eb400030a4cd605e1c42ebcb962b561e10b9b3c74c3e12328706494081049cd4680d57220b48c0932300a94918e4f668f23019f000043cdc5161a61404880003066d10ad371db6e0b802fb9f4664ab4f4
  | 35 => 0xfbb07d3fcb7975c0f7cfab8cd00022410ea08a3200f633be2e963192e917a6a40799c8d760d9c4c30c90f56b45181109c5e8e0b37b8b740ea453bde1783c6c68c2b20c753ccab30f90c180001374b49e911860003afb6c017c89d2f1f4a08a81f921210789126ef22884340192a6555338db7c00022a8d54cba6722098aecc9e0004492a960000000000000000677000003d9e000063c99d986e2f700000018ba00060d90c09f67d26420ca4df2392d92105ce8c00047b1d4c45f48a3cd884800081300037740007e401ec3bc0642fa6f7361459859156c191c1d41684ab2bdd8a06324a10ebd6f08fa000000000000000000000000000001524bf72168001bf567a0000000000f14a4a2f3375518c17e0228d6d0004740021440cf8c874e287b9698179554a9784545382431c2d408c4f56938a80008e06220be4c520000001c106980000000000c9c6b5691269400000000000016ea8585391420d364a102d268176ab1372995ac19e41c2ed0000000eba4968034e6ee8c000015d720463b303870000c8a2d4800000000018dc7095dca01a118cb6000e674240000eb6e4511485c41860006300000cfa51acd5800034f00045001a165c000000000000097e05500007120002ff5ccc000c64248c0000005dc00019e5b665d94191c1591a230f381870d5e87742900c5b6800000000000000000000001b083560002d2d8606b70001a947c6a3b7320e55ad044f10e86c07640002e18d21128b1d000000000015534eda8111a9314bc00007071342a29300b5e31c5952919a387ce398a62d9a0dd74da8c500700000001649518a860288000000000758000063200007c1cd40000c03538000738173000214d800cf7ec18000c11da73c9015467ab2f50efa54000000151386955a000000171583a00000000000000000000000000d3009300000007dc3ca03f40000000c7047c00051959c3240000000000083aeea87e5cc16fcd280004590a100320000002f90ca400000000000000000000731b9a0003ed208c00086b00007ec1d614a0002a2c0000000002d903b66bb5de0e040004af60b35540000b4000000076c00012e8001b0c00069700019a60005b3819c0000000000000000c7b24788a14d84c369e15a40003fb0003290fee8804bef4840001560001c097fa00045b1c260004c400000002269f90000db16d00000000000c61000039abd000003e0c315ed57aebd18d14940008854a7347554ee625d400007f0aa46580000db0c8b46c11d80000000003480d640004021531b7600037b19b400000000000000000003a8b3e9532ca1000073c700b06026000049c00000968154589d05b0c83cff200003129593301c854e0000670e2c285a289812e101e08000734b553f5b25841aa2811890ddd0ab764e400016767ca6a80525350dfc258b2d99
  | 36 => 0xe440006e000000766160b7268823c6f06b180000000d50000f2941ea766b3b0cc0000f55b31ff8c47e0f6a38036c8612f63b8c5d5f612d618a7f0930c2032c34b12d022b28a0001d266ae4bf92fc9262e329939698ca9770a3aeb41a277b00eb1543863d7237036c5a69b16f98c80844da036780000004565fb000000079c38900012162c70000590940cc70302e7ccacd2669e95bdba214552e83d8d608cc67725f4000d2400022eda86a340d61a0402eab82c410fca88bba8002d584695ef96fb364daad793f1a64496e83e057a960a4ee130051e85d4e8f81978001a3d13f0002e10000dd226b0a751522bc0530fe8bca02a72412b446fce1384a779a56a8f4a3a1680009540713049b96d8d0000000728c4b00018dc000000242ba880003d40864000000bd02e822192280000001d84000ad1000119c00000002c00000009052f7ba18000c4e617800067c43533c00000b60000000001be0a9717c1c54000000386067c2ce43940b000101200011ced087b01c935c25cc4f70006c0ab6da5e7f68000000000cdd00000000006a60002c6c2ea0003c626304380005b7800141000000024e80000006c8a85cea8c490ed0000000a70426a8ac9617df362072b90c79a3439178c5ab94eb53689d04d452d12a754160055a18bf09eacd40c58bed3e02f49461a247187d83d8810c98c0fe2a83144084a510a100000003ba20cb7d514898e3e0839d3eaa6760a24605ca00000033d4a0013942a06fc000aeb708b70c01c2046260000d50904259308570e38f5783a500000006ac2108d101d552aad40322278968800051cdb20000c1c0006c50000000000110000275000000000000007cc5fe54a800000052300002c4000c3230be6fd26c000000069200028cbfaac2800082700033bdb8c971c4f06b522e30366d8dbcc1c92101019c422eb595e23460348100359b60848e0000feae28000a3f0000ae8dd6c75016bb0000036672e90a10ed00000029ed3aeca50000000b649ef0000000668d0766032012f26bc000000093a08133a989800000000000009000f40000000000ead1b48eed8cee171569e5cb06cd75a71f7b0312ee449a0c55d20ec71397f0d7ed376ec244d21a18a64f868c00071974900003c0730531182c1da0000000c5431200065334e0e960280a69629af42a5555b42dbc2b1223589609d295a00d0cb13d2c9e62180011aa8262c48000ce830910c5c90ccb3ce5e434cc00000050d2e79a180000001294a0800063f8bf8d22082314395ca7e6c0000af780009cc65500000000157308001c622d2000000000000000016f4000d9500000000000000fe21156563084e6939075086e2bc2f809d0bd929f173c3687436fb9fb99688de05d80000009814c79a0d306000459800000066a2ae861d4380001a1a254a600005fe380d82a0005
  | 37 => 0x21000000000031880000180e23660000e7f012bad8fda393c5538e94c6e0400017ec00000063e936d89053900000011309e01cb800177eb3074e09549767644010a29bd20006b824c000047152696ac4fd12b3e44ddc484ac74a74500ef024c39703dd59ea2d5c28eb5374b7c0003a20eedd7700011dcae2be100008b064a684000308c09000008ad0e000000031107d12385f71868fb80d4c2200005317acb39202000000055524840000000002c98000000c0d3fda15d6c21f763b100cffe29f13180016ae00051080000000004f71245cdadb91c280000000000000000fb6401353552181e96200015c0a580b601b2824cc20000d7800000008f9b5800000000003780017e8000020c001c985c84ed02344a20a10000b6d308c3d4e4b02869400019bb54d1e847f3ee800114a00000000000010005e312a9542a644e127ca554000605800000000000000000365f41940000b1c00000014840000001429b84d5280f00000016cabd508db74d89ae87000000000067f5778444fde20261a0001520478171ef480000a30000ff800000066700005c20005f701e183c0005c6259528dd565b51124d9253c1bc000185ae4e4f128f46f2b65bd78990000000000000000000015bab00b6c00000002416bcb5118900015000005578000a9c00005af584dc600000009899fc18d27101d08d858168817e800089b68b4000000000000078c0000000002dc053205900025351ae2e625580004d80000000000000e38625250c00074b80000000006b0a8d099436e9ae1919434000000200000002800000000014f491e665c001ac0b497156ad4e2eacb3d1000025c66e4780e283820001e630380000000448ce83bc00050a1db4eae3ec23d857cfd0de2000158478996712f86e0a2f43e4d2e0a19d26548c92d7cc145e11c71d6170c4d10001470f68599538c90db82d6d00035ac290d010002ad074a53b4ae962e0000000002374ba600000016351f64ca5e8a8006c874500017fe8390cfdd4ac54490a3e3e2020c0560004321f21d1c2c000926e0000000000329d44ca1968b981cab04d066080000003dc6734000636b1f59aa4f1b6a0006740001b2600052e2906ffae3e198000091ae0940cf53831815e71781f031e8712158058061d5a06400000000003410000b80e053230acc92eb3ab288ab84cc7be5d3aea807f30f582017492492c42e8d2d342000047a12d8b4b1727724a8ef2000000000000080c31701e8e3cdd410f4000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x181d75a135398f200040f6627599243c800121d95e194310f20004176607598d30c800181d851d2634c320436072117558e438806909c985d94310e20104172617558f328800181d7521163cca2000417e61731cf65480014e1901c4764c9201a5232597410d324806988c861d1324c12000545652851cd654400145696940735951000515a58501cd654400151594140735951000551648501cd654400152594d4c725951000519a5a501c965440014669614072595100055164c501c9654400191575a135318d10004b12498614c6344001135989d46490d10004c56578750c4344001315952194310d101a4e42418550c434400131595e094310d101a465261435c043440695909050d7010d1000554654635c043440015919418d7010d1000564652535c04344001d125454d7010d1000554656435c043440695929850d7010d101a564261435c043440015929650d7010d1000564259435c043440015939550d7010d1000564655435c04344001d138550d7010d1000744215435c043440015939250d7010d1000534259201cd624417b4569694273949105e455e6175d0f32440019517560043cc910006645d18010f324400149694d4c764c91000531a4b531d93244001456958c8764c91000525a52321d932440014d1908c8764c91000534640321d93244001854851d9634c910006312087658d324400189476211634c91000615a1476d0d32440018c6821db434c910005252597410d324400199174600434c91000730188635c032440014e0964c9700c9101a66460d801d13044001155981d4634c110006456147418d3044069990801d1534c110006456147490d304417915497617324c1100064561474cc9304400185475219324c11000625218744c930440019908750d404c1100066461d4310e2044001165981d46248110005b0259324c12044123b40854c93048110006e0211324c120440030f09661c4348110004f0e4d85d892044001c60761d76248110004d8e5583d8920440013a39460f6248110004d8e63751892044001361981d46248110006d0dd5831892044001b407560c624811000658a1f759492044001b437560e524811048ed01d583949204406596087dd5524811015cd8261655492044057560975955248110005d024d6554920440013a194e0d524811015cd8a62535492044001b438394d5248110004d8e63758c92044001361981d63248110006c8dd5848c92044001b20756123248110004d8654864c92044001ac383219324811015cf064f854c92044123b4353e153248110004d8657844c920440013c29898d324811015cf0261634c920440575c09758d3248110006b0219634c920441237409558d3248110005e0251634c920440573c298d0d324811048dd0a57434c92044001b818410d3248110
  | 1 => 0x30064561710dc94310c698987061a7050c43004476578750d6210c6909c9761253580431a4a62418494d6010d6581c879515358043436861018590d6010c6909c9761543580431a4a62418550d6010c0181c87dd54358043006862037550d6010c0181c871d54358043006862007550d6010c0121d95e094358043005a46448050d6010c694949750f10580431a5a424143c416010c012989850d10580434350764e87991539480103d981c26454e520050b64870991539490d05d98dd26354e52434872518098d539480141d941c26354e5245e07dd98550c439480141e9394974d8d520060b20974547635480181d87a136394d520040fe61741d165cc80121c94600735973200607610731c165cc80184c7360870597325c615e1f1059743cc80141f976116510f3245e0721d8459443cc84105e989d16510f321060761d6595043cc80105c985957010f321a427261645c043cc80181d65a137354b3200515a5c53185654c80121d95e1d6410d320048765782590434c80188f87e096410d32004a5a6310590434c869298906195410d321a427261645c0434c869498905917010d3228c0fe6175d93424c8018b174600611813245e07a0d75d52640c91781c436177650c325f607e1c8458e539410d81c845d56390e5059607e1e5458e439406909c985d94310e50006075db8550c439400141f9461a7394a501851565b109ce529400103e989d16394a5000607e127358e529400181d7521163cca501a4872598550c435400181d851937250f3000507a53865d732cc00105f985d664ccb300050725183dd5628c00105d98dd74358a3028c0f26175593428c0012b19020572191300048765683c84644c00121d9520d10191304350765f54192534c10d41d97a146494d3000507a5c53191534c10d81f85a1c6454d3000507a5c52191534c15541e97d406454d3059507a5b74951534c00141f97d946490d300050765c65192434c001c1575c406490d301a6261c286dd1434c00105c966177250d300060761464dc9434c0a381c869d1539493043507e5c6454e524c00141c965d643d093000607a197590f424c10d81c64616731093000417660659cc424c17185486c4175cc93010417a5b87d97324c00141d9719764cc93010417e6175993324c00141f97d9464cc9300050765c65193324c00141d95a1c64cc930007055d710193324c00141d95dd0644c9300050765687191324c00149697c40644c9301a60721c6454d504c10d81c6461673d01301a4272607650d404c069898801d943501300060761473dc9640c11781e8461576d0c3045e079d187597430c11781f875d564d0c300048765782590430c117a0e846174358830005836567410d620c00181d865d443d08300050765d6510f420c001c0d7510d62d08300052c64071591320c
  | 2 => 0x402812ca711800ce5274bcc000c5e00000b90d80044765bb41702c2500062000f000b2b11700020251c2140000000e408411ea4c1e2d25bd918442ab34000049180bc6429ba0d2002e6a908cf523440a1f59a2dbe2014ad904db05261aa5764001c6e23e2d17c8f0013400a800001848d440008ef104800391364884353400000000000001b200000013e003f000000030a88f16827161d4c762ad4001dce091ac632d37816901d1fc2c5c41bbdcabf70851d8e73117d4226361d4a5a56a1c52a810c09d86a9773d54dd2670555ad87581c90cb4ba6802bb35a50a8433c3d13232530bcda3347144983c69a7964306617e322b001955e003c8447e6a2d800007722801224200000e41711de8ac49608010e02e526d464f790dc38e0563000c005eb6876ab3a310fa1a001750cf015035b88a3e6c08c12011b86a7b6bbcb12001f3913aae3300dba70000018c281b10010006379800ed0e9bc000e002e8e6000ad400005004020d008901a01008101400028200013108240602000000001008001c0001810081a00008140d000040409000bc020c0b800040e0100c220e0e80030000307000000082c04020c8280c0f1c8040605130000805000203435008340014018810d05d9720d51d915343607a0d87d925454c0141e94e0d75d89430044766254dc95310d0d81e54e197550c430064561710dd94310d1781f65e197550c4300607e1b855d54310d1741c965457550c4345c47656875954310c0181f766177250c4300607e5985dc94310c0181c966177250c4
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1020050030462800201ca76578250d6010c01288d292ca1ae021a20348642a19550d7010d100062213042a86b808688002511a5e49435c04344001448532e8c00869922000c3025c8658d3248110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x20004110b86949650d7010d10004110b86979250d7010d10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x94e
  | 5 => 0x3
  | 6 => 0x8a
  | 7 => 0x8e
  | 8 => 0x98a
  | 9 => 0x98e
  | 10 => 0x128a
  | 11 => 0x128e
  | 12 => 0x150a
  | 13 => 0x150e
  | 14 => 0xca
  | 15 => 0x4
  | 16 => 0xce
  | 17 => 0x168a
  | 18 => 0x9ca
  | 19 => 0x9ce
  | 20 => 0x12ca
  | 21 => 0x12ce
  | 22 => 0x168e
  | 23 => 0xa4a
  | 24 => 0x134a
  | 25 => 0x3ca
  | 26 => 0x3ce
  | 27 => 0x170a
  | 28 => 0xcca
  | 29 => 0xcce
  | 30 => 0x15ca
  | 31 => 0x15ce
  | 32 => 0x170e
  | 33 => 0xd4a
  | 34 => 0x164a
  | 35 => 0x58a
  | 36 => 0x58e
  | 37 => 0x178a
  | 38 => 0xe8a
  | 39 => 0xe8e
  | 40 => 0x178e
  | 41 => 0xeca
  | 42 => 0x17ca
  | 43 => 0x94b
  | 44 => 0x98956
  | 45 => 0x128956
  | 46 => 0x198a
  | 47 => 0xcc956
  | 48 => 0x170956
  | 49 => 0x1a0a
  | 50 => 0x1649
  | 51 => 0x44a
  | 52 => 0x589
  | 53 => 0x1789
  | 54 => 0x1a4a
  | 55 => 0x17c9
  | 56 => 0x5ca
  | 57 => 0xbc9
  | 58 => 0x14a
  | 59 => 0x5
  | 60 => 0xcc992
  | 61 => 0xcc996
  | 62 => 0x15c992
  | 63 => 0x98cd2
  | 64 => 0xd4992
  | 65 => 0x164992
  | 66 => 0x14b
  | 67 => 0x449
  | 68 => 0x134b
  | 69 => 0xcd512
  | 70 => 0xcd516
  | 71 => 0xd5512
  | 72 => 0xecb
  | 73 => 0xcd692
  | 74 => 0x40a
  | 75 => 0x40e
  | 76 => 0xd0a
  | 77 => 0xd0e
  | 78 => 0x160a
  | 79 => 0x160e
  | 80 => 0x188a
  | 81 => 0x188e
  | 82 => 0x18c9
  | 83 => 0xe9692
  | 84 => 0x18ca
  | 85 => 0x18ce
  | 86 => 0x104a
  | 87 => 0x194a
  | 88 => 0x1689d2
  | 89 => 0xa0e
  | 90 => 0x180e
  | 91 => 0x9d712
  | 92 => 0xcc9d2
  | 93 => 0x9ccd2
  | 94 => 0x1709d2
  | 95 => 0x9d792
  | 96 => 0xe89d2
  | 97 => 0x1789d2
  | 98 => 0x9ce92
  | 99 => 0xec9d2
  | 100 => 0x17c9d2
  | 101 => 0x5c9
  | 102 => 0x1949
  | 103 => 0x171692
  | 104 => 0x179692
  | 105 => 0xed692
  | 106 => 0x17d692
  | 107 => 0xd4a52
  | 108 => 0xeca52
  | 109 => 0x135652
  | 110 => 0x1357d2
  | 111 => 0xcc3d2
  | 112 => 0x18d712
  | 113 => 0x104b
  | 114 => 0x16cb
  | 115 => 0x170cd2
  | 116 => 0x170cd6
  | 117 => 0x58cd2
  | 118 => 0xcc592
  | 119 => 0xcd8d2
  | 120 => 0x18ccd2
  | 121 => 0x1715d2
  | 122 => 0x59712
  | 123 => 0x170592
  | 124 => 0x1718d2
  | 125 => 0x1a4b
  | 126 => 0x17cd52
  | 127 => 0xd57d2
  | 128 => 0xed652
  | 129 => 0xe8592
  | 130 => 0xe8596
  | 131 => 0x58e92
  | 132 => 0x178592
  | 133 => 0xec592
  | 134 => 0xecd
  | 135 => 0x17c592
  | 136 => 0x178e92
  | 137 => 0x18d792
  | 138 => 0x105792
  | 139 => 0x104c
  | 140 => 0x195792
  | 141 => 0x17ced2
  | 142 => 0xed7d2
  | 143 => 0x194ed2
  | 144 => 0xed952
  | 145 => 0xcc9895e
  | 146 => 0x98d52
  | 147 => 0x99292
  | 148 => 0x128992
  | 149 => 0x94996
  | 150 => 0x98092
  | 151 => 0x138b
  | 152 => 0xd5992
  | 153 => 0x9512
  | 154 => 0x151292
  | 155 => 0xed992
  | 156 => 0xd692
  | 157 => 0xc9d2
  | 158 => 0x1692d2
  | 159 => 0x12c9d2
  | 160 => 0xa0a
  | 161 => 0x199352
  | 162 => 0x9712
  | 163 => 0x9a12
  | 164 => 0x138e
  | 165 => 0x129512
  | 166 => 0xd5d2
  | 167 => 0xd8d2
  | 168 => 0xda52
  | 169 => 0x184b
  | 170 => 0x597d1
  | 171 => 0x5c591
  | 172 => 0x17c591
  | 173 => 0x24b
  | 174 => 0x12c3d2
  | 175 => 0x12d692
  | 176 => 0x12c592
  | 177 => 0x12c5d2
  | 178 => 0x194591
  | 179 => 0x749
  | 180 => 0x98cd6
  | 181 => 0xcd716
  | 182 => 0xcc5d2
  | 183 => 0x138cd6
  | 184 => 0x139716
  | 185 => 0x1a8b
  | 186 => 0x58e96
  | 187 => 0x194ec59a
  | 188 => 0x95716
  | 189 => 0x171396
  | 190 => 0x585d1
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 45
  | 7 => 1642
  | 6 => 6411
  | 5 => 3777
  | 4 => 247
  | 3 => 7
  | 2 => 2
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1310+((h/20+packedAt gbK8 (1170+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (68722+((h/664+packedAt gbK7 (60754+(h % 664)*12) 12) % 3501)*12) 12
  | 6 => packedAt gbK6 (341314+((h/2399+packedAt gbK6 (307728+(h % 2399)*14) 14) % 10451)*14) 14
  | 5 => packedAt gbK5 (240471+((h/1356+packedAt gbK5 (222843+(h % 1356)*13) 13) % 5371)*13) 13
  | 4 => packedAt gbK4 (18073+((h/87+packedAt gbK4 (17290+(h % 87)*9) 9) % 314)*9) 9
  | 3 => packedAt gbK3 (575+((h/2+packedAt gbK3 (567+(h % 2)*4) 4) % 12)*4) 4
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc1fc07f81ffff81ffff807c04e73e89f3f3
  | 1 => 0x3e07e3ff83fe0f03fe0f03ff803b5ad976cd9c
  | 2 => 0xc007fc0003fff003fff003ffffc39ce1870e1f
  | 3 => 0x7fffffc000003fffffc0003fc1f01f80fe0
  | 4 => 0x7fffffffffffc0000000003ffe001fff000
  | 5 => 0xfff80000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4210004004801108801108810800000a0050b1
  | 1 => 0x3430a1d881a20a19a20a192b08194a5832c594
  | 2 => 0x80454c042255a02255a0225471c294a1850a0a
  | 3 => 0x108676ad6810804379ccf00612ec1f01d80f40
  | 4 => 0x21079b367379ccf0108040182377e001efa000
  | 5 => 0x39e00038406108806108806043bffff4000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36905
namespace PEqualNP.Outside.L_meta_36905
open PEqualNP.Outside.L_meta_36905.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 16 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 13 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 2 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_128 : Interval s1Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_160 : Interval s1Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_192 : Interval s1Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_224 : Interval s1Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_256 : Interval s1Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_288 : Interval s1Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_320 : Interval s1Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_352 : Interval s1Atlas 3 352 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 364 := (concat (concat (concat bs1_3_0 (concat bs1_3_32 bs1_3_64)) (concat bs1_3_96 (concat bs1_3_128 bs1_3_160))) (concat (concat bs1_3_192 (concat bs1_3_224 bs1_3_256)) (concat bs1_3_288 (concat bs1_3_320 bs1_3_352))))
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
theorem bs1_4_160 : Interval s1Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_224 : Interval s1Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_256 : Interval s1Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_320 : Interval s1Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_352 : Interval s1Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_416 : Interval s1Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_448 : Interval s1Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_512 : Interval s1Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_544 : Interval s1Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_608 : Interval s1Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_640 : Interval s1Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_704 : Interval s1Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_736 : Interval s1Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_768 : Interval s1Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_800 : Interval s1Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_832 : Interval s1Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_864 : Interval s1Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_896 : Interval s1Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_928 : Interval s1Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_960 : Interval s1Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_992 : Interval s1Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1024 : Interval s1Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1056 : Interval s1Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1088 : Interval s1Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1120 : Interval s1Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1152 : Interval s1Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1184 : Interval s1Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1216 : Interval s1Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1248 : Interval s1Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1280 : Interval s1Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1312 : Interval s1Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1344 : Interval s1Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1376 : Interval s1Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1408 : Interval s1Atlas 4 1408 15 := block_range (n:=15) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1423 := (concat (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128))) (concat (concat bs1_4_160 (concat bs1_4_192 bs1_4_224)) (concat bs1_4_256 (concat bs1_4_288 bs1_4_320)))) (concat (concat (concat bs1_4_352 bs1_4_384) (concat bs1_4_416 (concat bs1_4_448 bs1_4_480))) (concat (concat bs1_4_512 (concat bs1_4_544 bs1_4_576)) (concat bs1_4_608 (concat bs1_4_640 bs1_4_672))))) (concat (concat (concat (concat bs1_4_704 bs1_4_736) (concat bs1_4_768 (concat bs1_4_800 bs1_4_832))) (concat (concat bs1_4_864 (concat bs1_4_896 bs1_4_928)) (concat bs1_4_960 (concat bs1_4_992 bs1_4_1024)))) (concat (concat (concat bs1_4_1056 (concat bs1_4_1088 bs1_4_1120)) (concat bs1_4_1152 (concat bs1_4_1184 bs1_4_1216))) (concat (concat bs1_4_1248 (concat bs1_4_1280 bs1_4_1312)) (concat bs1_4_1344 (concat bs1_4_1376 bs1_4_1408))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_64 : Interval s1Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_128 : Interval s1Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_160 : Interval s1Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_224 : Interval s1Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_256 : Interval s1Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_320 : Interval s1Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_352 : Interval s1Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_416 : Interval s1Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_448 : Interval s1Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_512 : Interval s1Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_544 : Interval s1Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_608 : Interval s1Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_640 : Interval s1Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_704 : Interval s1Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_736 : Interval s1Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_768 : Interval s1Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_800 : Interval s1Atlas 5 800 30 := block_range (n:=30) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 830 := (concat (concat (concat (concat bs1_5_0 (concat bs1_5_32 bs1_5_64)) (concat bs1_5_96 (concat bs1_5_128 bs1_5_160))) (concat (concat bs1_5_192 (concat bs1_5_224 bs1_5_256)) (concat (concat bs1_5_288 bs1_5_320) (concat bs1_5_352 bs1_5_384)))) (concat (concat (concat bs1_5_416 (concat bs1_5_448 bs1_5_480)) (concat bs1_5_512 (concat bs1_5_544 bs1_5_576))) (concat (concat bs1_5_608 (concat bs1_5_640 bs1_5_672)) (concat (concat bs1_5_704 bs1_5_736) (concat bs1_5_768 bs1_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 40 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 10 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
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
  · exact alls3_3 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 7 := bgb_3_0
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
theorem bgb_4_224 : Interval gbAtlas 4 224 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 247 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_3776 : Interval gbAtlas 5 3776 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3777 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856)))))) (concat (concat (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 bgb_5_2080))) (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336)))) (concat (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560))) (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816))))) (concat (concat (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat (concat bgb_5_2944 bgb_5_2976) (concat bgb_5_3008 bgb_5_3040))) (concat (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)) (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296)))) (concat (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520))) (concat (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648)) (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 bgb_5_3776)))))))
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
theorem bgb_6_6400 : Interval gbAtlas 6 6400 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6411 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)))))) (concat (concat (concat (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))) (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))))))) (concat (concat (concat (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744))) (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968))))) (concat (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))) (concat (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768)))))) (concat (concat (concat (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))) (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)))) (concat (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))) (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))))) (concat (concat (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760))) (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984)))) (concat (concat (concat bgb_6_6016 (concat bgb_6_6048 bgb_6_6080)) (concat bgb_6_6112 (concat bgb_6_6144 bgb_6_6176))) (concat (concat bgb_6_6208 (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400))))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1642 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 45 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0feeaeaeaeeeaeae0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808426 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36905.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.and,[2,9]⟩,⟨.and,[7,9]⟩,⟨.or,[0,6]⟩,⟨.and,[5,8]⟩,⟨.or,[11,13]⟩,⟨.and,[12,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36905

open PEqualNP.Outside.L_meta_36905 in
theorem PEqualNP.Outside.L_meta_36905 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
