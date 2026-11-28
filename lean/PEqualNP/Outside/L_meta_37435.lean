import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37435.Model
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


end PEqualNP.Outside.L_meta_37435.Model

namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
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

def SBf (j : Nat) : Nat := [4, 4, 4, 8, 6, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 33]

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

end PEqualNP.Outside.L_meta_37435

namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xf83fff803fe00ff803fffc03fc07f80ff98c7
  | 4 => 0xffc1ffffc0000ffffc01fffc0007fff01e0f8
  | 5 => 0xf0001fffffffff0000001fffffff800001ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4110825924928a28a4924552d2d4a5a952ab5b
  | 2 => 0x822104aa4925145149248aa565694ad2a555ad
  | 3 => 0xd47609376239a69a63b913f0398c7318f998c6
  | 4 => 0xe843b1c473b1d8e47231dcf9b0307c7c31e0f0
  | 5 => 0xf7bde0783c1e0f87c3e1f3e3e3e6060c1fe00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37435
namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
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
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf80fe01fe01fffc07c0fe07e07e0fff016327c
  | 3 => 0xfffffffe03ffffff0007fffff03fff83f8f
  | 4 => 0xfff0001fffffc0007fffff8007fffc001fc3f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8202142224204880851648a48a1451542d4b5
  | 2 => 0x556554ce51d4a91abe0aac56c568eba0d6325c
  | 3 => 0x468992949491b23256a81065965a22ca982b0a
  | 4 => 0x64cd1b19191923a3673cd941079cb0831d43e0
  | 5 => 0x870e1c1e1e1e3c3c7bcf1e79e410c30c1fbc00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37435
namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xf80fe01fe01fffc07c0fe07e07e0fff016327c
  | 3 => 0xfffffffe03ffffff0007fffff03fff83f8f
  | 4 => 0xfff0001fffffc0007fffff8007fffc001fc3f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8202142224204880851648a48a1451542d4b5
  | 1 => 0x556554ce51d4a91abe0aac56c568eba0d6325c
  | 3 => 0x468992949491b23256a81065965a22ca982b0a
  | 4 => 0x64cd1b19191923a3673cd941079cb0831d43e0
  | 5 => 0x870e1c1e1e1e3c3c7bcf1e79e410c30c1fbc00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37435
namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x843f541087ee6210fd0c421f790843f621087da4210fd48421f2908437e50086faa010df94f40ef29e815e53d02faa7a07754f40aea9e81be43d037887a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f50e40bf294817d529037c85206f10a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81be435037886a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6205f54c40dfa1881bd43102fca4205f54840df21081bc42102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a661be54cc27ca9985f55330deaa6613d54cc2f8a9985f94b30bea96617e51cc2faa3987e90330fca06617f548c2fca9186f952309f2a4617d548c37aa9184f55230be2a4617d538c3bc87187750e30bf294617d528c3bc6518770ca30bf28c617d518c3bc6318770c630bf28461df308c3f661185fd5130bf2a2617d544c2f8a8985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8185f55030be2a0617e530c3bc86187750c30bf290617d520c3bc6418770c830bf288617d510c3bc6218770c430bf28061fa400c3f2801877cc030fd18061dd300c3f26018764c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xc5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a17d94742bb28e857d51d0beaa3a15d54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0997ed4132bda82657c504cbf0a0995e14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cafca7a0df54f41dfa1e83bd43d06fca5a0fb94b41b7296837d52d07daa5a0db54b41df21683bc42d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520efd0a41dea14837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941df21283bc42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883be43107788620df94841bea9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c6faa418df94431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c87ec8390fd50721fb98e43f431c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea9443ee42887da8510fbcca21f6194437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fb90821f6a1043ef32087d86410df94421fb20
  | 2 => 0x592600006c4001890008f037a3f000000000001b20000000002c0000013b0000003698e34c8884d04c000668000d64282ec5c04e000730118000004490e80042a0000024e054000050f80008bc000e4184000000fe2801690b000000000000000004ace2209000000000254f05710980026432000000000834f000000068cb20000000003d9091de45c0409c06a8cc83058000380000001f6000d7a6a000000c2800000000000000000004a8002a82247f87500000000000000000861e10004dc000d01e40004f2054200002184b00041c6ba6200000073045000104f30d52744f4381d60c832d109db3385210e1200dc90c6d24c36a21032947000594b88000007000019949a050be0860004540000008e001258ba3ca000311e211a000000000000013600005e000de800000304000fa3925bc001aa000708568d44ce415368b100000000000000000001ec000000001e900000000000000000001b60000003580000042c5e8000003b400000284000000000004b4001ae0000000000011c03c000c700000000126000620000000005f4000000cc000fb8e50e83b0e280000000000000000244000000000008c00030600000000000000e8a6300066014a320005d0fb179000000460000005dc5fa5e0340000000029647d221f31d43600025f00000000135000001330243020000000000073cc11ef2f600000000232248aaa28000000000002b2000000b914400135a3a180000001cb27e69c4191b4e600000000000000b00004e02bd138004b4000000000006ccd48960000009a00000000000000000000000000a600000000000000000003909092d8003a0000c80003560008d005000000ea8db0001a0099fa0005ad038420005440000000000132800000006008010000000040080f00e000010060000040100200400000800002000000020060080000400001000000008000010000100140000000400000801002010008050020000380000200000002004014010000000000000000601000001000008008070040080000300601c0200900000400000000004010000060080000101400800802000004008000000000000000200000802000000000000120000380300400000001000008000000060000080000202801001000000030000000000000200a0140000001200000800004008000050000080200b0040000000000400c0100000001000001004008008020020140c80000000c098000040000080000000001000004018000050080040400100000400001008000080000000000000100000afca5a1df54b43bf28e877d51d0efca1a1fe94343bd286877d50d0ff2a1a1de54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877
  | 3 => 0x8c470f70a80000008125d160818000e747c000718000000000000020600000000000000001fd4729a4a7800328000598001861f87883710a3244e8802ae88cb080000079c441291d66106694a1d049c01a252ec2f0f5a0f0002840012405c000000000005582900000085c000932b033c0000000000000000000000000690003b80010f13613c000000008480005e0a20000006003a000b910a000000000000667346e8001be59c0000022c27c00006000000000000000012aa0c2e00000019f0002d055000000524000000000000000019c25000079000294ed04a03e845209d227c0f1058000004b09c8572c64a8c6827000000000004b00f4000000000006f0000000002e1ba0000005ba242d264c001b04b20000003f000060ca8004dc5cc00101000444f80000004d85aa2a00067420063000118c38123c8000000000000000000013234c002520be2f80000025028c180544149dc001bf000400b60004de0009819e00000000000000000ae80032e0008a1452bc000000003d000000000000000000000000a000000000000000003646580000100000000000000310391c7198208bd000000880000ab0000001a00001200000000000000000220000013c800000000691434e854c539a80ee000002530009c40000018c1640014d0000011882d000000000003440000000000054000000000764000000007d45493c000298339753e463c002183da0000000003875000000000000001dc23c344ec1440643f0dd8560c2001131b9342000000000000e0000003e80000010d00000000000000000001ad3e28b0000000fa0000021a24600000247000000000000000013a9bc0006006e0000004cc8827234802c7a86c0000000000021c738748730a0010970001ee1c4bf2301021fc0397f0000000000046e000928000000011c000000000001ca000940000000000009896a1480000b8761c40e8241c3408000000000003c1011a50009d80020347a0000000046a25c068870002b0000000000ac9c1dd2d02600014c2c466c0000038c804000000000e40012108893ceb8000004bc1b0f93d46f80108a3225680f02600095c70a2d2b600000268000030001860000010d855000000ef000208630e98000001f1230004c247400000042000501220000004780000000000178000000c9141358080000100003d11580e0580000000000000000000000000000490001e0fc800000054350902da3cc001b40220011d8000000007b24911616c84000000000000000000012504d000314001f815c0c524208000000b30000003291a00000000120000000000001fc2dc87ca900038277c0018b3706dc0000000044c0005d00078c001ff0008d8d000000000000000000000001fb29c0010f2192be001228fd4009451718a0000640001b0002d8ff254000
  | 4 => 0xf40f8000004ac8a53225c41c0ec000002
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x9544c27761551309d185544c23e64149308f590524c23e64145308f590514c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30b6582430c23f64548308f191520c27761548309d185520c29d640c830b6580320c23f64544308f191510c26f62544309b189510c29d640c430b6580310c23e64940308f592500c2796590030b658e400c3994390030e690d400c29d64cc030ae592300c2d9638c03097d95300c27b654c030b6d95300c35b654c030b6d91300c2d9644c030b6189300c2d8614c0309798c54c825d63153208fd9153c823c6454f208f99053c823d6414f208f99251c823d6494720d6d4c30c827661152209d584548823e64d4e208f593538827661d4e209d587538823e6494e208f592538823f64546208f191518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614f204836451881208f596540823e64150208f993530823d64d4c208f990530823d6414c209d98453082756114c20cb552210832d5408420d9544210833954cc0209e5943008339540c020d654c300826f6548020b9185200827b6548020b618d200825e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c435b530c3109b988548426d62152108f993538423d64d4e109b98b538426d62d4e108f992538423d6494e108fd91528423c6454a108f990528423d6414a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104423d65950108f990540423e64d4c108f593530423e6414c108f590530426e6214c109b588530423e64d48108f593520423e64148108f590520425e63148109758c520433554c84109d59421043355408410d9548210433954cc0109e5943004339540c010d654c300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xca3f64542328f191508ca3e64951329d986544ca7561951329e982544ca7960951329dd85544ca7461551329ed81544ca7860551328f994544cb3754d4532cd153514cb375414532cd150514cb673214532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d68c8504ca3d65950328f990540ca5f654c832b6181320ca6f654c832b9185320cab960d0f41cbd0d52d072d4354b41cb54a42d072d5210b419ed8153906786054e41ad58742906ad62d0641b998b419065f63542419718d509063e65d0d41ae583435063e6510941b998b415063d6590c41ad587421063f6550841ab58b411063f65504419dd95411066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc67a60152319e580548c63e6494a318f592528c63f64542318f191508c63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c72f54d4931cb153524c72f5414931cb150524c76452cc531ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c7685214131d68c4504c63d65950318f990540c65f654c431b6181310c677654c431b9189310c73561953218f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f21cd95241c86b5640c721cb58a548863e64d4e218f593538867a60d4e219e583538863e6414e218f590538872e5490a21ab59032886ad64c8621cd553218866d62951219d586544865f63551219718d544867b60551219e181544863f6454d218f191534866f6254d219dd85534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530867b6054c219e181530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b9586420866d650c821ab59032086e5610c8218f992510863d64944219d59641086e56290421e950a41087a642504219d59431086b5640c421b958831086ad64c8421ad59221086e562884219bd9521086776548421b9d9521087676548421b9d9121086e56448421b998d21086e46348421b9181210863f64540218f191500865f63540219718d500871d5390f40c754c43d031d53d0b40ad58742d031d5350b40c754f41d02ad62d0740c754d41d02b960d0e409dd8552902746154a409bd89519026c6254640a758f40902da63d02408f994435023e65d0940ad587425023e65d0540ab58b41502da63d0140ae583431023f6550c408f596421023d6590440a758f401023f65500409ed9540103396095330ce95240cc31d6395230c7952438c29d640ca30a7590318c29d64cc230ce553308c25d63951309e582544c26f62551309b18
  | 2 => 0x152b4000001f2b0a29445732e8b9fc9f37c101e6001b2818d211122c99ace119ec88000c30c230007831a002ccd581251a2a0a000a9b6a6a0009faf8808000004e7597c0c94c7d0006d10a192f4c824c0291ebb344002085406e87b0aad99c0001c068d866b02d19a2a1800bf000aa85a6c0de0017a25a7a7b800000007231494af69180018b86a115656330a3800b903eca1ea0031e901d42d29c1c37266000000880014a000001e80000000980001480031800003881d04a00200de20ca0962e88000007e8809e44000000f2291602716a71800e5a5c98800c381e000586536c49000ceb8e0008400000b18500005e001aa64a7476800b223ea3008b01fa000f0000048d30400060ba800000d06f000000000011a508000509244a964fb2c00306000000008e10986dd8c053968000000031200140000003b9341aaee268002f000d0948a8a12860d640018de8003e2fa3e95400038d986c86ae80317424310ae358629f0d5264b1340738940027000210d90f4cda78c023a8d92ebf9c09d9825685c41ba076026000480bb68000b00000000258471be9424a002b23290e038001d800b7000321d0ab2a0d716e9c9960a80039800cf392b51265cb48a0244640ba000b6598000010200188bcb24a22ce000c2008004c800600ac002f0a500009000000560031c1c98e3da4e2e0da88b388c952749289b35a3f0e2ab976a61ec3ab08000000039882a92aa3603b1f2001a6d4118000a68c0007db1828ada728004aa9a9b9e86e000001783739400000788ce2a800e73909a846d780000104000000000000000a40780026600000d38c4001b6950009a2d80034a351f800000003740d36e330b20033296b34d311400242cf97e430feaf2be692e04b13a7fa16771ba6ba48d883c2a17057b9e219e44e25e5908a00c03008010182f0080100001008080341105c000040700800068000380d004010380000805004160001a03c0100800000030280f0600004800000080040f00c05008010040c01c01000080180004c0000003020060100800c000040105c0b01006000030240000c0602406028020080202408038060000000c13000000341702800004040200102c00008090340000c000100300c030300001001000010040500c010500000c0201c020005301c0c0040001007004020100f000000080d0081101eb960d0e43b69834390e776154a439d1855290e6f62546439b1895190eda60d0d43ae5834310e3f6550c4397d954310eb960d0f42cdd0d51d0b3543547429ed815390a786054e42ad5874290ae661d0a4297d8d5090a5c63542428f9974350ab960d0d42b99874250a3d6590c42ad5874210a3f65508429bd954210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518
  | 3 => 0x3a44209805a9e2fae2d48e80000083a2c001a0e08000004c0d8000438a0b00008936392d2712040000045800dc000b2a38e32e6002a448000000000000077930852566323cc5ac2ae8800839a5b0aecaad00013cdf882612d6b7a28730e0870060eb8070868000008980019a2428000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xa2301a05a0e9030640a800006c00298b8686a8e854a5c34354b4194ae9b2a4210cc4735912108670382c890843295d0634842194ae83024210e155358742d0306a9ac5a0e81265d3654c030990e4b2260184d071591300c24cba0c498061265d0614c030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 634
  | 4 => 467
  | 3 => 14
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (19439+((h/211+packedAt s3K5 (17118+(h % 211)*11) 11) % 1224)*11) 11
  | 4 => packedAt s3K4 (19296+((h/155+packedAt s3K4 (17746+(h % 155)*10) 10) % 617)*10) 10
  | 3 => packedAt s3K3 (706+((h/4+packedAt s3K3 (686+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffe03fc07fffffc0ffffff80fc1fffcff81ff
  | 1 => 0xc07ffffff80ffffff03f01fffffe0fff31fe3f
  | 2 => 0x7ffffffff01fffffc001fffffff07fc1ffc7
  | 4 => 0xff8003ffffffe03ffffffe000fffff83fe0ff8
  | 5 => 0xfffffc000000003ffffffffff0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x430298c47122448c02cb325982c094e45780db
  | 1 => 0x9524294890e48914b01550aa95520d2930b62d
  | 2 => 0x2a4852912241d2295540a13529a5a052c15b46
  | 4 => 0xc616322448903b269a6c4060e394a03aa0db0
  | 5 => 0x307183c3870e1c3f8e38f9c7c0318c63fde000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeac0c0e8e88080eaeac0c0e8e88080eaeac0c0e8e88080eaeac0c0e8e88080eaeac0c0e8e88080eaeac0c0e8e88080eaeac0c0e8e88080eaeac0c0e8e88080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37435
namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1301070016062543288808803bf43bd43be42bc42be41bc41f721ee21ec21f421e421bf40bd40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1800a40611c83000082a80b00405ce54343b328c43a641087488210e990821d221043a75408748a810e9d0c21d2a18431d53d034843a06908540
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x20430a158c54086a16015021a858343087055308740
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 13
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (228+((h/4+packedAt s4K4 (208+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s4K3 (371+((h/4+packedAt s4K3 (351+(h % 4)*5) 5) % 18)*5) 5
  | 2 => packedAt s4K2 (155+((h/1+packedAt s4K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe03fc0fffffffe07fffff01f07ffffe7f81ff
  | 1 => 0x7ffffff01fc07fff83e03fffff83e03f99fe67
  | 2 => 0x7fffffffe0007ffffc003ffffffc003fe1ff87
  | 3 => 0x8003ffffffff81ffffffc001ffffffc1fe0ff8
  | 5 => 0xfffc0000000001fffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x298c462448c106014a64b30302529b22b80ab
  | 1 => 0x242948a1c914a4a5816a1552d483429498b665
  | 2 => 0x4852914483a9494aac1426a569680529615b86
  | 3 => 0x6163220912300d934a5880c18e529601d40d50
  | 5 => 0x7183c38e1c3e71fc739f38f80c631831ffe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeac0eac0ea80ea80eac0eac0ea80ea80eac0eac0ea80ea80eac0eac0ea80ea80eac0eac0ea80ea80eac0eac0ea80ea80eac0eac0ea80ea80eac0eac0ea80ea80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37435
namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x28010341539912513183c909070088021180001c007c00b06089a82e1149d10007801c58a800034d80008088000192814600004e00b04009018244bff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe817d53d03baa7a05754f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53102faa6206fd0c40dea18817e52102faa4206f90840de210817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87986f50f30bf296617d52cc2fca3985f54730bfaa4617e548c2faa9185f15230bea9c61bf438c3bc87186f50e30eea1c619d438c2fca5185f54a30ef19461dc328c2fca3185f54630ef18c61dc318c2fca11877cc230fd984617f544c2fca8985f55130be2a261bf434c37a86985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c37e86187790c30dea1861dd430c33a86185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc65907b4cb20bf28e417d51c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20dfa1a41bd43483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20dfa1841bd43082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43ec63887d4c710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10dfa1a21bd43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec62887d4c510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c530437e86086f50c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x75150af8a2a17d14542ba28a857f5050af8a0a15f95042bf29885de5310abca6215f54c42eea98855d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65de434cb7a86997750d32cea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea96837e50d06faa1a0df55241bf29c837d539077e8720ef50e41bf294837d529077c8520ef10a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41dea1a837f52507dea4a0dbd4941be29283ec52506d8a4a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31ef21e63bd43cc7ba8798e750f31bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c77a8718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c77e8698f790d31dea1a63dd434c73a8698dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf290637d520c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c43bf438877a8710df54a21f7a1443ec42887dc6510fb4ca21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43bf434877a8690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610efd0c21dea18437e52087de8410fb10821f719043ed32086fca210fdd0421fa20843f631087ea6210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a07794f40af29
  | 2 => 0x1d86f40009c3ac9a90c80010068c291da0003f0eca56000a780000000086d2c058090000000000000000006500098000000000a2cbb2ab1040a00016b05e170001720d05b92f000496870000000008fd1e9c20007fc000001dc0000006b000001031053400c800000088000000f10000000000010a4580000000071000000000560a0aaf000000ce0000000000000000022c0008a2e8000000000006d92400010e0000000000000000299172830288005668b03c9c906a0004f0000000000d0ea1b015ca3109000630650301c85f8a21af3dc3cc0000000000000000306000000000000000003a0d42510b8004504314a85f0ba30d3ca0b0003d4b415b4c6a8c000d701a51d572041be000002210003ac928000000014b1ed000000478001c4344002844947ace30003f2370ae8f6068000b12263e2000e00000f60000000020e38c000004ba8cc0029435a001188e825c01cd98cc044738b98f84f496d209540ea3789b07a4460114c000234a140029d000660ba80000000111134274100002511a087d4f9dc19a0000000000600001002000000024000000280080000300800c0000000a000008040120000500100200c090010000040000000000c03003002004008010080080000500c0000080200000400003000000028060000080000500000c010010040040500200600003000000018008030020000080000c000078000040080000101600404000016000018010040040000100200400004002004018000020340000400000c018030020000300100401c0180001a000018000020000000000a00002800002004010040020000300d00c008040000000100000000000c0000100002001801000004060020000000880100002000000000000000050000100380100000c0a00300400001800000008010120120000180201600000800002008000010160100100100000000000018000000000020040080000401400003008008010000017e52d0efaa5a1df94743bea8e877e50d0efaa1a1efd4b43df29687bd52d0f78a5a1efd4743df28e87bd51d0f78a3a1efd4343df28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542fba8a857
  | 3 => 0x8001ee0ec26a2e0007f000000000520000002840003015f0004e422a294c8000f11612ee800001ac000000e60000000006d23a36e544002401a4a29488000004483991c2e291c000005104543b239000000ce935108911210a10628ec389bb3f0000840000004cd1b8000009340f1cb0004e00002300082000000000000cf22735ca380000009c0f8cd16406680cb303d00032cc1292534a30c38003cc1bd4e09a00000000000000000000000000000010e00078c1b8000000015b000000000fa1fd2560000000000000000000042000a6a35098ac8000db27800c0000041c9f8001b20000007480000000000000000000610000005580000000000000000000000000004fa9a53c0fd570a0108000000000000004dca6c000004e00000001129c000000910000641e1ba00062c00000000ae9048250007d800000000484002a7000001449693a895cf80ab4e69f004a8300058c0025f2963e45f8bc4cc7ecdf80226e0009d80004e5b0d88003a4040e08000c60004b8690006995423e2f800091ab7314514da8360000000007000099c878004542d95093f4aa000000000000008886e43c220000bd2600012480054c00000000402000d08000000003e00031c00000000000238512074861b0c29d0000000bca7b0a62f9088004480000012423a000670b500044ca900048a0012c8000ee604002130000000000002a9b452000000000c322d430000001de000000000000000000000000000000000000164f380046c0000011b000018000004280000d8000000000000013013c000435528d0000fb0000000000000000058a2054a0fcda00000000025000000060a02900000009f0000002bc000005680014b95a4b465c582683fc7d4ee8004b80007680000074c36854000728000004d600000000000048000000000000000000000000000332001029f7000524d38e50003200016701c498780c74ca6442a8000fc354801ab0008c800000000230000001060004d800000a9149a6f13298479042000324ca246214ad420a2b3e63e9078ac38a1253b00002c18400000016000b52743aa000d528600060000000000204608002440000006600050c2f0b4000000e390405a0000415500000139127164001439e92204044e8001c033c2d0b30000000000016e3fc000a71c2000f60b801800000000000001568ad0ce8292a0e718805c9690d0000001009202601462800000ac14107f3f48c0430260000008c000000000000000006f8002b1000000988c61ba0e4bd14f0540000018900000000132000858000aa0000000000000000000000000948000002522a4ec0001a645c000000000003ea6c4a076d0e82412c000000004fe000de000000158000003d042c000a000084800000000000002b90004bcb80ef502000cb1d71505305700031e0000000
  | 4 => 0x24c31073c000470006e400000470000f915708c0013892a20c7340092c00066c00150000000001602da0000002c0002940a0000f0868e8800000298f2159000000001031804781580001e6880028d3c2000000004ee640170002f600000000294000d424f0008bc391530001408c80003e00000193000000000001206e0000a3324000c2038000000000000004f4f797f1a800000128052000051a91b26553a8fe4a6a880e1ea0e83d04a8002f0695561df23e12c0008900000000120000000ae0000000010a80000000000000000358311652fa190000000000010100051eaa9310000006c0af09f49c8f0d21c811a4500010231aa80731e017424c0e96f38600000000000895068bb33e16cf2
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe548823e6494e208f592538823e6414e208f59053882766114e209d584538831f5350e20c714d438823d63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e65151208f58c544831f54d4d20c7153534831f64d4d20c7193534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d208f990534823d6414d2097994534831f5414d20c7150534831e6414d20c7590534834d6214d208f997434823c65d0d20c7d4f434831c53d0d208f995434823c6550d20c7d4d434831c5350d20d314e324826c654c920e350d32482e8604c920cdd53514833454d4520d5d4f514835453d4520cdd0f514833543d4520cdd5051483345414520d5d4c51483545314520cdd0c51483354314520d98c851483653214520d9146204825e63150209758c540827661150209d584540823e6494c208f592530823e6414c208f590530826e6214c209d98453082756114c20c794d430831d5350c208fd91510823c6454420d954421082e960084209bd9520082e461480209ed95200825e63153109758c54c423e6494f108f59253c426e6294f109b58a53c423e6414f108f59053c431e5350f10c754d43c423e64d4b108f59352c425e63d4b109758f52c4395434c7109b98b548426d62d52109798e548425d63952108f992538423d6494e108f990538423d6414e109b988538426d6214e10c7d4d438431c5350e108f993528423d64d4a10d9d48218423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c544431f54d4d10c7153534431f64d4d10c7193534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d1097994534431f5414d10c7150534431e6414d10c759053443556114d108f997434423c65d0d10c7d4f434431c53d0d108f995434423c6550d10c7d4d434431c5350d10cbd53524432c54d4910d3d4f524434c53d4910cbd0f524432d43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524432f4314910cb50c5244354538c510d914a3144274654c510e550d3144364524c510bc181314436452841109798c540425d63150109b988540426d62150108f992530423d6494c108f990530423d6414c109b988530426d6214c109d984530431e5350c10c754d430423f64548108f191520423e64148108f590520425e63148109758c52042756508410d954821042f160084109e59610042776544010b9189100427b6544010
  | 1 => 0x863d6414f21c794d43c871d5350f21b558c41c8795434c7219798c548865d63152218f992538863d6494e218f990538863d6414e21c794d438871d5350e21b358c428878d434ca218f58f544863e64951219bd89544867761551219798c544865d63151218f994544869d6315121c798c544863d6315121c758c544861d63151218f992534863d6494d219b58a53486756194d218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f997434863c65d0d218f995434863c6550d21c794d434871d5350d21cd153214872c54885219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219e98053086796014c21c794d430871d5350c219b59442086cd6310821b9584420866d658c821b9586320878d434c8219d59441086d56310421b958841087a442104219d59631086e5628c421e550d31086e562884219bd9521086ac64484219dd9521086b46448421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121086e76348421b958d21087a74348421e950d21086e460484218fd91500863c645402197d8d500865c6354021c799153d031d53d0f40c794d43d031d5350e40a758c429029d6310640a758f409031f5350d40c714d43502b86050d40c754f43102b960d0c409dd8552102746154840a758c421032d52108409bd89511026c6254440a758c41103355110440a758f401023f65500409ed95401031f6550e30c7195438c39b6050e30e6181438c23f6454a308f191528c31d4354a309dd85528c2746154a30a7590328c23f64546308f191518c31d43546309bd89518c26c6254630a7590318c29d64cc2309758e544c26f62551309b189544c27761551309d185544c26e62d50309b58b540c27661d50309d587540c23d6595030c798e540c23f63550308f58d540c23e64150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c25d6590c30a7592430c2d96090c308fd95430c31e5450c30a7d95430c31f6550c30cb952520c32d5494830e350e520c32f4394830cb50e520c31d4354830cb951520c32d5454830e350d520c32f4354830d390d520c32d4354830d350d520c30d4354830d354a320c29d640c830cd952510c3355494430e550e510c3665294430d954a510c3374394430cd50e510c31d4354430cd951510c3355454430e550d510c3665254430d9549510c3374354430d590d510c3354354430d550d510c3154354430d5546310c29d640c430c750e500c29d64cc030e650e300c25f654c0309ed95300c39b434c0309798c54c825d63153208f99253c823d6494f209d98653c82756194f208f99053c823d6414f20c794d43c831d5350f20e350d32c827661d52209d587548825e63952209758
  | 2 => 0x10000e00c0400804010010000400003004010000000c000040002c03010000080d024010040200019008000080d00402000010040002c06000010080c0340001801000020000000002040050000002802004010180200809000100300100806000009dd8552d0e746154b439bd8951d0e6c6254743add8552d0eb46154b43cb54852d0eaf6254743ab18951d0f355114743ce54050d0e9d62d4d43a75875350e9e60d4d43add855250eb46154943aed815250eb86054943cb5485250eaf6254543ab1895150ebb6054543ae1815150f355114543abd895050eac6254143add855050eb46154143ce5405050e3f6550c4397d954310f1e5450c43c754f43d0b1e5350e42c754d4390a5f63542429718d5090b1f5350d42ab1894350b3743d4542cd50f5150b374314542cd50c5150b674214542cd9085150b1e6454c42c754f4310aad62d0c42c794d4310b1d53d08428fd954210b1d5350842ad1854210a6f6550842b91854210a7661d53329d58754ccb1e63953329d98454cca756115332c795143cca9f6550f32c7d9543ccb365494732cd55251ccb954394732cdd0e51ccb354394732c750d51ccb365454732cd55151ccb954354732cdd0d51ccb564354732cd50d51ccb554354732c550d51ccb1d4394332b9987328ca3f64546328f191518ca3f64542328f191508ca7761551329d185544ca7b60551329e181544ca9d6490d3297195434cb1f6550d32c7195434cb8f6250d32e3189434cb8d43cc932b9987324cb1d43d4532c750c504ca3d65950328f990540ca5e63150328f992530ca3d6494c328f597430ca3f6550c32c794d430cb1d54cc83297d95320cb1d544c8329bd95320cb1d53d0f41c794d439071d5350e41a758c429065f63542419718d509071f5350d41ad185435072f43d4941cb50f525072f4314941cb50c525076452d0541cb14a415071e6454c41c754f43106b561d0c41c794d431071d5390841a758c421071d5310841c754f411063f6550441c754d41106ac62504419dd9541106e462504419b98b54cc66d62d5331c798e54cc66e62153319b58854cc71e5450f31a7d9543cc71f6550f31cb95252cc72d5494b31e350e52cc72f4394b31cb50e52cc71d4354b31cb95152cc72d5454b31e350d52cc72f4354b31d390d52cc72d4354b31d350d52cc70d4354b31c750e50cc63f6454a318f191528c6e662cc6318fd91508c63c64542319bd89544c66c62551319ed81544c6786055131a7592434c65c6550d31c7d95434c71c6550d31e5d85434c7946150d31c750f524c79543cc531b998b314c71d43141318f596540c63e64150319798c540c63e6494c318f592530c63d65d0c318fd95430c71e5350c31c7553310c65f654c431c7551310c677654c4319798c54c865d63153218f99253c863d6494f218f99053c
  | 3 => 0x43e9104b4024ffa1a338001031321860009113b2c8984d31c9000000a8800000000d385047e0780015945c7881820949682096800000000000342d25fc0017a0007d134249000000000ca00000000115202400700cd000000ed80029e000b518d38800000000000000cb0f0240001129e50000011a000000000d999728a1500d0c00cc3f1151573560d8e58003a200000000000000001f0000000c78bc00067c34890292000ef0a40000000000000000137800344001009b749a1d41da191288a4530552be9700020c2969211e2180c03a4aa1994ce60cea16646a83846810000000820000000000012600012cb81560b270cc02161b685c478811646a89e878000000000000008e88e0710a203c51000000001209b03b080c371794562cc000003d67dc98175224368298000002f40008e000358c70004000000013a3dc7912aa6e000390000001f2100070002fc340000000005c40002d14e384001250007f4971f9000000000000001786586517291800000168160000000ae000000000002c06100010a0001e0a9000000308000000002e800042428000000005d11c8001141fca90001047a0fe0000225951200000006cc284930e64800111000000d0000000608001b12500000019a0003bc6e0000000005192a0000000010b4cc90800000000000000f8000000b60000000000200000021c2d00025e268001884ae000000483ce3308a06b4b22f8152520000d44b9be000000e38000ec9b12a17d04c88840000006360a004a00000000000000000000002985d8350000001a0000001300000021300040c3223644000000000000000789cd0c647c099720300310fa1035e8c8000000000005fa4500051c0000004659c000001d46410a15d2de684000773506e4c4800188008000002c637d280000007741780040a000000000000012f0000f87bc6e800000000000b733689c0020b0f40000000000031446099000254000332426d40001548e0940025f20a00000000000828001930006440000008c00027856000000999a30003ac0e8000002240e0000003b0000070580007394d000944000a8000000000b5000000d20e81ee468eb000000000000002b64fc000001401cc001e90005f0af0001c648c001a90004c4da24418e274000000000000004e0006b84901f4700000020700005800000000474fa92b2328c015800000000000c8080000101000008020140000c01020040000600003004020000300005028160080001c03004000400600c00000000200400401000130000102800004000100301804010000040001c0700803034000040100c07004000040000009004000000b000030300000002038000040c00804004000000101001014030100103c08024030040001009014000000600000024010000201002000000080001c1b008
  | 4 => 0xfb13607a714849cc0da2781f1bb4d6000dc19d22e0005626d0003d81c1944a60000018b0008f49ba2f1dc17ce993c000354458000740005c0000160000014a4ba3212515a0a405c768003be7ec238000000b867a1e000000000001ea5700000000000000000000770031130000000021d1223c9078002f60000007900049c4fa044e06e8729423c08c50d8001a23fd319843cc0008400000063132896204704fc1ed302110e5041000000d9262000000798004ac000b080044c764cc0934c06b04da2d00041cb000016200000000000000a1a3b09a88c0000000a7c40000a0482a92d9d20623f8000004801c02e106290001198003a00013500026a2e85b0de0001312183f000768090ad00020cb69d51ae4e0948000006d81386c00061857000000000879390007008c2643d40345d8c92ee8340c9bd1cc4d07e8ce3d8000000080008a109258000854000431820000014e1f4518ac032000000fd24f000000000000002ac21150282000f981449c58800000000000000002aa2206a23e4d27c8420d327c6f0870294583ec33a112e6218140a51c46540018a0006fc3f1e304475c6c97823c000a98f4000000e4000000000001c20000011080008a4b06905b0009c48696e0000006324c0000004e06f4046b48b1e1040000001ce2360dc390003fc8711b9c6000000861442485ac578000c45a050874072678e787b34a00
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xf800a00008003240880001b169800148b9d9790801380150800199c9ea01192870000219c2280000b0e1a931600209f0d900d090022120003801594250f058000002491010009800000049a001900078680001882800e8c001f9b800006050217000401a100000c801e231d238a839300001800214085000099f06000820404280000005247154852d0e92392a228e8725dc562d4d4391ee4b0ea6a1d24715485250e94382a429287491c95114543a60e0a88a2a1d28725405050e9838aa028287491c94314542c1aa6b1686214a47158b4310b0aa98c2a1085a150e61cc932a48e2a18a4a0e15535874310652392c3a18838354c6250441d0a873166298d0d7294d434868ab8ca6a1a43071d95350d21a30e0a9a8690d15731532148686b98a910a43291d1618c821b0ae62108210e856310841086523a2c518843235cc644842192ae63224210ca6749912108662b98c890843615cc6448421d0ce63224210ca5731912108742b98c890843215cc6448421948e8b1a4210ce07058d21086523b68690843291d94348421d0ac6a1a4210e0d63548421029238aa4210818558d5110440a48e4a88822061543d85528c306a1ec4a8c61c150d5294430e0a87292a21870543549510c28ab8ca6a1e41455c45350e20c1ac8b10a69050c7550d324830632a8699241a250c604c920e0a86990a290560704c8514820eb98c8a8841491d15108420a1ae529a878850d7214d438420eb9cc9a9421499d35208610c2ac8b08a6885147550d314430a32a8698a21c150c524c510d2286302628866052181314420eb98c8a9021491d15208410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1409408ca000235b080000e00522c05531c562d0c42c05531c961d0c418848758d4348421a808058d4348421c05631c55210840c05631c95110440a088550c604c920d01431c13214520905831d15108420905839d35208610a108550c604c510e0143148604c510905831d15208410
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (756+((h/14+packedAt s5K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s5K5 (21436+((h/233+packedAt s5K5 (18873+(h % 233)*11) 11) % 1226)*11) 11
  | 4 => packedAt s5K4 (25868+((h/208+packedAt s5K4 (23788+(h % 208)*10) 10) % 999)*11) 11
  | 3 => packedAt s5K3 (3850+((h/25+packedAt s5K3 (3675+(h % 25)*7) 7) % 110)*8) 8
  | 2 => packedAt s5K2 (800+((h/4+packedAt s5K2 (780+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3ffff03ffffff81fffff07ffc1ffff9e3f1ff
  | 1 => 0xfc0ffffc07f07ffe0f83ff87ffe1e03e9c7e67
  | 2 => 0xfff03ffff8007ffff003fff87ffe003f1f8f87
  | 3 => 0x3fffffff81fffffc00007fffffc7e00ff8
  | 4 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x98208118912010005284b0088c02298821b0ab
  | 1 => 0x296312287244a49605a15485352142928c5665
  | 2 => 0x50c5a45120e9492ab04269505a540525168b86
  | 3 => 0x628a3882448c0dcd29680c4463999607c00d50
  | 4 => 0x830c30e3870e71f1ce738e6603111807fb6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80eae8ea80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37435
namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1c00c00544ab007002c3b4e000003c0203300f8016000184274ad280b4000006851b1a0000000000000001129015ac8000b8a410a5f2aa4c00b000000e404e6f19710501de0049201b1a08000000f46220819a800a704004c280020000182001000002100031018001040005ff54017f95005fd54017f15003ff5300dfd4c03fe5300ff54c037d5300ff14c03ff4300efd0c03fe4300ff50c03bd4300ff10c05ff51017f94405fd51017f14401ff41007f90401fd41007f10403ff3100ff8c403fd3100ff0c401fe21007f48401fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc4000ffcc003fe3000ff4c003fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842000fec421004ffeca88026ff6544001bfb2a20009fd951004ffcca8800afe6544013feb2a2009bf5951004ff8ca8800afc6544013be32a20029f19510007fec888002ff6444001dfb222000afd9110007fcc88801efe6444001feb222000bf59110007f8c88801efc6444001de3222000af1911004ffea888027fe5444013feaa22009ff15110047fec688022ff6344001efb1a2000b7d8d10047fcc688006fe6344011feb1a2008bf58d10047f8c688006fc6344011ee31a2001b718d10047fea6880237f5344011ff29a2008ff54d10046faa688023fc5344011ffa1a2008efd0d10047fc8688023fd4344011dea1a2008ff10d10007fec488002ff6244001f7b122000bbd8910007fcc488002fe6244001feb122000bf58910007f8c488002fc6244001f63122000bb1891004ffea488027fe5244013fea922009ff14910007fe8488003fe4244001fea122000ff10910047fe6488023fe3244011fe9922008ff0c91004ffea288027fe5144013fea8a2009ff14510007fe8288003fe4144001fea0a2000ff10510047fe6288023fe3144011fb18a2008ff4c510047ea6288023fc3144001ff90a2000ff88510007fa4288003fc2144013ffa822009ff9411004ffaa088027fc5044001ffa022000ff90110007fa8088003fc4044011ff9822008ff8c110047fa6088023fc3044001ff9022000ff88110007fa4088003ff1044001fd8822000ff84110007ec2088013ff65040097fb282004ff99410015fcca080137e65040053f3282004ff59410025faca080037d65040013eb282004ff19410015f8ca08003ff64040017fb202000ff9901003dfcc808003fd64040017eb202000ff1901003df8c808013ff5404009ff2a02004ff55010027f8a80800fff63040077fb182003ff98c1000dfcc60800ffd63040077eb182003ff18c1000df8c60800fff5304007bfa982003ff94c1001ffaa60800f7d5304007fe2982003ffd0c1001f7e860800ffe4304007fea182003ef50c1001ff88608003ff62040017fb102000ff98810005fcc408003fd62040017eb102000ff18810005f8c408013ff5204009ff2902004ff54810027f8a408003ff4204001ff2102000ff50810007f8840800fff3204007ff1902003ff4c81001ff8640801afe6104009ffa882004ff94410027faa208013fc5104001ffa082000ff90410007fa8208003fc4104007ff9882003ff8c41001ffa620800ffc3104001ff9082000fdc8410007fc4208003fd2104001fe1082000fd0841002dfcc008013ff5004009ff2802004ff54010027f8a008003ff4004001ff2002000ff50010007f8800800fff3004007ff1802003ff4c01001ff86008003ff2004001ff1002000ff48010007f84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x2fe611000ffeb088000bf5844003ff8c220037ff511001bff288800dff5444006ff8a22001fff411000fff2088000ef9044003ffa822001ffc411000fde208800cffcc440067fc6220033fd3110019fe1888000ff88440007fa4220003fc211001d7f300800dffd404006ffca020037fd501001bfe2808007ffd004003f7e802001ffe401000ffd2008007ff500400077a802001ff94010019ff980800cff8c040067fa6020033fc3010017ffb2e200bbfd971005ffccb8800afe65c4017feb2e200bbf5971005ff8cb8800afc65c4001ffb262000bfd9310007fcc98801efe64c4001feb262000bf59310007f8c98801efc64c4017ffaa6200bff9531005ffaa98802ffc54c400dffb1e2006bfd8f10037fcc788006fe63c400dfeb1e2006bf58f10037f8c788006fc63c400dffa9e2006dfd4f10037fca78801bfd53c400dbea9e2006ff14f10037fe878801bbf43c400dff21e2006ff50f100377a878801bfc43c4001ffb162000ff98b10005fcc588003fd62c40017eb162000ff18b10005f8c58802fff52c4017ff296200bff54b1005ff8a588003ff42c4001ff2162000ff50b10007f8858801bff32c400dff1962006ff4cb10037f8658802fff51c4017ff28e200bff5471005ff8a388003ff41c4001ff20e2000ff50710007f8838801bff31c400dff18e2006fd8c710037fa638801bf531c400dfe18e2000ffc8710007fc4388003fd21c4001fe10e200bffd431005ffca18802ffd50c4017fe2862000ffd0310007fc8188003fd40c4001fe2062006ffcc310037fc618801bfd30c400dfe1862000ffc8310057fecb0802aff6584015ff32c2002bf99610057facb0802afd6584015fe32c2002bf19610007fec908002ff6484001ff3242007bf99210007fac908002fd6484001fe3242007bf19210057fea90802bfe5484015feaa4200aff1521002ffec708016ff638400bff31c2001bf98e1002ffac708016fd638400bfe31c2001bf18e1002ffea7080177f538400bff29c2005ff54e1002efaa708017fc538400bffa1c2005efd0e1002ffc8708017fd438400bdea1c2005ff10e10007fec508002ff6284001ff3142000bf98a10007fac508002fd6284001fe314200affd4a10057fca50802bfd5284015fe2942000ffd0a10007fc8508003fd4284001fe2142005ffcca1002ffc6508017fd328400bfe1942008bf58610057fea30802bfe5184015fea8c200aff14610007fe8308003fe4184001fea0c2000ff1061002ffe6308017fe318400bfe98c2005ff0c610007fe4308003f72184001ff10c2000ff48610007f84308003f421840077f304200affd4210057fca10802bfd5084015fe2842000ffd0210007fc8108003fd4084001fe2042005ffcc21002ffc6108017fd308400bfe1842000ffc8210007fc4108003ff1084001fb8
  | 2 => 0x4003fbac7a0002dd63d000ffe31e8001bf18f40097fea7a004b7f53d0025ff29e8012ff54f40096faa7a004bfc53d000fffa1e8007efd0f4003ffc87a001ffd43d0025dea1e8007ff10f4003ffec3a001ffe61d00017f30e8007ff58740005fac3a001ffc61d0027ffa8e8013ff9474009ffaa3a004ffc51d000fffa0e8007ff9074003ffa83a001ffc41d0025ff98e8012ff8c740097fa63a004bfc31d0001ff10e8000ff48740007f843a004fff50d0027ff2868013ff5434009ff8a1a004bff30d0025ff1868012ff4c340097f861a0047ff65900237fb2c8011ff99640015fccb200477e65900053f32c8011ff5964008dfacb200037d65900013eb2c8011ff19640015f8cb2003efd6490023ffaa48007ff9524008f7ca920047fd5490023deaa48007ff15240077fec72003aff639001dff31c8001bf98e40077fac72003afd639001dfe31c8001bf18e40077fea72003b7f539001dff29c800eff54e40076faa72003bfc539000fffa1c800eefd0e40077fc872003bfd439001ddea1c8007ff10e40007fec320003fe61900017f30c8000ff58640005fac320003fc6190023ffa8c8011ff9464008ffaa320047fc519000fffa0c8000ff906400077c8320003fd419000ffe20c8000ef10640077fe632003bfe319001dfe98c800eff0c640007fc4320003fd2190001fe10c8007bf9824008ffea120047fe5090023fea848011ff1424003ffe8120003bf409000ffda04800effcc240077fc612003bfd309001dfe1848010ffd9540085fecaa0043fe65500057f32a8010ff59540085facaa0043fc65500057e32a8010ffd514003ffca8a0043fd545000ffe2a2800fffd8d4007dfec6a003ffe63500037f31a800fff58d4007dfac6a003ffc63500037e31a800fffd4d4007efea6a003ffe535001ffea9a800fdf54d4007ff8a6a001fff435001fdfa1a800fff90d4007ffa86a003fbd435000ffe21a8000ffd8540005fec2a0003fe6150001feb0a8000ff18540005f8c2a0043ff5150021ff28a8010ff54540087f8a2a001fff4150001ff20a8000ff5054003ff882a003fff315001fff18a800fff4c54007ff862a0003fe2150001fe90a8000ff08540087fea0a0043fe5050021fea828010ff1414003ffe80a001ffb4050001ff2028000ef9014007ffe60a003ffe305001ffe982800fff0c14003ffeca2001eff651000fff3288002bf9944003ffaca20036fd651000ffe3288007bf1944003dfcc82001fff541000fff2a08007ef9504003ffaa820037bd541000ffe2a08007ffd8c4003dfec62001ffe63100037f3188007ff58c40065fac62001ffc63100037e318800cffd4c40066fea620033fe5310019fea98800cdf54c40067f8a62001fff431000fdfa188007ff90c4003ffa8620033bd431000ffe2188007ffd844003ffcc22000
  | 3 => 0xf21c4216ff50e210b77a871085bfc438842f7eb144219ffd4a210cffca510867ee5288433fea944219fb54a210cff8a510803ff4288401f7a144200ff90a21007fa8510803fc4288401f62144216ffcca210b7fc651085bee328842dfe9944216fb4ca210b7f86510852fe6188433ffa8c4219ff946210cffaa310867fc5188401ffa0c4200ff90621007fa8310803fc418842dff98c4216ff8c6210b7fa631085bfc3188401ff90c4200fdc8621007fec110803fe60884017f3044200ff58221005fac110803fc6088433ffa844219ff942210cffaa110867fc508842dff9844216ff8c2210b7fa611085bfc3088431ffb2a4218bfd95210c7fcca9080afe6548431feb2a4218bf595210c7f8ca9080afc6548401ffb224200bfd9121007fcc89081efe6448401feb224200bf59121007f8c89081efc6448431ffaa24218ff951210c7faa890863fc544842fffb1a4217bfd8d210bffcc690806fe634842ffeb1a4217bf58d210bff8c690806fc634842fffa9a4217dfd4d210bffca69085ffd534842fbea9a4217ff14d210bffe869085fbf434842fff21a4217ff50d210bf7a869085ffc4348431ffa8a4218ff945210c7faa290863fc5148401ffa0a4200ff90521007fa8290803fc414842fff98a4217ff8c5210bffa629085ffc3148401ff10a4200fb88521007fec090802ff6048401ff3024200ff58121007f8c090802fc6048431ffa824218ff941210c7faa090863fc504842fff9824217ff8c1210bffa609085ffc304842bffb284215bfd94210affcca1080afe650842bfeb284215bf594210aff8ca1080afc6508401ffb204200bfd9021007fcc81081efe6408401feb204200bf59021007f8c81081efc640842bffaa04215ff950210affaa810857fc5408429ffb184214bfd8c210a7fcc610806fe6308429feb184214bf58c210a7f8c610806fc6308429ffa984214dfd4c210a7fca610853fd5308429bea984214ff14c210a7fe8610853bf4308429ff2184214ff50c210a77a8610853fc430842d7f3084215ffd44210affca210857f6510842bfea884215fd544210aff8a210803ff4108401fba084200ff90421007fa8210803fc4108401fa2084214ffcc4210a7fc6210853f63108429fe9884214fd4c4210a7f86210803fe2108401fb1084200ff48421007ea4210803e52108401ffb004200ff98021005fcc010803fd60084017eb004200ff180210affea010857fe500842bfea804215ff140210a7fe6010853fe3008429fe9804214ff0c02103ffecba001eff65d000fff32e8002bf9974003efccba000a7e65d000ffeb2e8013bf5974003efacba00027d65d000ffe32e8007bf1974003ffea9a001ffe54d000ffeaa68007ff1534003ffec7a001eff63d000fff31e8001bf98f4003fbcc7a0006de63d000ffeb1e8012bf58f
  | 4 => 0x803fc609043fffa84821fff942410fffaa12087ffc5090439ff984821cff8c2410e7fa6120873fc309043dffb2a821ebfd9541006fecaa08027f655043dff32a8202bf995410f7facaa087afd655043dfe32a8202bf195410f6f8caa080a7c655043dffaa28207ff951410f7faa8a081ffc545043bffb1a821dbfd8d410effcc6a0806fe635043bfeb1a821dbf58d410eff8c6a0806fc635043bffa9a821ddfd4d410effca6a0877fd535043bbea9a821dff14d4103ffe86a0877bf435043bff21a821dff50d410ef7a86a081ffc4350401ffb128200bfd8941007dec4a0802ef6250401ff3128200ff58941007f8c4a0802fc6250401f63128200bb189410f7fea4a087bfe525043dfea92821eff1494103ffe84a0803fe4250401fea12821dffcc9410effc64a0877fd325043bfe192821effd45410f7fca2a087bfd515043dfe28a8207ffd054103fee82a0803fe4150401df20a821dffcc5410effc62a0877fd315043bfe18a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a087bff505043dff282821eff541410f7f8a0a0877ff305043bff182821dff4c1410eff860a081fff651040f7fb288207ff99441015fcca2081f7e65104053f3288207ff594410ddfaca2081f7d65104013eb288207ff1944103df8ca2081efe641040fffaa08207ff9504103ffaa82081ffc541040fffb188207bfd8c4103ffcc620806fe631040fef3188201b798c4103ffac62086afd631040feeb188200b758c4103ff8c620806fc6310435ffa98821adfd4c410d7fca62086bfd5310435bea98821aff14c4103ffe862081fbf431040fff2188207ff50c410d77a862081ffc431040fffb108207ff98841005fcc42081ffd62104017eb108207ff188410dffea42086ffe5210437fea90821bff1484103ffe842081ffe421040ffea108207ff108410d7fe642086bfe3210435fe990821aff0c8410e5fcc22086fff5110437ff288821bff544410dff8a22081fff411040fdfa088207ff9044103fec822081ffd4110401dea088207fd504410d7fe622086bfe3110435fe988821aff0c44103ffec02081ffe60104017f3008207ff58041005fac02081ffc6010437ffa80821bff940410dffaa02086ffc5010435ff980821aff8c0410d7fa602086bfc3010433ffb2c4219bfd96210cffccb1080afe6588433bf32c42029f996210cffacb10866fd6588401beb2c42009f596210cff8cb1080afc6588401ffb244200bfd9221007fcc91081efe6488401feb244200bf59221007f8c91081efc6488433ffaa44219ff952210cffaa910867fc548842dffb1c4216bfd8e210b7fcc710806fe638842dfeb1c4216bf58e210b7f8c710806fc638842dffa9c4216dfd4e210b7fca71085bfd538842dbea9c4216ff14e210b7fe871085bbf438842df
  | 5 => 0xf00760000301200200c008050000000200e0000380100a0060880100401e0880c00002a0000081700008400000000000000040020680800000c00c0001d0100001580b0040143400d000010010000120042800d0020e401801078008030060060080000001a04c02804010030098000300486f00000e0a427800000000040010da0040400000c0100281a00c0140000300601400033002030010020000500380102c0000080100200409805000000060010a40d0008170020181b800000050000250180000000306401402806010024000020000500000100027c0000500c00003008008000000150020100480001400c0900202201401001004074000010020101e84800000409800008034010010000d400000004030010430000480200300c0b0008050140080580010c0200780a0020180b81b0040240180000005c0080100202c010010020b4000010280100000002e0000100603c0180080f004008000000040480e0060000600800900601c028000042981980304a0000081205202c010af03600000802014110000260480000fffb2e8207bfd974103ffccba080afe65d040ffeb2e8221bf5974103ff8cba081efc65d040fffaa68207ff9534103ffaa9a081ffc54d040fffb1e8207bfd8f4103ffcc7a0806fe63d040ffeb1e8220bf58f4103ff8c7a0806fc63d0441ffa9e8220dfd4f41107fca7a0883fd53d0441bea9e8220ff14f4103ffe87a081fbf43d040fff21e8207ff50f411077a87a081ffc43d040fffb168207ff98b41005fcc5a081ffd62d04017eb168207ff18b4110ffea5a0887fe52d0443fea968221ff14b4103ffe85a0883ff32d0441ff1968220ff4cb41107f865a0887ff51d0443ff28e8221ff5474110ff8a3a0883ff31d0441ff18e8220ff4c741107f863a081fff60d040fff3068200bf9834103ffac1a0802fd60d040ffe3068221ffd434110ffca1a0887fd50d0443fe2868220ffcc341107fc61a0883fd30d0441fe186821fffd96410fdfecb2087ffe65904057f32c821fff596410fdfacb2087ffc65904057e32c821dbf592410fffea92081ffe549043ffeaa48207ff152410e7fec720872ff6390439ff31c8201bf98e410e7fac720872fd6390439fe31c8201bf18e410e7fea7208737f5390439ff29c821cff54e410e6faa720873fc539040fffa1c821cefd0e410e7fc8720873fd4390439dea1c8207ff10e41007fec520803fe62904017f3148200ff58a41005fac520803fc629043fffa94821fff94a410fffaa52087ffc529040fffa148200ff90a410e7fe6520873fe3290439fe994821cff0ca4103dfcc32087fff519043fff28c821fff546410fff8a32081fff4190401dfa0c8207fdd06410e7fe6320873fe3190439fe98c821cff0c641007fec120803fe60904017f3048200ff58241005fac120
  | 6 => 0x3c18caa6923bbd90ef09f1850003e43082d943342f0e0b7c00011f00048946734100d1ca2961da4073390a32cb8b20581b7cce2dc03826748345c09a34b40634e0e434c49248533728a11344702d36f3b32421bcc940003e601e4172cd8002d202c2c89322200434b640a2758001bf0002eb20b36d09e1f9ae50000000002cd00021f3031a00a200000000f80017e3ee12824b16f0ee3f641b48d2c92802fa00036134d21e1a89d014a2cb27d06903448f3aa0740924c61a32810003508001bb23f8003440002791b623f4bc1cd17a1b521d1f1a7c83c36339e3023d046c0820f0c4018843a0912ac3fa3521e20ac4311ae1b326b1b23c837636aa6200029027119627a012c8e1b1bff0001ef3669e40004ca1161c51f08374aa3b905746604620547e4a93ba2fc0e82e02661c028b2fb27e20e2d38990e529f20d1ac0f33dc33001cb16a34a291f8c6986d10d0ff071b2d33b42425116e0a527ba00c9549014343828e1c31d402fcc21943c23b649b4653a40fe1afa3a83292f1733d60e11ff8a406437f1d31483af279bf222844c13e4a63270fb2841b89074a72603790004030af2a113a0bd1ac8003a703b3b711c2370eb3e10f84bd37e4283314584179dc3698002410003d10098004782b20001374c01bab6581421a0f73c1367a7b0000fc285ab83d42c1a429af2081670062af25c0000000002192fd1172c7cae0f20a12c300041c3322c5ccf0bc2da10641005c3bf4b846b0b9125287c0f0000133e700011a00000000018d10e40c00000000029700000007b00000033600034000000000031b0004161043383f729a06342e1294a12a815b2d18001db0a03b225d3fd0000000000000000b826100034701883080006e3cd2f80000004360004290004082553e50e7c0d14b280c7b2452e20000f93460001e929215800000000005503307a1b5add09d0000000003974d71c74151420002bd0cf00000000500042c0000000000000000680002502ad00000002a41f36e40b4b20d30004430000001e839b0000000004cc05b1ce15f0000004140000004c43d830539643b0000040003b804801062018000050320000200000a05c080050020bc0301e00004c0200002a01c0001403401812000008000020170120104e8c10000980300000200406001004008038020200000880b0da0240081c01c080008020020000000201e0602380602a02c0080000a0040380300e0009401414e1d4020130060540000000c00c0001901a1dc0001c00200c0680f002038008050280d80480100c0240c8190000e00800000400c000000002fc048020060000f0680001000600205219c0000e01e224018030080a00100e01c0640000011e0100d80016600c08010016000010000020000b00700002c03802006068040000040040000b01c0900080001801c000
  | 7 => 0x3980d01ff2db19d15400001f08d1090000d73f310012a24f0774d10013ca22435b2b12b71089ee4870dd1fe0322a50000243fb00000000000000000a2d531c3e90002533da0000001f801928900032a18c0940000001058004090363663340000d50002740001be3e30bf0000000d619f30d8d425e0b137b12b2580860001f39a70001cb0390841f10650df00035432917b46447312207104f353314b1923d00038d30430a20a00031813000e30c1782f041808a17f09716549e4bb04a43c1350000004320531f01392943153583cf14c9c23114570002fe0be142b702c3b222992e824631246009b1860004460002f74b41f69b09151f522701aa8498929c07e1ec2882c211130638c1ad079b1d0f04232b93163bb1bd39d14d43d106bc2aa722fc3f1869971fa93f34528d4c80752d119e0ee8b300300015d076b0c8524493138850181e637d23c26c28745a19a1a447d3202723b500008335e22a23e15c0000001720000001fca3920c00045939c2f10979fbb11aca9e34d54690414ba2df24c0c032f235238bce2e93f02213ec011ac54bf49c42b3132521121643861618d92c71210004270000949d20120003d300019549601d46d0002cea3327da3a2bf8e700f44a1144452642150709fdba50292cc4a22ba39f2bb2472c12853551de0c8949ad02ef2e611928205e028452236a75276a5b1c647f0d817c16837401db5a2683f50ec0e224a0aa3591a9ad4bed1270312e112c82544d01533c00b0510930810471b40220791c9175233cb52f44882b325a1f5a3ea7800705a3b1240057c803a90764d34ab2031233188213514a838027f22c26a0261e746e1a803000408f381095c262c601c3df1ee99208e35d2c43f40422362d5872141b241ab0882ee19c2bc35c2be1d74213fe45334f3bc1693b41cc07c27a84509608b4351fa34803d9aa4631ae8b00cd2ea1f93681ba3423689cf29516b3f802e20910137a3db008b563b83281ea2910540870a705d1f61450108a60a294647608c1f22771e0310af206c0cc12e4551f33002100f13653ea29d2f536424e0ab30e1f70ae2121360233c3b9324320f09537545427c0fd0e62c2b50144bf14a51b28f636730fa829b131e3c023ca81a1129e3ae4c33782d81fc0594612040172b64561f4be03d749f46245f27345e0b50c13ab1b6ca41fb1053923693872832073ad2e711d41126341e1311a646849122338b4af0bb3178c93c34841f2a9318e1810f50b4162c7c26e2ca2d32d408944221618b18445015fc81240ba11240c748c1632ccc823570319994931c845b2e44b32f306b1080fa1f41904b74200350003c740e2300492ce2329fd2b04c90e00ba2de23186a000477416960a860002482ae0004a02a00c833301985db2100000047a0002cf1df0c610c0004d62c84980001d12c9b8a4c5
  | 8 => 0x1b485609c4d800026d0001773c638331a4c70ce1b725f15114f22e2f903e00919813339a3b031f09822644f07f8c2278c010d2277a7628c12c18736b3881aba6524390b0000001621a91aa91e0001c12e300000000015513c0602418003820002ff0003851f780033a00021718a00031000049701a3cb3623ac27f8003d23602b544e3a01660c30404cb0000000001801b84ad237b263a63bd1494a33dd0673894ac0700004be2341b9b8433f3be00000034a21c1dd0f3b6c0000000e300032c0000000003c94022b424421800041a0001022490f414021b2d29031793c54220e687895011804e43e2869bbaaa4b12543e243014e28f03d00000000048a47122b00000000046a1d83d522200000000000000030e8001c40b70a900044800000000000018200000000007f37332b3a81342a929b25717d0002c4b3505f44110a00000000020230d2592cf8000002ec2a40dc13b03f1e50000001100004000000000113173f904c48b0b60004c10001ed00000000800019313800004442a2701078002c686200041300037119b4054440000000001fec1200001600031280000c00008180042517047238f1412ed43913298c8efb8a91b30b0db0000000001a24b923080004d0003230001ad94400000016a14c00000000000000026f0a830f00010f0000782d0c1900000031400030729837238e47500006f22f31595a0ad23b0000002011591a100040416c000077b7749a16d14a8da46f00000000007d120000156283bef3a30733494992140cb3431a52d71b04d41613eb153319a0613d0001760001eb00a84b1bc000147000235a13390ccd2a62c002b2f600000042d0ea00000041d1e106143400015200000024d3a227e8021570f2a3845d1262a20de43700000049d01b2324741b39600ca0003010001713251d530923100000000000012d0000000c50274d90e93cc2560101b947023997439518f0003fc0000004790004b048603a000143b6a0ed33e0500660968e88000d12a335f4d009015e3c423da2d44b2d632e39939118302f1912ab0801d63900000000000004513e80003940c40000002003de0e5a2500004800033d1d91ef8000200002bf4d207e8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7630841019ef5630841019f77530841019f75530841019fb7430841019fb543084101adf67208410007e67208410006f76208410007e66208410006f56208410007e56208410006e562084101a7e652084101a7e55208410007e74208410007e4420841019fe6320841019fe53208410007f27008410005f57008410007f17008410196f66008410004fd76d00100257e75d00100057d75d001009e7e65d00100067d65d001001dde73d0010005dd73d0010004ff769001003cfd76900100257e75900100057d759001008e7e65900100067d659001003ebe6490010006bd6490010005f67190010005f57190010004ff76500100867e65500100067d655001003cff7610010004fe7610010004fd761001003cfc761001006e7e65100100067d651001003ebe6410010006bd6410010005f67110010005f57110010004fd76c801018e7e65c80100067d65c8010004ff7688010004fd76880101867e65880100067d6588010006ee6288010006ed6288010005f67188010005f57188010007e42188010004ff76480100057f75480100257c754801017e7e65480100067d6548010005bf7448010005bc7448010005df734801001ddc7348010005f77148010005f47148010004fe7608010004fd7608010004fc76080101767e65080100067d6508010005f67108010005f57108010007e4210801005e7e65c40100067d65c4010036f576c401016f7665c40100077565c4010166f763c4010166f563c40101677753c40101677553c4010167b743c4010167b543c4010005f672c4010005f472c40100567e65840100067d658401014df57184010146f6618401001df9768401002ef9768401000cf9768401015f7a65840100077965840101577b5384010157795384010157bb4384010157b9438401014df97184010146fa6184010007f26184010007f32184010007f02184010004ff76440100057f75440100257c754401004e7e65440100067d6544010005bf7444010005bc7444010005df734401001ddc7344010005ef7244010005ec7244010005f77644010006f77644010004f7764401000777754401012f74754401012f766544010007756544010007b77444010007b47444010007d77344010127d47344010126f76344010126f56344010127775344010127755344010127b74344010127b54344010007e77244010005f67244010005f47244010007e47244010005e4724401013df77044010136f66044010005fb7644010006fb7644010004fb76440100077b754401012f78754401012f7a6544010007796544010007bb7444010007b87444010007db7344010127d873440101277b5344010127795344010127bb4344010127b94344010007eb7244010007e8724401011dfb7144010007f37144010116fa6144010007f26144010
  | 1 => 0x881020cfd70588100257e75188100057d75188100067e65188100067d6518810005be7418810005bd741881001dde7318810005dd7318810006ed6218810004ff7518810014fe75188100067e75188100147e7518810004fd75188100067d75188100047d7518810014fc751881003cfe7418810006be741881003cbe7418810004fd7418810006bd7418810004bd7418810004ff731881000cfe7318810006de731881000cde7318810004fd7318810006dd7318810004dd731881000cfc73188100067f53188100067d5318810006bf4318810006bd4318810004fe7118810006f67118810004fe7018810006fa701881003cff76d0810004fe76d0810004fd76d081003cfc76d08102067e65d08100067d65d081003ebe64d0810006bd64d0810005f671d0810005f571d0810004ff7690810004fe7690810004fd7690810004fc76908101fe7e65908100067d6590810006ee6290810006ed6290810004ff7650810004fe7650810004fd7650810004fc76508100057f75508100257c75508101f67e65508100067d655081003ebe6450810006bd6450810006ee6250810006ed6250810005f77150810005f4715081003cff7610810004fe7610810004fd761081003cfc76108100257e75108100057d75108101ee7e65108100067d651081001dde7310810005dd7310810004fd76d041010e7e65d04100067d65d0410004ff769041003cfd76904100fe7e65904100067d659041003ebe6490410006bd6490410005fa7090410005f97090410004ff76504100057f75504100257c75504100f67e65504100067d6550410005ef7250410005ec725041003cff7610410004fd76104100257e75104100057d75104100de7e65104100067d651041003ebe6410410006bd641041001dde7310410005dd7310410005fa7010410005f97010410004fd76c84100257e75c84100057d75c84101e67e65c84100067d65c8410005f576c8410006f576c84101df7675c84100077575c84101def765c84101df7665c84101def565c84100077565c84100067565c84101d6f664c84101d6f464c84101cef763c84101cef563c84101cf7753c84101cf7553c84101cfb743c84101cfb543c8410006f762c8410006f562c8410005f570c84101c6f660c8410004ff7688410004fd76884100257e75884100057d75884100ce7e65884100067d6588410006ee6288410006ed62884101bdf67188410005fa7088410005f97088410004ff76484100c67e65484100067d6548410004ff7608410004fd76084100ae7e65084100067d6508410006ee6208410006ed6208410007e52108410005fa7008410005f97008410006f57608410004f576084101a6f765084101a77665084101a6f565084100077565084100067565084101b6f664084101b6f4640841019ef
  | 2 => 0x73d43594100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100063f43594100067e43594100067d43594100063d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c32594100267f71594100067e71594100267d71594100267c71594100067f31594100067e31594100067d31594100067c31594100267f70594100067e70594100267d70594100267c70594100067f30594100067e30594100067d30594100067c30594100267c10594100257e75d90100057d75d90100067e65d90100067d65d9010004ff75d9010014fe75d90100067e75d90100147e75d9010004fd75d90100067d75d90100047d75d9010014fc75d9010004ff73d901000cfe73d9010004fd73d901000cfc73d90100067f53d90100067d53d9010006bf43d9010006bd43d9010004fe72d9010004fd72d9010004fe71d9010006f671d9010004fe70d9010006fa70d9010004fd76990100067e65990100067d6599010006bf649901003cff76590100067e65590100067d6559010004ff7559010014fe7559010004fd7559010014fc7559010006bf7459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d5359010006bf4359010006bd4359010004ff7259010004fc725901003cff715901003cfd715901003cff705901003cfd70590100257e75190100057d75190100067e65190100067d651901003ebe6419010006bd641901001dde7319010005dd7319010005ee7219010005ed72190100257e75d88100057d75d88100067e65d88100067d65d8810004ff75d8810014fe75d88100067e75d88100147e75d8810004fd75d88100067d75d88100047d75d8810014fc75d881003cfe74d8810004fd74d8810004ff73d881000cfe73d8810004fd73d881000cfc73d88100067f53d88100067d53d8810006bf43d8810006bd43d8810004fe71d8810006f671d8810006fa70d8810004fd76988100067e65988100067d6598810006ef6298810004ff7598810014fe7598810004fd7598810014fc759881003cfe7498810004fd7498810004ff739881000cfe7398810004fd739881000cfc73988100067f53988100067d5398810006bf4398810006bd4398810006ee3298810006ed32988100067e65588100067d6558810004ff7558810014fe7558810004fd7558810014fc7558810004ff745881003cfc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810006bf4358810006bd4358810006ef7258810006ee3258810006ed3258810214ff71588100bcfd7158810006f4715
  | 3 => 0xf63c8510216dc63c8510006ef62c8510006ec62c8510005fa70c8510005f970c8510004fe768851004d7e75885100057d75885100067f65885100ce7c6588510006bf6488510006bc6488510006df63885100b6dc6388510006ef6288510006ec62885100067f65485100c67c6548510006bf6448510006bc6448510006df63485100bedc6348510006ef6248510006ec6248510005fb7048510005f87048510004fe76085100067f65085100ae7c6508510006bf6408510006bc6408510006df63085100a6dc6308510006ef6208510007e52108510004fe76d011004d7e75d01100057d75d01100067f65d011009e7c65d0110006bf64d011003ebc64d0110045de73d0110005dd73d0110006df63d0110096dc63d0110006ef62d0110006ec62d0110005f671d0110005f571d0110004fe769011004d7e75901100057d75901100067f659011008e7c6590110006bf649011003ebc6490110006df6390110076dc6390110006ef6290110006ec629011003cff7650110004fd765011003cfc76501100067f65501100867c6550110006bf645011003ebc6450110006df635011007edc6350110006ef6250110006ec6250110005f77150110005f47150110004fe76101100067f651011006e7c6510110006bf641011003ebc6410110006df6310110066dc6310110006ef6210110006ec6210110004fe76c81100067f65c811018e7c65c8110006bf64c8110006bc64c8110006df63c8110246dc63c8110006ef62c8110006ec62c8110005f671c8110005f571c81100067f65881101867c6588110006bf6488110006bc6488110006df638811023edc6388110006ef6288110006ec6288110004fd7648110004fc76481100067f654811017e7c6548110006bf6448110006bc6448110006df634811020edc6348110005f77148110005f471481100067f65c411005e7c65c4110006bf64c4110006bc64c4110006df63c4110036dc63c4110006ef62c4110006ec62c41100077b65c41102377865c4110007bb64c4110007b864c4110007db63c411022fd863c411022f7b53c411022f7953c411022fbb43c411022fb943c4110007eb62c4110007e862c411022ff231c411022ff131c41100067f65841100567c6584110006bf6484110006bc6484110006df638411002edc6384110006ef6284110006ec6284110007776584110227746584110007b76484110007b46484110135f77384110135f57384110007d7638411021fd4638411021f77538411021f75538411021fb7438411021fb54384110007e76284110006f66284110006f46284110007e46284110006e46284110007f360841100257f76594100267f76594100147f76594100057f73594100057d73594100067f63594100067e63594100067d63594100067c63594100073f4359410
  | 4 => 0x8910007af4318910007ad4318910007e63118910007e53118910006ef7518910006ee7518910006ed7518910006ec7518910006ef7418910006ee7418910006ed7418910006ec7418910006ef5418910006ee5418910006ed5418910006ec5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef53189100066f5318910006ee5318910006ed53189100066d5318910006ec5318910006ef4318910006af4318910006ee4318910006ed4318910006ad4318910006ec4318910006ef7118910006ef5118910006ee5118910006ed5118910006ec5118910006ef3118910006ee3118910006e63118910006ed3118910006e53118910006ec3118910006ef7018910006ed7018910006ef5018910006ee5018910006ed5018910006ec5018910006ef3018910006ee3018910006ed3018910006ec3018910006ed101891003cff76d0910004fe76d0910004fd76d091003cfc76d09100067f65d09102067c65d0910006bf64d091003ebc64d0910006df63d0910266dc63d0910006ef62d0910006ec62d0910004ff7690910004fe7690910004fd7690910004fc76909100067f65909101fe7c6590910006bf649091003ebc6490910006df639091025edc6390910006ef6290910006ec6290910004ff7650910004fe7650910004fd7650910004fc76509100057f755091004d7c75509100067f65509101f67c6550910006bf645091003ebc6450910006df6350910256dc6350910006ef6250910006ec6250910005f77150910005f4715091003cff7610910004fe7610910004fd761091003cfc761091004d7e75109100057d75109100067f65109101ee7c6510910006bf641091003ebc6410910045de7310910005dd7310910006df631091024edc6310910006ef6210910006ec6210910005f67110910005f57110910005fa7010910005f97010910004fe76d05100067f65d051010e7c65d0510006bf64d051003ebc64d0510006df63d0510106dc63d0510006ef62d0510006ec62d0510005fa70d0510005f970d0510004fe76905100067f65905100fe7c6590510006bf649051003ebc6490510006df63905100e6dc6390510006ef6290510006ec629051003cfc76505100057f755051004d7c75505100067f65505100f67c6550510006bf645051003ebc6450510006df63505100eedc6350510005ef7250510005ec7250510006ef6250510006ec6250510005fb7050510005f87050510004fe761051004d7e75105100057d75105100067f65105100de7c6510510006bf641051003ebc6410510045de7310510005dd7310510006df63105100d6dc6310510006ef6210510006ec6210510007b54110510004fe76c851004d7e75c85100057d75c85100067f65c85101e67c65c8510006bf64c8510006bc64c8510006d
  | 5 => 0x6ed43d8910006ad43d8910006ec43d8910006ef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef30d8910006ee30d8910006ed30d8910006ec30d891004d7e75989100057d75989100067f65989100067c6598910005be7498910005bd7498910006bf6498910006bc6498910045de7398910005dd7398910006df6398910006dc6398910006ef6298910004ff7598910014fe75989100067e75989100147e7598910004fd75989100067d75989100047d7598910014fc759891003cfe7498910006be749891003cbe7498910004fd7498910006bd7498910004bd7498910004ff739891000cfe7398910006de739891000cde7398910004fd7398910006dd7398910004dd739891000cfc73989100067f53989100067d5398910006bf4398910006bd4398910004fd7198910006f57198910006f63198910006f53198910006f970989100057f755891004d7c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df7358910045dc7358910006df6358910006dc6358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891003cfc7458910006bc745891003cbc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006bf4358910006bd4358910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed6218910004ff7518910014fe7518910004fd7518910014fc751891003cfe7418910004fd7418910004ff731891000cfe7318910004fd731891000cfc73189100067f53189100067d5318910006bf4318910006bd4318910006ee7218910006ef5218910006ee5218910006ed5218910006ec5218910006ef3218910006ee3218910006ed3218910006ec32189100a4fc7118910006f63118910006f53118910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d531
  | 6 => 0xc321911003ebf711911003ebd7119110006bf5119110006be5119110006bd5119110006bc5119110006bf3119110006be3119110006bd3119110006bc311911003ebf701911003ebd7019110006bf5019110006be5019110006bd5019110006bc5019110006bf3019110006be3019110006bd3019110006bc3019110006bd1019110045de76d8d10046de76d8d1000cde76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d100079f74d8d100079c74d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10007d771d8d10047d471d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d100069f74d8d10006de74d8d10006dd74d8d10006dc74d8d100069c74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df71d8d10046de71d8d10046dd71d8d10046dc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df70d8d10046de70d8d10046dd70d8d10046dc70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10046dd10d8d100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d8910014fe75d8910004fd75d8910014fc75d891003cfe74d8910004fd74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006bf43d8910006bd43d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef32d8910006ee32d8910006ed32d8910006ec32d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d8910007af43d8910007ad43d8910007e631d8910007e531d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006af43d8910006ee43d8910
  | 7 => 0x9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf73d9110005bd73d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110007b631d9110007b531d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110004bf73d9110006be73d9110006bd73d9110004bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d911004d7e75991100057d75991100067f65991100067c6599110006bf6499110045de7399110005dd7399110006dc6399110005ee7299110005ed72991100057f755911004d7c75591100067f65591100067c6559110005df7359110045dc7359110006dc6359110005ef7259110005ec7259110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110004ff7359110006df7359110004df735911000cfe7359110004fd735911000cfc7359110006dc735911000cdc73591100067f53591100067d5359110006bf4359110006bd4359110004ff7259110006ef7259110004ef7259110004fc7259110006ec7259110004ec7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911003ebe6419110006bd6419110006dc6319110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110005bf7319110005bd7319110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d5319110007b63119110007b5311911003ebf751911003ebe751911003ebd751911003ebc751911003ebf731911003cbf731911003ebe731911003ebd7319110004bd731911003ebc7319110006bf53191100063f5319110006be5319110006bd53191100063d5319110006bc531911003ebf721911003ebe721911003ebd721911003ebc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006b
  | 8 => 0x1c6f563c86101c77753c86101c77553c86101c7b743c86101c7b543c8610007e662c8610006f562c8610007e562c8610007f270c8610005f570c8610007f170c86100557e75886100057d7588610006ef6288610006ee6248610006ed6248610005fb7048610005f87048610007e52108610005f57608610006f5760861027ef7650861027ef565086101b6f664086101b6f46408610196f76308610196f56308610197775308610197755308610197b74308610197b54308610007e67208610006f76208610007e76208610006e76208610006f56208610007e4620861027fe6520861027fe55208610007e74208610007e44208610197e63208610197e53208610005f570086100557e75d02100057d75d021002dde73d0210005dd73d021003cfd76902100557e75902100057d759021003ebe6490210006bd6490210005f67190210005f5719021003ebe6410210006bd6410210005f67110210005f57110210005f67188210005f57188210007e42188210005f576c4210006f576c4210276f763c4210276f563c42102777753c42102777553c4210277b743c4210277b543c4210005f672c4210005f472c421026ff250c421026ff150c4210005f976c4210006f976c42102777b53c42102777953c4210277bb43c4210277b943c421026ff251c421026ff151c421004d7e76d951004e7e76d95100147e76d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100073f43d95100073d43d95100077631d95100077531d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100063f43d95100067e43d95100067d43d95100063d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951004e7e71d951004e7d71d951004e7c71d95100067f31d95100067e31d95100067d31d95100067c31d95100067f70d951004e7e70d951004e7d70d951004e7c70d95100067f30d95100067e30d95100067d30d95100067c30d951004e7d10d951003cfe76d91100067f65d91100067c65d9110006dc63d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d9110006bf43d9110006be43d9110006bd43d9110006bc43d9110004fe72d9110004fd72d911003cfe71d911003cfc71d911003cfe70d911003cfc70d911003cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d
  | 9 => 0xe75d9210004fd75d92100067d75d92100047d75d9210014fc75d9210004ff73d921000cfe73d9210004fd73d921000cfc73d92100067f53d92100067d53d9210006bf43d9210006bd43d9210004fe72d9210006ee72d9210004ee72d9210004fd72d9210006ed72d9210004ed72d9210006f571d9210006fa70d9210004fd76992100557e75992100057d7599210006bf649921002dde7399210005dd739921003cff7659210004ff7559210014fe7559210004fd7559210014fc7559210006bf7459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210006bf4359210006bd4359210004ff7259210004fc725921003ebe6419210006bd6419210004ff75d8a10014fe75d8a10004fd75d8a10014fc75d8a1003cfe74d8a10004fd74d8a10004ff73d8a1000cfe73d8a10004fd73d8a1000cfc73d8a100067f53d8a100067d53d8a10006bf43d8a10006bd43d8a10006fa70d8a10006ef6298a10004ff7598a10014fe7598a10004fd7598a10014fc7598a1003cfe7498a10004fd7498a10004ff7398a1000cfe7398a10004fd7398a1000cfc7398a100067f5398a100067d5398a10006bf4398a10006bd4398a10006ee5298a10006ed5298a10006ee3298a10006ed3298a100057f7558a100557c7558a10004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067c7558a100147c7558a10004ff7458a1003cfc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a10006bf4358a10006bd4358a10006ef7258a10006ee5258a10006ed5258a10006ee3258a10006ed3258a100557e7518a100057d7518a10006ed6218a1003cff76d0a10004fe76d0a10004fd76d0a1003cfc76d0a10006ee62d0a10006ed62d0a10005f671d0a10005f571d0a10004ff7690a10004fe7690a10004fd7690a10004ff7650a10004fe7650a10004fd7650a10004fc7650a100057f7550a100557c7550a10005f77150a10005f47150a1003cff7610a10004fe7610a10004fd7610a100557e7510a100057d7510a1002dde7310a10005dd7310a10006ee6210a10006ed6210a10005fa7010a10005f97010a1003ebe64d0610006bd64d0610005fa70d0610005f970d0610006bf649061003ebc649061003cff76506100057f75506100557c755061003ebe6450610006bd6450610005ef7250610005ec7250610005fb7050610005f870506100557e75106100057d7510610006bf641061003ebc641061002dde7310610005dd73106100557e75c86100057d75c8610006ee62c8610006ed62c8610005fa70c8610005f970c86102877675c86100077575c8610286f765c8610286f565c86101d6f664c86101d6f464c86101c6f763c8610
  | 10 => 0x93100067c75593100147c7559310006bf7459310006be5459310006bd5459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d5359310006bf4359310006bd4359310004ff7259310004fc725931005d7e75193100057d751931003ebe6419310006bd6419310035de7319310005dd731931005d7e75d8b100057d75d8b10005be74d8b10005bd74d8b10035de73d8b10005dd73d8b1005d7e7598b100057d7598b10006ef6298b10004ff7598b10014fe7598b100067e7598b100147e7598b10004fd7598b100067d7598b100047d7598b10014fc7598b1003cfe7498b10004fd7498b10004ff7398b1000cfe7398b10004fd7398b1000cfc7398b100067f5398b100067d5398b10006bf4398b10006bd4398b10006f63198b10006f53198b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1003cfc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10006bf4358b10006bd4358b10006ed6218b10004ff7518b10014fe7518b10004fd7518b10014fc7518b1003cfe7418b10004fd7418b10004ff7318b1000cfe7318b10004fd7318b1000cfc7318b100067f5318b100067d5318b10006bf4318b10006bd4318b10006f67118b10006f63118b10006f53118b10006f97018b1003cff76d0b10004fe76d0b10004fd76d0b10004ff7690b10004fe7690b10004fd7690b10004fc7690b1003ebe6490b10006bd6490b10004ff7650b10004fd7650b10004fc7650b100057f7550b1005d7c7550b10005f77150b10005f47150b1003cff7610b10004fe7610b10004fd7610b1003cfc7610b1005d7e7510b100057d7510b1003ebe6410b10006bd6410b10035de7310b10005dd7310b10005f67110b10005f57110b1003cfd769071003ebe6490710006bd6490710005fa7090710005f970907100057f755071005d7c7550710005ef7250710005ec725071005d7e75107100057d751071003ebe6410710006bd6410710035de7310710005dd7310710007b54110710005fa7010710005f9701071005d7e75c87100057d75c871005d7e75887100057d7588710006ee6288710006ed6288710005fa7088710005f97088710006ee6208710006ed6208710007e52108710005fa7008710005f9700871005d7e75d03100057d75d031003ebe64d0310006bd64d0310035de73d0310005dd73d0310005f671d0310005f571d031005d7e75903100057d7590310006bf649031003ebc649031003cff765031003ebe6450310006bd6450310005f77150310005f47150310006bf641031003ebc6410310005f671c8310005f571c83100557e75d92100057d75d9210005ee72d9210005ed72d9210004ff75d9210014fe75d92100067e75d92100147
  | 11 => 0x4ff7648540004fe7648540004fc7648540004fe7608540004fd7608540004fc760854003dbe7408540005bd7408540006f76108540006f46108540007e52108540005fa7008540005f970085400857e75901400057d759014003dfa709014003efb60901402e73e75901400073d75901402e6bf65901402e6bd659014029dbf739014029dbd73901402debf63901402debd63901402df3f53901402df3d5390140006bc619014003dbe709014003ebf609014003fbb6090140004ff7598440014fe7598440004fd7598440014fc7598440004ff739844000cfe7398440004fd739844000cfc73984400067f53984400067d539844003ebf4398440006bd4398440004fe7298440004fd729844003ef67198440006f65198440006f5519844003ef7419844003ef44198440006f63198440006f53198440004ff75584400067f75584400047f7558440014fe7558440004fd7558440014fc75584400067c75584400147c7558440004ff735844000cfe7358440004fd735844000cfc73584400067f53584400067d535844003ebf4358440006bd4358440004ff7258440006ef7258440004ef7258440004fc7258440006ec7258440004ec725844003ef77158440006f65158440006f5515844003ef7415844003ebc415844003ef4415844003eb44158440006f63158440006f5315844003dbd7690440006bd76904402d5bf75904402d5bd75904402cdbf73904402cdbd739044003ebf63904402c6bd63904402c73f53904402c73d5390440005be729044003dbe719044003fb67190440006bd6190440005bd70904402bebe609044003fba6090440004ff768844003cfe7688440004fd768844006d7e75884400057d758844003dbe7488440005bd74884402b7ac4288440006f66188440006f56188440004ff7648440004fd764844003cfc7648440005bf744844003dbc7448440006f66148440006f56148440004ff760844003cfe7608440004fd7608440005bf740844003dbc74084401b7b44108440007e5210844003dbf7650040006bf7650040004bf76500402adbf75500402adbd75500402a5bf73500402a5bd735004003ebf635004028ebd635004028f3f535004028f3d5350040005bc715004003dbf705004003fbb705004029ebe605004003fba6050040297ba5050040297b9505004028fbb305004028fb83050040004ff75d9310014fe75d9310004fd75d9310014fc75d9310004ff73d931000cfe73d9310004fd73d931000cfc73d93100067f53d93100067d53d9310006bf43d9310006bd43d9310004fe72d9310004fd72d9310006f671d9310006f970d9310004fd7699310006bf649931003cff76593100057f755931005d7c7559310004ff75593100067f75593100047f7559310014fe7559310004fd7559310014fc755
  | 12 => 0x56190640005fa7090640005f9709064033dbf759064033dbd75906403373e65906400073d659064032dbf739064032dbd73906402bebf63906402bebd63906402bf3f53906402bf3d5390640005be729064003dbe7190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b9709064003ebe60906400057f755064008d7c75506400f67e65506400067d6550640005ef7250640005ec7250640006f66150640006f56150640005fb7050640005f87050640005bd761064003ebd761064003dbf751064003f3e7510640325bd751064003f3d75106400053d751064031f3e65106400073d651064003dbf731064003f9e7310640315bd731064003f9d73106400059d731064030ebf631064030ebd631064030f3f531064030f3d5310640005be721064003fb67110640006bd6110640005bd701064003fba6010640004ff7688640004fe7688640004fd768864008d7e75886400057d75886400ce7e65886400067d658864003dbe7488640005bd7488640006ee6288640006ed6288640007ac4288640004ff7648640004fd7648640004fc76486400c67e65486400067d6548640005bf744864003dbc7448640004ff7608640004fe7608640004fd76086400ae7e65086400067d6508640005bf740864003dbc7408640006f66108640006f56108640007b44108640007e52108640005fa7008640005f97008640005bd76d024003ebd76d024003dbf75d024003f3e75d0240305bd75d024003f3d75d02400053d75d02402ef3e65d02400073d65d024003dbf73d024003f9e73d02402fdbd73d024003f9d73d02400059d73d02402f6bf63d02402f6bd63d02402f73f53d02402f73d53d0240005be71d024003fba60d02402efba50d02402efb950d0240004ff75d8540014fe75d8540004fd75d8540014fc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d8540006bf43d8540006bd43d8540004fe72d8540004fd72d8540006f761985400057f75585400857c7558540005df735854007ddc7358540005ef7258540005ec72585400857e75185400057d7518540006f56118540004ff7518540014fe75185400067e75185400147e7518540004fd75185400067d75185400047d7518540014fc7518540004ff731854000cfe7318540004fd731854000cfc73185400067f53185400067d5318540006bf4318540006bd4318540004fe7218540004fd7218540006f76190540006f46190540005fa7090540005f970905400057f75505400857c7550540005ef7250540005ec7250540006f76150540006f4615054003fb44150540005fb7050540005f87050540004fe7688540004fd7688540004fc76885400857e75885400057d7588540006ef6288540006ec6288540
  | 13 => 0x8f4003edc4058f4003e9c4058f40004ff7598740014fe7598740004fd7598740014fc7598740004ff739874000cfe7398740004fd739874000cfc73987400067f53987400067d539874003ebf4398740006bd4398740004fe7298740004fd729874003ef6719874003ef7419874003ef4419874003ebc4098740004ff7558740014fe7558740004fd7558740014fc7558740004ff735874000cfe7358740004fd735874000cfc73587400067f53587400067d535874003ebf4358740006bd4358740004ff7258740004fc725874003ef7715874003ef7415874003ef44158740004ff768874003cfe7688740004fd768874009d7e75887400057d75887400ce7e65887400067d65887400b6de6388740006dd6388740006ee6288740006ed6288740004ff7648740004fd764874003cfc76487400c67e65487400067d65487400bede6348740006dd6348740004ff760874003cfe7608740004fd76087400ae7e65087400067d650874003dbe7408740005bd74087400a6de6308740006dd6308740006f66108740006f56108740007e5210874008d7f765964008e7f76596400147f765964008f3e74596400073d74596400057f73596400057d73596400067f63596400067e63596400067d63596400067c63596400073f43596400073d43596403477b405964034778405964008e7f74596403467e74596400067d74596403467c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596403467f43596400063f43596400067e43596400067d43596400063d43596403467c43596400067f71596400067e71596400067d71596400067c71596403467f41596403467c41596400067f31596400067e31596400067d31596400067c315964008e7f70596403467e705964008e7d705964008e7c70596403467f405964008e7e40596403467c40596400067f30596400067e30596400067d30596400067c305964008d7e75d86400057d75d86400067e65d86400067d65d8640005ee72d8640005ed72d86400067e65986400067d6598640006f76198640004ff7598640014fe7598640004fd7598640014fc7598640004ff739864000cfe7398640004fd739864000cfc73986400067f53986400067d5398640006bf4398640006bd4398640004fe7298640004fd7298640006f63198640006f531986400067e65586400067d6558640004ff7558640014fe7558640004fd7558640014fc7558640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640006bf4358640006bd4358640004ff7258640004fc7258640006f63158640006f5315864008d7e75186400057d75186400067e65186400067d6518640006f561186400fe7e65906400067d6590640006f66190640006f
  | 14 => 0x34fe6534842134fe5534842134f65534842134fe4534842134fe7434842134fa7434842134fe6434842134fe5434842134fa5434842134fe44348421007e77048421007e67048421007e57048421007e47048421005e47048421357e75048421357e65048421357e55048421357e4504842134fe7304842134fe6304842134fe5304842134fe43048421007e521d8021007e52198021006fb6098021004ff7598021014fe7598021004fd7598021014fc759802103cfe7498021004fd7498021004ff739802100cfe7398021004fd739802100cfc73980210067f53980210067d5398021006bf4398021006bd4398021006fa5098021006f95098021006fa3098021006f930980210057f75580210ad7c7558021005bf7458021005bc7458021005df73580210a5dc7358021007e52158021004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff7458021006bf7458021004bf745802103cfc7458021006bc745802103cbc7458021004ff7358021006df7358021004df735802100cfe7358021004fd735802100cfc7358021006dc735802100cdc73580210067f53580210067d5358021006bf4358021006bd4358021006f63158021006f53158021006fa5058021006f95058021006fa3058021006f930580210ad7e75180210057d7518021005be7418021005bd74180210a5de7318021005dd7318021007e52118021006f9601802103e7f745974003e7e745974003e7d745974003e7c74597400067f73597400047f73597400067e73597400067d73597400047d73597400067c735974003e7f435974003e3f435974003e7e435974003e7d43597400063d435974003e7c43597400067f71597400067e71597400067d71597400067c715974003e7f415974003e7e415974003e7d415974003e7c41597400067f31597400067e31597400067d31597400067c315974009e7f705974009e7e70597400067d705974009e7c705974003e7f405974003e7e405974003e7d405974003e7c405974003e3c40597400067f30597400067e30597400067d30597400067c3059740006df7558f40006de7558f400065e7558f40006dd7558f400065d7558f40006dc7558f4003edf7458f4003ede7458f4003e9e7458f4003edd7458f400969d7458f4003edc7458f4003edf5458f4003ede5458f4003edd5458f4003edc5458f40006df7158f40006de7158f40006dd7158f40006dc7158f40006df5158f40006de5158f40006dd5158f40006dc5158f4003edf4158f4003ede4158f4003edd4158f4003edc4158f40096df7058f40096de7058f40006dd7058f40096dc7058f40006df5058f40006de5058f40006dd5058f40006dc5058f4003edf4058f4003ede4058f4003edd405
  | 15 => 0x564d04211b5f773d04213cdf573d04213bf7753d04213bf7553d04211b7b743d04213bfb543d04211b7e772d0421005f572d04211b7e472d04211d6f662d04213c7e652d04213c7e552d04211b7e742d04213bfe632d04213bfe532d0421005f670d0421004ff769042103cfd769042103ebe6490421006bd6490421005ee7290421005ed72904211b5f67190421004ff76504210057f75504210ad7c7550421005ef725042103cff7610421004fe7610421004fd761042103cfc76104210ad7e75104210057d751042103ebe6410421006bd64104210a5de7310421005dd7310421005ee7210421005ed7210421007b54110421005f576104211b6f57610421004f576104211b5f775104211b77675104213b5f575104211b77575104210057575104211b5f674104211b7b674104211b6f764104211b7b664104211b6f56410421007b564104211b5f773104211b7d673104213adf573104211b7d57310421005d5731042139f77531042139f7553104211b7b7431042139fb543104211b7e67210421005f572104211b7e57210421005e572104211d6f662104213a7e652104213a7e552104211b7e742104211b7e4421042139fe6321042139fe53210421005f670104210ad7e75884210057d7588421395f77588421387767588421395f575884210077575884210057575884211b5f674884211b5f47488421375f77388421375f5738842137f77538842137f75538842137fb7438842137fb5438842135df5728842135de5728842138ef66288421007e66288421387e65288421387e55288421007e74288421007e4428842137fe6328842137fe53288421005f67088421004ff7648421005f77648421006f77648421004f77648421365f77548421365f575484211b5f674484211b5f4744842135df7734842135df5734842134f77534842134f75534842134fb7434842134fb54348421375f7724842136ef66248421007e66248421357e75248421357e65248421357e55248421357e45248421007e74248421007e64248421007e54248421007e4424842134fe7324842134fe6324842134fe5324842134fe43248421005f47048421007e77648421005e77648421006e77648421367e77548421365e77548421357e67548421367e57548421365e57548421357e47548421357e76548421357e66548421357e56548421357e46548421007e77448421007e674484211b5e67448421007e57448421007e474484211b5e47448421007e76448421007e66448421007e56448421007e46448421357e75448421357e65448421357e55448421357e4544842135fe7734842135de7734842134fe6734842135fe5734842135de5734842134fe4734842134fe7634842134fe6634842134fe5634842134fe4634842134fe7534842134f675348421
  | 16 => 0x9121006bd43d9121004fe70d9121004fd70d9121006bf64991210057f75591210c57c7559121004ff75591210067f75591210047f7559121014fe7559121004fd7559121014fc75591210067c75591210147c7559121006bf7459121004ff735912100cfe7359121004fd735912100cfc73591210067f53591210067d5359121006bf4359121006bd4359121004ff7159121006f77159121004f77159121004ff7059121004fc7059121004fe76191210c57e75191210057d751912103ebe6419121006bd64191210bdde7319121005dd7319121004fe76d0521006bf64d052103ebc64d0521005ee72d0521005ed72d0521004fe769052103cff7650521004fd765052103cfc76505210057f75505210c57c7550521006bf645052103ebc6450521005ef7250521005ec7250521004fe76105210c57e75105210057d75105210bdde7310521005dd73105210c57e75885210057d75885213e76e75885210076d75885213e6ef65885213e6ed65885212b6ee64885212b6ec64885213deef63885213deed63885213df6f53885213df6d53885213dfaf43885213dfad4388521007e76188521004ff75d8121014fe75d8121004fd75d8121014fc75d812103cfe74d8121004fd74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006bf43d8121006bd43d8121006fb60981210057f75581210c57c7558121005bf7458121005bc7458121005df73581210bddc73581210c57e75181210057d7518121006f96018121004ff7518121014fe75181210067e75181210147e7518121004fd75181210067d75181210047d7518121014fc751812103cfe7418121004fd7418121004ff731812100cfe7318121004fd731812100cfc73181210067f53181210067d5318121006bf4318121006bd4318121006ee2118121004ff75d9021014fe75d9021004fd75d9021014fc75d9021004ff73d902100cfe73d9021004fd73d902100cfc73d90210067f53d90210067d53d9021006bf43d9021006bd43d9021004fe71d9021006f671d9021004fe70d9021004fd70d9021004fd7699021006bf649902103cff76590210057f75590210ad7c7559021004ff75590210067f75590210047f7559021014fe7559021004fd7559021014fc75590210067c75590210147c7559021006bf7459021006be5459021006bd5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021006bf4359021006bd4359021006f47159021004ff7059021004fc70590210ad7e75190210057d751902103ebe6419021006bd64190210a5de7319021005dd7319021005fa7019021005f97019021004fd76d0421005f576d04211b6f576d04211b5f775d04213d5f575d04211b6f764d04211b6f
  | 17 => 0x3ebe64d0a21006bd64d0a21005f671d0a21005f571d0a212b6ed76d0a212b5ef75d0a21435ed75d0a2142f6e65d0a210076d65d0a212b6ef64d0a212b7ae64d0a212b6ed64d0a21007ad64d0a212b5ef73d0a21425ed73d0a2141f6f53d0a2141f6d53d0a212b7af43d0a2141fad43d0a212b7e671d0a21005ed71d0a212b7e571d0a21005ee70d0a211fe7e6590a210067d6590a2103cff7650a210057f7550a210cd7c7550a211f67e6550a210067d6550a2103ebe6450a21006bd6450a21005f77150a21005f47150a210cd7e7510a210057d7510a211ee7e6510a210067d6510a210b5de7310a21005dd7310a21007ad4210a21005ed7610a212b6ed7610a212b5ef7510a212b76e7510a21415ed7510a212b76d7510a210056d7510a2140f6e6510a210076d6510a212b7ae7410a212b6ef6410a212b6ed6410a212b5ef7310a212b7ce7310a21405ed7310a212b7cd7310a21005cd7310a213ff6f5310a213ff6d5310a212b7af4310a213ffad4310a21005ed7110a21005ee7010a2110e7e65d06210067d65d062103cfd76906210fe7e65906210067d659062103ebe6490621006bd6490621005ee7290621005ed72906210057f75506210cd7c75506210f67e65506210067d6550621005ef7250621005ec72506210cd7e75106210057d75106210de7e65106210067d651062103ebe6410621006bd64106210b5de7310621005dd7310621005ee7210621005ed72106211e67e65c86210067d65c8621005f576c8621006f576c86213f77675c86210077575c86213f6f765c86213f77665c86213f6f565c86210077565c86210067565c86211d6f664c86211d6f464c86213eef763c86213eef563c86213ef7753c86213ef7553c86213efb743c86213efb543c86210cd7e75d82210057d75d82210067e65d82210067d65d8221005be74d8221005bd74d82210b5de73d8221005dd73d82210067e65982210067d6598221006fb6098221004ff7598221014fe7598221004fd7598221014fc759822103cfe7498221004fd7498221004ff739822100cfe7398221004fd739822100cfc73982210067f53982210067d5398221006bf4398221006bd4398221006f721982210067e65582210067d6558221004ff7558221014fe7558221004fd7558221014fc7558221004ff745822103cfc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d5358221006bf4358221006bd4358221006ee3258221006ed32582210cd7e75182210057d75182210067e65182210067d6518221006f9601822103cfe76d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121006bf54d9121006bc54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d9121006bf43d
  | 18 => 0xc755044103f3e655044103f3d6550441455bf7350441455bd735044103ebf635044103f9e635044143ebd635044103f9d63504410069d635044143f3f535044143f3d5350441007af7250441007ac725044103dbf715044103fb7715044144ebe615044103fb66150441447b65150441447b5515044143fb7315044143fb43150441005bc7050441004ff7598041014fe7598041004fd7598041014fc7598041004ff739804100cfe7398041004fd739804100cfc73980410067f53980410067d539804103ebf4398041006bd4398041004fe7298041004fd729804103efa709804103efb409804103ef84098041004ff7558041014fe7558041004fd7558041014fc7558041004ff735804100cfe7358041004fd735804100cfc73580410067f53580410067d535804103ebf4358041006bd4358041004ff7258041004fc725804103efb705804103efb405804103ebc405804103ef840580410cd7f76596210ce7f76596210147f76596210057f73596210057d73596210067f63596210067e63596210067d63596210067c63596210073f43596210073d43596210cf6e72596210076d72596210076e32596210076d32596210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210063f43596210067e43596210067d43596210063d43596210067c43596210ce7f72596210ce7e72596210067d72596210ce7c72596210067f32596210067e32596210067d32596210067c32596210ce7f71596210067e71596210ce7d71596210ce7c71596210067f31596210067e31596210067d31596210067c31596210ce7e21596210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c30596210cd7e75d92210057d75d92210067e65d92210067d65d9221004ff75d9221014fe75d92210067e75d92210147e75d9221004fd75d92210067d75d92210047d75d9221014fc75d9221004ff73d922100cfe73d9221004fd73d922100cfc73d92210067f53d92210067d53d9221006bf43d9221006bd43d9221006ed72d9221006f671d9221004fe70d9221004fd70d9221004fd76992210067e65992210067d6599221006bf649922103cff76592210067e65592210067d6559221004ff7559221014fe7559221004fd7559221014fc7559221006bf7459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d5359221006bf4359221006bd4359221006ef7259221004ff7059221004fc70592210cd7e75192210057d75192210067e65192210067d651922103ebe6419221006bd64192210b5de7319221005dd73192212067e65d0a210067d65d0a21
  | 19 => 0x8141006ec62581410067f65181410067c6518141006ef6218141006ec6218141006f96018141004ff7518141014fe7518141004fd7518141014fc7518141004ff731814100cfe7318141004fd731814100cfc73181410067f53181410067d5318141006bf4318141006bd4318141004fe7218141004fd7218141006be4118141006fb3018141006f8301814103e7f745944103e7e745944103e7d745944103e7c74594410067f73594410047f73594410067e73594410067d73594410047d73594410067c735944103e7f435944103e3f435944103e7e435944103e7d43594410063d435944103e7c43594410067f72594410067e72594410067d72594410067c725944103e7f425944103e7e425944103e7d425944103e7c42594410067f32594410067e32594410067d32594410067c32594410de7f71594410067e71594410de7d71594410de7c715944103e7f415944103e7e415944103e7d415944103e7c41594410067f31594410067e31594410067d31594410067c31594410067f70594410067e70594410067d70594410067c705944103e7f405944103e7e405944103e7d405944103e7c405944103e3c40594410067f30594410067e30594410067d30594410067c3059441006df7558c41006de7558c410065e7558c41006dd7558c410065d7558c41006dc7558c4103edf7458c4103ede7458c4103e9e7458c4103edd7458c410d69d7458c4103edc7458c4103edf5458c4103ede5458c4103edd5458c4103edc5458c41006df7258c41006de7258c41006dd7258c41006dc7258c41006df5258c41006de5258c41006dd5258c41006dc5258c4103edf4258c4103ede4258c4103edd4258c4103edc4258c410d6df7158c41006de7158c410d6dd7158c410d6dc7158c41006df5158c41006de5158c41006dd5158c41006dc5158c4103edf4158c4103e9f4158c4103ede4158c4103edd4158c4103edc4158c41006df7058c41006de7058c41006dd7058c41006dc7058c41006df5058c41006de5058c41006dd5058c41006dc5058c4103edf4058c4103ede4058c4103edd4058c4103edc4058c4103e9c4058c41004ff7598841014fe7598841004fd7598841014fc7598841004ff739884100cfe7398841004fd739884100cfc73988410067f53988410067d539884103ebf4398841006bd439884103eee729884103eef429884103eec4298841004fe7098841004fd709884103ebc4098841004ff7558841014fe7558841004fd7558841014fc7558841004ff735884100cfe7358841004fd735884100cfc73588410067f53588410067d535884103ebf4358841006bd435884103eef725884103eef425884103eec4258841006f47158841004ff7058841004fc705884103dbf7650441006bf7650441004bf76504410073f75504414473
  | 20 => 0x67f65589410067c65589410067f65189410067c6518941006ed6218941004ff7518941014fe7518941004fd7518941014fc7518941004ff731894100cfe7318941004fd731894100cfc73189410067f53189410067d5318941006bf4318941006bd4318941006ef5218941006ee5218941006ed5218941006ec5218941006ef3218941006ee3218941006ed3218941006ec32189411b6f741189411b6f44118941004fe7018941004fd7018941005ee7618941006ee7618941006ef65189410076f65189410066f6518941006ee6518941006ed6518941006ec65189410076c65189410066c6518941006ef6318941006ee6318941006ed6318941006ec63189410076f53189410076d5318941007af4318941007ad43189411b7e741189411b7e44118941006ef7518941006ee7518941006ed7518941006ec7518941006ef74189411b6ee7418941006ef54189411b6ee5418941006ed54189411b6ec5418941006ef7318941006ee7318941006ed7318941006ec7318941006ef53189410066f5318941006ee5318941006ed53189410066d5318941006ec53189411b6ef4318941006af4318941006ee4318941006ed4318941006ad43189411b6ec43189411b6ef7118941006ef5118941006ee5118941006ed5118941006ec51189411b6ef41189411b6e74118941006ed41189411b6ec41189411b6e44118941006ef3118941006ee3118941006ed3118941006ec3118941006ef7018941006ee7018941006ed7018941006ec7018941006ef5018941006ee5018941006ed5018941006ec50189411b6ef40189411b6ec4018941006ef3018941006ee3018941006ed3018941006ec30189410067f65909411fe7c6590941006ef6290941006ec6290941005f67190941005f5719094103fb441909410067f65509411f67c6550941005f77150941005f471509410067f65905410fe7c6590541006ef6290541006ec629054103df6719054103ef761905410073f65905414673c659054144dbf739054144dbd739054145ebf639054145ebd639054145f3f539054145f3d5390541007af6290541007ac629054103dbe719054103ebf619054103fb761905410067f65d81410067c65d8141006ef62d8141006ec62d8141004ff75d8141014fe75d8141004fd75d8141014fc75d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d8141006bf43d8141006bd43d8141004fe72d8141004fd72d8141006fb30d8141006f830d81410f57e75981410057d75981410067f65981410067c6598141005ee7298141005ed7298141006ef6298141006ec6298141006fb60981410057f75581410f57c75581410067f65581410067c6558141005df73581410eddc7358141005ef7258141005ec7258141006ef625
  | 21 => 0xc73582410067f53582410067d5358241006bf4358241006bd4358241004ff7258241004fc72582410fd7e75182410057d7518241006f960182410f57e76d95410f67e76d95410147e76d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95410073f43d95410073d43d954146f7741d954146f7441d95410067f74d954146e7e74d95410f67d74d954146e7c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d954146e7f43d95410063f43d95410067e43d95410067d43d95410063d43d954146e7c43d95410067f72d95410067e72d95410067d72d95410067c72d954146e7f42d954146e7c42d95410067f32d95410067e32d95410067d32d95410067c32d954146e7f71d95410f67e71d95410f67d71d95410f67c71d954146e7f41d95410f67d41d954146e7c41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f70d95410067e70d95410067d70d95410067c70d954146e7f40d954146e7c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f65d89410067c65d8941004ff75d8941014fe75d8941004fd75d8941014fc75d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d8941006bf43d8941006bd43d8941006ef52d8941006ee52d8941006ed52d8941006ec52d8941006ef32d8941006ee32d8941006ed32d8941006ec32d8941004fe70d8941004fd70d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ed65d8941006ec65d89410076c65d89410066c65d8941006ef63d8941006ee63d8941006ed63d8941006ec63d89410076f53d89410076d53d8941007af43d8941007ad43d89412b7e741d89412b7e441d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941006ef74d89412b6ee74d8941006ef54d89412b6ee54d8941006ed54d89412b6ec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d89410066f53d8941006ee53d8941006ed53d89410066d53d8941006ec53d89412b6ef43d8941006af43d8941006ee43d8941006ed43d8941006ad43d89412b6ec43d89412b6ef71d8941006ed71d8941006ef51d8941006ee51d8941006ed51d8941006ec51d89412b6ef41d89412b6ec41d8941006ef31d8941006ee31d8941006ed31d8941006ec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef50d8941006ee50d8941006ed50d8941006ec50d89412b6ef40d89412b6ec40d8941006ef30d8941006ee30d8941006ed30d8941006ec30d89410f57e75989410057d75989410067f65989410067c6598941006ef62989410057f75589410f57c7558941
  | 22 => 0x8b41014fc7598b41004ff7398b4100cfe7398b41004fd7398b4100cfc7398b410067f5398b410067d5398b4103ebf4398b41006bd4398b4103eee7298b41006ee5298b41006ed5298b4103eef4298b4103eec4298b41006ee3298b41006ed3298b41004fe7098b41004fd7098b41004ff7558b410067f7558b410047f7558b41014fe7558b41004fd7558b41014fc7558b410067c7558b410147c7558b41004ff7358b4100cfe7358b41004fd7358b4100cfc7358b410067f5358b410067d5358b4103ebf4358b41006bd4358b4103eef7258b41006ee5258b41006ed5258b4103eef4258b4103eec4258b41006ee3258b41006ed3258b41004ff7058b41004fc7058b41004ff7598341014fe75983410067e75983410147e7598341004fd75983410067d75983410047d7598341014fc7598341004ff739834100cfe7398341004fd739834100cfc73983410067f53983410067d539834103ebf4398341006bd4398341004fe7298341004fd729834103ebc419834103efa709834103efb409834103ef84098341004ff7558341014fe7558341004fd7558341014fc7558341004ff735834100cfe7358341004fd735834100cfc73583410067f53583410067d535834103ebf4358341006bd4358341004ff7258341004fc725834103efb705834103efb405834103ef840583410fd7e75d8a410057d75d8a410fd7e7598a410057d7598a41006ef6298a41004ff7598a41014fe7598a410067e7598a410147e7598a41004fd7598a410067d7598a410047d7598a41014fc7598a41004ff7398a4100cfe7398a41004fd7398a4100cfc7398a410067f5398a410067d5398a41006bf4398a41006bd4398a411d6f74198a411d6f44198a41004fe7098a41004fd7098a41004ff7558a41014fe7558a41004fd7558a41014fc7558a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a41006bf4358a41006bd4358a41004ff7058a41004fc7058a41006ed6218a41005f67190a41005f57190a41005bd76d064103ebd76d064103dbf73d0641485bd73d064147ebf63d064147ebd63d064147f3f53d064147f3d53d064103fb661d0641477b651d0641477b551d0641005be70d0641006fb6098241004ff7598241014fe7598241004fd7598241014fc7598241004ff739824100cfe7398241004fd739824100cfc73982410067f53982410067d5398241006bf4398241006bd4398241004fe7298241004fd72982410057f75582410fd7c7558241005df73582410e5dc7358241004ff75582410067f75582410047f7558241014fe7558241004fd7558241014fc75582410067c75582410147c7558241004ff7358241006df7358241004df735824100cfe7358241004fd735824100cfc7358241006dc735824100cd
  | 23 => 0xc000801800002b000801c02e003002803400000800080000040010000014000038001000400002d0000000000025000000400000c001800c000007001000000c01000280000060000008000000007003000000a00a000000000000900280000000010020000000002001000002200200000000020040080000004009000000800c02700000080060000010000004000000800800e000000800000000600000000000000000008000000000800800400d000004400200c0080000014009000000800c0060008008000002000000c00600000080000320020048044000006000000001c00e0000020000005000000400000200000080060000078000000002006800400800000000000140010000004008000000000000c006000800000400000700000040020000008000001001800800401e007801003a00300380100000000018004004000010000800000000680100040040008000008005000002801a007000802000201a0020008000000000000001a00100300040140020020004040001001000c0060000088000002002003802c004011001800c002001001000000a000001004c00600600700280260030018004000000002800001a0040030000018009000000c00c004000001400000100e80000020090030008000006003801400400000400000060000070008004001003800001600100080280040040010004006007000000c004000006000c0040010010004002000000003800e004000003401001a0000020006000015000c00200501600180080050028000002000000003c00000100200080060120020014004005000803400000200280000000180000000004001001000800001500000440000020040000044000007000400201e00280000040000000004000006003800c00e0010008004002004001000000e000010800c00c0000000000010000007000002200d005000403400b000010400e0080000010000006000000000200000000040020020058008000005010000400000000e000400200200480040040040030000004009004800000000e0020000006001000001c00200b00000000080050048010008000000000000000300080040000030000000002009001800000e00300280400000020018008004000000000000a00b004006c00e003001800c004000001800000e0000080000002001002801000a00c000002407e01200000040180070000008014001002000c00a00100d800800800800000180140000000050006002000000800800a001000804200300e001800000e008000402e0060018000002005000802c00a00200280040060020008000002000002800c00a03b000001800a01000080240000050000008012002000000000200000100100000080008074000002004ff7598b41014fe7598b41004fd759
  | 24 => 0x2000000100000300060030048028008001001000001000600000200040000098008000005003001800000000380080000010000018000001002000800c005000800400a000001006400400b000000000000e0000014002009001800c01200f0018080000009001000c000023001000000200700a8038002003001800000000000100180200030010000000002000800000a00b001000c004004000000c000005005000400200000000000060000028008014004002001400c0060000000000006006000800800000a801c002000000000c000001009800000000300a800001a001000000400600100200000000030008010004003000000c00402500480180120010068008002000000001400c01300000080040010000000012019006005c000007000001c006000000003c01e00300000400040040000024014006000800000000b001001001800100180640020060040004000000000000000200100080000000030018010002005008000c002009000800400600100000580000100008008000000003000400c001000000800200300100000020010060018000009000000000c0000038000006009001000800200700000000000000018000004000006801c0000000098004002001000001c00c0050000008002006000001800000200000040020000038014006000000002c002000000000401c00100080000000020010000004002001006801c001004000c000002000000400400100080000000080000000004002001000800e004008800000600200080280120000008028008000001801000800a00280040020020058048000004000000c00200600a800400601100d800000e00200400300040070008000002000000000c000007000001c00200b000000c00800500f800c0000040008014020002000000c004001007000000200d000001c000013000000c0020000008034000003001800400002500000040000010030028000000000000800400700080080000000028000010013005801c002008004000c02c002002804c000003000000c002002001000c00e0000018004000003000006c00a00300380040000030048014006006008001c00c001005804001800a00180a0000003000800000c00000300200040000000004004001005001000400900380040880030000000006000002800800a000002000001c001000001000000000180340180090068030000002000801000a002001000800200b000000803c0020008000004001000001401a0000000000000002001800000600a001000400000b001000c000003002800800c00000080000000090040004002002000000001400100200000000010030010002000002002c002007002002c064001000001400600100100100040000028004000000000000000e007000000002c00
  | 25 => 0xe4000038ec8ea7c104c00000000000000000a0aeb000013c179aeba14e80f830e000000000000000000004a97668ee4bd8790e466910382600e248e13410000000e5f0002b85ada0000002b90e1c3ad2a08fe023a99c12e0efd31e623f3b33c066486125d9885a8e08f18410b1e3869f2380a4f16ed0236530cdba4b3020922184f627800005001da9835b628e45634c6039a3347007b93d393e41de8d83281cc01a40386c300d99e2d95800093c3cc000721b680000e850000000000e5448c80018387441fd13e93eec2a5d6000142e0002d2a6d866cecc5f062000000940002955a28f03738107d8048d079fb6ad7cd63f6452a19c785681730001d3c25908cf080658db00e62eacbdd1b8652aa04f9a50a0000001b7e0f9000000108810945da754792504275b028000e514b711087286836290000000bdc000000000001f000109c0000002d58bdb2400004d2a5244b61bd02cc5100000003a5b1c4d7a6d317b000117040b77293780008d429117988eeb322fea9883da968bc0346c0001740002034000ca800022a9b6282c2979178000be5b290b2c000b1f19c84f54d02a6800365438e7df476e8d11f693b7442b9c54e909000279c7440004fd3560620d9e22800016c80006d9ba08000d745c32e98f7664500000953da601b79b6b91e0324272b981ad60003796f28fe085839d1934000de55fc80001b9bfc4ea1d5db225f79092bf9078731315cbe4de8a74d169764f3aa373338010c76b6a437128de3437e6a995495800b5f0b840961278ce0ea8f94d42cd18f902409683822680000008243cb974a50ed08453b36c0446444f09c24f7c4b00a0b2497b200000000017209d760a82fc000a63f3137c9a7aa66f6aaf8cc62e8a00034b8b1e00000032c60009a12eb0c0c45444f0000000000e370000e64000000644000174e00022a009069ece000000000000000000a8c00085a0000aa8000e27000309daba60104f8001588c8d0000000000969b331fcc00059f0000000898312c68b5b1cda002008000000000200000000030000030000001001801c006000001000000c000001001800e00200e000000e0050028008006000004003c00e000001001c000001000000002e004002800800a00b001800000400300280280000050018000000003007002c0120090018008012000001002c016000000800400a000006800801c0070018008002009003801400c000000001000000100b8050018000000000c00e0000038014014007000004400000200f000c004004000800c0000050000000002016000000401a007001800c000008001001c0080010008000000004000804001400000080140000080000000000000007800000c0090018038012005000000c00401e00600200000020000008002003002800000200000080
  | 26 => 0xbfa414e400000001a480000095bd8001d0600000001880009812443be932691d0000f98000a46589034cc5c0007860000000000714b519a1212d1561b780000002f611c400061b2bb8001374e42250b1180000001c88000000000317b99c85c9eb0003ba00000005501464284e5e4248eb184467e0000c882768963a38661bc65ef31a30f8000aac0000239c6a31cb16d6e20c20007208001d0c6af17f05b001abcf000380c000000154906c00069c5cba7e00003375d7b3d9ade0000000080ece000000256d186bbd5318a840005325112d280003a6000137000000000000000000000000000388000421911800000000000000000000002631b8486648323ba1be96015599456926a35be0000ba8e3900026ed43400a17da3d98a65dfe7a95c485200035980006ba3e0598445a93400016c00018c62bb0000000000ece4868000324c0862183261640000ffae345fa75024a140ca3c000733000000000056d28cc000b512f2ba3801837c4f500008b0801990aaee0000cce2f800027e33a3dd02da0bf8950000000f86e8966729140006c7331ac40064000000000000032620e3b2492a62401fb33c0009fb33d9fd13ded89000072953a0b70003ab80b854b3f24001e92aa08000000000b175518bae000c5a6bf80000ec0003d53bcc00000000027940000000000869d7e1ea21d175c0000000002e94fb6ca044600018ac6a00002f064c2b616e9a58d66ca4fd20073405e352377af2c0000000000000b060006bb0001bf60001702d7879a0004039ae9c66b3be6e1e18000b745e8a95000020000034bd8ba8dc38a15bc1faf467378ef12362c945093d97c423000000c477200000000019586583cd119d248ec419516409981c223d91c9410ef40440f90b00d174c543940c53420910df505e00021130514b0d841512ffdccaf0d0003231e26b114d1218064099b2dc02742ab9e95ff02e8e70b5a3422bec3ec6c664d89a8000df800011580000ae0e7b8141290007a1000000093a18da3a114a7e1000000186092f356b7611f800048223b5172e3056c000000001651a4000000acb16301d6000d5709091f00003b336f80000006e310227f4000bb60002e7424311a306b7380feb0801eaa557b960f63fac8b5aeaf03021ff42d429a4024688d12dea36095f971c593036831da64858b058ab867800016419b4000164347a68c47000030300000001dc34f070c30a6682be80008c466f5e4a71cd7256d05f1ff07dc00059ed5807bc00000000012c1857e93ace1e4cf2f6383745d680000000bbccf2f3229d1a5000000000000000006a60000cd1b4c1b318000448b4af640a2e3d016b812d980000000000000000a8a993de80af54f4831303e7016639023d28000dac7de56c8fdd24b4073d100013135e0d7515d80008c2000000000000000000000
  | 27 => 0xabd4d3862c0000f467e93140009c352229b8000cc403006bdd3400036d31809ce0002b192f9ca65f50a501759a494c053a63bde451d518babc00027e9bd22cdd8e51b3f6b2440000020002d080000001200000000000000000000000043eba5400000000011fc78a284034277c84cebc00a9b20fed00000000012886000000000000bce29e80000000000000000000a742a30000962000355000057015a487a4a1cf83a81958421454b690000001350c3b1bb800082800017bacfc2d0703a4ba74834a0000000b38000c9c3d8a03c300000031c0000000000000001bd0000000384cc7402b38b1f3877651f1ed079cfea869ebc3151b8c2431f11c900020001310000ba600000010dc000000000127154e84e3ec000109e21777e800000000023280016c67d90a402455320fc6d29761ae4e6463402af1dfb17a8aaf058f87789e32324de200000000013c4000051ae90000a191e5b4a8ee4619263ad21006bf46da03e89d20e80003c08000d6300000000000000000435e442d000000000000001eeb7680000000001741a9a71b0ca821d0201ac00000001c55402718214444cc3000000000002c137195de8ee7158cb0e9e2829f1b692800000a505cb8089cc0001fe0a2128a5f67080cb877b5360000000c113e10003500e520003d31f3c0003a76532c940a8792000000000065a62b8dc9a168980c60000000000450127c4ca5794bc12599b294b08c80000f60d5000000000098e00000018e8ea570c800100c000641b584d770000000a700001695e034c07cef210001f251940b880015773f88046f3a4946768516570000b220000418001156d8e0000000fca00000032900000003bb16384eb6368002fa80000000003394000000000000000000014f166cbeee925be82f521800037580017d3000000000169c4b7621206db1429335e1cfd0b28c01a2a83091c0a600bafe87a40da79385d5cc24164578c43c92000525800000000000000012c70000001181a7000061f9dad9de0004973398000130c44a5d40000000000000632598447bcd9a14d4e5f8b4e983ec39083e4888965782621753c3418f2cd26493480001b3b829503995292b35cf0b068de050752c90000000000000da3699800000000060d8a460001c9374400000085276b965114c1242fc223400006f000000047ba731274000f686802bd8914000ce83ac809c0006dc795800000012fd788001b88000620a9990529268b8b8a9bc0a7671b02a95c000000000002b0520000000000000052b400000000000032680000006668378b4000000000000000000000000000a7b4ed91b03565cd2889830b863123d6874124613811e75e556027f0002b92000c245d1a3680009d16f98000000b23253000000078d000010c0006ee68b1f00fe422400000000003c0a0a89e40320002
  | 28 => 0xb2e1a314581ef001a2380000000002ae947a98600000010d08656090000da2000208384580800000000007fa00000000014f855700000009524081330001658cd60221cf4000e2f43f0000c96bd2290a9480000005a31b84bfeb2d0002a30c2008c429a0649febdb00a3c41b5aa8542f32752204190ff256531248c0002ac56f400000016a8c0e7ae000370d4e400059e1678000000703179000019400019c000000001b8000000ea30000894000b500001690000000000083800000060839ac7f6bdd11abb5800097c00014d4bba0000003c800000000000000000d15036e5900008b20002b7070a0006261a1800090e0000001e905c66832718f372ea3671d300003df26c0859de0ec3251015ce640000da01e8b74a1f31c5a548d400000001e09f815b0002c780002580b115a80008ec8878000000d970001c28cea0001712009b0e2f8b43b9705ca9295cc00012ca8761f9297000000040d10a9b9053e0000001b6a09e0002931146962800225c000c6c575a55db8078f00000016028f90d2c0017545515ce2af91ac30d00019c400081e25b0a09656bde0000ed000000074800000006c1c3b800149c34730915900000b2d07000000000007085180006ec3bc8b040000004b383604a80000db35053c67eb44f8000000a500000000000000000282ce660000003184000000000189a00000000002c400030432a215c5b2c9700007898dc00063680006acc442dd8fd8ed8bc56c918800005df54c1fe4d6a00f08a19b8000b40000000087ab0f0ae000060c38b0002f30000d2432a8000000ac70900000000add00005cc7468da800000088858935b00d07ac06c51faaa1db64d20001c5c4d802600000000f8d376ce8001a1e0000002b89266000000000000000030b006cd76b066aa2c08d02d94ea509a51de0004790000982eee4dc80008268e61b280014a200014ddea5ac06be0503ba9c9c00000013908dcdf94df00010560c000000000000000002f4200000011fc000000c1e64100000004300000f8c0009963042d340006e900003edd445b628b822d49ed4900000004ac0bbd5e17c49fcf170000000000000000204583400008635c4520b4f104a6286b00000af80000008b10001f2810c0000000000ed20000002c14ec60000000398ac2f3c00000013630000001cd0000d180000000000b9200008ec000bfd6d5160428ec400f400015de67c66625c000036003aba50fde6f56590000000ded2e780000009a600000014ac95d3e92a660000006148190ea4eef0003aa5cdc00000022b3c9000000010e0072484717090705c46b472232dc8e40e7251713aca4980cdacf9822d3f21916b80009298003ae1696f012aea66400000000024981fcbfb35ed3d57325305fc032d27a2f24e63880e2a000032789086c00028b26140000000721d74
  | 29 => 0x4000240c58000158ae52686000154200025e18a17351e00000000000d7b2bd00005cb0002ae4b840008e99b198882ce3f469b13689da0002b6068c000000557000000014c5ed1f21a964470000ee9c7a31643a8265e9e5d0800000000000011889280a9f233cc80000006b3a4519e1af48c137d11ccf5eac331a8f28f17efc1ae060d1581a730e1fe8d8800000015201b80000003cf800000002c5c69d8ccec00011900004923b40000f5074e27528740000c100000003ca0cf00008185cd188033a4c59e60000700000b98a77ad880000001b50001dd53660000f9a38d6c02a8038e208eb66b12ac8fb56b26382009c20b9c3893cf191e5d60a26d91ca15721136f8a2d16524ee42e05345c88c546dabcc000000000000087e513222ade4fa07a04e9a7c00003c8355a5e401cb0e4310444904f067021b6ddd62fa313828e000db619387f400000551093242f41343bfb8f8dee239439c604f48f2c55682b4038ec5019bc4800032d0c8b6a00005733a4372c000f535f80000a88e730f58dc5c1cbf600000000b6d261479ca8bd6a2cbc28000000be9000152856610b800000075c2f000033a40008d90001e20be40006ff1a296000d000019582068bf43558c021400056f8e390c66e2318ef4cbe1e8d39d8e199423d1319b2e9dee0000000000000f0b51326d02c2e1b71587213e400035faeb8000b1827600008860000000c3c00065b72e80000006b44620000000000000000180600000000017bd00062f0000000d670eb000000000004ab20074a0000000bd3774db905173e800045727000b91a40c32202c92fc8d9f0003870baf20c2e6c00003ad9647840007360002659b9c9204210001d59cea86c5dc9d2561a60ae3d0000000e6838303513d883a55a0001b1d97e517cb68000e0c6f78000000000191950856c00032f80000b2ade35e67cd0d62c402780000f2d501b9b2ccde7f540003ad800038c50a3b662a88f2a97050d32e1b211326bd08c8be70f000000000000000000009ce00030b400000000000000005864ffaefc00000000000014b4000000093600033e00021e539e0000cc965d1870003391f4cea60001c9c3cc000934000000079e02141c821000000000000002fe0000000b0d13252b3098000e00e5a0631ffc00000000000011050005aba42cbb15ef83f000186c7dc10a9d340006960dd0598ff0f5773633140003a40000000000000000000187a00027880000007073a10dac1e27746a137c0b7897d1338001dc2af22578000000f1816ea40c00000000002460000000002ee067a6e04ff004cf6ae990aebaac12b00036480010b3000546a66822e0001192e2597c869116bb44764bf7000000000073c00012780009874ca7a6096a4ac6698624ae08f18bb91f580a58479434b5cfc2644153388e72c587460b9d6066c7
  | 30 => 0x33100014de2b700000000004e262c96554fe38f34580000002ba0002aae00000000300010e89a00000000000a942c699940003a900000a80002af1099094000000050ab05c987e8347350c2f2096ca18000000ba03d82388fc604a00000000000003ff00000005c8551000168ac5c523a2f10101fb0002f191145a96fe327cf1cf160ec1efc9a043e60596310f049d0000ad5a983ea02d0000000b2a5920000605ecf58dae5047dc37143c18232c39a00008ad74296d39787d000000011d400104e1a96cd99a80a69d91e0d0081ce2190498ae5a525753b20d6d0a86474c8c001850d3131f7a707de78a18d1b2eede8688000000000c4800000001c48002c900016f036c78382040005ac06e9ab05be0973613b4ca300000038000be50db349b6dd4ca7413f51778d3400000024280008ec58580008340002dcb804c143b60000000000d4400008bc4287b2000142c000aed764000197800049e00000000000002e1cc5d93f65380000009cb55c018c3aa000000000000000029c00003be99416e1b0106acaf0001be14260003f70f54260dfa1f9962cdcd00010c2be00000000000000cc054f5d6a7581ab2de75097c07b80cd11e8f4d9c23b157a08b0000ca235c075ca24dee46400000007653bc00002384c25ca8001b34bd8000012a9320001f48001a684a8000186821b7100001e58000a352aa800000000032c800030867d2f680000000002468001ac821c29b88b876a1bf7a8b6e9bbe0000000001970a9f37b40000007956d080000a06a561c1ad70406e7cd5000000088800008dc18a4b948d363041029b00000012a65b200000005e871c4670001841000543e4c87241b900000000005f40000001a3c0002e1fd048089620001eac0006fc44980000000005cd0b54000cca0000bb8000097d30000018417000026fcf960005770000000b0a33093bd9f8e3f5482558d915c256b0d11618bbe11a15409acb220892b451d5cbb1d7ab31db22733bda62f878da75440001322000000245507c0000f700016794b80000000000edd00036140000000000a3432e000000000000000068d3a7d3562e910f8000000236463a6e09681a65a980013049210000af0000d9900000019329bd0c700000006d40001d140000d1000000186a64273f800000038800000000000000003605352a18517ba1c00024c1768c4c0000005c200013f20001fdd24536a11819c00000008670002c9c000369390acdc0006b700034b00002d71ce0000000a9b0002a097d8e440c115980008e75181e5176291e3260de4fef8bd31f38008c6b16600847c7f200066100003a8dbc75bb3508d02985ad8000bd244155913e0000f1e520ae0926000004e262c03c21b00000000005b0000000000078349c21cc3e00000000000e946d00000001e623fe000157c000350576347
  | 31 => 0xf9954c64436c419a080ce0000200000cc1131b2d03a26a16ea23dc0b500070c0afc99c9c94b08b8e0000002a19cb400000043500000000001ad3955556a6b0000000000000165000000000000000019a2000000222c000c16000000078e4d776680001ae891982a2bee020005978001ad400000000000000000000001b2600000000005ea0000000f08442f504c8375d4240000002c6800077c00000012feb7213a94a1bd8a499581f75d2eea7378281c2faaa900000000006374d8a93764d06e3f48001e229083429ba8b8ab66280800000000000010d40000000f0a9d60000006e8000175294f30f0e80000dcc00000013dc20a1fa8000000325157c00000000010f000070400000022e80d234d0365c1200096f000000174b0000000000000de90002e898302f80000000ab80003a32a90faaa6c00022920000000000000c0b0000000000000e781809bb475484b0001918000d0761188801c689c2ad280066080c3538225e0033f0000a4503e000000100d08206b0391b91e6a00000000000000001e1b44c0006cb000000090e1c61ba00000000000000000eb05da08bd49c0000007280001d62000719000040e0000003784074ea46ad20dd65ca8b2b10000000d9800000000005534630c610fe1783628bcc66200020684380003e800020a104a30700028b9cd484a6fb254408cb9e00028ec9f600000024488aa3640000000deb0005f089e800068800004542fc6d83791f59b527ac4c6dbf485e25d6be14b4f3e954364cccc000aa5327000049c1f80d519a45e37352e00f397c0e464ed2fa140c7030b917cd9ce15618a80004820000001bf800089163580000004fd496000089445c2d38e54000357000141c0000000002705adc7512df98e68c20000000000c300005fe40012e6cfe66f1c3c010cb100000002961766c84c5d592000000000146cb263828e046dfa3a6dd94416daf1d0002678c86cea26a0259a8a47931b00006be45d0000d39b1e887056235d5a400018f334095c0000002f1d51c27d000000000030a0003ccc00070200002cc9a2ee96e2a86d51448300031a8baa0000224001a00e4f5c5ac5ba5663d78280016ce3c10000001ac400000006f00000000000001bb250d00000019167621288000000180cb34000000a2300000015fa0000002e5956e3903b3117c0008f300025090460000000001b040002be2b5fbe800073b8000f18bd880000000001556c5a1080004df0000001e480003ea3a3c3b2eb55ae8f002a2611228a528000cd86001cb813402875517f86943eb5eb888c0008903787155db0efb00000008920000002a3d3b000059085255d0bf6cbb0e359dcc9628e11f83e2eb30d40564d309466271c0269813c63900003c673e0000ffc00000000010615a6f3b5252a1c00089b5bf80000000003468001e6800
  | 32 => 0xf80002ca0000789000000000000048b8001b7a00076d0a48000ee336e9438ba4699400bae53eadd674ea2b84e0c650cfa120cba6ae3e2bbd41e45e054b538555553360c926d95252472c18392007b667ca6756aa5b70003215ea41f51450684c901dd316817913c5e75b88c31996a8095880000000000002c75baa8164ee18c80007b33f30144502a27a862a5649a09bc200d540005c10527b7c0000005b79c356fc0000000000076f1f00012909742532f097a0b449662b718c3788f2557e30c51d200009b88149e688429317da0e20002f6e96cab6c0d1b78c2448840f1edbb712a4b3d7820000a920001521e840009715a189f12389410002378000d2500026b019416b000301c00026b0000c44b684a50000940e6e2952c53b000000002598000000d12000107800000000037880000000003278000000185800000000059a800000000000000000005c97a53564500000000000000064934bb2b4000ebb00000010b6990e4c00000006a20000000000c7340bab5533013a12931890da00000000001680004092e9b62897a0002e141d84a70520000000a110001ee0bc400000030ac4160000001f1c00000000011d86cc00047e80000004ca057a1f0104c2c30e9218000242216b0396e69e62d335f9972f0f000278124f5dc57a903048e8ad3c82054cc800048880000000000000a154380003fb0ab4000d901ec979ef84bdf6b43d5474238771a2561d503b05c6311ca12a5753fe3746a6be45f3bb05b8e8836470f40726dc10003885626ef90003848c72000023a174380d523af90812c392b5642f080002cc6ffb8b0000a1636c94c40002ff22433fc0200002df35d4000000000000024764f4ba09f8da50000000000000d39348000000000000000000000000003125044bd78001bfc2025ad21400002a00000a780015278506d200000000001b0a4bf50600000000014da89a2e59b98000092000280c000f4540e833a0007730000000c0600002de5ae0009c24c94000000000000000090a0000000000000000000000000009b68099e8000b33106ae2965b58507a804878839f0e28000000e9b50f04bc0008640000000000cf4000000000000000000006a8000423a3d0000000194440ef362b270596bc000a84740246151908d05c08fd786efe38629dde96d5531633ac3267c473e82f1a3e12bc75153406a31d66d1c16d9843c5b828ac2a46fddb134a000075554913dd1ad0000000000ba2adb00031a419830e6888de136500000000000000002ab2bdd98c0000002ddce9e2832619201ab83967532a98faec87376663429c7703ae2d11d2c23c66fa921bc8ef612a81000acd21524787eefc41154747a40000000003ab40a400000000010aa00021c8000ce81fa000000158c6d52cca9c0000dcf00000000000005eb2a01d405a300008
  | 33 => 0x61a440006f586c51d600000026116be06ae0ba4d4b0ea0a0000001554aff00000004902c0000185c000000633a070a2885f0002a5d3600000000000d8bf3d5a083240000000ef2204c45000686a33c0003f01df3ce400000058e0001b23bb21b40a979c6f0a7a630bc0006fb05ab1bda3800071425ace30000000000000099f000000000000016b1f4400000000000002ae00000000012bc39e0000eac25c0eb0003440376d202ce2edc0000e9000000110a00000001988cc0000002964beb2b400000004e8ab600000000006b264817a8ae400054480000000004b900015f40001725e1d80c7cc0000001aee28e65fb73489c1a026d80f00001a48e9808d8f28ff73da5a955e53c5c024d99ee9e879837f4e4aa29773ada06ec000305d9d8652a0d03e9578b3a7b764a0d18000154d0a9d011a6841c54ba056b804e2740da98420000000000000000000000168e0002e2000116c87b36688094784891c50001df0f4d000000000000079487046dc82600005943b470b1078001364614152a44d2cf4f40c81da949a131796a3f97da9dd4b5537452162a590357820095022dba45d96da2716800011be1407fa3c5672a0914cb08e0002db30f8fb000000070e8629cb20003ed0000d608cc5ab2ba57d60d60211f8800095a393042cc806a878429e67aee221e600006bca3e9138e5b4fc71d022b3c8ff675e0ed8000000dac45aac1ca58ad680030c8a7ec1c900812400017b5424001a06ee00000000e3c3b8203000000000000000000000000000001c2c2032e391b4bb6a0256100002c08a424580000000000540000000c9300000000001cb0000000c51000000000000000037439e800000000d0000000000000092c91ebee63b895a2640005140000000b3100006066ea24c82c00008d200011d0000000f38000000057c0006ee90cc00000000000000000000000000000000000271000054c12fb3548f4f3a07ba3806826f61f292b409818649c8154000284c951e08000405325363400095c0000000348bdfdac17b9afa2335177c25b5e83040c04d8e08d9c1678e10000e255e377d5e1ce93706b5a5492077122e3d40008942f198f0000856082bd000000001368000000000567000185cdbe5da8000e589680000ba000000000027d152200000032559f0d8fe078001caeca3077249d594bbc02f87e400012800012fc1670005aa00000003d40003d0c0000000000001aa200015015d00000005081469440beba66b1e058a00000000010e000000014180000000003b79b27000314bb0800009a9a4800000000000005f02729070000000000a5e626800009a0000002714b42000000237d8a28a832f000000000000014eca72000044e4f854c0005023219d64e4d0000e74a460005678000fce000000105c00000030480005a4d4f00000000008
  | 34 => 0x91480004f800000065eaaed2028343b000000000000000321a7800000028953e212b0e920159c80000d80001a1c9ca00007b000000000000008680004e83224000b340002a684bc00041f800000000000008401f00b02843415dc87e0022edd800096580000000004ab568000000054e00001a9676000000058c00000000000000004d573a0000000d3e5c1800050c0002790000000cab76519b00009484b49ef145b6414004b08bf89de65b9898a680000001a6d07acdd00003649b2623018297c33a91600020b472e22800000008f00005eaa891c703430000000082b152fc80000004935da11d0acef2e573000198076e000000101cc2517bc46d40a0001788000a520000003465d7ab9b00022745c6a9377321e809000075606f84ee21d48a19cc00016f4aa80000005fa69a960800026833b933c7b00000000001cc60000003324000c4b000084400000054b000000000000006b40003833bba9c419584d000054c000e3a2813b8944eb880003a11486ed416a1b5cea80004e40000f7a7363ce11480009f60bf647d0e20f0280263341e02913020c9e326d21a40cd4000e092debb41b102c753b7c546803bd139000000094d4a008a54028a20af2ad59da398083a084000bf205492a8d52d8061326ddda48090000a3106c7430cd36518262d1711af204ec9bc6408d44000f3708f0001b940003ad00000006e52b480000000000001728120a7853c8000000157bb0b5200000000000000000711367ac105d884503a09bd96a8d56421a740001b700000014840ea00004b000000063e8b4c00000060493012ee00053231d93c80bb2000a2424eedad338001abe43179529f5eac27141984954a661518e07c852e72b489e0ed1f484c02f4c51cf27223c224dc5167ec62da3956cac34745bd10252e56409b9a5a466f9352382024646f0880000000d83181000000008a2c4095c21d16d69d8000000b936adb1280000003c890ec0006c30001164000acd663b92d4c296c5d0cd89e9c78b389b89800000000000016989ae0002acc9641047078000ca600077624b51d700014a00000000006b8000000000000031ecf3000000035580007f72a3bbfc0000000000000f26ef15ba80000000005c8800000000065b2eec000000000000000000000020298cc7f1335800033c40a54f067031a0000002620b6ae5b00010ac00000000009250de2a7b3fa9d452cae33be84599f6e7200000017ea0000000000000bb06ee04a6c4a78128796a0e4e0004e6b76ce3262b4490ca1c2a306d2e8cbd4d20005a92afc84800000005b9accbd45f9800146400000009680005656dc0dedb92ad46ef2a71659c4f0e701ae000c8f6642f9848c34b00004d40004c824092f535a00005a6be4edae076fb9e8d9606b2f768fc46e05960002fbd7fb13363a86b8ef498ff5f0
  | 35 => 0xedc000be529503d80006054a3934d6747710fe35cc00087200000000000002b58bf14700b63e31808bf60ab5b5b1f8188000016955129c00b78d8dfc00012480001956dc0000a2800188ab9f4af8000000e311acb7984770000002ea0000e1f00007dce3eae509315618a045372280000000006060000846
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe67535882104001ccaa6b104208003a9d0d620841000752a1ac41082036ae786d082104001ccacba1042080dba9993420841000572c30841082000b65851082104001ccaca2104208002f160c420841000738b2ce010820008f7865c02104001ce2cab80420800a1fa1576d001009c3fc32eba00200487f8759740040010fb0eb2e8008003179cd65d00100062f32ae7a002000c5d655cf40040050fd0bbb480080021f617769001000477416ed20020008ed82dda40040010ff0cbac80082461fe1d65900103443ec3acb2002000cb5649c640040050fd0b3b080080021f61676100100063ab2ce22002000c75655c440040013c904b8880080031d596718801000672b14e31002000c75655c620040019ceec10c40080039959421880100143e42eec90020008f781dd9200405f0fb0dbaa40080021fa1d65480100243e43aca9002000c5c73595200400187ccbba240080030f59774480100061f328e89002000c3d651d120040018bccbb9a40080031759773480100063b32ee29002000c7565dc520040018ecca38a40080031d59471480100143f42cec100200087d859d820040050fd0abb0400800a1fa1476080100043ec28ec10020078be841d8200400117b083b0400800637a0c76080100046ec18ec100200087f8759420040010fb0eb2840080063d61a710801000672bb0421002000e656508420040017c30010840080023d61872c40100263cbb2cb0802000e716598610040050f90bbb220080261f61b75440100043f43aca880200487c8759510040018b8e6b2a20080030f99774440100061eb2ee88802000c3e651d1100400187aca3a220080031799773440100062eb2ee68802000c6e65dc910040018dacbb9220080031b994724401000636b28e48802000c7665dd910040018e8ebbb22008003351cf76440100063bc2eec8802000c7485dd910040018eea7bb220080031d54f76440100065ba1eec8802000cb543dd910040018eeedbaa20080031ddd965440100065bbb6e88802000cb7761d110040019aeedb9a200800339ddb72440100047ac34e488020009e6829c910040019ceec392200800359dd47244010006b23a8e48802000da7741c91004001b48e8392200800371dcc7244010006e2398e48802000d66651c91004001acaca392200800339d8c724401000672b18e48802000d67531c91004001acaa6392200800369d0c7244010006d2a18e48802000ce6601c910040018f4cbbb220080031e1d776440100066c39eec8802000c7b85dd910040018f10bbb220080031ed4f76440100063ca9eec8802000cbb43dd9100400197287bb220080031eddb75440100063dbb2ca8802000cbb76dd11004001976ec3a22008003661cc74440100066dbb6e68802000ceb76dc910040019d6ec3922008003781cb7144010
  | 1 => 0xce6a98c408003175cd531881003c5fc3e8631020008bd87d0c620412b87ceba18c4080030f5d7431881000e4f39e863102000c9d73d0c620400117f0ea18c4080022f61d43188104a61f3aa863102000c3d7550c620400393ce6a18c408003275cd43188100070ea9a863102000cb5749c462040019aae7388c4080031e5d670188100065cba4e03102000cd9739c062040050fd0b3b684080021f61676d081003c7ac34e3a102000c75659c742040018eacab8e840800a1fa1676908100043ec2ced210200287e851da42040010fb0a3b4840800637a0c76908100046ec18ed21020078ed8798a42040050f90bbb2840800a1fa1676508100043ec2ceca10200087f855d942040050f90abb284080ea3de0576508100143f428eca10200087d851d942040031bd063b284080023760c76508100043ec36eaa10200087e8759542040010f90eb2a840801e3b21d62508100063b32ee2a102000c7565dc542040011eb0c38a84080031d99471508100063ab28e2a102036cb6641c5420400196ac838a840800339988715081000672b10e2a10200287e859d842040010fb0b3b0840800a1fa1576108100043fc32ea210200087f8759442040010fb0eb288408003179cd65108100062f32ae62102000c5d655cc42040050f90bbb2820807a1f61b75504100043f43acaa08200487c8759541040018dccbb9282080031b597725041000637328e4a082000c6d651c941040050fd0abb082080021fe1975104100043fc3aca208200087d8759441040018bce6b2882080031799573104100062eb2ae62082007c9e645cc410400193ac8b98820800a1fa1576c84101e43fc32eb908200487f8759721040010fb0eb2e42080ee9de1d65c84100053ac3acb9082000a778359721040014eb06b2e42080038dd0d65c84100071aa1acb9082000a7585d8b21040050fd0bbb442080021f617768841003c5f426ed10820008bd84dda21040031bd07bb442080023760f76884100143f42aed108200087f865d621040010ff0eb2c42080021f61d658841049e3b38acb108206bae58158821040d5cccca90842080039959521084100063cb2ce01082000c79655c021040018eea6bb042080031d54d76084100065ba1aec1082000cb5435d821040019cc64bb04208003394c976084100053bc1aca1082000a75835942104001c6e86b2842080038d50d650841000733412ca1082000e658259421041258ece4b284208003998c9650841000732992ca1082000ae5869c821040016cb0b39042080039959672084100053ac2ec41082000ae5869882104001ccacb31042080023de1d62084100073332ac41082000e656558821040015cf0eb10420800339e1d620841000573c2ac41082000ae585588210406d5c908b104208002b9e0d620841000572c1ac41082000
  | 2 => 0x670594100243f43e60b28200087d87cc1650400147d09982ca080028f61330594100062eb9c60b282000e1d438c165040010fd0e182ca080021f61c30594100051f42060b282000a3d840c165040018bae6182ca080038750c30594100053741060b282000a6d820c165040014ed02182ca080029d60430594100043fc1aebb20200287e85dcf64040010fb0bb9ec80800a1fe1f53d90100043ec3ea7b20200087f8754f64040010fb0ea9ec8082570f9d743d90100061ebae87b2020018bf8750f640412987ceaa1ec8080030f5d543d901000e4f39a87b202000c9d7350f6404001c3aa6a1ec8080062f21373590100047c402e6b2020018bc8750d640400193ee6a1ac8080038754d43590100055c40286b20200287e851c964040010fb0a392c80800637a0c72590100046ec18e4b20200087d8799464040018bce7328c8080021fe1d65190100062f39aca32020008bf8759064040018bccab98c80800317595731901003e4f322e63202000c9d645cc64040018dccb390c8080031b59672190100063732ae43202000c6d655c8640400f95cc8b90c8080032b59172190100043fc1aebb10200287e85dcf62040010fb0bb9ec40800a1fe1f53d88100043ec3ea7b10200087f8754f62040010fb0ea9ec4082570f9d743d88100061ebae87b102094c3e7550f620400187aeaa1ec408007279cd43d88100064eb9a87b102000e1d5350f62040018eaeb38ec4080021fe1574988100143e42ae93102001c9e7350e620400193ae6a1cc4080038754d439881000c76c3c653102000e8d434ca620400117f08baac40801e2f21175588100047a40aeab1020008f4815cd620400393ce6a1ac408003275cd43588100070ea9a86b1020018ec874c96204001d1a86992c408002b920532588100143fc32ea310200087d8799462040018bce7328c4080021fe1d65188100062f39aca3102000c3e659d0620400187acb3a0c4080030f99574188100061eb2ae83102000c5e655cc62040018bacab98c4080023be1d621881000656ba2c43102000ccd73588620400f17d09ba8c4080022f613751881000c6f41eea31020008dd83dd462040010ff06ba8c4080030f9d674188100061ebace83102000c3e755d0620400187aeaba0c4080022fe0d74188100143f42ee6310200087d85dcc620400f17d09b98c4080022f61373188100062f3ace63102000c5d759cc620400193ce9398c408003275d273188100062f3aae63102000c5d755cc620400193ce8b98c408003275d173188100062f42ae63102000c5d855cc620400193d08b98c4080032761173188100143fc3ea6310200087d87d4c620412f87ce9a98c4080030f5d3531881000e2f39ea63102000c5d73d4c62040010ff0ea98c4080021f61d53188104b61f3a2a63102000c3d7454c62040038b
  | 3 => 0xc90220078bc845d920440011bf06bb240880063720d76481100143e428ec90220018dc831d920440010fd0fb2a40880021f21f65481100062e39eca90220008be87d9120440011790fb2240880030fdd764481100061e3aec89022000c9c73d91204400117d0e322408801e2f21c64481100061fba8c89022000c3c751912044001938e6322408800237a1f63481100046e43ec69022000c5f75d8d20440018b8ebb1a408800327dd363481100064e3a6c69022000c7765dc520440018e8cbb8a40880032dd9371481100065a326e29022000cd763dc520440019a8c7b8a40880031dd9471481100063a328e29022000cb7641c52044001968c838a408800335d8c71481100066a318e29022000ce7621c520440019c8c438a4088003a618c64c411004e3b3b6cb0822000cb676d92104400f96cec3242088023359db638411000733b28c50822000e646518a1044001d4ec83142088003a9190628411000763b18c50822000ec46318a10440019cee63142088003395cc628411000733a98c50822000e655318a1044001d4e863142088003a950c628411000739b2ec1082200087f865cd65040010fd0fb1aca080121fa1e63594100051f424c6b282000a3d8498d65040018bee731aca0800a1fa1d63594100062fb9ac6b28200087e8718d650400147d0831aca080028f610635941000537410c6b282000a6d8218d650412b87eeda1aca082530fdd943594100068eb9a86b282000e1e6350d6504001c3ac6a1aca080030fdd274594100052f418e8b282000a5d831d165040010fb0f39aca080028fa1273594100051ec24e6b282000c5f739cd65040018bf06b9aca080021fa1c73594100051f420e6b282000a3d841cd650400187ee7a1aca080030f5cf43594100043f43c86b28200087d8790d650413547b0921aca08003175ce43594100062eb9a86b282000a7b8050d65040014f100a1aca0800387e0d43594100061fb9a86b282000e1e7350d650400187ae6a1aca08003875cd43594100060eb9a86b282000e3b8050d6504001c7100a1aca080021fa1c43594100043ec3886b282099a3e8410d65040014ed03b92ca080129d60772594100051fc22e4b282000a3c845c965041254ef02b92ca080029d20572594100043f43e64b28200087d87cc9650400147d09992ca080028f61332594100070ea1e64b282000a7681cc965040014eb03992ca080038750d32594100053bc0a64b282000a74814c965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c965041314f30138aca080121fa1f31594100043ec3e62b282000a3e84cc5650400147b0998aca080038750f31594100053741662b282000a6d82cc56504001c3a8698aca080021fa1c31594100043ec3862b282000a3e840c5650400147b0818aca082629d60
  | 4 => 0x1440ad1d90fb1282880031bdd76250510006363aec4a0a20568ee87189414406d1d90e31282880031bdd46250510006363a8c4a0a2000cd863dc14144001976c838282880033618c70505100143e42cec20a20018dc839d841440370f90cba8828801f0f19175105100062e31aea20a200087f87d9441440130fb0fb288288003179cf65105100061f3aec820a2000c3d75d90414400193ce7b20828806a3721973105100062fb2ae620a2000c5c655cc414400193ec8b98828801f2719173105100046fc3ec620a20088dd87d8c41440018bcebb188288003175d76310510006373aec420a2000c6d75d88414400199ce7b108288003335cf6210510006373a8c420a2000c6d75188414400199ce63108288003335cc621051003d5a4328220a2000e37655044144001b2ae6a08828821fa518d4110510007523128220a200287c859db21440010f90cbae42880031718d75c85100043fc3ecb90a200087d87d97214400187cebb2642880030f5d764c85100061f3a8c990a2000c3d7519321440018bcebb1e4288003175d763c8510006373aec590a2000c6d75d8b21440018dcea31642880031b5d462c851000674314e190a200287c859da21440330f90cbac42880031718d75885100043fc3ecb10a200987d87d96214400187cebb2442880030f5d764885100061f3a8c910a2000c3d7519221440018bcebb1c4288003175d76388510006373aec510a2000c6d75d8a21440018dcea31442880031b5d4628851000675b10e090a2000e676548421440d5cc8ca9084288003a9d912108510007523224210a2000ec76348421440d3d88c6908428800a1f21676d011000c6e41ceda02200087c865d7404400f878c8bae80880031718d75d01100043fc3ecba02200087d87d9740440018bce7b2e80880030f9d764d01100061ebaec9a022000c9e73d9340440011b90cb9e808800317d9573d01100062e32ae7a022000c9f645cf404400f938c8b9e808800237e1f63d01100046ec3ec7a022000c5e75d8f40440018baebb1e80880031b9d762d011000636baec5a022000cce73d8b404400199ae7b1680880031b9d462d011000636ba8c5a022000cce7318b404400199ae6316808801f2d19271d011000672314e3a022000ce4625c740440050f90b3b480880461f21975901103461e322eb2022000c5c635d640440010ff0fb2c80880261f61f65901100061f3aec92022000c3d75d9240440018bcebb1c8088003175d76390110006373aec52022000c6d75d8a40440018dcea31480880031b5d462901100043fc2aeca02200287c855d940440011bf06bb280880063720d765011000477c12eca022000ce462dc5404400196ec838a808800339188715011000672314e39022000ce4625c720440010ff0abb2408800a1f21576481100045fc22e
  | 5 => 0x8002b9607301891000726a9c603122000e8d438c06244001d8c63180c488002b9e0530189100057240a6031220008ee870c062440011db0e180c4880029ba14301891000536c28603122000aae840c0624400155b08180c4880039354c301891000746a18603122000ae6810c062440015cb02180c488003b18c4301891000537c2a203122000a6c85440624400155f08880c488002ab211101891000567c1a203122000acc8344062440010ff0abb6848800a1f21576d09100046fc1aeda1220018dc835db42440050fd0bbb484880021f617769091000c6f41eed21220008dd83dda42440010ff0abb4848800a1f21576909100046fc1aed21220018dc835da42440050fd0bbb284880021f617765091000c6f41eeca1220008dd83dd942440050fd0b3b284880021f61676509100043fc2aeca12200287c855d942440011bf06bb284880063720d76509100143e428eca1220368f4811d942440010fd0dbaa84882730f19375509100062e31eeaa12200087e87d9542440010f90fb2a84880030fdd764509100061e3aec8a122000c5f75d8d42440018b8ebb1a848801e3ba1f625091000637baec4a122000c6c75d8942440018deea31284880031b1d462509100063bb2ee2a122000c7465dc5424400196ec9b8a84880eb2d19371509100066bb1ee2a122000cd463dc542440019c8c5b8a84880031dd9471509100063a328e2a122000cb7641c5424406d968c838a848800335d8c71509100066a318e2a122000ce7621c542440019c8c438a848800a1f216761091000c6e41cec212200087f855d842440050f90abb0848800237e0d761091000c6e41aec212200087c865d4424400f878c8ba884880031718d75109100043fc3eca212200087d87d9442440018bce7b2884880030f9d764109100061ebaec82122000c9e73d9042440011b90cb98848800317d9573109100062e32ae62122000c9f645cc424400f938c8b98848800237e1f63109100046ec3ec62122000c5e75d8c42440018baebb1884880031b9d7621091000636baec42122000cce73d88424400199ae7b1084880031b9d4621091000636ba8c42122000cce73188424400199ae6310848801f2d192711091000672314e22122000ce4625c4424400f970c938084880033a18a701091003c7c432e02122007cb8649c341440010fd0dbaa82882370f19375505100062e31eeaa0a209b87e87d95414411b0f90fb2a82880030fdd764505100061e3aec8a0a2000c5f75d8d41440018b8ebb1a82880023ba1b725051000637b2ee4a0a2000c6c65dc9414400195ec9b92828815b2b193725051000667b1ee4a0a2000ccc63dc941440011dd0c39282880031bd94725051000636328e4a0a2000caf641c9414406d958c8392828800333d8c725051000666318e4a0a20368ee87d894
  | 6 => 0x717b2e863122000e2c65d0c6244001d1ec7a18c488003a318f431891000557432863122000aac8650c624400195ceca18c4880038bd9543189100071632a863122000e8f6350c6244001d18c6a18c488003c354d431891000573434623122000e67658c46244001cc8cb188c488003a9d92311891000752324623122000ec7638c46244001d88c7188c48800399d9531189100073232a623122000ea7644c46244001d48c8988c488003b1d8d31189100076231a623122000f85434c462440015cd033a8c488002b9606751891000575400ea3122000ae9801d462440014df0aba0c4880029b215741891000573c0ae83122000a6e851d062440014db0a3a0c488002b3a0c741891000566c18e83122000ae5811d062440015d3003a0c4880038bd52541891000567418a83122000acd8315062440015cd022a0c488002b960454189100053742ce63122000a6d859cc624400155d09398c488002ab61273189100057340ce63122000ae5819cc62440014dd0a398c4880029b614731891000557420e63122000aad841cc62440015cd02398c488002b9604731891000575400e63122000ae9801cc624400155d09298c488002ab612531891000727a9ca63122000ae68194c62440015cb03298c48800393e0d531891000557420a63122000aad8414c62440015cd02298c488002b9604531891000717a9e863122000e2d53d0c62440014dd0b218c4880029b616431891000726a9c863122000ae68190c62440015cb03218c4880039354d431891000747c1a863122000e8e7350c6244001d1ae6a18c4880038bd4d43189100074729a863122000e2d5350c6244001d1aa6a18c4880038354d431891000537428863122000a6d8510c62440015cd02218c488002b960443189100053742ee23122000a6d85dc462440011dd0fa88c4880023b61f511891000733a8ca231220008ee87cc462440011db0f988c4880029ba17311891000536c2e623122000aae84cc4624400155b09988c488003a350f311891000733a9c623122000e65538c46244001d4e87188c488003a950e311891000573404623122000e8d434c46244001d8f06988c48800399d4d311891000732a9a623122000ea7434c46244001d8c86988c488003a950d311891000762a1a623122000e85434c462440015c900988c4880029ba14311891000536c28623122000aae840c4624400155b08188c4880029be1570189100053642ae03122000aaf845c0624400155908b80c488002b3e0d70189100056641ae03122000aae84d40624400155b09a80c488002b3a0f501891000566c1ea03122000ae681d4062440015cb03a80c4880039ad42501891000573c0aa03122000ae48154062440014dd0b980c4880029b617301891000557426603122000aad84cc062440015cd03980c48
  | 7 => 0x5f7354d62440038b8e6a9ac4880022fa1f435891003c5e43e86b122000c3f75d0d624412b878eba1ac48800327dcf435891000e4e39e86b1220008be8750d62440011790ea1ac4880030fdd543589104a61e3aa86b122000c9f7350d6244003938e6a1ac4880038754d43589100063bbaee2b122000c7475dc5624400196ee9b8ac4880032d1d371589100066bb9ee2b122000cd473dc562440011df0eb10c4880029be1562189100053642ac43122000aaf84588624400155908b10c488002b3e0d62189100056641ac4312200087f855d062440050f90aba0c488007279cd43189100064eb9a863122000e1d5350c62440014dd0b390c4880029b616721891000557424e43122000aad849c8624400159d07390c488002b360e721891000572c0ea431220028ed8794862440015d300290c4880029ba17321891000536c2e643122000aae84cc8624400155b09990c488003a350f321891000572c0e6431220018ed878c86244001d1a86990c4880029ba14321891000536c28643122000aae840c8624400155b08190c488002b960432189100074aa1a623122000c6e76d9462440014db07b28c4880023b61e651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000c6e7619462440014db06328c4880032b9db641891000717b2ec83122000e2c65d90624400155b07b20c4880023b61e64189100053742cc83122000a6d85990624400159d07320c488002b360e641891000477c3ac83122000a6f8559062440014d90ab20c488002b3e0d64189100056641ac83122000cae761906244001c5eca320c4880038b194641891000556c18c83122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e8c64d8c6244001c9f0bb18c48800393217631891000747c26c63122000e8c84d8c6244001d8f03b18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab612631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000a6e8518c62440014db0a318c488002aba10631891000556c20c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244001c9d0a318c48800393614631891000747420c63122000e8d8418c6244001d8b02318c4880029ba1b531891000536436a63122000c6e76d4c6244001c5ec9a98c4880038b193531891000727b1ea63122000e4c63d4c62440014dd0ca98c4880029b2195318910006373b2a63122000e2f6454c6244001c58c8a98c48800393d8d53189100072631aa63122000aae86d0c62440015590da18c4880032b9db43189100
  | 8 => 0xc8b9cc488003179d763989100062ebaec73122000c9e74d8e624400193ae9b1cc488003179d463989100062eba8c73122000c9e7418e624400193ae831cc4880031b9d7629891000636baec53122000cae74d8a624400195ae9b14c488003339cf629891000666b9ec531220078be84dd6624400117b09bacc48800637a0f75989100046ec1eeb312200087f835d6624400187ceb3a4c4880030f5d674989100061f3aae93122000c3d755d2624400117f06ba4c48800a1fa1773989100043ec2ee731220078be84dce624400117b09b9cc488003179d673989100062ebace73122000c9e749ce624400193ae939cc488003179d573989100062ebaae73122000c9e745ce624400193ae8b9cc48800317a1573989100062ec2ae73122000c9e845ce624400193b08b9cc48800a1fe1f53989100043ec3ea73122097c3e74d4e624400187ae9a9cc488007179cf53989100062eb9ea7312200087f8754e62440010fb0ea9cc48825b0f9d153989100061eba2a73122001c5e7354e62440018bae6a9cc48801e2fe1f43989100045ec3e873122095c3e75d0e624400187aeba1cc488007279cf43989100064eb9e8731220008bf8750e624400117b0ea1cc4882530f9d543989100061ebaa873122001c9e7350e624400193ae6a1cc4880038754d439891000e6b39c6331220018f7874c66244001d2a8698cc48800a1fa1b75589100043f43ecab122000c5c73d9562440010fd0e32ac488003171cc65589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f19474589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc645891000c6f436e6b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac4880021f60f75589100045fc22eab1220078bc845d562440011bf06baac4880063720d75589100047bc0aeab122000c3f75dd16244001878ebba2c4880022f60f74589100061fba8e8b122000c3c751d162440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100064fc26e6b122000c9c84dcd62440010ff0ab9ac48800a1f21573589100045fc22e6b1220078bc845cd62440011ef02b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f53589100143e43ea6b122000c3f74d4d624412f878e9a9ac48800317dcf535891000e2e39ea6b12200087e8754d62440010f90ea9ac4880030fdd153589104b61e3a2a6b122000c
  | 9 => 0x63d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727428c7b122000e4d8518f6244001d1d0831ec488003a361063d891000762c08c7b122000a6e86d4f62440014d90da9ec4880038bd9353d891000716326a7b122000e4f63d4f6244001c98c7a9ec4880029ba1953d891000536432a7b122000e2f6454f6244001c58c8a9ec48800393d8d53d89100072631aa7b122000aae86d0f62440015590da1ec4880038bd9743d89100071632e87b122000e8f63d0f6244001d18c7a1ec488002aba1943d89100055643287b122000e2f6550f6244001c58caa1ec488003a3d8d43d89100074631a87b122000f0d5350f6244001d88c718ec488003e150d31d891000573408ebb122000ae5811d762440014dd0bba6c4880029b61774d891000572c0ee9b122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce9b122000e2f54953624400159d062a6c488002b360c54d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000537428e7b122000a6d851cf624400155d0839ec488002ab61073d891000573408e7b122000ae5811cf624400155d0929ec488002ab61253d891000727a9ca7b122000e4f8354f624400155d0829ec488002ab61053d891000717a9e87b122000e2d53d0f62440014dd0b21ec4880029b61643d891000726a9c87b122000e4d5350f6244001d1f06a1ec488003a3dcd43d89100074639a87b122000e2f5350f6244001d1ca6a1ec4880038b54d43d891000746a9a87b122000e0d5350f62440014dd0a21ec4880029b61443d891000537c2ae3b122000a6c855c762440011dd0fa8ec4880023b61f51d89100047743e63b1220008ed87cc762440014dd0b98ec4880029b61731d89100055742663b122000aad84cc76244001d1a8798ec488003a350d31d89100053742863b122000a6d850c7624400155d0818ec488002ab61031d89100053742ee1b122000a6d85dc3624400155d09b86c488002ab61370d89100056741ee1b122000acd83dc3624400155d09a86c488002ab61350d89100056741ea1b122000acd83d436244001cd6a1286c4880029ba1730d891000536c2e61b122000aae84cc3624400155b09986c4880039354e30d891000746a1c61b1220008ee870c362440011db0e186c4880029ba1430d891000536c2861b122000aae840c3624400155b08186c4880039354c30d891000746a1861b122000ae6810c362440015cb02186c488003179cf65989100062f398cb3122000c3f659d26244001878cb3a4c4880030fd9574989100061e32ae93122000c3e75d92624400187aebb24c488003279cf64989100061f3a8c93122000c3d75192624400193ce6324c48800317d9573989100062e32ae73122000c9f645ce6244001938
  | 10 => 0xb1a2000e1f65d936344001c38cbb26c68800387dd764d8d100070e3aec9b1a20008dd8799363440014bd0b326c6880029761664d8d100054f424c9b1a2000ace82993634400159b05326c68800237e1d64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100054f430c9b1a2000c9e761936344001c3eca326c6880038719464d8d100070fba8c9b1a2000e1c7519363440115ad0db8ec68800365dd371d8d100062f386ebb1a2000c5c70dd763440014bd0b3aec688002a7a1275d8d100054ec24ebb1a2000a9f845d7634400153908baec688003175d475d8d100052f438ebb1a2000c5e871d763440018beebba6c68800327dd774d8d100070fbaee9b1a2000c1f75dd3634400193aebba6c688003871d774d8d100064eb8ee9b1a2000c9e70dd36344001938e1ba6c68800297a1674d8d100052ec2ce9b1a2000a9e849d363440014bf0aba6c6880029721574d8d100062fbaae9b1a2000a9e871d3634400193d0e3a6c68800387dd474d8d100070e3a8e9b1a2000e1f5495363440011bd0e2a6c6880023761c54d8d100064fba6e5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000a5f855cb63440014b90ab96c688002a7e1172d8d100054e422e5b1a2000c9f745cb63440015af02b96c688022b520572d8d100056b40ea5b1a2000ad581d4b634400193ee9b8ec688092b6a0371d8d1000567416a3b1a2000acd82d476344001caea328ec688092b5a0770d8d100046f43ea1b1a20008dd87d43634400153d09a86c688002a761350d8d100072da84a1b1a2000c9f7350f6244003938e6a1ec4880038754d43d891001477c3aa5b122000a6e85ccb62440014db0b996c488002aba1332d891000556c2665b122000e8d43ccb62440031df0e996c488003a350d32d89100053742865b122000a6d850cb624400155d08196c488002ab61032d891000536c1ecbb122000aae84997624400155b0932ec488002b3a0e65d891000566c1ccbb122000aaf84597624400155908b2ec488002b3e0d65d89100056641acbb122000a6d831976244001c5ecbb26c4880038b19764d891000556c1ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c488002ab60c64d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec488003a319363d891000727c2ec7b122000e4c85d8f6244001d1f09b1ec488003a321363d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000537428c7b122000a6d8518f624400155d0831ec488002ab610
  | 11 => 0x4400187ecbb98c8880030f19773191100061fb2ae63222000c3c655cc644400117f0fb18c888003275cf63191100045ec3cc63222000a3e8598c644400147b0b318c888002aba0a631911000556c14c632220008bf8758c644400147f0ab18c8880028f215631911000557c12c63222000aac8258c644400117b0e318c8880028fa1463191100051ec28c63222000c9d7318c6444001c3eca318c8880038719463191100064ec38c63222000e1e8518c6444001c3b0a318c888003a560463191100051f436a63222000a3c86d4c644400187ceda98c88800387d8f53191100070e31ea63222000a3e8654c64440014790ca98c8880030f9d953191100068eb9aa63222000e1f6354c6444001c38c6a98c888003a518e3119110006cab9a6232220078bf835cc644400f93f06b98c88825f0fdcf53191100061eb9ea632220078be8794c644400117b0f298c88825a8f61653191100064eb9ca63222000e1f5394c644400193ae6a98c88800387e0d53191104b61fb9aa63222096e1e7354c644400187ae6a98c88825b875cd53191100060eb9aa632220078be8714c644400117b0e298c88825e8fa1453191100055b40ea43222000ab581d48644400f17d0f990c8880022f61f32191100051f42e643222000a3d85cc8644400193ae7990c888002ada0732191100055ac0e643222000c9d734c8644400f17d0e190c8880022f61c32191100051f428643222000a3d850c8644400155d05a88c888002ab60b511911003c5f43e6232220008bd87cc4644400147d0b988c8880028f61731191100064eb9e623222000aae82cc4644400155b05988c888003275cd31191100055dc02623222000ab8804c4644400f17d0e188c8880022f61c31191100051f428623222000a3d850c4644400f17d0fa80c8880022f61f50191100054f41ea03222000a9d83d406444001c76a1280c88801e2fa1f30191100045ec3e603222000a3e85cc0644400147b0b980c888003275ce30191100070ea9c6032220078be870c0644400117b0e180c8880028fa1430191100051ec28603222000c9d730c06444001c3aa6180c888002aba08301911000556c10603222000ab6810c0644400156b02180c8880028fe1510191100051e42a203222000a5e86dd763440018bcedbaec68800297a1875d8d100062f3b0ebb1a2000c5e76d9763440011bb0f32ec68800297a1665d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100046fc3acbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000a5e8619763440018bcec32ec688002a7a1b74d8d100064f3b6e9b1a2000d1f75dd36344001c3ecbba6c6880038719774d8d100054f430e9b1a2000c9e761d36344001c3eca3a6c6880038719474d8d100064f3b6c9
  | 12 => 0x22f61f50d91100054f41ea1b222000a9d83d436444001c76a1286c8880022fa1f30d91100045ec3e61b222000a3e85cc3644400147b0b986c8880038754e30d91100045f43861b2220008bd870c3644400147d0a186c8880028f61430d91100070ea9861b222000aae820c3644400155b04186c888002ada0430d91100055ac0861b222007c3c645d664440018bce7b2cc888003179cc65991100061f3aec93222000c3d75d92644400193ce7b24c88800317d9573991100062e32ae73222000c9f645ce644400f938c8b9cc888003179d463991100062eba8c73222000c6f659ca64440018d8cb394c8880032bd92729911003e56324e53222000ccc639ca64440018decab94c8880031b195729911000657b22e53222007cac645ca6444001998c6b94c8880021fa1f65591100062e39ecab22200087e8719564440018b8e632ac88800317d9773591100062e32ee6b222000c5f7518d64440018b8ea31ac8880031bd9772591100063632ee4b222000ccc63dc964440018deca392c8880031b194725911000666318e4b22200087d83dd5644400117f08baac88800237e0d755911000c6e41aeab2220008ef825d564440011d904baac8880030fdd774591100061e3aee8b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fc2ee6b222000c5c85dcd644400193f09b9ac8880021fe1573591100143e42ae6b2220008bf845cd64440011df04b9ac8880023b20973591100047dc02e6b222000c5f751cd64440018b8ea39ac88800327dd073591100043f43ea6b22200287c87d4d64440018bee7a9ac888007171cf53591100043f43aa6b22200087c8754d64440018bee6a9ac888007171cd53591100045f43e86b222000c3f75d0d644412b878eba1ac88800327dcf435911000e4e39e86b2220018bc8750d644400187eeaa1ac8882530f1d543591100064fb9a86b222001c9c7350d6444001c3aa6a1ac8880031bdd77259110006363aee4b222000caf74dc9644400199ee7b92c888003331cf725911000637a9ee4b222000c6d53dc9644400195e87b92c8880032b50f725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000c6f531c964440018daa6392c8880032bd0c725911000656a18e4b222000ce472dc564440019b0e7b82c8880022fe1d64191100051fc2ac83222000a3c85590644400153f06b20c888002a720d641911000557c12c83222000aac82590644400117b073b0c8880030f9db65191100051ec1eca32220008bd87994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c8880030f9d865191100051ec18ca32220008be86dcc64
  | 13 => 0x51ec2061b2a2000e1d430c365440014dd04186ca880029b60830d95100053b40861b2a2000a75810c3654400187aebaa6c88800b0f1d654d91100145fc3aa9b222000a9e83153644400153b062a6c88800317dcd53d911000e2e39aa7b222000c9f73d0f644400147d0b21ec8880028f61643d91100070ea9c87b2220018bf8750f644400193ae6a1ec8880038754d43d91100051f42887b222000a3d8510f64440050fd0b396c8880021f61672d911000c6f41ce5b2220008dd839cb644400147b07b2ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec8880028f60c65d91100061fb2ee7b222000c3c65dcf644400187ecab9ec8880030f19573d91100064eb9ec7b222000a3e8598f644400147b0b31ec888002aba0a63d911000556c14c7b222000a3f8558f64440014790ab1ec888002abe0963d911000556412c7b222000a3e8518f644400147b0a31ec888003275cc63d91100070fb28c7b222000e1c6518f644400193b0e31ec88800387a1463d91100070ec28c7b222000e958118f644400147d0da9ec8880028f21b53d91100070fb1ea7b222000e1c63d4f644400147d0ca9ec8880028f21953d91100068fb9aa7b222000e1f6354f6444001c38c6a9ec888003a518e31d9110006cbb9a63b222000a9e839d7644400153b073aec8880030f5d475d91100051f42ce7b222000a3d859cf644400193f06b9ec8880028fa1473d91100051ec28e7b222000ab6811cf644400156b0239ec8880030fdcf53d91100061eb9ea7b2220008be8794f644400117b0f29ec88800327dce53d91100070fa9ca7b222000c9f7354f6444001c3f06a9ec8880030fdcd53d91100070fb9aa7b222000c1f7354f644400187ae6a9ec888003871cd53d91100045f438a7b2220008bd8714f644400147d0bb96c8880028f61772d91100055ac0ee5b222000a3e859cb644400147b0b396c888002a7a0e72d91100054ec1ce5b222000ab681d4b644400156b03a96c8880022fa1f32d91100045ec3e65b222000a3e85ccb644400147b0b996c88800327dcf32d91100055b40e65b222000ab581ccb644400193ee6996c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c8880028fa1771d91100051ec2ee3b222000aae82dc7644400155b05b8ec888002aba0b51d911000556c16a3b222000e3751947644400117d0f98ec8880022f61f31d91100051f42e63b222000a3d85cc7644400193ee798ec888002aba0b31d911000556c1663b222000c9f734c7644400117d0e18ec8880022f61c31d91100051f42863b222000a3d850c7644400147f0ab86c8880028f21570d91100054fc1ae1b222000a9c835c3644400117d0fa86c888
  | 14 => 0xd859d942840010ff0abb2850800a1f2157650a1000636bacc42142000ccd7398842840018daeab108508003335cd6210a1003c7cc34e021420008bd87d90418400193ec8b98830801f27191731061000636bacc590c2000c6d7558b21840014ef0ab1643080035c5d570c86100053bc2aec10c2000b65859c821840011eb0fb1043080027961f6208610005f1406c410c2000ae587d8821840019cb0fb104308002b9e17620861000572c2ec410c2036ae684d8821840015cf07b104308002b960f620861000733a9ec410c2000e6553d882184001d4e87b104308003a950f620861000771406c410c2000a778558821840016cb0a3104308002f8a0062086101b5724368410c2000ae68610821840016cb0a2104308002f160c4208610005f14008410c2007cb6645c440840013c904b8881080021fa1b73d95100143fc3ec7b2a2000c5d73d8f65440010fb0f31eca880028fa1263d95100051ec24c7b2a2000a6e8298f65440014db0531eca880021fe1d63d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d951004c3ec38c7b2a2000a3e8418f654400147b0831eca88003175cc63d95100062ec38c7b2a2000e1e8418f6544001c3b0831eca880039560463d95100051f43687b2a2095c3e76d0f6544001c3ec7a1eca880038718f43d95100051e43287b2a2094c3e7650f6544001a3ee6a1eca8800387d8d43d95100070e31a87b2a2000e54638c76544001e2a8698eca8800297a0e74d95100052ec1ce9b2a2000c3d741d365440010fb0f39eca880028fa1273d95100051ec24e7b2a2000c5f835cf65440010fd0e39eca880028fa1073d95100051ec20e7b2a2000c5d731cf654413f4ed0239eca880029d60473d95100061fb9e87b2a2000c3d73d0f65440010fd0f21eca880021f61e43d95104f51ec2487b2a2000c5f7390f65440018bee6a1eca8800387e0d43d95100061fb9a87b2a2000e1f7350f654400183ee6a1eca880030f5cd43d95100070e39a87b2a200087e8710f65440010fb0e21eca882768fa1043d95100053bc0ae5b2a2009a74815cb65440010fd0f996ca880021f61f32d95100051f42665b2a2000a3d84ccb6544001c3a87996ca880029da0732d95100053ac0e65b2a2000e1d434cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb654404b4f501b8eca880021fa1f31d95100043ec3e63b2a2000a3e84cc7654400147b0998eca880038750f31d95100053741663b2a2000a6d82cc76544001c3a8698eca880021fa1c31d951004c3ec3863b2a2000a3e840c7654400147b0818eca880969da0770d95100043f43e61b2a200087d87cc3654400147d09986ca880028f61330d95100070ea1c61b2a200087e870c365440130fb0e186ca880028fa1030d951000
  | 15 => 0x8ba8c9880022fe1d64193100061ebaac83262007c9e645cc64c400193ac8b98c9880021fe0d7598b100143f42ee7316200087d85dce62c40050ff0fa9cc5880021f61f5398b100043fc3aa7316200087d8754e62c412b87ceba1cc5880030f5d74398b104a61f3aa873162000c3d7550e62c400393ce6a1cc588003275cd4398b100070ea9a873162000e95434c662c400393ce6a1ac588003275cd4358b100070ea9a86b1620008ef8758862c40010ff0aba0c58800a1f2157418b1000e2f39aa63162000c5d7354c62c400393ce6a18c588003275cd4318b100070ea9a8631620018f5878c462c4001d2a86988c5880021fe1576d0b100143e42aeda16200287e85dda42c40010fb0bbb4858800a1fa167690b100043ec2ced21620018de839da42c40011bb073b485880021fe157650b100143e42aeca162007c3e645d442c400187aeab20858801f279917310b100064eb22e62162007c3e645d441c400187aeab20838801f2799173107100064eb22e620e2000d957350441c40014db0b31443880029b616620871003e1f322eba062000c3d7559340c400f93cc8b9e81880032759173d03100045ec3ec820620008ee82dd764840011db05baec9080021fe0d75d92100143f42ee7b24200087d85dcf64840011dd05b9ec9080023b60b73d92100143fc3ea7b24200087d87d4f64840010ff0ea9ec9080021f61d53d92104ae1f3ae87b242000c3d75d0f648400317f0ea1ec9082530f9d543d92100061ebaa87b242000c9d7350f6484001c3aa6a1ec9080031b9d672d921000636bace5b242000c6f539cb64840018daa7396c9080032bd0e72d921000656a1ce5b242000c6e755cb64840018daeab96c9080031bd4d72d921000636a9ae5b242000caf435cb648400195a86b96c908003399c971d92100064fb22e73242007c9c645ce64840031790ea1ac90800327dcd435921000e4e39a86b242000e1d5350d64840050fd0a392c9080021f61472592100045fc3ac832420078be84dd7628400117b09baec50800327dcd43d8a1000e4e39a87b142000e1d5350f62840010ff0aba4c50800a1f2157498a1000e2f39aa73142000c5d7354e628400393ce6a1cc508003275cd4398a100070ea9a8731420028ed8794a62840031db0f194c508003a350d3298a100043ec1eeab14200087f855cd62840050f90ab9ac5080021fa1f5358a100143e43ea6b14200087e8754d62840010f90ea9ac5080030fdd74358a104ae1e3ae86b142000c3f7550d6284129878eaa1ac50800327dcd4358a1000e4e39a86b142000e1d5350d62840058d8eb292c50800a3b21d5258a1000c7643a64b142000e8d434c962840011df0eb10c5080031b5d56218a100143f42ceda14200087d859db42840010ff0abb4850800a1f2157690a100143f42ceca14200087
  | 16 => 0x6085400043ec28ec10a80018de831d821500011bb063b042a00029d614610854000572c10c210a8000ae68648421500015c90c90842a01a30f9d975901403469d382eb2028000a3d85186405000393ce6a1cc220003275cd43984400070ea9a87308800287e859ca61100010fb0b394c22001e3d61e519844000c7ac3c633088000e95434c661100050fd0fbaac2202370f1d3755844046f1a20eeab08800087d83dd5611011b87e87baac22001e2f211755844000477c12eab0880008ec825d56110137878e83aac22026f8d10475584400043fc2ae6b08800287c855cd611000f17908b9ac2200023be09735844000476412e6b08800087e87d4d61100050f90fa9ac22025f8d10753584400043f43aa6b08800087c8754d611012dc6882a9ac2200030fdd543584404a61e3aa86b088000c9f7350d6110001c3aa6a1ac220002ad205435844000637baee4b088000c6c75dc961100ad958e9b92c22015ba9107725844000637a9ee4b088000c6d53dc961100ad95e87b92c2200032b50f725844000637ba8e4b088000c6c751c9611006d958e8392c2200db39dc472584401b752208e4b088000c6f531c961100018daa6392c2200db2bd0c725844000656a18e4b088036ce5811c9611006d9ce82392c2200db3910472584400163a3aca2b088000ce472945611000f1e90ea8ac22001ead211515844000672392a2b088007ab4848c561100019c8e518ac2200063d21d315844003d5a42262b088000e95434c561100019c8e498ac220002bc201315844003e5b38aed208800093d859ca411000127f0ab84822000267e0d70904400143f42eed108800087d85dda21100018eaeb30c42200da3de1d61884400063abaac31088000ae48258621100010ff0abb2422000a1f21576484401d47b43cc29088007cb47458521100015c904b0a42200021fe1576084400143e42aec1088036cb4415d8211000117b0dba042200dab9219210844000673bb2421088000ce576484211006d7490890842200030fa1776500400061ec2eeca0080008bf83dd9401000117b07bb280200030fd4f76500400061ea9eeca008000cba50dd94010001972a1bb280200024f614715004000e2f39aa7b262000c5d7354f64c400317f0ea1ec988007279cd43d93100064eb9a87b262000e1d5350f64c400157100a1ec98800a1fa1672d93100043ec2ce5b26200287e87dd564c40010fb07baac9880021fa1c75593100052ec18eab262002c3c7595164c40051790eaa2c9880021fe1573593100143e42ae6b26200087e87d4d64c40050f90fa9ac9880021fa1d53593100043e43aa6b262001c5e7354d64c40018bae6a9ac9880030fdd743593104ae1e3ae86b2620018bc8750d64c400187eeaa1ac9882530f1d543593100064fb9a86b262000e1d5350d64c400f87cc
  | 17 => 0xc8000c6e659cb61900018dacb396c3200031b99572d864000636b2ae5b0c8000a5d8399661900015cd05b0cc320007179cd53986400062eb9aa730c8001c9e7350e619000193ae6a1cc3200038754d43986400143f42ce530c800087d859ca61900031eb0f18cc320003a550d31986400052ec1ccab0c8000c5f7354d61900038b8e6a9ac32000327dcf43586400064eb9a86b0c8000e1d5350d61900050fd0bb92c3200021f617725864000c7a43a62b0c8000e95434c561900050ff0cba8c3200021f61e65186400052ec1cca30c800087f8759461900011ef0eb08c3200024f61672906400071ab2ac320c800093f855c2419000133f06b8483200021f61b75506400043e43acaa0c8000c6e65dc941900018dacbb9283200031b994725064000636b28e4a0c8000ce47298541900019c8e4b0a83201924fe1975106400049fc1aea20c800093d835d4419000187ec6ba883200030f58d751064003e1f302ea20c8007d3a605d4419000127b0eb28832018727a1973106400064ec32e620c8000d1e855cc4190001a3b0ab9883200034799573106400068eb2ae620c8007c9e605cc419000fb34c0b988320003275cd61106400143f42eed10c800087d85dda21900031bd07bb443200023760f76886400143f42ced10c800087d859da21900050fd0abb443200021fe1975886400043fc3acb10c800087d87596219000165b0a2144320002e360c42886400143f428ec90c800087d851d9219000187ccbba2432000a1fa1676086400043ec2cec10c8000ae582984219000166b0a2084320002e560c410864000573c324210c8000ae58648421900d5cccca90843200039959521086401b5d24224210c8000c79659c021900018f2cab80432001e6e21170086400061f32aeda04806093f865d7409000127f06bae81200024f60d75d02400061fb1aeba048000c3d635d7409000f87cc0bae812001f4e98175d02400049ec3acba048000c3d7659740900bd93d0cb9e81200032761973d02400068f42ae7a048000d1d855cf4090001a3ccab9e81200034759573d024003e4f302e7a048007d9a605cf409000193ee6a1ec2a0007271cd43d85400070ea9a87b0a800087f855cb61500050f90ab96c2a00023de1d611854000572412c230a800087f835d461500050fd0bb98c2a00021f61773185400143fc3ea630a800087d87d4c61500010ff0ea98c2a00021f61d53185404ae1f3ae8630a8000c3d75d0c615012987ceaa18c2a00030f5d5431854000e4f39a8630a8000c9d7350c6150001c3aa6a18c2a0002ae201431854000672396c2a0a8000ce47218541500050fd0a3b442a00021f614768854000536c28c510a800287e851d921500010fb0a3b242a00021fe1576085400143e42aec10a80008df835d821500031b906bb042a000a1fa147
  | 18 => 0x12d8bae8baac7a0003875d17558f400060eba2eab1e8000c5e705d563d00018b8e0baac7a025b871017558f404bd2f428eab1e8007a9e841d563d002553b083aac7a000297a177158f400052ec2ee2b1e8007a9e84dc563d002553b09b8ac7a0003275d37158f4000567416e2b1e8000acd82dc563d00015b700b8ac7a0286b62017158f400052f428e2b1e8000a5d851c563d000f53d0838ac7a004aa76107158f4000567416a2b1e8000acd82d4563d00bd53f08b82c7a000237a1f5058f400046ec3ea0b1e8007a9e84d4163d000153b09a82c7a000396d425058f400054fc22a0b1e8007a9c8454163d000393ce6a1cc3a0003275cd43987400070ea9a8730e800287e859ca61d00010fb0b394c3a0007279cd43587400064eb9a86b0e8000e1d5350d61d00050fd0bb92c3a00021f61772587400143f42eed10e800087d85dda21d00050fd0abb443a00021fe1975887400062f31aeb10e800087f8759621d00010fb0eb2c43a0003179d563887400062ebaac710e8007c3e7459421d000187acaba043a001f279d163087400064eba2c610e8000ae58298421d00015cf0c90843a0002b961921087403573332a4210e8000e656548421d00d3d8cc690843a0003b158d210874008d1fc32e8b2c800087f865cd65900010fd0fb1acb20003175cf635964008c3f43cc6b2c8000c5f7398d65900050fd0eb1acb2000317dcd63596400043f438c6b2c8000c5d7318d65900014ed0231acb200029d604635964048e1fbb686b2c8094c3f7650d6590001a3ae6a1acb200038798d43596400070eb1a86b2c8060a7b805d165900010fb0f39acb201a28fa1273596400051ec24e6b2c8000c5f739cd65900018bf06b9acb200021fa1c73596403451f420e6b2c8000a3d841cd65900018bae639acb200030fdcf43596400061eb9e86b2c800087e8790d65900010fb0f21acb202828f61243596400062eb9c86b2c8000c5d7350d65900d1c3886a1acb200029ee0143596400053c40286b2c8068a3f8350d65900d1c3f06a1acb200030fdcd43596400070f39a86b2c8000c3d7350d6590001c3ae6a1acb20003075cd43596400071dc0286b2c8000e388050d65900014dd05b8acb200029b60b71596400051fc22e2b2c8068a3c845c565900010fd0f98acb200021f61f31596403451f42662b2c8000a3d84cc56590001c3a8798acb200029ba0b315964000536c1662b2c8000e1d434c565900010fd0e18acb200021f61c31596403451f42062b2c8000a3d840c565900230fd0f982cb200021f61f30596403451f42660b2c8000a3d84cc165900018bae7182cb200038750e30596400043f43860b2c806887d870c165900d147d08182cb200028f61030596400062eb9860b2c8000e1d430c165900014ed02182cb200029d60430596400052ec1ccbb
  | 19 => 0x2f820121580210043ec1eeab0042008bf845d5600840f17908baac01080237e0d755802100c6e41aeab004200c3f75dd16008401878ebba2c0108022f60f74580210061fba8e8b004200c3c751d160084018beebb9ac010803171d773580210064fba6e6b004200c9c74dcd60084018bf0bb9ac0108031721773580210064fc26e6b004200c9c84dcd60084010ff0ab9ac01080a1f21573580210045fc22e6b0042078bc845cd60084018beea39ac010803171d473580210064fba0e6b004200c9c741cd60084010fd0fa9ac01080a1f21f53580210061fba6a6b004297c3c74d4d60084018bee7a9ac010807171cf53580210043f43aa6b00420087c8754d600840187ee8a9ac010a5b0f1d153580210062fb9aa6b004201c5c7354d600840117d0fa1ac01081e2f21f43580210061fbae86b004295c3c75d0d600840193ee7a1ac010807271cf43580210045f43a86b0042008bc8750d600840187eeaa1ac010a530f1d543580210064fb9a86b004201c9c7350d6008401c3aa6a1ac010807351ce31580210074aa1a62b004202c787594160084051f10ea82c010802bc205505802100e6c39c60b004200e59538c16008401d3287182c010803b48c6305802100c7c43a60b0042009e78748460084d5accea908c010803595d52118021006d33a2423004200da57448460084d3b8ce6908c010803715cd21180210047dc3ac03004200c79755806008401972e8b00c010803365cd60180214be1fa1ee6b2e8097c3c40dcd65d012d0fb0f39acba001e8fa12735974051d1ec24e6b2e8000c5f739cd65d00018bf06b9acba025b0fd0d73597404b61e202e6b2e809787e871cd65d000f47d0839acba004e8f610735974003d1fc1a86b2e8007e1f8350d65d000187ee6a1acba0003879cd43597400061eb9a86b2e8000e1d7350d65d000147900a1acba00029ba0b715974000536c16e2b2e800087e87cc565d00010fb0f98acba001e8fa1331597400051ec2662b2e8000e1d43cc565d00014dd0598acba00029b60b31597400070ea1a62b2e800087e870c565d00010fb0e18acba001e8fa1031597400051ec2062b2e805da3f845c165d00010fd0f982cba00021f61f305974003d1f42660b2e8000a3d84cc165d000f47909182cba00038750e30597400051fc2260b2e8007a3c844c165d00270fd0e182cba00021f61c305974003d1f42060b2e8000a3d840c165d0001c3a86182cba00029da0430597400053ac0860b2e8000e59300c165d000f53d09baac7a004aa76137558f400064eba6eab1e8000c5f759d563d01455b5013aac7a0002b66027558f404b52ec3ceab1e8097e1e749d563d0001c3ae93aac7a000396a027558f400072cc04eab1e8097e1c409d563d000193ae8baac7a000317e1d7558f404b62fba2eab1e8096e1e745d563d
  | 20 => 0x73c32e420842009e7855c841084013cb0ab90821080279e0d7210421004f2c1ae42084200d67535c84108401acaa6b9082108db69d0d7210421006d2a1ae420842009e4805c841084338eaecbac42108025de0d7588421004bac1aeb1084200d37435d62108401a6a86bac42109c359a097588421006b2c12eb10842a4c76625d62108401acc64bac4210803594c97588421006b2bacc51084200d6575d0a210846db4ce9a144210802d96144288421006b2ba8851084200bc58310a21084050fd0bbb242108021f6177648421004bac2eec9084200c7685dd921084018eb0bbb242108031dd4f76484210063aa9eec9084200cb743dd9210840196a87bb242109aad9a166248421005b2c2cc49084236da474d0921084013cd0f21242108da7921d4248421005b3c2a84908426ab6485509210846db48e8a1242109aad9a144248421005b2c28849084269bc683109210840178b0621242108025d6147048421355b342eec9084200b6585dd921084019cb0dbb2421080279e177648421006b342eec90842009e585dd92108401acb0bbb242108025961776484211b4f3426ec90842009e783dd921084013cb07bb2421080359d4f7648421006b2a9eec9084200da743dd92108401b4a87bb2421080279a0376484210067343eec9084200e6685dd92108401ccb0bbb2421080399d4f764842100732a9eec9084200ea743dd92108401d4a87bb242108da79a1f744842100572c34e89084200ae7865d121084016cf0aba242109aad92157448421355b3428e89084200b65851d1210846db4ce83a24210803695d0744842134de3418e89084200bc5831d121084013cd0fb2242108da7921e64484211b6d23a4c890842369e787591210846d3c90eb224210802d9e156448421355b242ac89084236da47459121084013cd0e32242109aad9a146448421005b2c28c89084269bc683191210840178b063224210802f8a006448421005f0c00c89084200ae5869c121084015cf0cb824210802d9e157048421355b242ae09084200ba7845c1210840174908b824210802f1e0d704842134de241ae0908426ab66851c121084016cb0a382421080279e147048421006b3428e090842009e5851c12108401acb0a38242108025961470484211b4f3420e090842009e7831c121084013cb06382421080359d4c7048421006b2a98e09084200da7431c12108401b4a86382421080279e1d21d8021004f243a433004200be08048660084018bee6a9cc010807171cd53980210064fb9a873004201c9c7350e6008401c3aa6a1cc01080a3e61e50980210163d3aca130042018f9878c26008401cb2a7184c010803a650e3098021004f243a42b004200d677548560084d5ac8ea90ac01080369dd12158021006d23a242b004200dc77348560084d3b88e690ac0108
  | 21 => 0x53dc564484018eaa7b8ac8908eb2dd0f71591210065aa1ee2b22423ac77615d4644840117f0eb20c8908028f215641912103e4f322e63224200c9d645cc64484759aec2b98c89081f2b19172d05210143f42ced20a420087d859da41484010ff0abb2829080a1f21576505210061e3aec8a0a4256cac64dc941484010ff0aba6c09080a1f21574d812100e2f39aa7b024200c5d7354f604840393ce6a1ec090803275cd43d81210070ea9a87b0242008fb8758060484010ff06ba8c09080a1fa1773181210043ec2ee6302420287f87d4c60484010fb0fa98c0908021fe1d53181210043ec3aa63024295c3e75d0c604840187aeba18c090a530f9d543181210061ebaa863024201c9e7350c604840193ae6a18c0908038754d431812100636bac423024201c5e7354f64084018bae6a9ec8108062fe1d43d902100e4f39a87b204200c9d7350f6408401c3aa6a1ec81080a1fa1671d90210043ec2ce3b20420087f855c364084050f90ab86c81080237e0d70d902100c6e41ae1b20420287e87dd564084010fb07baac8108023d20575590210043f438eab204200a5d831d56408405878eb2a2c81080a2f21d54590210043fc2ae6b20420287c855cd64084011e902b9ac8108023ee0173590210047c402e6b20420087e87d4d64084050f90fa9ac8108021fa1d53590210043e43aa6b204201c5e7354d64084018bae6a9ac8108030fdd743590214ae1e3ae86b2042018bc8750d640840187eeaa1ac810a530f1d543590210064fb9a86b204200e1d5350d640840156902a1ac8108031ddd471590210063a3a8e2b204236ce4721c5640840f87cc8ba8c8108022fe1d64190210061ebaac83204207c9e645cc640840193ac8b98c81081f2e99170190210065cb22e0320420087f855db41084050f90abb682108025de1576d0421004bbc2ae5a084200975859c341084013cb05386821080a1fa1776904210043ec2eed208420096d859ca410840f87cc8ba882108030f5d5641042103e4f322e62084200c9d645cc410846db2e82b988210803655cd41104210063ba9aec2084200c75535d8410846d96e86bb082108032d50d76104211b673a12ec2084236ce4425d8410846da6cc8ba882108025de0d7510421004bac1aea2084236d37435d44108401a6a86ba8821080359a097510421006b2c12ea208423ac76625d4410846dace84ba882108db591097510421006b3192ea2084200d65325d4410846da6880ba882108034d5d56410421006ab42ae62084200d55855cc410846db2d08b9882109cf6561173104211b6cb322e62084200d95645cc4108401b8d04b9882108037160973104211d66b312e62084200dc6525cc4108401b8aa4b9882108db71d0973104211b6e2212e62084236d94405cc41084751ef0cb90821080279e1972104211d6
  | 22 => 0x38ec9108062f21d43592210064fb9a86b244200e1d5350d64884050fd0bb82c9108021f617705922100c6f41ee0b2442008dd83dc1648846d8ecc2ba8c9108021f61e65192210062f39cca324420087f8759464884018bce6b28c9108022fe1d64192210062f32ae63244200c5d655cc648840f93cc8b98c9108032759173192211b66b30ae63244200c75659c742884018eacab8e85108038b59564d0a211b477c32e3a14420096f855c742884012db0b38685108021f61b7550a214e43f43acaa1442a587c8759542884018eccbb8a85108031d5977150a210063b328e2a144200c75651c5428846d96cc838a85108032d5907150a211ec3fc32ea214421987f8759442884018bce6b288510803179957310a210062eb2ae62144256d8f425cc4288401c5acaa108510803635cd4210a21414b7c32ea214420096f835d442884012db06ba8851095b4bd0d7510a2100696a1aea2144256d2c405d442884012db0eb28851080353a157310a21006a6c2ae62144200d4e655cc4288401a9acab98851095b63a117310a213fec6c22e62144256d8c405cc42884012db0b394831087a1f61b75506210cc3e43acaa0c4200c6e65dc941884018dacbb9283108031b994725062100636b28e4a0c420087f865d4418846d8ecc2ba883108021fe1d65106210062f39aca20c4200c5e655cc41884018bacab98831081f2799173106210064eb22e620c4236cd6615cc41884330ff0eb2e43108031d99576c86210063b3aaed90c4200c75765d721884018eaecb2e43109fa9de1d65c86210053ac3acb90c4200a778359721884014eb06b2e43108038dd0d65c86210071aa1acb90c4270c767259721884018bce732ec110803179cd65d82210061f32ce9b044200c3d659d3608840187ccaba6c1108030f59574d82210062f32ae7b044200c5d655cf608840193ee6a1cc110807271cd43982210070ea9a87304420287e85dd160884010fb0bba2c11080317dcd535822100e2e39aa6b044200c9f7350d6088403938e6a1ac1108038754d435822100746a1a64b04420287f865d460884010fb0f328c1108021fe1d65182210047dc3ac03044200c3d75d53644840153b062a6c8908062fe1d43d912100e4f39a87b224200c9d7350f6448401c3aa6a1ec8908021fe1570d91210143e42ae1b2242008df835c364484031b906b86c8908021f60f75591210045fc22eab2242008f7815d56448401878ebba2c8908021fe1573591210143e42ae6b2242008f7815cd64484011f700b9ac8908023e20173591210043f43ea6b22420287c87d4d64484010fd0ea9ac8908021f21d53591210061fbae86b224295c3c75d0d64484031790ea1ac8908030fdd543591214a61e3aa86b224200c9f7350d6448401c3aa6a1ac8908031ddd771591210063a3aee2b224200c77
  | 23 => 0x9804100e2e39aa73008200c9f7350e6010403938e6a1cc0208038754d43980410043fc2ae5300820287c855ca60104011bf06b94c0208063720d72980410062fb9aa6b008201c5c7354d601040193ee6a1ac020807271cd43580410070ea9a86b008200ab88050d60104050fd0a392c0208021f61472580410043fc32e6b2c420087e87d8d65884330fd0f31acb108028fa1263596210051ec24c6b2c4200c5f7398d65884050fd0eb1acb1080317dcd63596210043f438c6b2c4200a3e8418d658840147b0831acb10a570fddb43596214a61fbb286b2c4200d1d7350d6588401c3cc6a1acb108038758d43596210cd37c32e4b2c4200b2c845c96588401e1a86992cb108030fdd2745962100537c12e8b2c4282a6c825d165884014bd063a2cb108029760c74596210043ec3ce6b2c4200a3e849cd658840147b0939acb1080317dce735962154d37414e6b2c4200a6d829cd65884018bf06b9acb108021fa1c73596210051f420e6b2c4200a3d841cd658840187ee7a1acb108030f5cf43596210043f43c86b2c420087d8790d658855147b0921acb10803175ce43596210062eb9a86b2c4200e1f8350d658840187ee6a1acb10803879cd43596210061eb9a86b2c4200e1d7350d658840183ae6a1acb108021fa1c43596210043ec3886b2c42a7a3e8410d658840147f08b92cb108028f21172596215253bc0ae4b2c420087e87cc965884010fb0f992cb108028fa1332596210051ec2664b2c4200e1d43cc965884014ed03992cb108029d60732596210070ea1a64b2c4200a77814c965884014e902992cb108661fa1c32596210043ec3864b2c4200a3e840c9658840147b08192cb10a929ba0a71596210cc3f43e62b2c420087d87cc5658840147d0998acb108028f61331596210070ea1e62b2c4200a6e82cc565884014db0598acb108038750d31596210043f43862b2c420087d870c5658840147d0818acb108028f61031596210051f426e0b2c4200a3d84dc165884014bd07b82cb108029760f70596210063db84e0b2c4200a6f825c1658854d4d904b82cb108021fa1f30596210043ec3e60b2c4200a3e84cc1658840147b09982cb10803175ce30596210070ea1c60b2c420087e870c165884010fb0e182cb108028fa1030596210051ec2060b2c4200c5d730c16588401c3a86182cb108029ba08305962100536c1060b2c4200a76810c165884014eb02182cb108021fe0d75d92210143f42ee7b24420087d85dcf64884011f501b9ec9108023e60373d92210143fc3ea7b24420087d87d4f64884010ff0ea9ec9108021f61d53d92214ae1f3ae87b244200c3d75d0f648840317f0ea1ec910a530f9d543d92210061ebaa87b244201c9e7350f648840193ae6a1ec9108038754d43d92210063b3ace3b244200c75759c764884019cae5
  | 24 => 0x88207a3e84dc1651043747b09b82ca2080297a0f70594410052ec1ee0b288200c7b709c165104c747f08b82ca2081e8f21170594410043f43e60b28820087d87cc1651040f47d09982ca208028f613305944103d1e42460b288200c5d738c16510401c3a87182ca208028fe11305944103d1e42260b28820087e870c165104010fb0e182ca2081e8fa1030594410051ec2060b288200c5d730c16510401c3a86182ca208029ba08305944100536c1060b288200a76810c165104014eb02182ca2081ea7a137558c410d54ec26eab188200c9d74dd563104018beeb3aac620a5a9761e7558c414bf0f3a4eab188200e1d749d5631052fc3e833aac620a5f871027558c410064eba2eab188200c5f875d5631052d8bee8baac620a5b879d17558c414b62eba2eab188200e1d745d5631040183ae8baac620a5b87d057558c414b70e202eab188297a5e851d5631040f53d083aac62086aa76107558c410052f42ee4b188200a5d85dc9631040f53d09b92c62086aa76137258c410064eba6e4b188200ad681dc963104355ab03b92c620aaab5e057258c410056a40ae4b188200a5e851c963104014bb0a392c62081ea7a107258c410d54ec20e4b188200ad681d4963104015ab03a92c620802a7e115258c4103d4e422a4b188200ad78154963104015a902a92c620a2aa76127158c4100567416a2b188200acd82d45631040f53d0928ac620802a76125158c4103d4f420a2b188200a9d8414563104014bd0bb82c620802976177058c4103d4f426e0b18821aa9d84dc163104018baeb382c62081ea72127058c4130d4fc22e0b188207a9c845c163104014bd0a382c620802976147058c410062eba8e0b188207a9e841c1631043553b08382c620803275d07058c4100567410e0b188200acd821c163104015ad02382c62086ab56047058c410046f43ea0b1882008dd87d41631040f53d09a82c620802a76135058c410072da84a0b188200a9f84541631040f53908a82c620807279cd43988410064eb9a873108200e1d5350e62104010ff0ab84c42080a1f21570988410046fc1ae131082018dc835c2621040f17908baac420807279cd43588410064eb9a86b108200e1d5350d62104050fd0a382c4208021f61470588410061e3aeeca088200c3f85dd941104018790bbb282208022fe0f76504410045ec1eeca088200c3f53dd9411040187aa7bb282208032d94776504410065aa8eeca088200c3f76dd5411040193d0eb1a8220a2b2761d63504410070f42ac6a088200e1d8558d4110401c3eeab1a8220803871d563504414574bc0ac6a088287e948158d411040f93ee2b1a822081fa5dc5635044100657bb6e4a088200e8d63dc9411040195eec39282208034b1d4725044100746b18e4a088236da7711c9411040193ac6382822080317dcd53
  | 25 => 0x40155b08380c4a0802b3a0c701894100566c18e03128236ae5811c0625046d55d09a80c4a0802ab61350189410056741ea03128200acd83d406250401cd6a1280c4a0802b9a04501894100572c08a03128200a6e85cc062504014db0b980c4a08daaba13301894100556c26603128200e4d538c06250401d1a87180c4a08023ba1c301894100476c38603128200a6e850c062504014db0a180c4a08daaba10301894100556c20603128200e4d530c06250401d1a86180c4a0802b9a04301894100572c086031282368f6869c642504019c8c538c84a08021fa1f65509410063bb2ee2a128200c7465dc542504018eeca38a84a08031d194715094100673b10e2a12828de3761d964150401c58ca31482a0807179cd53d81410062eb9aa7b028201c9e7350f605040193ae6a1ec0a08038754d43d81410143f42ce5b02820087d859cb605040157308186c0a08039654c30d81410074ca1861b028200af1810c360504018decb394c0a08031b196729814100637b2ae53028200c6c655ca60504018dcebb14c0a08031b5d76298141006373a8c53028200c6d7518a60504050fd0dbaac0a0a361f21b75581410043f43ecab028200c5c73d9560504010fd0e32ac0a0803171cc65581410062fb2ee6b028200c5c65dcd60504018decbb92c0a08031b197725814100637b28e4b028200c6c651c960504011dd0fb12c0a08031bdd76258141006363aec4b028200ccf73d896050401998e7b12c0a08023ba1c625814100637ba8c4b028200c6c75189605040199ee6312c0a0803331cc62581410047dc3ac03028200ad883580605040193ee6a18c0a08038754d43181410043fc2ae4302820287c855c8605040157309980c0a08039654c30181410074ca18603028297c3f43dcd651052f87881b9aca20a5a1f61e735944103d1f424e6b2882aea3d849cd65104018bee739aca2080317e0d73594414b61fa1ae6b288296c3c405cd651052f0fd0e39aca2081e8fa1073594410dd1ec20e6b288207a3f8350d651040fc3f06a1aca208030fdcd43594410070f39a86b288200c3d7350d6510401c3ae6a1aca208028f20143594410053b40ee4b28821ba7581dc9651055b47f08b92ca2081e8f21172594415653bc0ae4b288200a74815c965104010fd0f992ca208021f61f325944103d1f42664b288200a3d84cc96510401c3a87992ca208029da0732594410053ac0e64b288200e1d434c965104014ef02992ca208029d20532594410043f43864b28820087d870c9651040f47d08192ca208028f610325944155d1ec24e2b28821b87e87cc565104010fb0f98aca2081e8fa1331594410051ec2662b288200e1d43cc565104014dd0598aca208029b60b31594410070ea1a62b28820087e870c565104010fb0e18aca2081e8fa1031594410051ec2062b2
  | 26 => 0x21fa1c655894100477c3ac43128200a6f8558862504014d90ab10c4a0807179cd53189410062eb9aa63128201c9e7350c625040193ae6a18c4a08038754d431894100572c0ea431282028ed87948625040155b08290c4a08029ba17321894100536c2e643128200aad84cc86250401d1a87990c4a0802b9607321894100c76c3c643128200e8d434c862504014dd0a190c4a08029b614321894100556c2064312820087f855c062504050f90ab80c4a080237e0d701894100c6e41ae03128200c6e76d9462504014db07b28c4a0acb99d0765189415973220eca31282008ed8799462504011df0eb28c4a08031b9d8651894100536c18ca31282b1e67411946250563cc882328c4a08023b61e63189410053742cc63128200a6d8598c62504011df0eb18c4a08029be1563189410053642ac63128200aeb8058c62504015d100b18c4a08029ba14631894100536c28c63128200a6e86d4c62504014d90da98c4a08029ba19531894100536432a63128200e2f65d0c6250401c58cba18c4a08dba9d87431894100717b2a863128200e2c6550c6250401d1ec6a18c4a0803c354d4318941005d240a863128200ae6819d462504015cb033a8c4a08daaba10751894100556c20ea3128200ace831d4625040159b063a8c4a08db8b95354189410057340ea83128200ae581d5062504015cf02aa0c4a0802b920554189410053742ce63128200a6d859cc625046d55d09398c4a0802ab61273189410057340ce63128200ae5819cc62504014dd0a398c4a08029b61473189411b557420e63128200aad841cc6250561cce83a98c4a0ac39910753189411b557424a63128200aad8494c6250401c9ea7298c4a080393e0d53189410072739aa63128200e4d7354c625055fcce82a98c4a0abf9910553189411b557420a63128200aad8414c6250401c5ea7a18c4a08038b54f43189410053742c863128200a6d8590c6250401c9aa7218c4a0802b9a06431894100572c0c863128200e4d5350c62504015cf02a18c4a0802b920543189411b753a0a863128236e8f8350c6250401d1ce6a18c4a0803a35cd431894100717a9a863128200e8e5350c6250401c5aa6a18c4a0803a354d431894100706a9a863128200ea78150c6250401d4902a18c4a08da3ba1f511894100476c3ea23128200e6751944625040155f08a88c4a08daab211511894100537c2a823128200a6c85504625046d1dd0f988c4a08023b61f31189410053742e623128200a6d85cc4625046d55d09988c4a0802ab613311894100746a1e623128200e8d434c462504014dd0a188c4a08029b61431189411b557420623128200aad840c462504014df0ab80c4a08029b215701894100557c22e03128200acf835c0625040159906b80c4a0802b9e05701894100537428e03128200a6d851c06250
  | 27 => 0xfc1ae1b2a8200a5c835c365504018f2e0386caa08021fa1f30d95410043ec3e61b2a828da3e84cc3655040147b09986caa080317dce30d95410070ea1c61b2a820087e870c365504010fb0e186caa0a368fa1030d95410051ec2061b2a8200c5f730c36550401c3a86186caa08029ba0830d954100536c1061b2a8200a76810c365504014eb02186caa080327dcd43d89410070ea9a87b1282028ef8754b62504014dd0b996c4a08029b61732d894100556c2665b128200e8d43ccb62504031df0e996c4a0803a350d32d89410053742865b128200a6d850cb625040155b08196c4a080a1fa1670d89410043ec2ce1b128200a6d83d9762504014db0632ec4a08029ba1663d894100536c2cc7b128200a6f8558f62504014d90ab1ec4a0802bae0163d894100574402c7b128200a6e8518f62504014db0a31ec4a08029ba1b53d894100536436a7b128200a6e8654f62504014d90ca9ec4a08038bd9743d89410071632e87b128200e2f6550f6250401c58caa1ec4a0803a3d8d43d89410074631a87b128200f0d5350f625040174902a1ec4a0802b9a0475d89412b572c08ebb128200a6e85dd362504014db0bba6c4a095b8b95354d89410053742ce7b128200a6d859cf62504ad55d0939ec4a0802ab61273d894100537428e7b128200a6d851cf62504ad55d0839ec4a0802ab61073d894100573408e7b128256ae5811cf62504ad55d0929ec4a0802ab61253d894100727a9ca7b128200e4f8354f62504ad55d0829ec4a0802ab61053d894100717a9e87b128200e2d53d0f62504014dd0b21ec4a08029b61643d894100726a9c87b128200e4d5350f62504add1886a1ec4a095ba3e0d43d894100747b9a87b128200e8c7350f6250401c5ea6a1ec4a0803a394d43d894100716a9a87b128200e8d5350f6250401c1aa6a1ec4a08029be1571d89410053642ae3b1282568ee87d4762504011db0fa8ec4a095a3ba1f31d894100476c3e63b128200a6e85cc762504014db0b98ec4a095aaba1331d894100556c2663b128200e8d43cc76250401d1a8698ec4a08029ba1431d894100536c2863b128256aae840c7625040155b0818ec4a08029ba1770d894100536c2ee1b128200aad84dc3625040159d07b86c4a0802b360f70d89412b572c0ee1b128200a6e859c362504014db0b386c4a095aaba1350d894100556c26a1b128200ace83d43625040159b07a86c4a08039ad4250d89410053742e61b128200a6d85cc362504ad55d09986c4a0802ab61330d894100726a9c61b128200e8d438c362504011dd0e186c4a08023b61c30d89410053742861b128200a6d850c362504ad55d08186c4a0802ab61030d894100726a9861b128200e8d430c362504015cd02186c4a0802b960430d8941006373aec53128200c6d75d8a62504010fd0fb2ac4a080
  | 28 => 0x354e60d052987ceaa1cc1a08030f5d543983410064eb9a873068200e1d5350e60d04018bee6a9ac1a0807171cd53583410064fb9a86b068201c9c7350d60d0401c3aa6a1ac1a080a1fa1472583410043ec28e4b06820087f835d662904050fd0bb9cc5208021f6177398a410143fc3ea7314820087d87d4e62904010ff0ea9cc5208021f61d5398a414ae1f3ae873148200c3d75d0e629052987ceaa1cc5208030f5d54398a4100e4f39a873148200c9d7350e6290401c3aa6a1cc520807279cd4358a410064eb9a86b148200e1d5350d62904050fd0a382c5208021f6147058a4100477c3ac4314823a8f7865c6429040193ee6a1cc120807271cd43982410070ea9a87304820087f855ca60904050f90ab94c1208021f60f75582410046fc1aeab0482018dc835d560904018beebb9ac120803171d773582410062fc2ee6b048200c5c85dcd609040193f09b9ac1208032721373582410043fc2ae6b04820287c855cd60904018beea39ac120803171d473582410043f43ea6b04820287c87d4d60904018bee7a9ac120807171cf53582410043f43aa6b04820087c8754d60904018bee6a9ac120807171cd53582410061fbae86b048295c3c75d0d609040193ee7a1ac1208030fdd543582414a61e3aa86b048200c9f7350d6090403938e6a1ac1208038754d43582410047dc3ac0304820087e86dcf65504050ff0fb1ecaa0803175cf63d95410043ec3cc7b2a8200a6e8298f65504014db0531ecaa08021fe1d63d954100537c12c7b2a8200a6c8258f65504014f700b1ecaa08029e20163d95410f43ec38c7b2a8200c5d7318f655053787ceda1ecaa0a530f9d943d95410068fb9a87b2a8200e1f6350f6550401c38c6a1ecaa0802cd20543d95414453b40ee9b2a820087d879cf655051b47d0939ecaa08028f61273d95410062fc1ae7b2a820087e871cf655051b47d0839ecaa08028f61073d95410062eb98e7b2a8200c3f73d0f655040187ae7a1ecaa08021fa1e43d95410043ec3c87b2a82b3a3d8490f65504018bee721ecaa080317dcd43d954146f0e21a87b2a828da3f8350f655051bc3f06a1ecaa08030fdcd43d95410070fb9a87b2a8200c1f7350f655040187ae6a1ecaa0803871cd43d95410053bc0ae5b2a821ea74815cb65504010fd0f996caa08021f61f32d954146d1f42665b2a8200a3d84ccb6550401c3a87996caa08029da0732d95410053ac0e65b2a8200e1d434cb65504010fd0e196caa08021f61c32d954146d1f42065b2a8200a3d840cb655051b0fd0f98ecaa08021f61f31d954146d1f42663b2a8200a3d84cc76550401c3a8798ecaa08029ba0b31d954100536c1663b2a8200e1d434c765504010fd0e18ecaa087a1f61c31d954146d1f42063b2a8200a3d840c7655040147f08b86caa0a368f21170d95410052
  | 29 => 0x10003c023001801400000000a800000200000c800000c0030038078002006010800403c022001801001001a001800001c0000000014002002005000800a00301280000100010048000004004002003001c008004804800000701880100060000018000006001005006400200300880600340100068044000007001000000800000000340040240010010006000000800400400e00380400200020038004000015000000001601000100000220030020028014003000802c000000007000001400200a8140000004004001804e0000010014006002000000000801c00000000000020140058030001002000004c00000e00ec0020240030058000006000000801a0020000064000001000000000000000200b001c011001001c014007004001000801100000280120010008010056000004800400200000880380320080090000000034002000800a00000280140240020008014000054001001c01a00f000802800e002005000801c00100100040520470048028000005000800000001300c00140020000018000014003000004000000100380840000000038004000002005805c0060030040000014022006800000a000004800c014003001800001c02400280e000600200e001c000001003002803600400180d800000300600080160070008040044000003801000000e001800409c00b00600000040050060000000005002000000600300280000060460040050020007020802800c0100010004020003004000000e00000580040000000008010000000001006800600001180bc0000020040028008005003800002400900600000200000048000002053000000001800500580240000030040004016001004800801000a00f800001c001000000000000c004007401400a001000c07c003001001002a000003000001801a001007400c009000000400401c00e8004006005003806c002003001800400a008000806800200400b800001601c00b802002403f000000c0000060000040010039003010805c002004007279cd4398b410064eb9a873168200e1d5350e62d040f1db0f294c5a08063b61e3298b4100746a1a65316820087f855c262d04050f90ab84c5a080237e0d7098b4100c6e41ae1316820287e87dd562d04010fb07baac5a0a730fd0f7558b410043fc2ae6b16820287c855cd62d04010fd0fa9ac5a080a1f21f5358b410043f43aa6b16820087c8754d62d040187eeaa1ac5a0a530f1d54358b410064fb9a86b168200e1d5350d62d04058d8eb292c5a081e3b21d5258b4100c7643a64b168200e8d434c962d04014bb073acc1a080a1fe1d75983410043fc1aeb3068268c3f435d660d04050fd0bb9cc1a08021f61773983410143fc3ea7306820087d87d4e60d04010ff0ea9cc1a08021f61d53983410062fb9aa73068201c5c7
  | 30 => 0x300a0000002003001000801200b00400040000020040000002001000003801200100a0000000001004000c00a01802e800c06c00500e00000040020008000014001001002802c001000809000e000000003c004024000002c000013000000402a0050000004024003002000800000900200000000010020004002019001000402c01000a8054002007002801001c00000081c40020070008000000005001000005001c0000030006043003800c00200a000000407202000000100060000028020004000001806800c00300e802002800d006800801c0000000000022015004800000e00802b004800600c00180b401000300c80100020000000014000001001001c0000010040004002000003805001000000f80ec00002800100180040170010000008000000000800a000000803002000200180140240000028018014001008001001202f002000c01800500180000040070050010008000002822003200e008000000600400180000080000040010000001044008407603000080bc00800100000340000000028024000000006812c000007002800000801b002001c00c005005800800a00600080040000060018000002001003800c00a04d00000080020260100038022009003802003200302380580100200000004010007005002402400000680080020070070018018002000003801000e000006800000200280b0008001007800000800500880100080080020004000000005800c00005c006800400000b000802400c003003003c00a01100000680240000060000012006000801c02000c001800405800400f80d8000005002001c00000200180000600060018014002000000000000a00a006801c0220170050000006000000011001c00701f800000208d00000a800e000016800400800a000000000000100b003400200600b005404c00b005001000e002000800007c00d00000340520140010004000009019805800200800e00f8000001003800804e000000000000000a0008044000004003000c002003000000c0060b3001801c00000500080080000030088000000013005804000c0040000040010000002011001e004000800000e00000c00140520100008018000008005800c020000000000c008016012803c04e0000000030000001033804402e0050080024004000002004800001b000000c0400030078030000000007002800001f014000000006100b80000280110000028000007010001400000100380000000000008024004002002803800000000300a40060000000008000006009800000401a00000040020040000148006000000008801600c0038000002007000001c01c002017007000200a000000400c00300200180a4001006800403e00200b000800003d0000004004007002800c04200000080080580000000
  | 31 => 0x22215c421209c49f000003ecab465000048c18318a03b8a1ad0508c327154c0004b2913968613a000372d9a80000be000014c3e80a08000c960b5b629b41cbad3f736acbd6e68e70b31e1800000058da1cc08d40a5022780a9e72237fa0fda3c6546a0bbf8bfe0586f502ec0a6a1539432343720cb0211c68f5aded4370ec4ef468a0d3274dae2f5069516bd92604822d2a8064a5251851fd97ac0c809b2260240f6f28128209003aa52a0b181bee7a6210bf74568e83891dec032d730000000c18a103cd9238000308fbb8fb0d4e5fd2ea8000ff63c5504be7c0000002f6ac2513a000000205fee8cc04758d58000b2b00025c0ad800030aa4e400080b74c0000e322ff00027a5e9a0000000594000fc43d98000000ad11e32b89e4055412a2fe9a044af35e1bc873c5d37d9a2b1e041ba5903a21a92d950b9a605ce0e374f83ed1ab48917ec049d34a1f265a070ced62b8438381dab68119bf8c58000206800186831a659000316c3f634b5c01a6dbe00cd3b011d00000001d6136c0004e670500018f8000228044ca3703728800000007670000000000c7500008295410a6f87000087400000000009128155390240000cf54ad3dac000a975ae31f80003e744f9117a9e00004d87a1582aa30000e09e4221a4cea8b5f7896647d973de3cb475480d52c1e66600000000004ee419281600a00500840000010040000010005000000808403200681100040000030024010000000000c002009000813c01c00d000001000000000000000180070090004002027000800007c000004000000000e009000002600a00580a8008004003004800e003001000000000000100000060080000034004001000000001800101c800001000201b800c00000400000040080080038030020009000001802c00b006001c00000c00f001800c009000002000000100b000c0160010000004000001000800804800200b8010002013004001002c00800780100140010000064004023000801405001d00080c400000000080000000020018000002001000803400c00f0030010042001000000001a00100200140000030000048006000000000c0060000008034000000002800800c00e0000068004000001015800400101200040020060088014002002001004000000c004003c002000004007800400d005800000201600080440060010098108026003001804001400000200300120000010000028015001800000000a0020000078007004001800801e001800401c002002802803800e002000000a00d00e00bc00000e003002c000006005001c000003000002000002b004806000600100300180000bd000001c0080010028000004014000800402c00500a000400e005001003403400100080a400800001b00380020170070030004000002801400e00102c800c000
  | 32 => 0xcb70000099150504e074000000016e0e28544704f723c7762898da880004c305a8f2679661e11246d0e110001ad80006752ca876074643700024b8ad2de906880002e09c400000009400006fe23f53e24d74203ba13902b50a82171d380000c59100d9a4a10000001e5ee827010001c26a776868521f38000000053422e23b0000001faa000610000000000046a3404c9e7aa19896d11c61de2f7000066a7ac6a700005de3270000c642fe56100021486cee3800025b8ea60005ac3595522dcf6a8800000067e0002ae8000e2a0003218b4a02e7ee8c6c0005c26bf312970481b330b1c5f94000000348d3122187ad8f8c76600025c8000834a6d4960ed5b04b6c00a86ed60491c2d4a29cce8b78000000118c0b0a3100f1c820001d72940868daf51fa609428f9a588af8dc48c6e05527b8000e5c0eb9d6d7446780a78001f1633b5fab681bea8b83c6860550814fd9bc8e4b382ad00004e5b200003b82795ef85340879bd4000a7a62880000008f2336086f888b4a0699524b74aac0f01401d0258376b96d453a0a71448f6c9206f30000e6846c6147378614c1ceea50f3439278cee0000000a4c20b74f80014d04944bc0001588f005768001d0039c09400016f40bc1cbb06c9c46426daa75ab8c883267349c00080e7d7800050ccdf56500000002f30d218443629586bf9300c100007ad1ff2644b6a6ba00013446620000c1d7e4a990002c4000000000014289fc000000121468a00018a8ad00000005bd9094b2ebe7000339c7982b1c6080005eb000132050c00088b51ba028d3ead64f781718c00001dd90480003b9726a46c5345e100000000a810b6450000000000000088c1260007d23d6400040302fb1c000038000000010a20003b6be800009cb00036ac4ae4ec00004f9f2a85a22b0000000e740b107580005272a310755c29ea62a89645187fc2d61309d7c1c76ebb0f9bfa2e442398284ba6400933c6d962cb93208c15d702b23ff364df207115ae9a70d624df4e7a89016fb457e2af1d5604a636c2a73b5c4593a432ede62f26653066c5604714c91f8dd1285b0ba029ef288ae5f540d504c57511eadb42329a419088540e7eba19737546862d21ca83910908a12ee9b51e8aed147e221de562fd41a00019326ea00018840ec0006e49bac2fabb804680013b899b0003c70000ed60000e0d2a2b220000a88000000000005cc76dd403900000007cd0003931e3400011a9ea49a04812b68000d00eab5e002442782215ab21a1a2e5891532f040005a61ccbd99e8e00013a8000e1200079b86dc000ecd00000014ba0007efaa54b90b7c70a08b15b20de00035a8bd2a06000151ce8cc943fefa5502675a39b0fc400003366080000ea000399bb1d1840004658568d061ce37babf4028f7338580000000000000001566f6d0000000000000
  | 33 => 0x5f657260782491b5b7e05e87c042055131f951121800044205700000006b58000ea056a7deae9033e9404da85f8a9813d0000000b02268577a57cb9a33c7240000f7e70a0000000da2d7c00011ac5e21c9689b105db400040b000000000000035e958c0000c31078000abe000399598aec9000098834ebc36cf2b794c10000002e0ec587357aab65973c351d54acf20ce34a00000013badca00031fd4685a12ae0f50a5a00006480000008f064c09600008d300033685c0b7000012f07dad72252038c968cb257b9d2800077f0003cc8452000730828d9cc0002368000fba4530001f58790b604469369200000398178977194a6ba8f0921ee6e1df9769678eff38f07954c2acb1f2245c04ad7b42e9b64800222000298169cac5160a7ddc306c83248001712a9a573aba94fa32f4bcbeb10eeef50e9a33ddf211003e22d1ef0fbf215a1194f02b3291039c71661b3443f5c3d6a9b2039da0280d4b4ba1cc55aafdc05d07980000e8e348370d2adac7112e98f6af5c29d0e25dce1544ff159489eb82807800000029e0f88014afaf855d8dbe0fa61310000f5549049806780016701a15842e542bad680a4a2b48fe0000249234258e52253aa50d026366aa3f1c000d1d00001f545e9ff2719934f4c8207c1000010e0007782d31d168a800001bcf6ec2f10b40003e6b590000b69752c770003e206a26120cab75821084105a80009fea572340df0b7e53342a1661ba04ea7df00001d253b472885cd962a05828ed09a492d2cd83ccb3e02d010236982c2af5a7eb7c82ec1d7e181cb2ce0c708f8d047be18a1fa2f850a67430acdcf51aabd929f3024506000337af704628a61fd80009ca0000000001e1265d0003689ee01150f3a5ad138fd65dc93f40005050002e11308201930000000026155934200000004e10000916f125818000150c4510080351b25e45beb97cac0b2422b8a2cca0946519249c5acf7f1c42788ac894e00018f1bbab1c552a165ac654b00020ec0dc4210000e6c6880002c73b89c7200076ea7f4e886353fe8000c0413b6b819a012d9ce75200003100002123f488e64290000001500d5200000019f84f67393f6d3660001e9b7dd4d2220298b2b929eb674faabb874828d66f0ba1eec6ac00025c98147fa4ba93c469c89377e9540bae34240926e49826bb056be4978400057a24ff1d8f86288a6d86c0b6b491b6d80aed3a6c2a0f41a8b1a3c127859d08b64e81c0ca7a0262089a751ac0b68970f6408272544833a5392a980f2111f3a89fc45f2520f2a5176310f04d847915cf994477493b097a269e985c768224e00601b00889871f183de38c0001f4cb35f31a764000fb51229229a562a157dab31466c5d78ab1e89ea10a40e0cd8722a5fddb8900c468074a63e3858a44200022c400008c00000005f4d57341350
  | 34 => 0xa9f444e92721c21676ed4dce000063ab3b9868ab800034954b124dc6627271e933cb322784ca1641a1800078a16f9310f51678903047e45f000084582858413493dc2da3cc83d000011200067a0000cd2cd644da10ceb821f7118008116c6d5ef0205d6eb4f29200009747c01ad07b1eac14e440000000010008a1674000cea6e880003645ae2237b78d220002198688fbc9c300000017d651d00014657a400067c979983004c2430001146603059080b252921318123d37ece450c8a2808819e3383e1044c3f82112da46e69076972f6d2f680d71f2c9429d65540824681722ce12808a916e6a070917a98f66aa0001050ae8b86119efb35ccb9b056179466ea5a5c270d03981597450b0813a0bf4310d4880805675aad891864d4082c9fcadc2532641564a70eee6519c18002f3661087d0108ab14529d5143e7847af0ddca42e0f785955cb7ad5300000000001d14adb14c00043f7220000bc66c00000fc000024f66914b8b86219000000000000000034dc204edf48884780c5d5c6111f051a2c8f7ab8000fdc4965e49364aa4ba76020380000d9a6e2b628eae00041e15f861824828aba6c000d312ef35081cbf620ea000000024c555a5641aa0000001879376bc54941c80ac66281bd80000002e10003ac5c4c0007851df5c362c80debd904fa000068058c330930135b2b1cccb9171918dcd089350b38fa4ec218e1e7a24834af3c218985c000c82626db9c7a2ad419eb18a00022e5ef80003b6b6474283b4e1a9bd685870173f4aa125aabc000f96180b3fc0000002940001f4abbc26f3cd4089787059c30d21200053b76c9f9a38c4211d3d8c2a4b1e481983b847925b8ff128e375738ab00000a07143f211668b92414a86973a67a1a9c090562676317b62445f2ba4ef00000004f81129155a662791eeb0999c66891b607f51766b700039ac000ef800014ad77e8d20270001044bb652521d8e0400057b00ed8a065a00032d80000004999e8dcb40004cb000095a000258b4a52b89427b90f174e8e512320368bf00033c2b40cc560000002001d60000038beec000ec660600013c60001c219fd02915f6e3b01490853569a0ca0000bcf0000000c70d390b90220a9002217280019fc06400022ad7f883a0002d259445733cc8eb5abe0006d211dfd4a6f636192d8208d9c64b8001b4c00000024409a200019c008463c93110226f8d0a10e44b1cc8d8825200001a43f038761c0001db8def3f6212c0007f1000000167a73c36e9dc4d2ceb900037a18328ce0002954de8f5465c3ce098af53336b0e800045400000002b0d840003d818cc469140afaee92220d7f10e1cf63533ea04904184bf2ad8ec81d63ee0a31979bf2cc32843455616c012229254fd6858168b1908e0b851288000d7a825000372000081d5b93a400189fa1b72ffb57620
  | 35 => 0xba68c87bcec4b515948001664a6f36b80000000000f68250d24e036ccb0ac1889696d1a664af60000651528d20ed9081a80ce5aa5e551fa650300000a3800065832a0c81aa00005b07420e85144a8b0e82a7d3140000cb0fa953a000022a65d84e00026a8000000cbc4d30000000b3960331a1f56c1173abf44000ca929b3e618a19010278000eb263e2fd00005b200000027d00008c0789808cdc40001fe808ac9c24e3d0361c00088200001a00000005878330e3a3592ab25a0156c9e0000001aaa47c00000013382284778001bb272c7f00001e84eb607b5ec47786a50a994607f296c04d18c5e685097cdac55dd6b46788a9e545c213b6db6f1caa0000001c715a63c005a6334d30f48000261c88eacf00e91a91741876943c5cbf22c758c279cbbe00007a8e7526c0004a910c800001b0000f4fde8fa81559acdbbcb1e04fb3f4d0c0001238001a1445c7539d35d689c4ece800098cec10002f40dc25120193af177c0b164009297bd5c45f9ad785aa00000015dc66000e5e60001d24e9a13800017060006d51a3560054500000019ee17b520863d1d2dfb1e7148c5cc000393000000074e2e62de53b4a7e287990d8ce1b47d89bb0e5e44c382bb4089ae42395b838f94b503f1258d852f521098001c408f65f30df515eceb3f3a9458ca667439318fb987f53d38e3854800075682811482ec2f7897de54d486010bb57dfee97972be8000ef643fb31c840c2e524a62d7d8e540b200000f26e86480da51babfb447bf185f8bedfd6986034071403694a564c6ce296187cf568db76516c46046d24c98fcdcfcf1004328d97c8c2c5610a08e7c28807a3914000d325228001240e0c0002d69f22585717960808e92208615ac3c2b858e125c41e21f55e511609469190740b346b0ef23ba23a813303f2ac0aed7e2deb3e70bb89f6ce047087f9f32ab900037df922fc075415e511448755e11d991ceac03f00f9f2684e49eb5f5a2c0004a2a181654b120ab2d11824a0270c8675a28af81b180018e8be559eef180004dd4d5030136262e0001a880000e67e40e142705bc09f8140cc09af0bd2730714ad73c0bf4c000bbf8003e50e2a0000000000efc0003241e84638cad3bca0b9bf004a000185800040534d20b5004ca706703743320003c70f9583480873e0d4a8029e862300007deae42493d292f4886781baf49365fb1e80cf81d8c9b62c8010bfc9ba000000133ca5811b8b400000000002a707ee6446848c44d4800037db0912aaa8a574976c1680730003e9c05e00043288c83885c52e736480001305ec0000000abf0000001e664276dd93580006f97ac377c85c29f0000000308fd45d0c60893400066e80000000005ea80000000000002c7518800061684140007c26cd91c978884d25a9ab8d0e00064900009f457a0003b3c000a4e58339
  | 36 => 0x4b473e0006ec00015700007af8b257589a748f88510bc00000330ccf7842800026b0000ed87bd1244000000621bd9d3aefb92413094410724523a0ddec247a43c399c6266e90001e755a43395642324f0606a252800062e0f08001ef9334ee67ed0a9c79a303539b8f14465944f2000147a46c04f25255ba7cb61824992c86576ee00000005a2547bbddc5c42a28f17b1d7e9951541196552c4862b119ca72cbe18309716be2bc5d507a8c3a9cd2b12ecc456ece73c07fd510e973b2945977462572c2bc9164e2d5148b6c6ca02a0bb29c4bac3fe4be09cd2687f408d87749d0aa84d0bb80e8e2851dea03190eb4cf25bda8eaab6671ab58515282804aaf4d7cb98f7c3a0d9474c6f1bf22d49f846e7b4b7b183cba1331ba8c4b6ed205ce54164283e31390644fc97f1bc0808e766f022eb1349885c00f1b4f10427416a51b54858c4911e16ecbb8d836190ec068ea93054ae3db84fa96ac02cdbf407f6b397d598cdee7820c104bc6de5983abdb5a7ea11217a15a00001ee1a5db70a056b03b8cebccc80003138e3600071d9ee8000619000023de8800031a26006562d765800010325a800001ece1ef3e221ca64a351357c4a4958a4b13232bbb0d16c2800000018a8d5e6aca90d77a8941d49bb557a2871ba3d18e8432019f9e21092bfe79820c53789c58b62044fde68c7949a987b4e2150689f09e662a0dfb5dd902be866e07e547866e2790d71a220003d1385d65a0a50aa972901fbda00000000000004eab47cec80000910001fb249f3251f49d2673a4408001ad27df0000000000000380ac7d846000013800000005217a3519cb6e0d7478d43322e1c35c21d5cc8a8513e4060a262b631983604d400033ba31509e53f21e2719d22cd704b3a58f889c5727884836c01c79206b95ca69e6244001b2e3a740200018d493279c9811a441ac025a111a8e000705b841c2a15249b86e1a0e6f17610714cd40a9faebf38f8e58f422881c20cd6e199a6b5cb2bf61991d493b6c8362f29d4a0e2093f499c88fa0005ba9da9132000000217d1dc0000000001012a1b47f36844dc19c2b7b3b48a48e60704e98f48bef3e607d8a86cfb3b903a958eadb1849f0ca6e62965e8e49c08e270e784746d45b977dafb4acc312259196136801158518413eca8147d35b5d4211678eb0e45bab2725f02841600db5742fe5e0c2c320137c83467d8729bc61b6e3644f5a2a944c98e6680dc08907a52098f99e469616a6313b9d881a7dd065c76cbd164fae1aeb0ee579eac347402cf6c08485472cf066c9da420241f7b40e04fda88812a8058000bce3838a3d75e4971400000c48b681363055f54a6c0d41cfc0000a46ff8000e703502ec95fd198a670000000952b3623180004862420a529fc20d76c400a38000000000028293300006da34487c05d20001724000c
  | 37 => 0x90d3a2af8b23ce5700505e549efb70411eed17a58a66a88ccf6ca73d9a404105e451000227800000025c0fad66291428f8101166bc80b4bb2c18af9734720a975c6fd329b360b0c2e25daa6e01f0c4b10d81856ee2410b7a19c4b44cb09193d0132c4f0363c1ca0c99f6c6b3e0f38caa13691ec0c035f53d96ddb9ae8d13b0d20d5ae0528a2ffd488da54aa18e886c72311a257588e00070fbb2057a1af5c68f49360c3740f3b912829c14d01f94d603d62c038d92c46323ed8f61e0ac5a43e97459a234c770964dabad242871958dacc96625dc39bc6bd4351b78000e16020592a109408519a2744268d945870ca49deda73a590182c234fcb69e601703793e80001254a8300020185be8e24bea8051ee7d56658600000dc307fa8000000809790bdc3c4d9f31e8001df436b444ab8cedca6b3b9800063e37117c8c2093829b22d8000e727a82a01d31ba6000000344000000048c00000000000000000b160000000001b7e90a43e1d441e0f7b2599534e2604d1894001d64568609ac8c56b0005113df400097320c38e8b0e0a252d959d2fb0000000b506ae00048a800000060b7a594684f6dfe66232907fe60574308182b6cf33c9142c0004448000000e3eab42a13940f2e00000032bc00097700037d031800000900006cc00052c877dbe2a2c3ba89c40d60003c4b819296b170218000000a530000000000000060969c0000006661f5c000b0114c1fe5a400004c1b8ac0006cf0b40001476fae3ab1d8c78600050bb6c51b0f4955b90340b6c172ec2b71a6c02b650a1adcd23e10b72bad86aa891f1310006200001d2dd90f400052338c0cb61d949f9ae881000000036e869e6af000334c00020541aa9f0000e464c82e80000d2c33221540000001ca2bfd746c8921eb6a44f7244156285849adbd17800018b04462f88000e540000000001cecd7850e8c681f4c0e00484a5ec678b7a78001350aae0a200011bced35070a700005eb11d3e0dd3cc0724616301de000225abc12c0e493881931356bc0e8da84c00079f0000000c5a8642db025dba4c32d380000d8c1c66e03f2569502877892658beedb0001385b1ca4200021b4c120005fc00001056dc6c88001d5c0000002d00000297615000020e0003d90000a080006bc800000000054f0001aec8b0338a35df1ef401553879066c6c4d73980b3ca1243f2c1db608dc1248000fb40002ea0000cf8cc91af25a950490805721a54620d73fddafc47000000010383b400025125580c43b76a828a82bca04b71b794aaaa665d8a1a91e67b021cb9f55eaa186cc0ce69569ec507a68c0000000001e000000005062dc4000fd02668000b4000023a8c901eefc100027674a47400002d84be676f00022541007783592341a1ef65390800000000071a018c5268741a692f500a00038009aed98a8c33cb
  | 38 => 0x1df1a42a210000000906dc64a202965ec6d35430870c0e0006014c2ceba000275ad6c98ede14fda99445ec6365037041305e73970874646b4b416253428af71478a7613daf0d1bb2a1c5b0ae01d5852c0526fa0a8b9cc846c7aae083d8788b165372ea00ba00072f0b8c298000377b62117e532220bc7c0aacce00012c000000065ab02d0cc12a0000b9d94a0001c32c50000db95f50001b500fff18b329e4ab65d7c9af9d1c60648b191c8c2bc782f0d6d51aec315287541c4fb85260a44394125630ed48e086ab1b09b1d7dd4e05618a1120a1574bf1ae464c2f5237a8d5d5450c2e834d567fea941c2321714ada51c3071796ba0d1292790aef3a1cc04490607cf5a41635734a403eca3e41ac6c922f04dd03ef6c58c9bf956a07800583486dade201b0b4d12e5f26830ba8000b81000004b8e4ea00000e94a6000000029a90de66b76620e554eccd57895797d22675fa00003248ff29e2d4d36e0001fa92215b08c703ba1c40009d2132a185730d3b40bb46000073473fad054b84428001330d8220f667b07c00020d4501994c4cc79c958a50b10fcc0bc000061cbbb0000001c50000579bbcc37cfde0001c300009b23229bf0770216680000187a0000002b39898e791aaa5780000002078000000620000000197e1a907e00000004d30000000cfaa630003cb46744ae67100d00002de0003df80000003c538957e1b963ee1fc98063906542798d6a3d74920b10000be01ae8000fc0b904e024480007c500000011f00001d100017ba00051f311fcee82453b3c9df42e4700000000003008000000000aa2000000057c14264283ec0005a306300000000000000b005205202048000bf877769c34f48763400003928000d660000001a6000000009d045ab35596336de862f800039b03781334b7a84415eb0c02c86ccce6fb207919197fa00052fb738000b8b2183e34129a627a0be048fc0e10002d94000f4e0001e79a9a5534429cdd91600052b2991c1257c5550068000e4e13edc580000000cd130c000d640001d7de0287b39395d80006a90002b341149435268145e5000008d000174a12b75304359c27c67960ef931a0be2d530e6beed255c6000000078f26e0001d28b54000204a00086300006b40005cb1bd16441714bb00037d9862596635aa851189f800000000007660160000000f9e0002236000f790e5bb11eeab3e2b800000001b578780018e60003f30001208d1c273aad93528230ba80016fede403817d9c3429607f1fdc9da97cbff9948f6826f0000f29e7e0006c5a8a193aec000033bc7f40380001ee172691d5821ffb70e396280a8707e40c27d81eb82ee5031c9a42dbcefcb49d020cbc0e2c20a95690985f470422f0356460174b0fd0ac28e5d5bc31bb64772ae969083600010f1ad0dbe55f51834991ea9c71490624ddc
  | 39 => 0x4eb39003dcbd71d41e68796b6e1759e418f0d8065b9199ade9030000748be0f8000027c8000e834830001650bee59703f56aa19300021414162277e78470000d860000e35bfbb882083b51e76e8c2169a656667af2d9bed981afa31b13bbdd0eebb7b713290f26e03e41b90db4d8c5c71a4d8202566598000000d8f5c3fc59c0042f2c938040000002978dbdcd07c948985ac9b01f70042f3567443e0098001f841910000118000d4000000000000000003c88c4417100019edb7c65c5f10000000e165b186500009ca11f2ec154882b00000000000000003958d426943003bb46e428ae9f31f4fe0e29661339525ec081332ab5a344c90000001cc4729000277ddf8b943de8293934b375da02d97ee95324e9fe0c7297628d9834af032d67d2d0921ccf67513e2854631813b86a882cc95072883986cd2f646255d8b808e2133769c3a8ed13d0c3d440bf01883c21d3a35443635b0fd012d3f98b2cf18435166315d67ede634793e400000060013c1c86000000000000038f000000000061361d88c00ca60100027cc00026eb72adbdb880001a31b98000f9d0002d5cb5651c3f08bf840641c513bb4e39a8008003c6400000047a197c59430063c8721524d6200003645b82148000001732717000000088600045ca4093180002cd33c8000bad2a70001c7eed51fb2bf03f46ca17ceb2569a2b73e88f6bd668e415c9f91006a8e15fabb1a8a88e5ba0078a54db30fe00000004ac407a614eec00064400013f200000001680001e900037cc0000005cbaec80000f900016b407a8df63b11280722952d90ebdaac81423c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1a0f85e1363d8910006836158418f6244001a858460463d89100058364c6454f624400160d9418d53d89100058364c6550f624400160d9518d43d891000583a595350f624400160c9654d43d891000683a195350f6244001a0c8654d43d8910005836547350f6244001685911cd43d891000623a1d43cc76244001a0d8550f31d891000683611530c3624400188e8750c30d891000683615430c36244001a854360430d891000607615845ce624400141f9754d43989100050765d5350e624400181f8754d43989100060761d5350e62440038978750d319891000607e1784dcd624400141e9754d43589100050725d5350d624400181e8754d43589100060721d5350d6244001a0d8550f3218910006a150d81cc86244001a0f85e136318910006a1e1381d8c6244001a0d856106318910006a16118118c624400160d931915318910005836506354c624400160d931954318910005836546350c624400160e9654d4318910005832595350c6244001a0e8654d4318910006832195350c6244001c0e7654d4318910005a164c644c462440016859418d3118910005a1a59434c462440016849650d311891000781d95434c46244001e046550d3118910005836567350c6244001685919cd4318910005a16465350c624400188d8750f31189100068361543cc46244001e055350e311891000781d4d434c46244001e055350d3118910006a150c804c46244001a0d8454c30189100062361d430c06244001a0d8550c3018910006a150d810c0624410f494965cd411051003e25219735044144001c857318941105100050764e75d92404400105e989d763901100051364e75d8a404400144d939d4629011000721dcd4318a1044001e055350c628411000507e597350d65040018597320143594100050765e7350d6504001c1973e014359410007065cc8050d650400121d9321172594100060761d43cc96504001a154360732594100068550f814c9650400181d8750f31594100068350d82cc5650400181d845cc30594100060761d430c16504001a0d4360830594100068550d810c1650400141f9754d43d90100050765d5350f6404001a1953201435901000507e5d5350f620400141d9754d43d881000607615845cc620400141f9754d43188100050765d5350c620400181f8754d43188100060761d5350c6204001a158350d65c84100070554d435d82104001c85434c976084100068560d4359421040016249460965084100078150d3259421040012659859672084100049965787588210406d2a4946156208410006a160d435882104001e055350d620841000499661651082104001a456560c420841000619594825c440040014659759421080100070554d43dd91004001c856350c72440100074154d431c91004001c195350f7644010
  | 1 => 0x507650705d563d000181d855d37158f40006235d182dc563d000505f985cf635964000417e617318d659000105f985cc735964000607611731cd65900018597320143596400050765e7350d6590001c1973e014359640007065cc8050d659000181d8750f31596400068350d82cc5659000181d845cc30596403460761d430c16590001a154360430596400051364e659cb619000144d9399572d864000417e4d86dd5419000144d9399772506400051364e651c9419000181e86615731064000447662655cc419000105d93e1975886400050764e65dd1219000141d9399576d024000607a19855cf409000111d9899573d024000507e5d5350c615000141d9754d43185400060e5d48050c61500018997320143185400068654c8050c615000126595219210854000507a5d5350d6110001c0d5350f725844058f09104751c96110001c0d5350c72584401b629210725456110001c85431c93158440006a450c804c561100018657520961884401b43926176484211006d8a4845d921084400050764e85dd9401000181f8354f765004000e07e1d5350f64c4001a195320143d9310014172617354d64c400141e9754d435931000507e5d5350e62c400141d9754d4398b100050765d5350f6484001c0d5350e72d92100070354d435cb648400141e9754d4358a100050725d5350d628400388c8750d3258a1000499e5587d88218406d2a694e176208610006a1e0d43d882184001e055350f62086100063861e80d882184001a158460463d951000507a5b7350f654400141e971cd43d9510005856447350f654400181e8750f32d95100068550d81ccb654400181e8750f31d95100068350d82cc7654400181e8750c30d95100068350d820c36544001a154360430d95100050764c65dcf644400181d85dcf32d911000625dcd81ccb644400181d85dcf31d911000623dcd82cc7644400181e8754c30d911000607e1784dcd644400141e9754d43591100050725d5350d644400381c8754d43591100070354d43dc96444001c0d5350c72591100050764c655cc644400181d855cc63191100060761d8518c644400189587604631911000607a197354c644400181c865cd531911000507e5f6354c644400141d9718d53191104b6076157394c644400181d855cf3219110006255cd81cc8644400181d855cf3119110006235cd82cc4644400181d855cc30191100060761d530c0644400188d736083019110006255cd810c0644400141d949db75d8d100050765676dd3634400141e96dd774d8d1000607a1b75dd3634400141d949c375d8d1000507e5571dd3634400148f925c774d8d100050765670dd3634400148d929c374d8d100052564670dd3634400181e87dd474d8d1000607e17745cb634400189774e0572d8d100068361543ccb6244
  | 2 => 0x401685919cd43189410078154f8150c6250401e055320543189410062361d43cc46250401a0d8550f31189410061361d530c06250401a0d8454c30189410062361d430c06250401a0d8550c3018941006a150d810c06250401a198454c30d8141006a450d810c3605040181d8750f32594410068550d81cc96510401a1543e0532594410060761d43cc56510401a0d4360b31594410060761d430c16510401a0d4360830594410068550d810c1651052d81d875d27558c4100507241745d5631040181d855d37258c4100e2560574dc9631040181d845d47058c4100607615741c16310403895815d07058c41006235d1821c1631040f49591a1d6350441007031d5631c9411046dc877158c72504410068654c8050d601040141f965cd4359621004c364c845c9658840141d979cd43596210058364a7350d658840121d9321172596210060761d43cc96588401a154360732596210068550f814c9658840181d8750f31596210068350d82cc5658840181d845cc30596210060761d430c16588401a0d4360830596210068550d810c1658840141f9754d43d92210050765d5350f648840190d846157310a210068560d43597218840141e9754d43591210070554d43dc5644840141c9559173191211d525e45645cc644840141f9754d43181210050765d5350c604840381f8754d43d9021014172617354d6408401458905cd535902100507a5d5350d6408401455931d471590210070554d435d8410846d5249460975104210074150d325d441084019158461573104211b561251525cc410840116595e1972104211b469251855c841084019858350d72104210074154d435c841084011659520172104210064560d435d621084015249460975884210074150d325d621084019457560c42884210070554d43dd9210840116595a1e424842100459e4d85dd9210840116595e0f76484210045966353dd921084011659854f76484210064961743dd921084019258550f76484210066160d43dd92108401d055350f764842100619a1d85dd92108401e055350f76484211b6291d1869d12108401524955d074484211b6619d1831d121084019857460c74484210045965687d91210840116793614704842100459657831c1210840116598d4c704842100459661531c1210840192585d0c704842100649615431c121084019858350c70484210074154d431c1210840116595e1d21d802100459654874866008401361952012198021004d865480485600840181f85e13735802100507a5d5350d600840141c9754d435802100607a1d5350d600840181c8754d43580210051625d538c160084014989750e30580210060761d43cc565d0001a0d4360b31597400060761d430c165d0001a154360430597404b60761d749d563d000141c905d17558f4
  | 3 => 0x180781d409081064052921d80255101d86a000c9000592a87d1a0000651d001150007100049000c0001075a14e2b4a002082468f04e88d1416d0e8564d1145814320c11168ec094134a6a849c000012b07d7c3a5230dca5290a6000962f8cd4140f5e09c2d13d2416f034b109891344c15b94d558052bca124cdd518f440d37358ab2f52e3bcb52fc64224061c96b4ae6f458655c5043b2920ecd95c14538ca21448e399620e0625044e45d5e0014b0d473000c8464842b921c84fc29cb255c00148f856d2c001631b86c5d000444000002300400000005453f14c005684d3c4ed000553544b02c2b3894c0012f3e4f50885d122b6390855e8450008f3cc0039c294c0e0000de3c8da4d4104780000175408000002d46d28605691ac9e218361d15f1185c000ca1fc120003f0014005c4a1089b37c810430f3ac6d150994955d36a0048b3c371543a8bc3086326037de440230215485e01d12bfcfd05512340ac2ec8b070333dc0053d7d36c043952d44c9f131311c0b3001332e43c3317f4ed733480e051222201613d1c4d8003a0003d8480017242411ac0004e079250d35980c15cc70296454c7e528d847cd725c9d1050e5f9493116c0756a4c9836082f00069001395700017d083ec2e00c0006d0c5dc80314b800144498341e8004bafe1f10b5d84319984090001dd7b28c000c567554005202a001424003d564b70005b078000003000147560003189a32c00000004f8a90000043444584cf5400001c0001090640005038ac040304810083021848040a0100816000001832000000000313b8ac482c19000000400800001805800040100018140000040020314800680700800000604800001909020042d08820920a068000004000002c02000140405008000001000000400000340806090580206000380608030143a0b0002c0c060180816000401050000e0081803000ac02120204c0141e9754d4358b4101417a637354e60d040141d9754d439834100507e5d5350e629040141d9754d4398a4100607e1784dcd609040141e9754d43582410050725d5350d609040141e971cd43d954100607a1d43ccb6550401a154360732d954146e07a1d43cc76550401a0d4360b31d954100607613730c3655040181e8750c30d95410068350d820c36550401a154360430d95410068361543ccb625040160d9319543d8941005836546350f625040160e9654d43d8941005832595350f625040160d951cd43d89412b5a16447350f62504ad88e8750f31d89410068361543cc76250401a0d8454c30d894100623a1d430c36250401a0d8550c30d8941006a150d810c36250401a0d8550f3218941006a150d81cc8625040160d93195431894100583a595350c6250401a24652054318941005836527354c625055fe074154d4318941005836567350c625
  | 4 => 0x2e800490670010a0001811c584a80030c00000000a0390000000120594000f800000d43b8e1460fa000002287b0b03209c00000610000006800008ce
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6350100000040200002a05a31948150c6250401282d1928c12eb1084200a416a15350f76484210052094aba3063a24210802905a854d431c1210840140cd3aa64028630a800098168c946096508410
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x4c
  | 4 => 0x4e
  | 5 => 0x124c
  | 6 => 0x138c
  | 7 => 0x5
  | 8 => 0x94c
  | 9 => 0x94e
  | 10 => 0x124e
  | 11 => 0x138e
  | 12 => 0x10c
  | 13 => 0x10e
  | 14 => 0x130c
  | 15 => 0xa0c
  | 16 => 0xa0e
  | 17 => 0x130e
  | 18 => 0x180c
  | 19 => 0x180e
  | 20 => 0x20c
  | 21 => 0x20e
  | 22 => 0x140c
  | 23 => 0xb0c
  | 24 => 0xb0e
  | 25 => 0x140e
  | 26 => 0x28c
  | 27 => 0x28e
  | 28 => 0x148c
  | 29 => 0xb8c
  | 30 => 0xb8e
  | 31 => 0x148e
  | 32 => 0x184c
  | 33 => 0x184e
  | 34 => 0x95394
  | 35 => 0x5254
  | 36 => 0x94054
  | 37 => 0x94056
  | 38 => 0x95254
  | 39 => 0x5394
  | 40 => 0x125394
  | 41 => 0x4954
  | 42 => 0x124054
  | 43 => 0x124056
  | 44 => 0x138054
  | 45 => 0x138056
  | 46 => 0x8e
  | 47 => 0x98e
  | 48 => 0x128e
  | 49 => 0x150e
  | 50 => 0x21254
  | 51 => 0x20054
  | 52 => 0x20056
  | 53 => 0x5554
  | 54 => 0x20d
  | 55 => 0x4214
  | 56 => 0x155254
  | 57 => 0x154054
  | 58 => 0x154d
  | 59 => 0x154056
  | 60 => 0x154e
  | 61 => 0x40e
  | 62 => 0xd0e
  | 63 => 0x160e
  | 64 => 0x188e
  | 65 => 0x98c
  | 66 => 0x154c
  | 67 => 0x124954
  | 68 => 0x124956
  | 69 => 0x138954
  | 70 => 0x138956
  | 71 => 0x128c
  | 72 => 0x150c
  | 73 => 0x40c
  | 74 => 0xd0c
  | 75 => 0x160c
  | 76 => 0x188c
  | 77 => 0x139256
  | 78 => 0x139254
  | 79 => 0x21256
  | 80 => 0x155256
  | 81 => 0xa0114
  | 82 => 0xa0116
  | 83 => 0xa1314
  | 84 => 0x10a14
  | 85 => 0x10a16
  | 86 => 0x140d
  | 87 => 0x149314
  | 88 => 0x148114
  | 89 => 0x11494
  | 90 => 0x11496
  | 91 => 0x130a14
  | 92 => 0x130a16
  | 93 => 0x181316
  | 94 => 0x181314
  | 95 => 0x131814
  | 96 => 0x131816
  | 97 => 0x29314
  | 98 => 0x130294
  | 99 => 0x29316
  | 100 => 0x130296
  | 101 => 0x131494
  | 102 => 0x149316
  | 103 => 0x131496
  | 104 => 0xa4d
  | 105 => 0xb0214
  | 106 => 0xb0216
  | 107 => 0x20b14
  | 108 => 0x20b16
  | 109 => 0xb1554
  | 110 => 0x21414
  | 111 => 0x140214
  | 112 => 0x140216
  | 113 => 0x141554
  | 114 => 0x21416
  | 115 => 0x28214
  | 116 => 0x28216
  | 117 => 0x20294
  | 118 => 0x20296
  | 119 => 0x184214
  | 120 => 0x184216
  | 121 => 0x21854
  | 122 => 0x21856
  | 123 => 0x140b14
  | 124 => 0x140b16
  | 125 => 0x155414
  | 126 => 0x155416
  | 127 => 0x41414
  | 128 => 0x140414
  | 129 => 0x41416
  | 130 => 0x140416
  | 131 => 0x189414
  | 132 => 0x141894
  | 133 => 0x189416
  | 134 => 0x141896
  | 135 => 0xb8294
  | 136 => 0xb8296
  | 137 => 0xb9494
  | 138 => 0x28b94
  | 139 => 0x148b94
  | 140 => 0x148b96
  | 141 => 0x14cd
  | 142 => 0x185496
  | 143 => 0x185494
  | 144 => 0x149854
  | 145 => 0x198d
  | 146 => 0x5556
  | 147 => 0x4216
  | 148 => 0xe8e
  | 149 => 0x18ce
  | 150 => 0xecd
  | 151 => 0x1a4d
  | 152 => 0x4956
  | 153 => 0x58d6
  | 154 => 0x4e96
  | 155 => 0x2cd
  | 156 => 0x164d
  | 157 => 0x958d6
  | 158 => 0x94e96
  | 159 => 0x95456
  | 160 => 0x130e96
  | 161 => 0x180054
  | 162 => 0x181354
  | 163 => 0x180e96
  | 164 => 0x141556
  | 165 => 0x44d
  | 166 => 0x140096
  | 167 => 0x1418d6
  | 168 => 0x140e96
  | 169 => 0x1415d6
  | 170 => 0x29554
  | 171 => 0x28b96
  | 172 => 0x29556
  | 173 => 0x29616
  | 174 => 0x28e96
  | 175 => 0xec215
  | 176 => 0x1a4215
  | 177 => 0x2c215
  | 178 => 0x14c215
  | 179 => 0xb8e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1242
  | 6 => 3928
  | 5 => 4065
  | 4 => 389
  | 3 => 7
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
  | 8 => packedAt gbK8 (1369+((h/21+packedAt gbK8 (1222+(h % 21)*7) 7) % 101)*7) 7
  | 7 => packedAt gbK7 (51223+((h/479+packedAt gbK7 (45954+(h % 479)*11) 11) % 1725)*12) 12
  | 6 => packedAt gbK6 (207056+((h/1424+packedAt gbK6 (188544+(h % 1424)*13) 13) % 6202)*13) 13
  | 5 => packedAt gbK5 (258165+((h/1410+packedAt gbK5 (239835+(h % 1410)*13) 13) % 5078)*13) 13
  | 4 => packedAt gbK4 (28427+((h/133+packedAt gbK4 (27230+(h % 133)*9) 9) % 482)*10) 10
  | 3 => packedAt gbK3 (575+((h/2+packedAt gbK3 (567+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1807fffff80ffff80ffffffce7f3fc1e3f1ff
  | 1 => 0xffff81f81fff03ffff03f007f598ccfe9c7e67
  | 2 => 0xfffffe001ffffc0ffffc0007f9e0f0ff1f8f87
  | 3 => 0x1ffffffe000000ffffffff83e00ff07e00ff8
  | 4 => 0x1fffffffffffff0000000003fff0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x30000a282580451180451536402b15c021b0ab
  | 1 => 0x52a581590aa903a6a903a05294984c5a8c5665
  | 2 => 0xa54ad6021352e80b52e800a52960b0ad168b86
  | 3 => 0xc1f365974018208c7cb2cac03e00ea07c00d50
  | 4 => 0x1fc79e79c7cb2c0182083003fd50007fb6000
  | 5 => 0xf86041040060c30060c30c063ffefff0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37435
namespace PEqualNP.Outside.L_meta_37435
open PEqualNP.Outside.L_meta_37435.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 14 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 19 := block_range (n:=19) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 467 := (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat (concat bs3_4_96 bs3_4_128) (concat bs3_4_160 bs3_4_192))) (concat (concat (concat bs3_4_224 bs3_4_256) (concat bs3_4_288 bs3_4_320)) (concat (concat bs3_4_352 bs3_4_384) (concat bs3_4_416 bs3_4_448))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 634 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 bs3_5_512) (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 13 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 13 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 75 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_160 : Interval s5Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_224 : Interval s5Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_256 : Interval s5Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_320 : Interval s5Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_352 : Interval s5Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 626 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 bs5_4_512) (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_64 : Interval s5Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_128 : Interval s5Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_160 : Interval s5Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_224 : Interval s5Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_256 : Interval s5Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_320 : Interval s5Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_352 : Interval s5Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_416 : Interval s5Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_448 : Interval s5Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_512 : Interval s5Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_544 : Interval s5Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 699 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_384 : Interval gbAtlas 4 384 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 389 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384))))
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
theorem bgb_5_4064 : Interval gbAtlas 5 4064 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4065 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016)))))) (concat (concat (concat (concat (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 bgb_5_2144)) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272))) (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)) (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528)))) (concat (concat (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656)) (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 bgb_5_2784))) (concat (concat (concat bgb_5_2816 bgb_5_2848) (concat bgb_5_2880 bgb_5_2912)) (concat (concat bgb_5_2944 bgb_5_2976) (concat bgb_5_3008 bgb_5_3040))))) (concat (concat (concat (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)) (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296))) (concat (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424)) (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)))) (concat (concat (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680)) (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808))) (concat (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 bgb_5_3936)) (concat (concat bgb_5_3968 bgb_5_4000) (concat bgb_5_4032 bgb_5_4064)))))))
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
theorem bgb_6_3904 : Interval gbAtlas 6 3904 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3928 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672))) (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800)) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928))))) (concat (concat (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152))) (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))) (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)) (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)))))) (concat (concat (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 bgb_6_2144))) (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))) (concat (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784)) (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 bgb_6_2912))))) (concat (concat (concat (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136))) (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)))) (concat (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648))) (concat (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776)) (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 bgb_6_3904)))))))
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
theorem bgb_7_1216 : Interval gbAtlas 7 1216 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1242 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)))) (concat (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056))) (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80eaeaeac0eae8ea80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264064 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37435.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[0,6]⟩,⟨.and,[2,4]⟩,⟨.or,[4,6]⟩,⟨.or,[3,9]⟩,⟨.and,[7,10]⟩,⟨.and,[0,1]⟩,⟨.or,[5,12]⟩,⟨.or,[3,8]⟩,⟨.or,[13,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264064 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264064 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37435

open PEqualNP.Outside.L_meta_37435 in
theorem PEqualNP.Outside.L_meta_37435 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264064 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264064 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
