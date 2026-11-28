import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36336.Model
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


end PEqualNP.Outside.L_meta_36336.Model

namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
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

def SBf (j : Nat) : Nat := [7, 6, 5, 5, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36336

namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x344068000ace00000128352602222204024542119714007853a086283c593864c4c0093284f920050a8e00805873668300054300200128b2c4ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1c818011979a080000000b9a800000001900000017028002180000000022001024001b800c1d258b0c8000141f000018801580000eaaa600098000001496121100000a8e0d012a2c0896800000000000071f92a1a0998000038005a10d800000000f00000513a3802b8000000a000000000000000f890000000400001c24802510800000002913002ca2801e8007a7a680000006801b00000028a8008000201d83298015049e002b2706002300400080404101408040400042004040000000c000c0c04080030000400027ca5a1cf55243b7a92876c5250f3ea6a1ebd49439e29287ac5250e58a4a1cf950439ea9c853e5290abca6215754c42cf298853d5310b3aa6214754c429f29085ae5210a7ca9994f55332cea1e65ac42ccaeca3995d547329faa4653c548ca7ea8994f15132cea1a653e540ca7aa8196b10832b7a92836c52506bca620d754c419f2a6633d54cc73a8798db94b31b6a96639d434c67ca818cf550319f2a4433d54886bca710d754e21d6214433f5448678a890eb10821af29e815d53d02dca5205b54a409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2600078002c0003a442a000028502c1c29820c1a212e6a048058504e14a201030c6254c42a318943cca8d6310b32c910a51ccb15435473287195434ca2d6510832a318943cc70d4354b31a3189434c62c6255031a358c428870e5310a218758c544868d63108218b18954cc28c6250e30a3189430c30d4354830c550d510c28d6310b208758e548828d6310920c314c42483244214520
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa811a000008282b988528e65411c9435473281aed2988510d047250d510c206bb0a621241415cc4214520
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2670+((h/30+packedAt s0K4 (2430+(h % 30)*8) 8) % 172)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s0K2 (302+((h/2+packedAt s0K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 2 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2004088824020000a41280444022914810d095
  | 2 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36336
namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc4120a0000033a42903bf43de43bd43dd439d43f721ee21ec21f421e421
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa494c010007020801844611d5490f2a8790e350e21b328c438d430872a8610e9d0c21e321843a5430878a8610e150c21
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x2856490c21
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 10
  | 3 => 11
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (172+((h/3+packedAt s1K4 (160+(h % 3)*4) 4) % 13)*5) 5
  | 3 => packedAt s1K3 (309+((h/3+packedAt s1K3 (297+(h % 3)*4) 4) % 15)*5) 5
  | 2 => packedAt s1K2 (39+((h/1+packedAt s1K2 (38+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffffc0ffffff03ffff07ffff07fffce3f1ff
  | 2 => 0xe07e0fff03f07ffc3c1ff8781ff8781f5cce67
  | 3 => 0xff800ffffc007fffc01fff801fff801f9f0f87
  | 4 => 0xfffffff83ffffe000001fffffe3e00ff8
  | 5 => 0xfffff000000003ffffffffffe0000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc10400460820000044230088c30088c40150ab
  | 2 => 0x4b18948a3944a92c1d0d48514d4851494cc665
  | 3 => 0x862d291450e95255c216950296950292970b86
  | 4 => 0x1451ce20a28c1b9aab40c44418e66703e00d50
  | 5 => 0x18618c38c30e63e33398e66700c44403faa000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaa000faaafaaafaaaa000faaafaaafaaaa000faaafaaafaaaa000faaafaaafaaaa000faaafaaafaaaa000faaafaaafaaaa000faaafaaafaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36336
namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
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
  | 0 => 0x1fffff03ff83f83f87fc1ffffc1ff03e98fe73
  | 1 => 0xe07c1ffc1ffc1fc3f87fe0f03fe0ffc16f339c
  | 3 => 0xff801fffe0001ffc007fff003fff00018fc3e0
  | 4 => 0x1fffffffffffff8000003ffffffff003ff
  | 5 => 0xffffe00000001fffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc108811841148804808c85518c85508c085631
  | 1 => 0x4b10a228ca10a9418834a46294a465842b3294
  | 3 => 0x863ad451875adadc445ad6453ad643198dc3e0
  | 4 => 0x14431882144214aa5502100823188a31d0014a
  | 5 => 0x186210e3186317336663188e02100c21f6a800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeee0000eeeeeeaaeeee0000eeeeeeaaeeee0000eeeeeeaaeeee0000eeeeeeaaeeee0000eeeeeeaaeeee0000eeeeeeaaeeee0000eeeeeeaaeeee0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36336
namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
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
  | 0 => 0xffffc0ff87f843f87f87fff87f07f8093f73c
  | 1 => 0xf0787ff0ff87ffc3f87f8703f87f83ff6cc9cf
  | 2 => 0xff807fff0007fffc007ff803ff8003ff8f0e0f
  | 4 => 0x7ffffff807ffff800003fffffc01f00ff0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x6110046210800804809809198091188c01531c
  | 1 => 0x250088a2400a0081882882288825092424c145
  | 2 => 0xc23551443555455c44555053550232598b0e0a
  | 4 => 0x8a466208a441566a55044082664a6011d00ca0
  | 5 => 0xc64438cc66667b3666664e0440c4061fea000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36336
namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8437c53086fca410fbcc821f6190437e51087ee8210fd10421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81be439037887205f94a40bea94817e51902faa3205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea94617e518c2faa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3bc6498770c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ee218617e520c2faa4185f94430fb2886176510c2faa2187d54430baa88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53882faa5105f94620fb28c417651882faa3107d54620baa8c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ec62887d4c510fb90a21f421443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cafaa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf28483fa50906f4a120df54241fca84837950906fea6a0df14d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f710d31bfa9263ef524c6dea498df14931f6292636c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea9
  | 2 => 0x3940012100011c1d4001a115600000000000000000000000000000000056c8880445a3180d00016e37cf08ae25a2e8002330001591b92500000000000442000530003220005e9f60004dc3d24b1140600012808089cae8f51760500015a0008bc858000001bcde80000000000000000000001392340000991400090c872480f83e07913247009d311c74062a0f10002900001d0003ba0000016d3740002201d1ce00104a222001a0000fb2fe7181c15f1c822c00226324000db9ea152834b91343581ad170833986b9209ce2e61cd2d26300050d0f0000be00000000000000978003f2001090670006bc00138000891192340726a8da80010a47800000478000c322a1ac00051000000000000000002d0a99582520002108f0004c52b0002ea5bcfb8001b2000a08000562449980000076c00000000000000f412c000eb00025c750c60d7014000010d00420140f05530a88d0d0860002b0d98cb4a059526a2c0002d46f1fb3d07905f8613969451aa4e178260fe8920000000000021a000dd8001460b4002362605f0ec2111d229c002464ba6980000006a2210a00007a5188987e29884c24800346198231880180012396e0008008192b04460c908000000000322b1c0280bd1c11546a07f8a5330398b0000000978180eb274000951a00004d4420790009512fa530000000000000025cef8000b220129000000000dc8000000009e1eb3a000000008000000000122bc1290a9973b8000000000003cc0011500091400000000000000c2000000000000000006480027a00038a5c31200000000000748000000005e4cc91b248330fd0000007d40000000000000000000000710003e47b4f614d036270a78000000010c8004740000000043e21c000454080b89d95c000924bb17d47a000038002a41dc002390000006a0000000000018d000000000000005a4000000a65640b9400000000007f4b60000000027c000000002ce0012c0ec016710001452c20a8d81812326fc000a400024cc210a1a2714508000000c0100100c0800001004040000400800004000140700000000000040601403000010000000802014000000201c000040500001018010000000c00024020340000001010000040100000000030000b03c000000300400000030180001c0800000008060040a010010000000002014010100300401000160000000012018000040300001000040000e03408004000240402000004040000000003000000100e00c060080702806004000600400803000070180800800004010000200003000000000204007000000040100800004000140207803004010000200800000080000b0000000c0300000000190080500000004120100300004020040280200408bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x62c4a1c318e00000000348000001a70ae2c8e9a0a01e000001cd0001b12b80001a1786197042c900000000005e0770003de13c7508c27e0000021c120000000002462ccd28e83fc3f866800182080d119d000044e7a2031e320b518e18a840dc0dd1b67780011c2aa0000017e1728c0002084aa5880000007e0000017748800000000000000db0001120000000021875c779640000f0df1bc00067c4d14a1ca000ab9c840261c242670760003a0000667fc6d00004c2e0000d32081912514e1607246a84d0004880000033c458aa0000007c4fe00016c0002d00009808d27841498814000002306585791013287400000000000831e520a000001e30006a4000000008f800000000000000000000000000023a000d896c3f07cc000ad06c0010c0cf0000002816341647c6c1da1e20000723f09643c9b0002e2000000003d25d0001260000000b05c01200040800000000002070000011da060a21b83280003207d3012c00000031a171da79c080f73345980000035683d2c8000000002a0001f438c001ee0000001f0761fa66c0000000051c2d800000000000310008a0000ce22e0000016b1f20005f0004cc0d0348700e42347e0474ca9900a800000000000000001a8000250f6408a4800240278f81423263004a8430641390d8e1368628891012f6000001d53208a4838524c26b40e000304004ce1801620010107800000000151000000148002ac160a20000000000007d462090938000006c8000f0000424a58dc1ec780161083b2650fa09b0da0dd071c213e000140623a28306509d0000bcb4000000000ca8030c0798000003800002e8000003100015000000069225000000410
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x552d025e63947409758e51d035853d0140c714e40503586054c40c754e431034e5394840d354e521034e5354840d354d52103686054840d594e51103555394440d994a51103655294440dc98251103565354440d554d51103665254440d9549511023f6550040a718d401027b6550040b618d40102d86050f309dd8552cc2746154b30b318931cc2d96310330e690c40cc26e62152309b588548c27661152309d584548c23e649513097d8d544c27b60551308f994544c31d631513097996434c31c5490d3097195434c31c5450d30b6181434c31c548c930b6982324c31c540c930c7153314c31c544c530b3189314c33854cc130c7152304c27661d50309d587540c25e63150309b988540c26d62150309d984540c275611503097597430c25d6510c30d5d0d510c3544354430dc547400c2796510030e610c400c3715110030d5547300c371518c03097d95300c29c644c030d5545300c27b654c030ae191300c371514c0309798f54c825d63d53208f99353c823d64d4f20ba18142c82e962103209798f548825d63d52209d987548827561d52209798c548825d63152209d984548827561152209d987538827561d4e209d98453882756114e20d594e51883555394620dc98251883565354620d554d518825f63551209718d544827761551209d185544827b60551208fd91534823c6454d209dd8553482746154d209b195424825e63145209758c514825f63550209718d540825e63150209758c540826e62150209d984540827561150208f990530823d6414c209d98453082756114c209798e500825d63940209e594400833954100209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b10b558e41c42e4624c710ad59021c42d56308710d954821c425f63552109718d548425e63152109758c548426e62152109b588548426e62d4e109b58b538425e63d4a109758f52843395410210b658c40842e96210210ae19130842d9638821097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c6354910b558e41442f260905109d1954144274654c510b9189314427665c8510ad59021442d56308510bc980214427a65d0110b658c40442e96210110bc9844044278654c110ae19130443d1314c110b658e20442f261881109e195204425e63d50109758f540427a60d50109798c540425d63150109b988540426d62150109d984540425d6594c109798c53042766114c109e980530425e63d48109758f520427661d48108f990520423d64148109798c520425d63148109e980520435553c40109e596100435953840109dd95100435553440109ed9510043595344010
  | 1 => 0x9000020080105801004070180000000000050240000406000030040100c0300401014060001e0180100800004000080900c0000009014000000000003008000040201400020010140201c090040100c039e98251d0e7960947439d9845050e756114143d6d0c5050f3a4314143dc9845050f7161141438fd954310eb86050c4397d954310ed86050c439dd855210e7461548439798e51d0a5d63947429e98251d0a7960947429798e5090a5d63942429d9865090a756194242d5d4f5150b5453d4542d5d4c5150b545314542d6d4f5050b5853d4142dcd475050b7051d4142d6d4c5050b585314142dcd445050b7051141428fd954210a6f65508429d98754cca7561d53329e98354cca7960d53329e983548ca7960d52329d986508ca7561942329d986544ca75619513297d8d544ca7761551329d185544ca7b60551329e181544ca7a60145329e580514cb673214532d58c8514cb726014532dc580514ca7b60550329e181540ca7661150329d584540ca7a60150329e580540ca5d6510c32c7550430cacd6210c3297d95320cad4614c8329bd95320cae4614c832ad18542d075a5394241d654e509075a5354241d654d509065e63141419758c505065f63548419718d521063f65504419dd95411067b60553319e18154cc6d4614cb319e983548c67960d52319b98a544c66d62951319bd89544c66c62551319ed81544c678605513197997434c6d661d0d31d3d0c524c74c431493197997324c74c52cc931d3149324c6d4614c931d914b314c74c528c5319798f540c67a60d50319e583540c66e62150319b588540c67a60150319e580540c65d658c83197d95310c6cc624c4319dd95310c6e4624c431d68c9500c7583254031d6cc5500c7723154031d64c5500c771315403197d8d54c865c63553219ed8154c86786055321bc58031c865e63943219758e50c865e63d52219758f548867a60d52219e583548867a6014e219e580538865e63951219758e544865f63551219718d544867761551219ed81544867860551219798e534866f6254d219dd85534865e6514d21d514f214874c53885219798f540865d63d50219e983540867960d50218f596540873461550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d318953087546154c218f990530863d6414c219798c530867a6014c219e580530874d53cc8219b594320873554d04219d59441086e56210421d554f31087c732cc4219d59431087c4320c421bc580310866f6548421b318d21086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500865f6354b409718d52d02776154b409d18
  | 2 => 0x6a0147e2e8ca00000000141b0040008f8383e8005d800c20008e854002c4000000000033800002fc43800bd800000782511c93800000360016a000aa78272103100017a0031200172c90f65b800000dc2a06a519ac0000001b34001b400000b98008400000000000de4fa62002a40031600000000000031c000000000000000c600000000979b823a0c000000009c0000000000a58000000067a4a3503400000000000000000160c02044305eb529e003228a11e0002abb800310f81f910b19b6a02f00c2f49e8002c0000398a00000a2a7c00000aa1a6a433664a6e7e99a0b090b7800b58b894b1e000002c9183b800aa9200000082000000002b800be000078005794895abc4b000001023c0007002805892221127922c56ac8000000000046a262819016a54002ea00024971348780000132b28000000073800548007f8e6002b6a10001a00c0021290220a31be0e8649d00081a0a748009b026752462980090a2419800003300000007278740a4a720e6890a930003a8000000011800002d0a892413086b80000000000000258e0ce000001080006077ab20000000000289cc7d800000007d2d80000000198558988e1ae65a5a001161b800002f2088420f2163f0004e0745c2681b2ec8a926c8230000c000000ab9147cb2c76800001ec32800000b6000000000030800000000007a982220018875a502eaac7c294021bcc38004a000b08000016600000b89ca0000000270aea48419ee2b0f24f1ba0012e00000b38000005800000c501ac30006184a61218000d052b2aad08c8b80038800000c80002e4a872cca3c4014c001ea08168afa007a000001aa00000cb94200000000005b08000258872da4d80000000000000028e00326b71441588256000002cc720003b2327108400930638d835ab000000010120000069000001a0002d20033a0000031800279809118200000001c200000000000fab800000c08d241048a831a5f00a5e1d818800000e83900000000000009f8008518c0000013800998006523657286c181877234670440029258a82a6aa61c07c4e94e7f174331c6148f42d000002760009aa62c0000dabea64c126a001e68688a551406c8321717e78a88000be00000000000030a000763f922592feb9150808bc01c01028040000000402044020000101801010010080000003008000040004802000000000200405000000000100004000000340701c0c01c000100002c0700c00010030000000003004040040b0380600c0500002010050040400
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4403030185002cf1000962120090001ce2851935c1550341880002181461c15410c32988e2b1086194d170987434c6a338e8629263345c0614c931a90e498aa018d60724c5500c722310c2a9843545c06154c21988e6b108210ec03258031086a8b88c0a9881861506050d309a2e2302869861854982324c268b8cc11926183150624c530e2086a88801861464545300c318322a298061461cd5410020a88e6a9043885187355040843483226298221701c9314c110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x20134000941809c74314931c40625c06154c21c10545c46050d30c10545c6608c930c80641c9314c110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (18682+((h/205+packedAt s4K5 (16632+(h % 205)*10) 10) % 984)*11) 11
  | 4 => packedAt s4K4 (17112+((h/138+packedAt s4K4 (15732+(h % 138)*10) 10) % 660)*10) 10
  | 3 => packedAt s4K3 (1265+((h/8+packedAt s4K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s4K2 (303+((h/1+packedAt s4K2 (300+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf81ffffe03ff841f1f0ff1ffffc3fc008cfe7c
  | 1 => 0xffe07e1ffc1fffe01ff0fe3c07fc3ff8f3338f
  | 2 => 0xffff801fffffffffe000ffc007ffffff03c3ff
  | 3 => 0x1fffe007ffffff000007ffc007fc03f0
  | 5 => 0xffffffe0000007fffffffffff8000007fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48c30d0238412c030345305471e2643084563c
  | 1 => 0x5149112448ca24a00d54521892662950b13285
  | 2 => 0x228424489114014d2000a481248892a302c15a
  | 3 => 0x471659912287367656660012473320c5dc03e0
  | 5 => 0x84186001c31843989888c923800003066ba800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeae0c0e0c0feeafeeae0c0e0c0feeafeeae0c0e0c0feeafeeae0c0e0c0feeafeeae0c0e0c0feeafeeae0c0e0c0feeafeeae0c0e0c0feeafeeae0c0e0c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36336
namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x426242a0589431600903805270018428d3031a540940020e80209cf001c88d0c1eac1120000f805a44c801401528165cd811071ce02b5406c22030d2ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fa10fd10f910fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd4c1c18000054017848ad60b4997c813515250c5140688c009c000154000001316c0175498550c86d69440000b8000014311c880000c4dccd383c00600020a878d4bcf52908d800004438ed00100170004074e0e44cd12c002c00e93c00a0b000047c015cf800fd589465100118000188840104918000000058f000a4c164080000002401200000005c287000003400000404040014000006001e0212020000020606160202003000000c08000e04016e52d0edaa5a1ded4143bc282875e53d0abaa7a157d4d42ae29a85775150ae8a2a15ed4142bc282855e528cabaa3195794832e729065ce420cb9a84195754432af29c835d53906f4a120de54241af298835d53106dca420db54841bd280837950106bca598d754e31bd2846379508c6dea498db14931e7a92635c524c798a498d314931eba8a635e530c6f4a018de54031afa9e435c53c86bca710d754e21e6194437a50886f2a110d7d4d21ae29a433e540867aa810d794c21aea9843cc32086f4a010de54021afa9a815c53502bca6205754c40b7290816d52102eca2205d54440bb2886175510c2bca7105754e20bb28c417551882bea6905714d20af29e215d53c43aa6388768ca10ec194217951843b66308764c610ea98a21da32443b064887cd4510f920a21f141443b662887c8c510ec98a21f131443a262887cc8510f810a215e53042baa6085e94010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x30000000069e00018400090002642238009600060829ca2049400004000000502716114143b1185420ca4c6254e4193594320870d540c821b118931c42c8624c610b118931442d1610c910b458e41442d1638c510b218931442e0624c510f0d8931442d0624c510f018931442c0624c510b4d8f21442b16408510b458c21443c03208510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x284c07258e4144260bb06410a21a05903208510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 143)*8) 8
  | 3 => packedAt s5K3 (840+((h/7+packedAt s5K3 (798+(h % 7)*6) 6) % 36)*6) 6
  | 2 => packedAt s5K2 (149+((h/1+packedAt s5K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf81ffc3fc0ffc21f1e1fc7f07ff0ff004dce7c
  | 1 => 0xffe0ffc3ff07ffe01fe1f8ff81ff0ffc72738f
  | 2 => 0xffff0003ffffffffe001ff0001ffffff8383ff
  | 3 => 0x3fff803fffffe000001fff003fc03f0
  | 4 => 0xfffffffc000003fffffffffffe000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x48c61a604e109603068ac1511c78991844c63c
  | 1 => 0x51422224823112200aa8486304998a28505285
  | 2 => 0x22884889144600cd20019204292224d183815a
  | 3 => 0x471cb33228a39b765ccc004a51ccc862fc03e0
  | 4 => 0x8410c00030c421989111248c600000832b2800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0feeee0c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36336
namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c180017fd50057f54017f95005fd54015f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4301ffd4801fe52007f54807fc52017fd0805fe42017f50805fc42007fcc801fe32007f4c801fc3201ffd4401fe51007f54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2101ffd4003fe50007f54003fc50017fd0003fe40017f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824001ff04120027fecb88012ff65c4009ff32e2003bf99710027facb88002fd65c4009fe32e2004bf19710027fec988012ff64c4009ff3262002bf99310027fac98801efd64c4009fe3262004bf1931003ffea98801f7f54c400fff2a62007ff5531003efaa98801ffc54c4009ffb1e2004bfd8f10027fcc788002fe63c4009feb1e2000bf58f10027f8c788012fc63c4011ffa9e2000ff94f10007faa788023fc53c400fffa1e2007ff90f1003ffa878801ffc43c4009ffb162004bfd8b10027fcc588002fe62c4009feb162000bf58b10027f8c588012fc62c4011ffa962000ff94b10007faa588023fc52c400fffa162007ff90b1003ffa858801ffc42c4001ff9962000ff8cb10007fa6588003fc32c40037f30e2004ffd4710027fca388013f651c4009fea8e2000fd54710027f8a388013ff41c4009ff20e2004fd90710027fa838801ff541c4009fe20e2004ffcc710027fc6388013f631c4009fe98e2000fd4c710027f86388013ff21c4001fb90e2004ff88710027fa4388013fc21c4009fa10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188003ff65440017fb2a2006ff9951001dfcca88003fd65440017eb2a2006ff1951001df8ca88017ff644400b7fb222005ff99110015fcc888017fd644400b7eb222005ff19110015f8c888017ff544400bbfaa22005ff9511002ffaa8880177d544400bfe2a22000ffd8d10005fec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2006ffd4d10007fca688003fd534400dfe29a2005ffd0d1002ffc8688017fd434400bfe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122006ffd4910007fca488003fd524400dfe2922005ffd091002ffc8488017fd424400bfe2122000ffcc910007fc6488003fd3244001fe1922001bfd8510037fea288013fe5144001fb28a2000ff54510007eaa288013fc514400bffa0a2004ff9051002fec8288017fd414400bfaa0a2004ff10510007fe6288013fe3144001fb18a2000ff4c510007ea6288013fc3144001ff90a2000fdc8510027fc4288003fd2144009fe10a2000fd0851000dfec088007ff504400dfda822001ff9411000ffaa088007fc5044003fc2822001ffd011000ffc8088007fa4044003fea022005fe5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044009fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fc314c001ff90a6000ff88530007fa4298003fc214c0037fb026001ffd413000ffca098007fd504c003fe2826001ffd013000ffc8098007fd404c003fe2026001ffcc130007f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff1026001ff0813000ffc2098007fa104c003fe082600bffd9720005fecb90037fe65c80077f32e4000ff59720005facb9002ffc65c80077e32e400bffd9320065fec990033fe64c80057f326400cff59320065fac99002ffc64c80057e326400cffd5320066fea990033fe54c8019feaa6400cdf55320067f8a99002fff63c80017fb1e4000ff98f20005fcc790003fd63c80017eb1e400bff18f20005f8c790037ff53c8001ff29e4000ff54f2006ff8a790033ff43c8019ff21e400cff50f20067f88790006fe62c801bffa96400bff94b20007dca590003fd52c8001f6a96400bff14b20067fe859002ffe42c8019f7216400cff50b20067da859002ffc42c8001ff996400bff8cb20007fa659002ffc32c8017ffb0e4000ff98720025fcc390003fd61c80017eb0e400bff1872006ffea390003fe51c8001fea8e400dff14720067fe8390033fe41c8019fea0e400cff10720007fe6390003fe31c8001fe98e4000ff0c72005ffe4390003fe21c8001fe90e400bff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff0864001ff04320007feca90002ff6548015ff32a4003bf99520007faca90002fd6548015fe32a4003bf1952004ffec890026ff6448013ff3224002bf9912004ffac890026fd6448013fe3224002bf1912004ffea8900277f5448013ff2a24009ff5512004efaa890027fc5448001ffb1a4000bfd8d20007fcc690002fe6348001feb1a4000bf58d20007f8c690002fc6348015ffa9a4000ff94d20007faa69002bfc5348013ffa1a4009ff90d2004ffa8690027fc43480037fb12400affd4920007fca490003ee5248001fea924000fb54920057f8a490027ff4248013ff2124009fb9092004ffa8490027ed4248013fe2124000ffcc920007fc6490003fd3248001fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520025f8c29002bff5148001ff28a4000ff54520057f8a290027ff4148013ff20a4009ff5052004ff88290003ff3148001ff18a4000ff4c520007f86290003ff2148001ff10a4000ff48520007f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024000fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0
  | 2 => 0x5009ffa84a804ffc4254001ff992a000ff8c950007fa64a8003fc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa004bf1855001ffea2a800ffe5154007fea8aa003ff1455009ffe82a804ffe4154027fea0aa013ff10550007fe62a8003fe3154001fe98aa000ff0c550007fe42a8003fe2154001fe90aa000ff0855000dfec0a8007ff5054007fda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fea02a001ff1015000ffc60a8007fc3054003ff102a001ff0815000ffc20a8007fc1054021ffb2e6000bfd9730097fccb9800efe65cc001feb2e6000bf59730087f8cb9800efc65cc021ffb266011bfd933008ffcc99800afe64cc023feb266011bf59330087f8c99800afc64cc023ffaa66011dfd533008ffca998047fd54cc023beaa66011ff1533000dfcc79804bff53cc021ff29e6000f794f30007faa798003dd53cc021fe29e6011ffd0f30087fc8798047de43cc023fea1e6011f750f30087f88798043ff62cc001ff3166000bf98b30007fac598002fd62cc021fe3166012ffd4b30007fca598003fd52cc025fe2966011ffd0b3008ffc8598047fd42cc023fe2166010ffccb30007fc6598003de32cc001fe9966010ff0cb30007b86598043ff61cc001ff30e6004bf98730007fac398002fd61cc021fe30e6012ffd4730007fca398003fd51cc025fe28e6011ffd073008ffc8398047fd41cc023fe20e6010ffcc730007be6398003fe31cc001fe98e6000f74c730087f86398003ff21cc001ff10e6000ff48730007f84398006fd60cc003ffa866001ff9433000ffaa198007fc50cc003ffa066001ff9033000ffa8198007fc40cc003ff1866001f78c33000ff46198007fc30cc003ee1866001ff8833000ff84198007fe10cc003fe0866000ffd9530005feca980037f654c0013fb2a600fff9953001dfcca98003fd654c0017eb2a600fff1953001df8ca980037c654c0073e32a600effd9130075fec89803bfe644c0057f322600eff59130075fac89803bfc644c0057e322600effd5130076fea89803bfe544c01dfeaa2600edf55130077f8a898006ff634c01fffa9a6000ff94d30007bca698003fd534c001eea9a600fff14d30077fe869803bfe434c01def21a600eff50d30077ba869803bfc434c001ffb126000bfd8930007fcc498003fd624c001fe3126000bf1893007ffea498003fe524c001fea92600fff14930077fe849803bfe424c01dfea12600eff10930007fe6498003fe324c001ef1926000ff4c930007f86498003dc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6004bf1853007ffea298003fe514c001fea8a600fff14530077fe829803bfe414c01dfea0a600eff10530007fe6298003df314c001ff18a6000ff4c530007ba629800
  | 3 => 0xeaa24219ff15121007fec690802ff6348401efb1a4200b7d8d21007fcc690802fe6348401feb1a4200bf58d21007f8c690802fc6348401ee31a4200b718d210d7fea690803fe5348401fea9a421aff14d210cffe8690867fe4348433fea1a4219ff10d210d7fea490803fe5248401fea92421aff149210cffe8490867fe4248433f72124219ff509210cfda8490867fc4248401ff9924200ff8c921007fa6490803fc3248435ffa8a4204ff94521007faa290813fc5148433ffa0a4204ff905210cffa8290813fc4148401ff98a4204ff8c521007fa6290813fc3148401ff90a4200fdc8521027fc4290813ee2148401ffb024200bfd81210c7fcc090806fe6048401feb024218ff1812100df8c09086bff5048431ff2824218ff141210cffe8090863fe4048433fea024218ff101210c7fc6090863fc3048431ff1024218ff081210c7fc2090813fc1048409ffb284204bfd9421027fcca1080efe6508409bf32842039f99421027faca10802fd6508409beb2842009f59421027f8ca10812fc6508409ffb204204bfd9021027fcc81080afe6408409df3204202af99021027fac810856fd6408409deb204200af59021027f8c810812fc640842bffaa04215dfd50210affca810857fd540842bbeaa04215ff15021027fec610812ff6308409ff3184200bf98c21027bcc610802de6308409feb184200bf58c21027bac610802dd6308409fe3184204bf18c210b7fea610803fe5308401fea984216ff14c210affe8610857fe430842bfea184215ff10c210bdfcc41085bff5208417ff2904200ff5482105ff8a410857ff4208417ff2104215ff5082105ff88410803ff3208401f7990420bff8c821007fa641082ffc3208401f61904204bf98421027fea210813fe5108409fea884204ff14421027fe8210813fe4108409fea084204ff10421027fe6210813fe3108409fe9884204ff0c421027fe4210813ef2108409ff1084204fd88421027fa4210813ed2108401fa9084204ffd8021027fcc010806fe6008409fd3004201be98021027fac010802fd6008409fcb004200be58021027f8c010806fc600842dffa804214ff940210a7f8a010857ff4008429ff2004215ff500210a7f88010853fe3008429fe1804214ff8802105ff84010813fe1008409fe0804201bfd955009ffec8a804eff6454027ff322a002bf9915009ffac8a804efd6454027fe322a002bf1915001ffea8a800f7f5454007ff2a2a003ff5515009efaa8a800ffc5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa000bf18d5001ffea6a800ffe5354007fea9aa003ff14d5009ffe86a804ffe4354027fea1aa013ff10d50007fec4a8002ff6254001ff312a000ff58950007f8c4a8002fc6254007ffa92a003ff9495001ffaa4a800ffc5254027ffa12a013ff909
  | 4 => 0x813f6310c409fe9886204f74c431007ea6218813ff600c409ff3006201bf98031027f4c018806fa600c409feb006200bf58031027f2c018802f9600c409fe3006201bf18031117fea018883fe500c441fe2806221ffd0031107fc8018887fd400c441fe2006220ff8c031087f86018883fe200c441fe1006204ff84031027f8201882fff65c84017fb2e421fff9972101dfccb90803fd65c84017eb2e420bff1972101df8cb9082fff64c842f7fb264217ff99321015fcc99085ffd64c842f7eb26420bff19321015f8c99085fff54c842fbfaa64217ff953210bffaa99085f7d54c842ffe2a6420bffd8f21005fec790803fe63c84017f31e4200ff58f21005fac79082ffc63c84017e31e421fffd4f21007fca790803fd53c843ffe29e4217ffd0f210bffc879085ffd43c842ffe21e421fffd4b2105ffca590803fd52c8417fe2964217ffd0b2105ffc859085fee42c842ffea164217fb50b2105ff88590803ff32c8417ff1964200ff4cb2105ff8659087fff51c8409ff28e4200ff54721027f8a39085fff41c8409ff20e4217ff50721027f88390803ff31c8409ff18e4200ff4c721027f8639082fff60c843dff3064201bf98321007fac190802fd60c8417fe3064201bf183210fffea19087bfe50c843dfe2864217ffd03210f7fc819085ffd40c843dfe206421eff8c3210f7f8619087bfe20c8417fe106421eff84321027f82190813ff65884097fb2c4204ff9962101dfccb10813fd65884017eb2c4204ff19621025f8cb10813ff64884097fb244204ff99221015fcc910813fd64884397eb244204ff19221025f8c910873ff5488439bfaa4421cff952210e7faa9108737d5488439fe2a44204ffd8e21025fec710813fe63884017f31c4204ff58e21005fac710813fc63884097e31c421dffd4e21007fca710803fd538843bfe29c421cffd0e210e7fc8710873fd4388439fe21c4219bf58a210effea510803fe5288401fea94421dff14a210e7fe8510873fe4288439fea14421cff10a21007fe6510803ef3288401ff1944200ff4ca21007f86510803ec32884097f30c4204ffd4621027fca310813fd5188409fe28c4204ffd0621027fc8310813fd4188409fe20c4204ffcc621027fc6310813fd3188409fe18c4204ffc8621027de4310803f72188409ffb044204ff9822100dfcc110813fd60884017eb044204ff1822100df8c110877ff5088437ff284421bff142210e7fe811086ffe4088439fea04421bff102210dffc611086ffc3088437ff104421bff08221027fc2110813fc1088401ffb2a4200bfd95210d7fcca9080efe6548401feb2a4200bf595210d7f8ca9080efc6548433ffb224219bfd91210cffcc89080afe6448433feb224219bf591210cff8c89080afc6448433ffaa24219dfd51210cffca890867fd5448433b
  | 5 => 0x9231025f8c9188a3ff548c451bfaa46228ff95231147faa9188a37d548c451fe2a46225bf58e3114ffea718803fe538c401fea9c6229ff14e31147fe87188a3fe438c451fea1c6228ff10e31027fec518813fe628c4017f3146204ff58a31005fac518813fc628c453ffa946200ff94a31007faa5188a7fc528c451ffa146228ff90a31147fa85188a3fc428c401ff9946200ff8ca31007bc6518803fd328c401fe1946200f70ca31025fcc318813ff518c409ff28c6204ff54631027f8a318813ff418c409ff20c6204ff50631027f88318813ff318c409ef98c6200fdcc631027fec118813fe608c4037f3046204ff58231005fac118813fc608c4037e3046229ffd423113ffca11889ffc508c451ffa046227ff90231147fa811889ffc408c44fff1846227ff0c23113ffc411889ffc208c409ff0846204ff04231007feca98802ff654c44dff32a6203bf99531007faca98802fd654c44dfe32a6203bf1953112ffec898896ff644c44bff3226202bf9913112ffac898896fd644c44bfe3226202bf1913112ffea8988977f544c44bff2a26225ff5513112efaa898897fc544c44dffa9a6226f7d4d31007fca698803fd534c44dfe29a6226f714d3112ffe8698897fe434c44bef21a6225ff50d3112fba8698897fc434c401ffb126200bfd8931007dec498802ef624c401ff3126200ff58931007f8c498802fc624c401f63126200bb18931137fea498803fe524c401fea926226ff1493112ffe8498897fe424c44bfea126225ff10931007fe6498803df324c401ff1926200ff4c931007ba6498803fc324c44dffa8a6204ff94531007faa298813fc514c44bffa0a6204ff9053112ffa8298813fc414c401ff98a6200fdcc531027fc6298813de314c401ffb026200bfd8131127fcc098806fe604c401feb026224ff1813100df8c09889bff504c449ff2826224ff1413112ffe8098893fe404c44bfea026224ff10131127fc6098893fc304c449ff1026224ff08131127fc2098813fc104c409ffb286204bfd9431027fcca1880efe650c409feb286200bf59431027f8ca18812fc650c409ffb206204bfd9031027fcc81880afe640c409feb206221bf59031027f8c818812fc640c443ffaa06221dfd503110ffca818887fd540c443beaa06221ff1503111dfcc61888bff530c421ff2986200ff54c31087f8a618887ff430c421ff2186221ff50c31087f88618813ff620c409ff3106200bf98831027fac418802fd620c409fe3106222ffd4831007fca418803fd520c445fe2906221ffd083110ffc8418887fd420c443fe2106210ffcc831007fc6418803de320c401fe9906210ff0c831007b86418812fe610c409ffa886204ff94431027faa218813fc510c409ffa086204ff90431027fa8218813fc410c409ff9886204f7cc431027fc6218
  | 6 => 0x7fea94a203ff14a5117ffe85288bffe429445ffea14a22fff10a51007fe6528803fe3294401fe994a200ff0ca51025fcc328813ff5194409bfa8ca203fdd4651027f8a328813f45194409ffa0ca204ff90651027fa8328813fc4194409ffb04a204ff9825100dfcc128813fa60944037d304a204ff58251005fac128813f960944017cb04a204ff1825100df8c12880fff5094407ff284a203ff1425117ffe81288bbfe409445ffea04a22eff10251177fc61288bbfc309445dff104a22eff08251027fc2128813fc10944097fb2aa22dffd915116dfec8a88b7fe64544057f322a22dff5915116dfac8a88b7fc64544057e322a203ffd515101efea8a880ffe5454407feaa2a22ddf5515101ff8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc63544017e31aa203ffd4d5101ffca6a880ffd5354407fe29aa22dffd0d5116ffc86a88b7fd435445bfe21aa200ffd8951005fec4a8803fe6254401feb12a200ff18951005f8c4a880fff5254407bfa92a203ff9495101ffaa4a88037d5254407fe292a22dffd095116ffc84a88b7fd425445bfe212a200ffcc951007fc64a8803fd3254401fe192a203bfd855101ffea2a880ff75154409ff28aa204df94551027f8a2a88137c5154407fa28aa22dffd0551027fc82a88b7fd4154409fe20aa200ffd8151005fec0a88b3fe60544037f302a200ff58151167f8c0a8806fc6054407ffa82a203ff9415101ff8a0a88b7ff4054459ff202a22dff50151167f880a88b3fe3054459fe182a22cff88151167f840a88b3fe1054409fe082a210ffd9731005fecb988affe65cc4077f32e6200ff59731005facb98843fc65cc4077e32e6210ffd933111dfec99888ffe64cc4057f3266223ff5933111dfac998843fc64cc4057e3266223ffd533111efea99888ffe54cc447feaa66223df5533111ff8a9988afff53cc457efa9e6210ff94f31007faa798843fc53cc457ee29e6223ffd0f31087fc879888fde43cc447fea1e6223f750f31087f88798843ff62cc401ff3166200bf98b31007fac598802fd62cc421fe316622bffd4b31007fca598803fd52cc457fe2966223ffd0b3111ffc859888ffd42cc447fe2166210ffccb31007be6598803fe32cc401fe9966200f74cb31087f865988afff51cc409ff28e6200ff54731027f8a39888fff41cc409ff20e6223ff50731027f88398843ff60cc455ff3066201bf98331007fac198802fd60cc421fe3066201bf1833115ffea1988abfe50cc455fe2866223ffd0331157fc819888ffd40cc455fe206622aff8c331087f861988abfe20cc455fe106622aff84331027f82198813ff658c4097fb2c6204ff9963101dfccb18813fd658c4017eb2c6204ff19631025f8cb18813ff648c4097fb246204ff99231015fcc918813fd648c4517eb246204ff1
  | 7 => 0x190cffc418c817ffb046438ff9823200dfcc119003fd608c8017eb04640bff1823200df8c1190e7ff508c871ff2846438ff1423219ffe81190e3fe408c867fea046438ff102321c7fc61190e3fc308c871ff104640bff082321c7fc21190e3fc108c801ffb2a6400bfd95321bffcca9900efe654c801feb2a6400bf595321bff8ca9900efc654c86dffb226436bfd91321b7fcc89900afe644c86dfeb226436bf591321b7f8c89900afc644c86dffaa26436dfd51321b7fca8990dbfd544c86dbeaa26436ff151321bffea699003fe534c801fea9a6437ff14d321b7fe86990dbfe434c86dfea1a6436ff10d321bffea499003fe524c801fea926437ff149321b7fe84990dbfe424c86dfea126436ff10932007fe6499003ef324c801ff1926400f78c932007fec299002ff614c801ff30a6400ff58532007f8c299012fc614c86fffa8a6437ff145321b7fe82990dbfe414c86dfea0a6436ff10532007fec099002ff604c86bff3026401bf98132007fac0990d7fc604c8037e3026437ffd41321affca0990d7fc504c86dffa026435ff901321b7fa80990d7fc404c86bff1826435ff0c1321affc40990d7fc204c86bff0826435ff0413205ffeca19002ff650c865ff3286403bf99432007faca19002fd650c817fe3286403bf1943205ffec8190c6ff640c863ff3206402bf9903218ffac8190c6fd640c817fe3206402bf1903218ffea8190c77f540c863ff2a06431ff5503218efaa8190c7fc540c8697f3186432ffd4c32197bea619043fe530c801fea986410ff14c32197b8a6190c7ff430c821ff2186431f790c3218ffa86190c7dd430c821fe2186433bf98832197fea41902ffe520c801fea90640bff1483218ffe841902ffe420c863f72106431ff5083218fda841902ffc420c821ff9906400f7cc83205ffc6419003ee320c801fe9906400f74c832007da641902fff610c801ff3086404bf98432007fac219002fd610c817fe3086432ffd4432197f8a2190c7ff410c863ff2086431ff5043218ff8821902fff600c861ff3006401bf98032007fac019002fd600c817fe3006401bf18032197fea0190c3fe500c861fe2806431ffd0032187fc80190c7fd400c861fe2006430ff8c032087f860190c3fe200c817fe1006430ff84032187f8201900efd6594409ffb24a204bfd9251027fcc92880afe6494409feb24a22fbf59251027f8c928812fc6494407ffaa4a203dfd525101ffca92880ffd549445fbeaa4a203ff15251027fec728813fe63944017f31ca204f798e51005bcc728813fd63944017eb1ca204f758e51005bac728813fc6394407ffa9ca203ff94e5101ffaa72880ffc539445fffa1ca22fff90e5117ffa87288bffc4394409ffb14a204ff98a51005fcc528813fd62944017eb14a204ff18a5101ffea52880ffe529440
  | 8 => 0xf1825201ffea12900ffe5094807fe284a43fffd02521f7fc81290fffd409487dfe204a43eff8c2521f7f861290fbfe2094817fe104a43eff842521f7f8212900eff655487bffb22a43dbfd91521effcc8a900afe645487bfeb22a43dbf591521eff8c8a900afc6454807ffaa2a403dfd515201ffca8a900ffd545487bbeaa2a403ff15152007fec6a9002ff6354801efb1aa400b7d8d52007fcc6a9003fd6354801fe31aa400bf18d52007b8c6a9002dc6354807ffa9aa403ff94d5201ffaa6a900ffc535487bffa1aa43dff90d521effa86a90f7fc43548077fb12a403ffd495201fdea4a900ffe5254801bf292a403ff1495201ef8a4a900fec525487bffa12a43dff909521effa84a90f7fc4254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa404bf1855201ffea2a900f7f5154807fe28aa43dffd05521effc82a90f7fd415487bfe20aa400ffd8152005fec0a90f3fe60548037f302a400ff581521e7f8c0a9006fc6054807ffa82a403ff9415201ff8a0a90f7ff4054879ff202a43dff501521e7f880a90f3fe3054879fe182a43cff881521e7f840a90f3fe1054879fe082a410ffd9732005fecb990effe65cc8077f32e6400ff59732005facb99043fc65cc8077e32e6410ffd93321a5fec9990d3fe64cc8057f3266434ff593321a5fac999043fc64cc8057e3266434ffd53321a6fea9990d3fe54cc869feaa66434df553321a7f8a9990efff53cc821ff29e6400ff54f32087f8a7990d3ff43cc821ff21e6434ff50f32087f887990efff52cc801ff2966400ff54b321dff8a5990d3ff42cc869ff2166434fb90b321a7fa85990d3ed42cc869fe2166410ffd8732007fcc399012fe61cc801feb0e6400bf58732087f8c3990efff51cc877fe28e6434ffd07321a7fc83990d3fd41cc869fe20e6410ffd83321d7fcc199006fe60cc801feb066400bf58332087f8c199006fc60cc877ffa86643aff943321d7f8a1990d3ff40cc875ff2066434ff503321d7f881990ebfe30cc821fe186643aff883321d7f841990ebfe10cc875fe086640bffd9632005fecb190e7fe658c8077f32c6400ff59632005facb1902ffc658c8077e32c640bffd923219dfec9190cffe648c8057f3246433ff5923219dfac91902ffc648c8057e3246433ffd523219efea9190cffe548c867feaa46433df5523219ff8a9190dafd638c873ffa9c6439f7d4e32007fca719003fd538c873fe29c6439f714e3219ffe87190cffe438c867ef21c6433ff50e3219fba87190cffc438c8637f3146439ffd4a3205ffca519003fd528c817fe2946433ffd0a3205ffc85190cffd428c817fe2146400ffcca32007be6519003ef328c817ffb0c6400ff98632025fcc319003fd618c8017eb0c640bff186321cffea3190e7fc518c867ffa0c6433ff9063219ffa83
  | 9 => 0x400000000600000800400000201c00001a00000000c03400e01000401802800c00a0a000400000000800c01600200200400000600000000001200200600001a00e00600000800400000000200c00400003201000402600800e01402600400003bf59653087fec92990eff6494c87ff324a602bf9925321ffac92990efd6494c21fe324a602bf1925301ffea92980f7f5494c07ff2a4a603ff5525321efaa92980ffc5494c077f31ca603ffd4e5301efea72980fdf5394c07afa9ca610ff14e5301fb8a72990fff4394c21ff21ca643ff50e53087f88729843ff6294c01ff314a600bf98a53007fac529802fd6294c21fe314a603ffd4a5301ff8a52990fff4294c87ff214a643ff50a5321ff88529843ff6194c01ff30ca604bf98653007fac329802fd6194c21fe30ca603ffd465301ff8a32990fff4194c87ff20ca643ff5065321ff88329843ff6094c85ff304a601bf98253007fac129802fd6094c21fe304a601bf1825301ffea12980ffe5094c85bf284a603ff1425301ef8a12990fff4094c85ff204a643ff50253217f8812990bfe3094c21fe184a642ff88253217f8412990bfe1094c85fe084a603bfd955320ffec8a9906ff6454c83ff322a602bf9915320ffac8a9906fd6454c83fe322a602bf1915301ffea8a980f7f5454c07ff2a2a603ff5515320efaa8a980ffc5454c077fb1aa603ffd4d5301fbea6a980ffe5354c01bf29aa603ff14d5301ef8a6a980fdc5354c83ffa1aa641ff90d5320ffa86a9907fc4354c01ffb12a600bfd8953007fcc4a9803fd6254c01fe312a600bf1895301ffea4a980ffc5254c83ffa12a641ff9095320ffa84a9907fc4254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa604bf1855301ffea2a980ffc5154c83ffa0aa641ff9055320ffa82a9907fc4154c01ffb02a600bfd8153207fcc0a9806fe6054c01feb02a640ff1815300df8c0a980fff5054c07ff282a603ff1415320ffe80a9903fe4054c83fea02a640ff10153207fc60a9903fc3054c81ff102a640ff08153207fc20a9903fc1054c077eb2ca40bffd92521fdfec9290fffe64948057f324a43fff592521fdfac92902ffc64948057e324a403ffd525201efea92900ffe5494807feaa4a43fdf5525201ff8a92902fff6394801ff31ca400bf98e52007fac729002fd6394817fe31ca403ffd4e5201ffca72900ffd5394807fe29ca43fffd0e521fffc87290fffd439487ffe21ca403bf98a5201ffea52900f7f5294807f7a94a40bff14a5201fd8a5290ffff4294817ff214a43fff50a5205ff8852902fff6194801ff30ca404bf98652007fac329002fd6194817fe30ca403ffd465201ff8a3290ffff419487fff20ca43fff506521fff8832902fff609487dff304a401bf98252007fac129002fd6094817fe304a401b
  | 10 => 0x222f147143c2fa2512f488cd0740ce38d8e248e263330703cc00614800200000600400400201000600200200000403000001000a00401601c02800800400200000000001000802000203200601600400602002800200a00000000000000000004c00600e02e00002c00e00200400600000600003a00400601200000200000400201600000200802805200e01401603c05c01401400202000200200600202201200402000000e00000000600002200600a00009200600401c01008200600401800000000200002400000a00000000000006000400000a00602800400000c00a00000000202200600000001c00000400000000800600e00000802c00000800200600000c00801800202c00400000000000600c00000001600400002204601e00001000e00000000200601200a00202004200400801e00000202e01c00400e00c01800200201a00400201003c00a00802e00c00c01000001000401c00a00002600404204400e00c00000c00a02600001200000001800a01000000200a00201000800000600e00c01600000000001200201a00200002200000a00000600600c00000c03000400e00800400001800200002800400004603000000400604001000000000200400601002400000400800400000200200200600002200600c04400000600001602600400800c00e00000200801c00600400000400e02e01601400000a00200801600000800000e00e0000ae00200e00000400a00000c00c01400200400a00400000000a00600e0000020140060000ee00003a00000000002000200200408a00000c00600400000802c01600000000a00001600202600002c00000000000c00a00a00800400800000000200402400800400a00c00a01600e00a00000000c00600200200600a00000800000203400800000203400600200400200802e00000200c00000000c00600400c00000600600000a00800800000400000000000e00000401201a00c00200002001a00a03202802600600400001800400001413208e00600000000400000000411600203200000403c00000e00200001000005800a00401600a00001200000200000400200602200400000200200800002200000203c00802e00200400000601000002a00200400400a01200202800005a00400000000200001c00401400006a00401a04400000200400000000002601c01802c00000200200e00200600600000200001000000400201401a01401800400600000400200000a00002800000204200800000201601600c00200000c00800c00400001200000001600400001200603e00201002800c00c02c00000200000602400002801000001400000000200c00400000600200001a00e00800203200800400a00000a00c00200403400200a00203200001600000000800000200800200e00000401a
  | 11 => 0x20644ae421311fa1080002470dd9d2447a00000000009400b0000000000000000005200002dd0001cacbea02f0a19ff055a5fa0701b8894a00043621342f65cf3e505e00b614c12c0858afa00039721810f81160ba1bc8cde00042a9ca80000320e100008880cc2d0800011828c00000004fc00000001a883a7d1000015c1e05f11161d6007e57e179853c2542b83ce8e805928391e109d40005362238000e0c18f031804c0007422c10000f000000000000000580000074c14c2d9250806068c46114b11302d28700b19d34e4e2a012d9b4c1044ad1ec13546428223858a8480e000008886ce580001391438e960001a420280000000001d3d0d41fb1f58178a7c48603fa19d0f07f92330cf88ee454071908087621e1b5944c75e3441d5189848872f3350c2842e15437880004f64f020d915cc500002f696d47ac5043ad893c01e7ed229000000e0150381404c3e00029201ec3f40004248b9800022a415128800004300000000000960a801044e800012e013400000024f1cf80001572cc9a350dc1803d419786dc0991e29ad4a702f21430a7c6ba46c251a060c7e0d73f79e0865e0612ba0068bca3fd3b213384206f442408b85465192318d5c2061f80e00ac04686553408000f1e7cf1be920c0001012880000000716000000000000002500000000db3b89c3006e69b00000000000a514795b4f481972699e7817c0000001fc46ec38100005844ca29523a10b00006c220300000000000ce8decea8000000000000000000010dc00016a000000000052132698487505a73b5800000002100000000003c40001a140000000000000d8600000000006ee000276000000000000014e41fe0000399d980000003cc000000c00043d9c54de65341ee8000a1602500d8000fac0b337f000022200036b8d24aba1923ae8000dc85b422f014865864918d86ccda47df1c183a8d8a00000000005c8379000000000000000007bc0000000002110f8c65d38283b48a20003f9961c45079b00011a06d43bf1cb17fc5082d104a85d41d048b12913a800040a00000000000002b12100a2a76d2a19a0cb3e4d42538fec12071140b12303fa00000015d800000000000002be03900000d0aa812b2801a2c00077d3da14680008280c11380d9660a02593ac5a83c338e17a08343c61b49ec81c20e73890000c486e30d2800100200000018a400011700000000000383df1e281d624e1229aec2265eb1b1800000011a000214c9c248910c8cf40000d92b4060c0005a52c280001ba5e70000000000000434157897a37c3309e4406a4fb42e83b8e2886b166000062080d249992c7e612439e000025c31e0000974b20152000092c0008513ab000070058c09f9334000000131080c10c5713a1831857a0000001188cac37a06089e020405c15917906123ee000071884
  | 12 => 0x182a70000000a4441400c875467036c34b178405a1674188000db864409c91c8f7e1a82f0099864c2681bc06f844a78c0181f70d881e80001ed8dbe4790e09a6400000022f800000000009180000006db30580005224c40681a94fa017143f12c0a4c5dc1a89b74a1854c400041840e15c00000000000003b01c9072a5f03bc962479a00000011380005a337480000000003371c4000000000000000785c8000180c00000000000000001db00021d000016636c00000000000000bbcca206916d8748fc679c000000000000000000000000000001ea400000537f80006540003118b3cdfa702000028c116000364800095c27d0ee1558af45310cd94e8e902930008790f4000035e9260e724531a2850871a40417a0b150940f537012e86ca7e631d80006fe30010c00004a81ee0001c4c5ca0a700001f00001770000684bbc6ef4349eed03e0003d2800000072300000004dc297000126d00c40905d02b827610d0c48aa012e3e70a8a08c3160923d3890821030624b89dc1d800014280000004151cf80010680c444200b07f817a2a5a05c0de48d10100004345b20000d3c6802fa2e6935c41863200020b0f740000138000a9c0df3f20bc062e00032c80001d22be0000eac6a488524a194cfb00002b98000fb40ad41392f037846a0eb9b551182063ab92f853a0a42ca96d85fa56e2081f7818443824c9ee01ca29442d1cc0cc04050a31328c105c928b8b04e140002bc0000b4c0e200013b40001cc4438e6c27c0762f50000c600493008eb800067000002dc1fa0003260a949385b000001c8000000000069c84e00000000009b400027e00000e83a92091de800082f0000000000000000034cec647e115800000000000012c4efc26a134a008f6a26712d0ed8b7c01c02e8f8c0003ad295a164b6606e15d8e40a587b30000000cb647f0000430d468123940c94cce0000b1000091c16817891b872676e02b174003e0461a680000006bf17b0c60bb20001b380010382ae2c19b205c20000000e3c0002fb2fe19ad0f45c644820440008651bf07440004551eb90cc1520001878c309020911149eb800000029810307f05912fc8f3853228131b88ecdcc00b2bc96200121e0281188486c6864129d94a5c4d210004cc9f27fd3b40c7437067e0f1921071816019480744245d20948ce80006074101ebc5ae5ac1dd1ea8cf833f1c89a607700003cb800042a7a331b0ef42e4000000000000000000004400000002e080000003940a588440000fb1ea9c04000476000000035e1d4000203c5a40002e11f6c00049f35d0d88b7014e41915983383d101b1b50f9c4af376899027a70d40f095416a46d3e185246de39c3d898504860001fa87d4cc64b22a019609484911b300004166be39e96a835818c29198547586e50000000b0c88800000003140000b
  | 13 => 0x71a807de1b50171070b525bd37c14a805200000014748726743b98000f2056b05c06e80006d00001f5cc563023fd888400043e15311ac9fe4732770f1c8d24c500008f10601bd079104cd8e0000000000eec00014f0000a307d5279937ca2c7501ce82f056262d2900aa81c81440c99ba0ab27720001d840004410221a1000000000005cc82e15941b000090059d01d8000e4a230151000023a00027b083424e00000007f800010538c80007b252d05f990cf5a000000000032c45d32403580000002561c84c5e00000184d40003cb06d00000005c721581380000002a68000ede66d33a800000058a0ec9428d8000000000000001a30001e58d2e3e03ba1ba8a367bc1ba0ce4f280000011e68d380002ab972c5c000025b800072e6820001cdc0007b90f28dc000074a00011bc890000339184cac62e23bb8cb41120000001678ebe48f0479864d141de13007acc3c7b02a28a0046c0880000ed02626e71c907e49843e10f88fdc30a0933f096b88f054809902c800020400021140002820001fb8fea3f90040028d1e0000940234f0e8372929510000000085000111233107a00000500400000920ef64e416d07c826e21d0330e1c5aa00000015409867f6000000000000018d17e000000000015f00000002429b845f00000fb80010820e627d0e6437e13c3fc0b4041e7c90878b0842870f22d93944721562a090648c03c81d38478fe00ab07e15183e80682869038d8c56514d959c0ee5082550270e3c54f31a89acade00000020a47c86f73e68f250c40000b29e7cbe88803028c7c2dc80300019ccd50350000000000036d00006ac0001a000015248100003c400007b43120a6989c23000000008c8afe00000022281b000029d9a684406d906400000000002ad00007e40714390000000313000042c0006091d996340005e61e6000056814a31292748460000000000cae7ab30d032400083c3a280000000cf2dd9a2044e5fb1601cccb241e71cc1114c0c63815e01b10ae00035201b4fd06b21a7199423650615a83005c614539a90c40002311f89c7400042418a800107a00023d0d680aa72d22c8114cbe76a0ca000004600006e0578d2464a43c935850609422519b0c1e3e219a0000000000000032c0000000000000baa691184000056e69511c1098a4e57719b96fc0203fa000161000044d00020fc00000000012d800003d0000000666678000054c2320002168000000000000000074a0001c3000002e5d600000002da42932d121cfd200030b800000000000010bc2246c100000006ea00000012544c26790090038ec45c41828e68ad40f839d910c3a02ff2f11ad866068e35c0f280b401406a8c88f426110db9918ddc6932ac17609f07671a09e1066a35e2ad8724d6835c43b211c8ea0b90000d809fa67b40a223830c00037d80000
  | 14 => 0x4e23e8167201cb566ae24b0b0c05474c12b94f51160af06386d8b7433b0c686c8c9e2b31360d6c96882b17c8b210e63472db894cd3c2f703e8bf00485f60628f5107611c1eda2051044b9393020415870422b113ccc47460f502d815418e1122010a6e1b936b0f9453863d12c8a905960f12cd140d0ac40f2a91ffd05a5962088fa862861d03a9fa901240d15f8f0104c04c4171900bfa00025597c8ffc084000000056c00000000001860ca0f098f04ec15b02100003200001759750eb20000001e640663ed00200010186ce18b00000006683c58000000425000073caaa83e0d4964c000000000000000067705000005165b93ad163c38a81b0cc96f10cc3f624118e4dec84c0001660b165ce25f84800001042010000f025c50001bf085000000012d4d5853c00019986e60a11260000c7c5ee000017c48c000332022800066900000004f83190429bc0000560000166ceb862023e1108e824cc0690000bae2df000000000030127b80010260602998000c302ba32085f87606aa0c40c34a520000000000cf40000fb02380000002e8800068670800002ec00088f13f96bc9242011548000000000000000000000020b2074f1244b0000000c380000000e100006500000e380000620158c910bc0000000000f246cc21a0a24d607cb1ab1cd876a2e900b000086a00000021f47b843a07b8814a503361e09a50000000000122838671725d819474c0000e51eb05dc00018713bc1f209d0ca9d48aa22d33bc00003da0002f780000007d238c1768e700a241088d4fd80000000870aa60003f100008000000001728000600431800096629212f9b440ce00000021d40004a82600ca063800020199c47761382b480005ac4e811d20410da1fc0b59c0c0000000aa88389cc0001d88698000000091213c0a022324402d0cfa4c822e07a40006a227f0fd049a7fa0241a1c44c34c26084540000002680ef90a47700da02789d267f0001424f8e0000a398401bc170058939cdf284e0000000000000000132421c000000210c00017f00000000003722d89c802ba6de000000000000000016383cc0001c50b9cd526f5419800060688315600004807e70000000d5e1250000d540d6000066800000023723800008b428d00002690961ec2a504b0af669d00007fc00000005e90785721ce155a1bc00028743ba140fd6507000119c5d83710b60ff82f200039498350323df0001060e8e51441c04b4abe00021e978c49200000000009b888d3a99e347647b738d1cc80000221d100e8e7444042a132c3344f242d800076e6ec09d0b346168862d10824e6800000014c887885c083867c0004f500000002f834a38f9a000000fa3b493745fc7852a112e007c4f109792680b208723e9378ca886400018a8b5000000689e8e445cc0a01d38000359190193883e0514
  | 15 => 0x6163061cc4a7e0003d10fc00000000000f788644d80000000000000000016000000029780005b800003200c47420000000b10b860540c080006a622d3539c1cbd87c810418b0000581000000000000026c8e8c00046543080000f283523d81e800000000000007040003a00c8cb3819813683bcc6211f0e21680ba639e3ca944900a0f61f310b85bc60234490fc8545643e989e4f987513171f74c8469f33b075867819e3589d109525df26d8d60d2028a2181cfc66455c000000035a4f400019700006bc1b20d0869601e10fa160eaa6a13e21f04f261dd00000005d46ca00000000000000d80000bb60000001140b800001110ee46d01aa4230e2c13e0d400000000003270001650000000080205409e51e3e012982b00001e98c100000000f80000ef863a2ba877c55e1873569fc88020474388424d9e61b0930568d6e2ed3c700006be77f3c31160fe835424803440a600000000002681cb00000000007753b60ba00001a40000000130000282933c000000311000079e7bd2b606b80001da0001f945201d80001ae40005970f1000058e1a23e10bd4fc023e232026cfb24e21958d844146fa36d1c2451085f0d89a30bee0001e8151cb5a75e1c41e9898c7f71ff977465c81a05407ccdd66470bb0000a6a2413e28b285308081251444a3e6040400b189c66ab0a084c0c8a40b08a073504851c138020cbe64d12b80e90e1c4222ff18d02de87f1f48fb04e66a60e39e0c7a4184131994898e7d4128008088c25603f202c5b05a41de0c441fc700013048453425e13784d8d9a38518381e08921c82b09acc
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7604c510027f3604c51027ff3504c510127f0504c510127f2404c510277f1404c510127d7304c510127f2304c510127d5304c510127f2204c51000cfe76c851000cfc76c8510006ef62c851005eec62c851000dfa70c8510005f970c851000df676c85100f6f676c851000cf676c8510005f775c8510005f575c851026df774c851026df574c851025f7754c851025f7554c8510005f773c8510005f573c8510025f672c8510006f762c8510007e762c8510006f562c8510007e462c851025fe642c851025fe542c851000df670c85100f7f270c8510007f170c851000df470c8510026f760c8510027f360c8510267f350c85100f7f050c85100f7f240c851025ff140c85100f7f230c85100f7f220c851005cff764851000cfe76485100c4fd764851000cfc7648510005df7348510005dc7348510006ef6248510006ec6248510005fb704851000df870485100ddf67608510026f67608510025f77508510027767508510005f57508510027757508510005757508510025f77408510027b67408510255f57408510027b57408510005b57408510247775408510247755408510025f77308510027d67308510005f57308510027d57308510005d573085100f5f67208510027e67208510006f76208510006f56208510007e73208510007e4320851000df67008510027f2700851000df27008510027f1700851000df47008510026f76008510027f3600851024ff350085100a7f050085100a7f24008510247f140085100a7f230085100a7f22008510025f8764c110006f8764c110024f8764c1100077b754c110035fa754c110035f8754c11000778754c11003578754c11023dfb744c11023df9744c1102377b544c11023779544c11000dfb734c11000fdb734c110007db634c110086fa634c110086f8634c110007d8634c110007da534c110007d9534c110237da434c110237d9434c110005fb724c110007da324c110007d8324c110007f3714c110025fa714c110025f8714c110007f0714c11000efb614c11000ff3614c110007f2514c110007f1514c110237f2414c110237f1414c110007db314c110007f2314c110007d9314c110007f1314c110007d1314c110007f3214c110007f0214c110025f87648110006f87648110024f87648110035fa7548110035f8754811022dfb744811022df974481102277b5448110227795448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811005efa624811005ef86248110007e86248110007ea5248110007e95248110227ea4248110227e94248110007f37148110025fa7148110025f87148110007f0714811000efb614811000ff36148110007f25148110007f15148110227f24148110227f14148110007f23148110007f13148110007f32148110007f02148110
  | 1 => 0xc910006ef62cc910006ec62cc910025f671cc910005f571cc91000dfa70cc910005f970cc91005cff768c910004fe768c910004fd768c91005cfc768c910006df638c910006dc638c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910005f7714c910025f4714c91000dfa704c91005cff760c910004fe760c910004fd760c91005cfc760c910006df630c910086dc630c910006ef620c91005eec620c910025f6710c910005f5710c91000dfa700c910005f9700c9102c5f67694510026f67694510165f5759451001ef6659451001ef46594510025f774945102bdf574945100377754945102b7755494510027d67394510005f57394510027d57394510005d57394510005f6729451000df67094510027f2709451000df27094510027f1709451000df47094510026f76094510027f36094510037f35094510177f05094510177f240945102b7f14094510177f23094510177f2209451001cff765451000cfe7654510164fd765451000cfc76545100067f655451001e7c6554510005fb705451000df8705451000df4765451001ef4765451000cf47654510025f7755451002777755451000777655451001ef6655451001ef465545100377465545102adf774545102adf574545100377754545102a7755454510005f77354510005f47254510037775254510007755254510007f3705451000df6705451000df47054510167f07054510026f76054510027f36054510037f35054510167f05054510167f240545102a7f14054510167f23054510167f2205451000cfe76cc51000cfc76cc510006df63cc510086dc63cc51000dfa70cc510005f970cc510105f6768c510026f6768c510025f7758c510005f5758c510025f7748c51029df5748c51028f77548c51028f75548c510125f5738c510086f6638c510086f4638c510005f6728c510007d6328c510007d4328c510027f3708c51000df6708c51000df4708c510027f0708c510026f7608c510027f3608c510297f3508c51013ff0508c51013ff2408c51028ff1408c51013ff2308c51013ff2208c510084ff764c51000cfe764c510124fd764c51000cfc764c510006df634c510006dc634c510005ef724c510005ec724c510027d4314c510005fb704c51000df8704c510027f0104c51000df4764c510126f4764c51000cf4764c510005f7754c510005f5754c510285f7744c510285f5744c51027777544c51027775544c510025f7734c510027d7734c510007d7634c510086f6634c510086f4634c510007d4634c51027fd7534c51027fd4534c510277d6434c510277d5434c510007e7724c510005f4724c510007e4724c510005e4724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c510127f0704c510026f
  | 2 => 0x4ef7258d1005cfc7258d10006ec7258d10004ec7258d10154ff7158d10006f77158d10124ff7058d10006fb7058d1013cfe7618d10006dd6318d1001cfe7518d10004fd7518d10084fc7518d10084ff7418d10014fe7418d10004fd7418d10084fc7418d100067f5418d100067d5418d10086de7318d1005cfe7218d10004fd7218d10024fe7118d10086f57118d10024fc7118d10024ff7018d1000cfe7018d10024fd7018d10086f97018d1000cfc7018d10086df3018d10086fa3018d10106dd3018d10084ff7694d10004fe7694d10004fd7694d10084fc7694d100067f6594d1001e7c6594d100375f5394d10025f67194d10005f57194d1000dfa7094d10005f97094d10217785094d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10005fb7054d1000df87054d1001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d8910084fe73d8910004fd73d89100def571d8910024ff70d8910024fd70d89100deef20d89100deed20d8910006ef62989100c5f5719891001cfe7598910004fd759891005cfc759891005cff7498910014fe7498910004fd749891005cfc74989100067f54989100067d5498910084fe7398910004fd739891005cfe729891005eee4298910006ed42989100c4fd719891005ef571989100f4fd709891005ef9709891005efa20989100057f75589100357c7558910005bf745891002dbc7458910005df7358910005dc73589100f5f77158910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df7358910084fc7358910006dc7358910004dc7358910006ef7258910006ee4258910006ed42589100f4ff7158910006f771589100c4ff7058910006fb70589100dcfe7618910006ed621891001cfe7518910004fd751891005cfc751891005cff7418910014fe7418910004fd741891005cfc74189100067f54189100067d5418910084fe7318910004fd731891005eee7218910024fe7118910024fc7118910024ff701891000cfe7018910024fd701891005ef9701891000cfc701891005eef201891005efa20189100a6ed201891005cff7694910004fe7694910004fd769491005cfc76949100067f659491001e7c659491000dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc7654910005df7354910005dc7354910005f77154910025f47154910005fb705491000df87054910084ff76cc910004fe76cc910004fd76cc910084fc76c
  | 3 => 0x46554710305f77454710305f574547100477754547102ff755454710005f77354710005f4725471004777525471000775525471000df6705471000df47054710025f7764c710006f7764c710005f7754c710005f5754c7102f5f7744c7102f5f5744c7102e777544c7102e775544c710027d7734c710027d7634c710086f6634c710026f4634c710027d4634c7102efd7534c7102efd4534c7102e7d6434c7102e7d5434c710007e7724c710005f4724c710007e4724c710005e4724c710007d7324c710007d5324c71000df6704c71000df4704c710127d7304c710127d5304c710025f576c8710006f576c8710005f775c8710005f575c87102ddf774c87102ddf574c87102d77754c87102d77554c8710005f773c8710005f573c8710027e672c8710026f762c8710006f562c87102d7e642c87102d7e542c871000df670c871000df470c871001cfe76d95100367e65d951000dfa70d9510025f970d95100377b50d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100367f54d95100067d54d9510084fe73d9510004fd73d95100367c53d951005cfe72d9510004fd72d95100367c52d9510024fe71d951000cfd71d9510024fc71d95100367f51d9510024ff70d951000cfe70d9510024fd70d9510036f970d9510024f970d951000cfc70d95101767f50d9510036fb50d95101767d50d9510176f850d95100367c65595102cdf77159510174ff75595100067f7559510004ff7459510014fe7459510004fd7459510014fc74595100367f54595100067d5459510004ff7359510084fc7359510004ff725951005cfc72595102ccff7159510006f77159510164ff7059510006fb7059510036fb5059510166f8505951001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d1005cfe72d8d10004fd72d8d10024ff70d8d10024fd70d8d1013edf30d8d1013edd30d8d10006df6398d10125f57198d1001cfe7598d10004fd7598d10084fc7598d10084ff7498d10014fe7498d10004fd7498d10084fc7498d100067f5498d100067d5498d10084fe7398d10086de4398d10006dd4398d1005cfe7298d10004fd7298d10124fd7198d10086f57198d10154fd7098d10086f97098d10086fa3098d100057f7558d100357c7558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d10155f77158d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10006df7358d10006de4358d10006dd4358d10004ff7258d10006ef7258d10
  | 4 => 0x971001cfe7598f10004fd7598f10084fc7598f10084ff7498f10014fe7498f10004fd7498f10084fc7498f100067f5498f100067d5498f10026de7398f10006df5398f10086dc5398f10086de4398f10006dd4398f1005cfe7298f10004fd7298f1000cfe7198f10026f67198f1000cf67198f1000cfc7198f10026de3198f10026f63198f10026dc3198f10086df3098f10156dd3098f10004ff7558f1001cfe7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10026df7358f10006df5358f10006dc5358f10006de4358f10006dd4358f10004ff7258f1005cfc7258f10024ff7158f1000cfe7158f10024fd7158f1000cfc7158f10026de3158f10026dc3158f10126df3058f10126dd3058f10026fa1058f10026f91058f10084ff7694f10024fe7694f10004fd7694f10024fc7694f1001e7e6594f100067d6594f100475f5394f10025f67194f10005f57194f10004ff7654f10024fe7654f10004fd7654f10024fc7654f10025f67154f1001cfe7598b10004fd7598b1005cfc7598b1005cff7498b10014fe7498b10004fd7498b1005cfc7498b100067f5498b100067d5498b10084fe7398b10004fd7398b10026ee7298b1005eee4298b10006ed4298b1000cfe7198b1000cfc7198b10026ee2198b10026ec2198b1005eef2098b100f6ed2098b10004ff7558b1001cfe7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b10006df7358b10004df7358b10084fc7358b10006dc7358b10004dc7358b10026ef7258b10006ee4258b10006ed4258b10024ff7158b1000cfe7158b10024fd7158b1000cfc7158b10026f47158b1000cf47158b10026ee2158b10026ec2158b10026f42158b100c6ef2058b100c6ed2058b10026fa1058b10026f91058b1005cff7694b10024fe7694b10004fd7694b10024fc7694b10025f47194b10004ff7654b10024fe7654b10004fd7654b10024fc7654b1001e7e6554b100067d6554b10005df7354b10005dc7354b10005f77154b10025f47154b10084ff76ccb10024fe76ccb10004fd76ccb10024fc76ccb10086de63ccb10006dd63ccb10025f671ccb10005f571ccb10327e421ccb1005cff768cb10024fe768cb10004fd768cb10024fc768cb1031edf638cb1031edc638cb10025f4718cb1031fd6318cb10004ff764cb10024fe764cb10004fd764cb10024fc764cb10006de634cb10006dd634cb10005f7714cb10025f4714cb1005cff760cb10024fe760cb10004fd760cb10024fc760cb10316df630cb10086dc630cb10025f6710cb10005f5710cb10317d6310cb10317e4210cb10025f7765471030ef7765471002777755471001ef66554710026f
  | 5 => 0x5df7354920005dc7354920005fb705492000df8705492000dec765492001eec765492000cec76549201f5ef75549200076f75549200076f655492001eee655492001eec65549200576c655492033def745492033ded74549200576f54549203376d5454920007cf7354920007cc73549200576f5154920007eb705492000dee705492000dec70549201e7e870549201e6ef60549201e7ea105492000cfe76cc92000cfc76cc920006df63cc920086dc63cc92000dfa70cc920005f970cc920184fe768c920006de638c920006dd638c920084ff764c92000cfe764c9201acfd764c92000cfc764c920006df634c920006dc634c920005fb704c92000df8704c9201c4fe760c920086de630c920006dd630c920024fe76d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d8520084fe73d8520004fd73d8520006ee42d8520006ed42d852000cfe70d852000cfc70d85200f6f710d8520006f761985200057f75585200557c7558520005bf745852004dbc7458520005df7358520005dc7358520005de7318520005dd7318520026f66118520006f56118520004fe7694520004fd7694520024fc76945200067f659452001e7c6594520005de7394520005dd739452000dfa7094520005f97094520004ff7654520004fe7654520004fc76545200076d5254520004fe76cc520004fd76cc520084fc76cc520086de63cc520006dd63cc520004fe768c520004fd768c520024fc768c520006df638c520006dc638c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520006de634c520006dd634c520005ef724c520005ec724c520004fe760c520004fd760c520024fc760c520006df630c520086dc630c52000dfa700c520005f9700c5200a4fe76c852000df870c852000cfe7688520006f76188520026f4618852000dfa7088520005f9708852000cfc7648520005df7348520005dc7348520006f76148520026f46148520005fb704852000df870485200f4fe76085200557e75085200057d750852004dbe7408520005bd7408520005de7308520005dd7308520026f6610852000dfa700852000dfa76c812000efa76c812000cfa76c812032f7b54c812032f7954c812000dfa72c812000fea72c812000efb62c812000feb62c812005fea52c8120007e952c812005fea42c812032fe942c8120005f971c81200267f7559710004ff7459710014fe7459710004fd7459710014fc74597100467f54597100067d5459710004ff7359710084fc73597100467c5359710004ff725971005cfc72597100467f5259710024ff715971000cfe7159710024fd715971000cfc71597100267e51597100267c51597101667f50597101667d505
  | 6 => 0xd76887200dcff7648720005df7348720005dc734872001cfe76d95200567e65d9520004ff74d9520014fe74d9520004fd74d9520014fc74d95200567f54d95200067d54d9520084fe73d9520004fd73d95200567c53d952005cfe72d952000cfd72d952005cfc72d95200567f52d9520024fe71d9520004fd71d95200567c51d952005cff70d95201f4fd70d95201f67f50d95201f67d50d95200567c6559520005df7359520005dc7359520365ef72595201f4ff75595200067f7559520004ff7459520014fe7459520004fd7459520014fc74595200567f54595200067d5459520004ff7359520006df7359520004df7359520084fc7359520006dc7359520004dc7359520364ff7259520006ef7259520004ff7159520024fc71595201e4ff7059520006fb705952001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d20006df53d8d20006dc53d8d20006de43d8d20006dd43d8d20024fe71d8d20004fd71d8d2005cff70d8d201c4fd70d8d201c6df30d8d201c6dd30d8d201c6fa10d8d20006df6398d201aded7298d2001cfe7598d20004fd7598d20084fc7598d20084ff7498d20014fe7498d20004fd7498d20084fc7498d200067f5498d200067d5498d20084fe7398d201acfd7298d20086ed7298d20006ee4298d20006ed4298d20024fe7198d20004fd7198d201d4fd7098d20086f97098d200057f7558d200557c7558d201d5ef7258d20004ff7558d200067f7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20014fe7458d20004fd7458d20014fc7458d200067f5458d200067d5458d20006df7358d201d4ff7258d20006ef7258d20004ff7158d20024fc7158d201acff7058d20006fb7058d201aefa1058d201c4fe7618d20006dd6318d2001cfe7518d20004fd7518d20084fc7518d20084ff7418d20014fe7418d20004fd7418d20084fc7418d200067f5418d200067d5418d20086de7318d20006df5318d20086dc5318d20086de4318d20006dd4318d2005cfe7218d2005cfc7218d20006ee4218d20006ed4218d20024fe7118d20004fd7118d2005cff7018d20184fd7018d20086df3018d20186dd3018d20084ff7694d20004fe7694d20004fd7694d20084fc7694d200067f6594d2001e7c6594d200575f5394d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2035cfe769492035dee7694920356ee76949201e5ed759492001eee659492001eec659492034def749492034ded74949200576f54949203476d549492000dee709492000dec709492005eef60949201f7ea109492001cff765492000cfe76549201e4fd765492000cfc76549200067f655492001e7c6554920
  | 7 => 0x8f200067d54d8f20006de43d8f20006dd43d8f2005cfe72d8f2005eee72d8f20024fe71d8f20004fd71d8f2005ef970d8f201acfd7698f2005edf6398f2001cfe7598f20004fd7598f20084fc7598f20084ff7498f20014fe7498f20004fd7498f20084fc7498f200067f5498f200067d5498f2000cfe7298f2000cfc7298f20006ee4298f20006ed4298f2005ede3298f2005edc3298f20024fe7198f20004fd7198f20086df3098f201d6dd3098f2005edc6358f20004ff7558f2001cfe7558f2001cfc7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f200067f5458f200067d5458f2005edf7358f20084ff7258f2000cfe7258f201acfd7258f2000cfc7258f2005ede3258f2005edc3258f20004ff7158f20024fc7158f201aedf3058f201aedd3058f2001cfe7518f20004fd7518f2005cfc7518f2005cff7418f20014fe7418f20004fd7418f2005cfc7418f200067f5418f200067d5418f20084fe7318f2005ede7318f20086de4318f20006dd4318f2005cfe7218f2005eee7218f2005eee4218f20006ed4218f20024fe7118f20004fd7118f2005ef97018f20084ff7694f2005cfe7694f20004fd7694f2005cfc7694f2001e7e6594f200067d6594f2006f5f5394f20004ff7654f2005cfe7654f20004fd7654f2005cfc7654f2000ded7694b2005eed7694b2000ced7694b2001eee6594b2005f6e6594b2005f6d6594b2005eec6594b2005def7494b2038ded7494b2006f6f5494b203876d5494b2000dee7094b2005fea7094b2005fe97094b2000dec7094b20364ff7654b20005df7354b20005dc7354b20365ef7654b2037eef7654b2005f6f7554b2001eee6554b2001eec6554b20375ef7454b20375ed7454b2006f6f5454b2036f6d5454b20007cf7354b20007cc7354b2006f6f5154b2000dee7054b2000dec7054b201acfd76ccb201d4ff764cb2005ef76198720026f46198720024ff765872005ef46158720004ff755872001cfe755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc74587200067f54587200067d5458720004ff7358720084fc735872000cfc7258720006ee4258720006ed425872005ef7215872005ef421587200c6fa20587200c6f71058720024ff769472005cfe7694720004fd7694720005de7394720005dd739472000dfa7094720005f97094720004ff7654720004fd765472005cfc765472001e7e65547200067d65547200076d5254720084ff76cc72005cfe76cc720004fd76cc720086de63cc720006dd63cc720024ff768c72005cfe768c720004fd768c720004ff764c720004fd764c72005cfc764c720006de634c720006dd634c720005ef724c72005dec724c720024ff760c72005cfe760c720004fd760c72000dfa700c720005f9700c7200c4f
  | 8 => 0x157da10cc53000cfe768c5300067f658c53014e7c658c530125dd738c530006f7618c530026f4618c53000dfa708c530005f9708c53000cfc764c5300067f654c5301367c654c530005ef724c530005ec724c530006f7614c530026f4614c530005fb704c53000df8704c530127d8304c53000ddc764c530026dc764c53000cdc764c530005df754c530005dd754c5300075f654c530136de654c530136dc654c5300075c654c5301365c654c5303a5df744c5303a5dd744c53039edf644c53039edd644c53039f5f544c53039f5d544c530007cf724c530005dc724c530007cc724c530005cc724c530006df624c530007d7714c530007d7614c530026de614c530026dc614c530007d4614c530007db704c53000dde704c53000ddc704c530127d8704c530126df604c530127da104c530154fe760c5300067f650c5301167c650c530155de730c530007d5310c53000dfa700c530004fe76c8530004fd76c853005cfc76c85300067f65c85300fe7c65c8530005df73c8530005dc73c8530004fe7688530004fd7688530024fc76885300067f65885300ee7c6588530005de7388530005dd7388530006ef6288530006ec6288530007cc328853000dfa7088530005f97088530004ff7648530004fe7648530004fc76485300067f65485300d67c6548530005df7348530005dc7348530004fe7608530004fd7608530024fc760853007d7e75085300057d75085300067f65085300b67c6508530075be7408530005bd7408530005de7308530005dd7308530006ef620853005eec6208530007cc320853000dfa7008530005f9700853000dfa76cc13000efa76cc1300077b65cc1300077865cc1303977b54cc1303977954cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc130087da53cc130007d953cc130087da43cc130397d943cc130007da32cc130087d832cc130005f971cc130087db31cc130007d931cc1301e4fd75d972005cff74d9720014fe74d9720004fd74d972005cfc74d972006e7f54d97200067d54d9720084fe73d9720004fd73d972005cfe72d972005eee72d9720024fe71d9720004fd71d972005ef970d972001cff765972005e7c655972005e7f7559720004ff7459720014fe7459720004fd7459720014fc745972006e7f54597200067d5459720004ff7359720084fc735972006e7c535972001cff725972000cfe725972001cfd725972000cfc725972005e7e525972005e7c5259720004ff7159720024fc715972006e7f51597201e67f50597201e67d505972001cfe75d8f2005e7e75d8f2001c7e75d8f20004fd75d8f2005e7d75d8f200047d75d8f2005cfc75d8f2005cff74d8f20014fe74d8f2005ebe74d8f20014be74d8f20004fd74d8f2005ebd74d8f20004bd74d8f2005cfc74d8f200067f54d
  | 9 => 0xd4218930024fe7118930004fd711893005eef2018930186ed2018930004fe7694930004fd769493005cfc76949300067f659493001e7c6594930004ff7654930004fe7654930004fc76549300067f655493001e7c6554930005df7354930005dc7354930184fe76cc9300067f65cc9301de7c65cc930087d830cc93000cfe768c9300067f658c9301ce7c658c930006ef628c93005eec628c93000dfa708c930005f9708c93000dde768c9301c6de768c93000cde768c930005df758c930005dd758c9300075f658c9301cede658c9301cedc658c9300075c658c9301ce5c658c9303d5df748c9303d5dd748c9303cedf648c9303cedd648c9303cf5f548c9303cf5d548c930185de728c930006df628c930007cf628c930007cc628c930005dd718c93031edc618c93000dde708c9301c7da708c93000dda708c930007d9708c93000ddc708c9301c6df608c9301c7da108c93000cfc764c9300067f654c9301be7c654c930006ef624c930006ec624c930005fb704c93000df8704c9301afd8304c9301d4fe760c9300067f650c9301967c650c9301d5de760c930006de760c930005df750c930005dd750c9300075f650c930196de650c930196dc650c9300075c650c9301965c650c9303c5df740c9303c5dd740c9303bedf640c9303bedd640c9303bf5f540c9303bf5d540c9301c5de720c930007ce720c930006df620c9303bfce420c9303bfcd420c930005dd710c930316dc610c93000dde700c93000ddc700c930086df600c930187da100c930024fe76d85300067f65d85300067c65d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d8530006de43d8530006dd43d853005cfe72d8530004fd72d8530156f710d853007d7e75985300057d75985300067f65985300067c6598530006f761985300057f755853007d7c75585300067f65585300067c6558530005bf7458530075bc7458530005ef7258530005ec72585300067f65185300067c6518530026f66118530006f56118530004fe7694530004fd7694530024fc76945300067f659453001e7c6594530005de7394530005dd739453000dfa7094530005f97094530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530104fe76cc5300067f65cc53015e7c65cc53000df870cc530087d830cc530105de76cc530006de76cc530005df75cc530005dd75cc5300075f65cc53015ede65cc53015edc65cc5300075c65cc53015e5c65cc5303b5df74cc5303b5dd74cc5303aedf64cc5303aedd64cc5303af5f54cc5303af5d54cc530005de72cc530006df62cc530026de61cc530026dc61cc530087db70cc53000dde70cc53000ddc70cc530087d870cc530086df60cc530
  | 10 => 0x95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95302167f70d95302167e70d95302167d70d95302167c70d95302167f40d95302167e40d95302167d40d95302167c40d95302167f30d95302167e30d95302167c30d95302167f20d95302167e20d95302167d20d95302167c20d95302167f10d95302167e10d95302167d10d95302167c10d953007e7c655953040ddf7359530214ff75595300067f7559530004ff7459530014fe7459530004fd7459530014fc745953007e7f54595300067d545953040cff7359530006df7359530004ff725953005cfc7259530004ff7159530024fc7159530204ff7059530006fb70595302157e761953007e7e76195302147e761953007d7f741953007f3e74195300057d741953007f3d74195300053d74195300067f64195300067e64195300067d64195300067c64195304075d73195304067f63195300075e43195300075d43195304067f60195304075e30195304075c30195304077830195304077a1019530404fe7694d302167f6594d3001e7c6594d3007f5f5394d30405de7694d303fede7694d30205dd7594d302175f6594d3001ede6594d3001edc6594d3007f5c6594d3001e5c6594d303f5df7494d303f5dd7494d3007f5f5494d303ef5d5494d30005de7294d30005dd7194d3000dde7094d3000ddc7094d30086df6094d302175e5094d302175c5094d30217da1094d3001cff7654d3000cfe7654d30204fd7654d3000cfc7654d300067f6554d3001e7c6554d30005fb7054d3000df87054d3000ddc7654d3001edc7654d3000cdc7654d30215df7554d300075f7554d300075f6554d3001ede6554d3001edc6554d3007f5c6554d303e5df7454d303e5dd7454d3007f5f5454d303df5d5454d30005dc7254d30005df7154d30007db7054d3000dde7054d3000ddc7054d30207d87054d30206df6054d30207da1054d300067f65d89300067c65d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d89301d6dd73d8930006ee42d8930006ed42d8930024fe71d8930004fd71d89301d6ef20d89301d6fa10d893007d7e75989300057d75989300067f65989300067c6598930075be7498930005bd7498930006ef62989300057f755893007d7c75589300067f65589300067c65589300067f65189300067c6518930006ed621893001cfe7518930004fd751893005cfc751893005cff7418930014fe7418930004fd741893005cfc74189300067f54189300067d5418930006de4318930006dd431893005eee4218930006e
  | 11 => 0x87d9700cb3000ddc700cb30086f76198730026f46198730024ff7658730086f46158730004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d545873000cfc7358730006de4358730006dd4358730004ff725873005cfc7258730086f73158730086f43158730126fa3058730126f71058730024ff7694730084fe7694730004fd7694730085de7394730005dd739473000dfa7094730005f97094730004ff7654730004fd7654730084fc765473000ddd76cc730026dd76cc73000cdd76cc730085df75cc730005dd75cc73015ede65cc730086dc65cc730085df74cc73042ddd74cc730086df64cc730426dd64cc7304275f54cc7304275d54cc730005de72cc730006dd62cc730026de61cc730087d661cc730087d561cc730026dc61cc73000dde70cc730087da70cc730087d970cc73000ddc70cc730124fd768c730026f4618c73013cff764c730005ef724c730005ec724c730087d4314c730127da304c73013ddf764c730006df764c730005df754c730005dd754c730136de654c730136dc654c73041ddf744c73041ddd744c730416df644c730416dd644c7304175f544c7304175d544c730007cf724c730005dc724c730007cc724c730005cc724c730006dd624c730087d7714c730087d7614c730026de614c730026dc614c730087d4614c73000dde704c73000ddc704c73005cff76c8730084fe76c8730004fd76c8730005df73c8730085dc73c8730024ff7688730084fe7688730004fd7688730085de7388730005dd7388730007cc3288730004ff7648730004fd7648730084fc7648730005df7348730085dc7348730024ff7608730084fe7608730004fd76087300957e75087300057d750873008dbe7408730005bd7408730085de7308730005dd7308730007cc320873000dfa7008730005f9700873001cfe76d953007e7e65d9530004ff74d9530014fe74d9530004fd74d9530014fc74d953007e7f54d95300067e54d95300067d54d953007e7c54d9530084fe73d953000cfd73d9530084fc73d953007e7f53d953005cfe72d9530004fd72d953007e7f52d953007e7c52d9530024fe71d9530004fd71d953007e7f51d953007e7c51d9530084ff70d9530214fd70d95302167f50d95302167d50d95304057e76d953001c7e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95302175f73d95300075e43d95300075d43d95302175e30d95302175c30d95302177830d95302177a10d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d95302167f73d953007e7e73d95302167d73d95300067f43d95300067e43d95300067d43d95300067c43d95300067f72d
  | 12 => 0xf7348550005dc7348550004fe7608550004fd7608550024fc760855001d7e75085500057d750855009dbe7408550005bd7408550005de7308550005dd730855000dfa7008550005f97008550204fd75d9730084ff74d9730014fe74d9730004fd74d9730084fc74d97300967f54d97300067d54d9730084fe73d9730086de73d973005cfe72d9730004fd72d9730024fe71d9730004fd71d9730086f970d97302167e50d97302167c50d973001cff76597300867c65597300867f7559730004ff7459730014fe7459730004fd7459730014fc74597300967f54597300067d545973001cff735973000cfe735973001cfd735973000cfc73597300867e53597300867c5359730004ff725973005cfc7259730004ff7159730024fc71597302067f50597302067d505973000ddd7694f30086dd7694f3000cdd7694f3001ede6594f300875e6594f3001e5e6594f300875d6594f30086dc6594f30085df7494f30475dd7494f300975f5494f3046f5d5494f30005de7294f30005dd7194f3000dde7094f30087da7094f30087d97094f3000ddc7094f302175e5094f302175c5094f3040cff7654f30207da3054f3040ddf7654f30466df7654f300875f7554f3001ede6554f3001edc6554f3045ddf7454f3045ddd7454f300975f5454f304575d5454f30005dc7254f30005df7154f3000dde7054f3000ddc7054f30086ef6298b3001cfe7598b30004fd7598b3005cfc7598b3005cff7498b30014fe7498b30004fd7498b3005cfc7498b300067f5498b300067d5498b3000cfe7398b30006de4398b30006dd4398b30086ef3298b3005eec3298b30024fe7198b30004fd7198b3005eef2098b301c6ed2098b30086ec6258b30004ff7558b3001cfe7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b300067f5458b300067d5458b3000cfc7358b301aedc7358b30086ef3258b30086ec3258b30004ff7158b30024fc7158b301aeef2058b3005cff7694b30084fe7694b30004fd7694b30004ff7654b30004fd7654b30084fc7654b30005df7354b30085dc7354b301acfd768cb301addd768cb30006dd768cb30005df758cb30005dd758cb301cede658cb301cedc658cb3044ddf748cb3044ddd748cb30446df648cb30446dd648cb304475f548cb304475d548cb30006dd628cb30005dd718cb3031ede618cb3000dde708cb3000ddc708cb301c4ff764cb3000ddd760cb30086dd760cb3000cdd760cb30085df750cb30005dd750cb30196de650cb30086dc650cb30085df740cb3043ddd740cb30086df640cb30436dd640cb304375f540cb304375d540cb30087ce720cb30087ce620cb30006dd620cb30087cd620cb30437ce420cb30437cd420cb30005dd710cb30316de610cb3000dde700cb30087da700cb30
  | 13 => 0x8021026fb5158021026fa5158021026f95158021026f85158021026fb4158021026fa4158021026f94158021026f84158021026fb3158021026fa3158021026f93158021026f83158021026fb2158021026fa2158021026f92158021026f8215802100cfd75d8d50004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d503fe7f54d8d500067d54d8d503fede53d8d503fedd53d8d50006df43d8d50006dc43d8d5005cfe72d8d50004fd72d8d50024fe71d8d50004fd71d8d5001cfd70d8d5040edf30d8d50006df6398d5007df97098d50095fb7058d50006dd6318d5000cfd7518d50084ff7418d50014fe7418d50004fd7418d50084fc7418d504667f5418d500067d5418d50086de5318d50466dd5318d50006df4318d50086dc4318d5005cfe7218d50004fd7218d50024fe7118d50004fd7118d50084ff7018d5001cfd7018d504067e5018d504067c5018d50086df3018d50406dd3018d5000cfd75d8950004ff74d8950014fe74d8950004fd74d8950014fc74d89503567f54d89500067d54d8950084fe73d8950004fd73d8950356ee52d8950356ed52d8950024fe71d8950004fd71d895001cfd70d8950366ef20d8950006ef6298950055f97098950005df7358950005dc735895006dfb7058950006ed621895000cfd751895005cff7418950014fe7418950004fd741895005cfc741895037e7f54189500067d5418950084fe7318950004fd731895005eee521895037eed5218950024fe7118950004fd711895005cff701895001cfd701895005eef201895035eed2018950004fe76cc950004fd76cc950084fc76cc950004fe768c950004fd768c95005cfc768c950006df638c950006dc638c950004ff764c950004fe764c950004fc764c950004fe760c950004fd760c95005cfc760c95001d7e750c9500057d750c950006df630c950086dc630c95000dfa700c950005f9700c950024fe76d855000cfd75d8550004ff74d8550014fe74d8550004fd74d8550014fc74d855047e7f54d85500067d54d8550084fe73d8550004fd73d855005cfe72d8550004fd72d855047ef651d855047ef551d855001cfd70d855047efb50d85502cef850d85502cef710d8550005de7398550005dd7398550006f76198550035f97098550045fb7058550026f66118550006f56118550004fe76cc550004fd76cc550084fc76cc550006df63cc550086dc63cc550004fe768c550004fd768c550024fc768c550004ff764c550004fe764c550004fc764c550006df634c550006dc634c550005ef724c550005ec724c550004fe760c550004fd760c550024fc760c55000dfa700c550005f9700c550004fe76c8550004fd76c855005cfc76c8550004fe7688550004fd7688550024fc7688550004ff7648550004fe7648550004fc7648550005d
  | 14 => 0x6bd6454821005df7354821005dc7354821006de6354821006dd63548211e6fa6054821004fd76cc8211de7e65cc8210067d65cc8211a6be64cc821006bd64cc821086de63cc821006dd63cc8211d6fa60cc821325ed76cc821006ed76cc8213276e65cc8213276d65cc821326ef64cc821327ae64cc82149eed64cc821327ad64cc821006ad64cc82149f6f54cc82149f6d54cc82105dee73cc821326ef63cc821327ce63cc821006ed63cc821327cd63cc821006cd63cc821325ef71cc821325ed71cc821326ee61cc821327e661cc821327cf31cc821327cd31cc821327ea60cc821327e960cc821004ff764c8211be7e654c8210067d654c8211b6be644c821006bd644c821006de634c821006dd634c82105fcc324c8211aefa604c82105ded760c82105eed760c821004ed760c82105f6e650c82105f6d650c82105eef640c82105fae640c82148eed640c82105fad640c821006ad640c82148f6f540c82148f6d540c821325ee730c82105fce730c82105eef630c82105fce630c821006ed630c82105fcd630c821497cf530c821497cc530c82148fce430c82148fcd430c82105def710c82105fe6710c821315ed710c82105fe5710c821316ee610c82105fe6610c821317ce310c821317cc310c82105fea600c82105fe9600c821025f77648421006f77648421004f77648421027766548421027756548421027b66448421027b56448421487775448421487755448421007d77348421007d47348421027d66348421027d56348421025f77248421027e7724842105ef66248421027e6624842105fe65248421007e55248421005f77048421027f26048421027f16048421004ff755802101cfe755802101cfc7558021004ff7458021014fe7458021004fd7458021014fc74580210067f54580210067d5458021004ff7358021084fc735802100cfd7158021026fb7058021006fb50580210a6fa50580210a6f85058021006fb40580210a6fa4058021006f940580210a6f840580210a6fa30580210a6f8305802105efb205802105ef82058021026fb1058021026f81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb54580210067b5458021006fa5458021006f95458021006795458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f843580210a6fb725802105efa7258021006fb525802105efa5258021006f9525802105ef85258021006fb425802105efa4258021006f9425802105ef84258021006fb325802105efa3258021006f9325802105ef83258021026fb7158021026fa7158021026f8715
  | 15 => 0xd7498c21086dc7498c21006df5498c210065f5498c21006de5498c21006dd5498c210065d5498c21006dc5498c2105ede7298c2105edc7298c21006df5298c2105ede5298c2105edc5298c21006df4298c2105ede4298c21006dd4298c2105edc4298c21026df7198c21026de7198c21026dd7198c21026dc7198c21026df5198c21026de5198c21026dd5198c21026dc5198c21026df4198c21026de4198c21026dd4198c21026dc4198c21026df2198c21026de2198c21026dd2198c21026dc2198c21086df7098c21006de7098c21006dd7098c21086dc7098c21006df5098c21006de5098c21006dc5098c21006df4098c21006de4098c21006dd4098c21006dc4098c2105edf2098c21006de2098c2105edc2098c21026df1098c21026de1098c21026dd1098c21026dc1098c21004ff7558c2101cfe7558c2101cfc7558c21004ff7458c21014fe7458c21004fd7458c21014fc7458c210067f5458c210067d5458c21024ff7358c21026df7358c21006df5358c21006dc5358c21006df4358c21006de4358c21006dd4358c21006dc4358c2105cfe7258c2105cfc7258c21006ec7258c2105ede3258c2105edc3258c21024fe7158c21024fc7158c21026de3158c21026dc3158c21004ff7058c2100cfe7058c2100cfc7058c21006de3058c21006dc3058c21026f71058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c210065f5458c21006de5458c21006dd5458c210065d5458c21006dc5458c2105ede7258c2105edc7258c21006cc7258c21006df5258c2105ede5258c2105edc5258c21006df4258c2105ede4258c21006dd4258c2105edc4258c21026df7158c21026de7158c21026dd7158c21026dc7158c21026df5158c21026de5158c21026dd5158c21026dc5158c21026df4158c21026de4158c21026dd4158c21026dc4158c21026df2158c21026de2158c21026dd2158c21026dc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dc5058c21006df4058c21006de4058c21006dd4058c21006dc4058c2105edf2058c21006de2058c2105edc2058c21026df1058c21026d71058c21026de1058c21026dd1058c21026dc1058c21084ff7694c21024fe7694c21004fd7694c21024fc7694c2101e7e6594c210067d6594c2121ebe6494c21006bd6494c21086de6394c21006dd6394c210b75f5394c21216fa6094c21004ff7654c21024fe7654c21004fd7654c21024fc7654c2101e7e6554c210067d6554c2120ebe6454c21006bd6454c21006de6354c21006dd6354c21005ef7254c2105dec7254c21206fa6054c210fcff765482101e7e65548210067d65548211eebe6454821
  | 16 => 0x94210067d54594210b67c5459421004ff7359421084fc73594210b67f53594210b67c535942105cfe725942105cfc725942105e7e525942105e7c5259421024fe7159421024fc71594210267e51594210267c5159421004ff705942100cfe705942100cfc70594210b67f50594210067e50594210b67c5059421026f710594210067f74594210047f74594210067e74594210067d74594210047d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067d43594210067c43594210b67f725942105e7e725942105e7c72594210067f425942105e7e42594210067d425942105e7c425942105e7e325942105e7c32594210267f71594210267e71594210267d71594210267c71594210267f41594210267e41594210267d41594210267c41594210267f31594210267e31594210267d31594210267c31594210267f21594210267e21594210267d21594210267c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067d40594210067c40594210067e30594210067c305942105e7f20594210067e205942105e7c20594210267f10594210267710594210267e10594210267d10594210267c1059421006bf7559021006be75590210063e7559021006bd75590210063d7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006bc53590210aebf725902105ebe72590210aebd725902105ebc7259021006bf525902105ebe525902105ebc525902105ebe325902105ebc3259021026bf7159021026be7159021026bd7159021026bc7159021026bf5159021026be5159021026bd5159021026bc5159021026bf3159021026be3159021026bd3159021026bc3159021026bf2159021026af2159021026be2159021026bd2159021026ad2159021026bc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bc5059021006be3059021006bc305902105ebf2059021006be205902105ebc2059021026bf1059021026b71059021026be1059021026bd1059021026bc105902101cfe7598c21004fd7598c21084fc7598c21084ff7498c21014fe7498c21004fd7498c21084fc7498c210067f5498c210067d5498c21024fe7398c21026de7398c21006df5398c21086dc5398c21006df4398c21086de4398c21006dd4398c21086dc4398c2105cfe7298c2105cfc7298c2105ede3298c2105edc3298c21024fe7198c21024fc7198c21026de3198c21026dc3198c2100cfe7098c21004fd7098c2100cfc7098c21006de3098c21086dc3098c21086df7598c21006de7598c21006dd7598c21086dc7598c21086df7498c21006de7498c21006d
  | 17 => 0x86df7518d21006de7518d21006dd7518d21086dc7518d21086df7418d21006de7418d21006dd7418d21086dc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d21086df7218d21006dd7218d21006df5218d21006dc5218d21006df4218d21006de4218d21006ce4218d21006dd4218d21006cd4218d21006dc4218d21086df7118d21316de7118d21006dd7118d21086dc7118d21006df5118d21316de5118d21316dc5118d21006df4118d21316de4118d21006dd4118d21316dc4118d21316de2118d21316ce2118d21006dd2118d21316dc2118d21316cc2118d21086df7018d21006de7018d21006dd7018d21086dc7018d21006df5018d21006de5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d21006de2018d21006dc2018d21316df1018d21006de1018d21316dc1018d21084ff7694d21004fe7694d21004fd7694d21084fc7694d21006df6394d21086dc6394d210d75f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21006df6354d21006dc6354d210ecfe7694921006df6394921006dc6394921024fc76549210067f655492101e7c6554921005df7354921005dc7354921006df6354921006dc6354921005f77154921025f47154921024fe76cc921006df63cc921086dc63cc921025f671cc921005f571cc921004fe768c921006df638c921006dc638c921024fc764c921006df634c921006dc634c921005f7714c921025f4714c921004fe760c921006df630c921086dc630c92101cff76545210d4fd765452101cfc76545210067f655452101e7c6554521006df6354521006dc6354521005ef7254521005ec7254521027e42154521004fe76cc521006df63cc521086dc63cc521005ee72cc521005ed72cc521084ff764c521004fd764c521004fc764c521006df634c521006dc634c521005ef724c521005ec724c521006df63c8521006dc63c8521025ee72c8521026ef62c85214a77754c85214a77554c8521007d763c8521007d463c8521025f672c8521026f762c8521027e762c852105fe642c85214a7e542c852100cfe76d8121006df63d8121006dc63d81210c6fa60d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d8121084fe73d8121004fd73d8121024fd72d8121006ee42d8121006ed42d812100cfc71d8121006f721d81210c6fa20d81210c6fa10d81210057f75581210d57c7558121005bf74581210cdbc7458121005df7358121005dc7358121006df6358121006dc63581210c6f86058121024ff75594210267f7559421004ff7459421014fe7459421004fd7459421014fc74594210b67f54594210067e545
  | 18 => 0xc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d21006df53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d21007ce42d8d21007cd42d8d2131fce21d8d2131fcc21d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d2131edf72d8d21006dd72d8d21006df52d8d21006dc52d8d21006df42d8d21006de42d8d21006dd42d8d21006dc42d8d21006df71d8d2131ede71d8d21006dd71d8d2131edc71d8d21006df51d8d2131ede51d8d2131edc51d8d21006df41d8d2131ede41d8d21006dd41d8d2131edc41d8d2131ede21d8d2131edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21006de20d8d21006dc20d8d2131edf10d8d21006de10d8d2131edc10d8d21006df6398d2101cfe7598d21004fd7598d21084fc7598d21084ff7498d21014fe7498d21004fd7498d21084fc7498d210067f5498d210067d5498d21084fe7398d21004de7398d21004fd7298d21086ed7298d21006ee4298d21006ed4298d21004fd7198d21086f57198d21326ee2198d2100cfe7098d21004fd7098d2100cfc7098d21004ff7558d2101cfe7558d2101cfc7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d21006df7358d21004ff7258d21006ef7258d21004ef7258d21004ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21004fe7618d21006dd6318d2101cfe7518d21004fd7518d21084fc7518d21084ff7418d21014fe7418d21004fd7418d21084fc7418d210067f5418d210067d5418d21086de7318d21006df5318d21086dc5318d21006df4318d21086de4318d21006dd4318d21086dc4318d21006ee4218d21006ed4218d21316ee2118d21316ec2118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21086dc3018d21005de7618d21006de7618d21004de7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d21007ce4218d21007cd4218d21317ce2118d21317cc2118d21006de6018d21006dc6018d21
  | 19 => 0x8e21086de4398e21006dd4398e21024fe7198e21026de3198e21026dc3198e2100cfe7098e21004fd7098e2100cfc7098e21004ff7558e2101cfe7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21026df7358e21006df5358e21006dc5358e21006de4358e21006dd4358e21006ef7258e21024fc7158e21026de3158e21026dc3158e21004ff7058e2100cfe7058e2100cfc7058e21084ff7694e21024fe7694e21004fd7694e21024fc7694e210ef5f5394e21004ff7654e21024fe7654e21004fd7654e21024fc7654e21005ef7254e21005ec7254e210d4fd7694a2101cff7654a21024fc7654a2101e7e6554a210067d6554a21005df7354a21005dc7354a21005f77154a21025f47154a21086de63cca21006dd63cca21025f671cca21005f571cca21325ed76cca21006ed76cca21326ef64cca214c6ed64cca214c76f54cca214c76d54cca21326ef63cca21327ce63cca21006ed63cca21327cd63cca21327e671cca21325ed71cca21007e571cca21327cf31cca21327cd31cca2131edf638ca2131edc638ca21006de634ca21006dd634ca21005f7714ca21025f4714ca21316df630ca21086dc630ca21007cd320ca21315ed760ca21006ed760ca21316ef640ca214b6ed640ca214b76f540ca214b76d540ca21007ce730ca21316ef630ca21317cf630ca21006ed630ca21317cc630ca214bfcf530ca214bfcc530ca214b7ce430ca214b7cd430ca21315ef710ca21315ed710ca21317ce310ca21317cc310ca21025f576c862105ef576c86214af7754c86214af7554c8621027e672c862105fe652c8621007e552c8621004ff755822101cfe755822101cfc7558221004ff7458221014fe7458221004fd7458221014fc74582210067f54582210067d5458221004ff7358221084fc7358221006f72158221026f42158221026fb7058221006fb50582210def850582210defa4058221006f940582210defa30582210defa2058221026fb1058221026f8105822101cfe76d95210d67e65d9521004ff74d9521014fe74d9521004fd74d9521014fc74d95210d67f54d95210067d54d9521084fe73d9521004fd73d9521024fd72d95210d67f52d95210d4fd71d95210d67f51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210d67c50d95210d67c6559521005df7359521005dc73595210d4ff75595210067f7559521004ff7459521014fe7459521004fd7459521014fc74595210d67f54595210067d5459521004ff7359521006df7359521004df7359521084fc7359521006dc7359521004dc73595210ecff7259521006ef72595210fcff7159521006f77159521004ff705952100cfe705952100cfc705952101cfe75d8d21004fd75d8d2101cf
  | 20 => 0x6dc7359721004dc7359721024fc725972105e7e525972105e7c52597210fe7f5159721004ff705972100cfe705972100cfc705972101cfe75d8f21004fd75d8f2105cfc75d8f2105cff74d8f21014fe74d8f21004fd74d8f2105cfc74d8f210067f54d8f210067d54d8f21006df53d8f21006dc53d8f21006de43d8f21006dd43d8f2105eee72d8f2105ef571d8f2131ede31d8f2131edc31d8f2100cfe70d8f21004fd70d8f2100cfc70d8f21004fd7698f2105edf6398f2101cfe7598f21004fd7598f21084fc7598f21084ff7498f21014fe7498f21004fd7498f21084fc7498f210067f5498f210067d5498f21024fe7298f21006ee4298f21006ed4298f2105ede3298f2105edc3298f21326ee2198f21326ec2198f2100cfe7098f21004fd7098f2100cfc7098f2105edc6358f21004ff7558f2101cfe7558f2101cfc7558f21004ff7458f21014fe7458f21004fd7458f21014fc7458f210067f5458f210067d5458f2105edf7358f21024fc7258f2105ede3258f2105edc3258f21004ff7058f2100cfe7058f2100cfc7058f2101cfe7518f21004fd7518f2105cfc7518f2105cff7418f21014fe7418f21004fd7418f2105cfc7418f210067f5418f210067d5418f21084fe7318f2105ede7318f21006df5318f21086dc5318f21086de4318f21006dd4318f2105eee7218f2105eee4218f21006ed4218f2105ef57118f21316de3118f21086dc3118f2100cfe7018f21004fd7018f2100cfc7018f21084ff7694f2105cfe7694f21004fd7694f2105cfc7694f210ff5f5394f21004ff7654f2105cfe7654f21004fd7654f2105cfc7654f210b4ff7654b2105e7f6554b2105e7c6554b21005df7354b21005dc7354b2105edf63ccb2105edc63ccb2105edf634cb2105edc634cb2101cff765472105cfc765472101e7e65547210067d6554721005ef725472105dec7254721027e62154721086de63cc721006dd63cc72105dee72cc721005ed72cc721006de634c721006dd634c721005ef724c72105dec724c72100cff765832105ef86058321004ff755832101cfe755832101cfc7558321004ff7458321014fe7458321004fd7458321014fc74583210067f54583210067d5458321004ff7358321084fc7358321024fc7258321006ee4258321006ed425832105efb205832105ef820583210f6fa10583210267f7559621004ff7459621014fe7459621004fd7459621014fc74596210ee7f54596210067d5459621004ff7359621084fc73596210ee7f5259621024fc71596210267e51596210267c5159621004ff705962100cfe705962100cfc705962101cfe7598e21004fd7598e21084fc7598e21084ff7498e21014fe7498e21004fd7498e21084fc7498e210067f5498e210067d5498e21026de7398e21006df5398e21086dc539
  | 21 => 0xd628c83131ddd718c83131ede618c83131fd6618c83131fda608c83131fd9608c831004ff764c8314dede634c831087cc324c8311aefa604c831196de650c831086dc650c831086df640c8314d6dd640c8314d75f540c8314d75d540c83131dde720c831087ce720c831087ce620c831006dd620c831087cd620c8314d7ce420c8314d7cd420c831087d6710c831315dd710c831087d5710c831316de610c831087d6610c831087da600c831087d9600c831025f7764c431006f7764c431004f7764c4314cf77544c4314cf75544c431025f7734c431027d7734c431086f6634c431027d6634c431087d6534c431007d5534c431007e7724c431007e4724c431027f2604c431027f1604c431004ff755803101cfe755803101cfc7558031004ff7458031014fe7458031004fd7458031014fc74580310067f54580310067d5458031004ff725803105cfc7258031006de3258031006dc3258031026df3158031026f63158031026dd3158031006f53158031026fb7058031006fb5058031106fa5058031106f85058031006fb4058031106fa4058031006f94058031106f84058031086fb3058031086f83058031106fa2058031106f82058031026fb1058031026f81058031006fb7558031006fa7558031006f97558031006f87558031006fb7458031006fa7458031006f97458031006f87458031006fb54580310067b5458031006fa5458031006f95458031006795458031006f85458031106fb7358031086fa7358031006fb5358031086fa5358031006f95358031086f85358031006fb4358031086fa4358031006f94358031086f84358031006fb7258031006fa7258031006f97258031006f87258031006fb5258031006fa5258031006f95258031006f85258031006fb4258031006fa4258031006f94258031006f84258031086fb3258031006fa3258031006da3258031006f93258031086f83258031006d83258031026fb7158031026fa7158031026f87158031026fb5158031026fa5158031026f95158031026f85158031026fb4158031026fa4158031026f94158031026f84158031026fb3158031026db3158031026fa3158031026f23158031026f93158031026d93158031006f13158031026f83158031026fb2158031026fa2158031026f92158031026f821580310fcfd75d972105cff74d9721014fe74d9721004fd74d972105cfc74d97210fe7f54d97210067d54d9721084fe73d9721004fd73d972105eee72d972105e7f52d972105ef571d972100cfe70d9721004fd70d972100cfc70d972101cff765972105e7c6559721005df7359721005dc735972105e7f7559721004ff7459721014fe7459721004fd7459721014fc74597210fe7f54597210067d5459721004ff7359721006df7359721004df7359721084fc7359721
  | 22 => 0xc931025f4714c931024dc764c931135de754c931135dc754c93150ddf744c93150ddd744c9315075f544c9315075d544c931007cf724c931007cf624c93105edc624c931007cc624c931006cc624c931007d7714c931025de714c931025dc714c931007d4714c931005df704c931004fe760c9314fdde730c931006ef620c93101cff7654531134fd765453101cfc76545310067f655453101e7c6554531005df7354531005dc7354531006ef6254531006ec6254531027d43154531025de73cc531026df63cc531006ef62cc531006ec62cc5314ef7754cc5314ef7554cc531025f673cc531026f763cc531027d763cc5314f7d753cc531087d453cc531087d643cc5314efd543cc531007e762cc531007e462cc531087d732cc531007d532cc531005f570cc53100cfe76d8131006ef62d8131006ec62d8131126fa60d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d8131024fd73d8131006de43d8131006dd43d813105cfe72d8131004fd72d8131126fa30d8131126fa10d81310057f75581311357c7558131005bf745813112dbc7458131005ef7258131005ec7258131006ef6258131006ec6258131126f86058131024ff75594310267f7559431004ff7459431014fe7459431004fd7459431014fc74594311167f54594310067d5459431084fe7359431084fc73594310867e53594310867c5359431004ff725943105cfc72594311167f5259431024fe7159431024fc71594310267e51594310267c5159431004ff705943100cfe705943100cfc705943115cff7654c31206fa6054c3101cfe7598831004fd759883105cfc759883105cff7498831014fe7498831004fd749883105cfc74988310067f54988310067d5498831026ee729883105eee4298831006ed4298831086ef329883105eec3298831026ee2198831026ec219883100cfe7098831004fd709883100cfc7098831004ff755883101cfe755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc74588310067f54588310067d5458831026ef7258831006ee4258831006ed4258831086ef3258831086ec3258831026df3158831026dd3158831026ee2158831026ec2158831004ff705883100cfe705883100cfc705883105cff7694831024fe7694831004fd769483105eee6294831006ed62948311f6fa6094831004ff7654831004fd7654831024fc765483101e7e65548310067d6554831005df7354831085dc7354831006ee6254831006ed62548311e6fa6054831004fd768c8311c6fa608c83131ddd768c831006dd768c831004dd768c8311cede658c83131edc658c83131edf648c8314e6dd648c8314e75f548c8314e75d548c831085de728c831006d
  | 23 => 0x326ec41d8931326ee31d8931326ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d8931006ee30d8931006ec30d8931326ef10d8931006ee10d8931326ec10d8931006ef6298931006ed621893101cfe7518931004fd751893105cfc751893105cff7418931014fe7418931004fd741893105cfc74189310067f54189310067d5418931006df5318931006dc5318931006de4318931006dd4318931006ef521893105eec5218931006ef421893105eee4218931006ed421893105eec4218931316de3118931316dc311893100cfe7018931004fd701893100cfc7018931006ee201893105eec2018931005ee7618931006ee7618931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931006ee6418931006ed6418931006ec64189310076f54189310076d5418931007cd7318931007cf5318931007cc5318931007ce4318931007cd4318931317ce3118931317cc3118931006ee6018931006ec601893105eef7518931006ee7518931006ed751893105eec751893105eef7418931006ee7418931006ed741893105eec7418931006ef54189310066f5418931006ee5418931006ed54189310066d5418931006ec541893105eef7318931006ef5318931006cf5318931006ee5318931006ed5318931006ec5318931006cc5318931006ef4318931006ee4318931006ce4318931006ed4318931006cd4318931006ec431893105eef7118931316ee7118931006ed7118931006ef5118931316ee5118931316ec5118931006ef4118931316ee4118931006ed4118931316ec4118931316ee3118931316ce3118931006ed3118931316ec3118931316cc311893105eef7018931006ee7018931006ed701893105eec7018931006ef5018931006ee5018931006ec5018931006ef4018931006ee4018931006ed4018931006ec4018931006ee3018931006ec3018931316ef1018931006ee1018931316ec1018931004fe7694931004fd769493105cfc7694931005de7394931005dd7394931006ef629493105eec6294931004ff7654931004fe7654931004fc7654931005df7354931005dc7354931006ef6254931006ec6254931004fe76cc931006ec62cc931005de76cc931006de76cc931004de76cc931135de75cc931135dc75cc9314fddf74cc9314fddd74cc9315175f54cc9315175d54cc931007cf62cc93105edc62cc931007cc62cc931006cc62cc931517ce42cc931517cd42cc931025de71cc931025dc71cc931086df61cc931005dd70cc931024fe768c93150ddd738c931006ef628c93105eec628c931025f6718c931005f5718c931024fc764c931006ef624c931006ec624c931005f7714
  | 24 => 0xe720ca31317cf620ca31006dd620ca31317cc620ca31527ce420ca31527cd420ca31315dd710ca31025f576cc631086f576cc63151f7754cc63151f7554cc631027d673cc631087d653cc631007d553cc631005f570cc631004ff755823101cfe755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231004ff725823105cfc7258231006de3258231006dc3258231026df3158231026dd3158231026fb7058231006fb505823113ef8505823113efa4058231006f9405823113efa305823113efa2058231026fb1058231026f8105823101cfe76d95311367e65d9531025dd73d95311375f53d9531004ff74d9531014fe74d9531004fd74d9531014fc74d95311367f54d95310067d54d9531024fd73d9531136dd73d9531024dd73d95311367f53d9531136df53d95311365f53d9531136dc53d953105cfe72d9531004fd72d9531134fd71d95311367f51d953100cfe70d9531004fd70d953100cfc70d95310067e50d95311367c50d95311367c6559531005ef7259531005ec7259531134ff75595310067f7559531004ff7459531014fe7459531004fd7459531014fc74595311367f54595310067d545953114cff7359531006df7359531136df5359531136dc5359531004ff7259531006ef7259531004ef725953105cfc7259531006ec7259531004ec725953115cff7159531006f77159531004ff705953100cfe705953100cfc705953114cfe7694d31135de7394d311375f5394d31024fc7654d310067f6554d3101e7c6554d31135df7354d31005f77154d31025f47154d3101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d8931006ef52d8931006ec52d8931006ef42d8931006ee42d8931006ed42d8931006ec42d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310076f54d89310076d54d8931327cf73d8931007cf53d8931007cc53d8931007ce43d8931007cd43d8931327ce31d8931327cc31d8931006ee60d8931006ec60d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d89310066f54d8931006ee54d8931006ed54d89310066d54d8931006ec54d8931326ef73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d8931326ee71d8931006ed71d8931006ef51d8931326ee51d8931326ec51d8931006ef41d8931326ee41d8931006ed41d8931
  | 25 => 0x8b3105cff7694b31084fe7694b31004fd7694b31085de7394b31005dd7394b31004ff7654b31004fd7654b31084fc7654b31005df7354b31085dc7354b31024dd76ccb3115dde75ccb31085dc75ccb31085df74ccb31545dd74ccb3153f5f54ccb3153f5d54ccb3105ede62ccb31087ce62ccb31087cd62ccb3153fce42ccb3153fcd42ccb31025de71ccb31087d671ccb31087d571ccb31025dc71ccb31005dd70ccb31005df764cb31006df764cb3115dde754cb3115ddc754cb31535df744cb31535dd744cb314df5f544cb314df5d544cb31087cf724cb3105ede624cb31025de714cb31025dc714cb31005df704cb3101cff7654731084fc765473101e7e65547310067d6554731005df7354731085dc7354731027d6315473100cff7658331086f86058331004ff755833101cfe755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331024fc7358331006de4358331006dd4358331004ff725833105cfc7258331086fb3058331086f83058331156fa10583310267f7559631004ff7459631014fe7459631004fd7459631014fc745963114e7f54596310067d545963114e7f5359631004ff725963105cfc725963114e7f5259631024fc71596310267e51596310267c5159631004ff705963100cfe705963100cfc70596310067e505963114e7c5059631026f71059631134fd7694e3114f5f5394e3101cff7654e31024fc7654e3101e7e6554e310067d6554e31005f77154e31025f47154e3101cfe7598a31004fd7598a3105cfc7598a3105cff7498a31014fe7498a31004fd7498a3105cfc7498a310067f5498a310067d5498a31026ee7298a3105eee4298a31006ed4298a31026ee2198a31026ec2198a3100cfe7098a31004fd7098a3100cfc7098a31026f71098a31004ff7558a3101cfe7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a310067f5458a310067d5458a31026ef7258a31006ee4258a31006ed4258a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a3100cfe7058a3100cfc7058a3105cff7694a31024fe7694a31004fd7694a31004ff7654a31004fd7654a31024fc7654a3101e7e6554a310067d6554a31005df7354a31005dc7354a3105eee628ca31006ed628ca31025f6718ca31005f5718ca311cede658ca3131edc658ca3131edf648ca3152edd648ca3152f5f548ca3152f5d548ca3131fce628ca31006dd628ca3131fcd628ca3131fd6718ca3131ddd718ca31007d5718ca31006ee624ca31006ed624ca31005f7714ca31025f4714ca31007cd320ca31315dd760ca31006dd760ca31196de650ca31316dc650ca31316df640ca31526dd640ca315275f540ca315275d540ca31007c
  | 26 => 0x4fd70d895100cfc70d8951006ef62989510d5f57198951005df7358951005dc73589510fdf7715895116dbe7418951005bd7418951006ed6218951024fd751895105cff7418951014fe741895105ebe7418951014be7418951004fd741895105ebd7418951004bd741895105cfc74189510b67f54189510067d5418951084fe7318951004fd731895105e7f521895105eee52189510b6ed521895100cfe7018951004fd701895100cfc70189510247c76549515557f74549515557d745495154e7f645495154e7d64549510075f73549510075c735495101d7f725495101f6f72549510076f625495105e7c62549510076c62549510077771549510257e71549510257c715495100774715495101e7f615495101f776154951004fe76cc951004fd76cc951084fc76cc951006ef62cc951006ec62cc951004fe768c951004fd768c95105cfc768c95101d7e758c9510057d758c951006df638c951006dc638c951004ff764c951004fe764c951004fc764c951004fe760c951004fd760c95105cfc760c95101d7e750c9510057d750c951006df630c951086dc630c951006ef620c95105eec620c951025f6710c951005f5710c95100cfe76d8151166fa60d8151024fd75d815100cfc75d8151004ff74d8151014fe74d8151004fd74d8151014fc74d81510467f54d81510067d54d8151084fe73d8151004fd73d815105cfe72d8151004fd72d815101cfd71d8151166fa50d8151166fa10d8151166f8605815115cfd75d9731084ff74d9731014fe74d9731004fd74d9731084fc74d973115e7f54d97310067d54d9731086de73d973115edf53d9731086dc53d973105cfe72d9731004fd72d9731086f571d973100cfe70d9731004fd70d973100cfc70d973101cff76597310867c6559731025dc73597310875c53597310867f7559731004ff7459731014fe7459731004fd7459731014fc745973115e7f54597310067d5459731024fc735973115edc7359731024dc735973115edf53597310867e53597310867c535973115edc5359731004ff725973105cfc725973115e7f5159731004ff705973100cfe705973100cfc7059731114ff7654f3115ddf7354f31086ef6298b3101cfe7598b31004fd7598b3105cfc7598b3105cff7498b31014fe7498b31004fd7498b3105cfc7498b310067f5498b310067d5498b31024fe7398b31006df5398b31006dc5398b31006de4398b31006dd4398b31086ef3298b3105eec3298b3131ede3198b3131edc3198b3100cfe7098b31004fd7098b3100cfc7098b31086ec6258b31004ff7558b3101cfe7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b310067f5458b310067d5458b31024fc7358b31086ef3258b31086ec3258b31004ff7058b3100cfe7058b3100cfc705
  | 27 => 0xf7358a51084fc7358a51026ef7258a510d6ee5258a510d6ed5258a51006ee4258a51006ed4258a51024fc7158a510267f5158a510267d5158a51026ee2158a51026ec2158a51004ff7058a5100cfe7058a5100cfc7058a51084ff76cca51024fe76cca51004fd76cca51086de63cca51006dd63cca511d6fa60cca5105cff768ca51024fe768ca51004fd768ca51006de638ca51006dd638ca511c6fa608ca51004ff764ca51004fd764ca51024fc764ca51006de634ca51006dd634ca511aefa604ca5105cff760ca51024fe760ca51004fd760ca51086de630ca51006dd630ca51025f6710ca51005f5710ca51186fa600ca51004ff7458251014fe7458251004fd7458251014fc74582510367f54582510067d5458251004ff7358251084fc7358251004ff725825105cfc7258251024fe7158251024fc7158251026fb7058251176fa5058251006fb4058251176fa4058251006f94058251176f84058251176fa3058251176f83058251176fa2058251176f82058251026fb1058251026f81058251036fa7558251036f97558251176f87558251006fb7458251006fa7458251006f97458251006f87458251036fb54582510367b5458251036fa5458251036f95458251006795458251036f85458251006fb7358251006fa7358251006f97358251006f87358251036fb5358251036fa5358251036f95358251036f85358251006fb4358251006fa4358251006f94358251006f84358251006fb7258251006fa7258251006f97258251006f87258251036fb5258251036fa5258251036f95258251036f85258251006fb4258251006fa4258251006f94258251006f84258251006fb3258251006fa3258251006f93258251006f83258251026fb7158251026fa7158251026f87158251026fb5158251026fa5158251026f95158251026f85158251026fb4158251026fa4158251026f94158251026f84158251026fb3158251026fa3158251026f93158251026f83158251026fb2158251026fa2158251026f92158251026f82158251024fd75d8d51004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d5114e7f54d8d510067d54d8d5114ede53d8d5114edd53d8d5105cfe72d8d51004fd72d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51006df6398d51135f57198d51005ef7258d51005ec7258d5115df77158d51006dd6318d51024fd7518d51084ff7418d51014fe7418d51004fd7418d51084fc7418d511167f5418d510067d5418d51086de5318d51116dd5318d5105cfe7218d51004fd7218d5100cfe7018d51004fd7018d5100cfc7018d51024fd75d8951004ff74d8951014fe74d8951004fd74d8951014fc74d89510ee7f54d89510067d54d8951084fe73d8951004fd73d89510eeee52d89510eeed52d895100cfe70d8951
  | 28 => 0x8e51006de3098e51086dc3098e51086df7598e5115ede7598e51086dc7598e51086df7498e51006de7498e51006dd7498e51086dc7498e5115edf5498e5115e5f5498e5115ede5498e5115edd5498e510065d5498e5115edc5498e51086df7298e51006de7298e51006dd7298e51086dc7298e5115edf5298e5115ede5298e5115edd5298e5115edc5298e51006df4298e51006de4298e51006dd4298e51006dc4298e51026de7198e51026dd7198e51026dc7198e51026df5198e51026de5198e51026dd5198e51026dc5198e51026df4198e51026de4198e51026dd4198e51026dc4198e51026df2198e51026de2198e51026dd2198e51026dc2198e51086df7098e51006de7098e51006dd7098e51086dc7098e5115edf5098e5115ede5098e5115edd5098e5115edc5098e51006df4098e51006de4098e51006dd4098e51006dc4098e51006de2098e51006dc2098e51026df1098e51026de1098e51026dd1098e51026dc1098e51004ff7458e51014fe7458e51004fd7458e51014fc7458e511367f5458e510067d5458e51026df7358e51136de5358e51136dd5358e51006df4358e51006de4358e51006dd4358e51006dc4358e51004ff7258e5105cfc7258e51024fc7158e51026de3158e51026dc3158e51004ff7058e5100cfe7058e5100cfc7058e51006de3058e51006dc3058e51026f71058e51136de7558e51136dd7558e51136dc7558e51006df7458e51006de7458e51006dd7458e51006dc7458e51136df5458e511365f5458e51136de5458e51136dd5458e510065d5458e51136dc5458e51006df7258e51006de7258e51006dd7258e51006dc7258e51136df5258e51136de5258e51136dd5258e51136dc5258e51006df4258e51006de4258e51006dd4258e51006dc4258e51026df7158e51026de7158e51026dc7158e51026df5158e51026de5158e51026dd5158e51026dc5158e51026df4158e51026de4158e51026dd4158e51026dc4158e51026df2158e51026de2158e51026dd2158e51026dc2158e51006df7058e51006de7058e51006dd7058e51006dc7058e51136df5058e51136de5058e51136dd5058e51136dc5058e51006df4058e51006de4058e51006dd4058e51006dc4058e51006de2058e51006dc2058e51026df1058e51026d71058e51026de1058e51026dd1058e51026dc1058e5105cff7498a51014fe7498a51004fd7498a5105cfc7498a510fe7f5498a510067d5498a51084fe7398a51004fd7398a51026ee7298a5105eee5298a510feed5298a5105eee4298a51006ed4298a51024fe7198a51024fc7198a51026ee2198a51026ec2198a5100cfe7098a51004fd7098a5100cfc7098a51026f71098a51004ff7458a51014fe7458a51004fd7458a51014fc7458a510d67f5458a510067d5458a51004f
  | 29 => 0x4fd70d943200cfc70d943201cff765943205e7c65594320875c535943205cff755943205e7f7559432004ff7459432014fe7459432004fd7459432014fc74594321967f54594320067d5459432084fe7359432084fc7359432196dc7359432194dc7359432196df53594320867e53594320867c5359432196dc535943205cfe725943205cfc725943205e7e525943205e7c5259432004ff7159432024fc71594321967f5159432004ff705943200cfe705943200cfc70594321967f50594321dcff7654c32195df7354c321ccff7654832005df7354832085dc7354832195de75cc832085dc75cc832085df74cc83258ddd74cc8325875f54cc8325875d54cc83205ddd72cc83205ede62cc83205fce42cc832587cd42cc832315de71cc832005dd70cc83205def748c83257ded748c83256f6f548c83256f6d548c832085ed738c832086ee638c83205fce638c832577cf538c832087cc538c832087ce438c83256fcd438c832315ee718c832004ff764c83205ddf764c832006df764c832004df764c832195de754c832195dc754c832565df744c832565dd744c83255f5f544c83255f5d544c83205ddf724c83205ede624c83205fce524c832007cd524c83205fce424c83255fcd424c832315dc714c832005df704c832085ef764c832006ef764c832004ef764c832565ef744c832565ed744c83255f6f544c83255f6d544c83205def734c83205fcf734c832086ee634c832087ce634c832087ce534c832007cd534c832087ce434c83255fcd434c832315ec714c83205ef76198432026f4619843205ef46158432004ff755843201cfe755843201cfc7558432004ff7458432014fe7458432004fd7458432014fc74584320067f54584320067d5458432006df5358432006dc5358432006de4358432006dd4358432006ee4258432006ed4258432006df3258432006dd3258432006f64158432006f54158432086f73158432086f4315843205ef7215843205ef42158432004ff705843200cfe705843200cfc705843200cff765803205ef86058032004ff755803201cfe755803201cfc7558032004ff7458032014fe7458032004fd7458032014fc74580320067f54580320067d5458032006de4358032006dd4358032006ee4258032006ed4258032004ff7158032024fc7158032186fa5058032186fa4058032006f94058032086fb3058032086f8305803205efb205803205ef82058032186fa1058032084ff7498e51014fe7498e51004fd7498e51084fc7498e5115e7f5498e510067d5498e51026de7398e51086de5398e5115edd5398e51006df4398e51086de4398e51006dd4398e51086dc4398e5105cfe7298e51004fd7298e51024fe7198e51024fc7198e51026de3198e51026dc3198e5100cfe7098e51004fd7098e5100cfc709
  | 30 => 0xd76cca325a6ef64cca325a6ed64cca325a76f54cca325a76d54cca32087ce53cca32007cd53cca32326ee61cca3205ef76198632026f4619863205ef46158632004ff755863201cfe755863201cfc7558632004ff7458632014fe7458632004fd7458632014fc74586320067f54586320067d5458632006df5358632006dc5358632006de4358632006dd4358632006df325863205ef7215863205ef42158632004ff705863200cfe705863200cfc705863200cff765823205ef86058232004ff755823201cfe755823201cfc7558232004ff7458232014fe7458232004fd7458232014fc74582320067f54582320067d5458232006de4358232006dd4358232004ff7158232024fc71582321c6fa305823205efb205823205ef820582321c6fa105823201cfe76d95321be7e65d9532004ff74d9532014fe74d9532004fd74d9532014fc74d95321be7f54d95320067d54d95321bcfd73d95321be7f53d95321bcfd72d95321be7f52d9532024fe71d9532004fd71d953200cfe70d9532004fd70d953200cfc70d95320067e50d95321be7c50d95321be7c65595321bcff75595320067f7559532004ff7459532014fe7459532004fd7459532014fc74595321be7f54595320067d54595321ccff7359532006df73595321ccdf73595321dcff7259532006ef7259532004ff7159532024fc7159532004ff705953200cfe705953200cfc70595321ccfe7694d321bf5f5394d3201cfc7654d320067f6554d3201e7c6554d32005ef7254d32005ec7254d321dcfe76949321bf6f529493201cff76549321bcfd765493201cfc76549320067f655493201e7c6554932005df7354932005dc735493259eef64cc93259eed64cc93259f6f54cc93259f6d54cc9321cede658c9321cedc658c932596df648c932596dd648c9325975f548c9325975d548c932007cf628c932005dd718c93201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d85320067f54d85320067d54d8532006f741d8532006f441d853200cfe70d8532004fd70d853200cfc70d8532006f7619853231edf6318532326ef6218532026f66118532006f561185321adfa7018532005f9701853200cfe76d81321aefa60d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d8132006de32d8132024fe71d8132004fd71d81321aefa30d81321aefa20d81320057f75581321bd7c75581321aef86058132194fd75d943205cff74d9432014fe74d9432004fd74d943205cfc74d94321967f54d94320067d54d9432084fe73d943205ede73d9432196df53d9432086dc53d943205cfe72d943205eee72d9432024fe71d9432004fd71d943200cfe70d9432
  | 31 => 0x8552006f5611855200cfe76d8152006df63d8152006dc63d81521e6fa60d8152004ff74d8152014fe74d8152004fd74d8152014fc74d815206e7f54d81520067d54d8152084fe73d8152004fd73d815201cfd72d8152024fe71d8152004fd71d81521e6fa50d8152006fb40d81521e6f840d81521e6fa20d81521e6fa10d8152005df7358152005dc7358152006df6358152006dc63581521e6f860581521dcfd75d9732084ff74d9732014fe74d9732004fd74d9732084fc74d97321de7f54d97320067d54d9732086de73d9732086ed72d9732024fe71d9732004fd71d973200cfe70d9732004fd70d973200cfc70d973201cff76597320867c65597320867f7559732004ff7459732014fe7459732004fd7459732014fc74597321de7f54597320067d54597320867e53597320867c53597321de7f5259732004ff7159732024fc7159732004ff705973200cfe705973200cfc7059732194ff7654f321bcfd7694b3201cff7654b32084fc7654b3201e7e6554b320067d6554b32005df7354b32085dc7354b32086f76198732026f46198732086f46158732004ff755873201cfe755873201cfc7558732004ff7458732014fe7458732004fd7458732014fc74587320067f54587320067d5458732006ee4258732006ed4258732086f73158732086f43158732004ff705873200cfe705873200cfc705873200cff7658332086f86058332004ff755833201cfe755833201cfc7558332004ff7458332014fe7458332004fd7458332014fc74583320067f54583320067d5458332006ee4258332006ed4258332004ff7158332024fc7158332086fb3058332086f830583321d6fa20583321d6fa10583321ccfd75d963205cff74d9632014fe74d9632004fd74d963205cfc74d96321ce7f54d96320067d54d963205edd73d96321cedf53d96321cedc53d963205eee72d9632024fe71d9632004fd71d963200cfe70d9632004fd70d963200cfc70d963201cff765963205e7c65596321cf5f535963205e7f7559632004ff7459632014fe7459632004fd7459632014fc74596321ce7f54596320067d54596321cedf73596321ce7f53596321cedf53596321ce5f53596321cedc535963205e7e525963205e7c5259632004ff7159632024fc71596321ce7f5159632004ff705963200cfe705963200cfc70596320067e50596321ce7c50596321bcfd7694e321cdde7394e321cf5f5394e3201cff7654e3205cfc7654e3201e7e6554e320067d6554e321cddf7354e32005ef7254e3205dec7254e32194ff7654a321cddf7354a32005dc7354a3205ddd76cca32006dd76cca321cdde75cca321cddc75cca325addf74cca325addd74cca325a75f54cca325a75d54cca3205fce52cca32007cd52cca3231dde71cca32005dd70cca32005ed76cca32086e
  | 32 => 0x1ce5f54d8d521cede54d8d521cedd54d8d520065d54d8d521cedc54d8d521cedf72d8d521cedd72d8d521cedf52d8d521cede52d8d521cedc52d8d52006df42d8d52006de42d8d52006dd42d8d52006dc42d8d52006df71d8d52006de71d8d52006dd71d8d52006dc71d8d521cedf51d8d521cede51d8d521cedd51d8d521cedc51d8d52006df41d8d52006de41d8d52006dd41d8d52006dc41d8d52006df70d8d52006de70d8d52006dd70d8d52006dc70d8d521cedf50d8d521cede50d8d521cedd50d8d521cedc50d8d52006df40d8d52006de40d8d52006dd40d8d52006dc40d8d52006de20d8d52006dc20d8d52006de10d8d52006dc10d8d52006df6398d521bded7298d521ddef7258d52006dd6318d52084ff7418d52014fe7418d52004fd7418d52084fc7418d521967f5418d520067d5418d52086de5318d52196dd5318d52006df4318d52086de4318d52006dd4318d52086dc4318d52024fe7118d52004fd7118d5200cfe7018d52004fd7018d5200cfc7018d52006de3018d52086dc3018d521cdde7618d52006de7618d52006df6418d52006de6418d52006dd6418d52006dc6418d521975f5418d520075d5418d52197cf5218d521975c5218d52197cc5218d521975f5118d52006de6018d52006dc6018d52086df7518d52196de7518d52086dc7518d52086df7418d52006de7418d52006dd7418d52086dc7418d52196df5418d521965f5418d52196de5418d52196dd5418d520065d5418d52196dc5418d52086df7218d52196dd7218d52196df5218d52196de5218d52196dd5218d52196dc5218d52006df4218d52006de4218d52006dd4218d52006dc4218d52086df7118d52006de7118d52006dd7118d52086dc7118d52196df5118d52196de5118d52196dd5118d52196dc5118d52006df4118d52006de4118d52006dd4118d52006dc4118d52086df7018d52006de7018d52006dd7018d52086dc7018d52196df5018d52196de5018d52196dd5018d52196dc5018d52006df4018d52006de4018d52006dd4018d52006dc4018d52006de2018d52006dc2018d52006de1018d52006dc1018d5205d7f74949525bd7d74949525b67f64949525b67d64949520075f63949520075c639495205d7e729495205f6e729495205e7f629495201f6f62949520057d7194952006df63d8552006dc63d8552004ff74d8552014fe74d8552004fd74d8552014fc74d85520fe7f54d85520067d54d8552084fe73d8552004fd73d85520fef651d8552006f741d8552006f441d855200cfe70d8552004fd70d855200cfc70d8552005de7398552005dd7398552006df6398552006dc6398552006f761985521e5fa7098552005f97098552005df7358552005dc7358552006df6358552006dc6358552006df6318552006dc6318552026f6611
  | 33 => 0xd70d895300cfc70d8953006ef6298953006ed621895305cff7418953014fe7418953004fd741895305cfc74189531967f54189530067d5418953196df5318953196dc531895305eee5218953196ed521895305eee4218953006ed4218953024fe7118953004fd711895300cfe7018953004fd701895300cfc7018953004ff74d8553014fe74d8553004fd74d8553014fc74d855315e7f54d85530067d54d855315edf53d855315edc53d855305cfe72d8553004fd72d855315ef651d855300cfe70d8553004fd70d855300cfc70d8553006f76198553205fa7098553005f97098553005ef7258553005ec7258553026f66118553006f5611855300cfe76d8153206fa60d8153004ff74d8153014fe74d8153004fd74d8153014fc74d81530967f54d81530067d54d815301cfd73d815305cfe72d8153004fd72d8153024fe71d8153004fd71d8153206fa50d8153006fb40d8153206f840d8153206fa30d8153206fa10d8153206f8605815305edf6398e52084ff7498e52014fe7498e52004fd7498e52084fc7498e521de7f5498e520067d5498e52086de5398e521dedd5398e5205cfe7298e5205cfc7298e5205ede3298e5205edc3298e52024fe7198e52004fd7198e5200cfe7098e52004fd7098e5200cfc7098e5205edc6358e52004ff7458e52014fe7458e52004fd7458e52014fc7458e521be7f5458e520067d5458e521bede5358e521bedd5358e5205cfc7258e5205ede3258e5205edc3258e52004ff7158e52024fc7158e52004ff7058e5200cfe7058e5200cfc7058e5205ef76198652026f4619865205ef46158652004ff7458652014fe7458652004fd7458652014fc74586520d67f54586520067d5458652004ff7358652084fc735865205cfc72586520d67f52586520d6f6515865205ef7215865205ef42158652004ff705865200cfe705865200cfc705865200cff765825205ef86058252004ff7458252014fe7458252004fd7458252014fc74582520567f54582520067d5458252004ff7358252084fc735825205cfc7258252004ff7158252024fc71582521f6fa505825205efb205825205ef820582521f6fa1058252004ff74d8d52014fe74d8d52004fd74d8d52014fc74d8d521ce7f54d8d520067d54d8d521cede53d8d521cedd53d8d52006df43d8d52006de43d8d52006dd43d8d52006dc43d8d52024fe71d8d52004fd71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006de30d8d52006dc30d8d52006df64d8d52006de64d8d52006dd64d8d52006dc64d8d521cf5f54d8d520075d54d8d521cfcf52d8d521cf5c52d8d521cfcc52d8d521cf5f51d8d52006de60d8d52006dc60d8d521cedf75d8d521cede75d8d521cedc75d8d52006df74d8d52006de74d8d52006dd74d8d52006dc74d8d521cedf54d8d52
  | 34 => 0x50004003000c000000c00d0084000002000200000010008005000001100040010000000003c004000400000100000028000002000800000010004001002c0000004000005800c002400000640010010002008c0020010001000c01100000010008003002800600380000000000000000b0080001001800d001000800040010000002005001000040070000003003c00100000000008006003c014000c005000400000180010010001002400c00000020020002000400e000400100140010000003001c00000080000004000001000300100020000005002c00700280000000003000400700040020024008000c003001400b0008003000400000040070000002001c00800000000008003000c006000c0000010000000000000080000004009000c0030004000004c00000100100008004002c00100100000008009001000c000400500000020000000001c0000008010000400000080000000007006800000300090004003000c000003400500000160008002003c00300000000004005000000600200061cf5f5398a53086ef6298a5305cff7498a53014fe7498a53004fd7498a5305cfc7498a531ce7f5498a530067d5498a53084fe7398a531cedf5398a531cedc5398a5305eee5298a531ceed5298a53086ef3298a5305eec3298a53024fe7198a53004fd7198a5300cfe7098a53004fd7098a5300cfc7098a531bf5f5358a53086ec6258a53004ff7458a53014fe7458a53004fd7458a53014fc7458a531be7f5458a530067d5458a53084fc7358a531beee5258a53086ef3258a53086ec3258a53004ff7158a53024fc7158a53004ff7058a5300cfe7058a5300cfc7058a5314f5f5398653086f76198653026f461986531375f5358653086f46158653004ff7458653014fe7458653004fd7458653014fc74586531367f54586530067d5458653084fc7358653136df5358653136dc5358653004ff725865305cfc7258653136f65158653086f73158653086f43158653004ff705865300cfe705865300cfc705865300cff765825301d7c755825307f5f5358253086f860582532177a5058253004ff7458253014fe7458253004fd7458253014fc745825307e7f54582530067d5458253084fc7358253004ff725825305cfc7258253004ff7158253024fc71582532167e5058253216fa50582532167a50582532167c5058253086fb3058253086f83058253216fa10582530857f7494d535cd7d7494d535c67f6494d535c67d6494d530857e7394d530875e7394d530867f6394d5301f5f6394d5301e5f6394d532167e6094d532167c6094d53004ff74d8953014fe74d8953004fd74d8953014fc74d89531de7f54d89530067d54d89531deee52d8953006ee42d8953006ed42d8953024fe71d8953004fd71d895300cfe70d8953004f
  | 35 => 0x40000038001000000b0000007000800000240030008003000400400000020008001000000200980000000002006c00200000030000002001c001000000a0008000000400000400050000000001c03300080000010000000000600080030008001000401c001000600480020010001002c00500000000004000000000a0024011000000000140010004000001000200200020000000000000000080050000003001400000040000000001002c000000000d000c00f00000000000001000000b000000000000000014000000c000000000200000010010000001c0020000000000c0030000001000400a00180000000001000c002000400000080000000002003000300380040004003000400a000400100100000010000000800a000c00000140000000006003000000240000024003000000500000250000000001c0180004000000c00200040010010000000c0010008000000400300100000010008000400300ac00d0000000000000300140030018000000c008000c0050000009001000100000000030000000000200b0009002c00000080020004001004c0020004003000000000000030000003002000600080000000001000c00400900010000011000c00400000040008000006000500100070000011000c0030000003001c000000c000001401500200090004000004800000140000000003001400000000020070000001c00300000000038000000400e0004002002c00600000000000001000400500000000020000000400000040010000000000000400040000000001000000000080030038001000c0000024000001400a000800b0004001000c000002800e000c00200480080000002001c0050024000001000000140030028000000c00e00000020000000000400000180080034006004400d00000010020003003c001000000400100010000000000c003001c0020014005000401c00000000004000000000000280020010000003800000180000008009000000a00040010008003002000100280020000000000800800040000024000000c00100140000004005002800000000010000005000400400200000004002005000000080010008002001801b001c00100800050000001002000400080020004000001c0000000002004000100040000000001000800a0024003003800000140030000004000400000080000004001001c00800000010008005001c0000004000000000500040110000009000000100040010008001000000100000000010001002c01000000040000007000000a000000000180000004005000000400080020008000001400800140030018002000800d000001300000050004000001c00100680050008008001000000200000008002000c00400100020018004000c0000000001000c000000c004000c000
  | 36 => 0xc00000000010006001c012000800000080010004003000c001000c00000000000000002000c00800000000004005002c001002c002004c003000400000000000000004001c001003c001001000300040020000002000400a0004006000002c001400100040080004006000800500040010000001000400000000300000004003400100080070024000000c00400040030018016000000200240000000002000800100040060018003000000000100000038016000800a00180030000004000000a0004007001000800000000008002001c0020048000000000100480080028000001c000000801d00100080000007000c008000c002005400100000010014000001400e0028000002400400040000000001000c0010010003000000c00180000004008000800000000000000000000c0080008005000000c000c00000100020000015000c00400180000000000001c000000000400180010000026000000c0004001001c0040010002000800000000000000000000c0030000000007400900000010010002000c00e000000b0024006000c0030004006000800100080090008000000c000000000500000020000000000400a0004022005c004000800000040090000000001800000080000010003001c001000000100200020010000000400d00280000024000000000100000010014004000000e00480050000003001c0030018003000c00000180000000002000000300000010000000000000b0014000000000000080000000001000400100080010024001000800100040010000001000400c00000030000000000c003004c0000004009002800100040040004005000001b00040060000001000000000000020004005000000000380010000004000400000080090048003000000100140020004003000400a000c00200000040008005000c002001000000000020008004000c00800000090010007001400e001000200000010008000000000200080010000000000000200080000000006000400d0000000001c0000004021002000a001c0050044005000400000300010000006000c0040004000003c0000008001001800200280060008003000c006000c006001c001002800000240040018000000c00000040110000000001000a0024007004c000001400c000000c003c000000c0060008004000c000004800100240030004002002c0000034000000c000000000000040030074000000000100140140040000003c00b0010000001c0010004001000c00100040000004001001800000040030000006000000000140000000000000000600000030000001000002a00000060034007001c00000000020004005003800000480000004017000000000280030000000001c0020008009000c00200340020020002000800200000050008015001
  | 37 => 0xef05260918b0a936e00000004c4800037b800300040030020004002801e0014001001c00100380040004003000000000040000028003000001500040070014001000001900240010044004000403000100020000002001c0050040000000000000040000000000000c00200000010010001000801100000130014001001c001001c000001402a00000100004004002400500000090018018000c00300180050000007000800000000050008021002000100140030008000000c002000c0060000000000800000180020000000000000a000000300000090000002000000500000030050000000000300000070000000000400f00080060004013000000b000000700080030000000001000100000000020009000000200180020010001001c000002400100200020000001000800600000000000000000c00100100040008000004c000001000500400000014006003c0010028001001400700040020024004000400000000000000003000000000340000000002001c00400300000000009000000800000060000004004000800040070000002001c0050000002000400000080080008000002c007000c000001000f000c013001800900040080068003000000100040090014007000c0000010005003400100100040030007002800500000040004001001c00400000030018001000c008000400b00140060000000000400400200020000000000c0060004004000000800080000008000001800a0000001003c0030000000003000d0008018000801f00040010010008001c0110004002001c00400140030014003007c000003800200040030004001000400300140000010000002c00100040000034002000c00200000010020000002c003000c001003c000001c003002c008003000000040070004001000c000000400400540020000000000c0060000000002400300080080008000000c00000080030008008000800900040010008001001000f00140010000002000c0000000001001000900080110000000000000000380020010003001400300000030000005000400600dc002001400e000000e000c003000000200080080060001000000100000000018005000800600040030044002000000d00040040004007000c006000c000000c0040018005000000400040000010003003000600140070000005000800100240010000004000c0080004005002c003000400a0004002000c01600200000000002000000e00140010024005000c000001000000000000004000004000a000000000000000000000000c000002c0020000001000c0030014002002000a000000a0000009002800000180020000000003800f00140030004000000c004000c000002401d000000000040000004004000000000480070030000000001a0000003000000
  | 38 => 0xcc62b143816f800028c87c610e80007fe80000000000993813e1b10000b8400007c30f9278f9e5c74787448faa5a6a83984e4d39730135a31c21182325e38fa289c27fe0001c540d900006519d5a00012742bd811c0000a28af1a0ce19e80000002240000000000000004678e6e0002b6c39c8bea72f90f88e19e6e510000000000000000deab351dc6b721a4600000002f12a7eb4d800094d94fa3d582d00000000386000089d0000a40152e763890853e166c00000005ca170636380008e2226ab8380005ac9c9c00003ac0e5066236f8fe200028244599b38478000088a06ea42d9a860fa03da0cf18787e02ade86d1e38497032262f00000000c960000000000000066d20de00000000002bf42f8243a00000000002ce45c88b0c11827b200017ce0000000816096621b8b96a86a9de8112a747eb800095a80004a798ae59400000308a2c00014c60c5aa7800008e609b80009310b025b1a3dc55b2e24b37a11cac6a3c679680007d02cfa81c1cd0a74179e62826384b5000000000006321f1200000002ad800001a249c949800083c00006fe8b2459caab693e9e325a9800077f890e00011c248d17840e086269e080004c680009fe1c68b5a997218d067299d800000029700002a2a508800082e800000003481401a88443abec55796e609d800023600007dcab58000123e7d500000000000880800000000000000000207800000000000000000835a5d424b0046483ab4484fabfc000210c348063e9001748000114a2bc80000000cc80001b8e147168424a80003d1000092a15564e8000009780004f5800005c81589611a5847d00005df98324721eacb4a13a2b5f800052f950e3040e9a0001aa6a3b0e980000000000086c83b9e7cb0a00000000000aa385ca00008623a700008fa00007549dc4b2f000001217d2000000062180007748000000000090f82d41fa95340df2ad02cc17444082d5c7398a0a9ea000087faad8a548afe0000a8814ea18a6120000864187c80083d4000097000000007191b8628e2bf08a41c2062715c000017e013a0eea4da8ce29c29bce08087525a02776000129a9f9989a4e284f0787201a7029aba2e2800235a93d848c19de0000000b1d08483b4220863d00002b493000001ff472f180200000008ab829884b29a4000000000000002d080000001282000219c0000000000000000000000000052095000046e800004e2410000000014995ca8dc9d8c4b684eea9f1dfc4fb27f003b8f46b67a8a87a4800059c035651e0e361069d2e65d000000000002408000244847821f81e2128000031b84660002c380000ad4400000016b25308e314064e08b48000019800019dc12f00000002dc6a290988b4d000099f000022d10ce0000000af386242b600000000000000278a07a8000a41965a3a42692a58146e00
  | 39 => 0xe8000000002a1a8000000000006ec00005ea835c00025040001e2e781000068400003fc9fe400029683ca000000000008d80000a149dd80202d260ac0000b280f3600011260000000234aa40000000076f25f0afc8000000000085b9d9e000000002a0860000000013d0436893875eb7b0be84b08000644859483000000000000970800000016fa00000000001ad063995b8000000000000000870ca6938a77418e006a0d000000000efa0001c6a00000004129e98a5b8000b7105ea0002116571a25292412500000bb200008caada9a0606e800007e000044c1850000136c000000000000000a50000000000000001083250800b291ac6a7e07c81d216c889584742200b7000006360002c3a00000008a328ce0002ba871da6ce58c853c00000002e5000000000005a8800036794841afa7d6000000000000000001c041798e7c00000000002bbe00010b024e800033d93b43ea00008cf817e2f0866a38d0c260001ef892c840847700008f094fe00009620000000709a77c0001b44000000026ca43c1f8ac8a3669930ace0ed21b5960c55502f67a98000000048c9c691de5d61638a9900004118000a8e24ccaad07a00ca251ab8986b84f917dc4b285c21da99ee9db92946e6a1bc4c110a85fa87e68bd1afc37e061e6d49cb2a5f93847b9196c2af0b507de8940000000024300008a8087843712540001fb82680ffc7f28cbc7ba81e46351a84000230a000287841aa3705a909ba9f78fc4941a9e61c69f006512d988b5000061ba8c4b35a46000012887d8a35c0a900005b30ffa9dc220a2be0000000000030c272c2578b2a000000014291d60000000404800000006fc00027ee89980006099292000000000000000331014714000000000005a38d4495429a660510de8709c5800000008f58e740000000a0e06024361434755191a7fe08260000000000153e091a3d27c2800012c80004f817de0091c962250660359862a53f173470c80002f516e88308000000000000023e40811ace9e780004d480000000000103000087a2740038a20e049a8d2451881c00000009b027789d79fba9c50a6a000108e13790283960e247b3068600024ee4f1a6fa7488aca9f7180c670adf4000097c03226480000d3a33680008af0000299a32c2858000000226e0001afe0000000b1f25c86861ae28ee1084000000081a240600022ee7e813f800001f481984182c780000f317f0ada08546189b8a8b82ace16a8000a6f06ca60ea392943925678386ac0000c4290688ac00000000000000abb800043c00004ee00001fa0d8097a19c4117879e4dd000022217bc0000000667000000022542090b2643fa19a7d1a11e00000ba493abe64ae18d0000000068000000002aea60a253c0000000000245a307a380000000005397fe00012607cc1ec00000f5278620
  | 40 => 0xf920a68e14ad40000000266e74c0a3c97c9a260002646b4507fc4ee8c2400027ac0aa198a627a2040001c9e19b28cc48b17acac9000029da9923059428000000092c0bd800012d600026ac00000008348000836a81eaa500387b600000000000000131800019ba99a8000000000027a90d4a1f9772000029600000003a99cae338000000000006d5800000000009629e960001ae4120132e94e176800009504d6a60c18c800000000008550d5473893a6792244813708f6a2f121600011a42741f8e8848b20855819a5ce9fc8000000000009680000000000285a60f21be416a61631905dc9398f2400718524d5a61e84d2b543f41ff6a98a54e69d93768fda13c44d9876a049ddc37110fa720a77e0702e0400029ac454a71c15f05bc16e89561ee1f4a34280008152c9e982aba2b44913e9200384159195a00023245d927a63f210724ef80008b8800022604322720000000155c000000056f8c209f211720000000616958e000239068900000000000000009e67c99520000000000103a00000008448000b0d01700002844000268e0fc02e60002c10000188a00000001ae80001a209bc2102a50b3395660001a9e130800000028b02f89c807e7acec0002b740000000000000076ca21ab60201c76d254ca309e5e0000cc0b34a90239a295883da28aa1c1e2c0228a860ce800027f1ff09ef9a3053c9e509d500fe4e6287a000000086a800000016ac00000002d5239c00029cc901000017680004908ea4850800000000000000000000050e00000000f425b030690980002dfe000100a00028308eb0b8cb130b38a3907327e0828087191d400000008d0068c8b3800000023a6a5500005d71da027b9ce02f0032c944096a350826662d291a51d8a90000286200f971899625e6000130c6640000000000062c800036f04a4a4c1812092adc28ab0a2ea19029e9a69c2a0000680000000000011d8491997a96b80008dd8000000000084800003218d0808f29b88ef89e890082a65250d9c15186ee1df86d059a8000b41a35600000004798a18602a9f29c8ab2a131221e95b1cc400000000000dde7309c4a00000000002a4a0000ee6422800000000002878f2cb6100003d5000096c8d3800000000c51b1800012146388e5e00007a450422ccaa800000002b480000000236950a57d000000017940000000753a7ae00000000000000000000000001a8000014000000000001454000000030c8a8c00000000000bf696080007f62c9a193299c406a74e86b97d48c0a8f43c4036e18b9f08331040430899be3708944000000023b25b89b7ad2c00004be000000071100004b10000499800085a2b9cb261aa82a5000018c2350a2100000cc000000000000001306a3bab1000000008d280007ec8c486a0800039680000000000891800084ea2a400023ae8
  | 41 => 0x3848d3028817809cc18041aa80000001ed000001c20e7117000011185350ef40000000002aa0a6db29c400000004fa000000014dc4572c4a000000000000000000000000153c80e21ba0000f08a4f800000000000000000a7180009c903b67b10cde5ed0f8a00000001c500001a580000000098620a3228f7819600004d400000003d8954c060800000016f20f60eaa92282fe8a100000842b9285300000001d16000000000028588ce94ea00020867dd9712000121a000201441f15f60000d900000d0e0000bdc838919a39d9c0229b8ec22a700008f2800058b0c2823c800000028f696d80004b8aae440700001018000558a81c0d88000800028a000000045e9d824740ef60e80dec1c596c2aaba31a64d82fa12093103b60d8a0b797781dd23f400002227f8800063080002560530999000043b280c77a0ae6b5326d447b9700a49269058926bc5500c00a4d03683e32d9a3ee19a000005b63909d184b6041225d2cf02ef0fba0378a4859728820001d7e00022de7261e705d50fe0428800023385c0a6c108203e27b859d27e0a781cd614b000000013384cfae0c831a22a7412382023832e0002188000000042ba93a8e2a9e800000000001bbe0001d6e277a34c1790a0272d12b2000000000013408382da2000000020ca1d633a000000000003ab8000000000064a8bb681200160000000b3013902e7aaf2aac01f008d1b8c91c09ec06c8f3e110859600000000000e8e55f8e0a00017828ca8bae117104226c10f60000aaa5b4044caef1ec692a82a060409ca1ee83923749b4239e29644cc151e77080000000000518000069b80000000000a1b00000001aa411fad00330800047486f26748cb405dab5a31d9564b04abd8567a438000173cb542c6c9e70000000000000010400002c46368821830f11be23500000000000000000000000000000d1243d00008ef00001da054892d9fe86b980000001c226c018e457e0000000280e000152666d84fc4fe800001714667db1392b1a19540000000000000058d8400000243200000000000000400a01e13ca1a800c00001e6800000000003770000000000000000001610cd600000002d1000000000006fa80000001ebc04a000000000000000e64011000000000005eb800062d9e3c0001e46000119c288a2984a02ca2a498aea07400104159b2e94802d20670000000165e46a00007ab8000024803c00000000000000496229c46d2ce205ba50c00000000cd80003d316ce893149c0002bf845fa51284c87aa391886632f8d341bd02388fe80002bb8d6e6808d72a1da8aa000000000015a271c018451c0b82550800000005a291b1abc0002a9e0000000000288673280003a01bac2ae9b7e0002da017f0000245231e0000000891297c1f423b6000237c84382f800024d49bc800000000605409
  | 42 => 0xfe4000000000000008ac83dc2e91d9c0002816a9e80007bf146455a804c00000000002508000132a63480007c8000000012760000000000000007f87000f9049a53080008c112480000000b32193400000002ea1a1a695800000000008b420a26a880000002cb4590a44e0002dba72400007c0ace01970118a230000000108683f294c0002d529259a4c3c48004556a97201994e87159fde262960e0002928abe973223a0f585bc000088591280818fd61d5919886d800083b000000025880001e86a65990e7501e00000000000011cc728212e000000058226e8484958a000207215829824ec96a09ae03fa6ad80e800004286e8a72e89b14da89715ce35d95aa6a280006111ab809a800000015a8658216074980004d89d440000766a669c5ea19adce38baaa892500001ca1e6c0001b7a06a8000000000000022729848b1a00003344d780002052d42a0f06c24ad9b66a5da5fa141914e581173e1491dcca5080d20fc8d104b014367a314a8a47a6a40000a640000cca00000000000d020b29c1208f80004ba93b0000139cb1829fa11a9628000027e777825ca340000a9a219200000ea000283600000001e22ddaa858e6c00000003e515cc0001a2a36a0018000000000004140ac800041317a2000000067986540001956584adea00022362e218ba840247c00014f60001ee6a0e80001f79bfe0001d2c0000e9e000000000016ae43a01364c2025a1160a407069d7a397222c1831be000000007c700000001c242ab978662200904d1ae1e57b87363898ec89fa21c854d80d400000860001f16000000066c8e94b3d97c40002106000038c9579db86fe00001151b0e0001cce0ea80004b18000936a19600025240000ebe17d878e6b28000125a4d891982780000b8072d9f3803ca34274f8c3a93d01ca00005e0483174a3fa0d0c20a1c9a00009f893403fe7418000368077064e16c4af7a3ec11920fa0000baa65d893845901ae98980000000000972a354940937e0002932a6220422a90df00000c8267d188468f283e4c9a57e0002b7218b0000000000000028f85388000000000081e15522c588b6094857671b928668a0000a02842c3741ee241800005c92e160002dac3cc296200012ce00000003988000000246480a95723c691fe6b62bd25bb949eb22259c6528000111178a3c700000001eaa0230c2e0ba171c6b6abfa4a71c8a16c9e64000210a3e122dca5e27ca5f9800008225d6ab4ac360000000a848214506970a9aca2c8b58aa923c0130a00a2c0e8e3978c2938d7044019140000b18000005612a00787f801d800000ae0001ce40001f5e7db80007449210ad48c9cb79800019a26ec5aea43486b169a85f25284f2000000000000002c70000000000012a43760000000070e00000000001906a7d800003c207a1cf80000589b1a
  | 43 => 0xc5b500000000000280000055c000000000000000caa00018e88619742000000000000000c080005f280003c50000b7d99c810915dc318048e2a9881200019c03b5839e2c70dbaa279cc0491000000491bcaba000000000000909138000174e14d0000a751ac0000184c0002be8823072a02c03e029105fa58c00007641f3c82711c60600000000182a34680004b40b0a79f800071e264a582863cb780000000290e95200007ada86e663106e06d25be00023f83f709dc000147c000285e7f10000ab0913cb6b83f87a3810e0000e323de000010980007bc800000000006618000b4aa4ac902229a97f28b669c8f807980b9aa748d3235d188086982845298e5237e9ae88168c9e059a0308b183388578cd8581852a3118786055a4d20002950b6911e27840f3a0000f6c7720a6802aa9ae4aa9ec2b4e03a2b52832659586b02108000b8200009c3a42e0002a5c95e000000000000001b96000000000011089158c74000187032b000000000005f30000000000037f00000000cb000000000002a5e369000000014206750000a6c8ab00001160758271000007ac1d70000b501a7e40580000000df623d0000ab200003ed1366b2f9f2c200800061d23d822b80000ab00000002056000000000006ce8a998065379b460ea00003039f4e25f800000022e800000002dfab8816b80009599c2e000000000000000001b80000115a000257670600000000000a24a9847482da8b5c000000023ba5d68000b0b0000000000000018ee805aa5a9d8000060387849bf80c404ba06a01d87a8a452b6e87d0e1a48e04e24618ede0a3ac169fd000000000003c30000b4c99d89db117400000000000b5663f144c14fa6781560000ae61a9a00006e696e800020f08b00002092079964e166268a55e993a9509bdc0001c74000298e0001b2009c10066f08386b5a1486294258c71f87ec591918e663800061829fc6c48000000160021290aa6408bde4dc0ce6000000004890c893293428c389aa8291f7e40c969eb2e993272a28105af000000000ec4cb24c898021ea0000b584640da60002b0687e8ba257a930225484fe5d5a6e4a5189c2649907675097c000000000dd98f0acea3a29da95ac427874c47ead5e0b129165fa0eb06b50f389de8c989d90000b0697d6304a7944ae983814884869381f34ab2a04a026aad473191b86f1a32e4d42d94000036669906783e915805bf000000000003631f60000097200008c6aa20ee43fd80321139a6ca329f420c7011026b8536b6f275828aa5a021d8db2647877a00000000001c840000e3e4508dd68e68e0eb212dca00007403d7800073e80004ff8000528000002ca63000000006c5256e26e27cc79a00000e380fa5c22a4400000007d5a59095f09347050000a7d00b8b6da104370193e8df80006af9ef434b80008d9
  | 44 => 0x90000a1380009d2a65c5fd20f27e7128c535a7ba00021840000000000246e2bb00005ec03f608e80006e4183400028140000000b1624de38b00005f600001340c4aaaf888c0000456000214e000187241d03ce00007d8000100c3e39e660000e88ac818542758f861a08a788b92248b771fa8623140c5b9000023e9fb457ea62a08900001528b0033f86fa10a95064b703b817fab5cb088000324800000024768cc142a40f242a0002c54000000031382626f62026b3a269462523f0b61883e11ba8b400000001d80000000000000002900e62d6c5670794b34152800000000000d189aea6669ad8000852000000019bc7f0a278828168c000096e00000004e6a136b121b8220b29c04ab0f7c00000000001d504ea0868796000000000000000000000169848a2756426800088ba59805aa102000256856529569659edc00019a45871ab4650031a020ae0a0990000133249a32a1e6a7f50c360000cdc661156840400000001b680c491ea82c0d220001d8a3d9a8e60001d3a685a8320000c4039e82ee6d921763571bfc45516f611c1c8c8650ef2089a920a298a3000010c0000284a3e5892451a0eb854c849200d12625c500000bc2bda3c8000017b800000000000000000139000000000000001402724800050e865e1a1091000024e40000000000000098380000000000a3fa8c64148a240292a6c552000042800009fcabf645a209049f000092ba114000239697d27088ea00003922922a8186c645f2b1c00014d8045ab323de8f2e0000000000287c5ba8a721b6000025d80000002850507800000000000000000a7883de0000000abf0000000000000000000000000000208e00000000002d7256800009211b1e49281542c4a554000010475980002089cf20000000752000032280000002b5e07f111a000198274a0000430800060580007e62cca2689bdaa3e86228492822af000000000000b5580000000b606e929d800000003540000000203251400000002a2c00023c823b81787c926020001b700000000aa88000000000040d80003d080009d201c6545800031e0fb600016940001a0c000000033a9924455a8d850f963c43c99e80ec8000acb961a20b9b98ac2a69851680000002ba45861fd0711a5646ec8000abb077c7698b529549e301d1a5d069a20b241f91acb1b854c00026e63c080000ef00000000000191aa5481b000023e0000000191c0000000000000000000006928000000141262c00000000000b4fa75a4f482f4ad822146fcaafe7a6a86846d8ace87302e4b060f76a810d963f3266c56d87fa04c000035f8000a9ba31466500004579a481bf81de3452a264da28c00632daa0178230100851643f09c6691015e7588000000163a09c80004bf8b28138215c0000f4a16080000000000206000046c2c940000000000268
  | 45 => 0x2c0b3a5009231b4c55b864a00024fe7148000732035874200008bc8f8215ba1eca998ffe74680000000000000000000000004f50000000294082299ac9e580002308000000000004480005561bee86c144614c92322c1883080121522ba2c96729144451e8bec8ed269600000002fc9d5c1f68a4680a282ab8620121849592668991639280009cf000026908cc2e4ab6658413ea6c18de8000000041c195c905a3a04d800000000c4c5fd87beb3b95e800000003ef0db60000000000000000000000000000a6f800000000007ad2ab2609285415d0132069ab027bb2b001468ff40000000a6000000000000000000000000007830000000295e23c0000000270272e999600000004ac16f42dd000052f09c00002222ab31cee00022d83418000027000044400000000000000018e000000000007f26d600001681a2c85c80000000000156800000000009b080000ca800000000003559c3e56ba95c0001af06c8a98a00000009ce800077da2fa5f18e203a48c3487c8bd682593fc1bb1d748f693ceabd24421778f06af8275c095a68457b001e0980cee6d882c2a2580fc114926e6f3131454889321b916dcb7a20bc3ab00b655282443ef8054505a2625239686128a5703f38420b7e27924409f3a0ff2dd25f92744300912aae18000124230655f00001a78000b1aa848196800000000002ff12a6000259a00000000000000000000000028d492214b0a2b05043f7916a0000ca045b1f6a6cc00006fa2492000000078690927d700000568772000005861580001a600008040008317a4c085d1db099421a431b10beb0213582b68b100c39dbe5029d3c7a019caa130d362968000000000000000e400020d85cb80001d8800052011f2000078c6ed0d405e90000a3f2a346649b241fc11c4a7b218e00006d227880002401a38577800087709b67b8083464884f808580a077d29b69f496606eb9d64a0680002358000003129818e8f187c60b5e56c2bfeadd8000937092679d09981ff998000007387f017209082cf89f90000000112400021820e22b342392bd400001c41ac8b34b1980009f6000000000000000324000236a7689ed26a024ec90526f47958cfa92612e600015d620e962e10f92f205700000001cda00000007fb08200bb25dc040167800009e0b87098e84880000001a8c0002d54000000005800000000000000000000004ea0002cd800000002258000046a3a4358212600019e237c814a77999ec99591daa4d8cf8216aa3a4e02a961c08dae0000000802000043990c69fa80000b88000b42865200002dc111a9e40002ccc00000000002dd092d0e38000000033400000002260779000008b00000000e86b808000856061c427000001b232078a24a4159946c8c325da3e2000055d28be72c16222948b4ab0c16766fda3e6a9617381a
  | 46 => 0x57000071690d6000114424800ac4ad1ca60000750000001472e1dc09f19a5a000216c90d80007650000000000046b9d1c0000000b01a2c412c0000723a3cc0000000000000000028e0000088a73a959a0d400000000000000256020581e00f08692000055c00000002bf278e000000000010ac000000000011780002d44a4f0904000259e599974c0001b500000000b56949277381f60299d78a862e14a938f5a0002622000000082b181a00023620000000b18a1d000001cc00000000c617f813380f60069644345aa6a3018000b7c0f740000000a909eba000257297e279a35e800000000007da00000002944a11a8c87c896201de000029d0372b2d8c90a85131c8d22238147987a0001950000034e0000aa07a798220419e7847c21ce4a580001f8144a000110a3a294ee000133c000206e00000009458a4c5930d4678d0a6c2509dd683e24a6287265a07e9e2a22827d03cf1d5e1ad82be0002dcc2d923268a397b291283e200000004810996260800084c000000000000838f50000119662aa9480002d66000000065b80001e98000000000000000003588000000235eac100007ae0986766139e000000012600001078cb600000000000000b08068a774000081f0000632800009f0000000170e5d0000000011aa36b000021f133aa28845a0001e0898a00000001e240000cec0000a560bf1d009d998640002700000000000000000000c84532800000028988c01b9e000000062a06d400017b600022ec9b81e127a405d25b88b5a2ab1b083a586084411a5c8d9800074295a60000000163223e2ae0b3c71b1b0249a95c2b790000347148a480065001e8de2a7aa4262cf8ccc73d06942f905420000000000000062f800089e93e25899448876000000000001e42c00b009024000016c6cf820a4ba15f0a95a9a85fb258e6e707e482d1184a3a91fc0dc2d6463680001c286f07ff056cb23041013692a070587b250b800034a03425f08cfc854000055da9b49e19ec873482884fc8e3a0641e202209f64364ab4016183ba6f98a14185aabc0319ac81cb09e485f92cc00000002cc91a2a68000066b9a526f014247cd894a186ac724c893f6000185c00000004d513acac60000224089a0002d200db08a67182aaa5a7269e1961eb0000000031a00008a180000001ad206c000023207761d29adc00010ea00000007768000b0f09548dd000023f9af60000000b2b926400000000000a7a000185e43817748bfaa1e30600006d8000062400000000000acf8a8a5ac17260001b40b7e8f322ed00000b3168a00000009c78000241851200009300000000333a7e290b0000352a6206768bfa935aa4600014cc6dba6eeb2a82aa96a00008ac0e103158000b3f9fac000000080d0300811800063e000000023280000cb86d380009d3000076e85e80001c
  | 47 => 0xbb6000125ea7f8000000271200019d00000000000152a13b213800000006f29e6222a0000000086a27c99d678da7fa2db0000b519f5aac20bc64d10e540000ade98d922400003043c10000000000069000007a08306ae10000000000021e8000010025067813a400000005859afaae5813c000000000015460fd0000000252a00013da95180000002d8a000000000000003da208800007bc000000000000000001658000000000000000000cb2a67a8e8000252e000000030a84682a496fe9ab8d04088111600000009070000000245e5d401485b78c52274a5d869980000000e84b19112200028880000734a2c984a000000034f000000000000001ebe0001b2865f80261789c30480800097ba352b0720647a815085380bf400000000001c2800026f00a180000002c42a4403b46e504620dea6d2000000047011ce743934a1828d6c0001c340000000b4700000001c7268e9236000000019f133600001420f2891c0000000a0b020c89f042265e2b7000000000000000b6200009e888ba5e20000955a60402220741c623b025688bc00000001ba2b9a00023e042301ec3291dca164a23000019686f7a9ba1ababb67b286b4851211a0002c5c8f01ea8000143ca358cae00000000001a8e88ea5de5c0800036aadde3af2178afa94ae489995829090e40000cf05d19af263780009f0297400000000000000000186626b000014400006fc0922a8c25e400000004651a90000000000006442b900000000000000000000000000000000000000000000000001c4e84a80003fe2198201000060711143eb078a91182ba64601d64dcad0c55813dc5fba3ee58080007430000000278c6b58b40000244c305255a193a4f023f000096b0000417800000022da0000000000000090280000000000a5285cc09d22be000278410380009869f66b8495780001b746410ea000000009b5a4c6114000094793ee31f860e349ac7a1639696524192045429a20fb9320872a5bc2a8a718aa1ad826b300000002686b2193c254e00008e780008d19a9c0002872ade000050380000001456981a2b682a835e5aa96d80001106b4400000000b62b492a8015a9e0aa158e3c8960514b561d4a6cea6ca8e1183e1fda74604e800073da27e7f4800098b80003199eda3bf938c662046c0000a7c971000068d22940002dd60000e5009eab94b47891a5af9a4e0000000000280400023680001f7830e00000001f4cac480002610ad05878fea0000000000000010d1094635a3ce88400007d12450000022e21727b00000000000000099018faa538d4c3be12401600a548180000000000001380006cd96620000000000193c3f2800088700002fe267a3e400000000000669800000000000000a080000000000000000029d60b585c6000000013280000002cf26f90b9806784ae2
  | 48 => 0x6cf0a3a59fa7629b620ae54319c61f5a14649e8c6232008a267c00006ab0000000000000007b4000049e0001cd800025a40001aec00000002db80005268000b138000000000000022f001695e46738b8648aa4b82a0800068b82e000008aa0002a82a8a0000438800000005ce00020a8021151a00000006e49b6a2630e40acf102649c00003931b2c00000006f8a840697a85c2530bb800000007ef0000889a90c00000000001a145b58dce52cab4e357aa981f304723e78fa000000007648b4663a8000000167c0001e7277b00000001e520000000003800063802f20000b2ea83000017c16d2af31f4856ca17000d8a9e00029944189b720002d6e611aad616d00008ae95d852310c41750ae039c0a809a82662aeb19a81500b688a880001800000adfa8e275a8eec608127ea23954e71e8fd82f48a704aa138800004c662606f60ae15245caaa021b200001cc05529f10c8e76b800095280000002c0a0000000544a7fc7021e420ad9df87b5821e8de8c5052e0b2c000000078580b465c2b42000275252e80006d20000000179c00000004b90292ac580003c3982c86c9aeaaa907100250f6e24a0f9c000012c30297da3b00000215ad9c2f39ba6b0ba25a99524829cda80800001c853400000fa9f101f00000000000000000000000000000000000000000001668a631d960000cf400028b815a1fb600000005640000574946a00000000000000aee83ec00000003c88000000000000000000000000af110660682a76000000052d1148a41131600000000000beeb240000000195e00022820002b8e000007200010642e9924caeb9a080001efa1af28266f515ba858a4ce7e59c06148091e76a28949651f8a0dd0d84897a47815380004562b1e000191051c9c0e0000000281000000000000002e060e68d520000bda3b50a0603382ea1e08000a598000ae014ec0000000000000000000000591e9c0000000698073a9748a340001d884e1a00ab539c48aa410d2398265e0868ac41d61e063aa27da000066e00023160000000000039600000000000f980000000ac9800000000000000000271263200000000001278000000000000003b81a740000000176192880917b8000000031aa2ca6ee8a5806906a60001d4c2a58e4e000000000000007a5000024d918c2130a5cad1adc00d126a2000000019d18585711c864221d328b0000000010bc000044879297529fb08e07a1010c7cf91e876aa2340001d361eda46a00015bc6c580003f08192000041c6ef1ea47f59a785db88be0a721d2216037ea4e101e9e802283fc128400027c2000000034f8000000080a000144e00000009d0800030300007fb95fc2290de06dd994c000000000000000000bd0b3724bc0001fc6a181ab0000000000023b23bb8e166e1199e0f113b699112bca949426af89
  | 49 => 0x800600000000002a4c444a4ea000000000012f8000000041424540001fccb24800024f8000494890a16710da0001640000000069f11f83c997f26248b840000c9a373176c99f8f9a0000d8848711ec0001d76000000097d97a86a5a04057404946c4201824ba7348c48754000235a00016b47bc000068480004060bcc9ca8000000000000000003b880002ef8000b581f84000226473c11804ef04ac8a7a15a38313d009600caabe07809c31f9a14305785ee848a00015fe3c2826c9218000000014c1128fb06ea035a03602c05541f94000183600017906838000a0808b298900003cd0000000000047daca60001f2e3592a701d380000000000a8886401620000b01128a000006e00000000000000102a3980001120b630000000012462389fea2800000001f046108f40b8002ae6b120e40002a8498205506d72ba600016f8b3a8e4400026fc0000fe60001dd40000000000208035600004a4000000007c200000001a6a1d40002cda58d1e3a4de93ca0002be499c08367d6007e59b99cc0000000a66196a084921e98f0eb200006cc237263ab09019446280000f200006888bc8510894616798a26e22d0e5b6aa32a7b8000a4280000000000000000000015828e5006460b8000000034a4cca7bc0000a625e821de0000b3a44724680001ade0001a42315105c927800041e000052081208fc800094d000000015e2637017c2ffa1e424f00000000000b4100000001aaa00028de66a85a88cd00009b6979218a1f14000038a00000000e41ed45171c3673a11340000ac643422764bb21da3e9a6b05179b0400023d400000006bba36c00000004200000038004200018f6000052800000007c19132acd913a00012a20000d8285900007189d5811f000000000000002a3c0001bc877c0ac80e9273e8890e2a84a2a204b800007e18a2629299e483100001c89df2803a95a00000000000fd20f0000000028028031ece50c80000001cdc6ab800027d800096a80003c5800099c9ca29a221c4928000085a8000000000079320fe01f0000b179e263dc9e889f390ca630123a000100eab01d0200000000002452000186a6df09f000000000000000b39800088c87a242d00000a09b0a0002bd005e94040c80000000000000000000000ae20288000000000074a876400000000000000b308074000000000000000000edcb0300000002a003010000000177c2af8000735000000000000000be60000000000000000024720000000375281852b0eda00000009aa93c492f80008bd8000000159823780000002674188240e3f69eb2a73a4a200001bc3401dfa0001a92000000000008862d380000000102000079c000030c00024f89e000003fb86049be04c880b29da4e39b264f990040de0bca328aa9c82500001cb80005452e20000200620301509871488
  | 50 => 0x9e22218000000000026c48a214300001c9483d08443a886daa0a0acc2a115001c100005f22d3059200000002b629932140142059a5fe800037193945aa2cb29c801d41b807ee54e91a044320d0464a9081908188aa6a2c22dc8476aed0c585991364ae7ac5a00024307c9a424000067e171000068fa50a042a7b44eb800000019b8000000003720e86ea80000000a983ea80000000ba019c000061a248e00000007c78000195a728b20800000008702cd8fc0000000000007d40000000000000075580000002db2a4b8916a5e909000000003792d8e0000000361933442c96ec9c58000b5e8000000207eaae2c80a7c00004ca03a68d107f8a8dab140451fce0000000b64253a00000004b21a0a9851a9400005a6968992c8bf2b30b3f10441c7209a12d00000000000a641d800000000b64800000022b40000000a7085568f885a40001c1ea82088ea9200008ff8e0800018000d3000000000001578268000162a1b7a5c68db9af87dd06e226d21182039b4a62905f20000000b2e1a327df000000017d0140a834ab18c7a00006062de0cc690a2c505c30c88279a11054c07267e41cf80000000afb87923d38b040cca58025920366421ede00029aa54612fc7ec0b9c0002a2e08a80000000000a72291c00000000ad0eb4633141c0000000000000015f987e5b290380001e221759efeb2a164a42e024c0001dac7efa4580000adc4bb800048208844e5a6d000000001861ac21a399fe3df800000007ce0c20000000097a000000000027060001e54395800000013240002d1697380003f1800052da2920001b5470f0000472800098fad3cb488000adf2d1a00000005c414e4b311d86594800094f8000080181e000251489084d8a2e80004c78000af295a4000072437f8af037203e697a85180000000000000000000009cc8b5c769000083725e073f18f2b698cd482f82409d41964000047a0000000000000020e20989b20ac0376a62c666997c820902288020d40939c1c9dc92d2aea9c425ef8b9063fa82e204112e10c2aa68b4838033c9034061a57a0c40bac0001ae040210961c19a0435a07427cc80005a08648b2b1aa0506097875c80000002d3aab10096883070c2b080002981840000014653489ccb7600000d50f606361f7069e87dcb2c1d1400000d00001b5a77b95e65dea96c0002a7237980009571a629e600005a411400001b2a4de242238c21f87d42c148688000000000079d9e1496d00008f401e80142e1a2b5a2062c210ee72a9e1e8cf00009a018081c22db0349202eaec871e7bb80000002b902642bb00000062688000071700002d32b820000d9800000003dc21666f58948b7b80006f4196693f1c109510e0000017e21f481d2a729348ac380000000000af200000002b8a000000000000006c7076eab680000001400482
  | 51 => 0x500000000000381800000013f08c6000000019fc00020840001b0c8ea9c40155028c9eda8f2b0c927253020ea40c2c1e0000c7c5b0114c5e6a5401e59d843a08f648ff222051480000002c440000000000000000000009b70b7a94c8aa80000db0a2686a800015da75b0864541033e7e200f43d700000000a8e39aa6ea0001f0e3ae80000000000abc0b0e30208c400026100000000000056251d000000016141f280000000000000000053d0360000255845b8000878002c5da8000a9828ae0000000ac300000000000000000000020b600021c027e92fa990800000020c80001e7a50b0d1e8929b3475c000010e042e16295449f50000842099c000292cacb04fa22480006ee2b64000102a77882bcb23a5e2aca1af412e0a129b18174b1f800020a80000000000000048400019f67a2a2a8000099200000004c3ac562068000b7892be38084aa7a88000a7717708528f1e30728f0631202200e93aa000104e51f849c87c15b45950f2a27600007eaa6f6b6e00da000076c93d9f2a32309da0000b76267a574000094e00000000000a3e09200008d6000094600000000fec0002b56000252c87b8000b0991b29030c5c0001ef63f5000052584f68cd934c03980000000000000000057c80000001068258000013981b6000287400000008a599fab1d80005a2247a60c1054aae8000000000000004a600000005ff2412000000041200c03d20eca9e40000625800000007ae8de000000022b807c86c0a0185b8000000034b1762000030a9702c3e4f013f486780000002842ad29d68b6d2bc25c126cc6588a1a0001a5097b27aa000000092e80000000ab200000004bc00001a8a61834aac7800000005a49ee800000008140db868da44433493cc79110a401c000058f80000000000a8915109da11e4000289c8be171e52a9c4c0001b5e8cc98a69c980006fb00000549c3a539a986ab99cfe000146200000004968d5a21780003b1192e6400000000223c40b0000b4600007f980002d9899a4a3800082e0a9a00016b621380000f1a4e80f5831e8c4000081d857298d0b6a2bd0ee8000052e000000000000000001c000768dca5160df40001b32642800000014a2000000010f0eceb3d12065d98b8e0002a8a284000000028dc000000067e1c3800000000000ce4000158872b00000eb800091f80002c509ce30f88c05e59cec9b890ba04a9fa617e17981b70e040ef88d08149716817a6b49fd836a6a60ecc687ab7a40f87120b204ba6e80d9426f800000000000000000563000000000000000000ab8000036d1942000072000000007902308b149f287e9016841b02368601fa25721d7c77822d66fd233831c800000010a62020000105800000004c0505000000022500738000000000000000000128000000000039fa86ab7c857ab5d8000b52000
  | 52 => 0x80644b1948aa30346174241e9c10000000118821c926897f952017b0eb680f10581f100001be000081314ce7e300009a98c5aa840c2c40bad7848b8000818935c122167a1a72bd6ac895d40b615844608e2891700005c685f400023c472212ae817256275186104b789a62830fae49b2dbe62e089c28d88501ec0b22047a03eb88ab4c38724403b182a2ae806667441ffe8799776a4621f6ae30000b7500bc64317a6b27140889a1fda77a8bb0488a7385d827a42df00002fc000063b19ea9a092188399b78000000000022e61102890666054400007988299f529189f1a7939e02af7175e1991c66b5f12f6687218c447a1b80002a3eb7f01a2062861454b00be35221e2297a0200001cdea4480000001ccc3110000abdad96703096c00003b000008e20001176353a2aa1fd0000695000074e11a671f25921720cba994857013480001cf2d0206f9d9a35e2418000000016c0538008800026a02da0000000b4228da48804b66062adc5782d2e000087407b81ac000000006e0000000292a000000000000006f118c600026be00002c6aee03d200024c20001fea000000000022ea91d0e8c2839ab21d68e22000000085ea69c2652a1c8680000998000069c089e16400004df0fb227d0000b10000000014c839980005470afa000000000020ca000159635f26a800001dc7fc96b8b31800000000000001fdc53c0676000280021480201a414a4ab890cc387923c948a96aaab116200000008d38efc9470ab476d8bba4f792f441ea5cc749204e260288003598ce00014c4a22a66822e08ea9618000b5d000087f17366538f6a000000031c172c000158674d0134000002e61b00000000000827800066c00000d4814400000000000a7e8a01bd269a800000000005b8000000024f20000000000000027
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xdc4724c93144001bc0e5b8262880063da1b75c8510004ebc1aeb90a20019f0805d721440031ed0db9e4288003331cf624851000666398c490a20018fa86dc12144093ae6a0ba842881275c1417508510004bbc22ea10a2000975845d42144001ae700ba842880035c20175085100263bb02ea10a2004d73605d42144001ae480ba842880035c5017508510006b9182ea10a2000d72205d42144001a6d0aba042880034d6157408510006d9402e810a2000db1805d0214400996ec0ba042880136cd817408510006d9a82e810a2000db0505d02144001b6460ba042880036c881740851000cf9402e610a2000dd2305cc2144001aaea8b984288003555517308510006e2412e610a2000dd2805cc2144001ba300b98428801335d817308510026e9b02e610a2000dd3505cc2144001ba0a0b984288003749017308510006e8a02e610a2000dd2205cc21440031eb0fb1042880023de1d6208510006d2ba66410a2000dc573cc821440013cb0e1904288003695d03208510404bd43eea9822000c7876dd530440018f0ec3aa6088002ce610754c110036ac3aca69822000bd18194d30440033b10ea9a60880127ca07724c11000ced43c649822000ada868c930440c79b0ed19260882ff561d6324c1100866c3b06498220bed58750c930440017a30219260880035c1d7714c110004f943ca29822006d707594530440017a30728a608801b5c1d5514c1100266c3b66298220bdd5875cc530440099e0ed18a608814b5c1d6314c110125e8c1c6298220019d8874c530440099b0ec98a608813f561d5314c110005e4412629822004dd0714c530440035e10c98a60880133c1d9314c11027eb83aa629822010ed0634c530440017c10498a6088006f421d314c110026e843a629822001bd2864c530440037a10c98a6088093b4219314c11008769bb2629822004dd2764c53044009ba0ec98a6088003b41d9314c110005e9c2a629822000bd1854c53044001ea6ea98a608813f749d5314c11027ee83aa629822000f50754c5304409faa0ea98a60882f2f4e11314c1105e5e8c226298220bbdd3744c53044177ba2e898a60882ebd4d51314c1105d7a8aa2629822000fc3824c530440017a10498a6088003f0209314c110005e0412629822000dd3724c53044099ae0eb90a6088002f4e0f214c110004f9438429822000b71850853044093ae0ea10a6088002ec610214c110005e8c18429822000de3720853044001f806410a60880123e2197348110034bc42ae690220019e88754920440017a30638a40880027ca1e5148110036b83aca29022000bd18394520440013e10ea8a4088003d85495148110006e9b9c629022000dd1734c520440017c10498a40880527ca1f21481100f4f9438429022000b718508520440017630810a4088002f460c2148110
  | 1 => 0x8e8aa6c48830b1d5c554d89100161f3a2a93122000c3d745526244001c5aa8a14c48800e1fa1f75589100043ec26eab1220028be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c48800e1f21574589100046fc1ae8b1220108dc835d1624400117d0e3a2c4880030fdd474589100061e3a8e8b12200087e87d5162440070f90faa2c4880030fdd354589100161e3a6a8b12200087e8755162440010f90eaa2c4880030fdd154589100161e3a2a8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac48800317d5073589100062eaa0e6b122000ccc73dc96244005958e9212c488003331ce42589100147643a84b122002cac745096244001c5aa8a12c488003331cd425891000477c3ac43122000acc8358862441838f2e1aa0c48800b0f9d154189100061eba2a831220c0c7970550624400117f08bb4a48800a2f21176949100247c432e129220108de839d952440011bb073b2a4880021fe1576549100045fc22eca9220028bc845d952440011bf06bb2a4880423720d765491000c7b436e2a9220048fa86dc152440031e90cb8e64880123e21970cc9100247c432e1192200087f855d932440070f90abb264880022fe11764c9100145e422ec99220008df835d932440011df04bb264880063da1b714c9100043fc2aec192200387c855d8324400117f08bb0648800a2f211760c9100846e41aec192200b8ec825d832440031e90cb88648802f39189710c9100247c432e01922010cd8635c032440179d0c4b8064880067ca017394510006e9182e728a204fd57545ce5144001aaaa8b9ca28800374a017394510006e8c02e728a2004cd7605ce5144009ba6c0b9ca28813f74d41739451027ee8282e728a2000dd2405ce5144001ba280b9ca288003748817394510004dac20e4a8a20019f2801c951440092e90ea92a28814b5c141758c51000667b18e498a2000ccc631c931440c5b886239262880127560f754c51027eaba9eea98a20019f280dd5314409fae0a1baa62880063d219754c510004f2412ea98a2000ce476dc931440033e500392628800378880724c510006723b0e498a2062dc7731c93144001acea8392628800359550724c510006e3b18e498a2000dc4631c93144001b8ea639262880037114c724c510006e3218e498a2000dc5431c93144001bc500392628800378600724c51031673b00e498a2062de3601c93144001bc6a0392628800378140724c510006f1200e498a2000de1401c93144001b8e603926288003788c0724c510006e2980e498a20009d687cc93144001b88e59926288002f4603324c510024ea43a6498a2000
  | 2 => 0xd7458b1000c7a40ae8b1620c3c7471d5162c400187ee8aa2c58800b0f1d15458b106163a38aa8b162063cd471dcd62c40018bea9b9ac588003175537358b1031e6d086e6b162063cd910dcd62c40c59a8e239ac58800317d507358b100062eaa0e6b162062cce211cd62c40c59984239ac588003331ce4258b100247643a84b162000e2d5450962c4001998e6a12c588012b92054258b1000c7a40aed29620008df835d952c40211b906bb2a5880063d2057654b100243e43acaa962032c5e651cd52c40018baca39aa58818a37e1d63ccb1000c7a40aed19620638df835d932c40031e902bb2658818e37a1e634cb100246e43ac699620108dc835d832c40c59c842bb065880026d61072547102eeaba9eea98e20009e4825d531c40c5b8ee6392638800359d50724c710006b2aa0e498e2062dc5831c931c40c5b8ec6392638818b7118c724c710006e3a98e498e2000dc4531c931c4001b8c8639263880037150c724c710006e3980e498e2000dc5301c931c40c53ad0f9926388003711cb324c710006e23926498e20009d7835d721c40031ef0eb1643880123e60374d95100143fc3aa9b2a2000c3d7455365441818f2e0aa6ca8800a1f21774595100046fc1ae8b2a20108dc835d165440011df04ba2ca8802e3b20974595100143e43aa8b2a2000c3f745516544005878e8aa2ca883131ddd771595100061fba2a9b1a2002c3c74553634400587ce8aa4c6880030f5d15498d100070eaa28731a200387e87dd563440010fb09baac68800a2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187f0bba2c6880030f2177458d100043fc2ae8b1a200387c855d163440011df04ba2c68802e3b2097458d100045f438e8b1a2000c3f751d16344001878ea3a2c6880021fa1f5458d1001c3e43ea8b1a2000c3f74d516344005878e9aa2c6880021fa1d5458d100043e43aa8b1a2000c3f745516344005878e8aa2c68800b271d24358d100146e43a86b1a2002c9c7450d6344001c3aa8a1ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bd537258d1000636aa6e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440018dea8392c6880031b5507258d1000667218e4b1a2000ccd431c963440011bf0eb18c688002b32096318d1061e3ab8ea831a20c1c7970d50634400587ce8aa0c6880030f5d15418d106163ab8aa831a20c0c7970550634400117f08bb4a68800a2f2117694d100052ec1ecb29a20018f4865c653440018eecab8ca6880123e2197094d100063db2ae129a200087f855d9534400117f08bb2a68800a2f2117654d1000477c12eca9a200b8ec825d953440091f50db82a6880063d60774d891061e3ab8ea9b122000c3f74553624400587
  | 3 => 0x7b1e40028df8750f63c800593ce8a1ec7900038755143d8f200161f3a2a931e4000c3d7455263c800595ce8a14c7900038b5514298f200161f3a2a8b1e4000c3d7455163c800587ce8aa0c7900030f5d15418f200070eaa28631e4000e2d5450863c80170ff0eb2ca79000297e0d6594f200061fba2a8b0e4002c3c7455161c8001c5aa8a12c3901923be09764c72000c76412ec98e400bccc7298d31c8017998e4b1a639000a1fe1d54d95200161f3a2a9b2a4000c3d74553654800117f08b8eca9000a2f21171d95200062e328e6b2a40008df835d165480211b906ba2ca900023de0574595200247a40ae8b2a40008fb805d165480050f90eaa2ca900030fdd154595200062faa6e6b2a4000c5d54dcd65480018beea39aca9000317d5073595200062eaa0e6b2a4002c3e74553634800187ae8aa6c690003175d753d8d2000566c16a7b1a4000a9d8414f63480051bf0ea1ec6900038755143d8d200161f3a2a931a4000c3d7455263480051df0ea14c69000b2b9d14298d2000716aa28531a400387e87dd563480010fb09baac6900028f6107558d200043fc2ae8b1a400387c855d163480011ef02ba2c6900123d2057458d200043f43ea8b1a400387c87d5163480010fd0eaa2c6900021f21d5458d200161f3a2a8b1a4000c3d7455163480018b8ebb9ac69000237e1d6318d200052e42ac631a40108dc835d4634800587ce8aa0c6900030f5d15418d200070eaa28631a4000e2d5450863480014bb07b2ca6900021fe157654d200046fc1aeca9a4000c5f651cd52480658b8ca39aa4900e7331db7354920196663b0e6a9240018df8758e32480734b90ab1c649000237a1c634c9200046fc3ac61924032a5c8558c32480011bf06baec2900423720d75d85200161f3a2a9b0a4000c3d745536148005958e8a16c2900038b55142d85200047bc3ac230a40018f8809da51480018becb39ca2900af1719673945200363c32ae128a40048de839db31480574b90ab1e629000336d8d708c52005c76410ec98a40008de8798d31480091b90eb1a629009a97215634c52000c77436e498a4000cce631c9314800199ac639262900063e202760c5200043fc2aec18a400387c855d831480011bb0fb18629000336d8d700c5200866c31ae018a400487c8755165c400187ee8aa2cb8800b0f1d154597100246e41aeb31e20c3c7671d5263c400587ce8aa4c7880030f5d15498f106163b38aa931e2000e1d5450e63c400187ee8aa2c78800b0f1d15458f100246f43ea6b1e2000c5f75d4d63c40095ad03a9ac788002a76105358f100246e43a86b1e2000e1d5450d63c40090ff0eb2ca78800297e0d6594f1000c7b40eeca9e20008df835d662c40211b906bacc58800b0f9d15498b100061eba2a93162000e2d5450a62c40011bf06ba2c5880423720
  | 4 => 0x14c001878cbba2c2980031bd9772585300063632ee4b0a6000c6f651c9614c0018d8ca392c2980028f61065185304063d380ca30a60008f787584614c0091b9073b4a29810b1e9c365945300062fb2ce728a602bc5c659ce514c0031b90cb9ca29800317d9573945301362e32ae728a6006c78655c2514c0578b8cbbae62980ae3721975cc53015d2f436cb98a6000b1d84197314c0018b8cb396629800676a0272cc5300046ec3ec598a6000c78655c2314c0018decbb9262980031b197724c530006e4186e498a6000c6f651c9314c0018d8ca392629809b17197754c53000c6e432ea98a60009cc825d5314c04d4bd0db2a629810b171db654c5304062e3b0ca98a6000b1d84195314c0c9998edb92629800393197724c530006e4386e498a6000c5c651c9314c0c5998ec392629800393194724c53000667430e498a6000ccd861c9314c001a9eca392629800333994724c53000666328e498a6000d4c651c9314c001898ca392629800333d90724c53000666b20e498a6000d4f541c9314c001a9aa8392629818b33984724c53031666308e498a6000ccf601c9314c001b9420392629818a37a1f624c53000666396c498a609ee5465dc5314c001ca8cbb0a629800395d94614c530006e4396e098a6042c7a70d94314c001caeca98862980021fe1576c853001c3e42aed90a60018de86dcf214c0018b8cbb9e429800676a0373c85300062e328e790a600087f855da214c0070f90abb442980022fe1176885300145e422ed10a6000c5c659ce214c0031b90cb9c42980031719573885304bf263286510a6000c78655c2214c0070fd0bbb242980021f61776485300846e418ec90a60018de86dcd214c0018becbb9a429800317197734853000ced406e690a6000c5f651cd214c0018b8ca39a429800e1f21676085300246e41cec10a60018f8809d8214c0010ff0abb0429800e1f21576085300043e432ea10a600087f87d94214c0010fb0fb2842980030f9d365085302163d386ca10a6000c3f655d0214c001878caba0429802f2b18974085300062fb2ce610a6000c5c659cc214c0031b90cb98429800317d9573085300062e32ae610a6000cad74d88214c00199ae7b1042980027361c3208530497263286410a6000d8d740c8214c0018f6cab8042980031e195700853000675b12e010a6042c7a76d97304c085cb6c7b2e609800f1e9d865cc1300059cc20cb98260359d9878cb304c021ba662b8e6098002f220931cc1300143fc3aa9b2e4002c3e7455365c800187ae8aa6cb9002e1f21d54597200061fba2a8b2e400087f845d763c800187d0aba6c7900030f61574d8f2001c3fc3ea9b1e400087d87d5363c800587ce9aa6c7900030f5d354d8f200043fc3aa9b1e400087d8755363c800587ce8aa6c7900030f5d154d8f200164f3a48
  | 5 => 0x810a1fa1f43d95300043ec3e87b2a6000c3f74d0f654c0014dd05a1eca980029b60b43d95300061fba287b2a600087e8710f654c01f0fb0e21eca9810a9760f72d95300051f424e5b2a6000a3d849cb654c0010fd0fa16ca980021f61f42d95300061fba685b2a6000a5e83d0b654c0014bb07a16ca980030fdd142d95300043f43885b2a600087d8710b654c00147f08b8eca980028f21171d95302152ec18e3b2a6000a79801c7654c0010fd0fa0eca980021f61f41d95300061fba483b2a600087e87107654c0010fb0e20eca980030fdd041d95300052f41883b2a6000a5d83107654c0014dd0420eca980029b60841d95302153d40083b2a6000a7980107654c0010ff0aba2ca9800237e0d74595300047dc02e8b2a600287c87551654c00187ee8aa2ca9832717dd773595300061f432e832a6000c3c865d0654c001a3d06ba0ca980034760d74195303fe1fb1ae832a6012c3f605d0654c001a3c60ba0ca98003470c174195300069c182e832a6000d3a105d0654c0010ff0fb20ca980030f5d364195300043ec3cc832a6000c3d74990654c0014dd05320ca980029b60a64195300043fc3ac832a6000c3d74590654c1914bf06b20ca980029ee01641953001c3f438c832a600087d87190654c00187ae8320ca9831e97a1a43195300068eba48632a6080a5c8650c654c001a3ae8a18ca980e7171967294d3000ced404e529a6026c5c655c6534c0858f0e1b2aa69800f171db7554d30216ac386eaa9a6042c5c76d95534c00147b0832ec4980063760f74d893061e2eb9ea9b126002c3e74553624c00187ae8aa6c49830b175cd54d893001477c3a85b126000e2d5450b624c00187ce9b2cc4980028f61065989300061f3a0cb3126000c3f655d2624c001878caba4c49802f2b189749893000656ba6c5312600087e87d95624c0010fd0e32ac4980028f61065589306362fb98cab126000a3d84194624c0011df0eb10c49800b0f9d154189300061eba2a83126000e1d5450c624c001c5aa8a10c4980423720c765493000c6f436e6a926000c5f65dcd524c0738b8cbb9aa49800317d9473549301962e328e6a9260018de86dd6324c0033b501bac64980e717195758c9301cd2f436cb1926042c5e76d96324c085ab4e1b2c6498203179d8658c9300058ec20cb1926080d5a70196324c001c9ecbb14649800393194628c9300062e32ae319260019da805c6324c0033b70eb8464980cb17197750c9301946e432ea1926032a5e86d94324c00163b0832864982bb93196720c9303146e432e21926000c5c655c4324c00147b0832ec29800b0f9d154d85300061eba2a9b0a6000e1d5450f614c00147b0832cc298317175cc65985300043f43ecab0a6000c3c74d95614c0010fd0e32ac2980028f61065585300061e3a0cab0a6000c3f65dd16
  | 6 => 0x2579408e6b004214af1811cd60084175d505a9ac010802ba60b53580210072da9ca6b004200aba8414d60084015730829ac0108029ea1743580210053cc2e86b004200e3954d0d60084175d505a1ac010802ba60b43580210071caa286b004200a7a8510d60084014f30a21ac010802b6e0d52580210056c41aa4b004200a7a85d0960084014f30ba12c0108038e55342580210056d41e84b004200ad983d096008401c72a8a12c0108030fdd154d8d500052ec2e87b1aa000e1d54d0f635400159d05a1ec6a80029761443d8d500046fc3ac631aa0cba5f8558c63540211b906ba0c6a800b0f9d15418d500061eba2a831aa080a788055063540014bb0ba18c6a8003875534318d50005674168631aa000c3f7455362540011df0eb10c4a800b0f9d154189500061eba2a8312a00187c865d432540171f10cb8064a80433618d700c9500161f3a2a9b0aa000c3d7455361541959e2e1b0cc2a80023de1d611855005c77414ec98aa0008ed829d931540095ad03b1a62a800333d8c724c55000666318e498aa0048f8865c031540011bf06bb642a80423720d76c85500846f41cec90aa0008dd839d921540090f90b3b042a80061f21975085500247c432e010aa00287f8755365cc00587ce8aa6cb980030f5d154d97302153c402a9b2e601087c8755165cc00187ee8aa2cb980029ee0154597300161f3a2a93166000c3d7455262cc00593ce8a1cc598003875514398b3000c6e41ae8b1660008f7815d162cc0091e902ba2c59830f171cf5458b300161f3a2a8b166000c3d7455162cc1858b8e6aa2c5980063720d7694b301cc6fc1aeca9660018dc835d952cc0731bf0cbac65980e717995758cb3000c6fc3ac519660638df865c632cc00187ee8aa2c39800b0f1d154587300070eaa286b0e60048dd835da51cc0031bd07bb2a39818e37e1d62cc7301346ec36ea98e6026c5e65dd531cc00139904baa639800333dd8724c73000666c30e498e6000cce651c931cc001998ca392639800333d90724c73000666b20e498e6000d4f541c931cc001a9aa8392639818b33984724c73031666308e498e6000dca801c931cc001b930039263980023721d624c73000666392c498e60018dc835db21cc0c71bf06bb243980063720d76487300246ec1aec10e6000d8d740c821cc00187ae92a6ca980029760e54d95300143fc3aa9b2a6002c3e74553654c00187ae8aa6ca980022fe1171d95300145e422e3b2a6000c3d74d93654c00187ee9326ca980029ba0a64d953000536c14c9b2a6000c3f74593654c01f0fb0e326ca980030f5d064d95302152e43287b2a6000d1f7450f654c001c38c8a1eca980030fd0374d95300061ea06e9b2a600087d879d3654c00187ee93a6ca980030fe1174d95300061eba0e9b2a6000a5e831d3654c0854bb063a6ca9
  | 7 => 0xd5811c163084095ad03282c610802b56065058c210046f438a0b1842008dd87141630840153d08282c610802a76105058c2105d67410a0b184200acd8214163084095ad02282c610802b56045058c210052f42e80b184200a5d85d016308401c3aa9a02c610812b5a064058c210056ac0c80b184200e1d5450163084011bd0e202c6108023761c4058c210052f42880b184200a5d85101630841759d04202c610802b36084058c210256b40880b184200ad58110163084011bb0f102c610812b5a062058c210056ac0c40b184200c5f535da53084090ff0eb2ca61080297e0d6594c210070fa9ac92984203a5e8558e53084171d904bb2a6108121f21d6554c2105e56392c8a9842048dc8758d53084018dacbb92a6108032b5937254c2100666b1ee4a984239c5e65dcd52084018bacbb9aa4108032799373548210064eb26e6a904200cda60dcd52084658bcca39aa4108031759473548210064f320e6a904200c9d641cd52084019b4c039aa41080237a1e63548210846e43cc6a9042008de8758d52084011b90eb1aa4108038ba1564cc82100716c2ac9990420bcae7359332084c995ee2b2664109932b5c564cc8213274798ac99904264e8d3159332084c9d4e20b26641080393d5163cc82100726aa2c79904264ec71058f3208417c9864b2a641082fa30c9644c82105d66412c69904200c6f545d832084018daa8bb0641082f33a0d760c82105e66c1aec1904200ccf535d83208401998a6bb064108033390d760c82100666a1aec1904262cce315d832084c599862bb064108038ba15640c82100716c2ac81904200e8e835903208401d1b06b2064109932b9cd640c82105f4739ac81904200e8f535903208401d18a6b20641082f2bdc5640c82105f5338ac81904262cad715903208417d4ae2b20641098ba38c5640c8213174618ac81904262ea71059032084c91df0eb186410993339cd630c8210063baa6ec9084200c7554dd921084019af07bb242108033520f764842105e73296ec9084200cd776dcd21084019aeec39a421098b71dc8734842100673bb2a49084202c3e74551600840187ae8aa2c0108123ea1f40580210053d42e80b004200a7985d016008401c72a9a02c0108123e21d40580210071caa280b004200aba841d56008401573083aac010802b6a0c75580210056cc18eab00420baea821d560084295d3043aac010812bca0475580210a578c08eab004200a7a859d160084014f30b3a2c0108029ea1474580210053cc28e8b004200ada831d160084015b3063a2c01082ebaa0874580210a574c10e8b004204af2811d160084295e3023a2c0108038ed5254580210071dc22a8b004200e3a745516008401c72e8aa2c010b038e90554580216071c20aa8b004200a7b855cd60084014f10ab9ac01082eba20973580210
  | 8 => 0x4282c810812ada0450590210055ac08a0b20420baae828c1640840155b05182c810812ada0630590210055ac0c60b204204ab6810c1640840156b02182c810802a7a0e20590210054ec1c40b204204ab681881640840156b03102c8108123720d7598c210246e41ae93184202c3e74552630840187ae8aa4c61084317dd75398c210052f42e873184200a5d85d0e6308401c3aa9a1cc61082eb3a0b4398c210070eaa287318420087f855c263084070f90ab84c6108123720d7098c210862fbaceb3184200a5e859d263084014bb0b3a4c61082eb3a0a7498c2100566c14e931842c0a5d859526308401c3ea92a4c61080387e115498c210070f3a2a93184200e1d745526308581c3c82aa4c610b03871055498c2160d2f428a931842108de87d0a63084011bb0fa14c61080297a174298c210052ec2e853184200e1d54d0a6308401c3aa8a14c61080297e157098c210052e42ae131842108de8714263084011bb0e284c610802a7a105098c210054ec20a1318420bace82142630840159b04284c610812b5a045098c210056ac08a13184200a5e85d0263084014bb0ba04c610803875534098c210070eaa28131842108de8710263084011bb0e204c61080297a144098c210052ec2881318420bace82102630840159b04204c610812b5a044098c210056ac088131842108de8788263084095ad03104c610802b56062098c2105c76412e8b1842048f4815d1630840587ce8aa2c6108030f5d15458c210246f43ea6b184200c5f75d4d630841759d05a9ac610802a7a105358c210054ec20a6b1842048de87d0d63084014bd0ba1ac610802976174358c210070eaa686b18420bace82d0d63084091b90ea1ac610803875514358c210052f42886b184200a5d8510d63084095ad03182c610812b5a043058c210062fbaceab18420bace829d5630840159b053aac61082eb32097558c210054f420eab184200a9d841d563084014bd0b3a2c610802976167458c2105d67414e8b184200acd829d1630840159f04ba2c61082eb32097458c210056bc0ae8b184204ad4815d163084014bd0a3a2c610802976147458c2160f2b886a8b1842c0a5d859516308401c3ea92a2c61080387e115458c210070f3a2a8b184200e1d745516308581c3c82aa2c610b03871055458c216072b882a8b1842c1a5e85151630840199cea392c610803331d47258c2100667ba0e4b184200ccd741c96308401c9ea8392c610803935507258c2131667388e4b184262ccc711c963084011bd0fa12c6108023761f4258c210052f42e84b184200a5d85d096308401c3aa9a12c610803875514258c2100666396e0b18420bace829c1630840159b05382c610812b5a067058c210056ac0ce0b184200a5f855c163084014b90ab82c61082eb32097058c210256b408e0b184200a
  | 9 => 0x724c52131667390c790a4200c3f745536048405878e8aa6c0908038b55142d81210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d604840187ea8ba2ca108123d20574594210243f43ca8b284200c3f7495165084090f90eaa2ca108030fdd154594210253b40ca0b2842c1c7710dd165085810fb0f3a2ca108030fdd274594210053bc0ae8b284204a74815d1650840187f08ba2ca108031de0574594216063a40ae8b2842c0c3e415d1650858187882ba2ca10b031dc41745942160c3f438e8b284200c5f739cd65084174d904b9aca108028fa1073594210051ec20e6b28420087e87d0d65084010fb0fa1aca108030f5d3435942105d3741686b284200a6d82d0d650840187ae8a1aca108021fa1c43594210043ec3886b28421687e87d0965084010fb0fa12ca1080297a0f42594210052ec1e84b284204a76819c165084014eb03382ca108028fa1070594210051ec20e0b284200a5e831c165084014bb06382ca1082e9ba0870594210b536c10e0b284204a76811c1650842d4eb02382ca108021fa1f40594210043ec3e80b284200c3d74d0165084094ed03202ca108029d60640594210061eba280b28420087e8710165084010fb0e202ca1080297a0c40594210052ec1880b28420ba6e8210165084014db04202ca108129da0440594210053ac0880b28420ba6e828c165084014db05182ca108129da0630594210053ac0c60b284204a76810c165084014eb02182ca1080297a0e20594210052ec1c40b284204a768188165084014eb03102ca108030fdd675590216051ec3ceab2042c1e2f219d56408583c5a433aac810b078dc4275590216755bc0aeab204204ab4815d5640840187f0ebaac8108030fdc975590210061eb92eab204200e37815d56408581c6902baac810b030f9c575590216061e38aeab2042c0e2f215d56408581c5a42baac810b038dc41755902160d1f428eab204200a3e85dcd640840147b0bb9ac8108030f5d7735902105d57416e6b204215aad82dcd640840187aeab9ac810b36abe09735902105d56412e6b2042ccab7815cd640840956902b9ac8108028fa1473590210051ec28e6b20420baae82d4d640840155b05a9ac8108022fa1c53590210045ec38a6b204200a3e85dc1640840147b0bb82c8108030f5d770590210255b40ce0b204248ab5819c1640840187aeab82c8108028fa1470590210051ec28e0b204200a9e831c1640840153b06382c81082eaba0870590210ad56c10e0b204204ab6811c1640842b56b02382c810812ada0650590210055ac0ca0b2042008be87141640840117b0e282c810802a7a0c50590210054ec18a0b20420baae82141640840155b
  | 10 => 0x31a4200a5e85d0c63484014bb0ba18c690803875534318d2100566c168631a4200e1d5450c6348401c5aa8a10c6908021fe157018d2101c3e42ae031a4210cd8305c063484011bb0f328c690802a7a126518d210054ec24ca31a42008df8759463484011bb0f320c69080297a166418d210052ec2cc831a42008df8759063484014bd0a320c690802976146418d210062f3b6a831a4200c5e765506348401c3ec8aa0c690803871915418d21005674348431a4262acc865086348401d1ec8a10c690803c35514218d210862fbacea31a4200a5e859d063484014bb0b3a0c690802b3a0a7418d2100566c14e831a42d0e4e21d5063485a1c9843aa0c690802976165418d210070faa4a831a4200ace82950634840159b052a0c69080387e115418d210070f3a2a831a4200e1d74550634859fc3c82aa0c690b3f871055418d2167f2710aa831a42cfe4c2155063484014bd0a2a0c690802b3a085418d2100566c10a831a4200a9e84148634840153b08290c69084237a1f4218d210046ec3e8431a4200a5e85d0863484014bb0ba10c690803875534218d2100566c248431a4200e4f549086348401c9aa9210c69098ab3a064218d213156640c8431a4200e1d5450863484015af02a10c69098ab52054218d2100747c228431a4200e4f545086348401d1ca8a10c690803935514218d2100746aa28431a4200e0d545086348401d8f02a10c69098ab3a054218d213156640a8431a4200ec48150863484014bd0a210c690802976144218d21005674108431a4200a9e84d44634840153b09a88c690802b3a0b5118d2100566c16a231a4200a5e85d0463484014bb0ba08c690802b3a0b4118d2100566c168231a4200e8d42d04634840159f04a08c690802b32094118d2100746a128231a4262acf8248463484014bf0ab80c690802972157018d210866c382e031a42108de8714063484011bb0e280c690802a7a105018d210054ec20a031a4200ace82140634840159b04280c69098ab5a045018d210056ac08a031a4200a5e85d0063484014bb0ba00c690803875534018d21005674168031a4200acd82d006348401c3aa8a00c69084237a1c4018d210046ec388031a4200a5e8510063484014bb0a200c690802b3a084018d2100566c108031a4262ad68110063484015ab02200c6908023761e2018d213156b40c4031a4200ad581880634840159d05080c690802b360a1018d210846e41aed29a42008df835d953484011df04bb2a69080e37a1f6354d213146f436e6a9242638de861cd52484651bd0fb1aa49098e3721f63549211cc6f438c6a9242108dc8718d52484c79a8e3b1a64908033318f7254521004d6c20e4a8a4200ccc631c951484c51dd0d39662908433318e72cc5210866631ae598a4200ccc63dc9314840199ec6392629098b3318c
  | 11 => 0xc84090f90eaa2cb108030fdd154596210161e3a2a8b2c42048dc835d6638840587ce8aa4c7108030f5d15498e210070eaa28731c4200c3f745516388405878e8aa2c71081237a1f5358e210062fbaea6b1c4200acd82d4d638840153b0829ac7108123721d4358e210070eaa286b1c42628df8758f32884c51df0eb1e651098e37a1e634ca21315e240a641944262bc6819cc328840187ee8aa2c11080b0f1d154582210247c43a80b044200e395450160884050ff0eaa6ca908030f5d154d95210046fc1ae8b2a42108dc835d165484011ef02ba2ca908023ee01745952100c7c402e8b2a420287c87551654840187ee8aa2ca9080b0f1d154595210062faa6e6b2a4200c5d54dcd65484018bea839aca908031755073595210066639ee4b2a4200c3f745536348405878e8aa6c690803175d753d8d210054f420a7b1a4200a9d8414f63484014bd0ba1ec6908029761743d8d210070eaa687b1a42028df8750f6348401c3aa8a1ec69080297a1443d8d210052ec2887b1a4200ad5810c3634840153d0932ec690802a761265d8d210052f42cc9b1a4200a5d8599363484014bd0a326c6908029761464d8d210070fb22a9b1a4200e1c6455363484c75990ca16c690803a319142d8d2100786aa285b1a4200a9e849d7634840153b093aec690803175d475d8d210052f42ce9b1a4200a5d859d363484014bd0a3a6c6908029761474d8d2100567410e9b1a4263acd821d36348401c3ea92a6c69080387e1154d8d210070fba2a9b1a4200e1c7455363485a3c3c82aa6c690b478710554d8d210054f420a5b1a4200a9d8414b63484c71bd0fa16c6908023761f42d8d210052f42e85b1a4200a5d85d0b6348401c3aa9a16c6908038755142d8d210052f42885b1a4200a5d8510b6348401d1a84216c690802a7a1351d8d210054ec26a3b1a4263e5651d4763484014bd0ba0ec6908029761741d8d210052f42ee1b1a4200a5d85dc363484c75ad03386c690802b560670d8d210066db84e1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4200ace82143634840159b04286c69098eb5a0450d8d210056ac08a1b1a4200a5e85d0363484014bb0ba06c6908038755340d8d210070eaa281b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a4200ace82103634840159b04206c69098eb5a0440d8d210056ac0881b1a42008dd8788363484c75ad03106c690802b560620d8d210161f3a2a931a4200c3d7455263484051df0ea14c69080b2b9d14298d2100716aa28531a42008df835d163484011df04ba2c6908023de057458d210061fba2a8b1a4202c3c7455163484018dea9b92c6908031b5537258d210046fc3ac631a42108dc835d463484211b906ba0c69080b0f9d15418d210061eba2a8
  | 12 => 0x80339dd8724c431316e3b98e49886202c3e74551600c40187ae8aa2c018843b4cc131580310247d43e80b006200a7a85d01600c4014f30ba02c0188038e55340580310247c43a80b006200e3954501600c401575083aac018802ae61075580310856d418eab006220ad9831d5600c4015d5043aac018802ba608755803102579408eab006220af1811d5600c4014f50b3a2c0188029e61674580310053d428e8b006200a79851d1600c4215b5063a2c018882b660c745803100575410e8b006200ae9821d1600c4095e5023a2c018882bc604745803160f2d98ea8b0062c1e7231d51600c583cb263aa2c0188038ed5254580310071dc22a8b006200e3a74551600c401c72e8aa2c018b038e90554580316071c20aa8b0062c0e5b31551600c581ce462aa2c018b03964c554580310872d29ea6b006200a7a85d0d600c4014f30ba1ac0188038e55343580310057541686b006200ae982d0d600c401c72a8a1ac018842b6a0f72580311056cc1ee4b006204af281dc9600c4415e303b92c0188029ee1572580310053c42ae4b006210ad8835c9600c4215b507a92c018802b660f52580310056dc1aa4b006210ad883549600c40157508292c018802ae61052580310053d42e84b006200a7985d09600c401c72a9a12c018842b6a0f42580310056cc1e84b006200e3954509600c4015b706a12c018842b620d425803100579c0a84b006204af081509600c4014f50a212c0188029e614425803131f6918c64b006200e5b548c9600c401cb2a9192c01898eb6e06325803131d6cc0c64b006200e5b540c9600c401cb2a8192c018843b2a0832580310076521064b006200ec9420c9600c4215b702192c018843b4a0432580313156cc0864b006210ed1810c9600c4c5d9442192c01898bb2084325803100739aa262b006200e71544c5600c409da70698ac018843b49cd31580310876929a62b006200ed1534c5600c401dc70498ac018803b820931580310143fc3aa9b2e4202c3e7455365c840187ae8aa6cb9080237e0d74597210846e41ae8b2e42008fb805d165c84031f100ba2cb9082e1f21d54597210061fba2a8b2e4200a778155165c84018bea9b9acb908031755373597210062faa0e6b2e4200c5d541cd65c840587ce8aa6c7908030f5d154d8f210062ebaea7b1e4200a9d8414f63c84051bf0ea1ec79080b279d143d8f210070eaa287b1e4202c3e7455263c840187ae8aa4c79080b2b9d14298f2100716aa28531e4202c3e7455163c840187ae8aa2c7908423720d7518f210161f3a2a831e4200c3d7455063c8401c3aa8a18c7908038b5514218f210046fc1aeca9e42638df8758f31c84c91df0cb96639098a37a1e634c72105e66394c698e420bccc7258d31c840587ce8aa2c1908030f5d15458321016563a284b064200e2d5450960
  | 13 => 0x727aa2863126200e8e5450c624c401c9aa8a18c498803a3551431893100706aa2863126200ec78150c624c4c559d02a18c49898ab320543189310076240a863126200acf8050c624c4014dd0a218c4988029b614431893100557426a23126200aad84d44624c40159d07a88c498802b360f51189310053742e823126200a6d85d04624c40159d07a08c498802b360f411893100567c1a823126200acc83504624c40159d07380c498802b360e70189313157340ce03126200ae5819c0624c40159d07280c498802b360e50189310072629ca03126262ae681940624c4015cb03280c49882e3ba1c501893100476c38a03126200aae84140624c40155b08280c498802b3a0c501893100566c18a03126200e4c53140624c4c55cd02280c498802b960450189310053742e803126200a6d85d00624c401c5aa9a00c498802b3a0f401893100566c1e803126200ace83900624c40159b07200c49898ab9a06401893100572c0c803126200e2d54500624c4171dd0e200c4988023b61c401893100537428803126200a6d85100624c40159d06200c498802b360c401893131573408803126200ae581100624c4c55cd03180c498802b9606301893131573408603126200ace83840624c40159b07080c49882e3b209769493105e66314e7292620bccc625ce524c4071dd0fb12a498803331cf625493100667b98c4a926200ccc73189524c4018bea93b664988031755276cc93131667c14ed9926200cce429db324c40199a853b6649898b3388676cc9313166610ced9926200cce76d8b324c4c599cec3166498803339d462cc931006663a8c59926200ccf7418b324c40199ae8316649880393d5062cc93100726aa0c59926262cce7118b324c4c5998e231664988033318970cc9313267238ec49926200ace86dc9324c4c9998edb126498802b3a1c624c93105e67438c49926200cce75189324c401998ea312649880333dd0624c93100666ba0c49926200e4f54189324c401c9aa8312649899371dc8714c931005e8c00e29926200ccc62dc1324c4018becbb9aa29880333dcc625453100666398c4a8a6210dd3305c3314c40187ee8aa6c09880b0f1d154d81310070eaa287b0262008ee87d89604c4018deebb12c0988031b1d7625813100657ba6c4b026200cac74d89604c4011dd0e312c0988031bdd46258131006363a8c4b026200caf74189604c401958e8312c0988121f21d54594310061fba2a8b286202c3e74552620c40187ae8aa4c4188038b55142988310161f3a2a8b106200c3d74551620c4091d90ea12c4188038b55142588310066d306e6a906210ccc73989520c4091d90eb12a41880317d51768c8310062eaa2ed1906200c7754dd9310c4018eaa9bb262188433594f764c4316956bc32a69886200cd77654d310c4019ceedb926218
  | 14 => 0xd84d47624c4c9ccca3a8ec4988029ba1741d893100536c2e83b126200ace831c3624c4c959b06386c498992b9a0470d893100572c08e1b1262008ee87143624c4011db0e286c498802aba1050d893100556c20a1b126200ace83143624c40159b06286c498992b9a0450d893100572c08a1b126200a6e85d03624c4014db0ba06c4988038b55340d893100716aa281b1262008ee87103624c4011db0e206c4988029ba1440d893100536c2881b126200ace83103624c40159b06206c498992b9a0440d893100572c0881b126264ae6810c3624c4011df0eb10c49882f2b10974189310161f3a2a83126200c3d74550624c40159b05a98c498802a7610531893100566c10a63126200acd8290c624c401c3aa8a18c498802b3e0943189310053742e843126200a6d85d08624c401c5aa9a10c498802b360f421893100716aa2843126200acd83880624c4015cb03100c4988023b61e651893100557424ca3126200aad84994624c4011df0eb28c4988023b61e64189310053742cc83126200a6d85990624c4011df0eb20c4988029ba14641893100536c28c83126200e2f64550624c401c58c8aa0c49898ab3a1b531893100727b2ea63126200e4c65d4c624c4c578d03a98c498802b3a185318931005c6c20a63126200ace8690c624c4c55990ca18c498803a3d91431893100786aa2863126200acf835d4624c4014dd0b3a0c4988029b61674189310056741ce83126200acd839d0624c417958e8ba0c49880393e0f54189310072641ea831262d0e4e31d50624c5a1c9863aa0c4988038bd5254189310056741ca83126200acd83950624c40159f06aa0c498802b320d541893100717c22a83126200e2e74550624c401c5ae8aa0c49880393e0d54189310072641aa831262cfe2e41550624c59fc5882aa0c498b3f938c5541893167f2618aa83126200ace83150624c40159b062a0c498802b361f531893100566c26a63126200e4f54d4c624c401c9aa9a98c49898ab3a0753189313156640ea63126200acd80d4c624c401c9ea7298c498802aba10531893100556c20a63126200acd8714c624c401c9d0a298c498803939d4531893100726ba8a63126200e8e8414c624c40159b08298c498803a3610531893100546c20a63126200e4f5414c624c401c9aa8298c49898ab3a04531893131566408a63126200acd8014c624c4171dd0fa18c4988023b61f43189310053742e863126200a6d85d0c624c401c5aa9a18c498802b361e43189310056742c863126200acc8590c624c401d1ce9218c498803a35d2431893100727aa4863126200e4d5490c624c4c559d03218c49898ab3206431893100566c04863126200e2d5450c624c4015cf02a18c49898ab9205431893100567c3a863126200ace8550c624c4015990aa18c498803a3e11431893100
  | 15 => 0xeb18c6a8802b32096318d510161f3a2a831aa200c3d74550635440187ee8aa6c4a880b0f1d154d895100477c3ac4312a200acc83588625440187ea8ba0c4a88030fa1574189510061ec2ae8312a20bc3f525d0625441787aa4ba0c4a882f2b0c9741895105e5790ae8312a202c3e74550625440187ae8aa0c4a8802ab61062cc9510062ebaec7192a20b8f4865c4325440187ee8aa6c0a880b0f1d154d81510046fc1ae5b02a2108dc835cb60544050ff0eaa6cb9880b0f9d154d97310061eba2a9b2e62048dc835d165cc4011f700ba2cb988063e20174597310843e43aa8b2e6200c3f7455165cc5818b8e6aa2cb9880b0f9d15498b310061eba2a93166200c5d75d4e62cc40159b05a9cc598802a76105398b310164f3a2873166200e1d5450e62cc40587ce8aa2c5988030f5d15458b310161f3a2a8b066200c3d7455160cc401c3aa8a1ac1988121f21d54596310061fba2a8b2c6202c3c74551658c40587ce8aa4c5188030f5d15498a3100716aa2853146200c3f74551628c405878e8aa2c5188123b21d4258a3100716aa284b146239c5e65dcd528c4018bacbb9aa51898af1205320ca31315e340ce41946200c3f74551608c405878e8aa2c1188123e21d40582310071caa280b0462048dd83dd3654c4050ff0eaa6ca988030f5d154d95310052fc1aa9b2a62c0c5d73553654c4014bb07286ca988023be09745953105c76412e8b2a62008fb805d1654c4031f100ba2ca9880a1f21d54595310061fba2a8b2a6202c3c74551654c4018dea9b92ca988031b553725953100667b98e4b2a6200c6f541c9654c4018daa8392ca9880333d4c725953100666298e4b2a6226c5f73d95534c40187ee8aa6c49880b0f1d154d893100557420a5b126200aad8414b624c4014dd0ba16c4988029b61742d893100716aa685b1262028ef8750b624c40595ce8a16c4988038b55142d89310053742885b126200a6d8510b624c40155d0932ec498802ab61265d89310053742cc9b126200a6d85993624c4014dd0a326c4988029b61464d893100717b22a9b126200e2c64553624c4c959d0da9ec49880393d9753d8931325e340ea7b126200b8d8414f624c4c95990ca1ec498803a319143d893100786aa287b126264acd83dd7624c40155d093aec498802ab61275d89310053742ce9b126200a6d859d3624c40195ee93a6c4988029ba1474d893100536c28e9b126200ace831d3624c4c959b063a6c4988038bd5254d893100717c22a9b126200e2f74553624c401c58e8aa6c498b4f8b90554d893169f1620aa9b126200e4f5394f624c40155d0829ec498802ab61053d89313247743e87b1262008ed87d0f624c4014dd0ba1ec4988029b61743d893100716aa687b126200e2d5450f624c4014dd0a21ec4988029b61443d893100557426a3b126200aa
  | 16 => 0x298e510070eaa28531ca22ba5e8510a63944014bb0a214c72880297e157098e5115d2f42e8131ca200a5d85d026394401c3aa9a04c728803875514098e510846f4388131ca2008dd8710263944574bd0a204c728802976144098e51005674108131ca200acd8210263944095ad02204c728802b56044098e510846f43c4131ca2008dd8788263944095ad03104c728802b56062098e510061eba2a8b1ca200a5d85d0d6394401c3aa9a1ac728802b3a0b4358e5100566c1686b1ca2048dc8750d6394401c3aa8a1ac728802976144358e510256b40c60b1ca204ad6810c1639444d4bd0b3a2c728802976167458e5100567414e8b1ca200acd829d1639444d4bd0a3a2c728802976147458e5160d2fc22a8b1ca226e1f845516394401c3ce8aa2c728803875d15458e516070f20aa8b1ca2c0e1c415516394581cae20aa2c728803335c87258e510046f43e84b1ca2008dd87d09639444d4bd0ba12c728802976174258e510070eaa684b1ca200e1d54509639444d4bd0a212c728802976144258e5100567414e0b1ca200acd829c163944095ad03382c728802b56067058e510052fc2ae0b1ca204ad6811c163944015ab02382c72889a97a174058e510052ec2e80b1ca200e1d54d0163944095ad03202c728802b56064058e510070eaa280b1ca2008de8710163944011bb0e202c72889a97a144058e510052ec2880b1ca200ace82101639440159b04202c728812b5a044058e510056ac0880b1ca2008de8788163944011bb0f102c728812b5a062058e510056ac0c40b1ca204ad68108163944015ab02102c72880b0f9d15498a510061eba2a9314a200e2d5450a629440187ae8aa2c5288123b21d4258a5100716aa284b14a20bacc8258d32944219acc6b8865288030f5d154582510846f41ee4b04a2008dd83dc960944014f30ba02c1288038e55340582510247c43a80b04a200e3954501609440d4f50b3a2c1288029e61674582511753d428e8b04a200a79851d160944015b5063a2c128802b660c745825100575410e8b04a200ae9821d160944095e5023a2c1288babc604745825160d3dc22a8b04a206e3b845516094401c74e8aa2c1288038e5d154582516071d20aa8b04a2c0e384155160944014f70ab9ac128812bca04735825117578c08e6b04a206a7a85d0d60944014f30ba1ac1288038e55343582510057541686b04a200ae982d0d6094401c72a8a1ac12881a9ea1443582510053cc2886b04a200ada83dc960944015b307b92c128812bca07725825117578c0ee4b04a200a7b855c9609440d4f50ba12c1288029e61742582510071caa684b04a200ada83d0960944015b307a12c1288038e55142582510353d42884b04a200a798510960944095e502192c128802bc60432582510061fba2a9b1aa202c3c7455363544011bf0
  | 17 => 0xaa404cf0615c261548011bd0fb1ac2a900237a1c63585524be67b90c6b0aa4008f787584615480187ee8aa6c0a90029e61740d81520071caa681b02a4008de87d8d60548011bd0e31ac0a900a1fe1d54d97320161f3a2a9b2e6400c3d7455365cc8210f90eaa2cb990030fdd154597320061fba2a8b0e6402c3c7455161cc8c91dd0f212c39900b2b9d1425873200716aa284b0e6402c3e7455160cc80187ae8aa2c1990038b55142583320143fc3aa9b2c6402c3e74553658c80187ae8aa6cb1902e1f21d54596320061fba2a8b2c6400a5f83551658c8014bb07282cb190e717dcd6554e321cce7c3aa599464ae9cf8754f328c80187ee8aa2c31900b0f1d1545863231c6f438a6b0c6400a9d8414d618c8c75ad0229ac31918e37a1e43586320070eaa286b0c64638de87cc9618c8c75ad03992c31900b0f9d154582320061eba2a8b046400e1d5450d608c8050ff0eaa6ca9900b0f9d154d95320061eba2a9b2a64008df835d1654c8011ef02ba2ca990123d20574595320047dc02e8b2a64018f8805d1654c8050f90eaa2ca990030fdd154595321ce2fb9aa8b2a6400c5f65dcd524c8738b8cbb9aa49918e37219718c93231e6a30ae31926402c3e74553614c80187ae8aa6c2990038d55041d85320056ac1883b0a6400ae582107614c8015e30020ec2990023de1d611853231e6db1ae030a6402c3e74553604c80187ae8aa6c09900a1fe1d54d94320161f3a2a9b286400c3d74553650c8211b906ba2ca190023ee01745943200c7c402e8b28640b87c87551650c80187ee8aa2ca190429720d54594321962e39aa8b286400c5f54dd9320c8018baa9bb2641902f3394b764c832084e643aa49906400ccf76549320c8018dea9bb264190031b553764c8320866729eec9906400ccf7654d320c80187ee8aa2c21900b0f1d154584323146f43ea6b086462ad681d4d610c80153b0829ac219002b360853584323156b408a6b0864628dc8750d610c801c3aa8a1ac21918a3b21d425843200716aa284b0864628de87cc9610c8c55ad03992c21902fb108732584323146e43a64b086462ad4814c9610c801c6aa920ac21902e3d21d415843200752a1282b086402c3e74551600c80187ae8aa2c019003875514358032016563a284b006400e2d54509600c8171f10ea02c0190038e55140580320161f3a2a931ca200c3d7455263944014bb0ba1cc728803875534398e51005674168731ca200acd82d0e6394401c3aa8a1cc728843330c97298e5115d2f42ce931ca200a5d859d2639440159d053a4c728802b360a7498e5160d2fc22a931ca22be1f845526394401c3ce8aa4c728803875d15498e516070f20aa931ca2c0e1c415526394421998e4b94c72884237a1f4298e510046ec3e8531ca22ba5e85d0a63944014bb0ba14c728803875534
  | 18 => 0x480193ee93a6c6a90e697a1474d8d520052ec28e9b1aa400ace821d3635487359b043a6c6a90e697e1154d8d521cf0fc22a9b1aa400e1f745536354801c38e8aa6c6a90e637a1f42d8d520046ec3e85b1aa439a5e85d0b63548014bb0ba16c6a90038755342d8d520070eaa285b1aa439a5e8510b63548014bb0a216c6a9003a350842d8d521cd66c16e3b1aa400ada809c763548015b30138ec6a90029761471d8d521cd2f42e83b1aa400a5d85d076354801c3aa920ec6a900237a1c41d8d520046ec3883b1aa439a5e8510763548014bb0a20ec6a90038755041d8d520056741083b1aa400acd8210763548015b50020ec6a9002b660041d8d520052ec2ee1b1aa400ad6819c363548015ab03386c6a9002b3a0870d8d521cd66c10e1b1aa439a5e85d0363548014bb0ba06c6a90038755340d8d520070eaa281b1aa4008de8710363548011bb0e206c6a90e697a1440d8d520052ec2881b1aa400ace82103635480159b04206c6a9002b5a0440d8d520056ac0881b1aa4398de8788363548011bb0f106c6a9002b5a0620d8d520056ac0c41b1aa4008de8704363548011bb0e086c6a900237e1d6318d520864e21ae831aa402c3e74550635480187ae8aa0c6a9002976174318d520070eaa68631aa400acd82d0c6354801c3aa8a18c6a90023761e6418d526a566c14c831aa4008df8759063548015af02b20c6a9002b52056418d520056dc02c831aa400ad8805906354801c3ec8aa0c6a9002b5a066018d520056ac0cc031aa432a5e859d063548014bb0b3a0c6a9002b3a0a7418d526a566c14e831aa410c9c745d063548654bf08aa0c6a90cb87e115418d520070f3a2a831aa400e1d7455063548211bd0fa10c6a90023761f4218d521952f42e8431aa400a5d85d086354801c3aa9a10c6a9003875514218d521952f4288431aa400a5d85108635492f59f04b88c6a90ca97a174118d520052ec2e8231aa400e1d5490463548211bd0e208c6a90023761c4118d521952f4288231aa400a5d851046354801c3aa8208c6a9002b3a084118d5200566c108231aa400ada8010463548015b300208c6a900297e157018d521952f42e8031aa400a5d85d006354801c3aa9a00c6a9003875514018d520846f4388031aa4008dd8710063548654bd0a200c6a9002976144018d52005674108031aa400acd8210063548015ad02200c6a9002b56044018d520846f43c4031aa4008dd8788063548015ad03100c6a9002b56062018d52005674142031aa400acd8284063548211bd0e080c6a90023761c1018d521cf27b16c7292a402c3e74553615480187ae8aa6c2a90029d61741d85520053ac2883b0aa400e355410761548015cb0420ec2a9002bc60041d85520066d386c730aa400cda7018e61548019b6c6b84c2a90033618d709855200679b0ae13
  | 19 => 0x80c81780100100400100200a00000380500080080380280a80200000e80000c00180180200180181500000000d00000280000080100100080280000600080000000100780180b80300500080100782700180202700a80900a80000080000080100080a00580280380080600000000480000180600000200000200880280480b00381480100101100000400200281700300200100380180880100000a80200000580280200200700280180280580100081a80080600000680981c80200980180680180c80180300000200280700180180300300080000000580100000a00400080000080300880400080180180500100c80000200200080380500280080100000300000700000b80000100100280280701380100700200080580100181c80680580400100480200a00e00000000000b80000280001700000100080080180080001680100900080380a80280100480180001200100880000480300180c00500180700000100000280000000900000000080900180200180600100700000101d80080081100000680100200500080580280180001900000000000100000300180300500400300000100201a80000100000200000080080100680e00080000082a80200280000180500000b80000480080180000301780080000000000100080000380500080000880000c80180300100380080200000300180000200000000300180000000080380280200080000080100780080200400300000381180000100280000180300000300180200080200180000180100180000200180500100081100100001200000100000280b80680000100180880580e00380380300000000000480180500080100200000480000180000580d80000000000001980100200000880000000a00080381a80b0f9d15498a530061eba2a9314a602c3e745516294c0187ae8aa2c5298030fdd154586530161e3a2a8b0ca602c3e745516094c0187ae8aa2c1298030fdd154d895301477c3a85b12a602cae7450b6254c01c5aa8a16c4a98023be1d62189536ad67c1ac4312a602c3e745506254c0187ae8aa0c4a98038b55142189530161f3a2a9b0aa600c3d745536154d3d9aae7b0cc2a98023de1d61185530061fba2a9b02a600a7985d036054c01c72a9a06c0a980b0f9d15498e520061eba2a931ca402c3e74551639480187ae8aa2c7290030fdd154586520161e3a2a8b0ca402c3e74551609480187ae8aa2c1290030fdd154d8d520052ec2e87b1aa400e1d54d0f63548051bf0ea1ec6a900b279d143d8d520070eaa287b1aa400a5d8510f63548015ad02186c6a9002b560430d8d520056bc0ac9b1aa400ad48159363548015b700b26c6a9002b620164d8d520070fb22a9b1aa400e1c6455363548015ad03306c6a9002b560660d8d521cd2f42ce9b1aa400a5d859d3635
  | 20 => 0x10960000002648000000000000000075b51310dcf7423e479824806600000000005346ce000187cd6c4cc1440000bea00023d00000000000000e6000035242514600000000c7864cbd89bf41880013f200052d9254ac6056000000000033d0b01aa50a261b1cd039828a06307c8a2800000000006b07e28fe06582b85d43b100017dcdac0000001c546fa88a0bf048400000034e09d0e061d20000000ab21c3000156c00088d0001c283740001bd0000be80004b208ccc3c63801f1abca6800051b0f2400000046602190d41791c116e8d32a020000e800009f14580ddc00021122e9cc000000000022a800000038d911c0006524df0c7855a205046a200be64910000f689523a200f1c90fe201a0ff0000dea0000248dc92e27ff0000a4469a5c61af163cf78a124ab800004600015521d8f8c0000000000d54a1c0cf0f1134246522c80013865ea00180000100100100680080000500380100080000680200001680080500100400000100000180000000180100180100680080700080100a80000680800880000000080200780f80c80001a80000980000000100200d00680180180080000180600180300000200800380280600500000000101d00180000100480f00100000000100000080080000d00400100101c80001000000100080080280001900000100000500180000a00080200f00100401380204080100100180400100100000000000280000080180100081500300180000180000380100100000900380380000301100780280100680100b00180000200480180080500500180000180180080581100080000000080200500000680780100480300000080080080480000000800000480000200080100a00300800100000700100080880080000081c00380000200d00280400580180080100700380180180000000000600080000680200480500180280800580600600280180100580580100580700000b81800500880200000300000480300000080280080000200000000000280080000000300000000080000600080380900600000000080001700280300000000180200600400000900380201100000080480380300400100480081380800100080000080080500400800401380280100001000100000a00000c00000200200000300000300280100480180400000400000000a80000080181080000000100080280200180200000200180100100080300000000080e00080e00480280180180480100080200680600180280080080000080400180300000080980080480180000180100080400100000300280200400100180780080380080000000080181480080080680080380000100000100980200000100100780c80000300100000000280000080a00380000800700000e00000b80380000000380900280200700200000480
  | 21 => 0x327b00004ba99c0000000d349fb00000004b461720c8000c84a404ef87203c253503080008608c400022d00003d42df18bd22a7bf3239dec000270000000099e66b00000000000004f01fc80008170758d8800000027800000000002b514e000079c00023092a493f000000088ca014bc8dd4b184330001c78c209fe0000001254a1847e8b80cbe0002a6964800000011c243c20063000019d4a6e00000023c40008332c5a76000047700028154b400000000010ce6be0000f9c0000c4000282cb700003568bec0002fa4e32175388a62098a0d800000000017c8a3e0001961ae800000021f136800052e00000001b80001290c04bb20202cb000134811700011e40001d400019800000005338000732000000000000000029f1de40004354a893786f819d5080cb51cc3d547b00000005200fa80000000e00d8a458a3465c4bb000000000019d1e9400026f00000006f0367000000063600009c260517a0002480b04b4a20b0000d9119e00043a80000001ff000000000000000000000003115060730d144e50000000cd45fa045063025a3c3215279854048725305080f6a3011581a04e200011b9954fe82ff43300a141e00052e2400e0e0000001dd40000000ca80593e893821600011722922aa9b5c3820584d3020800006551d02547c0586483973d14047300019b544848f0a5a2a4bd6a0e4d1968856a8442b811801161fb0f198fc4804d2492980c1d27cd3e79ab00005c54a81e007842680001a351ae05e294800123647e4ab02b41421632390ed400000000000010226fd488823cfb66eb50f93150c45ce1aa8000b5e4f31cb268121a6810000c311c48ec4d7888869c3c010226e0000697112803c4f24f422694193c87a636618f88080004b780bc43697e20f9b085d096e20a21511585ad34f800000000014e9200000000403039c6980ba325914cb62099348a47139879d00000000000003e19cd80003160001ed800098b000000008a5d318507700000003c880010029fd00000002b637e000000000074e33980000001f727e0cb80000002da96b000038900000011160001890000000646398a1e07f60000000808df8000123000062a0004b59c4816023b1689b7c000557000237c0004af10911b80ea2290000000c800002a08dec5fa00013695242448c600000000004d549f27dcb1a0f149e80e80000000001f5429a1752848fd0a160e50959f9c50444c1f7a438dde00000000b92f00854ac000000000023193005b2000000000000000000000000006b50ce0428e523df2890ee8e0a9dd4309db8a6687c08e8bcd42250d416a17066472a0298bdd2626f83c28c08c141c22c29a107ba0002e89a0d36829f00019652580cf1b6800000044336a9ad11f467d00000004aa5f800400000002be3fd12349da0003d78668000000000000
  | 22 => 0x540005e42d9180400000034f00000000a443ea0540000004341b814c20000002154d203ff00006c01fe7390000000f080000c39b28c0800010ba7e00001e650ba304238000075076ca4c4842b416e482a04d3db8000f2000000029e036400039a8d28dbc49f315846c00000000000011fe59d0002030ee297321ea6390c64b22270000da200000022b400074a45f1c44000a5600018e45de2f214097014ea7d307082ac024a7e0000f9000041335991d800001b12498a834e5721f0844804a1273ab00b03e02010368b70f8e6b727a800099c0445290c2146ea631b99078dcc9482038000cec0e2277090cf36a701d980012200000000cdc0002f90b314b46b62d7380160c00055405d9e3c00051906d08392a60844300bc11102150f4984c5da0c5154a4acbbe40900a8000824445021a758ae22cd000000000024b00006884903974cc958123026e47904549663b414aa72c5947705220a905be4cd18f95f4aa44c331304a8f102440230768a4e28651512d51a63461181e907640000de800066c0213b1a78c2d87733058e9cff6a2121191f4af28c819e20a4d9054e0000000df40002a41cb480a0001050764f660a81680f60d9e0001041cf80000000000000dfc528453912d428a2e0000000154a0d20d069800000013a80000009242738000e305dc000087ced84ac0a0a2cc3428593a48e514a80de32a07600003eb059931c3506622460ca8b4800000023ac000000000120c0000001a119340008f9000000089e0000000000b980004c5000077e1540000000a0e00002907ac00015e13321180007ae068a2c80000001f900011c80fe1ba000149e7584f793280006530000000000269000000012c39000016a124c2e515b988914c5f01859f710904220000000000a6e33c8c0c61c3bc06986d8b2009d11e85e832e62c1c912ec7362a14fd1398cfe0d200007254b063142d8d0c122a6a03789d946a6740fea3682ac2b90cd80000003db0c8162543a1e81d705481e09de0652674e668d0255a1300000000c50000c665aa2880490000561441095d2fe76739d27641d00001280bd897000000005a40127ab1f321c546200043790a048201800029f00000001838ff8c30a550000e105a800000000013305364529ac087e6e200000011ea00014293f89fe4a4457a1e466859b2ca9e48c005b718e0440000695049801901a0044d28d408742bb2a608b873a00036e19e800000044310089f09f307c134539415f00014ecba826546914746b400000022a118a57800000000004c617c1c581aa0000001eb1492a134f6a7b00005253f489c8e867c20da8cbd48a0002898000a36000262143924e1800fd0000f260003b9109028e26300013bc0005e300000000000003f5a7c86cc0000a800000000000001040a800900e88a0c73847500025a0bb611
  | 23 => 0x83ca1df0d8c7191b712140001b347080006e200024580002764c23ee80013521160000eec1c87d90000ad932e8ee08c27681909ee427a99848e6dd054848caee3c81cf8d0477c73c135a1f81de99e3d19d4c8d200032b251949455f4291cec8ac72f0a411c423e42130a20784b65b01e80908bac089337a17c0fa60f0fb032535675115820d010244006380a933e0341039e1908674d1e521ac76c09a2d3805c68e3195039bb4da696625f87a849c6a244e94a909c2bd29e0538dec4002f28f5cd2458202519a4c5070e107959917e0d82ea91fc3948450f881d03aa00000029dc6f21b7000295d1ac66713100000000000000f58cd87d228122513ae06c5158c98a5e00d0e327a93768a347380000003e2028203c5089020000d006b872e176117c00094230c9f505863cb3af9c202b0335255201cb3e5530f62084f8212534797a4bda83d16d87749c0214516000023c81639000150565e22d305006ca27e512854c170996539a8eca8e39553b043400039e1ef132cda08892431968d4a70901214f4a8689646500004468a228606106ba14f4fa826081c4ae04e0530000980491884000076a0002448000a411060000b7a00016228a08b600013b9e5cd8a88542c0ead49c5f905f0da8016431230a964d700100cf88347e02da237865911848213026548785ab33e20a14daa74157a3700a865e19826e80009d53c090190da5bc1dc1414fca33e3388e2d3184891d528cc1f80004e711900009693d08000d860943e60c3ce6e23537501391626ec02d05acf326bd00018748d6a32401937c0003594db0d247f47e8098138cd882cb17a8738afc5de1ac252d3a07be00000011741052191ea0c2c439200a09d07c5752cc007cfa2a6f5178dfce701140060190ecc92002580013848504ba122818c83a024013000051e00019451488980bc004c20c4a00000000e043bd38a1998d4807809a1f000000000001dd02dc0003d9186800000001f800000000043281741fa3e831d0ac52da13741b8ebccdc52200000010ae987000000027c0000b294448880000001c2c0004fd3af1e8004c000000223800037007b9b690285674db90946d62bf27d24c8000149538a66c92e29337827a419a4272ae17489627f70d4953c0e062031200000008fb0df9734ddc003189a3a02749932ac0b54a2c00041508690e00e320c2100b0e9392d49ea88e074c0fa0000f4e2dd159a8780004c10000bf0fe06e11530fb92be54619488700006a60211c053c22fe3030000e963cf03f8aad2106363d4a6c474891a25d00013924f205015ec6a228b31480013b849305a88fc9ba5142fe8aa08841bc41c8145470449326089c45029e1f487580004572a89c7c1108130000000c182cc0d78f147460000000d58000000319129c4067e200000000008d90f68000d2805936091
  | 24 => 0x620c8a5972a294c422235423c0944eba4962ab0b4825000045d80000000000000000e9e0000002244e8c86438985dd35c77f0398e30f0661c1150000ce49b24160650fa086e0001768ed20003d880000003ad4080e14ba084100013503de56200000005e218d3308e00c247590001400000297000000000098800025b00005b3000025c000000000202d15c1010001e31134494455879000059c01a8b9081a94338800011aa00011900000000000a2208c9ee66335d80dcdca6500000039226000000000000032500019ec574a4c2cc8f1861a00000019dc0f400000023800004920a880000004e220b86b8000a1600008989689db48587c927456c00019382ae438020a8a5076a4604f8000000000379242446808322098d40005d8000078910610400005ec3460000000b3c3c032801398340002b83d689f47f04b6215a25525a5fc3139a3000022400025c8d2c0000000230fd400011c9f240000000000f8c232955449800000000037b896400000000029440ae00000025d51e8381000148536a000000000000000030392741f60000000860dce000296036c000000061258c68800039380000007bb4ea0000022000402800000000022c05280008493b684bc000688000226cb1c0a214e0b1cb6c6483f09e2cec43911d80a60e0833b1600b241dc2202dda3a523c03953229a0b221be03c8740c7843b4a00f3021c87a2241de8172a083dc29c897c6b21d4971d31e20939a035c54a2a24348fdce84576079968c7da36311d0004d260001189ff8000000000000059c57a460152c5ac1b80000000b8200000014e842c00000000010040004f806ec10e81239f86ad17868e00006644bc00044f9cad42a38301c10812323f935c98b400094737897740004f10190c500001020be01dcaba0002c019611f00f61fa8ea00448260ad073cbde16745aa31c7f86023dc8e84000411465979c38a2530000e212a800000026e400049b00028e4d8000026c29fd4f44bc22904980003d208580012c47c444380c535860902380000000b60d689501780000370ab80001ee47502944587d61c3834038e6a709980009503c750c9c880009c8173a07c9a076404d80000005650b9864800000003380003021cd3f61a1c000000000193ce1e16f14ca66864436100000000005500000000a2a08e4f3928c25c6ff000188c00000000026500005c338d00b485c0000d2800000000000019940000550c880008bc00052828180000002721d5c6d881948a04d400000005f9c7400e00017484e4902000000114443a7b000000000000000000000b3400043b80010b416129c872c3ce000143990cd4246a3a003d0ede80809e93a493c368523a634d567d842b00000000000000000000000000000000010c3aa80004ce79e31a000095a0005219c183e672c2bf962116e1
  | 25 => 0x23605dc000000000000000043f82bc00062e07a8b8d36600000009900006d92c5000099281800019a00006b100021341da6211758000304000000000070c49913099e14460002be0c10b901aa3bb8e940fc9bc26d800000038e3aa294cbf695931ea4a419c9bd2a51d84f2c76039e94111a85443e412883ca6a33868a589304dc19385f459095b20416b8c9451c13991688a882534c1e1c28646d01d9b610bc8c30c5a74ccfc50f4808b4c8146f401e233467e21e50da4f0100a69027860d38e6861e700d8df697a4781ef425296a36a2570a022e6005297cf3e1fc15610a44f486c3f300000000003f1848000031a4e29ed40000a60002278e6405b13da705060a033719a249ac0002ba0a400005f600014c80000000000b08cba00049b006406097007920880006372ff85c01b23102280000efc7da1592270a146a03f6800060a6572b780002fe7e432094213f80000388000426a654bda4151ba02900012713129cd000018800000000000011bc3d12d0800016468000a000052828e0b2000143468b23a26a0b961c01e99dd8a462a349a8518bae12c3f980001a800000028b4f3495a0348b854bc89945c000000083202e01c947e88405ba41000018553c9b2400080e15a1e885bc72653d983907e1a02340000ff80002d01b9126847c49700006660001a580012c23b73a924c018600020d800000024d0001d4000047b29f800103a40c0849e2471410f3c695cc00038d38605c91ee1361f99f5c81e6d24718588d04782000280000000000000003f05640000fb141203d2cf214d124000147a40ceca6492f41f8128a7fd4af08f06de0a31032504b947f82470c8c0f89283e51d1c2ba8ed22e245d49a3090000000d5c8353940a30162000000074c93400012b00000007253fb13b11de16836580000003c103b1e28c1015500015acdd067021b1058a6013c3e297803be81c5400000000000000232400078e000000060c1d72a1181529a42f1179be53ca6db32d93a01d894e06626a80000000000000bfc11a0002788000a480001f7864009e0000000000922000292c000000258000000000000000000000000001c5c0000002250000efaa6b000209138071c4c200012ee4625211610c8835f5361a153ec34f08388641ba1f931288d8fbe7b413e119d2982c505e80000804fb40d93840563ea4e90000ab42d83ca8000e4200012520111ca4883cc09b126e0003320618000103000225c00024c192248520c5e6205a60cadc369180000086800002f85644b000000029801583934a505d0ff23b94f5a880b02a2706024292cea5d36384c932082f3ae06248cc91f2f88cac34834805a09706a628918ba744e4624528ba1c80d633134e8711288a344c3097d34e84725e8304eb40004d125752fa0003a09b344d44a12af17106727cb4f40
  | 26 => 0x59421328f14fa0000300e9897256d40d0a9c0000003f79af058c9b04479ba49f200043a281096e01d3bc28289a620009fa3453fe0004be264400006612780006ec00020e877879a42d40498ec00000000005a800087341c20f0de618e26c8000d503180000000a567ee41022051b60001a2a4cd0141b91ab9f3800094f30889fc0009600000b884420000000c753045b427580007584030000a6c00056947e28886c082e0000a00d7e0003a201a929276b34d935d39e5c915e03588d8000000107108400051f03e87b296506fa1ece8a0a7000000000092f0ae00009d45bf0b8a4752183210bb0fd800022d2c9a4ec51a0001ee00011420000001320a48615000000000000046717b8b840004c2800067016d1c786d0bc29ad0000000a064a51f29d2000019851ea0005e800200e00000003fd0001fd4ed08b644800004f0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x141d9419473c853000507650659ce214c00141d9419573885300050e650655c2214c00141d94197734853000507650651cd214c00103d9421975085300040f660655d0214c00141d94196730853000507650655cc214c00184c6561c320853000703195740c8214c00143994195700853001e0e9d984197304c00141f9755143d8f2001607e1d5450f63c800141d94194735952001607e1d5450f634800582f875514298d2001c0f261745516348181434915d15458d200050765075dcd634800121d942156318d2000513255631c9314800581c875514358f100160b21d5450962c4181a24815514258b10007035507350962c40c58c4811cd4258b1000561650531c931c4001d055450c724c71000551255301c931c400141c975514358d100160721d5450d6344001c0d5450c7258d100050b25d54509624400582c875514258910007035507350962440015c192a01739451000744551405ce51440011d19888173945100057064e201c931440015859414c724c51000570640531c931440015c19090c724c51000741551431c931440015c193a00724c51000478660501c931440015a194140724c5100057064c501c93144001d4053140724c5100057064e401c93144001d2154500724c51000551255301c931440019c072603324c5100054c650805d4214400155193201750851024d58648805d421440019318450175085100055864a305d421440015519388175085100064c615805d021440011b19814174085100056464c505d021440015a19214174085100056864a305d021440015919388174085100057064a805cc214400155095601730851000474660505cc214400159194141730851000570648505cc2144001d1154501730851000474662205cc214400183876610754c11027e541d58194d304400195075604324c1100054c65075dc5304409f9507560e514c110316321d8824c5304400194875209314c110006581d4824c5304409f95075e15314c110004f0249854c530441af55297dd5314c110007141db754c53044001711941d5314c110006b021b824c53044001d4075e09314c110006541d4824c53044001d4075209314c11000670a5c824c530440019c197209314c110316709d8824c530440c59c076209314c110006d0dd4824c530440019c275209314c110006701d4824c53044001b4075209314c110006501d4824c530440019c374209314c110006705d0824c53044001b4354209314c110006d0550824c530440c51d298dc9314c1100067020b724c530440032d296e0f214c110006541d783c85304400193075610214c110006541d58308530440019a184dc8214c1100067060f7208530440013c1980c8214c1106b7501d4320853044001b81840c8214c11027d54255734c520440019c1732093148110
  | 1 => 0x10048e650855c9600c401a195460f42580316068c20554509600c401a1954e0d425803100782551420c9600c4c56c0915083258031316b0e0c824c5600c40581f8755143d8f210160721d5450d638840583887551405822168e832195450b63485a360d921d154d8d2168e07a1d54d0b634840121d94a1770d8d2100634607709c3634840582f875514298d210068355182d0c634859fa0c865514218d210058364a74550634840181d875534218d2167e8520554508634840160d959514218d2167e83a0554508634859fa0c815514218d2100781553815086348401e05542054218d210068361542d0463484c528c985094118d2100487650855c06348401a0d5460b4018d2100623610631c9514840141d93dc975590210060b60975dcd6408581834815d573590210058364a74552630840181d875534298c2100487650855c26308581434915d15458c210058364a74551630840160f925d15458c216058524574551630840148d941d47258c2131531245741c96308401c0d745507258c210060761d54d09630840121d942157058c2100523650535d83208401c0d5450d760c821006836158359032084c56849160d640c821004a36605359032084012399421573580210068a55182d0d6008401a195460f42580216050d2457455162cc00148d94194724c73000703591541c931cc00182f7460a64d95300040fe6174193654c00103f985d074d95300060bdd182d0f654c00181f7460f42d953000607dd183107654c00182f7460841d95300060edd180107654c00141e96a0d741953000507259835d0654c0015189060d741953000507a58305d0654c001515910c174195300050ea58305d0654c001531910c174195300060b5d282990654c00182d7460a641953000607e0d74590654c00183974e01641953000607a197490c654c00181c865d143195300160be1d5450b624c00103d989d065989300040f65287d95624c00181f736106558930196071cd84194624c00181e76610658c930006469c184196324c00160d94194628c93000507650655c6324c00141d94195710c930006075cd84196614c00103d981d065585300040fa6065dd1614c00142d9419772585300050b650651c9614c05781e73610651853047e0e9c184194614c00141d9419672cc5300050e650655c2314c00142d94197724c5300050b650651c9314c00181c76610654c5300058365065dc9314c00141d94194724c53000583650651c9314c00144c95618724c53000523650651c9314c00150d94194724c53000703a50651c9314c00144d94194724c53000703650651c9314c00140d94194724c53000513255641c9314c00144c96d50724c53000513259541c9314c001c0d64550724c53000712196101c9314c00161594197614c5300050765065dcf214c
  | 2 => 0xf4761d0b91044c3cd21188290f47c3c893314a02a4133304535d0700116000892b8d92783c0485c1b86f2e0960012e084110784e42c7e001231610e00015354ad2a07a034f13a0ba49cbc34c4338cee410a527cc6248523f90003c040003f210d025d290e43e124b03a4af000003d400000e2108401d4562504d01911228f82441b0d8ed014223846d00000000280dd1833c003c12532830184b30ec002f52a440a60d400378d223cc100033000c80000002464000000c400000000005a368dd240003012c22067090b736c6837c65254ab05078230fc22cd418c001ec0026c6a291153ec3a0b034000002d4d83b086480000b4f90004b000be21477151282c8dc47838271050000b080e43d0d616400154ac000cd4b47107109118aa128170592419802428002fd2f00000010480002008200000008040a0108014020c0000c0c130500402010e8584804050040a0a0f8200c00018301602010080207000406e0403874200b0281400020004050020707c040400818100501844001e0004434030183c0a05000040200030101a20000003200010080a050400820011cd8364874553635487381e8755342d8d5200607a1d541076354801a0d5460841d8d5200686551801076354801a0d5460b4318d526a58364a74550635480181d875534218d520060761d541046354801a0d546084118d5200686551801046354801a255460841d85520068c551801076154801a155460c41d85320068955182107614c801a315460041d85323143325d8214d610c99f81c87551435843267e0b21d54509610c801a0d5460b4398e510058364a74552639440181d875534298e510068355182d0d639440160d929d15458e510060761d54d096394401a295460b43582510068655183d09609440582c875514258a310160e21d54501608c5a7a0c8655143d893169d8364c74553624c5a782e8755343d8931006835538250c624c401a0d5460f421893167e832195450c624c5a164691e0f54189310058364e74550624c401a0d84d53531893100683a158414c624c401a0e956105318931006839d58414c624c401a0d756105318931006836135414c624c40182d875534318931004932558090c624c59fa24815514318931314b1a468550c624c401a0f985514318931006832615450c624c401a0f87551431893167e83a055450c624c59fa0c815514318931007815538150c624c401e05542054318931005b06408150c624c401a0d54e01431893100493255839c0624c40160d9414e50189310061361c53140624c40160d9414c50189310068361053140624c401a0d5460f40189310049325583900624c401c0d5450a76cc931005236507518b324c401c0d7455062cc931316311c686dc9324c40148d941d4624c931007035d154189324c401a295460b435803
  | 3 => 0x411b000c200000420032651a47c8d2750c21d1913c6c0288e17832000f628c5d3a8c70a800448000007944c000002f000230002b2840039c0049800098001108316c73000d1450193806b1f522408fa45c510041a17cc4140b609cff11c72474483dceb0386029d03000c92ecc31fcb1208001c0ce00025000532d0180000015ce6000e51a4070212b2610607d0f32c9a43481288ef4041d0b91c2000c3
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x15000000e4cb808500000004e0000000011ac000129136640001e0cd0c00b402216840292e1c4923e2002a0000000485800000100000000002000068000509ab14803103000000007141e3a0010285000c080020c002062c133ea06a1e615450c624c401b00aa32040a8631262008836909560e701893100601b0eca0a6280c498b3f60091551420c9600c59f60250ae8aa0e4b1842cfc812458560d640c821004a234248306ba0ca98002911a19c184196324c001206d212ac30e498a6000b0269065840724c53000501b4832b0e190429800240da9195740c8214c001206d212ab18e498a40cfe01205541cd4258b10004a0b484aa603926388002540a5642431c931440012a052b27400e498a2000c5066053140724c510005a0348298a039262880035019414c501c931440012a052b27200e498a2000941690954c0724c510004a23484ab00b984288002911a41d5810c93044001484d20ea412629822000a4869075209314c110005a03483af0498a6088002911a41d4824c53044001680d20ea412629822000a5029597209314c110005303483a90498a6088002b01a41d4824c53044001c81520ea412629822000a5069075209314c110007203483a90498a6088002901a41d4824c530440014a052ae8412629822000a5029f54209314c1100052814eaa10498a608800390174550824c53044001488d20ebc1e42982200084c6a475610214c110005223483ab0610a608800314075660320853044001c803ab08190429822000a50295732093148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x400008602a00004501b429593a00724c5100061019869053140724c510004901b429597209314c110005101b41d5980c8214c110004901ba1d5840c8214c110004901b4295732093148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x138d
  | 8 => 0x138e
  | 9 => 0x98d
  | 10 => 0x98e
  | 11 => 0x3
  | 12 => 0x150d
  | 13 => 0x150e
  | 14 => 0x9cd
  | 15 => 0x9ce
  | 16 => 0x4
  | 17 => 0x168d
  | 18 => 0x168e
  | 19 => 0xa4d
  | 20 => 0x209
  | 21 => 0x20d
  | 22 => 0x20e
  | 23 => 0x154d
  | 24 => 0xb09
  | 25 => 0xb0d
  | 26 => 0xb0e
  | 27 => 0x1409
  | 28 => 0x140d
  | 29 => 0x140e
  | 30 => 0x1549
  | 31 => 0x154e
  | 32 => 0x249
  | 33 => 0x24d
  | 34 => 0x24e
  | 35 => 0x16cd
  | 36 => 0xb49
  | 37 => 0xb4d
  | 38 => 0xb4e
  | 39 => 0x1449
  | 40 => 0x144d
  | 41 => 0x144e
  | 42 => 0x16c9
  | 43 => 0x16ce
  | 44 => 0xbc9
  | 45 => 0xbcd
  | 46 => 0x14c9
  | 47 => 0x14cd
  | 48 => 0x3c9
  | 49 => 0x3cd
  | 50 => 0x3ce
  | 51 => 0x15cd
  | 52 => 0x170d
  | 53 => 0xcc9
  | 54 => 0xccd
  | 55 => 0xcce
  | 56 => 0x15c9
  | 57 => 0x15ce
  | 58 => 0x1709
  | 59 => 0x170e
  | 60 => 0xd49
  | 61 => 0xd4d
  | 62 => 0x1649
  | 63 => 0x164d
  | 64 => 0xec9
  | 65 => 0xecd
  | 66 => 0x17c9
  | 67 => 0x17cd
  | 68 => 0x98955
  | 69 => 0x94995
  | 70 => 0x9c955
  | 71 => 0x949d5
  | 72 => 0x20955
  | 73 => 0x20956
  | 74 => 0x94215
  | 75 => 0x154955
  | 76 => 0x154956
  | 77 => 0x95555
  | 78 => 0xb4955
  | 79 => 0xb4956
  | 80 => 0x94b55
  | 81 => 0x144955
  | 82 => 0x144956
  | 83 => 0x95455
  | 84 => 0xbc955
  | 85 => 0x94bd5
  | 86 => 0x14c955
  | 87 => 0x954d5
  | 88 => 0x2c9
  | 89 => 0x19c9
  | 90 => 0x155395
  | 91 => 0x139555
  | 92 => 0xb5395
  | 93 => 0xb5396
  | 94 => 0x138b55
  | 95 => 0xbd395
  | 96 => 0x138bd5
  | 97 => 0x4e
  | 98 => 0x3ca
  | 99 => 0x15ca
  | 100 => 0x170a
  | 101 => 0x150995
  | 102 => 0xd4995
  | 103 => 0x98d55
  | 104 => 0x164995
  | 105 => 0x99655
  | 106 => 0x128e
  | 107 => 0x449
  | 108 => 0x1a09
  | 109 => 0xd5515
  | 110 => 0x150d55
  | 111 => 0x8e
  | 112 => 0x165515
  | 113 => 0x151655
  | 114 => 0x1689d5
  | 115 => 0xb49d5
  | 116 => 0x9cb55
  | 117 => 0x16c9d5
  | 118 => 0x9d6d5
  | 119 => 0x3c9d5
  | 120 => 0x9c3d5
  | 121 => 0x15c9d5
  | 122 => 0x9d5d5
  | 123 => 0xec9d5
  | 124 => 0x9ced5
  | 125 => 0x17c9d5
  | 126 => 0x9d7d5
  | 127 => 0x12ce
  | 128 => 0x5c9
  | 129 => 0x1a49
  | 130 => 0xb5695
  | 131 => 0x168b55
  | 132 => 0x16d695
  | 133 => 0x1696d5
  | 134 => 0x3d695
  | 135 => 0x1683d5
  | 136 => 0x15d695
  | 137 => 0x1695d5
  | 138 => 0xed695
  | 139 => 0x168ed5
  | 140 => 0xce
  | 141 => 0x17d695
  | 142 => 0x1697d5
  | 143 => 0x124e
  | 144 => 0xb0215
  | 145 => 0x3c215
  | 146 => 0x3c216
  | 147 => 0x170215
  | 148 => 0x154b15
  | 149 => 0x155415
  | 150 => 0x3d415
  | 151 => 0x3d416
  | 152 => 0x171415
  | 153 => 0xb4255
  | 154 => 0x3c255
  | 155 => 0xcd6d5
  | 156 => 0x15c255
  | 157 => 0x16cb55
  | 158 => 0x16cb56
  | 159 => 0xb5715
  | 160 => 0xccb55
  | 161 => 0xb4cd5
  | 162 => 0x170b55
  | 163 => 0x16d455
  | 164 => 0x3d455
  | 165 => 0x15d455
  | 166 => 0x16ccd5
  | 167 => 0x1716d5
  | 168 => 0x16d715
  | 169 => 0xd4bd5
  | 170 => 0xbcd55
  | 171 => 0xcc3d5
  | 172 => 0x3ccd5
  | 173 => 0x15c3d5
  | 174 => 0x15c3d6
  | 175 => 0x3d5d5
  | 176 => 0x1703d5
  | 177 => 0x3d715
  | 178 => 0x15ccd5
  | 179 => 0x170cd5
  | 180 => 0x1715d5
  | 181 => 0x15d715
  | 182 => 0x164d55
  | 183 => 0xd5655
  | 184 => 0x17ced5
  | 185 => 0xed7d5
  | 186 => 0xb49c95d
  | 187 => 0xb4949dd
  | 188 => 0x9c94b5d
  | 189 => 0x16c956
  | 190 => 0x3c956
  | 191 => 0x15c956
  | 192 => 0x104a
  | 193 => 0x1a8a
  | 194 => 0x1049
  | 195 => 0x1a89
  | 196 => 0x19d4d1
  | 197 => 0x5cb51
  | 198 => 0x5d5d1
  | 199 => 0x5c591
  | 200 => 0x5d8d1
  | 201 => 0x1a57d1
  | 202 => 0x124956
  | 203 => 0x5d7d1
  | 204 => 0x216d5
  | 205 => 0x21715
  | 206 => 0x219d5
  | 207 => 0x1043d2
  | 208 => 0x1a83d2
  | 209 => 0x1055d2
  | 210 => 0xb56d6
  | 211 => 0x105712
  | 212 => 0x3cd16
  | 213 => 0x3d5d6
  | 214 => 0x3c2095e
  | 215 => 0xb45d1
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2193
  | 6 => 5908
  | 5 => 2689
  | 4 => 304
  | 3 => 47
  | 2 => 6
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (89913+((h/731+packedAt gbK7 (81141+(h % 731)*12) 12) % 2895)*13) 13
  | 6 => packedAt gbK6 (311150+((h/1969+packedAt gbK6 (283584+(h % 1969)*14) 14) % 8578)*14) 14
  | 5 => packedAt gbK5 (169403+((h/896+packedAt gbK5 (158651+(h % 896)*12) 12) % 3549)*13) 13
  | 4 => packedAt gbK4 (22189+((h/101+packedAt gbK4 (21280+(h % 101)*9) 9) % 365)*10) 10
  | 3 => packedAt gbK3 (3912+((h/15+packedAt gbK3 (3807+(h % 15)*7) 7) % 89)*7) 7
  | 2 => packedAt gbK2 (560+((h/2+packedAt gbK2 (552+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fffc3e0f07f87f80fff0ff001488cfc4dce7c
  | 1 => 0x87807c00ff83f87ff01ff0fff2b0f33072738f
  | 2 => 0xf8007fff0003ff80001ffffffcc703c38383ff
  | 3 => 0x7ffffffc0000001fff000f07fc03fc03f0
  | 4 => 0x7fffffffffffffe000000ff80003fffc00
  | 5 => 0xffff800000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa874060321580a821c789906000845444c63c
  | 1 => 0x8309440052908832604998a4a010b130505285
  | 2 => 0x501219a9000355008292224b44c302c183815a
  | 3 => 0x2246ed2eb580021451ccc818b05dc02fc03e0
  | 4 => 0x4040331c8c6266458e0000020fe800032b2800
  | 5 => 0x64780018084044060800000c0ffe6ba8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36336
namespace PEqualNP.Outside.L_meta_36336
open PEqualNP.Outside.L_meta_36336.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 6 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 90 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 11 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 10 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 414 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 616 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 bs4_5_512) (concat bs4_5_544 (concat bs4_5_576 bs4_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 6 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 47 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_288 : Interval gbAtlas 4 288 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 304 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288))))
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
theorem bgb_5_2688 : Interval gbAtlas 5 2688 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2689 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)))) (concat (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))))))
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
theorem bgb_6_5888 : Interval gbAtlas 6 5888 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5908 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864))) (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))) (concat (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248))) (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))))) (concat (concat (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))) (concat (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)))) (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))))) (concat (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)))) (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))))))) (concat (concat (concat (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072))) (concat (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)))) (concat (concat (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456))) (concat (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))))) (concat (concat (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808))) (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000)))) (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))) (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384)))))) (concat (concat (concat (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736)))) (concat (concat (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120))))) (concat (concat (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312))) (concat (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)) (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504)))) (concat (concat (concat bgb_6_5536 (concat bgb_6_5568 bgb_6_5600)) (concat bgb_6_5632 (concat bgb_6_5664 bgb_6_5696))) (concat (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792)) (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888))))))))
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
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2193 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)))) (concat (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016)) (concat (concat bgb_7_2048 bgb_7_2080) (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 34, 42),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0feeefeeafeeee0c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36336.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.and,[3,6]⟩,⟨.or,[0,7]⟩,⟨.and,[5,8]⟩,⟨.and,[4,8]⟩,⟨.or,[2,4]⟩,⟨.and,[0,3]⟩,⟨.or,[1,12]⟩,⟨.and,[11,13]⟩,⟨.or,[9,10]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36336

open PEqualNP.Outside.L_meta_36336 in
theorem PEqualNP.Outside.L_meta_36336 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277067968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
