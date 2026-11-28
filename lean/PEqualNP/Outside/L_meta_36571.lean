import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36571.Model
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


end PEqualNP.Outside.L_meta_36571.Model

namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36571

namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xcd5306501029008003a1610807be43bc43be42bc42bf41bd41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3800221800414610004b94a438f29c851c5350658a4a0ce14141e418041b040043a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s0K3 (255+((h/3+packedAt s0K3 (243+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 3 => 0xff83fffff803ffff807fffff01fff807ffc7c7
  | 4 => 0xffc1ffffffc01ffff807ffffe03fff807f8f8
  | 5 => 0xf0001ffffffffe0000007ffffffc000007ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x21108259092492588909168b162c5b4b49db5b
  | 2 => 0x422104af424924a952522b40ab56ad95942dad
  | 3 => 0x847609325762393247644dd5819b30c6e6c6c6
  | 4 => 0xe843b1c46473b1c4644771e6cd03c6e0c770f0
  | 5 => 0xf7bde078783c1f878787e78f1e2070707bf00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36571
namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
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
  | 2 => 0x3f80ff03f81fffffe07c1f07c0fc1ffff4923f
  | 3 => 0x3fff0003ffe03f81ff801ff800ffe0f818e3cc
  | 4 => 0xc0000003ffffc001ffffe00000ffff001f03f0
  | 5 => 0xfffffffc00000001ffffffffff0000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80840a000800810001842108461421094124d5
  | 2 => 0x1552946594d52a68f059164688a91ad694922a
  | 3 => 0xa64aa6aaa553b42b76c21bd212cf48e0d8e34c
  | 4 => 0x346cd8d3469a274dbb6f508424f39c431f03b0
  | 5 => 0x3870e0e3871c3871dc739ce7388210841ed800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36571
namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1000042400a1117344878a2a44c8d2818613000150b1c588000eac1a04614f8000780210074002380160052012a71200c044c6c0060017474840000005c205eff43fe43fd43fc43ff42fe42fd42fc42ff32ef32fe32de32fd32fc32dc32ec32cc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xb005341b890190d8005e00000c4005531000ba723693cbe071698c0054130001a00328000022000043e0000190b6002193800001a000003e0c00018002c940003700000ce230b000c000359f00000288381214001fc041c3984c4240001e8000000000747b360c8204438000764200000005a2691cbc741602822273b9042a5c378b824453e8ac0008000e470463b1d4fc3c1f810e24a308d45424260183a292b0f40680348a0401a2b9a8664b00078a6523c05cf23607800162500124cc3000030006018006828096818f0f8080000183000304088406008200218683800102830180808002048880005b94b43b6a96877651d0eeaa3a1dbd4943b6292875e53d0abaa7a15d94742baa8e855f5350ab8a6a15b94a32af294654e528cb9a64195794832e729065cf420cb9c84197350832e6210656e530cb9ca61973d0c32e721865cd430cb98861973d5032e72a065cd540cb98a81973d4432e728865cd510cb98a21973d4032e728065cd500cb98a0195794f41aea9e836e52d06daa5a0f30cb41af29c835d53906dca520db54a41e619483cc32507986420ed50441e6196633e548c67aa918db94a31b6a9463cc328c6dea498db14931e619263cc320c7986590cf952219eaa4435e53886baa710f30ca21afa9a435c53487986490f30c821e619681cc32902bea6a05714d40b7a92816c525039864a05dd4540ba28a815e53102baa6205b94840b6a9081cc32102eca2205d54440e6196616e528c2daa518730ca309faa2613c544c2dea4985b14930e61926177514c2e8a298730c830e6196415e53882baa710730ca209faa2413c54482bea6905714d20e6192417751482e8a290730c820e619621cc328427ea8884f15110afa9a215c53442dea4885b14910e6192213e540427aa8085794c10aea98216e52042daa408730c810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x60e001810800b91870317801a090888200b17169d1b018c9e8d00001615068000000002801b8d8793001e09998a801f958a100118991a850c0f821ca111139484140e8f1f209c04839d9221928580008001080260c0b0c3c0020a0011b14104040080001b1987420cac561d0832b1987430cac561d0c32b1987540cac561d5032b1986540cac56195032c3550540ca8e64d4432a3593510ca8e6494432a3592510cb455114432a3d91500ca8c6454032b1d85500cac46154032a3990500ca8d6414032b1984500cac561140329318953d064c6354b4193d9432d064d650cb4193189539064c6354a4193d94329064d650ca41e10c9411070e540ca31c3550328c70e540ca21c3550328864e62d4d409398f525024e650c94093194325034432d4540d10c8515024c6254c409318d521024f650c8409359432103443294440d10c9511030f540c930c3150324c34432d4530d10c8514c24c6214d20c3d50324830c540c920d10cb514834432145209398b534424e63d491093994324424c650c910c3d50324430c540c91093189530424c635481093d94320424d650c810c3950320430d540c810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (810+((h/15+packedAt s2K5 (720+(h % 15)*6) 6) % 60)*7) 7
  | 4 => packedAt s2K4 (3827+((h/43+packedAt s2K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s2K3 (2738+((h/22+packedAt s2K3 (2584+(h % 22)*7) 7) % 82)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 1 => 0x3f81fc0fe0fffffff0783c1f03e0fffff4923f
  | 3 => 0x3ffe000fff03f03fff803fe003ff07c0f8e3cc
  | 4 => 0xc000000ffffc003fffffc00003fff800ff03f0
  | 5 => 0xfffffff00000003ffffffffffc000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80882800200820000188442118a1084a0124d5
  | 1 => 0x1524519646514d1cb032191a2148d6b474922a
  | 3 => 0xa6149aaa8a3a856d56842f484a7a4706b8e34c
  | 4 => 0x3459634d14a0e9b66b5e8210939ce218df03b0
  | 5 => 0x3861838e18c30e3b8c67339ce0108420eed800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36571
namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x911d00518030008502c200b8bf42bd42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20048000c000067024a0004000a6aa3a15594632c6a10652d52d069ca518e55043196a9081355110298a4985514530
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (285+((h/3+packedAt s3K3 (270+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 1 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 2 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 4 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 1 => 0x48a65910ca5138658321a3445642a85a694652
  | 2 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 4 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaaaaae8e8a8a8eaeaaaaae8e8a8a8eaeaaaaae8e8a8a8eaeaaaaae8e8a8a8eaeaaaaae8e8a8a8eaeaaaaae8e8a8a8eaeaaaaae8e8a8a8eaeaaaaae8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36571
namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x10020480033954642c83010bf42bd42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x301d00018a0011211040a6aa3a15594632c6a10652d52d069ca518e55043196a9081355110298a4985514530
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s4K3 (282+((h/3+packedAt s4K3 (270+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 1 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 2 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 3 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 1 => 0x48a65910ca5138658321a3445642a85a694652
  | 2 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 3 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeaaaeaaae8a8e8a8eaaaeaaae8a8e8a8eaaaeaaae8a8e8a8eaaaeaaae8a8e8a8eaaaeaaae8a8e8a8eaaaeaaae8a8e8a8eaaaeaaae8a8e8a8eaaaeaaae8a8e8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36571
namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x14918000006dc000000003444304903e50c9a0002620014c8972b00000003b2f200060a250ea0e4001ec1a01cc8b8590006e9438cb000488cc93e4dc9d4001970007948a9d91e07d1440880000000018d2a07e400000052000d21f501230c2f00c24e81c8d18b0000012400047695c00209000000908f41409b13c9df3fc8b40021b4702a14a0003ac0f40a9f71760007e00014c3fcee06736c6a48380000034d100000003b4001420009dc00000000505458000000009e83e508480000000000000000000000000182000170b110f00052c00000000000948002e8000cda5a2b8078f20e01663cc01000518159388000388084a1060cc5790197b0003e4118000000000014f1f60000000023c0000014e4f4100000003b6000000001d00002c0e60a8000000003987cc001b00624dc1aa833825a87480037a6a02910d09415c8a02613c3e8a2a6b3586a8a30f830c444a02220007544b10a32c760ca0000000005f82f08e8f14107b3727f45d24248c5f14514d0ee8c44080018a240cc000344000000000008608f93f00028c79000132050bd0a4000990000004284ac001e700054cf5a494d40000017d00005c000004c4000d68002aa8480000000000000172000000858001fa000001134e8000c38762580003c02c034090ef0000000000010c0008043480033a1b1068003a296400105000000301a648a000c22300661f032a5328e2e527820000678259931ac56d4091641e564580001040012a0001d69542f802000000100c00c010040001401004060040300c020200100c000001700819004060100500c0200404060020000500c0500017028000001100c000100c000040000100008000060000001c0801c0203007018000181e02c040100104406038010000c014000000500400008020040100405038010000404c00014010080001c0300c0000000008000380000000004060080d0000000c010000100002020010000201c06000000180000410014040080100002010020000504800008000140401c010180900c0705406010000000102c000540000400004010040002001010010040600000000020000303400000010001701000000050080400008004010000400c01004020080300001000050040c0300302403016fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x14b8620007c8a49f0152000559b24540000013811c000eea3e0002303c800378000e68ac44e36947800136000001f800042413a3a0d60006f0bc1ca0fc0b0e313885cf48122dc5ac7f23f1620006c0cf25e854998000005b04d21306e0a11790316a2a8c723d0ba0e80819100e2005ea893dc59d3420025c3208e267380000ed02e530838ca8002041a94900000003ce4000000000b68000000007882a0000004a8000006f9309d331e9441e09824a000b421100098c0d9d011a3a84f8194a0970000003ae3240014c2ac000000e136672d0f000000000e7000000000002050000006a27f3620012f80019c000000004088ac9da470000106028632014d20000526520368001dc590001760f48dcb88001c49ece916f1d8859221bf14e16d3e1920000000c0000c815505800006000e78004ec330569a02e00000016909c354089572546d0c01182081c44e97e2028685700038a000000003120008d8004e60010c9ab0000000021c2ca2840024a2604e8001080007fc190be0006290ea902720006380000072859000000001470000001301c1af0000002286326423c000000007a0000000000007b0000000008ea290de70c000002a8580108061de370221e309a548739b506c7bc0024333e7881a0a544288c18000370000000004b67e87a8001ee001349fb2f0288449443f896021a7d410000b30003e200140256000374b1800248001380004981040000030a1b93f0c22249780015d1260949a8134142442802d2e60003f232200890fb1ed0008d80005a0007180000018c1f4f312d0008b8420b4000568d713c000108340cd0006205b8002c2001488d94de36ca500a3060005c18152c8d09b1ea346671198003767800684f24c8189400010e998000514da5dc30800194228000004f00000000051a9480015100072542872318000880000001202317500000000000000710bf8921880000091938e22d0f88346a69c001e134a8a12087f4ba00015a260001d01124e016439060001ae7091ca10496a54d0a4d01c0213007010a349390df15e7500001d00000000000000001160000006687215f0000005b0004ca0
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0x2000bf0734282d0e68e516e4982386d0b24e4fb1c72162000012a036698b912b000548342231a409c7e0003c86b40c8d32506a07680018a264821e62a2000ff83020023c6504b3b8000770e62bc7e4c7a1b2802fc3b1aa3563c8e920816664cf39851b06302b8694008785809f3b43b0e20082ca72d068a93727f8261b330e0e8009a322432000000000000da8002440e4ac800382000001012ba00000000000188168ea1787180005417c0c5081d62d631c001763dc138720001f04c0680002620f80e16a34052086041000088108120bc7389b8c60fe02cc194d0c26f0b48102a0004020041700c0a0041a0301404c000100500007000000100407402004040000000802000010043500c0306800004000141a00c3408800000100041e00810008080180000411018010040000400000040180100001054100901d01416000020740000c01004310000300400004000000001c070180102802030000280e004060000f05802068000600a0000207400000020000e01c03000020040207c0401008004020080203c000000704404008360080100c0701826028010640c058030040503801018090a40105412008020681b01806014050200000804034000040100408018020069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0xd5322000b89f51386ece2826294434901020001ec9c0ab3e4000408c320c5547098e28e0a8280891ac231131e328a580cb2051501bc328783ca6b90594b2ea77c848e31248281a90e42c5051087a0882d8e9800000570db05c1344509a8000001ac82800000119031ef12c000128001082810b9d11ea324cc0002e80acc80cf0006e800036000128b19682dc380498002fe584178a23d81984b8bb3ba001120a50006907c8060ee19c5a8000004bc4395a0005f4df1f000070c0b21a000000c30340006c83206018457c621ea17a4610c1491e637ce78af3444ccf0800312000001953427800020e000000000630841d4001f330032c2184810c48c000113b2000c40001467b40002c11a000fb9621b43fc148240007ec418ae33835c0a071008124a99432582c80010a2e03d8000002ac7ac569544320000000044a6fc0014c0000008c800000000198900004540000031600000000000479018003f4238f404d0e03f45091723e8707390f1b6508000822f60f0b6000000000000e8046000758d926404ca31111107504a1b70d481ccc8983925380001e05c00039003182114001f84022147783d0123442a8b83aa848278741ee3349f98424e1f00013402a298ca00004066cec0002b64211111c0300307d00f00e1b0bc125116788b783b0001002d9771740fd0480014e1f50aa1d064844450d4000468e120f154000000f01980a0671443ae068e62022b0720488f127a6bc4a8e903a3005200039465c0698d252278d897a0f207c9d1d03f80000287e0b0778c120c43e0dc3713637059c920dd2f22c40b99f1fc44c5c8522426f51005125c6a4cf0003e8168b98f42366280013b0a60008380e33a4f80016d334008ed8e23d24409e00013a26c000004086d06e14f3586c0c09fd01440cab8000005909680007084cb305f23a700c91a734a1746f0ac2f84582b0fb3e
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x38090c18479499c01002889a6085800802a0000000480099a01281431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20202+((h/222+packedAt s5K5 (17982+(h % 222)*10) 10) % 968)*11) 11
  | 4 => packedAt s5K4 (22768+((h/183+packedAt s5K4 (20938+(h % 183)*10) 10) % 662)*11) 11
  | 3 => packedAt s5K3 (1064+((h/7+packedAt s5K3 (1029+(h % 7)*5) 5) % 30)*6) 6
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 2 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 4 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 2 => 0x429291090d2206554084ca8265412a0a858b18
  | 3 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 4 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8eae8e8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36571
namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x484e6ba459448c434000560001680a52003b944990060001002e41ed878bc6538d50c5080b8a3444e073faa18b2a98205590081d000000e369c014292678aa656f8e051a0000e0000003420010b0600a81000005ff53017f94c05fd53017f14c01fe43007f50c01fc43017fd48057f5200ff94805fd52005f54803fc52007fcc803fe32007f4c803fc32017fd4405fe51017f54405fc51007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc21017fd4005fe50017f54005fc50007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x9c2000ff90e10007fa8708003fc4384007ffb142003bfd8a1001ffcc508006fe6284007feb142000bf58a1001ff8c50800efc6284017ffa94200bdfd4a10057fca50802ffd5284001bea94200aff14a10007fe650802bfe3284001fe994200aff0ca1004dfac30802fff5184017ff28c200bff5461005ff8a308003ff3184001ff18c2000ff4c610007f8630802bff2184001ff10c2000ff48610057f8430800efe6084007ffa842003ff9421001ffaa10800ffc5084007ff9842003ff8c21001ffa610800ffc3084007ff9042003ff8821001ffa410800ffc2084007ff8842003fdc4210007f62108027ff65440137fb2a2000dfd9510004feca88027fe65440057f32a2009ff5951004dfaca88027fc65440057e32a2009df19510014f8ca88003ff63440017fb1a2000f7d8d10005bec688003fe634400f7f31a2000ff58d10005fac688003fc634400f7e31a2000f718d10005b8c688027ff5344013ff29a2009ff54d1004ff8a688003fe4344001fea1a2000ff10d10007fec488002ff6244001f7b122000bbd8910047fcc488006fe6244001feb122000bf58910047f8c488006fc6244001f63122001bb1891004ffea4880277f5244011ff2922009ff54910006faa488023fc5244001ff9922008ff8c910007fa6488023fc3244013ffa8a2009ff9451004feca288027fd5144013faa8a2009ff14510007fe6288003fe3144001fe98a2000ff0c510047fe4288003fe2144001fb10a2000ff48510007ea4288023fc2144013ffa822003ff9411004ffaa08800ffc5044001ff9822003ff8c110007fa608800ffc3044011ff9022003ff88110007fa408800ffc2044001ff8822000fec411001ffc208800ff61044007ffb282003bfd941001ffcca0800afe6504007bf32820029f9941001ffaca08016fd6504007beb2820009f5941001ff8ca0800efc6504007ffb182003bfd8c1001ffcc60801efe6304007ef3182000b798c1001ffac608002fd6304007eeb182000b758c1001ff8c60800efc630400bffa982005ff94c1002ffaa608017fc5304001ff2182000ff50c10007f8860800fff62040077fb102003ff9881000dfcc40800fee6204003773102003ff58810005fac40800fed620400176b102003ff1881001df8c408017ff520400bbfa902004ff9481002ffaa4080037d5204009fe2902000ffcc810027fc6408003fd3204009fe1902006bf9841002ffea208017fe510400bfea882005ff14410007fe6208003fe3104001fe9882000ff0c410027fe4208003fe2104001fe9082004ff0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0xfff63880077fb1c4003ff98e2003dfcc71000ffd63880017eb1c4003ff18e2001df8c71003bff538801dff29c400eff54e20077f8a710003fe4388001fea1c4000ff10e2000dfac510007ff5288003bfa944001ff94a2000ffaa5100077d5288003fe2944001ffcca2000ffc6510007fd3288003fe1944003ffd862001ffcc310002fe6188007feb0c4000bf5862001ff8c31003bff518801dff28c400eff54620077f8a310003ff3188001ff18c4000ff4c620007f86310007ff2188003ff10c4000fb8862000ffa4310007fc2188003f610c4003bf9822001ffea11000ffe5088007fea844003ff1422001ffe611000ffe3088007fe9844003ff0c22001ffe411000fef2088003fd9044003ff0822001ff04110037ff654801b7fb2a400dff99520015fcca90037fd654801b7eb2a400dff19520015f8ca90003ff63480017fb1a4000ff98d2003dfcc690003fd63480017eb1a4000ff18d2003df8c690037ff534801bff29a400dff54d2006ff8a690003fe4348001fea1a4000ff10d2001dfec490007ff5248003bfa924001ff9492000fdca490007fd5248003bea92400dfb54920006daa490007fc5248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf1852006ffea290037fe514801bfea8a400dff14520007fe6290003fe3148001fe98a4000ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb02400dffd412001ffca090037fd5048007fe2824000ffcc12001ffc6090003fd3048007fe1824001ffc812000ff6409000ffe2048007f71024003ff0812001fd84090007f8204800dffb2e2006bfd9710037fccb8800afe65c400dfeb2e2006bf59710037f8cb8800afc65c4001ffb1e2000bfd8f10007fcc78801efe63c4001feb1e2000bf58f10007f8c78801efc63c400dffa9e2006ff94f10037faa78801bfc53c4001ff21e2000ff50f10007f88788003ff62c40017fb16200cff98b1000dfcc588003fd62c40017eb16200cff18b1000df8c58801bff52c400dbfa96200cff94b10037faa5880037d52c4019fe2962000ffccb10067fc6588003fd32c4019fe1962006ffd4710037fca38801bf651c400dfea8e2006fd54710037f8a388003ff31c4001ff18e2000ff4c710007f86388033ff21c4001ff10e2000fd88710007fa4388003f521c4019fe10e2006ffd431001ffca18801bfd50c4007fe2862000ffcc31001ffc6188003fd30c4007fe186200cffc831001ffc4188003fd20c4007fe1062003ffd961001dfecb0800ffe65840057f32c2003ff5961005dfacb0800ffc65840077e32c2003ffd8e1001dfec70800ffe638400f7f31c2003ff58e10005fac70800ffc63840077e31c200bffd4e1005ffca70802ffd5384017fe2
  | 2 => 0x30007fc8318003fd418c001fe20c6007ffcc630007fc6318003de318c001fe98c6007ff0c630007b86318053ff218c001ff10c6000ff486300a7f8431800efe608c007ffa846003ff9423001ffaa11800ffc508c007ffa046003ff9023001ffe611800fdf308c00ffd9846003ffc823001ff8411804fff654c0277fb2a6000dfd9530004feca9804ffe654c0057f32a6013ff5953009dfaca9804ffc654c0057e32a6013df19530014f8ca98003ff644c0017fb226000ff9913008dfcc898003fd644c0017eb226000ff1913008df8c89804fff544c027ff2a26013ff5513009ff8a89804fff534c00fff29a6013f794d3009ffaa69804fdd534c00ffe29a6000ffd0d30007be869801ffe434c001fea1a6007ff10d30007b88698003ff624c0017fb126012ff9893000dfcc498003fd624c025fe3126001bf1893009ffea49804f7f524c025ff2926013ff54930006faa49804bfc524c001ffa126012ff90930007fa849804bfc424c00fff9926000f7cc930097fc6498003fd324c001ee9926007ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c027ffa8a6013ff9453009ffaa29804ffc514c001ffa0a6000ff90530007fa8298003fc414c00fff98a6000f7cc530007fc6298003fd314c001ee98a6007ff0c530097fe4298003fe214c001fe90a6012ff0853009ffea09800ffe504c027fea826003ff14130007fe809800ffe404c001fea026007ffcc13003ff6609800ffe304c007ef1826012ffc813001ff8409800fff650c0077fb286003ff99430015fcca1800ffd650c0217eb286003ff1943001df8ca1800fff640c0077fb206003ff9903008dfcc81800ffd640c0017eb206003ff1903001df8c818043ff540c021ff2a06010ff55030087f8a81801efe630c00fffa986007ff94c3003ffaa61801ffc530c00fffa186007ff90c3003ffa861801ffc430c007ffb106003ff9883000dfcc41800ffd620c0017eb106003ff1883001df8c418043ff520c021bfa90600fff94830087faa4180037d520c01ffe2906000ffd083007ffc8418003fd420c01ffe2106007ffcc83003ffc641801ffd320c00ffe1906003ffd843001ffcc218002fe610c007feb086000bf5843001ff8c218043ff510c021ff2886010ff54430087f8a218003ff410c001ff2086000ff50430007f8821801fff310c00fff1886000f78c43003ffa621801ffc310c00fee188600fffc8430007fc4218003fd210c01ffe1086003bf9803001ffea01800ffe500c007fea806003ff1403001ffe801800ffe400c007fea006003ff1003001ffe601800fdf300c007ff1806003fe8c03001ffa601800fdd300c00ffc9806003ffc803001ff8401800fff65880077fb2c4003ff99620015fccb1000ffd658801d7eb2c4003ff1962001df8cb1000
  | 3 => 0xeb044200ff182210cffea110867fe5088433fea844219ff1422100ffe4110807fc2088403f61044218ffd95210c5feca90863fe65484057f32a4218ff595210c5faca90863fc65484057e32a4200ffd8d21005fec690803fe634840f7f31a4200ff58d21005fac690803fc634840f7e31a4218ffd4d210c7fca690863fd5348431fe29a4200ff90d21007fa8690803fc43484037fb124201ffd492100efea490807fe5248403fea924201df5492100ff8a490807ff3248403ff1924201ff4c92100ff86490806ff6148431ffa8a4218ff945210c7faa290863fc5148401ff98a4200ff8c521007fa6290803fc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290807e42148401ffb024200bfd8121007fcc090803fd6048401fe3024203bf181210c7fea090863fe5048431fea824218ff1412100ffe4090807ef2048403fe1024207ffd973003dfecb9801ffe65cc0057f32e6007ff597300bdfacb9801ffc65cc00f7e32e6007ffd933003ffcc998046fe64cc00ffeb266000bf5933003ff8c99801efc64cc02fffaa66017ff953300bffaa99805ffc54cc00fffa9e6007ff94f3003fbca79801ffd53cc02feea9e6007ff14f3003ffe8798003df43cc00fff21e6007ff50f3003ff8879801fdc43cc00fffb166007ff98b3000dfcc59801ffd62cc0017eb166007ff18b3000df8c59805fff52cc02fbfa966016ff94b300bffaa5980037d52cc02dfe2966000ffd0b300b7fc8598003fd42cc02dfe2166007ffccb3003fbe659801ffe32cc00ffe9966000f74cb3003ff8659801fff61cc00fff30e6000bf9873003ffac398002fd61cc00ffe30e6017ffd47300bffca39805ffd51cc02ffe28e6000ffd0730007fc8398003fd41cc001fe20e6007ffcc73003fbe639801ffe31cc00ffe98e6000f74c73003ff8639805bff21cc001ff10e6000ff487300b7f8439805fff50cc007ff2866017ff5433001ff8a198003ff40cc02dff9066003ff0833001ffecb1800eff658c007ff32c6002bf9963001ffacb18056fd658c007fe32c6003bf1963001ffec91800eff648c007ff3246011bf9923001f7cc918002be648c007feb246000bf5923001f7ac918002bd648c007fe3246015ffd52300affca918057fd548c02bfe2a46013bf58e300affea71801ffe538c02bfea9c6007ff14e30007fe871801ffe438c001fea1c6007ff10e3001ffec51800ffe628c0037f3146003ff58a30005fac51800ffc628c0077e3146015ffd4a300aefea518053fe528c02bfea946000df54a300a7f8a518003ff428c029ff2146000ff50a300a7f8851801fff328c029ff1946000ff4ca3003ff8651800fff618c007ff30c6000bf9863001ffac318002fd618c007fe30c6015ffd46300affca318057fd518c02bfe28c6000ffd06
  | 4 => 0x87fff208c43ffe104621effd95310f5feca9887bfe654c4057f32a621eff595310f5faca9887bfc654c4057e32a6200ffd9131005fec898803bf644c4015fb226200ff9913108dfcc898803fd644c4017eb226200ff1913108df8c898803bc644c4015e322621effd51310f7fca89887bfd544c43dfe2a2621effd4d3103ffca69887bfd534c40ffe29a6200ffd0d3103ffc8698803fd434c40ffe21a6200ffd8931005fec498877fe624c4037f3126200ff589310eff8c498806fc624c43dffa92621edfd49310effca49887bfd524c401bea92621dff14931007fe8498877fe424c401fea12621dff1093103ffe6498877fe324c401fe9926207ff0c9310f7fea29887bfe514c43dfea8a621eff14531007fe8298803fe414c401fea0a6207ffcc53103fee6298803fe314c401ef18a621dffc85310eff84298803ff604c4017fb026200ff98131007fac098803fc604c4077e302621effd41310f7fca09887bfd504c43dfe282621dffc81310eff8409881fff650c40f7fb286207ff99431015fcca1881ffd650c4377eb286207ff1943103df8ca1881fff640c40f7fb206207ff9903108dfcc81881ffd640c4017eb206207ff1903103df8c81886fff540c437ff2a0621bff550310dff8a81881efe630c40fffa986207ff94c3103fbca61881ffd530c437eea986207ff14c3103ffe8618803df430c40fff2186207ff50c3103ff8861881fdc430c40fffb106207ff9883100dfcc41881ffd620c4017eb106207ff1883100df8c41886fff520c437bfa90621aff948310dffaa4188037d520c435fe2906200ffd08310d7fc8418803fd420c435fe2106207ffcc83103fbe641881ffe320c40ffe9906200f74c83103ff86418872fe610c437ffa88621bff944310dffaa21886ffc510c401ffa086200ff90431007fa8218803fc410c40fff9886207f7cc43103ffc621881ff6310c40ffe9886200f74c43103fea621886bff210c435fe1086207ffd803103ffcc01880efe600c40ffeb006200bf5803103ff8c01886fff500c437ff280621bff540310dff8a01886bff200c435fe1006219ffd96210cdfecb10867fe65884057f32c4219ff596210cdfacb10867fc65884057e32c4200ffd8e21005fec710803fe638840f7f31c4200ff58e21005fac710803fc638840f7e31c4219ffd4e210cffca710867fd5388433fe29c4200ff90e21007fa8710803fc43884037eb144201ffd4a2100efea510807fe5288403f72944201ff54a2100efaa510867ed5288401b6a944201ff14a2100ffe6510807fe3288403fe9944201ff0ca2100dfcc310867ff5188433ff28c4219ff546210cff8a310803ff3188401ff18c4200ff4c621007f86310807ff2188403f790c4201fdc862100ff84310807f42188401ffb044200ff9822101dfcc110803fd60884017
  | 5 => 0x9532117faca9908afd654c845fe32a6402bf19532007fec899002ff644c801dfb226400afd9132007fcc899046fe644c801feb226400bf59132007f8c899046fc644c801de3226400af19132117fea89908bfe544c845feaa26422ff1513200dfec69908bff534c80fff29a6422ff54d3203ff8a699003ff434c80fff21a6400f790d32007fa8699003dd434c80ffe21a6401bfd893200ffea4990077f524c803ff2926401ff5493200efaa499007fc524c803ffa126401ff9093200ffa8499007fc424c803ff9926407fbcc93200ffc6499007de324c803fe1926401f70c93200fd86499003ff614c8017fb0a6400ff98532007fac299003fc614c8017e30a6422ffd4532117fca29908bfd514c845fe28a6401ffc853200ff84299003ff604c8017fb026400ff98132007fac099003fc604c8077e3026422ffd4132117fca09908bfd504c845fe2826401ffc813200ff8409901fff65cc40f7fb2e6207ff99731015fccb9881ffd65cc4437eb2e6207ff1973103df8cb9881fff64cc40fff3266211bf9933103ffac998802fd64cc40ffe3266207bf1933110ffea998887fe54cc443feaa66221ff1533103ffea79881ffe53cc40ffea9e6207ff14f3103ffe879881ffe43cc40ffea1e6207ff10f3103ffec59881ffe62cc4037f3166207ff58b31005fac59881ffc62cc4037e3166221ffd4b3110efea598883fe52cc443fea966200df54b31107f8a598803ff42cc441ff2166200ff50b31107f8859881fff32cc40fff1966207ff4cb3103ff86598887ff51cc443ff28e6221ff5473110ff8a398803ff41cc441ff90e6220ff0873103ffec19881ffe60cc4077f3066207ff58331005fac19881ffc60cc443ffa866221ff9433110ffaa198887fc50cc441ff9066220ff083310e7fecb18872ff658c439ff32c6202bf996310e6fccb1880a7e658c439feb2c621cbf59631006facb188027d658c439fe32c6202bf19631007fec918802ff648c401ff3246211bf99231007fac918802fd648c401fe324621cffd52310e7fca918873fd548c439fe2a4621ebf58e310e7fea71881ffe538c439ef29c621cff54e310e7baa71881ffc538c401ffa1c6200f7d0e3103ffc8718803fd438c40ffe21c6200f710e31007fec51887ffe628c4037f3146200ff58a31005fac51887ffc628c4037e314621cffd4a310e6fea51887ffe528c439fea946200df54a310fff8a518803ff428c43fff2146200ff50a310fff8851881fff328c401ef994621fff8ca31007fa6518803dd328c40ffe1946207bf986310e7fea318873fe518c439fea8c621cff14631007fe8318803fe418c40fff98c6200f7cc63103fee631887fff218c43ffe10c6200ffd8231007fcc11880efe608c401feb046200bf58231007f8c118873ff508c439ff284621cff542310e7f8a118
  | 6 => 0x1fe10c8607ffd824303ffcc12180efe6090c0ffeb048600bf5824303ff8c1218a7ff5090c53ff2848629ff5424314ff8a1218a3ff2090c51fe1048627ffd954313dfecaa189ffe6550c057f32a8627ff5954313dfacaa189ffc6550c057e32a8627ffd4d4303ffca6a189ffd5350c0ffe29a8607ff90d4303f7c86a1803ff6250c017fb128626ff9894300dfcc4a1803fd6250c4dfe3128601bf1894313ffea4a189f7f5250c4dff2928627ff54943137f8a4a189bfe3250c0ffe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a189fff5150c4fff28a8627ff5454313ff8a2a189bff2150c4dfe10a8600ffd8143005fec0a1803fe6050c01feb028600ff1814301df8c0a189fff5050c4fff2828627ff5414313ff8a0a189bff2050c4dfe1028607ffd944303dfeca2181ffe6510c057f3288607ff5944312dfaca2181ffc6510c0f7e3288607bf98c4303ffea62181ffe5310c0ffea988607ff14c4303ffc862181fde4310c0ffea188611f750c430073a862181fff6210c0fff3108601bf9884303ffac421802fd6210c0ffe3108601bf1884312ffea4218977f5210c49ff2908625ff54843127f8a42181ffe3210c49ef1908607ff0c84303fb8642181fff6110c0fff3088600bf9844303ffac221802fd6110c0ffe3088625ffd444312ffca221897fd5110c4bfe2888624ffc8443127f8422181fff6010c0fff3008603bf9804303ffac021802fd6010c0ffe3008625ffd404312ffca021897fd5010c4bfe2808624ffc8043127f840218037f6354801bf31aa400df58d52006f8c6a90037e4354801bea1aa400df10d5200efec4a90067f6254805b7b12a401df8c95200ef864a90037f6154801bf30aa400df58552006f8c2a90077f2154803be10aa401db08552006fec0a90037e6054801beb02a400df1815200efe40a90076f2054803be102a407ffd973203dfecb9901ffe65cc8057f32e6407ff5973211dfacb9901ffc65cc80f7e32e6407ffd933203ffcc999046fe64cc80ffeb266400bf5933203ff8c99901efc64cc847ffaa66423ff9533211ffaa99908ffc54cc8037f31e6407ffd4f3203ffca79901ffd53cc80ffe29e6407ffd0f3203ffc879901fde43cc80ffea1e6400f750f3203ff88799006fd62cc803ffa966401dfd4b3200ffca599007fd52cc803bea966401ff14b3200ffe8599007fe42cc803fe2166401ff8cb3200fbc6599007ee32cc803fe1966401f70cb3203ffec39901ffe61cc8017f30e6407ff58732005fac39901ffc61cc847ffa8e6423ff9473211ffaa39908ffc51cc803ff90e6401ff0873203ffec19901ffe60cc8077f3066407ff58332005fac19901ffc60cc847ffa866423ff9433211ffaa19908ffc50cc803ff9066401ff08332117feca9908aff654c845ff32a6402bf9
  | 7 => 0x100280000080c80281880b00000180100081182580080080000000500000201400180b00400c00380b00b80100280780000800b00000000380080980180200380201300080080200000d80b80300500d00a00000200503a00780401300280700400600100080a80580700381500000000680880200680500000100000000981380000800c80000080481982280300780000080200180100700280081800a00000300380000b80000400300400180d00000580400000000000780100080000600180180000280180400080000580000700180000900500000400000882280000380380380000380800380a80180700000080980080880000380280180000003484580081500600100280100282e00380382301400300001682600000180000100500000100c00000580000400b00180f80080000380180200082300280000000700080480000400202c00080180000080080400000000180080000000680000000000280402600001d00100380281500080480000001480980280180080600880080100080480680280000500700100500480000100080780600b80500f00300400000600280600180480480080180380380201680180280300100f80200000080900380202881280080180e00100000300580880000c00000800080000000000000580180a80080882180400200000200080200101180000100000200900301383800900f00a00000000000000080080480001800180400500281a00880180080d80000380380080080800080400f80000300000700100000200080300000280301300001280180280900100380080080000000080a00000e80581780180280100000180500100480e80080500100000000180000c80200000380200100e00700100000080380300180580000000200002b00000100080180400100000000000300180880f80100a80f80008880000100000700881081200000180400080280280200700080080280200000380100200480380501080080200d80000500080100080200080200000001300280080180080100680080300080080900500880000000100000400500300000900400280180f00500d80301600a00000b81fff6590c0f7fb2c8607ff99643015fccb2181ffd6590c537eb2c8607ff1964303df8cb2189efd6490c53ffaa48611ff9524314ffaa921847fc5490c0f7f31c8607ffd4e4303ffca72181ffd5390c0ffe29c8607ffd0e4308fbe872181fff6290c0fff3148601bf98a4303ffac521802fd6290c0ffe3148601bf18a4314ffea5218a77f5290c51ff2948629ff54a43147f8a5218a3fe4290c51df2148611ff10a4314778852181ffe3290c0ffe1948607ffd864303ffcc321802fe6190c0ffeb0c8600bf5864303ff8c3218a7ff5190c53ff28c8629ff5464314ff8a3218a3ff2190c5
  | 8 => 0xe61ce86b3d20353c22ae0000003108005a50af06e00000000000000046404580010c00000006e8000000000001f31ad45b4ef1213d74bd2b62be3254405021682d603b27c0f82170cb359b6938300000034b44360239dd882d963a2432190b3174c2a03bb6d2ecd5c80000055b58b5181cf4306090160f218400000049909280029b07825c0248000001960003a800000034bc181bb432d272a20f619e31738915407f51d23e28c82c31c04193c1102a75355dc0cc4cf0193d60b3e010c70175f49b64178aa1a3ca62d807301a2a36252c13cc35952201a82a13860641d4804f45395af0311cfb5725c8ac0432de4b4156220079c6b4cdb910d75cf43f5a6470987b6c63b42f5908543612053a22d41574981e450f3a60632bc06c61437611145a2840f69d030d14421f1e01be1e253403d895a6458117c1b7823555e344b20de4c86300eb3455ad07e1d634db0a56f205866512d1f2cf21597452d3196214972b90a83a0d03097ba725760739616e30422b0bd0ba0000001ba5c159a33b00000000001032819496d9b813d9aed4c19844200006400044653f00055a5c525f8de9232f226f1645a83aa5c1cf13c627d2140d90c15268be5721ea3e20ea0c010131e2e0d6862f2942695570180c1a795641c932061118f4df3182664eb09b97a1f499682f1882ef4310003d68ed3cd0e8da02511cda6d1520294ea57a0e2ba14814934c9139123c965fc16d2b412f2e7481e322a901455c36f2651ca544619104484d0bd6a1184fc50e0005b73a51025c3905e1c2854f31050000e08ca31a06ca12528509011077af737559c5634455313794415f25b532c27b2426135ed40436e0d134718639fb588135ae23c0d345216b95a360046ce45840800000003438000002bb8005b30002102fd0ef37307c3303222345de1c6618285b5ec89000049800267566125e2d63110f56d345c921fc4dd0003144035ef0bf54d12893f973c5115a8002c75f414724455111600031029a4ed0b74085df2b73123a90330004b609982000010a456018ae833529639b8229ff2bb16b0a539c2aac3803f9453e34ce5961342cb0d016907b1e624a1d7b920000004ab44a0bb63960822611b5e300048f28c0cba041cb24128650762b1323d2d6143b2985b21035bb0002610fa60002e59f07155d0271e09700000b800000055bc8b42700080080680b00880180000500080f00700080000100080000080600000000f00000101300b00580100300100500900500001a80100180000580200280700100b80180300880180280000200200000280100303180300000080700300180080200780600000502700b00200c80380300000980080680280000c80080000400000401180300000400380000300100b00100000080180680000c801000800001800003000004814800804003
  | 9 => 0x21975e136506f92280ed083051c12552f410d1b8cc08005acaa02b8d920003084360dd0090003003e90681c549553700060c15f1652d70930473246050980db39a8625754884f60f7bb73a2bd05c008b1a210d9462dd15d800480a293bc23038004037e0000003a00003385bd35f80038100045e12d000381df048e55836209ed5312232e00025243a2ac14341200054009e0c204a0b2363a2c41012024d3460d60605e00000503633d5361d3a00003981d0003550002d261b0cac62015044ccc4164f053820223681997100039c80000022a5334941064fb5ce5aeb8a00000000000051632938e42180000000000000000f0003e7d16b4c01b92780000009930b39414c8f50000005e42fe47e2e92000b5c3c46c5f34bc80000010f8003a18000004e900015841e0000b03ea12b15bc900005cd0004a51c45f962054730fc2902b12e5d229958f21b0e92c51ac30334a39f26c3780953fb48c4781172d53dd0d800d3ca53b0004ac0000005040000001d337137f52c0000f8d09ca438d47c3d4a813de0b61623bd0001c352b24b0420f32361313a4cd92a43260e7d560c0bf03a458638bd1b0c43bf39337b4a95b60495f847d5f78005854060dca5a3ba00061d1775493fc2501830014545145b40001b9de9203af84fe0bc0003720000003c45a258e5260a440f4280753128005bf8584d600047b3020c2cd3431c7f1b3840c77423000000254094c5d08e20920d5910e1c720d23565950a9061109180171df58000001e2800121ccccc21cc1611f84ad104bce5d43f25ee4075f71555dd18b0002160030000000f90ff4550000000004a305b0000003775553da00000063c0005fd2456150001068000003e28000000000b400046800024f62600051558941307900057e32f3a381f1b1bfd58a2b860f23f0e42084d24b53a35cc05f62b9b22b11e537fb899265e558fb5e2ed0001500f70000000000a726fb874f84e55301849a80392f34a24b709405652133632d00e1b33b05b85be3c3ac85e5a4fd4b45f30e20b00062a42121d3fe39000007a3744702b9af9307333591cd41e71ed3d91e80003c4cfa0083b805fc4c13728000000015b0005c92cc1b13b900011a5f53d45d65421f100042658012a9ec1991bf31f592a3a40e4bb0000000e49ce3214aa00000047504882400000000027f3b119d053298d9900000039e80c35bb5c0002580000000000000004de25b50528926b2234db00024612dcd033a0905c71d6b5220600000000012957038f0001afb480000001a127003e8000004cd20300027e09a0000005f3c2b0000251630ab00000027a0000c644400000058206a1de50a4e135b00ca590dc00044b42504140d0005d70b509080046a0001a1a6e3674742c35e6da432309602d186a4b8005bf00534004b2bf47486d0001af05156b30f0
  | 10 => 0x1ef0000fe00047916f0ec1941922710c33e433c1951958002a13e836485d0001fa364362da70005fe5290005beafb28a409126847dd00040004ae5905a100000049c00049e49b0005790002920000002ab3840001075112268000370c935a55d800398800382d7c5ea59b00038088500000005a1a31b2ab30000002f043441689f5d9176c194151ba9da3c15c633f42c1d10653704a712a00046561204c0341b50063e659e0ee1b4ae99aa09b1f92d304600035a8002484ee4855d14173434be0000004e64c300031110e5a91674ff3372bd00a14a1f43410004b01d53441f680040b1303d340500000000034480049a15344e091c632014533b416a4e809200014017e00000021e4a800007d000000170a8d05e9d25ba0001bd39e0871933151b955f13b1890000000070005452c61e959d0000002750001b723d2c262825e34d13652f53e01228e3b52fc4e735cbff0f053228f5c4d139a92910002240da39529317535f2ca3e480057d18e0438690003542f51a4cec09108335d9b429700057800000015d00000000007400062e0000005d83c709744d26213e00050003cae40ad63761f18a4c71df40003d08a4485e845754e000301260bc551e3c30005873e74bc1f211f02800ba27bc5e3d0b14e22732492c40000003af2a550d00008fd1a3340765733313421f280015e00009d00000013e89d9f72b00002131d4594129c01587a774c146d1c00000000005cb55433d39d2ac8005760003530000000768000002312d032a6330000001350e30ae1c834e83c24dcfd24e0000f4060d9330c01e3ac51221822531658d11c4f70b90895251a2d2a3861335192f608f193b983322e117240203ab7d4476162871190002900485aa5980a23e121a00000008d12c80058343e16c21160a0215624672af0f148583f54f0b2cc02b241b2aa1a719b0e031b0dfdfb14911e5480fc1f643360e2e212828b5ab2564e31595c350151c4832e52eb0000000000002e616ca0f0cf2632881758002c906f05e0005f15c28000e38218003ab078b8b00063500022e00000dcdc1249fb14d20294b588db153c342a9e5ec2fa46e14e2a8c5050656719f5db03a2cd0a025bb4c84514ea683028f5c8757f0d51254cb61a0e68383cf05c23231d41f0df22f54111404f3061a61bc4910a35170c500043d1e35bc2336233f7000061b8c47280035122e8002381785a351317d5c209c5c40e816ecb315c36853d0001b596f80000055020a0004f95773f35e216009380016635012410041100b01b52054a0c86274240ddd690000002a829510b0000e51ab3c9473237972d591fd0004b800036a0001ee6045d526a2389eb24744f3e55c08239824c52dc58e8e24ca5ac0c8dff2e360d2ad3f42feb9a2533f8072425adf3f9d6086dd103b604d2f14e00526220b4ac008e94c14
  | 11 => 0x61e1e1d0c25d35d03652e3ae13d5b908447611512711d18c1fe19014f0004d800039b56e0000673852ff0005970000fd6240002724c60001108000000000000001f000043700000031380045900004280019a37c5ca4ba3eb15c8002da3f51ae5e70fb0002351c725dad10c980025f41a1731870003ad1b680048a00009697b000000449181282399c6638857112b9408000003093b202600000007034900040c0005520000000005ab8bfa4c3f613a09880029d1dc5c82274bf4600001f5002239d0b00032717f4690862154393009cd000388e2900041c33e0002969a448d511a8d8003e3ab50320006100775bc9511850005f60ce62c3ed3f10004580002ee000434b995d31c20550e5b133d80d44202ea42e0821dfd2400000010e800103b582215b03970000002ec46f0004cf89c9794352e06033df19c0002978005f6e382db16a80029f17601c45c5da5fa14d9a50004d12070001858e70003db1481134a100048643200063e4af5430000003ec27638252332b23b4825604f514f9411d74238cd03e5653c823726018d29c4828003e68000003f90002833c00224d547a38adada1c34e1d920c2ba3be37a56c22d3663cb5363dc3bb4be9db1d84b13e040a23905708141424058c0e12280003ef00046100042d30ea959dd49d4841b05f8bb3030463de60000001e14f22e192c00013f08c0000004438000885eb4da4c400057442200011222d8442ce00034f1914713fa1085462740004a049f6170a12a660b33963655e0000003d109aaeb85900057b36b2784d7360bee1b084e4b92eaa2220e0a61a0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc705881001eef505881001eee505881001eed505881001eec505881001eef305881001eee305881001eed305881001eec305881001eef105881001ee7105881001eee105881001eed105881001ee5105881001eec10588101657f76548100067f76548100047f76548101667e76548101657d76548100067d76548100047d76548101667c76548101667f63548101767e63548101675e63548100065e63548100067d63548101675d63548100065d63548101667c635481016d7f725481002f6f72548101667f625481000e7e62548101676e625481000e6e62548100267d62548101676d62548100066d625481000e7c62548100077771548100077471548100667e61548100276c21548101667e60548101676f20548101676d20548101677710548101677a105481016775105481003cff76cc81001cfe76cc810004fd76cc81001cfc76cc81011e7e65cc8100067d65cc810006be64cc810006bd64cc81003ede63cc810006dd63cc81000eee62cc810006ed62cc810004ff764c81001cfe764c810004fd764c81001cfc764c8101167e654c8100067d654c810005bf744c810005bc744c810006be644c810006bd644c81003ede634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c810004fd76cc41010e7e65cc4100067d65cc410006be64cc410006bd64cc41003ede63cc410006dd63cc410106ee62cc410006ed62cc410004ff768c41003cfd768c41002d7e758c4100057d758c4100e67e658c4100067d658c410006be648c410006bd648c41003ede638c410006dd638c4100feee628c410006ed628c41001dfa708c410005f9708c410004ff764c4100f67e654c4100067d654c410005bf744c410005bc744c410006be644c410006bd644c41003ede634c410006dd634c4100eeee624c410006ed624c41003cff760c41001cfe760c410004fd760c41001cfc760c4100de7e650c4100067d650c410006be640c410006bd640c41003ede630c410006dd630c4100d6ee620c410006ed620c41001dfa700c410005f9700c410064ff768841001cfe768841000cfd768841001cfc76884100ce7e65884100067d6588410006de6388410006dd638841000eee6288410006ed62884100076d5288410066f6618841001dfa7088410005f97088410064ff76484100c67e65484100067d6548410006de6348410006dd634841000eee6248410006ed6248410066f66148410027e4214841001dfb7644010006fb7644010004fb76440100077b754401015f78754401001f7a654401001f796544010007db7344010007d8734401001fda634401001fd96344010007eb7244010007e8724401001fea624401001fe9624401015f7b524401000779524401001dfb714401001ff37144010156fa614401001ff26144010
  | 1 => 0x8c1001edc2098c1001edf1098c1001ede1098c1001edd1098c1001edc1098c10004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c1008cfc7458c1001edf7358c10006df5358c10006de5358c10006dd5358c10006dc5358c10004ff7258c1000cfe7258c1000cfc7258c100067f5258c10006de3258c10006dc3258c1003cff7158c1003cfd7158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c10006dc5258c10006de4258c10006dc4258c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df2158c10006dc2158c1001edf7058c1001ede7058c1001edd7058c1001edc7058c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ede1058c1001edd1058c1001edc1058c1003cff7690c1001cfe7690c10004fd7690c1001cfc7690c1014e7e6590c100067d6590c1008ebe6490c10006bd6490c1003ede6390c10006dd6390c10146ee6290c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c1013e7e6550c100067d6550c1003ede6350c10006dd6350c10136ee6250c10005f77150c10005f47150c1003cff7610c1001cfe7610c10004fd7610c1001cfc7610c1012e7e6510c100067d6510c1003ede6310c10006dd6310c100079d4310c10126ee6210c10004ff7558810014fe75588100067e75588100147e7558810004fd75588100067d7558810014fc7558810004ff735881003cfc735881001eef72588100267f5258810006ef52588100066f5258810026ee5258810006ed5258810026ec5258810026ee3258810026ec325881000cff715881000cfd7158810024fc7158810026ec215881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec205881001ef7105881001ef51058810006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ee4358810006ed4358810006ec4358810026ef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec515881001eef705881001eee705881001eed705881001ee
  | 2 => 0x5fb704851001df8704851001df4764851000ef4764851001cf4764851018df7754851018df57548510007776548510187746548510007d76348510007d46348510045f77248510007e77248510007e7624851000ef6624851000ef46248510047e4624851000ee46248510047775248510047755248510007f3704851001df6704851001df47048510007f07048510047e72048510004fe76cc1100067f65cc1100be7c65cc110006bf64cc110006bc64cc110006df63cc11003edc63cc110006ef62cc1100b6ec62cc110005f671cc110005f571cc11003cff764c110004fd764c11003cfc764c1100057f754c11004d7c754c1100067f654c11009e7c654c110006bf644c110006bc644c110006df634c11003edc634c110006ef624c110096ec624c110005f7714c110005f4714c11000cff7648110044fd764811000cfc76481100067f654811006e7c6548110006df6348110006dc6348110006ef624811000eec62481100076d5248110005f77148110005f47148110007e521481100067f65c41100367c65c4110006df63c4110006dc63c4110006ef62c4110066ec62c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c411017f7865c4110007db63c4110007d863c4110007eb62c4110007e862c411017f7b52c41100077952c411001dfa71c411001efb61c411001ff361c411017ff251c411017ff151c4110007f221c4110007f121c41100067f73594100067e73594100067d73594100067c73594100067f72594100047f72594100067e72594100067d72594100067c72594100067e32594100067c325941002e7f71594100067e715941002e7d715941002e7c71594100067f21594100067c215941001e7f705941001e7e705941001e7d705941001e7c705941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e77105941001e7e105941001e7d105941001e75105941001e7c105941003edf7598c1003ede7598c1003edd7598c1003edc7598c1003edf7498c1003ede7498c1003edd7498c1003edc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c1003edf7298c1003ede7298c1003edd7298c1003edc7298c10006df5298c100065f5298c10006de5298c10006dd5298c10006dc5298c10006de4298c10006dc4298c1003ede7198c1003edc7198c10006df5198c10006de5198c10006dd5198c10006dc5198c10006df2198c10006dc2198c1001edf7098c1001ede7098c1001edd7098c1001edc7098c1001edf5098c1001ede5098c1001edd5098c1001edc5098c1001edf4098c1001ede4098c1001edd4098c1001edc4098c1001edf2098c1001ede2098c1001edd209
  | 3 => 0x77158910064ff7058910006fb7058910005ee7618910046ee7618910004ee76189100476e75189100476d7518910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910047e571189101aeef6118910007e65118910007e551189101afe610189101afe410189100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f63549100075f63549100065f63549101767e63549100067d63549101767c63549100075c63549100065c63549100457f725491004f6f72549100467f62549100076f62549100066f625491000e7e62549100467d625491000e7c62549100476c625491000e6c62549100077671549100077571549100476c21549100476f205491016776105491003cff76cc910004fe76cc910004fd76cc91003cfc76cc9100067f65cc91011e7c65cc910006bf64cc910006bc64cc910006df63cc91003edc63cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101167c654c910005bf744c910005bc744c910006bf644c910006bc644c910006df634c91003edc634c910006ef624c91000eec624c91001cfe76cc51001cfc76cc5100067f65cc51010e7c65cc510006bf64cc510006bc64cc510006df63cc51003edc63cc510006ef62cc510106ec62cc51001dfa70cc510005f970cc510004fe768c51004d7e758c5100057d758c5100067f658c5100e67c658c510006bf648c510006bc648c510006df638c51003edc638c510006ef628c5100feec628c51001cfc764c5100067f654c5100f67c654c510005bf744c510005bc744c510006bf644c510006bc644c510006df634c51003edc634c510006ef624c5100eeec624c510005fb704c51001df8704c510004fe760c5100067f650c5100de7c650c510006bf640c510006bc640c510006df630c51003edc630c510006ef620c5100d6ec620c510054fe76885100067f65885100ce7c6588510006df6388510006dc6388510006ef628851000eec62885100076d5288510005f67688510056f676885101a5f775885101a5f5758851000777658851019f746588510007d76388510007d46388510045f57288510007e7628851000ef6628851000ef46288510047e4628851000ee46288510047775288510047e6528851004775528851019fe5528851000765528851001df6708851001df47088510197e62088510197e4208851001cfc76485100067f65485100c67c6548510006df6348510006dc6348510006ef624851000eec6248510047e42148510
  | 4 => 0x8d10006dc2118d1003edf7018d1003ede7018d1003edd7018d1003edc7018d10006df5018d101b6de5018d10006dd5018d101b6dc5018d101b6de4018d101b6dc4018d10006df2018d101b6de2018d101b6dc2018d101b6de1018d10006dd1018d101b6dc1018d1003cff7690d10004fe7690d10004fd7690d1003cfc7690d100067f6590d1014e7c6590d10006bf6490d1008ebc6490d10006df6390d1003edc6390d10146ec6290d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1013e7c6550d10006df6350d1003edc6350d10136ec6250d1003cff7610d10004fe7610d10004fd7610d1003cfc7610d100067f6510d1012e7c6510d10006df6310d1003edc6310d100079d4310d10126ec6210d10005f67110d10005f57110d1000cfe76d891004d7c75d89100067f65d89100067c65d8910006df63d8910006dc63d8910046ee62d89100076f52d8910004ff75d89100067f75d8910014fe75d8910004fd75d8910014fc75d89100067c75d89100147c75d891003cfe73d8910004fd73d89100467f52d8910006ef52d89100066f52d8910046ee52d8910006ed52d8910046ec52d8910046ee32d8910046ec32d891000cfe71d891001cfd71d891000cfc71d8910046ef21d891001cfe70d8910044fd70d891001cfc70d8910046ef20d8910045ee76d891000cee76d89100076f75d89100076c75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910197e771d8910007e651d8910007e551d8910197e610d8910197e410d8910006ef75d89100066f75d8910006ee75d8910006ed75d8910006ec75d89100066c75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d8910196ef71d8910046ee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef70d8910196ee70d8910006ed70d8910196ec70d8910006ef50d8910196ee50d8910006ed50d8910196ec50d8910196ee30d8910196ec30d8910196ee10d8910196ec10d89100057f755891004d7c75589100067f65589100067c6558910005df7358910005dc7358910006df6358910006dc6358910046ec6258910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7358910006df7358910004df735891003cfc7358910006dc735891003cdc7358910044ff7258910006ef72589100467f5258910054ff7158910006f
  | 5 => 0x75f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de62d8d10006dc62d8d100075f52d8d10007d651d8d10007d551d8d101bfd610d8d101bfd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d100065f52d8d10006de52d8d10006dd52d8d10006dc52d8d10006de42d8d10006dc42d8d101bedf71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df21d8d10006dc21d8d10006df70d8d101bede70d8d10006dd70d8d101bedc70d8d10006df50d8d101bede50d8d10006dd50d8d101bedc50d8d101bede40d8d101bedc40d8d10006df20d8d101bede20d8d101bedc20d8d101bede10d8d101bedc10d8d1004d7e7598d100057d7598d100067f6598d100067c6598d10005be7498d10005bd7498d10006bf6498d10006df6398d10045ee7298d10005ed7298d100057f7558d1004d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10005ef7258d10045ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1008cfc7458d10006bc7458d1008cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d1003ede6318d10006dd6318d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d100075f5218d10007d65118d10007d55118d101b7d61018d101b7d41018d1003edf7518d1003ede7518d1003edd7518d1003edc7518d1003edf7418d1003ede7418d1003edd7418d1003edc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d1003edf7218d1003ede7218d1003edd7218d1003edc7218d10006df5218d100065f5218d10006de5218d10006dd5218d10006dc5218d10006de4218d10006dc4218d1003edf7118d1003edd7118d10006df5118d10006de5118d10006dd5118d10006dc5118d10006df211
  | 6 => 0xc7690e1008ebe6490e10006bd6490e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e10005f77150e10005f47150e1003cff7610e1001cfe7610e10004fd7610e1001cfc7610e1003ede6310e10006dd6310e100079d4310e10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7358a1003cfc7358a1001eef7258a100567f5258a10056ee5258a10006ed5258a10056ef2158a1001cfc7058a1001eee2058a1001eec2058a1001ef71058a1001ef51058a100067f7654a101667e7654a100067d7654a101667c7654a101667f6354a101767e6354a100067d6354a101667c6354a1016d7f7254a1005f6f7254a101667f6254a1000e7e6254a101676e6254a1000e6e6254a100567d6254a101676d6254a100066d6254a1000e7c6254a10007777154a10007747154a100467d6154a100576c2154a101667e6054a101676f2054a101676d2054a10167771054a1003cff76cca1001cfe76cca10004fd76cca1001cfc76cca1003ede63cca10006dd63cca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca10005bf744ca10005bc744ca1003ede634ca10006dd634ca10005f7714ca10005f4714ca1003ede63cc610006dd63cc61001dfa70cc610005f970cc61005d7e758c6100057d758c6101bedf638c61003edc638c61003cff764c610005bf744c610005bc744c61003ede634c610006dd634c610005fb704c61001df8704c6101b6df630c61003edc630c610044fd7688610196ef628861000eec62886100076d528861000cff764861001cfc764861000eee6248610006ed6248610057e42148610005fb704861001df8704861001df976c4210006f976c42101cf7b52c42100077952c421001ff271c421004d7e76d951004e7e76d95100147e76d95100057d72d95100067e62d95100067c62d95101c77771d951004f7471d95101c77610d95101c77410d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067e32d95100067c32d95101c67f71d951004e7e71d951004e7d71d951004e7c71d95100067f21d95100067c21d95100067f70d95101c67e70d951004e7d70d95101c67c70d95101c67e30d95101c67c30d95100067f20d95101c67e20d95101c67c20d95101c67e10d951004e7d10d95101c67c10d951003cfe76d8d100067f65d8d100067c65d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d1008cfe74d8d10004fd74d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d10006de32d8d10006dc32d8d1003cfe71d8d1003cfc71d8d1001cfe70d8d1001cfc70d8d1003cde76d8d10006df65d8d10
  | 7 => 0xf10066ee62d8b10004ff75d8b10014fe75d8b10004fd75d8b10014fc75d8b1003cfe73d8b10004fd73d8b10064fd72d8b100667f52d8b10066ee52d8b10006ed52d8b10006f671d8b10066ef21d8b10006f970d8b10196ee20d8b10196ec20d8b1000cff7658b10066ec6258b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7358b1003cfc7358b10006ef7258b100667f5258b1001cfc7158b10066ec2158b10066ef2058b100067f7654b100067e7654b100067d7654b100067c7654b100067f6354b101767e6354b100067d6354b101767c6354b100657f7254b100376f7254b100667f6254b100076f6254b100066f6254b1000e7e6254b100667d6254b1000e7c6254b100676c6254b1000e6c6254b10007767154b10007757154b100676c2154b100676f2054b1003cff76ccb10004fe76ccb10004fd76ccb1003cfc76ccb10006df63ccb1003edc63ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10005bf744cb10005bc744cb10006df634cb1003edc634cb10006df63cc71003edc63cc71001cfd768c7100357e758c7100057d758c71003ede638c710006dd638c71001dfa708c710005f9708c710005bf744c710005bc744c710006df634c71003edc634c71001cfd760c71003ede630c710006dd630c71001dfa700c710005f9700c71001cfd768871000eee6288710006ed62887100076d528871001dfa7088710005f9708871001df5768871000ef5768871001cf576887101e5f775887101e5f5758871000ef66288710067e66288710007e5628871000ef46288710067775288710067e652887100677552887101dfe5528871000765528871001df67088710007f27088710007f1708871001df47088710197e62088710197e42088710024ff7648710006ef624871000eec6248710067e42148710005f77648710026f776487101d5f775487101d5f57548710007e77248710007e7624871000ef6624871000ef46248710067e4624871000ee4624871006777524871006775524871001df6704871001df47048710067e7204871003ede63cc310006dd63cc310005f671cc310005f571cc31003cff764c3100057f754c3100357c754c31003ede634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc764831000eee6248310006ed62483100076d5248310005f77148310005f47148310007e52148310004ff7558e100067f7558e100047f7558e10014fe7558e10004fd7558e10014fc7558e100067c7558e100147c7558e10004ff7458e1008cfc7458e1001edf7358e10006de5358e10006dd5358e10004ff7258e1000cfe7258e1000cfc7258e100067f5258e1001cfc7058e1001ede3058e1001edc3058e1003cff7690e1001cfe7690e10004fd7690e1001cf
  | 8 => 0x6f451d8520056f621d8520056f521d85200076d5298520006f76198520045f970985200057f755852006d7c7558520005df7358520005dc73585200076d5258520065fb705852006d7e75185200057d75185200076d5218520006f56118520004ff7518520014fe75185200067e75185200147e7518520004fd75185200067d75185200047d7518520014fc751852003cfe7318520004fd731852001cfd72185200267f5218520026ee52185200267d5218520006ed52185200066d5218520006f75118520006f45118520026ef2118520026f62118520026f5211852001cfe701852001cfc70185201aeee20185201aeec2018520004fe76cc520004fd76cc52003cfc76cc5200076d52cc520006f761cc520006f461cc520004fe768c520004fd768c520004fc768c52006d7e758c5200057d758c520006df638c52003edc638c52000dee728c520005ed728c5200076d528c520004ff764c520004fe764c520004fc764c520005bf744c520005bc744c5200076d524c520004fe760c520004fd760c52003cfc760c520006df630c52003edc630c52000dee720c520005ed720c5200076d520c520006f7610c520006f4610c52001dfa700c520005f9700c52001cec76485201edef75485201eded754852000def714852000fe77148520007e76148520006ec6148520007e46148520006e46148520007eb704852001dee704852001dec7048520007e8704852000eef604852000feb604852000cfe76cc12000cfc76cc120006df63cc12003edc63cc12000dee72cc120005ed72cc1200076d52cc12003cff764c12000cfe764c120094fd764c12000cfc764c1200057f754c12006d7c754c120006df634c12003edc634c120005ef724c12000dec724c1200076d524c1200357e75d8f100057d75d8f10004ff75d8f10014fe75d8f100067e75d8f100147e75d8f10004fd75d8f100067d75d8f100047d75d8f10014fc75d8f1008cfe74d8f10004fd74d8f10006de53d8f10006dd53d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100067f52d8f10006f671d8f10006f970d8f101bede30d8f101bedc30d8f10004fd7698f10006df6398f1003cff7658f10005bf7458f10005bc7458f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f10006bf7458f10004bf7458f1008cfc7458f10006bc7458f1008cbc7458f10006df7358f10004ff7258f1000cfe7258f1000cfc7258f100067f5258f1003ede6318f10006dd6318f1003cff7690f10004fe7690f10004fd7690f1003cfc7690f10006bf6490f1008ebc6490f10004ff7650f10004fe7650f10004fd7650f10004fc7650f1003cff7610f10004fe7610f10004fd7610f1003cfc7610f10006df6310f1003edc6310f100079d4310f10005f67110f10005f5711
  | 9 => 0x77158620006f65158620006f55158620046f62158620046f52158620046ec215862001cfc705862001eef205862001eed205862001ef6105862001ef4105862003cff76cc62001cfe76cc620004fd76cc62003ede63cc620006dd63cc62000dee72cc620005ed72cc620004ff768c62001cfe768c620004fd768c6200757e758c6200057d758c6201bedf638c62003edc638c620004ff764c620004fd764c62001cfc764c620005bf744c620005bc744c62003ede634c620006dd634c620005ef724c62000dec724c62003cff760c62001cfe760c620004fd760c6201b6df630c62003edc630c62001dfa700c620005f9700c620196ef65886201f6ed658862000dee718862000fe67188620197e66188620006ed6188620197e56188620197ea7088620195ed7088620007e9708862000eee608862000fea608862003cfe76d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d2008cfe74d8d20004fd74d8d20006df53d8d20006dc53d8d2001cff72d8d2000cfe72d8d2001cfd72d8d2000cfc72d8d200a67f52d8d200a67d52d8d200a6df32d8d200a6dd32d8d20004fe71d8d20004fd71d8d20006df6398d20095f97098d200057f7558d2006d7c7558d20005bf7458d20005bc7458d20005f77158d20005f47158d200b5fb7058d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d2008cfc7458d20006bc7458d2008cbc7458d20006df7358d20094ff7258d20006ef7258d200967f5258d200967d5258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200b4ff7058d20006fb7058d200a4fe7618d2003ede6318d20006dd6318d2003cff7690d20004fe7690d20004fd7690d2003cfc7690d20006bf6490d2008ebc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2003cff7610d20004fe7610d20004fd7610d2003cfc7610d20006df6310d2003edc6310d200079d4310d2000dee7210d20005ed7210d2006f6f76549200166f765492006f6c76549200166c76549200076f73549200076e73549200076d73549200076c73549200076f63549200076e63549200076d63549200076c63549200076e43549200076d43549200076c43549200076f71549200076e71549200076d71549200076c71549200076f70549200076b70549201676e705492006f6d70549201676c705492000768705492000f6f605492000e6f605492000f6b60549201676e30549201676c30549200076d52d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852003cfe73d8520004fd73d852001cfd72d85200567f52d85200567d52d8520006f751d8520
  | 10 => 0x84300067d529843001ef67198430006f65198430006f5519843003ef7319843003ef4319843001ef6109843001ef41098430004ff7558430014fe7558430004fd7558430014fc7558430004ff7458430006bf7458430004bf745843008cfc7458430006bc745843008cbc7458430004ff725843000cfe725843000cfc72584300067f52584300067d525843001ef77158430006f65158430006f5515843003ef7315843003edc315843003ef4315843001edf305843001edd305843001ef6105843001ef4105843008cff76d043001cfe76d0430004fd76d043008ebe64d0430006bd64d043003dde73d0430005dd73d0430004ff769043001cfe7690430004fd76904300857e75904300057d7590430216bf6490430006f66190430006f56190430004ff7650430004fd765043001cfc765043008ebe6450430006bd6450430005df735043003ddc7350430006f66150430006f5615043008cff761043001cfe7610430004fd761043020ebf641043008ebc641043003ddd768c430006dd768c430004dd768c4301ff5e758c4300075d758c43003edf658c4301fedd658c430206de648c43003edc648c430006dd628c4301ff5f528c4300075d528c43003dde718c43003fd6718c430006dd618c4301bddd708c4301bede608c43003fda608c430004ff768843001cfe7688430004fd76884300076d5288430006f66188430006f56188430004ff7648430004fd764843001cfc7648430005df734843003ddc734843000eee6248430006ed6248430006f66148430006f5614843007fe42148430004ff7558e200067f7558e200047f7558e20014fe7558e20004fd7558e20014fc7558e200067c7558e200147c7558e20004ff7458e2008cfc7458e2001edf7358e20006de5358e20006dd5358e200967f5258e200967d5258e20096df3258e20096dd3258e20004ff7158e20004fc7158e2001cfe7058e2001cfc7058e2001ede3058e2001edc3058e2003cff7690e2001cfe7690e20004fd7690e2001cfc7690e2008ebe6490e20006bd6490e20004ff7650e2001cfe7650e20004fd7650e2001cfc7650e20005ef7250e2000dec7250e2003cff7610e2001cfe7610e20004fd7610e2001cfc7610e2003ede6310e20006dd6310e200079d4310e20004ff7598620014fe7598620004fd7598620014fc759862003cfe7398620004fd73986200667f52986200667d529862001ef67198620006f65198620006f55198620066f62198620066f5219862001cfe709862001ef6109862001ef41098620004ff75586200067f75586200047f7558620014fe7558620004fd7558620014fc75586200067c75586200147c7558620004ff7358620006df7358620004df735862003cfc7358620006dc735862003cdc73586200467f52586200467d525862001ef
  | 11 => 0x6f4618c53001dfa708c530005f9708c53001cfc764c5300067f654c5300f67c654c530005bf744c530005bc744c530006f7614c530006f4614c530005fb704c53001df8704c53001cdc764c530245df754c530245dd754c5300075f654c53023f5c654c5300079f744c53022dde744c53022ddc744c5300079c744c5300059c744c530005df724c53023f5f524c5300075d524c53003ddf714c53003fd7714c530007d7614c530006dc614c530007d4614c530007db704c53001dde704c53001ddc704c530007d8704c53003edf604c53003fdb604c530004fe7688530004fd7688530004fc76885300067f65885300ce7c658853003dde7388530005dd7388530006ef628853000eec62885300076d5288530004ff7648530004fe7648530004fc76485300067f65485300c67c654853003dde7348530005dd7348530097e4214853003cfe76d013003cfc76d01300067f65d01302367c65d0130006bf64d013008ebc64d013003dde73d0130005dd73d013022f9c43d0130004fd765013003cfc76501300067f65501302267c6550130005df735013003ddc73501300079c4350130004ff7559030014fe7559030004fd7559030014fc755903001cff745903001ebf7459030006be5459030006bd545903003cff735903003cfe735903003cfd735903003cfc735903003ebe435903003ebc4359030004ff725903000cfe725903000cfc72590300067f5259030004ff7159030004fc715903001cfe705903001cfc705903001ebe405903001ebc4059030004ff7558830014fe7558830004fd7558830014fc7558830004ff745883008cfc745883000cfd735883001cff725883001eef725883007e7f525883007eee5258830006ed525883007eee425883003eef325883003eec3258830004ff7158830004fc715883003edc315883007eef215883001cfc705883001edf305883001edd305883001eee205883001eec20588300067f76548301667e76548300067d76548301667c76548301667f645483021e7e64548300067d64548301667c64548300075f73548301775c73548300b67e635483016d7f72548300876f72548301667f625483000e7e62548301676e625483000e6e625483007e7d62548301676d62548300066d625483000e7c62548301775c315483007f6c21548301667e60548301675f30548301677a30548301675d30548301777930548301676f205483008cff76d083001cfe76d0830004fd76d083008ebe64d0830006bd64d0830004ff7650830004fd765083001cfc765083008ebe6450830006bd6450830005df735083003ddc735083000eee6250830006ed6250830004ff7598430014fe7598430004fd7598430014fc759843008cfe7498430004fd749843000cfe7298430004fd729843000cfc72984300067f529
  | 12 => 0xe76cc93003ddf75cc930295dd75cc9300075f65cc93028f5c65cc93022dde74cc93003ddc74cc930006df64cc930006dd64cc930095dd72cc93000ede62cc93000edc62cc9300975f52cc9300975d52cc930005dd71cc93001dde70cc93001ddc70cc93003edf60cc93003fdb60cc93001cfc764c9300067f654c9301167c654c930005bf744c930005bc744c930006ef624c93000eec624c930005fb704c93001df8704c93001ddc764c93000edc764c93001cdc764c930285df754c930285dd754c9300075f654c93027f5c654c9300079f744c93022dde744c93022ddc744c9300079c744c9300059c744c930006df644c930006dd644c93003ddf724c93003fcf724c930007cf624c93000ede624c93000edc624c930097cc624c9300975f524c9300975d524c930005df714c930007db704c93001dde704c93001ddc704c930007d8704c93003edf604c93003fdb604c9300067f65d85300067c65d8530004ff75d8530014fe75d8530004fd75d8530014fc75d853008cfe74d8530004fd74d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006f721d8530006f421d853009d7e75985300057d75985300067f65985300067c6598530006f761985300057f755853009d7c75585300067f65585300067c6558530005bf7458530005bc7458530005ef7258530095ec72585300067f65185300067c6518530006f56118530004ff7518530014fe7518530004fd7518530014fc751853008cfe7418530004fd7418530006de5318530006dd5318530006df4318530006dc431853000cfe7218530004fd721853000cfc72185300067f52185300067d5218530006df3218530006dd3218530006f72118530006f421185301b6de30185301b6dc3018530004fe76d0530004fd76d053008cfc76d05300067f65d05302767c65d0530006f761d0530006f461d0530004fe7690530004fd7690530004fc769053009d7e75905300057d75905300067f659053026e7c6590530006bf649053008ebc649053003dde7390530005dd73905300079c4390530004ff7650530004fe7650530004fc76505300067f65505302667c6550530005df735053003ddc7350530004fe7610530004fd761053008cfc76105300067f651053025e7c6510530006bf641053008ebc641053003dde7310530005dd731053022f9c4310530006f76110530006f46110530005de76cc53003ede76cc530004de76cc53003ddf75cc530255dd75cc5300075f65cc53024f5c65cc53022dde74cc53003ddc74cc530005dd72cc53024f5f52cc5300075d52cc530006dc61cc53001dde70cc53001ddc70cc53003edf60cc53003fdb60cc53001cfe768c53009d7e758c5300057d758c5300067f658c5300e67c658c530245dd738c530006f7618c530
  | 13 => 0x9130005f47159130004ff75591300067f75591300047f7559130014fe7559130004fd7559130014fc75591300067c75591300147c7559130006df7359130004ff7259130006ef7259130004ef725913000cfe725913000cfc7259130006ec725913000cec72591300067f5259130004ff7159130006f77159130004f77159130004fc7159130006f47159130004f47159130004ff7059130006fb7059130004fe76191300067f65191300067c651913008ebe6419130006bd641913001cfe76d0d300067f65d0d302de7c65d0d30006bf64d0d3008ebc64d0d3001dfa70d0d30005f970d0d3001dde76d0d3022ede76d0d3001cde76d0d3022ddf75d0d302d5dd75d0d300075f65d0d302c75c65d0d3003dde74d0d3022edf64d0d300079f64d0d3022edd64d0d3022f9c64d0d30005dd72d0d302cede62d0d302cedc62d0d302c75f52d0d30005dd71d0d3001dde70d0d3022fda70d0d3022fd970d0d3001ddc70d0d3003edf60d0d3003fdb60d0d3001cfc7650d300067f6550d3013e7c6550d30006bf6450d3008ebc6450d3003f9c4350d30005fb7050d3001df87050d30005de7610d3003ede7610d3003ddf7510d302bddd7510d300075f6510d302b75c6510d3022dde7410d3003f9e7410d3022edf6410d3022f9e6410d3022edd6410d300079d6410d300069d6410d30005dd7210d30126de6210d30126dc6210d302b75f5210d302af9e4210d3022f9c4210d30005dd7110d3001dde7010d3001ddc7010d3003edf6010d3003fdb6010d3000cfe76d893009d7c75d89300067f65d89300067c65d8930096ee62d8930004ff75d89300067f75d8930014fe75d8930004fd75d8930014fc75d89300067c75d89300147c75d893008cfe74d8930004fd74d893001cfd73d893000cfc73d89300967f52d8930096ec42d8930096ee32d8930004fe71d8930004fd71d8930096ec21d893003cfd70d8930096ef20d89300057f755893009d7c75589300067f65589300067c6558930005bf7458930005bc7458930096ec6258930005f77158930005f471589300067f76549300057e76549300067e76549300047e76549300067d76549300057c76549300067c76549300047c76549300067f645493021e7e64549300067d645493021e7c64549300075e73549300075d73549300075f43549300075c43549300957f725493009f6f72549300967f625493000e7e625493000e7c62549300976c21549301777b30549301675e30549300976f2054930004fe76d0930004fd76d093008cfc76d09300067f65d09302a67c65d093008ebe64d093022f9f43d0930006ef62d093000eec62d0930004ff7650930004fe7650930004fc76509300067f655093029e7c655093008ebe6450930005df735093003ddc73509300079f4350930005de76cc93003ed
  | 14 => 0x4fd76906300ad7e75906300057d759063008ebe6490630006bd6490630004ff7650630004fd765063001cfc765063008ebe6450630006bd6450630005df735063003ddc735063008cff761063001cfe7610630004fd761063008ebe6410630006bd64106300ad7e758c6300057d758c630006be648c630006bd648c630006f6618c630006f5618c63001dfa708c630005f9708c6303075e758c6300075d758c6301bedf658c630306dd658c630206de648c6301bf9e648c6300069e648c6301bf9d648c630006dd628c6303075f528c6300075d528c63003dde718c6301bfd6618c630006dd618c6301bfd5618c6301bfda708c6301bddd708c630007d9708c63003ede608c630005bf744c630005bc744c630006be644c630006bd644c630006f6614c630006f5614c630005fb704c63001df8704c6301b5dd760c63003edd760c6301b6df650c6302f6dd650c6302fede640c6301b79e640c6300069e640c6301b79d640c630006dd620c6302f75f520c6300075d520c63003fd6710c630006dd610c63003ddf700c6301b5dd700c63003fda600c630004ff768863001cfe7688630004fd7688630006be6488630006bd64886300076d5288630006f66188630006f56188630004ff7648630004fd764863001cfc7648630006be6448630006bd6448630005df734863003ddc734863000eee6248630006ed6248630006f66148630006f561486300a7e4214863009d7e76d953009e7e76d95300147e76d95302e75f73d953009f5c73d95300057d72d95300067e62d95300067c62d95302ef7b30d95302e75e30d95302e75c30d95302ef7830d95300067f74d95300067e74d95300067d74d95300067c74d95302e67f73d95302ee7e73d953009e7d73d95302ee7c73d95302ee7e43d95302ee7c43d95300067f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067e42d95300067c42d95302ee7f32d95300067e32d95302ee7c32d95300067f71d95300067e71d95300067d71d95300067c71d95302ee7f31d95302ee7c31d95300067f21d95300067c21d95302ee7f70d95302e67e70d953009e7d70d95302e67c70d95302e67e40d95302e67c40d95302ee7f30d95302e67e30d953009e7d30d95302e67c30d95300067f20d95302e67e20d95302e67c20d95302e67e10d95302e67c10d95300067f65d91300067c65d9130004ff75d9130014fe75d9130004fd75d9130014fc75d913003cfe73d9130006dd73d913000cfe72d9130004fd72d913000cfc72d91300067f52d9130006be42d9130006bc42d9130004fe71d9130004fd71d913009d7e75991300057d75991300067f65991300067c6599130006bf64991300057f755913009d7c75591300067f65591300067c6559130005ef7259130095ec7259130005f7715
  | 15 => 0xf535923030ebe5359230006bd535923030ebc5359230006bf7259230006be7259230006bd7259230006bc7259230006bf52592300063f5259230006be5259230006bd5259230006bc525923030ebf3259230006be325923030ebc3259230006bf7159230006be7159230006bd7159230006bc7159230006bf5159230006be5159230006bd5159230006bc515923030ebf315923030ebc3159230006bf2159230006bc215923001ebf705923001ebe705923001ebc705923001ebf505923001ebe505923001ebd505923001ebc505923001ebf305923001ebe305923001ebd305923001ebc305923001ebf205923001ebe205923001ebd205923001ebc205923001ebf105923001ebe105923001ebd105923001ebc105923008ebe64d0e30006bd64d0e3001dfa70d0e30005f970d0e3008cff7650e3008ebe6450e30006bd6450e3003f9c4350e30005fb7050e3001df87050e30004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a3008cfc7458a3001eef7258a300a67f5258a300a6ee5258a30006ed5258a300a6ee3258a30004ff7158a30004fc7158a300a6ef2158a3001cfc7058a3001edf3058a3001edd3058a3001eee2058a3001eec2058a300067f7654a301667e7654a300067d7654a301667c7654a301667f6454a3021e7e6454a301673e6454a300063e6454a300067d6454a301673d6454a300063d6454a300075f7354a300075c7354a300967d6354a3016d7f7254a300af6f7254a301667f6254a3000e7e6254a301676e6254a3000e6e6254a300a67d6254a301676d6254a300066d6254a3000e7c6254a300a76c2154a301667e6054a301675f3054a301777b3054a301676f2054a3008cff76d0a3001cfe76d0a30004fd76d0a3008ebe64d0a30006bd64d0a30004ff7650a30004fd7650a3001cfc7650a3008ebe6450a30006bd6450a30005df7350a3003ddc7350a3000cff764ca30005bf744ca30005bc744ca30006be644ca30006bd644ca3000eee624ca30006ed624ca30005fb704ca3001df8704ca30004ff7598630014fe7598630004fd7598630014fc759863008cfe7498630004fd749863000cfe7298630004fd729863000cfc72986300067f52986300067d529863001ef67198630006f65198630006f5519863001cfe709863001ef6109863001ef41098630004ff7558630014fe7558630004fd7558630014fc7558630004ff745863008cfc7458630004ff725863000cfe725863000cfc72586300067f52586300067d525863001ef77158630006f65158630006f5515863001cfc705863001edf305863001edd305863001ef6105863001ef4105863008cff76d063001cfe76d0630004fd76d063008ebe64d0630006bd64d063003dde73d0630005dd73d0630004ff769063001cfe7690630
  | 16 => 0x873000cfc72987300067f52987300067d529873003edf3298730006dd329873003ef6719873003edf319873003ef7319873003ef431987301bede309873003edc3098730004ff7558730014fe7558730004fd7558730014fc7558730004ff745873008cfc745873001cfc7358730004ff725873000cfe725873000cfc72587300067f52587300067d525873003ef7715873003ef7315873003ef4315873008cff76d073003cfe76d0730004fd76d073003ddc73d0730004ff769073003cfe7690730004fd76907300bd7e75907300057d759073008ebe6490730006bd649073003dde7390730005dd739073033f9c4390730004ff7650730004fd765073003cfc7650730005df735073003ddc735073008cff761073003cfe7610730004fd761073008ebe6410730006bd641073003dde7310730005dd73107303379c431073003ddf764c730006df764c73032ddf754c73032ddd754c7300079f744c730325de744c730325dc744c7300079c744c7300059c744c730005df724c73031f5f524c7300075d524c73003fd7714c730006de614c73001dde704c73001ddc704c730004ff768873003cfe7688730004fd768873003dde7388730005dd738873000eee6288730006ed62887300076d5288730004ff7648730004fd764873003cfc764873003dde7348730005dd73487300b7e4214873003dde73d0330005dd73d03303179c43d033008ebf759923008ebe759923008ebd759923008ebc759923008ebf739923008ebe739923008ebd739923008ebc7399230006bf5399230316be5399230006bd5399230316bc539923008ebf729923008ebe729923008ebd729923008ebc7299230006bf52992300063f5299230006be5299230006bd5299230006bc5299230316bf3299230006be3299230316bc329923008ebf719923008ebe719923008ebd719923008ebc7199230006bf5199230006be5199230006bd5199230006bc5199230316bf3199230316bc3199230006bf2199230006bc219923001ebf709923001ebe709923001ebd709923001ebc709923001ebf509923001ebe509923001ebd509923001ebc509923001ebf309923001e9f309923001ebe309923001ebd309923001e9d309923001ebc309923001ebf209923001ebe209923001ebd209923001ebc209923001ebf109923001ebe109923001ebd109923001ebc1099230004ff7559230014fe7559230004fd7559230014fc755923001ebf7459230006bf5459230006be5459230006bd5459230006bc5459230004ff725923000cfe725923000cfc72592300067f5259230006be4259230006bc4259230004ff7159230004fc715923001cfc705923001ebe405923001ebc4059230006bf7559230006be7559230006bd7559230006bc7559230006bd735923030ebc7359230006b
  | 17 => 0x6dd638c5210ffe4218c52103cff764c52100cfe764c5210ecfd764c52100cfc764c521005bf744c521005bc744c521006df634c52103edc634c521005ef724c52100dec724c5210efe4214c5210fcfe760c52103ede630c521006dd630c5210d7e4210c52135eef658852135eed658852100dee718852100fe6718852100de6718852100eef618852100fe76188521005ed7088521067e421d8121004ff75d8121014fe75d8121004fd75d8121014fc75d812103cfe73d8121004fd73d81210667f52d81210667d52d8121066fa20d8121057e42198121006fb60981210057f75581210c57c7558121005df7358121005dc7358121047e421581210c57e75181210057d7518121005de7318121005dd7318121196ef6218121027e4211812101efa6018121006f96018121004ff7559330014fe7559330004fd7559330014fc755933003ebf7459330006bf5459330006bc545933001cfc735933001cdc735933003ebe435933003ebc435933003edc435933003e9c4359330004ff725933000cfe725933000cfc72593300067f525933003edf3259330004ff7159330004fc715933003ddd76d0f30326dd76d0f30325df75d0f30355dd75d0f3003f9e74d0f3003edf64d0f30326dd64d0f30005dd72d0f302cede62d0f3003edc62d0f3034f5f52d0f30005dd71d0f3001dde70d0f3001ddc70d0f30004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3008cfc7458b3001cfc7358b3003eef7258b300b67f5258b3003eef3258b3003eec3258b30004ff7158b30004fc7158b300b6ec2158b300b6ef2058b300067f7654b301767e7654b300067d7654b301767c7654b3021e7e6454b300067d6454b301767c6454b301775e7354b300075d7354b300075f4354b301775c4354b300b57f7254b300bf6f7254b300b67f6254b3000e7e6254b300b67d6254b3000e7c6254b300b75f3254b301775f3154b300b76c2154b300b76f2054b3008cff76d0b3003cfe76d0b30004fd76d0b3008ebe64d0b30006bd64d0b3003ddc73d0b303279f43d0b30004ff7650b30004fd7650b3003cfc7650b3008ebe6450b30006bd6450b30005df7350b3003ddc7350b300079f4350b3003ddf764cb3007edf764cb30345df754cb30345dd754cb300079f744cb30325de744cb30325dc744cb300079c744cb300059c744cb30006dd644cb3003fcf724cb3000ede624cb3000edc624cb300b75f524cb300b75d524cb30005df714cb3001dde704cb3001ddc704cb30004ff7598730014fe75987300067e75987300147e7598730004fd75987300067d75987300047d7598730014fc759873008cfe7498730004fd749873001cfe739873001cde739873003ede5398730006dd5398730006df439873003edc439873000cfe7298730004fd729
  | 18 => 0xf7654a210166f7654a210cf6c7654a210166c7654a210076f7354a210076e7354a210076d7354a210076c7354a210076f6354a210076e6354a210076d6354a210076c6354a210076e4354a210076d4354a210076c4354a210076f7154a21007677154a210cf6e7154a210076d7154a210076c7154a21007647154a2100f6e6154a2100e6e6154a2100f666154a210076f7054a210076e7054a210076d7054a210076c7054a210ecfd76cc6210076d52cc62100cff768c62100cfd768c6210cd7e758c6210057d758c62103ede638c621006dd638c62100dee728c621005ed728c6210076d528c621104ff764c621005bf744c621005bc744c6210076d524c62100cff760c62100cfd760c62103cfc760c62103ede630c621006dd630c62100dee720c621005ed720c6210076d520c6210076d52d82210076d5298221006fb60982210057f75582210cd7c75582210076d5258221004ff75582210067f75582210047f7558221014fe7558221004fd7558221014fc75582210067c75582210147c7558221004ff735822103cfc73582210467f5258221046ee52582210467d5258221006ed52582210066d5258221046ef2158221046fa2058221196ec20582210cd7e75182210057d7518221005de7318221005dd73182210076d521822101efa6018221006f9601822103cfe76d8d210c57e75d8d210057d75d8d210ffe421d8d21004ff75d8d21014fe75d8d210067e75d8d210147e75d8d21004fd75d8d210067d75d8d210047d75d8d21014fc75d8d2108cfe74d8d21004fd74d8d21006de53d8d21006dd53d8d210fcff72d8d210fcfd72d8d210fe7f52d8d210fe7d52d8d210fedf32d8d210fedd32d8d2101cfe70d8d21004fd70d8d21006df6398d210edf57198d21107e42198d21005bf7458d21005bc7458d21105f77158d210efe42158d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21006bf7458d21004bf7458d2108cfc7458d21006bc7458d2108cbc7458d21006df7358d210ecff7258d21006ef7258d210ee7f5258d210ee7d5258d21104ff7158d21006f77158d21004ff7058d2101cfc7058d210fcfe7618d2103ede6318d21006dd6318d210d7e42118d2103cff7690d21004fe7690d21004fd7690d2103cfc7690d21006bf6490d2108ebc6490d21147e42190d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21005ef7250d2100dec7250d21005f77150d21005f47150d21137e42150d2103cff7610d21004fe7610d21004fd7610d2103cfc7610d21006df6310d2103edc6310d210079d4310d21127e42110d2100cfe76cc52100cfc76cc521006df63cc52103edc63cc52100dee72cc521005ed72cc521107e421cc5210d4fe768c5210c57e758c5210057d758c52103ede638c521
  | 19 => 0x83103cfe76d0831004fd76d083108ebe64d0831006bd64d083103ddc73d08312ff9f43d0831004ff7650831004fd765083103cfc765083108ebe6450831006bd6450831005df735083103ddc73508310079f435083103ddf764c831106df764c83137ddf754c83137ddd754c8310079f744c8312fdde744c8312fddc744c8310079c744c8310059c744c83103edf644c831006dd644c83103ddf724c83103fcf724c83100ede624c83100edc624c8310d75f524c8310d75d524c831005df714c8310fede614c83103fd6614c8311b5dc704c831004fd76d043103ddc73d0431004ff769043108cfd76904310dd7e75904310057d759043108ebe6490431006bd649043103dde7390431005dd739043133f9c4390431004ff7650431005df735043103ddc735043103cfe7610431004fd761043103cfc761043103dde7310431005dd73104313379c431043103ddf764c431006df764c431004df764c431375df754c431375dd754c4310079f744c4312fdde744c4312fddc744c4310079c744c4310059c744c431005df724c4313675f524c4310075d524c43103ddf714c43103fd7714c43136ede614c43103fd6614c431367d6514c431367d5514c4311b5dc704c431004ff75580310067f75580310047f7558031014fe7558031004fd7558031014fc75580310067c75580310147c7558031004ff745803108cfc745803103ede5358031006dd5358031006df435803103edc4358031004ff725803100cfe725803100cfc72580310067f52580310067d525803103edf3258031006dd325803103edf3158031006dd315803103efb705803103efb305803103edc305803103ef830580310cd7e75d8e210057d75d8e21005be74d8e21005bd74d8e210d5f671d8e21004ff75d8e21014fe75d8e210067e75d8e210147e75d8e21004fd75d8e210067d75d8e210047d75d8e21014fc75d8e2108cfe74d8e21006be74d8e2108cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e21006ed72d8e210fe7f52d8e210fe7d52d8e210d4fe71d8e21006f671d8e2101cfe70d8e21004fd70d8e210ecfd7698e21006df6398e2103cff7658e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e2108cfc7458e21006df7358e21006df5358e21006dc5358e210ee7f5258e210ee7d5258e210eedf3258e210eedd3258e21004ff7058e2101cfc7058e2103ede6318e21006dd6318e210fdf67118e2103cff7690e21004fe7690e21004fd7690e2103cfc7690e2108ebe6490e21006bd6490e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21005f77150e21005f47150e2103cff7610e21004fe7610e21004fd7610e2103cfc7610e2103ede6310e21006dd6310e210079d4310e2100dee7210e21005ed7210e210cf6
  | 20 => 0xef6c21549311667c60549310ef6f2054931004fe76d0931004fd76d093108cfc76d0931006bf64d093108ebc64d0931004ff7650931004fe7650931004fc7650931006bf645093108ebc6450931005df735093103ddc735093100cfc764c931005bf744c931005bc744c931006bf644c931006bc644c931006ef624c93100eec624c931005f7714c931005f4714c93103cfe76d053103cfc76d0531006bf64d053108ebc64d053103dde73d0531005dd73d05310f57e75905310057d7590531006bf649053108ebc6490531004fd765053103cfc7650531005df735053103ddc73505310f57e758c5310057d758c531006bf648c531006bc648c53103df6718c53103ef7618c5313975e758c5310075d758c531396df658c531396dd658c5310079f648c531206de648c531206dc648c5310079c648c5310069c648c531006df628c5313975f528c5310075d528c53103dde718c53103edf618c53103fd7618c531005dd708c531006bf64d8131006bc64d8131004ff75d8131014fe75d8131004fd75d8131014fc75d813108cfe74d8131004fd74d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131005be7498131005bd7498131006bf6498131006bc6498131006fb60981310057f75581310f57c7558131005bf7458131005bc7458131006bf6458131006bc6458131005ef72581310edec7258131006bf6418131006bc64181311bedf631813101efa6018131006f96018131004ff7559031014fe7559031004fd7559031014fc755903103ebf7459031006bf5459031006bc545903103cfe735903103cfc735903103edc735903103cdc735903103ebe435903103ebc435903103edc435903103e9c4359031004ff725903100cfe725903100cfc72590310067f525903103edf3259031004ff705903101cfc705903103ddd76d0c312fedd76d0c312fddf75d0c3138ddd75d0c3103dde74d0c3103f9e74d0c3103edf64d0c312fedd64d0c31005dd72d0c312cede62d0c3103edc62d0c313875f52d0c31005dd71d0c31206de61d0c3103fd661d0c311b5de70d0c31004ff7558831014fe7558831004fd7558831014fc7558831004ff745883108cfc745883103eef72588310d67f525883103eef325883103eec32588310d6ec2158831004ff705883101cfc70588310d6ef20588310067f76548311767e76548310067d76548311767c76548311767f645483121e7e64548310067d64548311767c64548311775e73548310075d73548311067e63548310075f43548311775c43548310d57f72548310df6f72548310d67f625483100e7e62548310d67d625483100e7c62548310d75f32548310fe7e61548311775f31548311777631548311777531548310d76c21548311667e60548310d76f205483108cff76d
  | 21 => 0xe53d9131006bd53d913133ebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d91310063f52d9131006be52d9131006bd52d9131006bc52d913133ebf32d9131006be32d913133ebc32d913133ebf71d9131006bd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d913133ebf31d913133ebc31d9131006bf21d9131006bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d913133ebf30d913133ebc30d9131006bf20d9131006bc20d9131006bf6499131004ff7559131014fe7559131004fd7559131014fc7559131006df7359131004ff725913100cfe725913100cfc72591310067f5259131004ff7159131006f77159131004ff705913101cfc7059131004fe761913108ebe6419131006bd6419131005be7619131006be7619131004be7619131006bf6519131006be6519131006bd6519131006bc6519131006be6219131006bc62191310073f5219131337b73119131337b4311913108ebf751913108ebe751913108ebd751913108ebc751913108ebf731913108ebe731913108ebc7319131006bf5319131336be5319131006bd5319131336bc531913108ebf721913108ebe721913108ebd721913108ebc7219131006bf52191310063f5219131006be5219131006bd5219131006bc5219131336bf3219131006be3219131336bc321913108ebf711913108ebd7119131006bf5119131006be5119131006bd5119131006bc5119131336bf3119131006bd3119131336bc3119131006bf2119131006bc211913108ebf701913108ebe701913108ebd701913108ebc7019131006bf5019131006be5019131006bd5019131006bc5019131336bf3019131336bc3019131006bf2019131006bc2019131004fe76d0d31006bf64d0d3108ebc64d0d31005f671d0d31005f571d0d3108cfc7650d31006bf6450d3108ebc6450d3103f9c4350d31005f77150d31005f47150d3100cfe76d8931006bf64d8931006bc64d89310eeee62d8931004ff75d8931014fe75d8931004fd75d8931014fc75d893108cfe74d8931004fd74d89310ee7f52d89310eeee52d8931006ed52d89310eeee32d893103cfd71d89310eeef21d893101cfe70d8931004fd70d89310eeec20d8931005bf7458931005bc7458931006bf6458931006bc64589310eeec62589310067f76549310067e76549310067d76549310067c76549310067f64549310073f64549310063f645493121e7e64549310067d645493121e7c64549310073c64549310063c64549310075f73549310075c73549310ed7f72549310f76f72549310ee7f62549310076f62549310066f625493100e7e625493100e7c62549310ef6c625493100e6c6254931177773154931
  | 22 => 0x4a3100e7c6254a310d67e6154a31177773154a310ff6c2154a311667e6054a310ff6f2054a3108cff76d0a31004fe76d0a31004fd76d0a312a67e65d0a310067d65d0a3108ebc64d0a312079f43d0a3100eee62d0a31006ed62d0a31004ff7650a31004fd7650a31004fc7650a3129e7e6550a310067d6550a31005df7350a3103ddc7350a310079f4350a31005dd76cca3103edd76cca3103ddf75cca313c5dd75cca313bf5e65cca310075d65cca31205de74cca3103ddc74cca31006df64cca31006dd64cca3100ede62cca3100edc62cca310ff5f52cca310ff5d52cca31005dd71cca3103fd661cca311bdde70cca3100cff764ca311167e654ca310067d654ca31005bf744ca31005bc744ca3100eee624ca31006ed624ca31005f7714ca31005f4714ca310fddf764ca3100edf764ca3100cdf764ca313b5df754ca313b5dd754ca313af5e654ca310075d654ca310079f744ca31205de744ca31205dc744ca310079c744ca310059c744ca31006df644ca31006dd644ca3103ddf724ca3103fcf724ca3100ede624ca310ffce624ca31007cd624ca3100edc624ca310ff5f524ca310ff5d524ca31005df714ca31007d7714ca31007d4714ca3103ede614ca311bddc704ca312767e65d06310067d65d063103cfd769063126e7e65906310067d659063103dde7390631005dd73906310079c4390631005dd76cc63103edd76cc63103ddf75cc6313a5dd75cc63139f5e65cc6310075d65cc631205de74cc63103ddc74cc631005dd72cc63139f5f52cc6310075d52cc63103fd661cc63139fd651cc63139fd551cc6311bdde70cc6310e57e75d82310057d75d82310067e65d82310067d65d82310067e65982310067d6598231006fb60982310067e65582310067d6558231004ff7558231014fe7558231004fd7558231014fc7558231004ff745823108cfc7458231006de5358231006dd5358231006df4358231006dc4358231004ff725823100cfe725823100cfc72582310067f52582310067d5258231006df3258231006dd3258231006df31582310e57e75182310057d75182310067e65182310067d6518231005be7418231005bd74182310fdee7218231005ed721823101efa6018231006f96018231004ff75d9131014fe75d9131004fd75d9131014fc75d9131006bf54d9131006be54d9131006bd54d9131006bc54d913100cfe72d9131004fd72d913100cfc72d91310067f52d9131006be42d9131006bc42d913101cfe70d9131004fd70d9131006bf65d9131006be65d9131006bd65d9131006bc65d9131006be62d9131006bc62d91310073f52d913133fb731d913133fb431d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d913133ebe73d9131006bd73d913133ebc73d9131006bf53d913133eb
  | 23 => 0x67e32596313f67c32596310e67f71596313f67e71596310e67d71596310e67c71596313f67f31596310e67e31596313f67c31596310067f21596310067c21596310067f70596310067e70596310067d70596310067c70596313f67f30596313f67c30596310067f20596310067c20596310e57e75d92310057d75d92310067e65d92310067d65d92310fdee72d9231005ed72d9231004ff75d9231014fe75d92310067e75d92310147e75d9231004fd75d92310067d75d92310047d75d9231014fc75d923100cfe72d9231006ee72d923100cee72d9231004fd72d9231006ed72d9231004ed72d923100cfc72d92310067f52d9231006f671d923101cfe70d9231004fd70d92310067e65992310067d6599231006bf649923108cff76592310067e65592310067d6559231004ff7559231014fe7559231004fd7559231014fc7559231006bf7459231004ff725923100cfe725923100cfc72592310067f5259231006be4259231006bc4259231004ff705923101cfc70592310e57e75192310057d75192310067e65192310067d651923108ebe6419231006bd64192312de7e65d0e310067d65d0e3108ebe64d0e31006bd64d0e31005f671d0e31005f571d0e31205df75d0e313eddd75d0e313e75e65d0e310075d65d0e3103dde74d0e31206df64d0e312079e64d0e31206dd64d0e310079d64d0e31005dd72d0e312cede62d0e312cedc62d0e313e75f52d0e31207d671d0e31005dd71d0e31207d571d0e3103ede61d0e311bdde70d0e3108cff7650e3113e7e6550e310067d6550e3108ebe6450e31006bd6450e3103f9c4350e31005f77150e31005f47150e31005dd7610e3103edd7610e3103ddf7510e313dddd7510e313d75e6510e310075d6510e3103f9e7410e31206df6410e310079f6410e310069f6410e31206dd6410e312079c6410e31005dd7210e31126de6210e31126dc6210e313d75f5210e313cf9e4210e312079c4210e31005dd7110e3103fd66110e311bdde7010e310e57e75d8a310057d75d8a310067e65d8a310067d65d8a31005be74d8a31005bd74d8a310feee62d8a3100cff7658a310e57e7558a310067e6558a310067d6558a310feec6258a31004ff7558a31014fe7558a310067e7558a310147e7558a31004fd7558a310067d7558a31014fc7558a31004ff7458a3108cfc7458a310fe7f5258a310feec4258a310feee3258a3103cfc7158a310feec2158a31004ff7058a3101cfc7058a310feef2058a310057f7654a310067f7654a310047f7654a310067e7654a310057d7654a310067d7654a310047d7654a310067c7654a310067f6454a3121e7e6454a310067d6454a310075e7354a310075d7354a310ee7d6354a310075f4354a310075c4354a310fd7f7254a310e76f7254a3100e7e6254a310fe7d625
  | 24 => 0xe7498532005bd7498532006bf6498532006bc6498532006f76198532005bf7458532005bc7458532006bf6458532006bc6458532006bf6418532006bc6418532006f56118532004ff7518532014fe7518532004fd7518532014fc751853208cfe7418532004fd741853203cfd72185320d67f52185320d67d5218532006f65118532006f551185320d6f5211853201cfe7018532004fd7018532006bf64d8132006bc64d8132004ff75d8132014fe75d8132004fd75d8132014fc75d813208cfe74d8132004fd74d813203cfd72d81320b67f52d81320b67d52d8132004fe71d8132004fd71d81320b6fa20d8132005be7498132005bd7498132006bf6498132006bc6498132006fb60981320057f75581321157c7558132005bf7458132005bc7458132006bf6458132006bc6458132005f77158132005f47158132006bf6418132006bc641813201efa6018132006f96018132004ff7559331014fe7559331004fd7559331014fc755933103ebf7459331006be5459331006bd545933103ebe435933103ebc4359331004ff725933100cfe725933100cfc72593310067f5259331004ff705933101cfc7059331004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3108cfc7458b3103eef7258b311067f5258b31106ee5258b31006ed5258b31106ee4258b3103eef3258b3103eec3258b3103edc3158b31106ef2158b31004ff7058b3101cfc7058b3103edf3058b31106ec2058b310067f7654b311767e7654b310067d7654b311767c7654b3121e7e6454b310067d6454b311767c6454b310075f7354b311775c7354b311057f7254b3110f6f7254b311067f6254b3100e7e6254b311076e6254b3100e6e6254b311067d6254b311776d6254b310066d6254b3100e7c6254b311076c2154b311667e6054b311076f2054b3108cff76d0b3103cfe76d0b31004fd76d0b3108ebe64d0b31006bd64d0b31004ff7650b31004fd7650b3103cfc7650b3108ebe6450b31006bd6450b31005df7350b3103ddc7350b3100eee6250b31006ed6250b3103dde73d0731005dd73d0731004ff7558331014fe7558331004fd7558331014fc7558331004ff745833108cfc7458331004ff725833100cfe725833100cfc72583310067f52583310067d525833103efb705833103efb305833103ef830583310e57f76596310e67f76596310147f76596310e75e73596310075d73596310057f72596310067e62596310067c62596313f77731596313f77431596310067f74596310067e74596310067d74596310067c74596310e67f73596313f67e73596310067d73596313f67c73596313f67e43596313f67c43596310067f72596310047f72596310067e72596310067d72596310067c72596310067e42596310067c42596313f67f3259631
  | 25 => 0x9132146bd20d9132146bc20d9132006bf6499132135dd73991322cedf63991322cddf7359132004ff7559132014fe7559132004fd7559132014fc7559132006df7359132134ff7259132006ef72591321367f52591321367d5259132004ff7159132004fc7159132004ff705913201cfc7059132144fe761913208ebe6419132006bd6419132126df6319132145be7619132006be7619132144be7619132006bf6519132006be6519132006bd6519132006bc65191321279d73191321273f52191321273d52191323ffaf32191321279e32191321279c3219132127ac321913208ebf751913208ebe751913208ebd751913208ebc751913208ebf731913208ebe731913208ebd731913208e9d731913208ebc7319132006bf53191323febe5319132006bd53191323febc531913208ebf721913208ebe721913208ebd721913208ebc7219132126bf52191321263f5219132126be5219132126bd52191321263d5219132126bc5219132126bf3219132126be32191321269e3219132126bd3219132126bc32191321269c321913208ebf711913208ebe711913208ebd711913208ebc7119132006bf5119132006be5119132006bd5119132006bc51191323febf31191323febc3119132126bf2119132126be2119132126bd2119132126bc211913208ebf701913208ebe701913208ebd701913208ebc7019132006bf5019132006be5019132006bd5019132006bc50191323febf30191323febc3019132126bf2019132126be2019132126bd2019132126bc201913200cfe76d0d3200cfc76d0d32006bf64d0d3208ebc64d0d322cedf63d0d3200dee72d0d32005ed72d0d32125de7690d3203ede7690d32124de7690d32135dd7490d321479f6490d3208ede6490d3208edc6490d320079c6490d3208e9c6490d3200dde7290d3200ddc7290d3203edf6290d3203fcf6290d321475f5290d321475d5290d321479e4290d321479c4290d32005de7190d32005dd7090d3208cff7650d3200cfe7650d32134fd7650d3200cfc7650d32006bf6450d3208ebc6450d3203f9c4350d32005ef7250d3200dec7250d3200ddc7650d3208edc7650d3200cdc7650d3203ddf7450d3203f9f7450d320079f6450d3208ede6450d3208edc6450d320079c6450d3208e9c6450d32007cf7250d3200dde7250d3200ddc7250d32137cc7250d3203edf6250d3203fcf6250d321375f5250d321375d5250d321379f4250d321379d4250d32005dc7150d32005df7050d32006bf64d8532006bc64d8532004ff75d8532014fe75d8532004fd75d8532014fc75d853208cfe74d8532004fd74d8532106dd73d853203cfd72d85321067f52d85321067d52d8532006f651d8532006f551d8532106f621d853201cfe70d8532004fd70d85321157e75985320057d7598532005b
  | 26 => 0x14fe7559332004fd7559332014fc755933203ebf745933200cfc735933203ebe435933203ebc43593321367f52593321367d5259332136bf4259332004ff7159332004fc7159332004ff705933201cfc705933203ddf7650f32006df7650f322ccdf7650f3203f9f7450f3203f9f6450f3208ede6450f3203edc6450f3203f9c6450f3203e9c6450f3200dde7250f3200ddc7250f321375f5250f321375d5250f321379f4250f32005dc7150f32005df7050f32004ff7598732014fe75987320067e75987320147e7598732004fd75987320067d75987320047d7598732014fc759873208cfe7498732004fd749873200cfe73987320fe7f52987320fe7d529873203ef6719873203ef7319873203ef431987320fef5219873201cfe7098732004fd7098732004ff7558732014fe7558732004fd7558732014fc7558732004ff7458732006bf7458732004bf745873208cfc7458732006bc745873208cbc745873200cfc735873203edc735873200cdc73587320ee7f52587320ee7d525873203ef7715873203ef7315873203edc315873203ef431587320eef62158732004ff705873201cfc705873203edf3058732004ff75583320067f75583320047f7558332014fe7558332004fd7558332014fc75583320067c75583320147c7558332004ff745833208cfc745833200cfc73583320967f52583320967d5258332004ff7158332004fc715833203efb705833203efb305833203ef83058332096fa205833208cfe76d9132004ff75d9132014fe75d9132004fd75d9132014fc75d9132006bf54d9132006be54d9132006bd54d9132006bc54d913203cfd72d91321467f52d91321467d52d9132146bf42d9132004fe71d9132004fd71d913201cfe70d9132004fd70d913208cbe76d9132006bf65d9132006be65d9132006bd65d9132006bc65d91321479f73d91321473f52d91321473d52d9132407af32d91321479e32d91321479c32d9132147ac32d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132146bf73d9132406be73d9132146bd73d9132146bc73d9132006bf53d9132406be53d9132006bd53d9132406bc53d9132146bf72d9132146be72d9132146bd72d9132146bc72d9132146bf52d91321463f52d9132146be52d9132146bd52d91321463d52d9132146bc52d9132146bf32d9132146be32d9132146bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d9132406bf31d9132406bc31d9132146bf21d9132146be21d9132146bd21d9132146bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d9132406bf30d9132406bc30d9132146bf20d9132146be20d
  | 27 => 0xd7110d521276c2110d521657e7010d520057d7010d521276f2010d521757e73d85520075e73d85520055e73d85520057d73d85520075d73d85520055d73d85520067e63d85520067c63d85520157f72d85520157d72d85524676d72d85524567f62d85524676f62d85524577621d85524577521d85524576c21d85521657e70d85520057d70d85524576f20d855245d7d76985521757e73985520075e73985520055e73985520057d73985520075d73985520055d73985524457d72985520076d72985520c56d72985524467f62985520cf6f629855243d7e71985520067f61985520077761985524476c21985521657e70985520057d70985524476f20985520057f73585521757c73585520067e63585520067c635855245d7f72585520076f72585520cd6f725855245e7f62585520c76f62585520077761585520067e615855245f6c21585520057f70585521657c705855245f6f20585524557e76185521757e73185520057d73185520157f721855244f6f721855200d7e72185520157d721855200d7c721855243e7f621855244f6f62185524457e71185520067f61185520077661185520067d611855200775611855200675611855243f76211855243f75211855243f6c21185521657e70185520057d701855243f6f20185521757e73d81520057d73d81520157f72d81524376f72d81520157d72d815241e7f62d81524376f62d81520057e71d81520057d71d81520067f61d81520067d61d815241f6c21d815241f6f20d815241f7a20d815241f7920d81524257d76981521757e73981520057d73981520067e63981520067c639815242d7d72981521676d729815206d6d729815216e7f62981520776f62981520057e71981520057d71981520067e61981520067c619815242f6c21981521657e70981521667f60981520077b60981521676f20981520057f73581520075f73581520055f73581521757c73581520075c73581520055c73581524257f72581520076f72581520756f72581524267f625815206f6f62581520057f71581520077771581520057771581520057c71581520077471581520057471581520067f61581520067d61581524276c21581520077b60581521667e60581524276f205815241d7e76181521757e73181521675e73181520055e73181520057d73181521675d73181520055d73181520067e63181520067c63181520157f721815200d7e72181520157d72181521676d721815200d7c721815216e7f62181524176f62181520057e71181521677671181520057671181520057d71181521677571181520057571181520067e61181520067c611815240f6c21181521657e70181521667f60181521677a60181521667d60181520077960181521676f20181521677a201815240f792018152004ff7559332
  | 28 => 0x8443004fd7558443014fc7558443004ff725844300cfe725844300cfc72584430067f525844303ef7715844303ef7315844303edc315844303ef43158443004ff705844301cfc705844303edf3058443004ff75580430067f75580430047f7558043014fe7558043004fd7558043014fc75580430067c75580430147c7558043004ff725804300cfe725804300cfc72580430067f5258043004ff7158043004fc715804303efb705804303efb305804303ef8305804321d7e74d8d520057d74d8d520157f72d8d520157d72d8d524867f62d8d524976f62d8d524875f32d8d524875d32d8d520057e71d8d520057d71d8d524876c21d8d521657e70d8d520057d70d8d524876f20d8d5248d7d7698d5221d7e7498d520057d7498d5246d7e7398d521767f6398d520075f6398d520065f6398d5247d7d7298d521776d7298d521156d7298d5247e7f6298d5211f6f6298d520057e7198d520057d7198d5247f6c2198d521657e7098d520057d7098d5247f6f2098d520057f7458d520073f7458d520053f7458d5221d7c7458d520073c7458d520053c7458d520075f6358d521767e6358d5248d7f7258d520076f7258d5211d6f7258d5248e7f6258d521176f6258d520057f7158d520057c7158d5248f6c2158d520057f7058d521657c7058d5248f6f2058d524857e7618d5221d7e7418d520057d7418d5247d7e7318d521767f6318d521775e6318d521767d6318d520075d6318d520157f7218d5200d7e7218d520157d7218d5200d7c7218d5246e7f6218d524776f6218d5246f5f3218d5246f5d3218d520057e7118d520057d7118d5246f6c2118d521657e7018d520057d7018d5246f6f2018d521757f7690d520057e7690d520057d7690d521757c7690d521357d7490d520073f6490d520073c6490d521257e7390d5221f5f4390d521457f7290d5200d7e7290d521457d7290d5200d7c7290d521467f6290d5214f6f6290d521473e4290d521473c4290d521475f3290d520057e7190d520057d7190d521476c2190d521657e7090d520057d7090d521476f2090d520057f7650d520057e7650d520057d7650d520057c7650d521773e4350d521357f7250d520076f7250d520056f7250d5200d7e7250d5200d7c7250d521376c7250d5200d6c7250d521367f6250d5213f6f6250d520057f7150d520057c7150d521376c2150d520057f7050d521657c7050d521376f2050d521757f7610d520057e7610d520057d7610d521757c7610d521457e7310d520075f6310d521775c6310d521775e4310d5221f5d4310d520071d4310d521257f7210d5200d7e7210d521276e7210d5200d6e7210d521257d7210d521776d7210d520056d7210d5200d7c7210d521267f6210d5212f6f6210d521275e3210d521275c3210d520057e7110d520057
  | 29 => 0x3ef8305824300cfe76d8943136ee62d8943004ff75d8943014fe75d8943004fd75d8943014fc75d894308cfd73d89431367f52d8943136ee52d8943006ed52d8943136ee32d8943004fe71d8943004fd71d8943136ef21d894301cfe70d8943004fd70d8943136ec20d8943136ec6258943004ff75d8543014fe75d8543004fd75d8543014fc75d854300cfe72d8543004fd72d854300cfc72d85430067f52d8543006f651d8543006f551d854301cfe70d8543004fd70d854313d7e75985430057d7598543135ee7298543005ed7298543006f76198543006f56118543004ff7518543014fe7518543004fd7518543014fc7518543336be43185432fedc431854300cfe7218543004fd721854300cfc72185430067f5218543006f65118543006f5511854301cfe7018543004fd7018543004ff75d8143014fe75d8143004fd75d8143014fc75d8143316be43d8143326dc43d814300cfe72d8143004fd72d814300cfc72d81430067f52d8143004fe71d8143004fd71d8143006fb60981430057f755814313d7c7558143005ef7258143135ec7258143005f77158143005f4715814301efa6018143006f9601814303f9f7650c4303d9f7650c430069f7650c434af9f7550c434a79e7550c434af9d7550c434a79c7550c4303f9f6550c4303f9e6550c4303f9d6550c4303f9c6550c430079f7250c4349f9e7250c431259e7250c430079d7250c4349f9c7250c431259c7250c4303f9f6250c4303f9e6250c4303f9d6250c4303f9c6250c434a79f5250c434a71f5250c4349f9e5250c434a79d5250c4349f9c5250c430079f7150c430079e7150c430079d7150c430079c7150c430059c7150c4303f9f6150c4303f9e6150c4303f9d6150c4303f9c6150c434a79f5150c434a79e5150c434a79d5150c434a79c5150c4349f9f2150c4349f9c2150c430079f7050c430059f7050c430079e7050c430079d7050c430079c7050c4303f9f6050c4303f9e6050c4303f9d6050c4303f9c6050c434a79f5050c434a79e5050c434a79d5050c434a79c5050c4349f9f2050c4349f9c2050c43004ff7558843014fe7558843004fd7558843014fc755884303ede435884308edd43588430069d435884303cff725884303eef72588431267f5258843126ee5258843006ed525884303eef3258843126de325884303edc325884303eec3258843004ff7158843004fc715884303edc3158843126ec2158843004ff705884301cfc705884303edf3058843126ef2058843004ff7598443014fe75984430067e75984430147e7598443004fd75984430067d75984430047d7598443014fc759844300cfe7298443004fd729844300cfc72984430067f529844303ef6719844303ef7319844303ef4319844301cfe7098443004fd7098443004ff7558443014fe755
  | 30 => 0x20004001000c00200000000008005001400600000010000000000000f0004000000400200300020008001000c00000000010000004000000000000070000000000c0000000005000800000040000000000000000300180000000002000000000000000000001000c0000000002001c0000014005000000000280000004003000c0000000001000400000080000010000000c00100000020004000000000b00040000010000000000000000000008000000c0070014005000000100080030008000001800000180040000000000800100200000004000000000100080020000000000001a001c00000000020004000001000100000030020000000c00600000000000000000400500040000000000000400f00080060008001000000000000010000001000c00d005800100080010008001000c000000000500040000008000000c002000000100040000000000000c006000000300000010004000000000000000000004004001c00000040000018001000400100180020010000000000800180060020000000c00200180010004002000400000040010004000001000400080000004001000000100040020000005000c002002800000000000000000000800200000060000002000000000000010000000000400100000020004002001000100040030020000000c0010004000000000100000010000001000400300240000004002000000000000010000003000800100040000000002001000000040020004000000c00400000000000006001c00200000000000002000000a00000000000000000000000100080004002000000100000020000001000c00a000000000000010018000000400200080010000000000c0020000003000c002004ff7558a43014fe7558a43004fd7558a43014fc7558a4303cfc7358a4303ebf4358a4303ebd4358a4303eef7258a431467f5258a43146be4258a43146ee4258a43146bc4258a4303eef3258a4303eec3258a43004ff7158a43004fc7158a43004ff7058a4301cfc7058a43004ff7598643014fe7598643004fd7598643014fc759864303cfe7398643206df439864303edc439864300cfe7298643004fd729864300cfc72986430067f529864303edf329864303ef6719864303ef7319864303ef4319864301cfe7098643004fd7098643004ff7558643014fe7558643004fd7558643014fc755864303cfc7358643004ff725864300cfe725864300cfc72586430067f525864303ef7715864303ef7315864303ef43158643004ff705864301cfc7058643004ff7558243014fe7558243004fd7558243014fc755824303cfc735824322edf435824303edc4358243004ff725824300cfe725824300cfc72582430067f525824303edf3258243004ff7158243004fc715824303efb705824303efb3058243
  | 31 => 0x2000000100040020004002000c0010004008000000600080020028000000400800080000008000000800200000010010001000000a00000000018000000401100080030000003001000a000800100000010000000001000000040000000000000000500000010004008003c00a000000000000000000000000400000080030000007000800400000000000003000000300500050008004002800000000020000000002c00200040000000000000400700100000000002001000100080010004000001400600080060008004000c00300040000000002000000200000000000003003400000180060014000000000000040020008000001000500000000000000002000100000000008000000c00200000010048000000000400000000004002000000f001c0040000001000400200000000000000001000100040000000000000400100000000004003003000000000010004002000000500000020004000000000100000030000000000000100180000000000000c0060000000000c00000080070004000000c00000140020000000000c0000004002000000000080010008005001c00000000010000000000800000040020000005001000100040010008004003400300000010000001000c0060000004000000100040070000008000000100040090008001000000000040010000000001800000000000000000000000300000000004000001400000000020000008000000100040000000004000000a00040010008001000000000140000004000000800100080020000001000c00000000000008000000000f000000100000030024002001000200000060008003000000600000040008000000400000040070008000000c000000c0010004002000c00300000020008003000c0000000004000800300000000020000000400500000050000003000400200080010008002001800e00080010000009005400000040020000009000c001000800000000020000004000000300240000000001000400000000020000007000000000000030008004000c000000000000000020000003000c0000018007005400800000050000000003400000000000000001000000600100000000003000000500000050000000000000b000c000000800000040050004004000000200140000000000000800100000010008005000400100000000000001000000200000000010000001000600000000000002000400c000c0000008001003800d0008002000c000002c0000020000000000000080000000000000c003000400300000010008000000000200000020000000000000000000040000000000000200140000004000000000300040020000001000400a00000020008000002000100040000000000000c002000c000000400100000010000000000000
  | 32 => 0x10000000001000000000010004005000000100040050004000000800300000000008001001400100080000014000000000100000000000000000c000000000000040000000000000c001000400100080000000001001400000040090000000001000000040000004000000000800040030008004007c000000c00100000010004000000400100000040000002001400100080000000003000c000000000100000030000003000c0000014000000400000000010028002003c003000800300140040004006000c002000c0010000000000400000040080004000000c000000000600140020000000000000000000050008002000c0010004002000400000040020014007000c000000000000000000004001000000200040090010001001c0000000002000000500000000000002000000000040000004000000c001000000100180020010000000c00300300030020000003000000000050000000000000000140030008000001000400040030000000001400200000010000003000800900000060004006000800100000040000002000400200200060004000000000200040000000003000c00c0004002002c0030000000000400000000000000000000000000040030000000000400100000040004000000400300140050000000000c000000800200000010004007000000300000000000000000000200000000014001000000500000000000001000000700180010000000000c001001c000000400000000000004001000000200040020004000000000100040010000000000000100080000000001001400100000040000008000000000000000000000000000d000c0010000001000400000000000010000000000000040030014000001000a0000002000c00300000010028003000000200040000004001001c000002800100040000000001000000100040040004003000c0070004000000000000000000000006001400900000000004002003c0060000000000400100000010000001000400200080010004007000c00300000010000000000401000000010000000004c0000000000000400100000000000005000400100040010000000001c00200000020004000000c00300000000000002000400000240000000000005800a00000010000000000000000080000008000000800100040030008001000800100000040000000000400500080000004002000000800100070000000002000000000020008000001400100000000000000000000000000000000002000000a000000100080010010000000000200280000000002003c00100000000008000000400000040010010001000c004000800500040000000001001400200180020000002000000000000030008000000800000000040000000000000000080000000000000800100
  | 33 => 0x26c19022980000000000000096000000007a05f377a1134400000001a28000a1e0000664800000026f600000000000000000000000021560001f0600026280000000000044200022f24e980009fb94da20815aa000000000023c2000154a7d7d91b03803f4000000067f9be660e0000000000000002a20000000006e1e600014ef1bf000050c9a422e406160c7c000498800051bc00041505640d2a4ce93f81e67db1914756cd467a1c0001210000000000000000007b2c00000000000000d8086c278a00000006e8800000022082b507240972142000277a00000009f080000000000000189600017260000956000174c000129a4aa00001ad00006408000958000000007aa00006e2000228205624f0576a4e250583c7928155e8f31adf2fda46d547800024a89066af9ff20000a6a4628000000000039819a000040000004000000400000000000000000000000000040020008002001c008000400100080010000001000000000040000010001000000b00080050024000000400100000000004003002400000080000000000001c004000000000040010000003000800600140030004001000000a000400000240010000001000c00600040000014000000400100100040004000000000000000000008002000000e0008000001c0090000002000000500080000008002000800600000000000003000000800000050000001001400c0004002001400000000000000000000800100000010008000000c000000000100040000014001000400000000050000000001400100000000004004000800500140010004005000000c00040000004000000000100000010018001000c00200000060038001000800000000010000000000400100180000000001001c000000000000000030008003000400300040030004008000000b00100020008002000000300040000000000000000000040030014002000000100040000000007002c00500180000004002000800000000000000000000000600000000004004002c0020004000001000700140030004000000c0040000000000000100040080000001000000400000040008001001800800000000000004001c003000000100040010000004000c000000800000000020020005000400500140010004005000c0000004004000400200040030000001000800000040050024002001000500000050000009000000000100040024003000c000000000000140000000000000400100000030008000000c000000c004000000500000010000000001c00a00040050010000000000000000000000000001c000000c0010000001000c0000010006001000000000000004001000800300000000020001001c00000040020000004001c000000000200040010008000000400600000020010000001c0
  | 34 => 0x11100000fae00004da5c1066461f1b0a8f5183e0000000888800000000000270d7496c8c0036f985273c80007959d3e37900000000000000237a00000000000000000029600027c044785782ea8000000000036200002460cac3850000669a110392a01a000185e466d7ec956a6ec00008ca000052c0000000000000087ac1c200200006f605ca7e480000001744742a19e0001e642e2922400004a64868ab300020dc0000000981800014b80006ae000000000000000000000000000000003318000000196e00022dc92f80005c600005180000000000082e000000000000000db0868067e00000006a1124e00019d28719d169b48ebc5d2961e0001664000000000000003df5dd00000000000000000000002b795f800005fa000000016dc0000000000000000000019b489900002ac25790e1000058103143dec31a591a7c4000242c28500008aa12500fb800000022ae282823c00012da34a000000000007acc26877700007ce0000000015e00017ce00012c610f06080001f740bd9a6aa08800043d0398029000000000c0382000066e24d8153000000000000000000000218369e0000000000000000695e9000087780008a5a7b00000000000125d0000000946a1ce48a400000023b871c1a930748000739a71492193fa37524720000000000201800024767c48e580001e889cd00000000b1c0000000000000013d800095cc0001a1000005400004d40000000000000022ea9c700000001a7b3df10c6000000076c000000020ba0fb57d885a107a3819c4a3cb800038000662a596c000000009ea917800000004c680009ac000000000000000000949800094d16709730b3f82b800057ea78e92881286948932000000085e9b6884f8e5600007dc00024249ed0000000051400020f800000000000f509d280000001a480000000315128a3a300004a300008528000000000000000006de18d38d8251b2d784459fa562c7db91e603f0ed0000000000010dc0000000622800007e483006b880e48e000000016e648fa1ea00000006c38000000017858900008d58000631800000f1fd08330000000000064686b200020e0000000088a85bf45b800000000000f14000000000000024160001fec000204a50163ce00016b80000000000117200000000000000000000055210c20000000068800000000000001c14899a604000000000000009199d1200002d27700386752994830182b6000000000000000000000000119e59800004b60000000000020c91cc79f800024b400000816d40001b1c00015c09aa04ab00000005d902047d15928404877000012d69f221248d39fdc00000002218a3074f0bc400004860000000782c000000000051500001d4a76e000019a929800077600007e50000000000030889ee85aa2fe6580c3c0
  | 35 => 0x6e800005e300009fa94fa9641c5c3698000000000001240000000000664000000000000000000948000000000009b50000000000000000007ed0000000000098d1fae6741e80000000052b01b2000000027a00000515f6d0002010000000025c00001542728000000000000003fe98ca0ec000079ac24a00000000000000000000000012d4000000000003370d94000a18072671da2f46d0a2187228ef21d00c499f40636700879c585838e000000080b00000000c7600003d094a000023207540bb000079e000000d800000000002e3c00000000001fc800060a22c40d312660000e10000000000005b00000f9e17d8cc0735984c422998c0000df05c491e20001440273090d4d011ba0000ab6000000000000000001e2c16380004708d5200005c4562000010c1e6a116400093480000000c4500000000000000000000000015ba00000000000000000000087f8000803800000000000000c19000000047d8000000000000000000000f6e2c2000019387b830d9b44120c00022e000000000000001630000000000000003d494b40000000000145c7af80000840000000000048700006a3c000000000095c90344c2844e83900001fb00000001d70439800042980000f280000608000000009922b000000016dc52327d200027e253500000001f6a4408507460108600007ce000019e96f1df8189d67e00000000000000000000000000001a5800000000000000000000223a000000000000000000000134a80c2fa1c0419880002caa45648d89480001b5c00003d85ff8a3200023a8000000025500000000000000000000004b0000000000000006bd12000000b9c00002b47d6a68c8b98000873107e00014c4305000000015108e7a1961de096476081e43bb00002958000242c9e4000000000000007df800000000005aa181e5b808406b6e6820001ff4000000000019c26fc8000000000000000000000000393c0005080dce77913348d5000046226020000000000000095412fc07a820c69ca3b267e1bf40000000000000059e8fe82e480000001a2248c8000000000000017a0221000000000000000ec60001daa00000b00000000000000000000000001b167c69ac900009c80000a9f4921b7e3a103260000000000000087b9dfc84c00ef00004a40000c405429fd400020992079de683f161c0000000000115800000000000000000000000009fe00000001215da010505010001aec60891608fc80002a0000092608e0176800000005c200013880000000000000000000001c440000000000000000000012ee0000000372800000000004791d66715204009817a74a896800000000000000000026a479ba5681a01ede9d48b10000270400004aa000209c8bb800011dc00079f4e3493f120c38691de415890800026661e3801e90c80000000
  | 36 => 0x56e0d4a4fd000014a800000000009b200000001698048000000000000000fb2000000094f400000020549ba00003db04082bc80000000000094961200005097a680000001c722fa8000017842c2dc4000000000000000009ed80008208000916800005ca09d1354a84000000047ea1be00021862b107303c0a58693a000089d97420000000653258c385a4ac64200000d6800074da58833895983bea18210a00000001e2f30a9290000000000000000000c6455a80003a6167800000000000000000000000000000000000000000000000000000000000138e00000000001dea03c15380000c940000000951000024b0000000000015f0000134cf840001b8e18c80004d6839c00000009591a6400000009f380002c98b6c41b800000012a468f8000029c00062b800000000000000dec0000d6c8f7a56c00000008be00004c480001b113e414a05a69b888685f597720000000000000033da692000277000000002bf0000920a82a00019a2000000000000000000000000000000000008360000000000000000008160000000000031680000000000000000000002e487b0000000000049d9b126710000000000015000000000000000000014100000000000000000014e80000000000000000041ac97c00000008eb00000000000000000026f00000001c4634500008d7a55953c4723000059802100007269bde14d1e4223d9b5430596a683a9c600ca0da440315bc00022da3c340007489b4058322b8539115a62e962a000104600000007564e0a000217600000000000eb428f800064e16bc85d1ad676421909bdc000419a5fc000000000003aa00020ac00014e60000b7e000000029960c82be0000000000092e88e62410000000000000000000000494a14000000000009b40b73000000000000008260000000000057a000000000000d60000000000072093d455c9ff0000038c18800000cf0f6000006a0069c00057280000000986000000000000000000808000192636524f90000a4600000001c1238e15fa33c3dc1be8734800077b800000000000001eaa2d2152c08d800000016a28b3800001702aa869a654000000027e0000000232c3a7151c5fa0000000000037c800000017d20000000000000010b8000115c3a800007bc000053200000006fa80000000000000267e000226000000009a600003920fe4000000025f80000000a40502a5ea42a050a72c000090283009969f0a00019043e3810037686c08448000000169600000000000000019c0000000000000112a000000000000000df800000000000000e8200000000890366000000074e0000000000011800582d986fe71011d845e800000002e0177c000000277480b800000005a000023b0a19000095222505291eec59d8000000210c25e8000908000058b80000000000
  | 37 => 0x8315800006a81920001fc600008ec000063000000002d4000032286fb15c862460740006dc0db100005910000caea09800059b9996000000092d1f88000000000012ce1b48000840192c22b98e4000000090fc2421bf40005e200000001f32005c50321923c059706ac00000000000000000239400000000001c2b000160e0000e2a0000000000000091e009805d115653b82f22060000977006097ba3a6323800046100000000000000000000000000000000781800000000008e610ee25c8c0898c80000b318a237d8f969d0000019b9b0400001fc00000000000c5c00000000000000860169a589a30039f0000000000060c07c238780000a792fe2ee1ade7bd944e000192a00000000001f2c00000000000ca00000000000000002a034962380000000000000000000000007d499ee00000008a6800000018dc12ec0006fe063d0001234405247a000000055500000c38000a12800011a80000000000000207151d800046a80007ab1c86000041e4fd800000007960000000546000000000000000000000000000000000000ae00000000000000000000005340000a0114c00000a5800005e40000000357800000027328d2597000000000000000000000094b1028000108200001684af0d9e112998441898629c6800062f05e6000000000000006c780000001ad008600000002242000183a00019e21f815640000c801ae0d315e6000000000000000856701855400000003bd80007578e4653a8f5400000000000000000000042424fa615a49388495967a180001f284065758ad627781cf33d000027480003b30c7a000145200000000000ed84bd914a1e902d881c1b580000000000015a000000031b80008a31e2286395743c60000000000048b0000000062a0000000000000018280005910000000000000000346fd8f3c0000000000000000027fe94300000000000000000046c0000781c0005950acf4a5c00081d80003c2d5ea222000000000006030000000000000000000000000000000000000002450000000000088980000001ff80001aba410984a72880009f90000000238c00000006f6a7e00000000000000000000000000000363000000000007fa800000018f2433812221f8000000000056181bc92a14a2758000000000000000000000000000000001850ea200000000000aa80001aea00000000001f3e00028241a0800009513e6000000053314c82c8800000007d60c1800037e0000000133a4e08a60077000000000000329fa46e1248f000000000000009db15e088924b36af00c400000000001a140000000318000046d8f4a7e81cd400013680000648000249200004fa26d000000000008e925109402430000000002995fc00000002e58000000000000005880000ef00000000000000029687b000000000000000888
  | 38 => 0x4d300004b798760001f0e000283a9f5a05691110329179b3c0000000000177c0f98e383f81c5e0001ece7a306ea6b180f66ab000068d867666285ba7e680000000000000000000000000000000000097600000000001c9603a81645fd9e2e9ef0000000252100005ea74b80000000000840800000000000000000000000000014140001ec686d00000000e660000000000000000023928958132000000000000000000000000267a00000000000000000000000010fc97780003ea266a00000006aa0000000000000025b69a20000789230e3a50e9e97d000000000003dad41a00000009755e5a1a2000072f80000000000000179a000000000000008840870125c00000000008308000000000062fa57069056da9375a760001d18421220600000000cb9544931066626e15ee00010080001c5070581b86e40000000000000002a0000000000000000000456704027400023ee7d984ba5039d680001e1042d00000001ae600000aa000101a000090e000000000026a600000001e680000000bfe00019750000d1800000000000fa5000000087d00004ed807200000004b2864c0c80000952e0a000019796d19f5e106102e28f1bc88ac017d63f800024e5a38000208600000006a0000000013be135897820095c2a0f000000000001cd1d4400000003e8895c5ee0000000000085c89ca000129430f828c8a506650391dae2f3c00022392920000171733005600022e25f10a107c599be00000001f8800099c400000009d63910f283b800000000000000000000000005ad80003c480000001c8c0000000000160a0000000000000000000000000000000271200000005d8800000019ba0001bc500021264250000000121e000000045195e200023680c78fe2299ce2479780000ff00003d21dc29d1061951a00000001508000000030393a8000067f54080007cd000069100020000000000000000023e289e00002e080af45700000000be40000000000216c8299278162800067584501e0891a212125c3aa8dc80002577000000000026383608f7600000000000000924072e0dc8000885000049164527430b344bb0000388000000005fe000000021d000000026ca00000007c780004f780000000000000228400000007e11e38000000074d0000000000000000008c28000342971400000002b60bfa000000000000001d21a56000000075b075889c275e11a0000475137239b1540000155c94fa0d46e0a40c1a78a4c000000096a80004100000000000070b1c920002248000000093514e063501c600000000000000287000000000004194844000000050d8000000008500000005a0807a1c5172878687808079c6139a0a0409d42be6f95cfa00000000001e2000012aa0000000000092800000002c0a84e000116c7e5963661b06e
  | 39 => 0xb65b08ac8000000000000000000000000000000000009fd9c6f00007ae9e515c6000000000025f60001af08e70ae834aa5be00000005de870a777957c4e2800066600003c9000014e01c8000176576591242f34e5e000191e7668264549983684f170600005bc00004db0001a8a98f800000000000000000000000000000009868000000000020419b600000002e0c00072b0d1a00008c026100005fd00000002328000000000025d6388a64e37880000000000000000071900003f2141c15b194e31c9a9841c80008cd00009c290d603940006d68736000000000023242e7857f26480004470000000282c0000a501bd80003c200008cc00006429ffa00000000001fb081d000082316650001b300000f320f08000000000000000b873017780000000000000c000000096a000000002798f605333ff8000178800011b41126f4a36a000000000000000000000000008e000000000000002eb870f000083800014264668000658a608985a5c413280001c4a5b0000000000003de0001de807a17ee000134200010ae8a890100000ec27c40000000007f0918214738065c30e205008f80009fe070323695b23a8060e8149d5a93007e671592089c8866a0e417bc00013f10000e5268225740000000000246e00000006c9800023a8000000000068b80002c5851000000000000798713a6d861916ea805956c00000000000000000000012280006e180000000000974800000000003a2000000000001fe1a4c7ce428e1270000000212c0db80009105d6a000135e5dc000000004324b1060600000005a823068e2800019d00000000000000000000013167240c43000155a0002283a178b3085480008f98bf0000000000000004268000178126a00000888b925e864b80000000f5c9d90000000000000004e20000c6a3e7038f379a1d0219800020da51207d8000000000047b9392000131c0001dc40000b38776800014b400000000002d11cd0219d20221a587e0001c2804500000000ca24b0269726d98d200005f881b0701000000000000004a58000000000071e05f29cb00002ea18ea45a53aa11e016a1928000000000000004c030080003b78fa410c4000000000000000000001fd633e8fb617b046f29b1a2c0c9051688d800000021f20001846000087829d83b28ad000043880000000000000005a61098f800000000ce8000000202a2000000748023259a8000000020745980003d1000000000003ef000000013d83595efc0c418188f6800049e97e25ac00000000000000000028b80006f4016004da6680000cec00000007ef84960000000000000000005c0000000052a000089280000000000000000063b800000408a2000000000010220000cce0000000000000000000001b2124a0000000973dfc484d047a650d366a04951a085800000
  | 40 => 0xe4183434f1a122bc00000001f40945880500000009244e1c5d1800000000000001bca000012599c9eba146a6467419c9c3d7800091d00001f682dc66c114e0000000737263a000000019085c3509098a00e84cf3fb80000000000000153000016f00000000000000022f20b000000000001e50254800034b112e6be800000000000000c9a00000000001e4c56c00003ee00008cf8000871253f073259e00000001a691fe2c516f846940006cb800000003f29d8800032a133c0001aae000226c00014d8000000061c00000001e1600015320000000000185a0000000000000053e04ec0001418000000000000000000000000127c0000000000037814c00000ae972000000009f680000000000000000044e00005cb0000000000000000000000000033400000000000001dbe155a41e1c7c4e808e229f5aea4420000b04102a6604b889c257c00002a99e60000120b00000003af82a6620a150000000029c0000000000068980003d380009c315fe2fc9d489f9844c00000000000000000000041d800000011910001ed00001a820000000000000000000007c2000000021b18468000000000053ac74e00014a6760004c7c90b883119080660a66e49fa2c665a110e319834e4ee0c68067000052a916a9e707b4000149e7b21c2e57780000000000377000016e60b672e80000000bd200000000cd800031f1b4e00000000000000263800015197b28b780000001d280000000000000000000000000cb8000000028ea57e3c98000102400026680000728000000000089380000001ae069b0000000000000000009a890f06c300003628000000000000024690001dd6672800000000000000000969000e00000000000b3e0000000828800000000002b480008a92008a172380001000000000001d7960b20a9e8e55388a802407925ab0a4e5c9148a0001eea2bf806400000003320000000000000000000000000000277602e800000000000000000000000088680009b080007ff80000000000000226a0002344000000034440000f4968e69756110de8490000170a4cb0cd200000000002788000000000016c65e291f95cda7368a4000032f000000003c07bd00b6107206200000004f111b4249975a000264c00019589418a7c8c601da6e9228a0000000000105a00000008ee800093ec000306000000000007b51a1c7848e3f5959a5581f93a083280000000d6600016e2000000021080000b1951613212649fc400041200000001aca00000000000000000000005cc00081a80000001b2a0000000095800000000006388a680000a6465e000014146f9000000000000009b966243718db20000ff60000c9600021640000dd803786ee0000000046059c1871f28000063a000043e0001a8800000006929b186ca00001a900003420a08845273a16115
  | 41 => 0x8800000000000000004b000000000007189d76000000068a80007c8085978d00007ee0000000000047e1ee800000000000000953255e5f71bef4fc00000000000000000000009d40000000000000062d00004bc0000000000078526fa0001fac6c3445c00010379a4400000000000000cdc000000000000000000000000000093b8000000000069d000000004b30000166000271636ed27200000002e600000001fde710a3276230000000108c000093e00009206020d5a00011f28d6019626e800000008060000000000000000000000000000000000000014500001d261efa46f0000000000120a99018e621e80000000c0c516800003b17b42c9001288280000000adc000000000000004e1a547000194d0000346000044669659524619a1662d825800024ea1a1c47c2ad00004fb0000000000069f080b03303e80000000642685a000000000014e85698000000000029f627a1944000000000069e880c000257c00000005b5800000000007438000000000000006da9b78ea49fa0d448c5a5d4000188880d8000000158400020da000104e000000000000389551f482f20d68349994900008962dd856a000000020fc0000001878a0e0000000000000011ae0000000441136d2bd93480000000000000000026a0000264261500000001bac9b100000000000000000064e98c07728c2e0000000000006c000000090e40001a0400000000000000000000135c567808a94126b32620dfe0000000000000000020345d38000062a4da00000001f600003c300006f8a72e0000ec40000000496cace96b800000000000000000000000000000004e31ab4051c4cd00000000000bce0001bc2000000000000000001e1800000ee0e504740e7813a6db00000000000000000000001fd00008ee63810f60001c3e00025960000fa687a00004c9998681a00006c400006a801b90001f5783980000000000038d75e0050000a1f000000003327a280000000000000199e000207a00000007911fa174a85b200010ca297009260a800000000006bb9702000000033980007bf8000000000000000000000000174a8000001214264052600000004931b387e4d668000000000000007d31f5c04980006780000000076800000000000000000000000000000000000000000000000000001c6e1be00000a70000000278411b979c00000007822874643077c2818050000183f0002374754800044d80ae000000000005a80000ec03d8480900000000002308071000000005355599cc4252a6da0000e8a00000006960000000000000010be00000003188000000000015d80008cd80000000000000000000000000000fce000000000000000002060000000035b8552000035e0000000a1a17de1af239000000004fec0004951ef20000f0a0002540000057084625e25
  | 42 => 0xf691a62d90000335e7ec37100005a20f047b90000000000000000000001802000000000013546e722ec000000000000000000000000000000010da2ff00000000d4c00001a000000000000000809117e1f9000000000005b780000000f9200000002e8989e000000081e00007de0d701bc2286295204821f066c0000fbe0000000560843a0001c6c00000008670000000039a4739130544800015d200a2b30000000000000004ae04f082e00000003ce020100000002e0000000000005c31a240000000000260e00000000000000000000050045c823a000000022be000059e0000d5f90f9004347981253f80004f200009d5872c0000000405a0fa0000000000000000000000fe8e4e000026c0001d8a7699ae200019244f380005f083eb5108000000000000000005a78000000273c1288000000000000000000c48070000012700025e69210c88139096e98a867c26780008a9800000018604cb9cca6081d08227800000000000000000681845e2a28f140001b9a000164000005f000000000000000425975680e00000ee0000077a43d3ddc0000000000235000000005ae0001c1e5d9800082c8d32000191000000001b9240800000002e8c00025880007d380000001b4c23865320000000000000000015c48388000600270643a9a6340086ca40d95b491fa4f807947fe9181bfc1b5067b2c180000000000000000065d960336e9ce200000000000f6a0000000000000000017c822d0000000000044880000000f580000a0e000000019e973a0000000000000000000000000000000000079d8c9e2d48aae0000c9c0bd000034e800a0000000723800073d000017ac0007e9834831647e8427830c8dfa50a380921000026649949fce7ac19f27a7a7ac68a171e96384a34f9494460c94865cc835423588cc12c4fea00000000000000000279000003e4000000000000009c3800000000003098a9c0000d3600005c10000000000000000000000218000000077e3b3800050f18da5c9cdaa5630922247000070d800079380c74c825586700d61000201c9e618f10000000000039600014c60000000750000034709b005323b45439bec00013360001d7a00014b2321044491a095e5bc80007a9000081680003e41e705cc00005560c32000000000000009da98f637400001738da893f41d4181195d7ad99d8657982408c1c448c5234a16ee4220001e2a000153a000041600012f200660a87720000000244a01280000000000000000000000004e61bd42db9d5400026be0001ab04ac800000004820000000242400000000000000000000211e30ec00014be2621d68000596817e24e80004f293e200013144ed24140000d3f6aa40000000000051800000000009320000179550c1f30e0c137257571300000000000000000085b8ac20001
  | 43 => 0x8000000037c00000000000000000100a00002720001b2c000000077e800057b000000010e80001ac043b119600000000000e320c126ea000000057d05de4fe0000000000062a9aa4841a11c40a800059882a496700004681bae45a21ca00000008e580003fc00002b185a276520f076200000002699656a65e00000000000000000000080500009ef9e1c0000000000214c00000000001f5600019cc00000002aa800000000002cf06ff08807860000000000000073d9ae4494800017b4000000000029c80150001da233a0000580241a22480007b80000630800013f40009558000000037b000000053b000000012c8000215e0258000000051200000009fc8000000085c974000020580000d8000000000000000de000000000000000358d40c80980009d40000000206e000002c69025e436100007ad40004780000000000000000000001ba80000000000000017500006ec139e1980a332f080002ec0a2a389883a89ddf1400008768c4022a00015f69130f1c9aa827a00001a64961c6a9e90000000232e7ef00000000000000186800000006a680000000000843949c0000000000123c00001fe00000007e08000000000042616430eea00c00000f41fe800027c80008e68000000000000025d10001eb4000000093903d400000000000996718e5a200024581e10298000000000016f4000000088099500001c48000252e00000007570000000000000000000000000000169c000214400009e655c0a16000000095e83c88a719f40e8566617a1e403491f6806f9bbf000000089f8000633800087e8a1a000000000000000000000000147a23e800000000000000d2213c86ec0001a9c000000017311bc0000000000000038b00000000000823928000004d0987a83000025384f0129c32e80006dd00000000000000147447d000094701cd00019aa5ac9d309af0f642b1d0d00cc000045d04ac1c89f114651d720d4248e9e782e88b4000038c000051b0c470000000000287e00000006598e3c00025f8000011e0000d5c98c1be439a99ae85518bb6b5204600011e887840008080000000000044983c600013fc00000c262800005338000000000036e00000000000000084c9d6000091000002ee80005ed8000538800058e80002ce8000000286a000253c000000000014781d0800000019d400000000000c390000000621000000004ce000000022300000000000118a2b60001a8c0000dd20001db4000000000000008190000000000020900000000000000000000000002b90000000000000001629f5000000000000000000000000000015d0052c0000001bb80000000000083c7d1243b73c1ef80000000416428444ea8664b319e6000153c00000000000000000000006300008009fc8000021a62e40006970000000000000000001c40340
  | 44 => 0x8000000086b0000577000000001ac0001a548bc1a9961600005d81e660001fe60001c9e708057a1ab9092230908e3caa01200000000000fac98480008a380005af8e5b1ce00682d300000000f630001206384a2ca3664dae49a0656000000003c80003e6137a0000000815c000000256200024d092d8000000054e52e9d786a582ce38100000000862000000000000004f4800021780000000000000000058193c23f016aa000222e0408c304a100005fa80000108bdc0001154000000000000000000fb400000000001886000000060b069c749000045480000000000000048c0001ee6179c0fe0000000000000000025220001e6c05f0ff82138000000000000000000001260463117c000000000000000001c6b000000000000000000000000175805fdcde38742bc32da8805974000000047008e8a7e3ae80000001f7000000004d90b8c087800000013840000000000254e00000005c3400077480000000000000000056690b200005c65df800042e80000001c1c000159400000009379044000260a0000000000060000000009e480000c6c6c20f300000002104000000000014d20000ec5000000000000003cc000000000000000cda00002023310a980000000000000000000000001776000129e55fa68e72860886d580002408000306910006d01767c703883661e090b88f7a000000000007504f800009508035023d83d7a7018839526846aa8000242964814d87a66ad890c0001cb4317a67000003ce00000003ff00000e980005ff00009118bd02b24a3800000000000000576020a7028f1a18b260096509e2000000025980007af27a2000274c0000e180002502109035c4fc800000000000000000130800000000000001ace0000000000000000000009e18000048c0008f1d47000001499000a88763000068c00000000d7272200004428000000016c00006f400011c08f1537c887068e913a75a0000000000009e8f9079436d684c69816b459cd82e000240450e000000000e62c7800050080007c6000016500005078d4065f11623e21acb14c4bb200000000000e8600000000000bda3bf9dac6941f4a000000000002a8000000039d80001cc936e000000000000000001900000251d0000000466000000000000001cd800000008f183dc00000009d2000000000008fd08e46100000000000000024640000000740953600000008568000314843800012c28f11c3200000005a11da444487ba3230fb000000000d8c518687826204840000000000611580e7f880000000000000000071f800042700000000000971a26e0e81b9468400008dd8000014800000000004c400000001bba000070c70326ae00000007c9c0003299e36000000060584b4000144400000003b9000000000000da800000007d21a327a85bb82d60000000355
  | 45 => 0xbcd6484ea700302e5ec2b990686b700007338000000000000000000000000000000077886de0871f3c000168600003f0688000009d80008e8125e0eb850c8d7234689f24b54ad01e20000fc4000010600012e4356c00046421287e7095500013565130000000000000000000000000000000000000001305ae895162d671d40000000000000071a9ec930800000002eb1a8600000000000000000000059300000000000104000000000000f8275439c0cf097c91168ef000041280001c70000000125692e1134890400000016c826611b800012dc000000027d800024400000001b9662e00002c80000000000000024df5d4078c0000000000000000000005f913606405fe0821000026fa78c160d59c8b30ad002c8d7a89317748154000662000048c20447618278000000000000000000b5400016c400000000000000000184e5ab800049b8936000105c1860f8000000000001e7a64fdc08984104b8000b78956d0d200000000000000000076900004020000000310800000000006bd800000011d0000000000000003412320000000064380009b3800038a173c0000000000000018f0000000257600023641f0000061a800000000008be800032625ba9680000000000000008c40000e420001a3f06c00004f69ea24c384de13e21ae231a658000000000014bb5240000000000000018c88f2d22633ca140000000020100002831ca600000000001ba6000193c3c8a51400000006cd00001848d7c00000000000000000000050b16902af844837e852400000008d207646590ef873f8000298800000000001db0f5d000000058e000099f000000019547dae406909800000000004e59b9802ce40e3242448000000094908de000073e00010a200891c678ea05f000000027714ae0001fe8457dcb821c8000000000000016f6000000024f00008f2a36669a14621dc84880000af49b863420000e7e3f68cfe000000025300005b6000000000000001045651de2885fcf868fe80000000000000000042a8000000000000000000000e2e000000085f5ed2000000078319f01398000298c0009ce1fa200022ba136167444b04470a0000000022f627125496f0400000025368dc9ad9000163c0002362000000001f8951000000000004ff4bea50e0000000055995c39b827b0510000000000000012054ef0000000000044f9f267718000000187200000000000000842000000008dc4d3a27200005aa446146e0000000000000078c00000efc0000000a780000000954a59a3d5a7d8396863e3ad80000001bb4000000000028325ccc00040c00000000000000000033600000000000000005d23f8000000249464700006311f62000000000027685d000005da00004a0803e00019ec00000000000b4273f00007148a026c081e000014f40ce40000000fd
  | 46 => 0x920001fba000003068e8000000015260f0c09862c00000023f62d81528000000000005e90000000000000000013e800000000000dcc692400002c40002169c2100003447a51fc048f40006f1082873bc0005a480002a8800032089070000f342be84ea47440000000000481000022092be000000041900000000000000049a00000000000000047c00000020de00000001d2a6760438581a101cae4a8000052c000000000000000000000000000026d33e50000000000035d818400021d62b689fc000218a000151400000000000000000017508480000000000000026e0000c049d380003e8c000000000000000000000000309256e0571b4800008f2198e23c0000942686800000000002dc8940180881a82a8000000000076780007dea03e8fa800000012f8000000000000007aa0000000000000000000001a510000000691dac80c58aca00000000000000019400000021328ba000000022aa5e000000000000579800072d9d983c58f2c383a7240000e741ae8a9400021982a3193400000000001942000000094e9542a110000000000000000000430000000209a09200000000000000000033409ec000000075b800086d800012e048e114873c00005be0bf000000014826bf8f4c00000000b68d8632f8000127c00011f40000000000503e2fc959800000000004ab1c3480e80008580000000000000000000000000000248800000000001a7e0000000000000007e80620001d143b5800000000009c22806000000065293a225d002600000008614b463f4994578280000000000000000000015ac00000000001b3b0000000000247000004360000000a058c1744300000000000000059383121b24350c1287c1cc2280000687d8000000000000005b400000000000000013800033301a500000006ef00000000000000284836d84b21190000000102666c91ad00015004a98000000000000000000001b80810800060680000cf8000000002e000000000006d60000000000161000027423fc8ee20650a1e38d9f42000166b00000000000000000000000000000db000088100007f9124440e997e6de80001a51b9243c92e6000032c3634000000000000015be5e99dcc212a2c837a0fc20fe00008fc00000000000000051c90de2386cd80007198f8c00000003c799720000d0c2e74a906860000041241097c000004217008fb000000002b0292000000007b209a8f7e000000000000000000aa000002907814000000000000000006ce68460000000025c000000264822900000002178000000095a8318a0b800000000007038000115000000000007c000008ab000000000004db25982bb0000669196a00000000000000938000028d00004390000000000087007ff2ab000000011fc000267400014fc00017fa0001ed676f0f06000000070
  | 47 => 0x4769f8669b80000000000000000000000003ea852959624330901b4a13c26e6791a2162af112000000000000000468800000000009fe80000000000074000000024ae3ab0000000000082400008e0966c8c11dec000000000c8000000000000008465874c1e67e9182000208a0000eda3bf029400000007a09d3a1da8a869ab00001aa8000000034500000003ac8000000000000000002519f041510f377d505801ed800034e00001e213ae1fa8aea1e78000000098098806c6000120e7ae000062418d0000154c00010b60000000985000000000008dc1b9e70628720b29dfe00022d227384209e8011c3f583520c0800000000002e9631a61100004d8881200026dc00015f264480006fb86704da994137f069277c80005258a920000548000000035380004508076184000020703ac0000a2600000000000000000000000010fe0001ffc00000000001e0400002926c1855a000000000000000000a8e606c00028a28420ab805404e19ce0000cd698d987a100000019c800000000005ba00002701a9e6638950000038d69c000000012ba8598e62418034794601b70000d2e18880003140f460001ec000027f4000000088f810a869070e65ea42a0000b0ca15985c33f210a0001b8a1c21d64316c2fe9ff076e67714c2a1b0ba6034800004680000000c3f86e000000000000000cf80000000883000000000000001a0426a110610bc7167be80001dd800000011c403398f49d9a0ee79ca14822817ba5b4a54a6be1f2e90f0f0e7f300000000000000000020bc0000000fb500008263110000000122a00009820000ea600000000001cb22e824ec00019305c70b683041c1a42217c19ee000037780009cc1e9b4e40000484800000007a20000d5d989a17e00027a612603680000000000000094646cc000000000000004f30000000000074ca17c00024b200000000000000000165300000002b14e644770916973800000000002dc00000fd978e000163e00000007bc0000000086c0001b08000000002b15ae00000006fdc00000000003b48000000000000000000000930000000027d00009dc878a00000000e28c3a000165e00020f60002862164000000000000000000310400005c000000015c82e9e6f800000008290eb003880000000db49e005ee594000074712d05250000436000045c148127aa338000024c2202870000051e59f03425f19f8c15a40000800b9a5fe0e5c000168c45200001f4137e88d245c926a4a400000008e897be344a75c10a800011462a300006296b11d7400003ad0000000000158a000047242e00001ff0000000000000018742ac4000000000026b07f600000002e11c7a000061e9eb67ba393258495ee29227e8fec964849d0001b7c24adc265ea00004c7800084b80009e4407427823887b0d4
  | 48 => 0x360fe600000004d180002efa1e4a029a3ca1481f200000006b0800000021da2345df46ec842208a0e3e41e00000dd00001771bc6000000041d0000520000000000005a289da1ea00005cd0f3e683800000000000001eee1978000000076072511a46bf12b61758000459000023f04bf1898000000000000017da1ad800000000003de414800000007211b37000006e16f429a0000000000000079500006040dee00010cc1dd1a62032000093c864033900004880f3624ba6db00000000a280001b3800016927789a727c6238a523000000000005680b014040001d5600000008ce9b32a020000000000000000004889d920000000000040e00010570001ab23a386dc32900006198dc06ef83cb797000000002ee629279a101c00063b000034193380000000000000000000000000000624a19a00028760e080002a904e000024cc978000039e0000000000000000000000000316287a0000000000000085602e60000cd48ff872a55ba302000202204d000018b8000000000000000000001c9806e88b041a8078000000031f863f4e000004facfd0000000003500000002326089975d0000000000152200000000001434000000071a243a00000000001a8e904800001d531800000000000000000000000009c6000000024d000056900000001f7200021842c38567000000000000000001792099800000000009b900000be167220d1cee00000003d8800000013047670000906004003a000016080008c71b880000000593800054ba4e6263229e5e7985000015d2a041a0a98301e30000000000000097ea378000000000003bc47480000001ed88919b3a693a5da00016fd0070617222825a1df40003a4800091ac000000000000000000000000191800000019440000000321835608d0f42026800043e00009f79c3813edecc7cd8e8010124287948000431283413119c61560b5a1f186be72815a05e886901bc800045d80000000000000000000000002a780007c88b3205b800096d000097600000000000000234094c00008b620d2158e5a60001ec40000000558800000018040441f1d00026cc000000092724aa00002de0ab26f06a99e6222519ea9df000000000006f7000083a000080a19220000ec88972006968c00000000008801e98000103e8ea89a0646000000017940500d34000102479d17f0a0f8da078980006c512f414f05623f5091e39ea48c488c00000000000000000000000000000004b8000000021e2302a438000000000016a458a1c6900024c28ed925a4ee8bef45780004d600000000ba400026f564d8000834090000000000000000000176c83000004dd800000017860000000000057d00014d61eb00d3415400092f0000000000049000fa0000000000000000000000000a740939da8637800000013ee00022a00
  | 49 => 0xd96876047e20886681d5800000000007d1948e000262c522000000026e00000dea25680000000000000000000021880000016000000000007c800017ca7e400005929f02000241c0001dd444696208ca8000000000078c8ea83f28000000009400015202aca7ca00001f47b081a8140000000018a800011ec00000000000000000000000000006a400008770000000000000005d800000000001d1e0001fda000041a45e4c2014084120001d4e000065a000000022a921841c076148b818e116860c0000000000000069680d000000000000000751800031389b27091c2a4c080008650d0076e8000626000000000000f580009fc1bce91c4000000000000000008248000000000030d00008a61249541800000000006c680005bf80006fe947c7048000000000000000000000000000014e000000000026865c20000000000000020ce2df00000368d02214058c42c000000000000001894000000000026967b681541585940000000000020fe00012ea26500006d900000000000000137481300006d7814207b8c9213d000000000006d894300000000000000000000000001b6e3ee8458028000067900a282d16ce0000000504000019408be34c24c600016423328d5468d019870f001a700221e000272000000000000000000231222d800084814ca50e8bb40000000000000050a84800000b6200000000000000350a25440e008000006280000000000264a073800000000000001c6d292800000000000000000000000000000007f6000000000000000000000000000010a400000d65da846c1528b8625a9d1000025db1ac0000000000077da3d600000009c080003e68000000197f00009a200000000000000000000021a8be26e30000000052b5491f8e5790000000000094a8dac914149a4ca80008d318d800000000000cc2612203257500002ea40000b40dd600000000000000000000000000003ab8000692c00086f0b1800000000001cea96e0000864c00021600000000000000000078f95f16dd930607b092429b804b00000005cf80006cd61707f2800000009d800005b82ae970e75080000ca90e00821b5055426e79ca80008b08c6f8df0cb20000000000000086ac0000000bed5ec4eea5e9400034820bc000000000017cc526194b256139a00026f400000000000000000000000005d05e111c8000000000015a800000009a7800000000001b600000000a4200024344a3800000000008358000000000000000000000000609876643780000000000000000084891d600000000001cbc91a814a7f48b9466a065288b01193da12d38e19590512077a000000062980000002541831993d11981c00001a5e450000000000005020bca000000000000001669c580000000000000000000000000000947a69000026fe0000fde0000
  | 50 => 0x71e00025ac9701de000000000000bf400000000000000000017900000000002096a1600008589e483382252000236e851a15c18e1c7c00009f0000000000000000000000000204e2dbc22c0000000000161466b000000000001648706000017a8a561fc41f25c88ac8000000000022c980a00005ac0000c74000000000000001aa0000000000000000000001ca800000009bf000000023dc17d03920000000000083e0000000a0d80003b50bee00006340a08a5228b13dc55e1b2450a140691513c63b70000000000000000006ed800000000000000b1a00002c8000050e3c8000000000000000000872000000000002b880006a88000463c000000000000000000000000000000000013a4942189a000000020b031c117443464c9d7c01a8000000067842b0000000112800000000001bd600000000000000000000008b87006bc80004c89db686a0000000246c78f08d017852ae51c800000008ce000205c2f18a3d000000000019bc5bea09e432000000000005d7000000021a215818d60001d7e000042600003ea2df649621ac000a1502ea12821d203700002cd846744f00001ff5ea622422886c88000918a7468db1b054ec000046b000000026ee000000000000004728000298400000017f24ec800017f0be600000000000f8a00011502dd0000998a35a00013707ab8b5800000001fc662281f00004d2800000000000000000000000099bdff6000000000024f6000143e2d3a1e009c1db23ae00009a695ce1d899940000dbc35400000000000000000000018fa00000000000000000000000006d00000000000000000000001fd1bb5596c44000000005eb1e0000000005d4800000000005f0003300007a0127896c5cdc0c632a80003a412165ca8000000000084a8000000000083d00000000000269247c99100000bc18b23ce9ad803e1f6416d811654f80003b294584eb150426b97af00000009860000000000022e80001be800000000000000000362c0000000000159400087e000000000000000000406000003643700000000000000022680000000000047400000000002b000004ba0d7e46710c08d480002d02030932926c3580f8500000006ea800062c0000344000050b88f400000000000d9b1fb800088c15520000bec0000000a07119200021aa9629cc63a6800000000000000000312007d70880002e3800000004899371df000000000000fdc00017960000000000000000003ec73e1eb22c48000000248a95e269b9b8cd920000ff40001328407831d7ec8000645a55c30700005c5915d00000000001f800c2146640398ac06d800000008f000000000000898000000002310795ce049200026ba0000000366800000619560001058a08000039400000000c4c0001f5821058140001f4d046c0003d980009cf87460000000
  | 51 => 0x413f961899581803dc80003d000000001e7c0000000000263c98b9f8a2d71394515a61c947c40c582280e7f092b84179db892021ba1b997b028d461a55a000049180000000000699800000010067320b56000000089a0000000124200001242ca413049c00000000000588a4d636397aa00022bc580474466003a4038408290d681a4a2199a000218c000000005bdb3e6f000000000a9d23e00000000cee25a26b24140000000207278080005b3000000000000000c70000000000000004c30000236000046f83342ae1a466018bcc24497105f9a09451797229e5922839000006f8000024e00002f596f78b5032139440001961a324a18046500059672aa42e3f31fb68ff0000000000000003a700000000000807000000079a00000002066000000000020ec4516546000206549d1ea06a5000070e800000018e86a480007dd84fc3588000000000028900001a19d014130d487ce80000001f3073b037600000006b6a4f40ac9114000000000000000001ce40000a7a51923f800000000000000a0516947ca8000000000004b87f000005206d480000001b00000000000000007410bc07d8089c5cb94466b4955653c948428814a0000000000026c672011320000814000000035600008c7800012a000000024670c283647928000075975439c9b2045120be651a4953c0075c02d1d621420f5a75302440f122745b284b60000a7b7b7240289680008eba7cc4c90be04d480002848000000000000000000000000000000000007de000000075423be3708b2e3de000000023327960c6c000000092c04be0000000000152a00000007879560133017b157c00000000000000d6a00000008960000000000070c16e4000249e2c28f112889acc0001a00000017704a93fe00020f286488540a203b48d4000000000000000000000000000000000000000000146a00026b80000000408000000000009d8000000014f600000004b480000ed97ae08880004f419f6171c000161a2c000000004a614b79940c71000157600018d10000000997000000003e215983a9680a38400a186e73a09aa5f0c000a0606e0000000031dc00000000000001d1a000020e000000000000001c8000000000bd000000065d000000005427401bcc1419f9e0000bd4000277e00017e00001b66000000000027dc00000000001ce5000000097fa25e0000000000189c0a180000000000000115934f800071d00000000000000000007c000000003be3dd000000000000000000000000032d00000000000000223201f000038e855c52e1f509c98000539d0bc84e281e00027ae000004400007280000000972c00038c678224ed99c00000006071906000000000028020001e903b99d8e131996c00000002c00000000147e00004bc6da802464f80001f501a45b4114c0001d2c000
  | 52 => 0x1a89ca404f80be5bb00005949bfe09f176e09797d0000000015b89a684584d4000000000024ff00000008f226b6000000000000008f800c5076000050486543bd0000000224490d8b6a46a1bb76779c5a52f8b7a5bcc0004c00f825600000290d5a2256ca8200000004000000000000040b000000014f0000125f000000096080000000bd800000000000000000000000000000000000000099c0000fc65bf000000000007a48000000000041b28280000000000000000000002f780000000000000000000000481c6000030b0000000000011da1d430a0000000000000000000001920000000000013ea0001103000171a9ad0865657c0003a5a58056498f02740bbc3ba133e000000009fa66c4cc80008c8800000000000000000000000052d8653000000000025c284d8000000000000022401dd400000000007838000537944a8f4800033a869849d5422000271e00000000000f100001d58364000054d08602ca27ab09f4527407086e40f25430000000000000017142502d2800000018cc000205e000000000021c200000007c30000463a78f00000009a29eca00000000ae14bc000000000000000000000866c34b0000cb09c61b721f1157a1d3000000000008f400000000000000000000a97252148da20000000061a6804281a4f000000000000000b1055e85395cc51d400000011ea07e000023480000000000000000086e5cda595563400000000e88000000000000000003bb923a2fe0000000000058080008c326f22999f3d13b958e297a86e6830a440ce00000000d0e131d78230f40002a6a2e09b026b50ff8e030001ee21a980000000d1647c11080000000883800000002c200000007ea80000000000000073a67a0380000000014f9748000000037d0000000000000010fa00018fc000000000000000001e9676102d499e0c4a586937888a05227e6139c0000000000000025380000000000000000002f0000000000000017d40000000000000097280000000bb60002080801000046c80004ac26d600000004cc0206000000000000006fc271000000000000cd367f105200000000000c78000203c6720b2c000000000007020001fee9a50000000032200022800000000000000000005e300000000000fa028d879058c9b60773a3e820280000000cde35e0000000164d28600000001fa80de4d9c0000000000000055194dc2bb88570d88000000000000000002e2c0007df0d2167693d60be864
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6c82dd952040018dee5bb2a40800a1fe0b765481000637c16eca90200287d82dd952040598d905bb2a4080031b087765481016637906eca90202cc6d20dd952040014df04bb2a4080031bdc9765481016c3fc12eca902000c6f825d952040018e902bb2a4080031b085765481016637902eca90202cc6d205d952040598ee20bb2a4080b31d441765481016e2fb94c6a902000e4f7298d5204001c984331aa4080b393c82635481016726904c6a90202dc5f7258d5204001c9ee4b1aa40800393085635481016727902c6a90202ce4d2058d52040054dd0eb12a4080b71ba1d625481016636c3ac4a902002a6c8758952040094d902b12a4080069be01625481000d36c02c4a90202ce67105895204059cca20b12a4080029d61b71548100063abb6e2a902000e6562dc552040014eb0c38aa4080031d5d8715481000732b10e2a9020038ef8758b32040071d905bb264080022fe11764c81008c5e422ec99020008bd86dd1320400187ccbba264080030f597744c8104064f31ee89902028cae62dd1320400117b0c3a264080030f994744c8100061eb28e8990207fc9e631d1320404995cc43a264080022fa1e644c81008c5e43cc899020008be8759132040011790eb22640800e3721d634c8100064fba2c69902000c9c7458d32040071d90eb1264080032bdd1624c810006563a2c49902000c7565dc532040019aac7b8a64080033958b714c8100047ac30e29902000c75651c532040019cac438a640800a1fa17768c4100043ec2eed188200087f865d631040fd8bcc6bac62080031b989758c4104b43fc3acb188207e87d87596310400187ceb32462080030f5d6648c4100061f3aac91882000c3d7559231040018bceab1c6208003175d5638c410006373aac51882000c6d7558a31040019b2c6b84620800e3720f764c4100061f32ee89882000c3d65dd131040cf93cc7ba262080032b98b744c4100061f328e89882000c3d651d131040cd93cc63a262080032b988744c4100045f43cc898820118bc87991310400117d0eb2262080022f21d644c4100064fba2c69882000c9c7458d310400195ee8b1262080032b1d1624c41001c6ec1aec1882003cea70588310400f9b4c6b8062080033a589700c41001c77c3ac51082000a6f8654a21040014db0ca9442080331bdd9528841000e36bb2a51082000e4e6354a2104001c9ac6a94420803399985528841000674b12e11082000d69525c22104001cc842b2a4208003b108663484100076210ac69082004ae48158921040018f0ebbb220080031ee1776440100063c42eec8802000cdb83dd910040019b107bb220080033ae0b764401000674416ec8802000c7b52dd910040018f6edbaa200800336ddb73440100066dbb0e68802000ceb76dc910040019d6ec39220080031edd95244010
  | 1 => 0xb0f90aca0800297a0f21594100052ec1e42b28200087e8708565040010fb0e10aca0800387d525498c101652ec2ca53182000e4f5294a63040014bd0b214c608002976164298c1003c6f4388531820008dd8710a63040014bd0a214c608002976144298c1003c6f43ea331820008dd87d46630400153d09a8cc608002a76135198c1000567416a33182000acd82d46630400f1bd0f90cc6080023761f2198c100052f42e433182000a5d85c86630400153d0990cc608002a76132198c100052f428433182000a5d8508663040071bd0fa9ac60800317dd75358c100162f3aca6b1820038dc8754d63040071bd0f192c60800297a163258c100052ec2c64b182000a5e850c963040014bb0a192c608002a7a103258c100054ec2064b182000c5f759d563040015a902ba2c608003275d07458c100070faa4a8b182000a5e859c963040014bb0b392c608002a7e117258c100054e422e4b182000ad4815c963040014bd0a392c608002976147258c100054f420e4b182000a9d841c963040594bb0b292c60800393d4a5258c100052f42c84b182000a5d8590963040011bd0e212c6080023761c4258c100052f42884b182000a5d8510963040014bd0b38ac608002976167158c100046f43ea2b1820008dd87d45630400153d09a8ac608002a76135158c1000567416a2b182000acd82d456304001caea328ac60800237a1f2158c100046ec3e42b182000a5e85c8563040014bb0b90ac608002a7a132158c100054ec2642b182000a5e8508563040014bb0a10ac60800eb6a002158c100056cc0042b1820038bf8759243040071b90eb1a8608046a72116350c100063ab2ee2a182000cd563dc543040011eb0c38a86080031d5947150c100054fc32862182000a9d8650c430400f93eeca188608003275d94310c104a70f32a862182000e1d6550c4304127d1cc4a188608002e52054310c101643ec3ceab10202ca6d829d562040011e902baac4080b69be0975588100143f42ee6b10200087d85dcd62040071dd0fa92c4080031bdd7525881016e3743ea4b10202de6710d49620405bcca21a92c40800e3b21d52588100057240aa4b102000c6f759d5620405bcce213aac4080b799442755881000573c0aeab102000ae4815d562040018df0ebaac40800399e0575588100073240aeab10202ce67105d56204059cca20baac4080029ba17735881000536c2ee6b102000aaf845cd620400155908b9ac408002b9205735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881000727a9ca6b102000ae78150d62040015c902a1ac408003a350c435881000636bace2b102000a6e851c562040014db0a38ac4080031b5d471588100247743ea2b1020008ed87d45620400159d07a8ac408002b360f515881000733a8ca2b102001
  | 2 => 0x3634c91003c7743ec49922000caf74d893244001958e9b12648800a1f216768c5100e43e432eb18a207ec5c635d631440018d8c4bac62880021fe1f658c51004c3ec3ecb18a2000c3e75d92314400187aebb2462880030f9d4648c5100061eba8c918a2000c5e75d8e31440018baebb1c62880031b9d7628c51000636baec518a20418be86dd1314400187ecbba262880030f197744c51033e4e31ee898a2000cac62dd1314408517d0c3a262880030fd94744c5100061e328e898a2066c9c631d13144001958c43a2628819a2fa1f644c5102145e43ec898a20678be8719131440231790e322628800327dd3634c5100064e3a6c698a2037cd870d8d314400195ee9b1262880032b1d3624c51000537432a510a2000a6c8654a21440158dceca94428800393d8d52885100072631aa510a2000c74659da2144001cc8c5b2c4288003b118b63885100066b3b0c710a2000e946418e2144001d88c431c4288006b9a1b6288510006733b6c510a2000e678654a21440016cd0ca944288002d9219528851000732432a510a2000a648654a2144001acceca94428802b999d95288510007a3b1aa510a2000f446354a2144001cc843b2a4288003b1087634851000762108c690a2001ae681d8921440659d0e1b1242880e31d1db654851000732316ca90a2037cd476d8d2144001d88c5b1a42880db351d863485100074a320c690a2000ec46218d21440155cd0db924288007391db724851000d73436c490a2032ce476d892144065bc6e438242880025d61671cc11003e6a31ce3982200087f855d930440050f90abb260880022fe11764c11008c5e422ec98220008ef825d930440031d904bb260880021fa1b754c1102ee2e31eea9822000c6c62dd530441330fd0fb2a60881761f21f654c1100061fbaec89822000c3c75d91304400187eea32260880030f1d4644c1100062fbaec69822000c5c75d8d30440018deebb1260880031b1d7624c1100065a326e29822000ce462dc53044001968c838a608800335d8c714c11000672310e29822000a6e8654920440014d90ca9240880071b1d9524811000727b1aa49022000e4c6354920440018e8cbb8a40880033518f7148110004bac28e29022000c74651c520440019a8c638a408800339d887148110006b2a90e290220039e48748520440075c90c90a4088007391d9214811001df0402429022038c7a76d97104406f9b4edb1e208801f369d863c4110196753b6c58822001cea7618b10440038f4eca962088003d854a21c41100062fb9ce6b28202dc7710dc9650405b8ea21b92ca080031bdca72594104c53bc0ae4b282000a74815c965040010fd0f192ca080021f61e32594100043f43864b28200087d870c9650400147d08192ca080028f61032594104bd3cc04e2b28200587e87c8565040010f
  | 3 => 0xa3122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e4e75d8c6244001c9aebb18c488003b15c7631891000476c3cc63122000a6e8598c62440014db0b318c488002aba12631891000556c24c63122000ace8398c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488002b3a186318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d90631891000746320c63122000e4e7518c6244001c9aea318c488003b15c463189104df63080c6312209bec41018c62440015cd0d288c4880039919651189100076231ca23122035ae4865446244001cc8caa88c488003b118d51189101752f41eeca922000a5d83dd952440010fd0d3b2a4880031b18a765491000536c14eca922000c6f729d952440010fb053b2a4880031b60a76549100063610ceca922000c6f209d952440014bf06bb2a4880ba9720d765491000537c12eca922000a77815d952440010fd0c3b2a4880031bdc876549100143fc10eca922000c6f821d952440050fb043b2a4880031b20876549100063ac08eca922000c76211d952440018ea423b2a4880031b084765491000637900eca922000c76101d952440018e8203b2a4880ba97a1b63549100062f3b6c6a922000c5c76d8d5244001c3ec9b1aa4880039318b63549100062fb96c6a922000e4f72d8d5244001c9843b1aa48800393c8363549100043fc3ac6a92200087c8758d524400147f08b1aa48810e8f211635491000537c12c6a922001a6c8258d52440014bd0c31aa488003179d863549100062e3b0c6a922000e1f6418d5244001c38c831aa4880039318863549104d62fb90c6a922000e4f7218d5244001c984231aa48800393c80635491000d37436c4a922000c6c76d895244001c9ec7b12a4880039318f6254910045b240ec4a922000c6f87d8952440054dd0fb12a48800a9b21f62549100063643ec4a922001a6e81d8952440034d903b12a4880229b60362549100053b434e2a922000c74769c552440636cb0538aa4880b29d21971549100063a3b2e2a922034b67825c552440010ff0abb6648800a1f21576cc9100045fc22ed99220118bc845db32440031b906bb6648800a1fa17764c9100043ec2eec99220118be84dd9324400117b09bb264880462fa12764c9100045ec24ec992200087f855d932440050f90abb264880022fe11764c91008c5e422ec99220008df835d932440011ef02bb264880022fa1b744c9100061fb2ee89922000c3c65dd13244101938c7ba264880a32b18b744c9100045f430e89922000c3f651d13244001878ca3a264881ff2718c744c91012656310e899220008be87d9132440011790fb2264880022fa1c644c91008c5e438c899220018de87d8d324400193ee9b1a6488003271d
  | 4 => 0x34400193ceca18868801f271d94310d100070fb2a8621a2094e1c6550c4344127d18c4a1886880025d6167110d1003e6a31ce221a20038f4865c443440018b8ebb1ec488003171d463d891000e373b6a5b122000e4f63d4b6244001c98c7a96c4880029b60b75d891000536c10ebb12200087f855cf62440050f90ab9ec4880031b5d752d891000572c0ea5b122000c6d87d4b6244001ccd03a96c4880039960752d891001477c3aa5b122000a6e861d7624400159d0732ec488002b360e65d891000567c1acbb122000acc835976244001ccb0232ec48800393d9763d89100072632ec7b122000e8f64d8f6244001c9eebb1ec488003931d763d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727ba8c7b122000e4c7518f6244001cc8cb28ec4880cab921951d891000636ba8ebb122000ae6811d762440655cb023aec4880031ba1c75d891000733408ebb122000e65811d7624400155d09b9ec488002ab61373d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000537c2ae7b122000a6c855cf6244001c9ea729ec488003a350c43d891000537c2ae3b122000a6c855c7624400159f06b8ec488002b320d71d89101947743ea3b1220008ed87d47624400159d07a8ec488002b360f51d891000637baee1b122000a6f855c362440014d90ab86c4880031bdd570d89100143f436eab122000c6c62dd562440010fd0fb2ac4880021fa1c65589100062fb2ee6b122000c5c65dcd6244001998c5b9ac48800317d9473589100062e328e6b122000ccc621cd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d063589100143f43eeab1220008df835d5624400f1b906baac4880023be0975589100047bc0aeab12200087e871d5624400f1bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd62440018bea5b9ac4880031754b73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891000637baee4b122000c6c75dc9624400199ee7b92c488003331cf72589100063a3aee2b122000cd473dc562440018dcedb28c4880029b61f651891000732b8eca31220008ed8799462440014dd0b328c488002b3a0e651891000566c1cca31220008ef87594624400159f06b28c488002b320d651891000573c0aca3122000a6e8619462440018dcec328c4880029be1c651891000732c08ca3122000e66711946244001ccae2328c4882739984065189104e732080c
  | 5 => 0x80030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000637c2ee4b1a2000c6c85dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d100143e43ea4b1a2000c3f74d49634413d878e9a92c6880031bdcb5258d1000e36396a4b1a2000cb474dc563440019c8e5b8ac68800237e1d6318d100052fc2ac631a2000a5c8558c634400153f08b18c688002a72116318d1000567c12c631a2000acc8258c63440018bcedb28c6880029760b6518d100046ec3cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440018bcec328c688002976086518d100072ac08ca31a2000c9e76d906344001c3ecbb20c688003871976418d100046ec3cc831a2000a5e8599063440014bb0b320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc825906344001c3eca320c688003871946418d104ef4b080c831a209de941019063440014bd0b310c688002976166218d100054f424c431a2000a9d8498863440014bd0a310c688002976146218d100052f436a431a2000e1f64d486344001c38c9a90c6880039318b5218d100072a32ca231a2000e9464944634406d5a90ca88c688003a51915118d100056b40ea831a2000ad581d506344001c3ea92a0c688002b5a075218d100056ac0ea431a2000e5681d486344001cab03a90c68800393d4a5218d100052f42c8431a2000a5d8590863440015ad03210c688002b56064218d1003c6f4388431a20008dd8710863440014bd0a210c688002976144218d1003c6f43ea231a20008dd87d44634400153d09a88c688002a76135118d1000567416a231a2000acd82d44634400f1bd0f908c6880023761f2118d100052f42e4231a2000a5d85c84634400153d09908c688002a76132118d100052f4284231a2000a5d8508463440014bd0b900c688002976172018d100052fc2a2031a2000a5c85440634400153f08880c688002a72111018d100043fc2aed21a200287c855da434400f1b906bb486880023be097690d1000c76412ed21a200287e85dd943440010fb0bbb286880063ba0b7650d1000476c16eca1a200087f855d943440050f90abb286880023be097650d1000c76412eca1a20008f7815d943440231bd0fb1a8688046a7a136350d100043fc2aec21a200287c855d843440011df04bb086880063b2097610d100054f4328621a2000a9c8650c4
  | 6 => 0x52f41cc5b2a2000a5d8398b65440130fb0e316ca880031b5c862d95100062eb98e7b2a2000c6d721cb65440694ed02396ca880e29d60472d95100043f43c65b2a200087d878cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440710fd0f90eca880021f61f21d95100052f41e43b2a2000a5d83c8765440010fd0e10eca880261f61c21d951015d3b40ee1b2a200087e87c8365440010fb0f906ca88003175d753d8d100056ac0ea7b1a2002c5c7594f63440051bf0ea9ec68800297a1632d8d100052ec2c65b1a2000a5e850cb63440014bb0a196c688002a7a1032d8d100054ec2065b1a2000a5d82d97634400153d0932ec688002a761265d8d1000567414cbb1a2000acd82997634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc8259763440014bb0432ec6880039560465d8d100070fb2ec9b1a2000e1c65d9363440014bd0b316c6880029761662d8d100054f424c5b1a2000a9d8498b63440014bd0a316c6880029761462d8d100052f436a5b1a2000e1f64d4b6344001c98c5a96c6880039519651d8d101bd6a432a3b1a2000c5d751d763440015ad023aec6880deb560475d8d100064fba4e9b1a2000e1f54953634400153d09b96c688002a761372d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d100052f428e5b1a2000a5d851cb63440015ad02396c6880deb560472d8d1000727a94a5b1a2000a5e8590b63440014bb0b216c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c6880de37a1f51d8d100046ec3ea3b1a2000a9e84d47634400153b09a8ec688002b3a0b51d8d1000566c16a3b1a20378de87c8763440011bb0f90ec68800297a1721d8d100052ec2e43b1a2000a9e84c87634400153b0990ec68800297a1421d8d100052ec2843b1a2000a5e85dc363440014bb0bb86c68800297a1720d8d100052ec2e41b1a2007c5c635d663440018dce5b2cc6880031b9c86598d100061fb2ce931a2000c3c659d2634400f938c73a4c6880030fd957498d100061e32ae931a2007c9c635d2634400187cebb24c6880030f5d76498d1000657396c931a2000c5e75d8e63440018baebb1cc688003279d36398d100064eba6c731a2000cce72d8e63440018decab94c6880031b1957298d1000657b22e531a2000ccf635ca634400f998c6b94c6880021fa1f6558d1000636396cab1a200087e8719563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c3f651d16344001878ca3a2c6880030fdd76458d100061e3aec8b1a2000cac72d9163440018decbb92c6880031b1977258d1000657b26e4b1a200087d82dd5634400117f08baac6880462f2117558d100046fc1aeab1a20008ef825d563440031d904baac68
  | 7 => 0x658518521480018b8ebb1a60900025ba1d524c120004b643aa4982400087f825d763c40058bceb29ec78800a37e1d53d8f100143fc3ea5b1e200087d87d4b63c400117f08baac7880462f2117558f100064e3a6e6b1e2000c3f74d4963c413d878e9a92c78800237e1d6318f100054e422c631e200287e859d943c40010fb0b3b287880063ba0a7650f1000476c14eca1e20008df835d943c40050fd0b3b087880021f6167610f1003c6e41aec21e2000a9e8650c43c40015390ca18878800e3d61a7110f10004bac2ce221e20078de83dd762c40011bb07baec58800a3be1d52d8b100143f42ee6b16200087d85dcd62c405d4bd07bb2a5880029760f7654b101752f41ceca962000a5d839d952c40014db053b2a5880029be097654b100043f43ec6a96200087d87d8d52c400147f08b1aa58810e8f2116354b1000537c12c6a962001a6c8258d52c40054dd0fb12a58800a9b21f6254b100073340ec4a962000e6980d8952c40594eb0d38aa5880031ddda7154b101d5b2c14e2a962000c74765c552c40796cf04b8aa58800a1fa1676ccb100043ec2ced99620008bf845db32c402317908bb665880063720d76ccb100143f42cec996200087d859d932c402317d093b265880022f612764cb100045fc22ec99620118bc845d932c40ff938c63a2658800637a1f634cb100064e3a6c69962040a9c8458e31c40cd938c63a26388003271d3634c7100046fc3ac618e205fa9c8458c31c4001ad2a4b84438800399e19528871000732432a510e2001e667654a21c4003ccaeca944388003d854a7088710007b0a92e110e20038ee87d8921c40012eb0bbb24388002f860362487101bc6fc3ac79862064a9c8458f30c40012eb0b38e6188116a7211634c31000e363b2a49062000975851c520c40019cac438a418800359548714831001cf243a429062001ce47648520c40050fd0fbaac7080021f60b7558e102e43f438eab1c2002c5c7594d63840071b90ea9ac7080021fa1f5258e100143e43ea4b1c20038bf8759243840010ff0abb2870800a1f2157650e1000477c12eca1c20018ec825d943840010ff0abb0870800a1f2157610e100054fc328621c2000a9d8650c438400172902a18870800237e0d7558a1003c6e41aeab1420038ec8754962840034d905bb2a50800297e0d7654a101752e41aeca942000a6f825d952840010ff0eb1aa5080021f21d6354a100153743ac4a942002a6c875895284059cce20b12a5080b3994416254a1000732b16e2a942000c76761c55284001ccac438aa5080021fe1576cca100143e42aed994200087f855d932840050f90abb265080022fe11764ca1008c5e422ec994207fc9e631d132840071b90eb1a6508003271d1634ca101b46fc3ac798c2066c9e631d13184001938e8b1a63080231b5d952886100
  | 8 => 0xa438ac69000237e1d6318d200052e42ac631a4000a9c8458c63480015a902b18c6900021fe157650d200143e42aeca1a40008df835d943480011df04bb286900023de057650d200047a40aeca1a400087f855d843480050f90abb0869001e3720d7610d200047bc0aec21a40008f4815d8434800153d0ca188690002a72194310d2001c76432e421a4000d8d435c843480594dd0d39aa4900029b61a735492011e363b4e6a92402cb6a809cd52480016d30139aa4900029be19735492016536432e6a924000b2f845cd524800165908b9aa490002dae017354920165b4402e6a92408ec6c761cd5248001c9ec731aa49004ada602635492006cb643ac6a924000b2f8458d524800165908b1aa490002d9e056354920005b240ac6a924016b6b8058d5248001c9ac631aa4900029be1943549200053643286a924000a6e8610d52480014db0c21aa490003c350c435492000537436e2a92400da6d86dc5524800169d07b8aa490002d360f715492016537434e2a924000a6d869c552480338d8ed38aa490002d3a0e7154920005a6c1ce2a92402cb6a809c552480016d30138aa4900029be19715492016536432e2a924000b6b805c552480596d100b8aa4902271b1d87154920006b2b88e2a924002a6f86dc152480598d8edb82a4900b2daa1f705492000db4436e0a92402cd6a76dc15248141ad0edb82a4900035adc77054920006b4b8ee0a924083b6a871c15248059ad50e382a490216daa18705492016735430e0a92402cf4a831c15248059e9306382a4900b3d8a047054920167b0c08e0a92400087f855cf61480050f90ab9ec290002b5a0f51d852000572c16a3b0a4008d697054a6148001ccaa5b0cc2900365b21d5258520006a7b9aa4b0a4000d4c735496148019ad6e0a92c29027e5be1d52185200047bc3ac230a4000a748558461480015a906b08c29000399549611852000536c14ea30a400287f875d461480018e902ba8c2900022fe11731852008c5e422e630a4002c6e7554861480015cf02a90c2900029be1d521852046637c3aa430a4089c6c875486148001ccf02a90c2900039920552185200063abaea230a4000ad683d4461480015cb05a88c2900039954b511852000572c10a230a4000e655214461480018dceca9662900031b5d952cc52000732a90c398a400287e851da31480010fb0a3b46290003179d7638c520004b7c3aa518a400096d8754a314802317d093b262900022f612764c52000637bb2a498a4000c6c765493148001a5ee8a9262900034b1d1524c5200043fc2aec18a400287c855d8314800117f08bb062900462f211760c520166b5382a418a4000ce5721843148001ccaa430862900063e219700c520006b4a92e018a400c8ee8718521480195cd0e30a429000339a1c614852000733428c290a4000e
  | 9 => 0x76548301752e41aeca906000a6f825d9520c0014bb0db9aa41800a9ba1d62548300153643ac4a906000e4f73589520c05dc98e6b12a4180029b20562548301772618ac4a90602ce4f30589520c059c9a60b12a41816637e0d765083001c5e43ac8a106007c9c73591420c0038d8e4a94c21800e3d61e51984300045fc22eab0860118bc845d5610c00f1b906baac21819f271cf74584303364e398e8b086000c3f74d49610c13d878e9a92c2180030fdd1525843021e1e3a2a4b086000c6f72549610c0038d8e4a92c21800e3d21d515843020c5fc3ac9a0860648df865cf410c0050fd0bbb482180021f61776904300063abacc32086000c7575586410c02356908b0c821810237e0d765043003e4e39ac8a086007cd473985410c0018bceabb4621800317d49768c4300062ebb2eb188600095f8754a310c0018baeca94621800393589528c4302054e422c31886000c6f7654a210c0018daeca94421800e3d61e618843000732a94c31086000e6552586210c00117f08bb242180462f21176484300046ec36e69086000ae481589210c0035c90530a421800e3d21d614843000d72412c2908600287e87dd563880b90fd0e3aac71000b171d65358e2001c6e43aa6b1c40038bf8759243880010ff0abb2871000a1f2157650e200047bc0aeca1c40008f4815d943880010ff0abb0871000a1f2157610e200054fc328621c4000a9d8650c438804971904a1887100022fe11739862008c5e422e730c40038f58794661880058eceb28cc31000a1fa1f75586200063610eeab0c4038c6f20dd561880718da41baac31000237e0d755862003c6e41aeab0c4000c5f75dcd61880018b8ebb9ac31000327dd373586200062fa96e6b0c4000c5d52dcd61880018beea39ac310003171d473586200064fba0e6b0c4000c9c741cd61880058e8eb28ac31000e3d21d51586201b46fc3ac798c400287e85dda31880010fb0bbb463100021fe15764c6200143e42aec98c40008bf845d9318802317908bb2631019b2798c744c6200064e3a2c698c400087f855d831880050f90abb063100d63be1d618862000537c2ac310c4000c5d75d4f634800159b05a9ec69000a1fa1f7558d200043fc16eab1a400087d82dd5634800117f08baac6900462f2117558d200046fc1aeab1a40008f7815d563480011e902baac6900021fa1c7558d200061fbaee8b1a4000c3c75dd1634800187ea5ba2c6900030f54b7458d200061fba8e8b1a4000c3c751d163480018b8ebb9ac690003271d37358d20006563a6e4b1a4000c7775dc563480018e8ebb8ac6900032ddd37158d200065a3a6e2b1a4000c7752dc563480018eaa5b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000c77521c563480018ea
  | 10 => 0x9926045c9e861d1324c08b93b0c3a2649800347d94744c9300068e328e89926024c9e621d1324c049938c43a2649815763188744c9302ae8fa90e89926055d1d521d1324c0ff93ec03a264981ff66d80744c9301246f43ec89926045c9c74d91324c0031b90eb226498117271d1644c93000d66412c89926000ad481591324c001b18e9b1264980da37a1b714c930006cc3a6e0992600087f855d3614c0050f90aba6c2980071b9c952d853000636b92a5b0a6000ab684c87614c001ccaa410ec29800a1fa1b75585302e43e436eab0a600087e87d95614c0018d8e5b2ac2980021fa1c655853000636390cab0a6000c3f65dd1614c001878cbba2c2980030fd9474585300061e328e8b0a6000c6f65dc9614c0018d8cbb92c29828b175cc65185300047bc3ac230a6000ab484584614c0015c904b08c2980462fa1375185300045ec26ea30a6002c5e7594c614c00193ae8218c298002b560732185300054e4226430a6000ad7814c8614c00156d09908c298002b560f211853000672b904230a6000e6552084614c0071bb073b682980021fe1576d05300143e42aeda0a600287c859da414c0010ff0abb4829800a1f21576905300143f428ed20a600087d851da414c0010f90cbac82980021fe1f65905300043ec3ecb20a600287e85dd9414c0010fb0bbb2829801e3720c76505302ee2e39ecaa0a6000c5f65dcd414c0018b8cbb9a82980021fe1576105300143e42aec20a6045c9c435d8414c0011df04bb082980063b20976105300062e32ae620a6011c9c645cc414c001d288630882980031719676cc5300062fa94ed98a6000c5e76d97314c0014b90ca966298003179d952cc530006a6b92a598a60a287c865d6314c0010fb0fb2c62980030fd97744c5300061e32ee898a6000c3f651d1314c001878ca3a262980032d1d3614c5300065a3a0c298a605cc5c76d95314c08b33d0fba2629800347d94744c5300068e328e898a6000d1f521d1314c0cd93ec03a2629819b66d80744c5300052e432a498a6000d1c74549314c001a9ee4a926298003651d3614c5300064e3a0c298a6000e5765185314c001b28e830a6298003661d3704c5300043fc2aed10a600287c855da214c0018b8cab9c42980029ba19528853000536432a510a600287e85dd9214c0010fb0bbb2429800339086764853000672108ec90a6000e6421d95214c0071b90cb9a42981166721173485300062e32ae7a02600399c845cf404c023938c8b9e80980021fe1576501300143e42aeca0260018ec825d9404c1430fd0fb2a80981761f21f655013030e4ebb086a0260038bc87551640c00117f08baac4180462f211755883003c6e41aeab1060038ec87549620c0031bb07b8ac41800a1fa1471588300043ec28e2b106001a6c82dd9520c00147f08bb2a41810e8f211
  | 11 => 0x4c0018eea5b8ac8980031ddd471591300063a3a8e2b226000cd7731c5644c0019cee438ac898003391c871591300065b218e2b226000cd4431c5644c0018eea438ac89800e3760e76191300045fc3ac83226000aac82590644c00156902b20c8981862f61f64d0d3030ecc21ae1a1a605cc5e76d97434c001c3ecbb2686980da3721971d0d302ef0e21ecaa1a6007a9e83d91434c0018b8cb3b0869800267e1d6410d300070fb2ac821a6000e1c65590434c0ab71904b208698002e52056410d30315cdc02c821a6061a9f87590434c00193f0eb20869800387e156410d300070e42ac821a6000e8f82590434c04953d04b208698092a72096410d3000746412c821a6024a8c82590434c001c3ea4b208698003a5e056410d300054e40ac821a6000e9481590434c00152902b20869818aa7e016410d300074dc02c821a60248dc865c8434c00193ac8b9086980029b60b75d893000536c10ebb12600087f855d3624c0050f90aba6c49800a1fa1671d89300043ec2ce3b12600087f855c7624c0050f90ab8ec4980022fe1171d893008c5e422e3b1260018dc835c7624c0010fd0fb2ac4980021fa1c65589300061fb2ee8b126000c3c65dd1624c00187eca3a2c4980030f194745893000656310e8b126000c7765dc5624c0018e8cbb8ac4980031dd9471589300063a328e2b126000ce4621c5624c0010fd0d3b2a4980029b60a765493000636c14eca926000c6c219d9524c0018de413b2a4980028fe11765493021d1e422eca926000a5f835d9524c0014df04bb2a4980029de0576549300053a40aeca926000c5d831d9524c0050ff043b2a49800a1f60876549300062f990eca926000c5d321d9524c0018d8423b2a498003178c076549300062e180eca926000c6f201d9524c0010ff0eb22a4980021f21d645493000537c12c8a926001a6c82591524c0014ef02b22a4980029d20564549300052f434e6a926000c5c769cd524c0a169b0539aa4980b29721973549300062e3b2e6a926000b1c845cd524c0a569f04b9aa4980b297a1b43549300062e3b686a926000c5c7610d524c001c3ac821aa498002d3608435493000c5f424eda1260038dd839db424c08b93e873b684980021fe1576d09300143e42aeda12600287e85dd9424c0010fb0bbb2849801e3720c76509302ee2e39ecaa126000c5f65dcd424c0018b8cbb9a849828e67a1f43509300064e3b686a126000c5c659db324c08b33d093b664981163761f64cc93022e4f3a6c999260008df87593324c0c3938e8b266498006b320964cc9300056a40ac9992604599c845c7324c00187ecbba264980030f197744c9300061fb28e89926000c3c651d1324c049958c43a264980032b1d3624c9302e62e3b6ca9926000e4c62d95324c08b33d0fba264980a3271db744c9301264e3b0e8
  | 12 => 0xe2f21d6450a3030e4e39ac8a1460a5c9e64dcd428c00117b0dba265180022f618744ca301445f43cc899460118bc87991328c05117d0eb2265180922f21d644ca3000e36392a530c60038f587946618c0058eceb28cc3180031bdc9525863000e36392a4b0c60038f487545618c02393cc8b9e831800a1fa1776906300043ec2eed20c60a4c3e645d6418c00187ceab2483180030f5d5649063001c5e426eca0c6061c9c73591418c08193cc9b9a83180030f9d6648c6300061ebacc918c6000c3e75592318c00187aeab2463180031d5d6618c6300063abaac318c6000e1e75992318c001c3aeb324631800387d4a648c6301b64f38cc918c6037c9f70992318c06f93ae1324631800257e1d528c6300070f322a518c6000e4d6254a318c001ab2eab8463180022f61b744c6300045ec30e898c60008be87991318c0011790eb22631800387d4a640c6301be4f38cc818c6062e9671990318c06d93ee132063180db275c2640c6300070f322a418c6000e4d62548318c0018deeca9443180031b5d9528863000717322a510c6000e2d6454a218c0071eb0f30c43180039954a618863000732a92c310c6062c9c73991218c001d48433224318003a908564486300064f326e690c6000ae481589218c0035c90530a431800e3d21d614863000d72412c290c601387d8718b654c00147d08316ca980028f61062d953000636b90c5b2a605da5e83dd3654c0b94bb07ba6ca980030f5d074d95300051f420e5b2a6000a3d841cb654c0bb4bd06396ca981729760c72d953000636b90e5b2a600087e8790b654c0010fb0f216ca980021fa1c42d95300043ec3885b2a605da5e8310b654c0014bb06216ca980021f61e32d95300051fc22e3b2a6000a3c845c7654c0014bf06b8eca981769720d71d953000537c12e3b2a6000a6c825c7654c00147d0838eca980028f61071d95302ed2f418e3b2a605ca5d831c7654c0010fd0f90eca980021f61f21d95300051f42643b2a6000a3d84c87654c0bb4bd0790eca980029760f21d95300043f43843b2a600087d87087654c0bb0fd0f906ca980021f61f20d95305162eb98cbb2260038dd83dd7644c05b8bae7a96c898002a760c42d91300043f43ecab226000c6c72d95644c0010fd0e32ac8980031b1c8655913000637b2ee4b226000c6c65dc9644c0018eecbb8ac8980031d19771591300063bb28e2b226000c74651c5644c0010fb05baac8980023be09755913000c76412eab2260008f7815d5644c0011e902baac8980031bdd77259130006363aee4b226000c6f85dc9644c0018d90bb92c8980031bdd47259130006363a8e4b226000ccf731c9644c0010fd0fa92c89800a1f21f525913000637b96a4b226001c6c72d49644c0018eeebb8ac8980031d1d7715913000673b96e2b226000ce472dc564
  | 13 => 0x43fc3aeb30e607ec5e735d661cc0010ff04bacc39800a1fe1f52987300043ec3ea530e600087f8754a61cc0010fb0ea94c398002a721132987300056bc0a6530e600287e85dd161cc0010fb0bba2c3980031bdc9525873000e36392a4b0e60038dc835db41cc0050fd0bbb483980021f617769073001c6f41eed20e6067c9c43dda41cc0031dd05bb483980023b60b76907300061f3aac920e6007c9e7359241cc0071b906bb2839819b2710d76107300064fbb6e898e6000c9f761d131cc001a3ea43a26398003471d1524c730006a7b92a498e6000c9c7498531cc0050fd0bbb443980021f617768873008c5f426ed10e60008bd84dda21cc0071bd07bb4439800a1fa1776487300043ec2eec90e60038de83dd921cc0c933908b9a439800e6721173d03303170f29ea7324602de1f30d4a648c05bc3a61a94c9180b28f616529923000717a94a53246000a9f8354a648c0c553906a94c9180028fa1632992300051ec2c6532460118be87d46648c00117b0fa8cc91818aa7a0f51992300054ec1ea33246000aae82d46648c00155b05a8cc918002a7e0d51992303154e41aa332460118be87c86648c00117b0f90cc9180028fa1721992300051ec2e433246062a9e83c86648c00153b0790cc9180028fa1421992300051ec28433246000c3f75d51648c0071790eaa2c9180028fa1642592300051ec2c84b246000a3e85109648c00147b0a212c918002a760c42592300061fbaceab246000a3f855cd648c0014790ab9ac918002abe09735923000556412e6b246000ab7815cd648c00156902b9ac9181878794f53592300051f42ce4b246000a3d859c9648c00153f06b92c9180028fa1472592300051ec28e4b246061a9e831c9648c00153b06392c9180038bd4a52592300051f42c64b246000a3d858c9648c00147d0b38ac9180028f61671592300054fc1ae2b2460008be87d45648c00117b0fa8ac918186a7a0f51592300054ec1ea2b246000aae82d45648c00155b05a8ac9180022fa1f21592300045ec3e42b246000a3e85c85648c00147b0b90ac918186a7a0f21592300054ec1e42b246000a3e85085648c00147b0a10ac91800eaea0021592300055cc0042b246011cba645c3438c001972c9b82871800e3b21d5258a3008c5f426e2b1460008bd84dc5628c0050fd0a38ac5180021f6147158a3000d36416eca946000a6f825d9528c05b87ee5322a5180038bdca6454a300071610cc8a94602ce1f30991528c059c3a61322a5180b38bc826454a3016716904c8a946000e2f72591528c001c5842b22a5180b38bc816454a3016716902c8a946000c5d76dcd528c001c3cc9b9aa518003879907354a300153743ac4a946002a6c87589528c001c9ee6b12a518003931cd6254a300053640ac4a94602ce4f30589528c059c9a60b12a518
  | 14 => 0x7861c55288555aceec38aa510803595d87154a21005b2c00e2a944286c6f76dc152884014dd0d382a5108029b61a7054a21005b340ce0a944200b65819c15288401ac8e3382a5108029be197054a2100536432e0a94420dc6f765c1528840169f06b82a510802d320d7054a21005b3c0ae0a944200b64815c152884334dd0c382a5108029b6187054a21005a7418e0a944200b4d831c152884016cd02382a510802d96047054a21006b2388e0a94421dc6d7654b31884018bceab1c63108025be1d528c621004b6c3aa518c4220c6f765493188401a5ee8a9263108034b1d1524c621026b338aa5b0442a996c8754960884050fd0fbaac1108029b608755822108c5f426e6b0442008bd84dcd60884058d8eaa92c110a1b1be1d52582210053643aa4b044282c6c8754960884332df0ea90c110803539cd5218221006a6b9aa4304420cd667154860884011f70eb00c1108039a5496018221006b210aebb1a420087d879d763484050ff0ebaec6908021fe0975d8d210043ec12ebb1a4202c5e7594f63484051bf0ea9ec690803690877458d21006d2108e8b1a42008bf845d5634842317908baac6908023ee017558d2101c7c402eab1a4200c3f52dd1634840187aa5ba2c690803271d37358d210046fc3ac631a4200a9c8458c63484050fd0b3b286908021f6167650d210046fc1aeca1a42008ee86dc943484013cd03b9286908063da1b7150d2100cf3416e2a1a42019e4821c543484050fd0b3b086908021f6167610d2103c6e41aec21a4200a9e8650c43484015390ca188690892e32094310d21005ca40a8621a4293f842150c4348401ac842bac6290902a7211638c521006d210ee898a4266c9c631d13148401b48423a26290803271d3634c5210046fc3ac618a425fa9c8458c31484031d90cb8442908cb3a18170885210045fc22e7b0242118bc845cf6048401ac843baac090803710877358121006e2108e6b024232c6f625d46048401ac842ba8c090803710867318121006e210ae630242008fb8758060484071b906baac99801e2fa1f54593300061fbaea8b266007a9e83d5164cc135c3887a92c99819b2710c71593302cc6fc32e5a1e600287e85dd162cc0010fb0bba2c59800a1fa177158b300043ec2ee2b1660118be84dc562cc00117b09b8ac5980b297a0f7654b301762f39eeca966000a6f825d952cc05dc3886b22a5980029be096454b3000d36412c8a966000b1c845cd52cc15169f04b9aa59800e3720d76d0b3003e4e39ac9a1660038dc835d942cc0031790eb22859801f271cd6450b30404cf43e86a1660a7c9f761d132cc0ff93d0c3a2659819327618744cb301264f310e89966024c9c621d132cc14da3ea43a2659829b47548744cb303246e43ac89966064c9c7459132cc0071bd07bacc39825b179ce759873001
  | 15 => 0xcb96861880a1fa1774588310043ec2ee8b10622ea5e83dd9520c45d8bce7bb2a4188029be0976548311752e41ac8a90622ee1c43591520c4014df04b22a4188069b20964548310052fc32e6a906200b1c845cd520c55b69f04b9aa41881e3720d76d083103e4e39ac9a1062018bc87591420c40f938e6b228418a0267a1f43508313fccf43ee899062acc9f761d1320c4ff93d0c3a2641897f27618744c8311264f310e89906224c9c621d1320c557a3ea43a26418aaf47548744c8312064f308e8990627fd96611d1320c4bf1b90eb22641897f271d1644c8310143f42eed208620087d85dda410c4cf93887bb482188063ba0b76904310061f3aac92086207c9e73592410c4cd93886bb0821880317d4b764c4310066b28eec9886200cd551dd9310c4cd33d0fba2621880327ddb744c4310064fbb0e89886200d1f521d1310c48193cc23a2621899b65984744c431006cb288e89886200d95511d1310c4018beeca926218803471d1524c431006a7b92a4988620287e87dd5600c4bb8b8e7baac0188021f60b75580314ce2e398eab0062368dc8754d600c46d1bd0fa1ac0188021fa1f52580310143e43ea4b00620087e87549600c4010f90ea92c0188da3721d32580310054e42264b0062368dc874c5600c4015390898ac0188dab6201315803108c5f426ebb1c42008bd84dd763884010fb0f3aec71080a1fe1d75d8e210061f3ace9b1c4200c3d759d3638840187ceaba6c7108030f5d574d8e210061fa92e9b1c4200c3d525d3638840195ce8b96c7108031d5d671d8e2100672b94e3b1c4200a5e85d8e638840153d09b1cc71080297a177358e210054f426e6b1c42008de87d4d63884018beeba9ac710802b360b5358e210046fc3ac631c420287e859d943884010fb0b3b287108023760e7650e2100c7ac30e2a1c420287e859d843884010fb0b3b0871081e37a0e7610e210054fc328621c4200a9d8650c438840172902a18871081e3be197210e21006c6a1ae421c4200a6e869cd52884014db0d39aa51088f1bdda7354a21005b340ce6a944200b65819cd52884014df0cb9aa5108029b2197354a2100597c22e6a944200b2c845cd52884016cf02b9aa510802d92057354a2147637bb0e6a94421996e87d8d528840165d09b1aa510802cb6136354a210d5b340ec6a944200e4f6398d5288401c9ac631aa51087ed9a046354a2100537c3286a944200a6c8650d52884016cf02a1aa510802d92054354a210053743086a944200a6d8610d5288401e1a8621aa510a2e9b61b7154a21005a741ee2a944200b4d83dc5528850f6cd0fb8aa510a2ed961b7154a2100732c36e2a944200f4683dc55288401e8b07b8aa510802d96037154a2101537c32e2a944202a6c861c552885138deec38aa510a2ad9a1c7154a21006b3438e2a944201b6
  | 16 => 0x2191313370f29ea63226200ab681d4c644c40156b03a98c8988038bd4a52191310054fc1aa43226266a9c83548644c40147d0b190c8988028f61632191310055b40c643226200ab5818c8644c42317d0fa88c8988022f61f51191313354f41ea23226200a9d83d44644c40155d05a88c898802ab60b51191310054fc1aa23226266a9c83544644c40117b0f908c8988028fa1721191310051ec2e423226266a9e83c84644c40153b07908c8988028fa1421191310051ec28423226266a9e83940644c40153b07280c8988462fa1c50191310045ec38a03226266a9e83140644c40153b06280c898802aba08501913100556c10a03226200ab681140644c40156b02280c8988028fa1720191310051ec2e4032262118be87080644c40117b0e100c8988028fa1420191310051ec28403226266a9e83080644c40153b06100c898802ada0420191310055ac08403226211cb4649c7434c40196ec838a869880a3be1d52d89310043fc2ae1b12620287c855c3624c40117d0fb22c4988022fa1c645893121d1f426eca926200a3d84dd9524c4014bb07bb2a4988029b60a76549310051fc22eca926243a3c845d9524c4014df04bb2a4988029ee0176549311653c402eca926200e2c62d91524c40187ee5b22a4988038bdcb64549310071610ec8a926200e2f20d91524c4014df04b22a4988069b20964549310051f430c8a926200e2c62191524c401c5ee4322a4988038b084645493100717900c8a926200a5e86dcd524c4018bcedb9aa4988038719373549310052f430e6a926200e1c641cd524c4034dd0db12a4988038bd93625493100716326c4a926202a6e87d89524c4054d90fb12a49880393dcf62549310072639ec4a926200a6d80d89524c40317908bb6849890237e0d76d093100c5f43ec8a126267c9c73d91424c54b938c9b9a84988022fa1b744c9310045f430e899262248be87d91324c4511790fb2264988a22fa1c644c93108c5e438c89926211c9c645cf414c549878c8bac82988030f9d764905310061ebaec920a6240c9c64dcd414c40187cebb2462988030f5d7648c5310061f3a8c918a6200c3d75192314c4fd8bcecbac62989fb559c5758c5310070f3a8c918a6200e1d75192314c401c3ea4324629880257e1d528c5310070e322a518a6200e4f6254a314c40f1b90cb84629880327191708c5311be6c302e118a6201c6c7254b604c46f93ec73a4c0988022fa1f64581310061fbaec8b026200c3c75d91604c401958e5b22c0988022fa1c64581310061fba8c8b026200c3c75191604c401958e4322c0988032bd93725813100656326e4b0262008fb87580604c40f1b906baac81881e2fa1f54590310061fbaea8b206207a9e83d51640c40156d03aa2c818a6b171cf52590314d70e21ea4b206262c9c43dc1640c4b31bf0
  | 17 => 0x146200c9f76d0d428c4018bccabb665189026721176cca310046ec3ec99946267c9c74d93328c40359d05b26651890237e1d64cca312064f3a2c9994624099c845c7328c40187ccbba265188030f597744ca310061f328e89946200c3d651d1328c44995cc43a265188032b1d1624ca310063ab2ee29946200c75651c5328c4018beecb2a651880393989654ca311464fbb6e89946224c9f761d1328c48193d0c3a2651890327618744ca310068f328e89946200d1d651d1328c44993cc43a265189e763988744ca311264e310e89946279d1f521d1328c4f3a3aa43a2651880637a1f644ca312064e3a6c89946201ace82d91328c4491b90eb226518903271d1644ca31006c63a2c49946200d94741c5328c55d0ff0eb2c83189fa1f61d65906310062f32aed98c6200c5d76597318c4014bf0ca966318803535c952cc6310045fc22eab0462118bc845d5608c46f1bd0f29ac11880b171d653582311bc6f43886b046200c9f7410d608c46f1bd0f992c118802a721132582311bc6f43e62b046237ada80cc5608c4050ff0cba8c1188021f61e651823100637394ca304620087f87594608c4018dce4b28c1188030f99674182310061eb2ce83046200c3e655d0608c40187acaba0c1188031b995721823100636b2ae430462008fb87580608c40187aebaa6c89880a2fe1d54d91310051f42c85b226200a3d8590b644c40147d0a216c8988028f61442d91310054ec1885b226200aae82997644c40155b0532ec8988028fa1662d91310051ec2cc5b226200a3e8518b644c40147b0a316c8988030f5d475d91310051f42ee7b226200a3d85dcf644c40155d05b9ec898802ab60b73d913133f0f29ea7b226200a9d83dcb644c40147d0b396c8988028f61672d913133d4f41ce5b226200a9d839cb644c40147d0a396c8988028f61472d913100717a94a5b226200a3e858cb644c40147b0b196c89899e2fa1f51d91310045ec3ea3b226267a9e83d47644c40153b07a8ec898802aba0b51d913100556c16a3b226200e3751947644c40117b0f90ec8988028fa1721d91310051ec2e43b226267a9e83c87644c40153b0790ec8988028fa1421d91310051ec2843b226200a3e85dc3644c40147b0bb86c898802a760c70d91310045f438a1b2262008bd87143644c4cf53d06286c898802a760c50d913100557410a1b226200aad82143644c40156d02286c898802ad60450d91310051f42e41b226200a3d85c83644c40117d0e106c8988022f61c20d91310051f42841b226200a3d85083644c4cf53d06106c898802a760c20d91310055b40841b226200ab581083644c4011bf06baac8988022fe1d64191310045ec3cca3226200aae82994644c40155b05328c8988022fe1d65191310051f42cc43226200a3d85988644c40147d0a310c8988028f6146
  | 18 => 0xc4010fd0f212cb188021f61e42596310043f43884b2c620087d87109658c4fd4bd06212cb188029760c42596310043f43c64b2c621c87e87c85658c4010fb0f90acb188028fa1321596310051ec2642b2c627ea5e83c85658c4010fd0e10acb189fa1f61c21596310051fc22e0b2c6200a3c845c1658c4014bf06b82cb189fa9720d70596310051f420e0b2c6200a3d841c1658c4fd4bd06382cb188029760c705963100537410e0b2c6200a6d821c1658c4014ed02382cb188729d60470596310043f43e40b2c620087d87c81658c4010fd0e102cb188021f61c20596310051f42040b2c6200a3d84081658c4fd4bd06102cb188029760c20596310053b40840b2c6200a7581081658c4018dce532ec9188031b9c965d92310063732ae5b246200c6d655cb648c4031dd05baec9188023b60b75d92310043fc12ebb246200c6e759cb648c4018daeb396c9188031b9d572d923100636baae5b246200c6e855cb648c4018db0ab96c91880a1fe1f52d92310043ec3ea5b246201c6e72d4b648c4018dae5a96c9188031d5d671d923100672b94e3b246200aae82d92648c40155d05ba2c918802a760c42592310043ec3cca324620087f87594648c40117f0eb20c91899e2fe1d64d0e3133eca21ce3a1c6200e1d65593438c4bf1bf0cb8e87189fb8710d6550e310063ab2ee2a1c6200c75651c5438c4018bccabb087188026761f6410e310070f32ec821c6200e1d65d90438c4f371d05b20871899ae5a076410e3133d4ec3ec821c6200c9d87d90438c401c3d0bb208718803876176410e311254f416c821c6200e8e82d90438c44951d05b208718803a360b6410e311254e416c821c6200e1f52d90438c401d2d03b208718802a76036410e311246fc32e421c6200c9f645c8438c4010fb0f32ec5188021fe1d65d8a310061f32ce9b146200c3d659d3628c40195cc53a6c5188030f99574d8a310061eb2ae9b146200a6d829d5628c4014df04baac51880a1fa177458a310043ec2ee8b14620287e85dc1628c4010fb0bb82c5188031760f7654a310143fc16eca94620287d82dd9528c4018be65bb2a518803174cb7654a310063610eeca946200c6f20dd9528c48747d093b2a5188028f6127654a3100536c14eca946200a6f825d9528c4018df04bb2a5188031b0857654a3100637902eca94620087e871d9528c4010fd0fb22a5188021f61f6454a3100d37416c8a946200a6d82d91528c4018beed39aa5189dad360a7354a310062fbb2e6a946200b1c845cd528c4f169f04b9aa51880317ddb4354a310062fbb086a946200e1f6410d528c40169b0421aa51880a1fa1676d0a310043ec2ceda1462018bc845db428c48193e86bb6851880a1fa147650a310043ec28eca14627ec5c73595428c4018bccbb9a8518803175977350a3157ccf43e86a
  | 19 => 0x2ada0665d91320055ac0ccbb226400c3d751d7644c901c3ca7a9ec8990a2a760f71d91320051f428e3b226400a3d851c7644c80117d0fa8ec8990022f61f51d91324054f41ea3b226400a9d83d47644c85155d05a8ec899002ab60b51d91320051f42ee1b226400a3d85dc3644c85153b06386c8990022fa1c50d91320045ec38a1b226480a9e83143644c80153b06286c8990a2aba0850d913200556c10a1b226400ab681143644c80156b02286c89900237e0d75591320045fc3ac832264a5a9f83590644c823539073b0c8990022f61e651913259d4ec1cca3226400ab681994644c80156b03328c8990022fe1d65191325954fc1aca322647fe1e53d4c644c84955d05a98c899002ab60b531913208c5f43ea232264008bd87d44644c8ff53d07a88c899002a760f511913212557416a23226400aad82d44644c80153f06a88c8991fea720d51191323fd4f41ca03226400a9d83940644c82317d0e280c8990022f61c50191323fd4f418a03226400a9d83140644c84955d04280c899002ab60850191320055b408a03226400ab581140644c84993cec3248699103271927190d3222e4e322e121a6428cac72d91434c82353d0db2286990a3271db6450d321264f3b0c8a1a6411c9c76191434c8bf938c838a8699193271937050d3200c6ec1eebb0a64028f787547614c80187cebb24c2990030f5d764985320061f3a8c930a6400c3d75192614c96393ae6324c2990031d5d761985320045f43ec8b0a64008be87191614c8f393ee6322c2990023de1d61185320147ac3ca230a6402c7675944614c8010ff0ab80c29900a1f21570185320045fc22e030a64118bc845c0614c8050fd0b38ec0990021f61671d813208c5f424e3b0264008bd849c7604c8ab93ae6324c0990022fa1f64581320061fbaec8b026400c3c75d91604c80117d0e322c0990030fdd464581320061e3a8c8b0264b0c9f73191604c80196ec9b8ac0990032d19371581320065bb20e2b026400cb4641c5604c8011f70eb00c09901e2f21d54593310045fc22eab1662118bc845d562cc40f1b906baac59881e3b21d5258b310143f42ee0b16620087d85dc162cc4034d905bb2a5988028fe117654b3121d1e422eca96622ea5c835d952cc4014df04bb2a59880a9ba1d6254b310153643ac4a966200e4f7358952cc45dc98e6b12a5988bb930c56254b3100537c02c4a96622ee4f3058952cc4031790eb22859881f271cd6450b3100e37392a4b06621ca5f865cd658c40163908b9acb188721fa1e62596310051f424c4b2c6200a3d84989658c4018dee5312cb188030fdd274596310052fc1ae8b2c627ea5c835d1658c40147f08b9acb188028f21173596313a53bc0ae6b2c6200a3e849c9658c40147b09392cb189fa97a0e72596310052ec1ce4b2c6200c6f729c9658
  | 20 => 0xa6b9ae530aa400c5e73d8661548334db05b0cc2a92ef595cb61985520062fb9cc6b0aa400a768198d6154975acee5b0ac2a900297a0e61585520049fc22e630aa44393c845cc61548472df04b98c2a92e29d61a61185525cdb2c14c230aa40087f8758461548012ef0eb08c2a92aad9e0961185525bf33b12c230aa400a778758461548018ef0eb08c2a92e29de09611855200733c12c230aa4b7e6772584615496dcc8e4b08c2a90029d20161185525b733902c230aa40095f835c0615485d2b906b80c2a903a5be0970185520063ab0ae030aa40093f845cf605488727908b9ec0a908e5be0973d8152174af41ce3b02a40095d839c760548312db0538ec0a90665be0971d81521643ec3ec3b02a400c7671d8760548018bae731cc0a90029e6026398152004afc1ae3302a42e95c835c660548014bd0730cc0a92835a5cb60981520068fba6e6b02a400c5f62dcd6054801a9ec5b9ac0a9003530877358152006a7906e6b02a400d4d20dcd6054801a3ee839ac0a9003471d073581524d62fb10e6b02a400d4f621cd6054801a984239ac0a90031798073581520062e300e6b02a400d4f201cd6054801a9a4039ac0a900353dcf7258152006a639ee4b02a400d5773dc56054801aa8e7b8ac0a900359dcb7158152006b3416e2b02a400d6582dc560548018eec5b8ac0a900359d8b7158152006b3906e2b02a400d6520dc56054801aaee638ac0a9003551cc7158152006b3b90e2b02a400d67821c56054801ac90438ac0a90031dd887158152006b3b10e2b02a400c76601c560548018e8c038ac0a900359c807158152006b2900e2b02a40087e87d8560548018b8e7b0ac0a90031d1c761581520062e39ac2b02a400c7471585605496bad6e5b02c0a90b717d8a7318152006a7b14e6302a400d4c219cc6054859a9e41398c0a90b353482731815216e2fb12e6302a400d4f625cc6054801a9842b98c0a90b353c817318152166a6902e6302a400c5d7398c6054801ac843388c0a900359e0a7118152006b2414e2302a42dc77629c46054801acec5388c0a90b359c827118152166b2904e2302a41996f825c46054801ac842b88c0a90031d98d71181520063a31ae2302a400d67825c46054801ac904b88c0a90b71dd897118152006b3b12e2302a42cc77605c460548598eac0b88c0a90b359c817118152166b2902e2302a40087d8798460548014bd07308c0a90031d5c661181520063ab88c2302a40097b8758060549696d704b00c0a901ea7a137650f323364e320e2a1e6462c9c64dc143cc8014db053acc39900a1fe1d75987320045fc22eab0e64118bc845d561cc8031b906baac39919f271cf74587320061fa96e8b0e6400c3d52dd161cc8cd938e63a2c39900a1fa1f755833200536c10eab066400c3d75d53644c80517f0eaa6c8990
  | 21 => 0x5250d6210c0153902a1ac421a4fa308543588430054fc0286b108693e8f2050d6210c0f1d90ea92c421803a350d52588430143f42ee2b10860087d85dc56210c014db053acc22180a1fe1d75984430043fc12eb308860287f87d4a6110c010fb0fa94c22180a1fa1f75580430043ec16eab008600a6d821d56010c010fd0fa92c02180a1f21f5258043006b210ce3b1aa41996f825c76354801ac842b8ec6a92ff535cb6398d521752ec3ec731aa400c5d87d8e635497d8bae5b1cc6a90bb935cb6398d520049fc22e331aa44393c845c6635480187ec5ba2c6a90034bd8b7458d520069610ee8b1aa400d2f20dd1635493d87ec43a2c6a90034bd887458d5200696108e8b1aa400d2f201d1635485d8beedb1ac6a9003471d36358d5200697ba6e4b1aa400d2c74dc9635497ba9ee7b92c6a90bb4710d7418d522a4b7c12e831aa40095f8758c635480163908b18c6a92f2d3e096318d520ccb7c12e231aa40096f825da435480187aedb2486a90025be097190d5200cb6412e321aa40096d82dd943548012ed033b286a90025d6067650d52004afc1aeca1aa40096f825d943548032dd0fb9286a900a5ba1b7250d52014b6436e4a1aa40096e81dc943548012db01b9286a90065ba0b7150d52004b6c16e2a1aa40196c821c543548032d905b8286a90065b20a7610d52174ae41aec21aa42ec5c635d843548012df04bb086a90bac7e1d4310d520068fc3a8621aa400b1e8650c43548016390ca1886a9003c3e094310d521258f4128621aa424b1c8250c4354927e1904a1886a9092c32094310d521768fb928621aa42ef0e7250c4354927a3ae4a1886a90bbc35c94310d524d70fb128621aa494f0f6250c435480163902a1886a924fc30854310d520058fc028621aa493f0f2050c43548052dd0cb9086a900a5b2197210d52126a7c1ae421aa424d4c835c84354801a9ec6b9086a90bb5318d7210d52176a721ae421aa443d4d435c84354801a1a86b9086a90025b2057210d52176a618ae421aa40096f805c8435485da9e60b9086a90021fa1a7110d520043ec34e221aa40196c829c443548012df04b8886a90065b2097110d520043fc32e021aa40087c865c043548032dd04b8086a9003479d273d8552006a6b94e7b0aa49ac5f629cf6154801a9ec539ec2a90035308673d8552006a7904e7b0aa400d1e745cf6154801a3ae8b9ec2a9003535c973d85520062fb12e7b0aa400d4f625cf6154801a9842b9ec2a900353c8173d85520062eb9cc7b0aa400a768118f6154801a3ce939cc2a926b17d8a7398552006a7b14e730aa400d4e219ce6154801a984339cc2a900353c8273985520068f3a2e730aa400d1d745ce61548018bec4b9cc2a900353d897398552006a710ae730aa400d4c215ce6154801a9e40b9cc2a9003539cd7298552006
  | 22 => 0x300001e00000180102580300001580101a00a00300180980180c80180980201d00080280c80680100180480380180000380e80080000000180200980100080080d00200080000601280080000480000100280000080000000000001a80000000100180480181900100001480100000480080380000000000000380180080081980580200000000d81000000580200280500700180000582100100e00400080e80680300380780081300500380000580080000780b00001100000300d00400100080000200b00200301400100400000182900100980d01581380680180000000080480b00180600980500581280300000400100100000700780280000180080080000400700280000001f80000080800380680601f00001880680000180200281083580a00900580000200400401700080000380380580280000000e00080b00580200000000000000100600680580100480800080500080580003180481280080081100600b00000600000100080300000100100000001a00180880100180500300480980080000f80000280000000200000180080480e80100000b80080280100a1fa147158a430043ec28e2b14860287e85dc16290c010fb0bb82c52181e37a0f75986430043fc2ae130c860287c855c26190c0f1b906baac12180a1fa1471582430043ec28e2b0486028ef8754b6250c050fd0b38ec4a18021f61671d89430043fc2ae1b12860287c855c36250c051ef0ea8ec2a18031d5d7619854300672b96c330a86008f7875846150c051eb0f288c2a180b1d9d651185430043fc2ae030a860287c855c06150c011df04b80c2a18063b20970185430143f42ce3b02860087d859c76050c031dd0538ec0a18023b60a71d81430047dc3ac03028607c9e87dd94310c0193eebbb28621803275d77650c430054ec16eca188600e1f52dd94310c4933d0fb92862189267e1d7250c430054fc32e4a188600a9d869c54310d2963d0b38a8621802c76167150c4349dc7414e2a188600b8d829c54310c0153f0cb8a862199a67e187150c43334cec30e2a18862499e821c54310c493390438a862180347d487150c43336cb308e2a188666d95611c54310c01b2ca238a8621803655447150c43004cec00e2a18866299f86dc14310cc533b0db82862189267a0b7050c43124ce416e0a188600d1f52dc14310c0133d03b82862198b669837050c43316ccb06e0a188600a9d869c14310c0153f0cb828621802c7e157050c434a58e42ae0a188600b8f825c14310d2771904b828621802e5e057050c43005ca40ae0a1886078dc835d56210c0193f0ea1ac421892a721d435884349e4e43a86b10862489c8750d6210c01d1f04a1ac421892a7a0943588431254e41286b108693e8c8250d6210c4951904a1ac42181fa3dc9435884349f0fa9286b108693e8e
  | 23 => 0x481400080080480180000000500000000000580200300200000080880100480180100180200182781300300100200580000880080480f80080280200680180180180f00180280180080800880300000000080000100181100a00183e80000080000300000180d00500200b00000300501d80000a80000081480100580000080200d80000480480280000680700680f01180281200200000200600080280000080180100000000100000200100280000000100780300100080100000880380080800300000100180080380400b00600080180600180080300380200380200000000200c82f00c80500000400800580300700700100600000300000980101200080f00000980080080000080300100680183180480180180100180400700000200100200180e80380380380280000181200180180200100000181300980700280380100700000000400081600500000380000402380000201c80000100001200300900380000000080000380781b80080180080000000000080100200100080700000400882b00000080000a00200800e00000080400880000a80000000080080000580500080000a00101800280080400000500580800082281d00200f80080100100000000000000e80a80280000481c00080700000580100400600300780400100500080200780280000200080080000080000180800a80700002f80100000000e80200000000000100500000000200580880002780000b80000080080000002100100000000680081680080000380700580000100b01100600200180e00000300000000000600880380000f81400e80900380400100000600000d00080000e00680080a00000000200100501800000300180000400300100300080580101080700080400380000000280000382380480180200380180000000800080300200101f00080280000001c00080180380980000180100300300d01e80100280080280080000280080480900000080200100003580300080480100d80200000380a00d00080880000600000000000180382680080380400080000780700380001400180200080800200100580580100200400780000002200081100080280900100500180480f01380480381100581800401080501700100080080600182681080000480400001c00180400400080483c80080000000100980181280e00080180100780280c80000201602080000000400100080b80000900000380b81700080280580480680a00000500500080100000280080801480400080000080400000000100f81e80000200880400180180181580000280000000000c80600700700100200280100002100700200380000080001400500400000001d00000300380100200000482080400100100080b8040000070000030140018018000000008050008010
  | 24 => 0xb11f604e33f048410a3811a69a252484e814a2bb626fbd300026e172a00031f1ed90f42201d8a194406c252a3196400000034789332984210002590ccea9e48a1920bae4ff00016c167aaa60000298000000322000051318f543020cde09a7056219c19c69528dc6bc000b7361a9d0cb0e5642b014d8000b8d5af04526080670f88a620169370000000af461c9d20bc0000b784fc08f4000a7305e0000b0a57b233a1015886465ed0000000000000000093e00000030b827a6c950eb0e4ab6bad0001a0972c684420ab703fc0a71c780c86ee68700008d67bc0002ae000085017a45a4df8caa75911110e4b58a7d1e686681963fc0c9a8c140a494080a28c8a824411724bd780bfe04817c51e60000830e1c0008f3b3880005960002b48c357550000000001584104584800165c2c30000a9179266254886c16502cf2e993b840c8c52aa28043686f40de00008df50718f2e4e000b7a5cb9c5c000000336000149a0001062bdce965591292de4cdc05e1cf01fd6ec74d03c8f1c62255e5fe192c00025e307133821c4b35f9ab2c0008010000000d3c6dd42a1204bcc52c2bb80016560000e0a60800049a01b9a0400095e5010a300000003f49274000b5a436a8b8def6be2f9a63c00000000000008ca0000000920cb86d360a9c18000000554821000057e2d68854d289af5d0277d4e0000348835c40db8600014900008ba30e1a807e60000000e6c0000005a5948471435200003301d23a61b48f01408bf9605000042b701000245400000036fb0756770000001fdec564abac519bc00000044d000000000019000009a61f65cc00003fe9b954424b81266a1ca81094fa4b141b22b2498811c22f814000015f00008e812a30354e00005704f2396292cd8647b2012ac8e2a3a850fb030f7848b0c80100e0a6562fc1dfccd60dc359a0d461785100027fd26600053505080000fb000170400000058523951f29b6417e25c00042a3af80016704de27b2c7d1f35df5e9122f86c55600009a914f41331f86848de1b74071eb172582e87194b450fb2710e2c894eeafb36d930850e0000790e2035478000181580400000080580000200600480080600280080000200680000280700000200202c00000000100280600880980200000000680080200180080000180000000580002500100380000a80d80000400980280180080000000000980080280780300180100000100400084b80180000000000180080000102480100980080080080100080100580280300580380000080b00000080301880080380d00001400000b80001d00380280480180100002100b80180200080200000400000100100580080100080080304d00800000100100600d82280b00500080880000000a80481180600000280100700580000280800100980000000080300000e80280
  | 25 => 0xdc000121803e0a40001c680000004c3a1808d000047c00000009b010caeae2de00000000008d80001be1c6d430b6d1912ccd1fe6eb80014e04963e780022cd7122f50aa110b092b28a2c80000000000000000000992128305057e8d85dbcbc489e00000000000001d18000fd41a0a1c000000106424bc8d143c8f857205592c57e00004d12ad91d43bd2f4a3c00009530000001810b42be98610f9ab99159188946e00000009ec0000002860f40f2e173a6291fc000b4f0b996794846a22ce206973c34949380010041eb5729b300e00e8113160527e24a3069d789f6a260d1a97c0001194692a7c01e69c2720a70a5615089590712e67215f2ad9d60e91f5098000776344000000000000044e1340b346b612c9be0cd235c60da39098c9630ed000095a00000000003d80002272e401329f63be9099544148056831aa387a135a8fd068651d0dd03b8b680233269ebd12c251ba0ad8cfc28cb3e50f3920a21845295c70146ac5a28000662000064954d7ceb2a469a170a5d8f413580000006435ae93cc44ec3743daa040002215bf05f8e6e0002ad0dad0ee5a60150e94aecba340e111cc9e98539910641165e9d62a500f5a03a59a11e86bc3e8bdfa1bc8f23c82fa8540e760003628000970bcd09b6bd986808727b89727c6afd19a926555024e5ad80008001364468000c786e43779b1d2c241a33507b513ca5d08422bca3537959e0c2ca2c54d50b8a2c5172a604c2dd16de04f4ae15ccb12b8b8000000e90bde5e89bd87287c838380000008fc250153d67c27421e802b4b47341555fdd41a07d151a9bd3e89881c18cf852e29a5b08dd494e41b38556cd8204635869048b0c2693551a948408f14e829ac02600045ac0014b8a0b4d6992b2de0004290670e4e57800003c15da72214ec0012a8a461d081900007865dd92e575211605a01c4c769bd1808058730b722f800eca6e00000b8d2c1440004a5825156e0634f592c80007c53610544d880003a780000000002eb13f434c01217b00008c40000002e1c5d6c3d4ef1b206190000eb80000008d7c7e8000bd48291119ae08b650551682fc0000001d78000a9600000000000003511bda79944e616000000009800000000011364433300000634a45089c00000000000000000000222aa9bcc000a502b7a9997134743fc589ca0c33400000007380004062b58000000544800165aa165019ee0422b5000000000003cb01b0000be45753fe235400016c00000000000000000f2ebbc7421b81aad7c48c34ce8f60dd4b7559a8000000000000000000000030b80014c80003bd0000f020000000d18e1e27c057aaf8d7400028b8494d9c00000021c400000000022f80007a52e48cf14d000042294a417687f4039ee573e4314b587f77b02045891f6039098600024a8c4a00012629545c67a9517a6
  | 26 => 0x67527c4d922f1c403c4a413149a8b80e9cd00008253e03f83ae2fec5fc7ef27323d906044c4a3a1782b240f000136d0241790e01e544aa5e828c1740b867f115b2e3a2f868327290cc7840003ba154421698e299ae1187c0002cb2bbcc720004220124b52aa7094dd8c07c5e200db06042c7310a9922842d02f4f98268cb4234172204c88019721b19e23ac4a12ff800175cae8000023c9087dc0000c093d004b1959140e30929058077cfce07715f11dafb463d302a0905622281e540080002ab07a1af04a59310001c8c45a5a850726ad7d48b40f729293660d3556aad4dfc76f3a61f3800082519c81b08d450257a254919295b0100af48dc65b1a788e20002d82248ecd7ec4d453729b4bce7033c627595b48373669a6cfca18601866680000f10001e743d5b603aa9588172a08001aa0c40a5135aa0b00e2400000001704f28e76109d514c2ace39d04553763ee487afac394003939ab787a445d0b11f747be6332299368000ae12ed8000f681473bbaec89aa00055d2e855b60005c609b0a7c1074560000e94ba716f13ac0000000001e647cc6a758d000099000014aaee0000000029800000054880023773eeb6b1f520e000000034c86952fe1922a38c4c0002bb24aac72a902820002650f1081045420f15aa189276164d03c84e45018d50109bc09fc5d0c74b4037e2fb05362b009c97188f01835f882313905650e807428da3b9461059cdfe5322f199604b586100014d4f3e55d365a1d0c0c6dc12989d4a4e0b80001348baa719004e44107a41e00027b0b046d03c908227aa59416b93c13dac095459d1504ebd41ab9e80bba35d062e0d03441b20cf8180410a9257e06fc0567db0af09821aa80eb4696342ecbe81c30000000bb019405847549510000000000b25e1f8000a7a00009dad315d23671f0825d82c1d90000af0cda8f7000056ce5a471146a67cf9e00001ea1e4000b6c13b890c0006c651194045d89bf8000b50b40a15a2206646fa00028d19e0b64688168a864fcc7ae000248cd5a00000000004536e100000000000001e7a13004948310820a0f36232302255d84e214c77935819a3dc04096fd4429fd248a3288107d4025304895041735dab7c7a28065d2ad4547e2fd01e1a48b182ba3b51cf583c042434a93c7346203fe8000642000375800000000006c095cfaab8f12bda000de00000886d4eba51ca19e9c459454a5348000c3a51580000640000143b60000ef867bda31f100008a080000002f00000002b05338a8e000125d7ea0a31472bb039a065529148d20e0244430220a2a98035e9e40b6902e2d1266c60d4c938610ca8962841922b44ad8409154caa511e8aa13000120000000001e4d1173b2258da2ae149d145319c8f5620718c15096924230002c0c961b0105f2ac000000016a83aceec2c100000001beb
  | 27 => 0xff00020ab47c4e121fae0853c4482e42d09270c01046c9d837a9785e519dd05a829e0982c92ba4800039bdd3dc5951386380af20e02e010e64b085b3719994abe85800e006092112e0ac0b7453e0914afa3d440f0002619c20bec1b300fd3710e08560ce9a688ec7395e716f42b41d803d15d105825d51285a0ae03626141ea8adc0fc11a84dd3462642db09c155e56100017bca3cbed56ea03e3f05ca5f32c74140000000000048f54e45b8a600008481fc99840000f317b8000000bc50a300014005454150000bb845a1eb23993084bb490000160a16e5fd40000002ae0002d5d2447964a0dc08fd4ab92e68e4431840c23a99ec08e2d661515826a87142a026f8e3e9a63c10c587d26980001cac434917368800158110a0d4000061b51b61d8a0d852a20133049c7de78a45080011768ee0ea0be42da22a865251526482100012e8d82bb10001d800000005141f640da4e959300003ee8890002df0ff200000006ec0000000910d614b6aff1a999400002e500000000000004049bd552c3963d400017e81f2000079d4e81325c8430d0441333ab80016601a437da780a2726e581303cff600006f03f50fa76e4959851782bcb131271c9c4a85203000000056800004a28786ee12398620000001d484a158c2ed166800000000017380000000004360310b9c0000000eac00026280028793debcf26f80017230000e912ac00022520f87f178400010d97b12f44bc0001f5ea3e0004e318045e80002cf9134b6200044000014f601a000124c99e9c00c080015d6b3a10517113aa9281578fac55f9f20001cd972434e19b2d4800026f0002dfc2820001e20b11806054505000169c3080ab876ce7e4a52f5b070000ad439e2c70b061dbc3f2c1960009e213a4ec7ce041197295c6dc9b12d0836d58e0d2072985581c17d3e12a84c48a3828906e000017b28020c584c0b12be94342d200052389c72c035f0ea8dd800078400030ad6d245c1dd058d3f8a3b2571b652cc8983e3043cd7e187088874c296b2556c078d76c5923901160532b931c60514b5413f1212da98480210069fad01e47d3c71c38b72ae4234a3ac0b044641b0af6d80b8027524384fe9aa3f42e987c80c240a462d458a725bd6bc8d462d22454a955a64ca42ab080a5013011badf40000000001dd48523c9474000000013c3fa2f3068017546382cd8809dd5c2a08ccfe67c12095608820260001a28000888045251800000946cb0c8150610b2f10b08a279c21aed2945239f1878fc04ac23f5150c1e3227332fe1060388241d4a278471261850929200e611d00f2d5536aa2b16ca0651b35bb2071a390ea03f45881a066e0c731613006aa6751e984c47700005e8129026300021a400063a00040c2b8c236abb08d0580df482019680011ac255c6d8000cf5b5f22ee24553a28033c9
  | 28 => 0xa3c8000c044408f88000b08000187858ea4c2900eee00086b0000c505107c112ce8d018a3d402e934431c4033a4aa5cee4b5800010febda00047606b813600000019cd52a0001d19a910160005da00016760e60760b68d2e000406ac9a66091d4278040a1200014bcf14a8824d315123c856c381189de524c1f45eb8b853a407538001847ba46029d994c1b40005a4c1555207bb5d7a290b20b6e0e8ae6c0004373e61ff8dfa59831821f15301f50002da000000000004f94c40000001974224a844b90f0c294aea4fc9c860000f700000b550e00009a8e1048d93d1c90dd090b096402275d5cc7c03a3128c3f46e5586247125ab915899a997ee18a03301ad6c830c1b89c9859c1c25da8fca1f41f321210e8d5e4704662a90c22a7c4a52f90eda8003b10d1ca4ac2c00aabe576e442122d7f546a8bc317076a22e7a20f792565680000000388ed033d5c1ab297168831b6206d41220d3690114f866e80ef08bc97e600327053951ea074c88000a5c09f000000000048c0000c1800074001600000007b35e230e8000846532800139b519b7600005392fb000053118831732505004480003c58984664b1e566a134802ab1000000138861f47698214229dc3ef06acfae60727a1e3d3f696740f9f7e674342000000025ec3300009e070a8ae1ce8678d940006068d308ac00012e0da091a1521070000000af827c0000e7c23600000000003fd0001adc00000000023820008154491ca000024600007800004f94310c657e41cb2dd18a05293f20a218b4f6a00025e800155c36303c01692ca4e0242a15d630a4056b8000000000024276876846150d9c3437c00015501d80000004ba800000048700000011040000000000f7c00800021c835a5d23c692f96237300000dc89048b8397150c0000001d380016c90000002eccef03e059080014189c206300017280001449aa4a2052210b885f6874730001a313067ec12282b86765cb1f280001541f015a9c905580000d480000006e65ce00a45b60000000ffd23c95a2f700001da4b517b61287f40000c28e4cc167f6159835811c75300025605fe6370002c3e0009131e62bcc8d6a9332ba5c053a652205a53830400023316f8f79af89939e4462488a09a00040007ed218279c00013860ba2fc2589c13f10bbc000a1a4d284d27ae06958218d059873831780000008b50071868eb6000000000000000000000a0000c001d7000077c27d5d59f58e380005881ad12fc0255270450ffe26da7aa32000030953f09c40004cb0001bb41a89a4aab9d5876a81113380010a004d33a00017ac0b7249000024090300020515b26125d425887e21e90ee81640000003321ac0ea4b7b000000162c63249a03a8e6abac0921e6124a000429acc652082e19490eb0d07c7431a4c12fa7a600017f94660004e29c7961c
  | 29 => 0x2ea0a4400000011bef5448117036d098c000bfa46f26a11be8262d1a27cbc83260000eab5f40005c42ce50dc4c70b3d3b40ae47e0e7a3841b205b2172b9ce5372f25b96b8be83b609496bc5261dc31c098f6b81ac01396d4ed61dccd02c81326b156112aa861c38e35708486c07703c1af7c01494d55c2ab04fc38218d92d92248b01181a7cd5099e14de66020659b1a424255dc0394e78b88daa531100895077e23e9ca8d95128b27c84e0e89c61c5481256400096907b00000ac9b4288a5a16526f2000010d1d2a8d3109fe041e27246e26249447674d20000bb40a921a16dd13a3412a6279585e8ce2b68000336747601246c0004b00000e4181600000028f153600041f00004d900029d28d8654000142800062a815a9c885000062300007a831021e3f727e97c0a3a468800000097650a8f04bf69d43ad29e05a02405b890140688d4db281f01804f1096904137e8b95b14f6ceb01644caa4b03ca981000000000043e22b949800ab474ba1e680009180898000fe40004a2023200090600008e0e122a03c2850c54e8d70bc5e9cea0498511276167399043c1e5010c2dc43207254eab1b0000000ed2a635922764b9eb2f4a10524d3a2f300000012109a90001ae4000a8c2e891c83000003201034ea28ab0b5000047c28a92a5d985144961b7a198accb5cddd2ddc0d4a5e4bb9b610b42c817425ed03a2b70001e78c4c1050d8a7d5286a7a0000000808a6c00b63e803a2e92c794a88280000000000ee60001880000f4625b1d02058ec800000000000000004b500000000002de162173a21f00001885f05634be146526a86a3332b894a291654000013423da3f99c586ac54920e80010be895000000000000059f80010760005618c0000000000014280006d651eaef0000bbf5f09dec86400033e9058ee2a7f00008f000000036f000148654118283904f40004259ef429f8cf32600001fc761169a48419e60a2f36b416cc7a4389af8c51e25a128aaac84431f0fe8c0edc40520f5d0d53141b957a9a2d6757fa1dd54537541f90d38bf00e8b1129820149b0acf40b8cb0dbf9043212910476a604c61f252f22294c5873098208030c82f5566bd94e581f97446761d6281900690d43b24e481493a3928875222a670b587981ea90b3b64209182997309904557e17213695a8182b2c55e9450f6071d1342b306a020019194f10ba48e5a08c160a2a580881808ca288e4a49ca97b62e62e2ad5865e28601a830b61e59947f25b580a29a94090ec1428e3132a2a49ae9ea16f843427428681822d8cbeb4302312d15a4af044204982fe9fe50a08ad21848928224297fabee2a90d84d0c08d07392417fe6e70490ccd4923e852a23694a6bef5b1e6e8f12b1da53122058ca8a21c21656885a507c0e2c7da000002304400066300000005e4b8a4ed
  | 30 => 0x17ba2ad05a91dc0662961c01bd62acbc84cb0294d2696c1493018d9e22a0002ee4fbe8b208606505428854159b5c2e20002ec0bb87b296e518a30183e6b25528de1066a0f616a6656b2a320708ec05500005c09830df200004e82e80000159d1143895e3b70000fd875a4ac000093d1ba1661fda5542cd195382c2715908cd5a68f8f05e2ea11a6e91144b372168c1c4173c60cc00016951fb124822463920b29a1334c0637f08c0000b005082a8009e6d49c3166d1906138422c5ab00cf412a3748570b2205f2552ad000034a46a159ce0d14d2d22e3e0006a12e3af181ba843277ac64e088e218e13527ee0d1446048cc0d0000001d108a410200000002aabc319f9a400dc38d16104254486364f10809546a795c700e080ebc741faef84bf9c92e127290e60315cd25595fc9363208b246cc8c62dc2a80fa02e02bf99507d86d4281936b87891911628e4fc0b234a414fd6e09b23249e1d1164fe3789f440002135b5d5f1860c31000000000000000000004666314d727a40000000001df915a2b9453800177a4a95fc2c2ce5268537019fa4515e00fe4d680002fa42380013c81b60bbad20c2085499c22c2b560000b288e400037a05b00000003fe60c9d951a0a562c2180e386177e11803110e7e30f42840c36415469d4bc08814f41c9f2c000b321ada2062ba5d928592b292d49c00326dc64a1005f49ec90a17e422a847885e64530480000e43e4a7380015781e14f8ab8000018d4a080013a67ba1cb8000b980004e7071c0005f73f822401900f91de22f5662c1a00017951329cc49e0718e9caf124f0a88ae244a185191c00067052ca53d2e200000017e8b1c4cc0000000bf225f00024000000005a983bc0007b70001c2c23e5e134b0dcc34049b0000a56e2200003d93f09ba00000007380002c557bc6586da8930000000cd03455b10e643c89e33fa8d6488a3ca2d3aa64000000358a9d8c1e00054d2634b2e90158bacd89f47b154115ac00
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40144d9299576cca3100703989651d1328c40184f865c952cc631126239ce82dcf644c581c16715d4648c53100607e1c6454a314c40184f87d89528c531124a56588150c438840148f9650d7210e2100561245435c8438840144e97d8e6354a2100583a536398d528840124f9858c6354a210141ba5e8610d528840160f9650c4354a21005c12454310d5288401a4586a0f7154a21006c1a1283dc5528857146596a1c7154a2100613dd8835c15288401867762057054a2100619618711c15288449384922054310d2100570640215cc6048401629900856454a3000607e1e6454a318c00184f87589528c630005a864021591218c00181f87d956410d300068320b65590434c001a0c821956410d3000685d9481590434c001a14652056410d3000607e1f85590434c04928e98e096410d3000623e1c82590434c001a0f852096410d300068321482590434c00121e98d496410d301268320b52590434c001a8482e056410d3000625e1c81590434c001a17852056410d300068521481590434c001a87822056410d30006a120881590434c001a17522056410d3000626e1f80590434c04909c985917210d3012523249645c8434c001494915917210d3000507251321d9524c00141e948c076549300051364a301d9524c00144d920c07654930006071d8845cd524c00141c975904354930125832496410d524c001614915904354930006835918210d524c00144d9219676cc930006251d081593324c001c0c62d94744c930006251d081591324c001294946073218530006132197254b314c00181c861d1524c5300061321b72549314c001c17651d0614c53000538640211d9214c00184f87589528c430004a52458650c438800148c9650d7210d2000493e616318d524800144c9758c6354920005832516318d52480016449158c63549200141b25d8610d5248001264916184354920005832594310d524800184c76a0e715492000519259711c552480018678754961185200069120d52584614800164693e05521852000691a0d52d446148001866876146148520124a3a4a8650c43c4001076981d97154b10124a32498650c438400146691e08765491000519e49811d9524400146691c8076549100051964a101d9524400107598040765491000519648101d9524400164691dc8635491000619608769c55244001867821d9715491000519648659da214400126696a1952885100061921a7654a2144001a4486d8d5288510006912186354a2144001c467618d5288510007811906354a214400107598194714811000519648651c520440014649654871481100071118d521c52044001494915d07458c10004a56588150c4304001895762054310c10006855948150c43040016849150c43588100051a64021dd95204001649900856354810
  | 1 => 0x740020443001a81c68000b0a0945f00244002a0026400000000006000006416702a0014a000029c00a64d0010000000008c7a0221d460e429880067000bcfc0000160005200000000000001480000000c9001d2a4bc41000820000001980f2310800aa791ba3c2227000406688000780065001cc000046924e40a2597000a81900144000000400000000000503780080004d9a0004c128010c1a00000b600000f4ac0f0020cf69000000e23600008f042000880000000a41d4d362a87e004a00000000025c0009068e4005a4a9ac00771d80000000004c4826000007c002ea30c2002b800001b00001422e09000003c000003e00160006275000009e8a28851130000210fa0837000188e00164000000000001c002740000449140a8b16836fe92239900c00000013e9810000001d501b48600000012c000a9f0ec182218c700018000001f8000000004e14c006a41120d20000278009300000c01715938190000004000300006000180800030000800040080800000000004000180c00070000814020000400000100000010180000000100002000000810010000802000080008000000001495969447150c4312463249801c54310c4918e92a077050c4312427a638750d6210c4928e98e094358843124a32488150d6210c4928c92e014358843004a3261435496210c4948c9750d5258843004c5a468650c435484930e98e094310d52124c32488150c435484930c92e014310d5200643e61435c8435484950e9850d7210d5212543261435c8435492790c9850d7210d5212443261435c8435480150e9650d7210d5200543259435c8435480150c9150d7210d5200543e41435c8435480154691d8a73d85520061360a73d86615497326592e1d61185520051c241615c0615480145591180735815200513259201cd605480146696208715815200519a5b201c5605480146496480715815200552640215cc60548015619020a711815200615a0d719846054801a0e829976410e310060761d65d90438c401a0e825976410e3160685a0565d90438c40181d876176410e310062361e82d90438c401a0e85a0b6410e310068361682d90438c40121d98d4b6410e3112683a0b52d90438c40189587a076410e310068561681d90438c401a8582a076410e3112427a63645c8438c44948e92d917210e310050725132dd9528c40181f762117354a3100507a5f6410d528c44960e92d904354a3100683d918210d528c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x13000250460089210ea8a59435c8435480128350d2ca1ae421aa424883aa7646084354a3100501d4fb230421aa51889220ca95918210d524c00140653ac8c1086a926000a81285646084354930
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4b
  | 5 => 0x4e
  | 6 => 0x138e
  | 7 => 0x4
  | 8 => 0x94b
  | 9 => 0x94e
  | 10 => 0x124b
  | 11 => 0x124e
  | 12 => 0x138b
  | 13 => 0x98e
  | 14 => 0x128e
  | 15 => 0xcb
  | 16 => 0xce
  | 17 => 0x5
  | 18 => 0x9cb
  | 19 => 0x9ce
  | 20 => 0x12cb
  | 21 => 0x12ce
  | 22 => 0x168b
  | 23 => 0x168e
  | 24 => 0xb0e
  | 25 => 0x140e
  | 26 => 0x24b
  | 27 => 0x24e
  | 28 => 0x144e
  | 29 => 0xb4b
  | 30 => 0xb4e
  | 31 => 0x144b
  | 32 => 0x16cb
  | 33 => 0x16ce
  | 34 => 0xcce
  | 35 => 0x170e
  | 36 => 0x58b
  | 37 => 0x58e
  | 38 => 0xe8b
  | 39 => 0xe8e
  | 40 => 0x178b
  | 41 => 0x178e
  | 42 => 0x95396
  | 43 => 0x94056
  | 44 => 0xd49
  | 45 => 0x1a09
  | 46 => 0xd4c
  | 47 => 0x138956
  | 48 => 0xb0956
  | 49 => 0x94b16
  | 50 => 0x1409
  | 51 => 0x140956
  | 52 => 0x95416
  | 53 => 0x209
  | 54 => 0x249
  | 55 => 0x1449
  | 56 => 0x14c9
  | 57 => 0x139256
  | 58 => 0x138b16
  | 59 => 0x141396
  | 60 => 0x139416
  | 61 => 0x98b16
  | 62 => 0x141296
  | 63 => 0x1440d6
  | 64 => 0x144d
  | 65 => 0x289
  | 66 => 0x1489
  | 67 => 0xd4d
  | 68 => 0xa0e
  | 69 => 0x9cd
  | 70 => 0x180e
  | 71 => 0xb49d6
  | 72 => 0x9cb56
  | 73 => 0x16c9d6
  | 74 => 0x9d6d6
  | 75 => 0x28e
  | 76 => 0xb8e
  | 77 => 0x148e
  | 78 => 0x184e
  | 79 => 0xcc9d6
  | 80 => 0x9ccd6
  | 81 => 0x1709d6
  | 82 => 0x9d716
  | 83 => 0xd0e
  | 84 => 0x188e
  | 85 => 0x589d3
  | 86 => 0x589d6
  | 87 => 0x9c596
  | 88 => 0x18c9d6
  | 89 => 0x18cb
  | 90 => 0x9d8d6
  | 91 => 0x18ce
  | 92 => 0x17c9
  | 93 => 0x134c
  | 94 => 0x252d6
  | 95 => 0x24d
  | 96 => 0x1452d6
  | 97 => 0xa0c
  | 98 => 0x180c
  | 99 => 0xb5696
  | 100 => 0x168d
  | 101 => 0x168b56
  | 102 => 0x28c
  | 103 => 0x148c
  | 104 => 0x168cd6
  | 105 => 0x18d696
  | 106 => 0x1698d6
  | 107 => 0x140b16
  | 108 => 0xb4256
  | 109 => 0xb5456
  | 110 => 0x24b56
  | 111 => 0x24cd6
  | 112 => 0x18c256
  | 113 => 0x258d6
  | 114 => 0x144b56
  | 115 => 0x16d456
  | 116 => 0x1456d6
  | 117 => 0xcd456
  | 118 => 0x144cd6
  | 119 => 0x171456
  | 120 => 0x145716
  | 121 => 0x59453
  | 122 => 0x59456
  | 123 => 0x144596
  | 124 => 0x18d456
  | 125 => 0x1458d6
  | 126 => 0xbcc
  | 127 => 0x40c
  | 128 => 0x160c
  | 129 => 0x14b
  | 130 => 0x8e
  | 131 => 0x198b
  | 132 => 0xa4b
  | 133 => 0x134b
  | 134 => 0x150e
  | 135 => 0x2cb
  | 136 => 0x14cb
  | 137 => 0x20e
  | 138 => 0x19cb
  | 139 => 0xbcb
  | 140 => 0x154e
  | 141 => 0x5cb
  | 142 => 0x3ce
  | 143 => 0x17cb
  | 144 => 0x1a4b
  | 145 => 0xecb
  | 146 => 0x15ce
  | 147 => 0xe8593
  | 148 => 0xe8596
  | 149 => 0x58e96
  | 150 => 0x19cc
  | 151 => 0x4956
  | 152 => 0x5556
  | 153 => 0x14c
  | 154 => 0x1a0c
  | 155 => 0x24211
  | 156 => 0x2c211
  | 157 => 0x28251
  | 158 => 0x1a0d
  | 159 => 0x99556
  | 160 => 0x150996
  | 161 => 0x14d
  | 162 => 0x5c9
  | 163 => 0x9c593
  | 164 => 0xbcd
  | 165 => 0x15cd
  | 166 => 0x59693
  | 167 => 0x580d3
  | 168 => 0x169716
  | 169 => 0x140096
  | 170 => 0x21416
  | 171 => 0x58253
  | 172 => 0x596d3
  | 173 => 0x25716
  | 174 => 0x19cd
  | 175 => 0x144593
  | 176 => 0x592d3
  | 177 => 0x58b53
  | 178 => 0x59a53
  | 179 => 0x58ed3
  | 180 => 0x9296
  | 181 => 0x151296
  | 182 => 0xbc2d3
  | 183 => 0xb0216
  | 184 => 0x2cbd3
  | 185 => 0x20b16
  | 186 => 0x155416
  | 187 => 0x154b16
  | 188 => 0x3d716
  | 189 => 0x1715d6
  | 190 => 0x1a57d3
  | 191 => 0x15ccd6
  | 192 => 0xbc294
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 45
  | 7 => 1599
  | 6 => 5185
  | 5 => 3137
  | 4 => 171
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
  | 8 => packedAt gbK8 (1310+((h/20+packedAt gbK8 (1170+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (66903+((h/645+packedAt gbK7 (59163+(h % 645)*12) 12) % 2323)*12) 12
  | 6 => packedAt gbK6 (275984+((h/1936+packedAt gbK6 (248880+(h % 1936)*14) 14) % 11228)*14) 14
  | 5 => packedAt gbK5 (198631+((h/1129+packedAt gbK5 (185083+(h % 1129)*12) 12) % 4066)*13) 13
  | 4 => packedAt gbK4 (12510+((h/60+packedAt gbK4 (11970+(h % 60)*9) 9) % 315)*9) 9
  | 3 => packedAt gbK3 (575+((h/2+packedAt gbK3 (567+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc07ffffc03fff00fffffff423c7fcf8f1ff
  | 1 => 0xf80ff81f03ffc1ffff07fc07fbdd3a53473e73
  | 2 => 0xfffe003fffe0ffff83ff80c1e3c6387cf9c
  | 3 => 0xffffffc00000fffffc0000fe03f83f80fe0
  | 4 => 0xffffffffffff0000000000fffc003fff000
  | 5 => 0xfff0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x86000a504800212000844a1400040841850a5
  | 1 => 0xd084580a215a41a56906a816a1cd1a51432652
  | 2 => 0x410aad40426cb409b2d033502c162c62858b18
  | 3 => 0x822f3673e806108edce70060cee03783e80de0
  | 4 => 0x44fc79cf3b739c0184201830f7bc003f6f000
  | 5 => 0xe782040080382100e08422040fbfbf78000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36571
namespace PEqualNP.Outside.L_meta_36571
open PEqualNP.Outside.L_meta_36571.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 9 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 68 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 129 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 10 := bs3_3_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 10 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 12 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bs5_4_544 : Interval s5Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 551 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)))) (concat (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384)) (concat (concat bs5_4_416 bs5_4_448) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 666 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 1 := bs5_7_0
theorem alls5 : ∀ k ≤ 7, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bgb_4_160 : Interval gbAtlas 4 160 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 171 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_3136 : Interval gbAtlas 5 3136 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3137 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))))) (concat (concat (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))) (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)))) (concat (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912))) (concat (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136)))))))
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
theorem bgb_6_5184 : Interval gbAtlas 6 5184 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5185 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))))))) (concat (concat (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)))) (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200))))) (concat (concat (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)))) (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))))) (concat (concat (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))) (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))))) (concat (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)))) (concat (concat (concat bgb_6_4864 bgb_6_4896) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992))) (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184))))))))
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
theorem bgb_7_1568 : Interval gbAtlas 7 1568 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1599 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))))) (concat (concat (concat (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960))) (concat (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)))) (concat (concat (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248)) (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344))) (concat (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 bgb_7_1568))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8eeeaeaaaeae8e8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3941132456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36571.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[1,6]⟩,⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.or,[0,7]⟩,⟨.and,[4,9]⟩,⟨.or,[0,8]⟩,⟨.or,[1,6]⟩,⟨.and,[12,13]⟩,⟨.or,[11,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3941132456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3941132456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36571

open PEqualNP.Outside.L_meta_36571 in
theorem PEqualNP.Outside.L_meta_36571 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3941132456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3941132456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
