import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36847.Model
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


end PEqualNP.Outside.L_meta_36847.Model

namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
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

def SBf (j : Nat) : Nat := [6, 7, 5, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36847

namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x400025a809184a031c800c7be42bc42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1180c400940418c420ca58a4a0ce14141a7294632e5290298a4985514530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
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
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xffc0fffffffffffff81ff80fffffffffe38fff
  | 3 => 0x3fff01fff80fe03fffe0fff03ffc0f80fcf3cc
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4a4414423122490a01652a544a2194aa0d3615
  | 2 => 0x909228a442449414580a510a94c629546288ea
  | 3 => 0x230a4d2890e90566aaa09d6227688e06b4d34c
  | 4 => 0x3a2cb1d12481d9bb34d3064c39b3c418df03b0
  | 5 => 0x3c30c1e1c70e1e3dc71ce78f01c30860fbec00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36847
namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xa4d052c0000720440190038c225a28980626d40c24ad09f465402c0000e0000000004a0078008053000018f2f10500275c01803483402a0080e802e2c48200000000004001030c0c0810210300ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x22514742390c2c9c38988de100a104842b0e96d3203431746e51110790877408d8ce000e1547e17258e042583c0a41e00489cc101934000007d2b000dc5e2918d160151985242800215282e000f0b26c00000120600044408d001e80000248600a001a9c8004a058bc00003586c0e9e0d0a81400231b468982a0014864501f07c5318a54ca603f84c76480117d3a9347a7c7a5a199400015000012c45471347482191f81a2400039104c4d8104c8038230d20c41848726a0fa409c44180005a003d800f2760015c000013800cc232000142a2001d400004d21cb80012a5c584f080085000908838003000c00880203008800000384820204820103808b8003090003149000800280800003080383810200050103021208cf54b439f28e873e50d0e7aa921ddd4543ba28a879f5350e7ea4a1edd45439e28a87b45150e68a2a1cf141439f2a0875e53d0abaa7a16794f429ea9e859d53d0a3aa7a14f947429f286853d5490a7ea6a16bd49429e28a853c5050a7ca8214f953329eaa6653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86195794f41aea9e833d539067aa520cf946419f284835f53506b8a6a0cf54c419ea90833e511076ca220cf940419f2a6633d54cc7688398cfd52319e2a4639f438c73a8718e7d5231ce2a4639f428c73a8518d794631cf20c639c418c67ea898cf151319f2a0633d540c73e8618e750c31da208639e540c73aa818e7d0831cea10635e510c7aca218f5d0431cf208639c410c7a88218e5104319f2a6433d54c86bca790d754f219faa4433c54887a86310cfd51219e2a2435f53486b8a690f50c521bda824378504867ca810cf550219ea9c813d529027ca320678c640ce18c813e50902bca6205754c40cf298813d531033aa6204754c409ea90813e511033c6220670c4409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca9084f55210af29c215d53843a863084fd51109e2a2215f53442b8a6885bd4910b6292213f5404278a808750c410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x7036c1802824bc0001e7400066d00252a50600080800020840293ee5120765988b1064bb80e6c08a3824011469c6aa3400c2b00900005a4dbb50a780006001d2658b9900002e2420000140000200204020400a0004008c5d4c5150f1763145439518553d0a346154f42a518553d0b176154f428718553d0b146154f428518553d0a1d6314142a5185438cb1543946328758e544ca3461551328e181544ca946150c3287d8d529061d63942418b588548c69661d5231a3588548c696611523187997428c635651043187597420c6946150831a5986410c6976510431a5594410c6956210431a5980410c61d6315221c51503188714540c521d40c4504861d639502187d8d5290316510c6409518553102346154c40a518553103176154c408718553103146154c4085185531021f658c4408759431102946150f308d987548c21c6550d30a5185434c30d4314930c550c514c21d63953208758c548821d6395310c5950318421d63150108b5885404314540c410
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x200128003110000000938000300000283396c628a87051c5631414290ae5b288218c147158e540860b38ec6a9481411c54314930828e2b1ca9904147158c548820abb0a818821415c8540c410
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (912+((h/16+packedAt s1K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s1K4 (4895+((h/55+packedAt s1K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s1K3 (2420+((h/20+packedAt s1K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s1K2 (505+((h/3+packedAt s1K2 (490+(h % 3)*5) 5) % 22)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf01ffffe03ffe07fe0ffe07fffc1ff01ce7e7c
  | 3 => 0xffe07ffffc0fffffff03ff81fffe0ffff38f8f
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1142108c48824810052ca8a25012915414b0b5
  | 2 => 0x24c52914392484a960556454b6412a0cca565c
  | 3 => 0x42894a209069144aaa0255112aa40ca9630b0a
  | 4 => 0xb1674492241d974d3981861cd39c031bc0de0
  | 5 => 0x8c187871c38e1e7f1ce39e780e3188c1ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaa0aaa0faa0aa00faa0aaa0faa0aa00faa0aaa0faa0aa00faa0aaa0faa0aa00faa0aaa0faa0aa00faa0aaa0faa0aa00faa0aaa0faa0aa00faa0aaa0faa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36847
namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
def s2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8122801816f195c32bc6370c6f985d30
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8b096418ca390a318c424c2510530
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*4) 4
  | 3 => packedAt s2K3 (i*15) 15
  | 2 => packedAt s2K2 (i*26) 26
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (5+((h/1+packedAt s2K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (98+((h/2+packedAt s2K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s2K2 (107+((h/1+packedAt s2K2 (104+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 43 s2Pos s2Neg, 0xee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36847
namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb1c038900314804000a19030210d3cb88101bf43de43bd43dd439d43be42bc42de32dc32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x618a7428240240302c02026bc7552438e292871f5150e38a0a1c754c428faa4651d540ca3aa7a0c7553318eaa2631d531023ea9184755030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x500c0086983548ca0c625513186181544c60e62d5230
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (297+((h/5+packedAt s3K4 (272+(h % 5)*5) 5) % 21)*6) 6
  | 3 => packedAt s3K3 (367+((h/4+packedAt s3K3 (351+(h % 4)*4) 4) % 16)*5) 5
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffff81ffff83fc1fffc1fff83ffe07e79f3f3
  | 1 => 0xe0ffffe0fffffffe07ffe0fffc1fffff9e3c7f
  | 2 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x421888c428905040594c09498129212c28d1b1
  | 1 => 0x882111024122208a0291209224124a50922446
  | 2 => 0x444a22481a440314a8265204ca409505454a98
  | 4 => 0x96b3c4929076b5e734c318c7739c0619f80f60
  | 5 => 0x18c3871ce38739f9c73b9ce063181861ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe8e8e8e8e8e8c8c8e8e8e8e8e8e8c8c8e8e8e8e8e8e8c8c8e8e8e8e8e8e8c8c8e8e8e8e8e8e8c8c8e8e8e8e8e8e8c8c8e8e8e8e8e8e8c8c8e8e8e8e8e8e8c8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36847
namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x2587511f35a1890584f20e0008a83437c000f516d468000000cc2620007a82837a6d546a302960293d1234822b8001c0000738001043969ec3922f0884b8d80c23ee5106b8320d876c5f0640000c0268c61fa77000000000a4d388941c424cc61881f43440c01248044034169440504328002026d0e20fc41c4fc0000048c54887a010340880007416a8d8079b634c3bc6680010484cdc0563585913c16822455c3b98b43c7e4000001ec000002611e4000a1276156815089c922c94d3997f298478fb2681f06792a1c300045c0008e0002fc000aa114500ff8000007600012f37e0011f0b200025c0026c50e058000751da4754b27d0009bc05800000000c082906e00028a2a31e2140006a0b4a10a184a12209000000498254980ba264908000000005c03b1d2438001350003347ac6f0130965350906e1d63ec0002c0460005088f00074077249000000dd8331b80000d88900a0414513a4342b49625703a969392561b2311019e049c001460e10cc2cc0028538a5711a96700099400038506970e985f1ca248bf1a73ca54c8193633e5886984008a5390d9864da2812c24d0006e42a95d20ca2d170d81e64ec1c9b300018cd424821c0bcdb8bd0000011d0000000000017121a0d42b800000644002903ea514000092b4001129ef30a2d0000040007c12208c522998ba2470f21311c99d1709b8000001381bc6b000240000000000008b00007c04e000000004420013a05819e840998481e8000e400621097cb605c194001190000000403003004040300000004004090100000008000000280200007000130000a00c03030010180200402004010340000400048050000502c080080d02c0301011020010501f000020080203804004000081500002068060200000006004030000001002004000000300006034030100104c04064140040001c1403c04000070001500405000010140201002008030080000401040020b80000013010000080402004018000100702001004030040b0000200c1a00c0001408040010380201c1900801008020080904002018160001200002024040000500400000000081e01c05028020440201404000000080003000000010140a08406004000040100000008020540402802004020040900003010060a400bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x1da0000000000026a5c8001d4000000d2019000184aa1980f427c00243000000001504d296518a0618679c7f0421aa49c38000000000001874e081d288870780000a8003260009c00000066d3e173000000de1af42c210908000002a40012d35c104639cf504200001ab3be7a40000045a4293211b1bea540027f32c1fd2280201a8303e9d93bc8a4738b61fe555000360bc0a8a886b41e3dc860a4362338c00000006080028604a2a0002235124a8238a700019cbe1c1470000000f9312000ff00032e000d90002ec000000000000b5312084566a53c81f38e180eb1ec0002ec0000343e9d400000000a043f17d2ac1b4348710007189c9614ce38c0016b344400000a33c6071111a1000234189d5028730fa007000260441ee52496cb30001ba2dcc7000000000931e8000000fea26022001471844bc26c0020a07a3980013733800000000000148d285d0002f00000c2688340003e3e20012ea092560e9479922263a08e1f81205e08c17b000000af24b00093c0000024a00000000000264248d0000790001463e6000072192f256cd021500032c00000180278001ca32a0002196a32858c82911252560b70e900042c000000b6928d500039a0000000042826845909478164b29c2102808000f127851c0004e0406e80000029e000588d41b6020fe23f0000b88a0532940fc9f08613a000001751820003d800250488920001902b0780543e4000000735008ed1995900294000000000380002774080000b9dd000000b79833ae8903c0003148dcf0a7e0a0001140a23c40ac9e9992903490ea882c0368af8462043901d8ec3f62e41325242e7e92a80044e4688c80003c298581ed528640bd1774d600062a184c65254b8003a2324000003cc2bd3018d47a00052821106000d180
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2310c355518c430d5544310c35551cc03097d95300c29c644c030d5545300c27b654c0309798f54c825d63d5320cb18954c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c834e6294f20c795153c831d5454f208f99053c823d6414f20cb55342c82cd6310b20cb55232c82ac644cb20cb55132c834e534cb20ab19121c823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5488620cb95021882e96008620cb953208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d0920b358c424826c654c920ab19132482e8604c9208f990514823d64145209798c514825d63145209b99721482ac6448520ab992204826e62d50209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209b98853082766114c209d584530823e64948208f592520825e63948209758e520823f64544208f191510826d6588420ba580210823e64940208f592500826f65480209ed95200825e63d53109758f54c426f62553109b18954c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c426e62d52109b58b548425f63552109718d548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da5805244354538c5109d195314436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520435553c40109e596100436952840109dd95100435553440109ed9510043695244010
  | 1 => 0xc66f62551319b189544c67b60551319e181544c65e65d0d31b3588434c63e64149318f590524c69c644c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f59253886cd6310a21ab191328863f64542218f191508865f63542219718d508863e64951219bd89544863e65151218f992534863d6494d219b58a534863f6454d218f191534867b6054d219e181534872c54885219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cb553420866d6510821b358c420866d658c821cb55232086ac644c821cb551320874e534c8219bd9521086ac64484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b4254021da109500876a3254021da4c9500876b2154021da485500869d6310b409798e51d025d6394740ab18941d02ad6210e409798e529025d6394a40d398e529034d6394a40cb90e529032c4394a40cb94b429032e5250a40a798e419032e5290640cb948419032e52d02409b988535026d6214d40d3988535034d6214d408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540c714f415031c5350540ab189415031c5390140ab98a405023d6590c40ab588431023f65508409bd89511026c62544408f596411029e63904408fd95401029c63500409ed95401026e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62d52309b58b548c2cd6210e308f992528c23d6494a30a7191328c23f64546308f191518c26f62546309b189518c29e648c6308f992544c25f63551308f994544c25e65cc530c7153314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b3588430c32e5494830cb552520c32e5454830cb551520c31d54cc830a7191320c31d544c830d3949320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3573254430d54c9510c25d658c430a799
  | 2 => 0x410c354362011b2664f081900054400000000490001de0461f10819b40424482a0011a000ea18d3d8578ae0511de000000a22b46a81b96305c38c399c50000289b9a40002a425018228000001d11023a41c0792ba470071231f81d49d9590002940003f1000000605a0fe5a48581e23a460ce1390007c8d68f2000001069960000007f80000000000000000820508000000000000000c814809740004442f1be00071c7b12712e5e00000015c40c228002e28507c94c0ae448989b721e0002f976012000e68da00000000000000688a90bd2a83ac24122296698a010831c53885000076000931500005e8b100000070000000268228569a32e06d80e86621253c5b0621dc6088c9253ec2dc000000005f0e30003fc7d04d99723457cb400012800802010070000000401010050380004c0200c000940a0000000403028000440000003000030000d0000404406004060000004000008010000000001018010040b01001024030040300c0400002004010080000c0000400018050200001c01014010440101c0000801004270040100006000010100100400000000040200007028050040000c0100c000040b0040102808014040000a0100000400000060000402400000020200100c0000000000090400000c0a01c03024000000700c0001c030040f00c0204408014100301000000010000280601c010080300405058050226f62547439b18951d0e6e62943439b58a50d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3f64546328f191518ca3e64942328f592508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320caad6210f419b98a50d066d62943419b98a539066d6294e41d398a539074d6294e41c794f439071e5350e41c794e429069d6310a41c794c429071e53d06418f99443506ad6210d419798c525065d6314941d398c525074d6314941cb90c525072c43149418f997425072c52d0941cb149425069e6390541cb14a415063f6550c418f596421069d63108418fd9541106ac62504419dd95411065f63540419718d501066e62d53319b58b54cc71c63553319b98854cc66d6215331c755343cc6cd6210f31cb95252cc72d5494b31cb95152cc72d5454b31c755332cc69c644cb31c755132cc74e524cb31c7953318
  | 3 => 0xe7000392000001bf0006ac000560005ec00000190000dc00037a5b0961980c0214001020443f8b294d0004a43b0963e20a8280dc068704ed8fb00671000195000000d7000000000000000001d03d8070002e46e80026c00050000000000299790001c8000003f6000701842506bcd41900000e4c894231216cff910098560130a80007210319d1fa2d0000820003284c138000648671480004bcf18001ea528000421324b4a388806a5587890e3c00000007d0000006004127a0000018b000000001070000f8000000001bc1b000000000998003f4768001f522c10ce98de2261a89f064000510001d50002746d80012a0000000027e0005a8aa3fa7f0dd8a7146430d907822a050001860001c000000000000e789c0000010b8c23e60010986d2540010a8003ac0441280000020c0000041e5fcec13a3407b9048af000000c9a1808c4b9070653c43c0a482113c5b81987a2b6230001212de1b8340103be27cb501b1da37cc51e83624c0628b10b80bd0d0280a847ca99e63ae45ce58e53da7e0001e5000000001e70000000000001a3186b00018e67c00071000000de000058774f59044065183180026a0005d00004e7dcc0800000000001a10005c8470d70b06e80017d000000958490000001d204422330690b011e00053000000000000000000000000021a30c0001f000000560002ae000040b83988580000009e350168001cc164a08000000008f0172aa50cf813217834c000000005f8000f70c2070ec80000032ce90000000589e000366770b5800360400000243d2008830bf00059cc01d0026148da8f30007a80a8e10005dc001450000c0f79752da0ac73a191566143b8b20d2390688ea33c000d380b4143e8d28f8000324000002362f800000096240149662e66d023a070405845d80031000000000088000000000002480780037206852001080000000002c02247a1ac06433c0004d4160006c08b134210001c31827e4e103c4242cc000e8328000000000ce000000001c41f80203d30e668000c4000630c7800000000029a92c8340270551d83340005d3060004380000048000031418000000930d6728091e
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x24030550f1804530cd00e0000006070010121000085d540a0160022c0001000861818358d6215132a1ae529a8720d0d731494250707318a520a83435c86355331838ecaa26598d0d7318954086163b2a899043525cc4254021a50e8992a010d28744855008686b9ca4a14818398e5290640a1ae429a86a060c53189415030629cc520281435c86355030838ecaa264185457210d510c28a3a264a886185991518c430c28c8a8a601850d7318954c82163b2a8996418a9516008620
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x688080d8798c529054180d8798e529064080d8714c625054080d8714e6290140
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 876)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 1 => 0x884110480a400502882082420844a50622486
  | 2 => 0x144aa290354906a58444d50b540a950b054b18
  | 3 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36847
namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x113c00000001c214584cba90008596441500600a9292008ce241c0cea60268c0a18ac010005402d3e3c008326c6a84e844820030ce0103801c8501244ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x11488fd195d3d49258800012131386c0000380034b428bc0158f89d757c6808780044503c740000001001500140498098acc484e92904b900591c8d6ca53570cd854cb0f030a8247c64000108140040c8940000000c000000015568dc9000f4e4d1601c012c00a02d787000d455644c0480014418e0d90c2000ecc001100000605c0a001c000a020408360200060e060414082200340c02120034021400080216121b765110eeaa221cf94a429ea8c853e5210b5ca4214f544429f2a6653d54ccaeca3995d547329faa2653c544ca7ca5a0cf55241af29c835d53906dea4a0db14941d7a92833c5250758a4a0cb14941dba8a833e54106bca620d754c41cf216639c42cc73e8398e7507319f2a4633d548c6baa718ed50631daa0a639e424c7388498f5d4531cfa0a63d6414c73a8298f550531caa0a633e540c67aa818d794c319faa6433c54c87aa6390cf952219eaa4435e53886baa710eb10a219faa2433c544867ca810cf55021af298435d53087588410f54c421bd280437950086dca5205b54a40afa9a815c535027ea8984f151309f2a0613d540c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209f2a6213d54c42bca7885754f10ea98e21d5314427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1300d00e48c50a4402064050c40402c01c20093c6020314468c6250731a9189418c6a46250531a5584424c6956490531a3189414c6c46250531e1d89414c6946250531e1189414c6846250531c5d5131c862d6510821c55513108784424c421ca1095008751315402195584535032442145208b18954c4315544c710
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x84050575109310878021262a8043411c9544c710
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
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 130)*8) 8
  | 3 => packedAt s5K3 (833+((h/7+packedAt s5K3 (798+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s5K2 (149+((h/1+packedAt s5K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fff07ffffc3e0f87ff87fe1fffe07c39f3f3
  | 1 => 0xfc3fff83f0fffff00787f8ffe3c0fffe263c9f
  | 2 => 0xffc1fffc00ffc3fff807ff0ffc00ff83c7cf1c
  | 3 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 4 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x48041110a0204002810981120452212808d131
  | 1 => 0x11092209094a225042c248a522844a52222486
  | 2 => 0x28944520629004a58804920a480a9508c54b18
  | 3 => 0xb2a9884a481aab3954d0408d932c0613700ec0
  | 4 => 0xc3310e738ce333ce676764c102301863bfb000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8fae8eac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36847
namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x24719000c62652897800000a003e68f06005922e00c15807e41f0224dc5280a2079778e5084746d18068343ad4ef4a9102940335875b2a00d401c76010000001c0b624c00000c8018070008001041c0821210f0000048801200900017fd5005fe54017f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4301ffd4801fe52007f54807fc52017fd0805fe42006f90805fd42017f10805bc42007fcc801fe32007f4c801fc3201ffd4403fe51007f54403fc51017fd0405bf4100ff90405fd41006f50403fc41007fcc403fe31007f4c403fc31007fc8403fe21007f48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x804004ff4c020027f86010013ff2008009f79004004ff88020027f44010013fd2008009f69004000fe48020027fe2010013fc1008009ffb2c2004bfd9610027fccb0800efe6584009feb2c2000bf59610027f8cb08012fc6584009ffb242004bfd9210027fcc90800afe6484009feb242008bf59210027f8c908012fc6484011ffaa42008ff95210047faa908023fc5484009ffb1c2004bfd8e10027fcc70801efe6384009feb1c2000bf58e10027f8c708012fc6384013ffa9c2000ff94e10007faa708027fc5384011ffa1c2008ff90e10047fa8708023fc4384009ffb142004bfd8a10027fcc508002fe6284009feb142000bf58a10027f8c508012fc6284013ffa942000ff94a10007faa508027fc5284011ffa142008ff90a100077c8508023fd4284011fe2142008ef10a10007fe6508003fe3284001fe9942000ff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003dfa0c2001ff9061000ffa8308007bd4184003fe20c2001ffcc61000ffc6308007fd3184003fe18c2001ffc861000ffc4308007fd2184003fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fd1042004ff48210007f24108013fc2084009ff8842004fdc421000ff62108013fc1084009fc0842000ffd9510005feca880037f65440013fb2a2006ff9951001dfcca88003fd65440017eb2a2006ff1951001df8ca880037c65440073e32a2005ffd911002dfec888017fe64440057f3222005ff5911002dfac888017fc64440057e3222005ffd511002ffca888017fd544400bfe2a22000ffd8d10005fec688003fe634400f7f31a2000ff58d10005fac688003fc634400f7e31a2006ffd4d10007fca688003fd534400dfe29a2005ffd0d1002ffc8688017fd434400bfe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122006ffd4910007fca488003fd524400dfe2922005ffd091002ffc8488003be424400bfea122005ff1091002f788488003ff3244001ff1922000ff4c910007f86488012ff6144003ffa8a2001ff9451000ffaa288007fc5144003ffa0a2001efd051000ffc8288007fd4144003dea0a2001ff1051000ffe6288007fe3144003fb18a2001ff4c510007ea6288007fc3144003ff90a2001ff8851000ffa4288007fc21440037fb022006ffd4110027fca088003fd5044009fe2822005ffd0110027fc8088017fd4044009fe2022000ffcc110027fc6088003fd3044009fe1822000ffc8110027fc4088003fa2044001fe9022000fe48110027f84088007ff1044003fd8822004ff84110027ec2088013fc1044009fa0822001fe04110
  | 1 => 0x3fd5188025fe28c4013ffd062009f7e831004bfe4188027fea0c4000ef50620097f88310003ff3188025ff18c4000ff4c620097f86310003ff2188025ff10c4000ff48620097f84310012fe6088009ffa844004ff94220027faa110013fc5088009ffa044004ff90220027fa8110013fc4088009ff9844004ff8c220027fa6110013fc3088009ff9044004fbc8220007f64110013ff1088009fe0844000ffd9520005feca90047fe65480077f32a4000ff59520005faca90047fc65480077e32a4010ffd9120085fec890003bf64480015fb224010ff99120015fcc890043fd64480217eb224010ff19120015f8c890043bc64480055e3224010ffd5120087fca890043fd5448021fe2a24000ffd8d20005fec690003fe634800f7f31a4000ff58d20005fac690003fc634800f7e31a4011ffd4d20007fca690003fd5348023fe29a4010ffd0d20087fc8690043fd4348021fe21a4011ffd4920007fca490003fd5248023fe2924010ffd0920087fc8490003be4248021fea124010ff10920087788490003ff3248001ff1924000fb8c920007fa6490003ed3248001fe1924000ffd8520005fec29003ffe61480037f30a4000ff5852007ff8c290006fc6148023ffa8a400fff94520007faa29003ffc5148021ffa0a4010efd052007ffc8290043fd4148001dea0a400fff10520007fe629003ffe3148001fe98a400fff0c520007fe4290003ef214801fff10a4000ff48520007da429003ffc2148023ffa824004ff94120007faa090013fc5048021ffa024004ff90120087fa8090013fc4048001ff9824004ff8c120007fa6090013fc3048001ff9024000fec8120027fc4090013ee204801fff8824004ff04120027feca10012ff6508009ff3284003bf99420027faca10002fd6508009fe3284004bf19420027fec810012ff6408009ff3204002bf99020027fac810032fd6408009fe3204004bf19020067fea810033fe5408019feaa0400cff15020027fec610012ff6308009ff3184007bf98c20027fac610002fd6308009fe3184004bf18c2006ffea610003fe5308001fea98400dff14c20067fe8610033fe4308019fea18400cff10c20075fcc410037ff5208015ff2904000ff54820057f8a410033ff4208015ff210400aef90820067fa841002bfc4208015de2104000ffcc820057fc6410003fd3208015fe1904004ffd8420027fcc210006fe6108009feb084000bf58420027f8c210012fc610801bffa88400bff94420007faa21002ffc5108019ffa08400cefd042005ffc8210033fd4108001dea08400bff10420007fe621002ffe3108001fe988400bff0c420057fe421002ffe2108001fe908400aff08420025fcc010013ff5008009ff2804004ff54020027f8a010013ff4008009ff2004004ff50020027f88010013ff3008009ff1
  | 2 => 0x300c7fc8418003be420c031fea106018ff108300c778841801fff320c00fff1906007ff4c83003ff86418013ff610c009ff3086001bf98430027ecc218006f6610c009feb086000bf58430027eac218002f5610c009fe3086004bf184300cffea21805ffe510c001fea886017ff144300c7fe8218063bf410c02fff2086018ff504300077a821805ffc410c00fff9886007ff8c43003ffa621801ffc310c001ff9086017ff88430007fa421805ffc210c0097f3006004ffd4030027fca018013fd500c009fe2806004ffd0030027fc8018013fd400c009fe2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba601801ff9300c009ff8806004ff04030057fecb90002ff65c802dff32e4003bf99720006fccb9000e7e65c8001feb2e4000bf59720006facb900027d65c8015fe32e4003bf19720057fec99003aff64c801dff3264002bf99320077fac99003afd64c8015fe3264002bf19320077fea99003bfe54c801dfeaa6400eff15320057fec790002ff63c8001ff31e4007bf98f20007fac790002fd63c8015fe31e4007bf18f200b7fea790003fe53c8001fea9e4016ff14f20077fe879003bfe43c801dfea1e400eff10f200b7fea59002bfe52c8001fea96400aff14b20077fe859002bfe42c8015df216400eff50b20057f8859002bbc42c8001ff996400aff8cb20007dc6590003fd32c8001f6996400aff0cb20057fec390057fe61c80037f30e4000ff58720005fac39002bfc61c80037e30e4016ffd47200affca390003fd51c802bfe28e400effd07200777e8390057fe41c801dfea0e4000ef507200aff88390003ff31c802bff18e4000ff4c7200aff8639002bff21c8001f790e4015ff88720007fa4390003ed21c8015fe10e4016ffd4320027fca190003fd50c8009fe286400effd0320027fc819003bfd40c8009fe2064000ffcc320027fc6190003fd30c8009fe1864015ffc4320027f82190013ff65880097fb2c4004ff9962001dfccb100137e65880073f32c4004ff59620005facb100137d65880013eb2c4004ff19620025f8cb10013ff64880097fb244004ff99220015fcc910013be64880055f3244004ff5922009dfac910013bd64880015eb244004ff19220025f8c91004fff5488027ff2a44013ff5522009ff8a910013ff63880097fb1c4004ff98e2003dfcc710013fd63880017eb1c4004ff18e20025f8c710053ff5388001ff29c4000ff54e200a7f8a71004fff4388027ff21c4013ff50e2009ff88710042fd6288029ffa944000ff94a20007faa510053fc5288027ffa144013ff90a200077c851004ffd4288027fe2144013ef10a20007fe6510003fe3288001fe9944000ff0ca20027fec310013fe61880037f30c4004ff58620005fac310013fc61880097e30c4014ffd4620097fca31000
  | 3 => 0xe324601effd52300f7fca91807bfd548c03dfe2a4601bbf58e300fffea71801ffe538c001fea9c6007ff14e300f7fe871801ffe438c03dfea1c6007ff10e30027fec518013fe628c0017f3146004ff58a30005fac518013fc628c03fffa946000ff94a30007faa51807ffc528c03dffa14601eff90a300077c851807bfd428c03dfe214601eef10a3003ffe6518003fe328c001fe9946007ff0ca30027fec318013fe618c0037f30c6004ff58630005fac318013fc618c0097e30c601fffd46300effca318003fd518c03bfe28c601effd06300f77e8318077fe418c03dfea0c6000ef506300eff8831801fff318c03bff18c6000ff4c63003ff86318003ff218c03bff10c6000ff486300eff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc23003ff66118013ff108c009fe0846000ffd9530005feca980037f654c0013fb2a601cff9953001dfcca98003fd654c0017eb2a601cff1953001df8ca980037c654c0073e32a601bffd91300ddfec898003bf644c0015fb22601bff99130015fcc89806ffd644c0377eb22601bff19130015f8c89806fbc644c0055e322601bffd51300dffca89806ffd544c037fe2a2601cffd4d3003ffca698003fd534c00ffe29a601bffd0d3003ffc869806ffd434c00ffe21a6000ffd8930005fec498003fe624c001feb126000ff18930005f8c498073ff524c001ff2926000ff549300e7f8a49806fff424c037ff2126000ef909300dffa849806ffc424c037de2126007ffcc930007fc6498003fd324c00ffe1926000ffd8530005fec29806bfe614c0037f30a6000ff585300d7f8c298006fc614c039ffa8a601aff94530007faa29806bfc514c037ffa0a601befd05300d7fc829806ffd414c001dea0a601aff1053003ffe6298003df314c035ff18a6000ff4c530007ba629801ffc314c001ff90a601aff88530007fa429806bfc214c039ffa826004ff94130007faa098013fc504c037ffa026004ff901300dffa8098013fc404c00fff9826007fecc130027fc6098013de304c035ff8826004ff04130027feca18012ff650c009ff3286003bf99430026fcca1800e7e650c009feb286000bf59430026faca180027d650c009fe3286004bf19430027fec818012ff640c009ff3206002bf990300277cc81800abe640c009feb206018bf590300277ac818002bd640c009fe3206004bf190300c7fea818063fe540c031feaa06018ff1503003dfcc61801fff530c00fff2986007ff54c3003ff8a61801fff430c00fff2186007ff50c3003ff88618013ff620c009ff3106000bf98830027dcc418002ee620c009feb106000bf58830027dac418002ed620c009fe3106019ffd4830007fca418003fd520c033fe2906018ffd08
  | 4 => 0xf7c519404dffa0ca026efd065012ffc832809bfd4194001dea0ca025ff10650007fe6328097fe3194001fe98ca025ff0c650007fe4328097fe2194001fe90ca025ff08650025fcc128013ff5094009bfa84a003fed4250027f8a128013f85094009ffa04a004ff90250027fa8128013fc4094009ff884a004ff04250025fecaa8093ff64540497fb22a024ff99150015fcc8a8093fd64540497eb22a024ff19150015f8c8a800fff5454007bfaa2a003ff9515001ffaa8a80937d5454007fe2a2a000ffd8d50005fec6a8003fe6354001feb1aa000ff18d5003df8c6a800fff5354007bfa9aa003ff94d5001ffaa6a80037d5354007fe29aa024ffd0d50127fc86a8093fd4354049fe21aa000ffd8950005fec4a8003fe6254001feb12a000ff18950005f8c4a800fff5254007ff292a000df9495001ffaa4a800ffc5254007be292a024ffd0950127fc84a8003be4254049fea12a024ff109501277884a8003ff3254001ff192a000ff4c950007f864a8003ff61540017fb0aa023ff9855000dfcc2a8003fd6154047fe30aa001bf1855001ffea2a800f7f5154007ff28aa003ff54550006faa2a800ffc5154049ffa0aa024efd055011ffc82a8093fd4154001dea0aa023ff10550007fe62a808ffe3154001fe98aa023ff0c550007fe42a808ffe2154001fe90aa023ff0855001dfec0a800fff5054007fda82a004ff94150026fca0a8013fc5054009be282a003fe14150127fe80a8013fe4054049fea02a004ff1015011ffe20a8013fc105400fffb2e6007bfd973003ffccb9800efe65cc00ffeb2e6000bf5973003ff8cb9801efc65cc00fffb266007bfd933003ffcc99800afe64cc00ffeb266021bf5933003ff8c99801efc64cc043ffaa66021ff9533010ffaa998087fc54cc00fffa9e6007ff94f3003ffaa79801ffc53cc00fffa1e6007ff90f3003ffa879801ffc43cc00fffb166007ff98b30005fcc59801ffd62cc0017eb166007ff18b30117fea598003fe52cc001fea966022ff14b3010ffe8598087fe42cc001df2166021ff50b3010ff88598087bc42cc00fff9966007ff8cb3003ffa659801ffc32cc00fffb0e6007ff9873000dfcc39801ffd61cc0017eb0e6007ff1873000df8c39808bff51cc041ff28e6000ff54730107f8a398087ff41cc043dfa0e6020ff9073010ffa8398003bd41cc041fe20e6007ffcc73003fbe639801ffe31cc00ffe98e6000f74c73003ff86398003ff21cc041ff10e6000ff48730107f8439808bff50cc009ff2866000ff54330027f8a198087ff40cc009ff2066021ff50330027f88198083ff10cc009fe0866004ffd9630025fecb18013fe658c0077f32c6004ff59630005facb18013fc658c0097e32c6004ffd9230025fec918013fe648c0057f3246004ff592300f5fac918013fc648c0097
  | 5 => 0x8f21007fcc79081efe63c8401feb1e4200bf58f21057f8c79081efc63c8455ffa9e4200ff94f21007faa7908abfc53c8453ffa1e4229ff90f2114ffa87908a7fc43c84037f316422affd4b21057fca590803fd52c8415fe2964229ffd0b21057fc859082bbe42c8453fea16420aff10b21057788590803ff32c8415ff1964200ff4cb21057f86590806fd61c8403ffa8e4201ff9472100ffaa390807fc51c8403ffa0e4201efd072100ffc8390807fd41c8403dea0e4201ff1072100ffe6390807fe31c8403fe98e4201ff0c72100ffc4390807ee21c8403fb10e4201ff0872100fd8439082bff60c8401ff3064204bf98321007fac190802fd60c8415fe306422affd4321157f8a1908a7ff40c8453ff2064229ff5032114ff88190807ff10c8403fe0864200ffd9521005feca908037f65484013fb2a4228ff9952101dfcca90803fd65484017eb2a4228ff1952101df8ca908037c65484073e32a4227ffd912113dfec890803bf64484015fb224227ff99121015fcc89089ffd644844f7eb224227ff19121015f8c89089fbc64484055e3224227ffd512113ffca89089ffd544844ffe2a24200ffd8d21005fec690803fe634840f7f31a4200ff58d21005fac690803fc634840f7e31a4228ffd4d21007fca690803fd5348451fe29a4227ffd0d2113ffc869089ffd434844ffe21a4201bfd8921147fea490803fe5248401fea924228ff1492113ffe849089ffe4248401df2124227ff5092113ff8849089fbc4248401ff9924200ff8c921007fa6490803fc32484037fb0a4201ffd452100ffca290807fd5148403fe28a4201ffd052100f7e8290807fe4148403fea0a4201ef5052100ff88290807ff3148403ff18a4201ff4c52100ff86290807ff2148401fb90a4201ff8852100fdc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090812fc6048451ffa824228ff1412113ffe809089ffe404844ffea024227ff1012100ffe2090807fc10484077eb2ca004ffd9250025fec928013fe64940057f324a004ff59250135fac928013fc64940097e324a003ffd525001ffca92800ffd5494007fe2a4a004ffd8e50027fcc72801efe6394009feb1ca000bf58e50027f8c72800fff5394007ff29ca000df94e5001ffaa72800ffc5394007be29ca026ffd0e50137fc872809bfd439404dfe21ca004ffd8a50027fcc528002fe6294009feb14a000bf58a50027f8c52800fff5294007bfa94a003ff94a5001ffaa5280037d5294007fe294a026ffd0a50137fc8528003be429404dfea14a026ff10a50137788528003ff3294001ff194a000ff4ca50007f86528013ff6194009ff30ca001bf98650027fac328002fd6194009fe30ca004bf1865001ffea32800ffe519404bbf28ca003ff5465001ff8a328
  | 6 => 0x3dfb0a8201afd85410176ec2a0807bf5150403df28a8201ef5454100f78a2a0807be3150403de18a8201ef8854100f7842a0803bf6050401df3028200ef5814100778c0a08bfbf505045fde2828201efc414100f7820a081fff65cc40f7fb2e6207ff9973101dfccb9881f7e65cc4073f32e6207ff59731005facb9881f7d65cc4013eb2e6207ff1973103df8cb9881fff64cc40f7fb266207ff99331015fcc99881ffd64cc45b7eb266207ff1933103df8c9988b7ff54cc45bff2a6622dff5533116ff8a998806fe63cc40fffa9e622ef7d4f3103ffca79881ffd53cc40ffe29e6207f714f3103ffe879881ffe43cc40ffea1e6207ff10f3103ffec59881ffe62cc4017f3166207ff58b31005fac59881ffc62cc45dffa966200ff94b31007faa5988bbfc52cc45bffa16622dff90b310077c85988b7fd42cc45bfe216622def10b3103ffe659881fdf32cc40fff1966207ff4cb31007ba659881ffc32cc4037eb0e6201ffd473100ffca398807fd51cc403fe28e6201ffd073100f7e8398807fe41cc403fea0e6201ef5073100ff88398807fe31cc403ef18e6201fd8c73100ff86398807dc31cc403ff10e6201ff0873103ffec19881ffe60cc4097f3066207ff58331005fac19881ffc60cc45dffa86622eff1433116ffe81988b7fe40cc45bfea06622dff1033100ffe2198807fc10cc401ffb2a6200bfd9531167fcca9880efe654c401feb2a6200bf59531167f8ca9880efc654c457ffb22622bbfd913115ffcc89880afe644c457feb22622bbf5913115ff8c89880afc644c457ffaa2622bff9513115ffaa8988affc544c4037fb1a622cffd4d31167bea69881ffe534c401fea9a6207ff14d31167b8a6988afff434c40fff21a622bff50d3103ff88698803ff624c4017fb126200ff98931007fac498803fc624c4017e312622cffd4931007fca498803fd524c459fe292622bffd093115ffc8498803be424c457fea12622bff1093115f78849881fff324c401ef9926200ff8c931007fa6498803dd324c40ffe1926201bfd853100ffea298807fe514c403fea8a6201ff1453100ffe8298807bf414c403ff20a6201ff5053100f7a8298807fc414c403ff98a6207fdcc53100ffc6298807de314c403fe18a6201f70c53100fe86298807fe214c403fe10a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c0988b3ff504c459fe282622bffd013115ffc80988affd404c457fe2026201ffc413100fee2098807fc104c415ffb2e4200bfd9721157fccb9080efe65c8401feb2e4200bf59721057f8cb9080efc65c8415ffb264229bfd93210577ec990802bf64c8453ff3264202bf9932114ffac9908a6fd64c8415fe3264202bf1932105778c99080abc64c8453ffaa64229ff9532114ffaa9908a7fc54c8415ffb1e4200bfd
  | 7 => 0x99003fd614c86bfe30a6401bf185321bffea2990d7fe514c86bfe28a6436ffd05321b77e82990d7fe414c86dfea0a6435ff105321affc629901ffc314c86bff10a6435ff08532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c86fffa826437ff141321b7fe80990dbfe404c86dfea026436ff101321affe20990d7fc104c815ffb286407bfd943203ffcca1900efe650c80fbf32864039f9943203ffaca19002fd650c80fbeb2864009f59432057f8ca1901efc650c815ffb206407bfd903203ffcc81900afe640c80ffeb206432bf59032057f8c81901efc640c865ffaa06432ff95032197faa8190cbfc540c80f7f3186407ffd4c3203ffca61901ffd530c80ffe2986407ffd0c3203ffc861901ffd430c80ffe2186434bf9883219ffea41902bfe520c801fea90640aff14832197fe841902bfe420c815df2106432ff50832057f8841902bbc420c80fff9906407f7cc832057fc641901fee320c80ffe9906400f74c83203fda641902bff610c80fff3086401bf9843203ffac219002fd610c815fe3086401bf1843219ffea2190c7fe510c863fe2886432ffd04321977e82190c7fe410c865fea086431ff1043203ffc621901ffc310c863ff108640aff08432057fec01901ffe600c8097f3006407ff58032005fac01902bfc600c867ffa806433ff14032197fe80190cbfe400c865fea006432ff1003218ffe20190c7fc100c8037fb2aa230ffd9151185fec8a88c3fe64544057f322a230ff59151185fac8a88c3fc64544057e322a203ffd515101ffca8a880ffd5454407fe2a2a200ffd8d51005fec6a8803fe6354401feb1aa200ff18d5103df8c6a880fff5354407ff29aa200df94d5101ffaa6a880ffc5354407be29aa230ffd0d51187fc86a88c3fd4354461fe21aa200ffd8951005fec4a8803fe6254401feb12a200ff18951005f8c4a880fff5254407bfa92a203ff9495101ffaa4a88037d5254407fe292a230ffd0951187fc84a8803be4254461fea12a230ff109511877884a8803ff3254401ff192a200ff4c951007f864a8806ff6154403ffa8aa203fdd455100ffca2a88077e5154403fe28aa201df1455100fe8a2a8807ff4154403dfa0aa201ff9055100ffa82a8807fc4154403ff18aa201ff0c55100ffc42a8807fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a204bf1815101ffea0a880f7f5054407fe282a230ffd0151187fc80a88c3fd4054461fe202a201ffc415100ff820a8803bf655045fdf32a8200ef5954117f78caa0803bf6350401df31a8200ef58d4100778c6a08bfbf5350401df29a8200ef54d4117f78a6a0803bf6250401df3128200ef5894100778c4a0802bc625045fdfa928200ef949410077aa4a08bfbc5250401df9928200ef8c9410077a64a0803bc325040
  | 8 => 0xf5864205778c3210fbbf519087bdf28c843def146421ef7c63210f7bc319087bdf10c840aef086420577ec121003be6090801deb04840aef182421f77ea1210fbbc509087bdf884843def0424203ffecb9901eff65cc80fff32e6403bf9973203ffacb99002fd65cc80ffe32e6407bf1973203ffec99901eff64cc80fff3266402bf9933203f7cc99900abe64cc80ffeb26643bbf5933203f7ac999002bd64cc80ffe3266407bf193321dffea9990effe54cc877feaa6643bff1533203ffea79901ffe53cc80ffea9e6407ff14f3203ffe879901ffe43cc80ffea1e6407ff10f321e7fea599003fe52cc801fea96643cff14b321dffe85990effe42cc801df216643bff50b321dff885990efbc42cc80fffb0e6407ff9873200dfcc39901ffd61cc8017eb0e6407ff1873200df8c3990f3ff51cc875ff28e643aff147321dffe83990efbf41cc875ff20e643bff507321d7f8839901ffe31cc80ffe18e643aff887321d7f8439901fff60cc80fff3066404bf9833203ffac199002fd60cc80ffe306643cffd43321e7f8a1990efff40cc877ff206643bff503321dff881990ebff10cc875fe086640affd9632005fecb190e7fe658c8077f32c6400ff59632005facb1902bfc658c8077e32c640affd92321a5fec9190d3fe648c8057f3246434ff592321a5fac91902bfc648c8057e3246434ffd52321a7fca9190d3fd548c869fe2a46436bf58e321cffea71901ffe538c801fea9c6407ff14e321a7fe871901ffe438c869fea1c6407ff10e3203dfcc5190e7ff528c815ff2946400ff54a32057f8a5190d3ff428c815ff214640aef90a321a7fa851902bfc428c815de2146407ffcca32007be651901fef328c815ffb0c6438ff9863200dfcc319003fd618c8017eb0c640aff1863200df8c3190e7ff518c871ff28c6438ff146321a7fe83190d3bf418c871ff20c6434ff506321c7f883190e3fe318c80ffe18c6438ff88632057f8431902bff608c801ff3046404bf98232007fac119002fd608c815fe3046439ffd42321cff8a1190d3ff408c869ff2046434ff502321a7f881190e3ff108c871fe0846400ffd9532005feca990037f654c8013fb2a6437ff9953201dfcca99003fd654c8017eb2a6437ff1953201df8ca990037c654c8073e32a6436ffd91321b5fec899003bf644c8015fb226436ff99132015fcc8990dbfd644c86d7eb226436ff19132015f8c8990dbbc644c8055e3226436ffd51321b7fca8990dbfd544c86dfe2a26437ffd4d3203ffca699003fd534c80ffe29a6436ffd0d3203ffc86990dbfd434c80ffe21a6437ffd4932007fca499003fd524c86ffe2926436ffd09321b7fc8499003be424c86dfea126436ff109321b778849901fff324c80ff79926400ff8c932007bc6499003ff614c8017fb0a6435ff9853200dfcc2
  | 9 => 0xc89ff212a644ff50953227f884a9913bc4254c01ffb0aa600bfd855321ffcc2a9806fe6154c01feb0aa643ff1855300df8c2a980fff5154c07ff28aa643df9455301ff8a2a980f7c5154c89ffa0aa644efd055321ffc82a9913fd4154c87fe20aa643ff8c55303ff862a990ffe2154c87fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153025f8c0a980fff5054c07bfa82a603ff14153227fe80a9913fe4054c89fea02a644ff1015321ffe20a990ffc1054c077eb2ca40affd9252215fec92910bfe64948057f324a442ff59252215fac92902bfc64948057e324a403ffd525201ffca92900ffd5494807fe2a4a40affd8e52007fcc72901efe6394801feb1ca400bf58e52057f8c72900fff5394807ff29ca400df94e5201ffaa72900ffc5394807be29ca442ffd0e52217fc872910bfd4394885fe21ca403bf98a5201ffea52900f7f5294807f7a94a40aff14a5201fd8a52910bff4294815ff214a442ff50a52057f8852902bbc4294815ffb0ca441ff9865200dfcc329003fd61948017eb0ca40aff1865200df8c32900fff5194807ff28ca441df9465201ff8a32900f7c5194885ffa0ca442efd065220ffc832910bfd4194883fe20ca441ff8c65220ff86329107fe2194815fe10ca40affd8252007fcc129012fe6094801feb04a400bf58252057f8c12900fff5094807bfa84a403ff14252217fe812910bfe4094885fea04a442ff1025220ffe2129107fc10948077fb2aa440ffd9152205fec8a9003bf64548015fb22a440ff99152015fcc8a9103fd64548817eb22a440ff19152015f8c8a9103bc64548055e322a403ffd515201efea8a900ffe5454807feaa2a440df5515201ff8a8a9003ff63548017fb1aa400ff98d52007fac6a9003fc635480f7e31aa403ffd4d5201efea6a900ffe5354807fea9aa400df54d5201ff8a6a9103ff4354881ff21aa440ff50d52207f886a900eff6254807ffa92a403fbd495201ffca4a90037e5254807fe292a403df1495201fd8a4a9103ff4254881ff212a440ff50952207f884a9103bc4254801ffb0aa400bfd85521fffcc2a9006fe6154801feb0aa43fff1855200df8c2a900fff5154807bfa8aa403ff9455201ff8a2a9103ff4154881dfa0aa43fff90552207fa82a90fffc415487fff18aa43fff0c5521fffc42a90fffc2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a404bf1815201ffea0a900ffc5054807be282a440ffd0152207fc80a9103fd4054881fe202a43fffc41521fff820a902bbf659087ddf32c8400ef5964205778cb2102bbf6390801df31c8400ef58e4205778c7210fbbf5390801df29c8400ef54e421f778a72102bbe62908055f3148402eb98a421f77ea52102bbe5290801dea94840aef14a420577ec3210f7be6190801deb0c8400a
  | 10 => 0x300000300500400c00200300000300400e00300d00200100100300c00200000000400000100100000400000800200300100000100700200100200100000200200300000000200000000000000000c00100e00000000200200200100300100000000b00100000100100000200100100000f00200000000500000300000000000000400500100100000a00000000300001200200400100600400000500100000400000000100100000000100100200900000400000f00000e00000b00000000000100000800000000701a00100300000200100c00000000000101600200100000100000100000000300b00700300100000200c00000901100200100900000000200000300300300700100600100200000000500000000300100000000000000000000100400000100000500200000200600100900200000000300500100600100800300100b00700000000000000000500100000000000500100000100100700600200300600300500000000300100300000200100000000100100000700000100200200300200000100000100300000d00000000000100000100000100100300202d00300000600000801500800300600300000200000100101100000000300600c00000000200300300400200800300700200400000200000000200000500100000000000100000000100200700000d00101000000a00100000000300000500700201dfacb2981fff6494c0f7fb24a607ff99253015fcc92981ffd6494c8d7eb24a607ff1925303df8c92980fff5494c07bfaa4a603ff9525301ffaa92991b7d5494c07fe2a4a607bf98e5303ffea72981f7f5394c07efa9ca603d7d4e5303ff8a72981fdc5394c0fffa1ca607ff90e5303ffa872981ffc4394c0fffb14a607ff98a53005fcc52981ffd6294c017eb14a607ff18a5301ffea52980ffc5294c07be294a646ffd0a53237fc852991bfd4294c8dfe214a646ef10a5303ffec32981ffe6194c037f30ca607ff58653005fac32981ffc6194c037e30ca603ffd465301efea32980ffe5194c07fe28ca646ffd06532377e8329917fe4194c8dfea0ca645ff1065303ffc632981ffc3194c8bff10ca645ff0865303ffec12981ffe6094c097f304a607ff58253005fac12981ffc6094c07ffa84a603ff1425301ef8a12991bff4094c8dff204a646ff50253237f88129917ff1094c8bfe084a607bfd9553227fec8a9912ff6454c89ff322a602bf99153227fac8a9912fd6454c89fe322a602bf1915301ffea8a980ffe5454c07feaa2a603ff1515301dfec6a980fff5354c07efa9aa607ff94d5303efca6a981ffc5354c0fbe29aa603f714d53227fe86a981ffe4354c89fea1aa607ff10d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a9802fc6254c07ffa92a603dfd495301ff8a4a9913ff4254
  | 11 => 0x38188a8000124000000000000000000004724ec0000c191f671b34d0454f9e6b0227213cb966a135f93bc8f80001db00002de0003f314bc0000003a3122400000000008dc42c0001e7a3cc0005df1678f7c00044d1110c1c8a600000013dc0000000000000e460000000000c587de3a29f2c6b43be00005c40980000981520f520c8000000000000000000000000000000000000000000000017c0001f400000002c700005740d00004811e9c85406430f00650b602231b0000ec83721a000000004c80002130f0a00009d8b44ed2000000000000067f25c80005a005b1ae00009f200003c000000059f00010f07607ec39380582d200000019b048e000000044c0001c300000007a210400000000002b901598186b60000000000d100001f900000ec00043000000001820000db8c76000000080c0ea6cd1e39f6472a14d22100000005ee15b999000000009511007e23280001bfc7ec0001d90d902d615c457010c0000422c5800014800040e22cc0006080001904f3a00700000000000400300400000700200900000000000100000700100100000000700000900800100000100300200400200000200200000000100600000000000000e00100c00000400000700000600000000300700e00000100000000000000100200800100000100100300300c00100100300500000300200100200a00100100000000000000000100100100000000000000100200000100000200d00100000f00100000200000300100d00900000000300400800100100200000000000000200000200200200300e00101100200100a00400100000100000200000201a00800000c00000100000000100000100d00000200000400300400000300200000500000100400700100000100000000000100000500200500500700100100000400000001100900000d00700000900000400100000900000900000500100300800100100100200800600000000300000000100200200100000200000000100200200000000900000100000000300300000500000000100100000200100100b00300400600000900300000400500800000a00600300000000100600d00000000100400100000100100400000000000300300000a00000800400400100000000500000200100000200100000400100000100600000100900600000700100100100000100000800100100800100000000000400100000000000000000000000100000200000200000000100100600600f00000000200900100000100300200500100000800000000100100500300800200100400400000000000100200000000000100300900000000000000100500100000500300100100100000000200700000100b0020000000000020090000000010010020070000040020010010000010000000000000010040
  | 12 => 0x4543fd94ac94e000292800000000028b00000006c900000010ca1f63ce000000025004e80000000000001c3c0002fc2cc000000077024f9a140f843607600000006cf2c7800000020218c000018c3b90000c3c000000000027000000000000000004222bb88c08be00015e800018a0001c0007048a00047700005525d33ae8c5816e66600000000000002d180900000000000000fc82561f70000aec7530000aec00088f1f38acc0000003a200000ae4f631c80003aa6f9124885120e000213962800000000000000000003f4800000008000020a80e023200023bcc087ee013905c00046f4101754d680000f3030c0000000001f540005ce1fc00008ac000280218c0000003d713a0cae2830000000000000118800088a000000000072e50244e1a2c000000000000047c00000021d01f400000019d000000001d0000000000000000000000031883940001bc00000011860000001fcce4c3fe0ff000014e000000007480634f24117e0000000024991c00000018d942865c000000000000000031900480006ba2b00bd032e3653be800109c6133fb800000072f2660c2c00000000009fce0a47b00000000000000000000a708c502a0a8cff80000000000a1200028703fc00000008b904c62861b0001f444980002548d7881a27e000000082c53643c00001886f10dc178c00000014821482bc0001c304d4f1803105b00000000001540fe41dc00000000006605850a380009dc0001f4a120c8676330f9c3036e7342c887149642ed142a1244f218914e1f8ca5c8ba000000000000000007504b232306a87e81c86c7000161ce7000046015f8c2044338513d40a205e21883dc1840001da00000003ff0b6800000089000000840000000001bec3a27e70d905f447400043d1a491f8000431000000056b3e8000000000000012d88f00fd0001c548c40001e90000dd44f8125800000041f15200003c290a0000000ba06fd42f800000000000002985d210126a1c500006633c384a07786ca47f00006e2000000208c0008d7392800000001e40300000000000000000f8c00043e00000002e80649470e240002ec0000000000000239000000000008805ec75e129000107c00000000004cc79f3870c2800063f2b392cc0e26b2132814064a60537a9654b260000378000e507f9000000000013300010f43e00001e30000c4c3023bf06045c6000036000000000007c07c43405660001ec000000000003a500600000000000001c02e51c18ade1ee3db1af0fc213a222128080c41c2c21210be4268208146113c05a1b00288dee74a1bf94e500021c40100002348e0330000000064a0de800000049a2e6145c9e67202f215f0ac21db43600010de59c14ea264ab81a10001bd84b421b000237c99467709b94dc000000000005c6d00000000000
  | 13 => 0x1410000e2800026726980000000000000b0000000000000000000002a200008d60000c31ea00001ce007967461000003000004466c62d3239400000000000000006d5000000000068725284c828c38f12f23e488e3451ea80006a42872ea11048f40003d300007d485c18f80008761dd26f000000067900000001627d81f814ecd405122d48d101368c712a18dc6920003e40000c742cd3201ffce8031d00012484b642c00497d402000037c206059c45b00021c0354000004000000000000019bc00000000000005602c329497580003f30690e6c2a4000000000000000016400000000000001fc503c63c2309734d1228a0000000000000480000023a90f3460bfca980000001d847341511cf8558a0c0000000000fb618c0f180000000000000cd122600035c02e400040f00000000000000001bd000000019480010fc00103f8000000000000194c9d60002d01ee400014a1f59a380000cc1baa1c4da041d00006780000000001bcc0000002879d5c6725792e488007ba62e4650000cc4000165800000000004280000003ba0a000000005ad10718a80003940001290e643892d200005360000000000b906a900000000004ab0000000000000000000000000027f000000000006c9f300000002c003a8000000224144c9ae5aa3588d7471c23400203c080a2a70b2074028a67d0001b511e40003de0c44658000000192400000000014a80004ae091000000008f0001ad40006be00000000000002a280000008083b680003a60001a816a0b5e0000f5800000088e00003cce2c00000022440007f81320238126000000000112c16c00000004c400036c8d9876600000013040000002c70a546b21e90000000d3e000000218517c5101fe80000008f6000000033e000000000094c00000000002183322648000000000000000000000005c0d6112634d0000a2400018724a87284ee0eb1588660000000000000000000000000006fa1144698000d2e0001808fb00000c714b8000d860e000000000fc18512400010b09051d780002d000000000010e48153f406c070e1e400018e00000000001ef505238314b14852183090001ce427c3e11ea0730000336473a21475c4b80b38ab4a4e57b112880410677c45b1dfc0006cc455800009a0000000000cd00001460000cd600044095fc39600042c80000001030000000d1471d2a9825c00000023f1e880000000ce80000001d901f0000b860001770000000002000160c33618a0001e040002fb1508d9c0000004691f380000a10000000000351000000000038b2250508ec46c030c1b580003a938e08d8d360004348ef40000000001d54f4800000000000000000bf22b03160003ca80000000001890b800000002fd80009188120000f9101400000000007a6000000000000000011c0bf51f4575
  | 14 => 0xa474073495e0002ab9f74c6a03637315a03ee5630299380ebe33722a8f1496e17800000000000001fb812c98c00c3cd13982f400007a00006942df16a0f303e66ac0888000e7a37b33b000020485a44a8658b7e39610c9f5d1ba14e3d18e9c9862942550000f8800038c80000000002a10000000000390a1d4000000000000021c2693768000b328e110e8b6443066a07797d8c3a0000a18a4c7188940000d50cb800000013903920002a79fc8e048274299fbc17828e1d01b082ae05d34b1e184225960d11eccc168b1000000000037730b93890ae0820000720000000281a0880006720000ff00007660000944a10000412800000000045480005fc0002a917780000000000000e865340000001068000000000049c26d0b0a158fe83aa312800119a2070000000000000000000000000000000000005e700000000000001a58000f0650b0000cf00005e23211de40006823dd82d400000008f8698af000018e0c8431e8d1212095c9a46c511592781565ae1061cc054a000000000000004706e849c5f40003999e08cce000000188400000028f022d03204f41c0000000000380016000018d4099bc8eb678b16900000000003f10000f322f90000000742158035a26c3c40001eb14980000001c800002900810001cd4bb641e11980012125d221a23c10bc36d2e393d0f2e00000002500005740000358a7a73f00001641bc0000001b21184000000000048400006a00b400000023995cc99c0002a680000000000000dd80000000000c900008e3000206c2326953a600000000000000b580000000fd939c0000000000000fa409821b80000006d3462000000000028a8c6400060a0001d5045e5431e180002ec43841fa3b40000000f9117800000000000000d4724000000000053a0000000000000126a0a040a8cb15322e4b4e6dc000000000022e00023b00000290000000aa2435000000000076000000000000000df0000ffc0002a5800104c7da00000011760001b580000005b007f0d5c0501dc000000000049d000000121a0aa0001cf800071e00005e400078d0180254c1a898000019d1427ba043065408c000031988103a58d000000000000000000000007b50000824dc27f000000011a032600004b4000000000000000000000001c807802300021b40000000001b5c92248b28213b47827e50ba0000c1e3ad37285980003da000000088c00040d16e50a034e0000984000000000000000000000000008a444c00019cc000335000000000062700018c0c6600000000000005b830a97a40004872de800c6fc0b307e000000000000000000000000cd000000000040600010aa2e202080000000003880000f7e3840001d3c67606222780000ca000066862000000014c80004a673130c95b800067a0001b480008330000000000911000000
  | 15 => 0x40ea2000000000068c000000000000064e0001314ddc1490560828a7e420000000072256d0ec1adc00074e10f00000001501cc84b00005c52509a50000665000000005c0000880000d4c3c80000c809f843300000005d80000c180000dc0001af9d9cca40d14339ddc0da2db0000ae08ee00631180000000000001e800006a500000148ba15318f0e7067c22700012f06d800006e00000008b024419851102283009e28d662b619980000b80002da0000000000000000000091200020bc00000008380000006de15515a8fb80000000a48bf80cf0001cb09504d61621cec76a72e0b700000720000a5800000082d47896ac86000030012f88e84571121ca44be49c4730c38f920ed1c904846f81d627d8f08bd01c70ba80000000003e28ad065435645216cd18c0440000424bd638809f92f40001ec0000000000000000087c00061200021911c40000000000000000107800099679612a80000000000e0821cb34108000201c000000046807c8361ea45e80000005890000f344d835323900000000da08b197c000000000000091c0000b2a2941803ac228800085c0001bc1e60b420001d4000000017f00002ec0004dd3380000fa80000000000000000000069412000000010984e445000000f4000000000000000091002a821000000000000000000d0357a2e000046011e80006184712f78be000047641e00007f628d000000106e000000000000033f0d5a230c8a00008e1e40000000000028c0006b9006a05000000000011b83be000000112c000000000090000082b000000000000026e000011000000000004f80b23b283390820002c322d49fa0000000000f4200000015c882a00b00001f4606704000000000000a0000a009b486b349800000000013d8000f2400000000000001b500000007263f50a620c03222d50000000a024c7000098cdbe03b00000000005e1000000000000031f1e442f619030d000000082e00006e40001b44341360be63f40002118476112178a3f498822d04d1e780000003b4000080816232c98f4b6c04516d06380008e900010680000002a8048cbfe0000001850c900004258f8c7ae1e7000000000065e135800067069000000000000000000fbc00000005d104800000014f000096849005e800000000000022c8000000000195801c00000016f800012f3478000d3a0f9177a35434855945f8000f5a000000000000027001a8000e5a00017300000000002f51ab800073c46700000008b4000082000000000000008420000000000f5687d1c6851106c8d41b78b943527df0001a645d40202e11550d560560001f000000000001b6800000004492d4000000000236096040248208351342be14c000006e3412b213c51540000000000080000000000120c00029e20e800022600000011e845a22ca0b01ea4e
  | 16 => 0xca13b0580a0a6eb10d21511bc8a83c78000a6600000000001180130528000b100002be80000008d600000000000000001dbca363d81d295380007cd0000bdc7040000000000f1c00009e99680001af00000000000003a3800000012e2968f6c00000011a9560c8c81600c14680000003e99ec80001fd000000000000031400000003a300000004240000000000000843294000000023c00000000008ff000000000000000000000008cc2b81d6840c000395000000000024d8000000877242800000011b444864d0a27732ff1d240005ac000103807000000000000000000000000cf600000001a40000000001de8000778328800000059224680000000000000000e905562ca17b000007a278000000026f000165c0001250000a8913e000000000000022c42e9d585bc0002748000000000000000000060c30100000000000000000000788367137c0003223ac07f000000000006a0d5089d27280008e087900000d00001f90000000000000000000000000023f80005e00000000000000000000000101c07b00885680e82842ae95b055c13138b924c06646c0398000d30000000000000000000000004420002d100010220000000000000547000000000042900017c00000d300000004f00000ed0000aaa00027194900004752a0093d04800033680010f67b1000000000000000000000007c200000000000000001edc000000000000000000026014d44dc00000006c44264e129f236802a86a000000000000000001480000000000000502000030a1fc00000016c1004216000000091800031a3ba9fe919e6b62e30000db07eb00004d834e8442328000000000095847800000000018d04526e00f78000a221ba36e800000075200000000005fd00000000000001388de424c000000017c00048f0f68a3c37e41145382b465a6752431d7089259e38397d09a25b10001fa80000000000000ca80000000c402be00000016dc00000023380000007b40000b050dc8af0e21b884b824320c97e4dd07f600023dc000000000196c0005e50c000008cc2e10000000d084d54569ce8cba000000143455e6220e900000007f50000e140007fd2dd00000006aa10593e85040003b711f426858c0001be8240118000000000000016b8000000000395943102000000019c44e60000000bac000000000000000046a36d8000a284093621334abe7013568e04a4600000000000000002e791601b680d32687787701bb36880000007d600000008f223f19386b0f2852000022f0e6e840283a0ec9023ed19e8b24b028a0215a40c0005dd00000000000000000a2c00034342683605ea7c32b4a438cdc5a5000102c00000006b80009846a440b800032421539b0dcc558000322236c84664f2a08000000000000000000000037805f058c000000043481400038d13
  | 17 => 0xb9c00090125180007bc00000000000000000001dd800000024198ac000000074000000000003c8b08000000000000000032b0000000058000000220c00001b23200000000002e0000013c0000001bbd21678900007080000001f3000000000000000000003cb1f29f1c00000034310a095a000317801c87479b19d0000000000000000000088a446918ccfc00000000004c008a05f9060c126e42a483c81520002560da80004b13f01c2c00000000000000000a0000000000000020610b400000007380009e400034f19400006e31ba0b2800000007899601ec19934096f0e126830251fb400000004f800000000000000000000000001bf8000000000000000000044920c40ee00000010fc00080905a0000b768b700020c887c3ce00000002e63c01fd00000007720001c60df81e02e200006984cf30e000107a88724b176512e51d0001a9c0003c9000000030840800011b4e26000000000000000000000000000000000000e440e12e8800000064c0000000ef63dc2d910500003d91d31da800000020380000004990001c4400000000018a40002743e514c4000370000000000000032589e800059b00000002b270d1d10d200006bb00000000002cc073000000000002409107480004410ac80000320ce1a8c0000001e81d2c35a0000000000000000000000000029f0d997c497e0000000000f0067c00009f400028840f8d1cb820000000f888646a20f287a07c0000000000000035531686510840002001844ed80a844304286d254a4252114a647843a080fc000000000000000071f00006d800039e3d283ec6081550000000a5829a00021cc0000b00000d086c2000000000000000000000000007b832a85500006e9000000000031713a805073a5d725d832d08e2ab087830519068015f80011928a61d580000001cf182858c3fe49400009a80000001df80011161720000d8cbf40000830c540002dc25d06b80002f22b8800000001a3b88000eb21d71720000000000000037c7302a01dba02c2b61700a78000346000000041412c48a000000000031321281380008661208a44000000000147cc2c0000fc1d080006cb2f01eb10724803ba228c0006030000f280002e74078d8906a1f5000156800000000000000000000000000ac400000012603e80004400098f545b5000148800037a00000000000004510000ab61c621790e4b20000000000000000001280009fe0e33d7800000000026d800060000000000a8f827930000248aca5ed0000000f7c00000000011b20004021d344b000010b8b74420669000000000000026c8c3400000043b0000cf054646e00005a60910001af45e600028c8cc4d382bc09e0cbd1828ea00011a413290812522100000004109d40c0e00005795e82520000001170200000000000000000000020145740
  | 18 => 0xed602f03314c11f00003841bb04ba4970002004c483b147597dc0005da0b500000000000000a18776000346800058a55e00011a00000000bb82b84080e209c8f100008f515a800000000000004e00005e62c11b0400000000000009440003071a4400000000000000000002ee1
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe74cc910005bd74cc910006ef62cc910006ec62cc91000df671cc910005f571cc910054ff768c910004fe768c910004fd768c910054fc768c9100067f658c9101ce7c658c910006df638c91003edc638c910025fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100357c754c9100067f654c9101be7c654c910005bf744c91002dbc744c910054ff760c910004fe760c910004fd760c910054fc760c9100357e750c9100057d750c9100067f650c91019e7c650c910006df630c91003edc630c910006ef620c910056ec620c91000df6710c910005f5710c910025fa700c910005f9700c910025f4764c51003ef4764c510024f4764c51000777654c51000774654c51000df7734c51000fd7734c510007d7634c51003ef6634c51003ef4634c510007d4634c510257d7534c510257d4534c510007b6424c51024fb4424c510007d7324c510007d5324c510007f3704c510025f6704c510025f4704c510007f0704c51000ef7604c51000ff3604c51001cff765411000cfe765411011cfd765411000cfc76541100067f655411001e7c6554110005f7715411000df47154110027f0105411000cfe76cc11000cfc76cc1100067f65cc1101167c65cc110006df63cc11003edc63cc11000df671cc110005f571cc110007d531cc11003cff764c11000cfe764c1100d4fd764c11000cfc764c1100057f754c1100357c754c1100067f654c1100e67c654c110005bf744c11002dbc744c110006df634c11003edc634c110005f7714c11000df4714c110007d5314c11000cfe76c811000cfc76c81100357e75c81100057d75c81100067f65c81100b67c65c8110006ef62c8110056ec62c811000df671c8110005f571c811005dfa7688110026fa76881100277a75881100277975881100077b6588110007786588110027ba7488110027b9748811007df97288110056fa6288110056f86288110007ba4288110247b8428811000dfa7188110025f87188110026fb6188110027f36188110097bb4188110097b94188110097f23188110007f13188110054ff764811000cfe764811007cfd764811000cfc76481100067f654811008e7c6548110005bf744811002dbc7448110006ef6248110006ec6248110005f7714811000df47148110027e8204811000df8764811007ef8764811000cf876481100077b6548110007786548110007bb744811023fb87448110025fb7248110027eb7248110007eb6248110056fa6248110056f86248110007e86248110007ba424811023fb84248110007ea3248110007e93248110007f3714811000dfa714811000df8714811007ff07148110026fb6148110027f3614811007fbb414811007fb9414811007ff23148110007f1314811007feb214811007fe92148110
  | 1 => 0x8910004ff74d8910014fe74d8910006be74d8910014be74d8910004fd74d8910006bd74d8910004bd74d8910014fc74d891003cfe73d8910004fd73d8910006ef42d8910006bc42d8910006ec42d8910006ac42d8910024ff71d8910024fd71d8910096bf41d8910096bd41d8910096ef21d8910096ed21d89100357e75989100057d75989100067f65989100067c6598910006ef629891007df9709891001cfe75989100567e759891001c7e7598910004fd75989100567d75989100047d7598910054fc7598910054ff7498910014fe7498910004fd7498910054fc749891003cfe7398910004fd7398910054fe7298910056bc42989100acfd7198910056f571989100aebf41989100aebd419891007cfd7098910056f970989100057f75589100357c75589100067f65589100067c6558910005bf745891002dbc7458910005df7358910005dc73589100adfb7058910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891003cfc7358910006dc735891003cdc7358910006ef7258910006bc425891007cff7158910006f7715891007ebf415891007ebd41589100acff7058910006fb7058910094fe76189100067f65189100067c6518910006ed6218910007ac421891001cfe7518910004fd7518910054fc7518910054ff7418910014fe7418910004fd7418910054fc741891003cfe7318910004fd7318910056ee7218910006ef4218910056bc4218910056ec4218910056ac4218910024ff711891000cfe7118910024fd711891000cfc711891005ebf411891005ebd4118910056ef211891005eed2118910024fe7018910056f97018910024fc7018910054ff7694910004fe7694910004fd7694910054fc76949100067f659491001e7c6594910025fa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c6554910005bf745491002dbc7454910056bf7690910006be7690910006bd7690910056bc7690910006bf65909100073f65909100063f65909101f6be6590910006bd65909101f6bc65909100073c65909101f63c6590910006bf639091026ebe6390910006bd639091026ebc6390910265be729091002fae7290910006bf6290910056be6290910006bd6290910056bc62909101edbf71909101edbd719091025ebf61909101efb63190910007ba7090910007b970909101eebf60909101efbb109091025fb6109091025fb410909101efb8109091003cff76cc910004fe76cc910004fd76cc91003cfc76cc9100067f65cc9101e67c65cc91002db
  | 2 => 0x63c42d951028e7f71d951012e7e71d951012e7d71d951012e7c71d951012e7f41d951012e3f41d951012e7e41d951012e7d41d951012e3d41d951012e7c41d951012e7f31d951012e7e31d951012e7d31d951012e7c31d951012e7f21d951012e7e21d951012e7d21d951012e7c21d951012e7f70d951028e7e70d951012e7d70d951028e7c70d95100067f40d951028e7e40d95100067d40d951028e7c40d951028e7e30d951028e7c30d951028e7e20d951028e7c20d951012e7f10d951028e7e10d951028e7c10d95100367c6559510285fb705951012cff75595100067f7559510004ff7459510014fe7459510004fd7459510014fc7459510004ff735951003cfc7359510004ff7259510054fc7259510006bc425951011cff7159510006f7715951011ebf415951011ebd4159510284ff7059510006fb705951012d7e76195100367e761951012c7e76195100373e74195100373d74195100067f64195100067e64195100067d64195100067c64195100073c421951027e7f61195102773f41195102773d41195102777631195102767f60195102777b101951027f76101951027f74101951027778101951003cfe76d8d100067f65d8d100067c65d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10006dc43d8d10054fe72d8d10004fd72d8d10006bc42d8d10024ff71d8d1000cfe71d8d10024fd71d8d1000cfc71d8d100eebf41d8d100eebd41d8d100eedf31d8d100eedd31d8d10024fe70d8d10024fc70d8d100357e7598d100057d7598d100067f6598d100067c6598d10006df6398d100d5f97098d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d10105fb7058d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10054fc7258d10006ec7258d10004ec7258d10006bc4258d100d4ff7158d10006f77158d100d6bf4158d100d6bd4158d10104ff7058d10006fb7058d100ecfe7618d100067f6518d100067c6518d1002dbe7418d10005bd7418d1003ede6318d10006dd6318d1003cff7694d10004fe7694d10004fd7694d1003cfc7694d100067f6594d1001e7c6594d100375f5394d1000df67194d10005f57194d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d100067f65d89100067c65d891002dbe74d8910005bd74d8910007ac42d891001cfe75d8910004fd75d891001cfc75d
  | 3 => 0xd2158a10024ff7058a10024fe7058a10024fd7058a10024fc7058a10026ee2058a10026ec2058a10054ff7694a10024fe7694a10004fd7694a10024fc7694a1001e7e6594a100067d6594a10025fa7094a10005f97094a10004ff7654a10024fe7654a10004fd7654a10024fc7654a102a67f6554a1001e7c6554a10005bf7454a10045bc7454a10005f77154a1000df47154a10056bf7690a1025ebe7690a10006bd7690a10056bc7690a1025ebf6590a101f6be6590a10006bd6590a1025ebc6590a1025ebf6390a1026ebe6390a10006bd6390a1025ebc6390a1029dbe7290a10047ae7290a1025ebf6290a10056be6290a10006bd6290a10056bc6290a101edbf7190a101edbd7190a101eebd6190a1025fba7090a10007b97090a1025ebe6090a1025fba2090a1025fb71090a101efbb1090a1025fb81090a1003cff76cca10024fe76cca10004fd76cca10024fc76cca10045be74cca10005bd74cca10054ff768ca10024fe768ca10004fd768ca10024fc768ca10056ee628ca10006ed628ca10025fa708ca10005f9708ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca1004d7c754ca10005bf744ca10045bc744ca10006ee624ca10006ed624ca10005f7714ca1000df4714ca10054ff760ca10024fe760ca10004fd760ca10024fc760ca1004d7e750ca100057d750ca10025fa700ca10005f9700ca10025fb7648210006fb7648210007bb7448210297b87448210027eb7248210027eb6248210056fa6248210026f86248210027e86248210007ba4248210297b84248210007ea3248210007e9324821000dfa714821000df8714821007fbb414821007fb9414821007feb214821007fe9214821001cfe76d95100367e65d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100367f54d95100067e54d95100067d54d95100367c54d951003cfe73d9510004fd73d95100367f53d95100367c53d9510054fe72d9510004fd72d95100367f52d95100367c52d9510006bc42d9510024ff71d951000cfe71d9510024fd71d951000cfc71d951012e7f51d951012e7d51d951012ebf41d951012ebd41d9510024fe70d951000cfd70d9510024fc70d95100367f50d95102757e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c42d951012f3f41d951012f3d41d951012f7631d951012f7b10d951028f7610d951028f7410d951012f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d9510
  | 4 => 0x42000ebe61504202bfb6615042000eb6615042005ebd61504202bfb56150420006b5615042000ebc61504202bebe60504202bfaf20504202bfba20504202bfad205042003cff76cc420024fe76cc420004fd76cc42006d7e75cc4200057d75cc42003ede63cc420006dd63cc420004ff764c420004fd764c420024fc764c42003ede634c420006dd634c420005ef724c420055ec724c42000ef6614c420006f5614c420005fb704c420025f8704c4200acff76484200057f754842006d7c7548420005bf7448420065bc74484200aeee6248420025fb7648020006fb7648020004fb7648020007bb74480202b7b87448020025fb7248020027eb7248020056fa6248020027ea6248020057ea5248020007e95248020057ba4248020057ea4248020057aa42480202b7e94248020057b84248020007eb3248020057e83248020006f961480202b7bb4148020007b94148020057eb2148020007e921480200267f7559610004ff7459610014fe7459610004fd7459610014fc745961004e7f54596100067d5459610004ff735961003cfc735961004e7f5359610004ff7259610054fc725961004e7c5259610006bc425961011e7f515961011e7d515961011ebf415961011ebd4159610024ff7059610024fe7059610024fd7059610024fc70596100267e50596100267c5059610004ff7558e100067f7558e100047f7558e1001cfe7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10004fd7458e10014fc7458e10006bc7458e10014bc7458e10026df7358e10004ff7258e10054fc7258e10006bc4258e100d6bf4158e100d6bd4158e100d6df3158e100d6dd3158e10024ff7058e10024fe7058e10024fd7058e10024fc7058e10026de3058e10026dc3058e10026f71058e10026f51058e1003cff7694e10024fe7694e10004fd7694e10024fc7694e102ae7f6594e1001e7c6594e1004f5f5394e10004ff7654e10024fe7654e10004fd7654e10024fc7654e1001e7e6554e100067d6554e1001cfe7598a100567e7598a1001c7e7598a10004fd7598a100567d7598a100047d7598a10054fc7598a10054ff7498a10014fe7498a10004fd7498a10054fc7498a1003cfe7398a10004fd7398a10026ee7298a10056bc4298a100aebf4198a100aebd4198a10056ef2198a100aeed2198a10024fe7098a10026fa7098a10024fa7098a10024fc7098a10026ee2098a10026fa2098a10026ec2098a10004ff7558a1001cfe7558a1001cfc7558a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10004fd7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a1003cfc7358a10026ef7258a10006bc4258a1007ebf4158a1007ebd4158a1007eef2158a1007ee
  | 5 => 0x577975c8120007bb64c81202dfb864c8120025fa72c8120026fb62c8120027eb62c8120057ba42c8120057b842c8120057ea32c8120007e932c8120005f971c81202dfbb41c8120007b941c8120057eb21c8120007e921c8120024ff75594200267f7559420004ff7459420014fe7459420004fd7459420014fc745942006e7f54594200067d5459420004ff735942003cfc735942006e7f535942001cff7259420054fe725942001cfd7259420054fc72594200567e52594200567c5259420056be4259420056bc4259420004ff715942000cfe715942000cfc715942006e7f5159420006bf4159420024fe7059420024fc70594200267e50594200267c5059420004ff7558c200067f7558c200047f7558c2001cfe7558c2001cfc7558c200067c7558c2001c7c7558c20004ff7458c20006bf7458c20004bf7458c20014fe7458c20004fd7458c20014fc7458c20006bc7458c20014bc7458c20024ff7358c20026df7358c20006de4358c20006dd4358c2003cff7258c20054fe7258c2003cfd7258c20054fc7258c20056be4258c20056bc4258c20056de3258c20056dc3258c20004ff7158c2000cfe7158c2000cfc7158c20006bf4158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20026ef2058c20026ed2058c2003cff7694c20024fe7694c20004fd7694c20024fc7694c202ae7f6594c2001e7c6594c2003ede6394c20006dd6394c2006f5f5394c20004ff7654c20024fe7654c20004fd7654c20024fc7654c2001e7e6554c200067d6554c2003ede6354c20006dd6354c200b4ff76548200567f65548200567c6554820005bf7454820065bc7454820004fd76cc820065be74cc820005bd74cc820004ff764c8200057f754c82006d7c754c820005bf744c820065bc744c8202d6ee624c820004ff75584200067f75584200047f755842001cfe755842001cfc75584200067c755842001c7c7558420004ff7458420014fe7458420004fd7458420014fc7458420004ff735842003cfc735842000cfd7258420056be4258420056bc4258420026f7715842005ef6515842005ebf415842005ef64158420006f5415842005ef63158420056f72158420056f42158420024ff7058420024fd7058420024fc7058420026ef2058420026fa2058420026ed2058420026f61058420026f41058420004ff7654420004fd7654420024fc765442001e7e65544200067d655442000ef66154420006f56154420006bf76504202bebe7650420006bd76504202bebc76504202bebf655042017ebe6550420006bd65504202bebc65504202bebf63504202cebe6350420006bd63504202bebc6350420007af7250420055be7250420055bc7250420007ac7250420055ac72504200aebe62504202c5bf7150420067b771504202bebf615
  | 6 => 0xf41d852007ef431d852007ef621d8520024fe70d8520024fc70d852007ef710d85200057f755852008d7c7558520005bf7458520085bc7458520006bf6458520006bc6458520005df7358520005dc735852007ef46158520004ff7654520004fe7654520004fc765452001e7e65545200067d6554520006bf6454520186bc6454520006bf7650520005be7650520006be7650520004be7650520006bd7650520005bc7650520006bc7650520004bc7650520006bf655052017ebe6550520006bd655052017ebc6550520006bf63505202cebe6350520006bd63505202cebc6350520055bc7250520007ae3250520007ad325052007dbf7150520087b7715052007ebf615052000ebe615052000ebc61505202bfae2050520004fe76cc520004fd76cc52003cfc76cc52008d7e75cc5200057d75cc520006bf64cc52016ebc64cc52003ede63cc520006dd63cc520005ee72cc520005ed72cc520007cd32cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c520006bf644c52015ebc644c52003ede634c520006dd634c520007cd324c520094fe76c8520055bf74c8520055bc74c8520006bf64c852014ebc64c8520057ae42c8520057ac42c8520005ee76c8520096ee76c8520057af74c8520057ac74c8520007af64c85202efac64c8520005ef73c8520005ed73c852007ded71c852000eee61c852000eec61c852007faf41c852007fad41c8520057eb70c8520025ee70c8520025ec70c8520057e870c8520056ef60c8520024fc76485200057f754852008d7c7548520005bf7448520085bc7448520006bf644852013ebc6448520007ae42485202e7ac4248520006f7614852000ef46148520005fb7048520025f87048520025ec764852000eec7648520024ec76485200076f75485200076c7548520007af74485202e7ac7448520007af64485202e7ac6448520005ef7348520005ed734852007def7148520007e77148520007e7614852000eee614852000eec614852007fe4614852007faf414852007fad4148520007eb7048520025ee7048520025ec7048520007e8704852001cff765412008cfd765412001cfc76541200067f655412001e7c6554120006bf6454120126bc6454120005ef7254120005ec7254120027e82054120004fe76cc120054fc76cc120006bf64cc12010ebc64cc120006df63cc12003edc63cc120005ee72cc120005ed72cc120027e820cc12003cff764c120004fd764c12003cfc764c1200057f754c12008d7c754c120005bf744c120085bc744c120006bf644c1200debc644c120006df634c12003edc634c120005ef724c120005ec724c120027d8304c12008d7e75c81200057d75c8120006bf64c8120076bc64c8120025ee72c8120026ef62c8120024fa76c81200577a75c8120
  | 7 => 0x8d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d20004ff7258d20006ef7258d20006bc4258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20006bf4158d20004ff7058d20006fb7058d20004fe7618d2008d7e7518d200057d7518d20006bf6418d20006bc6418d2003ede6318d20006dd6318d2003cff7694d20004fe7694d20004fd7694d2003cfc7694d200067f6594d2001e7c6594d20006bf6494d20236bc6494d2008f5f5394d20005ee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2001e7e6554d200067d6554d20006bf6454d20226bc6454d200a4fe769492001e7e65949200067d6594920006bf6494920216bc6494920024fc76549200067f655492001e7c6554920005bf7454920085bc7454920006bf6454920206bc6454920005fb7054920025f87054920005be7690920056be769092009cbe7690920006bf65909201f6be6590920006bd65909201f6bc6590920006bf639092026ebe6390920006bd639092026ebc6390920055be7290920057ae7290920056bf6290920005bd71909201eebe61909201eebc6190920056bf609092025fae2090920057ac2090920024fe76cc920024fc76cc920085be74cc920005bd74cc920006bf64cc9201debc64cc920006df63cc92003edc63cc920025fa70cc920005f970cc920004fe768c920006bf648c9201a6bc648c920057ae428c920057ac428c920005ee768c920006ee768c920007af648c920307ac648c92030ded738c92003eee638c92003eec638c920005ed718c920307af418c920025ee708c920025ec708c920056ef608c920024fc764c9200057f754c92008d7c754c920005bf744c920085bc744c920006bf644c9201b6bc644c920006df634c92003edc634c920007ae424c9202ffac424c920005fb704c920025f8704c920025ec764c92003eec764c920024ec764c9200076f754c9200076c754c920007af744c9202ffac744c920007af644c9202ffac644c920007cf734c920007cf634c92003eee634c92003eec634c920007cc634c920005ef714c9202ffaf414c920007eb704c920025ee704c920025ec704c920007e8704c920025e8704c920004fe760c92008d7e750c9200057d750c920006bf640c920196bc640c9202f5ee720c92000cfe76d8520085bc74d8520006bf64d8520006bc64d852007ef661d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520006bf74d8520014fe74d8520004fd74d8520014fc74d8520006bc74d8520014bc74d852003cfe73d8520004fd73d8520024fd72d852000cfc72d8520006be42d8520006bc42d8520006f751d852007ef451d852007eb
  | 8 => 0x5f971c8220317bb41c8220007b941c822001cfe76d952008e7e65d9520006bc64d9520004ff74d9520014fe74d9520004fd74d9520014fc74d952003cfe73d9520004fd73d952008e7c53d9520054fe72d9520024fd72d9520054fc72d952008e7f52d9520006bc42d952000cfe71d9520004fd71d952000cfc71d95200067e51d952008e7c51d9520006bf41d952008cfd70d952008e7f50d952008e7c6559520005bf7459520085bc7459520006bc6459520005df7359520005dc7359520005f7715952007df4715952008cff75595200067f7559520004ff7459520006bf7459520004bf7459520014fe7459520004fd7459520014fc7459520006bc7459520014bc745952008e7f54595200067d5459520004ff7359520006df7359520004df735952003cfc7359520006dc735952003cdc735952008e7f53595200a4ff7259520006ef725952008e7c5259520006bc4259520004ff7159520006f77159520004f7715952000cfe715952000cfc7159520006f4715952000cf4715952008e7f5159520006bf41595200b4ff7059520006fb70595202a67e50595202a67c5059520085be76d9120086be76d9120014be76d9120006bf65d9120006be65d9120006bd65d9120006bc65d9120055bc72d9120005bd71d9120006be61d9120006bc61d912025fae20d912025fac20d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006bc53d912025ebf72d9120086be72d9120054be72d9120086bd72d9120086bc72d9120054bc72d9120006bf52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120004bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d9120006bf70d912025ebe70d9120086bd70d912025ebc70d9120006bf50d912025ebe50d912025ebc50d912025ebe30d912025ebc30d912025ebe20d9120086bd20d912025ebc20d9120006bf10d912025ebe10d912025ebc10d912003cfe76d8d20006bf64d8d20006bc64d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df53d8d20006dc53d8d20054fe72d8d20054fc72d8d20006bc42d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006bf41d8d20006de31d8d20006dc31d8d20085be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200057f7558d2008d7c7558d20005bf7458d20085bc7458d20006bf6458d20006bc6458d20005f77158d2007df47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf745
  | 9 => 0xd6590a2025f3d6590a200063d6590a2025ebc6590a2025ebf6390a2026ebe6390a20006bd6390a2025ebc6390a20055be7290a20057ae7290a20005bd7190a201eebe6190a2025ebc6190a20056be6090a20057af2090a20057b82090a201e67e65cca200067d65cca2009dbe74cca20005bd74cca201debe64cca20006bd64cca2003ede63cca20006dd63cca20025fa70cca20005f970cca201ce7e658ca200067d658ca201a6be648ca20006bd648ca2003cff764ca200057f754ca200a57c754ca201be7e654ca200067d654ca20005bf744ca2009dbc744ca201b6be644ca20006bd644ca2003ede634ca20006dd634ca20005fb704ca20025f8704ca200a57e750ca200057d750ca2019e7e650ca200067d650ca20196be640ca20006bd640ca20004ff755862001cfe755862001cfc7558620004ff7458620014fe7458620006be7458620014be7458620004fd7458620006bd7458620014fc7458620004ff735862003cfc7358620006be4258620006bc4258620026f77158620096bf4158620096f63158620096f62158620024fc7058620026ef2058620026ed2058620026f61058620026f41058620004ff7654620004fd7654620024fc765462001e7e65546200067d6554620186be6454620006bd64546202bdbf7650620006bf7650620004bf76506202bebe76506202bdbd7650620006bd7650620004bd76506202bebc76506202bebf655062017ebe65506202bf3e655062017e3e6550620006bd65506202bf3d65506200063d65506202bebc65506202bebf63506202cebe6350620006bd63506202bebc6350620007af7250620055bc7250620007ac7250620005ac725062007ebd62506202c5bf715062009fb771506202bebf615062000ebe6150620096bd615062000ebc61506202bebe60506202bfaf20506202bfba105062003cff76cc620024fe76cc620004fd76cc6200a57e75cc6200057d75cc6201767e65cc6200067d65cc62016ebe64cc620006bd64cc62003ede63cc620006dd63cc620004ff764c620004fd764c620024fc764c6201667e654c6200067d654c62015ebe644c620006bd644c62003ede634c620006dd634c620005ef724c620005ec724c62000ef6614c620006f5614c62007cfd76c86201567e65c86200067d65c8620055bf74c8620055bc74c862014ebe64c8620006bd64c8620025f870c862000cff76486200057f75486200a57c75486201467e65486200067d6548620005bf744862009dbc744862013ebe6448620006bd644862000ef66148620006f56148620005fb7048620025f87048620025f976c8220056f976c82200577a75c82200577975c82200277a65c82200277965c8220027ba64c8220027b964c8220027ea72c8220057ea52c8220007e952c8220057ba42c8220057b842c8220
  | 10 => 0x9620006bc4259620004ff715962000cfe715962000cfc71596200a67f51596200067e51596200a67c5159620006bf4159620024fc70596200267e50596200267c50596200067f74596200067e74596200067d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067d43596200067c43596200067f72596200067d72596200a67c72596200067f42596200067e42596200067d42596200067c42596200063c42596200067f71596200067e71596200067d71596200067c71596200067f41596200063f41596200067e41596200067d41596200067c41596200067e31596200067c31596200067e21596200067c21596200267f70596200267e70596200267d70596200267c70596200267f40596200267e40596200267d40596200267c40596200267f30596200267e30596200267d30596200267c30596200267f20596200267e20596200267d20596200267c20596200267f10596200267e10596200267d10596200267c1059620006bf7559220006be7559220006bd7559220006bc7559220006bf7359220006be7359220006bd7359220006bc7359220006bf5359220006bc535922009ebf725922009ebe7259220006bd725922009ebc7259220006bf5259220006bc5259220006bf7159220004bf7159220006be7159220006bd7159220006bc7159220006bf5159220006be5159220006bc5159220006be3159220006bc3159220006be2159220006bc2159220026bf7059220026be7059220026bd7059220026bc7059220026bf5059220026be5059220026bd5059220026bc5059220026bf3059220026be3059220026bd3059220026bc3059220026bf2059220026be2059220026bd2059220026bc2059220026bf1059220026be1059220026bd1059220026bc1059220004ff7558e2001cfe7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e20026df7358e20006bc4258e20004ff7158e2000cfe7158e2000cfc7158e20006bf4158e20024fc7058e20026de3058e20026dc3058e20026ef2058e20026ed2058e2003cff7694e20024fe7694e20004fd7694e20024fc7694e2001e7e6594e200067d6594e20236be6494e20006bd6494e200a75f5394e20004ff7654e20024fe7654e20004fd7654e20024fc7654e2001e7e6554e200067d6554e20226be6454e20006bd6454e2008cfd7694a2001e7e6594a200067d6594a20216be6494a20006bd6494a200a76f5294a2001cff7654a20024fc7654a2001e7e6554a200067d6554a20005bf7454a2009dbc7454a20206be6454a20006bd6454a20005fb7054a20025f87054a2025dbd7690a20056bd7690a20084bd7690a2025ebf6590a201f6be6590a2025f3e6590a201f63e6590a20006b
  | 11 => 0x57ac424cb20005ef764cb20006ef764cb200076f754cb200076c754cb200076e654cb200076d654cb20007af744cb202d7ac744cb20057cf734cb2003eee634cb2003eec634cb20005ef714cb202d7af414cb20025ee704cb20025ec704cb2000cff76587200067e65587200067d6558720056f46158720004ff755872001cfe755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc7458720004ff735872003cfc7358720024fc7258720056be4258720056bc42587200aebf4158720056f72158720056f421587200aef71058720004ff7654720004fd7654720054fc765472001e7e65547200067d6554720006bf7650720006be7650720006bd7650720006bc7650720006bf655072017ebe65507200073e655072017e3e6550720006bd65507200073d65507200063d655072017ebc6550720006bf63507202cebe6350720006bd63507202cebc6350720055be7250720055bc7250720007ae3250720007ad32507200adbf7150720077b7715072000ebe61507200aebd615072000ebc615072003cff76cc720054fe76cc720004fd76cc7200b57e75cc7200057d75cc7201767e65cc7200067d65cc72003ede63cc720006dd63cc720055ee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c720054fc764c7201667e654c7200067d654c72003ede634c720006dd634c720007cd324c720005fb704c720025f8704c720025ed76c872000eed76c8720024ed76c87200576e65c87200576d65c8720057af74c8720057ac74c8720055ef73c8720005ed73c872000eee61c8720057e661c8720057e561c872000eec61c87200afaf41c87200afad41c8720025ee70c8720057ea70c8720057e970c8720025ec70c872005cff76487200057f75487200b57c75487201467e65487200067d6548720005bf7448720075bc7448720057ae4248720057ac4248720005ef764872005eef76487200076f75487200076c75487200076e65487200076d6548720007af744872031fac7448720005ef7348720005ed7348720057e7714872000eee614872000eec61487200afaf41487200afad4148720025ee7048720025ec704872001cff7654320054fc765432001e7e65543200067d6554320005ef7254320055ec7254320027ea20543201167e65cc3200067d65cc32003ede63cc320006dd63cc320055ee72cc320005ed72cc32003cff764c3200057f754c3200b57c754c3200e67e654c3200067d654c320005bf744c320075bc744c32003ede634c320006dd634c320005ef724c320055ec724c3200267f7559620004ff7459620014fe7459620004fd7459620014fc74596200a67f54596200067e54596200067d54596200a67c5459620004ff735962003cfc73596200a67f53596200a67c53596200a67f525
  | 12 => 0xf41597200b67f50597200557f76597200b67f765972001c7f76597200567f64597200067e64597200067d64597200567c64597200567f63597200567c63597200573e42597200573c42597200567f61597200067e61597200567c61597200073f41597202a76e20597200576c20597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067e43597200067d43597200067c43597200b67f72597200567e72597200567c72597200067f42597200567e42597200563e42597200067d42597200567c42597200563c42597200567e32597200567c32597200067f71597200067e71597200067d71597200067c71597200067f41597200063f41597200067e41597200067d41597200067c41597200067e31597200067c31597200567f21597200067e21597200567c21597200067f70597202a67e70597200067d70597202a67c70597200067f40597202a67e40597200067d40597202a67c40597202a67e30597202a67c30597200567f20597202a67e20597200567c20597200067f10597202a67e10597202a67c105972001cfe75d8f200567e75d8f2001c7e75d8f20004fd75d8f200567d75d8f200047d75d8f20054fc75d8f20054ff74d8f20014fe74d8f20056be74d8f20014be74d8f20004fd74d8f20056bd74d8f20004bd74d8f20054fc74d8f20056ee72d8f20056be42d8f20056bc42d8f2000cfe71d8f20004fd71d8f2000cfc71d8f20006bf41d8f20056f970d8f20004fd7698f200067e6598f200067d6598f20075be7498f20005bd7498f20056df6398f20056dc6398f2003cff7658f200067e6558f200067d6558f20056dc6358f20004ff7558f2001cfe7558f2001cfc7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f20056df7358f20006df4358f20006dc4358f20024fc7258f20056be4258f20056bc4258f20056de3258f20056dc3258f20004ff7158f2000cfe7158f2000cfc7158f20006bf4158f2003cff7694f20054fe7694f20004fd7694f20054fc7694f2001e7e6594f200067d6594f200b75f5394f20055ee7294f20005ed7294f20004ff7654f20054fe7654f20004fd7654f20054fc7654f2001e7e6554f200067d6554f2006cff7654b2001e7e6554b200067d6554b20005bf7454b20075bc7454b201e67e65ccb200067d65ccb20075be74ccb20005bd74ccb20025ed768cb20056ed768cb20024ed768cb200576e658cb200576d658cb2003eee638cb20057ce638cb20057cd638cb20056ec638cb20005ed718cb20327af418cb20025ee708cb20057ea708cb20057e9708cb20025ec708cb200057f754cb200b57c754cb201be7e654cb200067d654cb20005bf744cb20075bc744cb20057ae424cb20
  | 13 => 0x8430006f44258430006b4425843003ef7325843003ef6325843003ef5325843003ef43258430026f77058430026f67058430026f47058430026f75058430026f65058430026f55058430026f45058430026f74058430026f64058430026f54058430026f44058430026f73058430026d73058430026f63058430026f53058430026d53058430026f43058430026f72058430026f62058430026f52058430026f42058430004ff7654430004fd7654430024fc765443001e7e65544300067d6554430186be6454430006bd6454430006ee6254430006ed625443000ef66154430006f561544302bdbf7650430006bf7650430004bf76504302bebe76504302bdbd7650430006bd7650430004bd76504302bebc76504302bebf655043017ebe65504302bf3e655043017e3e6550430006bd65504302bf3d65504300063d65504302bebc65504300079f73504302cf9c7350430106be6350430005bc7250430006be62504302bfae6250430006ae6250430006bd62504302bfad6250430006ad62504302c5bf71504300c7b771504302bebf615043000ebe61504302bfb6615043000eb661504300bebd61504302bfb56150430006b5615043000ebc61504302bebe60504302bf9f30504302bfba30504302bf9d30504302cfb93050430054ff76c8430024fe76c8430004fd76c84301567e65c84300067d65c8430005bf74c84300c5bc74c843014ebe64c8430006bd64c8430056ee62c8430006ed62c843000ef661c8430006f561c8430004ff7648430004fd7648430024fc76484300057f75484300cd7c75484301467e65484300067d6548430005bf74484300c5bc744843013ebe6448430006bd6448430005df734843003ddc7348430006ee6248430006ed624843000ef66148430006f56148430005fb7048430025f870484300b4fd75d9720054ff74d9720014fe74d9720004fd74d9720054fc74d972003cfe73d9720004fd73d9720056ee72d9720056be42d9720056bc42d972000cfe71d9720004fd71d972000cfc71d9720006bf41d9720056f970d97200047d76997200b73e74997200b73d74997200567f64997200067e64997200067d64997200567c64997200567f63997200567c63997200567e62997200573e42997200573c42997200567f61997200067e61997200567c61997200073f419972032f6e20997200576c209972001cff76597200567c65597200567f7559720004ff7459720014fe7459720004fd7459720014fc74597200b67f54597200067e54597200067d54597200b67c5459720004ff735972003cfc73597200b67f53597200b67c5359720024fc72597200567e52597200567c5259720056be4259720056bc4259720004ff715972000cfe715972000cfc71597200b67f51597200067e51597200b67c5159720006b
  | 14 => 0x3eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ec5158830006ef4158830006af4158830006ee4158830006ed4158830006ec415883003eef315883003eee315883003eed315883003eec3158830026ef7058830026ee7058830026ec7058830026ef5058830026ee5058830026ed5058830026ec5058830026ef4058830026ee4058830026ed4058830026ec4058830026ef3058830026ee3058830026ed3058830026ec3058830026ef1058830026ee1058830026ed1058830026ec1058830054ff7694830024fe7694830004fd769483001e7e65948300067d6594830216be6494830006bd6494830056ee6294830006ed629483020ef66194830004ff7654830004fd7654830024fc765483001e7e65548300067d6554830005bf74548300c5bc7454830206be6454830006bd6454830005df735483003ddc7354830006ee6254830006ed62548301fef6615483025dbf7690830056bf7690830054bf769083025ebe769083025dbd7690830006bd7690830004bd7690830056bc769083025ebf65908301f6be659083025f3e65908301f63e6590830006bd659083025f3d65908300063d659083025ebc659083026f9e73908300079d739083026ebe639083029dbe72908300c7ae7290830056be629083025fae6290830056ae6290830006bd629083025fad6290830006ad6290830056bc6290830005bd71908301eebe619083025fb661908301eeb6619083025fb5619083025ebc619083025ebe609083025f9f309083025fba309083025f9d309083026fb93090830004ff755843001cfe755843001cfc7558430004ff7458430014fe7458430006be7458430014be7458430004fd7458430006bd7458430014fc745843000cfd7358430004ff7258430054fc7258430006be4258430006bc4258430024ff7158430026f77158430006f751584300bef651584300bef451584300bebf4158430006f74158430006b741584300bef64158430006f541584300bef4415843003ef7315843003ef431584300bef621584300bef42158430024fc7058430026df3058430026dd3058430026f61058430026f41058430006f77558430006f67558430006f57558430006f47558430006f77458430006f67458430006b67458430006f57458430006b57458430006f47458430006f75458430006f65458430006f55458430006f4545843003ef7735843003ef6735843003ef4735843003ef7535843003ef6535843003ef5535843003ef4535843003ef7435843003ef6435843003ef5435843003ef44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006b64258430006f5425
  | 15 => 0xc515903003ebf315903003ebe315903003ebd315903003ebc3159030006be2159030006bc2159030026bf7059030026be7059030026bd7059030026bc7059030026bf5059030026be5059030026bd5059030026bc5059030026bf3059030026be3059030026bd3059030026bc3059030026bf2059030026be2059030026bd2059030026bc2059030026bf1059030026be1059030026bd1059030026bc105903001cfe7598830004fd7598830054fc7598830054ff7498830056bf7498830014fe7498830004fd7498830054fc7498830056bc7498830054bc7498830024fe7298830026ee7298830006ef5298830056ec5298830006ef4298830056ee4298830006ed4298830056bc4298830056ec4298830056ac429883003eef3298830056ec329883000cfe7198830004fd719883000cfc7198830006bf4198830006ee2198830056ec2198830026ee2098830026ec2098830056ef7598830006ee7598830006ed7598830056ec7598830056ef7498830056af7498830006ee7498830006ed7498830056ec7498830056ac7498830006ef5498830006ee5498830006ed5498830006ec549883003eee739883003eed7398830056ec739883003eef539883003eee539883003eed539883003eec539883003eef439883003eee439883003eed439883003eec4398830056ef7198830006ee7198830006ed7198830056ec7198830006ef5198830006ee5198830006ec5198830006ef4198830006af4198830006ee4198830006ed4198830006ec419883003eef319883003eee319883003eed319883003eec3198830026ee7098830026ed7098830026ec7098830026ef5098830026ee5098830026ed5098830026ec5098830026ef4098830026ee4098830026ed4098830026ec4098830026ef3098830026ee3098830026ed3098830026ec3098830026ef1098830026ee1098830026ed1098830026ec1098830004ff755883001cfe755883001cfc7558830004ff7458830006bf7458830004bf7458830014fe7458830004fd7458830014fc7458830006bc7458830014bc7458830026ef7258830006ef5258830006ec5258830006ef4258830006ee4258830006ed4258830006bc4258830006ec4258830006ac425883003eef325883003eec3258830004ff715883000cfe715883000cfc7158830006bf4158830006ee2158830006ec2158830026ee2058830026ec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006af7458830006ee7458830006ed7458830006ec7458830006ac7458830006ef5458830006ee5458830006ed5458830006ec545883003eef735883003eee735883003eec735883003eef535883003eee535883003eed535883003eec535883003eef435883003eee435883003eed4358830
  | 16 => 0xc53003ddf714c53003fd7714c530007d7614c53000ede614c53000edc614c5300d7d4614c5300d79f414c5300d79d414c530007db704c530025de704c530025dc704c530007d8704c530025d8704c53003edf604c53003fdb604c5300d7d7104c530004fe76c8530004fd76c8530054fc76c85300067f65c85301567c65c8530005bf74c85300ddbc74c8530006bf64c853014ebc64c8530006f761c853000ef461c8530004ff7648530004fe7648530004fc76485300057f75485300e57c75485300067f65485301467c6548530005bf74485300ddbc7448530006bf644853013ebc644853001cff76541300e4fd765413003cfc76541300067f655413001e7c6554130006bf6454130126bc6454130005df735413003ddc7354130027d83054130024ff75594300267f7559430004ff7459430014fe7459430004fd7459430014fc74594300ce7f54594300067e54594300067d54594300ce7c545943003cff735943003cfe735943003cfd735943003cfc735943003e7e535943003e7c5359430004ff7259430054fc72594300ce7f52594300ce7c5259430006bc4259430004ff715943000cfe715943000cfc71594300ce7f51594300067e51594300ce7c5159430006bf4159430024fe7059430024fc70594300267e50594300267c50594300067f74594300067e74594300067d74594300067c745943003e7f735943003e7e735943003e7d735943003e7c735943003e7f435943003e7e435943003e7d435943003e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c42594300063c425943003e7f325943003e7e325943003e7d325943003e7c32594300067f71594300067e71594300067d71594300067c71594300067f41594300063f41594300067e41594300067d41594300067c415943003e7f315943003e7e315943003e7d315943003e7c31594300067e21594300067c21594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300267e30594300267d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c1059430006bf7559030006be7559030006bd7559030006bc755903003ebf735903003ebe735903003ebd735903003ebc735903003ebf535903003ebe535903003ebd535903003ebc5359030006bf7259030006be7259030006bd7259030006bc7259030054bc7259030006bf5259030006bc525903003ebf325903003ebe325903003ebd325903003ebc3259030006bf7159030004bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006b
  | 17 => 0x1e7c6554930005bf74549300ddbc7454930006bf6454930206bc6454930056bf7690930005be7690930006be7690930004be7690930006bd7690930005bc7690930056bc7690930054bc7690930006bf65909300073f65909300063f65909301f6be6590930006bd65909301f6bc65909300073c65909301f63c65909300ddbe72909300dfae7290930006bf6290930056bc6290930005bd71909301eebe61909301eebc619093026fbb309093025f9e3090930024fe768c9300067f658c9301ce7c658c930006bf648c9301a6bc648c930006ef628c930056ec628c930025fa708c930005f9708c930024fc764c9300057f754c9300e57c754c9300067f654c9301be7c654c930005bf744c9300ddbc744c930006bf644c9301b6bc644c930006ef624c930006ec624c930005fb704c930025f8704c93003fd8304c93000cfe76d85300067f65d85300067c65d85300ddbc74d8530006bf64d8530006bc64d85300d6f661d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530006bf74d8530014fe74d8530004fd74d8530014fc74d8530006bc74d8530014bc74d8530024fd73d853000cfc73d8530054fe72d8530004fd72d8530006be42d8530006bc42d85300d6bf41d85300d6f631d85300d6f421d853003cfd70d85300d6f710d85300057f75585300e57c75585300067f65585300067c6558530005bf74585300ddbc7458530006bf6458530006bc6458530005ef7258530005ec72585300d6f46158530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530006bf6454530186bc6454530006bf7650530005be7650530006be7650530004be7650530006bd7650530005bc7650530006bc7650530004bc7650530006bf65505300073f65505300063f655053017ebe6550530006bd655053017ebc65505300073c655053017e3c6550530005bc7250530006bf6250530006bc62505300d5bf71505300dfb771505300d6bf615053000ebe615053000ebc61505302cfbb30505302bf9e3050530005de76cc53003ede76cc53003f5e75cc53003f5d75cc5300075f65cc530176de65cc530176dc65cc5300075c65cc5301765c65cc5300079f64cc53033f9c64cc530006df62cc5300079e42cc53033f9c42cc5300d5dd71cc53000ede61cc53000edc61cc5300d79f41cc5300d79d41cc530025de70cc530025dc70cc53003edf60cc53003fdb60cc530024fc764c5300067f654c5301667c654c530006bf644c53015ebc644c530006f7614c53000ef4614c53003fd4314c530005fb704c530025f8704c530025dc764c53000edc764c530024dc764c5300075f654c530166de654c530166dc654c5300075c654c5301665c654c5300079f644c5303379c644c530006df624c5300079e424c5303379c424
  | 18 => 0xe76195300047e76195300067f64195300067e64195300067d64195300067c64195300073c64195300063c641953035e7f63195300073c42195300067e61195300067c61195300073f41195303567f60195303577b301953035f5e301953035f5c30195303577830195300ddbe76d91300debe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130005be72d9130005bd71d9130006be61d9130006bc61d913034fbb30d91303479e30d91303479c30d913034fb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130346bf73d913034ebe73d91300debd73d913034ebc73d9130006bf53d913034ebe53d913034ebc53d9130006bf72d9130006be72d9130054be72d9130006bd72d9130006bc72d9130006bf52d9130006bc52d913034ebf32d913034ebc32d9130006bf71d9130006be71d9130006bd71d9130004bd71d9130006bc71d9130006bf51d9130006be51d9130006bc51d913034ebf31d9130006be31d913034ebc31d9130006be21d9130006bc21d913034ebf70d9130346be70d91300debd70d9130346bc70d9130006bf50d9130346be50d9130346bc50d913034ebf30d9130346be30d91300debd30d9130346bc30d9130346be20d9130346bc20d9130006bf10d9130346be10d9130346bc10d9130024fc7654d300067f6554d3001e7c6554d30006bf6454d30226bc6454d30005fb7054d30025f87054d3003fd83054d300067f65d89300067c65d89300ddbe74d8930005bd74d8930006bf64d8930006bc64d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930006be74d8930014be74d8930004fd74d8930006bd74d8930004bd74d8930014fc74d8930006bc42d893000cfe71d8930004fd71d893000cfc71d8930006bf41d8930006ee21d8930006ec21d89300e57e75989300057d75989300067f65989300067c65989300ddbe7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300e57c75589300067f65589300067c6558930005bf74589300ddbc7458930006bf6458930006bc6458930005f771589300d5f471589300067f65189300067c65189300ddbc7418930006bf6418930006bc6418930006ed621893001cfe7518930004fd7518930054fc7518930054ff7418930056bf7418930014fe7418930004fd7418930054fc7418930056bc7418930054bc7418930056bc421893000cfe7118930004fd711893000cfc7118930006bf4118930006ee2118930056ec2118930004fe7694930004fd7694930054fc76949300067f659493001e7c6594930006bf6494930216bc6494930004ff7654930004fe7654930004fc76549300067f6554930
  | 19 => 0x4630006bf76506302bebe7650630006bd76506302bebc76506302bebf655063017ebe6550630006bd65506302bebc65506300079f73506300079c73506300d6bd6350630005bc7250630006be6250630006bd62506302c5bf71506300f7b771506302bebf615063000ebe61506300eebd615063000ebc61506302bebe60506302bf9f30506302cfbb305063000cff764c63000ef6614c630006f5614c630005fb704c630025f8704c630054ff76c8630024fe76c8630004fd76c8630005bf74c86300f5bc74c8630056ee62c8630006ed62c8630004ff7648630004fd7648630024fc76486300057f75486300fd7c7548630005bf74486300f5bc7448630005df734863003ddc7348630006ee6248630006ed624863001cfe76d95300e67e65d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300e67f54d95300067e54d95300067d54d95300e67c54d953003cfe73d9530024fd73d953003cfc73d95300e67f53d9530054fe72d9530004fd72d95300e67f52d95300e67c52d9530006bc42d953000cfe71d9530004fd71d953000cfc71d95300e67f51d95300067e51d95300e67c51d9530006bf41d953003cfd70d95300e67f50d95300e57e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300073c42d95300067e61d95300067c61d95300073f41d95303677b30d95302af5e30d95302af5c30d95303677830d95300067f74d95300067e74d95300067d74d95300067c74d95302ae7f73d95303667e73d95300067d73d95303667c73d95300067f43d95303667e43d95300067d43d95303667c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300063c42d95303667f32d95303667c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300063f41d95300067e41d95300067d41d95300067c41d95303667f31d95300067e31d95303667c31d95300067e21d95300067c21d95303667f70d95302ae7e70d95300067d70d95302ae7c70d95300067f40d95302ae7e40d95300067d40d95302ae7c40d95303667f30d95302ae7e30d95302ae7c30d95302ae7e20d95302ae7c20d95300067f10d95302ae7e10d95302ae7c10d95300e67c6559530005bf74595300ddbc7459530006bc64595300e4ff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300fcff7359530006df7359530004ff7259530054fc7259530006bc4259530004ff715953000cfe715953000cfc7159530006bf4159530114ff7059530006fb70595300057e76195300e67
  | 20 => 0xedc614c73003fd4614c7301079f414c7301079d414c730025de704c730025dc704c730107d7104c730054ff76c873003cfe76c8730004fd76c8730005bf74c873010dbc74c8730004ff7648730004fd764873003cfc76487300057f75487301157c7548730005bf744873010dbc7448730005fb7048730025f8704873001cff765433003cfc765433001e7e65543300067d6554330005df735433003ddc7354330027da30543300267f7559630004ff7459630014fe7459630004fd7459630014fc74596300fe7f54596300067d54596300fe7f5359630004ff7259630054fc72596300fe7c5259630006bc4259630004ff715963000cfe715963000cfc71596300fe7f5159630006bf4159630024fc70596300267e50596300267c505963001cff7654e30024fc7654e3001e7e6554e300067d6554e30005fb7054e30025f87054e3003fdb3054e3001cfe7598a300567e7598a3001c7e7598a30004fd7598a300567d7598a300047d7598a30054fc7598a30054ff7498a30014fe7498a30004fd7498a30054fc7498a30026ee7298a30056bc4298a3000cfe7198a30004fd7198a3000cfc7198a30006bf4198a30024fe7098a30026ee2098a30026ec2098a30004ff7558a3001cfe7558a3001cfc7558a30004ff7458a30006bf7458a30004bf7458a30014fe7458a30004fd7458a30014fc7458a30006bc7458a30014bc7458a30026ef7258a30006bc4258a30004ff7158a3000cfe7158a3000cfc7158a30006bf4158a30024fc7058a30026ee2058a30026ec2058a30054ff7694a30024fe7694a30004fd7694a3001e7e6594a300067d6594a30004ff7654a30004fd7654a30024fc7654a302a67f6554a3001e7c6554a30005bf7454a300f5bc7454a30005df7354a3003ddc7354a30056bf7690a3025ebe7690a30006bd7690a30056bc7690a3025ebf6590a301f6be6590a30006bd6590a3025ebc6590a300079e7390a300079d7390a300debd6390a3029dbe7290a300f7ae7290a30056be6290a30006bd6290a30056bc6290a30005bd7190a301eebe6190a3025ebc6190a3025ebe6090a3025f9f3090a3026fbb3090a30056ee628ca30006ed628ca30025fa708ca30005f9708ca300057f754ca300fd7c754ca30005bf744ca300f5bc744ca30006ee624ca30006ed624ca30005fb704ca30025f8704ca30004ff75586300067f75586300047f755863001cfe755863001cfc75586300067c755863001c7c7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff7258630054fc7258630006be4258630006bc4258630026f771586300eebf41586300eef63158630024fc7058630026df3058630026dd3058630026f61058630026f41058630004ff7654630004fd7654630024fc765463001e7e65546300067d655
  | 21 => 0xe76cc550004fd76cc55003cfc76cc55001d7e75cc5500057d75cc550006df63cc55003edc63cc5501775f53cc550004ff764c550004fe764c550004fc764c55001d7e754c5500057d754c550006df634c55003edc634c5501675f534c550004fe76c8550004fd76c8550054fc76c85500057f75c855001d7c75c8550005bf74c8550125bc74c8550006f761c855000ef461c8550004ff7648550004fe7648550004fc76485500057f754855001d7c7548550005bf7448550125bc744855003e7f7559730004ff7459730014fe7459730004fd7459730014fc7459730024fc735973003e7e535973003e7c5359730004ff7259730054fc72597301167f5259730006bc4259730004ff715973000cfe715973000cfc71597300067e51597301167c5159730006bf41597301167f505973001cfe7598b30004fd7598b30054fc7598b30054ff7498b30014fe7498b30004fd7498b30054fc7498b30024fe7398b30056ee7298b30056bc4298b3003eef3298b30056ec3298b3000cfe7198b30004fd7198b3000cfc7198b30006bf4198b30004ff7558b300067f7558b300047f7558b3001cfe7558b3001cfc7558b300067c7558b3001c7c7558b30004ff7458b30006bf7458b30004bf7458b30014fe7458b30004fd7458b30014fc7458b30006bc7458b30014bc7458b30024fc7358b3003eef7258b30006bc4258b3003eef3258b3003eec3258b30004ff7158b3000cfe7158b3000cfc7158b30006bf4158b3003edf3158b30054ff7694b3003cfe7694b30004fd7694b303867f6594b3001e7c6594b30004ff7654b30004fd7654b3003cfc7654b3001e7e6554b300067d6554b30005bf7454b3010dbc7454b30056bf7690b3026ebe7690b30006bd7690b30056bc7690b3026ebf6590b301f6be6590b30006bd6590b3026ebc6590b3037dbe7290b3010fae7290b30056be6290b30006bd6290b30056bc6290b30005bd7190b301eebe6190b301eebc6190b3026f9f3190b30004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc7458730024fc7358730004ff7258730054fc7258730006be4258730006bc425873003ef77158730106bf415873003ef7315873003ef43158730106f71058730004ff7654730004fd765473003cfc76547303767f655473001e7c6554730006bf76507302cebe7650730006bd76507302cebc76507302cebf655073017ebe6550730006bd65507302cebc6550730005bc7250730006be6250730006bd6250730105bf715073010fb77150730106bf615073000ebe6150730106bd615073000ebc61507301079f315073003ddf764c7300bedf764c730166de654c73003edc654c730006dd624c7300079e424c73036f9c424c73003fd7714c73003fd7614c73000ede614c730
  | 22 => 0x8950005df7358950005dc7358950005f7715895011df471589500b5fb7058950006ed6218950024fd7518950054ff7418950014fe7418950004fd7418950054fc741895003cfe7318950004fd7318950056ee521895006eed5218950056bc421895000cfe7118950004fd711895000cfc7118950006bf41189500247e76949503bd7f74949503bd7d74949500057d73949503867c639495001d7e729495001f6e72949500067f62949500076f62949500066f62949500076c62949503af3c42949500057d719495020e7e619495020e7c61949503b73f41949500257e70949500077a70949500077970949500257c709495001e7f609495001f7b6094950056bf7690950006be7690950006bd7690950056bc76909503af3f75909503af3c759095025ebf6590950006bf639095026ebc63909501f73f53909500073d5390950125be7290950127ae7290950006bf6290950056bc62909503af3e52909503af3c5290950005bd71909501eebe61909501eebc61909501f73f51909503a6bf60909501f7bb509095025f3e509095025f3c50909501f7b85090950004fe76cc950004fd76cc95003cfc76cc95001d7e75cc9500057d75cc950125be74cc950005bd74cc950004fe768c950004fd768c950054fc768c9500057f758c95001d7c758c950006df638c95003edc638c950004ff764c950004fe764c950004fc764c9500057f754c95001d7c754c950005bf744c950125bc744c950004fe760c950004fd760c950054fc760c95001d7e750c9500057d750c950006df630c95003edc630c95000cfe76d855011ef661d8550024fd75d855000cfc75d8550004ff74d8550014fe74d8550004fd74d8550014fc74d855003cfe73d8550004fd73d8550054fe72d8550004fd72d8550006be42d8550006bc42d855011ef651d855004ef551d855011ebf41d855011ef421d855001cfd70d855011ef710d855011ef4615855039dfb70585500257c765455000e7c76545500247c76545503957f74545503957d74545500057f73545503767c63545500057c72545500067f62545500073e425455038f3c425455001d7f715455001f77715455000777615455000e7e615455000e7c615455011f74615455011f3f41545500077b70545500257e70545500257c705455000778705455001e7f605455001f7b6054550006bf7650550006be7650550006bd7650550006bc765055017f3e75505500073d75505502bebf6550550006bf63505502cebc635055017f3f53505500073d5350550005bc7250550006bf6250550006bc62505500073e525055017f3c525055011dbf7150550127b7715055011ebf615055000ebe615055000ebc615055011f3f515055011f3d5150550286bf605055017fbb50505502bf3e50505502bf3c505055017fb85050550004f
  | 23 => 0x1d7e750ca500057d750ca50004ff7458650014fe7458650004fd7458650014fc7458650004ff735865003cfc73586500067e53586500367c5358650004ff7258650054fc72586500367f52586500067d5258650006be4258650006bc4258650026f7715865012e7e515865012ef65158650036f5515865012e7c515865012ebf415865012ef63158650024fe7058650024fc70586500267f50586500267d5058650026f61058650026f41058650006bf76506502bebe7650650006bd76506502bebc76506500073f755065017f3c755065011ebd65506502cebe6350650006bd63506500073e535065017f3c5350650005bc7250650006be6250650006bd625065017f3f52506500073d52506502c5bf7150650137b771506502bebf615065000ebe615065012ebd615065000ebc615065012f3e515065012f3c51506502bebe60506502bf3f505065017fbb50506502bfb8505065003cff76cc650024fe76cc650004fd76cc65001d7e75cc6500057d75cc65003ede63cc650006dd63cc6503675c53cc650004ff764c650004fd764c650024fc764c6500057f754c65001d7c754c65003ede634c650006dd634c6501675c534c65000ef6614c650006f5614c650054ff76c8650024fe76c8650004fd76c865001d7e75c86500057d75c8650005bf74c8650135bc74c8650056ee62c8650006ed62c8650004ff7648650004fd7648650024fc76486500057f754865001d7c7548650005bf7448650135bc7448650006ee6248650006ed6248650024fd75d8d50004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500fede53d8d500fedd53d8d50006df43d8d50006dc43d8d50054fe72d8d50004fd72d8d50006bc42d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50006bf41d8d502ae7f6598d50006df6398d500e5f97098d50005bf7458d50125bc7458d50115fb7058d5035e7f6518d5003ede6318d50006dd6318d500247c7654d503cd7f7454d503cd7d7454d5001d7f7354d5001f5f7354d500075f6354d5003e7e6354d5003e7c6354d500075c6354d500057c7254d503c73c4254d500057f7154d5021e7e6154d5021e7c6154d503c73f4154d500077b7054d500257e7054d500257c7054d50007787054d5001e7f6054d5001f7b6054d50125be74d8950005bd74d8950024fd75d8950004ff74d8950014fe74d8950006be74d8950014be74d8950004fd74d8950006bd74d8950004bd74d8950014fc74d89500a67f54d89500067d54d895003cfe73d8950004fd73d89500a67f53d89500067d53d89500a6ee52d89500a6ed52d89500a67c52d8950006bc42d895000cfe71d8950004fd71d895000cfc71d89500a67f51d8950006bf41d895032e7e50d895032e7c50d8950006ef629895008df97098950005bf7458950125bc745
  | 24 => 0xf7458e50004bf7458e50014fe7458e50004fd7458e50014fc7458e50006bc7458e50014bc7458e50026df7358e500e6de5358e500e6dd5358e503667c5358e50004ff7258e50054fc7258e500e67f5258e50006bc4258e50004ff7158e5000cfe7158e5000cfc7158e500067e5158e500e67c5158e50006bf4158e50024fc7058e500267f5058e500267d5058e50026de3058e50026dc3058e502ae7f6494e503e67d6494e5001d7e7394e5001f5e7394e502ae7f6394e502af5e6394e503667d6394e502af5d6394e500065d6394e500057d7294e503e73c4294e5012d7e7194e5012d7c7194e503e73f4194e502af7a7094e502ad7d7094e50367797094e50005797094e5001e7e6094e5001f7a6094e50054ff7498a50014fe7498a50004fd7498a50054fc7498a5003cfe7398a50004fd7398a500067e5398a500b67c5398a50026ee7298a500567f5298a50056ee5298a500b6ed5298a50006ef4298a50056bc4298a50056ec4298a50056ac4298a5000cfe7198a50004fd7198a5000cfc7198a500067e5198a500b67c5198a50006bf4198a50024fe7098a50024fc7098a500267f5098a500267d5098a50026ee2098a50026ec2098a50004ff7458a50006bf7458a50004bf7458a50014fe7458a50004fd7458a50014fc7458a50006bc7458a50014bc7458a50004ff7358a5003cfc7358a50026ef7258a5008eee5258a5008eed5258a50006ef4258a50006bc4258a50006ec4258a50006ac4258a50004ff7158a5000cfe7158a5000cfc7158a50006bf4158a50024fc7058a50026ee2058a50026ec2058a500073f7454a503df3c7454a502a67f6454a503de7d6454a503657c7354a500067d6354a5001d7f7254a5001f6f7254a500567e6254a502a76e6254a502a76d6254a503df3c4254a5012d7e7154a5012d7c7154a503df3f4154a502a57f7054a500077b7054a502a7787054a5001e7e6054a5001f7a6054a50056bf7690a5025ebe7690a50006bd7690a50056bc7690a501f73e7590a500073d7590a50126bd6590a5026ebe6390a50006bd6390a500073e5390a501f73c5390a5029dbe7290a50137ae7290a50056be6290a50006bd6290a50056bc6290a501f73f5290a500073d5290a50005bd7190a501eebe6190a5025ebc6190a503d73e5190a501f73c5190a5025ebe6090a5025f3f5090a501f7bb5090a5025fb85090a5003cff76cca50024fe76cca50004fd76cca503657f75cca5001d7c75cca50135be74cca50005bd74cca50054ff768ca50024fe768ca50004fd768ca5001d7e758ca500057d758ca50056ee628ca50006ed628ca50004ff764ca50004fd764ca50024fc764ca500057f754ca5001d7c754ca50005bf744ca50135bc744ca50006ee624ca50006ed624ca50054ff760ca50024fe760ca50004fd760ca50
  | 25 => 0x8d21006fb7058d21004fb7058d21024fc7058d21006f87058d21024f87058d211c4fe7618d210067f6518d210067c6518d21006bf6418d21006bc6418d2103ede6318d21006dd6318d2103cff7694d21004fe7694d21004fd7694d2103cfc7694d210067f6594d2101e7c6594d21006bf6494d21236bc6494d211475f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2101e7c6554d21006bf6454d21226bc6454d213f4fe769492120e7f659492101e7c6594921006bf6494921216bc64949211476f5294921057e4219492101cff765492100cfe76549211fcfd765492100cfc76549210067f655492101e7c6554921005bf745492113dbc7454921006bf6454921206bc6454921005f7715492100df471549211ffe42154921265be7690921056be7690921264be7690921006bf65909210073f65909210063f65909211f6be6590921006bd65909211f6bc65909210073c65909211f63c6590921006bf639092126ebe6390921006bd639092126ebc6390921055be7290921057ae7290921056bf6290921055bf71909211edbd7190921056bf61909211efae2190921057ac2190921057b4219092125ebc609092100cfe76cc92100cfc76cc9210067f65cc9211e67c65cc92113dbe74cc921005bd74cc921006bf64cc9211debc64cc921006df63cc92103edc63cc92100df671cc921005f571cc92118cfe768c9210067f658c9211ce7c658c921006bf648c9211a6bc648c92103cff764c92100cfe764c9211acfd764c92100cfc764c9210057f754c9211457c754c9210067f654c9211be7c654c921005bf744c92113dbc744c921006bf644c9211b6bc644c921006df634c92103edc634c921005f7714c92100df4714c9211c4fe760c9211457e750c9210057d750c9210067f650c92119e7c650c921006bf640c921196bc640c9210077765c85210077465c8521057b774c8521057b474c8521007b764c85213efb464c852100df672c852100fe672c852100ef762c852100fe762c8521057b642c8521057b442c85210067f65d81210067c65d8121006bf64d8121006bc64d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d812103cfe73d8121004fd73d8121006be42d8121006bc42d81210aebf41d81210aebd41d81210aefa10d81211457e75981210057d75981210067f65981210067c659812113dbe7498121005bd7498121006bf6498121006bc6498121006fb60981210057f75581211457c75581210067f65581210067c6558121005bf745812113dbc7458121006bf6458121006bc6458121005df7358121005dc73581210067f65181210067c6518121006bf6418121006bc6418121026fa6018121006f96018121004ff7458e50006b
  | 26 => 0x20e7e10d952120e7d10d952120e7c10d95211467c6559521005bf745952113dbc7459521006bc64595213fdef725952120cff75595210067f7559521004ff7459521006bf7459521004bf7459521014fe7459521004fd7459521014fc7459521006bc7459521014bc7459521004ff735952103cfc73595213fcff7259521006ef7259521006bc42595211fcff7159521006f771595211febf41595211febd4159521004ff7059521024fc705952120d7e76195211467e761952120c7e76195210067f64195210067e64195210067d64195210067c64195210073c64195210063c64195213f67f62195210073c42195213f67f61195213f73f41195213f73d41195213f76e21195213f76c21195213f7742119521265be76d912113ebe76d9121014be76d9121006bf65d91210073f65d91210063f65d9121006be65d9121006bd65d9121006bc65d91210073c65d91210063c65d9121055bc72d91211efae21d91211efac21d91211efb421d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006bc53d91211eebf72d912113ebe72d91211eebd72d91211eebc72d9121006bf52d9121006bc52d91211eebf71d9121054bf71d91211eebe71d91211eebd71d91211ecbd71d91211eebc71d91211eebf51d91211eebe51d91211eebd51d91211eebc51d91211eebf31d91211eebe31d91211eebd31d91211eebc31d91211eebf21d91211eebe21d91211eebd21d91211eebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006bc50d91211eebf10d91211eebe10d91211eebd10d91211eebc10d912103cfe76d8d210067f65d8d210067c65d8d21006bf64d8d21006bc64d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d21006bc42d8d21054ff71d8d211c4fd71d8d211c6bf41d8d211c6bd41d8d211c6df31d8d211c6dd31d8d21024fe70d8d21004fd70d8d211457e7598d210057d7598d210067f6598d210067c6598d2113dbe7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d211aded7298d210057f7558d211457c7558d210067f6558d210067c6558d21005bf7458d2113dbc7458d21006bf6458d21006bc6458d211d5ef7258d21005fb7058d21005f87058d21004ff7558d210067f7558d210047f7558d2101cfe7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21004fd7458d21014fc7458d21006bc7458d21014bc7458d21006df7358d211d4ff7258d21006ef7258d21006bc4258d211acff7158d21006f77158d211aebf4158d211aebd4158d21004ff705
  | 27 => 0xf4158f211aebd4158f211aedf3158f211aedd3158f21004ff7058f21024fc7058f2103cff7694f21054fe7694f21004fd7694f21054fc7694f210067f6594f2101e7c6594f21006bf6494f21236bc6494f211575f5394f2100df67194f21005f57194f21004ff7654f21054fe7654f21004fd7654f21054fc7654f2101e7e6554f210067d6554f21006bf6454f21226bc6454f213fcff7654b210567f6554b210567c6554b21005bf7454b2114dbc7454b21056bf6454b21056bc6454b211ffe62154b211acfd76ccb2114dbe74ccb21005bd74ccb21056bf64ccb21056bc64ccb21056df63ccb21056dc63ccb211d4ff764cb210057f754cb211557c754cb21005bf744cb2114dbc744cb21056bf644cb21056bc644cb21056df634cb21056dc634cb211557e75983210057d759832114dbe7498321005bd7498321056bf6498321056bc6498321056fb6098321026f86098321005bf745832114dbc7458321056bf6458321056bc6458321056f86058321004ff755832101cfe755832101cfc7558321004ff7458321006bf7458321004bf7458321014fe7458321004fd7458321014fc7458321006bc7458321014bc7458321004ff735832103cfc735832100cfc7258321056be4258321056bc425832107ebf415832107ebd4158321056fb2058321056f8205832107efa105832101cfe76d95211467e65d9521006bc64d9521004ff74d9521014fe74d9521004fd74d9521014fc74d95211467f54d95210067e54d95210067d54d95211467c54d952103cfe73d9521004fd73d95211467f53d95211467c53d952100cfd72d95211467f52d9521006bc42d9521054ff71d952120cfd71d952120e7f51d952120e7d51d952120ebf41d952120ebd41d9521024fe70d9521004fd70d95211467f50d95211467c50d95213f57e76d952101c7e76d95210067f64d95210067e64d95210067d64d95210067c64d95210073c64d95210063c64d95210073c42d952120f3f41d952120f3d41d952120f6e21d952120f6c21d952120f7421d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d952120e7f72d95211467e72d952120e7d72d95210067f42d95210067e42d95210067d42d95210067c42d95210063c42d952120e7f71d952120e7e71d952120e7d71d952120e7c71d952120e7f41d952120e3f41d952120e7e41d952120e7d41d952120e3d41d952120e7c41d952120e7f31d952120e7e31d952120e7d31d952120e7c31d952120e7f21d952120e7e21d952120e7c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d952120e7f10d9521
  | 28 => 0x8131014fc74d8131054fe72d8131004fd72d8131006be42d8131006bc42d813103cfd71d8131106bf41d8131106bd41d8131106fa10d8131006fb60981310057f75581311657c7558131005bf745813115dbc7458131005ef7258131005ec72581311657e75181310057d751813115dbe7418131005bd7418131005ee7218131005ed7218131026fa6018131006f960181311fcfd75d9721054ff74d9721014fe74d9721004fd74d9721054fc74d972103cfe73d9721004fd73d97211567c53d9721054fe72d9721056ee72d97210567f52d9721056be42d9721056bc42d9721056f571d972120e7e51d972120e7c51d972120ebf41d972120ebd41d9721024fe70d9721004fd70d97211567f50d972101cff76597210567c6559721005bf745972114dbc7459721056bf6459721056bc64597210567f7559721004ff7459721006bf7459721004bf7459721014fe7459721004fd7459721014fc7459721006bc7459721014bc74597211567f54597210067d5459721004ff735972103cfc73597211567f535972100cfe725972100cfc72597210567e52597210567c5259721056be4259721056bc42597211fe7f51597211fe7d51597211febf41597211febd4159721004ff7059721024fc70597211567c5059721056bf75d9321056be75d9321056bd75d9321056bc75d9321056bf73d9321056be73d9321056bd73d9321056bc73d9321006bf53d9321006bc53d9321056be72d9321054be72d9321056ae72d9321056bf52d9321056be52d9321056bc52d9321056be32d9321056bc32d9321056bd71d9321056b571d93211eebf51d93211eebe51d93211eebd51d93211eebc51d93211eebf31d93211eebe31d93211eebd31d93211eebc31d9321056bf21d9321056be21d9321056bc21d9321056bf70d9321056be70d9321056bd70d9321056bc70d9321006bf50d9321006bc50d93211eebf10d93211eebc10d932101cfe75d8f21004fd75d8f21054fc75d8f21054ff74d8f21014fe74d8f21004fd74d8f21054fc74d8f21054fe72d8f21056ee72d8f21056be42d8f21056bc42d8f21056f571d8f211c6bf41d8f211c6bd41d8f21024fe70d8f21004fd70d8f211acfd7698f2114dbe7498f21005bd7498f21056bf6498f21056bc6498f21056df6398f21056dc6398f2103cff7658f210057f7558f211557c7558f21005bf7458f2114dbc7458f21056bf6458f21056bc6458f21056dc6358f21004ff7558f210067f7558f210047f7558f2101cfe7558f2101cfc7558f210067c7558f2101c7c7558f21004ff7458f21006bf7458f21004bf7458f21014fe7458f21004fd7458f21014fc7458f21006bc7458f21014bc7458f21056df7358f2100cfe7258f2100cfc7258f21056be4258f21056bc4258f21056de3258f21056dc3258f211aeb
  | 29 => 0xcfc7654d310067f6554d3101e7c6554d3141ddf7354d3103f5c5354d31005f77154d3100df47154d3103fd43154d3115dbe74d8931005bd74d893101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931006be74d8931014be74d8931004fd74d8931006bd74d8931004bd74d8931014fc74d8931006bc42d893103cfd71d89311d6bf41d89311d6bd41d89311d6ef21d8931024fe70d8931004fd70d8931006ef62989310057f75589311657c7558931005bf745893115dbc7458931005fb7058931005f870589311657e75189310057d7518931006ed621893101cfe75189310567e751893101c7e7518931004fd75189310567d75189310047d7518931054fc7518931054ff7418931014fe7418931004fd7418931054fc7418931056dd7318931056bc4218931054ff711893103cfd711893118ebf411893118ebd4118931056ef211893118eed2118931024fe7018931004fd7018931004fe7694931004fd7694931054fc76949310067f659493101e7c659493103dde7394931005dd73949311675c5394931004ff7654931004fe7654931004fc765493101e7e65549310067d6554931005bf745493115dbc7454931005df735493103ddc73549311675f5354931005f7715493100df47154931056bf7690931006be7690931006bd7690931056bc7690931006bf65909311f6be6590931006bd65909311f6bc65909310079e73909310079d73909311eebf63909314179f53909314179c5390931265be729093115fae7290931006bf6290931056bc62909311edbd71909311eebf619093126fb731909311ef9e31909311ef9c31909311efb4319093125ebc60909311efb7109093118dde76cc93103ede76cc931165de75cc93103ddc75cc93103f9e74cc93103f9d74cc931056dc62cc9310079e42cc93140f9c42cc93100dde71cc93100ddc71cc93103edf61cc93103fd761cc9311d79f41cc9311d79d41cc931005dd70cc9311d7d710cc93100cfe768c9311addd738c931006ef628c931056ec628c93100df6718c931005f5718c93103fd4318c93100cfc764c9310057f754c9311657c754c931005bf744c93115dbc744c931006ef624c931006ec624c931005f7714c93100df4714c93100ddc764c9311aedc764c93100cdc764c9310075f754c931165de754c931165dc754c9310075c754c9311655c754c9310079f744c9314079c744c93103ddf724c93103fcf724c931007cf624c931056dc624c931007cc624c9310079e424c9314079c424c931007d7714c93100dde714c93100ddc714c9311afd4714c93100dd4714c93103edf614c93103fd7614c9311af9f414c9311af9d414c931005df704c9311afd7104c93101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d
  | 30 => 0xe7458b31004fd7458b31014fc7458b31006bc7458b31014bc7458b3100cfc7358b3103eef7258b31006ef4258b31006bc4258b31006ec4258b31006ac4258b3103eef3258b3103eec3258b311aebf4158b311aebd4158b311aeef2158b31004ff7058b31024fc7058b31054ff7694b3103cfe7694b31004fd7694b3101e7e6594b310067d6594b3103dde7394b31005dd7394b313875c5394b31004ff7654b31004fd7654b3103cfc7654b3101e7e6554b310067d6554b31005bf7454b3116dbc7454b31005df7354b3103ddc7354b311775f5354b31056bf7690b3126ebe7690b31006bd7690b31056bc7690b3126ebf6590b311f6be6590b3126f3e6590b311f63e6590b31006bd6590b3126f3d6590b310063d6590b3126ebc6590b3126f9e7390b310079d7390b311eebe6390b3142f9f5390b3126f9c5390b31265be7290b3116fae7290b31056be6290b31006bd6290b31056bc6290b3126f9f3290b311edbd7190b311eebd6190b311ef9e3190b311efb63190b311ef9c3190b3125ebe6090b3103ddf764cb31006df764cb310075f754cb31175de754cb31175dc754cb310075c754cb311755c754cb3103f5e654cb3103f5d654cb310079f744cb314279c744cb3103fcf724cb31056de624cb310079e424cb314279c424cb3100dde714cb3100ddc714cb311af9f414cb311af9d414cb31005df704cb31004ff755833101cfe755833101cfc7558331004ff7458331006bf7458331004bf7458331014fe7458331004fd7458331014fc7458331006bc7458331014bc745833100cfc7358331004ff7258331054fc7258331006be4258331006bc42583310d6bf41583310d6bd415833103ef6315833103ef5315833103efb705833103efb305833103ef830583310d6fa105833101cfe76d95311667e65d953103dde73d953100ddd73d95311675f53d9531004ff74d9531014fe74d9531004fd74d9531014fc74d95311667f54d95310067d54d953100cfd73d953122edd73d953100cdd73d95311667f53d9531166df53d95311665f53d9531166dc53d9531054fe72d9531004fd72d95311667c52d9531006bc42d953103cff71d953103cfd71d953122e7f51d953122e7d51d953122ebf41d953122ebd41d9531024fe70d9531004fd70d95311667c50d95311667c655953141ddf73595311675c535953122cff75595310067f7559531004ff7459531014fe7459531004fd7459531014fc745953141cff7359531006df7359531166df53595313767e53595313767c5359531166dc5359531004ff7259531054fc72595311667f5259531006bc425953121cff7159531006f7715953121e7e515953121e7c515953121ebf415953121ebd4159531004ff7059531024fc70595311667f505953101cff7654d3100cfe7654d3121cfd7654d31
  | 31 => 0x81410079c73581410059c7358141006bf6358141006bd6358141005bf7258141007af7258141005af7258141005bc7258141007ac7258141005ac7258141006be6258141006bc625814144dbf7158141007b77158141045b7715814144ebf615814102fb76158141007bb60581412bebe6058141445be761814117dbe75181412bf3e751814117d3e7518141005bd75181412bf3d75181410053d75181412bdbc75181412cdbe7318141005bd7318141006be6318141006bc6318141005be7218141005bd7218141006be6218141006bc6218141015bf711814100dbe7118141015bd711814100dbc71181412c6bf611814143fb761181412bdbe70181412bebf60181412bfba60181412bebd6018141007b960181412bfba1018141437b9101814103e7f7559731004ff7459731014fe7459731004fd7459731014fc74597311767f54597310067e54597310067d54597311767c545973100cfe735973100cfc735973103edc735973100cdc7359731176df535973103e7e535973103e7c535973103edc5359731004ff7259731054fc72597311767f52597311767c5259731006bc425973121e7f515973121e7d515973121ebf415973121ebd4159731004ff7059731024fc70597311767f50597311767c50597310067f74597310067e74597310067d74597310067c745973103e7f73597311765f735973103e7e735973103e7d735973103e7c735973103e5c735973103e7f435973103e7e435973103e7d435973103e7c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067e42597310067d42597310067c42597310063c425973103e7f325973103e7e325973103e7d325973103e7c325973121e7f715973121e7e715973121e7d715973121e7c715973121e7f415973121e3f415973121e7e415973121e7d415973121e3d415973121e7c415973103e7f315973103e7e315973103e7d315973103e7c315973121e7f215973121e7e215973121e7d215973121e7c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067d40597310067c405973103e7f305973103e7e305973103e7d305973103e7c305973121e7f105973121e7e105973121e7d105973121e7c105973101cfe7598b31004fd7598b31054fc7598b31054ff7498b31014fe7498b31004fd7498b31054fc7498b3100cfe7398b31056de7398b3100cde7398b3100cfc7398b31056ee7298b31006ef4298b31056bc4298b31056ec4298b31056ac4298b31056df3298b3103eef3298b31056ec3298b311c6bf4198b311c6bd4198b31056ef2198b311c6ed2198b31024fe7098b31004fd7098b31004ff7558b3101cfe7558b3101cfc7558b31004ff7458b31006bf7458b31004bf7458b31014f
  | 32 => 0x17faf52549410073e525494117f3c525494117fac52549411fdbf715494100dbe715494100dbc71549411febf6154941207b761549411ff3f51549411ff3d5154941005bf70549412bdbc705494117f3c50549412cdbf76cc941005be76cc9412cebe76cc941004be76cc941005bd76cc9412cebd76cc941004bd76cc9412cdbc76cc9412cdbf75cc94117dbe75cc941005bd75cc9412cdbc75cc941056bc62cc9411d5bf71cc94100dbe71cc9411d5bd71cc94100dbc71cc9411d6bf61cc9411dfb761cc9411d79f31cc9412bdbe70cc941005bd70cc941005bf768c941005be768c941005bd768c941005bc768c941005bf758c94117dbe758c941005bd758c94117dbc758c9411adbd738c94118dbe728c941007af628c941056bc628c941007ac628c941056ac628c9410079f328c9412cfaf328c94100dbe718c9411c5bd718c94100dbc718c9411c6bf618c9411a7b7618c9412bdbe708c941005bd708c941005bf764c941006bf764c941004bf764c941005be764c941005bd764c941005bc764c941006bc764c941004bc764c941005bf754c9410073f754c9410053f754c94117dbe754c941005bd754c94117dbc754c9410073c754c94117d3c754c941007af624c941056bc624c941007ac624c941006ac624c9412cfaf324c9410079e324c9411adbf714c94100dbe714c94100dbc714c9411aebf614c9411b7b7614c941005bf704c9412bdbc704c9412cdbf760c941005be760c941005bd760c9412cdbc760c9412cdbf750c94117dbe750c9412cf3e750c94117d3e750c941005bd750c9412cf3d750c9410053d750c9412cdbc750c9411d5be730c9411c5be720c941056bc620c9412cf9f320c9412cfae320c9410079d320c9412cfad320c94118dbf710c94100dbe710c94118fb6710c94100db6710c94118dbd710c9412cfb5710c941005b5710c94100dbc710c94118ebf610c941197b7610c9412bdbe700c941005bd700c94117dbe75d8141005bd75d814117dbc75d8141006bf65d8141006bd65d81412cdbe73d8141005bd73d8141006bf63d8141006bd63d8141005be72d8141005bd72d8141006be62d8141006bc62d8141015bf71d8141015bd71d8141446bf61d814145fb761d8141447ba10d8141447b910d814144dbd769814117dbe7598141005bd75981412bdbc75981412cdbe7398141005bd7398141006be6398141006bc6398141005be7298141005bd7298141006be6298141006bc6298141455bd71981412bfb5719814102db571981412c6bf6198141047b761981412bdbe70981412bebf6098141007bb6098141005bf75581410073f75581410053f755814117dbe755814117dbc75581410073c755814117d3c7558141006bf6558141006bd6558141005bf73581410079f73581410059f73581412cdbc735
  | 33 => 0xf21d894146fad21d89412bdbe70d8941005bd70d8941475bd769894117dbe7598941005bd759894117dbc7598941006bf6598941006be6598941006bd6598941006bc65989412cdbe7398941005bd7398941006bf6398941006be6398941006bd6398941006bc6398941265be7298941006bf6298941007af62989411edbd7198941007b5719894113db571989411eebf619894114fb761989412bdbe7098941005bd7098941005bf75589410073f75589410053f755894117dbe755894117dbc75589410073c755894117d3c7558941005bf73589412cdbc7358941007af6258941006be6258941475bf7158941007b7715894114db77158941476bf615894113fb76158941005bf70589412bdbc705894146dbe761894117dbe75189410073e751894117d3e7518941005bd75189410073d75189410053d751894117dbc7518941006bf6518941006be6518941006bd6518941006bc65189412cdbe7318941005bd7318941006bf6318941006be6318941006bd6318941006bc63189411edbe7218941006bf6218941007ae6218941006bd6218941007ad6218941006ad6218941007af5218941007ac5218941015bf711894100dbe7118941015bd711894100dbc7118941266bf6118941467b76118941267af2118941267ad21189412bdbe7018941005bd7018941056bf7518941056be75189410563e7518941056bd75189410563d7518941056bc7518941056bf7318941056be7318941056bd7318941056bc7318941006bf5318941006be5318941006bd5318941006bc5318941056bf5218941006af5218941056bc5218941056ac5218941056bf7118941054bf7118941056bd7118941014bd7118941266bf5118941266be5118941266bd5118941266bc5118941266bf3118941266be3118941266bd3118941266bc3118941056bf2118941056af2118941056be2118941056bd2118941266ad2118941056bc2118941056bf7018941056be7018941056bd7018941056bc7018941006bf5018941006bc5018941266bf1018941266be1018941266bd1018941266bc1018941005bf7694941005be7694941005bd7694941005bc76949411fdbd75949410073f659494117f3c65949412cdbe7394941005bd73949410073e539494117f3c53949413f5be7294941056bc629494117f3f529494117faf529494117fac529494100dbe719494120dbd719494100dbc719494120ebf6194941217b7619494120f3e519494120f3c51949412bdbe7094941005bd709494117f3f5094941005bf7654941006bf7654941004bf7654941005be7654941005bd7654941005bc7654941006bc7654941004bc765494120dbf755494117f3e65549410073d6554941005bf73549412cdbc735494117f3f53549410073d53549413fdbf7254941056bc6254941
  | 34 => 0x95410073f655954117ebe655954117ebc655954117f3c6559541005bf73595412cdbc735954117f3c5359541005bf7259541007af7259541005af7259541005bc7259541007ac7259541005ac725954117f3f52595414bdbf7159541007b771595414c5b771595414bebf6159541187b761595414bf3e51595414bf3c5159541005bf70595412bdbc705954117f3f505954117dbe75d8d410073e75d8d4117d3e75d8d41005bd75d8d410073d75d8d410053d75d8d4117dbc75d8d41005be72d8d41005bd72d8d41015bf71d8d41015bd71d8d414a6bf61d8d414b7b761d8d414a79f31d8d414a79d31d8d412bdbe70d8d41005bd70d8d414adbd7698d4117dbe7598d412cf3e7598d4117d3e7598d41005bd7598d412cf3d7598d410053d7598d412cdbc7598d41006bf6598d41006bd6598d4148dbe7398d412cebf6398d410079f6398d41005be7298d412cfae7298d41005ae7298d41005bd7298d412cfad7298d41005ad7298d4149dbd7198d412cfb57198d4115db57198d4149ebf6198d4116fb76198d412bdbe7098d41005bd7098d41005bf7558d4117dbe7558d4117dbc7558d410079f6358d412cebe6358d41005bf7258d41005bc7258d414adbf7158d41007b77158d4116db77158d414aebf6158d4115fb76158d41005bf7058d412bdbc7058d414a5be7618d4117dbe7518d41005bd7518d412cdbc7518d41006bf6518d41006bd6518d4149dbe7318d412cebf6318d412cf9e6318d412cebd6318d410079d6318d41005be7218d41005bd7218d41015bf7118d4100dbe7118d41015bd7118d4100dbc7118d4148ebf6118d41497b76118d4148f9f3118d4148f9d3118d412bdbe7018d41005bd7018d412cdbf7694d41005be7694d41005bd7694d412cdbc7694d4121dbd7594d4117f3e6594d410073d6594d41485be7394d412cf3f5394d4117f9f5394d4117f1f5394d412cf9c5394d41005be7294d41005bd7294d4117f3c5294d4122dbf7194d4100dbe7194d4122fb67194d4100db67194d4122dbd7194d412cfb57194d41005b57194d4100dbc7194d4122ebf6194d41237b76194d4122f3f5194d4122f3d5194d412bdbe7094d41005bd7094d4117f3c5094d41005bf7654d41005be7654d41005bd7654d41005bc7654d4122dbf7554d410073f6554d4117f3c6554d4141dbf7354d4117f9f5354d412cf3e5354d412cf3c5354d4117f9c5354d41005bf7254d41005bc7254d4117f3f5254d4121dbf7154d4100dbe7154d4100dbc7154d4121ebf6154d41227b76154d4121f3e5154d4121f3c5154d41005bf7054d412bdbc7054d4117f3f5054d4117dbe75d8941005bd75d894117dbc75d89412cdbe73d8941005bd73d8941007af52d8941007ac52d8941015bf71d8941015bd71d894146ebf61d894147fb761d894146fa
  | 35 => 0x3cfe73d8951004fd73d89514feee52d89514feed52d8951006ef42d8951006bc42d8951006ec42d8951006ac42d895101cfd71d89513febf41d89513febd41d89513feef21d8951024fe70d8951004fd70d8951006ef6298951145f57198951005bf7458951185bc7458951155f77158951006ed6218951007ac421895100cfd75189510567d7518951054ff7418951014fe7418951004fd7418951054fc741895103cfe7318951004fd73189510067e53189514f67c53189510567f5218951056ee52189514f6ed5218951006ef4218951056bc4218951056ec4218951056ac4218951054ff711895101cfd71189513f67e51189513f67c51189513f6bf41189513f6bd4118951056ef21189513f6ed2118951024fe7018951004fd70189514f67f501895100d7c76549511fe7c765495100c7c76549510073f74549514ef3c74549514ee7f64549514ee7d64549513757c73549510067f635495101d7f725495101f6f72549510076f62549510567c62549510076c62549514ef3c425495100777715495100d7e715495100d7c71549511ff74715495101e7f615495101f7761549511ff3f41549510057f70549512a67c6054951056bf7690951006be7690951006bd7690951056bc76909511f73e75909510073d75909511eebf6590951006bf639095126ebc63909510073e53909511f73c5390951265be7290951187ae7290951006bf6290951056bc62909511f73f52909510073d52909511edbd71909511eebf61909511f7b751909511ef3e51909511ef3c51909511efb4519095125ebc60909511f73f5090951004fe76cc951004fd76cc95103cfc76cc9513757f75cc95101d7c75cc951185be74cc951005bd74cc951004fe768c951004fd768c951054fc768c95101d7e758c9510057d758c951004ff764c951004fe764c951004fc764c9510057f754c95101d7c754c951005bf744c951185bc744c951004fe760c951004fd760c951054fc760c95101d7e750c9510057d750c951024fe76d815100cfd75d8151004ff74d8151014fe74d8151004fd74d8151014fc74d815103cfe73d8151004fd73d8151054fe72d8151004fd72d8151006be42d8151006bc42d815101cfd71d8151286bf41d8151286bd41d815139efa50d8151286fa10d815128e7f6598151006fb609815128e7f6518151185be7418151005bd7418151026fa6018151006f960181514e5be76d95414bdbd75d954117ebe65d954117f3e65d954117e3e65d954117ebc65d95412cdbe73d9541005bd73d954117f3f53d9541005be72d9541005bd72d954117f3c52d9541015bf71d954100dbe71d9541015bd71d954100dbc71d95414cebf61d95414dfb761d95414cf3f51d95414cf3d51d95412bdbe70d9541005bd70d954117f3c50d95414d5bf76595414cdbf755
  | 36 => 0xd71594320067c71594320067f41594320063f41594320067e41594320067d41594320067c415943203e7f315943203e7e315943203e7d315943203e7c31594320567f21594320067e21594320567c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067d40594320067c405943203e7f305943203e7e305943203e7d305943203e7c30594320567f20594320567c20594320067f10594320067c10594321ccff765483201e7e65548320067d6554832005bf7454832195bc7454832055df764c832006df764c832004df764c8320075f754c8320075c754c8320575e654c8320575d654c8320079f744c8325179c744c832055df724c83203fcf724c832056de624c832057ce624c832057ce524c832007cd524c8320579e424c8320579c424c8325179f414c832004ff755843201cfe755843201cfc7558432004ff7458432014fe7458432004fd7458432014fc7458432056be4258432056bc425843203edf3258432006dd3258432056f7715843218ebf415843218ef64158432006f5415843203ef7315843203ef43158432056f72158432056f42158432004ff7058432024fc705843218ef71058432004ff755803201cfe755803201cfc7558032004ff7458032006bf7458032004bf7458032014fe7458032004fd7458032014fc7458032006bc7458032014bc7458032056be4258032056bc425803203eee325803203eed3258032004ff715803200cfe715803200cfc7158032006bf4158032056fb7058032006fa4058032006f9405803203efb305803203ef83058032056fb2058032056f8205803203cfe76d8d51185be74d8d51005bd74d8d5100cfd75d8d5141e7d75d8d51004ff74d8d51014fe74d8d51006be74d8d51014be74d8d51004fd74d8d51006bd74d8d51004bd74d8d51014fc74d8d5150ede53d8d5150edd53d8d513767c53d8d51054fe72d8d51004fd72d8d5150e7f52d8d51006bc42d8d5101cfd71d8d5141e7e51d8d5141e7c51d8d5141ebf41d8d5141ebd41d8d5141edf31d8d51024fe70d8d51004fd70d8d5150e7f50d8d51006df6398d513775c5398d51165f57198d511675c5358d51175f77158d5103ede6318d51006dd6318d5100d7e7694d5122e7e7694d5100c7e7694d515067f6494d515067d6494d5101d7e7394d5101f5e7394d513767f6394d510075f6394d510065f6394d513775c6394d510057d7294d515073c4294d5100d7e7194d5122f767194d51377757194d5100d7c7194d5101e7f6194d5101f776194d5122f3f4194d510057d7094d512ae7c6094d51185be74d8951005bd74d8951007ac42d895100cfd75d8951004ff74d8951014fe74d8951006be74d8951014be74d8951004fd74d8951006bd74d8951004bd74d8951014fc74d8951
  | 37 => 0x932006bd65909321f6bc65909320073c65909321f63c6590932056bf6390932055be7290932057ae7290932056bf629093226faf3290932057ac3290932005bd71909321eebe61909321eebc619093225ebc60909320067f658c9321ce7c658c932006bf648c9321a6bc648c93203dee728c93203eef628c9320075f658c9320075c658c9320079f648c93251f9c648c932055de728c932056df628c93203fcf628c9320579e428c9320579c428c932005dd718c93251f9f418c93200cfe76d85320067f65d85320067c65d85321b5bc74d8532006bf64d8532006bc64d85321aef661d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532006bf74d8532014fe74d8532004fd74d8532014fc74d8532006bc74d8532014bc74d853203cfd72d8532006be42d8532006bc42d85321aebf41d85321aef631d85321aef621d8532024fe70d8532004fd70d85321aef410d85320057f75585321bd7c75585320067f65585320067c6558532005bf74585321b5bc7458532006bf6458532006bc64585321aef46158532005fb7058532005f870585320067f65d81320067c65d8132006bf64d8132006bc64d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d8132006be42d8132006bc42d813200cfe71d8132004fd71d813200cfc71d8132006bf41d8132006fb10d8132006f810d81321bd7e75981320057d75981320067f65981320067c65981321b5be7498132005bd7498132006bf6498132006bc6498132006fb60981320057f75581321bd7c75581320067f65581320067c6558132005bf74581321b5bc7458132006bf6458132006bc6458132005f771581321adf471581320067f65181320067c6518132006bf6418132006bc6418132026fa6018132006f96018132054ff75594320567f7559432004ff7459432014fe7459432004fd7459432014fc745943219e7f54594320067e54594320067d545943219e7c545943203cfe735943203cfc735943203e7e535943203e7c5359432054fe7259432054fc72594320567e52594320567c5259432056be4259432056bc4259432004ff715943200cfe715943200cfc715943219e7f51594320067e515943219e7c5159432006bf4159432004ff7059432024fc705943219e7f505943219e7c50594320067f74594320067e74594320067d74594320067c745943203e7f735943203e7e735943203e7d735943203e7c735943203e7f435943203e7e435943203e7d435943203e7c435943219e7f72594320567e72594320567c72594320067f42594320567e42594320563e42594320067d42594320567c42594320563c425943203e7f32594320567e325943203e7d32594320567c32594320067f71594320067e71594320067
  | 38 => 0x3867f72d95321be7e72d95320067d72d95320067f42d95320067e42d95320067d42d95320067c42d95320063c42d95323867f32d95323867c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320063f41d95320067e41d95320067d41d95320067c41d95323867f31d95320067e31d95323867c31d95320067e21d95320067c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d95323867f30d95323867c30d95320067f10d95320067c10d95321be7c6559532005bf74595321b5bc7459532006bc64595321bcff75595320067f7559532004ff7459532006bf7459532004bf7459532014fe7459532004fd7459532014fc7459532006bc7459532014bc74595321ccff7359532006df73595321e4ff7259532006ef7259532006bc4259532004ff715953200cfe715953200cfc7159532006bf4159532004ff7059532024fc70595320057e76195321be7e76195320047e76195320067f64195320067e64195320067d64195320067c64195320073c64195320063c641953252e7f62195320073c421953252f6f321953252f6c32195320067e61195320067c61195320073f41195321b5be76d91321b6be76d9132014be76d9132006bf65d91320073f65d91320063f65d9132006be65d9132006bd65d9132006bc65d91320073c65d91320063c65d9132055bc72d913226faf32d913226fac32d9132005bd71d9132006be61d9132006bc61d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132006bf73d913226ebe73d91321b6bd73d913226ebc73d9132006bf53d913226ebe53d913226ebc53d913226ebf72d91321b6be72d91321b6bd72d91321b6bc72d9132006bf52d9132006bc52d913226ebf32d91321b6bd32d913226ebc32d9132006bf71d9132006be71d9132006bd71d9132004bd71d9132006bc71d9132006bf51d9132006be51d9132006bc51d913226ebf31d9132006be31d913226ebc31d9132006be21d9132006bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006bc50d913226ebf30d913226ebc30d9132006bf10d9132006bc10d913201cfc7654d320067f6554d3201e7c6554d32006bf6454d32226bc6454d32005ef7254d32005ec7254d3203fcc3254d321e4fe76949320067f659493201e7c6594932006bf6494932216bc64949321bf6f5294932057ac429493201cff76549321bcfd765493203cfc76549320067f655493201e7c6554932005bf74549321b5bc7454932006bf6454932206bc6454932005df735493203ddc7354932527ac4254932005be7690932056be76909321dcbe7690932006bf65909320073f65909320063f65909321f6be659
  | 39 => 0xb705833203efb305833203ef830583321ccfd75d9632054ff74d9632014fe74d9632004fd74d9632054fc74d9632056dd73d96323867e53d96323867c53d9632056ee72d96320567f52d9632056be42d9632056bc42d963200cfe71d9632004fd71d963200cfc71d96320067e51d96321ce7c51d9632006bf41d9632024fe70d9632004fd70d96321ce7f50d963201cff76596320567c65596320567f7559632004ff7459632014fe7459632004fd7459632014fc74596321ce7f54596320067d54596321ce7f5359632054fc72596320567e52596320567c5259632056be4259632056bc4259632004ff715963200cfe715963200cfc71596321ce7f5159632006bf4159632004ff7059632024fc70596321ce7c505963201cff7654e32054fc7654e3201e7e6554e320067d6554e32005ef7254e32055ec7254e3203fcf3254e3219cff7654a320567f6554a320567c6554a32005bf7454a321a5bc7454a32057ac4254a32055dd76cca3203edd76cca3203f9e74cca3203f9d74cca32057ce62cca32057ce52cca32007cd52cca320579e42cca320579c42cca325379f41cca3200cff76586320057f75586321cd7c7558632056f46158632004ff75586320067f75586320047f755863201cfe755863201cfc75586320067c755863201c7c7558632004ff7458632014fe7458632004fd7458632014fc7458632054fc7258632056be4258632056bc4258632006df32586321c6bf41586321c6f63158632056f72158632056f42158632004ff7058632024fc70586321cd7e75982320057d75982321a5be7498232005bd7498232056fb6098232026f86098232056f86058232004ff755823201cfe755823201cfc7558232004ff7458232014fe7458232004fd7458232014fc7458232054fc7258232056be4258232056bc4258232004ff715823200cfe715823200cfc7158232006bf4158232056fb2058232056f8205823201cfe76d95321be7e65d9532006bc64d9532004ff74d9532014fe74d9532004fd74d9532014fc74d95321be7f54d95320067e54d95320067d54d95321be7c54d95321bcfd73d95321be7f53d953203cfd72d95321be7f52d9532006bc42d953200cfe71d9532004fd71d953200cfc71d95321be7f51d95320067e51d95321be7c51d9532006bf41d9532024fe70d9532004fd70d95321be7f50d95321be7c50d95321bd7e76d953201c7e76d95320067f64d95320067e64d95320067d64d95320067c64d95320073c64d95320063c64d95320073c42d95323876f32d95323876c32d95320067e61d95320067c61d95320073f41d95320067f74d95320067e74d95320067d74d95320067c74d95320067f73d95323867e73d95320067d73d95323867c73d95320067f43d95323867e43d95320067d43d95323867c43d9532
  | 40 => 0x8242056bb6098242057b86098242057bb2098242057b82098242055bf7658242005bf75582421f5be75582421f5bc7558242056bf6558242006bd6558242005bf735824226dbc7358242056bf6358242006bd6358242055be7258242055bc7258242056be6258242057ae6258242005bf71582421edbe71582421edbc7158242056bf6158242006bd6158242055bf7058242057bb605824225ebe6058242056bc6058242057b86058242057bb2058242057b8205824203e7f7559732004ff7459732014fe7459732004fd7459732014fc745973203cfc735973203e7e535973203e7c53597321e67f5259732006bc4259732004ff715973200cfe715973200cfc71597320067e51597321e67c5159732006bf4159732004ff7059732024fc70597321e67f5059732006bf7559332006be7559332006bd7559332006bc755933203ebf735933203ebe735933203ebd735933203ebc735933203ebf535933203ebe535933203ebd535933203ebc53593321debf72593321debe7259332006bd72593321debc7259332006bf5259332006bc525933203ebf325933203ebe325933203ebd325933203ebc3259332006bf7159332004bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bc515933203ebf315933203ebe315933203ebd315933203ebc3159332006be2159332006bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006bc505933203ebf305933203ebe305933203ebd305933203ebc3059332006bf1059332006bc10593321bcfd7694b323867f6594b3201e7c6594b32216be6494b32006bd6494b3201cff7654b3203cfc7654b3201e7e6554b320067d6554b32005bf7454b321ddbc7454b32206be6454b32006bd6454b32005df7354b3203ddc7354b3226dbd7690b32056bd7690b321b4bd7690b3226ebf6590b321f6be6590b32006bd6590b3226ebc6590b32056be6390b32055be7290b32057ae7290b32057ae3290b320579c3290b32005bd7190b321eebe6190b321eebc6190b3225ebe6090b32004ff755873201cfe755873201cfc7558732004ff7458732014fe7458732006be7458732014be7458732004fd7458732006bd7458732014fc7458732006be4258732006bc425873203ef77158732006f751587321d6f451587321d6bf415873203ef7315873203ef431587321d6f62158732004ff7058732024fc70587321d6f71058732004ff75583320067f75583320047f755833201cfe755833201cfc75583320067c755833201c7c7558332004ff7458332014fe7458332004fd7458332014fc7458332006be4258332006bc425833203eee325833203eed3258332004ff715833200cfe715833200cfc7158332006bf415833203edf315833203ef
  | 41 => 0x26f9e6394e420079d6394e4226f3f5394e421f79f5394e421f71f5394e4226f9c5394e42055be7294e42005bd7294e42055bc7294e4237ebe6294e42237ae6294e4255f3e5294e4255f3c5294e421edbe7194e42005bd7194e421edbc7194e421f73f5194e4225dbe7094e42005bd7094e421f73c5094e42005bf7654e42055be7654e42005bd7654e42055bc7654e4226dbf7554e421f73e6554e420073d6554e42555bf7354e420079e6354e420079d6354e421f79f5354e4226f3e5354e4226f3c5354e421f79c5354e42005bf7254e42055bc7254e42226be6254e42227ae6254e421f73f5254e42005bf7154e421edbe7154e421edbc7154e4254f3e5154e421f73c5154e42005bf7054e4225dbc7054e421f73f5054e42055bf7654a42546bf7654a4253cbf7654a42055bf7554a420573f6554a420573c6554a42005bf7354a4226dbc7354a421f73f5354a420073d5354a42055bf7254a42056be6254a42057ae6254a421f7af5254a420573e5254a420573c5254a42057ac5254a42005bf7154a421edbe7154a421edbc7154a421f73f5154a42005bf7054a4225dbc7054a421f73c5054a42055bf7658642005bf75586420073f75586420053f75586421f5be75586421f5bc75586420073c75586421f53c7558642056bf6558642006be6558642006bd6558642056bc6558642005bf735864226dbc7358642056bf6358642006be6358642006bd6358642056bc6358642055be7258642055bc7258642056be6258642057ae6258642055bf7158642057b761586421eebe6158642056bc6158642057b46158642057b72158642057b42158642005bf705864225dbc7058642056bf6058642056bc6058642006bf75586420063f7558642006be7558642006bd7558642006bc75586420063c7558642006bf7358642006be7358642006bd7358642006bc7358642006bf5358642006be5358642006bd5358642006bc5358642056be7258642056bc7258642054bc7258642006bf5258642056be5258642006bd5258642056bc5258642056be3258642056bc32586421eebf51586421eebe51586421eebc51586421eebe31586421eebc3158642056bf2158642056b721586421eebe2158642056bc2158642056b42158642006bf7058642006be7058642006bd7058642006bc7058642006bf5058642006bc5058642056bf2058642056bc20586421eebf10586421eebc1058642055bd76982421f5be759824225f3e75982421f53e7598242005bd759824225f3d75982420053d759824225dbc759824226dbe7398242005bd7398242006be6398242056bc6398242055be7298242055bc7298242056be6298242057ae62982421edbe7198242005bd719824225dbc7198242056bf6198242006bd6198242055be7098242056bf6098242057bb609
  | 42 => 0xc6154d525773f4154d522a57c7054d520557f749495256d7d74949520073f64949525673c64949520057d73949523867c63949520557e72949520576e72949520567f629495201f6f62949520573c42949520057d719495220e7e619495220e7c61949525673f41949522a57e709495200cfe76d8552205bc74d8552006bf64d8552006bc64d85521fef661d8552004ff74d8552006bf74d8552014fe74d8552004fd74d8552014fc74d8552006bc74d8552014bc74d855203cfe73d8552004fd73d855201cfd72d8552006bc42d85521fef651d85521febf41d85521fef631d85521fef621d8552024fe70d8552004fd70d85521fef410d8552005bf7458552205bc7458552006bf6458552006bc64585521fef46158552006bf64d8152006bc64d8152004ff74d8152014fe74d8152004fd74d8152014fc74d81520b67f54d81520067d54d815203cfe73d8152004fd73d81520b67f53d81520067d53d81520067e52d81520b67c52d8152006bc42d815200cfe71d8152004fd71d815200cfc71d81520b67f51d8152006bf41d81520b6fa50d81522a67c50d8152205be7498152005bd7498152006bf6498152006bc6498152006fb6098152005bf7458152205bc7458152006bf6458152006bc6458152005df7358152005dc7358152005f771581521fdf47158152006bf6418152006bc6418152026fa6018152006f96018152055bf7659642055bf75596420573f65596421f6be6559642056bc65596420573c65596420563c6559642005bf735964226dbc7359642056bc63596421f73f5359642055be7259642055bd7259642055bc7259642056be6259642057ae62596420573e52596420573c5259642005bf71596421edbe71596421edbc7159642056bf61596421f73f5159642005bf705964225dbc7059642056bf60596421f73c5059642055bd7698e421f5be7598e42005bd7598e4226dbc7598e42056bf6598e42006bd6598e42055be7398e42056bf6398e420579f6398e420569f6398e420579c6398e42055be7298e42055bc7298e42056be6298e42057ae6298e420579e3298e420579c3298e421edbe7198e42005bd7198e421edbc7198e42056bf6198e4225dbe7098e42005bd7098e42056bc6098e42055bf7658e42005bf7558e420073f7558e420053f7558e421f5be7558e421f5bc7558e420073c7558e421f53c7558e42055bf7358e420579f6358e4226ebe6358e42056bc6358e420579c6358e42055be7258e42055bc7258e42056be6258e42057ae6258e420579e3258e420579c3258e42005bf7158e421edbe7158e421edbc7158e42056bf6158e42005bf7058e4225dbc7058e42056bf6058e4226dbf7694e42055be7694e42005bd7694e42055bc7694e42225bd7594e4255f3f6594e4255f3c6594e4226dbe7394e42
  | 43 => 0x4e523867d6394e520075d6394e520065d6394e523876e7294e520057d7294e523876d7294e520056d7294e5201e7e6294e5201f6e6294e5255f3c4294e5220d7e7194e5220d7c7194e525873f4194e520057d7094e522ae7e6094e5200cff765865201d7c7558652056f4615865220f765158652004ff7458652014fe7458652004fd7458652014fc7458652004ff735865203cfc73586520067e53586521467c5358652054fc72586521467f5258652056be4258652056bc425865220e7e515865220ef6515865220e76515865220e7c515865220ebf4158652056f72158652056f42158652004ff7058652024fc70586521467f5058652215be7498252005bd7498252056fb6098252026f86098252056f86058252004ff7458252014fe7458252004fd7458252014fc7458252004ff735825203cfc7358252054fc7258252056be4258252056bc4258252004ff715825200cfe715825200cfc7158252006bf415825208efa5058252056fb2058252056f82058252205be76d9152206be76d9152014be76d91520073f75d91522073c75d91521f73f53d91521f7af52d91521f73c52d91521f7ac52d9152005bd71d9152006be61d9152006bc61d91521f73f51d91521f73c50d91521f6bf75d9152206be75d9152206bd75d9152206bc75d9152006bf73d9152006be73d9152006bd73d9152006bc73d91521f6bf53d91521f6be53d91521f6bd53d91521f6bc53d91521f6bf72d9152206be72d9152206bd72d9152206bc72d91521f6bf52d91521f6be52d9152206bd52d91521f6bc52d9152006bf71d9152006be71d9152006bd71d9152004bd71d9152006bc71d91521f6bf51d91521f6be51d91521f6bd51d91521f6bc51d9152006be31d9152006bc31d9152006be21d9152006bc21d9152006bf70d9152006be70d9152006bd70d9152006bc70d91521f6bf50d91521f6be50d91521f6bd50d91521f6bc50d9152006bf10d9152006bc10d9152006bf64d8d52006bc64d8d52004ff74d8d52014fe74d8d52004fd74d8d52014fc74d8d521cede53d8d521cedd53d8d52006bc42d8d5200cfe71d8d52004fd71d8d5200cfc71d8d52006bf41d8d52024fe70d8d52004fd70d8d52205be7498d52005bd7498d52006bf6498d52006bc6498d52006df6398d521bded7298d521fdf67198d52005f57198d52005bf7458d52205bc7458d52006bf6458d52006bc6458d521e5ef7258d52006bf6418d52006bc6418d5203ede6318d52006dd6318d5203c7c7654d5257d7f7454d5257d7d7454d520073f6454d525773c6454d5201d7f7354d5201f5f7354d520075f6354d5203e7e6354d5203e7c6354d520075c6354d520076f7254d520557c7254d520076c7254d5201e7f6254d5201f6f6254d525773c4254d520057f7154d5221e7e6154d5221e7
  | 44 => 0x4fd7458653014fc745865303cfe735865303cfc7358653166df535865303edc5358653004ff7258653054fc7258653006bc425865303ef7715865322ef6515865322ebf415865322ef64158653006f5415865303ef7315865303ef4315865322ef42158653004ff7058653024fc705865322ef71058653004ff7458253014fe7458253004fd7458253014fc74582530e67f54582530067d545825303cfc735825303e7f535825303e7d5358253004ff7258253054fc72582530e67c5258253006bc4258253004ff715825300cfe715825300cfc71582530e67f5158253006bf415825303efb70582530e6fa50582532ae7c505825303efb305825303ef83058253225be74d8953005bd74d895303cfd75d8953004ff74d8953014fe74d8953006be74d8953014be74d8953004fd74d8953006bd74d8953004bd74d8953014fc74d89531e6ee52d8953006bc42d895300cfe71d8953004fd71d895300cfc71d8953006bf41d8953024fe70d8953004fd70d8953006ef6298953005bf7458953225bc7458953006ed621895303cfd7518953054ff7418953014fe7418953004fd7418953054fc741895352e7e531895352e7c53189530567f5218953056ee521895319eed5218953056bc421895300cfe7118953004fd711895300cfc71189530067e511895319e7c5118953006bf4118953024fe7018953004fd701895319e7f501895300cfe76d855301d7e75d855321ef661d855321f7651d855303cfd75d855303c7d75d8553004ff74d8553014fe74d8553004fd74d8553014fc74d855301cfd73d8553176df53d855358e7e53d855358e7c53d8553176dc53d8553054fe72d8553004fd72d85531767f52d8553006bc42d855321e7e51d855321ef651d855321e7c51d855321ebf41d855321ef631d8553024fe70d8553004fd70d85531767f50d855321ef4615855303cfd75d8153004ff74d8153014fe74d8153004fd74d8153014fc74d8153054fe72d8153004fd72d8153006bc42d815300cfe71d8153004fd71d815300cfc71d8153006bf41d8153116fa50d8153006fb6098153005bf7458153225bc74581532ae7f6518153225be7418153005bd7418153026fa6018153006f96018153056df6398e52056dc6398e52005bf7458e52215bc7458e52056dc6358e52004ff7458e52006bf7458e52004bf7458e52014fe7458e52004fd7458e52014fc7458e52006bc7458e52014bc7458e521bede5358e521bedd5358e523867c5358e52054fc7258e521be7f5258e52056be4258e52056bc4258e52056de3258e52056dc3258e52004ff7158e5200cfe7158e5200cfc7158e520067e5158e521be7c5158e52006bf4158e52004ff7058e52024fc7058e521be7f5058e525867f6494e525867d6494e5201d7e7394e5201f5e7394e523875e639
  | 45 => 0x64000004c00300080010000001000800a00040000018000000400000000080010000001400000000000000001002000500000000000000000800700200000000004000c0010000000000000000000030004009000000000040020000000001400600080010004000000000100180000004003000000100000070000000001000000000000000001000400000080000004000000c000000000100040000000000000c0000000000000c00100040000000000001800100100020000001000c00000080040000000001000e0014000001400000000010000001000800300080010008002000c000000800100000070000012000000100040020000004000000400040000000000000400000000050000000000000200280000000000000c0040000008000400200080000014001001800000000000000002000400100200010008000000000400040020018001000000200100090000000000400700080030000001000000000000000000005000c000000400b000800100040010000002000400200080050000004000c001000000200040000004001000000000000010000004001000700000030004003000000100000010000003000800000000000000001000000000000010008002000400000080020000005000400100080020000000000c0000000001000000000100000014003000c00000000000000002000800100040000008001000802a00280000000000000000400000000000001000000000000000000000000000100000040004003000800000040010004003000400000080000004005000c0050000007000000600040000008003000000000000030000000000000000000000008001001000200040090000007001400000200010004000000c0040014001000800000000030000002001c0000000001001000200000020008000000000000080020000003000000000040040008000000c000000c00000000010018002001000500340040004004000c000000400d0004000000000000000010000001054ff7498a53014fe7498a53004fd7498a53054fc7498a5303cfe7398a53054fc7398a53056ee7298a53056ee5298a531ceed5298a53056bc4298a5303eef3298a53056ec3298a5300cfe7198a53004fd7198a5300cfc7198a53006bf4198a53024fe7098a53004fd7098a53004ff7458a53006bf7458a53004bf7458a53014fe7458a53004fd7458a53014fc7458a53006bc7458a53014bc7458a531be7f5458a530067d5458a5303cfc7358a5303e7f5358a5303e7d5358a5303eef7258a531beee5258a531be7c5258a53006bc4258a5303eef3258a5303eec3258a53004ff7158a5300cfe7158a5300cfc7158a531be7f5158a53006bf4158a53004ff7058a53024fc7058a531be7c5058a53004ff7458653014fe7458653
  | 46 => 0x800100000030000000000c00c0004001000000100000000000006003c0010008001000400000040000004001000c0000000000000800000080050010001000000100040000000001000000000180020008007000400300180010000000000000300000010000002000000000000060004000000400500000000004003000800100080000000000001400000040020000004001c0010000007000c000000400300040020004000000400000040020010002003c0080008007001000300000010000002000400000140010008005000400300000120008000000c0020000001000000000000020004000000000500080030024000000400000140020000002000400000240030000003000c01100040010000000001000000000090014001000c0020000000003000000100020004002000c0030010000000400000000000004000000000000080000004001000800200140030000003000000000080000000000000800100080000024003000000100180040000000000400000040020000004000000300000000004000000400500000030004004001000000000020000004000400100040010028000001800200040000048000000000300040040004001001800c000400000000000004000000400000000000000001000c001000c000000c0010000000000400200000000000000000c000000c0080000001001c003000c0070000002001c001000001100040050000003000c0030014000000000100000070030000000c001000c0040018001000c00000000070004002001000500080010000002000000000000000000006000000a0010000000000000080030004000000000300000010000000000c00000040000000005000000300000050000002000000c001000000200010000002000c001000c000000c00000100000000002000000000000020000000001000400000010004003000800000000000008000000c001000400400040010028002000c00200040000020000000c00000200000000003000800000080000004000000c000000000200000000004003002400000000050000000000000300080010014001000000000080020000006000c002000000000040000004000000c0170008000000c000000000100000010018001001400000000010004001001800f000c000001c001001400100040060000004000000b000400700000000008000000400300040010004001000000000380080000002001400000040000004001000000000000000000002000000100000000000001000800000080040014000002000800000000010000000400000040060004002000c00000180000004000002c0000000000000000000000000000001000000000100000004001000c0000014000000000100040050008000000400200100040000004
  | 47 => 0xc006001000000040030010001000000400140030008000000c0040018000000000700000080008000000000000040010004001000400a00040000008006000000100000000008000000c0020014000000400200000000004001000c00700000010004002000000a0008003000000300040010004001002800200080010014002000000700080040000000000c005000c006000800200000010008000000c0020004004000400000000000000001000400200140010000000002800000380020000001002000100080000000005000400000200060000007000000000140040000000000000b001c00000040050004010000400000000000014000000400000080010000000000000000000000010006003c0090000001001c0000000006001800000000010010000000000600000020008000000c002003c00500000000000000000c004004c00100040010008001000400200040040024002000400600000030000001001c0000000001000000300000070018001000000000040000004006000800000000010000000000400000080010000000000000e0004000000c000000800100000000008005000000500000030000006001c001002800000000000000001000000300200120014002001000a000000800080040008000004c002000c00000140000010000000c0000000000000800300000000008001000400000000030008000000c002000000700040000004000000c001000000000000000000003000000100000050000000000000200040000000000000000200080070000005000400500000000010000003800000040040000000000000200000030004001000000000040010004000000000300000010000000000000000080000004001000000100000040000000004000000000010004000000000300080000008000000800000180040000000000000500000000010006000000700000020008000000c0010000001000400000140000014002000800100000010000001000c0000000000000400100000020018000000000000040050034002001000300180000000006000c0010000000000400400080010000000000000a00100060000001001c0090014004000000100180010000001002c001001400000040040000004000000000000020000002001400200000010004000002000000000000004000001c0010024007002c00000040000008000000400000000000000000000000100080000034001000400100000020000001000800100040000000000000400100300000000002000c0000000002000000000040000008000000000100000010004000000000000040040000003001800300000000008005004c000000800000080040018000000000000000000000002001c0070000000001800400000040008000000
  | 48 => 0x14000001400500000010000002000000700000000000002000000000000060000000002400400000000004000000000100000000008002000000200080000008005000000000180000014011001000000000070004001000800100000030000003000c001003c00000100040004005000800a000c000000000000180000000001000000000040000004000000400400000020004000001000200080020000001000800000180020008001000800f0010001003000300180000008001001c000000000000000020000000000000400080000004005000000300000000008000000c00400000000004000000400100180000000004001c00200040020004000000000a00000020000003001c0040008000000000400040030000000000000600000000000000001000100080020000000000c002000000300040000008001000000400040000008000000c001000400000000040008001000c00200240030000000000c00000040000000000001c001000c00000000000008000000000200000160004001000000400140030000000000400100100000000005000800000080010018001000000000140000008003000400000080000000000000000000000000004004000c00100000000000003000400100000060004000002800000200000004001000800700000010008000000c0010000008000c00600000010010000000000100080020004002000000300040000008001000c000000000200080030000001000c00100240000000005000000000040040000005000400a0004000000000200080000000006001c003000000500040000004005002000100040030000001002c00c0000000000000c0004002000c000001401000040020000002000c0010000001000400300080000004009000c0020000001000000c0014000000c0000000000000000a0004000000800000000000000005000c002001400000000000000000000800000040070000000000400100080040004000000000e0004001001800000080000000000000c00400240030008001000c0000004000000000600140020000003000000100040000008000001800a000000100100010000002000c00800000000014000000c000000000a000c002000c0000038000000000100040030004000000001800000040000000000000000040040004002000000100180000004003000400600100020028000000c001001000900100040000001000000100000000000001000400000000020000000000c004001400000000010010000000c001000c003000000000100020008003000c0060000000000c000002c000000c0000000004000000200000010004002002c000000c00300100000000000000000000040000000000001c001000c0040000002000000100000020014002000c00
  | 49 => 0x8c180000001a260000000000000000030b6000166e00026060000000000134e000267200009f800000003ae80000002ba600000004e9000028d80000001a8a0f50000000000000017300952388000000000037047d323b800030fc6a71f8600000000000ad06940000000364600012e400000000000000ef7b932eb3b33e0000000000278a00000000001fa0761800057b8a4e4ad948848aad5689380000ea88500001abed5b8000000261e04104846ac800073222040000000def9392000394e000337a00006cacc7b80e4720000cf08040c0100000001f6c0001d8c000000000000005c9b868acf96de0000000501000000004d0000227000000000000000c45a2c00000000000000065f0f0aec600006381a346bf00001478000505979439e9d1c0fb957c74a9172016b79400000000000000218a006e431aa40002c4a00014f000014c290e800000000010004000001000000100000004001000000900000070004002003c00000080050000000000000000000020034001000000100000040014000000000000000070004001000c001000000000000010008001001000000040020004003000400100080030000003000800000040100000002000c0000010002000800000000030000000000c001001c000000000000000040000001000000100000000000000000400100040000018000000000600080030004003000c00000000010000000000c00b0008002000000000040010000000000c00000080000008001000000300040040004002001400d00100020004000000c0000000000000800100200040000000000c0030004007000800300000000000005001400400040010008002000c0020004000000000000140000000004001c00900000000000001000000300080050004003000400100040070008005002c00000000040000005000000100200040000000002c0030004003001c000000400100180040000006001400000000000000001000000200180070000005000c0000000014002400000000030000001000c00100040010000000000c005001000c00200020000000000000100000040000003001000300000000000000000400400080000000001000400200000050008003000000500100000008001000000100000010008002000c0000004005000c000000c007000400200080000000000000000000040020004002000c0030004000003c001000400000200010004000000800000040030010001000c004000800000040020010001000000800000040008005000000200480040010002000000000100000048005000000200040060004006001400000140000008001001c0070004003000400200000040010002000c015000800000000020014000001000200000000010002000800000000060000000000000000
  | 50 => 0x2dce0000000000106a0000000c5ea30cb6e031e0000000a1192de0001cdc4398000b7826cc0000dd00000000000000000000000000000000000065db1b81d68000005000051c0000a658000000000000000000000000cc72360000097400017245ac0df8de2a900d2a089660e800000008c800038bc3fb09eae6e21209c50000c35b358c5980000000000000000000015d6c898000a238000000184a00031420002a580001bf4a32908cef40000000059cc388000000149a00000004b4accc2ac19e2dedb756000000000000000000000000000042d1f60240800000000002e4879a0001fe209c800083c10d068eb6d44cf800000000001438eb40000000000000038880000002ca00000000000336200023529848000000000073b8936f02800000013c60000000000000000000003528dcc673a0b8cda8000b060000e4f0000428a700a42000057127f200000005b50000000000000003e000037140000000000259800014a40b2a2feed22a9872200000000000000000016b8d3400033e600000000000000b2880000000f7a00000000000000bf980000000000000016ce379cf62128000000000000000009ae9c240000000000000000015986410000c2f800000037b832580000000000000000000000006df000000002ec000000000000000000000c280000000098683f2c4c13d378c5708000000000000023b60000000000000000024c86ac000000000000000fca8d92472000000000014aa000150a000296e0001164000064c000000007900005ce11ba0000e44000262400000007c33b649b724ea53b13d0b742ecc0000000ab780000000000000280e00023c68718f82000000000000009e631ee000000000019320f628349ec8b86e4b14e0000000000000006fba210559083e00000f09a4b2c07dc39c0943112c00016a000022e4ca78000000000000034fa1ea864a81a34f00002e928c938c63a31f3443500000001594e5a800080a0f946ec20907bf14a20003af60002caa0001b6adee88e6000223eb6680005da99300001b543d932e685c27c0dc6091c70eabc01f3a0a800028fe000038cbb61444000341caf62a5ead2000062198120001ed40000172000219e3d08000afd103c5deb83400000009800000000000000000000c03ae84caa686000000000020244d600000000000e8236ba680b008c68800000000000000000000000000000000000be0cb4bb100000000914a9640000000c0f800000000000003454158196a8bc8000000000010000000000000000097e0000000000000001e000000018985c60000000000000012120002f160001e3618d11240000cd4000000000000000000000000006a5a480000000c3a000000000017be00000007c4800000010fe00036f20eb8000b8d9e1e0468000000000000000
  | 51 => 0x9329146c26000016400701cda3962770bd0032299c703350ad86a55a0000000d70af3c5db08be0000000000000000000001d70000e0633560000000e26b12807880004852494a5825fc00000003e80000a7722aad23afd00000000000341a0000000000000000000000003476000000000000000000784000365825580006d8a8625520a0043e0000000000000000000002c7c0000000000000093f3aca7a920f42b32cf80000cd62fb08080000000c2280001d9056c27bae7e00000008b808484f58000d7d00009120000a1780000000e020000df400000003da0e480001ba000012d8b7d80001ddb0f26bb1916bfe00006662a4244300000000000b17386e0582c8837680000000e36c10000000039c6000000000000003c70000653800000022ca98200009eba4cc346800000038ea2bc809cb3d952e0003b26ccdac7a06532de3a7ab7e30117a867611d4000000010e183074a0000b1b00000000000000000063100000000000000318ce29123a58b00000000000e598000000104800000008168000dd311303af000060600000000000b48aece895000000032100000696e14058c0000000e6c0000b2a3aee95488a4ab028ba0e80000f08b2947559f428ec217a7a30d14000379cbcb2dfe8de8000aa1800049f800049680006228c322bb80008eb800000028f6000004c4d697b6c23b020ae2a37015d2fb2a2c381c0083464e9d000000000000002c58000000000000005cda52a00000000000000669a43e50f2084b110000c5880004a2835200000000000fbc000000075600000000000d3d000000015f40002512d4d93f499b800000010e256f3746b21b2006b431da138800025c8fee0370528e2980000002000f0e192c0000000000213400023144d3000000001ac0000000000000021e00006f495a2d35800000039de00000000000a7aa3407b471600006550000eef00000000000469232e8da139400035606f93adc57716ca0000000a709136edca59ad6d09bc59e9eae00019ca00000004c7a772de380000000000e18a4c2695914076f070e0003556000085c00033860000000bf480000000000000146c2118f0cbde1d146f6000000015060001534000000000009d2bc4000045e0b3c97d80005b98abca66800000000006918000c1d922c000000088e96488ea8c70c731c00000142c00000005d700002c680000000968370363e000000000000001a1b3c6000000000029c066100000000000000000000022460000000000158a0002482000000000000000db8000345800079d80000003aa28563a76cad1bba389239a00030a8318aba40d1ab3a00008f47e89d36e3b9a860000a220000000000000000031c0d10000000000008cc8000adc800000008b20002f92000295a2e500000003606190800000000000
  | 52 => 0x1a4e0000000ec8800000000000000000f07a708e722cf296204540000000c830000dba8e7c0001eee00013a600000000003530000000000000007573938576b92200036d61612d16d64000091b201cca6202c00d02520000f7c00038103122a34000032a0002ca674e21ce0773b6c938943eac2b9ee56384ea8031f2e3e3b1b2000290e21c22b41f0a8e0af8a1b2e642756b038080b119a140000efa00000000702bc42ac9e7400033e80000000000000000000240000c7e02d88c6294aac80002c9a000000000000009fc3610431917c445a6c8000128e0003424586b0d06b0284c10a80005b02f046ea37f229f1ec69210000e6325e01dc2546c558000000000049e000000000009f1000082311840000f4841bb2fc7a58c7a00000000000000000166800000000000000000000000000004c51dfe0000000ec006ba0002dd603b80000000000dc0bb800000626a1b80005eeacda00000008fb2a2acfd80000000000000000000000000002cfc0000000845319aa120d829298000073800000033c0000365e0000156093800000000000000000000000000000005cca5eeeb080005568000910388ab2f80002370000965b28e2cfac708f3000000022f8e898000d1191be00017d00cc00006b88000e8d00007f5800000000002820000a4d00000001236739800000016100000d2c4ed000043217d20000000000000012e310a00022ac99c219410b096c7b39d7e002b39216796a800000000002ba0000000000000000001a1e000000000035cca14926e0003bfee5c8000ab4000000000000001d629ca8e1681500a20000000b7c28720000000cc0b72600030ae036058a2c2269c44024280001b3a1ac10f086d000000000000000000c0b00000000000d55206c000000000000007d2a4e6cda33a200024e800003540000000000000000000008df1016bf7b83aa94b97e6e93400c34a21854f3b5cc8aac2a6eb8fc85201b0e76797529baa4188b9ad524658516975800000030fedca80009840000000162ec56250a7ffb7300c68000ee500000002ce60001bce600ac140edaa2c0000caa1fb996e0000000d68b002e0917fecf2b00e455a3e840136603200bf20000000000000095b8000ced003c0688162620b73c0000000f0680000002fae2a9a5b80001fda00000003c204ee00001f8000000087c0e200003bba0000000000000000000000000a7eb7c8000629144e5b580000003ba228b80000000000a4f029a00000000002fbc0003a1ca31b708c9b000000000000000d22adc00001d40000d7c80000000000cb400000000000b47178201c800000000006859c02000265c3d780009aa995000019fa50c02e6af9800015da9f41ac800058aa9b80002fd40003716365800081598629a2837a0000c8a64680000000000b8b00000000
  | 53 => 0xb6e0e6a980e4b094b84cb38ac3f9382a1f508981240cf000004c290dad965f61d7034c800081bb87818380005d11a485a2b6b200014ca00000000000000000234c46a203ad9c8000000000000008d0000000000000000000000000000000000000600d5c000236c5728000000000043687ec00021a425da04653f800035a0000000000000009d0000073e09d0000a0e8398000000052500000000000298000081faec0c9aa98e0001dae000000000003941551a6200000000000000c6706eccfe9464ec38b22b5700001968d8400000005f689fcd2e9e86cdf33720000000000000000000000000000d37000000014f20000000000000000000000000000493800000000000000cc8000000098500000000f36e360000000156eb620000cf380008368000000000000012e65482212d670326000000002480000003724a6102da0000000830330c0003252000000074b800000016b20001c4c60f39027bb00003c5000000009940000000000194400030b2d2900000001cf20001a7e20500000000762079800000000000000000b0280005e91baa000000058c800000002f83598b6c0000000000000090919e6b3500000000000a76800067fb856a8500000000fa6000000000000000000000000000039a8390ba7000000000006bd0000ba580000001b0400000000000000da8aab4000246a8668000c2e000000000009da1ff200010a6082b4c24de8000000139a0000000d33abda0670000b8b8000000351800035c4000000000000002600000270000000037503d98eea34a3aae07300002d2000099480001cb807670fb72200015240c08000000000000020520000000000000000015fc0000000000000042280000000000000161c017000000026a812b8b626d0800014980002582d18aab2f760000000826316c8df800000000003932fb028c0000989a75ecfb8000d0b0d088a9b6687350000b62af9800000000000000b3d00000003c480001c9e1c1082a0000e7200000000000000000035e59a80003811c1842100000000000000000085c8000c4780003908b5a000000000034b6000185e0000000e0505b612a3374a0a8608eb90f188f6869800011a0d6480002bb00000000000b258000f14303600000003ca0b522268d48eb400380000000e11baeada235f6674a4d8000000000000000003676000000000000000819dfca370dc6000179c0120000ed60000118b9960000000b73155434e2e7663c00000001fe6000000000000000001562000000092b8000000000000000000000000000199000000008e180001a40000000000000000000000000000000000000000000c5800027fa0000000000000088298b60000000000000032f80000000000b361d8085001c80000000000258e6f98000c63a87c2ef98543ed01de0000000a5b0000
  | 54 => 0x2c0cc9027eaac1800000028420001c304a90000ac49e920001810d5600000003906000057294dad0e00009100002f4800000004d785b80df938451e800000004126490692b9e321e96b00000000cba3ed8e90000000000003de000000000015a6000345098b800000000003e400000000000000000000003c6a551a7027d9414bfb07927f030ecce80fb82ff989c000000070200001db3af8ed997f600c00000000ea60000000deb8000931800000000000003b344df98d205000003100b6605f8c422e628d6eeaab9400000007c680000000000e8386a440c80000003ade00009408bb8000d010bfc00000006280000d123472000000000028880000000c0891620000644000176e2bfb7d2000233646e324c8b425bee668d5800a8e9a0002752cd806fe2cc800000023d062b8000000000000000000000a58ead0000000116a1598000000126c64b8000a4e8000a761f9c48400f66c1ac001771e825e1000000034d852109d863400000003734769185ab3280000002044000000018300000000000bf58000dea0000c258000960007e7830c94000393600022a40ab80009d0000000000009bd0000d618000b2628ce0002dae19dbb90919af2a58380000000000e2aa4160001b9c6a997684f28000a91800000000002dc000000036ceb82a5d481080001791eac5f18a821428000a9287742953a6ea728e340000000764800054521480000000000000000020860ea0000000211e00000002899ca80000000c8814f888aa6c6b6080000000cf4027b0c682c053e21f28ee35d2a5ce110000000000000000000000000be8000000000000000000000367c0002c022b71ea2000253e2bea4742a2ace400000000002c9e000000000000001b9849600000005be800000000000000f9c1b6800018e80000001e6a00035a600033a83e92ace42a9292000385ad77bb46000000000000002738000b4e000014c03a6000271a9db00004aba95e09d9b384fe83b400017a076e800000000005240000e011ef6a3a0000b8e092c3698000000128800000000000000000301200000009153324cbb800000002ee000364425b8000eac000000000006561884000136200036d2b98873200000000000420d228548726000000003e80000000581800000024620000000e1d2d8400036f00000000f0e80000000000682b1a8000170eb868ef000025fe9580000d0e000000000000000000c1c80000000aae0000000000000000000009871a06a46324a0000000ad9800073a000095300003b58000000002e00000002cd8000000000000003c0000091ad0f12300001b6cd7580007d8a77a000141ae4816a6000165a000000000015d879b9b80000307a37b96260000000b8929fe2be03e60000cc6000000000000000d802600000000000000000000002a19bcae82
  | 55 => 0xca1a71cd4b28363dcbc1200000008d100000000000e44800000000000002f000000000000000000024ee37c8000968800034980005a1af440000000000000073a8000e9a1fb247119a4395a31600000000000000000000000000005e41a38d30257c2d311d600026d800013ceaf480426388f50000323e00000000002baa0000000000000000000000000000959012ef0a8000000227eb2b94320268000a4c8000000000000000003220000b448000407000000000000000000000000000000007af9da000000001538000000163a6c280004fc8edc000190c10b894454598160001dde8ec98f835bb41e0000000c4b00003760000aaf11e80000000a28291c275ae3a9338ad6bc704d2a57344e00004fc8d60000000000000009060000000e77000000037802f213fc0000000d09904e00024da0001ec8000000000028fc1a000000000000000000087e00002679f7477a00000000000d9c1e04d6fb27e3e614da2afb8ba00014a80000000000268c0000000d950000ebf2f32123a40a8381cfae0bb0860003982da580000000ac217a8000983999c000000000039041f5b96e5633204cff111e2ef0ec6964395aaa9931c28495ba0ee0d3a1e42d3c000301cf0c046600021f20000000e9080aa3ab800000020c245d9046633197ab910f4c09129a0000000049d80007ed80000000000b313470000000000000000000000ab5800000018b4df5ba04d8a8b42ade800000000001c28000000000000000000002e489cc910a4709f8c1750000808000000036fc59c0280000000084617bcdeb12323d69a72861a6eea0032182dd9c546ef310c03e9d1e3a000000002aba44c80000001c86ab30000f1491bcdfe0000000000000000005230000ea500001d9b3e02ba95a000030a600000007c212580000000000000000001502b880002fb95823338dbc0000aca0000108c98080e0000000a539e2a5a2000000000000000000000217e9e900000000000377800000000f4000000000010680000000c6f027a99b33d4b4280c24888000e9000001e0a72e000229800000000000000000000000000000001a040001e9adfa90a89de0af0accab44bea800012c80000000000000000000026d4000000000032801430000e1f23187a825e86a58ba848734a6ae6238c90cb7b218e2c040000000000000000009e4c200c109c331c8c8e8270b4082ce870854c7d20000748288c00000000001a2ce6c8000000373a0002ea6000000000000000000000d1a8000000366668fba1206200000002b3c0000000000000000017d600000006d18000e3100000a28000c61815c00026588dd936e26400000001fe082385621dc800089f05e067c80000000000000000000015ec00028c86c91c44de780006f71becc040c1679b1e02415b8360001776048800
  | 56 => 0x98000000000000005718bba8f9821a00000000000000c8f0000a3e2af6a9911b4624adec000000000000002d7800000000001649f04cfc80004223bd20000000000000000000000000000668130200002bc0000000000000000000000000000000317cdd8192800000000000000000000000026f8000199200000007f600004091c68256041a000373600000000000000cdf8000000224400000000001cbed4fba7061d8000df616340000a9800000006870f02ad8161403a181a29b80005a70000b7600000001350000000026a000000000000002fdc0000000be6800094880000000000000000000000000000000aef1e4243814622b10120d570000000000000000006ad0730ba62570ef18734000192abbfac6a3b3ac20ba814ac00028e2e2200000000000000000000000000002ab60000000a05b6d08f7979a3f98c380001bc6497000000037f600000000002dc00000000534334c0000000311281c00000000000000000000020180000001f84000174670d000012aa9ec82d00001d294260000000000000025c00000001a2000000000000000000000000018449868000000000000000000000000000061a000000000000000003b82000000000011cccf735d800000002d112d01358000000306c0000f8a6e1329c0000000000310e0000000000000000000000000000ad000003b90000000022000026c0000000000000000000000000000000008d2000000000000005620000ad4379a4250c8eb31b8d05738000d4a00005c5800004a00004810000000363c00020e420c9ab60000000000000033a000063c80009e8000000000004b18000a8f000000000000000000a89b42e379b1fa8268a8400000000000000bb280000000a34000000032f19ea54080007af2490e1f800000003fc19a220c0002252000136a307145a000068c35d954e00000005bf00008229fb0c74000000000000000000000371ce10210c00000540001f5400021aa0000000000000059b167e9d90000ea1800000014e400000000003a6445c00000000000000251e00008ac00035080000000000000000000000000000000000000035b2c8923a800010ded2c000000000000000000e20000000000003b02e7400000000000000d390e76cdb289c1849712bc6af7a2b1bc58b6c00000002d2000029b463d8a2800000000000000000000c0002c380000b1c000337600027ec707800000037986d80000000303400000007950000000000000023ee30d141000000008ce3a14e0c0faa00009ecee7258ce531f1e0002ee4000302638531b67aa298c0001a920000000ec1000000000000002e000000000a8ca0580002146000000000000005f2000000008c444180009a5948ad5100000000396000334000036dadc322cc22c00008a18000398160c8a8320eb34800000
  | 57 => 0x52800083a97e8be300000000000264b6cc96ca6b69402774d970000cbd0000000259497080008e0a2780000000900000000031080001110000000000038dc62690a0000294c000000001480007f3000000000000003242000000065f800000020fa000288200025da90700007740000000049ce3c800000000000002136d57971c0000000000225600000000000000000000015e10cc0000000000315200000007e5101a4cd800093037ded3d8000a61b4949ff8bf0000212e00000002f1000000019c4329881ced000008b080000003a7e0e10e0c7c39fa689d0dca8120000000034ceee000000034cc0000ae000005e6c7080000000000000000000000000000f2a26f8000000000097e1d940001a60d3e0fbe1232c68a66000000000e000000005b18a88714ade2147397800023fc5c7bb548a58000000017695e00007a4000004732f64db0000ca1000071d8000000000094200006cc800000000000000000000000000000000000000d781560000394ab2f28fa1fab364c3800005fe338200000000001da2b9600000d1115200029c442b254ae0f070200027dc0001daa00028cc9830e6e009a0ec00017f0d6080009dd8000000011420d8f58897036c0001d5242400002f3a0ace5a12f0000140e00018a21fa00008c293562a7207c00031e26d2800000006dc7980ff66d3250237395082f930c2000000025e92605e593768a5006c0001bd000006ac36e000000000000003c1c0002b8ce210f208750000ebe9bda00019a89fe000000034844650000e4a85ba7de13d2a74000000027460003a78c95baf054d80000610000617000078d23c09eb02e8bdc80008d883f0513365000020a05648000000162413d9c5a4978000ae695d20000000000000000013c80000368e70800000000002410000a7e89d4e128c5a795862800000000001e3af16a7969c880000000000e7c80008d000000000000000000000021e40000000000000000027a600000000000000af5800000038e200000000000000000000000000006cc164e17f00000000000b9aa268bb68fd60000000a4a8bc200000003a480000003092000000000000001b000009a402fe880800034b915abad000080f3a6637e92b2024034e85d06a239709aed2f0fb000000007eb80000000000000000000000004ea00008559b440000000000360edf080006dc80000001d04000000000000000000000000000017b80000001538b2b00000000000a9a000000030f800008860002b96dc4b1300000c928ad959644f9cbc85b000000000007b680000000748de20000bba29ce00017a2000000000031e44ff800000000000000ff80000000f128cfc0003264a5d00000000000bb131e62d73514a2026b8303000000029300002786000130c7280c767940e0086d81aa000000067db7b400031
  | 58 => 0x61cb8601c8a2005c699d696f35da15f00000002574000000000000000000d200a400004910000eb580000000000a5e8000000182676e000092f00000003234000000018b3300878b222a4b092686580000000000b6aaff000000000002e8e00003720003bdc1a704980000000c6400000000088000279a000000000000000002d36000000000000002f680006c22032000000000000002a4bc360001b1c724b0627d1800000025a4cbb19d403c800073580000001e140000000000213e000052291196eccac8000199b93ee9b00000000000c1a8000d8b0000974a414b8aba9cd278928000147e2e38000a2596d29bf952800022a800011686fe0000dafb366765ba24b5f000095611ea00012001ec8000d400000a08800000000007da0448000325000029400a1800000000009ea0000307ae9400021faddc9e4a00025ec00000000001e5a0003abecc4031027a00000000000000000000000003b89dee9cfb8be000264adf73b1a855000000000000000000328800048a000000000006cdbac85e2316a0dd000026e000000000000000000000000079112a8bae0000000000000000000000000c4ab08cae4019a0002c5600006c20d8ac94000386600005f80000000000000002800000000000c151fea3b08a3c000000000000009d800002ae088c0001c7454f80006da0ff40000000b5c80005e280000001b0ce8a80000002792ca481c65958c0ea598000ad315ae0000000778000014c8000137000001eb4c6b508000000000000000000000000000000000019d000030c4872800000000005c200007e780000f238228e888429392cb80000000b0c999a00000000000f4ac4180000002b7cdf6a13aee58914b0b0000000000012011dc0000000000391c0000be2ac50000000000000000000000000c7f80000000000ba02328874003a0000c685a60e6860fa24c44980000000000a0900000000000000000023600000000000000073c7ad0000eb11cd800000000003a5c533bb869fd3418c5d2c5a0001f06000000000038b60000000000020ecbe994200000009b6b1ec0001eba00000009f4021400000000002f66d40ba8804f00000000000000068e2fe19061e7b8c859f2f884c211da000000000005240002860c1584be00018e41330000caf800062580000000000f02004ee8e0000000207a00000000002f5c00021c487002280003bd6000167630f8000000145c00012389889576ba7b5c055605ac00002c800007109540000bdc27c800019dc0002a360002a6e0002ee600032e400000009af80000000000000144261e8000f17241e416000000000000000d52000039c97700000001590181800000026caedd00000001f7c7ca8000000000000000000000000cc58000a650000d2cb4aa6498278a88ac7e0000000000292484cb5d41
  | 59 => 0xa027feac527ce8000de880000fd014a3b68aa0ed3b54ca878966d798000000000010380007ed12f80000000110a84e8ac39d45c2b0a400000000000544000365a0001e1071f000000000006ab000002b000000000000000e3cd528000000000000000004778b2e00004240000a6a0000000000327800023d6000000000028f4686283006597b045e9d500000a2cb93800064e8fba0000000000041e7b6000000000008ba00000000000262800000024ec000095c8768a44aa8399c4ec800000000000000000000000000007f600000006fc000000000000000000b8780000000000000000000033b000000000000000000206a96480000000000000000000000003c9081800000000001c6a7b90000000000000000005eb39e40002c34000177eabd00000000000557000089980005578502c920000632b778b909ca61811a901101f1600011c0aa20ecae398fcc1f11ee04eaac8c000140c00018a820900008599e0800000000000000000000000000000000ea4288000000000002338ede0000f5400027280000000a85b5f88142e88afe3b3a55c9aea2163a3685380000000fe269780000001700000218200008ece800000000151cbd78000000000000000000002ec61f30000d1a2bce7c60000e4b80000000ba42e203d200025320d40284a248000000000000014020000000000000000000003b4000000000006c80000d67a64c00000006ae933c0003ba80000fe88360c7823f1a2488a3bb02c11ef4c27a506000000000036220001b7e820000060936e23592e088c8895e88d85ec0000000d9b2492d3b25fa546800000000007a786d416a0000a6c0b24000000000000005d60000a49800000000009bb00002aab68669d84221e820040000000000000000037e892d000000000000000a161e9a102a0e000058800000000000000000000000005de2c8a00039509e40000b5e9b8e00000008311b2e86b04721c99dcc3050000829af60b71a3c80000d9cd90b1600001604ea000006969326ec704888992fb4384000060d97ae000000000014580000000000000006d11f4000246000026304a6ad3400000000000000da7ad4e000325a00000008248000757800096a8000000218e00000460000000de480000000000000000000000000000000000000000031c6000000000000000000000000183400024a21ff00d0b8391f27018000d3b80000002b1c000000000007947cf00005078000000000000001fc000000031c9db46723b1622080000c829a8d24000016980000000292cebb7e2e1aa8945322d8048901340c5000400011a600003da000340e00000000000000cbe0000b528682d848000000000062e0000abc0e1c1861d4a372000000000000000000000000010600008a2000016ca53c00000000001c1caec88284b805f213b0
  | 60 => 0x1bb8c9a017038200000440fde000000000000000000000000303863506000ec1cfc000205c000142000000008a3a53a0000000a848000000013e8578000cee8b460000000b57800000012800000000000216400004600ef00005a100000001ca400000000000000128b7a4000000000000000001b16a9d29c67c925188960000b5a33d60000000000318200000006e52f080000000000300073400009af0d1c9e734304e4000000000000002ee000036e400037fe58286e000000000001c10bfd988e599886052b8000000000000032e289d9c4600029f894980000000000353800000000007068000afc00000a8905e83f800000000008a43ad400002f6cea80004180000a8eb178b67ae5eaba1b7658f8ed4615a2320000000916ae5400000007318000a988000142200a0003b600002fa400006bc88800de0001a300003832b5e00000001c4200029e4000244c000012cd05000045d1d7a47fa7fcbc9bb781e70000a6f80000000000000000000015e000000000000000c75ab28a518c080efb9cebf80000000000000000003cf80009c42d4000000000000d12000000000000000002b42baa9878b71244214f20b200000000000000000109a00016a200019f800019e02ae918800000000002648b07000000013662998d6c00000007d496a434c2ac400000001ea1afa00000000001192efa80000fa8b4aba1800000000000000000000000019f0000e151a66498800000000000000000d4780000000000000000000019be000000000030ba0b6000000039000000000b7e370000018147212e3061a217695f83ba000000031400b2000215a4521252e76a016a368000f0800000001f4e00023a6168ba9ace006d8c3917dc0000000ea7a56600039800000000b04000000000000000000d62000000010d8000202232da138042a3f026083fad0580007be00000001e7a00021e6000000000024fa00000000002dde5142a8c0000000e3f000000000002c800002f9ac8e00020400000000000000022ab74a0000000eb99abc000307400035e4d438b0cea910c4d9d230400012400001d8800000000002668d5f861e1be0b740002392e7a80000000378319231aad5800000007c000032d600000003c4000000000000000000d2309f2abf8fd89f92ef60001ba69dc00009b8b4e80000000822000000015f8a44b290000000082b8198c8a36e662f8c2864e22168bc00000002b300cf1f1431b0cc000000000000000000163800013ec82a83a400014820000000000000060c9cde00000000b79b3e8d580000000000000272400021beb3fa48abfb94e600000000000916000057040080000001b78579000000000000000000c6519fc00000000000f06281974800015c0000368ca91000001a13ded6b297c70f0a5a529800000000000000000ece2a2e
  | 61 => 0xb17b40800012ecbef800000000000000000000370a00000006b200000000c9c0000000000000000000000001d0600025860000000d728000000000022e0000a3b2d9000000000000000000000000000000000000b8700000dd8000b4980000000000c1980000001c120001fdcb99af2e76a05cc2d5323888b80000001fbe061800000000001b4800012d000000000000000000000058e0000ab60000a76453000095536182721aaa229944800000005ba0000000077c58605423d1a7881722f6a00007a413036b66e200000001d680000000000318869100000001f386c03402000000000033d24d73ba6d1bab0269520304e78000290049a9d52ea20001d18000000000000001440000a68ada6e939d4e0000cfa00035ae0001b58eaeb2b673133bc000236a00000000001fa80001d9cbc30e8e5118000ed78000437062ad8900009ee00003198000000000064f80005218000938328c0209bb2aea38480003a58aba800087b10ce00000000003b680002ffac3d1ec057c150043f357a000000000039f6000300c2490e2600000009d686d00002adc000329a000147c00004bae5c1158490984e00030a270a000000014d63710e3000000005d790620001c32793b522b8f800086890c00001d080519ada03e00000002a9663a8c0662a8000c69974061b238e017a63c19380000000f045d90e5800000000000de0758000000025560801344000000000006ce000000000037ee00000002de8000000000000026de8eb0b4e00039583daa2cec998f008a8a3dca7aa1cc381aa0e48ba5ea000368e0001e8e00000000002ce200017b800000000001128000000048f0cda00035aad81124c000000000016ce21f8000000232a44f00000003ac6d4580006278000000000000028d800000000000000000000000000000001e9868a3984c53ab180000ad87502034bcdb05e000034800031ea0000000a299d6e00000000000e2c02593e80002a4c0000000000000052c800000000000002f28a80978c00000000b30c82909800000000000000000399a9e0550aeece919d743be2a40000230e0001bf662b00000000000c500000000000000000002df8000de1000021500001a800001768de20000000b1e357600005d20002e020000000000000000020f2000000036606f4ab093acb588000bee83f800023bc0000d72000000066e8c600000000b9297860002afc0001acc0000000000000000000009d88000000012ac8080000001f96e6b8000000000056a0a68000000000024b0000000000000000000000000000000000005440000c25195a0003584db78000cb82d8c362b04400019ae287184604780000ad0066000000000001a00002f64cf60000ddf8000d8da86a7a12d0caa080007a00000000204e000000083b80000000000a6231ac3e68000596
  | 62 => 0xcb8b412c2c84000000000004760000ebe00025402b39770282800028f8d8619c000000000000001aae00000000000988000000090480000002ac6974263a00022b2ce5388ebb500001700000224800000031320003164188000023c00000000000000302823680000001f7e07439acef537f4c6f80000002d54446000075a8000000045c00000002ba06f0a2e36f400018520000000aa7a0968baa4b65238dd251536c20000932000000000000000003664a8400000000000000000072d286c000034a00880009f78000ba2939c945800000036480000000000074e4e0000000020d0000000000000002922ad2d7480006a3b9e03c980000001f263e31aa01f72ab000008a0095a2ae6732548d9b800035680000000000c82aaec0000000d54000080d800094916e00001b4e6ef80000b50aa800000006b929b600013040003bbe00000000002dd4661b57c8bd8000000000000013820000f8470280000000000000000000000000001bc80000000000000006f8d9a00000003929f3e0002104630800037a2dd2000071210a2e4c1362038d1806eeaf93c165518c2686137c6ef1088a09081260000000000129c000000000000000002b9e00000000000000330800054b0654b68b54800000000000000bf1800057a2f3a0001fd0000000000000000000000c5280004b580000002676e72800033f80003dc27840001d7cc35155695b00006d9044c0000000332a87034296086d6856a0000000482a828aaf9fc40000c2200000000000000000159ae43800089000000002a1c0000000000295800000001c81ed0caf2bb6000000039f9ede800a90ce0f80002359dec0003a603952280ad6b40c00039481d12aa40000a3888200000002d1e0000798bd0275cdbb000000002b2840338a000035ca52988866daeea38e800017100000000000f0400001b300000000000000000049c8000000010000008028ae80009d6114400014f62942da09f580000000d1e089800069700000001a6a709ba16000000000013340002694d1880000000fdc65300000000000000000047d80000000000e50a4f8b1c80000000000cd1800000000000002720e4a1bac1d1800000019480000a329d98bb2e058dfe3bcad2eecc95b80000000000000000000000001a8c0001dce94712be000000046380000000000000184c0000a90000000000000006dd3aec00013b60000000000000000034a00003a984cbaf7c785808c00a0b640000000000386c000328a000054600000002e0000000006620002d586032886000000011f800046c81c2000064000008000a70000419800000011e47e0800000037f0b5305ca0000000000000000000000002bd000000009e88012000000003f0d1800000000000000000369278bb314e731fd21e22e509952b0c1c61cc200003cef10800
  | 63 => 0x86c9d0000e5000000761c56157000000014c60000000a4a0884dea800016aa3b4000357800000008dd2fce00000004b88000c0780009b9b5dc5ff0d103642e320002bc2935167468cade819b80003a60000000000000008e0c40b344544b542000000088e31f6d0400000002d6c1c20000e68ba3e00010300000ba65300d005b7000000008a2000258400036aa22db2c8c192d2490a80000002cd60000000846800040600000003c4c70b80007be8000000001e00000000000000000000000000002c3800000009fae0680001a222bc33c997800020be9d28e4e0000000000143a6800b9e0fb09c4cba800000026a200000003d3800000034320000d7a4a11e9c0000000d5194b6000223c00027e00000000000000023f9a741c7000061822de5ae8be80002e7a9cb0000000000065cb006044836a339041693c01d60000000000000000000000000ce6b1000000000000c3725720003a960000c5e00003400000d441ad92ce6ff84707208000000000094385649d100000000000000000000000000000000a3120f6c9b9e580000000e4580000000cf62b905580512d060002bec6241a6400000005178000000000010080000000000aa12c300001e9400023a4000000000000007f280000f91c480002fc20000000dce000000028f024380000002810000000000000000000000367abbe000000095d80000001044561800000000000000000000313eb94800000000000000000000043c9c1800000028a2c16b2729f18000ef31ee60001052000000022d000000000000000000000389435e0f324b1165e69b800098ca68e96e800072293003418000efd98587d4245e7a20000000065213980007d7bbee00024f29c9a66a21d215c410ac60483a248a2f00000000000000000049f0000000000000013ae000000023cbb3e9e7a0e6e171f0000000009ef0000651800067088ca000000000000000000a2a8600000000000000012a228e80004448a04ce11fa45a0871400000000000000000000000000000000a9eb1080008ae000000000007dd8000000069a2638000ee7ac6e12980000000eeee14a39c0000000000000092e80000000000000000040400000000f12a0c80001aa0000443bb7cbaf000084a00000002ddc0000000000000013a0000000249ed92ab1ea998000d9f90d6259224a6ed097c00037c800029e8688800017080005879b5000000000000000297afc400001a80000000c7ca7b00000000000233a3bf0000000000000000007ac8000d62ac080000d0e72c8000d66000059716ea000000000000000000000033aa5a00036281a28bb0000179e000000000000000000000000330e0001fe80ae80003ab0000000000035a97c4d1f0b2c0000000997b7b000000be00007e2818a09418ba78094ba10e00016eecc600000000000b6
  | 64 => 0x478000be10000337ba1e000257a000000071e00005b6000000028766b3b6406a6115c24298bc2faba3201634be00012a056b23a0000000000005a47f52bf627f80004c82aaaf008000177b34800000000001fac0000b1200038fe0000000000000000000000000a6ca5c0000397a31e4481980cf900000000000da6000000003063502fc8763a40e3991ca20001fb80000000db18000000000000010b000000000002628a0ba5200002206b888bd641919201e5800000038e44308000000391adbfa0ca0002d6e000340a0000000da2a354e6d156aeca1a9a8fea5c0923a5f2000000000031e800000000000c6e00038ca0001008000048200000000ce80000003be000000001d4975ab3a0000d5aa8f20000000ed6a6f600000000000000000180871c819049908f6c7e000000000008131dfa00033782c618668e5000000004265b6800000000000000c986590000cc9800000000000001af8def000071880000000000000000000000004ae800002f209c00000000001154000063c00000000000000a5f80008d991b000000001ba00005fa800078000000000000000000000000000000000000000089083160000000ce63bac00000004e886f6ef2ad9c0000000dd08000000000093100000000000d341fba0000a248e615042698864b0f00000000000000000042f8000703a6f000000000000000000000005e800006b84fe35c23fe0000000000000000000000000000bbd000000000000003498000163c2c7b4ea2928000000000000000d6ee204369190000eca80005d98000d2b37e0c85b33a00016f66c8800069f00000000000cfb080c1558000e2a00003620a78e030000d1984086ca3c461922b9263696467de80009b824206080000000000000000004dd02fc00000000000000c7d0000000000000014a07f7a8e6bf3234a0f5a12a68d8000e88b33800000000000daa000000000036ca165ba205cb3a30cb1b540000000000000000888844000000000380000001720ba900000000000000000000000000000000000080a00000000000000000000005f16f8cf7907e524af6200012500001e62d0a32e80000000000000012d80008f90000080b95400038f669a2430ad900009779f9a1c3000000000009f981ec2e717f2bac9d16000000000009460e3a470e7980000000f5200016d079fa8a800003fe9cdbbaec738000bc2953a0000000000182a73380005a5000000000000000000d248000e04800055c00007cc39a6e9e9eb825680009919ac60001df041e000019e80006c5041cbbb80000000000a0680000000000dd38000ad63886000000000000000000000000000010c8000240107200012ca00009420001780000000000000000000000000000000013c2d49280a355ba0c0000000bff2c1e0001dca985b296000000000013
  | 65 => 0x5d074c000000000006d5800027680000000000000000072523e20f08000b6f902200018d88530000000030e0000000000000000000000000000000000021b80000001ce4980b3d0ced9b5e08e94fa43d930aac38e3e3410000797269802c0a8e7592e6c750b67aa8e000000000003061a420002410d6e0000ca980002732e46901b77a0000000b8f00009c2b47a36d831214492bc5510000000000000000000001c9c0000000000345c1da800000008720c6323243b000032d000042e8000aa4b4800000000e929d0ebdd10ae00013e40000000000000000007c6af2371000001b20ba9d260000000b2d221e00000168b1b4e600000000000000000000000000009b4000000000000001f5a1c015b6e91100c8a68b266bb84445f9a91600029200000000000104c000000000000005af163000024aaaf78cd84ef9a8210fb8c061a984233bb7fc00000000001f64000222600012349862e700001370000280c2f799f0000000011a9e720003b200003a6a601ab3800013e274fa4a87903bf800001b6000000000031e00000000e6fb66a00000000b49a7aaf19388000000047603dca823046000228a00007800578000000324e00029a6e2c80000000000000125442480000001690e75ae6464481e85bd000000000000003b985270000ee39f560000000000298200000003f8393a0002f68c96033800012b40000000779b07e0000ec8acd9bde897800078c15fa9880000000095200000002dc80000000000d8baed6000000000024ac4c41cba000116ee54933017385bc248b3ac0000000cac1cca0003c3400008e400000001b593ba00012cc000014248580004d90000b8d07b8a418000d7b8ad20aa000000000000000000ad1a10800000007c080008b71db60001c7e00000002243b30eb60000000319245fb89eb7d3820b4e81a6cc8006437b0452000152a2879000e44111cd1d00007d7000031f35bc000103ae63abb05fb80000002bba837800085a80000000000263000000000000000000471800000000000002b226bc0000000000000016360000000b64b89607e98ba00000000001e3ec26800000034fc7e380001df8000c4900002b6904060b8000000000000002b80c20000000304c0000000abe0536000000000036a07d1000000000000002150c7f2f30e352504000000000020dc0000000be592e84172e10d683bb600000000000d62000000018c1ccc000045aaa0000000009b40000000aff2d460000000ba6a7348bd00000002962d353488467a6f2000000064d0000000000000000000002a3e73b0bd2c7607e08c829560003c0ebaa34a2e3e800033e00000003b7a65580008cf000047b00000000000ce30000000000026b0000c5c000000035fcb450000000288a7d9a2c4000008600000000000000000000000000006b580006
  | 66 => 0x2a2e1200000000001372df42878000000091a000094d0000000000000003424169c90d4480004738000692bc3e00000008b6251ab7b9cae94400005c181da9b92d7e00000000000000000115ec611282000025c000000000029aaccc800000019b20002f5a8c2311c79e2814222016e46a800000000001a501baeae0000000065800000003f10c6a0000bae0001ade00000000002d48000259e21a2948000066a0000afcd113144e95b3e280380000003a8c81d95fe000000000028aaa751dd800000003f500003ae1bb6054bc060002dc200000000000000000083cae080000003334000365200035328780a0c000000000000000e030fa98b2ed250280007b4800073d3452d5b248ca2ba9fc000154c000000061bb7e60003a8e663b0e6b7f32ac358322c9ac305200000006821dd6000000000000000002cfa00039a8ac000000000df000000006b2800028439fe00000000000bf466c00000000000000000000009ba00000004208bac0000000ad48dd6045a85c00000000000ca400033280001f90000000053795d417d28d4c818000a14000024f00009ad00004fda0cc62c3b12a303b8a5950d9437f203e0000000c20a45c0000000bd4234800000003949762875a93e139000069025cc000113a0000000000000008b8000000140000000000000baa0000000000101436e94367e000da1d02c629c796e40001f92e09b58c21680005908000d8e2a7a47e289871700009738000000321c78cb0aa0298f764f0146a0000000000000018524b291d8000000000000002081ee94dcc4d810c00039d20000000087aa7c00000000000a1a0000000c360000504ab9c99894225d2800000000000000000000000000000004e60e38000000000036b4000201000000000000ae600000005600d460003c180002480d5a0000e5e82e4630000000000000000000be2b4e200000006f596fe5a780000000000d59ad106ff32cebb700000000000df5000091580006010b002ce396056c32ca3ebb230063a9046ba11ae00000000002b2e8a79c04000202abbf00001378000000000056786eae9f17cae57065c00000008be8000000000000000000000000c3c00000002ccea110000c77af52598209e0001616c0b80001cb3754103077a8418000460900a17e8000b139bf2000000065480000000000000000000000000bc80002a93458c2f00000cb8ea22e6b8e02a300d447bb4fe36a0000000000000000000000000000000000000009c48098647000030080004598224000000000000000000000d378000000000000000000000000a09800000000000000f601018000dfe929e0000d5453f2ada000000014e00000002644000281800000000003a060003be43219ee800027c2000000000000003ba39649ee8000000000066228e42c0ba488db9e380631
  | 67 => 0x38020000e5a11d00000000000db0075600019080002aaecb100000000000c6c23786e68b300000b8cc3686c80000000000000000000000000000000000000006fa187000000004c4de40e8a69e285a02d0000328363a000087aaca8000000025a0000000de18c4a0000000000000036b0000d80b71e05900000000000b5d000000000005180f40ad280007ef04f024e81d200004f2000191824fb5ec56d0000b340000000000000002e200000003a73c048e0177ca64000000001f242d832257992dc8f2b7761f7bbce000000067d2f240003620b092f34679000056a95b20000000cee2a76000196c0000000000000000020bc0b4344c87b882285a334a0212f18c9c317689a80007ca32b8b0f80006bd80080a5800000000001d5313c00011907698000000000015e80000003b08775000031580000002e8200000000000000000221446700000000000c488000000157400005520002b8800000000000000d328f0e000396c9a6a4220000a1493d80000000000b4fb1f09ed0000266b15e00009e6d43303200000004038ff22f7107c00000000000000000000000001660002ffe0000000a190f88000000000018f461d19deac812fecc89d327348000912bba0c2d0000000000066b0000c2c000029d00000000a4ca9c00000001b100000000000249c387b770e5102f4d7f80000003b141f6028c5d59994cc6987c442180a0002a280000000efb00000002e600000000000290a57ca54e1bf0e62131a14400000000002e720000000ddb17c0df12438000000000000000000000b798000000380832300000001378000214a906a5d86f880000000000e2637a6000000000000000000000e13800000029b200000000000b16a19927a000063e2521b96cb32f460000db0b2080009a0ab5e41da77c41d33da35400000000000ecf000024a80000000000000353a00035064e805881eb85340003b2e0002aa2f0b8000bb8a6d27402568bd600000000000000000014b000079a0000000164c0000000cc1800000006220000760000000000000000001bc0000000057a8000000292e00011800000000e2e00000000000000000099f81f6246364c000235e1a98000751800000000000001d840cf800000028a4000327c49987f4ca8a130d271150000343e848bafe934a1d86251e123e48000d82802cbf6800000000001e380000000000b8596c2501af0e1c900000000000a2d80000000000000000000023f20003c26000000000000000000000000000043c80000d6800000035b00002d8e00029720000094ab988e2000384c00026385ec884000039fa645219c000000000000000000000d7a80005bc39f8000000000000008f38000c060000f100000ae88000000000000000005cb9966000320855b19c03a5b14600000000002f20d8200000afb050
  | 68 => 0xa220a400009f4086000000000000000000e3d000047e87b600018dc0000000000332a6c48f3ae5d93f8a2d2d6600014ee16d2be00318000a54800013e88d4132849ed7e83340000000ce700000000000000000018c80001682fc072a9fc6bdb9fcea018000ce68000f090000ab607f2000000070a8000e338000000000034a80000000514000000000020a287f2a4e00033c400020825478000849931212281e000024503a22f6c0003c0c00000000000000000000000000000000000000000000000000000000000000089e820c000000090b8000000046e0000000000000000027ca000000000000009e5000081c8370844359abd30000b9ba77e000000099900008a70ade00001b00002a900003c547d000000000000000000000000009eda0d649a195e00000005fe9d8a0003a62000000000034f20003930e7d2ab2dc6ab68c8b8ac0968047ab32000074080001981936ab2b31272313da0000efe0000b7c2ce800000000000000000a5e00000000000660800000002c2000000000000003a19fc80000000000138ae109faa00039a0000060200000000000000000000000000000000000ce90000de084d4e47a69ecbf9fc20002d863f39cc00000000000000000000000963214000990a00000000000000000000000039ecd8c1f3665d0000000000050200007268000a0b013a6f82976278240c0001bea0000000000000000000000000000ec0800004d930e5778000000000077683cc0002c287530cae7b31c804d20000b4a091200000000000000e7f369a8fa8000000000000000000000000a798742786303a0a600000811ec446880006b105f00000e2a3049c200000eaab46b8d6c6b8000a691d3a0000000a83376e0000000bb781ca6e792ac7389c6ee19348200000000000000000373e000000000000000000000e652facb6b0000000006e00016640002b1000000000000000000000000002ac00004460000000a478000a0f00000000000bd5800000000006200000000000000035725af924a0000000000000000000000000000543a96a00014760001c4032c000000022d46b609787898de40000000e8600000001c9698f800091e00000000000a1d25c448238820000e120000000e678000000008e67a351c000000000000008f480000000000e8f0000000265a4528478832083a10e82505ab0000b7680005f38000000193c6d980000000000d98972a0000998534a674d8d066442c901e00027d280b801c000302438b86160003b8c0000000e0780000001080e9404cea7c8646000000000000000000000a0fa2ecb6d00009908000000000043a80b8ac22f028b6b2d401f207426d8000b14000016f918aae02e8cad8825e9a8000090d129400000000000000000000000000006a1000000000001540000000370e000
  | 69 => 0x233400003640001afed73800000000000001b52b720c9e0000000a6480000002de4000310000004566dc177290f1f0a6cb0000cf20000b19a34e277889c0001aa8be50000ca8000000015f67bfb75ea4e0d8e3ea363251c9d727cc800014b8000000201a000000072c00007490000000040a00000000000000c97800000000006e600001ce8000de5aa18c7286b85258d42ee680005bc866cefc80000000000743000000031d40000000a6000003b4ba280003114935b64e00000000f4000000000000000000018800000005940000000adb934a0002514eb6abf2000247e00000009ce000000003c40001a88000000009b000008d800000019ee2058000c6a80001ab800030b0ab47662330c5f80002c40000000344a00014d800003acd2e00000fd8000421a292781800001813461f2894ef1100000000c460002db649c2bca000376a3eb353c000000000000000000000a44000000000000000000472946e32c800060007f81f2000023bbaa8caba7f65d0b3545cf80002a580002ee00001e31b1a3ff913800000000000388000000000006f291ea5c60000000000274200000000000000314a13c0002c1a00026a61ce1246ab8800029c000062980000000000000000000000000000000000187e00000000001ad475e00000002aee000276a000000093f80000002f4a52c000000020f8000000000000000001970daf00000000e46683ad64000000000000000001bccb0db396b81aca42e580008f1222200000005c4000000000000bc00000000000982882e00024f46190000d8780008eeaf385f780007d6039e4bd0192bf62cb24ae0dd4000094c000000086c23004bba950759800000000000000000c4e023000000000001ae6000000000000000000000c411026000000000000007198a620001d820002542d5d1df2dc1b7a00003504067ab780000000c328000000154000000000000000b898000ac90000ad3a73c000332c458000000000000002a6c0000000000000050b9d34132267a00000000003246c571cfe00029d29a00000000256200000000000a72d4d09aa2431c50850bbda8afa44e204961200000003e180009d400003acabcccff80000000000921800097900005941dc240494e205aba540000000000000000000000000000000114e0001dd2000335e00014400000000000000000000000001a5220b3048000000000000006830000000274c0000000000000000012f63630458000000000008c20003b4c6f529de7fc000003b352e000000096997aa0003112000000000000000001206000284ac7737cc3f0800042f0ff0a5a0000cb70624000000075235a88f536f8000000000000000000000b0e800000023f6a8c056e00018ecbf29bfa99e1d7656700000000000f15800000013ea4c18000000000
  | 70 => 0x410000304200000000003070000000000014be22380000000000000024892f8dbe5351850d368000b510000777000046b10700000d0c000000000000000002fe800000000003bf40000000cd41e1a0001b90b2e9418000000060a00000000000000000005a12489ce8000cf3126a00002c42e2881a00f80000000000a7b800003480000002fb800016720002eba09026fa0000000000000000000002f2b1c4000000000011860000000000000085e00008a3234637d800000000000003a5eb690f564da1d0a3e88000748800000000000000000d69000000027305988d9200000004788000b96800000000ba519800052d0000000226c000000000025f053aa12400008bc54c80000002fb60002936dd200000000b2a3ce21f600011b60001622a1509b28c736b0efe800000026600000000c1814740000000000000050900000003800000022ca81143423e00000000000000000000000000000000add00000002dbcb0baa5640a2a540000ef430bbb44cdbb068a2cb0ce12535702bd01f40001d2c00000009e08000dd6800000035642b539d0000000072380002a50000e1c0000000000000008fa7e20382bc7875e17600000870000ea1000000000000002192000361c000000000000007828000a7d8000d01a9d6573000003980002e102dc0000ce247f00000003be231380000001e4c643b0eebfd128c423b52aa450778d15ba3a8871f984f72c160ec8866c1f0cc4bea2f3e00000002f332820000000cd680000000000000000079f000038605f6000000000000000000000000000000000006fa15becfd000000000003cb0000000000040dbbd867b0c000000000000084c9bf00000000000000315a62c8786000145620780009fa00000000000bfcbaa0000226000000003aa2cb00002ec20002f120000000a309df426700000001f2cb4a938e00018d60000000000000014000000000000000000099580000002116000294424b80000000af67991e8a0000eec0002f90c7480000003bb2af5133a000000000000002098b68edd8c90df38000000000000000000000000000000000002122a02922a7c0000da9a12c0000000000289a71e8000c532bb8c12800067184bc000000000000000000000242059aec2837c86f1096b6e80003de0000b41000000029429eabb1ed0800000000000e55b6ac0002aa80001ff65c3142a000000026899da0b18000000000000000006b810e498d0da4e9301545d38b90e622b2c4272feae9c9df60691b4018d86be495a3509a2231023a2e5c42e3c32ca900001ef80000000000000325c794b8b000015786f11f1c00000000002d3200026ac5803ad2000000066e000000000005d800001f68bfa88900005d3000000030584f1013220e14980000000000219816c369c0000000000000000
  | 71 => 0xb6e00009300000ecc594b51000000000002fa29722ce00001870000095000000000001a3c0c291f02da80000408000da9000020d0000a8013f00000000000000000000009998232aa2b5c80000000cae80000002f1400d922663190a40002f7ee2338f874400003ecac48ea08ee0000313a8e7ac90000102c6501e7080485d0000000000000000000000e7624a000000003d70000ae380000000000d268000b018000cec800000000000000e9446300005f52e20ddf038a0000000000000000005fe0000000aff800000000003b100000000000e280000000000000000000000000000000000028080001d9a000000000000001da0c7400000000000000000000087f80000000a9a00000000cc8000000000030800000000000a1a307866a800050e2e7c5722be800000000000000ec300000000000c480000ebd13400000000000206000000000000000000000097d27021460000000000000000009f600000000000868000039b2cf00cd80000000000e6eb5380001ef20003c005d52ae4a210c240000000000211c64000000000000ce42c7600000000002fe200000003db80000000000000000000009a04fb80005900000daa334e0000000000000000000000000000c3226c20000000000000000000000001f6a934000003300008020ed896d00006c6000000000000001eb600028400002a1a15f80009a9000000039460002b84d63bb6a0000000dd910cacefa1b8000000014680000001de4f0a3682000135201d23720000c1a0001098000000000000000001e3c0001a941b8815a0000e2825a832464890ee7dc996800000000000266858204a10c29aeabe889edccba2ed7c1adc5a031a422a17e2194000047994ba0000000217800083a00001a1000000000000000fda03280002d8181e2c18000000000086a02b60000000000000000000006320000a8804040000000000000000000000000bf6b5c0000aae0000000000000000008079f20abc83ca9d217a6be9b6f68e28a4265836ee4df0cb800000009ab800044d000000000000000c9a043867200035c6a940000000000000008dee028000aeb80000002152c49ac9c0000f800229ff8da500000000ca85f93b929290000000000000022c8000000000034340003aac000302a00036560002b0426900001ff8e823370000000000026c000000038280000a567b5b54e4e5b236c6d00001b91d900bea9cc000000025280004f535203ad80000000000000000096d8000000000000000000000b148198e0a000382c00038a2d383496d0480000001f8a00000000002b6a00000000000000e710000665800039c07583fe800000000008a10000960800000039e2a6f000000000000000c5400000005b307ac360301600000c0dca00000001c64000000024d031c04c33f0d2d098400000
  | 72 => 0xa026869ec200025380001a4c6d7000000023be9900f7e5b8800000000001480000150000000000000000000000000045b000000036143b9b2f0e6d80002d000000002cec00000000000000000000000033f80002250000000035f3b063f400005d400008f800007baa91a87a38580002d300000000cc22812db139a4000000011b38e8000000000000000000000000220e09b9fee70d800000000000000000bac00004a400000000000000138c000000089c8ea0000072ad0e9ab8000000000027ee0003bfc00000000000000bbe13541f9b1509812a720000000a1f800088d00000000000000000081e00000000e840000000000000036b844e972abdc8e1306e05314bc00000000002c540c332c29b5ba92000000073680000000000a78a18a000000000000000000d2400000000000000006981c000000089b800000000000000124d6eb168ef093b0062aeaec9d9b0207b8000480af4e4a9abea23aa49a33480000001cac0003a52edc09e2caaa1ba0041ff43868000ba400007a98000bb218e628619bc00000000000000000000008e27da00022301db8000df90000000000069b000000000005c1000000000000003876d0d9c5eeed0000000000000000000000000cfa80000001b3c41400000003ac00001df80128000000000000000000000000000000000000000001ce000000004ee182c51497e080995520753b560002c920000586ccf0e0eafeb55200000001579ba237a800063b80000000f169ac800000000000000000000000000000003e596aa60e02a487a9822e7c246eb4239bc77a800000000000003918000000014eb580c3780000000000dd98000b83000000000000000000e62952600000005f0964ad3236c84ca00000000000000000000000000000e785ab921e00021de0001db20000000cd0a40400029c87b29ffc55400004c900004468000b403ab600000000000000000264e0000000000000043a0056b4b3b7e53108040000000dda0000df28000000390a979978e0cb0044dabb4c40001e5e6379218c0c10d20001c2229180000001eb000000000000000000173a00000001fe9f6e0000000370800000002a60001d1a00000004ef000000000000000000441000000000000002a7e3f19b8c0001c700002da89b38cecd1092c80001e20000000000000002d580004be80006689b1e353000072e03040001c60000052a4b6800083490207550000756800000015220000e4044893e60001cf0c6eb89000000000001c4a0000262000325400015e20002cdee36af420000000000000000001188389ac2d6d8f9e00000004aa9dc8b20000000000007c4169a5c50000e01b6005e600009c6000003f80003cf2804b8a20b60000000f0f000000000000000000aa50000000000000000000003b8400039240000158000252c0
  | 73 => 0x7f8a0eadb000036800001b1836609925ae0000000ce7800000000009c104a00b8000000000000000000b5d8db2000233e0002ef200003e2000000058081ea000000058a0cac0000000b308000be1b42200000000003b6200000000000000a1e85823c892eadcb82346c9b5e81c7b626e6600009f500006a019624bc8000000000000000001569468a82957a0000876000078ac4410060002a6ab08800000000004c58506cd4b6b8b1d05c60002b3400000000000000000000000027be000000000016c80000bc03d116b6a9220c60003b5000021a62d400007998fea270a5b06100000000316e0002e84cc10000c682ebe0000000000022a0a7ae180000f6c0002498aa700000b5b11ac173be6cbc8f62ac986b4c5cb8927b732daf052f9e8f089ca9221b92dd88f34caa20bad1fbc4e0e8911413e252800021ae48800002ed8000640a3029021ef021b22d6ca2232cbad800000021d2ddd0000e30884e00000006db800000000000000000a158c3081c2cdc9c5800030f00000000000000000000030e8b8507e45ae2eac00035e2000000029928ea138121a4f30000000242c6121dc0ea990fa000046800025e250a23908062820e332c640001a2a1e88e74317265066288102ed2a78c91346c8428cd09673a900a8270eadd80004d09dc432100000b0119800000000001a9e000000000000002cd00000001c3800000009f3a2828fd0ffc17a00000002b540003ab2000201400000008721e1c00000000000e321c5800011f387255f8000000000000025a8000000000000002e0841412b00000000000000278cdd60000000247c0003486cd7355a175823e00000001368000a07977422500006e294f4302a326ef20000000000000000000002530000000000000003f00000000000000000000002cb6b810000000000000000000000000000000000000005c880000000000d832d5a0ac1a2e8d69ad2c523a100e6a56a000000000036165e4800000000000000000d740938e8b000000008cc1ca09f0a6ea684000267c78380e220c3be8b3bb1186631c167fb000000000000000000c02988c000158426580000000000898a4581c6949eebc818200002aa937954a000000000011e00000e500000598000000034db974141000050705e2957000000028ac76b01481fc01bc23015307888000e42000087d0820ad700006848ba200000000000000c65a2fc00019b43cb800019f844a0002d604a1aa9ae648216a890ac8dd715688190000d1e000092e00000000000c052cc0a981dbea6280001ec01f000000003bd800000000006bc891e30ab89c00039140003acc000000000000000000000d9e0c3678917b4cc2af80edb80c45f31b480002dea0003740000000000030eabbeb45e0a380000ca0c4c000074c06e30907aa8000c9880000000000dc83
  | 74 => 0x3a8a000000000030c0000000011900008d0b388eaa800000039264408000000000041b000000000000000000000289e0000000000000000016c40a537c00000000091aa8e00000009ba00008b4a05e70504920000856271b088000000000016b46de800053a00008b89c4e0000000000263600000000003b4ae618000000342a000258ac6280009110000000000063a0000ac68000ecd8000000219000000ea000345adba3abce2bbba400010f400000003771aa2a379b34c4b912e0390268ab533a6652800087700000000000a2400003c780003dd1644f0b000000029ac05380000000000b9000000000000559800000039e80002d6a01401c48448000000304e000000000018fe2a8800000000000000000000000073e102a00001060001fe4db7123e74480006ca800000000000001b86ab800000003bf0c0f085200000000000000000000000000000000000000027c08f00004bf000000036fa0000000000385e886800000000006679e480002ed0000217c19e00000002f06000000042793220000f3000000000000000ed48000ac5800000000000000000000000000028d20000000000000000000004f60000633adcae34800072d800002912b0657000000037ec78a000000020d45a5800000000002481d3c00000000000486d65860ada10000000000000000000000000e8680000000610e588000000000000000000000000bc8af5471b3a5a000352600000000000000000290249d26c404e00000000282e1e8f1a8632544d650bd46f08174e0e00003578000e3c3ae009fa1620000d3e76c15a4a2fb4d240e36d836d1ee200030ac0d6332e1140000ae18000000000000000000000000c4d2e56da00000c55021022eb37035fb2124c687bc1c1afe4e57b51abbc00004a6216e00000185c08000c210ccc000043400012c02d6000034f00005a33ae269623d80000000000000040f80000000000c86800000027cc0000000b04869ed2b87d00000000ec908ae02b83864d8000046686565cd2f826840000000262ab3a800000000000002bac9f89d44c67a25a51e00000000000000278e00000001aa817800c80001178000c068b782201296000000000000006e08000000000000000000002f9c4cc914277198faed0a1880000bc6474824a1603690cb6120c0000bd8e4d00000002c260002d948d713382ab3b2c0000000000000009a97f49258000000309c70b000000028585460000000000000017ecce39de21b7a3120000000dd480000000000000035600038ec0000ce00001e4688b11d0000131800006749d380000000000000000041eb97c63f0da23ac191000000000000000b54255eef01e2c5a3abee0fc80003408000000000029728020002dfa59e333000000000000fd2000000000000004b50000000000044a8954
  | 75 => 0xdd12bb4000065e8339f22d58b72c129144ac600000000096240b903421aa40200023f8000000000010544f807d22c2824cb9a14cc5430cea9370000000000000000000001d6c000000000017280e48ba00000000000000000000000000b2800000000000568a818000000000000030ccc3d8000000276e00000000018000000000000000000000000b6600000000000000000000006c40000000c9ea99e000000000000000000000be380005cf00000000000000000000000000000000412800000000000000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xba58110862440151d904ba0c4880021fe15731891001c3e42ae631220008bf845cc624400517908b98c48802aaba1342189100145f424ed29220008bd849da52440a38f4e1b2ca4880063e21970949100145f424eca9220008bd849d952440010ff0abb2a4880022fe1176549100145e422eca9220008df835d9524400f1b906bb2a4880023de05765491001c3e428eca92200a87e87d955244001878e9b2aa4880030fd9774549101f61e32ee8a922000cae729da424400147f0abb484880fa8f21576909101f51f436cb21220b6c3e72d964244001c5ce5b2c84882d70fdc765909105ae1eb8ecb212207aa3e86196424400117f0eb1c848802a2f21d63909100051fc2ac7212203ea3c8558e424400155f04b1c848802aab20963909100045ec3ec521220b4cae72d8a424400117f0eb1484880028fe1562909101f51e42ac52122000a9f8358a424409b53906b14848802b2edda70909100555c432e1212200087f855db32440070f90abb664880030f9d365cc9100061fb2ae99922000c3c655d3324400195ce9b1664880032b9d062cc9100247a432e39922000c74655c7324400517d093b464880022f612768c9100043fc2aed192200387c855da32440031f10cb84648800e1fa17764c9100043ec2eec992200387e859d932440010fb0b3b2648800a2fa12764c9100045ec24ec992200087f855d932440070f90abb264880022fe11764c9100145e422ec99220008df835d932440011df04bb264880023de05764c9100047dc02ec992200387c851d932440010fd0dbaa64880021fa1f654c9100043e43eca9922000c3c74d95324400187ecbba264880030f197744c91001c3e42cec192200087f855d832440070f90abb064880022fe11760c9100145e422ec19220078dc835d832440151d904bb064880021f219750c9100043fc3eca192200087d87d9432440091e90cb8864880063e219700c91003e6c31ae01922051c7476d95314409f8e8ec32a628800395d94634c51025e5a3b48498a2000ad4864c931440956a90a9926288002f8608704c51012e3a38ecaa822000c7765dc550440095a90c98e608813a1fa1b754c1103543f43eca982202587c87d953044001878e9b2a60880030fd97744c1100061e32ee89822000c9c74d8d30440093a90e98a6088012b5219314c110256aa3aa629822004bd0804c5304409d0f90cbae40880961fe1f65c81100043ec3ecb90220b39b98790a2044001878e9b2a40881479a08365481100061fb2ee89022000c3c65dd12044001958e9b1240880032b1d062481100247b436e29022000c7465dc5204404b8f0edb2a408813b1e1d865481100065c3b6e89022000e6b6518920441653750f212408802b2e1da424811005754314849022000ae8864c920440013e10e98a4088003f04c93148110
  | 1 => 0xa83baac68800a2fa1f7458d100061fbaee8b1a2000c3c75dd1634401517d05ba2c6880022fe077458d100045ec0ee8b1a200087f855d163440070f90aba2c68800237e0d7458d1000477c12e8b1a200a8ec825d1634400117d0e3a2c6880030fdd47458d100061e3a8e8b1a2000c9c74dcd634400517d09b92c6880022f6137258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000657426e4b1a2000cad84dc9634400195e83b92c6880032b5077258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a200acaf841c9634401595908392c6880032bd047258d1000656a08e4b1a20008be8710963440151790e212c6880030fdd44258d105461e3a884b1a2000caf721096344015958e4212c688002ad6044258d1000672396e2b1a2000ce872dc1634400187ce9b28c6880030f9d06518d100061fb2ae831a2000c3c655d063440011bf0eb18c688002a72116318d1000566412c631a2000a5d83d96534404b8ece3b2ca6880123d2197194d100063bb2ae329a200087f855d9534400117f08bb2a68800a2f2117654d1000477c12eca9a200a8ec825d9534400517d083b2a6880022f6107654d1003c3f43ecaa9a2000c3e74d97624400187ce832ec4880030fd9574d89100061e32ae9b122000e2f6510b6244001c58ca216c488002e960442d89100045ec3ce9b1220028bf875d3624400195f04ba6c4881622fe0574d89102bc5ec0ae9b122000cad7410b624400155b0e216c4880032b61c42d89100071742885b122000e2d8510b624416955f02216c4882d2ab60442d89100561f212eb312200ac3c425d6624400187e82bacc4880030f505759891028c3e436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab122000c3f65dd16244001878cbba2c48800317d9773589100062e32ee6b122000c5f651cd62440018b8ca39ac48800e1fa1f75589100061fa0eeab122000c3d41dd5624400517d0fba2c4880030fdd774589100061e3aee8b12200a8be82dd1624401517905ba2c4880022fe0774589100045ec0ee8b12200087f855d162440070f90aba2c48800237e0d745891003c6e41ae8b1220008ef825d1624400117d0e3a2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c9f41dcd624400193a83b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880032b1d372589100066639ee4b122000c3f751096244151878ea212c48800327dcc425891037e4e39884b122000c7475dc562440019a8e7b8ac488003361cf705891000477c3ac43122000aac84588624400159906b10c4880038bd94421891000716328843122000
  | 2 => 0x776480200065dbb6e8900400aba882dd120080019d6eca924010002eae11524802000574c36649004000ba984cc92008015d5484b0a401002bb8c8561480200065dbb282900400abaa825052008001d62c2a0a4010002dae152148020005d5c224290040008df835d1658400f1b906ba2cb080121f21d54596100145f426e4b2c20008bd84dc965840070fd0fbaac7080030fd077558e100061ea0eeab1c20028be87dd1638400187eebba2c7080030f1d77458e100545f416e8b1c200087f855d163840070f90aba2c7081a22fa1c7458e100061fba8e8b1c2000c3c751d1638400517d09b92c7080022f6137258e100045f43884b1c200a8bc87109638400187eea212c7082a30f1d44258e102ac3fc2aeca9c20008bf845d9538400517908bb2a7080121f21d6554e100561f212eb314200ac3c425d6628400187e82bacc5080030f5057598a100145f43ee8b14204b8be871d1628409717d0e212c5080121fe1d6594a1000537c12cb294200a87d85dd9528400117f08bb2a50800a2f2117654a100046fc1aeca9420078dc835d9528400117f0eb1c850802a2f21d6390a100051fc2ac7214203ea3c8558e42840a717f0eb1485080021fe1576cca1001c3e42aed994200087f855d932840070f90abb265080022fe11764ca100145e422ec99420048ec87589328400117f08bb0650800a2f211760ca1029cdd43c84904200aea86290920840095d10c9924108002f8e0532482100061eba4a9b2a200287f87553654400587ce8aa6ca880022fe1173d95100145e422e7b2a20008bf845cb654400517908b96ca8800297e0d64d95100052e41ac9b2a2000a6f8259365440014d904b26ca882a30f9d842d95100059ac0885b2a2000c3f749d3654400187ae83a6ca880028fe1173d95100051e422e7b2a2000a3e841cf654400147b0839eca88003175cc73d951028d3ac08e7b2a200087e87d0f65440010fb0fa1eca880028fa1372d95100051ec26e5b2a2000a3f845cb654400147908b96ca880969e60072d95100043f43885b2a200087d8710b654400187d0e216ca880030f61c42d95105b51fc0885b2a20b6a3d8110b65440010ff0aba2ca8800237e0d745951003c6e41ae8b2a20008ef825d165440151d904ba2ca8800a2fa1372595100045ec26e4b2a2000caf721096544015958e4212ca880021f61e64195100043fc3ac832a2000a5f8359065440014b906b20ca880029be09641951000536412c832a200093d87108654400166b02210ca880022fe1172d8d100145e422e5b1a2000ab58110b63440010fd0fb2ac6880030f1d36558d100043f438cab1a2000c3c74195634400187ecbba2c6880030f1977458d1000637b2ee4b1a2000c6c65dc963440018deca392c6880031b1947258d1001c3f43eeab1a2000c3f41dd5634400187
  | 3 => 0x598a4000c7675d87314800517d09bb262900022f613764c52001c3f428ec98a400087d851d931480031b90eb1a62900b297215634c52000d6a40ac698a4000ccc764c9314801517d0fb26429002a2f21f64c852000656324ed90a40008ee86dcf21480093d100b9e42900030f193754852029c5f436e890a404c8be87d9121480971790fb2242900030fdd764485200061e3aec890a404bcac769092148097b50e121242900031d1d7614852020e363b6ea90a407ec6c761d52148001a58e83aa42900f72b1db744852025e563b6c890a40048ec865cd21480093d100b9a42900035add47048520006d5ba0e090a4000c6f65dc950480010ff0abb2609000e1f215764c1200045fc22ec98240028bc845d930480031e902bb260900030f193754c1200045f436e898240b98be87d9130480d31790fb2260900030fdd7644c1200061e3aec89824000c5c75d8d3048001878c8bae409002b5a08175c81200061f3aec99024000c3d75d932048097974edb26409002b78c8571c812000e5d3b283902400487c8755165080070fd0fbaac6102af0f90b7558c2055e1e216eab1840028be87dd1630800187eebba2c6100030f1d77458c200545f416e8b18400a8bc82dd1630800117b03ba2c6100021fe157458c2001c3e42ae8b1840688be871d1630800187eea3a2c6100030f1d47458c200164e3a486b1840048dc8750d630800117d0fa0ac61000a2f21f4158c200061fbae82b1840b8c3c75d0563080074b90ab1ca6101561fe157654c200045fc22eca9840028bc845d953080090f90eb2aa6100123721d6354c200043fc2aed990400387c855db32080070fd0fbaac2102df0f90b75584205be1e216eab084000c3f41dd5610800187a83baac2100021fe15745842001c3e42ae8b0840048f48750561080a30ff0abb2a2100121f21d65544200247a43ac2a884001ab481dd9410800147f0abb282100be8f21576504200055bc0aeca0840008bf8758d41080011790eb1a82100028fe15635042017d1e42ac6a08400acac7258d410801535d0fb928210002ab6187250420056573b0e4a084000cad761c9410800175300392821000aada1d61504200155a43ac2a084000e37855854108001c690ab0a8210003a9dc961504200565b392c2a08400acb4725854108001d48e4b0a821015fa9c8161504202bf59102c2a084057ea520585410800117f08bb6621000a2f21176cc42003e2f31aeb988402ea5c8558f31080018baeab1e62100021fe15764c42001c3e42aec98840008bf845d9310800517908bb262100123e201764c4200246e43ac6988402ca5c8558d31080099b0e0b1a62100023b61b724c4200065c3a6ec900400aeaa42dd920080018f50bbb240100031e617764802005675296ec900400acba42dd9200801597085bb240100032ed0
  | 4 => 0x3480011bf06bb2a6900023de057654d2000c7a40aeca9a400787c87595534800f4b906b2aa69010e9d2056554d200243fc3acb2924070a5c8359652480294df04b2ca4901069d205659492029c5f436e8a9240a88be87d9152480971790fb22a49002b2ed827690920056d4104ed21240008bf87596424800153f06b2c8490136a720d65909200055bc0acb212403dab481596424800117f0eb1c84900028fe1563909201f51e42ac72124000ab78158e424807b56902b1c84900f62f21971909201ee5a30ae3212400ada7215c64248015b5040b8c849014e2f21974cc92025c5fc3ec999240008bd87d9332480070fd0b3b464900021f616768c9200061e326ea99240538be86dd132480df17d0fb22649012e2f21f644c9200061fbaec89924000c3c75d9132480018b8ebb1a649012f2b1da424c92025ed4384849924070c6c76dd5324814b8d8ec3aa64900034b1d0754c92026e563b6e8992404bcac76d913248097b50e1b2264900127aa1f704c920006b5ba8e09924000d68751c13248001b56e838264900036a1d0704c9200061e322ea192400ad68205d4324800187cebb2064900030f5d7640c9200045fc22ebb0a40028bc845d761480011bf06baec29001e3720d75d85200055ac0ee9b0a4000ab5811d361480010ff0ab9ec29000e1f21573d85200045fc22e7b0a40028bc845cf614800117d0f216c290002ad60642d85200045f43885b0a4000ab58110b614800517d0dba2c2900022fa1f64585200061fbaec8b0a4000c3c75d91614800117d0e322c2900030fdd464585200061e3a8c8b0a4000c9f64dcd6148001938c9b9ac29000327d9073585200064e320e6b0a4000cd4611cd614800517d09bb2a2900022f613765452000c3e43acaa8a406ea5c8359551480034e902b2aa2900022fa1a76505200055ac0ceca0a4000cb5819d9414800147f0abb282900be8f21576505200054fc1aeca0a4059a9c835d9414800155f04bb28290002ade05765052017d1f428eca0a4000a3d851d9414800187d0a3b282900030f61476505200545e410eca0a40028bf811d9414800517b023b282900032bc84765052000656908eca0a4000cae201d94148001958403b282900032e84076505200065c880eca0a40008bf8759541480011790eb2a8290002a7e0d65505202cd4e41acaa0a4000ab781595414800356902b2a82900022fe1d63505200045e43ac6a0a4000a3f8558d414805f4790ab1a8290002ade05635052000d5a40ac6a0a4000cac768c941480af5590c99282900032b1d932505202bdd440264a0a40018de839db314800117f08bb6629000a2f21176cc5200061e322eb98a4000c3e75d93314800187aebb26629000237e1d63cc5201752e42ac798a4001ad48158f3148001958c939662900032b19172cc520024f4402e
  | 5 => 0xa2f21f41595200064fb9e82b2a40bcc9c73d05654800196ee3a0aca900072d1c741595200045ec3ccbb2240008bf87597644800153f06b2ec890002a720d65d91200055bc0acbb224000ab481597644802117b0e30ec8900028fa1461d91200051ec28c3b224000a9e83187644800153b0630ec8900032d5c461d91205dd57416ebb22404baad82dd7644800187aea3aec8900028fe1573d91200051e42ae7b224000a3e851cf644800147b0a39ec89017aaba0873d912025d56c10e7b2240008be87d4f644800117b0fa9ec89012e2fa1f52d91200045ec3ea5b224000a3f855c764480014790ab8ec8900030fe1571d91200061e42ae3b22400a8bc825c7644800147d0a38ec8900028f61471d91200054f418e3b224000a9d831c7644817555d0438ec89012eab60871d912025d5d400e3b224000ab9801c7644800117d0f28ec8900022f61e51d91200054f41ca3b224000a9d83947644800117d0e28ec8900022f61c51d91200045f43c63b2240008bd878c7644800147d0b18ec8900028f61631d91200045f43863b2240008bd870c7644800117b0f10ec8900022fa1c21d91200845ec3843b224000a3e85087644800147b0a10ec890002a7a0c21d91200054ec1843b22404baba80087644800147d0bb86c8900028f61770d91200054f41ee1b224000a9d83dc364480ad55d05b86c8900022fa1f10d91200045ec3e21b224000c5d75d4f63480010ff0ab8ec69000e1f21571d8d200052f42c63b1a40008be87d91634800187eebb22c6900030f1d76458d200065a38ec8b1a40008be87191634800187eea322c6900030f1d46458d200065a388c8b1a4000cb764dc56348001968c9b8ac6900030fdd77458d200061e3aee8b1a40008bd81dd163480010ff0aba2c69000e1f2157458d200047bc0ae8b1a40018f4815d1634800187eea3a2c6900030f1d47458d200062e3aee6b1a40028be84dc9634800117b09b92c6900022fa1c4258d200061fba884b1a40a8c3c751096348099968e2212c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900032de137158d200065a426e2b1a4000cb442dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200045f43e82b1a40028bc87d05634800187eeba0ac6902e30f1d74158d200065bb8e82b1a4001cb471d0563480019e0e3b82c6900030f9d76418d200061ebaec831a4000c3e75190634800187aea320c69014f2b5c86418d200046fc3ac631a4000a5c8558c63480015a902b18c6900022fe117694d200145e422ed29a4000a5d83d965348001c3ea7b24a6900123b2197294d2000637b2ae529a40049e8805ca534800517d09bb2a6900022f6137654d200045fc22eca9a40028bc845d95
  | 6 => 0x61f32ae32144000c3d655c6428807b96cc2b8c85100030f9d165cca200045fc32e99944000c3e655d3328800187acaba665100022fe1d64cca200043ec36ea9944000c3e64dd532880e10fd0eb2a65102961f21d654ca200061e3a2ca99440008bd86dd1328800187ccbba265100030f597744ca2026c5f43ac8994406f8bc87591328800187eeab2265100030f1d5644ca2019c3fc32ea1944000c3e645d432880290ff0eb2865100030f9d5640ca200061ebaac819440028be84dd5618800117b09baac31015ead60674586202c55bc0ae8b0c400387e85dcd61880010fb0bb9ac31000a2fa1373586200045ec26e6b0c40008bd87909618800156b03212c3100022f61c42586200055ac0884b0c400487c85dd951880090f90eb2aa31000a2fe0776506200145ec0eeca0c4057cba10dd9418800197221bb28310002ade05765062000657c12eca0c4000cb7815d941880eb878e4b2a83101630fdc565506200071bb8acaa0c400a9ae87dc94188001c5ccbb9283100032b9d8725062000656bb0e4a0c4000e2e651c9418800135b0c392831002b2b618725062005697428e4a0c400ad2d851c9418800195cca39283100034b994725062000617328e4a0c4000d2d651c94188001958ca39283100032bd8c725062000656b18e4a0c40bfcaf611c9418817f95ac2392831002b6a98072506205fed5080e4a0c40bfda9101c941880070fd0abb663100021fe1975cc6200061f322eb98c400087f8759731880010fb0eb2e63100030f9d564cc6200061ebaac998c40048dc8758d31880eb87ee8b2e43101d70f1d165c86200043ec36ea90c4000c3e64dd521880830fd0eb2a43101fa1f21d65486200061e3a2ca90c40008bd86dd1218800187ccbba243100030f59774486201ec5f43ac890c404c8bc87591218800187eeab2243100030f1d5644862002476c16e9b2a40008bf845cf654800517908b9eca9014f2b5c842d95205f717a9085b2a4000a5e8394765480014db0528eca900032d1c464595200064e326e6b2a4000c5c651cd6548001938c839aca900032d19371595200145f43ee8b2a40008bd81dd165480011bf06ba2ca9001e3720d74595200047bc0ae8b2a40018f4815d1654800117d0e3a2ca9000a1f21d54595200161e3a2a8b2a40bdc5c73551654812f8e8e2aa2ca9001e37a1f73595200064fba6e6b2a4000c9c74dcd65480018beea39aca9000327dd073595200064e3a0e6b2a40008be87109654800193ee6212ca901bf271cc42595202665a38884b2a40018f687dc5654800196ee9b8aca900032d1d371595200066bb9ee2b2a4000cd473dc5654800196f09b8aca900032d21371595200065a216e2b2a4000c77751c5654800196ee838aca900032d1d071595200066bb98e2b2a4000cd4731c5654800117d0fa0aca9
  | 7 => 0xbe84dd931c800117b09bb263900123ba0b764c72000c6e43ac698e4001ad48158d31c80510fb0dbaa43900021fa1d65487200b43e43aca90e4000c3c7459521c800187ccbba243900030f5977448720006963a0ea90e40049e8805cd21c80018dacbb92a1900021f61b754c3203643f43aca986406a87c8759530c8001878e8b2a61900030f997744c3200061eb2ee89864000c9c7458d30c80090fd0f2a2cb100030fdd254596200243e43aa8b2c40028be84dcd658800117b09b9acb100028fa1251596200051ec24a2b2c4000a5e8394565880014bb0728acb100031ddc651596200061fba4e8b2c4000a3e84dcd658800147b09b9acb1000317dce73596200043f43e86b2c400087d87d0d658800147d09b92cb100028f61372596200051fc22e4b2c4000a3c845c965880014bf06b92cb100029720d72596200053bc0ae4b2c4000a74815c965880290fd0e212cb100021f61c42596203ae1f43884b2c4075c3d87109658809747d04212cb100028f60442596200051f424e2b2c4000a3d849c565880014bd0738acb100029760e71596200063bb8ce2b2c4004a7a809c565880014f30138acb100028fa1071596200051ec20e2b2c400087e87d0565880010fb0fa0acb100030fa1f41596200061ec3e82b2c4075a3e82d0565880af47b0920acb100021fa1e31596200043ec3c62b2c4000a3e848c5658800147b0918acb100028fa1031596200051ec2062b2c4004a7a800c565880014f30018acb100028fa1221596200051ec2442b2c401487e8708565880010fb0e10acb100028fa1021596200051ec2042b2c4000a5e8308565880014bb0610acb100129ea0021596200053cc0042b2c4000c3f759d5648800147d0bb9ac9100028f61773592200064eb98e6b2440008be87d4d648800117b0fa9ac910306aee0172592200045f43ea4b2440008bd87d49648800147d0bb8ac9100028f61771592200061f42ee2b244000c3d85dc564880095750138ac910122ae602715922000557c12e2b2440c0aac825c5648800117d0f28ac9100022f61e51592200054f41ca2b244000a9d83945648800117d0e28ac9100022f61c51592200045f43c62b2440008bd878c5648800147d0b18ac9100028f61631592200045f43862b2440008bd870c5648800117d0f10ac91004e2fa1c21592200045ec3842b244000a3e85085648800147b0a10ac910002a7a0c21592200054ec1842b244004aba8008564880015730010ac91000e1fa177158e200043ec2ee2b1c400487f8759653880014bf06b2ca71000387d4d6494e200243e43acaa9c4000e2f525925288001878e8b2aa5100022f61b7454a201f61f32ee8a944000c3d65dd1528807d17d0eb22a5102a22f21d6454a200063cb2ee0a944053c3e7259642880ebc5ce4b2c85100f62fe197190a200
  | 8 => 0xc3b8242180028fa1261997200051ec24c332e400aa6e8298665c800127b0fa0ccb900123b20974597200543f43ca8b2e4000c3f7495165c80150f90eaa2cb9000b0f1d154597200145f426e6b2e40008bd84dcd65c800147d0928acb900028f61251597200052f41ca2b2e4000a5d8394565c800147d0930acb900028f612615972005537414c2b2e400ae672198565c817187eeda0acb900030fdd2745972000537c12e8b2e400aa6c825d165c800187ae83a2cb900028fa1373597200051ec26e6b2e4000a3e849cd65c800147b0939acb9000317dce735972005537414e6b2e4000a76819cd65c80014eb0339acb900021fa1f43597200043ec3e86b2e400aa6e8290d65c80014db0521acb9002a8fa1342597200551fc2284b2e400ae2c4250965c800147d0938acb900028f61271597200052f41ce2b2e4000a5d839c565c80154dd0538acb900029b60a71597200051f420e2b2e4000a3d841c565c80010fd0fa0acb900021f61f41597200061f43e82b2e4000c3d87d0565c801547d05a0acb9002a8f20b41597200043f43c62b2e400087d878c565c800147d0918acb900028f61231597200051f42062b2e4000a3d840c565c80154dd0418acb900029b60831597200051f42442b2e4000a3d8488565c800147f08b82cb900028f21170597200052fc1ae0b2e4000a5c835c165c80014ef02b82cb900029d20570597200051f42620b2e4000a3d84c4165c801587c84baec79002b0f10975d8f200045fc0ae9b1e40028bf87d0763c800117b0fa0ec7902e30f9d741d8f200061ebae83b1e4000c3e7499663c80158dce532cc7900030f9d16598f2005637392cb31e400ae4e3259663c800187ccaba4c7900030f5957498f200546f43e86b1e400387e85dc563c80010fb0bb8ac79002a1fe1d6594f200052fc1acb29e4000c6d655ca53c800517d09bb2a7900022f6137654f200543e43acaa9e4000c3c7459552c807d87ccbba2a5900030f5977454b200061f3a2cb9964000c3e655d332c800187acaba665900de1f61b754cb200b43e43aca9964000c3c7459532c8015c5884b2a65900030f997744cb200061eb2ee89964000d2c741d532c80070fd0bb9ac3900021f61773587200145f426e6b0e40008bd84dcd61c80150f90bbb2a39000a2fa1376547200045ec26eca8e400187c8759551c805f47d0b3b283900028f61676507202cd4f41ceca0e4000a9d839d941c800156b033b28390002ade05765072017d1f428eca0e4000a3d851d941c800147b0d32a83900be8fe1965507200561f392caa0e400ac3c7259541c800187ee2b2a83900038ddc565507200045f43ec6a0e40008bd87d8d41c805f47d0bb1a83900028f61763507202bd56c3464a0e400387e855db31c80010ff0cbae63900021fe1d65cc7200043ec3acb98e40028
  | 9 => 0x72584300053bc2ae4b086000a74855c9610c00156f08b92c218002ad211725843003d6a41ae4b086004af0805c9610c0014ed0a392c2180029d61472584300055b420e4b086000ab5841c9610c00f5ad06392c21805eb560c725843002579400e4b086017af1801c9610c00156d09a92c218002ad61352584300055bc22a4b086000ab484549610c0015af06a92c21801eb520d525843003d6b41c84b086000ad583909610c00156f0f212c218002ad61e425843026f4b41c84b086000e9583909610c0a756d05212c21812fa5cc2425843025f4a98484b086000a7685109610c0014eb0a212c218002ade1c42584300055ac3884b086000e3685109610c001c6b0a212c218003a9a08425843029f4b98084b086053e9530109610c0090f90bbb2a2180121f21d65544300247a43ac2a886001ab481dd9410c00196ee3bb2821802a2fa0b76504300145fc0eeca086000cb781dd9410c00517b03bb2821815f2d20776504302cd4e41aeca086000ab7815d9410c00196ee2bb282181672720d76504300545e412eca0860588bf815d9410c00196f02bb282181630fdc565504300071bb8acaa086000c9d76dcd410c00117b0c39282180030f99472504300061eb28e4a08604ccb6611c9410c0151790f312821802b2b1ca625043005657c3cc4a08600acac87989410c0b195ee33128218003a9dc662504300045fc3ac4a0860008bc87589410c001958e4b1282180032be1d62504300065643ac4a086058caf71589410c001d4ee2b12821800aada1d61504302c65b43ac2a086057cb587585410c0055690eb0a8218003a5dcd61504302cf4a39ac2a086000cb472585410c0afd2e60b0a821815fa54c161504300045fc22ed90860028bc845db210c0091db04bb642180030f1d165c84300045ec36e99086000c3e65dd3210c00187acbba6421802b2b98b74c84301ee5b30ee9908600a8be87593210c0151790eb2642180032bdd162c8430006563a2c59086000cb774587210c001968e8b0e421800e1f21776484300145e426ec90860048ec82dd9210c0091e903bb242180021fe15764843001c3e42aec90860008bf845d9210c00517908bb242180021f61b75484300061f326ea9086041c7661dd5210c0010fd0eb2a42180021f21d65484300061e3a2ca90860008bd86dd1210c00187ccbba242180030f59774484301ee5b30ee890860008be87591210c0011790eb2242180030fdd564484300061e3aac89086000c6f75989210c0018d8eb31242180032bdd26248430006563a4c490860048ec87589210c0018deeab1242180031b1d5624843000657ba2c49086000cac74589210c00199ee6b1242180031ddd561484300063a3aac29086000cb774585210c001968e8b0a421800335dcd614843003e6a39ac29086000ce962dc1210c0019e2
  | 10 => 0xb106000a6d85085620c00155d0810ac418002ab610215883003d6741842b106004aea80085620c00155d093aac418002ab612755883000557c22eab106000aac845d5620c00f59906baac418002ab607745883029d57424e8b106000a6e851d1620c0014db0a3a2c41812eaba1c745883000657438e8b106000e2e851d1620c001c5b0a3a2c418002ab604745883000717aa4a8b106000aae849c5620c00155b0938ac4180029be1571588300053642ae2b106000aaf845c5620c00155908b8ac41801eb320d715883002574402e2b106000a6e851c5620c0014db0a38ac418002aba10715883000556c20e2b106007ace831c5620c00159b0638ac418012baa00715883000574c00e2b106000aae84945620c00155b0928ac41801eb3a0e515883000566c1ca2b106000aae84145620c00155b0828ac4180029ba17415883000536c2e82b106000aae87d05620c0015590fa0ac4180038ba17415883000716c2e82b1060028bc84dd9520c00117f08bb2a41800a2f21176548300061e3a2caa9060008bd86dd1520c07d87ccbba2a4180030f59774548300065b30ee8a9060008be87591520c0011790eb22a41800317597735483000657ba4c4a906000cac74989520c0091d90eb12a4180032bdd16254830006563a2c4a906000ccf73589520c01555d04bb484180032b9c976908300545f412ed2106000cae825da420c09795b04bb4841802a2f20976908300045fc0aed210604de1e73596420c0a787ce4b2c84180038b9c965908300564fbb2e72106000e1d655ce420c015d1cc4b9c841814e2fe1d629083029e57392c52106000aaf8758a420c0a795f0eb1484180022fe1971908300061f32ae32106000c3d655c6420c01595cc4b8c84180032b58971908301ee5b30ae321060028be84dd5610c00117b09baac2180063760f75584302bc5ec3ce8b086057ab5819d1610c00f1b906ba2c218162ade0574584300145f426e4b0860008bd84dc9610c00117b0f212c218002ad60642584300545fc3884b0860008bd87109610c00156b02212c2180123da1f41584300053b42e82b086000a7585d05610c0b196d0fa0ac2180038da1741584300071ac2e82b086000ab682d05610c0b1d2e61a0ac218163a54c341584300247a43a82b086007ad483505610c00156d09baac218002ad613755843003d6b41eeab086017ad583dd5610c00156d083aac218002ad61075584300053b42ce8b086000a75859d1610c001c6d0b3a2c2180038d61674584300055b414e8b086058e97309d1610c0b1d2a613a2c218002b5e0d745843003d6a41ae8b086000cb7875d1610c001d2f06ba2c218167a520d74584300055a412e8b086057e97305d1610c0afd2a60ba2c2180038dd5254584300056bc1aa8b086007ad483551610c00156d09b92c218002ad613
  | 11 => 0xc00187ee93a2ca1800297e0d745943003d2e41ae8b286000a3e84dc9650c00147b09b92ca180028fe1172594300051e422e4b286007a5c835c9650c00f4bd07212ca180029760e42594300043f43884b28600087d87109650c00187d0e212ca180030f61c425943025d1f41084b286000a3d81109650c00147d0938aca180028f612715943003d2f41ce2b286000a5d839c5650c00147d0838aca180028f61071594300043f43e82b28600087d87d05650c00187d0fa0aca180030f61f41594300051f41682b286057a3d84905650c00147d0910aca180028f61221594300043f43842b28600087d87085650c00147d0810aca180028f610215943003d2f41842b286000a5d83085650c0094f50010aca180029e60021594300061fbaceab2060c4a9f835d5640c00f53906baac81802a2fa1f725903003d4f41ce4b2060c3a9d839c9640c00147d0a392c8180028f614725903005657390e4b2060008be87d49640c00117b0fa92c8180028fa1771590300051ec2ee2b206000c3e85dc5640c00187b0bb8ac81802a2fa0b71590306154fc1ae2b206007a9c835c5640c00117d0f28ac8180022f61e515903003d4f41ca2b206000a9d83945640c00117d0e28ac8180022f61c51590300045f43c42b2060008bd87885640c00117d0e10ac8180022f61c21590300051f42842b206000a3d85085640c00f53d0610ac818002a760c21590300255d40042b206000ab980085640c00117f08bacc41800a2f211759883002476412eb310600a8bf845d2620c0091d904ba4c418002aba13529883000556c26a5310600aaae84d0a620c01555f08a14c4180021fe15719883001c3e42ae331060008bf845c6620c00517908b8cc4180123b20971988300545f43e83310600aaae82d06620c01555905a0cc418002aba12219883000556c24433106000aae849d6620c00155b093acc418002abe11759883000556422eb310600aaae849d2620c01555f08ba4c4180038bd52549883000557424e33106000aad849c6620c0014df0ab8cc4180029b215719883000557c22e33106000aac845c6620c00155d0928cc418002ab612519883003d6741ca33106000acd83946620c00155d0828cc418002ab61051988300053742e833106000a6d85d06620c01555d0fa0cc41802aab21f41988300071742e833106000e2d85d06620c00517d0fba2c41812f2b60b74588300045ec0ee8b106000aae84d49620c00155b09a92c4180123ba1f4258830016563a484b1060048ec87509620c09717d0e212c4180029ba14425883000536c2884b106000caf74109620c09755d0e212c4180032ba1c42588300071742884b106000e2d85109620c00155b02212c4180022fa1f41588300145e43e82b106000aae82d05620c00155d0910ac418002ab61221588300053742842
  | 12 => 0x2a2f21c42d85302ac3e436eab0a600087e87d95614c001878e9b2ac2980021fa1c65585300061e3a0cab0a60028be86dd1614c0d11790dba2c2980030fd9774585300061e32ee8b0a60008be87d91614c00187eebb22c2980030f1d764585300045f438c8b0a6000c3f75191614c001878ea322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980031bd94725853000636328e4b0a6000caf641c9614c001958c8392c2980033918472585300145f426eca8a60008bd84dd9514c0070f90a3b2a2980061fa1f655453017d1f42eeca0a6000a3d85dd9414c00117d0d3b28298002ad60676505300545f414eca0a6000cb5819d9414c00147f0abb282980be8f21576505300054fc1aeca0a6000aaf825d9414c00155904bb28298002ade0576505300545f410eca0a60028bf811d9414c00517b023b2829800327cc476505300064e988eca0a6000c9e301d9414c001938603b282980be8fa1b65505300061f3b6caa0a6000c3c76d95414c00187ee3b2a82980038ddc765505300045fc3acaa0a60008bc87595414c00147d0c32a82980030f9d865505300061e3b0caa0a60008be861c9414c00187eca39282980030f19472505300045f43ec4a0a60008bd87d89414c001958e5b12829802a2f21c625053005656390c4a0a6001ab681189414c00156b0231282980032719276cc5303552f436cb98a6000e1c64197314c001c38cbb266298002a7a1a42cc53042f0e32c8598a606ce5431d95314c0d3d2863b2262980b297a1b654c5302ae2e3b6ca98a6000e5461d95314c0abab0e1b2a62981af171d8654c5300070e320ca98a606bd5870195314c0d1938edb22629800387197644c5300074a30ec898a6068d9870d91314c00153d0d212629812f271da424c5304170e32c8498a604bd9870909314c001ca8cbb0a629801276a1f704c5300145f424ed90a60008bd849db214c0010ff0abb6429800e1f21576c85300045fc22ed90a60028bc845db214c001878e9b2e42980022fa1b74c85300061fb2ee990a6000c3c65dd3214c01517d0fb26429802a2f21f64c853001c3f42eec90a600087d85dd9214c00517d09bb242980022f613764853001c3f42cec90a600087d859d9214c00517d093b242980022f612764853001c3e428ec90a60028bc841d9214c0010fd0dbaa42980030f19375485300043f43eca90a600087c87d95214c001878e9b2a42980022fa1b74485300061fb2ee890a6000c3c65dd1214c00117d0fb2242980022f21f64485300061fbaec890a6000c3c75d91214c0d98b8e7b2aa09800317d9773541300064e326e6a8260078dc835d1650c0090fd0f2a2ca180030fdd254594300243e43aa8b2860028be84dc9650c00117b09b92ca180028fa1251594300051ec24a2b286007a5e8394565
  | 13 => 0x61e42ae3b22600a8bc825c7644c0d353d0638ec8981a2a760c71d91300045f43ca3b2260008bd87947644c0d353d0728ec898002a760e51d91300045f438a3b2260008bd87147644c00117b0f18ec8980028fa1631d91300051ec2c63b2260008be87887644c00117b0f10ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec8981a6a7a0c21d91300054ec1843b226068aba80087644c0015730010ec8981a38e94350d913034c5f43e21b2260008bd87c43644c0ab8f0e1b2aa6980030f9d365d89300061f3a0cbb126000c3f655d3624c001878caba6c49806e2f61f64d893000557416c9b126000aae82193624c00117f02ba6c49800a2fe1f41d89300045ec3e83b126000aae82d07624c00159b0610ec498002ba60021d89300061f3a6cb3126000c3e74196624c00187ecaba4c4980030f19574989300061f3aec93126000c3d75d92624c00187cea324c4980030f5d464989300043f43ecab126000c3c74d95624c0018e8e3b2ac4980021fa1c65589300061e3a0cab126000c7471195624c00187ecbba2c4980030f19774589300045f43ec8b126000c3f75d91624c001878ebb22c4980032d1c764589300045f438c8b126000c3f75191624c001878ea322c4980032d1c464589300063bb2ee2b126000c7465dc5624c00196ec9b8ac4980032d19371589300061e3a6ca3126000c3c74194624c01555d05b20c49802aaba08641893000477c3ac43126000ae481588624c00117f08ba8c49800a2f21175189300043fc2ae2312600387c855c4624c00117f08b88c49800a2f21171189300545f43e82312600aaae82d04624c00117f08bb4a49800a2f21176949300145f426eca9260008bd84dd9524c00517d093b2a4980022f61276549300145e420eca926000c3c74d95524c00117d0dba2a4980030fd9774549301f61e32ee8a9260008be87d91524c0011790fb22a49802a2fa0a76909300545e414ed21260008bd819da424c00193c613b48498003270c276909300051fc2aed212603ea3c855da424c00117d0c3b484980fa8fa1b65909300061f3b6cb2126000c3c76d96424c00187ce5b2c84980038b9cb65909300045fc3acb212600a8bc87596424c00147d0c32c84980030f9d865909300061e3b0cb21260008bc865c6424c00187ecab8c84980030f195719093005674312e1192606b87e86dd5324c001878c9baa64981c3560c3754c9300043f43eca9926000c3c74d95324c18b17d0dba264980030fd97744c9300061e32ee899260008be87d91324c00187eebb2264980030f1d7644c9300061e3a6cbb0a6000c3c74197614c00117f08baec29800a2f21175d853000c6e41aebb0a6000ab581dd3614c00156b023a6c2980022fe1172d85300145e422e5b0a60008be8790b614c00117d0e216c298
  | 14 => 0xf75109618c151878ea212c3180032bdc842586300565639084b0c6000ab581109618c0a30ff0abb2a3180121f21d65546300051fc2aeca0c602fa3c855d9418c00155f04bb28318002ab20976506300055bc0aeca0c600acac621c9418c05f47d0b31283180028f61662506300045fc3ac4a0c60008bc87589418c00117f08bb6431800a2f21176c86300043fc2aec90c600387c855d9218c00117f08bb2431800a2f21176486300247643ac490c6000c3d74953654c0050ff0eaa6ca980022fe1172d95300145e422e5b2a6000a3e84947654c00147b0928eca980029760e51d95300051f410c9b2a6000a3d81193654c00147d0c216ca982a30f9d842d95300051f424c3b2a6000a3d84987654c00147d0830eca980028f61061d95300051f43683b2a60b8c3e76d07654c00187ae83a6ca980028fe1173d95300051e422e7b2a6055c5c735cf654c0ab0fd0fa1eca980021f61f43d95300051f426e5b2a6000a3d84dcb654c00147f08b96ca980028f21172d95300043f43885b2a600087d8710b654c00187d0e216ca980030f61c42d95300051ec0885b2a6000a3e849c7654c00147b0938eca980028fa1071d95300051ec20e3b2a606ca5e831c7654c0ab4bb0638eca980021fa1f41d95300043ec3e83b2a6000c3e87d07654c00187b0fa0eca980028fa0b41d95300043ec3c63b2a6000a3e848c7654c00147b0918eca980028fa1221d95300051ec2443b2a600087e87087654c0010fb0e10eca980028fa1021d95300051ec2043b2a606ca5e83087654c0014bb0610eca981569ea0021d95300053cc0043b2a6055c78705c3654c00147d09886ca980028f61310d95300061e32ee8b2a60028be87dd1654c00187eebba2ca9802a2fa0b74595300045ec0ee8b2a600087f855d1654c0011bf06ba2ca980022fa1c74595300061fba8e8b2a6000c9c74dcd654c00517d09b92ca980022f61372595300045f43884b2a600a8bc87109654c00117d0fa0aca9800a2f21f41595300043ec3cc832a600087f87590654c0014bf06b20ca980028fa0864195300051ec08c832a60c6e1e30190654c18dc3860320ca980028fa1842195300051f424c232a6000a3d84984654c0014bb07308ca980028fa1061195300051ec20c232a6000a3e86d04654c00187cedb2ec8980022f61e65d91300051f42ccbb2260008bf87597644c00147d0c32ec8980030f9d865d91300061fb2ce5b226000c3c659cb644c00187ecab8ec8980030f19571d91300051f42cc3b226000a3d85987644c03717b0e30ec8980032d5c461d91300061eba8ebb2260688be87d4f644c00117b0fa9ec8981a78794f53d91300051f42ce5b226000a3d859cb644c01595ce4396c8980022fa1f52d91300045ec3ea5b226000a3f855c7644c0014790ab8ec8980030fe1571d913000
  | 15 => 0x8bb064a800a2f211760c9500062ebaec6192a00187c855cf615400117f08b9ec2a800a2f21173d85500045fc22e5b0aa0028bc845cb61540d70fd0db9aa2a80024f613735455032c3f430e4a8aa075d2c421c951540fd0fd0fb12a2a812f0f1da42545500055ac0ceca0aa000a3f855d9415400153f06bb282a8166a720d765055000557c12eca0aa000aac825d9415400156f02bb282a815e8f219755055000596412eaa0aa0c7b37815d541540eba58a439282a80022fa1f62505500045ec3ec4a0aa000cac72d894154015958e431282a80038bd8a525055003c3e42ced98aa0008bf845db315400517908bb662a80063720d76cc5500062ebaec798aa00487c865d531540031bd0fb1a62a8006b5a07634c5500145f424ed90aa0008bd849db215400117f08bb642a800a2f21176c85500046fc1aed90aa0078dc835db21540090fd0dbae42a800a2fa1276485500045ec24ec90aa00387c851d9215400517d09b92cb980022f613725973003d2f41ca2b2e600087f855c662cc0070f90ab8cc59800e1fa1f7558b300145f43ee8b166000c3f75dd162cc001878ebba2c5980022f6077458b300043fc2ae8b16600387c855d162cc00187eea3a2c5980030f1d47458b3026c5f43884b166000c3f7510962cc151878ea212c5980022fa1f4158b300145e43e82b166000c3f75d0562cc171878eba0ac5980022fe117694b300145e422ed29660008bf845d952cc00517908bb2a5980028fe157690b301f51e42aed216606f8bf8758a42cc00147f0ab1485980fa8f2156290b300145f426e4b0e60008bd84dc961cc00156b02212c3980061f61776547300145f426eca8e60008bd84dd951cc05f47d0bbb283980028f61776507300055bc0aeca0e600acac7298941cc00117f0eb1283980022f21d62507300051fc2ac4a0e602fa3c8558941cc001958e4b1283980b297215624c73000d6a40ac498e600087f855db21cc0070f90abb643980022fe1176c87300145e422ed90e600087f855d921cc0070f90abb243980022fe1176487300145e422ec90e600487c87551658c0014bf06aa2cb1800a2fa1372596300045ec26e4b2c600ac3e425d6628c01587884bacc5182e30f9d74198a300061ebae8331460028be87dd1628c00117b03ba2c51812e2fa1c4258a300045f43e82b1460028bc87d05628c0014df04b2ca51802a1f6177654a300045fc22eca9460028bc845d9528c0011ef02bb2a5180063d2057654a300564e3b4e7214600aa9f865ce428c0a717f0eb1485180133a1c1624ca3001c3f43eeab0c6000c5e83dd5618c0018bb07baac3180030fd0775586300061ea0eeab0c600087f855d1618c0070f90aba2c3180023be09745863005476412e8b0c60028be84dc9618c00117b09b92c3180030fdd642586301f61e3ac84b0c6000c3
  | 16 => 0x458e500545f416e8b1ca000c3f52dd1639400117b03ba2c7280030f1477458e503461fa86e8b1ca068c3d50dd1639400517d09b92c7280022f6137258e500045f43884b1ca00a8bc8710963940010fd0f28ac7280030fdd25158e503652f41ca2b1ca0008be87d0563940051790fa0ac7281b297e1d6394e5035e2fc3ac729ca000e1f8458e5394001c3908b1ca728003871096394e500070fa0ac729ca00087f865ca53940ab2f70cb84a7281ab1ee197094e500069c212e129ca000d3b415c253940010fb0f29cc5280029b60a5398a5055f16214a7314a00aaae84d0a62940010fb0f28cc52800297a0e5198a5000536c14a3314a0b7e2c42946629401555905a0cc52800a2fa1f7458a5025e56c16e8b14a0008bd81dd1629409717d0e212c5280029b6144258a5000657ba084b14a04baae87109629400195d0e212c5282fb8ba144258a5000716c2884b14a000aad81109629400117d0fa0ac52800a2f21f4158a500043e43ac6a94a000a3f8458d5294001a76e9b82a5280032b9c97690a500551fc32eb214a00ac3f765d6429400117f0eb1c852802a2f21d6390a500070eb1ca7214a000b398094e42940a717f0eb1485282a24fe1d5290a500045fc22ec994a0028bc845d932940018deeb31265280032b1d2624ca50006563a2c4994a0008bf845d8329400517908bb065280021fa1e535865012d3b40ca6b0ca0028be84dc9619400117b09b92c3280021f21d52586500055ac0884b0ca000ab7815d9419400187aedbaa83280022fe1d63506500045e43ac6a0ca000e1d6394d419404b66d0329a8328002ce602535065000697a90e4a0ca00acac72989419400117f0eb1283280022f21d625065000656392c4a0ca00093c87549419400117f08bb6632800a2f21176cc65012cae41aeb98ca000c5d7558f319400117f08bb2632800a2f211764c6500246e43ac698ca000c5f7558d3194191ca8a6b0a63280022fe1176c86500145e422ed90ca000cac7458b219400117f08bb2432800a2f211764865000637bacc490ca000cac7498921940091d90eb1243280032b1d162486500052ec2e87b1aa0008bf845cb635400517908b96c6a800237e1d6318d500054e422c631aa06587e861c9535409f0fd0db8aa6a800a2fe1d74d89500045fc0ae9b12a002c3e74553625414b0ff0ea9ec4a800a2fe1f41d89500045ec3e83b12a06cc5f651cd62540011df0eb10c4a80022fe1173189500145e422e6312a06b87c865ce525400127f08b9ca4a80461f61f62949503af16216c5292a011a6d87d8a52540018db0fb14a4a80038ba13629495000716c26c5292a000e2f41d8a525409f0f90cb8ca4a812e8f61676909503af17296c5212a00487e86dd6325400517d093b264a80022f612764c95001c3e428ec992a00a87c859d8325400117f0
  | 17 => 0x1a4200cb864dc163484018f6ca382c6908031e1947058d210065db20e0b1a4200cb8641c163484070fd0fbaac6908030fd077558d210061ea0eeab1a42028be87dd1634840187eebba2c6908030f1d77458d210045fc0ee8b1a42008bd81dd163484010ff0aba2c69080e1f2157458d210047dc02e8b1a42048f8805d1634840117d0e3a2c6908030fdd47458d210061e3a8e8b1a42008be87109634840187eea212c690aa30f1d44258d2129e5c38084b1a4200c7b75dc163484018f0ebb82c6908032edd37058d210065c3a6e0b1a4200cb842dc1634840197683b82c6908032e5077058d210063dba8e0b1a4200c78751c16348401976e8382c6908032e1d07058d210066db98e0b1a4200ceb721c163484019e6e2382c69080237e1d6318d210056c402c631a42008bf845da534840517908bb4a6908029760f6594d210070fa9ec929a42028be84dd9534840117b09bb2a6908021fe157654d210045fc22eca9a42028bc845d953484011f700bb2a6908123e2017654d2103c3f43ecaa9a4200e2f52d925248401878e9b2aa4909071d1c765549212645f436e8a924200c3f65dd1524847d878cbba2a490aa22fa1f64549211ec5e43ec8a9242cca3e86d96424859787cedb2c8490adf0f9cb65909215bf17396cb21242b7c3f71d96424859587ae3b2c84908022fe1d65909215bd1f430cb21242c9c3e76196424840117f0eb1c84908028fe1563909211f51e42ac72124200abb8058e424849757100b1c84908030f9d365cc9212645e432e99924200c3f655d33248401878caba664908f62fe1f64cc9210045ec3ec99924200c74655c7324840f9a8c6b8e64909fa1fa1b754c9210061e326ea99242a587e87d9532484830f90fb2a64908030f1d3654c9212645f436e89924200c3f65dd13248401878cbba264909be2fa1f644c9211ec5e43ec89924200c3f75d913248401878ebb2264908ce1f219750c9210061e322ea192420087f87d9432484510fb0fb2864908030f9d7640c9210061ebaec81924241e6762d97214840187ce9b2cc0908030f9d065981210061fb2ae93024200c3c655d2604840187cebb24c0908030f5d764981210061f3a8c93024200c3d7519260484830f90dbaac0908021fa1f65581210061e3a6cab02420087e871956048401878e832ac09080a2fa1b74581211ec5e436e8b024200c3f65dd16048401878cbba2c0908022fa1f64581210061fbaec8b024200c3c75d91604840117d0e322c0908030fdd464581210061e3a8c8b0242bfcaf7219160484018becbb9ac0908031719773581210064fb26e6b024200c9c64dcd60484018beca39ac0908031719473581210064fb20e6b024200c9c641cd604849995ae4320c0908023ee1d60181210056c41ac030242028be87dd1639400187ca7ba2c7280030f14f7
  | 18 => 0x840517d0fba2cb9082a2fa0b74597210545e416e8b2e42008be871d165c84150f90eaa2cb9080b0f1d154597210545f43ea7b2642008bd87d4f64c841517d0e286c9908022f61c50d932155e1fb26eab1e42abc3c64dd563c84070fd0fbaac790aaf0f90b7558f2155e1e216eab1e4200c3f41dd563c840187a83baac79080a2fa1f7458f210061fbaee8b1e4200c3c75dd163c841517d05ba2c79082a2f20b7458f210043fc2ae8b1e420387c855d163c840117d0e3a2c7908030fdd47458f210061e3a8e8b1e42008bf845da53c840517908bb4a7908029760f6594f210070fa9ec929e423dcb671d9253c840f1ef0cb8ca7908032dd917194f210145f426eca9e42008bd84dd953c84010ff0abb2a7908022fe117654f210145e422eca9e420a87c8759553c855787ec9baa6590aaf0f193754cb213ae1fb22eb3064275c3c645d660c841535d05ba2c19080a2fa1f74583210545f416e8b06420a8bc82dd160c840187ae92a6ca9080a1fe1d54d95210045fc22e7b2a42028bc845cf654859547d0c216ca908030f5d074d95210051fc22e7b2a4200a3c845cf65484018bae639eca908021fa1f43d95210043ec3e87b2a420087e8710b65484510fb0e216ca90adf0fa1c42d95215be1ec3885b2a42b7a3f8110b654859747b02216ca908028fa1270d95210051ec24e1b2a4241a6d821c365484010fd0e206ca908021f61c40d95210061e32ee8b2a42d3caf72191654840517d0fba2ca908030fdd774595210045fc0ee8b2a42008bd81dd165484010ff0aba2ca908023be0974595210045f438e8b2a4200c3f751d16548401958e9b92ca908022fa1c425952169e57b9084b2a420087d8799065484010ff0eb20ca90b4a9be0964195216651fc08c832a42c9a3d8119065485a3c5c42320ca90b478b08464195216751f4308432a42d1e2f62108654859787cedb2ec8908022f61e65d91216851f42ccbb2242008bf87597644859f47d0c32ec890b270f9d865d91216661f390cbb2242ccc3f71197644859d87ae232ec8908030f5d475d91210064fb9ce7b224200a3f855cf64484014790ab9ec8908022fa1f53d91210045ec3ea7b22423d8be87d4b644840117b0fa96c8908028fa1670d91210051ec2ce1b224263aae821c3644847b55b04386c8908022fa1c50d91210045ec38a1b224200c3e74d96634840187ce832cc6908030fd957498d210061e32ae931a4200c3e75d92634840187aebb24c6908030f9d46498d210061eba8c931a42cdcad7219263484010fd0fb2ac6908030f1d36558d210043f438cab1a4200c3c74195634840187ecbba2c6908030f1977458d210045f43ec8b1a4200c3f75d916348401878ebb22c6908022fa1c6458d210061fba8c8b1a4200c3c7519163484018f6cbb82c6908031e1977058d210065db26e0b
  | 19 => 0x28fa1070597310051ec20e0b2e626ac5c731c165cc4010fd0e202cb988021f61c405973105476412e9316620aaae84d0a62cc40517d0fba2c5989372b60b7458b3126c5f438e8b1662078ee87d0962cc49b17d0e212c5988032bdd04258b3126d5743884b166200cae8710962cc401c5d0a212c5988038b6144258b316d557c0884b1662daaad8110962cc4070fd0bb82c5988021f6177058b310045fc22ed29662028bc845da52cc4834b906b2ca598803175957394b310045fc22eca9662028bc845d952cc4031b906bb2a5988030f1d16554b311f61f32ee8a966200c3d65dd152cc4018bacbb9aa5988032b9c97690b311ed4e41acb21662d9e1f8359642cc49bc3906b2c8598937879cd6590b3137e1f392cb2166200e2e7259642cc55387ee2b2c8598aa70f5c56590b3142d8e42ae72166200e1d655ce42cc4df17f0eb1485989bf2b9c96290b3152caf43eea9966200d1c741d532cc401a38ebba265989be67a1e424cb3142e8e3ac8499662028be87dd160cc41517d05ba2c19880e1fa1772583310043ec2ee4b0662028be84dc960cc40117b09b92c1988022fa1e42583310545e43c84b0662008be8710960cc4151790e212c1988063760f74d95310143fc3aa9b2a6200a5f83553654c40117f08b96ca9880a2f21172d95312664eb9885b2a62d8e1f5310b654c4011df04ba2ca9882a3b20974595310047dc02e8b2a62048f8805d1654c5af8beebb9aca9880a2fa1372595310045ec26e4b2a6200caf72109654c415958e4212ca988b317dcf6554d3158eaa29ee2a9a62008bd879d3624c40517f0eba6c498af22fe0574d89312cc5ec0ae9b12620087f855c3624c4070f90ab86c4988023be1d621893100574402c4312620ac3e425d4624c41587884ba8c4988030fd0575189310061ea0aea31262008bf845c0624c40517908b80c4988022fe1176949310145e422ed2926200a6d82d96524c4031b90cb9ca49880317d95739493100cea40ae729262028be849d9524c40117b093b2a49882a1f21d655493100c6f436e6a926200a3f855da424c47d4790abb484988f6a760f65909316b70fa9ecb212620ac9f769ce424c4155390cb9c8498a0ac721573909311edca40ae721262d599d8790b324c4592b90ab8664988b257a1f754c9310062e3b6ea9926200d5471dd5324c4018b8ec3aa6498803471d0754c931006aa388ea9926200c9c76dd1324c401a38ebba26498803651c7744c9316a4cf43c84992620ac9c76909324c505a38eb212649882ba318a424c9311eeca38c8499262019d687dc5324c401aa8ebb8a649880675207704c931006e9886e0992620087f855cb604c4070f90ab96c0988022fe1172d81310145e422e5b026200ab58110b604c4011f70eb00c098802ba20960181310045fc22e7b2e42028bc845cf65c
  | 20 => 0x5ec3ecbb02822fc3e75d97605040155904b2ec0a095e2f61f63d81410051ec2ec7b0282279b5819cb605040127f0ab96c0a08be4f21572d81412bc5ec38c5b028200a3d8518b605041595ce4316c0a08032b5c862d81410049fc2ae7302822f93c855ce605040155d0531cc0a08be4fa1672981410049ec2ce5302820acae7298a60505c1b62e3b04c0a08be4fa1f75581410061fb0eeab028200d3761dd5605045f878ebb2ac0a095e2f21d655814100556412cab028200d1f75dcd6050401a38ebb9ac0a080327d877358141006cbb0ee6b028200d1f751cd6050401a38ea39ac0a080327d9473581410064eb28e6b0282bcc9f611cd6050401b2ec239ac0a08032798073581410064e300e6b0282008be87d8d605040147b0bb1ac0a0967271cf63581412ce4e39ac6b028257ab88058d6050401a5eebb92c0a08034b1d77258141006c7b9ee4b028200d8c73dc9605040195ec3b92c0a080369d87725814100697ba8e4b028200d2c751c96050401b1ee6392c0a0803631cc725814105657c30e4b028200caf651c9605040195aca392c0a08032bd8c725814100656b18e4b028200caf611c96050401b4ec2392c0a08032b980725814100656300e4b028200c3f759896050401878eb312c0a080327dce62581410064e39cc4b02820acac7298960504af57501312c0a08028f61462581410061fba8c4b028200c3c75189605040193ee6312c0a0803271cc625814100657b90c4b02820acac721896050401a6eebb8ac0a08034d1d77158141006cbb9ee2b028200d9473dc56050401b4ee5b8ac0a0803691cb71581416fed9b8ec0b028258c3f615d46050401a6ec2ba8c0a095f0fd8175181412be1eb02ea30282008bd8798c605040187aeb318c0a0802aba0a63181410061eba8c63028200c3e75988605040187aeb310c0a08030f9d462181410061eba8c4302820acae72188605040195ae4310c0a0802ae6006218141004ddc3ac030282debb38158060504031b906ba2cb9881e1fa1e54597310061fba4a8b2e620787c8755165cc405878e8aa2cb98a5f171cd54597310145f426e4b2e62008bd84dc965cc499938e6212cb98b77171cf74597310061fba4e8b2e6207a5e839d165cc4014bb073a2cb9880297e0d745973103d2e41ae8b2e62bdc5c735d165cc40187ae83a2cb988028fa1372597310051ec26e4b2e6207a5e839c965cc4e18b8e7392cb988028fe1172597310051e422e4b2e6207a5c835c965cc54b8b8e6392cb9881e97a0e42597310052ec1c84b2e620087e8710965cc4010fb0e212cb988030fa1c42597310061ec3884b2e62dce1f7310965cc4dfc38e6212cb989368fa0842597316dd1fc0884b2e62dba3d8110965cc40f4bd07382cb989b3171ce70597310051fc22e0b2e6200a3c845c165cc40f4b906b82cb988
  | 21 => 0x85d486250415c5d0ba90c4a082b8b9d7521894105716baea43128200aad83d486250401c5ea7a90c4a08038b54f521894169d57c0ea431282d3aad81d4862505c7c5ea3a90c4a0b8f8b547521894100557406a4312820aaae82d40625040155b05a80c4a0b8b8b14b50189410545f438a031282008bd87140625041555904280c4a08038bd485018941004d7416ed29282009b581dda525040136f02bb4a4a08030f5db659494100596c16cb29282008bf865ce52504011790cb9ca4a0803475ce539494100596c14a72928241b368194e525040136b03bb2a4a08032d60776549410045f434eca92820093f855d9525040135f04bb2a4a08026de0576549410061f428eca928200c3d851d9525040187ea63b2a4a08032bd4876549410061e290eca928200cac521d9525040517f023b2a4a080a2f60476549410061fa88eca928200c3d511d95250401878a03b2a4a08024f21d65549410061e3b2caa928200b2c8259552505c366f02b2aa4a09664f21d53549410061e3b2a6a928200c3c76949525045f27d0b3b664a08024f61676cc9410061f42ced9928200c3d859db32504b395c653b664a09672b4ca76cc9410145fc0ced99282028bd819db32504b393e633b664a0803274c676cc941004dbc0aed9928200cb7815db325040127f0ab8664a08be4f21570cc941004dac0eed192820093f855da325045f2790abb464a08026de05768c94117c9f428ed192820093d851da32504b335b0e31464a082b2bdd8628c94100656bb0c519282009b581dd9325040195b05bb264a08032d607764c9410045f434ec992822f93e859d9325040127b0b3b264a08024fe15764c94117c9e42aec99282009b7815d9325040137700bb264a095e6e201764c9410145fc08ec99282028bd811d9325040193e623b264a0803274c4764c94117c9f43eea9928200c3f76dd53250401878edbaa64a0aaf0f18b754c9410061fb0eea9928200d3761dd5325040117f0cbaa64a08022f219754c9410049f438ea9928200c3f761d53250401878ec3aa64a09666ba1f624c94105557436c49928200d2c75d89325040195eec31264a08032b5d8624c941006963a8c49928200aae87189325041595d0e31264a082b8ba14624c94105716c28c49928200e2f75189325040195cea31264a08032b1d4624c941007163a8c49928200c2c75189325041595ee631264a0b372bdc4624c94166e56b88c499282cde8f31189325059bd1a6231264a08032b1c0624c941057463146499282019b4819d8325040136f02bb064a082b0f989750c9410561e312ea19282bcc3f615d43250401a6ec2ba864a080267e1d320c941014db432e219282029b4865c4325041596cc4b8864a082b2d189710c9412cecb992e21928200d95325c4325040117f0cb8064a08022f219700c9412bc
  | 22 => 0xb18c6a0bb2e5e056318d410049fc2ae431a822f93c855c8635040127f0ab80c6a08be4f2157018d4100cda40ced29a82009b7815da535040163f06b2ca6a0802cb2096594d4175d9bc0acb29a8297d3671596535040117f0cb94a6a08022f2197294d41014db432e329a82029b4865c653505d5b2ea6b8ca6a09676514d7194d41004dac0eeca9a820093d859d9535040135f04bb2a6a08026b2097654d41004dbc0aeca9a82009bb805d953504af37100bb2a6a09664fa1f6554d410061fbb6caa9a82008be86dc9535040117b0db92a6a0802ab61b52d8941056573b6a5b128200d2d75d4b625040127f0ab86c4a08be4f21570d894117e1e3aecb3128200c3d75996625041555d0532cc4a0802ab60a659894117c5fc3acb312820aaac82596625040127f0ab9cc4a08be4f215739894105656312e73128200a3e85d8e625040147b0bb1cc4a08028fa1663989410051ec2cc7312820aaae8298e62504b393ce6b1cc4a082aab209639894174ed2b8ec5312820aea4625c6625045f27d0fbaac4a08030fd8775589410069bb0eeab128200d2c75d89625040187eeb312c4a08030f1d662589410069bbaee2b128200d3475dc562505d1b4ee5b8ac4a082b8b98a751894117c9fc3aea312820ae2e625d46250401a5904ba8c4a082b0f98975189410561e312ea3128200c3f615d46250401a6ec2ba8c4a08be2f61f651894117e1f3aeca312820aaae82d94625040155b05b28c4a08030f5d6651894117e1f3aaca3128200aaf82594625041555904b28c4a082aaba08651894100556c10ca31282598bd87d8c625040147d0bb18c4a08028f617631894105557416c63128200aad82d8c625040147d0b318c4a08028f61663189410061ebacc6312820aaae8298c625040155b05318c4a08030f5d463189410064eb98c6312820aaae8218c625040155b04318c4a0b96ab61a621894173dd2c0cc431282008bf87588625040147f0ab10c4a08028f2156218941004d7c3ac4312820aaaf8658862504016590ab10c4a0b9ae9e05621894100557c3ac43128200caf875886250401c5f0ab10c4a0802ab21562189410071642ac43128200a2c855886250401c5ceab10c4a08038b5d5621894100557c1ac431282e5aaf815886250401d4f02b10c4a0802ab201621894100557c36a43128200aad86d486250401a5aeba90c4a08038b997521894100716b2ea4312820aaaf86148625040155b0c290c4a08038bd94521894100716328a4312820a8be87d4c625040117b0fa98c4a082aab20b53189410070fa9ca6312820aaae8294c625040155b05298c4a0aaf8b14a53189412655b40ca63128200ab58194c625040155f04a98c4a082aab209531894105557410a63128200aad8214c62505c9c58a4298c4a082aab61f521894100656c3ea4312820aaae
  | 23 => 0x4c8320062fbb6ea9906400c5f761d5320c80193eedba2641900333dd9524c8320547a43a82b0864028be87dd1600c80117b03ba2c0190022fa1f41580320145e43e82b006402cb874901600c8151f10ea02c0190061f61774d8d510045ec3ce9b1aa200c3d759d3635440517f0eba6c6a88030f5d574d8d510061f29ae9b1aa200c3c535d3635441517904ba6c6a88030fd4974d8d515c45fc0ae9b1aa200c3e515d36354401878a2ba6c6a88030fd4174d8d510045fc22e5b1aa2028bc845cb635441517f0e216c6a88022f61c42d8d512661eba885b1aa2f2c5d75d8e63544011bf0eb18c6a88b25761f6394d513752ec3ec729aa200c5d87d8e5354401c3d09b1ca6a8803876136394d510070e216c729aa2d7e1f41d8e53545afc3a83b1ca6a89fa1f2197294d512743e432e129aa2008bd879d3625440517f0eba6c4a88032be0974d89515c45fc0ae9b12a200a6d8510b625440195ae8216c4a8802ab61c42d895100656c3885b12a2f1e2e8510b6254401c5b0a216c4a8b8eabe0442d895171d56c0885b12a2008ef8758862545e14df0ab10c4a8802ab21162189515bf17b2884312a20a8ec825d062544010fb0f298c4a8aaf8b10a53189510555742684312a200c3c76dd152544010fd0fb1aa4a88028f61363549512743f436e0a92a200cae729da425456f47f0abb484a882a8f21975909510561e3b2eb212a20a8be87d8e425440117b0fb1c84a88f68fa1a53909510070fb1ca7212a2a893f8754a42544154790ca9484a88061f61676cc9510043fc2aed192a20187c865d6325440517d093b264a88022f612764c95100c3f436ea992a2028be849d8325440117b093b064a88061f219750c9510045fc22e5b02a2028bc845cb60544a387ecaba0c0a88023ee1d601815128d3dc2ac0302a22fc3f76d95655040195b0db92caa08032bd877259541006d3b0ee4b2a820acaf861c96550401a5d0a392caa08034bd94725954100657328e4b2a8200cac651c96550401a58ca392caa08034b14c725954100657b08e4b2a8200da7611c96550401a5ca2392caa08034b144725954100697a80e4b2a82efd3775dc56550401b4ee5b8acaa0803691cb71595414c4dbc0aebb1a822f93f875d7635040187cc6baec6a08030f18d75d8d410069bc0aebb1a8200d34815d7635040187ec2baec6a08034dd8575d8d4113cdac0ce5b1a82bcc3f615d66350401a6ec2bacc6a08bf0f9d76598d4117c5fc3acb31a8200aac8259663505ddb2ae3b1cc6a082b2be1a7298d4100657b2ce531a8200cad659ca63504b395ec7394c6a09672b58e7298d415e657b0ce531a8200da7619ca635057995ec2b94c6a080369d857298d4117c9f428e4b1a820093d851c963505dbb2ee7b8ac6a08be2f61f6518d4117e1f3aeca31a8200aac82594635040133f0e
  | 24 => 0x26400c3f65dd1524c87d878cbba2a4992a22fa1f645493226c5e43ec8a926400c5f65dcd524c81593ec73b484993928fa1b65909320061f3b6cb21264abc3e72d96424c957c5ce5b2c84990022fe1d659093255d1f430cb2126400c3e76196424c87b1790cb8c84990030fd9571909320061e32ae3212643dcb4615c6424c8e1c9ec5b2c64990030f1d365d85320061e3a0cbb0a64008bf845d7614c80517908baec299002ad60774d85320055ac08e9b0a64008be8790b614c80156b03216c2990022fa1c42d85320055ac0885b0a64008bf845c3614c80517908b86c2990021fa1f65585320061e3a6cab0a640087e87195614c801878e832ac2990030fd9774585320061e32ee8b0a64008be87d91614c80187eebb22c2990030f1d764585320045f438c8b0a6400c3f75191614c801878ea322c2990031ed9770585320063c32ee0b0a6400cbb64dc1614c801970c9b82c2990031ed9470585320063c328e0b0a6400cbb641c1614c801970c8382c2990033c18470585320056cc1821b026400ae982043604c80187ce9b2cc0990030f9d065981320061fb2ae93026400c3c655d2604c80187cebb24c0990030f5d764981320061f3a8c93026400c3d75192604c8e10f90dbaac0990021fa1f65581320061e3a6cab026400c7471d95604c8010fd0e32ac0990030f1d065581320063a388cab0264028be86dd1604c89b1790dba2c0990030fd9774581320061e32ee8b0264008be87d91604c80187eebb22c0990030f1d764581320065a38ec8b0264008be87191604c80187eea322c0990030f1d464581320065a388c8b026400c7765dc5604c8018e8cbb8ac0990032dd9371581320065a326e2b02646fcad72190604c8011f70eb00c099002bc20560181320543f43ca8b286400c3f74951650c8150f90eaa2ca1900b0f1d154594320051f424a2b286400a3d84945650c80f4bd0728aca190030fdd274594320061eba0e8b28640aa3e84d09650c81547f08a12ca190028fa1271594320051ec24e2b286407a5e839c5650c8014bb0738aca190028fa1071594320051ec20e2b28640087e87d05650c8010fb0fa0aca190030fa1f41594320061ec3e82b28640aa3e82d05650c81547905a0aca190028fa1221594320051ec2442b286400a3f845c1650c80147908b82ca1901e9720d70594320051f420e0b286400a3d841c1650c8010fd0e202ca190021f61c40594320051f42620b286400a3d84c41650c8010fd0e082ca190021f61c10594320051f42020b286400a3d84041650c80f4bd06082ca190029760c10594320553741020b286400a6d82041650c801878e8b2aa4190fb0f99774548320061eb2ee8a906400c9c74dd9320c8018bf0bbb2641900317217764c83205667296ec990640ac9e42dd9320c81593885bb2641900327d0776
  | 25 => 0x80147f08b96ca990028f21172d95320043f43885b2a643787d8710b654c95787d0e216ca992af0f61c42d95320051ec0885b2a6400a3e849c7654c80147b0938eca990028fa1071d95320051ec20e3b2a6470a5e831c7654c8014bb0638eca990031d5c471d95320043f43e83b2a640087d87d07654c80187d0fa0eca990030f61f41d953255d1f41683b2a640087d878c7654c80147d0918eca990028f61231d95320051f42443b2a6400a3d84887654c8010fd0e10eca990de1f61c21d95320051f42043b2a6400a3d84087654c8e14bd0610eca990029ea0021d95320053cc0043b2a6400a3e849c3654c80147b09386ca991c29b60870d95320043f43881b2a640087d87103654c80147d09886ca990028f61310d95320043f43821b2a640087d87043654c80147d08086ca990028f61010d95323852f41821b2a6400a5d83043654c8014dd04086ca990029b60810d95320061e32ee8b2a64028be87dd1654c80187eebba2ca990022f60774595320043fc2ae8b2a64008be871d1654c80187eea3a2ca990022fa1c42595320045f43e82b2a64028bc87d05654c8010fb0f320ca990021fe1d64195320051ec08c832a6400a3e86108654c80147d09308ca990028f61261195320052ec1cc232a6400a3e84184654c80147b08308ca990028fa1b41195320061f3b6cbb2264008bd87997644c80147d0b32ec8990022fe1d65d91320051f430cbb226400c3e76197644c9c987ce432ec8990030fd9571d91320061e32ae3b226400a3e85987644c80147b0b30ec8990da2f61c61d91320065ab88c3b226400c3d751d7644c89b53d063aec899002a760c75d91327a557410ebb22644daad821d7644c94555d05b9ec8990022fa1f53d91320045ec3ea7b22644de1e53d4f644c89b17d0fa96c8990022f61f52d913279d57416e3b22644daad82dc7644c80147f0ab8ec8990028f21571d91320061fc2ae3b226400c3c855c7644c89b53d0638ec899002a760c71d91320045f43ca3b2264008bd87947644c89b53d0728ec899002a760e51d91320045f438a3b2264008bd87147644c80117b0f18ec8990028fa1631d91320051ec2c63b2264008bd87887644c80117d0e10ec8990da2f61c21d91320051f42843b226400a3d85087644c89b53d0610ec899002aea0021d91320055cc0043b22644da9e83dc3644c80153b07b86c8990028fa1670d91320051ec2ce1b22645aaae821c3644c89b55b04386c8990022fa1c50d91320045ec38a1b2264008be87c43644c80117b0f886c8990022fa1c10d91320045ec3821b226400a3e85043644c80147b0a086c899136a7a0c10d91320054ec1821b226400aae82043644c80155b04086c8990031bd947254d3238536c16cb2926400e2f52d92524c801878e9b2aa4991c3171cf655493237c5f436e8a9
  | 26 => 0x28f21570586420061fbaae0b0c840aaae821c1619087b55b04382c3210022fa1c50586420045ec38a0b0c843dab681141619080156b02282c3211d70f18d759824229e1f312eb3048475d2e625d660908eb87ec2bacc12112f0fd81759824225e1eb02eb3048400c3d7598e609080193ae731cc121002ae60263982421ec5fc3ac33048400c3e75586609080187aeab0cc1210032d5c561982420055dc02c3304844b8bc87595609087d878eab2ac12112e2f21d63582420051fc2ac6b04844b8bc87585609080147f0ab0ac1210032ddc5615824203d2f41ca2b2e6400c3f759d564cc80f53d073aac9993daa760e75593320051fc2ae4b266400a3c855c964cc94d53f06b92c9990022fa1f52593320045ec3ea4b266400a3e85dc564cc80147b0bb8ac9990030fa1771593320061ec2ee2b266400a3e859c564cc80147b0b38ac99901ea7a0e715933240d4ec1ce2b2664008be8794564cc80117b0f28ac99901ea7a0e51593320054ec1ca2b2664008be8714564cc80117b0e28ac9990022fa1e21593321dc5f43842b2664008bd8708564cc80147d0a10ac9990028f614215933203d4f41842b266400a9d8308564cc8015750010ac999002ae60021593320051fc2ae0b266400a3c855c164cc9eb53f06b82c99901ea720d70593320051f428e0b266400a3d851c164cc80117d0e282c9990022f61c50593320045f43e20b2664008bd87c4164cc80117d0e082c9990022f61c10593320051f42820b266400a3d8504164cc80f53d06082c999002a760c10593320055741020b266400aad8204164cc80117b0dba2a5990fa2fa1d6454b325445e43ac8a96643d8bf865c642cc87b96cc2b8c859900a2fa1375587320045ec26eab0e6459ab5819d161cc97956f02ba2c3990022f61e42587320055ac0c84b0e64008bd8710961cc80156b02212c39900a2fa1370587320045ec26e0b0e640387e87dd560cc8010ff0aba2c19900e1f21574583320546e41ae8b066400c3f7590960cc87d878eb212c1990030fdd442583325461e3a884b066400c3f75d0560cc971878eba0ac1991c297a0e51d96320063ab8ca3b2c640a87c87551658c8070fd0fbaac31900317a0f75586320062ec1eeab0c64b7c3e42dd5618c96f87885baac3190030fd0775586320061ea0eeab0c640087f855d1618c8070f90aba2c31900a2fa1370586320045ec26e0b0c6400c3d74953654c8050ff0eaa6ca990028fa1251d95320051ec24a3b2a6400a5d83947654c8018eae328eca990028f60464d95320051f43085b2a6400a3e84987654c80147b0930eca990028fa1061d95320051ec20c3b2a6400a3e86d07654c97187ceda0eca990030f5d074d95320051fc22e7b2a6400a3c845cf654c8e18b8e6b9eca990021fa1f43d95320043ec3e87b2a6470e1c4350f654c
  | 27 => 0xf43e21b22a4008bd87c43645480117d0e086c8a90022f61c10d91521f51f42821b22a400a3d85043645480153d06086c8a9002a760c10d91520055741021b22a400aad82043645480196ce3b24c6a90032d9c46498d520065bb22e331aa400cb4645c663548019aec6b8cc6a901f3518d7198d520045f43ec8b1aa4008be8719163548011bf0eb18c6a90021fa1b7154d521f717b16c9292a40387c865ce525480127f08b9ca4a91c31718d739495201c3e432e3292a441c74615c6525480156b03ba6c2a9002ad60474d85520045fc22e7b0aa4028bc845cf615480117d0e216c2a9002ad60442d85520045fc22e1b0aa4028bc845c3615480117d0fb22c2a90022fa1c645855278e57b90c8b0aa402c3c7455360548d50ff0ea9ec0a900e1f61e52d81522a53d404a5b02a4becad72192605480517d0dba2c0a91022f21b74581520045f43ec8b02a400cb471d91605480117d0e322c0a90032d1c464581520064fb26e6b02a400c9c64dcd605480193ec839ac0a90032719073581520065bb26e2b02a400cb464dc560548011f70eb00c0a90fa2fe1d6598e421f61f3aacb31c8400a9f83596639080127f0ab84c7210fa4f2157098e42054ce41ae131c84e493e87dd5639080187cc7baac7212af0f18f7558e4255e1f316eab1c84abd2e62dd5639095787ec3baac7212af0fd837558e421f58e42ac729c846f8bf865ca5390957a5ca4b94a7212ae4fe157654e420549e43acaa9c840ac3c76595539081593ced31aa721003875966354e42054ce43ac6a9c84a8c3f7654d529099927d0fbaac3212df0fa1b75586420061ec36eab0c84b7c3c63dd5619096f87cc5baac3212df4b98b75586425be1fb06eab0c843d8be87995619087b56d0332ac3210f62f21d65586421f61e3aacab0c843d8be8798d619080187eeb31ac32100327dce63586421ec5e43ac6b0c8400a3f8558d61908014790ab1ac3212df0f9cb75586425be1e396eab0c84b7c3f71dd5619096fc6ee3baac3212df8dc8775586425bf1a10eeab0c8400a3e859d5619080156b033aac321002ade0575586420061eba8eab0c8400a3e871d5619080187d0e3aac3213330f9c875586426661e390eab0c84ccc3f711d56190999c6ee23aac3213338dc8475586426671a108eab0c8400a3e859cd619080147b0b39ac3210030fdd673586420064fb9ce6b0c8400ab5819cd619080147f0ab9ac3210028f21573586420055bc0ae6b0c8400c3f751cd619080117d0fa9ac3210022f61f53586420070fa9ca6b0c843d8be87d49619080117b0fa92c32102b8b94b52586421ed5b40ea4b0c8400ab581d49619080117f0ea92c3210f62f21d52586420055bc0aa4b0c843dab481549619080187eebb82c3210028fa1670586420051ec2ce0b0c8400cbb709c1619080147f0ab82c32100
  | 28 => 0x24005002000a00000a8028004005009002000c0000018004004001009801400400000980440060000000000010005003000003001c000000c006005000000800a0050060004002004000004c000066003000400003100100080140070088038002000000001400e002000000800002d00180000280010000038002002000000800000b00a001002801d001000401400100e0018010002004801c00800300000340000000180000026000003820400200000000300400000098008002001001800005400700e800000800c00000000040020168008004001001803800601a002001400c0000100010032002000800c056004006003406400d00800300180110068008020000001005000a00f002800003a002000007800001100a801c01c000000800801200100000080517d0fba2c5298022f6077458a530161e3a2a8b14a64d8be871096294c0117d0fa0ac52980a2f21f4158a530145f426e4b0ca6008bd84dc96194c0156b02212c32981e3d21d41586530145f426e4b04a6008bd84dc96094c0517f0eba6c4a98022fe0574d89530145fc3e83b12a6008bd87d076254c011df0eb10c4a98021f61e511895352d2f41ca2312a6008bf845c06254c0517908b80c4a98022fe1172d85530145e422e5b0aa6008bf845c36154c0517908b86c2a98022fe1172d81530145e422e5b02a655c3f655d06054c011f70eb00c0a982a6ba0b7458e520145f43ee8b1ca400c3e53dd16394801878a7ba2c72902a2fa0b7458e520545e416e8b1ca400c3f52dd1639480117b03ba2c7290030f1477458e520061fa86e8b1ca40087e87945639480187ee928ac7291c297a0e5158e520045f43e82b1ca4028bc87d0563948e14bf0eb1ca72900317e1d6394e520070fc22c729ca400e1c8458e5394957c3c84b1ca7292af871096394e520070fa0ac729ca4a587f865ca5394957a5884b94a7290f25be197294e5252e37c32e529ca400d2f845ca5394801a5908b94a7290034bd057294e520043fc32e129ca40087e8794d61948a987acaba4c1291028fa1b75d91520054f41cc3b22a400a9d83987645488117b0e30ec8a90032d5c461d91520064fb9ce7b22a400a3f855cf64548814790ab9ec8a90fa8fa1473d91520051ec28e7b22a4f7aae821cf645487d55b0439ec8a90028fe1571d91522051e42ae3b22a400c3f855c764548018790ab8ec8a90fa8fa1471d91520051ec28e3b22a4008be878c7645480117b0f18ec8a90fa8fa1631d91520051ec2c63b22a4008be870c7645480117b0e18ec8a90fa2fa1e21d91520045ec3c43b22a4008be87087645488117b0e10ec8a90fa8fa1421d91520054f41843b22a400a9d8308764548015750010ec8a9002ae60021d91521f51f42ee1b22a400a3d85dc3645488147d0b386c8a90028f61670d91520045
  | 29 => 0x50000000000032000800400e002002004400c009000009014000300300080140260000120000011001800c00200a001002800000f002807000001d00a80b002000d000805003c002000801000800400100480d2004006000000200d000000800e01b001800000c000011006c0060000000050002004001000000400200c8008018000000801800a02e000001000a000002000c03c01b00002a400a02000180640040000418048004001000003001200100d8018004001001800401a001000800800000100280240000130000040002004000004c00e002018000000a0040010000004000004800000800c000003800402900080480000050010050004000006805801800600480600080010008038020000001800c000000000000000200000100000000020068074008002001800800c0000018020004012005800402a00e00a000401000800d800400400203980040020020000018008007001800c00000b002805000000600080f00d602500180ac004016004800000a001006820002200f009803c02600100400380d000000000dc0000060040020004012000000005c00c000004800200001580740000000008014016002000001400600c01600100000350010150006004000000c000005002804c00201f0020000000004001825800400a007005c00a001000806c00e00000c800802400600180b400200000680240120040080028000008005000404600600c800c00a0080080000004006002001401c025000001402c00000100200b600300000000080360000014034003011800803a002007803c00000d00100c8028001004800001000100600c000000d0018008002000003803802400300d802c002010001802800800300a000001e004000001c002001004006800c0180040038002006001800000200100800240300000020040000010005801803800000200480040230098000000000004004c006003000803c00c0010018004020008004800401c0040008010030000000000000005d01000280060050190008030004005800401800100000a8008001001000800e003001800000400100000980000040008014002000005800000003500080000000000008004008004000001000a0030008044008004003000c00c03700280f0072015010800402400c00b0050016002000000000400000300c80000130058110000000001000000000900800680000150038010004001003006001c000000800800200a0008070002000000000801c000000807c0020000068004026004006001c08600000f007400a00000000000060020000000000005000000000400200400200060010008004024000000006808e001002006c00e00100000340820090090000006008004005400a00300e0034000009000004c0640010008044028007003000
  | 30 => 0xd8000d587c90003000ed8d0b0ac00016328d539890f80004d40001bd4f9ced20000000000a182f6346d32ce820002908000452543b131eca71e16580012925466b080004de0000003c45474bad1d4b27589257f33525d98d08f4666b1f5760bbb540bbfdd8a0343a0ba14000c2f5c02fb0000c9b770bd4490c4fc0132319a6c82e37004f01aa0002e50cc800037105ab85cbb20c351e11d0870cba6efa459e7eac3027aeac15266d63594215723fc3ce02203f09d802e205051cbe178c800000f00980100000030010004002000003800000000200b800002c00800300040020000060008002003003801003401900600040180000058094008000001000000c0000130010012004004812007a036000001801c0000100004030010001003c00a00d00000080140020008000000014001804402c001003004000200c00680040180070000030020015002000400801a0000014002008008801000e0010000000010001004004000c000005001c01000402a80400000000008078012000000000c01603900000a8008002003002800202700980000000030008040014003001000002c0030008008012003001801c00000e0048054000044000000800800000d8010000000000001002a003002001c00200900500100040000000000000000000803400000d012001000400100a8048014004000800c004000006002000e0310000014002000001018001200100000240020180010000016002003000401e00200f8000002000000009c05c00800a801c01200200000440280050000028002001006000000e0040010000016003003800c0200000008004054001002815c06c01d00d001c016000003801001200b00b8008022000008800000000100e000000a000000001000202d001800802c001000803800a004002805800c000004002c00e01100180d400e0000078038014000000800001a001001800800800b004002401a000000002c0000010000028010004005015800001301f8008000011000001000200701200980820050000010018003001800802a009000802003401000a002402c009000001000600002400a400e00d002001c01402a01a001c0000030008024006000013803800800c011000000600103b80040000000018000024008001002802c00c004001802801100000200c2000000000401605200080940040000168038070002000000000003400700d0000000000003c0040060028000026015000804800200f04b80040840000000018002023014800401000e003800004800200581540060040238018002000000000400400300381bc01201907280000140000068018000013000000c004000027800000000400800240000010088000004001013005c01e000014800007000f00a00000000140020000000001004800000000
  | 31 => 0x3008c2690665c043660658784d52a69013bcf1d20923510b00856ee55000192519472a0c588acc5c1a60002a5dab805f54980000000643d50000d82ae25ff80012eee2015c2158ff6bed5d210bcf22626701b64c9cc04e5d61ad9294a3f1bd955cc727e130018f0c38aab06a34892a48ad357a94090000078502acf584ca01c2438000f8700025c9c72d3b7ad80000000001a18000e6c0005330a987900002ca035c000ef3207073000000000022dc0000004559a1c5fa00000000000005f60001b8910200021700000000000000251eaa31757d00006be6fc000000000000013d000006c96700000000000005cf941467cdb942439c4a281113ac800055e1e40b12c19bd8cfa1d81b68816000000065829e000000261400056c749000178e18879800000000003cd00015dca0846f01b868af3a0001c8c0000000000000000000000000037c8f835ab158818d2c01fabedb9a417487b309b1a0003d80000aa4ab2565ae35654a850000000e1667c50700010740002ac1f6c0001b700014dc00000007a15d06880000299105d140001463bdc000c1d00000016fc9de35ca4353c676f04e21ad0eacd9269a2e084e0000000794e2400054f3a009d67dc447b5e8c0200027f80155ccaf93910d390623b920fbc0c60600037a00000000fa13f09dc000000000140987e00000032a508c6ab639368c0000000000001c800002268a1c9b4c9f62eabbd9820003ab094d362d9a599947c0ba8412d03c6d0a08aa18515bccec77d18f20dc4b018109712c5a70f7e13a951c74469d4bc368840a37948909a4ac60292482b45a468db33225e43eade90bc036475ead64291fb43e0a436cb0e342302ba3183c20b30d394b12bc0c1a69b2302dad37ee4854caf48506d2622e355119c0c92da8559b7ed891260b6ccca32a0762d3cc94be923c30a52180006bba4249923c545c9ccca8ab78367a3acc3e69632c24fccc616d3b1a55439eaa00bdbc482920006d881350460005a08e600007834549489c8cec65f700014b20002aa8050600a3d4511c2594e53c0d78a793883155fe26a59545400001208f3ac4e3629bf5e1ea0411500017e2f6e42f849dabc1d3266ab843ce13b000000114c7b8000275021e67b6eb800120e24d2371a3528444f03600000082a700000005c8cae30daef49a00001b72b8cd220002602a3132e84d541891c4b21d030aba60000000704bde93a6bc92da000000000047b0274e90f0d0003228450ea300a99e15543800003ba1cf0d2958a1b6d4f8b851168000c48a7a13997197d0974445a00945415d472bdedaac00066880000007a3017800192cd3c0001529adc9cc1099dacbda00000032313c43e90ae0539370eb3000303ca3a9340001748226000612838565037e0fe8efc3f4c9461837dca96dc20000000f3e0004d5162db4eb452f
  | 32 => 0xf929b973a04a0859695bfc5150cabb698500924d330642ea2d11a48ac8608788348312c8280f86601f68e5a36a18d80017f02f827380008e29ba601b349e5c646347bd9c7b400000012d54e255d2fc9c54b52b7478f38c84f6f455c4a0a4000000620a5600007445d7a7a000052924e31b1c1600000000002904a45ce00000000005869cc0f32c233448be4180cab626957cbe007920481812085750002b6d1ee4d15723180e9234f7c6b53419c53d0001c69972f18050000000069200033c0ce894b7b7940c7023dc48a86b1ac6f4c173815460432f75c12582bc48a4fd2e20ae0a36512800090e4071d097b9a0c0ba5668000000f6d256a3c5b5400000000c979c8cd50907a506410d68909e19c4a7514f800005c8dc4468b7577eb774831614000f280f63d50b5aab85b980010544c53c21638e48000417ba4dbe854c6331b344e4c7800025bc0009df3e60000620000000010120271b0000aad01e1443178a8c91839d47daf595129190220001a50ac15c58ae4faed4403e1864c8698434e3af1cb647057ebc691ded6b2bdaf6590a9736378ba875839f2f3068844adea207b8fcd7652e022b52c2faec4557b6946fadf50de8c489d8e57796288ccfcc6d298acb4ac815a0b30ff9a029a2305192ca56c620001fe80009af43d3d256b8f14059a7386287822392f4db3e47e67fb36c27250f3f8889dc385be282051c706075716bc88f44423323836cda225f0002c3172879b0c30000000d1a1f93a11322000103000000007a0000000000a964e037a12703776e498459602c01553068bc6cf40002ec90ae0000001a9da0866008315884ca000000000059800013300000000000488749e6ce3b6198f0c0002a11908000000cc42ce9055938e362cd80005840000a5a70867ae182a11da9d100002e58000f8a8613312cbcef01b80d00fe946a2bb2471f400000000bd372888c69760a1a552800005121de401e0114229215a3c00037821f53487900aab5c428079600007f1cfa0001ad2ad0dba52f43bb8213608da47f83d800000036aa56800060e0d29d6db1e06612e812deb23fd56d1a2800001e4da863c28cca61fa2fd9ee4c9922ab5cce3edd937b908159cd5a03b3ac8f1ac58288a01da74a1918c1bfda004103e894c1eac2d56e58000000a2258009042f26a2111ac3d9c0000000000041ae7273438e8626ddb00035483d6f1363d00019ee3763f930ec8e69a327710dc7b080a3bdbcc9cf80da24894489f61241eea804384f410d53854658e1e679359c00000071a08e8632a2c1a513093040005900001e622a4254076d1906664c3bdd912637c11d81a546e06f40fa5515fc56d4f8850d0da7ff1af1fd003842d5db067400083b5678320f860000003d3c0000f5523071d0d41c36ae9260578a5c000034509236d6a88ea0000ac90000e29b
  | 33 => 0x500a916290dd580a5ab36c18490f25f4688bb31020793352382929e2ac608a661d44d33031080cd8818d36b35993680f33029841970eae3752648fee0df4e5b1c562a39b000357d92ed1541e1e9922e69e32694e4004f4d2140505616b3c462b4707961df327254dc2cdb26e039ecd42b1f149a254646f8b3a52220e0e6820a1296c000000000000000000000000008922b630d2f6dcd800000003f54ce1a90003d1c4705253a10c0477a1f4715925c99c3d56102c99a926bf3ad3cdcd969130e21efc00045309500017b4cf369ea1a13f0000777a7f89c891a41a9bbd96e3722cb0859b6ce250119ce8aec0a81f09431534ca027d32fd0cebd06282cfc20452a67c0001b8ac830000f04da8f6100003ed496ebe6fb03ade422100000dcc648a7866f1cf9d9c0001c935c0a6aae057400013c00000ce3520fd4f900001dc582c7f653014e13b4b173dd80009d45cd51a060d77289e76a9f8dea00e72849601e6a00000030f4dd20006f111b5222b6700026200009223730a5de0043438a25c46a885d56a2538e32a2845f88e52f65336a600015feea108bac858f811a4c30001b2a0004db800080abde00010ecfc48f300000410806774f793d10346b35e888316be9c91cb14fd766896000119156020441b2ea85c00004258800b860000000d4c00027000000000000000000001948a540f1b79c8380002ed000055000002622cc18400000035f137c0005f51e606b07d5310b3980000000abaa2858c2c84af07b424480533814d8000e4d49f000046433603b8da1efef1760938a57f6aae0e50b8400c9e94619f34dfc96937434289d20006b43a51a1e5e96ea11a1ebe28b00924c00008277600b704f20004c6800118430d0002249cf4f5200000004c27b5443b32da12d2f305a8bcffa9467788000000a1117d8000000c0d63f25f10362ef3b0ad54a1c2f34e518f4168d403fe000141403100000000000002858ba01d08e62f2345133274f4ae24dd5e84540003248cbc41961c8475426ed6341b989250eed2fe05fde54c676c308f017cb512660c25b5824a3d6bd745c4bb15890ed80000004fc800000000064798ac20ebd52fb85dc43063163b116933e2e57218000df24b703f000026c3f52f788708f8a09659a35c502000458ba31efa9f000030999948b6000022517aed079180000004f04591b7986c3d761d0b4c0e8184421a239d344321fdb5a55808d200024d96d4e9f000286cc76d7e72cb671a4a0b8000285478000000038400000000001cb800000074180019fc78c0f78001bac13d00535f476e00000000010a800008f388813e5920002de536cc5443a344ceb87065e402345386883379894b425567322e413780566ca30910e6ad71e71ab826aec261092f437e8a105e91bd02410e7543a34bf04893a9a7b93202f706284f95e20000
  | 34 => 0x4323de539a3d409a2d4c000d7f52600000009d25a326f50fc661390137d3a24a93660cd4e1c1b13cab38c36adce000041555a8a84601b01baa6290390acd6b00dd4920141290e043e1034d82a0ef3eb10d95e63292eaad80000b810001d3000036c645a81dc1a82503d80016e40000000b108942866371b187e06754d9889055a11071514c8db82c77880b1509ce454a610107d80b275db8842be3f64be8e64468d50784ac4d49c82d55233acdc293167b3799bb4c8600007ec1945d10b40000c74000397a6383b4b6c0001f1d70e0006039dfc00049e3f499315ce99c130398cb3c28470f93540002a0205000049c59372b1fcc47a1294072e55b1ce132b922906a0ec12de1f50a00c5b3f3a3f84240005af12e0298a534ca0fb4f2ef465c504299580000001f750720001d904e800065f00000015eae761bf8001d600000001045440abd000000000000077600016c24350000991bbcb8347389087464e33b4b648f6e5774121e1c1dab16000085023e2635dab56c5da43904ab950d4a62d071b5e08881333d71418aa2d4a0b7240958e4670002c0c0b60000cbb3d4000cb4036a5d5c786276a29e9c72ab9b0002c6000031f0680f95c6200d19118a19c26551793e3db3c0006c11974000a0f3e300016807b2000000010c0001772f3d868d6a1b8000000000063a0000a5a5c81ff909000000043b0c3900800040b0000cb20003820cc40003d215ea75c000382038095dc1c5bf47185b19423db166994c3280070003221a8c6ce471267594ad2d000190995a00047900000000007338089802000562a57c00091e54a0001740f39470800000022e033944c3228ea45d0001d383332351cf0fd64f65612f31c666fb6628e2591a6364278b69d62c5522cb70d1c0aea7c006c888aabb740b594cd8a44683b6918868530663a748000a7369aaf95ec202152b20043c2461a5a85944c1703813a5de04ea403420b131470f329234099ee0c22b9634cdcb356d0bcf99788033bb2d31336685644adfd9aa2fa1adab10b4eb2b59ca9f53f8eb43039d547200000000000f40edd1a338697b03e6041b241022b6e7649bc497ef830e0b8657d639a45e2fc80fa8217a010e9f12a496f915c4b2ea5f1cf2fd446a4f124a9374ce4b316ce9e05278a477701700d842222069469c9e76e1a698d17468947092e383680350328b58346e2f6f7150c4bc0f16b6a9a825a5d61041cfd7faa0d41024e58ae34c1618e514281a878aae11aaece45df2b74ba83913f31af4c8a2896d7922c00050a6e78459536ec75973dd5356f6a12181440c2f5a14780002c0ee21229705a680177c502b52c0d9109800008beb4840c04a00f0ee758d1dcd10adab0b99690c40c2d1a0abad97630746b024d7943e3431a51d6949456ac29046c44e50003325c50eb65080cfc29433452b2c88
  | 35 => 0xc00092a13884e000048f582851400000054a95f040276d5c89c295b01b33b41ed11a6b543a01d80f0a10323d23502cadeb5c3249583cbe00150465704507185910140c6093d987216f66b72a78d9010a3372923a987ce32d21095e85043cd14d061414693d3192a882ecf865288001d86ab163bbb51a4ed642aa24d53e6a5d50fa41502a0e2154867ccfe7af0d3ae694bcc51695973c8a20803fc9784c103572420001a3e5786dd0eb427ebc4361ae792100006b91c74e582eb0001bcc0002ae0c8226d5049103faaf9ccb40007478535a40b0772f00f00008fa53903780a825b1eb0d580001fe42da91487ee0700025657500ea3c7b5e56ae0b97c8a7a8bfa10c0002668000dd20002f50ad075d43780000000002dc086d4947d9110b0dd25cb090000a51e4e00012486380007276743c18f4af2b0000ad54c29f253134380006a80000000000b7d00031ed5240005ee22c11da9ec4e33718e2e4816b6000000001d513804d0ca2e344fb0e015e0003a91714000000000353913a3d049d8b60dd6d8c20c011c1fceb90000000000dfa0e6a9ed3767be00000000009032d800000000002d6000000000041e89b00002983010000000f48556000000089800037fc0007fe00016200003f377e31fcc82041668000043235d0002000982000000318d06642a3768001120f7375ba4ad6ea00004b1535aea29252b8ac1780c310b4aa012426690180dbd8208ae3c731c13b8ce93a80311306855005a8e576ee601bc1dd10c41044fa1cd17323633a6995c7d41d87732f04a58ad35948000ba0b5d1fc3844f24eea5f21569530bae0840358e563a6658ab7da6e9c74bf061c670d050f5311923623724e95e45bc89c1d99058bba06325db278b847646a0abb5a043650dc8c98a20f6975a96a016c2d71681f2d318e7960318dcd927720929b94716e6d0000fac01c6224d41250ebeaa51e3a03596acce766bcd04529ff35888389de34704cb6293ee44c4381a3117c7ca000000146225c729102000030f04c1f90eca6145d31e0098c41e41a388cfca7e047737f54b4c757b1135834249260d85f169c4fe7b5bd3806e2670ba0690414bc258089a8e003e85be148cbd03a722d94859e286c729a8c0000df90f8800000000045a07817520090001c4484c9204f227140000006ee9f602003e20991580000e140b8980ce6400023b8565d7400000028edc3a0003c50001b10b302e200000000003a2800000000000028315d246600034a9e7600042e3ab45fe1d614403fd2ca8300001a6800000054327d4dd80003681ce58d2a4f4992fc1bf86f60003944000c6470080000365837238000b6e1147579018ccee493d48958134b8c43738d47681c6340acc9ca03c64ab1a98422ca23f73a44392b6579e96308c2b63045b2a1088ee46d30750522b4276d8000336081
  | 36 => 0xc68e80004620000000d45ac08603d22cdc1088c439d88cc9b60000003da000000030f00019ce0002c500016c84990003b646906e37be00001448cc6d9b318f5623f651bb5c00000012800000002620000001b5000049680000000004489c20f62b3d72729c16b64cb62fb371ceeb97460aee97eeab60000ce9ccadf143fa49c3dc4a1067a5c042ef1f7a12f154560004d395248feb1b5d138c0d3e1c067713a19d8a4069f2a2c1dc00000039a9cdc8f0234a3f4148ee31e617603a291d000000071800078e00002580005b119a09400003de00007be1cb77d800145c8a0000233c47c5280000001bca00039b8001018dfb5240000000e660000c813aa89a00023a1ed821d0003af40000006f00000000c0c0000000d7405e0002e600004a273f96655b255968c0a1407c4be2ef0a596de5ba00cb37db163a54eb36d1252f8507310cc946dbc4a1a3e415c7580e2a800afa00000006255f81bc434bbb808c12b351b721a9e33b68b09557e600041581a9c0000054691789264ae6399ae0d16c5c1d5130c792b7050b9380bf4cf90002a2197c0002f512e875cb1d3470001f185eb05600016ccc5a000000178600000003490b2d996f0b3bd2c687c0003c1c8f2a6d474963c46c8ac3a7131d816d766329584d3038f6e3b11c3d000005812e4bea7466420000d0cb2400013b4000a3e4578eac0004030000001c1edf035927ec00000000012cd3429dd0f99dc16a48e46e617f8eaee867c7360508451c2a080000d6ab75de3b3c00000024680000009d01c3ac4063800008900014c80394288c94c7c00044b8001c8400000030200001ab30c04540000000000afcd780003641b28fa609e7b0021d550000000345c0000003b32ff9214ad00ef2accb725505319b9c0006544528de9eee0007031fe00560000000095238b5a3cf0001050f745da32600002447ab800153845667294f8000cda6438969b7000000011f53820e40000000b6c62379000007e2000024b0880000003dc8470860a520c10001e02cc7463800189ef296da800135816f4a08854be60002ae3e093d6c61000276c0000002419cd405824f53f20207a24010000000fd86484ad96b8efc20b6fc31094068862e6378d894e3855a8eecd68efd60f9b7cb0465c40e0000000458400b0f800076772e81cc000995110000000022c00003f1dec3552e4a2edb0ad2107c800016e35c000110818c05a7b828e0412dad6a100003b844877d07fd9f630513584c4c1e26867e1ef4fa4e2e164a5adc7caa34d93aa45a48992f91ab554c7a10002d0cb22bef1ecb09d2a083f1dc16cc0000000000bd052acd32a2156c7883305d287391ba7106c21f3cb12a3200033740001980b220781427f036ba72143c000000273d81431a604bd9903af6425a07dcb5e5f100002ed35a3a41780298b202fe218b65
  | 37 => 0xad5bcbf91ac945c0000c72edac080000b1453bbc199e42b0a90dd0f129a05548f28988b38212ac39eb873801016541d2b2c5d0a79d4ec8c9550bd8d66c21a31f9771d3cb4759f20259a802833ea935a6039302910a54d8c0e686b320b084f73b13be42a836b5842e3cd604b24bd1478bce7296a9bc99b20747616255cea846c18b14608eab0a3203c75d2a81317630a908ee9b739a815386e8b712381488e048389858de1c8f55dc3aa88ec15b4411a4d57461327122d564ec53582112c4dc3ee1d8a795dd60f2769acedeb059f0b5a1687785010001910afc47b53f93d51be00077f2e48a2cb763af0799cea2a20003984c0c000792abdc0005d300000845a80000000bf1c983270c527d8000ac8547a3b04f827f1c30001bdee5a0000001f0201f0002624000725129282c0000007af029400012332db164000d6200038b128800000012d92c893a2f03b2c3b203342523f0cf205914eb4c93fa67320eade8de47a838e00018309e60900cac8ba5263f7b86c00039c00000000005867a98a40000c82799b89db0e0976ec2545e5aacc02b8ce5692cd80002d109f0d9b2090d9c00000001e80317f4c9523137047ee0900000c3011487b4d29c34000000000000094cb1c6202874000726386304c00097f000000044c0000000000000000000000185c6d95728c18bc4a5841f00ec2ce3081182d34c66b1e0668b0574e4f96d8118cc2c9e10001521c82f0500032d9646ad54f68000b446d23ef054c7c8cea7c400012284226a18000000cd65eb800000000019e39d03aae9666600b5b6e52016fb114e022483a18fbc65cabf0120c75016450548064889c72824d000123e42c772ac9435c8d11b4a28c56200000009f4000a6f000168d108c3c4eca62c0007e83552229e189816d009b400043c2a71958000be2165119400053b74cb9c0b54c175f314e8df017200016ec0008177bc25a824241a3c58ca008653434a301125ef0b3e080010442d903fafd12dcbcd0002e583c41f906e397d29af845a81e186c2000201307000049b501258482677a20da9a0e420bc4030000000d3531613600000180388b996e203a257820996495d00013cde5e1b65421dd4d8eec8547143468492c59d0001df018057c3bd1e2cc2b5b42af0000ef2072af8c31824b335b7b435a4a73400ed53267c800038f45146fa0cf29d178ce446e8396079e96d0c9bab0ae69335f2b0c97264fd2e7000000000000000012d0d2e6b7ac44000000576000057cda96aaada4f74d59000335cfbef246dda42db5c397103bbd5a4877c31c0000cf40f075faf2c000caf117ba94e06a3300000009580000000000f8088948c2bc80026844d70000bcac352b487d958c617107af7cbae88030211ad118ed1252800ce0a0e024fb9bceee1b06842065e8600000b0a649ae1dd12a18d4784ed
  | 38 => 0x28697ba2e92d89464000d193770001372a650808000b3421f221b7cd0f012f33889d848015006c3ce10b00002b30000d409261dd213000000048004dc960e8e2643b2800000024426781ee00072595a9a06e4a15a0944bfed3f21e80000003401c22b294f200000033b5c6e3be2938001d4000000039acb38d3100035d16b256704db1218bc3856ee2954b8e716000000197aa2928d8000000ede3e23898b4c08e64d360cf281090003a1de083a0686351dd4e0001f018a9af60000000021d120000001384000a9d3a8a9cd4ee87100018759fa0006df12ad9263f959a37104e88721c700002fc71854fb9f98f288308daa9c9e474b755a59992216a7a5823c3343d341c15940004dc50e16c86a42f646c2d59ee25814b6232c1545530003ba5e94058569194418204276c1af859c55e39eb9a53001d742f137824cc6a34cb239bc8000327983059e1ba7a200000004aa32823640008264c7a1995b81613db00002a228d6409b905e24d972e0f780002f56e8b6005360bf1888001ba6edf2c392f07103602b700696da56b6de977cb7ac44661ad2d45ad100dda9
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x127c566e66367e5e00300000001eb6000000a00072780000000000aa8086948e26002e547a000e0060008200002a004c000000761a0000004e00003c0000a85c3400909e000044a48a0a00000000008cae00002cb23a52a200740032000c10925802046a9c5a8462b4963eb0a69a481c06186824985046ac4008884a2822162042706c14643802020300020a1d0100080004040000010a01000e00010505010100090f3100607a0f74945639480103f985d0745943200507a4e515d3635441522c9261363549510050ba5a851c9655040142e95d8472595410050ba5a511c9655040150e9394472595410050ba58511c9655040142e9298d75d8d414d44da63615d76350401926712096594d410560ba097598c625040122c9560863189410060be1f85588625040122c989d562189410048b26175588625040182f875d562189410042b65f86d48625040122d98d9452189410048b66065148625040142d97d4f521894155c8be6153d48625040182d87d4850189410542ba4b865ce525040103d98d4c76549410060b1d882595525040142c955d8628c9410050b2557618932504014a8905d8624c9417250ba567518932505c942f981d4624c9417250b660751893250401c0f311d4624c941007034c475189325040142c955c862d814100523249651cd605040141d951807358141006071cd85d8d60504150ac9859472581410050b657631c960504014a89058c72581410050b657611c9605040142d9518072581410560b1c985189605040103d981d462581410060761473189605040182d75a0a63181410040fe61741d165cc45d05c9760e4259731006071cd841c165cc50b21c985957390b3100607a0f749456394001a0c42a0e5198a500548ba4b8458d52940150ae92e1d63506503ad0b65b521c941940150ae92e1176cc6500060b2147258941cc001435911d365189300050d64474194624c001495910c2769093000525644301d9414c18dc1870190654c5300040f65e8498665c800103f985d074597200548b24984dcd65c800103d989d26598f200050ba56761c941880158aa6061872506207150be62651c941881c542d9899472506207150ba54651c9418800142e95d8c72506200040f6627519063480014a591080765052000728485101d941480018a8801d932505200050b255761c941080016a1901c96150420174172617558f3108015aa28258541480200040fe61741d365440150b4976044258d10056291c981109634400103d989d06518d100040f66274197624400122d9819442d89100048b660651086244001a276560442189100067021d324c520440016c0964c93148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc3021c964c93148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x4
  | 8 => 0x124d
  | 9 => 0x124e
  | 10 => 0x3
  | 11 => 0x8a
  | 12 => 0x8d
  | 13 => 0x8e
  | 14 => 0x150d
  | 15 => 0x98a
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x128a
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0x150a
  | 22 => 0x150e
  | 23 => 0xca
  | 24 => 0xcd
  | 25 => 0xce
  | 26 => 0x9ca
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12ca
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0x168a
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xa4a
  | 36 => 0xa4d
  | 37 => 0x134a
  | 38 => 0x134d
  | 39 => 0xb0d
  | 40 => 0xb0e
  | 41 => 0x154d
  | 42 => 0x154e
  | 43 => 0xb4d
  | 44 => 0xb4e
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0xb8e
  | 48 => 0xbcd
  | 49 => 0x3ca
  | 50 => 0x3cd
  | 51 => 0x3ce
  | 52 => 0x15cd
  | 53 => 0xcca
  | 54 => 0xccd
  | 55 => 0xcce
  | 56 => 0x15ca
  | 57 => 0x15ce
  | 58 => 0x170a
  | 59 => 0x170d
  | 60 => 0x170e
  | 61 => 0x160a
  | 62 => 0x160e
  | 63 => 0xd4a
  | 64 => 0xd4d
  | 65 => 0x164a
  | 66 => 0x164d
  | 67 => 0xeca
  | 68 => 0xecd
  | 69 => 0x17ca
  | 70 => 0x17cd
  | 71 => 0x98955
  | 72 => 0x128955
  | 73 => 0xb4955
  | 74 => 0xb4956
  | 75 => 0x1609
  | 76 => 0x40a
  | 77 => 0x160c
  | 78 => 0x14a
  | 79 => 0x2c9
  | 80 => 0x198a
  | 81 => 0x14c9
  | 82 => 0x99255
  | 83 => 0x409
  | 84 => 0xd49
  | 85 => 0x17c9
  | 86 => 0x98095
  | 87 => 0xb89
  | 88 => 0x1849
  | 89 => 0xb8c
  | 90 => 0xcd515
  | 91 => 0x150995
  | 92 => 0xb0995
  | 93 => 0x154995
  | 94 => 0x995d5
  | 95 => 0xcc995
  | 96 => 0x15c995
  | 97 => 0x98cd5
  | 98 => 0x151295
  | 99 => 0xb1515
  | 100 => 0x15d515
  | 101 => 0x1a09
  | 102 => 0xb49d5
  | 103 => 0x16c9d5
  | 104 => 0x1789
  | 105 => 0x130c
  | 106 => 0x14c
  | 107 => 0x5c9
  | 108 => 0x134c
  | 109 => 0xb5695
  | 110 => 0xbcc
  | 111 => 0x40c
  | 112 => 0x164c
  | 113 => 0xbca55
  | 114 => 0xa4bd5
  | 115 => 0x138e
  | 116 => 0x198d
  | 117 => 0xa4b
  | 118 => 0x164a55
  | 119 => 0xa5655
  | 120 => 0xeca55
  | 121 => 0xa4ed5
  | 122 => 0x161352
  | 123 => 0xd5355
  | 124 => 0x17d355
  | 125 => 0x154b15
  | 126 => 0x44a
  | 127 => 0x1a0a
  | 128 => 0xccb55
  | 129 => 0x170b55
  | 130 => 0x160b56
  | 131 => 0x1a4a
  | 132 => 0xcd6d5
  | 133 => 0x1616d6
  | 134 => 0x10a
  | 135 => 0x4d
  | 136 => 0x180a
  | 137 => 0xa0a
  | 138 => 0x130a
  | 139 => 0x138d
  | 140 => 0x20d
  | 141 => 0x188a
  | 142 => 0xd0a
  | 143 => 0x140d
  | 144 => 0x5ca
  | 145 => 0x58a
  | 146 => 0x24d
  | 147 => 0x178a
  | 148 => 0x18ca
  | 149 => 0xe8a
  | 150 => 0x144d
  | 151 => 0x104a
  | 152 => 0x19cd
  | 153 => 0x194a
  | 154 => 0x1a8a
  | 155 => 0x14cd
  | 156 => 0x74a
  | 157 => 0xd4bd5
  | 158 => 0x20e
  | 159 => 0x140e
  | 160 => 0x17cbd5
  | 161 => 0x144e
  | 162 => 0xcc3d5
  | 163 => 0x15ccd5
  | 164 => 0xd4cd5
  | 165 => 0x44c
  | 166 => 0x1715d5
  | 167 => 0x1a0d
  | 168 => 0x40e
  | 169 => 0xed612
  | 170 => 0x1a4d
  | 171 => 0x17cb
  | 172 => 0x164d55
  | 173 => 0xd5655
  | 174 => 0xecd55
  | 175 => 0xd4ed5
  | 176 => 0x17d655
  | 177 => 0x19cc
  | 178 => 0x95295
  | 179 => 0x94995
  | 180 => 0x128412
  | 181 => 0x135612
  | 182 => 0x134412
  | 183 => 0x14cb
  | 184 => 0x184e
  | 185 => 0x10c
  | 186 => 0x99555
  | 187 => 0x98455
  | 188 => 0x184c
  | 189 => 0x104c
  | 190 => 0x40996
  | 191 => 0x41292
  | 192 => 0x128215
  | 193 => 0x129515
  | 194 => 0xd455
  | 195 => 0xccd5
  | 196 => 0xda55
  | 197 => 0x589
  | 198 => 0x585d1
  | 199 => 0xa59d5
  | 200 => 0x94b56
  | 201 => 0x44412
  | 202 => 0x165612
  | 203 => 0x164412
  | 204 => 0x2cb
  | 205 => 0x40cd2
  | 206 => 0x45612
  | 207 => 0x161652
  | 208 => 0x160452
  | 209 => 0x40452
  | 210 => 0x45892
  | 211 => 0x41a12
  | 212 => 0xb5715
  | 213 => 0xb4cd5
  | 214 => 0xb5616
  | 215 => 0x1a57d2
  | 216 => 0x40b56
  | 217 => 0x16d616
  | 218 => 0xcc412
  | 219 => 0xec412
  | 220 => 0x416d6
  | 221 => 0x1a8c
  | 222 => 0x5255
  | 223 => 0x139255
  | 224 => 0x138955
  | 225 => 0xd59d5
  | 226 => 0x198b
  | 227 => 0x1a0412
  | 228 => 0x5cb
  | 229 => 0x40d12
  | 230 => 0x21555
  | 231 => 0x20b15
  | 232 => 0x155415
  | 233 => 0x140b15
  | 234 => 0xb4b96
  | 235 => 0x17d9d5
  | 236 => 0x256d5
  | 237 => 0x16d455
  | 238 => 0x144b55
  | 239 => 0x19d4d5
  | 240 => 0x45652
  | 241 => 0x41416
  | 242 => 0x1a4ed2
  | 243 => 0xcc215
  | 244 => 0xcd655
  | 245 => 0x1712d5
  | 246 => 0x170ed5
  | 247 => 0xd55d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2324
  | 6 => 7727
  | 5 => 3986
  | 4 => 92
  | 3 => 1
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (95276+((h/774+packedAt gbK7 (85988+(h % 774)*12) 12) % 4081)*13) 13
  | 6 => packedAt gbK6 (406946+((h/2575+packedAt gbK6 (370896+(h % 2575)*14) 14) % 14933)*14) 14
  | 5 => packedAt gbK5 (252438+((h/1328+packedAt gbK5 (235174+(h % 1328)*13) 13) % 4784)*13) 13
  | 4 => packedAt gbK4 (6680+((h/30+packedAt gbK4 (6440+(h % 30)*8) 8) % 134)*8) 8
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff07c07ffe07ffe0ffffe01fc0cf467c39f3f3
  | 1 => 0x3ff800781ff83fff0f00ffffc733b98e263c9f
  | 2 => 0xc1ffff801fffc0fff000ffe0383cc1f3c7cf1c
  | 3 => 0x1ffffffe00000ffffff00003fc0fe03f80fe0
  | 4 => 0x1ffffffffffff00000000003fff0003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x52014012260251201152204a8045023408d131
  | 1 => 0x2528042908c82a490a044a950312188a222486
  | 2 => 0x8052d880131480b2a00a95409828c150c54b18
  | 3 => 0x19cad4d404008dcccac01812d80ec03700ec0
  | 4 => 0x31e736779de73c080830060637ff0003bfb000
  | 5 => 0x380038060186301080c018183efff7ec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36847
namespace PEqualNP.Outside.L_meta_36847
open PEqualNP.Outside.L_meta_36847.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := (concat bs1_3_0 bs1_3_32)
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
theorem bs1_4_160 : Interval s1Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat (concat bs1_4_0 (concat bs1_4_32 bs1_4_64)) (concat bs1_4_96 (concat bs1_4_128 bs1_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 6 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 13 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 17 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 bs4_4_224))) (concat (concat (concat bs4_4_256 bs4_4_288) (concat bs4_4_320 bs4_4_352)) (concat (concat bs4_4_384 bs4_4_416) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)))))
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
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 92 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_3968 : Interval gbAtlas 5 3968 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3986 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)))))) (concat (concat (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)))) (concat (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))))) (concat (concat (concat (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072)) (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200))) (concat (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328)) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)))) (concat (concat (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)) (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712))) (concat (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840)) (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 bgb_5_3968)))))))
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
theorem bgb_6_7712 : Interval gbAtlas 6 7712 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7727 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672))) (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800)) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928))))) (concat (concat (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152))) (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)))))) (concat (concat (concat (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112))) (concat (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368)))) (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592))) (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848))))) (concat (concat (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072))) (concat (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328)))) (concat (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584))) (concat (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)) (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 bgb_6_3840))))))) (concat (concat (concat (concat (concat (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936)) (concat (concat bgb_6_3968 bgb_6_4000) (concat bgb_6_4032 bgb_6_4064))) (concat (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320)))) (concat (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544))) (concat (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672)) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800))))) (concat (concat (concat (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)) (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 bgb_6_5024))) (concat (concat (concat bgb_6_5056 bgb_6_5088) (concat bgb_6_5120 bgb_6_5152)) (concat (concat bgb_6_5184 bgb_6_5216) (concat bgb_6_5248 bgb_6_5280)))) (concat (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat (concat bgb_6_5408 bgb_6_5440) (concat bgb_6_5472 bgb_6_5504))) (concat (concat (concat bgb_6_5536 bgb_6_5568) (concat bgb_6_5600 bgb_6_5632)) (concat (concat bgb_6_5664 bgb_6_5696) (concat bgb_6_5728 bgb_6_5760)))))) (concat (concat (concat (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984))) (concat (concat (concat bgb_6_6016 bgb_6_6048) (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240)))) (concat (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))) (concat (concat (concat bgb_6_6496 bgb_6_6528) (concat bgb_6_6560 bgb_6_6592)) (concat (concat bgb_6_6624 bgb_6_6656) (concat bgb_6_6688 bgb_6_6720))))) (concat (concat (concat (concat bgb_6_6752 (concat bgb_6_6784 bgb_6_6816)) (concat (concat bgb_6_6848 bgb_6_6880) (concat bgb_6_6912 bgb_6_6944))) (concat (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072)) (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200)))) (concat (concat (concat (concat bgb_6_7232 bgb_6_7264) (concat bgb_6_7296 bgb_6_7328)) (concat (concat bgb_6_7360 bgb_6_7392) (concat bgb_6_7424 bgb_6_7456))) (concat (concat (concat bgb_6_7488 bgb_6_7520) (concat bgb_6_7552 bgb_6_7584)) (concat (concat bgb_6_7616 bgb_6_7648) (concat bgb_6_7680 bgb_6_7712))))))))
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
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2324 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))))) (concat (concat (concat (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)) (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 (concat bgb_7_1664 bgb_7_1696))))) (concat (concat (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824)) (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984)))) (concat (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144))) (concat (concat bgb_7_2176 bgb_7_2208) (concat bgb_7_2240 (concat bgb_7_2272 bgb_7_2304)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8fee8eee8fae8eac8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276678376 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36847.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.and,[2,6]⟩,⟨.or,[1,3]⟩,⟨.or,[5,7]⟩,⟨.and,[0,2]⟩,⟨.or,[0,7]⟩,⟨.and,[1,3]⟩,⟨.or,[10,12]⟩,⟨.and,[8,11]⟩,⟨.and,[9,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36847

open PEqualNP.Outside.L_meta_36847 in
theorem PEqualNP.Outside.L_meta_36847 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
