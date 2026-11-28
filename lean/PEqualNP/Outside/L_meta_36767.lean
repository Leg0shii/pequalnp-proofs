import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36767.Model
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


end PEqualNP.Outside.L_meta_36767.Model

namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
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

def SBf (j : Nat) : Nat := [4, 4, 5, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36767

namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
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
  | 2 => 0xfff00fffe01fffc07c0fff81ffe07ff0139e7c
  | 3 => 0xffff01fffe03ffffff01ffe07ff81fffce38f
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1210a08422420490105162a288a8a215452cb5
  | 2 => 0xa4aa694a51d4a90aae0ab591556455a0d2965c
  | 3 => 0x88c94a529491b22a4ea81954465511ca98c30a
  | 4 => 0xce8d8d9d191923b3773cd061879e78831f03e0
  | 5 => 0xf0e0e1e1e1e3c3c7bcf1e79e418610c1ff800
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0ccc0ccc0cc00ccc0ccc0ccc0cc00ccc0ccc0ccc0cc00ccc0ccc0ccc0cc00ccc0ccc0ccc0cc00ccc0ccc0ccc0cc00ccc0ccc0ccc0cc00ccc0ccc0ccc0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36767
namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
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
  | 2 => 0xf807ffffe01fe03ffc0fc0ffffe07c07f27e67
  | 3 => 0x7f01fffe0003ffff000fe07ff8007fc6387
  | 4 => 0xfff8001fffffffc07fffff0007fffff81f83f8
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x830104222424404085149164868853224acab
  | 2 => 0x5552a98c51d48969360ad0ab95a46855525665
  | 3 => 0x46a4cad69491d5b25eb828ccc6dd20a79c6386
  | 4 => 0x64c68d1919191923672cb281071672c11b0350
  | 5 => 0x87070e1e1e1e1e3c7bcf3cf1e41843061ff800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaa0a0aaaaa000aaaaa0a0aaaaa000aaaaa0a0aaaaa000aaaaa0a0aaaaa000aaaaa0a0aaaaa000aaaaa0a0aaaaa000aaaaa0a0aaaaa000aaaaa0a0aaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36767
namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
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
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 1 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36767
namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x20d800008d0000840033a40229000138038646130c9001f2e94018220118b002848f1c480160a9800d02514220e80f002a00a00008505c001004003ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe817d53d03baa7a05754f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53102faa6206fd0c40dea18817e52102faa4206f90840de210817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87986f50f30bf296617d52cc2fca3985f54730bfaa4617e548c2faa9185f15230bea9c61bf438c3bc87186f50e30eea1c619d438c2fca5185f54a30ef19461dc328c2fca3185f54630ef18c61dc318c2fca11877cc230fd984617f544c2fca8985f55130be2a261bf434c37a86985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c37e86187790c30dea1861dd430c33a86185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc65907b4cb20bf28e417d51c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20dfa1a41bd43483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20dfa1841bd43082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43ec63887d4c710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10dfa1a21bd43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec62887d4c510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c530437e86086f50c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x75150af8a2a17d14542ba28a857f5050af8a0a15f95042bf29885de5310abca6215f54c42eea98855d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65de434cb7a86997750d32cea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea96837e50d06faa1a0df55241bf29c837d539077e8720ef50e41bf294837d529077c8520ef10a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41dea1a837f52507dea4a0dbd4941be29283ec52506d8a4a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31ef21e63bd43cc7ba8798e750f31bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c77a8718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c77e8698f790d31dea1a63dd434c73a8698dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf290637d520c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c43bf438877a8710df54a21f7a1443ec42887dc6510fb4ca21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43bf434877a8690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610efd0c21dea18437e52087de8410fb10821f719043ed32086fca210fdd0421fa20843f631087ea6210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a07794f40af29
  | 2 => 0x540c9dd3ce6f4ab8793fa688b39b021e8d00a09915a2c06201b0f0054c70b90b05a0a214200008c5a00015c73cd68ec4266181d1ed1f8138002a8000a9528a8d4fa0006f81700a5cc431f91f25e07a8851caaa4b4a3a53400121800056000000003c8000381ba234718d41d12ec818c8aaf4bc004000a320a000001b72c28dc00000000724759992f47f0200c71168494f15d440a60d600c1f4784109c441a4849812a1de9a84511b3b49ad050653ea720a91c03562f0238000004d05aa71290ab45c0003d8930478e10000a51ea584666d0d205b124a3d148060127ac000dc06e0b8000885061554a8000009a0ba000016234e50e33244c89fa36280840892350008540d1e506439c3a08102c528aa8ac3e29001e227128191498004c09b93103e0006cce287f1fe91c4016d460a7d3f2040c68e4b58a6528319118004701584f060500118c420f372918819fb01e4e00015c4182ec0021d4889e12e2b04d2a054317210e29c67a000101c89b07736c1c4ee1591061f81c2634927cc000a13528ec521b23c457d01000402260900f01aa9140007d5120004b26c1ec6a8001db4363d1530e60020303e0f8160280c210001c800008000005a03004018040206e0180c088122103a00000070000900402006028000a0180d802000ba0001a038060003203800008040281a020020d0060001801008008120000001076000000403207800028280c802018000200c0200e0200001006058020980a010060b000000041384c0002400006038380082c000002e01c00000150020200a000060f03a00000008100585c0100c000020b802020520100604834000001a8000a80e0d8200183c04844070000100003002010000001c000040a830000000280800806010000c0180a02000008000020500a000180302c00000000080200601010008060100401002018180380c02042010041380003006018001380c028060b008118360281c000000900e000277e52d0efaa5a1df94743bea8e877e50d0efaa1a1efd4b43df29687bd52d0f78a5a1efd4743df28e87bd51d0f78a3a1efd4343df28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542fba8a857
  | 3 => 0x3490193929c49d189d049077865a173f02ac000bf000000000272f8904000005581f0c3800000000f906c548060f0189096400c1800362ad80000033e37459800204868038c9000238001a3000000e905d0004513d80020e4ec4813d464670bd9d9428210250a515e610ab0d004000094256092568c6947282a44f81930e6000188bd45ea114ea3e43c1a53b0003cc51466a881046686d1330ea498ba9fe3d0864c79a648471c1b16428c3f8001064ce750858ce1b61411500000052ca180033a490b015e35c0001e94945c4b88828b39a8acbbaab4a01ec27a7a538108369f73d208914299214a1d5ba052d4000f191534e705131174944d45b0c31c05c0000000062dd110001805f8001f4000494000003ae314000004be000000b1000488d01b532800008a9b3a60000024f0ae2692ba0b026000a682f2a2134068e900894c9580a37c1989621c3d4938308002f219c000f82180006f0000000004600000035c0022d1980002a2b923800000000316168168000000d40e2ba1a82a8002ae520001392b147e2f8b78a80006ec8715013807c8f0004e8320ca8c23021648b11304a954000003705fc000ba066ad40028a00027c9883b568000de0d92a6a9c7695b2d8a30b322407e594218100a482031101194a841401d29866d2d26f44a358750344300c09499e0009e40025b13600159000398844e727743e24c000000000012a05c2306bcaa0765667600000000070cc290d4c29913299840e345550001644bc0006b1e61a10b0000003c53a8a01128840000029e104fb0d81c8694001bf00496551962000000b1a96058a387e80032c9cc130c127844400297098038b70483de7b8cb8a90007fc2985f2b06012900000092d331230003a0eb0001e434ce582a25a1e8770394123dd368a2320a155127c12e1bc370453429fc842821229755c1c20244649f13a1c43ec2220e0d4934c10004e0274ef8002fa0000f2a0458178c602412a8f0289fa2120000011d26e5c48218a23e001490000007
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xe548823e6494e208f592538823e6414e208f59053882766114e209d584538831f5350e20c714d438823d63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e65151208f58c544831f54d4d20c7153534831f64d4d20c7193534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d208f990534823d6414d2097994534831f5414d20c7150534831e6414d20c7590534834d6214d208f997434823c65d0d20c7d4f434831c53d0d208f995434823c6550d20c7d4d434831c5350d20d314e324826c654c920e350d32482e8604c920cdd53514833454d4520d5d4f514835453d4520cdd0f514833543d4520cdd5051483345414520d5d4c51483545314520cdd0c51483354314520d98c851483653214520d9146204825e63150209758c540827661150209d584540823e6494c208f592530823e6414c208f590530826e6214c209d98453082756114c20c794d430831d5350c208fd91510823c6454420d954421082e960084209bd9520082e461480209ed95200825e63153109758c54c423e6494f108f59253c426e6294f109b58a53c423e6414f108f59053c431e5350f10c754d43c423e64d4b108f59352c425e63d4b109758f52c4395434c7109b98b548426d62d52109798e548425d63952108f992538423d6494e108f990538423d6414e109b988538426d6214e10c7d4d438431c5350e108f993528423d64d4a10d9d48218423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c544431f54d4d10c7153534431f64d4d10c7193534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d1097994534431f5414d10c7150534431e6414d10c759053443556114d108f997434423c65d0d10c7d4f434431c53d0d108f995434423c6550d10c7d4d434431c5350d10cbd53524432c54d4910d3d4f524434c53d4910cbd0f524432d43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524432f4314910cb50c5244354538c510d914a3144274654c510e550d3144364524c510bc181314436452841109798c540425d63150109b988540426d62150108f992530423d6494c108f990530423d6414c109b988530426d6214c109d984530431e5350c10c754d430423f64548108f191520423e64148108f590520425e63148109758c52042756508410d954821042f160084109e59610042776544010b9189100427b6544010
  | 1 => 0x863d6414f21c794d43c871d5350f21b558c41c8795434c7219798c548865d63152218f992538863d6494e218f990538863d6414e21c794d438871d5350e21b358c428878d434ca218f58f544863e64951219bd89544867761551219798c544865d63151218f994544869d6315121c798c544863d6315121c758c544861d63151218f992534863d6494d219b58a53486756194d218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f997434863c65d0d218f995434863c6550d21c794d434871d5350d21cd153214872c54885219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219e98053086796014c21c794d430871d5350c219b59442086cd6310821b9584420866d658c821b9586320878d434c8219d59441086d56310421b958841087a442104219d59631086e5628c421e550d31086e562884219bd9521086ac64484219dd9521086b46448421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121086e76348421b958d21087a74348421e950d21086e460484218fd91500863c645402197d8d500865c6354021c799153d031d53d0f40c794d43d031d5350e40a758c429029d6310640a758f409031f5350d40c714d43502b86050d40c754f43102b960d0c409dd8552102746154840a758c421032d52108409bd89511026c6254440a758c41103355110440a758f401023f65500409ed95401031f6550e30c7195438c39b6050e30e6181438c23f6454a308f191528c31d4354a309dd85528c2746154a30a7590328c23f64546308f191518c31d43546309bd89518c26c6254630a7590318c29d64cc2309758e544c26f62551309b189544c27761551309d185544c26e62d50309b58b540c27661d50309d587540c23d6595030c798e540c23f63550308f58d540c23e64150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c25d6590c30a7592430c2d96090c308fd95430c31e5450c30a7d95430c31f6550c30cb952520c32d5494830e350e520c32f4394830cb50e520c31d4354830cb951520c32d5454830e350d520c32f4354830d390d520c32d4354830d350d520c30d4354830d354a320c29d640c830cd952510c3355494430e550e510c3665294430d954a510c3374394430cd50e510c31d4354430cd951510c3355454430e550d510c3665254430d9549510c3374354430d590d510c3354354430d550d510c3154354430d5546310c29d640c430c750e500c29d64cc030e650e300c25f654c0309ed95300c39b434c0309798c54c825d63153208f99253c823d6494f209d98653c82756194f208f99053c823d6414f20c794d43c831d5350f20e350d32c827661d52209d587548825e63952209758
  | 2 => 0x202400018010180500000034010080601c04008000140b0081c0040000c0400804084050000000c0f0104a0040400c00000020800101404004000100600c0a00c010040000000014040080302c050140200001008040280b010080101301000014019dd8552d0e746154b439bd8951d0e6c6254743add8552d0eb46154b43cb54852d0eaf6254743ab18951d0f355114743ce54050d0e9d62d4d43a75875350e9e60d4d43add855250eb46154943aed815250eb86054943cb5485250eaf6254543ab1895150ebb6054543ae1815150f355114543abd895050eac6254143add855050eb46154143ce5405050e3f6550c4397d954310f1e5450c43c754f43d0b1e5350e42c754d4390a5f63542429718d5090b1f5350d42ab1894350b3743d4542cd50f5150b374314542cd50c5150b674214542cd9085150b1e6454c42c754f4310aad62d0c42c794d4310b1d53d08428fd954210b1d5350842ad1854210a6f6550842b91854210a7661d53329d58754ccb1e63953329d98454cca756115332c795143cca9f6550f32c7d9543ccb365494732cd55251ccb954394732cdd0e51ccb354394732c750d51ccb365454732cd55151ccb954354732cdd0d51ccb564354732cd50d51ccb554354732c550d51ccb1d4394332b9987328ca3f64546328f191518ca3f64542328f191508ca7761551329d185544ca7b60551329e181544ca9d6490d3297195434cb1f6550d32c7195434cb8f6250d32e3189434cb8d43cc932b9987324cb1d43d4532c750c504ca3d65950328f990540ca5e63150328f992530ca3d6494c328f597430ca3f6550c32c794d430cb1d54cc83297d95320cb1d544c8329bd95320cb1d53d0f41c794d439071d5350e41a758c429065f63542419718d509071f5350d41ad185435072f43d4941cb50f525072f4314941cb50c525076452d0541cb14a415071e6454c41c754f43106b561d0c41c794d431071d5390841a758c421071d5310841c754f411063f6550441c754d41106ac62504419dd9541106e462504419b98b54cc66d62d5331c798e54cc66e62153319b58854cc71e5450f31a7d9543cc71f6550f31cb95252cc72d5494b31e350e52cc72f4394b31cb50e52cc71d4354b31cb95152cc72d5454b31e350d52cc72f4354b31d390d52cc72d4354b31d350d52cc70d4354b31c750e50cc63f6454a318f191528c6e662cc6318fd91508c63c64542319bd89544c66c62551319ed81544c6786055131a7592434c65c6550d31c7d95434c71c6550d31e5d85434c7946150d31c750f524c79543cc531b998b314c71d43141318f596540c63e64150319798c540c63e6494c318f592530c63d65d0c318fd95430c71e5350c31c7553310c65f654c431c7551310c677654c4319798c54c865d63153218f99253c863d6494f218f99053c
  | 3 => 0x139000000f10002f600131809270000fc8484ac000252711567c80012939e000000001001f4000e40003f889800246978ee8850006cc00020000270b59cc0289441803d1bc7a5250553ca000c80020000000019a0000007e8a81f46dc000001b02e5142053c24f839008000950000000000009e800000000312330361d49a8004642e90984b0005b00022c058139350ac350895040ea0000010819548e90c961c138e528a885825e800580c8374828921fd0822982b15a29e1ec6ca0f396324a31b22646e4000003143b04409e0000000000000051cf018d2d424000237380614f20000c8000c40003a0258001f12e68ed299503ea02c9680c2aa4fc4212702c3a43a1ca0224ec4082b4681a00c05f29c47c9e19434c9a1059c40b474c8d2240207b41899d3e659c942312160d05e97526c4e80516943c66c0022b0ec9b45a8001f00006880011c0000000000093ce1a09268100da9720465b863a0445e6c4b08e04520dc028000506886b80039a0000018f2a679c00192000260000420a04746d197378000eb00004c60c370bf0005e8698cc0002f8000002cc0003f000428175311493126601f0000000f0002504c0410a580000076cff800000464000890000a800000000000000000000000003622c4842a000404340b7912000000368bc2ec930c6000000905118922ac550001010000000003a064094fc1bb000804711840267541fa150004c12208200077d320ed48a7d0c59441a83c041a353a4018ed0211402ec3f95840e30c8180038a0002997c0b6285110a72e01809580115c470d69fc0d64b80004f000000001a434a39d1f00013e2291ea6121e001249fa000000c7240422250de8390000012c8704e0000e11ee236000018690007788f1110a224c7c80035e274001e3000818000000380000006116e000000000003bc0008b2c6000b88b100011800000000000c89e61442c90b87c28a8b498a1d230834cf1370761990b26509875cbc0e82e83988024800000007159478290df8d62908d84d21b3b8424c08042b626c4315f4dc948ea0913d807c2498720a6a8519821542bd26a4200067c00133132000a60000000013300043e4507a01d000504001c63567d8378772fe408138ca00099c269b80003343c8a90001102c8571be50d070970003dc1781e21c9551500036c0b4670c416c354000b81e26c00021a00000402000070000600c3a00000008000040003c06028060081a0600b02021098020000c000020181400006000000300100005008000000006c000480801c0c000010980301800014000080200008034000300a004040000401c020000100000008010040a000020180300c0100c090180a0040103402014000b8080080a0101d00c03010000000200023000130180300401000240040003400044010700800000000
  | 4 => 0xa90e52442cd061d94388b8628cf21811ca681705c494478650004288680d4748c12d2460003b91c25d1f8960001d10004806926c44e1149519c000000be8b44068e48a9e8032318528431e603cd000035c000f78e110e3fc00165000000bf1f7000000000004d6588df0713b0000000001d62308403800069cf5800000574000524de0484aa2000000000000000000002191b60007d9800d8938880002d01e8b010624c7f92e1070e61e0d180044201cbc8000000011fa1244c1a8148c000000134800000000da0c10c6234cb1c900092ca10cb0000007b0001845901a9a100038c6ea5b0666a4d615c332500e715e0000010c1c82da1708ba5f3d464c568671ea7ec0d0dc0483c80a9862ae088bb85e4ae7c
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1680800409001a1900128003801310800006070a9b801d921700001e80230d20899b00000000210025078322859d010193a38f1a9f20028e98a41e0006a197960000141f8b8c0c8e08049011958a000b00088f82150d8514a491000000000022199c9c18010c0614003020000024280890a040800400280220ca5247154852d0e92392a228e8725dc562d4d4391ee4b0ea6a1d24715485250e94382a429287491c95114543a60e0a88a2a1d28725405050e9838aa028287491c94314542c1aa6b1686214a47158b4310b0aa98c2a1085a150e61cc932a48e2a18a4a0e15535874310652392c3a18838354c6250441d0a873166298d0d7294d434868ab8ca6a1a43071d95350d21a30e0a9a8690d15731532148686b98a910a43291d1618c821b0ae62108210e856310841086523a2c518843235cc644842192ae63224210ca6749912108662b98c890843615cc6448421d0ce63224210ca5731912108742b98c890843215cc6448421948e8b1a4210ce07058d21086523b68690843291d94348421d0ac6a1a4210e0d63548421029238aa4210818558d5110440a48e4a88822061543d85528c306a1ec4a8c61c150d5294430e0a87292a21870543549510c28ab8ca6a1e41455c45350e20c1ac8b10a69050c7550d324830632a8699241a250c604c920e0a86990a290560704c8514820eb98c8a8841491d15108420a1ae529a878850d7214d438420eb9cc9a9421499d35208610c2ac8b08a6885147550d314430a32a8698a21c150c524c510d2286302628866052181314420eb98c8a9021491d15208410
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x18b010493800051861400a01807c05531c562d0c42c05531c961d0c418848758d4348421a808058d4348421c05631c55210840c05631c95110440a088550c604c920d01431c13214520905831d15108420905839d35208610a108550c604c510e0143148604c510905831d15208410
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (756+((h/14+packedAt s3K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s3K5 (21203+((h/233+packedAt s3K5 (18873+(h % 233)*10) 10) % 839)*11) 11
  | 4 => packedAt s3K4 (25868+((h/208+packedAt s3K4 (23788+(h % 208)*10) 10) % 827)*11) 11
  | 3 => packedAt s3K3 (3850+((h/25+packedAt s3K3 (3675+(h % 25)*7) 7) % 100)*8) 8
  | 2 => packedAt s3K2 (800+((h/4+packedAt s3K2 (780+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3ffff03ffffff81fffff07ffc1ffff9e3f1ff
  | 1 => 0xfc0ffffc07f07ffe0f83ff87ffe1e03e9c7e67
  | 2 => 0xfff03ffff8007ffff003fff87ffe003f1f8f87
  | 4 => 0x3fffffff81fffffc00007fffffc7e00ff8
  | 5 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x98208118912010005284b0088c02298821b0ab
  | 1 => 0x296312287244a49605a15485352142928c5665
  | 2 => 0x50c5a45120e9492ab04269505a540525168b86
  | 4 => 0x628a3882448c0dcd29680c4463999607c00d50
  | 5 => 0x830c30e3870e71f1ce738e6603111807fb6000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaea8080eaeae8e8eaea8080eaeae8e8eaea8080eaeae8e8eaea8080eaeae8e8eaea8080eaeae8e8eaea8080eaeae8e8eaea8080eaeae8e8eaea8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36767
namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x68018000000a003098e0064d80000079100400000aa4a06440011f380138024580002e740014801400000069e008c480000002642005800e1000300004254000015000000080000400010100020000007ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe817e52d02faa5a05f94740bea8e817d54902fca7205f54e40dfa1c81bd43902fca5205f54a40df21481bc42902fca3205f54640df20c81bc41902fca1206fd0240fda04817f53502f8a6a06fd0d40dea1a817f52503dea4a05bd4940be29281ec52502d8a4a05fd4540be28a81fb405037c80a05f95040bf29881de53102bca6205f54c40eea98815d531037e86206f50c40bf290817d521037c84206f10840bf288817d511037c82206f10440bf28081bf40103f480206f50040fca00817f54cc2fca9986f953309f2a6617d54cc37aa9984f55330be2a661bf43cc3bc87986f50f30eea1e619d43cc2fca5987b94b30b7296617d52cc3daa5985b54b30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7186fd0e30dea1c617e528c2faa5185f94630bea8c61de318c3b863185f94230ef98461fb308c2fea8985f95130beaa2617c544c37e86987790d30dea1a61dd434c33a86985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c37e86186f50c30bf290617d520c2fca2185f54430ef18861dc310c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7906fd0f20dea1e417e51c82faa3907ed0320fc20641fa30c83f261905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7106fd0e20dea1c417d52883de85107b10a20f719441ed32882fca3105f54620f710c41ec21882fca1107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41bf434837a86905fd4520be28a41fb20483dc40905fd5020bf2a0417d54082f8a8105fd4c20bf298417d53082f8a6106fd0c20dea18417e52083de84107b10820f719041ed32082fca2105f54420f710841ec21082fca0107ed0020fc20041fa30083f260107bc8020fd10041ed20083f240107a48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43f641887e08310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10dfa1a21bd43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443f460887e4c110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c530437e86086f50c10bfa90217e52042faa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf5050bf6a0a15ed4142be28285f85050af0a0a15f95042bf29885de5310abca6215f54c42eea98855d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3995f54732bf28665fa50ccaf4a1995f54332fca86657950ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65de434cb7a86997750d32cea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41ef29e835e53d06faa7a0f754f41aea9e83bf43d077a87a0df94b41bea96837e50d06faa1a0df55241bf29c837d539077e8720ef50e41bf294837d529077c8520ef10a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41dea1a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31dea1e637e52cc6faa598df94331bea86637f548c6fca918df55231be2a4637d538c77e8718f790e31dea1c63dd438c73a8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131dfa1a63bd434c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863bf430c7bc8618ef50c31eea18639d430c6fca418fb94831b7290637d520c7daa418db54831ef19063dc320c6fca218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fb8cb21f6996437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710efd0e21dea1c437d52886fca310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21efa9a435f53486fca690df54d21be29a43dc53486b8a690efd0d21dea1a43ee32487da6490fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610efd0c21dea18437e52086fca210fbc8421fb10843ed21087ea4210df94021bea80437e53d02faa7a06fd0f40dea1
  | 2 => 0x309e588bd9f6010001358e60e836ce89c80f20fcfe21900092ca501b27e000001950fe848000004a6100000000006e9200da000000078450000dc000000004801e0000009604a8de000000000000001604698700089c9e8000860012325d0007a9528750389cc0000000031d1714e47a7500019a00079c6315635c948c4020000000000000a0658f7a310003d01e9024b2000cc27c3a02902685c3a621c799b2308048001290d60004f00024cae0002b20004743b2050900011c22d1767100004100008546000192000000001aa460000001d24840000000071c8604c000000b9a6247c00096800000544001e6512380002ac000000ec8dc15a251400243440e4601dd00020d0b07a13493c2d000014030001ff3480015195f55c950ac0ae130ac000122000a0400000000a685b000256000010002667e01780000000019800000000160001c40003d8000003a80018929a0012d80045497c0000000032d1980006a7883e1092924e91a80048aa29380c134aad07c14121e1c06b92c3500000702900254d5d00000000200400805006008028010100140000700001c000000020440280d00601800000000000018000000080080500c000000000000440000701a000010110000240180200a01c00000002000028000020040000001200001801000004010030060000100202a004030030000080180300802003001002000000050000040000402e02c0000400a0000b0000000340000100001000001000018040030020000080000401c048020000000000300000c038010000080000001a00c0300200000002003000000010010040440100000c000008020020040000100200405000008004000010060000000300200807800000018000050020100001a000000058000080100300000a0180000301c0040000c00a0080b00101400000806004014020020240000380000400001004000000010000120140000700202001808010008010000037e52d0efaa5a1df94743bea8e877e50d0efaa1a1efd4b43df29687bd52d0f78a5a1efd4743df28e87bd51d0f78a3a1efd4343df28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542be28a857
  | 3 => 0x80d4d46f8b02a713a42cea8904564e00000031a000001b40000003c26552e000b5846056000001122a88ec129b1000a54001142500011b90a448000d600023e2300000044c8a0df80000086d558540002889c80000025c6680034c23c000001da0000007305a51c6a244000590d0800000000410004ee860000003004700000026c00000000000000ab92402a2183b8d82109444d80041c7706184754c0a8dd96d000758001314b4678001610265e8918ef4401a13400000000004aa10000115204b3167913d0005246ac488003e041ccf8003ae9f5248074285b8daaaa2b2000001042a452c5e0003320187721d03a0440000049c00000000000000000000009ed4322c00019cb60001a4000000000004bc2e8000000000018645271832081000000000000002d0000d30009b80021a33a7092104441aa150a822166000f6000000238000170003214c80000000000000000000000030fc000001a74ec7ecd80005204003499100077ce28d90d460c002785520000021e000000d00005720000009f27c000db8000000000020a464000e900032e00000085398000f08f5442459588f62545d4000000de0003e8270005184b0a00009800800000000106000194340000f714c000bf1f13d60ecaa8000c2000000003c0000492af37a1988297d162001500a70da87c980df21c00000000000adc000000006a8611db000000fe80000000000000000500001b841e000fa94f0008949d83a3820000026348200000000000000bb80010008d4400000076892a8d4de6b52380051c5105500005c0000018a062000000004448d1458001d600000019188000ff111000970000004464c80000035e5bcae9f24ea8104500047e2fc7d9100a43f444a4c3806e5361762ce82c728e431890d4e9f33660000029e5308042f9cb1f22e0ef0004102dc000000002b1088000000015980000050800000000000000001ac46c7d0000c00003880000038c000003f20002b28213233c000003d27b47888b324958000380000013f95a00000000000490000001010005fc780002980010001a000000000000000008c8000c4aa0270004c873c559502bc000b893c4bc02d1796a000ad80000007c0000000025c3fd4f8d10000001a0dd4aa0000007230a0013a23a460384000a91d0870e694303c934868005360005900000007c001ca3460014191a1ce5211b0552c6000fb800538000001350000005083223c2f55110351e5e4319680002a0be0000009b4c8000000000000000000005c97202c840421940ca000001f400006051a0347260400000000124ce000000000002b50002bc0000022e0005d00018a7e852aad508808e18002b67b8181134ae4d05f0005228240000026e000db00000000014207336608000000008f0ec26631c221439e81fc15cb486e4c25d08a89
  | 4 => 0x1b0ce0940000a1c90000994a05100014d030424d2a4d099450d849c000fc0002c13c85b000000000054fc99c000004a0000000000009282c8000bc000001781385705a9703c6000b30004e4000001bc0007380000042e000000002ca9c4c98000003b079000000330f280052c00000000352418c7
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd30c825e63152209758c548823e6494e208f592538823e6414e208f590538831e5350e20c754d43882cd6310a20e350d328823d63d51208f992544826f62551209ed81544825e63151209758c544823e6515120a758c544831e63151208f58c544831d63151208758c544823e6494d208f592534826d6294d209e582534823f6454d208f19153482776154d209d185534823e6414d208f590534823e65d0d208f197434823e6550d208f195434831e5350d20c754d434833854c8120cb152204825e63150209758c540827661150209d584540823e6494c208f592530823e6414c208f59053082766114c209d584530831e5350c20c754d430826d6510820b358c42082e960108209b59632082e9608c820e350d320823f64544208f191510825f63544209718d51083655108420ba58021082796510020b658c40082e96210020ea1084008279658c020ba58a3008399434c020ba58a200826f6548020ab191200827b6548020ae19120082eb6548020dad9520083ab6448020ba99120082e86448020ea19120082a86448020bad8d20082e96348020ead0d20083a94348020ba185200826e62d53109b58b54c425e63953109758e54c423e6494f108f59253c423e6414f108f59053c426e6214f109b58853c431f5350f10c714d43c423e64d4b108f59352c436b52083109798c548425d63152108f992538423d6494e109b98a538426d6294e108f990538423d6414e10c794d438431d5350e108f993528423d64d4a109798f528425d63d4a10e650d308423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c544431f54d4d10c7153534431f64d4d10c7193534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d1097994534431f5414d10c7150534431e6414d10c759053443596014d108f997434423c65d0d10c7d4f434431c53d0d108f995434423c6550d10c7d4d434431c5350d10cbd53524432c54d4910d3d4f524434c53d4910cbd0f524432d43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427b60549109b994524432f5414910cb150524434f5314910d314c524432f4314910cb50c5244358538c110da14a3044278654c110e650d3044368524c110bc185304436852c41109798c540425d63150109b988540426d62150108f992530423d6494c108f990530423d6414c109b988530426d6214c109e980530431e5350c10c754d430423f64548108f191520423e64148108f590520425e63148109758c52042796508010da54820042f161080109e596100427765440109ed9510042e86244010
  | 1 => 0xc7994394031da94a500c7695294031ced0e500c7394394031c750d500c73a5454031ce551500c7994354031da949500c7695254031ced0d500c75a4354031ce50d500c7594354031c650d500c65e63153219758c54c863e6494f218f59253c867a6094f219e58253c863e6414f218f59053c871e5350f21c754d43c878d434cb219e983548867960d52219798e548865d63952218f992538863d6494e218f990538863d6414e219e98053886796014e21c7d4d438871c5350e218f58f544863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544863d6315121c7d53534871c54d4d21c7d93534871c64d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534863e6414d218f590534865e6514d21c7d50534871c5414d21c7990534871d6414d21d3588534863e65d0d218f197434871f53d0d21c714f434863e6550d218f195434871f5350d21c714d434874c538c9219b195324878d434c921b9185324873b54d4121ce153504875b53d4121d614f504873b43d4121ce50f504873b5414121ce150504875b5314121d614c504873b4314121ce50c504876a3214121da4c8504876a21141219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219b988530867a6014c219e580530871e5350c21c754d430866f6548421ba181210867765484218fd91500863c6454021c754f43d031e5350e40c754d439029d6310a4097d8d519025c6354640c7d4d43502b86050d40cbd0f525032d43d4940cbd0c525032d4314940da14b405032c5290140c7991531031d53d0c40ae583431031e5350c40c754e421029d6310840c754c421031d5390440c754c41102b96010440c754f401023f6550040c754d40102ac62500409ed9540102e862500409b98b54cc26d62d5330c798e54cc26e62153309b58854cc31e5450f30a7d9543cc31f6550f30cb95252cc32d5494b30e350e52cc32f4394b30cb50e52cc31d4354b30cb95152cc32d5454b30e350d52cc32f4354b30d390d52cc32d4354b30d350d52cc30d4354b30c750e51cc23f6454a308f191528c23f64546308f191518c2d9600c630ba98b308c26f62551309b189544c27761551309d185544c29d6490d3097195434c31f6550d30c7195434c39b6050d30e6181434c31d43d4930c750c514c39943cc130ba98b304c23d65950308fd8d540c23d63550308f990540c25e63150308f992530c23d6494c308f597430c23f6550c30c794d430c31d548c430c7550310c31d54cc03097d95300c31d544c0309ed95300c25e63153209758c54c823e6494f208f59253c823e6414f208f59053c831e5350f20c754d43c82d96310320e650
  | 2 => 0x200c00003002008000000000040080000c00001800006000000010080000000000000400000000004018010020100000000000401806004000000010000000080000000c0000000200c0180600a000000010000080080001201000002002010000009ed8152d0e786054b439bd8950d0e6c6254343aed8152d0eb86054b43cb54852d0f355114743abd8950d0eac6254343ce54050d0e9d62d4d43a79875350e9d60d4d43add855250eb46154943aed815250eb86054943cb5485250eaf6254543ab1895150ebb6054543ae1815150f355114543abd895050eac6254143add855050eb46154143ce5405050e3f6550c4397d954310f1e5450c43c754f43d0b1e5350e42c754d4390a5f63546429718d5190b1f5350d42ab1894350b3b43d4142ce50f5050b3b4314142ce50c5050b6b4214142ce9085050b1e6454c42c754f4310aad62d0c42c794d4310b1d53d08428fd954210b1d5350842ae1814210a6f6550842ba1814210a7a60d53329e58354ccb1e63953329e98054cca796015332c795143cca9f6550f32c7d9543ccb1d4394732ce95250ccb395494332e650e50ccb3b4394332ce50e50ccb1d4354332ce95150ccb395454332e650d50ccb3b4354332d690d50ccb394354332d650d50ccb194354332ba983328ca3f64546328f191518ca3f64542328f191508ca7761551329d185544ca7b60551329e181544ca9d6490d3297195434cb1f6550d32c7195434cb8f6250d32e3189434cb8d43cc932ba983324cb1d4314532c750f504ca3d65950328f990540ca5e63150328f992530ca3d6494c328f597430ca3f6550c32c794d430cb1d54cc83297d95320cb1d544c8329bd95320cb1e6454f41c754f43d071e5350f41c754d439069d6310a41a758f419071f5350d41c714d43506b46150d41c754f43106b561d0c419ed8152106786054841a758c421072d5210841a758f411063f65504419dd95411066f62540419b189501071f6550e31c7195438c7976150e31e5185438c63f6454a318f191528c71d4354a319ed81528c6786054a31a7590328c69d64cc6318fd91508c63c6454231c750d508c66f62542319b189508c65d63951319bd89544c66c62551319ed81544c67860551319b98b540c66d62d50319e983540c67960d50318f596540c71e63950318f990540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c3197596430c69d6490c31b5586430c63f6550c31c7951430c69f6550c31c7d95430c72e5494831cb552520c78d4394831cbd0e520c72d4394831c750d520c72e5454831cb551520c78d4354831cbd0d520c74e4354831cb50d520c74d4354831c350d520c74d528c831a7590320c71d4394431a7593310c795438c43197d95310c677654c431e5d0d310c73a5494031ce552500
  | 3 => 0x85cc50210000000001b31e7fc0016100000000000000288001e50aa7e0139be00000000000272148001ef4de000b385e032000cb1581c04e10f0000000010910646262000000000000a18003da20c00000000000000000007f8bf80014e0811a8850000000001f0562f51b8003b05880014c000000002130000006e00000000000000256000000000007f0000000006f40000013c7540000000084000000148208a209c000000000002c81187e87e204000000000000000024800000000000000490000c000000061000000000000000a8000680000000a40024a000604000534ca000000000008807100000000000000000000000b23700010380009c6ec1688a4320000000033a000002331d664c00000000000b008132e9b4000000000000000000000018247000000fa0b50000000000024e00090070014434ea0001a63d081a49000360f588d1526b800000000000001e200000000000000000000001aa00000000000000a4800000000cfa0a0000006f0000006784989908400057000482505048800000ed3011c0000000025a00039c000000000000000013675c0c0110002bc0000000069400000000000f9800000000ac90b26e00094800356000a90000cc0000000000000094000000000b500000083c000000000000000000047c000000000340015a000000730000000000007800000000000350650000002ba5ac0000000000089a02000000bc2000000000004f000000c60582d8120728000000004b000000000000641ec6a8001460ac000000ba0000002f931000000000000004100000023632408075000000000000008b8000004220002000000055c000000002c40014d00000084800000000000004d69480024c0000000022a00052d0700011e86cc020d4e2000888000000000000000a000000004b6000000000000000002c0000000013003a5f06d0ac1d400000000000000000002ac0000023645a00000000000671200ec2b858c0591e15a45c9a171054000000000000008602f00000000000000000000c700000000000000000388001f4220d38000003c0000000000000000039a2fc1d1fd00000102a2400000000000000000871cb000000000000000000023a0005540000f00000105800000038000000000f40015f000000a99fb0000000000480000000000001002010000020040000180200000000003000004028000020000080100c0080000100000400003002004010000000000000400800000000008000008000000000080000200000000000038000000000000100300001800803002004000010020000100000000000000000000018020000040380100800800004000000018000040040100000402801000002000000000000000180000000000002000004000000000000000200200400800000000000010
  | 4 => 0x129800000000dc80008a0000913629e000000000000007c000000000b9800000000001b30000f87890a368000000843ec0000000000000000000000000000004460dc000000000000380024a0012325e06c0011f000112000000000f600000000000000000000000007700000065400000000000000000005bc000000005e40011542a0000000019e00000268000700000002100000000000071c00227000000d00000000000000000000000000000001381de3c20000018e0d61d8001cf2bc000000720000006c800000000000000000000000000000000049000648000b0168001220000008acd30790000000011000000000000000774cc800000000000002d00004ea16000001190000b4000d880000c00000208000000000000000005284447e7d4000264a84d40000000010c00000000000000250000011800011c0000000000000000000000000001693e277c00014000008001a30000212896519a43c000003341b40600000651cd680000093cc2800000000001182b6000f7000000000ec80000000000000000001019bf000000002211503105f1d6000000000001e600048800000000000ab000000000000000005180000000000000360000998001fe00000000000684000000004508c9b22461f4348000005d0000c600000000000390000000000006a40004728a000000e8000000001f04d49b8000611308040000000000000000000000000001ba00000000478000001720f49904802e000000000000000552a8000000000000029c000de1e30000010a24b2764a80485044a0000000000000000000200000002390ce298000000000003984c0ee0000000014227c00000000000e49c4000000f480000000000000000000000000c4000000002780000000000000000000294000000a000000000000000000000000000011112f0000004a0000003dc1984d000000bb99b06a608001af4d21a0671ca4b25b4ed26210e8f4fc81e000000c88000000705500022c000c181700070c5c80025a000e0800000000000004c20012b13e4503500b1d1484940689e01760011c000000000a40000000000008b1ea414f90000004b8000000000c8b70c1000000d613a000000000000007dd2700000000000000000000000000008bd318df4cc0002e00000000000000284000e10000003b40000000000000000026000000000000007900000000000226000000000004ce0000000000038400000000000000004184f4000001c8001160000000f0f3a433d4000000220000005b00000038c000000000910d0002f40007c8004b08d000184000000000003b6748db8c8476484598fe2fc874002180006e8000000000003f8003a6000000313f45ec001870000000005d000000000000000006911d0003ecc4800438000000e90002181c00000
  | 5 => 0x7a0e7000000000020c500000000000000000000000c6000d20000000000009a000000000510000000015412a00000257000000000000007180024d000000000000000000007400000000198280000000000002e0ee06f30c688000db11862c000ca0ca4481c8000d80001a01a00000000000000914000970944985e0001240000005b0005f4960600000003e00043e00000206000000000000005c0a88004d88106b0cb000000000003c8000000000000000025f0006d800000000000c68003a0000000000000000005700041c619760000000000000000000000050004000003981b8350000000000000000000000000000000000b70825d4a80000000000000000000025800000468001e64ba4c8c8000000000000000000000000000000000000000000000000000002c8000003f0b3000202000e293f0006d51480000000000000000488000001ae3301183f0000012e0ef3d800000000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2180000496091793988f081f8015a2a09f0ba20f8006911800250786248b0011970004000c909c00000a8020239d1d8c1b9900008883800e859c800a021680151a8d0d8024211210230e1b071300019a051e129482830119941e89800306080060000a801c0880106000010600384101995287054852d0e94392a02868726dc162d4d4391ee4b06a6a1d24715485250e94382a429287491c95114543a60e0a88a2a1d28725405050e9838aa0282874a1c94314142c1aa6b1686214a87058b4310b0ca98c0a1085a250e60cc932c1ac6a908420d2870548421070ca1ec0a94638350f6254231e1286a94a018f0943949500c784a1aa4a8063465c25350f21a32e029a8710e0d6458853486863aa869924383195434c921d0a8630a6490f09434c850486b038a6428243075cc6454021a50e0a18a4a0619535834310254392c1a18818654d6010440950e4b00822060d531894010344a1cc598261435ca5350d20a32e129a869041c7654d434828a38aa6a1a41465cc54c8120a1ae62a440904a87458232082543a2c010841625cc4210020d12c621080104a87458a3008246b98c890041265cc6448020954e932240104c97319120082c4b98c890041a29cc6448020952e63224010689731912008244b98c8900412a1d163480209c0e2b1a40104a876d0d20082543b28690041a258d4348020a1ae429a878841d7399352c42953a6a410621435ca5350e10c32c8b00a6885187550d304430c32a8698221c250c524c110d228630a608866052185304420eb98c8a90214a1d15208010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc0200292814c020e258c030021c09531c162d0c42c09631c15210841a048550c614c921d01431c53214121c09531c960d0c40c09531c96010440889831d160084208888758d4348020a808158d4348020909839d35208310a108550c614c110e0143148614c110909831d15208010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => packedAt s4K6 (770+((h/14+packedAt s4K6 (672+(h % 14)*7) 7) % 80)*7) 7
  | 5 => packedAt s4K5 (21436+((h/233+packedAt s4K5 (18873+(h % 233)*11) 11) % 1115)*11) 11
  | 4 => packedAt s4K4 (26076+((h/208+packedAt s4K4 (23788+(h % 208)*11) 11) % 1604)*11) 11
  | 3 => packedAt s4K3 (3850+((h/25+packedAt s4K3 (3675+(h % 25)*7) 7) % 91)*8) 8
  | 2 => packedAt s4K2 (800+((h/4+packedAt s4K2 (780+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffff01fff07f83ff83f0fffc3fe03b83f3e7
  | 1 => 0xf80ffffe07fffffc0fffff07ffc1fffcfc7c7f
  | 2 => 0xfff03ffff8007ffff003fff87ffe003f1f8f87
  | 3 => 0x3fffffff81fffffc00007fffffc7e00ff8
  | 5 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xb0a2911c51249480b3a0b04cac13228981b1e3
  | 1 => 0x126102243240201404855101144049902c542d
  | 2 => 0x6145a448a0e9492d50426a905aa40526168e86
  | 3 => 0x458a3891048c0dca696808c463399607c00b50
  | 5 => 0x860c30e1c70e71f38e738ce602311807fb6000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xece8ece8ec80ec80ece8ece8ec80ec80ece8ece8ec80ec80ece8ece8ec80ec80ece8ece8ec80ec80ece8ece8ec80ec80ece8ece8ec80ec80ece8ece8ec80ec80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36767
namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fb90821f6a1043ef32087d86410df94421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40bfa9281ef52502dea4a05f14940f6292816c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5987b94b30b7296617d52cc3daa5985b54b30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ee32883da65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53483dc84907b50920bfa8a417c51483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884107b8c820f6990417e51082faa2107b88420f6108417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f460887e4c110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132ef21a65dd434cbdc84997b50932f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f790c31eea18637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719243ed32487ee4290fb88521bfa8
  | 2 => 0xf1438290098212641400926640e394a200021213d16a4d1e4698f01461d02289517547e3d4fa9d723232819a4724c8502199c0787011b806014318c913932a000000001d44dc000c4358000c206a3d2000639f40ca4a4000002de15d068003ee0e400000000000d38d51c07b0000004200012580038c478cc1f832c3cc0108f0008c41b0d0000000ed89d0fc7106f90f206200b51fc28a48ceb1be41858c0a25f08425c3b10839a7e4cd0d64a436c75a241b48483413f2b468c148003565f40012d486900c02441a808c2411700072c5f9bc4ae7a0880ba30c2bc92a4a178198b023d224930179eb2a02d8cf0e11ba4509016b10a00c8e9cc1d20e8b405a184820860f813e3150182d4b63303986b4ac6150e97c4bc550f787b3d451c1e86420a0543481a2f4530a00f74049811b0051325a41300018683ce124f47812c288780b00001891f000768d880044a42cdb9b5000000d9819408590410001640002f800154000000004a6000001bd1288545a84a0007b44e086466034000910762a50b1ba00081887053120298360cb0c22cc5f26106e3b0f708c3b807124898000268f91b60000007700001e26c459e4150304b094e470180d69b431c204d78ce47c720d29d81088bc4685943098c3aa2149c6e4f112739e804120110b8134f992c292490561532be088538544600240393c4824088a8cf1e23e4cc9aa43e5e4491383aa2c4c617b2228d4a79132aa814e8143056278768713644340017748c8ec0000032e470ef0000003f92c1910dc46c001fe0b6280c98a13600002f21b2e006c7300038a0009799b1ae578850001f66e00008922c0005180020e570000b900018800000000000002222564d41717e2cc55c0026438689c202391bc418648d9414388601fd03a1e47b0740408b9131ce2301480015930e56c7ea294aa7c000000000000390fa200620d10772b060c7783438263d2a1d21107d9310ae070294f09ca4469750c9fa15a82c001360002ac0414b1b8410df8c812a62c718003a60000000000c0401401008000a40702c170000c008150000c0200004013000011040b03804094000041800c030101b0001d028050800000016038050001600002020000201402017004000240100805008000180a0000e064060d8290000f0001c028020000503c0500000004060100003c06000010340d004000200101006090010d40400402010020102605c0100c050140100006008100140e0000001802000000140102c2204c0201006038600001303012000110280400c02004000904f0480202404000000300001c120300001c02014080900100c010000600805010000040c0200401c0205c0d0040009c111440001c440140004403000080480702c2a0a437bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x2113be000669783ba508b984610e000721822d85d8f18170da85cb6804000520000b7234405240000000003f95600002c00171000594980f000084c000000600012d027000000a884c412154ba0964ca6280012211c000f28004ce964319a44580b1158451600a8d08b832020cea25135c634d018127c24d0f0d20004a09a0002c4000060413a20001414a0004e80025c0006ec7a03e3cc058971c948a5c8998a247459c380000ac0011a0e709c0000019f176000001ff00079c5a0d30008a807010088800ec93d350000000bd0de4ec190183f600400025282000001c71a2624bf9a90ba5746c0000000010713143407cca07d0005b81f99d0008a0a907a0928800006708e4847f8004a08c83e0350003f0a6a420000000f1
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd431034e5394840d354e521034e5354840d354d521032f4354840cb50d52103686054840cb54a421029d6310840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cdd0d51103354354440cd54641102b960104408fd9540102ac62500409ed9540102e862500409b98b54cc26d62d5330c798e54cc26e62153309b58854cc31e5450f30cb95252cc32d5494b30cb95152cc32d5454b30d390d52cc34d4354b309b988548c26d62152309d984548c2756115230b6580318c26f62551309b189544c27761551309d185544c26e62151309b588544c25c6550d309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c26f62544309b189510c355510c43097d95300c27b654c0309798c54c825d63153208f99053c823d6414f20ba18142c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823e6494e208f59253882cd6310a20d394d32882e4614ca208f992544826f62551209ed81544825e63151209758c544823e6515120c798c544831d6315120cb588544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d209b996424832c54909209b195424832c5450920ba181424833854c8120cb152204825e63150209758c540826e62150209d984540827561150208f990530823d6414c209d98453082756114c209b597420826d6510820b358c420826d658c820b9185320825f63544209718d51083655108420ba58021082796510020ea108400826f6548020ab191200827b6548020ae191200826e62d53109b58b54c425e63953109758e54c426e62953109b58a54c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538426e6294e109b58a538425e63d4a109758f528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d6580534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524433454905109d1954144358538c1109e195304425e63150109758c540426e62150109b588540427661150108f990530423d6414c109b988530426d6214c109e980530423e64148108f590520425e63148109758c520427965840109dd95100427b6544010
  | 1 => 0x7140000003010080a000000c00160484c020302000000f05000060502800060500004061d0100008020c000240d0280800010980812000c05402221005c0c100101c06010180c2008018200a060b00044069bd8950d0e6c62543439bd895190e6c62546438fd954310e5f6550c43cbd0d5210f4e4354843cb50d5210f4d435484397d8d5190a5c6354642ced0c5050b394314142dad085050b3a4214142c754f4210b4d53908428fd954210b1d5350842ae1814210a6f6550842d354d4210ae860508429e98354cca7960d5332ba181428ca3f64542328f191508ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5c6550d329b195424cb8d4350932ba181424cb564314532d550c514cb664214532d9508514cb673214532d58c8514ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320cad4614c8329bd95320cb2d544c832b9185320cb1e5350f41d394e52d074d5394b41d394d52d074d5354b41cbd0d52d072d4354b419b988535066d6214d418fd95411067765504419bd89501066c62540419b98854cc66d62153319b98a548c66d6295231a7590328c63f64542318f191508c66f62542319b189508c65d63951319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131d914b314c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c71e63950318f990540c66e62150319b588540c67a60150319e580540c65d6590c31b5586430c71e5450c31cb952520c72d5494831cb951520c72d5454831d390d520c74d4354831d9185520c74d528c831a7590320c65f654c431b3189310c677654c431b9189310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c75a4354031d650d500c65e63153219758c54c863e6414f218f59053c86e4614cb21b958831c87c6320c7219e983548867960d52219798e548865d63952218f990538863d6414e219e98053886796014e21cb95142886e86050a21ab590328865e63951219758e544866d629512197d8d544865c63551219ed81544867860551219798e534866f6254d219dd85534863e6414d218f590534865e6514d21c7990534871d6414d21d3588534866e658c921d314e324866c654c921d314d32486e4614c921d514f214874c53885219798c540865d63150219e980540867960150218f990530863d6414c219b988530867a6014c219e580530866d6590821ba181420866d65cc8219b59432086ad640c8219d59431087c4320c4219bd9521086cc63484219dd9521086d463484218fd91500863c64540219b98a539026d6294e40a758c429025f63546409718d519026f62546409b189519036852d0140cb14a40502b960d0c40c794
  | 2 => 0x6a8006eaf09d8f25924c2625462264342f283038821ae3900032800001e843220002060014e000a224ab2909fc6f230c98005e00025816002d477002c70128b8822b018a4ade35088b22ba4025e11946a18b2268e22a0320b0207d800000a0501a2a0afe488268fa3c00000af99c5284c9408ca300c920f6002dc4400010800a5800001ca00000000000020a30b360011e93a7ea617a000445f2f4a71185601e56938128742d17e349c61b212c88ea919089e2402786a152da9d2883d1264b000781e66d9cc000dc000004a16600000ac07257266000860014c2a8007b1facd2cc4c1d0360007f96c1a2c2789de1f2cab000000150cbaa6a69680000000000ad2609e80000180bf182162440009c763160680ebb9547b9f8399a0002fa320f889890751be67a363f84e42a9051312a7b14a52324091a4821c01a1ab59140a8e866924b9330168000028eba8008e822720003b30255aa823800332840f8300f18a412d2001e41f87000328b60008a800000f084000888243b9b8891d6ba1da002e60008ab4184002c40002ec112a4bab8449a44f8625db06838da178527c9f402992af00085aa0811b21b8a69c8b665174c6a586d2c69c27c4717221004c90a465b38971864e9365c094ab2628e0e06a050632287c18e1215e2e9c035a2c182a4319ac202a25481c159c2c8234c7b00663081e8c0852e0862b600000000769b33aaaa8a00000cc85cbda803f0b8bb2ce000080001031000c40001e000000002c000cb0002fb2a10014be190aba1e2b8009ba684f106c31c4002560d2e20010ec61a65230e0020000132378001930a5a96e2f03a4d1b0949160a202000ce0014219a4a96836581ce74a6a3e9627a800010b80002040080402140100416000000026270680000020d814020001870000000000102b000000000008303e1a350083e000a800000d080100c1701000001702830000b0b024080
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1634308060000938828000c0000130000115404805c04143c41802c11c5001040021800158654c6050842c92a6302842168943181424cb82a1a8428a65581c14214532c2aa830a641962554185320ca62392c321863435ce5450a21c54a83028510e0d645885348686ba0a6992439114c614c921b0ae81906210ca8725834310254392c020881511c9510c430a1ae929a6510646531853288306b1ac42a241435cc5450920c50a830284905447354421082543a2c010841625cc4210020
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x400820006000d01431c14214532a09839506050a21a058414c614c921a058494c614ca20a09831506050920
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 740)*11) 11
  | 4 => packedAt s5K4 (16974+((h/138+packedAt s5K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffc07ff0fc1ff0ff87ffff0fe03a63f3e7
  | 1 => 0xf01f87ff83ffffe0ff0ff8701ff0fffd9ccc7f
  | 2 => 0xffe007fffc00ffff000fff801fff003e1f0f87
  | 3 => 0x7ffffff07fffff000001fffffc7e00ff8
  | 4 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x614500470821100330118091cb0122882151e3
  | 1 => 0x24c20889194040a051068822451049908cc42d
  | 2 => 0xc28b551230eaa56d088b550496aa0526170e86
  | 3 => 0x8b14662442883656aaa0440918cc9607600b50
  | 4 => 0xc184438630cc798cccc664e00881807daa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80eeeaec80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36767
namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x3c6470900ec6244e8159d0000a020c00b3800fd12a50016004c41eb624cc50578207977468f846e00d8760354804a00a91028df0026bd90000c401c72010800001a0b5ad40035c00018070008001041808c14543030004c100e00a00017fd50057f54017f95005fd54015f55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03fe4300ff50c03fc4301ffd4807fe5201ff54807fc52017fd0805fe42017f50805fc4200ffcc803fe3200ff4c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41017f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42000ff08210007fe2108003f71084001fd884200bffd951005dfeca880037f65440013fb2a200bff9951001dfcca8802ffd65440177eb2a200bff1951001df8ca8802f7c65440073e32a200affd9110055fec888003bf64440015fb22200aff99110015fcc88802bfd64440157eb22200aff19110015f8c88802bbc64440055e322200affd5110056fea88802bfe5444015feaa2200adf55110057f8a888027ff63440137fb1a2000f7d8d10005bec688027fe63440037f31a2009ff58d1004dfac688027fc63440037e31a2009f718d1000db8c688027ff5344013bfa9a2009ff94d1004ffaa6880277d5344013fe29a2009ffd0d1004ffc8688027fd4344013fe21a2000ffd8910005fec488003ef624400177b122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488003ec624400176312200bffd491005ffca48802ffd5244017fe292200affd0910057fc848802bfd4244015fe2122009ffcc91004ffc6488027fd3244013fe192200bffd451005ffca28802ffd5144017fe28a200affd0510057fc828802bf64144015fea0a200afd50510057f88288027ff3144013ff18a2009ff4c51004ff86288003ff2144001ff10a2000ff48510007f8428802fff5044017ff282200bff5411005ff8a08802bff4044015ff202200aff50110057f88088027ff3044013ff1822009fe8c11004ffa6088027f93044013fe1822000ffc8110007fc4088003fd2044001fe1022000ffc4110007f62088003fe1044001fb0822006ffd9410035feca0801bfe65040077f3282006ff59410035faca0801bfc65040077e3282005ffd901002dfec808017fe64040057f3202005ff5901002dfac808017fc64040057e3202005ffd501002efea808017fe540400bfeaa02005df5501002ff8a808013ff63040097fb182004ff98c1000dfcc608013fd63040097eb182004ff18c1000df8c608013ff5304009bfa982004ff94c10027faa6080137d5304009fe2982004ffd0c10027fc8608013fd4304009fe2182000ffd8810005fec408003fe62040017f3102000ff58810005fac408003fc62040017e3102006ffd4810037fca40801bfd520400dfe2902005ffd081002ffc8408017fd420400bfe2102004ffcc810027fc6408013fd3204009fe1902008bf98410037fea20801bfe510400dfea882006ff1441002ffe8208017fe410400bfea082005ff10410027fe6208013fe3104009fe9882004ff0c410007fe4208003fe2104001fe9082000ff0841003dfcc00801bff500400dff2802006ff54010037f8a008017ff400400bff2002005ff5001002ff88008013ff3004009ff1802004ff4c010027f86008003ff2004001ff1002000ff48010007f84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xbfe4108025fea084012ff1042008ffe6210047fe3108023fe9884011ff0c420087fe4210003fe2108001f71084000ff48420087f84210003ec21080297f3004013ffd402009ffca01004ffd5008027fe2804012ffd0020097fc801004bfd4008025fe2004011ffcc02008ffc6010047fd3008023fe1804010ffc8020007de4010003fe2008001fd1004000ff48020007da4010003f9200801fffb2e200fbfd971007ffccb8800efe65c401ffeb2e200fbf5971007ff8cb8800efc65c401dffb26200ebfd9310077fcc98800afe64c401dfeb26200ebf59310077f8c98800afc64c401dffaa6200edfd5310077fca98803bfd54c401dbeaa6200eff15310047fec788022ff63c4011ff31e2001bf98f10047fac788022fd63c4011fe31e2001bf18f10047fea7880237f53c4011ff29e2008ff54f10046faa788023fc53c4011ffa1e2008ff90f10047fa8788023fc43c4001ffb162000bfd8b10007fcc588002fe62c4001feb162000bf58b10007f8c588002fc62c401fffa96200fff94b1007ffaa58803ffc52c401dffa16200eff90b10077fa858803bfc42c4011ff9962008ff8cb10047fa6588023fc32c401fffa8e200fff9471007ffaa38803ffc51c401dffa0e200eff90710077ec838803bfd41c401dfaa0e200eff10710047fe6388023fe31c4011fe98e2008ff0c710007fe4388003fe21c4001fe90e2000ff0871007ffea18803ffe50c401ffea86200fff14310077fe818803bfe40c401dfea06200eff10310047fe6188023fe30c4011fe9862008ff0c310007fe4188003fe20c4001fe9062000ff0831006ffecb08036ff658401bff32c2003bf9961006ffacb08036fd658401bfe32c2003bf19610067fec908032ff6484019ff3242002bf99210067fac908032fd6484019fe3242002bf19210067fea9080337f5484019ff2a4200cff55210066faa908033fc548400fffb1c2007bfd8e1003ffcc708006fe638400ffeb1c2007bf58e1003ff8c708006fc638400fffa9c2007dfd4e1003ffca70801ffd538400fbea9c2007ff14e1003ffe870801ffe438400ffea1c2007ff10e10007fec508002ff6284001ff3142000bf98a10007fac508002fd6284001fe3142000bf18a1006ffea508037fe528401bfea94200dff14a10067fe8508033fe4284019fea14200cff10a1003ffe650801ffe328400ffe9942007ff0ca1004dfac308037ff518401bff28c200dff5461006ff8a308033ff4184019ff20c200cff50610067f8830801fff318400fff18c2007ff4c61003ff86308003ff2184001ff10c2000ff48610007f84308012fe608401bffa84200dff9421006ffaa108037fc5084019ffa04200cff90210067fa8108033fc408400fff9842007ff8c21003ff4610801ffd308400ffc9842007ff0c210007fe4108003fe2084001fe9
  | 2 => 0x200b5fac51006bff5288035ff294401aff54a200d7f8a510067ff4288033ff2144019ff50a200cff88510053ff3288029ff1944014fb8ca200a7fa6510053ed3288029fe1944000ffd8620007fcc310002fe6188001feb0c4000bf58620007f8c31006bff5188035ff28c401aff546200d7f8a310067ff4188033ff20c4019ff506200cff88310053ff3188029ff18c4014ff4c6200a7f86310003ff2188001ff10c4000fb88620007fa4310003fc2188001f610c4011bf982200d7fea11006bfe5088035fea84401aff142200cffe8110067fe4088033fea044019ff102200a7fe6110053fe3088029fe9844014ff0c220007fe4110003ef2088001fd9044018ffd95200c5feca900037f65480013fb2a4018ff9952001dfcca90063fd65480317eb2a4018ff1952001df8ca900637c65480073e32a4017ffd91200bdfec890003bf64480015fb224017ff99120015fcc89005ffd644802f7eb224017ff19120015f8c89005fbc64480055e3224017ffd51200befea89005ffe544802ffeaa24017df551200bff8a89005bff634802d7fb1a4016ff98d2000dfcc69005bfd634802d7eb1a4016ff18d2000df8c69005bff534802dbfa9a4016ff94d200b7faa69005b7d534802dfe29a4016ffd0d200b7fc869005bfd434802dfe21a4018ffd49200c7fca490063fd5248031fe2924017ffd09200bffc849005fee424802ffea124017fb509200bff8849005bff324802dff1924016ff4c9200b7f86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a4018ffd45200c7fca290063fd5148031fe28a4017ffd05200bffc829005ffd414802ffe20a4016ffcc5200b7fc629005bfd314802dfe18a4000ffc8520007fc4290003fd2148001fe10a4018ffd41200c7fca090063fd5048031fe2824017ffd01200bffc809005ffd404802ffe2024016ffcc1200b7fc609005bfd304802dfe1824000ffc8120007f64090003fe2048001f71024010ffd942009dfeca1004ffe65080077f3284013ff5942009dfaca10043fc65080077e3284010ffd9020095fec81004bfe64080057f3204012ff59020095fac810043fc64080057e3204012ffd5020096fea81004bfe5408025feaa04012df55020097f8a810043ff63080237fb184011ff98c2000dfcc610047fd63080237eb184010ff18c2000df8c610047ff5308023bfa984011ff94c2008ffaa6100477d5308023fe2984011ffd0c2008ffc8610047fd4308023fe2184015bf9882009ffea410043fe5208027fea904010ff14820097fe8410043fe4208025fea104010ff1082008ffe6410043fe3208023f71904011ff4c82008fda6410043fc3208021ffb084000ff98420005fcc210003fd61080017eb084010ff1842009ffea21004ffe5108027fea884013ff14420097fe821004
  | 3 => 0xe1824210ffd94210fdfeca1087ffe65084077f328421fff594210fdfaca10843fc65084077e3284210ffd90210f5fec81087bfe64084057f320421eff590210f5fac810843fc64084057e320421effd50210f6fea81087bfe540843dfeaa0421edf550210f7f8a810843ff630843b7fb18421dff98c2100dfcc610877fd630843b7eb184210ff18c2100df8c610877ff530843bbfa98421dff94c210effaa6108777d530843bfe298421dffd0c210effc8610877fd430843bfe2184221bf988210fffea410843fe520843ffea904210ff148210f7fe8410843fe420843df7210421eff508210f7da8410843fc420843bff9904210ff8c8210effa6410843fc32084417f308421fffd44210fffca21087ffd510843ffe288421effd04210f7fc821087bfd410843dfe208421dffcc4210effc6210877fd310843bfe1884210ffc8421007de4210803fe2108401fb1084200ff48421007da4210803f52108421ffb004200ff98021005fcc010803fd60084017eb004210ff180210fffea01087ffe500843ffea80421fff140210f7fe801087bfe400843dfea00421eff100210effe6010877fe300843bfe980421dff0c021087fecb90072ff65c8039ff32e4003bf997200e7facb90072fd65c8021fe32e4003bf19720087fec99006eff64c8037ff3264002bf993200dffac99006efd64c8021fe3264002bf193200dffea99006f7f54c8037ff2a6401bff553200defaa99006ffc54c8021ffb1e4015bfd8f200affcc790006fe63c802bfeb1e4015bf58f20087f8c790006fc63c802bffa9e4015dfd4f200affca790057fd53c802bbea9e4015ff14f200affe8790057fe43c802bfea1e4015ff10f200e7fea590043fe52c8039fea964010ff14b200dffe8590043fe42c8037f7216401bff50b200dfda8590043fc42c802bff9964010ff8cb200affa6590043fc32c8021ffb0e4000ff98720005fcc390003fd61c80017eb0e4010ff187200e7fea390073fe51c8039fea8e401cff147200dffe839006ffe41c8037fea0e401bff107200affe6390057fe31c802bfe98e4015ff0c720087fe4390003fe21c8001fe90e4010ff087200e7fea190073fe50c8039fea86401cff143200dffe819006ffe40c8037fea06401bff103200affe6190057fe30c802bfe9864015ff0c3200d7fecb1006aff6588035ff32c4003bf996200d7facb1006afd6588035fe32c4003bf196200cffec910066ff6488033ff3244002bf992200cffac910066fd6488033fe3244002bf192200cffea9100677f5488033ff2a44019ff552200cefaa910067fc5488029ffb1c4014bfd8e200a7fcc710006fe6388029feb1c4014bf58e200a7f8c710006fc6388029ffa9c4014dfd4e200a7fca710053fd5388029bea9c4014ff14e200a7fe8710053fe4388029fea1c4014ff10e
  | 4 => 0x843fc42c8443ff9964210ff8cb2110fdc6590887fd32c8443f69964210ff0cb21147fea3908a3fe51c8451fea8e4228ff1472113ffe839089ffe41c844ffea0e4227ff1072110ffe6390887fe31c8443fe98e4221ff0c721087fec190803fe60c84017f3064200ff58321005fac190843fc60c8451ffa864228ff94321147faa1908a3fc50c844fffa064227ff9032113ffa819089ffc40c8443ff9864221ff8c32110ffa6190887fc30c844dffb2c4226bfd9621137fccb1080efe658844dfeb2c4226bf59621137f8cb1080efc658844bffb244225bfd922112ffcc91080afe648844bfeb244225bf5922112ff8c91080afc648844bffaa44225dfd522112ffca910897fd548844bbeaa44225ff15221107fec710882ff6388441ff31c4201bf98e21107fac710882fd6388441fe31c4201bf18e21107fea7108837f5388441ff29c4220ff54e21106faa710883fc5388441ffa1c4220ff90e21107fa8710883fc43884457eb144226ffd4a21137fca51089bfd528844dfe2944225ffd0a2112ffc8510897ee428844bfea144225fb50a2112ff88510883ff3288441ff1944220ff4ca21107f86510876fe618844dffa8c4226ff94621137faa31089bfc518844bffa0c4225ff9062112ffa8310897fc4188441ff98c4220ff8c621107fa6310883fc3188401ff90c4200fbc8621007ee4310803ff6088401ff3044200bf98221007fac110802fd6088401fe3044226ffd4221137fca11089bfd508844dfe2844225ffd022112ffc8110897fd408844bfe2044220ffcc221107fc6110883fd3088441fe1844224ffd9521125feca908037f65484013fb2a4224ff9952101dfcca90893fd65484497eb2a4224ff1952101df8ca908937c65484073e32a4223ffd912111dfec89088ffe64484057f3224223ff5912111dfac89088ffc64484057e3224223ffd512111efea89088ffe5448447feaa24223df5512111ff8a89088bff63484457fb1a4200f7d8d21005bec69088bfe63484037f31a4222ff58d21115fac69088bfc63484037e31a4222f718d2100db8c69088bff5348445bfa9a4222ff94d21117faa69088b7d5348445fe29a4222ffd0d21117fc869088bfd4348445fe21a4224ffd4921127fca490893fd5248449fe2924223ffd092111ffc849088ffd4248447fe2124222ffcc921117fc649088bee3248445fe9924222fb4c921117f86490893ff5148449ff28a4224ff54521127f8a29088fff4148447ff20a4223ff5052111ff8829088bff3148445ff18a4222ff4c521117f86290803ff2148401fb90a4200ff88521007dc4290803ff60484017fb024200ff98121007fac090803fc60484017e3024224ffd4121127fca090893fd5048449fe2824223ffd012111ffc809088ffd4048447fe2024222ffcc121117fc609088bfd3048445f
  | 5 => 0x610000b11fc95d8001d090f09d8bc1530000001e89638348001c5a3280088fa241510c202e05506780984418706f00c1ed0000001c38000261260000001cba0c9aa80000006e8000390000598fc0000e180019e00000000008296606280016400000000021c00006e00008c89aa0292c84002294f96d8cc03b0ab21514001d21c9561ce80007d10d0269b581391c21914084d9d593a9dd8af8df072a4080010d8000e000000500000023f9079228b380022a80017c0001968000ee18b0000de9b700013b80014983d80000004c8001fe9f887a04f23b03b8b41898f49dc9168748000878d910880000021702f00021193a2059e50659448000bd8000b91c80001b991089d0001118e10e81ac0000010000000c40da1ec0008000160040d00900c0040200301e0080002a0060040500003c00420000006000028060380000080201801c0000505a0040000300002803006018000000050140180000401005c000000280000380100200c018100000000100904e0080480400a0000380100a0000001e000024000020020140180500000c138090080040580300e02c0b0000000241180202807005039022008008140000000000a0040040380000401c0980204e02401801004000008010100240300500e034060000100080000a016050000150060140000000002c07800004004008090020000000405c0080500800002800001000004000000020000203800000400000002004040000000100180001601401004006008000040080300400200a0bc0181100c0200680304c01c0080400000c0080100a00400003000004008010280000001000000006005000004098170960a002000000000000010020200200200409c060000020240601b0020340501600000001807006028008010020080100500001c0000900c0040000400e04c0980000415c0600300400002800000008018160280040000700000c0580101801c0180000200000003012004008030000040000401401c00008006020030000000000201101601c0a8020000441100000402c00000000000028020020080580000601c1100a01a00400800000004040070000100180400a0740000f000014020220000300000000002c21ffb2e4228bfd9721147fccb9080efe65c8451feb2e4228bf59721087f8cb9080efc65c8421ffb264227bfd932113ffcc99080afe64c844ffeb264227bf59321087f8c99080afc64c844fffaa64227dfd532113ffca99089ffd54c844fbeaa64227ff15321087fec790886ff63c8443ff31e4201bf98f2110ffac790886fd63c8421fe31e4201bf18f2110ffea7908877f53c8443ff29e4221ff54f2110efaa790887fc53c8443ffa1e4221ff90f2110ffa8790887fc43c8451ffa964210ff94b21147faa590843fc52c844fffa164210ff90b2113ffa8590
  | 6 => 0xa68000fb1d216f8fd8e787416a20e1321e90000b01f100000002b0000002338549248000001009c71888001330791c88242038f08538f18408290000000001280a280000019c80000000000010181da248000000d08968000c29bb0000001579489598001f480006a8d193695495a1158120f306923098292404197f08c12019118a1470001ed90521f9131bd22523708b0001f287a9f30001918000001cd85d12f00018e14d8f60d50e580002fa3d00000016c0e709f00a94b0000000c813d05b95391a192a2b09ba2009e9a380011800b0b187b9150001de08995180782c85f10a1f41cd00022613e8002050000ec0001651e080000009e00010b8000e99dd0180002040bb8028000b81f60ac96598c0000001328000000000db9621809f20668a18448001431010e51a60dd00006992080022913980021d21e90709498d0001758399950a8a300001f70250ef80580023612d0d11468000001b21b80e203c9cf0001128a396f000184800190a1e00003d0068001a31348d81a08c000000012987d9d50c68961600001c900010315580000000000000022280000000002a0889611221bc14604a23e01780a20d9e281b9a80000000a40761a58160a60000d30000001a28000000430bd09b1b49c0a270f41be0730769c606880019a089183a2b96491e1111750e495282000000019b85c9f900318803681a1e40001729d81be8ff00000000003808380006d22c0ce9ef83898c80f8ae94803c06c02aa268cf02381117989989fa128f99e20ce1149581779b60cd11f049996174a2d23194e9c18fe93f2381f013386009c92698e9a000610c07011b1699ec8001d68e680023d80018796b00007184800022d91400013c16080c87220020a90212b8338270dd8988cd8ed03412e1cb1958622108880c78158541b009580010900013590400004c0d20000000000000000000c58bf8831668001840758000081ba06823221a0818280000411ea9e68439720b695f9c28daa1480013900015c80000021218b8d41eb83713622e0f686c92885a18007b08ba0a24016286d863037a1f0fa8858001e58000cb9049d990698180010fa1000006b9ea0f81a211ca0e83e16e8ae1ef0478c9a3f22f1ff8b78048ad87c84e13895b0990d49db0d79fd15019c1a92210041d91e80bc870a3ea220ee8b58ca14107100002489c13081718d80021400383a2048c310e1318be8ff8a71a187805e2021ff1af0f28000a81b79279000210d700001180004d00017e9740980001990b30df8aa9f698fa350810660000001f80070001591300d00af1310000001b42391540c180016b80000007397a8000000000000001d60001ca0359eb00000e92e9db89383211fa379ca8000092159618001de8001738000000350619c40000000000000000001900140cf8000001688490
  | 7 => 0x5212b1cc9139fe032856a180d89c488f1d11520c88460d69478650750580778b9a358e300000014f1ae1f5a3894b94280011da3c03617e1d19ee22a00015ea1b8511550018fd00013811b80019d0000e28021cc097a289219858001b088e00009a0002398000e61aa1d707f2110000608001949df8f90ed8a31921d2a2c99d8b880022e91e8f39ee9ae8a780000000019722306f89097d80002200013e1d312d85b00001290b0000000000132218641a401b1989459b30288000e40f116e1868318dc8a900d00014a0189250871120000001e11b3a071450e88000bb14197b80016c91719f1d7a178c09c51fa9e39708ba16d1820c600e1bd94a80003315a9670fe0000000000001b915f0f22281178000000000000001a984e82d8148001fb15096815c0310259e19a10aa1762340001570f794c0000000000e900020b92385621991d1189941af8500000450e380005181697107714c9d484585920f9c685e8000002368f5a3a1d391900001c82183e8ef0578002278eaa3b8648000000278001ad0000001e304200000000003f9731890ea09709004a8c38eb00013500017b19b07e02c08d8000000508000001c10000000001c79810941c207e87893b19f90392f84680000011000002e80013c9439081a480020b1210000108ad1930000a59f980000000022980015d0d3a3c9ab0c701518508420f07f9e99a50799b69c985a8d994e0638190488a21700559df0bf223a2f9da96aa068a521894d08010e8b61d891a81e05d9e78f012a1fa1ab9718fb80020d1b18199a691980000010980013d8000000001768001258001a7000029a330eca008db00b8b29f5086a208821770eb8cb1ad9fb8230c521a94420881e83008d00000000010a80000017d0000930c904280018a80000000000017f80000001f0000ab9bf9860000001830a00b704704b02d17c9780dc1c30ca8b50000001c004f98f01a8589bc9230001588002349e721b0001980be091a1399e8929569788001fd8002098a100000004b9d007c0001e60001da2061b280000886b12c0e080000020c00020808080000000d8b20848fa0c485f8a4a168b08000f52311978570c113f9a8852a3a90c8000002259998001a78001271630000000000000309ba8001f788516785c0530fc8000000000000001b88000b48209370de0ba92a8000000001bba091f1a1300000008610594201f8001b500000f13789510608e9fc08a19a93415e2010a981c17a1e01bf0000000d60f89029f38ac1490d583f0671cf92903a88a9dc1ce1f09791690001ac82b8102161938000a086a00020180021d9160000000d28910002030f70000000000000001d415b8000002079b10921e48000cc80
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc73588100067f53588100067d5358810006ef7258810006ee5258810006ed5258810006ee4258810006ed4258810006ee3258810006ed3258810084ff7158810114fd7158810084ff70588100b4fd70588100357e75188100057d751881002dbe7418810005bd7418810025de7318810005dd7318810006ed6218810084ff751881001cfe75188100867e751881001c7e7518810004fd75188100867d75188100047d7518810084fc7518810084ff7418810014fe7418810086be7418810014be7418810004fd7418810086bd7418810004bd7418810084fc74188100067f54188100067d5418810084ff731881000cfe7318810086de731881000cde7318810004fd7318810086dd7318810004dd7318810084fc73188100067f53188100067d5318810084fe7218810086ee7218810004fe7118810086f67118810004fe7018810086fa7018810004fd76c8410004ff7688410004fd7688410006ee6288410006ed6288410005fa7088410005f97088410004ff76484100057f75484100357c7548410005df7348410025dc7348410084ff7608410004fd7608410086ee6208410006ed6208410005fa7008410005f97008410004fd76c8010004ff7688010004fd7688010006ee6288010006ed6288010005f67188010005f57188010004ff76480100057f75480100357c7548010005bf744801002dbc7448010084ff7608010004fe7608010004fd7608010084fc7608010086ee6208010006ed6208010005f67108010005f57108010046f576c40101aef764c40101aef564c40101af7754c40101af7554c40101a77753c40101a77553c401018df57184010186f66184010025f9768401003ef9768401000cf9768401019f7b548401019f795484010196fb6384010196f963840101977b538401019779538401018df97184010186fa6184010007f26184010004ff76440100057f75440100357c7544010005bf744401002dbc7444010005df7344010025dc7344010005ef7244010005ec7244010005f77644010006f77644010004f7764401000777754401014f747544010007b7744401016fb4744401016ef7644401016ef5644401016f77544401016f755444010007d77344010167d47344010167775344010167755344010007e77244010007e4724401017df77044010176f6604401014ff2504401014ff15044010007f22044010007f12044010005fb7644010006fb7644010004fb76440100077b754401014f787544010007bb744401016fb8744401016f7b544401016f795444010007db7344010167d87344010166fb6344010166f963440101677b5344010167795344010007eb7244010007e8724401015dfb7144010007f37144010156fa6144010007f2614401014ff2514401014ff15144010007f22144010007f12144010
  | 1 => 0x8510004fe76085100067f65085100fe7c6508510006bf64085100f6bc6408510006df63085100eedc6308510006ef6208510086ec6208510007e52108510004fe76c81100067f65c81100e67c65c8110006bf64c81100debc64c8110006df63c81100aedc63c8110006ef62c8110086ec62c8110005f671c8110005f571c8110004fe76881100067f65881100d67c6588110006bf64881100cebc6488110006df63881100a6dc6388110006ef6288110006ec6288110084ff7648110004fd7648110004fc76481100057f754811005d7c75481100067f65481100c67c6548110005bf7448110055bc7448110006bf64481100bebc6448110006df63481100b6dc6348110006ef6248110006ec6248110005f77148110005f47148110004fe76081100067f650811009e7c6508110006bf6408110096bc6408110006df630811008edc6308110006ef6208110086ec6208110007e920081100067f65c411007e7c65c4110006bf64c4110076bc64c4110006df63c4110046dc63c4110006ef62c4110006ec62c41100077b65c41101e77865c4110007bb64c41101d7b864c41101d77b54c41101d77954c4110155fb73c4110155f973c4110007db63c41101dfd863c41101df7b53c41101df7953c4110007eb62c4110007e862c41101d7f241c41101d7f141c41100067f658411006e7c6584110006bf6484110066bc6484110006df638411003edc6384110006ef6284110006ec628411004df676841100077765841101cf7465841101c5f774841101c5f57484110007b764841101bfb464841101bf7754841101bf755484110007d763841101b7d463841101b77753841101b7755384110007e76284110007e46284110007f360841101b7f230841101b7f13084110004ff75d881001cfe75d8810004fd75d881001cfc75d8810004ff74d8810014fe74d8810004fd74d8810014fc74d88100067f54d88100067d54d8810004ff73d881000cfe73d8810004fd73d881000cfc73d88100067f53d88100067d53d8810004fe71d8810006f671d8810004fe70d8810006fa70d8810004fd7698810006ef6298810084ff759881001cfe7598810004fd7598810084fc7598810084ff7498810014fe7498810004fd7498810084fc74988100067f54988100067d5498810084ff739881000cfe7398810004fd7398810084fc73988100067f53988100067d5398810086ee5298810006ed5298810086ee4298810006ed4298810086ee3298810006ed32988100057f75588100357c7558810004ff75588100067f75588100047f755881001cfe7558810004fd755881001cfc75588100067c755881001c7c7558810004ff7458810014fe7458810004fd7458810014fc74588100067f54588100067d5458810004ff735881000cfe7358810004fd735881000cf
  | 2 => 0x6f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed6218910084ff751891001cfe7518910004fd7518910084fc7518910084ff7418910014fe7418910004fd7418910084fc74189100067f54189100067d5418910084ff731891000cfe7318910004fd7318910084fc73189100067f53189100067d5318910086ee7218910006ef5218910086ee5218910006ed5218910086ec5218910006ef4218910086ee4218910006ed4218910086ec4218910006ef3218910086ee3218910006ed3218910086ec3218910104fe7118910084fc71189100a4fe7018910084fc7018910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac64189100076f54189100076d5418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d5318910007e64118910007e54118910007ea3018910007e93018910086ef7518910006ee7518910006ed7518910086ec7518910086ef7418910006ee7418910006ed7418910086ec7418910006ef54189100066f5418910006ee5418910006ed54189100066d5418910006ec5418910086ef7318910006ee7318910006ed7318910086ec7318910006ef53189100066f5318910006ee5318910006ed53189100066d5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec4318910086ef7118910006ed7118910006ef5118910006ee5118910006ed5118910006ec5118910006ef4118910006ee4118910006ed4118910006ec4118910006ef3118910006ee3118910006ed3118910006ec3118910086ef7018910006ed7018910006ef5018910006ee5018910006ed5018910006ec5018910006ef4018910006ee4018910006ed4018910006ec4018910006ef3018910006ee3018910006ed3018910006ec3018910006ed1018910004fe76c85100067f65c85101467c65c8510006bf64c851013ebc64c8510006df63c851010edc63c8510006ef62c8510086ec62c8510005fa70c8510005f970c8510004fe76885100067f65885101367c6588510006bf648851012ebc6488510006df6388510106dc6388510006ef6288510006ec6288510004fc76485100057f754851005d7c75485100067f65485101267c6548510006bf644851011ebc6448510005df734851004ddc7348510006df6348510116dc6348510006ef6248510006ec6248510005fb7048510005f8704
  | 3 => 0xc65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d89100076f54d89100076d54d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d8910007e641d8910007e541d8910007ea30d8910007e930d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d89100066f54d8910006ee54d8910006ed54d89100066d54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910006ef30d8910006ee30d8910006ed30d8910006ec30d891005d7e75989100057d75989100067f65989100067c6598910055be7498910005bd7498910006bf6498910006bc649891004dde7398910005dd7398910006df6398910006dc6398910006ef6298910084ff759891001cfe75989100867e759891001c7e7598910004fd75989100867d75989100047d7598910084fc7598910084ff7498910014fe7498910086be7498910014be7498910004fd7498910086bd7498910004bd7498910084fc74989100067f54989100067d5498910084ff739891000cfe7398910086de739891000cde7398910004fd7398910086dd7398910004dd7398910084fc73989100067f53989100067d5398910084fe7298910004ee7298910004fd7198910086f57198910004fd7098910086f970989100057f755891005d7c75589100067f65589100067c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df735891004ddc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef7258910004ff7158910
  | 4 => 0x9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110056be71d9110056bd71d9110056bc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf70d9110056be70d9110056bd70d9110056bc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110056bd10d911004dde76d8d1004ede76d8d1000cde76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075f54d8d100075d54d8d10007d641d8d10007d541d8d10007db70d8d1004fd870d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d100065d54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1004ede71d8d1004edd71d8d1004edc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df70d8d1004ede70d8d1004edd70d8d1004edc70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d1004edd10d8d100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef42d8910006ee42d8910006ed42d8910006ec42d8910006ef32d8910006ee32d8910006ed32d8910006ec32d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076
  | 5 => 0x84ff7518a1001cfe7518a10004fd7518a10084fc7518a10084ff7418a10014fe7418a10004fd7418a10084fc7418a100067f5418a100067d5418a10084ff7318a1000cfe7318a10004fd7318a10084fc7318a100067f5318a100067d5318a10084fe7218a10086ee7218a10086ee3218a10006ed3218a10086f57118a10086fa7018a10086ee62c8610006ed62c8610005fa70c8610005f970c8610006ef6288610006ec62886100057f754861006d7c7548610005df734861003ddc7348610006ee6248610006ed6248610005fb7048610005f87048610006ef6208610086ec6208610006ee6288210006ed6288210005f67188210005f571882100057f754821006d7c7548210005bf7448210065bc7448210086ee6208210006ed6208210005f67108210005f57108210007e92008210005f576c4210006f576c42101f6f764c42101f6f564c42101f77754c42101f77554c42101ef7753c42101ef7553c4210005f976c4210006f976c42101f77b54c42101f77954c4210185fb73c4210185f973c42101ef7b53c42101ef7953c421005d7e76d951005e7e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100077641d95100077541d95100077a30d95100077930d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951005e7e71d951005e7d71d951005e7c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f70d951005e7e70d951005e7d70d951005e7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d951005e7d10d9510055be76d9110056be76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110007b771d9110057b471d9110007ba30d9110007b930d9110006bf75d91100063f75d9110006be75d
  | 6 => 0xd73d8b1000cfc73d8b100067f53d8b100067d53d8b10006ee42d8b10006ed42d8b10006f671d8b10006f970d8b10004fd7698b10006ef6298b10084ff7598b1001cfe7598b10004fd7598b10084fc7598b10084ff7498b10014fe7498b10004fd7498b10084fc7498b100067f5498b100067d5498b10084ff7398b1000cfe7398b10004fd7398b10084fc7398b100067f5398b100067d5398b10086ee3298b10006ed3298b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10006ef7258b10006ee3258b10006ed3258b10006ed6218b10084ff7518b1001cfe7518b10004fd7518b10084fc7518b10084ff7418b10014fe7418b10004fd7418b10084fc7418b100067f5418b100067d5418b10084ff7318b1000cfe7318b10004fd7318b10084fc7318b100067f5318b100067d5318b10084fe7218b10086ee7218b10086ee4218b10006ed4218b10086f67118b10086f97018b10006ee6288710006ed6288710005fa7088710005f970887100057f754871007d7c7548710005df7348710045dc7348710086ee6208710006ed6208710007e52108710005fa7008710005f97008710086ee62c8310006ed62c8310005f671c8310005f571c8310006ef6288310006ec62883100057f754831007d7c7548310005bf7448310075bc7448310006ee6248310006ed6248310005f77148310005f47148310006ef6208310086ec620831006d7e75d8a100057d75d8a1003dde73d8a10005dd73d8a10004ff75d8a1001cfe75d8a100067e75d8a1001c7e75d8a10004fd75d8a100067d75d8a100047d75d8a1001cfc75d8a10004ff74d8a10014fe74d8a10004fd74d8a10014fc74d8a100067f54d8a100067d54d8a10004ff73d8a1000cfe73d8a10006de73d8a1000cde73d8a10004fd73d8a10006dd73d8a10004dd73d8a1000cfc73d8a100067f53d8a100067d53d8a10006ee32d8a10006ed32d8a10006f571d8a10006fa70d8a10004fd7698a10006ef6298a10084ff7598a1001cfe7598a10004fd7598a10084fc7598a10084ff7498a10014fe7498a10004fd7498a10084fc7498a100067f5498a100067d5498a10084ff7398a1000cfe7398a10004fd7398a10084fc7398a100067f5398a100067d5398a10086ee4298a10006ed4298a10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a100067f5458a100067d5458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a10006ef7258a10006ee4258a10006ed4258a10006ed6218a10
  | 7 => 0x8420005df735842008ddc7358420086f46158420004ff75584200067f75584200047f755842001cfe7558420004fd755842001cfc75584200067c755842001c7c7558420004ff7458420014fe7458420004fd7458420014fc74584200067f54584200067d5458420004ff7358420006df7358420004df735842000cfe7358420004fd735842000cfc7358420006dc735842000cdc73584200067f53584200067d5358420006ee3258420006ed3258420006f65158420006f55158420006f64158420006f54158420006f63158420006f53158420086f72158420086f42158420004fd7688420005ed7688420006ed768842028eef648842028eed648842028f6f548842028f6d548842025def738842025ded73884202876f53884202876d5388420085ee7188420006ed6188420005ed708842027eee6088420004ff76484200057f754842009d7c7548420005df734842008ddc7348420086ef6408420276ed64084202776f54084202776d5408420085ef730842026ded73084202676f53084202676d530842025dee7108420087e67108420087e66108420006ed6108420087e56108420006e56108420087ea7008420005ed7008420087e97008420005e97008420256ee6008420086ef64c802024eed64c802024f6f54c802024f6d54c8020085ef73c8020245ed73c802023f6f53c802023f6d53c8020005ee71c802021ded7288020236ee628802022f7b548802022f7954880202277b5388020227795388020085f97288020086fa6288020087ea6288020087ea3288020227e93288020007ea2188020087e82188020004ff76480200057f754802009d7c7548020005bf7448020095bc7448020005ef7648020006ef7648020004ef76480200076f75480202076c7548020007af74480201ffac74480201feef64480201feed64480201ff6f54480201ff6d544802021def734802021ded734802020f6f534802020f6d5348020005ec7148020085ef7048020216ee6048020207ea5048020207e950480201ffeb40480201ffe84048020085fb7648020006fb7648020004fb76480200077b7548020207787548020007bb74480201ffb874480201ff7b54480201ff79544802020f7b534802020f795348020085fb7248020007eb7248020086fa6248020087ea6248020087ea5248020207e952480201ffeb4248020087e84248020087eb2148020007e9214802007d7e75d8b100057d75d8b10075be74d8b10005bd74d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10004ff74d8b10014fe74d8b10006be74d8b10014be74d8b10004fd74d8b10006bd74d8b10004bd74d8b10014fc74d8b100067f54d8b100067d54d8b10004ff73d8b1000cfe73d8b10004f
  | 8 => 0x6bd31d9120006bc31d9120006bf70d91200bebe70d91200bebd70d91200bebc70d9120006bf50d9120006be50d9120006bd50d9120006bc50d9120006bf30d9120006be30d9120006bd30d9120006bc30d91200bebd20d91200067f65d85200067c65d8520006bf64d8520006bc64d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d8520006f731d8520006f431d85200c57e75985200057d75985200067f65985200067c65985200bdbe7498520005bd7498520006bf6498520006bc6498520006f761985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520006bf6458520006bc6458520005df73585200b5dc73585200067f65185200067c6518520006bf6418520006bc6418520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520004ff7418520014fe7418520004fd7418520014fc74185200067f54185200067d5418520004ff731852000cfe7318520004fd731852000cfc73185200067f53185200067d5318520006ee4218520006ed4218520006f73118520006f43118520004fe76c85200067f65c85201467c65c8520006bf64c852013ebc64c85200067f65885201367c6588520006bf648852012ebc6488520006f76188520006f46188520005fa7088520005f970885200057f75485200c57c75485200067f65485201267c6548520006bf644852011ebc6448520005df73485200b5dc7348520006f76148520006f46148520005fb7048520005f87048520004fe76085200067f65085200fe7c6508520006bf64085200f6bc6408520007e521085200067f65c81200e67c65c8120006bf64c81200debc64c81200077b65c81202c77865c8120007bb64c81202b7b864c81202b77b54c81202b77954c81202bf7b53c81202bf7953c8120087ea42c81202b7e942c81200067f65881200d67c6588120006bf64881200cebc64881200076f65881202af6c65881202a5ef74881202a5ed7488120007af648812029fac648812029f6f548812029f6d5488120296ef6388120296ed63881202976f53881202976d5388120006ec6188120007eb6088120086f76198420004ff759842001cfe7598420004fd759842001cfc7598420004ff7498420014fe7498420004fd7498420014fc74984200067f54984200067d5498420004ff739842000cfe7398420004fd739842000cfc73984200067f53984200067d5398420006f65198420006f55198420006f64198420006f54198420006f63198420006f53198420086f72198420086f421984200057f755842009d7c755
  | 9 => 0xd7088620007e970886200057f75486200d57c7548620005df73486200a5dc7348620006f66148620006f56148620005fb7048620005f87048620005ed7608620006ed76086202e6ef64086202e6ed64086202e76f54086202e76d54086202ddef73086202dded73086202576f53086202576d5308620007e67108620006ed6108620005ed7008620005ed76c8220006ed76c82202d6ef64c82202d6ed64c82202d76f54c82202d76d54c8220235ef73c8220235ed73c82202cf6f53c82202cf6d53c8220005ee71c8220005f976c8220086f976c82202d77b54c82202d77954c82202cf7b53c82202cf7953c82200c57e76d95200c67e76d952001c7e76d95200057f74d95200057d74d95200067f64d95200067e64d95200067d64d95200067c64d95200073c64d95200063c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200076e42d95200076d42d95200067f74d95200047f74d95200067e74d95200067d74d95200047d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95200c67e72d95200c67d72d95200c67c72d95200067f42d95200067e42d95200067d42d95200067c42d95200067f32d95200067e32d95200067d32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95200067f70d95200c67e70d95200c67d70d95200c67c70d95200067f40d95200067e40d95200067d40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d95200c67d20d95200bdbe76d91200bebe76d9120014be76d91200073f75d91200073c75d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006bf63d9120006be63d9120006bd63d9120006bc63d91200073f53d91200073d53d9120007af72d91200bfac72d9120006bf75d91200063f75d9120006be75d9120006bd75d9120006bc75d91200063c75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d91200063f53d9120006be53d9120006bd53d91200063d53d9120006bc53d9120006bf72d91200bebe72d91200bebd72d91200bebc72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf32d9120006be32d9120006bd32d9120006bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006be31d9120
  | 10 => 0x8421087e43248421086fb6098021004ff759802101cfe7598021004fd759802101cfc7598021004ff7498021014fe7498021004fd7498021014fc74980210067f54980210067d5498021004ff739802100cfe7398021004fd739802100cfc73980210067f53980210067d5398021006fa5098021006f95098021006fa4098021006f94098021006fa3098021006f93098021086fb2098021086f820980210057f75580210fd7c7558021005bf74580210f5bc7458021086f86058021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021006bf7458021004bf7458021014fe7458021004fd7458021014fc7458021006bc7458021014bc74580210067f54580210067d5458021004ff735802100cfe7358021004fd735802100cfc73580210067f53580210067d5358021006ee4258021006ed4258021006fa5058021006f95058021006fa4058021006f94058021006fa3058021006f93058021086fb2058021086f82058021086f76198720004ff759872001cfe7598720004fd759872001cfc7598720004ff7498720014fe7498720004fd7498720014fc74987200067f54987200067d5498720004ff739872000cfe7398720004fd739872000cfc73987200067f53987200067d5398720006ee4298720006ed4298720086f72198720086f42198720086f46158720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc74587200067f54587200067d5458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d5358720086f72158720086f421587200057f75487200e57c7548720005df73487200addc7348720087e421487200d57e75d86200057d75d86200a5de73d8620005dd73d8620006f76198620004ff759862001cfe7598620004fd759862001cfc7598620004ff7498620014fe7498620004fd7498620014fc74986200067f54986200067d5498620004ff739862000cfe7398620004fd739862000cfc73986200067f53986200067d5398620006f64198620006f54198620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620014fe7458620004fd7458620014fc74586200067f54586200067d5458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d5358620006ee3258620006ed3258620006f64158620006f54158620006f56118620006f66188620006f56188620005fa7088620005f970886202f6ef64886202f6ed64886202f76f54886202f76d54886202edef73886202eded738862027f6f538862027f6d5388620007e66188620006ed6188620007e56188620007ea7088620005e
  | 11 => 0x6df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d210067f65c85211467c65c8521006df63c852110edc63c85210077765c85213877465c852137f7754c852137f7554c8521007d763c8521377d463c85213777753c85213777553c8521087e632c8521377e532c85210067f65885211367c6588521006df6388521106dc63885210076f658852136f6c6588521366ef6488521366ed64885213676f54885213676d5488521315ef7388521315ed7388521007cf638852135fcc638852135f6f538852135f6d5388521007e761885210067f65d81210067c65d8121006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006fb40d8121006f840d81211257e75981210057d75981210067f65981210067c6598121115de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211257c75581210067f65581210067c6558121005bf745812111dbc7458121005df7358121115dc7358121006df6358121006dc63581210067f65181210067c6518121006df6318121006dc6318121006f96018121004ff751812101cfe7518121004fd751812101cfc7518121004ff7418121014fe7418121004fd7418121014fc74181210067f54181210067d5418121004ff731812100cfe7318121004fd731812100cfc73181210067f53181210067d5318121006ee3218121006ed3218121006ee2118121006fb4018121006f84018121085ef74c8421355ed74c842134f6f54c842134f6d54c8421086ef63c8421346ed63c84213476f53c84213476d53c8421005ee70c842133ded7288421336ee628842132777548842132775548842132f77538842132f755388421085f57288421086f66288421087e66288421087e64288421327e54288421004ff76484210057f75484210fd7c7548421005df73484210eddc7348421005ef7648421006ef7648421004ef76484210076f75484213076c754842131def744842131ded744842130f6f544842130f6d5448421007cf73484212ffcc73484212feef63484212feed63484212ff6f53484212ff6d5348421085ef7148421316ee6148421307e65148421307e551484212ffe731484212ffe43148421005ec7048421085f77648421006f77648421004f7764842100777754842130774754842130f77544842130f755448421007d773484212ffd473484212ff7753484212ff755348421085f77248421007e77248421086f66248421087e66248421087e65248421307e552484212ffe7324
  | 12 => 0xd7498221014fc74982210067f54982210067d5498221004ff739822100cfe7398221004fd739822100cfc73982210067f53982210067d5398221006fa3098221006f93098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221004fd7458221014fc74582210067f54582210067d5458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d5358221006ee4258221006ed4258221006fa3058221006f93058221006f960182211257e76d95211267e76d952101c7e76d95210057f74d95210057d74d95210067f64d95210067e64d95210067d64d95210067c64d95210057f73d95210057d73d95210067f63d95210067e63d95210067d63d95210067c63d95210075c63d95210065c63d95210076e32d95210076d32d95210067f74d95210047f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210047f73d95210067e73d95210067d73d95210047d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95210067f72d95211267e72d95211267d72d95211267c72d95210067f42d95210067e42d95210067d42d95210067c42d95210067f32d95210067e32d95210067d32d95210067c32d95210067f71d95211267e71d95211267d71d95211267c71d95210067f41d95210067e41d95210067d41d95210067c41d95210067f31d95210067e31d95210067d31d95210067c31d95211267d21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067f30d95210067e30d95210067d30d95210067c30d9521115de76d8d21116de76d8d2100cde76d8d210075f75d8d210075c75d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d21007cf72d8d21117cc72d8d21006df75d8d210065f75d8d21006de75d8d21006dd75d8d21006dc75d8d210065c75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d21006df72d8d21116de72d8d21116dd72d8d21116dc72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df42d8d21006de42d8d21006dd42d8d21006dc42d8d21006df71d8d21116de71d8d21116dd71d8d21116dc71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006de41d8d21006dd41d8d21006dc41d8d21116dd21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21
  | 13 => 0x1f00000000000000400000200100c00100300700500300100000000100001200000000100202000000500200000800e00000000000001100501600a00000400800401001e00b00700000a00000000300500601000300201a00100000800600401d00601c00000200100f00b00600500700000a00402600300500900200b00d00900400600d01300d00400a00600500700502500001200000000300600003e00000200a00200100300600300100c00000300f00001100100400300800000300e00d00400200300e00000000200f00100100400500101300000200200500900300a00000000400000200000500100a00000000700300100500000700000000000300300102100c00100100b00600000100100500000000001a00300000200200a00000800100200000902f02000500500100500c01103a00e00400100400200a00e03f00600002300000200000502d00100100500400000100100000000000202900000500000300000300701000001600000100200000500800a00100300700400000601000700a00600300800900000000700b01000500000b00000002500a00000f00002b00000100700100300001b00100e00d00400800600000000100b01400902f00001800102700000300000000300200004400100100201701000000600300102100000300700000200700100500201200a00100001e00301001600300000100200000500200001100000900200001800100a01802f00300200004600200000100000901600200200000000400200e00000000100900100d00c00b02600700500f00000001300000d001086fb6098321004ff759832101cfe7598321004fd759832101cfc7598321004ff7498321014fe7498321004fd7498321014fc74983210067f54983210067d5498321004ff739832100cfe7398321004fd739832100cfc73983210067f53983210067d5398321006ee3298321006ed3298321086fb2098321086f82098321086f86058321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321004fd7458321014fc74583210067f54583210067d5458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d5358321086fb2058321086f82058321005ed76c8621006ed76c86213a5ef74c86213a5ed74c862139f6f54c862139f6d54c8621396ef63c8621396ed63c86213976f53c86213976d53c862138fe651c862138fe551c8621005ee70c8621005f576c8621086f576c862139f7754c862139f7554c86213977753c86213977553c8621087e652c862138fe552c86211357e75d82210057d75d822112dbe74d8221005bd74d8221006fb6098221004ff759822101cfe7598221004fd759822101cfc7598221004ff7498221014fe7498221004f
  | 14 => 0xb9800036d8000ce06e205e07184ac52800016c099c84314718282d62b2000000058e22922d800052c86e000192000051a00011180001d90000cb0dda2380171a1c0000002f619140001b630980005168ad31c8124b302df1a8958c2ea00014d80000008894120c288267d105595641508d43c81368c8081930880006fc36b44f800000000000020489d26ee2250f908640003a508ac8be6c1460202800003800000000000000000000b821bb1fe8000b8c00031200000ec51f41000000006a023d193025857507900005082e103a8dd800011300012640001a4000091000048a245800092001238b9b210f826412d00011225713ae0facfb60041909a08a2a0000000000d0818401e1004a9217a3ee8000cce57700000008200000f49d4c7261391a31404df206207f82f80005483cc000111044917b80007040001d01ddc000000000160800000000013703a87eb00022c400024e000000057e27b3b100000000000b380011820000d08ea9074627243892d0d63b100000003361301c4228cad800008f07f4de07133bf1ce095c0b9209218c00011d4388000ca26970001e5106404800009fd0c201435216a800043a0391634a4676b00000008fe00019b01640006be31700000003ee01608d883621500000011de00100100c00100400000000400100000000100000700000800400700000100200300401200000300000400400500600001500100400100100000300100102200a00100000000200100000300002100000000300900000400300700a00a01800200500500000200a01500001a01500000000000400001800400000200b00200800000000000000100800200200000100200000100d00400c00000000700000600000300000001100200100900b00400800000100000900100400001900600e00000301a00400201100000100500100400000100100000d00601e00100500200001e00d00000000a00700800102f00801000000500500400100000500000100200600000700800a00100b00100601001200900800700700300400000d00200a00100000000700000300000100100401000d01000301c00500000002400800001c00000f00100000100000d00300001500300000300000100000800100300000c00000000000300500f00700500000300101600101300500a00900900300201400000000200000200400a00400100200700000000000000901f01f00400800001200200200500500e00200b01600100200000000700900000600000900100300002d00700000301300000200b00c00401800a00000000301900000b01500401901000800e00600300300000200100000000100b00500000101100003200203700000000000500000300700901000001e00100800200000500200300000200500000000600000000100000100
  | 15 => 0x3368cb480c66b385961400024a06a9ff4a2060537a947100e0d02491f3c45a5fe09516901d65d90e60aa80fc66e46991e0fd01ca14e20f800000e1dc08580008860840fc10e65bd0030f245801bc29380000002bc00009781480001071f5c0000004119d2414c0003c6a1e03c60000bf1d84ad05fc02080005ac52e1bd9e1872a2800470000cde7ed3f79d18e846f12d78c4400230121219a8bbc3423c89c4076c5063709d9400e3db3a68e180005642618c745a034c37585402da7570e41534d8a701368137402e78715410e4aec5ad24990c0a6e4163cb0000b2600032507e45100000000c24f36708463226cab60000000f9c6ae00032b94bc350000000000000032800015ec0006023c59e8c0000002e412180008760001edcd38000000000025c8f20bb0c086dc3d71488278cb0522268993c12853f28483351b010c23f0f3c3628bf0788d4895a48f37600849d8690150a3400004a241b232000068033a93a8dc6688175850c3827ae4081c1871a5042988ca82a44191c01ae905881c46714e903c5c707f1c7041a00016195ad12c135043930028453327a2188d024833ff8e14a1c2141c71de400087b3f505283d60000000000f740571239d100000000001b581440000001e7c62408d0000934646000000056c29689e0000804be85d21328d143ea63b00002187740000b30b98e188b44420fa8be43c747500007428e22b7800054e6190002250eea000000239c38e50d0690000bd20002fd800055288e321986ca8600005180000004433c61e10de451d00015cc39242c43280000d46283bd800067c0001f4800020846646d0000d44671098938400000000000005707bd000153c66a000000000000076a00000000003d0000000002a0000000a683be000254133c00000000017fc00085500000002e410a0001d386f20ec1d386e87764c90000328b2200024b0000afe6b305c10a0c661bf41b8000e907dc1740a7c68872d4151e9057407a2f5102cf7e6b604d9c0002c4270320bb11e253d0000b8c0000001e1000057c3a23118000e061e131c10d05285c900012840005c215c961c0741b40f307809307f323e8000c9a4bc000132800081723a80000000000000ea000081300011a90fa000000000000000000020e50f20003fe000110000036300010b804c20111bc4c477d1c1849c78c6bd1369a84c0c6520a88bd86908273539e787aa182000000031a00002e0b5c0003ab3f8a3acb440fa3ac9d0000073136a0be115c00026319f86000001aa9bf8b0602317a9790aaa5a902780011148023f004acffc5342ce881c0186211001460d0a79d22015041841732291804b7600f1b40068cca8b82d620fc9628264380c2111a87e38f12c84a04c71d60c60ba010306499fc59409046c9ac054c3ce45217d4f4c15c0629998064503227809c
  | 16 => 0x400072842c861c48c000000000029c1473741b9c0000002f7800000000008386511b800002012500000003020000ec07d200022bc00025d0830e74f148b60001cb08d637a36e20c035200009005f42663cd45e98d91720003d11d6c83a00038f800000050540213509ac00007c00004467b0312800000031f1f792e06400701358000000000029800016886c0000f789462850c59ee474645e2d5800009674c0002314174364000000115606b28596f10361a514b8000cac000000000000069e00013080005071b880984de7830db9a6c58a8ac0001ca88ac0001e5800014a046422000039e4853d4000000041516721dc31e7f93b90a251260a93068abd0848a03461278c0089a037000c6c22f220d0b18dde74100007dcd5a02040c15140008580000000c288b3359101c42065944a94290788e92c40e3003e2ee145058c00020c39d0b600880002b680009be5e22cb9f009f40003169fd800030411080001764d800013a00003411208000eac5c53311d740001211021d7c6b46302d980c4a6c7c4000198c0b685000000000600001c90d0007a3c00c98e3d0443ed09f817c4b673337b1650af80000001ce41c44f028102705b432921b991c4b241e0bd882c97e0000ce17b49d649b05b8000ee800039109f03e41791be9f1c88806016997c4d5033804d00290340da13f21a03fe30d10e943d1846983970000d527e21518bfcf342740cf0e6400082d4650e604685d730e08c847c6602af178485271922986b81422cf04c0000a007df25e9ae08da59628b1ba43f01230000000a8029d345054c38600024008a02820000000214c4c000000000024a26800007540001bd2981fb8b6e5a000000001122243c1014860c1880000000000000000103800000038522a800061510e1028c2e4973390f04000396000080cf2e7b109c22404ec4141729908a4029e038915d05285219e9558e7a3da3049560b0c1371ae86f88e00191fe0bec32c0000000000e6e8e400000000000003690f74bca00004996f909c2d12860ab90284602ad0000abe2ed00021145d200007794e40001ef21180000001fa06fa3580000000e7025ce048cb000022cc3c171000037487a76f1b11dcd0b631e29290ec00037807280006e00003f821000005e325b9b30e4c00017a22ec4326df2a61d9c0003b50001c9435650839d927d1c200000002041582092bc0a88f0a3d327704c80007b5231027ce1e0003c711f02680001180c9465683444299f4384000135053c9a681600007b908e05000011dc85600000003181cc18a1b607cc2b005e12e01348ec6a3000169c6a81570c281e11d8000000119502a14045b974cbce0d80001bfc0007632659f1477817c20790151ca1aa37e1b6822a2fc1ee000000071d3e18f8877c2b10d782bd1a21141a50488cd865d2aa076055831a
  | 17 => 0x82280000fce41c1d8214475a833000000006a0680c89e80ce62403c79e8400085f1e6237830c6fd0000c3800000000000010ac8a90000c98eec77c062231c0001450001abc2be12f2691080ca00001921c44ee04cd33c1c14c9c468000138800058b0000280f8c8381a5800000029518a11500e87d60000000afc3a90000fd069a00001280008c80000da9c8000011a2209f20be08b50b8188043e80c08f9eec41e4de02e9de82de5a117f203c0008f02410ad03e20963060dbcd9423d00013f424c4d521793902aa3030b089a4ce823308486247086c000e1bec0723f12a2180c3b62172408cc4b5c4cc20c019862c2b51371ca49fe5350c71274ff00002dd0fc835a0cc00000009381dc3ec8001092000000000080000000000007f40000001b988dc0000001954d4a13c28a05b01c64b92d1a3a05de6c21b18ee4f940d603e1f6900a00000000000007884591a0c0000000001b78af481f00012b08667160708f0ca580113620d4c82e0e904e8518f385cd2ce10d859a0aa3588da40007ad2e00a0cace0000598150ca603b00016c8d1e1a309487d800087a404a2f071686f2c70bc40004591860000a7c0003871f3889c0003e800000124c41858bc02506bb155a3b400448e23a20f44c059211100000006160110000fc800805e9c483966dd0b7000000029202393f80000000000000e280000000b2c0004670c00e6d13a1b231e9b901085ce1f621500003ae000000098a4ed1998b650827c23b49ab80002e20000000e7e0003e48000aa20000a41b2c00015e29d81a49540000000000e1228f00000009340001939168a2e22636c9598d5477f47197a01603e312498a887848c0cd09e86781b3149846416459522e83d01b237319118d4fbc02f25793c8ea8077067831cafa3fe278a20c03a7503469518cee0000000000f32000000000000052a30393d86ce7e900000000000001ce1c34bf400014c09b06ca34e1ca1574a2688706a0c4c8120ee21698a40006c90dc1bdcf786bc00000000003431f980000000ed00000003180003ec0344bb004300000011cc435161100c4761243df000117415426c9c90f260000000b748708cc45284d85325b10eb800000082e414000109e06c25483f47ac76d0dc8000a223a400017805040004581cf119200000003f00b400035a89300000002c600000006a60479f30ebc07b32e2260e361e42eb16d8a7053c0ff0390000000221211800016535c9628e467952ba1c1ccb47520000880c8c49500000002c867934fa22c7b05dc3820be4000000000000000000003980fc15c06116da3810a65ca2cc955c5a467c00000007344f345095c00000002a58b206b000002a843c1b86f41fb87ec00000041d89c800048d4128000c8861f1d28df040c267002944885442e0c9112c7201ed3d79be096c28c0000f4
  | 18 => 0x5400036d0001224c1c1c00bc04403a662b202237d09a00000001b4e6809509f030c77a86000005a872e3af1a7966873c59006099d825a8693f280000008a205b00cc8b04ba264152914c7cd0099548b085f74461b1cf540000001244b120000000d640000000000b780004b416e00000004f700005dc1ee0ea1b3000096a8741599fb084c0d3372a1a801a4fc2718000c9672f00009c00000000ed1b540000002529dc400076c00009cc7cc1f41fc1be8b3e5b9143146501668600005103207e131f98b0788718000095c0001122b70908f003b344b94909b646c0d307c09f039f2eea2088a200015b12804547a71a49f50bdc0004338c409ca1b032a135c89821e37980407021dd0f50f48d2c0291e518dc47247312420007b2350070182c7fe08233d058077e00000006b003674b35b800065e37508e000000000000000000000f6000197c0002782348688fea4791af80000005a63f909dc3ac69d08d8b0409423c3208b243300000589210f0203400004e87140004189cd403c1973d996e017e06f3e09a38bbe40d0000fa101a000104187429a00014689e4298000223a26447e2810808000e4e69102c21201bc8111b006640008dd4040f8000000018d8000ad400046681089c06320000000426000015800000071543909d509637700013ecac42521438000e600990ca9d0c1906922fc869c1803562f99f980fe2ad12a18bc3a20000b48000eb45b436c15700000000e680000000000000f7c00022e1029594da20f300000000006bf0000c3c06c67b183824900600000000000000000000000faa00040e907c0008011db80000000000001ea40007322948000b3600019b963cdc06182b90000a5a00000005681140db000002c00025f0000cc0a565bf0001da0af24ef0bf918488a3470001e48ecc82b09d9b38ba25504321fed0ea000152019422200008b9ee09105eb08688e876468b46902005601c41d3091400021a2c01b34ba832e2319ed01d01d02e787a0bb444d000000049e00021f929c4a633a22a9d1c00040818c8c5d0ae66800022480003f910880000006690001d90000149000151ccc872100013d400051e044090cf962f300016d403038715e8b540001a0000231000061a056800000000021880008183054541a5446a000000158400035b0f28d78d120003d2818cf5800009e9cf8000699000035cda661002b1290000227087000000033446a9120bec0f032d9848ac0028000153807c0001b500000005d51fb1b0cb4a80603e8f1519e4e60ae8c5400041100000000001051660cec00000000000000000002a98bf42ac526015000113871a00017f506a5e6239000096600021096780007f708c000000029034a21980005db2fc1b3cf12271255a17854a0671f0a20446e3fb0670e4505e65e1051b5c6727e30e2950846221
  | 19 => 0x3f86081738b1104226600018f80000000001d3c00020217503d400000000007b0c7845c25f1f4c0008ee000000000000000000000001590001cad11e22f00012980005cb13e80002160004071d1514e21b46d80010fe6ea1ae000000000000000b406e11616a18d09ce19d0800f200008be25d9cd85761d21ba084809c17412c02441ce6933fa130408a0003ac1710c6233f17000000007fa15b87887ca08c1b909844a21de0b100000007551ea1d440007ab17d000030276e2e181446646493db05a0c74000000000000000046183e43ce000000213000047b0000e24000000238800000069a0000000a36000211000000000046b96a016a0000000000d560001720ed0106000000000000084a000160419685d1319ad0c44661436a16830619f00015a40000a718e00000004d0000000044a0fb00001e4c1e1021bf94844580003d9109487c4b000000909f22a000000000007780000fd400053235609
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6f75d8920440018d8ebb1240880032bdd36248110006563a6c49022000c6f7518920440018d8ea31240880032bdd06248110006563a0c49022000cd463dc520440019a8c638a408800339d88714811008574432401022000e6b65480204407fd50c89004088003aa19062c411005e3b3b6cb082200acb676d9210440139acedb1c2088003399db6284110086733b0c50822000ec46318a104400587ce8aa6c4080030f5d154d881000e2f39aa7b102000c5d7354f620400587ce8aa4c4080030f5d1549881000e2f39aa73102000c5d7354e6204001c5aa8a14c4080039354d329881001c3f43eeab10200087d84dd562040010fb07baac4080021fa1c75588100051ec20eab102000a5d831d562040010ff0aba2c40800e1f21574588100047c402e8b10200087e87d5162040070f90faa2c4080021fa1d54588100043e43aa8b102002c3e74551620400187ae8aa2c4080021fe15735881001c3e42ae6b1020008f4815cd62040010fd0fa9ac40800e1f21f53588100043f43aa6b10200087c8754d62040038bce6a9ac408003175cd535881001e363aca4b1020038ec8754962040051d90ea12c4080038b55142588100057440284b1020018ec874c96204001c9aa6992c408002b9205325881008637312ea3102010cae625d0620402199cc4b98c4080023be1d621881000636baac43102000cad74588620400199ae6b10c4080021fe1175188100043fc1aea3102000c3e855d0620400187b0aba0c40800e1fe1f54188100043ec3ea83102002c3e74d50620400187ae9aa0c4081e3179cf54188100043fc3aa8310200087d87550620400587ce8aa0c4080030f5d154188103be2f39aa83102000c5e855cc62040018bb0ab98c40800317d5173188100062eaa2e6310200387f87d4c62040010fb0fa98c4081db0f9d353188100061eba6a63102001c5e73d4c62040018bae7a98c4080021fe1d53188100043ec3aa63102075c3e7454c620400187ae8a98c408007179cd53188100062eb9aa6310200387e85dda21040010fb0bbb4420800a2fa1376884100045ec26ed1082000ce9629c221040070fd0bbb440080021f617768801000c6f41eed10020008dd83dda20040019cac538c40080423d61a71080100063a3aeec8802000cb474dd910040019a8e7bb220080031dd5376440100063aaa6ec8802000c7753dd910040018eaa7bb220080031dddb75440100065bbb6e88802000cd776dcd10040019ceedb92200800339dd87244010006e2398e48802000b738548110040018f0ebbb220080032e1d376440100066c39eec8802000c7b54dd910040018f2a9bb220080031ed4f76440100063ca9eec8802000c7b76dd51004001976edba2200800336ddb734401000675bb6e48802000ceb761c91004001b50e83922008002dce152144010
  | 1 => 0x301218c4880029ba15431891000536c2a8631220108ee8710c62440011db0e218c4880029ba14431891000536c28863122000a6f855c462440014d90ab88c488002b3e0d71189100056641ae23122000ace83d44624400159b07a88c488002aba10511891000556c20a231220108ee87d0462440011db0fa08c4880029ba17411891000536c2e823122000e2d54d04624400159d07a08c488002b360f411891000716aa2823122000aeb8050462440015d100a08c4880029ba14411891000536c28823122000a6e85cc462440014db0b988c4880039354e3118910084774386231220008ed870c462440014dd0a188c4880029b614311891000557420623122000aad840c46244001c9aa6188c488002baa00311891000574c00623122000a6f855c062440014d90ab80c488002abe11701891000556422e03122000aae84d40624400155b09a80c488002b3a0c501891000566c18a03122000a6e85d0062440014db0ba00c4880038b5524018910084774388031220008ed8710062440014dd0a200c4880029b614401891000716aa0803122000ace83100624400159b06200c488002b9a04401891000572c088031220108ee87cc062440011db0f980c4880029ba17301891000536c2e603122000aae84cc0624400155b09980c4880039354f301891000726a9a603122000ae7814c062440015c902980c4880029ba14301891000536c28603122000a6f8544062440014d90a880c488002abe11101891000556422203122000acf83440624400159906880c4880433a18a70c851001c3e428ec90a20018dc831d921440010fd0dbaa42880030f19375485100062e31eea90a200087e87d9521440010f90fb2a4288003171cf65485100061fbaec890a2000c3c75d912144001938e7b22428800237a1b73485100062fb2ee690a2000c5c65dcd214400193ec9b9a42880032719373485100046f43ec690a20008dc87d8d21440018beebb1a4288003171d7634851000637baec490a2000c6c75d89214400199ee7b124288003331cf624851000637ba8c490a2000c6c75189214400199ee63124288003331cc62485100065c326e090a2000cb8641c121440019d6c43824288042b9219210851000733b2a4210a205fec46348421440219c8c538e40880021fe15764811001c3e42aec90220008bf845d9204400517908bb2408800237e0d764811000c6e41aec902200387c851d92044005179083b240880021fa1b75481100061e326ea9022000c5c63dd520440010fd0fb2a40880021f21f65481100061e3a6ca90220008be86dd1204400187ecbba240880030f19774481100064e31ee890220008be87d9120440011790fb2240880030fdd764481100061e3aec89022000c5f75d8d20440018b8ebb1a408800327dd363481100064e3a6c69022000
  | 2 => 0xd53189100062eb9aa63122000a6e85d0862440014db0ba10c4880038b553421891000716aa2843122000a6e85cc862440014db0b990c4880039354f321891000726a9a643122000c6e76d9462440014db09b28c4880029b60f651891000476c3cca3122000aae84994624400155b09328c488002b3a0e651891000566c1cca31220008ef87594624400155f08b28c488002ab211651891000567c1aca3122000acc8359462440018dcec328c4880029b610651891000536c18ca3122000cae76d906244001c5ecbb20c4880038b197641891000717c2ec83122000e2c85d9062440011db0f320c4880029ba16641891000536c2cc83122000ace83990624400159b07320c4880023be1d641891000537c2ac83122000a6c85590624400159f06b20c488002b320d641891000537428c83122000a6d85190624400195cec320c4880038bd94641891000716328c83122000e2e851906244001c5b0a320c488003a9604641891000537436a83122000a6c86d5062440018dcedaa0c4880038bd93541891000716326a83122000a6e8655062440014d90caa0c4880031b9d9541891000717b22a83122000e2c64550624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c48800393e1763189100072642ec63122000e4f54d8c6244001c9aa9b18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab612631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000a6e8518c62440014db0a318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000727428c63122000e4d8518c6244001c9ea8318c48800393550631891000764c00c63122000a6e86d4c62440014d90da98c4880031b9db531891000717b26a63122000e2c64d4c6244001c9ec7a98c4880039318f531891000537432a63122000a6c8654c62440018dceca98c4880038bd91531891000716322a63122000e4f6354c6244001c98c6a98c488003a919241189100076231c823122000f25545046244001d88c6a08c488003aa19230189100076431c603122000ea8644c06244001e92a6980c4880029ba16741891000536c2ce83122000a6d83d5062440014db0b2a0c4880038bd52541891000717c22a83122000e2e745506244001c5ae8aa0c4880029be0d541891000537428a83122000a6e859cc62440014db0b398c4880029b613531891000536c2ca63122000e4f5394c62440014df08a98c48800393e0d53189100072739aa63122000e4d7354c62440014dd0a298c4880029ba17431891000536c2e863122000ae681d0c62440015cb03a18c4880029ba16431891000536c2c863122000aea8090c62440015d
  | 3 => 0x9312200387f87d5262440010fb0faa4c48800b0f9d354989100061eba6a93122078c5e73d5262440010ff0eaa4c4880021f61d54989100161f3a2a93122000c3d7455262440ef8bce6aa4c48800317a1573989100062ec2ae73122000c5f545ce62440018baa8b9cc48800e1fe1f53989100043ec3ea73122076c3e74d4e624400187ae9a9cc488007179cf53989100062eb9ea7312200087f8754e62440010fb0ea9cc4881d70f9d153989100061eba2a73122001c5e7354e62440018bae6a9cc48800e1fa1b75589100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400517d0dba2c4880030fd9774589100061e32ee8b1220008be87d91624400187eebb22c4880030f1d764589100064e39ec8b1220008be87191624400187eea322c4880030f1d464589100064e398c8b1220018de86dcd62440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d063589100043ec26eab12200087d83dd5624400117f08baac48800a2f21175589100046fc1aeab1220018dc835d562440011df04baac4880030fdd774589100061e3aee8b122000c3f85dd162440018790bba2c4880021fe15745891001c3e42ae8b1220008df835d162440031b906ba2c4880023be0974589100047dc02e8b122000c3f751d16244001878ea3a2c4880021fa1f545891001c3e43ea8b122000c3f74d516244005878e9aa2c4881e3171cf54589100043f43aa8b12200087c87551624400187ee8aa2c48800b0f1d154589103be2e39aa8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f85dcd62440018b90bb9ac48800317d5373589100062eaa6e6b12200087f855cd62440070f90ab9ac4880022fe1173589100145e422e6b1220008ef825cd62440011ef02b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f535891001c3e43ea6b122000c3f74d4d62440ed878e9a9ac48800317dcf535891000e2e39ea6b12200087e8754d62440010f90ea9ac4880030fdd153589103ae1e3a2a6b122000c5f7354d62440038b8e6a9ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000cd473dc56244001970e9b82c4880023be1d621891000537c2ac43122000a6c85588624400155f08b10c488002ab211621891000567c1ac43122000acc8358862440211d904ba8c4880423b20974189100161f3a2a83122000c3d7455062440211d904b98c488007179c
  | 4 => 0x24400155d093aec488002ab61275d89100056741cebb122000acd839d762440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d362440014dd0a3a6c4880029b61474d891000573408e9b122000ae5811d362440014db07aa6c4880038bd5254d891000717c22a9b122000e2f745536244001c58e8aa6c4880029be0d54d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000537428e7b122000a6d851cf62440015d50039ec488002ba60073d891000536c26a7b122000e4f5394f62440014df08a9ec48800393e0d53d891000727b9aa7b122000e4c7354f62440014dd0ba1ec4880029b61743d89100053742c87b122000a6d8590f62440014dd0aa1ec4880029b61543d89100047743887b1220008ed8710f62440014dd0a21ec4880029b61443d89100053742ee3b122000a6d85dc7624400159d07b8ec488002b360f71d89100056741ea3b122000acd83d47624400155d0828ec488002ab61051d89100047743e83b1220008ed87d0762440014dd0ba0ec4880029b61741d891000716aa683b122000ace83d07624400159b07a0ec4880038b55141d89100053742883b122000a6d8510762440014dd0b98ec4880029b61731d891000726a9c63b1220008ee870c762440011db0e18ec4880029ba1431d891000536c2863b122000aae840c7624400155b0818ec4880039354c31d89100057540063b122000ae9800c762440014dd0bb86c4880029b61770d891000557426e1b122000aad84dc3624400155d09a86c488002ab61350d891000567418a1b122000acd8314362440014dd0ba06c4880029b61740d891000716aa481b1220008ee8710362440011db0e206c4880029ba1440d891000536c2881b122000e2d54103624400159d06206c488002b360c40d89100057340881b122000ae58110362440011dd0f986c4880023b61f30d89100053742e61b122000a6d85cc3624400155d09986c488002ab61330d891000726a9e61b122000e4d534c362440014dd0a186c4880029b61430d891008636312eb3122000c3e74d9662440018bce7b2cc4880030f9d065989100062f398cb3122000c3f655d26244001878caba4c4880432b18974989100061f3aec93122000c3d75d92624400193ce7b24c4880030f9d464989100061eba8c93122000c9e7319262440018becab9cc4880031719573989100064fb22e73122000c9c645ce6244021998c4b9cc488003179d763989100062ebaec73122000c9e74d8e624400193ae9b1cc488003179d463989100062eba8c73122000c9e7418e624400193ae831cc4880031b9d7629891000636baec53122000cae74d8a624400195ae9b14c488003339cf629891000666b9ec5312200087f845d662440010ff06bacc4880030fa1574989100061ec2ae
  | 5 => 0x8002a7a1051d8d100054ec20a3b1a20008de87d0763440011bb0fa0ec68800297a1741d8d100052ec2e83b1a2000e1d54d07634400159d05a0ec688002b360b41d8d100070eaa283b1a2000a5e8510763440014bb0a20ec68800317dd770d8d101656b40ee1b1a2000a9e84d43634400153b09a86c68800237a1c50d8d1004c6ec38a1b1a2000a5e85d0363440014bb0ba06c6880038755240d8d100046f43881b1a20098dd8710363440014bd0a206c6880029761440d8d100070eaa081b1a2000ace82103634400159b04206c688002b5a0440d8d100056ac0881b1a2000c3f745536244005878e8aa6c48800317dcd53d891000e2e39aa7b1220038ef8754b624400155d08296c488002ab61052d891000567418a5b122000acd8314b62440014dd0ba16c4880029b61742d891000716aa685b1220028ef8750b6244001c5aa8a16c4880029ba1442d891000536c2885b122000ace8310b624400159b06216c4880029ba1732d891000536c2e65b122000e4d53ccb62440031df0e996c4880039354d32d89100053742865b122000a6d850cb624400155d08196c488002ab61032d891000536c26cbb122000a6d83d97624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc8359762440014db0832ec4880029b60c65d891000717b2ec9b122000e2c65d936244001c5f0bb26c4880038b21764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000537428c9b122000a6d851936244001c5eca326c4880038b19464d891000717428c9b122000e2d851936244001d4b02326c4880029ba1b54d891000536436a9b122000e2f64d536244001c58c9aa6c4880029ba1954d891000536432a9b122000e2f645536244001c58c8aa6c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec48800393e1763d89100072642ec7b122000e4f54d8f6244001c9aa9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec4880029ba1463d891000536c28c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4e8518f6244001c9b0a31ec48800393d5063d891000726aa0c7b122000ec98018f62440014dd0da9ec4880029b21b53d891000717b26a7b122000e2c64d4f6244001c9ec7a9ec4880039318f53d891000537432a7b122000a6c8654f6244001c5ec8a9ec4880038b19153d891000727b1aa7b122000e4c6354f6244001d48c920ec488003c955141d89100076431c61b122000f49534c36
  | 6 => 0x51ec2e63b222000e1d538c7644400117d0e18ec88802a2f61c31d91100051f42863b222000a3d850c76444001c3aa618ec888002aba0831d911000556c1063b222000aba800c764440015730018ec8880b6ada0770d91100045f43ea1b2220008bd87d43644400153d06286c888002a760c50d91100045f43e61b2220008bd87cc3644400147d0b986c8880028f61730d91100070ea9e61b222000aae82cc3644400155b05986c8880038754d30d91100051f42861b222000a3d850c364440014bd0dbaec688003179db75d8d100052f430ebb1a2000c5e761d763440018bcedb2ec6880029761365d8d100046ec3ccbb1a2000a5e85997634400153d0932ec688002a761265d8d1000567414cbb1a2000acd8299763440011bf0eb2ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec68800297a1865d8d100062f3b0cbb1a2000a5d84197634400193cedb26c68800387d9764d8d100070e32ec9b1a2000e1f85d936344001c390bb26c68800387dd764d8d100070e3aec9b1a20008dd8799363440014bd0b326c6880029761664d8d100054f424c9b1a2000ace82993634400159b05326c68800237e1d64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100052f428c9b1a2000a5d85193634400153d0c326c688003279d864d8d100070fb28c9b1a2000e1c651936344001c3d0a326c6880038761464d8d100070fba8c9b1a2000e1c751936344001d2b02326c68800297a1b54d8d100052e436a9b1a2078c5e76d536344001c3ec9aa6c6880038719354d8d100052f432a9b1a2000a5c8655363440ef8bcecaa6c68800387d9154d8d100070e322a9b1a2000e94649076344001e2aa8a0ec688026b6a1b70d8d10006adbaee1b1a2000a5d84dd763440018bce3baec688003171c775d8d100062eb86ebb1a2000a5e859d763440018baea3aec68800297a1c75d8d100062f438ebb1a2000a5d841d763440014bd0b3a6c6880029761674d8d1000567414e9b1a2000acd829d363440014bf0aba6c6880029721574d8d100052f428e9b1a2000a5d851d363440f75ad023a6c688002b560474d8d100052f43ea9b1a2000a5c87d5363440f54bb0b2a6c68800387d5254d8d100052f43aa9b1a2000a5c875536344001c3f08aa6c6881e697a1454d8d100062fbaee5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000a5f855cb63440014b90ab96c68800317dd572d8d100046f438a5b1a20008dd8714b634400153d08296c688002a761052d8d100052f42e85b1a2000a5d85d0b6344001c3aa9a16c6880038755142d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d101656d406e3b1a20008de87d4763440011bb0fa8ec68
  | 7 => 0x7d8710765440010fd0f98eca880021f61f31d95100043f43863b2a200b87d870c7654400147d0818eca880028f61031d95100053741063b2a2000a6d820c765440014f50018eca880029e60031d951014d3b40ee1b2a200087e87d0365440010fb0fa06ca880021fa1c40d951005c3ec3881b2a2000a5e8310365440014bb06206ca880029ba0840d951000536c1081b2a2000a768110365440014eb02206ca880021fa1f30d95100043ec3e61b2a2000a3e84cc3654400147b09986ca8800317dcf30d95100053741661b2a2000a6d82cc365440018bee6986ca880021fa1c30d951005c3ec3861b2a2000a3e86dd7644400187cedbaec8880028fa1875d91100061f3b0ebb222000c3e76d97644400147b07b2ec8880022f61e65d91100051f42ccbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb2220008bf87597644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147d0c32ec8880030f9d865d91100051ec18cbb2220008bd8798f644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400117f0eb1ec8880028fe1563d91100051e42ac7b222000aaf8258f644400155904b1ec8880028fa1463d91100051ec28c7b222000e1f6518f6444001c38ca31ec88800387a1463d91100070ec28c7b222000e1f7518f6444001c38ea31ec888003a660063d91100051f436a7b222000a3c86d4f64440ed87ceda9ec88800387d8f53d91100070e31ea7b222000a3e8654f64440014790ca9ec8881d70f9d953d91100070fb1aa7b222000e1c6354f644401556d0db8ec8880034ddd771d91100074c31c61b222000f19534c3644400147b07baec8880030f5c775d91100061f386ebb222000c3c70dd7644400147d0b3aec8880030f5d475d91100051f438ebb222000c3e871d7644400147b063aec8880028fa1673d91100051ec2ce7b222000aae829cf644400155b0539ec8880028fe1573d91100051e42ae7b222000a3e851cf644400147b0a39ec8881faaea0073d91100055cc00e7b222000a3e87d4f64440014790fa9ec8881f68f61653d91100070fa9ca7b222000a3e8754f64440014790ea9ec88800387e0d53d91103e51f428a7b222000c3f75dcb644400147d0b396c8880028f61672d91100054f41ce5b222000a9d839cb644400147f0ab96c8880028f21572d91100061fbaae5b2220008be8714b644400117b0e296c888002a7a0c52d91100054ec18a5b222000a3e85ccb644400147b0b996c8880038754f32d91100070ea9a65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000c3f75dc7644405b57501b8ec888002a7a0f51d91100054ec1ea3b2220008be87147644401517b0e28ec8880028fa1731d91100
  | 8 => 0xab9ec5080031761573d8a100062faa2e7b142000c5d545cf62840070ff0fa9ec5080021f61f53d8a1000e2f39ea7b142000c5d73d4f62840010ff0ea9ec5080021f61d53d8a1000e2f39aa7b142000c5d7354f628400399ce7196c5080063be1d32d8a1000e6739a65b142000e4d534cb62840015c902996c50800b0f9d15498a100061eba2a93142001c5e7354e62840018bae6a9cc5080038b5514298a100061fba2a8b142002c3c7455162840038bce6a9ac508003175cd5358a100147643a84b142002cac745096284001c5aa8a12c5080023be1d6218a100161f3a2a83142000c3d7455062840038bce6a98c508003175cd5318a1000726a9a6431420008ee8798921840011db0fb1043080433998971082100043f436e9b2a200387f87d93654400187ae9b26ca880021f61e64d95100052f41cc9b2a2000a5d8399365440014dd05326ca880029b60a64d95100043fc3ac9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a200b87d87193654400187ae8326ca880030f61c64d95100071ac08c9b2a200087e86dcf6544001878c9b9eca880030f19173d951001c3fc3ec7b2a2000c5d73d8f65440010fb0f31eca880028fa1263d95100051ec24c7b2a2000a6e8298f65440014db0531eca880021fe1d63d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d951005c3ec38c7b2a2000c5d7318f6544001c38c831eca880031761c63d95100062fba0c7b2a2000c5d7418f6544001cb30031eca880038d19241d95100069bba283b2a2000e34645076544001cb0c7186ca8800356dcd30d95100072c31a61b2a200087d83dd365440010fb0f3a6ca880030fe1174d95100043fc1ae9b2a200087e871d3654400187ae83a6ca882029da0474d95100053ac08e9b2a200087d84dcf65440010fb0f39eca880021fe1173d95100062fc1ae7b2a200087e871cf65440018bae639eca881fe9ea0073d95100053cc00e7b2a200087e87d0f65440010fb0fa1eca880021fa1e43d95100043ec3c87b2a200087e8750f65440010fb0ea1eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca880028fa1272d95100051ec24e5b2a2000a5e839cb65440014bb07396ca880021fa1f42d95100043ec3e85b2a2000c3f74d0b654400187ee8a16ca880021fa1c42d95100043ec3885b2a2000a5e8310b65440014bb06216ca880021fa1f32d95100043ec3e65b2a2000c5f73ccb65440018bee6996ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880a69ea0371d95100043f43e83b2a200087d87d07654400187ee9a0eca8800297a0f41d95100052ec1e83b2a2000a6e82d0765440014db05a0eca880030fdd141d95100043f43883b2a200b8
  | 9 => 0x325842001e3a3aca2b0840108f48754561080215c904a8ac2100423d21d41584200071aaa282b084010ae48250561080015e100a0ac210007351ce31584200072aa9c62b084000ec6328c561080211e90e98ac210042b920931584200867338aed1084010ae78758421080019cf0eb08421000399e1561084200073242ac21084000e67545842108001ccaa8b084210003b1e0d61084200076241ac21084010ce77358421080019cae6b08421000399d4d610842000732a9ac210840109eb865c021080019d70cb8042100035ae157008420006b442ae01084000dab845c02108001b5108b8042100433ad91700842000674b22e01084000d6b545c02108001ad2a8b8042100035ad4d7008420006b4a9ae01084000c6c75dd92008001958e9bb240100031bd53764802000636aa6ec9004000c6f53dd920080018daa7bb240100031bddb754802000657bb6e89004000c7875dd92008001970e9bb240100031ed5376480200063caa6ec9004000c7b53dd920080018f2a7bb240100031eddb75480200065dbb6e89004000b6b85485200800517d09baec5880022f61375d8b100052ec1cebb16200087f845d762c40010ff06baec58800e1fa1774d8b100043ec2ee9b162000c3e759d362c400187aeb3a6c5880030f9d574d8b100061ebaae9b162000c3e855d362c400187b0aba6c58800e1fe1f54d8b100043ec3ea9b162002c3e74d5362c400187ae9aa6c5880021fe1d54d8b100043ec3aa9b162002c3e7455362c400187ae8aa6c58800e1fa1773d8b100043ec2ee7b1620028be84dcf62c400117b09b9ec58800e1fe1f53d8b100043ec3ea7b162076c3e74d4f62c400187ae9a9ec5880021fe1d53d8b100043ec3aa7b162075c3e7454f62c400187ae8a9ec58800317dcd53d8b1000e2e39aa7b162002cae7490b62c40051df0ea16c58800b2b9d142d8b1000716aa285b162000ae88050b62c400587ce8aa4c5880030f5d15498b1000e2f39aa73162000c5d7354e62c4001c9aa6994c58800b0f9d15458b100061eba2a8b162000c5f7354d62c40038b8e6a9ac5880063b21d3258b1000e6639a64b162000e4d534c962c40011df0eb10c58800b0f9d15418b100061eba2a83162001c5e7354c62c40018bae6a98c5880038b5514218b1008675312e010e20008ee8798920c40011db0fb10418800637a0f75d8a100046ec1eebb142000a3d849d762840010ff08baec5080021fe0d75d8a1001c3f42ee9b14200087d85dd362840031bd07ba6c5080023760f74d8a1001c3fc3ea9b14200087d87d5362840f18bce7aa6c5080021fe1d54d8a100043ec3aa9b142000c3f745536284005878e8aa6c5081df179cd54d8a1001c3f42ee7b14200087d85dcf62840018bceb39ec508003175d673d8a100062f3aae7b142000c5d755cf62840018bd
  | 10 => 0xb224000a3e850c7644800147b0a18ec8900038754c31d91200055741063b224000aad820c764480015750018ec890002ae60031d91201fd57416e1b2240008be87d43644800117b0fa86c890002a7a0c50d91200054ec18a1b2240008be87cc3644800117b0f986c8900028fa1730d91200051ec2e61b224000e1d53cc3644800155d05986c890002ab60b30d91200070ea9a61b224000a3e850c3644800147b0a186c8900029760c65d85200061fba2a9b0a4002c3c7455361480038bce6a9ec290003175cd53d85200072aa9863b0a4000ae5820c761480015e30018ec2900030f9d365985200061f3a0cb30a4000a5d83196614800187ecaba4c2900030f19574985200061f3aec930a4000c3d75d92614800187cea324c2900030f5d4649852001c3f436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480014bb0632ac290003171cc65585200145f436e8b0a4000c3f65dd16148001878cbba2c2900022fa1f64585200061fbaec8b0a4000c3c75d916148001938e7b22c2900022fa1c64585200061fba8c8b0a4000c3c751916148001938e6322c29000317d9773585200062e32ee6b0a4000c9f64dcd6148001938c9b9ac2900029760c65185200047bc3ac230a4000ad483584614800587ce8aa0c2900030f5d1541852000e2f39aa630a4000c5d7354c6148001c5aa8a10c290002ba20142185200072aa986230a4010ce8209db21480010fd0dbaa42900030f19375485200043f43eca90a4000c5c73d95214800187eebb2242900030f1d764485200064e39ec890a4000c5f65dcd21480018b8cbb9a429000327d9373485200064e326e690a4000cd473d8521480019a8e630a42900032e19370485200065c320e090a4000e676548421480318dcedb2c409005f2b9db64881200161f3a2a93084000c3d7455261080018bee6a9cc210007171cd53984200847ac3ca330840108f5879066108001c6aa8a0cc2100423d61e31984200072aa9c63308400087d84dd561080010fb07baac21000237e0d755842000c6e41aeab084000a3d841d561080010ff0aba2c21000e1f21574584200046fc1ae8b0840018dc835d161080010fd0faa2c21000e1f21f54584203c62e39ea8b08400087e8755161080010f90eaa2c21000b0f9d154584200061eba2a8b084077c5c7355161080018beebb9ac210003171d773584200062fc2ee6b084000c5c85dcd61080018bea9b9ac2100031755373584200043fc2ae6b08400387c855cd61080018beea39ac210003171d473584200043f43ea6b08400387c87d4d61080018bee7a9ac210007171cf53584200043f43aa6b08400087c8754d61080018bee6a9ac210007171cd535842000e6639c64b084001ccc734c96108001c9aa6992c210002b9205
  | 11 => 0x480010fd0f98eca900021f61f31d95200062fb9c63b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4000c5f730c765480014dd0418eca900029b60831d95200053d40063b2a4000a79800c765480814dd05b86ca900021fa1f40d95200043ec3e81b2a400087e8710365480310fb0e206ca9000297a0c40d95200052ec1881b2a4000a6e8210365480014db04206ca900029da0440d95200053ac0881b2a400087e87cc365480010fb0f986ca900028fa1330d95200051ec2661b2a4000c5f73cc365480014dd05986ca900029b60b30d95200062fb9a61b2a400087e870c365480310fb0e186ca900028fa1b75d91200061f3b6ebb224000a3e861d7644800187cec3aec890002c760c75d91200061f3b6cbb224000a3d83d97644800117b0f32ec8900028fa1665d91200045fc3acbb224000a9e83197644800153b0632ec8900028fa1865d91200061f3b0cbb224000b1d831976448001c3d0632ec8900028f60c65d91200070ec18cbb224000a1d83197644800117b0f31ec8900028fa1663d91200051ec2cc7b2240008bf8758f644800147f0ab1ec8900028f21563d91200055bc0ac7b224000ab48158f644800147d0a31ec8900028f61463d91200051f436a7b224000a3c86d4f64480ed87ceda9ec8900028fa1953d91200051e432a7b224075c3e7654f6448001c3cc6a9ec8900038758d53d91200bd57436e5b224000d2f75dcb644807f75501b96c8900028f60f75d91200061eb96ebb224000c3e70dd76448001878e1baec8900028fa1675d91200061eba8ebb224000a9e831d7644800153b063aec8900028fa1c75d91200061f438ebb224000e1e831d7644800147b063aec8900038760c75d91200050ec18ebb224000a3e859cf644800147b0b39ec89005eaba0a73d912000556c14e7b224000a3f855cf64480014790ab9ec8900028fa1473d91200051ec28e7b224000a3e87d4f64480014790fa9ec89020a8f61653d91200070fa9ca7b224000a3e8754f64480014790ea9ec89000387e0d53d91200070f39aa7b224000e1d7354f644810347d0a29ec8900030fdd772d91201fd5d406e5b2240008be8714b644802f17b0e296c890002a7a0c52d91200054ec18a5b224000a3e85ccb644800147b0b996c8900038754f32d91200070ea9a65b2240008be870cb644802f17b0e196c8900028fa1432d91200051ec2865b224000e8d320cb644800187eebb8ec8900028fa1671d91200051ec2ce3b224000a3f855c764480014790ab8ec8900030fdd571d91200054fc1ae3b224000a9c835c7644800155f04b8ec89005eab20971d91200054f41ea3b224000a9d83d47644800117d0e28ec8900022f61c51d91200051f42e63b224000a3d85cc76448001c3aa718ec8900022fa1c31d91200045ec3863
  | 12 => 0x8030fdd153580213ae1e3a2a6b004201c5e7354d60084018bae6a9ac01080b2b1d24258021016563a284b004200e2d5450960084015d100a12c01080f1e1d650580210847c43aa0b004210ae8825416008405970e9202c0108038e55240580210075521480b0042108f88750160084215d104a02c0108423e21d30580210072ca9a60b004210ae8824c160084015e102982c01080b0f9d154987200061eba2a930e4000c5f7354e61c80038b8e6a9cc39000b2b9d1429872000716aa28530e4002c3e7455161c800187ae8aa2c39000317dcd535872000e2e39aa6b0e4002c3e74552618800187ae8aa4c31000317dcd539862000e2e39aa730c40028f5879066188001c6aa8a0cc3100030fdd154586200161e3a2a8b0c4000c5f7354d61880038b8e6a9ac3100039354d32586200147a43a82b0c4000e355450561880011ef0eb08c3100021fa1b74d952001c3fc3ec9b2a4000c3d74d9365480010fb0f326ca900021fe1d64d95200c43ec38c9b2a4000c3d7419365480014bd06326ca900029760c64d95200061ec38c9b2a4000e1e831936548001c3b06326ca900038b60864d95200043f436e7b2a4000c3c64dcf6548001878c8b9eca9000e1fe1f63d95200062eb9ec7b2a400087d8798f654800147d0931eca900028f61263d95200062fb9cc7b2a400087f8758f654800147f08b1eca900028f21163d95200062fb9ac7b2a4000a778158f65480014e902b1eca900621f61c63d95200062eb98c7b2a4000e2c6490b6548001a5ee8a16ca900038b19142d9520005b440285b2a400087d83dd365480010fb0f3a6ca900030fe1174d95200043fc1ae9b2a400087e871d3654800187ae83a6ca9000297a0c74d95200052ec18e9b2a4083a6e821d365480014db043a6ca900021f61373d95200043ec3ce7b2a4000c5f739cf65480010ff08b9eca9000317e0d73d95200043f438e7b2a4000c5d731cf65480010fd0fa1eca900021f61f43d95200043f43c87b2a400087d8790f65480018bae721eca900021fa1d43d95200043ec3a87b2a4000c5d7350f65480010fd0e21eca900021f61c43d95200053741087b2a4000a6d8210f65480814f501b96ca900021fa1f42d95200043ec3e85b2a4000c3f74d0b654800187ee8a16ca900021fa1c42d95200c43ec3885b2a4000a5e8310b65480014bb06216ca900021fa1f32d95200043ec3e65b2a4000c5f73ccb65480018bee6996ca900021fa1c32d95200c43ec3865b2a4000a3e840cb654800147b08196ca90003934c832d95200051f424e3b2a4000a3d849c765480014bf06b8eca900029720d71d95200043f43e83b2a400087d87d07654800187ee9a0eca9000297a0f41d95200052ec1e83b2a4000a6e82d0765480014db05a0eca900030fdd141d95200043f43883b2a400087d8710765
  | 13 => 0x62fbaee1b1a4200a5e859c363484014bb0b386c69080297e1570d8d210052e42ae1b1a4200c5f755c3634840153f08b86c690802a721170d8d2100567c12e1b1a4222acc825c3634840153d09a86c690802a761350d8d210046f438a1b1a42008dd8714363484014bd0ba06c6908029761740d8d210070eaa481b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a4200e1d54103634840159d04206c690802b360840d8d210056b40881b1a4200ad5811036348401ccecbb0c42908028f61065d81210161f3a2a9b024200c3d7455360484018bee6a9ec090807171cd53d81210071caa081b024200ae98210360484015e302206c090803179cf65981210051ec20cb3024200c5e7319660484018becab9cc0908031719573981210062f3aec73024200c5d75d8e60484018bcea31cc090803175d4639812101c3f436eab02422487c86dd560484010fd0fb2ac0908030f1d365581210062e39ecab02420087e87195604840147b0832ac0908030f1d065581210062e398cab024200c3f65dd16048401878cbba2c09080637a1b73581211146e436e6b024200c5f65dcd60484018b8cbb9ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b024200a3d8419460484011f70eb00c090802ae21160181210161f3a2a83024200c3d7455060484038bce6a98c090803175cd531812100726a9a643024200ae4814c86048401c72a8200c0908031b1d776484210066639eec9084200c6f54dd921084018daa9bb242108031bd4f764842100636a9eec9084200ce651dd921084019caa3bb242108031bddb754842100667bb6e69084200c7475dd921084019a8e7bb242108031dd5376484210063aaa6ec9084200c7753dd921084018eaa7bb242108433994b764842100672a96ec9084200c7776dd521084019aeedb9a42108030fdd154980210161e3a2a93004201c5e7354e60084018bae6a9cc0108423e61e50980210847cc3c813004200e395490260084211f30f184c0108039654d30980210043ec26eab00420087d83dd5600840117f08baac01080a2f21175580210052ec18eab004200c3f75dd16008401878ebba2c0108030fe1774580210061e42ee8b00420087f855d160084070f90aba2c0108030fdd474580210061e3a8e8b00420087e87d5160084070f90faa2c0108030fdd354580210161e3a6a8b00420087e8755160084010f90eaa2c0108030fdd154580210161e3a2a8b00420087f855cd60084070f90ab9ac0108022fe1173580210145e422e6b00420087e87d4d60084070f90fa9ac0108030fdd353580213b61e3a6a6b00420087e8754d60084010f90ea9ac010
  | 14 => 0xd87cc765484010fd0e18eca908921f61c31d95210051f42063b2a4200a3d840c765484014dd0418eca908029b60831d95210053d40063b2a4200a79800c765484014bd07386ca908029760e70d95210051fc22e1b2a4200a3c845c365484010fd0fa06ca908021f61f40d95210061fba481b2a420087e8710365484010fb0e206ca908030fdd040d95210052f41881b2a4200a5d8310365484014dd04206ca908029b60840d95210053b40881b2a4200a758110365484010fd0f986ca908021f61f30d95210051f42661b2a4200a3d84cc365484018bee7986ca908029ba0b30d952100536c1661b2a4200c5f734c365484010fd0e186ca908021f61c30d95210052f436ebb1a4200c5e76dd763484014bd0c3aec690803179d875d8d210058ec20ebb1a4200c5e76d9763484014bb09b2ec6908023761e65d8d210052f42ccbb1a42008df87597634840153d0832ec690802a761065d8d210052f430cbb1a4200c5e76197634840163b0832ec69080387a1065d8d210052ec20cbb1a4200e1d84197634840143b0832ec6908023761e64d8d210052f42cc9b1a4200a5d8599363484011bf0eb26c69080297e1564d8d210052e42ac9b1a4200adb8059363484015b100b26c69080297a1464d8d210052ec28c9b1a4200a5e86d5363484014b90daa6c6909e3179db54d8d210052f432a9b1a4200a5c8655363484ef8bcecaa6c6908038799154d8d210070eb22a9b1a4222ace86dcb6348401a9eebb96c69097ef1a0772d8d210052ec26ebb1a4200c5d72dd763484018bce3baec690803171c775d8d210052f42cebb1a4200c5d751d7634840153d083aec690802a761075d8d210052f438ebb1a4200c5e871d76348401c3d083aec6908029761075d8d210070ec20ebb1a4200a1d841d763484014bd0b3a6c6908029761674d8d2111567414e9b1a4200acd829d363484014bf0aba6c6908029721574d8d210052f428e9b1a4200a5d851d363484014bd0faa6c6908029721f54d8d2142d2ec2ca9b1a4200e1f5495363484014bd0eaa6c6908029721d54d8d210070fc22a9b1a4200e1e745536348401c3ae8aa6c690a1297a1454d8d210062fbaee5b1a425fad681dcb6348401c9ea5296c69080237a1c52d8d211146ec38a5b1a4200a9e8414b634840153b08296c69080297a1742d8d210052ec2e85b1a4200e1d54d0b6348401c3aa8a16c69080237a1c42d8d211146ec3885b1a4200a5e8510b63484014bb0a216c690803a350842d8d212fd67416e3b1a42008de87d4763484011bb0fa8ec69080395d4651d8d210054f420a3b1a4200a9d8414763484011bd0fa0ec6908023761f41d8d210052f42e83b1a4200a5d85d076348401c3aa9a0ec690802b3a0b41d8d2100566c1683b1a4200e1d5450763484014bd0a20ec6908029761441d8d2100
  | 15 => 0x3603c00601203100100100003800003200000400400000000700000301600000003700a03400a00100201500000000100e00205f00000500200000900a00000500100200c05900200209c01200101905f00e05c00501700300300300000200300000100500000500900501400000000100e00302400200000a00000500000200400100300a00000800b02f00900501100e00300900000000400000900c0060061fba2a93064202c3c7455260c84038bce6a9cc190803175cd539832100e6739a653064200e4d534ca60c840187ee8aa2c19080b0f1d1545832100e2f39aa6b064200c5d7354d60c840187ee8aa4c11080b0f1d1549822100e2f39aa73044200c5d7354e60884031f30f184c1108039654d30982210061fba2a8b044202c3c7455160884018bee6a9ac110807171cd535822100716aa284b0442018f8874c16088401cb2a6982c1108023ee1d60182210043f436e9b2a420387f87d93654840187ae9b26ca908021f61e64d95210061fba4c9b2a4200a5e8399365484014bb07326ca908021fe1d64d95210061fba2c9b2a4200a5f8359365484014b906b26ca908029ee0164d95210053c402c9b2a422487d87193654840187ae8326ca908021fa1b73d952101c3fc3ec7b2a4200c5d73d8f65484010fb0f31eca908021fe1d63d95211243ec38c7b2a4200a3e8418f654840147b0831eca90803175cc63d95210062ec38c7b2a4200e1e8418f6548401c3b0831eca9080317dd063d95210062eba0c7b2a4200e4d8218f6548401c98c7196ca9080353dcd32d95210072631a65b2a4200b64814cb65484010fb07ba6ca908021f61e74d95210061fba4e9b2a4200c3f845d365484010ff06ba6ca908021fa1c74d95210061eba0e9b2a420087d84dcf65484010fb0f39eca908021fe1173d95210062fc1ae7b2a420087e871cf654840147d0839eca908028f61073d95210062eb98e7b2a4286a6e821cf65484014db0439eca908021fa1f43d95210043ec3e87b2a4200c3d74d0f65484010fd0f21eca908021f61e43d95210043f43a87b2a420087d8750f654840187ae8a1eca908021fa1c43d95210043ec3887b2a4200a6e8210f65484014db0421eca909829da0772d95210043f43e85b2a420087d87d0b654840187ee9a16ca908030fdd142d95210043f43885b2a422487d8710b65484014bd06216ca908029760c42d952100716a1085b2a420087e87ccb65484010fb0f996ca9080317dcf32d95210062fb9a65b2a420087e870cb65484490fb0e196ca908028fa1032d95210051ec2065b2a4260a6e82dc765484010fd0fa0eca908021f61f41d95210061fba683b2a4200a5e83d0765484014bb07a0eca908029ba0b41d952100536c1683b2a4200c3f7450765484010fd0e20eca908921f61c41d95210043f43e63b2a420087
  | 16 => 0xe0c41a94eb641c00003e512258120185180007b242a04f82f82fb0fe117093e42c19f0e386de50c020909861617109782c406e0000001ba000065626800007642dd2271f180004550d6842c5ea24032d8988a7601e02c02600400200101400104201100800f00000200000200402a00300300000100700a00100500400000600200000000000000300004102000500a00000200200700000100001400000400000a00000000000d00000600001704302104601900003200100600100000602f00b0050190150000080070000b602a00400100500d00000001f01100606102200003500200200200a00403c00500901200502800200000d00d05100e00000300000200500000400400000600300700000d00100000601c00800000200201800300e00500600d00000000f00600100200100001700000300a00a00000000400d01a01100600000200100200009e00700600200d00100b00301602500d00200000901f00f01200700000600000100100e00300800400200200300f00701c01700000e00d00c00200000000600500b00000b01500201300000202501105900500000600100200000001403000500101000201701000e00400800600000a00a00700000100200406c00000008204400804302c00100000000000200600500002200c00000300700000200d06a02304100000200b00000401900601a00000000600e01100000300b0010070ee00001100100d00403302900b02100000300000100b00000802c00200000700100502800000a07600000b00102c01701800100500600300000500002601100200101100400705400300a00500205a00409701301b00000101001703200000f00402200901303800003604f00009500106900700000000000a00e00000800500400900200000301d00100700c00200000005600000b00700600001000000201b03700000000800200300800000500c00500500100100000000000000c01600000000000200200000500800000001400201401c00000c00000b00101700000200100000f00300b01000c00001300400100100200404308200700900001900200100101700902900700000701300200400005b00000900000004900100001900001100100304b00a00000200500800300700000000001000000a00500000500000000500703200c02500100000400a00500405000600b00000100100600400100100101200000f05a00400105600b00400600000800b00300500101a00404300000200100400000100701101300408000000000000500204900000400001100000105900800004801f00a03501000b00300202600200600004c02f00300000304902e03e00001700000200100200a00b00102c01300100500003200c00000200f00000800100000201503202a06400000400500c000006002
  | 17 => 0x102e864d08f82882da46e20a065c2900d42561194d9e0af145056c878819070214092220020e803400000027b8000a361ef00007007560531ef9b703548122438b9c0008843168d6c1f80000001a6000000000006bc4fe85b1550f00d582a73dca10012439f3df17d4c7045d024a11c10230700002d000081b1c497180000000000000000866000145c0006020e620f800000008188dc18863015804cc2ac7ce0dd99c800000010f19646123a34030fe863834a277000040468b00000007d403d00000010e00003278894fc84f90000000d682e800c033c0000003c40e28a6e00002ba1040003a81b214583662fc2300a7882c4f016c1ca091831a00017bc0002ed30083f49427131298c3058e0000d080007d800012f89640004e73ce21f064424c05f000092e6b925e85e886008d08289280003e132f9e088f009413d83080e6000270915c6a21280e409b429a42026519c0efe5580000000e0a4791059300f166cd2201664d808000002088b345112eb857c98e53d3e59f805003b0059940c70435233c800049082609c9bcc7941d33b61b285a800027291f056e08f0a11ff000000015980006280003f303d0bb63e81fb9260dbe7410000cdc00048600004b83a200026480010265570000940f7800000000007e832c4228000e065a439a9830f8e75841e9778f1a4a201a9fd800000000000006b034911480000000003af11acb1200000000007ba0002f400000006b80001bc415000017900000007970000d4ce9e0000001a7cc3037f1660ab86ae7d50e71a089f662400005fc8342a437097d01a40004158ce800033415480003fc3f63471498f44878224800000009c0000000e5e02d1ac8b6c2cc00000006fc5440000001ed04380001c888c471a83715d168ca7e65a3888eb02ee6993f58ed48d05552f605250722c229a0e8910a8832f90d30f945fe0669648bc440b2121d547fa5fa0279a44fea2733cd998cf584a73290e0003e3c80b221881346dd41d8864b0c7a1101a1e506424f2611a70c7a13402702ec0da5d628c090d1126d33961fe91045f72c217a40b264e37f19bc97242734301c070e1b53e0922ca8a6d62b007147ae29f3b18a5cfd0786194077c3ee3b6323046867a32117b1148d3a6d1374967030a0ad00019a006668a33620301707fd0508cd826a1610f60bbd10e03b01719d8e624b733e20447de42307592405102e12ed04a890080d35e9678ef44341ed9c6502c1c70b513747ea43529d1e8c2627a7210972016a5052fe83b076e33b36314b816e3a10c800002fc0f10cd88100a43711b29a04cc40001a28888dd41890401ddcc163ee13a80009b46540001a8c9a4315082217888235e15a21c4b9a0c81d3867c1a258c2d68000ad62330f88b210e60e82e384ecd5e13f08602fc1b02e0000000095277c06d800026e81
  | 18 => 0x9e4129eb400032b294800000000013608505be63a28e1b1c0c8000000091ca6684b00f147400082320c1fc400079f19f99d4ab428300003007b012d35807490a444b31005101160000db9b883061600000dd4a1e38339c94a007464300016c0b5073e3b20000df277e03514e000044300000285f40ac1c09b9ca542661ea86c008a0d33161d004202f73af9b50872000000013000014b361000000022f099000060c4b60001f5000000040e83988882e3000000000000041898dc6fc5f9407a2383784ec3eb8e8041e279000004458c3da00019609d20002e51ded0ce74e1e916c81c47da0be8000a3e38f30e0ce0000106290085c7923923609f88c7c3192659c680004f13e1000110c0ca000000005e0003c9800000074d0000e4c0a80000d19c5400000000013f40540002cd85a013a0162a89140f0842517c9e4800089324b0084eac4ed0000b70000000245000072c00027200000000000879de412246a00000009de22407911c47840001a002c0ca66501f583304a40002d30d0886e3501141e9474a6731519264b0a47d3e002647c6000092000059486308d965c902000000000000014f3ef89942466d9359872c318706390902043a0ae39e02d89040003108764ca219d3ef00008f687227a8ef8c3660a17a1df4f987202a687e0a9c03201c126c7c00ed2550d34b0615a3ba8644d3c1760f90530af64f23cc081cb9c017303859493a8091f9a240e1279403b1704e4c6c91f381083825e407c21587ac0c622d8dc0c8478c4370da8bca0852a01224fe8894061831440c05a0901a110f41fb135817840a51a30e86b80c082d14619ac36c52d03e1d64fba19c2c99708a125d331a840100a39b14a201c6308281388618c1e1ee3ba20d869c52400e13e8df827641c0b38aa42cb14da16872a07e24184a506603e189008c6aa1271b484f469611514b129903455e1801a201646f830996f49fe8594058b5c1fe7362f301f46ba6890721bb49f06833629e80cf034f0090e98e9637a2c58698b3a7ff43d8bb8b2a81f1aa0c10ad01ff3b40ee855a80e0a00ef03ba7420c70160f7a11825c10c50e86960d2014086c6eb39f918842a82f2ea88fc11286d13b9a5013004b1f90858b5275d35b81fc46a8581068a610d203122f90e885684225a0f3096001300021fd12a06910885b87344723f490ccf5227d29880000000290810d7c02a12b3570444daa00029100000000000331f9c0d802c0000000bc24102dc00000004ad4040000000827000210c0005be250209068e0000ca892c00074a31c90ed1160002d716ec910855089115065c5d113e0ab064a5500b784647307cd26a8c98f1e4c52870000dc000000018184c64582a600000005ac0000ff862e0001df817c0000bd4308ed05800001b68000f2a0001fc0000a242932471d9830e7123f907
  | 19 => 0xe0c87c18f273173c6f072a08987848000df2a20608e4e17805392785fe0a92a39b68ba82eb2a58038ee24512be8a84bf04b3000093800044500003cc1b874500000001de0d609088600001454479e381784612a78d68d76456335054c5e258715400008ec1a20fb0144ab646c1ee12fcd5a6ec16d000012a7e1107000c1ba7471168a1c1c682c00019244ac1f31bb00000003730ed800000058828a119800057235e0718da45f10420004f326873ad0000c448480a81834f863f91321e4435061f0a909101d400001000205d84013f506608507510c90f78aa82e626e1a0035861a2d9914c83664c3f994005205b13b08c449b279e1648c084bc5c90dc1bc8a4a1d60001594d6250b1781ea90de4ba08f0be111409733d08844aa09f391096c78e3ff44689b8acc10737807e503029c4050b1082a11c1449b8cef0344324000095600000009700002d016898c453231609b078039a1170419268d867b600012344e40001190000eb82493821b4102a00000000000005593998778d201b92e1901c2e000000c8000b8a19a11000006106cb26d80000005d00d88000d901302a51748e460000f59c500002a511a116411050825a8a3c0125cc3a189a489a74800019908641ed2618c380000da06708688e81e92698c148244ae26c0de510278a36c0f100001a01ec80990fc85f25185ec0004193f6918c1e01cf1c81bbc91e5621a310f4e7482a349208109c74c2df9aa82446190de9320cbc0a32f5a118e520cb14a8dc850815842891d403a44a2dd0000cca0871f81c1ca588923b9a0708705b72f51e901aa57f01b21284560001490ae000010e0000da0f662450000d703ae76a000000050452700013a09261080f28ba400884d3b48768e045fb0cb0c401ec26f3671310ff000033f000034a64100000009481ba1090000dae3d005280000c200f1119aa4000609214800039462600000000000003f1a180fb64ea33e8df4c1c32d0869c74bc65530f18b54f9e1c22cc15dc2b25b93731be8d4c29a0d593d8e76005179875070a64a10080c02ea51e23f9404cc233937e858c55e36b4081c590046973720ca8ade645193938cf8a1e20221878b4e04a3a98e64f740ba3a31cf470c4700c08c34e7039d00382580000000000fa464800000000004a800035f8dd08261fd3968ee06dc00034d811d11058d000141800000000017f0b4400000009040005b52168a14c7670a08e80000000e7000069c81a01411d0000b5e29d0000610000000092819456400039810380e418000007e8ae6000311800032833225400000001e704608f43ea3c10269af847814716b08f8b200000000d580720003b900009ae15743a9fc00006ba0da0000ede00007d0ea402049539200002d261619000000343410001d88a4605c18e98940e20000001bd444c1e600000000001
  | 20 => 0x7fb1ca099c0000d90000cc072e2bc2979650ffc0d02c01f650ba82915f895c1c271006085444f07d21e3157c58a6773539018a200000000bf44b0608000050c0000002d00ba857c86b0218000f7e000342800095e0002d09ad80005563d80aac10c0000000000fb85f60c69cc81365753e88000e6e0000001cb8a8463c0110000a6c6672bc18a51004bc2e585acb222d22f705741dc57e42489f8b5684c2321a886ee0003559248bba38b2e002910fa00000017ccece55d2a180009ac617015831c00053238b8b0475482e11619701f628633a18c883e26a3d421b00f0669014009438662b29599c4a0e42a2ba00000006a138c14e4eda3433da9e9904200000002ac00036200009441d243f0b39d24f1203f167898000078011da1dd0b85df37d95b865e00b1618000000208000200c0000003661c200000000001cac14000000012506147810d482287f842201a14647c46112be1dc056200036d9330aec1552178d843147522b68c0506000000000000004850000fc40003e53f780005ca06726a0b6400000034a800048c00009c0450a7c3cd2c520f0ccc39c30a800100800028105386f63af2398c790745e000012ed1186343a8205cfb00002c101881ea0002b20d204f44111138000f9045e1b196582c47ab2de02e4fca3fb2b0948424c3d42c70d9c0004f30fa15200004ce2230ccc75c31b0001bd80004c100007a84d083f1710cf00002b5053000089e00007f00000005633fb84e8e1c0000001810e164022630db046c21f3869f4073c7af3b28f14f0a28e2ff80003d02fe2b610b80780de191919cd500003b01cd09383b10000000708040322180c49a1f030296d01261b232e88e0e1800038f99540000002cf84400003bd2f394f0f8847e429800027800014892f8814000207800000062a2d280000003b90001c94c966000410ae49be1162a0959cd404050000f2c5a648420489d0090000000066459a5f000000009c45492d515c4a261be2240b7800006e00000000007440001c780005dc0e800000f200037700002b80003178000000000000000048486400000000003294329e680005c407b8c7ccda0550ee0aecc7e5702db133cf203cf23d086cbb23c3285191c0488972b49e1c0ea20c0470c4ccdc0aa2529f5881861012e989ceec54603d01d0fdc10a0c58018c5006310501a0f5c63615ea05106836002321d82583e44340e30e004b20af18ccdbc28d1d21a3cf7071b1d9a258d883ad1e71010d648350011db86cc37c286905c01876b00013ac99a45a0359e743aa8013e9976054c4e028a8f4c61e6a437294102f271c04f15701923883db94d4a603e62349ad40006ff07295a812069a3aa1eecc8067b25880009fc26119a835c0000000000a8109e0000b99d5cbda16c02e913046062e435184888414a1151a4cf623310b91
  | 21 => 0xde00033f93f08ee07b14585509e810102da1110ae7960ec195cff257930a0b90d181092c7806c0002b61f68f4447200013808b86067012239fb032668d0000504de857a33000000004de000134400000000000000ee0000f21f24e1e02737b91b40ac20920f084c4b446f0e48a04776
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x181d8754c31d91200068354d820c76448001a195360031d91200060761d53cc36448001a0d5360b30d91200069154d820c76148001a515360031d8520006079d183196614800141d9319574985200050764e75d92614800141d939d46498520006071d183195614800105d981cc65585200050764c65dd1614800105e9819773585200068a55080508614800105d93a1b75485200040f65287d95214800103e981d7644852000417a6065dcd214800703c985d154584200050765075dcd610800141d94217735842000507650751cd610800103d9421d53584200051325d534c96108001a455320532584200068c5508050561080014549754e315842000589650855842108001a448520d610842000499261535842108001c457354d61084200055264c855c021080019288521170084200045a261545c02108001c296455170084200051364c75dd92008001459931d776480200050764e759d362c400141d939d574d8b100050764e855d362c400105d93e1d54d8b1001c17a637354f62c400142f9755142d8b100160be1d5450b62c4001a295420142d8b1000e1321d534c962c400703e98dd154d8a1000507652759cf628400141d949d573d8a1000507652855cf628400103d94e1d53d8a1000513e5d534cb628400384f8754d32d8a100069154c814cb628400582c875514258a100060bdd182d07654400184f7360b30d9510006866158018f644400142f925c775d91100050b64a70dd76444001435919c375d91100068354d820c76444001a195360031d91100068354d82cc36444001a158560464d8d100051364a71dd76344001459909c775d8d1000513e4970dd76344001a0d5460b41d8d1000683551821036344001a155460440d8d1000689615811936244001a498560063d891000589644745536244001649901cd53d89100048b65285dc7624400182e8755341d891000613a1d530c76244001a495360031d89100049364e85dc3624400182e8755040d89100068955181103624400184e8754f30d891000689615811906244001a4985600631891000781550635046244001e086454d30189100048b650855c4624400182d8755341189100068a55080504624400184d8754c31189100069254d800c4624400124d9321570189100060b61d541006244001a255460440189100061361d53cc06244001a455320530189100040f65287d95214400103e981d764485100050765075d8d214400142d941d762485100050b65075189214400105d93a1f65481100050764c75d91204400105e981d763481100051364c75d89204400144d931d462481100041764c87551620400703c985d154588100050e24174551620400103d9421d535881001c172617354d6204001454915cd53588100068a550805096204001a45532053258810
  | 1 => 0xb00028000000068000e48e0012954823a001e04200628010a8a46864002d00018006534910002a00800041c2700034051991976b900000000000000000000000e8000032c0000000005ca2002c852a62a000fead6302c000000224585c001f57a003ca85242b439f896861a898687b1b8f53c45311d8280e4102420594d310a0b04b0c1746a49a6d1e664c860623e2888d6a000f0bca6a8000ec6c5b251c120ca1e300f4324e044de24339b93e7c458012a005f1094e814407c000780c1c08000000e020201004200102048120080038300901000000183002150000c0a140480c000d0300c400000800021300008061504000060100000061f03000160f0209c40040880c180000e1621d534c1608840703e98dd164d95210060edd080593654840103f985d064d95210040f65286dcf6548401a0d8460863d952100513a5b734cb654840160d9418d32d95210040fe61741d36548401a0d8350842d95210060bdd182d07654840182f7460840d95210060ddd181103654840184f7360b30d95210048765286dd7634840181e7661075d8d21006079d984197634840141d9799154d8d210048726164553634840141f9759154d8d210058624164553634840144e96dd772d8d2100651a0775dcb634840144d929c775d8d210051664271dd7634840160d929d154d8d210048726174553634840188e8750842d8d210060761d54d076348401a0d5460b41d8d2100487652859c3634840184f75e0970d8d210060761d541036348401a0d5460840d8d2100685551811036348401a295460840d81210068c55181103604840181d849cc659812100507650655ce604840141d949d76398121005076527518e604840103d981d065581210060761073195604840103e9819774581210050765065dcd6048401a455320532181210050b65075dd92108401435941d776484210050764c75dd1600840141d9321774580210050764c751d1600840105d9321d545802101c172617354d600840142c9755142580210068a5508050960084014389755240580210069454c814c160084058348755141586200041764e86dd36548001a0d8360864d952001c17a637358f65480018577320563d952000417e617318f654800142e96dd142d95200058364c6450b654800105f985cc73d952000683611320cb654800182f7460b41d952000613dcd820c7654800185b7360031d952000613dcd82cc3654800121d93a1b75d9120006079d9831d7644800181e7660c65d91200050765e6354f644800121c9858d53d912000507e5d6354f64480016149158d53d91200050ba5b75dcb644800192a80dd772d91200050b64a70dd76448001435919c375d91200058364a7354f644800121c985cd53d912000623a1d320cb644800121d93a1671d91200060bdd7825c76448
  | 2 => 0x9203649901ec14b960009d068757e771c30d9060240009ebc55185468e002c42a2236b092208052916e13419d500c700000004d101594016001ac0040362a5705f062d8baae3186c86710013024000023000980b8007e72002ac00b30017800af420000000021cc0e52002d1285a13800005752a
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1c80ac0700185681e3224c20280414a000481b494b6e6996ca9080240da4a5b75dcb63484018234b503baee5b1a420090368c9755142580210050514eaa100a12c01080240da3a5b7450b6548001206d1d2dbaee5b224000c0aa5a80dd772d912000481b484baa6992c210002844a754c814c96108001502d210a41ac21084000a4268c85211700842000481b47cbaa8a16c58800282ba75508050b62c4001206d272ea9a65b142000a11e9d5320532d8a10
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa00000000846204005005b4a5a81dd772d8d21004809b329d542014258021005009b3a5a80dd772d9120004805b429d532053258420004809b3e9d5420142d8b10004805b4e9d5320532d8a10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x4c
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x124c
  | 8 => 0x138c
  | 9 => 0x94c
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124d
  | 13 => 0x124e
  | 14 => 0x138d
  | 15 => 0x138e
  | 16 => 0x3
  | 17 => 0x8c
  | 18 => 0x8d
  | 19 => 0x8e
  | 20 => 0x128c
  | 21 => 0x150c
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128d
  | 26 => 0x128e
  | 27 => 0x150d
  | 28 => 0x150e
  | 29 => 0x20c
  | 30 => 0x20d
  | 31 => 0x20e
  | 32 => 0x140c
  | 33 => 0x154c
  | 34 => 0xb0c
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140d
  | 38 => 0x140e
  | 39 => 0x154d
  | 40 => 0x154e
  | 41 => 0x94056
  | 42 => 0x95394
  | 43 => 0x5254
  | 44 => 0x94054
  | 45 => 0x94055
  | 46 => 0x95254
  | 47 => 0x5394
  | 48 => 0x125394
  | 49 => 0x4954
  | 50 => 0x124054
  | 51 => 0x124055
  | 52 => 0x138054
  | 53 => 0x138055
  | 54 => 0x124954
  | 55 => 0x124955
  | 56 => 0x95255
  | 57 => 0x124956
  | 58 => 0x138955
  | 59 => 0x138954
  | 60 => 0x138956
  | 61 => 0x139254
  | 62 => 0x139255
  | 63 => 0x98095
  | 64 => 0x98096
  | 65 => 0x98094
  | 66 => 0x99294
  | 67 => 0x8994
  | 68 => 0x128094
  | 69 => 0x128095
  | 70 => 0x129514
  | 71 => 0x150094
  | 72 => 0x9514
  | 73 => 0x150095
  | 74 => 0x21294
  | 75 => 0x9414
  | 76 => 0x20094
  | 77 => 0x8214
  | 78 => 0x20095
  | 79 => 0x141294
  | 80 => 0x140094
  | 81 => 0x140095
  | 82 => 0x128994
  | 83 => 0x128995
  | 84 => 0x99295
  | 85 => 0x128996
  | 86 => 0x150995
  | 87 => 0x150994
  | 88 => 0x150996
  | 89 => 0x151294
  | 90 => 0x151295
  | 91 => 0x128214
  | 92 => 0x21295
  | 93 => 0x129414
  | 94 => 0x141295
  | 95 => 0xb0214
  | 96 => 0xb0216
  | 97 => 0xb0215
  | 98 => 0xb1414
  | 99 => 0x20b15
  | 100 => 0x140215
  | 101 => 0x140214
  | 102 => 0x141554
  | 103 => 0x20b14
  | 104 => 0x154214
  | 105 => 0x154215
  | 106 => 0x21555
  | 107 => 0x140b14
  | 108 => 0x140b15
  | 109 => 0x140b16
  | 110 => 0x154b14
  | 111 => 0x154b15
  | 112 => 0x154b16
  | 113 => 0x155416
  | 114 => 0x155414
  | 115 => 0x155415
  | 116 => 0x141555
  | 117 => 0xecd
  | 118 => 0x1a4d
  | 119 => 0x104c
  | 120 => 0x1a8c
  | 121 => 0x95a94
  | 122 => 0x95054
  | 123 => 0x95494
  | 124 => 0x95a55
  | 125 => 0x94ed5
  | 126 => 0x952d5
  | 127 => 0x952d6
  | 128 => 0x95496
  | 129 => 0x99a55
  | 130 => 0x98ed5
  | 131 => 0x99616
  | 132 => 0xb1a94
  | 133 => 0xb1054
  | 134 => 0xb15d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1154
  | 6 => 2291
  | 5 => 2200
  | 4 => 204
  | 3 => 16
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (46922+((h/384+packedAt gbK7 (42698+(h % 384)*11) 11) % 1523)*12) 12
  | 6 => packedAt gbK6 (119124+((h/763+packedAt gbK6 (109968+(h % 763)*12) 12) % 3025)*13) 13
  | 5 => packedAt gbK5 (138596+((h/733+packedAt gbK5 (129800+(h % 733)*12) 12) % 2641)*13) 13
  | 4 => packedAt gbK4 (14892+((h/68+packedAt gbK4 (14280+(h % 68)*9) 9) % 269)*9) 9
  | 3 => packedAt gbK3 (1321+((h/5+packedAt gbK3 (1296+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt gbK2 (560+((h/2+packedAt gbK2 (552+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff81ff81ffc0fffffe0ffc01d33dc1fa63f3e7
  | 1 => 0x1ffe07fe07ff07803ff03fffecd27e3d9ccc7f
  | 2 => 0xe0fff80007fff8003fffc001f0e38fc61f0f87
  | 3 => 0xfffffff80000003ffffffe3f03f007e00ff8
  | 4 => 0xffffffffffffffc00000003ffc0007fff000
  | 5 => 0xff00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2900198088c008a3960464144104c0d82151e3
  | 1 => 0x120a02a2035105048a10094c845016288cc42d
  | 2 => 0x40d7681045aad0092daa802930a30b46170e86
  | 3 => 0x8e5b555d008401231cf32b03b03e007600b50
  | 4 => 0x10f9c679663ce65c008200c03ef80007daa000
  | 5 => 0x9c41006180308460010c23003ffffdb0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36767
namespace PEqualNP.Outside.L_meta_36767
open PEqualNP.Outside.L_meta_36767.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_2_0 : Interval s3Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 13 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 75 := (concat bs3_3_0 (concat bs3_3_32 bs3_3_64))
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
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 626 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 bs3_4_512) (concat bs3_4_544 (concat bs3_4_576 bs3_4_608)))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 699 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 (concat bs3_5_192 bs3_5_224)) (concat bs3_5_256 (concat bs3_5_288 bs3_5_320)))) (concat (concat (concat bs3_5_352 bs3_5_384) (concat bs3_5_416 (concat bs3_5_448 bs3_5_480))) (concat (concat bs3_5_512 (concat bs3_5_544 bs3_5_576)) (concat bs3_5_608 (concat bs3_5_640 bs3_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 42 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 13 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 75 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 626 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 bs4_4_512) (concat bs4_4_544 (concat bs4_4_576 bs4_4_608)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 699 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 (concat bs4_5_192 bs4_5_224)) (concat bs4_5_256 (concat bs4_5_288 bs4_5_320)))) (concat (concat (concat bs4_5_352 bs4_5_384) (concat bs4_5_416 (concat bs4_5_448 bs4_5_480))) (concat (concat bs4_5_512 (concat bs4_5_544 bs4_5_576)) (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 42 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 6 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 16 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 204 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_2176 : Interval gbAtlas 5 2176 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2200 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))))) (concat (concat (concat (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312))) (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))))) (concat (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)))) (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)))))))
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
theorem bgb_6_2272 : Interval gbAtlas 6 2272 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2291 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))))) (concat (concat (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)))))))
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
theorem bgb_7_1152 : Interval gbAtlas 7 1152 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1154 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80eeeaece8eeeaec80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36767.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.or,[1,4]⟩,⟨.or,[2,7]⟩,⟨.or,[4,6]⟩,⟨.or,[2,3]⟩,⟨.and,[1,10]⟩,⟨.and,[0,11]⟩,⟨.or,[9,12]⟩,⟨.or,[0,11]⟩,⟨.and,[13,14]⟩,⟨.and,[8,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36767

open PEqualNP.Outside.L_meta_36767 in
theorem PEqualNP.Outside.L_meta_36767 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
