import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36326.Model
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


end PEqualNP.Outside.L_meta_36326.Model

namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat) × List BoundPool

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.1
def apools (g : Atlas) := g.2.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [6, 6, 6, 6, 8, 8].getD j 0

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
      testAll (k,ws.length,ws,preCov true ws,apools g,links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ p ∈ apools g, ValidPool true (roots g) (target g) p) ∧
    (∀ a ∈ first g, faithful r s a) ∧
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
        exact decode_faithful _ _ _ _ _ ready.2.2.1 _ ((selectLive_sub _ _).subset ha)
      · exact ready.2.1
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
      exact poolCut_sound (ready.2.2.2 k i hi hn) _ he h.1.1 hc

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

end PEqualNP.Outside.L_meta_36326

namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x13320100100be40bc42df31be42bd41bf41dd31de30bc40dc30bf43bd43
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xb000972948155510c23aa6214b14941
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s0K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s0K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x31000110001dd43bd42bc40de31bf42de43be40dd32de30dc30dc31df32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcab28c6154514ca5aa4204755031
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s1K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s1K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffffe07fff07e0ffff83ffff07ff03e79f3f3
  | 2 => 0x81f07ff83fff87f0f83fc3c0ff87ffc1a6ccfc
  | 3 => 0xfe007fffc3ffffff003ffc00fff87fffc70f1f
  | 4 => 0x7ffffc0007ffffc00000ffff8001f80fe0
  | 5 => 0xffff8000000007ffffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc20023080208001184804463008908c085171
  | 2 => 0x2444a45191440a506a1a428a54852584a2c4b4
  | 3 => 0x108948820a8844a60424a81089504a31450a0a
  | 4 => 0x596e712528ed573bb6862224ee660319f80fc0
  | 5 => 0x618c61c6330e67ccc73733380c440c21f7a000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xdc31de31
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/1+packedAt s2K4 (32+(h % 1)*1) 1) % 2)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffffe07fe1ff83fc3fc3fffe1fc07fd31f3cf
  | 1 => 0xc07c3ff83fff0fc3fc3fc381fe1fff02ceccfc
  | 3 => 0xff803fffc01ffffc003ffc01ffe007ff0f0f0f
  | 4 => 0x3fffffe00fffffc00001fffff803f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8510023080220004c044048ca02451281051c5
  | 1 => 0x9308445194081141441c41146209321846c45c
  | 3 => 0xa2aa8830d548ad8222aa8215540a4d30b0e0a
  | 4 => 0x2c5331242906acaeaa8220499992c063b00ba0
  | 5 => 0x306221c63198cf333333327011030083eda000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x10be40bc40
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/21+packedAt s3K4 (32+(h % 21)*1) 1) % 2)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffffe03fe1f087fc3fc3ffff0fe070133f7cc
  | 1 => 0xe07c3ffc3fffff83fc3fc380ff0ffffeccc8ff
  | 2 => 0xff803fffc01ffffc003ffc00fff007ff0f0f0f
  | 4 => 0x3fffffe00fffffc00000fffff803f00ff0
  | 5 => 0xffffc00000000fffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc31802388422100cc04c048e701231181153cc
  | 1 => 0x4900444890080101441441121104924844c055
  | 2 => 0x842aa8910d548ab4222aa824aaa044b30b0d0a
  | 4 => 0x165331222906acdaaa822048ccc96023b00ea0
  | 5 => 0x186221c33198cf6333333270088180c3eea000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaececc0c0eeeeeaeaececc0c0eeeeeaeaececc0c0eeeeeaeaececc0c0eeeeeaeaececc0c0eeeeeaeaececc0c0eeeeeaeaececc0c0eeeeeaeaececc0c0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x817e51ccafaa690fd8c710bea8c857e54442fca2107e94032bfaa0437e5190bee4290df54e42be28a817e5390efea0a0df15332bfa92837c514c2fca0085f55230df20a837c540c6f8a6a07b54a10bf29e217e52d07f661187d8c510fba8a657f53843be61185f94442df21c817e538837c86a1ef90440eea1a61bc43902faa3a17d10721be28a876e528437a84215f54443deaa0435d53086faa7a05f95010be2a2657d50906faa5885fd4930bfa9a217d50087f260185f94830bf28065f721886fca120df55220bf2a2417f53486fca610df55120bf29465ef20882fca621df14542f710a41bf4210ae8a2997e48020beaa2617e50d0afaa3a1df14d41fd10041f651102faa9885f94840fb28c417d538c3d86510df95221fb98e437f54cc2faa710df94e40bf280637e510c3ea8220fdd0721bfa9a41dd531037aa8195fd5230fd98261ee20482fca1197dd0631bf298857e5410efca218dfd5332bfa9e217e53103f621086f95331f7a92637d52106f8a918df54b41be2a641f721c43e843885f55331f790c437b5050efca890df94020bea84857d52842f8a5087ed4143beaa4657f544cbba64194f55030f799465ef32886fca2194f55320fc904217f540cafaa9985fd5221bea84637e5090efaa620dfd5020bfa8a417d50c86f8a9186f55331bf28c83f710043ba6218fdd0541fa880217551103ec4210fed0220bea94437f540c6f8a690ef15130beaa0617f52c43eca321df94f40bf28881df324c6fca3a1f7d0d43fa18e435e53086fca020df55320eea1e617e54c87f081105fd5120bea9021bd43107f461107ec8220bf298217f54486faa6105f95210bfa8a61f9304837886206fd0d42bea8e6575510c37883207b88720bea9c837651882f8a0995f54643bf290837c54cc2daa5087e88110beaa0637d53c43ec8220df95021bf284437d50ccb7e87a17bd0942bf28c65be43102fea898cf95021bfaa0217e50c86fea9905fd4a10bea8c817c54842faa6215794c40bf2a065f5510cb7a87a05f95232fa208437e53107eaa3107d48421bf29e417d5490efaa2215f14931bf284217d51083be6318fd54440bf280817c50507ee8320dfd4143dfa1e813e540cb7e81205f95031f699065bf41106fea2a05f15110bea84657e50d077aa8187ed0240bfaa6437e544c3da4210df94a10fca80437f53886fca1995e54032bea84877a50087ba60185f54831be2a0613e54c82faa918fdc8510fa98a437e51cc2faa198fb50b20be29e417e54106fea6085f14e10bf298637c504c6fca9905f55020f6190437c548837aa9907e90040ef21e617c54cc67ca998ef50a40bfa92877e548c2faa3905f14f10bea80877e52d0feaa2185f151309e2a221f910042fca520df54910bf29c837f53502fca9884fd5110fb988437d50d0af8a6085f94742
  | 1 => 0x741086fea9885f14c21bea94877e52086daa4206f95030bba8a657e540c2eaa3107bd0a42bea90877c52442faa7106f50441fa98c43bf42902fca690df94c32f6292637d54042faa0215f94043beaa421bf43906fca7085e14143fa188437e5410bf0a0a1ef95032b7a9263fb400c2faa5205f54341bf28e81bc41102fca010f754c21be29841f55190fee6298df54032fb18a437f540c2f8a090dfd5331bf2a081dd324c6fea9195f15032bfa82857e51c82faa810fbc8421bea8881f8400c2faa110df94f41f7216417e54882fca6185f15131bf29c857f50486faa5985f55240beaa4837c54082faa2195f54041ef29881fa300c3ee8298ef90942bea8c217d548877e85a0df94240bf290417f5350bdc64195f55110fb20a217f53c82f8a4a0fed0330bea9e856d520c2fca2087d90710ba28a857f54842fca0185f94831fa20c63f5310c67aa998df54343bf29085ee42483de6410df15221fd104217c548cb7ea89877cc431bd28485f4514cb7ca9905f55321be2a021ed4210bdaa42077ccb31be282877d52882fea0995f94f42bf2a6637c524c3f680905fd4810f7992657e5290efca4085f54430fa10a217e51882fca5185b94830dea1a817c5350afca918fe10330f610e41fb204837a8720dd94430df20281bf42506fca5885dd4542ef298436e52103ec6310efd5110dea12837f52442fea098df14142be29e43f930883dca5086f90640beaa2657e52443dc65906f50840bfa98417f54882fca5a05f14e21bea8c657f524c6fea2995f54b31de2a221fb10442fea790df94441bf294637d51cc2eca2205f94d20bfa9a837d53843ee6318efd0c43f6996417d54486eca2197b08520fda02817d52d02faa6207e10120f6a90617e52cc2fca6107d4c710beaa263bf421037ca810fb8c920fc902217d53086eaa321fe8c120bf28c43f531442fea4a06f50c43bf29a217e520cbf2a1215f54a41bb28c877d528c3da64907bc8020dfa1c87bf401037e8320f7cc030be28a41de314c6faa6085e54242bca8043df320cbf280205f94343fb188637d52102f8a7105f54d20bea9e83fa10042fca8106fd0a42be29a417e51903dca4185f94a40bea96877d538caf8a990fe94021bea9a21ed20083dc84217d94430be29021df328caf8a8905d54432bea8c61de4310efaa790df94e21ee996637d54ccbdc4290ef50b419faa261bf43106f4a0197dc4210bea9463f610442fca9985f94242bf288877e5290afea2a15f95332bfaa2617f5150ed8a498df94220be292877d500c6fca8995f54620bf296637d53c82faa3a07790d30bfa98433d540cafaa718df14d10bf286637c54087e8a2a15f94643eea18875d53102fca421fd94432bf284637d540caf8a4a05f15121dea00817d53902faa4187dd4542fd284857e510877e86a077d0e43f729
  | 2 => 0x2001c060401002c0a4d00201006005bd0200100c020000b000ed0184201c000040000818014006452d6dc6c0000d0040a0101219d14010360b4000e5300080754c0c010084c402150000041101c73334b003c04214340024500c030041f0000e0dc30020000540219c4d01c040880008c000200a0081f05c0056267000650680104c01554813cc180881105000014190580102519028070241a34c001a8b609400074080600a005ae00c020049008836030023080b024011b8250544f150190002400000000000140f04c0d094021800d0581d000020603604c0f001be0040000c19018970340000017080050000a0040300009200020440f0180a0b89501c027ac640000123c010000000c0005803018017c00700c030740901809200500043ddea1a85f4414c6fca790fb509209e2a2617f53882f8a5885f94630faa0e21f541442fca1185f95131bfaa221de324cbbc60984f55021bf28c637c54c42f8a2997e54032dea1e857e5010a7ca8185fd5231beaa485f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2528c25e6314b108f590538427a60d4c219d195414434d5394840b618143cc27a60d52319dd855210e6d62942419b189544c6e562104218f590534833854481109b59432086746155132ae191308825d63d5021dc9865090a7661d50319758e544863e6414f209b98a508c74e5394840dc945500ca6d6214c109bd95320ca5e63150109dd8552cc31e5454c21cb98a54c82b66190c40ad59021c427661d5032ae1814350334544c5109dd85548cb6a6094a10d554c31086766114c218f590520426e6215210b558c21c427a60d50219d984540c23f6454d208f99353c426d6214143ad993310866e6215020b9185320cb5a5394021da982521026e62141438f59053c82756114f209758c54842d96310120ba982424823f64540318f59252842756114d209718d524427a6014c208f990540ca3d6414c219d987540c26f6548421ce181540c31c5490d309ed81544c73554544329b58a50042796015032ce551500cb345490510cb990524c676658c521d914b414c67561d53328f99053882766114143ce95150086ba64c8120ad18542d063d64149319e580524c66d6215030c7552530865e63150219b58a508c6f16110120d994951103725194032d5cc9510ca7765484219ed95200827b6550040b658c40cc3346155021ad993314c674615523297d95310c71d53d0840c754e431027a60148108f59353086796094b41d5185530867661d53328f592538867a6094b41b9189318867561150329758c548833a5454032cdd09511026f62551319e580530863e6494d109bd95200833b4294242ce152204423d6595021d6181531032e54948309d18554482e4614cb209d584538827b6544010da548400c27561d4e20cd552510c2ba6090942da54a300c27960d5021b998a104423e64d4f20d9148414c66f6254730ae58041102756115230ae191300c36552944408f990540c31d5350840ba988404832e54548308f99052c423d6494f10b918542c823d6414e208f990520433554544308f59053c8679651003097d95300c27665c85108f59353c826c6254d109d584540827661d48108f990530865e63d53109b98b538436652944308fd954310ed963102209dd85534825f6550c43ce952500cb6652c4210b9189314875653944409758c52042766195132d694d50086ea60085209ed8154ccb665254430d514d314427a65d01209e98252d0f354254440d954a510c23d6494c31da549300c25d6594c21bc584408827a60150319d59731087555394440ae99320883655254430ad185429027b6055132cd152314434d53cc8218f992544c2746154843c754c411023f64543328fd954210a6e62942419bd89534431d5310c40cd952510ca7661150108f99053482e5610ca219758c540827960d50329e58252d0e7661152209b588540423d6414c10
  | 1 => 0xc674654c5219b988530436960149319d587540c31d63151308f59252083665294440ab59021482f261881109d98754cc27561d5032d914b314c66d6215031d554c41087696214143b518532cc63e65151309d18552d025d63150109dd8554487693254032ad99331c865d63d53109e580540c67960d4c21b358c214826d62951319dd8552d027a60149319e980540cb3551904409d984548c23d6590c40cb552520c2b86050f428f99053c871d54cc0309d98753882756114c209d58653d0b555388421ae1814310e746154b309798c52042b66190e40dc98251883656114931cb551520c25f63549109d594410863d6414b10ba580328863e6494e219dd95411071c5350d42f1cc9318867561150309e98354c873954d00309b98b548435553544409b988540c31d5350040ba580320863f6454d1097d95320ca7a6015021ce552500863c6454221d314b324c66d62152108f59253486e4624c710cd552510ca3d65950309d98754883595394021b9189310c67b654c0308fd91518c26d62d5030da980524c7374314542cd951510ca6f6254d21dc546500cb2e6494a10bc980214423e6494a309e181544c6b86050d429d98653d0a7a6014c21ce552500cb555348421d9549511036732145328f59253442b461508409b58b538434e53548409d58754cc23d64949108f992544426e62940109e983540ca766114d209798c530872e5450b209e583548cb9a4310330d354d521026c6550920cb590524c73543145429e58053c863f65500409b98a544c6b8644c120ce153304c275650c4219b988530826d6215230ad9864350f5532544328fd95411063e6414e1097d8d544825d6314b109dd85544ca3e6414c208fd9150886766114f209bd954210a7860553329d997414c7c732cc4218f992534866c654c920c7551530865e63150309b58b54842776154d219b988538427965840108f994544433a4314143ae181431063c64549108f191518c31e5350e4197195434c277654c4318f19150cca776155120da54b400c2ad64087209d584548836651c82209758c540879943d03309e58354c863e64d4c219e19530482766114c209d984540cb5553cc421ad590214425e63152209d587548833561151108f992528433a54940219718d544831d544c030cd952510c27661150208f59353c423e6494f109d586508cad56308510b358c21c827661942429e983548cb3454085109e98354082766194f409798c54083395454021ae18143d025e63951219b98b540c36a52482108f992530c63e6414c109d986508cab86050e418f99252083a942101209d5845050ee4614c920d654d50086746154d20cb592528433654544309d984538826e6215230d594d51103726114143b9185424823e64149318f992524427b6055130cdd0e5190e6e62150318f59
  | 2 => 0xe4c150004a050b868002949808704f0f008000c0992c1a160009822020400030420c01408010600d46120001408111e2844094018005e140180c00010000e2c9e04804942f008000411000fc0c13000b8041f0206418160186018000015818f4208001e070000400140000014000082032040d81c0026028ac023b1f83cb4070f0100001068880600000840a020684408000081406010d0080002010ec0003000083415010503c3901814007803070101800040700400000460d01800d4000282cc22a0207408030207c7006028b81c14040e0a039040a66d6214e109798f54086766114c10c7952530863e64150219b18951cc2d663d0531cd15321442e4624c5109d58653d02796015021dc5845050e786548110cb949421023c6454d20d318953086786055132c754e41103715154032b9986204825e63152109e98053c8674654c5108f191500c7e021481108f59053082756195132cd553410863c6454d109d5865090b6a62141438fd91524436a32540328f997435026e6215010dc5865090b1d53d00409e583548c63d65950329dd95100435553d0421ad993318
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x400000510804001249002080079154d6210421ac0e2992a0196266414b314c6d038a8420241265da4310330a64e3218a0a1e2864549300c2a4b90c0a98810d5d85408510c8cc62968298da1740852044350a12c220241a258d4210120c8acb9966210e1a53181439070aa98c2a10818614c6050d42c2aa730c8620644531893144314b22c029263c81502148110a60e0a18a2a1549701895308730b12c228287851516308510b82e610a408861953580411030b322a79884389150624c510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc81631c54210120d00545cc2148110921871502148110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s4K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/231+packedAt s4K5 (17064+(h % 231)*10) 10) % 632)
  | 4 => 2*((h/192+packedAt s4K4 (17974+(h % 192)*9) 9) % 473)
  | 3 => 2*((h/23+packedAt s4K3 (1421+(h % 23)*5) 5) % 29)
  | 2 => 2*((h/1+packedAt s4K2 (180+(h % 1)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe0ffff03e3ff80e3c7f1fffc707ff0013f4fc
  | 1 => 0x1ff0f8ffc03c7ff03f8fe381f80707fcecc8cf
  | 2 => 0x1fff00ffffc07fffc00ffc01fff807ff0f0f0f
  | 3 => 0xe00000ffffff80fffff00001fffff803f00ff0
  | 5 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc2621011844801020413048cc111311801545c
  | 1 => 0x44a621228c90b0301c8521154822526864c8c5
  | 2 => 0x8840524510094046400a4828925024910b050a
  | 3 => 0x188a48828201298a920004124a4c022b00aa0
  | 5 => 0x110cc00e313264ed324c927000c080c3dea000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafac0fac0feeafeeafac0fac0feeafeeafac0fac0feeafeeafac0fac0feeafeeafac0fac0feeafeeafac0fac0feeafeeafac0fac0feeafeeafac0fac0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2217d53d02fca1a1df94e21bea9021f621087be6498fe4c120bf29821bd43106bea6905f54440bea9841ee4210aeaa2185f54231deaa0437d51ccafca8995f95041beaa261ed4210bf641106f50840beaa4817c53506fca1206f50441bf28c65fa30882fea818fe88110bf28443df4350ebaa620efd0641bf286437d54043ee8210ef50f40bea9c836d52106fea6a15f55221bfa9421f5510cafca6205f54f10bf28843be41102faa520f74c630bf284217d5190bea4210df54241bf29e41dc53482f8a498df15231bea8841df318c6faa1a17e10330bca80657e544c2faa7205f54640f7a1285745150afca8187ed02209f2a0437c540c6f8a2a07b48421bea84657d540cbba8698df55331bfa9c437b5050efaa890df94341fca80437e54c86fca199774c030be282637a50086f8a9185f14543bf28e817c53843f0a0a1df94730fda04817d50cc6fca890df94a10f7a14857e5310efca618df94243bf296817f50487f280885f55020bfa9821dd53086f8a8085f54831dfa1887f840483da8490f794f10ef98c617c53c82f8a7885fd5032de2a2437e518c2fca720fdd0531faa8861f531486fea8085f94232be298217d51cc3f220085f54042be296217e52102fca4195f54910fca80657e51d0efea7107d10721bf29e437e53106fca120f750c43bf28c63bd40103f4a1215f94342dfa18837d54482f8a998d754f10bfa9a837e5110eeca321fb50b21fa98c437d53882bca620dfd5021bf290217b504cafca7a16f10841fa20a637d51c82fca1187ecc230bfa9a81f95090bbc60985f14532bf290437c52443f680a05f54f41dfa1e817d548cafca010dd94430be2a641bd43d0b7aa9905f54840beaa043bf42506fca420df94e10bf29865bd4310efea9196f50941bea8087df32cc6fca3905f95320fb18a437d53d0aeaa321de54041bea84437c540cafca8197dcc531fda0661df310c7f440105f15110beaa4837c54cc2fea790f790f31bfa9261df310c2fca6215fd4810be2a2417e530c3f460187e94231efa9a417d51842faa5087e0c320ee992633e540c2faa5987b948419eaa0657d510cafea4a05f54b40f6990657c53082fca9887d50441bea90877c53c87de4210fe0c110bfaa243f8504cbee8320db54830bf2a4617c53502fca4105f54e42beaa4217f5250fdc64195f94410bfaa221bd4350afca0185f94831bea8e87f5310c6f8a610df54341bea9441f75150bde65195f55243bea84877f52442f4a1215f55321fa208437f53c82faa521fe88210bfa8265dd53106fea9887b90921fd204217d52d0f7a8720df95232beaa0617e54cc3bca610df94620fda0061ef324cb7c82a0fed4143bea88617f544837ea890df94a30b729061795090afca5a0df95331fd98641dd53c42fca918df94641f7196417c5350afea9107ecc110
  | 1 => 0xb10442faa3195f54343fb98c637f544c3eaa321de54021bea9c21f940842fca690df54c40de20c81ed32c82eca2197ec8120ef980617c54c43ec6218fe94021fa98e21fa30482f8a2a15f54b31bf28c43ee324837e84217e48110dfa04817e53083daa4187d4c510bf2a421bd54cc7b864184fd5121bf284857e53442fea9997b4c920bea94617e52cc2faa6214f15110fd20081de314c6f8a8185f15232bea90617d53042f8a7107bc8020ef99065bf4350afca898df15210fd08021f6510c3dc4290df54d20f7290617c534837ca810df14520de208817f54c86eea2a15f94220bfa92637a50106fca821df14d10bea9a217c544867ea8885f14810bea84857d518c2fca2205f15021f6900417e528c77e8220fd84110fb884217d528c7f2a118df95020dfa1c837a500cafea2a1dfd5132bea8c417e5290bf680905f14943fca80837e5190ff060105f54c21dea10857d548c2fea2994f55030bfaa4217d500c77e8721cf95320df21a877d53c83f081105f54e31de214837e5110b7e80207d946439f2a6637e50cc6fea898f70ca30bfa8a817f54886fea690df54740bf28463ee42c86f8a4a0dfd4143fb28865be54cc6fca521df95042bf288417d51d0afaa420df94732be292817e53c42b8a6905f54d21ef298837e53883f660105f14142df2a065f721486fea8185f54443bf28e85df4390efca7215f55320fb18e21bf4290afca3216f90640bfa8a857c514c3f4a0195f55332fb18a217e52906faa7195f94e43bfa9c21f830843ee8390f7cc230dfa14817e5210f7aa8185f94830fda82657e500cafca0086f90140fc900417d53106fea4a0f74cb31fca0081bd42902fca9105f54b10bfa98437f53442faa010efd0d40bea94815d53086fca2195f94b43bf280637f54cc6faa9106fd0b41f7904417e50107bc64185e54231bc28287f641106faa918df95332be2a2637f53482fca0217d10631beaa4857d54443f260185f54332bf288637d544caf0a0995f94842fb90c43be4250afea918df54e30bfaa6617e53d02fca610f790d31fd9842175510caf8a9105f95021f7102417c50507e8a2a15f15332bf2a2417e51106fea7885f54e21be282657f54c82f8a8986fd0840bea8c87ef2188778a8887ec4210bf280817e510c2bca78877cca32beaa0637e500837c8520f74c832bf294657d54c43ee82a0fecc1309e2a2437d52886f8a5085f94a40be2a4437c544cafea0a15f94e40bf2a2217d52d06fca910f790c43be28287bf544437aa8195fd4520fc200617d500cadca420fd44010fc90421ed52106faa2215f54321ee988617e52cc7ee20085e94231ee988637e54043bc64995f55330bfaa0417c534877a85a0fe94041df2a6417f514c2fea0a0df15321ef194613d54c82fea9185fd4b10bea9e43f7418c6bca610df94f41fd20
  | 2 => 0x5a80a000000001a0201b01c2801802000460100007c0301c0e08c0e0402d02c2d0185300c3a0f01c008420380006cbf038100040200835000003080601c0d014050180b0c2320001b29c044f1d00000302414364720101807c41008001f80c01402011c7394001140006c0e42c040900e00008048000084c0f4143380a01c74054010140000c2504827044615e4070041b2f41f00c5a26825098000557e01c063d8090341200400125040280622402034ed11800008030000000c0805c392c42d09c00020070002002005044590001e0040314c1b0001369022018220000900c0c00943058171ec0069c0107469020020b8000819d0001e3c41c044000080701473044002361c0040d0017906cbf00000000080d41f00c00001030000c02405dfa1e857c524c2faa020fd8c621bf29a417c50486fca818df94910be2a0417e5010efea6105f95040bfa82637e51902faa898cf553319f2a065f930882f8a710df94b109eaa043be540c37a86a07750f31df21083f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x53c863d6414f219798e534825d63d4b109b58b548434d524c430dc9805150a3f6454420d394d521066e62d50309758f540875532544329e580524c63f65504419b588530433654544328f990538823e64d4f208f1915348734544c510d598453482766115020dc9825190e7b60551309e980540ca5e63d502197d95320ca7a65cc110ae99320482766114c108f99254442e8604cb209e583548c63e64148109e980540865e6315020ad185425067a658c1209d58453883ca320c3209e58354c872d52908419b588540c23e6494a10b6181324c67561150209e580548863e64149318f990530426d6214e109d587548827a60d4c21c7551530867b60551328f990540c25d6315221dc5805150a78654c1209e58053c875a5394021d654e500872d52504418f992528c3395454021cd15231442d66190d319b588540c6d96310030ae982421066f654c832ae99320882b464484218f997425063e65151219e9835388769524c030d614e304827b6054f21c759253c431e5350c41ce50d501063c64549109e58054086b46150b41c7952530863e6414f208f191508877160946439b988540425c6354910ba588304425f654c0309e983548c7d1310c1109b988548c71d544c4309e983530432d5210841d6580534837151540329bd89534427665d05318f593528437260944309ed8154ccb3743145428f592524435553d04219d984530823d64d4c21ab1894350a7960150319d185544cae9620c020d5986531067a60d50208f191518c27a60152319758c540866d6295130ba588308432d52d04418fd91508866e62d52109d584540ca7960d4c218f59253c423e6414d20d694e501074d528c8309ed8153d07354314542ce95150086da63c4110ae982429073654944308f993528435b31942319e98251ccaf16010531ba58830c825d6314810b958841c867661d50308f59353c831e5454c21ce150304436932540329798c52c436860548309bd95200835953540418f590538432f43548419758c5150b6952d0030c799253c423e6414e109d58653d027a60951329798c540c66e6214c10b6181320ca3e6414c20b598c414c72d4354841c799053482766194f409b58854c427b6544010ce153304435553104219d185544823d6414d208f990540867a6094b418f99253c42b96010640c7552530871e5450f319e19540442b9640c1109758c540436552544308f5965408756514c4309758e544827561d5032d598c5150a3f65500408fd954210a3d6414b109798e544827561150309ed8153483355110440ae18143106756114d209e9805150b2c5490921cd15321486b46150842ae9824250a776548421ce1512044358534c1209e99740482766114f209dd85548ca7a60148109798c520425d63946409d98653d0a5c63551209d58653d0a3e6494910
  | 1 => 0x426e62153109758c54082796015032cb949429026c65509219b988540c23c64544209dd85544ca7965100309b588548c67a6014c219b988540867960145429e582544cb3854901109b189544c6da608c5319ed8153486b664cc6319e5825190e5c6354321e550c414c7385488110cb551520c23d6414c208f993530866f6550842ad9864350e3e6494820b618d20082b86050d429798c54c42786054c428fd91518cab86050e4197d8d544823f6454630d9949510c27a6094b43b618143cc63c6454d109758e5104334544c5218f59252842e562106318f99053c866c654c9209dd85544833b42942429d587540c2796094b43d558c5150a7661d53329b988540c6d863482109e583540875853c81209ed95300c32d54c84218f590538827960d52328f992544865e6514d20d68c8504cb365494432cd552510ca7661d5330d614f404827a60d5032cd551510c23d6494e21d5cc9510ca6c6254d10da8c9500ca7765504418f99253886e46150b219e980524c77251940329ed95200823f6454910ae18143d025f6354910cb552520c2786054f21b5584320c274654c5108f59052042d5610ca309e594300823d6494820dc546500caea62d01209d584530834d52cc4309e9805488734548c5218f596540cb5953540219e58251ccb4d6214d20ce951500ca7a60d5321d654e501065d6314b109d987540c6746155232cd5534108677654c4319dd85544874c538c9209e195204427561d53329e181544ca3f6550c43e950b41c866e6214c20d694d50086756114f209d987540ca3f6454d218f191518ca6e6295130d694d501076552944309d984538825f63543219e9805404356534c71097d954310e7a60150319b58b540c25d6394620cd551510ca7561d53309798e51042d8604cb31ce552500ca5e63145428f59053c825c6550d318fd91534423d6595030d354e521065d6594c21b6580328c33a540c320d9185521076a5254041da5495010769528c030ced0d501063d6414931cb951520c27960d4e218f592528c2e56210531f28ca30482b664cc53197d95310c7a642107219798c530873a54940219d987548827a60d5232ad18542103555388421ce95330c82f2608c5109e596100427b60551319e18154cca786054d218f592534863e65151109d984540cb2d54484219ed9540103555348421ae18143d0b3a5494032b6181434c67965cc0209bd95210873954940219d9845348274654c5218f992534423d6414c21c7553310c23e64150329e580548c71e63953319d984530873461550219b588540436652944309e580530875853101209e18153d065d63d5310ce551500cb3654544309798c54886ad6210440dc945500ca7a6014c20cd9085150b2d62151219758c54c433554944309798c540872e5494830d394e52107566194f109e98
  | 2 => 0x18140e1b048000a03021780400001240000001604203038001200012980808092ce82040381004023480000100300066100000006000000400010000000430003404c1000000004010e03b4e2d00c2011002407a04000c8a4100881c013c15d683400038001420040365c00010102002040fc00005c00c4a041c8181a06028000e1902008080019000a66e000000a2b9000042000588018020080c04003e0023a000086800230b8ec042915010060608894040001800040015800040e00034f6030202a960541a840a010582016024b80002aa000101400018000232020040e5e0e01024000701410540113d0a00062700005011cc0400000180003080193a04001c004050081e3d6494c319d59441086f160106318f59053043685248110ad185429027860551318f596421067a60d5021da54a50107695210030bc984304433743946439bd89544c76a52940419e583540cada63c42109798f52c42776544010d354d521065e63946409e9825190eb9640c2109d984540c23e6494c31ce181540c26e6214e109798c540423e6494d21c7590534823e6414c218f59253443556114d20ce553400c33960151109ed815310a5e63d53109e58252d06ad62106408f99052c425e6394620b618d204
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x118001405002060040010400088000000300c19458d6014542c2ac8b08a690625625444110324b1aa420061a450d6010531c4ca430a85204397615030442983828628a859218c524811094aed2108390d50704c9510cb2429cc5a0241a150d6210531c54a8b106190710544c43044322b12c229a41491c94314542c50a8b106088532709085150a9438286a90838a54a6090841c34c829e409064a658ca30482a2b98c2a9083641c14310531d22c898860886185418d2044360b126218221851915348421
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x40a1186151310c110e0054589310c110a808050d6210531
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/231+packedAt s5K5 (17064+(h % 231)*10) 10) % 632)
  | 4 => 2*((h/234+packedAt s5K4 (17974+(h % 234)*9) 9) % 473)
  | 3 => 2*((h/30+packedAt s5K3 (1421+(h % 30)*5) 5) % 29)
  | 2 => 2*((h/8+packedAt s5K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe07f8f07e3ff81e3c7f1f81c707ff8037c4fc
  | 1 => 0x1ff8ffff803c7fe03f8fe3fff80703fcc8f8cf
  | 2 => 0x1fff00ffffc07fffc00ffc01fff803ff0f0f0f
  | 3 => 0xe00000ffffff80fffff00001fffffc03f00ff0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc2b211131458210614170494c111589813c45c
  | 1 => 0x445220210c8090200c81210d482229284058c5
  | 2 => 0x882052462009404a400a4820925012510d050a
  | 3 => 0x144a488482012b0a920004924a4a022e00aa0
  | 4 => 0x1184c00c713264dd324c927000c0c043bea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0feecfac0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q5K4 : Nat → Nat
  | 0 => 0x619006030bd43dd31df31bf43be40bf42bd41bc40ef21bf41ed21fa10bd42f910
  | _ => 0
def q5K3 : Nat → Nat
  | 0 => 0x801002287848510d8a0a21c5314865aa5a1cd544408ea9881d1314425aa4204754f42
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q5K5 (i*5) 5
  | 4 => packedAt q5K4 (i*16) 16
  | 3 => packedAt q5K3 (i*27) 27
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q5K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/10+packedAt q5K3 (243+(h % 10)*4) 4) % 9)
  | _ => 0
def q5Pos : Nat → Bits
  | 0 => 0xfceef8f73e7c7c731e3e189e7c738cf380ac6e
  | 1 => 0x7f777f07cf9f9f83e7cfe0e38f8c0f3cf95093
  | 2 => 0x9f879ff80fe01ffc07f07f03f00ff03f06631c
  | 3 => 0x1ff81ffff0001ffff8007ffc000fffc00783e0
  | 5 => 0xe0001fffffffe00000007ffffff0000007fc00
  | _ => 0
def q5Neg : Nat → Bits
  | 0 => 0x1000011020084042040000414008410080426
  | 1 => 0x0
  | 2 => 0x28382920a40929204c02a902a125202a126118
  | 3 => 0xd003d24201525242009552a8024a4a802582c0
  | 5 => 0x1addfc84a958036a9529fcd34b60628a47f800
  | _ => 0
def q5Atlas : Atlas := ⟨5,rawDecor 47 q5Pos q5Neg, 0xfeeefeeefeecfeecfeeefeeefeecfeecfeeefeeefeecfeecfeeefeeefeecfeecfeeefeeefeecfeecfeeefeeefeecfeecfeeefeeefeecfeecfeeefeeefeecfeec, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q7K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q7K4 : Nat → Nat
  | 0 => 0x11000241006bf40df30bd43bd40bf43ef20bc41be41dd30ed20f510f710bf42bd42
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x10000000784811096a9083c9304836280884b54b439ca80831d53d0ba260884754c41
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q7K5 (i*5) 5
  | 4 => packedAt q7K4 (i*16) 16
  | 3 => packedAt q7K3 (i*27) 27
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q7K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q7K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/10+packedAt q7K3 (243+(h % 10)*4) 4) % 9)
  | _ => 0
def q7Pos : Nat → Bits
  | 0 => 0xfdeef8773e7cfc733e7f988e3c718cf3f8a427
  | 1 => 0x7e777f87cf9f1f83c78e60f3cf8e0f3c8158da
  | 2 => 0x9f879ff80fe01ffc07f07f03f00ff03f06631c
  | 3 => 0x1ff81ffff0001ffff8007ffc000fffc00783e0
  | 4 => 0xe0001fffffffe00000007ffffff0000007fc00
  | _ => 0
def q7Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x8080008102002404081000104402041008084a
  | 2 => 0x28382910a40949205402a9029124a02a126114
  | 3 => 0x5003d2220152924200a552a402494a802582a0
  | 4 => 0x1b5dfc44a958036aa549fccb2b60628a47f400
  | _ => 0
def q7Atlas : Atlas := ⟨5,rawDecor 31 q7Pos q7Neg, 0xfeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeea, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x13b18ed32f261e8c3a98ee32
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x314c931d1314c324c930
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q8K4 (i*4) 4
  | 3 => packedAt q8K3 (i*15) 15
  | 2 => packedAt q8K2 (i*26) 26
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q8K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q8K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q8K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffbe93b368ec8f
  | 2 => 0xffffffffffffffffffffffffffdf1cdc70f533
  | 4 => 0xefe0ef80fa3c
  | 5 => 0xffff0fff03c0
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff422441212085
  | 2 => 0x244124424112
  | 4 => 0x180a1a048228
  | 5 => 0x0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 54 q8Pos q8Neg, 0xfffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0xc000102e195e30b86178cae98df31
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x3089a408ca31093198404c6390a30
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q9K4 (i*4) 4
  | 3 => packedAt q9K3 (i*15) 15
  | 2 => packedAt q9K2 (i*26) 26
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q9K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q9K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q9K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q9Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 2 => 0xffffffffffffffffffffffeffe7fffe3fffc7f
  | 3 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa21c2243049261b1
  | 2 => 0x1021040421248446
  | 3 => 0x9446819484a2a98
  | 5 => 0x7894eae920ccf60
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 46 q9Pos q9Neg, 0xfcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q10K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q10K3 (i*4) 4
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q10K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q10Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def q10Atlas : Atlas := ⟨3,rawDecor 30 q10Pos q10Neg, 0xfcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x108000002f98dd32ba637ccaf185c30
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x95410c25507328d420c2350b31
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q11K4 (i*4) 4
  | 3 => packedAt q11K3 (i*15) 15
  | 2 => packedAt q11K2 (i*26) 26
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q11K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/16+packedAt q11K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q11K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q11Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 30 q11Pos q11Neg, 0xfcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x9000003c905f32ba65d487b10fa20
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x1103848520c53248724c920
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q12R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q12K4 (i*4) 4
  | 3 => packedAt q12K3 (i*15) 15
  | 2 => packedAt q12K2 (i*26) 26
  | _ => 0
def q12I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q12K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/16+packedAt q12K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q12K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q12Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffbe967377446b
  | 2 => 0xffffffffffffffffffffffffffdf1b9c7b8593
  | 3 => 0xffe3ef83fa1c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff422881110829
  | 2 => 0x244424221092
  | 3 => 0x0
  | 4 => 0x18015a402340
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 30 q12Pos q12Neg, 0xfffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x64003b10fa20be65d486e997920
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x1000314c921e12148324c920
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q13K4 (i*4) 4
  | 3 => packedAt q13K3 (i*15) 15
  | 2 => packedAt q13K2 (i*26) 26
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q13K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q13K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q13K2 (78+(h % 15)*2) 2) % 3)
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbe967377446b
  | 3 => 0xffffffffffffffffffffffffffdf1b9c7b8593
  | 4 => 0xffe3ef83fa1c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff422881110829
  | 3 => 0x244424221092
  | 4 => 0x0
  | 5 => 0x18015a402340
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 57 q13Pos q13Neg, 0xffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q14K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q14R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q14K3 (i*4) 4
  | _ => 0
def q14I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q14K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xdbf19f3f1c3f8d9c
  | 3 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 2 => 0x24ac285909932594
  | 3 => 0x1101502242244a0a
  | 5 => 0xe091ab493064f40
  | _ => 0
def q14Atlas : Atlas := ⟨3,rawDecor 45 q14Pos q14Neg, 0xfaaafaaafa00fa00faaafaaafa00fa00faaafaaafa00fa00faaafaaafa00fa00faaafaaafa00fa00faaafaaafa00fa00faaafaaafa00fa00faaafaaafa00fa00, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0x6500002f995d31b86174caf185f31
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x4048d420c25504308d42cc6550732
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q15R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q15K4 (i*4) 4
  | 3 => packedAt q15K3 (i*15) 15
  | 2 => packedAt q15K2 (i*26) 26
  | _ => 0
def q15I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q15K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q15K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q15K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 45 q15Pos q15Neg, 0xfaaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x6004003690dd31f421e443790df31
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x1314c521d131443848510
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q16K4 (i*4) 4
  | 3 => packedAt q16K3 (i*15) 15
  | 2 => packedAt q16K2 (i*26) 26
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q16K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q16K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q16K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 5 => 0x18016a2012c0
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 45 q16Pos q16Neg, 0xfffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x4162f18dc31ba657ccaf185c30
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x96418c26101329a408c6510532
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q17R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q17K4 (i*4) 4
  | 3 => packedAt q17K3 (i*15) 15
  | 2 => packedAt q17K2 (i*26) 26
  | _ => 0
def q17I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q17K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q17K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q17K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 2 => 0x6efe3fcfe3ff0cfc
  | 3 => 0xfffffffffffffffffffffff7ffcffffc7fff1f
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c824304926171
  | 2 => 0x11258415212624b4
  | 3 => 0x840280848488a0a
  | 4 => 0x7892eae920ccfc0
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 29 q17Pos q17Neg, 0xfaa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00faa0fa00, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x202000fb887431ee43d087a887731
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x9443442590f21a442442990b31
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q18R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q18K4 (i*4) 4
  | 3 => packedAt q18K3 (i*15) 15
  | 2 => packedAt q18K2 (i*26) 26
  | _ => 0
def q18I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q18K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q18K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q18K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0x6afc39cfe3870ecc
  | 3 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 5 => 0x7cfffe0ffff80ff0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018800104912055
  | 1 => 0x152b9297213266cc
  | 3 => 0xc41350a4844cb0a
  | 5 => 0x38221ac92608da0
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 43 q18Pos q18Neg, 0xeeaaeeaaaa00aa00eeaaeeaaaa00aa00eeaaeeaaaa00aa00eeaaeeaaaa00aa00eeaaeeaaaa00aa00eeaaeeaaaa00aa00eeaaeeaaaa00aa00eeaaeeaaaa00aa00, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x60000800000803d087b30f041e443c187b20
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0xc000aa42cc2610d10a842442690f20
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q19K4 (i*4) 4
  | 3 => packedAt q19K3 (i*15) 15
  | 2 => packedAt q19K2 (i*26) 26
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q19K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/23+packedAt q19K3 (90+(h % 23)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q19K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0x5af0f9cf1f8707cc
  | 1 => 0xffffffffffffffffffffffefff3fffe3fff8ff
  | 2 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0x251e929704b163cc
  | 1 => 0xffffffffffffffffffffff9022800121122055
  | 2 => 0xc44350a4844cd0a
  | 4 => 0x38821ac92608ea0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 23 q19Pos q19Neg, 0xececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q20K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20K3 : Nat → Nat
  | 0 => 0xc100002e986d20ea21bc82f987710
  | _ => 0
def q20K2 : Nat → Nat
  | 0 => 0x2007848110c93048344c110
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q20R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q20K4 (i*4) 4
  | 3 => packedAt q20K3 (i*15) 15
  | 2 => packedAt q20K2 (i*26) 26
  | _ => 0
def q20I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q20K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q20K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q20K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q20Atlas : Atlas := ⟨4,rawDecor 15 q20Pos q20Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x40000b00000000007690fa10be63e442e98ef21
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x344c510e12144314c521
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q21R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q21K4 (i*4) 4
  | 3 => packedAt q21K3 (i*15) 15
  | 2 => packedAt q21K2 (i*26) 26
  | _ => 0
def q21I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q21K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/23+packedAt q21K3 (90+(h % 23)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q21K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 1 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0x424880910426
  | 1 => 0x0
  | 2 => 0x241415020918
  | 3 => 0x18016a2012c0
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 15 q21Pos q21Neg, 0xfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeec, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x420000442400820020003c000204f5460000000000810000000010000442801fc20007fcc801fd41007f88001fd52007fc4001fe30007f8c401fd42007f44001fd31007f94c01fe41007f48001fd21007f55001fe43007fcc001fe32007f4c801fe10007f0c801fd30007fc8401fd51007f94401fe21007f50001fc10007f08401fc31007f94801fe50007f54001fd53007f90001fc30007f90801ff20007fcc401fd43
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xca000ff50951007fc6398002fe60904017f30ca600ff98b10005f8c6a1003fd31cc001fea1a6400df19530005fac528003fe6308401fea966000ff90e52007fa8698003f72188415ffa144200ffd8131007fcc528803fd5350801dea1a8400bfd9321007fec6a0803fd54440017e302a807ffd4a30006fccb98833ff420c4017eb2c6200ff4c520087fea499003fd43cc8017fb1aa000ff55132007be6218803fd608c41bfe32a6200ff48530007f8c4aa003ee5248001fe990600cff10831007fcc608002ff6355001feb102000ff8ca51005facb90803ff654c4017e31a2000fd94710005fcc520002fc6254401ff1946204ff10520004facb90003fd3104001fea1c6000ff90920007fe6490803ff6050401fe3026400ff0ca20007fe42a8002fd644c401fe1948000fd8c710005fec0a9803fd528c8017fb0a8400ff548210057ac818002ff6454c017f3084003ffd4820005fac718003fd43440017eb2e6000fd4c71000ffea908003ff30040017eb286000ff08730087fcca99002fd654c001ff28a4000bf59010087f8a499002fe630c801fea184000ff54920005f8c2a8003fd4288001ff1966000f794d30047fcc99802ffc50c8401ff18a4000ff98a53005fac129802fc63548017f3066200ffd8d52007fa6490802fe628c40ffe294600dff14531005fac121003fd6308001fea1aa400f78c531007fa638803ffc434c801ff29a8200ef55140005fac518002fd6290001ee9806000bf59540005f8c6a8003fd218c0017fb0aa600bf18552005fac890003fd52c4001fea086000ff88620005fac308002ff60548017eb266400bf58e32005f8c4a0002fe63908017f3006000ff54e21005f8c4aa04bfc41cc8017fb12a000bf59710007bcc610803fe538c801fab08600fffd0d32007fc6408002fd6548401ff21a640effd0231007fa8728003fc31840017eb006400ffd8532007faa4990037e650c8017fb246000bfd8132007fac218002fe60880017fb1c4000bf18931007ee2008003bd4350001fe9926000bf58321007fe6528003fd61cc0017f3006408ffd0f30007fac790802ff6488401ffb2a4200ff58532007fe6499003ed42c8401fe194a200bf98620007fa4328003fd538c401feb14a6009fd9530007fa64a0803ef324c801fe9002000ff08520007fa6010003ff21500017f31a4000bf58221005facb98803bd64cc401ff1924000fb4cb2008ff8a319003fe538c401fea948200fdcc631005fecb90003fe32c40017f314a600ffcc820005f8c710802ff65880017fb184200fdcc53104ffea8908037f654c001df20c8000ff94731007de401001bfc404c01dfe2046200bf58d10005fcc720003fd5150001fea9a6200ff90730007f8c4a1803fd53500017eb2a8600bf9883106ffea098802fe6088401fe9922012ff10332
  | 1 => 0x3fe404c001fe30a6000ff8c550005fec690803ff6348401fe98aa000bf98e50007fa6590802ff624c001fea928400ffc8630007eaa288003ff60484017fb1c4200ffcca20005facb90003ff21940017fb184001ffd4a10087fea299002fd60cc8017eb142000bf58b10005fec0a1802ff635080dffa126000ff98c20087f8a69904bff42cc801fe1902000bf98e21005fac721003dd310c4017f304620cffd0c31007de4110002fc615080fffa8c6000bf58e20007fc8610003fd54c80017eb2c6400bf58a41007fac119037fc504c4017e3162000bfd8121007fa64a8803fd534c801fea9a2009ffd4d2101ff8a610003fd3290001fea1c2012ff10b32006fca328003fd6290001fea944200ff4ca20007fc4088003ed32480017eb204210ff19532007fa62a001bfc644c001ff2022000bfd9640005f4c010803fe5248001ff2962000ffcc650005fec6a0803fd6008401feb2a6400bfd9630005fcc728803fe21cc023ff32c6400ff50f20005fec2a0047fc508c801f69004000ff94a41007fc64a0003fd210c0017fb26620fffd0932005fec8988037d5294001ef9966200ff50920005fcc52803ffc424c801ff192a000bf59310007f842a8002ff6354401fb1084200bf59251007fcc299003fe5350c17ffaa64200bfd9610007fc8728002fc63484017eb148600ff98620005fec4a0002ff654c011ffa0e6000ff54a42005fec6a9023fe54cc001fea186000bfd8141005f8c498002fe6004001bf29aa600f754d30007f8c4980037d5454401beaa2a610ffd4132005facb08003fd5350401ffb0aa400bfd9110057fe8710803fe53484017f3046400fe4c030007fc4290003fd4188001fe984200affd02210077ac818003fd5448401fea92800fff19132005fcc598002ff648c801ff31e4200bf98820005fec8908037d65c80017f3004200ff58c21047f88398002ff6348001fe30aa409ffd49210077c80a0002fd65884017eb084000be9803202ffea910002fc63c8401ff2166000ff18131005facb21803ff32840017eb144200fe8c030005fac720003ee320c81dffa1c6200ff58321007ec2088002ff640c801ff29a6400ff98321007fec6aa002fd6090401fe1948200bf18950005f8c290002fe608c001fe31aa400bf98810007fcc720002fe6190001fe18e4200ff94531005faca08043ff534c80fffa9c6000ff98e20007fec290003fe314c4017fb204000ff55130007fa6590003fd528c4017f3148600ff98242005f8c6a8813ff41480017eb1ca200bf181320077aa8a1002fd63c8001feb146200ff4ca10007fca398002fd6194007ffa984000bfd9320027fca890003fc31880017f30c8400ff55332005fecb90803bc6444001fea926200bf58c20005fec890003fe41540017f31e2002ff95310005fec4080037e52548017f3
  | 2 => 0x32005fac510007fc53840017fb122000bf58d20005fac690802ff6254c017f3082000fd44010005f8c790002fd648c4017fb284000ff8c932005fec908002fc6155001fc90220009fd9510067fca818803ff30080016eb184200bfd954102ffea710002fd654c401fd8822000bfd9730004facb98837ff544c401fd1824000ff086300077ec890803fd54c84017f31c2000bf98242047f88198002fd640c4017fb2c6400bf98a30005fac398003fe40c8001fc9004000ff18121005fac928002bf6444001fe9902000ff44010005fec0a8802fd6188001df2148200fb98830007fa6410802fe6094c01fea928200df55152007fe4110003fd53c80015eb204206ffd0d30007be6498802fd6550815ff2a4420bffd4b21007fc6518002fc6048401ff9086000afd9121005fec2aa003fd43c8401ff2928000ff98a43007fac720043fc514c801fe9924000ff08310007fa8398003fd43cc401ff10aa000ff98730005fac32184bff43cc801fb90a4200ff58132005fac418002fd6590801ff20ca000fd8c431004faca10802fc6150001ff30e6400df99430005fcc399003fd6294401bf282a000ffd8143005f8c608002ff6304001ee9926200fd4c431007fa6588013fc4048001773106007ff14630007f8c6908037e65c80017fb266000ff90530005f8c408003ed2108401bfb2a2005ffd4a20007fa4010002ff64540017e312a600bf58251007fc8690802fc63480017eb222003ff14420005fac329002ff65500017eb1c2000ff08650007fa86a884bfe64cc801fea9a8600bf58b31007ba8798803fd310c401ff9948200ff50e2004ff8a690803bf64440017f3184000ff54831007fa8598802fe630c423ffaa46400bfd915107ffe8099003f93088001ef994640fff15132017f88188002fe6094401fea1a4200f7cc230005fcc410803fd65c84017fb162000fd4c62102ff8a510003fd53484017e302a400df19510005fac998003fd62cc001ff996420eff9523100ffea708003fe528c401dea148006ff10930005fec898003fd2188001fe3028200ff58c10007f2c010802fd64cc401fea0a4000ff4c220007fa6520802fd64c8001ffb226400ff48640007fe4298002fc63c4001feb106200fb58830005fac929802ff624c401fea126200ff94b30007bc6499003fc328c4017f30c6400ff90630007fec898002ff63440017eb2a8200ffcca40005dac418002ff6150c017eb246400bf98020005f8c2a9803fe4108001fb18c4200fbcca32005fcc390003fa20440017f3166200ff54832007fc84a8003fd42cc001fea9a6000bfd9410007faa2980037d650c813ffa824200f74cb31005fec999002fc614c01fff3226400bf59532007fc6418803fa4044001fd1844000ff98a40007f44010003ff3254401ffb126000bf59630007fa659880
  | 3 => 0xf1886000ffd8950005fac31904bff41cc801fd8842000fe50110007fcc329843fc504c8017f31a2000ff4c43008ffea71901bfe544c01dfe21c6200bf18a10005fecb21003fd32884017eb284200fec8120005fac728003fd6394417ff32e4206ffd0530007fca610803ff62550017fb2e2000bf5912102ffea310003ef21084017eb0e6411ffd4a32097fca99901bfc414c001bf28aa200ff50d31007be6419002fe6390401bea9ca200ff18143005fcc218003ff3188001ff10c6000ff50a50007fe6519003ff10840017e3026200fb50921007ee2108003fe5148401ff21e420aff10221007fa82a8003fd61cc801ff9002000ff48730007ba6419003fe62cc001ff3046400ef90942007fcc010802fc614c801ff18a4200df54951005fcc610803fd4254001fea9e4200ffc8640007fa41080037d5354801ff90c4000ef59320007fa8798002fd644c81fffa0a6400ff5492100ff8a308003be64c8001fd9826000af59331007fcc418002fd6244001ff21aa200ff55232005fec790017fc53880017f3182000bf58810007fc6418003fe424c001ff2906200fd58432005f8c0a1803fe4388001fe1086000bf98431007fcc408003fe63840017fb028400bf58c21005feca18803fd6194c017f314a200bf58e31007dc42908027d650c81ffe20a6400ff94530007fc4328003fe42cc801fe9928000bf98031005f8c710002fe630c0017fb204200bfd9731005fac819003ee2048001ff994a200ff55120005fecaa1803fe3294001fea1c6400ef551430077c82a0803fd6090801fe31a8200ff4c530007eca288003fb308c001fe30a4000fd4c510005fac018803fe628c4017fb12a800bf58642005fac198803ff328c401fea926000bfd8131005fec918802ff6548001deb206400fb4c832007fa6528803ff324c401ef29e6000ff55331005fac918002fd6488401fe9082000ff90932007fec4a1827fc5148401ffb0aa000bf58720007f8c299003fd52cc801feb226400f7cc030007ecc219003fb2088001ff31c8400ff94510005fac11882fff53c84017fb2a6200f790f31007fc8518003fd4348001ff18ca000fe4c120007fec890003dd434c4017f3106000ff58e20005fcc419003ed52c80017f3042000bf98621007fc6210003fe4294001fe9946200ff8c5100057ac990003fe6394801fd1042000fe44010007fa6498802fc6350001feb1c2000ff48520007fc6318002f9600c8017f30c6000ff4cb30005bcc610803fa4084001ff29c8200ff54910005fac329803fd318c001fe90e2000ff4c010005fac129002fe62840017eb286200ff8c930007f84298003ff32040017fb2e6400bf18543007dc8490803fe53c8401ff2086000bfd8943007fac729003fd620c0017e3028400bf18141007fac521803ff3208401ff21c2000bfd91
  | 4 => 0x3ff21cc0017fb206000ff90d52005f8c4a1802fc6384001fea1ca400ff58e42007fac998003fd3188001ff18c4000bf98652005fac528803ef21884017eb166000bd58432007fa6528003fd420c0017fb2a6400ff4c640005fcc190802fd620c4017eb1e4200fe50210005fac78802fff50c84017f30c6200bfd8550005faca19002fd6304001fea8e6000bfd9621006faa6a8003fe53884015eb206400df55250007bc6098003fe41480017fb1c2000bf58432007fa8318003fc6254001ff9882000bf58243077f8851881fff548c01dffa146200f790d31087fea899002f960084017fb02a800ffcc220005fac318003fd64cc807ffaa04000bf59641005f8c0a9803f52108401ff2066000ff4c650007ecc218003ff21040017eb284000bf59510005ecc2190027d650c0017fb0a6400bfd9430005f8c6aa002fe60cc8017eb046400ff50d50007f8c2a8003fe524c001ff21c6409ff14121005facb20047fc538c8017e3184000ff8843005ff8a790803fc2188011ffa166000f7cc631007dca590003be6408401fea124200ef99030005fcc519003fd5308411fe2166000bf59030007faa719002fe610c801fcb006400df94e50007fcc118803fd4194001ff31ca20bff14721007fca599003fe524c801fe90aa000bf98910005f8c488002fd6190001de3224200ff8ca20007fe4290003f551c4001f71924000bf59220007fe4388002fe6094801fe9906200ff0c420005fac929003fe3290001ffb2a6400bfd8f100077aa920802ff6508401fe9906400bf98e52005fac898002fc60544017eb004200bfd8941007f4c019003fe4048001fea8a4004ff19120007fe6320003fd424c001feaa66000bf98f20007fc6298002ff64c4001f72164209ff19521006facb98803fd534801bffa9a6200ff88120007f86328003fa60084017eb1c8200ff88310007faa788017fc5188001ff18c2000bf59020057f88710802ff658c4017eb2c4000bfd9542007fcc218003be640c801ff28e4000ff50b32067f88018802fe6348401f71964000bf58e520077a8720803fe41c8001df3266200fe84010005fcc210802ff614c001ff10a6011ffd4232007f86528013ff4248001feb2c6400ef90d43007fc8418013fc4248001eea9e6000bfd8520007ec6290802ff62840017e31a8200bfd9643007fc639000bff42c4001ff29c8400bd98430007fac310003fd32540017eb2a4000fd8c510005feca88003fd52c80017fb2c8200bfd9010017f88588003ff614c001ff9842000bfd8d40007fa8499003fe620c4017fb28640dffd4931007f24108003fd42440017f3162000bf59732005fcc520802fc6308401feb162000ffcca21007fa8518003fd21500017f30c860fff95132007faa898802ff6154801ff20c4000ff54e41007fca698803f53148401f
  | 5 => 0x484400e000058140045b02c8080500380a80101e020060ab00000409805086554010280060001300d0040cc00807012000030cc00000c0180424c02c998da000004020000020001d00800c0740000024a1540400100601402000058000041b4022008028045900000380604c04c018f103a0080300b05c000240f801e87881803000a100b0c201a0081980a0140000f80839e0340000700c0200600400614c030010022f03e80b00807c050441be0040000000c0400e0040500ec098070020003f8060040480480e08a0303d8160060101325710a01802007016024160011400ec0281b01601c2700300a0180000202e0380f02d11a0044e00400e02ca780034a0040c82f00400c2380800001c020051d80080182d08806c23117042e90008081e80000280308a010210030000e4000060120000c9b600e0040882d000000000010000ac0004d00009c040030200841180a008054018000020141d0000240040000317a03c02000092025080240065840000203c018040010e40900600003400c0980700018c010b100a7300c0060000541a8050000d0ba8000ce09c0500000000c090230040000891b000000302020081640004e0000f4000330ce0000006103a01000000138004010060000b41b8010000580000500600c000340160000100109c024498500180140c00300003c080000126fc169420ac0140080100803c008000000040400000201c0780000001801002172ad80086b00400022049374060038006700000080a00e00c0c80b0080080400200c0580400204a02411001024000060070028842b81305400bfd8951007fca390803bd64084017eb1c4200ffcc631007bac610803fe31c84017eb242000bf98730007fa6518002fe6090c01fea142000ff4c820005eac218003fc6355001feaa06400ff50530007fc8510002fd628c405ffa1e2000ff50c32005fac990803fd5390801ff9928200bfd8f21007faa598803bd425041bfe29a6200bfd9031007fec099002fc62504017fb22a400bf98e20006faca18002ff6548401ff29a8400ff54b21006faca10802fe63c8401ff1948200ff98132027fe8690002fd610c001bf3284200ff90d3107ff88099002ff6488001fe18a4200bf58a53007daa490
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xd7394521005fd748c420006fd634c620005ff7259330137ec5050b21006fd768c430005fd7390830005ff7258e40006fd7694c21004ff7258d20004fd7218d40006fd6354c21005fd75cc9210afec424c920005bd7408630006fc4158b30006fc4298f10005ff7350a50004fd76988100867e654cb31004bf7458652006fd6254b10004fc76551200077d6554f2104f7c5348650006fe764ca51005f9700c620006fd3218532006f5618c420004ff725923108f7f5155232005fd7198830006fe6350520005ff7354b10004fc7655130097bc41593320057c7154a50004bd7498a50007dd63cca41005ff764ca400067f6548530005fd7290530007f631d8121005fa70c8530004fe76cc931005fd73d8954004ff7655321007bd3290640004f67118d20007ee42c8630006ff6250930005ef7250e32006ff6354d21006ff638c810005ff7388430006fd648ca310067d6590720046fe6350830005fd7318954006fd62582310047d7518542005fe70cc821005f5718ca31006fd65cc821006fe7258e40005fc72545300a7ef428852007fbf4055132007ed2108530004fc765513106f7f524c650006fd61cc220005fe70d8532006ff654c5400077e6548430006fe5398a31037bf4150930004f97018542005fe7190130004fd73d90210047d7598d21006fd644ca500063e6599320005ff704ca41006ee624c83007fbc6459132006fd634ca410047d7598e21006fd6558132004fe768c520006be6498c21006fd6288730005fe70ccb21005ff73549200067d5358a51007ed52cc821006ff644c910007bd4390430007f56148730005fc7155232005ff76c8730007dd54cc931005ff7054a4114fdf504c931005fd7694e32006fd654c620007be6488430005fd7394530006df764c832006fc764c650006f54358430005fe76c85300077d7508630007fa218c030006ff6548630007de538c932007be4290530005fd7494720007bd7408430005f5710ca51007dd538c530005ff74549320067d6558c2108f7f5354a32007dc7354932045bc7448730007dc6354d21004fe76cc941005ff7250d51007f53148650005f970cca20004fd764ca51007ee4248730007f53254710005fd7390420005ff7454530004bf7458d10004fd73d8940005f8704c920007ef6250930007ed714c920004fd73d9120006fd3218540006fe6558532004ff764ca10004fd7218f10005ff7488530007b7648c5210063f65d911005eff65c8550006fc7648550007be3290640006fc72d8d540067d658c720004ff7650620007bf7448730004ff7358650006ff71d8943007dd324c730005fd7488530005ff724c530006ff7650c20005f5710ca20005fd744c63008f7f53d8d52004fd764ca10006fe61cc220004fd7398810007cd324c52004f7f5394d21006e56298430
  | 1 => 0xc30007f8501813205f7f53c8550005ff7348730005f5710ca31006ff73d89540077c41d95300077e5388650005fd7290630005fd7194b30005fd7190e50007bd5450d30007fa324c2200063f6519110005fd7488630007be4290630005fc7054832005fe7318121006fc61d8132005ff7150950007ee624c8100077e5354d21005fd718cb30004ff7358a41006fc4258f10097bc41cca40005fd7298430007bd54cca410057c7155153005ed76cca32005ff748c730004f970d8c21005fe7290e50006fd4258332005fd7118950005fd7394930006fc73d8954005ff7488630004fd73189510077d53c855011fef525092107ebe644c830007dd5308730004fd7298640005fd758ca31006ff5158e20006fd7058f21007bc7448430007dd5350d31005fd744c920007dd5348530005fe7190320005f5710ca50005ff7650b30006ff3218151006ff50d8d21007f97090520006ff74d8930006ae6250a400077d52cc650007ed624c810007ee628ca50005fc7059132006de6350c200063d6559331005ff724c63005f7f5354b21084fd72d9532005f9700ca40076be648c720006dc638c520005ff7155130006fd6558532004fd73d8a10006ed62884300077d5454a210867e654c821006fc7648630004dc7358910006ff7258e1006e7c654c530006f96348210005ff748c83006f5f5358653006fd6290a50006dd635802108f7f51d8d52006fe7458a310057d7294e50006ff5258e10006ff6318954005dd7290d31006ff7458a53007de314c630007ec714cb200057f725515105f5f5394f21004fd73d9210005fd7394720004fb764c030004fd7218d51006f66148620007dd5390530007ee714c832006bd6448430007f74118532006ad64988300077d5454d32006fc6218530005ff764c620006ff634c810006fc63085200077f6588530007cd524c832006ba6498032006fb7658021007bc53191210077e514c650005fd7418530006fd644ca31006ff75d8943006fe531894107dbc7458532007ef2108730006ec624c930005fd7094721006ff644c931005fd7550b32005ff73c8530007f5538c521004fe7688110005bf7448620006fd65485300067d6598830006fe614c020007be74085300047d75d9320005fd73d9521005fd73485500877f5454932005ff7558232006ff32982510077d5354a32007bd5450a20005ff70549210077d5308550006fd6558f21005fe7090b320877f52d9532006ff654c921097bf425533205f7f535532107cfd7690e32006fd6250a30004f57118e20007ed42c8550006fe635065006f7c50d953107ebf4358a43006fc3298650005ff744ca30005bf7355142006fb7458032005fc7355321004fe76cc921007ee5350921005fc7155132005fd7198a530877c6559532006fc5058d210077d5454e32005f
  | 2 => 0x5ff7250d30004fc7648530006fc7655132005fe7090f21005fd75d8131006fd768cb30006fc764c910005fc7354a2102e7f53d8950006fc40d89300067c65d8930007ed6248430004fd7694e42004bd7498d21006fe6398242004fd72d9230006ff658c932006fc6318552004ff7358a51006fd6290650006fe6390920006fe6058321006fd3218530006ff628c950007ef2188430005fd74cca20007d5324c710005fd7118930006fd634ca50006ff624c950006d532584320067f6590530007de314c530006fd64cca20006fd648cb300867f53d9532007f5618c620005ff744c430006fe5458e21004ff7655331004ff73587200047d7518c21004ee72d9430006f9325802115fdf5050d310047d7699432007f63148730007f5728c521006f661c8640006fe6258830006fc5318931006fc5158e20007ed320ca41006fd658862006eff654c550006f552984320047d7518f20004dd73d9421006fd3298231096bc64cc921006fd6250630007be740863004f7f5254d21007dc21cc030006f5618c620006ff638c620006796558032046ff7650c30007dd53c873004f7f5448650007ed4248620005fd740c620005ff7258653005ff7258c10007fa21cc130006ff70d8943007f6618c620007f9324c220007bf5319121005ef7250d32007fb7358021005fd7308730006fd6294b30007de5350930006ff64cc810005fd70d8d41005fd760ca20007ef324cb21007bc5019121004ff7650730007f8724c220005bf7448650006fb764c220006fe7158830007bd5450f20004fd768c620005ff735511007fbc6450d32005fe70d8d210065e6598c21006fc5158c20006fe54d8d20006ff764cb21007f56118532006f6614c6500077d5454c21037bc4250930006fd628c650007f66188730006fc63c8520006ef764c832006fd61cc020006fd624cb10005f9708c620007d4714c931006ff6250530005ff7250d10007ec3254920006fd634c410177ee64cc932005f87055120005fc704ca31006fe6198132005f87059532006fe5358642006fc63885500077d6588430005fd7288430007ef324c821006ff3298620006f96018132007ed2108630005f57194a31076bf42d8d41007f83290210046fe6350430006fd638ca50006fe5358a31007ee624ca50006fd640c810007ee7198830005ff7690b30007f9424c030005fc714c02008cff7654832005ff7350530004ff7655320004fd7318941005fc7050d31147dc544c931007f53188550005ff7348640004fc764c921007bd4290330004fa70d9421005fe7290330006fe6118132006796558021005ff7250f31005ff7448530006fc5058f21006fd65885200877c6554932006fe3298231005fd7398021004fd7398a10005fd73c8550006fc51d8d21006fe3218530027bc4155120005ff715
  | 3 => 0xf754cb20006ff764c8300067d6550f31006ff70d8d54006ff7358b10005ff725512106f5f5394d31006fd7158830007ed4248650006ff6308550004ff7648430006f87158032007ef6290930006ff7158a40004fd7218131006ff43d8930006ff7558831007f66148620006fc3298640006f56348421006fd6308520006ff6348620006ff4358a310077d5394521005fc704c921006ff6394940005fc724c430006fd6250b30004fd76cc620006fd6458132004fe768c51008f7f535963202e7c6588110004dd7318810005ff7054f21006fd6308650007ec714c8320067d654c83006f7f54549310047d75d9030006fe76c8730006ff658c530005fd7494e32047bf42d8143005ff7448630006fe3298241006fc764ca40004f870595430067a6598032024fd7690320007dc218c130006fd638c610085ff7559532007f8214c220007ef744c920005f8704c930004f571d90320047d7518c1006f7f5355131006fd6354b21004fc764c520005fe7290430006ff65d8121004fd72d9531006bc64d8121005fd748c430007f9414c0300067e6598021004fd7218153006fe76c86500047d7518d420067d53d8950006ff6294530006f7764c431005fe7194930006fd6354e42006dc7058c21007f72148530007fa328c220005fb7250110005fe71908300066e6558830005fd728c620007df744cb310d7f841cc130007dd324c5400067f6518530005ff7459532004fd760ca40006fd644cb30047be64907300073d5490650006be6458c21006fd7358810005ff75ccb210077d5354b21005ff7054c21006fd7058c21005ff7254730006bf6390541005ff75cc821005fd7318552006fd5458f21004ef7648020006fd6388620006ff65d8131005fd7408430005ff74c8730005fe728c650007ee528c520006fc63d8954167df434cb31007f63188520005fa7008530006ff64d8530006ff6458532047bf4250f30005ff724c220005fd7094c21006fd6498b30006fd72d8d21005ff7354910005fc7150d200063d6559032007de5350e32004f970d9032006ff5258a30005fe708c932007e55248421004fd73d8950005ff7355130005fd7390430004bd7418e10005fd72d85500077b754c2200067d54d8d51005ff73c86300067d658c830007de324ca50005ff73588100077f754ca50007fb6098132004fd7318142006fc4058a3118ebf42d8d54006ed43988300047d7518d40007bd4350b32005ff7055321005dd7308530005fc714c830004df7358910006fd640ca51006ff4298d20006fe6390a50007dd434c730007f52108530006ff7258e20005fd764ca51007bd5450e300077d5454f21007dd634ca51006fe76c8550005fd7294d41006f77558432006fd7358b10006ff6548730005fd7388550006ff7650e20007de7308430004fd7398242
  | 4 => 0xc9200dfdf4154d30007dd634c810006f96388020005fd728c650006fe764c941006ff62cc81005f7e75c8650005ff7250650007de5290d31006fe6358a51006ff4358831006f66148430006ba6458021006fc764c550005dd7308630005ff754c821006fc764c950006fd7158e40006ff628c530006fd74d8d52007fa21cc230006e66298430006ff65485300afee544c920006f6768c521006ff7158e40005fa7094520007bd5450920005fc7655132005bf7448520004ed72d9430006ff65d8132006bd5458e41004f57118c20005fd768c6200067d6508430007f943881100077f6550930005df7348630006fc6198132007f7328c521006fd65cca20006fd628c83002cfe76949200057d7394952005fe7398242007dd21cc230007ee42c8550007ee5390921006fd6290a30005ff73887300077d54cc650006fd70d8d21006fd63c8520005ff7255120007bf6459132004ff7650f20006fe71d8d52004ff7259330006fd54d8d20005fd70cc941006fd53d8543006fd63cc821005ff7250e30006ff5318931004df764c43113fec5090b21005ff7654f21005fc7250c30006ff4258a31007de21cc030005fd720c620006fe63c8640006fc64d8132004f8764c120004fd72d9431007dd7308430007df218c130006fe768c520005bf7355241006fd7158a53006ff7558b10005fd760ca31005ff7454d20167de544cb31005f973c8220006fd63588100069d6498c21004ed7218e10006fc7358810007fa7008430005fe7018532007f52108630007bd4390730006ff62c8550006f57298430006fd63c8650006ff65591320057d7518943007f73294710006fd3218520006ff42d893007eff644c9410047d7518c20005ff704c921005f573c8621005fd7494d320057d7508520007bd42cca40004fd76c8010006fd32982410067f65d8530006fd658c420006fe639065004cfd7694721005fd748c830006fe6458132007bc6454d21006ff4058e21007f62108430006ff74d8d21006ff6248540005fe708c721006fd53d8520004fd7690b30007bd7408730006fe63907200077d5354821007e932480200073d5450d52006fd658c720006fe6390520006ff63cc921005f970cc620007ec7198830007f9328c220006fe53d8532005ec724c620005fd7190330007de53505300067c6419530007bd4250430097bf40d8943005ff7355320005ff7354930007fb214c220005fd7094f210047d7598a30034fd7690330005fe7218530006ff6290930046fe639083002e7f5259620005fc72506500077d5454b3206f7f5354931006fd6248650004fd7298d20006ff41d8132006f53298432005bd7408550007ee5290520006f95358021005ff7350630006fc6388620006ff64cca31006ef7158830006ff6208550004fd7218141007bd6450b32007e
  | 5 => 0x7de5390930006fd6290630007bd4350a20005fe73d8141006fd7458e20006ff650c8100067d654cb31007b4648c5210057f735515205f7c5354f21007dd7398132004fe7618d21005fc76c8530007f562cc631007bc7448730005ff7254f21007f72148630007dd7098c21006fd43d8950005df7250d31006fc7654931006b96498021004fd73d855000676655843008efd72d8d52004fe760c521007dc7098c21005fd7494b30006bd6454821007fa6018132006fc5258a30006fe329865004f7f5048650005ff7558532005fd7294730005ff7350910005ff7550e32006fd4258331004bd7418e20006ff4258831006ff6350921006fc6350950005fc7058c21005fd74d8520007f5708c521006fd6350e50007cd434c832006fd6398321005fc7055121006ff6254540004ff7258e40005f77159132006fe5358632006de7058c210077d6554e32005ff7350b3104f7c5148650006ff75d8930004ff7258331046fe6390430005fd7290550006fd6548730005fd7294e31005fe7094932004fd7318152006f6614c640006ff6290530007fa424c030007de5250d31006ed628ca500063e6599032097bf4250f3207fbe54591320077f3294650005fe7394521007f9434c220005fe7690930037bf4190530006ff4258332004ff764ca40004fd76c84300077d5454d31006ff764ca41005ff748cb30006fd6250730006fd53d8540005fd7394a31007de328c430007de534c931006ff70d8954005fd72d8143004fc7650d52005fd744c93004f7f53d9521006df7058c21005ff7348540007fb744c2200047d75d9021007bf5019121005fe70d9531006fc76486500067d65c8430006ff7358a40034fd73d9130006ff7558a43006fc764c920005fd75d8132005fc7054a32006bc64d8d21004bf7458420006fd6354e41006fc50d8931006f5618c650004ec764c920006de634ca51004bd7699032006fc4058831005f97290210006ed6250830005fd7190a50005ff7254c21005fe7188530005fd7390b30047bc4150730006fd53d8530006fe4258332037bc4155130005fe70cca21007dd43cc931005ff724c550007bf6494d2104dfd7594d21004fd7398a41006fd5458b31006fd7358a51005ff7458132006bf65d9121004f671d9430006fe7058a43006bf6454910004fd73d9721006ff7058a31004fd72d9710006fe7558f21007fb764c220006fd65d9132007f8218c220006ff764c810006fd764ca40006ff6354920006fd634cb21006ff764c650007f72188430006b96458032006fc5358d21007de7098c21006ff658c620006fe634865007fbe64d9132006ff63c8550006fc6118132137ec5350b210063d6559030006fe6348520005ff754cb21007f56148430006fe5458f10006fa7398021005ff7354b20006fd64585320b7ee754
  | 6 => 0xe72d9210006fd7458a53006bf644c910006ff624c550007ed544c920006fd6398242006ff63cca21007dc6394d21006fd6248010006fd7690b30005fd744ca30007fa414c0300875f5358a53004ff7258e10005ff7308530004ff7359610047bc4190b30007f73294510006fc2198030005ff72545400077c6508530025be7408520006ed6250430004ff7650f21005fe708c531006fd6254a41147df434c931006ff62d8530006fd6350a20007f93290210006fb6388110006f93298032007ef2188730006fd62486300057d750ca31004fd76cc640004fd7698c20007bd43cca41007f77298430006fc6388520006ff658c520005bc7055142006fd6294730006f7618c530005ff764c810064ff7650f310067d6550c30005fd73c8410006fc71d8930005fc7150d30007ed528c9200bfee758c920006fd6358620007dd544cb310047d7518941007f9314c220007f53148530006fe7258c10007ed524c921036bf43d9130005ff7050d210063e6599021005ff7454b30006fc50d8f21006fd648c810006fd6258730006fd65cca41006fd5318931005fc7150830006fc764ca50006dd63cca51006fd6548640006fd7558a31005ff7350930006b664984300077d5388550005ff73c8550005ff7154b30005fd7348430006ff6548620157de74cc931007ed52cca21005fd72cc2200047d75d9032006fe6358c21006fd54d8931006fd624ca400067f654c9100dfdc4254d30006bd6458830006bd6458430006fc7058a31007f87050d30027bc4150d20006fd75d8d41005fd7398242004de7318810006fc7648430004ff764ca51005fd7294e41006fd7458830007ed548c920006fd65582320067f63549510067d6558021005f6710c5210067d54d8d52005ff7550d32006fd768c620005ff7350951006fd6398a40005f6768c521005fd7090d21004fd7698c210077f65505300e7df4294d30006fc5358f21005fd76cc620007f6614c650004fd73d9410006fe6348430006fb7648210006ff6248530007f9708c620005ff7558f210047d7518d20006fd5398a41004fd7298653006fc4058b30006fd6208430007ed754c920007fa3290210037be5450930007f5728c510006fc6350951006ed624ca50004bd7498d10005fd720c650004fd73d9641006ff65cca41006fe53d8941006ff4258031004f97018931007ed7198830006bf6418d21006ff7258e40006fc7058e420069d6458c21006fd3298650147dc404c931007f942cc130006fd6398620005fc7054932005fc7358321007dd754cb31007ee2148530007ed42485200065e6354e510077d5354931007be4250830006ff7648550005ff7150f300077d520ca50004fd7218553007bd5490620006fd6398810007fb218c220006ff65cc941006ff64d8520005fe7208530006fc42d8132
  | 7 => 0xf21007ee21486300067d654c4300047d7598f10006fd72d8d41007ed42c8430004ff7655332007bf7448650005fc7159330006fe6348410006dd76cca32005ff7255110006fe329873007ebe644c8320057d7508530006fd62cca51006ff5018931007bd6455132006ff4198d20006ff4258b30004fd768cb100077d5454e21006ff7358810005fd7218550006fc70d8943006fe7608630006fc7648730007fb5018132006ff71d8954006ff5458f21005fe7290730006df638c520007dd7058c21097bf4259332005bd740ca2017ebf43d8954005ff764ca510077c65c8530096ff64cc941004fd7318121004fd7398620005fd7590b32006fd644ca51007df324c640006fd3298730006ff52d8d21006ff648ca30006ff7358a51006fd6354b10005fc7150f20007ee6248430007de5390530177ec41cc932007f941cc13007ebe644cb3107dff7459132007bd64c8430007f47159132006fd611813207fbe5450d3208f7c508ca51005fd70cca41004f4764c510027be5490520006fd7458e10005fd748c73005e7f53597210ffdc4154f30005fc7054b21006de634c81007fbc404ca41006fd7158a43007f553c8621006fd7558b30005fe7190b30006ff4258231007e93248210005ff754c931006fd7458c20006ee624ca31006ff2198030007f7638c521006fe6298231006ee768c920006fe74d8930007f6538c521005ff7058f21006fd3218141005fc7054831004f57118f20007f87398021006ff6308520007f53188430006fd5318943006ff7158a53005fd7408730005fd7298653007dd74cc931004fd764c810007be4190330007bf6450d32004fd73d9621006fd6290b30007de63cca41006f54258430037bc4290530006fd634c650006fe6298730006ff764cb20006fd73d8954005fe71cc020005fd768ca40005fd73c8430007ed524c920007ee4248650007ef324ca21004ff7650c20006fc7058a430077f6554d21006fc6350550005ff7648730006fd62c8430005fd728c520005fe7398021004de7318b10007f8214c120005ff7255331004fe7694930007bd6408430036bf42d9130005ff7150830006fd644c810005fd7390730006fd648c830006fd5358b10006bd644c821004dd7318542005fd7390b32005ff7059721005fd71d9130005fc7158830004bf7459510005ff714ca50005fc7054821007dd63cca51004fd7694f21006fd7058e52005fc715492006f7f53d9531007f63188530006fc4118d20005fe7094831006fd7058a31005fd7294d21006fd644cb31004bf7458650004de73d9710005fc714cb30006fd76c8730007de7308730006ff6394d21004ff7654831005ff744c730004fd7398020006ff4358b30005ff7458532005fd7448530006fc764c810005f9700ca20137ef5350b21006fe6058021004e
  | 8 => 0x77f6554d3104e7f52d9521006fd7158e20006fe6398a51007fa214c220007de434c620006fe6358e42005fd7650b30006da6398021006fc62d8143005fc7059532006fc7648530006fe7608730007de324c930005fc7250f30007f63148620004ff76484100876f5294932007bd74cca41004fd7218554006ff5258e20005be7090942005df7354b32007ed5350b2104e7e6548430006fd654cb2110ff450c8521007ed2188120006fd634ca51007f63188630005f47150f21036bc4158e40004fd7298643005f4714c921006f5628c710005ff7454b32004f67118f20006ed624c810004fe764c910027bf4255120005fd7308620004ff7359310007f72148550006ff64d81320077d5354a2115fdf5250d31005fe7298730007dd7308730006ff6394521006ff644ca21007f73254710006ff62185300057d750ca41004fe768c521004fd7690e10004fd73d88100077c3255151006f96348020004bd7418951004fa70d9631004f67118c20005f9700ca310877f5255132005ff7054e21006ed6290830004f87648110006be6458021006fd624ca41006756598430005ff7308630007de5348530004ff7359121005fd73d8552006ee624ca10005ff7550931006ff5258c20006fd644c8300077f42d9530006ff644c951004ff7258231005ff7159330006de635482113fec5390b21006fe70d8d410066e6598830006fd6350620004fe7608530005fe7094d21005f87054d10005f87054b3007ebc644c910005dd7308550007fa7008730007f62108730005ac7250d42004fa70d9432006ed628ca31004fd7318554007f53148630004ff7358620006fe6308620006fd7694f21006ff6350910005ff748c620006fc7258c10007f9318c220005fd7388430007e8704c920005bf7448530007ef744cb2005f7f5454f21004fd7698c10005fd748cb30005fe72d8530004fd73185400047d7598910004fd7218d5405f7c5094f21005fc7150e30005ff72551300877c504ca51005fa709093007fbf434ca41007ed52085200077f6590930004f57118d20004fd72d9643006ff7258e5107fbe6455132005fd7448630006fd6390f21006fe7694f2104f7c5048550004fc764c941007de5308730006ff6548520007bd4250730056be6488430006fd4358830007f23188110005fe71d9120006ed628c810006fd70d8d52007fa708c930005fd7398a40005f9700ca51027bf4355120007f9214c030007f521085500047f7558d10005797094e50006fe7558e10006ff5358f21004ff7654b10006ff63c8520007ec7158830006fd628c730097bf42cca40005fc7354941006fd62cc650006e56258430007de5350d31097be74cca41005fd700c521007de634ca51004dd73d9710007df658c932007fb214c120005fd7294e42006fd3218121005ff755
  | 9 => 0xf7258e50007bd5450a30004ff7259310005fc7354a42004dd7318b10006fd6354f21037bc4150d30007de32581320d7fb42cc130004fd768c420006f94398032005ff7348650007bd5490520006ed628c430004df764c832005fc7250530005fe7094521007f970c85300047d75d8f20007f441d8532005ff744c830006fd53d8542005bf7448630006ef6208530044ff7650c30006fd6394c21005fe7198e20006ff6254530005ff7348620004fd769083007cfd73d9132006ff6350d51006ff6508430006fd630c721005fd718ca50006fd64cca31007ed3208520006ff72d8d21006fd71d8950006ff65cc6200077d540ca50006fc4298d20007bd4350920004bf7458221007fb218c120006fc53d8931006f47058432007fa708ca30006ed6298430005fe7294730007ee42c8430007fb724c220007ed744c920006fc4158d20006fd7608730006ff644ca300077f6590530005ff7608730047bf4350b30006fe7058a31006ef628c93004cfd72d9521004ef7259131004bd7418931006ff65cc921005fc7358021007ec3154920007ed4248530005fd708c521066bf42590310057d7294650006fd4358b31006ff7558e42007fa42cc130006ef745883004f7c5055121004f7764c4310cfee754cb20006fe6298653006fd65c8430004fe7608520006fd624873004f7c5054921007dd744cb31006ff7648430006fd650c810005f972cc130007bf3290640006fd6388650007bd5450c20005fe71d8930006fc31181211a67c50d8954007ef32d8532006fd624c430004bd7498a30006fc7458a31005fd710ca50007dd434c620005bd7408430006fe3298640007be6448430007ed5250b32004bd7418d500077d7508430005fc7054d21005fd744c430006ff6388550006fd63885200077d5454a31007f9218c030007bd5450e32007dd538ca31006ff6288550004fd760ca51006fd6354d21005fc7690520006fd7558b10006fe768c950006ff3218532005fd72d8d54006ff764c430007f941cc230004fb7648020004ff7359620005bd7418d52007f5618c650006ff41d8930005bd740ca50006fc6390950005fe7198132005ff7454f20006fd7158a4002d7c754c220007f97008530005f9700ca41007ed52c8520006fc75d8d21006fc6558532004fd73d9610007de53c8730006fd3298640007de218c130007be4150430006fd6298231005fe728c530006fd6394a410067f6550d10005fd7218530006fd71d8930006fd7558f21006f1619803207dfc7650d32007f46188520006fe63c8620097bf4055332007ee624ca40006fd6358242007f8218c120005ff7250d50006ff634c951006fd7694d21006ef624c930006ed624ca31007f72188730006fc7358a40006fd6394720006fd6508430006ed624ca10005fd70d8d21006fd6458732
  | 10 => 0x4e210047d75d8142007fa41cc130004ff7258c10005ff7355232006fd76c8530007f970c8630006ff654c810007f6768c52108e7f54d8d52006fc74588310afee744c920005fe7108530006fc6350920006fe75d8d21005fd7190930006fd6390720005ff7488430006fd6508630007de3250f310067d6550b31004fe7690950015bc7448710007ed42cc93207efd5458e32006b664584320065d654c030004ff7359541006fc7158e52006fd6348640007ed754cb200bfef548c920004fc764c550006fd638c420006e9624c0300067d5458a50004fd7218154005fd7598532006ed6248430006fd63c8710005fe728c630007de324ca30006ee624c810005fc7150b30006fd624c210004fd7318141007ed42c8730005fd7488430005ff7254e21006fc53d8f2105f7c5154f21004bd74d9432006fd624c640005ff7350a30006fc6390550005ff7550d31006fc7558e10007fa218c220004bd74d8f20005fd764ca40007bd5450d3207ebc6459132006fc7650d200077d544ca50007ef744c832005ff724c430006dc638c950006ff658ca31005fd73c8640006d56388421005fd7690730004ff7359542005fc7054931005fe7190c20006fd648ca51006ff644c921004f970d9421005fd7290430006fd658c620035be7408530025bc7448520005fb7059532006fe63c87100073d5454d430047f7558630006d96398021006fd624c010007de314c430004fd72986300077f6548530006ff71d8d520077c21941500077d528ca50004fd7298430005ff7358620007de434c650005fd7394721007fa3250210005fd75d8532004ff7655132006ff65c8430006fe76c8530005fe700c52107fbc41d9132007f942cc230007ed32c8520006ff658c81008f7e758ca50005fc724c730004ee7218c20007ed4354920037bc41d9130007dd5388730004f67118153005fd76cc810007f63148650005fd7348730006fd6390a20006ff654c910005fc7055331085fd7354932006de634c821005f87054f200067d6588430004fe76945300867e654c832007dd324c650074fe7690d31004ff7650e20005fd7398620005fd7590f2102d7e75c8220085fd7394932006ff644ca2007dfd7290d32005fd7308650005fe7190e32007ed628ca50004fd7690e52006fd65cc640027bc41d91200063e6599030006dd7558c210077d75c8650006f77658430006f96358021007ed624ca50006fe624c210007be4250b30006fd76c8550167de744cb31006bd6498021006ff6018121137ef5050b21007f5534c621006ff638c521005fc7150c32005ff7250d52006dd6354821006fd76c8650006ff5058d21007df7348630004ee72d90300077d548ca50006fd72d8d54007dd4354b31005fe7188120006fd6394e42014fe7690110004f671d9220006ed6290430004f
  | 11 => 0x6bc6418d21005ff7355132007dd754c832005f976c8220005fd73181410057f755813202d7e75cc620004ff7358810005fe70d9132005dc7354932005fd74c85300077d524ca5008f7c52d8d52005ff73c8430006dd634c821006bf6454d10005ff748c52004e7c6548530006fd654ca31006fd6548620005fd754cb21007ed524cb20004fd72d8143006ff64cc93105cff7654821005fe7190d3204f7f5248650006fe6258a53096ff7650c32006fd42d8131006fd6394e41006bd6454b31005ff7350950005fc7050b31005ff7158a53006fd644ca10006fc635052008dff7354a32005fd74d8532006fe72d8d540077e5348650007f921cc1300867c6559532005fc7255330004fe76c8550006fc6348550007fa7090930007ed524c520007df328ca50006fd6390620006fd6288430006ff7558a3105f7f5054f21005fd76c8730007be7408430007bc3255140007d9314c0300047d7518943006fc7258e4007ebc4158e42007bd54509300077d54086500077e7508530004fc7650530005fe7094731006ff6348540006ff6498132005f47150d310047d75d9331005fd760ca51004fa7018c21006fc42d8930005fd7094e21007ee624ca31006f5618c430006fd768ca50006ff4158332005fc7250630006ff654854018ebf40d8d5405dfe7208550007f53188730004fd72d9640007ed544cb20006fd43d8931004fd7694b10005bc70552410077d6548430006fc764ca41006fd65d8132004bf7458630006fd6390420005fd7390a20004bd7418c20006f56298430037bf43551300b7ef544c920007f66148730117f4504c52115fdc5250d31006f93298021006ff6158132006bd6498830005fd73c873004dff7554d21005fc7354a41005fd7018d41006ff53d8931006fd620ca500063d6559021007f53148550006fc4358e21085fd7594932006fd3218131006ff6394510006d73258432007ed2108430006fe3198020004f571d9220005fd76c8620006ff7158e20006fd6548520006ff6418132004fe7694d410073d5454942006fc7558c20005ff7150b300867f52d9532006bd6350a40005fd754c821007be4290430004fd7398021006ff654ca31007df3150c200047d7598c31007ee4354920004fd7398251007fa42cc230006fd73d8950007ed758c920006df634c921005f97008620006fd6559132007dd5350b30006ff5058f21005ff73886200e7df4194d30005f972cc230004ff7648730006fc5158f21006ff634c941007f671cca21006fe53d8543006fe43d8931006ff54d8931006fd65c8630005ff7250530007f66108430004fa7018931026bf42d9120005fe73d9521037be5490530007f93250210004fe7690d52006fd658ca310057c7155250006fd7258c10006fd62547300077f2194150004fc7655121006fd635
  | 12 => 0x97018f210e7dc4294d30005fd768c8100067f6294150006ff635095009ff8414c120096bf4259332006e66258430005fd7398321006de6398021007ed7298532006fd6458b30006ff7458c20147dc744c931006ff7655032006fe7258e51006fd7608630006ff6250950007ed5290b320047d7518e20006fd6350920007ee7158830006fa604c020006fd74d8930005fe718c9300077d52c8650006f7764c710006e93258032004fd73d8954005ff714c930006fc4258031005fd7390a50007df754c9310067f658c930004fd73189540afec544c920006fd6350a50005fd7298c10005fc76485300065c6354d52006ff3298241005fd7290330007ef324c941006ee6298430006fd70d8943005ff7448430006fe5398a41006ad6448421007dd434c650006fe7558c20005fc760853006f7f52551310077d520c650006bd5458a41004fb7059543005ff7350550005fc7155330006ff71d8930007fa214c12006cfd7694e310077c4119530047bc4050b30006fe7058f21004fd76cc821007f9424c220006fd6290730006fd654cb10007fa41cc230007ed4248630005fd7388730006ff65d8d21006fe2198030004fd7298410005fd7648430006756598432007ed628ca31005ff7258231006ff4158b30007f631485200867c5058a53005fd7190a30005fc7154930004f87059532005fd74d8530004fd7690e20007dd434c930005fd728c530005ff76c8430006fd6348620006ae6458830005ff7348710007bd6488430005fd73085200c7ec43549200067e6558c21005fc7054a21005fe71cc932005ff7354932004ef764c832006ff7458f21006ff764cb31006ff658ca30007de704cb31007fa7358021006fc6350921006dd634ca20006e9628c030006ff764c832005ff7688430007ed5390b21005ff7250630007bd4290120006fc63c85400077c6588530004ff7358a50007d9434c030007dd704c931006ff7654a31006ff6354540007dd5350730004bd7418f21006fc5258e20007f97008630006fd63cca41007bd4390620006fc42583320077d540c6500077d54c8650007bc6494d21006fd638c620005ff7054d42006fd70d8d54005fd7290d52006ff7458e1013fef5390b21006ff65d85320047d7598d100067c65d8530006fd76cc821005fc7354921007dc704cb31037bf4255130004fe768c550007f661c8430004fd7298231006f46148520004fd7298251076bc648c521005fd72cc640006fd7458b30004f970d94320067f6518930005ef724c620007f9614c220006fc63d8552005ff7694f21005fe7098532005ff7348520084fd7694e32004fd768ca40006fe624c010006bd6454c210077d5208650007fb704ca20007ec6208530007fa614c220006fe764c950047bf4250730006fd658cb10006bf6418121004bf7458632
  | 13 => 0x4b31005fd748c620005ff7358a51006fd650ca40107dc4194f300bfec518c920004fd7694831005ff7254d40004fd7318520006ff6318d210077d750873010ff453c85210b7ec754c920005ff744cb30006fd638ca51006de76cc931006fe6388620005fd7094d41047bc409073004f7f5348550007dd538c930004f671d9432006fe5318943006fd764ca50007dd21cc030004fe76c8520005ff7054d410067d6550830007bf6450932005be7090a41006ee624ca4001cff7654b20006fc6390920005fd74c8630006fd6348410006fd658c8100077d544c951004ff76480200065d6598c21005fd7518532005ff7258430005dd7308430004bd7498a10007ee42c8730007ed5288520004ff764c83007dfd7350932007dd324c530006fd7608430004ff725954002e7f5298252007bf7448530007f97090930005bd740873008f7f538ca51007f67258430004fd72d94100067e65588300b7ef514c920004fd7398a40005ff7250c30004fd7398a5107fbc41551320067e6558430005bf7458532006fe614c220005f87050d300877e65d9532006fd63ccb21006dd634c810007df214c030007bc7448650005f576cc6310f7df538ca30005fc7050d21096be54d8943006fe7458b10005bf7448550005fc714ca20006ff6354941007ee4248530004ef76484210077e3255151007dd438ca300067f654c930007f521084300047f7558332007f921cc230006fe6358f21007dd63cc810004fd7218d50007dd434cb3113fef5090b21007f87358021006ff7158a43006ff4058a31005df73484300077f41d9530007bf6450920027bf4250d200047d75d8f1002d7e75086200047d7598a10005ff7354821005fd7655132006fd764cb10007ec3154b20006fb6098132006ed6254831005fc7055032006ff53d8f21005ff75cca21006bd648c830006bd644cb310063c65d9110006fd53d8931006fd3298321005fd7390620047bc415933006e7f53d9531007bd4350930007bd5490530005ff754ca21005ff7058c21007ed7158830005fd7290e10004ff7359521006ff5358d21006fc41d8d200067d6394650005ff7355321005ff744c620006766558432005fd7098f2105cfe7694521006fd5358a41007bf6450930006fd6350f21007f672984300077d5454921004fd76cca51004fc764c910005fd70cc921006df7558c21005fd7318121006fd64cca50005ff7350430006fd75d8943006fc7058f21006ff7648650007dd434c520005fd728c63006dfd7394531005ff7408530007f7658c521007be4150730006fc63486200077e5148650006fd7690830006fe5318931007dc214c030006ff650ca40006bd6454b20005fd744c730006ff654ca3002cff7259520005f573c8521004f970d9631005f572cc6310077e7508630006ff6388520004f
  | 14 => 0x36bf4258e40006f66298430007be4290730005fe7608520006dd6350c20007ee42cc932006ff6354f21005ff7408630007ed4354b2007fbe544c940007bd5490630005fd7608430004ef7258d10007ef2108530007ed4248550006ee6290430004fd72d943010ff753c8521005bd7390942006ff50d8931005ff7054821004ee7218e10006fd7058a51006fe54d8930005ff7488730007bd4350a30005ff7254d420077d544c650005ff74547300b7ec514c920004fd76c8410006fc3198321005fc7150c20005ff73885200077d5354932005ff704c821006fe76c84300077e65c8430007dd634ca20005fa708c520004dd73d9021005fe728c550006fc4058b10006ea3258032006fd64d8132006f5611853203e7c51d963008e7f5359632006fd7258e510047d7699430005fd7390650006ff6508630007ee42486300066d6558830006b66458430177ef42cc932006ff3298650005ff724c730004f67118e20006fc764c9400047f7558910157dc40cc931005fe718ca30005fd7608730006fd614c020007de538ca31005fe76905300067f6508530007bd5490720005ff714ca30007ef3208620005fc7358242005fd7290730005fd7290d31007bd4390520005fd75cc821047bf4390730006fd6350520006ff7258c10005ff7250e10007dd5390b30007ee4354b200ffdf4254f30006dd6390c20004ec7258d10006fd6588430004fd76cca10005fc7150e32006ff6350550004f97018c21005fc7054b32007f6708c521006be6498430006dd639802107fbc744ca41006fd764ca41006bd644cb20007ed744cb20005fe70cc921006fc4258231006fd654c810007de314c73016fdc508c932007dd534c930006fd6358021005fd754c931007fa218c120006fd6350650006ee628c430005b47150941007f97388110005fd7418520006ff6418930005fd738c8100877c50d953200778754c220004bd74d9430006fe7058e420877f534ca51005fc7654d21005fc7058a31035fd7490930006796598032006fc4258b30007ed64cc932006fd658c932004f67118c2104eff6548550006fd61d8132007cd52cca32006fd6198132005fe7694d32006ff6458132005fd718c930007de324c950007ed624ca31007df754c832047bf4290b30007ec7250d320c7ec4154920006bd644c830007dd32cc640007f4638c521006ff4218d20006ff650ca20005ff7150e50005ff724c6400067d654cb20007f57194e21007f72148430005fe7094b32006766598432004ee7218c10006f26158032006fd6350e52007f5524c710005ff7354b2116fde658c932007f9414c220005fd7494730007f653c8621035bc7448530006fd614c220005bc7050d420047d75d8c21006fd768c420007de5388730006ff7158830006f55458432004ff72595430077d545
  | 15 => 0xc3298251005fd7308530004fd73988210077f6554932005ff73c87300069e6498c21005fd7418132035fd7490530006fd6588630005fd744c830004fd7318910007bd548c940005fd7094e42006ff7655232147df404c931006fe61cc020005ff7254d41004f77159132007bd42901300077c65509300063d6559320004ff7258241004ff7650e52007ef3254920006ff764c821006bf6454921006fd65c8530006f55258432097bc43d8943006fd628ca50007cf628c932005fd72945201a67f53d8954005fd718ca30005ff7250d31007ef324ca41006fd7258e40005ff7054e42007d5324c431005ff7054b21005fd7194930006fe3218132005fc724c650005f47150910004fc764c920006bd54d8943007be7408730006fd64cc810006f53258432005fd73c8540006ff644c930006dc634c920005ff735832107ebe644cb20006ff7654b310077e5354c21007bd6450b3007dfd7490d32006ff50d8f21005ff7348530004fd76c8730006fd648c8310077d5454e31007dd5390730025ff7450520004f571d943004f7f5354921006bd64c8430005fc714c220006ff3218141005fe7290130007dd324c63008f7f548ca500077d538ca51004f571d9643007dd5308530004fd72d9130047bf4150b30005fe72906500afec414c920006ff654ca21004fd76cc01005f7f53d8552006fe768ca50006ff63d8954004fd73d9421005ff704cb21006fd5318910006fb7648020006fe5458a31006ff648c9300057d75cc631005fc725473005f7f5394f21006ff6354d41004fd7318552006ff65c8630006f66148730007f97090a30006ff4358b10006ff6254940005f47150b31007f5328c621004ff764c430007f47154921007f57258430006fd6394d21006dc634c550005fc7250550004fd7398b10006ef6288530006fc6350910004ff764c810007ee5350b21006ff6350d52007bf7448630005fd7094521157df43cc931007ed2108730004f77648421007fb32902100077c42d953005f7c53c865007ebe64d913204f7f54549210077e6508430006ff6588430006fe6398a40006fd6250830004ff764c020005fd7094a410877f544ca5017cff7654a42007f8704ca20006fd6508530007ed3288520007ef328ca41007f9634c2200063c65191100065d6558c21005fd75ccb21006fd65cc620004fe764c941005fc765093004f7f5355121005fc7150d32007df7359532007fa708c620005fd7488730006fc6390520004fc764c9500077d758ca500067a6558021006ff6394920005fc73551210d7fb41cc130004fd764ca4011fec5050921004bd74d9731007dd658c932004fc7650520005fd7390920006ff6250550004fc7655132006fd62883100077f6559532007ef3298532006fd62cca40006ff654c931006796598021005fe7690932
  | 16 => 0xc620004bf7459521006fd6250430005ff7254530006ff6350951005ff75cc921005ff744c520006756558430006ff658c930005ff7690730005fd7498b30005fd739052005f7f5254f210047d7598a40005fe7098f21005ff748c530006fd6394f21005f47159132006fe3218550007ed744c832007ed5250921005ff7350730007ed7218132006fd71d8d52004ff7258031006b96498032097bf43cca4105f7f54c8650006ff629095006f7c754c650006ff7648730004be7619110007f4714c931005fe7194e32006ed6258430007fa314c220005ff74487300077f7548650005f6710ca20007f553c8521006fe6398620005fd7518121006fd768c830004fd7218151006bf644c921024fd72d9120006fd71d8943007ee2148430007bd540ca41005ff7255132005ff7358a40006ff4258d20004fd731881007fbf43d9132005fd754ca21006ec62cc941007dc704c832007dd434c530007f53148430005ff7454920006fe764ca50006ff6390950007f77258430006ff64d8532005ff7354931005fc7250e50005fd7688430006ff6508730007ed6208430004ff764c010005ff7354540006fd6390a50005ff748c720006fe764c920007f6534c621005fe7208430007bd544c940007ef21086300d7f842cc130006ff32181210067d6598430007ef324c921004bd7418f20006f5624c431006fd624ca50006fd54d8910004ff7655330004fa7018c20004fa70d8c21006fd6390920005fd71d89500067d6550430006ff6350920005ed7394920006dd6354c210077e2194150007df324c650005fd7398a51006ff64cc9320047e7619510007dd5348730006fc7058c21005fd7298e40007ef7198830005fa70905200077d53485500067d654c821005ff73551310067f6550d30006fd75d8d21004fc7654931006fd32181320067f65d9130007dc73486300073d5454a41006fd53d89430067f65c85300077e5354f21006fd5318930007df7354932005fd7298730005fd7608620005fd700ca41004f77644010006fe7358a40006fd3298021005ff7559132005dd7290f31006fd644c831006fd64cca51007dd53c8530007f9424c120006ec7158830005fe7188430006fc7158c200077d534ca510067f6550910006bd6390640005fd7298231005fc7694d21006df6354d21004ed72d9030006fe5458831005fd7190950006fc71d8d52007fa424c220097bc40cca41004bd7418810007f55348421027bc6490520006ff4258b10006ff764cb10006fc6348520076be648c430006ff638ca200063d6599032004fa7018f210077d524c650004df7359520005ff7558132005fd740c420005fd728c550005fd76cca51007f661884300077d5354a310cfef544cb200077e51cc650005ff7250550007f963c8220004bd7418c10006fd6458730006f
  | 17 => 0x4ff7259530005fd708ca410077c6550530005fc7150c30007bd7408530005fd71cca50006ff764cb30005fd7308630005fd73c8620006fd620c650004fd7218d4110ff750c8521004ff7258243005fa7008730004fc7655110005ff7158b30006ba645803208f7c518ca50006f53298430005fd74cc932006fd3218550007f44118532007f9428c120006fd6390520006ff6390550006fc6318954006fc7558e20007f9414c120005fe7018d21006ff6290550005ff7054d21007bd5450932005dd7308730006fd76c86300077d5394721005ff7254e42006fd6394b10004fd7218d10006fd634ca10035ff7450930006fe74588310077d5354921006ff3298640005fd7190130007dd3150f200063d6599320006fd7558e42006fd6254a31007f63188430006dc634c921005ff7054e41007f63148630006fd6390650005ff7458732006fd62cca41005f57394710005fd748c520006ff6254930006ff62189300877c754ca50007f631485300057f72551530073d5454d42005ff754ca310067f654c530007e52108520005fe708ca31005fe7194d321a67f51d8954007ef3218532006fd6498132006ff6308620004fd76cc820004fd7298e5004f7c6554d21005ff7308430004fc7650d20007f52108730007ee524c9200077d5288650005ff7250d3207fbf42d9132006ef62cc9410069e6458c21004fd7298e10005fe73d8121005df7250f31006ff6598532005ff7055121005fc7258653007ec6288530006fd6394e21006fe6350a20004bd7418153005fc7155120006bd4358a41004fd76c8640006ff640c810007fa414c220004ff764c431006fe6158132004bd7699021005fc714c920006ff628c550006ae6498830005fe7190330007de5350b30007f7714ca31006fd6208650006ff65c8730007ed5250920007dd5350d30005fd7094e41006ba6498021005fc704c821005f5710c810005fd7498732006fd65ccb21004f571d903006cfd7694731005fd7448430007ef714c920006fd6418132005ff7348630004fd73181510067d6590830006ff5258f21004de73d9021007f76198532006fd70d8d41006ff64cca21006ff7648630005fe7650930027bf42d9120006ff654c630006ff624c940004fd72d9031007de704c832037bf42d9130007ed62c8430006fd6358a40005ff71553300067d6550f20005fe7090d21007be419012000e7f5359610006dd7058c21005ff73508300077d5488650007f7754c710006f632984300047d7518f21006fc6188120027ac4250920006fd6598f21047bc4250b30006fd54d8930006fe6358620004fd73d922001e7f5359420006ff658ca40005ff748c630006fe768c620006fd638c650006ff64cc9510077d5454d21005ff74c8530006fd6298730037bf4250d30007f72188650004fd760
  | 18 => 0xd73d9531007dd324c550006ff5058632006ff6518d210063e65993310057e7194d53005ff735972104f5f5394d21007ed5250520007df7348430005fe71d9132005fd7198b30006fd624c810005fa708c930004fd76cc810006fe4358a50005ff7358242005ff7258730127ec5090921004ee7218153006fe6308650006ff4118d20005fd7654f21005ff7354a21007ec3194920006ef6250930007f97398021006ff6248550006ff640ca31006ff628c930006ff64cca20007fa708c520006fd6254831006fe73d8954006bf64d8121006ff6318552007ed424c920006fe7608430006b56498430006fd65d8532007de5350730006ed6294831005ff7250f30007fb714c2200067d6590430007f56108430007de32d8132006fd6290830004fd72d8141005ff724c020005fe7398321005fa708c53007ebe644c821005ef73549200877f5155132006ff63485500047d7518e10037bc4150530006f54358432005ff74c8630006fd654cb20006dc6350d20004fd7608730007bf744ca41006fe6308520007dd534c530005fe7298430004ec7259131005fd7390930006ff658ca200867f5358a530067e65988300867f5258e52006fe7058c21004bd74d9421004f671d9032006ff6508530006ff6118530006fd6348520006fe6348640006fd7694e210cfec754cb20005fd758c932005fc704cb21004ff7654b30005f67190d21005fc7055132007f4714ca2108eff7654832007f671cc921006fd634865007fbc4150d32075be74cc631037bc6450930006fd764ca51006fe64d8132007fa318c220005fe70d9521007f46148520005f77354510007dc21cc230006ec6254931005fe72cc650005ff738853016fdc538c932007dd218c130007ee42485500877c514ca500877f544c951007f8704c920016bf4259310005fe708c521007de214c030006ff764ca10004fd7694a31004bd7418d200efdf534c630007bf649052007eff644c940004fd73d9010006ff7058c210077f754c650006fc764c951006f6614c620006fd654ca10006fd654c820005fe72d9130007dd434c630006ff63c86200067d5318550006f56258430007f72148730006b56498432006fe5458b30005fd7348650005fe7194b30005f6710ca50006bd644c430007f9214c220006dd634ca41005ff7558321006fc50d8532006df638c950006fd764ca10005fe7098c21007ed42c8650007bd4390530004bd7418953117f4534c521005ff714c950006bd64cc821007ed424c921005ff724c540005fd7094d21005f87054920005fe7608530006fd6298430007bf6490530006ff654c930007df744c931006fd6394721005ff7350a10005fd7498132147de544c9310067d658c430004ed7218c10007f87059532006ff6350520007dd7318532006ff62d8143006fe6158430
  | 19 => 0xc932095ff7250f32006fe6308430005fe76c8520004fd72d933004f7c5354d21005ff7388630005fd739494009ffb424c120004fb7644010007ef6208530005fe7394721004fd72987300047f7558243005fc7354942004fd72d97300067f65885300066d6598830007ee4394920006ec624c931005bd7408620006fb3298021005fe7094a31005ff7254d2107fbf4355132085fd7294d320077d52cca50047bc4155330007f9218c220006fe53d8542006ff6518532005fd7218143005fe728c430007f631181210067f65d89300077e6588430007f97008430005bd7390a41005fd74cc620005fc71553320073d5450e50006fe53d8931006fd62c8650006ff7458830006ff6354d42006bd54d8d42005fd74d8132005fc7258730006fd650c420007bd4390630006df63cc921006fc6158132005ff7150d30007de324c83007cfd7690b32007fa424c120005fd7294530006fe5358a41006fe63c85200047f7558221006fc5398a10097ac4250b320077f4219530007dd754c931006fc5058632006fe71d8950007f53188650005fd760c620004fd7398a50004fe7608550006ff764c730006fc4058e21006bd6498c21005ff7254e41007f56188730005fd7098c21177ef41cc932006fd650ca20005bd7290d43007bd7408630006ff7158b30004fd7298241006ff63945200067d6548430006fd628c430006ff65c8530006ff6588630006fd624ca31005fd718c95007fbe544ca410867c654c910004bd7498910006ff644c92006f7f544c650005fd76cca40006ff65cc8100ffdf4154f30005fc7055232047bf4259330006fd768c730005fd7494930006fe63c8650007ed628ca40006d56348421006ff63181210067d54d8951006fd638c721004fc7650d50007bf7448550005bc7050e41007f9418c120007f561c84300077c6590930005fd7398810006ff4358e21006bf6488110006fd4358a50007ee5390b21005fd7294e32004bd74d8a10007f5534c5210077d54cca50006fd6508730117f7534c521005fe7218550007f4329471005efd5398821005fd73c8650006ff650ca41004fa70d9642005fc7154932006fd7608530005ff7350931005fe71d9532005fe7198b30006ff654ca2008f5c5354e32006bd6454f200cfec514cb20005ff748c93014fdc504c931035ff7450530006f661c8430006fe76c8630006ff63cc941007bd4390720004fe7694d21005fe7118930004ff7648640006bd6458c21005ff7150a50094ff7650c32006fe7690b30007bc50d9121006bd6494c21006ff624c930006fd42d8151006ff64cc92111fec5350921006fd7558a43006ff654ca40006fd654ca4007ebf4258e42007dd5350e32007bd5450830007df21cc230006fe6350620005bf7448430006ff7458e52004fe76c8530005fd760c81006cf
  | 20 => 0x7f6614c620006fe6390a20006fd6248430004de7318542006ff7458e20005ff768c620006fd650ca41005ff7254f10006ef7658830005fc7155130007bd6490730005fd72cc650007ed524cb21007ef7259132006f9624c030167dc404cb310063d6599331006fd76909300067d654c832007dd5388530005ff76887300b7ef524c920004df764c030006ff654c920006f95458032006ff634c620005fd7090f21006ff65c8620007f531487300047f755913014fde754c931005ff748ca30004fb7059532074ff7359131006fe7694d21006ff5358e10006dd63cca20004fd7318550006fd658ca40007ed52909200077c6590530005fc714c930004f77159542007de5390b30006fd6254b300047d7598e41006ee7158830006fc4218d20007de7308530005ff744ca20006fd6350e10005fd7518131084fd73d9532007ef3258532007ef3254b20006fe63c8430006fd5358720006ff650c62016fdf538c932007f94348210006fd65c8640007dd634ca41006ff62c8530037bc4190930005ff7254d20007cf724c931006fd74d8d2104e7c5058a5107fbf4255132006fd654c821007f8714c220006fe6350a10007ef2188530005ff724c010004fd72d9010005fc7250430006fc41d8132076bf4359231005fd738865008e7e658c8300057d7294d53006fe764ca400877f53d9532006fd624c650004fd72d9630005fc704c931005ff744c53007cfd72d9132004bf7458910006fe7158e20005fe71cc220006fd62086300067f658c510005f87055330006ff5458e10004ff7259031004fd7218543005fd7598132006fe3298251004fc7654941117f7504c521007fa70c8530004bd7418b10004fe76945200077c3294650007f96018132007ed4394920006fd7458f21007ed3250520005fa700ca31006fd64cca10005fc768853008f5f5398a53006fc764c921004bd74d85530077d53945310c7ef4354920005ff7054a21004f57118153006fd5458b30006fd6290430005fd75cca21076bf4398643007ed424843019ebf4318554005ff704ca21005fc7054a31006ff658c920006fc6218143006fc5358a10004fd72d8d41005f671cc921006ff42d8d20004fd73d8552005fd7390a30007de5250f31006ff6508620004de7318c21005ff74549300bfef528c920004fd7218143006fe764ca410067a6558032047bf4190730006fe6158730006fd7458e52006ff7058e52006fd658853005f7f50c8650006fe7458b30004fe768c950005f57394510007ef3288620004fd7318542004f471595420067d5318552005bd7290640007ed624ca40005fd7294d42006fd65c8730006ff6208530005fd7288530006dd63cc821006ff6390920007dc3250d31005fd7094d42005fc7055321005fd7598232004fd7298e51005fc7159532177ec64c
  | 21 => 0xf6588730006fe6258b30006ff3298321006ff6394d41006fe7158e52005fe720c650005fe7318141047bc4290730005fd72cc020004fd72d9310007bd4250530006df634c920007ed6288430006fe764c9400047f7558241006fe7558e20006fd53d8940006ff64d8930006ed7158830005fd73c8710006ff6558132007ef7250e32007de5308530006ff6508520004ed7218153007bc7448530006ff648c810005fd7390530005fd7550d32006ff5458a10006ff624c5400047f7558031005fd70cc821005fd75d8d21005fe719093018cff73595430877c5055132006ff5398a10005fc7650530004dd7698c21006fc7258e51005fd70ccb2107fbc414ca40006f6614c430007bd544ca41007be4190320094ff7259132006ff654c530076bf4259231006ff70d8d21007bd6448430004fa7018810006fe4358a10004fd7690c20006fd2198030005f97290110004fc7654930044fe7690130007ed3294520005fc724c530007bd4350932006fd7058e4208f7c5054a32007df6354d21005fe7655132005ff7308730006fd628cb30005fe769052004f7f5454d21007f63188730004fd73d9321006fd70d8954005f97090620006fd62c8630006fa6398021006ff4158d20007ee2148730005fe7108430005fd7190830007ed528c520005ff73485500077c6548530005fd7550932177ec42cc932007ee6208430006bd54d8940007bd430ca41007f47298430004fe764c950005fd73c8520004ff7650430004fd768c810005fd739072005f7c51c8650005ff7250430004fd72d8d54004fd73d9221005fe7290530007bd5490420004ff7358a40005f5710ca40005fd728c430007f8214c030007f63148550005fd7690b32004fd7298c10005fd7448730005ff7154930004fd7398321005fc7150f3003e7f52d9630006ff6390520005fa70949300877e6555132005bd7408650007fa428c120005fd730855005f7c5059721005ff7150e30005fd7294f21006fd43d8910006b96458021005fd7290620007be4190130006bc6519121005ff7488620005fc7154d20007ec6250930004dc7359520007fa7090520005fd7418930005fd748c530006fd71d8d54005fd7550e32047be5450b30007de3298132006ff6394f21006f672984300ffdc4254f30107df4294f30005fc76505200867e654c8300047d75189310063d6599030005ff7350b30004fd73d90200dfdc4154d30004fd7398241005ff7050f21007ee3294520004bd7418d52005ec7250d32006ff75d8d21005f87048520007bd548ca41007fa414c120004fd7298e40006fd5318940005ed7394b20006fe7158c20004f671d9030006fe7358a510077e5354e210c7ef4254920006fd3298251005fc7059721006fc50d8d21005fd7650730007bc7448630005fa700ca41007f8704c530
  | 22 => 0x8321006ff7058e42006fd635482107cfd7258c20007f93290110006df7658c21005fd7290e20005fe7290630004fc7648550007ed5350921007ed5248520006fd638ca40005ff754c921004fd760843002d7e750ca20006fd65cc810006fe6298430006de634ca20005fc7054c21006dd6394c21006ff73d8930006fd6354b20005fd7590d21005ff7550d21025fd7290120005fd748c630006ed628c830006ff6354921005ff7354940006fd6288650005fe7094f2104f7c5094d21007ee714c920005fc704ca21005fe7190a30005fd71d8930006fd6258653006de634ca41007fa70c8630006fe70d894305e7e65c8430006fe53d8943007bd5450e20007de53c8530005fe709472112fef42cca21007f8704c630007fa418c1200057d7508730006fc53d8532037bc4050930004ff764c832004f571d9432004bd74d8c21007dd32cc650007dc7058c21005de7308620006bf6454d21006fd644ca20006fd3218151005ff7354942004ff7259610006be6458830007f65348421007f72188530006fd7558c21005fd7294d4308cff7359532006df634c550006f9628c030006fd5398a31005ff724c650005fc7055131006ff4298f10006fd6158132005fc7255130004fd72d9631127ec5390921006fe7058831005fd7408630004fd768c8310afef424c92006f7c514c650007dd438c830005fe7094c21007ec2188120004fd7218550006ff65c8520006fe7158a53005fd700c721005fd7290650006fe63c8410005fd7298e51006fd5458f20006fc65d8d21006fd32986200073d5454e41004ff7358420007fa708c530005fc7054921006ff764ca200063d6599021006fe31181210063e6559030006ff644c810007ef7250d3207ebc644c921005fc7058f21007fa3290110005fd748c720006fc7358a510077d6555132006fd6248640005fc714ca30007f8704c930006ef6290930006fe639832105f7c50c8550006fe6390620007de7308630005fc7250d30004fa70d9021004ff7258e51006ff5358a10004fc7650d10006fc7458b10004fc7650550006f95258032004fd7318940007dd7308530005fe7650530007ee424c920005fb704ca2003d7e75086300047f7558d20007dd538c932006fd54d8d21005fd748c930005ff7058e42007ed5290520097bc41553320077d54cc951007dd434c550007de5390730006ff5458a30006ff6354940006ff6348520006fd4358a10075be740ca31006f5618c7200077e7508430005ff744c630007fa7008530004fa7018542006dd63cc810005fd7408530005fd7390630007f62108530007ee62c8430005fd7648730005fc7155320006fd43d8930005ff724c210004ff764c640007f9214c120007ef2188630005fd7294c21007fb214c03015fdc5050d31005fd74d95320047f7559110006f
  | 23 => 0x857c7558132007fa708c630005fc7059632007df7098c2102e7c50d8950007de21cc230006ff629011005f7c5054b21027bc40905200867e65d9532006fd53d8930006756558432004ff7654a31006ff74d8d52005fc7258430005fc7250e30007be64c8430027be5450d2008e7c658c930006ff644ca31007bd4350830007f97008730006fd630ca41006fc53584200067d6550c32005ff7054942007f7328c621066bc640c521006fd640ca50006fd62c8730005ff7550b31004fd7694b30005ff73c8650007f62108630005fd72cc010006fc5358632006fd42d8132004fd768c720005fd72d9130007dd43549311ae7f52d8d54005ff7158830006ff7654831006ff658ca41005ff7408430007de534873008f7c5055232076bc41d8d41006fc5358620007fa70086300077f6554d32007f632947100077d5454932007ed3290520006ff63545200877c5054932005fd7518d21005bd7408520005fc7150f32007de324cb30007fb218c030046bf4259330007cf734c9200047e76195300067f65509300067c6518930005fb764c220004fd764cb10005ff748c420006fc5158e10006fd6548430005fe7090932147de744c931007f5528c52105f7c5055321005ff7254d10007ed42cca20004fd7694730007bc53d9121005fd7018d210063e6559021004fe7690d21005fe7190e20005fc7054f21005fe718c830006ff7558c21007f9218c120004bd7498c3111fef5350921006ec764c920006bd644c832006fd634ca40007f9735802102e7f5359620005ff714c830006ff658c940007bd42506300b7ec524c920007f8704ca30006fd64cc932006ff654c620004bf7458d21006fd64d8532006ff764ca40005fd75d9132004ff7358652006bd4218141004fd72d9231005fe7294530006fc4258d20037bf4350930005ff7448620006ff764ca51007f653c8521005fb7048620007df704c931007dd744c931005ff7255131006fd654c640005fd73d8121007f57194d21007de3218132006fc764ca51007dd63cca20006ff648ca31005ff7350620005ff7458b30005f47155321037bc6490530005ff7354520005fd7098e42006fc645813214fdc534c931005ef7354b20006bd6454832006fd53d8910006fd5318941006fd7258e10007ee42c8650006fd6208730007de4354931007bd5450b30007f8218c030005fd744cb30006ff624c530006f56388421005fc724c630004f671d9643005fd7418532006ff61d8132007ef2188120004fd72d8131007be6408430006f96398021005bf74487300063e6559032007f66188620006fe6348620005fa7094730006ff6558532005fe7118132006f93258032005fe71d8132005ff7255330024fd7690a20006ff6388620007ee3290520005fd74c8430006ff4258f10076bc648c510006fd635
  | 24 => 0xf7655032006fd634c820005ec7250520006fd76c8430004ff7650e10006fd6588730006ff624c810006fd6508520005ff7150930007de3290d31045be74087300047d7518810006fd54d8d10006fd6348710006ff6118132004f970d9642005ff7454520005fe71d9130004fd72d8d510077d548c650007de328c630006df6350d20004fd73d942009ffb414c120006fd42d8121006fc74d89300077e5308650007de7058c2114fdf544c931006fe3298430005fd76887300077e3294650007dd3150c20004fd760c420007f850d8132005fc7159132005fc7158132005fd7348530007f77159132005fd72d8530006fd7690a300067d655883004f7c5154d21007be425093011fef5050921006ad6458830006fd638ca20006ff7655132005ff7350650007fb7398021006f7628c510047bc4150f30005fd7290520006dd634cb10006ee6254831006ed745883016fdc658c932007bc7448550007df7354b32027bf4390520005fd7294d31007de434c931006fd640ca31127ef53909210067d6558430004ff7358b10007f5328c521007fb744821016fdf508c932005fc7250730004fd7298650004fd7398252005fe7694d21006fd654ca20005fe700c721007df7058c21006ed62084300877f524ca50006fd5398b10006ff6290130007bf7448430004bd7498820006fe764c8100867c654c930005fd7218d5408cfe7694d3218ebc41d8d54006fd6358a51006fe6348710007de3250d31006dd63cca41005fc7050931006ff6548430006ff634c921006fd634c821004fd73d9640007dd3190c20007ed3248520005fc7155032007dd43cc620184fe7694d43006ff654c940006ff5158a30005f9700c810005dd73086200047d7598820006fc4198d20004ff7359420004fd7318950006fd658ca20006fd6298653006fc4358a31006fe6388650005fd7290e50006fd76ccb21005fd7494520007f56188430005ff7250e20006fd6598532006dd634ca51006fe6558f21005fc7150930007f532947100077f650853006f5c5354d31005ff7648430007ef715883001d7c754c020004fe769093004f7f5255121005fc7158e20007f72188630006ff53d8532004bd7699030006ff7655332006fe6388520006ff654ca41007bd424ca40006df6394d21005fe728c730004fd76cca40006ff3298021004ff7644010006fd5358a31007dd7308630006fd5358642006fc7158e200047d7518b10005de7308650097bf42d8943004fd7318154007fa7398021006ed628ca40006fe6458b30006fe71d8930004bd7498f10006ff7058e51085fc7654932005ff744c920004fd73d9521006fe7358810005fe768853005f7e6554f21005fd708c721007bc3290640006ff6588530007ed42c8530007ee4248430006ff65cca21005fd748ca30007bd5490430
  | 25 => 0xc931005fe7094531005fd768ca510867e654cb20006fd654ca41005bd74cc620007dd544c93100676659843006f7c5055131004fc7650d21004f4764c5210c7ef4154920005fc7159332007ed3254520005fe7098a310065d6394e50005fc7150a30005ff7254f20006fc41d8930006fd638c810007ef3294920006fe6388430005ff7354a42005fd7290d21006ff7458b30005dd7308650005fc7354821005bf7255143006fd764c810005fd7290110006fe70d8d21005fc7154f20006fc6318121005fd72cc210006d96358021006f26198032007f6534c5210077d65c8430005fd754ca31005fd7348630047be5490730005fd7190b30004ff7259130006fc70d8d21005fd76c8430006ff630c521006fc63c8550005fe72d8550005fd7498532086ff654c951004fd768c430006f53258430004fd72d8c10006fc7458b30006ff65c8540005ff734841005efe5398821006f1615803200cfe7694510005f47155131006ff6588620007f66148430006f94358032007dd43cc650004fd768ca51006ef764cb20006ff7650f20006fd6354a42006fd65c8520007ef2108430005fc7050e32037bf4250530006fd6508620006fe3118131005ff7250e50007ed42c86300077d6508430006fd62cc210006fd3298430005fd728c730006fd74d8950006fd76cca41005ff7354941096fd73d8943005f4714c9310065d65cc03007fbf4250d32006bd6458021007dd324c430006fd75588310077e53c8650007f52108650007f821cc130007de634ca20006ff6288530006ff7558f21005ff72507300077d3294650006da6358021006ff72d8d54006fd3298020007be4250a30005fc7154b30005ef7250520007bd5450b3206e7e654c430004fd76cc020007bf3255140004fd72d9641006fc5158a30005ff704c9410cfef524cb20006fd658ca41006ff5358620007f4714ca31006fe62cc210007dc7348430007f66118532005fe71901200077d528c650006f95258021005fd73c8530007f53188530006ff6354910006fd7158b30005fd70d9521005ff7150d50005ff7488520006de634cb100067d5458e50005ff7255332006ff70d8d52006fc53d8d21005fe7198830006fd62cc010005fe7654d21004fc7654910007ec714c920006fe7158b30005f67194d21006fd634ca20006bf64cc921007dd434c931006fc6308550006ef625493114fdf534c931005fd7394520005fd7394a41006fd4358b30007bf53d9121094fe7690932006fd6548630006ff41d8d20005fe71cca20006ff63c8540004fd7298e41006ff654c520006ff7558b300077f411953004f7f5054d21006fd62cca500077d2194150006fd63c8640006fc7058831006fc7558f21007ef62885300067f65505300067d65cc821006ed624ca40005fc7054b31006fe6358a40004f
  | 26 => 0x7f5528c510007fa214c030006b56458430006fd3298431005fc7055332005ff7655132006f5624c710005ff765073007ebf43d9132006fc4158332004fd7318a10005fd7694f210877f5459532006ff764ca50006fc42d8d20005ff7608430006fc5018931005f47154921097bc4150f32004be7619121006fe764c921007ee62884300047d769942117cff7259542006fd65cca10086ff654c950005fe72905500073d5450a50004ff7258e41007f72148650006fc6308620007ed5290720006ff6394d42005ff7354530006fd644cb10007f53294510006fe62cc010006bf6350941006ff54d8d21007f53188630004fd76cc410006ff648c950004fd7218540004fd73d8520006fe635881009ff8424c120005fd73c8630005fe70d953204e7f5358a51007be4150530005fd7394920005fd744c530006fd65cc820007f67194d21006f5628c431005fd7308430006fe76cc941006fd65185320057f7255250005ff7354a31005fe7394a41006fe764c910006ef624c93104dfd728855004f7c7548650006fd6558321005fd74c8730005fd74d8930006fe5458b10007f47258430006ff5358632006fd634c810006ff7058f21005fc76909300067d54d89530077f65c8530007ed42cc921005fc7259330006ff644c950006fc6348540005fc7158b30005ff7150a30005fd73d81410067d6354a500067d6598c21157de54cc931006b56458432005fd744ca20006fe6390420005fc7354b21006ff6198132005fd7388530007dc704c931004fd7690f21007ed42487300077c4219530006ff5358420006fd71d895405eff7654821005fd7290130006fc65d8532006fd65c8620006ed435883006f7c5054931004bd7498e51005fd7390550007ed5390921005ff73484300077d5448650006fe6398021006fd6250a50006fd624c730005fc7050d320077d5454831006fd53d8941005ff7258e51006ff6218143004ff764cb10006fc7158830007f97090620004fd72d9030007ef31549201967f5218154004de73d9421007ed3294720005ff705494105f7f52c8650007bd4390420005ff745873008eff658c950006ff654c941006fc764c941005fc7058532007ec6290930007bd438ca41006fd6308620006f96388210004ed72d921015fdc5350d31006ff65cca40005fe7648530007fb7059532006ff7058a51006ff63d8121007bd5450d20005fd7294e21005fe729865305e7c65c8530006bd43d8940007ed528c72008f7c50596320077e7508730006fd648cb10005ff748c430006fd6258430006fd53d8532005fc7359721007fb21cc130007dd5350930005fc7690530107df4194f30006ff7648530006fd650c620007dd5350530004ff764c821006fd6288630006ed62c8430005fd754c921007f57298430005fd718c830007de704
  | 27 => 0xe43d8951007bd5490730006ff63d8552004fd7398010006ff5358c20006fe321854004f7c50d9521007bd4350b30006fd7058e5107fbf424ca40006fe764c9510877f5355132007ed628c810006ff5458e20006fd6250650005fe7094e21005dd7308520007ee2188120006fc7158b30007dd5390930006fe61d81320afec744c920004fd7218c10005fc7050f21006fd768c720167dc744cb31006fd6350c20005df7354932006fe6350a50004bd7418c21004fd7218530004fd7398221056bf43d9221005fa700852000d7c754c210005ff7408730006df764cb31005fc7150e20004fd72d8f10006bd54d8d400e7dc4194d30006fd6350a10004f67118c100067a6598021004fd73d9642005ff714cb30005fd7690b300c7ec4254920007f821cc230005fd7388630007f4714c921007de634ca41006ff65cca200067f658c530007fb21cc230006ff6294930005fd7590932004fd760c810007df754cb31107dc4294f3008f5f5394e32005fc7154b32084fd7694b32007dd324c640006ed624c430005fe718cb30006fe635092007ebf42d9132005ff744c930006ff5458c20005fd7598f21006fc3298241007f5614c650006fe31983210dfdf4354d30006fd634c6400067c6194150006b66498432004fd768c8300063e6559320007de5388530047bf4255330006fd65cca40006fe7608530037bf4290930005bf7355140037bc4090530006fd5358632007dd214c030006fe7690930005fd759832105f7f5359721005ff7358021005bd74cc65008f7f528ca50037be5450d30006fd75d8930006f76198532007ee714cb20005ff7250d21006fd62cc810006fc63c8620005ff7054a42007ee42c85300afef414c9200057e7194e50006fe65d8532006fd6398021006ff6588520005f97090e20004ff7259630007de634c810007dd434c430006ee624ca50005fd7390950004ff7654b31047be6450b30006ff658c630147dc434c9310067f6590930007ef64cc932005ff7448520007ee42cca20005fd75d8121004ff764c620006fe42d813214fdc754c931006fd62cc640005fc724c55008f7f5355232007dd434cb30006ff50d8532004fd7398650005fd764c810007f63148430006ff65d9132006fc64d8930005fd75181320077d5248650004ff7359721005fd70cca21006fd63c8620007bf6454d21006fc7158a53096be64cc821006ff71d8d54006ff53d8d21005bd7408530006ff6390d2107dfd7390932004f970d9021005fd7394b100077d7508530056bc40d9221004f47159132004fd7298f10005fd760ca40004bd74d9720007dd320ca500077e51c8650006f4614c530007dd534c931006ad64c8421005ff7350520005fd7498730006ff6350d21004ff7359221006fe6258231006fd7358a40005f8704c530005bd74c8220
  | 28 => 0x880140e200f00880e000003200183e000c00a004800c03800303586a000a000007801077a041000001c000012000893000000107f85ec002003012000002604d01d01000060010e281a402ac8000f80980062c9000004809200000204240062e3003000402a002020805c0560040000014048051002001c002005000000005009704e800000000161e8f3c0000020000020224061003801c13002600000000380ce03e801400e12f193003c24200109d8014000002008000404263e008009c014010004006c02a0960268208006011005800003a00c00004ac00c00000a81541ac01501206f000c001000007000000302a800802e009002801014c01a003006402c00c35f801c00a001000800002e00001a808c10a27600c01f001087c30b0004000126035806000600200e807c09800d112030400200000080d800001401887140000040768004000000000021c00000100200800be0fb000000000200900c807808600201b0014000022000008802800f02581a000402d007801c004047008800033e00a0b9815401200100701480ba37f00a80780020000290000000001034800808604900d001400604900000048721e2006805000400000480142860750010008006001001000400000a00283e8068262000821c00c00400480500020040000038016049004001403a17a076000806ac72001800c00000402d2bc00e0252020000000c000000803c00c01100100f805000c014801c068002012002c02c000099800005601100680d40020ba00080000680000018004114014027003000018b000011427a0d200f00000980000000050036010003000800000201a8024026000069801c02a009000006c008003001000002a01e0198f4400800b00f803c02c10f000804009e026012013803c0010f3807c0000010877f5354932006fd43d8951005fc7054e21004fd769472004e7f53d9521007be4150630006fe76cca41006f6768c510004fe768c920006fd6354a41005fd7290d51006fd6350e20006fd638ca410077d5454931006fe6398810007bd434ca41006fd648ca50006be41181410dfdf4254d30007ed3290720006fd624ca51005ff74c8430005ff7250d20004bd7498e21037bf4390530004fd7694c21004fa70d90320875f5394d32004ff7655232006ff42d8132005fd74945300063e6559331006ff5358e20005ff735512115fdf5350d31127ef5090921005ff7354a41007f63188620006fa7688110007bf50d9121006fd63c8410006fd6290330005ff7354921007df6394d210065e6558c21006fe76cc921007df21cc030006bf6494d21005fd7394510007ef754c920006f97398021005fc7250d50004fd7398640005ff7355120006fd6398a51006bf64d8d21004fd73d9620007f72188550005f7714ca31097be54cca41006f
  | 29 => 0xd005100000000fa00d00c800400600000d00a800000f000004c00005f049824ca3c004003001400001c00200dc032001015000001e01d00080080162fa006800404e000004000401400108c805c00002806384fc00001500c80080e8003006007402e02302c806804004200b80303be040000000801001500000000c200500d80180560010000000000004000010402e00400001ac01e0190540018156014000001400200200b006400a000003801005c04b02d00000a0001002804c03c03c00003840420160180b1814e001014000400a0040c4807400200000a80100e217d002823800402b01d8008000002010807c00c0090030028a4c00138a800001c1c3024800001e02c005801c000006027804c0da0000378084008019009834000a111003001000005900d001000002c00581b0000000005800468c00000d0970002000027800007006000001e005200503d804c058009006807c00000b01b0038014040003007400000000f8008012024024801432200b01d800000e00e02780000a2005012810802a42400723cc004046000005805001600500d421600906400680040e200080000021370298284004218003800403802b01300b46da0020010e5400e02e0038188000045086803006600004280080100070000bb00060040a800501d4003009800400010d01c001004200b00400082c00000008ac4b4800000e012c7ac07d002015001a00000080002722e401c804400a08a000805008206100581bc0200240038088008005000075401000500a804801c047000005006800000e88c8000000016007802000e000807402a01f00400140b000001680d4020298017805400600101380600082f30010089da80480560000024006000071c00200412600c00f200e01d008000400000c017c000001000005014200200683bc0000110148058042000002834801e000000029044e0930aa84c004a022000001401400c00800300ba00303d8000004040010000003a00001e00240e0033017002400200300b039c000000001031400000a0088108dac007000000c00400000d01b402a0f500380282be410002000039400405f00c40ae04d00085b010a0a8000800c09614e0000434078018000001000401912a005c532248001002001a014052807402a00000000683c8007000000c02e0040010094282002002804000402f00e005400e05f007805c00800e000003400000502284280066ff000000023a017000000806600a02e006800200000600c80280280038088124000006807c3c6019001001402a00b002802c052006000089400203500080000080050000038046000002801001a0020500008010003012806000c009003804000c00000500ac01400c001802401800000080140000040018008044002024003800031d009000000000600
  | 30 => 0x109c064002014806a0510048b1000000400004aa148002065001006400b0080000070051004002400805702500240ec01300a801800e01c00c03686720f001b800011003a17a009c00001e06d000802a00000300440000070430014234017079802c00201e00585d812800402286d000a08b5c2001c00405000f000400e00707d811400400a02380301a000504c00580101e3000000800600307a0004006001009003400200d074000001602c047806c01a003000002c002001003001001416d009800005201b0038000070010001001400000301583ec004001004000c0040120b6800031a00800e004803e12b8e400280260060140010006007095803c00000003805b41e80c212c000c0080000030054008033084805c000000000801801400c035808818200305a00b006a00204700040520350090d9415400e00000041de0130018004008033011002c0a403c00a8004036023002005c00000302d00c0010037004800013800207000e005c000004800000019500300a00160490008000000045001088002600f018803001c004031009800001d01680100142e801f0078002000000001801e8af0008000000042007803402800072680040140000028000a0e01700b803402603000e001804c00100482a800001101300c0002047006000002e04b00400240c401f032007834400400000b807e01601f80540040000060000032005006000401e006024800000000100780100080160100014022074002808801c00700880180062ec116847c00e00d06d805c00e00e00002fc00a00a000000c004000039000c00200c009803800000d0000068022000004003400201201e0000bf600100080001f80250000024000000009018817400100002a000200000b800401000d63f801003200301f0008014000005000800e05d001000407a0d8000801002a00100781200420010260028000011001800402a00b000004401000001a80640000070008000048013002800c0a000f009800c02001700600dc00a09700180081da08f001800801203c00000b002601d002003402e0000028000012000001800002600001600000220000000034002009004801000e0080d4800002804100300000a600c00682f800036a003801c01c0824310038000025000802c000004000094802400e00180a43780050088008002004038801800200500100041ea000005859000809c000025001000235e807c0da01a025004001807401400480f4000007001c00225a0038000182000000000c0b8025039003800e14f00e801c00002600100a400600c0030000002008018000401c00600500580
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xcbc645c332484015d904b22c5980032f9d362085300056ec34e09906400c7f76551520c4018faed3a84398003b961e62984300069f3aae810a6000eaf41d89424c0019dee4b1262180027e2017550e320063e3a0cbb0a6000cbd7418c21540011fb0f31c8528002bd60b76584300076dc02c73004200af68114163c84013f30e10e60980033b5d3624c9300056ec1880b1c4200cdc805cf64084011ff04bb264080025f6147358321005ea40ae999262008fd878ca608c4019f2e0382c610803e3dd1434c8320076d43cc73004200cde835d8210c001cbacb10e60180031f595748c83000737b2ec52126045eac64593324c8019e8ec98a42980023fe197294730004bfc3aa810ca000cf8329c3658c401cdccab8cc4180023f61b73553210067dbb2c69844000b798094c2194001cdacaa124218002eea0242509300075a326e2b2264008fe87d95324c4011fd0fb2a4318002bbe097358a400047f43ea4b1c40008ff865ce210c00197eeca1283980023fe1d65d9132005dbc22e4b0860009ee8790d52480019ece3b0ec0990031f55172d8d510066fbb6429806000cbe765d0214c0019bee6b1ac1908026f61071588300063e32ae23126000edb8758e60084018fecbb9262980033758c704c8210055ec20a7b1a42009fb805d532484015db04286c7908023fe1d32185200057b40ea6b084000cbf641c13248401abaeb3984298002bb219744c9200063f3b0cb20a60008fe87d01628c401d3ac9b82c6108027d20575509320063f3b6ca90a6000aed82d53624c40197ac9b92c2180033be057218153004fcc38652042000aef8258e52c40019bee731ac5288032f5d7644c9100057cc00e4b1ca200aee8210562cc001cbac6a9aa4108027b6087054c210066fc1cec10a6000c7f75591604c8013e902ba265980e39b1d5624ca5000774c2264b006400a7d8694d530840137b0f3a042180023f61e76084300057c402c6b064200c7f655c8614c0015ed03a9ac3100033b9d942c8530006dbba4c29086000cfb321c16550c01b5a40ba0c6a9003ad551425843014eaf3aeea9926200cbd75d936048401dcae5b0cc2990033b5c932181510047f43e86b1620008fe8710162cc0019f2e0382c790802bbe0543588300066fbb0e0b184200aef8258d32840019bee7b1aa4880026f61c53191210057c402cb1926400aef825cd6204001a7aa9b9287280039b1946290930006aeb9aa610aa000aef8750d620c0011ff04b9ec8900023f60f7654b100067d990e0b2a6400aed8294c6250c011fb0c38a65100031f5d465d85320076a40264b086400aed8290f624c401d9d04382c61088b9d9953148430006f5b06e6a924000aed82141618c80197d083b2a899002cfe0d5454a4100576c10c690aa000e5d651c16308401d5b09b128498003a75907058c21
  | 1 => 0xecb39042980037adc1754c92000767b1e64a924000cfb709c1639080197aebb20c0908032f1d063485200065a320e29924200d5d755cc210c0019bac7b92a610802be61532580210066eb9ac79082000cef74dc5620c00197acbba24310003375cf32983210066fb9ac6a964200adf8358932040015e902b24c099002f660c218c22000576c16c72928000af5829da314401197ceca1480980029fa1841195300065fbaec8992200097e878c9545440197ec8b94a6908039bd964248530004be43aa8994a000ecd628ca310c001d9ac6a966410802afe1161cc0200065eb22e73004200e3d65991210c0015ef0c98c42180023f61d63c86400056ec1ecb9948200e3f65d9153484019bee6b1ac3100023f61f650ca40004f743c86a964000dcf63dcd5248001c7ee8aa6c6a9002bb60a5398a31004bfc2ae131e4200aed82dd3624c0019bec6b8c64a80033718c714c9200072eb2e429806000ced815cb650c0011ff0cba264180032f1817418d52004bec28e0b184200e3d5458e41940018facaba26418003375cf63949200047ec34e39944000ced724ca6090401b9ae699042900032f5d7644c92100676392c4b0e6000e3d65591210c0011ff0eaa6c4980039d99561484300053ec2885b1260009dd83dd542cc40197acbba242180033e60176087300065fba2c690c4000c7c76195424c0018faca38a86190032f0c374586520057d404c4b046200cef73d89424c0015f500212c0188033b5da62c843000677bb284908602bd5f53dd5434c4015db05386c6a08027e6087050d300067bb8ce2b14a600e5d65dc16308401dccc530c4218002bb60b50189310066eb9a6430a40008ff8759721480011fd0e202c5188033d18c71509100053ec2cc790e2000cf4201c5644c801bb2e738042180031fd96718c9300056ec18ebb1a4200e5d658c943cc401c7aa8a1ac528003b3e0d624c81000677b9ac4a086000ef2768c620440019dac538c641800367dd253487300056ec18a03126200cdc865cc21540015bb0628ac790802bea0242583320063eb28e2a106000e75658c5210c0014ff0ab82c7908ab679537250d31006e6b9cc41086000dba745c021cc001a7ccbba2421800337dda704cb3100676b12e32106000dd5315ca43484011ff0eb2842900b7571d63258132004f7c12eaa1a6400cbc76d9253484011ff06b94c32810ba71d1634ca410066e406ec98862008fe86dcd54484014ff0abb042980023fa1c4158b30004dec26ec10e60008fd821d9315400137b09b984218003a7d0b6350d200066ebaee0b184200cbf435ca6190c015db05b2c65188023f61b74c87300047ec16e6b262000c7f759d563c84011ff04bb487080031fd9571909300047fc32e99944000d5d54dcd524c8019db0fb104298003b658f704ca200057ac0884b046200
  | 2 => 0xf640ca310062eb2ee690860008ff825ce60904013eb0638aa490802b7a1e634cb100066fb9ce6b148000cdf7358d21c40019dee8b126218002bd61832947100047f43eca9902000c7c65dcf214c001d9b04382c6108023f61f658ca200047ec16e6b2c20009be871d1214c0011fd0db8aa498003ab58a42904300072fa86c6a9a4200ed6811c1630840197ac8b8cc418002bbe19744cb20004bf43ca690ca000add8314763484019b8eca1a62900033be1d628c4300047ec30e2aa66000b79800c954544015f30c10c6018003795c962cc6310066eb9cc72144000cbd64dc1520840167f04aa287280031f59773508300047fc12e7b282000cbf65dd121480011fb0c38a84180038f59641903200075cb20e73004200aed87d8a424c0011fb0e31842900027760e70909320066eb9ac73064200e3f65906404c001b5ee9992c299002af2195450d300065e3b6c8a9a4200c7f65dd1314c001e3aa8a9c8398002ee610218c0300055ec20eab1e4200b3f8355152508012ff0ab806390803b3e09634ca51005ddc224298440009f9829c2314c001cdccb31442180033e18c70551200074e31a86a124000af88054c624c001dcce238ac4180031f195718c9300066eb9ac790e2000bd98308530480015df04b1a65208023fe1d4358a100063eb2ae91886000e3f65d92414c0011f90cb94a298003b3989434c4300057d430429824000ecd63cc932904019bee6b1a42080025fe157090d210067dbb2849806000dd7635ce51440018fea4b9eca9080277a187354932006eb190e2b226400cbc76dd1215408dabea6b94a719002afa0f65d912104e3ebb2a728e4222f57535c653484011fb0fa92c70800357cc575189430063eb2ee89086000aec864cb21480015db053a2c598003b39cf620853000677c16ec90860009fb805d532884019eeed18a42180032fdda64484300065fa12ed9948000cbf76591210c001c7ecb2148298002f960a708c5210066fb98c710a4000f655354921084011fd0e29ac3100032f611769083000756206c4a126000ced7458a210c001d6cc8b94c21800337dcd6358a40006aeb2ee4a1e6200af880585604c801bcae238a64900034f5d6740863000577416a8b146000d5d7394c21940013eb0f994a388003371cd63582420056ec1e85b1a400097d87108654c0015dd05a1ac598003375cc63909200065eb24e13184200ced7258a61cc04fcdccb21642180031f9da750853000577c12c731020009dd839ca404c0011fb05bb282180bb6b1937250d320056e41acb10a40008fd82dd93190001d74c9b9ac01080337d8e70cc9210055f43484a126000cfb709c1630840197ac8b8664108023fe1d62cc6500057ac364290e6000cee811d9324805dd58c999264908036bc817418d520066fb9ac6b102000b5d850c9434c4018f
  | 3 => 0x810e6000a7d8510963c40018fea63b2a890803ba58a424c0300057c402a8b166000cdf73d8d42440013f50d38484980365f61e51cc6500071ea1ecaa122000cbc7458921cc0011fd0c39aa490803735cd6208430005b741083b2a6000b3c8155143940019bee7b1e42a8002afe195450e20006ceba2e610e6000ee772589610c0019dec4b8664a08031f54d721855000676c3ac52086000ecf8258d328800197cc9b82c6108023fa1e63486500065fba4c690a4000eb5649c9610c001e5aa8a1243280023fa18704c9210056ec10c7192a000c7d75d88214c0015f5013b265280039d59472984300065f3a2c610a40009f88748530480015ed03b2265100035e5d570087300047fc12e6302a200cbf74589218c0011fd0c39262980023f61b73484300053fc32a8a9e4200afb854c960084013df04ba26218003ad194648c5210065e208ecaa26400cdd7358e6290001dab0a992c2190033eddb214c0300071eaa2a7b128000cdd7358e51c80013bd0e39a4218002bb61f6208530006ed402e610a4000ecd73588210c0019baed39842180031f5d9538ca510072e42ae0b184200ead64cc9320840197ae831842900032f59072584300047fc32e520e60008fe87143624c401cd8a1b12a4988033b9c962984300075620ec521260009bd841d8214c00197ae83184310002bba1b324c9212372fa9ecb1926400cbe751936048401978eca128298002bbe0964cca3100676b9ac59086000ead6498b210c001b3ee8a9a4298002bbe09648cb300065ebb4e810e60008fd8758a310c0019dae8b1262180039d99561084300067ab88e3b1aa400bad840c952480015db0c18aa590003375cf63085500072fb1ca6a9a4200de772dc5644c8019beecbaa65988027d61d62cc6310063fb2ae790a6000e3c6519153484011fd0c392a8980031f995739802100676b9ec510a60008fe8710763480011fb0fa12c788003571cd53549210053f4368432a60009ef8748421cc001f890299262900037adc3754c92000576c16e7b12a800cec7258931cc001cbacb3984218002b760e54d8d200047ec3e643028200cbc74995614c8011fb0c38aa5980023fa1f624c5300047ec3eca1086000e5f655cc214c0011fb0f994c320003b558e53484210055fc1aa8b148200c7f655d1314c0018f6ec3aa611000376601730852000766b126498ca000cec72589418c0018facab9462180039b59571588300076cb9ac73004200af5851c1610c8013db05b9aa919003b354d628ca310066e39ac6b004200cdd7650e320c0019f6c538042980031fd957488530006b7392a418ca0008fe87d9132040019bcecb9843980a6b760f654c9310072fa9aed29a4200e6d54589520c4015db05b2c64080033b98c72505200047ec38a1b1a42008ff8750f62540015bb0bb82c6108023f61
  | 4 => 0x48c801c7ecaa1480980038f59474484300056fc3262a184000e3d65990210c0019bae6b1043280023f6187054f210067ab18e2a1e42008fe8718d21540015db05b2c6520002b7e19754cb3100774b16431806000cbc75193634840197aecba043180023fa1871509300071ea1acaa1662009ed821c554480019dec7b9263100038fd976450930004dec20e4a8a60008fc865c6324c0014fd0c216ca980bbab1937259132004eec3ca610a6000ade83143614c80197ac8382a419003b9dc6715883020cef43864a1a6200afa8010960cc8019beedbaa65988033bdd1628c83000676c0ae4302a600aed8214163484019beed29a43980038f5536350d510063eb2ee4b086000c7d655ce210c001baae7994a288002b7e0d6598f2100577c1286b16602dd5f535d6324c80197aebb26c69080337dd3638c5200057640a86b106000c7c76197214c0018faea32ec6908033758f704c8210053ec2cec1086000c7d65dd2210c0011f90ea1ac5280fe7d61e538c5210066fbb24298060008ff874c860504011fb0e202c41880337dce63588100065f3b4e810a6000eac42d89424c001c7aa8b12a5208027de05744cb30004fc402ea9904200cef769c532c800197ae8b1043980036b5d321084300047ec3884b1e2000ee981589300c00137f08b8c65980027d608715532100676bb6421086000aed82d4d62840019d8c7b9282900034f197744853000576c26e2b1060008fd861c542cc00197ae93184310003375ce63c841000677b9ac49086000c7c501d9524c4019bee631a42a8003f8484214c1200077540ac51806000cef72989608c4013bb07ba04398003ab55174588300075ab22e4b086000c7f651c5434c0015db05a0ec4980033721d63548210066e432e610ca000ecf76549320c8011fb0c382a418802b7e0d65cc6200053fc2ae1b128600cfa765c0218c0018fecbb9a42980027760f72551320056ec06eab184200cbf649c253484013f30738482900032f5da64084300add6422e29924000add83086600c00197ae93184328003b958a61884300066fb98c6a0a40008fc8758931940015dd0c18ca490002be603631812100676b94c530e60008ff865ce420c0019daecb1642180032f5d96408430005ecc18a030264008ff8758c21940015f70e994c0108031fdd66558f210071eaa2c6a14a0009f4815d942cc0015f50020ec099002b7a0c5058d21006ceba4e61086000cbf645cc60484014f90ab82c790803375da53087300065fb2ae81944000af880595604c8013db0539ca390802b7e0d62cca400055fc328720c4000af48155163c84013eb0e194a3880033b5c96298231006ceba4a610a6000abf845c562cc0019dee9b1442980031f8857518d400071eb2ac81086000ade83d016388401d9eeca1a64190039b59721084300065fb2ae
  | 5 => 0x9803f44c5214c03000757324e2b106000cbf75d91324848d3bf06bac6499002be61f3298021005db408a03224200aef8258e32900019bacab9843180031f5d563085200053f430ca90a60009ed821c554c8001bcae690842900032f59373c843000676b946430aa0008fe87145628c0015b90ca1a62a8002afa18531912100737b28c510a6000abe8614364484015db0631664a08023f61d63c841000756b24e2b106000e77654c6214c001c7ecb21284980027760e7094b320065e3b2c8aa26400ead84589410c001bb300b984398003a7592324c8300066fbb2ea9906400cf781dd9210c05bcb8cb1926498002b761a634c8100066fb2ae610c6000afb8058e60084011ff06bb642080033ddc671d893000577c12a7b122000ee7621c5324c401abceab9843980023fa1f53586320057ac18c290a4000ec943589300c0018fecbb9a82980023fa1870509310063e3aac2b026400ced7298b30840019bae6990c0a0803a75927098c210065f3b6c929a4243e9f8359132cc48dcb8cab2c6499073671d2534853000775c22c498060009bd849cb614c00137b083926318002b760c5158c200066f3b464992a000ee68158a310c00197ee93a2c5980032fd0b76553300067cbb4e010e6000adf835962148001baaa6b8c65188032fd087650d20006dcba4e010a6000cec72589310c0017b30610e60980029f61441d8132004efc1ae890c6000c7d769d4218c0011fb0c382a6108032fddb7448530005cfc22431826000cef761c532c800197ae8b166328002bb60850d8532006bdb2ae520220008fe8714d6108001a7ae8a9065280025f21d544c6500063f32ee49886000eaf8458a410c0014fb0a212c018802af21d6448430004fa40ae89944000c7c659cb614c001cbaca90a6018003379da53085300076bc2a64b08640bc7f7654d5208401c7aa8b1aa5208039b61471588300047f43cc690c4000cf9639c02148001e3aa8a9a85980023fa18715492000766b1ac499020008fe87d8d52504014fb0b31a4388002bee19434c2200047fc12ed9802000c7c7558930840013f100baa64988039b99562884300072eb2a62a1e4000cbd645c6320c0018feca39262980039bd9542c85300047ec10ecaa26000abd841d56388001baae690843280036e551700ca410073bb2c4210a6000ecd43589310c001d72c839ac01080397d95434c5300066eb9ec410aa000aef87588210c00157f0ca1c8390002bb61b21884300075cb24e6b004200add83d9332040011ff06b94c120802f6e01658c9320057bc0ac530ca6008ff8755163c80013f100baa8699003b520163484210065eb22e12984200bac8250d428c0011fb0fb2c631000337dce634841000677c3ac4a086000af88059560c840173f0890e6018002bba1e624ca310066f432e610ca000c7f53dd95
  | 6 => 0x4fbc3a421086000aed82951620c401c7c80b2a8598802bb60b43d8930007cca1c829806000ee481589210c001cbea729ec498802af6107158830004fac3ca790c4200e5f658c5314c0015df04a1ac418002b7a1e634ca200067ac16ec9886200cbf641cd52484015f301194c120802bbe0963886500053ec28c5b028600a7f8558e21480018fecaba64298003b3209634c810004f7430e4a1a6400adf8358b32904015df04b1c4290002f6a02314c5300057a40acab0a6400cfa769c0214c001dcac490843280023de1d61185320047dc3ac03026400cec76909214c0019bce6b1ca390802bea07745803200767c1ae2b106000af48150b60484011fb0f298c4a18032fdd8744865000576c16cb108600097d821c554940013db0439aa9908032fd927018d210057b43cc29086000af586c85210c0536b90ab8264988029f61442583320055fc3286a144000ed63250d610c0015d902a1cc4180035e1d4724c2200047fc3ac518ca0008fc8758d5290401bcce290c409000337dd8214c0300057a40ac8b0a6422f545354d31484011fb0f190c2a0003755cd21084300047fc3ec790a4000daf7454921480011fb0eb1ca58800337dcd6354b100063fbb2a8a9662008fe861c9414c001bb500b9843980035d54c71549210057c402cab226400ed4634c6215400157b0829ec7908029f6144258d200066fb98c690c4000c7f7654d528c4018facbb82c610802bb219324852000676b90c430a600097f855c0314840197e81bb2a9990023fa1b7255130006f4990e090a4000cdf7358d52c8001d6a86a12c2180023fa18714c9200066eb98c790a4000cdc805cc61508019f2e0386c69080277a1b7250d3100756b22c59086000eae6458b210c001be262b948088002bde1d61185320057ac10c298a60009f6869c653484013f100baa64908036e5d170086300057bc0ac93026400bd4815d5324c45bb9b05b9aa499003b32097058c210047fc1ae43028200cbf431d9544c8019dce5b148098002bee013298321005ba40aa8a9e4200ed88058d60084018f8edb2c4298002afa0365d91210069ebaae810a6000c7d765d421cc0015bb0620ec099002bb60841d813200577c12c71902000bdb83486300c0019f30c382ca990025fe1d54cc6500076639ac490860008fe861c1524c46fae8cab9ca28800337dc07058c210063fb2ae3b126000af8805d563c84011fb0fb284318003b958931884300057a40ac830264008fe861c1434c8011fb0db9a84180031f1d761581320047fc3ac23026400aef8758a3294001cbaa8baac6108032f99170cc8210076631c849924000cde8758d5208443ce8cb90a42980037398f7354b200076bc02c69084200cbf761d1210c0015b900baac6108023fe1d63085201273732c849086000d3e759d0214c0019dae5314c32
  | 7 => 0xad62909420c00197aebb26649080397d4e7694d21006eab9c4210a6000ee48158a610c0015df04b1aa5880db6e191729011000766b126498c8000eaf84589420c001b3ce8b984398002d76147098c2100736b2a421086000cfb645c0328c4015db0531e43880027760c70509310fece3a2a690e6000add8718e31480011fd0d394a2980023f61c41d89300065fb20e0a9242009bf845cd21cc0011fb0eb1ca390802ebe117198830004eec38439806000aee86c84214c001baae730842180031fd4d72d9531005cec20429806000cdf739cd629440197883bb265200023fa1f4358a310074e326c729a4200e6c65d8a214c0013db0db9aa590003b560163884210071ea12a9b12a200c7f65dc9414c001b3cc9b9a42180033ba1d6250430004eec1ce128a6200cdc631c543480019eaed30e42180031f9db65909300076dc02c6b004200cde765cc210c001cf0ca382ca990031f08775582430066f406ec9906400d9d64dcd210c0019eee530a6218003b5cca614c650006dbba2c2908602eeae64cc93208401b3ee9b9a43180033ed95700ca41004dec18e0aa48200af6868c621480019eeed29a4210803679d273084300047e43ac6a904200ee562884210c001db286b126018003b958961884300057a40ac9b0a6400cbf75d93324840197ecbba243100023fa1b735491000756ba6c410a6000c7f76595210c001d5ac938cc418002b760c4258f10005dac0864aa28000c7e765d4214c0015df04b1ca520802b760c5158e100057741083b1a4000ecd628c5310c001d3cc6a1c82100032f9d0630852000676c26ec99064009ed82dcd544c849e9ea729c8490802bd61841d85320072eb28429806000afb864c63088001d5ac93124218002cf610329465000766b1cc49902000c7d651c543c80016f70ab9cc01088bd5d4e534c5210047ec1ced212a000cf8639c2514800197ae8b1042180023f21d54d89100047ec36e91886000c7f61dc95454c01978edba24398003375cd53189100047ec3e86b166027f4f5394e42c84011fb0fb2c65200023f61e4358a100047fc12ed98c8000c7d54dcd62940019bae731e43100031f5877255250007a6a9665194a0008fd87d8e51484011fd0c3828690802b760f6518d210057ac3ec330a6400dcd73cc82188001a78e9b2a4298003b3d8f324c9210073ab2ae53086000aed82d0d620c4011ff0eb14a398002f9205744c9200066e3b464992a000abd84143624c4011ff0fb1480980033b5d162c84300063e32ae690a6000f1d5454d434c0019eae730e4218002bb60873d89540067dbb2429806000cef745c5620c001af4eb38042980023f61d62cc6400067a190e2b2a8400abc84587604c8015eb02310c298002af610535863200576c16ca9902000afb80597644c8019bee631a42900023fa1f42582310
  | 8 => 0xc38aa8980031fd9671d89300065eba4c61086000cef8758a32040019d8e5b1282980029f61770d8d210066ebaac69904200de920dcd52440014ff0caa2a599003a7d8d43905200063eb2ae1990423eee7865492108401cdcebb104298003ad59321484300065eb26e2b106000aed82d96328c0011f90cb94629800337595730843000677b18e498c4000baf844862048001cb8cbb1aa690802ed2054250430005cec204398460009f4815d1328c0015df0c90842180033b1db324c9410067ab9cc390c80009bd84dd8210c0013bb0638aa5980039b19462509300055f424e0b146200cef621c1324c4019bae6b184310002b761c638c95000774b124318060008ff874c861500017c902ba265900031f5977150830005d6c10a1b2242008fd86dd132880018fccbb9a42180023f61c6308620004fcc18e090a4000edb639c231480018faed32e42180027760c7250530006f5990e0b2a6400e6d6598b210c001dcac5b8a65188023fa1b748c5200067dbb6e498440009ed821c1538840197aed3a043180039bd9762509300047ec3e65304a200de77298531880013bb06382a519003765c0704c931005dcc20431824000ee472589610c001d9cc6b1264080027e20176551320059fc2243282a0009df87487300c00197ce8b1043980033ddd96188430006afa9ee2b14a600ee9801c5620c0015eb0d18c431000337dcf6354520006d6ba2421086000ced76484210c0011fd0e212c690003a7d936354d21006afa98e4b0ca600d3f7454921940011fb0e20ac5980a797195324c5300065e322e118a4200cfb83dd91004001ceccbb92c218003c755143cc650004dfc22ec90e6000cf9629c251cc001dad00b1c42108032f595740873000736aa2c5194a000aec864c82148001b74e8b8043180037394f7250e320076641ac49902000ced7498a310c00197ae8b184328002af6105358a100069fb2ae810a6000e3f65d4f64484013db0539ca2908023fe1d6418132005ecc18a1b026400ead4210960cc8015ed0f30a4398002bb60a73588100063eb2ce21086000af980cca60084019eee730a42180033b5c9321814100577c22e2b106000a7e86194214c001baae6994a288002afe1171d8d5214eafa9ae529a6200e6d53d89524c4013bb0738c80980023fa187050d310061fb2ae810a6029e5f535896194c018fccab9e4218002af6107558c200063e3a8c8b026400cef72589410c001bb2e6b804218002bea0363d81210e6cf3a4a610a6000cad74588210c0015f501a12c0188035edd7714c2200063f3b6cb10a6000e6c50189524c4019bae7b1ec4aa002ab61071588300066fb9ac6b048400add86085300c00173d06286c8908033d5c47158b300047ec3a6530ca000c7d75590328c4014fb0a210c69010397d4f654c9310057740eecb106000e
  | 9 => 0x32581320047e432e890a6000cbf65dd1214c0011fb0fb2e64080027760c71551300072fa9ec729a4200e5f8558d53084019e8c438aa898803b398e624c81000772b146290860008fd878ca60904019f6ec10a60180032f19273d81210066fb18e29924000af48159161cc0019dac438a8418002bba0a54d89300067c318e0a924000cee72d88614c0017a902a1a63180033d5c47158a5315f2f32a869886000add83d9132040017b30610a61100b79719773595320047ec3c65304a2008fd879da53c840137b09b984398003375cd6398a51005bcc04a710ca000bd983905300c0011ff0e990c098803bacc932980210063e32ee299260009ec825d1310c0018f8a0bb4a790802fae09318c2200047e43ac690ca000e77658c5214c0015e902a12c1988027b60873551210055ec20eab1c2000cbd64dcd60084015f100b12c1188031f5d475d8d210053ec3aca1086000dcf62dc9434c40137d0e192a8a0002bbe09634ca40007cca1a849806000c7f65dc9434c0015df04b1cc528802b760e7558f210055f436a1b2242009f98758f2088001ceacab92c218002e760c50191210067c31ce010a4000c7f651c5424c0013bb06382a9990023f60a76945300077243ac4b086000e9e649c263084017d704a0c60900033be1d62904300053ec28c790c40008fd8798e4288001c7c81b2a8488003ab59262084300047ec36e6a0c4000ade83d436348401d588431a84900031f5d9650843000767c1ac499480008ff825cc61500011fd0f31a4320003675d1530873000577c12c89966000afb80595614c8015bf0cba2659880397d4d6394f2100576c16c6a9280008ff865cf210c0015b906b2ac7908033d5c471d89300071eb2ae81086000adf83589329000197aecba042180023fa1f4058e210056ec10c698aa000c7f655d2324c0018f8eca9aa498803371cd63583210055ec24c498420399ec86dcd5248001978edba24218003ad21172984300047e43aa9b1a2000cdd73cc86054401cbac729c43280f3979953150f200069eb2ae81086000cdd635ca53084015d90ea1ac4180023f6187050f210063eb2ae33106000abd86cca41900018fcedb2842980023f60f76484100065fb2ae81086000c7d65dc943cc4013bb0638a85980031f5947250c300066f39ec728a4200d5e655cc210c001dcf02b124218003b56047058c210053ec2884b166000cdf7394d62904019dee338ac4180038f54d6454b200075d320e6b004200cbd655d331880011fb063b282a80033759573086200063fb2ce3b226000cf472985310c053abea7baa64988039bd9542485300063e3b6caa0a6000ee962905300c001d3ec831ca6908034f5537254e41004be432ea10a6000c7d651c9610c0013bd0e10a6018002bb60b654ca400073ab2ce4b0860008fd861c5438c8011fd
  | 10 => 0x9844000e3e65593210c0019dae4310c0a1803b920562584300063e3aac29804000ced724c861540019f2c4382a5980026fe11718ca300066eb9cc610a4000e3e65993210c001dd2c410c6018002bd205635862000757426c4a126000c7f655d2314c0015f30c10a60180023fa1c5158e20006ed402e610c4000ee5635492108401fc240994a2880033d5d921087300057b408a1b1e4200cec72d89514c001978c8b9ec0908031f5da7508430005f4402e89924000e9c4118d434800197ec93866490802b76147058c210066fc3ac79948200dd7731c5644c8019dee5b1262a00033e60f7644010005f4402a91924000e3d5454d62904014fb0a326c09900337dcd62484300074fb1a86a124000cf576587210c001abaeab9843980027760e709493200677bb2e899064008fd839db21540011fd0c38a86980033d5c471588300055ec24e1b1a42009f7865c6328c401cdcca38cc4180033b5c962986530069f3aae81086000c7e76d95414c0019dee5b12a2980023f61f5258c200066ec32e610c4000cdf7558d32084018fce8328c498002bda0450586320063fb2ee890a60008fc865c24348401cdacb9926410803ad99261c8430006eab9ac21086000e5d8558d5208401d9f04b1a6520803755d4714c9310066fb9ec710a4000cf8321c1654c80197ac8b9a4218003b9d8a3188530006773b66499282009bf845d9210c001d5ae8a1ac4180027be1d21086300066eb9cc72084000adc835db21540015f50020cc6900031f1d5614c2200065eb22e131842008fd8710a63480019dee7b104298003b960562c84300072fa9ced29e4200cdd7358e61880011f90eb1a43100026f60c70551420063eb28e4a086000af781590604c8011fb0eb126408003ab99162484300047ec3ca6b1462008fd861c553c80018fb0abb4a610802bbe09634c81000773c0ac53086000d3d759d0214c001bd2e83826490002bb607745883000676b9ec410a6000cec765d132480019bae7b1c8490002af61050d8d210063eba8c610a4000d3f749452194001b98c6b9ca490002bd20564d8132006ecc02e610c4000aed8298e62040014fb0a31e4290003ab5933254b20004eec3ce610a6000a7d859d3624c00197ec9b9aa4880023f60c76549410047ec3eca1902000c7f535da329440157b0829ac690803ad190714c921006aec2ae610aa000e5d65dcd210c0018fea7bb2a990802bba0b5158a30006ed39ce01086000f2d5450d52480015bd0732ac7908025f61c32946500066fb2ae610a4026e6e6550b210c001db30f31cc0108033e5da70086300065fb26e0a9a4200cbc74d8d2148001bb2e738043980031f21676085300053fc32a8a946200af5868c5210c0019b8c7b928690003b3d8a324c93000676b92c518e6000cf983dd92008001c78cba98c89080357dd6
  | 11 => 0x940018fae8b2a65988033ea01760843000677396c5b0a6000dd7751c5324c40197ee8b1a4290003abd90625093000676b94c53046200af58198a61cc001e3aa8a1aa498803ad1d261487300075b324e53086000aee860c552480015db0531a4388003b9d95210852000773c3cc53086000aed829cd6294401ceacb18c4218002b760e614c22000576c16c6312a800cbd7650b32900019bf0eb1e64080031f143764ca510053ec288331a4000af9800ca609040197ae9b1842900033b5c9628c43000667b9ac49086000dd531dc943440019f064382caa18023fa1d6354a420047ec30e099462008fd839da51480015bb0d98a86100031f59471588300067740ae5b286000c7f655ca314c0018facab984218003b39cd6208430006dcaa4e01948200d9d745cc218c001c78cbba242980031f5977308430006dca1ae01948200c7f65dcd424c0012fd0e192a8a88023fe197390430005ae41acaa9e4200ee962509300c001e5aa8a92859900337e01731854200736b2ac59086000adc86486304c001e9eeaa9264190033758e7094c210056ec188431a4000d3d54dc953508018fecab96c8980031f595748c7200057c402c6b0042008fd86dcd54c800157b0c1948320002f660e614c2200055ec20a0b1e42009df865cc210c001db2e731cc010802b7e0d624ca410066eb9ec6312a800d5d545cc21940011fb0fb1ca7908033761f6394d21006ce3a6e69086000f1d5454d438c8011f90cb9ca2900033bdd3624c93000576c16c6a12a200bb984087308c001f1a869906520802f9e05744c9200076d39ac73004200aee8290d62940011fd0d3b242980a3a7991324c4300047f436e6a122000e5f659cc214c0011fb0f18cc01009bd3d4e5350b210056ec1ea8b1c4000e3e5159153c8001d5ce9b1042980032f5d964884300063ebaac410e60009f5821c5544c4015ef0e994c218003a7591324c43000576c10c790a8000dea329c241480019dae8b1462180031f58c7154a50006ae32ae610a6000cde865cc214c001af2eab8043180032f5937254f2000676b96c5b028644d9e54dc943cc40197e86b90c2aa002b7a19324c550005db408a63224200cbd74d8c21880015db0531cc5200036b5937354b20004dfc22e32966000a7d851d162c40018f8e832ec4980a7571d5754c93100676b90e4b1ca200cdd73cca6194001baae7994a388002b760f624c9400067a194e3b244000f2d5450d52c8001cdccbb8ac4180029f61776485300071eaa2c6a9c8200c7f65dc943440018facab8c64180031f59773c84300047ec3ec518aa000ced721c963040019bae6b1043180033bdd1624843000767298c49926200adc864c93154001cdacb38ac4180023fa1d63548210057dc02cbb0a6400cbf421d9544800197ee9b124298003376197308530004fc43a42
  | 12 => 0x802db6084119530006aeb2ee690860008fd878c86154001d6ac8b0e4218003b958921086300063eb2ee899060008ff825ce60944019dee4b12c3980032f5907054c210066fb98c6a12a0008fc8755163c8401cdf0ab12a418803b518e314852000736b2ce33106000e3d659d0210c0019df0eb146520003579d5730863000677b96c498aa000afa80d93604c8018faa9b92c728003abe11715883000774b16429806000c7f859d8214c0015bb07b2e65108031f994724c4300076d404c73004200eb964dce6008401b3ee839a42180576b1d1744c920004be43aa890ca0008fe8714163c84015db052a2c5188039b99771988300057ac364310e6000e7665586210c001cbacb384c6108026fa1c7448430004dec3cc81086000ead64589210c001cf2cb39ac010802af21943905200047ec36e910e6000aef865d1320c80197acaba042980031f5d975086300056ec3ec729a4200cbf76dd121cc089b3cc9b9287988023f61f648c810006d7392852026000abf84586604c8019df0eb104218002bb6084198d200047ec30e2a184000cf9629c021cc001cecca392c2180039b5966248430005ea40ae89926200cee7258a61cc001db2e7b04c099002b760c4198d200047fc3ac728e42009ef825d131cc001abaeb39842180034f5537250d52006dbb22e728a20008ff874ca608c401cdaa8b1265280031f1d865485300055fc32a920e6000e6d65c86210c0011ff0eb2e42980038fd925354d210071eb2ac91086000eae64588210c001cdecb908429800337dcf63505200077540ac49806000adf855c163084011ff0cbaa84990023fa1c4058e210066f402e630a8400d5e7354e51c8401d5ac8b104218002bea004258231005edc0a869806000bb984085300c0015f5013b26528802bba1e624ca100067cbb2e010e6000aed82953624c0018fceca9842a80023f61870552320063fbacebb1a4200d78741d53088001978edba24328003a75516350c200067cb80e1b128600af7815d162cc001b72e8b804298002dea0041195300056fc1ac518ca000cef815cb650c0011fd0db8a64980023f6187155320005bb40ca6a9a4200cdf865cc21880019becbb9a421800337a1973085500071eaa2c520ca000cdf7350d6294001c7acb3244218002bb6085358a10005edc1a431824000d9d749cc21cc0013ef02ba26518002bee0d52580210065eb2ae810a4000c7f75d91604c80197aed32442180027760c72547300065eb26e29906000ed7634c521540018facb39462180033bdcd62508300066fb9c86b1420009fa87085300c0019db0db928719003375cf32986400047ec16eca1c2000c3d65dd1210c00157b0829ec299002faa02714c9200066e3b2a690a60008fe87d9132480019dee4b1261080033d1ca614c6400053fc3eca10a6000ed53298531
  | 13 => 0x63fbaac2b026400c78651c1654c8178fceca9ca290803ab1d16248430004fc402ea9944200c7f659cb644c0011fb05bb2a998003735cd52085200047ec30e2a966400d5c7354d52884015db04202c4188029fa1770d8d210065ebb2c89086000cbf421d9544c00197ae4aa6c6a00023f61e329865020cee436e4a1a6200abd8414d618800137d0f992a8a00032f10676909300056fc02eab1842009ec825d941cc0019dce4b1481980033b5cb62901100057cc34631844000cdd7318e2154001d6cc930a42180023fa1c41d893000677ba6c410a6000cf5655c432040015df04a98c488003375cd3218540005f240ae89906400abc86552414c0019f2c6b8065208023fe1f62945300047f436e0a1a4200ecc6350932480019dce2b8ac4180031fd9774885300047f436e6a8a40008fe86dcd52480011ff0cb94a6108029f61a5354f210047ec3cc790a4000a7d851c16308401d3ac8b84c610802eb61331549200072eaa6c6a9a4200cdd7398e41c80019dee4b12c2180039b54c62549310067c188e0b2a64008ff825cf65484015ef04a1ac218002afe1161181320067d3b2e010a6000dad74188214c001d9aa631264980038fd9474485300047f438a0b0c6400aed82103624c001c7883b2ec8980033b188704c931006e2b9a4210a40009dd831c554cc80137b0839262980033b5cd62884300065fbb2c99086000eeb629c0214c0011ff06b96c8080033e5d963c82200066eb9a64302a200cbf7418d21540014fb0a212c1188023f61f62901301173a32a6290a6000cdf85dd9320c83fb3ce8a984398002b760f4118d200075d324e6b004200a7d8518d21880018fecbba46498002d760c411953000775c32649042000cdd764c643080019bf0cb9842a80033ba0976c8430006ea992e2194a000cdd734c861540019dee8b1442180023f60f72593100063eb2ee6a166200ade8798d32944019deed31242180023fa1c764ca510065ebb4e81086000ee781589610c0018fecaba264980027be0973904200063fa90ecaa26400cdd7418d32480018fc43baac1218023fa1c41583320067db24e01946200cf7655c432900011fb043b286a80023f61b725533100737328e2b106000cdf73d8d2150001ba86438ac8990033b5d1628c8300047f43ea5b1a4200ecd624cb319400157f0caa483100029fe157058c2100577c1286b142000dad74c8421cc001dcae5314c218002f6e11314c0300057cc1ced1022000e5d658c9320c0018fecab9c4298002eb20943509300047fc12e730ca0008fd861c152cc4015df0eb1642180023f61e61181320077243cc53086000eb9645cd6008401dc90eb14c218002bd61e329843000576c16ca99460008fe871456308001dd708992c0190035e19670c8530004efc1ae52086000cdf764c543c80016e902aa2a698
  | 14 => 0xd86dd732084013bb07baa84988023f61e639092009ddc422429824000e79659c0210c0015db03bb2c4180032f5907054b3100576c14a8b162000a7c8155163940019bb00b9ec8108032f9d464d8d21004dfc22e23126000adf835db21540015bb06282c3190033b5c962cc65000736328c410a6000c7f75d85604c83175d0998aa4900033dddb21484300067ab28e2b226400cdf7558f3208401a7aa9b9a85280023f21d5458b3000775430e09924000e6f53d89524c401c7aa8b1285280038f1934219530004eec18e2a146000a7d851d1628c401b38e839a43180038f996644843013f3632c8590a60008fd8710a63c40017d100aa264900032f0c174189510071f32ac89086000aef8258d5290401b98e499262180032fd9170cc9210076641ac4994a000e6d65988210c0011ff0eb2842980033bdca7258c10006edb9ee0b2a6400d3e759d0210c0015d90cb8a6490002ee20154905200067db84e0b1e4200add83d8932540019bae6b1ca520803375cf63c85200065fbb6e890ca0008ff874c8605440175f08b8a64900027de1d21086500073ab2ee53086000a7d869d4210c0011fb0e286c7908032f5d76418d21006bdb28e0b2a6400cbd641c132084013db0c3926310002f6611314c030005edc02ea9926200c7d74d9532440011fb0db9a43200033718c724c550006ebb9ee2b226400cbc415da42cc0015dd0420ec0990027b60a71901200055e40286b148200ed7864c931c40015db05a1ac59808f9b99542484300072fb28c6a9a42009ef825d941cc0011fb0fb2e4398003735cd32905200067cb2ae01948200e3d6454d52084013eb0638a8598802bde0564d81320047f43880b106200be8824c630880015bf0eb1e65208037318b7250d31004f743862a924000d3e74d94214c0011ff06b96cb20002bda0762d853000757a1ec4a1260009ed821c1548c80157b093aec6908027760c70551320065f322e131842008fd87d9532900011fb0e28ec6908025f60a7194d5300576c34e29964000cdd7418e314800197908b94c3200029fe095458e50006f4c10e0b2a6400cdf73d8d21880011fb0e21ac5188032fd917018d21004eec18e0a9262009fa869c0214c0011fb05bb2a9988034f5d1530855000736baec410a6000af681197614c8019b8e6b1aa4108032fd9574cc620004f6c10e2a1e64009df874c832940015eb0530e43200023fe1d6394f2100676312e19928200a7d8518d21480015ed03b26c298002afe195450f200047ec38a1b0a6400e7565c85210c0015bb073166108002bba084058b300047ec3ac528e6046ecf86549320c80157b0829ac2100023f61f5358a100aed63a26490a40009bf8755032904011fd0c38a64980023f61a729073000576c1686b146200af5810ca61940013bb07ba043180031f597715883000
  | 15 => 0x2ba264980034f5d57408430006bdaa0e0b2a64008fd87d9431880018f8cab96c298002bb60863485400047f436e6a0a4000cdd73d8e51480019bec638a8690003375cf6390550005774364310a6000bd880596324c8013db0438aa690003755cd32947100047ec1eecaa64200cfb76dcd6008401daa6430a629800397596214c03000577c0ae8b106000e6f65d88214c0014fb0a3184310002d760c219415000676318e4a0a40008fe86dc943440015ed02286c299003375cf63d81210047fc12e7b2c82008ff8758f21900011fb0e28ac7080036b5d1320852000756b22a599042008fe8798d21040019beec98a86100023fa1e4358a50004eec18e0aa26200c7f65dcd42440015db04318c4aa0026fe1173486300047fc32e89086000ced7690b210c00197ee931a4328003375cd3298650004fcc10e098a60008fd82dd930040015db04286c4988023f60a768c550006e6b9a6520e4000e79651cd60084011fb0dba043980032f9d363085200065fba0c690c40008fe87d4963c8401d6ac898a4218003375cf32986200047fc32e121e4200e9c6418d5348401cdacab124218002bb2094358b300047ec30e0aa664008fe87d4d61880011fd0c38aa8900023f61e63c843000577c12c7214a0008fd821d9544c4013df04ba462900033bdd9744cb200bd76c16cb1924000cbe645ca610c0019becab9843100033b1d9424853000676b946430a8000d3d7454b319400137b093b242980023fe1d32986400066e31ae518a4000ecd831c5620c0019bce6b104328002b760c50d8f21004fc432e52022000afb864c53088001bd465384a2900032fdd874486300067d988e0b2a64008fd87d92324c0015eb0c208c2990033758c7054821006f4994e120a40008fd821d94154001b3ce8b9843180027ee1d60181320076bb18e29924200a7885580604c8015ed02282c690803755cd21087300067a3b46290a6000c7d655cd210c0013ef0eb08c299002af2195450d32006dcba4e01086000bbb84486300c047e9ea729a84908023f60b764c43000767b126498a6000af983dd960084019daed310421800337dcf63485200067ab14e2194a0009f78748421cc001da900b1c4210803b961d629843000676c3ec521260009ee870c552c80018fcedb2e42980034f5d253086500057b408a6b0c6400ece5358a328c4019beed10a60180039714f6354d210071eaa6c6a1aa400c7c855ce60084017d50038a6490003cb55152509210055e43286a1240008fd87cc86054401ceacb30e42180032fd9370549210055fc32a8a166000dad74988210c0011fb0fb2064080032fd9574086300066f39ec7b024200ecc8358932900018facbba042180032f59273980210071fbaaa9b128600aef82590328c4015db05a1ac58800375dc5744c9310056f418a1b1262008f
  | 16 => 0x45092000756c22c52106000aed8294f624c401c7ccb32042180023f61e63c86200047f43eca90e6000af5844c9610c0015eb03194c3980033b597724c6200056fc1ac418ca0009ed821c553c8001b68c8b9ca2880031fd9771509300071f32ac81086000a7d85d0163884019bae7b1042980032f21172185430065e322e1b1a4200dd9735c021cc00197eeca128218002bbe0943d895100577c12e8b1660008fd87d9732484015d90c9944290002af6135158e200072fa96c6a9a4200cdf835d932900015db0431a84880023f61c4198d200047f438c2b0264008fe86dd0214c0015f100a9ac3900027b60870551210063fbb2a6994a200cde73d8c60484015f501a12c118803ae99173580210076bc02c710842009ef825d231c8001dd2c490a6018003375cd32986400055fc32a92086000d9f7494d214c0013f30f19481080027de057650b300047ec38c610aa000aef8259262cc0019dac7b9263100029fe195454e310047fc3ec728a42009ed829c6438c801cbaa6298c498803b9588714ca31004bec2ce7b024200cbf65dd121cc001d9b05b1a64908039bd9462909300063eb2ee6b004239e6f52d9632480017730810a6090002bbe0953d89410067cbb4e01086000d5c7354d5208401b3ce9398439800397595324c430004f6c14e32064000e6e655c5620c0018fecb3884298002be60263980210063e284ed29a4200ee581588210c0019eae238ac7100023f61e5398a410066ebaac79904200cbe64dcd60084019bee6a9ac5880039e59773580210057d40083b126000a7d8510b63480019bec6382a690803375cc63181210047ec36e918c40008fe8794f6250c0197ac9b92a6108033bdca72d8d540067b40aec1086000abe86d4c64484016bb06216ca980023f60e76c8520004fcc1ce128a4000e6d65885210c00179b0610c40900029f6146308520007e898c429806000dba745c0214c0015790caa284980039d59672984300063fbb2ca10860008ff8750d620c0011fb0fb2a6520802af610219803000737b2a4210a6000cf7651c5644c8019eeec98a43280032f213764843000772b92c53086000aed82d01628c4015bb07a14c7880025fe1d548ca500047ec3ecb1948200cdd86dcd210c0014fb0b38ec498003ab5917198830004bec3ca610ca000c7d76596210c0017730810c61100036d1927194d2100677bb2c49086000cdc80dd9320c8018faecba842180037ad8972901100056ec1ecb99020009ed829c6538c8015db05b1c64080031f597714c8300047f430e0aa264009f7825db318c4019dd0eb1262180023fa1f654c620006aeb9aa410ca0008fe8718d214800197ee831a42900023fa1c50d8d21005afc2ae099262008fe87d9532900019d903bb24010003a7a107058c210055fc32a8a1440008fe86dc954440013e90
  | 17 => 0x106000be88054a32480018fccbb92c2180033edd9414c0300047fc1ae5b2c8200bad8214f64484011fb0db92a610803b621d63580210047f430ed29a4200ced75d89324c401b5ae8b104218002bda0764d85200063fb2ce430a6000cfb709c363484013bb0638285988027ea1c214c1200d5dc4224398260008fd87103624c0015bb07a92c7100027b60c72505200067ab2ae21948000bad841c5620c00197ec8b84a690802de61473580210076db9ac6b004200cbd74d8c21540019dac5b8a84180265f61e51c86500067db1ce010a40008ff825cc61540015790caa48290003b9e1d6258430006afb9aa690aa000adf8359531900015bb07aa6c6908032fd9373549210067dbb4429806000de930dcd52480015db05b20c4980023f21d614c220007b2a924210ca000cdd7398e62944015bd06282c790802fa201714c920005f5c12629844000cec72589610c0015db0d2164218002b760f64cca210055fc22c3b026400cbe30dd16194801d3cc8b84c6108039b5956208430005da40a84a0e6000cf582dd910040019dee4b126320003b92056288430006af39aa728a42008fe8794d62904013bb06392a9980031fd947250d300056ec18a4b1c4000ead74588210c0019e8e2b0a6010002b760f654ca21004fbc3a4210aa000cec72d8931540019eac4b8865280033b9c9628c7300057740ee8b106000abd8418f61548017d704a0a60900038f5964150430006ecb9ce010c60008fc87553624c001baae710842180023f61c5058f210047ec3ec528a6000d78651c1654c801d6cec32462908023f21d54d89310047f43ec498aa000c7c76d95424c0019bacb3984310003b9605624c43000577c12c721240008fd86dd231c80015ef02b14c3980032f5d5644cb20005dcc006520c8000eb564585210c0015eb0d29a4210803ab55362509300057cc04c73064200c7e76195214c0015eb0d90c42180023f61e6308620004dec3ac810860008fe8718d21500011fb0f3b485980023f61e63c865000576c16c6992a200bac8259142cc001baae690842a8003f44c532901100b6b73aa6410a40009bd84dcc218c001d68e930a42180023fa1f5258e100047f43ea2b1c4000cbf435cb644c0018facab84c6108032f9d97408730005dc402a920e60009f9821c153c8001978c9b8264908033bdda21484300066fb9cc6b0c40008fe8714763484015f501216c0990033dddb7258430004f7c12e720c4000abf84585300800197ee8b1243980034fdd774486500047ec30e4a0e6000e3f655d0214c0018f0ca38264980023f61f65cca400063f3b6cb20a6000db9439c032904014fd0da08ca980033be09764ca40005da40ac8aa26400dad7448421cc00197ee931a43100023fa1871549320067a38ac29844000c7f655c4624c0011fd0c38aa899002ee2015
  | 18 => 0xc0012fb0f194a3280039d59661484300065eba2c410ca000eb4648c76048401cdceab1042180023f61a70948310066fb9ac6a904200ee962085300c0019dae9b8ac4180033d1887150d310053f43685b2a6000dd761dc9434c4013bd0f2928698802bb60b53d89310065fbaac89964000abd84140624c401cf6ca286c099002af610764c8100063fa98eca9262008fd861c5544c8015f700b2cc299002afe11715883000576c10a1b1a4200d5f7394d21940019bee7b1aa490003b3dcd6248430004df43ac89086000bcf825d1324c4011ff06bb4a3900037594d718ca310047ec38a03126200c7f651c9414c0019ef05bb262188031fd95718c9300066eb1ee0a984200eb46418e3148401a78ea3a243280038f55153d8943004f6c10e0aa64200c7c7654d21540013f100bb2a790802b7a0e5458e210066eb9a65306420097f855c332884019eacbb8ac899002bea0061d81320053fc32a8a9662008fd87d4963c84018fd0a3b2a89900397d4e5318931006e7b12e521a6200cbc845ca6190c0175b04298c890802abe1171588300053ec2883b126000af880597644c8013d304382a790002bbe09650853000762b1aa49084200e7a655ce60084015bb0738ec4980023f61f654c9210057bc3ac31884000afa8010563480015eb03314c218003769ce700873000767418e2b1060009ec825d131cc001be240b9ca2880031fdd965c84300063ebaec610a4000e6f54d89524c401b9ec6b9ca4900037a5ca329021000577c12c73148000add83107624c001d9f04b82c6108031f597748c43000677bb0e2b106000a7e86107654c001dcd02b164218003375ce63983210066fb18e09924200aed82107624c0019db0eb1282180029f614764c81000576c10a0b1e42009ef87484214c0019daecb104218002f5205744cb31004f6c38632924000d3d7494731940019bac738664108038f99474484300047ec36e99086000e3d54d8d42544019deebb1264988027760c715513200772c3ac4b086000deb80dcd52480015bd06286c6908036b5d332086200073632ec5212602bb5e850c9434c4019becab9842980023f61f64cc8100066fb1ee4a1a40008fd869c2328c4018fea3bb2a919002bee0165185320047ec38c790a4000d5d755cc218c0019bee7b1aa4a0002f9205324852000756b24c51086000eaf745d1620c0019bce6b1cc1908029f61476484300073ab2ac390860008fd861c154cc4013f30f90e6118002b7a027058c21004f6c10e0aa26400af783509610c0018fb0a3b2a899003335cf6208530004dec38a03224200cef825d93294401e3aa8a9c8298002b7a0c65d8d210047f43ecab2264008fe869d9544c8019dae4b106328003735cf62085300063e280ecaa26200c7c65dc9314c0019bb0cb98432800397d8d53549210057641286b
  | 19 => 0x3abd93324c921005f240aa490a4000d3d759d0210c0015eb02212c7880032fddb7448430006e6b9a6528a4000e9d841c163084018fea6bb4a7908031fd9574185300056f418a031262009dd83dd0214c001cbacb90e60180031fd96728c530006ecc06e690c6000cef725894194077adea9b9aa5900029f6144158d200056fc1a4330060009f8805d5328c401abaeb39843980031f59574484300063eb2ae53086000d5d549cc21940019eacb3886510002ee2015450b300076cc04c73004200eaf62509414c001dcf02b1442180039758e5354c210065fa12ed2166000d3e755d021cc0019eeed30a421800397d8d53945210074eb22e0b1842008fd87d0b604c80197ee9322c0990037a4ca709452000576c16c91946000cde769cc218c0019dee6b1642180023fe0d764c8100076d39cc73004200add8310b6348001bd6e5b82ca990029f6174058a310065fba2c49086000ced7258b3190001d5ca9b128498003b6d8c704c920007663b6e69924015dae744c821480014fb02320ca980033b5c93218540006ceba4e610c60008ff874ca60944018bacab98421800337dd57058c21006afa9ee4b0ca600e79655cd60084015db04202c518802f66003250d3100677392c51886000afa86c8630480019dae4b166108002f6e0d218c2200b576c16ca9924000fcb731c132480015bd0e382c6108031f99571988300057a40ac99926400cdd7390f6254401e9aa49906528002cf2015454a410066fb1ee4a9a42009f586dc5328c4019ef0cb8865280027760c70548320066e31ae3192a000cbc74195614c80197e843b2a899002afe1954508300067cb1ce01948200e5f658c9324c0011f90cb948298003675d1730853000774b14431806000c7f65dcf214c0015bb07baec690802ee61021cc1300065eb26e09904200dcf734c921480011ff0cb9c8310003375d973087300047ec3a6430aa000a7f8655153084013f307384a3980027760e7094731006ebc0ee4a1a6200aef8258e3294401d9286992c01910a7761e3290d310055ec26a2b146000a7d82190654c001e3aa8a9a86988023f61f32986200063ec2aec10860008fd874c86150001c7acbba242180032f5537258e41006bcbaae010a6000cb4641c5644c80137f08b8c6498003ae5917398021006db2a0e2b226400a7e869d4214c001978ec3a24298003375cc7358a510047ec16eca0e6000cbd74d8821540019dac4b8c641800337d977348630005dac20e4b086000a7d8218650540019bae6b1842900031f5d965484300057c40a86b006400e9d5458f329040197ae83a6c4980033b1c962504301273632c8490a60009f9839c021480011fb0f194c32005f5bd537354920004bfc3aa990ca000eb564584210c001d9ac499663200031f9d953c85500074e20ec6a1a4000dcf73989210
  | 20 => 0x7fc1aed90c8000bd481553324c4018fac6b94a3280032fdd163486500047f430e0aa26200cbd64dc9310c0015bb06282c6908033ddc671588300057bc32421086000ecc634c821480015bb07b2a6408003ab59162884300047ec388231a4000afa86087304c0019eecab8864080026fe1d54cca410047ec38a2b1c4000eae6458a210c001b7708b806520802be20165d8532004f643a64a0a4000c7d65dd3210c0015f102aa2c019002bba084198d200078eaa2a6a126000e6f53189524c4014bf0ab82c610803375cc6308550004fcc3c652022000dad54dc9438c871cdea5b2a6490002b760e71d89500047fc32e728e4000cf576484210c0019bae631ec2a90034fd9774485300074fc22c6a184000cdf73d8d21540011fb0f31660080023fa1c764ca400047ec18ecaa24200ade8618d53484018feed32a4218002fa209418c1200047fc1ae5304a200be8805d53248001bb100b984318002bd60432982510057b408a7b0a6400d7b751c930880011fb0fa1ac418803c7d4c6494d21006d6ba64210c6000ced7654b32084018f8cab9e4298002bd61a318843000772b14631086000cbe76d9153484015f100b2ac119002b760c4158d2009ddd420429824000cef825d93284001e5aa8a9a8590803379d97308530005cfc22429806000cdd7350f62544019bce6b1ca520802bda0765d85320065eba0c9b126000cdd85dd9320c8011fd0c382a690802af219545092000676b9ac41086000e9d64dc263084015bb06286c2990033761b7354b320072eb2ae13184200cec811d9324800187ecbba242980023f61a7294730006ed406e690c6000af787d8a3144001dcd0f314c2180027760e72903300047ec3880b146200aed82140624c4012ff0ea946328002bd20154584320066eb9a6530c4000af88054c62440015f30029ac5080032f597744873000775b12e010a6000cec87589310c00197ac839ac0108033bdcd62084300074eb24e0b184200cee81dd920080019bee631e42a80031fd9573085300073bb2c6310a6000aed82d8d32040011fb0d39042180033b20572181530065e20aed99480009f5831c542440011fb0e194c120802b7e19754c832004fdc32e199440008fd86dcd42840013db0538ca6990033dd9771591320047f438c8b0264009f98790b308c0011fd0fa12c018802be20165585320071eb2a84a086000afb87d8e20440011ff0eaa2c5988033d8c871591320066fc32e610ca0008fe869ca314c001bd064382ca990023f61870553210065eb2ae810c6000abe8614f64484011fd0eb1a4320002af6137158e200047ec386530ca000a7d859db210c001cdd0a38ac41800376dcc70595320057cc04e5b1aa800e5f755d563084011fd0e282c6908027761e73084300063fb2ee610a60008fe87d9532904013ef02ba264980
  | 21 => 0x87d8d52440018fcca392c2180032f99073580210066fb9a86b142000e79655c0210c0019eeec98a42180025fe15739802100576c16c69928200b3c805515250801cdccb31642180029fa167158e200069eb2ee890860009be87991210c0011fb073b042a80023fe0d72986400067ab2ae219440009ed82dd153480013f30738043980031fd9672d85300072f32ce0b184200cf576984210c0017d100baa65900037a4ca70085200057d40085b0264008fd86dce210c0015f30018cc1908033bddb744c8320056ec34e09966200d75549c43294001dad0c38a6498802bb2192108530004fdc02ea9964200c7f65dd1324c0019bae6b1cc0108023fe19758ca3100576c16a8b142000cfb709c1628c4013db05384a390802bea0365d81320071e320cb20a6000cfb645c032040015f30d18a6110002b760f41d8d200056ec1ea1b1a4200db574984210c001cb8a3b1aa690802bb60a531893100676b28e498c4000cec76dd132480019eee730a4310002bea0041583320074fb26c729a4200cbd54dcd62904018f8edb2e4298002bb61a42484300047ec3e8531e2000f2d5454d42484015db04202c588002bda0653d85320066eb9cc73048400bd48150f324c401b9ee6b1242180032fdd95450f200057d406cbb024200cbc845ca610c0011ff0eb28c299002b720d65c8520005da422c230a6400af481591604c80197cecba042180033b61d628c43000676ba8c49926200cdd74d8d3248001bd6e838264900023f60c76551200055e422c2b0264008fe87d45628c001d5ce8b104218107a795163cca410063e32ee690a6000cf57688421cc0019beedbaa6419002eee11218c1200056ec1ea8b184000b3f825515350c01978ea320c690802976147058c210047ec3ec610c4000cdd7358e42880018facb39482180033bdd8714c832005bcc28e73004200cdd865cc2154041b38e929a43980033b58c724c6200056f41880b1c4200e6d655c6620c0019dee4b126008002bb60a4358a100065fb2ee89086000e6f65c86214c0012fb0e32842980023f21d624c6400047ec36e4a9e2000cbd545cf62500015eb0530a63200039d59531484300072fc2ae0b184200b9f84487308c0011fb0f31e43200032f9da74087300063e3acc8b026400bb7845ca610c0011ff06bb4a588003b5d8e31485200057ac0cc530ca600cbf76551438805bab8cbb9aa4990032bdd162484300071fb2ce810a6000aed821056348001ceacb30842180023fe1d5458b30005b74108232a60008fd8718e42540011ff0e994c3100023f61d32181410073ab2a421086000abd8414f624c4013bb0db9a4218002bb6084058b3005cbfc3aa410ca0008fd83dd9544c8019eeec392c218003b998a61c8430006e6b9a6528e4000f2d5454a414800137f0cba04218003375cc7358a40004
  | 22 => 0xb1460180033bd97724c6200076c43ac73004200cdf659cc218800197aeab226410802bd60673d89540063f3a0cbb0a6000cbd655d0210c00157900aa2c520802b7e0d658ca200063e328e498a6000db7641c5644c80179f06baa64900039b59642c84300066eb98c610c4000a7d8510560cc801baae690843180033edc270d89430047fc3a653048200e7765c85214c0017d100a904290002bea004118d20004fcc18e0a9240009ed82dd153c800175904a1a8418002af61065585320047e43ac6a948400e76655c9610c0019bae6b1cc1210032f5d163086200047ec38a4b1c4000af986c86300c0019bae639ec4aa0027760c71509300057ac0c653086000ed7634c621540019dae5b16c2980023f61f6508730006f4b94652022000cbf42dd954cc8011fb0f3166108002b7e0d65ccb210063fba8c2b026400cbe64dc132084019df023b264900027de1d21086300055ec348520860008fc8758d2190001dd102992c0190033bd88714c9301373632a8590a6000d9d7494c21cc0011fd0f31a43880023fe19744c4300063ebb4ca1086013fa84250930480017b30610c60180029f6147458b300078eaa286a966200adf8355363480012ff0ab8665908037a5c9329021000676b9465304a2009dd831c552cc8011fb0c382a5990023f61870550320047ec30e2aa46400ced72d8a404c0019eb0c38ac8990037a4c9700ca41004f743a64a0a4000d6d754c821480015df04aa6c498802bb61a714c8320069f32ae81086000cf7201c5644c8019bae9b1c62900032f61076551320072f32ae0b184200cdd63dc152084015bb07b2265108af97195434c5300057b40ca6b0c6400a7e8694d53484018f8a03b2a8990029f2195454d32004f6c14e321a6400cdf7398d62900014fd04320ca98002fa209314c220004fbc3aa518a42008fc875853008001e5aa8a948390002f6201754c9310047ec38a2b1e4200a7c86551524c8014fd0c210ca980032fdd26348430006afb2ee6a926400ced74d88214c0015bd0e31a6490002bb60b648ca31006e6312e521a6200e76659c9610c0019f2ecb8042180b757d537354932005f3c0ac99926400aed82d4c624c4011ff0cb8ca5980032f1d87448550006e6b16e4a1e6200cbc7619153484017d100a92649000337e0d764c81000773394c53086000b748154921940013df04ba263180038f59543904300066fb18e498aa000ced7218b6050c0157b0c3a242180f7b6e19434c0300066eb1ae19904200af681995614c801b9ce6a904290002bbe0943d89100056f406ecb184200db9745c0210c001bb700b984318003ab5526290430006cfba2a690e6000abd84dc7624c0013ab0638a85988023fe19754c821005ba40aa990ca000e7565585210c00157f0caa286100023fe1973484300065eb2ee8b0a64008fc
  | 23 => 0x50f310047fc12ed28e6000cdd83dd9544c8017cd02192a490002bea03658ca310057c402cbb026400c7d75d90328c4019d8ecb8a6490003a79917058c21005dcc20429844000afb8058e609080179f06baa65900032f1d2634871000677ba8c49926200cdd765cc218c0015f30d2126018002de21560181320047ec3cc790e2000af68114d61080018fea7bb265288023f61c4058b100066eb9cc73148000aed82d91328c0011fb0fa9ec2990033b207764c8320063eb2ae81086000cbc7519360484357750810e60980023f61c63c85400056ec1e84b1e2000bad841c6620c0015db0420ac199003b65cf638811000772b14c39086000d78659c2424c0012ff0eaa065280031fdd661581320065fa16ec9948000d3c74195214c0011f90ea1ec4880023fe1d62903300055f430a032242008ff865cf21900018fecab9a42980031f19571d89300055ec20a6b1e4200af9800ca619000157f0caa28599003cb5515250920005cec18a1b224200cef74588210c001cbd0bb1aa690802b760f5258f210066eb2ee690c6000af980cca60c84018fccab8c6418002b760c41583320047fc3aa9b1a4200ed56354d21084011fb0e20ec0990032f59173c84300053fc32a8a906200c7f65dd0214c0019daeca164218003b518e31885200053ec28c790a8000c7c76d94214c0019eeeca9a42108026f61072547300069f3ace810e6000cde631c152084018fecab8ec8980023fa1c42580310065e20eecaa66000aed849c5620c0016f30a10a60900032fd97745853200677b14e32126000cbc411d94348001aef0ab8865280033ed88704c93000756a1ec4a126000cdd7318c21480015bf06baac7908033ddce61c84300065e3a4c690a40008fd861c543c80019f4e6b9cc010803baa0532580320077343ac53086006cbd7690640cc001c7aa9b1aa6a1002fa6085018132004dec20e498860009df835d1210c0014fb0a216c0990033bdca624c010006cf3a2e610a60008fe87d95210c001cf6cb3804298002bda0453586200067d994e1b2c6200aef8258d42940019f4ed38043980031fdd1654cb31004dfc22e690a6000ee984589300c0017770890a6018003b58c9329843000677b9ec510a6000cfb761cd60084015ed0331ac3100032f5917294c2100577c12c6994a2008fe86dc9434c4015bb07aa2c7080027761e53087300066f432e610a4000e6d6598a210c0015bd0e31a869000337e1973084300066eb9cc610ca000cf776585210c001dcac590a4218002bb61a624c8100047f436e4aa26200add83d8b320400167902aa2a6a1803aba10715883000676392c4b0ca600cdf635ca3148001cf2a8a9ac0108027761b7250f310047ec30e0aa26400abd84197614c8019dec4382a4988023fa1d624c6400065fba6c690c4000ced73d8a424c001dd102
  | 24 => 0x86000ee67258a610c00197acbba24290003a75536350d2000576c10a7b1262008fe8798d210c00197ae931842900031f59671908300077340cc53086000e5f654c9314c0015db05b2e4218003a75907098c210065fb22e7b024200aed8210463480011fb0c3928218002be61071580320053ec28c710a40008fd87cc86048401dccc530a4218002bba1e624c8100047fc3a6430aa0008fd87d97210c001fc240a9462880033e5c07058a310455fc32872086000ead5458a410c0011fb0dba44218002be20543980320063fb2ae9b0a6000d3d755d021cc0019eaecb0842180023fa1b73551100056ec1ca8b1e2000e3d6550d420c0019f10cb8065208023fe1d639092000677b96c498a600097c8754931940015bd0f31a64080023fa1873551210063eb28e6b004200af58398521880019eee338ac71000277e1d21cc2300065eb26e69086000cbd76993210c0011fb063b2a4880039bd976288530006daba2c21086000cf7659c432880015bb07b2e65100038f5516350e5000756422e2b106000ee681588210c0011ff0eb106328002b76167058c210056f41ea9b1a4200cde80dd9310c40197ee9b1a4290002bba1c624c9310071eaa6c6a928000afa80d97604c401b5ae89084318003ab99071588300066fba0c69924000c7e76d95424c0015db05a9cc508002ee2014390530004fcc18e0aa24000e9e64dc263084019dee5392c7200023f61f65cc620004dec3ce810a6000dd9735c0218c0019eee338ac5980027760c71549300066eb9ac410e6000add83d4b634840197eeab2264108031fd4973982520073732ce2b10602de5e658c9320c001b72e938043980032fdd95450c200071e320caa126000dcd63dcd52c80018fcecba84398003379c17058c210047ec36e2a966000e9e649c163084018fecbb8a64980023f61e63084300ad76c16c89924000a7d8510463480018facab9c84180023f6187355321005cec204318260008fe861da424c0019dee931462180031f99773c84300053fc2ae0b1c8400cee8758a410c001cdaeab104218002f9e0152484210047ec34e321c4000ee9629c0210c0015ed033b265208033b5d171588300065ebb2c99086000cdd7398c2188001cbaca90e601800337e0d764ca510047ec3ea5b1a4200e7565584210c0011fb07b92cb080037a1897290110004eec18e0a966200d75545c43294001cdeca31284980023f61c32986400053e432a8a9a6200cbf649cf604840197ecaba04290002bea004158b30006663b26498a4000e9d5458d32904015dd0f3126528002f660e214c03000736328c510a60008fd821d9414c0013bb0e10e6118003ad5937258430006af39aa410ca0008fd8714e62840019bae631ec4aa0033e591700ca510053ec28c710c4000cf676d8e31484018fea43b2a89080277a1e52
  | 25 => 0x4019dee4b128318002b760c4158b300055ec20a0b0c64008fd87d4c624c4019bae731cc3100033e591700c8100057cc04c730484009ed821c5430c8019ece3b08c099002af61050d8f21006baa94e2194a0009f5821c543c8401cbea729ac319002bb60b644ca310067731ee4a0a4000ed98758e600840197eec3a242980032f5db744ca4100577c1287b126200c7c615d46250c015db043a6c498002bbe097358a510056fc1ac5994a0009bd841c961cc001c7aa7b22a4880027760c70553310065fc26ec90860009f4815d1320c0019bae6b1e43100031fdd3654c91000737b2c4290a6000abd8414c624c4015ef0c98a42180032f10476551300056ec1ec99944000cbf649cc6048401cdccb3124218002f5205544c9310056fc1ac5994a200cf67158730080019bee739ac408003765ce70085300047ec10ecaa220008fe8798930040011fb0f994c1208023fa1876085300073732ac590860008fd8714d62840013f50f20a60900027e60c7054b300065eb20e498860008fd871456308001af0ebb8a61100033e591700ca310066fbb662a184000cbd74193604c8015bb07a8ac7100026fe11719493000773c3ac53086000cef8758a329408dabea6bb4a7190032f9d86494d210055a422c230a6400ecc864c931480011fb0e210c6900038f99664884300066fbb2a690e6000ed6804c9610c80137b09b984298002bd20564587320065fb20e0a9a4200be8805d63248001dd702b1460180023f61f644c8100063f3b0cb10a60009df865cc21cc0015bd0c10c6098003ae59273980210067a38ac2b026400c7d65dc5430c001d9ac799264108027b60a70945210047ec3ea2b1c4000aef8258e32940019dae5314c218002b720d65485200071f32ac91086000bbb84487308c0015e900a94c2190031f1d6624c2100053ec2882b166000cdd73d8f6154801abf0ab98432800367dd37348430005eac1883b0a6400cef76588210c001a78caba042980025f6087155153005ed40064a1a6200abd86909420c0013f50e10a61100031f59573904300063ebb6ea994a000cdd7358e62040018facbb9c421800375dce61484300053e432a8a924200ead641c5620c0011fd0c392a298003b61cd63580210055fc32a920e4000cf67158730880019b8ed29a4298003375d953087300063e42ae7304a200a7d85191604c8019dec538c6498002ed2054250630005f2c1083b0a6400ee681589310c0015f300318c0908036b5537250d32007e3b90e29926200e7565c86210c001db70eb1ac0108031f594714c8300047f436e6a924200cbd74588218c001f910099262900033b5d962884300047ec3ecb9948200af9800c460484015f700994c01080397595438c8300056fc1acb90a4000aef8258d4248001abceab984298003675917308430006cf322e610
  | 26 => 0x33dd95710ca200067bb8ce3b1aa400c7f531d9544c801cf4cb39cc010802be61f60981320063e3b0caa0a6000cef651c931880018fae6aa6c4a8802bb60a4358a500047fc3ac790ca000aed82145628c0011fd0c38aa690117b3e19434c8320076b994c298c8000e5d658ca310c0013f30e10e6118002be61850181320074fa10c6a1a4000cdc7358d52908555bb07b2664988033bddb744cb200065fba4e9b126000ecc63509324840137f08b8cc418003b958961c84300069fba2a690aa000cbd635ca4190041b3ce929843980033ddc375584320065eb24e12984200e5f65d8d53484015bb0c10e601800337d8d7294d21006ceba2a610a6000ade8718d31540015dd0420ec4980031f14076551210065fb24e1b1a4200ead64dc5620c0019df0eb146518803b154932584320047ec3ecb90c60009df835d542cc8011fb063b242a8003755ce21087300063f3aac410c6000bd4815c1324c4011ff0eaa2c79080337dcd6358a510047f43e85b1a4000cef73d89524c401bd2e499480880031f597735043000677c3ac59086000c7d659c6320c001cbacab82c610803b6e1e639802100676b946530e6000c7e76194214c0019bee739ec4aa0034f55173906500047ec3a653048200ced74d8a214c001cf0ca38264980023f61b7250e100076d43ac73004200add83d0163884019baebb1a6490803575d6730863011f3632a8490a6000c7d655c6420c0015f700b1cc1908033759773484300065b3b0c918a4200eaf6290a414c0019dce4b106328003575d573085300065fb22e1b1a4200ecf8258d32040016f500210ca98002e761021cc0300066f402e7b20420097f855c332484017cb02192a4900032f61176084300047ec30e0a946200a7f8558f21480019bb00b98c2a10023f61a7290430004fdc02eca9e4200b7985087304c0017a902a1a6498803b9a1d62584300047f436e4a9a2042e9e5458d3290401af4eb3804398003b6589314c0300063e3b6cb2126000bcf825d132cc4018fce832ec4980026f21d544ca41006ebb8ee89926200cee7690b214c0015f100a9ec298003ab58a41504300c6d63a2a490a40009bf845c662cc0011fb0dbaa65188039b99671988300066eb9ac72962000cdf7318d21500013db0438a86900034f55172906500066fc1aec9962006cbd7650a40cc001c7ecb20a82980033b9c962986530063eb2ee49886000e6d6558a210c0011fd0f31261080027b219739492000756b20e33106000d7b761d5308805bcbea7312c529803579977348430004fcc10e0a9a2000cde7654c214c0013f30f90e6098002f5a04704c9310072eb28439806000af7814ca61cc0011fb043b286880027b209744c630007e898a871022000cdf769c1320c8015ed02286c4988027d2057655132176d63a664b0a6400d3d54dcd5290
  | 27 => 0x7bb2a499064008fc8755363480015bb07b2a651000317d9573085300071eb2c852086000cec87589410c0015df04a1ac598802bb60a5358a31005d7c22e2b1060009fb805d532084011ff0eb166320002bbe096350a10004f7c12e898a6000eaf74589210c0011fb0e202c598002af61262cc210004eac18e2a122000b9e831406448401d5aa8b1284180033bdd3628c9300056ec1e8431a40008ff825ce6190001a7ee929a43280027e61e42cc1300056ec1ec49902000dad7454821480015bd01baac6108023fe1d63c85200057a40ac4b0e6000cbd765d0214c001cbea7b1ca790802bb60b648c8100057a402a4b086400cec621c1524c4019db023b26490002bd60a61c8430006da320e2b226400daf74989210c001dd2c510a60180031f1d0651893000677b9284b0662008fe869ca414c001d5cc9b8ac4180023f61b73c843000576c14a7b128600af78158a610c0011fd0e20ac6900033759573087300056e41aca10a4000c7d655ca410c001b3ae939842980034f5d5430ca4100772b14c29086000bd48150d310c0018facb39042180023fa187250d3000677bb4849086000c7e855d8210c001c7ecbba24298002b7a0c5158f21004eec18e4a8a6000a7d87d94214c001c7ca3b22a6880036e9d170084300053ec2ee0b1462008fe86dcd54480016ed0329a4328003ad59161884300057d436429824000cdf8758f3288001b98c7b9aa4900033b60b76551320057cc00a6b0c4000ee581d8a214c0018f8a1bb2a9190032f595740862000576c14e6b148000ade83d9763484011fb0c3828719003671d3734863000767c1ac4994a008abf8650d420c001cf2a6a92c010802b7e0d654cb210053ec28c690a8000cef7658b210c001dd2c4a0a60180027b608715523210f3b32e429086000cdf655cc21cc0018fecb388c498003b35cf6208530005f4c10a1b026400abd8690a41cc001d3ca9b1a86900e67ba1c32549200063f32ee2b106000aee8299162cc00197ac9b9aa5900027760c725073000773314c210860009ed821c543c80019dee238ac4180023fe197290e100063f3aac610c40009f9831c154cc00157f0caa2871900357d4d7198a5300764b12629806000e6d65909210c0015f700baac7908031f597748c720005dc40286a126000cbd65dd1214c001cbac729e4328003975967058c210063fbb2cb1086000af5811cd62900018facaba442180027a6087054d100065fb26e4a9a2000dd531dc943484019dee8b146218002bd20562584300056ec188231a4000cf4865c43294001978ec3a243980036b9937354b200066eb9ac41086000cec76dc53248001bb4e73804318002f6201754c8320047f43ea6b084000c7e76196424c0011ff0eb0e6110003574c5751894300676b9265304a200aef82596214c001a7ceaba0431800
  | 28 => 0x4107614c80197ae8b1065280032f9d263085200067db8ee8b006400c7c76d95214c00197cea320c6908e79bd51628ca500066fbb0e099662008fd874ca60944013b90e90a6018002dd205544c65008cbfc3aa4194a0008fe8758d21040015bf06b2a4290003b958921084300065fbaac99904200e9e641c263084018facb394c21800337dcf63509500074e320c729a4200ced7258b30040012fb0a39ac0108023f60c76505200decf3a2a610a6000c7d655d1310c0011ff06b90c0aa0038fd9153945210057b406eab086400e5d655cc210c0011fb0eb1ca3900034f5d67408730006ec402e610a6000c7d655cf210c0011fb0e31e43100033b5c96298430006b6b92a418ca000b7b855cd6008443eaea729e4290802fa209414c1200069eaa6e6a928400cef84dd9320c88dcbccbb2c6499002eb608501912116eafa9ced29a6400afb8254d600840197aed3a042980026fe11718c8300057741687b126000cdd7398e62040011f90cb8664908025f61e53c86500066fbaee0b184200cf576986210c0011fb0fa10c69000337d9573084300063fa92e6302a800ead4398a410c0013d90ea9282900023fa187150d20004dec20e4b086000aee82d93624c001b5ae99084298002eee11218c2200057d4304318240009ef87484210c0011fb0fb2c6408002bda1e614c65000676ba2c490860008fe86dcd214803175d08192a490003b95c471588300047ec3ec99946200cbf655d021880018fccab9a42180031fdd95454a310047fc12ed18860008fd861c5540c8019d8eca9262900029f6144358a310067ac0aed9086000cdd7398f21c40015bf06b2a63100027760c71553300056fc32632184000abd8414e62840013eb0f994a2880032fd937254d210047fc1ae4302a2008fd83dd94188001d9aa7b146498003ab59371988300057d404c8b0264008ff87d8c21480015dd0e312a4988025fe157098c21006baa92e2194a0008ff8758e53484019bae6b184328002bea03654ca3100576c16ca9086000cf6725ca610c075cdf04b2a6590002bde053298430006d7ba26490a40008fd87d8f2188001abecab984298002bb60a6398a510057bc2264b086000cee81dd9320c8018fecaba2429800375dcd61484300056f418a3b1a42009f4865ce5144001d38c9b1aa6908032fd8373551420067dbb48498060008fd87d943290401d9ec7994a490002af60f65d91210065eb20e6a904200d5d54dcd52cc801c7aa8a1ec4a88032fd9774486300073732cc41086000c7f539da5348401978edba24318003ad59072584300047f436e4a1a6000cdf75d8d32484015bb07a92c610003375cc6318552004eec1ce32066000c7d65dd1310c0019eae730a42180023fe1973084300071eb2ac8aa26400cbf431d9544c00157b00328c890802bbe0953189410066
  | 29 => 0x1ca6908027760f7408430006ecb9ac79044000c7c76595544c8015bb072a2c7108032fdd363485500076a994c29886000cdd734ca6008001cdccab1242180a797995324c4300047f43ec498a8000c7d65dd2320c0014ff0eb2842180ef5b9977354b200047fc3ac72948200cfb629c2314c001ba8c6b9ca288003b518d31485500057d404c2b026400a7d8510a63480018fecbba46298003ab58942504300047ec3ac59802000e77654c5214c001d3ec831aa690803b958a61084300057d406c3b026400cdf865cc21cc001a7ae8a9043280031f597704c8210047ec36e919060009f7815d1320c0016bb0620eca98003b318d32885200063eba8eab1e4200d3e74194214c0018fecb3948298002bee0165591320047ec3eca1944000c7f531d9544c4015bb07a92c7080033b5ca32982310066fb9ac6b004200af58298531940011fb0e994c3200038fd9542505300065fbb6e890c60008fd829da53504018f842ba8c6a000357595730843000772b12629086000e7565986210c0015db04298c4988027ba1b735492000677ba2c59086000aee82d07624c001d9904b1a65288031f21573982520055fc326520c8000af880596614c801de50d18c4088003375d97308430004f6c10e0a9e4200b3d8408650540011fb0c38a87100023f60e76085200047f43ac49802000cbc74d89214c0019bd06bb04398002b760e624c2100056ec18a2b1c4000cec72d89314c0019ece2b0cc0990023f219719493000756c20e2b106000cdd7354f62500018faecb2e42180033ba097608430004bec14e329ca0008fe861c5524c0011fb063b2a888002afa1b50191210047ec30e4a8e6000af781591604c8018faed32c42180032f211721855400757b26c4a126000cbf429da424c0015bf06b126528803799d921085200066eb9cc610860008fd87cca61940018facbb9a421802e5fa1e51486500066eb98e6b102000b6d82107654c0015f100b28c2990032f59070548210074eb1a8720840008ff8758e42940018fecbba64298002afa1371d89300055ec3484a166000e3f42d97644c0013dd0c3928290002bba0864d89300076aa9ec318a6000cdd7318c62550015ed02286c69080337d8e7094d21005ddc224298240009ed821c143c840197aeab2664108039d59772584300056fc1acb98c8000d6c725493194001cbcca382c6108031f997714c830006bcbaae01086000aee821056348001978823b2a890003335cd62084300055fc22433006000bd98308630480017c902b266499003abd8a4250930004efc1ae520c60389ed87cca52480011ff0cb9ca588003579977250f31006cfba0e690c6000dcd53dc9438c8013db053846390803baa0071588300076cb80e0b1842009f9869c021cc0019bae7b18c09080337dce63487100055e432a8a126400eb76
  | 30 => 0xc4300056f41ea4b1e42008ff825cf64040019f707bb24010003731c9324c630005afc2ae13184200ed9631c132880011ff06b96ca08002bda1a31485200072ec28e0b184200abd84143614c8019dd02b90c0a98038f19474485300053ec28e8b106200aed8210d628c401dcee2b8ac4180033b20572d94300067bbb4c390860009fb835db2088001cdccab1042180032f8c1741895100736b2a859086000c7d651c9310c0019f2ed38042980023f61f650862000756a1ac52086000d5e755cc210c001c7eca286c890803b95cb628c5100057cc36429806000e7565884210c0019dae531660080039714f6354f21005bc402caaa264008fd869c2528c4015dd04206c498002f5a06704c9310072f32ee0b184204cbd7690640c80015d902ba2c418003755cd210853000774c0ac51806000af681140624c401dcac4b0a42180033bdc962582310066f3b4e610a6000b5d851c163084013ef0e90842980023f60f76486400076641ae2b106000cef825d932040015db0d90842180023f219739052000773b144210a6000ced721cb63550015bf06b1265280038f54d54d8d400067bbb46290ca000e3f6550e414c001daa6530a63200023f61b7050f21005ecc18429806000e5f5394f614c8013eb0f29e4290802bbe0963086500065eb06e6aa482008fe8714f624c4013dd0f98aa490002b760f644ca20176d72a6e4a1a6400edb705c16308401dcec498c4298002b760e61cc2200075a320e2b226400eaf6250a404c02537f0ea186520802eb61021881200063fb2ae83126000fe12108630480015dd0f3126520002bb60b5158a3000577c12c6994a0009ed821c1438c8019dae73148218003ba589700843000576c16a1b1262008ff835c86150001ceeca9084298002bb60b6508430004ee432e521a6200cdd73d8c21880019bee6a9ac5208033b5c93298730006f5b90e0b2a6400e5d65dc2630840197ae7208c0a08036b9c94290330006763b44290a6000aed829c36348401cf10ab9cc0108027be0974947200056ec06ecb184200abe86d4f64484019bee831c629000337dd8704c8320066fb9aa6b0e4000c7d7558c32904014ff0ab1a42900033bdc962586530055ec20a0b1a4200bb5841ca610c001d3ee8b1a65208033d8c871595420055ec18ca3224200cde7358e6008401c7ec8a9aa490803b9a0762885300047ec3c6430a6000afa80193604c8013df04ba4a290002bda0764d85320055fc1aa9b128000e7b655c0214c0016eb02194a32800376e0173085300053ec2886b1c42008fe86dc132484016bf0ab82c6108033b5c96290330006ceba2e61086000e6d651c5620c0019dce4b1482180023f61b748c4200053ec288531e2000cdd73d8e21540015db0431e42a8002b7a1e634ca410063eb28e2a1860008fc87595214c001cbea6b
  | 31 => 0x6200ed7638c621480015f30118cc1908032f991728c43000756b22e2b106000aee8210560cc80195ae9b104298002bbe19754cb200065e20eecaa66400c7f655d0214c0013bb0738485990029f2195454d21006d7b26e4a1a6400cdd7398e600840157908b8ac598002bb60b644c81000736b28e331060008fd82dd9544c801b5ee8b1242180033bdcb62505300063fb2ae9b126000eae645c5620c0018faeb31842900023f61f4358b100047f438a2b1e42008fd87d9721880015eb03994c3280027ee19700c620006eac18e2b226400cbc7458d21c40013bb0f29486988e39bd51624ca500076b402c69084200cf6765ca3148401d72c9b9ac0108031fdda65c8430004dec1ce121482008fd8798c21940019bae6b1c82100023f61e63c84100071eb2cc99086000cbf7458921940015bb07b2a65208039b55362549310065fa12e7b224000db9749c0218c00197ee9b1242a8003b358a324ca500047fc32e52086000e3d65593210c0015eb0d18a4310002eb2094350b3000676b94653048200cf576985210c001b3ce939842980033721973085200066eb9ec610a40009f4815d132480019f7013b04298003b9605628c4300063e42ae6302a400e5d6394d21940011fb0e31e42a80023f61f654c8101456ec1ec89926200cbc7458d21480018faecba842980039d99561c8430006ecc02e61086000a7d86995210c001cbaca39a42180023f61d6390a20004fa40aeaa166400cf576884210c001ceaca98c42180032fd93704c921004f6c10e2aa26400cfb865c032904019eaecb1663188033bdcc625493100737b28c410a6000abe831946448401b72e8b8043980023f61b7255330004efc1aeaa126400cf782dd910040015f70eb00c099002f660c21cc230004fcc36e099440008ff865d121cc0015f30c286c0990023f61872553300047fc12e63028200be88054a21480019f2c938065188023f61b7354b100066fb98c6a1220008fe871d932040011ff0fb1ca2900039bd9642c85300065fb2ae810a6000cdd73d8e51440011ff04b98c0aa0023f60f7655320004f6c3c8729240008fd87d913248001dd102b126018002af6105258e200071eb2a8720e40008fe87d85604c8019bae0382c610802bea0041d8d200055ec06cbb224200ed58058d2108401d3cc8382c610802bd61e61c84300076db84e0b1842008fd874c860544015bf06b166408002b7e0d65085200067d31ce010a4000d78655ca4044001d9904b1a6520803371cd6354b210066fc3ac7994a200cbd74d88214c0019f2e0382c7210029fe0954d8d5100676392c4a0ca000eac64d89424c001cbaa8b1aa6108027be097550e320063fbaccab0a64008fe8710b63480015db05b2a6518803ab10a63509200056ec18a1b126200cf4321c5644c801cf0cbb82ca9900397595434
  | 32 => 0x13bb06392a8980026f61b74484300047f436e990a60009fa8790530880019dae6b1484180031fd95739053000677bb4c51086000d6f7254931940016f30129e43280033b5c962904300066eb9ac728e4200e5d6394c21940015db0e31664a0803b958961084300065eb2ee890c60008fd87d8e53484011ff06b90c2a800397d536354d21004eec1ee4aa66400cbf7499162cc0017b100a1a62980031fd95729053000775b10e09926000cbd655d03288001db70c98a60180033758c7054c2100576c1082b166000cdf74d8d324800197ac9b9aa410803a79937058c21004bfc2ae199042009bd839c242508019baebb1e6490803b661d63580210047fc1ae430aa800e5d8558e53084013df0e99065208032fdd874487300066ebb4e610e6000e3c64104654c0019d8ec38a64900023f61d62903300063fb2ae72126000c7c505da3294401978c8b8062908027e201754cb2100796aa28590ca000adc865d5324c4019bee6b1243180038f9977448430004eec18e2a1060008fd861c554cc801b38e839a42180038f19450191210072eb28e13184213af986909308808b3df04ba664990023fa1c65585320047f438ec9086000e6f7558932940012ff0ab8487908031f1db65905300047e43aa9b1a4200c7d76995210c0011fb0fa02c5188031fd9572d85300053fc2ac610a4000d3e759d0218c0013db053846290803971436394d210063eb2ee4a186000cdd73cc86050401b5ae890842980038f55362549400053ec2883b1a4000b798094d219400197cecba0431800337dd763cc9210072eb2c629886000aef8258e32904011fd0d39042980031f59574c8430004bfc3aa598ca000f1d5450d31940019dee5392c7288029fe195454e320063eb2ce33106000eeb325496008401c7acb212841800337dcd6354a420067a388c6a124200c7f651c5324c0019dae238ac4180034f5d57408630006cf3a4e610c6000cbd649c33208401cd8cbb128498002bb6085398a100056f41ea5b1a4200cef7258931cc0015df04b184290002bde1d618c620006ecb9ae010a6000ced74588210c0011fd0eb1262180033b5c87258e400047f436e910a6000e5d5314d618c80197eeca1265200033b5cb6218530006bc32ce010a6000bd8805d532cc4012ff0e994a32806f671d153485300047fc3ac39804000af581d88614c0015f100b22c099002bb61071588300c6d73a2a410a4000dda805cc210c0011ff0cb9c83900023fa18704c9310065eb20e0b18422edcd83dc9434c80157f08b0ac0990033bdca624c2100066eb9ac720e4000cbf76dd121540015e902ba2c598002eea0242905300056fc1ac49962000cdd655cc2148001cdacbb8ac4180036b5d362085300063f3b0cb90a60008fd86dcd410c0017770890e60980027b6087054d2100766a98c4992
  | 33 => 0x710d00d000800204d071802404800cdd755c16308401cbd0a382c6108023fe09731855400577434e29924000e9c6350e41480011fd0c382a4908027b209744c5300066fbaec6a9a4200de9305ce5248001db4e0382c610803755ce21086300047f43e84b066400ee5654842148001c7ac929aa61080337e0173d902100736b2ee331060009fb865c231880011fd0c382a8908027ea1a70c85300078fa9ec929a4200cf5645c43294001ab8e6a9aa590802b7a0c50d8f210063fb2ee2a1a60009bf845ca610c0019dae5b10c0a1803375cf63945210056ec18a1b1a4200cdf7390d62940014fd0da0eca980033bd88715093000756a1ac4a106000dda739c0214c0014fb0d3284218002bba085158a300065f322e71086000cdd635c253084015bd06282c3190033bdda714c8320063fb2ce32126000bd8804c9314c001d6ec918ec090802bd60a614c4300066eb98c720aa00097f855c06348401ceecb90c42980023f61a7190c200073ab2ac31086000cf6329c76488001cbea6bb4a7908039b19762085300065eb26e0a984200adf8359432880017cb04208c299003b5615634842100766a1ac51906000ced629c6420c0015db05aa2c5180023f61c32982510057b40cec9948000dcd73188214c001dcb03314c218002afa1a42905300065eb26e0b1842008fe87109608c4015bb06214c788002be61832902100059ec286520c8000a7f855db214c00187acaba042180032fa117608430006e7316e4a1e6200cbd741d162cc0019dae6b1482180023fe1973904200065eb9a843028200ed88058e60084019f6ed20a6018003b958b21884300055fc22e2b14a6008fd8798c21480011ff04b9ecb20002d760c42195300075bb20c718a4200cec769c532480019dae9b1464980027b6087050d210065ebb2e810e60009fa869c241480011fb0f298c4a08031f59573907200067643ac52086000c7d65dc9410c00157b08292c5180033759573085300076d43ac6b004200eeb81589300c0018f90ab98c0aa0032f5d163085200073ab28e4b086000ed78558d21084019bee1382c610802bba084118d200071fb2a86a1260008fd861c142cc4017ab06208c2990232f9da41901300056ec18a0b1e42009bf845cd210c0015ed03b2665100023f61b73084300057cc046230242008fd87d4e62840011fb0fa1ec4980023f61b7408430006f3b90e2b226400cdd73d8c6154801db10f31cc010802b760c41d8d2000576c1083b1a4000cbc76dd1214c0019eec638a64908031f14376553210047fc3a6530ca000d9e745cc210c0011fd0eb1aa5880033b9c962cc650005da40a84a0a600097f8755231940018fecbb9c42980023fa1c40d8930004bec388232a6000cde7358e6090801978c8b80c6908026f610724c7300072ec2ec6a9a42009f5821c5434c4
  | 34 => 0x48038000018000003c010006002005811806c082801400201701980d401c0090008004002005005856c00e04100000a400c0f60c800c838c01c00c800c01810e00280900420000008014000019006a0400180820060010056003008000c0300046c5000000200710406cc01200000781b82f200200a802001c00102b80bc0920b300a0f900c800000a01b000a000025007113200200b801406001a02b00b001400900180c0008009025000c09800b0008158000000000008c00a10900280cc00600d001038c010003078829c15a001142012c000f84000004401602c05a801c11800606d004c000034000000040a01912316c01740010030000000279001807c0000000178008010008000002800206f001805c1ac000001800c024013000002000000102c000008c00b000002000c25e00c0c5c006000001020000002707380d41000be0028cd001804e0ca0004002000011000c01802900a804007000a00003e00be003004000400001d00500040c0003055000000e00e00c826001804103f8018000263005800406400d00c806403c05c004008400000301000fc0464ad04f808821c7040008000004001035835006c0010053fd438407b000800001200a000016402401f07584000060010f90010020002000295c03800400080240000060070030004007013000001a00f001013400000f04980c800800604d00210fe00042702081520070e58018018023004866825e00000e004c10802001d001006600a00038c400000000300f02800000178064004004094800043a00100d8060000022160801c00000000e0dc801000000300040300310043db401009f02b8f98006077003009008000c00081ac018009005801802e0020000c2007400d00c800c06a0b4001801401a04000080c00060130261648004026000004401800101283f4008016006000c00404b025003803e00300481300e200701500045fa00104c801064200700780540040110788054002008002000444829702900cc00e00600302f8000003007006c0c4003182000004c00b001800400e00001d002401000602a801400608407e80000dc17c0028354094000003008886000401f869400603c00b00e80b6005004000c02e0020039a3404e03b00483604a0002000004805402305c80c000000200c80000e000b001835c66401b636005c30600e006028407a00105700482ae00400e000c01a0ac00f800421e00200a001801800000500f8000003008800005a1a30038000494001335805000800301700a49c805a000004401600900001540bc035000005c0080022f48edc0000690ce8024004011000000000a0500118018000056000000002000100803fc0340070068010004014000821000a47409700043bc064000012c06a000001809c01600a00f800005c00100280cc06
  | 35 => 0x7822300080040120050c6800800800002c83b800e02b000020402e1510378030006369004000001e475010130c00800300000501cc000000029c01c05e0940004044000007000c05e00209e00a45e84b8000005000c001001802012e0010030004004020012000024e019005000003e006007000000000e0cb800400004c02a01a44ba07a0000000000001000002800200700300440021ca261809400c038047800400402000400003200050008008186002035000800600000b000000076f00f003400004f02c08240a0000006099423000800000209a4008002800805e1b400a006000e00a000000403401400e809c0020023570018000000014000002400201e0010008002002009486a00e15000e806c000001004c00802800b8488000036041800802601500080000083f3000003402a00110500b01200170220000000601016829401400000000700b808700000f400c02100a006c00400f00080501683dc002005400a13e03982580080120030020000004000000c06c01d00001e000000c01480ac00a0040da0ee000604400000003e005c004801c03a00000a800000000506c801c01a0090cd00740500080020130560077005000005600e013803000001900f00040000040158080028040001803c00600004f0018000054000008001601701b80d00101d8000000001041604b000000e014043008400a30e0010194c00006025800801000000200e81380db000000000600b01602dc000585016800c1c2c912d8893c008016047800002800d00a006805409a0140000160007011030c00c00000100140060001b580b80000dd00900f82300000110000096000000002405e00f041000014a0600030004006005000002022600f002810806802d00000e400000f002014096a0032ad8190016012000977c00a0110018008000003001803c008018000000400e001000002c10801b00080b000002500000302120120028594a9a31200000183840070170034000004010872401e0c30708014004094000007403803b003003cb6e00007480f8004026022059426e00f0000000062006000800005400d024800000001102300cc01a04400800a80107a000000000280100008008126006004005000a01e002801c0000fa02e000003c00402e150c02400a00183fc02e000000800002e005000004000003c00b818401806d12030c0006000000940c004001000006016402200080040b600100080242224380020078000168001019412e000000801c01801c00104b0000362011883c02846402a0020016002003801802601d0010014000003000000000000000d0000040012000003000409000e000400e04f040001000000300000ec00002f0a601c8000035005000c2ee015000002812403200107ac01a07f03b866c02c001002803851e00303
  | 36 => 0x200a0008000008007000000c00200100290e4000022006814c022004023002c0fc15400300c802a02e02204f400202d29a05a807a51500e800c01409e00083b8062040003000c00000500d009477ccef000003002408700180d800400026d000802c07300300040580000058a9400800700000002be00a013000009801800f001c04000f010802809200000c80086c401500000000000160028044058000001000000806600e800003c04312e000401a009006000001200e03580d0006007005019002a03400000300064fe00e805c58400001980000060061f180282600c70c5006c0120060038004082018000000806000000300000141cf00302300000030068014012001002000019400500f829422200400c800003600000a8210118027000002092c00000081900ae000009801c02c4d4003814c00000a0003e581c0120011801804e01e000000000a0010131744140020001020400237b000800801e00c00080a40000000250020006102000825c0180060ae004418e0613ab373436e0320368000054002864807457a00301d8000000003004000019401100084b400e00d0010034a5c0010000000004000000029c3d8000004807000a00d04700001c00030130004002010005069c00000054b000000222a01e00044080191788a400a8025020815000400c00b0040302061003009c008ba50160008000005001003400006b002804803e018006800c00e03c016001000401200080000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x40145d931417694f2100596e558758e600840183d8699774484300068ba16841c5620c0017289055152905200060fd95841c9314c00146e929d065d85300050f65076d94214c00165b95602639802100556643855cc2194001cc5735892108430006176157318c21880018cc865cd3208520006b2611624c5300c00183d65e11718c830004b6e61701c163084018af875d162084300042fe5d8414e62840018ad84a0976084300053364c815c86054c016599520163580210068ee15645cd600840162c9655152509210060fe177458d2148001aa984a0071588300068ee15645ce600840146d97194620853000713e5776549320c8016e091611325803200695a15811c163084016a59420562584300051725d6354d5208401a1d536107558e1000674481831c54244001c2d755d3620853000475660321c5644c8015399419470595320051765f539da5348401c2d655d321084300060fd97845cd214c0014b69799261484300053a24175d89324c40149f935957408520005b164483589329400185e875947348430005b124543589310c0016359119041195300069aa15801c5620c001c4e65dcd624843000527a4e751936048401d45524c9710ca50005a9e518798a610c0014bb905977458532006aae1162485300c00183f64e15700c521004ad65881509410c0014ea97205624c0300061721d65485300c001c4d7518d32085200058765285d8d53484014b8905d5644c821004ada5a8114c6448401c39655d2700843000687616841c16308401dc1905cd2108520004ba6488150d600c80183d6561072584300052b64b655d0210c001a8e84a0c7158830007239d273588210c001558955c0704c9310052b64b431d9544c80165b955cd63980210060f2147458d2148001e8b8450d32580320058b65442d89424c00143e95dd87448530006aaa11801c5620c00145d97d8d53945210063a48087d8d5244001ca574589610843000693615821c1630840183e85a1176084300063a58d821c1534400183e841d6624c2100062b5d38258c219400145d9521973085200043be61711c5620c00183f8699574084300052e64041dd954cc801a8c84e0d71588300051ea5c651c1654c80145d93d4876551320063a60375189324c401ac682a047058c210041fe61751d76348401a1f855917058c2100716595739c0210c001c2e65dd16248430005362417558d32084018cd73e09630865000617d9583dd0214c001a3565e1172984300052da5d64585210c00187775e0564581320044f66074195214c0014f2900c871591320041fa62655ce60084014b59759161084300052b65072d89314c001a1c6560c501912100687e15645c26308401a96846047058c2100517e55865cc214c0014ad94dd962084300061d594815d1320c0019d22060c7150910
  | 1 => 0x52ba5f41d89424c00183d65e11734843000693616831c5620c0014cc97589324c6400057264f60dcd5248001dc2905cd2108520006176177398d21c400183d855d07458b30007315cd62484218c00145d9314076549310070bd967250a404c001c2d655d1620843000791e15524c9610c80146d97197620853000693616821c16308401a1d8454c53189310060fa1d65591210c0010f5981887155131006aa611801c5620c00183d65610724c4300063a21b705d53248001c4d655ce62084300060f61e65990210c00149c9359574085200052b64841dd932900010f7985c471d89300053c644329c3658c40183d85611760843000617dd9851c163084018bb76e11214c030005b4241854c9610c80189d8659373484300068b5538258d429400145d97d9673085300052b650811d9324800143d951db74484300059364c50d89524c4010dc9859573085200071359573588210c001c1e65991730843000687616641c26308401c8c74dcd624843000695616811c1630840143e969d6740853000713d9573188214c00145d930857518d400041fe61631c552940010df985cc7358a510072a9d3625c0214c001a2e65e1171588300060f61d65590210c00143d95211721854300517a5c53d8d53c84013c993201544c9200060f6157418c21880018e776205744cb200070d59774985210c00145d95e1973087300050fe5f655d0214c00162d9510863509200041fe5d8510a63c400162c965515250920005a96508758a610c00168d921076350d200053924584dd9320c801a2d5460b63549400062b591821c153084018e78758921084300063360f621c5424c00143f945d965484300053364f74588210c001ac563e0152484210066a5d0805482148001c2e65dd262484300072a5d1625c0210c0012b698991729843000587a4c65d4c6448401a2d5460b6350951006b2e11624c5300c00183f7461663487100042f66074195614c8019a474205524852000596e557398e60084012d59320542583310052b65272d8b614c00123d981947448530007075537354d6290401c6a755897008430006725cc8054821480014ad921047650d200062b219744c8214800143d969d674084300058765053d8d53c840125f9854c53586320041f6607598930840018ac865d121085300061761d6394c2194001a1d65e11214c0300061bd97825d1314c001bc183484218c1200049e6548058d600840161d9310765d91300068d597845c9610c0018e9636087054f2000535a58321c5644c80143f97596740843000517e5f655cc214c00183e871977448530007325cd625c0210c001a2d6561071988300052be5974588210c001c95645cd61084300063618c805d53248401c1d54dcd4358a50007315ce81588210c0010ef985d1624c43000497662651c16308
  | 2 => 0x4801a2d54e096354a41006a3a11831c5620c00185f86595730843000596e558798e6008401a55856047058c210070d194645ce51440014b6971937159132007325cf625c0214c001a366561072584300068b6154210960cc801c5865dcc7059532006335cf8258c2148001c8f74dcd62484300072399173588210c001c3b659d170085300052765874dcd210c0016c990209634ca510041f66274197624c00143e969d574085300042f25d8414d61080013c993201758c9200060fa10659cb614c001a2c6460841195300050f65a755d0210c0014f0905977159132007075517350f625440143f975957408430007295d162984210c00145d959cf63d81210052b65b74989210c0014f1910c8705954300731595734842148001c8d641c9324c4300052b648411d9544800183e8799664484300070bd9574d88214c00145d9759673084300060fa10651c9314c0016389059564551320068759584087300c0018af646087054d210052da5c641c5644c8014cd9220173185420041f66274197614c0014ad9799162084300051765a755cc210c0019966460c7150b310060f6157418c2148001a6b6560850d81320068ba15841c5620c001728905515250920006a3612831c5620c001c1d54dcf63549400050f65f659d0214c00145d959d97308430006561d4805d5320c80183c75211615813200517654805cf6408401a1f6460c4119530005872595454d434c00183d85d9273d81210060fdd784585604c801c1f649cd53945210060fd95849cb614c00143d942157318152005a924584589410c0010fb985c07058e42007315cd62984210c00145f975957308430006a3612821c163084016359519071591320060f214645c33248401cc573605620843000627591831c1520c80127b9560f765802100635d89831c542cc401c4f655cf62085300042fe5d8414c624c401c1d65993734843000617d95831c5424c00183f6561373085300062b21d7450d620c001c1d6559173084300063ad8d821c153c8001aab84589218c030005b16448358932900018db76201754c83200693a15831c5620c00185d855cc63085200062b61d74d88214c0018af7661071588300070d99774585210c001ac98358a214c03000707594741cd210c00183d856107655132007a261143589300c001c2e759d162084300068b595841c5620c00145d9314376552320052b65b74589210c0016ab94605624c030006391d8815d132480014799759570084300070b59574988210c001a976460c41d85320071559773985210c001c8e745cd620843000635585831c5420c001a69856007158830007315cd62884210c001c8d749cd62084300051d64474194624c00186d65e09744c4300070bd9574188214c00185d65e0d74484300052b650815c86054c016a59421e629843
  | 3 => 0x21006955948150d310c001e894358a414c030006691d0815d132c800183d855907058c210053924574d89324c001c8d745cd62084300043be61721c963900016a5941c962584300053364b65dcd210c00185d6560c715083000635e59831c54244001c8d749cf62085300068b509851d1628c4016359519371591320070b9d574588210c0014af9460572181530049ea62655ce600840143595190715913200716d95735c0214c001c35655d161084300071319573d88214c00183d7561065d85320050f65376594210c00149f935977448520007315ce62984210c00143d97d9574085300072a5d3625c0214c001a3665e1172584300043d660329c764880010fb985c070d89430068b509851d1620c40147a969d670085300070b19574188214c0014ad97d8942901300061e1d880595544c801c57655cd210853000517a58655cc214c0014b8905d7644c921006691d0815d1320c80107c97614425803100627dd984085300c0018ae865d321085300068b509851d162c4001cca7358a70084300042fe61741d162cc0018e9606087054e210052b6538758b210c00186d875d7620853000517259855cc21540014db905d5634c821004abe5181dd9620c00168d931086350920007139d573588210c0010df985c07058c210072359373589210c0018cf636087054d21006b160a811c16308401a3665e1172984300071559573584210c0014b7965d161084300064e5d18094c21940010bd989d464d812100729dd162585210c00145d97d95730853000635585831c5428c00183e8519273d81210060f59584dcc210c0018e476e05744c9200061b595821c543c800171491551434c65000687a146418e53484010fb985c07058a310052b65373d88214c001c39659d170084300052b64b65dd1210c0014cd93dd3620853000617615701c1630840183d8719041195300065a195821c153440018e462205744c93000687615641c2630840143d959d9740843000707597741cd210c0019e2316087054d10007295d262984210c0014cf9361d629043000693e14825c1630840107f985d47558f210043e65c8054c624400162f965514354b200062b5d38258c21480010f7985c47158a5300497e615314c624c4019556560c7150b310050fa5276195214c001c5665dcd6148430006b2e0d62486300c00195973602530865000539e5d81588210c001aa562205425043000517656835d821cc0014af945c962984300043ee61701c163c8401c1f659d2730853000547e5d5450f319400126d98140625493100536a58805cc214c00127a96a004219530005b26408258d3290401a2f65209435093000639988815d1320c00183c851917018d21005a36484118d434800162f965515250b320058e650651c1654c80145f955ce63980210043de61711c7635
  | 4 => 0xc001c39655d170084300072599173584210c001c57655ce210853000707d96745cc214c0016a7945c962984300052b65072589610c00185d865977250f310063ad81821c15348401aa7622054250530005956548058e210840185d85dc07058c210060f5d5841d563c840149c9359774485200071399573588210c00186d65209744c430006a3e10835c5620c00183f86595740843000687616641c1630840187765205744c9300061be1f65484214c00143d975957408430004b564c8150b60484014eb92591700ca310063a581821c1530840145f955cd639802100729193721c5644c801c2d65dd162484300053ce41651c5644c801a1f6560c50191210063aa1d62085300c0014d793595710ca200051b64a74197614c0016599521d635802100635e1973484210c001d45735492108650004ba6488054f614c0010df985cc73d895400716595735c0210c001a8d8460c71588300043e660631c1524800162d95a13625093000517a5a755cc214c00185f8558d70cc8210053365c634c821480015359519071591320061b595821c5430c801c2d759d162084300070bd9574484214c0015a4945c4714c9200060fa147498d21c4001a4d8560c7158830006a3611821c1630840145d9699573084300071559573484210c00185d85a0d760843000635589831c542440019946460c71509100057164b61dc9434c40161d951076350d200051765d655cc210c001c1f7458e5348650005956548058d2108401a2e6561071988300063a481831d95244001c1d641cd53548210052ee4175591320840183d85dd063486200068b5948250d420c0010df9859573085200061761965dcd210c00145d93143764ca510060f2107558530080016599521e639802100696d9583143604c8018ac86dd132485200076250d325c03290401a2d85a1071588300071a5d5625c0210c0010ef985c87258e5100587e595454d438c8019e1316087054d100052be517298a610c0018eb636087054d1000707596749cc210c0014ad9210776553320052ba5e64589210c00187787d95210853000517a5f50d8d5348401a2d65e1171988300053624175d8d324840195875201754cb310065a995821c153c80014d59118f7250d20004aba588250d424c001e459558d52484210042fa5c8050d6290401a3b8599173580210052764c605d06354801a4e85a087058c210070b19574d88214c001c3b655d170085300053325d624c931940012ad9899071588300061bd94825d1314c0010df98dd8214c0300041fa63525ce60948018d486dc5744c931005aae518158a300c001c4d759cd62084300050fa58655d0214c001c8e745cf6208530007315cf62884214c001dc1724c532901100051ea5c65dc1654c801cc773589614843000533e49805cc6150801a4f85e097058c
  | 5 => 0xa4000687d95831436448401a8e846087058c210062b1db845c532480014ad920c174189510053c640321c5644c8012ad9810863509200070b5d574588210c00183f8559173980210070d99774985210c0016c59218d31485500071359773989210c00115d98d4c725865300617e1d65487300c00161d9414f6354d21005876544118d4348001c1d659d173084300050f65a655d0210c001c2d655d12108430007139d573d88214c00183f855d163085200060f61574193604c80183d6561071588300072a5d1629c0210c001c8d745cf62085300051764c50dd954c8401d0d5454f7250e320043d660631c542440018db76201754cb310060f6177418d214800183d8659774484300068759784487300c001e8943589424c0300071559573884210c00146d9218575189430066ad91821c153440013c59220574cc9310068e616641cd6008401c1e6559173084300061be1d65484210c001c5b659ce70085300062be1974484210c0010f99818e709452000707d95749cc214c00162d941406254931006b2a0e801c5620c001ac983588214c0300060f214645c03148401a2d54e0943d895100635589831c542cc401aa984588214c030007135d573588210c001cc57358921086500051764c501d9544c4010bd9819273d8121007325cd629c0210c0014d69720163484210058b64841d97644c00185f855cd63085200070b99574988210c001a35656107298430004ba6488054d61c80018af84589718c83000596e558758d600840162f9655152907200060f210655cd214c001ac531e0943d89100062d1d881591544c801a1e856107058c210047a660321c1654c8018ad84dca624c2100053524574d8d324800145f9560173d9021005a9e517298a610c0012b79460b76584300051764c505da3294401657956016348421005a9e518198a610c00185e87594214c0300068b615841c5620c00147595c80715913200731d95734842148001c2d65dd262484300043ee61701c36348401c386419572901100060fa147418d2148001714915515350d310043b660631c941480014b8905977458532005a9e5187589610c0012e7985c471588300052b650815cb650c001ec291589314c030007705cd204ca51440014ad920c374586520052764e7519360484014ad9210676909300061de1d65484210c001c4e655ce62084300070759474dcd210c001a5865201434c530005b2e4543589300c0010ef985c87258c100073248373d8d5244001ec1624c5214c0300072559373585210c00185d85dcc63486200061759583dd0210c001c6975d897008530005a965087589610c0018d5815d0634c920004a76604118d43480018cc86dcd3248520004ad65081589610c001c4d6598b7250f310052b652825db210c00183f8559170cc8210070b9957458821
  | 6 => 0x10c00145d96d4c72586530068bd9182104654c001c56655cd610843000687e16645c163084019a9646087054f2000635259831c5424400161f965514354b31006b260d62086300c001ca974d8a70085300052e653311c1654c801c1d65dd373484300060f597845c6620c00143f955d974085300052d65b74985210c00147b97d9570085300072399373589210c00145f9560173185420041f660659cb614c001a95846047058c21007235d0634c821480010be972015458a4100517654805cc615080189d6460c7054b3100707596645cc210c001aa76460841d85320041f66075191604c801c8d645cd620843000536e59805cc210c0014f09059471591320041f660651c9314c0014e8905d4624c931006176177318d215000195875201754c9310062edd984085300c00162d9510a63509200061ddd481591604c8014cf935d1624843000707d95745cc214c0018e8966087054d100052b648415da42cc001a356520542504300063698c805d5320840183c841957118930007b0645624c5300c00193b7460253486500070d59574984210c00187a8619670c8530004b564c80549610c8014ce981d9324c5200041fa5c815516394001a4e856087058c210061721d8558d5208401cc77358a614843000595e558058e21084010f6985d921084300052ba5d64989210c0014cc965cd32905200051d64450dd9548c80183d8759664084300052b65d64988210c0010f7985c47158e200043ee61701c16308401a1d855907058c210052be49655d0214c00145d93140765513200729dd262985210c0016399419770595320068750d85d016388401a2d65e1171588300050f65276d95214c0010df985cc73588100052b65d64588210c0018db7660c214c0300062b61974c84210c001a1d536107558c200062da1c7498521cc001c1d65593734843000729dd162985210c00185d85dcc6348520006691d0815d132480014ad941c9624c430007b058931885300c0018e980dcc62549310068bd958214064484014ad9210476551320073264173588210c001a5865201324c5300042fa63435ca6190c0185d86e1573086500061dd97815d1324c00185d65e0d729043000713594724c9310c0013c592205544c931006691d0814c921480014ad9210576cca400057264a80dcd218c0014b595190715913200533259734ca5148001c55655ce61084300071359773589210c0014cf9259573085300061761d65087300c001a1d65610214c0300053ce4165dc5644c8019576560c7150910004f264c82505304800183d756107558c2000653e1d524c83294001c2e755d36208530007075517354f6250001a376520542505300052be51811d932480010f5981c46350921005aa65081589300c0014ae97591624843000693214825c163084010df985cc7358
  | 7 => 0x8430006a3210835c5620c0014ad9421d624c4300070bd9574c84214c00183c84195718c9300060fd97845c4624c00149d961d073484300043e660631c154480010f7985c47158b300068754d841d563880014ea960c8705953200732a4173588210c001c1f641cd53549210052b65072d89514c0018eb966087054d100060fd97845c6324c0016a994205628c0300053624185dd9320c8010be989917298430006a919081593324c8010f7985c471588300059364c50189524c401c8f741cd6248430005872595454d434c4014af9460572d94300070ed95749c0214c0014b9940c870595320042f6607498d21c4001a2f6560850d91210068b54984d45628c001a5865201658c9320060fa1d65991210c001a4d5360853189310053ca44321c1654c8014ad9210476551300068b995841c5620c001e456354d5248421006876115314d618c8014cf93605721815300639dd8815d1320c80162d9414362549310052b65373588210c001a8f84e0d71588300063360d621c5420c0010ef985c872d8d540071559773585210c0018d76160c7150930005a9e518758a610c0010bd989d464d8d210060f597845ca610c001c4d755cf62085300068d595841c9610c0016a5942056298430006f060d210853048001a2e65e11719883000716d95739c0214c00183f75612624c2100060f5d1851d1620c401c4f76dd5524c8320053c640329c76488001475950c871591320063a60175189324c4018d53121d43d89100062b613711c5620c00145d96d4d7198a530051764c501d9544840183f855917098c210053c640321c5655080183f85d917018d21005966548758e600840147994194705953200707595745cc210c0016c593a07628853000517e5f659cc214c001a39855907358021006aa61162086300c00145d97d4e7694f210070d59774585210c001659951cd63580210072359173988210c001659952016398021006b260d62905300c0010bd981d0634852000517a587354d52484014bb905d7644c921007075d16394c219400143d95ddb7448530006356077418d3248001a5553a0453586320070d99574584210c00183d85590735802100687615841c1630840145d931427694d2100693217825c1630840145e9714f6354d210068e993855ce600840183e87d9474485300063358d821c153084010fb98dd8214c03000707595749cc210c00145d951cd635802100687a16841c163084014b9901d46418d210043ba6176484210c0010bf985d074d893000497e5580dd9630840187565e05744c830005352457418d324800183d8719450191210070e9d3659c0214c001cc973d8a70085300062b611711c5620c0014f1910c8705953200627ddb84485300c0018d76260c71509100068d59481591544c801a3985590739802100716596739c02
  | 8 => 0x4110000105c046fc004bc0218802000005cc1f00000014f300c10014080c4040001102c00014010942400806019d10084c010170000006c3210005014151a40a02c5127805198000ec1101c1418879008210900c01409010020080c0080d2283b0054d01c190040400025190010000101c8f000000180f00024004293981b40c300001605440000030d81600000204220000f080080300116c2a038023bc26009e39f40600018024050217e0001801c0f0001d0380005c00000050280000402020001ec7b090fa2d404004000080100c5603c0015c00074020f0030d4710080405405000000000000c070135400004000277e4230b4021d5d3034029b0130100b544941177a1840d0bc024f02a00df800000488010000408c1b0286603c5d040023a80a01d04090110040c0040863c022403218000028527400b01063bd80b010802b40006040000140cc0b0c8250880002c6c0040073828004150140403c2f00c5c040010242b00c041480a044008c40005c0800085000012980212801034040300e0141b000011400112d521882b008e6594020051ee5d655c0210c00145d9308775582430060fe17645c3324840145f9758e5308650006b260e801c5620c0014ad9210776553300050e650651c1654c80183f75e11614c0200051e65f659c0214c0014e697205624843000687e16645c2630840107f976144218d200053364b655cc210c0018ad865937354b20007315cd62584210c0018d5316087650d100060fa1d651d1210c001caa74589700
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x514201a0033080408c0300407b52420cab9a4298002919a41d4805d532cc401512d28c840ac9992640080f6a295dd874485300064a10a4830a992c21900203da8a5276195214c00148cd20ea402ea992620080f6a48519170cc92100407b52420cab8c64980020e8a9481831d95244001c0b32cc8c18e2a16620080f6a484195711893000546140b2902b22a899002919a41d4805d5320c80101ed490a3a2c690a4000a8968464608411953000524b4a3a102ba2649000203da9a1c65dd1214c00150cd20ca402cb1926400e051946460c7150910007050c832b04382a68800203da9214645c0634840101ed490a322e018a4200e0a992656087054f2000407b52420eab0a60100032a084245844c9600c80160cd20cbb98e0b2a6400b0969464dc8715913200524b4a3a102ba2659000203da91d484585604c801492d28e840ae899064008352a56260c7150910
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x5221b5210916113258032005211b4214906153258432
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x124e
  | 2 => 0x138d
  | 3 => 0x8e
  | 4 => 0x98d
  | 5 => 0x128e
  | 6 => 0x9cd
  | 7 => 0x12ce
  | 8 => 0x168d
  | 9 => 0xb0e
  | 10 => 0x140d
  | 11 => 0x154e
  | 12 => 0x24d
  | 13 => 0xb4e
  | 14 => 0x144d
  | 15 => 0xccd
  | 16 => 0xcce
  | 17 => 0x15ce
  | 18 => 0x170d
  | 19 => 0x9c995
  | 20 => 0x140995
  | 21 => 0xcc995
  | 22 => 0xcc996
  | 23 => 0x15c996
  | 24 => 0xd4995
  | 25 => 0xcd516
  | 26 => 0x1689d5
  | 27 => 0xec9d5
  | 28 => 0x17c9d5
  | 29 => 0xb52d6
  | 30 => 0x15d2d6
  | 31 => 0xed695
  | 32 => 0x17d695
  | 33 => 0x154b16
  | 34 => 0xb4b16
  | 35 => 0xd0b16
  | 36 => 0x160b16
  | 37 => 0x171415
  | 38 => 0xd1556
  | 39 => 0x161556
  | 40 => 0xccb55
  | 41 => 0xccb56
  | 42 => 0x170b55
  | 43 => 0xe8b56
  | 44 => 0xcd6d5
  | 45 => 0x15ccd6
  | 46 => 0x170cd5
  | 47 => 0x1a0d
  | 48 => 0x5cd
  | 49 => 0x1a4d
  | 50 => 0x10e
  | 51 => 0x2cd
  | 52 => 0x188e
  | 53 => 0x18ce
  | 54 => 0x98955
  | 55 => 0xb4956
  | 56 => 0x98cd6
  | 57 => 0x995d6
  | 58 => 0x150cd6
  | 59 => 0x15d516
  | 60 => 0xb4e96
  | 61 => 0x9d695
  | 62 => 0xb1556
  | 63 => 0xb0b56
  | 64 => 0xb4cd6
  | 65 => 0xb5715
  | 66 => 0xb4cd5
  | 67 => 0x16ccd5
  | 68 => 0x1716d5
  | 69 => 0xcd715
  | 70 => 0xcd5d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 41
  | 8 => 1157
  | 7 => 4839
  | 6 => 4719
  | 5 => 954
  | 4 => 32
  | 3 => 2
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 10 => packedAt gbK10 (i*15) 6
  | 9 => packedAt gbK9 (i*26) 17
  | 8 => packedAt gbK8 (i*37) 28
  | 7 => packedAt gbK7 (i*48) 39
  | 6 => packedAt gbK6 (i*59) 50
  | 5 => packedAt gbK5 (i*70) 61
  | 4 => packedAt gbK4 (i*81) 72
  | 3 => packedAt gbK3 (i*92) 83
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 10 => gbHint (packedAt gbK10 (i*15+6) 9)
  | 9 => gbHint (packedAt gbK9 (i*26+17) 9)
  | 8 => gbHint (packedAt gbK8 (i*37+28) 9)
  | 7 => gbHint (packedAt gbK7 (i*48+39) 9)
  | 6 => gbHint (packedAt gbK6 (i*59+50) 9)
  | 5 => gbHint (packedAt gbK5 (i*70+61) 9)
  | 4 => gbHint (packedAt gbK4 (i*81+72) 9)
  | 3 => gbHint (packedAt gbK3 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 10 => 2*((h/1+packedAt gbK10 (15+(h % 1)*1) 1) % 1)
  | 9 => 2*((h/41+packedAt gbK9 (1066+(h % 41)*6) 6) % 41)
  | 8 => 2*((h/427+packedAt gbK8 (42809+(h % 427)*11) 11) % 1157)
  | 7 => 2*((h/1627+packedAt gbK7 (232272+(h % 1627)*13) 13) % 4839)
  | 6 => 2*((h/1601+packedAt gbK6 (278421+(h % 1601)*13) 13) % 4719)
  | 5 => 2*((h/325+packedAt gbK5 (66780+(h % 325)*10) 10) % 954)
  | 4 => 2*((h/17+packedAt gbK4 (2592+(h % 17)*5) 5) % 32)
  | 3 => 2*((h/7+packedAt gbK3 (184+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe3c1e1fe1fc038e03ffe005304fc37c4fc
  | 1 => 0xf0e01c01fe1fe1ffff00380ffcac3b30c8f8cf
  | 2 => 0xff001ffe001ffe003fffc00fff30c3c30f0f0f
  | 3 => 0x1fffffe000003ffffff003c0fc03f00ff0
  | 4 => 0x1fffffffffffc000000003ff0003fff000
  | 5 => 0xffffe000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x121c0c0a02e0242982089621801005413c45c
  | 1 => 0x1042440062022091a90110a4a80419304058c5
  | 2 => 0xaa04895200155404124a8049513042c10d050a
  | 3 => 0x81625554000092495268022c0ac02e00aa0
  | 4 => 0x88111bb99999992e0006030043fb0003bea000
  | 5 => 0xcc9e0030110110300018040183fef7a8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 6, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 6, 0, gbRaw),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 5, 0, gbRaw),(0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 4, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 5, 0, gbRaw),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 4, 0, gbRaw),(0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000, 5, 0, gbRaw),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36326
namespace PEqualNP.Outside.L_meta_36326
open PEqualNP.Outside.L_meta_36326.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 4 := bs0_3_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 2 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 2 := bs3_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 29 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 473 := (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 632 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := bs4_6_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bq5_3_0 : Interval q5Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq5_3 : Interval q5Atlas 3 0 9 := bq5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 14 := bq5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_5_0 : Interval q5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_5 : Interval q5Atlas 5 0 1 := bq5_5_0
theorem allq5 : ∀ k ≤ 5, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_3 i (by omega) hi
  · exact allq5_4 i (by omega) hi
  · exact allq5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 9 := bq7_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_4_0 : Interval q7Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq7_4 : Interval q7Atlas 4 0 14 := bq7_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_5_0 : Interval q7Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_5 : Interval q7Atlas 5 0 1 := bq7_5_0
theorem allq7 : ∀ k ≤ 5, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_3 i (by omega) hi
  · exact allq7_4 i (by omega) hi
  · exact allq7_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_2_0 : Interval q8Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 3 := bq8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 6 := bq8_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_4_0 : Interval q8Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_4 : Interval q8Atlas 4 0 1 := bq8_4_0
theorem allq8 : ∀ k ≤ 4, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_2 i (by omega) hi
  · exact allq8_3 i (by omega) hi
  · exact allq8_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_2_0 : Interval q9Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq9_2 : Interval q9Atlas 2 0 4 := bq9_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_3_0 : Interval q9Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq9_3 : Interval q9Atlas 3 0 6 := bq9_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_4_0 : Interval q9Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_4 : Interval q9Atlas 4 0 1 := bq9_4_0
theorem allq9 : ∀ k ≤ 4, ∀ i < count q9Atlas k, checkRow q9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq9_2 i (by omega) hi
  · exact allq9_3 i (by omega) hi
  · exact allq9_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_3_0 : Interval q10Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 1 := bq10_3_0
theorem allq10 : ∀ k ≤ 3, ∀ i < count q10Atlas k, checkRow q10Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq10_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_2_0 : Interval q11Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 4 := bq11_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_3_0 : Interval q11Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 6 := bq11_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_4_0 : Interval q11Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_4 : Interval q11Atlas 4 0 1 := bq11_4_0
theorem allq11 : ∀ k ≤ 4, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq11_2 i (by omega) hi
  · exact allq11_3 i (by omega) hi
  · exact allq11_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_2_0 : Interval q12Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 3 := bq12_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_0 : Interval q12Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 6 := bq12_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_0 : Interval q12Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_4 : Interval q12Atlas 4 0 1 := bq12_4_0
theorem allq12 : ∀ k ≤ 4, ∀ i < count q12Atlas k, checkRow q12Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq12_2 i (by omega) hi
  · exact allq12_3 i (by omega) hi
  · exact allq12_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_2_0 : Interval q13Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq13_2 : Interval q13Atlas 2 0 3 := bq13_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_3_0 : Interval q13Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 6 := bq13_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_4_0 : Interval q13Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_4 : Interval q13Atlas 4 0 1 := bq13_4_0
theorem allq13 : ∀ k ≤ 4, ∀ i < count q13Atlas k, checkRow q13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq13_2 i (by omega) hi
  · exact allq13_3 i (by omega) hi
  · exact allq13_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_3_0 : Interval q14Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 1 := bq14_3_0
theorem allq14 : ∀ k ≤ 3, ∀ i < count q14Atlas k, checkRow q14Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq14_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_2_0 : Interval q15Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq15_2 : Interval q15Atlas 2 0 4 := bq15_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_3_0 : Interval q15Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 6 := bq15_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_4_0 : Interval q15Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_4 : Interval q15Atlas 4 0 1 := bq15_4_0
theorem allq15 : ∀ k ≤ 4, ∀ i < count q15Atlas k, checkRow q15Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq15_2 i (by omega) hi
  · exact allq15_3 i (by omega) hi
  · exact allq15_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_2_0 : Interval q16Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq16_2 : Interval q16Atlas 2 0 3 := bq16_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_0 : Interval q16Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 6 := bq16_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_0 : Interval q16Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_4 : Interval q16Atlas 4 0 1 := bq16_4_0
theorem allq16 : ∀ k ≤ 4, ∀ i < count q16Atlas k, checkRow q16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq16_2 i (by omega) hi
  · exact allq16_3 i (by omega) hi
  · exact allq16_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_2_0 : Interval q17Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq17_2 : Interval q17Atlas 2 0 4 := bq17_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_3_0 : Interval q17Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 6 := bq17_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_4_0 : Interval q17Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_4 : Interval q17Atlas 4 0 1 := bq17_4_0
theorem allq17 : ∀ k ≤ 4, ∀ i < count q17Atlas k, checkRow q17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq17_2 i (by omega) hi
  · exact allq17_3 i (by omega) hi
  · exact allq17_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_2_0 : Interval q18Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq18_2 : Interval q18Atlas 2 0 4 := bq18_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_3_0 : Interval q18Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 6 := bq18_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_4_0 : Interval q18Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_4 : Interval q18Atlas 4 0 1 := bq18_4_0
theorem allq18 : ∀ k ≤ 4, ∀ i < count q18Atlas k, checkRow q18Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq18_2 i (by omega) hi
  · exact allq18_3 i (by omega) hi
  · exact allq18_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_2_0 : Interval q19Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 4 := bq19_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_3_0 : Interval q19Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 6 := bq19_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_4_0 : Interval q19Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_4 : Interval q19Atlas 4 0 1 := bq19_4_0
theorem allq19 : ∀ k ≤ 4, ∀ i < count q19Atlas k, checkRow q19Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq19_2 i (by omega) hi
  · exact allq19_3 i (by omega) hi
  · exact allq19_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_2_0 : Interval q20Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq20_2 : Interval q20Atlas 2 0 3 := bq20_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_0 : Interval q20Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq20_3 : Interval q20Atlas 3 0 6 := bq20_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_4_0 : Interval q20Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq20_4 : Interval q20Atlas 4 0 1 := bq20_4_0
theorem allq20 : ∀ k ≤ 4, ∀ i < count q20Atlas k, checkRow q20Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq20_2 i (by omega) hi
  · exact allq20_3 i (by omega) hi
  · exact allq20_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_2_0 : Interval q21Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq21_2 : Interval q21Atlas 2 0 3 := bq21_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_3_0 : Interval q21Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq21_3 : Interval q21Atlas 3 0 6 := bq21_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_4_0 : Interval q21Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq21_4 : Interval q21Atlas 4 0 1 := bq21_4_0
theorem allq21 : ∀ k ≤ 4, ∀ i < count q21Atlas k, checkRow q21Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq21_2 i (by omega) hi
  · exact allq21_3 i (by omega) hi
  · exact allq21_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 32 := bgb_4_0
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
theorem bgb_5_864 : Interval gbAtlas 5 864 90 := block_range (n:=90) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 954 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864))))
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
theorem bgb_6_4704 : Interval gbAtlas 6 4704 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4719 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2496 bgb_6_2592)) (concat bgb_6_2688 (concat bgb_6_2784 bgb_6_2880))) (concat (concat bgb_6_2976 (concat bgb_6_3072 bgb_6_3168)) (concat bgb_6_3264 (concat bgb_6_3360 bgb_6_3456)))) (concat (concat (concat bgb_6_3552 (concat bgb_6_3648 bgb_6_3744)) (concat bgb_6_3840 (concat bgb_6_3936 bgb_6_4032))) (concat (concat bgb_6_4128 (concat bgb_6_4224 bgb_6_4320)) (concat (concat bgb_6_4416 bgb_6_4512) (concat bgb_6_4608 bgb_6_4704))))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2688 : Interval gbAtlas 7 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2784 : Interval gbAtlas 7 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2880 : Interval gbAtlas 7 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2976 : Interval gbAtlas 7 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3072 : Interval gbAtlas 7 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3168 : Interval gbAtlas 7 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3264 : Interval gbAtlas 7 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3360 : Interval gbAtlas 7 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3456 : Interval gbAtlas 7 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3552 : Interval gbAtlas 7 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3648 : Interval gbAtlas 7 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3744 : Interval gbAtlas 7 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3840 : Interval gbAtlas 7 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3936 : Interval gbAtlas 7 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4032 : Interval gbAtlas 7 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4128 : Interval gbAtlas 7 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4224 : Interval gbAtlas 7 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4320 : Interval gbAtlas 7 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4416 : Interval gbAtlas 7 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4512 : Interval gbAtlas 7 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4608 : Interval gbAtlas 7 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4704 : Interval gbAtlas 7 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4800 : Interval gbAtlas 7 4800 39 := block_range (n:=39) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 4839 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat bgb_7_864 (concat bgb_7_960 bgb_7_1056)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344)) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632))) (concat (concat bgb_7_1728 (concat bgb_7_1824 bgb_7_1920)) (concat (concat bgb_7_2016 bgb_7_2112) (concat bgb_7_2208 bgb_7_2304))))) (concat (concat (concat (concat bgb_7_2400 (concat bgb_7_2496 bgb_7_2592)) (concat bgb_7_2688 (concat bgb_7_2784 bgb_7_2880))) (concat (concat bgb_7_2976 (concat bgb_7_3072 bgb_7_3168)) (concat (concat bgb_7_3264 bgb_7_3360) (concat bgb_7_3456 bgb_7_3552)))) (concat (concat (concat bgb_7_3648 (concat bgb_7_3744 bgb_7_3840)) (concat bgb_7_3936 (concat bgb_7_4032 bgb_7_4128))) (concat (concat bgb_7_4224 (concat bgb_7_4320 bgb_7_4416)) (concat (concat bgb_7_4512 bgb_7_4608) (concat bgb_7_4704 bgb_7_4800))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_96 : Interval gbAtlas 8 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_192 : Interval gbAtlas 8 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_288 : Interval gbAtlas 8 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_384 : Interval gbAtlas 8 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_480 : Interval gbAtlas 8 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_576 : Interval gbAtlas 8 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_672 : Interval gbAtlas 8 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_768 : Interval gbAtlas 8 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_864 : Interval gbAtlas 8 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_960 : Interval gbAtlas 8 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_1056 : Interval gbAtlas 8 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_1152 : Interval gbAtlas 8 1152 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1157 := (concat (concat (concat bgb_8_0 (concat bgb_8_96 bgb_8_192)) (concat bgb_8_288 (concat bgb_8_384 bgb_8_480))) (concat (concat bgb_8_576 (concat bgb_8_672 bgb_8_768)) (concat (concat bgb_8_864 bgb_8_960) (concat bgb_8_1056 bgb_8_1152))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 41 := block_range (n:=41) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 41 := bgb_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_10_0 : Interval gbAtlas 10 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_10 : Interval gbAtlas 10 0 1 := bgb_10_0
theorem allgb : ∀ k ≤ 10, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  · exact allgb_10 i (by omega) hi
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
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 6 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 6 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 4 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 0, 8),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 0, 16),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 4 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 5 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 40, 42),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 5 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0feeefeeafeecfac0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq5 : Complete q5Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 6 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 6 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 6 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 6 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 8 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa : Sig) 5 :=
    slice_correct (ms:=fixRows 8 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555 : Sig) 5 :=
    slice_correct (ms:=fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 32 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : Sig) 5 :=
    slice_correct (ms:=fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 4 :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : Sig) 5 :=
    slice_correct (ms:=fixRows 16 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276943552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_36326.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,4]⟩,⟨.or,[5,6]⟩,⟨.or,[2,4]⟩,⟨.and,[0,7]⟩,⟨.and,[1,8]⟩,⟨.or,[9,10]⟩,⟨.or,[0,5]⟩,⟨.and,[1,12]⟩,⟨.or,[0,2]⟩,⟨.or,[13,14]⟩,⟨.and,[3,15]⟩,⟨.or,[11,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 17⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 12 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_36326

open PEqualNP.Outside.L_meta_36326 in
theorem PEqualNP.Outside.L_meta_36326 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq5 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allgb)
