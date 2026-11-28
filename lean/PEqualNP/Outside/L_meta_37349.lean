import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37349.Model
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


end PEqualNP.Outside.L_meta_37349.Model

namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
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

def SBf (j : Nat) : Nat := [4, 5, 7, 7, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37349

namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def s0K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt s0K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 30 s0Pos s0Neg, 0xfcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 2 => 0xfff81ffffffffffc0fc07ff03fffffff98e3ff
  | 3 => 0xffffffff81fffffff0007ffffff81fffe0ff8f
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 2 => 0x88524c892091831405582594128e525498a0d5
  | 3 => 0x30a111120d2224a950224a29a5510ca960570a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831f503e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1def800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc00400020000c024000000601200008a002180022002300000146ed32ff42fe42fc21ff32ff20be40fe32fe10fe40ee32fc41ff40fd10fc10fc20ff30fe21fc42fd30fc40ff43fd21bc40fc43fd31fd41fd32fe20fd43fd20fc32fc31fe31ff21fe30ec20ff31fc30ff10fe43ff41fe41ee20fd40fd42
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x61e0c0000200346100008000906b83a243930029180000c1800010580380040e023c519047c000013c54442d8a4885b54e32b72906174514c2dea4a06a10020d6200413d54c42bea6a0d714d10b7a92836f524c35881104f95310f5280416f53882eea2984f95031f5a0041ad32902bca790ee102309faa2613d54c82b8a6a0db54841b7296616d52d02daa421f354c20f4200416c525027ca9985b54b30e7298413f5448374a0205b54b31b729083b840c8278a8905754c20b6a9c41ae329039a6418db94232dc206213d54cc37080085bd4910b7296216e5290ef4a018db94843b7a98416d52c42daa6105b94832af29841b8404c35c81104f95320bca8487ae40082daa521db54831bc282837b5050ad8a0994f550319eaa0436c52506dca1105b94831b728041ad32102dca598ee10020bc2828579500c6daa4184f942409f2a0433c544c2baa790cfd5110e6994637a5090e7ca0205354c20e699261cd32cc2bea68873d4d32d7190817b50506dca5a05b14930
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8000000001081bc006800601c000000000e4d6394b10ca94840c424d6594c20d254f400830d5310020c254c400830d5390020d24c9500c72953100208e18154087453214530e254c40082a8604c840cad4c40083285210130e294c40083195310020e24c8404c3305110130aa98240083495310020
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8015097394840c4380990a220261425d65310020
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => 2*((h/47+packedAt s2K4 (2673+(h % 47)*7) 7) % 99)
  | 3 => 2*((h/28+packedAt s2K3 (798+(h % 28)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s2K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff01fc0ff83ff83ffffff03c07ccffe67
  | 1 => 0x1f80fffffffffffc0ffc1f81ffffffff311fff
  | 3 => 0x1fff03ffe000fffff0001ffe1ffc007fc1e387
  | 4 => 0xe00003ffffff03ffffffe0001fffff83fe03f8
  | 5 => 0xfffffc00000003ffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc48a2811c4852880b380a58a2b224524466e63
  | 1 => 0x412611224910411404a40aa1454493491114ad
  | 3 => 0x96145b4483b693ad5062936d16ea0a73c1a386
  | 4 => 0x1458a28912241aca694ac04818b32c22ea0350
  | 5 => 0x1860c30e1c38e3738e731c7180c03043bdd800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x10835004c50034010846c100019f40ffe20fe31ff42be40fd42fc42fe21bf42fd41fd32bc40fe30fe10fe40fe41ff43fc10fd31fe43ff30fc21fd10fd21fc40fc43ff21fd20fe42fe32ff41ff32fd43fc20fc41fc31ff20fc32fd40ff31ff40bd42fc30ff10fd30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4500332c0811600686020000300442463400003164c48e00007000000b022240981000000e3c3095124488053814006000c0000c50b001a035a85194f15130bd280437b5050adaa4205714d10d6a12413e54c427aa9885e94241b6292633d521027ca8214b54840b6a96616d520c67ea8906b50b209eaa6433f544c27ca1205bd49109faa263ad424caf4a1194f95021b7290813e548ca7aa92157d4d10b729661b840c837080106e94040dc2006179509067aa9194f55032b7a92635d53c8278a9105e14143b6a908778504c67ca990ded41319eaa0413d54c82f2a018cf95320d6a14437a500c770a0a16b508219e2a263af5250a7aa5206b948409f2a0413d54cc278a8885b149109f280813c544827ea9106ed41429faa221b8404435aa4205e540219f2a065b840842bca7904f141429f2a063785050adca5a0ee10330af298437b5050edca421cf943429c282855d53086daa5a0cf550319f2a6616e520c6f2a1194f55021
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x900100080004201804000000000005032852101108e59440082a86050b20aa58840442a86050932c694c40c832860548408b19542482a86050a32ca509508ca2d6295310aa18142886a96210320ca94840cc3294254021c354d42086a96210330aa18142086a96210210aa588400c2386055032c354d42c823860553218b588544c3185310110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x400000704a98c0a10438254c6050b20c14a6b108190608535884044214bb0a4202210a5da5210330
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/21+packedAt s3K5 (704+(h % 21)*6) 6) % 44)
  | 4 => 2*((h/65+packedAt s3K4 (2430+(h % 65)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s3K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s3K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf03ff80ffe1f830ffe1ff83fc3fc0f019e77cc
  | 1 => 0xfffffff07ffffff03fe0fffffc1ffffe63f8ff
  | 2 => 0xffc1ffff801fffffc000ffc3ffe00fff838f0f
  | 4 => 0x1ffffffe003ffffff0003fffff003fc0ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x158c88e314252502ce093a25c12469188e33cc
  | 1 => 0x2080112120080020122048484409224820d055
  | 2 => 0x4315a2440d526355411896a2ab408cb3830d0a
  | 4 => 0xa29448849034a99a55204033292c023540ea0
  | 5 => 0x8c31870e719c73ee399ce730230308c3fbe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeec8c8ececc0c0eeeec8c8ececc0c0eeeec8c8ececc0c0eeeec8c8ececc0c0eeeec8c8ececc0c0eeeec8c8ececc0c0eeeec8c8ececc0c0eeeec8c8ececc0c0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x28c0be40bc40bd42fa20f920bf42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x35284904b54840
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s4K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s4K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3ffc07e0ffe0c3e0ffff07fc3c0ff013e767c
  | 1 => 0xffffff800fffffc00fc1fffffc00fffe23f87f
  | 2 => 0xfc0ffffff07ffffff001ff83ffff0fffc38f8f
  | 3 => 0xfffffff800ffffffe0003fffff003fc0ff0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x586447149314940e82d27425c24619190e363c
  | 1 => 0x2888890d242908c1056098ca6408a26a20d855
  | 2 => 0x1125122081408512901125208a920c9143028a
  | 3 => 0xa2ca2449080d2a6529a40843312cc022b40d60
  | 5 => 0xc30c3871ce71cfb9ce39ce70223088c3fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfac8fac8f8c0f8c0fac8fac8f8c0f8c0fac8fac8f8c0f8c0fac8fac8f8c0f8c0fac8fac8f8c0f8c0fac8fac8f8c0f8c0fac8fac8f8c0f8c0fac8fac8f8c0f8c0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc43de53102fea9996f50b41bea9881fa40102fca7a15fd5130baa88657f52842fca621fed0220fa880217e5310bf2a0195fd4d20bea9c417e529037a8621ded4121beaa4217f544867ca818778c932be28a657a50d0bf641887e0c020bea9843bc42107f680a05f54831f7a12853f544877883205fd4143dea1a85bf42102fca821f790f31ef98061fa20083f040085f15310fd986417d5310af8a4985f94010dea1481fb50486faa920df94840beaa021f920443f460905f14d20bea86435d53086fea2a07e50320bf29465f930483de65197b54841bf28485bf43502faa5105e14143bea86657d50d06faa910fe50020bf2a463de320c7bca610df94631bf29a21bf40903bc8698df14810fc984417f53043de85214f95320bf298817d53482faa7887754c21bf29e43f7318c7f260185fd4d42fd20641df308c3f621087e4c010fca0261795010efca9905f94c20bea86857d52906fea4985f95042be296217d53d02fca7a0de14121dfa1c8776510cbeaa2195f55032dea1e817d51d0ef8a498df94640fda82657f54082f4a010df94441be2a4657e520c37c8520dfd5030bf294877c54cc3b864185f95210bd28087f7100437a8620fe54041be2a2657d510c2bca7a16f95320ef29e217d544c3ee4310df54a30bfa92875f53482bca610fecc210bea9081f8400c3bea690dfd5230bfaa263be41506fca421df14940bf29021f621086fca9185f54d21bea80437e528c2fea0996f55021fa98c437e52d06fea990774c431fb08221dd4310f7a84205b94841bea86873d540cafca3187ed4143bfa82837d51842fea990efd0a42bfa90217d54086fca998fe90210bf286637d52843bc6518df54742ae29a417d53842faa8995f14d42bca84857c54886fca3a15794c40bfa9a43de304c2fca3997e54331dfa0883bc54487de4310efd0941fc200217d51082f8a8987754c41be29e217d51883dc4290df95321ef98863f8408827aa810df94442ef194617d53d0afaa8105f54443bea9c657e50886f8a6a07ed0120bfa9a81fb10442faa8905f94431bf2a2417e5090ff280205ed4143f699065dd43cc2baa7887790c32de208817a50106faa4185e54331bf29c213d54cc6fca1196fd0f42bf288617e50d07eca2195f15031dfa1c837c54cc7f240105f95310fd08021f95090bf660885f94030be29e43f6310c6faa3995f14c20dfa00817e5390efea818de14141bea9c43ed21086fca9997b90842ee992637c54442f8a810df54e40deaa663be4250bbca7a15f54032bf288657d51d02fca2085f55242beaa663dd5310278a8887dc4210fd900217e530c3f461887794c41bea9621f531486fea8996f55032bf294857d548c7bc6298df54e41bf2a243fa404437c80a05e94231fb90a437d54ccbea4210fe0c320bf288417d51102f2a118fecc230
  | 1 => 0xd54c82f8a0a0fdcc531ee29a437d53c8278a890fe0c210bea8e417e51907f681886f95021beaa221bd42506faa890df94e40fd204617c50486fca818fe88210fc28243bd54c82fca0205f54a21be28a617c504c6fca9195f95131beaa6215d53d0afaa3195f55031bf298837e50882fca88877cca32dfa1a857f52502fea790df54b30bf29463fa500cb7ca998de54041bf28c417a5090bdc8490df95032bea80877f54442fca010df54630be28a87f6411067ea8885f15030bf28c853d540c2f8a2907e101209f2a0657e52c42f8a918df94a41bf28c65f820c42fca6195fd5232bf284837f52442fca7a04f95331dfa1085f95010efaa7186f90d43df21083bf4310ef8a8107ed0330be292877d5490fde4210df95021bfa8a85dc328c7788520fed0240fba0a837c51502f8a8195f94e41bf2a0837f53c42faa121df14d21eea1a63bd411077e85206f95032bf290657d52d02fca5a1df94041be29a83ed20083ec6310cf95021af29e217d5110afaa1195f55330ef21887dc328c2baa620df54242eea1e63bf43d02faa3205f54843ae29a43bc54443f660107e14143bea9e837c548c2fca021fe4c310bfa8243f741906faa9195fd4543beaa4617f540cbbe6498fe0c110ee980617e50d0bf220087e94242dfa18837d5290ff4a198fe88110be2a2417f53507bc879877ccb31bf280637e51d0ff480105f95130be2a0217e50c86fea8907ec8120bfaa4637c53883bc64185fd4f20f6a10857f53883f280885f54331bfa8263fa5010fde41106f50040dea1e85dd53d0b7c83206fd5121fd284637c5050af6a0997e54231bf29843fb304c2fca1a1d794c41bfaa0217d53042f8a4a0ded4141dea1c837e5190efca9105f94b30bea8463fa300c2fca1205fd4c21bf29043ee42c86fca618df54642eea9e21dd320cafaa4085f54b31bea84437f5050bde64995f94842be292217c54883f460085f95132fd202617e51cc2fca1185f94210bf28665fa30882faa718df94231bfa92637e53882fca310f7d0d43be2a6657c53c82fca0105f54b41bfa8a61f920842faa9105f94d20fc206217f52c42f4a198df94443f729083f5310c6f8a6887e50230be294217d54902fca0195f94b40eea18657e54886f8a0995f54d10fb18a437c54c83f0a0995f54b43bf2a0417d524437e85a0de54032bea8865f950d0b7ca81877d0e43dfaa2217d52107bc86986f50842bc282657e520c7da8590df94b31bea9e437e540c3da8490fed4141bea80837e53c82f8a610df54c20bf29221fa50107f2a010df14c10dfa0c837e5010af2a010df94820ee988617d54c87f0819877cc832bf29c43de438cafea9885fd5210fda00617f54cc6fca6087e94021bea8063fb40043dc40905f94720bf28e817d528c6f8a710df94841bea94817d509077c822077cc430bfa9
  | 2 => 0x7418114051ec0f3080c001006541f010000007d07c280280400005028e3070100d423000050000f3280014804020000009200802014001200a01449138000344100818089c41043c79c0600006694031ac010000100004670250000402c3324818005060013e0140001c180040103c13000e30040000414144000fc084dc06080230000001c100082803c00000360540f038040700106c0e0881a0080c0017500c0b020c80e04410c1211000004cc008010543b0101c0081300004064022c4000180005801288183c83d0e4040440006801000004740e0780a0003c0040302c0f018261cc0c0d4020181a1003706c040080b000031700704826354100080302c1d0001c0280f4505001e1f20c324fc0022e600200a08010000a001844010080000000401ef98c617e5390bbea6905f15321bf2a021fb20883b86418dfd4941bf2a661bd540c2fea7085e94032bea9c857f54087be6318d7d4d21be29c21dd32cc7f28108774c630f719065dd434c2fea9985f15131bfa9a217f54886fca7885f55131bea8e617e53486fca210df14542bca8685ef20082fca2205f54042bfaa4417d53107f4a1a17d50441beaa6417f53083b8a6907750e32be2a421f850506f8a890df95040bfa8a417d540c2f8a0a1db54841bf294217f514cb7a86a05f54643aea98813
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3530867a60947329e1815310a5d63151109e994404837151940329b58a544c25f6354910cb548421067461551209ed81544863e6494f109758c540427a6015010ae583429025d6315220ae982421067a6015030c794d43d0a7965c80108f590524c63f6454d109e996204423f64544209b189534427b654c0309e5805150a7960951218fd91518c27561150328f592528435a53d031097d8d52907596094f109ed95300427a60150329ed8153d067761551329e58252d0f1d53508409718d54482786054a439e582544823e64951218f593528427b60548319bd89534423c6454221b618d204435953540419e98053086786054d219798c54086766114c20ce95030c826f6550842b658c400c2d963103309e583548c65d63951208f590530827965d0010b6181430ca3e6494820ab1894350a7b6055110ae982429067a6590110ce553400c27a6014c209e98353043586054c40c798e54c823e6494d10ced0d5010e5c6550d3097195434c63c64549109758c52c423d6414d20d694d30c4358534c120ae18143d0a5d63145429758e54c825e6394640ce152404427a60d5032d6d4c504867661150208f997425071f54d4d219e58251cca7b65480208f99353c826e6215031cb50d52106766115032cd951510ca5c63549109ed81524435853d4121d654d500863d65908418f592530c67960152219e18151d0e3d6414b108f992524435a53540419758c548871d63953209e58254c86d963100109e980540873954940219e5825344339544c030ae993200425f6354321d614f20482b9640c020d614f404823e6494a309e59630042b960106409798c540c739548c0309e983538863d6414f21d690d500ca3c64546329758e518836a52940418f590538423f6550441d650d50cc65c6354a409bd95210867a6094d219ed81540c73b43540419ed81548867b6055332c7590534827a6015332d554e21086da63c4210c754f401025d63d4b108f592534865e6315221cb54941106796015031cb553210865e63944109e580540865d63946409e580548c75a5394342d354e521065e63150109d98453c825f654c0309d584530826f62551318f992534867461551328f592528c25e6315020cb54a421063d6414c21ce1514044339545403297d95310c65e63148109ed81544c65d63d5021b6181324c67b60544428f99053c871d6494f10b618143cc277654c4319e99430442786054831d5cc9510cb1c5414d21ae590308435953940219e195404c26d6214c108f596540c31d53500409758c54c423e6494a108f990540ca3f6454221c754f421036952940419ed815290e7a6014542b6982314c73943543429e195404425d63150209e9835408738541412197596530863e65151109e5825348674654c521d650d5010e5e63150308f99352843386055030
  | 1 => 0x431d544c430d6cc6508c71e5350c41ae9824250b1c54d4d21ce50850507553254432ce153304425f6355121d694d50087556114d219e58354c873b4294242ce15030442796094e41cb15242486796095232b5584320c23e64951108f592538867a60d50209ed81518ca5e63946209dd95411075953940419e980520425e6394d219e9825190e6d62152319e580544c6b860504419e181548865d6315210b6181434c73a54903208f59353c827960d5331c795153086d5610ca309e982544cb5b53d41218f99454486796510010ce50d5010e5e63145429e583548cb5943540329d984530863e6494e219dd95210867b6054d2097997324c73a54cc3208f191518c2756115020d654e50d0ad8604c8329e181544cb1e6414d209e98053c86796508010b5584320c74e53948419798f52842786054a419b988548c67761551208fd91518ca7960153319e980524c73943540418f99053082b864440108f19151082796014c218f990540865c6354321ce153504872f4354841b6583318c2d5610ca31c7552320c27661d53309ed95400825d63944108f590530426e6215010d60ca508c67960d4e21ce951500867965cc020b698f10442796014f21da949501079943d03309798c54c426f65480209798c544423f6550842ce58254c823e6414931d694c40c42b86050c418f191534876952540419e59640082b86050f408f992530c66e6295130cd952510ca5e63951219bd95320ca7a6015331d614c404827b65440109b195424863f6454d219798e54c871d54cc430d654d401027561d533097d8d52042786055131c7952530867a658c1208fd954310f3a54503209ed8151d0ed86050e32d694e500875a53083109ed81529071e5450f318f9905308758538c1209e982538865d6314810d554d210867561d503297994534825c6355121c7d50534866e6214c10c798e540cb1d5494c21c799253c427b6054d219e580524c65f63551208f59252082b9640c1109758e54c866e6215021b658c408832d52d0441ced50504867a60152319e983530873a5494021ce951500caba64c81209e181544867a60d52319b189544c6ad62106409e5805350a7960d5021cb551210871d5454c21ce904505065c6354a41ae99320882776544010ced0d50d0b7151540329ed81544cb54538c521ae59030c82b86050e418f990540c25d6590c32ce550400c25e6514d21b618143cc7355454432d694f20c427b65500409e98254c86786055031d614c504867a65d0120ce55150cc6d46150d31ab588411026d6215310ce55250cc71e6315110ce1531044278654c1208f590538823e6414e108f596540867960d50329d987540cb5953543429e594300825e63d4b108f596540cad96310120d6580534823d64148109e983548cb1d540c830ce551500863c6454d108f99
  | 2 => 0xf3a0170680a010a9004053f005000300241b0003c090060a80c00000004010001105000004050f4000540300c650f000000030b80125c0b000040000e01c0b000150bc140048524c2d0543000060090062bc00078000340a000370002501000000030e4bb0600200d25000d10000e024013541f008000080c00825000b22d80604c942f0c70100528402000740240500c26004000402705c0000c084b800004000a003004d804806000020100002c1714c0200c02000023852b0001d160980040001c2300c2d0240001005050d701c011f802044691d00206c9e1d0001e01203801000050640000a7965d00309e982539067960150328f59053c833854881109e982548cb7251540329758e544cb3b54d4121c7951430cad863480209e982544871d63151109e996404c2b86050d428f990520425e63d53109ed8153c86796015332d690d5010e7a60d5331d550d510cb3554944329e596100425d63d4a108f592534425e63d502197596320c67865481109e98252d0e7b6054c428f59253c426e621531097d95320cb1d5310440c7551300c25e6315220d68c8504ca796094b41ce151204427860553329758c540871e63953318f593530865d63951219e594400c35a5354342b658c40c423f6550040d690d50cc6786054f419e582538863d64949109758f54c427a6094b419e582544cad9600ca30d354d52106ba64c83109798e54c827960d4c219e980544c7564354432ce952500cb5a32942318fd91524425e6315210ced08505072d6215121d694e501067b60551309b588540c63e6414e20c754e411025f6354a409798c530865f6550c439798e544835a538c3109e980540c63e6414d20b618132cc6d863482109e980548873954940328f99053c827a65cc1109e9805350a5e6394d208f99052c42786054f219e5825190f994350130ce95150cc71d54cc0309798c52c433a5494331d654e401037251940329e181518ca5c63548109b58854042756114f209e1815110a3e6414c109e98354c874e5354841ce580544
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2000008c000002002c00008000000000003700000003465cc5450110872ec2a060884397695030c8306a9ac420881465d2534c3108b2ed29881885287050d521070c2a4c788221465d0534c120c30a831a40884597614c4048314a94c121083541c14354432c2aa8b0864186196458053482a838264a88658658d6095320c32c6b00a8886195458c400c2a8b886528463865916094f10a32e72a2819061a6494f20c430d320a7902418a5486050441
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8198715263c41108198715063481108198799253c83108198799053c8120
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => 2*((h/235+packedAt s5K5 (17928+(h % 235)*10) 10) % 664)
  | 4 => 2*((h/186+packedAt s5K4 (20482+(h % 186)*10) 10) % 539)
  | 3 => 2*((h/36+packedAt s5K3 (1225+(h % 36)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81ff87c0fc3fe23e1f0f1fe078f03f8247c67c
  | 1 => 0xfe1fffff003fffc01fffe1ffff003ffc78f87f
  | 2 => 0xffe007ffffc3ffffe00ffe007fffc3ff8f0f8f
  | 3 => 0x7fffffc03fffff000007ffffc03f00ff0
  | 4 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xacc34c4e2a59460f0b8713253891a49a43c63c
  | 1 => 0x14440082188080400511204349020928105855
  | 2 => 0x8091114400a0092200a4408122482508d028a
  | 3 => 0x519666289220cb6556a0111264cb3023700d60
  | 4 => 0x61184430e33313b998cc999c008c2043eea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0fcecf8c0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q1K4 : Nat → Nat
  | 0 => 0x2220080030ee32df32f641f541dd32cd32bf41b541ed32bd41
  | _ => 0
def q1K3 : Nat → Nat
  | 0 => 0x20a86020985325071a65a0f14ca41ca992838d325078a64a0cd55241d299283a6325072e64a0d354e32
  | _ => 0
def q1K2 : Nat → Nat
  | 0 => 0x285638c941
  | _ => 0
def q1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 10
  | 3 => 11
  | 2 => 1
  | _ => 0
def q1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q1K5 (i*5) 5
  | 4 => packedAt q1K4 (i*16) 16
  | 3 => packedAt q1K3 (i*27) 27
  | 2 => packedAt q1K2 (i*38) 38
  | _ => 0
def q1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt q1K4 (160+(h % 10)*4) 4) % 10)
  | 3 => 2*((h/10+packedAt q1K3 (297+(h % 10)*4) 4) % 11)
  | 2 => 2*((h/1+packedAt q1K2 (38+(h % 1)*1) 1) % 1)
  | _ => 0
def q1Pos : Nat → Bits
  | 1 => 0xff0f3ce3ce3fcf1f8fc88e238fc7e3e3c074cf
  | 2 => 0xb7f03f03f023f7e3f1f0f03c0e78fcfcd24b33
  | 3 => 0x3bffc003ffc3f803fe3f003ff07f00ff238c3c
  | 4 => 0xc3fffffc0003fffc003fffc0007fff003c0fc0
  | 5 => 0x3fffffffffc0000003fffffff8000003ff000
  | _ => 0
def q1Neg : Nat → Bits
  | 1 => 0x10404404040201000020082012020001045
  | 2 => 0x4a1088888884a4060220912445085050924112
  | 3 => 0x85220251240902490059008920520a8a208c28
  | 4 => 0x1544124025120201249a248020648a0a240e80
  | 5 => 0x6a88a082080024924924c932490010109b6000
  | _ => 0
def q1Atlas : Atlas := ⟨5,rawDecor 62 q1Pos q1Neg, 0xffffffccfcfcfcc0ffffffccfcfcfcc0ffffffccfcfcfcc0ffffffccfcfcfcc0ffffffccfcfcfcc0ffffffccfcfcfcc0ffffffccfcfcfcc0ffffffccfcfcfcc0, q1N, q1R, (fun _ _ => 0), q1I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q5K4 (i*5) 5
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q5K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def q5Pos : Nat → Bits
  | 0 => 0x9f8e3cf9e3fc31ce38cce3cc7f98e198719e8b
  | 1 => 0xe7f03f3e039fc1ffc0f0fc7070e0ffe07650f3
  | 2 => 0xfbffc03ffc1ffe0fff3f007f80ff01ff88631c
  | 4 => 0x3ffffc0001ffff0003fff8000fffe000f83e0
  | 5 => 0x3ffffffffe00000003fffffff0000000ffc00
  | _ => 0
def q5Neg : Nat → Bits
  | 0 => 0x208286084504821441042084128a2490a08689
  | 1 => 0x9110890882904880a10445124204941425032
  | 2 => 0x0
  | 4 => 0xf6a492055352a104956da9020ad694122d83c0
  | 5 => 0x5f4920a5820329a926bad26b4c0418444f7800
  | _ => 0
def q5Atlas : Atlas := ⟨4,rawDecor 55 q5Pos q5Neg, 0xfefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q7K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q7K4 (i*5) 5
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q7K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def q7Pos : Nat → Bits
  | 0 => 0x9f8f38f9fc7c398e3e0e33cf8f9c319f01ae4e
  | 1 => 0xeff03f3e3f9fc1ffcff03c71f0e03fe3f25073
  | 2 => 0xf3ffc03fc01ffe0ff03fc07e00ffc1fc0c639c
  | 3 => 0x3ffffc0001ffff0003fff8000fffe000f83e0
  | 5 => 0x3ffffffffe00000003fffffff0000000ffc00
  | _ => 0
def q7Neg : Nat → Bits
  | 0 => 0x20818a0888848214404210828284948a108646
  | 1 => 0x0
  | 2 => 0x5120490112910280294405424290150246098
  | 3 => 0xfaa49205aa52a104956ab5004ad2ac0a4b8360
  | 5 => 0x5f4824a53003354929bd2a696c0308508f7800
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 47 q7Pos q7Neg, 0xfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcec, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q9K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q9K4 : Nat → Nat
  | 0 => 0x100ef20ed20df31dd31
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q9K5 (i*5) 5
  | 4 => packedAt q9K4 (i*16) 16
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q9K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/8+packedAt q9K4 (64+(h % 8)*2) 2) % 4)
  | _ => 0
def q9Pos : Nat → Bits
  | 0 => 0x79fe1fc7f0f1ff1c718f8fc3f1c1ff870b34f3
  | 1 => 0x7e1fe7f8ff01c7ff81f1f1fc3e01c3ff34c89f
  | 2 => 0x801ff800fffe07e3fe01fe003ffe03f8c70f1c
  | 3 => 0xffe00000fffff803fffe00003ffffc00f80fe0
  | 4 => 0xffffffff00000003ffffffffc0000000fff000
  | _ => 0
def q9Neg : Nat → Bits
  | 0 => 0x8424088120280201002824090444892011431
  | 1 => 0x1084810120240a008090108822089124104886
  | 2 => 0x5484292464094053201a41194940a52470518
  | 3 => 0x2081952488a1024ac5a4002a29293024b80ac0
  | 4 => 0x451116000cc924936949493300302040eea000
  | _ => 0
def q9Atlas : Atlas := ⟨5,rawDecor 31 q9Pos q9Neg, 0xfeeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x100007521ec43b487790e521
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x2950a21
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q10K4 (i*4) 4
  | 3 => packedAt q10K3 (i*15) 15
  | 2 => packedAt q10K2 (i*26) 26
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q10K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q10K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q10K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q10Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfd99fe39cff07f
  | 3 => 0xfffffffffffffffffffffffd7e1e4fc1f73993
  | 4 => 0xe7fe073fe07ce1c
  | 5 => 0xfbfff83fff80fe0
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff404220008410025
  | 3 => 0x289509244a2a892
  | 4 => 0x19115069424aa18
  | 5 => 0x60002921000540
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 58 q10Pos q10Neg, 0xffffffcccccccc00ffffffcccccccc00ffffffcccccccc00ffffffcccccccc00ffffffcccccccc00ffffffcccccccc00ffffffcccccccc00ffffffcccccccc00, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x103005531ec6374c7a98df31
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x2550e31
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q11K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q11K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q11Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfd9f3e39fe71cf
  | 2 => 0xfffffffffffffffffffffffdbe13cfc1cfb933
  | 4 => 0xeffe3f3fe0fce3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff404204008420045
  | 2 => 0x249461244a52912
  | 4 => 0x110080490080228
  | 5 => 0xe102ab25212d80
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 54 q11Pos q11Neg, 0xffffccccfcfcc0c0ffffccccfcfcc0c0ffffccccfcfcc0c0ffffccccfcfcc0c0ffffccccfcfcc0c0ffffccccfcfcc0c0ffffccccfcfcc0c0ffffccccfcfcc0c0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x40c0005d31ea637cc6a98f631
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x2550e31
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q12K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q12K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q12Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfd9f3e39fe71cf
  | 2 => 0xfffffffffffffffffffffffdbe13cfc1cfb933
  | 3 => 0xeffe3f3fe0fce3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff404204008420045
  | 2 => 0x249461244a52912
  | 3 => 0x110080490080228
  | 5 => 0xe102ab25212d80
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 46 q12Pos q12Neg, 0xffccffccfcc0fcc0ffccffccfcc0fcc0ffccffccfcc0fcc0ffccffccfcc0fcc0ffccffccfcc0fcc0ffccffccfcc0fcc0ffccffccfcc0fcc0ffccffccfcc0fcc0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q13K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q13K3 (i*4) 4
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q13K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q13Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q13Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def q13Atlas : Atlas := ⟨3,rawDecor 30 q13Pos q13Neg, 0xfcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
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
  | 1 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q14Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def q14Atlas : Atlas := ⟨3,rawDecor 30 q14Pos q14Neg, 0xfcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0x4000025f329a65b4cb7195d32
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q15K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q15K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q15Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q15Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 30 q15Pos q15Neg, 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q16K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q16K3 (i*4) 4
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q16K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q16Atlas : Atlas := ⟨3,rawDecor 45 q16Pos q16Neg, 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q17K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q17R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q17K3 (i*4) 4
  | _ => 0
def q17I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q17K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xdbf19f3f1c3f8d9c
  | 3 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 2 => 0x24ac285909932594
  | 3 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q17Atlas : Atlas := ⟨3,rawDecor 29 q17Pos q17Neg, 0xfaaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x40000045830bc6170c3d987830
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x2690230
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/15+packedAt q18K3 (75+(h % 15)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q18K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xbbc3ff3e3fe03fc
  | 1 => 0xfffffffffffffffffffffffdffc7fffc7ffc7f
  | 4 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 5 => 0xf3fff03fff00ff0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0x4479224e09261bc
  | 1 => 0xfffffffffffffffffffffff208b0412424a455
  | 4 => 0x111068249094a8a
  | 5 => 0xe224eb92418f60
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 51 q18Pos q18Neg, 0xeeee8888cccc0000eeee8888cccc0000eeee8888cccc0000eeee8888cccc0000eeee8888cccc0000eeee8888cccc0000eeee8888cccc0000eeee8888cccc0000, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q19K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q19K3 (i*4) 4
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q19K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 4 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q19Atlas : Atlas := ⟨3,rawDecor 51 q19Pos q19Neg, 0xeeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q20K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20K3 : Nat → Nat
  | 0 => 0xc000003b085e30e82170c37106c20
  | _ => 0
def q20K2 : Nat → Nat
  | 0 => 0x3808010c83008340c010
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
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 1 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q20Atlas : Atlas := ⟨4,rawDecor 43 q20Pos q20Neg, 0xaa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x60000800000803d087b30f041e443c187b20
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0xc000aa42cc2610d10a842442690f20
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/8+packedAt q21K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0x5af0f9cf1f8707cc
  | 1 => 0xffffffffffffffffffffffefff3fffe3fff8ff
  | 2 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0x251e929704b163cc
  | 1 => 0xffffffffffffffffffffff9022800121122055
  | 2 => 0xc44350a4844cd0a
  | 4 => 0x38821ac92608ea0
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 23 q21Pos q21Neg, 0xececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q22K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22K3 : Nat → Nat
  | 0 => 0x1400037196f20dc43b4cb610ed20
  | _ => 0
def q22K2 : Nat → Nat
  | 0 => 0x40a940086350c218d43c82a50232
  | _ => 0
def q22N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q22R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q22K4 (i*4) 4
  | 3 => packedAt q22K3 (i*15) 15
  | 2 => packedAt q22K2 (i*26) 26
  | _ => 0
def q22I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q22K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q22K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q22K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdbf3cf3c7e7e3673
  | 1 => 0xffffffffffffffffffffffeffdf3ff8f8ff99f
  | 2 => 0x72fe03cff00fce1c
  | 4 => 0x7cfffc0ffff00fe0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa41890441222a231
  | 1 => 0x1020040084040086
  | 2 => 0xd49aa1d2169ae18
  | 4 => 0x38102aa49410d40
  | _ => 0
def q22Atlas : Atlas := ⟨4,rawDecor 23 q22Pos q22Neg, 0xeeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def q23K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q23K3 : Nat → Nat
  | 0 => 0x8001203d107920f621e043d987830
  | _ => 0
def q23K2 : Nat → Nat
  | 0 => 0xc000b041482c907309843482690f10
  | _ => 0
def q23N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q23R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q23K4 (i*4) 4
  | 3 => packedAt q23K3 (i*15) 15
  | 2 => packedAt q23K2 (i*26) 26
  | _ => 0
def q23I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q23K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q23K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q23K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q23Pos : Nat → Bits
  | 0 => 0x56f0e7cf1c3f067c
  | 1 => 0xffffffffffffffffffffffe7ff07ffe03ff87f
  | 2 => 0xfffffffffffffffffffffffbfff9ffffc7ff8f
  | 3 => 0x7cfffe0ffff80ff0
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0x291e4c970589663c
  | 1 => 0xffffffffffffffffffffff9822d1092212a855
  | 2 => 0x44404024884428a
  | 3 => 0x38881ac93208d60
  | _ => 0
def q23Atlas : Atlas := ⟨4,rawDecor 15 q23Pos q23Neg, 0xf8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0f8c0, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xd1000308805101c800401fd10007f8c001fd43007fd0801fe40007fc4001fd41007f480017e50007fd04017d52007f50001fe20007f90401fc10007f4c401fe21007fd0001fd30007f50801fc40007f4c801fc41007f84001ff43007f8c401fd21
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x188200ff88630006faa520003f92084003be2802000fe84010005fac708003ff634840bffa8a4200ff58e41007ba6318003fb10840017d3008201bf98210046fea51882ffc30504016eb188000b758c410077e84a0802fc6150019fea8a8210ff54d42007f28108017fc51484017fb1c4000ff9824102ffaca9083bff31d04017eb188200ff4ca40005bec690003fd3188001feb1c4200bf98241005dac4208037d4194001fc8802000ffd093105ffe64a0803fd3104003bfa902000df48650005fac8988027f6544001fea0a4200bf59221005fac890803fe2184001bf18ca000ff58810005fec908002fd6310001ff3024200ff48640005bac7a1003fd3188405bfa942000bf18121005fac808002ff644c401ff20c2000ff50d21007fe829880b7c50840013eb2e8002bf98010087faa2a1003ee2148419fea928200bf58740005fcc3a1803fd3184001bea94620cff94141056f8a120803ff6448401bea14a00abf98441007fac520837ff3190401bea946006df14221005fac520803be4150401ffb1a820bff94d41056fea520802ff648c4017eb2462009fd9520006faa408003ff644c4017fb128605ffd4d21007fa6220003be41900017eb0e8600bf18543007fa6408017fe50484013fb2a8000ff8c5210077a872081f7c504c40bffaa24200ff90531005fec2a1802ff62504013eb288200bfd8c1008efea4a1803fd418c0013e302a400dfd8552007fa4318003fd41880017fb244200bf9844000578c8880037d4354801fa98a4200df94010006f8c2a9002fd63d0801dea1e8400bf58742007fa4208043fe50508017eb226400bf9874207ef8a099003fd43880017eb102000df54a4105ffe62a0802fc60504017fb1c2000bf58e41037f8a11081f7f524c401bf10ca000df54941005fac2200027f654c001fe9928200df54a10005f2c020802fc6050c0feea9a6200ffd0a31007fa8708003fe608c401fe3226200ff4ca10005fec690802ff624c401fea146000fd8c621007f8c098803bd4290001feb224200bf58e21005fcc110802fe61d0001ff20a4200bf18520005fec2a0003fd329041bfe1848200efd0e41005fac518837ff32904013fb2c4000ff8c620005bac7880037e5084001fea0c2005ff94521007f8c090803fd218400bfeaa24205ff99521007fac5080037d3294019be2828200ff4c640005fec918003dd324c40bbe2824200df90650006faa498803bf4190419ffb2a8200bfd8810004facb880337f52504197eb248200bfd8a10007f46110003bd41104017fb202000fe90210007fa85080037d3194001feb182000ff50531007fac9080477c5050c21be2828409ffcc441007ec6290802fd63484017eb142000ff98221007fec4a08027d6294001f6a124200bfd9220005fec290002fd63d04017eb242000bf18131
  | 1 => 0x120a830080000800060000218b8261380006085780000ad191805800060003c1c1800006022683830000285c0861120c89c180100c00050480006010100c1a3d3601800370000008810001114010026808161d0002000039e0143501019ae000000436000100020003e800021300004040102a502c2c0201008040282c000000218bc06008400001010044400198240807007fa6290803be4110001b6a924000f750d31007bc6298802ff614c001bea1ca000ff90630026fea520002ff644840bfea9a4200ff18143007fac690803fe3184001ff188800bff18d41007ea6310817ff6548401dea128205ff1952102ffaa290833fd5350401fe3028200dfd9152005fec6a081bff538840bfe2824200ff10531005fac6080237c508c401be302a403dfd4a30005fec710803fd63840017e30a6000afd91100077a86a1037fe6390401ff20c4000fe88210007fa8498802fe608c401dea
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7118152005ef724c6200057f744c6500066d6254a300067c50d91210057f7348650005d47150d310df5c504c9310067c6118152005bc7050d420067c5059132004ff7259210007e5424c521005bd72906400067d6454a10004fd72d92100076e4154920004fd7218143004ff7158c400ff3c5050e410076d41549200cf74508c6210067d73181520067d624c6500066f625493102f7a60486500067d6454a310076e31549200067d6454a30004ff7158f42006dc7158c40007e531885210057d748c650006fb3198041004fb7644010004fd72181410057c70549310e75c5050d310057f73506500067c5058d210057d7448650006785018121005787054a4004edf7158c41004fd72185430057d744ca501176f2018552006bd4358a41004ff7650e10006ef32d8941006bd63904400077531886500af74504c5210067f5259231006ef62d093110e6d7218152006bd61904400067c50d92310067f64549310076f7454920005bd76d0e410077850982310057d744c6500067f52592100076f7154920004ff764c4400ef3f529054109f5e3250e500073d4350a50004fd72d9010006ef31588410067c50d89310055d73185520067c5058a310057d73906500067c5059121004fe76d09310bf6c50509210b774508c5210067d62906500057f7150d520067c5058e210057f7150e50004fd72d91310067f4158a500067d6250650005bf73504410d75c508c531004fc7650d21006de32181430067d628c650006ed62486100073d439065000778501814305edf31d8d410066d6254a40005f976c4210005fa70105310067c50d89410073d52906400077850181410067c50d8943004ef72591310057c7054a310057d71181520057c7054a410057f74486500067f52d91310075d324c6500067f41181520057f714ca500057c70549410067c5058a410057f72506500067f52185430057d73486500076d4354920005bc7050e410057f7350a500067c6418152004bf76504410f73c5050941006ed624c8100067d71181520067c50d92210073d4050d520067d6154a300075d434c6500057f7150a50005bd71d0e411167f621855206cfe76105310057870548100073d4354a41007753148650006dc7158f42005dc7050d31006ed52d8931006bf63905410076870549200067c5059221004ff72590100067d7418152006f96284010006ad625044111f6f20d85520973f52906400057d741815204cfe76905310067f64181520067f4358a500067c76549410067d64548100067f61181520067f52d85430067e7418152005ef7250521006bd64d0a310057d728c650005bf744c440007695248210117752118552004fd768c4400077850181210ef3c50905410067c50d8d21005fb76502100a76c50885210067c50d8e21004fd7298231006be4118141
  | 1 => 0x9000010000b09040847001201020000620014001f0201180608180401000e02dc03032406020d0008630000e90b881c0307320301022f00070b000003733300000809470400001200030303070004010a000c2d00000a020d0f02012903400600010b01c400264b2b0200000c0424017b1a0ff3f5250e41006df7158f420067f43181520076a30549200067c4158a50006bd42181410066d6254a100067d4358a50006bd76904400067c5059231006785018143005bd72905410067c50d9131004fd71d8e20005de708c531005ef724c5210057d73886500c774504c6210067850181410067c41181520057f7250e500076f7354920004fd72181310067d43181520076d315492006edc3058e410057f724c6500067c50d8d410066d62548100057f744ca50004fd71181430057d7418552004ff72592310067f6550620005f47150a100067f41d96200076c7154920004ff7650d210077631486500067c5059131005fb76482100067f52590100067c50185430073d4250650004fd72982410057d71d91521073c5050d420067f64d8552005bf7150f42004f87059131006df7158c40005f77150a100067c5058e410069d6390440005ed72105310067f76549410057d748865000678509823111e7f62d85520067d6154a40005be76d094111f7521d85520067c50d8543004fd76d0a31006ad43588410076d42486500057d72906500067
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x6000000008200000021500280810200000009cb031c0c18a0001082162470204000001400200000800210043000000018eae2308c0a90021fa1c50591310069c208e0a948000c6f72141644c4014d90c98aa4900029b6085058e2100536c10a0b226400a6d82143644c401a70a038287208029e60850982310071ca10a03028200e3a4114060504014db04286c4a18031bd97724c620006aa280e2a1a6200a6d8214163904010fb0e280c2a18021f61f52185430059c402a520c800087e87105629400169b0638aa4900029e60850181410052ec1882302a400a6d821406150c014db04282c8988031e590705481000534c10a03024200a6d8214363484014db04282c5208021f61c411815200536c10a1b128200a6d8210460548018dae5388c0a90029760c4158a500051e422e2302a400caf7358941104014db04282c5188029b60850d8d4100637b10e0a926200b6982142608c40147f08b0aa51800393e0d6254a4000534c10a03028600c6d725cc6054801ab0a038286988029b608505912100536c1082b14a000e5a321406050c016d304280c0a18029b60b43181520049fc22e2302a400a6d821436488401c9906b12a520002976147158f4200536c10a0b246200a6d821436150c01a70a038286a10971b1db715492000536c10a1b246200a3f845c460548014bb06308c0a90038e503431815200534c10a03028200a6d82143624c4014d304284c1188030f5d0641815200536c10a1b224200a6d8214164884016d304280c0908031b5c97418152126363b0e2a924000d58509c2314c4016d303182a4900031b5c971181520071ca0286302a400b698214060504016d302382a4900029b60850d8e2100536c10a0b1a420096f825d131940014f50020ac5280029e6085018143
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x424500008000000000000000029e0c9580044006746000000154992142708c5310068aa51821406050c01a2a9460850181410068a105821406050c01a2841608501814100692e4d821406050c01155981407150d310068ad09821406050c01a489360850181430060be11725c46054801a4b3160850181430069224d82142608c401a4b3160850982310041b25d82141644c401545921407150d310068a651821406050401a483260850181430054a648411c15290001a4b9360850982310068a651821406050c01855835c461181520054a648501c1439040184c7660c715492000552648501c1434c40124c9660c71549200068a60a411406050401a2b42608501814100496662321406050c01a298250850181410044e660411c15290001a49828c850181430041be6372141644c401529921407050d42
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa000800420e00088a6a44160850181430050534e20b04280c0a1802849a7cc5821406050c01520d0926c10a13046200a0a69e9460850181430044535220b04280c0a0802a41a10c9821406050c01424d3926c10a03028600a90684936085018143
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4e
  | 2 => 0x124e
  | 3 => 0x12ce
  | 4 => 0x130e
  | 5 => 0xb0e
  | 6 => 0x140e
  | 7 => 0xb4e
  | 8 => 0x144e
  | 9 => 0x28c
  | 10 => 0x148e
  | 11 => 0xb8c
  | 12 => 0xb8e
  | 13 => 0x148c
  | 14 => 0x184c
  | 15 => 0xcce
  | 16 => 0xd0e
  | 17 => 0xe8e
  | 18 => 0x149316
  | 19 => 0xe9353
  | 20 => 0x140b16
  | 21 => 0xb4b16
  | 22 => 0x144b16
  | 23 => 0xd0b16
  | 24 => 0xb5416
  | 25 => 0x145416
  | 26 => 0x144b56
  | 27 => 0xccb56
  | 28 => 0xe8b56
  | 29 => 0x148b96
  | 30 => 0xd0b96
  | 31 => 0xe9496
  | 32 => 0xe8d16
  | 33 => 0x8e
  | 34 => 0x2cb
  | 35 => 0x19cb
  | 36 => 0x20e
  | 37 => 0x154e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 27
  | 7 => 264
  | 6 => 238
  | 5 => 82
  | 4 => 33
  | 3 => 9
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/16+packedAt gbK8 (702+(h % 16)*5) 5) % 27)
  | 7 => 2*((h/130+packedAt gbK7 (9768+(h % 130)*9) 9) % 264)
  | 6 => 2*((h/114+packedAt gbK6 (11424+(h % 114)*8) 8) % 238)
  | 5 => 2*((h/55+packedAt gbK5 (4838+(h % 55)*7) 7) % 82)
  | 4 => 2*((h/32+packedAt gbK4 (2310+(h % 32)*6) 6) % 33)
  | 3 => 2*((h/17+packedAt gbK3 (729+(h % 17)*4) 4) % 9)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc7c0f81e1ff80787c03fe003674f9e47c67c
  | 1 => 0xfff800ffffe07ffff8003fffcc9888fc78f87f
  | 2 => 0xf07fff001fff8007ffffc1fff0e0f0e38f0f8f
  | 3 => 0x7fffffe0000007fffffe003f00ff03f00ff0
  | 4 => 0x7ffffffffffff8000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x84c1c8590e0cc853864193218123438e43c63c
  | 1 => 0x1908002a22201234c802244a84088834105855
  | 2 => 0xa4125100155900811494819510e050c08d028a
  | 3 => 0x86caab740044126632b38022f00ad03700d60
  | 4 => 0x773cc5999665c0020c10043bd50003eea000
  | 5 => 0xce00300601180600443021183efefef8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 4, 0, gbRaw),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 6, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 5, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 5, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 5, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 6, 0, gbRaw),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 5, 0, gbRaw),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 5, 0, gbRaw),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 4, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 4, 0, gbRaw),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 5, 0, gbRaw),(0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000, 4, 0, gbRaw),(0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000, 4, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37349
namespace PEqualNP.Outside.L_meta_37349
open PEqualNP.Outside.L_meta_37349.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat bs2_4_0 bs2_4_96)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_480 : Interval s5Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat bs5_4_288 (concat bs5_4_384 bs5_4_480)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bq1_2_0 : Interval q1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq1_2 : Interval q1Atlas 2 0 1 := bq1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_3_0 : Interval q1Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem allq1_3 : Interval q1Atlas 3 0 11 := bq1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_4_0 : Interval q1Atlas 4 0 10 := block_range (n:=10) (by decide +kernel)
theorem allq1_4 : Interval q1Atlas 4 0 10 := bq1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_5_0 : Interval q1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq1_5 : Interval q1Atlas 5 0 1 := bq1_5_0
theorem allq1 : ∀ k ≤ 5, ∀ i < count q1Atlas k, checkRow q1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq1_2 i (by omega) hi
  · exact allq1_3 i (by omega) hi
  · exact allq1_4 i (by omega) hi
  · exact allq1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 1 := bq5_4_0
theorem allq5 : ∀ k ≤ 4, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_4_0 : Interval q7Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_4 : Interval q7Atlas 4 0 1 := bq7_4_0
theorem allq7 : ∀ k ≤ 4, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_4_0 : Interval q9Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq9_4 : Interval q9Atlas 4 0 4 := bq9_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_5_0 : Interval q9Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_5 : Interval q9Atlas 5 0 1 := bq9_5_0
theorem allq9 : ∀ k ≤ 5, ∀ i < count q9Atlas k, checkRow q9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq9_4 i (by omega) hi
  · exact allq9_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_2_0 : Interval q10Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 1 := bq10_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_3_0 : Interval q10Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 5 := bq10_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_4_0 : Interval q10Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_4 : Interval q10Atlas 4 0 1 := bq10_4_0
theorem allq10 : ∀ k ≤ 4, ∀ i < count q10Atlas k, checkRow q10Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq10_2 i (by omega) hi
  · exact allq10_3 i (by omega) hi
  · exact allq10_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_2_0 : Interval q11Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 1 := bq11_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_3_0 : Interval q11Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 5 := bq11_3_0
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
theorem bq12_2_0 : Interval q12Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 1 := bq12_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_0 : Interval q12Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 5 := bq12_3_0
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
theorem bq13_3_0 : Interval q13Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 1 := bq13_3_0
theorem allq13 : ∀ k ≤ 3, ∀ i < count q13Atlas k, checkRow q13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq13_3 i (by omega) hi
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
theorem bq15_2_0 : Interval q15Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_2 : Interval q15Atlas 2 0 1 := bq15_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_3_0 : Interval q15Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 5 := bq15_3_0
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
theorem bq16_3_0 : Interval q16Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 1 := bq16_3_0
theorem allq16 : ∀ k ≤ 3, ∀ i < count q16Atlas k, checkRow q16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq16_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_3_0 : Interval q17Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 1 := bq17_3_0
theorem allq17 : ∀ k ≤ 3, ∀ i < count q17Atlas k, checkRow q17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq17_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_2_0 : Interval q18Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_2 : Interval q18Atlas 2 0 1 := bq18_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_3_0 : Interval q18Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 5 := bq18_3_0
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
theorem bq19_3_0 : Interval q19Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 1 := bq19_3_0
theorem allq19 : ∀ k ≤ 3, ∀ i < count q19Atlas k, checkRow q19Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq19_3 i (by omega) hi
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
theorem bq21_2_0 : Interval q21Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq21_2 : Interval q21Atlas 2 0 4 := bq21_2_0
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
theorem bq22_2_0 : Interval q22Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq22_2 : Interval q22Atlas 2 0 4 := bq22_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq22_3_0 : Interval q22Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq22_3 : Interval q22Atlas 3 0 6 := bq22_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq22_4_0 : Interval q22Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq22_4 : Interval q22Atlas 4 0 1 := bq22_4_0
theorem allq22 : ∀ k ≤ 4, ∀ i < count q22Atlas k, checkRow q22Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq22_2 i (by omega) hi
  · exact allq22_3 i (by omega) hi
  · exact allq22_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_2_0 : Interval q23Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq23_2 : Interval q23Atlas 2 0 4 := bq23_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_3_0 : Interval q23Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq23_3 : Interval q23Atlas 3 0 6 := bq23_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_4_0 : Interval q23Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq23_4 : Interval q23Atlas 4 0 1 := bq23_4_0
theorem allq23 : ∀ k ≤ 4, ∀ i < count q23Atlas k, checkRow q23Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq23_2 i (by omega) hi
  · exact allq23_3 i (by omega) hi
  · exact allq23_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 9 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 33 := block_range (n:=33) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 33 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 82 := block_range (n:=82) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 82 := bgb_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 46 := block_range (n:=46) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 238 := (concat bgb_6_0 (concat bgb_6_96 bgb_6_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 72 := block_range (n:=72) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 264 := (concat bgb_7_0 (concat bgb_7_96 bgb_7_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 27 := bgb_8_0
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
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq1 (cert : Complete q1Atlas) : Lower true (roots q1Atlas) (target q1Atlas) 6 := by
  have ready : Ready q1Atlas (asRow q1Pos) (asRow q1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 5 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 0, 4),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 6 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 4 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 4 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 4 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 4 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 16, 18),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 4 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 5 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 5 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 5 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0feeefac8fcecf8c0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq1 : Complete q1Atlas) (certq5 : Complete q5Atlas) (certq7 : Complete q7Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : Sig) 6 :=
    slice_correct (ms:=fixRows 0 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq1 certq1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 6 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : Sig) 5 :=
    slice_correct (ms:=fixRows 4 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa : Sig) 5 :=
    slice_correct (ms:=fixRows 8 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 16 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 32 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000 : Sig) 4 :=
    slice_correct (ms:=fixRows 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f : Sig) 5 :=
    slice_correct (ms:=fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074632 * 2 ^ 32 + 4243388608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37349.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,3]⟩,⟨.or,[4,6]⟩,⟨.and,[1,7]⟩,⟨.or,[2,5]⟩,⟨.or,[1,3]⟩,⟨.or,[2,8]⟩,⟨.or,[1,7]⟩,⟨.and,[9,12]⟩,⟨.and,[10,11]⟩,⟨.and,[0,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4243388608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4243388608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37349

open PEqualNP.Outside.L_meta_37349 in
theorem PEqualNP.Outside.L_meta_37349 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4243388608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4243388608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq1 allq5 allq7 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allgb)
