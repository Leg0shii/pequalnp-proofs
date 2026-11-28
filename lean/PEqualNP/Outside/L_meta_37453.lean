import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37453.Model
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


end PEqualNP.Outside.L_meta_37453.Model

namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
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

def SBf (j : Nat) : Nat := [5, 3, 7, 6, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37453

namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 3 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x104b092124851444848a8b162d545b4a936b5b
  | 2 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 3 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 4 => 0x73ff80fff803f0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff8041102888a8d5
  | 2 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 4 => 0xe2476e66463b0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 29 s1Pos s1Neg, 0xaaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def s2K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa714aa67ac10062218e5a402e00042020001a4a83021882006006fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x5808000000404008000600020444a0a000141e1a0c8000000048040000000000204000180203010101c00be41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414cbdd0532b7414caf10532f4414cad10532bf404cbed0132bb404caf10132f8404cae10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432bd410caf90032bd400caf90b31bd42cc6f90331bd40cc6f50e31be428c6f50a31de328c770ca31be418c77cc631f7318c6f90231bd408c6fd0931ef424c6bd0931bc424c7b10931ac424c7dcc531de314c6fd0131fb404c6ed0131bc404c7e10131b8404c6f90c31be420c6f50831de320c770c831be410c77cc431f6310c774c431f5310c754c431be400c6f50031bf43c86f90f21bd43c86f10f21f731c87d0c721be40c86f50321bf43886f90e21bd43886f10e21bd42887bcca21ec32886f90621ef21887dc8621be40886f50221bf434877d0d219f43486f90d21bd43486f10d21dc43486710d21f721487b88521bf40487ed0121bb40486f10121f840486e10121bf43086f90c21bd43086f10c21be42087bcc821ec32086f90421f731087d0c421ef21087d88421ed21087d48421e521086f90021bd40086f90b30bd42cc2f90730bd41cc2f50e30be428c2f50a30de328c370ca30be418c2f50630de318c370c630be408c37cc230fb308c2fd0930ef424c2bd0930bc424c3b10930ac424c2fd0530f7414c2dd0530bc414c3d10530b4414c3ecc130de304c2f90c30be420c2f50830de320c370c830be410c2f50430de310c370c430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20be41c82f50720fb30c83e0c320bf43882f90e20bd43882f10e20bd42883bcca20ec32882f90620bd41883b88620ec21882f90220ef20883ec8220bf434837d0d209f43482f90d20bd43482f10d20dc43482710d20bf41483dd0520b741482f10520f441482d10520fb20483b88120bf43082f90c20bd43082f10c20be42083bcc820ec32082f90420bd41083b88420ec21082f90020fb30083e0c020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43ecc310f830c43ec8310f820c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610f731843d0c610f721843d08610be40843dc4210fb10842fd0d10df434427d0d10be43442f50d10bc43443710d109c43442fd0910ef42442bd0910be42442f50910bc42443b10910ac42443ec4110f610442fd0c10be43042f50c10bc43042fd0810be42042f50810bc42042f90410f731043d0c410f721043d08410be40043ecc010f830043ec8010f820043dc4010fa10043d44010f910043c44010
  | 1 => 0x3064090021da73a3e630e22e906358da7c9b22f0781ca0c001983e0660025a00098000ac77000842085f004148008d9d0000020714e6a884000000f242000a00007a15138258606514c7080a2691051800042021f9ca7e9740ba4e690d4469c40011c371181c0004a800159de000c08a8000f8d85280030800891c6910aa4080086042320be01a2e84800001f8348005600004800310de4c1527a0943a00039924878460000000076000000011e2715a0b0fc110004f0320606a880ea8f1d61a114649ae7b8801206c8c90a4b092601722d1fc068a27f8b67200e0586e6f014000260e05c6b1628188a55a0a0013a7d034000fe001d85b8008d00000000001a0499be658864c85e3805a5e9a81620e339ba000002c9202c0ca4a01e95000340003ea463d9d24890457800330005424a1d18e8a17600064000405203a9498a0011240154188006d164000b8679c0000a44588e889700a99a208006e088002005a0ee511a64b9b62b80c59a560024c0017e002385aa0478000090a63c8000000012a3a9400000000000a800000000c690000001cc789348680000108001b0000009622c002160a178279f61f00000000870000d84c00184002304f90e50a147a986000001400039000572483d0220016c670006080068960000f0001407b00075000081887c1e44da263b0002304e001e64300003094080d0000800000687402270300002000080000011303c02040081c06050600400070002c0001038080401010000a0000008000a0002c020001808000100828020416800
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x88632f5250031962928018ce94343c8672a1a1e4397430c7219d2868710ce543438871e86194431e5390d219d2848690ce542434865ea4a1a43375150d219da828690ce141434863ca821a439443c8521c621c4290e6d0f404873087a02439b4310121cc2188090ecc84404875442202433b5050c219c2828610ce9404308672a0218432d540c821c6a186410d9544320866aa81884395430c421b2a906210f10c831086caa5108432f5448421a629a4210da141210866ea890843545348421b82824210d9d51210874ea890843c75348421b329a4210d914d2108788a690843445348421f1a824210d914121087c0a0908436050484218fa9a8010c714d400874e85a0a61a442d0530d3a10829869108414c3508598261b041cc130c6214609865106304c26ea2a1061345150830c6a10641856540320c25ea4a08612c5250430caa08621856540310c2b2a7180611f544c030a6292601855145300c276a89806168524c030b828a601856d51300c336a898061cb524c030ac292601872149300c290a498061d3514c030ac28a601874145300c2a0a2980613651d0f209aa8e879066d0c30c826ca3a1c413551d0e20c7a1865104794e434826ca321a41355190d2097a9286904dd454348268a2a1a413b5050d208f2a0869065d0f414832887a0a41974310520ca21882906610f204836083902418c4388120d220c40904dd454308268a2a1841365110c209aa8886104b550320831a861904169500c8208fa9a82104714d410834a82108416950084209caa060106650c30082d2a418041c8320c020b4a9440104bd512008298a6900416451480209daa240105614d20082e0a2900416b5448020d5aa2401072d4d20082d4a690041685348020e429a40105214d20083c6a290041685148020f028a401058145200825ca5a1e212d52d0f108f29e85884754f42c43368618621ab42083109729687084b54b438423ca7a14211d53d0a10cba18630869d08218423ca721a212e5290d1096a9486884bd494344258a4a1a21375150d109da82868847950434431e87a12218c43d09108f29c84884754e424425ca5212211f53509108e29a84884dd454244276a0a12212e5410910c7a1884886310c42443308788221a842c4110ca21c20886910a104425ea4a18212c5250c109729086084b548430423ea6a10211c53508108f29884084754c420426aa81882195430c410b8a8062084d550210434a84108217150084109caa060086650c30042e2a218021d0310c0109caa040086a50820042e2a210021e021080109caa420085c546100426ea888021545344010b229220084ed5110042b0a688021685244010b9aa220086cd5110043a6a688021725344010b829a20087414d10042a0a688021e35244010b929220085c14910043c0a488021605244010
  | 1 => 0x924b00079048221dc00000651503894e0022a6d91c52800490088518c2f1ea3f0721e9f45f9c25a0644c946338264f8344a1d245876131b45d90e05992799fc3495c359be3a8143e1d0818220013840000000d48b1e80f9700e8001816450978750524f18a00000071128a202189580005e001a23613a661204a9ee1e0022d8ba00000001cc07800001aa5e8281a95e00220000aa7e96a691fe409847e058061de3b1bc450ae608301083c12940839485303247930600384d1ac399522c0ca87896230f0781965110a0aa0c030208902c63a08218ee119366e910641ae489ec768be2d1086c80430806168b84309a0001a738a2619c01a0826206e381607c0a029800000000011a0015400000000c6000c032010000005b0a4002186c1047c8fe150008997c1c0002a0000015a000c472126000001f92e110000002e8000013800000507d962391b82c9d623a0a419c61f0983d99e67040668003a1d800172002040005c84800228945d012159663789e000da888f2371e25ba10240d00006c00000028f4039a60d8802b1a027000871567287400066858fa6a1c48682433118000840500404310007800000087008002b00002060a800000a01810000100018061501000000b0781c020b018000827068040e17050d002001081800000404c54000091000351b078080500018180002868180f0287c0609030000205030640006070d8040308800220101e9cc8414cb2c6420a65b341d0132d820e80996cd04404cb608220265ab3210132cd19080995354e320ca3ea89906554514c832ac28264194bd51320cac8a29906568504c832a7aa2641963d51320cb8ea2990654c514c832e228a641951145320cb96a0990654c504c832e4282641952141320ca76a0a08653850504329ba8a80194d145400cb488598a638c428c531d5a168098ea10b404c7568420263a84210131d99888098e68c4404c676a0a1063385050831c6a106418d5544320c6aaa7188631f544c431a62926218d6141310c66ea89886364524c431b82826218d5d51310c72ea898863c7524c431aa2926218f1149310c688a498863d3504c431aa2826218f4141310c6a0a09
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x16150398860119971100001800000000140000001f80000015800000000a0e000c80130f92000817831f1a108a801a8004070f019680020b098000091e801d80001d001380000680000020800d990d1c800000001b928e84889c2000000c07809000000b91801b02800005148580000000001e00000200911000010008000030a100090000100d0147504c832d0d44504c832d0144504c832a2181420c83194181510c831d014b504c431d0d48504c431d0148504c431a4983430c721a2983430ca21a2181430c82198181510c821a4181430c42198181520c421a1590320c421c1550320c4219198e5348421989825348421d014f5048421d0d4c5048421d014c5048421a1185420c83094185500c830a1189410c43092189500c430d014b514c030d0d48514c030d0148514c030a4987430c320a1987430ca20a1185430c82098185500c820a118d41084209218d5008420a4185430c02098185520c020a2590320c020c2550320c0209298e5348020989865348020d014f5148020d0d4c5148020d014c5148020a298b430c310a298f4208310a198b430c610a198f4208610a1189430c41098189500c410a118d42084109418d5008410a2189430c01098189510c010a4590310c010c4550310c010a218d42080109418d5108010a85902108010c855021080109498e53440109898a5344010d014f52440109498e52440109898a5244010d0d4c5244010d014c5244010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*4) 4
  | 5 => packedAt s2K5 (i*15) 15
  | 4 => packedAt s2K4 (i*26) 26
  | 3 => packedAt s2K3 (i*37) 37
  | 2 => packedAt s2K2 (i*48) 48
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (5+((h/1+packedAt s2K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (400+((h/8+packedAt s2K5 (360+(h % 8)*5) 5) % 29)*6) 6
  | 4 => packedAt s2K4 (8752+((h/100+packedAt s2K4 (7852+(h % 100)*9) 9) % 399)*10) 10
  | 3 => packedAt s2K3 (11160+((h/93+packedAt s2K3 (10323+(h % 93)*9) 9) % 335)*10) 10
  | 2 => packedAt s2K2 (3322+((h/22+packedAt s2K2 (3168+(h % 22)*7) 7) % 115)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffdfc3ffff1ff1ff
  | 1 => 0xffffffffffffffffffffffffeffc3fffe3fe3f
  | 3 => 0xfffffffffffffffffffffffff7ffc3fffc7fc7
  | 4 => 0x7bfffc3fff8ff8
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffa078888b0490db
  | 1 => 0xffffffffffffffffffffffff908b911521262d
  | 3 => 0x9113a26484b46
  | 4 => 0x62223b8920db0
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 27 s2Pos s2Neg, 0xee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x800409394602014602c40213be42bc42df32dd32be41bc41de31dc31bf40bd40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc00815180401365190aa8a2995614132ca208632c5250268a2a05594630
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
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (197+((h/2+packedAt s3K3 (189+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffc0fffffffffffe07fff80fffffffff1f8fff
  | 1 => 0xffff01fe03ffe03ff83ffff03e07ff80e7f27c
  | 2 => 0x3ffffffffc0fffffffc0fffffff80ffff8ff8f
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4852146248824c0c014b29064a8b18aa0b84b5
  | 1 => 0x92864ca43924855658155b521645ad0665b25c
  | 2 => 0x2308290890691122aa809468a5508654b05b0a
  | 4 => 0x3a2cb1d12241d9bb34e6064c39e6c418fe03e0
  | 5 => 0x3c30c1e1c38e1e3dc738e78f01870860dfec00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8558000000063e00e0000016820881627066d32e2a3120d4a38f293a0040000003805451809621400b000000a200001a44440000200b9900a00122c4d1af1e0000000600000000003800a0c19020100041200000ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x10e8b4a230089039a4cda8d06884e00e2e89cd60b001140003001f146640d000be652720cbc3d00184787b0018cfc00000080047000006800248fd36000a238002400148002b048013e000015c00174e8645800000040000000c820621b001241f2e08912461703d086f1d0d48207000000000169007c1300001407700061486c05020660012800a60013268940000150545b00074884b1c1e9000017858a000489d49e48000008672090012e8506070009934288d47110260f0792680000294322050232d1f40000370c436063b2080a660000060394780102424f1592a601ba70b06950a582200289fc3c8a2a99c2a59001d0983b01808002030502058002818200001681150100020002000712800a0000010b830000810084801180800200030f80020e8c858002020302cf94b439f28e873d50d0e7aa921ddd4543ba28a879f5350e78a4a1edd45439e28a87b45150e68a2a1cfd41439f2a0873d5390a7ca5214f946429ea84855e5310abaa6216794c429ea98859d5310a3aa6214f94842d7290853e5110a7aa0214f953329eaa6659d43cca7ea9194f152329faa2653c544cb3a86995dd4532ba28a657b504caf0a0994f950329eaa0655e53d06baa7a0cf54e419f294833e519067aa120d7d4d41ae29a833d531067ca420cf94441db288833d501067ca998cf55331da20e633f548c678a918e7d0e31cea1c639f548c738a918e790a31ce214635e518c73c8318e7106319faa2633c544c67ca818cf55031cfa18639d430c7688218e795031ceaa0639e420c7388418d794431eb28863d7410c73c8218e710431ea2086394410c67ca990cf55321af29e435d53c87a86390cf952219eaa4433f5448678a890d7d4d21ae29a437b50486f0a090cfd50219e2a043d431086bca7a05754f40cf29e813d53d033aa7a04754f409f296813e51d033c63a0670c7409eaa4813f5350278a4a04f14540cf18a819c3150376a0a04f950409f2a6613d54cc27ca9184f55230cea1c6176518c2eaa3184f951309eaa2613e540c27aa8186750c309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c43a863884f952109eaa4215e53842baa7084fd51109e2a2215f53442b8a6885bd4910b629221d4314427ca8084f55010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x17006401e26b102300adcb300a85b45a68c1f1c75c0022306b6000179050b9db24485bb504a43161e482000a00e1b74292b160243a628013a41004015060840000120c3010415000000cb1a6e20084c5d4c5150f17631454387d8d5090a546154c428d1855310a946154c42c5d855310a1c6154c42c51855310a146154c42a518543cca3661d523287195434ca946150d32c550c514cb1943141328758e529061f63542418e580548c69661d5231a5984548c699601523187994428c6356510431a5986420c61d6510831a5986410c6976510431a5594410c6966210431a5580410c716540c7218758e548861d63150218e5805408714540c4219518553d02346154f40a518553d03176154f408718553d03146154f408518553d021f658c7408759431d021d6314940c514431502946150e30c550e518c21d63951308b189544c2346155130a5185430c21d63153208758e548821d6315310c515031c4314540c510d1148314421d6395010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x908047190c500008009c289386c628a87059c76354242a20e2a18a09949170d94410c60abb0a818843445c0540c421828e2b18a4a04147158c54c820a38ac72a441051c56395010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4895+((h/55+packedAt s4K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf03fff81fffffff81fffe07ff07ffffe7e31ff
  | 1 => 0xffc07ffe03ffe07fe0ffff81ff83ff019fce7c
  | 2 => 0xfffffffffc0fffffff03fffffffc0fffe3ff8f
  | 3 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1485188c48824c18052ca432502599542e10b5
  | 1 => 0x21932914392484a960556c90b482aa0c96c65c
  | 2 => 0x420a422090691042aa025145294804a9416b0a
  | 3 => 0xb2c74492241d974d3981861ce734031f80de0
  | 5 => 0x8c307871c38e1e7f1ce39e780c6388c1ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xe8e0e8e0e8a0e8a0e8e0e8e0e8a0e8a0e8e0e8e0e8a0e8a0e8e0e8e0e8a0e8a0e8e0e8e0e8a0e8a0e8e0e8e0e8a0e8a0e8e0e8e0e8a0e8a0e8e0e8e0e8a0e8a0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x10341540014513980e98909388cf191800100007c02900849a22e1019d100059500580000034d8048808801e187014a0000421c004308200228bff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x681ee52d02dca5a05f54b40f6a96816d52d037e85a06f50b40bf28e817d51d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a85205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40bfa92817c525037e84a06f50940bfa8a817c51503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4206fd0840dea10817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461bf428c37a85185f94630bea8c61de318c3b863185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930dfa1261bd424c3be6498774c930bfa8a61f7514c2eea2985f14530fa28a6174514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4186fd0830dea10617e510c2faa218778c430ee188617e500c3be60187e8c030ee98061f9300c2fea9905f95320df2a6413e54c82faa9906f553209eaa6417c54c82fea7905f94f20bea9e417c53c837e85906f50b20bf28e417d51c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20f721441bd42883da85106b50a20f799441ec32882fca3105f54620f710c41ec21882fca1107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41bf424837a84905fd4520be28a41fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6105f94820dfa1041ee420837a84107b50820d6a1041ef32083d864105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3087dcc610fa18c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443ec42887d48510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c520437e84086f50810bf28821f731043e862085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc5350b7ea4a16bd4942dfa8a85be5150b7aa2a16f14542dfa8285be5050b7aa0a16f14142bf2a0853e5410afca6215f54c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465bf428cbdc85196f50a32f6a1465ad428cbbe65197bcca32bf28c65f6518caeca3195f54632faa8c6575518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1265ee424cb7a84997b50932d6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32bf29065bf420cb7a841977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e837e52d06faa5a0efd0b41dea16837e50d06faa1a0df55241bf29c837d539077c8720ef10e41bf294837d529077e8520ef50a41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077c8620ef10c41bf29083ee52106dca420df54841f6a90836d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663bf42cc77a8598fdd0731fa20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31dfa1463bd428c7be6518f74ca31bf28c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a2637f524c6f8a498efd0931dea1263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c7be8618f710c31bf290637d520c77e8418ef50831ef99063dd320c6fca218fdd0431fa20863df310c7ec6218f74c431fa98863d5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643ee42c877a8590fb50b21d6a16437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21dfa1443bd42886fca310fdcc621fa18c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53486fca690df54d21be29a43bf42487dc8490ef50921f6a1243ad42487ee6290fd0c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf29043bf420877a8410df94421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40bf29
  | 2 => 0x1dc2f0000001f89c50ca7e00086c29000000000001a6000aac00000000000698000001612980000000000070000994000000000a00000000021c001652d8170179680001d40021c00092c00000000000002430009f4f30483480007a1ff00000082a060f80c80000000000022000000000000f2000000001160001b8e30000000014a17300068800000000000000000005b80008d00000124000000238000000000000008a0006a49500017a00028a0c54c724fa800000000000354609f06f8572120709e97b0f2001520301863b0f11b80000009c9ee00000000184124001308001380000003c0000000005d42e184860000f63011626951a8e87b959000001022b01bc17cb213e442020000001da5c8929ed0008240280053e0004c8000000014e1eb000001140e30007e4000000009a0328342bc18c0024a108764000003823e000000244000de0f34c83a89800044c0000000018a5b40380047c739471540928f09a80444620d51800234a740025455467150907000000ca000444100000001aa7710e8c80000020080000301000002000000004008020000040000000a00407005002008098080140000400400005400003000000000010000040080000204002800008004028010000040000a0020100200100000000000000000030010000140080001a0000280100000800003000000000000000000000500e0000080200e00400001008000050010160000300100200402002006000000010020040580300001c0000000000c010040020340300200c0140100100000800801002000000010020000100000e0080000000a0000080500e034000020220000200000000000001000000050070040040180000400c0200100000000004004000000000060040280a0000080280c0000000080000601400003002004040000120000080000001000000002000000030000000080100401800800000014008010000040200100000c008000017e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150feea2a1ddd4543be28a87f45150ee8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843f7290876e5210efaa421fb54843b6a90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42df21e85bd43d0b7887a15f94742bea8e857e50d0afaa1a16fd4f42df29e85bd53d0b78a7a16fd4742df28e85bd51d0b78a3a16fd4342df28685bd50d0b78a1a15f552429eaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a16f94d42dea9a85b
  | 3 => 0x4f0000001e8000004b8000002768d40015b27e7f8338000c800116a6b08a0000015d2f0a94e60000006d400000000800310000000000011c000000708000000003416b100000670000004552000048e00000134000224000003f0878ca8a706240d221c40000001024d44e000e58000004dc00000000820998000000000d0004560000014e0008a4cf1b20660001f80000060c000c400080cc4aa73c82895480000000000000000000000002f2000f1ab6000438a7800000000000003d25353f948000000000001ae000940a504600000000322a482720e1c400c002a21cc8dd3d9bb00000000000000000000eb0000005f8003e8a440000000055946000000508db8004e096c000fd570a60002103ac97400000000aa0ea8000709d400000292044000000000f80000012c000c98000009695d0cf000a6d058250007d8a20000000000025116a008e0285016a40000760005847c9040003513693617c7f40001b28c714498002cc6e8ea00004e0000001013e6ac001b30000015a0783b05dc918690006489e0360feadc908000000011980037c9b8002ae000000878004820000027911644c0000000000124ab30000009480032c0014b8664022140019f000244c396000060054000000000ba8d00fa6fd03a8f0a6000392114480000018f0004906580000000122800000000a8262000608000004be204000c902a4405514c31084d3a23443000000000000778000000000000009800000000000000618000000b2a040011b47e0000016f4280000000003a00050258000000000cd00010c7d800094000000004540005c92d302880de800000ac81d1702ec9a8000000982b1500005260dc000000002bcac06b25666d31a6f000000ee9f01de7ec3f1b13ae0002a0004e4000e52423180000c0000000480000000025c001080000000019d000501029f7358000d00000000000000001c498000004d80002a8000000006d100000000001b400023d1e80014628541000500ac4440424cc5f47b0c72a43080000056a428208003e64450786f48ca200006c02c2080006a01a0000016235e9dc5b0fa2fe514e82860000008e873000000af98b0002ec000ba000000e38000bc12c0515505a00093800224000001e753c40473a78000000000d20001e94185a1d00001d8b11fea2cf623945c00000284000370000e94a02dc110170e8000a889a3e24343897e026000001fc3f40014d0860000000023b04c00117918000180001e5000000000001ac304000392620a87214a000000b88000000010b18d000064000002642d0000000000000000000000000000166768978001b045c000000003c00000000076d3989e0480014a8000000000000600000000000000158858a6000848f08b83a2000000002c6ae4b52991ea0000019a28e2c9291970000008f00
  | 4 => 0x24c3142ace784739a000570000009d9560461a20000016720c68cf900118c6851914b274000000002b80005802c0002b4000004f4050000000008680015746c000000001945041598e34a03c000000000000000000000017174000a280024f000000d680000054c8c8094700012ca5704250c2800041400000000000000e18a9330000c29a80006d80017c0004e0961ef1b26b814a893320000604d0007087f0cc1c036c0f1ea4626a943aaf13aa592f1df23e0012e08c00000000120000000000000000010a800404000000001280006e8000ee1b400256000954000002f4001338f13726c0ad1c8120939300a443e450f01020007a0b489b12aab40f99034e000000e5000834e91d344a16c00
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3208826d629512097d8d544825c63551209dd85544827461551208fd91534823c6454d209bd8953482776154d209d185534825e63d50209758f540827661d50209d587540823d6595020cb98a540823f62550208f589540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530834c6254c208f990530823d6414c209798c53082766114c209d584530823e64948208f592520823d65d0820c794f420831d53d08209b59642082ad6490820d354e42082e960908208fd95420831e5350820c754d420832e5450820d354d42082af6550820cbd95420832f5350820e394d420832d5350820e354d420830d5350820d354f320826d650c820ab59032083365494420cd55251083565394420d554e51083a54294420cdd0a51083354294420cb50951083365454420cd55151083565354420d554d51083a54254420cdd0951083664254420cd50951083654254420c950951083655188420ab590210832d4294020ab59320083a942880209bd95200827b6548020ead09200826e62153109b58854c423e64d4f108f59353c426e62d4f109b58b53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c432e5250b10cb54942c43a542487109798f548425d63d52109b98a548426d62952108f993538423d64d4e108f992528423d6494a108f990528423d6414a109798c528425d6314a10cbd49428432c5250a10d5d4c318423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d4910cbd93524432c64d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524423e64149108f590524426e6514910cbd50524432c5414910d3d4c524434c5314910cb990524432d6414910d9584524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb14942443545388510d914a21442746548510d514d21443a54248510bc181214435453841109798c540425d63150109b988540426d62150108fd91530423c6454c108f990530423d6414c109b988530426d6214c108f992520423d64948108f990520423d64148109798c520425d63148109d984520432e5250810cb5494204275650c410d554c31042f1600c4109e59610042776544010b518d100427b6544010
  | 1 => 0xc797644c431b5991310c6d4644c431e5191310c694644c431b5d89310c797424c431e5509310c6d4604c4318fd91500c63c64540319bd89500c66c62540319798f54c865d63d5321cb98a54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c874d5390b21c794d42c871d5350b21cb95142c874d5350b21abd9542c872f6550b21cbd4d42c878e5350b21cb54d42c878d5350b21c354d42c872d42943218fd91538863c6454e21d554c31886d663c86218fd91508863c645422197d8d544865c63551219ed81544867860551218fd91534863c6454d219ed8153486786054d21ab592424866c6550921cbd95424872c6550921cbd4d424872d5350921e9d8542487a461509219d99731487a542cc521d554c31487a5420c521b598f21487a542c8521cb508504863d65950218f990540866e62150218f993530863d64d4c219d987530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520863d65d08218fd95420872e5250821cb553210866f6548421cb55121086776548421cb99152d032d52d0b40cb94942d02ad6210e40cb54942902ad6210640ab58b409032f5250940cb14942502b860509409dd8553102746154c40c754c43102ad6210c40cb54b42102b960d084097d8d511025c6354440ab58841103355110440ab58b401023f65500409ed95401026e62153309b58854cc23e6494b308f59252cc2766194b309d58652cc32e5250b30cb54942cc38d424cb309d987548c27561d52309b98a548c26d62952308f992528c23d6494a308f58b544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c23d6215130cbd53524c32c54d4930cbd93524c32c64d49308f990524c23d6414930cbd50524c32c5414930cb990524c32d64149308f997424c23c65d0930cbd4b424c32c52d09308f995424c23c6550930cbd49424c32c5250930d314b324c38d424c930b6181324c33754d4530cd153514c36752d4530d914b514c33742d4530cd50b514c3375414530cd150514c3675214530d9148514c3374214530cd508514c3573214530d54c8514c354518c1309b988540c26d62150309d984540c27561150308f992520c23d6494830cb949420c32d52508308fd91510c23c6454430d5544310c2d9600c43097d95300c2d4614c0309ed95300c23e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c823f6454e208f19153882776154e209d185538832f6550a20cb195428832f5350a20cb54d42883ab6050a20ea18142882ad640ca208fd91518823c645462097d8d518825c6354620cb50951882ad6408620ab59
  | 2 => 0xf01c080081e000000a40002c090000e008010182301c00084000240a0100f00000028030080215c000100008801094040080701400004000001902c0401000054000801b0000e0000f01402014000340200c0200c150680b0000b00004004009bd895090e6c6254243d5d0c5150f3643145438fd954310eb46150c4397d954310ed46150c43cb9915210f2f4354843cb50d5210e776154f429d18553d0ab76150f42ad18543d0b1d5310f4297d8d51d0a5c6354742ab58b53d0ab76154f42ad18553d0b1d5314f42ab58853d0a9f6354742a718d51d0b355114742ce54050d0aae6290d42c714d4350ab76150d42ad1854350aae6210d42ab58a5350aaf6254d42add855350ab46154d42aed815350ab86054d42c754c5350aad63d4942ab5875250aae60d4942a7d8d5150a9c6354542aed815150ab86054542cd5445150a9f6354142a718d5050ab76154142ad1855050b3950141428fd954210a6f6550842cb9514210a3f64547328f19151cca3f64543328f19150cca7661d52329d587548cb2e62952329d984548ca756115232cb951428caaf6550a32cbd95428cb365494632cd552518cba54294632cdd0a518cb354294632d5cca518cb2d4254632cd951518cb355454632e9509518cb374254632d9909518cb354254632d9509518cb254254632cb50a508ca7761551329d185544ca7b60551329e181544caad64909329b195424cb2f6550932cb195424cb8f6350932e318d424cb8d428c932b5986324cb2d42d4532cb508504ca3d65950328f990540ca6e62150328f992520ca3d64948328f597420ca3f6550832cb949420cb2d548c83297d95320ca6f654c832cb551320cb2d52d0b41ab588439072e5250a41cb549429066f62542419b189509071f53d0941c714f425071f5350941c714d425072f5250941ad185425075453d0541c714e41506ad6210c41cb991521072e4354841cb10d521072d52d0841ad587421072e5250841cb54b411063f6550441a718d411072d52504419dd9541106d463504419b98854cc66d62153318f99252cc63d6494b31cb94942cc72d5250b31b958841cc66e62152319b588548c6cd6210e318f992528c63d6494a31cb949428c72d5250a31e3509328c63d62d51318f992544c65f63551319dd85544c66e62151319b588544c63e6515131ab588544c72e62151318f588544c72d62151318b588544c63e64149318f590524c63e65d09318f197424c63e65509318f195424c73454cc531c7152314c66e62150319b588540c67a60150319e580540c65d6510c31b3588430c6d56110c318f992520c63d6494831cb949420c72d5250831b5587320c78d424c8319d594410c6d56310431e510c410c6e56210431b558e310c65f654c431a7191310c677654c431ad191310c6d7654c431d5d95310
  | 3 => 0x45b9531163f90d9580ce4c4dc180000000000000000000e9c1158000000001e2000460002f40f8000ab3440002290c1be27400000000000fd1491026644003a18a000170002ca1ac00000050064f28004584fc032681345085800035e5fc320650008640022709661c770001ee57c000e50d46c0759d13f8488c69e6000588db12c3941f07a89b21c678ae22a08c3506613b24c5001c8b21e69b93017424a3e8dc9e72a42549ca452ba720d695a00068c07097448344361de04c680c40930346c8db8d92905c93792a35253ced1284c44188d8042dc384f00ef3fa74c8b0940006409b00028a45c340e04ac301231d2230924c18004d20000000039205d199bc0060008918c21497822090000340001bb0001c44399a000198cd9aa3161fcd30b84b8304b1a340008988f8162a00d4fb8763b0648aca35138218001330000007800036865400000018000710000140005a0002ec0008403039a8fc0025a32e0a8378730a8060470744c87d02ca5d3be148888000ea900ea8003886a07502d1049b0918e6046518b815e25e2e48c8c20b695c198a219210c9f0ad4704102d2073124712f8990006840009f42243c4290001e2d84482700a32c2b82b3f256cbf00000093852a6a3e05a84c0154307ac9014b03e63c0901c24e06c3117d000000001440fa0891294300222881175000000faa150007bc8a23d00017031a2030a2a50918e00020c000002482f12d8f83380446920006e6acc314e1f61ecf70d80f2378bca441e87a08f18400e3c84b0004747cc5e9940fc6600012900014d3191d2aa141380701c6000000001c8608001c040a8346e8cf1ec808972060006c4208d300000049203398598309ea07e9651123103c1750a0322e67ed0e86e13c718aa16b0d235d0b16c0ac51c5d800190000cb23027a178b3a482f07b41622e46e6b0b49ce37a504631371741b40025845202c7f8883c892c550000003a4b20000681800024215c28c1892d1fa31d118a000090cff1b33c6580eb09133e48495a0b4568305423b1d0000be15746c2fd1e0000003b41e00035c7c8ffa394aa804dd0b10aa95083a4f4a2424f10003d23590402f2705851783d278000ec800000050539c54a0529291e13960009a10b3485dd168090000900008434e30d0f84e01a5a1269c2000001080a600083cc08be0009c50d16f4147751924c3263b13681309e010010080900c0102c28038000000c02405000010080201c3100c05040050081e024090180600417028000b802010010000102c00004030000401c03000020380904c0202c030040401c0000801000060001a00009024000700703c03000050300200402000100040000000014000040100404004120200009809014010841104c0c084020181d01c0300c0601c000300002004038000000900406018030040400c
  | 4 => 0x3e42f84d0000000019d142084000000f00000000000099820151408000000000000006a800264628e814c34a334000000003f0001be1b6001108004265347390d2021601291015e5589aa6b38e311239032262d40000019c6450b8490208a02393a22a144261f64820e03921e3b85ec982613b6414001ec4ce3688d20e14875c149f11b870c241f80ee329299cf11a928df80011e0803d008084008daa3e4389941d84a2e20d85996d3a882
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2281180016208286120a1a8508000200088b9d049a220c1f000e1f8a8d8595098c939300018b1e00001b238014a106871c91801680090003000f80170019001b801018a317879421a51984110f1c00009da48e9ea41095838d2012810b480020100081000a0000100003960a0038116040d247150d5210e8a38aa621e85451c55314f42c1aa6b10a7a15147354451d0b0a298c2a1a85451c55314d42a30e0a98a6a14a77158f5250a47b9ac3a9285451cd5114542a60e0a88a2a1518735405050a9838aa028285a150a618c932c28a630a84a0c94735874210712a92c3a10838318d5250441a4ae42a66298d0d72152314c64a3a2c399063615c84310431d0886b108218c8d72191310c652b90c898863259d2644c43198ae43226218d8572191310c743390c898863255c8644c431d0ae43226218c8572191310c64a3b68498863251d9424c431a28e8a986310c2c7654d4248694382a6a12438999542cc521a28e8a986290d507054c3148782a9a8418a43a198d42c8521a1ae72928410d147154c4310306a9ac421881451cd5110440c4ac4a8882205257194942cc2863aa8499261a2508604c930e0a84990a298550704c8514c216b90c8a8861451d1510c430a4ee2a9a851060f635095188286ba0c4a9841495c75350820a1aeb29a84107055350a510838329a84a8841c154d4254420a1ae7292858842d729935384286b98a4a1421459d3530c610c4ac8b08a48852475509214431232a8490a21c114d4248510ca0a630242886a1421812144216b90c8a9821451d1530c410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8038005324000094060568180000060a048154d6214f42c047354961d08419048754d420c521b008054d420c521a048154d6210c40c04735895110440a0885508604c930d01421c13214530905821d1510c430905829d3530c610a20855086048510e00535086048510905821d1530c410
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
  | 4 => packedAt s5K4 (25868+((h/208+packedAt s5K4 (23788+(h % 208)*10) 10) % 752)*11) 11
  | 3 => packedAt s5K3 (3850+((h/25+packedAt s5K3 (3675+(h % 25)*7) 7) % 91)*8) 8
  | 2 => packedAt s5K2 (800+((h/4+packedAt s5K2 (780+(h % 4)*5) 5) % 22)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffff03ffffff81ffc1fffffc1ffff91ff1ff
  | 1 => 0xf80ffffc07ffc1fe0ffe1f07ffe1fc06e27e7c
  | 2 => 0xfff03ffff81ffffff0001ff87ffe3fff038f8f
  | 3 => 0x3fffffe001ffffffe0007fffc007fc0ff0
  | 4 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8a101189104800052c02508940245500cb0b5
  | 1 => 0x126292287249129605520b452d20a83262565c
  | 2 => 0xa144b44120d231aaa03112d44b5432a7030b0a
  | 3 => 0x858b28924483a54d39a54080729900c5b40de0
  | 4 => 0xc60c30e3871c39f1ce399ce603102307dbe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0eea8e8a0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q1K3 : Nat → Nat
  | 0 => 0x1020801a8002f98dd31de43b487d087910
  | _ => 0
def q1K2 : Nat → Nat
  | 0 => 0x420314c521d131443848510
  | _ => 0
def q1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q1K4 (i*4) 4
  | 3 => packedAt q1K3 (i*15) 15
  | 2 => packedAt q1K2 (i*26) 26
  | _ => 0
def q1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q1K4 (5+((h/1+packedAt q1K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q1K3 (98+((h/2+packedAt q1K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt q1K2 (80+((h/1+packedAt q1K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q1Pos : Nat → Bits
  | 1 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q1Neg : Nat → Bits
  | 1 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q1Atlas : Atlas := ⟨4,rawDecor 30 q1Pos q1Neg, 0xfffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0, q1N, q1R, (fun _ _ => 0), q1I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q4K3 : Nat → Nat
  | 0 => 0x4002031000005f32dc6574cb6994d32
  | _ => 0
def q4K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q4K4 (i*4) 4
  | 3 => packedAt q4K3 (i*15) 15
  | 2 => packedAt q4K2 (i*26) 26
  | _ => 0
def q4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q4K4 (5+((h/1+packedAt q4K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q4K3 (79+((h/1+packedAt q4K3 (75+(h % 1)*4) 4) % 11)*4) 4
  | 2 => packedAt q4K2 (27+((h/1+packedAt q4K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q4Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q4Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q4Atlas : Atlas := ⟨4,rawDecor 23 q4Pos q4Neg, 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8, q4N, q4R, (fun _ _ => 0), q4I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q7K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q7K3 (i*4) 4
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt q7K3 (5+((h/1+packedAt q7K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q7Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 3 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q7Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffff4061010824892131
  | 3 => 0x2088281109124486
  | 4 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q7Atlas : Atlas := ⟨3,rawDecor 60 q7Pos q7Neg, 0xfff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q8K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q8K3 (i*3) 3
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt q8K3 (4+((h/1+packedAt q8K3 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q8Atlas : Atlas := ⟨3,rawDecor 26 q8Pos q8Neg, 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x1020801a8002f98dd31de43b487d087910
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x420314c521d131443848510
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q9K4 (i*4) 4
  | 3 => packedAt q9K3 (i*15) 15
  | 2 => packedAt q9K2 (i*26) 26
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q9K4 (5+((h/1+packedAt q9K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q9K3 (98+((h/2+packedAt q9K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt q9K2 (80+((h/1+packedAt q9K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q9Pos : Nat → Bits
  | 1 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 30 q9Pos q9Neg, 0xfffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x1020801a8002f98dd31de43b487d087910
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x420314c521d131443848510
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q10K4 (i*4) 4
  | 3 => packedAt q10K3 (i*15) 15
  | 2 => packedAt q10K2 (i*26) 26
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q10K4 (5+((h/1+packedAt q10K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q10K3 (98+((h/2+packedAt q10K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt q10K2 (80+((h/1+packedAt q10K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q10Pos : Nat → Bits
  | 1 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 30 q10Pos q10Neg, 0xfffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q11K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q11K3 (i*3) 3
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt q11K3 (4+((h/1+packedAt q11K3 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q11Atlas : Atlas := ⟨3,rawDecor 25 q11Pos q11Neg, 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q12K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q12R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q12K3 (i*4) 4
  | _ => 0
def q12I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt q12K3 (5+((h/1+packedAt q12K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q12Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcf9ff8fc3ff39f
  | 2 => 0xffffffffffffffffffffffdff3fcff1ff87cf3
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40602810250a4185
  | 2 => 0x2089010908912432
  | 4 => 0x150b506a42a52e18
  | 5 => 0xe221ab493064bc0
  | _ => 0
def q12Atlas : Atlas := ⟨3,rawDecor 53 q12Pos q12Neg, 0xfafaf0f0aaaaa0a0fafaf0f0aaaaa0a0fafaf0f0aaaaa0a0fafaf0f0aaaaa0a0fafaf0f0aaaaa0a0fafaf0f0aaaaa0a0fafaf0f0aaaaa0a0fafaf0f0aaaaa0a0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x288001a01082f995d32bc6370c6f985d30
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x65009940cca35083199400c6350b30
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q13K4 (i*4) 4
  | 3 => packedAt q13K3 (i*15) 15
  | 2 => packedAt q13K2 (i*26) 26
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q13K4 (5+((h/1+packedAt q13K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q13K3 (98+((h/2+packedAt q13K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt q13K2 (107+((h/1+packedAt q13K2 (104+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf39cfc7e39f70f
  | 2 => 0xffffffffffffffffffffffeffdff3f8ffe39f3
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21829041288a305
  | 2 => 0x1020004084100052
  | 3 => 0x941501921250c28
  | 5 => 0x7891aae4985af80
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 45 q13Pos q13Neg, 0xfaf0faf0faa0faa0faf0faf0faa0faa0faf0faf0faa0faa0faf0faf0faa0faa0faf0faf0faa0faa0faf0faf0faa0faa0faf0faf0faa0faa0faf0faf0faa0faa0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x8201a81001ef98dd31de43b487d087910
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0xa0314c521d131443848510
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q14R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q14K4 (i*4) 4
  | 3 => packedAt q14K3 (i*15) 15
  | 2 => packedAt q14K2 (i*26) 26
  | _ => 0
def q14I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q14K4 (5+((h/1+packedAt q14K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q14K3 (98+((h/2+packedAt q14K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt q14K2 (80+((h/1+packedAt q14K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 29 q14Pos q14Neg, 0xfffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q15K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q15R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q15K3 (i*3) 3
  | _ => 0
def q15I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt q15K3 (4+((h/1+packedAt q15K3 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q15Atlas : Atlas := ⟨3,rawDecor 19 q15Pos q15Neg, 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q16K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K5 : Nat → Nat
  | 0 => 0xa714aa67ac10062218e5a402e00042020001a4a83021882006006fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def q16K4 : Nat → Nat
  | 0 => 0x5808000000404008000600020444a0a000141e1a0c8000000048040000000000204000180203010101c00be41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414cbdd0532b7414caf10532f4414cad10532bf404cbed0132bb404caf10132f8404cae10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432bd410caf90032bd400caf90b31bd42cc6f90331bd40cc6f50e31be428c6f50a31de328c770ca31be418c77cc631f7318c6f90231bd408c6fd0931ef424c6bd0931bc424c7b10931ac424c7dcc531de314c6fd0131fb404c6ed0131bc404c7e10131b8404c6f90c31be420c6f50831de320c770c831be410c77cc431f6310c774c431f5310c754c431be400c6f50031bf43c86f90f21bd43c86f10f21f731c87d0c721be40c86f50321bf43886f90e21bd43886f10e21bd42887bcca21ec32886f90621ef21887dc8621be40886f50221bf434877d0d219f43486f90d21bd43486f10d21dc43486710d21f721487b88521bf40487ed0121bb40486f10121f840486e10121bf43086f90c21bd43086f10c21be42087bcc821ec32086f90421f731087d0c421ef21087d88421ed21087d48421e521086f90021bd40086f90b30bd42cc2f90730bd41cc2f50e30be428c2f50a30de328c370ca30be418c2f50630de318c370c630be408c37cc230fb308c2fd0930ef424c2bd0930bc424c3b10930ac424c2fd0530f7414c2dd0530bc414c3d10530b4414c3ecc130de304c2f90c30be420c2f50830de320c370c830be410c2f50430de310c370c430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20be41c82f50720fb30c83e0c320bf43882f90e20bd43882f10e20bd42883bcca20ec32882f90620bd41883b88620ec21882f90220ef20883ec8220bf434837d0d209f43482f90d20bd43482f10d20dc43482710d20bf41483dd0520b741482f10520f441482d10520fb20483b88120bf43082f90c20bd43082f10c20be42083bcc820ec32082f90420bd41083b88420ec21082f90020fb30083e0c020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43ecc310f830c43ec8310f820c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610f731843d0c610f721843d08610be40843dc4210fb10842fd0d10df434427d0d10be43442f50d10bc43443710d109c43442fd0910ef42442bd0910be42442f50910bc42443b10910ac42443ec4110f610442fd0c10be43042f50c10bc43042fd0810be42042f50810bc42042f90410f731043d0c410f721043d08410be40043ecc010f830043ec8010f820043dc4010fa10043d44010f910043c44010
  | 1 => 0x3064090021da73a3e630e22e906358da7c9b22f0781ca0c001983e0660025a00098000ac77000842085f004148008d9d0000020714e6a884000000f242000a00007a15138258606514c7080a2691051800042021f9ca7e9740ba4e690d4469c40011c371181c0004a800159de000c08a8000f8d85280030800891c6910aa4080086042320be01a2e84800001f8348005600004800310de4c1527a0943a00039924878460000000076000000011e2715a0b0fc110004f0320606a880ea8f1d61a114649ae7b8801206c8c90a4b092601722d1fc068a27f8b67200e0586e6f014000260e05c6b1628188a55a0a0013a7d034000fe001d85b8008d00000000001a0499be658864c85e3805a5e9a81620e339ba000002c9202c0ca4a01e95000340003ea463d9d24890457800330005424a1d18e8a17600064000405203a9498a0011240154188006d164000b8679c0000a44588e889700a99a208006e088002005a0ee511a64b9b62b80c59a560024c0017e002385aa0478000090a63c8000000012a3a9400000000000a800000000c690000001cc789348680000108001b0000009622c002160a178279f61f00000000870000d84c00184002304f90e50a147a986000001400039000572483d0220016c670006080068960000f0001407b00075000081887c1e44da263b0002304e001e64300003094080d0000800000687402270300002000080000011303c02040081c06050600400070002c0001038080401010000a0000008000a0002c020001808000100828020416800
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x88632f5250031962928018ce94343c8672a1a1e4397430c7219d2868710ce543438871e86194431e5390d219d2848690ce542434865ea4a1a43375150d219da828690ce141434863ca821a439443c8521c621c4290e6d0f404873087a02439b4310121cc2188090ecc84404875442202433b5050c219c2828610ce9404308672a0218432d540c821c6a186410d9544320866aa81884395430c421b2a906210f10c831086caa5108432f5448421a629a4210da141210866ea890843545348421b82824210d9d51210874ea890843c75348421b329a4210d914d2108788a690843445348421f1a824210d914121087c0a0908436050484218fa9a8010c714d400874e85a0a61a442d0530d3a10829869108414c3508598261b041cc130c6214609865106304c26ea2a1061345150830c6a10641856540320c25ea4a08612c5250430caa08621856540310c2b2a7180611f544c030a6292601855145300c276a89806168524c030b828a601856d51300c336a898061cb524c030ac292601872149300c290a498061d3514c030ac28a601874145300c2a0a2980613651d0f209aa8e879066d0c30c826ca3a1c413551d0e20c7a1865104794e434826ca321a41355190d2097a9286904dd454348268a2a1a413b5050d208f2a0869065d0f414832887a0a41974310520ca21882906610f204836083902418c4388120d220c40904dd454308268a2a1841365110c209aa8886104b550320831a861904169500c8208fa9a82104714d410834a82108416950084209caa060106650c30082d2a418041c8320c020b4a9440104bd512008298a6900416451480209daa240105614d20082e0a2900416b5448020d5aa2401072d4d20082d4a690041685348020e429a40105214d20083c6a290041685148020f028a401058145200825ca5a1e212d52d0f108f29e85884754f42c43368618621ab42083109729687084b54b438423ca7a14211d53d0a10cba18630869d08218423ca721a212e5290d1096a9486884bd494344258a4a1a21375150d109da82868847950434431e87a12218c43d09108f29c84884754e424425ca5212211f53509108e29a84884dd454244276a0a12212e5410910c7a1884886310c42443308788221a842c4110ca21c20886910a104425ea4a18212c5250c109729086084b548430423ea6a10211c53508108f29884084754c420426aa81882195430c410b8a8062084d550210434a84108217150084109caa060086650c30042e2a218021d0310c0109caa040086a50820042e2a210021e021080109caa420085c546100426ea888021545344010b229220084ed5110042b0a688021685244010b9aa220086cd5110043a6a688021725344010b829a20087414d10042a0a688021e35244010b929220085c14910043c0a488021605244010
  | 1 => 0x924b00079048221dc00000651503894e0022a6d91c52800490088518c2f1ea3f0721e9f45f9c25a0644c946338264f8344a1d245876131b45d90e05992799fc3495c359be3a8143e1d0818220013840000000d48b1e80f9700e8001816450978750524f18a00000071128a202189580005e001a23613a661204a9ee1e0022d8ba00000001cc07800001aa5e8281a95e00220000aa7e96a691fe409847e058061de3b1bc450ae608301083c12940839485303247930600384d1ac399522c0ca87896230f0781965110a0aa0c030208902c63a08218ee119366e910641ae489ec768be2d1086c80430806168b84309a0001a738a2619c01a0826206e381607c0a029800000000011a0015400000000c6000c032010000005b0a4002186c1047c8fe150008997c1c0002a0000015a000c472126000001f92e110000002e8000013800000507d962391b82c9d623a0a419c61f0983d99e67040668003a1d800172002040005c84800228945d012159663789e000da888f2371e25ba10240d00006c00000028f4039a60d8802b1a027000871567287400066858fa6a1c48682433118000840500404310007800000087008002b00002060a800000a01810000100018061501000000b0781c020b018000827068040e17050d002001081800000404c54000091000351b078080500018180002868180f0287c0609030000205030640006070d8040308800220101e9cc8414cb2c6420a65b341d0132d820e80996cd04404cb608220265ab3210132cd19080995354e320ca3ea89906554514c832ac28264194bd51320cac8a29906568504c832a7aa2641963d51320cb8ea2990654c514c832e228a641951145320cb96a0990654c504c832e4282641952141320ca76a0a08653850504329ba8a80194d145400cb488598a638c428c531d5a168098ea10b404c7568420263a84210131d99888098e68c4404c676a0a1063385050831c6a106418d5544320c6aaa7188631f544c431a62926218d6141310c66ea89886364524c431b82826218d5d51310c72ea898863c7524c431aa2926218f1149310c688a498863d3504c431aa2826218f4141310c6a0a09
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x16150398860119971100001800000000140000001f80000015800000000a0e000c80130f92000817831f1a108a801a8004070f019680020b098000091e801d80001d001380000680000020800d990d1c800000001b928e84889c2000000c07809000000b91801b02800005148580000000001e00000200911000010008000030a100090000100d0147504c832d0d44504c832d0144504c832a2181420c83194181510c831d014b504c431d0d48504c431d0148504c431a4983430c721a2983430ca21a2181430c82198181510c821a4181430c42198181520c421a1590320c421c1550320c4219198e5348421989825348421d014f5048421d0d4c5048421d014c5048421a1185420c83094185500c830a1189410c43092189500c430d014b514c030d0d48514c030d0148514c030a4987430c320a1987430ca20a1185430c82098185500c820a118d41084209218d5008420a4185430c02098185520c020a2590320c020c2550320c0209298e5348020989865348020d014f5148020d0d4c5148020d014c5148020a298b430c310a298f4208310a198b430c610a198f4208610a1189430c41098189500c410a118d42084109418d5008410a2189430c01098189510c010a4590310c010c4550310c010a218d42080109418d5108010a85902108010c855021080109498e53440109898a5344010d014f52440109498e52440109898a5244010d0d4c5244010d014c5244010
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt q16K6 (i*4) 4
  | 5 => packedAt q16K5 (i*15) 15
  | 4 => packedAt q16K4 (i*26) 26
  | 3 => packedAt q16K3 (i*37) 37
  | 2 => packedAt q16K2 (i*48) 48
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt q16K6 (5+((h/1+packedAt q16K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt q16K5 (400+((h/8+packedAt q16K5 (360+(h % 8)*5) 5) % 29)*6) 6
  | 4 => packedAt q16K4 (8752+((h/100+packedAt q16K4 (7852+(h % 100)*9) 9) % 399)*10) 10
  | 3 => packedAt q16K3 (11160+((h/93+packedAt q16K3 (10323+(h % 93)*9) 9) % 335)*10) 10
  | 2 => packedAt q16K2 (3322+((h/22+packedAt q16K2 (3168+(h % 22)*7) 7) % 115)*8) 8
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffdfc3ffff1ff1ff
  | 1 => 0xffffffffffffffffffffffffeffc3fffe3fe3f
  | 3 => 0xfffffffffffffffffffffffff7ffc3fffc7fc7
  | 4 => 0x7bfffc3fff8ff8
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffa078888b0490db
  | 1 => 0xffffffffffffffffffffffff908b911521262d
  | 3 => 0x9113a26484b46
  | 4 => 0x62223b8920db0
  | _ => 0
def q16Atlas : Atlas := ⟨6,rawDecor 27 q16Pos q16Neg, 0xee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x80a62004a2f195c32bc6370c6f985d30
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x132000096418ca390a318c424c2510530
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
  | 4 => packedAt q17K4 (5+((h/1+packedAt q17K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q17K3 (96+((h/2+packedAt q17K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt q17K2 (108+((h/1+packedAt q17K2 (104+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 2 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 2 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 39 q17Pos q17Neg, 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x980201002842f995d32bc6370c6f185c30
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x10608094414ca6101329a408c6590630
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
  | 4 => packedAt q18K4 (5+((h/1+packedAt q18K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q18K3 (98+((h/2+packedAt q18K3 (90+(h % 2)*4) 4) % 14)*4) 4
  | 2 => packedAt q18K2 (107+((h/1+packedAt q18K2 (104+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 1 => 0x6efe3fcfe3ff0cfc
  | 2 => 0xfffffffffffffffffffffff7ffcffffc7fff1f
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c824304926171
  | 1 => 0x11258415212624b4
  | 2 => 0x840280848488a0a
  | 4 => 0x7892eae920ccfc0
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 23 q18Pos q18Neg, 0xe8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x4002031000005f32dc6574cb6994d32
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q19K4 (i*4) 4
  | 3 => packedAt q19K3 (i*15) 15
  | 2 => packedAt q19K2 (i*26) 26
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q19K4 (5+((h/1+packedAt q19K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q19K3 (79+((h/1+packedAt q19K3 (75+(h % 1)*4) 4) % 11)*4) 4
  | 2 => packedAt q19K2 (27+((h/1+packedAt q19K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 23 q19Pos q19Neg, 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1401e08088a40600038000068020c816600000484700128c03007f90c01fd43007f90401fd41007fcc401fe31007f4c401fc31007f90001fd40007fcc001fe30007f4c001fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2e8d80a9a4da052e7c1508452301c8003c1a52a60c83c4a0003a4244134fc7356800b27a0e24c9e853c02000654e13916802611400774e90400002f88092001d0003e00000ac00000024400ac189a44e551d830125620000000d0d90ca6b009aa906820000000a9508012a0050000b8000027c7e2e239105a6b2ba99180a1a24058113405802501f0dd468a019ec001019118180c001a04000062aa0c00cc12040000281a36000a16040a1e400012040610040000141000080a061a04001c06001200002e0002360216000a240000bf58a43086f8a521802fe6190c23be28c8600ff88643087f84321802fe6090c23bfa848610ffc8243007fc4121803fd2090c21fe1048600bfd8943005f8c2a18037e5150c01ff10a8600bf18143006faa0a1803fe2050c01fe902860fffd4a41076fca52083bfc529041dbe294820fffd424107efea1208037d509041ffe284820effc8241007fc4120803fd209041dfe1048200b7d8d41005b8c6a0802ff62504017e302820ddfd4141007fa40a0802fd62cc4017f306620cdfd4331007fa4198802fd628c401dfa146200ef50a31007be65188037e518c401ff10c6200bf98231006faa118803fe208c401fe9046200afd9131005fec498803bd424c4017e3026200ff48131005fac41882b7c520c401dfa106200f74c83105ef8a218803d5310c401ff108620aff08431005fcc01882f7f500c415ff9006200ff88031007fa401882bfc200c4017eb148009df94a4004ef8a520002fe6190001bf28c8008df14640007fc4320027fc2190011bfa848000df54240005fec4a0002fc6150001ff10a8000bf58b300077e8598003dd32cc0017f30e6000ff88730005fac51801fff428c001dfa146000ef50a30005fcc3180037e518c00ffe20c6000f70c630007fc43180037d508c0015fb226000bfd8930037fe8498003bf424c001dea126000f7cc930005f8c29801bff414c00dfe20a6000ff88530007fa4298002fd620c00bbe2906000efd0830005fcc2180137c510c001ef1886000ff8843002ff842180137f500c001ff21e2000ff50f10005fac588003bf42c4001fea162000ef50b10007fe6588003fd32c4001ff18e2000ff0c710007fc4388003f621c4001fa90e2003dfd4e10005fac508003bd4284001fe9942001bf9821001efea108002bf64440016fb1a2000b718d10005fec488002ef6244001dea122000ff4c910007ec42880077e6504001beb282000ff59010007fcc608003fd6304003bfa982000df54c10007fc8608003fd43040017fb102002ff98810007fac408002fd6204005bf2902002df148100077e840800bfe4204001fea102000ef50810007fe640800bfe3204001fe9902002ff0c810006fca2080077c5104001ff1882000ff0c410007fc420800bfc2104003bfa802000df54010
  | 1 => 0x8c005225a3c6a244492800001c1c8f29e05848300e00248047d331d0ce600798d488457a34b0760a184e2ae14000c4042d05cdca81796d4470438650c22288984a540a920daab000000075002387a6c538192c00379a8005e199fc0e99
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe76d0930004be76d09300373e75d09300373d75d09300c6bc65d09300073e51d093012f3c51d0930004bc76509300b6bc65509300078d32509300073e51509301273c5150930004fd7218530006bf4218530006bd4218530006df3218530004fc7688530006bf6488530006ef6288530004fc7648530006bf64485300067c7558830004fc71588300067c515883011ebd76d083011f3e75d083011f3d75d08300c6be65d08300c63e65d083002ebd62d08300073e51d08301173c51d08300067c5298430006bf4298430006dd628c4300079f428c430004ff768843009e7e6588430006f66188430005f47150f100c6be65d0b1010f3f53d0b100073d53d0b10006bf7650b100073f7550b101073c7550b100b6be6550b101073f5350b100073d5350b100073e5150b101073c5150b10007b87050b100075d53ccb100075d534cb10007ad424cb100077651887100ff7451887100ff7753887100077553887100f77753487100067f5358a10006bf7650a100073f7550a100ef3c7550a100b6be6550a100b63e6550a100ef3f5350a100073d5350a10007b47150a10004ff764ca100075d534ca10007ad424ca10005f4714ca10006af74d8910006ef73d8910006bc7650910004bc76509100073f75509100e73c75509100b6bc65509100b63c65509100069f63509100e73f53509100073d5350910006af6250910004fc764c9100debc644c9100075d534c910006ef624c910007ad424c9100d77753885100067e64594100057f73594100067e65590100067d65590100067e6598c100067d6558c10005bf7458c100057f7654c100047f7654c100ce7e6454c100ce7c6454c10005747154c10004fd7690c10004ff7650c100067f53d88100067d53d8810014fd72d88100067e65588100067d65588100067f75588100067c75588100067f53588100067d5358810016ee4258810016ee32588100067c5158810016ec21588100c6be65d08100bf3e65d08100c63e65d08100073d65d08100c6bc65d08100bf3f53d08100073d53d0810015bd72d0810016bf62d0810016bd62d0810004ff76508100b67e6550810006ed6250810005f47150810006bf7650810006bc76508100073f75508100af3c75508100b6be65508100af3e65508100b63e65508100073d65508100b6bc65508100af3f53508100073d5350810016bf6250810017ae6250810016bd6250810007ad6250810006ad6250810017ae3250810007b77150810007b471508100af3c5150810007bb7050810007b870508100075d53cc810004ff764c8100075d534c810006ed624c810007ad424c810005f4714c8100057d73944100067d62944100073d42944100057970944100a774510c41009e7e6588410006ed628841001c7f76540100967e64540100067d64540100057f7354010
  | 1 => 0x10200004000100830000002416060000c0c0000014180f0200800010181000010202c00030002400010080026000003410080081008050001000060002c0e030680408030067c7558a43086bf4258a43004fc7158a430067c5158a430debc4158a430067f5058a430debc4058a430067c52986430067f5098643004ff768864309e7e6588643004fd72982430067c529824303ebf4298243004ff7648243004fd72185430067f62945430073d42945430057d7094543004fc7688543004fd721814311ebf42181430067f62541430973f42541430073d42541430057c71541430067c6154143004fc76481430057f73542410073e43542410973c43542410067f62542410067d62542410973f42542410073d42542410977441542411557f705424107d7e758824107d7c75482410065f5018d410067f50d8941004fd7218141004fc764814106d7c7548141006df6348141006dc63481410067f5058b31004fd7298331004ff7648331005f471483310c6be65d0a311873f50d0a310b6be6550a310078d3250a3117f3c5150a3117f3f5050a310073d42946310057d7094631004fd7298231006bf4298231006bd42982310967e64542310067d64542310067d62542310073f42542310073d4254231004bc76509310b6bc65509310b63c65509311773f50509310073d5050931004fd7218131006bd4218131004fc7648131006bf644813115ebc64481310067c75588310067c5158831056ec21588310067f5058831056ef20588310c6be65d08310c63e65d0831056bd62d083116f3f50d08310073d50d08310579f424c83109e7e6588431006ed6288431167745188431004fd72980310067c5298031006bf4298031004ff7648031006ed6248031005f47148031007d53148031006fa60480310067f7558a400067c7558a4004ebf4258a40004fc7158a400067c5158a4015ebc4158a400067e52986400067c52986400047d76946400057d73946400073e43946400067d62946400073d4294640004ff768864009e7e6588640006f661886401547f76542400057f73542400073e43542400973c4354240004fd7218540004fc7688540006ef628854014ebd76d0b3014f3e75d0b3014f3d75d0b300c6be65d0b300c63e65d0b300073e51d0b301473c51d0b30006bf4298730006dd3298730004ff768873009e7e6588730006ed628873003ebd76d0a3003f3e75d0a3003f3d75d0a300c6be65d0a300c63e65d0a3013f3c51d0a300b6be6550a300b63e6550a301373c5150a30006bf4298630006bd4298630006f441986300047d76946300067d64946300067d62946300073f42946300073d4294630006dd620c6300079f420c630004ff768863009e7e6588630006f661886300247f76542300967e64542300067d6454230004bd72d9130036b
  | 2 => 0x309705219c32a54128004a840099aa410ac9c000722340620c379124689e0a0f61902000274000001d0b034094931948f03e550000000076172408325706266a10678d88e84c6a0dc158fc298ba0327c26000001f83a8c8001c6002469712ca1a8c2b8003d000751ee810008487233a320018c001da00158460000900000000001000ba300004e001640011e310600f1e86b8f2048040007e2d8227f800708066d09051000150006221494a80000000015e4e17a53042001d090800198020006a808aa880348613a5a10a00070519a092846600a44f09a001ac0027e0016a7823e000001b8000013000000000000012000000858000026a00000001085980000000a10000000034a6600000051268da7a2818e24a2421a2a9800e8b12238a488b9bc458bc69a0a000000003000000589ba1b0880012e629e2330003c0c6000a26601a798b23a0ec00000988007aa286103a5b2580007a111be83a64a38e0001cc00052001f2001140007800132508685e05e000009000088800711860001c07800548e6a297e8196e12136001b023140959fc00000418002d02a0025e0e11c559f48680a00000a2000000001d8ee5285c3026e208107c21c0000077016001a400036a4a443f800728001680000000001de7b058a4050001b68007c000000000079000640004d000000a8701ce0017c4a080a08847ea682e1d2359963e8da00000938000002c002766e10c00192000008e0002280000000688be021825d27889a506c80053800000e4000009c92496a1e00000259d6000000015a001f60000000000001764f91027208000000010e0008e9b1503e0d45801a01070040003028300c050680c08000380c00040001c1800008000000018180c060000406030200402000004c00030400c08040a000040
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe2d42d41620c40147f0ca868418802cd20550d08310078a98aa1a10620087d8714a600c4014bb06294c0188029e60052980310c61f3ae8530062009d4874c5200c401c5a85baac5200630f9d07558a4000716a10eab148000e2d4214562900010fd0f294c3200029da0652986400043f438a530c8000a5d8314a61900014ed02294c3200030fd0976946400043fc3ac528c8000c3d7650a5190001c5ac4a14a3200ab0fdda43542400051ec34a3a166018c3c75d0a61cc031878eba14c31805b0f1d542986300061ebb68528c6000c3d7650a518c00187f0ab96c8980030f21572d91300061f28ae5b226000c3c515cb644c00187d0b3b684980030f61676d09300061e28ceda126000c3e76947424c00187d0a3b284980030f61476509300061e288eca126000c8c764c9424c069e18a299284980030f9da51509300061e3b4a2a126000f0d32945424c03187ceba10c2980038d14742185300b61f3aa8430a6000cad72508614c001d1a64a10c2980038d145421853000716a10eab106000e2d42145620c00147b0d28e84180021fa1c52984300052ec18a53086000a768114a610c031878eba14c21805a8fa177650b1000786a9a849962016a3c85dd9428400147b0dbaa85080028fe195350a100059a40aa6a142000a5f8654d32840016a902a9a65080cb8b995424ca1000786a9a849942000e2e85dd36244001c5b0bba6c4880038bd4f74d891000716a9ee9b122000caf74dcf6244001c9aa7b9ec48805a8f21476509100061e3a8eca122000c3f851d942440018790a3b284880030fd4c76509100051f436eaa122000c3c76dd54244001c3eebb1a8488003871d763509100051e432a6a122000c3c7654d4244001c5eebb1284880038b1d7625091000717a9ec4a122000e2d53d8942440014b90ca9a6488003171d9534c91019f0e322a69922000e4d53d8932440015590ca1264880032b1d9424c9101971632a849922000f0d5350932440014bb0732cc6080030f1d16558c100061eb2ee8b182000c76641c553040018e8c838aa6080021fe1d53d88100053a40aa7b10200087c8754d62040014e902a9ac4080628fe1965d08100051fc32a7a102000b348154f420402d4790bbb2840805a8fa1476508100051ec36eaa102016a3f86595420400147f0ca9a8408002cd20553508100071732ac4a102000e2d655894204001c5f0ab1284080038b215625081000717baac4a102000e2c755894204001c5ea6b1284080038b54d62508100071628ac4a102000ea562dc54204001d4ac438a8408003aa58b705081000754b10e0a102000db0711c142040014bf0ca9e6408002d520553cc8100052fc32a69902000b548154d3204001c9aa6b1264080032bdd9424c8101971732a849902000f0d5350932040630ff0eb14a2080038b5894294410
  | 1 => 0x69563b00000a66711160a48b1c87c0078212855e10328014a00002355a000026936004200018850016c00690015810344f001023a41a8c88000029cc200030000000561b0f600000000088248005e001009952002e060ba8900288000019800aa6e25838003009164807701004289518a08da004907048362397c007f1c1d41e4514a00e637300013a484a1f05404089285a6816259666b05058cc90141c11e3d00079609c26074b40031025220311ac95441271c8007937800f4071a8000000000acfa0021a98005e0025cec860c8b87e1b49a1d3e4d0b8f800a45882d32002303400ae4c1911c8c191c568501e094001509950420045000000000000e85700144c6a8001a84e4f3f0000aa0020206008b820101010180020100030001008081020980028280808081038000010e0181020009828101088003800b008984830006020180000000020630f9d07558a4300716a10eab148600e2d421456290c010fd0fa82c5218038b50b5058a430043f438a530c8600a5d8314a6190c010fd0fa84c3218021f61c52982430052ec18a53048600e2f6250a5150c01c5ec4a12a0a18031d1c461541430049f43c86a84820087e87d8950904010f90eb12a1208024f21d425424100716b1284a848236e1f42d406350401c3a85a80c6a08038b50b50d89410062e3a8c69028200e2d42d4162cc46be18a299285188d7c3d413250a31007869928528c6218c3e75d0a608c42d87ceaa14c1188021f21d64542310078699284a846200c3f851d9424c4018790a3b284988030fd4076509310051e432a0a126200c3e76541424c401878eca828498803c50c550509310b61f3aa843026200cad72508604c401c5a843aac4188038b50851588310043f43ea0b106200
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x104ba00672ad3002692802e7ac3b662258408850c68003202000a0380811c00c00001450050b25d6250950904016149150b5018d4100543e5d3250a518c40150c974c94254231007050c7851d9424c401c14312147650931007050c7501d9424c401a14860c55050931007051d831541424c401314984c550d08310050be5d6250a5190001c0e951d9325093000703654764c9424c001c0c511d93250930007031d932945424c001e0532145421853000583e595350932840017049154d424ca1000703dd153dcf624400160c9654d424c91000683219535093244001c0c7654d424c9100050b648745956304001465921907154c1000589245535894204001ca1621c470508100059124553589320400160f9654d424c810005c124553509320406f42f975894294410
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4e
  | 2 => 0x4b
  | 3 => 0x124e
  | 4 => 0xce
  | 5 => 0xcb
  | 6 => 0x9cd
  | 7 => 0x12cd
  | 8 => 0x130e
  | 9 => 0x130b
  | 10 => 0x24b
  | 11 => 0x24e
  | 12 => 0x16ce
  | 13 => 0xb8e
  | 14 => 0x148b
  | 15 => 0x148e
  | 16 => 0x178b
  | 17 => 0x178e
  | 18 => 0xa4d
  | 19 => 0x140e
  | 20 => 0x24056
  | 21 => 0xd0056
  | 22 => 0xd0e
  | 23 => 0x188056
  | 24 => 0x188e
  | 25 => 0xecd
  | 26 => 0x140956
  | 27 => 0xccd
  | 28 => 0xd0956
  | 29 => 0xd1256
  | 30 => 0xb1396
  | 31 => 0x141396
  | 32 => 0xd1396
  | 33 => 0x189396
  | 34 => 0x1880d6
  | 35 => 0xcd
  | 36 => 0xd09d6
  | 37 => 0x1889d6
  | 38 => 0xd12d6
  | 39 => 0x1892d6
  | 40 => 0x189696
  | 41 => 0x168d
  | 42 => 0x198d
  | 43 => 0x98d
  | 44 => 0x140256
  | 45 => 0x188256
  | 46 => 0xd0b56
  | 47 => 0xd1456
  | 48 => 0x189456
  | 49 => 0x154e
  | 50 => 0xd0cd6
  | 51 => 0xeccd5
  | 52 => 0xccd09de
  | 53 => 0xccd145e
  | 54 => 0x198255
  | 55 => 0xd1556
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 18
  | 7 => 177
  | 6 => 330
  | 5 => 181
  | 4 => 30
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (498+((h/6+packedAt gbK8 (468+(h % 6)*5) 5) % 28)*6) 6
  | 7 => packedAt gbK7 (7021+((h/59+packedAt gbK7 (6549+(h % 59)*8) 8) % 213)*9) 9
  | 6 => packedAt gbK6 (16830+((h/110+packedAt gbK6 (15840+(h % 110)*9) 9) % 479)*10) 10
  | 5 => packedAt gbK5 (11159+((h/60+packedAt gbK5 (10679+(h % 60)*8) 8) % 239)*9) 9
  | 4 => packedAt gbK4 (2160+((h/10+packedAt gbK4 (2100+(h % 10)*6) 6) % 37)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf80fff00fffffffe03ffffff471f3f191ff1ff
  | 1 => 0x1ff03fff01f01ffffc0ffe00b8e7cfe6e27e7c
  | 2 => 0xffffc00001ffe03ffff03fffc0f8f1ff038f8f
  | 3 => 0x1ffffffffe00003fffffc000ff00fe07fc0ff0
  | 4 => 0x1fffffffffffffc000000000ffff0007fff000
  | 5 => 0xe00000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x20014b0062542c4a011662aa030b17080cb0b5
  | 1 => 0x8b0156900b11696a40ab40618654b6262565c
  | 2 => 0x5d5a8018112b42256aa01954c0b0a0b7030b0a
  | 3 => 0x166ce6b2b4020039d3cd0018ed00fc05b40de0
  | 4 => 0x1f8f38dcd9cf9b0060801060f6fe0007dbe000
  | 5 => 0x840800e0e00c1c01830e2180ffdfffd8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 5, 0, gbRaw),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 5, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 5, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444, 4, 0, gbRaw),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 4, 0, gbRaw),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 5, 0, gbRaw),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000, 5, 0, gbRaw),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 4, 0, gbRaw),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 4, 0, gbRaw),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 5, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 7, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37453
namespace PEqualNP.Outside.L_meta_37453
open PEqualNP.Outside.L_meta_37453.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_32 : Interval s2Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_64 : Interval s2Atlas 2 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 66 := (concat bs2_2_0 (concat bs2_2_32 bs2_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_128 : Interval s2Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_160 : Interval s2Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_192 : Interval s2Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_224 : Interval s2Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_256 : Interval s2Atlas 3 256 23 := block_range (n:=23) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 279 := (concat (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96)) (concat (concat bs2_3_128 bs2_3_160) (concat bs2_3_192 (concat bs2_3_224 bs2_3_256))))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 302 := (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 bs2_4_192) (concat bs2_4_224 (concat bs2_4_256 bs2_4_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 24 := bs2_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
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
theorem bq1_2_0 : Interval q1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq1_2 : Interval q1Atlas 2 0 3 := bq1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_3_0 : Interval q1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq1_3 : Interval q1Atlas 3 0 6 := bq1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_4_0 : Interval q1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq1_4 : Interval q1Atlas 4 0 1 := bq1_4_0
theorem allq1 : ∀ k ≤ 4, ∀ i < count q1Atlas k, checkRow q1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq1_2 i (by omega) hi
  · exact allq1_3 i (by omega) hi
  · exact allq1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_2_0 : Interval q4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_2 : Interval q4Atlas 2 0 1 := bq4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_0 : Interval q4Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq4_3 : Interval q4Atlas 3 0 5 := bq4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_0 : Interval q4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_4 : Interval q4Atlas 4 0 1 := bq4_4_0
theorem allq4 : ∀ k ≤ 4, ∀ i < count q4Atlas k, checkRow q4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq4_2 i (by omega) hi
  · exact allq4_3 i (by omega) hi
  · exact allq4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 1 := bq7_3_0
theorem allq7 : ∀ k ≤ 3, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 1 := bq8_3_0
theorem allq8 : ∀ k ≤ 3, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_2_0 : Interval q9Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq9_2 : Interval q9Atlas 2 0 3 := bq9_2_0
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
theorem bq10_2_0 : Interval q10Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 3 := bq10_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_3_0 : Interval q10Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 6 := bq10_3_0
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
theorem bq11_3_0 : Interval q11Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 1 := bq11_3_0
theorem allq11 : ∀ k ≤ 3, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq11_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_0 : Interval q12Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 1 := bq12_3_0
theorem allq12 : ∀ k ≤ 3, ∀ i < count q12Atlas k, checkRow q12Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq12_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_2_0 : Interval q13Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq13_2 : Interval q13Atlas 2 0 4 := bq13_2_0
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
theorem bq14_2_0 : Interval q14Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 3 := bq14_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_3_0 : Interval q14Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 6 := bq14_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_4_0 : Interval q14Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_4 : Interval q14Atlas 4 0 1 := bq14_4_0
theorem allq14 : ∀ k ≤ 4, ∀ i < count q14Atlas k, checkRow q14Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq14_2 i (by omega) hi
  · exact allq14_3 i (by omega) hi
  · exact allq14_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_3_0 : Interval q15Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 1 := bq15_3_0
theorem allq15 : ∀ k ≤ 3, ∀ i < count q15Atlas k, checkRow q15Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq15_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_2_0 : Interval q16Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_2_32 : Interval q16Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_2_64 : Interval q16Atlas 2 64 2 := block_range (n:=2) (by decide +kernel)
theorem allq16_2 : Interval q16Atlas 2 0 66 := (concat bq16_2_0 (concat bq16_2_32 bq16_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_0 : Interval q16Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_32 : Interval q16Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_64 : Interval q16Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_96 : Interval q16Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_128 : Interval q16Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_160 : Interval q16Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_192 : Interval q16Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_224 : Interval q16Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_256 : Interval q16Atlas 3 256 23 := block_range (n:=23) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 279 := (concat (concat (concat bq16_3_0 bq16_3_32) (concat bq16_3_64 bq16_3_96)) (concat (concat bq16_3_128 bq16_3_160) (concat bq16_3_192 (concat bq16_3_224 bq16_3_256))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_0 : Interval q16Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_32 : Interval q16Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_64 : Interval q16Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_96 : Interval q16Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_128 : Interval q16Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_160 : Interval q16Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_192 : Interval q16Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_224 : Interval q16Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_256 : Interval q16Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_288 : Interval q16Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem allq16_4 : Interval q16Atlas 4 0 302 := (concat (concat (concat bq16_4_0 bq16_4_32) (concat bq16_4_64 (concat bq16_4_96 bq16_4_128))) (concat (concat bq16_4_160 bq16_4_192) (concat bq16_4_224 (concat bq16_4_256 bq16_4_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_5_0 : Interval q16Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq16_5 : Interval q16Atlas 5 0 24 := bq16_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_6_0 : Interval q16Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_6 : Interval q16Atlas 6 0 1 := bq16_6_0
theorem allq16 : ∀ k ≤ 6, ∀ i < count q16Atlas k, checkRow q16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq16_2 i (by omega) hi
  · exact allq16_3 i (by omega) hi
  · exact allq16_4 i (by omega) hi
  · exact allq16_5 i (by omega) hi
  · exact allq16_6 i (by omega) hi
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
theorem bq19_2_0 : Interval q19Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 1 := bq19_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_3_0 : Interval q19Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 5 := bq19_3_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 30 := bgb_4_0
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
theorem bgb_5_160 : Interval gbAtlas 5 160 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 181 := (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160)))
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
theorem bgb_6_320 : Interval gbAtlas 6 320 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 330 := (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320))))
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
theorem bgb_7_160 : Interval gbAtlas 7 160 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 177 := (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 18 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq1 (cert : Complete q1Atlas) : Lower true (roots q1Atlas) (target q1Atlas) 5 := by
  have ready : Ready q1Atlas (asRow q1Pos) (asRow q1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 5 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 4 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 4 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 4 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 4 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 4 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 7 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0eee8e8e0eea8e8a0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq1 : Complete q1Atlas) (certq4 : Complete q4Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 32 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq1 certq1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 6 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : Sig) 4 :=
    slice_correct (ms:=fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : Sig) 4 :=
    slice_correct (ms:=fixRows 36 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 32 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 33) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : Sig) 4 :=
    slice_correct (ms:=fixRows 36 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : Sig) 4 :=
    slice_correct (ms:=fixRows 8 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : Sig) 5 :=
    slice_correct (ms:=fixRows 16 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00 : Sig) 4 :=
    slice_correct (ms:=fixRows 36 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 7 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241376 * 2 ^ 32 + 4004047008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37453.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[2,6]⟩,⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.and,[1,8]⟩,⟨.or,[2,10]⟩,⟨.or,[7,9]⟩,⟨.and,[1,12]⟩,⟨.or,[0,13]⟩,⟨.or,[11,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 4004047008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241376 * 2 ^ 32 + 4004047008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37453

open PEqualNP.Outside.L_meta_37453 in
theorem PEqualNP.Outside.L_meta_37453 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 4004047008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241376 * 2 ^ 32 + 4004047008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq1 allq4 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allgb)
