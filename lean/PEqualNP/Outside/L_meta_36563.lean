import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36563.Model
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


end PEqualNP.Outside.L_meta_36563.Model

namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 5, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36563

namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x210780000000bc40de30be43bc43dc30f410ee20ec20bc42be40bd41f610be42bf41
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x900881004b94a4396292833850507a060086c100108f29c851c535079060107808010
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt s0K4 (224+(h % 18)*4) 4) % 14)
  | 3 => 2*((h/10+packedAt s0K3 (243+(h % 10)*4) 4) % 9)
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
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
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
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf807f807f80fe03ffc0fc0fc1f80fe07f64cc7
  | 3 => 0x7fff8000ffffffff000ffe000fffff870ff
  | 4 => 0xfff80000000fffc07fffff000000fff81f80f8
  | 5 => 0xfffffffffff000007fffffffffff00001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8304850508020810430c50c228e164922955b
  | 2 => 0x5552d534a39653aa3e0b54b51b12aac7564cc5
  | 3 => 0x46a4a4a5352a95345ad820db4824cd969870ae
  | 4 => 0x64c6c6c6c6cd1a276f6db6821248f1e31f80f0
  | 5 => 0x87070707070e1c38738e38e39c7081041d6a00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4805c20718400000e28300508a1400170140c0040fe32fe10fc43fd20dc32ff41ff20fc42ff43fc32fe31fd42fe43fc40fc31ff42fd30fd43fc30de32ff40fd10fd41fd40ec32fc10ff32fc21fe40fe21fe42fd21ff31fd32fc20fe41ff10ff21fd31fe30cc32fe20fc41ef32ff30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x78302040180002383800080820001808000b28b848780013682028400268000010a16838098031a06080700850685802b99000880810700dbd4940e619083cc324439864205d14540b7296876c52502dea4985dd4530e6194615e53d0aeaa3a15d94440baa88817651d0f9ca4194f55010aea9c836d528c6b8a6904fd51209faa221cc328439ca8195794e41e7288657651d0abca519734c832b7294635f535039aa0195b54a309e2a241cc320c2dea498db14943a7294655e53102baa7a1730cb31e7a1065cc32907986418d714d21b6a9683cc329039ea8195754f419faa261cf430cb9865a0db94a41e619043cc500cb9864985754c10e7a8865ce420ca7aa910d754c40e6196613e54042bca7104f15130e7218656d52102dca5a0d7d4d42b6a9687cc324879ca6197310832e6194436f5250ebea6885794e21afa9a433d548c6b8a6a0730cb40e619643cd510cadea4885d14520e619281cc32c42d8a498f30c920e6218653c54442baa710ddd45409f2a4435c5350abaa7105b14910b7290817551d0f6a8220d794f41e619441cf500cad8a4987315032e6aa0656e530cb9865905d14530b7290215f534839ca0195b54810e6190415c53443986518ddd4520af29065cd430cadca5195b94a30e619021cc324c6daa520f350832af29821cc510cb9864a0cf95231
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x400044c303003c00d0a3800102005001a0050000984820200000000c201140000400005803a1c08002000309398f524424c6354a41c3550540ca4d650ca41c3150324824e650c910d10cb514c28e64d4432a3592510cac66114032d10c8514828f6454032c395032043843250441d10c9511024d650c840b1584500ca4e62d4d40c3550320424d650cb41c3150324424c6254f41b1987540ca4f650ca41a3990500cac46154032d10c851502c561d0c32c3150324c3443294440a3593510ca8e6494432c3d50324430d540ca319318953906c661d0832a3191500cac6619503293d9432d074432d454093d94320424c6254c1093189531024f650c840c3d50324c24d650c810b1d85500ca4c63548409398f525034432d452093188534830d540ca21b1987430cac56195032c3d50324824c6354b4193194325024e62d4d109318d520430e540ca31c395032887443214530a3590500ca4c650c910b1587540cac561d08329399432503455114432
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s2K5 (720+(h % 29)*6) 6) % 45)
  | 4 => 2*((h/57+packedAt s2K4 (3483+(h % 57)*8) 8) % 129)
  | 3 => 2*((h/50+packedAt s2K3 (2584+(h % 50)*7) 7) % 68)
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
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888eeaaaaaaaa888888, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xcc32
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
  | 4 => 2*((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s3K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 1 => 0xe07f01ffffffffff0781e07c0fffffffe493ff
  | 2 => 0xff8001fff03f03fff801ff800fff07c0f8e3cc
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x220a100460821040188a228462884a4a092615
  | 1 => 0x491462c88514c18b0320c868853194b46490ea
  | 2 => 0x8526b55123a856d568497b2129da4706b8e34c
  | 4 => 0x1658d9a24a0e9b66b5ec12424e6ce218df03b0
  | 5 => 0x1860e1c38c30e3b8c6719c7380708420f6d800
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaaaaac8c88888eaeaaaaac8c88888eaeaaaaac8c88888eaeaaaaac8c88888eaeaaaaac8c88888eaeaaaaac8c88888eaeaaaaac8c88888eaeaaaaac8c88888, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x50115010bd41dc32bf41be40ef32ec32cc32bc40de32
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x6020039aa88818c325069ca519630c840c6aa0658c329031865a0e395032
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x30408359432103043254440a1586540ca0d650cb41
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
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
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s4K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/9+packedAt s4K3 (216+(h % 9)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s4K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 1 => 0x81fc0fff83ffffff0783c1f03ff87fffd24e3f
  | 2 => 0xfe000ffffc0fc1fff803fe003fff8781e38fcc
  | 3 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8828002300208000188442118a0088940490d5
  | 1 => 0x24519644194530cb032191a214c85568d2462a
  | 2 => 0x149aaa8928ea13556842f484a755060d638b4c
  | 3 => 0x59634d125283a5a6b5e8210939a66031bc0db0
  | 5 => 0x61838e1c630c39f8c67339ce01c44441fb6000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeaaaeaaae888e888eaaaeaaae888e888eaaaeaaae888e888eaaaeaaae888e888eaaaeaaae888e888eaaaeaaae888e888eaaaeaaae888e888eaaaeaaae888e888, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa817e5010fee82a0dfd4e21f7296837e540cbbea6a1778c531bea94217e518c2fea2985f94c41dea08837e540c7be6218df94030dfa1a837c5150f7ca8195f54d20bf280437d510c3ee4290df54841bfa9e435c5350afaa110efd5132af29821ee528c2fea8107754c10dea14837751483ea6218df54f21bfa9a217d538c6faa4887d44010bea9487bf4290778a8905f54743bf280217c53082d8a498ef55321f6a14437d53042fca7085f94031dea1a857d51882fca3a05f14810f7210856f5250efaa3995f94732de212837e50906faa6215fd4131bfa92617d508c6faa70857d4d42dea1e85f421842faa990ef90942f7908435c53483de42907750c30bf2a441bd540cafaa908774c832bf29e837c540c2faa020df94a32dfa1a857e509037a8420df54831f6190437c548427ea8995f54640bf294837e52cc6fea8085f94332dfa10837d540cafaa3987ecc230dfa0a813d540437e87a15f54f42bda8263ed42c837c80a05fd5332ee21c657e53c82fca6905f54740f6192417e50106fea4085f94641efa9a41ef21886fca220df94c31be282877d540c6fea090fe0c310bf29c815d53d02fca5a1df15320b7296837d53d06faa9995fd4910dea1085f721042faa890df54e42bf294217d500c7ee4310df14c10af29883ec32886fea2995f94f429eaa4617c548c7f641106f90f40beaa487be41102fca99957d4d10bea98417e54086f8a890f754f40bf280653f54482f8a818fbc8720ef984617c54086fca5215f95221bfa8a815d53042f8a9984f15131be298437d53c837a86205f54b41bf28861bc43d02fea8985f55020bf280417f548c3f260185f94b40bf290857f54887dea498df14520bf2a087ec524c77e8620778c830bea96636e5210378a8995fd4d20de20881ec21882faa898fe88020efa9a21ec32c83dc40906f950319faa2637f54cc77884205f14910bfaa643f451482fca521dfd4d21be2a4657c52842f8a2995f54630df21081ee42086fea2a17b90920ee98e61f7318c6f8a9187dd0641bea84857c53443be65195f54f10f6990653c54483bc86185f54643be282857d51d0af8a0a0df14d41de218853e54cc2fca1a0fbcca32beaa465bd41503b862185f54021bf294637e51102fca210df94810bf29e437d5090efaa2217754c41bea94617d521027aa9985f54b10deaa4617d53487788620df94f10de2a2637e54c82fca4195f54810bf29c877e50d0bdc43106fd0240df2a041ec42ccafca2085f94331bf29087ee42886faa610fed4131bea84837d53902fea8996f50940ef98e61bd548867ca8107754e21bf29c85f830042fca6105f14e10df2a6617e52107de84a15f55010bf28c81bf41d03ba60185fd4941bf298877d53103ee2008778c430bf298433e54c86f8a710df94442f7a92877d534437aa9985f55230
  | 1 => 0xd518cbf620885f94632bf28e417c524c2fea898f750e30bfaa4657c540cafca5985f94a30de2a221bd4310efaa5105f95131bf28085f920082f8a4a1df94321eea1a637f53086faa5a1df55320bf284657c54043dc4290df95041f729081ef420cbb8a6885f55240bf29e81bd41d0278a8996f90c419eaa443be4390afca6197bd4910bea8c857e50102e8a2905f15120b6292217e51883ec6218efd0c43dfa1c877c504c6fca1087d50441bf2a6217e510c67ca9186f55031bea9c657d540c2fea9085f54720fb90c21de53106faa9107b48720dea00817e544cafea5085f55330f7992417e50886faa5205f95030f6a96837c52c42baa710fbcc821bf298817c52503b86598dfd4f10be29c417f548c6faa2105f94642b6a9081de53886fea890de14131bfa9821fb304c37c86215fd4142f629221be54c86faa8907d88421bf28687df4390edca4085f15221fd88421f421042f8a9996f50e40b6a9021bf41906fca710cf95010bf29c417f514827ea8885fd4931bf290417e510caf8a7905f95321be29a817f54c42fca8105f95331bfa9a83ed4210bbe86195fd4943f7994436d528c3d8a4a1ef90640bfa8287bd43d07bc8621f78ca309f2a0657c54443ba8798df54443af29e817c524c6fca6217bd0a429f2a0637e534877e85215f95110bea98837e54486faa1a17ed0140bf28485fb30042fea6105f55231fba8a41dc5350bf681207e44010dea16817f5150efaa7105f14542fb98a63bf4210af8a4a0efd5110f7996417e50883bc87186fd0441bf28e877e548cafaa22077d0d43dfa1681bc419037ca9186fd0f41bf29481fa300c3be60186fd0e40df2a443dc430caf8a8986f90b41bfa96217d5210fd842107bcc932f621065be429027aa990fb48020ef990656d52d07b863185f14d42bf2a463de53042faa1a0df54a41bfaa641dd310c6faa720ef90941fb208837e51cc2f8a8997790d31bf284877c54082dea498df95130ef29e816e528c37885205f95230beaa4837f54086bca710f7cc631de216837e53043bc60985f54232b6292877c514c2f8a0995f54343beaa4437e52d06f8a990df94443bfaa441bd43507da8410df55132beaa2617f53c83b8a6907b88420bea9661df314c2fea818df15331f6a94617e530c3bc6598df55310fc28263fa10043f280205f55021bf2a0817e52442fea6a15f54610de21a813d540caf8a090df94821df21a817d53d02faa1995fd4e20df20a837c53c86fca9086f55020be2a621f710842baa620df14d21ee98a617e520c77e80205f94d10deaa0217e510837ea8904f95221be2a4417e52102faa9215f95010ef18c61ed52103bc8798dfd5110bfa8283fa40102fca8217bd0b329eaa0637c53482fea4a05f54432f790041df438cbda84904f55020ee19061dd4310fdc64195fd4d40be28
  | 2 => 0x10008000000c04c08014050040017c16004000106b000000140000404000850000300400000010103400416000000040c0480a0e000000410800100011088170100d00000028040425401c010581b00c004400000c00024bf06407058290100702c1e0009605c090b0370542d0240000c0b0140a1682f01800510000001a010030300a00003008042dc25004030000102000480000542d000170100a004240300102001040000a40012c24030120002601800010050140102402030003bc000640407c080000210400004011c40101000040030200b014000680005008000021450f054040001e004001fc00128220740000016000120982852412004070200000043018912740000001048000186c1cc0000002044400340e0043e034040081515c4d03c040007a0441c00c0100011008020340002004020060280e001660001601cda000070000a00c00000080042b03c0702c0900802010004f80700c0005c000f4000280001c5d0f000008010004f02c1400004000040040301c0aee194615f53482faa198df54a21ef192657e520c2fea7085fd5330bf28c437e508c678a8885f54a31f729021ee42c83de41105f54e21bf28c877e518c6f8a7885f54032df2a021f610442fca8905f54b40f690a41bf42502fca720df54042f690843fb20482fea8905714d10be2a2637d50c87daa4085f94b10bfa82657f540cbbc6498df94742b7a92217e54cc3ea4210ef90d43de21c85fb30c43b86498df55331bf28461be43907788720df54043bea9061bf544c6fea8185f55110bea9c617
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x251c832d54d08329718d544836461548108f99743507586054c108f99250ccb654214520c7952538863e64951109798c54c825d63d52218f997425023d6590c418f992544ca5f63540219b594320871d5494e21d354c328863e64948219b588548c23e65151328fd91534825d63951309d986534832c54cc9208f592524423e64d4810a718d429073754d4520d68c4504c72d4354b41d3d8953d032f4354b41ab59032c832d54084209798e544835453d4520cb54b401023e64150329b98b5404367321452097d8d544425d63d4810cb150524c66e62949108f9974350a6e62943319ed95100425d6395110b318d424832d52104409b588548423d6494720cb552210823d6595020cb951520423f65504419798c540438f43d08329758e5190b2e54948108f990528436b52141319dd95210872f54149109718d524423d6414f219d584540c34f53d4910cb588544826d6590821a758c411026f65484218f990504872d52908408f191534426e6295310cb150324823d64141218f59353c863c6454c218f590530863c64546208f99353c865d6394910c7152324caad62d07409758f52c423e6494e20ab189439023e64d4c10c7d53534426e62153319758e544836451485209bd89519023e64d4e1097596530426d62d52308fd95421063c64540219758c52042d9600c8309b58a54486cc6250e309758f548823f64544309798f520423e64d4c20cbd50524c63e6415031b318d4210b1e5454e21ab18943d0b4f530c9208f99454482ad640c9209798c530425e6514d10ab1894350a7860551218f992528c65f6354840c754f411074c53d49109758f540425e63946429d984530832d52500408f990524c2ad64c8720cb952428876432145209b98a534425d63952109d984540c35832141318f593520426f65480209718d5090a6e62951108f19152cc66c62544309758c54c829d640ca30c754e43d026d6294d10c758e548c32d52904409b997214825d63145408f990534866d6215331d3548328c26e62141419ed95300c2e462440109798e534825f654c030cb551528c25e63d52209798c515034c6254f40ab18943102d8604c730c7551538863e64944218f59053c423c6454d209bd89534423e6414c209e980548ca3e6414c218f59252c425e63944218f592538823d64944219bd95320ca3e64145309d586534832d54c8020a718d4210b1c540c931d650c504c6796014c21c7d5353483375414520d394d520432d54480209ed81544871d5310c41c7d50534434d53948109798e534431d5454c109798c548863c64542329718d544866d62d4c109798c540c71d5350441d318d521034d53548108f993538865f6354b41cb153324cb1d544c730c714f4350a3f6454a108fd9151cca3f6454d218f997415023d64d4c109b988548431d5494c10
  | 1 => 0x826d62150108fd91524423f6454830c7153534423d6414e21ce153504c63f6454f208f191510c36852141319b99732482756114c20d914a104426f6550842ce150504c71d54d0c3297d8d528423e65151109bd8953d023e64150208f59052042786055131cb152424827a60d4f219798e51c825c6354241b318d420869d64cc030c754e43106746155120e310c420ca3e6494e108f592530c23e6414f208f99053c426d62d50108f990538871d53d07409b988540c36451881208f992544c63d6414a109b594420cb3b54d4131d358b534835a3214131c7551310c66e62d52319e582544c66d6294243b318d428863e64946329dd85544c26d6588420a7191320ca5e65cc5308f590514c23d6494d208fd91534433b54141319bd8954442d863440108f593538865c63551108f19152842d8604c5308fd91508c65e63952108f59053c826e62d4c209b588530423f6550c408f994425067565084109e980530863c6454732cb950328863e6495120d9908514823e6414c108f596540ca3d6590c42c7150534434f6254e219b1895190e6f62551309e580540863d6595010a7590320c26d62141418f99352c423d6494632dad4b504c75a4314131d3d4c524425e6514d20cb548421025e63949108f99053c86746154d20ab590320865e63d50109d58454cca5d658c4308f191508c71c63550329b18953c42ad64c8421a718d421065f63551329b189531063c6454910a718d42d031c548c9318f994544c66c6254f409b988540826f6254d219b189519026e62148108f592534425f6354241cb189540ca6d65948109798e544426c65509208f99250cc66f6254c419b189544c6d8604c43197d95310c72d4354840cbd0d521032e5454a309d98454cca3d64d4e20cb153524c63d6414c20cb90c5250e3d64d4e10c754c43d023c64548309758e51c827b65500409b988540423e64940309718d52d067761551209b58a54c431c5390942cb58a54886cc6350b209dd9510043575314520c754d41d025c63540219dd95411065f6355121c7d50534831c5490d31cb153524434c5314910d614f104431c54d4d208f992524434c53d09429798c520435953cc010d3d8953106ad62d04418f593530826c62551308f990540426e62d4e108f59250cc63d65908409ed81534863f65508429bd895190ead62d06419ed81544c63f6550040a718d425027a60150219798f548874f6354b41a758f409033454145208f590524c25d6315310cb551520432f54d4931cb952528c23f64542328fd91500865c63548409b189544431e548ca308fd954310e7a6095131a7593308c23d64948219e181534869d640c4308f596540c72d5494810c7952438c36852d41318f59250cca3e6494b108f590530431d535084197d8d5090aad64c8621cb54842d065f6550c438f99
  | 2 => 0xd001024071041c05000024110003a0b4000040700c0200005009280b82a2fc8e010011580a2600407c1300c022fc0008400040030000a03cf502032000001700b0e00400c4c084041640b02c200001905c95550142885f030120180709401000070045f02c0808c002e80702c000003008004088d1000b204c010dcff000020180308c031100309c3602c1600004014560a89e000020e80100400004701880208c0f06c04104020f40c080010000c36806050080181d040000b40002c000000d0240900818018500a0e15680006d3402c2f0dc04000190500e3582c00804068000001a058110181b020000301508c0b0eee46148020d394e520426f6254f109b988548c26d62d52318fd91530867960d4f21cb54a42d063f6454f10a7590318c23f64546209798c54c431c5414d20c7553310c6ad64c85209d98654482ad640ca219798f52c425d63152219718d528423e6494d208f19153c834c6354b41ab18943d06cc6250d31cbd53524431d54cc730ab58b415029d63d0040a758c419034c6254c419bd89544ca3e6494c309dd8552442cc6250c308f590534875453145209b588540c26d62943319bd89510c26e62d5230c754f42106746155130b318943cc6ac644c8328f992534427b65480209b98a544c71e5454c10c7952530423d6494a318f59352c423d6590440d3d48324c66d62d4e109b98853042776154d20c754d42d023d64940308f990520425d63150219b994524425d6394421d954b210423d6494e109d586544825e6315021d3d0c5250e5d6590c30b31894310e3f6454b31b9584320865f6355120ab1894310e3e6510d40cd153514831d53d0b409b98b530432d5494a3097d8d524431c5350d429e594300425c6550d319ed81534431e540ca30d5d4f514825f654c832cb150524429d640c931d3d8d521025d63150108f19153c429d640cb319b189534432e54cca219e580548ca6f62551319b58a54442ac6250d419b58a544c679658401097594430ca3e64d4e208f191534866e62942439dd95310c71d6315131d9147214
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xc00000000000182400080400020000062801431c95310c41a18e6a9085a0d25740c85148306a9ac5a0883075d8540c931c32a83026218e0d5358b41d028cba06428263521c9431413185aed2a06510e25541852008286392a621e8186550604c730c1ac6a96802050c7258e548c306318c4aa0658959051c852083aed2a0651860d6354841102a239a8428a41431cd6295221a18e6b10a89050c735484210286392c62a2630b5d8540c920
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x42080c8758d521044080c8758d52d004080c8754d62d074080c8754d62d0441
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
  | 5 => 2*((h/305+packedAt s5K5 (17928+(h % 305)*10) 10) % 664)
  | 4 => 2*((h/193+packedAt s5K4 (20482+(h % 193)*10) 10) % 539)
  | 3 => 2*((h/29+packedAt s5K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 4 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 2 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 3 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 4 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q1K4 : Nat → Nat
  | 0 => 0x5534150f710be42bd41bc43f510bc42bf40dd30bd40df30ef20be43ed20bf41
  | _ => 0
def q1K3 : Nat → Nat
  | 0 => 0x24a5ca521c794e4296292831c53507a260887848110
  | _ => 0
def q1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
  | _ => 0
def q1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q1K5 (i*5) 5
  | 4 => packedAt q1K4 (i*16) 16
  | 3 => packedAt q1K3 (i*27) 27
  | _ => 0
def q1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q1K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/9+packedAt q1K3 (162+(h % 9)*3) 3) % 6)
  | _ => 0
def q1Pos : Nat → Bits
  | 0 => 0x8738fe3ffe1fcfe7fe1c63c7fc787c3fe09d27
  | 2 => 0xf83f0fc38fe3f1f8e1e07cf9879f8fc6036ada
  | 3 => 0xffc00ffc0ffc01ff01ff80fe07e00ff81c731c
  | 4 => 0xfffff0000ffffe0001ffff0007fff0001f83e0
  | 5 => 0xfffffffff000000001fffffff80000001ffc00
  | _ => 0
def q1Neg : Nat → Bits
  | 0 => 0x0
  | 2 => 0x88842101241028104402448908a050421284a
  | 3 => 0x9106a489248895402aac809225212ab04c5314
  | 4 => 0xa21221aa4912804a53354900465560909683a0
  | 5 => 0x44a4c93301db29949dda72e5700643251bfc00
  | _ => 0
def q1Atlas : Atlas := ⟨5,rawDecor 61 q1Pos q1Neg, 0xfffafaaafafafaaafffafaaafafafaaafffafaaafafafaaafffafaaafafafaaafffafaaafafafaaafffafaaafafafaaafffafaaafafafaaafffafaaafafafaaa, q1N, q1R, (fun _ _ => 0), q1I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q3K4 : Nat → Nat
  | 0 => 0x150600030008060dc31be40bc40bf41dd30de31bd41bd42dd32df30df32bf42
  | _ => 0
def q3K3 : Nat → Nat
  | 0 => 0x280000135511025aa4205354b3096a968359500c71a84995354831
  | _ => 0
def q3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def q3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q3K5 (i*5) 5
  | 4 => packedAt q3K4 (i*16) 16
  | 3 => packedAt q3K3 (i*27) 27
  | _ => 0
def q3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt q3K4 (192+(h % 18)*4) 4) % 12)
  | 3 => 2*((h/9+packedAt q3K3 (189+(h % 9)*3) 3) % 7)
  | _ => 0
def q3Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 3 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def q3Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 3 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 4 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def q3Atlas : Atlas := ⟨5,rawDecor 59 q3Pos q3Neg, 0xeeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88, q3N, q3R, (fun _ _ => 0), q3I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q7K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q7K4 : Nat → Nat
  | 0 => 0x14800041000bd40df30bf40de31ec21ef20ee21be41dd30ed20f510f710bc41dc31
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x10001c431087488210e510431
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
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
  | 3 => 2*((h/8+packedAt q7K3 (81+(h % 8)*2) 2) % 3)
  | _ => 0
def q7Pos : Nat → Bits
  | 0 => 0xfc3ffff0ffffffff81f87e1ffe1fffffd11c7f
  | 1 => 0x3fc1f0ff07c3e1c0fe3f8fe30fe30c3c2eebaa
  | 2 => 0x3ffe00fff803fe00ffc00ffc0ffc0fc030f3cc
  | 3 => 0xc00000fffffc0000fffff0000ffff0003f03f0
  | 4 => 0xffffff0000000000fffffffff00000003ffc00
  | _ => 0
def q7Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x849461123285420b16188621262124b84669aa
  | 2 => 0x290caaa451aa9055aac44b544b544b88b0b2cc
  | 3 => 0xa3a94cc8a520d4a6cd6d51108d9ae1113b0370
  | 4 => 0x3231888ec6331938f1b66d9ae11082223ddc00
  | _ => 0
def q7Atlas : Atlas := ⟨5,rawDecor 31 q7Pos q7Neg, 0xeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaa, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x2f18df30b86578cae985c31
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0xc0008c424c2390a3194414c2590632
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/2+packedAt q8K3 (90+(h % 2)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q8K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q8Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 3 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 4 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q8Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffa0180202049440a5
  | 3 => 0x122324452122a652
  | 4 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 60 q8Pos q8Neg, 0xfff0f000f0f0f000fff0f000f0f0f000fff0f000f0f0f000fff0f000f0f0f000fff0f000f0f0f000fff0f000f0f0f000fff0f000f0f0f000fff0f000f0f0f000, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x18000036105c30e82178c37107610
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x20003808010d03004320c020
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
  | 4 => 2*((h/1+packedAt q9K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q9K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q9K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q9Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 30 q9Pos q9Neg, 0xccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x300000000000004000402f985d30de41dc436907510
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x480344c110e12044324c120
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
  | 4 => 2*((h/1+packedAt q10K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/30+packedAt q10K3 (90+(h % 30)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q10K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q10Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 2 => 0xbf333e3ba0da
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q10Neg : Nat → Bits
  | 0 => 0x0
  | 2 => 0x42444211044a
  | 3 => 0x241814820914
  | 4 => 0x1801a92012a0
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 29 q10Pos q10Neg, 0xfffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaa, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q11K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K4 : Nat → Nat
  | 0 => 0x20480a90006040c26fa65f0cbf087c30fc63fcc7f907f32fe43f087e18fc20fe61f883f887e21fa43f043f197d10fc61f4c3e98fd20
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x4000308100300100002000b7c00000000000000000000c000000500332750c20cd320cab10910b541ccad50632ad42cc6d90420af42442b90a319d43886bd0930ae420c3948421b5410c27d0d20b741482790c209d43042d90430d5310c67d0d109e43c86d90732b441482790e21ae42042b508309c43482750f21ac424c2dd0530ad42042d10530b541082d90632ad428c6790c10ae42cc6710d10
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q11K5 (i*4) 4
  | 4 => packedAt q11K4 (i*15) 15
  | 3 => packedAt q11K3 (i*26) 26
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q11K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt q11K4 (360+(h % 15)*5) 5) % 24)
  | 3 => 2*((h/41+packedAt q11K3 (1014+(h % 41)*6) 6) % 39)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 4 => 0xe6ff07cff81f8f1c
  | 5 => 0xf8fff80fffe00fe0
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 4 => 0x1942d41a90932b18
  | 5 => 0x78486ad24c24dc0
  | _ => 0
def q11Atlas : Atlas := ⟨5,rawDecor 51 q11Pos q11Neg, 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
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
  | 3 => 2*((h/1+packedAt q12K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q12Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 4 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q12Atlas : Atlas := ⟨3,rawDecor 51 q12Pos q12Neg, 0xeeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q13K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K4 : Nat → Nat
  | 0 => 0x14200880701800a9400fc63fcc7f197f30fa43f4cbf10fc21fc41f0c7f887f20fa41f043e987d10f861f0cbe98fe30f841fccbf087f21
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x4c00400000000000062000013440010000041400c00000000001c03800452add0530e521086b90830ae428c6790c10b641cca710d10d5310c6790f219d43c86d10520ae42cc6dd0520af42442b50830b641082790c20ac42442b50b31b5410c2d507329d43886750c209c43482750c10b6410c2d506329f43442b50810cd320ca790e21af424c2b109309f43482d10530b541082b50a31b6418cab90810
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q13K5 (i*4) 4
  | 4 => packedAt q13K4 (i*15) 15
  | 3 => packedAt q13K3 (i*26) 26
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q13K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt q13K4 (360+(h % 15)*5) 5) % 24)
  | 3 => 2*((h/41+packedAt q13K3 (1014+(h % 41)*6) 6) % 39)
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 5 => 0xf8fff80fffe00fe0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 5 => 0x78486ad24c24dc0
  | _ => 0
def q13Atlas : Atlas := ⟨5,rawDecor 43 q13Pos q13Neg, 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x8002c02f98dd31bc6170c2f995d32
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x9541cca350b3195410c2350830
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q14R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q14K4 (i*4) 4
  | 3 => packedAt q14K3 (i*15) 15
  | 2 => packedAt q14K2 (i*26) 26
  | _ => 0
def q14I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q14K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q14K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q14K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 43 q14Pos q14Neg, 0xeeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0xc000000200000002e18dd32bc6374c2f985f32
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x1808d42cc26500318d420c6650332
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
  | 3 => 2*((h/23+packedAt q15K3 (90+(h % 23)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q15K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf39cfc7e39f70f
  | 1 => 0xffffffffffffffffffffffeffdff3f8ffe39f3
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21829041288a305
  | 1 => 0x1020004084100052
  | 3 => 0x941501921250c28
  | 4 => 0x7891aae4985af80
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 27 q15Pos q15Neg, 0xeeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88eeccee88, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
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
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 2 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 2 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q16Atlas : Atlas := ⟨3,rawDecor 39 q16Pos q16Neg, 0xeaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x86000ae98dc30be657cc6e995e30
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x200009541cca350b3195410c2350830
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
  | 2 => 2*((h/15+packedAt q17K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 39 q17Pos q17Neg, 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x4001802e98dc30be6578c2f98dd32
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x300095410c25507328d42cc6350830
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
  | 2 => 2*((h/8+packedAt q18K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 23 q18Pos q18Neg, 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x108000004c32b865bccaf196c32
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x2390a32
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
  | 4 => 2*((h/1+packedAt q19K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/15+packedAt q19K3 (75+(h % 15)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q19K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 1 => 0xfffffffffffffffffffffffdff8ffffc7ffe3f
  | 2 => 0xebff0f3ff8e0fcc
  | 3 => 0xf3fff03fff00ff0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff4070220a092a0d5
  | 1 => 0x20864414425462a
  | 2 => 0x1512e8669086b4c
  | 3 => 0xe248eb92418db0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 15 q19Pos q19Neg, 0xe888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def q20K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q20R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q20K3 (i*4) 4
  | _ => 0
def q20I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q20K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 2 => 0xebfc1f3fe03f8f1c
  | 3 => 0xf3ffe03fffc00fe0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 2 => 0x1523506a42a52b18
  | 3 => 0xe0a1ab493064ec0
  | _ => 0
def q20Atlas : Atlas := ⟨3,rawDecor 15 q20Pos q20Neg, 0xeac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x30064493070000010d120020e109000812007f54c01ff43007fd0801fe10007f88401fc20007f8c001fd42007f10401ff20007f4c001fe42007f48401ff10007f94c01fc40007f0c401ff40007f08401ff21007f44001fc10007f54801fd31007f88001fe40007f94801ff41007f55001fd43007f94001fd20007f0c801fe43007f94401fe41007f54401fd50007f0c001fd41007f10c01fd32007f8c801fd40007f95001fc42007fcc001fe31007fcc801ff31
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x286213ff14e43007fc8708002bd64c8401de2188200ff58a50005fac329803fe21c4001ff29c4200ffcc520007f86328002fe63c4001fb28e2000ff50130005fac39802bff5390001bf282a000ff90710007f8c588002fe60cc401fe98020009fd9510027fea588002ff65504015eb246001ffd5010005fcc390003fc41cc4017eb0c6400bf18d10067fea190803fd63040016e31a8400ffc8310007dac5a0803fd61d001bfe3286200ef59010005f8c888013fc53c40017eb284200ff54441005fcc121803fd41cc001ff28a800fffd4141007da4010003bd5410401ff3206200bf59743007fac528802fe6195001feb166200bf58810007f86528003fc430c0017f31c8600ff0c621005facb200037e5154401ff9886200af19132005faca19002fe64c4001feb008200ff50b31007fca7a0003ff40c40017eb2c2000bf98c41005faca20802fd60904013eb2c8200bf58032007788320003bf6444001ff992200dff14431007fa43980027d6504001f790c4200ff54520007fe6508023ff54cc001f6a924000bf98420007f88288003ff4254001ff28e6000bf584200057cc819003fd20440013fb2a6000f794c31005fcc888003fd64cc4013fb2a8000bf18d50007fec788002fe640c001f7b122000ff48210005fec4a8003ff6148001fea0a6000ff1061008ff8a219003ff32c4001f69084200ff8ca10087fea720803fe418c001ff21e2000ff54140007dc4290803fe410c401fea886200bf18d51007fc6488003fe5390c25fe2848402ffd4d10007fcc818002bd64080017fb288000ef90f4008ffea019002bc6444001773146000fbd0b3206ffea418802bf644c801fe9902000df54550005facb10803fe4204001fea12a200fb48720007fac408003fc3144023ffa886400bf58643007fecb98003ec624401bfe2986200ff50910005fec4a880fff5384001fe18c2000afd9131017f8a488002fe630c401fe192a200ff59030007fac418803ff4394401fe2182000bf58341007fa8508003fe64cc4017eb008200bf99031007be6398002fe64cc0017eb2c640effd4331007fca788003fc6148007fe2942000bb5884002ff8a210003fe53480017eb2c6200bf98043005fecba0003fc3244001fe31e2000df59410005fcc918802fd6194801fe18e8000bf19221007fc62a0003fd50cc001ee18c6000ff94530005fac119002fe6094c01fe1942000ffd0a50005fcc7a0003df314c0017eb2e8200fd54510007fc6208003fd61cc001ff3242000af99020005fec40804bff50908017e3226200ef10d40005fecb10802fe6344021fe2848200bf99120005fec298002fe6190001ffa166200bfd9443005fac420802fc63508017fb2e6400ffd9151007fa4188002ff6055001fe2102000bf58343007ec208801ffc510c001ffa1aa000bfd8540
  | 1 => 0x2df6344001ff20ca000ff94520007fa86a8803fe6204001fe2142010ffd4641005fcc72a003fd6110c01ff2864000ff50d10007d86510803fe41cc401bea92a200bf59440007f8c018803ed6204001ff2888200ff98730057f8a720002ff60508017fb024210ff146410077887208037e5454401fea824000ff50e10007fc6528803ff3188401fe194a200bfd8a10007fc8588003fd32c4001ee98e6000ffd081006ffea818803fc6254001ff992a00effd4b31007fac928003ff620c401feb266004ff19710007dc4210003f710040016e31a2000ff9434005ffea210803bd4110401ff2886200ff1903105ff8a210803fd42944017f3186007ff15030005fec29903bfc53cc4017fb0aa000bf18143005fec099003fc43c40017e30aa800bf18152005fcc620003fd52cc0017fb2e2000ff546210077887a0002fc614c001feb1c2000f758c1004ff8a0a0003fe4394001ff2988600ff8c710005fcc110803ff300c001fea12a000f7cc431005fec48801bfc51c8001ff98e8000ef99010005feca90803fe54cc0017eb006200ff50010005fec0a9803fe32540017eb2e4200ff10550007faa210803fe64940017eb0c8400bf59442007f88588003ed5288401f6a904200bf58743007faa72081bff51c80017f3086400ff08510007fe4088003fd54c4001df2a28000ff88510007faa320802ff654c401deaa68000fb88120007f862a8003f65144001fe10c2000bf99221007de6490003fd51c8001ff10c2000bf58242007daa590002ff6588005ffa922000ef5004000ff8a808002fd60c8401ff20a2000ffd0b30005fac510803fd43c401bffa886200ff58e5001ffea50800ffc5384001ff20c2010ff14e41047f8a198003fe43cc401dfa048000ffc8210005dec4a180bfc53440017f3048400ffcca50005fcc129003ff3004001ff31ca000ff0c950005f8c6080037e5194001fea066009ffd4140005f8c910002fc640c401ff30e8000bf18132005dac518003fe6494401ef1886000bf58043005f8c710802bd6404001fea8e8000ff10330007fcc508002fe6094427fe28c8600ff10c31007fac808003dd530c40fffaa06000bf19030007fa62a0003ff40440017f304a800bf19331005fcc3a1803fe6110c27ffa8c86009f59720005fac219003fd6494401ffa14a200ffd0210007fca090002fe600c8015f3264200bfd9730007f88528803fd53c4001ff992a200fb50920007fc64a8803fc31900017eb066200ffd0c10005dac5a08027d658c4017fb028200bf18142047f8a998003ec3248001fea14a000ff90d51027f8a388003fc41940017eb044200ffd9110007faa818803fe5390401f72944200bfd9441005facb21803fe32940017e3024200ff90d10047fea198002fd6110001ffb22a000ff08710005facb21002fc638801bff3
  | 2 => 0x20007f8c488002ec62440017f3088600bf58654005fec098803ff6254001f73108000ff54530007fa652804fff5090c01ff2884200ff88550007fc8298003fe4294001ff2a06200bf18d54006fca6a8803fd3044001ffb262000bf59510007fca320802fd6094c01fea106000ff10e5001ffea908003ff3204005ffaa22000bfd8542005fec0a1803fd548c401fe98420009f59421027f8a988007ff53040017eb04a200ff58b30004faca19002fe618c8017f3242000ffcc310005fcc021003fe51c8001fe9002000ff98e51005facb20803fe6294001fea864000bf59410007f862a0002fe61880017eb166200ff98a51005fcc608002fe61cc001ffa1e2000bf58910007fac110803fc41040017e322a400ff50e50007fca588002fd6210c015eb206400ffd8d51007fe8418803fe3194001ff1902000ff94f30005facb10002fd650c4017e31c2000ff19150007fc63200037d52940017f304620dff1403104ffea6a0003fd640c4017e322a600ff08550007f8879884bff5190801fe1882000ffcc220007fa811804bfc5190823fe2806400ffd9710005fcc710802fe64cc4017e30a8600ff98043007fa8408002ff62c4001ff21ca200ff0c440007f22008002fd658c001feb242000fb88620005fac318037fc540c409ffaa62000bfd9540005feca98007fc5204001dfa108200ef50740007fa8598002fc64cc8017f3202000ff90550007f42008003ff3048001ffa106000f7cc030005fcc1a1802fe608c001fe1902000bf59443007d843100037f6544001fe992a200ff19110007f8c688003fe42544017eb142000bfd9610005fcc720803fc41cc001f79944200ff58e51007fa6488003ff640c40176b102000ff4c310007fc8488002fd60950017fb286000ff10d51006fca928003fe63040017f3088400bf99253007fa6508003de538c4017fb2e8200ff90a10005fcc708003ef208801bffa806200bf98652005fcc119003fd50d00017e302a800ef10440007f86398003f51004001fe21a2000bf19310007fcc710002ff60544017e30aa000ff94710005f8c8a8802fc6054c017f324a200ffd8d50007f88708002fd6010815fe28c8000bf98643007fec4a8803ed42884017eb04a400bf98440007faa318802fe60d0401fea006000ffd0730007f8c690803fe43540017f3042000ff88650007fc6288002ff65cc401fe31aa400bf19010005f8c6a9002ff65480017fb282000ff18d51007fc8318802dd63040017eb168000bf59420007f884a8803bf41500017eb0ca000ff58031007f84328003ff32944015f3202000bf59430007ba6018003fe31840017eb14a200ff50431007fcc80803fff53504017fb0aa400ff0c521007faa188002fe60900017e30aa400bf18d20007f88488002fe61908017eb2a4200bf98e2000778c88800
  | 3 => 0xeb2a4000bb189430077e83a001ffc530c001ff2986204ff14b10005fcc820002fe618c0017eb0c4000ef50b40007fca6a1003ed6210001ffb286200bf992200077c8620802fe6348001fd8842000df19510007de4290003ff42544015e3226200ff58a10007fca198003fe60104017eb046201ff14410005fcc928003fc32c40017f30ca600df99410007fec018803ff400c001ff2066009ffd4540005fac221803fe6384001fe214a009ff1454005ff8a010803fd418c401ffb0e6000fd54710007f88218803fd32944017f3224200ff90a51005fac218002fc6154c01fea1ca200ff0c520007fe8488003fe2104001f690a4000ff08410007b86218003ff42840017f3004200ff10e51005fecba101bfc50c80017e3226400bf99230007fe6398002fe610c0017f3048200bf98d21005fac010807ff5204001feb008600bf58740007fc8208003f71084001ffa1ca000ff54d40005fecaa1803fe64cc001ff9002000ff5454004ff8a6a0002fd6294c01feaa26000ffd8b10007fe8218803ff64cc011ff32e6000ff90c30005bcc608003ee6204001fea022000bf18540005fac598002df6350803fe2982000f794f30007fa8418803be5490401fe322a200bf18520005fcc018803fd40840017eb14a800bf18d40005f8c0a8823fc51cc001bf29ca000ff94631005fcc208003ff4004001ff2826000bf18d21005f8c898002ee6210001fe992a000bfd9532007fc84a8023ff51cc0017e322420bffd4021007faa588003df6344001763126200ff90130005fcc728002fd65c40017eb162000ffcc110005feca18803fe21cc005fe2a22000bf18f10005fec0a9003df318c4017e3224000ef9534009ff8a121802fe6008001fe2086000ff95310005feca88003fd51cc001fe21aa010ffd424101ff8a90803bff54cc411ffa966000bfd8543017fea08801bff50c80015fb222000ff597300077a8420803fe41cc001feb106000bf59720007fc8298803fe4304001dfa088208ff14f30007faca18803fe6088401fe3262000ffd0b10007f8c998002fd62940017eb144000ffcc210005fcc020802ff61550017eb0c8000f718d10005fac418003fc4254001ff18aa000bf582430077c8220003ee62d040177b122000ff94740007f86090002fe6190401ff29a8000fb90920007f8c6a8003ff4354401dfa168000bf18131007bca698002fc614c8017f3208200bb98b41007fca7a1003ff62cc001ffa066000ffd8910007f8c398003de63040017eb2e8000ffd0d10007be6118002fd62d0401ff28c4200bf588400077ca820803fc6254401fea062000ffd0e10005fac221003fc310c01ffe29a8200efd0040007fec688002be648c009ffa862000bf98631005facb98803fc6348001ee9886200bf18542007fc8798003fd520c401fea1aa000bf587
  | 4 => 0x3a0087c198001400a1e8080000a010300001a1d09c01000070120a030028000002c0b80c030001d0160d06e00800148524a0000202a0006001828210002d9380e81a0301a0000004106898048c86e0000e0000c16000030020b00c0480e0080e138049d000008000080e2e0141e80a080280b8b61f870018020680032000008141900604a0e0f0003f8060880001038640000200801802018160a0000001200800010ac0081c0a806238060000e308681c81e0280e04000008123f8000080201000070165781e0700409800070160100a008002000206800008020004c0800e0200c028080280a0e8060000000688108027e0000501a410000680c000060180a2400000800028025600c030161d800220020b02444830bc6660500a0000004000038003f06a220160480c010001300e0808c000000c00200800000020081c000000004c0380400072000160001e010000002a0100116804080157801209004000020182c010280100a0000c06004168020b0240e0241781bb78180401810000008023c8240381600000080240189a000060d0c60400800034000000002473800038000001a010001a8020102e0000e0006803000d78000a8000301c0000403000000680380003000d68121c0180c834000080382a0a812020140a02400bf98421007fa8608003fe210c001ff2186200ff10f30005fec2a9802fe63d04017e322a000bf98e40007f88388003fd54cc001f72144200ff94140007baa798003fe5310401ff31c4200bbd8931005f8c0a0803fe32c4011fe32e6000bf98740005facb98002fd61840017e3266000efd0641005fec290003fd504c0017f30ca000bf19210005dcc408003ee5248001fe18e2000bfd9542007fcc018803fc318801dfe2a66204ffd4f10005fcc008002fc63504017f31ca200ff50b10007fc8218002fe60c84017eb106207ffd4830007f62088003ff31500017
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xe7448310005bc7350b400257e750cb10005fd74d8d50007be4394740006bd7119132007f65188710025fe758cb10006fc5198e40007ef3288510006fc4398031005fc764cb10007bd644c810005fe7310d10007be640c810005fe7110a100067f65d01100077e4394551006fe6518730005fd72905310aefe6258a10006fd73d8142006fd75d8143005fe71d0910005fd7090c100a5fe728c810005f471501100077e5490d51006df7518d42005df7350a50005fe718c810006ff63d85200a7de324c810004fe76d0d50007ef73d8910004fe768c510005fe74c8110006fc4398410005de7394530007bf4350950005fe760cb1009eff6590d510267f52597100367c65c8110005fe7694b100beff6218b100977c5490a50006fe4158231007f930482100067f6508510006fd4158043005fd7498810007df430ca100d7ec3254320006fe3158031006cc63d8910006ff7650a10007be4394641007dc6390d50005fd7319310006fd4218151005fc7690d51006fe6459210006fc4398650007df438cb10006dc63d0910007bd72d9110004fc7650730007dc6310d10006fd4358430004ff760c640007de6390810006fd7558041006bf64cc110015fe7510d10007be6450a500977c5190a50005fd700c621007ef3254421006fe7198c10005fd7298c10005fe7488510007bd64cc810005fd7094e41007bd43d0a51007bc4310410006fc74580310057f754c3100057f755822106f7c50d9431006fd6358a10007ee7318910007f64110610005fd76d0a500067d6510c100c7be740c9100067565c4010004fe73d9620005fd700cb10006fd71580420eefe6254431005ff7650810004fe7318c10006fc3259731004be74d9410006fe5158031006dd7018d42006fe6394421006fe4258650006dc6310910006ff65d0810007ed628c810006ff76480100475f5194f30005ff744ca510077f6590910006f661884300067d6590410005fd73d02100066f6518910006fe70987430a7df328c810007f970d8b10025fe754cb10005dc7354130007f6418c710005fd7090730007ef3208410025fe7508710006fd628c6400c6fe760c910006bf6418d10005de73905300afee42c82100bdfe7210f100a7ee628c8100a5fe720c410006fd3298251006fe7598730007f63158031006fd6510d10006ff6510810006fc5198720006fd65d0b10006fe42583310067e7518520005fd73d0a10005fd740855000e7c5418151006f461cc540006fe7558021005df7350b10007f63254510007f46494710015fc75d0d10007ef420ca51006fd6510b1001dfe7590e10004fc7358b41006fd7598e41007bd4254641006fd74d8132005f4714c9510067f6590510006ff4298331084ff7654441005fa7010f30006fd65d0e100047d7599110007df4350c1000d7e75c8010
  | 1 => 0x8221005fc7650d50005ff704ca50005ff76cc810006ff7358221006bd76106400167c5458650006ff5198432006de638c4100067e6598c100eefe62547400adfe7210e10006fc2158041006fd6494431006fc7558021005fe71cc120007be4350c10006fd7298730006bc64cc110005ec7250c10007ef420c9510bff97018b100077c4354550006fc43d8151025fc7550b10007bc4394540006ff51582430a5fe72d0010004fe7118d54005ec7250d51006fd4358251007bf6450d50006fd65d0a10006ad6488420006fc638c510005bc744c951006fe5498f10005fd74cc110004fe7318152006ed6358810005be740ca51006de6388410005fd7010f31005dc7350b31006fc6318b10004fe73d9710006ff7158042006fc6318910006fe6308650005fe7194d40007ef420c8100efec420c951007f74294510004ee76c8520005fe76945400057d758c710005fd700ca10006de5358231007de4310c100077e4354951005fd70d0b31006fe31d81520e6fc6294130007f943c4110007de6350810006fc3258654007bf42500100977f5090951006fd42583310477c5454730006fd6458e51005fe760c950006fc7398740005fd72d97100a7ec420c810005fd74c82100067d65d0010006fc61cc120007f44294510006bc6418d10005fd7310410005fd7010c30004fd76c8010006fd624c540007bc72990100aefe7610a10006fd76cc210006fd40582210467c6559730004fe7695310005fe7319310007bf6490f10004fe760c5200c7bf4210910007bf4254540006fe76885100a5ff76108100067e6559010004fe73d95410aff97010a10005fc7154120005fe719081008e7c650c910007f44108610006fc5258031007f63188710005fe7690b10006fd6258031005fc7454b10006fc2058043006fd4258650005fc7355310007bd42d0010005fe710c810007bc6450951006fe6394641005bd740ca10007ec3248210007fb4050110005fd74d8d100077f6550910005ff725053009f7f5190e51006be7119132006fc3298430006fe31d8142007f6518c7100067d6508410005fe73d0b10015fe759091006e7c650c540007ec62cc910005fd70d0830006ff7558032006fc7650b10005dc73508300adfc7258e10004fc7359610005fd748c550007bc43905500077e53d0a50006fd5258031005de73d03300867e6590631005fc7150910006fe42987300477f5298e5003efd7018d50007bd4250210007be7299010006ed620c4100adff740ca10005fd7290f10007bc744ca10006fe6354f100adfc725921004f7f5259250005fd7290e10007ed42c8210006fc6259431015fe754811000d7e7590410005fe718c951004ff70588310a5fe7299010005fd7090d510edfe728c951005be73d06410077e5310a50005fe7110d50006fe4158041005f
  | 2 => 0xc5fe72d8d10006bf644c110005df7350a100067f6294150006fc5058032006ff5098432005ad72d0641007f97090710006ff7318542006ff7018543006ed620c81000dfc75cc8100bfec32c8310005fe71d08310077e650c810007f443c4010006fd6458831005ff7050830006fc7598720005fd7610330006fe63106100c5fc7250d10004ff7058a51005fd760ca10006dc6350d50006fe43d8121005fe7110e50007bf4350b100067d65cc8100067f654c910005fd748c650005fd7318b10004fd768c65000e7c5459410006ff6550c10005fe73d8910005fc7654f1000e7f5359410006fe7098e41007ef324c810006fc6498031006ff65509100e5fc7259250007bc4390650006be6350040006fd6458b31005ed72d0730007df654c730006fc63d0310005fd7308710005f6710c910004fe7398241005ff7488410005fe73d0a10006fd6550f10006fe6110730005ff7350910005dc73503300e5fe7299250006dc5298c10007f47150110005fd7008550006fe6394621006bc5059032005fe71cca51007ed74189100157c754c110006fe6558031007f67118f10006fe6259431007f53284110005fd7090530006ff5058243006ff5398640006fd65cc910006fd6510f300e7ec3294320005ff7054e41005fe7448210004fd7610430006fc6308710006fc5218d10005fd7390b10004fc7358654006dc6394f100ffdc54cc7300a5fe7290c10006fd71d81320077c7550110005ff7059431005fe740cb1009f7c5490d510a5fe720c810005fc74885100bdfc724c310005fd70d0910006ff3298031006ed62c8010005fe73d0a500967e65908100bdfe72d9710006ff6590910005bc7454140005fd74087100057d7590530005fc744c11001d7e750ca10006fe6354720006fd65908100077c65d0d1007e7c6550530005ff7050c10006ff6458031005dc7350910006fc5118d40006fe4258730007ee7498810007bd42944410067f7558221005ff704cb10007f77150810004fc7359521006fe7318520006fd42587300065f6518d10006fd6510a10015fe7550d100167c54d95100167f53d95100273f5495310007be648c810004fd76d0e50005fe73109500c5fc760c910006fe7690531005fe73c8010006fc43980100a5fc740c810006df7118d42004fe760c510007f643c4210007f7328411009f7c5090d50007df7458c10006df63d89100c7ee4208510005fe7494b10006ff5198642005fe7310510005fd7010d1000dfe7510410007ec42cc950005ff7458e50005fe768c951005fe7394340006fd628c410005bc744c810006dc634c110005fe7690d50006fd4298730006fc6310951006ff7158343005ff7610e10007de530c740005ad72d0740004fd7098e51007df438ca10005fe7348310005fd7408650005fe76cc950006fe535
  | 3 => 0xe7119130006fc4398331006fe6194720006fd65d8b30005df7654f30005fc7359250005fd70cc951006fd3298650004fe7118d20005f9700c710007ed7318910005fe740ca10007df74d8d10006dd76cc230007ee73988100047d7518520006fd655083000d7c7550010007df6390d50006fe3298430004ef72584300ef7f5290951006ff3298650005fd7408610006ed5298720007df74cc2300047d7598730006fd3018520007ec42ccb100c6fe32586200077e758c41009f7c5390e50006fe7118d20006fc32594400d5fc760c950005fd70cc810005ee760c920005ff7050d51007f64294710005fe7308510006fc3259430005fd7395310005f47150a51007ee4358810006fe5298c41005fc740c710005ff764ca50007f471508100bdfe72d8f10005fd7390a10006fc32594310077d7590d51005f47150d51004de73d9441005fe74d8d10005fd70887300a5ff73c8010005fd7095031005fe7110f10006fd3298410007ec42cca50007f942c4210005fd76d0c1006f7c540c650007ee4398810007fa4244010006fe6498730005ff704ca10005ff724c0100bf7c5254b10006fe72580410bfbf4290b10006fd6458a10005fc7650d51005fe7348210007fb4384010007f431086100a5fc7590810005fc76d0d100067f65cc910006fe52987300c7f5710c910005fe76d0b1005e7c5018552006ff764c010007dc634c910005f47150c10007dc438c951006dd6498c10007df750c6300edfc760c951005fe710c9510377c5398a50005de7310730005fe7418d10006fd64588100047f7558041005ff7050b310a6fe3218121007ed74d89100d5fe7290550005fd70d88310adfc724c210026ff5398410007dd74cc23001dfc7550a10006de6350e51005fd74cc950006ff65d0e10007be4390510007f930587300067d654c8100aefd76c8210004fe71d8132007bc4390710005ff74cc110006fc6354520007ef7250c10006fc3258254006fc5298f10005fc7348010006fd6550810006fd7518530004fd7098632005fd748c710006ff3298410007f93098730025fe7518b10007f64354510025fc7518f10006ad6210440006fe4258031007f4435471000dfe75d0810005fe7190951026fc5498410007ed42085100477c6594330006fd7458231007ef6290951007fa42c4210004fd7690650007bd64d0e51007f57110d10006af64d8910005ff7654730004ff7650830007bf6410d10005fc7150831005fd708c9500bff97008710007f64344010007ec624c910007ef620c910005fe7190d50007f97010710005ff7350010006dd7418d10006fd654c910006ff5098642006ff6590f100e7ee620ca500c7fb2048110004fe71d8143005fd70905500cffb50cc310005fe7650910006fd6358221006be640c410007dc63cc9100dfec3294421
  | 4 => 0x731005ff7454130005fd74cca50006fe63c8210006ff75d8142006fd65d0b31004fe760c91006cff765463105cff7654621007df6390910006fc3218550007fa3098730007de630c810005de7394730006f97018f10006ff20987300057d75907100077f7558041006ff3259730004fc7158343004fc7654530005fe7190e50007dd7298c10006ff65d0a10005fe7110e10004fe71191320bdfc7254f10007f54294710007bd4350950006fd7318542005fc7655310006fc3258440006fc2198e54006ff7158043006be640c810005fe73905100bfbd4210b10006fe4359621006fc42d9731006ef628c510007f94244010006fc50582420467e65d97300bfee320cb10006fd32d81510063f65d9110006fc3258650007ef324811006f5c5094c31006ff764c810006fe6358221005bd74d87300a5fc7258c1000dfc75d0c10005ed760ca21005f4714c1100077f650c910005fd748c610004be7498331006fe610c730006ff5318f10004fc7654b10006fd6458e100057e7395250006fe6394740005fd70d0831007bd4210430005fe74ccb10007bc4390610006ff3298010005fd7388510006fc43d8550005fc7154320005fe7310b10006be6490630004fe7690530006fc6310a10006ee76189100377c5494320007df4390f100067f7259410006ff6510a1000dfc7590c10005fd708cb100077e5490a50006fc3258331006fe71580210077e4294650006de6390810006fc4259731005fc714c950007ef628c910007be43d0110025fc75d0b10006ff32d8151006fc2158253007dd53507300bdfc750cb10006bc64501300067d7598730005dc7350831007bc6410d10006fe7098632007bc43d0310007bf43d0810005fe7498810007f47148310006ac64d8910006fc61541200afec32c82100c5fc74c8110006be64c80100077f4394150005fa700c7300c5fc7690910006fd6550e100c7be4250910007dd6390810004ff7650810025fc7519310006df6390510004fe7318141005fe71d0d50006bf5359010007dd530c640007bd43d09100bdfc7510b10006ed628c8100077f3254550005fd7394b100d6fe6254330005fd7390710006fd4258031005fe7310a50007bf4350a10006fc6418950005ff7255231005fe764cb100077e658c810005fc7350950006bc5159010005ff7258e10005fd7308610006be5458241005ff70509100077c65d0910005fd708ca500c5fe72d9110004ff7650b31006e461485200a77d750c810007f54394510006bc5159020006dc6350d10006fc5118f100d5fc7690950005fd7010c31006df7018d100ef7e7590951006fc5418f10004fd76cc740006fe6398810005ff744c91000dfe75cc810007be5490730005fd700c520006ff64945300077c6510910007ee4294621007ef42ccb10006ff628c540004f
  | 5 => 0x77f658c910015fe7510910005fc7650d10005fd744cb10006de6310410007bf644c910007fb4050010005fd7348110005fe7398810007de54cc730006fc325804308f7f500c951006fc759843200dfe7590810007bd6450a50007dd7458c10005fc714ca50006bc43185400077f4294150004fd76d0e51006fc6310550005be740c5400afbd4210a100adfc750ca10007dd4310d10007df7298c10006fe3258331004fe768c951006ff7650f10005fe7410d10007bf4350a50005fd700ca50005fd73d9310025fe75d9310007f532c4010006fc3158031005fc7150810006fe5318540006bd76d02400077c7550010005fc7388510006ff64d8d50007bd4210510007df635091009dfe7310d51005fe73909500adfc7510a10006ff43d85500077f4394551006ff2058043007f63198031007bc43d0210007bd4290531006ff759844208f7c510ca50007ec73d89100d77e65543200bdfe7290710006fd628c650007be6490c10005fe71d095104f7c5394140006bd6419330006be5498740005ff7259010006fe4218550006fd4218550007ef3288410006bd4298740005fe7310c10006dc5318d10007bd42547400077d6590810006fc3258730007dd7258c100067c65d9110006f6610c430004de73d9740004ff764ca10005fd74ccb10005fc740c610007bf64cc910006ff5018540007bd6410e10006de6350810007be4354140004fc7358840007be5350740005fe71d0810006ff7558041005fe744c310007f73254710007ec42cca10005fd7390610004fe73d8540007dd750c430007df4390e10007ef42cca10005fd740c510006ed73d8910006fd5458231006de6348010006fc329873001d7c7558e100afbf4290a10007bc7219110004fe76cc540005dc7350130005fc7358a500c77e7508510005fd7690e51007dd530c540005fe7190f10005fd7090a510077d4294650006f4610c54004f7f5254d40006fe7558031007fb4284010006fe321815109f7e7590e50007f732c4010005ff7254f10007bc435011006e7e650c410007dd6350810007ef32947200efbe740c951006fe7598e41005be74d8730007bd6410a5100dfe7510c10004ed72d9440007f65110710005be740c9100e5fe7290650007bf4210710005fe76d0d51005fe74c80100077d3254550007dd7218d100ef7d750c951025fc75107100477f5195330006fd329801001e7f52d9610007f84284010006fe760c5500a7be740c810007de5398730006ff2098c41006fc4158031005fc7690d10006fd53987300767f5259731006fe625873008f7c540ca50005fe74884100e6fe760ca50004fd76d04310377c5498a50006fc6318950005fd7498a100c5fc768c910006f46108550006fd76106100e77d5290a50007bd5490530005fe74cc310005ef7250d50007bd421
  | 6 => 0xc6258031007dd54cc530005dc7350810005fc744c010007bd64908100efee4254421006ff32d8550007ef73588100067f658851004dfc76541400077e75d8f100077d75904100077c6550d10006fe6258031006ff74580310067d658c410005fe744c21000dfe7550c10006fc6418f10006fc72987400bdfc73c8310006fe5158231006fd3298331007df72d8d10006fe7118d40005fe71d0f10007bf6410d51007f67110d10006fd6398221005f97008410007f6310c710005ef7250e50025fc75d0310007bd4350a500adfe7298e100a7ee42084100077e5390951006fd6599330006fe3298730005fe7610d1008e7e650c810005ff7054831006fe43984300d5ff7408550007bd548c540007bd5490630004fc7158243005fd7010c10005fe7190e10005fe7194f42006fe3218550004fc7158a54004fc7158b30007ef62ccb10007dc7350130005fc7350b10006fc6354f10006dc63d8910007bc64cc910006fd644c010004fe7199030006fe4398221006fe6354441006fd7598e21027745354710006fd650c8100defe62946310adff7610a10007bf4210610007bf42946410067d6588410006fe52580310a6fc32181210df7e6594421006fd6454730005ff73508100077c42941500077d6550810007ec74d8910005fd7088550006fc43584300bdfe72cc310005fd768c810004fe7318151005fd74d89510c7ec32085100063f6519110005fe74cc210005fe7310410006fc4298653006fe634c0100e6fc6394320006fd4318520005fb70547300e5fe7298e50006fe4298251006de7218d1006f7f5254431006fd7558043007dd5358031005fd74cc0100077e5450a50006fe6310810005fe73944410077f4354951007f6510c710006ff32983310067f6590530006fc2098443005fd7290530006fd648c650005fc714cb10005fe71d9330007f671d0110006be4358041005fe73191100bdfc748cb1004f7c6554540007de638c810006fd7098e510067f658c5100aefc32d8520004fd70986430367e65c8010005ad740ca210afee320ca10006ed70d8910006fe71580320477f5154b30005fe768c95006f7f50594310e6fe62943300067e7598443007f53254710006fd7558031004fd7098642007dd654c730007ec7250d10005fc7610d10005fc76d0b10004ff760c440006fd7098720006fc6394540005fc7350a5001dfc75d0a10005fd72d0d100057970952500067f65189100077f754c310005fe71cc9100467c5359730005fe7388510005ff7050831006fc6310510006ff650c910006ff5298430005fe7418f10025fe75c8310006ad6448020006ed620ca50005fe74cca10004ed7219331005fe744cb10005fd708ca100a7bf4210810005fe71d0e50006fe325865009e7c6590d10006fd3058221005fe7310a10006fd760c740
  | 7 => 0xa10007f743440100bf7e75c8310015fc75cc110004ed7298331007bd6450810005fe73d0110006fd658c810006fc3258031004fd7098443006fc4358251007f83244010004fd7018d520077c42945510adfc748ca10006ff5098730005fe71d0e10005fd72d0110005fe76d0d50007f843c4110006ee4358810005ed7218031005f671d0310005ff7654e41004fe7198e500eefe62544410befc5298410007be4350310004fc7359520005fe71d0b31007ed42084100c7ec6290910006fe6498a50005fd7094641005fd720c710007ee43d891004e7c65501100077e6590c10007bf4294d400c6fd760c910007bd4210431005fc714ca10007f94384010005f97090410006ae6458810006fd7690410005ff7454310007be5350b40005ff740c6500a7fb2048010005f671cc110005fd7610e10007bd6450e51005fe741091009e7c5098e54004ed76988100edfc7250d510ef7f5254720006df7658c10007ef32c81100a5fc7250c10106fc3218152005fd73c8310004fd7610a51004ff7650e51005fc7150330007ee4294520006ae6498810006ff54984300c5fe7290910004fe76cc520005ff7458e51006fd7518d40006fe6394b10005fd72107100077f4294551005fc7150b31006fd6358810025fc7550f10004fd76d0c10007df735091000e7c5259410004fd7099331005fd70d0951007ee428851005f7c5354421006ff658c910007dc430c950025fe7588710006fd32d8550006bc6490531007f743c4210005bf744c950006fc32594430e77e6594320006fc72984430877f52906500d5fe7210950005ef7250f10004fe73d8a1011efc32d8552006ff72580310977c5090a510257e75087100aefe32d8520006ff628c710004fe76945300867c5359641006fd32980310077f654c54006f7e750c550007be4394140005fd744ca10006f661cc730006fe5418f10006fd62980310457e75d9330005fd7010d51025fc75887100067e7598740005fe768c910004fc7650910006ff7558043005dc73509510067c73596410877c535464104f7b5094140006fc4258653007f832c4210007bd4350b1000d7c754c010006fc3298043006ff7318520006dd6458c10006fc7650e10006fd6494621006fe51580410767f5459731006fd7558032005fd74cca10007dd53d8730007bc644c910004ef7258643006ff6498031006ed7688420005ff74cc010006bd7019110005ff7690e510057d75d8f10006ff6550e10025fe7590710005ff7250110006fd42982510ddfe7299251005ff744c110005fd7319110006ff2058031005fc74884100adfe7290610006ff7498730007df644c431005fd7194f42006de630c410004fe73987400057d7295151005fd70d08100167c52d9510007ef620c951005ff740c550004fc7158232005fd7250130006f
  | 8 => 0x6bf64d8910006fc7558031005fc7150d50006ff6510c10006ff628c5500a7be4250810106fe32181520bdff7408710007be4390a510a5fc74c80100477e6554330007bf4290430005ff76cca10006f76198730085fd769464101dfc7550e100adfe72cc210005fd7250230007f742c4210006ff3258430006fe61584430067f65909100067d6598c10005ff7348310007bd4154d40005fe71d97300dfbd740ca51005bf744cb10006fc5218f10007ec6250910007dd630c810007dc438c9500057f7550330006fd4318121004ff7650a100077d7598730006fd6510f10007ed320c910006fe43181510bf7d7518b10006fe4298031005ff7050810006fe6310910004be74d881011efe32d8552006fd4358620007f442c4210004fc7158032006fd6590c3000dfc7590410006fc62597300067f7359410007bd7359010006ff20986540077c3294650005ef7250e10007bd43d0810007ef4358810006fc2198740004fe76d0d51006fd6590c31005fc7448110005ff7358810006ff64d8d10007f64284110004ff7648010005fa70cc730007be6490e500edfe72d9151005fe7394720006fd4358221005fe744ca10005ff744c951007be6490a510e5ff7408650007be435464110efc32d8152006ff2098c40005fc7350a10007fa32c4210005ff7290531007ef4398810004fe7198d20005fd7090910007ed428851001d7e7508610006fe63982210477c5394330006bd648c4100a5fc7508410005fd728c510005fc7610f100edfe7290d51004fd70d8951007f74354510007bd4350a100d6fc635432005f7c5418951005ff744c810007bc6410f10007bc43909510bdff748cb10006fe6354421006fc50986430067e7598730007bf4310d10006de63c8010005bf744ca500067d6559010007ec3294621007f77150e10006fc71d8132006fc63d8520007be7399010007f7649471000dfe758c410006ef620cb100adfc73c8210005fc71509510077e75d9310005fe740c510005fe73990100e77f52086500077d43941500ef7d5210951005fe7498c100c7f671c8110006fc32181510067d65906310df7e750ca51006fc5358241006ff7598443005fe7498a10007f6310c610006fe3258730005fc74cc110006fc63c8110005fd7290630006fc6394710005fe7308410004ed72993100ef7f520c951007bf64d0b10006bc5159032004fe7608550006fc638c710005ff740c710004bc7459520005fc73543200877e6594641007dd6454c310057d7294551006ff7650c10005fd7398a10006fd7158043006bc53d9110005fd70d0d50006fe6598031007f43294710006fc71d8143007bd7110e410057c7454a50006fd76d0010007be43904100877e6554e41004fc73588410057d7598730005ff7358a10005fd768ca10006ff65d0f10007be645
  | 9 => 0xc6310d10005fd7418d10007bc4350010004fe73d8810005be740c810006dc6308510005ff7259210005fd76cc810007dd638c810006fe5298f40005fc73590100d5fe72105500067c6518d10006ff64191100067f6550910005fd70d0e500077d650c810007ed62cca10007dc430cb10005fc744c91010efe32d8152004fd7018e21007ef74d891009f7c5490e50004fe76945200077e7590631006fc764cb10007f74244010025fe750c710006ff65d0b10006f5610c730006ef620c5100adff748ca10005fd70944210066e6558810006fd6590910005fd744831001d7c75592100befe4298410006f6610c730005fd76d0e10006ef7648020005fe73d9310006df7298c10006ff64d8950004be76d05400d5fc73085500067f65481100077e548ca50006fd4298031005f67110f100257e7518b10005ff7254631007de6390c10006fe6354641006fe4318550004fc7650b1006f7c509503109f7c5190e50007f44244010007df6394f10007ee73d8910006fe4298650006ff6510b10007f54284110005fc7359251006ff7598740006de630c810005fe7318b10007dc63909100077f6590d100066e6598810005ff740c610004be74190100077e5450d51006ff7018542006fe43586500077c7558031005ff70509510ddfc7250e5106f7c5318d51006cc6318910006fd7518532005ff7050a51006fd76906300ddfc7259251006fc6150130006fe6259730005fd70cca5107e7e6550631006ed6250010007ee7418910006fd3258430006fe7610510005fe7390410006dc7518d10007bf4250330005fd73c8210005fc73501100069f64d8d100defc6294540007ef328c910015fe750c910006ff5258331005fd72cc110007f632947100e6ff65909500067d6590810007bc6490d510e77d520ca500af7e75c8210006fc5158032007ed42544210077e540ca500befc3298620005fe7390a51007bf42907310befe3298620007dc430ca50007df630c910007bf744c910006fe7358221005ef7254320007be43547400077c754c110005df7654c31005fe76d0f10006fe4358331007fa3244010005fd7388410005fd7094e21006ff6454120004fd7019221006ef3218520005fc7155330006fd7690631006fc7598730007be4350210007ef3248010005fd720c610005fd7310b10007ed7458810007bd42d0330025fe75d0310005fd7498c10006fd628c610006fc3298654007be43d0010005fd7290710005ff7354b100457e7590730004fe73d9621007dd72d8d100ddfe72d0e51004fd768c6400c5fc75c8110015fe7550910006dd7298c10006fe3258031005f97010910005fd744c310006dc6390510006ff6454730004ff7650831005fd7210f10005ff748c510006ee6388620004fc7358910006fd6454f10006ff2198443006fd75d8142
  | 10 => 0x4b100067c7558043005fd7010a50005be7395140006fe4359620006fd6498730005fd7498e50006fd3258251005fe71cc95100dfc758c410007bd740c740005fd7650810004fd7610a50005fc7150f10005fc7158b30005fe7410c10005fc7154d40005fc735474000dfc750c4100befd7610b10006ff6590d10006ef7358810005f970107100457e7598730006ff5458331007ec7250c10004fe73d9510006fe7098432005fd7294530007bf4390f10005fe7695310006ff74d81320a5fc72590100067d6510410006ff628c510005fd7348010005fe71cc810006fe42d81510157e758c510006dd5398730005fe7388410007f932c4110006fe43d8520006ef620c9510c5fe7219110005fc7690f1006f7c5054831006fd4298410005fe7399210005fd744c210005fd74885100dfee4294720007dc438ca5000dfe7510810006fd7458221007be54cc5400adff7408610007f6418c510004fe768c540007dd4310c10005fd7310a10004fd7688430007bd4254d40005fe7399251004fc7650130006ff5058031006fd64947200077c654c540005fd7010950007ed6290a50005fd748c9500ddff760ca51006fd7018530005fc7354421007ef4290b10006fd4298650005fd7290610007be64d0c10005fe748c9100c5fc7408510007dc6350910005f9708c710005fd740c950006dc63d0110015fe758c9100077e530c9510bdfc7254310006fc3298251006bd6498c10007ed62d0810006ff5198e41005fd7695031006bd7019131006fd6510e10005fd740c410007df638c910006fc6154140006fb6098031017775254510004fd768c810005fc7388410006fe7158042007bd4210410007f940481100bfee4210b10007f44394510007be43944410067d65508100069c64d8d10005fd70d0f10004ef76484210467c65cc110006fe4358730007bd4290530004fd7019151006fe4398730006fd6550910007ed6210810006ff32582510067f6510510006f7610c520007bd43d0951007be4310950005be748c5400077e3294650007fb32c4110006fc2198443006fd7158032006fe75185400d6ff6454320005ff7348210004fe7398010005bf744ca10006fd64544310077d758c4100e6fd760ca50006fe42582530067d65480100a7ee6210810004fd768c4100ef7e6554421005fd7210e100077e5310e50006de638c8100c5fe728c510005fd7490d10006ff7518543007dc6350d50006fc7650a10005fc7150e50007bc4310910025fc7550310015fe75d0d10005fd72106100a6fe760c810005be740c951007bc4354540005fd73d9110007bf4290510005bc7350841004ff7654b30005fc71501300077d4394551006ed620ca10004dc7358650007bc4390950007f74254510006fe65d8031004fd7694740007f442545100a77e7508410006d
  | 11 => 0x7f671cc1100d5fe728c9500e5fc73086500b7f45108410007bd42543400467c5459730006ff6458730015fe754c9100bdfe7210710004fe76105500afee4210a10006ff64543100067d650c410006ed62cc010006fe3298251006ff64545300c6ff6218910006fe7198e200c7ec620c910005fd70d0e100077d4254550007dd5398031006fd42d8151006fd654cb10005f4715081004e7f5158254007f642c4010004fe76905100c77e750c910007fb304c310006f96018031005fd7298e10005fe7394b10007dc6394f10005fd7090d50006ce6358810007ec321852008f7c500ca51006fc6418d5109f7f5090d51006fe6194f42004fe7608510006ff5498730005ff744c010005fe718c950007be7110e41007bd4294540004dd768c4300077d43549510a7ec3208410004fe73d8142004fc760c520005ef724c540005fe7110a51007bd42544410affa700ca10005ad740c920005fd768ca51007ed4294720006ff6498730006ff5098e41005fd7494631006ce639881006f7c6554431006ef620c910007bf42d01100063e6599010006ef3258221005fd72d0c1004f7c5494140005fc71541400e77d528ca50007ef4250b100077d7598740006ef7658810006f76108550006ff7650910006dc63cc910007dd540c630006df5318d100077e75905100077e7598730006dc5418d10006be645001009e7e6590c10006fe73d8142006ff2098f40006fd7518543006fe6354621006ff6494120005ff7448310005fc748c7100d5fe720c550004fc7158a53006fe42597300877f52d9151007ee62d0810006ff7318540006fe62990310067f650c510007f7714c8100457e75d8730006ff644c310005ad72d0441004ef7258640007ed4210b10005fd72d8f100bdfe72d93100077d658c810006ff65cc810006fd6590c10004fe76d07300efec3254421007f543c4210004fe73d8910005be7494641004f77644010007bd640c810006be7610d40006ed5258021004fc7650f10006fe4058043006ff52987300977f5190950005fd7094c41005fd70d90310c7f62108510007bd4290550004fe7398254005fd73d8b10005fd7010b10005f97088410015fc7510d10007bf73d9110007f4714c110006ff5018d10005fd7448210005fd76d0e50005fc7155130007ef3208550006fd65ccb10006fd7118d20015fc754c910007dc430ca10006fc6298031006ef62c8110004fc7358041004fc7358a10006fd6458730005ff764ca510aefe4298010006ff65d8f10006fd760c440005fc76d0f10006fe7690550007ee4248110005fd76d0a510c7bd740c9100057f7550130007dc438cb10007ec3258221006ff7558021006fe63106500c5fc758c910005fd7418b10004fe760c550006ad6250040005fd7094d42005fe73d97100bf7d7508710007ef625
  | 12 => 0xf3208650006fe63547400257e75d9310006fe6058043005ff7448210006ff64d8f10007f43284110006fe4298331004ed72d8554006dd53580310077f7550130006ef628c91009f7f5290d51007ed4358810005f47148310006fd7018542005bd74d94310e5fe720c6500c5fc7250110004fe7118d52005fe7390910007ed4210a10007ef43d8910005fd7295310005fc74cc010007f542c4010004fe73d9610116ff2018552004fd70185420d6fe62543400477c5398e500277f5254f100877c5094e41004bc7458910006fc51580210befd760cb100077d75d9310007ed4398810007be4390910005bc7454d400077c6510d10007f73294510006fe6498c10007f642547100457c7550330007f54344010005fb7054f10006bc6490510005fd72193100067f65c8110006fd7018d52004ff7650a50006ff4398430005fd7010a10007fa4344010007bd4290650004de73d9410006fd6558031007f47150c10007bd4310d10007bc5459031007bd648c810007ef420c950005fd72d0010006fe4398620005fd7010431006fe4358031006fc71d8142004fe73d8552005fe73d0010006ff70185320067d6558c100077d75984430bdfc7518b10007ec62ccb100077e65d0c10027745454710005ff7388710006fe5398730004fd760c740006ff65d8b100aff9700ca10006fe5258041006fd7018532006fe4318152007be4310b10004de7399110007dc438ca10005fd748ca500bdff74c8310007f54354510006fd6550b300c5fe72d0d10006fd6559031007dc7258c10005fe768c540006fc7650130007ef32c80100047f7558221006fd31185420877c5454641006fe6298031007ef3254720007f9708871004cfd76943400c5ff73085100bdfc7308710006fe6150330007ee62cca100057e7494551004fc764c110005fe7190950006fd4398221007de7498c10007ec74588100ddfe7210e5104f7c5359250007ee4254621005fe74108100267c53597100077e4254550005fd700ca510077e53cca50005fc74ccb10007bc4390b10007bf4390e10005fd740ca500047f7558910007bf42541400057d7294d510047d7598740006ff6550f100047f7558043007be64108100ddff740ca51006fc6310710007f4410c610006fc3298341007df430ca51005fe7650b10007df7350810007dc7350b10006fd4298010006fe43d8552006fd7518d20007ee42884100a5fe7290810076fe7198e51007de638ca51006fc764c810007bd4290630007bf4290431005ff7250010007bd428c540007ec3294520005bd740ca510e6ff6494320006fe7358043007be4310a50007ed4248110006fe5318542004fc7358440006dc634c910006fc6418b10006ff654c8100bdfc760cb10007ec3288510007ef4290a10006fd43d8121007f44194421007bf6490910
  | 13 => 0x9110006fd4298331007de5390530006ff43181510047d7598443004fe7694730005fc7654b10005fe718cb100bfde324cb10007be4310a10004ff7654831005fc7150b30006fc42d9430006fc3298650005fd72d91100057d75d9031005ff7454b10006fc3259741005ff7359010004f77159520006fd4359621007bd42943400bdfe7218f10004fe7198e40074fe73d9431006fc764c910005f4714ca10007be43105100057f75503100bdfe7219310006be64cc010007df6390d100067d650c810006fd648c610006fd7018543007ef4250a10005fe7408510006df5298c10006fc5158241005df7350a51006ff50987200bfdd320cb10004de7318c10005fd72cc010005fd7090e50005fc74cca10004fe7610f10004fc764c950006fe6398a50007bc4390a100e6ff650c950006dd7218d10005ee7388120005ff748c410006fe4298253006ff5358241007f43194421007bc43107100069e6498c100c6fd7610910006fe42d85500277f5394f10005fe71d0b30006fd31d8142004ed7219210006bc6408510004fe7118d50005ff7250631005fc7358a51006fd7610e10006de6390c10005fd7294710005ec7350a2100dfe7550810006fc5198643004fe7398d10006be6498810006ff52580310afdf320ca10006fd650c910007dc7350a10005ec7250d50007bd4290710004fc71588400c5fe7218d10005f671c8110005fd7218f10006ed521852005f7c54544210a6fd76084100276f5294b10006ff6518f10007be64d08100077e4394650005fe76cc951007ef3208710005fd748cb10006bd640c410007ed320c810006fe43d81520adfe7210610005ff7290530006bc64905300067f7558041006fd6094f420adfc73086100d5fe7290d50005ff7355310006fc7558032007dd6390c10005fd73d0110006fd654ca1004e7e6550010007fb304c210004fe76885100bdfe720c710025fc754c310006ff6510e100d5fe72d8d500bff67118b1003cfc7359430005fc7150e100a6ff7018520006fd6510f310867f5359641007bc64909100e5fe7210650007f53294510005fd7090951007ef6290b100067d65c8010007dd7498c100c7ec628c910005fd7610c10007bd5410730006ff4298430006fe6354320005fc748c610005fe7394320006ff64d8d51006ac64189100257e75c8310007df4350f10006be4398740007ed4288410006fc6394b10006fe6498e51006fe4118520006f56190430007bf6450910006fe4118532005fe710c950005fc7448010005ff74cc910005fd728c4100defc6294710005bc744c950005fd7090810116fc3218552004fd76d0730006fd54d81320066c65d8910007f5315803104e7c65501300d7ec420c950004fe7119332007bc6455310007bf4310c10006fd7018540005fe73189510077e5490e50007e
  | 14 => 0xdfec3294720005ff7055231006fe53d81420bdfe72d0310005ff7454530007bc7399010005fe71109100ddfe7298e51004fc7654b30006fd65cca10007ef3208610004f57119030007bd7219110006ec6388521005fd7690a10005fd7010f30005ec7250f10007ef420cb10005ff72906300afdf328ca100eefe6254631006fd7098743006fe7158043007df430c910007bf4350a5104f7f5254540005fe710cb10006fe7498730005ff7650a51006fc63c8310005fd7310710007f93048110007be6450c100bfdf328cb100adfe720c610006fd658c910006fc7018532007bf4290410006fe73185400bfdf320cb1000dfe75d0c10005fd70cc950007bc4310810006fc2198f410bfec420cb10004fc7359640006ff5058242007bc4390a50006ff5118d400a5fe728c410004fd76886500077c754c010006ff7598432004fd760ca50005fe7094d42006fe4158221007dd74d8d100e7ec420ca500977f5090a50005fd740cb1001d7e75c82100bdfc7610b100477c54943300067f658c910007de538c640015fc7548110004fd76cc010006fc7650810004fe71d81420c6fe7158221006dc630c520005ff7250e10006fe7158041007f64110510007de63d0c10005ed72944210077d6590c10007df740c630006ff6318d10007bd4290610005fe710ca50007ef62d0910007bd42d03100077c4394150005fc7058443006fe3298031006fd6494421007bc6450910006fc4259431007de4310f10005fd700c540007ef420ca50005fc744c810004bc74595100059c7350b40005fe73d0a51005ec7250e50005ff7388610004ed7218c10006ff2058041006fe7198c30006ff4358650044fe7694130006fc32580410077f65d0d10007bf4294140116fe3218552005fe7190a50006ff43583310077e65d0810005fd70d9431006fc6154130004fe7318142006fd7318520006ff7558042006bf42580410afdd320ca10006ff5018d41005fd73d0910007f63284110006ed624c010006be5418540006ff7558241007dc74d8d10005fe76cc910006de7198c10007ef6250b10006fc6354540006fd6358a50015fe7590d10006fc6418d10006fc6354120004fe7318520005ff704ca51005fc7159330005fd7094621005fc71580430e6fd7608650005fe7694f100257e75907100077e6510810007f843840100bf7d75c831006d7e7518031007bd73990100067c7459410004fe7398221006ff5158242005fc7154330005fd7399010005fd740ca100077e4354a50005ff7610c10005fc735001000dfe750c810005fd7090f10006bd6458c10007ef328c8100befc3298410005ff7458e10006fe7358241007f671d93100defe760ca51007bc6495310006fe7690530007bd6490e50007ec3298221007dc630c910005fd74c8110006ff5458031006bf53d
  | 15 => 0xe76d0910006fe63084100277e6595310005fd700c9100a7f62108410005fe710ca10007bf4250210005ff764c810007bc6450d50005fd7299210007ec42cca51007ee42545200ef7f5218951006fe6194740006fe6299030006ff755823100e7f5218151005fe740c410005ff7488710007ef324cb1001d7e7590610007de72d8d10006fc4298430004fd7690430005fe718ca10007df4350e10007bf42d0010005fd741895106d7c755803100dfc7510c10007df6454f300c5fe7210d10006ee4218520007ee42480100077c3254550005fe7398a100aefc3298010006ff42181510467e65cc010006ff65d0d10006bc6490550025fe754c31003e7f52594300c7f970109100defc6294530005fd7610e51006ff5018d400077c654c910007ec3248110007ef6294b10006ff65cca10006ff7518542005fe73191510a5fc758c810007bd42d0210007be540c540005df7350910004fe768c910025fc75ccb10006ff325973108f7f510c950006ef63d8910006fc42594300065e6598c100bdfe7290f10006ff644c110006fd6458e50004fc7158a50015fe75cc110025fe75503100977c5390951007bd6450a10005fd7490c100077c65cc910006ed52582210efbd740c951005fd70d0b30006dc638c5100c6fc21582210077d7590e50005fd7090e10006fc7098432006cd6358810007de6390e51007dd6454f30006fd4398430006fe7258031005fe7110e51007de739053006f7c5418d51004ff7650010006fe4258430006dc6318910005ff7050f10005de7390631006dc638c550005bd740c910006fd65d08310067e6598810007bd4250110005fe73c83100bdfc740cb10025fe75d8b10005fd7488410006de63500100afde324ca10006fe3298650007dd544c7300befe3298410007ed620ca50005fe76ccb10006dc6388510045dd7694f30006ff7418520006fc53185400edfe72d8d51004fe768cb100bdfe72953100a7bd740c810006fd64946310067f73596410e5fe7290e50007dd5358730006fd6599031007bc744c910006df5498c100077e5390d5100dfc754c81000dfe758c810007bc4394641005fd70946310c5ff740c910005fd7290d10007dc638c910006ff7598720006fe43982510a5fc7408410006fd7518540005fe73d9151006ff43587300069c6418d10004ff7058a53006ed620c440005fd748ca10004fc7158b40006ff64d8b10005dc7350b30005fe748c810006fc32d8151007ed42c8110006fe75580320077d75d8f10007be4350f10004ed721814106e7f5259431007bc4310610004fd7690730004fc7650d10005ff7050e50006fd65d08300277f5495310007bf4250310007fa43c42100067d658c810006ff4398730004fe7610d100bdfc7690b10007bd7010d40005bc744cb10006fe6394320007bf4254641
  | 16 => 0x4f10007ed43d891004e7c53d9540005fd70ccb100077e758c7100a7ef7498810007ef324ca10005fd74189500277e6554b1001dfc75cca10005fc7150950007f63188510006fe6518031005ec7350920006fe7018d42005ff724c3100bdfc7590b100067d73d9540005fe73d0910006fe4258251005ff7050b30006fe6310a1001e7c53d96100077f32941500077c4354951006fe7518d100057e7494d51006fd64580310077d7518520006fc42987300767c5359731007f93284010006fe62993300aefe32980100077e6550c10006fe7198e50006fc5058243006fe65d8730004fe7688550006fc7398443007fa42c41100adfc740ca10006fe634c210006ed4218520007bf6450951007be53508410c7ee42c8110007ed4248010005ff7058443006fe645901009dfe7310d50006fd3098730007bf6410f10007fb43c421000dfe754c810005fd7610810004ee7618910007ed6290a10006ff624c540007bf640c9100066d6558810006fd6454621007ee4318910007de74d8d10005fd700c73004f7c65541400167f5258650005fe7310a51007ef7250f10005f97010c300ddfc7258e51005797094e5009f7c5090e51006fc4218151005fe7399250006fe41d81320ef7e750c9510066d6598810007be4350e10005fd70cca50005fe7448110006fc4258331006fe7158241007df7218d10005fe7390d10007ec32884100157e750c91006f5e6594c31006fe5158021007fb3284010006fd65d0c10006fe32d8151007ef420ca10004bd7690440005bc744ca50006fc7650c10007de63d0810006fd42584300ddfd76947200e77f5290a50004be74d85520adfe72d0210004fc7650530007bd6490c10006fd6358a51006fd41d81320077c43945510a77e750c810005fc7348310006ff4258650006fd7518d42007f43254710006ee43d8910006ff654ca100067c6454550006fc4218550005df764c431007de6310810006fd5358241005ad74c8621006fd7018520005ec7250e100477c5459730006fd3018542006dc5218d10005ff7050d50006de7498c10005bc744ca10007f432c4010005fe7194f40005ff764ca10005fc7154130006fc63941200067f75580430bff6710cb10006be63904400477c5159730004fc7358b40006fc3298041006fe63d00100077e75904100d77d750c9500077f65d09100afec420ca10007f97018f10034fe7694120007df438c910005fd7310610007be7010d40006ff7558232006fc3259730007de4310e100077c7550130005fc7458810005fe7190a10006fd65d88310077f65109100edfc76909510067c7558031007bf744c810007bf7259010005de7394631004fd7098442006ef64d89100d7be740c9500edff76547200567c659013000d7e758c410007be6490e10006756544010006fc4258650005f
  | 17 => 0x4fd7098e41006fe7098e21004fe73d8520005fd7650e10025fc7590f10007f443c42100067f6590d10006fc32d8550007f970d9310005fe7190e510e7be740ca50004fc7650b30006fd6510810006ff65908100077c7558e10006fd7018d10006fd425825108e7f5118d52004fd760c440007bc640c910006fd4318151006fc73185400077c7550230006de6398810006ff4298730005df764c730006de63cc0100d7ee4208550005fd73909100057d75180310eefc6254540006fe4318552006fe5158241006ee4258221006ef7058b41006fc5398430005fc7348210007f942c4110006bf6499330007f63254710005fe7398a51007f64384110005fe7110c30007ef620cb10005fd7090631007bf648c910007ec3254621005fe7310550005de7310431006fd6590b100defe6294641005ff704c910005ff7350210007f743947100077e53509510767f5198e510e77d750ca50006fc6458730005fe7390951004fd7099221006fd54185320a6fe6258810007bf43d0b100ef7d7590951007fb4344010006de6358810005fd76d0810005ff74886100a5fc72500100c5fc724c110006fe7518d40006ff65d091004f7f5194d40005fe7348110005fd74cca510067f65d9110006ff5018f10006ff5398c100067c6354550006ff6510910007f9700c410007f632c4010005fe7690f10005ff74cc810005f97094710004fd70191530adff74c8210007ed6250a10015fc7550910005fe7390810006fc3298331006ff70185300c7ec7318910007f4714c810004fd7019121004fc73595100367f51d8152006fc5198c10006fe7558241006fc64987300077d7590530006fd6454330005fe748c410005fd76d07300077e32545500069e6458c10007be43908100057c7354951006fe7118d500057d75d9310004fd7610c10006fe7298740006fc65580310c5fc7610910005fe76909100477f5254730007be73d9110007be4390951006fc6558730006ff65987300bf7d750cb100edfe72d0d51005f9700ca10007bd4310c100069f6418d10025fe75ccb10006fd54185200a6fd760c810006fc5098642007ef6210910006fe6154330006dd7498c10004ef7648020006ff4358031006fe729844303e7f5118d50004ed72991100bdff73c8310006ff6258031006ff4258331025fc75d8b10006fc50984320a5fe72d0c10005fe7610910006dc6394d42005fd708ca51007bf64909500067f65d8d100067f650c9100eefe760c9510257c75503100e77e7590a500877e6554641004fc73586200a5ff7308410006fc4258730005fe71d0950006ff7650010005ff7050e10005fe748c5100adfe7290e10025fe75d0b10004fe7318154006ed4358810005fe73c8210004fd769503103e7f5459430006ff4258730004fe7610510007ec6254b10005fd729
  | 18 => 0xe718ca50005fc7150b10007ec4398810006fd6550b100defc6394720006fd73582210077c7550310007f9708c410006fc7298730007be4390550006fc325844301dfc7590e100067f65191100afee6290a10007bc648c910006ed4258221007bd72990100a5ff7690810005fe7110d10006dc6348110005fc7650b1006e7e65d9431007de6350c1000dfe7590c10006fe6498e10005fd73d0810005f47150310004fe73d8542006fe4398410006fd645472004f5f5394d40005fd748c510006fe4398650007f64394710007ef32887100a7ec7398810005ff71580430a7ee42c8010006ff7518532007ed4208550005fc7150a500077e5390a50004fc7358640005fd74c80100d5fe72191500077f6550d100af7d750ca10007df63d0d10007bc4390510006f561884300477c5498e50004fe7610950005fe71d0b10006fd43586500067e73d95100077e544c951007f54254710004be74d962100e7f5259410007de7398730025fe7510f10004fe7610b10006fd76cc010007bf43509100defe6294730005fd7299010007f44354510006fe3298331005fd70d0950006fd531852001d7c7550210025fe75107100063d6599010005fe71d0e510077f75503100047d7699410006ff6510f10006ee5218520007f970d8f10007be43104100873c5095241006ff6454330007f443440100d5fc7250d50005fc7350a510077d32941500c7ec32c8110006fd76906500067d6590c1008f7f500ca500defd760ca51007fb42c4210006fd6258730005fd709444104f7c6594140044fe73d9430006fe7458031005fd70cca100077e758c610005fc714ca51006fd4358331007f47150a10006fd6590d10005fe740841009eff6590d50006fd4198443004f67119030007f842c4210005fd74d8f10005ff7350310007ef7250e10007bc6450b10005fe71d0a50005fe74c8310005f47150e10006be6450230006ff6518b1004f7c54592500bfbe740cb10006fd6298730005f9700c43001d7e7598a10007f77150a10005ff724c210005fe7488710005dc73509500affa7010a100047e7619510007dd63d0c10006ef6250110005fd74d9710005fd7308510006fd65d80310267c5459710004ff7650e10006ee73d89100adff73c8210007dc72d8d10006ff7098730006dc6390910007dd630ca510adfc7590a10005fd7408510006ad6458810007bd64d0330007dc7498c10006fc7358241005fe7318910006fe71d8142005fd760c810005fd73d001006f7c5354431005fd7290130006be6450330006fd7018d51005fe7110f31006fd65d0810005fe760c951005fc7458c10025fc75d0f10005fe7494710006fe30185420047d75193310167f52d9510005fe740c910006fc5498c100475e6594f30006fe43d9520006fd6458a5101dfe75d0a10006bf648c510
  | 19 => 0x465005f7c5308650015fc75d09100557e758c640006fd42d8550006fe71d81320c7bd42109100077e5350a50006fe32d85500c5fc7510910007ed4254720006fd7610f100077e4354550007f732c4210005fd7010f10006ed6250230007bd42500100a5ff740c81008f7c530c951005ad74c8520004ff764c810006ff64d8951006fe43d8151005fd7290c10006fc631095001dfe7510e10005fd7418910006ff6494330007be4394540004ff760c410005fd70d0a50006fe6458031005fe7310710006ff4318550006bf4298740006fc32584300067f6550110006ff2098e54007ed42c8010004ff760c7400e6fe6294340007de538c540005ff7350b10006fd7018d40005fe74c8210006ec73588400afbe740ca100a7ef7398810006fd4018552007df430c951005ff744c950005fe7488610007be5390440005fe71d8b3001dfe75cca10005fe7110951006ff71d8143005f9700c520006fd6458b30006dc6310510005ff7458a50006fd5358221007bc5459330007bd544c540005ff7650a10005fd74cc310004fd7610e50005fd73905100e7ee4208650006fd7098730005fd700c550007bd43d0950006fe7598c10006fc7258043007df4390d10004de7319010007ef42cc9100167f54d95100057d7295250006bd6419031005fd7010e50007f74294710006fd6590a10007dd5398730006fd30d81420057d75c8310004ff7654720006fd7118d420bf7f5294b100077d65d0c10005fe7110810006fe610c740007fb4244010006fd4358730007df430c810004fe7688730005fe73d8950005fd7094431007bd42107300377c535472006f7f520c650006fd4318550007fb4050310005fd76cca50004fc7359410007ec42cc910007f44294710005fd7610a50007dc7218d10004ff7650e50006ff4218550025fe75483100077d75906300065c65d8d10005ef7250e510065e6558c10006fd4398730006df7018d42006fd7558231006fd5458221007bf43d0a10005fe731065001dfc75d0e10004fc7654730006fe5298740006be6490431007f64294510007f6411041005f745154421007f84244010005ec73485200bfbf4210b10005ff7250f10006fd7418520007dc6390d10006fc764c110006fe3118520005fd738c9100efee4254720004fd7018d41005fc740c510006fd6494330004fc76501100bfec6290b10006fe43980310c7bf4290910005fe730c910007ec4358810025fe7590b10007bd4350a51026ff52984100877f5254e410077f4354a50006fd7018d210057e73945510077d3294551006dc6350910006dd63500100877c53906500077f4394650005fe7308550006ff4258031005ff7690c10005fe7190b10006ff6550810006bc6418910006fc6194520004ed76884200077f3294551006de63d0c10005fd7010d50005f
  | 20 => 0x6fc73d8142005fe74d8b10007ed4208650005be73d0540005fe7390c100d77e7508550006fc3258740004fe73d8b10007bd64d0c10007f643c4010004fb7644010007f943c4210005f97090710006ff764cb100077d7590710004fe7318540006fe30d8142007ed620ca10005fc7650951005fe7308650007bc4354140004fd76108100e77f520ca500a6fe7610810005fe7398a50006fe52984430057d7590631007f73244010005fe7190d10006fc7358041005ad72d0540005fe7110c310aefd760ca10005be740c950006bf5159032004fe760c540007df438c810005fc73544410e77f5298a50005f9700c620006fe6310b100afbf4210a10006ff63185200bdfc7250f10007bd64d0a50007ec62cc951006fe51582210c7ef7318910005fc764c950005fc764c910004fc7654520007bc744c810006fd7258031006dc630c510006fd6550c10006ef62cc110005ff76d0a100e77d5210a50007df63d0910007bc43d0110004fd7688730005bd740c951004fd7694730005de7390431006fe7198e40007bf42105100edfe7210d51005fd700c951007fb4050210004fc7358b10004ef7259510005ff7458a51005fd70d0b10005fc7650f10005fe74cc1100257c754c310005f6710cb100057f7558031006fd6590f30006dc6354f100a5fe7210c1001dfe7590a10006fd4118532006dc630c550005fc744c310007f47150310006ff7098432005fe7310910004fc7654540005fc7150a10006ee6498810006de6310810004fe7690531006fe7118f10005fe7195330007bc73590100bfee4208710007f532c4210005fd700c810005fe74d8910006fe7158031006fe6310a51026ff5498410007df6310910006fd6550a10006de63d0810006f7610c54009f7f5190d500c7ee320c9100e5fc7258e50006ff648c5500e5fc7250e50007dd63d0810007f44154421005df7350810006ec63d89100e77f52943200057d72946500077c7550210005fe7098443006be63d02400077f4294650007f542945100067d6550010006ee5258221006fe7018543005fc74887100befe760cb10007ef3288610007bf7219110007ec3254520006fc634c110005bf7650441006fc73582210edff740c951006fe439801000e7f5459410007be4354340007ee6250a10005dc7350b100a5ff760c810007f4714811000dfe750841006f3f5495031007f44108410007dd6310810005fe74cc910006de634c0100c5fc750c910006dc638c540004bc7458653005fe71d0a10005fd708c910005ff7055031006ec3218520005bd7418031007ec6250b10005bd740c810007ec3248010006fd624c010006fc6598730006fd43d8520007bd4254540005dc7350a50006fc6310910005f97008710004fd768ca50004fd76d0030006ff6550d100df7e65947200077c429
  | 21 => 0xf20987400057d750cb10006ff7418532005fc714c910007f54394710015fe75c8110007be4394340005fe7308710006ff4298251006dc63c81100c5fc748c910005fd7010e10007be72d91100067f6518d10006fc5398730006fd4398620025fc7590710005ff7050b10004ec76509200047d7519030007ee624c81001d7c754c210006de630c621006ec7358b41006fd7098e41007dc638c540004fd768ca51007f94344010007dd548c430004fd7695330005fc7454310006ff7298730006fd7518520006ff7650230006bf5059032007dc430ca51006fc4298251006ff65ccb10004ed72d9410006fe7318542007ed4208710004fe7318542006fd435803106e7c6559431005fc7358a100a5fe7298c10005fe73885500077c6590910005fd7318910006bc43580410077d65d0810005fe71cc950005ff74cc210005fc748861006f7e6594431004fd76947200bdfc75087100a5ff768c810007bd6410431005fd70d0a10005ff744cb10005ff74cc310005dc7350a10006fd7018d42005ff7050a50005fe73d0951006ff6494431005ff7650a50004de73d9621004fd7610a10005fd7290631006fe638c4100bffb2048310005fd744c910006fe6498e50007be4390650007ef43189100bfec6294b10006fd7098740007ed62cc81001dfe7550e10005fe744c910005fe73d0810007f53254510025fe758c710005fd7498e51005ff7050950005fd74cc910025fe7550f10006ff7598730006fc3258251004dc7359520006fc7650f10006fc764ca10006fc4398430006ff63d8910006fe6498a51007f431544210afee4208610007f43108410007f53244010007bd7259010004be74d9730006ff764c210006fd6559330007ee62cc810004ff7058841004fe7119150004fe7119120007f832c4110007bd4210550006ff654cb100977c5190951006fe43d9521006fc3298440005ff744ca50006fd43d8552005fd76cca10006fd75d8132006dd6358810004fd760c640007bc7259010006fd745803100d7e750c810006fc535833106f7e6595031006fe32584300c7ef7418910006fd6598730007be4390710005fe744c110006fc3298740007de7418d100d6fd760c9500867c6590510005ff7258c10004fc7359641004fe761073004d7e758c5400c5fe7290510005ff7350a10005fe74480100067e74d9510007bf6490d10006ff53185400077d6510810006fd648c410006fe3158221007f57110f10006fd7518f10006fe7598720005fe73106100077e75905310bff5710cb10007f64354710006fd4359620006ff4398251007f73254510007bf4294e41006fc7650110006ff5158032005de7394431005fd7218d100067c72594100deff6494421005fd74cc210005ff7359210007bf7399010007be6410c10005ff76d0c10005fd740c550
  | 22 => 0xd10004fd760c6200a7f97008410005fd760ca500077e6510c10004be7418151006ef5018910005ef7250d10005fc7354720007bf4350810004fc7650950006fc3298031007fa4284010006ef624c110007dd6390e510067c7558041007bf4290730006ed6290410025fe7519310006fc7018542006fc7158032004bf76500400067f65d0d10005fd7308410005bf744ca51006fe53580310477e659533001e7c54d9610007bf7319110005fd740c650006fe6358e10005fd7210510006de630ca51007bd64d0810005fe740c810006fc6598031006fc5198432005fe7494f100e77e7508650004df764c431006fc2098c41006de6350c10006fd6454421004dc7358910005fe7308610007be64d0a10005fe7390710007df7418d100067d65cc010006fc4258031006ff7558031006ff7650b10006ff6454130007f74384110005fe7390550005fd7098e21007be4390610007ef3248310006fc3298443006fd7018f100065d6598c10006fe43d8550006ff6298031007bd64108100157e7508510005fc7354310007bd6490a51004fd70185430877751946410067d74d95100077d4394650005fd7408410006fc7158042006fe3258251004fe7199250007bd4350910007bd43d0a50005f47150951007dd6350c10005fc76ccb10005f4714c310005fd7390810006fd7610d10007f76394710006fc6418d500067d6558810004fe7119152007bd43d0b10004fe73d8950006fc3259441007be43d0310006fd43d8152006dc630c910007fa32c41100c5fc73c81100057d7590431005fd7388710007ed4208610005fc7154b30006fd628c540006fc6190530005ff7255130005fd70d0e51004fd7610730006ff6590a10007dd53180310bdfc768cb10015fc75d01100067d6598810005fc7654540007bc6490d10005fc744c210005ff704c8100077f754c1100eefc625453004e7f53d9540007bf6495310006fc5158243006fc5298c10005fe7390650006fd64980310affb20482100deff6590951005fe7348010006dc630c9500063e6559010006ff650c810007de5350530007f762947100bdfc7255310006fe4259731005ff7250130006fe768c5100077e5310951006ff70987400067f65cc110007de53107300bfbe4250b10007f6310c5100a5fc724c010007dd644c4310077e5450e500177453545100adfc7250e10005fc73509100d7ec3208550006ff20984430bdfc74c8310005fe71d0d10007de535803105e7c6508510006ff5058032006fd650cb10006fe43983310977c5490951007ed624c810006ff64d89100c5fe72cc110007f671d8b10005bc735074000dfc7550810006fc5118540006dc7498c100077e53d0951006df64d8d10005fe76d0d10006fd65d9330004fd760c810004fe760c9510066c6518910004ed7219010006f
  | 23 => 0x6bd6458810005fd73d9710005fe71ccb10006fe6398a1004f3f51951400065c6518d10005fd7418f100057d75d9330005ff72502300067f6254550007dc7418d10025fe7510b10006ff5398430006dc7198c10004fe7318121007be644c810006dc638c910005fd7388610005fd7690a51006dc7598c10004de7318151005fc740c410006ff7558343006fd7518542007f94284010005fd7210d10006ff764ca10007ef3248210006ff7018540005fd7098443006ed62084100a7bf42908100059c7350841006fc5498430004fe768c550025fc750c710006fd6454631005ff740c510006fc7650d10006be6490631006fd71d8143006ff3298430007be43d02100067e73d9540006fd650ca1006ddd7694c31006de630c7400077d6550c10007f43294510006fd6510c30005ff7050a10006fd5318540007ef32543200057d7294e50005fc7354b10006ff4398410006ff658c810005fe7110d51007dd4310f10005fd7348310007bd54cc7400afbe4250a10006ec3258221004de73d8810005fc7388710005fd708c540006dc638c950005fd73d8910007bd4210710005fe73886500adfc74c8210007ec7358810006ff6519310006ff4398650005fe7394710005f671d0110006fd768c610006ff6494520007bc4354641005fe71cca50007dc63d0d10005fe74d9710007bc43904100067f7459410005df7350951005ff744ca100077f7558031007dc7358031005fe7110c10004fd7610e51007dd750c630006fd75984430bfec620cb100c77e75c8110004ff764ca51007ec62d0910005fd748c4100077e4294150005fd7010730006fe7398740007be64cc810005fd7019031006fd658cb10007f97010410005fc764c951006fd75984420077d758c7100067d65d0c10005fc7150e51006dd760c630005fe730c810004ed7298d10007bd6490e10007ef7458810025fc758c710006fd6510c31007be4350110006de5318530005fd7010a51005fd720c5100efec3254720005f57110c310bf7e7508710007bd43d0a10005fd7494b100477e6594730005fd740c710006ff6550a100c7ec6210910007ee4288550007ec43d8910006ff7458221007dc438ca5109f7f5090e50007bd4210650005fd7294130006fd6550b31006bf640c510005fd73c81100d6fe760c950007df7498c10007be5490430007bf72d91100077e530ca50005be740cb10005ff704c9510a7ec32c8010007bc4350310004fd760ca51006fd760c650007bf4350951007be4354441006fd65d0d10006fc42d9730007f46394710006fe7018542015fc7550d10004fe7610d50005be740ca50006fe7098443006fc7258031006fd7598740007f65110431007dd53d8031006fe61543200077c6550910007f97090410006ff4398031007bf6455310004fc7158830007df635
  | 24 => 0xf3294320006fe7610e10007ee4288650006fc5198642005fd7348210006df5018d10005ff744c310006fd65109100057e7494650005fe7310951007bf6490d51006fd65d0910004ff7058b310bf7e7518b10005fd748ca51005be74d94310a7bd4210810007d661cc730006fe5358041006fd7558021006ff43d8151005f67110d10006fd6158043005fe7198043005fe74cc810005fe73d89510066f65d8910007bd424c540004ff764ca500067f65d0910006ff4298031004fe7199330005fe76d0950006be6490410004fe760cb10005fd7310910006fe6354340007bc72d9110005fd740ca510077f6510d10005fd7694730007f67110f10006fe6558730005fd708c810005fd74d8b10004fd70185320077e5490951005fd740c610006fc6194540015fe75d0110006fe6299331006be70191320a5fc750c8100f7dc540c430006ff6494130006fe65987300d6fe7608550005f67110f31004fc7650951004fd76106500af7e7508610005fe73108100477f51d9730007dd5318730005fe73d9150005fe768cb1009f7c5390d51004fd7098e21004fe71d8950005fd744c110004ff7058a54005fd7090431007bc4350210007be4310a510c5ff7408510004fe71191530befe7610b100d5fe72d9150006fe4358430006fc5158242007f442841100067f654c110005fd74941300067f6510910006fe7118d42006fc4318151006dc7018d42005be740ca10007ec42cc951005f4714ca51007f74284110007bc43d00100a5fc7510810004ed72d9741007bc4390a51004be7498253004fe7119330006fd7498730005be7395241005fe7650d10005ff73481100077d4294150005fe7610f10006ff73d8142006fd43982510defc6394421006fc4298031006fe7098442006df6350110007df4390c100bfec32087100047d7518c10005bf744c910006fd3018552004fc7654831005fd72d0f10006bc640c510004be7418152006bd64cc010005f97088710004ed72982430069d6498c10006ff6558031006fd3298430007de530c440006fe4298653007bf73590100077f7558221004be7498d10005fd7390410004fd7019132006fc21582540e5ff7690a500877c53d91510067c7558221007f671d0310006bd7019132007ef42cc810007dc7298c10006de638ca51005fe7388710005fd760ca51006fc610c520007de630ca510077e54cc951006ff71d8142006fc6518f10006ad6290440005fe7498e10004fc760c540004ef7258653006ff7418530005fd7090950006fc5358031006f5610c430007bc4394140005f9700c4100defe6294441005fe7390610004fc760c550007bd4254e41004bc74586500077d4354a50005fd738c8100c5ff748c910007ec42cc81006f7c545443106f7c750c6500afee620ca100477c6554730007ec7250f10
  | 25 => 0xc951006ff75d8132007dc63d0910007f74354710007dc7458c10006fe4158043005fd708c550006fc43583310c7ee42109100a6fc3218520005fc764c540005fc7458a10004ed72190300067f6550130006fe7298730007ef62cc910004fd7690410007f743c4010006fc618c5400ef7d5290951005fd7090a500adff768ca100077e654c810007ef32c8310005fd7498a50007fa43c4110007de6350e51005bd74d97300a5fe72904100deff6494720005ff7354310006be64084100057e739515108f7c540c951005fe73d0310005fd74cc9510c7fa700c910004ef7258650007de7298c10005fd72d0310004fe76109100067d7518520025fe7518f10006ad62d0040006fe7610c10005fe744c0100077e5450951006ec7158840006bc64c8110025fc75cc3100977f5190a51006fe7518f10006fe7598432005f671cc310004fc7358a51005fd74cc810006ff3259431007bf4290550005fd7194d42006fc4358730005fe7190d51006fd71d8142006dc63cc1200a7ee320c810004fd760ca1009f7f5290e50006fe63104100377c5454720006fc4398730005fe7388610006ff2158043005fe7194d42005fc7358810007bd4294641005fd764ca10007bd4290631006ed43d8910006ec5198810006ff4298410006ff7518530004bc7458430005fe7190c10015fc7550110007ee62cca500c5fe7210910007ef3294421006dc5398c10005be74d9730007be5310640006fc5098e41007d9700c4300d5ff7654320006fe6190730004fe71992300a6ff2018520006ff4298650007ec7250e10006ff624c310005fe71cca10006ff7098720005fd7448110005bc744c540005fe7610950007df7350b10005fd7690c10005fd72d0e10004fe719912000dfc75104100077e65cc810006fe6310a50007ee4288710006ff6419310004fe76950310befc4298410004fd76d0010007bd6450c10004fc764c540006fc4298650007dd4310e100077c7559210005fa700c520004ff7654740005ed72d043101dfe7510a10007dc430c910007ec32d8520005ff74588100277c5354f10005ff7250310007f63294510007dc63109100bdfe7294f10007bf4210410005fe74cc010005fd708c951007bc73d9110006fe4258653006dc630c540005ff7458a100067d65d0810005fc7458e100877c5490650006fe6498031006fc4258253006fd6458a50004fc764cb10005ff7255310006ff6454f100047d7598d100077e4294551006ff4398010006fc4358650025fe75d8f10007de6310c10005fd7290510006fc4318550006ef6290531004fe7398341006fd658ca10006df7218d100067d654c010005f47154310005fd7198043005fd76cca510067d6510810007bd4210610006fc6354140006fd4318152005fe7194d2000dfc75d0810006fc3258341007e
  | 26 => 0x6ff6590c10005fd7219110006fd43185520057d7518b10007ed421091006e7c5359431006fc5458331006fe7598e10006ff6258730005fe764c910006ff4298010006ff63d8b10005fc748c510005ff7254130005fe71d0d51006fd6510c10007ef32c82100867e6590410005f67110c31007f6310c410005ff748c710007f54384110004ff7650a51006fd43d9520005fd7010910006fc42d8151025fe7550b10006fd6590f100dfec420ca51006fd6458c10006df6418d10004fc7358740005fc7350951004fc7358a54006bf6499031007ee4288610005ff76d0e10006ff62987300aefc4298010005fe7418910006fc2158043006fd6458830004fd7099253004fe73d85540057d7598443005be74180310bdfc75c83100a5fe72cc010006fe6498810006fe6308610005fc714c951006fd7098443005ee76c8520007bc6490f10005fe7190a51007bf6450b10007ee4254120005fe71d0c100e7ec32086500c7f9700c910005fc73508100077e7590530007dc438c910006fe6394340005fc714c810006fc3259740006ff650ca10006ff3218151006ff7648210005fe710ca51005fd7490910007bf4294540005f47150a10006fe61d0330005ed7294720005cc7350a21006fc2198c41006f67118f10006ff75185400a5fc748c810005ff7650e50005fc7448310006fc7558241006bd644c010007be6450e51007f642c4210006fc6310b10006fc21987300867c6590530006de6498c10007bf4390d10004ff76487300077c42545500d5fe728c550007bd4294740006fe6398a5104f7c5354540005ff7250210005fd7418d50006ff7358241006fe5358043006fe7258043007bd540c740006de7618d10005fd76107300defe6294431005ff744c210007ed42887100063c65d91100deff650c951006de5398730006fc634c310006fc3158221005fc7388610005fd7695330005fd728c7100065d6558c100275f5394f10005fd7090b10006ff6494710007df6454c31006fd70984320047d75d88100067f658c540006ff5058021004ff7654e41005fd70105500d7bd740c95006f7c5459431007bf64d0d10006fc7158232006ff75d8143006ff3259430006ff51986430077c650c910006ff6510d10007bf4310f100afec3208610005fe744c810006ff2198c41007ef4290910006fe4358251006fd6519031005fe740c710006fd7018d41006bc640c9100bff671c8310006ff63d8951007ef624c9100077d4294551005fd7090e51005fd744c81009f7e7590d51006ec6418910004ed7218154007ed4318910006fe5258043006fe7118d52005fd7094f42005fc7150d100eefe6254641005fc74cc310005ed7210330006be7199010005fc7154340005fe718ca51007f7714ca10005fd70d0d100376f5154b20005fd729463108f7c510
  | 27 => 0xf7690a510a7ee6290810005ff7254530006f56118730007dc6350d10007bc4310b10007de634c810025fe75d0f10007bf4290710006fd3218550006ff658ca10005fc74cc210005ff7454f10006ff5398730007ed320cb10006fc5498e10004bf7650441006fc549873005f6c5054821006fe40d8132006ff5098643025fe750cb100c6fe7608510006fe7598e40005fe7690d10007f74254710005fc74cc910007ec3288550004fd7690630006fd6519330007bf64d0910007df7350a10006ff6318f10005ff705883106cfc7359431006fc51987300adff7690a10005fd728c610007bc43909100077c3294150007dc7350910005fc7448210006fc635431000dfe75884100467f5259730007bf6410910005fd7090a10007ef425091005f7c5318951006fd325833100dfc7550c10005fc744cb10006fd3258650006fd40987400ddfe7290e5105e7e65084100077f654c9100c7df320c910007f542c4210007bf4310e10006ec7358810006be5458041006ff63d895000e7c53181510067d6550c10007be73191100aefd7610a10005ef7250d510057d758c540006fe6394720005fc73503100c5fe7210510007f64254510006fe41580310077c754c310007bc7319110006de6390e51006f461cc5200a6fe32185200067c6518910007f442c401000dfc7588410005ef7250c10005fe73d0210005ff70590310c6fe76c8110007bf42906500c5fc73085100e5fe728c650006ff3218550005ed72d8730007bd6410730005bf7650740006ff648c710005fd72104100077f4354550007de63cc810006bf50d9110007f64244010005fd7650a10007de5398031007fb304c110007bd43509510077c658c910004fe7119031006ff6590b10006fd6550d10006df5218d1000d7e7508410006fd65d0b30006fe6358c100eefe62547300063c651911004f7f5294140005fd76d0e510d77e750c950006f6619043005f7c5408650007ef328cb100a6fd7610810005fe7690951005fe7610b10005ff7448110004fe71992200077f4254550006fd32181510eefc6354720007bd4350810004fd7098743006ff3258650006fd759874300dfe7590410005fd72d0210007f83284010007f47150e10004fc764c951004de7398d10004fe73d8550007bc64d0d10007ee74d8910006ff5058241006fd5418530006ff3258331004fc7654f10006fd624c2100077f65cc9100067f6550d10007f77150c10006fe7690510007f843c42100877e75905500defe6294740006df7498c10006fc4259730006ff7650210004fc71582420a5fc73c8010006fc6394140006ff7650e10006fd7318540007bf744cb10006fe63d0210005ff7458c10006ff42d8151005bc744ca51006fc53d8141006fd7558042006fc7318542006dc6390d50006ff5358331006fd4398031
  | 28 => 0xc740005ff7650e51007ee7458810007df7258c10005fe7610d50007bf4250030006ec7158810006de6310c10007bd42d00300757e75907310877e7590650005fd73c8010005fd7610a51005ec7250e51007ee6250810004fd7099231006fc2098f40005fd768ca50006dc6390d10015fc754c110007f44254710005ff7250d10004ff7058b41007be4390950007bc6410910005fe740c610007ef328ca100047d7519010004fe7198e20007df4350d10006de63904100aefe760ca10004fd7099251006fd3258730006fc2158031006df5418d100057c7454951005ff7050e51006ff3298730005fc7350210004fe73d9540006ff624c11003d7e75904300257e758c7100057f7558041007de7458c10006fc4298331007dd6310c10005f87054730005fd7210c100edfe7218d51005ff748c610007df6354f10006fd6558b300ddfd7694421007bd42905100157e75c8110005f47150e5101dfe750ca10006fe760c510005ff7650e10004ed72982530067d7598740006fe41d8152006fc6194530007ed4288610006fd6590e10006ff65cc910006de5358031005fd72cc21009e7f5198e5403e7c53594300a5ff748c8100057d7598740007f54254510006ff6454431007fa3284010004fe73d8951005fd74887100977c50909500077f7558043007de53d0730005fd720c410006fc5298430006ff75582210bfbd740cb100067c7359410006fe61580430d6fc6254140007bf744ca10025fc754cb10007bd73191100056d750ca21005fd72cc310006bc4398740007f54244010006fe63c8010007ec6250951006ff6550b10006fc6394520005fd748c910006ff2098f41006fd32987300167c5358650007bd7010e410bdfc74087100077c754c2100047f75580310077e7590630007f671193100edfe7219151005ff740c410007f64394510005ff7290631004fc7650d50005fd740c910005fd7488650006dc7218d10027775254710005f47148110005fe7319150005f97010a10006fc7098443005fe748cb10006fe5398740007dd7418d100977c5390a50006fc6318520005bc7454e41006ff5398e1001dfe7550a10006fc70984420ef7e65547200d5fe72d0d50005fe71193300c6fc3258620006fd4398410007f65190710006fc6518b10006fd43986500077f658c5400c7dd320c9100adfe72992100a77e75c8010007be43500100057471549510bdfe728c7100077e5390e50007f462947100e7bd740ca50006fd40d81320c6fc32582210069d6458c10006dc7298c10005ff7388510006fe4098443006fc7258041007de540c430017745454510006ff3258730007be4310910007ed6290810006fc42d9431006ff20986530c5ff74c8110007f84344010006dc6418d10007bd7110d40004fc7654d40007f742c4010007ed320ca100ddf
  | 29 => 0x7dc430c810005fc7354340005fe7394421005fc76509500a5fe7210810006fc2198c40006fd5318542006fc51580310077d6510c100adfc7408610006de63d00100afbd740ca100057c7354a50007bd42d0110006fc5018d4001dfc754ca10004fe7118d420e5fe72d0e50006fe53984430057e7394650007dd740c630006fd7098e21005ff7454631005fc7654d40007ec3288710006fd760c610006ff43983310077d43545500477f5294330006fd7098442006fc71583430067f7558031005fe760c910006fc53986400167c53d9510006fc63d0110006fc6418951006fd654c8100c5fe728c910005fd74d8950006ec6318910006de6308410006fe6198043005fe73189500d7ee4254320006de7298c10004ff760c6200157e7590510006be6310640004ed7218151004fc735865001dfe758ca10005fd7494f10007dc6354f100c7fa7010910006dc7118d42004fc7358a50005fe718c9100a6fd76c8010006fd7418530005fe748ca100057e7494e500077e7590710006fc6308510007be7359010006fd6454320005fd7090d100c7de324c9100bf7e750cb10006ff7650810007dd5390730004fd7018d54007be7010e41006fc6308550007bf42cc5400877f5254641005fd700c740006fd4098443005fe7610951005fe7650f10005fd7310810007fb32c42100adfe728c610005bc7350441005fe7094f42007bc64d0910004fd70191520077c32945510aefd7608610005fd72d8d10004fc76487300077c4354a50007dd65cc730004fc73588100077c4394650007de7258c10007be4310550007bc4310510006ff435843001dfe75d0e10004fd7018d21007bd6410e50006ed628c410006fc4298253007be7259010006fd43980100a5ff7408410007f94048210007bc4310a100c6fe3258221007bf4290610007ec3288650006cf63d89100af7e7598a10005fd7290410007dd644c730005fe7690950007df6310d100eeff64544210df7d750ca510057d75d8730006bf64d8d100057d75185200067c63941500477c5354730005fd7690a50004fe7690550007ee4294120005fd744c01000dfe750c410005ff7650c10004fe7199253005bf744c8100c7df328c910005fd76d0a10025fc75d9310007be4354540006fe7158231006fc42d85500e77e750ca50006fd43d8151004fe7398041005bf744c951005fe74d8f100bff62108710005f970cc730006ff7158232005ff7348010006fd65cc810006fc4358031007ee4248310006ff654c910007ed6250810007ed73588100c5fe720c5100077e3294150007f4714c310004fe7695330005fc744ca100ef7f5254421025fc7510f10007ef3208510006fe7610f10004fc764c910007bf42d03100063d6559010005fe7610d51005fe73d9110006dc6350110005fe7118d20007bd42c
  | 30 => 0xe3294551007f55110431006ed64588100c5fc740c910007f44394710006fd651873004f7c6594540005f970104100d5ff740c950007be6450810005fd7498e10006fc5198e41007f932440100c5fe720c910006de7018d42004fd760c650007be4350d10004be7499110004be74181210ef7d520c951005fd7490810006ff7458231005fc7150d510065f65d8d1008f7c500c950006ff648c510007f4410c410025fc75d8f100077e7590610007dc638c950005fc7150c1006f7c530c6500077c6590d10004fd7608410004fc7358221004ff764c0100077e54cca500067e72d9510007fb43c41100bdfc7250310005fe71d0a51004fc7358241007ef4290810006fc6318951015fe7550110005fd70d0d51006ff71d8132007f9700c710007dc630c950005ff74ccb10004fd7019332007de5358730005ff7690e500277e6594f10005fe7390b100c5fe72d0110006fd65d90310f7de750c430005fe7394740007de7390631006bd545804100e7c5359410004fd7098432005f9708c410006fc7318520006de7518d100a7ee4210810005fe748c710006fc43982510077e5310d51005ff72543100aff621086100473f549533009f7c5190d510bdfc758cb100067d7598443004f47159520007bd4310f10005fd70d0c10007df430c950004fc7650831006be7619110005fd7610e50006fd43d9521005fd7394710005f97010f30007ed7398810007bf72990100e5ff760ca50007fb3244010005cc7350920005fe76d0951007bf42d0210004fe76d0d1001dfc7510e10007ef420c9100d5fe7218d50005fe7390a50005bc744c9100277c5455310006fc610c540005ec7250d100bdfe72d0f100077e548c9510bdff7308710004fd7610e10006fe7610d10005fe71109500dfbe740ca51007ee4248210005fd7310510006fe4298430005fe710c910007bd4250130007bd64d0a100967c6590910005ff76d08100e6fc62941400077e540c951007ed73d8910005fc7359210004fe7398251006fd65588310c7ec420c910007be4390b10007f54354710007bf6450d10007f651087100c77d75c8110006dd7018d10006dd7518d42006f4610c520005fe7190910007bd73d9110007dc430c951006fe64587300e77d7590a5010efc21d8152004fc71580420057d75087100edfe7210951006fd5498730007bf4250110005fe71d0330006ff7518520006de7418d10005fe73d8b10004ff760c650005fd7448010004ff7650730005fd7494530004fd7019031004de76cc530005fd7488550007f543c4010007be4390a50007ed4248310006ff32580310adff760ca10007df644c730006ff535803104f7c6554d4001d7e758c610006fc545803108f7f510ca51007f932c4210005fd74d8910007be6490810007de4310d10006ff7158032005fd7488610
  | 31 => 0x910007ef7250d10005fd7010e510377c5394320004fe7690130005fc7348110004dc7359510006fc7498730005df7350950006fe7358041007fa43840100056d750c9200eefd760c951007ed7498810005ff7350110005ed76c86210077d3294650007f43254510006ff65d0c10006fd768c410006de634c8100767c65cc540006fc62587300adff73086100067c6494150004ff7654730006ff7098442006fc6418910006ff6454520007ed4210810007ef4250810006be7199230006fe6498a10006bf5059321007be7110d40006fe6394441005fd7610a10006bc5359010006fd43d8550006fe5358241007be4390a100aefc3298221007f4324401006d7e7590431006fc5258331006ff650cb10006fe71d8143006fc6298730005fc7650910004fc7650d51005ff7448010007be4310710004fc7158843006fd65d0f10005fd7010810006fe61887300bdfe7294710006fd75582210c5fe7290d100077f3294650006bd4258041007be7219110006fe4318520004fe7118d40007dd634c810005fe7110f30005dc7354330006ef6290510007df63cc9100c7f6710c9100ef7d528c951005fd7650c10005fd7010951007bf64d0951005fc748c410005fe74087100e7ee4294320004ff7058843005ec7354a21006fe6194730006be6490730006fe5498730005f9700c910006fd42984300077f7550110006ee635881003d7c75500300befc32d81210adfc758ca10007bc6450d10006dc63cc110006ff2198f400067d6599010006ff5318d10006de63cc810007bd6410c10005ff7488510006fe62987300067f650c5400067f65d8910006fe3118542007ef324c910015fe754c110006fd7418532004fd7608650005fd7690e50005f671c83100d5fe7210d50005fd700c950004be74d9431007be6410e10007ed4248210005de7390730005ff7050d10006fd3258031007ec3288610005fe7690d51006df7418d100877c54d91510077c658c540006dc5498c10006df5398c10006ee6398810006fd7598632007be431065006f7f5218d51007dc438c810005fd73d0310006ff4258430004fd768ca10006fc3298254007f97019310006fe7198e4106d7e75d9031006fc5418d100057f7558043006fe7518d410a77d7508410007f53294710006dc5198c10025fc7548310006fd4398331007f432c4210007f671d8f10007de7218d10005be7494540006ef620855001dfe754ca10026fc5398410015fc75cc910007ed4254320007dd63cc810005fe73c8110006fd7598730004fd7019131006fe4018532006fc4258430005fd764c810006fc6458031005fe7418b10005bd740c950005fc7690d50007f671cc310005fc7150a51007bf4390c10007bc6490950006ff4358251005fd7498a51007ec3254120007bd42541400af7e750ca100077
  | 32 => 0x8e7c5018d520077e53cc9510077e6550810006fe4358221006fc7650910006ff3298251007f73294710006fe4358620005fd72d93100277f5354b10006fe61543400ffde65cc730006fd4018532006fc2198f400befe32d8121004fe768c950007be53d05400767c5098e51007ec32941200067d73d95100a7ec7498810007be4310951007bf6410950006ff7098443006bc6450110005bd740ca50007dc73508100a7dd320c8100eeff6454720005fd7690e100077d654c810004fc7359710006ff53d81410157c7550110015fe75cc910006fe7018532006fc5298e10006ff42582510c77d750c910004fe76c8110004fe7610d51006fd7598720005ff7388410005f4714c810006fe42594300adfe72d0e10007ed620c8100077e6590810005fd7494710007be4310810006ff65d93100a5ff74c8010005de7388730007bd4294140005ff7690e10007bd5410430006fd7610c10005fd70cc9100077d75906310e5ff740ca50007df430cb10005fe7110b10007f97088410006fc5298730007bd4250230007df630c950006fd7558241006dd6390410006fd5358031007fb42c4110005fd7690810005fd70d0a510077e758c510006fc7518540006fc4258251007bd420c740007ed42943200077e4394150006fd6494320005fd7398810004fd7099031006fd7358241006ef6208510006fd76906100e7ee6290a50006fd4018520006fc7018543006dc7418d10006bc435824108f7c530ca50005fc74cc810004ff7650c10005fc76d0910006fd7118d40006fd5458031005fd76d0431007f64110710004ff7650b30007f842c4110007bc4390810005fc76cc910004fe7690730006ff6494730005fe73d0950006de7118d420067d72d9510005dc7350a51004fd76d0e10006ff42d855003e7c5018d5004f7c5454540005ff724c110007df430ca50004fd7018d420d6fc62543100077d65cc8100c5ff73c81100a7df320c810005ff74cca100eefc6354421005fd74c83100a7ee620c810004fe73d94100c5fc7590910006fd7598432006bd7610e410a5fc7308410004fc71580430c6fe7610910005fc7159730007bf64d0d50005f9700c730005fd7418d51006fd5298730006fe4259431007ef6290910005fe7110a50006dd7118d42006ff764c910006fd7098632006dc63d0d100adfc7250210007f632c42100a5fe7210410007f9708c710006fc5498f100efec620c951006ff7650d100efec6290951007bf420c540006fd6590f31005fe7395310007df634c9100257e75d8f10006ff5398f10005fe7390a10005fd7399210007bd4310e10007f4714ca10005fe748c610025fe7590f10004ed72991210dfee4294421005fd73d0b10006fd76d0210006fe638c610007fb304c010006fd6494730006fd644c210007ec4318910015fe75d
  | 33 => 0x80400320001b3000c0c2000002807812a0d101d000422600400480dc0140230158004b5000200800f8000002000803800a00200b8044000001000002404801700182b408e010007007c02a03800000000140000038054000000002007005e0040010000008000003000000001000000ec01005d000801000202f001066c01401c0700000000005003804000401f0000000010000009801806801e08f808803400800080000020bc002000c01e0000bf000c0020150068058072001007000012401516d800000000200309d400000d02a800002c096002800002e01600580e40000020008010014042091808402400f00980401600080de808806e0181be88f0000003020000805001201c817c03607706e8001f2e017000012c03a000008804400000a002000000000b00081e8054002005814406226500b800002000500000c430e00100e80503ba0c70be0bd8002004000000c0561292fa800000002d000808401600401703bc06010825c80942ac007018803800a0de00000300060030058210008054007000400804100000cc0340040000008000000017000000008e00007d0012003008002c18a11c0448fac08604f03f81087900000a9802001c00301a8810f16001026000404606601d0044000009001003804a002001806800c022103007804806a0b38008080001000002802c01100000500041c500c801400000000b004802404b14b808800000f00000d000a023015812c0040a402b8020006000005000c00801700502a0012001002801c0000c200600000040540180000000002018016406a000000800006e04b00402e4004003005801001e039035804800a0190750f6c000004005fc7150830007ef6250910005fd74d8d51006fc7158043006ed6290630007f743945100067f6510d10005ff704c950004fe7610951006ff658cb10006fe5458031007bd4290410007bc744cb10007ee7358810006be6498c10004fe76d0f10005ff7250c10004be7418c100875f5394e41005bd740cb100077e544ca50006fd7688610007ec32483100bfee42c8310006fe42181510057d7590730025fe75cc310006fe5318520006de7598c10006fd65508310867c5098654005fd748c951007ed42c8310006fc6310810004fd7018d51005ec7354920004df764c030007bc64d0b100e5fe7210e50007be4054e41004bc7458620007f63244010007bf43d091006e7c650c510007ee6250a50007be4310610005fd748c810015fc7590d100d6fc625413006e7c54594310bdff740cb100aefe32982210c7ec7418910005fe71d0830007f44384110005fc7454f10007bd4250310004fe7694540007ed4294421005fd740c951006bf7659010004fe760c950006ff6590e10005fd740c810006bd5498740005fe7408610006fe4318121006fd53d8142
  | 34 => 0x12028003000200200c00300020010008004022000000057c0023800010018094000005000400235a0000abc01e84b004004c24000705d005c0540e805f8024188019034003400009a0038018114000006805c00200012707e000600c0118000000028315009c00c00000680a004a00000180000140000021efd1720d8000802c00600c002151c002015002802001a18e005000402413c00080300aa00600001f804201d00100140006c602480000100ee00f800004a193002837405e000000a4ec46c01c0018354000007002801882e000002009806c00000280d00040b911f825c18003e00700400d800000780000e80050120034002011015804804402200b803401409d00b00080000e900100440480060061b18002129009820c2ce00f00481201fe010007010400600700300380180000440018006233001000c004000022805801600026a001001000602c816400200701c000c00000c00180842cc0060178004008009004000c00656300b8050000017002802407400121c801003e00a023805461e01c1528010000015006003009c00f01a809878c0010020008010005201008c006018002818009800300000c800201d00d0018002000000002400200c571803400e0020048004148065002908c00600600380801aa3a5008824800000c000800800400035d8004016047001000810c03e06e800000801b02d869c00001a019804800006000e8010020000009803c0000000570034c4e0040028028000003001000000001e005001c076043064006400000d146800426600e00400941ee004000800c09009500781bc00670801e00000e8003003001800800b01080c400001f00000f806804b0090018000000000800400003300e80040000050158010014002006056001400900c000001800202480e004e001002805000403234b01c401200304280e001a0000000020fa802000100dc04400504680ac02c00d13b800000200300e000000a1042b60008154015006000800600001280a801883d00c009c0160000018bd824a00d007000400400100101783ea00600a812004c01f000000420600204b8028002000001014400000001786f00020000018004126000006808829402c0b9895c05c015004800800603101204740280000009aa0000004009803001e01500c80340c808119100e800600000502705c201a2020014030014001000400200a0010000004008001801c02c000001801c1b600001400dc00a00001200f00ee350006008001a000012001403600500000a0066005027806c00e000009805801040f0000000044095006000802356800080101d80020010000016007008000c02a02d00083b40360190028bcc012005000000001e000000000800c00600d008c358000000801400604300780180160120ad0098080000003
  | 35 => 0x402200200201fc00a00000380300080000000038000046004805401e00605f001c0142d400502f4008081000012c082456006000800076f000800001200001980bc01003d0478040006009003839001a00507d00f00240040018000000000000000002200500a800001c01b0008004002000007802800e07e00600f0086000004058002200306407b006034f005826c00402b005001800601e002800000412901b80000200c10040374012018025800004e0b3011813ca400020008048000015016000000000e00a000401a01000488a8006006006801804a00100b80cc0c6000009803c13e015000004002205d00080009ae0010090114008008003836c0000011c703380040f0025806c000004000802400635401780cc00002802a8010000061002800000200a000022c08c2eb000028c02c04e000021c0060290208000078000009000c30e0b8001000000002000300200120150018134054003000128c000005039801c01002401081c0000015393812c16401f01b8074090001001000800607a0028020bae0c3006000406e031002000001e05c00000480ca62407f801407400401b0004006003003011400025300083100000000008000000001012801400a00a000000402a05e02e001c018002007875c00007d47680c00d2000027800000e03101a8000004059001878000e00400a0000086000000801007602d02ea3b407e4aa0fb800c03a000006813400400603f802800205a000801000c001000000c0020020168020024004019007c00e0c7002836000200300400c40e009e117005c00800c007800001a01201a82e003a00500b0004000005000000000a25f002817401400700000000ba0b5000003401402f000800000600400180081f2000000000001c05a03f801c01209d00180e004a097002032499228a015800c01000502581c000000e024000400802606a000003203605b8000008060002000c05600005402dc00c0000050004142000002003c00600002e8464000001014002000408d03b80182ce03907a80002a602700000f00000020128de803400017c80b400006f0000044000128002800400000400f8000016000047002c002000000006414000100000d009a1d401a003400a006000000c006091017801000608400100a1d7a01a00e00000b201910600800c6005007802406400600680040ba0160000030048097000000c05601d00080880040120108558000001001002001c0162fb800000000606880cc00001500781b80a401707c814c024020001002c01a00b011002800603a005007c2700120030c88000003011009002208400380f801e01900a00000089d601c80f8006002014800803a032001001004c01218080001d000612c8b2c12403200380900160180aa811c07a00200f8040000008028000000
  | 36 => 0x280001fe7d6008000003a0e6000800c00203800500e40c011c061004401800100a012801200002094b001600e2aa823404800000b820c0220160000a7c00e00000000140b800f04b812400802a03780f400c15003302000180071b2800c84800c02f0090002002007002c01004f03b000004c001009046c07c2f20000040062000104801c01c071000000401800100e000803400c003003403402902d0094016003000001400605900282a401008a031834c00000806c0040002003034000400200e0000208000018000000000404e00b004000811202100000320000020000000005038018c02c003007800c014000003004804400e04400600080110170008000006001814001801000a00400101b000600001ac0b101100140a4000012802417a02d00000e4028016002000800601624c00051e400204400e008400300580080020180068000000000000006004400000e8054002000008805804e00d00081108b600007802000960301b18000022002002807400400400b804c74a0000030ab401e01d02500a88000000000000042007001002017000111a000401207b146001c03404c00d851000404a00000180020990001868000000002014801200100213180041080028000096001003963809202d00
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xbd78350b10840019dca53b662900031fd9671109100075721ec4a022000e3d65d0b4004001b3ce93186408002976177118d42004f643a84a864000e3f51950615000197c81388c8a90034fd96740c9100063fc2ae13246200cbc761924244001b6c8638a86080029f616735822100677b9ac4a002000cdc839d843440018faca39c42080029f60b73594100066f418e2b0084008fe869c643440019b8ea31a64880038f197648c910004bfc3a8528ca000c7c751c56010c017a906a1420880027d205740ca510056f426a431a2000b9c8350841540014ff0a980c2a10027720d74480100056ec18a531c20009ef825ce6484001938e831a64880031f5d56498730005da40ae532020038fe8794560884018ff0ab80c910803a799263cc8100063ebaee830a4000baf825ce64040013bd0239a84180033b98a71d8b300063f42ce231aa4008ff865d132040012fb0e214a32800337dd163588100063eb2ee8b182000cf77610910040015dd04384c2218034f90375580410071fb2ce43222000e7565d0f10040018faeb398c290003b3e1163588100063e21eeab044200a7e8690a505400197ae9380c6a1002bda04325865000677b2ee4a1e2000a7e859c66390401b6ee9b8a6408003371db7350b100055ec2064b066200add83151600c40167b08194a328002afa1062987300063eba88530e6000e5d7594e61cc0479dce53acc3900036d55071501100057a40aeab00420087e86dd5404c00197cc939cc408002bd20542980100063e39ceb30e6000d3d655d032040019deed9926508002afe0570191320a576412c8b102000a7d8508663104038fceab2864080031f59572990100069fa8ce9b2e6000e5e7598f20040018fd0e3aac018803b3a1d63588100063fbb2cb1902002a7e85d0d61940019beecb22a6188037c6007150c100047e43acaa122018cec329d82144001b68e838a64080023f61f5158032024fac3ca210e2000e3f6510d40440032f90ab866408003ab99143988100076731cc59902000c7f759d560904018fcc6bacc3a0003e3d0f420c91000766194c610820009f980dd031c40395d904b1ac5280023fa1c32986500047f436e0992a200be48250f100400175904a188788003975947258c100053e42ae2b006400eaf8558a411002997e84bb0840800397996638c810025ba42e84a8e2000af98010a600c4019bcea31e4088002b720d6458e5000767c3cc73102017d76215d421c40355dd05b1ec4a80029f61673580410057a40a6530e6000abf844c960944018ff0eb288608002ee21132440100066f430e6a026000a7c845cb65440011fb003b286a88029fe0d72d95100045f43ea2b206400c7e43dd56010c0197acb3a064880039d60475580310065f3b68621a2000ecc7358d62040011fb01388c6a10032f1db6450d10
  | 1 => 0xeca3a264080033b5cf6290510004df43ec89922000d74659c43244001c7aca39cc808002e7e117298c100063fbaa84b0062008fc865d252c40018facb3a660080036b5d3420cb100069eba4a6194a000c7c72595430400173f06b90c8880033798d70108100a677410e2b0484008fc87549600c4019788738ec0a1803379d4630c9100066e310e6a826015dac215d032840019bd0c39a85288038f5956490c100055ec1ea1b222000bad840ca218400197aecb208408002afa1372987300065f390c831a2000eaf64d8a32440013f3003a46208002d7a147298c100047fc3aa6b048200c7e72d9763440096ed0a212a3880c357d4473543300047f43884b286000c7e751ca6110c013df0ea1085080039b9415258021006dcaa2e020e2000c7f855c0614c8015eb0c19620080032fd9170cc9100066ebb2c7a1020008fd8718c42c400197d0838ac019003371db6350d10006dda12e020e2002c7c75d964344001b9ac7b9286080038f99564d0c10004de422e61082000c7f759cd60884018f8a8bb483280032fd97744ca100057743e64b0442159ec825cf4084001f5284a0240880029f614709844200767904e231a84148ff865c232840015ed03a9cc320002f5e0d42945100069fa8ae8194a2008fc875026110c013ed023a661880031f1d66358e10004fcc04e3a1620009ef825cc41c4001cbea23acc6080032fe1170984430067ab28e29902000db7649c443440011fb0fb288788002bbe0143d89100055ec16a6b202000d5d759ce418c4013bd0db9a8488003b31886310910167c6210861922000abf865084104001cdc85b2e40880031fdd671580310065ebb4c9a182000adc8358a3150001b76c8b806488003b394863c8110005d6422641962000add8314a61cc0011fd0f904c22186abe60275580210053ec284330e8000abe849ca61cc0019b8c7b8284880039bd957318910006daa14e3a062000ed88054d600c4019ed033b085880038f90b655091000577c32849002000cde635c3320400157f0ca148318062bba08315822100556c16a2b206400c7e72596310400197aecb208608002b760e51580310055ec20653008200c7d659d120040015bd0638ac0210039bc8575185200072e32ec6a122000e9c87d9363440018fac9baac11089adda1432c4010004dfc3a862182000e3c6450d51540011f90cb8684a88533ba087158032006ceb9887a062000aed86d0e620400137908b9a400800379cc8714831000676b12e01902000e6f5154a61c80019b8edb9a840800277a1873509100a57b40ee13088400cde7650c434400173906a14a1a00035d50c71549510059e4226528aa200c7f751c9600c4018fcc5baac021803a7190638c9100074f326e53182000cbd7499262944019f70cb848208002eb61032d8520004dec388728c8200
  | 2 => 0x66490630005cec1cc821c2000e3d65dc964040014ff0ab8ac02180379d8a710c9100073632ce83122000af9800ca600c4018faeb3a4c39800337dcc63543100ee9ea92e8192a200e756550b1004001d9ec621ec4880023fa1874cc9100063eb2ae59802017d6c625d432c400197ac8b808798002b7a007018d42005ce422e53182000c7f75991600c4072f90aba2610800b1f995709442100756b22c4a142000ade82150634400197e84b84c3a18023f21d43d81520063e3a8e6b0082009de83dc9518c4013eb0038a65080023f61a74480100056e41a84b0662008fc865d12044001978e8b22c6080033b61f624c11000676b2ee4a1c2000db4439c740c40014fd0a3a4c398003379c8638c5100053f430eaa022000aed82d45600c8015bd05b20c6880027761b7350810005cf41ee5b222000cbc7650951500013d906b94a3900023f61a71d0e50005ce41a8420862008ff865cc41040014fd0a194c398003a75cc43185400047f4388530ca000d5d759ce414c0359dd0c39286a80033dddb424401000772c18c290a4000dd5631c5420400197d0e21ac1208037c945701071000676196e0b1682009dc835c9404c0018fd0abb483280023f21d654c9100055fc2c8730e8000acf825d063440016b906a14a3280038fd9443909100a676192ec1082000c7e325d4614800197ac9388c9980033da18714c1100c6f5212e02122000d5e759ce61cc001d38c7a1680880033d1857008550005e641a84a8e4000c7f759856010c018faeba14c3980039d20575185200047ec3885304a200ecc8718c62440014fd0c32a86880031fd9574cc11000676bb2859002000c7d625d764c40019f3003b287880023f61c4398730006ae98aeb20e6002a7c854c9619402f8fac4ba8c588052bb20943181210153f42886b04a200e6c750c9608840157b09b2ac0188039b0837558221006cfa88e6a168000e5f65d8e3244001abaca39a84080026f6107358a510063eba8e530e8000daf505d032480313eb0f18c42880023fa047650b300063fb2ae43222000ced629c432040014ff0aa02c110802b760f6518f100065e422e030a8600c7e72d9740440014fb0a312c018803675d3430c9500057a43264a8a2000ecf63d8942440013bd07ba442080735b6147250e500063f322ea1962000a7c855c263904019b90ea9ac018802afe1943508100c6d6312e819220009f9801d221040019d8c53888688002be60271580430071ebacc92082000add80d506344001cbecba1a8688002bb209435865000756aa2c52082000c7c76d96434400157d0c21c82a80031fdd8754c2100057dc02873066200c7f72dd56010401cbacb29ac018802ede11329471013ebc3ae609802000add80dd0634400157f08994c3980035da1671d0110004ee43cc6a1020008fd87994600c40197
  | 3 => 0x4a0220009de83dc9514c0018feea322c0188039b595628c81000756b2286b102000e75658c910040391fd0e282c1210031fd95744c910025bb4288728e2000cbc74185505000157b08194c3a0002b72096498c100047fc3a65b0aa0009be861d1324402b1fd0d38e60900033da1a71d01100065ebb48621020009bd87d903244001cbccab1884080573da1a71c81100ee77430e4a1aa200aed82d46610c801978ec21aa2a0003a7e1c6418d10006bc42ae01882000cbd645ca3104001ceaca21e20080023fe1d31d81420047f43c63b028400aad840c960884016bf06a14a0a80627b209740c9100063f42ce3b028600cbe76d084144001c7ecba108288003675cc4310510006e7a18e4a1a2000d3e651d13204001be101388648800277a0f72906310066e418eca1220008fe8718961cc001aeaeb20c63880039b1886590910004df43ac89902000a7f855026110c015ed02294c2180038fd9673d9110004f6c36e4a182000ee78154a61c8001cdea2a92c0108036de05740ca100066eb80e031a8400af48150d610c0058fccab84a218803ab19143189100055e4328420a2000ece8458d62040015ed023aac010812dda1642547100263f3aecbb262014ced870c86148077ae86438aa4a88031fdd965d0c10006d7b26e4a1a2000ecf201c46350801d9cc6b1484080039d5947150c100a772c086430a4000aec865092044001cdcebb1482988023fa1c6354520006b6328e4a1a2018cec76d8a32440018f8ea39ac110802f5e0d4244010006e7b9ac4a102000cec76dc94344001b38c839a84a8802af61e5498740005ce41a85282800287d87d942144001d9ae6190c29006a6f21d43509500055f424eb3086400e3d65d0940040015bd0229cc6080031fe1570190310066e390c6a1a2000cbf761d13204063af0ca382a398002e720d42d01100065eb2ee89902000adf805d0634400157f0ca1886080038fd9743509100063eb2ce720820009ef825cf40c4001cdecaa1ec4880032fe13764c810007363aec49822000abc8650f424400197ecaba064880036e50970107100047ec3886302a2008fe87109610c0019eaca38a85080035b9537250e500063e2a2ec194a000cde861cd428400157d08192c1288031f2157018d5100757ba2c8b102000e3e53d45640c8015f3002a2c0188039b54552987200ac7e43ac49842000cbe861d13244001be30038a840800237a1c63509100047ec06ec994a200add84dd96304001ced0b30e63980023fa1f53984300065e432e81922000c9d7498c32040016bb0bb226398002b76077018d420047fc32e89942000e5d65dc96304001be30038a4188003379d66390c100056ec18ca31e2000c7c539d832544013e902b8086880033760e71d81420065f3b0c82122000c7f758c9600c4018feeb312c0188038f5d
  | 4 => 0x254401abae6bac831880397d9474d8d100047f430e29922000e5c630ca50540013bf0ea1887080036dd087150110004fa40ae99842000cdd7398c218400197cedb2664880023fa18748c5100a67cc00e2b008400c7e42dd56010c015bb062a4c398003371d8634c910026bb3aca210e2000dcc431c943940019f6ed19220080033754d7018d210074e31e84a0220008fc8754c6150801d9884ba8c6a10031f14c76545400071f32ac82182000e3f651c864440019d8ec31684880035ee15700c5200066e31ae118aa000cde635c0320400173906b92c808003379d954cc5300066fc1ae030a6400d6c20dd56088401b390039a85a00033e8817018543004efc1aeca142000c7f761d540040018feed32a84080573b9da42885100074fc3ec9b1a201ccec325d84294001cdeebb1280880031f9d463c83100066fb1ae018a4000baf845cd62040011fb0e2a4c78805ebda0470984420071eb2c87a002000e3f7595160904014fb0a31884080032fd96740ca10006ba3a8e2a022000cde535c06348401d3ec9b1a86880038f5954350810006eca9ae11882000e7565dc5430400157b08312cb980037694d708c4100066fc3aa730e60008fd861cd42944018fceb3184308002fc6024344010006cfa80e6a1082009fb865c042840015bf06a16c2a80029f61641580410063f42ce331ca000b3d859c4439040117f0eb20c8188038f1d54258041004de422e79022002a7e850c96194001c7ecba1886880039d614610c5200056ec00e231a8400ade83d9363c4001978edb2686880833b1c875580210053ec2ec7b162000ecd8758d62040015bf06a14c2180633b98970887300047ec34e3a14a000bcc8350a21840015e90ca1c2088003731cc62509100065eba2e630a80009de83dca414c0019df04b80c2a1803ab98a6410810006ce39a86a162000c7f655c2414c00197eeda1280080029fa167118d400074fb24e5b1a2000e9d6458e3204001b7086b8083880023f61e63108100073c900eab008200e9c645c863440019eeec9922008003375d974cc230006bbc28e2a12a200e3e409d661d00015bb062a4c708002bba0473588100063ebb2ca9902000c7d87d94324400197f08b84c3218023f2197210f100066fbb2c72182000cf7760c910040011fb0e190c0a8803b318c62d091000773990c210aa000e9f63d9143540018fd0a38ac1218035e9c2758c7100053f43687282a000bcc8350821840018fb0a38ac119002af6103218550005dbc22658802000cbe841c560108011fd0d38e8688003ab60864189100055ec3087a002014eae840c8614800137d093a264080023fe1970d0c100047f430e2a026000af48154c61500015b906b84c2218031f5d43298730176cf190e89942000abd840826110c015bf06a14c328002be60021580410066fb1ee
  | 5 => 0x8802de602548ca500056ec1882b006214cee421c560108019dca4bb442180027d20570d09100063eb2ce32182000ecd7458d6204001b38e9b1a648800337dd96350c100063fc2ae03224200e5e6598f32040018faecb2a84080567b20973992100066fb9ce7b028400ade8219063440015bb06288c7880023f61a744c8100066fbb6ca98e6000ecd87d8f624400157b08192ca188031f59573884100072f32ee53182000ed553984310c00137b09b9c42880023fa1c32987400047fc3aca1962000e6f7554960084019bacbb9a85880031f5d532987300063e3aee2b008600a7e8619442440014fb0a10cc7a00037a0c970884100a57cc00e630a4004d767594431c400197ec8b9ec4880033798e710c8100069f21aeb30e80008fd870ca6010401c7e84b2c84080027721c63509100067b430e2a022000d5c7394d42940019bb0e31884880039b99543988100072f31ceb18e2002c7e75d9732440017d704a1e2108002bee017258031024bf42cec21e2000c7e659ce6204001cd8cba18c4880026f61e43109510065f3b6c921a2000d6e75d8832440011fb0e212c018802b7e0d75582410055f426eb30e4000e3d6550c43040019f70cb8082080036e55170907100057b40c853086000c7d851c560108015bd07b246388002b7a1c6354f100047f43ea530e6000a7d82dd16504001cbaa6a94c398003ab99262d08100053ec28e13088600cf5871873148001bce6538e40880031f5d473984430057ac08a031a80008fc8754a61cc001b58caba64290003379db630c9100063fb16eaa026000aef8250e600c401aeca838a86a88039bd9432481100071fb2ae5b222000c7d659cf20040011f90cba264880065fa16744c0100055ac08a0b2064008ff865c33294401cbecaa188688002b7e0d4258031004be41ae528aa2008fe87d9151cc00157d073b0c8880023f61a71d08300056fc38a53182000aec8350960884019beca39a848800337e1276cc5300063e3a6cb1922000ece63d0d62040011fb0d39a40080023f61e63104100074eba2ea31a8400e6f6550b20440011fb0db826528812dda146494710004fa40ae4a046000e9c8418c41440018facaba064080023f61f21580430047f438eca102000ecc63189324400157d08194c3980039b8c9650c8100056ec184330e6000abd840c965cc0019d8ec316648800337dd9654c7300056ec1ea530e6000cdf83dd9320400197ec9b9c4288003b3188630c910005db4206528e2000c7d659d221040014ff04ba6ca880023f21d5318520004dfc22e610c2000adf8654e61cc001cbe64b2c6408003675d153180310056f428e831a2000b5c83509515400197ae930ca3a0003b520553987300063f42ce231aa000c7f655c841440015bf06a10c0a88023f61c42d94310047f43864b0e6000d5c73d0d5
  | 6 => 0x47f43e42b008600ed98018d53c40015b906a10c2a8003a750d7018d420065e3b486a1a2000b5e851c8634400157b01a9ec888056eb2094350a100047fc3ac918c2000bcc8250c4344001b5ae9b1064a880357d9773509100066eb9cc328e6000e5d6594e61cc0019e8c438aa1880029f61671d81420056ec1e40b006200cde7498e31040018feec3aa8118002be60371d8132005ce41a8520e2018aec8250d61880018fee8b2c64080031f9db6510d100065e432e8192a000cf77690d10040058fccab84a2208031f5947448010006d7326e4a1820009f9809c443040018fecaba062880071f9d565d08100065f21ae130e86008ff875056010c01d5d06b22c4080bf671087350b1000736b288599020009f9801d031040013ed023a66488002b7a0f644c3100057dc02653066200e5d651ca63040019f70cb8462080031f9d4638c71000736b2ce73102000c7d659d263040011fb0e216cb988038f54654582410263e3aacaa1e2000c7c76d9432440019b8c738c8688003379d063885100055ec3086a002000cbc76dd132840018facab9c82080034fd41740c9510066eb98c7a062000c7f65dc9404c00173906b90c8880034fd96748c540006f2396e2a1c2000dcd535cb61cc0011fb0fb2864080031fdcf65c81100066eba8e231a8400cdd861cd4244001d3ca831e80880032fa11760c8100053ec24e5b2a2000c7d659c64204001cdaeab148318002bbe0943d81510047e43a6030a8400eba8010d60904013db0e194a2900031fe157018d410056f408a53182000cdd84dd9300c0319d904b84c219002bd20540185200065eb2ce819020008fd861d132840014ff0eb2864080029f2157098432024bf42ee918e2000abf8650d4284001d58c432084880039bd9762109100047fc3a83b0264009f4815cb30040013e902b968008002b7a177218d100047f408e6b108000e3c54596640c4038fceab2886080023f21d31d81420057a43284a8e2001a7c8550c605440137d0fa1a84a88031f6167199120004fa40ae89042000adf8350961cc0078fee23aac018803979d76390510006bbba8e29862000cdd311d942cc00179d05ba6c688003abd9173d89101b72fa88c6192a000a7d859c7604c8014fb0b188c290003a718e43d01100063ebac8730e6000c7d765973204001bc8e438a8708003971435218d100ddd641287a14a200a7d851c560108378fd0abb065288035d61671cc110005ce41a84a0220009bd87990320400157b0d29a84208031f5d475580320066eb2ee6a1220008fd8714a6384001aec8638aa4a8802af60271191320072f32ac7a1020009ef825d130040018fecab96c688002b320d4258221005d7c22e73102000cef201cd62104319d864b84c31906ebda0475984320063fb16eaa062000d9f801cd42d00011fd0e212cb9
  | 7 => 0xae5219320440019b8c738c8488003379d97418d10025af428c729e2000e5f855c063508011fd023b2a5980125f21574483100a5764126030a4000c7d7518c62c40018f90bbb280080027be0973990100066f39a61b028400cdd651cd42cc001eab0b30e63980026fa1c744c9100074fb26c62122000abd8510c61500011fd0e212c3298031fd967410910005dac20658842000adf815d463508013f30138e6588003370c27118d520066ebb2e818c6000cdf635d12044001a78a6ba06528003371cf53582410056f430861922001c7c709d661cc0011f90cba064a88b36790873509100072fb2ec7992201cc7f525d82194001cd8ca31284880027d2057010b10006dcaa2e02082000adc845ca6304001bd284b8084880031f59574cc8100065e3b6e8996200497e859d942c4001cbea3a94c6080039d6167118f100a676c30e4a182000eaf64d8b32440015eb02284c2190023fe1d4218151015bb42e86a8a2000d9c73d0d42940313d904b9882880036d99071508100263f3aeca31e2000a7e82dcd65040015bb0e2a0c6880031f5da65d0c100053f4284330e6000e3f65dd132440018fecb39c42880736bc81740ca500071eba8c81922000abe829d864440018facbb8286080026fa1e4054e410071eb2a852082000abf8650c438400137f08b9a41880031f5957298c100069e32ee89922000c7f759cd6010c018fae4bacc2218623f61a7110a100055fc2264b0ca01ddac825d0325440197aed32684080032b5d3620cb100071eb2e87a1020008fe87d91600c4011fb0fa92c19880397596638c8100071fb2c8620a2004b76858c951c40319dc853b04288002ee61032840100065f3b48620a2000adc835c061508019bae731884080031f594744c0100063fb2ae810a2000cbe74d9231440019d904b80c299003a72096458c100047e432e5a022000c7d659cc42040295d904a98c2900037998871508100047f434eca122000eac731906244001d98c7218c488003ab98a640c8100063e43acb2102000c5e7598e41040014ff0fb2864880633b2097098642006d732ae81944200d75759c763c40014fb0a38ac1a18036b145740c92000767214c61082000cd4639c4434400197ac8b8086188032f5d06418951005db4206588020008ff87549600c4019beec39a8508003ab992624c8100066c31ae0192201397e8795143544014fb0bb98c290003b3dd26398810006f5212e018a4000c7f759c560104019f2e0380c299003ab59162108100053ec2e413088600cbf765934204001d9cc72144208003a719063cc9100071eb2ac92102000cdd311d952cc0012fd0e192a2a80023fa1c52987300063ec2aec1082000e3d6590d40040015bf0fa80c688052eb20943d08100063e3b0caa122000ee642184314800157908994c128802b7e017118d420
  | 8 => 0x4b9883080023f61e61d03300056f424ec31a2000a7f855d84384001cdacba1664080031fdd4625803100736316cb1922000c75651c54204001d3c82b80c6a100277a0f7290630007363ac84b044200e3e7599032040015db0ca1ac4080038f59443904100066e3a0c69822000cdc63dc143440015eb02282c019003a71097018d420063fb2ae520a6004d767594441c40015bf02b80c6a1002bb6085158021004fd438858822000cee7650a21440017d704a1a20080031f21570185320047e432e79022000cbd64dcd20040011fd0f20ac1108029fe157018543006bc42ae02186000de6521c520440096ed0b21aa3880027e6007150b100c676192e13088400b9c8350b40cc0011f90ea1ac310003a7d9172d8d100072ea8ca6b006200cec321c5620c0019bcea31e8488002b760c5218f100056f408e031a8400a7d839d365440011fb0f318852800277e0d765081000737314ca2102000e5c651d06344001b5ac839286080031fdc872594100071fb2ce63222000e3e845d661d000157b0c21c8408002ed2113284110006ce41ae8194a200c7f75cc9600c401d9d0f31cc408002af61032594400063ec28e2b108000daf74d8932440015790ca1a858808fabc835159032006bda82e121ca000bad840c951480018feeb392c020802bb2194318910006db218e2a0220008fe87d913044001c7aca21884080032f5d26498c100065fb22e418a201acec219d832540018feecb2886080039bd9762d09100c676194ec21220008ff865ca518c40179f06ba4c40800337d8f74481100065f3b6c921220009bf845ce62840013eb0038a84a88031f2147654d400071fb2ce5b22201dc7d529d832544015e90ca1ca388003b354d628c410006f2a94e39022000d3f855d032544018fcedb2e84880032f9d3648c7101bf2fa88c721aa000af68114e610c00157d072a0c2a00031fdd675987200047f430e8a962000cef321c5608c8011fd0e196c0a88573da1a710c9100066e3a0c69022000ece5358a31040018ff0ab80c9990036b5d3420ca51006cf320e6a142000c7c759c56010c017e50219620880036d950715011000576c10a330e4000cdd759c463508019b8c6b80629000397d967418d10006ae39886a92a200de7321c53284001c7a84b2884080038f19764cc9100072eb2ac6a182000abc8650f42544011fd033b084a8002bb60850582430047f43ea630a8000cde7518c43440018faed2a06528002ed2054350a510063f3a8e630a4000eaf745086148001c7eca398c8880032fd917218d100053f41ee4b2820009ef825cc64440018fecaba2608800375dcc7150a100065fbb6e89962000cbe76d92324400175904a1887080031f9cd73d9510005d6c20e6b102000c6d65dc9430400197eed21a80080033b1db6250910005774306510aa000e
  | 9 => 0x71580420065fb20e29922000e9d6458f32040019dee9b1462880027d21d43c4010004fa40ae69002000c7e635d421c40019bced21886880032f5d9640c8100057743287b1220008ff865c34294401cdecbb1264880036b20d72d054000766410c790220149ec8750e620400176902a1a8408002b76005218d100bd77416c7b16200097d870ca51544018fcea30c62a0003371ca6350010006ce39e86a122000d5d735d6414c001cdecbb1064880031f5cb658c5400074f3988630a8000be88250f10440018b8ea31a80880033d9c57018f10004fb40ee0a162000e5d859c663040015dd07b1042a80033759473508310075b2a0c218a8000e7575d8661cc001ceacb9922008002f320d429432000736b2ac59902000b75858c621c40011f90ea9ec0a1002afe19425023000737ba864b044200cbe435c26190801998c7b928688002af2194310f100065e3b0c89922000cef761c94344001cdacb39ac4080127d61e518c7100047fc32e120c6200e5f5394d609042b5d904a1cc11080f1f9c275185200063fb2ae118a8000e6c6510c62440018fee6bacc3a00032f5d9648c8100c6d7902e81922000cde321d932440315df08192c1108029f61672580410066e3b0c621220009bd8710e5150001bb6c6b8084880033b0877650831006e6210e6a14a200c7d859c463500019ed023b26588002f92094354510006ceba2a7b0e6000cef825c06150801d5c86b148208003a795063501100065fbb4c92182000cdd539c46350801d58c831684880033d5c471580430066ea98ec9822000cde631c53204001a7ceab2064080035bdd432582210053fc3acb1882000cbe765cc64440014f90ca1aa2a8003a7d90638c910006bb42ce221e6200cbc649cc62440018facb39a40080031fa1f65cc91000736a8aa4b0442008fe87d8961cc00197ac8b808608003a761f64d8d100047e43a653082000bf18090910040018fea43b2a6a00031f21570987430063ec28e2b048600e9d8319063440015bd0231ca6a1003371cd6358a51006dda12e120e2000e9e63d0a4104001b3ce721ca220803a760a6498c100066f298ec9822000abe84d4c6150001c7acb21c8408002afa1032586500063f42ce331c8000eae6490e620400197ceda1482880029fe1570984320056fc1a84b04a2008fd8798c21840013ed03b826488003ab59162d08100067a38ac2b008600bb5840ca51440011b906b80c2a1012dda1762947100071eb2ac9a18201db6e8210d52544018fecb38e868800397e1553987300047ec3cc62122000f3551d9254c40011fd0f204c221802bb2094398331006ceb9887a0420009f681dd33204001cbecba186488002bd20552987300053f430ca1922000ecd7418f62440011ff0eb28c3980031fdd8754c3100071f206cb20a6000c7d42dd56010c013df
  | 10 => 0x9922000a7e859c5600c40167908994a32800337dc67118d42005d6c206510ca03bd76421c55254431dd300192c1108036b1907250d500066fc18eca122000b9c8350951104014fb0b38ac0208aedea1432c41100057b40864b086000dd9535c031cc001cdccb31684080037518e710c9100072e3a8c69822000e3d655914204001a78cb3a064880036720d740c81000cbe42ae1a102000cef65dc943040011fd0e218c2a80023fa1f6550c100057641286b0860008fe861d132c4001d5ac8b106408002be60042982510057b40ea730860008fd87149600c4019bce531c82080023f21d439862000756b22c499020008fe861cd54c40015df0ca1cc408002bbe1d52185200063fb9ee4b282000e5f6518d43440019bd0f31842080030f1d7644c1100056f41884b2e6200abe86d0f42c4001b5c8639286080038f5d664906310069eb28e89902000e3e74d94324400137d0e21aa0a00033bdd3624c1100056ec2ce031a8402b76850c95144001c7ceab2462080039b597324c8100056f41885304a600cdf639c730480019f6ed99220080033d5c471d81430066fb2ee6a142000af481500614c8017590899065080032f5db4310c100073ab28e2a102000cde639c732040011fd0d38c64a80029f6142158031005cec20e431a201ac7c859d832540011fb0f904c22180a5fa17740c5100069e28ae8192a200e5f65dd063440011fb0d39c82080033b0c871588400063eb2ae5218200497e859d943c400197ac8b9a40080026fe1e640c8100066e3b0e6a162000e9c649c8634400157b0939ac1108031fd957250130006dab20e29902000c7e855db20040019b8ec31c64880032f9d0610c5400c57641280b044200c7d65dc13204001d5f06b22c408003e3d0f420cb100057cc346130e6000e9d6498c420400167b0b38886a00031f8cb75582210063e284ec192a000abd80d45640c80197f08b84c2210036b5d3420c810005e641a842102000cde301d942cc0011fd0e192c3a00031fdd562580310062e3acc69802000d78855c22104001d58c43206488002f960841086100073ab2c822082000eac641893244001dcc84b0c42180031f99175c8310004dfc32e81902000a7e861953244001b6aa838a8188002cf61032545500053f428653066200e5c6390e5054001b3d0a39a84208032f5d954906300063fb2ce610a2000c7d759ce61d0001b38a239a84208031f216768c5100a677bb2c52102000cbd645cc41040056e90a992a2880023f61c43582510066ec38c718a8000c7c7598d3004001d5f0fb26c4880032fa1271d81430055ec264130e8000cde76d8f4344001b6902ba06528803579cc329455100677900e6b168000afa80145600c8017a906a1621080033b0ca71d81320074fb26c7a122000bd88350a100400157b0e21cc3a00033b508
  | 11 => 0x500019bae73088398003a79926350e510043ec3ecb18a8001c7c7559632040015bb062a0c7880021f21975905300074e41ac8b182000cdc734c160884018feecb2a8408003375ce63c82100057dc02a6b006200cbc649cf204400197eedba265080065fa1671d0810004dfc22e731020009f4815c343440018fce5b2886880031fd9774cc91000737b2c87b122000c7d7518a61cc0011ff0cb8685988626f61f43d09100047e432e528a60008ff865c042944019dceca104288002f320d42c81100047ec38a431a2000d76859c740c400137d0d3a462a00027d2057310a100055ec20c4b0e6000a7e850c9610c00157d0da1e84880031fdd875580310065f3b6c89922000c7e851c560d0c014fb0a394c398003578c375580310067bb28e2a102000cdd531d9420c4014fb0a314c3980031fe1676905300047f43ec4b006200aef8458d6204001b5ce9b1064880033718f704c9100074fb26c61922000abd8610e42944018fecab848688002af61032986500056ec1ea0b006200cbd845d83204001d9842ba8c6a1002bd20543980100047ec3eca2102000cbe76d9042440019b8ea31a40880026fe117218d10005da40a8621820009bf845cf20440015bd07a94c39800367a047350841004bf43e86a94a000ade831416090c019baed29c6320003671cd4350a50004bec3ca9194a000d9c7350d42840018fb0fb2c86880036ed0970104100056f406e231a841cd3d529d03294001a78a8ba06528003375d94310c10006bbc28e2a1aa200b9c8350a414c4019beeab80c6a1003b3209635881000677bb0e4a1820009f58710e10440014fb0fb2c62880023fe197090c10006e7408e6a124000d79755c363c40019eeed21220080533bdd9628c8100066e3b0e6a1020038fe87945600c4018fcedb2a84880031fe1d75987300066eb9cc620c2000c7d651d162040018fb0fb2c6488002cf61032941500e6d610ae8194a000bb5840c910040315dd0520ac1108523f21d624c010004fac30e29942000cde8798c4104001cbccb29ac0188031f9d662987300057cc0484b006200b6d850ca60884019bce931842080573b0c97610a100076731a841082000abf844ca61940017a906a14a2880031f1c96558c10007673a0c63122000d5e7394c4254401cbecba1c86880038f9d654185400065fbb4c8a182000ecc7458d62040018fecb39886880039b19573189100071eb2e872182000e5d6558c420400157d08194c3280023fa187350b100063ebac8530e6000c7f509d83254401c78c8a1ca0a8002f5e0d4294710004bfc3a6528aa200dad7458832040011f90e992c328002bb61a43988100053ec2ce4b008600adf8350a61cc0018feca3a44288002b7e096458c1000736192cb90020008fc865c6535085ff1884218658800a5fa14748c5100065fb24e3
  | 12 => 0x2a720d42580410055ec2064b006200abd840c961100011fb0fb2462a80027721f63509100063eb2ce73102000d7a755c364c40013790f32264080023fa1a73905500069fa8ae8192a000c7d755c261cc0014fd06322a2a8002e760c6410f100053ec2cec21820008fc8759151cc0013bd0eb1a8408002afa1843909500066f186eca906200e3e65991320402f1ff0d38884080033761276cc5300071f32cc81902000d3e425d66110c01bd484b844208002be602755803100756b2486b102000abd840c86054439a7aa4ba065280039b59543988100063fbb0ea98220009f68710d51440019dce5328c0188037c105700c410006f5992e110e2000c7d655c343040015f30118ac018802b7a037518d42005bac2ce23262022aed8714662040018f8e8b2e400800337a0e71d8142005ce41ae5320201d9bc8750d4254401d6e84b0c8218003a7d917218d100055e41a84b008200cdf76dcd42040013df0e99064880027be09744c8100063fba8e6b044200ecc6218e42440013ed033a240880036b1d0624c9100074eb24c7a102000cdf835c26110c01be4a2b84438800367e147350b400065ebb4e221c8200ade83145600c4315dd05b1ec4880027d2057010f100063eb96eab008200d9d74d0c32544016f3012a66528003731cf42508100073732cc49902000c7c855d84384001daaa73086398003b30c863c81100063ec2ee0b168200e6e6299432040014fd0a10ac0188029fa1720580310047f43ea730c8000abd841c0614c8011fd0fa9ac120802af60f76590100065fc20eca1220008fe870c96110c019bae63184388002fc6004284110006e7408e6a144200af980189650c401d5b0fb26c48800a5f21573481100063eb2ae5a182000eaf64dcf62440018faed32e84080032f213764c8100c676314ec1922000d76531c542544015db0c21664080035b9977250c100066eb2ee6a102000abd840ca610c02f9dd0c3928788002b7e19531873000e3e328e2a826000abf8650b40cc00137f08b98c48800375d8e7110d100056f41884b286000ddb635c03244001dce65b0842a80533b9c9628c4100063eb2ee818820009f980dd22104001cbeca21864880025f61e42945510071eb2ac82182000c7f8759732040078f8ebb2a87080032f5d9420c740014bf42ce7b122000abd840c961cc0015790ca1082a8002af61032d85500c6dda12e02122000add83c8261cc001d58c9218c488002b7a047298c100074fc3cc93182000d77751c540440013ed0239aa988002cf2113254550006da40ae81902000d5e7390e51544015ed03298c2900031f50d7598443006e6318e4a1a2000c7f75dc9600c401d9ca431a40880031f9d463087100065fb22e020aa000bad840c95188401d3ec9b1a648805f3d986710c8100057cc04c73044200af681dc061
  | 13 => 0x4fcc06e918e2000ade84d4a630400197eca3a264880771f216760c9510047f438413088600ecf8258d62040299dd0438ac0210031fd9570d09100047ec3c83b026400add839c760508018ff0a3b280880026f219740c9100066f41ce3b026400c7c501d9520c4011ff0eb2ec5980023f21d3018552004fd438658842000c7f655cf40440018f90ab80c2a1802b7a0f5158243004f7c3a842102000d9c811cd421040137d0e322648806f1fa15769472000e3e3aacaa182000d75859c74044001ceacb196200805e7d61e51887100047f438c6a8a8000cdc635c031500013eb0038a652880337dce73185420065ec2aed20880008fd8718e51480011fb0db826408003371d6634c8100064e3a4c69902000afb8050b6054401d3ec9b1c86880038f59542d0010005ddc22658822000c7d655cf42040011ff0ea94c3980125fa16764cb10006eab18e2a182000abe8414d60904011fd0f20ec099076bb20943596210072f2a2ea31a84009ef8750a51084018fa87baac0208039759563d08100047f43ea7b02820297e859c443440011fd0db92a298003abe0964588100066f3a0c7b122000e6d65cc821040017a906a1220080027d2057090d100071e284a830a8000abe861d1324400176f08992a2880023fe19740ca51006d6ba2c4194a000cec625c043440013eb0e2084208076bba0b64d89510074ea9ec89822017aec8250e610402bbd064b8085080633b8ca760c9100063fb2ce99022000cbf765913204001d9f0e318c48800339a1c614852000736b28e4a182014cbd425d8420400175b08194a310802be6003298251006e639ac4a102000d77431c55254401d3ca7b2260880031f59773588100055fc22653066200cde635c24394401d9884b88c6a10029f61663109100047f436e8a826000adc845c8634400197ced21c8288002afa1843105100057b408eab006200c7d651d23104001cd8caa1ec4880032f5d064189500072fb2ee5b1a2000e9e5498e4104001cbacb31e6408002b760f71d81420067bbb6868802000e6d65cca2104001cb907baac01886f6b085740ca5100676ba6c59822000cdc7694d414c001d3f0931e80080023fa1a71109500056ec38a33182000b6e859cf62440058f8ebb2e6488003b3d8f628c91000767b9ac6b102000e5d65dca630400137b0d3a06408003579d4630c910005ebc1a858802000cbd655d032c40011f90eb2a64080032fe1170185420063ebae8730e6000ecf201c063508019b8ea31c6488002b5a075418d10005ce41a85a062000e3d6599143040011fb0dba462080023fe1d3298010005cf420e431a20008ff805da32944015e902992c2180023f61e63106500065eba4e231a8400e6f65dd36244001abce6a1ca328002bd2194254510006bb328e2a102000c6f651c943440018faebb84c3a0
  | 14 => 0xc5094d600c4015bd06384c219002bda0752580310072eb2ac6990200097c835ca519400173d09396c688002be60021582530071ea0ceb30e8000abc844c86154001cbacab1864080023f20576953300063fc3acb2102000cde535da31040014ff0ab80c6a10033718c7150d50005ce41a8520c2000ece8498e620400175908b98c4880031f9d66398a100066eb88e231a8400e5f5114e63040011fb0c38a81980038f59443d00100066e3b6e6a122000d74751c540c40015d909a80c488003571cf4354a500066f3acc61902000cdf7698e32040012fb0f2a064a88bb671087350a100072fc1eeab006200ed553d8661cc0092fd0b3b66588002bb20d62084100065f3a6c9b162000e5e6558e42040071fd0e30aa0900036e90d7090710007363aac4a002000cef325c0614c80157f08992c218002eb61032884100a6774386430a4000e3e6559232040015bf0ab88c6a10033798f7050810006da3a6e29942000c7c72d95304402997e8438ac02100397d947218d100066fb1ae018a8000af980949600c4011fd03bb28728002d720d4294150005ba40a8528aa200c7f659d13044001a7f0aba065280039b99643988100074eba2e231a8400d9d7498c32040018fecb388868800373d8f7250d10006d632ae81924000c7e725cb65440019eaca38a870800337a0d7610c100076ac18c218a80009df835d120440012fd0dbaa8098003379c57118d420065fc26eca102000c7e859c76050801d5d07b26c48800277e0d7498810006f8c00e29862000e5d5194c614c001cdecb2124088003b39cc3218520004bf418e8a92a200adc8350b61540011ff0ea12c198802b720d4258730006ceb988620e2000ecf20dc063508011ff0cba062080071f9d5654c8100054ec20e53182000ecc63d0c6244001a7ecaba064880023f61a748c4100074fc16c9b1a2000a7c855c06350401cd8a0a94c39000397d964310d1000736b2ec4a962000cbe649cc2104001cdb0bb82c5a0802b720d4298430007673a0c7b122000adc8350a61940038fcca38aa1a0003371d063c81100066e31ce39824023e3d52d45640c801d3ac931a64080031f1d67258041006bda82e1214a000cbe74d9251c40015ed03b80c2980034f141740ca510071e32ce7b222000cdd7658e42040019bae631ca3880039754653987300063fa96eca8e6000cbd7610c4204001d5cc532484080037598c7150e510072fb28c62122000cf7311c560108018ff0a3b2809800373d0c7250f100047ec3cc7a0420008fe87d95600c401a7a84bacc3a00039b5d65218520004f7c12e7a042000cdf7659153cc0011ff0ea12c128862be60271580210063eb2ee4b182000c7d7659743040013f30138c64080071f9947154330006dba10e2a062000cbd655d03244001ade42ba8c290002b7e1c5198c1000
  | 15 => 0xa192c1108733b18972941300065ec20e2b008400e6c5054960084015db05324c5080029f2157018d10006bd3aae12082000cdd631c542040013eb0038a64080039b98965108100065e422e030a84148ff865c03284001c7ca6282c819002bd2193254710004fcc00e2a182000aec84146620400173d09b96c688003ab5d26498810006ba218e2a92a2009f4815d120040019baca39a84880038f901759874000cbe42ae89802000cdd731cd60884019ba63bb2a598002b7a047118d4200577418a33102000cef761c943840015bd042a4c6080037c9c57018f100063f42aec1902018cee425c261108015df04a1cc128803379ca638c4100057741ec410a2000c7c535d821940015ed02214c2180023fe1970d08100056e41ac918c2000cbd645c3320400157b08102c0218033d1c4215804300766c14c73102000af48159251cc00197ce0b80c8990027d20570d0b10004fb408e6a122000d7b855c043cc0019bcecb90c6880031fd97724c1100067cc04ec1962000d6e541c9435440173906a1281880031fd4676945400066e3b0c6a122000c7d651d13204001c7ecab90c8880032f5097098743006f3994e39062018cee429d842440011fd0f200c2990023f61c6308550004dfc22e690420009f9809c442040014fb0bb9ec0a1003a79d26498c100047fc3a853006200cdc7418e3144001b74a8b808208002b720d4258031004dec26e710e20008fd87d9432440015d90c99064880029fe157018540024bfc3aeb18e2000e9e63d0b40040011fd0e212cb980038fd946450d1000667318e4a1ca200ecc84d8f624400137b0eb2064080026f61e4310a500066eb1ae91082000c7c645d432c4001b6f02ba065288033b0cb70588430067bbb2848802000c7c76dd5404c001d9e84b88c6a10036e90d70104100057a4328728a20008fc815c0644c8038f8eab2e86080023fa1c54987300063ebaec930e6018aee8294560884019baca39a85880035e5d5708c4100063e3a2ca1082000a7d858c76050801d38c6a1680880034f1517418d510071e32ae5b2220008ff865d03204001b3b0039a85a00029fa1272d9510006eca9ae018e2000aec825d1600c40137908b9e41880023f21974cc1100056fc1a84b0ca000d3d415d63150001c78c9212a2a80023f61f545803100676bb66410ca000c7f751d1600c401bb4a6b8063880039bd9462cc9100076631e6410a2000bcc8350a51084299dc64bb064080023fe1d43181210063fb2ce83122000adc835086054429b5842ba06408003379d6638c4100069fa82e8194a000df2715c064c40015ef02a04c221802bee0164980310063fc2ae13088400a5f855c063508019b8ea31a86880033754d768c410005f8c0065082200397e85dd2318400197908b84c2218527b20973d0010006ce280e6a168000e5
  | 16 => 0x18d4000677c3ac51882000a7d8508661cc0011fb01398c2a10029fa17709873001c7f43cc2a8680008fe871d943040018f8edb2e84880037a50970884100047f430ec21a2000adc8359130840014fd08392ca080029fa1764587300066fbb686a182000e756510421040015bd06282c1210031f1cf65c81100063eba8eb30e4000e5d3259432040315d904a1ac110802bd205628c5400047e43a653086000e3f415d661d0001d5ec9b12858800297a167198c100053ec2c82b044200cdc7418c2144001d3d04b22c608003375d963108100047f438a630a8000e5d31dd5600c401d3f0831882880032f10d70987430055ec2064b04a2009df8754f600c4019dee039ac4200035e9c275904100053f42ce8b006200cdd7658c43040018facbba26008003570c375580310047fc3a87304421cdac825d032940019beedb9a85880031f59772906310063fbb4caa182000db7815d032040018fee7baac020802f32094310f100066f438c79022000c7e7619443440015bb01388c6a10033758d72904100057a40a85304a21fd5f519ce51cc0018faeaa14c398002eda1032545100076dc32e018860008fe86dca414c0019b906b84c2210029f61f65905100047ec04ed2a06200d5c65dcd42440011ff0eb1462a00031f596718c8100a4f6412e93182000aee8190d62040015df04ba2c018803abd9273d8910006da324e21922000cbc761d132040019eeec21a20080032f9d94210510006763b6e4a1c2000cdd315c063508014ff0ab92c0188031f58b75501300047e43a873086002a7c8550d61940018fecab8484880038f19672d9110004fb408e99962000abf8550960104019b8e531a860808abbe1c51988100047fc3aca2102000eae64d0e62040011f90ea16c0a8803a718c43d01100063fb2ae910a2000c7d62dd56010401cdecaba0c4880037acc970084100065fbb0e89922000c7f655cf64440018faea21cc39800367dd0634c9100065f3b486212a200ecc6318942440018fce5b288488003d55476394f100d5d641287a12a000e3d659904204001cdeebb1260880039b54d521852000756c16c9b1220008fc8754d60884018f8a33b064a8802ed20543d09510065e424ec21a2000c7c761943244001bab0239a8488002afa1032983310052e42ae031a20009be87d0d42940019b8c539ca29800397d9463d09100047fc3a6030a4000a7d851c06150801c7acaa128008062bba0a31582210163eb88eab008200e6f65cca324400197b0838ac0190023fe197010e510065f3b68598a8000e9d8759163040010ff0eb286408003b32126398810005bac2ce3b1620009f4815d0325440173906a1483180029f21942545500053f42ce33182000abc8650d42440019dce6b86c4880032fa1176108100066eb98e630a8400c7d65dd23104031cdb0
  | 17 => 0x182000abd84949601040197ac938e81980036d9507150310006e7b9ec4a1220008fd8710a60cc4018fec4bac82980037c6027110f100071f328e4b202000e9f7310d6090401d5ae8a12c110803a75d27018d420ec7ec3ec7b12a200abd840ca6010c093eb0fb14a388012dda17435471000774402a4b004200c7e859c463500018f90b3b48298002afa0453590100063fa8ae131ca200ead6458a42040011ff0ea1cc128803751cc7150a100047f43864b08600397e85dda438402b5d904b1ac5080031f5da6590c100055f42064b086000ecc6310c62440018fcea394c398003a798f425001000676ba6c418a2000e3f5195160904015ed0221ac198802ee2113284010006daa10e2a022000abe841c5600c8011fb0e21cc0188026f61e431091000676b9ac520820009f980dce2104001b3ec839a84a88039bdd64258221004fa40ae99802000cde76d8e32440015f301a9ac19886eeb2094350a510055f420eab006400db6431c540c40018fd0fb286488002bba1843d89100071fb288620a2000cbd76d0a4194001cdeca3a6c4880033b98a7110c100066e3acc61082000cbe7610c41440015e902ba2c0188038f9d664084100072eb2ac72182000ecc429c063508013bb0039a85988c75e15070547300047e432e81962000abf844ca6104001eb10ab8062180bf679087350b100063fb2ae520a2000aed82d4261c8001abeca39a84880563f21d6358a100074ea02e031a84008fc87500614c801d5d05b26c48806ebb2096358a510057b40ee030a84009bc845ce62840013e90ea1a20080031fdd762580310072fb28c6992201397e879514394001d5864326408805e7b20973107100063e3b6cb9922000e5c638c95154001b5ae8b106508003574c775501300053fc2ae131c8200d76541c532544015ed03a9cc39800397d94630c91000737106eab044200e3f65508414400179906a104208002fc20540481100c677b9ec59022000cf4719856010c2b1fd0d3886488003b35cf63d89100071fba8c8a022028d9e321d1320400179906a1442080023fa1e41d81520047f436e0a1aa200dba545c241c40019baebb80c6a10039bdd365189100053ec28e630a4000a7d859d1600c401c7aca21a8008002b760c70185420066eb9cc62162001c7c755944204001d58c43248488003a79917298c100069ec26eab0086009bf845cc21040019daecb166408002af2194310d100063eb2ce221020008ff865c343944019d90ea94c390002b760f509873000577c1ae1b1220008fe87d95328400197eeca128008002ada045059032005dd420658822000e9f825926304001aeceb38ec9880030fd97744c91000676196e0b166200aee86d0c62440015ed022a4c2180038f94254582410066f38ce031a8400e5e835d661cc00157b09b2cc398002bda045
  | 18 => 0x40015b906a12c1288032f5d26498e100074f422e031a84009f681dc132c40011f90ea1ec0908031f9c965d00100c577c2c84b044200e5d65d0d4304001cbe63baac018803b358d43588100066eb98c620e2000ece8418f6244001be4a2b846388072dba084354a500053f43464a8aa000c7e87d974344001d3b07b26c6880029f21943941500063eba8ea30a8000e6f65d0f62440012f90cbac62a00039b188658c9100073dc2ae031e20009de87d91530c40176b08194a3880039bd976290910006db320e2a182000e5e6558d42040018feca38a84880031fe157019131006e6a9ae43006200b6d850c960884011f90cb8486a88033b5d3624c1100056ec00ea31a2000eb56410551084019bd0638ac1a18038fd946410910005ce41a8598e8000cdc7418d32440014f906b96ca880023f61c43982510055ec206530e60008fd861d33004001d38e721ac0208023f61a744ca100063fb2ee99822000cdc639c44244001abe63baa8098003a7d9363909100056b40ea431a20008fc8750d60884015bd07a8ac1210038f909655081000576c286430a4000e6f655092044001cdaca39ac408002f920543988100063eb2ee8b102000e9c8498c410400157b09902c0208037954a71c83100074e43cc93182000bad840ca50480011fb0e210c0a88023fe1d6510a10004ee41ae53202000c7c751c9600c4018fb0fb2e64880071f1d56590c100071eb2cc9a1020009be87d0d424400197ecaba065080027760e76509100056e41aca2122000e5c5014c6344001d9ee8b1ac4080033edc270185430057cc006530082008fc815db43940015ed02398c2a00031fa1471580320053ec2ee13088600cdc73185404c0013bf06ba26488003b30877118d420ae77212ec2142000ced425c2611080197c8638ac0210036d10c71501100047dc3ac03006200add8610c32040013e902b928098002bbe0143588100072f41ceb30e6000add8319063c400197eec21a8008003ab99262508100072f284a6b006200cbe7299263040011fb0d39c43280039b081751852000766a9ac41882000add81dd46350801af70ab844208003a75927258c1000736b2cc5a1020008fd809db435440157b08192c1a08029f61774185320047ec04ec212a200c7f751c96010c01d5ce4a14c3a00039bd9473d89100a756c206430a4000c7f659d04344001978edb22648800e3fa1e51582310047e40aec194a000be78250e10440019b8ea31884880031f9d865d09100053f430ea9822000cbf645cb30440015db05a8cc32180397d9574d8d100057b408a0b006400abd8418a61cc00197aeca1083980036e90d70109100066fbb4c7a182000e5c659d06344001cdc84b2e40080038f21375580410069f3a8c81922000cec761c943c4001f1e87a106508003ab90d6250010004efc3a862
  | 19 => 0x2bb60870185430063ab28e2a182000cbe7695331500014fb0a38ac119052eb209435081000756b2686b102000cbd655d032040019bcedb1c84880035ee15701071000576c2064b0442008fe861cd40440018feeb39ac020802bbe1942108100147ec04e3b12a000e5f5194d600c4011fb0f31e4108003ab19343189100047e43ac498a80008ff8758a31940015df04a1ac1988033798e7190c1000656ba2c419420008fe870c96010c018f8cb39842880034f9d143945510c677904ec1922000c7f655cc2144001cdacb31264080773b0cb7654720006f9400e2a182000de9525c021040014ff0ab8ac021002e7e117218d10006af3986528ca017cee72d8a31c40019bceb31886080023fa1c425865000737314cb2102000e6e6259432040019f10cb806290003b3d0a7018d420065e43ac91882000dac74cc932440016bd0b396c688003736047350a210055ec20e4b006200c7e859c66388001b3906ba064a80029fa14729873000576c16a0b004200dcc7358942840019bae6318c588003791cb7150c100075741cc93102000e3d6510e42040018fccb39842080033b9d942109100053ec28eca102000cdc7398540cc0019bce931c42080063f21e615433000676314e818a2000ece4218f2044001bab0f30e6398003add0861cc5400047f438653088000d9c73d0d42c40014fb07b92ca080031f5d965d0810006b6b2ee4a182000bb4844ca51440011f90cb9086880031f140760c5500057ac08a131c8200e7565ccb1004001cbeca31c8688002f9a0443189100063fc3acaa102000c7f755c9600c4012fb0e194a328012dda1763947100066eb98c79062000c7e625d661d00011fd0fa8ac019003ab99043988100075643ac8b102000bcd83dd36244031b5904ba064880021fe1975906310066e38ce031a8400c7e635d631c40014ff0a980c290003ad5915110431006f840ae01922000c7d655d33004001a7ee92a264a88029f61720580430053f428c4b006214cee825d84204001b988439a84a80036b5d3420c950006f2390e2a182000d9e7418c32440018fa86bacc3a0003a7dd16458c100bed7902e81962000a7d8699543040017c904a1aa3880032f5937388410005cec26e5b1a2000cbd74190635406dcb8a031864a8003ab21e64988100065ebb285a006000e6d7558a31040015bd0620ac0188637a189700c9100c6f4312e02122000ade8414663040018fa64bacc221803a75927298c100074f31c87a002000c7d750ca6110c018feeb3acc3980031fd897590710005da422658842000cee76d8b42440016db0a190c2900033b5db32c80100053e412e9b2a2000cf5711c7605083b9d8c5b92a298003ab50d42582210a677312ed2102000a7d821cd650400197f08b80c299003a750d7518d420047ec3865308862ef8c4210c328
  | 20 => 0x77214ed98a4000cde639c642040018facaba4c60805e7b209731931000737b2ec4a1220008fd869c4329400197a82b80c8a9003b3e0863c811000756a164130e8000cbd841c56010c015bd0a394c608002b720d42987300066fc2aed18860008fd869ce41940011fb0e194c3a0002eb2094310c1010d76c3ea03122000a7c855c0615002bbd484b8085080029f6147650c100163e3aecaa122000cbf7650d42944015790ca1a84a8803375da63cc8100063fa8aec194a20097f874ca51940019bceb3184208003275d0630c950005dac20658802002c7c75d9432440058fccab84a320803b3d8f62cc9100046f436e6a122000bad840c92044001d5aeab244210003378c17018d42005ce41a8420ca000ade8794d600c40157d08384c2190033be0970185320071eb2e8420820009de87d8d4244001adaebb1065880027e603740c4100074fb26c7a1a2000cdd855da310c0018f8eb312c0188038fd9464d09100053f414e9b2a20008fd869ce51d0001978c8b8482a80031fd95728c51000677906eca166000e5e659d2630402f97cc33a064080125fa17740c7100066ebb4862182000cdd8798f4004001b98c639286a80033d185700c5400056e41ac518ca000e6c7558930040014fb0b20ac118802b761b438c8100065e3b0c8a122000b748150a51940011f90cb8464a88038f15165993300056f414e331820008de861cd42440018feea192c0208033760c71580320073a20cea30a4000cde7218f40440014fd063a2ca08002bda0640984430057cc00e3b026400e3e6559332040018facaba264080023f61c54580310063e996eab008200c7d87d954344001d3d04320c6880032fa18744ca100047fc3aca1942000b6f8250e51940011f90ea9ac1208026f61c640c9100066fb9ce6b044200dac641c94344001cbc61b2c62a0003371d463c8110025bb42864a8e2000e3f65dcf64440019d8c43a062880034f145740ca500072e328c6a1a2000cdf7398540cc0013bb073b285880035d59471508100047e43acaa1a2000ade829d86344001bc86438a40880036bd45740c9200063eb9aeb30e8000de8825c031480011fb0e2a4c3980031f1d8754c1100053f430caa122000e3d65d0d4204001cb8cbba0c6880023f61f54583310056ec38a431a2000e3d659913204001a7b0bba264a8802b7e194310c10005ce41a8498a8000e6e505496088401d5a8410ac0208031f15376547200a67dc32e02142000abe87d096010401cee82ba8c2900023fa1873509100061fb2ce81922000df0415c021040018f90eb2a6408002afa1351580320056f41ca2b0462008fd871526384001c7acb32064080065fe1e650c8100057dc02873006200ade81dc063508018fc65baac0218023f60271191530dd7b408eb30e4000c7f63dd540c40011fb01bb2a7208
  | 21 => 0x511cd42104013df04b9882080563fe19708c81000736b2c8731020009f9801ce21c40019bcc7b8286080033761873509510057ac08a130c860397c855d12084001c7acab2464080032f9d942905100bd7dc02e2b0084008fd870ca6010c01d9ae6318c488003ab59162508100072f328e93182000cde839c463508011fb0038ac52a0032f5da64108100063ec2ce23226400e5d5118e53c4001f5284a024108002dd20543945510067a208e2b006400e9f649c863440018fcc4bacc2218031f5d5729873000e3f3aacb9902000b3c844ca5054001cbcc73aec7880023fe1d4398010006af39ca6214a000cdc7518f4344001cd8eaa92c010803a79d17018d42007d2a108210c2014cee625d8420400137d0839ac4080023fa1b7488510005da4226488020008fc865d132c4001d9842b88c6a10039b19643d89100074eb22e4b182000d6c65dc931500071fd0f28ac1208031f151760c650005e641a8590620008fe819cf60508018fccab8486080031fd9474cc9100055ec26ea30a60008fe869d1324400197aed32086080036b1d1624c810006d729ae5a0a8000d6e42dd560884019baedba66118002be20161580430073ac2cc398e6000e3f75191404c001cdccba1cc4080032f210764c9100072f32ae53182000ecc8298c21040096e90a992a388003379d4634c1100055f426a33086415aec8250e60040018ff0ab80c2a18029f60a73d95400047e40aec21ca000c7c655c243440013b906b84831880373d0c7250e10006ceb26e6a1020008fd86dd332040015bb0c2186528803371d26348010005cf420e4b1820009f4815c343c4001aeeea38a81880023f60271193320053f430ca21a2000ecf20dd46350801b3ae62188308002bb6184398810005d7c12e63222000c7c87596320400197ce8b2462080037c945709071000756320c4a1220008fd8714a61cc0018fecb38e84880533bc81760c8100053ec28e73088600de7321c5320400137f08b9e4188003379d663d081010757900a0b2064008fe869c443440019bceb31862080039b995749881000757c3cc93102000c7f851d930440014fb0839aca0800337dce73185200065ebb48720ca000cef201cd6295001d98c6a1ec4880023f21972501300057dc0287b02a200df2715c362c400197ec8b9c42880032f1ce64c8010024bf428e918e2000a7d851c2610c8018fc86bacc2218035d6167110c310076739cc73102000af58610f108402f5ed02384c2190031f1db6550d100ac7f434e32122000dd7731c542040017a906a14a3880029f61072594100066fb28e6a142000b9c8350b4084001cf641b2a4088003ab9d06418910004ee41ae52826000e5e30dd5600c401d5f0e320c4880033761676cc5301ef2fa8cc6194a200b6f8250d51540018f8a7bb2a3980023f6007158a53006
  | 22 => 0x30aa0900773b6187250d510066e3b2a6a0e6000b9c83508414403197e84b84c2210533ba0871582320047ec36e0a1062008fe86dd332c4001cbca1298c298002b7a135018d100072ebacc71882000cbc865d032544015bd07b26c6a80032f1d9544c5400c677430e4a1a2000cdd539c6639000197f0cba064a80029fe157018d400067bb28e2a182000bcc8350920440013e902b8487880023f21d41d813200677b28e4a1e2000b6d850cb61480013ed0e21aa3880033b21d52580210065f3a0c328a8000ade8315261cc0038f8e13a8c290003671cd4350a510047f438c8b0e6000e6f6510f62440014fd073a6ca880031f9d661907300074fb26c6a122000d7b855c031cc001d3904320c688003171d663500100063fbaee8b044200e6e6518952c40011fd0e322c018802bee0132980311bf2e280c721aa0008fe87d4a610c0014fd06324a0a8003a718f42105100066fbb0e6a102000bd7835095144001cf6cba0280880039b59573588100053ec28e930e6000abc844cb61540019bca738cc720003379db631091001e3f384eb30e8000cde731086054401cde433a8c2900039bdd5425822100576412e2b008600abc844ca610c0013f30138e84080039d594714c8100065eb22e41882000c7f859d8324400199cc7b928608002bb60243d891000676bb2842142000cdd531d942cc0052fd0b38e64880039b59542c8010006bc42ae018a40009dc835c2414c0071fd0f28ac0208023fe1973084100063f21eeab008200a7d8699442040019b8e931a6008003a721c6418d1000677b2ee4a1a2000e9e415d4635080157908994c3280026f21173c82100063eb2ae42082000d5e7390e5194001d5a8520ac1108038fd94644c9100055ec204330e8000d9d74d0c3294001d5ae9b26c4880031f5897590631005d6422641902000aed8218c6244001c7cca39ac8080038fd94640c9100063fbaceab006200cdc835c26110c019baa7bb06208003978cb654c9100047fc32e02182000cbc74d91304400157908b92c0188023fa1f644c3100057cc0042b04a8189ec825d063440019bac7b9280080039759563908100e65fb2ae8192a001a7c85cc860544019eee330ac0218032f1d8744c9100a576412c6b102000ade811d663040018f8e8b2c64080033759473508100053fc2ae030a6429e5e6510c32040015bf06a14c1988036e509709071000736b28649002000e5d6550c43040015d90ca1084880033bddb4250810006ceb9887a002000db7741c53284001d3f0eb22c6080125f215734831000766b1ac42102000cbd7499262040019bb0c39a85288038f5974310c100047ec34e22186000e6f65ccb20440019b8c6b8064a80a797194430c9100063fa88eca966000c7e759cc61480018feecb2c86080023fa1c2158043024fac38c928e2000d9f
  | 23 => 0x594100c6dca12e02122000ade8398c42440011f90ea9cc3980039759563d0c100072f284a730e6000eae645ce62040019daca39287080032f590714c8100056ec34a998e6000afb804cb60544015f30c21220080023fa1e41580310d6d610ae8192a00497e859c443c40018fce532cc6080027760073508300072e3acc69802000f655118952c4001d3ec9b1886880029f61a758c410004bf418e8a94a000e5c30dd5600c401d3b05b20c6880029fa176318f100057cc0464302a2008ff8759231040013e902ba641080031f589758c7100067ab88e2b006400cbd7498431d0001d3b04b22c6080031fdcc7359410015ba42a86a8a2000adf83509610c00157b0c21882080033ee19700c62000577434863122000cbd861d132c40291f902bb46408003979d563904100066ec30e6a1620008fe81dc16295001c7acb32486080031fd9573189100065fba4e930e6000c7d859c4640c401d98c6a1640880031f595740c4100063fb9eca10a2000e6e6598942040015bd0738ec0a10025f61e42946500072e186cb18a8000eb65418731500015e902994c0080131f9d7650cb100076dc02a6b006200cfb709c26110801cdacaba2c4080032f594744cb10005edc1a858822000abc844c9600c4018faea31843880037358c7250c100076643ec7b122000c7d655d021040011fb0c39a85080038f9d643987400056f43086192a0009bd84dce21840014fd0bb24c398003376187350950006af196eab008600aef8250c61540015ed03aa2c1988032fd0970185430047f4388530e6000cef821d932440011f90ea1cc2080029f2157458031005f4c008599220008ff865c0410c4018fee6b2e40080039719463109100066f3a8c79922000eae5299021040013e902b988408002dd20542545500e63fa92ec194a000bf18010a5144001978e9b2261880627b20973191100053ec2ce3b028600b9d84d9531cc0011fd0dba664880031f1917518520005f2c10821082000bb7844c951c40018fccb38ecb980031f19175c83100056f430e6a122000cdc639c432540011fd0c39a84a8002af6127298730004fb40ce890620008fe8710d600c4018fceb384c22180397d9674d8d100063fc3aca2102000b75859c463c407dcbea331c872880b1f9d765109100063fc2ced18a8000c7f655c843440018fecbb9280880032f9d843905100047ec38853006200cbe83dd94010001b7086b8483880031fd9673d09100055ec2064b0ca000abc844c86054401daaa630862a00023fa06768c9500066fbb6c89886200a7d859c46350801c7acaa148318802bd60450986420163e3aeca21a2000eac6410c62440014fb0bb8ec0a10633b20970984420be3fb12ea3162000cec731c562100014fd0439aca08002f520d42c401000756b2086b102000cef7658942040299d8e4
  | 24 => 0x2000a7d84dc96504001c78c9214a0a8002e720d42d00300a677390c218a4000a7d860ca51940018fecbb928688002b7a0f65108100066fb98c790220009ed829d943440019bce730883980023f61e63084100072eb28c729e2000d5e7558c320400197ee93a2c0188034fd94744c9100056f41ec9b1a2000d5c325d66110c018fce5b2e86880031fd97734811000737328873102000c7d655d130040015db0c3928608002f320d74988100056ec3ca730e6000a7d85d9362c400179906ba0c4880029fa0b74594100063ec2aec194a000abd8510d60904014fb0a10ac0208032f59271cc8100065ec3ec898220008ff8754c61480015dd0c21664a88031f1d673580410067a388c2a026000af6811c0614c8018faed32c84080038f5964310410004fac388218820008ff8754c61500011fb0039ac420803375d9638c810004f7c12e7a002000e5d651d163040013f30138c8788002f32094310e100066f31ee09902000dce801cd42884014ff04b9eca880025f61e540ca500063fbacea30a801baec8259162944019b8e831c6488003ab1917318910006ce39a86a102000cde635c031d00311fb0d38c850800337a0c71582430053ec26e6b282018cbf429d842440019dc84bb442180039b1d265988100072fb28e5b1a2000cec76d094244001cd8ca31664880023f21d6550f100072ebaca630a60189bc8750d424400197ceca148298803ad60443185400066f3acc62082000e5c651c8634400117d0c3a264880031f59674108100063eb2ce71082000e5f7518d3044001cbeca31c8488003b5e055398730006bd384eb18820008fc865c032544018fd0fb2884880033e6027610f100056ec1ea031e2000de9425c04284001b7284b808208003b361063189100066e3b6e6a142000af681909610c00157f08b92c0188037654d700c6200063f3b0cb18a8000e3f6519243440013eb0038a8708003b358d62d08100063f3b6ca1922000e9e82d9063440019deed9926408052bda0770984320065ebb486214a0009bf845cc62c40014bb0b388c6a10038f1d7644c1100056e41ac8b1c2000c7f725d66110c015dd0c190c2900029f6163158031004efc1ae89062000ade82d4c6344001aecca38a86080034f195740c9100071eba6ca19220009bf8750a51904019df05bb26408002b76037218d100047f434e2192a0008fd8718c415400197aca3a264880023f61f648c5100ac7fc32e02102000e3f651cf6444001d9e40b80c6a10023f21974085500075721c84b044200c7d76596430400173906a1281180023f61a7388410006dbb24e21922000e3f65d9143440018f90ab80c6a1003b994861cc520006e7318e4a1ca200c7e645d462c402b9deec19240080023f61c5098e41006bac2ce3a062000c7f7659543040013df0e99065880029fa0874
  | 25 => 0x17e300194a2880031f9cb651051000676310e998220148fc8718550480014fb0a194c3a0003b358d624c8100047f408eca9a8000e6d750c86148001c7aca324a988002afe1643580410053fc2ae030a6000cdd71dc06350801cbecbb90c688003a718e431051000766b1ac41902000de9525c221c405db3c8439a850800397597430c810006eac08e6a162000c7f65dcd42440018f8edb2c62a005f7a94970087100053e42a6130e6000d75859c730c40019bb0f31882080031fccb75580430063ebb2eb1882000c7c7598d308400175904b9ac8080029f21570987201debb190e2a92a2008fd87d9442c40019bec7b8284880039b5d5629041000576c16e3b028600e9d54d8d40440018fcc8baec9880023f61f54987300066ebb6ea18c6000de6521c520c40014f90ca14a0a80033e600764cb10004bec3eca1922000aed8298e62840018feea38ac02180337dd87258c100066e3a4c6b102000a7d829d365440011fb0e212c1988023f2197010d51004dfc22ec9942000ced721ca61cc001baac638a6408002e720d42502100063eb2ee6b202000cbc74d9153c4001cb8ca31e84880033760c71582320065f3a6c9b1a2000abf844ca6004001b7086b80848800277e1d53180310047fc3aa630a8400c7d755d06148001cdecb398c48800367e0073508410063fa92ed20ca000cbf64dc1324403b97a853b084a88033761e63108100066f3b0c621a2000c7d769d661cc0014db0a192c1108031f6167198d200071eba8c920a6000e6c42d943244001b5ec839286880071f1947154140006bac28e29022000abd8418a600c401d986531e400800397d465398730005cec20e53182000db8435c041040319d8c53b464880027da047350b100acf6412e620c2000cbc7619243440015dd07324c40800b1f1d765d09100c66e994ec1922000c7f655c043440018fee5b2c62a00733b6187250e500c676396c49822000d9d74d0c324402f1fb0fb2ec5880131f1d565ccb10006763b0e4a1a2000ecc63d88424400157908992c398003aba0a64988100057a40ac4b0e6000d3c505d03254001b38e931a64080032f5d26498e51005d6c206510aa000ecc219c0635080137f0fb2064880023721c63509100065ec30e89902000cdd731cc6148001ccb0a30a42900036b5d3620c9100066ebb2c61902000d78855c041c4001c7aca392c808002b72097418d100056f41eeb30e40008fc865ce52c4001c7cc93aec988003371d8735091000576c3686b1020008fe8714d60904014fb0fb2c62a00025f21975905300053ec2ee930e6000c3c755913004001d5f0eb22c4080035b9507250e500055f438c8a026003c7e7559432840015b906a12c3280039b6147158810004efc3aa7b0e60008fd869d221040052f90ab8086880031f5d770987300071eb2ee899
  | 26 => 0x31f61f65d0910004f7c12eca1c2000abe8395160904018fecaba24088002bb60b73582410057cc04e6b0482008fe8710d61940015f301a1ec0a8802afa105158241006ce428e6a108200c7c85dd9539040197aeca1483180038fd9764109100065f21ae13088400ecd53d8b304400197c86b80c2a18029f6087459410006cec00e6a1082189ee82dd23144001a7c87baac020802afa1e54580410ee77216eca8e4000e3c7590d601040157908992c1988027720d7094631005ce422e4b182000c7c855c26110801cdcc4b2c84080031fd9573c81100063f3b2eb20a6000aef8650821040018faecbac8318802af2194290531006dcaa2e12082000cbd645c0640c4018fccab8483188027761c430c91000756c1cc93102000cbd649c4430c441c7aa4282c8190036d50871503100069f3aec81922000b9f835ca64040071fd0f30aa198003379d863d09100053fc1ae9b2a2000cdd63dd12004001aed0b3888618802b760b64d8d101ceae284e72886200cdf84dd9310c4015bf0ca9ec018802b7a0c54580310056f40ea73182000adf8350a61040013f50e21621080031f1d46258031006ae39886a94a0008fd87d9250cc0019790cba06528002fae094384010006ebb9ee2a142000c7e755c261d00015df0ca1442080029f6167610f100071fc2ae03222000e3d415d661d00019bec7ba442880032fd97744cb100053ec2ee630a8000cdf7698d42040018faea3aac1208026fe1d420c7400072fb28c7a1a2000bcc835082154001ab8ca39a84880033ddda32440100047e43a86b0ca000c7f655cd20440015bb002a0c688002bd20542185500073ab286210820008ff8750c61480358f90b3b042a800367200735084100566412e93182018cec629da4244001d986431842a80031fa167118d420066fbb0e6a162000c7c655c24244001c7aeaaa4c3a00cb9d9d461085500047ec38653068200bb6840c951c40014bd0a390c688003a754d648c4100063ebb4a6194a000c7d325d661d00015bf0e290c6880038f54654987400073b428c218a4000c7d758ca61cc0018fecab9882880031f5d432987400ec7ec3ea33086400c7d87d974344001b390a39a85a00031f9d470984430065f41ceda0a802cd9c321d13244001d3ca6b2462080033b9db32885100055f426a6b048200cbe74186315000179f06ba2c4080036b553724c5400053ec34ca1902000a7d8699532040015bb03380c6a10039b19574189100063f32ae12102000a7e85dca61cc03b75904a1e84a88031f61671191300063f212eb3088600cdc7598e3204001c7b08bacc3a00039759563508100047ec00ec992a200cf5651c532840014ff0aa00c2900032f99071503300066eb1ae890020008fe87d49600c4013bb07ba442880039bd97420c9100063eb2ce3a18201caec8250f6548
  | 27 => 0xf996ca1922000ecf8298c210400197acbba265080038f59564cc8100071f3a8c819220008ff865d021040018feca38a8688002b76147118d420065f3b4862122000a7d859056010c0137d0fa1a85880031f5d5701852000677394cbb0e6000cdc7498e31040096ed0a314a3880027d20573d02100057b40ea630a8000af48150e6094401cdee8328c4880023f21d32185500063eb28e91082000ade83905600c4011fb0c39aa1900031f1427118d52006da218e2a0620008fe869c74254001aeb0a38a8528803b554d61187300047fc02ec214a200aec864c832c40019dee8b1260080023fe19708ca51006bac28e2994a2008ff8750c60548015bd053acc6080523f21d645881001e3e3aecb9942000e5f65dcd42440018fecbba240880a3671087350810006da3a6e29902000c7d859c464cc801d9ce7b1ec4880029fa164158031006f840ae021220008fc8750e619400193ae931865288039bd95320c9100047fc32e81942000abe8694f415000157b08194c128802f92057358810005ce41a84a9c82008fd809cf6254401b3ee8b1a64080023f2197090951005ea40ae53182000e3f84dd560104011ff0cba26008002fa20943c42100059f424a6a12a200e9e6498d43040013f102b8064880038f9d1650c8100ee76194ec212a200ad6811d46344031bcca538e4088002976147018d420057cc0042b008600e5c6518d32440018fceb394c3980031f5da65108100053ec2ee630a84008fd879d84304001d9b09b1ec4880031f90b75580410066ebaae031a8400dcc73d894244001d3a86b88c6a10031fe16760c951005f840a8508020008fd809d832544019d8c539882880532f50871580420057641aa4b044200af980109600c401be30138865880037990871481100063e2a4ec192a200ecc6218e32440012ff0eb2864080036bd41740ca210066f39ec7b12201dd3d529d03254401cdccab9cc408002bb603620c951006af39a8728aa21bced861c943944016df04a1ca2a88033bdda62d08100055e42264b04a200e5d319d661cc02bb5e40ba06508002af61032580410076731a873102000cbe645c2410c4018becbb9a84880033760e71d81320073d106eab008201a7c8510c60544034fd0a190c0a88039718e32941500072eb2ac62182000aad840c86148001bb2a6b8062180065fa17748c4100066e3a4c79002000e5c6518c32440018facb39842080038f596649081000576412873006200cbd76d0a53904018faed32886080035ee15700c7100a66e992ec1902000cef7458a31040091fd0c39aa1880572fd097610a100053ec10e6b2c8200abd84d9464c40015e902aa0c2900031f1d8654c5400074f418c831a2000c7f655d0634400197aecb80872080277a1f654c7300065f3a6c9b122000b3f855c0439040173906a14a32080
  | 28 => 0x5d9642440011fb0138cc9298032f1db6450910005da40a86a12a200cdc635c6535080173906a1083980027e60274885100067dc32e01882000cdf7659131cc0013db05ba46288002bda074218550005d6412e73202033e7675d8421540013eb0e194a2880023fe197348010004fcc04e39902000c7f75d91600c4018fae5b2862a00031f59772590100065f3b4a7a0a8000e6d65d0e62040015bf00b90c688002af21153185400072e280ea31a2000ecd8498e62040015f301b8ec0a10035e5d530987300066e41eeca10200297e85dd221440019ba62b80c6a9003ab9d364d89100072eb2ae53182000d3d42dd5601040197d0838ac1a18033b21d624c0100063eb2ee99902000af681d4960cc4018fce4b288608002bda0443986500066fbb2c6990201abac8250d42540072fd0a3a463080036b9907250c10006cec28e6a168000a7e868ca50540018feca39a4088002afa1051185400bed6412e81962000eaf62d9142544019b8ea31a60880039b19743d89100ae5f304e81902020cee760ca50480014fd0839aca080029f6167358043005764328510a20009bf845cd200400137d09b9c4288003b3dcc32582210075639cc93102000c7d75dca61cc0015bd0bba0c68800397d9463509100063eb2ae12182000e7565dc542040019788638ac0210b6dea1432c421000736b2ae931020008fe869c743540071fd0f28ac01080337a187350b100065ea0ce23226400be78250f108400157b0928ac0208031fe157019132004f641ae52884200e77658c4314400157d03380c8990029fe1530d81420065e422e030a64009f48750b10840019db0538ec0990131f9d76510f100053ec2c83b0264009de831c5504c041d5842282c8190032fe19740ca510063f32ae1b286200be78250e51440012fd0fa1aa4a88032f1d16458e10006af2a6e6a12a200c7f655d231440011fd0fa8ac1218033b9db3208510004fcc04e710a2000cbf421c560d0c015d904a1ec0a88031f5d475984320071ea0ecaa026000cfb709c2610c80157908b84c2190031fd97729053001cbf42ee818c2000cbe87d9231440014fd0bb98c2a0002bda0450984320053f4286530062008fc8759532840018faebb24638800b1f9d76550d10006af3ace720c6200e9e6350b40040017e3001922008003b398f3208410006ce39e86a142000eae74992620400157b0028ac819002e720d42904100047ec30e2a106000ead749086148001cbacba1c8608087ab08750590320a677390c39824000adc8359163944015db07b26c48806e3f21d6358a510047ec38a4b066200ead62591429400197906bb482200031f5967310c100063e42ae131c8218eea800c960884019b8eb31a8608003975967498c100067643ac518820009bd8790c42c4001d9ac721ac4080023f6027610d510072
  | 29 => 0x8a418800337dc27018d420ed77416c7b12a214cee625d832040015bb00298c6880031f9d175185200053fc2a8030a6400f8f43d0832944019d90ea1ac4080023f61f6510a100053ec28e030a6400acc8350861480034f90aa10c0a88023fa187454f10006ae98aeb20a6000cde861cd42040015f30120ac020802af61321984430067cb80e13086400c7f7558d608840197aed32464080023f21d43185500c4f6412e898220009fb865c03284001b3906ba064a88027e60071508100066ea98ec90e6000d7a755c231c4001a7ceb3206408002b7a0f71d81420143ec3ecb20a2000c7e769d631040011fb0f18ec0a10038f59473590100263f3aeca3262000cec711cd62d04019b8e931842080039b99543588100072fc2ae031a2000a9d841c863440017c902ba4c408003379ce31d814200e3e3aacb9902000abc844ca61cc0019deedb928788002e720d42906310047fc3a86302a200cbf659d032c400197b0838ac1a1803971d763501100056f418e13088400cbc7619032440311fb013b0648800397d946310d100063ebacc530e6000cf7719c560108015e902b92c018862be602715804200677990e2b008400c6d75d8832c40015d90ca104288002bd60640984430067db84e030a64008fc815c064cc8018fc86bacc3a00533b989768c8100063f3b6cba1a2000a7f855c2618c8018ff0ab80c2a10633b20970986320073b42cc218e6000d5e759ce414c001d5cc53246408002f320d42c8210006e6210e6a12a200af48650d51c4001a7ce8a1ca3280036b5d3420c9510072eb28861902000cd4631c520440015bd073acc2190038f5d664084100063f326eab0442009bf845cf2084001cdaca3a2c408002fca0432440100253f42865b02a200e5d651d2630400137b0dba264080033b9897010c100066f98ae031aa4028fd8794560104019dae530ca390002af60b76590100bef4192e010e2000e5c6518e43440015bd06292c0188038fd9464909100074f31887a002000d79755c241c4001b58e999265880023f21973481100063eb22eb18e2000adc835c5600c8018fecab846488002bb61f32185200071eb2cc9a182000cdc76d8d3244001cbb063aac018802bb20d421852000c3e43aca9802000af9800c961cc0017d3013a6c4880039b5964248010005da4226528e2014cee825d83204001c7ecbb268488003a75d26498c10005f4c04e7b122000c7c855c26190c052fd0bba660880035ed9570109100053e42ae6b048200e9d641c963040011ff0cb868418803371cc42586500057b408873086000d3f7495132940019baecaa462180032fd94744ca100047e432e52a620009f4815d130440013df04ba4c608002b720d75582410aedda12e02142000e3f54951600c4018fac4bac82980032fa18744c81000cbe42ae89002002c7e7
  | 30 => 0x84420074ea02ea31a84189f8865c032440052fd0bb9c4288002bbe0943986500043f43eca9822000e6d65dcd62040475d904a1ec2a90033bdd942547200065fc2ceda0a8000e3f65d913244001d5a84a02c11080277a0f705523100736b2cc4a102000c7d655c342040319d8c53b084880023fa1a7650d10006ea398e2a102000e6e42d94424400157d08314c0188031f216768c54000736196ca10a2000e3f65d903244001d3c82b88c6a1003371db4350d100063f3a2e9b2a2000cdf76d9153cc00157b08192c2218027da077050d100063eb2ae7a002000cbd7690c4284001b3ce8b186408002bd60450582420063fb2ce89922000be88250d100400153d08394c608003a79097018d421e7c621086194a200c7d659c443040019ba63bb28598002b7e0d7018542007363a6ca3122000c7c855c061508015bd06380c2a10032f21170984420066eb98e7b028400af9801cf60508015dd0c19240880033b5cf62085100063eb9eeab008200bcc825d063440019f0c2b806290003b360863189100063fa8aed28e4000b9e8390153904018fb0a38ac019003a71097118d420065ebb28520ca0008fd801cd6294401d3d0f324c60800379988714c8100063e3b0caa1a2000a7f8550261d00019b865bb26408002ebe0973590100071e284a8b04820097e839d251544019bac6b80631080a3f6027118d5000676bb2c5a1020009ef8750f624400197f0cba06408003179d463c81100063eb2ce99002000af48150c61480018f8a6bb48328002afe1443185400065eb28e89902000e6f650ca21440017cf04a1a200800397194638c5400074eba4e231a8400ecf8498e62040017730819620880026fe1d429474000767314c62102000abd8694d41d000197aed32064080023fa1a744c1100263e3aacaa162000dbb425c2410400175b08192418800337a187350a500055ec08a0b206400ced7458b30040015bf00ba8c6a1002af61c640c9100072f98ceb30e6000cbe76190434400155b04282c8190035bd97724c54000766214e231a84009ef874c83284001abb0a39a8528803379ce61d03300063ea12eb3088600e5e30d9431500019a8c73886488003371d663d0c100a47fc32e12142000c6d651c94304001b38c9b9a8488002b760f54580310065f43ec89822000bb5840c951440072f90ab9a41080023f61c5498c100056f41ea8b006200ade83c81600c4015f301a9ac018803b654d60180310069e42ae8192a203c7e7559443840013ed033a260880031f9d463c81100055ec20653066200e3d75d0a61d00015f301b8ec0a18038fd9772191100066e3a4c69902000c7c855c263944015f300192c0188033718d7090d100057b40886b006200ade8610e3244001a7b0bba26528002e720d42905300057b4086530880008fc875954284001bc8643
  | 31 => 0x2000c75651c532040019e902b80c2a18035ee157010c3000576c14e3b028600cbd849c76050c01cdecbb1464880033b60a71d81420de7610aec194a200adf87150634400197c8738ec0a18031f58975984430063f398eab00620397c855d93284001a7a87baac0218032f59172cc0100063eb16eab008600e9d64dc963040015df04a1ec2a80033b0c871588430056f418e13088600e6c6510f6244001d5906b148220092dea1432440100074ea1ce031a84009ed870ca5188401ab865baac0218033be097098432005b64128728aa200c7e76d96315000157b08192c2180031fd9570cc9100069ebaa8518a8000aef864c83284001cdee7b28c4880023f61c5418f100053ec3aca19020008fd871426190801cbcea3184288002bda077298730014bf43eea982201ddac625d032544018fce5b286288002afe1942107300072f184eb30e6000e9e741906344001aeaca38a8608012dba146254b100066f318e2a1ca200cde639c442040015db0931ac4080027720d74481100063e29aec194a000b748150e51940019d2e4b00c018803379d463d0110006f9c0ae01922000d9d641cd42940015d90ca1ec4880032fdda435474000666318e4a1a2000c7d42dd560104018fce5b2864880023f61c63c81100065f3b0c9a122000c7d659d13004001baaa638a60880032f19071501300066f3a8c79822018e6d75d8b20440015df04a1ac398002dbe0943941500065ebb08720ca00297c855c332440015df04a1cc2180038fd9464d0d1000766a94c61082000c7c755c56010c01bca8438a40880031fd96740c510006bbb2ce221a2000c7f759c9600c401b38c839a85880039760d759873000576c14a2b004200dd6531c530440015bb0720ac0188523f205760c8100073b3aec330e600397e859c44384001af6cab80648800397d9774d8d100074eaa4c62082000c7c725953004001c7acb32284080036d205740c9510071f3aa8530e800097f865d6418c401d5f07b26c488003e3d0f420c810006ceb20e6a102000cdd831c56010801bcac438a8408002ed21132c40100057b408a131c8200ade83d9363544011f90e996c0a88034f151740c9510072f280c729e2000e5d6590c4304001cbecba1c648800357cc57590530004ee41aeca1020008fd86dc1429442f9d8653b08588003ab9926250a500066ebb4a7a0e6000ce9625c031040014fb0a192c0218026f2117218d100076631c849022015cef7690920040015f300212c128802afe1132980310065f3a6c9b1e2000cdf835c261d0c01d3cc931884080031f58d75987400065eb2ce81942000abd84c856010c019bc61388c6a9003371d663108100063f392cb31820009dc835d262040015f30130cc0218036d990714c8100047ec36e520c6000a7d859c56010c01ab8ea39a80980033e5c0709
  | 32 => 0x17a906a12a288003b358d62908100053ec2e413188200e5e6598d43040019dacbb928688002bb60850984320074f324c7a102022eac21145640c8015ed02284c321802b7a045498c100075639284b008204b3e85d9254c40015bd0bba4c6080036d9907150e510067bb8ce3b0284008fd869c73294001b5ee93126408002dd205435455000676bb06510ca0008fd869c740cc0019eb0f30e6398003578c175906310057a40a84302a200c7d65dc930040011ff0ea12c0188031f5d574987300066f18eeca166200b9c8350841c400137f0ea14a2a00037554e71cc110006dd21ae02142000dd6539c73044001cdacb99464080033bd947250c100047ec3cc79002000cbd765913204001f4a8420ca21080397dd553580310074fc24c62082000e3d6599043040015db0c1924008002b56047018d4200676314e7a0220009bc845cc21440017af06a12a3880039b5d6421852000576c3085994a000d5e738ca515440157d03b24c9980032f5da53904400076731cc5a102000c7c655c031500017b106a162088002f320d42483100163f3aecb1922000e6c7459662040013ed0239aa588002b7a0a7518d100062f3a8c61922000dac515d03288401d6d02218c2a00023f60273d89100072fbaca6b006200aed82141600c8415d904a18c0a9003b390a63c80100056ec00c729a84008fd861cd50d00018fcea31c62880023f61c42d85500072fa88c729e2000cdd7318f404400197eecb2686080031f9d473987400063fb2ae91922000e3d659ce64040015bb0bb88c6a1002bd205425873000577c1286b006202c7d711d560884019f6e1380c2a1002be61832440100063fb28e818a2000af48150b61540018fac7baa81880033b5977250f100063f31eea9862000c7f635d641c40019b8c6b86848800a9f21732586500067bbb66488020009df835ca640400157f08996c0a880277e0d74482100047f40ceda1aa000e9d879926304001cdf05baac110803379d063c81100063fb82ea30a4000cde749c863440018fce23aac1108036b141740c920006cfc28e6a108200cde73186414c00157f08b98c2900125fa1671ccb10024bfc3aebb1e200297f8719432440019beeb38cc608003ab188648c9100053f428e2b0064008fe8710e61940019b8c73888688002a7a107218d10006d7b2ae990a4000c7d75cca61cc0011fd0faa2c0188038f59472990100047e40ae1324a600af4864ca1044001cbcc6bac63880023fa047358b400047e43acaa162000c7c509c463540019bf063b264880038f194644c9100047ec38a130c8600d7b505c0329400197b0838ac1218023fe197210c100063ebb2cb2102000cbd861d132840015b906a14c1988a3e3108430c81000736b28873102000b9c8350a51d0001c78ca3206488003a758d6450e510063f42aed188
  | 33 => 0x3f2057018d5400e3f3aeca19020008fd869ce51104018f8e6b2e40080031fd9572d0110004bfc2ae33008600cdd7698f4204001cd8e732cc408003731cc6250951004fac38650822000c7f761d540840015ed023aac120803374c37650b310063ebb2eb20c6000aef8250c60544011f90cb96608800337dd9530c640005da40ae6b202000dce63dc943040078fee23aac0208029fa1764980310071fb28c8a12203de5c5098c32944093eb0f28863880031f61471582420074ec10c831a2000cbf7699132040018faca38a84080029fe1570987200055f404e232264008fd870ca600c4015f300192c1288035bd977250d10006bbb88eaa022000ecf429c463508019b8e431a86a80037acc970884100073db2e60982201acef209d8325400187ecaba064880031f6177058b31005f240ae8b102000d3e7490a515440153d06282c819003671ce5350b400074f438c831a2000cde7398641cc001b38e6a1a84a80032f21276109100065ebb685a002000e3d655cd6404001d38c831a86880033720e760c9100063f3b4eb18a2000cef325c2618c83b1fb0db92a3188023f61e40185320066ebb2a618c8000e6e659d262040019deed3126408003375da530c44000576c16e930e6014aef840c861480058fcebb2c8688012dd21543547100263f3aecbb162000c7d759ca6110c01cdceab14831805f3b6187250f100065f3b68418a80008fe86dd03154001cf4403aac020803ab591628c8100063f43ecaa122000cdf859db314c001b3ae83186488003a7d8d4290510006e6194e72884200cde7298f4004001c7c81baac0208031f59570908100053fc2ae1308841aaf9809d5600c8013bd07ba442880033b1d832545200071eb2a842082000cbe645c2418c42b1ff0cb8063108026fa1a740c9100072f318ea9862000c7d7519261cc001cdc40ba8c2900039b59542480100063ebaee630a4000c7c505d832944019bae9b1ec4880023f21d42185500055e42264b0ca000c7e425d661d0001978c9398428800397996535873001cbe42aeca1c2000c7f655c0424400137908b9a40880031f59574884100045e432e81922000af6811cc6150801c7ecbb248688002b761b740c6300063fc2aec21c2004c7e7559442c40011fb0e216ca180033be1d43d8910006763b6e4a182000e6f65cc92044001d98c6316648808abb209431855200576c04e7b122000e9c845c463508018bcea31c62880027da1a710c9100263e3aaca21e20008fe861cd42544011fb01388c8a90031f1d4634c31000737b2e852122000c7f759d56008401cdaa2a90c2900023fe19740ca500056ec36e99846000c7d859c464cc001c7ecbb96c888002bb21d42582210063fbaae6b044200dd6811cd42440018faea31c6388003379d0634c1100065f218e2b068600c7e7259442040
  | 34 => 0x41ee4a864000cbc761d132c40015ed03aa4c2180039bd9542109100063e3b6cba1a20009bf871903244001d5ec8a1ec4880031fd977350110005da40ae73202000ced721c9600c401cdcc532c6408003979957498c100074e214e031a8400c7d655d262040295dd05208c2900033bc83765083100756194c81082000eaf8319062440019b8c6b8484880035ee15700c62000d3e42e84302a200cf7651c532040011fb0e284c219003970c27598730005ddc22648802000fa54210421040019dae8b106208002b7a0c5298730024fac3ec728e2000ecd74d8f62440014fb0b904c3a00033b18a74cc1100065eb22e71082000e5f65d8d43440019bc61bb285980527b20973990100071fb28e89922000dd6631c542040011fd0db8284a8803b35d06318910006e6c00e6a124000aef8650d62040015f700a1ac1988031f217764c010004dec24e7b122000c7c875944304001b38a039a84208027e602710cb100069e328e89922000e6d825d46148001c7e83baac0208031fd957218d100056f41eeb3086400dcf431c94304001c7acb392c808003ab20f64d891000775c02a4b004200e9e6498d32040015bf06a14c008002de6025310a500056f41ec518e20149ec825d032040018faecb288408002eea1032c421000677c3aa4b00421ccbd425d84294001d3cc931864080035d6147148310005ba40a86a92a200ed68118d53c4001c7eca3208688003675cc43104100063fb2ee89922000e5f6510e32440011fb003b2a4188023fe1974480100c47ec3ec7b1220189ee829d943440019bee2b80c6a1002b760c42983310069fc22eb3088600c7d655ca41040019bce431c62a80039719463909100057643aa4b044200cde76d0c324400173906a14a2a0003ab9d564884200a677b9ac590020009bf8750c4344001777089962108003b398e624c8100067c902e030a8600dba545c241040015ed02284c3210038f5d643987400071eb2ee532020189f8865c042440019eb0c38a65080031f5d96510c10006ceba68619620008fe87108615402f97cc2ba064080027e618705473000767314c61902014aec8250061480019b8e431a6088003371d87350a1000cbf428e6b10201cc7e855d821940014fd0a312c3980776b085740c9510056e4328621a20009f980dd2310400157d08194c0188038fd525498730004de438c89922000cbc8759130040014ff0ab80c7880032fdd943508100acf6412eca1c2000c7e76194324400173906a1680080031fd94735011000677c16eca182015cee7258a31840015e902b24a3900035b9947250c1000756320c4a162000c7c76dd53044001b7486b8482080030f597744c8100072e988eab006200b74814ca5154401be30138e818800337dd9644c43100d3f42884302a200ece84d8f6244001978ec3a26508002
  | 35 => 0x50c61540018fecb39c84880029f61771d81430053f43084a8aa000d3d749503254401cda43baac1108027d600714c95100cbfc3aeb1882000e5e65dd2630400157f0ca148318802bda0754580310072fb2ce5b1a2000c7d76994320403975904a1e85280031f5947458c100057a40aa630a4000cee629d031040379d8c4b94a3880027d20574c801000676ba2c49802000c7d859c76050c015bb07aa4c398002b7a0f549873000577c12e630a8000adc83509610c0015bd07b1261880031f5967410c100063fc3acaa182018cec829d832440011ff0ea00c2990031f9db6590d10004de43ac89902000aee811cd62100013d90ea1ec488002cfe1132945510047ec38a431e20008ff805da540c40197ce532062080037310c7250e5111e77bb064a8c42009dd83dd221c402f5dd05b2ec5880632f5097098442004bec3865282a000cdd76d0e320400197aecb266408002af618744c810006d63a6c49922001c7c709d661d00419dced214a090003b3dd0631891000677992e13088400cbe861d132c4001af2eab86c9880026f61e4310a100071eb28862082000c7c745d461480019becbb9a85880033698d700c4100147ec04e2322a000cde73d8f62c400197ae9324c7280031fd9473509100063fbaa86b00622fd9c321d132c40018fecab8064880031f59774cc0100071ebaca930e8000c9f7418d32440019bd0738ec0a180357e1473509510063fb2ee710a2000e5c65dc86344001cdacab9cc4080536b98a740c810007373aec520a2000cdc8754e61cc001c7ceb326400800f1f1d76550a100063ebaa8630a40008ff8750a6094401cbecaba0c688002afa1032d81510063f428e2b048400cbe719c0644c80137908b9e40080031fd9573d89100047e43a84b0e6000cdd731cc61500011ff0e992c1988031f5da658c81000766b1e86b102000a7d859856010c01b3f0239a85a00027d6007150e5100767c3ec7b122000af587d8661cc00197eec3a265880032f20e76d0540004be41ae52a2a200ade83d41600c4019790cba065880029f61772987300074fb26c719220009f6811d153c40019bee739ac120803b318f62909100047ec30e2a166000ee652986210c0411ff0cb806528003ab99262cc81000677bb2849002000bac845ce62040015db0d21ac4080033b9d973189100074f20ce031a8400e9d5458e41040019dcedb1064880031f9d46318b100057b40884b086000e5f311d5600c401bd4a4b8443880036ddd0714c81000656ba2c4194a0009be849d1324400197c80b80c899003a798f42104100063f428e2b046400cbf7699032040018feeb38ac021803a79d17518d420053ec2864b006200c7e76d9732440018f8edb2a62a000375d8e710c9100073632ce63122000e9c635084144001c7ccb3246408002b7a0c5058032004f7
  | 36 => 0x2c018802b7a0c50984320065e21ae13088400ecc219c463508013ed0e192a2880023fe1d43583310065fbb686a14a200e3e751902144001cdaeaa10c29000373d8c7250d100066fc1ae130c6400aef8359162040019bd0f31884080031fd96740c9100053ec28433088600adc835d5600c8011f90cba4a788003a75916350c10005ce41a8520aa000c7d861cd5294001aeb0a38a87288023f61b7050e510074e320c62122000c7c651c5404c00197ecbba264080031f5d4749873000736b2a86b102000cbd645ca63040018fcedb2c64880023fa1a71909500063e42ae031a8200e9e87d936344001d9d04318c4880039d59543440100c6f5400e4a1a2000af681d0a610c001c78cbb208488003379cf53185400057b40ccab0e6018aef850c960884018facab9462080027d61c31084100072fbaec6a022000c7d655cc21040319dee7b10428800317d9473509100063f3b4a621aa200aee8610b324402bb5904ba06508003a7592638c8100bcf7416e918e2000cdc7498e3204001d3cc931c86080023f61c63d01101f72e284c721ca200dda535c03104001d9cc6a164008002b7a0c6310810006ce39c86a8680008ff8750f6148001c7ecaa1e84880031f5d4618c5400057a43286a8a2000eac6418942544019b8c6b8062a8002bee0175580310067bb8ce3b028600c7d87d953244001d9cc721cc4080031fd96710c91000766422c6b102000c7e635d763c40313d90ea18c4880031fdd8754c0100057a40a87b0a4000b9c8350940040019dcc43a062080027d6187150e100bef5212e010e2000cde738c760548015b906a14c2080023fe1d53d81420065eba2e031a8400add809d463440019bceb31e64080031f1d67258043004f7c12e831a2000aed8219062c40038f8eab2864080033e5c07018543006eca9ae0188201297e8795142544011f90eb2a85988127d61c62947100065e3a2c89802000bac825cc64440058fccab84a310802f320d425442100736b2ee8b102000dd473dc54284001cb8ca31e86880031f9cb65cc1100c73742864b0442009f9809c743c40018fd0fb2c86880023f2197310b100047fc02ec194a2009ee861c94344001cdecab9ec488003a754d640c410006bb328e29902000cec76189324400157f0ca1e85280039799663108100a47e43ac6b102000abe8710d60104015bd07904c398003375c57018d42005ce41a84a9a8000aef8250d6094401ab860bac8318803375db430c810014bf42ce89822000c7d751ca61cc0011fd0c38a86a8003ab2096458810005d6c24e7b122000add8314863440013ed0339a4088002b760c42584300066ec18e2b008600e3e5095261d00018fee9b2e40880033754d7018d42004df43e86a142000e3f6550a414c001d38c621882880022fe1d64193300066fbb2c79902000af481
  | 37 => 0xa510073d902ca9002000adc8358a31840011fd0f18ec0a90031fd9573109100072fb1ecb18a8000c7d62dd540cc0015e902b22c3980033bcca71d81320066fc1ae030a8600a7e829cf65440015d904a1cc1288026f211764c81000677c16eca102000aed8418f62440015ed0229ac198802f32094310c100065e422e130e8600cbd841c560908017750819220080023f61c32582510047ec3ea6b066231d7b521c151cc001c7ecbb24848800337a1e63c80100063f3a8c610a20008fe87109600c40173f08b92c6080038f59454593300053e42ae4b0062008fe8710d61cc0013f30038a65880029f61774d8132004bf43ca8992a200e6f65d8b324400179904ba4c608003abd93621091000676b9ec59022000cdd65dcd42840015dd05ba4c3980039bdd732582210053ec28e53088600abc805c4644c8011fb0c39a8408003375d57018d10004fa40ae12122000aec8650821540011fd0db9c42880032f10b76508100056ec18a831a2000c7c73d9421440019f6eca1a20080027d205744ca100047f43cc2a066000bcf835d06244001cbeca39a84880632f50a76109100066f3b0861922000db7815d03254401cdcebb146288002afe1942904100065ea12e030a8600d5e75d8c32440019b906b80c2990023f61e63106100047ec38c610a2000a7f855d1608c40157d08392c01880237a1e635081000677b2ee4a1c2000a7e849cf65440018fac7baac0208031f50975987400063f3ace53088600c7f751c96010401d9e40ba8c6a10032f9d972191100065e21ae030a86008fe87d9543c40015bd07a8ac019002bee0132583310063fb2ce918a2000e6f6590a214400173906a1462a00039bd977250d100066f3a0c63122000c7d72dd56010c011fd0dba0628800337a1873509100063f316eab0082009f5801c543040015dd073b0c488002af60b50d9110005bcc04a7a14a002c7c75d9642440019df043b284880031f5d46418b100065e3b286a122017de6529c720c40013df04ba260880036b1d3324ca100063ec2ce231a8400cbd7690f40040015ed02380c2a10029f61671580310061eb2ce81902001c7c755954204001c7eebb226088003b318f43d89100053f4308728aa200abe840c965cc4398faa4bb06528002bd20564547300066e318e2a1220008fe811d9325400137908b98c4880029f61f650c9100047f43864b0880009bd84dce21040058fcebb2a848800397d94638c5400072eb2ac71902000de9525c22104001d9ac6b1284080029f61a65508100071ebaac91882000ade82d4e63040011fd0e18ac1108031f6167198e200066e31ce329a8400c7f659cc3244001bcc8438a41880031f5d774987300066e31ce321aa000cde635c03294401b6aa938e8088003676047350b400063eb16ea9862000adc855c863440011fd0e2a
  | 38 => 0xdd773dc54204001abee7baa80980035e19570109100073732c86b102000e3c65d934244001d5ac8b1664080633b20a761091000736b2e659002000cbd64dc132040019bae730c43980027d61c32947100074e424e231a8400e5f5394d600c4092fd0bba443880032f9ca64cc01000737b2e84a122000a7d869944304001d9d0931ac408002fc20543840100056ec3ce031a84009be871d132040313f10ea024088002af61032587400056e41ae13088400acf825d263040018fecab9062880027d205744c3100063f42ce3b026400e9e6390c4104001b3ec9b9a84880023f61c5298c100066e3a8c6a122000e5f655cb63440015bb01ba8c6a1002dd616310c710004f7c3a8528e4000a7d85d9363c40019baed31c86080023f61c63108100063fba884b006200eac6418b324400197eec3a265080023f21d42987300066e41ae130e8601a7e859086054401cbaa329ac118803ab59273588100065f3b6c821a2000cec825c06150c013db05ba4638800397d9763109100063fb2ae83122000c7f655ce4244001978e8b22c5080039719463509100047f43cc6a9e2000b9c83509404c0018fcedb2c84880023fe1d6510d100065fc20ec9922028d9e421cd42040018facb39cc8080031f10975185200047e432e72a62000cde7598e410400193ce831864880023fa1a71cc9100067bb28e2a142000cdf7698d4304001b38e7a1a852880337a1c6354f100047fc32e818ca01bdaf205d032944013ed03ba660880031f150765454000676398e2b102000cbf76dd132040019790cba06508003375cc63085100a4f6412e620820009dc835d942840011bb0c39a84080027e205701091000766b1886b102000c7d651d332040018f8eb30a8198003179d463085100057ac3ec210aa000bad840c920840018faed3ac6308002e720d4210731006763b0e4a1c2000cec321c562cc001cbc603aac0188633ba1c32582210072f32cc7a102000d5e541cd4254401c78eab2260080031fdd965108100065eb8ae03226400cad74d8832544015df04a1cc398003571d473580310063fba6ca10a20009be84dce21c40092ff0ebac838805f3b90a7610b100071eb2ce53202018bac8250f42440013eb0038a85080032fa1271d81420047ec30e2a14a000c7f651d330440018facb38e84080029f6172098f4001e3e3aeca21c2003c7e75d9442840015f30038ec0a180e5f2157650a100063ec3ecaa122000e3f655cf6444001dc902a94c3900032f9d8431091000677414e3b028400e6d851c56210001cbd063aac0188034f997744c8100072e284a730e6000adc83591630400197ec8b96c6880023fa1f6550e10006afba8e6a026000abf845d5608c4017cf04a1ca3880039b90b65085100047ec3eca1962000af4814c061508011f902b80c6a90033798e710c
  | 39 => 0x15f700b14c018802ed61032547100057b408e030a8600ced7690a2194001cbccb31a64080071f1d56510c10006e6210e6a14a001c7e7559442040015bd03b94c6080029f60f74594100069e42ae8194a002b7485cc9514403b75904a1a84a88039d59442440100074f43ac8b182015cbd425d842840019ed033b065880023fa1c42984300063fbaae8b044200a7f855c5600c801c7acab9cc808002a7e117218d10006dab20e2a1ca200afb805086054401d730021ac1208023f2057018d420057bc0a8030a6400e5e6594e61cc00117b0e3206488052bba0a31185200066e31ce3a122000add861cd42040011fd0e2a4c2180027da06744c3100057a40a65304a200c7d755c261d00018f8edb2c8488003975d463c81100047f436e4a826000a7d869d6418c401b3906ba06528002af21942905100a736c286430a4000cdd8718f20440018fecab8062a00031f99175087100059f4206528aa200cf4311c560108018facb39e84080023fa1c3258650006f5b12e02122000e9e649ca63040018fee9b2864880031fa1f6510d1001d3f42865304a200c7d751d661cc0011f90cb8686a88029f60a73d951000756ba0c83122000e9f64d8f3244001cbeca31c64880031fd9573191100053ec28e730e8000aed8090d62040015d902a1ec488002f66007218d10007673a6c7b122000e7965d0140040018fecb3988288002eba1073588100ec7ec3ea330c8400cbc421d94244001be30138e41880023f61f53582410075729ac52088000b9c845c86344001cb8ca31886880027e6027190b100065e3b28498a8000cbe645c032040018fecb3a46488003375d8430c8100057a4328528e2000a7e859c463c4001cde423aac1108031fd41760ca500047fc3a85b0aa000c7c851d9304400173b08392c608002f920943841100063fb12eb20c62049f58794641c40391fd0e282c019002af6103298443024be42ae021e2004c7e7559642c4001b5ae9a1065280033b5977250c100074ea02e231a8400c7f8759643040019d865b82c418863790ca71c81100063fbaceb3086400e9e5319330440015bd0938cc608002b720d71580430056ec1ca931e200187f8759720040017a902ba4c608002bb61842cca100066e31ee0a1aa000abe8494560904018feed32a64080039760e7598730006af2a6e6a14a000ecc211c46350801d9d0531cc408003a71907218d1000676ba6c518a2000e9e5498c41040015b906b126108003371d86350d100a677390c328a40008fc865d32044001cbc64b2a64080034fd94744c540006ce298e6a168000a7d85d9064c40015dd0c39286880027da1a7110d100263e3aacba162000cbf761c96404001af70ab8062180031f9d865d0d100074e320c7a1220179ee829d943c40011fd03b82c5298537a94970084100063f396cb21a2
  | 40 => 0x72057298c10005e6412e8b182000c7f75d09600c4018fb0fb2884880023fa1c32580310056f41ea130e6000c7e72d9463440015b90aba4c6080038fd964350d100066f39ec7b12a200e9c6418c32440018fecb38e648800397d9763d09100065ec24e3b026400db7429c740440019bb0c39a85080039b082751852000677bb4c59902000e6c7419462440014fb0d21aa5280033edd842440100063eb2ae73102000c7d625d763c4001cdacb3a4c4080026f61e5310640005ce41a8420c20009f4815cf4004001d38c831a6488002bba1b43d89100066e31ae129a8400e3e6599332040017b706a162108002f320d42482100071e32ec89922018cec329db20440011fb0f318432800e3fa1e61543200074e320c6a1aa000e6c425943204001cbeeb29ac11880337a1a7390530024bf42ee710e2000aed82d9462c4001b5cc83928728802ed21132545100053f428c530e6000c7d751d56008401d5906b22c4080032fd96740c8100047ec38c6212a0008ff874c9600c401cd905baac1108023fa1e41582310066f430e6a12a0008fd87d943284001c7e85b288488003975966350c100056ec30871902000c7f651c532440014fb07396ca880032f992710c8100051ec2ce23226414daf205d03204001978e8b22c4080032f5d954cc740004fb40ee0a1e2000d3e7494c3254401b3ee9b1a6488003ab60c64189100065fbb284a8e8000bcc8350a51c8001be30038a8188003b318f32c8110007b2a8ec4a962000c7c72d9540440355d904a1acb100033b1da42545200066fbb2a6a0e60008fe861d132440019bf07bb284080033e5c07098443006f4a12e010e2000c7e759ca61d00019e902b80c2a10aadda1432841100047fc32e12086200cf6861c520440078f8ebb2e8508002af6085159010006bc42ae018e6014aec8250c6148001c7ecbb2686880035d5d671d93100047ec36e0a1820008fe871d932040018fd0b3b08788002b7e0d42980310055fc22e030a640397e859c732840015d90c218c488002af21132983310063f43ecb212200497e85dd330c40011f90eb2a84080035ee1570104100057b40864b066200c7f75591600c40173b07b96c888003abd9362d09100066e39ac6b14a000a9e83d45640c8011f90cb9884880031f9c775582210063fbb4ca1902000cbc7319320440019eaca38a84080031fdd965d08100057641ac59002000cde705c063508018fee6b284208003ab20d6250040004dec3ca72088000be78250f1004001ceb0a30e62900036719073509100057b40ea53086002a7c855096194001d3ac8b1884080038fd9742905100072f32cc61902000e3e401d56010401d9ce8b1ac4080031f5957210c100063eb2ee4a002000af68110d6194001bb2eab806218003371db635091000736b2ac42102000f8f43d08325400
  | 41 => 0x1ce928ca01ccee861c94394001abce7194a3280039ee1560180310056f40ee93182018de4629c432440018faeb324c3980039b989658c8100057dc02e8b006200abe840c9650c001c7ecbb228488002afe1132982510047f430e6a962000c7d65dc94304001cbecbb186488003379cd30185520071fc2ae03226400c7e7259743040052f90ab868488002af2113258430006ce41ae81922000dea429c03148001b5c8639286880526f61f43d081000757438c83122000ee4321842154001cdecaa104288002b7e0d42d81510063eb2ee69002000c7e76d9532440015d904a1ac1988031fd9674085100067b38cc33008600d9e64dcd4204001db2a7b04c018803675907350a100065ec24e3b028400abc815c0644c80137908b9cc4080039bd9543189100066f438c610a2000cbc7399021040015f30c2142008002b720d6454f100063f3b6ca21220008fd869c63294031bd3003928688002af61b43d08100065fc22e030a86008fd870c960104313f10e9824088002ee21132c411001cbe42aed994201dc7f52dd951c8001d5ec9b126488003abd93620c910004bfc3a8728aa200c7e72d964144001d3cc931c84080027da04740c5100056e41ac918ca000afa809856010c014fb0d3ac8208002f320d421091000737b2a8510a2000ced821c5608c8016d904a1ca328003671cf43508100071eb2ae4b202000cbf7659142040092fd0fbaa61880036b5d3420c910006e7b9cc4a1020009f48750b10040018fced2a064a8803379d463109100065eb22e020e6000d78655c032440013e902b8464880023f6007358a540066ea9eec18c4000af68114e6190001aeb0b38886880035dd46710ca510047f43887b02a200c7f859d832540013b906ba24188003a72096498c10006cf400e6a168000aee83d8b2044001c7ae8b2864080023b6187250c1000cbf42ee81882000d6d651c94304001cee833a8c2900035d1967110d100055f408a0b2064008fd8710e60cc401baaa638a61880125f21570ccb100055ec10a7b222000e6c7359662040011fd0fa8ac121003b398a63908100063f192eb30886008fd801d942544011fb0e104c2218036bd95740c9200065ebb0862142000c7f75d9130c4001cdccb3166408002be6027358221006f2a10e29062000aed82d456090c018fecaba640880034f996740c8100263f3aecbb1e2000abe81d4d64040018fac4bac82188037594c714c3100055ec2064b288200d5d851cd42540011ff0cb988508002af2194250130006bbc28e2992a200cdc7518d40440014fb0a194c3980533ba187250c100065ea10e2b068600aec83146620400197d08bb086080031fa1776547300071e32ec81922000cdc73185504c06bf188421864a80027d20573481100065f3b68529a8000e6f7554960884096ed0bb24a388002b
  | 42 => 0x953004001d9ae931cc408003578c1759043100736b2e8419020009de839d942440013bd07ba443880029f61720580310063ebb2ca1902000a7e859c9600c40137908b9843880029f6177098730004ee41ae92826019d7875cc130c4001d990eb1ac4080032f5937258c10006e6190e6a864000e3d7550a61d0001cbacab1e64080029fa1432583310057a4328508220009bc845d932840019bd0e31e808800a9fa1442586500153e42886b0ca000cbd76550410c0018f864ba8c2900023fe1d32982510065fc32e81942017dac625d032c4001aeceb38ec7880031f21d65cc81000773210c398a4000b6c8250d51540019dceca10858805e7b209744c31000756a1a8430a4000e9c6418e43440018faea3aac0188026f21d4254e410066f3b0c61922023cef7690951884295df0b210c29008abda0775987200a676392c49802000abf805c4644c801cdecbb9ec4880031fd49760c6500053e422e7b2a2000cbd8710d60904018fac9baa618800b1f9d765d0d100075743cc93102000c7d755c26110c015bd03380c6a10027e600748c7100263f3aacb1962000cec211cd621040137f08b94c6080031f59773508100a676190e2b046400e3d859c6648c0018feea992c0188023f602711913200677c2aed1084000e9e425c4635082f5d904a1ec090802f320d42c80100063fba864b006200dd5539c730c40018faecb2c64080029f61641185320065eb26e6b102000ade8414863440013bf0ea98c3980023f6187350a50005f240a86b102000e5c301d5600c4019d904b80c2a100337a0c71580320047f43864b008200ade83d46610c8011f90cba4a2980039bdcc65189100055ec38c920a6000be68110f62440018fd0c39aa4a88037594e71cc31000677310e99802000cdd535c06350401d3ac8b1e84080026fe1173c801000767c26c7b122015db9425c042840019b906b84c2190023f61c6310510006ba3a8e29822000deb625c03244031d5d08192c1108031f5957010c100071eb2cc91902000cde535c06350401ceacba122008003379c47018d420063e3a6ca1922000cbc7459231040015bd0428cc6080572f981740c810004f7c12e63262000cdc7398550cc0291f902bb084080032f10c71583430065fc22e130c8400c7e635d720c40091fd0dba2a1880033b0877654b30006ceba6861942000be4814c8328400137d093b265880071f1d565d081000677b94e530e6000aef8250d6194001cbacaba4c608003972157018d4200d3f42c64302a2009de87d9131cc0018ff0ab84c321003a720b64d8d10004de422e69062000cbd861d132440011ff0e992c1288065fa14748c410004dfc3a8621e2000e9f6350940440014ff0ab9ac1108023fa1874cc1100072fb2ec69922000cdd7318c62440015d907a80c488003379cf63d8950004bf4
  | 43 => 0x86880031f99473500100063eba8e730e8000e5f65d8e43440019b8c6b8462a006abba0b64d8950004fcc00e910e2000cdf76d9131cc0032f90ab9a4008003ab21f64d89100063eb2ae79002015dae625d03284001d9cc72124008003a7591634c81000737282a430a4000bb7844ca10440019b8c6b8086880023f20570191530055ec26e6b044200c7d851c5620c00157b0029ec888003a7591630c81000736b2ac41902000af48150d61cc0013df04ba264880027760f7488610005edc1a848802000ecd5218f2044001d98e931ac4080025f61e3294551006cf3a6c619220008fd861d33204001ceaca99220080039b595624c8100066eb1ee91082000dcc73d0942440078fcebb2c8508002f3a0f74d89100072f42ce231a8400e75650c910040018fb0b38cc910003a75027018d420056ec3087194a217aec8250e61880015db08190c29005ebee017158032006ce39a86a12a200af5860cb1084001d5b05324c408003a76117018d42006bab28e29902004b5e85d8e53c40319db0c39286880131f9d56590f100074f324c7a182001a7e8590c60544019bf06b84c22100337e13764c03000767398c63122000cdd765d4318c00197cc8b8483980023fe1d4358251176ce190e89942000c7e7259441040018faecbac82080038fd9643905100057a40a87b0aa000d77711d540c4001cbceb29cc398002b7a0f65d8f100072f3aaa730e6000dac835cb41904011fd0fb2a84880034f9d242946500066e41ae031a8400daf641c943540018bceb31e40080038fd9643109100057a4326528a2000c7f855c263904019dcc539882080023fe1d30185420074f3a2e231a8400c7f515c063548011fd0fb22a788002bd2054398430006dca12e12082000e5d6598c42040019bd0e31884880027be1d320c8100063ebaac530e6000c3e655d032040019d8ed9926488003b398f43988100063eb2ae69002000cdc7598c41040011fd033b064a80038f59454590310053f426e6b282000cf4711855048001b38e831a64880023f20570191520079aa88c92a62000af6811d661cc0013bd073b285880029f61774185200072eb2ee93182000e6d6558b420400197eec39ac80800375a047350b10004fcc00e7108200097d87d0e51544096ed0a31ca3880032fd95740cb100047e43a853086000e9f845c463508018facab988208002bda0774987300063eb16eaa062000e3f65d9043440011fd0e29cc320002b76007218d100065eba0e8b006200cfb76d0910040052fd0b38e84880031fdd54358221005f940c8688020008fd801cd62d04018f8ea392c0208031f9d663c8010004ef418e2aa260008fe811cd6294001cbecab90c6880036e10d7010a1001cbe42ae021c20008fd8718730480018fecb3a664880033798d7090c100056fc32a6b006200a7c875
  | 44 => 0x50005cec24e5b1a2001c7e7559543040015bb0bb80c6a10031f995700c8100043ec3eca1922000c7f65dc1424400187eca3a26488002e720d420c7400069e3a486a92a200c7d635d641c4001cbe64b2864080036d95271d01100063f3b0cb9922000cbc7650d42540019b8edb1c86880031f21d65d0c100056f418e2b008618aec8254d6088401cbccb394c6080031f1ca65590100057a40a8530e6000abc844ca61040018faca38a8608003375d67198c100066f3a4c790020008fd87d8a31540018facbba240080027ba1c3254120004dec24e7b12a000af9800c960104018feeb21ac0188031fa1471580420066ec38c7a022000e7621d94214400173906a1082180026fa1e644c8100076ac18c218a4000a7d858c560884013e90e99621080038f5d464c8110006bc42ae018e2000bcf825d06344001cbceb3184208003ab55162906300067dbb0648802000c7f65dd22144001be4e2b86c788002be60071d81420053f43486a8aa000ecd8718c62440019f6ec99220080039759773508100047fc3a8030a4000be98010b3284001d5b06b22c408002b760c5198c100063fba0e8b282000cdd7318c414400195ae9b1064880038fd9542501300063fbaceab006400e6d654c8320402b3dd05ba4630800e3fa1c6154140004de422e53182000db6439c74044001d3ec9b96c688002e7a107298c10004dfc3a8518a8000cef651c94344001b3ae831864a80038fd94648c9100053f43eca9822000c7c515d83294001cbccb31c8608002b720d42980100067cc00eca162001c7e651c550c80019bce431882880731fa15760ca50005f940c8488020008fd869ce51084011ff0cb9062080023fe1d435822100cbf42ce22182000c5d65dcd42040011fd0e312c018802f520d4254710006ceba2c61902000cce631c94304001d3f06b22c60800b1f1d7654c91000767906e231a8400e3d65d9254c40014ff08b96ca880031f19473501100047ec36e0a1662008fc87509619400173f06b92c80800a5fa1f755011000757b9cc93102000ead42c816010401d3a87388c6a1002bba0f50189100063ec3ecb2122000be5820c42184001b7086b848208002b7a077518d420072fa9ca730e6000cf5861c543840019bac7b8284080023fa047650d500047fc3ac928e4000b9c8350950d00015db04318c588002ee60272d91100edb641286a92a200af6811cc61480011fd0c39c42880030f195740c9100055fc3285a002000c7e7259664040019ee8238ac0190031fd9673d91100063fba8c2a026000ade85dca63040019b8e6b1ac4080023f61b74cc0100071eba88730e80008fd86dd22104001c7eeaaa2c020802af61062594310071ea0eeab008200b74814ca51940018facaba24008002bd205431815100737a94a4b0062008fd869c44294001978ec322
  | 45 => 0x497e859d130c40019dec4b8064880031f996710c8100063fb2ae9b1a2000c7f659cf62440018fecab96c888002eba1373d89100074eb22c72182000cdf65dcd4204001a7ae92a06528056bb20943d85200065ea0ae03226400abc8650b40440013ed0339a4188003b9e0c614852000676c2aed1084000dd6631c54304001cdacb21ac4080033761c63085100074f324c6a102000d78855c041040019dcedb166488002b720d624c5400056f404e231a8400ade85dc06344001aed0b3888688002afe113258331004fa40ae81942000cef73d8940440019b8e531a60080627b20973d01100063f32ce72102000bad840ca2144001d9cc73128408002b5a047018d420074f214e031a84008ff8759231940014fd0c214a0a8003179d6638c41000576c26ecb1020009f9809c643040016f3012a265280039b18b65109100065fb22e7a022000e6e65d0d620400157b0810ac0208029f61273d9510004be41ae52a4a000c7d75d9363c4001ceaca2086208002de602540ca500063f3b0cb21a2000a7d85dc7604c80197ae8320c6a88023f21d32987300072eb2cc7a102000b9c835095050001d9ec6a1ec4880063f21c61541400072e98aeb30e6000cbf845c2610c8038fceab2c84080029fa1875501300059fc226528ca017aee82d9362c400179f04ba2c608002af21153582410047ec3eca21c2000ced765884204001d9b05380c6a10023f60071588430072fb28c79922000c7f855d843940015dd06320c4880032f5d26498a10006eca9ae118e2000c7d655ce64040016f30129c8528003179d6630c8100163f3aeca1922000cdf651cd42c4001b5ea2ba06510803731cc6250b10004efc1ae890020009f6870c951c40018feeb30a8198003371d463d011000767902e231a8400ece82d8f62440018faca39a4008002bb20943185500063f3acc71882000dda535c231c400157d09b2ac018803a7d9063109100057a40aa830a6000cdd731cd60904019bcc6b8684080027e205700ca100045ec30e899020009be849d93244001ceacb1886208002bb61843588100055f42065304a200af7814c061508018facaba46208003b990861085500057ac30868802000cdd7398f40040019bcc738886080031f8cb75580410072e32ae831a2000bf1801095144001cbcea31c6288003971406394f100057cc00a2b0064008fe861d1204400197ce8b246308002d7e0d42945510066e41ae030a8400d9d7498c32944014ff0aa06c099003374c776508310057ac08a0b048600c7c655c032440019f2e0380c2a10027be1d42109100055f426a030a8000c7c855c06348401c78a8b22a39800337a0c71582320069e2a2e931ca000c7f659cf404400197ced38886a00027d21d32440100053ec308728ca000ade8610e3254001abf0a39a852800a9f21742586
  | 46 => 0x97e853b08588002b760c5298c100069eb2ee89902000c7f52dd953904015db0638ac408002bb60850986430053ec28e2b006400a7e869d6414c0019d8ec31284880023fa1a7110d5000766414c79002000c7c875954204001d3cc93188608002afe1443582410059fc2264a8aa00397e85dd330840052f90aba260880027d205744c2100063f43ecaa1a2000c7d859c6648c0019baa7bb285980023f21d4318520006e639cc4a14201aced861c94354001d3f04b22c608003a750c4398331005da40a87a142000afb8050c6054401b988639286a80029f20d74d95100047ec3cc62142000db5549c740c40011f90ea00c2a90023f61c6310a100055ec34a6a1680009ed82dd231840012fb0f2a464a88032f595740ca100047f430e69022000c7f725d661d00019f6ed21a20080033be1d52987200047fc32e121ca201a7e850c861540018faed2988728003a7a0e6498c1000737b2ce7b122000e5f315d661cc0013bd0e31a8488003abe0e64988100063f3b0cb1922000ead641cd62040011f90ea1ec0a8803a720a6498c100057743487b122000d6c65dc94344001bcee5b8a87080723f21d6358a50005d6c16e7b222000df1809c730c40018feecb2a64080027be1d431891000577424ec3122000cdc7358d62840013f3013a4430800337e0c7650d10006b7212ea30a4000eaf6490f6244001d9cc621cc4080029f61470185430063eb2ae1190200397e85dd221840014ff0ab9ac120803a7a0f64d8d100065f3b28621a2000e756550f10040019baed31c84080031f59175d8f100ad76412c8b142000cbe74d913044047d5843a8ac8190023f21d4258031007663a4c73102000bb6840ca10440011fb0e2a2c1988031f9cb658c510004dec3c86214a200cdc631c54344001d99043184288002bda0775987300056fc2ae031a8400eae875916204031b5842ba064880023f61c53582410a676192ec21020009be84dce21840011f90ea14c3280039798f754c3100057a40a813088600c7c42dd5608840197aeca1680080031fd9674481100047fc3a8530e6000ee432d842154001d6e8430862a00032f61f648c5100063fba8c69862000abd84dca61cc0011d90ea1ac4080032f5917010431005e641a8410ca000c7e755c26110c01aed0a38a40880030f9d7648c5100063f396cbb222000e6c73d946244063af0a6382a398003b361063d89100055fc32842086200cdd8798c21040315d904982c11084a5fa1e5450a500ae7dc32e01082000c7c659ce4244001ceacb21a200800379dc87150e100c6f3214e39022000c7f651ce2144001d5a85208c290003375cc63c81100055fc3284a002000c7d759ca61cc0019bce931a6008002bb6007358b410071fb2e85a022000af98090a600c4011fd033b086a800e5f2157610e100072f32ca730062
  | 47 => 0xa18325455000736b28651082000abe84d9661cc001abc64bacc2218023fe1d43d85520063fb2ae59822000cde629ce518c4011fb0e214c3980029fe1530987300057b408ea30a8000a7e859c66390001d3ce9380c6a1002b72017518d420075721c8430a4000abd84dc7604c801d3cc6a108208003a754f64cc1100072e3aac6a0020008fd878c061508019bae730c8398002d7617740c6300047e43acaa106200cbe841c56010c018f90ab84c3210023fa1f6550b1000676192e030a6400abd840ca600c401c7cc9baa81880623f61f628c510006cfa80e6a168000cf5711c7604c8015790ca148298003971405418d100073ac2cc218e6000d6d750c861480019deed992a3900039b59662cc8100056f42ce331820009f9809c443c400157d03a82c819002b72097018d100e677392c518ca000c7c659c432440015f30132cc0188033b5cd620841001e3f3aecb1942000cbe849c7604c801d3c83388c6a10031f596744c810004efc1ae8990201bdac825d032944014fb0bbb286880023f61c325834100736192ca1082000abc845d560084013f3003a063880031f5d643185200056f41884b0ca600e9f6418f424400197cec32064880025fa1e544ca5001c7f438c2a8260159ec825d130840011fd0faa4c3980029f61641185200063fb2ce63122000e9c8418f4044001c78eb2a2c1208039bdd265988100073c42ae031e2002b7485509514400157b08192cba0803979946394f10024bf428eda1e2000a7e8610d52544019ed023b28788003a710a7118d42004ef41ee520a6200af4814c861540016e902992a2a80031fdd9650c810006d7ba0c499220188fd869c632840019ed023b285880027e60273886100063eba8e630a4000cbd7610f40040018fecb3a660880026fa1f4350a5100c7e43cc2a864000cdf83dd9430400197f0cba065280039b5d552987200056fc38a9318200097d8790e51544019bb09bb262188038f6167119132007373a86430a4000a7f855c261d0c015b90ab80c6880037a0c9708871000677414e3b026400afb8050d600c4011ff0eb2887880023fe1d650c8100072eb2cc69902000e6f21dd560884018fe64bacc22180397596630c810005f8c0064a8a2000cbf64dc930440019bceda1c64880032fd927110d10006ec31ae02122000c7e74dd560884015ed0231ec2900027be09744c3100066eb28e6a142000abd879903204001abccbb9a84080027720d741891000677b14e219220008fe87185404c00177300390c8880023f618740c410004fa40ae12162000e5c855c06344001cdeca31684880023fa1c4358430004fb40ce89942000cde7518e424400173906a12a3208038fd977319110006bd3aae1b1e2000c7f75dcd60884018f8e5b2a86880027d20574481100063eb2ce93102000e5e6598e420402f
  | 48 => 0xe4a1ca200d9d851cd421040157b08196c0a88031f15176086500057dc02e2b008600cdd7698c4204001d3cc62188208003a7a0b64d8d100065fc26eca182002a7e859096194001d38c9b90c6880033518e71cc1100047f438a4b0062009bf845d932040013e902b9087080033bdd873588100056f418853066200abe840c960cc4018facab86640800277a1e6350810005ea40ae8b182000e6f651893244001ba8e7b8a84080034f596740c81000736316ca1922000cee629cf40040019bcc6b848408002f320d74588100072fb2ec72122000e6f7399662040018f8edb2a6488003ab60f64d89100063ec2aec1902000e3f855c0644c4011fb0fa88c6a000397d967218d100072eb2ae8b182000e5e5094d608c401cdcca21ac408003a7e0a6498c100065fb2ee8992201cbac8250d42940019baed31886080033b20b7650c10005f44128708020009f681dd330c40018fce4b286208003abd9362909100056f426a631a2000cbc76d9342440391f90cb94a0980031f9c9650c8100053ec2e4130e601a8fd87d8f6254001d58c9398c4880031f99473590100047f436e8a8a60009f4815d1320400197e8538ec0a1802afa10625973000766420c63122000cdc7298d4394401c78cab9ec8880032f19170905300063fbacc6b0442008fe8710b60544014fd07ba2ca080033b0847358b40006af2a0e6a14a0008fc865ca53c40019bc63bb2841800f1f9d76590e100057cc00a4b006200c7e325d661d0001b5ac9b928608002bda0443584300074fc10c831a2000abf8650d429400137b0f21884080033b61f628c5100066e41ae130c8600c7e7619642440015ed03990c2a8002be60032584300c47ec3ca2b044200c9f7498d3204001d3a8621ac2180038fd9742501100055e43284a022000e9d82d9363440018fb0fb2886880023fa0473588100063f996eab008200abc8650a41540013eb0e21ca2880031f14f76547200047ec04e231aa400cde631c5420400179906a1042880026fe1173085100065ebb68520e6000de7321c520440011fb0e21ec2a80032fdda64908100063eb2ce81882000a7f855d1600c4011ff00bb687288032f90b76508100057b40e85b0aa000cf6819d843c4001cbcc6baec78808e3fa1a710c9510063e284ec10aa0009f4815cf20840015b906baac0108038f59664cc8100057cc04a4b008200bb9840cb1084001c7880bacc3a00035ee15700c4100047ec30e6a8e4000b5e851c963040018fecb39c8288003b358d628c8100047e43aa630a8000e5d65d0e320402f75904a1e85880032fe1576904400a67dc32e01942000c7d75d8a31c402b1ff0cb8064080038fdd74258041166cf190e8992200097c8750d5254401cbea22a4c6080039719763109100074e320c72122000c7c859da515000179906a1442880029f
  | 49 => 0xa51104011f90eb2a85980039b5974290810006da3a0e299420009f5801c54294401ceacbb8a64080023be1d43d8910006bbb88ea9822000acc825d06344001d9843b80c6a1002b7a0c50986430ac7f434e31922000cbd7690c41940011ff0cb9087080023fa1871509500053f418e4b282000af681dc0614c8017d704a1e20880031f5957290631006ea31ce221a2000db774dc5328400197ae8ba8c6a105f3b1cb624c3100a6d6412e81902000abc845c5600c801d9e41380c6a10031f5d762987300072f182eb30e6000cbe8710c6150001c7cc8baec9880032fa0f7650441006ec31ae01922000d76859c730440019bcedb1886880027d20570cc9100047fc3aa6b006200cdf76dcd4244001cbcea31e408806b6bc81740c9500047ec30e2994a000aed860c96088401d38c831e86880036d90c7150e100072e328c71922000ecd82d8f624400175b09b9ec488002af60670191320071ea08eab008200b3e840ca5194001c7ecaa1a8488002bba1063189100063fbac84b006200e3c65d934344001ceaca21620080023fe1d65d8831025ba42e64a8e2000e3c54591510c4017cf04a1aa288096dea1432840100047ec00eca1062008de831c5601080197b0b3b682a00023fe1970cc810005bcc04a6a14a000d9c73d0d42540012fd0e21aa2a80033dd947150e100057dc0264302a2009dd861cd42040014fd0a384c2190033754e7198e20006d7c2ae5a0a8000c7e72d9464440435d904a1ec0a90036d59071508100055fc226430aa001c7e7559632040018facab8084080031f21d6590c10005d6c206528a4000cee765d062440013b906ba24108002af61e6490631004efc3a8621a2000cde539c663880015b90ab94c6080029f61770987400066e190ec9922000e5d6598e43040015db05324c408003b554e61cc7300055ec16a7b222000ee54218421540019deedb9286880031fd9471501300075743ec9b1220008fe81dd932940014fb0a192c0208023fe1972104100063eb28e8188200397c855c332840011f90cb8664a88031f9d570185200063f43eca99220008fe8708560104014db0a190c2900633b10a760c9100066f186eca106200e9f6418d32440018facaba46408003b35ce63988100053ec2842b008600aed8219462c40017e50221e20880031f6167610f10007663a0c631220008fd809c46355001d986431842880029f616311854200767b1ec421220009f4815c032440015df04a1cc1988033798d700c621004df43e86a102000cfb87580600c42fbc86538e41880536b989740c8100055f430862122000b75859c44344001d3ae9b26c6880623f602768c9100e676192ec10ca00397e85dce21840018f8eb392c018802f920943c4210004dec24ec9922000e6e425944204001cbccb31e86080027be1d4398810006d6b2
  | 50 => 0x2880032fe12760c9100075641cc93102000a5e851ca63040013bd07ba443080032f5d06418d10006f9c04e21922014cef73588210400167d08192a2a80b6dda1432c4210004bf43c86a92a200c7e63dd56010401d3ac8b1c84080033718d70109100063f3acc61082018bac8250d424400157d08312ca18802b7a075498c100066f430e6a12a200af48150e61cc0011f90cba26088003d55446394f100ee77316e4a8c62188fd809d84244001af4eab846208002bee0132580310053ec2ce4b006201c7e755964304001cbecbb1e8688002af6103259731015ba42886a8a2000e6f6590c62440015bf06a14c1288039d5964244010004df424e7b1220009f4815cd20c40019beeb388c6a1003b9948610c5200065fba6e6b048200c7d655cb40040018f90b3b482880023fa1c42594310047f43ea93086000ced821c5600c801b6e8538e81880d397140630c55000756b22e6b102000bd88350b10840015f100a0ac0218033761c631051000767ba4c6b102000bcf825d26304001a7ce92986528002af61032580430c6763b6c52122000add83152630400187acaba0640800337dd87458c100056f41884b0860008fc8750c61548017e102994200800337ddb6454c310073cb2e6098020008fe811cd6295001bca8538e40880039719763d09100071fb28c999220009df835c864440018fac4bac83980038fd0b65909100c6d6314e81922000a7e8690d5254401d9ca531842080029f21932545500071ebacc81902000c7d769d64184029bd064b8042080031fd9673c81100066e31ae19922000cdf835c0615080197ee930aa1a0003aba086418910004ee41ae4a046000dea525c031480018f90ab84c2190026f2117308610005da42264a8e2000eaf641cf6244001cdea5294c3980032f9087650910006bcbaae120820008fd8710a6094c018fce4328c6880036b1d3324c8100063ec2aed18820009bf8750c43840019eae238ac021003971d553580310045f438a0b206402c7d711d5600c4015bb07a80c6880023f61b70508100063fb2ce910a2000e5c7594d600c4018ff0eb2e84080023f61f2098730005f24128728a2002c7e75d9443440014fb0bb18c7880031f14d760c6500063fb2ae81922002b76851095144001d9ca531c4208002be61832840100067d38ae031e20008fc865d032440018fecb38c8688003b30847018d420056f416a831a2000cdd7398e6284001cb8c6a1aa2a80023f61c53185400066ebb2c6a1020008fe87d954284001cbaa7a92c018803375d77018d100067cc04ec2162000cdd30dd9420c0018f865baac1108039b48575185200056e41a853006200e6d65cc920040011fd0fb2a65880031f90975185200066e3acc718820009bc845cd20840014f90eb2a80080038fd9643d01100056ec00e831a20009bf8750
  | 51 => 0x57a40a6030aa400baf845cc624400197907bb28220802af6036499031005b7428e6b102000c7d759ca61d00019bcc738c87288027d60071508100067bb8ce2b006400d9c511cd42d00014fd07b12a2a80039b54d5258221024be42ae1a162000e9c6418d42440019bcea31c86880039b59542108100072eb2ce4b182000e7565d0b100400157d0c21c82880038f5465418540006ae98eeaa066000c7d65dcd40040019beeab80c6880029f2157018f100066fb1ae018aa000ade839d661cc0011fd0f18ac1108031fd9574d891000576c1eecb102000c7f651d12044001cdeca21664880038f61671990100047fc3a853002000af6810ca610c0013bd0638a80980037954871481100056f41842b00620397c855db4284001d3ac6a148208002bde193158031004de422e63162000e5d65d8e53c40019f6ed2122008002eba1273d89100066e3acc6a102000bb9840c91004001c7cc8bac83880031fd9573905100047f43c6030a8400e3f759516010401c7ccab208408003975977458c100071eb28e89902000d9e641cd4204039b5cc4ba06528002b760b7658c1000677bb0e4a1e2000dae431c943c40018feeba1ac0188036720d740cb100067ab8cc329e84008fe81dc16210c013790ea12a6a00023f61f6510c10004bfc3a8728ca000c7e7259730040014fb0fb2c82980031fe1d658c8100069e3a486a94a000e5f32d96324400179906a12a190002a720d42987400056e40aea31a8400ece6350d620400193ce931864080032fd96740c910007ab42cc398e6000cef76dc94304001b3ce721ca3a0002be60021580310056f41ca2b0062008ff865c032944011f90eb2a86080033b9db420c910006e639cc4a102000add87152630403ba7ea4ba064a88031f1c965590100059f424a6a14a000e5d6510e3204001c7eeb21ac020802afe1943d0810015bb4286528a2000c7f435d46148001aeb0b38887880033d5947150c1000767438c63122000abc8350a61d0001cdd04ba8c2900033be0970984420066eb9cc61082000a7f845cf6544001978edba26408002bda0443984100063fc2ae031a4200cbc83dd9401000157b08312c018802b720d42d81510073b42ce231e2000e3f6550c434400179906a1085880027d205708cb100063eb1aebb262000c7d65dd13204001cbf0aa9ac0188035e21570887101d7c621086192a200b3f855c04350001d9ec7b168488003179d663084100065f3b4862162000e5e6598d42040299d884bb064080023f61f65109100065fbb6e89922000cde76d8f42440015d906a90c2900026f21f644c9100065fbb686a102000c7d625d661d00019db0538ec0a1803e3d0f420c951006cfb20e6a122003c7f711d5608840157b08194c2200039b595629081000677314e99802000c7d651cd40040018fecab9c4
  | 52 => 0xa7e8690951540019dee530aa190002cf6103294551004bfc3a8528aa200b9c8350a5110401be50038a84080039b8cb650c91000d3f4288630aa000c7d855d832944018f8c8ba84388002bb20943986500055e4226530020158fe869c442440014fb0a394c3a000397d9763509100063fba2cb9002000c7c851d9515000197ec8b9462880123fa1b72543100066f31ce3a102000c7d43dd56010c011fd0fb22a2188563fe1970908100071e32ec821a2000ead8759162040018baca39a8408002bda04329865000736b2e86b102004c7e7559743c4001d9b0931ac4080125fa1671d0b1000757b26c4a122000e7565d0d1004001be30038a64080539b5d56208410004f6c30e4a1820008fe861c543440012fb0e214a2a88031fd9574cc9100065fbb2c8a182000af6810c96110001af10ab80879800add21742545100047fc32e928c6200e9e8299263040015ed03218c290002af61271d81320072e32ae431a2000bd9809cb63440291ff0cb8085080031f9d472987400047f40ced2a66000e3f6550a41440019baa6bb06310003b3d8f624c9100047ec3ea630a8000ece829c0635080153f08b94c608002db209439415000737b2ae9b122000ade851d26304001d9ec7b1064880023f61c3298254006773b6c42122000cbe7619343440017770899420080039b9d562904100056f40ceb3182000cdf7698c4204001c7ecba1e84880071f1d565908100063e3b6ca21a2004c7e75d9462c4001b70c8b8084880031f5947350810006cf428e6a168000bd78350a10440018fecb3a6c6880032f1db43509100063fba6cb1922000c7f651d130440015bd0da1c6488002b7a0f51986430063e42aec18ca000e3d42d9442440015b902ba4c6080031fd9673109100047e43a8730e6000a7d85905600c4015df04a1ac2180031fe1570986320063fb2ee0a1a20008dc8798d42040015bb01a90c688002eb2094310d10005f2412868802000ade831d5600c801d3b0e320c68800a9fa1632586500063ebaae630a4000cdc7618f43440018f90b3b042880038f54654580410057cc0686302a202c7e75d974244001d390eb22c6080031fdd643582210063f3b0ca2122000cf4615c031480015d902b1065280026f61073588100066f180eca906200e5e6598c43040015bd093a8c688003975967298c100063eb2ee71082000df2515c031c40015df0ca164008003375d47198c100047f436e520a6200c7d655c0320400175b081924008003379ce3118520006e631ee4a1a2000c9d7418c32440319db0e192c1108032f1db42545400047e432e0212a200e3f6590d40440034fd0ba18c0a88031fe157018d42006ba3a8e29862000c7f659c642440015bd06284c321002ed20572590100047fc3aca21220149ec825d943040019deed9924008002bb608641891
  | 53 => 0xfd0a194c328072db2094354a5000e3f3aacaa102000cbd741d261cc0019bb0f31e4008003abd9043d8910006e639cc4a14a000c7c76dd540440015eb0c19220080026fa1b744c9100065fc32e8192a2009f980dd221c4001f4a8420aa2108033ba0a71d814300736bae6430a4000e6d51549600840176f089962108003a71d16458c1000766b1ac5990200397e859d130840011fb0c38a87280032fd94744cb1000577426a0312200497e87dd540c4001b3d0239a85a00029fe15745822100767c3ac6b102000af48650a5144001cdf0ab86c4880039754f52987300063e3b6cb1922000dea425c221c40011fd03bb28528002e720d42104100071fb28862122000ade83d4661908011ff0e990c0a8803b31097018d420065eb24e221e6000eac831906244001d3ac8b1e86080031fdc275185200071eb2a87a102014cee425d842040013df04b988288002f620d42440100071ebaca830a8000e9d745c063508019f6eda1a20080031f9da75905300047e432e8192a000af6810c9600c4011fb0c3a665080029f60c725941000736b2ee4a182000bcc8350920040019bcec31e64880033718d700c910006daa14e3a022000cbd76d0a410c001dcc85b0842a80033d1c72158043004bec3c6528ca000bac844c832440015df04a1cc2080032f5d06418f100055f42064b2e6000c7d659d032040019d8e7b82c5a08025f61f43946500076731e659002000af5810826110c019ed0d3888688002e720d42547400065fb2ae819020008dd86dcd42040015dd0828cc4080035b9d5620c8100057641286b0e60008fd80dd94294401b98e7a128588002bb20943d8550125bb428648802000e75650cb10040011fb0d38e85980065fa1671cc81000677c12e130c6400df3815c04244001af10ab8063100033b08473588400047ec36e710820008fe87d9542040019bce6980c290003671ce5350841004fb408e99822000aec8250e610c001c7ecbb246488003b3e0a63c80100054e422e53182000d9d7310f40440011f90eb22a3900031f59673908100c66f994ec1922000aef825c06150c015f30120ac0218038f99564d08100063e32ae120a6000c7d659c43204001cbd0b38cc608002b7219530c5400063fc2ae13086400abe84141600c8019eee338ec09906f2fd95740c9510065fc22e130e86008fe811d942540014ff0ab80c2a10033b5db420c8100047f430e99962002a7e8590d61940019baca39a85988023fe197310810006ceba686194a200d3e42dd56010c018f8edb288488002eb61032982210071fb2ae63222000c7f859db2044001d38c83188688003a7e127118d4200773214c31086014cf9801c5600c8018fceb39cc3a00533b0c976c80100066f196ec9902000c6f65dc94344001cb860bacc3980032f5d96490c10004ef43ec8988620
  | 54 => 0x9573108100063e42ae130c6400ecd53d8930440019bd06bb06408002af60750590320047f4388730820009ef825d1308400157d0028ac819002bd61843c4010004fcc04e31962000add83992638400157f0aa14c3a00032f9c8640c5100071eb2ac8a1820008fc8750a6104001a7ccaba064080037654d700c5200047fc3aca21c2000adf8350960cc4015bb0fa80c6880038f15164943300057d40482b008600aad849cf6244001b38e8b1a64080027720d72191100047e43ac89842000ecd8798e62040019bce730c43980033b9d9320c9100053fc12e7b2a8000d3d7494c3254401cdee8b2cc4080036d1927110d100075721ec520a2000eaf7319062440013df0ea1085880023fa0673d89500072eb2ae4b182000e6f659d06244001b70c8b8064880032f99273c80100053f428653086000ced7358b2004001cd8c43288488002bb21942c8110005ae41a8528aa200c7d769d631c40016bf06a14a328003b3d8e43d8910006da21ce3a0220008fc865cf40440011fd0e294c2180029fa1a439415000756a128030a4000add80d4c63440019dec4b8042a80039b90965084100063e21aea30a4021afb805d5600840173b09ba863180029fa1432587300047ec36e0a106015dea801c943840018f8a9bb2a3980623f61f64d8910007373ac8430a4000a7c825cf6544001b6ca938e8188003975967458c1001d3f42865b0aa000ecc730c96088401cbaca39a8408003b3e097118d4200c3e43acaa002000ece635884204001bcac438a64080033b5947250f10004de43a84a868000abe84142610c801cdacba1284080038fd9443905100066fb9cc61082000d5d65dcd42040015f300314c018803379d663108100072eb2cc72102000c7f659cd2044001c7ccab2064080031fe1d650c8100263e3aaca9962000c7c7359421040019bceb31c4208002afa10325943100756190c810a2000c7d659d23104001cdacb2144208003b394f624c1100047ec36e818ca000c7d655c2418c401c7cea32640880775b6147250d510071fb2c872122000bb7844ca5144001cbecbb1886880033798f7050e510071e328c91922000aec8250d600c4013dd0db9286880023f61f20987400063f992eb30e8000eac871906244001aeecb3886488003379d86390d1000737b2e859922000c7d659cc32040051fb0f28ac018803379db63509100071f32ee6b2020009dd87950310c001d3b09380c6a10023f61e6310a510055ec2064b2886008fc8759153c400157d08190c2a80029fa13725941000c7e43cc2a868000c7f7659732040011ff0eb2864880023f61873547400053f428c53006200af6810826110c015bd0630c62a0087abc8350590320073ab2a658802000e9d83992630400157b08398c290002b7a127598c1000676bb2c41902000c7c659cf64440094
  | 55 => 0xcbb2220008fe8718d53c40013bf0ea9c8398003ab99273988100073ab28868802000e9e74d9363440058fceab2864880023f618748c410015bb42c84a8a20009ef825cf40440018fced3ac82880035da147148310005774306510a2000a7d85dd0614c0018faea31e41880033718e7094d420066f3a0c718a2000a7e85dd261cc0018fb0b38ec0990023f61e4158043004fa43a848802000b5f835095154001d98c72144288002bb20543588100047ec38873002000e6c7319462440032f90ab80860805f7990a71c83100055f43087a022000af4864ca51c4001cbb0b388c6a10037398c7250c100067dbb2848802000aee8498e62040019beca39a84080033bddb7250e100076643cc73102000bba840ca1004001cd8c5b2c84880031f9c96590c100057a40a65b0aa0008fd870ca60944011fb0e31884a8803671cd43509100066fb9ce630a8000cee87d89304400197aed32664080031f5897590710004fcc04e21902000c7c759cd6088401ceacb21e20080032f1da43545400063f3a8c530e6000d6f651c943440018f90b3b482a805e7b20973d03100053f42c62b006200cbe835da411000157d08312c398002e720d42545400063eb2ae72102000af48154e61cc001aed0b38887880033ddc671580430055fc3287a1420008ee861c943440078fce13acc3980031f5d7628c5400057a40a64b0e6000eb742986410c0018facab9062080033b5947250d100063e3a8e4b008600ed55318431480018feea21ac018802bb2094318151006f9404e21962000cdc639c43244001d5aa9b1280880039dd96411051000757b2687b1220009bc8750553500011fd0d38c86a80036d90e71d03100057a40a653086000ade8414a630402b1f90eb22c5080039b19543189100047f43ec49822000a7e850c9600c4011ff00bb087288031f2157018d520047fc3aca2182000c7f855c261d0c01ced023aac018802f92057398810006b72a6e4a1aa200e3e655913204001aeeea38a60880027d20572d02100a4de43a86a102000e6d6558942040013e902b966108003b39d263988100066eb9cc73102000d9d74d0c32040019ba63388c6a1002af60853590100047f430e818a2000abd87d0a61d00019d8ec3928608002f9205320c81000756c3cc93102000add83145600c4018faebb84c2218032fdda4350c100074eb22c6a102000d77519c643944011fb0e196c2a80031fdd165084100072e328c79922000cbd651d132840018ff0eb2a64080039d595424401000757324c4a142000ced764c832040013bd07ba2a3188033761873508100063eb28e99802000cde738c461508011fd0d384a6a10023f61c5298f10006cfc08e6a108200c7f65dc132440015e902b22a3900039b9d5628c4100a66f992ec1902000abd840c9650c0034f90a990c0a88031f5
  | 56 => 0x4284001cdecb99264880036e9517010710005da40a87a14a2009f4815d120c400173906a1483280036b1937250d10006f9400e29902000aed850c96088401d3ce721cc3a00022f61e640c8100063ec2cec21aa218ead840c960884017cb0418842080039b5d5521852000677312e1b10620497e851da43c4001abceb3186408002cfe1132941500047ec3ea4b006200d9d7458c32944012fb0a382c2218031f594714c8100067ac30e2a142000dcc431c94354401b9b0239a84900035dd467190a510066eb1ae018e80009bc875095050001d3cc931c64080039b0807558221004eec1ee910820008fe861d2214403b8fea53b064a88025f61c43941500065f3b2e021a8000c7e87d974244001c7acba148208003b398a638c8100074fb20e5b1a2000cde635c0430400157b08192cba0002bd2053018520006bac2ce221e621dc7c85dd951c80018f8e9baac1108027e6007150f100046e41ae13088402c7c75d9632440019bd0638ac021802ede1132440100074f29cc81882000d78855c0310c0015db09b1ec4880031f5d46190530006f5292e11082000e3d655ca64040018fee8b2864080573e9817010810024be42ae89862000e5d7598c21040019df0b3b64290002bba184318910006bb2a0e2a12a200e3f4259442040015f700a0ac0218026f618744c810004f7c12eca1820008fe870c8615400197aeca1886080125fe1d75d9310004ef41ee8a8a6000abd8494a61d00013eb0038a86a88023f61a7110e50006e7b98c4a122000ade81d4a63040093eb0fb24a388002bda0732d855000576c14c73102000cec76cc932c40019dae8b1462080023f21d6550e1000757ba484b044200c7d659cc41040056ed0a21ca288003375cc63109100063eb28e6b202000bac845cd62040015bd0638ac0190027e600714c8100065fc32e81962000afa800856010c01ab8e729a84a8803a718e43105500056f408e93182000c7d659d232040011ff0cb808798803a75027118d42005d6c206510e2000e9e6394c41900014fd0da1aa2a80031fd4876545400066f39a6030a8400e5d6598f43040011ff0eb24a3980028fe1570191320add641287a142000cbe76d9032440038f8ca38aa090003a79907298c100063f31aea3162000d9c811cd42d0001c7ecba1c868800277a047350b31006ceba6c6192a000d79755c231c40015ed03a12c2180033da1a71cc11000767210c610a201ccee425d821940013db053b28788003a75916310c100062f3a8c720a2000e6f73596620402b9dd0c3928708002eda1032c4210005d7416e7b222017dac215d032c40011ff0ea14c1988036e90d70107100066fbb2c6a102000af4814c860544018f90eb2e84080023f219740c550006bd3aae120e2000cfb865c0310c001cd865b2e40880633b086760c9100063f390
  | 57 => 0x288032f9c864cc1100056f41c82b046200cec821d9434400197ec8b988288002eb61032185200063e32ce720a20018fc87185504c0019d8edb9287880038f90165906310063fbace8b006200a7e860ca51544018faeb30c83980039bd974318910004be43a86a94a0008fd87d9231c40018facb38e64080038f5956410810006eb318e29902000abe8610d4044001bd284b8443880032f1db744c9100065f218e2b048400daf745893204001abe62bacc3980029fa1832941500055fc2264b0e6000a7d859c463500019bb08bb462180023f61a744c010004fa43a658802000c7f659cc64440011fb0e212c1288bf678c8744cb100063e3a6cb9022000dcc329ce51c8029bd484b8042080031f9967390410005e641a8510e2000a7d859c463c40015bd0a390c6880029fe1530582210065e3a6c8a862000ecc825c46350801c7acb39ac8080027b21d43588100063ec2ce3b028400d7a709d641c40018fae4bacc3a000f1f9d765d0e100063fa8ced28e6000cde749ca6304001d3ac8b94c6080527ba0b748c4100063ec2ce331c8000cec211cd62950019deecb1264080023f61a7190a500263f3aaca1962000bcd82dd36344001d9843ba8c6a1002b72057018d420056ec18a4b006200cdd7398c41040013df0ea1ac408002b76047018d420dd7641287b2a42008fd870ca60cc4013bb0e2186408002bb61832884100063ebb2eb20a6000ced7650842040018f8cb398c488003b3d097018d420066fb9cc2a8660009bd8790c42540011fb0d39ca3900036b141740ca21146ce190e89902000c7c72595400400157f08996c2a8003ab50821987400066f394c62082000cdc738c560884019baed3186408003b950b61085500063fb2ae5a1a2000cdd311d9420c431bd064b8084880039b1d5625023000677900e6b16821bcef205d832944013f30138e86080027e6027110b100055fc22653086000a7d8610d52940019df043b286880038f99772590100066f39cc328e6000cbf865d0324400197ec9b9a4088002b7a0c21987300c677396c518a2000e6d6510d6204001bd664b8043880033759473508300a57b40ee130e4000e74415d461480018fecbba062880027e2057010a10025ba42a84a8e2000cec21dd942cc001b3ae9b1864880038f5964350c100063fb96eab008600c7e659cf65c400197aeca1663a00032fd917010d100072e31864a8aa000d9d811cd42104093eb0f28883880031f90b75582210063fb2ce9b1220048fe861d150c4001aba62bacc3980025f61e43946500047f43ecaa1a2000cfb865c221040315dd05b26c488002b7a007118d420063fb2ae521a2000c7d851c560d0c2b1ff0eb146308002bbe1843988100047f434e3992a000d5e651cd42040019f6ec21a20080031fe1d65d0c100066f3b0c721220009f5861c5
  | 58 => 0x65ebb4a9208600087f875963104001cdaca312a5880031fd46760c9500065ebb28420ca000e9d74190634400197c81388c8990031fdd77458031005da40a86a142000cbe715c4644c8092fd0b3b685880026f612764cb100072ebaac72082000bad840c960884018f8ea31a60880032f597744c910004fa43a878842000c7e7598f20840013e902ba064080b3671087350910004fa40ae01962000cdc7218d40440093eb0e31ca3880036714c73508410073c906eab008200b75859c443c40058f8ebb2a86880037c94570087100063f3aee13088600e3f6550b4044001cdacaa104208002afa105318540004fa40ae69042000ade8299263040011fb0e194c398002a72117218d1000736328c49922000c7f855c26190c0197908b84c219003375cc6310a100063eb2ce81082000e5c65d8e42440011fd0e29ec0a08038fd9764cc9100d6d6412e8192a000cde73186514c0015b300390c6880023fa1c65587300047e43acaa106000e6f651c94344001cdecb990428800337d977350910004fcc06e710e2000a7d85d9261cc00155b0839ac408002be602755824100672398c290a4000bb8844cb1084001cdacaa144208003971967218d100053ec2ce331c8200adf83508615402bbd30039287080038f9d7648c51000737b2ce9b122000c7f655cf424400137f08b9843880033760c71583430063fbaae8b006200abc844ca600c401d3c85388c6a10039b188650c9100047ec3885b2e6000c7e769d6414c401978c8b8064880033718c714c91000757418c831220008fe869d932440015bb07ba8c2a0003671ce53507400056ec28e031a84008fe87142610c8015ed0321ec2900033bdca72580310055e43287a162000a7d87d9421440014ff0eb2e40080031fd94748c5100065eb2ee89962000e9c63d0a41440015b900b88c6a1002b76167118d420072eb2cc6a102000e6f65cca21440052fd0bba462880023f61b74cca100047e43a6530ca000cbe7619332440013ed03ba665080031fa1f658c9100072fa9ca630a8000abf844c9600c4011fd0d39c42a80023fa1c425873001cbf42eeda1c20009be87d0d42540015df0c9906408002b7a0c75580310066eb9cc79002000cbf645cd2044001d9f043184288003375d963d0c100a67610aec1902000cbd745c4635080157f08990c0a88031f1d8654c9100067ac38c398a8000cdd76dd0318c0018fb0abb482080031fd9570d0d10005e641a8410e20008fe861c5424400197ae8320c5880031f216760c9100065e432e81902022eaf20145640c8018facaba64008003979d6638c41000767420c63122000c7d75d8c61480013eb0e21ca3880023fa1f654c810004fd438658822000e6d659d1620400157d08312c018802eda1032945100056ec18c831a2000d9e641cd42940015d904a1ac1
  | 59 => 0xe6e850c861480015bd05a80c6880027b60b748c41000676c10e2b008400add8714a63040032fd0bba66008002afa1843909100065e3a2c89842002c7e75d9532440096e90a21aa388003376187350a500047ec3ea530e6000de5429c720c40019bec638a84880623f61a710ca10006d7218e4a1c2000d3f65dd132440013e902ba26008002af61843904100053ec2ec8b006200bb48150c43840018faecb2a860800367dd2634c81001cbe42ae1a142000dcd801cd428840167d08194a0a80031f4cb75580430063f32ce32182000cde309c463508019bce431c82880027da06744c8100053f41ce5b2a2000cdf761cd4244001d9b08b1ac4080023f205768ca500063fba864b008600cec76d893244001bcee5b8a8608002af61843108100047fc32e1214a2009bf87590320400197ac8b9e80080034f50575987400066a318e2a022000dae745883204001d3d09380c6a10035ddc4754c3100065fc3ac91882021aef87d40624402b9dcec19442880039718e43545500075ab24a22086200abc844cb6054401c7acbb9cc8080033754f7648730007363aec4a022000cbc649c432440011fd0dba462880039e21560180310072eb2cc62182000c7d7558a315000197a86bb08728802bda07701854300cbf42ee910820008fe861d1304403bb5e40ba064a88036b1d2624c8100067b38cc329e8400e9c7310d6090401d6ac820ca2108038f94254580410065eb24e221820009f4815c332c4001a78a6ba064a88035da1671cc3100066ec1ce3b028600adc835c560108013790ea1262a0003171d4634c1100047fc3a86b006200c7c509da415400176d081922008002b7a147198c10004bf43c86a94a000a7d831d165040019bcc638a86080039d88565084100053ec16e6b2c8201c7e75597430400137d09b9c42080032fdda4350e100066e31ce399220008fd8718c4244001be4e2b86c9880032f5d942104300063fa1eeab0442008fd870856010c01bcee438a86080037ca027110f100046f41ce3b02840197f875d64104001a78a8ba0632800337ddb7350a1010d7dc02eab006400abe84d9764c40017cf04a1aa3880573e981700c810004efc3a8621e2000c7c87595430400157b0628ac8080033720d70185430047ec04ed192a200c7d751ca6110c019eeeca1a2008053b9a0432185200063ebaa8730e6000e9f8418f40440018feea39ac020803ab1d1645881000577430859962000cbc849d832440018f8edb2a84880031f1d1650c810005ce41a8520a2000add86dd4318c0054fd0a192c1288035ee1570887100063f392cb2082000af6811416090c0176902a1e8408002b7a0c51987300065eba4c9314a000c7d659d33204001b5acaba065108029fa1720987300056e42ae831a201acec62dc950c40011fb0fb2886880029fa0f6294150
  | 60 => 0xb0fb2c6288002dd616418c7100057740c87b122000ade83dd46150001cdeca218c4880029f614764c8100053ec28653088600cdd7398f40840018fec8ba8c2900023fa1c41580310047f430e2992a000cbc76d0d42540019deed3128408003ad9526190430005ea40ae4b182000e5f651d063440014ff0abb0868800337d8d748851000676bb28410ca018af9809c5600c801d9d0fb1ec4880031f5da65cc8100074e424c7a002015ced861c9438400173906a0aa6a00533b90976c80100063ebb4eb20c60008fd8718e51500058fccab84a3188033edc27098443015bb42c64a8a2000cbc7319021440019bb0d39c8318803b318d42085100073632c863122000c7f651d13244001d98e9b1ec48800367d907350b100047f43ec8b0e6000e3d6559342040018fced29864a8803a755063d01100065ea1cec21aa0008bf865d0320400176b0819420880033bc8376548310056ec3ce231a8417bac8250d42c4001c7881baac0208023fe1d53582210063f32ce79002000abe840c961cc0018fcedb2a8688002afa1032d85500a4f6412e898020008ff865d02194001b38e7a1a84a8802b720d42982510055ec20653068200c7c87594320400157d08194c2180037a54970087100259f428c92a62002c7c75d9743440011fd0d3a2658800f1f9d7650ca100047f434e3a122000e756590b10040013f30138c840800adda1643545100056ec18a330e6000dbb645c04244001a7a86bacc2218026fe117348110006d6ba6c41962000dad74d0832840011f90eb2a65880032fe1d644c0100e576412c8b14a0008f78758461cc001daacb30e63980038f59643904100071fbaa84b0082008fc875913004001a78a13a6ca1880277a1f6454f30005d6c2064a8240009f4815c04244001bb2a6b8663980039b9d552987200055f406a2b206400ecc215c063508018f8e9b284288003a79d27118d420057cc0465b02a200cdf635ca41440014f90c994a0a8002b760e6498c100056e412e93182000c7c659cf20440018ff0ab80c710803ab0ca64c80100053ec2eeca1220008fd87d9251cc0019deec3a2c4080030f9d5648c4100071fb2887a022000e3d6590c42040015b906b84c2190036720d740ca100074eb1a84a002000cbd429c76050c052f90aba24088003371db63cc910004bec38cb18a8000cde7418c21440011fd023b28418802b76037118d421157b40eeb3086400ead87190624400179906a108508002f9209439471000737baca4b044200aef875086148001d98c6a18c48805f2f50a7610b1000767b1ec52122000e6f65189424400197cec3246488003379d6639081000677b28e4a1c20009df835d06244001d5ac9b9ac4080023f61e6310b100071e328c99922000a7c855c063500018f8cb38c868800f1f1d7654ca100065fc20eca1a2014
  | 61 => 0x4640040000001001800300140260000002008800200040340380005010c00c0020002000c02502a0064059c56a0004078000400900a0000000015000040000065eba0c83122000cf5719866010c019bf08bb46218003974cb650c9100055f426a0b0482008fe870c961950011fd0e10ac01885e3fe1a710c8100063fb2ce831a2000c7d651cd62040013ed03b828488002bd205624c54000666318e4a1aa000ade83d49600c4018faea318c2900035ddd631580310072ebaaa730e6000ecf74d8f62440011fb01bb287288031fd97744c1100063eb2ce7a002000cbd659d032c4001cbaa6a92c0188065fa1773884100063eb2ee0a1020008fd8715063440019db0b3b642900031f19671909100047fc3aca2162000cad7458832040091fd0db9aa1880038f595644c8100066e31ae121aa000f8f43d0832940014fb0bbb264880573b1c9624c2101deba210e2a92a202c7c75d944244001c7acab206408003731cf6250b1000737282a530e4000f5b855c0310c0019eeca38a65080533b0c8715804200767b1e87b1220009f4815c843040015d904a1cc3980039da1461cc5200071fba886b008200cbc865d032944018facbba442080031fa147654b100056f426a73182000bdb8350a10040019bcec3188488002bbe0943980100066f3a4c73102000ecf8418c62440019bc603b284188023f618744c810006f4a12e010820009dc8758d4204001cd8ca3168488002af61b43d0a100047fc3a87b0aa000add83085600c401c7ca12a0c2a00031fd96718c9100065e3b486a1e20008fc87509610c001cdccb39cc4080031fdd96590810006e639e84a142000e5e651ca63040013e902b9e4008002b7a0b5498c100065fbb4c8a102000add83d49600c40157d08192c0188031fdd7624c3100de77430e4a1ca200e3d65dcd64040018fccb38c84080033754f76508310053ec2e40b008200b758590441c40018fae6b96ca880033720d7098632006f2a90e290620008fc815d842940018faed3ac62080031fdd672580430066fc3aa6b006200cbd64dc930040019beed31a640800337e0d7098432006cf400e6a108201c7c755953204001c7eca396c8880033b5947250c100c676312e110aa000cdd7398740cc0011fb0f31e80080e3e3108430ca500047fc3ac51882004b76850ca51c400197aecb24840800e5fa1671d0a100e69fa92e8194a000dce801cd42480018fecbba46288002bda0450582420057a40a8030aa400e3f6550940440011fd0fb2a6488052bbe1432185200063e43aca2102000db5641c543040018fceb31c63080036d205740ca100065f3b08621620008fd869c6439400187aca3a264080039718d43941500057b408a6b006200cf4815c0614c80157d08190c0a88029fa1764580310056e422e031a2000cbd8710c61500050f
  | 62 => 0x483b24309017c000000000900280ab002800e007c00f00180314a1c002000c00800b401e0718008000001e004c0c0002400300240000000037000800d000408900801d1010c00901940ae016400001640160000015000000e00540a200f060b001000a72e0000001c020000c002001c001008002200040fa0040006169c07d00155dc000000c002cb73007800b0034006000589f000806400e0053003800f007c00100b401101300180168006002003d13d4000000800000880020000028000c0000000041000402000000010028001003dfe1020800700080000000081001c0000000079024402200180000190000000401300ec00300ac006000805300a80100000001000000a0014000017838900a015e0000000001413b03d000b00082c500e00000bf81d90000030009006d002c74400080000098011070c00300d8032000c01a00c4005080800200442ac000193700c0006110c000121c02a0000021006c00000ac01800a000508f4010011c0000000017000c03f00b400e003c007002402d000403a011804a0008007002000000640000014000015400101d002b00481ad000800000001f700000000028013008001500900020004003014c00a126003300240000000019004c0050000001003007301cc13b004097a00018310004000004c15f0004014002c000018001743b800800d001442f0001001801f59000240238006009800000d40240058000000800100dc02200f411d003810e42b800002c00000304002000069100099eb0000006000001c000800500380000034024000c023000000b00080410004003000c002002400f005c004076800000800000014896039000b00094f2001c00300000130014000035800201a0054000800d006002c00000040000001001000005ac040002801f07f800100241ad00000020004005003410d014c1b300ec01200d40150004008000003b1478642003422c00ece8c00060ee001000200780090000024000c019006401d0014001005800200000880098004000408905540580008240001800101640da0054006005c0040010013006800e000000c0034009003003f00840a3611003600f0008001800f001000200b0001000c00b00b04b4000007500f400a00000050000000004400d00e800400080330000000000801103181b00000015000817300001e200a800800180f800200000024001003005f000000200b800d003c006000001200fc0070054132000c04d005807314a800b0000000000007a01040080000011000c0002b7006c01dc019001c023000000600700b100000020000001003800b0064005008c00700180010010003006c00100001270000002000c010000400b01c00000000002002409e03980021464000000800a007003f00b013d00000f2001800000180020000028
  | 63 => 0x14000800000940ea0030001000c024000004d000006c018c00300080050088000000002300d400202300050028010000196800840010000001000007800001317a5c000002004701d001400100000450075005c000000000000d0001000c000000000100dc0050000037000c0160078029010c0ca0004010005002b00040570058000000800000000310014000000c01c0004000024803200a40100140002000c00a008007602d8001008800001980010324089027800001681e900000020b48049009c00f001400001f4000000406b005400300ac031036c0040004004000800500c000100040080000000000000800f4000000003100100e200256f1039c01c000c02a26d0006012000b000810c00015d3051c002000000101ec0d2001c02e00680070000019013005600000270000005002801e00a8194000001805380a100940030028000405402a0005377009800600080020048000019c27d00100010010019006000100600000000017008000900000700040000017c07d0014032000c089001400600bc6aa00d000a0064089001401f03940000000002004802711c400000982711e601287a94094000012603d00080020037004400a03e802a006c02201b800502240010008000000000000300a000000002c4000c0008048015c00a02440010140012003c00d0024032007cc7400240000000018004c005003800000040000018038015000600a80300018039005800e0990009001404c00080d700e0083003c01c000009b0028000018d49c018006d003c001000c00003b403b0104001060002c008400f02b9583012c00700f80070000072013400e021401e000c0320164008000000011a8036003114d011c051000400720a00b900480000198001003400202200060218ebf0000076002cbdb078c00e000809a0018025119c0260060003000403276cc004000000700dc008000001a00e804f01f0027000c034000000d013000200ac0960000004002400801080030028026026c0000050000003800f0024006000417605cc04d0008007000000d00340000034099012c00e0058134006c000008c00300840000088001001800400016c6005800c010c000001401e00000050000009008801e01d800f006401b000000a0605a7200c800100e001500fc02300a801907c400000c8039005c4bc00081810000000001400312b8001000003e02b4001000802f0154137000c000003c024002c00b000000c00e45480000000033801d0138011001000403cc0090044000002c000000005f018403101300000088012006000b0000000000c09001d40c9005400100c800100400040114000005c0000050002024000000d000100d40010170012074007f001000e003c00d022c06200700eb0c88034000000d037c00b00000010098014043
  | 64 => 0xc046701440430014011000000e00042ef000c00100f8019026401a157801b004c01100000660060006006000000100000084001002418a00d000300640032d4800300080000040424006001100480c400d0000001c0900000042000000000240230b101c24e94002001404300ac00000606b50008004015400b186003f001000800a8019000c065005000b000405f015800000dc07e0080048012800400c80020018003001c06b00140010004063000005e009004300c4006007405100b001a00100010024004001000003dc009006000003b400901b000004cc00100e0000000000000ac000109c00102c8586001400301180db36a0009000800c00000360010006000822a002c2d200d80080018023006404c00140010004015002c05a00400092130001007005100d40cb001003707c8006148d60f004801d009c024001003805b40000044003001400200000a70008000001803b002800200880110000113005c03e000400700000970004003001402100240190064001008c01507d009d05ac06a001c03501bc00600000310050009059801100140050004c3003e0006000400c02dc0000000002018c00100f000007241630084000004000a0024000000c00000140630028001000801f0010041044000a001801a00dc00518ac05500f0017000400f000800200881dc001000100e8016000c08c006806500111c51f3801900480010340001003800200040b2001000400f800001780000140005035802e0014000003401c001000205e800800b002402e017b0034008011004e008c736000c01700f8016010007e00000010094000050400201b4018076800800340040000000000000007d0005000801500e8040004000701880000198000002c00024a001400100140148005009000b000001d00300080004b3d00a8027001001401fc0f5001018b0000006015c002000c00d000c088001003b00000270028200004c06b000001801a900904580090378005000012100240010000000001c00c02a800300201e7009801e000002f00000110048071001000a008c0000000003006004b0028019027000000ac47508d0001000c3c6000c01600a0003002c00401380521fc80010038001000401701640030020008000001c010805b172c00408bc0000070005005800300046e30110005006c03300040910078002008c00204d80080008009008471e000800a00080f4023800300a0025023c00800b800400b8004000000a00e004500080016a0801d045401b00200010034660001c0000054004000c018004c07f00d4004000000001dc00e003400e001cb7b0594028002015d234484000140090014001024400000180010004032003400d00e8002005c00c000c0000008002000000104c400602dc02f0008059000404f12a800300041ba000000
  | 65 => 0xa00049c6004800e0000014000c019000803102bc0150040007000c00100080060000001000c00529dc00c0070001004001800080080018024010da0300bc004000c000000c118008827002d800000ac0010094001000002e00740a3000000c01bcd2700040dc005c006000814701a4280000003a0084009050c03b00180060004003024008700b0e380000000002c02600c4005000004900cc01101bc0000011d6a007c0004dc411701d8008046800b0085bee0000002004007601a8013018c03c03980020704005000c10b095c00900b800e001000200200015e4c0010000027003000500385e3006c06a01b400200100040040004005801300141fc001805d011400a00040000310002085c019003409900000005d44002005c00000a099f00d41c0140400b000c0330014301020809f006c01d005001800e80013fe000c00bc0010161b8501f16d801a81850000001000402e00f400300f00000458005009400b00840c5000c21b004405500a40170034000001c01a00a0123000c0040000000015400401bc003000c10c0028326005808200ac0180014089013404000440200005764000400e004c58c03b40050014093002c05b0254006000403a00141f107d80680034000004c000001c0f5006400404940290004002002c004004c06901f000600e4004000403101345150050004007000d004c00e001c007008807b003c03e0000001002c003028400500c40610024000000000101b800100200000034006000001410d40bc13dc0040000087000000300a172100840050124002000c3ed0094001072002b00782b8002803f000002300089d10000003001833f0024000016c0130004003000000200044c4000000e003c00c001402b000400d00680060884000000c0b5002000b00100000020025009c0cf000c073000400600001130000001001805c001003d000809e001400a014400b0000007000c58800a005a000001c0d0805601d408500b40270018068000003c002003b01d40f5004801001a8002000c000000800100040090cf800a00740c0000003300740140094002001c02600280fd0008026003c004000c00a004c0050000009009000000400000000000006400c000000100d003b0024b17004001100c001a007c0000038021005c002000018900000000004000000823f009cff1002003a002402703c0f61000000f002401a0000c88007800200340000054007636841b01cc057001001701f00000014000000004f00080130000d2e000000000000180b74000004444b002007b0004040031963f013003c0010000007482a031c013020800b002c00a0068023009402c0000220006400e17fc010003425900e401c002000100040150100009004000602140a303d400504b001500000461c60000002803300a0014032c00503
  | 66 => 0x3001800e5cc409a00440310004005000c003000000200000310050019000c0bb005404002b400b005000100d4000003000002b40081f0c001000001f0444015004c01f00b4036024003f005800b0128006001409400240080040094002800000e40090020000001c190001808f005807a00240410050004000009a02f000503880050000043000493a0030001039000000011430000001004800400b40cd00f0000019c00002040000020070003400000080660000018004c09200040000000002000000d004c000074800f008c030012000500b00030040037031c0ac0004000002800e0004043003016e01c40bf000000800283dd009ccb70090063033800501040000008004009801401640000058000084800700000130008032000c009000000300500040008017000802e01ece76013800000080010000003008400000680170084002389c0ab05800130044015001802d01c0005000801300080040024021005801b0000019000800000cc03a46b000200681b40018000003c0070000000003c009001402c00001dd0454ad5011c04a001400a00000000c1c00000e0907010000400080001848066001001501b40fe00200b20004014011c00000340000048000000001c00080000004010013c00500200090008005000402d06ec0190060159001400f00000220008001006801d00d400400080010068000006c004005400515a405101dc000004827c00400090000025000002f00840290038011002804a0008000006800700b400400100000060004016001a0020002000002d1ce804600080000000187000000001e44cf001400001110ee0150017000802307c00080000018000006c0038055000000a01c00970020002000c05201b00140004001001402c0038000470c01100000810000025002132c0034019005dd4d004c040016c00002c400000100ea0098088001001500fc00a006c03d004c005000404a00d0000005c0060134000032c039000400200040b300c80060044003000000300ac0060000000000403e16f947e00441fe0090011000c011003c02908480be00c4078011401c007800000100250168038016800001e0001001c0080000004004c00e46d001a0708001045c018002c01d0004001004802c0060ac500b029e0004000001400000000100170043004406c001000e002c00004e80110000000027004b005853000580910004050003800d0008001520c0030040005007800400041010364003000400000000030004000000c01900300
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x10be9810b76508100041fa63755cd60884018cd8698f7250c100043726130dd942cc4010dd988c076548310061b2097550c614800507d98dd67158041005a6e41435c0635080145e9315376547300041f6607598540cc00166591141529872000617a1a730ca5154401875652057210c100051be5d215d46148001a1d656107298c100041f25d85c81600c4010de980cb764c81000627dd984d9531cc0015c4935087148310007235d26298c320400185d65a0f7290631004ab259840c92044001a546320543545500052b658505d0328840107d989d472987300049de61650c91004001c1d655cc43104100050f65f5195061500014d5961cc7150810006935948350b2004001c3565205740c8100052724d74992620400164e9521d63588100061e601751cc6148001e0f65d0f420c9100071319463dc943440018ad869937250c100060f61d7590e61d00010ec989d9320c9100078a48375509601040162d940cb65c8110005962416594d600c40151d9520073508410058b652825d4614800186c87dd552582210061b21f6550f624400166591141525802100633618321cd50c800146f9261f6550d10006339d88350842440010ef985d3624c11000665604811cd421040183d65e1173084100051b654731c56210001c2d651d1624c8100069560d859c463c400168d9421f63d891000693d97825d06344001c8e74188630c9100051b648535d821940014b49150d7610e5116663208835d032440016a49161d64588100068b5d5840c8614800145f935cb75580410062b593825cf4004001cc5831cc61485200050fa50735972004089d0e541087350a500052b650731c56210001c6862d95700c9100062761b801cd42d000107f9761432987400054de45425d661d0001c4f65d8f7250d1000627619801cd42d000149c965d0630c9100051b65e205d461480010bc985917298c100041fa6374594320400143f97595640c810004a76588350a4104001a356520572990100051be497659543040012cd9810a7018d42007139d55298c210400507d98dd36508510006a310a8610c3254001c8e641ce6250a50005a3249845c063508014e89650970109100052b251721c9600c40168c93608641891000533a5d63589420400164e951cd6358810004b3a63205c4635080162d9408275185200061d594815d03204001c1c655d0630c9100046ba60505d0324800143d96994744c8100058724d42d94424400185c8799563508100072359373589420400146f9258d75987400052765c6418c3244001a692061432580410052be5173d8b204400143e94d4876545400141f663659c44344001367985446254b1000617196831c5504c001a1e32e15701913200715594731c5420400162d94083755822100517a568798f20040010be981087650910
  | 1 => 0x6275d88350831d0001c8c74d8f624c9100070b9927558832040014ae9720d6250040005272518718f204400143f944c97598740007079d764d8c324400185f76a147258c1000437e627610c3244001c8d6458f7250c100051764f725d661d000186d869947250c100061d59681dd33204001c1e651d2634c81000687196849cb634400189c87d9363509100060fa13759cd608846b98c8220d740c950004a7a60425c463508012af9461f32185200050f657865d03244001a4f6520d42885100050fe59435d66110c01a1d6520d42906310061ee1c85580600c4014e697e0c6148520006b1a04211c063508014ce9610c7250d500052d259429c7404400186f76a1473588100061b214825c0615080107f97618439465000627218835d032440014d4935c47158042006a3c8283d45640c8012cd9620d42c8010005a324983992630400168d9420863c811000617a1b651cd424400151f9560073508410051ba4a76d95434400145c9754d52580310041fe61751d661cc00165a90d4653580310052ee59425c0410400127596205329465000556643851cd429400146e9210d75185200052b25974d883244001c2c655d3620c91000713a4a7598c2104001a67815d54218520006871948350b404400149f965cc431041000527658801cd4210401a2e6520973990100061b61a65dc94304001c2e62995740c8100052b65073dc162d0401c9463d0871501100051da47725d66110c01a8c21a0c50590320a43b26174589300400149d9718c43d0110006960c1858c5600c4014ad969d1620c8100061b209655ce6404001c4f75dcc325822100467663511cd421040186d752094398730006b1a07201c0635080169b905d27018d4200768508415c021040018af9761032185200068d594844cb100400162e941cd65988100061b615829c76050c0185d65e0d74988100061ba16629c4430400189d7620d42104300051765f51d4a6304001c2d655907250c100043ee61701c0615080162d94c8775582210055c654815c032440018cd8698c7250c10006335d883508219400189c8759163508100068b195840c9204400145d9798d758c71000687d97835c8644400187765205744c11000617a14639c4434400145d969d5630c81000517a4c7459720040013379854764953100055a654325c2210400149e93d91731051000687615409c4635080507d981db650c9100061b59582dd231040014ae961d3324c910006179d683186315000149e949c8638c51000547a56811cd4210401c34415d574185200041fa63755c9600c40162d92d0775580410e51ba5c505496008401571959c57018f10006a9c8181141640c801c1e7595263104100070b1947418932440018748759532c401000437a58835d1204400143d9799175907100062b61a641c94304
  | 2 => 0xc0010bd981ce64084100062721e6498d420400143d96996740c810005272517398c2104001a2f65211320c9100070d596431c543040014d890618735095100527a5e6498d320400185e8518e71cc91000713d9473189424400186c82dd543582210071399773989420400107d981d46258031006a9d45840c8614800146d9214f76547200051ba4843dd5608840143d97902759874000617214835c261d0c0185d6520d72990100068b995840c92004001cc563588715081000716194635c0324400168c925d27118d420056624d425c2410400143e97993755031000723993739894204001a4f6520d42085100041f663659d13044001c8d74188630c910005a3a5273d8f62440010bf9859373884100052e640739902104001a1d8550e7118d4200536241315c0635080129c9858d429041000617994835c2418c40145d9798e758c71000715614639c730440010de98dc57018d420060fe19655d032040014b99610d70904100051764c745d4614800107d9815376547300051be4943dd56010c010bc9859173480100068b594845ce62040014ac925d26498c10004a7a63635094044001a8c42618430c8100041fe5d850ca61cc00107e96a1c43545500060fa1c65d91324400149e9620d740c910006339d88350a21440018e4622057010d100058b65432193204400145e931d1650841000517a5c30dd5600c401a1e656107258c1000687614849c463508014cf9761063d89100050f65c509506150001c1d651d1634c8100059a24151549608840189e8719063509100042f25d840c9610c001a674161432185200a61ba0575d8832c40010be98d95740c81000693597825d16304001c1e7595063d01100062b5d3825cc615007598c8220d740c95100539245745893004001cc563588714c81000635d8c815d120440014ad940c8715883000497a5681dca63040018cc8798d43588100060fa1865dd13244001694916096458c100068d591859c464c400191f85a147350841004a726063508414400186f8798a650c81000539249711c56010c89d0c420cb75580430070759574d0c320400183f756103258043005332498718f404400145d939d375582210042fa5c844c9610c00153591141740c95000527653859db314c00162d941cc65189100052725f64d8d32440018ac97610325822100565a44501cd421040189c87190635091000633a1863dc9434400145d97d94630c910005332497318f404400307f98596744c01000754546535c031c400146d92e1d6550c1000627a5c8350a61d0001a1f6560f72d91100061b20b655cc414400168c925d06418d100061bd97825cc4144001a656520943440100060fe1d6550c430400185c8518d70d091000553656811cd4248001c956458c7150c100071ae15625c0310400195883215700c41
  | 3 => 0x10006b1204215c063508010bf976103298331004a7e4d82dd964040014e49650a71c81100052765f64d8c3244001658904c47558031005956465094c614c00143d94a1f650c91000633dd88350951c800107e97a14325803100715d94639c4434400168e9420963588100042f658845cf2004001479969d5708c41000633e1c6350c624400183d7561272987300060fe1f65d90324400185c879966350810007239d363d883244001c3565990714c810006335d88250c430400183e87996644c8100054d644505d0329440187886e15700c52000687a14849c463508010bc989d94310d1000762c82801cd42d00054749161f654c910005a324d4250061480016359194254987400051b65f65d88324400107d98dd365c81100061d596819d13204001565950c8714831000617616831c560108018756520573108100052765a801cd42104014d9901d2630841000627e187350d420400126d985d432185200052b65e5358a411000145f9350b75580430061761965dcd420400186c82d957418d100052765b851cd421040162d9299275d93100068bd94845cc624400185e8759663508100052b25e64989320400186f8719543d89100052b658835cb41904014ac965d3420c9100042fa58845cc21440010df985c07018d4200693617209c4635080189f93219740c9100050fa58505d032540010be98d917218d100060fe1e65590320400149d971097118d421e663208835d03294401a1f856117018d420068d5948150f420405f58c925cc43d0310004b3660211c0635080145e93d4b76547300052765873d0d4204001c2d659d1620c81000566a40811cd42d000189e9720d42580410068bd9582dcf644400186e82597748c4100062b2087650d425400145d95a1873508100068b5948250c430400168d940c863085100068b597845ce620400185f65a0f74885100050f65c405d661d0001d315195170107100060f61e7519032440018cd860ca73944210070bd9774189324400107d98141760ca510052765a7458c320400143d941cf65085100043de59801c53204001a1e6520d42d00100060fe15745c0635080189d9720d4298740175632497310f408400183d756106298730006279d883508414400126e981cd659881000687a16641ca6304001c4e7554863c811000687994835ca640400146d950cb7058b310050f65087594320400189c7620d425454000627618811cd42104012ae962094310d100052b25d83591620400147691d49760c6500062b9db825cc644400129e9620d42d011000687d94845c86344001ca462192710c9100070759473d0d420400189d7620d42d00300062edd8844c9100400186f7520943580310050fa5076d943244001c35651d3714c8100061b21e6550d620400143e949cb65d8d1000617196831c5404
  | 4 => 0x400119e981407350b400060fd97845cc2144001c568518e71cc11000687e16425c063508018af879914398810006279db835c8644400107d98d457694720007071417418c3254001a4f851097018d420050f656861d132c40018ad74205620ca500049d656811cc6150801c8f64d8c7250d100070b9d5645883204001367985476254b100061d594815cd200400107d98dd661580430064bdd5840c960884018af875914358810007071977418d32440014ad97591620c81000c1f261655c3420400191d849cc329465000723dd263989320400168c935d06418910006276187394d421040143f9461f654c91000687d9684dcb63440018cf8798d4398810004a765883508410400126c9761432582210060fdd7845c9600c401a2d65610735881000565a44801cd4210401669901d36518910004ab24582141640c80168f9260c6418d1000617a16639c7420400189d7620d4290630004b5644805d46350801c1e659d2630c8100050fa58651d13244001a1e64a147258c10005b12458458d6204001c356599071508100051b65473dc162d040185f76617644c730006278c9861d1320400187b87e15601803100687e16745c0635080185c87d976350910005a324d42905608840145e951d0638c510006875948350841040010de988c37650b300070b5947498932040018ad8798a640c810007156467518f20440012ad962094310c1000527a5a74d8c324400183d87194640c9100058b650201d56088401a5681d447598c100060fe14845c2610c8010f7985c471580320041fa60509d8325400168f9461c631891000723d8b641cd4254401c1f65dd3634c910005396607318521480012759620542946500060f615845d832040014eb96549700841000693197835d0624400168c9261c6418d100073118e521c52044001999802007350b400061d21d6550b100400107d989d472984430043b261425c2611080107c9761432580430050f65276d95324400185f8520d70984420050f65e5095261d0001534915d2540c951005a3249745c0635080185c8520d70986320060f61d751903244001a3565a1032c401000517a4c745d461480014cd97e1363d89100060f595841cd6204001c556598c715081000527e5974d0c3204001c8e641ce6250a100062b208865d0324400152d9214d740c9510062b21d6450d620400183c86195740c910007235907358942040012cf985d263988100060f5d6849ca61cc0018776520572501300041f662751c26110c0149c9461e63084100070b188659d03244001c2f651937250d100060fe1d659903204001c556598c714c81000437660309c46354801a1f6520d42905100054724d425d661d000143e941cb654c11000437e59801cd420c00145c935097598740007079927558c3204001669901cf65189
  | 5 => 0x4430051764e76d954244001a4d7520d421852000693994835d26204001c8c6418c7250d5000527a527298e310400125d95a077018d420062dd90815cd204400162d94c847558221006870cb855c0644c80183d879d6640c8100050fa5073d97204400107e97a1421580310072a188645c04244001c2e7598a640c8100061d5d4814ca61cc001c8e76d0f420c9100050f65a655d0320400143d951db744c8100041fe5d8508661cc001ac5810847018d420050f65076d9432440018bb76a1032440100070d595641c53204001e0c42594430c8100041f663750c96010401c1d659d1630c81000693597835d2620400107d981d3650c91000517a4c74d9720440010bd98d94744c81000687614429c4635080168d940c863c81100051d245625d6414c00186f6560b748c5100060f61a651d13204001879869c2758c41000517a5a7518c3244001c8e641ce6250810004ab663649cf624400186c87d9543189100052be5187d8a3144001aa79161032185200068d594815ce640408bd0c420c97598443004a7261405c4635080168c935d264988100051b24963dd5601040146d970817518520005a324987992630400168c9461d635881000617214835c06150c014cc925cc63105100062ba51861c9430400183f65e117218d1000617a16831c5601080162d92993755031000732188635c0324400127595a0770185420061b21d6550e6204001a8c8350d421852000599e595118952c400187980a147158032006391ca811d560084011ae98141740ca210051b654761c9430400149d949cf63d89100070b99774989320400186f8799543988100045d261431c5525440159493508715011000627651861cd420400187487595424401000687a14641c8634400147795618714ca100061b597825d2630400152d94c85751852000693d948350b20440014ce97d8f625091000715614631c5204400164e95a0b63d8910006171ce859c5600c40168c9250c43983310063320c825c06150c016a49150d421852000517a547598c21040016949150d7118d420060fa1f6519132440015c89350970087100061d594815d3300400185d8718c32941500061d594815cb300400185e83a15768c410006a91928110c6244001a656520573588100060fe17845c2610c80187886195700c91000467660501cd42d005dd883210d7010a10004b3262635082104001c1f655cc43105100042f261655d0324400185f85e0d70185420068b20b6550d42440018b78420570185320052ba53729ca61cc001a4d85d0a7118d4200539259521c5204400143e96d41740c95100707d9464dcd42440014ae96dd0624c910005276587498d320400152c9250d75984430058b653219d4614800185c6520d70905300068de067550a61d000145e969d67390530004abe5183dd962
  | 6 => 0x1c800186e861977250d100051d245435d66110c010dd9720d42181510060f211755cc614800149c9461e63c80100060f59584dce2104001c2f65d937250d100051b654731c562040016389054654582410041f66373d9720440011b49761032440100057224d425c04284001a6551608515802100617a1c65d8d424400185e8619773509100051e65a755c24104001c1e655d2630c810005956475394e61cc001c1f655d3430c91000696195801c863440010de988c776508300048f259859c4435000145f974c9650c8100061be17825c06150c01474915cf75580410062b188865d0324400185c8598d70d08100062b61c6219032440010de988c77650b3100695a075114e63040015a5940c8714811000687596841ca630400507d98dcf650851000723dd063189324400183e871d6435804100617e1d6550c4304001971856007148310005b2640219c06350801c8d74d8f620c910004a7a63645c8634400149d97591630c81017d632497310c41c4001a568360475580310060fe1f6550c434400145e93a1f65109100041f662751cc6148001c356559071508100051be4973dd56010401a2c6561273d89100060f596841cd62040010bd9810e71d8143175632497310c41840010f7985c471d81430068b0c9859c4644c801aa9426002158041006a924a81141640c8018ac21a1c5059032004a7a5883509404400186e7221570987200070b5957458832040012ae9899173988100061b214825c0614c801c1c659d3630c91000497e55819c0635080125f956007118d420071399473989420400129f9460b7658c100072399263dc94304001a2c6561032885100061b597825d1320400185e831d672580310062b9db845cc624400185d8659473508100061721f8554d600c40125f985947258c100060fd96849cf62440010ed972094318151005a6642415c063508014b4945c471580320060f594845cd200400185e8598e7110c100052be5d8399262040018ac821d943509100041f660501d83154001c2f751c942580410061bdd7825d1600c401a1f7520d42580410061bd97825cc644400145d95dc67118d420ae2bdd9840c9200400168f9360a64988100051da4774596320400168f925d26498c100052be5173588210400143f944cb755804300627252861cd424400143d95219740c810006651cc8150d428400146c9250d75987400041fa60755c56010c012ac9661032885100051ba48739d661cc001c4e7598a630c8100049be61651cd620400189e865cc43d0110004976605018e53c4001c6462d96710c9100052765c6310c4144001a1e855907258c100060f21c75509601040146f9250d7598443007079d56458c32040010be9721132586500052765e6310c410400183e87dd654580410061d5d48150a61cc00183d756103298
  | 7 => 0xc950005e124d42104210400185c87d94635091000687653855c0635080185d65e0d744c8100051ba5a75d88324400107f9761720987300069318c8250d515400183d85a10715803200617a16639c7320404146e9794152580210060f21e6559132040010dd981d063c8110004a7a52829c6630400146c925cd72d9510005996578318521480012ad980c86408510004b3a5883509204400145f9754d52987300051b654321c56210001a1f65a0f72d91100068b995840ca21040010bf9661d640c8100062ba18641c9434400185c8754d525803100695594815c96304001c2d759c942987400068b596841cd6204001a6521617741852000713597735894204001a8d7420d425822100437e61731cc61500012cc9898d42c801000699606759086148001c1f651cf43509100051765e305d661cc00164e92d475298c100042f66073190214400185c864c575905300069359483508420400168d9421d6358810006995978250f10040012ce962094310d1000517e5e6598c32040010f7985c471d81320070b989659d0320400145e93e16760c9510061d594815d1200400189d862147350b40006a5252811c0635080145e96cc575905300050f65e645d764c400107d989d473987400052765e419c46350801a2d65209735901000533a58421cd425440149e97d93634c9100058b653215d4614800168c9461f63d89100043ee61701c2610c8012cc936086418910006a320e7250a61d000307e98dd165c80100049d6588150e5194001a2f32e157019132005332497398f400400183d6521173c801000497e615118e53c400168c9361e64988100061b61d75908614800126d989d4321852000595e456594e61cc001a4d652094310c100049d245821d1650400146f9258f755804100553656811cd428840183d86597744c81000527e51855da310c00183f85e1170185320041fa63745942104001c2c62195740c9100051724d751d56090401a4e65e097498c100061e595801d03104001a2f652094310d100070b084655d0324400168f9260e6498c100061d61d65104310400149c97592634c810006a320c7250960104010dd981d663108100071399663dc9430400143d95a18744c8100051da47725d661d00010dd98d9473508100060f21f651913244001a5a50a0f50580310051724d42dd56010c01c2e659937250c100068d595840cb100400145f93509759844300633e0f825c261108014ac9250d7610e510056a650325c221c400186d65e09739901000517a4c74d9421440010ef9850871580420058b650205d46148001c56919d463c81100051724d87d95424400146e92dcf72594100060fdd4845c9600c40151d95e047350b400051da478759543040012cf9361376588100068b997825ce64040018e576205320c810005996465054a6
  | 8 => 0x424400149d962147350b400052725e6498d32040014eb9650970084100050f65072595630400185d85a0e7118d420062edd9840c9100400165591142539873000723591631c9430400162d9210375580410050fa5c50951609040149c935087158343006b1e04215c0635080183d875d6640c8100058b6548358a411000185c875956350810004b3660219c06350801a1c859d17018d4200555656811cd4244001c546518e710c91000517e55861cd425400168c945cc63189100068b197825cc6444001c2c21995740c81000617a1f6518d4244001a1f6520d42105100041fe6165dd22104001a1f855d17018d4200699594815d1620400145e95a1c63d0110004abe51831c5620400151d952007350b40004d5e615118e53c400107c9761421580310051b64a645d462c40010be9621c644c910007139d46218c324400143e9710375580410078a480755096010401e2565508410841000695e178154e61cc001a6565205435881000707d94641cd424400145f97194630c91000437e61711c4635080129e9810a7118d4200699105850c86148001c4d6558f7250c100051764c745972004001a5565e0d42c40100052765e415c0635080507d98d97740c5100141f66271dd5608840146d9714152987200051765a7598c320400189d7620d42107300041fe61751d5600c40189e42618735081000617616711c0635080146d9221d6510c1000517a4f875954204001c1d655d1630c81000593a5673d8f624400168d940ca630841000517a547518f20440010dc989d94310d100062b24b865d032040014749158b7550130006b1607201c063508012cf985d0631891000635e1d5358461cc00143f9750965108100043ba61764c8320400107c9761421580410059624131dd5600c401c95635907150e51004a7a52829d863440014af965d1620c8100049be63750c96088401a1f65a107218d1000633e1f6350f6244001c4c65dcc62509100060f61e74594320400107e98d457098e510060fa1b651d1324400168c9460a6398810004b36588350842040012ae96211320c91000617d97835d06244001c588598d700c4100056524d429c740c4001c65851cc61485200061be1c6550c6244001c1e4259473508100042fe61651d1324400189d76613750c63000719597721c54304001c4f65d8c7250d1000627611831c560108014e4915d3624c11000535a467518c424400185d6560f748841000617d97835c86444001cc4639087148110007231907318942544015989350970104100062761c8498c41040018af94a187250d100062b9d8844c832440014ce961cf6250910007231d1635893204001a1d65e0d72590100062ddd8844c91004001c1e65993735081000517657715c0635080186d65e0973d00100068d54981141640c80149e9620d740
  | 9 => 0x50d1000437e59801cd42cc4012cd962094310c100061ddd4815d1600c40185f6520d72501300062be48865d0324400145e9798f754c3100061b61c62d94324400185d875d653987300052765e6498c320400107f97617209874000565644501cd421040123d96e157010e410043726130dd9420c0018e9825c0701854300707d457498c329440183e87594744c8100050fa5073594210400146f9258d75d9310007075947498d320400129c9818d42d0110005a3e4d87190624400163591902759874000617e14835c063508012ad980c864c811000693197825d06344001c2d6590c7250c1000437a63635d1204400185e8718c32545500070bc80655d032440015949160073508410061ea0075189600c401a2f6520973191100062b651861c94304001a1d6520d72590100062bc80865d0324400146d950cb7058b4100687616419c46350801e25421067518520004376607518c42440018ac21219740c9100043b663651c94304001c1f73dd643580410071559773dc54204001a1d65e117298c100050fa58659d03244001c4e7594a6308410167230c8435c2611080145e951d2638c4100041fe6165dce2104001c556558c7150c100060fe1e7550a61d00012b496610325451000569a44505d0324800149f9760a6498c10006a9e4a81141640c80178893509404811000c1fe6165dd33004001c8f63d907250d500a62bdd9840c920840014ce96dcc625091000617615701c0635080186d879d642185200061765c855c063440018af92e19740c810004ab65287cc9608840192c7561032582210061720d735cb6544001c668761461485200043ee61701c06150c0126d989946254b100070719574d8c3244001c8c6418f7250d100051b64b735d661d00014b5961d0714c81000527a507218d304400151f956007350b4000707d947418d3244001cc9535c960180310041fa63519d832540018af64e0973d01100068ba15641cd62040018776520573481100059aa4321dd560884016c99021c63189100068b992851cd620400199483205740c8100061d594815d320040010df985cc735824100547a56811cd42d000186e85a0a71d81420052725974d8c32440010f7985c471d8142007078c9651d1320400107d989d462987300051724d72dd56010c0146c9258d75987400071a58b855c0410400149c9359173d00100060f616845d8320400127595a0770185320050f65a75990320400149d9614c735084100c1f261655c3320400186e8518a7110d1000617a1b851cd42544018eb76e09434401000497654805c4635080107d97a172098730005a364c87d9362440018af20a1c50590320061e25787580600c4014cc9261e63104100068d594815cd640400186e82d97748c5100041fe61751d6610c801a4d850867118d420055c654815c0
  | 10 => 0xd600c40189d86a14735084100467a63511cd42104018b776a10324401000c1fe6175dc261cc001a3b6560072191100051ba5f21dd560884010ec976126358810007079977498d320400107d989d6619073000713597431c9430400183f6521173481100060f61d74594320400162d941ce659881000633a1b431c9434400307e981cd65c801022f43950421cd425440185d878c3658c5400061761d6510c3204001c2c65dd0624c9100061bd97825d1324400186c82595744c010006270c9861d13204001474914c97598740004376607418c2144001a2f65e1173189100070bd9474d8932440015c49350a71c8310005a36503298f2004001c56919d463085100078310b6510c324400185e86194735091000617e1a305d6418c401939809d2530ca500058d64450950615000186d865947250c100054b65020dd560884010df985cc73d814200547255801cd42104014cc9350970984420041fa60545d83194001c8f74d8f624c9100061d5d48158a31500014cc925ce63104100060fe1e74594320400146c925cf7558041007235db43d08320400145d97142539873000527a5c6418d32440019718560271d0310005e124d42105510840145c9350975984430042f66073193204400107d981d673580410051b24943dd56010c01a1f656107218d100050fe5176595320408bd0e5410c7250d510051765e309d661cc00143e96195740c9100060f61e659903204001a4f6520d74189100062b1d9840c9514800146d950c871588300070b1d175508614800149e961cd435091000536e59535c03104001c2e62595740c8100050fe51325d66110c012ac9460863189100050f2597550a31500018d46320570109100062ba12829c7604c80151e95e04735084100617594835d26204001a1f6561272d8d1000617a0e751ca61cc0018ce76e097418d1000687d97845c86344001c2c74dd642582210151d24587d95424400163a90d07755804100517a5b31dd5404c001c2d65dd1624c81000517e59315d641cc00186d865977250c100068b594825ce640400143d969d5640c81000693d94825d0634400168d9421e639881000617214635c0434400107c97614215804300527e597458c3204001596911407350b400062ba1a431c943440018db76e0d42440100053324d421c560108016c9901d063189100059aa435154960084014af97d93620c9100052765c429c06350801c1d735d64398740004a7261409c4635080107e98d49760c65000533a5873d09424400143e9414c76545400050fa5287d94324405f38c9260c6410f101ff8319743d0832440016a5940c8610855000595644305d661cc00143e97d077558041004a7261645ca630400129d98d9272d8d100061b216625c043040018cd860ca73947200051b64a76d954344001c4c6518c72
  | 11 => 0x58c5400043b26276508424400149d96e047350b40004b324d82992620400158d940ca7394421006875948350b4004001c2f651907250d1000687e16845c0635087fe0e65d0f420c81000497a56811d2630400186c8759543588100061b209655d2630400183d7561372987300041f66074d972044001a5681d445498c1013d1e25d65cc1300400507d981cf65085100072a509205c06150c0143d97901759874000693d948250c434400192e74209439465000619a1d85185214800107f985d47558241005276507358d62040012ad980ca640841000687d9483509404c001c4c651cc6250910005956445018e53c4001595912007350841005a3a5087d8f624400163890507755804100517a4e76d9542440010ef985947250d100050f656839db41500014cf97610631891000707996641cd4204001a1c65e0d72191100052be5173d8821440318ad76610328861000617597835ca6404001ca564588715081000761086811cd421040183d75211329873000687e51859c463508014cd9610c7250e51006179ce85dc261cc0014cc97d8f6250910006995948150e620400189f76a107258c100070b9d175908614800189d8798e53106400068b597825cd640400168d949cf63d891000437e61731cc615080145d97d97630c9100062b61a431c9430400183f87d94640c91000707d97641cd424400145e959d0634c1100070bc82655d032040010dc984c7765083100566640811cd42d000145f974cb650c910147230c8431c560108018af84e097098432005962415194d600c401c1d6520d740c81000c1f261655d12004001c8d625907350a5000527658851cd421040185f8520d70185420058d6445095160904012b49661032945100041f66352dd951cc001cc46218e710c9100063321c6350c6244001a658061461485200061da1b711d5404400193785205740c95100716e16635c0310400143d95dd8744c91000699595820c4210400147491509759874000437e61731cc6148001c4d651cd6250810004a7262635084104001a1d656107258c100ed2b65b515d0328840183d86996740c8100041fe61651d23104001a2d656103248010007079d66498c3204001a3565e1132c40100051765e639d763c400189e8759163508100052e6407319021440010bd96211730841000707d9764dcd424400191e841ce5350a500041fe61751d5600c80169b9050e7018d4200719597321c5320400126d98d9673d89100051765f315d661cc0318ad805d3620c910004a7a636350a414400189c42a187350910006cad41840ca5048001a2c8259543d081000633dd883509200400183f75612735822100535a467518f4044001d615154970087100c43b66374d8a3144001a2d65e1173588100069558d859c463c4001c8e7458d620c81000696e148054
  | 12 => 0x943204001a1e7520d42987400068d94d81141640c801c4d755cc321852000547a54801cd421040146e9221d6510c100061ba1f750c9608840189f8620d740ca5000687194845c8634400129d9620d42d00100068b194845cc62440012cf926137658c10005a5245749c46350801a1d65e117258c10005332498718c414400166591082751852000693994825d2630400149c965cc43d011000517e5931dd540cc001c1d659d2630c8100065c615809c730c4001c4e7594863c81100068bd9584dcf62440016c49161d635881000725950631c54044001476961d4714c110005a3e498799263040018ad76211320c81000617d9583dd2214400185e85a0c7158232005a3e518798e6204001c8f641cf6250b100071559473dc5420400168d941cd63588100062eddb844c9100400507d98d97748c5100052b65f83d936244001a1f855017018d420061721f7554d600c40199483205740c95100754546535c231c400129d9810a7018d4200695a04501d46344001a8f7420d4218520004a7a62645ca630400186e85a0a71d8132005e124d421065108401a1f6520d72191100060fa1d659913204001596912007350b400068bd96849cf624400149c97190634c9100071359773989420400186f87595435881000533658735894204001a1d6520d7299010004ba6588250e100400168e9421d63588100058e24151951601040183d65211730841000517e4d87d95424400145c935d475580210041fa607459432040018748759532440100061dd94815d1204400189e865cc43105100068b1908250e5054001c3565dd3714c81000617594835d12004001c986418d700c9100041fe61751d661c800183d75a1062987300051e64073594210400107e9620d72951510060fd94845cf2044001a556520d42c4010007139d763d88324400143f9750b65109100052b65874cc9320400143d949c9658c4100068d594844c9100400126d981cf65189100052765b851cd42d00018ae62e19740c810005a3249745c46350801a1e65e0d72990100051ba4a731d5600c40168c925d26498c100052724d429c76050c01c1f659d0630c9100042f65a84dce2104001c3464a1471481100068b192859cf624400183d65e1173c801000693d9583dd36244001c1e42d9473509100058b64a645d641c400146d95ddb7250d10007075977458d320400149d9620d740ca51005a6e41745c063508015c89350970887100041f66073d97204400143e96145740c9510042f66073993200400183f65613738851000627611731cc614800168c925d17518d420058ba5473190624400183f87595640c8100060f21f65d91324400107d9620d729525000595644309d661cc00185f65e0d744c9100052d259421c5404400107d98d9774cc1100071a18b655c0424400183c865057
  | 13 => 0x610855000687610630ca505400168f9361e649881000725591631c5320400507d98d94748c5100061d595801c54204001357985476394f100054724d42dd56010401c8d7458d620c8100060fa1b659d032440014db906187350951005956465094e61cc00166a90c84755822100617a1b31dd5404c001939805d2530ca500050fa5b515d0325400164d950c863c81100042fe61429c76050c0199483205740ca510061ba1f75909608840507d98d9671d09100060f61f65d903244001a1e65a107258c10005272518718c214400507d98d9671cc9100051724d855d832940010fb985c070185320053a658325c221040018798061471580420057124d421c520440018cd86d0c7250c1000636dd883509100405f98c8220d740cb100041fe61751d560084012ce9620d420851000699606750c8614800168c925d27018d42005a3e4d87591620400185d85a0e71d814200699594815d26204001c2f659d3620c9100061d61d75d8661cc00186d75a0b7498730006275d88350a419400189c861cd435095100627a12839c7604c8014d5961cf71508100060fe1d74594320400149d9620d740c810004abe4182d45640c80189f8620d740ca10145632497310f4004001c35651d0714c8100052765e6310f4004001c2c651937250d100055c656715c362c400146f9258d759071000725591631c5420400194e7320943946500068b0cb855c0644c8018ad64e097310410004ad245840c96110c0186f65e0973d01100060fdd4844c9600c4012ae98191731891000627613739cd608840125c956037218d100051be5d65588320400149e961d0634c910004a7e61641c9630400143d9614274d94310060f615841c5600c80168c9461e6398810006a9245840c8614800185c8518d70cc9100059a64073194624400125d98d9672d8d10004976626518e53c400189f8620d740c810006272187350d424400189f861cd4350a5000533a5873189424400183d652117298c1000527a587350d42540010dd985d8430c8100051764c74d97204400147691dcd759874000627218835d0325440143c9750775580410051764c7459421040014cd96dce6250810005a3e4d74190624400168c9260c6418d100051765f319d661cc00168f936086418910004abe59840c9200400165a90996535803100633a0e829c7605080168c9361c64189100071a21572580600c40149c945ce63988100058b64b415d661d00014b990108765091000617a16839c760508014ce9798e62508100050f65f6550a414c00145e95a1e63104100043ba617650842040012d59620d42c40100051724d751d5600c401479901d16508410005a324d42904614800166890487755822100687616749c4635080185c87596635081017663208835d0328400185f87d954310d100041fa60875
  | 14 => 0x50c624400189d865cc43d001000715a467518e3144001a55652057298c1000527a4f74dcd60904018ae762094310d100042f261425c06150c01a8d849cc321852011d1be5d5154a61c8001c568518e7110d10007078cb651d13244001669901d065189100050fa5276d95324400107e98195700c5400070b996641c943040014ae961d3624c9100c43b65e8650f624400189c861cd4350b100068b20b6550f42440016679154d52185200051b648539d8325440146e92dcd7598740006179d4835c26110c01c6565dcb7150c1000517a5a75d8c324400159791600735084100693594835d26204001c2c82595740c8100070bd97641c9434400185d7520d628c5400060fe14845c0614c8014db9754d601803100569a44505d032884012ce981097118d4200559654321c520440016359194254185400041f660509c46354801c586518d701091000723d9373d8942440010f79660071508100060fa1c6519132440018ac82219740c9500060f5d6840ca61cc00183d86594744c81000497a56829d86344001a1e652117298c100053325d63589420400185e6520d709463100627e187350d428400168e941cd63588100070bd96431c94344001c1c65193735091000617e17835c2611080145d97194638c540005a3a4c87d936244001a37815d542987400051b249435d66110c0183f85e12760c91000563650329ce51c80016a49160d645881000547656811cd42104018ad84608715803200617615839c760508018cd7620d42c8010004ab66032993200400107d98dd3650c9100063320c825c061508054749161f6550d10005a32518218c624400107e981cd65084100072358d641c9439440183e87d94744c9100043de59801c54304001a1f8550d7018d420053365a801cd428840127595a0770185430042f261425c261d0c0149e941ca634c0100070b59774989320400145e961d473501300061be1c62194324400149d962047350b400061be1d654c832040018b77661032440100049de61650cb10040010be9810d7018543006175d985dd0318c0018af87d9143d89100043b65c8250e60cc401c8e6498c7250c1000639ddb8250d10040018756520573c80100063321f6350f62440010dd988c076508310041fa6074594210400187a85dd83244010004b3a588350a214400129d989057018d42007079d46418c324400146d950c871588430060f616849c7604c85958c925cc43d01100061be1d6550e620400143e940c975185200060f5d684dca61cc0014d6919d463c81100051de55861c5438400186c82595740c8100062761a811cd421040107c97614325804100715194639c4434400107d97a1432987300070b59574d0832040018af8798a640c81000517255731cd609040107f98597740c4100061ba1b651c943440016a5940cb
  | 15 => 0x37250d100061b20b655cc64440012d6912017518d4200517a567518d304400189d862047350b4000533658739894204001a558560c610c52000497255801d063440018ce76e0d74189100056624d425c241c400168c9350b20580410052be5d83190624400146d9215176086500062b6508750d6204001a679161432185200069960575908614800183f756103258041006b118e8110c624400185d86e147350a500a43b25d8650d62040010f7985c47158042004a7a588350a41440016a89650940481100141f66365dce2144001c1f655d0630c9100051ba5f211d56088401a4d65e097498c100043726131dd942cc001a2d65e09739901000617597835d120040018ac92219740c910005a524587591630400149c9359173104100069948585904614800185d87d94430c9100051d656811d932c4001c4f6518f7250d10006871d483509601040143d96d4674d9730007075957498c32040012cc9260e6498c100050f25d411d560104016c4915d1635881020f2310a7610c324400159691a1473508410070b19275d883244001a98646007218d100062b252861c943440018748759543440100062761c8498f4004001a4f65a0b74d8d100051b64a645d764c40016c49350861085500064d9d08150e5154401c6462196710c9100061d21d6550f1004001e24415d5421852000699245850c861480014e49654a71c8110005a324d8759162040010be9621173481100050fa5032dd56088401476961d471501100060f61e7590e61d0001c8c641cc6250b100061b20b655d1304400116f976143218520004a7662419c0635080186d85a0a71d814300695594815d26304001a3565a1032440100050f251635d764c40015c8935097008410006875948350940040018b980a107158032006995948250f100400307e98dcd65c80100050fa5272596310400183f6561273d89100055a654325c221c4001ac563205435881000517e5d6558c32040014ac9750d42185200041fa60509d821540018d776e0d42440100045b25d850c9608840185c8598d7010c100050f65376594320407198c8220d740ca500071359473989420400191d849cc329455100565646851cd421040145e93dd67598720006276187394d41d000161c944c9650c8100062761b801cd42104018778520570185320051da58431c55254401a4f6520d42109100050f6507259530040018756520572d00100063558c815d1200400189c93e19740c81000713996631c9430400189d866007350841005a32498759163040010dd981d263c8010006878c9859c4644c80143e941cf65085100041f662751ca61d000185e83dcf72594100068ba17649cf624400146d950cb70588430060f5d7845cc614800143d97d94640c9100051da4787595320400143c9461f654c9100061b21c65
  | 16 => 0x41906244001a3741614219874000627210835c0614c80143d949cb658c5100051e64073d9421440018eb7620943440100062d5d88150c430400168d94209635881000617615831c56010801a6565205320c8100058ba507399662040012d79854f61987300068d5948150d420400149f976086418d10007075947350d4204001a6521e1530185200062b20b7650d420400187595e1d6118730006a3611730c86148001c2d651d3324c810145632497310c4104001c35659907150c100060fd97845cf2044001c1d659937350810005a365282d8f6244001a1c64a1672d8d100061d5d681dca61cc001c3565e05740c8100060f21d65591320400145e951d063085100052b65b74989320400183f75a103258031006275d88350841940019567320543945510051ba4a87d94434400189d9720d42580410051764c74d9421440018ac82e19740c810006339d883508214400186c75209715804300693e17425c06350801c1c651cf4350910004a7a50825c06344001c8d641cd6250a100061b209655cf4004001c4f65d0c7250d1000687d948350b404400154f95600735092000517a4f759d46150001c2f655d3620c9100068b595840ca210400149f97190630c9100062da18649c4324400146d97941521852000517a567498d30040018af8719143189100060fd94845cc624400107e97a1641580310051764f8759542040015a591141740c9200052765b801cd421040192e7561032185200051d656811d942c4001c4d6558c7250c100043ee61701c26110801699909067018d42005a3a4887d936344001c6b855c960180310055c656715c064c400107e98d957348110006651cc8150d4204001477956187150a1000687995841ca6304001a2c652097319110004abe61641cd620400107d981d67258043005936543298c210400189d8460c715803200c1f261655d130040014ad949cd70d8910005a3a4b849c463508016559114253580310070b59664dc94304001a2f6561032481100041fe6165dd2310400146f9250f7558041005a3a508798e620400183e87595644c81000687a53855c063508012ce9620d42c811000696c40855c0634400146f9258f75503100049be5d850c8614800183d8561271d81320058b6543299021040018af76a1073588100068d1908150d5154001a4d6520d42480100058ba5073d9462440010be985d94310c1000707d94835d03244059d883210d70109100042fe61741d261cc00186c852097018543005a664082190634400149c965d3430c9100052be5974d083204001c65651c87150c10004a765883509400400187695e1d61187300060f615749c4635080168f945cc63189100070bd9474189324400143d941cd65c80100058b64a645d764c40018d980a0c71580420071359663dc943040018ae8619
  | 17 => 0x45740c92000617a1c6518d424400191d7520d428c54000533259811cd4248001c1c759506350110004ab653835c362440012749160873594100061ddd4815c9600c4010ef9761063d891000437e61311d952cc00183f756107258031005a364887d93634400149f97d93630c91000c1fa63705d461480015c893509701091000723dd163589320400189e32a18744c91000723190631c94344001a4f65a0f74d891000693194825d06344001c5b6518d700c9100052be517358b200400186d75e0943987300062dddb844c9100400307e981d165c8010005936548298c210400145e95a1c63c81100042fa63645cd2044001c2d655937250c10006a310a8610c3244001479901d36508510005936548218f204400168c9350821580410061ba1c7590960884018ac9761032185200052be5d64588320400168c945ce639881000c1f261655c0430400168d9420a6308410217230c97610c428400186f8520970185430058d644405d661d0001c556598c7150c10006279d88350a505000186e75a087098443005276587350d429440149d961cd43508100051765776dcd4244001879809d473185200058b65032594210400145e95a1c63085100061be1f6550f624400107f985d4329874000627218835d032c400183f652117308510005272517318f204405958c925cc43105100051d24572dd5601040183e86194744c91000517e4d42dd5601040189e8619373509100060fa1f65d91324400183d7561032987300050fa53875953204077d2421145740c9510061b61e750c86148001cc5710847118d420050f650325d461480010dd98d8f74885100051725d31dd5600c401ac4926047018d42007156447518d3044001cc86218d701091000617d94835d1204400183e86d97744c9100061721c6518d424400186f87989650c8100041f25d859856010c0186c851897010d1000617e1d7554e61cc0010fb985c070984430060f61d7595261d0001a94946047018d420056a650325c221040010dd96a0f74884100052b650731c56204001a1f851097018d4200687d96849cb63440018798061471580320061ee5787580600c40189c7620d424c5400052724d425c261d0c0187575a0774987300058b65073d9462440394ae96141740c9200060fa1375dcd60884010de980c8764c91000565644501cd42d000187686dc4754c1100042fa58845cf204400145d93a1f651091000639e08815c06150c014d8905c57018d420070dd94649c4434400147591142760c95000517a587394d425440107e98d95744c1100051765e5094c614c00145e951d063c81100069361421dc463508014b4915d17118d420061ba16829c76050c014ad94a1f624c11000723193731894244001875879d76198730004b3658835092004001a652161631185200052724d7
  | 18 => 0x7598e31040014749150975984430071359473d09420400143d9690975984430062bdd182dcd609040199473205435095100635dd883509100400129c9898d42d00100062b08687d45640c801c2c62d96740c91000617a1d6558d4204001a6565e0943440100043ba60325c0614c80186f87d95320c9100060f597845cd20040018778520570185430070bd9574d08324400119e9814073508410052b25f64d89324400185d75e0d4298730004b32498319063440018758759441084100041f25d850c9600c401c346461471481100070759564dcd42040010df9859473509100056524d421c540c400168f9461d635881000687616429c4635080149f975027118d4200647a107394d425440185e85dd67198c100068b997845ce6204001c35655907150c100041fe61750ca61cc00166591081751852000527a4f645cf40440014769114d760c65000627a1f64d8d424400107e980c97518520005a324d4208661d0001c1f651d3634c9100060fe1d7550a61d000143d9690b755804300527e597498c320400168f925d06418d100061d594815cf4004001a2e75610321852000699594815ce62040298ac815d1620c8100051b64854dd951c80014ae97190624c9100060f21d65991320400129c9858d4250010005a9e5183185214800189e7620d4290510004abe59840ca210400186e871d43258221007079d65498e4104001c1f515d0630c95000599646205d46148001c2e75d93620c9100062761a64dcd4204001c6962215701041000539658721c5430400183d65a137388410006a9c8281141640c80183d8759643108100051d245325d66110c0185c8598d70cc8100069948785500614800143d940cb755822100437e6163dd2210400183f875d6640c81000725190639c432440018ad7661032886500062724c865d03244001a2f7561032582210070799473d0d420400189e84a0e71d8142006a3611829c06350801c1d655cc43d001000687d9584dcb63440012ae94a0e7618910005a3e518298e620400143d97d97640c91000595646305d661cc00183f86995740c8100046ba63515d03288401a4d8510a7118d42006875d48350a61d000189e8799263508100053325d8458d6204001a1c6520d42105100068b994845ce62040010dc9858d74480100052765b511cd4210401a1c65a107218d1000527a5873d0d424400129d981097018d4200762c81801cd42d000151e95e047350b4000547255801cd42d00018ac8420970185430061b597825d1300400507d981d365085100052ba5a535cb4150001d6151549708871000617a16839c7604c801a656560841084100068d595840c910040012ad96211320c81000713d9773d89424400168f945ce639881000539259421c5204400152d9214d740ca5000517a4c545d831940011ae98d
  | 19 => 0x5957310410006279db845c863440015349150d7598443005b2640215c0635080307c9859573480100053325c63189424400166591941521852000627e52861cd424400162d9420b7558221006a908681141640c80162d941cd659881000517a4c875944204001a4c6520d741891000693e14215c063508015a5940c871483100051765c50d4863440018cf8758d43588100052b65c8358a41100014f296202710c91000437662711c063508014ad9421d624c0100061be1d65508420400145e97cc775580310058725132d9432440010de9720d42586500053365873d09420400183d75610731852000517656861cd42c4001a5565e0d42440100050f65072d9530440014d6911d4634c11000627dd88350951d0001a1e6520d421041011e2bdd9840c9518840152d9520d72d05400051765476dcd420400149f975017018d4200593a4850d4863440010bc985d9644c8100062b087865d0320400168e9421c63189100072a188645c0324400119d98140735084100687a17649cb634400146f9754d52185200061765e859c66304001a1c65e117218d1000565644801cd42d000149f97591630c8100058d646405d661d00018d5819c47018d42007075977498d320400186f75e0943580310060fa1d65d0d4204001c1c651d0634c91000517a5e631d530c400143d9799275d9310007231d263989320400189e946187350810004a7a588350841440010df985cc735822100719595621c53204001c56911d4634c1100043ee59809c432040018ac82e19740ca510061d5d48150e61cc00146c9261f6550d100060f21f7550960104018cc8758d43588100069361720dc463508010bf9850871583430073254d625c031040014ad940cb7058b3100617a1e6598d420400107f985d47518540004976635118e53c400183f75610325803100617d94835c8644400185d8699773508100070b20b655d0324400145e95dcc63c811000627e13835c2610c8016c49350b610855000719595621c5420400107e98d4676945400051b656735c3624400164e9520963588100060f61d6599032040012d69120d42584300043ba5c8250d619400183c86d95740c9100060fdd584dcd608840143e9421d650c8100c61b60175d8832c40018ce762094310d1000633a18631c9434400185e85a0c71583430061b20b655d032440014ac97190624c91000707d977418d324400185f65a0f72905300056524d429c7404400168f9261d6458c100061da17760c91004001a4d850847018d42006a950881500614800149f97992630c8100061d61d650c42104001c4e7558d620c8100060fe1e74d9432440018757520543185200070ed94645c04244001a8c42618430ca510062b5d180d88325440143e969d4640c9100070b99674588320400149c93509701854300517a54
  | 20 => 0xc3218c215400186d65e09731041000533a5c63189424400187565205744c010006651cc8150d429440151e952007350b4000527658531cd42d000107d98d46769473000723992631c943944012b49661032841100051725d311d5600c40107e98d957448110004b366320dc4635080143d949cb65d8d1000517e4d76595420400189d861ce5350b4000647e16851cd42d0001c2e75188640c91000467a63511cd42d000145e93dc97598740007071417498c32944018ac87d9143d89100061be1d75548614800185f87e15539873000517e55861cd4284001a4f6520d42481100052b65f64d883244001a1c85a117018d420041f65e8508661cc00145c9350b755804100687195849cb6344001a8d84dcc325822100627210835c0615080185f75e0d4258031006a324d840c9608840185f8754d52987300069c595800c91004001a65815d432185200068b197845cc62440014ae969d3620c9100051765c305d661cc00183f875d4640c91000627109861cd42040018758761661cc7300050f65073d97204400189e8619073509100051ba5e20dd5608840164c9561f63d89100062761a851cd42d0001a1f6520d42501100070bd9774d893244001c8c641cc62509100051b249765954304001a4f65e0d741891000517a4f525d8319400143e941c96558c1000635605701c0635080154f956007350a210078359743d08320400168f935d264988100061d594815d132040010de985d94310c1000699e01851852148087c8c329d84310b10005a36503218c21540012e696a044318910207230c97610c420400143e9414d76906500060f61e74d943244001a35652057259010004b326063508214400143d97d0575987400062b21e6450e62040018cc8798d43988100050fe5132dd56010401694916117018d4200707596641cd420400147691e1d65508100052b6587458932040014b69610c7150110006561cd8094d4294001a35652054310c100042f65c844c8605440168c9250c43584300070b9d3755096088481c8c425d8430c81000517a568798c210400143d951d8744c8100068b995841cd620400165a90d4e535803100627e4f865d032040018cd7620d4210a10006275d88350b31d0001a1f6520d42905300070b994749893204001a1c656107218d1000c1fe6175dc261d000162d940c965c801000723d9073d894244001668905455258021005a36508298f200400185f65e0d744811000695644855c063440014ae961d0624c9100060fa11751cc614800161c9350965108100061720c851d93044001c1c6519073509100053325d8498d620400189e7620d42905310061bd97825d0634400183d86596740c810005a5245439c4635080146d95dd87250d100062761c8418f40440010bd981d8640c9100050fa5272d96314400186c82
  | 21 => 0x84c476508310052765273d8f625400145e939d37558221006a320d435096088401c2e655d1620c810006339d88350842c400186d7560b749873000687194835c864440014ae97992624c8100ae2b9d9840ca214400185e86d9773509100068b196849cf624400185e87d9763509100057124d429c7204400186c829d5701852000636e1d53580600c40145f9561873509100052ba5d64589320400107d97a18650c9100070b18b655d032440014e6960c871481100060fe1d74d94324400149c945cc631891000569644505d0328840149d961407350841006a9590815cd620400145e951d2630841000693594825d2630400145d969d6739063100627e13835c26110801a4d85c807018d4200627dd883509400400143c945d9654c810005956466594e61cc001d84216047350841007231d0631893244001c4f651cf625091000693997835d2620400143d94e1d654c81000696d95801c8634400143d95ddb744c910004ba6408150d6204001a666261671d8b10006171d6831c56010c01c4e929d463c81100052b249741906344001c1c659d0630c910005962415194d608c40145e95dce73185400051b25d53549608840143d9520d769044000707d947350d424400168c9360a6498810006935948350a210400189d865cc43104100074c546545c241c4001c5565dcc715081000695a0450d486344001a4d65e0d74588100058e241411d5601040107e98d457018d5200723d9363dc9434400185d870c3658c5400068bd95849cf6244001a4c6320943941500062be5d840c9608840185f860c1759063100783950425d463508018cd8360871580421062b9d9840ca5048001c1f659d3630c91000527e59811cd42d00014ac9250e7610d500050fa5a75d90324400183d75e1132987300060f61e40d96414c00168c9350b20987400058ea43519516090401c2f651d3324c9100062d590815cd200400143e94dd9650c8100041f66032dd5608840146d9214d760ca5000437a6230dd9420c401c556558c71508100141f66365dd22144001c1e659d1630c8100062b20b7650d429440183d87d94640c9100061ba1b65dc94344001a1c3261671191320070b194641c9434400143e94d4976906500041f663515d8329440186c82d9573d01100051b25d21dd56088401a1f859057018d4200517657761cd4244001a2f65610328851000617217755c0634400149d941cd6358a5100693d9582dd36344001a6465a0443189100061d595801c543040010bc9761032586500061b21e6550e6204001a1d65e0d72990100061de14815c0615080189d8699073508100041fe5d85c826110c01655918c275987300058b648405d661d00010ed980ca71d81320041f660509c4635400185d869cc329465000715595631c53204001a2f65a1373d89100063361
  | 22 => 0x8a659d03204001a2c7561032582210051d644505d8329440149c935d173185400051b65476dc9430400145e93dc97598443004ab2518298e62040012e99620943440100060f594845ce620400168d94208630851000693594825d1630400146d92a1f6510d1000617214835c261108012cc9818d42c81100060fdd584189600c40143d941cd6508410006a908581141640c8018cf8718d43d89100042f65c844ca60cc40126d981d432582211dd59a48431c5525440145c935cb755804100695cc58508661cc001ac6810877518d4200517e5d6598c32040016a99021c64189100041fe5d850ca6110c01a2d65211320c8100052ba58835cb415000149e96dd0634c910005a36508718c624400183d86997744c8100061759683dd2210400146f9250d75987400062bc8287d45640c80149e97d90634c910006e8508815012044001a2f326167119132005a3e4987190634400183f85212760c9100062ba12829c76050c0165a90cc4755803100517a577398c2104001aa45161032185200064b5d5840c861480018af64e0973105100051d656811d943c4001a4f85c817018d42005272517398f200400149e961d3634c9100060f5d5840ca61d0001a8c21a0f515903200695cc7854c261cc001a4d6520d42084100061bdd4825d1600c40186f65e09744c1100051724d765954204001694915d17118d420058b65032d94214400185d7520d42987300042f66364dce214400143f97596640c8100056624d425c041c400189e86d90735091000687996841ca630400164e9521e63988100052be5d4350960884017849350841086100061e218855c03148001c1d6559073508100042fe61741d1600c4019558761661cc7300060f61d74d943244001a8d841cc32582210058ba54739926204001c65651cb7150c1000627618851cd421040155595a047350b100051765e635d763c40012cd9620d42884100052b25d6458932040015c89350970884100043be61721ca61cc00145e96e147350951007239d26298c32040013379854464953100060fa1f7590d60104018cd7620d4210810005272517318c21440014b5961d3714c81000687615749c4635080168f94608631891000547656811cd42d00014cf9761263988100068b594845cd62040016a9901cc64189100053325e6398942040010f7985c471580430052ba5b515d0324800183f652117218d10006a9e4981141640c80183f75a1072580310068bd9682dcf64440018af20e19740c8100061761a651cd420400178893509404821000639dd88250d1004001c946418e7110d100068d597844c910040015a994209700c52000517a547498f2004001ac5810877518d420052765b7498d320400149d961d1634c810005a324d4250160884010ee98dd1628c4100141f663759c5600c4010df9
  | 23 => 0x9250f75580410050fe55861d13284001c2d659907250c1000596241835d661cc00165a90cc7755803100713596631c943040014ae92dd27498730006875948350a4104001474915cb755804300535259539c73044001c4f651cf42509100052b6538758a3104001a65516086518b100050fa507259530040014d9901d063085100051ba4b8759543040014749150d7598740004a7a60645c863440010de98cc57018d52004b3a5883508424400149e97591634c81000715a14631c52044001a8f20a0c5059032007079957458c3204001a1d8418c32545500068bd97825cc6444001c576518e710c9100068b2096550d42040018ac87191431891000517e4d425d661d000119d98d447350b400043ee59809c4420405d38c9260e6410e1000635e0c815c061508018ce83a0a71d81430062b6538750f6244001a4d6520d745881000437e61311d942cc00183f65e1173189100062761a811cd42d00018ad762094310c1000533658421cd4294001c1f655cc43d011000617214835c0614c8018ac842097018532005a3a5282d8f624400145e970c0755803100617a1f7594d600c401879869c2759041000593a548718c6244001ac492a047018d4200687596841c9630400146d969d5620c8100ed1b65f5154a61c800194e732094394551005332498798f40040012af9260f765901000715614639c44344001a1c946167118d420068b996841cd620400183d87595640c8100041fa60509da415400183e87d9743509100051b65c209d4614800149d96d447350b400050fe5943dd56010c83c8c329d843109100043765a811cd420c00152c9250f75580430041fa5e85c81600c40192e7420943945510041f660759c96010401c986418d701091000713d9773189424400186f87d95431891000517654761cd4204001a55652057458c100060f61c65d90324405198c8220d740c8100070719275d8c32440012cd9620d42084100065c615809c443c400189d7620d42d001000547657811cd421040183e86196740c91000693dd483509608840186e861947250d10004376607498c210400183f65a1373885100062d190815c03244001c656598871508100069559483509100400185f6520d74189100070d597741c5320400107d9620d7294650005176587394d429400189e42a1873509100060f597845ce620400185e8518e71d09100060fdd7844c9600c401a56912157018d1000687617849c4635080307e98dd9650c810006c9d45840ca518840183f75a10625803100687594845ca630400107e98dcd65084100071a215625c031040014ac925d0745803100627619641cd420400183d87d96431091000719596621c5320400158d940c873543200068b1908250d5154001c2c659d3620c91000517a4f759d661cc001a8f84e097118d420070b9
  | 24 => 0x700d0420060170053dc00002d00600139a02e01d01203e00a08707e0190710a400a01206418c04a0022ab01500f2110030040001cc00300a02c02208400000607505501b06812600000102a00402400200000204a08600200001e0908cc00900000b0261830214f400103b07200300b01102a00000000601d03a0b400500200100800305f0000542de01f00100002d00000000400508200000000600c69734200300200c00e01209800800000307200106500000502300000500f00200900200900000100002a00004100a0f306f05100709407502301b02900700a02500a00612e21502b04903900000001004d06206100617900101100100301401600200005e00000300200a00d00000105c01501a00400a05400e0010bd00d0080110370100081ec01f03600208b00d0f506701f01c00a0030080000060000003f700e00a0310020001db0010010bc48e0040080000df03300104d01800100b00205000200603c03100002500500200000302500704e00100002500f0010080002fb00100001d00201400001700e00815c00401b0055310070080000070000050b700004e0220f900100900300700d00200400700004c00e00900900000100100000a00d00c00100d00200000000404c0d900f00d04711200200303701900100700400112f01b05a00200405c5540090030cc01c01e00000005003c0071d403800200201203f00403400102201f0000000061351eb0f301400021c31605300201f0090020db00502d0f203300800500000e01401202e09700000200161608200b0200200510050060de00201003c04700701100103f09600000e02406700202b03c00300008300602b00005e00100d00001c0b103e04900d0d100200900704b00400007a7be0030020001ec04f01354500a00700700801d40d0960061be1f655084244001aa49260450590320043be61721c9600c40143f95618744c9100052725d6458d3204001c1f655d3630c9101dd59249431c55254489d0e5410c7250e5000617214835c0615080125d989406394f100051764c875944204001c4f6518c7250d10006270ca861d13244001a1d652117258c1000687997845ca630400126e95a0e76189100062761c8418c4144001479901d175185200061b61d750c86148001a95642057258c1000617dd483509600c4018af87188640c91000687a16749c463508014e5961cb7150c100042fe5d840c8605440183d65e117298c100052ba5f64d893244001a8c93610321852000699e057554861480010ee97209435843000617a16839c76050c0187565600714c8100052b65874989320400168c9461c63189100060fd97845cd204400185e864c775501300058ba5073194624400199483205740ca10005a3e5187d8f624400185c86cc57590530004b565883509100400146c
  | 25 => 0x300001400502200200000003d0000000000111ef02001400e00a00300f0620240020f600000800500e06a0390130050060010010470bf08800000210900300508400100300100107c03101d01505200300205207600001c00300700000c00600200301600d13f0000020030c00000250130020050321db00602d15400900406f00b0ac01343101000108c00001000403e0020110135ca00366300401102400600400902701c00500600900100000d00000003b01000600005300000500301400a1650730065a801304201b02d00100c03d00100200101b00204b00900a00a0133410000000040230190b806601f0110004a300200000000006304f01506b00000b00500600200903301b00e0e500901402200005503703600100000011802c19b01201f04e00104600004b0000110010000aa0010b20530020510f900a2a700700102004b02800500f01c00704c02106903801501500003605a00000900101914223600200001b00702806100005e03b00900003a00001005401300000e00800303c00100100302100202003904a50d0270720020b50641770000050da09000300100509206100105b00400001c04b00f00000300404d01402002e00b02e0530620000090080d700000202206200000400300200600600500002d00101d00000300000005b00500303c00200c01e00900a08500300301502002f03500e0060000c901500c01f0111fa02c06b00000a0120000000100130010100060000cd00500900000300113100b00401500700800a0090020cd00000001c0b40120be04301d08500e00603e0000000b702501e15e36b00100900000700b03902e11f00200612000200500300000003001f01f00e00200506803d02a00402b38405300e00200200000001d00200400001a07006c01a02004c44d00101c06900503205e00200d04c01803300800901105f0140490070140260f301f02d05a00100a00800100005000201600000b09d01106b0bd00300216601d00000504100006503400300a00c02000302f00200901600000301103615e07701002300c0000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa4000a2a68082219740c91000581b463a2eaa10c29000308d876503218c215400145350e40432e81922000c2561a91a147350841005c0946a10833a8c290003a04415d483508614800110ed4f0b20ae031a8400d09191950c8714811000591146a1240b80c2a1802d80a3508415c0210400184649924432e81922000a19a9f80614614852000611b0cca06539ca390002a0ca2653855c06350801c073a6ea41a84b044245d0310893509759874000550946a1102a00c29000308c82a58835d0324400160ad08a0ba0c6192a000d0324b655cc43d011000505d503a2eaa10c29000340c925957310f4004001432d3cc4c2ce3b162000a25698732054350810004c534448283baac02080301d86255801cd421040144751729430e6a1220008956a6811407518d1000641b0a492e9388c6a1002499a624d425c2410400184649925c32e819020008a9aa7516103218520226818c449a85baac02080301d86255801cd42d000144651328c30e6a102000c83e14926117018d4200512b4c41902ba0640800320f85249745c0635080129250b2429ae8192a200e824807520d425804100611904cb106ba0652880320d85a4b849c46350801a06496cab988620a20008876a6852127118d4200681924b2ae62188208002b80a3508815012044001a1232b28190e29022000925285971097118d4200611924c32e621e800800301d86a56811cd42d0001b02b2926a10821082000a2a68092219740c91000603b0d4ad0239a842091340c4324963dd56010401c07bab09b9864b044200e03dd4831c9425804100611925432e621e808800228da8249749c0635080190bc2922c22e031a8400d03251755cc32185200061192e49b08190c29000308c9720d43508614800112ad4d02286a431a2000c856149150e7118d4200503f4eb2906a14831880380c82d94835d0324400110f54f0ac22e031a8400e032096520d740c81000512942ca30c39a840800288ca3651861c943040018464950cb988620a2000c23249865cc431041000443952c2a81388c6a100321585245749c4635080140f53eca41a84a026000e031d17520d42185200049934c49a84b80420800340e94dd7730c960884014465130e420c7a022047d0395296108735095100741241ba906a12c02080282ea89d375509608840151352722c286430a40008a5285981097018d422268188449a85baac02180288ca261c8418c4144001846c3328190e6a864000c2320a9620d740c95022e8188449a84bacc221802c0da39d375509608840144ad30e640a86a14a200c64645802007350b400050394cba906a1462a000288ca261c8498c4104001a82ca843408e6a108200c23619940ca739442100515340410eca1a848800281da7d948350a414c00194241922a1a8430a4000a2569883205740ca51
  | 1 => 0x108f00011e001c16a2000b1a00080040d20002204bf0410401060048004f8602000478118240000ac418e0002407020800306010862600aa228d42600215804100511d47ca50c392868800328493245840c86148089a0621126a16eab008200c23e5c9361032582210049494cca06438a408800308c82658835d03204001c0ab28e640a86a102000e035d5845cc321852000511944c390931e8008002a0ea2e51859c46350801342d3126a10821082000b05684505d2630ca5100451d50492e8b88c6a100380d7520e7250a61d0001314d1120a08eab008245d0318893509759874000611f2e41a86a12c11080303497595840c91004001c0ab290640ae81902045d0310c9258d75987400048c94cca86438a408811b40e54658421cd4294001614d00e8baa8430
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x21c046000408cba619940ca739472023700990dd4831c9425804100408cba61d940c8630855000600ca95d5845cc321852000600fa9dd584dcc3258221005809b01d17520d42185200060889368092219740c910004c81b628d421057008410
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4e
  | 2 => 0x94e
  | 3 => 0x124e
  | 4 => 0x138e
  | 5 => 0x8e
  | 6 => 0x150e
  | 7 => 0xce
  | 8 => 0x168e
  | 9 => 0xa0e
  | 10 => 0x130e
  | 11 => 0x20e
  | 12 => 0x154e
  | 13 => 0x24e
  | 14 => 0x16ce
  | 15 => 0xb8e
  | 16 => 0x148e
  | 17 => 0x3ce
  | 18 => 0x160e
  | 19 => 0x178e
  | 20 => 0x4b
  | 21 => 0x124b
  | 22 => 0x20056
  | 23 => 0x138b
  | 24 => 0x94b
  | 25 => 0x169396
  | 26 => 0xa4b
  | 27 => 0x14cb
  | 28 => 0x134b
  | 29 => 0xbcb
  | 30 => 0x240d6
  | 31 => 0x16d696
  | 32 => 0x14b
  | 33 => 0x198b
  | 34 => 0x2cb
  | 35 => 0x19cb
  | 36 => 0x94056
  | 37 => 0x124056
  | 38 => 0x138056
  | 39 => 0x168056
  | 40 => 0x58053
  | 41 => 0x583d6
  | 42 => 0x124956
  | 43 => 0x138956
  | 44 => 0x58953
  | 45 => 0x139256
  | 46 => 0x59253
  | 47 => 0x59393
  | 48 => 0xd696
  | 49 => 0x5696
  | 50 => 0x4216
  | 51 => 0x124216
  | 52 => 0xc256
  | 53 => 0x58a53
  | 54 => 0xc3d6
  | 55 => 0xd796
  | 56 => 0x59353
  | 57 => 0x16c256
  | 58 => 0x58bd3
  | 59 => 0x2cbd3
  | 60 => 0x594d3
  | 61 => 0x16c3d6
  | 62 => 0x16d796
  | 63 => 0x18d883de
  | 64 => 0x4593
  | 65 => 0x94593
  | 66 => 0x124593
  | 67 => 0x138593
  | 68 => 0x3d355
  | 69 => 0x3cbd5
  | 70 => 0x1343d5
  | 71 => 0xbc3d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 50
  | 8 => 933
  | 7 => 5700
  | 6 => 8600
  | 5 => 2850
  | 4 => 125
  | 3 => 8
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
  | 9 => 2*((h/23+packedAt gbK9 (1300+(h % 23)*6) 6) % 50)
  | 8 => 2*((h/381+packedAt gbK8 (34521+(h % 381)*10) 10) % 933)
  | 7 => 2*((h/1928+packedAt gbK7 (273600+(h % 1928)*13) 13) % 5700)
  | 6 => 2*((h/2901+packedAt gbK6 (507400+(h % 2901)*14) 14) % 8600)
  | 5 => 2*((h/950+packedAt gbK5 (199500+(h % 950)*12) 12) % 2850)
  | 4 => 2*((h/62+packedAt gbK4 (10125+(h % 62)*7) 7) % 125)
  | 3 => 2*((h/9+packedAt gbK3 (736+(h % 9)*3) 3) % 8)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe03fffffc01ffc03fffffd08f8ffcfe31ff
  | 1 => 0xf00ffc07c07fffffffc0ffffef72749323fe3f
  | 2 => 0xffff8007ffe07ffff07c0307c78e3c3cfcc
  | 3 => 0xfffffff800007fffff8003f807f03fc0ff0
  | 4 => 0xffffffffffff8000000003fff8003fff000
  | 5 => 0xfff0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10e200594494104940090a4a800481244e10d5
  | 1 => 0xa1042c028829a3929a40d4b50732349120e62a
  | 2 => 0x822b56a8144ed444ecba0701b05c58e2c34b4c
  | 3 => 0x44d9b34f90060873734e0063b806f03b40db0
  | 4 => 0x88fe3c73e7379e0061842183def8003fbb000
  | 5 => 0xcf01020020038100382084203efb7ed8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 6, 0, gbRaw),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 5, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 6, 0, gbRaw),(0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 6, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 6, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 4, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 4, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xeeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36563
namespace PEqualNP.Outside.L_meta_36563
open PEqualNP.Outside.L_meta_36563.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 68 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 33 := block_range (n:=33) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 129 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := bs2_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 9 := bs4_4_0
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
theorem bq1_3_0 : Interval q1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq1_3 : Interval q1Atlas 3 0 6 := bq1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_4_0 : Interval q1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq1_4 : Interval q1Atlas 4 0 14 := bq1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_5_0 : Interval q1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq1_5 : Interval q1Atlas 5 0 1 := bq1_5_0
theorem allq1 : ∀ k ≤ 5, ∀ i < count q1Atlas k, checkRow q1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq1_3 i (by omega) hi
  · exact allq1_4 i (by omega) hi
  · exact allq1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_3_0 : Interval q3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem allq3_3 : Interval q3Atlas 3 0 7 := bq3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_0 : Interval q3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem allq3_4 : Interval q3Atlas 4 0 12 := bq3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_0 : Interval q3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq3_5 : Interval q3Atlas 5 0 1 := bq3_5_0
theorem allq3 : ∀ k ≤ 5, ∀ i < count q3Atlas k, checkRow q3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq3_3 i (by omega) hi
  · exact allq3_4 i (by omega) hi
  · exact allq3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 3 := bq7_3_0
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
theorem bq8_2_0 : Interval q8Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 4 := bq8_2_0
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
theorem bq11_3_0 : Interval q11Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 39 := bq11_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_4_0 : Interval q11Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq11_4 : Interval q11Atlas 4 0 24 := bq11_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_5_0 : Interval q11Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_5 : Interval q11Atlas 5 0 1 := bq11_5_0
theorem allq11 : ∀ k ≤ 5, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq11_3 i (by omega) hi
  · exact allq11_4 i (by omega) hi
  · exact allq11_5 i (by omega) hi
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
theorem bq13_3_0 : Interval q13Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 39 := bq13_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_4_0 : Interval q13Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq13_4 : Interval q13Atlas 4 0 24 := bq13_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_5_0 : Interval q13Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_5 : Interval q13Atlas 5 0 1 := bq13_5_0
theorem allq13 : ∀ k ≤ 5, ∀ i < count q13Atlas k, checkRow q13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq13_3 i (by omega) hi
  · exact allq13_4 i (by omega) hi
  · exact allq13_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_2_0 : Interval q14Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 4 := bq14_2_0
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
theorem bq20_3_0 : Interval q20Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq20_3 : Interval q20Atlas 3 0 1 := bq20_3_0
theorem allq20 : ∀ k ≤ 3, ∀ i < count q20Atlas k, checkRow q20Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq20_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 125 := (concat bgb_4_0 bgb_4_96)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 66 := block_range (n:=66) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2850 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat (concat bgb_5_672 bgb_5_768) (concat bgb_5_864 bgb_5_960)) (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 bgb_5_1344)))) (concat (concat (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632)) (concat (concat bgb_5_1728 bgb_5_1824) (concat bgb_5_1920 bgb_5_2016))) (concat (concat (concat bgb_5_2112 bgb_5_2208) (concat bgb_5_2304 bgb_5_2400)) (concat (concat bgb_5_2496 bgb_5_2592) (concat bgb_5_2688 bgb_5_2784)))))
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
theorem bgb_6_4992 : Interval gbAtlas 6 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8160 : Interval gbAtlas 6 8160 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8256 : Interval gbAtlas 6 8256 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8352 : Interval gbAtlas 6 8352 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8448 : Interval gbAtlas 6 8448 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8544 : Interval gbAtlas 6 8544 56 := block_range (n:=56) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8600 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960)))) (concat (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440))) (concat (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728)) (concat bgb_6_1824 (concat bgb_6_1920 bgb_6_2016))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 (concat bgb_6_2400 bgb_6_2496))) (concat (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784)) (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072)))) (concat (concat (concat bgb_6_3168 (concat bgb_6_3264 bgb_6_3360)) (concat bgb_6_3456 (concat bgb_6_3552 bgb_6_3648))) (concat (concat bgb_6_3744 (concat bgb_6_3840 bgb_6_3936)) (concat bgb_6_4032 (concat bgb_6_4128 bgb_6_4224)))))) (concat (concat (concat (concat (concat bgb_6_4320 bgb_6_4416) (concat bgb_6_4512 (concat bgb_6_4608 bgb_6_4704))) (concat (concat bgb_6_4800 (concat bgb_6_4896 bgb_6_4992)) (concat bgb_6_5088 (concat bgb_6_5184 bgb_6_5280)))) (concat (concat (concat bgb_6_5376 bgb_6_5472) (concat bgb_6_5568 (concat bgb_6_5664 bgb_6_5760))) (concat (concat bgb_6_5856 (concat bgb_6_5952 bgb_6_6048)) (concat bgb_6_6144 (concat bgb_6_6240 bgb_6_6336))))) (concat (concat (concat (concat bgb_6_6432 bgb_6_6528) (concat bgb_6_6624 (concat bgb_6_6720 bgb_6_6816))) (concat (concat bgb_6_6912 (concat bgb_6_7008 bgb_6_7104)) (concat bgb_6_7200 (concat bgb_6_7296 bgb_6_7392)))) (concat (concat (concat bgb_6_7488 (concat bgb_6_7584 bgb_6_7680)) (concat bgb_6_7776 (concat bgb_6_7872 bgb_6_7968))) (concat (concat bgb_6_8064 (concat bgb_6_8160 bgb_6_8256)) (concat bgb_6_8352 (concat bgb_6_8448 bgb_6_8544)))))))
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
theorem bgb_7_4800 : Interval gbAtlas 7 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4896 : Interval gbAtlas 7 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4992 : Interval gbAtlas 7 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5088 : Interval gbAtlas 7 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5184 : Interval gbAtlas 7 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5280 : Interval gbAtlas 7 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5376 : Interval gbAtlas 7 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5472 : Interval gbAtlas 7 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5568 : Interval gbAtlas 7 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5664 : Interval gbAtlas 7 5664 36 := block_range (n:=36) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 5700 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat (concat bgb_7_672 bgb_7_768) (concat bgb_7_864 bgb_7_960)) (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 bgb_7_1344)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)) (concat (concat bgb_7_1728 bgb_7_1824) (concat bgb_7_1920 bgb_7_2016))) (concat (concat (concat bgb_7_2112 bgb_7_2208) (concat bgb_7_2304 bgb_7_2400)) (concat (concat bgb_7_2496 bgb_7_2592) (concat bgb_7_2688 bgb_7_2784))))) (concat (concat (concat (concat bgb_7_2880 (concat bgb_7_2976 bgb_7_3072)) (concat (concat bgb_7_3168 bgb_7_3264) (concat bgb_7_3360 bgb_7_3456))) (concat (concat (concat bgb_7_3552 bgb_7_3648) (concat bgb_7_3744 bgb_7_3840)) (concat (concat bgb_7_3936 bgb_7_4032) (concat bgb_7_4128 bgb_7_4224)))) (concat (concat (concat bgb_7_4320 (concat bgb_7_4416 bgb_7_4512)) (concat (concat bgb_7_4608 bgb_7_4704) (concat bgb_7_4800 bgb_7_4896))) (concat (concat (concat bgb_7_4992 bgb_7_5088) (concat bgb_7_5184 bgb_7_5280)) (concat (concat bgb_7_5376 bgb_7_5472) (concat bgb_7_5568 bgb_7_5664))))))
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
theorem bgb_8_864 : Interval gbAtlas 8 864 69 := block_range (n:=69) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 933 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 (concat bgb_8_288 bgb_8_384))) (concat (concat bgb_8_480 bgb_8_576) (concat bgb_8_672 (concat bgb_8_768 bgb_8_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 50 := block_range (n:=50) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 50 := bgb_9_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq1 (cert : Complete q1Atlas) : Lower true (roots q1Atlas) (target q1Atlas) 6 := by
  have ready : Ready q1Atlas (asRow q1Pos) (asRow q1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 24, 56)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq3 (cert : Complete q3Atlas) : Lower true (roots q3Atlas) (target q3Atlas) 6 := by
  have ready : Ready q3Atlas (asRow q3Pos) (asRow q3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 6 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 24, 56)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 6 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 4 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 6 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 4 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 4 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888eeeaeaaaeac8e888
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq1 : Complete q1Atlas) (certq3 : Complete q3Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : Sig) 6 :=
    slice_correct (ms:=fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq1 certq1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq3 certq3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 6 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00 : Sig) 6 :=
    slice_correct (ms:=fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0 : Sig) 4 :=
    slice_correct (ms:=fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : Sig) 6 :=
    slice_correct (ms:=fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 8 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36563.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[3,6]⟩,⟨.or,[3,4]⟩,⟨.or,[5,7]⟩,⟨.and,[0,9]⟩,⟨.and,[5,7]⟩,⟨.or,[0,11]⟩,⟨.or,[1,10]⟩,⟨.and,[1,8]⟩,⟨.and,[12,13]⟩,⟨.and,[2,14]⟩,⟨.or,[15,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36563

open PEqualNP.Outside.L_meta_36563 in
theorem PEqualNP.Outside.L_meta_36563 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq1 allq3 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allgb)
