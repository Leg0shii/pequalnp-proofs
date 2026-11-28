import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36274.Model
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


end PEqualNP.Outside.L_meta_36274.Model

namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
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

def SBf (j : Nat) : Nat := [8, 7, 7, 5, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36274

namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0xa3c50c005190000001210008a08024f003fc42fe41ff42fd41ff40ff43ff30fd10fc21fe21fc20fc31fe40fd30fe10fc30ff20fd20fc41fd32ff10ff31fc43fc10fd42ff41fd43fd40fc32fe42fe43fd21fd31fe30fe20fe32ff32fe31ff21fc40
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x81ef20082fca4194f15120ee992617d510cb7a8220ef50f42bfa92617c540c2fca810df55331bf290437c53082fca68877cc831ef29821dc43cc2dca4085794c20bea98217c504ca7aa8086fd0740bf2a441fb20882fca210cf95020bf28041ed21c837884a0efd0e43dfa16817f53442fca6205fd4143beaa043be425077a86205f54042bea80437d5110afaa890df55332be2a663dd53c86fca990df95210ee196637f53c437ea898df15010bf286877f53c87bc64186f50f41bfa9c43dd43cc6baa6217754c41bf298217e530caf8a8907e50040bea96617e52906fca418d754c41f6108417c540c6fea9105f54e32af29883bf40103da4210df54031bea94877e54482faa3a05f54221beaa021be540cbda40107bd4910bf29461f741906f8a4985f94032ef188617c5150efca420df94f40bf2a0417d518c2f8a9886f90e41bfa9a85df300c2faa6204fd5132bf2a4657d53487da429077d4d10beaa4219d4310ef8a9187710e31beaa487f521442fca690fecc230bf284637e540cafca7215f54e40beaa461bc544c6faa020df94632bfa9821be40502fea498dfd5132bea86437c54883bc65185f94431f710a43ef4290a7aa990df94b30dea1a836d520427ca9985f14910bf2a66377514827ea8885fd5020bea9a41bf4310efea6107b88420bea88417e544cafea9995fd4d40bfaa4657e51083be62985f94242dea1483bc544427aa81977d4d41fda02817e53c42f8a610f7d0f30bf28c877c53843dca4085f55241dea0e81fa40103baa710ef90c42ae29a85f5210877aa8084f55031bea8e87de324c7be6218df54c20bf29081bf42502faa5085f54841bea9443dc53507be87195f14131be2a6617d54c86bca72077cc230bf294817e54cc3ee82a0df54843bf29421f521c437aa8194f552219f2a4617c5150afea8887dcc6319f2a0637d540c2fea9087794c42bea9c417e53907ee6298df95310bea9c217e50ccafca9995f94c20fb90a437e5010f7c8620d7d4d20f7190657f54886fca618f74c730beaa463de324cafaa598df94f20ee996617e51cc2fca2184f950109f2a4437e51906faa7a15f94321dfa0a817d540c77ea8905f55032fb08221be4390bbaa7205f15021bf29c217f504c6fca621fd08610ef996617e50882faa120df94a42dea0081f451483f420085714d10beaa443bd54082f8a5887714d42bf280857e50d0abaa7a05f95231bea98855e53886f8a9995f54831bf29087ed52043bc63185f94830dea10837e51882f8a7105f54643bfa98437d51c837c84a16f55330bea8881bd4210afca020d794f21ef99463bf43902fca910cf15132f6990657c5250efea2a1df95043bfa92217e54042fca620d794c42bfaa6637e51ccafca818dfd5310bf28c857d5190afea4a1ef90d43bf29e83bf4350afaa610f78c531
  | 1 => 0xd53c877887215f94910bfaa243fa200837e87a15f14540bea9e837e509067ea898df94b41bf2a0817d52d077e86a0df95041dfa1e837f52c42f8a8106f95010bf29c817c54c82faa7217d08410bf288657d53442faa8105f15231bf288837d54c837aa9186fd5110dea1a85de43cc6fea2a05f94740ee190617d508c6fea690f754c42be28a617d538c6faa3207750c30fda04817d548cbbe63984f15131bf294637e518c77aa990df15321bea9e41f710043bc86187794f21bfa9a417f548c2faa5a1df94630bea9461bd42d02faa92177d0c31f790441bf42907b886985f54a41bfaa4637f544c6faa3995f14d10baa884176510837e86207ec4210bea88877e53482fca7a17e4c030ef994657d50cc77885a0dfd5130ee218637e54443ee42085f54043bea9c617c53c86fea8185f94243bf280437c544c2fca790fbc8720de20c81f5310c6fea5085f15131aea9c437d53d02fca710df55310dea1887f751482fca3a15f94232beaa2657c54886f8a9196f10e41bf288877e5210afca1086fd0641bf29885df318c6fea4085f94b10bea8465f910042fea7905f54b10ee194617c52502fea7105bd4910bfaa6437e52042fca721ef10f40eea1c61de53902baa6085f94440de21481ef210877c82205f14142beaa4817d528c7ba601857d4d10bfa8265be42903bc87186f90d40dfaa265dc53442fea6a0f7d0e43be292637c50507bea690770c430bea9883dc324c6fea2907b08620df2a661f641107de42905f543419eaa6617d518cafca4107750d31bea90615e53042fca1a0cf15110be28243ed4210afca3207d88421be29e217d51cc3bc8698df14d41dfa1083dd53082faa7885fd5021efa18657e53882fea70877cc832beaa221df4350fdc40907750d32bea9e437d54482f8a4085f54332deaa4437e508c37e84216f90541dfa1485dd43ccabca7a0774c832fb18863de43ccafea4a0df14d20dea12817f514cb7884207bc8621afa9a85f621442fca9905fd45429f2a6437e52cc77ca9185d14520be2a2437f50486faa3087790d32f799465be54887f660985f94c21aea9c81de304c37e8220fb14910ee98a617f54c837886a07b886209faa2417c53502f8a4a0fec4110ef298417d5090efca5a1df54e41bea90217d54cc2fca018df14e21dea1c817e51886f8a5087e8c030bf2a243dc318c2f8a8195f54342df21683bc41103bca7a07794e21df2a0417c54442fca3a1df14c10ee21c657f54cc2fea4a05f94b40bea84857f540c6f8a690dfd5032bf2a263bf40902faa9105f940409eaa4617d51d0bba6418f7cc930df210815d53082faa310774c431fd902417e50903baa6085f54a20bf29861f621c42fea89077d0d30de2a2657c5050efca2087714d20bea9c437e500c3bea6a15f95030ef29883ef324cbee4310df54343bea9
  | 2 => 0xe0e15c7e6f8000100115c0309c32610020042a0150b02800000640080d018000b8050002302c0002c060000b00c180180067c0103800000035d00201c010002677c0004c4a3a1220040501c00000010007e0d0040880202c07064030140e000000001101007004b70a00302036000180e0010881301009080020000604c0c01c01004067281200046614004080302824030036c808010e00000010000010280100038c08000000081104c01004576183102805000013e4da08c0104c021c1530e80f004080c40000807010000580111db001400130000002002402004020001c020392a891018050000500420088000140b04c1f02c000000200001005a1034000900f1782d014050040305023020000280502c190d0140a40409c1e000070000409002000002a4040280201406004000540508018001942e81600c07138410003e0780005c041580100c0d06408045a900efca198df94442beaa2617f54042fca5195f14f20bf2a0857c514ca7ca8197dc4210bfa82835f53507b886196f50540fc90041bc54482fca521f754f40be28a41ef4250b7aa818df54b40eea18876c52443eaa2105714d41efa1c633d54082faa5205f95230df21e817c544cbee43085f54430bf2a2617d500cab8a6907790c43de218837e51c837c83207d44010bfa8a617e50886f8a908774ca31beaa2637d524437ca818ef95321f2908437f5050bea8220ef10c42fb28841ee4210bbc6598df94010be29a855
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc540872e54548109758e51c825d658c43097594430ca3e6414a10c795153c863e64940309d987530825d6394421c7550434c25e63d50209758e52c429c6350540d9547200825e63153209bd95320ca9d640c630d9d48218423f6454d10a7191310c65d63d53218fd91534823f6454f10c754f4210b3654944209798c504863c6454f209b98b540425e63151218f992510871d54d0c318f99053c86786054d219718d540869c644ca31cbd53524431d5410c31c754d411069c63507408fd91508cb1e5454e2197d8d540865e6510d308f593530825f6550c30b9185200825e6394b109e181544875653544209758c540832d54548109758e529066f6548020c714f435065d63d52108f592530c31d4394043c758e548c25e6514d208f59053c423d6414c10c755331cc25e6394d209b58854042e5628842197d8d511025f63549109d597210423e65151319e980540863e6414530c7951438c25e63150208f191534871d5390f4097596430c2746548510cd552510829c6150c43d9544210834f5314910c7153534823e64141218f992518cb57531452097d8d544c65e6315031c715053482746154d209b997214831d54ccb3097d8d544865f654c43197d8d544426d6294d109b98854cc69d631094197597430c65e63153218f590504871f54d4d208f596540ca9d63106408f992538831d5350b40c7952328c23f6454620d514f514835753d45209798f520423e64150328f99053c423e65d0d41c7d50534825d6510c318f592510866d6588420d514c514825e6394d109bd89544426d6295110cd951510836551480209dd95411067561d52329758c54c863d64d4e219b988520425e63946429ed95200831e5454c109dd85544c31d53d04418f997425026f6550842a758c42d065e63d5221a7191314c25e6314a109798c530425c63548408fd95401025d63d4810c794c42902e462440108f191534423d6414c219798f52c425e6314c209758e544423f64542319798c548865c63551218f191508c67a6014c2197d8d518829d6310a40a759032cc7645288510c7953308c2756115030c794d439023e64d4c10c7152434cb1f54d4d109758e524431c5450f31a758f401031e5494c208f19152cc71c5450c308f99250cc65d658c830cbd50524427661153329e596100425d6395130c718d540c76452841109d584540831d5454c10c7553320cb3554544208f191510c23e64d4e21d914521482766588510cdd53514823e64951209d984530831d5310f409b98a544423e64d4b10d394e520425e6590d318f990540825d63152218f992534834c53d49108f590524c2776154d20a75924310e5e63d5321c7952318c25f6550c438f990540c65e6394821c7150324c63d6414d2197d8d54c42e460484218f191524425f654c8329d594210431c5350d42
  | 1 => 0xc71e540c6309b98b548c66f62551308f994425063d64940308f592520863f6454c219758c540431e5390640c754c4310a6e62d4c109758c54c823f64549108f191528425d65d0c32a7593308c25e63952209718d51d0a3c6454c219798c54c431c5450f32a719131cc31c5310941c7551320c63e6414c109758e5190a9d6310840a7191320cb1c53909429b988540423c6454d209798e524429d64cc030d314c52442756194d209798c520427461551208f993538423e6494720c755253c8764518812097596530429d640c9319d185544c31c63553309798c515032c54d491097994534423d64d4c10a718d421063e6494d108f993538826d62d50108f992530c26d6215030c754f42d023d6494e208f592518ca5f63542428f99250cca3d6494e108fd95431025e63951108fd91510c36552c40108fd9151cca7561d4c20a718d429063e64948219758c525029c6250c43d9d95210865f6354b41b9d95210866e6294d109ed95100431d6315131c7152314c65c6354a108f992538431e53d02408f59250cc74d53948108f990538865f63548409718d544431d63151329b98a524431d54d0f308f99053c826d6214c109d984540c25d6594c208f992544ca3d6414f209ed95401031d5410f3097996434ca3f64548308f99252c431c5450d329d984540831e5494f21a798e40503655188420c754f41d031d5454f219798f54042796015021d354d520429d640c830c7951530823e6494a319ed81544865f63553209dd85544823d6414e21c7d50534425c6354910c7952530434f53d49108fd91528423d65904409798e544831d53507408f990540425e63943418f993530823f65508428f19151cca3e64149308f990520425e6394a41c7550430ca6f65484218f590528427661d523297d8d528423d64d4b108f191500871d544c4318f590514c25e63d52209758c515029e648c1309b58b530429c6350b409b988540c36521540219dd95210865c63546209e580530872e5494810c7553430cb1d5454e21c7153534425c63553109798c540cb655244010a718d411065f63540219bd89534423e6414c219758f540831e53d0e40a7590328c25e63d5210d594e510823e65151109798f540c31c53d0d429d986534823f65504418f596540423d6494d10a718d425031d5494c1097d8d51d0a5e65d0d308fd954310e5d63148108fd91534871d4354443c714e415069d640c430cb552520426c62551109d984520423c6454232a758f409031d43548439798e54843645248710c7d954310e3d64949109dd95310c65f6354241cb150524431d5454c208f592534823e651513297d95320c71c63550329758f548823d6414f21c7552538871c5490d31a719132cc25c63544409798e510871e5494e218f191518823e6510d40c7950328c25d63951209758
  | 2 => 0x1014390fc06000f60000203c56000050080201808000480180c0000f02c040502700c01018186dc140000006c140dc0702c021601d000530080400004000020305900c2202824274000000900009004740040030c000b4b1044060000b06c1403c040301a001242340e0043a0080e010000ac10000260402400035004030fc0d1a80005473018000dc0b0080d00001018180040200c1f001850493702c050180c00000018000100b114010040c000020000200c0a098000000e00c080000f06c000583b010010340d01c0e0d4070000d05c57004d2008100003f000030a0010283a0005732c0304437000000e8070081e02c280a81e00c50000000008a043655208410c755132cc25e65cc930a7d954310e3e6494910c7150534431d5390c42a718d4210a7761549108f596540c63e65151208f596431065d63d4b109798c540431d5390c419758f540429c644c8318f9974350b1f5410e319798e51c831d54cc4319718d509071d54cc831d554e510829f6050c438f990530825d6394342c754d421071c548c9329ed95300c25c63553208f593520433454d4520cd150514823e6414d219758c504867661951208f99352042756114c20c7552530826e65149109b59652043375414520c7d50438cb1d544c7308f59252c425d63151218f592528c63e64951109758e548423e6495131d394d520426c6254d108f59251c825d63948219d58454cca6c62551308f997415025e6314940c7151434c71c548c93197d8d544827765440109718d544823d64d4e209758e548823d65950208f191520c25e63943429b988530423d6590c428fd95421071d53508429ed81534863f64540219718d52d065c6354021c7551320ca3c6454f10c794e429025d63d52218fd9153c831e53106409718d5090a3d64d4f219b58b548c67561951208f593538423e64d4f219d587540825e65cc530c7952438c23f6454b3197d8d544ca5d6315310a758c411036552c841097d95300c365611491097195434c69c644c930d554d510836461548109758c528423d6590840d9149214431c5390941c714d435063d64943328f590530823d641481097994324c65d6394341c754c431065e631502197195434cb6451c85209d987540831d53d08419b58854c
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x804e00c08000410000000003000200001435c85450f31838ecaa26418c1c76551320ca8b38ea821c65075da540ca3083aed2a0631851b7050e5010e86392a821a61439cb5410e31a2ae22a2861851471550434c20e3b2a899661071d9544c431838ecaa2639850d72151430c28ab88a8a1e65075d8540c931a28e2a1aa221d0c7250d5210e0ebb4a998461191d95244010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s0K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/271+packedAt s0K5 (17982+(h % 271)*10) 10) % 666)
  | 4 => 2*((h/204+packedAt s0K4 (20938+(h % 204)*10) 10) % 551)
  | 3 => 2*((h/28+packedAt s0K3 (1029+(h % 28)*5) 5) % 21)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 2 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 3 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8104044410480000a5090044802254501850a5
  | 2 => 0x248a48832490612c0a42a429521482a9432652
  | 3 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1952011814801c03000001c00000002c2094411118fd43fe10ff41fd42fe31ff42fe43fc31ff43bd43bc42fd20ff31fe42fc21fe20fd21ff40ff32fd31fc42ff20be42fe21fe41fc32fe40fc43fd40fc20ff30ff10fd41fc40fd10fe30fc41fd30bf43ff21fc10fd32fc30fe32
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x44080122878f10081cd3c080190884f053600aac061008118000820408a8f12c6dea4885d944309f29085af5250f5885906b108219eaa4433d5390a7ca818e750e30cf298859d5310a7ca52167d4d43b7a92835d538873a8698d794f409e2a2433d54042daa5204f553329f2a6657651ccadea4a1e750c30bba8a41ac420cadca5204f953319faa4653e54cc278a4a1c754c429f2a0613e5410e7ca8085b948109f2a4436d52cc73a86995d54430ae29a413d540c35885994f950329faa2433c548ca7aa9985b14910cea1e655d530427aa998d794c419e2a2415c53442eaa3996b1092096292876c525067ca9105b548109e2a2216e52cc758a4a1db14943aea98853d540ca7aa921eb94842cea1e635e530427ca5a1cf55031afa9a413c544ca7aa6214fd5132af29c433f54442bea6886b10a21aea98837451482dca4185b54830af298855d53d027aa9104fd5120
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x3004220000100040580000000a0000000800000c0000020100000000000000000000000000001021d6315121a318943cc68d6310b328b18954cc28d6310a21a3189438c30e5310a2187195434ca8d6310821c314c42483244294732c550d51ccb0d4354830c9108514822c6255031a358c424830c6254c428b594420ca8c6250c30c550d510c21d6395220a358c42c828c6250d31c350d52cc68c6250f32
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xe06bb4a621443035d85310920a0ae6210a2905057310a51cca8239286a8861411c94354732
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s1K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/37+packedAt s1K4 (2430+(h % 37)*7) 7) % 90)
  | 3 => 2*((h/64+packedAt s1K3 (950+(h % 64)*5) 5) % 25)
  | 2 => 2*((h/16+packedAt s1K2 (294+(h % 16)*3) 3) % 6)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 2 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 2 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xdc20c244f0c794010a29109b0233400011402c04c29faa2433c544c2f2a020dbd4941afa9a2175511027ca918ded41329faa26574514cad8a4885b54843b6a90615d53c82eca3105714d40af29e413f544427aa810cf950219eaa6413d540ca7ea8985754c21b7290873d548827aa918de940419eaa6633e54c82eaa3104f15121bb2886175510c2b8a6885ed4143aea988579508c67ca9104f95030bd280436e52cc6f2a010cf15132bb28881745150af4a118db94830b6a96633d54042bca610de141329f2a021785050ed8a4a0cf95331bba8a853d540c2eea2995794c429f2a0653c54442bea6a05bd4910
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/27+packedAt s2K5 (640+(h % 27)*6) 6) % 40)
  | 4 => 2*((h/28+packedAt s2K4 (1728+(h % 28)*6) 6) % 64)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 3 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 3 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
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
  | 4 => 2*((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 1 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 2 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 4 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4244451104250808a849a124065290944310b1
  | 1 => 0xca48c321292129416942a50c4286a584594594
  | 2 => 0x491080a5242129410844a52a8084a2980aa0a
  | 4 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2004c0a4700048400300700f0a5149a41ff30fe42fc21fc41ff20fd31fe31fa10fe30fe43f910fe32fd21ff31ff42fc31be43fd32bd41fd43ff32fd42fc40fc10ff40ff41fc30fc42fc43fd20fe10fe41fd30fd10bc43fc20bf41fe21ff21fe20fc32fd40fe40ff43fd41ff10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3060009e0210902160c00222002850c01b80120018500e1e810000c9603689810c8408012000020002a0300c801f01f0314437682885e94041aea9c857b5050a7aa920cf550319e29a833f544cb7487085d145329faa2633e540427ca810cf950419faa24177514ca7ca9887c885109e2a2417950106f6a0994f95230bc282657a500c6eaa2204f95232ce21c639c434cbe482885e54031bca804379508c67aa321cf94f41dc21a21f3314437087085e94241dd21a213c544c2f4a010cf94e439eaa44375518c2dca418cf552309eaa0419f5350678a998dd94420b6a90633d548ca7ca621cf95020bd284637551083388618d7d4d419faa2613d54c436282885794c20daa0e21f3514427aa8084f15132f8a0a215c53506f0a0a14f552319faa663b5414433ca621d754c20ce21e659c53506eca2205794c219f2a0637950906f2a110fc48510bb28c61b9414427ca910de940108e29a833d5110f6ea2a0ee506109f2a4633c544c6f2a3084f55021af29c857a50886baa610eed0610
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x400802010400184200800004000018000021c6355221a418d41442b16490510e4d8d41442b364cc510ac59031442b063505109c5845050b906350510b858831442b16110d10e410c314430c4354831c510c514ca946350710a518d4144298635051087594430c6d06350510a618d41842b16488510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x20268043588314424839ac910a21245d8430c510
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s4K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/54+packedAt s4K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/28+packedAt s4K3 (798+(h % 28)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s4K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf07ff03ff0fc3e1f1f0ff0fe3f81e0fc4f3793
  | 1 => 0xff81ffc1ffffc3e01ff0ff0fc7ffff0071c9fc
  | 2 => 0xfffffffe00ffffffe000fffff801ffff81fe1f
  | 3 => 0x1ffffff0003ffffff000ffffe0003fe0fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x150d118c492a6205078938960c8d2258471391
  | 1 => 0x21252284884226400998598245254a085140b4
  | 2 => 0x42104410229000aa20008228901094a180ac0a
  | 3 => 0xa588921201889335222000d22580432aa0f40
  | 5 => 0x8c610e39cce333dc9cccecc0046118c37df000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfee0fee0ece0ece0fee0fee0ece0ece0fee0fee0ece0ece0fee0fee0ece0ece0fee0fee0ece0ece0fee0fee0ece0ece0fee0fee0ece0ece0fee0fee0ece0ece0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4857d54c42faa2195f95320ee21a65bf40903be61185f95042ee18e617d549077a84215f55020beaa0217e520c77e87a0f7ccb30fd28063dd320cabaa7085f55132fb98c637f544c2fca9185f95020bea8841ef324cabaa7215f54a41bfa94217f5050efca4217750d30dea0081f721487f660985f94332ef29843bd54c42fca8085fd5310dea12837e53102faa7206fd0842faa0e217d500c7ea20085fd41419e2a2617e53903be6498df94031bea8c65ee204837e84a0df14930bf29083be4350fea42885b54831be2a6417d53082faa3a05f15110beaa241fb40502fca9996f50441be29a857c53506fca6905fd4810beaa0616e52103f080885f55243bea94437c53042faa9185f94210faa08837c504c7bc6418dfd4530ba28a657f53c82fca598f7cc631bf290417c544c3ba6218df15131bf2a2417651103dc859077cca32bf28c81bf41906fca998df95041fa908437d52cc2faa7885f94f40eea1e61dc438c6f8a299770ca31dfaa2417e544c2eca3185fd5320bf290615f53506faa998fdc4010f6a90637d54842fca5195f55131beaa6437f540cb7c80a05fd5030bfa9e43f521c42faa5a05f94c41bf288813f54482f8a9105f54c42bfaa2217e51882faa7105f54342efa1a87be43102fca1106f90942bf286857e54087de40105f94241bea88857950087ba6598df54810ee992617c548c6f8a690df94630de2a2417e5110ff260885f54243bf28e415f53486fea8905f94321bf29a21bd548cafca198fd94630bea9487fa20443f241086fd0a429eaa465f741906f8a710df94040bfaa4637c504ca7ca810df94642ef298415c53506f8a9885f94240bd280437c54043f680887dcc531be2a6617e544c6fca421dfd4d42bea92217c504877a86a0cf15120bea98217e5390efaa1217dcc721bf28e817d508cbde4310db54840baa8c617f53c42fca8185f55232bba8a65f721887f460187754e42de210817d538cafca7a0df94221faa88817c52042fea9187b4c921bf280837d50d06fea4a0df14b10beaa243f950086fea090df94b43fb98a21be43902f8a890774c030df2a0437f54487f461085fd4c20faa8c617f51482faa518dfd4b10faa88417e54442faa3185f15332bda8285bd54083be86996f95020af298817e530c7baa6207e94021be29283df53506faa418f78c530bea9c615d53082f8a610fec4210be2a0417c53842faa010df95330de21a857e5190efca2215f94b40bea98437e50083f081906f50440bfaa2657f504cafca5207b4c832dfa08837f5150b7887a15f14543bf29c857e52103ec20885f94343bea8c417d5010eeca2105fd4c10bfa92877e5410efca8207bc8220bea80657e508c2fca1a0fdd0541bf28043f731c42f8a8185f54a10f719643f7310877e85a0df14a10fca8483bc42902faa7a17794e42
  | 1 => 0xd42d06faa720df94231bea8e857e51cc2faa020fd14532df210817950907be8718f750c43be2a643f7108437a83207bcca32fd984617e518c6f8a4a1f7cc832bf2a0637c540c6fca7905f55031dea16817c53882f8a998fec8220ee29a837e51d0f7ea8985fd4142bfa9a21be540c77e85a05f94421bf296837e52442f8a2a15f14f10fd08021dc320c7ba6498ef50c43bf298417d50c86faa9105f95220ef98061fb40c82fca1197d88510fc902217f548437a87a0df14940f7290815c53487bc64997bc8421ef21887df53486f8a2985e14142bea9081f651102fea8085f15210f6a12417e53086fca7885f54843be29e437e518cafca918df14c20beaa4817d51d0ef8a0a1df95221fd10041ee21486faa810df94c30df2a4657d53103f68120778c730bfaa0417e54842faa4185f94e20bfa9281be42903b887995f15232ee218637c53502faa5a0df54f20de2a261bf41102fca5987ed0020bfa9c417d52d0efaa3905fd5031dfa00817f53842faa3985754c21bfa8a81dd538437886207d88421fb10e217d528c3f460885f54a409eaa043de434c2dca418fe90040bf298857e53486f8a6905f94a30bfa92217d50906faa7085fd5220bf290217e53d0be86390df95232bea84637d5390abca7215f14141dea12817d53d07b862985f54b31dfa12817f53887be6598df94742bea9c63df324c3bc6298fd90510bf288617d50cc7f620885f542219f2a621ee42482faa5107e10210fa988637f53086fea498f78c130f6a90817e52086faa9987b50842ef988637d53487f0a0a1778ca31bea80857c51502fca4197b94831beaa2617c53c82faa1a1fd94420deaa0437e51106fea2a1df94c43f6900417f53482f8a0a15f55332bf2a0655e53843dc6490df94042be2a4437e5290efea4985fd5331bea8c217d52106faa321dfd4d21eea98437d51ccbe862885f95310df2a6217d52c43be8721fdd4532fb20883dd53082faa8886f10e409eaa0417f53502fca6197d90710bfaa643de53102faa6885f14931bca80633d540c6fca0187e4c030bfaa2637d548c6faa2187bd0942bf296215e530837e83205f94a10af298437f53506fea9985f14d10bea9a417e53042eaa2205f54443bf294857c54087f261085fd5232bea8c817d53c86fea910fec8120ee29a43f431086f8a2905f946219eaa621f431c43f441087b90842bf28865bd540c6f8a8997e50040beaa4437e51042fca790de94031efa18637c548c3f681084fd5130fc880217d53106faa9906f90541bea9c437c524437c87a15f94043f6908435d53102faa2205d54420fca80637e51ccafea810fd50510ef21e617d5490a7ca8105f15032bf294637e54c87f4a120efd0c43bf280657e52906fca720fb4cb21bf284877e51906faa7a05e94241bea86657e53887f240107b50b20f7a1
  | 2 => 0x5000710d42b0640303c00024010008a0b0050056a2a00014c0301001000050000f0080400000000000000264c0355408028000000100000000bb0000002800004190042b000060040112c0008c000300002017224250400005c0404c1c00c00000033600c018000102f00855000f1748bc00010018000000006c03094010080000400000500040201400008100000202a350085524c0001800000000142a0000f008100182b034000040900801004000000302800000000000d0001e004000281d6a80700000000001480001400044002a40800005048181780000c01000201a4000a04723c03000020000115c0001c030000043c000002600000008180000800c08020000100000001020062517f01c3e9040000000045db028090000302c0011c8300c270000301c09058160605a0440747407000010047d000003b0620a80102801428940000000000048700642c0001a000010180c0200f030000000042c000000400c0f0241c000000000003c0f0040512400004040100b0780c00020000050b8080000301c00000010340d000000000000c100004700034bea8c857e5090b7c86a15f94010ee99661bf435077e8721cf95031fda82857f54ccbbca70877d0f329f2a4657e510c6fca8995fd4532beaa0657e53843f080105fd4131fb188637e51082f8a890df95121f719065b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8548437160145329b588540431e54cca32ce552500c6e962103209ed95401025d6314910ae18142d069e648c932a798e421023f6454d10cb588544831c544c930cd945411023c64543318f99053086766115230cb90d521033a54940219e580540c65f63547209dd95210863e64150318fd95401033a5454021da94a500c6796014e21c7952530827661d50209b988540c3355494420c718d540c63d6494b318f596540c67561152309d58753082f2600c5108f59353c436952940319b988530425f6355221b5986304c32c5490920cb952520c76860548409dd95100425d63d53218f59353c865c63551219798c540865e63141428f99252cc31c53d0d41cb951520c6796510020d654e500865d63d50219798c54042d463507109798f54c865e6514d219798c540c27561d52309ed81544ca9e6390a40bc98630442cd620c5309e58251d0b3664145329758c548435a534c210c795253086796014532d394d521032d52108409d584530825f6354910c7951530865e65cc931ae982415065e6314810b598e104427a6014e21b518532cc75553544409758e509072d52d004097d95320cab860508429b588540c66d6215030ae191308432d5250040ced06509065d63d50209d987548c25c63547408fd95411069d640c5309e58354ccab864481109d9865090e5c63544429b58b54cc27960d52318f990530825d63d4a108f59252cc31c54cc9308fd91524427661d4e209bd954210ad4614cb309d984520435a6394241d3149324c23e6515120d554e510825e63149109b98853c42b8644802097d8d544c67b654c0308f992518c2d4614c832dc982511027465485109758f54c832c43548408f990514cb7221540219e980530863e6515130d594d511023f6550842ce9085050b5553544209798e52d034d53c84218f997425027661951329b98b54cc27a6015031c714f425065e6394d2197d8d51d023d65950208f592518c27a60d5332b5185324c27960d4c21d394e521034d528c831c7551530823f64540329798c530873564145329d594310865d6594c209758c52c42e5620c7108f99353c8677654c431ce552500866e6295131ae181425065e65d0d32d594f108427461551329e195304427561150209e580540ca3e6414a10d354d521025e6314a108f99251042ce62d0d32d310d520c65f6550c439798e544863f6454d208f59352c432d52504409718d51c83712154021c714d425063e64d4c21d3d0d520c65c6550d30ab98a4350b3a54940319b98b540c63d6414e21d658c5050a7561150328f990524425e63d50219e980540ca7561d50209e58354086766114c209e596100423d6494410a7992328c72d5448020cd951510827561942438f99053c425e63152109e58251d0e776154d21ce951500c73654944208f590530867a60d5031
  | 1 => 0x3d0314c1109798e500426d62152309e98053042746154f209e983530863d6414b10b358831cc23f6550c43d3549310c7716114142a798e4250a6f654c832dccc5500865c6354910ce153204825e6314b10dc546200826d62d5031c794f4290a7a60d5221cb551520c6ba64c41108f590530426d6214c108f99052c42d96310110c7152314c3565354420ad590314426e62150209718d548865e63d50208f99352c433954540218f19150c863c64540329758c548826d62152109758c540871d63151309718d544435a5394021ba588404431d5350440cb54a421023d65908409758f548431d53d0440ba18142c831e5454c209d58650cca3c64549109d195414426d62951318f992520ca3e64150209ed8154c87a942d0320ae58043102e5620c72197d95310c73a43141428f59353c83c532cc721a7992320c65e6315020b918532c87366195310c7150314c31d5494c209798f540ca7561951329758e508866f65480208f992544c3544314532d3588534866f65484218f99054087366494630c754e431027a65d0110b6980314c23c6454e20d5d0c514ca3f64543319b98854043703154021cb54b41102ba64c42109d987530836952540319e18154c875a6094e108f590530825d6314a109798e52d065d658c8318f99252cc65f6355121d954a511025e63942418f990520423c6454d108f99053886b5640c7109e580530867661141429e980514ca7561152209e98052042796015021ae18142d027b6055121ba588408427661150108f59053c42766115030d9949511029c63504409ed95200827b6544010ae181425031c5490d309d997314423e64d4f10b518d214427561d4e209bd89544427860551329e583540c65d6394b40d5947308c25d63150108f59052443c6320c7218fd9150c865f6354442b5584430c74d5348421d354b310c65e63d5320cb553200825e6314c209798f548433654507109dd8553c823d6494d20d698c5050a7a6015021d9185520c66c6254d109758e52d06d4614c9318fd91538823d64d4c20c7552530876a5254031ce10c5050b2c5250941b658c408425f654c0309e983540866c62551108f990530427a609474397596530865d63150209758c520429c6350640d694d500865d6395121d994a511027561141428f592518837260145329d987530423e6495120ae191304426e62150318f992518825e6394221ce553400834d520c8319e181544877151d00209798f528427960d5221b518d414425e631522097d8d544427a60d50109b195324867a60d5231cd551510833860550209758e500426f6254d109b58853c423e64d4f20ce551500c69d640c7309ed8154482d46348710d514f214866e62152309b98853086776155132d314e32486786548110bc984404437260946308f596540873564946309b98
  | 2 => 0x36040382014702b008020007b60e81500080220a1392402040129cc25b0482526003602003660612800721a1e800000f01470205300420000012803050002c00401380002000c958ae1701001be4f060c550020e004ce00000cc2e0e1b84804172001c220000034000412824040600000009f270ec7a192b80808004302800260230400001c029f229000040059020040001012ac08060080000d0008200407008c4fa057d8080206068a028360a810000a52808d8191201812000580008080a82400075100400010080402150001c00135d84414131680af2609051097594430c7726114142b518d21087aa42103209d584540c2b864482108f590514ca3d6494832c7553430c75553cc4218f590520437151480209b195424827a6094742d5185530863e64d4c209d98650ccae5620c510d654d50086766115032d658e50907565394420c755153086746154d209dd9541106766115020d554e51103565394440d58c8514cb4d5394840ec504404423c6454d20cb552520c65d63141428f99253482776154d209d984548837151100208f593530863d6414a10d9549511
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4008400008000000500802100012002010100000400041a458d4110110a54e5218a0a156170185520c6e0b9062982218a1486050941d20c818a608860e6454a320c6a839a42a8043a85894110110952ed210819056171181521030a2a0c299261645d0314c110b20e6a08808851a739085050b28b1ac228285519cb4314532c30a630284a0cc5768c831c860ebb0a818a614a5c04354840c88a430a6498516748c8514cb18322a2900418c5916014532c1cc6a94842060c6354941103062a2c418a61515c44354831
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100000000089187190314c110c80645c8314c110c80735894110110
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
  | 5 => 2*((h/329+packedAt s5K5 (17064+(h % 329)*10) 10) % 632)
  | 4 => 2*((h/192+packedAt s5K4 (17974+(h % 192)*9) 9) % 473)
  | 3 => 2*((h/44+packedAt s5K3 (1421+(h % 44)*5) 5) % 29)
  | 2 => 2*((h/22+packedAt s5K2 (180+(h % 22)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff03fc7c70f1e3f1fffc7e0707c19f793
  | 1 => 0x1fe078ffc3fff8f01fc7e381f8ffff8066c9fc
  | 2 => 0x1fff80fffc07ffffe007fc01ff007fff870e1f
  | 3 => 0xe00000fffff800fffff80001ffff8003f80fe0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42431011880888010609048cc1231118085391
  | 1 => 0x44490122890201200a4321144849250822c0b4
  | 2 => 0x88842244109500562004482112044a61850c0a
  | 3 => 0x819654892281929b54900049a4960232d80f40
  | 4 => 0x1118600e332624ec9926927000180c4377a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q4K4 : Nat → Nat
  | 0 => 0x2000000080000600000000000dd43bd43fa10bf41bd41bf43f9109d43df31dd31de43ef21ed21
  | _ => 0
def q4K3 : Nat → Nat
  | 0 => 0x1084c0224c036282887848510cca1a21c5314873287084755243c6a1e438d434863aa898f44c510d2a0a431d53d063aa998c7d4543
  | _ => 0
def q4K2 : Nat → Nat
  | 0 => 0x43814348510a45913144285644c521
  | _ => 0
def q4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 14
  | 2 => 3
  | _ => 0
def q4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q4K5 (i*5) 5
  | 4 => packedAt q4K4 (i*16) 16
  | 3 => packedAt q4K3 (i*27) 27
  | 2 => packedAt q4K2 (i*38) 38
  | _ => 0
def q4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt q4K4 (208+(h % 25)*4) 4) % 13)
  | 3 => 2*((h/11+packedAt q4K3 (378+(h % 11)*4) 4) % 14)
  | 2 => 2*((h/8+packedAt q4K2 (114+(h % 8)*2) 2) % 3)
  | _ => 0
def q4Pos : Nat → Bits
  | 0 => 0xfd4e7cfb8f77998f998e3e44e733399ec08c6e
  | 1 => 0xfe77bf7df07be1f3e1f3cf87183cc1e77d1093
  | 2 => 0xff87cf9eff83fe03fe03f0f81fc0fe0782631c
  | 4 => 0xbff80fe0fffc0003fffc00ffe000fff80383e0
  | 5 => 0x3ffff000fffffffc000000ffffff000003fc00
  | _ => 0
def q4Neg : Nat → Bits
  | 0 => 0x4908100011082108210400021100882040426
  | 1 => 0x0
  | 2 => 0x828102012010025002402080a005004082118
  | 4 => 0x5005680fa420554a510095d5408aa5501382c0
  | 5 => 0xe0040ad7c8425100554929e694aa045023d800
  | _ => 0
def q4Atlas : Atlas := ⟨5,rawDecor 55 q4Pos q4Neg, 0xfefefefefefeececfefefefefefeececfefefefefefeececfefefefefefeececfefefefefefeececfefefefefefeececfefefefefefeececfefefefefefeecec, q4N, q4R, (fun _ _ => 0), q4I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q6K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q6K4 : Nat → Nat
  | 0 => 0x20205550601f710bf40bf43bc41df30dd30bd40ef20ed20be41bd42bf42bd43f510
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x183f24c1208ea98831d53d0ba260884b548419ca8083b140443c240884b54b43
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q6K5 (i*5) 5
  | 4 => packedAt q6K4 (i*16) 16
  | 3 => packedAt q6K3 (i*27) 27
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q6K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q6K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/3+packedAt q6K3 (243+(h % 3)*4) 4) % 9)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0xfdeef8773e7cfc733e7f988e3c718cf3f8a427
  | 1 => 0x7e777f87cf9f1f83c78e60f3cf8e0f3c8158da
  | 2 => 0x9f879ff80fe01ffc07f07f03f00ff03f06631c
  | 3 => 0x1ff81ffff0001ffff8007ffc000fffc00783e0
  | 5 => 0xe0001fffffffe00000007ffffff0000007fc00
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x8080008102002404081000104402041008084a
  | 2 => 0x28382910a40949205402a9029124a02a126114
  | 3 => 0x5003d2220152924200a552a402494a802582a0
  | 5 => 0x1b5dfc44a958036aa549fccb2b60628a47f400
  | _ => 0
def q6Atlas : Atlas := ⟨5,rawDecor 47 q6Pos q6Neg, 0xfeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeea, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q8K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q8K4 : Nat → Nat
  | 0 => 0x10002041000bd43bf42bd42fa10f910f510bf43f710f110
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x8010808800004b54b43d82a221b1434436684886cd51108ea9e85b142442e2a3086cd0d10
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0xa458c54442a16215110a858b434429163d0910
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 9
  | 2 => 4
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q8K5 (i*5) 5
  | 4 => packedAt q8K4 (i*16) 16
  | 3 => packedAt q8K3 (i*27) 27
  | 2 => packedAt q8K2 (i*38) 38
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q8K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/24+packedAt q8K4 (144+(h % 24)*4) 4) % 9)
  | 3 => 2*((h/24+packedAt q8K3 (243+(h % 24)*4) 4) % 9)
  | 2 => 2*((h/8+packedAt q8K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def q8Pos : Nat → Bits
  | 0 => 0x3de3f8fc7f0f18f8e631f1f87c71c7e38b3273
  | 1 => 0xc1fc7f1f8ff01f1f183e3e3f8781f8fc15c39c
  | 2 => 0xfe007fe00fffe01fffc03fc007fe00ffe60c1f
  | 3 => 0xffff80000fffffe01fffc00007ffff00780fe0
  | 4 => 0xfffffffff00000001ffffffff80000007ff000
  | _ => 0
def q8Neg : Nat → Bits
  | 0 => 0x4290a40812221010010504914105229011231
  | 1 => 0x40491240122240202012121114809249014294
  | 2 => 0x88122009244402500a4024822124009226040a
  | 3 => 0x108004924888100254a4800442492400580940
  | 4 => 0x2112449800cc94949f292926600c24127ea000
  | _ => 0
def q8Atlas : Atlas := ⟨5,rawDecor 31 q8Pos q8Neg, 0xfeeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x220102f18de32ba6170cae18df30
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x40000008c424c25906328e428c6510530
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
  | 3 => 2*((h/16+packedAt q9K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q9K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q9Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 46 q9Pos q9Neg, 0xfcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x21b02e995c30be637ccae98de30
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x4009541cca5504308d420c2350b31
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/9+packedAt q10K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q10K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q10Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 46 q10Pos q10Neg, 0xfcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x20000b82e18df30ba6178c6f195c32
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x8e428c65906328c424c2510530
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
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 30 q11Pos q11Neg, 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x108000002f98dd32ba637ccaf185c30
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x95410c25507328d420c2350b31
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/1+packedAt q12K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q12Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 30 q12Pos q12Neg, 0xfcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x300cd32dc6574cb6995f32
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q13K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q13K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 4 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 4 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 53 q13Pos q13Neg, 0xfafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x4000084c32bc65bccae196c32
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x2390a32
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q14K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q14K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 2 => 0xfffffffffffffffffffffffdff8ffffc7ffe3f
  | 3 => 0xebff0f3ff8e0fcc
  | 5 => 0xf3fff03fff00ff0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff4070220a092a0d5
  | 2 => 0x20864414425462a
  | 3 => 0x1512e8669086b4c
  | 5 => 0xe248eb92418db0
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 45 q14Pos q14Neg, 0xfaa0faa0a0a0a0a0faa0faa0a0a0a0a0faa0faa0a0a0a0a0faa0faa0a0a0a0a0faa0faa0a0a0a0a0faa0faa0a0a0a0a0faa0faa0a0a0a0a0faa0faa0a0a0a0a0, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0x140400076906f32d843b8877906c32
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0xa441482310d208e43886990732
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
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 3 => 0x72ff81cffc070f8c
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 2 => 0x142322862122c64a
  | 3 => 0xd49751b48546b8c
  | 4 => 0x38241ac92608d60
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 29 q15Pos q15Neg, 0xfaaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x14202e98dd32b8617cc6f185f32
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x219541cca350b3195410c2350830
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/8+packedAt q16K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 29 q16Pos q16Neg, 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x200000047d086d21be63e442e98ef21
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x3848510c53148744c510
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => 2*((h/16+packedAt q17K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q17K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 1 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 2 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0x424880910426
  | 1 => 0x0
  | 2 => 0x241415020918
  | 5 => 0x18016a2012c0
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 39 q17Pos q17Neg, 0xfefefefeececececfefefefeececececfefefefeececececfefefefeececececfefefefeececececfefefefeececececfefefefeececececfefefefeecececec, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q18K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q18R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q18K3 (i*4) 4
  | _ => 0
def q18I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q18K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 2 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q18Atlas : Atlas := ⟨3,rawDecor 23 q18Pos q18Neg, 0xeaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x1004000400003c885f31ba63bc87d086d21
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x400001344c510e12144314c521
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => 2*((h/16+packedAt q19K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q19K2 (78+(h % 15)*2) 2) % 3)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 1 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 2 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0x424880910426
  | 1 => 0x0
  | 2 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 23 q19Pos q19Neg, 0xfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeecec, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
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
  | 0 => 0xffffffffffffffffffffffbbc79cf8fc38f793
  | 1 => 0xdff9ff3f1fff09fc
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 3 => 0xf3ffe03fffc00fe0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff44742918258a6391
  | 1 => 0x20940049089220b4
  | 2 => 0x1101502242248c0a
  | 3 => 0xe211ab49304cf40
  | _ => 0
def q20Atlas : Atlas := ⟨3,rawDecor 15 q20Pos q20Neg, 0xece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x400007110f221d443d087710
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x2c50610
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q21K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q21K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffafcc9ce3b9f3273
  | 1 => 0xcff0e73c3e7c39c
  | 2 => 0xffffffffffffffffffffffff7ff07ffc07fc1f
  | 3 => 0xfbfff83fff80fe0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff506921208d1a231
  | 1 => 0x30aa0864152a294
  | 2 => 0x9005009004040a
  | 3 => 0x60002922000940
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 15 q21Pos q21Neg, 0xfee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def q22K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22K3 : Nat → Nat
  | 0 => 0xc100002e986d20ea21bc82f987710
  | _ => 0
def q22K2 : Nat → Nat
  | 0 => 0x2007848110c93048344c110
  | _ => 0
def q22N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q22K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q22Atlas : Atlas := ⟨4,rawDecor 15 q22Pos q22Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x400001c12800000020000000029c43270000004000800000150010130001801ff40007fc8001fd41007f50c01fd52007fc4001fc43007f10801fd42007f44001fd31007f8c401ff32007f48001fd21007f55001fe43007fcc001fe54007f94c01fe32007f0c801fd30007fc8401ff43007fd0801fe21007f50001fd32007f08401fc31007f94801fe41007fcc401fd53007f54401fd50007f90801fc41007fd0401fe51
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1aa80eff88231005fac898803fe5350001feaa06400bfd8543007f8c498837fe104c403ffa8a2000ff94931007fa64a8002be6408401ff9908200ff18954077fc8118803fe4244001fd9826000ffd9110007fe8790803fd54440017fb1aa800ff4c941007feca88003fd53c80017eb28621affd4843007fc6290003fe31cc0017eb108600bf59242007be6598803fd524801ffe2066200f7cc931007fca2a0002ff61480017fb2a8600bf98c41007fc64a081ffc3048431ffa808400ff5973009ffea219017ff52d00017fb0a800fff84331005fac110803fd52cc00ffe3024200ff55132005fec4a9803fe420c4017eb1ca200ffd8954007fe6520802be648c825ff1806404ffd4b30057fc8190867ff51d0801ffa0e4000ffd9330087f8a598803fc3294401ff98a2000bf58a51007fca498053fc604c801fe1966200bf58b10007ee6298803fd51c84017fb2a6400ff9532009ffea81900ffc51c8001ff90e8000bf58653007fa8588002fd60d0c017eb2e2000ff8c950007f8c6a9002fd628c401feb222000ff19332007fcc999003ff42cc401feaa46400bf59330017fea490002ff65cc0017eb224000ffd0c32007fec090803fd4254401fe2166200efd0941005facba0002ff6350401ff992a200ff54921007fc64a8803fd31440013eb286216ff18332007fec099002ff64cc801ff29e6201ff15110007fc8790803ff43cc001ef9926000ffd0d20007fa86a8002fd64c8001fe1926218ffd4442007fec89000ffc53c80017eb224216ff0c332007fec498803ff328c401fea0aa000bf98c43005fac7a1003fd52cc801ff29a8200bf58740007fac488003f95044003ffaa22000ffd8b31007f8c690803ff21cc023ffa968200ffd8520057f8a190803ed42480017f31e8401ff99510005fac621002fd6008401deaa68400ff90f10007fe65a0802fd65908017f3186400ff50731007fc8598802fd6094821fe2a66200ff55331007fa8490023ff52484017eb288200ff59510007fc84a8002fd6290c01fea8a4000bf580310077a86a0802fc63548017eb266400bfd9541007fca721043ff50cc401ff214a200ff085400bffea599002ff64544017fb122000ff10d20007fa8598003fc324c001fe21a4200ff90d51005f2c120802fd6550401ffb266200ff54730005fac510802fd63480017fb12a200bfd8d21005fac221002fe6390801fe1908200ff10f30005fac319003fd6448001bfb2a6215ff0c232005fcc729002ff654c4017eb1ca400ffd0d21007faa4a083ffe40cc401de21a8400bf59721007fa6390847fc52d04017fb02a60aff943210077a85a0002ff6054801ff98aa000df94d500077aa8a1802fd61c8001fea0a6210ffd4731005facb20803fd64cc0017eb184200ff54f21007fecb98003f551440017fb02a800ff95321
  | 1 => 0x3ef328c801fea126200ff9452000ff8a688013ff51cc001fe21e4208ffd4121005faca88003fd5448401ff98e6000bf5953009ff8a619003fd424c02bff2846400f74cb30005fac918803ff3148001fea8a6209ff88221007fc8728803fe51cc001fe312a600ff90f31005fec8a9833fe200c427ffa986400ef90d43007fa8799002ff6590c015eb206200bf59221007fcc8880037e5494c017eb2a8400b758c210bffea199003fd53504017fb2a4219ff14f42007fec4a9802fc63540017f31e400fff14331007fa42a805bfe60cc825fe2006400ff193310d7f8a621803ff6250c09fe2a6600dff90131005fac221803f65144001ff29a420eff0c231047fea290803ff43c8023ffa868200bf59730005fec299003fd60cc801fb98a2000bf58342007faca90803fd54cc801ff2928200ff4c520005fec899003ff324c401fe98e6000ff54e42017f8a890003fd514c02fff32e6417ffd473203ffc6090803ff3254001fe1928000fd4c431005feca90003fc3254001ff29e6400bf59731007fec69000bff5448001be32a6200ff58520007ba8798003ff3148425ff0806400ff50e52005fac790002fe6344001ffb224200bfd95300b7fc6199013ff54cc003fe2922000ff90d52005fec890802fd650c801ff10a8000bf58042005fec6a90037c6550c01faa8e2000fb50b20007fe8398802fd62d0401fe192200dff18131004facb19003fe54cc41dfe1046208ffd5121007fe659883ffe20cc409ff32e6000bf18d200d7fea221803fc43c80017eb008615ff84232007fe8488003fc3150029ff0826400ff54720007f86418802fd64c402ffe32e640fff94331007fc64a0003fc414800dff2004200ef95143005fcc621003fd3148401fe9922000ef50f41007fecb99002ff6448003ffa9a2000bfd8121005fac5a182bfc30c8401fe3266008ff15121007fec688002fd62cc401feb024200ff94c32005fac32104ffc540c801ff2184200ff10730006faa8a9802fd6395001ff2966200fb4c832005fac990802ff6054401ff3166000ff18b31007fcc890003fc21cc0017eb24a400ff10910007fc64880037e5354c2ffe2a66400bf58643007fc8790037fe504c401fa90e2000bfd93300077aa8a105fff54cc801ffb2a4000bfd8552007fc8290003ff65484017eb1e8200ff50a31007fc8799003ff3150001fea1a2016ff14332007faa4a1003ff65cc401ff3122000bf58e21005fec6a8002fc6344001fe90a6000bf58742087f8a798803fe41cc001dfa128000bf5865403ffcc090803fd3150001fea0a2000ffd8730007fa8619002fd62d00017e31a420dff881310bff8a799003fc3250401fe3122013ffd4032005fac12a0027f6550c017eb2e4000df54951007fe6498003fe5344033ffa868400ff18d20007bc8698003f64144001fe3
  | 2 => 0x2105ffea790802fd638c819fe1006200ff10b30005facba105bfe20cc835fe2908600bf58432007f88688003fd514400bfe2968000ff54931007fa6390002ff64540017eb2c8600bfd8553007f8861905ffc51cc8017fb128008ff14d21007f865a0002fd6194801fea0e4200bf58331005fcc690803fd4288401fe3224200ff55321005facb10803fd420c42bff2046400ffcc940005fac199003df32cc001fea1264009f59741005fec6a8802fd654c8013fb2a6200ff4c951007fac399002fd6490c01ff2186200ff58730005faca10803ff424841ffe1866200ff50f21005fec998803fd52cc401ffb066400bf59443005facb19002fe63084017e31aa20bffd4321005fac920802fd6548001fe90a8000ef50940005fec498003ff42480017eb188200ff90d10007fe6528802fd65484017fb0a6004ff14b30097f82019003fc32cc005ffa9a4000ff90c32005fac919003fd32cc001ff9922011ff14f41007fa6490802ff64440017eb0e8600bf59032007fca790853fe404c801beaa2a400bfd8d42006faa4a80037e5354801fe20e4000ff95110007f8c890003fe4388401ff10a4007ff10121067fc8018837fc304c401fe18a4012ff14032005fcc71086bff5010c01ffa166000ff4c920007faa2a082fff51c84017fb2a2000ff50d51007fec6aa003ff624400fff0824200ff50520087fea598803fd6348409ffa9e6000ffd8542004faca2103ffc60cc401fe90a2000ff54930057fc6190802fd600c8017eb226400bfd89410b7f88199003fc31cc001ff2162000ff90720005fec099002fd62950017f31ca200bfd8950005fac998803ff324c801bfb2a86009f594430b7fc2199003fe5350801fea12a000ff54d40007fe6390803bf43504017eb222000ff90951005fcc618803fd43cc0017f31ca800fd88510007facb99023ff5348401ff21aa000bf58a410077a862181bfc3008401fea1a4000bf582430077a84a0803fd6548001ff9944200ff18542007da6490802fd640c401fea14a200ff54d1007ff84198803fd530c801deaa68600bf5823202ffea3a0002ff65cc801ffa0a2000af59232007f8c498003fe31c8001fe9928000ff50730007fa859882fff54c8425ff2806400fd50510007fca4a005fff53cc801ffa166400ff10f31007f865a0803be43d08016f3184200ffd8d42007fca819002fd63c4001feb1a2000bf59631007fcc890803fe6348401ffb1aa400fb8c921007faa39882ffc54c8401f72124013ff14432007faa890003ff31d0001ff29a400dff08131007fe6418803ef324c801bea8aa000ff18520007fe429800bff5148029ff2826400bfd8d20007fc8598002ff604c4017eb122000ff94e43005facaa1803fd4348401ff9928200ffd87320a7fc4099002fd6094401feaa66000ff50521007fca48800
  | 3 => 0xa188242727a078040684e0381006000568000e88a1c0020003c028080001c0e206029900416c020000e010cc80e0100401002fc6350401ff2126200ff18b30007ba6598803fd4248401ffa1e6400efd0e43007fc8690003fc64440017e31a8000ff0ca41007fca798003fe21cc0017eb166000ffd0721005fac418803fe63440017eb24a204ff19730017f8ca90003fd21d00017f31e8000ff54521007fc87980037d5454001df21a8400ff55131005fec2aa003f7318c431fe2988400ff50b32007fe6588002fd63440017fb2a8400ff4c550005fec0a1002ff6250c01fea9a8400bf59743007fca999003fd414c001fc9822000ff54940007ba6498803fc31c80017eb0e6407ff90121007fc62a0003f541c4007ffa9e4000ff10f32006faa6a8802fd608c401fe192a200bf59253007fe65a0002ff65cc401fea122000df55251005f2c010803fd21cc0017eb2a6200ff54910005fac721002ee620c403fe32a2000df94e51005fac52982ffc53c8401fe90a4000ff59121005fac720802ff6350019fe18062009f59641007f86518802ff6454801ff21a4200ff90930097f86019003fd54c80017eb1e4216ff90332007f8c398003fe32cc001fa90a2000ff50f20005fcc690003fd544c001feb1a4000bfd8542007f8c4a1802ff644c021ffaa66200f790f30007fe6490002fd6408401fea0e4000ffd9332007e86288003ff32cc0017eb108200ff54d20005facaa0002f9600c4015f3206200ff54f30097fc8019002ed620c429fe1826400fed011004ff8611082bfe10c84017f31c8200ff18d10007fcc399003fe64cc001ffa0a4005ff14f40007faa499003fe4394801ff28e4007ff9412103ff8a090803fe54480017f31e4200ffd8d21007ba649800bfc5148023ffa8e820aff10321007fe42a0002fd63d00017f31e2000bf59130007fe8398007ff5244001bf2a2a210ff197310cffea5a1003ff434402dfe0866400ffc8510007fca998003bd42d0401ff29e4000bf5804101ffea390003be5450809fe28e6000bf18d54007fe42a8023fe6548401fb98e2000ffd8131017fcca90002fd65cc8017eb048204ff14f30005fec688003fd62cc0017eb0484009f59421005fac690802fd65d0401fea9a4200bf58321007fe6490803fe61cc001ffb166000bf98f41007fa86a9003ff31c80017fb12a800bfd8931005fec0a180bfc5348001ff2a24200bf58730007fac999003dd434c0017eb288400ff98d20007fca598003fc61cc801ff30a4008ff1952101ff8a990002ff644c401ffa0a4200bf18d42005fec0a0803f92044001ffb126000bfd9540005fac1a0802ff6154001fea9e6400ff54540007fec198803fc63508017eb1c6207ff8812101ffea990003fe428c4017eb04a600fb4cb210057ac810803fc32c402dff2866409ff902
  | 4 => 0xbd0040b01a080060100000004000080002e0309c06822190be0100a0141c0000200008048081333c128021712404000038aa0000a285840003e00102050000780a010480b000d88b2008360284c078621a0000001a0517a1b0001c01200000019380608c018580315e04800e700eca8fc0e80a00030090080409001010178300598c06000118220bbe600012148120202c050029c804000240c8565c0100080e0c04005036018101c0040000200000360585980400006cbb520288e0000000d4809006002d81081e4d8088f8660001e0c05c0781e128020001a19158001420000411804530060013e00800450140bbfa100882004e03030150000080cee008008001c8aa3187acd2460180237090ae0000602604812050000303e33212058603a800018066380000a6e185720480a60328010760002a0103c1f0020100000802020000180c17808700021782
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xd6559332006bd640c831065fe70cc8310b7f610ccb10004fd76947300defe768c52004dfe7090e21007bd645533129fdc30cc931006fd7458332167de3259332004fc7655330006fe64d8730007f73254710005fe7348740095ff700c9300057c7355150007f121541100267f52d9730007f642cc510005f97088520007be74cc9411f7df320c930007f463545100a5ff704c9101fdfe7210f30007be5450b31005f571d0921006fd625051001d7e750c720006fd71d8930006ff6448530006fd75d89310ddfc7159120005fd7194d42004fd7610520006fd52d8141005fd7090b3111ff721cc5210077d6555332006bd5458b43007f762cc5100057d7599110004fd71d8954005dd73189100e5fe72d9510067f61018d1003ff62048510005bc7459520007f56354510067ec200c520006dc638c910055fd70c8550006fb325803106ff61058d10006ff65cc9101f6ff620c93000f7853541100effa7548110005fb7050920005de7394b30006fd65d8d100b5fe7019332006fd62ccb10005fd7598732006ff65cc94114efd6194720007f141541100dfed729852003ff61058910006fc43d81210477c5354921006fe42d8151004fd76c87300067f6550531004fc7359542007df3250730006fe7218d54005bf74581210be7c53597320477f5454d21007f97448110007df735533207efe2098d10096fa1058032004fd70d8931005df7358520006ff6558332007f552cc510007df6398d10005ff7254d40006fd7018d42007bc54d9120156fc51d8910097dc3018930006ff545843204efe21d89100defc3158910006fe32d8540096fc405803210fde634c721004ff76ccb41004fd76cca51005bd72d0e4300f7e65d9510007dd71ccb31007dd42cc931006ff5358b30007bd54d0b3224fee654c921006ff52d81211fefe76c8730004ff7650d10004fc7650b31007bf6410d10006ff6358520006fd7158b30007dd70cc931005f9700c9400fff853d0110006fc4358321007f9534811001f7c5494f20006ff525833112eff2159121005fe7695120007dc53d8d21005ff7050e52005fd7098d21005ff7050b32005fd7294d21006fd7458231006ff3258221005fe7390720004ff764c521006fc5358740066fe620c720006ff6558730006de630cb41136fe32d854217efc6254d40136fc63d0721006fe7218d100e5fc72591100ddff7388520007de4398b30006fd7648740005fb7048510036fe4058021005fd7190d21007ed654c921006ff65d9120006fc7358720006ee2058831006fd53d81421d6fe52d8520006fc32d813104efd70d8910005f571cc92104eff40d8910004fd72d8d54057f41098910005fc7348740006fc6318910006fc43587200aefc20d8d20006ff41583210a7fa504c910004fc7359320095ff700cb1007dfe70d8b31
  | 1 => 0x9541007dd71cc9310077f75cc950007bd6419120005bf7459520006fd71d8132166ff6218943007d732cc531006fe63d0920006fe7198e420057c7355251006ff65d8d10075ff764c73003dfe70cc92118f7f5255320005fe73909500477c50d95211a7be425083106efe7358730006fe63989100e6fd6210910006fe6418d20007f6425451001f3f5495320007fb634811003efc3058b1006ff51058730006fc74d85201fefd620cb30007f542cc71015dfd7210f20007f54254710006ff4358032006fc3258031056fc10d8520005fd700ca4119ff721d8121007fb32481100157e75d05200057d750c7200defe5158321005fd7694520076ff608c520156fc31d89101fefc32d8132005fd7090951006fd755832113ff7215452104ff610d8910006ef7458831005fe768c520006fe5458331056ff6098910007f9644c11003dff7048550006fe54d8121006fc6458730006ff63d812112ff4215912113efc63547210b5fc705533214dff720c720006fd64c8730006ff6518d20006fd6250b1018f7d6555032006ff624c951006fc6348510006fc7358a5111efe4298e21007dc63cc510004ff7058732005fe7390a51217f72148540007fb7148110006fc6498d20006ff73d854206dfe700c9311ffdc42ccb3010efe5258732137bd64d0720006fe72580310a7fa104c950007bd42ccb40007f5625451001d7e75d0720005ff7454b32007f66250510005ff7255132006ff64c8730007f7314c520005fd70d9521096ff650c95007efe50d8530005be7418910215fc73c854006ff8204c520005fd710cb4104efc30582210267f54d81530a6fc5058b300a7de104cb300057f754c521007f67448510005fd720c540006ff6458b3006dfc7018931006fc5358432006ff64cc950007dd3254730006ff505843218fbd425523224fef524c921006fc32582510b6fc10583320877f52cc5500dff6310c520004fd76d0520004fe76c8530007ed70cc93206efc305873003efd6248510066f8305803107dfd70cc550007f94248110006fd42587300b4fd7098d20007fa6254110054ff7158910007df3248730007bf6495110074ff764c73023fec5150b20005ff7650b30006fe50d85320afec20d8d20004fc7359742006ff3258730005fd7550b321e7ec5190920005be748c910006bd4258341007bc645092014efe51d8121006fc63505100a6fe3058b30006fd650cb40005fd7690730005fc7690d21004fc7654d42006fe5458720006ef725891003efd5058720007fb7058520037f51018520005fb7254110004fc765093003ff6204871003ffa10585202e6fc32d8552004fd7218d1018dff7255321006f94258031007f6620c5100e6ff62189100a7dd404cb30006fd75d8132006fe5458321006fc6354942006fe6350720005fe7395121006f
  | 2 => 0x177e65d9520004bf745953006efe10d8131007d8634c110006fc75588430057f7550f21007dd4348730007f3314811004fbe4088540006fe7558b41006df7358910004fe73d9520004ff7650f21006fe63949100e7f65248510006fe6598910005fd710c951006bf64d05210467c6559521007dd75cc931137bd42d0721005f673885100063d6550c43006fd640ca51007ec20d8931006fc6018931006fe1058432006ff32d8141055ff70c8530056ff30d852006dff704c540007bd5450a31005ff724c550006ff51587200177c5494d20216fc525834217efc6254d100577c50c8550006ff74583211bdfd76907200477f54d9521095ff700c9100977e500c950007f5435451013ff72159521056ff40d8520005fe7390520006df7498c21006ff5158321005ff764c520005f97094d1012eff620c9410057d7598d20004fe73d9121004fd72d9731006f561cc730006fd70d8953005fd7694730004fd7098e52007ec648c921007f732cc510007df638c520057fa20c8510005fc73549420067d6590c310067d7598d20097fa100cb40007ed62c8730006ff6248510004fe76945200e77e7518910004ff7058e54175fd72d0f21006fd65d8d210267c53597300b7bc40cc9400df7d7518520004fc73595101a6ff640c720005fe7398910007ed420c720005ff75587320e5fe7295110006fd65cca411fefc4298d200e7df320c910005fd7090931007e632485101fefe3298d20006fe7498f210b5fd70ccb30006fc6350521004fd7198d21006fc64989100b6fc6058332006fe7458720006fd6488520007ee420c520217ee32c8540096ff1018d20006fc6350d200877e65553310a6fc60d813209f7f510c950007f652505100b5fd70ccb40007de43c8530005bf71553420267c53d815314fec21d81210df7e7518520006fc7358642006ff5458b3019efd6290b10007ef639092010ff7214c5212ef7c5218d52007ed3248550006ff515804312fbf420c941007fb424c110005ff7150920096fe600c831005ff7650520006fe53d8540005ef7258d10006fc5458432007f642cc71007fbe40cc740005de73d07310b6ff2098d20007f762545102defe42d8152006ff5258342006ff64989100e7f66248510006ff62505101ff7c5254b3019efc52d81210057f7558520006fc6310910006ff6558732007ed32c8740005fd76c8730006fd6458b30006fe64989100a6fd1058b30006fc73582211c6fd760ca51006fc5258331005ed72d05200be7c65cc931006fd65cc94003fdc3048730005fd718c950005ff7055232166fc6250d10006fe4358021006fc7458910007bc6450b301f5fc7250530005ff7550b32007f772cc5101fdfe72947300a6fc604c941005dd7394b30005de73c8530006fe53d85420b5fe70597320b6fe4098d20004fc735
  | 3 => 0xe730c941005fd72cc7402c7cc304c832096fe600c951007df630c9100177c65945200477c53d952103efa10d8121007df6358d20096fe600cb41006fc6558520007be4099332005fe73953201b6fc6310720007f542cc51007fee20cc720004fe76087300e5fc7259510005ff764c5211877d5294c32005ff7054b32006fe7498d100b6fa2058332005f970909101fdfe72d8730006ff745802105f7f54c8550007f4639451003dfe7019121007f15148110005ff7154940006fa7358241005fd7190f200467f52d952107efe5058331006fd7558332007ec6248510004fc764c910006fd7058642007fa744811012fdd320c9410ddfc738852007ff430cc510006fd640c520004ff71593321dfec515092003efe50d8121097dc300c93014fbd41107200b6fe10d8930056fe505832104ffa10985200077e7598d2007efc40583310deff6188520177fb20d0d2028ff420cc53103efc40d8121004fc7648730096fe600c841007f5629451007dfc7090b310b5fa70187320b7f610cc910006fd64d8d2004ff730885100063d6550f4116efe6290f30006fd70d8954007f9544c110057fa5098910007f73254510006ff62545300b7de10cc930007fb7548110135fd76d0720006fc6018d21006fd65d9110007df3254530005fd7018d21004fd72d8d41005fc73551211bffb2090520094fe76cc9301a6fc4218d21006ff51583420e5fc724c510006ff6558d210defc51d8520007bd54d0f2116fbe6490f21004fd72d8d10006fd62d0730005fd711912003ff25048510006fd76cc950006fc6458520005ed7295320006fe63505210b6fd40d89300b7fa70cc9100a6fe604c941057f84098910006ff51d812114dff728c7200b7dd40cc93003ff73048710006fc65989100277f5154b30037f820185200157e750c520215fc7254d4011dff76cc720007f5654851003efc4058720006fc5358b30006fd6598d10006ed7458831006ff62885401befe32d9121056fa10583211877f5294f200a7df204c93000f7f54d9510006ff6458332007de4354b30007ee544c921005fd7110f32006fd7198f2103efe5058720056fc40583210077d548c9500e6ff6210910004fd70d8943006de4098c21006fd70584320a6ff5058b30007df6398d20096fd3018d20067fa200c72003dfc7054921007dc634c510005f57110d100a7fa204c910007f56550510005fd710c940005fd70cca2103dfe7090d21005fd72d0730007f7314c720005f5710ca41006fd51d813103ff04048510004ff7650e52004ff7650a51006ed6218b30005ff745873218fbd645503209f7f5195032005fd70d0f320a6ff2058d20006fd2118d2116efc6290d500057d7599121004ff7258f41037f41018910055fe7050721006fd43d81520dff97088520004fd7118d52004fd71d9120
  | 4 => 0xc520005ff704c95122ff72148550186fe6294f30007ef635092012dfe7294d41007f86448110007bc6450b31006fc7258031006ff7558732007ef658c921006ff75d8542006fe43d81520a5fe70509320e7f462885100a6fe1058b300057f754c7200defe4158321007bf645912122dfc73c85500e5fc7258d10006fe7558732005fd7090a5107efe20d8530007ef62c8510067f7300c510007f76294510006fd7118d52006ff65d9110006ff43587200deff610c5201fdfe7290730007fb644811014efd61907200a5ff704c940005ff7054942006ff75d8930005fd7690910005fd7118d4218fbd6455321006de6390c21055fe72085400b5ff764c920055ff7648510066fe4018d100177f5454920006fd6254730006fd53d8141006fd32d8121006ff64087300a7dd304c920006fd64485200b7df20ccb3013dff7654720006ff63d85200be7e65d9732006ff6598d10247ee504c921165ff7650c320a6fe10d813213f7e750c95101e7c5359720006fd7498d10006fe4058a31007bd64d0910006fd74d81211aefe628c730006fd74580310a6fd4058b3007efe60cc5210aefc608c951007fa6448110007f76548510007fb7048510006ff62d8131077ec208c72003efe4058910007bd424c9400e7be741891016fbd6490f21216ff2158342055fe70d0721005fd70cc831247ec404c921006ff6318910006fd6418730007f54254510006fc6098d21005fb70549200a7dd504cb30007fa6348110006fd6418d10006fd7198d100077e325525111efc4298d21006dd32d813100f7c53d9510007df42ccb300177f525512015ff72110d210b6fe4098f20005fd7210d200173f5495120006f56118732006fa7358031006fe5058632005fe73d051014dfe7110f20007ed428852001f7f5454f20007bc6450921006ed7058831006fd62cc7300be7f5259732004fd769073007ff470cc510005fd7290f10287f6204c431075fe710c5200057d750c520006fd6418b300ce7f50d8954005fd7599332006ef62cc91005d7e7510f21006fb3258241005bd74d833218efe6255330006fd6458d100b7fa10cc92004ff220885100177c65951200057d7598b30006fd7058a51006fc5358442067be400c540006fe6350a21007d5310c730036fa4058021006fd64589100057d7518910006de63cca4119eff21d8121007f76550510007dc7358910006fc5458b3007cff764c510005fd71ccb30006ff5058442217bd42c8540006fd62107301b7df320c841005bd7010d42005fd7199120157fb70d8910077fa208c720004fe76d0d21006fc6058732007dc63cc9200fffb52d011003df572885100067f7558910006fe638c5200057d7295151006ed62c87300b7de40ccb301b5fd76107200e7dd7318910007bd42cc941006fd76cc841006ff5258740005f
  | 5 => 0x6bc635094107eff62cc520006fe4018d21006fd64cc72119ff771d8121005ff7050d2105f7c53c8550005fe76d0d1022fee32c8550227fb20d91200eff8654811011dfe7295331005ff7155132007ed42485201e7ec659092022efc3259520005fd7418b31005fd74d952110dff724c72118fdd32550321f6fc4258332005fd72d052108e7f53d8554005be74d8b30185fd7694f21006fd76cc941006fe43589100adff764cb300fff852d011022eff62c8550006dd630cb41096fd1018d200ddfe71d8d20006ff43583210b5fc7058732007bd74ccb410effa6548110006fd52d85420b5fc7050f32005f57110f310077d6554b32006fc7558732005fd7418d2103efe60d8121007fb7058d20006fc525874003ff74048510005f57194910096fd7018d200177c5354920007dd54ccb3003ff73048510006fd435865214eff6110720004fd70d8941004fd7648730187de32d9732006ff6148520004ff7258e41005fd70d0521006ff624c950006fd73d8520007ef7258121005ff735852006fee204c720185fd7294f20007be645533229fdc60cc9310a5fd704c9200e6fd628c91003efe6348730005fb724c110217be740c940005fd70cc92107eff4098d100177f5294d20006fd62cca41006fa4358021067f2200c51015fbd6410f20007db324c110006ff75d8910004fd71d8943007f57348510007bf4248540004f77159132006fd7558720057fa10d8520006ff74587321c5fd7294720095fe7010c32006fd64d891000f7b5254110006fc6394941096fe3018d20006de4058c2106dfc7090931006fd7218d54006fd6408730006fd655873005f7c539532114efe41d812114dff768c720006fd624c73003eff2058910006ff43d8121005dc7354730006fc43584320167f52d9520165ff7250f2014dfe71d0f20217f5210854010efc764c720197f72195121117f475cc5100b5fe70d0f32005ed720c730006fe6358d20175fd76d0c32066ff2018d10006fe50d893100d7e751091006fde3058730005f7714c921006fd5498d20137df320cb41006dd6318d101adfd728c7201b6fd760c8410dfbd411052001f7c5354f20005fd76cc520007f64294510006fc63549400ddff760c52006eff2058d10006ff6150520005fd7118d20005ff7158d20006fc63d0910136fc63d072013f7d528c95113f7f520c9511aff721d8d210e5fe7219110007df32cc51003fbe4048540006ff7650b31005fe7394720005fd71d0b30166fc3259332007ed420c5200057d75907200adfd708cb30006de63cc721005fd70cc9410b6fc60cc9211fdfe72d0730006fe6558b30004fd7690a51007f763545100be7c6559732077f610d8d101feff6298b30005ff76551101ffdf328cb30065fd700c540005f57290510006fe20d8532005fb704c5100dff9708
  | 6 => 0xf5258b300e7f462485100b6fd50d89301a6ff2018d210e77d75189100077e544c951007f970cc91019ff421d8121006fe4098d211effb2018d200b6fc2098d20007f25148110004fd7218d40007f764cc510036ff60189100defe315891009f5f5394c320ddfe7110d20006fe638c720007d671ccb31007f73294510006fe7558843007f664cc510006fe7198d200a7de504cb30007bd54d09100e6ff628c91003efc6058121136fe62d0510006ff65d8d200b7dd50cc930005ed7290f21004ff7158032057fa209891007efe2058331005fc735952010efe769093111fdd32cc720005bf7458520006fe745873009f7c530c950005f9700c95006dfd7198d10006fd650c9100177f5454d20007dc6390d21006de634c7210dffb1058910005ed72d0f20006fe73d85420a7dc204c93004efe40d8910006ff645873211fde7390b3107ff770cc510007dd4398b30006fd62ccb40006fd7198e4221fbd740cb40005fe73d8910005fe739512000f7f525951017dff7254f21004fe76cc91011dfe7219331004ff71588430077d325455013efc6354720187ee4294f20004fe76c8730006fd76cc940075fd708c540005fd7190d20006ff658c9400bdff7654b32007f8625411011efe52d8532006fc63d0921007df328c730007f46250510005fd71cc94103dfe70d8d21007f972cc130035f67688510006fd76cc910247ee604c921076fe628c720006fd74d8930006fd654c921006ff620c540176ff20d8d4203ff4704871007fee20cc5200bf7f5055332006fe5458432095ff700c940006ff64cc5200effb5348110005ff765533222ffb20595200ddfc715092009e7e650ca41005fd7294d2013fdf320c9512b7de404cb31006fd5418d1003ff22048510005fd710c950007f77150921006fc6310520006ff648c9510bd7e7519332005fd71ccb40005fd74d8b31005bf7250f41217bf42c8540004fe73d8520037be400854006dff704c550136fd760cb41005fd719933004eff20d8910096fa600c8310057d7510f3003dfc70cc52114f7d750c720005ef724c521006fd5498f200e77f52949101d6fc42d8520006fe6018732065fe7090831217df320c94011efd6210b31007f071481101afee428c720007be43d09100079d43d073006efe604c5210adfe7055232005fd73d9520006fd62d0910006fe7058831005ed7295120096fa5058032006fd52d8540007be5450f21006fd64d8d21007f4620c51024fef544c921197ee3295321005ff744c52116fde32d9332006fc32582410afdc308cb30007df324c5100063d6550b4114dfe7194f20006ff62d0910006fe7358841006fe7558b3025fec658c921006fd74d8520004fd7610910007dd43d8b3014f7e750c720006fd5458910007f77150a2100f5f5394d10005fd70953211ffdd73c8730
  | 7 => 0x45200067f65d8131004ff7058831007cd3248730004ef764c832004ff7058b31006ff6458121005f673905100df7d750c520004fd760c720005ff7150b32006ff74582310a5ff704c9500277c5155330006fd54d8910007f66354510005fd73d91200e7f83248110005fd728c520005fd73107200ddfe71d0d2003dfe7095121217bd4208540005ff7250d200079e6490f300e6fc3258221066fd2018d10006fd6294730006fd5418d21096ff6018930197bd429532121efc32d8142007f66454510007dd544cb310b6fe60d8332006fc64d852003ef860581210a6fc2058d20247ee204c921004fc76485300a7df704cb30117f665cc510216fe76c8540005be7418730005fb7055320007bc7458910007f56290510007f77150831006fd7258730004fd76cca4121efd620cb40196fc63953210267c525973018fbe64553210177c5354d20006fe7158032005fd7190b30096fc1058032006fe64d833207ff61098d10005fe739452010fdf320c931005ff7050f21006bf6499110004fd7198f2012fdf328c94111fdd63cc72011dff72cc7200057d759052006efd2058d10055fc704c721005de739912106eff624c5200b6ff64cc94004eff609852010efc4258732077dc308c730006fc63d0520004fd71d8132006ed62ccb41007f9624c110006fc6418910005fd7694d201ffde62ccb3003efd20589100be7e65ccb41006fe7418d20056ff5058321006f77158910037ef20189100477f52d95210477e65d9521006ff640c95018fbf4255032007df73581210b7ec2098d2007dfe7010f31006fe63d0921075fe70cca31197bd6495320005fd708c941007bf64d0521005fd7318520007f464cc510006fd75d8131007f76188520006fd7158332006fd644c721226fc32d91201ffdd32c8730005fd76487300467e65d952106efc5058730005fe7619121006dc6390d21006bd6419330007de4394930006fd64cc910005fe7398520007b464505100477c65595210057d75d8d20007df32d0731005fe73c851011efe62cc510006fd4258221006fc4358b300277c6554b30004fc76551310057f754c520005fe73191210ccff72595420ddfe7198d2011fdd7390b31006ff6418910005ff7250d21004fd7688730005fc735532010efc634c7200b7df30cc920006fe635852015fbd4210f21005ed7210c32005fd71cc921005ff7350720066fd7118d10006fd7458232004dc7358910005fd7094f21007ad42d0720006fe6418910005fd74ccb31006fe5358910005fe73d9121006fd644c921006fe43d8910005fc7350b10006fe52d85300057d7508730005fd7295330007be645533104dfc7050a2112fbe645072014fee21d81210df7e750c520137f721d0521005fd7290d10007f5514c521005de7390b30077ec208c520006fe6318910006f
  | 8 => 0x7ee644c9210047e7619543037f84018910006ff74d8520006fe7418d21006fc6518910096fe1018d20004fd76d0d10006fe60d8d2116eff2198f42004fd7198e52006fd7498e522fefc32d915209f7f500c951007ee428c52005d7c7550f21006fd62cc740005ff725533010fde7390931005ff725055006efa10d8131007ed428c720006fe64d8121005ff725473010eff621893104efd20d8910006ff5158432006fe7498f201fefc5258b30007fb624c1100079e5450f30006dc7058c21096fd4018d20006fc73d8542067f7100c720006fd5498d21006fd64ccb10006dc6350d21006fd64d8d10095fd700cb30006ff6448510005fc76cc520056fe40d852008e7f50d8554007ef62989101aeff648c72000d7c754c510037fa50189101fefe4298d20007df630c951006fe4058b31005fe73949410a7fa3058b3006efe50d8131007be64507300b5fe7099332004fd7118d54007f541485100067e5418d510afdc3098b30005fd7010d21216fe3259120007df32cc54018dff76550320ddfe7194d20006ff62485400057d75d07300a6fd5058b30006fd7558642006fe5058432007bf64d0d20005fd7099332006fc7458332215fc724c540004bf7650c43097f6100cb100b5fc7059332007f932d0110006fe6348510004ff72593300ddfe71d9520005fe76d0d21007f9524c110007bf64d0b31006fc6350550006fe6350510215fe720c5400effb544811003ffa10d8121007f43254710157fb10d89100177f53d9520005fc7654d20004fe76d0910006fd53d85400257e758cb30005fd71d97320057c7354550006fc63485500047d7518d41095fd700cb402bfde10ccb31006fd745873213efe625451022f7f52c8550006ff71d89300077f7558121007e76248510057be40c8740004fc7358321004fc7359741006fe5458b300a7ec2058d20007df3254731065fc7050831006fc65d8520006fe4098c210b6f86058332006fc4058432006fd7418d10006fd7558730005fc7354910117f465cc510006ff7158332006ff5458730006ff650c941006fe20d89310067d6590831004ff7654e420857e7510b31007f76454510036fc305802119eff71d8121006fc70587320077c755891022f7d528c9501f7de735833219efd620cb10007f4645451003dfc7054d21277ee404cb210067c72597410b6fe60cca21055ff70c8540006fc7648730006fe7648550006de63cca51006fc32587300dff84148110006dd63cc91022f7e750c950007bf5419120005fd7198b30156fe31d8910004fd71d893003fde304873006efc7358730006ff650c910006fd6358520006fd6458730006ff645873006fee204c52004efd71d89100a7dd624cb30006ff644c520006fd6458d21007f54294510006fd53d8542006fe6518910007f46390510005fd729
  | 9 => 0xf3254531007bd64191210afbe408c94004ff7108852011efc62cc54009e7c650c9310a7de204cb30005fe76cc520006ff6418520006fd7098d2106efc2058d100067d65cc8311c7df320ca51005f970ccb30005ff7154f20005bf71551431fdfc7254730007bd5450b32005fd72951211d6fe32d852003ff64048710007fb3148110004fd7098e42095ff700c950007ed544cb210057d7510b30006fe63d0721004fd71d93300eff85348110005fd7190d52005ed721072022fdf320c950006fe4358332007dd4354b30004ff7258c41005ff7350520006fd650ca41006dc63cc921006fe6398520005fe761091000f7c52d951007ff450cc510005ff7050b31005fc7350910005fc735512010fdd324c720005fd7195330037ee2018520056ff6198910006fe735802103efc2058910005ff704c721004fc7654931005ff7054d2103ffa30589101f6ff62c8530135fd72d07200267f51d8153177f721d0d21005ff7454f21006ff7158b41076ff20d8d100077e2019531006fc634c520097dd3018d20006fc72d8131196fc32d9542005fc7650d20006fd650c940006ff6418d21004fd72d95100e5fe7218d1014dfc7154f20007ad42d052003ff72048710005fd7695330004ff7058a31166fc6250d50006ff7458232006ff64cc550005fd7494d2100575750c51000f7c65551100177e6554520004fd7298d10006fe6350d20005df7350b320b6fa10d8930035fe7298910216ff628c9401f6fe3258332006fe7058432006fe53d8910007fb414811004ff771d89100057d7510d2104ff640885100b7da10cc930007ee5350b20006fb7458021006bf7458910007f76148520007ed525092103efe20d8121006ff6488730007ed42cca21007ed648c9211ff7e7598b30005fd76d0d2016efe6290e51056ff20d85200bf3f549533210fdd634c72003dfc7050921005fd7688730005bf7250c43005fc73485200057f72551500befd5498c320b7de50cc93003ff47048510007de43987300be7e65cc831004fc73587200057f725455019efe52d81211fdfc725533021fbd420cb40007f56488510005ed72d0d200b6fe50d8930005ff7054d41095fc7055032006ff425833218dfe72d8d54075f6760c510006fc5358730005ff7158332005fc7650d10006ff7358910036ff6218520006fc5158032007f84254110007ee63909200057d75d8332006fe525833107efd4098f1004dfe7050a21006fd62d0b3113efd760c9510e7f4424851011f7f5294b31004fd7018d51004ff7259110006fe631091006eff50587302a7f620cc631006de7318d21006fc635452010efe624c5101afbe4250a310be7f54d89530b7df62cc930004fd72d9330007df63cc920007be4350b32006fd7058732007bd7498d20006ff32d8540007f76290510007fa424c110
  | 10 => 0x8910005ed7218730006ff644c550007f7649451004ffa30d8910006ff42d8520005fd7090d51006bf64d092003efd4058b10006ff75d8132007dc7354b32006ff628c540005fd700c941006fc73d8910004fd760c910006fd65ccb410073e5450d511fefd62c8730005fd7194930005fd7290d51117f754cc51017efe6254f30006f97458031007dd324c520007f643885100057f7550f3025fef548c921005fd70cca31005ed7210520006f87258031004fd7610d10007f95148110006fe7558032005fd7110c32006fd74d893115efe6210d10006ff72580310077d75d8d20067f6400c510006fc7058432057dc30c8530007bd64953320b7fa1058332007f96454110007f66394510005ff7159520005ff705095104ffa7088520006dd63cc84121efd760cb4013efc6254531006fe655873000f7c6594d1007ff540cc710007bd42d0730006fd615473004ff7208851014efe760c720007dd52ccb30004ff7259130065fe7050831005f77150f21007ee53909200057d75d052110fec2018931006f76198520006fe20d8d21006fd74580321befd760ca41006fd5458b31006fe6354920056fc1058321006fc6458332006ff6498d211ffdc624cb3022dfc724c550007f5640c5100bcff7654c32257ec508c921007f4715092104dfd7088540077be408c540005fd72d8d54006fd6498d20004fd760873006efd4058730004fd769083122efe760c95003dfc704c521006dc634c9200ce7f52597421aefc2058a31005fd7099121005ff7359520005f77150b31006ff4258732007f432cc5100b7dc30d8930006ff5158b30006fa7258031006fd54d85200a6fe5058b300bf7f5454b32185fd7294e4203cff70589101dfec6550920005ff7354720005fd7018b31006fc6358910004ff7650d211c6fc6394720005fd70d0c32006fe32d8550006fc6158332005ff7454b31007f643487100a6fe50d8132005ff73509200b4fe760c9300277e6554730166fe6250f30004fe76105200057d758c910006fe20588310eff85448110006fe43d8550004ff7058e5103fec2058520197df329503212efc62505300b7de70ccb30006ff7058b43007dd32cc5200157e75d8d200a6fc4058b3004dff7648520196fc6395320004ff7650910005ff7259330006fd648873019dfe7290f100277c5454730005fd7310520006fe7258730055fc7090f21006fd635891022dfc7250550004ff7655121007de74ccb30006fe4058732006fe43d8520005fe7348520097bc400c940004ff7158a43006fd5458332006fd648c520037ed201891011dfd72cc720005fd74d8331066fc2018d100bf7f52553321f7df32c8530005fc7650520006fc5458730007ed6390920005fd7194d4003ff870485200067f625455000f7f535511029fde10cc9310be7c53d8953007d
  | 11 => 0x7f77159121006ff74d8131004fc7655120005fd72d8730006ff5258b40007dd43ccb3016fbe6490f20005fd72107301c6fd6290a51007de54ccb3103dff7048740005ed720c7201afdc3298732007f93148110207fb20d8d20055fe76185200ddfe71d0920004fc7358841007f77158121006ff7458831007fa3254110037fa201891007dfd70cc740006fd63d8121005fd72cc520196fe62951100177c54d9520004fe73d81211a6fc2018d2107dfe7094b31006ee4058831005f5710c831007ee63509200177c655952006efe20d8131006fd7158232005ff745493125fef508c921005f97010f300e7bd4210910006fe6390a51005ff7050931006fc6390910005f972d0110005fc7654910006ff6448730007f741cc510006fe74587321aefd6290a31005fd70d973113efc6254540005f47348710006fd61d0730006fd6458d20005bf71551420057f7558d10004ff7655320005fd7610520004ff7058d210277f5494730007f9424c110005dc7358121006fd7358720006fc6358121006fc63d8910005de73d0b30007df32cc55014efd760c7201fdff76c873012fbd420c941005dd7310b30004fd71d9332236fe32d9520175fd76d0f21006fe53d852003eff405872007ff750cc51012dfe728c94103eff3058720005fd7210f32006ff7458a51005ff705912112eff2058742007ed428c520005fd71d9330006fe1098f21004fd7610b300a6ff7058b30007f121d0110006fc6498b30005ff7250d52004fe76d0d200057f7254d510a6fd624cb3003efa60d8121006fe7458321004fd7018d52007f564485100e6fd6290910007df62cc931137f72199121004fc7654d21006fd63d8910006fd6498d10006f57198d21067f7200c510006ff7258910055fd70c873010efc624c540007fb4254110005fd700c831006fe53d89400e5fc7250d10006fc63549100077d54cc9500bf7c5354b32004fc7359110007f43254510055fd70c8740006fe73d8954006fe6558332006fc6318520006dc3018d21004ff76cca4103efc1058720006fe63509200bf7f5054b32005fe760c910067f7100c520006ff64cc921216fd760c940007f241481101feff21d81320b6fd7098d2014dfc7155320006fe6354721006dc638c951006fd7018d52005fd72d0f30097f6100c910007ac4350b20004fc7655130006fe53583320067f6590931005ff7059332006ff745803103dfc704c921006fc5358b400deff618c520005fd72d933003eff7058b10006fd7648730006f8325803106efe10587300157e75185201ffde42ccb30006bd64d0b32006fc7158b300aefe405823204efc20d891007dfc7055331006ff7058b4103efc10d8121007f73290510006fd6254910006fd64cc720005fd7250521007bd42cc7400053d7510d42004ff7655330057f8109
  | 12 => 0xd7519331007dd524cb310477f5059521005df73589100057d7510f20004ff7259510007de4348530006fe655873207ff540cc510006fc75583320277f525473003ff64048510005fd76d0520005fd7294d42006fe7358b41006fd61d8332095fe70d0c32005f97090d10006bd6419332004ff7058f42005f67394510007bd4288540006ff5258730006fd6558d21004fd70d8d420e5fe7290d10004fd70d8953005ff7154d20006ff648c91001f7f53547200e5fe72d8d10055ff70c8550004fc7654930006fc62d8131006fe5358732007bf4350720075ff708c720006ed624873000575759051025fec548c921007fa62d01100073e5450951007fa52d011014efe21d812114efc51d8121004fd76107300e6ff6290910005fb7050910005ff765533004ff52088510006fc63549210a77e504c950005ff7690d2112ffb2050520005f67348710006fd5458232006f56118730004ff7258d2106dfc7055131007f77448710006fd75580320b6fe76cc92006dfc70cc93107eff2098d10007f551d0510117f454cc510007bc4059332005ff7150930006fd644c720007f5414c521006ff7558642004fe760c5200defe61585200e7f63248510004fd76d0d21007ed62189100057d7518520006ff755872018fdf3255232006fe63d8520005f5710c94108e7f52d855411efc62cc510005ff7255121006fd63d8520007bc7350b410d67c5118d540b6fc60cc951005fe731911017fee4254f20096fd5018d20006ff4358b3011efc2098d21004ff7654d10005ff7258d10006bf64d05100177f5154920004fe7610d20006ff7058432006de7318d10006fc764853003dfe705092100e7f545825116dff7690f21005fd740cb310b6fe20d8930006fe6350f20005fe769512111fdc204cb3118fbe6455320006fd6448730005ee720c730007fa4354110076fd20d8d100e6fe760c910004fc73589101ffde524cb300b7de20cc93003ff86058121006fd4358910006ff3258041006ff7458a310e7bf42909100ddfc7154d200057d75187320aefe6398b30005fe73d9520006fc53584430077d5454932005dd739912103ff72048510117f453cc51001f7f5154f200257e7510f30006ff5058443005dd73c8730006fd5458732006ff7648540006fc6458732005fd7094941004fd768c720006ff6598b300a6fe604c921006ff624c941004fd76d0910007f6430c510005fd76087300defc5158321006fc6394520005fd7319120007ae5450b2022f7e75c8550005bf7458d1007efe4098d1003ff52048710005f7704c431004ff7655120005fd72d0520005fe7690d21006dd32587301a7fb200c52003dff7048730006f832582412d7ee70cca32007f74248510006ef620c910006fd6290730005fc73549400b5fd70cc92007fbc40cc540006fe63d0910
  | 13 => 0xcb3100d7e75d05100067c65d8931006ff644c920007b942d011010efc624c510007df7358520004fc7359120004fd7018d54007ed62487300effb5248110067f5200c510006de76cc930007bd420c540006fd7458b10004fe768c910006fc6558b30006fd76ccb10006ff75d894304eff70d8910007df6550f30176fc63d0f20007bf74581210057f7558910076fe20582311c6fc62945402bfdc40ccb311bfdf320ca410067f65cc9310ddfc7155120005fd71d9120004fc765513221efc5258b400067f65509310067f6518943006ff76487400ddfc760c5201ffde73c8730005f77154921007dd42ccb300b7dd70ccb30006fd41583210afdd30d8d200b6fc2058332007dd3258730006fe6498d2007ffa10cc520006fd7018d210077e75d8d201ffde32d8332006fd62187300b7de30d8b30006fc535804214efc5158720007dc630c951004fe76d0520195fd7295320007be6450b32006fd73d85420b6fa60d8332006fe635492103dfe7050521005dc7354932006fd62cca511fff72188730007de6318d21006fd43d8910006fc75589100a7fa20d813206edf3058f100057f7550d21005fd76d0b32067f41018d10006fe43d8151007bd42d05210a6fe604c951006fd645852004efe76885200057d75d0720006ff6598d20005f97010520007bd42507310a6fe2058b30007ac435092014efd610c72003f7c5048550004ff7654d21006fd7458831006fc32d8141005ff724c730066fe205803114efe768c720007dd74cc930006ff745803206efe2058f10005f57294510004fe76909100a6fe20d8132005fe7610d100257e75087300bcff725953213efc6254510006fe76cc921006fd5358910036ff6118910075fc700ca3103ffa2048510005ff7054b310defc3158321007be6455330007f8434811003ff41058910005ff7155330005ff7354520006fd640c730006ff6298730136fc62d0510006fe655852011fde424cb31006fd65cc941007f55448510007fb7058910095fc7050c3210fdc204c93122efd760c950006fe76cc940006fd5498d10005fd71cc920005fe73991210e5fe72d9110097f82018d200dff871481101fefd6218b30005fe7694520007ee32d81210077d52cc951007f965d0110005fd72d0d2119ff5710cb10006ff65d91210067d65cca41007ee5350920006fd62cc9100077e53cc950005fd7610b300077d7598d20005ff7655121007f63250510006fe60d873214efc21d8121007ee3248540006dc3098c21005f9700c54013f7e6554720006fe32d8151005fd76cc910005df7250d301a6fe4218d21007f551cc51007ff610cc510005fd7118b30006fe64d8732004fe7694b3106dfe7094931007f64348510066dd3018d10007ed6350920007ed3248740005fe73c8540006fc64581211befd620ca410057
  | 14 => 0x457e7510d2106efd505873012efe3259121007ed5390920006bd641912109e7e650cb41005ff7054931007fa644c110006ff74d893003dff7058121075ff708c520007f66390510006fe5498f21004ff7058a51006fd640c910004fe73d9110005fd739912000f7c5494d10005ff76549100e7f85248110006ff7158232005ff7650d210b6dd3098f20226ff21d9120177df32d0c320d6bd7418d54006fd7058831004fc7358021007ee4298520007bd4248540007df32d813107efd2098d10005fc735472011fbf4290b31005ff745833204ff420885101c6fe32d9521006fc3058a31004fc765091003ff52048510007ae545092000e7c5358251096fe4058032007f43294510075fc7050a31006fc6418d21006fe6358121006fc5258730006df7098c211f7de52cc9300877c6554b311f6ff6294930007bc4350b30006fe629873006ff6104c510007f5514c510056f710d85201fefd620873025fee658c921005fe73c85500b6ef20d893010dfe72d8131057ec20d8520096fe5018d20007ed4258520055fe7010f21006ff635891003dfc70d9121006ec20d8931005fe73185200b7dc20ccb3003ff5704871004ff410d891007efc60cc5210077f7558520004fe769493111fbd4210b31007fb65d0110005fd7694d10006ff65cc940006fe5418d20004fe76cc931007d532cc5100afde3098b30006fd7218d1014dfc7150f20007dc63cc921005ff7150910006fc6350910005be740c730006ff62cc910006ff7458b3003ff42048710005ed720c520096fc4018d2011fdf32cc7210b5ff70ccb100177f5154d20004fe760c931007fa5448110004fe7610b31007f6534851014eff6194720005f9700cb3004fec2098520006ff7158910005f473485100a6df3058f20007de76cc931005fd76107300a6df604c930006fe52d8131006ff6558d20006fd6250a31076fc20d8d10004fe73d95101befc6390720007bc40d9121006fc764c520006fd53d891003efc305891001f7c5155320005fe7388540006fe5458730007ef725852011efc2058b310affa508c910005fd7290e510067e53d895300f7e6554910005fd7290d50006fe6350a51006fd7258332007bd54d0d2105e7f50d8552005fc7350720007ed658c921007f1514c11000d7e7599110005fd7010b31007f571cca21005fd7090e5111efe4298d210aff8408c910006ff64cc951006ff764c7200b5fe7055332166ff2159332006be7498d20006ff6254910006fd64987320b6fd7098f20006fe63c8740006fd6150720056fc20d8520006fd6250910005fd71d0920006fc7458432007ee4258520036f83058021004ff7259541004f7764c431035fc7090c21005fd7298730007f653505100057d758c940005be7498d20006bf64991210a7ee204c9200dffa51481102bfde50c
  | 15 => 0x72158d21006ff5158730006ff52584431fefe52d8132004fd76d0f2000f3f5495110005bc7458d1021efd62c874011eff20d8532006ff6250531075fe7090a31006ff6248550006ff63d89100e7f5710c910007dd424cb31005bd7498b30005fd7195320004fc7358b41007f5310c720006dc630c91015efc6210d10037f81018910007df324c5500f7fa654c11018efc62551300b5de730c930007f57198d21006fe6418b300affa108c950006fe7498d2100e7c6559510005bd748c910006ff7458332007df3298730004fd7198d201d6fe42d85200877f5055331007ed7290f2111efd6290b31007be5450b30005fd7694910007ed5250920006fc7558432006fc6350921006fe7258231006fd6250a51005ff7050d52006df5318d210477c539512107efe40d8530007ec62cc9100aefd6098b301fff721487300457c7558121004fe7648530004fc7654d10007f443cc510006fc325823110eff6294931006fe74d8910004fe7690931004fc7650931006ee43588311d7fb70d852014eff6190720007dc7350b3204efc30d8910006fc6498d21006fa735802106ffa104c520006fd64cc831007dd71ccb3029fde50cc93106eff7058730006fc634c920004fd7610d21007df75cc930176fe62d0d10005fb7050f2003efc60d8121007bd4250531007bd43d0720007ed70cca3201f7c5194f20005ff764c9100047f755912014fed720c720005fd741873219efc42d812107efc60cc721136fc32d8542117f752cc510006fd6254b3121dfc73c87401f6fe42583320477c534855018dff7255320006fe5358642006fd52d8520006fd64cca5113dff7254720007f8644c110006fc4258331007f46388510006ff625091010efc2058732006fd41d8121215fe72cc540057fa70c85101fdfe72d0f30007ef62485100177f5354520005f67348510006ff6250550006fe40d8532005ff7050a511e7ee659092006cff7058d10004ff715933003dfe70d0521005bc745812120ffb2019120007dc3018d21006ff65581211ff7d7598b30006fe6458b30007bf4350520006de63cc910006dc3058c21007dc6350d21005fd72d93310057d7510d2013dfc7250d51007bd54d0b3103efa20d8121007f774485100067d6590c21005ff7150d50004fc73593210067d6550831005dc7350932004ff725974103dfd72885400267c6559730006ed620cb41005ff7154932006ff5158b40004ff7259740007fb644c110006fe62d8730004ff76cc9101eeff2118d20005fd70d0921004ff7058843007ed5350b200a6ef2058b300b6fd3098d20096ff640c940007f562885100177f52d9520006fd5258332005dd73d0b30007bf641091003ff07048510005fd768c910006fd654c920007df324c540006fc43587300b6fe6058332004fd7218d51005fe73d0721
  | 16 => 0x110007bf7150b41006ff644c9500b7be40cc94007efc2098d1003ff42048510007f562505100deff619852000f7f5454910006fd5258732067df3018d10007dd6550f300e7fb2148110005fc7350950004fc7359540247ec604c921175fd72d0f20006fe5098f21007f5635051013dfe7290d51006fe43582520857e75d07310257c7550f300b6fe60cca41006ff6518d21006fe75d8121005fd700ca31007ee548c92117efc6254d4103ffa60d812121eff21d8142006fd61c8730006fd64cc510005fd710cb30067f8200c520006df6398d10006fd70d8943006fd43d8550005fd7299110005fd710cb40004fe7610d21005fc7350a510ddfc7150d20006fe7358a41007f654cc510007f96354110006fd7458321006fd7558432067f4630c5100b7df30ccb10006fd43d852012eff6294941006fd76cca51005fc7350520006fb7258031075fe7050a31004ff764873001f7c54547200e5fe72d051000f7f5255110004fd72d8d50007f472cc5100aff820d8d20005ff7558332004ff7258031004ff76cca5118fbf4255321006ff615833218dfd7255032006fe2058e21005fd76d0d21007f9625411000e7e65d9510006ec2058831007f44354510006ff715884309e7e650c831006ff64c855016fbd4290c32005ff73591200e7f64288510006fe6458520007ee32485500b5ef7258d20006fd73d8121004fc7655121006bd64d073006efe505873007ff550cc510006de3018d21006fd64cc920006f76198730006ff658c941007bc6310d42006fe4358032006fd7498d20006fc6558121005fd71949400b7f410cc910006fd658c941006fd7058841007f5620c510007f571cc921006bf6410d10004fe7690b3104ff7628851021fee32c874007dfe7010b310defe760c52007eff20d8530005fe73d8121007ee42d8520006fd640cb10005fd7210d10006fc6390520006ff75d8520006fd4358332005ff724c521006ff7458730005ff71593300073d5450d5214fdf310c7200f7f8654c110006ff6558520006fc63d0d20006ef62909310dff97098520005ff7058d21006fd654c9102b7de204cb31005fc7654d21007f473487100aefc608c941006fe605873206efc40587301fefd6294b3016fbf4290f21004fd70d8d4112ff6710c94110fdf324c7210477f544855014efc31d8121005fd729512006efc604c521006fc32d8540006fe64587321a5fd760c72003dfe7098d210b4ff7258d200b7da70ccb30067f4200c51021ff72148740006fe43d8951006fe42d85500effb51481100077d52cc950007de634c910005ed7210f21005fd70d073113eff628c951006ff6254940006fd7418d21006fc73d8520007dd43d87300067c735944219ff642487100057d75d0520004fe73d8951005fd720c730006fd6598b30007e8624811010ff
  | 17 => 0x7efe2098f10005bd740c730006fc635454016efe6290f10007fb6254110006fd65cc84102e7f525974003efe40d8121006fc7358b10006ff6418d10006dc63cc5101fdfe72d9330166fc2159332005ff7154b300b6fd3098f200167c5359520006fe6418d1000f7c535491007efe4058331005dc7358520007bd54d0f20005ff7254520007bf4390f2003efd30589101fdfc7259330096fe2018d20006ff6598d21004ff76cc841007ed42cc92007eff60cc520007f6420c51003ffa20d8121006fc5258443006fd7258031096df3018d20007f55250510005fd71d8b30006fc64589100b6ff30d8930005ff7454932006fd54d8530007bd6419110005ff7648730007ed5350920006fd65d9120007bd64d0730007f73248710005fd709083100f7f5294d10006fe65d85200b7df60cc930007f7620c510006ff32d8550167dc3259332006fd64d8520007bc4350921005f970cc9200a7f8704c920006fd53d8520007de43547300aefe608c94118f7f525503218ffb2055120006fc7650b31006ff654c941065fe700c831006ff6458910004ff7654d200a5ed7298d20006ff32583410067c65d8131007f463485100a6fc1058b30006ff7558332006de63cc720007dd3250730006ff6458d10006ff32d8520006ff654c910005ed7290d21005fd7094d210b7dc70cc930005fd7090f21005f77154d100067d650c831007be5450d2116dfd7290f21005ff70550320affa208c910006fe63589100067d5458a51005fc73581210b6ff1098f20006f97098d20007f9324811003efe4058720006fd5358332006fe7158b30006fd7258231005ff7150b3115dfd7210c32055f77158910006fe645891016ffb2090d20006fc7648540056fe40583210e5fe7299110007bb64d0110006ff62cc940007f56348510007ed4298520005fe7318542035fd7008540005ff7254d21004fd76ccb41006fd6258730005fe7694910226fc21d9120005ff705093206dff704c730137bd42d0720006ed7298d20007f73250710006fc4098f21005757194e510a4fd7298d20004fc7358b1003ff570485100057f7550f20005f97010910006fd53d894003dfe70d91210a7ef2058b3016efc6290d51006fc609873218dff72552320b6fd7098c32117f452cc5100b6fe3098d20006fe5358032007f67348710004fd70d8951006fe6350921005fc7350951077dc3098730005fc73545200a7de7358b300177c51551202bfde20ccb31004df7359521005f572cc510007f4635051010efe4258732005de73d0730005ff7254d410bf7f52cc9510bdfe730c951006fd5458032037fa101852008e7c525974106efc604c72103eff1058910005fe73d8520196fc6295110006ff7058a41005fd70951210a4ff7058d200b5ff70cc910006fd54d8532007f86354110007f862d
  | 18 => 0xe4394730007ed42d8520217bd428c940187fb2094d20005bf7458910006ef625093103ff4304871000f7f5454d10006fd5458321006fe4358321257ec408c92119efe32d8121007bf42cc940006fd73d891007dfe70d9331006fc6558910004fd7198e42006fd6498b30006fc60d8d2106ff84058d10006fd7498f2012dff7650720095de76cc930006fe72d813107efd20d85300873f5495331006ff5058843006fd7198c3205d7c754c7210dff46188520006fe43587201b6fe6210730006fe64d8910004ff7650f2009f3f54950321fffb2098d200a6ff4058b30006ff64d8910005fc76cc910065fd700c730005fe739511007efe60cc721006ff61545400a5ff704cb3007ff650cc5100f7fb544c1100a6ff3058b300077d540c95015dfd7610f2101d7e7510f2004dfc7090e21006fc63909500a6fe7358b301befc32d912129fde20cc9310dfdf310c520006fe6390910056fc30d8520007f76248510006dc5318d211b5fd7210720007df74cc930004fc7359721006fd62ccb41006fe405863203eff20d8121007dd74ccb31006fd42d8550006ff65cc92107dfd70cc720005ff7150951005fd7094d41005fd7190d10005fd719512007ff440cc510137bd740cb410067e5358a51007be5450921055fc7055321006fe63d8910006ff4258331006ed7218d21007bf6499121005fd7294d10007f2214811005e7c535972122dfc7250d50004ef7258d10005ff714c920004fc7650b30004fd7610f202eeff2118d52007f43290510006fd42d8520006fc5058432007be4350b31006ff7558032007f5310c520006ff6418d20006fd6250b31117f751cc510006ff42d8121006fd644c510005f57190b1011efe62cc740004fd7018d4104eff10d8910006fd650cb411affb208c520006fd75d8542097ee2018d200077d75cc951004ff7259540005ed7294f21006fd640c831006ff6498b30006fd64985200b6fc3058332006ed6290831006fd7198d21006fc6418d10006fe6558910005ff7458121007f55248510004fd760ca51007ef6590920006fd64d8b30006fd7418d20005fd7550932007f76158520007f73288510006fe6354910007bd43d0520006ee40988311dfee6550920096fe5058032006fb7458031006fe4358a51056ff60c85300077d54cca5114fdd310c720007bc64905200dffa4148110007f76250510006ff70d854211dfe72d97310177c5194d20007fb4348110006fe6310520005fd71d8d42005ff725512012ff7215052101f7f5494720004fd70d8d51006fd4258332005dd739533021fbd42c87400bf7f5154b320bf7e75cc951005ff7154e42007fa4254110007dd3248730007bf6450b31005ff705873207edf3098f10006fe73580320dfed720c520004fd76d0f21006ff61cc5400073d545494203dfe70d0921
  | 19 => 0x53005f7f5355321006fe76485300057f7550d20007f732505100277f5195330006fc3058732004ff7650c32006fe40d89310cf3f5055342006ee7358831007f67348510007fb3254110007bc6490d100b6fd1098f200a5fc70cc9320877f5454b3113efe3259521007df3250530006fd32d814111efc62cc550007f03148110007bf4250730007be6490b301f7fb2058d20005ff7155320005dd7290f30006fd65ccb10006fd6158332005be74d833218dff7655320217bd740c940006fd659891014efd618c720006fc6558730007ef424c921007f553505102cfee20cc932004ff715912013ff5710c951005f571d0910006fe7058a31005fd739852015eff2118d42006fd545833103dfd704851022eff628c9500b5fe7095332076fa205823106efe2058730005fd71d9730005fe73d09210b7de30ccb300defe3158321006fd645812119efd760cb100ddfc7158d20006fd54d8121005e5720c510006fe65d8910006fd7458b300e7dd320c910007d970ccb30006f5610c730006fe7648730005ff7055331006fe7558432004ff7258643006ff655912003fbe4048740006ee4398831006ff764c52001f7c5395320007f7320c510005ff7250730007f543485100b7fa2058332005bd748c951006dc63cc521257ee508c92107eff64cc540007dc7355332007dd430cb301fff521087300057f754c51004efe2058221006fd71d8953007bc645511013f7f5254720006fd6518d20004fd7610d20005fd739472011fde52ccb31006ff614c540006f561185200a7ed2058b3001f7c53947200b7df30cc910005fd72d0d20005fd70d0f2112dfc7254d41006fa7258241006fe63d0520006fd6288730006dc634c510007bd4310f20006fc5158b3004ff43088510006fe6058d21066fa2058031006fe43d8121005de7310730005fd710c941006df32d85300e7f64248510006fe735822112efc63507210a6fa20d81320b5fe70d933209efd7218d52005ff7154d421fdfe7210730006ff535891003ffa5058910067fa5018d10004ff7058c21004fe73d89501ffee62c8730006fc6258730007f9435411022dfe72cc550004fc7359720247ee404c92106eff604c520006fe76cc9300177c5454520007f731c8510007bd5450b31004fe7688730004fd72d9730006fc72587300077d540ca5107ff620cc71011fde32d8732007f5428851004efd30d8910006de634c72010fdc62cc931075fd708c730006fd71d8943006fd654c940004fd70d8954006ff7058841067f84018d10057bc40c8540006fd545872006ffa5058d100079e43d0b300477f5248550006fc64d8910006fd7058b41007f5424871004fef20d891016dff7290f21007f47348510005be748cb3003ff840589101eefc2118d20004ff7058a43006fe7118d2005f5f5394f21007d
  | 20 => 0x5fd721052006cfd768c730005fd72d9110005fd7090c21004fd76909100ddfc7154920005ff705493203dfc7090d21137bd64d07210defc4158910036ff6018520005ff715093116dfd7290c21077df30d8d10004ff7058a41006df630c951007ef6550920006fe64d8520006ef62c85100057d7510f3222efe76c85500aefc3058232006fd650c941006fe63545200877c5354b311fdfc7250730067ee200c7200077e325455016ff72190e21006bd64d091011efc20d8532006ff64cc9100b6fe1098d201fdfc7258730065fc7090831007b74350510004fc7654b31005f97010d200067d650ca41006fd7198f20176fc62d0d10006ff7158b430f7f8544c1100e6fd620c910004ff7259730007dd64ccb300047f7559131006fc5358843007f7619852014dfe7190f20006fd620c7300057d750c540067f4300c51021efc21d8142005fd7018732007f12148110006be6350b41006de63cc831006ff7458720007f5325451000f7753545100a7f6104c910007cd62ccb30287f4204c431004fe73d8941007bd54d0d20007df32107300177f549452012fbd425072100e7c53d9510007be5450f20005fd74d9732006fd6558332006dc7358910007ed544c921004ff7650831077f51098730005fd7010f3207ff41098d10095ff700cb402deff21d8152006ff65cc920006ff53d891011efe62cc730136fe62d0730007bf4390d20006fe75d89102f6ff20d8d52007f5420c510004fc7358642006ff7058732006fe535872007fec20cc7200e7f9700c910006ff5158042006ff75587300dfdd310c520006ff6248530004ff7058f41007f73248510006fe7558910007bd428c5401adfd768c720006fe6458730006ff7358321006ff64987321c5fe7290e51006fd4258732006ff7158b3014efe31d8121007bd545093113f7d520c9510063f6495151006fe7458910006ff7648730004fd76d0c32006fe43d8950007f4744851003efc50589100477e754855004ffa50d89101fdfe7295330006fd5458632004fc7650d52005fd7610d2107dfe730c52021fdf320cb40007f55348510006dc630c520007f97018d10006ff70d8931006df630c910007f57198d1006efe604c721007bd42d0520007df5318d21007f14148110057f610c8510007f551c851004ff840d8910005ff7454d21006fc635494113f7d750c951007cf724cb3000f746554510006fd43d815122dfe7290d50004ff7258e51005ff7159332007fb7448110006ff640c951005fd71d0f201eefe5218d20005de73949300047f7558f42005ff7250d1007ffa20cc72003efe30589100b6fe3098f20004ff7058c41005ff7550932006fc65d8910066fd1018d10006ed62cc831006ff6559332004ff70584320073d5454d42096fc600c951005fd70d8b31005de73c8730006ff625
  | 21 => 0xa5248110005f47350510007df75cc93117dff7654f21007bd4310d201aefd620ca31006ff7558432006ed6250831006fe2058d21004ff7158b400b7f840cc910006fc7358021006fd75d8520005fc735511009d7c7550c320b5fd70cc930005fd70d9331005fd7090e52005fd7210f31006fd42d8151196fe6295331007df32d0730007f763485100877f5054b31006fe4058831005fe764c52007ff620cc510005ff704c52111dfe72d07310a7df204cb30006fe5258730005fd7394520096fc1018d200047f7558e21006bf64d0b3106dfd738c520006fd41d813113eff62909510067c651893103eef2058b10007dd74cc931005fd72953320dff82148110007f741cc721005ff7150e5204fed20d89100177c539452003dfc7059521005ee768c921006fd6248730006fe5358321004ff7258f40004ff7650a31007f87348110006fc3258041005fe7694d210047f7558f40095fe7055032005ff71509500067d65ccb4116fee7290f21005ff704c921005df73595210077e530c95003efe2058b10005fd74d83320b6fe60cca31257ee608c921006fc6350950006bf649933209e7f5018d520457c7550d2106ffa204c72003ff43048510006fe634c520007f46148520005ff7654d21005fd7110b3012efd760c941004fe73d8542004fd760cb411f7de3258332006fc639454010efc624c55003fdc3048530006ff32d8151007f54248510006ff545891013efe6254730007f763505100067c6518943006fd74d89100077c754c720005bc7458520006ff65d8520005fc7655110056ff10d85200277e6594b3010dff724c720007f474cc510006fc7558321005f571ccb311fdfc724c73017dff7254f2003dff7048520004ff7654f20005fc7348510005fd7690d20165ff7250c32006fd6418d21094fe7398d20006fe6350910006bd6410f30007f743545100a7fa104c920007f97548110006fd535864223fef5350b2004efe30d8910007de3018d210b6fd4098d20005ff704c941007cc634c921007f7318c720005fe7610d210067c7359443007ed5250b3204dfe76189100077e20d9531006fe53d8121004ff7655110007f942541101c6fd620ca510157e7510d20005fd72d9730007bf64d0920005de7310b31007fb6354110005fc765512115fbd4210f201e7ef53909200077e548c951005fd7218730006ec3058831006fd6250730007dc634c920005ff7055131006fd54d89310067f650c931006fe735872007dfd70cc520004df73595410a7de404cb30006ff6598910007df3248530006fe6598b300b5fc7050b32007bd424c9410b5fd70ccb10005f57190910006fc6390951007bf7458520006fe6310720005fd74d812110fde52cc93107efc20d8530005fe7610520005be740c7200e7fa6248110007bc43d8542006ff64cc521
  | 22 => 0xd20007ed7218d2106cfd7198d10005ff7050f320877f5255331096ff4018d20005fe7610d2012efc6350720007ee648c921006fd7158321006dc7098c210047f755913007fec20cc520006bf6499120006fd645873210fde7358732006fe43587320b5fe730c9101c7f5710ca51004ff725913101e7f54d815206efe40d8131006ef7058831007dd544cb30006fe435883103dfe7059121006fd64cc921005fd7690d2100e7f5259510066ff620c520005bd748c950004fe73d8910004fd768c520005ff7655120055fc7050f2112fdf320c941006fe70587320aedf30d8d2010efe624c73010eff2058732005fe76d0d2016dff7290c21195fd7695320006fe6458332006fe42d8530007bd6495330004ff7158332006fe40584320e7fb2058520007de43c8730007de43549300aefe20d8d20005dc735533214fee720c720005fd74cca21005dd73d0730006fc5158332006fd75589100b6fe4058332006fd43d8951006fd62cc510004ff7258f10006fd65d9121005fc76551200b6ff2058332005fd71d0d20056fd30d8520006ff54d89100067f65d8943005fd7690d10005ff7155232005fd7498d21004fd7098f21007f76488510007de4358b30007dd4354730006ff52588430b6fc60cc93103ffa2058910006fe2098e210a5fc70551320b6fa60cca4122f7d750c950006fc63d0510007f77548510067fa2018d10007fa32d0110007ef644c921005fd7190d51005ff7054d4214fdf318c7201fdfe720c7300bf7c5155332005f473545100e7f970189100a5fc7054932006fd52d8530004ff7058e5209e7c535943207efe62cc72018dfd759503211efe42d85320079d4310f3203efe7648510005fb7055110007f96548110005ff7155120006fd43580320047f7559132004fd760c8410177c5395120005de7308540005fe7348510006dc634c52110fde3258732006ff64d8121005dc735453021efe52d8142007f66388510195fd729503206dfd768c730007df32cc740006fd6498d21006fe63d0720156fc41d8910006fd62d0510197bd4295320007f3315411006ffa2058d10006ff644c521005de730c931055ff70c873018f7d5255032006fe7298d10217bd74c8540004fe76d0d1018fbd42550320a6fc604c9210157c7558520006fd52d8532006ff7458432007df6390d2112fbe740c941007bd6495331006fc5358910004dc735952114efd768c72011fee42cc720055fe70d0f210e5fe7210d100e6ff620c9100b7fa50cc910055ff70c874009f7f505503203eff5058910006ff64d8d10096fa40580320b6fe7098c3216dfd7290e5204fee208852006fec204c720004ff7258331007ed3248520006ff64885201aeff20d8d2103ff870485101a5fd720c720006ff650c940215fe728c5400177f525452004efc50d89100e7f
  | 23 => 0x6fc63c8540005ff7250d5103eed2058b10097f4100c9101dfef535092005f7f5094f21007fa645411006efe624c720006fe73d85202defc32d8152006bc74589100077c754c520007df624cb30004ff7058e42005fd719933204ffa20d8910007df324c730005ff7054e42004fe7690930006fd64c8510005fd7218d100bf7f50cc951006f972580311fefd6210b30004fd71d895029fdc70cc931006fc63d05210e5fe7294d1001e7c53d8152006fc75d85200bd7e7518732007bc4350920007fa6354110005f7714c910166fc6250d51197bd6495032006ff72d81310275f5394f30066fd4018d10006fe75d8520005ff7255332006fe635472007fde30d87300b5fd70cc910067ee200c5201fdfe72d9730007dc63cc521006fc7458730007f6630c510006fc6350951006fe7458432005fd728c5400b7f82098d20005f571951100b6fe1098f20007fb6548110107f47548510006fc53d8910006fc6388520217dd320c9400b7fa10cc9500e7f5719891022f7d520c950006fd6254510216fd76c854003eff705891003efe1058910005be7610d4215efc2118d42005bf7055342005f57110d21005ee721873013fdd320c9510cf3f5255342007bd74cc941006fd7098f21005ff7254d200047f7559331005be740c520006ff62d051006dff704c720005df7354b320b6fd4098f20006ff62cc951007f7318c520006fc76485500b6fc60cc9320b7de40cc930005fd7294d40035fe7198520004fd760c5200b6fe40d893003efd405891013fee4254720077f840d8d1005f7f50553210e77c5254910005fe73109100f7fb524c110006ff75d8131007dc638c91004eff50d8910007db32cc13011efd7690b310257e75d8b3007efc2058331005bf7250d41006ff640c52001d7c7550f20004ff7259530005fe760c520006ff64d8d200257e7590730006ff705864203efc20d8121007fa72cc130004fe7610b3016eff2098f42007df3254730005ff7650d10005ff724c5200b7de10ccb3018ff72155121004ff7259731007f662cc510006ed62ccb30006fd74d89530afee20d8d20005f9700854007dfe70ccb31006fd7098e52006df3258331006ff63d85420e7ec620c91018efc63553210b7dd40ccb30006ed76cca320ddfe7190d20006fe63185200057f754c540007dc5318d21136fe52d8542005fd76953320257e7510b30217be74c8540005df7355332004ff7655032005ff7055332006ff7058a31006dd63cca5103ef710587200b5fe7054b3203efd7058720005f77254510077f8208c52016dfd7690f200b5fc7054b32005fd71d0b3217fde3259732006fc54589100b5fe70d0b32006fd53580320b5fe7050b32005fd7695120005ff7354920005fc7358520005fd70d873216ff72190d21006fd6558732006fe76cc910007be545
  | 24 => 0xe7498d20056fc50d85200dfdf318c520167fb2050d2015efc5258843006ff64d8d21005fd70cc84104efe10d8910006ff6254510007f43250710004fd7610f21007f652cc510217fb2059120006fc54d8910005de7318910006ef6298910216ff620c94005f7c5494f21217bf420c94015fbd6410f21004fc735912104dfd7088730007bc6490910006ff61c8540006fe6348740005fd74cc921007dc7358121006fe4358432075fe700ca31006fe63d0521007df3250731005de7394b31056fe30d8520006ff6318d20007f471cc910006fd650c841004fb705954206dfe70cc931007fa544c110007be54509200067f65d893110efc20d89311f6fc3258332007ed42cc720006ff6498d102e6fe32d85520077e5059732007f764485100257e751873011eff64cc720005fc7359120005fd7294540007f66448510005fe76d0520006fc5058b31006ff75d8931007f565cc510005fd720c52012efe62505100a6fe4058b30006ff70588430a7f82058d201ffde624cb3007ff250cc510006fd52d8121005bd740c72006eff4058730187f72194d2117ffb2054d200b6fe305833210fee424c720006fd6558121005f9700c730006fd52583311c6fe6294730005ff734852007dfc7054b31166ff2058f42007ed3258121007f66348510006fe5498d20007bd54d0b3014eff610c7202e6ff20d855206fec204c520006fd7498f21006fe52d8141004fe7694b30097be400c940006fd5458432006fd7058b43006fe53582420057d751933007ff040cc510006f76198732005fe7394540006ff6250951006df6398d2100f7454545100075c65cc931005dd7308540004ff764c720004fd7690520006fd644c910006fd71d895419ffb20985200067c7558910007f57448710007f86454110096fc3058032077fa50d8d10066fe1018d100b6fc5058332057f61098910004fd7690a3105d7e75d0721006fd7158b4123fec5350b20006fe634c720006fd624c510005fd72d0510007fa53d0110004ff7058b43005fd7090a3111fbe4250b31004fc7650d10216fc3259120006fd65d8d2003fee20485200a7df304c920006fd64ccb300b6f83058332006ff6559330006ff6448520005bd7418910004fe73d9120007f662545100b6ff20d8930096fe600ca41005ed72d07210b7df20cc930055ff7158910175fd76d0f20004fe73d95210057c7355152004ff7158b30006ff62cc51018fee32553211e7ec5390920277ec504cb2115efe6210f30004fd7690b300b6fd5098d20006fd7118d54005fd719533211efe6390831006fe639452007df77158d10005fd70d93321ff7f5294b30007f663505100867f52d9731006df764cb30007fb645411014fde314c720006ff53d8520007f7640c510004fd76cc841006fc6354510007bd5450f21005fd74cc831
  | 25 => 0x5101c6fc32d9521006fe4358031006fd64cc520006ff5358332197bd6495321006ff71d813200e7c52d9510007f775cc5100defd6118520006bf64d0921006fc7458b30006fd43d812105f3f549532111efe7690b310be7f51d895306dfe7018931007df7358910005fe73d092011fde63cc72016dfd7690f21006fd75d8930006ff5258910005ff76cc52022eff6290950005fd7190d500a4fd768cb3018fbd42553210157c7550d20006be54d894303df57198910006bd54d8943005ff7158b30006ff54d8520006fc63485200e7f4328851000f775494510005fd7690b30006ff71d8943005fd7494b31007ee4254520007ed425472010fbe4250931004ff7654b3011fdc42ccb31007df764cb30006fd7458021004ff72594432feff21d915212fbf425072018dff7655321006fe6498d1014fbe740c72007df6730c510006ff5158843097fa1018d2016fbd4290f210a6fe40d8132006fd7418d52006fe4358251006fe1018d21004fc7650d21006ff5458b31006fd76cca411fefd628cb3014f7f5194720005be7408730007ef6258910005fd75d0b320e5fe7298d10006de76cc93104efa2058221075fd708c720005fd7290e21135fd76d07210dffa2148110006ff624c510127f46550510006fd4358720007ed524c921066fe4058031107f66548510007ee20d89310b6fe60cc941005fc7359510006fc7358910006fe535843216efe6290c21006fc6354521006fd42d85300dff8514811012efc625053104efd40d8910006fd54d8930006fd4358321006fd76ccb41006dc630c951007df74cc931006fc63505200057f7550f32005fd7090e210b77c50cc950005fd71cc910005ff7050c32007bd42ccb41006fc63d8121217f9700c940005ff7050a21006fd32d8540007dd54cc930006fe65581210deff6110520006ff6559121065fd700c720006ff5458332006fd7158843006fc32d8550007ee42cc520005fd7019332097ef2018930007bf6450521006fd75d812119ff43248710136fd620cb41006ff75582320a6ff2058b30006fe76cc9500a6ff20d8132006fe43d8552005ff7650730007dd32cc5400b7fa20cc9101bff721d9121007dc634c5210bf7c54cc951005fe73d05210f7f8524c11006eff2058f10004ff7650d20006fd64cca21057f710d8520006fc325834115efe5218d42007df32cc521007f46448510005ff7150932006fd42d853203dfe7018d21006fe42583311d6fc32d852006fdc304c73003eff3058b1011dfe7210f3103ff53048510005fc7348540056ff64c8540005ff74cc721196fe6295330005fe73c8740005fd72d8131127f66550510005ff7650b3227fef544cb2106eff3058730006fd6518910006fd62d0b3019efe42d81210dfee720c520004ff7258e54006fc6498d10006df63cc921007b
  | 26 => 0x5f5718c910165ff7650f2003ff8105891007ff740cc510005ff7055132007be43d0921005fd7299330005ff7154920005fd70d9121005fc764c910006fc755803204dfc70cca211feff2198d20006ff545873203efd50589100077f7558910006fd53d8121007de54ccb30007df7350b32005fe7690d100bd7e7510f320b6ff61cc910075fc7090a311a6fc205883127fec544cb21006bf6499330006ff62cc54012eff628c941006fc5358b41007bf42cc5400defe5158910007df324c5210065f6394d5016ff52190c210a7dc204cb300dff83148110005ff7050831007d4324c431006fd75d8910077fa20d8d100b7dd50ccb30006ff32d8121005fd70ccb31006fc64d81211a6fc620c540006fd43d895012efe760c941005fd73d09200b7dd30cc9201aefc20d8d21006dc634c921007bd42cc940004fe73d89540177c65549200af7e508c9500057d729525300f745394510006fd73d8954007fb7348110006fd62cc841004fd7118d4218f7f5255321006fc53d8520006bf6410520007f765cc510006de7318d200b5fe730c940004fe7610910006ff7258231006ff61d05200dfde314c52010eff6290931005fd7494931097fa700c910006fd62487400257c754c730004fc73597400057c7354950006df32d8131006fd7198d20006ff7458910005fd7198d2018f7d525523206dfc7054931007ed7290d21005ff705532115dfd7610f20005fd72d8d10056ff50d85200affa3098b30056fe76c8510107f7534851010efc3258732006ff6498730004fd72d8540006fc71580320adfd708c910006ff5058b310bf7f54cc95007fbe40cc5400b6ff505833201f7f5195320005de7390930006fc7558720005fe7348540007ed424c720007df329473028ff620cc531007df3250531005be7498b3011f7c5254b310ddfe71cc9200b6ff70d8930006fd5458b30006fd535872003ff82058520006fe63d8121007bd5450932005fd7190930006fd7458221055fe7094f210b6fc4098d2015dfd7210f210b7df70cc930006fd54d81320e7df328c910006fc4358910006ff6518910005fd70ccb4118f7e6555032006fe1098d21006fe6354521006fd6518d21037ec2018520007ee424c5200057f755912010eff644c720007df634c92007ffa5098d100bf7f54cca511c7ee4294720005fe73d8954004fc7358a4109cfc7359432006ff6254931006fc5058732006dc30d8d210e7f862481100077c2019531076fe4058231005bd7110d42006dc638c520005f77150a21006ec7058831004fd760ca4112dff72507202a7f420cc631037f5711891006dff704c520006fd54d8131005fd7119332006fc7458732004fd76d0730004fd7610c321d7fb20d8520007de4308730006fe4358b30004fc764c52007ff84098d10107f46548510127f7535
  | 27 => 0xe10d852018fdf3255032006fe7098d210e7f43248510005fd7098732006fc6418d20006fd6498910004fd70d8542005f571d0d10006fd4258331004fc7654910056fd40d8520216fe760c94006efd2058f10007ee4218520005fd70d893103efc30d8121006fe7098f21007fb704c920237fb20d95200dfec2158121007f97098d2016eff21d9132005fd7110f300047f7558d10007dc7354932005fd72cc5400e7de7318910006fc5358732006f873580210857e751933122ff9700c9500057d7518730005fd7094e4206dfc70d8931005ed7210d210a5fd7298d20007ed32c8540006fc6308540005fd7290d21267ee20cca21006ff5058732065fd700c520005fd70cc951006fd65cc921007dd524cb30006ff62cc950005fd7090d21007ef7258d200e6fc5258910215fe7294d40006fd614873003dfc7018d211beff21d9121006fc70d89310b6fd5098f20005f77150831006ed620c831007f92148110006fd7298d20006ff71d893103efc30587200b6fe1058332006ff64485500047f7558d2113efe760c951065ff700c7200ddfe7199120007ec644c921007ea4248110006fd7458a31006fe6350721007e5324851003ff47648510005f77154f2103ff45048510006fd644c520005ff7050921007f962d0110005ff74cca21005fe7694d10006dd6318d20007f863d0110004fc7359521007f43250510006fc5358332004fe760c910006fc5458b310b5fd70cc940007eb6248110004fd7694720005fe73085400b5ff7258d20004bd7498d20006fc43d8910056fc305832110fde634c720005ff7654b30056fd70d8520005ff7355320006fc54d8520006fe634c9200b6fe60cca51006ff6358121004fe7690520005fd76d0730006ff72d8132005de7394931005fd76d0b3003ff63048510095fd700cb10006bd64d0721007f66294510007f963d0110006fd650cb10007ef62cc910095fe7095032005ff7250d50005fd74d8d21006fe5498f2012efc3258742005dd73d0b32007f832541100065d6394e51006fe5458910006fd6498730005dc7355132006ff7258730066fd5018d10006ff73d812100f775254510006fd6150730097de300cb30006fc535834107ff730cc510006ff52d8910007be6450910007bd54d09210dfbe740c520005f97018732004ff7058a541ffbd7498b30077ee208c720007ee3248740007f4320c5100defd760c5200e7bd7418910005bd740c520004fd72d8d510b6fe5098d201eefc4218d200b6fe60ccb41007be4059332006ff61cc520005fe7394910004ff72587300177c51d95201bff5710ca41004fc7358a51005fd70d0b32006fc5458332215fe729454007dff764c510006fe6394720007de4394b301dfec5350920005dc7359521236fc32d9520004fd70d8d21005fb7048520007f57448510
  | 28 => 0x8530097df3018d200e6fc52d8910005fe7395321006ff5158910006fc6394940005ff7050d51006fe5418d2111dfd76cc72005f7f5454f211aefc638c720007df6398d2104ff82098520005ff7258730006bd6419120007ed42947201a6fd62908311a7f72118d2103dfc7055121004df7358910005bc735534211fdf32cc720007ed424c520007bd4248740004ff7159032096fe4018d200067c65d8943004fe76d07300057d758cb30006ff65d81211befe6290730176fe62d0f300b6fc20d8930006fd628c730005f97090730006fc76509310177c5359520006ff5058742005fe73d0720006fe54d8910005fd71d8d20005bf7155343006fc5458732007be40d912114eff72d8121005fc7654520005bd74d8b30006fd70d8931006f97258241056fd72d8520006ed6218910005ff7458d21006fc5358742007ee42945200077f3254550007ed424c921006fd7218d21005ff7250520005fe73d9521007df42ccb31004ff7258d10005ff7154d401f5fc7255130005fd749873203dfe70991210177c6554d20004fd70d8d52006ff614c520007ed4254520005fd71d93320ddff768c5200df7f5194520005fc735494104ff54088510185fd7294f21005fc7348550005ff7255130005fd72d07310ddfe71d9120007dd43c8730107f75448510004bf7459520005fd72d9731005bd74ccb41006fc32d81511877f5294f2107dfe7090b310065f6394d5210eff2058e21007de71ccb3006efc20d8131007fb62d0110007bc7458121005f5710cb101ffde424cb30005f970d0920226fe32d9120004bf7458d100057d7510c321a6fd7690831005fd761091026ff751cc7210057d7510d1006fbe404c54004ff810d8910005fd7295110006fe7358910006fe5418d10007f94148110005f7715092107ff220cc510007f462cc5100a6fd7058b30005fd7694d21007f952d0110005fe7690d20005ff7654d20006ff73d852018efc6355320006ff61545202bfde40ccb310b5fe70d8732007bc2155143005fd70cc931006fd640c7200077d3255251007bf42505200e7f7215812103ff77048710004fc7358a540057d75d0510006fd42d8121005ff71553320e7f84248110006fe53d89410077d544c95004efd50d8910005ff7254530006ff640c910007dd6318d10006fd76cca21006ff644c921097ed2018930006ec3098831007f77150b31006fe639052011dfe72d833121ffb20991200047f7558c411fefe6258b30006ff5058b410a5ff704c920006fe5358b30057f510d85200477c6555121075fd708c520004ff7654f2114fbd740c720095fd700c930006fc4258730007bd64d0b32005fd7190910005ff7454921007ed42cc520007ed7298d20004fd76d0b3003ff54048710156fe51d8910006ff7358720006be43d8943005fd7010c32056f
  | 29 => 0x47f7558910005fd7010f31217df328c940006fe6098732006fe7358b10077ee208c520067f5400c510066fc2058031007ac6450920007df724cb300a6fc20d8132007dd62ccb30005f5720c510007df654cb30007f731485100d67c53594430b7de50ccb30006fd7058a41096fc600c931006ff5258332004fe73d854001d7e7590720005fd7290730006fe5498d2129fde40cc93103fbc404854018efe62551100077d524c951006fe6350831007ee62487302afdc300ca3116efe6290c31007ef654c921095fd700c9101eefe3218d20005fd740c831005f970cc910005fd7395320007f87448110006fe7358831005fd70191211ffbf4290b30006fe105873211eff64cc7210ddfe711912012efc6250510097fa500c910006ff648c52017dff7654f200bf7c53cc950006fb7058910006fd76cc951007f56118520005ff74cc9210457c7558d21007f671cc921004fd769452007eff2098f10004fc765533103dfe7010d210b6fe5098f2000d7e758c910004fe7610d10186fc6294d41037f61018910006fd6598d210b7de70cc930005fe76cc910066fe5018d10006fd64d87300b6fe2098d2018fbc215514210eff644c721097f8400c910006fd6418520004fb7059132167f72150d2116efe6290d10006fd52d8131107f45348510006ff624c54007dfe70953310a6fc604c951005fe7348550006fc53580431ffbd4210b301ffdf32c8730096ff2018d2021efd76c8740007f74148510006fd7198e520b5fe70593320b7dc40ccb300057f754c721007f541cc510006fe63d0510007bd645533203ff75048510006ff74d8910066fc4018d100457c754c521006fd72d8131006ff7058a51006fc30d8931006ff5358032006fd65591100a7de204c93004ffa1088520006fd7648540006fd7018d54076ff628c520006fe7558332005fd71cc95121dfe72cc74016fbd4290c21007f4625451007ffa2098d1003efe5058910006ff64c8530004ff76ccb10005fc7359121004fd76cc9101f5fc7254530006fc63d0920007de4358730005fd70953321fdfc7250f301afdf320ca3122efe32595200063d6495253004fd76d0720096fe600ca310067d650cb41004fd7218d54004ff7158a5322fdd320c95003dfc7058d210067c6354950007bf64d09210b6fc4098f20006be64cc831006fd6559330006fd705884318dfd7655032006ff62509500177f5459520004ff7650b10005fd71cc940006ff6250931005ed7294d21004ff765533203efc4058910005fd70d973218efc625513118fbe6455032006dd63ccb10007dd4358b30007dd32cc5500177f5195120006ff6254540127f453505100b7dc20cc930005fc7350a21006fd745843207efe4098f10007f771ccb100077e54cc9511bff421d9121006fe63d0d20006ff73d891003eff604
  | 30 => 0xd700c841007f55148510007f1214c110066fa4058031006fe63d0f2007ff720cc710006fe73584321e7ef5190920006fe7498d200bf7f52cc950006ff7158032186fe6294d10006ff4258730007dd4318b30005fd7388520006ff4358910007ed42185200defe415891018fbf4255320006ff6294540006fe63545100057d75109102e6fe42d8552006ff325874003ff7704851006dfc700c93107efe1098d10005fd7094d42006fe76cc93116fbf4290f20007de43887300167e65d9520006fc43d8520007dd424cb30006ed620cb30006fd76cca3107dfc7050b31005dc7358910005fe7319120055fd70c8530005fe739494004efe50d8910006fc6558332006fd64d833203ff540485101fefc2198d20006fe6498b30005fd708c951006ff6559110005fd7194f20005ff7054941006fd53582421fdfe729933007efd4098d10004fd71d8953067fa100c520257ec608c921005fd7194b300bf7e65553320b5fe7058732006fc6598b30007dc30d8d21004ff7058e21005fd72191100dfbd740c520007f55150510007dc630c520007df43ccb30006fd5418d20004ff76549100affa10d8d201f6ff629093001e7f51d815214eff618c7201f7de42cc930007df3290730007f442cc510006ff644c951004fe73d89400057d758c941057dc30c8730005ed7210f2014ffb1098910007f9644811012efc32591211dfef52509200077c7558121006ff5258b31005fc7350921005ff71591200057d7510f31006fe62187300a6fe2058d20006fe7118d420877c75cc5500b5fe730c95010fdf324c720007be5450b320257e751933004efc40d8910006fc73d8121006fd654c941006fd65cca210477c6594d21005fd76951210deff61185200457e7599121007f77158910004fe7690b30006fc4358332096fc505803218f7e65553210eff8754811001f5f5394f20006fe52d8540076fc2058231007fb32d0110107f454485101b7f72119121005fb7050d10097fa700c940007bc4350b3207ff640cc710006ff64cc510006ff52d8520005ff7355120006ff51d8910007e9424811017ff72154d21096f83058032004f77159532007f87648110006ff6498d200aefe1058232006fd624c910006ff5258341006fd62cc831006bc6350940006fe42d8131005fd7190f21007dd52cc9300b7ee2098d20005fd7610d20007f953d011003eff1058720004fe768c520065ff700c520005ff725511013fdf328c9510dfee2148520006fe64d8b30005ff7254d42096fa600ca410e6fd62c8510006ff625493006efc2058f101ffdc32d8132096fe3058032005fc7650d21006fc63c8510005fe73189100adfd708c940005fd70d0d2109f7c5155032006fd7118d210a6fc2058b30006fd7118d420067c7359741007df63cc921007dd54ccb31006fd7298d10
  | 31 => 0x854014f7c5154720007f57548510007bd42d0510006fd7558232006fe7558730004fd76949101fefd6290b301fefe5298d200057f7550d100b6fe60cc831007dd63cc910005fc7355321006fe435873000d7c7558d10004ff764c910005fd76d0d10007f47150b31006fc74580320b7be40ccb40006df6398d20007ed32c8550006fe5098d210b7fa70cc920004ff7258231004fd70d8d540257e75d0730095fe728c910006fe5458b31077fa708c52003ff61048510007ed524c920006fc43587320475f5394d2124fec654c92117dff7254e42007fb63d0110006ff658c9100e5ff760c9100bf7c75cc9500877c6595331006fd43d8552006fd640cb30006ff32d81310e7fa3248110006bd6550f4111ff72198d21096fc600c9411f6fc5258332007f771cc910005f970d0510006ff644c5100ddfe7118d20006fc4098d21035fd7008730007fb7048520005fd70cca51006fd625083103dfc70cc92103ffa1048520006fc7358a41006fc4018d21005fd72d0d10005fe7390b101fefe42d813203eff2058b100067c6354951006ff624c910006fe54d8520006fe4258251055fe7090f21005fc7359521006ff5258732006ef624851008e7c53597410a6fc764c920006fe7358a5121efe32d81420bd7c7550f32006fc65d81210e5fc7255110004ff7058841004ff7259543005fd70d8d2106dfe70909311877e6594f21007f53148510007f66290510005fc7354921007f44254510006ff654c940005ff725911016dfd7290f200addf764cb30006fd64187320b5fd70cc950005de7395330066fd7018d10007bf6499110005fd72cc550007f1414c110007df32cc520006f974580210477f53551211a6ff2118d21006bd42d8540005ff7054921006dd63cca21005fe73d0520007ed4294520006fc3058831006fe5458332007fa624c11007dfe7018b31056ff1058321006fd52d8132007bd4250521005fe76d091004eff20582210deff6194520007fb4248110006ff5458032006bf6410910057f820d8520005fb7050b30006fc7058a31006fd6254b30006fc638c520005fd72953310e7f421581210a7dc304cb30006ff6458d20005de7390b31005fd7655332007dc634c921006ff648c950067f77118d1018dff7255032006fd658c910097fa100c950006fd6598d200057d75d073106eff2058730004fd768c910004ff764c520007dc7358520006ff7458b100047d7598d20006fd5358321005f9700c720005ff7459521005f5710c910006bd6410f2103efe6058121006fc6058d21165ff7250f21006fe4098f2115fbc4218d4203efd30587200e6ff62c851013eff620c951005ff7150f200a5fe70cc93203efe4058b10006fe6390720005fe7310720007f5414c5100177e6555120005fd7190b3123fef5150b200a7ee2058d20005f
  | 32 => 0xafde7398b30097fa200c910006ff7458221007df324c52003fee2058520006fe4358b10277ec404cb21006bd6410f3203dfc7050d21056fe3058321007bf64991200057f7550c32006ff515833218efc3259742007ee544cb21006fe5458732006fe6158332006fc7558730007f84354110006fe7458332006fd4358b3006efc30d8131007bd54d0d100defd768c5200adfc7055232005fd719093110efe7358732007f331d0110006fe7358642006de63ccb10005df7250f3003dfd7198910006ff53d8121006fe75583212eeff2018d52006fe7358321096fd2018d20007df71cc930007f564cc510127f75250510066df3018d1018f7e655532012efc3259221005bd7510d42006fd65ccb40006fd5498f21007f9654c110066fe2018d10005ff7155130005fd700cb31006fc71583320057f7558d21007f64354710006fc65587321a7f42118d210467f5458a51006fc3058432004fd7118d4003dfe70d0d21055fd70c85100073d43552510dfee2158121005fd71cc950006fd42d8131006bd64cc83107dfe7050b31007de64ccb30007d571ccb31005fd7298d10005ff7154b321b7fb2010520007be21551430a7dc3058b30006fd6318d200b5fe709873210dff764c720006fc6388540006bd64d07200067f65189310067e53d895011efc5258b31005f970945200b6df3098f20006dc63cc92006efe2058d10006fe76cc9411c7f721d9521006ff65d8d2118dfd7255232005fd7019331006fe5018d210157e7590520006ff53587200157e7598d20004ff7058b410b6ff65cc95010dfd724c720005ed720c540177dc329933204eff71d8910007f46294510006fc5358032006fd64cc521006ff525874203efe2058910007f954481100e7ec62c85100277e6555330007ee7290d2103dfe76d8121006de634c910056fd50d852006efe4058730006ff5258b4111eff2198d210e7f970c8510006fd7118d200067d54d8950006ff43d8910006ff3258251005fd73951200dff66118520156fe41d8910005fd71d8332007fa524c1100b6ff62cc930005fd700cb41136fc5258b4107efd2098f10107f67548510007bf74589100ddfc714c920005ff7654730004fc7359442006fd7558732005f9708c910004ff7259331006fd5458730005b5740c5100067e7598d20096ff50580320077f754c72006dfc7050931007dd54cc931006fd43582520a5fd768cb30005de73d0b32007fa4348110006ff5358321004fc7654b301f6fe760c9300177e6594d2003dff704853003dfc7098d2104efe4058221005bd7408730006fa4358031005fd7190951006fd6558d20005fd73907200b7de20ccb301d6fc52d8520006fe4358221006ff7558910005fd72d9510005fd71950322fefe32d9152006fc525834127fef504cb21006fe42582310057d750
  | 33 => 0xb60581210a7be404c940007bf42cc941005fb704c92018dfe7218d54004ff7259531006fd6558520006fd644c521006dd6318d2107ff520cc710005f57110910007d732cc710216ff62c8540007f371481101fefd76c87300977c500c95003efc50d8121006fd639891007efc50583310defc4158321277ee504cb2104dfd7088520005f77250510005ec7258d10006fe7018d21097fa700c950107f75248510007bd54d0920195fd7695321006fc6458b30006bd6419110137fb20d0520005ff7254540007f151d0110007f970cc920005bd740cb41007d463cc5100e6fe62589100b6fa1058332007be4019121005fd760c910006ff3258231007f774cc5101f6ff2158332007f564545100073d5450a511fdfe7218730006fe6098d211dfef515092006efd2058730005ff7150d2004efe20d8910056fe50d8520006fe4098e21005fd764c520005fd7610d10005bc7458910005bd748cb3007ff720cc5100b6fc1098d201877e6594f2010efc5258732005fd7190e52006fe5058b310157c7559120004ff7058f21057fa309891003efe30d81210257e750c7300467c5358a51006fc7358b4111fdc20ccb31004fe76949100477f5055121005fd7018931007dd4394b30007fa7348110007f742cc510007b74250510006fd644c92000d7e7510d100defc2158910095fd700c940056fc40d85200afdf30d8d20007fa5348110006fe7458032057be40c8540006ff5158b41006fd71d89310afef2098b30007dd74ccb30007f44348510006ff6558b30006fc4058b31006fe4258031005fe7390910006fd62ccb30006fe6018d21186fc6294d4022fdf328c950006ff3258031006ff51d85200b6fc30d8930006fe64581210b6fe5058332196fe32d954203efc50587200b7dc30cc930067fa700c720006ff32d8132006ff625873003dff70485100175f5394d20006fd658c9400c67c5359442007ee2018931004ff765532107ff640cc510006df7058c21006fd64d8121004fd7098d21006fe53587301ffdf3208730137bd420cb41006fd5358b30004ff7159121006ff7058831005fd7194d20006ff5158341056fc5058321005ff7059521007dd42cc930006ff6458520005ff7255331006ff7358642006ff6250930007dc7350932006fd42582510b4ff764c920005ed7210d200b6fc405833210efc2058e21005ff7650910257ee408c921007be43d092003ff23048510006fc745832110dfd764c7200077d524c9500b6fd70d89300dffa31481100b7dd70cc930006fd641891003efe3058720096fe600c941005fc7354540006fe2058a31005ff7559332005ff7050a311aefc628c540005ff7150b300a5fe7055132007df70cc931216ff2159120005fd71ccb41005de7390931006fe7418d10005f97010d1013efc6254530004fe76d0b30
  | 34 => 0x8930007de76cc930004fd760cb10006fc5258043005fd760c520006ff54d8121006ff62cc941096fe600ca510277f5454b300e7f4524851018efc6255110006fe73588430acff764cb30004fc76cc910006fe5498d10005ff724c510004fe7690730007ed548c9210457e75d05210aff6108c910007dd654cb30076fc3058231007dd52ccb3107f7c50cc5500b6ff4098d2014ff9700c720247ec504c921007ed424c920007de4348730006ff515873203eff6448540004fd7690b10006bd6410b3007efd40d8530005bd7190d42097ec2018d20006fc4058732006fd644851001f7f53553200e6fd6294910006ff5458331006fd32d8550007ed644c921005ff7255131006fe74d8121007dd71cc93014efd6110720006de63cc84107ffa20cc51016efc6290d10007ef324c920006fc7358321006bf7650b41007bc74585200077f754c520006fd42582310057d75d8b302bfde70ccb310477f5094d21007f773485100057f7558121007f554cc510006fd32d8520095fe728c9401ffde52ccb30006fe74d852007efc2098f10007f643cc510055fc70cc721006fd6250b300b77e50cc950005ff7650d20066ff600c520005ef724c721005fd73905200b6fe60cc921005fd74d87320adfd708c95014efc41d8121066fc3058031007bd5450a21127f452505100273f5495330007f97348110007fa63d01100277f5255330006fc74d81210a6fc30d8132037dc3008730007f654485100e5fc760c910216fc32583420bf7f5195332005fd700c9310aeff20d8d20005fd7094b3109d7e7510c320df7c5154520166fc6350f20005ff714c940006fd42d8132005fd73d0720005ff744c721006ff624c9400057d750c730007f7425451019efc32d81210077d5454b32096fc2018d20007de74ccb3108e7f525974113dfe728c951135fd72d0721075fc70cca31004fd7218d50006fe70d8931006fd6559121006fd42580311f6fe76c8530006fc6398910006ef6298b30006fd648c720006ff75d8121005fd7110f20006fe32d8141006ff5458720004ff715823211ffb20cc52012efc5258742217bd420c940006fc60d8931167df3250c32006ff74d812103ff5504851000d7c75589100b7fa10ccb40006f731d8131004ff76cc7201b6fd620c8410057d7510b31007715154110006fd53d8941004fc765533203efd2058b10056ff21d852009cff7654f32006ff54583210a5fe705493200f7c539511007efd5098d1014fbf4190720004fd7118d20005fd700c951007be4350a21005fe7310520005f9700c520005f9708c520005fd70d0721056fe63c8730005fc735911006dfe7050931006fd715803209f7f540ca51006fc63d8542005fd7290d20005f5710cb31006fc7258231006fe2018d21007fb654c1100bf7f51cc950005fd7695110007f
  | 35 => 0x1eefe4218d20005be741873203cfd76485100fff865d0110007bf64d05101f7dc3258332007e46248510006fc5358342006fe53d8141004fd71d894004efc20582210aefe505823209f7c5318d52007ed6590920006ff74d8132005ff7259510004fd7218d41066f82058031004fd7118d50006ff71d8131006fd74d813106efc2058730006ff41d8121007bd5450d210a6fc3058b30006fc5458032067fa700c520006fd76ccb4010fdc20cc931007df325873003eff505872003eff10d8121137bc42d8542005fd709503222eff620c950006fd64cc730006fe53d8142004fd76907200277c5354b30005ff7254d100047e7619531297de204c931005fe73d9120006fd61cc72010eff620c93109f7f540c950007f653cc510005bd72d0d4104eef20d8910127f7515051003eff50d81210047d75d8d20006ff61485400b6fe60cc95103ff67048710007bd545083115eff2018d42006f76188520156fc21d891007ff420cc710005fe7318954006fe6418d210157c754c520006ff43d8520007dd75cc930147fb10189100b6df60cc930175fd72d0c32005ff7155032006ff3158321005ff74cc521006fc6354920006fe62587301fdfe7219330005f77154b310adfe7218b30005fd72d833106dfe70d8931006fd6558910005fd70949311c5fd769472004fee2098520035fe7090c21006ff6498520005fd7219331007df630c5200d67c5259443006fd6518d1001f7f5394f20006ff7558321056ff72d8520006fe6388520007be4350831006ff654c92114dfe71953200fffa65d01100077e5354b32004dc7359541005fd768c5200177f5159520004ff76552320ddfc768c52010dff764c721005ff7654d10006ff6458d21005fd7210f3003dfe70d95210073e5494d4213efc3259521005fc73589100077c7558520006fe7458b30005fd7219330007f64354510007de6318d1012fbd428c941096fe10580320d67f525944311fde42ccb31006fd6558d10007de4354530004fd76107200157e7519120005fc7354920005f970907200deff6190520005ff7654520005fd719095013ffb20545202defe32d8152004ff7158b432b7de504cb31004fc7359520005df7358121006fc5358720005ff7150921004bf745891001d7c754c720006fd7558b300075f65cc931006fc5358321007ef620c9100ddfc7159520165ff7250e520e6ff6298910005f5710c951006fc6358520005fd7690520005fd76d0910006fe2098d21005dd7310730006ee7058831096ff610c910007dd43587301f7f7214853004eff629852002e7f52d8154006fc6394910005fe7695110005fe7399120005fd70cca410b6fe60cc841005ed72d0521007f632545100e7f6710c9100e6fd760c91007dfe7050731006fe5058732005fd7348520215fc72545400b7ef20d
  | 36 => 0xc215912006fdc30587300b6fc60cc9410e7f72148510095fd700c9500877f54cc550006fe63c8510006bf64d0b30004fd72d96430e5fe72d0d1012ff72159121005de76cc9310077c20d953107eff50583310177f5355120005fe7694d20007f56494510006ff6518d1010fde42cc931006fd65d89100067f72597410e5fc73c8510007f37048510004fc7654d20006fe2058b31006f77648710006bf64d0d20004fc7650d20007dc638c520007f46290510005fc764c520005fd7110d20007f932541100b5fe7018732005fe7388520007ef648c921004ff7158a5417efe6254d100a7de3058b30056fe20d8520007bd6450b32006fc74587200a6fc7358b30004fd72d8131006ff6398d200877c53cc55011fde524cb31005f97094910006fd7498c32006fe7158332006fd6154720005fc7350920007dc638c951007bd6410b300057d7294d5007dfe70d0731006ff6558d10166fe6250d10007f863481100a7dc704cb300473f549512124fef504c921006fe755872003efd7058b10006fd74d8132007d732cc510006fd7098e42007bd5450921006ff6558910006fe76cc95106dfe7050531006fc5458331005fe73991100dfbf419052007efe5098d10006fc705883103efc1058910007f541c8510006ff74d89310b6fc1098f20004fd76ccb10005fd70d0b31007dc735513203efd4058720007dd52cc931007ec6390920007ce62ccb30006ff654c9201bdfd72907200a7df304c910006ff64cc9200047f75586430dff970185200857e7510f310167f53d9520006f97018d10007f96348110006f57198d10006fd6298730007f8624c110006f73158231006bd6410f20005fe769091003efc2058b1003ff44048510055fe709532110ffb204c520004fd72d93310fffb53d0110005fd76d0f3212fbd740c941007f97148110064fe7398d1007efc4098d1012ff5710c9411f7de73c8530007be435092121fbd74c87400aefe608c95106ffa204c510004ff72591320e7ee621891000f786554110006fd7358642007cd32c8730005fe7310d21006fc4358032006ff31d81210077c3254550006fd7058a31057de30c873006ef71058730007bd42cc540006fd7258221006fd64d8732006fd7218d42006df32587300b7dc10ccb30006fd7458a51006fd73583210aefa1058232055fc7054f211f6fe7358332107f7514851007dfe70d9731006fd7358910006fe6390b10005de7310b3009f7c540c9510047f7558f10006fc54587200e6ff62949100477c6554921004ff7058e410b7ee20cc920096fd7218d201fdfe7298730007be5450d10005fc73505500057d75193320afed2098b30165ff7650f21067dd3018d1029fde70cc931006bd6550b41006ff7558b30006fd70d8542005f9700c910006fe6498d21186fc6294d10007bc4350910
  | 37 => 0x8121004fd72d8d40197bd4295032007dd42ccb31005fd7119330006ff765083111dfe72d9331007df3288730005ff7250f30005fd73d852006ff71058730006fd61d0720006fc3258740005ff7650f32006fc73588410defc21d8520006fe43586520ddfe719512013efc3259621007dd70ccb31005bd7418730005fe73d9110005fd728c730006fd52d8142006fc5458321006f76148520005fd7494f2112efe62507300b6fa60cc831195fd7695032004bd7418d5111ff42198d21006ff644c910005bd7498d2004eed20d8910005f97090520006ff65d89101a6fd620c83104efc10d8910004fd76d0d20007dd644cb30004fe7398d21007bd424c54015ffb2010d2003dfc70591211cffb2018520006bd6410c32007df7354b32004ff705864224fec544c92106efc60d8131216ff62085400055d7395253004fc7655110005ff7154942005dd7390b3011efe5298d210057d7519120005fe76905200e6fe4258221007fb62481100057d7590730006fe6348520006fa4258031007bf64105200e7f97098910006fe42587301ffbe7498b3010fdc3258732005fe73d9510006fd6458332006ff32582410b5fe70d9732037f7101852014ff6310c7200b6ff4098f20005ee720c540006bd7498d201f6fc2158332007f532485100b7ed20d8930006ff64c8510006fd63581210b7df40ccb30006ff62cc550007fb4354110006fd5158321006fe7358031006fd745873003eff405891004ff62088510005fd73d05200b7fa1098d201a6fe620c730006fd52587300057d7510f21005bd74187321ffdd320cb30005fd7290d52005fe7390951005f97008730006ff70d8943006fd7158b43006fc75d8910005fd7090d52057ee20d85200257e7598b30006fe73d89100dff9700c5200477f52551210a6ff1058b30007f95248110005fd74d9731006ff64d85200057f754c73004cfe7618910067ec200c720006ee20d8931006fd6559120005ff7154930006fe5458032006fd614c720006de63cca21007da434c110005dc7354b32007de6318d200b5fe7010f32004ff7159320006fc54d81211fdfe728c73012efc6250550004fc76cc520006fd51d812103efe10d8121006fe6350520005ff7055121096dd3018d20006fc6398520004fc735822103eff7058720005dc7350b32004fd7694b30006fd3158321007df644cb30004fe769493007dfe730c540005fd7194e4210efc2058d2115fbd4210c32005fd700ca510477c5494d21056fe10583210077e540c951006fd65cc920004fd72d911003dff7048540006fc53d8121007be545091003efe1058720076df30d8d1007dfd70cc540005f571cca21005ff7150d52005fd7010f2118efe6255331077fa108c52003dfe7094d21076fe20d8d10005fd7210d21007f532505100adfe7618d20216f
  | 38 => 0x19fdf320cb1011efc2098e210bf5f5394f32006fd63189100dffa7148110095fe728c950006ff5158032007bd42d073112fbd645072104eff30d8910006fc63d852006df57198d10006fd7458720007f463cc510006fc7558b41136ff20d8542005fe73d85420167c65595200e6fd621891013ff6710c9510b6fd10d893000f7b54541100e7f66288510005f77150d10007dc630c91007dfe700cb3100d7e7518910197fb2095120006fe764854004dfe70cca21004fe7610730005ff744c921006fe6350b100b7dd30cc910067f6200c510005fd7294d41006fd31d81211f6fe5258332007ee3258121005fe73d0910005df7354730006fd65cc910006ff624c550005ed7210f320477f50549212cfee70cc932007f562cc510006fc6350920004fe76d0b3107ff520cc51007efd50d85300b6fe20583321aefd7690a3100f7c6559510006ff6254531097de3018b300067c72594430d67f5018d54004ff7650b30007bf64d0b30006fe10d8931005ff7054f21007ed6550920005dd7308730006fc63c8550006fe73d8121006fd648c91010efe760c9310267e65d9730005f5710ca511f6ff6218930006ff6254941037fa301891003ff65048510006fe65d8121007f8424c110005ed72d0720005f970c8510006fd6558b30217f72188540005ff724c54022f7f520c950055fd70c854000d7c7550d10097be400cb40007bf6450921006fe61d8332005fc7654d101f7dc62cc9300477f5294d21004fd7018d42185fd7694f20007f64394510006ff43583320057d75d0721005fd7218d54006ff5258043007dd6318d20004ff7058c42007ed3248540006ff6398910007dd32d8730007dd6318d210467c53d9521006fd65d8121006fd75d894303ff67048510006fd65d8520007bc6450d2006dff704c5100a7fa1058d20195fd72953211a6fe5218d2111eff2098e21007f6425471007ff420cc5101c7fb2094520007df71cc931004fe7694730004ff70586430defe2158910005f571cc8310defc5158910066ff4018d10004fc7358b400e5fc7254d10005fd71d9520006fc6298730006fc6348540006fd62d8730005bc7355142006df63cc92011fde63cc7210d4fc73594431aefd760ca31005fd718c940005fe768c910005fd710c910007f74348510007de63cc910056ff70d85200e7fa424811007dfe7019331007ed32d81210a6fd3058b3014dff760c72010dfc7255131005ff76cc910006fd6418d20005fd7294730006dd63cca41005fc76509100a5fc7050932007d763cc5100bd7e75d8332065fe718c520006fc6318542005fd7694b30006fd7458910006fe2058732005de7308730006fd32d81510be7e65cca41004fd7018d210177f5394d200067f7259443005fd7095331005fd70cc932005ff714c950007f832d0110006fc75d
  | 39 => 0xa400600000000cc2860012d2002c00001e00700200000ba48280000dc00300080541184da01f004800208f02a801c00000600c06ad4ae0000040004072063004018c000000000847c13200d01300dc02c03100400000000290040288030075000000c000003042001c00806d08400500122b300100000244ef0020418000028040800429007b070301020a03100d80b801001400b800000408309fb374022001051804805e143028002400009c001800801204300380a001e1cd0030068ff4018000000003200205c839c00e00100280080ae00a002000828c001013011401209101a80e8018003001800000201401105a006c1fe01200000540000038dc40000900028034096003084818821600300600241ea00a101804401602700280040ec007034804803e00200100d403401e00001ec03400506f000400000300000000000640018018004021000800c24801e0018008022109012802802e03b0320020000001000002402003100000a000000c0022114016855012800004601001802e800a0d800000b800407600180100ce007025001003200200000140060430000040008028011800401200100080000183e1001801001a05708480540bc026118000c004031000d48417e002001800000601800000944220210008008000000000001800e03d0020008000038000001c01000600701402e260b042821c02e00000600040181b400384fc0f06790000001634000000000400801507080f809800000b8020072000000002002004700b8014020002002806801a0ca001020c05419e07480cc012dad04d807403212f0000008014038000801401e00d023805403403e0ec000c00000a00000000480a7009005803000210c80002060010220278028130000002400a13100800380de00b00001c000800000300305ae009002003c00c02b00f0000080009003022c1e00000008254004002004047001004104b801cbc2000003803400004e00183ac05406f0098040096031003000401a04700980281da000000011001e00000080b0038000009000800202d05a000402800368380280021e8018804800000000c801804811b05f800c0b0001032809800000000100180000001231e9c0c404f005800c00601400380140c600400b000004c0d3000000c00200a0b600000ae0140a30004040006000800c00004e077804413600d004ff7058a530067d54d89532eefe4218d5203eff3058910007ec6350920007bc4350b3111efd6294b310bf7e6554b3200f7c659491004fdc3088730006fc74d891007dfe70d0b31006fe7198f200477f54549211a7ee420c720005ff72505300a7f8404c910006fd7498d21006ff7650a31007f9434811007ff820cc5200d67f5218d5411dfc7255331006be640c831216ff6294940005fd7290520006fc7558b30
  | 40 => 0x2600200cc0b402207300243be00104a013c1904160018054000013013003c1b800004c002800a056001000005000000102e028c000003bcec01424a065803400012e000800c074000009800800200f01780bc11a02500c802408a00d005001407400200000016a400010c8000000003004803800203c001009c01800300f80005f00f90010004024008650801803e0090120000126003000002c000000007800c0000000cf0000040002000000c00c00701b0038428584001ce900d60120028000006001000002400204200080540180ad1c980ec00237000a0000000015002800400000a00b00c801615f09d000004001002e802c00000c001800804e02d01f8d2c00e00c000009010014f003801400200103d814c006002003d1f8010000004802400803000c809006c000002002c018029002009c00000203508300240e9001002c00c0022c10000e680e801900000a4002003004800600000081500140560018018070008002808c8c2029000808800200b00986a00dc003000800c00c001002caec006000009807800001a00082382f4004000013c00200900194e8000022004000012e2b402a80e80120220038dd000006f07a00a001c05467e800c01000600e802000201e000000413e006000000800001100023400160010a1829c006007027804c0040d900e010805800400d0000020000001000409e00200484dc0120040008000002000002003400a00f00c800000600800304f805c00a000803c02e00301101a800807e00680f802a00002a801c0000000010b2001405c00a008401600702e006401832d000000801801204f815c00801e00c0000010011030807003203302280080260130c100280120010270004000003002802407800909b8008008038000000005e00f2b3801c04e00000500b401000200c03f0214000000015000c00800500042a0054000001800001103101880000000168044000004002806578800c01f0028016000002000c0060a300680000101c9002801c00e00008b000029c00000183bc00045200b00ec00001a000000000201b00c00000120001a10040000007003000400c006002001000602000200140f8eb200d8a34ea6382003996802e0800040028272002000804030c000081000c01c0010000000008006008000805e00a00080080e200000900f8172054009800002200203f011000200200586ac2b602a000800400e000001802c2c353f0ac858400e00300d800014e0190000050094000000000c0001ca0020008002003000000000000b053012000e0011f282ac00061400081201360f1011800c04400202e0000012000007800002c00000a803000021100180dc00200300180700000000018000002018001012800000302280800000000018010eda06f012005800c00100e0008000dbb02500
  | 41 => 0x17002002f012002800a367003803800005a0994ce00120120408080000005018800c0f600b00d80bc12a018071000c01800e1718018000002071800400202b0008f2407e01602d000400a012001801418000d000000802c0ef01e00f405e004007826001c024021009c000000023006001e05a00798740381287db037400208b015007403402f03980200000070020004004042002800c0080340100008000000000000000000f00180740f804d012000008a0940000124042001002000000600a002014810a07f04a026004e0050130032b8604a001833c06400103c00040000000040068b380000518000040034017000004810f00a000408c00100101ac01000601b000401e0f0004800c632003002800000400d00380040000000b300740020f1000037800a00100d006005200000c80480aa0000b7001912200100b89880f800c001800406a004009805802000603e800000200f006ced801c01400000180000000010010006004048001c056000068800407200100082c801400609282a400804100000040001db0cd801c120001026805818600b000001c0020000010034000004052000c0000170038404174001002d78801c19f00002c41a807700300ac08800401b00040c67c3035804c04000300201b800400b000b8a400403d000009806c001001801407013702a8001934017000001801805c000005800016701800081f400e00c802c22800300000040080002cb000835e22f0000000046001006808816200c05c800400c0230c3802c00c00000080d00f41a1012000000800800561e000004b00d800002c00800280343ac01e005803800035d00d0a1801a00900000e000414e00400ac01401a00c803474001400000000420010000d340000060064b5404a004000802412e0e4003801c182380052003801e000001009400610405f82a80880aa001001007a00401100000000460488ed801e188018000402014700988a401024400f00400662c600d032849c00002280dc0280000120124086016000175400602600181f404400201a04c401a0150058014002075000801c00c00000180c888000f025003c09831b0020080010000004800c0fe00d00c090809c00d00f80002320ae003800408c02209e80000041e800d80000ec000003807caca0d904391f800a02800005e000956f00580780ce00844c80ec00000200f009400001900b80c0002000000819401000200002dc2020ad02c0dac14c00f006800400200200986400120090110adc0000f204e000000e000000852000812311a804009004f000011401e00442d0000020000006803400a01000600280460610168000000061059001403608f00080040c0022003000c00606900025900300070068158002000000000034203b08e814870a00000a00d802c01500800d00160
  | 42 => 0xde8084151008003c36a000029000402e04000d001c02400000716f800201009e81a8024000088802e74a0a3034000000200e0090e78012000000801402205300902580062b7027842400a29c096001800000400b80181140070070130008fd8004800000003f0000034000005000000800016d00280000020070038054038002003800c00000e00000140669871dc8058022027000000005c03b3dc801001600300800c80060030008924000061049006408e00003801c0026003000cc44028001000001404200b002000404005400001e400400a00e0e4c01c037000000800200000500000fc018010002005a00800100000f800000702d00000d40000024024859006001c06a001005800829800b0090048018075084007803c00300b800c1c80030078034000000001003402a00000b00c006824a0010000008814165031c0da002008820800e17c004800c02e000090000820a00d00400000000060090110000001002003004e011001001400201b03b001815a0030000000024013043357400c0ad04e01d922a004051028411a12d004000004a006009016c00a006002801c3da00101680318140230000004000016000001c08c03d002801811e004008026000001c0258008006000009803413809a00906e400e05104384d402a001004801400000b005869c0a800f0b5800400801e01900000f620b00505600400000000004002016000003808401000280581b80030020000aea0159f1801000001f02a00000540000d0800400c024014800402c00621e4c440061a3008003c018005003004003c00000400c426201a2d0800000053e0010004066001000000400000601180b42d2002000027009002201e00080000d120a000400a02b0d40048000016000002400c0b200580380000a4000096405213b054001800a00003e801028800a0ad80100080220031ff000219e00180000002ca00000dc08e00000202840320021400
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xaf9809cd6244001f66c890e8088002bd21942885100057c412e8b006200abe8610d42484018fac0ba8c9988033d58971cc8310059e41aa8a14a200a7e859cd62440416e90ab1a42880c7374cb7655032074fb430e690a2000abd8414d6110c0dfc6e438a40880037ae0172105200047e43a85b0a6000bd5839d12144001bcd00b90628810b1fd89750854003775b08c49022000df371dc1624400d7d50db124088002bd60463185420047fc3ac918e4000cfa62dc14344001fc48598a40880033b9cf62c85100063ebaac5a0e6000cbd7458831cc001b9ee7b92c090802bee193248110006eb180e690a2000af5810c9600c401cf0c1baac0908033edc22058d210053f42ec7b0a4000bd68318a5144001f60c8a0a60880033d58b7150b310056f41ec298a4000dd840dcd624400197ecaba4c6900031f9d562d0730004fac3c8528a2000c3d75d9042440019beed21a43981c33d5c36148520005d8c20629022000a7c855c1610c8018f8eab1263980031fa1873551520076c39ee0b12200dafa80cc961cc001bb0c6b846290003678c974d8332006f0c02e418a2016af88058560cc8013f50fb226088002af21173d89100053ec28c831a401baf68198d614800157b0829ac0190033719073581210067db84c0b0e6442af9809d160c84015b906baac3900023f61f42587300056ec1eca31a4000ced645c861cc001bb6c6b8462900027b60a73d07210066fb26e6b1220009f58790831440011fb0139ec2a10033b592720c73031f74386c490a2000bad8119142480014fb0a3a2c1991afb3cc362cc9100047ec06eca186400df076dc520440011ff0eb2443980023fa1b725513000576c14e8b166000cdd635c863440017e301b9662880263f21f624c5100047ec04e7b12a200d9c311cd54d08018fceab8cc69004abea004358032005f9c02a890a2034e6d85081620c4011fb0f286c498803375d063cc9210047ec06ecaa6421caed87d8a62440017cd0d1924288003675d543d0730004fa43aa690a2000a7e859cd60c84011fb0e2a2c3900029fa1a20195310b67d302e19906200adc835c560c84013db0f214c2900023f61e52587300056e41ac89924200c7d7598c424400197ae8b90c6aa0031fd497118d540047fc0ae5b266000cf980dd94348019be4e031c8288002be21932d01102b7e82026598a200dadc835d561cc00197908bb4a488002fae0964481101376739ac41968200de57218a41440675dd05a0ec0908027be1d65909200047f438c6b024216cfa605c332904011fd0e192c0188036ed9170105200b47f43cc8b06641cf668518921440759bec3398c48806fdc614714811000576c108131e42008fe87d9162cc001fa66490a60880727761e63cc9101a5774108031a421cc7f525da52440015ed0d99442880337a989700c720
  | 1 => 0x865baac4880025f21d54cc950006f4412e018e4000d6d759086148043b3a8539c84988027e60073551200061ebaac82186400adc8359532504011fb0e31ca4880032f58f71553420056ec06e93184200bd68318b31440011fb023b2a9990033e88171d81320066e320e6b0a402dcee625ca43c40018fac4bae8398802b721942cc9310057cc00e7b024200cfb709c3624c401cbeebb9ac4880f3d3d4e53909200069ea12eba0e4242dac7250931500018faeab94c6900037a209700c52000576c1682b064200abe8419562cc0013eb0239a84880032fd9172d0d200057ac0c40b166200beb8258d2044001fc265b8242880033b60b764c5200047e43aca9928200af581943614c8019b8e6a1ac48815ef5e0563cc910005ed41cc89822045af9809d5600c8019baec3186290002fa60b43481100065f312e818e60008fd8798e4148001be283b8262880031f98975d07301ef78908e6b004200cbe42dd9420c4015db043aec4880027d61e63885100066e210e6b1220008fd87d496110c01be6c3b824290003dc18d51541100047ec38a9b122000af9801c961cc001bd700b94a8900737c48171109100047ec3e64b0682008fe8710961cc0019baedb18629009b3d887715932018f96192a8a928400de4635c831440018feeb3aac48800337dce73d81210066e3b66490a6000ade83d85315000197ce6a16c2a0002b7a0e64581210057cc0084b0662008fe8715162cc00197ae9326c1990a7374c5768c720006cec20e6a8a6000cfb805d841480011ff02b84c7290038fe056550f4113d7ac0ceab0e4000c7e625d741440015f300192c11888adda1664cc5100655e4328418a800097f87552325400197ce8b94c690002be60243587300068ebaa87a0e601cc7d625d44244001a7eebba2c090803f818a51481100071ea1aa8b14a23ecec72d89514c0013f301b8a84880037c881720c5100047fc02ec1968200cde765d3324c4014fb0b322c4880036ed917010d1000677bb28498a4000e77855846148001bd104b8462900d3b3080634c9210069ea1aea21a4200de4305c831440019b8ed31a6488002afa0f7650b4114e5fb0ae818e4000aed8299262cc0013ef02bb46488003f8d89214811000676b12e19906200ed56318d41440017af02a9665988037c60273485100065eb22e3a166400a7e8510d600c84d7cf02b24649085abea0353583320063fbaec8b1a202e9df865cf42cc8014ff0ab26c690002fc607425411000677b26e498a4200cdd821cd654840157b09310c398002afe1163989100053ec2880b086483ebb205906448001b72e83a240880031fd51760ca510056e41ac918a4000cf7865c7320c4015f50521ac018802b76103018d2110e76316e498a8000bd78358951440377e102b9a4088003b318f620c9101f6f5212e19924000
  | 2 => 0xb7250d10004fdc02eaa166400ade8314960cc4011fd0e202c219036ee201424c54033eebb88c698a20009dd82dcd51cc0015f106b92c1208029fa166458910006f5212e018e401cbcc8258f32440017b106b168088073b35cd62189100057cc0064b048207af6869d121440379dac2b9062900033d591710c8310059ec204032a621cfe2428852044039be440b8864880033b591720c5200056f41c84b0e6000c7d751d560cc8011ff00bb68619002bbe0964485100056f41c85b0a60078fd87d91214403daf0cab84a688003371d9324c5200b4f7c12e7b22400dadd8690d61cc0011fd0fb1ac4880735ed497094910004f7c3ac91924200de6835c83144001af640ba886900aabe60374d89100047fc3ac81922058ece3058862cc05397ac33a06390036b761b3258730005ebc1aea90a20008fe87d8961cc01d7e50c18a40880023f6037650a310063f312ebb16603fecf8358b32cc01f7e50021662880037a9437258d100066f306e6b024200eaf84589420c47fb3a853988598002de614434811000576c1060b0e6484d7a65dc154c80d1fa441b1e6288002b7e19424cb3010d7ac0ce6b08641baf8865d120440013f700b9086900029f61442583310067c106e4b006200abe8419662cc0019bae639ec090826fca1871481101a57ac08e0b106233cdd32dc1610c80197cc53a6c5980035d5d4320c510005d6c168721e4000cbd741d161cc80157b0832ac1990033e591700c730216d73928418a8021e6d85083624c4017e3032a24088002bd6045058b310063fb2ae12126200ecf8258c6348001bca80b9062880032f5d36398d200071faa4a8b0064008fe8718d4348001ce8ebb8ac488002e76105318d210053ec2ce9b122000fe062cc5204400157b0931cc290073b39cd6218910004fcc00e6a0a4000dd4635c4325441b1fb0339ec4880029f61443587200066eb9cc720e402acf876d8950440131ff0fb1682880031f595700ca410066eb98c7a0a4000bf38150d50440011fd0e28ac1990023fe057610f20004efc3ac631a4000aed821d362440019ee203b662900ff3b9c962907300071f2a0c6a12a200cf5109d831480019f440bb6648814ef560663cc910006ea39ec690a2063fe250d8921440018facab8064188033e88276cc9100065fba6c6b024200abd8498961cc00f7e501a0a4288002fc60a5148110006af996eaa186400cf9701c1628c401bace79944288002b7a1e634c7200047fc3a85b026200cbf7695142cc0011fb043b2a9988035b8c975d0521004ee43a64a8e6000aef825d162cc001dab0d996638802b3d1da625451000596c28c8a1240009f9801cd5444001aea43baac4880d33b1c162908310066e41aec18a402edeb605cb43480018faeab26c1991769f6087359442006f2b96c528a20009f980dc943480018f
  | 3 => 0x6b044231c7d52dd9548c80157b03b2686900038f2096550b4110d7ac0ce6b0e4000cbe7650b41480019b8e1b1e64908032f5d074584320057dc02a9b024200b3d8510f61508018fea8bb665288027da0f72505100066fb1ae0192a200abf845d5624400197acaba46488003bcdc770589100057cc3864b048200c3d7559341c80019dee5392c1188033b5937258d100e6ea992e2192203feac4258942cc0819bce7304c399002f520d75485100056e41ac898a2000cdd861cd60484019ef02bb08690803b958862905100967db22e01928000cde621cd51cc03547b0839aca21802fc60332945101a767210c6992422e8fe8798d43c80015bb0231c629007bced52544c1100069ebace931a401cee571d8a62440011ff0cba6641881ebb21942585200047ec3ec990e600fbf28094b31440014ff0caa2a5990033ee01768c5200047e43ac890e6000af581dd36148001db4e721ac010802fc60232505100066f31ae12184200af781553614c8015ef02b92c3980033dd8971d09100069ebaa87a0e401cdd6219cc6244001b76413a06290073375897318910096f9b0ae01922000d3d7550f41480015bd06392c0188023f61e5098f210069ea1aeba0a200adf372dc520440015eb03a92c4880031fdd6755873014d7dc02e4b044200ecc764c921cc001a7f04ba886a10036e509700c540004f6c14e72a6423fcec7258961cc0018f8a6b96ca88003b9e0574588310055f424cb3122000cbf749d161cc0011ff0eb20c290002bee1d42580310065eba2c59968200af980dd3604844775d05b2285988035b1d772585200053e42ac7b122061fe04018921440014fd0b392c398003f850a5148110006ec41ae010e60008fd87d9432440159e8ed312828809775cc9710c9410e66eb14e63122042f8c325093250001978ed2a284880032f5d074580320053e42a86b00642ccee725d263c84015b906b12628805b3ed8570cc91000576c10c7292201bbf2819d120440019dac9b9262908033e59170187320053f428c8b066400b9d8195143cc001ee0c8a8aa088002b7e19544cb300066fba0c698a4212cf8605c0324c43b6f10ab8a408806f6e442740c52003ef940ee090a202aee710881620c4015ef02a96c298002ed610620c51006c7ec0ce7b22206bced70d8b32440015f700a16c098802b720d62545100053fc2a86b064221cec70d8a424c4395dd05a1ec4880023f60b7655110006daba0c418a203fcbf625d021cc001aeaea1948288003b3d8b324c510006f4312e19922000dd8201cd6148001d6f02b20c890802b760e74589100057a4326490a2000cdf74dcd62440019db0cb906398003b9d9062485100057d43c86b00420fbf2830c5204400d1f90cb9682880029fa16745843203d7b4368290a20008fd8798f42440011fb0db9aa9900023fa1
  | 4 => 0x348401aeaebb1062880033d0877159332005f941a4290220008fd809d842cc455d9e63102c418803b520d611852003ff1b9242902207aaed829cf61480011fb0e31c848800337dce73587200047ec04ed21262008ff8750d61c800157b09392c398002de61672cc13032775282c431220009f787d8831440019df0cb9063980032fdd27358910005f8c066598a2000ef1811c9600c4019be603b26488002f5e0d62505100056fc3ac7994a200dd8109cc62440475ef02b9ac3210023f6087359110006f5b96e0b0a4000cfb721c9600c4017ad0d9966288002b7600634c921006f339ec490a2000aed84dc1620c4019b860bb04398002f620d62541100057cc0064b04a2008ff865ca54440019bee739ec29005b7c9c3320c51000676b20e4b1a2000df1724874044001db0c039ac090833f4d84634c1100047f438a2b006431cdf32dd9548c8017e30339a408801ebea0363d81211fe3eb12ea10e600fafa8014960cc439fc0c510a40880032f8cb74595200067dc02ec1922000de9425c332480019beea39ac4880031fdd772589100047ec06e4b1ca800af581d0b60484018fec9baa6390802b7e08638c95104e7a3b6c490a2016df270cca41440017e30221a4088002f9606644c9211be76396c898a4200c7f75dc562440c79dae1b1242880023fe0970d8d5414ef920ee090a2000eea205c9600c40197ac939e8390802bee0142582310055ec20a4b0886009ed879083148001a7aa9b9286a90d33bc8176908312166fb12e610a8027cec62dc951500377e5023a240880d3374c873587200066eb98e6b0c8400ddb109cc62440bbb9e4239aa4990023f60673d89500065f3b0c621a842dde7615ca434847d5dd0421ac199003b3594634c9210076641ec41922000fe142cc520440015eb0221ac390002cf20d54549420dd7c432e69022000abd84d8961cc00176b0221ec2a10023f6087359741004eec06e6a966400af980d51600c8015eb03304c399076dea1673481100047f438c8b0e6400aed8215161cc8014f90aba2c0190037650d700cb300053ec2ee5b026400ee876d892044001fa6e618a40880032f5917110c32007e83986290220009fb805cb43cc0011ff04b80c6a88023f60873595410667c380c6a12201df735494520440013ed0f2a6628806fbca183148110006f5212e018a40008ff815db42cc0011fb05b82c6208035dc857510d2110e76316e498aa00d8fd870cb604c4015bd062a2c2190027761e54ccb3000676b12e39968200ade80d4c6348517cdccbb2c6490802b760e64d81210069e41aea21a84009de83dc5424c4018fccab8ecb98002eb60b4390d20247f11026490a2000d3d7550b41cc40197ec8b9882900033b219720c5400065fc26eca1062009ef825c643c84015eb02196c0a08033b9c1629083104d7d4048
  | 5 => 0x8002b7a0c425873004e7db12e110a4000d5c7518d4348401af4eab84c6900863f61c30d8931004eec00e6aa66400c7f855d841480011ff00bb064208023f61e50587323ee6eb84ed9926048fe0704c921440015bf06b2ec090803dccc951541100e736baac431220009f9801cd4244001cbea729ac1990029fa0873597410067db84e0b10621cdf2205c632440014fb0b324c6908023fe017610d21004eec06e6a166400cdc635c831480018feeb3aec290002f960a63485100063fc2ae3b224000cbf65dd16148053b5a82b9083900033e5c06018d210055fc0ac9a166400bb98010d42cc0019dae8b82c4188031fd5176947200055fc32a8a1062008ff815db43480019bacbb9ac48806fdca1471481100dfb942862902201cdda209cc62440013dd0fa126490802dde156350510006f2b966418a2000dd5211cd62440019bce6a1ec4a804a3fa1b735092007d7d40084b0662168ff865c3328c401fa6c798e8088002af61854d91200057ac0ce8b0e603cd6c75909314800137f0ea1887900ff2fd8a748cb300e57741086b122000abe8419560cc86fd9865b2264908029fa1471583320047fc12e231aa000cf8625c03150001be4a139a42880023fe19700c8410947e432e710a4000bf18090d51440018feeb3aac3900026fe1d4310d20004fb43e8598a2000af9801d5610c8015eb0c19062880023fa1e50d89310063fb86eab122000aed8214f6148001d6ec9322a288002b7a0e52d81310047ec38c7292821cece73d8832440016db0bb1c84900032fd95748c9100047fc3a63b024247f4f5394d42c80375ed03a92c4880031f8cb755912000576c10a9b0a40009f68710d2144001aeaebb148288003b320d62ccb4100576c10a8b086400deb62dc121440015bf06baac390077dcd495148110006b6baa8430a4000c7c855c663948011fb01b8ac529802bb6085358432004fb43cc598a2000aef825d5624400167b0a202c9990023f61d628c73000677386c52126223eac4258942cc46f9f240bb483900023f61f4358720005dbc22c418a20008ff8759031cc0018faeb318c48801efc606624c11000772318c490a2034eeb20881620c4019ea2139ec2900035bdd53258121006ce3a6e6b024229cdd315d831c80011ff0e996c2900023f61b704c72104df9c12429022000cfb709c1610c801b3ee839ac09080337dce73d8542005f8c06eb98a20008ff805cb63550019bb0e31c64880030f5d564193320967d302e01928200cfb405c7604c855dd421102c418802dd61462cc5101f63fa92e131ca400cbf7655143c8455dd221102c4188031f59770508310066e188ec98a4000cde7698f32440017e30019062880fb3b98970cc8310076631aa49924223ee462cc521440011fd0db9a829017f730cb74549320047f43e84b0e6400cdc635c64
  | 6 => 0x65fba0c6b0a4021cf5215c663c800197cc3ba2c2900032f1d263589100055f420a6b0e4000bb8845d520440011fb033b085980023fe097018d410056e41ac4a0a20008ff8754b604c45b3df0cb948790802bb60840587320069f2a2e329a841cee776d89214400175b042a6c8900034f1d4745891000767318c59922000af68610f31440015ef0ca9662880d63fa1f32587300047ec3886b12200aaed821d160c84011fb0039ac520802b7a1b71cc9300757d40064b046200cef625c732440013ef02b948690802afe1173d89100047e43aa5b026200a7e8519161cc8011ff00b8cc729003b350d620cb300065fba6c6b0a40008fd87d4f6244001be6e2b86648800317dd47358910006f5102e431a2000d3c751d161480015b906baac219002bda1b42485100063ebacc7a0e423ff8e8498b32cc0859dce4b206290002ed21162cc5100047e43ac898e4009cf676d8b31440015dd0f202c418803575d732d0730006ec31ee098a2034ead84081620c4014f90ab9ec0908533be1d7298d200e63eb12ea312201baf681d936148001f88c59966288002b7219524cb31004f7c3ac43122000eb96419130440019dae4392c398003f850a2148110004dfc3ac8216600abf38158b40440011fb033b686900037a509700c7200055ec24cbb122007af4865cd21440017e10ea0a40880023fe0176ccb4110d6f41ce0b0e6400afb805d562440011ff0eb2462900efd3d4e53509200047f438a4b0662008fd829db434400176d0da1a8288002bee1e425803100576c10a9b0242008fd8718e515000157b0832cc5980023f60076549310067cb12e19922000af58190162cc4015ef02a1ec2900363f61c62d81311fe3fb12eb1966000de9425c031480011fd0e21ac19080379608734851000576c1686b166000b6d8598e42480011f90cb9c8290002bbe096498910005e6c148790e6000a7c8558d6048401f60c8a0a40880023fe0176cc84114576c08e0b106200df1805ca414400197ecaba4c59807376881731891013e7a3b2a298a4200c7f54dc1629441f5ed0db9662880032fdd263585200047ec04ec1926200ecc62d8c3244001cd8ebb92c488002b720d70588310056ec00c721a4200eea20843624c4011fb0fa1ac0190037a883724c51016e6eb94c7218421bdad415c8414800197c853b6848802a7de057218d1019eeb992e21962000cbd87d92644840157b0829ac390002af61065587320061ea9ae831aa200c7d7559362cc04fe9864a9264a8802f521b32cc5101a57741480b106200d9e405cc215000197eec3228598002b7a0f624c9400047fc0aed9922000bf1810cb4044001baee7b8ac4880033bdcb624c55003ef943ee090a20008fd87145600c8015db0429ec0908027de1d620c5100047f43ac498e60008fd8718f41480019eb033b2429
  | 7 => 0xf060dc5604843bee0a728a4088002af21954509320067b434e690a2073cdd7058f32c400177108b1a4088002bb60830588310056ec16c6192a200aee809cd620c401be6e598aa08806ebd205645852000576c1086b006400af586cc92144001d5908b10c488002bda1b3248510216ed992e019280008ff865ce5148001bcf08b9062880023f21d4258031004fa43a8690a2028ee710081620c4019beec31c62900027ba1e42585200063ebaac830a4000df0405cb31440018feeb31a62900029fa14435872007df94048598a2000fe2421c520440015f700a12c128802b7e0d6598d200076631a8499242009be8719142cc0159f6c2b8642880027720d71909310066ec10e6b122000bb9800855450c01ba8e6192a3880039b61470588310065eba6c631220008fd8714161cc8015bf0ca9665980537a60b704c9200076db1cc6a8220008ff87596325047fde24339ac0108033de1d61187300047fc02e431a8200add878c063484019ef0cb8e65108038fdc16550b410047e432e72a240008ff8759061cc8019beeca1a439812bf810232485100047ec36e4aa2203fdcd8798b32cc00197ce3b24c8900023f61e63c85100067ab16e29922000aef8258521cc0015eb0331a429015f759cf320c5100047fc12eda0e6000f395419150440011fd0f282c219097b30c9644c921007e9b1e62a822000cbd645c443c80013eb0e194828806fb50c531583210047f436e6aa240158fe861cd52480018feeb3aac598002afe1165cc9200a67db16e0992403cd6e7590861480011ff0cb8665208031fd4d7118d5400576c0841b1262398fe86dc1314840db76c8b8042a00031fdd76458d210dc7ec02e5b1a20008fd82dd943440018f90abb064880023fe1d640c7201beeb992e219482008fe87d9532440015b906b2ec090802fca0e51481100047f43ec8b1a42008fe869ce5244001be702b846488003755cc73485100de3eb0aea30a40008fd81dd94394801db700b18c6900032fdd07358910004ef43ec8996600dcf47658d21440011fd0e29ac3900036ec807459520007f099243a022000c7f7558d624400fbd305b8242900ff9b94b5258b300065f212eda166050eda5058c634405d9dcc4b968798003f8189214c1100063fb2ee2a126200abd8414d6210c0197e42ba4c69000337d977358121005f2c14e890a2000bf180cca21440014fb0a382c2190031f5d475580320067c102e031a4200aed82d852150001bace631ca288002f360853d8d211ae6f43cc698e421db78855d12044001cbea729ac488003b560732d85300056ec10c7192a23fe6d75d8a62cc00157b0832ac598003f198d32485100e6f4312e190a2000cef72cc9608c40179906b2a6490802bea1f32580310047ec3c84b046200af7815d562440015bf00b1e652889abde0574587200
  | 8 => 0x9a98c6908023f61f64885200055f420cab0e6432fab609514248001af640ba86290002fce0951d01100047f438c8b16603fc7d625d662cc001b98e6992c09080379591720c5100063e42aed2122000c7d7559021cc0015f700a1ac199002f6a0c62d01101deb63aa8498a4000c7c655c3324c401be10e90a60881173b1cb624c55014e3eb0aeb20e4000dd583dc542cc4017ad0731662880023f61e40587320063f3b6eb992a000db774dc56048401d98c699242900037cdc9214c1100055fc32a8a144223dce72ccb41cc46b9e8edb9a42880a72fd86740c7200066ebb66520e6000c7f75d8d6048401c7acaa1665a08033ee0176cc9100065fbb6e2a168200c7d625d443cc40dfc0c438a4088003ea95142481101a6f4102e418a4000aed820c3624c4011fb013b4a5988032fdd86450d200047f43860b10621caec8255362440555ed0221ec4881933d9d9628851010d7741086b0e6400cdf65dcd62440013df0eb2c64908038f59564553310061ebaae931a40008fc865cc41480015bb0fb1864a8802dd6166448510006cf39a85a0e6000b778550d21440379db0cb906290002bd6044058b3114e3eb0aea18e4000dd4301cd21440018fcc4ba88798002bd60773d85420047fc3ac818a4000c7c855da31480018feea31a629006f3e1d9624c11006d7d400a6b0e6036cdf325d83210437be4a2b864288003791cf6248510055f9c0ac4a8220008f78758461480013f50e31260880ff3b9ca63d0520005f841a429022000cbf74d8d62440019eb033b664880a23fa1b704c9210067cb22e018a40009df825cf41cc00157d0c10aa8a1802be6003258730006ea39e6290a2000afa801d5610c8015df04aa6c48801f7ad8b70485200067cb84c130e6428ecf31081620c4375ed0332ac2900febb2094358b3024773882c490e6000af980dd161cc0017d30532240880036e1d370585200069ea12ea21e4223e6e52d4962cc401c7aa8a1ec0a9003371cf71589100066eb9cc730a40008fd81dd9548c8015f301992c018803e690f424c1100065e316e8b12202c8fd8798f43c80015bd03398c690003751cc6348510105bb42ce890a2000db874dc1624400197c64ba4c69010337a1f325833100577c02e8b106200bf38050831440011fb0f31e8390803b9594624851011d7741080b166200abf8459563480019b8e7b92c4880031f98975193310e6dc902e91922000cfb805db434807f9bac4b9843980023f60476509302ae6fb80c718a4000ba98010d4248001cf50a392c018876dea14434811010f56c2041b126200af9800cb6154001bcf02b9486908022f61f6410910006f9baee29022000bf1810c950440019db01bb264190023f6077058a430067d302e3b066400abe849d162440015bd0dba664980031fdd5644c7200059fc02a8a928470e
  | 9 => 0x7358520005f8c0c84982203faee8299562cc0c7bcae3b14c488002eda1062cc510005ddc22ea9022000cdf309db3244001b9ee7b92c2900025f60873545500055fc22e2b006442df1215c021500011ff0cb8c85980a67ee19700c720006dd906e8b2a401bfe1820c5204400197ae13a4c6900023fa1e63549100047fc3aca1928200cde73d8f60484017e30139a42880033ec81760c5200063e316ea98a2000ce5625c7320c4019eb0fb0c42900033be1d62189100053e42a86b0e40008fe8798d43480013bf0ea1ca5980023f60376cc91000796aa2a6a12400cafa80909600c4015f30021ac3980027de057294d210063f3aae531a4000ee9721c9600c4018f8a6bb4a390003751ce3254510006eb418e690a201bdf276dc520440515df02382c4188035b4c975d072110e76306e498e4207bf28094d2144001be6e7b8a40880033b5cb61d05200065eb22e1990623fcf9625c021cc0cb9dae1b164288002f660c62d01101fe77b8ac490e6029af68110f6048401dd441392c0188023fe1972d07300066f408e6b122000c7f655c0624c4013ef02bb0648805abe20143583320067a882ec18e4020f7352485504400187aebb2682880036d18d740c510005ce41aa8a126416af88059160cc8011fb0e2a2c5980a7b9c4370588310063f312ea21a2000ced765c3328c8393ed0f31a4288003b5dcf71589100057dc3c86b0042008fd81dd942cc0151ff02b96c8880023f61e6348510007e8996629022000c7e655c332d04019df0cb9062a00a71fd477058a51035f943ee29022000f2f6595142480011fd0e196c098802af20d641911033fe9100c798a201caee829916244001be4a039a42880031f5d663d05100063fbaec898a40008fd8798f41c80016eb0ba0e62880023f61c63885200757ac08e4b046200d6e325d4434843be76a92a24088096bd6067458432004fbc02e39906207af4865d521440018facab8665a08035ec8175905200047ec00eca9a4200ade83d9363480014fb0bb9ec2a10023fe1d43d85200069e328e8b2a4000c7f755916348485a7a84ba842a006f5e441750c5200047f436e6a8a4000aed820c1610c8014f906aa6c4a80032fd8f7155142075dc4028518a8029cf9615c241c8051dce20382c418803dc59151541100067d31ee0a124016fd361cc930440019bb0e186c690802bea1832541101fe6f992ec10e6000fe13248550440538fea2bb4a390002fc60632d01100057ac088131e4200f2d5454d42c8001dceca31242880023fe1973d07200e6f890ae021220009f9801cd215400197cc53a063980039b8c95458a511ee77390c7a0a4000df1515c34144001e5aa8b2a849001efca037448510005b6c2ec6a1240079f58719121440015e90ca1242880037618d708c910005e641aa89924200c7f761d562440015bb
  | 10 => 0xb12a200bf1818c950440011fb01bb665208033b5c962947300047f438a8b0e6000c7d755936348001dc902b124398002cf6144350b310557d404ebb0a40008ff87509600c401e3aa8a1aa59801b7698d7008730004fdc02e518a4000ee972909600c439fc48490a4088002b7219424cb31006dc326e0aa22000dda801cd6244001d9ac7b16648808adda1741cc5100065eb2ee8b0242008fe8719161480011ff0eb2664880034f5d54310d2023eb63aa8498e4000cef7298961cc001bb4a1b9ac4880023f6027690b313c5f3c12c230a40008ff825da41cc0019dac4b8865a08026fe1d420c540004eec00e6a166400bda831895044001bd704b806390002af21942505310063e290eca9220008ff865c03290401fc28438a4088052bea004358b300047ec3cc831a201ceae7458862440015dd0121ac4188027ee0171909102ae6f388c618a4028ecf311c1620c4011fb023b285980031f9d562d05100065fba4e8b0642008fd819cf62550016f70ab1a40880035dc8575991210061ebaac821e4000db710dd16048401a7eebba2c2900023f600765513100772c0c40b106200bb582d0d41440015f3013a2c199002bb60b41d81210069ebaa8621e4000d3f75dd16244001af6a2b8064a80023f61a7390a5114cfdc02e5b1a2000cdc101cd62440019bac9b9ac488003375c030d8d21005f44328490220009fb805c841480539f421b82c518872bb20965589100063eb82eb31a4000adc8358b424403797ac2ba062900023fa1c53d85202256ec1480b1842008fd87843624c401d9d07b1664880034f50d7510d1004ff1b0ec4902201caec8254f6244001a7ac8bae83908a6bda0453d812113e76316e4a8a604bd6c758c960484016bb0bb86649895bf494132cc5100055ec24e6b006400abf8458d62440016db0b31a84900032f4c97418d51005dac0ca8a1a2025cf47650531484019bce7b1ec4880aabe60075d89100066e190ec9922000e5f5394d60c84197e5001906288002bb610705883122f66196c4992a000ead54589420c40157d0829ac5980033e98d7090720005ed41c84982203fcbf629d021cc0019bae639ec488076de21543481100056f41ec4992a2299fb805c864440013ef02b9086908023fa1f6458d10006f9106e29922000cdf101cd6244001ab8e6192a2a809fd38c952cc9510065fb22e5a0a4200de2205c831440018faeb31c83900032f9d263189100055f424eab122000deb825c031480017e50f20a4088096bd60674587200047e432e421a2000bd6839d1214400197eecaa285988037adcb7058d200067c31ee0a124000e3c751d16244001dd6e5b82c488002b76085318d21005edc1ae2902201fb7a858cb4044001bb641b9ac290002fce0553481100066eb9cc728e4000af9849cd6008439aea42ba8848800376843
  | 11 => 0x440018f8c6bac83901c73ddcb71589100067cba2e031a20008fd819cf62500019bce6b0e8398126dba16644c9210053fc2ac99924000bf18094941440011ff0cb9c839006fb95cb61985200047f43e84b066200fe3620c520440019f441b8ac199087f2081324c5200072f992ca1968200bb6848c951440011fb0fb168288002b7a1b70cc9310066f208e6b1220009de87cc951cc001d38c721e849098fba18372581211747fc3ac9996601bbf0814c92044001f6684a0aa088002f360830d8d210063eb02eba0e6245dd9325c032540011f90cb9ca290073f160c6248510005724326490a20008ff8750d600c8019bae9b9ac4880023fa1f53d89100047ec00ecaa664009bf815d44350801d3ce9b1cc6900031fdd675583320053ec2cc69924000dd9745c332cc0019bce231e64900033de0576cc9100066f2a0e6b122000fd063cc740440014fd0b326c090802b760676cc9300063ebaec418a801cdd5219cc624400d1f90cb8e64900974f509758c9410055ec20a6b16600dabc86509315000d5f305ba2c0108027da1e42cc71010e77396c5b026200dd673cca5144037fa50618a4088002bde05628873007df9406e598a2000cde201cd62440f779b05318c69014fb684332d81310057cc04a8b00641ccbd629d062440011fd0e2a6c0908033e21970cc9100063e3aac498a2000af58118d5148001bd700b906290002b720d65d8d210055f424c6b0a4000cbf435c4635507b5db0e184c418802bee014258730005ed41e849822007cf47658951440018ff0abb6869020b735cb6398d2000572c08e0b106200bf083545204400173906aa28418803ae1d370589100056e41acb1922000adc835d162440019eaedb8e6588082dda1664485100dcfcc38c69022007dea82dc121480014fd06392cba0803ab55362509310057ac0ea0b086400adc8359163440015ef02b1663a000337dc073589100def910ae190a2000c7d7655032944014fd0b382c399002bb60863c85500066e39ac6b122000df175dc121440017b306312a0880035e14d700c9500057ac08e8b00642ff4e3259552cc8014ff0aa1ec29006ebde1d61185200047ec0eecaa24000abc845c560c845f9d8c5b92a688003976176398d200066eb1ae01968200c7f75591634407fd9cc5b126598003b3980634c9210047fc32e620e401cfc68318921440251ff0cb806518802be60053587300047fc32e521a2021cdd87cc961cc0afdaa2131e63900037a201720c5200063f192ea31a8200cbf845da314801f9e8ed31a82880027b60873551210053fc2a87b122000af9800c960d040197ee93a2c3900efcb196545092019df34148690e2029ecf31dc1620c401bb665b82628800237a1e634c910006773b6c91924216af686dc73244001a7ceb3a4c6900027e60372505200047fc3a87
  | 12 => 0x2b7a0e52587300057dc32849022000add8018d434840157b083aac59815ff488332cc510106ba3aaea90a20008ff825c764cc00197ce8b106398002b7a0e52d85300067a886e4b0e6000cbd7418c62440db5bd07b14c3980033be0976487300063ebaac93166000e3f5495161c800176b0221a85989c33ddc37158910006773b2c919242289fa86dc930440739ef0cb8865880f35b1d64258520005bcc28c5a022000cf5655c432c40018fccab8e65a082abea0273d85200065fc3ac83224200a7f85591634800176f08b12a28809f754c9710c951216cea12e610a8000e5d5218c32544019bc603b2439800337a1873509320e63fb12ea2122000b3d8599142440019b8e6a1ac390003ba082725803104d7d40664b044200dd473cc921440017e300192a2880023f60876551100053ec28c1b1a4200abc8359542d0401c7aa8a12c128802f960863485100e577414c6b122000c7f505c8635500157d0932ac4880034fe057510d420557c402e9b0a4000cbe32dd16244001bae43b9ac09081f3d1d962505100063eba8eab122085bcf864c921cc0015db05b2243980b27761b7350b321feaf992ea10e6000c3d435d463504019f301bb28488077dcd4d51481102c676b82c41966030de7615ca5348401b6908b8864a081ebea0364d81210072e3acc698e4000d5f751cd604847f97ec53a4c598002dce0951541100df79382c230a4000ee532d8521480015cb02106c4988029f6176358520154f7c12e1b1a421cfe06248520440ab9bae031c62900036bdd372581210066e39ec6b024200af9829cd600c4015bb0c29ec6908037ccc570c8510006f843a42a8220008fd821cd65500015db0529ec4a00023fa1e52d81310073632c41b126200ee78258461480011fb0e2a2c3990027e603724c5200053ec2cc6b0a4038cee625ca51cc0013bb0f99683988027d20d71909100052f42c6031a4200e3c8359542d040157b0931c429003b7ad89708c520006ed404e63122000dda309cc62440015eb0c21e62880029fe1543d8121004fc43aa89022000edb635c26348001be4e038e64880023f604765512000766310c61922000c7d75d9232440019bce1b1e64908023fe1973d05200b47f43cc2b066400be7825cd214400197e43ba2c488002bd60432d81510067c31ae120e401cdd5215cc62440015b906b2a64a00032fdd274587320072ebaec731a40008ff815c362550019bee631a429004abea0254580320063ebaac931a4000a7d8295063544013f10ea1a40880031fdd673589100067d900ecaa240008ff865ca51cc037af220bac82900038fd9454d91200557b408e8b064200cfb645c032440012fd0f192a9288023f21d4258231247e39826490a202aaf68114f62440011f90cb8c8498002faa1a42481100063fb2ae5b026207af4864c521
  | 13 => 0x6f2b94c418a2000c7c76dd531c80013ef0f994a2880032fdda5450f200053f42cc9b122000c7d7558760cc839b7284b8084880031f5d5620c7302d6e7b9ee4b1a4000df274dc520440019ea21bb2439805a3fa1e6558332005f8c0ce890220008fd87ccb60484011fb03b92c9980ff2f589748cb300056ec306031a4200cef20dc963440715dd0521ac528802fc60652d01100066f39ac420e60008ff815c063550796dd0b31c8490003671d373589100dff1410629022000de57218a51440014fb0ba0ac190832be20242580310063fbaec898a2000c7d76553329441f5ed0c3a66288002bd60450587320047ec06ed9908200ced20dc96344001fa0c6a8a6088003375db32107300053ec28c93166000cde76dd3324c4019dee4b12c398002b720d644c5210065fba4e9b12201ff5b5394f40440019f2c8b8043980031f5d562d05100067cb80e0b086400ced87d8b21440519f0ec312a088003f418f3154110006daba66418a2000c7d751d561cc00179d0732264908032f0857498d2022e5eb12e9192a000cee20dc963c40019eae238ac199003379d971cc9310047f43c84b046200e3f75dd1624400157908b1cc4880ef5b9d542185200e576412c6b122000cee205d831480019b8c7b9aa39006efc21c31481100de77b0ae418a4000cbf7458d60484859f6c4b8042a0002b7e09630cb41006ce3a6e6b0a40008fd87990634804b9d8e4b2262908337cdc57018d100047f430e6a922000bf3814cb40440377e102a9a40880031f59571ccb410047f43ec890e6000e3d5459564cc001d9d06382c418802b7608638c910056f9384c520a200dafa800c961cc0399dce7b1664880029f21531583210047ec36e6aa240009fb805c643440019eee338ac19907376cc9708c910004fb43ca890a2000bf18010d51440019bd0e31a62882135ed4b705532000756ba2c59968261fe2501892144001b9c41b9ac2900037ca0273485100047fc0ae1b12a600ed980ccb604c4011ff00b90c6a8872bba0b65d89100066e300e6b024200cde87ccb604c4395dd05a9ec488002bb60864189100febda96e0aa22000cf586dc542884015f30121ac110802be61d4258031315f3430c490a20008fe861cd42440293f100baa849906f3e619700c5200047ec30e6a162009af88050960884011ff0cb8c8729003375cc73583210071fb2a84a0a6207bf18288520440011fb003b2a8908027b60a73d05210053f42886b166000aed870c1620c415be4e13106288003b3e0f620c910005f8c04a798a2045af9809d560c84015bd0d9926288002bd6183254510127b829a82a822023d9f429ce42cc40f5f50131ac090802be60243d81520066e31ae399242008ff8759062440019f4e4b92c120803b3dcf725891000576c10ca3122000ee56418921440011ff00b88c6a9
  | 14 => 0x3805d521440011ff04b80c6aa0033318d720c5200e775430c49022000e6c65083624c4019ef02bb46488082dd2157348510006f9402e418a2000b79851d120440015bb01b1e64908023fa1c5158b30005f8c066490a2000cef205cb604c4019eb0db8a8418803b3dd93248730006f240ae521a4200af9861093044001af640ba8c890002bd60453589102163eb12ea10a8000ced725c663480013db05bb262900031fdd4735891018f56312a8a126200df2209ce21440015bb0431e6288002bba02439883100677c12ed18a4000cbd7619242440011fb0f328c4880976dd09710c9410066fa00e6b122000bf180dd331440011fb03b82c52a227b5c84634c5210053fc2ae8b064200abe8498961cc0015bb04180c6908033790073589100069ebaec93222000be98210d20440015db0421ac3900029f215631891000577414e8b0e601ccdf625cc624407fabe64bacc59804abea0053580320066e100e6b122000cef72d893144001aeaeb2106288003a750a630cb4100577c12c93166000af581d4b62440019de41b92c198802b7a0e64d81210047f438a6b168000cf9625c241cc001fc28490a4088003ab590648c9210069fb02ea21a8400cdc835d8324400176b08312a288002bbe09650c910006bd906eab2240009ef825db314807d5dd0429ac1990023fe1970cca210065fba0c6b122000cfb709816348439ecb0a3124288002dee15744811019ef5216e090a40008fe8715362440011fb0d39c8488002bea18424c1100047ec3ca0b08643eaec825c560cc8018feea31ac29000375a0f7150b310065f392c821e6000aed81d8a62cc00175b05a1a82900038fd525458b3016f56ba4873106200abd841c9608c4011fb0e2a2c219002bde0564985200055fc22c598a207dbcf8258c63480011ff0cb8064188031f5d5629073000774b9284b006200e9c7398d42d04018feeb31ac290087b318b324c510005b8c2c82902200fbf28090f31440397cd0421a428800367dd073589100b57d404cab066457cdd7098f31c80015b906b0a63900031fdd76358520007b9312a2a822000cef8758832cc0011ff0eb20c5980022fe1d64193320047ec0ced2126000cdc7018d43484013e906b94a2880033d18f71549210057dc32a5a022000a7d859d162440011fd0e2a2c598802af61052583310067b31ee2a92425acdf76d8932cc0399bec5398c4880027e60372551200063eb2ae99906200cf862dc15444001773083126088002b721b324c510004fbc3ac910a2000cfb201d943480016e30a18a40880abb9a067058831005ed41884982201cbe88259120440e19eae5b0cc2900027be1d420c7200047ec3ca0b0c6442db9425c021500019bb0239ac4880027be1d420c5200053f428e8b066477d78655c251480017cf04b2a4288052bea0332d813200
  | 15 => 0xba6c1990032fdd26358121005bac288798a2000c7d751d560c8401bd0c5b824288002afe117058a310047fc3ac420e6000cec205d831480018feebb1ac4880023fe1974cca210047fc02ed210621bcfa105d83148039bd50e312408802abda077358321006f3398c490a2000a7d8598361cc8015bd073a2c219002f320d644c9210047ec36e4a1a200ddf181dc13144001a7aeaa1682908023f61c54d85200dee698ae418a4000ecf6518d32484435bb0fb1e64908023fa1e40584320053ec2cc9b12201cced7618921440019f6e0202c5988037ae017210d200075721ac4a106200af9801d561cc0375e902b1ac2900031f18b755891029d6ec34e39966000a7e859d3604840177108b12a0880a7734c5720c7200047f438c6a928200cf9708826348497e5ea92a464908023f61c5358042005f9c0284a8a2020f575394d214400175b05a1a8390003dc10d51541100059ec2886a166407afa8099160484019bcc5b9ac48800337a1c6350d210e577410a6b122000a7e86080654c4015df04b1cc4880023fe1d63d8121005ebc0aa4996621cd3d425d442440a57ab0331a64880737c4817190910005f841a829022000f726454550440e39dee5b8ac4880037584073589100047ec3e86b122000e3f5495162cc4011ff00b8cc721002b720d75589100057cc0086b006400c7f75d9161480535d90c996c090833f8dc831481100047ec30e6a122000cbd655d06244037da863b0a62900033759773585200047f43860b0e64008fd87cc960904251f90cb8064988023f60676d0b301ad6fc3ac79944200af58110161cc8011f90e98ac1908be7761b7354b320047f438cab1660008fe87901628c4015eb03a96c0908033b5c220d8931005b6c2cc91924200ddb635c0324406997a8439ac321002bbe0971583320755e4328518a8000cfa625c241cc0811fd0f992c0188af7ad817210d200047fc32e52a6600aaec8650b61480017b106b2a6088003379cf63d852000775390e4b006200bf3814c95044037ceaeab08c290003b6a0c72580311feed992e010e6000cdc329db32440015eb0231a82900029f2154358b30004fd43886902201cd75215d46244001b3ee839ac290032bee04725803100576c14c93122000abf86551428c4015db0439ec488003f490d214c110004f743c64b0242008ff865ca43c40018fcc4bac839800373608735952100577c12e8b122000cef625c432440011fb0e204c7908023761f630c910006ddb22e02122016cf8865c332480016790ab20c8900023f6007358a5114e3fb0aeb20e4000ade809cc63484011fd0f286c2990033718d710c9100063eba8c610a8029cfa7698b4044001cbcedb2e64988031f989750c7300047ec08eca1a4000acc835c1620c4019f2cab8064a00027d6037150b310066fc1aed18a4000bf
  | 16 => 0x690b300047ec3886b0e4000cd4635c732484015ed0c21a42880ab3bd89720c5200067a316e2a1a207ccdf76d8d32480015ef0ca92428808bdc19731541100073632c4031262009fb805d5424c8014ff0ab1cc488003ad2116118520004f7c12e321a4200cdd7358b42cc0011ef0eb08c39800373083735852000576c14e8b0e60009f581ddb324400187aebb208688002eba1843509200072e310cb992621cfe2324852044055dce21382c4188027e60273909100072e32e65b02621cdea801c963440011fd0e29ec4880033d607764c91019d7dc02e2b006422b748558b3144001be702b8664880023fa1c5358b300061ebaac9a0e4200ade83d9763440019baa039ac488097754c9710c9410077539484b006200cbe645c3320c4019d841b92c7880031f9c96590c31004fbc3a8690a20008fe87d4d61c80019baec31c86908033de0576d0d21005ecc10c69822000aef825cd6244001f88c71924288003ba5c220d89310056f418e8b066400bf182cc520440015f309392c01898f3bdc36248510005db43684a0a202aaf681d4b62440eddaa2031862900035d5d46290510004fbc3a6490a2000b75858c941440a79baed9946398002afe0964d0730005f9c0ae69022000d6d325d443c84379f1013b062900039d5c5650ca41005f8c0064a0a2000cdc621cd514c001f32872a260880031fd537654b300b67d302e19944200eba405d1600c4019bb0c39aca90803375db3288730005ecc06c49966000e9c74dcd62440299f0e0b1285980523f60a73d8520004fac3cc728a2000bf382505304400177708b1260880ef5b1d5425852027eb7a82e529e4200cdf651cd61480011fb0c39aa890026fca0243885100063fb2ae01926200cbf655d06244001dcac4314a28801ebda1a7348510005ea41ac418a2000cbe7650b41cc0015eb0239ec290032bea0243580310057ac08a4b0e6000f1e5450d51cc0015df08b82c418803f8d8b704851014e3fb0aea18e4000bb9849cb304c0019baec31c64880023fe1d52587300056f418a8b0e6000ee970081620c4014fb0a21ac1990af79d857210d212a67b3b4c618a2000d7775dc56048401aeaea31062880029f61674d81210055ec24c630a4000cf662dc55344063f1864aa284990027de057290d100065eb2ee4a1e8200cf5655c4325041d9e8edb1a4288002b720d7058432007e999663a0220008fe86dc5424c0679bec1398c48806ebe60272580310047ec0eeca9a4000dd4531cd214407d3f30139ec890002b7e1d63cc9100b577410e8b0664149ed829cf65480019dce0b1284188835dd5172945100069ebaec82122000dd7811cd62440015df04b2c64a00023f60276d0d210053f428c8b0e6000bf08754520440014fd0a3a2c598003375db630c9100057cc06a4b122000eb8601d16048401b3a6
  | 17 => 0x24200de942dc121480435dd0429ac39901ebe20154587200047fc0ae431aa000cdc7218d314402dbe6c3b9260880037a909708c5200066f308e6b0a4000abd849946244037f630818a4088002bb60a63487400047e432e521a2000adc8650932cc0011fb01bb287290031f5d5640c7300053ec28c8b166000c7d709d6634800157908baac1908033790873589100065ebb6c820a4000db8645c241480397cd053224288003379c06390d210065eba0e8b166053ed710cc961cc001b6ee9b8ac4880029f6144358b3000774b18c49022036cf9205d841c80011ff0eb1063980023f61b725073000676b12e23166000aed82dcf624400197843ba2c48812bf894232485100053f42884b0e6000cbd65dd162440019bce5b1cc6880023f61c42587302867ab82c218e601cc7f625d462440535db0439ec0908cebba0843d81210063e32ae1b12622afe010d89214407fd9f0cb166598003f418d414c110004fcc06e4a8a4000bcd8290d214c04d9ea43b8ac9900035e551700c9500066fbb6c61922000cfb805da51480019f6c4b8664880033e18f70509101ddb742cc6a124000e3d6559154cc80157f08baac019002bd6065018d210de7b884ec18a40008fd87d4d60cc8014fb0a21ac488002af61372d81320065fba4e8b086400a7d851c562cc0295f100a16c09900379607724c5210057cc0665b0a4029af681d4b60484018f90abb4a4880abf8d836248510006f9282e598a20008fd870cb61500013eb0239a858804b3e981700ca310073642ac4312201baee829cf614807d9d8e5b1282980033b5897090831144fd436e4a822000cee70d89424c4011f90cb8c86900029f61662d87300047ec3cc720e401db7a851d120440018fec8ba86390003a7dd07358910005e641aa49924200c3d65dc943d04011fb0c39aa290003dcd0d5154110006dd902e931a4000daf645c84148001dab0331a6488003ae55142580310067cb2ae0192202dc7f725964308401a7ac8ba887908023fa1c63509510055fc22eab064200bb9849cd204400197c43ba2c4880032f5d17198d2000772b10c598a2000cde62dcd51cc0014fb0bb9ec29001f3ed877048510007d8a12a3a022000af581dd7614800157b0931ac6900023fa1f644c9101d57741087b0a4000af58118e215003dee0caa8a60880a77c94770485100066f39ced992a2009f580dc542884015eb0c19282880038fd92544c951006da908e8b122000af5811d5600c8018f8a7b82c5288fe7ee0173d8520004eec08e6a966400cdc7690d214c0011fb0f318c2900031f98975d0731004fac0eec9922000af980d4d60cc8013db0539ca890873f10c932485100066639ee4b12200caf1811c9600c4015f301a1ac1990035ed51700c95003c7ec3ec490a2000cde7358c62440693df0cb9063900023fe057
  | 18 => 0x4001b72e8b84c6900034f1d46450d200055fc22c5992203eecd6098b32cc0015eb0d9906288002ede11634851007df94008798a20158ff865c831cc0011ff00bb485288023fe0970d8d51005bbc2ae690a20009df8750c32cc0015df04a1ac5980023f61c63d09200047fc32e421a2000cee635cb41480019bc623b262900533e9c162ccb30105ba42a6290a20009f7815cb43484019dae0382c4188033d44073587200a57c402a9b0264008fd801d952cc401bd500b90639005a9fa1b75cc95006c7ec3e64b0e601b9f987d91204403baf4ebbaa4088002cfe055454942006bc3aee0b0a4000cf9725c063440019eac5b8a84188abba84270588310063e42ae231aa463fe080d8921440011fd0e21ec090802be60032580410055f420a4b066221aee82183624c4013bb0239aa999002afa1053583320066f438c698a4200bad8210164cc8016bd0b180c6908023f61e4018d2124eb632ae529a4200a7e821cd6510c011fb0f202c2190023fe057218d400057743c86b106200d3d53dc55450c018fac0ba88798802bda1b320c510006f9c02e21922000d3f805d443508019dc40b90c6880023f61f6488730006b7212ea18e4000aed87901620c47fd5ae9b14c5980029f6147458b302166eb12e610a8000e5f5394f6244063e5e42aa2a4a10033759473581210e774b82c43122021cec625c732440019de41b92c0188033e5c24018d210057bc0ac930e6000d6d75908314800197ae83a6c29019b37dc0634c5100056f418e8b0064009ef825d831480019dae0106c498802fce014348510004fdc02e520a4000af986d09204400197cecaa686880029f21563d81210047ec0ee0b108600dd7635c732484011fb0f996c2a00032fd9774589100367b3b0c598a2044aef87902620c4011fd0e312c398002afe096410f30006bbbaa8298a2000d7875dc162440479dce531e82908023f61a7394910007e9992a2982202aecf319c1620c4018feedbaa63900033e883764c9100de5eb0ce818a4000bbb8458d50440015bd07b2ec6908031f9c865d81310066f400e6b122000b3d848c951540011f90ea1ac190802be6027458910006babaa8418a2000cde635c032d04014fd0b3aac4880033ed95700c910004fb438c890a200fbf38158f40440011fd0f216c0988a73ea19700c52040f66b02c59966044ef121dd16008401cbea729ec2900ff2f50a7610b30004fac388690a2000df331dc121440018f8edbaa62900023f61c40587320e676396c498a20008fd809d843484011ff04bb086880033b5c87258031006f9b9242a822000a7d859c263c84019bae6318c2900023fa1f525873006df8c0cc7a022000cef62dc931480251fd0db9aa49001f7c9db7048510007e999662a822000dd9801cd624404d57b083aac5a0803571d773581210053fc2ac6b
  | 19 => 0x2eba0c645092031f723b6c490a2000c7c53dd952cc001adeebb92c090803378ca73d85420056e41ac4a922000a7d85dcd60c840f3eb0fb1a42880027e60273949100057cc2064b0062009f5870ca5144001ee264a8aa0880029fa1674d89100e577410cbb122020d74535ca51440019b8c6b9e83900027b60873551200063fb2ee0a12620dade839d161cc001be4e7b8242880036b1d13258121004ee43e64a8a60008fe8714162cc4015e90ca106288002bd61b32487100057ac08c720a4000aed821c3624c4018fea3bb2a598003371cf63589100066e31ee498a4200adf8758f32104297d30539a4088003751cf715812100676306e498a421bcfa109d831480135eb023a6c48815ff4a0332cc5100e6dc902e83122000cf7645c432544018faebb204398002fc6047448110006d739a85a0a4000dd9809cc62440019f0c6b8042a0002bee017458b3016f5731486a106200ee562dc5420c4015ef02996c090803791cc624851003e7cb16e090a201bafa869d12044001cbcebb1cc6900036dd9171d09211f4fcc04e7b2a4031cec62dc954440017d104b1e80880023f21d644c910005f8c0ee69022000d3d645d741c80015eb0339ac488073b30cb624c910004fbc02e219062008fe8710d62cc001fc6c4a8a408810b3e1d974481100066f31ae19908200cfb209d8314800f7e100a1a42880023fa1e634c5200067631ae5a0a4000abe82d9264cc0015eb03102c418803371cf63585200ddf840a869022000eea72509600c4015eb0221ac488003735cb32d073100775b82e0b1062008fd861cd54c800197ae9310c39806ebda0664585200066e310e6b12201bc7f615d461480011fb0c39a83900fe3fe1d62987300055e432a8a126200d9e54dc943cc0013ef0ea9a42880737c48570c85100057cc00a4b0086168fc8750d60cc839dc8c4b144288003b6d94634c110004dec00e6aa68400b7585d0521440397c904b2a4288073e9a1062485100047ec3c80b0c64009f9801cd2150001cf30a392c0188023f61c51583320061ebaac821660009bf805d443508013ef02b94a688002bde056248730196f5b02e52a24000cf762dc53244001cbea729ec09086f3e1d971481100057bc0ae7b024200cbc74dc562440011fb0fa1ec0908ab3e1db624c110004fcc04e6212201bcfb615c031480015eb02192c1288023f61e5018d21105bb42e8290a2043afb805d1600c8014fd0b31ac290003bae0162189100065e3a6e4b122000cbd7458861cc0011fb0f31882900033b5da420c520005dd420c4a8220008ff825d841cc001db2ca31a6088003ba5c070588310075dba2e8b00621cfa98418920440019f640bb482900031f1cb655053110d6e41eec98e4056cde7358861cc0011ff00b88c6a100379e057294d212166fb14e610a8000be982951204
  | 20 => 0x7ec38c690a2000c7f7518d434807fdcee2b124398002bda18320c510005e6c148690e6000add828c063484011fb0e21ac190802be60275d8520006f4406e4b1a2000cde76d8b324c4439dec9b9263908d72f5097690a310a66ebb2c5996600fdf27098e41440019f0803b2648801ebea004358910006ec31ee09924000dd6109cc62440011fb0f30ec1990031fdd5644c7211fecf992e91966000de6435c831440015b106b92c018803addd371589100066eb9cc620a40008ff8750961cc001978c3ba2c29006f9d9d561185200053e42ae2b00641ccdf325da3244001bb6c7b826490002be60075587200047fc3a86b0ca4008fd861cd5448439b72413a464880033ed91700c95013e9ea92e9192a2008fd829db41cc0015eb0231a42a80029f6144098d210eebc32ae12922000a7d8510d60c840f5f50132ac0908033b61f62989100947f436e690a40009f9809ce54440017ad0732662880023fa187354520006cf204e610a8000c9c741cd62440019bec839ac29010b6ed09700c9400063fbaec8b122000b9e830855450c0157b0931a4290002af61072580310078f98286aa4a200aed8290f625401fbe6e598a408818ff81c362485100dff1c12429022000a7d851d160c8401f6686a0a4088002be60051580320047ec08eca1aa400cfb655c0325000157f08b92c1108031f5d475587200065fb22e73224000a7f855d3614800157b0829ac199002b56063018d2103d7b40ce9b024200cdd75dcd6244001bb664b848398003ecd9151d01100056fc32a49966000c7d7558c62440015f301996c09884b76e0d700cb303766eb80c719220009f581dc953484018feeb31a86900ff2f5897498b300071fc02caa1e8200bda839493044001be102b866488002b7219544cb310de7c884ec18a402bcee625c843440011fb0f31884880027b6087355320006babaec818a20009f6839cd21440019bee0382c610802f3600634c921006f3902e418a2000c7f76dd53148001bca40b9062880031f2157118d5407df9c0ac6a822000cbf8759064cc8011ff02b80c6a90023f61b7254730006e7b9c84b0a4034fc76118d32484011fd0fb12648805677e197290f300055e422e6b122029df372dc121440011ff0eb286488002fc60242945100065fba2c6b0a400dbf18198d5044001d3ca831a86908027ea1e644c1100071fb24a8192a200cde7658f324400197ee03a2c4880023f6007650d5215577c12e0b146200c7e32dd562440015ef02b206390003ab6136250931005f943ca290220009dd801cd544c8559dd0f102c418802bb60a43587320e6da90ce83122028aee80881620c401abaeb99483980f7b3948634c9200055f420a6b1220008fe8718d42540014fb0a21ac3990023fa1f624c5400066f438c699240008fd878cb61500013f50fb2240880
  | 21 => 0x7618d214400157908b2ac2900023f61f640c9100066e906e6b122000b5c8355152cc80f5f100b1ac090803b358c62cc9100066f410e6b2a4200fe36248740440015bb06320c690002bee1172580310057dc0287b024200c7f855da42440259f4c0b80642080337c83735891000676ba2e431a4200c7d75d87414803797ec2ba062900033de1d610c7300057ac08a0b086434cee7218f414842d9f4e131c829008adda1443cc510004efc3a86316601cd79205d6324402b5bb0d21cc5980036ec8374585200057ac306520a2000d74545c4325441f9e8ed98a428800357dd47358520006eb880e6b024200bf181d0d204402d5f501322c19900357dd473589100063ebaec5a0a2000df3315c231480011fb0439aca88002eee1171481101fe3fb12ea216601ceea7058862440014fb0bb1ec290002afe1163d891000676ba6e0b10621bcf776d85214800dfc6c231240880033b0817218d1003df9404e690a200cafa80509600c4014fd0a21ac199002af61273d85200065fba0c6b024200f3954d0d5044001fc48418a40880031f9d762d051000576c06c52126200cdc709db324c4018fcebb0e82900037ad89700c9100067b886ed98e4000eea70883624c401bd284b8462900023f61c63c855010e76106e4b1a4200cf5645c43294401cf0ebb82c488002bde0562487400066e3b2c79922000cbf7499160484018fec9baa63900b6bee0a4358021004eec3cc99966000afb864cb40440011ff0cb866528802be21952481100047ec3c84b0e6000cbe76593424400157b0829ac4880031f9d561d83320075d21a84b006200c7d655c432d04015b906b128488002dd60420d95310747fc32e21966000dd6105cc6244001bb0c6b806488002fc60242cc510106bb3aeea90a2000cf7109cf614808be9864a9264a80029f2157158321005f8c006520a2000aed82d4d62cc001aeea0b8864a881e3f61f63d81210063e3aec498a2000ee581901620c4018f8ebb0a6290003b660332587300063e312ea18a80008fd8798861cc0519dae4300c6908873d1d973485100de76414ec18a401baf68119761480011fd0f202c4188037a90970945200057bc0ac998a40008fd82dc163d04019f6e1382c399072f9a0a6348510006f4b92e131a4000e3c8759542d04015bb013b664988031f995710cb410047ec06ecaa24200f7243545504407f9dce4b1463980038f5516250a51005f3c0ac89924200cdc764cb31480011fb0239ac990002afe11654c920006eb39e6390a20008fd87d9121cc00178b06312428805b3e18170cc93200677b94e4b0e60008fd87d4f614807fa7a84ba885980027e61c434811007ef9384c618a2014add8690d62cc001f50c92124088002b7a0e74589100059ec2886a124200cfb709c1628c401b5ce6a1683900031fdd5635812103c
  | 22 => 0x3a0c488002b761f6398d200057cc0664b048216cf8605c3324c4a75bf00b1e6488002af61061583320053f42886b122028aee809c1620c4015bb0da98c6908032f5957498d200047e432e5a1a202aaed819c1620c4018feeab0a63900033e941760c910006baba8c720a2000d3c825d44350801d38c721a84908b3375d974ccb31006f8b9ee29022000aed8298f21440018facab86652088f57cc97510b310056e41acab1a4233afb805c560c84019dc413b062900027760873545300055e422c6b12201df706554520440014fb0b31ec2900037cdd770485100047f436e4aa22024b768518941440015db0429ac019172f9e05658c9210065f3b28621a4000bf181d093044045e6ea92a662880029f61741d81210059ec28c8a1a4000ced76508314801d3ed0c39a8288002d7617624cb300056ec20e13184200cbf65dd160484015f30029ac019002afa10535873203d7d406a4b122000adc8359163480013eb0fa1a42880277cdca214811003ef9382c418a2000bcd8218c325442d7b100a1665980029f21564585200056fc3ac631a20008fd8718f42440019f4e4b92c01884b3e981700ca510057dc02a7b028400ade83151600c8019d8e1b1284988031f5d5648c9100053ec2ce8b0e6016cfb625c332480011ff0ea96c2a00023fe1d640cb3000556c2041b126200cdd7618c32440017d704b1e80880023f21d654c9100057ac308690a2000bd68318831440011fb0f216c098803dc98d5154110006ba31aea18a200097e83dc9545400197aecaa687908029fe1563d81210066fbb6c721a4200a7d8518163484259f4e031c82900863f61e638c7200047fc02e5b1aa2009f7874c431480019eac5b8aa5988027de1d310c7201fe77392c430e60298ff805cb63440017cd0f19242880038f5d1650cb410047e43a87b02a43acdf32dc5608c8013db05ba6639080337cc176ccb10006f9104e690a2009cf476d89514400157d0838ac5980031f18b7550d100065ea1ae231aa81eb7a8518930440014f90a98ec0908036d5d2620c5100055f424c7b0a4007df27058a41440011fb033b4a5980033e6017690720006d7ba6e4b0a4000cde641cd61480011fb05b82c3218563fa18735092000756c20e0b1062149ed829cf64480018feebba2c4880031fdd675d812106c7ec3ec5b02621cbe48258d21440019f2c8b8064880038fd5165d91200079a88286aa4a200ead8458a420c4014f90ab9ac48805afae097348110006b6baa8418e4000be88258d50440019bce6b1685981d6bb60a6348520005f9c12829022000cfb805d84348001fa664a0a60880023f60476549300ddf940e849022000d6d755083148085bb264b8064a00031fdd463589100047f43ec898a4200ee64258461480015bd06202c5988033b5db620c910006f331ae418a200ccf4
  | 23 => 0x541100e57ac0ce0b086400cdd64dcd6048401b6e43ba2c09087ede21562d01100047ec38c610a8000adc8058c63484018feeab2262880023fa1f61583320069ebaa85a0a4000bd48358951440011fb0f204c690872faa0b41481100075cb2ec9a022000a7d8599160484011ff0eb2c6488002af61053587320047ec06e4b1a20008fd87d0f62440197e50798a4088003748c07348510006f839ee090a2000aef8259032440015e302192c018802bd60762885402c767182c41966007af4815cf6048401fc6c490aa0882335d19771549210047fc3ac3b06648dd7750dc552cc439bd300392c68801ebea1b60581210de3eb0aea18a401ccef76d88324401b3eb0339ec8880023de1d61187320e5f5410c89022000c7d655c3320c4017e302212a0881778f508735944222fa7192a5992a000ade80dd263084bb9ba6439acb908273d1db62505100047ec38c7a124200c3d7559043c84017e10f98a4088003571d7735852014e6f98aed18e4000d3f751d1604847f5f700b9ac190802dee15624c110005f3c12c890a2000af5811496110c015dd01ba2c418802776047350b320057cc3c86b006200dd8401cd624400197eecaa28418802bb20174588310065eba4e431aa823cf4769cd2144001ab8ebb9ac4880033b9c162cc8310047ec30e6aa6423fcbd625d021cc037be50e38a40880037518d71cc921004fdc3aa890220008fe87d4f60484015bd05398c6880034f50975d07200067d906ecaa24000eb974509600c4011ff02bb687900031fdd663581210055e422eab122000cdd731cf61480015bf0eb18c690002bee0142582210047ec08ecaa26000aed829d16244001a790cba886a10c33b1897294d400066fb20e6b12200dafa8094d61cc001bcf02b90869080277e1d43d8b300065ec36e8b024200eeb729c9600c4015eb02202c219002bb60860189310066ec3ec731a4029aee871c1620c49fe5ea92a26590803795c9620c510007f1b12829022000cef62dc5424c4016f70a98a40880032f98974d8b30004f6c3cc721240008fd829cf6150001fc0c418a40880023fe1d43583210e6f910ae121220008fe8718d62440019bd0e31a64908367d60673d89100072f2a0c7192a200cdc635c432544018fb0c39aa92881ebe20143d812103d7d400cbb02423fcdd629cc21cc0015bb08298c690802b76103098c21006e7b9a84b0a4000abd82d9341440014fb0b320c488172bde0575587201ed6ec10e0b184242c7f625d632500015ef02b2442900eabde05705843210cfac0ce7b2a4200adc8158c634800157d0932ec4880732f589748c9100056ec1ec831a4000bb58110d42484013df04bb462900037c5c951d01100055e412c83222000d3d7550831500015bd06306c690892dd21563505100066f908e6b122000cbd745ca634803997ec5
  | 24 => 0x8641becd315c1620c4019bae639ec2a10ff3bdc162c87300057ac0ceab0e6000af9801cd61c80011fd0e29ac421803aed9764d011007e7c384c6a12200aafa8010d60c84895bb05204c6109172fd89748c9500053f42cc4b0e6000cfb645c021cc0014fb0a304c690802b7a1c73589100055ec16c9322206bcef70d8b3244001b7108b8064a0002fca0e41481100066ebb48610e60008ff805db43c84017e30129a4288002bb60863909100047f43cc6a122000d7721dd53148401bace631c82880030f591751933103df94048690a2000cdc7358d604841f7e100a1662880034f14c74595200e756216c4a122000cbf749d160cc8011fd0fa1ac390003abdd372589100dd76c14e0b106200abf8459561480018f8e7b12a2a807adea14424c1100e5f5414a89022000c7f75d89315000157b08382c418802be6024258031096763b0c6a124000c7c525cb65440395d904b1ec4880027ca1c31481100047f43c81b0a6400c7f759d560c840157b0829ac1908030f59574ccb41005f5c12c6a8220009f580dc54248401dd2c43168088002afa1053583210055ec24e531a2000cdd8718e32544015b906b2464880023f60a7694730004eec36e6aa66400ade8398163484014fd0a38ac019002b72096318d100047f43887b0a40009f683dc95144001fc6c5b8a40880038fd5254589100076b99663b026200aed82151600c801be700b8c8488003750c0734871000676b94e031a42008fe86dc5424c80157908b82c2190033794473589100047fc3a65b024200cf7815d921cc0013bb0039a84990031f9897510f31006eca1ae19966000d3d755d2634800197a43ba2c48801abe60873580210055ec20a6b0e841bcfa7658b40440377e503b9a408822b9b997654c921004ef43cc699220009fa8794d20440397cd0db124288002b760f42583320056f41ec9b1a203bd6c655ca54480015bb0231e649001efca0274485102c767102c631a4000df3615c221480015ef0c9924288003371c0634c92100677b22e418a4000c7d75d9262cc00197ee9322c19906f1f58575905200053ec288031a421cdbb425c242440015db0121ac41885b3b1da63509200061eb2ee4a1886008fd87d4961cc0019bce6b1cc4880034f5d542d05100065eba0e9b1220008fe861cd5448401b98e7b92c090803378c376487300071f216caa1262009f5821cd41440011fb0fb2664880031fdd6634c72000676c06e4b1a20008fd80dd9548c8011fb0e21ec0908029f61674587200057ac0c80b106200b7785589414400137b0fb20848805b7cd8570cc9101ad7741060b1462008fd87d9231480011ff0eb168398002bd60473d85421557cc00e7b122035cf9205da31c8001ba8a639a82880023fe1d65cc9400053ec2884b0e603faee8299162cc00157b03b268490003dc58951
  | 25 => 0xc019bce7b18c4880032fe117694910006f4a12e128a4000cde87ccb614c0259f4c0b8065a08023f61f53589100056e41ae2b0064009f7805c432544019f080b8ec099002be60374587200063ebaac818a4000adc8654b324c0013ef0eb24a28800337d937358121004fdc02e598a4021cec62dc931440013f700b8e648800337dd073589100e6ed992e01922000af58114f624404bb6a84b8864a08033edc210587320047ec30e6a144200dd6831cd21c407f97ac53a4659811fcbd465450b200667db12e018a4000a7e851d36148077e5ea32a284900033b1cf72589100053f428e0b086434eea80081620c4379eaec30a4290003ae90174580210053fc2ac899240008fc8750d61c80015f301b9ec0908023fa1c545832114e7b882ec18e4000daf645cb41484199f4c4b8063900023fa1e525873000567418e0b106200af58194162cc4015eb03202c2190023fe017218d5416e76312e521aa070cf570dd921c40019dd0fb1664880034f5d764d05100057ac0ce131e4200cf710dc5600c80173906aa28518803b950961185200063f438eab1220008fe87ccb604c401c7acaba665a084b6ed91700c940006ea39886a8a2000be78258d21440015f308392c018802fc603320c5100046fc3ac631a2000a7f8558d62440011ff0ea1ec4a8002f36085318d2114e76c12ec18e4000e78601d5604840157f02aa2c5a18b33b98b7250f301ad6f418e0b146200cde8798d3244037f650818a40880d3b360c20588313ce77b90c6b0a4000d5d7590c21cc0017e50690e80880027721d4354730006edb9ee0b122007df181dc121440015eb0229ac2190027ee01720c5203bebdaa2e128a4058ecc2058c6348001f30c921a608806e3f6017218d1031ff1186c490a2000d7b20dd531480014f90aa1ac4880033b591720c720006bdc2ae0192a000cde601cd604840157b05b208688003b3e0d62189100757d40484b046200d7775dc56244001af10ab8064a8002bb60620d89310df3b28ea2b064200ecf62ccb31440015eb0231a42a00029fa14435873200576c06c4a126200df061dc121480013ef0eb08c290003cd95143545100057d43a84b006200af980cc9609442dbd704b866490003736087358121004fac3cc520a2000cdd64dcd61480015bb09b84c6108033ba03764c832007f0a10629022023d9d429ce42cc41f77100a1662a00023fe197390520006f1402e418a2000e5f3259432904014fd0ba0ec0908abf8e03624851000576c10c690aa042aee8294f62500015f30f992c1208029fa166418910006edb9ee0b0a400fbf2801cb31440019bd0439ac4880023fa1f65589100edbd42ee690220008ff874cb6150001af4a6b8064a80034fd4474595200057bc0ae8b0e60008fe8718d42440014fd0a38ac59800397dd473589100047ec3880b0
  | 26 => 0x22fe1d64191102b7e91026598a2000e3e42595420c4019eec8b886488026fc2014288510036f9b90e290220099ef825c76448001aeaeb9906288002be60352d89100de7a38ac49922000ade839d562440013ef02bb6648809b3b18b715093118f57312a8a106200cec70589420c4295f50029ac598087baa0020d893100576c1486b1062008fd87d4960d040157b093b243980033b5d1620c83122e76396c4a0aa000de7305c831440019ba8039ac488002bb60863c85400057ac08a7b02423fc7d625d632cc0017e30121ca288003ba081725803100775b92e4b006200cbc749cd62440195f302392c018802be60352d852000796aa2a4a166400dd4734c921440015ef00b08c3990036de11710c94110f66c1841b126200be98219120440755dd0429ec290002e7a0e5450b300047fc12ed28e6000bf1809d121440393f10eb1a40880023fa1c43587300047fc3a86b122029ced82dc1620c401cb8ebb9ac4880036bd9172d0d200047f438c2b066428ee6811c1620c4015eb03b20c2900038f55143d895023f9629ca8a164000ee962189504400197ce3b268490002af6105358b411efe4100c69924000e3f5495161cc8015b906a8ec098852fa201524c92000677382e0b106200af984dc9600c40157b0c21a84880023fe1d43d8910004ee41aeaa126453cdd7098d31c80013ef0f99482880035b5d57298d200047f438a8b0e4053cdf7098d31c80011fb0db9aa3900029fe1562cc91000677c32e521e4200d3d645d443c800157d0939ac1908033be09760c52000576c10c6312201df72755452044001dd6c631240880031f5d564187320e577416c7b122000a7e85d0560c8401bd700b968290002f960a4348510207e4106c69924000e3f8259543d04d1fa081b1e6288002b761f6398d210057ac0ca131a4200cb5645c4320c4015ef0ca1662880033b59272187300053ec2cc831a4200aef87901620c4399be64bb06488002b7e116318d2103e7c382c4a1220008fc8759131480018f8c7baa63900036b9d17298d200064fba6e6b122000bd5810c0634840197ee93a2c0190023fa1e42d85300047ec3cc83166000acd8214c6348401ce90ab08c2900026fa0f7155342005ae41aa9992a000cf581dd943484019b8e031a6290802afa0f64d09210ac7f430e690a4000d6d325d741484019d8413b0629004b5ed95700c9500a57d400e2b166000df2201cd21440014fd0a21ac190802b7a0c52587301a73742840b10623fd9f325d262cc0016eb0a21a42880034f1d7745812100773318c490a2012afa80551600c8011ff0eb14839807fdcd4951d01100047ec0ced2926000a7c8550d60cc8539f500bb0639006e3f61c63d85200047e43a87b0242009fa8794930440014fd0b39ec29004ab760c745803215e6e990e6b2642008ff805c76250
  | 27 => 0xc43a849822064eea3058862440015cb03382c4188027e61e53481100047f43ec8b122021e6e85083624c4011fb0039ac52a003751ce43485100063f32ae3b2a40008fd87d903148015fc6e5b8a40880033708473589100057dc02a9b02641cbea82d0d20440139dd0fb12428810b6750a7308540004f6c10e6a0e403dcdf76dc932cc0013db0439a8290026ee20142885400047f438c6a9280008fe87d0f61480675df00b10c488002b7a1b74cc931006f8202e21922000abd849cb604c41b5f500196c098802be6004358b300047fc3aca1928000cbe765534244039fc3003124288002b7a0c705883100676c3ec59922029aee87081620c4017a906b1282880023fa1c43584320567b43ee2b12207dcdf709db324c0675dd0429ec090803375927308730005dac0880b266400e3f5495160cc8015f50539ac018802f620d644c1100047ec3887b122000be4864c9214405bc7a84b2c86108023f60276cc931006f3b96e2b0242008fd8714d61c80016b906a9664a8003bce0161185200047ec3c80b146200cbd7619241480699f240bb063900023fe1d648c9100357d40486b00423aaef815886244045ee6a998aa0880febbe1d62c87300047ec38c620a4000dda20dcd6244001fc0c5b824288002bee0171583320065fbb4a8a1e4200cde211cd6244001a7aa9b82a6a10031fdd563585200057cc06a2b0064008fe8714161cc8011ff00b96c6a088f6750a7310b310063ebacc630a40008fd87d973244001daec731aa2880033719073589100047f43ec8b1a4000eda731cd60084019dac4b8065a0802ed61071cc9100071faa4a8b064200c7e655c0320c4019b8c13b664988023f60a7610d100056e41acab1a4000af581d51610c8e99bae131e65880031fdd4635812100775b12e19922000bf18010951440699e8ec39a4288002b7e0163cc841005ec41ac49822000af78150b614c801b7708b8042a00af3e4817610f20005f941a42a822000afa87909600c401aeaeb9948288002bb60b43d89100047ec16e2b2660008ff865c841cc037de50d10a40880033958b715083100576c06e8b106200cde861cd544c839ed50a31240880032f59774585200047f43c81b126209deb825c221480015ef02ba2c3991b7375c3630c9100055fc32a8a166429cdf315d831c806797e85b82c321002fc604435411000772c0ce0b106200d9c741cd604841f7e5019966288002d720d54cca510047ec38a4b0e6000dd473d0d51440011f90eb126488003f2d8b324c1100057dc02a8b0e40008fd811d9544c837de2e0b08c290002bd60672d81310067bc3ac230a4000abd849d56244041ee0ca90aa088002f56063018d2100576c10c6a922000afa839c960904013f50fa0a408815fb5c4263cc72015774884e0b106266add819cc6344001be6e4a8a608800
  | 28 => 0x18921440019dae4b1463980a3f804062485100053ec2ce7b0a4000eeb70881620c401ba8e7b8ac4880029fa1674589100053ec2886b086400fb06450550440395d904b22c488002af6135158b410063f316ea98a200dafa8018b604c4018faebb20c290002be6005458032006ea39e6490e204aee8608c9604847f5d904b22c598002bd60674589100065ebb2a9a166256ade831c562cc0014ff0aa1ac019002bd60675d81210065f396c9a0a2000df270dc7324401b5bd07392c398002afe1942d0730006f5c12e118a403fd5d325d662cc039b6a84b88848804abea0051580321a75742040b106200af7814cb61540014fb0b320c688002bee0152d81420056d418e4b006200adf8355263c80015eb03b1242981275bd417294d210057ac0cc530e6000de4865c83144001d9ac631c84900032f5db6410d100657cc0ee4b006200af581901618c8014f90aa1ac19081f3e9c162cc910006ae39c64a8aa01bd7b515c25148001b5ceca1682901f7b684276cc9300055fc22e6b122000a7d8510f6148001753083124088002fce0574481100067cb22e018e4000aed8290d610c8011fd0db9282980029f61632d85402177890ae8b004200cdc635c23254415be6c2b8642880033b98d72d05211ee6e990e6b064206fe18118920440019ba60b90c6880ffb360d6218b300063fbaac498e6023cbf429da42cc44bbc8e4a0a629081f3ea1b70485100047ec3c8131e42008bf8759064480019bcc4b9e83980030f5d564d07300066fb9ce7b1220009f4835c642c40015f300196c2a000237e1d6318d210073bbaee2b12202def12190d600840197ac8b8885980036d08774581210057bc328510a207fe6e65d9642480197e501210628800376a1f324c1100065e3a4c6b0a4000c7e655c032904014fb0a38ac019002d7a0c20d95310056641ac43122000af6860c951440017e303a124088002bde0553583210067d286e2b006400cdd74d8e634844db9865b8a84990033e5c070d89310dd76c3ec590a2000aed8210d60cc8015eb03106c299032be20142580310047ec06e2b14a828afa829c9600c40fbe243b8242880031f5d463185200047f438c698a4000de5805c831440011fd0e186c4988039b080651893122677396c818a4000fe3629052044001c7aa9b2ec8880032f5917110f320056e432a5992621db788558d2044039cdca5a96c4880c72f50b76552320047fc32e72a64000f714354550440019b88239ac4880037c201710c91000576c048731062008fd87d4f60484015eb032a2c219003dc10951541100076db9ee0b122000daf748c96048491fc08099242880033b5cb62d8131005eac08a7b1a4200adf835c560c84011fd0fa1ec4880032f98b74589100ddf840aea9022000bf18090f31440019f6e1102c5188034f5537054942004f
  | 29 => 0x948690073f8a00624851024eb63aa64b024235cee625ca31cc0d3ceccbb2a828802a7de0572d9110006aebac873166000cf7815d8324404fd9864b2a64908023f21d52583310067db22e018a4000bd68318951440c1cf4cbb2a608805aee20142cc9400066fb22e63122000cf97018363484017e30121c42880023f60a73d911010f5742041b126245d7b525c03254001bcf02b9682908023fe1d65cc9100065fb24e73222000edb320c96090401abaeaa1ec598003bc604325824100576c10c790a2021aee820c161cc8015b906b2c64a08038fd525458331006ebb1ae219220008fd829cf654406f9be64bb065208037c101718c9100063fbaac8b122000cdd801cd62440019bec9398c488002be60332582310067cb16e0a166000abc8655142cc4018fecab8c8498802bb60854587200053ec28c8b0a4000ee870881620c4015db05ba6c4880a6bee017258231004fbc02e21928228cef865c831c80011fb0f296c0989cf37dc163ccb100066e980e6b064200abd8498b61cc001bae42b9cc8908035b4c97510d210e6bba92e329220008ff805d843c84015db053aac5980033b9da420c52000576c1086b122000dd8409cc62440014fb0a21ec09080337d94735891000677906e4b04625dcdd321cd65c81059bee1bb265980039b4c95458a510065ec22ed2106200d77545c432944013bd0fb2a8798002af612634c920006bd906eab0a4000cbd655d262cc00197ec8b9e84900031f1d772589100053fc2ac8b0a4000cbc741cd62440015eb0c192a3881df5e14d7094520006f9c0ae01922029afb805c9600c4011fb023b2a5980033dc847654d210046ec38c61922000cbd7655342cc0018f8ebb8ac4880033bdc220588310957d40686b0064008fd8715162440013f30039aa488002af60463509400067b886e4b0e6000cf9709826348401adeebb92c2900029f2157358720006ed438c69822000af98014d62cc00197aecaa68790002fc20d21d011000576c10c6a122000aad84081620c4395d904a1ec4880ff67cc974087300053ec2887b122000aed8214d61c80195f501992c018802dee1571481100053ec2ce531a202aee760d8921440137e50199442882035e19770549200dd7ac3ec310a4000bd68390b314400f7e50021a4288002be60275589100057bc32e890e2000cde301cd61c803797ec33a062900efcb14e5450920007f1212a290220008fd8718f41440018faebb18c488002be60372d81310053ec28c031a42009f982dc131440011fd0f202c399003759cf32905100047fc32e5a1a203dadf821c163084019f065b82caa10033ba19720c5400076cb18c6a822000aed82d8c62440013eb03b9286908032fdda43508310057cc0664b0e6000cbc7418d61480018f90abb4a2900033759473589100e4fd43cc89022028fe36
  | 30 => 0x45100053ec2ec731a4012df2700c831440259f4c0b806418802ee60243d09100059ec2886a124000c7e62dd531cc001b9ec6b94869083a3fa187348510006d6baa85a0e40009bd811cd54d08015eb03382c3990023f60b7654d10096f93806520a2027d77525c4325440167f04a1aa928802e761370cc931055f9c0ac49822000cbd705d2634807f97e853b48598002cf61020d9531007e9180e690a203fcbd629d021cc0011fb0e2a2c398002afe096410b30006f9b92829822000bdb8358b404400197ae83a2c390003b3d90634c9210047f436e4aa26209deb625c22148001b9ec6b90629001efc60662d01100febc32ee0aa22000d5e325d760cc801fc0c4a8a40880033ed8b7048510006dbb22e22122000b5e83080654c4019f6e3b82c48800379611720c5100047ec36e6a8a4000c5c751cd62440013bb0fb186488002afa10535843203ef9b924290220219f581dc931484011fb043b2a9980027760373553320066f380c7992422acee865c83148001cbca831864a8802fce0553d01100047ec00ecaa264009f7875903144001bb041b9ac2900033e591700cb3015577c12e0b106200c7d7518c42440011fd0fa12c39801efc20173485100056f41e84b066400af58110f62440019f2e1084c7908026fa1c21551430065eba4c931a42008fe8714d60c847f9db0d3906398002ee2116354110005f8c04a598a2016afa8098560cc8015db0532cc5980a33e1d8624c1100065fb22e53266000a7e851d160c845b9dcc4b948728802f560c62545100065fbb086a1660168fe87d4d60cc87d3f30139ec290002fce0543481100967d302e01948242af9809d1600c8014ff0ab9ac48800375d8d710c951004fd43cc49822000abd848cb6054401978c43a2c48800277e1d32d87300053f41ee4b2e8200bd98290d30440013f10eaa260880031fdd7614c5400dd7b408c9b0a4000cbd7419063484019f2e1106c4988027d61e63485101567c3b6c49022000d3d425d443c80016f30b322608806f3e1db7148110007e899663a022000bf38058d2144001aeaeab206288002cf61443509100063fb80eab1220008fd8758a41cc0011fb0f212c128802be60243580310071fc0acaa168200af5810c960904559dee3b1242880029fa1663d85200a56f41ce8b1660008fd8718d2150001be2ebb8a4088002af21942d0510006ec202e63122000cf8205d83148037be062b8642880023f60776553200057ac0886b086400eaf62509414c4015bd0dbae6498002b7e1d6318d210057c432649022000bd78150b32cc401cbca8298c690802ed60654509100047fc02ed9948200cf5101d9214c0019beca39ac0908863f60673d912100676304ed1924200af581d892154001a7aeaa1683980036d5d2630c5100067b886ec90e6006afb821cd60084013f700b
  | 31 => 0xa27ee6e65d954248001ba8e731aa2880ff67cca748cb300047ec3864b008200cde709db324c4395df0eb10c4880033718473585200047f438a8b086400fe232dc121440014b90ab18c6908031f21576105200047ec3cc631220008fc8758931440371fb0fb1ec2900033bdc020588310065eb22e221e600fbf08055331440478fec4ba885988031f5d475587320053ec2ce5b026200c7f759d5600c801ba82039ac48814eb760663cc9100057c41ae8b0042008fe86dc9514c0015bd07212c19886f7c61c314811000796aa2a4a124200be58299121440155f50021ec2900023f61f53587200066e186ec90e6000c7d7518f4148039bcd0e3124288026bea0352d89100057ac0ec490a80009be8710f61508155f501a96c2900032f1d843509101d66f996e2b006400a7e86883654c4011fb0e2a2c190893dcd49415411030ff0380c490a2000adc835c960884016f30a21260880736d485748c91000677b94e4b0062008fd8718e42544014fb0bb18c6900023fe057218d541a67743840b106200adc8359163484015bd073a2c390112b7e0a4058c21005ebc02e39966200b79800c951540011df0eb10c5980032f1da6450910117b829e62a822009afa8010f6244001bb486b804398082dda14434851000676b90c5b026200af58110f60484375e902a9ac190803ae61072580310e6f2c08e4b1a20008fd8758b41cc00197908bb064880029fe1573d89100072fb28a7b1a42008fd8798f60484018fa64ba8c6a08023fe097118d540057bc0ae6b122000cbd741936048401b6ae8b106288002dee1563d01102169ea12eb1928000bb48458d21440011ff00bb686909ef375c0634c9200047f43886b122000bf1809933144001abaeb9968398803798407258d100063f428eca922000ced625c0320c4011ff0eb2e64a0803b559763cc510006e631ae418a4000db474dc56048439be242b8484880023f21d644c521216dca12e01928000e5d5218e32544015f50539ac120802eba1a54509200dfb8c28629022000cbd745c463550255f501a9ac0190033b2037258d1000677382ed994640fabc8650b315000157d0829ec290002f3e094358b300061ebaac821e641caee8299562440011ff04bb68688002fc20d21541100057cc20e6b00421ccec825d832440015db0521ac588003371cd63585201fde7c3a6590e6007aee829d3604840157d0829ec488002bde056448520006eb90ee6b2a421bcf772d8521480013bb0239aa4990ffab9d36298b30005d6c1081b224200abd861036448401b5b08b9062a00023fa1c535891004df44028510a4000d7721dd560484018feeaba2c4880032f5d7745891000766c18e0b1062008fe870c961cc0019dc40bb06390002ee61232541100063ebacc7a0a401baf8865d520440011fb03bb287900027de1d629
  | 32 => 0x157908b2ec290002bd60640d85320063ebaec83122000c7c625d741440011ff00b8ec4aa0023fa1f6358121006ed900e6b0a40008ff805db3294401adc85baa63900029f61474580320047f438a8b0e64009dd801cd52cc801bb42039ac290133f888332885102166eb14e610a8000bd8835c5204406b9bd0f31a6390026bd60475d89100047e43a87b0aa434ece5218d32484011fd0e31aa4880023fe017118d541079baa4a890a2000d9f74dcd60484011ff02bb0869001efc20131485101f65fa12e131c8409af581dcf62440011fb0f992c1288736dd0971909100065eba0e8b06427bcdf7018d324800d5f705ba2c0108033dc417198d200076bc1ac230a4000db864dc142480011ff0eb22439800337a0d76087300055fc22c63122000cbd645c464cc0015eb03104c71081a7d21972cc5100065f392c832660009dd811cd544c80157b0829ec488097ab189425053116f5ca1486b004200dad7550b41480559f6e3b92c01881efc606625411014e7c3b4c4a82202a9f887d8930440579ba6439ac9900033e5c0705873233fe8200c798a2000d3d435d741c84559dae5300c690803dc0c951541100055ec24c6b0a4000bd68310b31440018faebb1cc6900033ee02760c5200076bb2ec798a2000d2d7550b41c800157b0829ec2900032fdda5450b311feaf992eb1966000af987909600c4016eb0b3a2428800277e1973087300067ab2ae21922000afa86d0920440015eb0231ca290003b358c63509200056fc3ac61968200c7d75d9363480015f704ba2c0188023f61e40588310057ac08a8b0864009f78758a4144001d3d0831c64a884abea0354580320047ec38c7a0a4200afb805d162440014fb0a202c59885abe201545833203df943ee090a2000bf287cc520440011fb05b82c72a0027e6037254d203b76b880c618a4000af6860c941440013f301b92a68800337dd7735891000737428e0b106200c7f855da31480375f301392c1188033799073581210047fc12e1b1a820aaed821d3614807d5dd042a2c1990033e5c872580310e6f890ae11922000d2d7550b41480014fd0a322c2900039bdd772589100067bb8ac2b066442eb9425d16008401db0c1b9ac0908037514c73487100047ec08e6b14a800cf862dc14344001a7aebb208688003795c8320c510005dac0886a122000aed8214562cc001b5843ba2c0908027de057290f100069eb22eba0e62008fd81dd954cc0017e106a8e80880fb375d970ccb3100677306e498a4200abe8414f604840179f04a1cc598002ed61062945100051ec28c6a128200db7645c65444001da8e7b8ac488002bde0542d8530007e899662a822000c5c651cd6548429bd6c5b8264900036b88774581210057cc00a6b008400a7f855c1610c8015db0421ac3990033d98f7150a210047ec06eca14
  | 33 => 0x3f61873485100047ec08eca9a4000a7c8558e624401b5f501b16c0988035b9d57298d200047ec3ec810e6000bf1800ca51440015f30f992c0188027ee01734852011fe41026598a401cde8625c0324400157908b1ec488073ab5d16218910005d6c0ca8a124000cdc7118d32480019dae4b0e83900023f61b7150b300066f41ced9922000abd8414f60484015bb073aac4880023f60276d0b31006f9400e690a20008fd8784263c8401d5d08382c418802be6005158b300057cc1486b006200bdb83589504407d5db01b14c5980021f61873552510047fc12e231a8000af5819d161cc8019f2e0306c4988277a209708852004ef9386c418a2000dda501cd62440011fd0e292c398002f5a0c62505100dd7b408c7b0a4000aed821026348401be703b9260880029fe1573d81210066f314e7a0e60008fd80dd953908018f8cab80c498882dd21543485100047ec3cc620e4000adc8650b324c0019b8c9398c4880d33ba09760c72000677ba2e0b1062008ff8759061cc0d59dae1b106488002ab610705883138772c16c290a40008ff8758c62440019ecec38e64880037548773589100047fc3ac990e601ff735354740440012f90eaa264a80023fe1d62947300047ec16ecaa66000cfa105cb604c40d9e8ec312a2880873d8857198e42005f8c0664a8a20008fd8794b61500019eaec38e64880034fdd474589100066eb20e6b122000fd243545304404b8fec4bac64a0802b7a0c40587320063ebaec931a4012cfb615c03244001b98e7b92c290002b32096318d100047f438a9b0a4000b5c8355132540377e50221a40880033dd95710c9100069fba8e8b0a4009df270d8a414404fdc8c4a8a4288002f6a0c624c1100047ec3e85b0a4000cbd7498c624405397a82bb083900033ee01760c5201ffa6c2cc59966000cde329db324400197ced21e84880032f0cb74595200069fbaa8498a8000bf38254530440015eb0c1928388002bb6085058b310069f2a6e4a1aa200dd7211cd65485039dae0b94c6900febba0b4358b300063ebaac3a0e606ccdd7018c32440399d8c4bb06488002af6107158b301477340840b10621be7651d4761480019f4c5b82a88800277e1973c8730007f0a12a290220009fb825c031c807f5dd0428ac598003f818921d0110005eac00649886200d6f759093148001978ed2a28688003b3590634c9210063f3aac3a0e6000be98298d204400179b04180c690802ed61062cc5100065fba2e6b122000c7f855c46348001d9ac59926398002afe11624c9100057ac0860b106200cf9701c1620c43d6f50b32260880a6bda04435872010e6ebb2e399660008fe87d9131480013f30139e84880029f21564d852000572c0c80b106200bd48358a4144001b98e7b12c4880ff2f58a7498b300047f43e86b122000e9d74d8e63480
  | 34 => 0xc3ac631a4200e3d4259432d04011fd0e32ac488002ed21162545100067b880e6b0e4000dd47350d214400173906aa685990022fe1d6410b3004e7c386c490a20009fb805c43244001fc0c4a0a4088002e761053d8d210de3fb0aea18a401bafa869cd2044001c7ea92a2c2190023fe19700ca511fee739665a0e6024b76858c941440019deec31664880032f5d161d83320567c386c290a4000a7d8518560cc8013f50f21a40880031fdcb65505310056ec08a631a4200e3d7455162944014f906aa2c528802bd21952cc51015ee7908e6a126400cfb70841610c8019dee0382c418802b7a1b32cc51000767b1ae531a408cd7750dc552484014fd0b3a2c398003ae21172582410053ec2ce4b0e6000af5810c1610c8018f8cab96c098896f9606648c9210076c184e6b004200cdf7318d414807fbe242b8043980f2dba176390920005f4c16829022000f736254550440019dce7b1242880027da1e52cc5100066eb2ce63122034cec205d831c80014fb0bb12c398003aea1072580310055f424ca3122021cbf425c6639083997ac4ba0c4880ff1fd8975087300053e432a8a926400adf8758f3290401b58e9b92c090803ecd09414c11000576c10e8b066400d3e755d263480017e3003a66288002b721954cc93000676b16e0a106216cfa605c33248401bb0c6b86649006b4f61073551520066eba0e6b1220008df8758c634807f9f441b82c790802b7e08638c9100053ec28e2b066400adf8758f32c40015eb0c194a2880d3b3a0c2058831005f8c106290220009dd821cd51cc063b9864baa849914f3761f32d8131004efc12e620e6000aed8790d620c4011fb01bb2a9990032f5917210f32136f5b02e5a0a4000add848c06348401bcae5b1062880d63fa1c63485100071e412caa1e8221ee681083624c4eb5db0531ac2900727d21d6348510006dbb22e221a200e8fe870c9608c40175b032a285900039720d65ccb410056e432a89966012cfb655c032540019dc41b92c398002b7219524cb300053f428c8b166000cee80dc96344001dd0c831240880033bdca72d81310055f41ec9a124000ead64191324840176f08b14a288002af61053584320e65fb12e91922045d3d525d232540013df0eb1c84900037c88172cc510007f1216e29022000df040dc5324400157d0832ac398002dde15634851003e7db16e090a4000a7e8510f6244001c7eeaaa6c4a1803975535318d210047f43ec898a20008ff865c643480014fd0a21ac21900376d8d70cc920006afbae6498e6042ced869c831500011fb043b2a8988033b9d9420c520005ea41acb98a2000cfb809da41480018beebb9ac488097e30c9424c9410053f42887b0a401ceeb76d8920440395dd042a2c4880023fa1c43d89100047e43a87b0a40008fc8759532500019f2e1300c399072
  | 35 => 0x5c663948018f90ab88c6900031f5d57498d200053ec2cc9b02421ed7b525c2534400173b05324879800337dcf72589100065f3b287a0a4026cec635cb41c8401d5f08b10c4880033d98b7150d10005ae41aa8a926400aed8299662440395f30138ac019003379cd7218d10006ea31ae21922000b79859912044001bd6e5b1260880038f5947350b410047ec10eca1a20009f7805c43290401d98e7b92c48809b79d8572d0521007f0316e29022021aee8215161cc80157f08b2ec2900036ec41741891000678b0ae018e6000aed82dd762440013f303b8264900031f18b754c5400071fba8e8b122000b7b8550d204400f1fb0e326c0908732f58a748c91014d7b408a6b0e4000cef86dc963440e39eae1b0c4290003371007358910005b6c2cc89924200c7f75d9131484019be61b92c7880023fe0570d894323eb7a8ae52a64025c7d625d63250401aeaeb31482880033ee0176905200063eba8c63122029fe372dc1214400157b08292c3980030f59175d0731005eac10c798a2000fd363cc5204406b9ef0cb88641880375e0673189100056e41ac899240008fc8759131c8401adeeb192c0908027da1f43485100063eb2ae81906200cf9805d831c80555ef04b08c29006f3ed8570905200047f438c8b0e6000cdd211cd624400197f0eba4c6900033b98d72d07200047ec3ec990a2000cdf659cc62440017ab0631282880027ee0172951200047e43a86b1220009df8750f21cc0014ff0ab82c3210023f61c53584420057cc16e8b006200ee96518920440017b700a166598002dc20d51541100066e39ac2a8e60009f48758b3144001b98c7b926290802be61b32481100057ac306598a20008fd81dd943480017e50638a40880023fa1c42583310053fc2a86b0e4006cf47618941440013eb01b8a84188038fd5254d89100e6db10ae83122000e3f549536148001fc0c490aa0880035d5d6620c5100069e3aee8b0a40008fd801d9424c401a78ebba2c4880032fdd26358910004ef41ee2a126014dea82dc132480019f4203b26290003171d4634c52103d7d400eab0e40008fd87141610c8013f10e98a408801eee2014248540007d4a16829022000ced725c063484011fb01b8ac5a1802b7a0c42583310063faa0eca9220009fb805ca544407d5f30139ac019002bd60672587300053ec2ce6b064200be58294d21440011fb0e192c12880375c84735812129f6d40665b02620cbf28090c31440011fb0e31e42a00023f6037654f21005dbc22c598a2000ade83d8932440015f50d99240880023fa1c63485400065e18ee8b122000aef8058a420c40197ee9b9ac4880035714c73485500055ec368721e40009f58798831440019daedb166488002fc60032cc51003df84028490a20008fd86dcd41c80012fb0439aa8a80031f98b7558910004ef
  | 36 => 0x2c48815ff410332cc510007d5322849022000cbe871d162440013bb0f9968398036b761b324c73003d7d400e6b0e4000ebb6499150440858fac4bac64a0002bee0173589102ddf5c02cb2124000c7e85dd952cc001be4a0b8864880033b593724c7210e6f5212e110a4000bf38050d514400157b0932cc4880033dc847650d21006ddba6e0b122000d5d7550e62cc0159eced316628806f1fd857590520055f9438e29022068eda50d8e634407d5bb0fb1e6490002de614624c110007b9a12a2a82201bcf67158b424400167b0a21a8598002afe0554d894303d7d406e8b0e4000cf7655c4325042d5f50030ac1990036ed9170d09200053fc2ac7b122000cde63dc131c84398fac4bac64880023fe01760ca41347e9286c798a2000abe871d162440018f8ec3aa63900033d591710c91000766a1ac43166021aee8294d61cc8011fb01b8ac5218d63fa1e634c7200065e3a0c6b122029af7805846148051d9a62102c4188023fe1970ccb410047ec3ec418a8000c7f7598d43c807fb3e653a04398002f6a1b324c110006ea39a6290a2027cbf625d232544019dac4b8e659818fb960762485100063eba8ebb0a4000aed8294d610c8018bcec32e6498802be6027158332006b7baa8498e4000cdf8758c634807d5f30139ac190887b3a0c20d89310047ec38c790a2000d6f7550931480011fb0239ac89006f79c41720c52011f663166598a2007afa8014d62440011fb01b92c7288d33bd91720c72023eb629ae52a64000cef829d83148001b6ec9b8a8490802bde19424851000757ba2e8b10623bd6c535ca54480011fb01bb6652886efca06734811003d7c402cab024200cee70588320c401af641baa86901c779dcb61585200657dc0ee4b0062009fa8718d2044001b9c4039ac290003671d073585200047ec36e4a9a2000d9c741cd6244001c7ea92a6c090852f6201424cb3000775b28c49022000af88650920440019ba6139ec0908023f60b7058e41005d6c0886a164000e5c531cd6294401f60e920a40880023f61c63905200047ec10e6b2e8000cdf76cc921cc0018feeb3aac3990775e1d57548110006f3b12e21922000cdd708c0634844d5ef02ba2c219002afa1362587303df67100c699240009f58798e41440015bf06b24c6900aabea1c72580311deb7a8ae52a24049f2f5495132484014f90aa1ec48812bf81c232485100047f43ca5b0a60008fd8798e42440014f90aa1ec2900d2bba0830588310047ec38a2b166000dd8635c03148039be240b886488072bb61f620c910005f8c008798a20008fe87d0d60c84559f4edb1680880023fa1e4258031064fa438c690a2000aed8298d2144001cbea729ac019002ed60864505100063eb2ae12184200bad8110d42480015ef02a1ec2a91ceb7a0c62587300066fb9ee2b122021c7f52
  | 37 => 0xb200067cb8ae131a4000b3f8155153508011fb0fa1ac1908afead804350920005f2c0841b126200cdd7398c41c80016eb0a31282880f6b76087098c210057c43c84b006207afa80d97604844397a853b48498802fc6024348510107b9aa242a82202acf471d893244053b9e62b906390002bde0564cc52100576c108031a42009f5811cd54484011ff00bb664880037cdd370485100dee798ae418a400a8ff815c863440e3bcee5b8ac488002f621b324c11014e76b0ae418e4000bae8395142480014fd0a202c5988023fa1c4358732006f3102e418a2000af5811d160c84531ff00b90c6880023f61c43d8520007f0a16e2902204db7685d0731c84011ff0eb2043980037c54570c85100053fc2ae8b122000d737254550440015eb03b9ac190802eb61443509204166eb96c731a4000af5819d561cc8019baec31c62900023f61e6394720005f8c1663a022000e5e76197324c4015f507ba2c010802f6a0e544c1100072e298c6a924200af58190263884015f300192c0188023f6007654d423dd6ec14e631a4000cdd655cc62440013bb0239a849902abe20142d85200047f43c84b066231cdf32dd9540c801fc46490e80880023fa1c64589100047f430e6aa240008fd829da41cc0011fb0e31a42a80023f21973d05200e5f2412c890a2000fe13248520440019f421bb262900873b98971ccb300053ec288131e4200cec20dc961cc00197aedb2686900fb3b98970ccb411fe77392c420e6000add839d360484139f0e1b12848801f7cd87704851027676b82c590e60008fd829d841cc001ae90ab8864a8883dca1521541100066ebb6c718a4000f71635455044001e3aa8b2a87980027ee1d3148110005e641acb1924200abd82d90424400197ce8b10c3980026fa0f71551420056fc1aeab122070cf770dd921c400197ee93a2c488003571d4735812103d764326490a4042cee869c8315000176f08b1442880032f5917119332006bb90eeaa1a42008fe8710161cc8017ab02186c6908031fdd5644c5210047ec0cec21a4000dd4819cc624400f7e501992428803efca0374cc510005dbc22c6a8a20009f8875893044039be442b8064880029f21543d812112f723128290a2000cf9708406348439af240ba88488002be60043589100047f438a8b0662009de83dc9544c8018fd0c39aa8a81b737dc3630c9100047ec04e7b128200e3d6590d420c4017e30199282880023f60276949310066eb806031a4200af98094d61cc0c3fc4603124288002b7e04638c5200057cc00e9b0242008fe87d4d6244001d3b0831c64a8802fce0142945100057bc0aa7b0a4000af6860ca4144001dcf02b1243980023fa1f43d81211367631ae5a0e4000aec835886244001f5086a1240880023f61c52583410066fb2ae63122000add8399263480011fd0e2a
  | 38 => 0x8fd8799063484019bee739ac321002bb61270588310053fc2ae231a4000c7f525c063550019df0eb10c5980035bdd6425852014ef818ee090a2000cdf70dcd62440435dd04186c4988ff67d0a7390b3006d7d40486b0e6016cfa605c3328c439bb241398c488003750427318910005f9c12a29022045aee8290f625400197908bb46290003371d932487301ad7ac08e0b146200dd4635c63244001d9906b82c41883a3fa1a73c85100e677392c5a0a2042dad849c831500019db0fb1064880033759473585200063f192eb31a4000bb982d934044039f930631240880031f59570908310053f42ee6b06421db7a8599120440e1bcae5b0cc290002bd60670d89310057ac0884b0e6000c7f7559131480513f10cb968088002bee01435803200677106ec98e40008fe8790162cc47fb3e653a4c59800373a1c634c9211a677212ec18e4000be58210d21440015eb023aac1908031fd4171d895400577c1287b12202dc7d7259643084015df00b128418802f5a0c629051000677100ec98a401bf705154520440297b501b9265980035719473595210057cc3c86b004200cef80dd9320c8015f301212c1188038fd95649533117676312e5a1a2000ade8384161cc8017e30329260880ff7a90b704c9200047f43860b086400ecf835c1620c4018f8c7baa8790003379887358910005eb418e998a203faec8255162cc001bcc21b92c6880026fa1e21551430065ebb285996821cee68618921440015bd00298c6908023fe1d43582520047fc02e3b12a600add82d8e63440018f8eabb664a80023f6047654d421fe6fb12e610e6018a3d841cd651081f9eced98e42880023f21d52d8530006ddba6e0b0a403decc2018d32480011fb0e292c22186f7a841720c5200071e3aee8b122000a7e859d161c8001f90c59926088002bbe0965cc9102ee5ea10e6b288400bb68418951440015bb0231a64900d37ad81720c5200def4882e418a4000ced7258a61cc0879dcc5b828418873f2a0c6248110005dc422c49822000cec73d892144001dcac43106288002fce0142cc5101ddb742ec6a124007bf2801cd21440017ab05b1e628803b3ed89708c5200047ec3cc7a0a401cbe68218d2144001bb6c6b8062900033e98f70509100056ec36859966000cde821cd65504018feeab12628800277e0973953300067ac3ec330a4000bf18190950440014f90aba2c488002fc20d41541100067d284ec1922000cfb805db41480015df04aa2c59805b3e9c263907200065f3a4c430e606bcee73d883244001978e931ac0908038fd92548c951005ae42ac631a4248fe2504c921440019f2e1280c6908023f6037258e410063e196eab224000abf845c9608c4015b906b168288093d5d4e535051043f6b90ac631a4200abd8419561cc0014fd0bb9ec290002eb6144350
  | 39 => 0x18fea0b88c6a9003795cb62905100de7c884ed20a4000c3d7559043cc04d9dcc4b9682880031f1897510d10004be43a64aa4a200cdd649cc62440255f100a1ac0190033d5c47158032006da3a6e2b122000abe849cf6148001be4a0b8c6488002b56045318d2100773b96e2b122000cef641c963440019bcc839ac4880023fa1c43587200063ab2ae21948263ced71d8a62440019b8613b664988035de15710c9510e6ec992e01922000abe849cd62440011fb0f31ca4880039bd9620d89310055fc22e2b064200af58118c61480639dcc5b92a9980febb61f6298b3039d6f418e4b0e6009cfa70d8b3244035a7b0839aa9288034f5537254d4200676b96c418a803f8fe8718d324803dee0a8a8a608809bead8142d0520005f8c14829022000cfb205c0634840157b0931a6290002bde1942cc71000576c10c690a80008ff865cc414806b9bd0d39c84988033d61a73487100557d400a6b064200cee73d8a6244051d9a62382c418953bc88331582310947f43e86b006400aed849cd620c40197ee93a2c598002bde0564987320063fc2aec19220009f98790d2044001dd4e0102c4188023f21d425833103d7d400c9b024200cde20dcd6244001be2e9b8242880037c205700c9100066e3b66498a403fcf8769cd2044001f628598e8088002cb61443509200067cb16e0a122000dd4211cd6048401b98e7192c0908031d595710c83106ef9b0ee098a2000bb58110364484015db0531cc4880031f5d463d0510007f0314829022000bf182cc5504400165b0a21a85900033d98f71509210047f43ec498aa01cdd9205cc62440015bd07b26c6908027de1c63885101fe3fb12eb3166000c7e7558831cc0018fccab8065a086ebd20553d85200074e3a0e6b12200e9f6861cd51440014ff0ab9ac390002be603325804110d7741486b0e6400bd68394b31440018feeb3aac21906efc20e21481100dd76c14e0b146200dcc201cd61480011fb0e31884880fab7a0e71583320047f438a8b006400cdf700c163084015f30029ac4880468f6107259741006dd886e8b122000adf8650b32cc0751ff02bb064880031f14c7654910004fbc02e39966200adf8655332cc001cbe65b2864988027da1f634851021d7dc02e8b064200b75851c732440375ed03b2ec2900023f6087654d100069ea1aea21e4200cdd301cd6244069d5ee8b1284188037518f714c9211d57b430c290a4000c7c655c0324c4015bf06ba2c48805afca0071cc91000676b94c530e60008fd81dc16294c011fd0d39c84880033b5c872582311ff6d994e6b004223cbd429da42cc4011fb01bb2a690802bbe09631891000577c12ca9928033cdf32dc1610c8014f90aba6c2900737c481718c91035f66986c59922000eda73cc960904456ed0a3a66288002af61273589100066ebb66528e6
  | 40 => 0xfa1443d8121006f9c3a43a022012aed821d1600c8019b8e1b1cc6908333d1d863505100076ac366598a2000af98090d60084017e700ba24288002be6033258221006ba3aee2b024200cdf305c863440017e700aa662880035d551710ca510053fc2a86b166000ed686ccb31440435bd07386c4988fff1dc532487300055ec0ec9a166000de4205c83144001fc6c528a40880031f1d8754c52003d7c402c8b024200cef72d8931500011fb0fa1ec2900029f61464583320045fc3ac83224200cfb805da42440014fd0a324c598002bbe0964c85100053ec28c9b0a40009ed82dd331484019daeca106390002bb60b6418910054fbc0ae5b2a2000af9870c9600c40197ae83a6c0908033b883764c52000576c1086b064229ecd31dc1620c401d76e9b82c4880032f8c97418d51406bdaa6e0a924000ed46354531440015db0421ec290002afe1943d0720004bfc3aa8192a00aaf6811d560c84011ff0cb8c87900031f9d562907300e774b86c5312201caee8218f62440015f30028ac1990023fa1c50584320063fbaae6b122000f2d545494248001bd284b8442900029f61673580320066fb9ce6b06421cdf1215c252440015eb0331cc290002f6a0e624c11018f97902a8a928400df0715c33244001e5ca929a85900033bdca4258730005f5c02caa124000cbf741916048401adc64bae839080375c86739912112e76316e4a0aa000e5e85d8e63480013eb03b92a8908029fe15624c91014773b00c490a2000a7f8559361480014ff0aba2c019002b7604630c520005f2412c6a8a2000a7d859d1610c885f4842a1242a0002afa107558b3014ef3882e418e4000bda8319130440015f30021ac19080397dd6634c72004f75b0ec49022000c7c545c4635506d1fd0fb224288002afa105258730006afbaee6b02420aafa80ccb614800175d072a28590003cb95253509200e6eb992e21922000cdf7418d3248437fa06298a408806fbca18714811004df5c12e29022000bf2870c52044001bd080392c688002bd60674d81210053fc2ae831a4000cbe7418c6244001bb4a0b98c488002bb60843584320047ec38a8b06643dcf8761cd20440015f700a12c0188033e082760c520007f119242a822000af1810c9609040147b0831aa4a88038fe016550b41006daba06418a2000ade83d8932504fb5bf04b18c6900ff674c97498b300047e432e52a22000deb80dc963440014fb0a21ac3980033d883764c4310067ab2ae21948200df37250550440015b906b2a64900ff3b9c962987300067d904ed20a4000bf38050a21440015eb03104c69080376942731891000677b96c4a0a601bbd4814c931480011f90cb94a68803efca0032cc5100063eb2ae01968200c3d7559064cc00197ac8b8064188029fa1763585200066eb22e63122000fb342505204400
  | 41 => 0x12e19922000add8718e31480195f500192c018802fc602420c5100056f41ca4b066200c7f70d95414c4018fccab86ca9085b76e1d70ccb300047ec06ed9968200add8614c63484379f0ecb12a0880031f98b7550f3003df8402a890a2000bf180cca414400157d0c21ec2a10031fd5176945200def9438629022000a7e85d8961cc001a7a84ba886190037a50b704c92003d7d400c7b0242009f5821cd5144001fc6c598a40880032f1d063581210e773b8ec490a2000c7e62dd543440013db0f3246490802b7e0d65d9121396eab8ec731a20158ff865c843cc0015f700ba2c1990023f61c4018d2100576c1087b024200cbf649cc42440015bb073a2c3900023f60476553300063fbaec8b024200c7c52dd952cc00197ac8b90c888027f8e0762481100e7b4c28c49022000abe8498b61cc0013eb03ba665108030f1d47458910107b829a42a822000fd063cc5204400167b0a32285980036b901720c5400063ebaae331a4029af4814cb60484019d8403b26290002b7a0c4058432006f3432e418a2000bba8418930440018feeb3aec4880733b1cf62c851010f57ba6c4a126200cdc73d0d62440439dcc4b8e65a08d73e881768c7200047ec0eecaa06400fb364cc740440011df0eb10c488002d720d524c9500067d906e0b1e8400cdd7358841cc0011f90ea1ec4880027d20d72905100057ac368490a2000a7e8518560cc8017e30132242880577cd85708c910004fac3cc528a2000add8018f32484019b864bb665a08029f6166498910006bc982eba0a2000df1415c321440397d50421a4088002be6024258251004fbc02e399442008fd878806348419be6e418a40880029f61662587300053fc2a62b064200cbf749d361480019b8c6b8064a8803ce55342541100063fa82e231aa822b768518b31440475dd04282c5988e3b30cb654c9210a57d400a2b1660009df8758c63440011fb0f212c01882afaa1c62481100055ec0ec820a4044aed87902620c4019b8c6b9486908023f61873551100047f438c690aa000ade83d9532440017d704b2a40880023f61c53d89100055f424e6b00640faf6861cb3144001b70c8b8484880023f6037650d210065fba4c8b0e6400cbe745c663480019beec31a8690802bd604535844216d76c3c873106200d5c734c954944019bd0839ac48808f7a08172cc5200055e432a8a124200c7d7598f4148401a7aeab2085980935d1d5414c5100047ec06e4b1e8200cec635cb41484015f700aa2c1991133e1db7448110005eac04e399662008fd870c1628c4293db0539ec2900032f5d074587300047ec38a6b0e8400cdc60dcd6048443bcec3b9262908a3bca0472580310e66e992ec1922000de6405c831440015ef00b8cc6908031fdd8754c7200b6edc1ae19966000cde76dc7324c4559f301b92c0188029
  | 42 => 0x8d21440014fb0b3a2c399033f4e04634c110006e7108e6b024200cbf65dd163440555dd0c31242880035ec8175185200063ebaac83122000db574d8831440375e902b2ac290002be60052583310efada9ca690220008fd8714d62d04015f301996c0990033bdc832582310047f430e6a0a4000abc845946348015be702b864288123b944162487300063fbacc6b122000cbc42dd942cc0011fd0fb126288002fce0575481100047f436e4a9a2000d6f75509614800157f08b1262880ebb98cb61485200047ec3cc728a40008fc865c643548015db0431a42880c7d30c954549320066e106e6b122000abf845c1610c8018fecab86649899ff494063cc510006da326e2a124200c7d751d76244001b98e7212c2900023f61c535891000677c3ac590e601cd79205d4624402d9f4c0b8665288027d61c620c5100055f420a6b0e60008fc8750b604c455d9a63102c41898ff8103624851019e6f992ec1962000afa870c9600c401db306392c01880397d4e53587200065ebb6c9a166000eeb709c1620c47d9dce4b84c790802dde1562cc5100053e42ae8b0642008fd80dd943c840137d0f32284880033bdcb625055011e5ea14ec216621bdf0315c2314800197ac939e8390002af21171580320e7d2c20c490a2000c3d645d443cc40157d0c21a8490002de61632d01100069eba8c621a8400c7f75dcd62440011fb0f206c4988035d951710c9510047ec38a6b06421baf48150d60c84017cb0521a4388036be20142d81310047ec0ced2166000b3d8519142480299f4e0b106398002bd6044098d21005cec26c49966000df1805c831440015b906b2a6490802bde05640c5200b67d302e19908200cef709c1620c4015db0e106c4988033ed91700c7201fe3eb12ea2166000eea701c1620c401de6c3b824290002be60053583210079aaa28528a2000cbd65dd16344001fa70399260880023f600765533100572c0860b1062008ff8758861cc00177308312a0880867d60673d91210055fc328621e4000aed82d4f62440011fd0e29ec090802ed60640d91210055e422cb31a4023af7815cd61c80019baea39ac4880523f60a73d95201c67c902ed28e4021cec20dd931c8001f88e699242880035d5d6430c5100056ec3ec6192201bbf281d0d20440019bce131c86108023fa1f53d85200066eaa0e6b122000cf840dd9324400137b0239aa8a1002be21952d01101c66f992ec194a2168fc865c3324c401baea639a4288002af21e6350b410047ec06e4b0c860eaf880509608c4011fb0c39a85288739b9d56218910006cfba6e6b122000d5c7518d3148401ba8e6192a2880f7b3908634c9200047ec3c2031a4200cee609da3248401b3ee9b9ac29012edba16648c921004fcc00e6a8a4000c7d625d464cc40157b0d206c8908363f61f32d8131006f5b
  | 43 => 0x62900023fa1f635852000576c1060b146221af5819cd6190801c7ac0a1aa9288027d6077255110006eb086e6b122000f3554d925144001b76403a2c2900ff2fd89748cb300047fc32e529a2000b3d8519142cc40197ae83a2c1990533e9c162907300056fc02c799442008fd82dd931480539dec2b906390002be60375d81211ae6f434e619262008fd87d496010c2977100a1264a00023fe197290e510e772b8ac4312201cdf1205c65244001bc900b9062880f6b7a0e634c92000676b92c418e6000c7f7599560cc8015db08182c41894fb6a0332587300def4882e420a4000dac74dc961480012fb0e100ca9886f1fd4576945200055cc20e4b0062008fd87883634841d5bb0d99463980023fa1c76487300057cc00e5b026200adf8058f329045b5f30521ac0108039be156218910115bb4288598a2000bce83d093248401be700b94a2880033718f7250d21005e741cc91924200adf8359564484018faea3aac219002bde0574589101c6eb992e2194a231fa42155142484579ea42bb087908035d5d66390510007d8206e890a20008ff865c3320c4011fb0c39a8290002b7608630c951006e6108e6b024200cdc635ca31480019bb0439acaa0802f9e0963545100347f436e498a203e8fd809cf6148001a7cea32482900033b5d162cc8310056ec10c698a2042cee72d88315001d1fd0f992c1188b73bd857290d2114e7cb0ae018e4000cdf739cd62440014fb0a202c3990025fa0f72545500076bb1ae331a201ff706554740440533f700b96ca880029f61632d814107d7b4368398a2000afa8790d600c4015db0429ac19908f1f5897510b310e6eb992e319220008fe8794162cc4014fd0a326c2900736d48574189100056f41ecbb1a4000cbf645c841480019f6e1102c418802f86083148110005f9c0a64902201cbe68294d21440011fb0eb1083980029f61a3255251005dd42464a822000eb474dc562440251f90cb9e84900035d5d6630c51000737b2c4031262008fd869ce42c40019be60b96c6880023f60673d91200067b886e2b066400de840dc963440019eac4b8e84880733bdc3620c9100047ec3cc710a40009bf8759064440014fb0a3a6c29001a7da1b72505100063fbaac8b02421bd79105d4614800197ae938cc6900033d083764c4310efb83aca2902201bbf0815d120440015eb03300c399036bea0043587300055e41ac9a1220008ff8758c63480015b906b2ec8908027ee0172945200079b2a284a8a2000cfb7088162cc4017cf02b2a6490802f6a1a434c1100056ec3ec731a20008fe87d4960cc401d98c6a9264900033bd937258d10006cf39a85a0e6200fb34350550440015bb07322c0908029f21563589101fd77416a6b1660008ff875963250001cdeca106c498802bb60a63c87400056ec346031a420fcf4769
  | 44 => 0x30005e6c148790a6000ced205ca6344001aeaeab148288002bd219524851010e77216ec98e400fbf280dd731440397d50532240880033b589710cb300066fb98c710a40008ff865ce54480019ea20bb443980029f61660587320047fc02ec194a2009fb815c332480011fd0f292c198802bb60a75589100057dc0287b02a40dade839cb604c40dbe4e0310628800397d9732d81310047ec00eca1a4200a7d8519161cc0019be4039ac4880033de1d61187320066e900e6b1220008ff865c032d0401ba8e721a4388002b7a0e42d81310063fbaac8b0a4000a7e859d161cc8011f90ea12c398002bb60a53587320063e29aed28a40009dd8718c3244101af0a7b82a490002fce0941541100053ec28c8b0e6400a7f855cd619080157f04b20c9980023fa1c5358b41004fac3ca890a203aaee8215361480019eee330ac1990033bdc9624c730006b63aee4b024200cfa635c2414800177700aa684880031f5d663905200657ac08e4b006200eba42509600c40dbe4e03148288002dd60420195310055ec24c718a40128fc8750d600c8435dd04202c3990032f9d161d833200576c10a6b122000d757558831440019bc6239ac190802ee21171481100055ec2465b0aa03cd6e759083148001af6ebb82c488002bde0553d85420055f420c2b066400cef625c6424c4551ff04bb062900023f61f32580410063ebaac818e4000adf83595604840d7e50d10a4088003b620d72580310057dc0285b026427cbd625d2325440137f0eb20c8900033e9c97018d100047ec0eeca966000af9809cf6148101af6a3b82a4900036ed0b70553200047ec3864b048225cec62dc9414c0017c904b1a828806fb9c4170588310067a31ee2a1242008fd81dd953908019dae4396c098803b518d414c5100047ec38a8b006400e3f64953325441d5f501992c1188033b083764c52003ef83b6e090a2000bbb8458950440019d901bb264190035edd77058520005f8c0e86a822000f724254550440015b906b1264880d33b989720c7300066eb98e6b122000e5c62d97324c401be4a1b8a648803efca0074cc510004fdc02e5a0a401cdb5219d2324407f9bee5b82c6108029fa144058432006f83a6e29022000df1801cd2144001878ca3a2ca900032fdd77458910005ebc0a849966200a7e8599262440014fd0e3aac4880023f61c54d81210057dc32a49022000afa8610d20440013ed0f2166288003ae1837458121006f3c02e418a2000cef7250961cc0017e507b8a40880027761f321073000576c1080b086400cdf65dcd614800157908baac019027f8d8a21481100047ec0eecaa66400bcc8358862440015ed023aac01904abea0054580320065e210eca122000de57290831440015bb02180c690802bd6062018d21006bda06ea98a20128fe87d4d600c8018feec3aa
  | 45 => 0x7ccdd70d8f324801977100a1062a00872f5097198e422dd7dc02eab064200abf8059542d04015bb0431864880029f6167098d2100677b96c4a8a8029cbd615d031c80015df04b0e43980023fe1d42582510066f324e63122000f2d5450a51c80019bce6b0e43980023fe19739472016f4ea14c7218421aa3d841c96510c01ee0c4a8aa0880027d60473549100061f3ace931a4000abf8459463480011f90cbaa84990031f1d5614c720006e6b9665a0e60008fd8714f61480014fb0b31ac6900030f595740cb410e5f34148690a2000ed46354531484397d104b2a4088003b6e0d7258031005cfc1287a0e6000eb784584614803997ec4ba0c4880027ee0172cc74021766196c499280009df805cf42cc8019f6e5392c0188023f61c53583410047ec3ecb1922000c7d7558861cc0019bca039ac4880eb374cb71580320066f080e6b122000db9425c34144001d9ec7b106488002bb6084058b310063eb82cb2186233aee821536048447a7a84ba88598802fce017348510006f2b90c418a2000ee56218951440015eb03b9ec2900027b60873547200063ebaec818a4000dba64dc154c801b3eb0339eca880023f61c63909500055fc22cbb1a4000aed82901620c40197c833b682900b7a750b7498c210075dba2e8b004200af9860c9504400197865ba2c4880027b60873545200061fbaee8b122035cdd769c732cc02dbd6c4b8664900735d485758c910006db908e8b0242008fd82dc163944018faea3aac5981eabb60a63d852000576c14e7b0a8400ae88650920440017710ca16808806ebd20543d85201b6f5b02e420a4000af9829cd60904439dcc5b926398003b318d424c92010c7ec36e498e6007af880553604840157d09394c6880031f5d463905200067c31ae120a4000cde870c163084011fb003b28598802afa1275d8910006763b48498a40008fe8788161cc83bee0a8a8a40880033ed89700c5400e6f890ae01922064ee84058862440017ad0721663880032f5d074589100057743860b1062008fe878816388401be2e598e8088002f520d62945100056f418a8b066200cf721dd9434840157908b18c48803ff8dcb3148110006da90ee8b122000cdd731cd61c80015f700a1ac390003f460063cc51000576c1486b14a200dae409c8315004f5eb033aac219002af61263d85200057ac0ca0b086442cec72d8931500015bd0dbae64988027ee017294d2000676b28e4b1a2034cfa205d831c80011fb0fa9ac19081efc2017448510005f8c04a6a0a2000abf845966348001d3ee9b9ac4880034f50d75d052100576c16c390a8000af58190263484018faea31e82908027ca1e414811000576c10a8b122000adc835956448415be102b86428801efc20175485100053f43041b2a6200f3654d9151440019bec839ac0908023f21d52587
  | 46 => 0x7750939a408815ff494332cc5100065f322e01906200aed8214d61cc80179906aa2659086fb9a0b6148520066ddb22e018a80008fd86dc954cc001e5ca8a12a3900023f60073588410066e3b28690e6000bad84083624c401adc64ba88790802bee0142d81510065eba4c3b066400cdf64dcd61480018fecab86c498803cb95142545200047f438a8b066406af88090d60084015df04b2cc4880031f9d561d07200047ec0eed992200eadd86cca61cc001c7f04b2a85a08033bc817298d100056e432a99926200eac74dc962440011fb0db9a8290002dde1531485101ac7f43860b146200af5819c063484399deedb1242880032f9c764d0d200063f396cbb0262009df8750f61cc0015bb0c186c6908039b0836518931006f4c02e418e4000cde861cd524c8018faea3aec0908035ec8175d8d200055ec20a6b0e60338ff805d8324401d5bd06392c11880337dcc63585200057ac34e690e2000bd48359331440011fb0e192c1a08a33e9d862d01100067b882ec90e6000af5811d361480018faeb310c398003ba9906248110005afc2a879966048cef7058921cc037dcee5b0a4290003571d473585200054ec20a631a423decf2118d32480018feeb32ac3990863f607764c7201fc7fc3ac518e6000d7b205d74148001be2a3b82428821fb5989310c73000576c04e6b1062008ff865c33210439f550831240880033b983724c721005bcc2ee69022000deb625c3214400157b09314c398002bb6122058831005bcc2e829022000d5c751cd62440019d90eb12439810b3b1cb62545400066eb98c7b0a4000ade83843624c4014fb0a21ac019002f56045318d210047fc3aca312203fdd9325c032cc001fc6c490a60880032f9cb6410d100057ac08ebb0a4000cdd65dcd60484014fd0a212c1989f7375c063cc9200071eaa6c4a12a0008fd879426348437be482b864288076dea1741481100067cb80c03126200f2d5450a514800f5f100a1ac390002fc6004348510005ea41ac598a2000ced7618b3244037b7220ba062900037c102734851003e7b3b2c598a201bee9105c1620c4017e302212608806fba841705883100677b28e4b1a2000ece63d8b32440019bd0e39ac488002eee116348110007e831a4298220009f987d052044001dd6c5b824288002bd6044018d21007e3b166598a2000ade839d360484695dd0521ac418803f4ccb31481102256fc14813184200c7f545c36254c6997a84bb48418a23379ce62d8730007b9b1aa2a82203fade8718d3248001c7acbb8a85a0832fc201420c51011e76314e690a2014cf860dc132504016eb02192a2a8003731cd42585200055ec24cab122000cdd7398f42480014fd0a21ac3980023fa1c4058b310056e41acab024200c7e655cb65440018faeab0e83900023f6037158843005ce41aa8a1664
  | 47 => 0x6066318d100072fa9ca6b166000b71851c52044001af260ba886880033b5c962107300557d400a7b0a403fcec7258931cc00157b0829ac22101f3e9db70485100053fc2ac63122000ced7298861cc0393e90e98a42880033b98d72d07211567b38ec5a122000a7e8598161cc801bace631c42880035dc877558d21007b8a12a2a82203ecfa205c263c84015db0539ac4880cb730cb75509322477430264b024200dd47358d51440019f301bb26290003f460332cc51000576c2061310623fcee7258a51cc0018f8c6bae83908023f6037650831005e841aa298220269f7815c94148469dcb02102c41886ebda0763d85200056f41ce6b122000cf7719c5600c80197ee9b92c4880aa3fe09768c5200057cc0686b006411a3d841cd65d040197ec939e82880027da1c42cc5100e63fb12eb1922009afa8014f624400197ee9b8ac4880031f99570cc831006ebb9ee2b024200cef7690931480019f465b82caa1003795c9420c51000576c2441b126200d5d305d760cc8019f4403b264880ffe361262ccb30006ddb22e1a0a2000ed7635c663484011fb0e29ec090802bde0562987300067a316e2a9a2016add831d160cc8017e3032a260880036ec81740c5200e6f2312e21922000cef825db32440013f50f2126088002f320d424c92145737a96ca99242008ff815c26390801af640bacc69006fbc5c361985201ae6f43e64b0e603f8fc8758931cc0011fb0039ac5a08031f21576d0d2016677312e999062008fd809cf6255001cf6ebb82c488002de616734811019d77410e7b024212cfa605c032544377e5032a24088002bd606755891038778386c290a4000afb804cb60504011fb0e29ac1a10023fe057610b300057c43c86b004200cdf7318d51480019bce1b1cc690827f8dca2148110006d6aa2e5a1e401cbe682d05214408fadceaa1063900032f9c964d07300063ebacc7a0e4000af980d4d600c8011fb0fa9ac0190036b55172d0d200967c380c6a12403bd6e7550831480014ff0ab8ac1908033b591720c730005f8c00e598a2000cf7719c562cc019bd6c4b8062900023f608765513010c7ec38c1b12621ccbf629d232440019bca439ac4880c7d38c95454b320066e316e6b12202aecd319c1620c455dcd03b124288002bee1c32582410def830ae110a401db78854c520440013ef00b8865288026f6037155342006f5b90c49822000cf9725c26348029bd0e09924290002bde19420c5100053ec10e6b288600ecc835886244001b5ae8b94c690002bee0174d85200056ec16a631a4216cf87098d42480015db053a6c090802af61b4350720006dd904e931a4000ece8358832d04011fd0c3b664881eeb360a7318d200055ec3684a0e6000aed82d94624406997e8439ac3210835d19571949100957d406a2b0064008fd861cd5244001
  | 48 => 0x284b0e6000ee96218930440011fb0c39aa3900033e589700c730006ed880e6b122036cf7865c432904018fceb310c398002bd6064018d210055f420a6b006400dcd829ce64484015f3013aac199002b3a0c20588311bfd210ec8a124240cde869cf214c0019bee731ac2900a6bda0742d8121006ddc22e0192801fb788558f404401fbe4e198e4288087b960420d89310057cc0087b0a4000bf1801cd214406d9dcc4b908398092dd215625051006d7d40665b026200ade83d91324404faeaa4b8864a8802af60764993300047ec34e690a2000cdd641cd61480013f30139a42900033b619720c5400056e41ae4b0062009dd801cd524c839b72413a0c4880032fdc374589100057d416e8b0062008fd80dd9540c8df7cf02b10c4880abb9a0620588310b47f43e86b06640cbf280cc831440014fb0439acba08732fd0976909100047f43ec89924200cbd7458c62440015bb05b1864880033b5c96290730004fdc02e5a1a20009f5811cd544400157d09392c3980029fa144058732006f5c02e5a1a4000bf18090c31440013f30139a428801ebd219744851000677bb28498e40008fe87cc960884015f30939ac01887edea1462d01101feaf992ea21660009ed821cd54c84011fb0e31ca2900031fd51769473003d7ac0ec490a200fbf38158d2044001be2a3b82628808ebba084098d210057b4366598a2000aed8214d60c84015eb0d99662880027ee0172d0d20005f3c12c6a0a2000add820c3634840d3ed0db92a288003374c276cc9100055ec24ebb122000e5f6514c63484011ff0ea1ec0908036bdd1325812122eed992e0192a0009de87d9532cc001b5ae4a1062a00523f60a73d9120006763b28498a401eb7885589304400137b033b086a1002af613629873000566c10c6192a2008fd87d9232440397d50531a408806ebda0443589100057cc0486b04a200bd48358a21440015f30021ec488003675da43d0b300074eaa0c6a1a4200ece2018d32484019dacbb92c6880023fe197290730004fbc02e21966200af9801c562cc0011fb0eb14a3980034f1d474581210066e3a0e6b122000cbd75d92644408baf2a4b8064a8002bb60854583210056f41ec4992a000bb58190064484015eb03282c319002bb6102058831006cf420e6a8a60008fe87d9562cc001fc6c438a4088002bd60432587401447e432e19924200cf5645c432c40011fb0239ac5a005b769c33290730005f3438c490a2000bf3805092144001aee42bae8290803761cf70589100055ec34803224200c7e7558861cc001daac631aa288002bbe0964cc9101fe77392c418e601ccbd425d842440011ff02bb4a5980036e1917090d100053f42ce6b006400afb87cc960904ed9bae031862900023f6077654f2006df8c0cc690220008fd87d8a51500017e50710a408819af5
  | 49 => 0x1620c4011fd0f282c399002ee60043509200747fc32e3996600fbf28094f3144001c7ea92a2c3980023f61e64189100047fc0ae031a841caee8219362440013f702b8064a808bdc21731541100061ebaec93222000bb98010d424400197ce5b24c888003dcd915154110006f8200e690a20009f78758d214400175b0a3228490002ed612325451016676316e4a1a2000cdd635c33210401b74e8b84c6900033e989700c7301d677396c3a0a4016afa80d0d60cc82dbd104b8664900873b61c20d8931005f8c06e890a2041fab601914248001cb8ea39ac4880023f61c5258043007d8a1243a02206beea70d8b32440819dce5384c7908036ee11700c5400057cc00ebb0242008fe87d9132480015d90f202c4188029fe156498d20005da422c6a8a2014be88050932480019ba603b66488002be6184348110007d43a2849022000adc835d92150001da8c6a0a629080379d91720c5100057b4306528a201cfa8425092044001b98c6b948690802b760c54580320066eb20e6b024200ead7490d620c40d1fd0db8a8490002bd21942cc5100047fc32e81906200bf18090951440015db08106c4988024fe157190d42005f8c008598a2034cec621cd21440011ff01b92c6880a73e1da624c1100047fc3a84b04621cbe88258d2044001abeebb9ac2900029f21573d8910006afbaee6b122000a7d859c161cc8018faeab20c398003b358b3258730005edc02849966000cef80dc963440013ef02b94871081ebda0675d81210065f310e8b12201c8fd87d8f624400197f08bb06488003b958862505100057bc328490e2000aed8215160cc8375ed0229ac4880ffb360d620cb301be77312e520e6000a7d8599263440375eb0fb0cc2900023f61f628c5400063fa8ae1b12a600abd81d9264cc84fbae64b8864a88029fe154358332006ec39ee0b0a4000c7f75d8531480013ef00b8e64908027ea1c424c11000676b12e199682008fe869d931480016eb0b326628800327dd0735891015d5ec20eab108600c7f75d89314402d5f50028ac1990033bd977258d100066e180ec90a6000af98094f6050801b68c8b8c848819ef5e056318d1003d76c16c290a4000adc8359563440018f8c6bae83900033b5c962d0510006bcbaae131a4000a7d859cd62440015ed023a2c0190d63fe19728c7300057cc2664b006200bcc8258c634405bf484321a84908023f6007358910127b832a82a822000cde741cd62440015f700a96c0a08033d5c47158b300056ec24e631a4215cde87dd932cc0011fd0fa9ac1908032f8c774589100056ac086031a4200af78154b614c8395dd05b26c48800375d4c73505100047f430e6aa22000a7e851d1600c801abea039aca908027de05729512114e5fa0aed20e4000cbe861cd54508016eb0a3a6628803e7da1c62cc51006d7c40
  | 50 => 0x802400c0070050bf40221730fd8054004000044003410a00200009c80b4001030003c02c00700700080040065c80030000014007806004000901a80000101b900280b4008004033808404e05d000807803e000003b71400401402701ac01a01e002800064600002d800c00200000c82ec01e0c80130028012009000000027a070000007c00a039000000001403401717280248e400280240100000048430302002000808c03403e00300000960041fb80888ca1ee00000c0034054000009007600f01782cc00a003062000c00400200e800006409900900700ae01702380240140340080084012002001335896e02900300c422201b009000002000000180100520230020000006000001000000019f00400b80d8012000001804a03c00200600080003320198c4416f003828c00800600576c16c990e6000cde635c432d0401fc48528a4088003b960470588310057dc0285b0a4000af6860cb31440014ff0aa1ac488003b9e0562189100067db16e0a122034cec625c831500bbcbe6439aca210cebba0a4358b10005f8c0464a8a20008fd801cd61908019ee43b8ac9990373d1d931485100057ac366510a2000bd4864cb31440016eb0a2166288002be60032d8131004fac0ee99924200af78159331c807f97ec4ba4c59805a7e2017550b320059fc0aa8a1aa4008fd8710263484015df04a9ec4880033761c638c520435e7c326590e60008fe8790961cc0019f641bb286900023f6037258c410066f39ec7b0a8400cbf7458d62440019dee5b12a29800277a1f32545301567790ee4b046200df141dc121440013f70ea1a40880034f5d564d0730006ed100e6b122000c7d72596430c437d9e62b82c4188029fe156418d200047ec0ee0b16861ef735254530440c5fc440b14428803e7da1c64cc5100067bb0ae130e6400af887509600c4015ef02a1ac1908029fa166458121004dfc3ac8322421b9ec874c921480019f2e1084c6908023f61c63949400065ebb6c82122000ecd83d8b324400197ee93a6c0908029fe1531d81210057cc00a7b122000f72325455044001bcf03b92c6880037604073589100053fc2ae2b006400dea501c96344001d98c031a6490802be60053d8520006d63a464b024200c7c535c36254c015ef02996c2a00a73bd81720c520117b9a9662a822000cf5869cd21440019ecedb8e648800337dd932487300063f32ae3b2e6400cdd841cd62440439ec42b8cc7900023fe017690a310057ac08a6b0e4000c5c7518d43484014fb0a324c6900033dc877654d210a5f54066499240008fd8718e21500018fccab8665208033bdd37058831005bdc2ac5a02205cdcc32dc5524c80157b0939ac1908035d1d771589100051e42ac83224000daf72509315000117f0eb20c998002bd60663885200053ec2ce1b126200ead545d
  | 51 => 0x2021064800c032004000009c00600000a80014d210301280dc00203605b8044020001000000c0021150038048002009000800000000000c812028804b009001805a0070000014a6e00300880001b400000006b41a003402a809002600001516540301a1006006405018505f800000402538494dc02a00f02e0000652009009000400007a0020a4802a000014812c0020340a8806800c0070008004019008010807010a00000700dc00600f0089b840160140018cc807800c0228060000030003801400403f00000340b605400c8000020007010003801000100101b000a060011800800200004c80200060060010094008001006003800a00000582447ea0d5004806c07006401b803402800000a000001205301600bc11c0020008110018029000808c02600003200002b8001000000c00280a02800200080060d4816c01600e002000000800000200000ec001004019001604b156817c00a000107038001e00a000000451000600002f800800500000100000151e50194016085004000411e03800d800007201800000b002c02a000006407402e00000c455a000020800000601700105f8024000001801002c014006000400a005029000002a00400b0e901ce0010000148000038013804802a0011ff804000428601280080900b20048058020525007804822a003003802002600410d015817001901100d8074001016000015202400000ec0000120000010000088001000c036003000002800200005c000c0f872f01a8020000001007800400600200b10440173da002808c00205e0000000148000001008c07e000157000000403b0090004064023003877005000b005061800000000000a0016012001803401606200b802c03400000e8ef01a001200702b000800201800400000000108d281e400f00080b4a4402b0120000002029074014c0f4008000132800000014580004fa84900501b401702600b000c24c4a401a8000001ac60008dec05600502e000001c0440000390000000065003401e03402800080ee0020008000000039001449c0000e901489e000c00a159801c00400500280140080030b0000809e001000009406000b002808400420505a000c00c01d00a821804400400380482aa103406000005c00003a11e80500000000088000040012800002000105b009c0100030010000042010002846400002d2030000000007000000161203203006380160060498034108004048002400400400e081001c031030002811400200f0118272000000000001c00303e8074048000001821806c084000000004c96c002013001807a32c00fcdfa00804e82d800022e001001001a013001066c000000000000001200300000001b402b0030028008004033014c0a800c00100001900050050024030607000801041600000e005c01e000001
  | 52 => 0x2806800608408f001000000e000002c002014000001800800011581740420d3030000805a027076800002800000109a8002875003800000200a00680680001180018bec012000007009800208c01f0024000000001001801401f001805809a01b23b81e00180460018004024014000014002603c08631d4078073001003400001000600a007a0000de80340000bc001829411e007000000012c02601480a802000e0018004004033001800000600000101d8018023018800000600209d0054064004001013c00201d0080020070002002002c002012006002c0a60a700d012000010d00800080400041bf800401c10500f0020000013001000000a0320000064020000000802802a0230000034004016050802a8c00c500000000000026c5b76d550008051815400a00604a801405401c01c003801000e00801c403202b008000400600a00000000fa039007000001c00200105dc01e027020806806c0061a8003004c00109480600180e1003806400000317000080ca0a600d80401e643b015801800600f003000c02e00c01a000814e0000078010002006000001c00405a06188740c200100e804401a00e00c80085dc00500180082be0230168208026008008800084603e017000808e019000003c00001a000805004e00001700300303ac003002c000000000800001c520036803403a006012000416631c003801400800c0561258244168220012c2d4028002811c00000f19b012804c0b5003833c00000d00d803801600b013002c2460000018030003496002802c02000100200100060220000000000005005000004a0060031c7004200500587e000a01147c801407003f06d00000160010000040000003000000020600100000280a8001000005400800000085340120b7016036009407e000800000001400400cc3e200d000801800800013f00e40140070118104076000000800c00c0040108008000161008800092c018013800006000401e8004014005001000808403a0000d6400403b001025401006d0040000000000000800447400e00180b4572a7d013800000000003180f400c0010141ce401404b005000001a006023009004000300b805400459f0c50bf000004b0010000000000007048c00a0020178268002073001000000000f06380d415a01521e000c01a00500d000006200200e000c1c8016001032c0080f7000000c02c00000f004400c001010801c00e0130000004012024003801000800000483ec040004000000c00400100380a80300530028014000013000800c02600200200080080080b081140860010b580016b00e2000809c00601200a8004000024000800003000f02700000bc002010000002601900380a80a006d00000b401200d07e800001e07900a03ac01401300d831803802a01101180221980068a9400
  | 53 => 0x14003009808407000100b800003400608e802c032006011019805c03b00080181d4007000001007201800500400040810b680d800600003c00f800a05800285700060070010390090003000005400c000000002400805a098000c000003000057001200c001800009e00300c872800200004d002402c0cb00380108cc000000160000000f00100a8002002008803000229900180000fe002034000804c1f100882c401607000a004c01802e0ca017008c0000010130014552000053c03e0590028080000004000001412c464000005417802a004005001400901c80fc01c00a0040014018034008800007402e000000801406401900dc00014100f80ec01a0a100482040000a20028bd8004009000001c000000001011c04a005000000000401d00001700540180000008048000006805815a028031800401806a000012000200d000215c00007808a00b80140560189bb000a000000003c1a403100d0b5800e02e01e814002c137007007c04a001015004037806d001000021800000000740a000000480204b401700a802c24697000b800407d0dd008800803002101000000000140020008002000007808c00006a059802800401d000800001000002680081e2003002011c000003035800803a00400d8014002000011801400607a079052c00000600000200d803e003832476e001004812000c02e01281cc01a0fd00000000b804c0120000086000000000004a00200980b45e40270000020020038009811821a01010a954c008004372801822c005003800c0100030020a4401652218b800408e0a8000002000001801580080fe06e02780300004940008158104000059848002200e19e81f800000827e802c13a0050120a2c000027004017004403d00b801800a0b4001809800400b0058008628072002000402600702200080000010350048070000000062c0160250938080196011020800402468100000003720f2017800403406d02600000a0035006803802200000700980020000808ce4aa011600486d4008004083807005c00c003063016000700302f800400403f80000c80000428000006086009009400002700000180da08200d800021c000003007803400000f000804200102180100040021a6012c00600d229000800e01b001800408e0ae00104f401603400983e001400901f800c01800000000080c605207d009404801502281d46e008a000001001203d028802800a03b0000000086003023001c06828b0000044000038000000400c007008032000001c00180780440160000030096024006802401401500004680740200148058002001002009400004e00000742840aa00580e400015600c800000c006081800c0580b200000000340200580054000000002000400600000200280ec0130020a4805000101885a800207f01
  | 54 => 0x8001800e0af02800cc000000005001002a00d019800863000000080000020010050198050000101004c000009022800002a04100680040840a00048044022000001801000000600001440b401401e801817400001e006c00800200c8088022000000018400000a01f008000825400001e40c601a06e00b0006026007800800000000900dc000063013000002e0000028174b661480cc800005e0020061394000006011004801e26a04500080000410001b4c0d61ee04484340001e600000000060d600800080020008e3800800a03701e00a403a000011800006000c0ce801c0880000000110000001064000400e0000358110000017000800003602e00080b40f4043001801886a00600a003801c000000003c0f815601b00d002800300002cc01a00201714580cc0140161af800600f004000000200900700a8000024013807800000a001802961e008008002000c00c0000008000002000000c3020210d500b000e020001001000a000000801c060002005803168603b001b35400003f02500240020830000004012001005000000000002300001c40060c1021802000101600184da0e402500a855c00600880c818c00006080b490000300e00143f802600980e001c00000014a40
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x185f8520d760c91000574a40819cc62440014cd97d8d7298d200061b25787588624400197175602430c51000536e41741cd624400185f7560e755891014578a5a205c831440018ae875d243588310050f65052dd952cc00157195201710c9100063c607709c161cc80158d9308774581210062b611721c9600c401a398561072580310050f652625d762cc0010fb985c87258031006e81c5841892044001b919420d514c110006aa611631892044001b618590871481100047a261425c23148001ac730219324851000533a4a735c863440019d2801cf3248510006d420e3254550440015b1941c570cc9100050f65053dc1629440183d75e0964d073000693a15831c1620c401c1c751d0735891000678e0b72505504400183f7461464585200041fe61751d56244001ac5936047058831006aa611721c9600c4018d476a0c6250510005d8e496354550440015e192101710c9100062de1c84584614800107d9818b7558910006749c28318a414400143d94989750c73000539646705db328c801a598560c7258031005b8259324852044001ac4861cd32485100062e1db8458930440011f298dc570cc91000536642329db324400185e871d6634c7200063c6057098061cc8375e192a01720c5100061d5d5811d5600c8018f181dc270d8931006aca05841c9600c40107f985d475587200055c654815c032440012e49660a534851000535245641cd61480014ea96201720c52000556654401cd6244001994841cd6354510005e864864505204400189c849cd631891000669e117258831440018ce7220d62d05100043de61711c5600c80183c865d542d051014539a5a805c831440014da96042731891000517654621cd624400158d940837358520004ae26174509600c4017a19418b71481100066a20372509315000187787e15611852000699d9581083624c4014cd97d8f620c9100de7865d820c5204400143f925917519331006175d48358b4144055ce076d892148110006d86146290520440010dd981c8634c51000527652821cd654840143d949cb65d81310050f650525cb65440014d596a0c7348710006b1d958318921440015d1928c07348510004f8660620c520440014d696040735891000678a017290831440010ef985c87258730004b96468090e620c453973805d562905100050f650521d952440013aa98991424811000517656801cd6244001c987418073581210056c25175dc5204400183d75612631852000527e51651cd614800189d84dce73589100047ca60405c43244001479950817018d21006366027018f324840143f9561b745812100517656741cd62440010dd9810073589100043da6020dd9310c40149c9361b745812100535a58211cd60484014d69110073589100073218b635c032440019d2801ce4348510
  | 1 => 0x10055a648535c032540018797560075584320062e1d9849cd20440014b59190a76d09100060fdcd8518d42504010be98d9173d0920006a6a11831c9600c4018ac82dd163589100073218073dc960484015d2968c0734851000707dd4741cd62440016a99408272580310051765462dcd62440012cf9858c62cc91000517654611cd61480018d78720d6118520006b25c083588624400162c9655152509210042fe61741d160cc801a2c8521162189100050f65462dd162440012e591a0243588310064d5d584188314400dae28618b31481100050f65073d8951540019707420d5154110006b4a06831c9600c40186f95e1d621891000527a4c62dd162440018ac94e1d621891000517e55741cd62440015c5921cc325451000699615811c1620c4018ad7460863189100de6c60174988314400158d920c473553420050fa58531d16548001569951007258d100061bdd7825cd624400157191215700c95000535a46801cd6244001c2c72d9542505310053964420dc961cc069cc4761cd32485100043ba60205d831480559e37260831481100047ce5d80cca414400157195101718c910004f864883505204400185f851cd4358910005396467058a420c401c1c751d37358910005e864b43505204400183f766144350b310070d441535d0635440146e9299572d95100060f5d18599262440155e09750b714811000671a0d72188314400149e94a0873589100043be61721cb604c4015d297e07324c1100062b5d38258c6244001aa88610d424811000517656641cd624400149c93597745812100617e147358d604840147696151710c95100533648311d931480015719510273485100060f1d98599142440015e19210172cc510004bae61701c1620c401ac483e0961185200051b65780dd9320c8015c59214c7348510005b82594248520440014ac96611720c540004f426332545304400183f95e1d6419120006d414c835055044001a1f656105318d2100527e5165dcd61480559e29760831481100070754e325d063544014cc925907358910006b15c483588624400154d9214c7348550006a9a05841c1620c469ac583604705883100437a5c8359560484019e287d8a4148110005b86408158921cc001954851cd43485100063361c62d8c32440018ad845ca62187300056c64021dd160484018ad84dc02058831006e4a5083545304400192f20e157190d4200535646739db325441d3d29620d514c110006b8605701c1620c4010bf985d074587320042fa62425db42cc0192f19121d42580310070b1d474dc9624400143d94a177654b3000527e4d65dd160484010fa98081760c5200068bd9584083624c4015719520570cc91000556654409cc624400183d85dd36358520006a3cc584081620c4016aa9290d4258031005e8644435092044
  | 2 => 0x400145f9559373585200063961d6218831440016c791594634c9210052b65020dd931480018ad84dc07058831006a9c4184081620c401aa8869514248110006a34c584081620c40183f7461664589100060f5d98519142cc40173294189515411000655214734c5214400147990d5076549100041fa60545c463550010fb985c070d893100437e5d8218c32440015d1988c07348510064f426063545304400145f95604735891000437e61731cf6150801bc07060c62485100052b65020dc961cc001c4c751cf7258910006b1d918318921440017c19318b704851000635a1873cc92144001bc22020d62885100062d593805c4320c4018e982dc04058b310061be1c8558862440010df97604630c52000517656641cd604840154d921cc32545500061d5d58118e4148001c6575588620c51000732188635c032440014cf925d47358910005cce516354550440018cd972096318d10004ae652829cd600c4018cc835c962d05100041fe61751d562cc00183f766146450b3100536a42411cd62440015959420673189100043b66020dd931480014d5918c073587200060f50d861cd54944015a594219720c510006749c08358831440016e0964c921d011000794d8e635455044001a8e84a0c705883100535644201cd624400146e9214d72d95100061b20b855d83244001c1d5350d7118d54005e86447450920440014ce9608473581210049b66065083624c401aca9020d62189100065c5d5800c8314400189f869cd42d07300063ca1d811c9600c40162c965516550920004bae61721c9600c401475911487654910006332087658f3244037971805d6629051000678a01720c8314400183f75e1173589100042fa5a83dc554508016559114c635492100617dd7835d1624400d2f191a1e43580210041f66272197604c4010df985cc735864200527a50621cd624400149d968c974d83320053624d62dc142440012d591a035318d210042fe61741d1600c8018f07660073485100de5c6017598831440014cd920c0764853000627dd1839d1624400147a9718075581210065c5d58090831440019c47320963545100057424d75dc121440015e290a0d720c510156395c9818806348401ca574588620c5100069ca15811c9600c40145f955907358520006ca5538059542480014b994989700c7300066c5d1800c831440016c791590634c921004b365c8358862440019357461443cc5100069320d32551629440166b9558c624811000627a1f741cd6244001b2b70614645092000587650531cd62944010dd98dd8638c520004f1a62634c921440019e28718a4148110006ac611811c9600c401a3510610635495100517654101cd62440018ad84dca72d8131006781c28718921440014cd9218d700c9510050fe59435d443c84010ef985c8725823
  | 3 => 0x100050f650535da51c80014cf925d8638c52000693615831c1620c401ac48698d3248510005ca654745092044001a3510614635094100713dd473dc9624400183f75e11635891000527e51731cd62440015d093547704c51000665604311cd54d0801a646560420d89310052ba5821dd160484010bf985d074d852000527650201cd62440014ac925917219110006aa6136318920440010de97e0d6558121006b1a06831c1620c4014d49159473585200060fdd58498d31480014ba971807458121005cc2516254550440019557520d6290510005a324d545d1620c4010fa98082760c5200053964670589420c4010bf985d07458720036b82186250520440017c1901cd3248510006b1a4d811c1620c40147a9718375581210053c644209d831480014d59108373589100050f65062dd5314400107e97215635891000517e55731cd62440019b174603320c51000527251651cd6148001559950407358910006b8100864c921440011f29720d4148110006f09418318921440016a99408172580311a4b964487901620c4014b9940817018d2100437662741cd624400183f85dd16358121005cc650625455044001b61855083148110006b1c4283081620c40189f74a0e6458121004bae6170081620c401a8f3161070588310061d597805c432904013d19220d514c11000678219805c831440019d283dcf71481100053c64021dc564cc8014d5910c8764c91000571648635c43254401c1c75dd07358910006555d48358831440014d7915d073589100050f65442dd942cc0019e172e01420c51000693214835886244001b508310d51541100041f660531d952440019e28790831481100052724d741d162440018d787e0d61185200062b6538758862cc00185f7520d7458910006356047118d32480018af829c9641933000476660401cd62440018d67360660987320065c5d5800ca414400145f95618735812100574a40531cd2144001d2b805d542d0520054baa5c8650920440010dd988ca76cc91000555a56301cd21440018b787e11611852000539e45645c831c80014e5911c362509310055c654405c4324400187565e01710c8310ac7ca5c834852044001c657558862905100050f65461dd161480014cf925cc7358910006a9611811c1620c401c1d755d36398d20006b4a0d811c9600c4014ae920c774589100068ec8085590644800191d845d732d07300061de5787584614800107d989db75cc950006f08818218f31440010dd988c07648730005b8259420c5204400145e9318975d0510006f01cd820c5204400143d958c97498d2000533648401cd6244001c1f751d373589100042f65c845966348001ac820600634c921006655d08358831440018d687606634c9100042fa627350b615000155995a0073589100047ce5d80cc8314
  | 4 => 0x44001a8d7420d62189100062b60a72d926444001ae22021932485100060fdd58498d6148001a4f8520d6218910006ca61542d0520440018b6865d0320c5100053ce45645c03148001a2c6561020d89310a4f864a83dc520440194b896509700c540007c8551429452044001ac56560c62485100064d5d784588314400107f985d475d85200053565f635c663484014ad920c774589100060fdcd8418d525440185d85dce73589100050f65062dd562440019d270a0c620c510004b3646831c1620c4011b898509700c54000437e61731cf61480018ad84dca725873000527e51751cd62440015e192103714c910007c8951425452044001c1f75dd073589100049b66020194624c4019e182a0073485100052765020dcd62440019717560332905100060f5d78259064cc0010de981d963cc91000527a50211cd62440014f191081760c52000574a46801cd624400183d756106558b30005356467018e43484018af74e09735891000476660409cc6244001a3651610535843215539a58805c831440010df985cc735832100556656809cc624400145d950807358910006356047698d3244001a3985a107258031147389d8624874044001a1d85610638c951005b864670883624c4010be97a126358520064bc64687cc9600c4014da900847358910007985886254550440010be98dd16358910006d420d6354550440012d591a005318d210047c660409cd2144001b2b20e01545494200517656821cd6244001731948c951541100062e1d98010d42440019e382dc9514c11000693d958214c6348401569951037258d100060f5d582d90424400143e931947459520005ca6544350920440014ad94e1b7258d1000437a5c8650932cc4015c592a0f7150b31006d8617621c5204401d3729620d515411000535a58109cc62440015e390611720c5100052764c215d263480010df985cc73d8910006361c08358942440010ef985c872580310062be1c8458862440695e191201720c520006361d8835c5204411db505420d514c110006a39d08358862440014e591a03764c8320043ba60209d831480019e384601720c510004976625414c63484011cd9808473581210061be1f85588624400183d85dd2645812100437660321d932440010bf985d07458432006d420e635455044001b606261471481100068b4818518d42504015e192100734851000535e45751cd62440019e382dc9414c110005e865062545204400183f855d16318910005b82594288520440017519318951541100055c654405cb31440010be980857498d200065c5d580cc8314400183f84e15769091000517a4c62dd5434400107d988cb75589100060f2578759064480012e89660b4348110007231d073dc96244001996841ce32545100068ba16841c1620c4014d69614c73485
  | 5 => 0x510006741d0835453044001c1f75dd3735891000687d958414f634840195575a0c620c510006331d98290d214c00183f85e117694910005b16466018d32484017a19418831481100043b662205d831c80018ce73e0963189100042f662429db424400107e981d5624c51000617dd48358931440019d07360232545100042fa63745cd62440011e9981007258d100050f65632dd16244001dc2201cd324851000574a44401cd6244001e33649915154110006d414c8348550440018e880dc942587300060f5d58499662440512e4972193248510006655d28318831440255a992211700c94000633e1c83588624400145d931517118d540050f652325d663480018e5726067018d2115539a58205c8314400107f985d47558332006aa2187450920440013e398d88314811000527e5175dcd6244001876865d4329051014d7825d32dc121440015c693081720c51000678201725083144001dc2301cf62485100050f65232dd5624400149c935d774589100055c640855c43254401a8d31610705883100555644531cd2154001d2954509709452000633e5d8218c32544014cc935907258d1000617e147358d6244001e516318d51541100050fa5c8359542d0401b2b706144350920006b4cc9810c9609040113e97e055454d4200556656309cc6244001a8c8420d621891000574a44409cc6244001571959c371cc910006a9c41841c1620c40145d9508373589100052b650205d8314800145d9318b75589100052b653865c831cc0015a994209708c5200042f66272d93414400143c9650d7510d1000678a1f620c52044001876865d4320c5100060f5d78259042cc001c7375dc7705891000695c848558c63484017309458d51541100073888110dc961cc00145d9518073581210050fe49435d463504019d07360043545100053964470589420c40185d95e1d6318d20005876505318d524840107f985d475583210060fdd584995624400186d756086318910006f0dcd820c520440014da971807358121005d424d6254550440018d67620d62cc5100058b65020d94624c4014cc935947258d10006b1a0d811c1620c40145f955d3735891000437e5d8218c3254401a56546045318d21006a3611831c1620c4014ad94082760c52000559648545c43254401a5a8560c725803100527e4d75dd1624400183f85dd173589100060fdd5849d562440019a8805c9420c5400043ee61701c161cc80183e7661664509100043be49861cd5444001a998460c725803100437e5d860c063484014ce92cc17218d100050f654215d263480013e1989083148110005aa25163189204400183d85dd273589100062e1db845c520440018e562e0171cc83100574a42831cd21440015a594081720c5100052d65020dd9310c401a3a85a10725803100572648405cc62
  | 6 => 0x20c4018cd8218873545300052e640421d9424400183f865d543d072000633e1f8358862440010fb985c07058a310068bc818518d42504014b5911087650910006876125414c63484013719220d51541100041f66052dd952cc0014d9900ca76cc910004f864883545204400189f7460e645812100647615841cd514c001f115150e544c1100042f6607610d424400149f9361b745812100696616831c9600c40183f75e11624c510005cce51625455044051ce076189214c11000437660201cd62440019e28718831481100052da5821dd16048401c1d435d463d05210062761d74d8e6348001d19434c175d05100058be595454942cc80183d7561262187300052ea5c60dd1604840145d9508473589100050fe49645d741cc4017c19318921d011000536a58201cd61480018d68360676cc91000699a15811c1620c401571951007348510006d420f43545504411db506520d514c11031f381db62dc121440010bd9898a740c730007381db62dc5204400145e971d473589100043ee61701c1610c8018757560463185200060fe197550b41cc0018f1716007158b300061e6157018063484016c89358862d011000533a4a641cd624400149d9418873589100051765460dcd60484011ea981037258d10006369438758c634400143f9650d75d072100738a5a205c831440017539358951541100041fe61751d561cc801c5732595710ca4100517a5f5394d62440014da97183735812100527251751cd624400143d941d576cc9500074595073d0d5144001dc2301cc62485100053364a741cd624400189f8420d760c9100060fe197550c43c800d2e8972194248110066b460d811c9600c40143d9598974d8b30006939d48358862440015559504073589100041fe61751d5610c8017a1919514248110006b10c8864c9214400143e972096550f410068b615841c1620c40143c9650d75d0510005e864840dd121440011f3976003290510005936546018d324840107e9814d76945200062bdd1829d161cc00195575a0c6290510006475d78250f41cc00143d9414d76945200056a650825c031480011f29720d51481100064721e5450d51cc0515e296a01720c5100043766020dcd62440013c59120d544c9210061761e85d8e634800143f925917510f3100539259845c831440f7ac88018d424c9200062e21d74509600c40193875211754811000556654109cc624400183f766146450b3000517654401cd624400186d75e096318910006d420c3254550440018d5861cf324871000437e617618e4348401875855c4715803200517a4c52dd952cc0018cc93e1d62189100060fdd98510d42cc001ac99020d62189100053c644635c241c8001a9a84a0c7258031005ca6566450920440014d89059073581210055c656809cd21440438e476e097348
  | 7 => 0xc91000437662641cd60484018af94e1d6218910006176177398d61480018e476e09634851000533a48401cd624400197175e01420c5100052764c21dd1624400183d75e11631891000533648635c432544015d191080735852000678e61805c8314400149e940807358910006a3e108358862440192f191a1e4358031005aa25942d052044001b6185508714811000678611805c8314400189f849cd63189100055c654715c332440014da96083735852000536a58101cd62440015e190a0d720c5100062e1d98418930440017529318951541100043725d8399160484014b89650970d05100060f5d18519262cc0018cd829cb6398d100051b656705db328c80185e87dd47358910006f01018318921440017c193189215411000678e4a870c5204400183f75612735891000517656649cc62440010ef985c07058831006aa612721c9600c4018e476608634851000527a52741cd62440010bf985d074d8121007348c1101cd61c8001a4d85a0c70588310048f65883551429440107e9721543589100062d619740c8314400183d746166498d100060f615741d162cc001ce372dc77058910006874c18418d5254401aa84221942481101a5b864470881620c40145f95610735891000627e107358d6244001ac71020d70588310dcf8261324852044001c54751cf7158910006369d88358b40440018e6726067098f21006696117218831440017c19218d214c110005d824963545504400183f7561275d89100063320a7658f32440015c992103735891000569650805c8314400143d9498975193310053aa58825c03148001dc093601720c5100041fe61751d561cc00143d9510876509100051b65680dd9320c8010bf985d07458321006b8606701c1620c4015e29090d720c51000517654421cd624400123d98d9454d91200043de61711c562cc001c1c75dd37358910006785c980908314400183d766146450b30004b5e616318d51440016e09650b31481100060f617749d362440015c99210073589100060f612861cd54548014e696a0d720c51000565650531cd21c40018d47620d625051000574a43531cd21440018af87e11621891010e2b21b725093150001672960c951541100070e1d4601d160484015d2918c273189100060f5d58419662cc0010df985cc7358910034dca5b8254550440014d5919c26390c2100533a58201cd614800185d875d76398d2000535658531cd21c400170c935515250b3200527652821cd6244001c38751d3705891000527a4c42dd942cc001c8f741cf72589100060f5d18519063480514e696881720c5100051d644635d641c80015a890611720c5400041fe61751d7624400d2e89660b41481100042fe61741d362440015e19090d720c5100060fe177458d6244001b61859083148110006a9a11811c16
  | 8 => 0x624400125d9620d54cca51006e8613620c520440010bd988cb74589100053324d87d8a62440014ad940837258f10005cca523254550440019e182600734851000565650531cd214400183f85e11760c91000527251731cd6244001a8d84a0c7058831005e86506294520440015559504273189100047ca60715c33244001ab2846047258031006a3a11831c1620c4015e290e11720c5100062edd98010d42cc00183d7560b64991100060f5d58499462440014cd920c3764873000547650531cd21540010bf985d0745873000535259731cd214400197384dc9515411000639e197250831440014cd9720f620c91000627210835d832440014ad940817218d100061b20b7558d62440014ae92d917299330004dca4f82545504400143d9119474595200050f650535c36254c01875865d4320c5100061b6578758862cc0015c992102731891000555255731cd21440011f19810073485100052765062dcd6244001a57656045318d210051765a325d760cc80183f85e11768c5200057124d205c831440010be9721163589100de7860172988314400143e9620d7510d420062b20b845d8324400143d9498b754c7300060f61574d8e63480017c19290d214c1100052b65380dd9320c801ac710a0c70588311fe3364f8758862cc013ae086d892148110006cad818510d424800162d9408065189310061d619750ca41440013959120d5450831006749c08358a4144001559951017318910006272107358d6244001ac84020d62189100042fa627650b41cc001dc393601720c510006551d4835d521440015e1902057290d2100536640321d9324400107f985d475580320052764c62dd1624400189d879d36398d20006e450d8195130440012d79160b5318d210053365f83d8832440012e89660a54481100060f6177498d614800145d961cd325525100533644635c8314800157195dcf71481100060fe61645d464cc401c1d3054d7418d5100533a5820dcd61480019e070a1e3248510006785c9800c8314400143d9414d72d95100059a6566418920440010ed98dd862cc91000517656411cd62440019e2805cb320c510006b11888358a21440014e99210171d81320062b611701c1620c4011f397600320c51000517a4c62dd5314400187495e1d61185200041fe61751d7604840143d95087745891000678dca870c5204400189e8358f7155342006cad818519142480015a994209700c7200042f6607498d6148001cc71018d720c520006359da8318b314400157195103714c9100dc7c66373dc520440010bd980c774589100069521483584614800183d746146498d2000617e167358c62440015c693219720c5100050f650531d95244001571951d371481100060f5d582d93414400183d75e096410f300051e640521d952440014d5918ca76c
  | 9 => 0x508310060f5d1859906244001a1f306106354951006a6612831c9600c40183f70610635495100571648531cd21c400197083dc9515411000437e617618c3244001c57211d4634c5210042fa5c845956148001c3764951710c95100517a4c62dd5624400185d851cf63585200051b65680dc963440015d1900847358121005356447018d43484539b3805d1620c51000527a4e425db42cc001d2b605d542d0520004b6e616318d5044001ba184188314811000587a4f8259543d04018da76a0c62d0110007c44c11050d549440163b9055365d911000517654641cd614800183d756107558b3000647a15841cd514c00183d855d26498d2100738a5a805c83144001b6185d8a41481100068ba096590d420c4192f19121e425803100555654819cc62440014d5910ca76cc910476d4d4883545304400192d20e157190d420051b65786dc963440014cc9361f62c85100042f66042dd942cc0010bd98108765091000533249305c8634400145d9019473595210044f6607519143480018ad845c020d8931006aa21a64509204400143d9499572d9510004b92598290d21440018cd87188630c910006a521083584614800149e971d0735891000571a4c805c831440014ad94080764c520006276137398d614800189f74a0e745891000533a4e80dc963440019d0801cd43485100054e255741d120440014ad94a037258d100060fa1f751d162440015399414d700c950007320ca201d9324400107d9814876549100043ee61701c1620c401b6185d883148110005aa6584350920440019d07360032545100050f65431dd16244001a718560472580310042fe61741d16244001a2d85a10705883100563650201cd61480015e19210273485100041f658874c9549440143d9414f7654b300043de61761c732440018ae82dda43508310053a25d62189304400183d85dd2745891000578648405c632440012cd9898c62cc91000633e4f875886244001c351050d7518d410067120d72588314400183f7561265d89100052e642429db424400143d94a1476549100063a1c18218d42440379e092a1c31481100051b654205c8634400183d8461873552510042fe61741d162cc0014d6968c0734851000527a4c621d16244001ac56460c624851000578643845c8314400189f84e0d768c52000527650211cd624405157296dc951541100062ba538758862cc0698ac865c9420c54000678a19805c83144001a3a856107258031006561cd800c95154001ac980180634c92100617a578758c63480015d19108373585200061761e75d8e634800183f865d542d073100539e45645c83148001c94741cf715891015578e49805c83144001a4d7520d621891000533249635c86344001cc46218d710c910006879458414c63484010f7985c47158332006b29c083588
  | 10 => 0x980100041c048000000b0648048aa2880282a00420c018283aa000010040020100383701c0082d0060101780100505e0200000b0000002089f18e0883d00300602c620610100000009400253c2980300a03c0483c00008400a990180001605508e2c8b4801096118000250000840000106c0000180100e0000182a07e004a20730002680a00310a08c040300363b805016010098000000048941000c0320000280300667800005250009ae03102a0183f908008550fd00000057c0180a0000180388d02c06c12812012004730a30000000000301c004b50030020100014f0aa0b13c8050000480b80012c3d00202800a0241182500400c0417715e394008d301a00401826014b642700409054c0a0214b205401109030044000300440000400201403c03808018011258010ec0040d0010060854db290440002700e0000002a82e00a3dc1b8040120182800405c0040780a0001000003c002510090190080301b8040020140100a0002cc000000f000400000010034120010500ad7700600400811808000074028020460040c00a0320580087f0000000a807008010000010d40041980601064c0100f0001c80100814403c138000320040308000403c0b802000030088010080042083c0000045102d008034000240000002b8180102000103a1b0094010010002040003700200c110000be5c00080202cda80001626e138030370020200c01301038c0c1063780a00c89000000001009018a58010210041b00e84e09a0708c8dd007864c16050d54944014cc92594735891000633208835d832440018ad84dca625873000571648730c951c4001b6185188314811000617dd6839d56244001a2e8561070588310063a182878c960484532e69721932485100058b2595454942480018e562603715083100617e17835da314800149e93087745891000437e61731cd61c8053973805d5620c5100061761d85d8e6348001879855c07058432006785c980cc8314400183d7560b6410d10007261d073dc162440014e996e09700c72000678a1d420c520440010df985cc73d812100535a5a831cd21440018778721561185200059c6583254550440012cf9720d62189100063961972cc831440014cf925d073589100053a64840dd9324400183c76614435091000535a44201cd62440017a19418b314811000574a46809cc624400155995103735891000578241845c8314400168c9355162
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x68018108040811000a210780452000b0048a18200011ab002183802919a0a15841cd514c001588d20a641a42a822000a70688736003254510005583401910c99242880033408324963545504400180ec1b2839ec4a8aa000ac86906261471481100064510cca886a124088003c1130441535d06354401498d08ea422ea9022000ad06885320d215411000686320882a6ba0c6a88034c076640734c921440019894a107192a2a822000a52688736003254550004d0b4249aa8ba2c4188033109420d635455044001a0a38b28298c6a92428fe441d05320d41541100052a3403a906baa428800308d86648311cd54d0801c44ba2e041ac43122000c9265580180634c921005543422110ca1240880030c5975c48358862440018c2c9302188e6aa68400cc86159418831481100065810cc80e699242880022a9a9218435092044001c882a0e841aa29822000994ea56318d5154110007442408830a31a84a0803a11304418418d52544019144332b322849022000c8a2598550b41481100051934e20106b10c4880029c2a7101831892144001514532a9c02caa124000ad06944060c62485100066232aca106a8a6088002b41a51c18318921440019144332a3a2849022000cc4a559420d514c110004d0b4249aa8b1284188032a0866447450920440015a0d1106192a2a822000a4c69083dc9515411000701aeaba106b10c48800308d975d083588624400128ad4ca839e86a8a20008b26a44020d62189100054934a1030031a6490802a29a5108865092044001826cbaea41ac43122000a3829984601720c51000598342194403b264880029a1a4219805c831440018d143b28310629022000e0c5c11061063549510042e3523a106a8aa088002710a9545439513044001c883a10621aa2a822000aa269020600634c921
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80010061119369083dc95154110005030b86411054d7418d51005411b01c59414c6354921004911ba1d08310d5154110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x204432d9369083dc95154110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x94e
  | 2 => 0x98e
  | 3 => 0x150e
  | 4 => 0x168e
  | 5 => 0x180e
  | 6 => 0x209
  | 7 => 0xb09
  | 8 => 0xb0e
  | 9 => 0x1409
  | 10 => 0x1549
  | 11 => 0x154e
  | 12 => 0x249
  | 13 => 0xb49
  | 14 => 0x1449
  | 15 => 0x16c9
  | 16 => 0x16ce
  | 17 => 0x184e
  | 18 => 0x3c9
  | 19 => 0x3ce
  | 20 => 0xcc9
  | 21 => 0x15c9
  | 22 => 0x1709
  | 23 => 0x170e
  | 24 => 0x40e
  | 25 => 0x188e
  | 26 => 0x58e
  | 27 => 0x98a
  | 28 => 0x94b
  | 29 => 0x98956
  | 30 => 0x9c956
  | 31 => 0x180956
  | 32 => 0xb0956
  | 33 => 0xb4b
  | 34 => 0x16c956
  | 35 => 0x16cb
  | 36 => 0xb8956
  | 37 => 0xb8b
  | 38 => 0x184b
  | 39 => 0xbcb
  | 40 => 0x8a
  | 41 => 0x150a
  | 42 => 0x128a
  | 43 => 0x58b
  | 44 => 0xe8b
  | 45 => 0x178b
  | 46 => 0x18cb
  | 47 => 0xecb
  | 48 => 0x17cb
  | 49 => 0x104b
  | 50 => 0x194b
  | 51 => 0x138b
  | 52 => 0x24b
  | 53 => 0x144b
  | 54 => 0x28b
  | 55 => 0x148b
  | 56 => 0x14cb
  | 57 => 0x4b
  | 58 => 0x124b
  | 59 => 0xd0996
  | 60 => 0x160996
  | 61 => 0xcb
  | 62 => 0x9cb
  | 63 => 0x168b
  | 64 => 0x12cb
  | 65 => 0x10b
  | 66 => 0xa0b
  | 67 => 0x180b
  | 68 => 0x130b
  | 69 => 0xa4b
  | 70 => 0x134b
  | 71 => 0xd1516
  | 72 => 0xccb11
  | 73 => 0xccb16
  | 74 => 0x15cb11
  | 75 => 0x15cb16
  | 76 => 0x171411
  | 77 => 0x16d556
  | 78 => 0xcd551
  | 79 => 0xcd556
  | 80 => 0xb4251
  | 81 => 0x16cb51
  | 82 => 0xccb51
  | 83 => 0x170b51
  | 84 => 0x16d451
  | 85 => 0x3d451
  | 86 => 0xcd6d1
  | 87 => 0x1716d1
  | 88 => 0xcc3d1
  | 89 => 0x170cd1
  | 90 => 0x1715d1
  | 91 => 0x198b
  | 92 => 0x19cb
  | 93 => 0x5cb
  | 94 => 0x1a4b
  | 95 => 0x1a8b
  | 96 => 0x949d6
  | 97 => 0x20b11
  | 98 => 0xb1411
  | 99 => 0x140b11
  | 100 => 0xb0211
  | 101 => 0x141551
  | 102 => 0x24b51
  | 103 => 0x256d1
  | 104 => 0x1456d1
  | 105 => 0x94b96
  | 106 => 0x1403d1
  | 107 => 0x141711
  | 108 => 0x243d1
  | 109 => 0x1443d1
  | 110 => 0x255d1
  | 111 => 0x21551
  | 112 => 0x154b11
  | 113 => 0x155411
  | 114 => 0x144b51
  | 115 => 0xb5711
  | 116 => 0x16d711
  | 117 => 0xb0cd1
  | 118 => 0x3c251
  | 119 => 0x94996
  | 120 => 0x21411
  | 121 => 0x3d411
  | 122 => 0x154cd1
  | 123 => 0x3ccd1
  | 124 => 0x15d711
  | 125 => 0x3d711
  | 126 => 0x98d16
  | 127 => 0x99616
  | 128 => 0x150996
  | 129 => 0xcd711
  | 130 => 0x15ccd1
  | 131 => 0xa0113
  | 132 => 0x181516
  | 133 => 0xb15d1
  | 134 => 0x1555d1
  | 135 => 0xb4253
  | 136 => 0x15c251
  | 137 => 0x24b53
  | 138 => 0xb0cd6
  | 139 => 0xb15d6
  | 140 => 0x154b16
  | 141 => 0x1556d6
  | 142 => 0x249c95e
  | 143 => 0x5c2495d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 41
  | 8 => 875
  | 7 => 6683
  | 6 => 7040
  | 5 => 1208
  | 4 => 63
  | 3 => 4
  | 2 => 1
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
  | 2 => packedAt gbK2 (i*103) 94
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
  | 2 => gbHint (packedAt gbK2 (i*103+94) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 10 => 2*((h/1+packedAt gbK10 (15+(h % 1)*1) 1) % 1)
  | 9 => 2*((h/41+packedAt gbK9 (1066+(h % 41)*6) 6) % 41)
  | 8 => 2*((h/305+packedAt gbK8 (32375+(h % 305)*10) 10) % 875)
  | 7 => 2*((h/2227+packedAt gbK7 (320784+(h % 2227)*13) 13) % 6683)
  | 6 => 2*((h/2360+packedAt gbK6 (415360+(h % 2360)*13) 13) % 7040)
  | 5 => 2*((h/402+packedAt gbK5 (84560+(h % 402)*11) 11) % 1208)
  | 4 => 2*((h/35+packedAt gbK4 (5103+(h % 35)*6) 6) % 63)
  | 3 => 2*((h/8+packedAt gbK3 (368+(h % 8)*2) 2) % 4)
  | 2 => 2*((h/1+packedAt gbK2 (103+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0f8783c3f87ffff1fc03c07f16313cc19f793
  | 1 => 0xff07803fc3f87807e3fffff802bc1c7066c9fc
  | 2 => 0xffffffc003ff8007fc003ffffcc0e07f870e1f
  | 3 => 0x7fffffc000007ffffc0000f00ff83f80fe0
  | 4 => 0x7fffffffffff8000000000fff0003fff000
  | 5 => 0xfff8000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x6848080c0480ca330641a412602111c4085391
  | 1 => 0xa9410014418850512294a950202c145022c0b4
  | 2 => 0x1292b24002550084480212a584c06029850c0a
  | 3 => 0x4dcaaa8000126912b0020cb00aa82d80f40
  | 4 => 0x10876733336625c0000c00c10fd6000377a000
  | 5 => 0xdce0060220444600023023060ffbdf7c000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 8, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 7, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 5, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 6, 0, gbRaw),(0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555, 5, 0, gbRaw),(0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0x33003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 5, 0, gbRaw),(0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 4, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 4, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfeeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36274
namespace PEqualNP.Outside.L_meta_36274
open PEqualNP.Outside.L_meta_36274.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 21 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 71 := block_range (n:=71) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 551 := (concat (concat bs0_4_0 (concat bs0_4_96 bs0_4_192)) (concat bs0_4_288 (concat bs0_4_384 bs0_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 90 := block_range (n:=90) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 666 := (concat (concat bs0_5_0 (concat bs0_5_96 bs0_5_192)) (concat (concat bs0_5_288 bs0_5_384) (concat bs0_5_480 bs0_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 40 := bs0_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 6 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 90 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := bs1_5_0
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
theorem bs2_4_0 : Interval s2Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 64 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 40 := bs2_5_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := bs4_5_0
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
theorem bq4_2_0 : Interval q4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq4_2 : Interval q4Atlas 2 0 3 := bq4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_0 : Interval q4Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq4_3 : Interval q4Atlas 3 0 14 := bq4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_0 : Interval q4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allq4_4 : Interval q4Atlas 4 0 13 := bq4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_0 : Interval q4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_5 : Interval q4Atlas 5 0 1 := bq4_5_0
theorem allq4 : ∀ k ≤ 5, ∀ i < count q4Atlas k, checkRow q4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq4_2 i (by omega) hi
  · exact allq4_3 i (by omega) hi
  · exact allq4_4 i (by omega) hi
  · exact allq4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 9 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 14 := bq6_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_5_0 : Interval q6Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_5 : Interval q6Atlas 5 0 1 := bq6_5_0
theorem allq6 : ∀ k ≤ 5, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_3 i (by omega) hi
  · exact allq6_4 i (by omega) hi
  · exact allq6_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_2_0 : Interval q8Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 4 := bq8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 9 := bq8_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_4_0 : Interval q8Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq8_4 : Interval q8Atlas 4 0 9 := bq8_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_5_0 : Interval q8Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_5 : Interval q8Atlas 5 0 1 := bq8_5_0
theorem allq8 : ∀ k ≤ 5, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_2 i (by omega) hi
  · exact allq8_3 i (by omega) hi
  · exact allq8_4 i (by omega) hi
  · exact allq8_5 i (by omega) hi
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
theorem bq10_2_0 : Interval q10Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 4 := bq10_2_0
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
theorem bq12_2_0 : Interval q12Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 4 := bq12_2_0
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
theorem bq13_2_0 : Interval q13Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_2 : Interval q13Atlas 2 0 1 := bq13_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_3_0 : Interval q13Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 5 := bq13_3_0
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
theorem bq14_2_0 : Interval q14Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 1 := bq14_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_3_0 : Interval q14Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 5 := bq14_3_0
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
theorem bq16_2_0 : Interval q16Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq16_2 : Interval q16Atlas 2 0 4 := bq16_2_0
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
theorem bq17_2_0 : Interval q17Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq17_2 : Interval q17Atlas 2 0 3 := bq17_2_0
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
theorem bq18_3_0 : Interval q18Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 1 := bq18_3_0
theorem allq18 : ∀ k ≤ 3, ∀ i < count q18Atlas k, checkRow q18Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq18_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_2_0 : Interval q19Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 3 := bq19_2_0
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
theorem bq21_2_0 : Interval q21Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq21_2 : Interval q21Atlas 2 0 1 := bq21_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_3_0 : Interval q21Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq21_3 : Interval q21Atlas 3 0 5 := bq21_3_0
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
theorem bq22_2_0 : Interval q22Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq22_2 : Interval q22Atlas 2 0 3 := bq22_2_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 4 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 63 := block_range (n:=63) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 63 := bgb_4_0
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
theorem bgb_5_1152 : Interval gbAtlas 5 1152 56 := block_range (n:=56) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1208 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152))))
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
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7040 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)) (concat (concat bgb_6_1248 bgb_6_1344) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1824) (concat bgb_6_1920 bgb_6_2016)) (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 (concat bgb_6_2400 bgb_6_2496)))) (concat (concat (concat bgb_6_2592 bgb_6_2688) (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976))) (concat (concat bgb_6_3072 bgb_6_3168) (concat bgb_6_3264 (concat bgb_6_3360 bgb_6_3456)))))) (concat (concat (concat (concat (concat bgb_6_3552 bgb_6_3648) (concat bgb_6_3744 bgb_6_3840)) (concat (concat bgb_6_3936 bgb_6_4032) (concat bgb_6_4128 (concat bgb_6_4224 bgb_6_4320)))) (concat (concat (concat bgb_6_4416 bgb_6_4512) (concat bgb_6_4608 bgb_6_4704)) (concat (concat bgb_6_4800 bgb_6_4896) (concat bgb_6_4992 (concat bgb_6_5088 bgb_6_5184))))) (concat (concat (concat (concat bgb_6_5280 bgb_6_5376) (concat bgb_6_5472 bgb_6_5568)) (concat (concat bgb_6_5664 bgb_6_5760) (concat bgb_6_5856 (concat bgb_6_5952 bgb_6_6048)))) (concat (concat (concat bgb_6_6144 bgb_6_6240) (concat bgb_6_6336 (concat bgb_6_6432 bgb_6_6528))) (concat (concat bgb_6_6624 bgb_6_6720) (concat bgb_6_6816 (concat bgb_6_6912 bgb_6_7008)))))))
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
theorem bgb_7_5664 : Interval gbAtlas 7 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5760 : Interval gbAtlas 7 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5856 : Interval gbAtlas 7 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5952 : Interval gbAtlas 7 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6048 : Interval gbAtlas 7 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6144 : Interval gbAtlas 7 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6240 : Interval gbAtlas 7 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6336 : Interval gbAtlas 7 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6432 : Interval gbAtlas 7 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6528 : Interval gbAtlas 7 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6624 : Interval gbAtlas 7 6624 59 := block_range (n:=59) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 6683 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672))) (concat (concat (concat bgb_7_768 bgb_7_864) (concat bgb_7_960 bgb_7_1056)) (concat (concat bgb_7_1152 bgb_7_1248) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1728) (concat bgb_7_1824 bgb_7_1920)) (concat (concat bgb_7_2016 bgb_7_2112) (concat bgb_7_2208 (concat bgb_7_2304 bgb_7_2400)))) (concat (concat (concat bgb_7_2496 bgb_7_2592) (concat bgb_7_2688 bgb_7_2784)) (concat (concat bgb_7_2880 bgb_7_2976) (concat bgb_7_3072 (concat bgb_7_3168 bgb_7_3264)))))) (concat (concat (concat (concat (concat bgb_7_3360 bgb_7_3456) (concat bgb_7_3552 bgb_7_3648)) (concat (concat bgb_7_3744 bgb_7_3840) (concat bgb_7_3936 bgb_7_4032))) (concat (concat (concat bgb_7_4128 bgb_7_4224) (concat bgb_7_4320 bgb_7_4416)) (concat (concat bgb_7_4512 bgb_7_4608) (concat bgb_7_4704 (concat bgb_7_4800 bgb_7_4896))))) (concat (concat (concat (concat bgb_7_4992 bgb_7_5088) (concat bgb_7_5184 bgb_7_5280)) (concat (concat bgb_7_5376 bgb_7_5472) (concat bgb_7_5568 (concat bgb_7_5664 bgb_7_5760)))) (concat (concat (concat bgb_7_5856 bgb_7_5952) (concat bgb_7_6048 bgb_7_6144)) (concat (concat bgb_7_6240 bgb_7_6336) (concat bgb_7_6432 (concat bgb_7_6528 bgb_7_6624)))))))
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
theorem bgb_8_864 : Interval gbAtlas 8 864 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 875 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 (concat bgb_8_288 bgb_8_384))) (concat (concat bgb_8_480 bgb_8_576) (concat bgb_8_672 (concat bgb_8_768 bgb_8_864))))
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
  · exact allgb_2 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 6 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 6 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 6 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 5 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 4 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 4 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 5 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0feeefee0feeaece0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq4 : Complete q4Atlas) (certq6 : Complete q6Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 8 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555 : Sig) 5 :=
    slice_correct (ms:=fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x33003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 5 :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 4 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 4 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075680 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36274.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[2,3]⟩,⟨.and,[5,6]⟩,⟨.and,[4,5]⟩,⟨.and,[0,2]⟩,⟨.or,[0,7]⟩,⟨.or,[6,9]⟩,⟨.and,[1,12]⟩,⟨.or,[4,8]⟩,⟨.and,[11,14]⟩,⟨.or,[13,15]⟩,⟨.or,[10,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36274

open PEqualNP.Outside.L_meta_36274 in
theorem PEqualNP.Outside.L_meta_36274 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq4 allq6 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allgb)
