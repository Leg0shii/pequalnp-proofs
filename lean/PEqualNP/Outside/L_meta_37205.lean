import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37205.Model
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
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
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
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
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
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
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


end PEqualNP.Outside.L_meta_37205.Model

namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
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

def SBf (j : Nat) : Nat := [8, 6, 6, 5, 5, 9].getD j 0

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

end PEqualNP.Outside.L_meta_37205

namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x8300568b0040c00080171011020451803072c0016fc41fd42fc32fd10ff43fd32fc10fe32fe10fd41bf41fc31fe31bc40fc21fc30ff42ff31fe40fe30fd21fe21fe20ff10fe41fc42fd20fd43bd41ff41ff32ff40ff20fe43be40fd31fc20ff30fc43fc40fe42fd30fd40ff21
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x283bf54443be8721df55320dfa10817c504c678a898770c430dfa0e417e54082faa7a0efd5132de206417751483be64195714d10de21a83bf429037a85205f94432bf2a2417f544c2faa890efd0740bf2a0615e53886fea998df94230bf29083bf4390ed8a4985f55021bf2a665f4318427ca820ef90320bf2a441b751506faa5105f54041dfa0081bd50506fea790dfd4d42bf29021f451482fca1207bd0b32bea92217e53902faa1995f94641de2a241bf409037e82887d90441b6292217d53483ec6218df55220de988817e50883be61185f94232f721085dc430cb7ea2a0df55240df282837e50102faa1a0fbd4930ef188617c540837ca1a0efcca40be29a43bc408837a63206f50840bea9885bc421037843205fd5132f799441bc52506faa421ef10f41be2a441df438cafaa4205f14e10bf2a0637f5050ef8a2a1ddd4530bf296217d50d0f7c81105f55032bfa8a417d53902fea910778ca30bfa9281bc31902f8a0a0df946429eaa483bd43102faa2196f50e40bea96815c5348378a2206f94440df21881bd410427ca910cfd5110b7290217f54886fea2986fd0941bf296613d54042fca3a16f95031bf28861df300c2faa3986f50731df20661ec42ccaf8a5086f55231be2a663bd51102fca3205f94341df20a837e508c7bc60985f14143fd982617f5250fda84215f15221fba0a83bd54042f8a8987bd0832bea9061bd54886f8a9985fd4f20aea9c43dd4310fd843104fd5210bfa9a417d54442faa190df94a10bea9c41bc535077e82087b48720fa880217d529039a6419778c830de20461bd321037ca4205f94b40de21c857f54c837881985f54831b629287bf41cc7e843085fd4c21bf29e81bd32902fca7a15fd5030be290217e54cc7ee21085f94242bf29c857d520427aa9985f94e21bfaa661df430ca7ca9886f50720be29a217d52cc77e8320cf55031f790e417d54ccbb865186f90b41bea8c217e50c87ba60184f54640bea96613d54c437e64205fd5021bf2a4437d5190efaa920dfd5310deaa043bf42d07f640907bcc932bf29c417f54442fca4887d48421bfa92637c54ccbbc63186f50620dea0a63bc40c43ee8320ef10a40bf286877e518cbf680a05f948309e2a265be531037842205f94e43dea1283fb4090378a9087b94810bf29e837e51cc2fca6905f55010bea8e417d53c42faa3a1df15030de20261be21903e8a2985fd5210fb90c217d53d0bbc8621ef50431bea9a43bf53902faa998ef90310df194817e538437aa620770c830dfaa241bf414c6fea2997d88421be28285bd43507d865106fd5130fb90c43f731042faa620df95041bf29085ec5250ff621084f95021bf294877d5110afca6885f94f20be2a065bd418c7f440106f15130fc880217e52902fca3186f90130df29683bd4310efca9887b54a31
  | 1 => 0xe53887d86590ef50440df29c817e51c82fea2a0774c730df2a6217e544437aa9986f0c941bf28043bd52103f280205f95210efa9a41df314c2f8a9185fd4a10dfa0a437e5310efca2105f54632dfa90817e50cc77aa9885f14940bea9e417f524437ca6a0df95330fb98c63bf4210b7a83185f95131dfa9481bd41887de64105f54440beaa4637e530c37a8290efd0610bea9a215c5350afca3105bd4930dfaa4217c54c42faa021dfd5321de28683ec32486fca418efd0721bf29881dd53042fca690dfd4c109faa2417d530877ca3204f14141bf29483ec21083ec20885754c10fa98863de324c6f8a710ef0cb41bf28887bf50506faa7217e90040dfa1a83fb1044374a0206fd0630f7a14857f504c6bea6884f15110fd180617d548877887205f14f20bfa9a837d509077e8318ef90d43ef98c63bf51902faa221efd0c43bf29865f710042f8a918cf950319eaa0656d528c7e842085f94c10bf28e816f5250f7ca810df14c21fba8a417e51887ba62986f14b41bea80857f53882fca7886f50520bfaa241bf43d077880885f94342beaa421dc5350b7e82186f54e40f7a9221bc53902f8a4985f94832bea8e65dd53886fca2086f10c40dfa0c437d53083de42905f15121dea0a817e5290b7a82187b88521bf29663fb208837aa5205f95232dfa0c81bf43d0b7a8220ef50420bfa9c213e54c837c80885f15021bea84857d5290f7e62205f14910bea9881bd4210b7a83205f94643bea90837f52c43bc649957d4d42bea8043dc5344378a6205fd5232be28a817f52507b86498df54e30ef18a63be42902fca6215f948409e2a421f920082faa3104f94341f6190417d52c42fea890df94c21dfa98817f548c2fea918df15110f7a1285ed21482faa5a1ef14141dea1683f731843d8a4884f55320bf28e877d5090fee42085fd4543df21885be311037e8220df54430bf29043bf411037e82105f94010bf28885bf415037e829077cca32bf2a243be540cafaa3184f95231df294816e528c77aa5a0dfd4142be296217d51d0ae8a2985f54642de218857c5350bea8220df15131bf29c83bf52d067ca8196f543419eaa043dd320cb7aa6a0ef505109f284817c5150af8a2985f55321bf294653f544c37aa3205bd4910bf298837d54082fca1997b88420df21081bc40043dea4a1df54c10ee18c61be42507b8a6905fd4810bfaa0217d52887de41105fd5032df20881be53d06fca218dfd5020be2a643be40042f8a29977d0d439f28081be54cc2fca8995f94041deaa641be54c82fca210df54e41bfa9a217e548c67ea8995f94f21bf2a6417c54842faa790df55230df21c81be41902fca01857d4d20dea9283be321037862205f95043be2a465df5350bf420086fd0d42be29287bc53d06faa5a0dfd4121f6900417c504cb7a83a06fcc640bfa8
  | 2 => 0x28086200a200040c8bc0a0b0010cf059a00b008088580284a010360a004f10000006f04018000100185408000348000006430824058000080a1c80002808020b086856018020000c000128c966040603000002002150060086e000020b814000a01f800598000406a0011c009ce0314a0b010748000a0340587a0a01a2b8780c8221c864010020990400004688000c00e0680c04016030007f0120a00009026100860287c078443602c051fa01010040004d00a1181cbe8181304c20014018a000800000080000445026018fe00000c985a26824050000482a37800098185995202808560360b0001b060438001f810710021100e028160600613806960023104003b461981409828110120180a0200e038040116a108000081a020081491c0089a55972000073b000170000400a1261426020090020102e7a03c05840141d603818009f60001c038000bfbcca32bf294617f524c2faa818df55131dfa0c417d544c2e8a2906f95010dea1e837d51902fca1087dc8521de19081be43506fca5a1df55310dfa1485be52507dca518df54e32dfa08633c54482faa8995fd5031fd98461bc40843be6218fb4c832dfa86837e5210efea0996fd4d41df90881be40842fea6a05fd4e21de992837d53887dc43105f145209eaa463bf2190378a4205f54a109f2a0217e511077aa818ef0ca40df2a463ef20082fea690df54342de212837d54cc37e87205f54420bea8e817e52082f8a498df54031dea0e61dc438cb7aa7a0df54331bf2a0857e530c7d8a4985f14c10df21e837c544cafaa520ef48440df196833d51102f8a6a0df95230df992837d53842f8a6906f88440df21285bd21903de6590df94032df18c81bf52506fca810efccb41be29e43bf53d07eea298774c431dfa8881bd32d077c81185f15031be29a81ee20482bca6085f14e20f799243bf43102faa110ef14640dea08437f53c4378a5205f55030bf2a0657d54482daa4087794c10f6a90217e54102f8a090fbc8421df192837d53d037c80186f50710df2a4437e51102fca6106f55032bf2a6437e5010af8a9905f94b41de2a265df31cc2f8a8907b10832de2a221bf41cc2faa118df14941bf280877e509077a87a15f54e31f7190657e500c6fea6106f90020fa188217c53082faa1195f95010de20061bd414c3da4210df94a31bea8065be4390bee6298df55232beaa4857f544c77880106f10440bea94617e50082f8a7885f95130df20241df53443bc6598df54a319eaa443bf41086fca121ef10b41bf284437e518c77880905fd5332bf28e65bf41c437883207e4c030df20281bd401027ca9986fd0530df28081bd418437a86a15f55243f790c437c54042fea2a1770cb31dea0e43d
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4321023e6494c30cd146404823c6454c208f59741c826d6214c108f19153442b661cc941d9d48514c25d6510c328fd9150c863f654c9418fd91500865c6354021c794f418866e6215030c7d4c404823f64540318f585540426c62551308f982548c6b56194d41abd8943d066f6254031ad584400427965840108f592518c2b860507208f587544c23e64951308fd8554cc23d6414b109758c540427b6055131a718d521032d52900108fd9150cc67b65480209718d528438e544c8328f592510863d6494d208f994211032d5494810d914a104423d6590440c7d4d414431c53d05108f994544431d53d0410cd147414c25d63d5220aed8153506ac6254c40cd545211032c5210130b998732486ba60d4440d394e520425e63150109b58b530429d6388640a7d8d525069d63146409b98b548c66d62150308fd91508863d64d4121ab58851102af6254f419dd85544c25f6355121cbd4a404426e62949109758e544432d5210b41c714c404823c64542328f590530863d6595021ab58b539031f53505209b189538432c5250510b358e320caac6254f419798c548878d320c9419718d54442ce63884208f992544425e65cc5309b98b548c23e64145308fd91508cab8605073097d95320ca5c6355120cb949418c71d5454c10ad586400423e6414c209b988530434e5354810cb54b410432f5414910b3991320ca7661153329dd95210865c6354910ab189439029f63508408fd9741cc2ae628c440cd951411073751101309b98a544c26d62d5231cbd48404c34d5394810ad58752d074d530cb21cd945410823f645483097994534423d64145309758e51c833464d4530ad587325072f52d0510ae181410825f6354840d3548320c23e650ca40a7191320cb1f5414d20c754f418863e6095031cb149425066e6295110c7153534823d6414c109e58053086b6618c9418f594400425e63153219718d54486ad62d43418f19152cc71f54d4d20aed8131102b86050430a798c519031f54d4d10cb150524436552c84109b988548c63d6494e208f99253442ba60148408f992528423f6550040a7d8d505063f6550c438f994325073764d45308fd9152442cc624c0308f181540863f65d0720cd193514823d64d48108f19150ccb2d5454810e34c8329023c64542319799453482cf654c8328f994544c26d6215331b9185200823d64948209b98b540431c54d4d109798e524434f53149109758f520429c6354141c715053482776550441c754c53d063e6015110a718d429023d65d04218f992518c33a60d52109798e51c83366414520a718d4210aae62d4e408fd91500ca3e6494720cdd53514c2ae6214f41d5185530434c5388120cdd44404823d6494a308f596540c65c63548408f994219034f43149439e980530863c6454032a798f50d06ba60d4640
  | 1 => 0x25d63d4b10e3d0f420ca6f654c832a798c511023f6155032c7150534423d6414520e3191320ca5f654c4318f592530c2b56114b41d5146304c25d6394421cd990514c26f6255130d5d4f514823c65d05308f594219023c654ca409b58a544425e63d5220a758c511027561d4f20c754c531025d63d5010ab988531032f52505108f195321031c53d05208fd95410867b654c0308f992510865e6314810c7551538863d6494e10cb548521033751d05309b994524423c65d0520cb552528c63e6414d21aed81525063d6494720cb94b418c74f530ca209b58b548c32c52d05309d185534823d650c640d514f51483375190120d5147314c32f54d4910cbd4b414c33561d52108f997414423f654cb418f982540866f65484219758c540823e6494910ab191320ca5d6394910ad586408423e64944308f590538869f6354b418fd91508c6766114c20cd547411023e60d5132cb949429025f63540219d986544823d61151308f990540863c601511097d8d524436451c85209b98854cc73751505408f997414c26e62d4c10ab189435063e650c6409798e544432d5210840ab58851902766115030ab58a319023e6414f108fd95329033754145308f994311032c54cc9329d58454cca3d6494a108f593504caba60d4a408f592518833751d05209d98753c832c54d4910e34c8321023d6494420abd89505063d6195320cd54741d031f53101108f59251cc23d61d51208f5964310a3d6115132c794e400423e6494632ab588531023e64d4f209798f548865e63d50109b988540423d6494910cbd4a529026d6588420cb94a40043355188440c754c535063e65d05408fd91534826c6254031d3d4f524423e6550530ae181535066c6254d10cb148404423d65084409b98a534431c53d0d429d185500ca9c6354b41ce982501023c64542219b594420cb2d54d0832b318d200823d6414f20cd146404c2b5619494197596310c23e64944319758c520426f6254d108f994544826f62551108f996404423e6414c10ab18943d0aaf6250e408f993520427b6054d21a798e219032d5454a319bd89544c735514c4408f993504c63c64540218f992544823d61953308f59053c863d64d4c21d5d4c514832d52d0631abd89535066d6215231ae9835310354514c530a7d8d521025e63d4810cd147414823e64d4132ec10110042ba6014640c754e400431c53901109bd8953102746155120a758c52d063d658c640cb94b410428c644c832ae181414423f65507208fd95410423d6195032c7553430ca3d6414f108f990540ca3c6550520ae181311023c6454e10c794f410427b65500409b58a51cc2d46344010a798f529023e641501097d954310e3d6414810c7952538875453145208f99251cc31d5494c10d9148514c27461551308fd9152cc69c63549418f59
  | 2 => 0x6454e10b918910042b561d4f419d986544c25d63951209ed95100431f53901109798e534423d64d4f10cd14440482ba6014e409758c54c863d650ca40b318d4210a3f61550108f592510c63e64145329dd85524429f6350a40cdd45414823e650c840cd545419023d65d0410c754c43d074e52cc6319758f548871e5454e21cb14a404c23f6454c208f191500c78d544c8329798c540823c6454331d914b514c31d5350621b358c420ca3f61553208f994544ca3d64d4b109d984540823e6590130cd590514c23e64d4e209798f52c432d5210010e9505210872e5494810c7952530429c6350b41ab98b50d063d6595032cb549418c63e6494620b398e218823c6454f219b99732486756115232a758f50d072e5250410cb54852d065c6354b41b3588430ca6d62d5010c794d410425f654c030c7d4e539023d6595010c794d418878d320cb41cb14b414434c53c8520a758e211023c6454830cbd50524c26c6254f419b58b53c423f65504419d986534826d6294d108f992510caac6250c43ab988519026c6255131ce980548427561951309dd85500cb1e5454c10cbd53524c2b860549419798c530426e62148108f592510423e6414f218f994404825f63551208f59640042ad6214f41cd150514833754145208f990520425d63152218fd9541cc36451881209d584540c27761551208f99621902786055121c7d4f414426f6548020a758c521032e5494a318f997414823f654c840c718d540ca5e6394421c754c43102756115020ecd0510042af6250d418fd954210a77654c431cdd93514826f62551329b98a51cc31c5350510c7d4e404831d5494e218f584544823c6055032e3d91320ca3e6414520e5505310c63e6494732cbd4a404c25d6594c108f590530831c5350d42ab98851102756195120d3149314c23e6494a308f191524429f6350b419d586534831d53504108f191534873551504208f98254886ce628c531b398e21486786055131b5185300c2ae628c6408f59353c826f65508428f996211026c6255110b3181320cb1c548c9328f992544cb1c5390942cb548525063e6494e20d514e104431c53901208fd91534866f6254f418f982540ca3d64d41318f59353887356115210d354832cc6af6254c40cd145414834f654c832cd145414c32e54548108f990530873454145309d59431043355150430c7d50534438c43108329d59421042ac6254141ae983418433751901309d584530832e5454a31d9d4b514c34e53c86218f592534423c6055031ab189431023d65507308f59541c823d61d51329b59652042b76154941a718d421023d64149318f996404835553cc4108f996311023c6550510d314c524423e658c640c7d4f414823d650c94197d8d528436451485208f993504872d5250410ad584408425e6395120aed81211
  | 3 => 0x8113c013cc0400401040f10240b000228d80b1f0010140016801078020345a0000a004040000a064960f0031540b0e439030050c404118060ac7f00c4905c1c2a005091590000607c9c0080806d680000900870028001844401c05088080043a0486000041114211c400050020380a00027168010310f054090200e0cc0317c2401c010040c25c0c000053448f08c01000f51ec0001802148003983c0104a0009302c0b028080f0020000d00400114aa00c5b0cc001b0cc098020380c1440a02c000100200c0002000000270145601c0002801010000181300003000001f400000180980009c020b41f044000586d000ba3cc001bd980400023c0007c030180200005484980102a3141835810070960400009000868360381309c2c0000802400000001781a06c09001610d402080000280604c240400766c130110b19c3c13811000010073451101308f59251cca3f6454332b31894310f365150430cbd49414c23e6510130ab189535066c6254c40ad98452102b86050610b398a310c23c654cb418f990524c6ad628c440ae983414432e43149438f994404423d658c4408f992534823e6550520d354c324865e6394d208f9974350ab561148409d984548ca3f6454a10a798c52d063d65d0431c714d435063e64d4c218f99432d073751505308f19153482b66114c40d354c320834d53548109dd85534823f65100109bd8953482b5618c9418f99353c431e5310010cb153524c31c5350520cdd53514829e63148408f195414c2ac6250f41b3d85320ca3e6414e218fd95410c7356414520cb948400423d64145329b99721482b56114c409b58854042776154d10cb149414c32c54149308fd96400433454d45309b594320826e62d4c21ae980511029f635094197d8d544caba6014a40ad58453d07646154810ae181211023e60151328f99352c423d6494632a758f529027765440108f592510cb4c53d49108f596219034c5348520abd89431023c654c941add85535073454d45208f992538429e63884409e181534869c63509418f593538823e64150318f181548c6cc644c8328f993538863f6454f218f594311023c6454321cb189540caba60d4840d314a304c23d64d4c108f99052c434c53d09428f181548863e64d4c108f590534865f6354b418f596211023e6494420cbd48404423d64944308f191528423d650cb41c754c400423e6414f20c714c404426e62d4f109ed81544863f6454d10b5986324c72c5290110d314b314c335518c4408f59741cc26d6295130c794d43902ac6250d42b398a318c25f63551108f992510426f6254e108f99252082ba6014c40ae983539023f
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8002d0060014c63c20003450ac1404001800c760601201da18e6a90a5a0d0c74548320c2873a6a6194418a1486050510a1eea990652060d5358853d070c298c0a0a21239c0644c832a1ce7a94a52048e74991320cb06a9ac429881431d5320cb41a18e4a98a7a0e0c53189435068c382a629a838c5446050420d20c6202200850c73548421030631ca4a14818358d5214b41c2aa6b08a62050c7454c32486463b4a899065895496110010a18ea99064a0e1563546211035031080880218358d5214840a18e8a906598d0c7254c531028639aa4290818554d6110010c4ac4a8c622050e72d4e539021ab88ca99081431cd5210b41c1ca63128720528705485250706b2a6419081895496114840c18c6312a819631619835484306318a4a1283431c95310f41a18e8a9864105487054c324868639aa429283431c95314d41918ecaa2641948d71191320ca863a2a6196438c5446050430a18ea990642050c7254c431021c382ca1928383595320cb41
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x2040000a048254d6114c40905811d5320c84080c87595320cb41a04835496114840885811da544c83280c87595320c840
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/267+packedAt s0K5 (21627+(h % 267)*10) 10) % 801)
  | 4 => 2*((h/260+packedAt s0K4 (29678+(h % 260)*10) 10) % 781)
  | 3 => 2*((h/32+packedAt s0K3 (2744+(h % 32)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s0K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 2 => 0xf81ffffe07ffffff81f07c1fffe1ffffa23e3f
  | 3 => 0xffe03ffff80fe0fffe007fe0fffe1e03c3cfcc
  | 4 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x882808c4122400016509421280222a80cd0d5
  | 2 => 0x924519103244986580a4291a53215551a2262a
  | 3 => 0x2149aa2490e909aaaa084f489d54181ac34b4c
  | 4 => 0x859634492481d2d34d3d0210e6998063740db0
  | 5 => 0xc6183871c70e1cfc71ce739c07111183fbb000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_37205
namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
def s1K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1c000c003080e200002fc43f0c3e907e31fe21f8cbf087f32fe43f443e18fc20fa43fcc3e10fc32f821f4c3f907d31fc41f4cbf187f31
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2204010000000300018004344138a0354c431ad42cc6d10530b5418cad50420b6418ca790e219f4344334c832ad428c6790f21b441482b90810b641082710d20b5410c2d907329f43482b90a31af424c2b50830ac424c2dd0530ad42042790c20af424439484219d43886b908309c43442750f219d43082b10910b541ccadd05209e43042b90b31b6410c2750c10
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*4) 4
  | 4 => packedAt s1K4 (i*15) 15
  | 3 => packedAt s1K3 (i*26) 26
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt s1K4 (360+(h % 15)*5) 5) % 24)
  | 3 => 2*((h/20+packedAt s1K3 (1014+(h % 20)*6) 6) % 39)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 2 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 2 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 29 s1Pos s1Neg, 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37205
namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x8be41bc41f510bd40f710bf40
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x272a020ec50110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/2+packedAt s2K4 (96+(h % 2)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s2K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffc1fffffffc0ff83ff07fc3fffffd8e31ff
  | 1 => 0xfc0ffe03f07e0ff0ffc1ff83fc3c0f02f3cecc
  | 3 => 0xfffffffc007fffff0001ffffffc00fff03ff0f
  | 4 => 0xfffffff800ffffffe0003fffff003fc0ff0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x48244448841084022a12542440652948861055
  | 1 => 0x19648c3924a494b05a50b4a1c4286a18b2c6cc
  | 3 => 0x20c91090694909550421294aaa8084b3016b0a
  | 4 => 0xb28a2122480d2a6994a408433312c023580da0
  | 5 => 0xc30c39c38e71cf8ee739ce70222308c3efb000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37205
namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
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
end PEqualNP.Outside.L_meta_37205
namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 1 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 2 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 3 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4244451104250808a849a124065290944310b1
  | 1 => 0xca48c321292129416942a50c4286a584594594
  | 2 => 0x491080a5242129410844a52a8084a2980aa0a
  | 3 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37205
namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
def s5K8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K7 : Nat → Nat
  | 0 => 0x3830400400cf00a0000060000000000006c000000008c2820000590000020c0008001ff30fd20fe20ff10f710f510fe42fe10fd21fd31ff32fe43fd43ff40fc31ff31fd40ff20fd30fd32fc10fe40fe30fe21fc30ff42ff43fc42fc43fc40fc32fc41fd42fc20fe31fe32ff41fc21fd10fe41fd41ff21
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x661fe40843fe20885f94231ffa1881f220443fe84087f105209eaa061fc32506fca7a0ff50540fd18061dd4310ffa6420ff14831fd10041fd53486f8a6907fd4231fea9e857c54c43fe64885f95130bea88417f548cbf8a2907f88440fb20a21ff500c7faa4a07f50831fe21c61fc54087f88590ff14d21ffa9081ff40843faa0a15f55210ff21021fe41083eea6887f10d40fe10c61fc210c3fe84995f95010dfa1681fd41cc3faa598ffd4941fe98e21ff510c3f886197fd0920be28a877f540c3f8a121ff4c621ff99683fe328c6faa5185f94042fea9061f530c42fca9887f50b32bf298637e544caf8a7105fd4540ffa8483f452c43fa86997f55032ff29687fd53c86faa598ff90932feaa461bd54083fa42a07f0c921ff28c85fd43043f862a06f50f40ff99263fe43c82fca110ff10f21fe29a81fe21843ea60885f15132fea9a21fe53d0bfca2a17fd4532ff88421ee324837886206f90e40fba1e217e540c3fe4290ff4c510feaa465fc43cc3f8a4205fd4c21fe206217f540c7faa818fecc130fb206217e500c7fa84217f0c730ffaa243f441c87fe65087f4c020ffa0c83fc320c7bc8621ffcc840bea8e87fc42503fca9087f50430ff19683fc51d0ef8a8197f14231faa8c81fe420cbfa83187f90020fea1a41ff20042fea2987fd0f41fea1441fe53483faa0197f84110fe202217e53906fca5a0ff14b41fe90e61f6510c2f8a8087f0c721bb28881f743443f865107dd0721ff20c63fe43cc6daa4207f95331fba06217d54043ec80887f54131fea9e21fd4350bfa63087fd0c20ef99465f9100437a84a05f94642fe21861fc52cc7fa81107f94e21bea8683fd42107f885987f48430fe98881fc32106faa120ff95010ffa1065f5518c3fc6410ffc8120aea9c857e52906fca898df54430fe286837c54443f882a05714d40fe99641fc53483fea498df95331ff90c417c514c3fa43187d88710fba02217e5310ffea2a17fd0942be29e43fe50087be6218df54910ffa0041fc50887fe62087fd4910fe28c87fc5110bf88390ff90b41ffa1281f920443fe61105fd4b10ffa94217551883fc62985d54420be29421fe41087fe8590fbcca32fe21061f732c43fca7087f0c430ff2164377514cafca120ff54840fe21461fd52107fca418df94210beaa063ff438c7fc84a17f10730fe18c61f750443fe85987f94232fe20421fe42cc3fe82987d88510f719065fd50907bca6107f90940fea8887fe53087fa6598fe84010ff98a417c54cc2f8a610ff15020efa1e65fe21083fc61107fd4432df2a043fe32507f841887fd0441ff99463fc544cbfc63207f55021bea9441fe54c87f861105f14931fb99221fd414c7f8a420ff50d40fea1865fc32c83fea0a0fed0140ef18a63dc53502faa3987fd0640ff99041df324c2faa7197f10e32
  | 1 => 0x551103fe6290ffd5330fea9e417a50087fca7207f90130ffa16637e5290afea090fdcc631ffaa063fe41c43fa65a0fd0c910ff28e8175518c3f842085f54e42ffa9c83f542443fa84107f50020bfa8a41f453c43fc81885f94443fb29a217d540cbfc8310ff10b31bf28663fc41c83baa6107f0c820faa02217d52887fe6218df54342ff21863f721443ee61887fd5132ff99481ff32907fa82087e88110be2a465ff50107fea7905fd5221ffa0261f651903fe87207f90c43ffa16417d53c82bca72177cc631df21a857f54082faa3197f54f40ff98c41ee52103fc86a0ffd4e42ffa1e81fc52907ba6498ff14b40be2a2437d52d0ffe42107f4c821ff20a21fc21483fca0217f94730fe2a061ff54ccbe8a6887dcc110fea8e817651083f8a1197fd4d10ff29841fe21d03fc6498ffd4a40ff216417e54ccbfe60107f4c310ff10a61f430c43faa9995f54e40fe20e637d500cbbc60987dcc421bea9021f630c43fc8598ff14c21f719641fd53907fc82204f95232ef99661fc52c43f862905f55310ffaa2617e50083fe87887d8c110fea9885ff324c2f8a2907fd4c40ff29421fd52843fc65085fd4e10ffa0a81fd30443fc8690ff15131dfa1887ff43887fc64205f94641ff20a637e53483fca6207d0c110fd10421fd43c83fca4a1ff0ca31f6a1241fc43043bca7217d95110ff10c81fd50487faa910ff50520bfa8a857e5410beea7887f0c020fe21021dd300c3fc62a07f4c941ff18041fc32d06f8a098fd54b10fe28043fe51502dca4185f94842ff2a461ff5010ffaa918ff50b41fe28285ff43ccafea8997f15331bfa9e41ff40c42fca2207f90610fe90821fc32086faa3a17f8c721fea1e63fd51902fca6217fd4732bf2a041fc54843faa2a07f10d20ef99065fd54483f8a020ff94430fe29841ff43442fca021ffd4440bea9885fc434cbfc871077d0c30fea8a61df438c3f886a17f10832ffa0e43fe40442f8a998ff8c730fe98a61ff5350bfa63207fd0040fe99243ff51482fca518ff0c410fb292217e54c86faa418ff94743ff99443fd518c2fca1a17fd4e21ff99681fc404c3f8a090ff50821ffa1085fe500c77ca8184f15130ffa0e61fd21483ec65887d54620bea8083fd30843fc8620ff14543fe10a817d53083fc87a17f8c820ffa8065ff40443fca5a0df15332fea1243fe20483fe8698ffc8421fea8043fd52043fc43887d8c910fea9481fc424cbf884907754e42bf29041fd50c87fca8197f8c430bfa8a65ff53903fc40087fcc720ffa1c217d51882eea2a17f8c630ff21241fe500cafca2197ecc230bfa8285ff50d07fe65887f90040deaa0437e52107f882087f4c740ffa9e855d53103fea898ff88510bea9483ff410c3fea418ff50941fe10e617c524c3ec83887f90e42ff21a87ff418c3fa8390ff4ca20fe29
  | 2 => 0xc3daa4207f94d10bf2a461fd32842fca1997f10120fe28265ff54482fca890ff50c21fe196217f52043f86510ffd0941fea1621ff41c83fa64205f94430ffaa065fc54487fe86187d8c431ffa0661fe215027ca8185f14943ff21885fd5150ffca7a0ff50310ffa9885fe420c7ec87887f90030ff90c43ff400c3fe64197f94f20fea8865ff438c3fc43987f90230feaa2657d52d07faa2207f10a20fe90c41ff318c6fca218ff50d41ef19265fe32906fea998ff90941ff98621ff21c43f864887f54931fe21e85fd42443f88290fdc4010bf2a065f521086fca421de54021ffa9843fc50907f843907f14f10ffa0461fe53d03faa3906f50842f710a43f643443fe6590ff50110be29283fc5350bfaa710dfd4543fe21c85ff41cc7eaa4887f0c840fe18c41ed320cbfe42885f95231ef21a61fe43083fe8490f7d4d40ff28c81fc410c7eea5885fd5310ff280877e51082faa9197fd4420bea8665fd4310fea41887fd0831fea9c85f431086faa7107f14a30ff988437d54083be6598df95041fe10021fc30c43fca910ff14a31bf2a043fc324c7faa521fd54420efa1c87f510042faa521fd4cb10fea1263fe218c3fe60887f90921ffa8c87fc53442fca4207f88430bf29e41ff434c37e8320ff54542beaa221fe30c43fca6215f54b40fb90c43bd548cbf883105f95220ef98461fd40103f8a198ff14242fea1421ff320c3f8a1a1ff50720ffa1c657d51c82fca7215f14e10ffa9087fc51903fc84217f0ca10ee99261fd31c87f8a7105f54843fea1081f520443fa8690ffcca30fa992217c54887fe85107f50210bfa9a85bf42502faa190ff14843ff2a221fe414c3fea4087f48020fe99041fd31cc3fc65207f0c110fea9a85fe438c7faa1a0dfd5210ff18221fd520c6fca39977d0d32fea1885fc54c87fe43087f10f20be2a063ff504cbfa8398ff54b10ff21441be4250af8a0a17fd4f10bb28c41fd51ccbfe42207fd4b40fea18637c53c83f881987f15120beaa263ff53d06faa921ffd4d41ff98421fe52502faa110ffd0e41fea1e85fe32d02fca521ff94243ff21e83fe42107ea8220df94631bf29e857e52c43eca3187f48720bea9e43ff40903fca1a1df94f10ff20c81fd544c2fca1197f94d40fea1883fe31043eea8885f55230ffa1485fd310c3fc64887f54041fe99063be41507fa87105f54e10ffaa4617d520c3fa63187f10b20fe29885fd4390b7a86a05f54031beaa483f542c43fca4887fd0520fe288417e500cbfa6518df14910ffa0821fe43087fea4987f0c210fe18e41fe32887da64907d0cb10bb28861fe50d0bfaa3107fc8220faa0621fe41d03fc61087f8cb10ff29263fe518cbf880187f54742ff18a417d54483fca5207dc8710fea14637f504c7fe65197f94331bea9e85fc408c2f8a6a07f14430fe29e85f
  | 3 => 0x82887f55331ff904217d508c7f881905f54243bea9821fd324c3fe62207d90b10ffa86437d51843fc80087f10f41f790843fc41082fca818ff90f40ff18a43fd43083ee84885f15320fba08437c5350bbc87987f90e21bfaa065fd41087fca0a0ffd5320bea8c85fb20483fe8420ff94221fe2a4617e51d0ffe84107f90f10fe28a81fc51883fe6298ff8c832fea90877d53907fe8290ff10631faa1e21fd54843fe80086fd0f40fea926176518c3fe86995fd5230bfaa043f4514cbfc64a07dcc710dfa0481fc520c3fca8107fd0d20fb21221fe310c7fe63087f90120ffa8e85fe53c87faa6a0ff8cb21ff202817d538c7faa5985f55121ffa82877e53843fc84105f54d10bfa9841fc53d03fc86887f10b41fea9a81bf544c3f8a521ff0ca41ffa0863f45150afca1207f15110be2a643ff50887fa8520ff90f32ff29461ff21d02fea5085f94010ee990657d52102fea498ff90540fea1681ee20483ee41887f48421ff18c41fe32cc3ba86987e94021faa1a21fd32d03fe8518ff14440ffa0241fe21043faa4887fd0620bea8085fe514cbfea090ffc4010ff290617d54087fca9196f50b41be28265fe320c2f8a6087fc8530fea1261ff52c43fea4a1ff90721ff990213e54083eca2207f4ca21ffa1683f454c43f886a0df55132bf28487fd5090ffea5187dc8110af29881fd20c43f8a4a1ff0c421ff2a263fe21482faa021ff50130ff28643dd32cc3fea3197f90730f9a82217f52443faa6087f4cb10bea9e217e52d0ffa20087f14e21fe19261fd53082fca721df54a31ff19461fc51ccbfaa7107f15031efa1a87fe428c7fe64997fd5321bf2a6417c548c7f8a5085fd5120ee98863fe434c7fe65987f10c31ff90041fc21883dc84906f10e40ff992417e53886fea9907d95310bea8663fd42903fa8290ffcc130fa20843fc32903fea420df55331f6a9061f651882bca610ffd0d42fea88417d54883fe86197f10421fe99221fc518c3fca6a16f90f42fe90221fe528c7fc82187f90e10fe21e63fe514c3fa8718ff4c030fba0a83fe418c3f884a0ffd4543ffa1a81fc51d0bfa62087f94443bb28821fc53106f8a8187f50431fe98a81ff31083fa6498ff10d21fe21c417f5050fee62887f94841fe21063fe52d03f8a7a0fdcc531ff19261fd500c7fca9107f84010fea8687ff43c87fc81987f10841baa8c81ff51d02fca3106f10d42fea1e83fe5050bfe43207f14f20bea9881fc4310bbe60185f94730fe19681fe5390bfe80a05d54610dea1283bf401033a8621ff10010bf28441ff54443fa83107f4c520ff99281ff43cc3da65905f14d41fe29821fd41107f88620d754c21bfa8265fd42886f8a8907d15110bea8c61fd20843fea221ff8c130ff18e417f5250ffca118ff54232f7a1285ed42c83fea121ff10921ffaa663fc544
  | 4 => 0xffd4042ff20e637f54043fa87207f90b40ffa1443fe51083fc60087d50710fe986417f50507fc4088774cb31feaa243bc43d0bfe6420ff54430ff206417c50507f886205f15210fe28e41ff52d07fca090ffd0b10ff216217e5090bfaa021fbc8220fb208837f53043fea2217f14043ef29843fd310c6fca6087f10931fe28685fe544c3de85217fd0b32bf28883fd43d03f882887f48610fe99061fc30483e842887f10a10fe99461fc53907fc60905f94343fea96836d520c3fc8510fd94b10fe108417e5410fdc85905fd4d10bea8c87fc514cafca610ff50e219eaa041fe42443fe84886fd0842bf28c61dd530867ca810ff0c610fe188817e53882fea990ff94a43fea0c63fc32503fe62985f94740ff21665fc42102fea6907f4c620ff2a463fd5010afca321ffcc640faa0a21fe51103fa84a07f147409eaa465ff53c87fe65906f50c43ba28a85fc500c7fa87887750f30ffa8263fc5390bf88298df55130bf29c817e53107fca520ffd0631bea9843ff51883fca0997f50420bea9c61ff40c83fc41087f50b21fe20441fc32cc2f8a5887f54642fea1465fd54cc3fe42a07f50a30fe20c21bd40103fa87997d10f10fea0661ff424c7fca4087f94543beaa665ff50ccbf8a098ff15332fea1661fc5190bf8a6a0fd14910bf28081fe32043ea43887f10440ff19265ff53d02fea9995f54740fea1a21ff51cc3fc8720ffd4e10bea9e81ff54043f2a010ff88720ffa8a617d54886e8a2995d94640eea9881ff31d03f886105f15131ff19241fe424c7fe41887fd0a10ff18843ff21cc3fca8907fd0840fa21a21fd434c7e885887f55320bf29a43fc53903fca321ffd4c10fb29e21fe41043fca6085f54242fe28e61fe53907faa3a1ff15310fe90841fe54c42fea898ff90d30ff2a043ff20443fe8210ff50830fe19061fe42843f620887d0c710fe21043fa40102fea9107d48510ff284837e54103f865185f94341fe28065bf4290bfa80187f94d41ff28287fc31083fc84207f14542beaa643fd408c3faa198fd10910fea1c21fc428c7b887997f15320ff2a6617d52903faa9107f54141bea8c81fd30042bca6107fd4d40df21a87fc42083fe63887fc8430fa18a21ff218c3f8a2985fd4e21ff20a41fd32907ec41885f15020ff2a641fe54487fe8721ffcc230ffa9687fd540c3fca3187d55310fa20e21fd43103f8a221ffccb31bf28821ff51d0efaa9907f14332bfa92617e51087eaa2187dd0b10ffa9487ff300c3fea8107f94620fb28841fd31c83fca421ffd4940bf28c65ff41507ea6218df54432ff98a21fe43902fca6195f95210f6a1085fe300c2faa7a0fd88110fe29283ff53483faa4a1df15220fd88421fd32902fea89857d4d40ff21881fd30483fca5987f10e31fea86857f548c7fc40105fd5330ffa1821ff5090be8
  | 5 => 0xb40fe21483fe438c3fc62887f10930ff990437d5490bfe82887dd4532fe99021fe30c83faa321ff10d30ff20863fd50ccbfea2a07f90220ffa1a83f741907fc6420ff08440bf29861be54083fea1a15f55330fe2a443ff54843fa83207f48010fe28865ff31c86baa6104f55021fe98843fe51482fca6887dd4910ff10843fc42d03fc87197dd4542beaa481df324c7f843887fd0a32fe21c81fd214c3fc83107f0c320feaa221f120443fa61107f50740beaa463ff31cc2fca010ef55030bfa9a81fc540cafea890df94b40ffa84657d50d0ffe8621ff8c531bf290437d50086f8a0a1ff90441ff28e657f52507fa64906f95232ff18881fd420cafca5207e50040bf298417c53c42faa710ff90a32fc90041fd504cbfaa110ff0c530ffa1e85f420c43fe8690ff08510be29a217d52107fe8298ef50b40df21881fc54883faa6907f8c610ffa9663fc50c87fa8310ff94b10ffa1483fe53883fa43a07f48640baa8861bf41107fea1a1ff48440bf28e417e520c7fca690ffcc430fe21e81fc520437e85a0df95330f790c43ff520c3fc86a17f50710fea1c65ff51c83fe63187fd0c42fe21481fe540c3fe83087f90c32fea9687fc52d0ffea810ffcc941fe292617c54087faa518ffd4c41ffa0881fe42907faa8107f0c640bf29461fd53103fca4205f94041ff29e21fc414c3fea8185f95221ff21a817e508c3fe84985f95110fe294817d52cc3faa2997d08110ffa04417e500c3faa7207f10e21be28a857551103fe8798ff50510be2a2617e520cbfa8720ffd4642bf29881fc32043f887887f90f21fe29e437e51d0bfca4987fd0e20ff21e617e52443fa42885f14c20fea1021bf43503f8a4887f15231feaa263be40503f843085f14532fe90e21fc43ccbfc65907f14e10fea0021ff43106faa620ff88521bea8e65fe504c7ee83885f54b10fe20c81fc31886fea4a05f94640fea1265ff42903fea9197f4cb21fe21443fe424c3f886887ec8220bfa9e437d52843b886185fd4f10ff90821fe53107ec63887fd5220fbaa621fc41d03fe87905b94840f721085fd320cbf863885f94f40fe19241fd42483f8a0217f54a41ee21c61fc42c42fca790ff55310fe20e21ff30043fc83907f54941bea8887f631443faa0a1ff50120de2a261fe540c6faa8187f10910dea0883fe430c2faa2217f54e10fea1a617e520c3f885997f10e10ffa1c857e52cc3fca1a0ff8cb31faaa221ff21483fe6418ffd0b40ff98241fe42902fca8907f10d31fba0a21fd41842fea7105fd4d21fea0881ed200837e84a0df14540fea8485fe31083fc43105f94321be2a461fe5090bf86590ff88310fe18a217e52043f8a3195f54232ff2a665f421c43fa65987dcc721ff99441fd51cc3fe82107f10621fda0481f621086fca5087f0c010bf28885ff4350ffa6290
  | 6 => 0x81a146000020005a007402043020000218140020900501b03c0143f00e02c2a00000a032000000220060040082d8080600001f00400000800014094010060000480781f28e1280b0900002bc3200303e0080b808004010018030021b04b81c0163440800300200c1308111200c0200d00c138000011000100100100000c268002ac0200095e00205c0101000002c00800080000000180060080080000e0443880801800c020d6012e30380040040e8028180ec02c320090000340003500219403000010000008091ac0040902629201c0780700002c0001c0220a40280601026c0002a0340380000009e2840005300e030c181100c034008000220400c0040700240000007e0040f028094064008120420180780a0020001a00102e01c589452180080080000601c7080403c0340010202c000068120000148e83c0142ec228050002480280501e0380380302e0640100800e0181c99208e0701c093000db40081305e0000389800e0000001900021c05000030034000050043e80088309c004a3806012028000000001441287d1820300000b01401c0000804c094240013840000080701a0282a80600009003c9f000060038980001f40b00000000c0a0680040640000801c030000d10ae040b20060100000480600004c033f300301f430070000d00f9770040a40612ca440247d17703e044008030340080980a02005021807003a78208412460981a93e00213c0080d08400c1c00b1680c02f0010000600000f02c0544085b030098060061120040d03f00414403803014fa00984d00c028028140ac0000a00304c0041581a0000a426003001ff518c3f882185fd4d41ef29881f9300c2f8a090ff15010fe28283f920843fe8618ff55321ffaa443fc418c3faa8087f08530fea9843f531c43fea010df14e21ff28865fc20443fea6107f94332bea8881fe41507dca4187b48421fea1e43fc43907fc63a07fd0830ff98a817e51887f8a4a07fcc921ff28083ff428c3fc6490ff54442ff296637d53483f8a0a1fdc4210fe18a43fd430c3fe8610fdc8521fea9883fc524c77e8721ffd0740fa20621ff51903fa85907f50f30fea0641ff528c7fc85187f90830ff218213f544c3fea690ffd4b30fa98a217d53486fea8887f94941ff2a265fc53103fea0a17f08640ff18c43f553443b886997f10a32fe98841fe5110bf8a9987f54231ffaa463fc548cbfc8290fd0c721ff18e21fc43087fe43907f94742be29021fe320c7fe6310ffd5310bf29663ff42087faa3197f50b31f790041fe42087fa82987f4c940ffa0e21fe32883fc86997bcc932fea8a41ff41887ec20887fd4e20be29281fe43482fca9197f50e30fe19663ff52906f8a690ff08740fa20221fd528c3fe61907f08210fe18e817e528cbf880107f54f41ff28e41f553c43fea198ff54
  | 7 => 0x10260180100803002c0b80400203062000016138259ba00201c1183a0000080a0a3022b6001017014004140000140600000001800002808006000070a600e000b600105a0100180a0061fcab00f0320a40000d03a01807112000008178040000e40f80201f8000480e0121280c8084a41880143d1120000000503400007822000144048100a6000060045180c80400100006c500090002c80000c0080180080d0c000004033000028010e70f20001902f0020080103a20e008100001540c0840050023d00200071e050528220460180080b00c0084c80000203c0501904a13c0000900473c000ef11a00c460030000240083501200c0001009203c0080300a0001f89a00800c0c00412a0140b8120000051d8000540a0010a604003c018040a027c048061520380b8010020280082f000a98470000240280380b00a0dc9a85d02e00405
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x44350b3e54104209f99441c82f46448310bdd95310c7d532cc110ed95151082f76550b10d714f43502fa6010c40e7d93535033e6414132b758f54c837764d4532d794d321076f54c8220be58021083b66408110d310d520c3744294440ebd89425067c654c640d754f510827c6454d21eb95120082f56210f10dd95154c427c654c720f34cb30483766588110bd583410877551906309f197430836c52d09109f59532c435d5390421fcd41304433d4354043bd19152c427f6550830c7151324c3cf624c930af59232d036d3254032dd94f21487776154d20cfd9154cc2fb61440109fd97318827e6508630ddd92518c27d6508640dd98452c427f6590a309d98754042f66315310dd94b41c42f6618c9319f59251c83cf524cb30be596208436e658c920fcc81204427e65d0c21d754e43907794294021eb58a4350bf162d4110dd10a510c36e52c8310ad59232443954310d10d798c520437b5094241b758c418c67c6054c41af98c4350af46148110b7597318c67c654ca40cf55142c43766494630d794e43043795284010bd59443c42be64d42319fd97420c73c63550309f99432442f56190230f9c8220c42f4644cb10d754f31086de6314c21de98353082f561d4a40d754e31c42f96090910f510c30442be648ca21bd19020c435e524cb318f590538827e6550e219f98f540427c6154f429f195210c36e6215010dd94d314427c65d0b109f59541083776548421d74c951cc2be644cb409f99632c435e530cb41bb58854042ed60d09429f99432d037643944209fd8d5190b756195131fc90120443b742d0310fc502204435e6254c21d794c420867e6214d40ddcca510435e6214d409fd95320c27e6214c219f5825290f7743946309f19643087355494430ddd0b514caf76150f21f994720083ad4210932b798f42cc2ad648c920d994a510c27d62d5031b598c52c42fa6010f30dd99731443ba5450040d714d41502f562d0110bb58b40482ee620c421bdd9743c437a4294021dd54f314436e62d53219f99642442f661148409f98251d0a7d6094643fa14920442f96008630db94a32902dd63951219f586548c35e538c421b958831087773294620cfd52434835f5394c42cfd52514c2f66190c21bd59721c439e5490c43dd90e518c3755108620b798c208427d61d5020bd193304427d65d0d20b758c404427d654c440db94a42903ad4250320d794d42082f765ccb109f18d54487b54010310b75924310e7e65d0d329f996434cb6c53548409f59250887e551c8220bd99232443d651cc2309f194400c36f52cc910ec500404427e60947439fd96310427d6015031d754c320833f54909109f19431086fb6050e309f59441cc2f56108110cfd52438835d534c820db54a20043e532481109f59431103d7634c510be5825150e7e6094442
  | 1 => 0x836d5250a10fc9013044375658c710db949420837651cc010bd986508caf4604c510fc98032443746354420d714f525035e538c0308f99054082f76044010be58343d027d6508540bd99642c435d538c621bbd8d424827d61948439f98253886ef624c320d714d315033e5450e31bb1894390b5e5310f42dd944418c27f6454331f5d0c514cbf063d4110be580218425f6355220cf98a540837651cc220bd58343c437552c4010d7182530879c54cc930ddd9542443cd6210f329f99742486f76550710dd191518827c6155130db54820842f465c8110bc980214427e60d50209f19643c439d648c932db98853042f66188010cf953431033f544c530fc982324435f53cc921d754f430833f5490d309f59721d03776554430b7583438c36c528c9319f592510873d5450c109b98b540c33e54d0e20cf98b544c3756194d219b58853843766094620bd98a54c43d663d5310db14b324427e6550d20dbd49424c7d44394630d7d4e32443794254021bd185329067f6550040b798f511036f5294b419f58553042fa60150319fd95420c73c4354840bb58b41487b65454430bd18532cc7b65415110dd547218c2f662101109f59543c827f6255132dd58453442ee62cc521dd54731cc27e60d4943bd98f21c43f15188020b7d8d40882bf6448640edd91414437551cc220ee98342d02ed620c310b758c548437661542419f98b544c75f3254232dd153514ca5d6314142de59710842ee6210120be982318c2f66210710cf55141083d6538c431bd586200427e6394042b7d8d42ccb6e43548409f98b544c35e53d0020dd59431c873f42547409f18554cca7c6355020db949328c67d60145329fd89548427e6094643dd994304427f60553219f59251043756354420be181418437654085109f586540c2f56510b109f98c544c3745210510dd58654443d46154c21d718d54442de6314642ddccb514caf56310310fc88020442dd6310230be58032c827e6115031fc9512044375518c020bd98732d06f86050a40db94a511033d5450a10f9908424427e6494810be9805110e7f6355030d798f54086f562cc710af59021c42ed60cc932ddd4d511033d540c020ddd465190a7c65cc910be18121882f9608c630d794c43c83eb62480209f99431482f56014532f5d8532cc73d63952329dd8553c827e65d0920d594d510827c6054831bb58851102ef6048020f5d0f32442f6640c710bd58632c423d64d4c219f58653d033d5450a21f5d4e534436d5210841edd51544427c650c941d7d4e53502f66510910cf99054042f6600c110cd95251082d663081109f99642043f364881109f596414839d4310f409f58853c435e53d0821d754e438433f54d0d309f98a51cc33c6155030dbd0d521027c6354a41bd99120442f662841109f98254486ef624c420af58
  | 2 => 0x65d0a31f994520082f661d5030ddd0a510c2ee6210130db592520c27c6255110b798f509073c6255020bd18c20442bc6050d40e7551300c23d6590c40d754d31842f562d0721af990520c27f6254f41bb98a4350bd6538c710bc195204427d64d4c10fc14d20443f060485109fd9640043e56188120af590538427c60546329f590504cb76514c420ed10d42c427c6254343be582435033f5410520e790e404c27d6215031bb98853102f6640c310bd98642c42f7614cb30fa4c920442de6314a40bdd9132c42f7650cb10bd99352c4376518c440af99252cc67761551219f59731d02f7654c710cf153424cb1e5454c209f98c54043af4350842cb54940102f7614c810f510d324427e6494010be580520c7f22144010eb50b40c827e6414f10cfd53434c6f66008710bdd85421073e6414810cf55153086be6408720f5185324c67d6014f21dd944211033e5454c21f3949300c2f66308510bd59543442746154f20f958840c437554104219f1815390b7461d4142d798c548435d534c420dd544514c27c6154b409f59732906f76348510db94b32cc3e76150920db14821502be6408640af59021903f26010910ed191304437453085109f59641082fa60144329f59741882f46050710b718d420c2f56190140fc986401035e6315032bd584304827f650c8409b98853043765110010bed8b10843765188640bd98a41c433d65d02409f98c525073e5450a109f992518c35c53cc5109fd9432443cc434c920b7185324c75d5314021cf153514c2ee620c220bd99020443765108430dd951510835e53d0f419f59731c827f62551219f19642042f4614cb21d754f32c437661d5310afd8943d027c6354321dd182518c27c6454831cf589540c2fa6014c42bb189438cbcd53c80209f996325035d53cc841bdd90324432e5494830bdd9021c42dc6355120bed81324837651102209f58f525027d6550e20bdd9221443b54250110cf150424c25d6314a10dd98a510c35d5394840db54931103f220841109f18d54842f4654cb10be9805190b3f6455131f9947208833c54d09209f595410c3746354440f5d4c32442de63d0831bd19130c433d54d03109f997418835e53548409f194410875c548c130eb509404827f6255131d754e430833d54d0e20bd5924110774538c510d798c53843d7324c510bd58232443775194632db949320433d54d4c20bd587434427e6590120ddd4a510c3eb6248210fc50a204427e6494f10bdd8d424435e53cc8219d987530831d5390c40be980324433c54d0b20cf552510833d5490c32b798e42883b643946409f18154cc67d6550521be980424c27f654c740fa98242c83755110220af99021c43776154b31cf54b40903d6630c421dd180514ca7e61d5132dd98e51883f2300c1109f995315027d64940109fd9531c
  | 3 => 0xf10bd99331442de6308310cf952310c2f6610cb10bd185404427c6054443bd58753903f360885109f587540caf76150a21bed8143842ed620c320d9548524427d6590410af59353c86dd63107309f995424427f6354720db553208827c65cc540cf150214c35d5314f41cf95243cc33d54d4420dd944310427d65ccb40fc54f504425e6394b40be58242503755148620bed81324c35c53105409f98a544c77b5094132db548411027f61542429f184544427d61948309fd89544835d53cca219f990534833c548c530dd545300c3da538c030de996204433f5450110d798c5304375650c310de983520437a6014c219fd96420caf76488110bd18d52442dd6390a209f59420043b651500409f986540cb3e65d0d40db54a420c77654c8621d798e52d02fa60d08409fd8552d026f6550842bb58841086ee6214043dd944318837561d4e10de540504caf565d0421bd98f41c86f561900208f590528427d6508730db54b42106bf6454910fcd0240c427d6115320ebd51424827c63540419f185540cb7754d4532be58241043f34088110b718d41cc6dd63d0930e750c43c43745288510be58241cc27d65d0f20e75894310ef7624c110cf951510c2df6350430f9d0a42443f26488110be98021d03565354440dd15310842de6308730dd10e51042766508110bd584540c2f662d41109dd9532442f56110c41af18542d075e534cb109f18154c875f654cb31bd58e52c42ef624c120b758f54c87e62048310e750e5210ef56110b219fd9643c427e6314b10b798c21042be648cb31d7996434c33d544c820af992329067e61d49439f5905384375510c620dd551510c2746154843db94920c43b74010310be18520442bd648cb10cf98654086f560153109fd95410c35f64d4d40ddd4f504425e6314a10bb58b43886bc6454121dd18e51903b960d0b40dd10e51883f120083109f19531d02f664c8510cf58d548cb775254440c7152434c36d5214b10cf151434873f6155020d754f210875f5494c21e7d4e4350fd5434c310cf90e50d0b774294440bd19543442f26548110ddd8a510427e650c110d754d401036e52144409f9865010ef96008740ddd4951903f26348110d754d43882e66210310bd58f204427661d4c10cf10c5050b3e64151309fd9743043e36248110cf953420c67c6550d20f590f30443746454430ddd87504c6de63d0531dd545400827d6195121cf952210839d6315130af98742506f563d4110f9986204827c654c521f518d404427e6394b10db94a210873c6454d10dd54c31c867d63d5310bd58440883e52108420bed8143083765110420bd58c41443744354620ddd8a518827e62d4530e755253082f56014b10dd952518c27e6414f20b758c529027f658c8219f595424433c54d0521db54a400c3e55294430dd14d510827f
  | 4 => 0xf58e5110b796015032cf953420c2bd65d0a42dd941100427d6590820bd58e214427c650cb10d714f31887ba54940219f992500c35e53940219f58a500c73c54d09309f98253d067d6115030af59232c83d55354420dd54e51102dd6394b409f596414c3cc534c920db54a510c3f260909109f990534427d6494a10de54050cc73d54d0c20cf94f43d027561150329f596424c75d534ca41f610e300c2ed6288020f558c204427c6454b30bb592424827f60551329f58b544437741d4141f5d4d31442ee6290020e754e439027f6510910bd58854443756154331cf55243ccb7454d4110fc4c1204436d520cb31cf189548cbeb60509209fd9532106f56490910be18131443f1514c030dd19251883d653ccb10bb58850cc7d64310d109f582544ca7d6510630cfd9154c82f96090820af990508cade6314341f8d4920442fa60087109f58a54cc73d61550209f59532d07795014243d7d4e53c433c5410910bd190314435c5390d409f19532107ae4394840dbd4a52902ed62d5030d794d500865e63d5320ed951210877452d0541d754c41083766454420edd5243443b55448421ed950310867e650c920bd18132c427f6550c41cf950210c2bd64d42329f98c54442f764cc710bb98b41c82de63d0b32af990510c27e61d4d42d7d8253087cf634cb20bd98732442f66010d10d755253082f56490110b718d424caf961c8120ed952411075f654c030de982518827d62d4c10be583324827d64d4d109fd96418c3b943d01409f986540c27e6494031af59030883e7328c910d7549310c67c6510c10dd58754c877741542419f596218c2f86050920e7d0d400c27f6454630be58041d027e6394421c714d42502f56190210dd584538437a60d5230cf94942d027d6194043de582534833e5410830af990500caed6215230dd10f514ca7f6054d10ed95243c42f5600c7219fd8954cc37651484109f5875250ef4614ca21bdd9120442f66550f10dd945218827d6314810bdd855250f6e528ca309f99731083b54350310dd94641902f56088421cf98d540c2ed6210c32cf953520c27c650c010af58f42502ee6590920ddd87504875d53cc310dd192510435e53d0c41bd587540c2dd63100209798c5050b6e5290a30db94d320cade6310930cf981540c27e62d4543dd55041443775194540cf951428c27e6394440dd99151882f5648c110ed99232c43b5540c421cfd50414c3e521086109f58a540c77732944409d98452042ef6488120bd592534427e6508540ddcca510c3d753d0d10b7181434c27e6115332dd946218c3745294440d7d84535035e63d5321ddd5341c879c6494c409f98b54cc67d6394840dd08151082f765504419f58054087e54248421d794c421035d53cc320bd982204427e6510521b798c21103f16488110dbd4921442f46150
  | 5 => 0x31c427f6510431bd18d20c42df654c431cf587544c3766194332d794e400827f6454f20cfd86540c27f6590430ddd95511027e6114910d710e500c35e5348421cf9504310af76355110dd944400c2df6350030bd996414435c534cb209d587540837653c8710cf953320c2756114142bd5865090b5c5450f30bd584400c2f46254d10ed953410867e64d45208f99253486f96008710dd584540c2ed6290e21bdd8542cc75d6314b109f587544c2f96010e20f594c410875e53084409f997321075f534c941ed50b404436c6094840dd54740902f5620c110b798e420c2f665d0b10bd987531033d54153319f19531482f7614c921ded4250c86f7640c110d754d421035e534c910cf550320835e53c80209f18553103b95494021fc58620442f46550f10dd58a518c374538c710bb588304837452cc510be1815250ebc644c840bdd91304427e63952219f996304427e6510120dd50951903775194643eb50b40482f9600ca40bd984400436d524c810f6cc5300c27e6014532dd0c550c867e65cc640cf551310827d6590430dbd4821503756394440db98d520c3555394420eb90f4250b7651d0410db14921442f66110a31dd50951082fa6090540bd584438875d5310f10db58853043cd6390b20bd5845310a7d6590720be983434c36e5250a40afd954310e7f6590c21bdd85404427e64d4c109f992538427d6214d41d798c538876e62d5032d754f4310b5d5310c41bb58a410877751141329f58a544c37451d4132f558c52442f960d08409fd9431d02be6408520be582428435e530c421cf95241082dd6310832d7d4d415027f6154843bd98430042bd6408520dd947300c33d64d4f109f592534827c60547439f19542c437651d0620b798e418c73c63550209f98e54c436d520c840eb50842107b542d0710ddd4b21442bd64087208f994544c2f5654c910f998b41c87755208710bd984529033d5490c20d794e3110375530c421b718d210c3b66410721dd98d519033d5415232f354f210867d65d0431d7553308c27d6510030eb553200835e61d4d40bd58d20442776550441bdd85320c67f6510a30bdd8532103745354640cf153324c39d4310f20f354d200835e53d0f10bdd8143c42f66310721dbd8d521027f6054c21bcd81434427d6294043ddd4a52442f6620c310bd18542883775194442dd544510caf76454f10e750c43902fa600c9409fd9543c437551d06209fd8152cc67f6354840bd58c52c426c6550920bd18e21087ae5454830cf584544c2f56108210f398e42c825d6510c30ed59052c42f565ccb10dd94721902f9608c9109f19521102dd63102109fd9532d06796584010cf95331083756588710de980530827d6494b30d794c43086f56090f109f98e500433f54d09329fd94420427f61550309f59441482f66190c319
  | 6 => 0x7b651d0040bd59331c42fb6055132fa54a40102f661cc3109f99542c427d621521097996434c27e6194c40d7d4c52502be6408530db94842d02dc63541219718d544427e6094843bdd85430867d6094c21fc580434427d6494032ddd4c534435f530c940b7584434cb3d5490210be18132d02f4658cb10e794d401027e6094642ded8d500867e61943329f983544c7d6304c310db551520c2f661142439f98454cc39c6355030bd984431075e544c832b7990430c3f06050d10cf153304c27c6254630cf586540835d5388420af191300433d6315130d754b300c3b554d0421bc58242442f86050640cf94d4210a7d60d5132ddd85534427e6014d419f58754cc2fb6450040e710d428c33f54d0b31dd946418c3b654107109f994420c2bd65d0240edd0e43c42f56488110e7d0d325027e65885409f593524c27e65108109fd9442843ba6090e40d7d53300c2dd6314321d7d4e53d02f56090b10dd50e510427f6510b31bd58e20c436d54c8020af990528c27d6550a319f19532503e54210910f994a21c435d5310f209f984524c27d63951329f987540c35d538c220bb592204839f53d0d409fd91534867c6590f21de54e500876d6214143b798e42507746550510bd987424879c5350f409b588530435d5410e30bd194424427c6254041dd98754882fa608c740bdd8542906f561148309f996325077551d0020d7d8d544c7755394620bd583214875d53d0040d754c420877442546309fd855310af7614cb419f19643482f76150e31be98021c83ae648c832db949410c27d6590e10dd50e518837a6015230b758c424c73e54c84209f99543c86dd6390941dd947318c27e6590f21bd58353c427c62544439f994544427d6194342bd594324436c6394830d7597328caf9608ca309f99620442de63140219f58a544427d6590f20bd58f524437a5288110d7d0e5090f5553cc421bd99040443746494440bd98231c426d6214143af18143d03d653cc310bd59032442f76388510d754b318c67d6295131e714e4350a7e6510c208f99052c42f46250510f954a51103e05248110bd98442086f66488110cf90e50102ec624c4209f98851502fa600c820f94cb20c43765494430d754c53487795014221fcd4220442f661d0831dd50d518827e6294c41cf15043482f56190b109f18553883745308710b758e420c3b742d0541b558c40442fa6008640d794e32c827f6510831be58041c42f565d0710bd984511033c3055030bd586508ca7d6494e20bb59132c82f66110330b758743cca7c6588540ee55150087755410710cfd52214c2ee6210f20cf953508cafa60cc730dd98754042ee6214830db54a211035c53885409f587540c3cd62d0d32bd98a53c427f6054432fc986204437562944309f18d519035f63551309f997434872d52d0040d754c
  | 7 => 0x4d4d10d7d4d434867d6414520e750c5210eee6214343bd58f21442f665d0110eb551200833e5410030dd94521102bd6414321af19152443b640501109fd8d52107ce63909209fd9441c82bf644c840bd1855250e7d65908109fd9150ccaf66114342f598e42443d7300c3109fd95300c36e524c841eed9140103765148430af983435027f60550219f195418837561d5332bd98c404427d658c9109f181548cb7632546209f98654cc27c6550510bdd81544433d5410420f6980430c2dd6390832fa4c9208427c6454810e7d0f400c37651107409f59631883f03194021db948320c35e53cc840fcc82204435d53cc610af5923248375518c630cf550320c33e54d0841b758c524427f6054442d754e310867e6508510db94a420c67f6254243f34c8328867e658c720bd98f20c43d96090f30fcd4b504435f5394c41db982520c33e5490210b798c50c87f240881109f584530836d52d44309f59743c87765394910f58c932442ee62d0520bd98720c43765190420bd584500cbdb6350040d7d4d4350af663901109f993504cb765294430ee95240102bd64cc841b958830c436f5394840f594e21086f4624c310bd9834244376510c440f9588410867c6550430bd9865050a9e648c932af590214c3b543d03109f1855390afa6088410be58341102be640c010ed90942c42f5620c421cf990540cb5d52cc431bd991214437543d4532bbd95200836c64948309f18d544827d6550b30bd98d210877651c86309f58e51d0aee6290f209f596430427e6194f20d795332cc2bd63d0b40b798e420cb3d5310c40f5d0d434433f5490520bd98b414427f654c821ed58640503f0604c510db95242c837950141439f98c54082f66494d10cf953300c33c54101309f19541083ad4210a21bd98b43c42f96008720bdd9443c435f534c940de54d50087744214532d714d32486ec6250d429fd94410867f60548319b988538435f4354a309f58a518c3774154321be98043442ef6254d109f98f54883755354620dd944310c36e6054830be580219027f6454730ee95150086f7644c510cf186540827d650c420f3d8d324837764944109fd8951d0ff3400c1109f98252cc7744394440bd99131c42f764c85109f98c52443b55490f10db549300c2bd6090f42dd947310833e5410c31d798b53502f56110841bdd96424436c52509319f191528c67d65d0910af58b435037663d4542ad99021c427f6154332d994a51102756014532cf95051082b56408710d794932cc27d62d4d10bd98753d0af565d0721dd10e510c27e6394a41cfd91540c67c6055021dd98c5150b5e53cca409f18953d07765354640bb98a318867c654c941cfd53404425d6594c20d7d53438c3d960d0e309f58e50c867c6254e10f9d8532c82dd638c832be98032842f8604c630cf55042cc
  | 8 => 0x10f998840443765144010bd99232c427e62d5030be58231c437651d04309f987544c35d53cc420cf987544c2dc614cb31cf150314c27e6315021db94a21042f5600c421be58232083e53248310be980214833e5450a31fc0c5500876f52948409f58e52d06dd63c8730dd95321c435d538c4109f583514caed644c920d714e52502ee628c020db152520c2e56210421bd59132443756354440f554d511027f6548110cf950428ca7d6588730b758a434c33f4254242b7990434caf564cc910bd58f414435f6154e429f59053c42ed6214243f84c920442f565d0641b758c50107775194440bd58a53c436d5290440ded425010ede6310330d7d955390af66210d10eb10d521036e6215032ddd09518c27f6510430bdd8553482f66188110dd586544cb746155120c7952530867e6494a31bdd8c21c42ee6210220af99352cc67e6510f20dd947319037565cc710b798c400433f5490530ed10e40c42ee6210d20cfd954310ebe6390c40d714e415035d63951219fd94319027f65c8640bed81435035e5348020be58231d027d63d5320d758053502f4614ca31d794c521027d6195132ed5905150bd6530c7109f984544433c5450531fc985500879c4390230cf95243ccafa6014843cfd53314c3b554544209f58b538427c6550130f9d48324433e6055021d794f42103f15150040d7d4e43507756115020dd9945150af663d0b10fc952204427e6510d4197d8d524427e6494c10bd98241c427f6510c10cf551320c2be6414021cf55142043766294640bd58643c42f6618cb21f554f31c865f6355120dd94721082f561881109f992510c2f56190310bd984438877631540319f996329033d5450430dd8ca51882f56114243d708553087d732cc510bd586544ca7c6254243d7d4d324833c5410d309fd9531103d65310f10bdd9521c435e63d5320de98e50086f564c8310dd8ca51043795014341ed185425077654907109fd9532902f6600cb10be18520842b46150b41dd544218c35f5354540ddd8a519039c5450d30dd987548c27d64d4a10dd90a51043745314542dd4c9511036d5214a41d710d520c3f263d41109f984534833f4254642a71814310f756115321dd994404436e6215021f558e424427e6015331bdd8554483f15348110db54b311037653c8510dd9865090ef56448310d714f315035f5410c30dd90a518833d5410b20d7d4f434827d6094f42fa549300c35e5350c219fd954310bcd63909209fd9642cc79d4310d209fd9543887eb5088120b798843cca7c6254440db9095010b355494420bc980324427f6154c10db94a20842f56110f319f988540c7d7320cb10b7d8d414c7cc524c9309f59253c82f664cc1109f59643082dd63909329f593514c27c6550a30bd98e414436e524c830cfd5142c83b56408110db54951102f66
  | 9 => 0x58841c877442946409f595420c7ce5354840ddd08514caf66310421d798f540833e5448430d394e521036c538cb209f59543c427c6590b109f195324433c6454d20be582210427c6354841bd58640c827f658c841fcd40304435e5390821c755153082f664483109f58654083d532cc310dd58650103e7614c920bd584420875e5390e42dd94b108436f4394830d7d4f52502f560d4532be582328427f6254043ed99020c4376518c220cf151434cb5f6554c40db182520c35e538c821d794d300827c65d0931d7153328cade63143429f993504876c534c9209f597424c3f05388110fc586200836e6215320eb508429075e65d0d32dc996204427e60d4d21f5545300c37743544409f98853042f663d04219dd8552d03775194630bdd8532443b76454d10dd982510c27d654ca40b759132cc27d65d0520dd0c951102dd64ccb309fd8554c836e5250a30ddd8e511036e6295320bd98742d079f434cb40be18131842dd63d0730f594f31086f562d04219f189500c73e5494830d754f320867e63d52219f98754ccade63d0731d7d4d31503954310f109f992510c75d5390420dd546308837732546309e580540c7786454021cfd53214c2de6314c40cf186548caf5610c220c754c43d0add638c931bed81328835c6355220cf585540c27d6295132bd18520c42f46150830dd98452043d4430c310dd192510835e65cc931fcd06500867d6194042f394d210867e6215110bd584428c67d658c520edd0941443755454420cd951510c2b5648cb10bed8143c82f663d0110fcc8120c42f96090e40db54b211035c53c8540bd9845050abd648c930dd597410877632d4532bd590204427c654c6209f590524c76d5448020cfd91548c67e6494331d7d4e435023c6454e20af993530827f6510d20e750c434c27c6454c209f995434427f6154810bd58b40c427c60553329f98f5150a7d6094743cf950310c3655214b109f58454cc3e74250910bed81439037753cc7109f588544c27f6254231bdd9532c43746155021fc14b504437651d0440af997425027c61543429fd94430cab76454910f5d8d31c42f464cc3109f18153d0676650c110f554d30c427e64942328f596540827d65d0b319f59253486f56494b10ed590214435d6315021dd984530827f6550c30de58354c42be6414c219f596540431d5494c219f9865390b6e52d0b40cf151214c2fa608c7109f98754cc2fb654c0309f59742082de6314810d754f420867e65cc540d7597438c3d4614cb31ded4250887d4534c110dd90b514ca7f65908209f19532042dd6310310db549420c6f461509419f99743042be64cc841cf55243cc2f56108310bd59431086dc64cc230bd59052c427c6055221cf550540c3764254620bd583424427e6494e20f354e521033e5410c30bb189514c3f360505
  | 10 => 0x40833e54d0430ded4250d0b3d6095232d7d5153087775410510bc582324437564546309f58653486df6350a30dd990514ca7e65cc740d794f4390bb551d0240cf153414c3f2300c310cf150434427f6454b319fd9150087f261882109f596400c37732145329f596320c3f16010710bd189310c6f96090a40bd18131c427d6510f21fc58620842f66114c429fd8d5090a7d6115132eb58843d0b5c5390d42de980540c75e530c4409758c54042f7614ca30d954a510c2f561d5332dd18a511035d6054c21bd582544435d53cc810be980214c27d6510421bd185424cbd7324c710dd185521073d54153209fd9532042f664884219f58f540827e60d4c219fd91530433d54151209f58454482de63085109d584540c3746294410b798e410c6f56094910b758c40c827d6590c21c7551300c35c6494c20dd94d310c77761d41329f99440042dd6314841eed53304c39d5310d42d7d86531027e6015020d754e5090bb76450710dd150514ca7e65d0810bd587548827e6548540fc94f504433f5414530db189534427d63d4141f658332cc37664d4532ded42504867c658c520f34c832086bd6190f429f59441c827e6414132d758c5050b7762544309f9805250e7f6510420de94d300c3f341540219d987540c27e63d5020bd185420caf56114840d754e40102f56284110bd98840c439c6250c43dd547200833d544c430b758e424c67e6295110dc982518836e524c430fcd8920442f662081109f18954cc63e6414c209d58650d0abd6010d42bd993324433d54151319ed95401035e53d4440cf9524210bb65450910dd50e511035d538cb209758c548827d6494331dd54640082de63d03309f1855290ebd62d0f40bd984540835d5310f21be583434c27d650c410bd98443cc6f960105209f597430cb5e5310c40dd545311036e4394830d754e4390a3d64d4f10bd980404427c6508010bb98850cc6f56308510d794e5090af66290d109f99053882be648ca31af582431035d63d50209f195310827e6214d419f59353c835d53c84209f98b54c42f66114c20cfd954210bf160d4f109f19732503d55314f10bdd85524c27d6214e10bd58742107f22008310bdd89314435f5394c21e7953438c33d5490c30bb98a43482f56414d109fd95434431c5390140cf15142486f660cc510db54a328c27c6454d20f990842c435c6454c209fd9152442de63909319f59641102be6494931dd14f21487796015021dd984504cadd63d0130e794f40102f561d0a21f5d0f32c433d6414c20cf952408c3786548110fc50710443b664085109f592530436d5290a30d754c53483e4520c910eb94b42d03764354440d714e434867f6254440cf9525308374654c910dd983514cbf26188020dd50e510c2d66308310bd9864344376518c010f34c8328c73d5488420bd
  | 11 => 0xf13088110bd58c41c42f661d4a43bd58453882f76150842fcd8e204427e62943439f98f52c43e76255110cf953328caf4614c810bd5835150a7f6454b30bd18c20c43f35248110af593329067e64951219f58a519033d5250040ed99052c427e6395021cfd52544427c6550530dbd4f208825d63150219f98c540ca7d61943439f99743082f661150309f9974350b5c6054e42f5d8532cc36c5290940cf55141c87d651cc030f598c31443f132d4110bd5845210ebd6414a319f98c54486bd6414432f6d81324c33d54d0c30b7d9532cc7775114142edd854210af661d4840be580414c3755110230be58053107776014532dd945408837763544209f595210c2f66088510cfd52524c3b65490710b758c211035f5310540dd8ca510c37651086409f992508c7756114f21db149324c3f121540219f582540867c6155220be583328827e65d09409f59642cc39c548c130de94510043764294430f314932cc25d6315020be1813248276658c110db94d32c83f032d4110af181425027e6414131e710f420c2f961c8220dd592510c36d5214940d914921442f96008530d74c9510cb766054440b798c218c33e6415331d7d0f5250eed6214443bd58a53443776154b30af59353086fa61881109f191510caf960148419f19743c86f663087109f58851502dc6354910bbd89544436f5294b43bb58b4310abd6414c20ded81524427e6588740cf153434c67f658c820e7d854310f755150220ed19130c433c5450d30dd54d100427d6014d21f510d32c43d763501109f98652d0fb554d0910bdd8953c427f6454d20dd98753c427f658c0109f181534873e6414c10af98343d027e6394742b7d8d218c2746550b10af990520436d5214943d754c43d06f66408310bdd8d21c42ef62505219f98853c43746155320d754e50086f96010c309fd81544c776518c640d7d88535027e62d52109dd855210efb6050510bb588540c6f4648c9109f19443842f76048421be18142883d753cc510cfd9153482f7640cb109798e54487755114742bd996434433e54d0a32bdd95404435d5410d32be98241c427d6294643bdd855350af661d0910d755043ccbb54250310dd548524437551cc2309fd9742042f76488710b758c21cc3b74090110fc993504437960d4b109fd8d54486f6654cb10bd586300427f6054a41bd58752d0f3d6414e20b758c21043756294640bd58232c427d6394341af992320867d63d5021d7d8d538436c6154840cf950420827e6510420dd584548c2ee62d0d32fcd81544435f534cb21bd58743c42f76350b10d754c51083d7438c1109f993530827d6590d10ed55041c427d6590830d794d211027f654c640be58242c837660145429f98b544427c6550c209fd954210b5e5490c43d794c308427f6590f20bd58a314427c61548409f1855
  | 12 => 0xc821b798f521033e6415121e7d5143cc2ee62906218f9974350374514c530d794d32842746154b40d794f410867d6494c209f59053c83d553104219f59432503775414532bbd954210add6314b109f98053486de63152109f9825390b7651080109f59252cc69e6390942bd18540c42bd6414332cf150524c2766194332cf950210833e62550209f98654cca7e6015231f510e510c2f56190120cb951520c27e650c120cf15342cc27d63d45209f99643842796015021bdd85325037653087109fd9620042f664cc710de582544827d60d5232cf58e54087756115331af5924310ff363d4110cf55054ccb6d6454830b758c42cc67e62946409f9865090ebd64d40219f58e528427f65d0910db95142c835d5310c21bd986200833e5410b31d714f325077443546309b58b540c27f6590a108f99353c86be6408620d754e511027d6094d10be98241902f764883109b988548c3f121940219f59053083795014041be1815350afa6010410bd185525033c5450b31d758f548cb3d6414c21cf54e43902dd6390841ddd52518835f5494c209ed81544cb5c54cc832db948410c2bd6408620f94c8324435e6314910db949411036d61948309f98a53d02fa600cb20bd185321037561d4d109f58a50cc73e6415120af59232902f561d0b31cf552410835f61d4d40dd10a518c33d6055232cfd87544c3774314542bd98440442f7624c3109fd94438827e6494830af590508cb7661d5020db54a210427c6548540dd54441102f561880209f997424cbb6640c110dd98a510427c6154c429f98a500c7e74290b10be980329035f5394e42bd98e534427c6355221ed90c5150b3e64d4f219f19542483d55314d10bd59642c427f65886409d996204433c6095232cf95231083ae5490b20d794f50086f16015310d798953082f66114143dd58c5150a7e65cc530fc553504437950140439fd85520c2f465d0f10bb988400c35e53d0440d794c43d02f465d0910d794d32886f6610c110d714d30883764294440b798e421067e6550530f510f514ca7d6114940dd94e510835d32d4131cf99054c86f664c87109fd81534835d5354021ddd0a519033d54cc4209f98b51503775454620f614f405027e60d4543bd98b53c43ce534c832de951401027d65d08218f99053042f5610cb319f58a53043b942d0140d694e500876e63948408f59052042fa6010e109f99641c827f6254640dd8ca511033e5410b21ddd8f5150b3e5450c309f996434c67d65d0530db54a321067e65cc720f518d40c437b6494021ddd4f31c87d643cc3109d587540c2ef634c832bd58f20c427d6590a309f19743c83745354440dd98251103756394410dd94e31c43765150010ddd48214433f5450d32db54b20c42f16014b10bd18532cc3b561d0b41dd19151082ee62106219f98652d03
  | 13 => 0x1d795332cc7f243d41109b98a544c67d65cca40db14a424c6df654c0309f994415027f6155230c718d540c37731d41319f195304833f60151309f98054c875f5388540bdd85424c76d65c82209f98a540c66d6215031dd594310873e54d0c10d694d500866e6214c209fd95320c7765254640b758c410c7776394420af19130443d5434c4318f596540c2df6355110dd98d510c376518c630db94932843cd320cb30f3d0f324cabe648cb21d9549511027f65d07309fd91520c2fb6050540bd58831c86bd6010e40dd94610043d56308310bd98620842fa600c730cf58b544c33c62950209d19541442d56314910db58b538877462944309f58b544c2fa600c410b7d93324c33e548c8309f59641882f76150821ddd9251882ed62d0f42af5924210a7e6115030bdd85320827d65cc840fc14920442dd6310120dd5445150af66110230db58a544867e63d41419fd9631c839c43d0932be582314837b5094041cf952420c2fb6050d30af993329067d6214c109f59520442fa6010f40f590c43c43754294410bd98752902756114c20d795143cc33c5450b219f5885050e7e65cc910d794d43906f960cc4309fd8552443744314532dd948414427d62953109798f540caf46350510be582415027e62d4c21fcd0f504427e6550d21bd58650d0ef5610ca41af99232cc2f76454b10af99232042f960d0510af191504c67f6054e21dd545218c3e46150b20bd58432c867d63951309f595430427d6590e21d794d431036d42540429f19152442de6308540b9d895344376518c030cf953420837542946209f996324433f54d0832bd98732c436d5214b31dd985508c7e932c8120cfd85540c2f56388710bd98043c433d5410430db988520437551504309f18152906f960c8510bb18941883b643d0910f9cca32c4375530c510dd10a51082f56188210dd994314435d530c621d798c5050b76658c510cf55321083754254620e7953300c35f5394e20cf54b40102f46150931bc98043442f76450441cf95141c835c53cc110bd19032442fa6010440cf58a540c36f52948419f189548c6f66115230cf152324c3755148020bdd85428c67f6354042bdd9120c43cd524c030f958b41c867d6094e21bd58a204427f6510c31bd19031c42ed62d0c21db98b54cc7d661ccb31bd987324867e6314c20cf55043cc73d54144309fd9642c42f564cc110ed990410875c534c521dd591518827e63947209fd9643487743054430be983314436e5214430cf590538427d6494620db949420c75e5350e40e714c439033c54d0510be181324c375510c630d754c31087773294640cf152424c37a60d4e20fc980214427e6494720d794f329067f6054443bd59230c42f66194243bd98d204427f61543429f59621902ed620c220ddc87504867a6014c21bbd85210867f65
  | 14 => 0x9743c86de63c8530dd952518835e5390840bd586500cb3d54108329f197325075f4314143d7997324c2bc6050b409f59532906f46388510d7986530879e5410c30fc94d204427e63d53219f19443c437432544309fd9632d073f54d4530d714c434435d6395132eb552520c3795014343dd151100427d6590e209d583514caf562d4110be982314c2f9600c830edd91304435d6395131b758c404c2f6618ca319f5825110b3c548c130dd5845050a7e6590110af592328827d6114f20dd94f218876e5288430e710c400c36d5290a41dd547418c3ce52ccb31dd94c214435c52cc931d754f41086f9608c5309f58652cc27e64d4f10dbd4a425037661150309f990538873c6155020bb58a30082f7640c310dd547408836f54c8020db54920c42f5620c310bd58e304435e538c410af590528c27f654c010de58053c837654546209f596410c7b454505109f98a508c67d6315210b7580430c2f66190330d798c54cc6f561901309f582534827e6494f219fd85534437742946309f98353c86ef6250e32bd98640042f7614ca10dd94631082f665101109f586524435c5310940cf15040cc33d54d0e31bbd89515031d4354043be58031cc2ef6388120bb58831c836f6255120db988528427e6214e109f595428427e6510530af99231903745114132cfd50424c27d6194e40cf18e540c2dd63147209fd895110ef76150310b7d8d41cc7f2518c030ed50b40c42f7644c310b798e42887746394420cf55043c82ee658c9209f98c54c827661150329fd94420867e6510d32bd185324876e524c8409fd815190b5e5310c32be5803104375510c730bbd894390a7f6055032bb58843c86f56510910b798c21082766194032dd94f5150b6d52108409fd9643083b554907109fd974384376538c510cfd9154cc67f6054732fc50520442bd6414430bd1855050b766114f109fd89548c35f6554c20bd59030442b464549109fd95424c77b5094232af990304427e650c440db54a32903f131c4110cf990540837b50942429f580540ca7c6550730cf985540c2bd6090d43ddd0b5150a7f658c740e790f42cc27c6215120cf95332082ee62d4f41d754c31043796094d10cf55051083cf524c930bd98442d07d76355110cf14f43502756195132af990520c73c6055030af99042502f56348310dd182510827e6194a43b798c324c27d6394242bd997204427e6590930e7d53324c27f6550a31cf552430c67e650c941bb58b511036d5290a409fd91528c3f03048110dd944218c3765294440dd90c5150a7d60d5021db18152102f662901109f99632d06fa608c520cf552400436c528c941af992321027e6094d21bd584325076e520c840d75855390bf164d41109f594400827f65c84409fd95424c3f160085109f58c544425f635513097997434ca7d631414
  | 15 => 0x4435e534c8319f993528427d650cb10bd98442443ae5490842dd151510c27d65d0830cf95330082f561140429d98754ccb7751945309f185548c2f96288110cf54d401027e6095021de58054c827f6590d209f58354cca7c65d0c10af191219033f6295030bd18954c439c53d09409f98251ccbcf43948309d195324427d65cc640d754d43086be648c9219f996428c2f46250d10e7553430c3f03248110dd50d518c39e6310f42b798e52d06f56194332d7192531027f654c420ddd465110e7d658c4409d58650ccaf66114332dd94a21443ba60d0f409f5825210f3e54d0e32cf951518ca7f6154232af990200437461548439f98653d0a7f6254331db5974290af561142329d986544caf46254f10bdd9732442ed62d0d32e7d53434ca7f6544010b7597328cadd63d0932bd99052c433e5410e329fd95410827f650c020b758e428867c6355321cf55243c86f561d4830bb988540c6f56488310cfd52314c33c54909109dd8554c83e54210b109f584544c2de6310110fc4c030443f15190040bd18532d07774294420af990315036d528c440be58232c827e65cc840d714d32c867d6215330dd945401027e61d4d20d798553082f561d4a30d714e31502fb6050610dd95021c43cd320c831d7d4f30883776155132cf552434cb3d6414910b518532cc67f650c420d794e200827c62543319f982544c6fa60905209d5865010a7d64943329f590524c27e6114d10ddcca518c2f960cc8309f990504876d5250a30fa94940102f4624c510cfd5141486de6390932cfd52544c27e658c420af992320c73d54d0a30dd552518823e64d4f20cf952300c35e534c610dd594410867f65cc420db14e521035c6254c40bb9885110e7f6054c429f988520436f528c941bd583314c67d62d45309f98e54043f15388110dd945400c2dd6390631fcd8d204433f54d0f30d7153324c6f860508309f99641482de6308610dd14a510c27f6550130bd59632c42de6310832af59353c827d6494e10dbd4a42507765108420dd948410873d4254740cf55341cc75d5314440d794e43842de63140419f597210c27c6254f409f586500caf661900409fd8951cc2ed62cc721db588548437651d0010d794d42086f66488310bdd97434435d538cb21bdd8e21c42f6618c8219f98a510c2f46250710dd50b514ca7e63151209f98354ccbf251d0240bd59032c43755454620f554e210875d54cc030bd18e10442d56310310cf152438c27c654c510d754c420827c6154a40dd4c9510c27e6550c20d794e32102f76150b329f994200433c5450120dd947408836e51484219f98e529027e60d5331bdd8e204439d4310e20bd587321067e61153209f98252d07d763d45329f99632106f160d4f10eb14942503764314532dd593514cb5d5314c419fd963108375514c0209fd
  | 16 => 0x564083109f992544835c6494c21ddd805150b5d5350c10ee95120082f4658c9109f181548c67e6294e419fd91510ca7c6454232db94b310c23c6454d109fd94420833d54cc430bd588534437a60d4c109ed95300c27f6590c329f58c54c836e60948409f9845350bb74310d10bd98e41c435f534c110f918954443f32088310db549410c3b640503109758f54c43774354430ddd4d10043786055132d798f54cc7776550710bd5805150a7e63d5210d754c210837551cc440d754f329073c5450130bd980414437950142319f18951903d66390b10cf151424ca7c6054b43db94931102f96015032bd98c40c427f65ccb10cf95041042ed62d07209f58b54843746254440b7d8d51502bc6050c43b798c408c36d52148109f597318827e6294043a7d894310ede6308740cf990540c67e63940209f582548caf56390110bdd8542cc35d538c420cfd53424827d6394b40ed55054442bf6454d109f59431883766154221dd50c514ca7d6294430cfd53424c39d5390c409d9865090ef76150810bb98b31c82de6390b31bd58354c42f36055110cf99252cc37554d0721db54b42103755214b10dd591510c37a5184010e710d321035c53d0940c75515308776510c640d794f32043ac5250941cf951410876d62d5332db0c1520c25e6315010fc947208833d5410431bd984400827d6494f219fd8954082f663903109f195420c6dd6010d32f694d300c2ec6255110af990210c36e4394840cf551410875f6294c40bb58b53d075c6154e42ddcca510833d54d0720bd992524427d64d4d209f996218c2bf6454520bd18d210873e64149109fd9543482f56110b41bd99121c42fa61882109f99421d035c5308540fc10710442d66308510bb58a43086f662d0710ee952300c3795014042fc551204433e5410020b7d91324c27e62d41439fd954310fb64310110c7951530867e6590b309d9865010e756194043be98342d02ee6214c10e799043ccaf6610c020bbd9532c82ed60d0a42dbd49324c35e5314242fc103304427d61d5120f5d0d43c43e4614cb209f594438875f43943329fd97428c2f7644c710cf15142483d6324cb10d714f314875d53d0f42dd10e51902bd6408430f9185424835d5348421d7d4e5350bce6210f32ddd45504cb7561d5230bb98850106f660d0b10ddd0f5150b3e6415332fc547208833c5450b20f994821c43756014542bdd9321c43cf624c931cfd50214c3796588210bd584528c27e61d52309f18951d03d5618c130db58854ccaf4644c510dd546211036f4394840dd54d519037451d4142fc4c9204436d53c8020d7d4f315036d52084409f19542442f7614cb409f58754882dc6354142ddd46514cbe5620c421cf552210c2f465cc110d754e32d073c5490e20edd50424427e6510c10de545200827d61951109f18452
  | 17 => 0x5020bd58342c43f34348110af99351ccaf661080109f990540c73d52504419f584504ca756510421be983318427e65cca40edd91524433f6555021bd98d214435e6314d209fd8553d027f6550c329f99443442f5644cb10dd94b31442bc6454d209fd9542c42f6600c510bb98b438873d5490b31db94a200835e53948409fd8552cc27c6454b10cf951400c2de6390b21eb59232c833c54d01209f99632042f962c41109f580544c67e6214131f954a21c439d4350130dd14c52c43e74250b10bd18d54c427d658ca41b798c424c774654c5109f992544caf563841109f194438827d62d4143af990325077661d5231cf55342882bc644c020bd58f41c437251440109f58753503af52509409f584548c35d5410c30f910721086f564ccb10cf950310827d6510420d79865390b776154f219d58650d0fae5450842bd19153442be64d4f21bd98620c436c6394840f998840c42f66210f109f594321076d62d5221d754f5090b7460d4542af59643102f66494b10dd15251082be64d44209f58a538433f54cc930cf59052043b443d4542bb58a535076d5288210db58e521027e62943318f590530867e6588530bdd90204437a6014e20ddd5151082f46150a21bc98620442f96008620b9d89544435d538c821bd58c54c43763254630db548521023e64d4c219f98c54c437454c8621b518d524427c6354b409fd9532d02dd6390b31bb588314827f65d0430bd58620c433e5414830cf153524c3765288421cf552410c37653440109b988540427d6590730bd984408435d5390821bd58e414437642546309fd89548c75e6315330d714f325027c6550932b758e42906f960c8420bd588314427c6510020f554f31087776354620dbd51200835d53d0820fc192204433e54d0840cf950430833c52d09419f990514cbb44354440dd94521902f56210421d7d4f215033e54d0a20dd50a510c39c5410e30d7d8d524433e5450831d754f32442be648cb41dd90d510c27e6550c21d794f5090a7c6510d10bbd89318833f5310d42bd98430842de6310631bb58a43cca7e6508430bd58f21c433c6215130b798e418c3d732cc710dd54641103754294440af993500865e6314b10bdd85421039e4310330d7d4e52503756194243db149425036f6548020bd99330c42bd6490040cf586548caed6214341bd58b54c43ad5250040de949208427d63d4941bdd85434437765546209f99721cc33d5494c209f592510cb77514c530e79854310fd56390b10bd9845210e7e61d5032d794f4310b9e6050c43d7d4c43882ee628c4219f59443082ed62cc320db58854482bd64d4c20b798e429067f6548410dd947308c2f565d0310dd14951903bb5090140f58cb514cb5d53cca109fd95325067f6550030cfd0b51502f6618c010b798e408c27f65d0f109f996428c7b
  | 18 => 0xdb149325076e5208410d7d85531027e6414a10dd54d510835c5350d41dd185544cb75650c710f918532482f56308110bd1855350b9d4310d41dd547208827d65d0030cf95043cc79e53d0a42bd185324433f60552329f19542cc35c6294c209f191518827d6510830f9d4b214427e6590b10b558c52c43745248510be596100427d6394440dd19532c427e62d41319f997329077651d00309f980520436d6154840d554e511037651d00409f18d50d06be6414e109f58b50506ee620c720db54d20083b45490d10fcd53504427d658cb409f596520437960d5330ddd885150a7d63951109f988540877551902209f994410875e63d5310d794b32cc6f46454f109f19532c439e6310c40ddd8951102ed62900209f58652d0e7f65487409f98b540c79c63500409f582544c2bd648c941cf990548c3746494630d794d401027d6510a30d7d8d538879d4310c309f597310427e6214d109fd9150c875f6355132d7d9532cc2f4654c110bdd8532c437443946309f594218c27d6550630af191308436d520c830d790d5010fd532cc5319f98a54c427c6550d21fc887104427d65d0d21dd94440083f13148110bdd85420c7b94150040dd553514ca7f6550c219f196320427e65d0b31d7cc951cc33c63550219f594214c3b74250710dd8c8514ca7c65905209f59531c82f960c86109f593530827e64149309fd96328436c654c920bd59020c4374520c5109f597410436d62d5220af592320c33e52d0b41ddd52510c27c6054c429f58e548867d65d0832be580421033c5450930be58341843d932cc130bd98f40c42be6414a10cf550420833f54d0931eb50842086f465ccb109fd89530836d5354840af990300827e6394821bd584504cb765254b10b758e42c867d650c941f9d4a524435d6194c40bd994314433f6454e20d754f320836e62d5020cf98d540827d6510f10bd587328873c5450f309f994424caf66190941dd94741902f6654c9109f59442c436d6295131ddd8a510c27e6588640cfd5342c867d6494021d715153082ee6214031dd10f5150bf24348110af99353c427c6550d309f59521102f5640c5109f58f548427c62544309f58453882be65d0941b7993308c33e5450e329fd9632442f76510d109f597430c3b664087109f18d50d0b6e52c8430cf553210c27d6294d21db14a214c2dc604c930bd18d404427d6508430bd98a304433e5448420cf550408c3765110230de5405090a7d6394910cfd95411076e5290430be58342d027d6095331dbd4a520433e540c821ed59021c435f6354c219fd8d52043cd434c8329f58c548873f5490e30bd586304433e5490f209f597430c7745450710fc48510042f565d0d10dd54721103b742d07219d987548c2f5654c110cf550320877651cc0209758c520427f65d0d209f58a53d073c605
  | 19 => 0x421cc27c6548110bd98b31443e65214910cfd9154ccaf46355110f994a210873d54942329f98653d033d54d0c219f58c52507d76350310cf5502108376510c4209f1815110b755110430bb58b304835d53cc020dd992518831d6315130bdd9643443d4614cb30bd983214437651c8220be98053086f561ccb319f18954cc36e520cb41d754f50086f764cc110af98843d0b595394021cf992520caef654c832d794e31c427d65cc421f3d8d320caf66310510bd58f544427d61d41439f992508867e658ca10be58241c42ef6250d429f98e52842b4644c110f34c930c835e6315021cf952428ca7f6510410af98e4350ad763551109f99352c427e61d5021bd593214436f654c832edd8542d06dd63080109fd9432c42766115030bdd9442c427d6590b319e98353086f46150b31b798c400827d6115332be181314c2f564d4f109f98f54086be640c740db58a53482f665d09109f19432442f4648cb10bd9865090b3d5415231cfd53304c36f5294a30f5d0e30c42f76550310bd58b41442f9608c930d714e324433f5410130e795253086f56114343b718d40102f663d0510bd99332c436c5454830dd10e51083745394b10db101521039d5494c21bb189515035d63152309f98a538437a5490040dbd4a52d02bd6494930d714d304827e6115232ded42504c67e65c8630bc58254442de63087109f997434427d65100109f597428c7f35288110ed95342c42dd63085109f997210c3e52108620cf552518cb9d6050c439f18054443766114e219fd9443c82f661d0c41d7d4e415035f534cb209f988548c27c65d0e21cfd5341886ee62cc520db948411037651486309f58253906bc6454930dd54b10842f6610c941dd94720042f46150d419f594414c2f160949109f996214435e5350420cf15140442fa6090f30a7d954310eed62d05209f19542842dd63d4642bd98e524433e65151309f99632907f25148020bb5884310bb664d4f10f594d511035e53cc8419f99053843d732cc110cf950530867d60d4941e754f4290add6308630db58853886f561cc110d798a530827c6154332dd94640043d65314d109f98650d0ebe640c2109fd8153042f4648c110afd91534833d5415010bd98a43c43765444010dd54c53c42f565909109f996321027f6154b43d794c300827e64951309fd95410c73c5454930bd592314427e6394620bdd8931c427d6094b31bd98331c433d53d0040cfd51424caf465d0d10dd94640882dc6350330cfd53434867d6194a409fd89540c6ed6210010ddd4e534433d5414c21cf55132086f66190f10cf95043c87d563d5310bed8142cc27e6015131b718d400433d5490b20cf951420c36f52c8110ddd8750506f761509219f58c51502f561d4c20be18132882bf644c010bd59542c42ed62103309f994414431c54cc930
  | 20 => 0x837632946409f18151cca7f65cc4409f596210c36d520c4409f18d528433c54d01309d195314436d524c4309f594410c7b96010c40bed8141903756194042dd90a51903f04148110bd58454082f960084309f18d548827e6114c219f593504875f6554c21d794c32083ce62d0d329fd85544827c6114d109f1855090e7e6510831be582419027f6510620f654d20083d75354f109d996404437a5048010af590518cb3d5450610b798c21c82bd64d4231b758c5010a7e61d5020be98332cc2f56510d109f18c544c27e6515132ddd4621483f05288110bd586408833f5450b31f510f324433e54d0030b798c219035d53cca40f354d210873f64551219fd8d52902bf6454930b798c41cc3f331c4110f598c31c433d5410220dd54441d037551146439f983524c73d544c421dd945210837451c8530bd986410867c6508540dd58d51902fa60d0440be980418c37651d0630af99232443da43cc130bd98221c42f5618c9319f996424ca7e6510d31cf950518cabd6290541b758c408827f6508730dd183514cbd56310110cfd50434c3d5300c110be982318836c52c8110bdd89534435d6510c30dd15052443795494021eb592324827f6510630b798c408436d52d44409f98a548c27d62153319f990540c27d6394b10b758f509075d3254331cf55342083f16014f109f994418c27e6095231ed90d434435d538c010db588540c67d60d4d21cf94f42d027d60947429f586521033e5454830eb54b401027f6510010f914b214433e5450c20f998831086de63d0730dd54620082f9608c620d794e510833e54d0721be980434827f6354321e718e540c33d5490c21de95250086de6314420bd98020443796014910dd54f100437653944409f58b540c27c6548640d794d421027f65d0f209f5865090f7a60d4a10af593518cb3f42d4141e7d51434c27d6294e40afd8140102f962880209f994414c73f5410d20d754c400837565d0721b758c50d0a7d61d5230ed50b415076e5210841b758e410c73e54102209f18554cc27f6154243f9d4a52c436e5048020d7d8d538835d53d4840d7d8d534437941940219f99432d067f6588410dd953504436f4354830e7d50438c2f46150a41cfd52540c2f7614cb20bd992214427d65109309f195404433f5495331b7592434c2ed6214c10af592320ca7f6255010ddd835150af56308710dd14b414426e6215020f6d4f405035e6094c20d7d4e53083745450510e7553328cbf1618c0309fd8d51103b74090310d7982530876d5210b31e750d5110eef6250420f514c324436d5250a419fd9721cc2f96010620bd19220442f5610c821bd98742c436d5250a40bdd85329033d548c420cf95343086f5628c710dd54a510c35e530c410be58341d02f562cc110bd185328c27f6590830f554d32c42f561109109f99
  | 21 => 0x6190941cf59052c42bd64d4430fa94a40102ef6254530ed551510c3e652544309f194314833d54cc820bc58a204427e6394241dd984530873d5415132cf99353c827e63d45409f597430835e63d5332de951500873e6415221d794f318427d6395121bd98e210877562944409f587524c36d5214941bd986204827c6590e21bd994524433e54d0420d7d0d5290f5d3254032bd584430c67d6094f419f181540ca7f6454f10de4ca50086f66590f109f993514c2f76548310bd58650d0af662153109f98a53903b66410510bd597324433e5490c329fd91528433f4254341d794f510835d6254c40b7991300c3783294021cf95342ccb3f5495230cf951418426e6215210e750c5010e7e64d4e21dd5445150e7e6495110dd589518c36f5248110dd50e518c36f6254d2197d95300c3d6618c130f554f43c42bd648c932b598c404435d530c4209f988505075e53ccb10dd947410827e64940219fd81548c6f6620c510fc50620442776544010d714d215027e6590b31f510c514ca7d65cc9409d586500ca7c6550810cfd5254ccbf260087109fd855290f5e6494c21cf58154086f56188120af59331502f76154132bb58843d0a7d650c0209fd9741882f66190110cf95241042ee620c5209f98e54442f76354910dbd89520427e6510d21af992328c3746294640bb98a40882ed62d4643f94c832c431d5310c40d714c31503f252d41109fd96430c73e5490f109f19151ccaf76355310de50550087756254640bd19642443764214532cfd9543d02f663d5310d79825390af66110310fc986500873d6414c10fc0c2204439d4310d32cfd51214c37954540219fd85534836d5248440d7182531027e6590530b798c521073d5490431cf55054083b44394640ddd9531c43b6640c3109f994534433e54d07319fd9542102b6640c110bd98430c439d6150c43dd14f504435d5310c20afd91311037543d4542db94a21102bd6090d429f58e51c833f6115130ddd92519039f6450f309f98853083e65294440bd993204436e6494830bdd8152442ee6210c329f585520439c5350d409f99543c435e534c320cf550430cb3d64d4c21cf550540867c6510d21dd95141107756194030d798f540c3755254440bd987528c27d60d4943cf990540877a6015210fc907104433f540c530dd553410867e6094a319f994434836c4354840cf187544c27c60544329718d54483ad42507209f197214c3795014121db90d520c27f6508740bdd9031442bc6454520b798e525065e6315020fc98241c43776454420bd58443486f46150b21cf59253487595354021f6181324c35e534c820f3d8932cc75c544cb319798c524436f5250940d7591530879d5310f42e750f404c3776554640db54b321027c65905309f99421103b5648c9109fd9541c82ee62cc320cfd50438
  | 22 => 0xd20b758c54087785394021af99253486ec6250320bdd89210879d4394443cf950410867e6294f109e580540cbd6530c421d754d43906f4614c820dd18552cc27e6114f20dd553414437442544409f98f544427d63d48109e58354086f560cc721be582430c33d54cc020be98321442bd648c931bdd8532483d66314b10af5824250b756194343fc885204427c6548740d754d420879f6450c43d794f430827e65cc521bd98430c83754394420de540504c7f16008710cf55041087b65415310dd509518c37565d0641f514d314433d5450320f5d0d510c3d653484219f18d540435e5350c10bb98a430cade6390842ddd4651ccb775194730dd98951102ed6210f32b798f51d0af46155120cb552520c27e61d4132de54050506be64081109f19543c427d62d41319758e52d067c61552329f58053506f56310910bd986408c2ec624c620af19130c433f54d0530cf951320877652cc421de0c9500867f6155010add9153443765190030cf951310877751cc520cf951508cb5e530c220be58b108427d6394021cf552438caf66114232f54c9304427f6154a40b798c410c75c53d0540d7d4c425033c54d01109f1815190ebd6490441dd50e519033e5490d32bb98232c82bd6490d409fd89531035d6510e309f590534835f538c520db588548c3b46454910db98a544c77463944409f582544c77652cc631ddd8a518c27c6354b41cf184544c37551502309f58c52c42e46255110bd18554c83cd324c1209f597214c2de6510d32dd544510c36d5208410be980210c31f6550c43bdd9231442bc644ca409f58b548c67f6588630d74cb514c2dc6350630b758c21502f663d41109fd95424439e5450c439f59742cc27e650c7209fd9742cc74d524c030dd193514cb775110520db54b42cc73d54d0e32bd19032c42f46350710d798153102f7648c110dd551518c2be6414420b758c5110b6d6215010d7181530827f6548630ed55342c433e5490820f9d85320cb7454c8521cf95342442bd6190942ed90f42c437551884309f996324873c4394342d754d210833d5450e30edd50434427e63d5120d794c431067e61d41439f584548ca7d63951208f590530433e548c8209fd81544c3715148020ddd875050b7554153109fd94434867d65ccb10bd98d20c427c6055031d7191530867c65909319f59743043766115231bd59330c436f53c8020dd550544427c6590d10d754d43903e731c8421bb588500c7d753cc1109fd9153442f5618c0209f98b540873d60d5130fcc8710443775354640e7d4f42502dd63084209f997404c377530c710bd98650d0ff25388110dd94520043d453d0d109d58754883f260cc5109d195424433e5490c21bb988410875e53d0040bd580424427f65cc841b798f424c37b5094143bd185325027d64141219f984544caf5
  | 23 => 0xe583548c6ed65d0a42be5824148376514c2209f18d50086f6618c110bd98341442ee62cc1208f590524436f6255132d794f32442f662cc1109f982520c7ac43d0942bd98a53443b954480209d584504cadd6315010bdd85424427c65cca109f596310433d5410d32cfd91544839d53d0f40db94a41102f4614ca10cf551510c36d5214a10bb59720882ed648cb209f990520427c658cb10cf55043ccb3e548c020bd18e21c431e5494c20be980315037b6055130f9d48424437454c4010be58321c837853540219fd97328435e6395330d714d43503f3308c110eb10e52102f96015021ed509414427e65d0b10bd99631443b7644c310d754f410833e6395030cfd51434c37551506409d584548c3775495310dd994414427f6550c409f197215036d524ca31fc583214427d61d4f20ddd855210f5e6294c40dd508514cb9f548c1309f59431503775410421db50d52103765254910cf95041c43d75310d10b758c42cc2fb6048510cf9524310f3e5490b31bd19331c875e504c030af98f401027e65d0120ed95043c42f46350910af992325036f5294b30bd185434c6f162d4110fc55220442de6308520dd945300427f650c7209f58e50083e632c8110de4c9500873d5410020bed9520082f5618c2109fd91500c67e6094e419fd94438435e534c420dd18552c427e65d0830dbd4a52cc76c52481109f99053487756114910fcd8143442dd63d4840d7d4e315027d650c7209f19643883f13288110fc58252442f56190030bd59640c42f5638c431bd98f52442f76448510bd98a524427e6194c42dd58753c87e642c81109dd8552cc3ad4250520dd8ca518c36e52887109fd9432d033d5410830ddd4e51882f56115220af590504ca756114e20de54620083d9300c110cf951510833f5495010d758c520437b6394021cf59443903e541484219fd9621cc3764294630b798e515036d52ccb31dbd4a520c67e60d4c10af59032d073e54906219f996314875f60d4d409f9944388775514c220d754d438435d53d0f40bd984538835e5390c20dd181519037642d45429f994424c35e544c930be980204436e5254440be98241883e752549109fd96311027d63d5220af99030c42f662d4d10b718d42ccadc6355220dbd4a52506fa60d0920bd59030c436d524ca109f58b535067d6590f219f99730442f66110c31cfd91544cb9d4310d31f694e500867e650ca41db548410c2ee6290421bb58841c82f76050910ddd4d51882f661d5220dd584548827d6494910b758e4210abd6414021fcd51204435c53ccb209f996420c33e5490b21db948420c27f6550410e7d894310edd6308610f394f20083765190040af590200427d65cc020dbd49324c67c6590a10fc0ca204433e5410f30bd58352c427e65d0521d7d53308c3e86050920bd98a40c427e6394
  | 24 => 0x320cb3f5450510f6d8d300c33d5488421b7583430c27e61d52329fd9641042f660cc910bd990214427d64d4910bdd85428c37463944109f191500caf661081109f197430873d5450e20bd98442c427d6015331d754c53d0b77530c7219758f54086be640c3209f59721043756590310dd994214433e5250842b7d81300c2dd6390821cf952400c2ed6214143d7d825390a7f6550630f954852442f4624c710ddd46504cb6e5208430be58042442f7654c110cf550210c35e5310f109f596210427e6215010cf55031082bd64cc740bd58d214437661d4c218f99052443b654944309f5845350adf6354121ddd8553c83ad4350842f590d304425d63d5020be980520c75e6054e42cf951438836c6354840bd18943c42dd6110f329b18953443766194032dd10550086f960144439f98e52082f56194042b718d5148274654cb10b798e42086bf644ca409f58d540c3755108440de4c6500867e6014d429f18d52103785494021bd986405027d60d5231dd54721c833c54d0832be580540c75f5410e30dd546410c35e534ca20e7d0f325027c6510e218f99252cc33d54d0e10bb59721887ae4350b20dbd4a520c3b74350441b758c511035f53d0940db949510c33f5495320d754d430837563546209f98054886de6310310cf98d54086f76350510bd58854c435f53cc9209f594320827d6194c209fd8953106be648c8209f99053086f9600c540b758c21d027d65d0010d799153086f56408510cf550430835d5350440eb98a4350b6e52c8440dd9835150a7f6254e40db94b218435d6315020d7985530875e53cc3109ed9510043ce5394840cfd53414c76e524c820b798243cc37551d0230bd59643c43763294420bdd85324c27f6354640afd95411073d54d4632dd14f10842f66508110af19130c825e63d5020af992514c375518c440db548510c33d548c4309f993524427f6510f10dd18553482d563085109fd95410877551504209f596319027d6494c31bd590524427e61951209f59053886776550b109f597428427f6550a30d714e515033e43d49439f596420cade6390a31bd592414427c6254e40dd54b21442b664d4f10bb189504c7766115310cf90d529037a60d5231cf98654082f46488421edd5341443765314b10dd54430082dd6310030dd145504ca3e64150219f596321067d6494321b798c42cc67e6294643db94b31102f463c8110bb58e42c827f6510730bd984528c23d65950219fd95414c77a5288210dd58a51043756194910ee952200832c5250941bd98443486f665d0f109f594321027f658c840cf152404c33d5490f10f594f410867e658c540bd98a411075f53cc941cf59252cc2f56190d41b7597430c36f5288530dd547310c2766194342fa58242c82f6608c110bdd8e20c42f5628c110bd98243442fa6088710d
  | 25 => 0xa7e60d5021afd91304427e6494b31b7586324cb3d5490832e750c431073f5495131cf151418867d65d0a30ded42500caee6090b20d798e52d06de60ccb30bb58e32483d5534c910b718d40443765394b10edd8542502f96010a309f189544c67960d4c21d79855390a7f65086409fd8954cc73e5410f329f58650042ed62105209f98a5110e7d6550730d7945310c75d52cc230bbd8940c827d6095221ed95251082766194343d714e325027d6314910d758753502f6628c910db94d32482f561940439f596310c2f96088710f394d20083b55150040cf951400827d65cc440cf10e501027e63944209f990524c79e6410e309f59542cc73e5414c20fc4c620442f46250110bdd8543c427d6094c42bd99032442f66010710bd58742486f6630c421c7953328ca7c6054a43cfd5254482f561d4f428fd95411073e6195232bd984404827e65d0a10e710d420c35f5394f41fcd0e204435e5310420de59150086dd6310530d7186531035d534c310bb189404827e650c421ddd4f100437753d45429fd85548ca6f654c8329f58a53c42be648ca10bd59130443765354f10de4c550087b55450910dbd8953443e452109109f189540c73c5450b309f58e51d03f2608c7109d5865090ef56390310fc90520443796095110bd984304835c53cc921dd4c951902dd63902309f596325067e60d5231f5cca324435d6294c409f195420c27d6094732db94b420c2f563953109f58a540427f65508219d587548c36d62d4e20fc90e204436d528c840dd0c9519027e60d4d42bd584320c6ee608c920f550f30443b554153109f983540433d54d0830eb551520c33f5450d319fd9643842f56110d10cfd52324c35c6194c21bc58354c427d6414d219f997414c6f664d4110db54a210c27e6550810d714f43883b74350110bd19131c437551c8430ddd4a519027e6014543d7d4f325033f54909309f99741442f66414910ded81544836d52908409f99642482d663087109f58f51502be6414e20bd58453103b64310310bd18532d039e6250c43bd98443d075c53909409f98853483e75188521bb98a308827e6394341cf551210833f6455232dd98753886f561d0831d754c4310adc644c0309fd95214c3774254440bd98650ccb9f6350040d7d4e53842f46354b109f98854482ed62d0e329f592510c2f661d0f219b58b54cc75e530c710cfd88544c33e5450a329f98053083766194030cf553520c3b46150842cf14f42506fb6548210ded0d500875f6494e42cf953438435c53549409f594320437a4354021f94c9210867c6054a319f597420c6de63085309f595438427d64d4931bd986324437753544209f98e54882de63d4242fccc520443f1300c310d7953320cb766394420bdd8c20443ae54cca329f59540482f762551109f185520c3776554420b7d89
  | 26 => 0x18c310d75974390f5d5314f10db548524c75e53d0c329fd855010af665ccb10db9885050e7e6510910dd90a51082f463085109798c53082f661d4c20bd58e42442f661d4830db99152102bc644c120bd190304427d6014d429fd97210c2df6350330dd54f10842f6600c710d7d4e53442f6654c110b7d8d40043f042d41109f587525027761551209798c5408774518c530cf59252cc77a43940219fd91508c75d538c8209d987540835e534c8309fd95404835d538c210fc582424427e6294010db949329036f5294931dd58e518833d5410621d794e32d06be64c8540e71814310e7d6414e20b7583434ca7f654c5209f996434875d5354420af99232d02be6415020dd584528427d64d4f219f99442486dd63081109fd9421102f46284110db98d52102ed648c920bd59232443746154f20dd552510c2fa60c84209f595321066e6214143d7583535027e64d4931dd0c951082f561d0b419f189540c3f160153109f59442042f76150940cf989540c27e63d4a109f59632d06f5644c5109f993514ca7e6114940cf952510c2dd65d0e439f185530836f6494830bd98e424427d62d5010fc94920443b74310f10dd94741d02dd648c1309f59052c429d6490c43bb98b53103766588510b758e42ccaf46510b109f59421043af6450842be58342482fa60d0510c7553430c2f66194043f594d510827d6094443cf55041c433d54d04209f196214c27d6590c32be980320c35c4354a30bd986408435e53d0a429f98b548c2f5620c710ad992324437a5248020f654d401027c6154a30be580529067e6194a40bdd9020c436e528ca31bd58841443d66308110bd99132442de6390c30d794c43d0777654cb10edd08424426f65484219f195214427d6510b31dd50a519027e62947439f18d51c833f6455210dd94f10042fa6090430bb58843486f56114043bd58e41c427d62d45439f99541482f56550110bd98d21c43d532cc721b758e418c27f654cb10fc54b504427e63943428f592520cb7854540219f58354487b55410f10fc50040443f36054d10bb58840443d63214532fcc85204427d6095332d794c32c867d6494b10bb58a210873c6195021bd18d214435f54d0f329f597218c27d64948209f98653903775194542db94b320c33d54cc830bd1854210b76518c020ebd8942d075e538c010f354b32cc2f7604c431d754d321037a60d5210f3d0d520c3773254440b798c40c83d46354910cf18154087e64248110f98c92044376538c431d7d8053502f56114242af990530427d6014e21dd149511027e6315210f9d4b424427d65909309f983514ca7f6454e20dd4c9510827f65cc810d758f54c82f76350110bd58e324435f53cc120d754e420835d530c840d594e51082f66110320af59052042ed6290e42fc986300c2de6090c439fd85500c
  | 27 => 0x31d794f43c86be6414031eb98843d0a7d6494a31dbd95521027e6394841d7d4c32443f25188020f9c80204436f5348020b798c324c67f6355132bd98754ccb5f5308540dd55341c436d52cc430bd19121086ee62d0c21d794e210835f5394d41edd5254c4375514c640d7d4c314836d65c8621cf553300c2dc63551109f99442503f04188110e7d0f32d02dd6390810bd18532c427e60d4542f958b31c867d650c010d7952434c27d650ca10cf953438c2bf6350940bb98b4310af66410d10bbd9232c835d538c020b398b434cadd6390b30af5864350a7f6454632f994852c433f5450120dd550514cb774354420e7992324caef64508429fd97321027e63141419f58353506de6390b32bb988300427e64d4d21d7597430c2bd640c010e750c43886ed62152109fd81539067d64948109fd9421042fb6550040dd98a51102fa6088520e7951530835f5310d20d718553083e452d0910e710d424cabe640c120cf95241086be64082109f99721d027a6014810be98043883e53148421dd90d51902fa60c8610de105500873f5414930d754c5190af6608c910bdd8542082bd648ca21be98041d033d5490421bd584400427f654c430d718953083745394640cf984544c33e5350f40d7d4e534867f6510c30cf551430833f5450832ddd465050bf36144010bd5865090eed6214e10dd58e51082f56014f10de980540cb5d534c320db54b411027c658c940ed90d42443755254640dd59721c42de6390b30cf951420833e6415110b7d8d401027f65d0830ddd46510c35d5314e219dd8553483e552087109f98854082f7654c910d794e43883766115010b798e42042de6395121af993315035d6154c40f598c21443756454420c714f435027e6214543dd953100427d60d4c21ddd0d519033e5150441e7951530875c43943329f587504cbae4350920bb583328ca7e6195020dd144214c36f5294a10ded42508c73f64551109fd9542cc36f6550b20dd95251082dd6314840dd54f50442f46150a31d759743ccb5d63d53219fd94210c39d5454c21d794c5190af6650c910fc58231c425d63d5320cfd5140883da5354021bb58b314873e54cc421bd59031c433f6195020db98b530867c6354420bd984404c3755354440d754c531027d64d4e21bdd8d204437661d5332bb58e424827d64948319fd9642cc26c654c9209f98b530427d654c420b758f51082fb6248020dd95052c427c6590e10edd52424433f5495231dd18553c427e6590931dd18e518835c544c930af582439033c54d0931cfd52304c27e6510a31cfd5254842f66590910bb588408c36e52d0841bd18d40c43762154021bd98a30c437762d4532f550c43442f56494f10b758c21c42dd6314142f9d4b32443b54110531dd945300c27e6014d10de58353c437462944209f59353086f56
  | 28 => 0x951300c2f46488310bed81425027d6394410bd18542ccbf340cc110cf990538433f5490d10b758c500875c5350d42bd98f41c427d6055010bb98b40c827e6215210af993520c2f56448510fa8c920442786548110fc58241c427e64943329f58f54482f66510b10dd95252c427f6590810b7594438c35d534c440f314d32c83e542c8110ed90e511033e6414b10ddd8d511033d3015130dd15251883665254440de88650087d74354630bd98321c42f562cc310b75834390fea4248110be58042082de6310120ad99020442f56484110cd95151083d9300c210c7152304c27e62151319f18552cc2bf6350b40bdd9330c427d6588540f5cc2304427d6095032dd59731086f66310710dd50a518c27e65cc6209fd9721d03766194232d758f544caf5618cb21bdd8940443ae52d0b41fc98043442bd6490940bd58442c43f021c4110b798f50086f564c8710bd58a414436d52c84309798f54c867e61d5220ebd4a4250b3d5415321af590530875d5394642dd994514cb6f5294930ad19130c427d6114143bed81218433f6555030bbd89404827d6510430dd54531082f66090910ddd8552442fa6010710bb588540c3766508110edd0f404427d6394342bd592214433e5450c40cf55042c86dd6308640bd58630c82ee62d0f429dd9542443e452cc910b758c21c82ec6250d32db94a320433e5490710dd591519027e65d0d41bd58b31c86f76150a10bb98242482be64d4c21d7d4c435027e6314c21d754e43103d7538c910bd58e314437551902309f982540c6fa608c910cf95321087e9608cb20bdd89434437460546209f983548867e64940329f596210827f6550810d7d8d544827c658ca109f59543442de6390d32bd58b41c427c6550e219fd8953c433d54c8421e790d42cc2ed62d53319f586531033d5410f309f58a501067d65ccb41dd90d51082dd6390840bd98b31c42de63d4420e714d425027e6514d21cf550400c37554946309f997418c33c6454e209f197420427d6510a10d794e5190b746054630dd181511036e62d5030f9549511037653145429f59732042f66190020d7549300c2f66310d108fd95401037742145429fd9432906ae6290d42ee58343d03bb6050940d7d51300c33e43141439f18d54c827e64150209f994420cb6c5208530bd58730c436e52908109fd8152d0ef564d4110fc8c7104435e5394440bd98443443d46355110bd19230c43746314542db149324c76d5214a439f99532c436d5210b40bd58c20c437651d0240de980538427e65cc120bd594410867e6194232dd14e510827f6550c10d7585530827d6195131bd98630083d732cc310de94220042f465cc910b758c528435d53d0c40f594d30c42f56290110bd59231c43e551c8020f654e20082de6390840dd945400827e62951309f58e54c86be6414a
  | 29 => 0x443756414532edd5154c427d6394221f394e32c82bf644c020cf98254082ed62100209f59441043755148440e798c4350aee6290e21dd15321c43795014232be580428435f53d0d109f180524423d6414132d714c515036e3254032cf55151083b46454d10bdd8f214423d6414e10bd987404436e62d4c20bd995424434d53c8020b758c428cb6e520c430f554e51082f56550910d7984535036d520c831ddd45415035e6294c21bd59720c42bd648ca419f59642843355454430d9949510c27c6550931af590204435d5350020db15242c833c5450521d7d53434cb755114443b798c5050a7d64d4e10bd189544427c6354910cf98e540827e6114d40bdd92104433e64153309f98054087ce52ccb30db981521033e6055232ddd46510ca7e62942439fd96400831d5350040fc945300c37451505409f980540c6f6618c210dd905501073c61550219f58e510833d540c430af59032502f36054910ddd53414435d5314c20cfd53524c3745454620bc98321443d443ccb10e750c43cc67d65486309f58654ccbd5414c4319f593504ca7e6494c20cf953510c2fa600c710f514f31443b5648cb109f996418c27e61952329f5825390af66114420f54c030c427e6550e10bd9921044375510c440cf553420c77460944309f98e50107b66190140cf953420433e5414021ed90d43c43d56310310ee90e40102bd648cb319f98a510433d5450a30bdd89414427e65d07309f997428c36c43948309f99442cc27c65486309f19543443b8644c030cf14f42503da6090f309f191538435e538c6219fd89534835f6355220dd58754842bd6414a10dd94e519037b5094343db94842103746154b40ddd4f31443746394430d754c4390b6e54908429f98354c86f4614cb209f98653083d1300c110b798e420c75f53485409f59642c427e650c810be982435033d5414021cf550430c2fa608ca30f594c53c427c6354042dd94620042df6354910cf54e43d0a7c65d0f109f58b515027d6094d21bdd94324437561940209f98a548c6f4614ca40bd98642906df6250f30ad99030c433d548c820cf552420835f53ccb21dd15241c436f6550842dc546200837443544409fd91500cb3c6055232bc98020443d86050d309f99252087b76150b40e7d4d435027c65109309f58e52906de63d5310af597419076f6194840dd58454843775410710ed54740102ec6250721fcd0b50442bd6414b109f58e52083766194b109f194424c75f530c540bd99221c436e5210030d759443cca7f654c431b798c528427e62d4f10d794e430c37661940209758c54842f464085109f595430873f6455032d7951530827f65cc740ddcc5500867f6154043af98742d073e54d0020ddd50544433f5450130d7500535027c650c020db549401027d658ca109f996430827d6115220cf
  | 30 => 0x7e65c8520bb58850d0e7c6354242b798e52d033e6395021ddd46314c35c534c9209fd8d50d0a7d6550620dd50a510827d63d5010db585520c27c658c5409fd9152c42f16010910dd5835150b3d42d4540af99232c42de6308620bd984329076d5214b40db94a311027f654c4219fd9521086bf644c210cfd91548833f4254442be58241882be648cb20f654e500873d6590f42db949328c39f6350d40bb58840842df6250c43b758f428c77764d4542d7d4e53c86bc6454132b718d40843cd320cb209f5935388376520c510bd98640c43e75248510dd18151083b66410710db195424837752d4110ed95341c877561d4e209f98a50107e55148020e750f5210f796584010d7081530835d5310440d7d4d31443f265881109f992510cad663103109fd9641883e52008110ddd8a511033f54509309f9825290ef561d5020cf94f42d067d62151109f98f520433d6095021af59051c837b3194021bd185420427f6550020de597308c3766194343d714d425027e658c520af99331d03d55348421d794c511037561151109f99631d02bd648cb219f59442cc2be64c8740be980528c6f6620c710bd98641443b75450110bd18542cc3755208510afd9543d027d6255020d794e41082f46048510fc549204427e6114142bd58041c87756115032bd583318c6f46150e41bb58a31887f36148110d7d4f415027d6494030be983530873f54d02209758e52d035f3254432b758f214c27f6550b31bdd8954c43755314d10bb58a4350b6d5214b30bd9945150b5f32d4131bbd9232483e66210421ddd4b21c427f65d0420cfd52548827f6055331bb98b41c875d6394b40b798c540427d650cb409f590528427e6295331d798c53c827d6394421b798c404c3f26088710dd945408c33d5448430db54b42d037764145429f18950906f76150b40cf98a540c27e6015030be58031c437651d0230ee951300c2de63140429f1855010fd4438c110dd18553086f661082109f19153087f35488110cf993530837561d49109fd8d540427f6355021b758c529075f6194e429f98f52507766354440ded425050b755114540db952520c3e76150842de980548827d60d4f21bd99320c42f7614ca20ee181435033d54d0b329f98e5190b3d5415221b758e420c67e6094f219f994544833d54d0a31cf95042c835d5314e40eb508425027d6114930b798e42486f7658cb10d754c308825f6550c43b758e424867d65c85409f592534436c5490920bd98642c867f6055031bd994304435d6494c21cf552520c2f66114830edd935150a7f658cb40fc88620442bc644c440bd19331086f96088520bdd9031c42f6610cb319f992530c7d5530c421d7d4d435079d43540439f596329037965c8220dd54441902dc6350020bd58742442f5610c910d794f310827d6015321fcccb5
  | 31 => 0xd4f219f98e50c86bf6454132dec8650086dc64cc030e794e43102b7644c110db94b410c36f654cb209f992534867e6114c209f99641443766194040dd187504cae562101109f194328427d6095031cf95221087776154b40b518d40442746548510af99232903795014342db54832d06de6314442f3d8932cc3b65450310b798f404c377654c431b758c520427f6588430f9d89210873d5450a209f994400c2f661140329fd8d54442756194010bd58f52c427d6294443db54a320437761551109f582544867d6510d219f59632043d553d0421e710f42cca7f6254c109f984540835e6315031db54a420427f6454221cf151514c27e65d0930be58043103775394440af99743502f9600c640bd58c42c427d61950329f18953442f6648c110d714d43486ee62d0120cfd5254c879d4310e419fd9731902dd6390b41bdd94424435f6414d40cf15240cc2ee6210f219f195324835f5350d409f191520c3775254430bd98743087775108530bd990534436e52d0840af99020c437442544309fd94428c6df6450c43dbd4a5210ff350cc110dd94921086dd6308210d71825390b3d5490621d794d5190a7d6414530f9185320cb9e5490f309fd8d50907e75254b109f982544caf562d5110dd152524427e6590430c755253083f04248110fc945100433e5450330ed150424437564946309fd96329033e54508409f58f548867c6255130f54c930c433d54d0c10cf9514288375658c310d754d328833d5490710cf553410c27d654c910dd546310c35d5350820bd98c544427d6314121b798c51102fa60d0610d714f515027e6515130db548520c7e54248110e710e400c27f65d0d219f58c514827e6215330db588540c27f6055332b758f414c376520c421be98242443755108720ed10c5150abf6454530cfd81540867f6155110be58043cc2dd638c431bdd9231c437661152309fd8950d0f766394410bd59353442f5618c120bd987438c6dd644c9309d997414437651d00209fd9641087775154142cfd0d5010eee6215010be980430c2dd64cc930b758c21482f46150f21cf98a548cb3f5454930d794f21083745490510bd98432c873e6415232dd54741103ad52d0b40bdd9230c437661d5031bd98e214435d63149109f99643087cd424c832dd144414837b5094042af990504cbf1608c9109f993534837a4194021bdd8153442f7648c9109f992520cb5e53cca109f593514caed628c220d7d0c504cb7762d4542be58042d03b95488020d794d31c867d654c120db94821102dc6354540dd949214427d6014c21bd587434c6fb60549439f181544cb745344010d794f32886bd64d4420cfd5342cc2de6390b41f9cc932442fa600c640e750c43c86be60d0940cfd53404833d548c020dd544410827d658c421be983428827f6550c20bd58042c42
  | 32 => 0xf54cb310875f5354940af9834390e7c6255310fc94a204425d6395121bd18542487765150620cf550530833d42d4141b758c214c3f353d4110b718143cc2f6618c310bb98851102f5628c310f5945300c376510c0109f992520c71d53d00409fd95320cb3d5450020bd59352c42f66110220af590500cafa6010520ed590304427e6548530bd18d42c427e6395020db948200437652d0421bd586304c2fa60d0740f998830442ee6214e40dd54621082f96014c42dd5845050f5c6154c40db94e320caef6550b20f3d0d32c833d54d4232de98052043b651d0240bd98421443f362d4110ddd49518c3e742d4542d554d51082f662cc310bd58743106f463c8310cf950418867e654c9419f59251ccbf16088710fccc230c42f6640c721bd192314436e52cc8409f58252d0776510c2209fd8d51d02f76155132fc90620442d56308110b758f42cca7e61948409f19442442f96014432bd98341c435e53542429f597325067d6510821bdd8553c83f26054620ed50941c43775294440db54832cc3e552544309f99052c42dc6350a309f99251cc27d61953209fd9631087d6534c910d354d200827f6054841bd586429073d5450c30d714f434837663946409f592500827f6510c21bd185420c77561d51109f19521cc27d61942329f189508c7b64354640f9149214433e5250b41cf95040042f76150b109f99721903b443d0910d754d5190af76448710dd54f5150b5e53144209f1974148375510c220b798b434cb774254430bd587324867d62d5331d754d4390bf35010110bd996304435e538c431d7149324c3f23148110db50e520c2f66090f10be58342883f064d4110ee582439027561141439fd9743087d7614c9309fd91538873f54509319f98253087ad54c8421ebd8942503745210710dd14b504437652d0510de90550086bd64cc9409dd9532c427d658cb109f59521cc2bc63500409f58354c86df6354940ddcc5508c67f65d0e20f98cb20c437463546409f98a509073f54d0130d718153103766115031bd18553483754354440db94a42907e642c8310db54b40102bd62d0e439f997438827d61942429f99252842fa608c820ddd92510827f65904209f58f524436d5214a40fccc6204427d61d4d20db98b53c83ae52500409f594324427e6590d20ebd5142c82f663841109fd8154042f4614c920cf55340c827c6550d31dbd85520c33f6555020dd952411077454c85109f98453883756194232de98054082bd6414830d354d52103744314542d794d4390a7d6295120ed50b41c873f5450920bd181434431c5450f30eb953210876c649484097195434c2f160d4b109f580524c77a60d50309f596540caf66190320d7951324c6f565d0b109f983540caf662d0110f654d500865d65d0c30bdd8142c433d5310e409f58b548c36e62
  | 33 => 0xc920843786294021bed8131443763254440cfd5040cc37760d45329f181544c7795014021b798e428cb3c2055020bd59742442f562d4d109f99353442be60d0b40fc48710442f46154f20bd587538827e65d0e10bdd8c20c42f66108310db94d52102fa600c5209f19732043f06448110bd98332c439c5390140af9884350af66314910b7992324cadf6350110ddd88514caf461549309f992530c27d60d4d42dd544210c27d6394821bd59130c427e6014e21cf94140103796014c21dd589510c27e63d5031ddd8e518827c6154042dd981510c3ea4248210d7588535027f6354b40cf18a548cbd95390040cf55054cc2fa6010840db94832cc75e6394842b518d54443f1408c1109f98c540c27d65d0430bdd85320c36d5290430f394b300c2f561ccb419fd9152042f56348710d754e43883b65450b109f59743842be648c920d7d4e53d0b9d54cc030f590d30c43746014542bd185324c27f6055110bd59431c875c53ccb219f586538836e528c430d798c54083d5320c9109f59431903d7430c110b798f54c87f32188110d7189530876e5248430dd146504cb7653d4110de94a200833e60550209f99740443cd324c720f34c83248376658c110db94942043f24010110bb58b43c83ad4210b40d794c32c82fa60d0c40cfd82540875e5450c439f98f540c3d6434c431db98a53c827f62540419f194414c3f031c4110dc105500867c6254f10cf153434867e63d51219f99250082df63506309f592518c3f34248110bd59021c42f66408710bd58f42443cf524c931cb553200836d53948409f982531067f658ca41bd58642c877664544309e583548c7b46150b419f993524c33c6295021af590520c7745188520dd98753882fa60c8720bdd8d41c436f64548309f992534437b65482109f197414c36d52c8610bdd9742c433d5410c31e758e4250af86048510ddcc9510c27d6214530db94b300c2fb634c030cf99054c825e63d5021cb551520c2de63d09329f596400839c434ca40cf153414c67f6154c20bd984308833d5410821dd94731cc2f56588310fc983214427d65908219f98254cca7f6590910d7949320caee6214e10dbd4a528c67d6510e20bd994544439e6390942eb592320cbf26010710f3d4d324827f65908219f595320435f53909409f593514827d62952319fd85544cb3e54c8020f554e51103765150410bd996204437a6254021bd58a544435c6254e42af59032d03f043d4110af59231103b764504419f194410c73f4254042db98b548cafa608ca10dbd48214c33e54900209f59521d03b55494420db988540836e5208710ed90e40442bd6414331bbd8931c86ee62150309f9865010b3f6315130b558c21c43755150620ded95200835d53d00209f98e51d03f16190040fc085204427c6550630af993518cb5d538844
  | 34 => 0x8835e6314f21bd98854442f76350310b7d8d408c33e6095021dd5865090b755114743e750f5110fe642483109e983540875e5494c21f88c920442f86050d10bb58840c435d6054e42bd58841c433e6095232b718d40c435d5494c21cf953438c7755114630bd58643906f5610c010afd9130c427e6510e109f98e52042fa6088620d7d4e531037551cc030f5d0e518c2f9600c520dd4ca518827f65507309fd8553d0b6e5450842dd94721c83755190640f354e32c837a6015030f890920442dd6390910bd99443c433d5410f219fd8d518827f6054d21af990308833e5410631cfd9153442ee620c110e7551530835d5314f209f18d54c43766194f10dd597100439c43cc840bd98640483b554503109f596315027f6254f40af590208427e6414520cf95340cc3775194520ddd4f310867d6550932be582410c37660546309f59631c82bd640c110bd98632c427d62d5330d7d4e515035e5350421dd950524425c63552209f988540caf6640cb109f58e544c7743294410dd547319027d64944209f986520c33d548c421bb988521027e65d07209d987548827e6494b109f982540cb745288710cf95231086df63484309f98c52502f56110110cf55142082ef6548421bd18542d067e61d4810bd99432c43b742d05109f994314867e61d4940fc58052c42f5618ca31f9905210867e62d4e109fd815210ef66508510b71814310f7661940439f18951cc39c6454c40de980540437532546209fd95414c35e53d0f20bd59743c427e6214143bd98630c82f6608cb10be982425027d6550d20db98853c83746254430cfd52540c7d7328cb10ded91500876f6194830bd984531027e65ccb40b798c210c3775194720b798e424427f6454430dd99251042f463c8510fc153504437554944209f58c54c43d543cc310cf550544876f520c910cf990530837651902309f58c525039c644c030b798f52d06f56110f10cfd8e540836d5254430db54a21c42fa6010530cf55041043764254440ded9540102f66190d419f99741483f332481109f997214437463d4542db94a420c2de6315021b758f42cc27f6548730be583540876d658cb20edd0d40c427c6454331db54852d0f4f43548309f99543c83e942481109f98e54c835e53cc8319f18552d0e7e6314810bc98232442bc644c220cf151434c77432546209f580544cb6e520c831cf552420c2dd6390a32bd98c424427c60547429f997435033d548c8309f994321027e6414530bdd8542903795014332cf95342886df63508309d986508cb5d6394842dd94841c43756114e20e790e40cc27d6194f42cd952510c2f560cc421dd18d51882f76348310bb98840cc2ee6210010bb988548c2f860551329f58252d0ef76150b20bd192214427d62d5310bdd85325075e530c621b7d8d5050bb754d0110fa8
  | 35 => 0xd4210a329f994319033c6255030ad59020442f86050e30bd59731c423d6494d21dd989510836e520c440db14832442dd608c932af9944350a7f6454a31cf95120082fa65881109f98754c836e6215030cfd5142c867f6354742dd14c524433d4254341cf95342087755190420cf150438827e61d4142e7550430c3d54310f109f987540c6df63509329f997314827c6454e209758c52c432d5448020dc885500867d6294241ddd4521483f33048110b758e428c2bd644cb409f5805250e7e61d4f20dd94a519035e53d4840fc481100427c6354221bd18c21c433d548c030dd147314827c650c810db949218437751c8530dd984540ca7e650ca40bd19030c436d5214a30e750c4310a7d6095120dd5865010ef66514532dd547219027c6454f109f996404c37654544309f58a53102f56114332bd58643c867d6394841b798c521037563d4542cd185540867f6054632d594e51102f76548110bd98a310c7bb43d0140f398e4210add6308310f5d0d32442f46154b40cf95142ccaf76544010bd98650d0b6e52d44409f19532842f764c8110db10e52103eb2194021bd98e42c433d54d0821af59332d036c5450920dd14b10843b44310110d7597308c27f6154d21de980540867f6454f21ddd4431482f5644c710d754e41102f56010d10bdd91524427c6550f21eb94b401027d62950309f99742cc3cf434c920cf550428cb9e6310e40b798c42cc3d66308310b798e428c33c2155021cf182540c27e63d4121dd50c5150b6d61948409f98a54043755110030f558c21442f7614c832af98a4350b765450510ad99232c427c65ccb109f185544836d528c430be982420827d6294743dd547310827d61d4142dd947200827f658c810f310f324ca6f6548020bd18940c43f14010310b5d8d52442f66110510bd99132c42f5618c8219fd95400436d5208430be58331cc27e61952209f99442cc6be64109419f592530ca766114e20af990530827e6294341dd59440c43765190020f98c920c427d6590c30db548420c27f6054742e7553438c36e6214c21db98854c86f96010b20f310e520c3d7518c531ed95340c427d6294440edd0842c427f6550f20e7951300c2dd6010f32db15142c836f5294a41db94842d06f562d4f10d794f31c875c534c110bd98732107f341c4110b598f54c42f6630c510bd9845010ef76354b10d794f43d0b5d53cc440dd55350442746154b30bd58b31087776454620dd98151882be648c930bd18d21c42b56414b109b588548c23f64549109f99641082f560d05419f988514c35f6354d21bb58a40882f6640c4219fd8d54c827f6054a43f34c8324c277654c431dd4ca51042be6415021dd0ca51882fb604c630f90c7210876d6214e20d7592530835e534c720bd596324433e6415131cf950420cb7662546409d58454
  | 36 => 0xe319f994428427e6194b309f59641087756154341bd185428cade6514d409f59731082ed620c621bdd9543442f56290310afd9542d07f36188110be583539067d64145329f98b54cc33e6415231dd54531883755114730dd19542c435d534cb109f584534835d6094e42cf55341c86fb6048520f9c8020c433c52d0940bdd8552d027765484219f58654482bf644c320d798f540c67c6550a31ded8154443e65248421b798c52907f364d4110be583530875f6494c20bd58853c43784294021cf150438c3cd324c5209f19632507d732cc531be9824390375510c4309f98e5090b3d5450330db549328c3eb2154021bdd8542482bd648ca31be983539077743944109f990530833e4314142ded42500c67d6510931d798f540cb9d5490f30ee552300c26d62150309f58054cca7f6510b10de583540867d6015231db54b320c35d530cb20f994b20c423c6454d20bd59731086f662085108f59353c833e5450c109f59353c437451541429fd9442cc27d6094910be58032cc3755114740f6ccb304c2ed62103209f98e52d07755114640fc94610042be64d4232db54a40103764354620dd15021c42f6648c510bd984400c2766114142dd945410c35e5310c42b718d40c827c6354742cf95142442ee6210c429f59643483f3604c5109fd94420ca7d65908319f997311036c534cb20bed81321033e5410f209f58252107d5324c510ed90d42c437743946209fd9543842f66194143dd18251902bd6110f42b758c54083744354430cf953320867c6550b31d7d85530836e5248440cf552418c75c53901409f996319027c6254743de58354c839c544c930db94832cc27d6315120fc10120443756494420d794d320873d54cc821dd94a21c427c6454b31e7d4d425035d53c8440ed55142c42fa6090a109f586548835d5310f42bd58b434433f54901309f992530ca7e654c8109f58a500427e65cc931db54820043746154831bd984510c2ef62506209fd8152043d5538c710bc58053c42ed62d0d20be580528c73c5350d40f598c21c427c65d0e20bd995434427e6508530bd986404c3774354620b758f420c6fb6050a409f58e548435f534c921fc50f504435f6354c109f596530873e64d4f10dd547210827d65950209f98054443776394410ed9085150b5d5454c20bb58a43c827f6255030bd59232c433d54d0020db186520c35e53108209f99643c827e658c1209fd8953486be6414b10ddd8554c833d5490230d715243cc27d64d48109f58a53107746294630dd953514caf46155132dd551100427e6494c21cd55151083d66310110af59053042f5654cb10cfd9542d037663546209f59053442f464cc9109f596300439e43d0930cf55142ccb5d63d53109f59643106de6310220db54b420c3ac5250b40bb98b511036c538c920f358e4210ba
  | 37 => 0xde186500867e6094f42cf151414c2df63541419f5885150ebe6408410d7d4e4350aec6050b20d7d8d548c2bd6408730bd18543087b554d0310be181435035e5308420fc8cb504427d6590630af59021043ce53d0a42b7d8d400837b5094341dbd89544427f6508630bd596434427c61553209fd91508ca7e65cc921bd984320876e5250030b358e42c833d54940219fd8953907733154021c7550434cb3e6155020cfd9154086f662d5110ddd5041c863f6454d20cfd52540877554c4210bd59721887d74390d10d7d8d53c42f66494f10bd98631086be6414632cf553428cadd6390940bd59121c427c6154232fc54a20442bc6454d109d984540827d6550b109f59632102b66408310ed15043443764214542afd9542d027e6510d40d794e310837452cc710c755043ccbd7308c310d795132cc76f6254a10f950b20c435c6094c209fd8951d03e741c8421dd945310427c6054e219fd9520042f56390b10db94b411036d6214e10db988530827e6494620db94e32c82f6658cb10dd545401027f6454732ded4250cc67f6354420afd91211027f650cb41bdd8940c435d534c841f6d0e300c36e5250a41d7181530875f53ccb209f98352043756114c20db988548427d6095110d794c320875f5394e40bd58a41c42f46150910db94b42d07b74290910dd58654486be6414720dd151518c35d6395130edd0f40c437965d0240dd59420c43765455110e750c43087796014f10eb50842c836c528c9309fd94311039f5390d42dd98251083e46254d10e7d0f408c27e6510d42ddd0f514cade6390940bb98b438caf7634c4319f99542842f46150e31cf951300827d63d41219f18950d067d6294d10fc10d204427f6590f219f195321033c5250941bc98242442fa6014841fa94a300c37563546309f596530435e5350e10bd19643c43f3304c1109fd9532102bd648c821db549420435c6194c208f990538833d5450e31be582218827d6294f40cf553424427d65d0020bd987328873e65d0941bdd8552cc2fa6014c41dd544510833f5410e30bd18530442f660109109f197424c27a60d5231dd984548835d5314e429f995325036f5294b108f990504cabe64ccb40dd545210c3f35348110ddd4741483d56314532dd592510427e63152209fd895190ef662951108f993530827f6354341dd94531882f6618c120cf95342c42ef6254131d7d4f31443775444010cf952401035d53c8020bd58041087765150440d7d4d308837661d5030bd19742c43765254430d714f405027d63940419f59642102f4654c910bd98343443775208710dd90e510433d6395020dd14910043f265481109f986544c3764394620be58332cc2f561cc910bd98443c435c6154c219f994314c27e6590d10af590510827f6550110cf95240883f06548110fc583414439d431
  | 38 => 0xe51902f6618c1309f594211035f6194c20e754c43102de63d5320bd59630c43766195310fcd01404435f4394030bb58a434827d6590a31cf90d52102f763c8710af99252cc35f6354d20db50e521039d4310f329f98854c435e534c4219fd9530482ec624c721af590300827c654c540bb58850106f86050c20bd98454882f561d0b10bd58432c427d60d4e21f394e320caf661d0310bed81318427d65cc821f98c8324435f5350940cf990544caf66394b10d718753502f563d5310bd584400839e4310130db548400c3f25150040bb98843d0add63086209f994404c2f66395310d754f43c433d5414830d7d4d314873d65d0e43bdd9643c427e64d4e20edd5254443b542d0421b7d8d40842dd6390820dd15021442bd6408310af59352cc67e62947409d586508caf76050441d758f540875f3254331bb988300836d524c841f6580430c27e6590f10fc15120442fa608cb20ddd4a518c35d53d0f20cf552408833e5450430bd98242c437754c4210dd587540c27d65d0421cf553328ca7c6454420f3149324c75d544c0309f98a511027c654cb41be597308c27c65d0910cf14d425075f6454c21ddd89518c35d5390020d794e430875d53d0c41be980500877a64540219f59052042be6408440dd4ca511027e65d0a31af59021102f5618c220d754d32886df654cb30dd90f514cb3d54151309f191500867e6115010e7152434c3f04288110bb58830042f56114c209f990530437551d0430dd953108427a6015031db54a51102ed638c8329f98252d0e7e6588440d794f43087743294440dd94b31c427e6394021fc485204427761551329fd8d54c435e53d08209f98f54c427d6494632cf151420cb3c6395020dd58650d0b7660946409fd815390af96014843cf95341c82be6415030bd98743d067d61d5232bd99053c43776254640be58043442fa6014a419f98e53442f561d0f21db54b300c27d63d4142de58054cc37651480209f58b535036e52ccb41bdd8f20442f76150930bed9510042f56090441f354f4290b784254021bd587531033d5450030bdd8e10443cf528c932d754c53443f36054910be181218435f5394e41dd54e519027d65cc5409fd95438827d65d08109f984530427d6590d219d5865090b5e6454c20bdd8943c436e65909209f984548c33d64d4c209f58f5150a7e65909219f995314836d65cca32bdd85324c7d553ccb10cf99353086f76250710dd597318c6df614c4319f58a548c2fb6054d42bd584529027e65cc940bd19021c427d63d53219f993504c79d6414d40b7997324c2bd6414031cfd5143cc3f03148110af191300c2f46448510dd0ca510c3766254630dd54f31c427c6550e209d98453082f56488710e750c43d0a7e6095221afd91319033e54940219f5805150bf242d4110e7d954310ebe6408730
  | 39 => 0xc2f663081109fd95418837453c4010d7d8d544433e6494b31f34cb31c827e65c8110d794e401027e62d5020bd19331442fa6010620cf550540caf965c8220bcd8153443786394021cf950310863d6494b30be18142cc33c54d0d329f583524c75e52ccb30d754d200833d54d0a10dd991518c2dd6290f309f996420c7775194743b7993300c35c544cb30fc18d204425e6315210be980518caf661d5230db10d520c27e65105209f195424c3775314542f998821442d76350110fc18e204427e6195320bd98450d0e7c6510f21e794c43d0af86050e10ed18542502786055132dd987548876e528ca10ed15341443b654104219f19643083d553cc310b798e410c2f66190821de085500873c544c9309f59741cc27e6395321bd58440cc2f46150a30db952424836e5290a10bd582534435d54d0e309f5865390b3c5490d20dd54741d03766054420b758f540867d62953309f58253106de6310030dd949518c3e52008310cf55342886ee6210f32b758e428437763d4532bdd8a104433e6415310af59030843f3508c110fc8c620442dc6348630b718d408c25d6314910bb98830842f562884219fd8d5110a7e6115130ed50c434433e5410c219f983544cb754354430bdd97424433d5454632de14920443776454430fcd0520442f460487109f99432502de6315220cf952418c73d5490b21bdd9232c43765110410de98354042f960109309f980548cb9f4350230dd98754086f66410421bd584408427c6550720cf150324c35c5494c21dd14e511027f654c8209f983548cadd63909429f58753882f661ccb31db949420c33d54508309f194420cb5d53548409f988548c67d654c740d754d31c827c6155132db951520c2f561102309f195414827f65d0c20b798e400c33f54d0921dd146415035e6094c40d7d4f51502dd61d0d32d7152434c3ea32c81208f59252cc71c5450d30d7152530827d6494c30cf9524310af4614ca209b588540427d6510c31d794f32082de6390a10de8c550087ea42c81209f5865310b765110620dd50951102be64d4430dd4ca510c3b54110631db18652103d66314910f510e30c42fa60cc430cf55342c43d6534cb10bd588404435c54ccb319fd8d501075e6315220db94a300c3f061881109e980540876d62d5030cf988544c2f66314b10bd98753883e65248310afd91304835c6114d40cf951500877454944309f5835150e3d6414c20b718d404826f6254d10d7d4e43486bd65d0e439f581520433d5490410bb58840482796014c21fa50920842de6390942dbd8e521037b42940219d5835150aee6214341dd14a51902766194042f954852c42fb6050920bdd81324439d43548439f99353c873d5454021af59443902f56290d109f19431503755110620b798e420833e5350b40de582544c27f654c5409f98
  | 40 => 0x650c010d758c548cb5e538c2109f99253c827c6454221e750c431035e5310421b558e42442ee6210110db548511027f6355220af58e40503d6414c4319b988540c33e5410c32be98332483b74250110dd547401027e6510110dc9975044374534c5109f58654cc2f76550f109f587530833c5494530b518d40c433f6455010bc181434427c65cc5209f58e54c836d5248430dd90e511027d6094a41bd58c54443f26388110f5547300c36c6054830cf952430c67d6395220af994544c27c6510010ded4250ccbd7324c110b798c200435f32d45309fd9431086f5600c910d7d95320cadd6394540b798e42d02de61cc9319f18153d0b7653c4210af592321027c6154e40dd945310c36d6295120bb181424836d524ca40b998830443555354440eb54b42d077661d4c10cf551210875d5314e10bd98b40c42f4650cb10dec85500877a2154021ad590304439f6350f409f99250c873e54d0a109f58a51042dc6350130ebd8942d039f5310e40dd54621902f6648c310bb588404c35c62d4d409f19531103f342881109f588535033d5410c21b358e42482df654c8329f594420c67d6550c20cf985548cade6394940af993325035e6395121bd997324427e61141329d987520427e65905219fd96300835f538c940cf151414433f54d0521db98853c877442546409f58153042f46150940af591325033d5454830cfd91540c36f65548309f58c5050bf14348110bd984504cb5f5314540d754c5350b764394430ddd51518c36f5494830dbd4a5290e7c6054642de8c6500876d6590b209f99632482f56548110d7d4f405039d4310f30ddd0e51103d6534c431decca500873e5448421cf95043c42f76148110db94a321039d4310c109f59730042d66390910fc18b50442f6628c5109f98a531037451c8540db548310c27d6590c40fc08620442ef6254141f950920c427e6095232cb90d521037b5094141ed508424436552544309f99743c827d6395020bd19152442f4640c721ded09500867d60946429f19153c86f7614c841dd587530827665c85109f594424433d54c80209f596540c2f46150840bd58f40442be63d0240cfd5254083ac5450b20d754d51102f6658c910eb508424835c6355030cf99052843e14248110bb98a430875f3254032dd94951102bd648cb30af59232042dd6394b419f996430437a60d4c21cf552400823c6454910cf18a540c27f65ccb41bd98e21c43d453cc110bd586504cbd75394f109fd85538837751945439f594329037562544409f9865348376514c020cf18254087774394430dd101511036f6548421bd59730c42bd64d4f10bd99331c86fa6010910d798c52c42f56190821f354b32cc73e540c8309fd89544c3765354420ed55041087e7324cb10fc580424427d6550810d794d41102fa6015032cf55340c
  | 41 => 0x132fad81324827e65d04309f994544c7b643903109f59531882f26588110ed95221086f661d0d31dd982518c3e63148421bd986408835d53d4642fc547308c3da5350040ddd4721502f960d0c40dbd49325074c524c931d795132cc27c65d0d20fc591204437950143219f992544c67f650c410ddd53504437752440109f580525076d52d0430d794d32907da5348020dbd855210375518c640f9d89214436e6215031bd584304439f53901409f98054ccafa6090b20de580540c6f561cc831ed59030c435f654c4319f58f54487743154021db58b54cc67e6115021cf550438cb5f5394c10be580318827e6314540cfd5042443e6620c3109fd85521027e61d49309fd8953842776154d21be982429027d64d4d21fc58f504427f62540319f5805150ef9638c030dd909510c2f66114e409fd8d54c867e64d4f20b558c20c437651884109f59053c867f6510f21b798c524433e5454c209f594420cbd45310d109f58354887d5530c710bd996404427e60d4e21bd19231c435e534c8409fd97438867e60151219fd9743443d4614c930cf953410873f5450d21db548521075e53cc720eed91300c33d54d0421c7553300c27f65cc9109f19150ccafa60d0e30e710f428c2f46150820fcd4140443765188620be597409027d6094f219fd9432903776154d219fd95414873e544c830f558c52c42f661d0d109f59621d02fa6008730d754c32c867e65cc930dd989510c2ed6210f20be98021043f33288110cf950434ca7f6354a10cf153434c37651087209f195430867f6510c20ed10f42c427d650c821d754d300835d6454c209d185544827e6295030bb189414875e54cc930db98b540867d6590f10dd191518c35e6054c209f994424827d65c8640d794c400835e530c8409f588504c6f5650c3109f59253c435e6314c21cf950420867d6215310edd0b41086de6310a32bdd8530443763254430ded5250087e732d4532cf550310875d5310840cf55331086b7644c310f554c43c435f43548309f191510c2ed628c4219f9825110f7b4394021db94b400c3784194021dd546218835f54d0c30dd996414433c5450931dd1465050aee620c621cf990540c2f66194d42bd58332442e562103109f58c528423e64d4f10cf553400c2fa6010a30ed59353c437565c8621dd586500cb3e5490b20dd10550c867f65cca409fd9153843775194740d798c538827f6354021bd193214437b3154021bd181424435d4354043d718d54483775190540b758f40cc27c6254c40dd10951082f561c8110decc950086ef6250d32bd19542c43766154021bd98a42443755114520bd18143c42fa600c620bdd85435075e53cc020f594f43c43f2408c110afd91538827e65d0f10b758e42d03796494021fc5825344376514c440cf54e431027f650c810bb189505067f
  | 42 => 0xf550508cadd63d4440cfd52544cb76619513297d95310c77553cc7219fd9742cc27f6454831eb151424833c5490d30dd546300c33f5495221b7d8d514833e52d0b40ddd4c53c427d654ca10dd18951903774254640dd54421082f66188510dd54451c839f6450d30d794c310837551146429f59251cc3ba6010c40be58041042f561150329f58754ccaf561d0110bd19542442df63503109f196324427d6315321dd94b419073c6095020b758c510833d5410210eb90d52102be640cb41f54cb314435e53cca209f584540827e6015010e750c434873e54d0a309f58853442bd648c921e7550434ca7f650c841cf951310c3795014142cf550540c6bf6350c43ddd8c514cb5f6494c21bd984320c7756114132d754c43d027e62d50329fd9732907cd32cc5209fd85540ca7e62d5231dbd4a324c2f66550b10dd94d534433c5450230be58021042ee6210720be58021cc3765354440cf58f544c27e6394b40cf951430877852482109fd85544c7f350081109f980540ca7e650c540e750c430ca7f6548020cf551430867e650c931d795153087ce424c832bd18e20442bd6494b31d7551530877b65540219f99430043776544010fa94a208433d5415110af592320c7766394440b758f5090bd5320cb10f5d0c30c435e6315030ded51500875d538c4409f99253886de6210d329fd8153d07b45490910b7996434c35f534c6219f997434c2f56110f41ddd53410867f6155330fc90040c427c6354740dd485500865e6314c21b7d8d544839c6150c43ddd52510835d530cb41ed59052442bf65500409f58e54c435d6114d409f58a539075e53d4642bb58b41c867e61952309f58a5090f3d5415310d794c430827d6215230d754d41086f46150a10de58d5008775518c420bd58f42c433d61950309f185500cbd44354430dd545418c35e6454c409f99743c86f56190c21db58853482f6610c5109f992524427d6114d40bb98b31c867e6314a10bb98b414867e6195132f5186530867f62542419f983525076f5250941ebd4942506bd640c540b758a4310ebc6150941dd544219027e62d41419f588505067e6494732cf151314c33e5450841dd98d510827e6508640ded81544ca7f6054b419f189540427f6254341be583314433c5410520af59232106be6310c40dd5085150bf23248110af99232882ed62cc720db94a32106f462504419f194420427f6355020bd99130443765294630b758c210c3755254630fc90920442f5618c030bd98742107765244010dd50550107776554630af5905388377530c510bd59420c42f56190f31b798f414c33e54d0c30bb988408c27e65d0831be98021102dd6390a31cfd53434cbf262d41109f997424c75e534ca409fd95434867f6054f429f19152842b66414b10ed552210867c6354b10cf550418c6746155
  | 43 => 0x53083d763549109d18554c833d54507209f18953107ae648cb20dd546418827e65c8530f558c21c427661152309f99532443756194332cf550548427560145429f99731443756194d109f59530443ea5248020dd152518c27f6510d10d758c54843f23048110d754d5090af56194d42dd544514cbb54010110dd181510c27d6494232d7994434cb7a61540219f982518cbf1518c0309f58e518827e65109319f582510ca7c6510f209f59543c87ac4350b20d754c320867e6315321dd947310435d6590f309f993530873e6510d429f59632502bd648cb41de98d50086f46150b40ddd90514ca7e6014c10cfd91524433e6494d219f5835150b3d5415230bbd9132c83f26448110d754c5310b5e5348420de58054c43d7534c110b759743ccafa60d5231ad19153442f464c81109f191528c27e658c440d758c548c67c60548439fd8d548867d62150309fd815190f5d53d0840ddcc951902f4614c830bb58853902ee6294d41db985521037651cc620b7597308c2f9600c9109f195214c27e63944429f99732842bd640c310cf95142042ee620c3109f58e500433e5410210fc102204433e5490c30ed90b5150af463c8710d794f43102de6310530f958830442ee6210d219f588544c67e6510f21d794e439033c54502209f98f54c827d6194b40bd5845050b5e6315332d794e21086f663881109f587544cb774154021cf986540c25c6354910eed05401027d6414131bd58440c427e65ccb10de0c6500875d53d0f219f597418c27c6510b10edd0b41c436e6194830ddd85544c67e6510020bd584539026f6255110ddd0951083f1600c910d714f308827e6414f21be58041102f764cc910fcd4210443d7614c832afd894310ff06148110dd98453042f560c8621f3d4d32c837551cc620bd990424433d53d0240cf551420c6f7614ca219f597314835d530c010e750c430c73d5410f10cf59741907e652544409f99732d067e6510a30cf14d425031c53d0940db548524c36c6255110b798e42c427e65d0d31fc106500867f6550a109f98c5050abd64c8540bd19221c437960d4f209f597200436e6214e109f19532486f960084409f992518cbf142d41109f58e50907745114142bb5924210a3f65508429f19643487b66414910ed186540873c4354a409fd9531486f4614c941dd149518c27c6454d10be5805110b3d64d4f20b7d8d548827e6115220bb98a43ccb5e6294e429f98c530436d43548309fd9532502f66310b10cf950410c73e5488020ed18542d031d5410c30d518553086f96014642de10e500867d6195232dd94441103776154b41be982324c33d52d04419f584540ca7f6588440eb55242c82f76150a32be580438427d6395010fccc2204437a60d4e10fc881100433d5448020dd944410c3d943cc130d754c211027e65cc810c
  | 44 => 0x27d65cc820cfd5142cc2f562cc510bd19332c43753214532bd98643cc67c6154d20bd582310c76f6255121bd587430867d6294231d794d30c42be6408510af59031d033d42544429fd96438837554c4010cf551438ca7c6155030d794f43d027e6094841dd947218827f6155332dd54640102ed62cc520d798c53442bd6408510dd545400c27e6094c42f9484210439d4310f419f98a548436552944409f992528c3756588310fcd43404435e5390e41af99232506de6390b20cf55141cc77661150219f5865290e7c6254643ddd5054c436f52c85109f58650ccb6e6214b10fc105500867d6594c209f594310877565cc721cf95140c82f764c8310e7d8f544c2de6390a40bd994434433e5350b41cf95353086f661d0a21b758c5090b5e534c440ad59020c437665c8510be980310c3d732cc7219fd85531027c650c940bd185320cb7b52440109f58f528427e60d5121cf58d54083743254630dd95321486f96090f30bed81328c2dd63d4742fa50b20482f661941329f98f5050b6e5208210cf99054842df648c1309f9845050f6d528c8309f58b544c7f043881109fd96430435d54d0d32ddd8554c877652d4110de0c550086f46408110fc58354c427c654c110db54a420c35c6214d40cf152434427c6508530b798c5090b766194042f5d0d32c427c63548109f98753882f56414f109f59721cc27f6055121dd14d31c43776494430cf551300827f6510e21bd58043c427e6590a10bd587438c7e72088110dd15151083765190410cf952420867f65d0a109f5845250f6c6154830af992320c27e65d0e21d794f410835d534c721d754c52102f56210d10fcd4e204437a6494021b7d8d40c82df64ccb30ed10c40c42f6630c910de48650086766115010bd19132442f66110931d754f43d06f6618c220cf95232086fa6010820b798f540879c4310230db54821c436d5214843f354b300c33d548c821b7580438c27e64150109f18154487773254420cf150414c33f4354243b7192324cb3d5450a31de10d500875d6454e429f19150c867f6454c209f98c51482dd6394941dd587540823f6550c439f994314439f6050c43d754d320873d5490821dbd4a524435f5454c20bdd855210e7e6508520de192500875f5390140bd1855210e7e6550e20af98a43d0bb742d0110ed95331086766114c10ddd52544437751947429f98650d0af661d4b43d7cc9518cb5e5490f30dd4c9518c3d553cc910d754f4290af16010d10b758e42c433f5495310dd94641883ad5448421f91854210af56194143bb588434827d6595031cf94f4290bb554cc421e754d401027d65d0d109f189548c27d6510c30d758253086f960d5231cf185548caf76150a20bd191204436e5250040bd19443442fb6048620eb951210873f54545309f590530877553944209f98b
  | 45 => 0x315020ebd4942d033e6414c219f58653482f662d5310bd58732c43b86050940cfd83544c2fa608c4109f98053c87db6050d30f9d4b204429c6350040b758c50d067e650c420b758c40cc35e63d5330d7d4e534833d54d06109fd97218c27e63150319f59620042f66510510b758c400435d53d0c21bb597328caf5610c020fcd8121442f565cc721fc15220442f665d0d10e710d42ccb5f5410f32af592514c27f6154e40dd945419027c6355110fc50120443cc4354830d758c54042f9608c410bd584548c2f66214d10ddd0d518c37551cc020bd584200427f6590d10d798153086df6550c439f592508c73d6414132eb50b41c827c60548419fd95318827c6550521cf54b41906f56190040bb98b5190ef6630c110be983540867d6590841dd99151103f151d0240fcd8352442f96010f40b758c5190b3e5450a21d7d8953102f46590b109d587538827d658c831d794f320c23e6414e10f598c40c42f56550f10f594f31c87766114e20ddd4852442f66008510cfd51408c27c63544409f594438427d6394042bd583434435f6354f219f59252086f561d4a43dd549100425f6355110d7153324c35f62d4d408f992544c36f5354840bd986400c27e6510e209f58a50d0ef76408510bd597318c6f66190e41af990524427d6494c21fc48620443773154321bb988400827d63d51109f596430c6f5618c910dd985500c67e65d0910f558732cc73e5490832fc886500875e5350c209f995424c6ed62106219f98a530437560d4532d754d320427f6550841bd58e54442bd6494b30bd586400427c6054c21bb18132c82bf6454131dd149510c27e6394910cf952518cb6c5288540cf950510c27e6550930be98042842bd64d4830cfd89540c23e6414a10be18132103d5324c710b758343ccaee6214143be18143c83766154041dd950514caf6648c710f5d0f514caf56110320bd58640cc37651880209f58a544875e53cc4219fd96438863d64d4c20db54921842f66210510dd946211035f5394e219f99641882bd64149109fd9432842f86050e40ded9510043f03188110d79895390aec6254d10bdd85434c6f46154132dd54f310867c6454632cf94f4210adc6350430bb98830c82dd6390b20bb98b51d0f7963940219f98b54042ed620c110f994a510c37651c8410bd98f21442dd6310930d7d4f314873d54d4c219f9865090add6390a40cfd86548cbb55494430db14a42506dc6354940d7d91530827e650c620db94a400c27d6194d10dd984548875c5310e209f19532d037b41940219fd9641cc2f7614ca41bd58e52442ee62105209f191530436e5250a10d754c53086f56310110cf552400c27d6494431d718a531027e61948439f19743442f6640c510dd544518cb5f5394f20bdd9632442ef624c521b758f414c73f6550b419f5964244
  | 46 => 0x20b998840443776548710b798c52c427e6510b10fc58352c42f66114042dd952524433e5410230cf550518caed620c4219f994418827e6394840af992324ca7e6550c10af58043d0af4640c421cfd9154c427561d4c20bdd8554c836e6454830f698332cc33c54905209fd91510835c63553329fd9641c827d6550a30be582311027d6494830ed10d424433954940219f98754482f6640c110f5547308c27d6294730ddd85544835e53c8421dd144215027c6454730ddd475050b3c54d02209f98454483756014532af191319027f6590a31b718d408827e6314121cfd85548caf66190910e750c438cb744354640dd9845050ff12008110cf553500867f6054910dd98151903cd5354840ed992324433e540c0209f592500c6be64d4f20b758f54c427c6454031f5d0e43c433c54885309f58854042f5610c210bd19121c43f34188110be181425033f54d0b20ce95250087b940101109f594434433d5490f31dd587548836e6214910ddd0c514cbb46155021cfd8b544c377539464097d95320caee6295131be580325027d65d0e20d758f548c37852881109e980540cabe648c8329f597438867e6510c21bdd91324437565d07109d99440443ae648c920d754d3108775514c6309f996438873d64948329fd8151d0e7d6394642d794c41102f46150b10be580310c2f465d0110bd19432443754254430be18121482fa6010b40bb58b510c3795014032bb98b540c2f661108419d9845050ef4614c310af59321d03ac4350920d7101531037960d4c21f514e32442dd638c0309f58e540867d6094a31b7997324c6f662905109fd89534435d6194c20cfd82548cbb661d0b419f583540c67d63151219d984504ca7d65cca10d758c544c3f25190040f958840443e74214542dd54440082bf644c220bd18141442fb6050a20db54a300c27f6254630d754c53906ed6210220dd54c5150af56114342db14b21442f660901109fd96420c67f650c620d754e430875d62d4d409f594430437b4154021bd996214436f52949439fd9153087f34090110d798c53c427f6510030fccc130c427d65d09319f59443086dd63949409f98052443db508c1309f583544c6f66010b10d794e41086fa60d0f409f586544c2f96014632bd98643c879e54cca32af59643d0bb45450110d754f31c837b5094243cf952508ca7e650c930ddd52518c23e6415030ddd53100436e54509209f18152d07b74290b109f58a53482de6090d30cfd8d540835d65cc6319f994410c2f56184010cf950508ca7d6550830bb988408427c6354a40ed95141106f4644c110dd59441c879e53d0f40f5d85324c67e64944219fd94400835c530c910bc980424439c5450f30db588548827d658c821af990218c2de63c87309fd96430c3d74394430dd1825188376510c730dd14b10042de6
  | 47 => 0x98c31c873e5450721ed10e511035d6194e42d718a5390b3d6355021fc482104427d6510d20dd9865090a7c6254e41dd987530839e54d0c309f583540ca7d6215231bd58a43c42bd64d4732cf990548833f6455020d714f434427f6054f21de8ca500877651cc440bd18542c833d5490f20dd59641c427c6550120bdd85425075d5314d41d754c31102ee620c120af590304827d6548640de540509067c65d0a10fc58e204435e53544209f582518cb766494430bdd95210873e54d4c20bd18542903395454021db986521027d6095321db54f208827d65cc8419fd85544c3f14388110bd584404837754d07109f58c548837863540219f59732443f251cc230dd95241442de63081109f18153c875d5390c10be9805110af6610c910dd544310833e5494420d794c43c879c54d0d32cf951438434e5354840f954b20c42f663d4b109f580548ca7d65d0420f5d8d310c6bf6550842dd946410c2f6618c510dd192510c27f65d06309fd9530082bf61504419f98f514835f534c120f98c832c43f33194021cfd9154c87746550910dd549510c37551486409f18d5110af56194142bdd85420c35e5314021ddd51510c33e5494c21dd98752c436d6354840cd553410879d4310e42b7d9543cc3756394640e750f5010f3e54d0a31be58032083bb6050d40b7d9132cc25e63150309f596214c37753c4210fc181414427c65d0e10cf153408c2dd628c130fc509204435d5310c409fd81548877a60d52209fd9621d02f565c4210cf9535008775510c640cfd91548c2f560d0641b7983324c2bd640c320b758a314c67d654c8409f987540427d6294341f914b204427e65107309fd8d52442de61ccb31d714e314839d4310d10bd185324c77943940219fd8d54482ee6214430bd58341c877443544209fd8954c427e6194e20de50d500867e65d0540e754f40102f46548110dd95321443f1404c110bd98e43442ee62152109f992520827f6155220dd0ca519027d60948319f58754c827c6454231bd192104436e52d00409f99641cc3f16014910fc100304435f6054e429f196424436e5210b319f5964310af763c8310bd9845090a7f6254430dd947310c33d6155232db54842d07e9528c030ddd8e519027f658cb10cf550548835c534c941cf98554086f56190c31cf5095010a7e6588730f550d304427d6295210d754e20083e62048110cfd95548cbb554d0721d354e52103b74010110cf953418427d654c640edd8542506f960cc610af59232443b543504419fd9532906f66514d10bd993310873e5488430fcd91204427f6054c41dd4c5500c6f66548110b758f50086fa608c440cf94d4310fd75354d10cf553420427e6510431d7151320cb5c5454c21cf551438433e54504209f997325067c6255210bd19540442ed6214c41cf552510c2df63501
  | 48 => 0x443745294630f9d49204436d54948309f988540c2be6408420dd94430082f76050d109f58c540427e6510941bdd9153442f76590b10e750d40cc2f66308310de909500877665d05109f9845250f3d65d0a429f98b534433f54d0230cfd8d54086de63d4642af992324c7756254620bd58243442bd6408420bed81314c2bd64949319f98854cc76e5394840cf95140c433e6414e20bd19331c43f35090110d754f321027561d5332ddd47504cb3e544c820cf153424876d5214b41cf18b544c33f5450621db988548ca7e61d4c20dd4ca51903f33154021b5d8d40c433d5454c20e794c4350a7f654ca10eb50b414827d63d4b10db588548867c62540439f194430837651c8440ded81534827e6590531e7952530837551144429f593504c73f54509219f59742c43745148520cf95141cc6b564d4f10bd18552cc3f15148020dd946210c3e92154021e7990430c35d53104219f196424c35c534c510cf153314c37551106309f195438427c6550d32f390d320cb7763145429f59631082f66214f10f594e511033e5490e32ed50b414432c4354840af990215027e60d4d41cfd8e548cb7453c85109f19543042f96184010bd58b43c42ee62d0f20eb952520c2f664951109f59532d037651c8430ed50c43c439f5350f40ddd4b108427e65d0420e794e43902f4604c9109f99432106df63501308fd91534437a60d5021b598c52442ec624c320cfd52540cade6314720db549400c27d6414c10dbd8952c433d5310f42cf950320835e5388440fcd0140c42f9600ca10dbd8953482dd638c930cf191524433f54953309fd95430c6fa6008510f510d518c2dd6390030d794e32082f7654c310de549100427f65d07209f18152cc67f6590431bd98e544435c6194e42af592328c374510c520bd984540cb5d63d5231cf552428cb775194620dd94c524426c62551109f984540ca7f6354221bc582534433c54d0f30fc88550086ef644c9209fd9542083775108540bdd93314427d61d4d429f58e52043766294630db54b320c7e92194021bd9865010b745414b10d754d211027e63944109f980544cb765150630bd986300c2ed62951319fd8553c833f63d5130ded4e50086f56288510b798e42483766114142db548520c2f660d0f10d794e42082f56110931bb181324835d5314f40cf55253086ed6290621be98332882fb604cb40dd195214437453d4542be98032cc27d60d5331bd58840c427e650ca10b758e42482f46150d10dd14e524427f6548540dd54a518c37551d0030cfd50434427e62d4d41ce95150087f163481109f98c5150afa6090730af59021502f6620c110bdd8132c436e62d5320dd58752842fa6090410ddd4c310867e6094a419fd96400c27e6510d309798c520435f53cc110d754c538827e6514910ed50d404433e54d0320f5
  | 49 => 0xf665cc110dd4ca518c27c65d0d21dd15252c42f56190910cf153214c37451d0520ddd4e51083e73214532dd10a510427c6590f20d758c528437643546309f180534427e650c9219d997314439e4350930bb98840c427f6550520dd54a519036d5250830af59231903eb6248110d7951434c36e52d4430cf951438c3785288210af991325027e61d4d40dd14921c437261540219f98753042f56494910db54a328c73d54d4430af590218427d64d4b10e7d51324c3746155310dd90e51902be6408610ad59030c427d6015221cf186540c36e528c820f998821c437b5354021dd10a518835d54d0c30bb58b531035d6315220bd98f54442f463481109fd9151c83743294630be58053086f46050b109f596400427d6510620db94a510c27f6355210af99050c876d528ca10bed8b10442f5600cb109f98254c873e54904309f18d5190b5d53cca20bb18941083f254d4110cf551420867f650c820dd18251102dc6350531be181434c36f5210910b558e42c427e6014931dd95141c427d6015121cf950410c37a538c030b998830c427f65cc720dd54451102f1600c910d7d954310ef76150932be195204426e62d53319fd8d52d06de63d0a31ded4a100427661152209f983540c2f761508329fd95420caf4614c841d7d4c43442fa6008630be980540875d530c210e7d91300c27e658c510de98252843776454630db54b42d073e54d4420dd109518827d6510c32d714e435073e6255232db94b42cc76d6295132dd14831c42bd6490941d718a53087f232881109fd855390b776550b10d7149324c77551d04209f997211027d65c8440d798653102f960d0e30dd59251883b454d0110b758e424c37552d41109f19153886f76148310db949300c3b54210b10af580431033d544c030de98052842f664105109fd9521082dd63d50209f18553c839e5410d329f994544873e54cc430ddd4e53c42be640c940fc90a20442756115020b758e410c37743946409f98a52442f56295310b798f54082d66390b10bd587521027e6315221bd587548c2f56110130d7d8d53c835f5410d32cf952410c7da5390040dd945410836f528c9319f59443c836d5290a10db94a200433e5490010bdd9542442ed620c0209f98e50886ed62d4743ddd4852c42f6628c710bb98a4390a7f6548640db94a420827d658c7409fd81544833f6355232d794e30082f86050510bd58f40c427e60944329f98a54cc3af6450b20cf580544c27c6454630b718132cc2be64143329f98f52442f661d4e40de582524433c5490530b798e424c37a60d5020fcd01204439d4310e30dbd4a424c67f6550f21ed953424435c53cc920f694e200827c6154343db58a534875e530c010d7d4f31886f46590d109f597430875e5350e20bd98742cc67c6454720de8c9500876f6254910fcd432
  | 50 => 0xd0b319f99453482bd640c9419f996210c35e6254c409d185534836f5454830dbd4a21502f6644c510cf14942502f561141439f983540c7745354620dd4ca51082f76154940fc14f50443d653944209f98f52502df6250d308f99053086b56408510ed90d511035d6394b41db1494250776534c710edd46415077442d4532d754e210867f6354a419f99252cc35e6314a10db54b32cc27e650c020bb58853103772154221dd54c31c427d658c020d794d400835c52cc930e7d52434c2f564cc5109f98753087ae54c8020f34cb30c827e6114810ddd4b100427c6054e419d594310873f6455130ddd8d51902be6414432d754c300835d5314d40f594f324437661d48109f996438833c5390140d710c504caf56510310db191520c3766494420d794f31102ee6214243bd987304439d5410f32bd58430c435c6550d30d754f31c87e76248710dd0ca510827c654ca41bd185424839d4310d409fd89544427e6494d209f59531486f664d4f109fd9521102f46510f10f6983438c27c6510520cfd4e4350ade6310d30db548524433f5490330d714f30482de62d0f329fd8554486ed6210030be98042c82bc6454e209fd9541103703154021d754f511035d53d0440ee10e40103ea524c0309fd81528c67d658c8209f993538433d5454232cf95142c427661d4e20ab59232c83775294b10b758f52d067f654c110dd50d519033e54c84309f594329067e6294f419fd8d544c67d6315020edd0e434433e54d4632dd50d51082f56090910f954920c433e54d0c20af99231103655208710d7d9543cc27c6454f20bd592434425e6394b419f990540875d534ca40bd98743c436d52ccb419f586528c35d5314c109f98254cc67d6294740bd58e204433d64d4f21dd55041c867c6510c21af99050cc7d6304c1109f98e548437452cc531ddd95411077561d5331d7151324c67d6595021d7985531036e52ccb319fd81548cb755114620bd99121086fa6090c30ee551300c377654c9109fd95324435d5314f21bb58e204827e6508110f5cc930c433e54508219f996434c2bd648c940dd98454082ec624c521bdd8530c43ce53c8421bb58b40c835e54cc931db548528c77b5094021de580514827f65d0b109f997324836d5250440cf55220082ed620c210d794d511037464145328f99052042bf644c030d7d4f438827d6414910be597108427e6294630f9149204433d5410010edd0940c42dc6350030c714d435027d6155010cfd53414427d6510a319f993520435e5494c20bd58332c425d6594c21fc98341442f6608c5109f98e544867c6510a10d7d8153086f464c8710dd945319027c6590c10dd951518c33e65d0940cf588544c2bd6408630eed0b40502dd63152209f592538867e6294d10bd58720c436e52508409f986528c2fb6050830f94cb20442
  | 51 => 0xdd996404427d6550d21cf55140c43f35048110dd54451ccaf564c8110dd59421c433f544c930dd94d518833f5450531af191211027f6355130bb5885010e7c6154843dd94921c427f6550441de949204433f6550040bb988424833e5490f21f998b31c87d7320c910cf596431033d5450a329f594314827d6315021d714c325025d63d5321bbd8d42c82be64949309f98b535036e538c920af592534867e658cb409f194434827d6588440e750e5010f5e53c8440d7952304c2f561d0f41bd58740c43755294440bd591204427d6394640bd59352442fa6094543edd51414437462546309f99443c437a6014c10dd90f5150b5c5450d30b798c530827e6014941ddd0951882fa60cc830d714c525036d52d0030af98e4250bd532cc710dd944210433f540c930fc98251882ee6214c41e794c431035e5350c309f18853482f5650cb10ed10d519027e6415032f5cc030442fa60085409f582548c75d534ca109fd8550d0f5d5394420bed8143442f661d5020ee500408427e65d0d20e795043ccb775194420dd909519027e6494420fc182214437632546409f594420826d6295131fa98232c837552c87109f99631883ad54cca32e710f32903f2600c710d755343ccaf565107219f18d518827d6550720cf55142442b66414910cfd52548ca7c6254c10ddd8e518c3f160cc510d714d318873c6395021fc582544427d6550130a7191300c2ed6290c32b758f41cc79d4314443dd94631882f663c8110af99021d02f463883109f592528c27f6154a30af58a405031e53d0a42dd59710843766014532de58052c427e650cb10de94e50086f66195132d794e320caee6210320cf982540c27b6548020cfd52544867d6394a40af58b4310e7e60d4c20d799253082ec624c120f98c921086bf6454121bd987204439d4310c209f18d509075e6194c20bd18930442e46254d10fad4920442be6410d40db94a401027e64944109f988544c35e6314d21be58043483775194640fc8c2204427f658c640dd14e51883755188630ed909424427c65505319fd94420c27e61940329f59743c43b543d0110e714f435039e6410d32af59021d036c5210910b95883044376518c410cf59052843e64248421fa94a200833f6455221dd14f2188776520c710dbd4a525033c6255021cf95131082f66194032c7d50438c3af6450920bb588510c2f664d49109d9865090af66550110cf95243082b66408510f5ccb31086f96010630dd14b41c42bd648c820ee153304c33f5450530ad590524435d5350420dd58550c875e5390440db985520c3e8604c920cf153418867c6154242dd94b10042f662d0d10dd54631883b643d4542af992321065e63152209f58c5150af6644c310d794d320427e6414910cf150514c27f658c620b75834350f712154021bb98b434833c54
  | 52 => 0x275000400100140091a1c00a013815901140050010136000143d00ac000000c00103e401300106e801a00040050008000004f00c8001000c00000340390150001003808300140ba00cc00a005801101f8016001c08c008c3d0003c02000bc003000405c19a001500cc070001001a00240010000000000000301100330004000000009214ac000001400d00a400d0014002179c00300341810650001009000e000005e0070000000c00a000400022d016b00000010b4400100000090018002009c006000400001ac00306f84ac003000100000010000000002c000003c02800046c80000013001d1dc0000006002000000b414402440a1014820000180da00380170038000003c0160018002007c00502ac015000001f011402e0060000003110b000036b09ec59b00000070040008000ceb406b40730018009091400c001c40800140000020001000c5270005237003b5d5390e40bd19320c43774394420d794f30c82f56314910be58021502d563d5310d714d325027c6550921af191514c3763254420bdd9332c437b654c030ddcc9518827e6014c219f58953082f7614c821db94b320c6fa60084209f19543c827d6494832d798c53083d4614c8329f997215027f64546209fd94200426e6215031cf95340c427d61141429f18553d027d6194f20d714c3148376514c6309f58b53c42f66388310d354b300c2f663d0910de540500c63f6454e20ddd85544877653946209f595414c75f6354c20cf95243cc6be640cb409f98f540caee62d5331bdd8c214435d5314242cf952411075e538c220bdd855050af6620c9109f595438867d650c7409f595404427d65087409f99431d02f46150930dbd4b424435e538cb218f99252cc6be60d0c43db549321039d43d0330f310d32c827f654c410bdd85328c73e6295021f618d40102f86050540dd14f21c426d6215210af592328435d538c840d754d32443e76254d10afd894210af964900409fd9732d039d4310e108f59353c87e76150b20ddd0a510423e64948329f98e544835c5354540dcd05500875e6315010f958830c42f76150e41bd58430c82f56190d109fd95424cb3d54d0e30fa549401037a53540219f997414c33c54d0b21bd982414435c5310d20dd909510835d5390840ed10e404425e63d5310ddd0a518836e6215230bd987320c67f65484309f18d54087756510710be181328c23d6414b10cf989540877551900309f59741c82ef6250721d715332cc37b6054d10bd586404427e6394d21fc58031c427e65d0941bd98442c86ee62d4430fa54a20842ee620c920d7953328ca7e60145429f995328439d4310d429f59432d075c6354910cfd8e54087766194342cf152524c27f6354b109fd85540835e6514d40b718d50507792154021f64c5300c2bf6250d40bd98032442f6621091
  | 53 => 0x100020048003001000700000e70014019009c024001c03a00040120028009000000a0000016002804100dc0161e68020004c0000abc1c200100a306a400a001c00b13040090004005000c0f4000000a0000006007005f00042df00040000004012002802200582e900040040b6c055000c001020408900f00310024000128c1a5091800400140030000162000403b000800514200a503c8016001c00200001f20000012000c019000c00444dc01700280000090004003800e0000f8200b40310000000002402a0da8bc6000828f00e80000ecc0261ee02420010000000002800040b800e84f40300003002400f0008002000800c015c0200084000011814a00140060008000002c007001c036000801c0104012004c003001000b000000000fc1e3001400100000003bf4003018c040001c00a00780050028002000000140e80500038011002000d00d0022003000b014808000082970204007000001c000806200000fe0a2c0050000002027008d003c00000000000100000039c000060c005000000400080010000004001800a0024151014080900a400100480040034026000000300500000c7400200480660208067007c25800000010004013008493804d001e0000000000c017016020700140880038000003419a001003000100071e4402024f800b001408900000090004028001858f004c00300000560004003003401500000090004005002400c00200051f540120280048000005600000040190001001c029017c0000014009003c00302900dc0034016043c01803d400600780000008003004c001005c00000041230000008004c043000004200100080000000000402a2a640000008000001000106ec030001000300a4067034004d00ec001000802602b801009e8077008c006000001100f40000008005004454500580a8003800900640060258024001400a018c00200080020b9001e00a003601100000034028002400200000010000021009000000b4004008002300140050000001042800200100080000038001801400600050000005001c00800900470018007000c081001c012000000000d80060024001000004800dc000003800d00540030000001009000b01ac00205c000b0014000003001c0c580350028017010800500ec0490008000160c04e000803000180100000002008001400c8011001c0510018042020c000021804700b40010000008000000301680240000004005800a002c011000005803a00000008002000401c008800100080190964092000400c00000004f501c3001c00101c8009007c1cc122402f2c5c0330000004000000000e8013000000000680030000060032c00b000c012000003408dc001002c00f00002f74f3c0040030000001c00100c8088001800000dc0043200191000801801483040044
  | 54 => 0x80150140047008400000fc02d00d000000ac0b700242e200bc00000d00031744000005c02c000092100380001c94026000401d0038032000000e0320000000400e00042c13b980010000000000000f0008021000806b00dc025000000f00381e7000400401d400000000040128008000c000043c00d006c00a00000190000327020400c013401a3c940e500600000074203013c03301d0007002001d0008e610024006001000000a40600124118000000e0274024000400d00040171b188ff011c005001000100200020138002001000b0034005011c044057800a000c020000c00023e8002007400200000090db82cb001ca84041800001400000d6403e04140390040ed4130003a0fc0085001404e00bc00000f801a0000020000000f00000f6001c02000000030120072001c02800c803f0000004001c007006804a00240b500700650038029003800900640810000002000806800380000008555004403a000400a008400000000050018078000000b004000a007405502e401701d0017000400a00b80ba01cc0102b240000050000003c00600713330000068007c01000800160a9400003a000600380050000069004000204640af001800a0000009005c005003c00300a00160120015001c15900300020000088000d1490074000002c00e0034000000c0740014000005000100381060038000005c5e700141320078026001800500540000000011004012803a000000000310070315004c00924fc018007c01d002c01000a0003000000b0ab4031004c00a00880a100500350000003053c01b00640070018003000002c001000226f400100e00000e940020044008007c070000400600000ba005c47a000000f01ec1e43b98002004402c0070009001407a00040000004deb02cc003004800300d80072b200bc000400c000000a000c003004c00800040000000b2700c0019034000329340000ef407f1b84002004019f00000120be80090008000002801b0088002008c0150004014003800700280600914000002401001d00170000005042407900080150014001009c0080024000003820d00481470000002091007b00b8049008806d0000032000431500180060024037000402d008c000023c006004c0ae00d0001026802801340000034004001c07c02c000000a8000001402800100670038008000406400280310028002000001c000003d0974045001000400200bf006c008003c13a000000000d80000000048000003d0008002000c00403881460040007001802200ec001000401f013001100800000230016001c04f004412e063800500c41cb00380000004033008c001001c00b002c185001800400980011f9436d052c004012c0130068e5f00240030030001004c0070014da300b018e0118a2b0384000080001c00780000014015
  | 55 => 0x4000829e093001a000800400040000000000001000201a007f0050003004d34a002000334b4161000c0000050047000c004058405d016003b00000010010013000003b0000012002c0000014000001c06400000020018012013c1b800400002a1049601d4005003400000a801a030c019002c01400000000110000000829705e013d000005a069005300ac00d026c00200a4002001c201000c001001000f000133808c0033008800200083370010004000002a004000a00082b9000002200041db000805e009000b21f004c000004900601100004000023891700400ea003000a00801c900a8005001406c000000002880020048005001400b0000001001c02400000170050030009c0000024002006c0f9002405701b80050000010001800401dc000011001300000000120038000800a0014112036400c000c0890028133001c02300001780000a35000000400c0017008c07b002802400000041b94008001000e000002400280a201dc00000080210038003000000600180020048020000406a00140350df400303800720000039003000000082771c58043000026e000c0210304000000c00000000421ca800000000000144032000000e0000039001c01a0000000000000f04e115a003400202cc00d005c2f401300380000009000413e010800b13a001d003c00200840070f5c02300ac003008800103b8000000800001f800f004400800c072701180000004389001c08c00000180048000003001700440030028002001400002bc01e063c29a000004e002839900d800000e0009041802a002c0130494078000c00507640100014009002001900e8000000000915a4000000c07800d40220000000002c0100014034004000d001c000000408b008800102bc01300240010028012027800200a0022077c0010014008000000d000404000180040008001008801701f00a402101100034018000402a000000200401600008013210c000011800c006c0120ef401700e000c007000802fc007043c0eb0000082004801e00140e4014402d00c4001003000000a4013005c91500f0011000000f06e801e0f4c003000800000c000000700500064027002401002b400101a0007000806f0134020011c44e0010035005000b004000300000123e301090008021000000000f40090000002005811e000005b001809b03d800001940c204ec05f015002f1400045000c0920008010000000508fc00000180030000000078c055000001a0000023005800f0010ae500000040018000004800500d8022012007e004400600240660000001003001f0004000000003d0014033001400600200040010e07064c0a1005c05a00104700008001007800400c8004000002703902cf001c030081806807f4000004800000000020094000001400c008c1da00a400f001
  | 56 => 0xd0000000000b002000100000000010000004000000440000020113013014300200010034e96001000b07509690000007000404900dc00b000c02000280280008008005c00005c400800102f100300050994001002803600080080014000000000c002c010016825d0084098000000000180320098039018800000400770328005007c005002800300ac01000c400b00480010024001002c002045401b00cce7800f0014004c00e00001880004009065800000180000004002115806e009002b000005900ec0040000153001c00c00200000004000003c0230084000000000e00380a3000c0010010000009407e00a0001000402d000c0000018000006c02c02981a7001400300080010368000005800000200250000076001001f412800c0080007000c004000003204e560a06780060038016008400b000000a00a40000008001002c032087400002b4023023c0040074002001407f0208111164c0280018100002800400000210d8800f02a809a180c00500180000000000011c034001c0480028004000800c00040000f2800000fc001012c0cb0048046002800301c000a00c008a00104c4004401500980184acc009002000f03c801407b40430094007000006911f4013028805c001400a0004005021c0012f84163000c000000000000000200004c45002400100e474c015c0000008023000001501580d10038027000001d000000208f4078000066f00040780000001002c02000140650028008005c008000000000e4000009800903480320050018008c004007000200d0000013002300100010000001000407a018000a032401b0044009010800000380db007c001009003e00cc0150070032000400a000801e002c086029c2890014280000401b000400702c0000000c057007003a000c00d0040003000c0000064918000003a00200060004004000800b001400a00840070000000000000000040010070000001002600000010004000010c0550018167038801c011c3790008000000c01100a4002007c00f4ad4000001c006000800900201090000007000800943cc30500a80170110002000004d00c80020040007012804e014004400300010028000012400d00f000c000000100000010064072000805401d001b03d404a001c000000401c000406200000010004012000c0040000381001000e004c01407b00b40008056033c20115d800a005c00001c00150008022000400c034c009025c000325002b003c00700500040000008000002c0c2c01800dc02a1b1c033000801b026c520000800a135800d000c338002c1140000018003007e00200130000925002000a009c035005400f0328160028400f0020000009c0270004001008000e049006d00343fe01a0013000806301a400000040050358016001800c00000350004007006002
  | 57 => 0x100541e200f40b2000400b007400200640190018069040c0410aec004020806a001c31b0000001000004300484ed000000200ac02c00bc01c00842a6000c0190010002029401b0000008025800b000c00e00315560118000001401400100080674010002400d00004e700300160378000065401000480090014019005000400c00050020000000000000040f900000473ae40070004046000401d000c113002400001d40160158001000000000c010d0008000000000f0664006084c01e187404d005c0384ac80050020001004400002d400300280170118000000000c0004193006c04801580000004000004c1c20018048036803900cc00100740190000035001c00400082a4001001c01a400f51b400512b800d0004019000c01e0000016095c0030004000001400f00f4002007027f0000002002c01800000380000003000000000a400b0040cc400800750000009009808b1ccc038008883f001c234011c001000000a00000000000004282c00c2a300040000011002c003001841a000400300c000502d000500000000058000006883b000c0730218000000c0000030018002800401000000000000494c005000400900240050024028002c05c005800502940020228000004c007000400100580000124034003c02c0034000001800400000fa0788066000c010002002802f400e01bc00101d017c008000100480020020000004c01e05e0004000011100000000894044001c231001800b0324004035c0000048073008800000e000c014000900000060034000000000b003003a00280010af801e000000007ac002000800004c007c00000020040000008c000000823f001c005000400000000010000028002408b0a8008b00900020008000004401c002806f001402e0000012004899d001402301640004b0c00a00000000264009000800202ac00f002403803b4038001809a01640000010001000c004013416f0004000018c00600ec00c01a800200041260010023019000000840030010015004c00d000401e0000000000c008105c0041f58006023c03b000094104180000014008001c016024c0210018000016c01100c800600000000000043016c01d00001f50058082000408b059404d022002d00000050064000004c14900080360074000001800700200210f100110118019000800134ec00a009c001008c0aa006400104c800404e01c600000310060005003c00d005402b004c00100980000058053000c00000240030000042023c00100d401400144600004588009c00000200210000000000001b000402303ec000000800d00640000004000001c00200b80010058000000d0e000c02b22ff4005006801500500060010155004409e18940120004009000001448f800800100000004000064c00800080110000001000801901
  | 58 => 0x1c000005402546300070020013006455c0004155003816b00c4073003800600100000324001000403d0028000030c00201d800401101f60058148000000f007c259010801100040260038000011006102f40130038049003c006000c07000d405e0018008000410b11d8016216823d00dc00801b00ab001004e009c0000e5400c034c4fe0020045005800b0024043005c0230000001000000200ec00102000000184000003c00902d8008017000a0068003001401c000004600b8031006000c03f400000fc014008cbc900c4000008c1fa01603ce004c01500840020000000008000c000801b0000172000001800e0015002800100f40810030001000c0310e400010054004003801200000840000000010c03a0038002054c001001c003000112f011056911dc002002000f0164007073d4ca00c004b28cc90901780260000000000c01000b803f004400b1430001003807000dc011000800007540f31744166012c2250078002000807e03ac1600000009002c3a70080002028c04b0104002000801c00ac00b038802c000000c02000be097c1b2022c0000010ec606f000200900e3086c01200000010058000000002700d4003002800100e0006001c00400000bd00641e700c40010031201000001300014b7008802a0000005003400c000c04d005c000001c34100ec069005c0070064044000c00200340010000027068800f002c003000800a040c0012fc0005008c0210010000007c02400d8024007001b00040000010089008400b004002d0168077001801b01280040024015000400606080000004020003801d0050001002000025ac01700c8004001000800a8001000c4bf0000007174400d00dc00c069400100100060004022001402c38840010174000018c0000000010000010d0014006001c0010008000045c019000801300180050014001192400202c405a0c7000000bc15a00740080010000010c00004b000000181290098001013403a000c0130000091006001100000230000b18008007e034802f247802434cc008002400300040152530000005841c001000202280030000000001400a125c00300dc04a000805d0004000006418e35bc028000040600380a3000801900080000000047000c0040000210001c00101a40010ab400c0000007028400b00040130014fcc0004e8b00000000078006000401f0000001000408a003c00f330407900080030000068000000b008c071007400100000020000dcb0000194008813d0000002000426a000c02a00140160038000002068800280060a54001108000000000000000048004403900201c000200d7007c1290004007013800500140050030001009c00500e0013043414100000000010002000000800b800000140010008005000c005001803d008c1c200a511a086c01901e80
  | 59 => 0xd000000300e0003004800d001c0000048018007c09909900000300001028400700540240000001000000a000002800580140000029042400300c401200bc01906f8000002c1dc000c003034000c024877a000800100000000000000037921510f80000078001003c02b001800e001409202f80ba01a4002002c004311004500a478400000000030a764730019000401c04780010000006003000d005808e000800000600001384008010000f01d8006010d57d0
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8853574149510c31b322c229221a318d42501208e8eab088690d7170d445050aaab98a9884210fdd95414420c3ca831a818846f7654852042ab38cc0a9881179cc6454021ec6eaa12408876152546300c22f3b4a699221535cf54480208eaeda986390f1471550434cb3930ac02a0434d5c46055232cccc4b08a90854d72182531031aaa0c2a10631d5d852c4010ae4e021aa2206946350d40442d838286a022165dc56250c439e4e032662884b67498b31c426b398c810e21745c0614cb30cd6caa92802053671181548cb593224010221749ce4288110d1cc9a946499598735004044278b88c0a12419658e6015020d4ac4a00808865563584548c30f2a2c628841559cf54544208eaeb30c801847a701855210f2bb2ca6908431e5c265cca41c74c9300a610c777654852c42f0b90a890221479d743cc940c3ec629a84a063554984520c279b82ca19221acd9040cc1108f4e032c8610c3e7498b514c2f1390a890221179cc6015110aaae7b20a2a1474764c9519030ea9ac021e85d1dcd5214910ae2e0192a21063554185420830f322a7196831ddc56295230cd2a4b0062186a464189534423b38cc029287271d94354043acae42a2a2185727119250086ab39ea3288415cdc12154021b1ae7b2284214d673190204428fba2c0a9c85e450f40cc110c38a9b1a809865553d85320863cb80c2a9087175db4314132caac6288a0a167251580418821f3aec6a128199d95514802096ae932a608865565947308c2793acc0212211d5c660150328bceca9a80206d163580524426ab9ccaa0221471d1534c9108ece232e860857271d8e500873832ca8902219358e5290830c9ca6b1060085377158d548cab9baa65102219358e6215232c3ca931c841849d73d9542d028f3a4c4a98814d9d36394620c3ec621aa52062e64548520c32b31cc22a0618e1936054d20cb4c6b00a810c7571997321023ab8ecba1e416c9d021c41108eee2b2a85985e2754c920442d83a2a690221c31cd5454830a9ce4304a610e6552984400c32631aa4a0081781c954d4110bc4eaa12408859a70d4c43902d8ba0a490221179cf6508010d62c6a0080884b57418c2044236b90cb2182187553635043087aec21ca0204f270189434423b38cc12988574dcd5288110e2aa9a1ca2184757695321442a7390c0a98810fdda5408430a98e6a90a4885b2740c120442b2b94a210c615cdc532540218deeca90a5a05e172d05204423abacc220061875954310c20ab2e610aa010c747558743442d9bb280202211d9c660952328dcec2a2a4184b57498b30c42b2b8ea5290815c9c24254640c3ca9318421063664144504caaab98a5288818d9925108640ec0ea992408847a70194320423b3b6a688021475d443d0830caca6b0c601043d74194314823b38ccaa1021875915314e20
  | 1 => 0x300c31ab24c229c41359ce6550110a3ce6304a810c7970195420c73832ca6902218b59152d44308baeb31c841043f76550540870fb9ccba1a814e5d06294021cccc4a88801865453586405029cba0c6a80439359553d0a42d28c8992618847475586424423ab8ec4a86879ad96525004087ae9b2c650867165947409030faa0c6a02213c5c26590b10a3ae7312a810e666294430882b83aa8510221471cd6155030ab2e62a4a010fc0538c92044332b10c4a8c618d5916114e20e9264192a010f194310d5008637390ca21c215c9c03254640c5ec8a92622055970151530863a388ca992218b951620c02087ae830aa41849c735974090335312c02a065531c9534cb10c68eab20438863554185420c30eb24a628043955cc654cb1087ae9b2e639063454185424832bb1ca2a0041531c9534ca41c6ea930c609845d7399542c4317322c529a433c5c365d0910c5ac9290400863464545319023abb4a7188639c54560087208ece3b22a1995677158e5210333312c22a0411d1d5618c9108baeb322601845f7358154042cc382872808787991530c020c3ac8a9c6410ce672d93314432731aa5a88818d1955450910aace62a4a31061e6454c530823ab8ccb19081555cc6014542c72a9300621870d5454f21086b8b8643a82431d9c66094b43c38c929a60106355418542c423abb0a420a21c354e52d0040acee4a9ea08847571993504cb1caa6c0a1841785c86388110d8e86b10618847575193310872b31ac3aa0411d9c66015232caca7308a22069464d4d534434a2a4c72122187991631502087ce8302a610c5e73195410823b3b6a6a88410fdd954140218baed29880104757159420043a8a9aa3100418d59251084408bae7b2c831057170d05500874bb20c6a922147dc95310c4087eeab1e85a061d6498c52442aab88a9990654e5d23254021c9cc6a90a2204f170d9543442c73a6c6992411d9c76254243cceca30a659043e76d51524c338b2ac310421879916314810dc6c5b02a8886e16214b504428fbaa8621843175cf65d091087ce9b2c648871a5454d4010370292c0192210f9d26294c10c9ca6b148610c7575d85321030e322a6908819598d6115020a3ae92988610d3674189518c3873a086a90613c5c262d4d10caaa7308801068c644c930c8327b1aa490861635ca5410d329cced20a4210e585398032502b338ea529081555cc5454620ad4e431aa010f5153546401022ebb0a610a818b5536250e3287ce9b2c64084e9721814384279386c610a211ddc5654ca4096ee8b1ea48847471595321028f39ec8aa643ca55321540218ece3328841864f63189534431c2a0c099261275c86050c43c3ac9318a6084e6721902044333314c2298210fdd1650c910c9cc7290801861e5498e420834ab1887a16214b9d030548309e2e132a65
  | 2 => 0x62a84639c5456014632a74e9a9aa010c7671995424c31bb20a2a82651b5d662100309e2e03206588475719964388364992c0196418e5926014c20c9ecb29a401061e6494e320ca3bbaac2204418795163908308bcedaa2601847a709875250e79b82c829a21999956210110aace7302a3204ce7614d32c832aa9ec2a104395d8f6155120a72e0308a89869464cc9304424f3b686a0061179ce6215120ad4e521aa010c3e74988534838b2a2a7288413c5da5348110ca8c6a8a831845d73988544830f2a4c6200412b5d262cc520c6ca930ea61047776546400832ab1ca629621359cc6510b10ccac4a88801045d7398b5050738b80c2a9681b158e6210110bc4ea2924088634755902144358326c0a9a219c9c660150219e4e1314628865563984548c31aaa4c2180415c5d73154021a6ce9194a2104f3764c0304428f3a040a984117dd95314e40aaae7214a2206956458c52c423ab80c2a9087475d062d4d408eaed28840086666254440882aab98a598a219558d6115210cb2a6b04622064f63949400c23bbb2a618e212d9d06308510caac7288811051d7498c53487172a2c420021875954310e108eaed28c600864d6358854883d13128020221749cc408811096ce932260886695298021102d8ba043102219c945600c620acae2304a418475719805250e2eb98ca2122187d5263085309ace731680886b24318143442e9398a5102211d1d56448110aace6314a2085557318a519021e3b4a898041b458d4010110c6cc9308a608476751923044354b12802042187190534c120c3ecaa1887106a643588404432ab2aa6208438d59161d4c20d8cc731081886d16388020442b3390c128c611ddd951100209e2e032c65886946454d30c423b38cca21c411d5c660d5232e8cc6a90a48847571996420c2b838286a8c81471cd5450a20b64e831c408852e72d91540c25bbb2802022199989510c020d4ac9900418846f76548521032ab1ca610a21471cd6095021ccaa4b0c80206d0634c120442b2b90a610e219614e6008540d28c929a6188572708c9518c38baa08728c610fdd16508530e2a8621ea29965563946410c2b83aa64902219354d620c210ab4e1a9ca720e55731855210e1fbaac8180415c1c542540218eaea30a851853574d4d5108278b80c2a908717dd95314e1087cec2a281104757694620042b2b88c0a9081665c26150c43b60e8a96a08859473500404421fbb2a829061e81914248110cb2c7306a810c3d74d943008392290c2a12831bdd95214a439ace7b2c858874553545200823bbb2a228c858bd536254530d2eeca18878855970152530861fbb2a82a441ac995401011087cec2a2a4986a464d49524438b2a0c2a98431edc16550f21cacc728842084b47458e2044370992c0192219598d6115331ad0e0b1aa42063764945
  | 3 => 0x9251084209ceec900408856572d46510c3383288290221555c46054c20aaee6a96a08847576944408c33332cc4182219594e611442095ae8302649073154985500863dbb2a0280878d5526114430ca8a730c80a0571708c5500c6b2b94a210c818b5516210220c9cc6a90a42047676151518822fbb2a629e83179cc6014910a6ce3304a8185567118253082ad398a8a80434d1d15354620b30e8980608866562984548870eb22c629021559c66054e428ecea30a8499571720c550086e8b9c8510221b2589300c1108e8ec994a32061d6510d424cb8631aa4a0081661cd4010210cd6a4b004298761720c550087e021a64902210f9d06114910ae4e7a0aa010c6f72595319022ebb4a721043479d85350d40c3cec2a6649843d75d91321023a3b264a88819358e5208410acae3302a4204777559132443c921c80982218d5506150a32c98ca99262906d063d81524430eaa2c62a0219954b615083087eecaa0a91945e7399542c42aab88c1298418b596648cb20ad6ea90ca010e7161980540cb2729ac521c85535cb5394c40cc8c4a8a831045f735925008398aa2a290041175cf6590a10a74e1b22a918e695258342102b938084a88410fdd56408430ca8a630a64a067051580215030e2a2c521a610f5db548c930c3ac9318a7085e17210520442b83a062a80433c5c061508408dae532e622061d6454c211024eba0c0996611d9c66550c20ce6caa8a601862c5458840cc332b2ac4206215cdd921540219e4e032062885e17290d2044279bb28710221b194d6210421caaa630a642045e7694d400821ebb08728685535d743548308e8e2b14a91847771592528c23bb8acaa14619358d5214810c3acb32086185377550940c421e3a2ca1922147dd165cc2308eaeb30c811072542108514cb38b0aa028087a350e62144439ace7b26408851d76d50438c3a329ca4a888117dd95314f10c38a9b12879865653d85420872cb1ac0296211d9c663d4142c68c8a8a601876242485500871aaa4c3180413cdc16510910d2ac9318408863554d85320c272b96cba1e21c3d4d42109408bae7b28432046d72194300431caa4c120861479d36354c21c6ee2b24a598e4e6354a410c26b3b486982219c9c660d52318ece232e861058d74d8d320cb0f324a719641559ce42d4542a58e8a90a48845d73189509068fbaa8621885559cc6294640a3ae8310a6a05e27210d20443a8a9e62a80439558d5110020c3cc8a98a21052d7590e5210333290c2990614b5d35294830ae2e030ea0a14b674181324431aaa4c22a0419694d600c8208bce632c85885e37255120442ab38ea9298410f5db5410e20c5cc8a96a21845c7359520442b2b88c0a90619614d60905408bce7316a2a067171980540ca9ab88c12a0612d5d3658c910cacc6a8842204f27598032442b8b86
  | 4 => 0xa2e031a80886365418542ccab938884a8043471d15350e10c9cc7296a2206956498c214428fbaa8621e214d1c55415120ce2e032a858861f5498e424c30f324c629021591d54248110c38ecaa2601867251580218c32729ac418441559cf64d4542a5aeb2a240104f276d41304426ab98c810621595ca5108410caac728842184747158f5050b16322a4990815c9da5144010cd2c4a80a018c6d72d9741cc23cb80ca21e43ac9916008510c3ec9b1aa4885b17010f424430e32c86a12619c9c46055132b2ee4a18868851d7494c430ca783b2a8902218b55162150108ece232a840861d6458c5244279384c5a1a21479ce52d0b40c6aa9b0a8410d347550b414430f3b0a8a1e61c355343548308ece332a64a045e73994410872aa9ec2a10416cdd130481109aae7b26418852e72d5342cc73830ec0aa2659594f6150840a5cebb1284a0e376590d42c438b38ea821c619c1943148110d62c832240885367414d5108272b96c998a213cdc96094d10c3ca8b1c84105347158d54086adb9ac8a8043c310d524ca40ab4e1aa2a610e3654185428c6ab38cc12984387d954310c21c3ca9318a21063964580530870f2a0c6a06419c9856014c21da664b00648865663584548828e3a2a6a18432d5d265ccb10cd2e4302a89967251582311021f3b0a8a04615c1c143546308ece332c87104b6741944244338a8cc010c811d5c46590e20e8ac6a90a48864f65549300c237390ca218411b5cb65cc74087ce9314a7084777654451103713b48490221995895110230dc2c5a80808853671d8f544c23abacc3204614d9c46095030aace7214a2084f171983428823b38cc12908739dd952149108baebb1a841846e72181540c7162a2c5a0a43acd096010910c5ec9b12a68866552986401023a3aac3a1221359ce65d0b10c3cec2a2649851e7654d401026ab9ecba1621591c963546309ace7b20408846f765485110236b90caa1c214d9d36394630ce4a2b00421852e72981548ca9b3a0c128c6117dd953908219aae632c84886d063d41404421fbb2a82a265ac193304c1108f4ec29aa010e1d5498e400c29d3a6a1280439358f5208530cb2c6a80a0215e07254f504431a322a298441555cc52c4010d2ae632260887154310c5150a79384c520a21655d25310f10c5cc8b10a818d717294510042783b260902218715063502208d8e4b2a808855571d8b5350353322c4208438bd91524c840c3ce6b2c862043e74189518c25aba6c7906214d5d363d4542c9ac7310a5085367118254086783b287a82212d9d26348510c3aa931c8598c9d74181324c30eaa4c610841711c5424c8328f2e132e8518e2f65951210862fb9acaa0c410f1d1654c620c98c729280204b47458d20c422ebb4a7190659518d5150230cb0e7b2a80206656218951902e8b98a5102218d9
  | 5 => 0x86365498620082d83828621a218e9916014c21c9ac6a90400855973191500878ab8ea821c61595c864145328f2ed2a480204787059543c8770b1680182211d5c3654c910ce2a2b06621853571d91540c2cc3828621e41359cc6488110caec7a8aa0a1572740c55008754a12c0216814d5d23294430ae6e0a0aa020d71708c9518c2373b6a8900418d5925414b108eceb30684884e67218c204421fbb2a82a241539cc61548308bcebb26649863b64181544cb4ab208618621d254d5250040c3aa8b00861865963983548c6e4b98a4902219518f5154142c3cec29a84a0558735405050a2eb98cba14219594c614c810c3ac8a98a21062c54189514c3172a2c42042127dd94314443c6ca830a641863554d85430874a3246098621179cf659081096ae9b1e4388666521854204386b2086a90611d1d56110910caaa6b0ea4204d573d93214423bbb2a820a218d591611491087aedaa0429847571594300431aaa4c3a9841871506350130e8aa728e401066565547208821f3a0ca194211d9d8524401096ce831c418861c5458f414c72b31cc22a4414d9c76455030c38a9b128698475711815290f0f2a6c6a0061395c86484110c6ac9308a0996c563480204422fbb2a629e438dd976150842cb0a6b00629066952583320c2e4b9c8490221a55926314b10c5ca8b10811065953580420834631aa4a00811ddd564c8310b4ae9196418855a7015153086aa39ac8a8c41279c36550c43c5aa8b148610e2d6454821042ab39c84a8881461c14354043c3aa9318421849f7654c4350b1b324a218441475ce5410f20a74e831aa010c7671195420c266b98c0a12411d5c46054e42c3cc8a98422051f7550c43c83e09966090221ac59160d4f10a6ae3b1ea89845f7654c53d031b322a2180413c5d84348110ae0e890aa010d397414e50086aa3aa6498a210f9d06254031ba6ec98060885d17094f324431baa0c2a9261f04cb3148110ae0e2b22a010e1f7654c43d0b38a8ec098c6139dc960cc421caaa73088410c7571197430832bb1ca2a0081599ca4314542c3eca31a802047671181540cb32b14a2180218d1965450910a9ae1a1aa41853a7018a548ca1f3a0cb99421471d543d01308beeda9842a05b37454920442ca3a260182211e1d56010d108eeeca88a3a064e63948511021eba4c529e21b89496014b10d2cc8b18428865453d8552502ab398c128c81999896114143e4aa4a8e80204777654821442aa39aa410a21591d5320c910c3cc8a9c6420752535462008317324a410861471cd54509109a8e6b26a4886376555121086b4b8086a906196d8c6055132c3ea831a809051d74d4e5308352b168020621a9951620c421d8ac4980608862d6494a3204369b1cc7a8221d494d2154021d4886b108088725549452008332b12c22a4611d9c465d0810d
  | 6 => 0x20865a3a2ca992219398d6214c10c9ac6a94821861f5498c404c23c3aac121221875516315020b62e831c408843f7654f401031b322a2288419c9d6600c910e2a8621ca2184f2768cb5044358326c0a9221599c830544308beeca98a61074552545300c364b126018421715ce4248110a3aeaa18879067061181544cb27a1ac4282871d5c660d5332c6ca830a6410598744c0308433332cc4202210f5d36508010ce2a3300431864d6394a420823b388ca21e4147dd95410c308beeca98a62143f76d50214c22fb9aca20a41879536350020acce3a94a521d4e7295132cc69b38ea92a6658bd91524c030acae4298a48851e75d8d435032aa9cc3a908187d974350030c9aa7314601055671d4e53d0b63b18c4aa221475d6544c030c38c9a9a608851c73550544430e2a4c790a611d5d4614ca30c9ac6a94840857270d905150b0fb22a6980411d9c66015132c6ca8b0ea6104b674d8c20c423b388caa184147dd54310c32a6ae3b1ca91947570d95310c61f3a6ca90a61471cd5450c21c38c6b12a81847571d895090e5b3a0ca192212d9d3658cb1087ae8312a018e5563944200432729ac428881175cc6054841a6ce3302a81863654986400426a3b286982210fdd56408420c68a9b0a8490f1454d85324c31b32cc8182211d9c46550a30a6ae9194a31863554986430869c382a82a2658755263908209cae53266210e1e6414f31502f13b48490221acd9264d41109ace7b26438866952982410c29b3a040a88411d5c56588010ae2e0192a218536741825188237390cba1c218795263d4420c6ac928842086546554d32c432731ac42a665565c36354c21ba6e6a04408854e75d0d324829ab88c42a261999496190040ccac5308a9185557198253102aab98a4a88814b5d06054830caac6b08a5086b164480204422f3aec899261475c36550c43c3aa8b18a9106954358043c42b9baa849022195196534cb10cceeab106210d367118a548ca9b3a465288819698d6014b10caca7b0a6410e2f65549401032731ac5aa6639598e5110010c3aa8b18a210636741855210f4a32287982216c5d24010110f46a92124088666629845050f4aa1ec2a9087535cf5294840bc2e9a92408851f7654c43d0a8f39ea92a621741cd404c1108ece332864086d15358053c4316b24c4298210f1d16548110a3ceb21e84986d3535804344326a9cc4298812e5d0604cb40a3ae7312a8106a94258042c823d3b0a4902211d5da51102208eaea30a851064d53d812008297396a8a16613cdc16550d108deeca90a5184b77458d20442ac382a9a1a658b1516210130a6ae829e2008715435445110e3b38cca990211edd9501404296ae9b18408857170144504cb1caa2c02a04317dda5310020aace6296a0886d25358053c43d0aa284902216c9d062d4110c72a9304820
  | 7 => 0xb902211d1c5654cb40c70a9300429851d73d915408672b96c8182219554d6110020a3ce929665985d07354a204423cb80ca218438b19542507208ece3300a6a16c46318954442d2392a8a1221995966210310c38c6302a81865463945400823a38aca21a412d9d363c83108deeca90a418c7471592520c29d3a6a128463559cc52c40108ecebb0a64887615258052c422e39ac0aa0219558e5108630c9cc7310a81043f76550540ca2fbb2a6108411d5c4650c94087aedaa0848851d741815308273394c898e212d9d363c87109ceeca1084884b574d97324433930ac1aa04387992530c0208f6e0b2a869045f7694e420861eba6ca10c61555cc52d4110a6ae9b1ca32063454586404c2573b0a8a1641a5990538c910aaae7b24a3204ae7614942d031ab2cc8106216c5d363d4110d4aa8b108210c3f76550548864fbb287a908795197434c910ba2e7b26a08846d7219443c4332b10a418e218e5516014632a68e2b10a89845d7654c211022f39eca10c819958851105209e4e0320648843e74194214c31b2a2c3204210fdd954151218bae63288210e6462d85534438aa188728c619c9456090640b62e818240886d363d815444386aa4a4980614d1d54250510e18e8a9aa42061d5418d40cc370a12c0212218d59551d02408f2e03288710e1c64d8d538823abb4a220061555ce4294410b64e919440885587054c5350a1f3b0a8a1e61591c96354640a9ce630aa4204d47359120c430eb24c6290214e9c261550308eeeca88a3a143c7458053486e83828621a21561cd64540218eae232a861065653984400823d380ca21263559cf5194742c6ccb32040884b57498d214430eb24a7190438b551620c0208ecea320608865b6554d4010332a92c229061559cc62546409e6eca9a408863664944211032ab1aa2200619998a6115030acce5aa4a2184e572d9643442b93a8c9102218718d53500408baed298421051e74d8d53c42ad39842a8043785c0614c920a3ce9a9ca7886b3545804344278b80c8188433c1d94348110c3ae6322a71063554986300c31bb2886a1621f0dcd3248110c6ac8a88422051e73d5342c8348b226018221acd0d6010d10acee2b22a41861c63981540c30fb2a86218218d5516115030aace6202a22047676d5151083172a2c4288618d5506150b32b66e8a9a408847775588310870f324c62984147dc95410c309e2e131486885c5731492044392aa4a5288619c5456014443aace62a2a3104e472594434423bbb2a2288651b9d8535484087eed2a464104b77650842c4333296c2a14214d5d35194420a9ae6296408851d74988535023b3a8c8102219954961100309e4e032040885977650c43c426ab9cc52a221715cc52cc910a38e0a9887a162e64548510c21f3b4a8a1221179cc6550810c9aa631262106c5325843
  | 8 => 0xe6115231a5ce4302a9196b070590304423dbb2a02846593d4f6254540c9cc6b10a9105d07050f30442973a0c32908159dd542c8310da0c7b02a8886946450d3044317324c42a061595cb5454430c98c7292801851e73181540866bb9ac890621879526314c20d32c6a00808845e73d944004334a92c010861569c24354043b28e8a9e648861d5498c40082ab388c0a9843551c56054c2196ce8320608873154d0650086ab398a588421685d23248110c6aa9308a11971553947401028f3b2a8980618799443d0a30c3cca29e84a043d74194214c2d9b82a8a12219354d628c421d62c93046488596748c8514cb0e2a2c620a619559653cc421a98e4a9e64884af7458e204823ab88ca2126187dd953d0040caea7b0a84a055571982530833938cc02a0633c1c1644c510f4285a0a408845e7614d32c86ad398c9280431ddc5654cb40d28e6b20608849f76550434cb1d2a2c020e21471d15314e20d3286b00a421d957414c434429b38ec8aa6654b5d0305483087ce832c658857172d055008759aa2c021221b498e2008110da2c6b0043884757199632902e4b9c84904211ddc1619513287ceb3246498475719805350a8e3a2a6a18418d5966410421aace7216a2996656218a51902d93a043102219a5496010440968e8b2a6088475719954388326b1cc42a421875526390830cacc7288422043d74d963204317aa2c4206619a9896015021a38eca1aa021d6672152518c316392c8292219558d61d50208bce7314a8085557318a518c2aab9c84a88811d5c26115032b32e1a9a87a05d3735922044353b20c4a9a21531d532cc120ce0cba924088665629444008333b28c2990659998961d5331c68c9a8aa09966662544408c24e3b287280871bdd95214940c6aa8b088108573760c5500862eb98cb214219614f60509408f0eab0064885d173085204430f2a2c6204611ddd94254430e88e6a90a4885e17210d2044333294c3200819698d60d5310e32a929a60187155454e510829aba6c628a65745cc40cc110a74e829ca010d1d741815390ab938c64a80434d1d15208510dc4c5a80808864d6314a424c733312a218441475d25310f208dae4300a8884b67418c20442f13b26490221d454e6194021bc6e498c408865553584530832d29ac0218814d5c660550309e6e0b2a848857273485500868eba040a9841599c85394440b1ae529886a155673d925188236392ca982219558d51102208ecec292a2186556594c41086ad39c84a80430f1d16588530aaae7aa2a210751538855008726b1ca521461179cf65485408bced2a2659861c64d4d308830f322c62a441551cd52c85109ace6328848847775588434423dbb2a0280839658d5014021f22c6a00808864d6354a400c3a22926598a631d1d5644cb10d28c7a1281886366555243c425aba0c
  | 9 => 0xccba1c60885367418a510822eb98caa14211d1d564485108f2e032c8610d1c73552408823d380ca19283355cc62841108baeda98871055671d92530876831a6110221175ce6295310c68a8b0c609865a53580211022ebacc721043535cc4054840c6ec928a611062e5458843ccb2ca9ac0108418b5915214831c3aa9318a21045e7319642042cd380a821c611d9d85450710f826419240886e0525804244353324c4182218bd965250040c68a930c80984d673d9742443162a4c4202614e9c35495231ba6e6aa2408847975181430823ab8ecba1a410f5da5414021a6ae9b1ea29945e7615143cc3d12a28490221789ca5348110a6ce8182a21851d759854310e2fb9ac12a0438b5925208210d66c9b02a6884797099543886b839a42a8043b4995300c110c3aa9318801846d72d9643c42d2392a82a22117dd95314d41a5ce830aa41861d5498e428ca8eba4c4a98436c5c24250910c9ec6a92821863a64583530871ab2ca3a0481559cc525464087ae9b28421854e721865390b1ab22a2288411b9c86054f41c5acb2a6651957271d8d50086aab9c85a8a854e5c054508329e4e131062884777158e52103862a6a4992615c5c042544209e6e0b2c848864e635885484326b1aa4294218755163908208ecebb20608866552185321071b322a8208433c9d6608c910b62e9192408862f645492110278b80c899221395c86150c21ae2e0288a0a152d72153408c30eb22a6180419a5896015031cb0a6b0062a04d57399542c433928ac118821551c56214d40e2aa8a9a4210e8c63949401032d31cc02a043591c96154331c3ac631ca810ce57299131442ac39ac9280439998961d5030ce4caa94408866662584540cab83aac6902210f5da540c020cace630aa421d71700c9519030f324a628841555c66054e42bc4e429a408871473551510c266b9cc5a02414d5c75495020a6ae2304a81066465d85324828ebae87a00619394e62144408eae1b2a8220cf275980434432d31ac029221a550d6114043c38c8a9a622055673d9251902f03ac84902211bdd95214430d4cc8b10618843d76950210c23bbb26528c61781c954881108eaeb308601065b6554d2008272b90c818a219358d5208430bc4ebb12408843f7655054cc273390c0a1e21c59525394420caca630a6520cb476551424422eb9ccb10881a5593300c31087eecaa0a610c6d72181540c61fbb2a828c65749cf64d4110ce2c3300a81061e6454f510829aba0c128c41d85ca6154021c9aa7b1287215b17095342442b8b9082a8043a550d6194043a3ce9a9ca610cd473595424421eba0cb19221659c66050c43cccc530ea81873154485500869ab8cc12a465b858a208411096ceda1a81885e373509204429b3a0a4a88611d5da52cc510ea0e2a9ca010e1f76550434ca2f398ca200219558
  | 10 => 0x57170d4c31086e839a81182219c98560d5231c3ac829e42a057170d87504cb4b324c610a218b59262d4f21e32a929ca010d707158d500878aa9887a8a858b991528c841ea26598aa010e3654986508cab0b9082a8043ac5c0644c110cacc728843186356495021442b3388a6a90816c1d15288110c3aa8b0087994b77655054442a6b96c829a81931893254730c6ecb2a24210c7b76540500c63b3b6a2a82658755263d4420c6ea830a64984ad7498b3048272b90c9182219594f61508208ece3304a7a146d7299431102ab38cc1298814b9d0615484096ae9316628847576946400431b2a2c2180418755163908309aaeda1860886e27058830442aaba886a8c61595ca6054640c6ca9b0a8410d727018e519031cb22a02806587dd95410c30b2ae33028621d4d73185521021eba0ca188432d5d06388310aace6314a21871a5454e50087872a2a790041539cb5394c409e2e33008710571710c950086363aac8992412d9d365cc9108dce4328860872654949510c2363aac421a41471cd6255030a70e8b1aa010d707150d50086d9b82a82a2219c5c560150328bae6328858843e74196324431b322c22a04163dc95310d4287eecaa0a11946f7654852902e839aa8902211edd5608841087ce832a62104b57418e10442b93a4c2a804395d8d51484308eaec2984288556739085150a79380c4a0a214d9c66055020ccccb904408852d74186520c31b322a2184411edd95014332ae2e198ea098e2d6454a320c2b2392a228a81a6d8c6050d40a6ce8292200846e72181531063ab8ccba18419554d611484087ae932e639063554d85320870eb24c629c4117dd56390030c98c7b12a48869563500404425aba6c610a211e5db5284010c6ec8a8a601069463d0d40c422ebb4a7188639594f614c840ce6cb28a802043d7695051082e2392a6996219598e510843087ce9b2c650851d731504344297390c0aa061179d85354540a3ae7b10a89851d74085530863bbaac3180219954a61148308bae7b28801052e74d4a52cc70e2a2c621261535c0524c931ac8e2b24a4184f17019031c8678b84cb996211d9db5454430caaa7b0a641064e635885384278b84c9a922155dc56454e42caec728a80085547154f31c82cd384c2a18873c5c2650cb108bae7b2a8290e9464545300c29b388c12a0411d9c46510e208baeca9c8410e1d6494c308434a32486982215c9c46394021c6ca9b0a851951c76551300c23ab88caa1c41479d26294c21c38c829a611064c6510d324833332e40102211d5c565900109e2e032a858873254985500861f3a6ca108212b5d2620c9208ecec29aa32075253cc5500863b38cca21821a59506350310f228621a40885397408550087a3a1aa5288612d9d06408110ce2caa8e611847471588544c23b38ccb19481ac193504c110ca
  | 11 => 0x442963aa84a0241875954310c3087ce8302a790e1d54580434ca2f3b0a8a98433c5c06150930cccc4b08a9185c672d0c514ca9aba040a884135dd95314f10d2ac7218808869664cca32c42f0ba6c490221a658d4010210c5aa931487906365458620082cb3a46499221c3153624c930a6ce9b1ea29965553586401029aba0a728841875916314a10ccaa5308a22051e749895308768b1ac0296214d5d36394620ccca430a6518ed16398021442e838264982213c9c6608c910a9ce5322a610de173d892044333296c299421879926314a108eaed29663884f27018f21443b0b9082a80431e5da51840108bce7b2e85884f171983324832d31aa0280438b1906254d10acae429e200845e7319440082d93a0a5a8221559c46054e42f20e0a18868847675d85424431cb24c029821359cc6590b10aaae7b20a2994f2760cb50442aab9c85a8a650f5d3658c4108bae7b2c82086727018552d03172a2c420843551cd52d4110c38e7b2a80206355458341086a7398c1290814d9c66095021c6ac8288a0995e1720c6500870ebb0a899261179cc6590a10aaaeba1aa2184f170d94324423ab88ca99081acd516095110aace6294a32043e74987524c2d8b8ec8a00819354c624c721d28c6a12808847b7654050c861f3a0ca90861179cc6054b418eae3304a621555739815188326b1cc429021c31d15394840a9ee6aa6411061d6494e32102ac382c4a98818d5526188020d60a8b04848853574189510c26ab9ec8102219658d60149108f4e032c64086956410f32c430faa2c72a2430f9d06054b31a6aeb21ca22056671182521025b3a0c7082211d9d6654c910a6ce3b16a89861d6454e3208316b10c42a2618d5d0615484387ae83286010479701895110e37390cb21c21385c86050d10caaa6b08610846f7654852842f0b88c0992419c5866015030878e8b04a610d947355342443713b46490221c91d15214910ca8caa9a64885657215052c4278b80c2990619954861508309e2e132c87886e162d4b504430fb22a6988811ddd95114730caec6a8a80205647254f314434b322c6106218715163d01308eaed28880086e352580324432aa9cc229841479cf5495320a5ce5aa4a998c3e7499732c430f2a2c7a14639a5496014831ab2e7212a010e1e5498e42c86b2392a290c613c9d46050d109e2e5b02a88855a70d52530869b3a4652882187150604c9309ceec990648847a7019443c8733292c3200613c9d842d4110c6ca8b088410e6952980310c29a3a2a590a211d5c361548438baed298a3215e27290d20443c821c8118221d158d5214b10ab4e02a4a610e2e6354b4010279388c0a1a21555cf4214532a3aeaa188790e4d654c83208786a1886a9061cc1c55494021b1ae4298872063564584538432b29ec2994211d9c46055132a3ce9b1aa790
  | 12 => 0x29421175cc6254440c3cc829a64a0476761455050b4ab268618221359ce62d07108eceb300848862d64548528c333290c2a14831d9d763c8510f44e9192408861f5418d40882b939cc2a80438b592528ca10caacab18818861e5418d400831d322c1a9e213c9c262d051087eecaa0a89858e721814310e1ebb0a810a618719354cc230caca630a842054e73d91520c23bbb2a228a412d5d26294d10ac8e4aa6a0886d3644c0304430fb24a698041479cf5495321a3ce7aa28590f3071951500863bbb2a2200615a9c04354830caca6b0ca12163665590204428fb9ac0aa4658e99160150218baeda9c84a04d7764c0304432b3288618221539cf52948409e0eca0240886377559021c42ab39c85288619354e6210421aaae62a220084757198254cca3b388c0a90878d592510c220cb4a7300a32145c73582540863abb4a3080215c9c06414532c3aa9b1a801067165947208832b31cc22a021175d95390840ccaa4b08a421eb06450120443a8a9e82a80439518e51500408daeb3148610dd073502204422eb9ccb9088135dd9320cb10c38c9b1aa68866762185534828f39ea8a1065a85894010110ce2c3a84a0a1c5f7558c21102a7394c0a9c85c395152cc0308bceca9a801061c5498e42442d339487a8a85999896114e10c5ac8a94622061f6418d524438caa2a7280434d5c76455020ca8a7b0a6490d6a72105500863ab88c8a80658d59554cc421ae2e0320a299732655004044386aa264190438d550614c820a6ce2310a89852d72990544c78621aa420061ac591608c9108e8e2b24a51856a70186520c30f2a0c6a00618b5926214c20d2ac821a658863565550410863abaec2a1461a3191324c120caccab18808863664944210421fba2c7a92210f5d065cca108e8ec994a2104d77359220c432b31ca210021475d05310e208b8e6b24a190c3f7655054cc61eba0cb196211d5c5658c010c6cc8b08a70847575d85420c2a6b90c0a988139dc96550110c38a8b1e8298666629444008279bb26310221475d06094c218eeeab08600864d53588531030fb20a8992618b95162100308dce4300a888566729492144317322c42a461471cd54151209ace732a858872674149214432aa98c2a10418ed94644c0309e6e4b0086884757694c5150b46b208699641879516310010c38c9aa260185e272cc12044370b148020221789c84248110c6aa8b0ea6105e272951204433928ac1108211d5d854c40108ece3306a919536748c951102f1ba26490221479d2524cb31bc6e4b1a40885717090550106b838eca88021565c35394c21c3aa831a42184f172181434422eb9eca10e811ddd5619003087aeb320601055671d925390bb03aa84902211bdd952149438ece332865206595398021103393acc119221559cc5494420838ecaa260187a14250520
  | 13 => 0x6548540ce4cab0042884f17019443c4338a8ac19084178dc15214910c5ac9290420851e7615143cc32da9ac010a81c55534354430caac6a88811851e74d4d43486f0b84a429221875516315210caac6a88421055673d46511028eba0a7984419558d5114442e8cc6a90a58847576944300425aba4c529e211e5da538c0308e2e030aa421e4e6354a400c21f3a0ca99021c3191524c030ccac4296a08856772591518832aa9cc320081c358c4354840a6ae8306a2a156571982520c33928ac018c81475cc5410d20da2c7a808088475719825390ab2b90a88802163dc95410d32c68c928a60104747158a539021f3a0ca1884387dd26590d30e1aa6a92802043e76551300828e3a2a799441475cc54502208f6eca80a0a0e9943580438821e3a2c0a98214e5c24314143c3aa8b1ea010c3e74d8d52c434ab1e80206211b1c9654c6408bae6328829043d7695232082aab9ea528881789d64248110ec2a4a8a80206556394c52442e8b808799221475cf549502187eecaa0a990c7776544300830fb22a699081d494e6194021c6ac8a88601063554185320c338b0ac029221d154d5294440e18a8a1264196a65458841086aab9c8428a858b9916214c10e2aa8a9e6210cae7598a4350a4e3a2cb984618d1965450b10a6ce8314a22061d6494c51083623126498e218e1516010530caacb3186210cf171181324832ab2ac610e2195d95514c030d4ac8900418862e5458840082f1384849022165dd54310f109ace7b2043884f2719804244333294c3200611d1c56294c408eeeca8c811064d6394820042c6b90a821c614e5d35094021c3aa9b1a801861d5458c4088333292c3180613c1d560109108deeab1480104f170988434423bb8acaa12211d5c66015232bc6e4a9a408871b7050d5010f1ab2ac810621a51506350110c38a83028798475711815210f58b1280202219594d6110020cacc7a88a0a15647550842442a239aa4292211b9d8534cb208bce6312a32066662984548c338b0aa028085711c95314d1087aeb32042105e07254e204432ca9ec0a1841f04c93048110ccac5308a81853474589518c23abaec999221399c863841109e0eca0260884e7725954344279b82c9992210f1d163940208beeca98a620c3e7615142c87c821880182218b19362549108eae232a652066952d8132102b2b90a6a8c81551cd549462087ae932c62104e67219030c422eb9ec8a96218d59654d0421ce2cab00438853574149518c316aa4c521843b898b500c1108b8e6b00a890c757518543086b9b8262a80634d5d05244010a3ae9b08a6a057270d92510c2a7390c1298811edd950143318bce7b2c820873154cc550086f0b90c9102213c5db400c110b62e1aa4a9885387458e500862f398c4a80831ddc563d41428beed29c841067365545200831b322c2
  | 14 => 0xe0314a72143d7695240103392a2c029621559c45454c20caca7308a42047a76d49100421fbb2a8288611d9c46510930a3ee8b02a610c5e7694d4388338b86ca99221871cd6414e209e6e0b28868861d6550c438832731aa4108611d9d85254640ba2e6324408871454986304c23cb84caa18439558e6114142acae429ca22063764545300c31b32ac8182215c5c04354620bc2e429a408857176105500869a3a2a5a82219614c6050940cd6cb292601847776544514ca8fb9ac0aa0433c9c262cc510c9ac7294840865453d854250237bb2a4290879598e5110030c5ac8a90410861e65153324c30f322a719641355cf6408510a58e4b0aa8107c273149204431a2a6c2a1263d4995300c110a6ae8304a318656639875408333312a2288618d9516190030ae6e0a9ea2a1790744c0304431b2a0c2a1063179cf65908208bce7b22a58853671d8e548ca3bbaac3200219cd456008540da0a6b0464886d26358052c4316324a4980619c9d660c8510c6cc8a88422071553547401030e324a698641875906454c20c9ac7a94a4a0c7a701944304297394a6a1683359cc6590910a74e1b22a810c5d76953324c71ab24a210861591c95415110d2ac621880884f1769522044317322c42a061175cc6590b1087aed2a0a218763754c9204429dba2c6a804399596620c310e2aa929ca21061e5458c408829b388c12a465d454d51480209e2e030a64a06976410e304431d2a4c010861875d8548c130c3aec29e84a043f769503008316aa6c4988419654e6014c218bce6312a22054e72951324c32b31ac2298419554e610c0208dce5b2e63a05357418951902b938084a8c61175d84394030d62c8200608861d5498c530831b32a80202210f5d2650c42096ee8b2a40884f37650040c423b3b0a4a8c613c5c262151109ace630285886556554c31086e9b82a629a2195d4f614c9408bce7328422061c6454d321032b32e60182219354d6214c41ce4c2b06a610cad72181435038aaa08728861b498d6008710ca8e2b18a58851c745815308717322c42a4214b9c86115130c3ee8b18a0a147671191500cb2bb2e86996212d5d0604c910c38a931864985567390a518c28e39aa8a1821699ca4350b108f6eca80a098e71701855210e2e3b4a6a0081659d54310d109e4e1310828864d6398b54c872ab1cc22a0414b5c24354840e6285a0aa010f5253885500869b3a6a5288610fdd9548c821acce429a200859073500404421eba6cb192219394e62d4440bc4ec292408862f5458a544c6aa39aa429221a5d5063551108eeeca88611046e721954304326a9cc4290815c1c53254021a68eaa16808861d5498c540871ab24c229821789c23248110acce429aa2205717010d510c25b3b0c898221479d06054c21e1ee4aa0869953574180514ca3a38acaa1661175cf
  | 15 => 0x5653185328870e2a0c0a1a618dd946150842ce4ea30286885577158a531023b388ca99081591c954d05108bae732e8588655535865090acc3828621a21c550c4354420c74c9300a4087507194d50086b9bb082a804317dd95314d20a6ce9196a29951f72550434cae8b808618221471d1530c220aaae7214a2184767119732042e9b9aa490221879516310210c9ac6a90a420c6f76548524c31c2a4c0212619654e6014642e4aa528a802062d54588510c21fbb2a8108419698d6015032ab2e02a264196c44358830c431bb22a2984413c9da5448110a6ce8294a31864d6398b540822eb98ca10a814e5d35394021a9cebb126498de2758c92044237bb2a429221749cc214811087ce832884884767119642042d83a2a7a82218e55260150218ece3b2c87904f376551204426ab98c0a12216c1c14250110e2aa928e601845d7694c5110333bb2a410e21591c95314d10dc6c5b02a68847475587324425abb4c8102214d5d052c42108bae632c848867365545401029aba46428a654d1c56055021ad4e418aa010e1d6494c300832cb1ac02a043175db530854087ce9b28431854e73d92520c21f3a6cb18c418759443d08308dce532c821861e64553300c21f3a6cb99621569cc6454021acae3aa2a41855673d5251082e2b9c85906211ddd56448110d28c9b1aa488667659452008237bb2a4296871d9c46510d20a6ae8314a3204f170193324423b3acc0192212d5da4310310c74a9300421047571194434830eb1ec02a2615a9c06154830da4c6b04848865b6594d2008278b80cb21621535cb54d0c308eaed2a6438845e73994400822eb98c0aa643639c843d0b32a3ae62a4871061c5458c404c31aaa2c228465b458d60d53108eeecaa0a8884b67498b30c42acb98c5280439598e51102308e8e2b2a87904f170d964344236bb4a510041a550d6114843c3cec2a4609857176cc5500862f39ecba0e411d9c46254043a6ee8a9ca3105367414d100429b388c0aa0411ddd5644cb109cae4328878843d74d9732c42b2b90a728c814e9d232540218eeec992a2185b17418b504426bbb2a629a218d9516190020e2a8621ca3107497010d520c32629ec4a8a81991976150920acce3aa2a41843e74d9531486cb39ea92a62187991538c821c6ac9288431867275980424429aba464a8841a5591300c310a70e0aa4869961f6554d40102ca3828621a21475cc609502087ee8b04a610c3e7695130082e339686992211b5c8654c4408bce630aa42071771550434ca3bbb26528881535c043548308eaeb3226488535748ca518823bbb2a2204614d9d640501108eee2b16a0a1e2c6590d42482b3388a729081559c66094c20cd2a4b00438872554484210822e39acaa0c41c395043548308f4e032a8610c7671996420c23ab88ca21e41b498e6090910ab2
  | 16 => 0x821e3a2ca90c614d5d35394420d8ac5980618861e64553308c21f3a4cb90861b0589300c11096ce832c658845d73d96420870faa0c6a0261179cf65c87408bae7314a80875153105500870e322a498061479ce6295030a9ae630ca42061d6314e405028ebaa86218430f5d2650c02087ce932e62106d26358354c432bb18c2aa2418e59260d4c21ab2e1a18a0a1fc173149204422eb9cc9a82431d5d4640cb109e2e031a848861f5458c40cc22eb9cca208413c5c0650cb10ac8e4a9ea0886a462509414423ab8ecb21e41695d23248310caecbb0a64196656294440042b3bb2a410e210fdd95415230d64c8b00a488659635835408678b80c4a1a21a559163083109e2e030a851866652986200423b38cca21461741c1434c110f84a6992408859674d4e53c422fbb2a6184412d5da640c1108f4e132e8610e3654d8532086a6baca690041cc9512154021c6ccb21c808846d72d944004386a1aa4290873cdc16548110c3aa831a8398d6571d4a520c32b29ac2190433cdd92008110c72a8b04841045c7359352442b8b80c628a858d9516110f318ece3326a09947776509518c22f39eca200418d1906154d20ca8c630aa8905697010d5210279bb287a8221c914b42d0510aa8e6b0aa190cb6749953044237390ca20a618e55160150318e8e2b2a841853a74085500868fbaa8621e43595c45454830e1886a96642065653d8532082cc3828621841555ce42946308daed2944210f0d5390d521032ca9ac1a1881279d2644c030caca730ca1214b774595304423b3b6a4a8c61599c85444010a6aeb21aa2205247454852442d8ba0a5a82219c9c56014c2196ce83142088654639454004332a92c0296215a1c964540218eaeda96200853a7418e500864ebb6a621c81879954310d21e34a929ca010e395458353086e939c84902218b55262150308eeeca88a31947676d49100428f398c0aa041879964390130ccac4290838866a52580320c32ba98c2a1281479d02154c21a38e0aa0879962e435885050e373b0a8a12418b55062507218eeec994a3206355458430082ab388c129881531d5324c12087ce9b28439863654586300c333294c228881875906494c219ace7322428860c64549300c21fbb2a820c439c9c06154843c58ca21a84906b264d403044279b82c8996219358d52144408beeab00861847675d9332c431b2a4c3200611b9c865d0c10c5ca9310801865a535802108386aa2a79004178dd23248110e2a86218a29964c535884348362b1e40106219c9c660d5021c3cc929ea21061d6414f3150236b96cb21a439518c51541428daed290a2185347458d518c2b938864a80438d9964310110ae6ea992408863664544510c31aaa2c22a041659d35354f108dcec29a64905b07458d204429ab88a8a1065355cc64087108f4ed28a20086
  | 17 => 0x8a21475d05310d20a6ce9302a31066552984510c23ab8ccb21841ca551524c0308e8e2b16a0a1c7b765405090a73390c9182219698e6014c218e8e2b24a4087315488550087a529aa4980611ddd93294410acae4202a2204b67498a534432b31cc2298419c5456008430da2c4980608845e7615132cc62ebb0a7212814b5d06094830e8ac6a90438870d5310d521021f3a0ca19221c95d052485108deeca90a4a0e4f6318954442b8b8442a8043659ce42d4542caac728880106966498c20c42aab9ec028a65475cc60550218eaebb0a651066552986300c21ebb4a828465991496110910aaeea9966210cd57398a54c4274382c8996410fdd5648c821a38e6b02a810c757694630882793b6a0a02211d5da51902209e4ec212408856a701855210352b24c418221175cc6015110aace62a620087265414b42442b3388c0a90611ddd95314d10ce4c2b00a818d567315310842b9baa43280439354e62d0f20c3eecaa2601874452d85324c6793b4a4902211b5c865d0c10cb0a730482a061d6494e3208333290c299021995896114e10e8aa728a401066962980530430fb2a8621861b498e6008510a6ee8b12a3184b774595324426abb4c610a216a5c04350920ba4e62924088474715885350386a9ca4a0081d494f4154021a6ae9302a3184f27694d20443932a2a52886159dc96454640f86c699240886356599030c421ebb4a810841a3192524c030aace3b1aa610535740c1510c316b26a519263d88c92154021e4c86a94a22057075509204426a39ac91022159dc56354840ae6e2a14a010d1e74d9532cc2793b06490221ac50d6010d10a68e8a90a48863654986400823b3acc1a1a21711c9534c910cc8c4a8a631065663584540c23a38ac52a0215cdc14354420c6ecb28a8020636545863008359326a0102218d1526110130a3aeb318862063b54181434c22fbb2a629821179cc60553218ecea32642886546354540102793acc12122187591530c010ccca8312a88851d7395043c425b3a4c690843ac192404c1109e0e0b1e848843f745953048317aa2c4202618e9916015032d64a8b00a98863654185428ca5bbb28621a21695d23248421a6ce9b18a29945f7694c21103a8a9862a8043391d93248421aaae7b16a2a161e74597430c2aa39ac4a8c811b9ca64d4131c6aa8b0c401057170c85508870eaa4c721641a598f42909108bce632a850861c73590504cb17aa0c4a8a61d85496008710cccc528860105e0764c92044237bb2a429683b418f4050110a68e8b12a220590744c030442e8b9c601822117dd95314e20b4ae829640884e57218e104423b3b0a8a0a21569cf5454021aaae6292a32063664987530823bb8ac42a661a9591620c310c68a9b0aa498555731835150b32b12c228287785cb63881108dce4300a6884767614d518
  | 18 => 0x15031c98c6312a88857170d0750506e0b98a4902219354d62d4440878e8b1ca010e3964980520423ab8ecb21a43a55916308710c5aa8b10801049f7650c5210f26b1ca4200618d9944310110cd2c4a80a021c3f76550420ca3b388c0a98859cd876055132ce2a2b0043104b5749883244272392caa1a211bdd5628c020e4aa9292a2186946414d304423c382caa1a431d9c66094e42d1a87310a021c7b7654050086f1b9283102210f5d365cc910c9cc6a94841857170d53410870eb20a618a8195d8d5150430ce4eb300408847b76540509071b3a0c2a96814b5c05250941b1ce7b2285905727018a518c273390c818a21551cd5454620b82e721240886b16458021c4278b84caa16219c59551c8220ba2e119264885677654852c4386aa086a90612b5c86050c438ece2328860849d7690c40cc2d8b808620221555cc5294640cd2c5300a818d3674981518c26ab98c9106210f5d2654cb10a3cebb22869855671981530871db2ca898061179cc65d0810aaae2304a62067251582318c32bb1ca2a00611d9d8545443087eecaa0a8086d1635824244279bb2a9102218755263d4021aace2302a61047a70194430821fbb2a82a0610f5d3654c5219aee6b2a80886c56358840c431c2a6c09926174dc1534c910ae4e0324a3105b0744c2204426ab9cc5a02219598d51144408eae332e841845d7318552103d0a1680902218b9916214e208eae332a64a046d72d96434432b298c2a1041875506350020ae4e0312a32065663584548423a3b26528861c554c4314542a6ce8314a2084cd7398b41c821f3a0c4a8463879d85450d30ba4e6202408861d5498e42086a6b98a5992211bdd95214b31c58e4b24a598d677550920c4272b96cb21e213c1c1644cb1087aedaa0819847675991324431ab2ca8208439594c614c8418ecea30284884f276d41204423bbb2a320061b458e6090910d28c728a802066565148424429c382a821a651ddd95114640c6ac8a88611065563544210c30e2a4c1992613c5c065ccb108e8e2b28879066752185324c22eb9cc52a221875516314021ccac5308a0a1c3c745953244368b1a4010221879916315010ce2c3300a61067151d81218822eb9cc5a8a81471cd5450c20b62e810a408849f7650f5010eb2b90a8a8c61275cc6050b408beed29c842043e76951300c3a2a9ca528881c394d52d0040c3acaaa6651963954980320828f39cc52a0411d5d66190020e2aa8a9c4210e695298021042373b6a6900411d9d763881108eae332e65205647258550d070ebb0a9992619398d62150108f4e132e6520d3671d8e54087e131260182216c1d1638811099ceda1a649066652185420c7a939862a80431ddd94214532a3ae62a087105e0754c92044279386c990a215a9cb43540218ece232e871062d6454a32843a2296659
  | 19 => 0xc992a2206e352580424421fbb2a8204411d9db5354640a38e8a9e64884f276085204421f3b0a8a8a610fdd9540c020caaca29886886d143580434432ca9cc0210812d5d06308310a38e6aa6851065953580411029aba6a528861395cb65d0d10e2ea621aa32061d5418d400c297390c12a0439c9c660d4c21e4aa8a8e4010699435805110ecb39ec9a8a85c5150614c9308eeeab1661884f17099742c433928ac120821479d643101309e4e1b1e42887244354a511025b3a4cb996219598d5108420c3cc9318a81054e72951324c71b2a4c3a90610f9d2650c4208ece23288610c5f7558c21082aab9ea4a88811d9d66090d108ecec2a2a31862f64189534432729ac4184211d1d94294410a3ce9b1aa61051d7414c4344236bb4a921085e490c40cc110c38a831a809065553986300826a39acaa0221999905248510a3ce9a9a6590cd57398b41c428e3a2a6a1c41745cc524811093aedaa0871847576d53100430f2a4c7210650f1d1654c1109aae7322438863654587520c34baa4c7212218318d5250040d1886b1080185717018552cc31caa4c0190619554e6194242a6ce829ca21065763945408c278b84ca21621395c8640c310d8cc6b10808845e73189509070f2a2c7a8043661c14310e108ece3304a89947671d97434829bba2c4a8c8187197434c940ba2e7212408846c7259443442b83aa43102214d5d23254430a6ce9194a2185d07359120442f1b92a9a82212e1c1644c9409cae4302878861d5418d40c42acb86a8a9843591d532c8110b2ce7212858852e7590d42c82e9b9ac890221871936354d20e8aa6a92a22047671996430834c218c0990814d1d16154321aace7b20a2a15957490c434421f3a0ca180418ed526008530caea630aa4a043e75990214c38b2a2a798843955966308710ae2e3212a010c9e7615143cc29b3a88628a85f0d4e324811087eecaa085904b77458e2044317322c42a02187d915348440a3ce729285a0e1c53983435029aba0c5288419514f614c9418eae2312a021d4d7314920443393acc12122139dc96510d109e2e1b2e64884767518f21443c9a1a8118221599d852485108eee2b2a648845d7398752502793aec0a1a21179cc65109108e8e2b14a60869463901404428e3a2a6a18218e1c164141329aae632885886366510e4044333296c2a1081c314f5250940ce4a2b00822062d64548210c2a6b90c229a818dd91514c440a3ce9a9a659076152885100421eba6ca108218dd516190130c9cc6a90801873254cc5500866b39ecb212219558d5108620c5ac8a90a2184777654451c830f320a719221599ca6054630c3acb29e85214f17690b504423bbb2a820e218715263d01309aeeca1886884f1701854288296392a8a1221c51d15394440a9ce4308a6a064d53588300823a3aac6902219a9896
  | 20 => 0xe73d97424421f3a0ca994218b95262148309a8e6b2884884797019543086373b0a8a16412d5d0650c9108eceb31a428846d721964384362392c6292214ddd15354620ccca5308801845d73996410831b322c22826535dcd65509108e8ec994a2207154310d518823b3aec9102214b1c95415110a5ce5b22a998e1e6494e320862f39ccba0e415c5c650880108eae232886104d67398a54442b8b8e86a8043b490d6010d1099ae43028621cd573197204428eb9ca821e43471d15390e20cb2e6302a89961d6494c2110326b1aa41088117dd95314f42b64e8294408863454d85424c2b33aec490a21d494d5148020acae4304a3184ad7098a4350a8f3ae86992819998a5110010e1ca8a9260184f37059130442b2392a820a219554e6114c408bcec2a2869843d76550210c23abb0a810a218d5516190020ae6e0aa6a29945d73d94211023d3b6a8a8043175d854cc930a3ce7aa4a810656539843008273396cba1a21271da53500409e2e5b0286885e272105204431b324a210861c31cd5494830da0a6b00648864e639885404326b1ca4288813c9d84348110aa8e6b22a21845c735954244334a92c0108819c5466008440a6ae2302a810656631445050a9d386a92a0438718d525004087eecaa4641853671d52540832a29ec2992815c9d33154021ca8c7b0aa48861e6354f401034a31a86a06218d5945410d10bc2e82924088559731515008738b80c2a9661a958940103108beeca98a21045e7614d525031bb26c2a9a41b89c86050d108eeeca12a2105387058d540823b3acc899621599c45494830a3ce7312a810c7776544510821f3a4c529e215c5c36314532acae5a8ca22043e74d94210c23aba8c2994813c5c660d0920a3ce92a2869851d7510c400c32ab2aa398461471d54310e2096ce9b1842884767118d5010ab4392c6a80438b9926214c209ace7b2e858843c76551424423abb4a790a214d5d23254620a3ae9314a6104f17018532cc2ab39ea52888117dd95410f32c38a8b1e859855973d525008717b2ca890041359cc64083108deeab10801854c73591520c23bbb2a82a6214d5d363944108f4e032e8610c3e76951438c32bb18c2a9a41591c95114530d60c8a0460885e1721065008673396c8182219a9496010840c3ac8a984210655635845050ab83a662a80431d9db5254430b4ce5218a2a16656298453042aab9ec9288211d5c765d0d2187ce8300a68852e7218154086b8b8084a8c612d5d06308710ce2c3300a50863664944300823d384ca21843595c85354440a3ae9312a61046c755884348732296c2a128317dd95314c408eaed28c601061e6498c5408716aa2c4200611d9d46388110e2a8621aa218536748ca518c32ab2ca618843561c15410d32ae4e1b24a31055573182519029bba2c4a8c418b55262900208eee
  | 21 => 0x32ab1aa228841879526314c21c3ac8a9c622045f76553300c23abb4a828a65c5d50435463087ae8312a21876142485500871aaa2c3200610f9d265084309cce5b2c868861d64d0c504ca3bb8acaa1a41785cb6488110a76e0b1aa9197175310e51902b339080a88811e9c265d0a31acce3a94a41843f7655054442b8b86c828a8593d9553484218eae2302a62151c7550d404c358b24c010a219358d52908308baeb318801051e73182540828ebacc4a1887559cf6494410ce2e2302a899655639875408386a9887290815c9c0435443087aed2a4641861d5498c500861ebb2a919043c39515348020a3ae829a611061e5458c400c38621aa4a10619698d6015031aace6300a2a143f7459431482aab88c529c851d5d7614c810a72e0314a91961d6414e325031b324c229021599d620481109b0e0b22659861d6510d321021f3a0ca100218799053c85408ece3300a81943d74181520c68eb98c22a2618e5516015032a6ee8b1aa3205e276509204429c382c4aa0610f5d66408430ccac530ca89965a639835408672b90ca21a2195194434c910aace7214a3106347159052c42aab88a899065995945248110e30a830264984e672d9331c421eba4ca18843ac59160149109aae7b2c848861f65191300c2b5baa42a80433c5c26510f10c9ac7290410855571d4e53102b3396a328c870fdd9548c820da2c7200808843e74d97324426b39cc5a06210f5d26294c10caecbb0a6598e1d5458e420861fba2ca90c613c9da3248110c72a930042104d573d9152c42e9398c9102211ddc564948308eceb3008688636549845108392a92a2a0081871526310d30ec6e490aa010cf37650620442973b0a4a12838b55162102308eeeab16818863a64980540865b3a4c598a21175d84394332acce42a4a21845f7654c211032aa9cc2288819594e618c020a38e8b0aa62043d74d94300423aba8c2a1061555cc6094620c3aa831a821870f4354b400c33332a4010221695d052d0910c6ea8b0c60984b57498b304423b3b0a2a8265785c35294b108dae432a860864c63549210c3c932260182214b9c8619523296ae832c658863754986404c31b2a6c2a1421559cc5254440c74a8b00a31947571982540ca6b398c810a218bd526210130caaa6b0e8610ce6721921044278b84c5a1a211b9ca65d0430aaae7a8ca21043e74197320430f3b0a6a1a81175cf6508010ba2e1298a68843e7418052442b2b90a810e21acd93504c110bc2e5322408855673d08514cab3396a8a8861559c45494c20c3aca21e642052e74d8d521023a3b28528c619cd846055132acae4304a32069a64580430c2aabae6598843475cc6095021e4cc8a90a48851e7498953082973a0c3290611d5c361551328ece332c85184f176cc62044279380c8182211b5cb65d0d218ecec29aa22045
  | 22 => 0x41a55926308310c6ecaa8a80205e172cc5204434a3226498221559cc5294440c3aa9b1a84185397414d500863abacc6908438795163100209aced21a618845d7399440082ab38ea729881b8dc36255110c5aa931080104f17018542d02363aac521a415c9c46454021d1cc7a9484a16357419542c4359322c1a9e2166dc16250c43ab4e7a84a120cb67418132c431aaa2c318041175da5314420dc0c5b02a88864d6394a4284267b9ac9102413c9d84388110ca8a630a84a051d741825390ab93a8c110a218b551628c020c9aa6b168610e946418d5244236bb4a42888199589510c020d62c9a80408845d73d9721d02aab8ec9a9a81555c46094e42c6aa930c80105367414e518838caa2a6a80439558d5108640e52a8a94601847571995424c31b324c22a061475d443508308b8e6b2a432045d73195211034a32664986211d9c660d5332c3aea31a802055573d525108339380c2a96610fdd9541513196ce8318438861e5498f50086793b64290221595c85408510d8e86b10608863a54583530871a32c84a12218b991528c44087ae832a62105727010d5188370b80c4a9a219654f604c840ccca6312a6885d173102204432b29ac2284858714c6050940ae0e0aa6a29961f7654c43102ab39c8428a651d5da53c8710c6ca9308a11966952980411023a3aac690a21555cc62544408daed29c64196956310f424423ab8cc12a4655a5cb4354021c3ecaa18861055573151510830f322a7a8043b158e62103108beeca98a710d2d72181540c28e39aa9a122159dc56494830e64a8a8c401043e74d943004278b86caa12211d1d5644c510c6ee2b20a488536719815408716aa2c42a061ac992608c9109cae43206210ccd7218143cc279bb26018621471cd54d0e209aae6324208861d5498c540830eaa4c6298434d5c66055232aace3b26a6a0671515802190386aa4a7900419c98660150329e4e1b20428861d6554f4290b0e29ac5a1a81cc9d04154021caca630a65886555318532c42b9b82a628a858b59252d4430e1aa8a9660184b674d8d52c4279bb28690221f018d3248110cb0a730062a06d3764c0304431a324a2980219c9d46548110e34e1aa0871847675982324431caa4c010861c555153d0421aaae6300a29962e54988300833932ea5102218e9916014b10c6ac8b08a61063664944218c21fba2c029a439598d6115032d4c86b1081885947350040c4316b22a5190812ddd94010310968e8b1c4188656654c0304432aa9cc2180214b5d06154830b66e8a96a088535719815408348b1a80202211ddd94294620c58caa1282905d373501204422f39ecb214218d1905154132a5ae5b18a89861c5458f424caca3aa8621a21e4d0f400c110c6aa8b086410e65625445110eb9380c4a8c61559ce42544208d8eab16869061e6590c404c
  | 23 => 0x10030c70a9306869843e7499532c438c29ec0a1281ac593500c110cacc6a88421853671981548cb32a94c2100213c5c065d0b10c68a8b08809861e5498c428cb4ab98c898621591c951486408f6eca80a1a15e2720c520442a6bae8729061555c76354c209e6e0b2e868866776548524432a32c6499221175cc65100108baed29c601869463545401031ab22a210841b85496014b1096ce9b2e6588565721835150b32b14a21844155dcd6454640c3ac631aa81047671997420432b31aa220041c39cc4354840aaae7b26a2a14b67498d21c429c3a2a0282652d5d365ccb10cacca21c60886e352d81524423bbaac22046155dc56214d40b66e8a9ea08861d641925308273bb240106216c9d363d4110e8886a94a218732549865008666392c221a655c5c35410421ae2eb102200875253105500863a3b264a8c618d99161d4c208ecea302868862d645885388326b1aa429481879526390a32c9ac6b10a91855671d4e530831b2a4c2200614e1c16355232c5cec29284a0e3464d85524423abaec9996210f1d5648c930e1ea629284a043d7498a534429b3a6a6a884117dd954cc23087ce8328629074743549510c21eba6c6a9621741cd52481109e0eab0464884d673197204423b388caa1821995886294630d8cc7310808847576946400823b38cc1a92874e9c343542438f4e032a8418d7170187504caaa3aa6598a21c5552514c030c3ccbaa4869854c725855390b0eb20c8a984317dd564ccb308ece232886104757198054cca2f39cca208418b99252d4430c3ac9a9ca690f0d4310d521022fbb2a629c850f5da5414830c6cc8b0ca690e3b65d91300c3a2a9ca4a88811bdc96550110c6acab2043886a564c8020442793acc190a219658d5014041c3ac631ca81058f7250e5210e2fbb2a628c8517dcd6494321cacc72888110656635845244352a12c2210431edd950143418bce7b2c83105e172995204428e3a2c1298431ddc56510f20c3ac8a98a610cd57319642c430f320a7992814b1c95450b1087ae932c421846d72997410c39321aa4a888199194614c920caaa730c401065953980500863b38ccaa1c411ddd9530c5108dce5b286008476719973210237396cba0e61551d532cc1108bae632c840843d76950530874bbb28621a21531c96054c21b34e029887204757694a210866b398c610a21d198d52087108eee2b14a8186547558c21443a8a9aa2a00811d1d942544309ace7b2641886646518542482a7396c829a811d1d562d0110a5ae5aa4a81862d6494a329032c29cc121a8193d8d5250030b92e021a64905b2748c920443a538086a9061359cf6454b108eee2b2a840861c65d91434c332a96c2990815cdc53294021c3aa931c841951e74949320cba929862a80438715163d093087aeb324641068d6410d324823abb4a220
  | 24 => 0xa14a010d667218251902ca3a26018621c51d15354440b1ae43028621e966458c21c432ab2ac610621551c55314d20d1a86b10a021ec93258032cc236b90ca200216c9d03088110c5aa831282105707054f5150aaa39ac8a8c81479ce6155030ec4ea292408843d76952320863a3b28528841479d85450d308ece2302a521ce57298f4108673baac420843171cd6494021c9ac7290422064f65949300c22ebacc6108414ddd16354630e328621ca010d2d74d4f200832ab1aa210c61785ca6348110e52e021aa4206705458052c4237bb2a429061cc1c5545402187ae9b2c6588636549844008335a92c010a81b1589300c310e62a930ca010e5463945400c21eba0ca19621a910d6210310cacc6a884310655639442190368992c0192210f9d85450b31caaa7b0a84206956498c21c423bbb2a228c615a9c86394021a74e8314a010dd17308710443992a442a80431d9d85254440d3286b0087a046d721943150338a8ac010c610f5d06548430aaae6312a3205e072551204429aba464a8c810f5d06054c21d64c8b0043885557390a51883a4a9aa520081d85c052485109aae732e8588672769451004398aa682a80430fdd854085308beeca98a6a054c73585520c2cbb928621e219a5895014041caccab1840884f370596324430e2a0c6a0221e450d404c110e28a6b0c80a061d6314f42502a6b90a619281879526390821b60e8a9c40886356555031086e8b8ec6980611d1c56550a30e2a8621aa3205707054c5150b4aa1cc3280871d5d6618c220a3ce7b22a98847671997430833928ac010c819a9496008440cccc4b08a81843d7418153c86b538086a908147dc94354043cb0a6b0042a0656531853210237b92caa1a21531c95314d10ccca5b0a841847675d922144386a9c8729081999896115321a5ae021aa42061e5458c418c71ab24c2290219554c614c820c3aa6b04862054d7318252102a6b98c0a90818d592518c4408ece332c64085557318a511036931a4010221871d16314142aaae3aa2a61056572981518c273b92ca98221175da5314242a9ce630ca4204e572d9331c429b3a0c4a88611edd95014143b64e810a40884f270190214429b3a0a5a82210f5d06508010c72a8b048218539748ca500871caa4c029843661c16250c43c3ac9a9842a06e352582524422fb9acb90a81559cc60d4542c3ca8b18a010d677258d518828e3a2a629a41879915410c30e32a8a9c401055573081510831aaa2c3180619c9c66015032aaae2302a62063554986400c23cb80cba18433c5da32d4110c6ca830a858867251580410421f3b4a8a0661b8588400c1109e2e0320648847571996428c317322a519061559cc62544409e4e330484885717190d500866b39ec8106211d9d66110d21968e8b1ea48843d74194328433332ac4182218b55262
  | 25 => 0x755844008333b2ec2a10853c5cb6054d108eeeca14a2186b2648802044316aa4c4188431d9c66510810c5ac8a9465184e67219443442b2b90a9884213c5c46050a20a3ce9a9ca6105b1748cb5044297394a6a168155dcd64546308bae73288210e2d54d89410830eb2ca9a18614d9c764550209c8eca124210d2d72151408c22fbb2a618c43951c5631491096ee8b1a41885d373553504430eb22a6184414e9d35394021e8aa528e6018567754cb20c432a298c2a92810f9d0658c810b48e4aa6848870c7494d521023c3aac021221391c56210f2193ceda1a811845d73195420432ca9ac02108195d4c614c9209ace6324418864d53d893108317b2aa8900415cdc14354640caaa6b08a1214f07650e204439221aa4a8881179cc6590910caac6b08a48861e6458c52c43a2a9a42108419958a5110230c6ac92a043885727018e518828ebae86a0061551c56454c218eeeca88a31047970194424c733314a218021471d54310d30d64c8b0464884d573d93204430fb28872006117dcd6015121acae5a9ca22063954582430c25aba6c6106216c5d05288110e1ae42a664984f270d9231442aab9c8428a65c959152149109ace7b20648861c6454d30c822eb9ecb21021599c854546308eae2b28800861d5418d420c32a31ca4a92214ddd163546208beeca98a690d7074885500863b3aec998a211b5c86510c10ac8e4a9862885d17094d32442a7390c129c851d5c665d0a30d4ac5a0080886655298452102cab9ca821e210fdd16548110e1ce429e84a065665cc230442cb39c8428a85b8dc36254d10cb2a7304620847676d455050b1ab2ac8186214d5d06314542acce3304a4184d573d9321c432b31aa2288416c1c143d0110acce429aa32064d6354b511023bbb2a2288878759053cc94087aecaa060104b574d8f2044392aa2a528861ca5525248020aace2302a62062d64d4a524c6adb9ac928043555cc52440108deeca90a498e3954980518ca9aba0c528c614d9c663550218eeeab1a408855970d52530863bbaac218041a5993538c9109e6e0b2e84885947454c534432a31ca2a04611ddd95190230e1ec8a9260186c56348020c43b099242a8043479d54310d10ccca5b0a642047575984400831bb24a2980419354e62d0c21ae2e1a0aa120e55639845408732b14a2200618b5916214c108dae431aa020d3674189511030e3b2a998061c554e5150040dc2e532a40884b47458d204423bb8aca99081395c8640c721e1aa9a1ca41855573909510822f39ccb90881c51c55454c21c3cc929c642046e72194300432731cc42a421875944350830a6ae030aa810d1e73989540832cb1cc02a04335dcd654811087ee8b02a60863654185420431ab26a210a81539cb5394f41c6ac9308a610556731825188279386c819221339d8524cb30ae0e2
  | 26 => 0xcbbb28621a210f5d265c8430d2ac8218608863664d44504ca1e3a2cb90a619398e6215030ea0e2a9aa010d59701885350333bb2a4296210f9d85450832c3ecaa1887085a974149204429a38ac6aa4651e9c0654c841c74c9306a610c75769524110679b82c7a92213c5c3648c9109e4e0326428847a70996430861eba6ca90a61179cc6054841a6ae829a200855773589518823abacc218441a5192304c11096ae932a658866652185421031bb22a29088155dc56254c40a58e4b02a810f155454c410871aaa2c328465875915314e10c9ca6b10601056770548524425aba6c790a21359cc650c910acce5302a3207155390e511030faa2c62026199948614c841c6aa9308a21065663586544865b3a0c710221555c76414d40cd2c5300a81864d535883004338b0aa0280651d1d93294410ab4e62a4a010d587050d5010e2f398ca908818d552610c8218e8eab0864885b37055342442d2ba46590221175d953100208eceb32a848847771595420c2d83a2a4902210f5d06014910c9aa6b10a22061e65d4f43502e2b9c8490621c550c4354630caaa730e8610d4d75909320caacb9ea1280439558d6115020ce4a2b04631043f7655042c872d31ac029843c350c4394840aceeca90a48864d635482084297396c62a2611d5d661102308eeeca88a2a147970195321078aa188728c819398d52084408ece33286420714539864050278b8cc021a41275da4310130c3ca8b1ea210731541055008696392c2aa465e450c43d41108bce6328829045f7654c539072b29ac3a9081559c76414d4087ce932c62105e2720c9204430eb288620061a59926314910aace7212a21843e74194300422fbb2a629a218b59262d4c2087ce832864085357418a510c32b31ac2294210f9db54545308eae3300a89961d6494c2108316aa4c5218658b592528c8409c8ec992408861e6454c530870f2a2c7214659c945600c410e32e02a2879843d749973108297396a8a10651ddd56188010c38a8b1842985e272d0d2044237bb2a4296219558e51100108beeca98a22051e73989540c32bb8ac729683871936354910d62c898060886376518542d02b238ac7290811d5d66448421a3ce9b1aa790e65625845484352326c4a9a210f1d56408530c3cc92984220639545803208332b10a418a213c5c0654cb10c3ec831aa88864e6454b300c28f3a0c1298411ddd56190220aace7a92a2204f17610f5044236b94c7a82831d9c765d0f208bcedaa2a610793744c03044359b26c0a92210f9d365cc720d3286b0086886c763d89544431a38ac929663879915308420e92a690aa010d35748c9518c28f39ec8aa0418b9915208430c5ec9292601852d72182540c3a8a9e6328043a519143cc31087eecaa0a81066452d85325066ab98c810221a390d62103308eae2302a899477
  | 27 => 0x6147dd95410f329e0e0b26648863874d95300c326b1aa521421ac5096010910c5acaa108410e5763545400825b3a0c6106211b5cb650c010ae4e0212a2205657114d521023b38ccb19081745cc62d411087ae8300a6886656254430882aab88a8a98411d9c665d0830ce2e032a65885597319250086aa3aa64192218edd3654c030acae4182a21847a701895110e373b6a6a90814d9c66095232e2aa929e8210cf27019032c42f03ac64902218dd5061509209ace632060885357414e5188359324c010a21479ce5250b40ce6cb28a401043d7498b514c31b324a318c811d5c663d41428b8eab1842a04d773593524421fbb2a82a621475cf5495020f2286b00868846e72d9743c4316aa4c4180411d9c46055232c5cc9290a2185357418a5104339a8ac010a61c555043544308f2ed294401047775586308829b3a6a328841551cd51145209e4ec21ea08866662584530821f3a6cb188218d153614c930c6ac8a88a21863554987520c316b20a5192831b9c86510010c3cc929c65a0c3e74d9420042c7b9286a9087359cf64c8510e2aa8a986210d5573d92518832ab1cc22a0219c9c560150328dce4322a018d6671981520c21eba0cb19021595cb63d4542d2a86b00868862d5458a400832d29ac028c851b5c86454031b28e2b128621e5653987521021ebb2a9190614d9d352544308eae232a851845e73d95414871aaa2c3a90610fdd1654c110d88c7b12a88861c5418d408c2b2b90a928861d819752481109aee6b28848870d5454d200830f2a2c721043c95915208710ce0ca90a40885647158d52102e2b9c8490843599c853946408eeeca88a2214b576990214423abacc3a18435a5c83154021a6ce929e4290d35748ca519022f39ccba0841875915314c10a9cec2926498d4e721815390a8e39aa82a4419954861483108dce432862a052d72152438c21fba2ca9922187590534c9408bce7326a090cd57698c204426abb6a619221175ce65d0420caec728a811043d74d96318823bb8acaa1a43555ce60546408eae3328851864e64549300c28f39ec8aa043539d7434cb20a6ee2b10a89851e7494932cc29d3a0a6a804399d4861509408ecebb1c428855573101511029b388c0aa0431e9d85248210d6684b04848863854580214c31b322c22a065559ce4254620ba0e6aa6a0885377158a540c2b5390c92804387991538c8208ece332e6408731540c5500861eba0ca994218e551600c83087ee8b1ca190d3970153420cb26b1ea5212635c9c74354021e1cc621aa42051e73d9542d031db2aa898061591c5521493096ce9b2c648858e74d4d32c8332292c390221641c14310d108bce6302a810fa3745092044296392a8a14635c9c4635402196ce9b18408847776544514c398aa2a29806199594520c910c6ca9b0a841845d7694e42082
  | 28 => 0x8620d66a9b02a8886715258052c434ca1cc0288871d5c46055332ac8e4b22a3185367198254082ca3a2a6992219598e61150208eee2b2a640851f7258c544c279b82c7a1221559cc524401096ce9b1e42884777654821c4273bb28421621875954310c10a3ce7aa28690d357414b50443c8b2260182219398d529084096ce9314a78847a75d8143443d02a484902210f9d26294d108bcec29a611062d545884004237390c0aa663c59515354420ae2e020aa190c767118154cca3b3b0a698a213c5c365909109e4e0324648866562984540431baa4c2202610fdd95410f30b52e1aa285904f1760cb504422eb98c4a80830f5d365c8730f24c6a008088536748c9510826bb9ac8902211d5c66550c20acae418aa010c3d74d9421cc34ab2660182211d1c562950308ece2302a7214767118153d0b27a9ac529a831d5c665d0e209e2ed2a240885e1701854248272b90c818e211d5c66094a43d28c8a1a618847671d8950d0ea6b9ca5996838e9526014c2196ae931a4388570754ca20443b0a944088021c69515354021c3cc9318a58857172cc550086f0392a690221175cc61149108eaeb30c601065753185325031ab24a2180418d992510c010b52e9196409054c7254d3244335314c02a0639318d52504308ece332886106966458c52442963a2c6a90819594d6114840ec0a490c408863654d85420833928ac0108418e55360508308eaeb32265884d4735912044368b226018221559c66054c20c74a8b00861843d76950518cb27b2ca6908434bdd54350842a5ae82964088656635442190272b96c8186211d1c56215330cd2a530462207c1324c52044273390c0a1a2196d965350040d4ea8312a88863464949524429ab88c52a4652d9d363c81109e4e0312628856572d93514ca9a38ac4aa061c65525354021c5ca9316a21845e7614d318869b3a0a6a8c411d5c76590d208f4eda9aa010e3454185424c2f1b92a9102218e1526010530e62a8a8c40104e6768c521086e839a8090221695d05248110a6ce9194a31047576944308822e39ac9280411e5c16508410c6ac8a88421851d73988544c23b3a8c8192214d5d06254630a68e8a9ea08843d7419532042793b484902212ddd94210910f46c8a1240886615258052c431aaa2c22a0651b9c86550430c3cc929ea010e576510d32c430f2a4c6280434d9d362d4532b62e021a848869b6418d401023ab88c6a80850fdd16588530c74c8b00a48867251582410c297396a8a16638b593528c941ba4e8980608847575d85329030eb2e87a00615cdc14354630c5ac9310a70843e7498b504c63bbaac2200619558f5108530c98a6b166290e385458041483992a682a80439554d610c020a3ee6b04a919659535805308786aa2a4980611d5c46054b43e8ca629664884f17019743c430e322a8980
  | 29 => 0x90421861d6498c530873232e6499221acd51609091096ceda1a808861d5458c540870e320a698221ac590648811093ae630284a0655535833108793322a42962159dc96354630a5ae42a0871855673d92510c394a1084a80431ddd56110010d8aa6b106210c3d7498853482c739ec8a12418d9915108420b66e8984408851d75990430c34a32486986213cdc164d4910a6eeaa168210dc473548524426a3b2a6992214d5d053c4210a9ae5aa0861845d7654e4208236392caa1a210f1d16394321ae4e0314a3204f17019643c42f1b92a7a82211b9c86510c21ab4e1a9ca610e6552185420c63a38ac7290811d5d76150a208bae6312a3206d163580214438c298c0a1281595c860145328bce7314a98863664944200431b2a2c228465c514f61509408bee6b2a8088475751903108733296c2990614d5c46095232a3eeab0a8621c5d7318152d076829ac021a211d9c4650c8108eceb304848857170cc5500871caa2c018861555cc52c4210c6ca8b088018671515805110b16aa2c4204211d5c66094843cd4a4b00421866662944408c327b14c5a9a811ddd56210f10ce2c3306a9186955418d40c430fb2ca8980611ddc56394a408eae3306a4a1ea66498830c426b3b686992211d5c46550830ccec4a8a621049e70d894310e8f3a4c2a988117dd9530cb21e2aa621ca2206947359030c421f3a0c2a9061a650d6010d20dc484b00848845e73d94211022e39aca20a41555ce4254430bc2e418aa010d5573d93514cb0e31ec4aa061ac1516010910ccca4b0880185717010550086ccb86a8a1e61359ce64484218eeeca90a48853970d915408673394c898a211b9c86510f10c6aa8b0c8410e356599021c426c382c8992619998a5110030c3acb29c862045e739962110326b1aa4290814d1d16354440ce4e2b00a818cf27018c214438621aa520061479cf5450b20caaa6b0c4010557735525188326b1ca5a88819c9c560d52319cae532263884777654451d0f17324c429c213c5c06550f10c9aa7310a22051e7498a531028f3ac86a12619c9456088620c98c6a92801846e7219743082b938c84a80438b55262148308dce432c8608536748c8514cab938ea4880211d9c66590c10ec4e420aa010c7576946408c21eba4c5a82638b952621443099ae7316829047675991214426cb98c0a16611d9c665d0a309e6e0b2c868861d6454f5108279b82ca992215c9c06254430c3aa831a81906994358043842aab9ec928c61781d94248110bc4e598a408865663544408828fb9acba04819918c5248510d28c7a12808847571181548cb0eb20a9182614d5d36394630c38a6b1480a06c6635883108768b18c710221569cf5094021acae3304a4205377550b40c42b5380c329081595c66054830c3cc9a9c64a063a54580420829cba0c7280438d591510
  | 30 => 0x3d97424428eba0c12984187d526390910c6aa9308a81868c6350940c8278bb6a010221639d3634cb20aa8ea992608845c73595404432db9ecaa00814b5cb6455030e2aa6a8a802047775586408c2a739ea5296838b591528ca40c6ec830aa89065663944219021e3b2a8980611b5c865d0e10c9aa6b10801054d72d53300c370316c0a9a21c61c143540438eeeca14a3204e7764c832c42b8bb062a8043f0d0d3248110c5acab2465904777558f20c431caa2c029843875d4644c030c3cc8b18a9086596398052042ab398c528881959966308110d64c8b00a58855673909519025bba2ca192218d192514c030ce4e3300a610c5c7694d400830f320a619281175cf6590b10a3aea21c801862d645482110393ba2a429221b1d4c6254d1087ae9314a7084747119542442f0b968690221179cc651081087ae831aa010e3654584400831b2a2c2290619cd96514c030caeca30a641964e63948211030eb20a9996611d9d852487108ece3304a521f1471552530878aaa2a398061359da534c910cacc6a88431869864d8d300c28f39ea9a16439358e6215230e1ce42a664984e57219230c423b3a8c819621535cf54c8020a68e8a88a2904767614d31c434b324c610e2193d4c62545409e0eca9a408845e7398a5484278bb08710221355db430c310bc2e42006088564754c92044326a9ac429c81555c75494c208eae1b2a4210d1d73550430c23abb4a320061939d662d0d328beeca98a010e5553d8532102a6392c2a984147dd95310c4087ee8b1ca0104777058754ccb86b90a7a1281555c66054c20caca630a641047776550514ca3bbb28528c61745c35354f10aaae7212a3105d273087104425aba4c598e21c55504314532cb2a6b00422045f7614c215023bb8ac42a2611d5c06155132e48a8290848866652586208429a3aa84a02216cdd15288110ccaa4b08410856472591510830eb20a610a812d5d363087108dce5b2c87886a664588304430e2a4c620a618d596540c421d2ac6a00818863754d85524c31aaa4c22004199d886155120c3cc6a9e81204cd72181434c23bbb284a8881359cc6284110c3aa8b188018477764ca518823a3aac421a21ac1516010d108bce7b2c84885357414a510c386a9a84210433c9da404c110cacc6a8880185727018a510c2aab8ea72984155dd532cc310a6ce8296200843c76951300c237b92ca21a21879935308540ae2e030aa421e666298454082abb9ac4a8c8117dd95314840aaae2302a72165563944210822eb98caa08411d5d7614ca30c3aa8b18801051c70550434ca78b86ca21a210f9d9544c030c6ec9a8aa09963a64580540c6f0ba46490221175da5314840aace6102a2105d170d4e53c4237390c6a80832b5d262cc720caca730c401063664584530823ab8cca21c414d5d23294420c9ac72
  | 31 => 0xb3b0a68802159dc954d4110e92a790aa010c3f76550530823bb8ac429a810f5d062546308ecebb18408861c5498c214c237bb2a4296618b95162d0e32caae630aa59862e5458b510c297390c12a4659c945600844096ae831c408863654586508ca2fb9acaa12211d5c660d51328eae130ca8995657114e521023db82caa1a431d9db5354620ae4e1212a21061e6454e311022ebacc610881175cf6508410c9cc6b14a890e1d6498c5284333312c229e43875536348430c6ca8b08a6105557510e518c31ab22c2282651ddd921540218ecebb26648865953582320823ab8cc12a2659c9c56015021d2ea831a808861d6390c5050b39b8ec0aa2659594d6190c21a6ae3b16a89871b70550434cb8aaa087a8a658755163d44208bce632842a043f76550408c34ab1c8620621ccd0b4154021ccca430a841874553547200832b31aa6188438759153d4021c3ac82a265984f27098a43443a999662a8043475cc62d5130b30e0a1a809855b705915390a9aba465a8a659c5856015032e88a430a6498e1d6494c3004326a9cc520041659d2324cb10a3ae9298861052e72d8e5408637bb2a4294631b9cb65d0d108bae7314a908659535805310b0eb2ca9994659954961900309e2e1b2e868861d6454e32102b9baa8510221595c85414910d28c6a12818855673981518831aaa4c22006187991538cb21ae2e018aa190e9463d0d4044332b12c22a061595cb5354440a6ae9b16a29943e749943108732b14c22a063ac5922008110a9ce5b24a610d667214f108423abb4a2180418b1536254530ce2a2b00a2196956498c524423b3acc898a2117dd5639082187ceb32264a06396458052c428ebaa8621e215c9d221540219e2ec216a08870d4310e520c32d29cc0280431bdd95214a418bee6b24a010c5f76550434cb33314c229841b89c2621011087ae832e640843f76550434ca3b38ecb21a419c1973148110cc8c5b0aa88843e7419432c42b8b8062a80431b9c86590c20a6ce9b1ca220654531853248332320a490a2193195324c7209aee6b22608867165947308c2b4382c8a90619998a61150108f2e132e8610e9b4318132d0274b90c0a1e414d9d053c4210ab4e1b1aa610de174909204432ab2cc610621c99515254430aace6312a21855570185530870f324a7190411d5c465d0e20dc242b00431055671d8b535028eba0c229a818d152618c130d52c8b04659057270189511028eb9ca821841355cf64083108ece3b2e85987255454520082d8b86a8aa621691c95450b10c3aa831a859962d54588540c6a739880a9081479cf54d0832cccec292428845f7654c5350b0eaa2c620461749cc62d4110c68caaa2858863574195424438aa1887288418b5926214a108dae5b2e86886b1648c030442ad39c8528043475cf6115130a6ae829683884d57
  | 32 => 0x187d97644c030c3ca8b1842185e372591204433928ac020c6187dd94354043ae0ea90a4088635645845284338b86caa12210f9d365c8730b48e8a90a4886e276149204428f39cc52a0438e5526014021968e8b28648869564d0c30c42cb39ea8aa6211d5db53c4010a3ce92966598cf17019442c4297390c12a061351cd65481109e2e132e87885e272d01204423d380cb21021f09ce4248110c9acb31c859047b765405050b2d29cc010881559ce4294640c5ac8a90a41847671983544cb1db2ca8900414e5c06215130a6ae8296200864d63588540423bbb2a228e651ddc56294c40a3ce9a9ca790dd27390b504424e3b4a898061a35c86050c43cb2a73004210793735004044236b90ca21a21a550c6154843ec2a4a8c802062d5458a410874b3266519221175cf6590910c3cc829862a066952582410c23bb8aca21a43b85c86050d10a76e8b1ca010db1740c220442f139080902210f9d263d4121c72c8b00a48853574d49510c30e3b2a6a0081999896195131ce2c2a80a12161e6458c5284316322a4908819a5496014843c6ac8a88432049f7650f5110f8aa9c86a888199148614c930caca6b0c802043f7695232086ccb808620061ca951525004087eecaa0a918d6672d4e511029c38286a808774dcd52d4110aaae62a6200843d76d50438c2b8bb682a80439c9956188110cb2a6b00a3214f17098853442b8b8884a80434d9d062946308ece3306a6a1732541055008656392c221a851ddd56210421caaa6b0c801047675d9020442ab39ca990a43475cb5410e309aeec980618873154546300c326b1cc42a04355dcd6254630ce2c3306a6107154310f5150a8e39aa8a1c41ca9c04354840c38a8b1460986956410f32442d8b84a8a12219358d5290840b2ce9b1ea29966452d85424c74b322c6102219554c61508408ecedaa220084757519032442ab388c429a813c5c262d5110b66e8a9c408843d7655232082b93a8c310221591cd5214910caeeab18438865563944211025b3a4c4192212d9d2654cb108eaeb30c8610cf370597324423ab8ecb996818e951600843087aed2a0a61067161983540822f39cc52a221561c16454c20caec628aa0a145c7654d40082b9380c928c611d5c261d53328eae2302a819572708c95108237396ca200214d5d052d0510cb6cbb1a802043e74181520c6b2b8ea6a908159dc9635464087ce932e639047571d9150cca6ab98ca212211d9d464881109e2e131ea48864c7258c524422e39aca212215c5c24254420ce4c2b00a5884b574d8d52c4334a94c0108610f5d0650c910aaae6314a21045f73596215031baa6c2a1261785ca5448110cd2a4b00a420e5763545400c369a9ac1192218bd955448421da6a7b02a68861e6498c5308636b94cb188818b5915214810c68cb21a848865953980411023
  | 33 => 0x110aaae6320a29964d5398b511032ab1aa228881749cc52d411087ae83286408476761492144332a92c3180618e152608c530c6ac8a88a2195717010d511030e320c6a92212d5d0604cb10ba2e021a648852d7494b42cc678b86ca212210fdd954153328bceda9aa2a064d635885484272392caa0221875915314c20a38e6aa081105567510c514cb1b2a6c299041555ce4254640c3ac6b00a89866562544510c31b2a4c229061c99915208710ae4e710aa010e96711814310eb338ea5296874d9d060d4532dc2c4a00808861d6318d540863aba8c2a10214d5d36014542a38e6aa2870866471588540c71bb24a2980211b1c965506309aeec99064886b361181425030fbb2a99806193197434c9208dee4b2a6088667651854210b2ab2cc6206211d5c66510c208f2e132c8610d657214c52c423dbb2a0286875c9c03254420dc2e0312a88853974d4d500861ebb4a9218870f5d06054b31938ecaa2601846e729973110237394ca20861a610c6050830a68eaa10848847a7019442042b3390a788021471d1534ca20bc4e529240884747558843c432b32cc620221561c16454e42ccaa530c801856671d4d5210333318a490a2187d906355220dc2c5a80608861d5498e410c70f2a4c721641a5590434c9108baed2a48621c767119442043b0a92c029221595c854c4010e1aa929a4010535748ca5110326a9ac429c21475cf6455020c3ac8a98610856672d0c514cb2a31ca2a0441175cf65100109ace6318408846e7298f505063abb0a7880218d5925414910ae2e0212a22045e73996410825b3a0c810a214d5d053546208eaed296838853571153420ca8fba2c1298439394d620c421bc0eaa12408847676d51518831d2a2c0108411edd9501423196ae8328658843d76952411062eb9cca10881179db5454c218ece3b1aa1a162d645885384327b1aa4a1061e89d05248110caac7a88a0a1732540c5500863bb8ac529c819358e6215020acae429a200868e43588404c26bb9ac9102212d5d3658cb10a3ce7aa4a810d1d73950434ca56ba0c099641275cb6550c43c9aa6b10a60861d751814310e9b3a464a88618759054cc930c38a931e849869464945300c34db20c0a1a615a9c864540218ecebb2642886956458c524429a38ac52a061d154a514c0308b8ecaa2601861e6494c210822f398ca208431d1d5644c910ec4e418aa010e8e721814310eab3ac6098221a55c46050c43c9cc6b10a8184f17694e204421eba0c4a8463471d54310d10c6cc9308a6105d0735922044296ba0a5a122117dcd6548640c9ac7294852065763545408834aa1cc228087559ce42546308f4e132a8610c5f7654c5090ab338cc0a9081d8dc15214910a5ceb21a84906555358442086d839a802022117dcd6508540d3287300a421c6e72d96434431b2a6c29906
  | 34 => 0x864a063471590524423b388cb2182199d97614c8328e8eca12a31845e76d4d5250392296c2a12836c9d35050110d32c8980608847570d95424438732086a9061355cc6050b10b30e0a9886a147475586434422fbb2a6298431d1d942944308deeca90a420d557314b31c432da98c0a1a81d454e61540218bce7b284208557735515188273bb2a429621749cf504c110c6aa9b0a84186e232580324421fbb2a8108615c9d12154021f4284a02408843d74994210c38629ec4a12818d5925108640ccaa430a642051d73188544c332b10a420a21719cb434cb108eaedaa08390c7575185429029b3a0a4a8c61595c863145429e2e030a65104767614d5108237390caa1c218b9916214e108dae5326a098d4e7295132cc32b31aa2204618d5516190c21c98c8a9660186c4624c931442aa39ac4a8c419994a618c030c5ac929042205b1748ca2044316aa4c5a8861555c66094e42c68ca21a84885647550b2044327b1aa4a00818d9506150830caac7288801868d435885110ee4b86a4996611d1d563c81108ece3304a99951c7050d5010f2a32ca699221651cd5450910d4ac890040884777654c5150b3928ac01886174dcd5488110c6ea8b08809851d739905448726a9cc4200415c1c14354420a6ce9192a3104f2719803244316aa6c0900419554e61900209aae7b20438866562544511023bbb2a3180411d9db54546308bce6308a4886d163d402044296b90a8212611ddd95410421d2ec9b1aa48862f6298b544c326a9ac5180413c5c3658c910c68c8a8a432051d74d8d53086f0b9c64902219598e5108420c3aa931c821855571152530830e2a4c7212619698e6014810e1ca6a92802062d64548200422eb98c8a80434d5c6609502087eecaa0a9084777654440882ab39ec5a8a85d194d5294440c3aebb2a8621e2e7598a4350b34a92c1188814d5d052946308bce7b2c858861d6310c5050ad8b84a82a221c555153544208eeeab0c60106d3431814344278b84c7aa221555cc60d4532f82a699240886966458c52c438a2a2c3182619594d610c02093eeca18a021c5d7319742042b2392c6a8841a5d90438c310a74e1a1aa021d7275d89204433829ac0296215c5c35114132b52e1a9285a04d67398b4144273390c8182215cdc15414532ccac5288811063664544210c30e324a69862147dd16094e42c38c8a9a618847776544515023bb8acaa1e415c9d76388110c3ca831a81984cd7318142c8326b9cc52a263875db5410e30a3ce92a2649851e7550c43882b83aac890221d19cc5248510aace2304a610e1e5458c21082e8b9843102218e55260d4c219e4e03226488477755864008353b26c4a9a219599553d0f10e2a8621ca22065463545400823bbb2a31844199d9452d0910c6aa9b0a841064d621885350333294c2288614ddd152d4
  | 35 => 0xd40404423b3b0a8a88419559553d0421aaae7214a3205b0744c0304426b39cc890e218b550624c420d62a8b00a98861f6594d401023dbb2a028487c59525354420aace6314a21069563d0040442e8b9c85a82213c9c36308110c9ac6a9485187c173909204430ebb0a7202811d9c665d0e20cacc7308a0a147775584200423a3b284a8c410f9d063540218eae232887106576554d21086b3396a328881a550e6114843b66e8b1c40886e1624c030442793b0a49022187d95544c030c6ca830a841067161540508ca3bbb2a228c879398d5290831c5ac8a90a50847676d49511023a3aac221a21c69525354021968e8b2a4088596748cb514ca3b388cb19021785c83148110ae6ea90a200852e74181520c2a7398c329061479cf6455320aaae62a4a31062d5498a3008369b08c0992619554d618c0208f2e13288610d7271d91500872bb8ac6292210f9d0658ca10ba0e6aa4408852e74d8e521023bb82c22a065479d26294c20a3ceaa18869057175d055008717322a519081e450e6010d10ae2e1192a21061d6410c504ca78b86ca992216c1d13048110acce3aa4a4184f276d01204423bbb264a8c819ad95524c030b30e0a1aa021f255494720083c9b828621a21b194d620c421a3eeab128621db174087104423b38ccaa1821c3d50524c9308ecea326628861d6494f510821f3a0c4a88614d9c46055030ab2e02a6641963454185524c279384c421a211e5c261d4943c5cc9310a6085597390a500869ab8cc12a061551c56294c408baed298422046e721953110326b1cc42a0219354c62504208eeec992a21057375485500861e3a2c7a9221b498d6008510a72e1aa4a810de173d49204426b398c0a1221569cc6294021c3cc829c64a064d535883088279bb28020221b89c162101108eae3306a6a147575185321032b29ac3184214d1d16354620d8ac790040884777654c53c43c8a1887102215c5c361d41429e0eab00868845d73181540863c3aac1192218d99261141328baedaa0871852e72d52540c30f2a4c7216635cdc542540218dae5b2e878862d54588548c28eb9cc52a041c554c4354440ccacab10618847676d49519025bbb2a82a6218d5925108010c98c6a92841851c7550c434823bb8ac9a82658e5926014c219e4e1b2040885a67290d42442e839a80202218b191524c030caac72888118636549845308278b94c021a214b9ca6355021c3ec821aa5185357510d51902aa38ac4a98811d5c660d50328f0eab00869045c73596215023b38ecb99681785d13248110c3ac82a2649865453584434431a2a2c221a219594d618802087ee8b2a631057271d9250086abb9ac8a8c41599c85454430caaa7308a42051d73950430870eb22c6296214d5c460550308bce6328858851d74d885350316b26a410a814d9d053c4010c3ac829
  | 36 => 0xb80c299481479d64390130a6ce8314a21865463545218c2b2b968628a655c1c532940219a8e6b24418863554d85428ca9b3a6a328e65995896115220ce4a2b04831069663d0a42c4278b8cc1994418d59261d4c2087ae832c650857275d92204421f3b0a8a1a659958a6114e21c5aa9310a218672515802104335312c02984317dcd6548110e2aa830aa610d1c7654d401032b29cc228485b4d8f6054910b2ae23028621d5573d4651102aa38ac8a9c85595c75494830c9ca6b1080105b17010e404430eb22a6280439558e6195132b8ae6296408863a54580530861eba4cb99621595c45494830a3aeaa1886106547158e52d070f322a6280434b1c954d0910c5cc8a90422061f6418d544823a3b28528881179ce62d4141ce6a2b04a2a1ee270988304423d380ca21a439398d6215031e1886a9264204747558b304423b3aec2a126559dc96454630a3ce8302a6104b67498b304426b39ec810a211edd95014032bc2e4302868876152545300c32aa9ec2a1843b110d620c1109e0eab0484884b57418a1044386aa2a6908439c1955248110b28e6aa0a88865563984520422e3aac7212819c546600842096aed218808847675983324430e2a4c6212614d1c554d07208bae7b2c84105657214f108422f39ccba16215c5c15244010d48c4a12838871473552510c23b38ccb210215c9c06294440b52e9192408843d74987524c28eba4a621e2195d4d6190140c72c8a80a010c777159443482b3baa4210821175cc6508010a58eaa16809047a709954304326a9ac420843e890d4248110cb4c6b06a810e3564944300423b388cb21c419358d5208410ec6c4a8a401066452584324432aa9ac2298854b5c86115130ae0e0aa0a29943d74d96320831aaa4c3218630f5d6648c8219cce5b2e878861d54583430c30f320a610a812d9da5450910a6ce8294a2184f37059540442b338cc1290815c9cc4154021c9cc6b16a8184f37648020c431ab22a210c615cdc54354021e8ae6292428843c74595304829b3a6c7288211b5c86054c41c3cc929c6590e95644c030442aab98c4a8c615a5c84154021b64e8292408864d53d89410831aaa2c220041179d66308540c38a9318809864d6558e42c8368b1861102215a5ca43540218bcec29a659061e6458c54086f0b88c0a12415c9d463881109ceeab106210f635294920442b3390a98802117dd9530cb20a6ce8296210865573195324430eb24a6184418b59554cca32ce0cb10a408843f74597214c31aaa4c321e211d5c46054f42ba2e6296a08861c6454d30082ab388c129c85995886294410a6ee8a9ea08863664544218822f3b0a899065c394e4354840acae5aa4a2186727198052042aab9c84a8c61595c7539484093eeca1aa421f2954485500862e39aca10a81471d15314d10ce0ca29a40886d263
  | 37 => 0x87dd3654c030d60c8a0440884e67219443c42d2ba464902213c5d8400c110b1ce7aa285904767119432502b238ac8a90613c1d5600c910bc2e6292408847a709954388769a9ac019221e85d05248110c38e9b2a6018596711814310e723b284902219554d6114c409e6e4b04a88855673151510834ab22c6102210f9d3650c0208e8e2b1ca52066662944408830f3288799481475d25310f21b62e030a85a056671182520c31daa2c010a61785ce4248110ab2e0308a6a066562987540c2b2b9082a80430fdda548c830d18c8a92601847a701944388672392ca982219554d618c821a6ae3b18a8984f1701923244296ba6a690041599c46054840c3ac9318a58853a748ca50086e4b86a699641c39534354830b66e8b1a408861f5458c214c2aa39ac4a8861d89d76248110caaa730e878849f7650e5210f26b1ea5212838d9926114e2096eeca1887885947050c43c4236b90c029a219958a6114e20c6ca930c601862d54588310863b38ccb99481559c75454c20a6ae9b18a2a145e73194428426b39cc52a621475cf6195232c9ecaa9a40105c57390b20442e8b808718221789c83048110ac8e8a90a488665629443008316326c4a9a218d9916114e20aaeea9926188672759804344266b9cc5a06414d9d232546408ecebb24608866452185425034d31ac0218814d5d0535442096aedaa0848861e6498c524426abb08618221471d1538c220a3ae6304a91947b76540504ca73390c9186211e5c0650c9418eeeca88a2a1ea56498830c42b8b8c64a80439394e6214840c74c8a80a010c6e729943110326322a498061871516390930aaae62a4a21056671d4e52102a7baa8699065a5193534c1108eae3304a7a14f370591324430eb24a7a8043c514c6150940a3ae6302a81063554584400c23ab8ec6a8685871d94354043e8886a92a21847b76540504869a3a2c4a8c41c310d5250a30c3eecaa087994f37058c544432b29cc3180219554c614c841e88a6290648863554584530823bbb262a8063179d66390940acae429842887615214a204422eb98ca20041475d06054c21d62c9a00608865b539802150326298c4a8a811d9c660950329e4e0318408846d72996410c278b84caa1e21a59926314b109aae6320428847675d85434421fbb2a82a641995896114e20aace7214a21065563944210435232284908435c9c36394620c6ca8b0e8610c5d73d9742c421f3b0a8a0c431b9c86510d10e2aa8a8a601864d6314a425063aba8c299021999895114440e92a7292401061e64d4e3244327b1ec4aa2219594e6190040ae4e321aa010c7671195320431b2a4c2288611d5d661102208daed29080186956310c40c42b3baa64906211d9c46054b438dae432a82184f27690b504423ab8cca190811b5c860553318eaed296828865463d855448278
  | 38 => 0x30e2a8621ca20843d76152324c3a2a92a398061719cb43d4532dc2c510e208853571d52540c274b90c0a1a211ddd9530c4218e8eab26408863665d004044316b24a519461475d66050c43c5ca8b168610ce672d9643c422fb9ac9a92218e9526014632ccac4a88801856571182521031d2a4c02804317dd95314f2087ce9b2c6588535741805150a56b90c0a1e814d1d15394620e1ca621aa42067261580540cb0fb9ecaa0081939d8524c931cc8cba12848855575d0e510c236b90ca21c218d9926115020a9ce6302a4204f370595304423bbaac2184418714e60d0940d8aa6b108210cd77650c43c4316b24a519041b4d4d6094d10d2cc931840885e172105500872ab1ac22a441179cf6590821ccca430a642047671196430831ab24a210841c31ce54548309e2eda0c40885567315110042a7396a6992818b18d5250040caca6b0c801045d73194428430f2a4c6108619658e6015010a9ae5aa2601871870550434ca1eba0ca180211d5c6650ca40ae2e1a9e6210e2d6454a320428eb9cc52a0438d9915108640ce2a2b068220476751813244327b1ca4a008117dcd6510910caea730c80a045f7654c400831b2a4c3180418715263d0530ce0ca2a240884e67219031c42673acc5a1a6587193534c1209cee4b068210dc97390b204825aba0cb19221f0589300c1108baeda98648865b6518d4010387a1aa4a00618d5516114830caaa7308a2106676518542c822fbaac7210419558d5108440c3aa8b18800866552584521022e39acb90a814ddc56255030e1ec6a92802064c63d89544429aba46528821875954310c219aae7316818856672d4d511021fbb2a8216633c5c4604ca20a3ae62a681104f27018d4244297ba2a790441175cc6014910b30e0aa086995727018c5150a3abaec2a14813cdd95388110e8ca7294a2206676514b324431b2a4c2180410f5d263d4121cccc4a88801057375885100432a31aa2a00611d1c56550d20ae0e710aa010e5a5358031c421f3a4ca180414d9d353944208deeca90801851e7394b42d06abb9aa9a82210f9d265884308ecea318408843f76550540c6ab38cc129c85c995252944308e8eca12a32052e72d51424c28fb9ac12a043745cc404811087ae9b2c6410d3574d46510c352b22c4182211ddd942d4532f428421240886d16318d20442acb9ea8a80438d5526194232e1aa6a96802051d75950430c2ad384c2a9881a91c96414910c9ac7314a898dc47254f32443992a2a2900419958a6115220cd2a5b0284186c562cc0304430eaa2c7208611b9ca658c440c5aa8b10a90845f7654e420828e3a2c4a98814d5d26054620970e0b2265a067271583530871ab26a2282658dd53614c9308bce6328648866452d85324c70f2a2c621465279d85350f40d32c8980610866562587540c2b938064a8861
  | 39 => 0xa018c3e769514388332b14c3aa665b89812008110ba0e6a96a08861c53d8943502cabaa8621e21d454d2154021a3ce9a9e65906c5635884044338a8ec0a0c8187d9763500408b8e6b2a80906b16458052c423b3b6a6a888147dd56050c4396ce8328658865563984548826ab9cc890a21569cf5494021c3cc9298a010ce672d9030c42aab9c85288410fdd5648c8209aae7316828861d5498e42c871aba0c2a96811d5c66094b43aa8e6aa6a0886c463d495244237b92caa0c618ed955448020bc2e1a92a58855970d0e5090f8caa2a6900418b55162d4430e48a4a1682a0c6d72194414c29b3a464a8c61475d35394c21acce5a8ca3a1e6562144314822fb9acaa0241599cb5194430caccba18608845f76550430c352aa2c4188431b5c86054f41c6ea830a849855571981531030f322c6292216c9d232d411096ce832e408861c64941300c32a31aa2a0441b198d6210310da0e0b18808853671d52540c2f1b92a710221ac5916008510a6ae8306a29951870550434caf0b90819822187553604c030da664b0464884f070591324431aaa6c2990411d9d85444010acae4300a2a163765d8542d0726b2ca7a14858b1516210d20ae4e1b18a29955571d925390a3aba8c2994414d9d2329464087ae8308a48862c6250951d0316b24a41086199589511022087ce9b2c641045d7399741c831a326c2a9a411e9c06510c2187aed218a0a152d74149204431c2a2c118a614d5d23254440b52e9192410851d7414f438830e32a86a0261959cc6154b30c5ca8b10811863464945308824e3b2a6a00810f1d9544c020c6ca830a8510d657290c5150a3a38ac7290219554e61142428eae3b2e859845e731974284326a9cc418041175cf65d072087ee8b1ca010d5a7018a5390a8eba6c329c85785ca5348110ba0e8980608864d5358a400829b3a6a32886117dd563100208f4ec2a2a010d2e74182520c237390caa18419694e6008420a3eecaa086997a162500404438621aa5a10610f5da5490842d60c8a0260884f270d92324431ab24c229843951d56308710a3ae9b1aa61061d5458e400c24eba6ca99661875516308420e4ac8a90a588669629805404348a1ac021a211d9c4654ca40878e8b28429862d6414a324c69aba88728c81175cc6510810cb2a73046220637641855348359bb280202214d9c76315130c9ca6b16a2204d573d9642c4326b1aa4200613c9c66010d10ba4e610c40886b164102204436931ac0292213c5c3640c910ce2a2b00a32161d5458c408423cb80ca21a4374dc153cc910a58e8b0aa42056472591519032b31ca220041c355043948309e4ed98240887a0435092044316b24c429843a518e4050310ce2a2b00422062f64189544425bba2c710621871526090d30c5ac9290a2186395458021082973a6a529061c6153604c9
  | 40 => 0x800000f01383f80040a9016001c0000140020d04000000035052400000900f800030203b01b804c048000016807804c000002006c0020060048008028589000001024a00201283900fc00821704dc082000004000000809000601f800201b0018000056049000002450204800b10880020000a100cafa0258007800408200200800107d002e000017c04800d00080480000003fd802018607e05c800c000004003000003605003164d6354a4290332b2ca390441179cf6508740ce2a330042185717090951902cd386a821c611d1c5654ca40c6aa9308a61064e5398840082b3390a9884211d5d8520c510c6cc8a884318564715485250364b1ac1216419594e61900208bce6328400865765945300c278b84cb196211d5c46590c20d1886b10811861c5458f214c36931ea01022117dd56310832cb0c7b02a89079073500404432ca9cc0210419c1c76055132acae4306a29962c64549311023dbb2a0284431d1c564d4132c6cc8b08a81848d721814310f3828ac010a611d1d93254620e1aa9296601847776505501061f3b0a8a1641b118d3248421c3ea8b00871861d6498c5308338b2aa3a0481b858a300c110c74a9306a610f155494d51082f13b46490221175da5314021e4aa8a92a218561720c5500866b398c908221d494e6154021aaae6314a20847671983540cb3832e82902218d150614c930ce4e2b06a810f0f544c8324c32b31ac2282851d9c665d0c108dcedaa2a41851e7418253086b8b80c2a9681559c46294e428eeeca88a2185967390942442aab88c429a811b5ca6510430c3aa8b1842186576518532cc22f3b0a8a9841539ca54cc9319e2e1326a6886556394c21c425aba0c610a2199dd56210421da6c7a82808851e74d4f32c86b2b90a928c612d9d0658c910a3eeaa1886104f270193324430f3b6caa1887475cc6055232c68c8a8a60105567390a511026ab98c910221479d35394f20d3286b00879847571994420c272b90c0a1a214d9d06014532c6aa9308800861c6550c4348792a94a3a0081aa58940101108daeb3168610ce5721903044256ba4c5986418759253cca41f42e9192408863954580210c3a329aa4a8881599c454548308ece3300a99965753d85525032ca9ac029883475d26294c21caec6a8a811865663984520421f3a6cb19043c550c4354440d2ac8b18428869a4318142cc23abaec2a10215c9c36394440c3ee6b20a09945e73987525025b3a6c610e21171d9534c910a6aeba168210da174149204421e3a2ca18a411ddd94294410c5ac9310a40863665d024044266b84c5a1a65559c66454c21ec2a5300438854e72181530872b31ca320c619c94d6014b10c72c8b06a610e67625454108296bac86a90815c9c05244010b2ae62a086885d17310030442f139682902211d9c46550e20c72c8a80
  | 41 => 0x1400000400000130070004000238007005813002c001002c00246d005015000201f00d83f001400100680cc00c1460028010b30024000000c00a001074008c01200001f805802716a0028028002014034000c2d800200303b400a002004800406200508700901dcea8009076001002502400fc00400202000940000220020034022032080803400000c00180380a6001001805410410b003000c2e2002005000c000012020800cbda01601e000055a013054802800600601203385b0012017807002400f00181bc00003900880000080e100c801003e00001b8000000005005001800600f03200540e0002001004c01a000000000315e006003001c24600300b001c02601204c8030172024000011012800600c83b40620510000000000003004000803000200780100280060000230578001091806802200000288c400201204a000001e00001a0098000089020004400200515a8008004000000031c0180000100004052008000003db2e0090010004000000000800014606c020001400083505e159c0000db00800000aa030000008804009e08d003c054057000804c000002009014827098c003800400000106f02a40de28b000804c00000c01b8000000002008878cccc000000003400203002880f400201600488cc00000a06983d826000400c08ac00600000e806400000015a802c02000000080280160000048010000013006819c016000000000403205e00080003397bc01c040810201e00000040240060000d4c01017100800d802803704b06b807a0020318174023024000829800600a00700500fc00300000ec00200000100d800802000980100cc0f4026140c0ca007002000000200027e000402800b000006001c006000034805812e001000001e0020048010cc209c0ac02dc468000000026007e002004ab840140190028010148000002005001a00000300100de02e014003000000f03600080000000008f7847400000000200920152498a08010000000001c018003000001011a01b00581f000800f04483f801800e00b802c0b80e80a481281fe00300000f82a600004b00140d2000002000000000201180b42f200000d80680241b8005000001807101f836400c0000048020002001008008000401d002004c0020803b8003800202101600040780030021650018253005025401000100000140341c70018000238006007002c00a002346803400006b00b9e2c1f4002021802001605c00e8064000008009000002a00001380380a8144001048809a01a00f80d41480000421dcc3ba071009001c8a4005042803800e00009e80080321ca01a0054028030021004c22c013063800000a1d3005002c01a0010230234000010002000c00e0000f781f007c06c001002400000800080a400000300480000105f5003009c01c0050098
  | 42 => 0x1c002268000000002201c139801000200300300580380030000064206027010801c02000300a000c00a040039800003205000402e003200805a026093e00d01880000b002900101a400a07200980287a4001007003c1a600a0000560000003008000c00201a02e009c11000d00b800000000000088840cc004003816804800c04c00c800002f01f003c00800400200005a200800200a4002060000054800406f000000c00001d0198028006062003819c02c00300901901880350020000006002007815000a05c294801001c046001000000006b02e80a805403d05e000c02000001e80000000160190078124002001001405c02b04d99b000e54c00080e4c68095087808039600100180340020010010000018000003811001e003000007411e00e024802400000200285b80000080ce001801c0070040020000000011813862811c0078024b3e1180008008000001003000414a00900081d402c0670308f0c0cc05e00d8150254021001001c9d4008013800c02e002004805001400e000802800201200580081d402d0000000104043001017000000000300101d4000010826404403800500040720000000020000134000801c11a00b00000000040370b3000802412d00a804007a019002801801202500a0000000005002b0cc00002b018862807402c000000807600500180b800a000000010801800e00e0000040014002005c000000110011406a04f0cc0000172000000800003a153002001000c00d087003002c00605d00e400802a00001ac07c17502c81dc01400b0070028012037003004808c01d00b8018026001016035000e012024803004a04d00904bc014006016001804000704b000408c00300600041de006009801000000000003a00003220240000076000000001800000901e8230010011000000004400800104b001003a024006c01602100105f000ac40013006404000000180340020000010054036036000000c0020180284da400e0120010000006009000804c00000301580080000040060b2409002f0008000038066000819845c099003001002200e00380600080230d18000006000012000804a002000805c00e01200b00602f200300580840060012e8099c016011000000401a609001875400000300000b81bc016000800001000b2a4800811e000009800c00000a00104146bc2210058004044001002804801202c4fa074c00001d010004c012002008807001016502c800000e01500380340060110370034014001002811c00c000019804c00200b000000803e012001013802200000880141940a806c800400600300b810401200401904d4108006020805400e02200801540e67c003580600bc038001cfa0014004010000803e03b00a828000e04521d03e001e01300303181d804704686ac0003ab000853c004
  | 43 => 0x4002013809805000d00b813014c004002800002c0932c1000807400502b002a2a62d7009001400001825a800146e00700a810085404b000800000003300a0010006001021800000202f01680242f600603c807800018300e800401200500004b803e009011802c0b606c089802800000300001ec012000003001402e056024003400007e001001c000017048000800400722400d0000011003813802e0160000118002000005800001402f003000400003f003872404401c015000000001e00003c800e001012002008c009001822400400f0fb004c00000e0050000158171002014025400001408b4014001252000000001e00000000d200001c001c00c001000807800001700095b001e00301380a8000000016071c0b813f00202e400000100080080240000008004038028011004817c00a002819400800f011802431a005094800803000200103c800000000602f003e006002000009800000000000280160015dac00200401d800001201b0038069fd800a000001033068200500f4000041001000400800200b8054522007000000404e10e000804400004001207a8000001005000c2c800400180e400600a00000000000f0002001800054f00000d4000009198800002800c014800400603f004011801a04224c8028000000000001c11c02f0058754000000040802001c0050088008010000012803007200500000b000200a02d83e816a00002f807061e01301e015c0140150010010014010001802800208f00d018c002045000000400000a0010000046135000000c00004600b805000004f048840001019f01b010c0241d0041838001421701200040a6029000018400e1f4002800404400802100180a20570458014028010004803406c15101080000b000600380080060000050002718001008006c00210000006b000634105a00b800001a000005000005f007006000201a030801006e01f0110018256023003803800804f00800c000004d00080643721f2024000400a00100b001002e003062002400a01d00701f401600c04c8250011546018807c00603e005800000c0d8006075402e01800180000500120048010012218003813000a009000006406a017010802c04c00000d800400e00222e801410200001a00080020cf004805801a0d60390fec05a00507e80080000cc00800c800201200000243d60270028090056080021002c00600408d002c08600249981d8000001008804000000000080600400cd000017400200000e002816c01102480000400010058000016000002000004c00000080000000300a3804c4da00003780100020520028294000007000800edf206900c01b8000104000873400e00000380040000c10b3002800c000001804800201c000803804a029013801005400600d00f802a0010ba8020012007000
  | 44 => 0x3a014023806c02c2b1000002c02000000d000808800001f001268a01000580000040e60000028006015000004c1c20bf00280580fc000056808819c00b00b800005c029003808400c02501a807c00004f001011c02601e0020be400604100780280013cc008006400407700100002780ee01300d400003600280a002803317e861801001c002800008200b002117c006020009043402c09c002001405e4b200200000000070048068010479000000406200f00680601fe02d00082f401201900a800c50601400180880060000000058000000000003496801b003021400c00106d003c00000008e802cca8000010000000807302a000819a00500100484fe045032007c01c15d00200bc2601d600001b400000610603ec00000108000c001002800502347b201417e00c80000031038220028000003821c09a00d00c003c006003014001c00a00c0128028020010004000c00401803c8bb40180020001d6401001106b00780000750018024008043005807000e00a10b000004c01d11e000000001f00081740000a80090afc300047005000000800a000809400200600000700160090be8034024267000002000a00603e800803401700000fc042008338000c01c005004800c01
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x460509408d087591300c110d4075dcd3248110ac1801c96314910c60655c85448110989821c14310f20a90835906448110a0c8355162102209c1821c1434c110a908050d6010f10c91861cd40101109c08754d324811081e869d9544c030c51735c06154843a9186991300c110a50854c9600c910d21745c05248510d05745cc5248510c1a765c05450f30ac0864c93048110c907418d3088110b108054c43d4542c31545c0614c830e41635496014910c0c75191324c120a44835945210910d22545c83154021c44659cb434c910a908650c4388110d41735c05248510c60655c0614c920d82435c840cc110a0c8694d5250040a908050d61940439a1849ca5348110989821c14354043a31801965450b10c90631c14250110918805d54310f21949821c14354043929821c14354043d11811c14354043e21645496014910963825db315402181c875954310e20aa08650940481108a9801c96110d42e056458d5214910b8283dd14248110916851c14310d10a61829456008410c907650d404c110b808454d3248110c0c545c86050f30aa18010d62101108c9801c96110d329c287d0d3248110c31645c051141329918790c40cc110e42635496008710ca1645c8400c110d21425c44254021ca074589300c110a91831516010d10c91861c14310d10c15755c46050c43e8043588400c110b81821c14310d10a9080590434c910c50535c0614c940991841c1324c110e80735894010110c90641cd4088110a918610c400c110c167518e4050110e8374589300c110c917458c6388110cc074589300c110b10805504314532e05435496114843a44835886254640b8284dcd3248110a61829456008640b80835514248110b41839092154021e22645496014b10d11719c35410e30c51535c06150840a0c8654e5250040b0980151424c832c30651d15248110ac08654d3248110a24845886254630e11435456014443b0581151424c832c19655c04310030ca0735894010110c24659ca4350910a1486552514c030c60655c85348110a9080590434cb10a44835945248110c90641cd404c110e8163989401011091a861c143540439c1809cb434c910c24651c95450910e22645496008710c90645c7634c030d82745cc5248110a5180196534cb10985821c14310f10a9186d0f400c110a18805906454c20cc0735894010110a24825945410d10a63865496014910e09435496014843a938650c43d4110a1486551514c030a918414d6010d10c15759c46050c43aa182191408c110919821c14354043d07741cd5214910989821c14394043c0c7518d4250120c91645cc4088110a268498c5248510a908458c6348110d09821c14354043e82635894010110c9074589300c110c90641c143cc110b20855094048110a44825945310d10a46839905248510
  | 1 => 0xe055454d6210421d05641cd5214910c90731c1640c110a19859916010c30870855d84348110d12851c14310d10e055454d620c421b40835496014910a908458c6388110b108050c4354420c93645c0438c110981821c14310d10c917650c4388110d20745092154021c917610c400c110c4475189324c510b09821c14354043b108055043d4532a18805516010d32c93645cc40cc110d04741cd52149109908750e6010d10d047498d5214910c84735894010310a0e8590d6210130d11811c15410d32951801c56214d40b40854c93048110a1685d90438c110a928550d6010d10919851c14310c20b08805904354830a0c86951524c030d42535c84154021d12651cd4010110d09821c15410d32a3085509601091089987d0c604cb40e4053149600c910c927690e404c110c91645cc400c110c147518d4250110c30655c24250910e046354a5150040e05544c9610c821a0c86552524c030c85729c46050c43a908650d404c110a908758d4010110d80735894010110c9176d0f400c110c92651cd4010110c927418f5050110a0e86d0d5250030ac1821c16310110aa0865514248110c91735c0644c110c32745c06154b40c18631c16255030c91645c0434c910c60655c83148110a60855096010910c16651cd4010110d80744c93048110a90835906488110c0c545c86050d30cc173588400c110c90641cd408c110c90641c1324c110e42635496014b10d0a735c04354840e8264589300c110b20845485288110c8474589300c310d42535c831540219a3845cf6248110a9181d9063500409448798d5214910985821c14310d10c938750d6010d10a24845945248110a0c8454d620c220d817410d3248110c91645cc6488110d81749cc5248110a908550d6010d10b11811c14354043a60854c9600c910a198598d6010c40c9087591300c110d407554d32481109c3835d35248110a90835904088110d22745c841540219a1849c83248110989821c14310e10a908058c43d0910d0a821c14354043c49625c06214d40a188058c6355020a908059043cc910a1485590434c9109a1841d63248110a908750d6010d10c25625c462151309908750d6010d10e8164989300c110e21645496008710a508558c6348110a2684d9452cc910961821d031540219a1849cb3148110b21848c92154021c1675192304c110e05535096110821a9287591300c110991831c14250110a188550d6010d20ca3765894010110e056458d5208710c0d755c86050c439908798d40101108b087591300c1109c1839ca54481109a1809ca4350910989821c14310d10963825db4154021a0c86551524c030c907418d3048110d11435c04354620ca3645c840cc110e8164589300c110d0a745c043548309a0875514248110e05435895114443a61801c56215031e1053d8
  | 2 => 0xc0430c110a2484594520c910a9284d8e63d4110d12651d1300c110c90649cf504c110aa1821c1640c1109a1849cb3048110e834358b400c110c88735894010210d06641cd5214910b108050c4354640c51635c05114142b108054c43145428e0865d13248110cc274589300c110a18805d8544c930a0d821506350230c9387591300c110ca2435c86050d1099087591300c110c50655c2324c910c1775191324c310a188054d6010f42ac18010d620c110e056458d5214b109c1831d64248110d81745cc5248110d13711c15410d3290d821c14354043c31745c06154843c60655c06150920c1a861c143540439c1839cb4048110c89645c0434c920c0c645cb544c030b088058c43548409448758d5214910ca1645c86488110a1785590434cb10c29625c06215130960855d132481109c28794d3248110a9087591300c110c52735c06154b30c52735c06154843c14659ce4250910c19651c14310e10a8880590434cb209a1821c14310d10a91831914088110a188550d6010e20c0d759c86050c439908758d4010110c50651cd5248110c45625c46214d40c91861d1300c110909821c14354043c19861c15410d32c8874589300c210d41325c43254021961829cf4154021a148654d51500409c1821c14310d10e41635496014b109a2879514248110c8074589300c11099287d0d408c110d42735c83154021c0c635c86055030d8074989300c110a1a85d8c6050d40e21645496014b10a61821516014b10c14651d1534c9108998790c6050b30c84735894010110e04635495150040a0c85590434c920d12811c14354043c14651cd5450910a908050d6010d10a918418d30881109a1821c143d0110c8874589300c110d21545c84154021d20755514248110a148654e5150040c917458c3088110a188550d6010d10d22545c84154021c44651c9534c910932849cd2154021e41635496008710cc1635c8638811081c87591530c220c53655c0614cb30c14659d2324c910d8074589300c110989821c14350130e20541496010910d2075dd14248110d80739894010110952839d12154021c80735894010110c91635c043d0910c91645c043cc910a4683d9452d0910a30855906448110d0474dcd5214910c19769c35410e30d40734c92154021c24751894250510a618214d6014b109c3835d36248110991821c14310d10992849d1300c110e8074589300c110c60655c84148110a0c8654d5250040c85725c46050c43c8873589401011089487591300c310d21545c8315402181d87190534c220a61829456008630a19801954310d2181f87d974350030b098010d52100309c1839cb4148110d81821c14310d10cc376589300c110c177518d4250310d80435c8400c110c92651d1300c110c32745c061548439a3845cf5248110a928758d401011
  | 3 => 0x700c650000002021201000301a964281b0e80c1c000c80c0a1b00800a2000000002052800c6058058001e080407d22012d80468041a8000002018280c00078280208030b85400020040002258740a003101ec60501000be057f8181800008940e0201a680409000008a00018000a000a8000005d08041607078008200020002c10170c0040f080840800040a40000018200022000180810020040000048001e0c04804000605028120202028cc0900011220c018003e031701414b1238500000061f4063e0000cba010980c02c31e80000072280c208c0000c040506118000b108040200d12811c15410d32c1475191324c110d10711c15410d32b40835485288110a938250d6010d1099087991300c110924875915214910a18805516010f32a898010d621003089487591300c110c16651d1300c110d82821c14310d10c61725c46055132961829d33154021b108050c4354630c908758d4010110e83735894010110924879915214910cc3435c86050d10ac182d91300c1109c1821c143cc11081d87150604c930a908458c3088110aa1801c96414910931801c56215130e1054d84604c93089887591300c210992851c14310d10c90735894010110c90641c1434c110a928690e404c110c9074d91300c110c19651c14310c20c0f76dc95410d3288d821d94394043e0464549514c030961821c54354021c91435c06154843d41535c84154021a1880590544cb30a908650c4348110c30545c0615093089087591300c110c8474589300c110b20845496014910a1a85d906050d309a1821c14350110c90641cd404811089887591300c110d047458d5214910c908750d6010d10d80735094048110e81635894010110d41535c83154021c33655c06150b40e046454a514c030a9283d9264d4110c91645
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x48001000000000290000112c00000001800000000001c008000a9400000000003800200099000000401850018000000000000009203200000000008010000000200000001c00002c0180000c24a5e87591300c110c4039b04382c818221880861cd42501204431030d410e0a1886884242617458c30881108c0c910ea1cc021a2190075a0f74509204431010c3a264982408850125d6458d5214910a404bac73128020221410955917010d32443100c8c10e0a1a608852025d64589300c110c803a908a9a649022109198190704c9304429012cba086992408864060a811c14354043c40c33043828621a21091981d0634c2204429012eb1ac4a008088640609811c14354043c1032b0139486a12218098660870550434cb20304c08e0aa086996401d4835514248110a044aac8b808699241809656087050c4384290324320e6a0460886805908354960149109204c2c6a92c029221281922014358043c4244130b22a4b00a488680211635496014910c2032b013968699221880646087050f3044212130bb28621c4088504a57645c0438c110c403a305b22601822148097991624c03044290126b22e43244088640214744c93048110a404a2c6b90c71022128192201435865010f2010a39a84a024088604619811c15410d32c803ad09b9a64902214809798d62500404430410c3aaa8a12408860121d6458d5214910940c9100a1ac021a21840861d5534c920442a012aba086992408852025d64989300c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6827
  | 3 => 467
  | 2 => 53
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt s5K8 (i*5) 5
  | 7 => packedAt s5K7 (i*16) 16
  | 6 => packedAt s5K6 (i*27) 27
  | 5 => packedAt s5K5 (i*38) 38
  | 4 => packedAt s5K4 (i*49) 49
  | 3 => packedAt s5K3 (i*60) 60
  | 2 => packedAt s5K2 (i*71) 71
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 8 => 2*((h/1+packedAt s5K8 (5+(h % 1)*1) 1) % 1)
  | 7 => 2*((h/49+packedAt s5K7 (672+(h % 49)*6) 6) % 42)
  | 6 => 2*((h/670+packedAt s5K6 (52569+(h % 670)*11) 11) % 1947)
  | 5 => 2*((h/3806+packedAt s5K5 (431490+(h % 3806)*14) 14) % 11355)
  | 4 => 2*((h/2275+packedAt s5K4 (334523+(h % 2275)*13) 13) % 6827)
  | 3 => 2*((h/204+packedAt s5K3 (28020+(h % 204)*9) 9) % 467)
  | 2 => 2*((h/101+packedAt s5K2 (3763+(h % 101)*6) 6) % 53)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff83fffc1ffff1c1c78fc7ffe3fff03c09f3f3
  | 1 => 0x7fc1e3fe0f1fe3e07f1f8e0fc707fc076cd9c
  | 2 => 0x7ffe03fff01fffff801ff00ff807fff870e1f
  | 3 => 0xf800003ffffe003ffffe0000ffff8003f80fe0
  | 4 => 0xffffffc00000003fffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x108840044200020000824122209110880050b1
  | 1 => 0xb1194448c642a04a0390c8466423258832c594
  | 2 => 0x4220889108254014c801120889044a31850a0a
  | 3 => 0x6072952214a064a755240010d24e0312d80f40
  | 4 => 0x8443180398c98939a649a49c00080c236fa000
  | _ => 0
def s5Atlas : Atlas := ⟨8,rawDecor 31 s5Pos s5Neg, 0xfeeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37205
namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f0703c3f87fffe1ffffc03f0b1b1cc09f3f3
  | 1 => 0xfc0f803fc3f8780fe1e03ffc015e5e7076cd9c
  | 2 => 0xffffffc003ff800ffe003ffffe60607f870e1f
  | 3 => 0xffffffc00000fffffc0000f807f83f80fe0
  | 4 => 0xffffffffffff0000000000fff8003fff000
  | 5 => 0xfff0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x209000040480ca220328a409201090c40050b1
  | 1 => 0x2482801c418850662141a9582016165032c594
  | 2 => 0xcb25364002550089540212a2c6606029850a0a
  | 3 => 0x4109daaaa800010d989700304b806b02d80f40
  | 4 => 0x820e6d33336625c0000400c08deb00036fa000
  | 5 => 0xf3c00e0220444601111823030ffdfdfc000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 9, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37205
namespace PEqualNP.Outside.L_meta_37205
open PEqualNP.Outside.L_meta_37205.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 6 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 56 := bs0_3_0
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
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 781 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 bs0_4_288)) (concat (concat bs0_4_384 bs0_4_480) (concat bs0_4_576 (concat bs0_4_672 bs0_4_768))))
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
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 801 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 39 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 24 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 2 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 6 := bs2_4_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 53 := block_range (n:=53) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 53 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_384 : Interval s5Atlas 3 384 83 := block_range (n:=83) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 467 := (concat (concat bs5_3_0 bs5_3_96) (concat bs5_3_192 (concat bs5_3_288 bs5_3_384)))
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
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1728 : Interval s5Atlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1824 : Interval s5Atlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1920 : Interval s5Atlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2016 : Interval s5Atlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2112 : Interval s5Atlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2208 : Interval s5Atlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2304 : Interval s5Atlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2400 : Interval s5Atlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2496 : Interval s5Atlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2592 : Interval s5Atlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2688 : Interval s5Atlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2784 : Interval s5Atlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2880 : Interval s5Atlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2976 : Interval s5Atlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3072 : Interval s5Atlas 4 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3168 : Interval s5Atlas 4 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3264 : Interval s5Atlas 4 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3360 : Interval s5Atlas 4 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3456 : Interval s5Atlas 4 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3552 : Interval s5Atlas 4 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3648 : Interval s5Atlas 4 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3744 : Interval s5Atlas 4 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3840 : Interval s5Atlas 4 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3936 : Interval s5Atlas 4 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4032 : Interval s5Atlas 4 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4128 : Interval s5Atlas 4 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4224 : Interval s5Atlas 4 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4320 : Interval s5Atlas 4 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4416 : Interval s5Atlas 4 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4512 : Interval s5Atlas 4 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4608 : Interval s5Atlas 4 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4704 : Interval s5Atlas 4 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4800 : Interval s5Atlas 4 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4896 : Interval s5Atlas 4 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4992 : Interval s5Atlas 4 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5088 : Interval s5Atlas 4 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5184 : Interval s5Atlas 4 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5280 : Interval s5Atlas 4 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5376 : Interval s5Atlas 4 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5472 : Interval s5Atlas 4 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5568 : Interval s5Atlas 4 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5664 : Interval s5Atlas 4 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5760 : Interval s5Atlas 4 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5856 : Interval s5Atlas 4 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5952 : Interval s5Atlas 4 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6048 : Interval s5Atlas 4 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6144 : Interval s5Atlas 4 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6240 : Interval s5Atlas 4 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6336 : Interval s5Atlas 4 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6432 : Interval s5Atlas 4 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6528 : Interval s5Atlas 4 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6624 : Interval s5Atlas 4 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6720 : Interval s5Atlas 4 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6816 : Interval s5Atlas 4 6816 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6827 := (concat (concat (concat (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768)))) (concat (concat (concat bs5_4_864 bs5_4_960) (concat bs5_4_1056 bs5_4_1152)) (concat (concat bs5_4_1248 bs5_4_1344) (concat bs5_4_1440 (concat bs5_4_1536 bs5_4_1632))))) (concat (concat (concat (concat bs5_4_1728 bs5_4_1824) (concat bs5_4_1920 bs5_4_2016)) (concat (concat bs5_4_2112 bs5_4_2208) (concat bs5_4_2304 (concat bs5_4_2400 bs5_4_2496)))) (concat (concat (concat bs5_4_2592 bs5_4_2688) (concat bs5_4_2784 bs5_4_2880)) (concat (concat bs5_4_2976 bs5_4_3072) (concat bs5_4_3168 (concat bs5_4_3264 bs5_4_3360)))))) (concat (concat (concat (concat (concat bs5_4_3456 bs5_4_3552) (concat bs5_4_3648 bs5_4_3744)) (concat (concat bs5_4_3840 bs5_4_3936) (concat bs5_4_4032 (concat bs5_4_4128 bs5_4_4224)))) (concat (concat (concat bs5_4_4320 bs5_4_4416) (concat bs5_4_4512 bs5_4_4608)) (concat (concat bs5_4_4704 bs5_4_4800) (concat bs5_4_4896 (concat bs5_4_4992 bs5_4_5088))))) (concat (concat (concat (concat bs5_4_5184 bs5_4_5280) (concat bs5_4_5376 bs5_4_5472)) (concat (concat bs5_4_5568 bs5_4_5664) (concat bs5_4_5760 (concat bs5_4_5856 bs5_4_5952)))) (concat (concat (concat bs5_4_6048 bs5_4_6144) (concat bs5_4_6240 bs5_4_6336)) (concat (concat bs5_4_6432 bs5_4_6528) (concat bs5_4_6624 (concat bs5_4_6720 bs5_4_6816)))))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1056 : Interval s5Atlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1152 : Interval s5Atlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1248 : Interval s5Atlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1344 : Interval s5Atlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1440 : Interval s5Atlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1536 : Interval s5Atlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1632 : Interval s5Atlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1728 : Interval s5Atlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1824 : Interval s5Atlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1920 : Interval s5Atlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2016 : Interval s5Atlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2112 : Interval s5Atlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2208 : Interval s5Atlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2304 : Interval s5Atlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2400 : Interval s5Atlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2496 : Interval s5Atlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2592 : Interval s5Atlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2688 : Interval s5Atlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2784 : Interval s5Atlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2880 : Interval s5Atlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2976 : Interval s5Atlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3072 : Interval s5Atlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3168 : Interval s5Atlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3264 : Interval s5Atlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3360 : Interval s5Atlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3456 : Interval s5Atlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3552 : Interval s5Atlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3648 : Interval s5Atlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3744 : Interval s5Atlas 5 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3840 : Interval s5Atlas 5 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3936 : Interval s5Atlas 5 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4032 : Interval s5Atlas 5 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4128 : Interval s5Atlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4224 : Interval s5Atlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4320 : Interval s5Atlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4416 : Interval s5Atlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4512 : Interval s5Atlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4608 : Interval s5Atlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4704 : Interval s5Atlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4800 : Interval s5Atlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4896 : Interval s5Atlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4992 : Interval s5Atlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5088 : Interval s5Atlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5184 : Interval s5Atlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5280 : Interval s5Atlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5376 : Interval s5Atlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5472 : Interval s5Atlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5568 : Interval s5Atlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5664 : Interval s5Atlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5760 : Interval s5Atlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5856 : Interval s5Atlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5952 : Interval s5Atlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6048 : Interval s5Atlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6144 : Interval s5Atlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6240 : Interval s5Atlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6336 : Interval s5Atlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6432 : Interval s5Atlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6528 : Interval s5Atlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6624 : Interval s5Atlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6720 : Interval s5Atlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6816 : Interval s5Atlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6912 : Interval s5Atlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7008 : Interval s5Atlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7104 : Interval s5Atlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7200 : Interval s5Atlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7296 : Interval s5Atlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7392 : Interval s5Atlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7488 : Interval s5Atlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7584 : Interval s5Atlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7680 : Interval s5Atlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7776 : Interval s5Atlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7872 : Interval s5Atlas 5 7872 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7968 : Interval s5Atlas 5 7968 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8064 : Interval s5Atlas 5 8064 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8160 : Interval s5Atlas 5 8160 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8256 : Interval s5Atlas 5 8256 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8352 : Interval s5Atlas 5 8352 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8448 : Interval s5Atlas 5 8448 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8544 : Interval s5Atlas 5 8544 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8640 : Interval s5Atlas 5 8640 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8736 : Interval s5Atlas 5 8736 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8832 : Interval s5Atlas 5 8832 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8928 : Interval s5Atlas 5 8928 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9024 : Interval s5Atlas 5 9024 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9120 : Interval s5Atlas 5 9120 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9216 : Interval s5Atlas 5 9216 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9312 : Interval s5Atlas 5 9312 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9408 : Interval s5Atlas 5 9408 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9504 : Interval s5Atlas 5 9504 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9600 : Interval s5Atlas 5 9600 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9696 : Interval s5Atlas 5 9696 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9792 : Interval s5Atlas 5 9792 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9888 : Interval s5Atlas 5 9888 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9984 : Interval s5Atlas 5 9984 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10080 : Interval s5Atlas 5 10080 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10176 : Interval s5Atlas 5 10176 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10272 : Interval s5Atlas 5 10272 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10368 : Interval s5Atlas 5 10368 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10464 : Interval s5Atlas 5 10464 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10560 : Interval s5Atlas 5 10560 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10656 : Interval s5Atlas 5 10656 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10752 : Interval s5Atlas 5 10752 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10848 : Interval s5Atlas 5 10848 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10944 : Interval s5Atlas 5 10944 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11040 : Interval s5Atlas 5 11040 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11136 : Interval s5Atlas 5 11136 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11232 : Interval s5Atlas 5 11232 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11328 : Interval s5Atlas 5 11328 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 11355 := (concat (concat (concat (concat (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576))) (concat (concat bs5_5_672 (concat bs5_5_768 bs5_5_864)) (concat (concat bs5_5_960 bs5_5_1056) (concat bs5_5_1152 bs5_5_1248)))) (concat (concat (concat bs5_5_1344 (concat bs5_5_1440 bs5_5_1536)) (concat (concat bs5_5_1632 bs5_5_1728) (concat bs5_5_1824 bs5_5_1920))) (concat (concat (concat bs5_5_2016 bs5_5_2112) (concat bs5_5_2208 bs5_5_2304)) (concat (concat bs5_5_2400 bs5_5_2496) (concat bs5_5_2592 bs5_5_2688))))) (concat (concat (concat (concat bs5_5_2784 (concat bs5_5_2880 bs5_5_2976)) (concat (concat bs5_5_3072 bs5_5_3168) (concat bs5_5_3264 bs5_5_3360))) (concat (concat (concat bs5_5_3456 bs5_5_3552) (concat bs5_5_3648 bs5_5_3744)) (concat (concat bs5_5_3840 bs5_5_3936) (concat bs5_5_4032 bs5_5_4128)))) (concat (concat (concat bs5_5_4224 (concat bs5_5_4320 bs5_5_4416)) (concat (concat bs5_5_4512 bs5_5_4608) (concat bs5_5_4704 bs5_5_4800))) (concat (concat (concat bs5_5_4896 bs5_5_4992) (concat bs5_5_5088 bs5_5_5184)) (concat (concat bs5_5_5280 bs5_5_5376) (concat bs5_5_5472 bs5_5_5568)))))) (concat (concat (concat (concat (concat bs5_5_5664 (concat bs5_5_5760 bs5_5_5856)) (concat (concat bs5_5_5952 bs5_5_6048) (concat bs5_5_6144 bs5_5_6240))) (concat (concat (concat bs5_5_6336 bs5_5_6432) (concat bs5_5_6528 bs5_5_6624)) (concat (concat bs5_5_6720 bs5_5_6816) (concat bs5_5_6912 bs5_5_7008)))) (concat (concat (concat bs5_5_7104 (concat bs5_5_7200 bs5_5_7296)) (concat (concat bs5_5_7392 bs5_5_7488) (concat bs5_5_7584 bs5_5_7680))) (concat (concat (concat bs5_5_7776 bs5_5_7872) (concat bs5_5_7968 bs5_5_8064)) (concat (concat bs5_5_8160 bs5_5_8256) (concat bs5_5_8352 bs5_5_8448))))) (concat (concat (concat (concat bs5_5_8544 (concat bs5_5_8640 bs5_5_8736)) (concat (concat bs5_5_8832 bs5_5_8928) (concat bs5_5_9024 bs5_5_9120))) (concat (concat (concat bs5_5_9216 bs5_5_9312) (concat bs5_5_9408 bs5_5_9504)) (concat (concat bs5_5_9600 bs5_5_9696) (concat bs5_5_9792 bs5_5_9888)))) (concat (concat (concat bs5_5_9984 (concat bs5_5_10080 bs5_5_10176)) (concat (concat bs5_5_10272 bs5_5_10368) (concat bs5_5_10464 bs5_5_10560))) (concat (concat (concat bs5_5_10656 bs5_5_10752) (concat bs5_5_10848 bs5_5_10944)) (concat (concat bs5_5_11040 bs5_5_11136) (concat bs5_5_11232 bs5_5_11328)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_96 : Interval s5Atlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_192 : Interval s5Atlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_288 : Interval s5Atlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_384 : Interval s5Atlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_480 : Interval s5Atlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_576 : Interval s5Atlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_672 : Interval s5Atlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_768 : Interval s5Atlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_864 : Interval s5Atlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_960 : Interval s5Atlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1056 : Interval s5Atlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1152 : Interval s5Atlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1248 : Interval s5Atlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1344 : Interval s5Atlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1440 : Interval s5Atlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1536 : Interval s5Atlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1632 : Interval s5Atlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1728 : Interval s5Atlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1824 : Interval s5Atlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1920 : Interval s5Atlas 6 1920 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1947 := (concat (concat (concat (concat bs5_6_0 bs5_6_96) (concat bs5_6_192 (concat bs5_6_288 bs5_6_384))) (concat (concat bs5_6_480 bs5_6_576) (concat bs5_6_672 (concat bs5_6_768 bs5_6_864)))) (concat (concat (concat bs5_6_960 bs5_6_1056) (concat bs5_6_1152 (concat bs5_6_1248 bs5_6_1344))) (concat (concat bs5_6_1440 (concat bs5_6_1536 bs5_6_1632)) (concat bs5_6_1728 (concat bs5_6_1824 bs5_6_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 42 := bs5_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_8_0 : Interval s5Atlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_8 : Interval s5Atlas 8 0 1 := bs5_8_0
theorem alls5 : ∀ k ≤ 8, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
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
  · exact alls5_8 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 9 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0feeeeee0feeaeae0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 9 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37205.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.and,[2,7]⟩,⟨.and,[5,6]⟩,⟨.or,[2,7]⟩,⟨.or,[6,10]⟩,⟨.or,[9,10]⟩,⟨.and,[0,11]⟩,⟨.or,[1,8]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37205

open PEqualNP.Outside.L_meta_37205 in
theorem PEqualNP.Outside.L_meta_37205 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
