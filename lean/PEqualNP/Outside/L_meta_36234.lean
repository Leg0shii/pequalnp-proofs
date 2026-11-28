import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36234.Model
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


end PEqualNP.Outside.L_meta_36234.Model

namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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

def SBf (j : Nat) : Nat := [5, 5, 5, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36234

namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
  | 4 => 2*((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 2 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc22231451041240529272126048a690c26315c
  | 2 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 2 => 0xe07e07ffffffffe0f81ff0780fffffff9333ff
  | 3 => 0xff8007ffc1ffffff001fff800ffe0fffe3c38f
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60288e390990c24563c
  | 2 => 0x49108a4490a208a06a0a905124a322549130d5
  | 3 => 0x842554890d44954d04952b0249548ca962c30a
  | 4 => 0x1659e7122876de76b6c18a448e79c831fc03e0
  | 5 => 0x1861861c31871b98c719cc67006100c1dba800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafaaaf0a0f000faaafaaaf0a0f000faaafaaaf0a0f000faaafaaaf0a0f000faaafaaaf0a0f000faaafaaaf0a0f000faaafaaaf0a0f000faaafaaaf0a0f000, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
  | 4 => 2*((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffe03f03fc1ff07fffffff81e03e67fe67
  | 1 => 0xc07e07ffffffffe0ff83e0780fffffff9933ff
  | 3 => 0xff8007ffc003ffff0003ff800ffe003fe1c387
  | 4 => 0x7fffffc1ffffffc00000fffffc1fe03f8
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x451440238214440330146288e5912292225663
  | 1 => 0x93088a44944108a05481a85122a249a48930ad
  | 3 => 0xa2dd6890eda9d6d0c52db424b750539e1c386
  | 4 => 0x2c5165122890d656a95812048c599611760350
  | 5 => 0x3061861c30e31b98ce631c6700601821dda800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaacccc8800eeeeaaaacccc8800eeeeaaaacccc8800eeeeaaaacccc8800eeeeaaaacccc8800eeeeaaaacccc8800eeeeaaaacccc8800eeeeaaaacccc8800, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8817f53507dc85195f94732fd904417e53482fca9995f95330bf290436d52d07daa5a0cf95032bf28483fb40082fca1997d90510bc282857c50506fca820774c431b7a92217c5050afca3a15f95321bf280437e53c82faa9185b54831df21285ee52cc2fca218df94e20bfa8283f930842f8a098df94e21eea18877e528c2fca220df94a40bea9c433e540c6dca5a0df54e20beaa2217e530c37ea8885f54e42f6990417c54886faa5985f94c43bfa9c417f5150fbea690df95121fda02817e50d0efca1185f94a43bea96217d538caeea2995b94b30bfaa221ee42c82fea810df54630de2a241de324cbbc6518db149409eaa6615d53102faa6907ec4110fc282857d540cafea610ef10840bea88657c548c3de65195f54e40bda82857c548c6fca2085f94f41bf296637f52042faa610df55010bf2a0437e510c3f420085fd4f10bf2a0217e50883ea4210dfd5130bf29c83ed42483dc43107b54843bea8c217d5010aeaa2207b08620be29c437f54882fca8905f54f42faa08837e53903bc6418df54321bea9e817d50086fea9905f54a30fc20641ed4210bdaa4207790c43fb988437d549037885205f94442bf2a421ec524c6b8a690df94c40dfaa2417c54ccafaa021db14910bf280657d54c42fea0a1df94810be29a21ed428cbdaa418df55120bea86637e548cbdea4886f55330dea1085ee52d06f8a9196f10440bea9683f5310c77883205f94d10fd18421de304c3da4210df95110dea08837c54882f8a7105f94841eea1a617f52442fca5887d0c721bd28063ee320cbdc8410fb48020ef98c63ed32c86fca998df54831bea9083ed42c82fea6906fd0842aea98857f548caf8a0995f15130f7290817e53c86fca3215f94443df2a0637e5390bde851057d4d10bf29e81be42102faa2187750f32dfa18877d53c43eea2995f95032bea84437d52d037a8621df95020be29821ee21487de6410dfd4542bf2a0637d520c2f8a9086f90a40f7214437c52502fca2205f55121fb108437e52442faa718dfd4e21f6292815e5310a7aa818f7cc832bfa9e41ef4290afca118df94b30be2a2637d53d06f8a7085f94730fb88421df310c6fca190db54840bfaa243de434c2f8a790df14a10ef21e657c53506f8a2a15fd4f21bfa98217d53c82faa9987b8c820dea18817f50486faa1197b14910efa1a877d53042f8a998fe48020be28a41dd300c2f8a7906fd0441bf2a621f6104437e85217e90040fd884217e53042fca918dfd4532b7a92637d50d06bea690dfd5132bf28e417d52882f8a990fed0320beaa6637d51c82faa3105f14d20bea88817e50d06fea898df14910f7994437e528cafca9186f50d42bea94877e52842f8a6105fd5321bf288657d540c2f8a9905f55130b7290817e50886fca018dfd4941bf290657e52d06fca1a15e54031
  | 1 => 0xe500437e86207e94031fba0a83df308c3ba86997b50821ee99065bd435077e86a0fbc8020bf29c21f7318c7f4401077d0e43ef29881ec42082dca421df55221bf28c61df53442faa690dfd4520beaa6417d528c77c82a0f750e31bfa9a857f54c43d86410dfd4931dfa1c817d5190b7a87206f55031be2a0637c52c42fca690fb90842f6a1443f4514cbee6298df94c41bfa9a817e530c6fca310fb8cb21bea86657d544c6faa818dfd5010bf28c877e5290af8a2a05f55210bf290417f548c2faa121778c630fd98261ef4250adca418df94020bfaa421ec32886fca520df141439e2a2417c540c2faa4206fd0040bfa9287dc328c7f681207794f41fb18863bf4350afca020f750c31f721265bf43d0bda6490df54a40bea9e43bd43d0afaa6885fd4131be29a85dc318c2faa5087790f309e2a2217e544cafca320df54241bf29e217d52886f8a4085794c40ef980617c5150efca4205f15021be29a437d51d02e8a2995f54c40df20881f541c42f8a8196fd0240bfa8265f4310877a87a0d794f41bea8e61f710043b86418dfd5331be28a617c53503f260187b88420dfa1e836f52502fca2105fd4540f6108413f54482fca021ef90640bfa8a617d52d0fee6390df94842bfaa6657f52c42fca7a17790e31ae29a21de310c3ea82885f54031fca80637f53843bc86997d44010bfa92617d508c6fea918fe10020bea94837c54082fea8187bcc932bfaa063f721486fea690df54c42bf284817d5110efaa920df54243fc982217e540c27ca9985f54742bea9c216c524c6fca8985f55021be29287de430c6faa421df94c21beaa4637d52cc6faa7185f94c32bf28c81bf4390f7a80205f54643fd98461ee520c6fea5085f94c42be28243bc54443ee8320fe44010df21a87f940102faa399770c430ee29a437d53082faa720ef90140bf280817f53083baa7a0df94421be2a0217f53442daa5985f95320fd902417e520c6fca1085f94042beaa6657d500cafca121fbd0820aea9e837c53c43dc40906f95330bf28c41df328cbf460184fd5110be2a241bf41906f8a610fdc8621f6a1265f651102f8a4987b8ca20bea98837e5410efca5a05f15110bf28e87fa30442fca1214f55032bea8885ef524c6fca721fb94843deaa0657d54882faa4087754c42be2a2437d50106faa2105f94830be2a2657e5410afca6107bc8421f6990656d5210efaa8106f95032bf284657d50d0af8a9985f55232bfa8285ed52cc3bc6298dfd4940ee29a217e5210ef8a9885f55242f7a9281fb5050afaa921df94030ef298857e52d0efca898df94632faa88817e54882fea9985f94740f7212417e518c6eca2205f55321f790c437e54886fea910df54910bea8c81f641c42fea8907b8c921bf2a0837d544cbd885105fd5032be28a65ef20882fca518df14931eea9
  | 2 => 0x1d070000a000001b8000040300405044160000c01c010083000c0e00c000f4160593509c1334c00018040b4180d0000001015c2d2581b0e0160180422800004021341f0042604403070620000002c07028860002500c1c014160ec000780405c5401400070970f0130041227005000250340201c024087e0003a0281a0080400c001880160c05008032ec0d0200000c1441c02080500014a01000000010892a488170782b024500380a05c070300203c2b07446004410000d0281a04c010540700c4f0b40d088120140001802004021240007000130630b804030050087a094010ac010000600015094060ac000386d0dc130480802405000060040003c0403c070041b000040680c0241e00c1b0541d004000501e6b42c01400fb208837d51d0fba87985f94331bea8c657d50d0ef8a4a0dfd5020f6994417
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xe524425d6590c31d354e4210b2f54d49109b988544c26d62951319b189510c23e64d4b109758e54486e962103209b98a54c426c625464097d8d544873954940319e980530432c54909209798e548865c6550d309b98b540c71f54d4d108fd91534425e6514d219ed95100427561150209718d52442e5620c7218f99253482756115220cb552520c78d4350932cbd0d5210e3e6415031d914b314c71e5450f309ed95200831c5414d109dd95310c66e62d5310da549500c6b860508429798e544867761551308fd91508c6766115230b358c420832d4354b418f992534427b6055121c7590534874f53d49109dd85534826f6254343ab191200825d63153209758c548823d6494d1097d954310f1d53d08429e980538866f62544309ed8154482ad640ca219758e544c6746155130d314d324871d54cc832c7d5053443554314532ce951500c74d43548439b596420863f65508429b588540c67661152209d195414426d6214c108f191534429d63108409b18950d0e5d6395110ba181428866d6510820cb95252cc31d5350842cb150524434c528c5319e580538863d6414e21d590c514ca6e658c9218f990530874c53d49109b98853086776548421cb551320cb665294440d650d500c768605484097d8d510826f62540419718d5190a746155132cb95152cc26d65cc8218f191534823d6494c308f592538423d64148108fd954310f4e43548438f992544432d43548439b98854cc6776154d21cbd50524426e6214c109bd95210863d6414d21d354a320c76b42141429e580530873a42141429b195424832e5454831da54a500c66d6294d10ce50c5050b6a52540319798c54c82e86050932c7990534866d62153309758c540826d6294d209b588548427561d4e20b9185320ca6d658c8209718d544426d6294e10a758c429023e65151109b58a548c65f654c431cd152414426c6254643c798e540c66e6294e409798c548835a43540318fd91534827765440109798c540826e6215330d3d4c52442ac625004097d95300c23c64542319718d510826e6215020ce952500c65c6355121d594d511025e63953108f990530426d62152309b98a538423e6414f219b189534426e65149109b988540c27761551328f596540ca3e6494e108f990540ca5e6315032d394d52d066d62153319b588535065e6514d109758e548872e54948319798c520434e5394b419bd89508c74d43548318fd95411063e65151208f191508ca6e65909209758c540426f6548020c7551320cb5553544408f59053c825e63151208f592534823d64d4b10d314c524426e6214f109bd95320ca5f63551109b58b540c72c52901409d185534826c625513097d8d5190b4e53548409bd8954482e860509209e583540c66e6294d109b58a544871e5450c319d984540c25e6315021
  | 1 => 0x30200000030901000004480406070000002180000804040701c000400068002c010001e0304000041f0080000010100004000004c0002001080405010000a05030201c001f0001201010202a17000081e06ae58343102d4614c8329b98a544431e5350c408f191524423e6414d21da94a500c63f6454232b5586430c66d62d4e109798e534426f62551319b588540426d65d0820cb588544826d6214f109e980540c65e6394d21cdd0d51102e4614c9219bd89544c3c4320c4219b189508c6766115010d390d520c63f65500409ed81544c71e5350f418f992530c34d5394b41d394e521026c62551319798c54042e4614ca209e181544c74d5354840b9189310c65f63546409b988540c65d63d4a109798c54c876542145329758c544834c538c9218f992524423d6414c109b98854843596014d109758c540865e63d4a10cd546411032d52908409b58b54c42766195132ba580210835453c85219e983548866e629491097d95320ca9d640c8318f191500863d6494910ba1814210b2f43548409bd895190e5d6395310d354e521027960d52219d594310866c65509329e181544863e64148109e980540873561151109d584548c27965840109b98a548c6d9600c630d954951102e862500409e594400825c63546409bd89519026e62d53308f596540c7664214532cd50d511036852d01409758c54c871e63151208f99053c42b864480209b189544425d63148109e580540867960d5332b518d210863e6414c20d594e511036551084209ed81544cbaa4210320cb95142886e86050a329e580540c65f63549108fd91524433854c81209e980530872d548c8329ed95300c27561951328f99053c82e4614c820b918532c87a842100209b988548c33954540319b588540c31e63953309e195304423d6414f219b988540432d43548409b98a544c66e62d4e10cb55252cc2766115020d350d52cc36652544409bd954210ae86050b208fd91500874d6214d219798c54842cc63484219e181544cab960104409bd89534423d6414f109798e544423e6494e209b58a544426e6214d418f9905388758538c1109d987538834e534ca209b588544c26d62953109b18950107555394440cbd0d52d071d63151209b988540cacd6310a20d5544310c3646154831cb152204827b65500408f590530832d5454b309b58b54cc3c6320c721d314e214874e4354b309b58a5390277655044197195434cb4d5354b419798c540c27a60d50319758c548432c54d49109d584530829d640ca319758e524426f6254d21d354d4210acc624c4319d584540c32c5450920ab590320866d650c8218f592538827a60d53329b195324873b4314142d58c8514ca766114c20c7153534436732145329bd89544436552944408f992544832d5454831ba181420863d6414c219798
  | 2 => 0x20006800070102800030000c04000084c0a0d000200a000000008020307408190000d1a00059c002010000014b207008000c00004011400000060212000080000000060500024040000004020b0e0100a0000800340020014000000020120a020183e000b5103a0b1a8141a380002cde370081c14040402400000080012041683c0096018042c0f018003a1006000080000008200206800260279854160007000140002000281
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x600010102000820090b435d2534ca20a88e4a88621850d7315142483142a0c0a1241615d0320c421c8ca630a651062554185320cb152a0c0a14438358d6215120e0a86a10a2994a87458021082b03828428a65511cd5108420950e4b0082204a8725834310286ba0a699243435ce5450a21988e4b0c8618d89731084008344a18c0a12659114c614c921c92a63028421619531814210b0aaa0c299065835916214d21
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1b000a09839506050a21a09831506050920a058494c614ca20a058414c614c921d01431c14214532
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s3K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/226+packedAt s3K5 (16632+(h % 226)*10) 10) % 616)
  | 4 => 2*((h/222+packedAt s3K4 (15732+(h % 222)*9) 9) % 414)
  | 3 => 2*((h/15+packedAt s3K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/15+packedAt s3K2 (300+(h % 15)*3) 3) % 5)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffc07ff0fc1ff0ff87ffff0fe03a63f3e7
  | 1 => 0xf01f87ff83ffffe0ff0ff8701ff0fffd9ccc7f
  | 2 => 0xffe007fffc00ffff000fff801fff003e1f0f87
  | 4 => 0x7ffffff07fffff000001fffffc7e00ff8
  | 5 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x614500470821100330118091cb0122882151e3
  | 1 => 0x24c20889194040a051068822451049908cc42d
  | 2 => 0xc28b551230eaa56d088b550496aa0526170e86
  | 4 => 0x8b14662442883656aaa0440918cc9607600b50
  | 5 => 0xc184438630cc798cccc664e00881807daa000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa417c5150aeca3987754c41be29a417f53506fca8995f94c40be2a241bd4210afaa7885f54b30fa908437e52d06faa121df54831bfaa4217d53906faa1215fd5230bea80877f54c42faa4205fd4532bea96217c51503eea2a05f95121ef18a637d5290ff0a0a0df95110bf28c657e520c7b8a690df54331df2a0657e508cbbe86a1df14941bf28e857d51083ec8298fec4110bea9a43ef4290afaa518df14940fb288817651102fca7a0df94231beaa4637e52cc7ea8318df94c32beaa2617d510c2fea4887d54730bfa82857f52502fca320df95020fba0a83f641c86fca4106f50f41bc282837e5190afca221fed4141f7908437e528c2fca9885f95320ee990657d53082fea8905754c40fb98a63df4390efca820df54730bea9a21bf43d06faa8195f94c31bf290875f534867aa8197dd0410bea96816e52102faa3a06fd0a42bea90837d540c6fca4187d94730bf294837e50107de64997754c40bea8c65fa30882fca1105f14141bfa8a61fa30482f8a990df54742dfa0c837e5190efca521df94c21bf28485bc41903f440105f95043fa98c213d540c6faa6207750d31f7210857d53c877aa8195f54440bf28e617d548c3b864185f54720de214817f53842faa610fb94840bea96877e540ca7ca8197bcca32fa98863f641442fea9985f94420df21285bf43102fea2a06f55330bea8865de328c2fca1a1ef15120bf284817e53842fca420fed0140fb18c21f721842fea5085e54032fd902417d53882fea9996fd5120be29e417e511067aa9985f14f10bf2a2637d52443ba87987bc8220f699065ed20082fea098df55330fb18863f431c86f8a9885f95040be2a463f4514cb7c82205f15121fc900417c514cbf641105f94f40f6908437e54c86f8a6107b8c832f6194437e521037e80207b50b20bf28085f65110ff280205f94a10ee988637e5310afca2195f95331bf288637d50886fca1a17750d30beaa6217d53482faa321efd0d41bfaa6437c53886fea4a0dfd4f21bf28e657d54902fca690df55243beaa4417d5190afea4085fd5132be2a0617d54ccb7aa818fd50531be2a443de43cc2fea690fdcc631faa0e43f5318877c85205754f42baa8887f731c86faa5185f55020be29a21bd43102fea998f750f31af298837e50043ec83886fd0e43ef21a61ef32887ec20885dd4520bf288617e530c2faa990df14c10af29e857c5050efca918df95332be282657c548c2fea610df94720dea00817e518c6fca3205754c41bfaa2217e52d02faa718fd4c410bea96637d52882f8a790dfd4132bfa9a81fa300c3be6218df14d41b6292637e51103ec8220f790f31be28a877d51d0efca7905f54e309faa221f631486fea710efd0f42be2a063f531486faa7905f54341be2a0657e5010ef8a8105f54e32bfaa4637e50083f66098770ca30
  | 1 => 0xe52086faa9085f94b43dfa1a85f721486fea9906f10840bea8085f441842fca010d7d4d20fb884217d50907be6318df15232bf284437d518c3f680087d8c621be2a6637d52042faa018df95042bea9c817e50906fca8185f15110bf2a4217451502fea7885fd4943fc98241df53486faa9215f94c20bea98217c54843f080085fd4143be2a6617e540877c86a1f7cc832faa0a217c504c7f4a0195f55241bf298877e53442fea9194f15110be29c4177514cbdc40905fd4542dea18877f54887eaa3a17d54432fc984417d52902dea498fb0c821fba8a417d50d0bbc87195d14520bf28c417c524c3bca7a16f90541fb20843de320c6fca9985fd4d42bea8e655c53486faa190df54c42bea98837c54c82fca620df14e10bea94437e53902fea8105f94210bea8c21f510042faa5a0df94a42f7216417e540c6f8a898df54620bfa9e41f840c42f8a2985f94a31bfaa2437d50d0efea80877cc030bf28e81bd43d0bda84905d94742eea9e85fb40c42fca210fd94432bfaa065de328c6f8a4885f94832bf29e857d5110afea810df54e42faa0e217f540c7de6410ef50d41fd080217e530427ca9985f95130dea1a857e518c2faa7a07750c43ee980617d54042fca7216f50441bfa9821765110ef8a498efd0c43efa9a417c50486fea6107d14540fd98461bf54442f8a5885f94910bfaa441f421843bc8621dfd4d10bf284617c54086f8a9997d50441fb880217d54c82faa5087bd0942ae29a413e540c77e8220df94410bea88877f53482f8a9105fd4930ba28a65f431086fca121f7cca32bfa8243fa40102faa998dfd4520f6292637e50ccbf681205d54742fba0c837c54043f621085f94331bf286437f544c37ca9986fd0e40bfa92637c52842f6a0a0dfd5131beaa061f451482faa1995f54843f7900417e53883e882085f54232bfa9c417e5110bde4310df94b10df202817a500cafca6905f95230ef192657d50106fca0205f94f21be282857e548cafea5887e4c030ef21a637d52906faa890df94e43eea18657d500caf8a690fdcc421de208817e53906faa3205f95221ef298817c53086faa8887bd4931bf28e877e53886fea8185f95120beaa4657c544c2fca4216f90640bfa82837e528cb7e81207b54840f6a10857d508c6fca1a0fdd0610bea80437e54882eea2a077cc230faa08436d52102faa810fd54440df2a06375510caeaa2205f94031df21081bd4390278a890770c831bf28065de430cbbc60985d54730ef190617e53c43ec8318df55131af29881f910042f8a4085f94621bb28865ee21486faa7a0df14943de2a2217d520c3eca3a15f95010ef29883dc328c6f8a6a07714d20faa8887f421042fca0185f55132beaa4437d538867ea8905f15132fb10843f9500cafaa7a15f94b30beaa241bf4210bdc84907dd4532be28
  | 2 => 0x190083c004050001b0a41528c07000160480900c05010053c019060330000218015028242481b0187c0001a00000084e00d4048600905c0f1cc0344c0205c050004504400001c40082302c001a40105c010008c1dc275d80802c0c0241a0d8031d87e004000000109000054002780a00075000020480d028000001c070000800200c2000813000050c8d2000070dca7020220d008000024cc0000c000403f008015244500ccc0000003c000a00004815020000000920005000733c807000000140b300010300113808108500707406c0200c060241802c0353c1a00806008400360c02c8e0600004800000020080900c08005241646c004064b802004210143f09400010110000a020ec0018a0b80901002fb90821f721886fca5207d8c410be29a857f5150efca4085f54e10eea1c657
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd544867561d53209d996314865e6315031cdd0d5110e6d6295131c7d5353483345484110d594d511023d6494e109758c548873454d45209d586534825d6395321c7552320c73754145209d594210426e62d4e108f191508ca5d6315220ae580421026f6254d21d914a414c7545314520c7590534874d53548409d98754cc25e6394d21cd95151cc23d64949109e594400427761551109bd89544c27561951209ed81544425e6514d209798c544427b6550040d590d510cb7151540329798e544863d6494d109d98753882796015021dc945500ca5e63150219d984548c23c6454d10c754d41106e4624c6218fd91534827661150309d19541443b041100108fd95401035453c85218f99053042756195232d594d318423e6414e21b5185320cb3954940329e980530823e6415032d3548320c23d6595032d554e51102776154d208f99053c431d544c4318f992534427661153308fd91534429d6310640cd55151cc33a54940329d586538827761542329798f52c42776550441c794d431031d6315110d594e51d0a6d62150308f59352c43655208410b358a430cb5643547309ed95200823c6454d208f59053c865c63548108f992538426e62150309bd89534427960d50329e596100425e63951209d185544c25e6315220ad590310863f65508429d584540833454905109d9845350a3e6515110d9949511023e65151209d185544825f654c431b918931043555354742b9185320cb3454145209d58453082e4624c5218f19150087c4320c4219d98453c823e6494e209d584548827960150329dd95100434e5394840a758c411025d6315310bc5802104354534c521cd50d511023c6454231c7153534836732145329758c520425d63d4b109d195314865f6354910bc18141c42d563104109d984540ca5e6395321d514e314875643544439bd95210867a60d53319d594410423e6414f20d390c524c675650c4219758f528437251940329798e534826f6550842cb15242482766194d208f992544827b60551319d996414427761551309b988540826d62150109d596310431f5414d209dd85529027561953209dd855010af060504419d584540cb1e63950329d986548ca5d6315010cb54a42102cc624c4319798e54c823e6414d218f990540c63d6414c21bc181410863d6595031b318d210867561951329d987540cae5610ca21d614e304825d6315020cd551510cb3b4314141ad191100433654944328f191524423d641481097596430cb3854c41109b18953442746154a40cd552510ca7a6015032d594e51103655254440d354e521027b6055121d314e214875a43540329e181544863e64148109d58453c82b5640c7219d586544873743544409d58454cc37341141418fd91508c65f63548108f992524426f6548020d394d521025e6315310
  | 1 => 0x44700c00271f8040c100e010122f0342000190200400060000416030004c027400000da3100000000500000ac020381c2805658400e000400c22000600c220c028007e040d100009200800000c1180042b89dd85534863e6414f218f99352c426e6215230d554d511027a6015021d58c8514ca766114c2197d8d529037151940328f590530831e639533097d95320ca756114d429b588548425d6315110cd50d51d0a3e6414c209798c540826d62d4e109798c548427661951329b988548427661150109d586539031c5414d209d1855290e5c63549109b195424827761543439d18550d0e7661d5320c794d43d0ad5610ca319798c54042766114c20d914b314c6b960d0c409d597410425d639532097994534866f654c8329d584548c36452505319d98654c823e6494c308fd95411067465505319d984540831d53d0441c799053486796014c21d5d4f514826d6214c109718d5448677654c4319758c540867b654c0309d586534427661151309b5943208735544c4319718d529026d62152309b98854042776155132d550d510ca5e63152219718d529075553504419758e54482766195120e550d414c6746154830cd552310c6f06050721d554e51d0b7051d01408fd91508ca7b6544010c798c544423d6494d20bc181414433654507219d185508ca3d6414c108f592530c2776155120d994a511033a5454032d594d51d0b556114d2197d95300c23e6414c21cd584544426c6255130ec90440c4339545403297195434c67461551329e58053c86746154d2097d8d52906f16110310d350c524c63d6414f109718d544833654947309dd855290f2d43548409ed81544ca3f64549109b98a544c73451901408fd954310e7761549109d986539027a60d53219d587538825d6395121cd151414433754d4520c795143cc27a6014c219e19530482e4624c61097195434c32d62151209dd85520c3554354443cd50d5110ed563106109798c52042b86050441d550d51cc25f6550c439d587540ca3d6414d21ae19110042d9600ca309758e544cb6552944409d584544c23e6495110cd55251cc33743547429d984540c7c4328c621b518d21086f06150040ce904505067561d53309e181544ca5e63d4a109b988530435753145209e181544c67a60d50329d98454882766194e209758c548423d6414e219b189544c63d6414f209dd95210865f6355120d514f514827661153328f992534827565cc4218fd9150086746154042bc181418c6b461500409bd89544c7596014d20cd546411027565904218f59253883656114931dc181511027561153329e98053c872f43548409e58354c86f06050531d314a314c75943540329d584540c31e5450c32cd951510cb394314141d554e411071d540c8319e58354cc71d54cc431b9189310c65e631503097d8
  | 2 => 0x5874001f0009c1e0310938040400010525202010106c0d0187c430a8006c062281004010080400050000c3e27000000a0007000061c0f8040856000480c0c2d00856031a00c16010007802090001804ad0400000090002c000300008000000808121a1a84c0c19420240059050000e3a01801b00102338000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x20214010140009c200000048c000000000438c9506050721988e2b14861962554189310c748a18c0a0a632c1d16008410a2ae829a6290e30541814144342b2064188432c1c560d0c40960e2b0084205917310440042a238aa419061455d2534c610ca2a63028220e46531893184382a18a4a0a63511cd5208410c1aa83126218d157395141c868ab98a8a0a218654c6050441c2ac6b08a888615645845348722298c498a43981486050531
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x18000018000000000a11831506050510e01431486050531a11839506050721a058494c624c610a058414c624c521
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s4K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/219+packedAt s4K5 (16632+(h % 219)*10) 10) % 616)
  | 4 => 2*((h/180+packedAt s4K4 (15732+(h % 180)*9) 9) % 414)
  | 3 => 2*((h/29+packedAt s4K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/22+packedAt s4K2 (300+(h % 22)*3) 3) % 5)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffc07e1ffc1e1fff87ffff0e03f8e3f33f
  | 1 => 0xf03f87ff801fffe01f0ff8f01ff003fc9ccc3f
  | 2 => 0xffc007ffffe0ffffe00fff001ffffc3f1f0fc7
  | 3 => 0x7ffffff07fffff000001fffffc7e00ff8
  | 5 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x628500470422100603118111cb02284821531b
  | 1 => 0xa58a4c891d4c64e10d86c8a2559052948ccc2d
  | 2 => 0x411311122806812a200b120486249821170546
  | 3 => 0x8a2c66245110365556a0408918c96306e00ab0
  | 5 => 0xc3044386198c79998cc64ce00818207daa000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfaeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6837f524c2fca1a15fd5330fd882217f54086faa818df54a31fd080217f53503bc60986f55032ef98061fa300c2fca110774c030bc28265bf43d0afaa8905f14d41f7994657e51042fea9885f94440dea1c837f52042faa418f750f31bf28487f9404c27ca998de54032bf29e417c54886fea898fd4c621bf29887f451503ec4210df54b41fca06417f54c82f6a090df55330faa08837d51843eea2a05754c40bea9e217f544c2fca1196f90841efa1a877d50086faa5206f50c41bea8c657e540ca78a890fd48421bf296217f514cbec6218ef90d43fc980217d50d06faa920df94810faa8865ed52107f481085f14142be2a2217e5310afaa021df94321bfa98437f504c7f640085fd4d41be29c417f52443ee820877cc832af298836c524c2faa2205f15220bfa9a43ef32882f8a818df55131df20281df328caf8a8905f94a30f721085ed21087f281185f54841bfaa465ed42c86f8a9905f54d10bf2a2637e544cb7e8320f78c932bf2a2217c53886f8a8985e94041be2a4217e53082fca7215fd4f20be282877e53902fca4185f54a41bd28065fa30042faa0195fd4e20bf29e21fa40c83f480987ed4132bfaa2417c514c3dc4290df15010fb082217d54c43f0a090df14132bf28c637e53d027ea8885f54840bf280857e531077a80204f55030bf29043ed20082fca020dfd5221bf29c877e52442faa610efd0842bf288877d5110eb8a690df94b40bfa9e43fb10842fca3995f94730ba28a817d508cbe883086fd0441be29421bf43d02bca6207dc4210aea9883de53106fea0a1de94043bf286877d54ccafea8085f14f20be298437f54c86faa8087e54331fc900417f50486f8a6885f55320bf2a0217e5110ab8a6905fd5032bda8283bf43906eea2a05f14520bf28e817d510c27ea890dfd4c10fc18041fa408c3bca7a15f14910bf28e417d51882faa3905d94432bea84437f5150afaa8987b0c820dfa1a85f631486f8a8105f94c40bf28c85f741906f8a990df54a20bea8c877e54ccaf6a0995f14e10beaa6637950106fca4215f94a41bea9c83ef524c2f8a6a15f54e40bf280657c524c2f8a690dfd4c20beaa4877e528437e8620df94231dfa1c877e520cafaa7215f94010fd280837e50886fca610df54b31fd980417e528cafaa1217e4c310be29821ef20082f8a81957d4d20ef298817e510c2faa3217bcc932fd906217d508c7de84a15f94630be29a417e548437ea8885f14931dfa0481de328c7f440105fd4520bf29e837d531037c84a15794f42bea9885dc328c6faa3a1df94c30bf2a0617c52c42dca420f754c40dea10857d54486fca3205f54e30bf2a243be419037ca8197b4c832fca80657e50906faa620df94341fba0a837e520827aa8197790e32bf29a43fa50cc77a8621df94b43bea9c637850486fca790dfd5030
  | 1 => 0xc54486faa5a1fdcc631bea9a437e54106faa8997e8c310be29841de43cc3da8490fed0140be2a4637f53483bc6298ef10a41fca8087de434c2faa990fd4c431de20c817c504c7f280105f55110ef218877d52886fca1185fd4d42be292877e51087788420dfd4941baa88657f53443f280205fd4142bea80837e53d0bbaa620df94030be2a2637d51d02fea7087790d31be29021dd53d0afca9885f54a10dfa0081fb40042f8a9985f95331bf28e877c51502fca2105f55232fb880217f51502fca9185f94632fca8685de320c6faa1a1dfd4b10bea9e433c54442faa399770c831f7190657f504cafea4a05f94031fca80837d53c83f260905f54241bea9c417d50ccafca618ef95030fca0221f441043ea20085e54331be2a6637e53906fca5217e10010df208817d53886fea7885f54b30bfa8a877d5090ff4a0195f14f10f629261f721486faa9087bcc820fd286857e51887f6a0a0df55240bf288657e5410efaa39877cc631fc100217e53442fea9086f50d40bfa9c437d53d07dca420df95130bfa92877e540c6fca9986f10440bf294637c548cbf681205fd5132bea9821f910042fca1085f94e21bc282835d53d0afea8105f54843bf290837e53042f2a1a17790f31ee988637f54443f640905f55030efa9a437e51882faa7195f54321bea8085ee20482fca8217e90040bf29865f850506f4a198fbc8421dfa14857f52842fea818df14121dfa18877d52042fca418df15021efa1c87bd43d0bb8a6905bd4930bf2a043f641106fca7107b50842bf2a0417d54082faa3185f54420be29281fa40083d865105f94840bf2a4657a50d0afaa6107750e32bf29a41fb50487ee83085f54742fb90c435f53486f8a9885f94b30bf29481dd430cbf480885f94240fd982617e5010378a890df94332bfaa243bc54442f8a2996f95331fd182417e51906fca89077d4d20bea9e85dd43cc2fea918fecc320bea8063be42906fca1215fd4931bf2a643dd434c2fca8205f14f21f790c43bd54cc6faa2195f94021eea18877e53843f4a021fe4c220bf28883ee42486faa198fd4c521bea88857c544cbde41107ed0310fc98061df310c6f8a2a15f55021fd904417c52506f8a8187750d31beaa0657d53d03eca2195b54841bfaa4617d548c2fca3a15f55231dfaa2437d52c42faa910770c830ef190617c535037c82a0fe14132bf290877d520c37aa8184f95032be2a6657e548c6fca521dfd5331bfa8a61fb308c2f8a0a0df54a43fc206217c5150ff061904f95030beaa4437d50d0bba64195e54043bf2a4437e54c82faa5a05f54640ef194617d528c3de85215f95220bfaa441bd43d03f041887dcc531bea9c217e5190f7a8220fe50210ef98461bf43503f461105f94b31ee29a43dc328c2faa9216f50d42bea92213d54cc6fca198df94431bf29
  | 2 => 0x608d099b32180600001000061a4020800600000000000000b16403004cf24c01024010000c02c0403c020340c6d0000102f0e0001c400044000145203c000140706c620000f0a00500001000012241804c00005bb0501206c0000c2306000254ee0b12f248160040f00c0d008000006f0002f000010d837000001b40902c0a02c730880402c1f00809038070203d0105103c1d034020f02204c0200404084180001f0700813435000250500b0000402c020000102c23014510000400c000142317400348010a80006000004008b00702004000010c401030125cc007fc41008050343a21002000090940700175018000042503c0801474030000cc3500c3b000970c40400d3400c00000000000303010234040c45a0000b26437bf28041de430cbec6310fb90b21bea9a417c548c2fea0a0df94043bfaa6657
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8300825e6315010d354e52106b56110841d354d521067860546329798c540c23d6414f20cb152424875643544329ed8151d0f6852901309e980540435b5314121dc945500cb1e5450c32ce952500ca7960d53319dd95411065e6394d209e580544c65f6354910bc18540c834e539484197d8d529032d621512197d95320ca7b60544428f590530863e6414c10da54950106d963100108f99052042786054743c754f401031e5450f319758e54c865c6550d309ed8154443596014d209ed81544c66f62551308f590538825e63d4a10ce55250cc75b53d41218f990538825f63548109d984530873a5454331cb50d521073960151109dd85544827b6054831d5584534867a60152219e982544866e62150109b195424866e6214c10cd152104425d63151109d584540833451901408f992544435a32141329e98354cc6b864440109e594400427a60d5032b5584328c76a52540419dd9510042e8624c220ba189304825e6395120c798e54cc65d6315021b318d2008279658c0109798e54c827a60953219b588548c6e8624c310d614e30482b960106409798c540c63d65950329b988540867860548318f590538433954540329798e544873b4354342ae59030c823d6494910cd551510ca7661d5032d690d50cc76852501308fd91518cb5943543318f191518ca5d6395320dc545500ca3e6414c218f99053c827561d53309d58453082786054d219b189544c31d544c0309dd95210867a65901109d19531486f061501309718d529026f65484219e58053c865d639512097d95310c66f6254d208f191518c34d43149308f9925348759535434297994534831d6414d20bc584200427a60d4e21ba181320ca7a60952329ed95200827960152318f992530c76a52940419718d529063f65504419e980530863e6414e10cb54a421067a6014c209d98453c826e62d4f109758c548865f654c030ce904505065c63549109d984540826c6255131d514e314866f654c8329b58a544c25f6550c43d390c524c33954543319e583538867b6054a418fd954210a5e63953219e58054cc67a6095132bc185400823e6414f218f593528427461551209ed95100427661d53209e58254c876960149309e98253907695208010ce951500ca7b6054a439d185544c2796014d429bd8953442796014c219e18154486796094d21d650d500ca5e63151108f990540c31d53104408f990540cacd6290c32d690d500ca756114f209758c5404339544c030dc580515036952940419ed81518ca7960d50328fd91510823e6494d109e582538867960951329758e544ca3e6414c20d314a304c35953540418f59053c867b654c030cdd0c515033943543429e58054ccb1e63950329bd89544c6796094d109bd95200831c5414d2197d8d529067a6094e21dacc8504ca5c6355121
  | 1 => 0x2008380400018144604108143400368091a1c06819420a06814060b030043413762580a0c0913cde5a34002aa010f1d0000c008081402080340a050003800930081006000082400004d05caa00118008c0c9b594320827a6015332dc147405025e6315020bc18141106e9600ca20d694d50107594354043c7d50534863c6454420d654e40103c8328c2208f99053483354314540c794d431075853c81209e580540ca3e64d4a10c754e411027a6094d21ced0d5010677654c431c758c544425e6394d21ec104400427865501309b98a544c23f6550c439ed95401025c6550d319d59441042766114c209758c52042e8624c0108f59253c425d63d4b10bc18540102796095120ce152404426f65508429e597400426d6215310bc185408c25d6395121ae590300827b6055121ce95250cc67960152219e980540c23c6454910ce50d50106d9600ca309b988540c63d6494c31cd552510ca3e64951218f590520435853141219dd85544435a534c3109e181544c67761551329e582544867965cc0209e980544c6796015021bc5804184278654c1208f994544865e63153108fd9540102786550110d614f504876852cc130c7550320c25e631522097d8d54486b561d0c419758c548823d6494e21d690d5010e7a6014f21ce150504867965840109e181529063d6494d10c7153534863e651511097994534863e6494910d694d50d0b5a53943429e980540865d63152109e996304826d62d4f109758c540823d6494d219e980540cb3b5414121bc185408425d6590c32b658c40c427a6015231c7553300c27b6055132d550d510ca3d6595030ce95140c8358534c120ad185401033b54d41219e980540c67b6054d20b3189300c27960150319798c52042796508010dc946500ca5d6315310d654d40102796094e418f590530834e5354841c798c544433654944329798f52c425d63d4a108f191534433854c4110c794d43d0a7a60153319ed81524425e63152219d984540ca3f6454630bc185404426d6215031cbd0d52106786054a439e58354c875a53940419dd85544c25f6355120ce15140442746155132ae181411067661d5330ce552300c31d53500409b588530427b6054d218f992538863d6414c109b588540427561d53209798c54843394354043ec106408426c6254d10ba189300c2d8604c8328fd91534867561150328fd91534435953940419b988548c63d6414d20ad191100433954940329d587540ca7a60d53218f99253c433854d4121c7552320c31f54d4d21e650d404c2786055132d314e20482796590020dc546500cb4d520c8319e9805350a3c6454d21c799053482d86348020ced0d5010e5e63150219718d544837341141419718d520435953943429b98854c433654544329e594300827860544428fd9152442796095232f20c
  | 2 => 0x405228700807020e8662a0007444000100000520f8481c03315794c5a0185800020400c00070f0084621000700016000041802030484a0021800089c00028005b078000601024d40001001b400070400c020003800880000020740100056fc0f0030c0000070c8120
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb80007808013862900ba458c4110010960e0b0e8620e485318930482a4382a419063465cc5450110a32e829a60904b070584421068cb9ca8a06418554c6150040cc0a430a80985487354820043182a0c2a0221321c16290c32e128629280986196458053483192a0c2a0641465d2534c310ca2a630a802060d54189300c348a18c2a02619294c624c310c32c6b00a888689640c83008314aa0c4980612c1d16108010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x400080a11831506150110a098494c624c310a11839506150320a098414c624c120e01431486150130
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/226+packedAt s5K5 (16632+(h % 226)*10) 10) % 616)
  | 4 => 2*((h/166+packedAt s5K4 (15732+(h % 166)*9) 9) % 414)
  | 3 => 2*((h/15+packedAt s5K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ff87c0fe1ffc3e1f0f8ff01f1e03fc87c33f
  | 1 => 0xf83fffff001fffc01ffff0ffffe003f8f8fc3f
  | 2 => 0xffc007ffffe0ffffe00fff001ffffc3f1f0fc7
  | 3 => 0x7ffffff07fffff000001fffffc7e00ff8
  | 4 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xb2854c4e252a540f0b8589924b122a4c83c31b
  | 1 => 0x518a00821c4420c005129021d5205090285c2d
  | 2 => 0x2113111448068152200b2204864498211d0546
  | 3 => 0x462c6628911036a556a0088918996306e00ab0
  | 4 => 0x84304430e198c73998cc4cce00118207d6a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880fcecf880, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q1K4 : Nat → Nat
  | 0 => 0x20000000222fa40f641ee32ed42cd32dd32f940ed32ee42f541df32de43dd43
  | _ => 0
def q1K3 : Nat → Nat
  | 0 => 0x1004c001c5038a64a0f24c940a6a9c85b1415029aa7196a50940e4994814f544cb3286a06950941a6aa26595435069aa521f14ca41
  | _ => 0
def q1K2 : Nat → Nat
  | 0 => 0x3813250540a15913250689644c940
  | _ => 0
def q1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 14
  | 2 => 3
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
  | 4 => 2*((h/11+packedAt q1K4 (208+(h % 11)*4) 4) % 13)
  | 3 => 2*((h/11+packedAt q1K3 (378+(h % 11)*4) 4) % 14)
  | 2 => 2*((h/8+packedAt q1K2 (114+(h % 8)*2) 2) % 3)
  | _ => 0
def q1Pos : Nat → Bits
  | 1 => 0xfd33cf6f8ee63988ef73cf430cd08fcf9c24cf
  | 2 => 0xfe3cf3b7f0f83e0f0fbcf38c30e0f1f3e44b33
  | 3 => 0xbfc0fc3aff003ff00fc0fcf03f00fe03fa8c3c
  | 4 => 0x3fff003cffffc0000fff00ffc000fffc030fc0
  | 5 => 0xffffffc0fffffffff00000ffffff000003f000
  | _ => 0
def q1Neg : Nat → Bits
  | 1 => 0x4441010022048110104100104410240802045
  | 2 => 0x8810408104090202201040410821081004112
  | 3 => 0x502a81c5a4152502542a81d0aa04a42a528c28
  | 4 => 0xe020aac3c89405449820aaea8208c928530e80
  | 5 => 0x0
  | _ => 0
def q1Atlas : Atlas := ⟨5,rawDecor 62 q1Pos q1Neg, 0xfffffffffcfcfcc0fffffffffcfcfcc0fffffffffcfcfcc0fffffffffcfcfcc0fffffffffcfcfcc0fffffffffcfcfcc0fffffffffcfcfcc0fffffffffcfcfcc0, q1N, q1R, (fun _ _ => 0), q1I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q3K4 : Nat → Nat
  | 0 => 0x707900300fa30f531ed42f930ad42bf42ed32bd42ee42f631bf43bd43ee32
  | _ => 0
def q3K3 : Nat → Nat
  | 0 => 0x400000013025aa9196a50a30d2a1463c5324c7528498744c530cca1a612d5490a5aa8994b54b43e499261a5424c65ea6a16550d31
  | _ => 0
def q3K2 : Nat → Nat
  | 0 => 0x100285644c931a2591324c381424c530
  | _ => 0
def q3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 14
  | 2 => 3
  | _ => 0
def q3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q3K5 (i*5) 5
  | 4 => packedAt q3K4 (i*16) 16
  | 3 => packedAt q3K3 (i*27) 27
  | 2 => packedAt q3K2 (i*38) 38
  | _ => 0
def q3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q3K4 (208+(h % 11)*4) 4) % 13)
  | 3 => 2*((h/11+packedAt q3K3 (378+(h % 11)*4) 4) % 14)
  | 2 => 2*((h/8+packedAt q3K2 (114+(h % 8)*2) 2) % 3)
  | _ => 0
def q3Pos : Nat → Bits
  | 0 => 0xfd33bcf78ee63dcf988ecf4323f333439c4c8f
  | 2 => 0xfe3cdf3bf0f83ef3e0f0f38c3c7cc383e4b133
  | 3 => 0xbfc0efc2ff003f03ff00fcf03f80fc03fac23c
  | 4 => 0xffff0ffcffffc003ffff00ffc000fffc0303c0
  | 5 => 0x3ffff000fffffffc000000ffffff000003fc00
  | _ => 0
def q3Neg : Nat → Bits
  | 0 => 0x4444100022044108110100100901104800485
  | 2 => 0x8812040104088050202040404204209001112
  | 3 => 0x502a181da41510aa502581d0a90aa81252c228
  | 4 => 0x0
  | 5 => 0xe0200aafc89420805449aaeab24a082053e800
  | _ => 0
def q3Atlas : Atlas := ⟨5,rawDecor 61 q3Pos q3Neg, 0xfffffafafffffaa0fffffafafffffaa0fffffafafffffaa0fffffafafffffaa0fffffafafffffaa0fffffafafffffaa0fffffafafffffaa0fffffafafffffaa0, q3N, q3R, (fun _ _ => 0), q3I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q5K4 : Nat → Nat
  | 0 => 0x1008024300bf43f920de43bd43dd439d43bf42dd32bd42f521f621fa20df32
  | _ => 0
def q5K3 : Nat → Nat
  | 0 => 0x1640000263ea4a1e550e21d4a1241c5324873286907848520d2a12431d544cb2a8690f24c9208eaa48799438823aa9994754f42
  | _ => 0
def q5K2 : Nat → Nat
  | 0 => 0x285644c921a259132483814348520
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 14
  | 2 => 3
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q5K5 (i*5) 5
  | 4 => packedAt q5K4 (i*16) 16
  | 3 => packedAt q5K3 (i*27) 27
  | 2 => packedAt q5K2 (i*38) 38
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q5K4 (208+(h % 11)*4) 4) % 13)
  | 3 => 2*((h/11+packedAt q5K3 (378+(h % 11)*4) 4) % 14)
  | 2 => 2*((h/8+packedAt q5K2 (114+(h % 8)*2) 2) % 3)
  | _ => 0
def q5Pos : Nat → Bits
  | 0 => 0xfd2e7cfb8ef798cf98ce3b48e673339e848c6b
  | 1 => 0xfe379f3df0fbe0f3e0f3c38f187cc3e7053193
  | 3 => 0xffc7efdeff03ff03ff03fcf01f80fc07fa421c
  | 4 => 0xbff80fe0fffc0003fffc00ffe000fff80383e0
  | 5 => 0x3ffff000fffffffc000000ffffff000003fc00
  | _ => 0
def q5Neg : Nat → Bits
  | 0 => 0x4508100021081108110400022101082080429
  | 1 => 0x8882040102102050204080108204104101092
  | 3 => 0x0
  | 4 => 0x5005580fa44054aa508095da410aaa50238340
  | 5 => 0xe0040ab7c882508054a926ec954a085043e800
  | _ => 0
def q5Atlas : Atlas := ⟨5,rawDecor 59 q5Pos q5Neg, 0xffeeffeeffeeff88ffeeffeeffeeff88ffeeffeeffeeff88ffeeffeeffeeff88ffeeffeeffeeff88ffeeffeeffeeff88ffeeffeeffeeff88ffeeffeeffeeff88, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
  | 0 => 0x9f8e3cf9e3fc31ce38cce3cc7f98e198719e8b
  | 1 => 0xe7f03f3e039fc1ffc0f0fc7070e0ffe07650f3
  | 2 => 0xfbffc03ffc1ffe0fff3f007f80ff01ff88631c
  | 4 => 0x3ffffc0001ffff0003fff8000fffe000f83e0
  | 5 => 0x3ffffffffe00000003fffffff0000000ffc00
  | _ => 0
def q7Neg : Nat → Bits
  | 0 => 0x208286084504821441042084128a2490a08689
  | 1 => 0x9110890882904880a10445124204941425032
  | 2 => 0x0
  | 4 => 0xf6a492055352a104956da9020ad694122d83c0
  | 5 => 0x5f4920a5820329a926bad26b4c0418444f7800
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 55 q7Pos q7Neg, 0xfefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8fefefafafcfcf8f8, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q9K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q9K4 (i*5) 5
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q9K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def q9Pos : Nat → Bits
  | 0 => 0x9f8f38f9fc7c398e3e0e33cf8f9c319f01ae4e
  | 1 => 0xeff03f3e3f9fc1ffcff03c71f0e03fe3f25073
  | 2 => 0xf3ffc03fc01ffe0ff03fc07e00ffc1fc0c639c
  | 3 => 0x3ffffc0001ffff0003fff8000fffe000f83e0
  | 5 => 0x3ffffffffe00000003fffffff0000000ffc00
  | _ => 0
def q9Neg : Nat → Bits
  | 0 => 0x20818a0888848214404210828284948a108646
  | 1 => 0x0
  | 2 => 0x5120490112910280294405424290150246098
  | 3 => 0xfaa49205aa52a104956ab5004ad2ac0a4b8360
  | 5 => 0x5f4824a53003354929bd2a696c0308508f7800
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 47 q9Pos q9Neg, 0xfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcecfeeefeeefcecfcec, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q11K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q11K4 (i*5) 5
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q11K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xbf8739f8fcfc79fe7fc631c7878c3f8ff0a467
  | 1 => 0xcff83e3f3f1f818f8e383e79f8f031f3035a5a
  | 2 => 0xf3ffc03fc01ffe0ff03fc07e00ffc1fc0c639c
  | 3 => 0x3ffffc0001ffff0003fff8000fffe000f83e0
  | 4 => 0x3ffffffffe00000003fffffff0000000ffc00
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x1088888a0824121410481208909094a2110a4a
  | 2 => 0x5110510114920280292405222250148246094
  | 3 => 0xfaa29086aa925104a56cb48054caac224b8360
  | 4 => 0x6f442524b003654949b72965660308488ef400
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 31 q11Pos q11Neg, 0xfeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaea, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x13b18ed32f261e8c3a98ee32
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x314c931d1314c324c930
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
  | 3 => 2*((h/9+packedAt q12K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q12K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q12Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffbe93b368ec8f
  | 2 => 0xffffffffffffffffffffffffffdf1cdc70f533
  | 4 => 0xefe0ef80fa3c
  | 5 => 0xffff0fff03c0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff422441212085
  | 2 => 0x244124424112
  | 4 => 0x180a1a048228
  | 5 => 0x0
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 54 q12Pos q12Neg, 0xfffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0fffffffffcfcc0c0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x636997631dc65e8c3c987531
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x324c930d1314c314c931
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
  | 3 => 2*((h/2+packedAt q13K3 (90+(h % 2)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q13K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q13Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffbe93b368ec8f
  | 2 => 0xffffffffffffffffffffffffffdf1cdc70f533
  | 3 => 0xefe0ef80fa3c
  | 5 => 0xffff0fff03c0
  | _ => 0
def q13Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff422441212085
  | 2 => 0x244124424112
  | 3 => 0x180a1a048228
  | 5 => 0x0
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 46 q13Pos q13Neg, 0xfffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x8020203a90df32f24174cbd107621
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x7848520c53248724c920
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
  | 0 => 0xffffffffffffffffffffffffffbe967377446b
  | 2 => 0xffffffffffffffffffffffffffdf1b9c7b8593
  | 4 => 0xffe3ef83fa1c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff422881110829
  | 2 => 0x244424221092
  | 4 => 0x0
  | 5 => 0x18015a402340
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 53 q16Pos q16Neg, 0xfffffafaffffa0a0fffffafaffffa0a0fffffafaffffa0a0fffffafaffffa0a0fffffafaffffa0a0fffffafaffffa0a0fffffafaffffa0a0fffffafaffffa0a0, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q17Atlas : Atlas := ⟨3,rawDecor 45 q17Pos q17Neg, 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x20001dd32be6534cb7196d32
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x2350e32
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
  | 3 => 2*((h/8+packedAt q18K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q18K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 45 q18Pos q18Neg, 0xfafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x100007d187631da65e4c37197531
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x10314c931c9324c344c530
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
  | 3 => 2*((h/9+packedAt q19K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q19K2 (78+(h % 15)*2) 2) % 3)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbe93b368ec8f
  | 2 => 0xffffffffffffffffffffffffffdf1cdc70f533
  | 3 => 0xefe0ef80fa3c
  | 4 => 0xffff0fff03c0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff422441212085
  | 2 => 0x244124424112
  | 3 => 0x180a1a048228
  | 4 => 0x0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 29 q19Pos q19Neg, 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
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
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 4 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q20Atlas : Atlas := ⟨3,rawDecor 51 q20Pos q20Neg, 0xeeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x18045d32da657cca6996e32
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x2350e32
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
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 4 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 4 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 51 q21Pos q21Neg, 0xeeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q22K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22K3 : Nat → Nat
  | 0 => 0x4001812f995d32f441d487b10f920
  | _ => 0
def q22K2 : Nat → Nat
  | 0 => 0x400314c921c932483848520
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
  | 2 => 2*((h/15+packedAt q22K2 (78+(h % 15)*2) 2) % 3)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbe967377446b
  | 1 => 0xffffffffffffffffffffffffffdf1b9c7b8593
  | 3 => 0xffe3ef83fa1c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff422881110829
  | 1 => 0x244424221092
  | 3 => 0x0
  | 5 => 0x18015a402340
  | _ => 0
def q22Atlas : Atlas := ⟨4,rawDecor 43 q22Pos q22Neg, 0xffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def q23K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q23K3 : Nat → Nat
  | 0 => 0x8003d107521ba65d887c905f32
  | _ => 0
def q23K2 : Nat → Nat
  | 0 => 0xb848520c53248724c920
  | _ => 0
def q23N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q23K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q23Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbe967377446b
  | 1 => 0xffffffffffffffffffffffffffdf1b9c7b8593
  | 3 => 0xffe3ef83fa1c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff422881110829
  | 1 => 0x244424221092
  | 3 => 0x0
  | 4 => 0x18015a402340
  | _ => 0
def q23Atlas : Atlas := ⟨4,rawDecor 27 q23Pos q23Neg, 0xffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x20000800c00020c000904a0920c01ff20007f94401fe50007f55001fd41007f48001fe30007f4c401fc21007f08001fc10007f90001fd21007f4c801fe32007fc8401fd51007f50c01fd50007f90801fd53007f88401fd30007f94801fe31007f50001fd10007f84001fe20007f50801ff10007f54801fe41
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc4007ff106300d7f86329007fc3104001fe304a400bf58e21005fac528043fc548c401f6a964000bfd912102ff88410003ff6404001ff1084200bf98810007fec090802fd6590401fb90c4200bf5824103ffe8518003fe4104001fea14a000bfd8c100b7f8c919003fc624c401fe994a000ffc8710007fac2a1802ff65c8001fea002000ff50620007faa108003fd42544017fb02a607ff1923006ffca610867ff5390801fe992a200ff90950007f8c518873fc5150c01feaa64000fb54920007fca520803fe608840dfe2884000ff4c710007fac010853fc63944017fb0a8400bf58231005fac99001bfc5208001ffb0aa41effcc954007faa41083fff5408401ffb12a000ff8c420007fa8518003fd2150025fe1848200ffd8131007fec81006fff4094801fe30c6002ffd0010005fac688003fd548c405fe208201dff10953007fa6010077fe6454c017eb246400ff90710027fe6410003f63188401ff194a20dff14c21007f84088003fd43440017e3028200fe90210007faa4a0803ff2108005ffa102000bf58232007faa88806ffc6494801f7212421eff98d54007fa8790803fd434800dfe3284000ff58b10005feca98803fc62440017e312a800bf59421007fcc2aa003fc6055001fe30ca400bf185530dff88329003fe5250003ff9882000bf58a51007fcc408002fe618c801feaa2601aff90e52007fec129003fd43c8001ff2142000ffd8953007f46110003ff6154c05ffa182000f78c130005fac91883ffc5108401fe9902000ffc8020007fec0a1002ff63c40017fb1a8400ff54e400b7f88119003ff6148025ff9848200ffd8c10007fa8408002ff6244001fb28e2000efd9110007fca318073fc5250c01feb0aa800ff18251007f84320027fc5390035ff98ca41bffd0e52007fc64a8002ff64884017f30c8000ff4c420007fc6210803fd54c8401fe9004000ff55120007faa790013fc3108001fe3026200ff182320cff8a121003fc21440017fb0a8604ff10c20005f8c2a1802ff65504017eb146000ff551310eff8c8a9803fd610801bff9904200ff54d10007fc8110003ff600842dff2a46400bf59110005fec61007bfc315501dfe3204200df54d52007ea6310802fd6544033ffa848400ff4cb10007fc4320002fd61c80017fb2a4200ff8c6200e7fea4a1803fd42c4001ff9084200bf59251037fea410003fe6154c01fe10e4000ff90420007fec721037fc43084016fb1a4209ff0ca40005facb19027fe5390001fea0e4000ffd9250007fa6210803fc214c019fe204a000ff8c621007fc4088003fe5104001ff284200bff18e50006fca32805ffc508c801fe3146000ff54d42097f8c720803fe3284001fe98c4200ff54d20007fa6110002fd64c4021fe214620fff1482102ffe801000fff5304001feb0aa600ff88510
  | 1 => 0x3ff6090801ff1062000fe4c120005fcc121003fd4308001feb2a8600ff54640007fc8590802ff64880017f314a000ff58d5401ffea80804ffc5090401fea12a000ff18642007faa408003f51004001ff3084000ff90230007f64090002ff65c84017fb102000ffd8954005fac520803dd538c8017eb202000bf5861000ff8c608003fe424c401fe3024200bfd8550005f8c298023fc518c001ff10e201cff9954300ff8a608007fc3204001ff2922000bfd8530005fec099003fd54880017e3126000fb50921007fca518802ff614c8017eb2a4000bfd9542007fc6590003ff628c019ffa14a000fbc8020007f8c2a9863fc3190801fe994201aff0ca52017f88408002fd618c001fea1c4200ff18420007faa298003fd31940017f3104000bf18152007fac8a9803fd53080017eb1c8200fd4c521007fa8108003fd2190001fea962000ff8cb210077c80a005ffc528c827ffa848200bfd9320005facaa0803f940440017fb1aa200bf9802101ffcca08023fc528c001ffb02a400ff58321007fac61006ffc4294801f69004000ffd8141005fcc41083fff51084017eb0ca000ff18943007f84210002ff6408401ff90ca000ff98321005f8c588003fd4308401ffb048200ff1852001ff8a208003fe4004001feb102000ff54520007fcc2a1803fe6054c01feaa04200ff50a10007fe4318002fd61080017fb142000bfd8e20007fac310002fc6254401feb044200ff8c410005fec6a0803fd4388001ff1948215ff10251007ec4210803fe21080017e312a000bfd8d21005fec808003ef2108403ff990200bff0c650007fc801007bfc6355001ff1004000ff48530007fc83280027f6544001fe30a8400ffd8810007fa2008003fd410800dffaa04000ff59410007f8c4a8803ff6408401feb202000ff94931007fec329002ff6254c01fe3004200bf9872000778c888003fd21c8001feaa44200bf58e10005fac58805bff408c801fe30aa000bfd9420005fec8a9007fe63040017fb024200bf59321005fecb88002ff658c401fe9802008ffd4a30007bc6518867fc65908017eb2c6200ff8c710027fca610003fe418c001feb204000bf59252005fec8a9803fe524c0017e302a800bf59532007fe4008027fc309001bfe3184200fbc82200b7f88319063fc6390801fe314a00cffd0e50005fec899003fd5308401fea904000bf58652005fcc518007fc43040017fb128000ff90a51007faa6a0803fe52c801bfe1904200ff5895405ffe6328003ff21040017eb2c8403ff1481001ffea408003fd2004019fe20ca01eff0c954007dc4090003fd4188409fe1904004ff14c20057fea320003fd53880017eb226402ff19010007fa8210803fd51500017e3028400ff4c410007de4310803fd5388401fe3028600ff98143007fca5908037e5254801fe1
  | 2 => 0x10007fcc4aa003fd54c4001ef1946000ff18a51005fec2a9003ff6050c017e3102000ff18132005f8c4a1803fd6304001ff2844000ff50c10005feca9800ffc6504001ffb122000bf18121017f8a80806bff3094801ffb0a8000ff55121005facb20002fd6190801ffb128000afd9110087f88118863fe5390801ff1904200bf98630007fecaa1803de314c401fe302a200bfd8141005fec708023fc658c0017e3128000ff54621007f84328013fc6308001fea1ca400ef55140005facb1003ffe6508407ffa882000ff98a10007fca290002fe61884017eb246000ffd8550005f8c2a0002fd6448401feaa02000ff59421005fac690002df6348001ffb128200bf58e20005fec4a8803fd61c8001fe30aa400ff5442102ffe8210003fc2004001ffb128600bfd9641007fc64a0802fd6090829fe18ca200bf98020007fa64a0003fc6250401ee31a4200bf58c2006ffcc610803ff6254401ffb0c6000ef55142005facb18003fd6055001ffb146218ff14e42005fec58802bfc5090001feb284000ff94641007fca410003fe4084001fea0ca000ff1814208ff8a118803fa1004001fe10c6000bf98421007fc4328003ff2154027ffa9c8200fe90110005fac810003fc6254c01df20a8200bf18132007fec728002ff658c009fe180401cffd4543007fcc4a9847fc658c4017f3142000bf18131005f8c0a8803fd2108401fe3102000bfd9231007fa878805fff548c801feaa04000ff08310007fc6110003ff639442dfe2146400ff4c550007faa690813fe4308001fe302a600ffd9640007fa8318057ff40944017eb2a4200bfd9510007fa8388003fe5150001f7296400eff15021007fac610803fe218c02bfe20ca200ff581530cff8a321003fe4154001fe312a000bfd9151007fa6108003f55144001f72924000df55250007fec320002fd6550801ffb02a800ff54c10007fecb18003fe428c43dfe182a800fdc8521007fec128803fb1084017fe194a000ff08410005fcc329077ff4154c01ff9042000ffd8542007f8c121003ff6290401ffb126000fd8c52108ffea118802ff648c011ffaa46000bfd9020005f8c0a1802fd6288009ff9804000ff94821007faa518002ff6448001fea8e4000bf1853202ff8a810003dc6348001ff216400dff0c021007fc4008033fc429402bffa1ca200ff4ca510cff8a521003fc6255001fe9042000ff8ca40007fa8528803ff63550017eb04a200ff50410007f8438805ffc518c801ff2126000ff54f10005fac8988037d5394001ff1922000ef90640005fac408002ff6550001ff1082000bfd8f21007fec2aa002fd65040017f30c8400ff4c950007fec918003ff6308415fe32c8000ff94941007fec31901ffc428c01bff2184200ff9424000ffca60801bff5108001eea1c6400bf59610005fcc12880
  | 3 => 0xeb0c8005ff95020007fecb19002fd6394801ff28c4000bf98210007fc8298003ff6054401fe1042005ff10020097fe652085ffc658c8015fb224200bf9823207ffea610802fe60948017fb2c6400bf986500077a86a0002ff6348001bfb2a2000ff48630067fe8328063fc30908017eb2a800eff9902109ff8cb20802ff6354001fe98e4000bf98b10007fc6328002fd64940017eb1c8400bf18550005fac129002ff6504001ffb24a21aff18e52007fc6008043ff408c401ff90a401cff14143005fecb08003fe5188401fea1c2000ff18141007fc6588002fe61040017fb02a200ff55210007ee2008002fd6290001ffb0ca000ff8c940027fcc61001bfc5008019fe324a000ff90720007fc62a0043fc418c401ffb126200bfd9150007fca390003fc21540017fb02a400ffd8642005feca10803ed21084017e3126200ff48410007fca51801fff418c001ffb24a400ff987200eff880a9802ff63440017eb142000ff54710007fa6488003fc61940017eb1c8009ffcc640007faa310003fc6155001ff20a4009ff18e40005fec09884bfc3190401fc9004000ff54e10007faa110067ff519081dff2a04200ff50550007fa6520003bf6448401fe3046200bf58c210b7f8a919002fe628c417fe184a000bfd8154077f88010802fd6508001fea1ca000ff90820005f8c2a9003fd428c4013fb2a4017ffd46320e7fea0a1803fc6090401feb028600ff98154007dc429086bfc439480dffa804000bf58c10007fa4210002fd65c8421ff2a46200bf5971009ffea520803fd42440017eb2a8615ff10a51007fec099003fe42440017fb0aa818ffcc642007f84308003fd424c0017fb184200ffc8540007fca408002ff6350001fe30c6400ffd842000ffc8608002fd6088405ffa082000ff48710007fa86a8803fe52c40017fb0aa60fff14021007fe2008003ff639481ffe3284200bfd932106ffe6010803ff614c801fd9044007ff15230005fcc120803fd548c8017fb0a4000bf58620007fa62a0003bd4350801ff1904000bfd8d54005fac010803fe5190001fea164000ff4cb20007fa8590803fe2084001ff3128600ff55230007feca08063fc32908017fb12a814ffcca51007fca010002fe60880017f3148200bf589100dffe8329002fe6108001dea1c8200bfd9520007fcc31002bff5390001ff3162000ff54e42007faa210003fe21840017e3122000ff59021007fa6590802ff65884017eb224000ff8c550007fa6520803fe42084017eb0c6401ff0c0100077aa920803f9308801dfe2104208ffd4630007faa508003fd424c401beaa2a400bf59720006faa8a8802fd639441fffa804200bf982210affe8528803fe3008001ffb046214ff10e51007fca29806bfc3094801bf294a000fd4842100ffe6008003fd4348439fe32a8600fd841
  | 4 => 0x3fd5390401bf28aa200ff8853002ffe8410003fd400801bfe1884200bf98620007fc8528002ff6254001ffb1c8000bf18542005feca99003fe51c4001ff10e4000ff54910007fa6410013ff3108029ff21ca200ff90a32007fa8290003ff2188001fea9a8000bfd9210057f8a320003f71084001fea802008ff14230007fc8210802fd648843dff98aa800ff4c6200a7f86128802fd64840017fb1c4206ff9942007ffea410803fe3084001ff90c4200bf59021006feca9005fff508c801df2148200ff54b21007f28108017ff43080017fb126000f7d8d20007bec690802fc61550017eb1e4000ff50820005fec4a0802ff6150001ffb148000ff54b20017fca808003fe41884017fb2c8014ffcc251007bc6499003fd544c805fe200201dffd0953005f8c290003fe4254401ff20c401bff10252007fec8a983bff4308401ffb2c8211ff146310effe80a9802ff644c43bfe20aa600ffd8a51007f8c4a0002ff644c001fe3148000ff58943007fc6320002fc628401dffa004200bfd9310005fec790002fc6254c01feb12a600ffd9642005fac790802fd60c8401fea926209ffcca40007fc2008003ff6294001ff2146000ffd9421006f8ca88003fc605481dffa104200df94150007fec919002ff6550c1dfe2084200ff08540097fca720803fa2008001ff192a200bf98a40007f8c2a0003fe5284001ff194a003ff14010007fec720802ff6354801fd1824000bfd9642005fec919003f91004001fea1aa416ffd0632007fa8728803fd4088001fea948200bf59220007da8590853fc3294401ffb046400ff94420005fcc190802fe6294401bea9aa200ffd9631007fca31882ffe43940017eb2a6200bfd9620005fec4a1837ff310840dffa984000bfd893100778c890803fd3208425fe1948212ff14e41007fc42a0043fc648c401f72164200ff50821005fac690803fe31c801dffa08421effcc154057f8a520003fd518c001ff8842000bf59621007fec0a98037c6548001fe3148200ffc8640007fc8408003dd434c001fd8822000ff18530005f8c4a0847fc528c401df2128400bf58e50007fca118003f551c4001ff18a4000bf58f1001ffea008003fc624c001ffb0a6000ff4c640007fa6290002ff6050c01fea1aa000ff94a40007fca521003fd5008001fe9928200f750d31007f8c299003fd52500017e302a600bf58a3105ff88728027fc3190001fe30a8600ffd8c20007baa698063ff30908017fb028400ff94a32007fec2a1803ff21c8001fe30c8000f754d31087fe851882bff5290027fe28c8200bf58a21005fcc118803fe42c4017ff994a015ff19251007eca28804ffc5290401ff1902000ff48650007fca008017fe6408001ff10aa000ff90631007fac508003ff214c023ffa946200bf59530007fca210803fd51040017
  | 5 => 0x4f8260001140008b0020200e1c301402c038050000640081201206c00088014018390310100700100e00001c148160001240480306c0000002000a441149f305602c1801506006009000008001240010006a80081a02405d3080c08a0980103b032004050000060000080a006018000010000096c00200c070080010ca028060290288dc000820000340408e0001b8020130000c83102001e068008120000005400929e0f41103021c0a82b8040203ad5c8030000040280001c010090000000084d8010100280100203a000e980c04a0011180704a028040660700200100002c0001e00847402c04001000038048010f20bc0980300a3fc128360020fc0080112c0940107f0ea030029d91f81a40b80304e104189a10082840e0490b80000f890008014008038a40000000d0040c40180000000c068071540e4220090e60113e00e040010010000680180000000a000280c605a01403800008078000120680d02e0050000a41b01a03802800804000000018e40001703003400001401219082044020181020c80024c0028c04700f0be0501800e00402013800008efc1a0060000140d000000000040776b20300e0010240000004b0160180194308c038000b200001801000064020400030aa06c0383600600c2680900001cf10020280302305d0000000700e1600000580201000c4801b0660100000900e0dc000510020c414800072010000040000001b00406e0000280f0f006117001007faa790803fd5290001ffb246205ff19020005fec88801ffe548c001fea926002ff9901002ff88210003ff65080017f3122000ff50530005fcc008003fe6008401fea946200ffc822008ffea918803fc214800ffe2046000bf59130007fa42a8
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xf31d9153004fe72d8554006fb609815402efd411894007cfc7259421004fe71d8132006fc6298154005fd7408420007fa71c822002efe4118940006fd73185540e5fe7518943005be7090a410067d6555310005fd754c52018dfa70d8e40004fc7690520006fd7398021004fc7059531006ff6218131004fe71d9632004fd7650c21006fc3259010007f721c4010005fd75d8a41004fc7650420006dd658ca31007dd4354931097bd5350e41004fd7650e21006bf73d9121006ff5258c10004fe7654c21006fd63944212d6bd74189541bf7f4154e500c7df3154e42086dd43d8d41166fd3118153004fc7655010004fc7650d50004fd74988100077e51906500bf5c5054e320077d548ca500577f5354a40006fe71d9632005ff7354a41004fe70d8c210067d6594b10006fe629401008f7c528c650007be42906303067c50d8d54006fd635464015efe3118143006ff6394540006fc5498232005fd73182510e6fc51d9543016bf425901006dde7318021005fe72d9010007bf6490650007f64294510005fd741895307efd50185522eefd40d8d54007fb20880100077c2194150005fd7408530006ff52d8c100077d54c8650007ee21c8020005df7348630005ff7059421005ef724c420007dd538c9402ef7c54d8d54006fe5458c21005ff73549412e6fe31d95430d6fd31d9532006ff4259630004fd76c8410006ff43982510067f6508510007fb714c220006fd658c720007de324cb100eefc6454d10004fd7318152294fe72d9632006fc62885100f5fc7358954005ff7348540006ff6558420007bd43509100cf7f5390951006fd6448630006df658ca300077e528ca50006fe6058221006fd658c421006fe6154420006fc32d9640006fc4158e52076bf4359021004fe7650c20004fd7518540007bf7250e410077e52c8650004fd7418931006fc7459410004fd759823111ff8418c220004fd74d9410004fd7598632005fe7088510004fc764c640237bf5390a41005ff758c94103efd42d8d40006dd5318930006ee6254a300a7dc32d8e51006ff6598943006fc41980210677d5450e50004df7358a40005ff758ca41006fd42982312dfdf30d9153006fd7518540007f22144010005dc7050e32005fd758c910004fc705913228cfe72d923225f7f4254d51007ad4350b21007f461c8540007bd5490630004fc7059121246f54118543007e6428c521004fb705953202fbc42904200067d6554420006ff6558810004ff7694420004fc7650951004fe7688540004ff7690a10006fd6454a31006fc4058e52196bc4118154004ff7654f10006fe62c4210004fc7690810006fd654ca41004fe72d9610006ff4198a50004fe7688530006fe7118950004fe76c8650004ef72595302defd32d9153005ec7254e2026efe54185531d77f5118154
  | 1 => 0x9543026fe3118132006fe621814304fde534c640007f53254710006ff7359010006fe6290210004fe7098a5107e7c50d9421006fe5498420006ff6118154004fc7654520007ee42c8550006fe7018532077bf40550212dfdc53d9153005fe71d9153004fd7650c10006fe7018553004fe72d9543005fd7308410005fd74184200e7ef5250e52006dd638cb20004bd7418810006fc5458c21006fd7118954005ff7350a10004fc7258e40006fe61c842025f7f4054d5107f7f5408650006fc5498231006ff7655320007dd6350e50006ff31189540befd54d8d52237bc5290a41005fd7388710004fd7318154006fe32986400067d6594621006dd6354e2007efe5018552005fc7150930276fd5218554005ff735512002cfc7690020007f971c8220007f94008210007bd6450e50004fc768c950007bd4390550257bf4218554004ff7458c21006ff654c940005ff7550c21006ef62989530f6fe6355321005fe71c8220006fd6550b10004fd7318940006fd6394621005ff7454d10006fc3198021005f776484210077f7454d51005ff714c820005fd76c801006edf3058c21006fe3298321005fd73d9641006fd71d8c20006fc65189430067f6554d10004df7358a4100cfc7158c10005fd7550910006fe7218141006fd6390710006bd6450c10196fe43181542b6bc41189540f6fc53d8d54004ff764c810004fe72d8540005ff74581532d77f5118954005fa70085500f6fe63d8d54006ff409842002dbc745842001f7c5254810005fe7018a31005fd75d82312b77d7518954006fc6498021196fd4318154005fa709464005fdf31981530677d5450a50004fe71d9620005fe7218640006fc5118943034fc7259420005fc725901029fbf5150d42006ff764ca10004fe70d9232007de324c8100e67c6550d10074fc7259021006fd6508640004ff7650e2101e7c5159410006ff4198252007f63148640006fc32d9410006fc7359010005f77150c210b79f4050e32006fe6254630006ff6354520006fe61c8220006fd7688310006fd6454a30006ff5159232005fe72d8251007f9518c120005bd7590a41006ff5498810005fd7318954005ff755802107cfd75d942102fbc4150c20005fe7284010004fe7650d512efbf40d8d54006fe52185400067e7518943006de3218132005fc7255210004fd7654f21005ff714c0200b7be645523215cfe70d92300eebe64d9153097df309854301e7c5118151006ff6358021005fd7308710005ff7558143006fc6398554006dd6354e10006ff74594100f6ff30d8d54004fd7518532004bf7459510006ef6298954004fd7518930006bd6450e20005fd75d8e41034ff7654b202fdfe76d9153006fd658cb1028eed3218943005fd7318810004fe7655232004fc768c520004fc7690930006fd54189312ded
  | 2 => 0x979c3250e41007e6628842107efc2159421005fe70d8c210077d5454530006fe5359021005ff704cb21006fd6454e210f6fc6355120006fd6598420006bf6418121005fd744c520007bf7494a41007f920082100d6fd30d9532074fc76904212f6ff41d9543005ff754c540007df7550d3106ef571189310057d7550e50007df7154d30006ff648c951006fd65c8630005fc7154f200063c6519110006dd638c4102ddbf7459543004fe72984100be7c658c910005fd7388410006ff6454a31005fd73d82410077f7558021006ff7558c10005fe70c87100067f6594540005ff7150d202d6fd5118954004ff7458c10006ff648c91027fdf5150e32006df638c9100b6be5459232005fe7018532004fe70d9221006fd65087200a7dc3250e51196f94018154004ff764c420006df658ca310efbe5454e412eefd41d8d5406ede5318931007ed2158021006ff3259250006fc6518143006bf6455121004fd7518943006fd6494a10004fe7098632005fd7494a30004fd739825105cff73d95300057f7590a500057f7454d51245f671d8e41005fd72c40100077f71552500067f6554d20004fe71d9630006fd5458f10096de5358e41004fe70d9642005fd7318a41005ff7350951005bf744c640007bd4390650006fc5359020004fe701855402efd5418940004fd7598810007ee42c8650006f4614c540004bf745952121efe6154e41006fe7018931005fd748c520005fe7218141006fd7418910006ff7654720006ff65d8943005ff7054b21004ff7654e21004fd741895007f7f5308650004fe7198a50006fd6354a1006ede63d8c210077e4294650007bf7355142006fc5118143005fa70887100e6fc65d9543005fd71c8220004fd74d8c20005fa7008650004fc7159632005fc7154a30006ff2158221005fc704c421006fc7359420006fe70d9232006fc63594212d6ed5218954004fe71d8153005fe7218151024fc7058c20004fc7648650005fc7150820006fe62d81430e5fe75d8143076ef7650b21005fd7650420006ff3259640006fc4398021007ed524c720007f52108710007fa3290110004fe71d9720006ff52988100d67d53d9532006fc3259641007f53188710007dd538c941005fd7518242007be4150420004fc7059021006ff65d8543006ff6558543004fd7598321006ff5059021006fc50590212defc32d9153005ff704c621006ff30d9421004fe7608530004fc7158a30004fd73d9421005ed76c8621006fd4298321006fd6218553004fd76080102e6fd73d9543005fd74949310f6fd74d8d54006fd7418121006fd5318520004ff7654e100077d5354910007dd538ca41006fd72d9153006fe6158720006fc3059021004fd7318542006fe6288210006fe3298420005fe71d8232005fd73d941000fdc3250c102e6ff32d
  | 3 => 0xd5490650004fe72d9410006ff6394520007fa518c120006ff43d9410006ff63885500067f654c520005fc7250210006ff411895303fbf4255230006df6318520004fe72d9630004fd74d9420005ff754c520004fe71181520b7bf4098943004fd73185200367c6559420006fd6118143004fc7655130006ff6118143005fc7059021007ea528c120006fc32594200063f65d9110005fe70d8e41006de7318810007be4290420006fd7418131004fd7418951006fd6494a310a4ff73d9531006ee6294a3001e7e65d941020fdf408ca31006fe71181420367e65d9420096ff6454d410057d75d8143004ff768ca100067c71d9520005df7348420005fe72d8e4006edc3118931007fa7008550196fd4218154005ff7050c21016f97018540004fe7650d20006fc62d8143006bd6450810005ff744ca100edfe74d8553007df638ca41006ff3098652006fc3098652005fd74d865006fdf3058c210a6de4358e51005ed76c8220006fd3298720004fd74d963005f7d534c650004bf7458d10006ff6448530005ff72440100e57e75d8143005fd7388640007bd5490530005fc7054e21006fd6550a30004fe7650d10005fd70c8621006fd654c620005ff7154220257bf40185540047f75580210bfdd5454e32004fe7198a30007f54394510005fb7054c20006fc62d8554004fe7655110006bf6454910006dd638cb21007f62108510016bc4018540006dd6350e5106cff764c621006ff2158021006fc4158c20007be4290530007bd5490420006ff4158e50004fe71189530e57e7518543006fd63946400077f7154d520067d6554c10004fc7059631005fc7050c21006ec6254931024ff764c220005ff7354a10004fd7654f20005df73485300065f65d8d20007dd4354930006df7359543005fa7008630004fe76c8630006fc62d8153064ff74d9540006ff7654f1016fbc5250d40005fd7308640004fd7318151006ff3018554007bf6490420006fd6548540006fd6388410006fd54d8d21097bf5350e41007f53188410007f521084102c77f3055152006fe5498a30004fe7218154006ff64d8553007dd434c52030eff51d9153006ff7655321004fd7598242005fd7398554007777554710005fc7055232006ec628853004edc32d92300067e751854307d7c755802108edd53d8d51005df7550e32006fc5058c20005fc7154e200f5ff7358d540067d53181510077d535095116fbf5250d40167dc321815300dfd738c810004fc71595202767c5018554006fd62c4010005fd73d8640004ff764c720006fc62d854305f5c3254e50005ef7258153006fd2198021004fe7018931004fc7058632137ef4194b20005dc7150e32007dd4348530006fc75590212b6fe4318954004fd7654e20005fc7055321006fc4058c20006dc628c130016be5459010
  | 4 => 0x4510005fc704c8210befd51d8d522f6ff54d954301cfc76940100f6de53d8d54007ac7255142006fd75185300eebc6454d21004fe70d8f21005ff7158c20007f570c86210debf4359252006dc70d8d21007dd538ca10006df75d8d20006fc62d8151006ff3259251006fe6288410005fd739494021cfe71d92310f6fe6355320007fa7008650006fc6248410006dd638c2202e6dc32d954300efd5318530005fd7488650005ff7355210006fd7118142005ff7548530005fe70085400f7df30595430e7f75150e51006fe6558c21006ff6350420007ef21480200eefc645915323fbc5250e41006fc411815322fbe5390a41007de3250630005fe71d9252067bc6490650004ff7648020006fe3218550007f53294710006ff6390420004fe70d8810005fc7050621005fe72d8c10004fc7259631004fd7654c10004ff7650f10005fb7054420006ff6398154004ef7258d1009fbe5355241006fc4158c10007ed624c810006fd6494a30006f5610842001f7f5255010006fe61c80202cefd5018953007f62158021004ff73594200cf7c7590a50005fd7494930007ed21c8020007df7050d3127fdc5150e3207f7c5208650005fd75909100d7de4394931014fd74d9010004fc7259250004fd73d964008efd52d8d51007fa20440100eebe54d91530076d5354b20006fe3198221005fe7018941006ff7158c202dfdf31d9153006fc4098a31067be5490650005ff7590530007dc7050d31017bf4359010007dc7358810006fd70d8c21007cf7254e320057f754ca50005df7454e32005fd754c91024fbc3055241006ff61d8143006fe6294630006fc4298021004fe72d8f101a77f4294650006ff659854307cff7654621006fd7518930006fc4058c10004fc7650d20097bd4390630005fc7048421005fc7250d5001f7f5294810004fe72d96410e77c5050e52005fd74d9632005fe7198953006fc6290530004fc70591310057f7355152005fd748855020fde548ca31006fc5498420006fd6494820005fd73d8a51006ee6208410006fd6588410006fc6598420005fe70c8720006fc6250530006ff62d81430f5fe7398954006ff6454930006ff3298251004fe72d8143005ff748ca102efbc54d8d54004fe7608550005fa7088640005bd7418021006fd61d814306cfc768c421096fd53d9131006fc5198a40005fa7088410005fc7054621007f53188640004fd7318941006dd638c2101d6bd7418154004fc7690550025dc7348420005fc7155120005fe709493123fbf5250e41006fc4318810006fc1058810006fd6454f20004fe72982410e67f5259543006f976c822008e7c658c520004f87059541004fe70d8951006f76198543006ff6548530025dc7348020075bc7448421005ff7159020004fe76c8520006ff62181430dfbc4094a410073
  | 5 => 0x5ff7350650005fe7008520004ff7458e5202dfa70d8a40004fe71189540afbf4350a5122fbc3090a410077d544ca5007efe5018951006bf6450d210f6fc635512107cff7654b21005fe7198153006ff6498953076ed7218542007f54294510004fd7518941006fe6458c21005ff744c6500edfc7458153006ff659093100edf3258c10006df6350520007ed5350b21004fe70d8d5401e7f53594100057f7558021006fe53988100fffb3290210006bd6490220006ff40d9632006ff7654e21005ff7458c20006fc4098810006fd6558c10006fd6390620004fe7218153006fd63506200047d7518543006ff648c810007f562c421029fbc7550d4207f7c5008550005fd7550d21006fc4159410007bd544854001e7f5418151005ff7354540005fc7050a31004f471591202cefe50189530057d7494a50004fc7650a312aeff5418943006fc539802101e7f5459410005fc725531000fde634c8102d6fe5118954005fd768c810006ff6118152005f67194931006bd639064005fdf3150e50005ff7255210006df639052019f7e43946502eeff42d8d5403fbe5490630006fc62d8154006fd644c6500067d6594210004df7359520006fe701894101e7f5318151005ff7454620005fc7250550006dd6354c2009f3f5255241007df638ca50005ff7058c210067f6518910066ff65905502e6ff53d9543005fd7598543006fd72d9640006fc41d9420006fc31d9420007bd5390640004fd7650f21007de3294631005ff7350b10005fc7154820006df71d8d20006fd76c8620006ff52d9230276fe5218554006de3298630006ff7458c20004ff7648010006ff5198242006fc62545400f5fe7398154006fd5418930006ff6298154005ff74589532d5ee72d9252006fd654c6400077d4394650004bd74d8a10006fc6218530005ff7350a51006fe6359020077bf4050c2106cff764cb21005fe7190950087be5450a31006fc5058c10006fd76083100bf7f548c95101d7c7544010006ff30980210e5fc7518143005fc7154930007df7054d31006fa701881027fdc7550e32004f8705952117fbf3290640006fd7498a10227df3018553076be64d90212eebc41d8d54005ff7454a10006ff6018121006fd70d9021005ff744c9510f6fc4359543056fd53d9150005ff748c520006fd7498321005fe7188110005fc7258554006fc5498a30004fc7648550007f261840100067d6594010005fc7250e50005ff744c550005fe72d8650005ff7454720004fe7118943006fe6188020226fd321855307efd5018951006fc614c520237bc5090a41025de7318420007d9534c220005ff7250010004fd7654e21005dd73d89543077f51d8d54007df7550d300077d5354720237bf5090a41005ff735055007f7c5054c21006fc6254910005fc714cb20007f6329
  | 6 => 0xd43904200067d6594710004ff7650b10005ff7254210006df63d8520006ec62949310f5de7318554006fd5458e20006fd3298420006fc4198a50006fe73d9640006ff5398642006ff4098632006bf6494910007ee52905200057f7548020006fc3198810006fa70d9640006fc5098a31006ff6358954006fd654c7200057d7518810005ff7354520006df74d8d21005fe70d964110ff43294710006fd75d8c210f6fe43d8d54004fe7654d42006fd3298640005fb7058953004fe721854307e7c5159421007ee52505200cefd51d9152006fe7118153006dd6354c10006dd54d8d20004fe7654d21005fe7118953006df70d8d21005fb70550102a7bc7355142096ff63905300e57e751894318eff5418143006fd74d8c200b6bc41d9232007ed42c8550005ff7154f2001e7f5259410004fc7259130005fc7255010004fd74d94210e6fc52d9543004fc7654a40006ff5098810004ff7558e40005fd71d8c20004fe72d9640004fe7098a41006ff644c550004fd7598b10004bd741895320fdc548ca31006fc6418153006f96018143006fd6148020005fa7008530005ff7250e10004dd7318554007de3290630006df7358c2002ebc4059020006fe61d8143006ff4359420097bd4390530005fa70084200f7dc3255231006fc43d9420306fd51d8d54005ff73508100bfdd538c951004fe70d8941006fd654cb102fdfe76d9543006ee72d9632006fc3159410007fa418c220006fd5458e1001d7e7518810006fe7598810004fc7650a30005fc7250650006fe3218540004fe71d9230005fd71d9020005fe71d8a500f6ff31d8d54006ff3159020004ff76508100efbf4258d54006ff764cb10005fe7190a50004fc7258e41006fe7018554006ff7650420005fd7394941004fe72d8153006ff41d9630005fd7394a41004fe71d9640006fe6118143004ff7650f20005ff75509312e6fd31d9543005f57188010006fe4198021006fd4198021007f9418c2200077d5388650004fc7654810006fc305925202cfc7059020007de324c910006fd658c6211c6f95018153005fd7408210006fd7598620004ff768c42028efd7418943004fe7218540004fe7018532006dc71d8d202b5ee72d9642004fc7159543004fd7518132006fc61d81420e7f45150d51006df7358c21067bf4250e50006ff5198232006bd6490010005ff7359010005bc7055241005f87054b10004fc72586300e6ff52d9543006fc7650d51007f95250210005f47150f21076bf4318542004fc7690950006ff6218153005ff748c951006fe7218540007de328c71007f7c50d9421005fd748863006efc7158c21005fe72d8141006fd62d85532cf7f5118953007dd548ca30006fc3098810006fc4198810006fd7608620006ff32d9640005fd74186300047d75d8b10006fc5098810
  | 7 => 0x8630006dd6350e21007bd5450931006dd638c0200f6ff3059543006fd7398221006ff6348550005ff7354b10005fe71d8e50006fc3198a50005ff7154e20006fd6454420006fe4298021006fd648ca10006bf6490910005fe7090a31005f87054a401f7ef5090b210577f5354640004fe72d8d54005fe72d82410077b7054e50005fc70551321cf7c32552500ce7c50d9642096fe30d91310eefe6454f10006fd6454c10006ff6494930006fe72181310f6dc6358d54006fd3298321007db734c2201efec3090b210befe51d8d5209fbd5454a412b6fe4018954006ff415963223fbc5050e41006fc7559020066bf4359250026dc3218132006ff6454520006ff659053003dbc7448630005bc7255241006ff655053030e7f51d9153006fd6494b2115edc3218143005fc7054a31016fb76502102e67d53d9543004fb7059541006ff6458420006fe71d9543026dc30189300077d4294650006ff62185430cf7c5090a51006fd62c4210007de328c2100673f4255250006ff32d9410006fc43594101bf7c4154e50005ff758cb10007ed42c8650006ff619842001dfa70d8650006fc5398241005fc7054d21006ff62d8554287df4054e3205edc32d9630034fd75d9420075be74180210067f6508110005f671882101af7c3294a50007de328c6402eeff40d8d54005ff76487200047d75189431c5fa70d8e50006ff658c540004fe71d9020007bc7458420006ee72d923215efd3118143006ff7459420004fe71d8c20006fd70d8d540f5de73d895406ede4358c210067f73d95100b6fe40d8d42004ff76550210077e2194150004fc7655120006fe70d8d54006ff644c95115eff53181430057f75486500477f5198153004fd7418153007f96244010065bc744865007e7c6508520004fd75d9232006fc7650520005fc724c210006fd6454e20007df7454e320cf7f5154e42046dd53d8d50004fe72d8553097de6354e41007ef2108620004ff764ca10007be4194240006fd6358021006fc6558c10006fc5318810006fe70d9153005fc724c7100067f6588510006fd6598810005fe7190a30006fe7498021005fd7390620005fd7390a10005ff7359410007f93290110006fc764c810006fc5359021006ff63d8554006bf6455110006dd7318154006fd658c420004fd76553100f6fe63552100067d6594220017bf4350810006ff7359421005797094a50006fe7608550006fe5498632006ff3059021066ff6590950006ff3018810006f661546300f5fe76d8d54004ff7694b100d7de4394930006dd6350c21007de328c410004fe72d8151006fd644c720005f87054810006ff325901003edd43d8d40026de531893007f7f500865001ef9501815109ebd54d9151006fc6518543006fd7318121007f562c4010006ff6218141005fd7498153007b
  | 8 => 0xdf976840100067d6554c21005fe728c540005df7348210006fc4398a50005ff754c940004fc7655131006fd64948210edfe7418553005fd73d9251005fc704c621006fc52181430eefe6454e2005fde438ca500f6fe6355220006fd7018554005fd7390951005ff735481002eee4218940004fc7259530006fd6388650006fd5418910006fc4398650005ff724c710147df4154d300edfe7418953026fd31181320077f7254e50004fc7654d100b7df5450e32004fc7059251006fe6248410004fc7650d10004fc7655121004dd73d8b1002efc7059020005ff7054f21006df74d8d20004fc72582312e7bc43d95432eefd42d8d54076bc6408510005fe71d9630005fd74d8420005fd7418a30187bf5290640005fd7550d20006fc6254530004fc7654420005ec7250c21005fc7648550005bf7448710006fd6394710006fc6598810005fe7108110005fd74d8e50004fd7518141007f52158021006fd6454b10005fd7388210004fe7608110006fd7018553007e521087100067d6554f20006fd6354810006ff6498021006fc6398154007ed42c8630006fc4218153007d47154d31006df638c940046fd52d8d50007dd7355232004fe72d8e10006fe75d9231004fc7158e52187bf539064008efd54d8d51005fd7418a50004fe7298650005fd7488530006dd638c82118fbc411814300fdc324c810005fd7284010006fc4398810004fe70185530077f7155152004fd7518910007bd4350950004fe76c8550007d5434c621005fd73d9250006fd6559021005f87054630004fe71d8152005fd74d8232006ff3259641007f421c4210005fe7688530007dd438ca50004fc7258e50004fd7418552165fa70d9630007f92008010004fc7059543004fc7654c10005fc71591530067f7559421006f66190420006fd6350b10006dd634c4202deff32d9153005fd748c950006fd6244010005ff7308550007cc7254e32005ff7644010074ff7650b21006fe72d9010005fc724c4100e67c5059543005fd7590a3102fbe5490420005dd7550d31006fd65885300bfde5454e32005ff7408550007be4190230006ff6118142005fe7608550006fc6598021006fd64546300f6fc535954304fdf3154e40006fc6398420005fc7154220006fd7398620006ee6288210006ff64d8153004fc7058e42005fd7518632006fc6294540004fc7650c20004ff7558c20006f66150420004f771595400dfbc4294a41006ff644c910007bd5450a301f7ec5090b21087bf4098543005fd7494630007ec7154b20006fd75d9232005ff7059021034fc7059420006fd6588640006fc6248010004fc768c910006de73181540dfbc7494a4121efd53185430065f6518d20005fe70985432eefe54d8d5423fbf5050e41006fd7518542005fc71480201efee5390b21005fd74d
  | 9 => 0xf6398021005ff7055021006ff7650e202e67f53d9543077bf4008640006ff6508540006ff4298021006fe7498810097dc318ca41004bf7458630007dd538cb10004fd7418550006fe63d9010005fe72d8e41226ff4318553005ff724c4100057d7508550007bd5450930006ff654c640005ff7358554007f772547102deff43d9153006f66194630007e5210872002dfd7490420006ff30d9642004fc764ca51005fe7218650006ff5198420005ff7255310137ec4194b20007bd4354940004fd7398b10005bf7448410006f56118554006fd6508420006ff40d94210477f5155230004fc7259010006fc70590210e6fe6550c20096fd30d9131005fd74d9630007bd43485402f6fc41d954300fdf328c810004ff7654a100eebc6454d1002dff7450420007fa5250210005ff7308650006ff62d8154005ff71502200a6fd43d9531107fb5290210005ff7354a400047f7559110117f74394710006fc3298420006ff62d8530005fd7418650006ee7218810005ff73553100057f7590650006fd63904200065c65d8d20027df3150c20077bf4308540004fe7298010005ff7050421004fe70d93212e6fd30d954324fbf3055241005fd7508530006bd7418810006fc61d8132005ff75505302677f3055151004fd7398a500e6fe65d9543005fc715022021efd73185430077b70552502bf7f4154d52006fd6494010006fe6254810005f77155010006fc5498632004fd7498a311d77f5218154187bc52906400bfdd538ca51005fd7550520005df7348540005fc7150d500367f5159420005fe7018931006ed6218954006fd648c8201bf7c7454e500077c7255250006fc4259410004fd7318810004ff7650a10004fc7059532005fc7250010005fd73c855000ddc7358810006dd638c010004fd7688410006fe7218143006ff6550520006fd6350420006fe7018951006fd72185432c77f3155152006ff3198021007de32546300afbf4298554004fc7059252006fc51982420a6dc32d9631006fd64c84200b7bc408ca41005fd7394a1009f3c50552412ddff7459153004fe71d8810007ef2198221007be4150520006ff6590520006fe7018542006ff63d8154004ff76548100dfbc4150e520bf7c758ca50005fd748ca501c77f5218153004fc7655110006fe6258a10097dc3254e41107fb5390210006fc3298640006bf75d9110006fe7018552006f661546200edfe7498153006bf73d9110007fa414c220097dc308ca41006ff6590930006fd6494220007f9414c220006dc63185200effb4054e40007e92008210005ff7154b20005fc724c640097de538ca41004fe765513002fbf4159020007f63188550006ff4098652005fe72d8e50004fe72d9010005dc7154e32076fc7259021006fc319825200cff764c210005ff7550930004ff7654c21
  | 10 => 0x93130f7f51d9153004fc7159020007bd4350a500077e3294650004fc76485300057f75506500077e528c650005ff754c941007dd438c950006ff30d9641006fc7458c21005ff735091006cfd73d8c21004dd7318154005ff7548540096dc639052002dbc7448420006ff6448630005ff7255010224fe71d9631006ff6244010004df7359121006fc4118953006fe73d9641006fc6218153006fc4018953005fc7054e41005fc7054d41005fc714c020006bd541854014fde548ca300047d75d8143006ff501894321efe3018543005fd7598143004fd7655221006ff644c81012fec3194b20004fe72d971009e7c50d9641006fd3218550005bf748ca41006fe6218553005dd7550d30006fc7650d21004fe7198a400077d5454b10006ef6208530166f93018153005ff7250f10004fc764c42030efd50d9153006fd5458c20004ff7654e200b7bc4155232005fd7418153006fd6390410005fd7494530006f661c8720006bf6450d100edfe7418153006ff6550420006ff6118132107f85290210004ff7690b10004fe7655230006ff6590420004ff7359640007dd4354530006fe6250010007f820c4210006fd65d8143006ff5198a300e77c5050e51004fe7650c10006fd648c010004fe70d9631006fc4198252006fd644c620005bf7448640006fc5198232007bd5490520005ff7550e21005ff715942002ebc42590200f6de63d8d54004fc725864021eff5318543005fc7155232007b47155241005ff7050e21007dd538c810006fc4298650006fc7159420005ff754ca41006fd6559020005fc7150e50006fc5018943005fc7258c10004fd7518810006fc73590200077e5254b10007dc7150d30005ff7355010007dd6354e4101e7c5059410006ff7650e50006ff5359010004fe76550100077d5348650006df6350d20005fd73c8650006fe7018953007747155151005fe71909302eefc54d8d54005fc70548212f67f54d9543004bf7458420004fd7398a411b77f4394a50004ef72591310a6fe32d9531006fc3159640006fd6354620006ff6098021007f9544c220004fe7218554004fd73d9410004fd7418151006df6354520006bf6450d51007ec21c822000efc7058c10005bf74487200f7dc30552322e7dc43d9543006fc4158e500077d5454520007f63188650006ff5218143007f8714c220005fc7050e210f5fe7318954005fe70d9631005ff744c42021edc3218543004fc7159630005fa708c640006ff5158e40007f55108710006dd7318554004fd7498321007f5329451005eff6550d5022fbc5390a41005ff7254710006fd648c220006f56118420004fc7258d10005dd7318810005bf744ca41005ff7458420004fd76c8010005bf73551400f7de5355232006fd64c8630006fc3218154005bd7418953006fc7655232006f
  | 11 => 0x8f7f5454a31007de3294630006fd6350a10006de3298231006ff43984200067f65549100f6dc6355120036ed7218152006fe6398021006fc3159421006fc5218543097dc3290630005fd74d8c2012fec4394b20005fd7188020006f66194620006ff40980210047f7558231007ef2158021005fd7390b10005fd7390a51004fd75d9021006fd5458c10005ff7150f2022fbf3090a41005ff7408650256fd7518554007be5290a410b6dd43d8d4203fbe5450a30006fc6218151006fe6288710006ff421881000efc7158c10005f870544200efbf4059543006f671d9641005fe71d9250005fc7050821005fe72d9250006ff6458810004fd7498252006fd7598420006fe6248010006fc6559020004fc7654e402e6fc43d9543005fe7088421005ff7590520004fe72d9230006ff30592520057d7494650004fe76c8530004ff764c620166fd7318153006fc5259010004fe7298251006fc3098642006fc61d8154006fd6590410004fd7598021006fd43980210075d538c951006fe71d8c20006fd5498a31005fa70c872009f7c5190650006ff5098642005ff7150b20005f87055310005fa7094a30004fc7259540004fe7118930004fd7398a10004fc7059642004ff7458e50007ed21980210057c7254e50005fd748c720004fe760851005eff658c950006df63c8520006fc5158c21014ff7650710006fe64594202deff53d91532e7df30d95430057f7550a500f7dc3155232007bf7550d40006fc6294530007ed42c853009fbd5494a41004ff7654420007be41900201bf7c4254e50006ee6208710006fc5098642006ff6454530007ed4394920006fd658c710005bf7355241006ff6590910006ff5218543006fd7608650076bc4159021004fe7650d520077d21941500073d5454940006fe6518143006fc4159421005ff7355220005ef7254c200073d5450a50006fe539864207e7f5359421004fc768c8102eefe40d8d5405fdc638ca50005ff7148020006ff6350550006ff63905502b6ed42189540067c6294150004fd7498221005f87054530006de3218532006fe7118143005f970c8420005f67108210005bd7418420007dd538ca40007bd4354a412dedc32d9153006ff658863007e7f5459421006ff31188100057d7550d52006ee6208010026fc7058c202a7bc3055142006fc5398810006ff7650e10004ff768c7200eefe6454f212e6fc31d9543004fc7259641006fd7118943006ff61d8152006fd711894030efe50d9153005ff7348640004ef7648020007ee6148020006ff5259010005f87054c20004fd7318910006fd7318550005fd7494420006fc7259410005fc7255110006ee62884100077d548c650004fd7598232006fd6488210006ff3098810006ff5098a31006fd7318542005ff7254410005fc7048530006ff655
  | 12 => 0xd54d915230efc52d9153006fc50d9021004fd73d964204efe32d9130006ff7458c10006fe6290650006be7418810006fd6348650006fe62506501efec5390b21004fd7318550005fc7054e42005ff758c910006dc6318121006ff7655232004fd7655220006fd7218530006fc32d9010006fe53d902107efc7159421006ff64c8530005ff7258c10005fd73908100067f7559543007bf7550e41006df6394520007dd434c620016bf4359010006fc7558c20006fe3298021005fe70d8a310e5fc7558543006fc62181410377f51550200079d434c540006bd6490a10187bc50906401efef3090b21004fe71d8f20005fe71d9230006fc641895308f7f5255231006f66154420006dd54d8d21005fc724c010006bd6450420006fd648cb21004fe71188100067f6518520005fd75180210eeff4259543006df6318121005fd75d9021006ff4198232005fe76c85500075d534c650006fd5398720006fd73983210073d5454a410067f73d9520016f64118540005f870550100077d3294650004fc7059641016f54118540005fd744c6200bf7c5055232006ff7654b10006dd658ca3005fdc32d8e50076bc6459021007df7150e32006ff7650720006ec6290930177bf3155140005fd75d8241005ff7254010046fd54d8d50006fd749881008e7f5459631007b77150e41005fd74d9420004fc7694910006fc41d963017fbc3090640005ff7550d21006bf70d9121006fd5398642004fc7158a40006f66154640004fc7654a41007ed5250720097bf4354e41006fd65c85400a7dc638ca51007ed42c8420006ff21980210debc41d9642006bf648c910005fb705481017fbe5390640007eb2148020006fd3218540007ed5290720006fd7518520005ff7150e200f6ff3159543006fd6448650005fe7018543004ff764cb10007dc7154e32005fa7008540007cf7250e32006bd6455210007f93088210006bf6490520026dc3058c200eebc4159543006fd6548530004fc7694931004fe70d9021005f970884102b6fd7518954006ff31d9642006fb6098153006fc6218154007fa6148020004fc7058e522defd31d9153006fc64594210069c6418d21005fd759802128fdf3018943004fd76880100f6dc6355121005ff7259410005fc7050931007f56244010005ff7358810006fc7654d10006ff6454d21005fd730821006eee3218931004fb76480200e6fe6550e21006fc3059251016bc6459010006fd6548640006fe6250410007bc7250d40006fc7458c200057f7355151026de5358c20006fe7018543006fe6290410006fd6494b100069c64d8d21005fd748c620006fd3198221006fd7018943006ff4058e52097dc32d8e41005ff7250c10006ff4159420006fd759872005efd43d95300bf7c508ca510e5fe7598943007ec6288530004fc7058e41
  | 13 => 0xf10004fd7598630005ff7648020007f9514c22019f7c3294650006fd6354420006ff6350951007fa6284010007ef218872002eed4218940005fd7418632004fd7498620004fd7650e10006fd7398720005ff7448650006fd655062001ef57118151006ff4018810056fd52d9150005ec7258543067bf4390650006bd6455020004fc7694940006fd654c420006ff53982420077c7254e50006fc3098a51004fc7159542007bd21901400eefe6454c21005fd7394b10006fd6558420006bf6490951006fc64984200067d6554810006fc4398251006ff654c540006ff52986300077d5408650006fe62542100077f758c6500077d5350650006fd7498b10006fd659062027fdf5050e320057f758c650006ff6550d200077d5390650005fe7008710006fd7418953006fd6408010004fc7655132005fc7155220004ff7655020004fc7259640006bc6418910006fe6359021006fe76085100057e7294650194fe70d9640006fc4098a51004ff7650c210047f7558d1000edc3058c1006ede43189310357c7548020006ff31d9420007bd4390520004fe71189400077e5208650004fc7654540006fd6590a10006f76198553007f62198021004fc7650950004fe71d894002cff7650220007bc7250e41207dc4054d310a7de4394530004fd7598620004fc715964026df671d8e51016fe421814100ede5358c1000dfa70d863001f775194410005fd76887200077f7255250006ff7059021296ed3218953006dd4318931005fe7118a30006fe6154220195fa70d96400d7df3050e520e6fe6550e200edbe74d8553004fe7688650006fd7218141006ff6458553005ff744c910004fe719824200ef63118530005ff7448550006fe72185530f7dc3255230006f671d9631006fd74d94200067d6554f2126ef55118553006fd7418132005fe70885300067f6555130006ff62d85400cf7c5190a5006cfc7158c21007dd439453001e7c6559410005f9700841014fdc548ca30007bd4394940006ff6448550004fe70d8e21006fd6590810006ff65c8530006fc61d8153296fd7518953005fc71581530b7bc428ca41006bd7418153006ff6218540006df7358c10006fd5498810007de328c0102f7bc41d95430077f7355250007f631485502dcff74595432afbc4118943006fe5398a40005fc7055231006fc54d8c200067d7518943005ff7354910006ff50d9021006fd7518543005fc7155320006bf6450910007dc7054d31005f6718801010ff73294710006fc4359421004fe72d8c10005bf7454a412defe30d9153006fd6394620006fd644ca10004fc7650e52006fe4218151006fd5398620006fc30d9021004fc764c810006fd4298021004fc7650931005ff754c7200067f6594930006bf7459010006fc4398252005f67190a31004fd7498a100ceb
  | 14 => 0x7bd4394a41007ed21084202f6fd40d95430f6fd75d8d54004fe71d8943005ff7254e102eebf42d8d540577f5154e40006fe6284010005bf7454640007bd54c8540006ff62d8550005df7550d31007bf7050e41004fe76551322e6fc53d95430047f755824104fdc328c640006fc4259421207dc7454d31005ff7155020005ff74486303077f52d8d54004ff7654720006fc5198a30005fe71d923202ebe64d90200f6fe635531011ff8548c2202e6ff30d9543306fe51d8d540065c6518d20006fc30590100477f5454a30004ff7359010005fd72d9010005fd739481015dfa70d9230005f576c42101b77f4194a50007dd538c910004fe7218530006fe32982412defd30d9153006fc50d8c21006fc5059010005fd7308550004fc7650a510be7f545963202dbe7418420006fd6458c10006ff54982320c6bd43d91320067d6554e21006fc5498021004fd7398a40005ff748c6202eefe41d8d54004fd7498650006fe5359010005ff7355110006ff7654e41006ff50592322dfdc32d9153006fe6294210006fc7359021006ff50d8c21006fc6118142005fe70d9021007bc7050e41005bf7444010006fe62d855306fdc30085302d77c5018954006fc4159632006ff6454931006bd649082007f7c7508650006fd701854300edc3158c10005fd731855429fbc5050d42005fe7090931306ff50d8d54004fe7218151004fc7654530005fe70c8421006ff6354941006fd63d8954006ff4218153006fc6250910005fe7094941006f976c4210006fe7118954006fc40d8c21006fc7650e50006fc529863006fde5308530006fe7018943005fd7318241007dd5388530004fd7498720004fc7694941006fd6388210005fc7054931004df7358a51006fc5158e40006fd6390210007de3290230006fe619422005efe32d9530004fc7654d20006fb6098021006ff6550d10006ff65589430e67e65d9543004fe70d8554007d87050d30004fc7655020006fc6498153006ff4258c10005fe7290550005fc7050d212777f5218554004fd7318141005fd7388010006fc3018554007f47150a10006bd6455230004ff7690420004fe72d8154006bf7459020196fd41181542debf43d9153006fd7318151006bd4318540005fe7094a41005fc7150c20006fc6248710006fc3198a4030eff52d9153006fe7218554006fd648c821004fe71d89530077d750855007e7c52594212cefe5418953226fd5318553004fe71d94202f6fc42d954327fdc5050e320eebc6459153005fe72d8e51006df6350d521cf7f3255250007f63148650005fa70949300067f6550520006fd6508710006ff6550930006f661c8420006fe7118940005df73480100067f6590520006ff42d8c10005ff748c9100067d6554e4106fdf3054c210dfbc4194a40006fd7598810004fd765
  | 15 => 0xe5250720306ff51d8d5407e7c6508510004fc7648640004fe7118950005ff7250d10005bd7408540006fc6498553005fc7254540016fc70590100077553547100677f5490650006bd6450e10004ff7690810004fd7688420005fc7055021046fd51d8d50025fa70d8a30006ff5458c21006fe72d9641004fd7418532006fe6248710004fc7650e51006ff5498231007f53188550005fd75c8530004fc7654d4026efe5018553005ff7054821006ff6558c100067d6554c20006fd61c8020006ff658c9102f6fd41d95430067f655511006edc3258c21006fe614c72003fbc6490630086fd40d8d41004fc7058a31006fd6188020026de63d8c200f7de7355232004fd74980210efbc4159153006fc63590200f6de43d8d54004fe76086300f7dc3258d54006ff4298810016be54185400077e52549100057f7454e50006ff63181540067f6554d40006fd6559010006fd72d9641006fd751891002ebc64081100077d5390a50006ff6548630147dc4154d30005fd7088421005fd7508540006ee6254810007f251901102ce7c50189530077c7155250007fa3250210006fe43d94202e7df31d9543005fd7394a40006fe614c6202eddf7359543005f47158154005ff7550d2028ebd74189430067f659491001cfc715941021efd3018543097bf4390630004ff7359410005ff70506210defd40d9542005fd74c8720004fc70592310d6fd43d9532005fc7155132006f6619442029fbf5050d4201ef55118550006ff3298420006ff745942105fdc3250e50006ff6518943166fe6050e500067f65d8520005fb7644010005fd7388550004fc7259110005fc7254d40004fe7655120166fd4318153005ec7250e21005ff7255110005fd7588530005fd7318650006fe7098a10006fe43980210047d7518810005ec724c620006fe5458c201e7f7508c621004fd74d9632006ff4259410006fe7118930006fd70185520a6fd32d9531006fe618c220005fd730865026efd5018553006fd5218530016bc41181410057d75c86502b4fe72d964209f7f5254e41006bf6488110076bc4259021004fe70d8943007787055250006fd6390220004fe7118142006f66194640007f87054720006ff32986401e7f4508c6210067f6555120006ff51d9232006fd64d8420007f621c4210004ec7259530006ff3159252005fe7290650006fe7098620005fd7590530005fe7008720005ff7050d21006fd74d96320eeff4059543006fd7118154007bd548c940006ff3198810004fe7654d41004ff7359021007de314c5200aefd40d9541005fd7590931006fe7598420004fc7259543007787054e50006dd6350f10004fc71592502aefd4018943004fc768c940006fc5018543004fe71d9320005ff7454c20005fd7494a10006fe74d9420005ff7454910007ef7050b21
  | 16 => 0x9121006fd7018951006fd73181420067d6554e42005fd74087202eebf40d8d54007ed4354b200057f75482100a7dc308ca51004fc7654d21006fc6288110006fe6154020006fd6590720006f96018153006ff6454d10006fd6550720007bd4354540226fe3018553005fc7254d41004ff7655220166fe3218153006fd6390650004fd7318954005fc7254e41004ff7650c10007f53188650004fe7608520007f22044010006fc5059232006dd638cb100f5fe739855421fdf30185430d7df3198953006fe4398810067bf4298154004f87059532006ff65d8143006fd6550e10005ff705522106fdf3008630004fd7418530006fe6254b10006ff6548640005fc7054f21004fe70d8553006ff6588540005fe71d9020006fe5458c10007bd548ca410077e5154520256f541185542567d751855406cfc7258c21006fe6498420006fd7018532014fc76900101a77f43946502defc30d9153255f671d9641006fc5398642006ff6598810006fc54188100067f6590910005fe71d8c20005f67108010006fd639442030efc50d91530defe41d9542006fe5498a31004fc7158e42006fc3259020006fe6254410006fd62d8143005fd7388650006fd73984202f7bf42d9543006ff6550910026ee321893009f7f539065021df671d9231006ff30986422aefe41189432aefd4118943004fd75984200367c5018950004fc7058a41006df6350d2128fdf3118943004bd7418153005ff7354640004fd7598a30226dc32185530defd41d9542004fe71d8930016fd4318141006ff6118520006fe4359410006fe74181530057d7588650004ff7644010005ff7354620004fd75d9010005fd7518143006bf6490530007df7358810006fd635065006efd5318532006fc4398a51006ff3218154007df7154e32006fd6558c20004fe76c86400067d5318152226fd7518553006fe6498021217dc518ca31005ff7550520076bc4218542006ff4298650004fd7398620006fc7058c21004fd749823108f7c505523130eff50d91530dfbe5494a412a7bf3055142004ec7258d10076fd4018941006fd6550c10006fe72181532f6fe41d9543007f95390110007ee628c810006fc4298251006fd4318151006fc42596310e77c5150e50005fc7244010004ff7650620006fd639802100ef930181310077f758ca50006ff62181541dff4408c621006ff6418153007bd529064015fbd7418143004fd73185522defe53d9153004fc7654910006fd6498810005ec7254c20005ff704c8210a7de538ca510077d6555232007ee5290720004fd74181210eefc40d915308f7c5094a31097dc638ca41004fd7654e10006fd6218143006fd6508630006ff3059421006ff3198a50006fd539842007e7f5059421006ff4098a310077d5454910006fd53986400079d4390530007e
  | 17 => 0x6ff764c620014fc7159010004fc7690951005fd7308010005fc7150b20006fe42181310367f5459420006fc4159420007ec2148020006ff6558021005ff714cb20005fd7494520006fe6194020006fe32181410eefc64d9153006fe76081100077d544c650006fd6394410005df7550d30006fe4398a50006fc6250550006dd648ca310067d65550100067f72d9510006fc62d8540006fc5458c20005ff754cb10006fe73185540077d548c951016f94018141006fd65d8021006fc7654d20004fd7398321004fc7654940006fc6290550007bf7055241004ff7459420005fd764c810005bd7550d40004fd75d9231006fd658c810004fc76949300677f5490a502e7be43d954309f7c5290650005fd7590930004fd75d90200cf7f5390a500deff6494941197bc4118154004fd7398642004ff768cb10006fc3218554004fc7159232005ff74485300067f74d95102aefd541894317fbc5390640005fe7118152007f66190420006bf64d8910006ff5159230006fc62185400edfc7458953006ff40988100eefc54595430d7df3150e5209e7f535964100fdc3254c10007f9308801007efc7259421005fc7054d42006bd64904210077e524c650006fc611815418efe4118143007f52198021006fe659842009efd50d9151006fd7418153006fd7598a10004fc7159230006fd7018954006fc5298231006ec6250930006fc6218143004fc76505302f6fe42d9543006fc7650910004fe70d854200fdc308c810004ff7655320056fe52d9150004ff7458e51147dc7454d3009efd53d9151006fc7650420005fd7690420004fe76c8540006fe3218151004fd765502115ef93018143006fd6350810007f66150420006df75d8d21006fd3298021005ff714c220024ff764cb20004fc7058642004fe70d8552006fc21580210e5fc755894300fde538c810006ff64d8953006fd760855015fdf31181431bf7f4254e50005fd75d9231004fc7159532004fe7098642005fd7390910006fd648cb100d4ff73d953203ebc41d9230006fc43d9410006bd6450c200057d7394650006ff5159020006ff3198252074ff7650621006ff41596300a7dc318ca51005fd75d8632004fc764854030e7f52d915306eed3218931006ff3059251005ff744c520006ff61d8153006bd6455321005fc714c950006fd65904210077e518c650005fd758c540007fa2008310006ff7558c20006bf644c9102b67d7518954006fe7118132004ff7654c10005fc7048540226fd7318553005ff7350520004fe71d8950007f55188710004fc7608540006fc4058e51006fc53d9020006ff5298231007df638c810007de218c130006ff4198a30006ff639842015efd741814307d7e7518021007be428ca41006fe72d95430f6df3059543004fe71d81431cf7c7355250006bc70d
  | 18 => 0xf7454e50006fe6158420004fc7159540004fd75d8c2108e7c50d9631004fc76552300e6fe6550f2012fef3194b20006ff3159250006fe63188102cf7c5018953007dd534c540004fc7259251006bc619014009f7c5054e41076fd5418941157df518ca30007dd534c520006ff6550630006ff5398420006fe6250810007747154d5102ebe5459020027de534c420005ff7050b21005fd74d865218fbf4218143004fc7258c102e6ff31d9543006fe5218530004ff7559231006fc54d8c10004fe71982520f4ff7359543004ff7655321006fe618c020005fd7498953006dd6350e10006fd4398252004fc7650d51006fd6590821006fc3159420004fe7298630004ff7650c20007df7550e32005fe7294540005fc704ca41006fe7608520005bd7390a41014ff76502100377f5159420006fd6550a100b7bc418ca40006fd7518943086fd54d8d41005fd75507200edbe7418153016fd4218141006f461c8540006fd6590b20006fd7318520006ff63549100367f5318152004fc7690530004fe70d91532967d75189530fff85390210006ff51d8c20007fa514c2200067f6550d20006ff6590630007be4150620026f93018132046fe51d8d503077c50d8d54006fe6288610005df73487100067f65545200076d5454b20005ec7258153005fe7188020006fc5398a402e6fd74d9543005fe71c8020006fd6550810006fd6390020007dd534853006edc32185320367f541815207efd5418951006ff3159640246dd7318543005bf7590a412f7bf40d9543006ff5398640004fc7654930004dd7318810006fe7118154007f92084010004fd73d96410057d7550d5109efe50d91510073d545454000fdc318c81005efd32d9530005bd7550e41005fd73d8650006fd7118953006ee6290a312d7bd7418954006fd6550e20006ee6288710007bd43c8540006ff6350950005fd744ca100067d6594020006bd6490b21006dd4318930007ed52c872002cfc725902007f7f50594212defc43d915304efd32d913005f7d5350e50004fd74986300b7dd438c94004fdc308ca40006fe5498810006fd701893101ef65118550004be7619121005ff7358154006ff6550d210aefe42d9541007f721887100bf7c518ca50006ff5158e42006fc53d9021005fc7148210006fd6494b200edbe7418953006fd6454810007be41507200c4ff73d9132007ef2158221006fd4218151006ff6494931006fe614c220004fc7655231005fd758c520005fe71d8e520367f53594200a6dc6394520004bf745865002fbf43904200057d751802104fde538ca40006ff7559010006ff62d8141006ff658ca41007f94088210026de43189302bf7c7454d520076f7554b20005fc714ca50005bf7355142006ff30d90212cefd5418953307bf54d8d54006fd658ca1018efd4118143
  | 19 => 0xd300b7be548c940006fc7459420097bd438ca410a7df3050e51005fc7055131006f76198420005fc7150d52005ff7350a500eefc42d915302fbc6490420007be4290720006fc52984200067f65945300067d6554f10006ff4258e502aebc4118943006fe7118953007f93250210005ff758c5200ce7f53596422f6ff42d9543006fd6390010006fd63880100077e5108650097de438ca41006fc4359420006f56118543004fd7398221005fc7648530006dd638c4210b7bc748ca41004fe7608540006fd7418950005bd7418153006bf7459021005fc7254e100367c52594200b7dd438c941006fc5298640007de328c550004fc7650c21005f671909310b7dd438ca4105f7d538ca50006fc615452006efe3018532004fe7218141007bd54906200eff74154e41005fe728c6400077d5454a31006ff6218550004ff7459631005df7348720004fc764c650036f95018152005ff7454d21226fd3018553026fb764c2200eefe6454e210079d4350931006fd72d9410006ff5298640005fe71d8252005ff725071006cfc7118910007bf7550d420077d53c8650006ff6218910005fd71c8020006ff6218530004fd73d90210067d5418151004ff7654f21006fd3298241006ed6208710005fc7250e10004fc7654e4218fdd7318143005fd7318154006fd7418152007f72188410005f47155210006dd648ca30006fe6250710227dc321855300ddc7348410006fe62c4010006fc3298021006fd65d9021006fd72d954330efd52d9153006fc4198232005fe7088540007be5290640005fe70d8e420eefe6454c10005ff7350950005ff7254f10004fd7498632006fc3198242006fc5498a310e5fc7558143004fd73982410063c65d9110006dd6350e20007b95450210006ff5498a30006fe6294410006fe6559021005df7348410005f47150c21006ff4398652005fe701894307e7e65d942108f7c50d9631005fe70d8a410077d5454720006ff6388540005bf7458420007bd5490720006ff5298420007f4214401000ddc73480102d6fd50189540067f6550d10006bd649082104fdc3254e40005ff7454630004fc7690910006fc6218554006fc7654d4003ebe545923018efe4218143006fe62907100cf7c5290a50006ff32d9010005fc704c941006ee6294810006fe614c420005fd71d9420006bd6455021005fe7118a50005fd758c9402b7bc411895404fdc318ca40006fd70d92310a7dc3294630006fc6318154006fc42d9410004fc76509300067c65185200477f52552302afbf401894300efc1058c10006ff7558c2101efd5318550005fd73949102f6bc41d9543006fc5458c10005fd7390550006fe329865007f7c50550210eefc6454d20004fc7259230006fe43982520377f5194420004fc7259131005fe7008510036fd54189500077
  | 20 => 0x5fd7398154006ff31d9020036ef7654b20006bd6450f21005fd758c9410b7dd5450e320defd43d9542004fd7498a510077d5354940005fd758ca41006fc4018553006fe7198810005fd7518543005fc7150d2030e7c50d91530067c6518910007d7734c6213067f51d8d5412fee4394b20006fd52986302777c501855400efd4318131006fc6244010005fc724c550004fc7158242006fe4198221006ff654c91018ebc411814304ebd43d9130005ff7250410005fe72d9641005ff7590720005ff7055121006fd741895109e7c65905202e6fe43d9543006ff63d8954006fc6318954004fc7654630004fe7688510005fc72542100057c7154e50077bc4008540006dd638ca10006fe71d9630006ff5058c21006ff5098a41004dd73d8954004fd751853006edc6358c21006fd7318141006fc6118152005fe70d853202efc7259020006bd64907100077f7590a50005fe70d9543006ff6548540005f47158943217df548ca31007df7050e32005fc7158953006fc4158c2105f7f5350e501c6dd7318153007be4250a1000dde7318810067bf4350a50005fe70d96320e6fc6550d20006fc5058c21006fd71d963030f7f52d91530077d5488650006fd5318540006df648ca31004ff7558e410cf7c5054e42004fc7258e51006fd6350720007b87050d40004fd7498420005fd7418252005fe7218810006fc3159642005ff7154020006fc53590100677f5450e50005fe7118930005ff7254c10006fc3098a41006be4218542006fc5498810005fe70d96420dfbf4050e52006fc4058c210077f2194150005ff7358954006fd7688610006ff50185432ceed5218953006fc5098a41004ff7655221006fe6058021005fe7218154007de328c6502e5ff7559543006fd5498b10004fe70d923105fde6350e50006bd6490210006bc6418121007dc7050e3207cfc7694421006ff5198021005f77644010006fe5398a41005fd73906500367c5218152007bd5450a102a7bf3155142004fc76945300377c5154420005ef76480202d6fe501895404ddc734864002cfd74d9020005fc7159020006fc7650d52005fd70d8c21127fb518c220006fc6398810004fc7159420006fd7118930006fe4298251004fe71d8e20005fd74d8252006fd6218810006fa70d9630007f87054b10004fd7598720006ff5258e40007ee61c80200f6fe635502019f7f3294650006fc7654d2100ef53118530005fd73c85400eff84054d40005df7348640005f87058953005fd75c8540007bd544c940005fe7118950007d47150d31006fd6590a310f5fc7358554027dc314c420007fa72c4210006fd71d9420005fc7154c20306fc51d8d54004ff7648421006ee62908100067f65c85200eefe6454e10006fd6390720005fd7398810004ff768c620004fc765494113fdf515
  | 21 => 0xd645802105eff658c550006fd71d8d54005ff7054c21004fd7318121004ff76948100bf7f548ca50005fe72d8550006fd65c8640006fc3259021006ff61d8132006fe7418953006bd6490020004fd73987200077f7590650005fd7590520247bf42185430979f3050e41005fe7298554006fc4259420005fe70d92311ffdc7550d31006fe63594102f67d54d9543006fe43594212e6fe32d9543006fd6398420006fe6598021004fc7159132006fd5458f200077d544c951004bf7458652005ff7590910004bf7458632006fe6518021006f576c8621007fb7250210004fe72d8141007dd5390530026ed3218930004fe70d8931007fa6188020004fc7158c20005fd7550d10006fe7688110005fc724c650005ff744c950005ff7550f21007bd7454e41005ff7155120006fd6494810006fc3298241007dd5350530007ed61480200e77f5258d54007ec724c620006fd7218554006fd648ca500077f7355152075f671d8a41004ff7459630007bf7050d42004fc7654d42007bd544ca41006fd4198221024fc768c0200f6fe63552210477f5454630005f87058554006fd7498021004ff7559232005df7454d31006fe614c020005fd73945400edfc7418553006ff6458153006ff42982511b77c4194a50006ff41d9632006ed6218943006fd64c8650004fe72d8550006fe70d8c210f7de4355232005ff7558943036ed52189500befd50d8d52006bf6454d21007f82044010006fd658ca40007df638ca400075d5354931005ff724c210004ff76907200b7be548ca41006ff5258e41005fd7518232005bf7448421006fd6550f20006fe6558c100067f65945200bf7c50d9632006fc4298630005fb7648020004fe7018941026df3158c200067f6550910004fd73d9420254fe71d9641005fc7154b20007bc7050d422cefd5118953027df318c420005df7358810004fd7418131005fd7318a40004ff7559020006be4118141006fe62880102defc53d9153006fe6290010005dd73180212deff30d9153006fe72d9153007df7054e32005ff768c810005fd75d8242006f6618c720005fe71d8950006bf64d8121005fe70c862102ebc41d9020024fc7258c20005fe7218540006ff30596412267d7518553004fc7259541005fd75d8c21006fc6258154006fc61c8520006fd6588710005fe70c8530006fc6118153006ed6208410004fc7694540005fc7058943006fd65d8c210aefd43d9541006bd5418542005fc7250d51004df73595210f6df3159543007dd218c130005fa7008710056fd51d9150007f7704c621004ff76553100067f658c910004df7358910007ef2198021006fd7418151005fd74d8a50006fc7655130004fe72d85430077d5350a50004fd7398420035fa70d8a500063f6519110006fe7118943007ee624c8100067f7559410
  | 22 => 0x8420076bf4059021004fc7650d210de7d54d9542006fd5298720005fe70d8941306fd50d8d540367c5059420004fd73189500e6ff51595430b79c4150e3202fbe6450420005fe7018542005ff7348550006ee6254a40006fc51d8c20006fd7608610007bd4390720004be76191100367c6508110006fd658cb20207df4254d3110ff44394710006dd6354c21007f96148020225f671d9631005fd7318a51006fe6598810006fd5458f21006fe74d9632006fe5398640006fd75d9231004fc7654640005ff744ca50004fe70d85432f6fd42d95430077d5354941004fe7118154006fd65c8720004fd7498652004fc7259510006fc7654520005fd73d8810006ff62d8543007b94350210004fc70595420067e7518810005fd73945200cefd53d9152006fd654c810006ff6318554007d9434c220005fc70552210edfc7458553006fe3198021006fd6358810006fd6588630017bf4255010006ff4059421006ff648c950005bf7448550006fe63594210eebf4259543094ff73d9131006ff658c941005ff745855302fbf4190420004de7618d20007f670c86212f6ff40d9543006ff73590210ae7d54d9541006fd73d964006efd3018532006fc7650d500067d6594b20017bc4250810007dd438ca10006ff4018953004fd7498251006ff31d9640004ff73596420067f7559420006ff64c8550006fd43982511af7c3194a50006fd32181510057f75480100047d7598910006fc6218543005fa7008720004fc7258251005ff7048421005fc714c820006fd72d9010036fd5118950004df7359120005ff7454420005ff7648421006ff6358810006df638c951006fe6148720005ff748c9500077d5354a41006fc5158e420e6fe6550e10005fe7098943004df7358a50006ff53d9010007dd634c81000efe3218131006ff3198a40006fc6598943006ff62185530befe50d8d52006fd6388640006fd644cb100079d43509302eeff41d8d540eefe6454f20006fe63988100bf7f5198953007fa2008110005fe7118420004ff7650e2002efe4118142006fd6458c21177bc3255140007bd645523209f7c7590650004ff769472007eed5218951006fd6018021006ff42d96300e5fe7598143004fe71d9220076bc4118941006ff4398021005fc7150e52005fd7518a31004fd7498232005fa7008410006ff6418953004ff7648420005f77158943006fa70d9230005fd76c8710006fd64547200e77c5250e5015efd4318143006fd74d9630006dd638c62105f7f538ca50005fe718c95006ef7764c6210b7bf4055232004fe7650d50005fe72c4210006ff4259631006fd54d8d10005ff7454530006ff5118810006bd6450c21005fa7090a30166fd3218153006f671d9231005fd7588540006fd6454e10006df638c520007bd6450420005ff7454d20006f
  | 23 => 0xbfdd538ca50006fc415963007e7c655942100efe3218530006fe3298251006ff6354940004fe7654c20006fe74d9630006fc4198a30006fd6550420006f66108720005fc7250e51004ff7655010006fe7398420006ff7559020006fe7098810005fd75d864204fdc638ca402e6df30d9543005ff7050f21004fe70d8953005bf7550d40005fd72d94100c6fd53d9132006bf7459543066fd41d9540004fb76440100075d5354930004fd75d92300067d6594410006fd4318121005fe70d9232005fa7094540005ff7550b10004fe7654c1005efe31d9530005fe718ca50004fe70d96410c6fe30d9132004ff735942115efd7318143006fc52d9010007fa6244010004fc7654a30005ff7348650247bf4018543006fc62d8141007bc7055241006fd65588102677c325515101f7f5254c10004fc7654e4124fbc3255241005df7454d30005ff748ca50005dd7318554005fe71d9632004fe72181310debc6494910004fe768863018ef94018143006fd6454c20006f561185531af7c4394a50005f771508100bf7c528ca50006dd6354e21005fd7518943006ff62d81510067d7518810004dd73d8a10006fc539824215efe3218143005fd748ca10007bd4350a100bf7e6555232005fe71d94200f6fe6355021006fd7118950007bd4390620005fd74d8553005ff7690420005fd7318640005fc7050f21006fc7459421005fd7418652005fd73d9010006dd6350c20006ee6250a310067e5118151004fe71d8d54004fe76552310f5fe73181540cefd50d9152005fe72d8640006fe6058321004fc76945200057f7544010096fe32d9131007d87054d30007f662c40100067d659482103fbc41d9230006ff6348540006bd7418953006bf6490630006fd64d855307f7e7508550004fe72d9631004ff7650420007bf2190140006ff52d9010004fc7058c2121ef53118543006fd7518941004fe70188100aefd42d9541026fd4318132005fa7008640005fd7488210006fc6118143006fe5398420004fe7098a310e6fe6550f10004fc7058d21004fd7398242006ff6218554005ff7550f10005fd73d8a410efbc4054e411cf7c3155250006ff6454d20006fe6254a10006fd6590b21006bd4318542005ff7648410004ff7459410005bf7448650007ee528c5200edfe7498553006ff5158c20006ff5098420006fc3098420006fc7558c21006fc4098420006fd658c821005fe7018632006ff654ca41066bc41d96400067d6555021017bf4290810005ff754c910004fc72582412efbc41d8d54005fd70d9021006fd64c8720026de4358c20006fc7359410096ff648c941006fd4218131004ff7650e10006fd6350a50287df4154e320067d6555320006fd654ca100bfdd538c95030efe52d9153006fc6418553006ff6598420006fd3218141006fc509
  | 24 => 0xc72552500e77e7550e50006ff42d9410067bc4090650006fd7218154005fc7250c10006ff42d9631006fe71d8d54006fc7655120006fe6559020005ff7054421006fe2158021006fd7598b10005fd7688420005ff7550f20006fd6454620036ee5218950005fc704cb210077d5448650006fc5198021006fd3298650006ff6358154006f56108720005fd7418232006fe72d9410006bc72d911006df671d8a310afbf4250e51005fd7494910006fc3259410004f77159120076be5418542005fc7154020007f521c4010007ed5390921004fc768c540007dd438c951007be3290640005fd76c8210004fc768c9510377f5354420006fe624401009f7f5354a4105f7d534ca50004fe72d93100057d7518420005fc7254710207df4054d31006df6308520005ff7254d10004ff7694620004fe7298910005fc7259410117f44294710016be64d90100dfbf4394940004fc7159530005fc7254f100f7df3159153276fd5318554007df7454d310377f545442007eff6508550006fe62502102277d7518553006fd64d8c202defd73d9153007f47254710007dd434c550007de314c620004fe701854326efd521855313fdc7550d30006fc6398021005fc7054a4113fdc5150d30004fe70986520e5fe7598543006f6618c420007ea6288020004fe7650c210eefe6454c20007bf7055142004fd74d8c21086fd42d8d41006fc4298231004ff7559021005fd7508710006dd638c820004fe76885500067d6555231005fc705494130f7c50d9153006fe529863000ede4358c10006ff6518543004fe71d814207eee5218951006fe72185500577f5254e4007dfe71885502adee72d8e420067f6588110004fc764c941006fd7118152006ff6498153006ee628c8102eeff54d8d54005f47150a10006fd7318152005fa7090930007ec7050b21007bc7255140007dc7150e32006fd649421018efd4218143004fe71982320047f75589100c6fd31d91320076c7255152006dd6350c100f6fc63d8d54276f55118554005fc7250f10005fe7298154006fe71d9420004fc768c941005bf7448630006fd648ca512f6fc54d9543007d5534c621007f63148540004fc7650520005ff764871000fdc32d8c10157dc518ca300cefe50d9152006fc764c910004fc764c520004fe7608650006ff3218554006fd648cb2022fbc3290a41006bf72d9110005ff7154820016bc41590102cefe5118953006fe6254640005dd7550e32006fe62547100357e75184202cdee72d8e52275f671d9251004fc764c550006fe6258810006ff3059642006ff40596310077d7550e500077c7155152306fe50d8d54066fe41d9540005df7350a31005ff7154c20006fd6590420016bc4059010004ff7359250005fd748c550006fc7654d420eebf4059543017b441504100077c7154e50
  | 25 => 0x9020004fc764ca50017bf4250c10005f4715095103fbc4090630006fd7118132006fe6148420004fc7159120006fe6250b10006ff5198810006bf64905500cf7c50d9642006fe6359420005fc70487100f4fd75d9543077be5459021004fd7398652004fc7650650004ff7558c100eeff42d9153005bc7250e41006fc61581532e7dc32d9543005fd7508720004fd7418810005fc7058c21006ee6250810004fd7418930006fc3298650006fc6458c10017bf4259010006ff3298021005fe708c941005fc725441006fde4308530004fe72185532c77c7355152004ff7559230006df6354d20006ff40d96310057d75185430067d7518543006fe624821005f5f3154e502aefe4018943006fd63547202deff31d9153006be7418153007dd434c650007df638ca5126f7f52185530067f654c910005fe72d8d54006fe72d9640006fd6590820004fb7059521005fe708ca41005fa70c8630006fe64d8c20076ee4218941006fc5398a41006ff65c8640005fb7058554007ee424855005fde434c650005ff7454a30007fa32902100047f7559120004fe71d9232006fc3018954005fe7218241004fe71d9543007cc7250e32007df7150d30006fe4398a51217df508ca31006ff658ca40006ff658c520006ff6258154005fd76c8410004fe72181430e67c6550d20147df4254d30005f77158154006fc61d8152006fd4398221004ff7359252005ff7454931066fe42d9540006ff4098a5125f7c7454d51006df638c81020fdc418ca31306ff52d8d54006ff3098a41006fc62d81310067c6194150005fe701802109f7f5298554006dd6354e40004fd7598a10005fd7390950006fe721815114fdf418ca300077e51547200e5fe7518143276fd5018554006bd64906211b77c4294a50005ff7550720006ff6550a30217dc508ca31006ff7159420036fc7259420005fd70d9421007bf7458420006ff5058e41006fe7018954004fc764ca41004ec7259131005fc7254c10006fc6258554005fc7058543006dc628c5312d6fe5318954076f54118542006fc7650d20004fd7518131006fd6494020006fc4218553005f47155010005bd74c8640005fd748c650005fc7250710006fd6550a31005bf7550e411d6f95018154005fd7308540006fc32d9641006ff6118153006fd63d88100eefe64d91530077c7255151007bc7255241006bf64085102b6fd7418954005bd7550d42006fe4398251007bd4350951006fd4298251006fd6590621036fe511895030fdf53d9153006ff41d8c20027df3154c20006bd6590640004fc7608010127f8518c220005fd748c951005ff7454e10006ee6208210005fd75d82320077f7254d51097bd434ca41006fc4398420006fd648c210004fd7398a51076be5459021004fd7598640074fd74d9021006fc31181540057
  | 26 => 0x7de3294230006fd6558c21006fd7018953004fd7518121006fe54d8c21006ff31594201ffdf5250d31005ff724c010006fd644ca50006fc5259231007f62108610007ef7154b2009efd52d9151004ff7650f21007dd438ca51006fd648c810006dd638c710007fa20c42100e7f85050d50006fc4298420005fd75d8143004fd7655320004fe70d94210077d5454931004fc71592520f7ec32552320c6fd30d9132004fc7655021006fe76086500d6fe31d953202efd4318142006fd7018941006fc5058e41006fd6354a40067bc4190a50007ac7250d4201efc7159410006ff2198221006ff4158e520057f7454d52005fa7088540004fe72d9231005bd7418810006fd6548630006fc7655110006ff6458c10006ff4258e5111ffb418c220006ee6294a40006fc6318554006ff62d8553006ff73594100afbf4050e51004fe70d853203efd41d8d40006fd6390421007f95290110006ff419802130efd51d9153007ee424865002efd4118142004fe7018951006de7318554006fd6550c21005fe7194a30006fd75189310067c72d9510007f53188540006fd5298420006ff6298810006fd644c420024fc7018910005fc7254640006fe6294640004ef7648421005ff7150020006fc7655131086fe40d8d41006fe75d9021007f5548c521006bd6490720006fd654ca40006ed6218810006fe5298720004fe7654d10004fc7650550005ff744c620005ff7459420015bc7448410006fd6458420005dd7388630005ff748c550006fe629471020fdc408ca310eff44154e41005fc7150020004fc7059632006ff650853026e7c5018553005ff7350620005fd7398954006fd7218131004fc7058e510eff44154d410edfe7498953004fd7318540006df638c950005fe7118132005fd7318a50006fe6458c10006fd7218540005ff764c810007ed61c8220006fc3118954006fe75d92320bf7f515523216fbf5150d400bf5f5154e32006fd648c020006fd6550f21006bd6450e520f5fc7318954004ff7690620167df31181530067f65d8910005fe71d8a30006fe70d9231006fd5298640005fc7250410276fe5018554006ff4059632005fd7388540005fc7254010006bf6454d10006ff5259231004ff7655210005fd7390a50024fd73d8c20006fd6348640005ff744c720006ff644c520074fc7159021006fd731854026edd7318553006dd7318810004fe7688640006fe76c8520007f87250210006ff40d8c21004fc76552320f6ff6355132004fe7654d40007f64254710006fd71d95430dfbf4394a41005fc7254e4002cff7650b20005dc7054e321d5fa70d92500dcff74d9542004fc7654c20006ff3098a51016bf4318540004ff7359020007dd5350931007f62144010004ff7558c21004fd7650c20005df7354a31006fe73d9410006ff535
  | 27 => 0xf51d923008f7c518c650004fe7218550004fc7158d20006ff3298241005ff73552212bf7f4054d521a77c4194650007b77155241006fd5458c21006fe7398021004fc768c550196fd74181540677d54506500677d54906500e7fb5050e502e6fd32d9543006fd6408210004fd765502000edc6358c102e6df31d9543006fd6454f21006fe7118152004fd7598a310e67f5159543006fd61c8220004fc7058652007bf725514003efd54d8d40006fc425963003fbc4190a30005fd72d8c10067bc41d9250034fc7694020006ee6290a51007be4190220007f4704c621006fd6390621005fd74c8550006fe6498810004de7618d21004fc7648630096dc32d9231007ed42c872021efe32185430e7f85050e50006ff4359410164fe70d9630005dd7318420006ff7458c21006fd5498a10006fc6498810006fc5158c20005fd74d863225f7c4254d51006fd6394220006ff644c950006fe6158620006ff6350910005fe70d86420077f7454d52006fd7218151006ff654c941005fe72c4010006ff72590100077e52906500077e5250650006fd658cb21006ff6358420005fc70487200067d6555321004fd7318142004fc7650910006ee6288010004fe7118143007ee4248630006f66108420006fe7218543004fd7598a40006fd6550e2100cfd73d8c10005fe7218554004fe70189540079d438c940006fd7218550007fb2084010005bc7050e41006ff3198242005ff75590211dff7408c621006ff52592300377f5459420006fc52590202df7e53d9153005fd7494620006fd2158021007dd438cb10007bb7450210006ff658c810006fc7458c10005bf7448420007df7454d30006bf6490420006df6354d42197bf4218154006dd6354e41004fe7298231006fe64594100e6fc65595430efbc4254e411dff6548c621006fd6388710076fe401894103fbc4155230005ff748c650004fc7258650005ef7258543006ff42986300067d6594b21004fc7654931004fd74d963105fdc328c650005fc7155230006ff54d8c20006fd6394720006fc62185530057f758ca50006ff6454910006ee6290b100077e5188650006ef6298943006fc765512100cfc768c010166fe3118153005f57108010004fd7650f20067be6450e50004fd75d8c10005fd758c72008f7c758c650004fd7518931157df548ca30005fc714c220006fe645942109f7c50d9641006bc6290541004fd7655010006f96018154005fe70c8540004fe7018953077bf40590210e6fc6550d2104efd53d9130004fe70d8954056bd54d9150005fc7154d20004fd7498a3003efe41d8d40004fc7650e50006fc7654e410a7de438ca51005fe70d8632005f87054f200efbc4154e42005fc7055121006ff62d8131005fd7494720006fd6394210005bf74485300067d6555232004fd7418553
  | 28 => 0xc810007f97008650007f95350210006fc6198153287dc4054e32006f4618c5400e6fe6550f21004fd73d9020006fe64184200067d6594720006fc54d8c210acff74d95410067d6555221006fe75189432eefc40d8d54004fe72188100075d538ca50006bf6590640005fa70c84200eefc6454d210b7dd438ca400047f7558232006ff4398650006fd5458e2119f7c319465002ebf4359020007bf73552410b6bc648c910006fd7518940004fe7655131004fd7418152004fc7608550007bf735514028dee72d9232006df634c520006fe6148020004fe71d8954004bd74d85532f6bf42d9543096fd32d9131005fe7218251004fe71d9642005f47150a51006fc5158c10004f77644010006ff5498021007f54354710006fc3259250014fc7059010007ed528c7200057f7355250005fe71c82100067f74d9520004fd7654f10004fd7518143005ef7250c21007f66244010006be6290640005ff7454930006fe4359420006ff4058e51006fc5398420004fd739881004fdc32d8e40004fd739865015efd3218143007dd534c640007dd438c810006ff62585540069f64d8d21005fd74c8650005fe71d8132006ff7359020005ef7648421097de5390530004fc7158a50005fe7188210006ff5098632006fd6550c200073d5450951004ff7654620015fa70d8640006fc62d853001cfd75d9410177bf3255140005ff7550d10005fe70c8520066fd43d9540005fa70c8530005fe76885500057d75189430376f5294820006fc50d9232005fd7518642007dd53509302f7df43d9543006f6614c720004fd7518940005dd7318154004ff7694a10004fc7058a51006fe628831000efd32181310b7bc41d9232004fd7418132006fd6448530006ff3159642004fd7418910007dd534c62015fdc3218143007f97008550006bf64909310077d53545402defe32d9153005ff7558c21006ff7359420005ff704c421004fe7655121004fc7654d41006fd6454c21297df3018953006fd7318552006fd658ca4100fde438c810007fb208821001cfc7059410004fd7498b10006fc624821008efd50d8d510f6fe63550100eefe54d91530f7f83055130006fe74d8c20097df3054e41005dd7308530005fd7598943005fe708871002ef94018142006fc5098632005fe72d9251005fc7050b21007f972c42100eeff40d9153004fc7259630006ff6498810006fd65907100077f7154e50006fc6298554006bd6455320006fc6598543005fd744c910006bd6490b20006ed6208010005fd758cb10005ff7454f21006fc5259230006ff6358554006fc41d9632006fc5398640006fd658c410006ff309842026efe52185532defd75d91530c7de5390931006bf6455131006fc4098632005f87054720007f56150420007f56190420004fd7598a41006fc7359421006f
  | 29 => 0x7f9418c120006fe6250630006fd73d9641006fc505923124fbf3255241006fe629063001cff76547100a6fd30d953119f7c4394650005fc7054c21004fc70595412677f325515106edc6308520006ff658c940005f47150810005fd74c8630006fd6350a5109f7e6554e41006fd6590b10006fc7654910067bc4150e500667d54d9540006ff6158153004fc7654a312bf7c4154d52006fe5298640004fc7694810005fd73d9640004ff7458c200077d5354b10006fd5318542027de434c420006ff6350520005fd74d8a300c7df3054e42005fe711823226fdd7318553006bd6490620005fd7498420006fd7518532006ff65c8540005fd75d8e42006fd74189301dff4548c621006fe6258b10004fd7654c210e6fc6550d10006ff5298021004ff768c810005fd75d9232006fc7650d10004ff74596320e6ff51d95430bedd53d8d520067f65949400e77c5059543006fe5498630006fe768851000ede63d8c10004fd74185200067d6594820007bd32906400dfbc41d9252006ff4158c20007b87055140006ec620853007ef55118552004fe7650d21006ff5398021005fe708872005f7f4354e50004df735881007cfc7159421004fd7654c200677d5490a50005fc7254d10007bf6490630004fd7518142006fd6354a4102efc20590202aeed4218943006ff7058c210079d438ca410077c7254d51006ee6254a1013fdf5250d3006ede5358c210077f7355151005fd75d8a31006fd31980212df7c53d91530f5fc73581540a67d53d9531006bd6450e50007ad5450b21005fc71594200f5de7318154006f76198554006ee624c810006fd644ca51004fc7059232226f53118553006f9601802101cff7654210004fe711815315ebd741814302fbc4150420006fc6498953005fd73d8a40005ff7648210004bd74989100077f7255151005fc7059543007bf72552412e6fc32d95430067d6594421004fd7650e20006fc3259640005fe7018a41005fc7258154004fe7688110006ff61d81540077e5290a50007f5544c621006fc62d8550005ff7454520287dc4154e3202fbc4090420004ff765072026f7c5018553007dc7054e3201efd521855001d7c7548010005ff7150c20005fd73d8954005fc7250d10005fe72946400077d5354520005fe72d941008efe50d8d51005fe7194930004fc764c5400076c7254d52295ee72d9632005fd740855004fde438ca40006ff52d92312eefc41d8d540f6fc30d8d54005ff7150820006df648ca300047f7558d20006dd5318931306fc50d8d54006fd6458c20006bf75d9121005ff75509100077d5454930005fd748c420006fd4318152007de324ca10006fd75d9021005fe70d9421005ff7054e21004fe7655021067bc42906500f6fe53d8d540069f6418d21166ff431815300efd3218530006ff764
  | 30 => 0xc7158e50005fd759072002fbc41d90200057f754c650006fd6508410006fd54d8d20005ff7454f2004cff73d9130006ff6298554006ff41d942005f7d538c650006fc3059020005fc7158c20006fd7118143007ef2188420006fe70d9021006ff5359021007f54254710004fc7259531006ff64949100047e7619520004fe70d9632006ff42982311ffdf5050d31007ed2108720006fc7158c20006ff6398554004fc7158252006ff4218553004fc7159130005fd73c8640006fe6154720004ff7558e42006fd6498021004fd7655210005ff7648010007f96284010006dd634c81009fbd5454e41007ed61c802016fbc7550d40076ed421894105fde538ca502f6bf40d95430057e7194a5001e7c5018550004fe72d9210006fe429823100fdf3258c10004fd73980211af7f3194a50004fc764c950006fe75d8c210f6fc6355110005fc7155020006fc505902001f7f5359410087bf425523102fbc4155020006ff654ca40005fc7054b21006dd6354f10007f93290210066fd42d9540117f74294710006ff6558143004fc76508100eefc54d9153027df3158c20017be5450810005fd749855302ebc6459020006fe5359020005fe7094a3105efd31d953006edc3158c21006ff50d9232004fd7418953005fd72c4210007fa5290110006fd71d9632087be548c540006fc764c5200b6fd40d8d420067d65550200f7fb3055230007be4250910005fc7054421006fc72590100f5fe73d89540067f658c520007bc7055142006ff3018954004fc7159642007b47150e41006fc40986522ef7e54d8d5409efe52d9151005df7350a30005fd75c8720006ff6559020196fe4118154005fc7150e20006fe73d9010006fd73d9010005f87054940005df7348421004ff7559010006fc3259421006fe4298321005fe7218550006ff6390520004fd7318554007ee42485302d67c5018954005fc7150950005fd7588710006ff6218151006fd6590630006ff6458953005ff7054621005fe7018642004fd7598221006fe5298420005ff7055321127fb548c220007fa418c120006fd71181530c7df30989430077554547103067f52d8d54006ff439825205ede4358e50006fc61d8143006bf6418910004fe7018552007f63254710006bd6490410006dd6350e500a6ff658c9510c7de5390930007ef21c82200067e521815206ddc7348421004fe7655020006fc5198810004fc7059421006fd7018542006fe6154620006fd65c8420007ee524c52004efd31d9130006fb6098143006fd7218143015be7418810006ff5059231006fd6488010006fe6418553005fd70c8421007bd5450910005fd7408650006fd658c820006fd6550630006ee72d9642007de328c5400f6fc31d8d540057f7508650006fe6458c20004fc764c91001ef77654710006fd658c620
  | 31 => 0x8510006ff5058e42004fe7018943006bd6455010006fd644c810005fd7518231004fd73189510047f7558242007dd4388530005ff7355121005bf7550d42005df7348550006fd658c640006fe7218530157dc508ca30006ff32d9641005fd7418553006ff5298241004fd76553211a77c4294650004fe70d9621006fe7198b10005fc7608550006fd5218540006ff51d9020006f7610854014fdc408ca30005fd7518a41004fe71d9153004fd7398252004ff764841017fbc3290640006ff5458c2005fdc318ca5006fdf3050c21006fe61c87200377f5154c20006fe65d8c21006dd638c620006fd6284010004fd759864206fde5358c21006fe32987200f7ec325513218edd7318143305df7359153006bd64552200efef4254e42005df734802000fdc638c810006f461085400e5fe7518543006fc3259251006fd6590a302e6ff43d9543004bf7458910196fe421815406ef53118532006fe63d941001f7f52594100047e7619510006f6614c4200afbf4394540007f662c4210006fd7498221005fc724c540006ff4118153006df6354d21006fc7654d41006fe655901009fbd5490550006ff5218810007ed5208720004ff7654c20004fe7298640006fe61c8620006fd70d9153005fe7118252004fd75982412b6fd4018954007de3290631006fd72185532b6fe4118954005fe728c550026dc3258c202b6fd4118954006df63d8121004fc7158e40004f471595400f6fc43d8d540f7f43155131004ff7654f20006fd6454f10006fc63989540f6fc6358d54006fc5058e420673c4155250006ff5118143006fd6558021006ff6354540276fe5318554006fe7518543005ff7454e202c77c3155152006ff5118943004fd7498a50177bc7355140097bf438ca41006fe6558c20005fc7150a502b7bf40189540b6fe41d8d4200dff734c8100b6fd41d8d42005f97008420006fe64d942003fbc4290630006fc7655132005fc7155130006ed6218953004fc72592310057c7155250015bc7444010005fc7150f20004fc7650a50006ff7259410006ff62d8153006fc61181320f6fe6255232006be7418953006fd73d94100077d5390951006fe6398420006fd6394020005ff715522021fdc3218543006fc3298251287dc7454e32005fd73905200f5fe7318554006fc62d8553004fc7059521004fd73d9010004fd7518520005fc7050421006fd5498a30007bd5390a41006fd3298251006fe6318954004fc7690931006fc5298021004fc7158232005ff71553200e77f5159153006fe6359010026dc6358c200075d5354530006fd6118420007ef210852007f7c510865005fdc308ca50006ff3259410006bd6455232006ff5398241005ff7648420007af7450b210067d5418152005fd74086300efec4254d42005ff7154d201cf7f3155250004f
  | 32 => 0x6fe6250a10005ff7054d21006ff435942130ebd54d9153007f63294710005fd74c8420006ff619815304ede5358e40004fc76085300f7ef3255232007be429065005ddc7348650005ff7550a31004ff73596410077c7558021006ee6250a51006ff5498a311c77f51181530577f5298154006fd64588102677c7355151004fd7518542006ff50d923109f7c5094a41004fe70d95430f7f73155231006fc50d9231005fa708c54024fbc7355241005fe71181530077d5308650005fd751824101efe5218550004fc7650c10006ff4298420005df7348650007ed628c810007bf7250d40006fc2058420006ff4018553006fc4398652004fe72d91530e67c6559543006fd6550f10004fe70d9721005fd73d82510fff83290210005fd7394640006fe7218154006fd73181540677e4355250004fc764c951006f671188102b6fd5418954005fd75d8021005ff72502100e6fe6550c212e4ff75595430077c7154d520efbc4154e40004fe72d8131007dd548ca31006fc529824100edc32d8c1009fbd54906501ffdc5050d31007f9548c120005fd74c8530006ff654c5202dedf30d915305f7f538c650005fc7258d54306fd52d8d54007f96188020006fc6218131006fd6394010006fe65d90210077d4394a50004fc7650d52005ff7558543005fd7590b100e6ff52595430efbe7454e41006ff4198810004fe7608640027de4358c200b6fd54d8d422efbf42d8d54005ff7650420006ff7650a10006fd72181531af7e4394a50005df7354a30027cc324c820005fd74d8e520ce7c65909100077f7508650006ed6208210006ff654c810006fc6598143006fc43d9421006fc41d8c20004fc7650630004f77648421007bd544c540006fd6358420005fd754cb10005fc705942108f7f548c650006fe2198021006fd6454a10007dd438c910005fe728c65005e7d53d9530005fe76c8540004fe7654d20005ff7259010297df3118953004fd75d8c20005fe72d9640034ff7654220004fc764ca40005fd7394620005bd74d8553005ff7354940006ff4058c21006ff3298650006fe731815421efd3218543006ee6250b10004fc764c940096bd43d913123fbc7550e41005ec724c4200be7c50d963207df671d8a51026f970189300e6fe6550c10004ff7654b100e7ec5250d52006ff3198420006bf6408110004fd7398640006fc52590210f6dc3259543006ff61d8142006ff7559021004ff7459421006bd6450f20004fe7118132005fc764854004eff648c940005fc7150a30005ff7050821005f67194a3100cff764c71014fdc418ca30006fd6354b10006fc53d9010007be42905500067f71d9520004fc7654c21006fc7559010006fc5498630004fd7608410006fc7558c10007dc7154d30005fe7008530005ff758c940005fe7108210006bf648
  | 33 => 0x8000022026006800000a000076802030c01a00c801001e00903680d800400302b000000400900b806c000001032000403e01e0700178000031000859000200100480400100040028054012000004801400402d016002c0f2000007002000217a013010c00001a006012001801d00a8090000012000000002e017000000000010300680081780de00000000c800100680181340010300f0401200000a0000008001001000c02a00a008001c0ee00000680d400c0010088b00072000000003400679700a00e0052033010842800600000000b4058072000801c3860210010051a2a01101d000002c00000180001e000500d0fb4006053000801c02200000300000bc003006803801c017000005009205b05780bc002016000801001e0061988000002009031004800000002380280020170000150048036001800400004c001800019e031005802c04200d003000006a00200a823801c002020002c01a00f000009403e003012804002a00f00180f804e047005802c0040a90020064000001002000002800706780000480370128270742012000000000000300c000001602500a848400a00100100c408e03500101d40001b50a6000006600000580b800203305c009c00000f17481600bc009001000813a000000002c0900d3005805000401e00200680040000080000062003004800406200a000000001e01f004801954805c000800000a91011b825c018009001b3ec000001025015006801200780000040000220afc05803900280040020030018024000006002002469c012000800001e00001d02b803801c0268174e58002022017c000009000000000001211301500000020d080b4000033001002406c009000001801824c002006802e00800f8048058043020800000c00b242800401400c000000800804400181c40b40cb0028b6801806f00c011400002e037002019800200000fc00800000c05400ac012003001003c107144007400000500380000a80390018010000062000004800405f004800000601d00f0014004013002800c046027015b15802e1f20280010024133001800c000000226fe3218553005fd748c910004fd74d8c10006fe7098420006fd4398321006ff5198a40004fe72d8530004fd75185430057d7394a50006ff658853001f7f545481000cfc7058c100067f6508520004f4715913201f7f5354810004ff7359251004fe71d8154006ff31181540077d6554e41077be5408540004f77159132004bf7458d21006df638c941005bf7448540006fd70d9232006ff5458c10007bf748ca41004fc7259410006fe6254010087bf4055231166dc3218153006ee6294a10006ff765062002ebf4159020007ee61c8220006ef6298810004fe7018542006ff645802107efd5318552006fc6218550006fd7418931005fd73d8a50
  | 34 => 0xa014000004804601100a800006603a00700000b6006005800403200000880a0004021003002400401302c0028040002002810c0080430018000004064002010c0000010000008008006005802000800a0118024026015011806400019900300240400f900c003408000000b007c00400e01700000a000400300140000270020008004020003112400004b12c80901d60040010084032006007803000000300280e805e02d00c804c000012828802809600501d008402607301e8000036003001800002200e2398004332025006148c02400601d80f000601e004004001c001007002c0400021ac800801e00f00c800406e01800700f800600000580580aa03701e8004000011036800c02400000400280ac0f8002000c01603c006806000e01e000010400e0120110000012000020005800200200881680000a9000000001000a03100b000000000201c0024000000012404800400600300560002ab80380002fc5cf81940120a0001006003602600d800004803a023800c0540000000444008f3d00e00040100210570164062029006002401e00c044002003c00b000002001e01000300140240020130164000000005801c00c00300200180080440160460020081007000c002009002000800c00f0088034598001005002000636100a000c0260000d101680cc2ec00003b400000e014007402a00400c8174868000001001800c01a005015403a00e001802403800d0058088166003024810403400a0020030014005012800000414c011802400602c00101e410401d0000000000019006804c1f2010002001c2ee00000b803000007f000804402200500000a000c034000000000000800100040041150008000068008032005000404604501300020000348094000036012001400019c001802c00400100001a806800000381280040ae0050038002096004802401e0061e7017c02c03f006000000c00001780000ba000011800c04601f0010000022066074423c02204f0438034000000013802800000500007740000240018026b0001700500280020f700300181081390048104008030002817804400600487f4002000036009801a002012017800c02b01d804c03400106801a400435b02d80380b0017008000001c00a000000010801700000bc7660010018524004000000053000600600100340be00202f02480ce02000b00ac000001007000800006901f8004014006002002000202d00591d802600a01580400b0000002800000200000080180a0003020823800000c00083a801e0cb013000000200000680dc018005000000c00200d0108100006000018001400003500100e4034009002006400200001080d410a102205801c060021025801402406400f829413201102481d000001802b006400200900a004c012046094034c02402e06a
  | 35 => 0x217600180440020030008030020001001000000406300c00140041042790000000012000010c00a0080060000000009001001006e00200b81800000000000064014001001000012000701e801000207310e80240320350030154000d3e02d80e401000200181b409a08a03b003400207101300140040060000058002008006008403a01600101fc15c568000001801e00c07680040680150010004058006005800c02200c01482880444d300300e800c00200480008e4000030003c004000016000003400800380002b405b016000c03601200c806800000b01c80dc008004001001c00400907f002c00404f00380000200090028224000025003800800600100b00080021a100d802005a05a0000014006008000800803c0030000014002001047002806c00200381600b200209b800827c0ad005004801a2df001807c01e017005800403a001000002407800006b83bc05400d011801800000100a003403800002280b034c26f0120110000000036009400e009006803c00000701480e00360e100000e402401301f81d00000540e3001004a00002101d006a000000000001a0010040b5c03c04200100a80c202500b002000000742d00d80ae00102680000ca00900c001006601d001811802401f06600600c00000010038000000002000000c00000600b00000c0002001804204e000009403a00600389f8028003170808400e029010b180006021000001c0a80721728438016009000809c01c00000d8000000052000006497e05800e09b000c000021808c00e00800902a408600b002803007208b03880cc00a17900080fc01208e08c835c18a003001802401000216280e819c000000000000000d01e002002601f001000c00401b00e00648b00030080014002024000000c00401202404784cc01f003008400a01700180042441a000c00180ec04e005806005e04b005062403400501880600020a103c805c000007022815c01c047005889803e02300007ec00406206d800001805c01a800404a004001000c00c011006005801c038000020836400000001000120091c3008017201d00b80bc09e01005680380ec011078003c01400001282b80120010098014028017030800803e032019800000e00000180a0004002000069001400400b000000600100a02b005e048053011c01a00c06b80480f401900300f006a00f03a817013416f01e074001600200101a401800008300000000340098b940ee00000a8000000009a31018808e001002800001200005d802805800001a800c02801e43c010c0b002e033003000e097002001000000804380300020000000138008000005802400007d12f800000003c00b0084000035007015c04a03800b806400600101180146fc01200200f800a00302482cc11c02202d801412c005000000000
  | 36 => 0x3340800010000088050012008013c028000003803400001a03e800c02000800e800010204400500000ae0011d8000000000700aca080040f8000800c0500bf001801c04200100680a40e6039000801c000020000800000c00e000800400002e00b008400001000e81b475513125580300000020000000000161004011803e00002380ac01c022018803818c00b003000001e07e0070010028002000801c00e00b044801c05c00000000cc06a002016809c04800100b011000403e008000805a01f01c00000020af00000bc0de00d000061000e01e00000f405a01602302800060000000104222021092000c05000900e802800001b010000001600800
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xaf68114163904015ed02282c6080031f14173d96410065e3a4c488020008fd87d4e609040197ec9b92a68807b379cf63181540047f43ec8b102000cbc305d06254c018fb0bbb287080032fd907050d2118ecec18e0a1c82008fd8710261080011fb0c392a8080027e20175505200063fc12ea30a8600e5c32595530400197ae8316c2a98033718d7494520004be43aa720ca000e5f6394551480011fb0f98eca10002afe1564508100067d408e0b2a6400cf9869c021c800187ae8ba8c4a1802af219219014045ebaa08e2aa4a000aed8210563040019bae7988c4080035edcc70552500065fa18eca9c8200cbf42dd954040018fe64ba8c2a18036ddd47150e41007aa40aa7192a200c79759c0620400157d0c392a8a02229fe1570189535055fc22e3b1aa800cbf439d821500010f90cbaa86a90029f61730185544a72e192caaa46200d9f7450d514c0015bb09b2c651880375a0c71552102de3fbb6e8a9ca00095d831c554940011fd0faa2c6108035e146700865000677bb2c2900400097d84dd632940019b86538ecb180029fe1570189410066e194e1b2a8600af4815972150001c78a0ba0c4a9802bee0162d85530053ec2882b1842008fd87d0f6504001978c9bb482100023f61f31189540047ec36e6aa42000a7d8518920040019b8eca1a42980031fd977255110004eec18e0aa4425cdce62dd5438c8018fe60ba8c4a18031f5d761d81430057b408c5b0aa600cdd7318c60550bd57d09396caa1802b7219438c9100047ec3cc430aa600add831046054c0157f08b0a40100023fe1973908100066f418ecaa22000a7f83596500400117b083b2a6100036e5037550d100045ec20eca8840008ff8758b108400157d08294c2100031f5d4431881000576412ca90a6000cbf305d06254c015f300192c8108023fa1a70949310063e2a2ea30a8600cde531c96390401e7700aa4832800337dd9534c6200047f434e12126200c7e759c06150c015b906b10c408003370c87058c210055fc1aa830a80008fe86dd632440011fd0db9aa890802bda0764d85534e5cfc1ae8a9c8200cf5869c6208400197ae9318c408002eee0d54502103063e32ee6aa22000add85d92328c4019bb0c382a7190033d618715521000676b94e030a8400c7c535d46150c018faeb988c4080031f1da51545200055ec20c4880200097f8754f2194001b5ee5b9aa8a10024f6147250e410047f430e0a9a8400cde431c963040bb97cc9b9aa8080023fa1f65585430063ebacca30042008fd87cc764080011fd0faa2c6100023f21d6454c200066ea8ae630aa800abd83dd764440011fb0e296c8080023f61c3198a50004ef436eaa1a6268ece43188214c001978e8b1a4328002bea00329864000576c10a1308409bd3f53dd5439040157d09988c4080023760c7654810
  | 1 => 0xae8aa64328002afe1121580210047f43ea4b202000aed82146620400157b09a8ec610002af209649041051cbe436e6aa2a20097f835d251940b7b9cc5ba2a7190023fe1973087100072e282e630aa800a7e850c964080011fb0f326c610002b760c51980210063e29aea3128600a7e851c964040014fd0a324c4080039798d6554e4100767a12a63126200cbc7418921040018b864ba8c2a18036b6107254e200063fbaea93046400e3d84d9543480011fd0dbac64a080337d8f7154d200074fb22a71922000cbc41dcd64084015f100b1ac0108032f14d74189530057b40ea8b1842008fe87d09658c0014fd0b984c321003376187050e320047f438a2b184200d6f72dcd54548019e8e430a62a0003375937354a300065e210e2b204000a7d851d943484015f500192c810802cfe1121941500072fa8ac6a9c8000e3f6590942440015bd07b10c0aa002bb60a63988100047fc3ac710c80008fe8798910040019dd0f31285288029f6143198a40146ce20aeaa1a6000cdf405cc60550011fb0e184c528802b760c50986320065e90ae8312a65e9bf855d543508019b8a8b98c0aa0038fd9543509100066f322e63084000c7f75d4e60908011fd0c38a869015b4f61472552410057dc02833044200d5d7354e21940011fd0e182c929002bb60850185434579da10e0aa4a000dad42dcd54484015bd0620aca0817f1f5d464189530047f43882b1ca000add83d8b615500197aebb2264880023f61f4098a510047ec3865b282000abf865524188001a7acbb9aa920abf675537454e320065f3b2a91928000df17148020040014fd03b9eca90003b350c62885300047f43860b204000cf5719c0624c4018f8ebb1ac0108032f10672d95430047f43eca90c6061c7c65dd153840011fb0f2a4c3190023f61f4098420004ee43aa690a60009f8805d532440015f5012a4c518002b7e11658ca310059fc1aa8a8a8000af581cc261080015bb07a94c118802af61062181530063e3acc0b004200a7d831cb65440011fd0e20aca08002be60265980210047fc3aa630a8400c7c521c165084b95bd0738ecaa1802bbe0964988102ee5e326e6aa22000d3f7455121940015e902b2263101873b9ca43982520066e98aea30a86009dd83dc954840011fb0f21cc128802b760c409842000576c10a0b246200c7f52dd16504001abf06baec0a1803175d673188100063eb2ee8a9e40008fb875806054c011fb0c38a87900025f60c71552500059fc1aa8a948200cbd65dd12190001a7ea2ba0c4a9802b7e115318931004dec18e4aa48200c7e759c06250c01e6902aa48328003375cf42188100047ec38a430a86008fd870c861550011df0eb10c4a18023f61c321815434f67298c52126000c7f415d46250c0197ec9baa87880023fa1f5359021006763b48490a6000
  | 2 => 0xc41594210065fba6c690a8000adf85592328c0012f90ea9c852819f5e14470544200067c316e0b0aa800a7e82dcf65440011fb0dbac8390002b760c51982320047f43ea2b246028d9c7454d214c0e7d3864b22a9180025f20973946500047fc3ac990ca03fb5e85dc1434c4011fd0e20ac6100025f60f7590650004bf416eb20ca0008fc865ce5148001cbecaa9a62a00032f5817550e410047ec3c87b2840008fd8794e62040014fd0a194c2100023fa1c62585540047ec30e4a9c20008fe87cc164944011fd0fb1ac0aa00337d8c7150d520065fb24e12126200b3d8550e41940011ff0e990c2a00025f60f75086500063ea92e9b2c6400abd840c965040011fd0d39462a80023fa1e62546400065f3b2a990a8000cfa869c02150001baee3baa8698802b7a0c40984200047e43aca98c80008fd86dd153c84011fb0c38287108763f61f64d85530053fc2ae1b184200c7d215d46250c3b97ce9b26c2a9802bb60841596300063e280e2b284000af9800c9649440197acbba242980032f59574c86400063faa0e0b284200dbb731c154500011ff0eaa0c488003375cc31982420063ebaea430a8600cdd64dcd528c4018f884ba8c2a18031fdd764580210046ec1eecaa640008fc8758d21940016bb0aa1c65280023fe1d52185400063fa9eeca9020008fe87d956250c015dd05a9ac810802b7205638c820006e6a98e498c406097f835d54394001a7ee8a9a43280031fd4c7059421006cfb9a86a948200cbf75d9143484015eb02192cb20002bb60850590100047f438a2b1840008fd8715363084012fd0db9aa8a9003e5205438ca413267739087304a400cdd305d06054c011f90cbaa84880033784173185540057ac0864b204000a7e851886050c01bb46538463200031fe117518943006cfc26e690a80008fc865d641480014fb0bbb287080033e5d560180210063e192ea30a8600a7c860865054001f2f02a1c8298002b720d72d96400074fb246520c6000af98019165084011fd0c38aa898003375cd7118154004be43aa810ca000cdf768c53188133f2e6038a8720803370ca71181430047ec30e2aa64000c6d759c86204001d3ae8aa6c690003375cc61181540065f322ebb204200cbd64dcd54880cb97ce8298c4080033b61e62880100065eb20e0a1e4200cbd625d543904011fb0e214c328002af20164904210066eb18e0a1c4200c7f625d543544011fd0f982c810802b7e0d72181510047ec3e87304a400cfb309c06150c0197ae8b08c210002af61062d81530063fb28e2aa26000abe849d66108113abcc7ba2a7280031fd4e70d95430047fc3aa73084000cdd73cc062550011fb0e284c4080023fa1a72905500047f436e810aa000af8805886154c0187aeaba0c408003b3e0d62188100063e422ea3102000a7d851056308001a7
  | 3 => 0x4b2c60008fe87d49648c0011f90eb226528002b7e0d72185400043ec28ec9902000abf8550c615000157b09a8cc5180032fdd56450f21004dec26e2a984000abe840c262040014fd0a324c2100032fe1076485400066eb9c87304a400a7d851086154c0157d08282c6080025fa0b7454e500047f43ec8b004200cbf525d06254ccdb98e610a40100731f1977550d100063fc28eca8a4039b5e831c55494001b98e518a63100029f61476504200063fb2ae72928087d5c321c55394001dccc4a8c4388002f5e0d21c40100063e280eca9c8200cbd74d03650846f67d08392a7280023fe1d32982415153ec2ce3b1aa800adf835cb65040019bae6218c4080031f5db75086503ef4e20ac6a9c8000cbf74d0e619400157b0a396c8880036d1c87150e410066e20ae6302a800add83d8860550019bae798ec8100035758f7454e50004dfc22e3b2840009f6811c153484019b8eca9a629007ab7a0c76551100056ec18c49002000cdc325d7648c4012fb0bb8287908027ea007254d100065e42ae83102000c9d749cc60550019b8a2b98c0aa0031714173185540047ec38a930c60008fe86dc95444001add0a3928710802372197550d300047ec3885304a200ecd53189424c0011fd0fb2ac0a18032f9ca41181410047f43ecaa084000d5f855cf62550014fb0a192c810002b7a0f52986400047ec30e2a9c4000f548154d3194001d9864b90c0a9803379957318021466b6a10e4aa4a000c7c505d3658c8016f301ba843280031f14373594100046ec18ed2102000b3f8355241940015dd0420aca102c36718f7550d420056e432a719280008ff8759763084015ef02994c3900029f61463590200055ec1ee1b2242008fe86dcc21540015dd0420aca108023fe1d62188100063e3aac8b0042008fe869c6424c001abaa6382a4988033da1a71909312de6f31ee8a9c2000cbd7498b6154c018f8cb38840880023fa1c6458c100073c282e0312a600a7e861c954544c19ece3a1cc1288031f99574d96320047ec3883b184000c7d651c554c8001f1f04a1c64a0003375cf31d94200075bc22c23084000af5810ca610800173f0890c60980023fe197390a1000477c3ac43102000c7c509cb65904011fb0db92a9080023f21d645442000676ba0c510a60008fd87cc76590801aeaa638a84a88033e5907054b100065eba08131462008fe8714964080011ff0eb00c010903679537454d310047f430e4a9a822cade80d96328c0019bec3baa869824b97d51658ca310057cc00833102065cfa7014e6190001d68c930c8210003b318e628c8100047f43e60b2c829fdad521c954904019790aba0c0a98033ed8c7058554006dcc20e0a9e405bcde63dd153080011fd0c38a849800367dcd43485400066eba2e6302a800cbc419cb63550015f500192c9288023fa1
  | 4 => 0x2040015bb06308c0aa0033790f764c4200053fc2ae1b246200afa80106628c001d5cc529483200032f5d25498a310047ec38a3b1840008fe87d0965040011f90cba4a498002b920961185430065eba085304a200cf9869c321c800197ee9312a32016eb7a0e70d9153004be43aa918ca0008dd831d954040015b906b96ca08002b760775d8d20004ef40ee8a9c645ecbc64dd54344001b5a85baa8690802b760c41982520057d400c5b0286008fd8710a608c40197ae9a10c2a98031f9d661d81430066f218e4b1ca200baf8448720080019bca7396c6aa0023f21d654c8100053f42ce73004200cef429c860550011bb07bb2a9908023fe1d32986500063abaac23084000a7e85cc364084014fb0ba04c3190023f61870550210053f428c430a8600e775398551900019bac2baa8719002af21954906300055ec2060312a800cdf305d3658c0011fb0c39287080032fd0b75590100057cc00a330042008fe87cc564948019b8e7b22c4080029f61432984200065fb20e4a9a2000c7e655cf65904018fc82ba8c4a180397a0e75189430f66f39ac7b12a8008fc865d4214c001d2a8630a62a01766fe0d7550d400053f42e81300420099d831c154904b99bcc7baa8710802bd60432d964000577416a730c8400c7f815d46150c0157d01baec8908022f61076085300053fc1acb2804000cbd74d0e60084019eb0f30e42100031f6177650e200047fc3a873064200aee8214164080019bec3ba2a6980029f61463984200065fb26e0aa242008fc865d631480398fcebb28c4a18023fa18724c550006bd3ace010aa000afa80187604c8015df0c90ac010803d3e09538ca500047ec3ca73148200cdc7359562040015f100b2ac0108023f61e4398a500065e324e210220009bc8750e529040173b0aa1c64a000357d4973181540045ec20eca982047b3e851c94390543a7e87ba2a6a88033d6187150a100057ac0ca93084000abd82dd764440019bf08b98c0aa0026f6137154e203266eb98c8302a6009de86dd1534c0011fb0f29cc32111f4f1417550e410063fc12ea3128600cbf7458d21940011ff0ea14c12897b2f9937550c210065eb16e6aa48200af681141639080197ac9b828610802bb20963886500065eba4e6302a800ade83d4a600840197882b9ecb211af57d4b7454d304f79a280e2aa48200d3d7554e42904011fb0f29cc2100023fe19758cb100071faa4a8b1820008fe8798530880015ed02192ca080031fe0d75185430066e190e0b2a86008fd8714e6190801dd2c410220080029fa1461181430055ec18e1b22420097c8754c21940018f8a0b98c2aa0033760f76553210066cb9ce03102000d9d42dd5438c8019dae5388c0a900337dd56350e210063e282e7b28420097c8755132940014fd0ba06c610802b7a0c50988100047f4388
  | 5 => 0x10029fa1441988100053ec26e5b2a2000cdf805cc60550015bb07a14c1288023f21d644ca510065e3a6ca90c6000cbf645ce42544015db0432cc4080023fe1d52986300066ebac6530c6000e5f85d8d5148001ad8e52926328002b760c4198021004fa40ae89922000cde531c963900bf8faea320c2a98031f9d953909510065e208eca084000ade839d6620400137f06bac85208023f21d654ca41004bec24e3294a000add83d4a60084398fcebb28c2a1802af61772d91100066eb9ce23028639d5c325d54394001878ecaa2a2a0002bea03215822100677396c43028279dd8329c231900dbd3865b2483180023f61e4398a510065ebaac920e4000aec8258d62040018faeab00c01080277e0d72d94100066fbb4649942000a7d850c662940011fb0e294c3200029f61431988100074ea1c6430a8062b788548020040011fb0e18cc1211835dd877355151004df406e6aa482008fd87d466290001af2a6382a390003975956354e410079a40aa8a948200a7e8510a608c523ab8a1ba2a69890367d017550d310065ec26eca9c428fd9f40dd5434c4014fd0a192c8081831f98373552500057ac0864b24a000e9d4318a414c00197e80bb28610803275d173188100066eb1ee2a184000aef875886255001f328719281080021f6147650c210063e422ea30a8600cbd60dcd54904018fecbb9aa2900033da037648421006bcaa0e0a8e40008fe8710163948015bb07a14c210002bba08509842030e3f32ee8a984000abf8650e41c800157b08294c010ab7755447154e3200666b9ce4310205ecbf62dd543508018fecb38c40880023f21974949100057cc00653004200abd8414a60904014fb0bbb287100022f61076548103267b38887304a24fd5c505d5438c80197882baec9190a2e7a137154d300056fc1a4330042b0d9f30dd543508015eb03a9cc210002b760f52986400057bc0acb3084000add84d96328c0015db0431cc408002b7e1543189300047d400eca1842008fe870c565040018f8a03b042a800337e0573185540047ec3e623102000c7f62dcd54544013dd0438a869000367cc574181530066eb06eaa1c6400ee55298721c80018f8a03b2a8108db4f1077590a50306b7b16e6aa2a400cdd64dcd62040c38f8cbba2a6880023fa1c4158c102f6db30eeaa1c8200cdc30dda320400157b09988c0aa17b37ddb7550e320ed5f420eca9a40008fe861c9435400197ecbba2c210002afa0062905410047f43864b202000cdd735c860550011fb0dba2a7100023fe1975907200047f43e84b182000c7e7598b6050c0137b06382a9208032f1d943545400057bc0ac430286009fa801c542c80011fb0fa8ec810003371da314c520004bec20e2a9ca0008fc8759543080013dd04382a690a4757d4b7454d310057ac0ea53084000cee879894
  | 6 => 0x47ec3e81b184200cbd749c86050c015bb0a386c6908023760c76948100063eb2ee8a9e4200cbf75d9232440018faeab10c4080032f10672181430063e280eca984200aee821406150c019eae330e41100029f6143259250006cfba2a690a60008fd87d486050c014fb0ba02c7288023f61f42986500f66e31aeaa1a40009dd831c154484015bb0620cc1190033dd9771589430059ec26e2a9aa46197f845d543548012fb0a38a8790002bd6044098420004fc402eb20a6000a7d8510563948011fb0db9aa9109776d98773552410065e2a2e8302a6008fd879946008401978c8382a690802af6135198021006afa8ae6302a800cbd74d0862040015b906b96cb2087b379cf63d89540047ec3e85b2c6000c7d615d543940019baeb194c118803171d953549300056f41883304a40097d839c652940019bc863b2a9192df8f1416450e520065f3a4e2302a61eade83dd954c8001abaa5ba2a719002be60321982210063e284e5b22a600cee81dd9200800197ee9a1cc3290023fa1c42596310066f298e4b182000adc80592328c4018daeab10c4080033b6187254e200065eba66231020008fd861c143084011fb0f21cc12916f1f1db7454d520059ec20e4a9aa2008fd87d4a61900019be84b98c2aa0023f6187054e210047ec3e803102000cdf415cc60550d7abea3ba2a6980023fa1c5158e420047f43862b2c8000cdd76d8e32040016bb0bb828698802b760c50590200073bb2c4210a20008fd87d446050c013790ea1a42a0003375837454e320047ec36e2a984000abd84cc662900011fb0f986cb208023760c76551100056f418a0b204000d5d7354e4194001978ed21284880026f6137154d2034767298c410a6000e9f4058d43944018faeba88c4a18023f61c32986400047ec3ca93146200cbf7559143c80019bae73a0c0a9a834f143735524154d6fc1ae430a86008fd8714f64084015bf08a98c4980033e20776480200047ec3ea730c8400a7e850c66090801a7ec9b9aa8a88031fa147650d21007563148520a60008ff865d251c803b978c9ba2a688003375ce7118153006d6396e0a1a84008fd87152608c801978eca1a84880031f19670085200063eba2ea3128600daf751c943508019b86438ac610003768ca708c5400066f39cc83084000cdd73d88605500157d0832ac6080032fd4574189530053f428e2b184000c7e7598c62040018faeaba6cb190032f5d175d92320055fc1acb20c80009dd831c554880015f500316c0a0803371d9435493058cde436eaa1a840097d84dd631940015b90690cc0108032f5d343982522e66f31eeaa1842acdd9501c1538c8019f4c4382a318002b7a187054d3155eafaa6eaa1c6400abe84d46608c8019e901bb2421093f97195438c91000574402c4312a6008ff8750e60944018f8a03b2a72
  | 7 => 0x5f7354d42940018f8a0ba0c2a98023fa1e43594210063fb28e4aa2205ccde63dd543c40011fb0e286c6108031fd977355220006dda1ce128a80008fe861c93150001d9ec6b1464080039d4c675185430065eba4c83084000c7f765d5439400137d05baa87208031fd497655010006bc388e0aa4a000cbd62dd54390401d3cc8b1a87280029f61462d85430065fba4a930c6499f94321c543904e9d6e8630842a0002bd60465590200047ec38873004200cbd759d06254c012f904baa87280033ea0870595410055ec26a33046400add83dd954c80015f700a0cc0108023fa1c32594210057ac08a73084000cbd76d92410800197885bb482102632fa187050e410047ec38613148200cf58718721500019f681380c4a18029f61432590100047e432eb19280008fd87952628c0011fd0e282c610003b30c6628c810176ce192eaa1a8000cee72d8b60504018faea310c2a18032f9507654e410047ec38a2312869babf845c76550c011fd0f2a2c6108031f1d676086500056f418a1308401dcbe74d906254c011fb0db8286108035b9c942946500055ec2662b284000abe8418d65084019dae531621082af67d0b7550e320056e432a7192825dc7f76dcd54940018fccab9eca08003335cc62085300055f420a130c64008fc865ce51500018f8ea3122008002be60054980210057c402c5b0aa65dcbe64dcd548409f6bd0a38a87190033d9c561c82200057cc00c73004200add8314261080011fd0fb2a6320002af61361581530056e40ac91946000c7f7694952c40018faeab264328002af2194350910356ce20eeaa1a6000c7d65dcd54040018f8a1b9aca100023f61b7550e210047ec3e60312a800cdc535cc60550015f50110ac0108021f6147650d2130cbfc22eaa1ca0008fc865d6424c0018f8ecaa2a4980022f6137654e210063eb2ae72962000f8c8250e32500011fd0c38a84a800277a1b7454d310065eba4a9b184200a7d85d0262041497ad03b1c6528802afa1030984200065e3b286a12a20097e86dd1535440197ac9b9a8408002b7a03658ca310056f41e853102000cdf7654d3190001d76c910040880032fdda41506200061ea12ea3128600c7e759c86150c018ff0a3b2a4880023f21d6550a300047ec38a9b184000ced7298b1004161b3865baa86a10033b9c962c42100057b408a13102000cdd65dcd218c0015bb09baec6900038fd0965552310063ebaac5b028600aef825876050c011f90cba042a8002bea0061d81430063e328e4a1a2000cbf64dcd42441539bd0c38a8719003375ce43d94200045ec26eca9e2000d77721c5545440197ca93b042a00032f50173d96400056f418a33048400aed821066204001c7882b2aa8100031fd977150d202fe5eba0ca3028644f55851c5534c4011fd0e29ac8108032f1d954509310
  | 8 => 0xeca1ca4a00032fd937050d210063ebae803102000abd840ca60084014fb0a20cc5180031fd4573d9641006af428e2a1c64009bd859c242904015b90ca9c6520003b58c8618c5400063ebacc3b0286008fd8714e61080011f90cbac82980022f610764c4200053ec2e6130ca400add831406150cdfaf6a8382a3180023fa1f63585540063eb0ee6aa4a000c7f51dd954080018fcea310c2a1803a7a1273185540065e402e8312a600cbd749526204001adea5390c2aa0031fc8575185430053fc2ae1b204200a7d850c8615503d9b8c7b9aa8900023fa1f4258e510055f426c3302a600cdc73d95620400117b08382ca108034fa107254e500055f436432028000add83141648c4016bb0638aa8a90033758c7154e200047ec3e603102000cbf645ce424411f9bae7b2cc2a18022f2197550d400e63f3aacbb028600c7d7598b6050c011fb0e184c4080031f5d752d8c100047f43ec4b0aa800c3d525d06254c011ff0cba4a2100023f21d644c650005d7c22c390040009dd831c554480bb978c9b9aa9880034fa147250e410046ec18e2b284000cbc415d46250c015d904b2ac40816f3e9c35498a3000676c06ec9084200aee82d8d42545515bf06b10c0a1802b7219538c8100055ec20a0b1820008ff865d020840011fd0db8aa69026f6798f7550e410066f31ae9b1840008fe8798952040011fd0e20acb190023f61f31982420055f42663304a400cbc7418910040019b8e73124008002b760c76504200066ebaae630aa800f3b8055142940019bee8b1a6210002af60f75d9121007ac402a7194a000af581196610800173b08382a6988023fa1e6254710004bf416eb18ca000c7d751946150c019dd0f312a52015a6fa0b7590a41006bc388e0a9ca0008fd87d006254c017af06b1220080025f2057550e500063ebaea3b184000b9d8550e414c0010fb0bbb287082d357cc37454d520066f398c2302a800af88059160084cdb986239262100027ee1d2008010004be40ae9294a000cdc329c76454c013bb07b92a988003370c974d96300047ec38a93046200e5f5394e619000157b08282c7208035edcb7054e500056f418833004200e3f425955404001a78a6ba0c0a98023fa1f655842000677c0eec9004000abf835924108401d5aa4ba0c4a98027e2017588530006eb29ce3212621ca7e851d943484019b886b98c2aa0025fa0472552500047ec3ea33048400cbf431c564948015bd06322ca108023fa1e5458c100067cc30e0aa620008fd86dd543c40019bce7328c010803d3209538ca500063fb2ee6a922000cd573584610811fb3883baa86988023f61e53d90210074f982c8a1ca400b3d851c943500018f8a03b2a9188023f61f409881000577410a0b202039b5e83dc954940011fb0faa4c010803375ce53d90210057c402a530c8000d
  | 9 => 0x52980210069fb2ee6aa280008fd871066094801ad8e5b8aa6a9002afa1052982310056ec18a0b202000cbe7498c62040015db04204c408002b7a0f52982410047ec3881b184200abd840c262944011fd0e282c810802bda0462d853000676390c2b02a600ade83141640400199ae6b10c4080025f6147250d100055f42064b2840008ff87552628c40197ae8218c408002b7a0c70590210053ec28e2b184000e9e63591439400137b08392a6880031f50575189430055e412cb20c8000cbd745c86054c012fd03b9aa92800337dd363545200047ec3ea5b246200db9431c152500015f501b2ec0a18023fe1d32982510065cba4e03102000c7f52dd954040011fb0e29cc520802afa187250d400065fc02e8302a600cf5651c5428400157f08b8eca10003d554e3254710006ceb1eeaa1c82009f6811c943440015bd06284c5208033b9c962c4010004be43aa890ca000cdf525cc605500197e8638ac9280023fa1a718c9500063eba8a33148000e6f65c84214808fa7ea4baa87208032f1d943485404eedca80e0aa482008fe86dd543480011fd0e192cb208023f61c50986320069fa92e8302a600b3d84dc5539400117b083b2a6900034fd097518543274bf40eeb20ca000cbd641c954840017b706b122008002d7e11538ca500047ec388130ca4009be82dcd54904019beed1926588002bb60841181530053ec1ee9b2a2000b3d8550d42940018fecaba4a2900038fd9554905200057bc0a653084000cbc411d9548c8012fd0438aa72827bcdd4871552410057cc0064b2842008fe870c965080018f8ebb22c0108038f10675189430063eba8a831020008fd86dc954c40015bb0bba6c6908032f191739491044eaf986e8a9ca000abd8418920040018faeba90c0a1802afa10325942130e6e3b6e8a9a6000dda321c1518c00197e85bb286080032fd037650c210055f42663300420097f8754e2194001aeaa3b9aa888002be60221980210047ec30e2aa0400097e86dd153548018faeba9cc2100023fa1e62542100063fb16e8a9aa200e5c5058d539040157d09a8cc4080032f5d171181535065fba6c6b0aa8008fd87152628c4019dee430ac0a98023f219759093147ece326eaa1a62008fc87595214c0019db0e31442980031f5d753986420063fa92e9b2c6400cbe655d06008401b3882b98c0aa003375d273181540057d400c5b0262008fe87189514c0011fb0e21eca108031f14676086500047ec3cc23028600cdd73580600840197ae8320c2a98031f5d452986300063f21aea3128600a7c855c364084018f8a0ba6cb18877ab191539092100796412a8a14a0008fd861c943040019db0f3144108003d6e01538ca500065e20ce1b2c84008fd86dd153080019b8ed19264880023f61c43986520055ec2ee1b2242008fe8794d640400197c
  | 10 => 0x30aa800cde531d9548c8011fd0e192cb200032fcc174181530065e322eb192200097c815ce52940012ff06ba4a528002d76147150d300053f4288530042008fd8714364084018fecb38ca498002b720154d8d210053ec28c731020008fe87101630800197ac1baa8720802af60e62906400063fb2ee6a0a4000cbd74d0363084011fd0e18aca10802676107054e320063e284e2312a8b4c7d75d926254d5de98a0392a7190031f5d75498a300055e412c720c808ba7f855c061550019f6c9b82c4a9a834f9977355241006bd288e0a8e40008fe87d8d62040018f902ba8c4a1802b7a0f42984200065ec20eca9a4000abe84d846054c015db0d90cc1108029f61740984200057cc0082b1842008fd87d0b65040019beebb1a86900032fd897550d4030ebbb0ee8a9aa200cbf7458d610800173f0aa1c64a0002b7a0374d8d2100677396c430aa8008fc87591518c0018f8a0392caa1802bba0b63d89540047e432ea10a80008fe87d856054c0137b07bac85208027ea0072551100047e432e7212a000c7e85dd9438400197ee8b1a43201cb6e1067090a30004bfc3aa990ca000cf77198550080018f8caba46488002af6133198a500063e280e2b2a8600c5d739d46150c0197aa0ba0c4a98038fd5254988100064f982e8302a600cf981dd920080018fb0c38aa9280030f5d574189530047ec3ea23102000b768194a31940018fecbba26290003375877550e320066e194e1b2c62008fd87d4b648c00157b0998cc4080033b60072591310056e432871902000e6d425d46250c015790ca1c82900023fe1d4218151005aec1ee4aa4a000c7d751946250c01c7ec8aa2a488003b30ca72181530063fb2ee4a9a2000af6810ca6008401c7ec8a9aa488002bea03215802100676b9ac431020abcdf73d956250d69ab865ba2a6a90031fd947154d20004fbc3a4210e2000cf9869c021c40015b906b96c8080022f610764c8100071fb2c82a0a4000add80dcd63084011fd0fa1aca100036720d74189530063f3a8eca1ca000cbf65dd1218c00117b083b4a408003b3d4943189300066fa82e630aa85ccdf61dd5434c40157d08284c4080036bd0a72181540047ec38a430286008fc87595218c0019f70eb00c0109875bd8b7454d520047ec3ea3b246400cb5641c54308401d3ac6a9c8320197375cc6518543004fd406ea98a80008fd871026204001d688530c821000337dce6148020316bdaa0e0a902000af980cc660084019e8e2b0a40100023da047650c200047fc3a87304a400dba841c153c80019baebb1c8290003379057318154006af98aea31286008fd8710e60948b99b8c7baa8790803275d273188100047ec3e8730ca4009dc8750d214c145a7e81b9aa8a8803b554573185540066eb9ac431020009f4815d132840011f90cbaa86908023f61c
  | 11 => 0x5440197ec9b9aa8880023fa1c62480100056fc2ac919462008fe87d0163944011f90eaa2c608003370c87654c100066e39cc29004000cdf515cc6055001b3e60ba0c4a9803379d953905300057a4328528a2000adf8558e320810deb064382a7280023f61c43d94100046ec18eca1020008fd8715363040011fd0e282c8080033718d759052000757430e4aa284008fd870c261908011f90eb1aa5208026fe1171d8c200065fb26e0a9a42009bd85dd2329040117b08392c6080033d9c561c80200069fa8ae8302a600cbe645cf6494141a7ea5b9aa9209baeea0364906300f53e42ae1b1aa800c3d759d062040011ff0e994c3200023fa1f63504200057ac08c93084000cf9709c4624c0019bae6ba8c2a18032fdd2624401000796aa28590ca000cdf305d943084019bd07bb2a9908023f61e54d8c210066eba6c718a40008fd87cc061550018feeab0a4010003b958421480200059fc1aa8a14a08fadd839c76550c015bf06b90c29800373dd07254e320056ec1e84b2c62009f8805d532c40015db05984c4080035edcf70552500057a40acab0840008fe861c543540014fb0ba04c51880337d8c7150d200047f43ea4b182000aed8294e62040011fb0e18cc0108023fa1e43594100072fc1eca98a4000c7d75d47640800157908b8ecb180034e55070549400047ec3ea33146000af681142628c4011fb0e196cb208023f2197590910004de43aa890a8000b3f8590a41940011ff0cba843900023ee1d60181540066f29eec9884000cbc7459561080018f8ecaa2a488003375ce70185540047f43ca6b20420087d851d820040011fb0e20cc4080023fa18714c9500045ec20ec10aa0008fe871416308401cbecaa9c64880031f1d953549100056f418c93102000abd82dd164040014fd0a196c808002be60321980210053f42e613102000abd83dd1640400197b0c392a9208026fe157390a410047ec3883314a0008fe861c943440019b8eca9a8498802bba0850592310065f192e8302a6009df845cc214c0b9baec3baa86988023f61872553100066e202e630aa800b5f8454d514c0019eec638ac0aa002bea0253590100056f41ec5302a800aee82d0d65080018fb0c38aa7280032f54574189534decf98eeaa1c825bcdc63dd153c84018bceab98c4080021f6147158c2000656ba4e431020008fe87d0d65040018f8a1396cb18802b760f52982410061fa12ea3128600add83105658c0018fae73a8c2a18023f61e5398a400047fc3ac99084000cdf64dcd620400197eecaa285080739b19543949200065fb20e0a9a4200e5f5394d64084010fb0bbb287100033759773588100067b43cc29884000d78721c153940011f90cb9842a0003a75916350e5043e3f430e2a9ca000db5541c542840c38fcc1ba2a7280023f2197390951006cfa12e6
  | 12 => 0x3175d6731855400576412c6a142000abe8419661080011fb0fa06cb188033d5c661880200067c310e0a8a6000d5d65dd1538c8011ff0eaa4c5880023f61c32982510056f41e85304a200cbf62dcd545000197883b9ac8082772fa187055241006ddb90e0a1a803fe5c6550d31480011f90eb1a8328003375cd70185540047ec3e8130ca400a7d8510a618c001baee3ba2a6988034f10d75185430047fc32ea10e20008fe87d91528c40197e64ba0c0a98023fa1f644c810006763b4a498a4000af58115261080018fecbba2a71000357dd6328c6500063ea8ae7b2c8200d9f835d36154c018fa84ba8c4a1803b390e628c8100057ac08c6b2040abadf835cb6550c014fd0a20ac6108031f14271d8d540066e2a2e631020008fd86dd543c80011fd0e312c0aa0033d1da31485400065e20ce0312a800add841c363484015ed02284c52097f2f5d065189430065ec20eca9a8474eb440184215000157d09a8cc2100023f61f53984200e63f32aeaa1a4200adc81596328c1694fb0b396c8a98031fd4c70596410047f43864b2040008fd871406150cb99b8c7baa86900023fa1c31596420047ec3ea33046400cbd749c86054c011fb0f318c4aa0023fa1c3059251004dec20e0a9a4200c7f65dcd54840019ef0eb08c2100023fe1d65886405169e20ee6aa2a200cf5801c5644c8015bb07a12ca080029f617305902129f1e32a86a122000cdd631c1538840197882b9ec8100023f61b7454e10004fb40ee8a9262008ff8759363080d75bb07386c8a98036714d74189530065e208eca1ca000cdd61dd1538c8015db0420ac728002be6004158e520065e29ae8302a6afd5e65dd1538c8019bcc6baec6108023f61b7550c210055f420cb310200087d851d8214c00157b0bb9ec88817b3b9ca53986420065eba4e4302a863db7431c54204001978ed20a82100031f14272185530055e4224330042008fd8714e61900019bae729cc2100033d5d970c86210066eb9e803102000b9d83dc95450001bab0638aa9080031f19470594210047f434e3212a0008fd870c7650816b2f90dba2a6a90032f5d26498420175cf41ee4aa280008fd8714c620400127b08392a7280032f59373550101b69fa1ae9294a0009f6811c143484019bf00b98c2aa003ad55061c85400066e190eca9c80008fe87d8910040010fb0a3b284080030f5d275189432f65e326eaa1e2000c7c511c1650840197b083b2a6a00027760c7608550004bf40eeb214a000c7f515cc61550016bb0638aa928003a7d92324c9100063e3b2a6a8a8000cbd749c062550014ff0ab86c9191df2f5d363981540057b408c4a8a601ca7e85dd943840015bd0d10c6098003ab98952906400053ec2e60312a800cdf74d8d53480011f90eb2a8318002bbe0965988100074fb1a8720a4000af48150860
  | 13 => 0x65e902e8302a600add83141648c8018feca392a688002f6e11534c22000576412c6a962000c7f7588560084011fd0d38464a08032f10575d9230006afb1ee8a9aa4008fd87cc365908011fd0faa2c608003375cf30d90210047fc3ac43028600b9f8550e414c0019bc65380c29917277e157550d310047f43ecab102000af681141630852b7ad03b1c6520803370c87650c100063ebae603102000cdd831d954440015bd0638aca10003adcc554185420063fbaea930462008fe8710563948014fd0d90ca0a814f4f1417550d42006ddb90e0aa28000aef825846050c011fb0fa1cc3280033754973185540057ac08c73084000cb57458461080012fb06392a9280033bd4a72185542de6e31ee8a9a401e8fd87d8f6255001cbccab1aa72080397d4e53986420047f43e60b2c84008fe869c252504b75b906b96c8a98032f5d270189530053ec2e60b24a2008fe87d916254c014fb0638eca900023f61c4398a510065fa1eeca102000c7d759c86154c011fd0fa92c9188029f61072d95100047e43ac890a6000c7d75d446050c012ff08b9ca328002b7219218c1300056ec1ec5302a8008fe87d45639095fab8a1ba2a719002af6107058c2100746a18c4a126066dce431c931080c38fccbba2a7900023fa187254d400063ebace430aa8008ff8750a608c4015bf08b1c64100031f5d672185430055f420a13084000e3d655524108001b76e1b9aa8a00029f61071d95203b6ce196eaa1a8068ecc30188214c0018faeb398c2aa002bea0362d8141004df436e6aa284008fe8794d64080015bb06324c2100023f61c5098a410067dbb2c290040008fe87d9532904014fd0a31ac8100033b5ca62840100057bc0ac5b028600eb9305d06054c015ed0321cc128a06f6a03638ca500046ec18ec10a8000d7771dcd5454401d3f09b1c82900026f6107254e100067a316e2b02a800add83d086054c019d8c5384a4988033de0b76440100072e194ea30a86008fd87cc261948018fa20ba8c2a18023fa18704c94144eae196e8a9ca000abd84cc5659009fabea2baa871900397d95434c5201be9fa12eaa1ca000c5f515cc61550011fb0e29ec8100031f1d954545300067739284302a200abd83dcb64440015eb03a14c2100023f21d63548102f55e422e3b2a8660c7f61dcd54544019bcc6baec7208035710d75189430047ec3cca3028600e9f4058d43084019bca8b98c2aa24f5d1427194a310065e20ce4302a800ae8825806054c018fecbb8aa8900023f21d65485404663fba8c4b02a800f994390530880011fd0e20ac610802be60041596320055ec2663b284050d9f405d5438c8015db05aa4c408002b761771d8d20005edc1ac50802000c7e7599061080019deed30a40101772fd8373551402256f40ecb1946200cdc301c9630400157b08282c721
  | 14 => 0xf8355152500015bb07b16c0aa002b7a0f42188105466f430e0a1c64008fe87d91218c0019bf0ab98c2aa002bea0041189530047ec3ca930c6000cde7654e214c0019f50d3848498002dbe115354b200047f43ea2b1c805ad3d841c954940efa78cbb9aa8a01c7a7951648ca3023d9f42ee0a1c8200c7f65dd231480011f90eb2a65200023760c76080100053ec28c49082000cbd64dc943040015bb07b12c0aa002be21952901100047ec3cc58842000c7f425d46150c01b3c83baa86988032f0c974181530065eba2e7b2c8000dd930dd543480c18fccbb9aa890802afa1062181533065e3b6e6aa28000a7e81dd365480014fb0a322c6080023f219748c5200063fbb2a6a948200a7e85cc261080015eb02286c91916f75d877454d310069fa02ea30a8600cf7719853008001bb286382a2980031f197748c5200065e3b482a0a40008fc865d13244001c7ea92a4c5188032fd937250d100055fc22e23028400cf9709c861500019bae6baec9188023fa1c62505300053ec16eab282000db775dc543904011ff0eb2e42a01776ed83735514000576c14873102000d9d431c931500b997eedbaa8720802b7e0d72181413a75b2a0c210a8000c7f7558d60084011ff0eb1c42080023f61f3118154484ee436eaa1a6200e9f6450e3254401878a0ba0c4a98033ee0b76440100066e31eed1902000abd841426204165a78a1b9aa8a10031fcc575185430074e20ac6a1ca000cbd75d92424c4019becbb9a42a011b4f1437590a410065e20aebb204076d3f53dd543500013bb0a38a87190023fa1c5058c100066f98aeca984000cf9631c151c80019b8c6382a890802be60353980210047f43ea2b2464adcde861c5538c8015bb03b9ac6100731f9d765d81430053f428c73084000abe8414a600851dd9c86314a498802bde1921580210057dc02c93004200add83d0a608c4d5abea9baa86980023fa1e61542200055e432a8a122000c7f655ce4148001dac6530aa3180023f6187050f210055f420c73102000cfb621c1615500197906ba0c4080023fa1e6250810006baa8ee8a9a20008fd861c953040b73bf08baa8698003270c974181530065eba084302a600e9e839d06254c015b902aa6c6900033bdca6254710004fd400e4a1a20a0d3f51dcd549040157b08194c1208036ba107254e200063ea92e8312a600abd84d866054c018fac3ba2a728002b760c40986520ee5f3a6c8302a6009f6811c930840019bac7baa86880029f60b74d95100065e20aea3028600cdd739c460550011f90cbac62a0002b7a0c65590200057b408a03128662d78521c152040bd97cc9baa87900033d9c761181530062f98aea30a86008fe871456304001cdd0c392a8a90032f9d07654e41005d7c2a86a164200abd80dcf6448401b3b08382a71900337dce614872000
  | 15 => 0xeaa263280029fe1570189510047ec38a930042aaf8f401c9438c8011fb0e196cb20003179d67318810004de43aa919482009f8805d7215000117b08382c6108033718c71551200047fc32e72962000a7f855c0614c801af2a8382a2980032f5d160180210053e432a8a922000cbe541c5648c8014fd0c392a6a88038fd9554905300065f426eca9c4200c7f655d2514c0015f50020ac6080023fa1871549300056fc1ae43026200cde535cc61550011fb0fa16c608002b7e0d72d96400047f436e0a1a4200c7f65dd23244001d3882b98c0aa002b7a0c40986520047ec30e0a9e4200cbf405cf659000197eebb228688003379d943945300056ec18c93004200add83dd954c84019ed0f30aa2100032fdd363485500053ec2e80b1ca4008fc865d2324413557f08b88c4a18023fa1c61581530075a422c2308405dcbe61dcd54904015bb0630ec0aa0032f5d3401855319eae196eb18ca0008fd871426108119a7882392a9280023fa1f5258e4000677c06ec9084200d3f855d36154c0195ae8b10c4080023f61c31988100053ec2e61314a200cef65dc96150c014f90ab86c9188023fa1c5458c210047f436e8a9a42009bc805d642904015ed02194c1209835e98373552500066fbb28698c4000c7f65dc553480015bd03ba6c690002e760c705524100766194e430a8600cbe645d7648c8011fd0c392a2a0102e7a107054d310063faa2ea3128600c7d751946050c018faeb388c4a98023760c76550200055f430e0aa284008fd870c4625500197ee9b1ac210003cde055454a410047f43ec8b0aa658d5f315d543548019dee5b0ac0a98afe66107050d300047f434e528a80009be80dd642904018fcea30ec0a180337441731815400677408e4b2a608dd3f42dcd54940c5af6a6382a40800337d9773485300069eaa0e0a948200a7e8510563080013f50038a8498003b318a218c130006aca98e0a8a6000f988050e32500019bac7b8aa610003370cb7558c200057b408a0b184064c7e7510c62040019beebb1a629011b4fd4d7590a410063fa1aea30a8600c7f51dcd65080018faea298c4080033758f7454d100065fa18e2b204000c7d75d4f64040011f90cba464a80032f107755902141db7416eb214a000cdf65dcd62040018f906ba8c2a18029f6174058c210067ab98c390a8000ade8314660084015bd0632cc2100029f61730986424972e286cb194628af38411c154940018fea9bb2a2100023f61e5498420335e641a4210840008fe861c154484011fb0db9aa9100035714173185540057cc006330042009fb87480208400137b0a3928720802bde0563984200065fa92e8302a600cec72d856054c0193ce8b98c408002b7e19538ca100047ec3ccbb204200abe84142628c4011f90eb1a85288031f19573905200063e284e3b2c8400b3
  | 16 => 0x3984200066fba2c6a9c2000cbc411c16550c01b3ee6a1aa4a0002bbe1921980210071faa4a8b184200cdd7390e609455f9bee7b22c4a98023fa1f64581530056ec1e85b282000e5d83d95434400187ceaba0c4080033da0871595400055fc224330042008f7875846154c018fecb394a2a00031f59574947200055f416e7b222000e3c509d06254c0197906ba0c4a98032f9d271189530066e196e8b184000cbf641c943544019becab9842980023f6187154f200057ac0ca73084000cbf515d06054c0157d09a88c4080023fe1d54189300047ec3882312a600cdf405cc61550018fecbb9a84880027b209744c6200053f42e613148200a7f855d821540018f8a0b98c4aa0029f6174018953004f7410e2a9a4000abe84141630850f8feea30ac0a98033ed8f70585540047ec3883b2c6400c7d755876050c018faa2b98c2aa002bd20542982513063f32ee6aa44200cbf7458910040c18fccbb9aa8080031f6147650d520066f282e630aa800c7f425d46250c011fd0d39462a0002af61052181430047fc32e918e4000d6f72dd15354801cdea9312a4080029fa1432986400056ec1ec430aa800aee82105658c8019bcc7396c6aa0023f61f6588630006bdbaae010ca0008fe861d82154001a7e80ba8c4a18023f21d5458c202ee5e326e6aa442008dd831c564080011fb0fa04c518803376187154e320053e432a8a8a4000cbf825d06254c01cbecaa9c64a0002af60b73d9110005cec26e2a9a6000cbf605d5435083ddb0c6aa460900023f61871552200066eb9ce030aa6008fe8710d65084011fb0faa4c118802bea003259020286cf2a6e8a9c6400cde329c4604c86557d01b2c83200025fa047254e500047dc3ac03004264cdd731906154c011f90cba04298003375d763505202eed7b16e6aa28400c7f815d46250ca1b3882baa871900337e0c76485300067cbb4e588420008fe8715163080c38fec5ba2a6a9002776107054e320065e20ce03128600a7e85d02618c8012f904ba4a3280025fa077454e500047f43e80b2c6400dd930dd1534816157b09396caa180337cc174181530062ea8ae630aa800d79531c1525000197e62ba0c4a9803371cc62480100047ec3e6130c84008fd8714e620400157d08194c1288033b9c962840100055ec20c5b0aa600ed632986518c0011fd0fa12cb188032fd0e71d91530066fc3ae6302a800ced8798a21c4001aeb0a38a87908023fa1f4258e50007cbc0a87194827eb7681dd631940019bae6318c2aa002bb60854988100047ec38873102000cdf315d7648c511ada64392a7280023f21d63504200053f4286330042008fd87d0e600849f6bd0bb828719002be60032984200055f420653084000af9800c965904018faeaba0c4a98032f5d1621881000772b104288020008fd8714a618c0012f90
  | 17 => 0x92a239d5f315d5439400157f08b88c4a80033bdca6244010304bfc1aeaa1aa21eabe849c3635515fabea5ba2a7190021f6147650c2032e3eba8c6312a800cfb641c16254c019db0c39287108031f5947154f200055ec26eca9e20008ef8758862550019b864ba8c2a18023f2197550d100063e98aea30a8600cf9861c152c40011fb0e214c2100034f94373551400066eb9e62312a800cef7298941c40011f90eb22a6080023f61f40986320047ec36e918c401ecdc635d54348401b3908b98c2aa002b7a0f62185540047ec38a93084000cdf875cc61550018faca392a9880027da0472551100063e32ce010a2000cdd505cc61550019eec5b8ac0aa0035755373486505666f430e0a9c64008fc865d231540011fb0e204c5288038f59554907200063fb2ae92922000d5f7354d21940011ff0eb08c0a1802bd60432980210065fb16eaa1a8000c7d751486150c011ff0ea98c2a00023f21d6454c210047f438a4b2460008fd87cc261080015bb0620aca108026f21d4354a410056f430e2a1a6000cbd745d46250c01aeea3388c4a98031fcc575189430075bb22c32084000d3d7455232940019baebb1c62900029fa0462941500066f986eca9842008fc875954308535b5a6439287208039e14270185540063fb2ee8a9c2000c7c435d46150c014fd0a194c010802eea024290630004ef406e8a9c6400cbc74595218c0018fa64ba8c2a18023fe1d5498a300063ebaea9b184000afa800ca6108001af2a6382a5880023f61c30d90210074eb2287190201dabe84dd953c40015f70090cc0108023fa1872551100067a416ec880205ecbe64dd543c84bf9bce62a0c408003a70c97418153006bcaa0e0a962000c7e7518b6050c018faeba90c408002afa135158c204653fc2ae0312a800add831d954440010fb0a3b042a00023fe1d65884100047fc3acb10c60008fe87d4d64040019bce6310c2aa003a7d91438c9100047ec3e8030aa600e9d6450e3294001978e9b2ac2100023fa187250d51004bfc3aa910ca000c75759c462040019dce5b10c2a80023f21d644c420316bc3a84088020008fe8710965084014fb0a214c2100023ea0076550210066eb9e603102000c7c315d46250c019b8a8b98c2aa0033ba1e6250a310066fc0ae6302a800aee82141648c80197f0eba0c4a98031f5d275189430063e982ea30a8600e9c4158d43080019bacbb9a8518803371d953485300055fc22e230264009df835d932040018facbb8aa810002bd6045058e420057a40ac8a8e40008fe870c565080019b865380c2990038fa1674181530065f102e8312a600cde7318860550019ba82b98c0aa002b760c41594200072ea9c64302a20097d841c953940011ff0eaa4c508002be20152185400055ec26a33148000c7d75d8b6050c3b4f90ab86c8a9802afa106
  | 18 => 0x4d5f5bf06b96c8a98025f21d535065032e6eb98ca3028600d3d51dcd54904015bb07a14c0108023fa1f315902055ecfa06eaa1c6400c7f535d46150c0157b07b2482100023f61c50d92310071fb24a4a9220a9dd5411c5438c8018faebaa4c408002b7a0f42594100055e4328720ca000a7e85cc0620400197ce9328c0108039e14170185540047f43e60b24a4008fe8710163040014fd0ba04c4080027be1d21087200056f41882b2840009de86dd5434c05b67d0a39286a00023f21d64548100075a30e432028000cdf831d931480015bb09b1c64082bbd3d447254e3200576c1082b282000c7f651c953500019bacbb9a4320002b7a0c41594210046ec18e0b2042009ee821c540880018facbb92a808002af6105098a310057dc02633044200add831446050c0197ee92a4c3180023de1d61185430065eba0a8310201cc7c655d543480019f50d38462a0003b354c62885300065fc12e8302a600aed82107658c0015790ca1c82a80031e5d56018021004f6412e898a4000afb8058e600840167b0bb8287208029f61472590100065fb06e6aa28400e5e859cc605514bb6e8638a85288032f9d943c85400067b98ce2302a600adf8654e32c40019bae6298c4081b27721b7454d300066eb9ce030a86008fe86dd153480011ff0eaa0c4988033e20b764401000677bb0429004000a7d850ca61940015bd07a94c4080033ba0072591310047ec386130ca400abd84dd95388555f18823928719003375ce43980210047f438cab204000cfb7688110040011fb0e20ecb18002af21171d96320047fc3ac990c6000add83d0a6194001c7ea92a2c610002af6133198242006e6a18e498c4000cf5861c543c8401e6f02aa483280033bdca62502100067cc08e0b2a64008fe87d91610800197883baac8080023f21d62440100063ec30e4aa4a000aed82cc662040011fb0e29cc1208029f60f71d95200071fb2aa8a1220008fe87cc564940015e102b00c0aa0033750973181540047f43eca9948000cbd74d0e60945595bf06b90c0a98032f10573d96400047ec30e0aa44200cfb7608110040bdb76c1baa86a0002af61032181540047fc32eb2162000c7f655ce42440015dd0420aca080033e5d972c42100072ea98c4a8a601eabc845c763550018facbb9aa8908029f61730d90210055ec20c73004200adf8558e320840157d08282c61000337dd9434c6500047f438c490420008fd87146608c801978e930ac2100023fe1973948100056ec1ec4b0aa800cdc845cc60550015bb0631242080032f5d340188100055ec26a2b1c84008fd8710e61940011fb0fa10c0a98035ed5270086500066f39ce430aa800cef7298940040019beecb9aa919002af610309881024ecf29ee6aa48200c7d755c46250c018ba62ba8c2a1a331fa187255250005aec2a871
  | 19 => 0x31f1da5254910006cea18e2a1260008fe87d8d610803d9b8c7b9aa890802af6106398810007a7c12a7192a25edaf62dd543508015f500192c80800337d977348640006b7baa42b004200cdd7394e619000157b08284c5208031fd95739452000677b94c4a882000a7d8510563040016ef06aa2a3881375760c7154e500045ec20ed19020008fe8710565080015bf06a14c118ac32f5d365989430056f40eebb1a4000b748150a51940019bec6382a6a10032f5917390a100066e3b46499020008fe8790d65080015bb06200c2a98033714173185540047ec3885b282000c7d65dc553080011fd0dbac62900034f5d14394a500064f3a4e63102000afa800c964940015bf06b96c8080023fa1e6250210006ae41aea3128600adc8650e32540019eae8b08c2100023f61c53d90100066fb9cc29084000f55534c621940019b8e731242080032f9d2721815300477c3ac4312a600cbf835d06054c011f90cbaa6290002d76177050e320066e192e8302a600c7d75d4462040015bf0690ac0109973b9c853986420047ec3ea73004200af6810c860550015f301a94c0108026fa0870552413876a194c328c609dabf845c460550014fb0a324c210002be60063594210066eb26e690c6000cfa81dd92008001db50c38286980023f61c4218553006af418e2aa4a0a8d9c411c1438c8011fb0c392878800367d8f7550d420066e3b28698a4000e3f52591548c0015f70ca8a61100032fdd7644c910006b73948528ca0008fe87141648c4011f90cb9ca4a08031f5d67118943005afc1a43282a000e9d83d9153440019bb0c38a87190023fa1f3159640285cf426e2a9c6400af581992610800177100a9483200025f6147150d200047ec386030aa8008fe86dd6414c161b3e63baa86a112ecfa107254d510046e432eaa1a6200abe82dd7644400197ec839286880035e1c870552500047f436e6aa22000abf83592410400137b0738485208029f61441189530ef5c322a720220008fe861c5435480137d00392a9208023fa1c53590200066fb18e0a1a4200c7f541d943940011fb0fa14c11898f6d95071508100066f98eeca984000afb8050a60c8401d9ca731464080032fdd163546400066eb9ec2302a800cbc649c021440bd97cc3baa8720802bba084118153007cc4028720a6000c7c435d46250c019b863bb46408002ebe1161480200063e902ea3128600c7d405d46250c019ba62baec9188023fe1d61184200065f902e8302a6008fd87d52608c8011ed023b2a8100023f61c54986320047ec3887314a000c7d861c9539400197886ba0c4a98033ddc661480203bd5ec24e1b1aa800cbc855d06254c014fb0a194c320002f5e0d62c40100064ea02e6302a800add83d4a618c0015db0418cc4080029fa1441d8c200063eba8c3b028600cbd205d0625
  | 20 => 0x7bb28e2b128600cbf645ce5244001d3864b228608002b7219538c9100056ec26e1b1a42008fe8710d65080011f90eb2a62100029f61432590210047ec3ea3b246000cbc411d954080015f30020cc010802b7617638c8100074eb1a8720ca000c7e659c36550c01f1f04a1c65208031fdd66558c21004bf40eeb194a000bdb834821004113a7e87ba2a7280038f59564552320063fbacc490420008ff865ce5284001baeea38a86988036ed0270189430063fa8aeca9840008fd87106608c8011fb0fa10c2a98032f5d362181530063e284e2312a000cdc7654d424c0018fecbb9aa8900023fa1f305942135eae32ee8a9a60008ff8754e61900011ff0eb2e43180027ea007150d200066f39ce2302a800af78154a61c800197882392caa18023fe1d6508630006bbb8ee8a9aa200cbc419cb6590001d3864b228728003375cc3118154007ca40a8720a6000cee72d8860550ade5b0a392a8a11932f5d063181540047fc32ea9962000cbd105d06054d134ff0ab86c8a98030fd4974189530053ec28c93102000cd5739c462040015eb02294c2100029f61375594200047fc3ac7100205ecbc64dd543884012fb0a3928788003375cf52188103265eba0c6312a800cbe54dd942040011fb0fb2e4320003370ca70d91530063e3acc4900209bd3d53dd543904011f90cb9ca4880032f20974181530063fbacc49002000abe84cc5650800157b09b08c0a98023fe1d42181310063fa9eeca884000d6d52dcd544800137b0a3828720803ae4c274181530071e282c8aa46400abd841d9534800157b0bb2483180022f61076080100072f98acaa9c8400add851c76348001c7882b2aa919002af60375d91210047fc3aa730c84008fe8710965040019dceca1642980023f61f42982510053f43443282a000cf9769c7208815fabea3ba2a71900357d977454d300047ec38a53084000d9f64dd5434c4018faeb388c4aa0032f10071590200053f428c73102000eb4415c4605500197a84baec9190023fa1b758c9400056e43287194a000d5d7354c21940014ff08b2ca010002b7a0375d8d214c55fc22e23028666dce531c931080011f90eb1aa210002bb60b51988100063ebaccb30042008fe86dd232544019beebb1a8690802afa1030986520063e282e8312a600e3e65591548c8015bf06b12200800367553734854033ebdaa0e0a8840008fd87d0e60944013e902ba464a88023f61f30988100ee5f322eaa1a4000abd840c965080013ed02382a590802be60032185540056ec20e3b1a4000cfa869c2515000197ee9322ca1000376dc47054d300055ec2ec92084000cf580dd9210840157b08192ca108029fe0d65544200057ac08a13102000d3c415d46250c014fb03b9eca9000357d4973185540047ec386530ca000adc8654d31480019b865388c0990
  | 21 => 0x841d95308401b76e1baa86a00023fa1c41596300066e196eab184200cdd748ca618c0011fb0dba2a790003975d554d8d212ecdfc1aeaa1c8200a7f8459552040015bd0632cc4080029f61373d95200063fb2ee899220008fd8710c6204093b3e60baa87208033759373486500063e422ea31286008ff8759721900010fb0a392c8080023f61f42d96310063fbaa42b004200cdd7394e61908d79bae7b24c0a98038fd4964550100065e41ae8302a600af08058461550011ff0cba263100036ed0e70085400066cb9ac03004200cbd745c46254c015bf00aa6c690803375cf31181540047f438cab1820008fe87d95219009373d06382a9208023f61c31982520047e432e898a4000cbc419c36550c0d8deedbaaa590002afe156490421004bf410e2aa4a0009de801c5438c8011fd0fb12c0aa0033e18870585540065ebaec91922000b9d841c1538c801e7100aa483280032f59774486300047e432ea9922000cdd7458e32840011fd0db9aa89000337dd56350c210063fb2ee6aa22000adc8654e32904019db0f3144208002b7617648ca300076731cc49902000aed8295262040019bae7986ca109831f19773551200072fb2c649922000cdf639c321480011fb0e20eca10003375cf62185540075a20ae231286008fe861c153504019eaed31621080029fa1674980210057b40864b284000abe849ce610800157d08392ca080023f61c53980210063eba8c5b028600c7c509c76454c011ff0cba46310002dda06524c6502fe7d380a93146000af6810c965084019bee9b1aa69080337dd56350f100067ac10e2b2a8000ced74188214c00197f00ba0c4a9933570c97550d510057b40c86b282000cf67218631500011ff0eaa4c4081832fddb73552410066faa2e6302a800cbd741906254c016bb0aa1a63280e7571cd544865000736a14ea3128600d9f83dd1214c0019db0c39263102af671077550e320047e432eaa1a4058d5e43dcd54548014f90ab86c6108023f21973909100057a40ac430286008fd87cc3650855b5bf06b10c2a98035721573181540055ec26c3b02a600abd841416308401938eca1a849880373dd77250e320076b29cc298840008fe87d95428c001b3d08382a719002be219518c1200075aaa0c298a8000cfb81dd920080018feeb31220080033720573181540067bbb4c4880200097d85dc14388401cbacaa9c6520802b760c65590200053f428833146000e5d6554e32c40011fd0e282c7208023f61f52d8c10004dec20e0a9e4200a7e850c9640840197eeca1a8528002afa1065980210065fa1eed208405ccdc63dd543c800157b09a8cc4080023fa1b748c950006bcbaae010aa00087d851da420400157b0832ac6081875e9837454e500055e432a920a40008fe8718910040018fea6382cb210026fa1b7550d40006
  | 22 => 0xbaa87908023f61c43d94200067ba8ce2312a600cdd73d4462040013bd0038aa7190032f1d9545091000576c10c8b1820008fd87cc262904011f90eb2a8518803b65017318154004fb408e0aa242009de81dd5438c969abe63ba2a6a9002bb60850d92310056ec2ee9b1a4000cf9861c153c800197ae9980c4080023f21d64486500057c40242b004200cbc419cb648c0011fd0f31283180023fa1c32590212d4bf416eb214a0008fe87d8d6008401af6e5b82a9280031fd5070596310059ec20e4a9ca0009be801c943904011fb0e28cc518003731c87050e320047ec38653004200afb8050a60084015d904b08c0a180357e17734865000677bb2a498e4000b9f8550d424c4019bae6180c2aa0032f1d163584200065eba2e0312a600cfa869c2524c001b38a8b98c2aa1773e9c353986400057d4006430aa800eb564585410800197e81bb2a8108026fa1b7550d42006bc294e010ca000cf7621c56055001b3ee8a1a42980026fe0d74085400057b408c5b0aa000aee8214164084c18f8cbb9aa9100039ee1560180210047e43ac8a9462a6e6c5098a4294463f330638286a00023f61c5498a300055ec20a0b184000abd8419660084012fd05b9aa928002bb6085058c100053f428653048200afa8094e6190157abaa9baa87190033748573185540047fc3acb10a60008fc865d2514c001c7f0bb22a4880038f10575189430074fc1ec919220b2d3f51dcd54508019b8c6392c6080023fa1c3259410004fc402eaa0e4000af58114164080018f8eab1ac0108039714273185540047ec38a230286009f4815d232840015bd06204c528802bb2096350a502e56e41ae5b2a8600b9f8550d424c0b79b8c7ba2a7900023fa1c62545400047fc32eaa0e40008fd861c543880019b864ba6c6080033edda62440100067b3b26310a8000cbf64dcd54884017af0aa1a63108027ea007154d200047ec36e0a1c4200d9d64dd5438c857b3b0838287190029fa1740984200055f426a3b1840008fd871086054c019f304382caa0802cf20954906500066e39aca90c8000afb86549408400197ce8316c2a9802bea004198a500056f41ea53084000d9f405cc6155001d3883398c0aa0029f61432592510f66f31aeaa1a20008ee821d954040018faebb10c2a1802b760f52181430055e422c23084000c7d625d5439400197ec8382a8988032f5d040189530055fc22e23128000e5c5058d530840197ca838ac810002afe1171181520065eb26e6aa240009dd851c1438c8015bb0632cc210002bee1d60181430055fc22c39004063db4411c941040bb97cc9b9aa8900033e5d971c82200066fa12e6302a800afa8010662040015b90ca1c6528802b7a0c4198a500055e432a920a6000ade8310662040efa78a1b9aa8a00031f5d75498a31005cec2a8719482008bd
  | 23 => 0x18953004dec20ec10aa000cdd831d9544c4011fb0fa94c1208031f14271d96320072fb1aa6a8a4000cef7298941040010fb0a3b2860800337dd16354e200072eaa6c6a8a4000c7d651c953c40011fb0f21cc4080038fd9554509300047f43e62b2c8400c7f7598520080011fd0e202c6108c6afa0364906300056ec1ea53084000cdf30dd9430850deb662382a728002be60064980210057b40ec8a8a6000ade8314164084013f50039262a00032f59372550100065fa12ebb2464008ff8754e61880019eb05bb220080029fa144198021004de43aa899482009fa801c554480018faeb318c4080038f55142181510067ab98c210a8000abd8418921040015e902b264328002af61050189430047ec3e8530c600097d85dc14308401d5aa53a0c4a98021f61471590200047ec36e6aa620008fe8795163080015bb0628cc121002afa133198810005cec18e0aa28400d7b741c153940015bf06b1420080029f61740986520066eb9cc73102000cec621c5424c00157d0998cc52800357dcd53509510067bb8cc2a844000e3d85d9153484b99b8c7baa8690803370c87650e500056e402cb1946200f4c8254e32544018faeab90c2a1803a758d4390420265af41ee4aa2a200cde731d9548c8b5e5b08392a8a9003add0e61904200063fb2ee8a8a40008fe87d4563080011fd0e282c8100033758c7150e200066e39eca90c80008fc8758d52900015eb02284c21018eed2112108410007572a4c4a1020009bc805d543904011fb0e204c319002bba0841982520055f430e0a1a84008fd87cc660948011fd0e3b282100032fd9372551100065fb24e110a2000c7f655d1314803d5bd07bb2a990943a7191538c9100047ec30e0a984200cdd73cc061550019bae8b1c631000277a047054e320065fa82e8312a600e775398551080018f8a1ba2ca100023fa1f65506300063fb2ae92926000cdd655ce218c0012fd0db9aa8a8802bd20565485400065ea12ea312860097d83dd6429411ba7cc9b9aa928003add4543185400053f4288530c60a2d3c64dcd54544011fb0f984c528802b7a0f42d94100053ec28c48802000d7b539c021940019bacbb9a42a0003371ce61484200065f2a4e3b22a67abda80d8e32900012fb07394a328002af61351181430065eb26e6aa42000cbf60dd543508018facbba2a6908bb671cd54485400067743cc4a946000cdd305d3658c0015bb07a10c2a9802bb60830988100066e190ec9902033d5e435ce51940015f301a14c010803a758d43906200066e422e63102000cf57658b10840011fd0f312a3180029fa174098a310065e20ce1b1aa800a7d85cc164948014f90ab00c0108023fa1b748c9100066e29ae630aa8008fe861c1544c4011fb0e200c4a9803ad10671189430047f43884b284000aed8214163904011fb0d
  | 24 => 0x84000c7f615d543548011fb0db9aa808003370c975d92300053ec1ee9b2a402bade80d92328c0019b8643b2a720802afa0373d912123f1e32a8720a4000cdc7398962040c38fccbba2a6908023fa1f43594210047ec38a83102000abf85592410400197ca8ba0c4a9802bee0131980210076b430e2a9a6200ade80d92328c4018f906ba8c4a18023fa1c505923200577410a130c8400abd840c262904019d8e4b122008002b7e19438ca100061e20aea3128600d6d851c943884015db0420cc010802b760c50590210073da02a6302a20097f845ce5294001a7f0bba243280029fe1165940100055f420e0b184200cdc435cc60550019eaca38a84080033bd9372581530063fbb2a8a8e40009dc805d5438c8011fb0e194c210002af60f65906400063fbb2a6a8e4000c7c509c861550015bd07a14c3280029f61730988100047f43860b204200cbd525d06254c0197ee9322c6100032fdd97454e410066fb1ce010a4000add83d49648c4015bd0620eca100031fd9671081100066e194e030a8600cbd735d06054c01abe60ba8c2a18033748173181540053ec2e81b184200adf8458e32084015f30fb04c0108029f614311895400576c10873102000a7d82dcf65440011f90cbac64880033358c7250c210047fc3aa630a401cc7c65dd543480019ba80b98c0aa00337dd16354c200073c284e0312a600cbf7498921c40018fea63b287280023fa1f31594205456fc1ae4302864d97e81dd63194001b9eea3928719002be60354980210047f436eb20a40008ee821d953040019deca392c2a1802bba0841980210055ec06e8b204200cbe7498b6154c0157b0bb9ec8908023de1d6118554006ecc18e0aa62000c7f52dd9530400197ae9380c4a18032f5d062181530056f41ea4b2020008fc865ce525000157d09a8cc5180033790e7608530004bfc2ae1b204200a7f855c061548011fb0fa06ca10802bba0b6354940004f6412e720c4000abe840c9650407fab8a0baa86988033790f768c8100063eb16e6aa4a0008fd87d446250c019b864baec6080032f5d053188100055f420c430aa60087d851d941080013dd04382a8908032f10670d92323c4de436e6aa280008fd8710e60944f7af6a6382a5200032fd9574085400055fc328720c4000af980196600840193ae6ba0c0a9adb4fd0373551520047ec3cc830aa6008fc875913204001af6e9b82a7280023fa187154d200063fb2ee4a1a2000c7c7598520080018faea28cc518002b760f42596300056ec1ea4b246000db5431c5425445ba7ea4baa86a0002b920562189432f66e3b6eaa1a6239d5e43dcd54940afa7882baa86a900337d817550d310065ea02e6302a800cec629c6424c00197ac8b9c83100023fa1b7550d100047fc32e6104201c8fd87d976050c011fb0fa1cc2100031f14271
  | 25 => 0x1a7ac9b9aa9280031fd0175185430053f428633148000cdf105cc605500173900a1c65208032fd937550e210072fa9ca6b204000cbc641c9534400197ce9380c4a98033edda614802013daf428e2a1a6000c7f651c543480011f90eb1a85280029f61462185430056ec1ea4b2020008fd87142628c4011fd0fb1ac4aa0023f21d65508100063fa8eeca9840008fd861c5530800187aeb3a0c4a9802af610325964000676c08e4b2a6000af48158d6108001af4a4382a5881871f9977454f210056f41ec530aa800cbf7650d428400197eed2128508002776107154e322f65f326eaa1a4000d35541c542544011fd0fa8ac8100032f5937550d200071faa4a9314604ce5c635515148001d986131464081db67cc77550d400057bc0aa53084000cbe541c5648c0019b8e6b2243280033ddd962440100047ec36eb1962000cde435cc605500197b09bb2a788002d7e1153549310065fbaec8a1220008fd870c0625500197b0c382872080277e0d72d90100063fbaac488020008fd87cc66204001b98e438a87190031f5d5701854326faac18e2a9aa200c7c651c543480011ff0cba4621000367e1173d895429d9f42ee0a1a8400ecd43189524c4011fb0e28cc4080023f61f5498a310065fb20e0aa24200aee82106608c8019b86538ecaa18031f195748c5200069e282e8312a6008fd861c154c84018feeb32ac8108023f21d63546400065fbb2a8a146000af98010a600840157f08b88c4980033d9c761d81320047ec3e81b2c6400af587d8661080018ff0eba8c4a18031fd497418953006b6a96e8a9a4000c7c7654d5250093b3864baa87208023fa1f405963100677b94c4a842000c7d755c06250c011ff0eb2e42100023f6187254f100047f436eb2122000cee72d8b6154001cb864b2aa72098737ddb7454e3200677b20e4b02a60097d84dd421940019bec7b8a86902636e4c07050e4100677b94c4a802000cf68798551900019d903bb24010002b760f52185430063fb2ae728a8067d7b531c151080015bd06308c0aa003e3209438ca410063ebaac23084000b5f8454d524c0013f500392638821f5d4c47154e500065f426eca9e2000ade83d0a6008401978823b286100031fd95748c520005afc22a7192a2008fe870c964940018baeab98c2aa003b30c972185430053fc2ae0312625dcbe64dcd54880019beebb1c82900031f14272d8d540053ec28ec99020008fd87d4b64040019b864ba8c0a1a2757cc77454e500063ebaae630aa800adf84596328c0011f90cba4a2900023fa1c43594100066f986e8b184200d9c325d06054d1b4ff0ab86c6aa0023f21d63486402de6e31ee8a9a4200e3f6550e41480019bea4b98c2aa0033e60b76440100047ec38a73048400cdc321d9439453fa78a0392a92080337d93734855000676b28e498
  | 26 => 0x32fcc57418153006edb86eaa1a6000af5811406250c01abe60ba8c4a18026f2017390a410065eb20e0aa64200abf845c7658c8015bb0bb9ac6108df4f1057550e500065fbb482a0e4000a7c8259650040019eb0d388410800397d95438c9100047fc3a643028200cdf63dc143484015f301a1cc0108033dd8f71581540055ec18e5b222000cbc641c564080013ed02392a6880029fe0d54181520067cc30e0a8e40008fd87cc662900011ff0ea90c2980039b550625493100676b28e498c4000e5f5394e61080014fb09b8eca900033b20376484210065e20ae6312a800cdd739d46150c019d8c4382a4988033edd962440102e4efc2aeaa1c6400b3d85dc143508015eb02184c2101feeea0364906500065ebaae8312a600c7c65dd232440013bb07b92a8080029fe0d54181510066eb9cc6310200097d85dc143484015bb06322ca10a7eafe1171189540055ec2064b2c820097d849ca51940012f90ea9a43280036d9087150a100069ebaaa919482008ff87594219000157908b8eca1000367cc574189530056ec18a130c8400cbe535d06254d1ba7e81b9aa9280025fe1570d8c210065eba6c2302a6a8dd9401c1438c80187ceb3a0c408002b7a0c5098642006cec18e0aa48200a7d84dcf65440011ff0ea94c320002b760c62440100063eb2ee6aa44277d3f52dcd54500015f30029cc0108023f61c5198a400065e3a4c49082000db5431c542840011fd0c382a498803576147150e322a6cf29ee6aa28400cbd7410a608c4019b865388c0a98031fa177650e200066e194e030aa600afa8095163080019dce4a90c2a00031fd977454d100069e422ea30a8600cbc40dda41080011fd0fb2ac8100032f1d954485400047f430e0a928200a7e85d0062040019b908b98c2aa0023f61c43984202ee3e3b6e6aa2a200cbd74d4862040016bb0a38a87190029fa0861941500065e3b2a898a8000db4711c154904016b902a9c65280033718e70085200065aba4e23102000e4d53189524c4019ed0d38ca4988023fa187155120005cfc1a432028000abe84cc76508001daaa630a62a02371fdd763581540071fb22a8a926200c7d65dcd520416da7883b9aa8a9002b760375d8d210ee5e322eaa1a42008fe87d0165084014fd0ba02c610802bb61f62988100063e282e7b2c8400cf57198720080019dd01bb242108023fe1d63886500063faa4ec10ca000c7f75d8d60084012f90ea9a85280023fa1b7454d100056f418a33148000a7d8510662040019daed30e4110002bb20965885300063ec28eca1aa261c7c65dd153480d5b3e85baa86980033721573181540047f438a2b1c8000c7d755cf6590401d38653a0c0a98029f6144198a500063fc3aea30a86008fd871046054c011f90eaa2c610802b7a0f5218810005aec1ee4aa2a200c7f65dd15348
  | 27 => 0xf40ec91946071e9c41d92328c0011fd0fb22c608002afe1171d96300055ec20a530462009bd84dc553c8001aeee638aa8a88023ba087650c104decf986eaa1c8200c5d735d46150c0197882392c808003d6e01534c6500057dc02c430aa65bcdf60dd1534c001d3aa9b1c82900023fa1c53590100055ec2663304a400cbc411c164084015f301a8cc010802e7e15438ca410066eba6c728a4057b3e84dc553548015ef0eb08c2a9803375cc30986420047e432e720aa0a1d5f30dd15354401abca1ba2a6980032f5d340189530057bc3284a8e2000a7e8519163040018fe80ba8c4a1803ad50c61c85400055f42061314a28bc7e861c554940019f6c5b82c2aa002af21171d8c200063fbaac8b004200cbc74d8d61080019eee330a61100023f61f53986400063e286e8b282080b7681dd64194001d9906b10c408003ab9526250a314bdd7416e92948200abd85dd1640840197ae93a8c4a19772f1937355121004de412eaa1c8200cbf435d06054c9373d07b92a9208035bdd07254d520057d406c3b026400af48158b6050c015bb06204c3190023f61c5098642006ea38ee0a1a625ccf671952628c4014fb03ba6ca900038fa1275185430066f98eeab1840008ff865d232840019bae6184c32921e9fe1570185530065f282e8312a600d9f425cc605503b57d09bb2a710802bd60443984200066e194e1b246200afa801056394001972e8b00c0108033e61a70887102f4dfc2aeaa1c8200abe8414363084018facbba2a210002af6166290640006d7b96eaa1a8400cf5769c321884019bea2b98c2aa00337d8f7550f200069eba2a810ca000c7e215d46250c011fb0fa94c318002b761375d8d210055e432a92084000d5d7350e519400157b0a386c8908023f61c51982420047f438a4b246200af6810c965900013df0e90842100034f6107254e500055f416cb20c80008fe8798941c40011fb0e20cc010802af61065988100ee5f3a2c9b0aa661c7c65dd15388001b98e4382a7190033718f75905200047ec3ea3b184000e75315d46150c019b8e631242080033ddda21440100063fb0ee6aa2a400cbe841d953480013f100bac64a023f67d0b7550d31007ac402a698ca0008fd871406250c015e902b22c21000337dd763505200047ec38833146000cde83dd954c80014fd0a20cc1191d7ad950618c5400066e188e4b18205bcde63dd1538800167f06aa284a88729fa177650e200063f3b2a9192a200db4721c55490401bd242b804210002cf6147250e410055f426a33004200cbf425d46250c015f30121cc0109665fa0b758ca500047ec30e4aa42060c7e65dcd54c400197ae9a10c0a9802b760f62985540047ec3862302a800abe84cc6610800157b08194c1288033760c76551300066ebaac71962000cf780dd921084011ff0e990c0a880
  | 28 => 0x21c554480011ff0cba4a3100031fd9471551200047dc3ac03028600cbf65dd121500019bec638aa6900023fa1c32592510069ec28e4a1c82008fe8714964040015ef0c90cc010802bb60850988100047e43ac890c6000db940dcd544400197ce8308c0a9802afe1563906400067cb20e0a902000d5c545cc60550011f90cba464a880337d8c7054d210056f430e0a1a62008fe8714964084015eb02192ca100023f21973905200047f43860b2020008dd831d941080018f8ecaa2a2900027de1d210841025e9fa12eaa1aa200c7f76551528c4011fd0dba462a80039da187154d51285cf420e0a9c6400cdd83dd954c80011fd0fb2ac608003375cc63189540056ec18e2b284000cdd748ca608c4019bec7ba2a790003375cd61184200065eba687b282000e5d65552328c4011ff0ea1cc0108031f99574d942021d6f40ec91946200c7f7694551c800157d0831cc010803ad10261904200047ec3ea9b184000cbd74d4462040015f50020ac6108027e2017590720004fc402eb1962000a7c8648650540019bec7ba2a7908037690e70949300065eba685b2820008fc87591528c0018fea9386caa18023f61b748ca100047fc3a86302a4559be82dd2329040157b09a8cc1210031fd947250d100063eb2ee4a982060c7c65dcd54840018f8eca9aa290287570cb7454d51005afc22a698ca000dd531dd54348401b3d06382a9208034fe1175d81430056ec0ee9b1a40008fd8715262040018baeab98c4080021f2197550d510066fb1eeaa1e4200cdd63dc14308401d3ac8a1c6508002b760c65980210065e326eb1922000abf835506150801be242b804208002b7a0c64984200047e432eb19282008ff865d252840019bee9b1a6290002af61331980210056f418cb30042008ff865d631c8001b98e438aa719003570c97518543425afc1aeaa1ca000afb804ca60c84011fb0faa4c4080023f61f53d90100047ec388030aa600a7d81dd565080015db05a04c4080023f61c30984200047fc32e720c40008ff865d021c810b67f08baa8728002bb20964588100057ac0e813084000c7c505d365084011fb0e286c9190021f614768c8100047f430e4a0aa000af6810ca609440197e80b98c0aa1732f1db7550d420057cc0082312a6009be80dd5439046fa78e8a9a4328002afa1052986300057ac0864302a800cbe54dda4108001aeeeb10ac010802bd6045058c200047f438ec99020008fe87d0163084b73bf08baa87190033721573188100055ec26a23128600cbc545d06254c019b865ba2c610802772057550e320053ec2e61308409fcbf7418961550018f8ea31240080029fa1442984200066fb26e690a6000ddb309c06150c011ff0eb24400800327d0173181540057b40864b2c8200ced7658720880b99bcc7baa86881b7a794d63906400056
  | 29 => 0x82a8a100397d95534c520005cec1ee4aa48200add84dcd63080015eb02282c919002be600529802100796412a8a9482008fe8718941540011fb0db8aa790003371d943549310065eba4a93146000cbc525d06054c0197ae8b16c2a995367cc17550d4200576c10a73102000af58110a610813597d0c39287208033b60776480200047ec3cc83084000cdc855cc6155001e7100aa28528113576147154e320066fb9cc6b2020009dd83dc95444001a7aa838a85280032f10d74181530065e3a4c29084000a7e8518e60084019ece3b08c0a90032f4c974181530067b43cc2a8c6000c7d65dd153080011f90cb9842a800337dcd61480200075d430e0a1a80009be821c143904015f50030ec0a10029f21953545200065eb20e4a1c20008dd831d954084011fd0c382a8990023f21975505200067a310e2b02a800c7e759c46250c019be63bb28610002b7219438c9510063fb2ae729220008ff865d132840018faea294c3200029f2195354910006ed21ce010a6000cbc411d9439480197ae9a16c6080032fd927008510415b7416eb194a000cdf7390e6294493d38c6aa482900031fdd721580210047ec3cc63102000cdd65dcd428c00197f0aba0c4a98039ecc154181520063ebace8312a600c7f54dd9520400197ec9b9aa988003275d173181540047ec3cc43028600cdf615d5434c0015bd06286c810802b7a0c51988100057a40ac898ca000eb664985410800157b0831aca10ab7571407154e323be9fa8ee6aa2805bddb60dd1534c0011fd0fa02c7290029fa187154d520047ec38a33004200cf682dd910040013dd04382a3108031fd95744c9102c5af418e2aa2a4008ff865ce51880011fb0db92a8080031f19573909100072eb2aa71902000ade8319260084018feeba9cc120802b7a07658ca300055ec2662312a800cdf63dc153484011fb0f986c81096f3798f7454d100056fc1aa530c6000abe82d92418c0011fb0f2a4c4080031f58b7454e500063e284e430aa0008bd841c965040019dce5b10c2a00029f61740185530063eb9aea30a8600ade861c5534c001db281398c0aa0032f99271d91530055f42065b2820008ff874c861540015ed03b16c2a80023fa187050d210065e20ce430282008fc8758d42040011fb0e29cc5200027da0470549310055ec26a2b184000a7e85cc26008401adeeb90ac010803370c974185532e6edb06eaa1a6000c7f541c1658c8014fd05ba6ca880023f61f52185434463f430e4a9ca000e5f5394d6404001d3ec720a82900033790c7258e500063e2a2ea312868dd3c41dcd54940015db04324c408002b7e0d72d96410069fba2a898ca000abf845c763080011fd0fa92c7208025f21d548ca500047ec36e2a9c4000cdd759cc61550011ff0ea9cc390002e7e15434c5400064e982e8302a6009ee8
  | 30 => 0x951000576412c3b0286a2d3f42dcd54544018fecbba2a4880032f5d7649091000576412c6a948200cde539d8214c0015bb09b8ec6900023760c7654420006bb428e2a1e42008fe86dd231480018feecaa2a5880031f20d75188100067ab8ce4302a200cbf65dd1214c0015f50020ac7290023fa1c62484100065e982e8302a600cde53dda32040018feeca9aa5880023fa1c5458c100063ebaea5b202000c7f305d46150c01c7aa8a90c2a00031f5d753986400055fc22c31004000cdc7359162040015bf06b1620080021f6147258c1000796aa2a520e4000cbf64dcd524400197882b98c0aa2d35718f7454d524c6ce190e0a1c8200cbf425d954040015bf0ab1a62100023fe1d43181210047e43acaa182000a7f855c061508019bae6ba6cb180033ea0b76440100065fba4c490820008fe861c153484017750121482980023f21974949311bd9f426e2a9ca00095d851c5438c8013bd01baa8719003379d943885300047f430e2aa26400cef8758862040015b900b1c64108026fa03748ca410063eba8a23128600b9d84dc5538c8010fb0a3b26210003379ce72181540047e43aca90c8000cbf641c9544400167b0aa1aa52080337dce63594100066eb9ae8302a600dda831c154c4001978a0ba0c4a98038f14164550210065eb2ee898c8000aee82d0e6094801daaa3398c2aa0023760c70594210047f43880b1ca27ceac4198a5290001d6ca930c8210002be60041d96320056e4328698a40009be86dcd54500014fb07baaca080023da047654c200055f420653004298abf845846050c0157f0caa483900033d9c561880200046ec18ec10aa000e5c325d46150c014fb0ba04c5288023f61c52982310071fc26caa122000cbc411d9548c00157b0998acb21003375cc31982520056f41ea5b20205ecbc64dd543484398f8cabaa86880026fe11765042053f2e282c6a1ca200e3e64595548c8019bcc6ba6c7280023f61c42980210f53f42ce3b1aa8008fe87d4d64080018f882ba8c4a18032710573181540047ec386331480008ff8750e60884019b864ba6cb188031f14072594100047ec3c87300421da7e859cb6454c01cf10ab00c0108032fdd56450c21004fd406eaa1260008fe86dd54348401cbe62b2aa61000337d837550d3100576c3642b044200d3c855d06054c015bb0620acb190029f6173098a4131eda3a0428802000cdf315d46150c015f50020ac6100032f4c574181530066f21ce5b1aa8008bc865d543508019bee729cc5208023fe197390b100065fc20eca122000c7c529d821940015eb03a1cc210002b760c7059021005ddc22c31004000e3f84d9641480018faeba10c4080023f61c429863000677396c4302a2008fd87d4e60908019eeec10a20080023f61c32d90100053f428633102000abe840ca61940a973d063
  | 31 => 0x2000cbd739d06054c015f30020aca10802b7e0d721855000766b1ac49902000cde739c061550015bb07a96c8080029fa144158c10004f7410e0a1a4200abd841d932040015bb07a14c31800375cc671181530053e40acb2804003c7776dd551c40011f5003b2a610803a7591548ca300047f43cc4a0ca000adf8550c624c401b6ee638aa9208023fe1d62185532bf1e322a6a9220008fe8714163908bf9ece22a4c518803754c77454d210055ec20e4b282000cbd861c154904018fa42ba8c2a1802b7e19438cb100066e194e3b2460008fe861c953440011fb0db8287908023f61c329824155ecf326eaa1c6400add8310565040015dd04284c3190023fa1a71949300065eba0c8302a600c7d7558e21940014fb0a316c0a1802b760374d8d210065eba081314a200c7c501d9548c801aeeea90ac0108029fe1153181510ee5e326e8a9a425bcde62dd1538c80157b09a8ac7201af571437454d300f76a31aa918a42008fd8714a60904014ff08a98c0a900397e0f658c910006bc3ace010ca000abc8650e41080011ff0ea18c0a88033d61e61c87200066fb9ca73148000cdd105cc61550015ed03aa4c5188032fd9373551210063fa9cec10ca000a7e861c5545480197ac9b82a8108033e58c70544200047f438c490e2000e6f54989528c0014fb0a20ac728002b7e0554d8d200067b400e2b226400a7c855c3648c8019b86438acaa18029fa1464980210056f418813102027d5f515d5434c0015f30021cc0108033ba1e62548100065f322e7b202000cbe741886054c01cbea2b1aa6100031f209751854359f1e20acaa9c849bcbf74d956150c015f700994c0108023f61f31d96405c62fbaee6b2a8600cbf40dcd64084013bd023828719002bea0032986500056ec2ee1b1a429fcbe861c9549040197acbba2c2100031f5d6641842000677bb64290040b9c3f75dd16550c018facbb9aa98825aeba0b748ca41006aec18e2aa4a0a2c7d75d8e615500197b0c39287208023fa1870509310047ec3e63314a000a7d851876050c011ef0eb08c2100023f61f5498a300065fa9ae8302a61dcbc645d543440019bec1ba2a698802be60032d96410065eba6c5b0aa600e9f3059143084014fb0a214c3280023f61e53986400053f42e60b20425ccde62dd5438c83d9bce7b18c2aa0023fe1d65d90210064eb9ce8302a600cfa869c0214c001bb6e1ba2a69826f670cb7550e410066eb02eaa1c6400db4711c14390401abaa6392632819b730c8714c8200047e43acaa0840008fd861c543080019bac7b82a61080337dce4398a500072fb2c6298a4000c7f655d232440019bae6b90c2aa0023f61f52982310057741082b2c6000c7e325d46150c011fd0fb2ac0108023fa1f654c8100067b38ec23026463db4421c54204001bb6e8382a6980029f60f72d
  | 32 => 0xe80ac002006000809c00601f00c00f410c0fd03581b00ea10800400c800004800100cc00a08d000820400601b02a84157f01de00104d4006042000004801800b830004014600800380000a4489045803c00000200000080ae005001001c07601a000001001200c00000f007808f001000400000c04600a402601400700b82c0060008803c03020a2fe0db00080b8004000800a2c60003c6800a003009804800000502a002c05404200f806408c00200b000800a0030080018000d950000f2801201804b000001e000038802803e00000104a8048001023825400a003004000000000a01600ac00a01800a037007c02400800040000db000003002800c062000000001201101d8bac00100c801c00000000780b004600203980100140a3003000c034002002800000001e005804403e0020068000002002022082c00401f0038054014009000023c0be00800000040f600301080000180000140bcc00057204803e800001a00180080d200300100d420e013023804c01e4c801480b006614f23200080d8000019802c04c09900000940440000000028004000006017809a00003500340c2004000801000e0120040000004008006027c050000000002403e034021017000000438d800000200000a800c01c008021004402800000100000420230148000a90003002805809e01d0100004034006019800402e00306881506e400102b803c014002011015400800a006801c01a13800001f0002003000800000600b0000038010003003800c2480000008010010015001005c05c002018803009206501800000ae01202403d000200000000180c608f21c800000600a00000001a2019002808803a00101000040020061430000248002032001400c015005000401c0000a3001400a00b002808c03e00700001c0204005000801c150005134802000000306d813c00000700084280ba00000102e0000002002104c008003002803800e001000801800c023028001c02600108e800001000d013001800808b000800c00402f00081a800403900000080060150008014114003000001801e002584802800801104580680100020000004008008000008800207600500080000000008258086000000004805c021005000000200000000100e205600f800800400000a0010258002002800c00e05d146806400e02800000f402203402f83b8002000000002c01800c0065eba2e6302a865c7d7518c61550011fb0e204c5188031fd877454d520063e3acc48802000cdc805cc615500197883380c4a08023f61f519881000576c10cab1820adadf835c86154c018fb0a3b28690803ab55062509300055fc2a8630a8400ade839d262041138feebb22c0a98032fe1d74181530047ec3ccbb184200cb574184215000177708b0a4010003ad10671181540e73a32a8728a
  | 33 => 0x7600716e000805201407a009000600a001004c00c02800502d803e010001806000201100c8004022029017004c12213b000002c02402a002800000200900180200020380138000000006057012dcae0020000050006048000019c00c012001a250006002012800405402601300000000000048020108001000012401600701100d800200400000200040010000018050044000000000c04600c809c00000a010801401c000006803000600402b803011a03b0bc02ac012011011019c02602773580180240091eb00dc008038193829800006a5870018008016001800002600a045000801800b004002005200c01180c40100310078070476028004000800a004004027c00601e00000980b605000081c0000001005008c0180130170650000025002048869800b005814c58e1db0010000002089019802c00200200800582fa00700b00506800000000014010000000002800000508b0030014001000000805202f00e02b00fc0010000018004000000007c00003f000000450a000007002801a003000002c1ca01300000ac01400003a013c01400100b80000060380018078000000019801001404609000000000070018024002001005008466e04400201d001603400400c00ae065000010801e06012b001002800e020014c000004005800127402500500000c80ca000000000c00502d003c63a00f0018358000005044844c06e00000f0f4c00009e01000000560340058ab800c013001004001400900f00240380030228d543ca000008003002200701080940f0001000801000a00a002000400a0060008010012000003001002e00100080ac00a022002006c000000004001800e00e0428134014005009000001e76b01d802c00c2df0000010040021005000400c013001021000400200f000800000a01a8044018013005039800000b0020000000005002002c06800701103806341640a9800000404500c01840200414832dac01a00200f8040040000003000009003f001801001800000981d003204901380d802a000003800002a0030c6003800a01300000b405a00209c810c05200300200ec232004019800001a648002800802800c000008c14a0380060018012034006001091a000025000000a021000000400000c059000c03c009003807004804a06a000027200e001815015807416a006c058003000005c004067002006004602303000340ca0090020864002011166006004200d000b04804e47d000801400000d00003ec00400000600180020030000018000005171001800606a0008c640002f10228044004026005000c00201a0068340270002001001801c2270b7000c10c06a00203c404c01100a8000032089001021001c00502b003400200201c830c00001400400cc02404602c00040ba3cf00b004c02400000085a444e1f401
  | 34 => 0x8800002001f0068009da61d801c800000a00a0008005282006206004400202901d00000da0020030d04006000000000402800b000800003200b002000002c00f037808c00003e000019419602300200440009d7010803401c0490060000000092002009c00e04c06d00b00c6000010a37408200f03e000400001f00b8000288000007000c4f80190160118000002000002009a77a00480bc00800a008003400207a0018064014035007800000000506184c400201c085805c082000004003c02e000002003000c00f0108038000005000800003a0050028a4400000200180040080000010005a2e00b05c007c0000911d500612a4000035001406e00e001002800200300601f404e20a004808c0000b600900d000802d05d000c0da01601a000005801000e801400800204700c0058773008808c03a00000780200060070210030000005001001000800000180001ac00c000800800000f80f8080016055003803401600005c009401002a0000004008042039802008804607d80180200060000000056000002000004e012000003c0740070010040006075009000000c08d244805c010001002019c00001d05c001c012003000853c01000e000022400c018007008000600805a802802e00001c004804800000401bc000097005006c0028f700a804000004b02b00a401e006000000002e49a01d800c00000300403dc00000b04e801c00a00200d007800a009004810008400c00f8078000058000000001c00200080000000010018090cd4001016800000c00900180a0034000005804800200c049802ce4200300282e8000098002812000204300180d012e01400495d401402500900ac0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc01477956007159132007162157358060084014b491593735512000533a6173588620400153990105751894300527245745cc605511983f855d2701895400553648505cc615500129e981056350c20004972598550e325440146f956007259131004a7a6032591430400107d97a14621854300437a60415cc60550010dd9818c715512000653989851c5438c801c4d5318870549310070d5d4419c46250c010bd989d062d855300617141831d9544400189e835d040189535fd17e5952dd1538c80143e952097418153006175d98550e32940010dd97a0f62185540060f614411d9410800107e98d0175185430051765c505cc615500189f6060c70552410051b648415d46250cb74d4964c77454d21006175d683d0862040014d5910c974d96310062d25387584610800185d6560f725501000547a50325d46150c01c3990105751894300627211831d95444001c1e93d4974189533051d25951dcd544400185f855cd7018554005a5e554318531500014b697992615042000627211735c0615500145d931d676086500050f65476905410800146d9214272d8d5400617a60505cc6155001c3b855d160180210062760c411d954080014b99010670d954300617dd783589100400185c76e1153549300051d644509c76454c014b7935d061085400062e192801c94344001c1d950c974181530061761673188615500145e93d0975189430062720d745c86054c018b97420162d85530060fe15745c06254c0143d9414870594210060fe1d54508605440149d9418f768c81000627a60325d06054c014d5910ca71d954300707a53515cc615500189e845cc30185540061754583dd954c84018d776e0d62440100048fe5580dcf644840147a985d560180210062761163dc553080014d9900c975d923000517a57805cc61550014cd9214173185540052d644641c56408001479900c9751854300617660325d46150c0143e94e0575185430060f610501d82154001c3974142701895300437e6173d8861550014d8905d763505200045764f87553219400125e980c96554c1000437a63525cc605500125d95219438c81000716640325d46150c01c1e94141731855454627e0d749c86050c0145d93146760865000627d01831d9544400189c845cd7218554004a764c865524108001c2d526107654d2000547a54415cc605500189c845cd71181540060f61564dc1430840189c322197550d400060f195841c9534400158d9210573181540042fe6176d924108001c9b9050173181540060f1d5841891004001c2f9254974189530060f614411d943080010be980c9741815300527e4d205d06054c0149d900c9741815300653614721c5438c80143d95108715902000527650768c9320400186d7520961d81430060f50985dd9438800146d9214174d9632
  | 1 => 0x100527a50505cc615500115e98d49731815400707a4f425d46250c0189f6460c70551210072521173584610800143d97105751894300556640325d46150c018b787211611842000617d85831c5549400189e845cf511881000497e5580dcd630840113d94e1d5388650007154c5105d46150c0183e9814174189530062720d745c06254c0185d8558f7050c210060f1db83551515000189c412197550d300060f5d584d4763080014d9900cb7558c2100627a19831c15490401c55910c9751854300617585851c5438c80149d970c97418153007135d483588620400143d9510b769042000536640415cc6055001c359114174189530064d985851c943904014cd93a0776480200060f610501c9650400185f316177650e1000617dd9851c5438c80189d845cf31d942000726a40415cc6055001c595318870545300051764f825d46150c0185d316177650e1000715546831d954440014d491597734854000517644505cc615500164f9454c625493100715a44505cc6155001c2d4248175189430052765030dda320400129c9661543905300060fa1175d446250c01c5a900c9751854300726e41305d06054c0125d95205638c8200052b648415d7648c80183d75a1351188100051d644325d46150c014d9900c974d96300063318e821c5434800183e855d330188100051ea5a759c0215400115d9321d54086500050fa53815d46250c0185e6060c715525000547a53315d46250cc146c9654b73551200060f614411c9640400143e91d097518943004a7e5181dcd630800107e98cc175189430052d65282dd910040018cf8720d6218810004a76538654e32c400125e980c96554e4156e17e0d759c86154c018757520562d814300707a4c415d46250c0189c636107054d210042f259841c9534400143d95e0174189530048fe5580dd1640840143c905497418953005a564c4098641080014d593d88715815400517241515cc61550b94d4964c77550d210062761173cc46055001c56910c9751854300527640415cc605500187a70a144198a300050fa57305d06254c010de9814573181540062eddb84585200800183c756106248010006271d183189100400183c646147250d10004a76508058e32084014d591141731855400527a58545cc615513f83f845d671189540060f614741891004001c95431c8614c5400060f5db83552419400123d952096490410004976578650e328400189d606107054e320061e196801c5544800183c855d1701895300726502831d954440014b99010670d8d540051764c511c1650840149e94d45731855400617614321d9320400155b9454c70545300044f25d8550d4294001c5973142701855400517a4f825d46250c0185d75a0f52188100052764c40dda41080019966160c70552410041fa60425d46150
  | 2 => 0x400186f65209744c52000533e5173188214c00183d626147250e41006276127318860550018b464a0470551210061720d759c86150c010df985db638c8100060f985851c9439040107c966147150d200053664f82dd9100400149d9319071590200051b648509cb6454c0189d84d8c7054d2100527a50805cc615500147591143735942000617e0d755c86150c0149e91d0173181540042f65e841886054c016359114164552320050fe51215d46250c01c3575e1161184200061721573580600840107e98dd97550e500041f6627518b6050c0185f616147150e320041fe5d8518b6050c014d9900ca70d95430048fa6041595540800189c836107654d200051e640415d46250c014bb9460470595320048fe5181dd56508001d315150373551100062d192811c943440010be98dd97454e410053664f621c1615500198d841c87054e320042f660741891004001478905977454d210050fa58535d06054c018b787e11611842000517a57405cc6155001c1e845ce751854300617215735c460550010dd97a0f62181540061760c501c5650800183d841407654c2100627a0d74d086054c0164d950c6628c81000547a57405cc615500113c976154354a410041fa63405d46250c0143c905d57418953006270c9841d9534800129f9360b745901000517a4f825d46150c014cd9290c7258c100060f995841c153c840153b93550705494000527249735d06054c01539941c87054e500060f61574d03630840183c416177650e20004a7a604158d439400183c856107654d2000617a19851c5438c80151e94d45731815400617995831c154884010be98d457418153006274c184dd953c40018cc63a087054d21004ada63645864108001c3575211611842000617a15730c460550014af94604725953000627105831d9544400149e93e09741815300437a63425cc605500189e866107054e320050fa50825d46150c0107c98441751854300627610321d9530400117a98dd570086500060fdd9851c9439040123d95e1943906200050fa58435d46150c0189d7420d62188100060f619841c9539400183e506107654d2000517657805cc61550014b99010775590210062de538758461080018ac64a0870551210054de4d541c54254401c8d74e0d62188100041f66075189100400143d941d676086500068ed0383550605440189c835d272181530049764e81dd3654800107f985d740188100050f65c505d06254c0189d6460f72550100070ea40415d46250c0107f9761461d8143007264c1841d953480016359510a61904200062750183dd954c800189d841cc6248010004a7e4d82dd764440014d9900cb7458c2100627905831d954440014b99010773590210052d64464dda41080010be9814974181530070ba48505d06254c0187b87215601802
  | 3 => 0x100055664c519c02194001535951c87150e4100517644325d46150c01a8f42e15431893100617941831d954440010df985cf521881000627e11735c4605500185f5160f7655321005936485058d539040185c326147650d210045725d8550d319400149e94d4573181540050fe55205d06254c0145d9319470594210070b549215d06254c014d593e0b7644010007075d2839d46250c01c994060c765511000547a57305d06254c0123e981416455021006275d183d086054c0145e9615173181540061720d851d94348401c99900c9741815300555644505cc615500183e866107254e5000437259831c55448001c4d750ca721854300707650505cc6155001b8482205438ca410062d9c684142628c4014b994e07764802000627e1373585200800107d981947150d20006171d58318910040018ce72a0c419825200547a4f525d06054cbd4ac9650b7550d210063618e801c5434800129e980c96450e500061d196811c95344001c57914c575185430061e196801c953440018ad84dcb61581530068e550805486150001555910c975185430060fd09851d943484010df985cf621815400547a50505cc61550014b99010573d964000437660321d9320400185d850c87650c1000617215739c061550014db9360870595410061761763dc143484014d5910ca71d915300457a63305d46250c01c555148573185540043766273184605500123e9814164552320060fd95841c9534400145d970ca75185430052765c419cc6055001d85424c77550d210053564432dd1630800123d9421821941500064e981841c9539400183e646147150f200042fe5d8418b6154c0183d526137654e21006175d583d486150c01c97845cd61184200070b648505d06254c0185d8660c71552500051b648505cf65908014d5910cb7558c200054e650529c0219400189d840c8764c81000517654631c9630400185e855cf4018810005a3e5543189424c001c1e94cc57518543006cc20480552419400185c855cd701855400517654311c9630400145e93105751894300627a19431c5424c0010de98dd9735523200693d4b8454c624c00185e835d451189430061b196821c554480014b9900c974181530050fa57805d06254c0143d94194705942100617215831d9544400164d9518e628c8100061761573cc0615500145c924c5751854300527a4f525d06054c0183c846147650d210041f66075189200400125f9360b74d95100064b61472dc1435080145e90d4573185540043766073189200400183f845d571189430062761073189210400145e95d0173181540051e26175580600857d49f9650b7550e320060f549841d9534800145d970c975185430052764f825d06054c01c9940481731815400533648631c9630400189f306107654d200049764c86086505
  | 4 => 0x550018b974e0162d8553005a564c64986410800151e93d097518543005a36484158d439417b43f96547735524100726a40325d06054c0149e92cc174181530052764c64dda41080018d463a047054d210041f660501d8215400183e866147250e41006275d283d48620400149d9418c7258c100050f648505d06254c0183c845d5721854300437259831c15448401479901d676086502f52e25940dd5434400183d426147650d210052d644325d06054c01c1e950c974181530048f65082596500400185c7560c62480100070e21574580600840189c326137654f1000715644505cc6155001c357510571189430062b61072d856054c0107c966147250d1000725a44325d06054c01c4d750c972185430061de1b7548560084010be980c17418953005a36506398a320400143e950c974181530050f654641c5640800151e93105751894300527a4f525d06254c010bd9810472595430061761573cc364084012ce98d8d628c8100061d5d78158b6050c0149d970ca74181530062760c411c1640840143d9210575189430042f660411d9410800183e845d452185430060f5d2851886050c0129f9460775d8d200041fa60415d46250c0143d9710675189430049765681dd36348001559931d6700865000527249305d06054c0183d9810575189430061714183dd954c840189d866107054e3200527653815cc605500189d4060c76551100062d9c6840ca609440185e855cf30185540050f245425d46250c0107c9848175189430043765e831846055001c993044174181530052765c415cc605500189d74a0f421881000627610321c1630840189f306137654f1000633e4f875886204001c555160c76551100053564f62dc56055001c1e9510573181540061dd94815d132440010be98cc57418953006170c985dd9438400185c636147150d2000497a605058d539040129d93201649042100617614321c563080010de98141731855400437a63425cc615500159994dc47054d300060fe1d54548615000129c96615438c94000533648311c9630400107d989d461d814300617a19531c1524c40189f7660c7055241005a564432591439400107d989d462185430060f61574d006254c01c1d93105751894300617617631c5434800198e626107054e3200467a63425cc61550014759114173d96410064b61072dc5535480185c322197550d51006175d583d4b640400145e95e01731815400716e1573580600840186d75e0961d814300497a605058d5308401c1d9314174189530062bddb84585200800185d5160c76551100052b648419cb63550010df985cf42188100042f662741886054c0183d626107254e500042f65e84d846054c0183e9810575189430041fa60315d46250d7949e969077550d3100437660631c1544840125f9360b75594
  | 5 => 0xd2000617215735c8605500113e98d017518543007255cc419c4605500145e92cc575185430041fe6176dd4219400189f606107054e32007135d783588620400149d940c07258c100070b648415d46250c0189e845cf311815400517241755cc615500183f75e1161480200051e640651c1650840145c925cd7518543007075d6849cc6155001c369114174189530049764c81596500800183c506107654d20005a36503098a320400185d98141731855400713648505cc615500151e9314174189530062798d841c9538400149e93e0974189530051765431dda32040014ad9210672d954300497e5580dd36348401c8d7420d621881000437660321c16550c0183c855d1711815300527a4c505d06254c0183c855d270189530052da6174584610800113d9421d530865000467a63315d06254c014b594a037648421006a5cc78550c615080185d7520d621881000617a1d53189514c00189c835d17118953006175ce851846050c0159993dc87055140006271db8550d424c40185d851cc62480100055664f72dc154940014ad9210773590100070b54a841d9534800185c835d570189430055664c711c154940010bf985d361181530051e65681dd9200800143c915d1751894300723a48415cc605500129d93a0375d9121004a765280dd763484010dd980c871595430063324f8758862040014ad9210775590100060f61764dc1434840123e9810565552325d517a5a50dd1534c001c2d42a147650d21006d22088054e329400185c6560c715512000627a19431c93150001599900c9741815300707a57405cc60550010bd981d062484100070be49425d46250c0189d6060c70552410061720d755c86150c01c1e855d273181540042fe6174d44620400183f626107254e500050fa57805d06054c0187b95e1d601802100517a4c815d46250c0187895e1d601802100633e1f8358862040014b59114174189530042f660641c953440014b8905d7644c910007154c6851d94348401c5791545731855400617dd783485600840147995a0b764401000527a53815cc60550014d9900ca70d915300517654768c932040014789059773551210051b64850dd1650400113e98d4574181530066560c711c1549040187b87e1560180210053364e80dd92108401c95910c974181530051765c509cc615500189d84d8f7154d200054d644505d06254c014b591108715902000627d0183dd954c800183d866147250e4100627d9183dc9544400183e855d0421815300627191831c154484bb4ac9650b73551210060f981841c953940c3474965477454d100051d65780dd92108401c4e92141731855400527a4c805d06254c0185e855cf30188100050f65c509d06254c014759114174d96310061e9c2850ca619000189e6460c71552200053664f62dc161
  | 6 => 0x204001c1d95105731815443e17e15739c06154cbb4b89650373551100055564f721c5545440189d306107654d2000627a1173cc4620400107f985d7301881000517e4d215d46150c0185f6560c71551200060f5d6841886154c018ce72a0c50986420060f5d684cc4620400189e326107654d200043766073189210400189f74e0d624401000636ddb83589100400143e94cc575189430060fa1574d006254c0183c855d172181530051d644509c7635500143d94e0575189430061be1b75485600840189f766107054e3200437a63525cc61550014cc9258f7550d104c627e11739c46050c0185d316147650d210052b65381dd920080014ad9210573d96420058d65464986410800185e8660c71552500062760c411d9410800183d9814174189530042f660411c16550c0152d92141741895300517e55105cc615500185d851cc62484100050fa43525d06254c0123f9460773d952000617a60325d46150c01c9930a107654d2000517a4f425d46150c0149d9310071590200059664032595539040145e9510573181540041f660651c9434400183c855d160180210062721173584610800143e940c975185430060f5d98550e41940010bc966107054d210060fd89851c943904010de9810173185540060f5d4845846108001c2e92105751894300565644325d06054c0185d866147150e320075254930dd1534800189d9810573181540060f211759c46250c014ad92141741895300527a58535d06254c015999010573181540065561471dc1434c40149d931da41504200070b509851d9434840143d951937690420006271d1831892104001c8d9210573181540042f660641c153484010be98cc5741815300527e51105cc605500189d980c9741815300617d45831d9544400145d9518f768c8102dd3625930dd1534800107e980c9751854300627211739c4605500185d8314076550210048f65282dcf654400189f835d172181535dd0fa5a50dcd545000146d95e037648421004a76508654e320400185e636147250f1000527a53815cc6155001c55316147650d210054b648415d46250c0107e98cc1751854300707650325d46150c0149c91501731815400617d9583dc9544400183d85d907250d100042fa63515d06254c014b4915937550d200062760e741846054c0183f426177650e200060f211755c46250c014ac9259774485300054e650759c0219400183c506137654e210042fa60505d06254c0183d75613511894300547a54325d06054c0195a6060c71552500060fd4984dd9538840183d851d0624841000627a60415cc6055001a3554205421815100627619831c154904014b591d0c715902030d1b25952dd153480014cd9218f768c81000533a5e6398932040014cc9258f7454d100052e640415d7648c00183f526107654
  | 7 => 0x54000ac0011b0000f0002f010020580f0258f00c02050990086e05c00164040ac000040d00001014050001f0e4020000a0001c0006d1a84f0000702c0a000080184200403018760441502c30014014300d000010041f0383a039330080001c05228000a943a40050040fbfc01000000040006800004c5018021b8060100000c0f128000d4041800d01c000001c024005900a07803004050040000421004030000203cd210805000000000105c0000c0501c0001c030908a000000e000000000002a0f01301000908070249901c0400e51c240012401004020080205800004ba19c0001c0a0485c000100001302c11000010001a05400014000240602045450ab00005024010940300c070000401c020000400d1d03c0027c2114039000000000600c0302c0101c020180a0040015800010320100200c08004063f8150240000c0800c00001031ac41050610040100007000185f4000000e0201905c0004c1e02c1b0182b15006000030600000000000010700506c8700001208002900001c0023c01020000004b020020100003a080000506c1d0f4111ad8964c010180200004000050d455038085cc001000e040040240500001004184041f0140a30c0100803174f452008000000000f06006098010140145e9610d75189430060f905851d9434840183f766107254e500048f65682dcf644400185d76e11538ca500050fa53315d46150c0189d76615438ca410051b64850dcd650400183c845d570185430062710583dd954c800183c416147650d210052d261745846108001c1e855ce74181530060fd9584dc5534800189d7460f42d94100061720d755c46250c0189d76e15438ca4100535644325d7648c40185f7660c715525000617cc5851d9434840185d83140760855000617585831c55494001a3751e0d541854000517a54815cc605500123d95219439042000617a0d75d486150c01c1e95cc17418153006178c9851d9434840129d93e1954907200050fa57305d06054c01c99901057318154007235d0329c86054c0183e855d340188100051d64450dd1650800183f75e112158021007075d6839d06254c01c1e9314174189532e53625930dd54348001c1e940c975185430060f59584dc553080014d793608715954000696cc38454c60548014cc985cd621881000533648415cc605500143d9414a76086500072350c621c5424c0016399010565552320042fe6174cc46
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x7408610002940a9400100040000404103162400000009890a18080000000112041831c0830e12d40003814414c5851d94348401c0c28280c18ecaa22000c0e66190105751894300691324c8082b98c0aa002855a1141831d9544400141cd0082c28eca1a4200a0b688506137654e210068332ac8082b98c0aa003c1151501831d95444001c0c28260c20eca9a4000c16661900c9751854300612b30c8864ba0c0a980341594644325d46150c01a0cc9b2020aea3128600d1164991141731855400682b2ac8864ba0c0a980380c83509851d9434840142ad08a0c1eecaa64200f0254930a107654d2000513340193083b2a69000309998640415cc6055001a48c8b20192e8302a6009612a5424c77550d210051334020b063b2a88800304d98648505cc6155001c0a422a2c18ecaa22000e055444160c76551100050b3401930a3b2869080302d98648505d06254c01c06a9064c20eca9a4000e062154060c765511000512942a03063b2a888003c05424c5851d94348401a0ccab20192e8302a600a266804160f765532000701a841930a3b2869080380c83549841d9534800142c502a2c18ecaa22000c26661900c9741815300683328c8064ba8c2a180282da2141841d95348001a0ac9b22282e8312a600a0d285426147650d21004a6152a8a81b9aa88800342592644505d06254c012a454aa4986e8a9a4000c1566191141731855400685324c8082ba8c4a180302d98648415d46250c0142651262c28eca1a4200c0d66191141741895300505b4420b0a3b28690802855a10c9851d94348401a06cab2420ae6302a800a15684326177650e10007822a2a05063b2a88800340d93648505d06254c0141ad08a0c20eca9a4000c15661910c9751854300681b26c9082ba8c4a1803818854c1841d95348001a28c8b20192ea30a8600a25684326107654d2000682b28c88a0b98c2aa00340d94648505cc6155001c0a42262c28eca1a4200c23661921057318154007812a4983083b2a690002838a0549841d95348001446d1082c18ecaa22000a0b688416177650e2000509b44283063b2a888003c05424c6851d9434840144651260c20eca9a4000a26680326137654f10
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd00050680000b4a00000021800004c10ba54540a0c7655110005809b21414060c7655110005811b0105316147650d21004c04ba509316147650d2100680942680326147650d21004c08ba549306107654d20006804a2105316147650d21006811516804160c765511000680552684326107654d20005808b0548326107654d20006810a11414060c7655110005811b1141306107654d20006805a25444160c7655110005810b05444160c765511000680542684326147650d21004c08ba54930a107654d20004c04ba50931a147650d21005804b1508326147650d21005811b11414060c7655110005809b2141306107654d20005805b2105316147650d21004c10ba5454060c765511000680952680326107654d20006808a2141306107654d20
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1000023000220172ca2105316147650d2100540060a84d0064c28eca1a4200a800c0549a10c9841d95348001102396508a0a03063b2a8880032006c8a11414060c7655110006400d1160a8882c18ecaa220008809cb288504c1841d95348001900144d88a0983083b2a690003200289b0105316147650d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4c
  | 2 => 0x4d
  | 3 => 0x4e
  | 4 => 0x8c
  | 5 => 0x8d
  | 6 => 0x8e
  | 7 => 0x12cd
  | 8 => 0x12ce
  | 9 => 0x130c
  | 10 => 0x130e
  | 11 => 0x134c
  | 12 => 0x134d
  | 13 => 0x20c
  | 14 => 0x20d
  | 15 => 0x20e
  | 16 => 0x144d
  | 17 => 0x144e
  | 18 => 0x148c
  | 19 => 0x148e
  | 20 => 0x14cc
  | 21 => 0x14cd
  | 22 => 0x15cd
  | 23 => 0x15ce
  | 24 => 0x160c
  | 25 => 0x160e
  | 26 => 0x164c
  | 27 => 0x164d
  | 28 => 0xe8e
  | 29 => 0xecd
  | 30 => 0x104c
  | 31 => 0x131254
  | 32 => 0x131256
  | 33 => 0x14d394
  | 34 => 0x14d395
  | 35 => 0x12d295
  | 36 => 0x12d296
  | 37 => 0x165514
  | 38 => 0x165515
  | 39 => 0xe89d6
  | 40 => 0xec9d5
  | 41 => 0x15d2d5
  | 42 => 0x15d2d6
  | 43 => 0x10c
  | 44 => 0x14c
  | 45 => 0xe8a16
  | 46 => 0x104a14
  | 47 => 0x149314
  | 48 => 0x149316
  | 49 => 0xcd
  | 50 => 0x14d
  | 51 => 0x14d354
  | 52 => 0x14d355
  | 53 => 0x165354
  | 54 => 0x165355
  | 55 => 0xed355
  | 56 => 0xce
  | 57 => 0x105354
  | 58 => 0x10e
  | 59 => 0x145415
  | 60 => 0x145416
  | 61 => 0x161554
  | 62 => 0x161556
  | 63 => 0xe8b56
  | 64 => 0xecb55
  | 65 => 0x15d455
  | 66 => 0x15d456
  | 67 => 0x28c
  | 68 => 0x2cc
  | 69 => 0x161494
  | 70 => 0x161496
  | 71 => 0xe9496
  | 72 => 0x24d
  | 73 => 0x105494
  | 74 => 0x2cd
  | 75 => 0xecbd5
  | 76 => 0x104bd4
  | 77 => 0x24e
  | 78 => 0x28e
  | 79 => 0xe95d6
  | 80 => 0xed5d5
  | 81 => 0x40c
  | 82 => 0x44c
  | 83 => 0xe8d16
  | 84 => 0x104d14
  | 85 => 0x3cd
  | 86 => 0x44d
  | 87 => 0xecd55
  | 88 => 0x104d54
  | 89 => 0x3ce
  | 90 => 0x40e
  | 91 => 0x1a8c
  | 92 => 0x194c
  | 93 => 0x1a4d
  | 94 => 0x17cd
  | 95 => 0x74c
  | 96 => 0x18ce
  | 97 => 0x178e
  | 98 => 0x8056
  | 99 => 0x20055
  | 100 => 0x58e
  | 101 => 0x5cd
  | 102 => 0x20094
  | 103 => 0x4096
  | 104 => 0x8214
  | 105 => 0x9614
  | 106 => 0x17c9d5
  | 107 => 0x1789d6
  | 108 => 0x9d796
  | 109 => 0x131494
  | 110 => 0x148114
  | 111 => 0x52d6
  | 112 => 0x1394d4
  | 113 => 0x12d5d5
  | 114 => 0x1292d5
  | 115 => 0xa1054
  | 116 => 0x4215
  | 117 => 0x5455
  | 118 => 0x194a14
  | 119 => 0x18ca16
  | 120 => 0xa18d6
  | 121 => 0x125314
  | 122 => 0x15c0d5
  | 123 => 0x9316
  | 124 => 0x151655
  | 125 => 0x9ced5
  | 126 => 0x1342d4
  | 127 => 0x148116
  | 128 => 0x1342d5
  | 129 => 0x15c0d6
  | 130 => 0x134454
  | 131 => 0x134455
  | 132 => 0x135a55
  | 133 => 0x135a94
  | 134 => 0x15354
  | 135 => 0x2d354
  | 136 => 0x45354
  | 137 => 0x1a9354
  | 138 => 0x15355
  | 139 => 0x2d355
  | 140 => 0x45355
  | 141 => 0x1a5355
  | 142 => 0x21654
  | 143 => 0x17cb55
  | 144 => 0xb57d5
  | 145 => 0x178b56
  | 146 => 0x1455d6
  | 147 => 0x141456
  | 148 => 0xbd054
  | 149 => 0x15c255
  | 150 => 0x148414
  | 151 => 0x148416
  | 152 => 0x11494
  | 153 => 0x29494
  | 154 => 0x41494
  | 155 => 0x195494
  | 156 => 0x1498d6
  | 157 => 0x11496
  | 158 => 0x29496
  | 159 => 0x41496
  | 160 => 0x18d496
  | 161 => 0x1a8bd4
  | 162 => 0x1a4bd5
  | 163 => 0xbda55
  | 164 => 0x15c256
  | 165 => 0x214d5
  | 166 => 0x155616
  | 167 => 0xb4e96
  | 168 => 0xd5d5
  | 169 => 0x255d5
  | 170 => 0x3d5d5
  | 171 => 0x17d5d5
  | 172 => 0xd5d6
  | 173 => 0x255d6
  | 174 => 0x3d5d6
  | 175 => 0x1795d6
  | 176 => 0x194d14
  | 177 => 0xd1954
  | 178 => 0x18cd16
  | 179 => 0xd4ed5
  | 180 => 0x1a8d54
  | 181 => 0xd5a94
  | 182 => 0x1a4d55
  | 183 => 0xd0e96
  | 184 => 0x1a57d5
  | 185 => 0x1a9954
  | 186 => 0x1a8154
  | 187 => 0x1a4155
  | 188 => 0x194294
  | 189 => 0x1a59d5
  | 190 => 0x195894
  | 191 => 0x1a9a14
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 33
  | 8 => 1128
  | 7 => 5674
  | 6 => 4464
  | 5 => 867
  | 4 => 75
  | 3 => 24
  | 2 => 9
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
  | 9 => 2*((h/18+packedAt gbK9 (858+(h % 18)*6) 6) % 33)
  | 8 => 2*((h/390+packedAt gbK8 (41736+(h % 390)*11) 11) % 1128)
  | 7 => 2*((h/1891+packedAt gbK7 (272352+(h % 1891)*13) 13) % 5674)
  | 6 => 2*((h/1544+packedAt gbK6 (263376+(h % 1544)*13) 13) % 4464)
  | 5 => 2*((h/373+packedAt gbK5 (60690+(h % 373)*10) 10) % 867)
  | 4 => 2*((h/46+packedAt gbK4 (6075+(h % 46)*7) 7) % 75)
  | 3 => 2*((h/22+packedAt gbK3 (2208+(h % 22)*5) 5) % 24)
  | 2 => 2*((h/10+packedAt gbK2 (927+(h % 10)*4) 4) % 9)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe1f03e07c3fe00f87803fc34c71fc87c33f
  | 1 => 0x7803e003ffffc1fffff8003fccb24e60f8fc3f
  | 2 => 0x8003fffc007ffe000fffffc1f0c38f871f0fc7
  | 3 => 0x3ffffff8000000ffffffe3f03f007e00ff8
  | 4 => 0x3fffffffffffff00000003ffc0007fff000
  | 5 => 0xfffc000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x887a0721642c132125848292410410ac83c31b
  | 1 => 0x50886000a8944048eac8052484124660285c2d
  | 2 => 0x110a944005aa4024311298110c08b811d0546
  | 3 => 0x422352aadd0011048c6656382f037006e00ab0
  | 4 => 0x4439cf316633997000418103bec0007d6a000
  | 5 => 0x678000c018022018004060203efbed50000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 5, 0, gbRaw),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 6, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 5, 0, gbRaw),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 5, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 5, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 5, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 5, 0, gbRaw),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 5, 0, gbRaw),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 4, 0, gbRaw),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 5, 0, gbRaw),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 5, 0, gbRaw),(0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000, 4, 0, gbRaw),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 5, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfeeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36234
namespace PEqualNP.Outside.L_meta_36234
open PEqualNP.Outside.L_meta_36234.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_2_0 : Interval s3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 5 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 414 := (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 (concat bs3_4_288 bs3_4_384)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 616 := (concat (concat bs3_5_0 (concat bs3_5_96 bs3_5_192)) (concat (concat bs3_5_288 bs3_5_384) (concat bs3_5_480 bs3_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 414 := (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384)))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 616 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bq1_2_0 : Interval q1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq1_2 : Interval q1Atlas 2 0 3 := bq1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_3_0 : Interval q1Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq1_3 : Interval q1Atlas 3 0 14 := bq1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_4_0 : Interval q1Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allq1_4 : Interval q1Atlas 4 0 13 := bq1_4_0
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
theorem bq3_2_0 : Interval q3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq3_2 : Interval q3Atlas 2 0 3 := bq3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_3_0 : Interval q3Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq3_3 : Interval q3Atlas 3 0 14 := bq3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_0 : Interval q3Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allq3_4 : Interval q3Atlas 4 0 13 := bq3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_0 : Interval q3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq3_5 : Interval q3Atlas 5 0 1 := bq3_5_0
theorem allq3 : ∀ k ≤ 5, ∀ i < count q3Atlas k, checkRow q3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq3_2 i (by omega) hi
  · exact allq3_3 i (by omega) hi
  · exact allq3_4 i (by omega) hi
  · exact allq3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_2_0 : Interval q5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq5_2 : Interval q5Atlas 2 0 3 := bq5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_3_0 : Interval q5Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq5_3 : Interval q5Atlas 3 0 14 := bq5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 13 := bq5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_5_0 : Interval q5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_5 : Interval q5Atlas 5 0 1 := bq5_5_0
theorem allq5 : ∀ k ≤ 5, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_2 i (by omega) hi
  · exact allq5_3 i (by omega) hi
  · exact allq5_4 i (by omega) hi
  · exact allq5_5 i (by omega) hi
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
theorem bq9_4_0 : Interval q9Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_4 : Interval q9Atlas 4 0 1 := bq9_4_0
theorem allq9 : ∀ k ≤ 4, ∀ i < count q9Atlas k, checkRow q9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq9_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_4_0 : Interval q11Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_4 : Interval q11Atlas 4 0 1 := bq11_4_0
theorem allq11 : ∀ k ≤ 4, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bq23_2_0 : Interval q23Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq23_2 : Interval q23Atlas 2 0 3 := bq23_2_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 9 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 24 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 75 := block_range (n:=75) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 75 := bgb_4_0
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
theorem bgb_5_864 : Interval gbAtlas 5 864 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 867 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864))))
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
theorem bgb_6_4416 : Interval gbAtlas 6 4416 48 := block_range (n:=48) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4464 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248)) (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536))) (concat (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)) (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112))))) (concat (concat (concat (concat bgb_6_2208 (concat bgb_6_2304 bgb_6_2400)) (concat bgb_6_2496 (concat bgb_6_2592 bgb_6_2688))) (concat (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976)) (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264)))) (concat (concat (concat bgb_6_3360 (concat bgb_6_3456 bgb_6_3552)) (concat bgb_6_3648 (concat bgb_6_3744 bgb_6_3840))) (concat (concat bgb_6_3936 (concat bgb_6_4032 bgb_6_4128)) (concat bgb_6_4224 (concat bgb_6_4320 bgb_6_4416))))))
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
theorem bgb_7_5664 : Interval gbAtlas 7 5664 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 5674 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat (concat bgb_7_672 bgb_7_768) (concat bgb_7_864 bgb_7_960)) (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 bgb_7_1344)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)) (concat (concat bgb_7_1728 bgb_7_1824) (concat bgb_7_1920 bgb_7_2016))) (concat (concat (concat bgb_7_2112 bgb_7_2208) (concat bgb_7_2304 bgb_7_2400)) (concat (concat bgb_7_2496 bgb_7_2592) (concat bgb_7_2688 bgb_7_2784))))) (concat (concat (concat (concat bgb_7_2880 (concat bgb_7_2976 bgb_7_3072)) (concat (concat bgb_7_3168 bgb_7_3264) (concat bgb_7_3360 bgb_7_3456))) (concat (concat (concat bgb_7_3552 bgb_7_3648) (concat bgb_7_3744 bgb_7_3840)) (concat (concat bgb_7_3936 bgb_7_4032) (concat bgb_7_4128 bgb_7_4224)))) (concat (concat (concat bgb_7_4320 (concat bgb_7_4416 bgb_7_4512)) (concat (concat bgb_7_4608 bgb_7_4704) (concat bgb_7_4800 bgb_7_4896))) (concat (concat (concat bgb_7_4992 bgb_7_5088) (concat bgb_7_5184 bgb_7_5280)) (concat (concat bgb_7_5376 bgb_7_5472) (concat bgb_7_5568 bgb_7_5664))))))
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
theorem bgb_8_1056 : Interval gbAtlas 8 1056 72 := block_range (n:=72) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1128 := (concat (concat (concat bgb_8_0 (concat bgb_8_96 bgb_8_192)) (concat bgb_8_288 (concat bgb_8_384 bgb_8_480))) (concat (concat bgb_8_576 (concat bgb_8_672 bgb_8_768)) (concat bgb_8_864 (concat bgb_8_960 bgb_8_1056))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 33 := block_range (n:=33) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 33 := bgb_9_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq1 (cert : Complete q1Atlas) : Lower true (roots q1Atlas) (target q1Atlas) 6 := by
  have ready : Ready q1Atlas (asRow q1Pos) (asRow q1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq3 (cert : Complete q3Atlas) : Lower true (roots q3Atlas) (target q3Atlas) 6 := by
  have ready : Ready q3Atlas (asRow q3Pos) (asRow q3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 0, 16),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 6 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 0, 8),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 0, 4),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 5 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 0, 16),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 4 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 0, 16)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 4 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 5 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 0, 8),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 5 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 0, 8),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880feeefaeafcecf880
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq1 : Complete q1Atlas) (certq3 : Complete q3Atlas) (certq5 : Complete q5Atlas) (certq7 : Complete q7Atlas) (certq9 : Complete q9Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : Sig) 6 :=
    slice_correct (ms:=fixRows 0 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq1 certq1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : Sig) 6 :=
    slice_correct (ms:=fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq3 certq3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 8 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 8 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa : Sig) 5 :=
    slice_correct (ms:=fixRows 8 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 16 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 32 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : Sig) 5 :=
    slice_correct (ms:=fixRows 8 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000 : Sig) 4 :=
    slice_correct (ms:=fixRows 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : Sig) 5 :=
    slice_correct (ms:=fixRows 16 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc : Sig) 5 :=
    slice_correct (ms:=fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4243388544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36234.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.and,[2,6]⟩,⟨.and,[0,5]⟩,⟨.or,[1,7]⟩,⟨.and,[1,7]⟩,⟨.or,[8,9]⟩,⟨.or,[0,2]⟩,⟨.or,[5,10]⟩,⟨.or,[3,13]⟩,⟨.and,[12,14]⟩,⟨.or,[4,15]⟩,⟨.and,[11,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4243388544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4243388544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36234

open PEqualNP.Outside.L_meta_36234 in
theorem PEqualNP.Outside.L_meta_36234 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4243388544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4243388544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq1 allq3 allq5 allq7 allq9 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allgb)
