import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36412.Model
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


end PEqualNP.Outside.L_meta_36412.Model

namespace PEqualNP.Outside.L_meta_36412
open PEqualNP.Outside.L_meta_36412.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 48,swapRows 33]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_36412

namespace PEqualNP.Outside.L_meta_36412
open PEqualNP.Outside.L_meta_36412.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x60003a228d9400000cf00798b01b8e80405849d709462915d01956a21241a92b7a024c70800e080041040210223ff41fe41fd41fc41fe21fd21fc21ff40fe40fd40fc40fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020ffaa6217f54c43fca9885f95310feaa6217d54c43f8a9885f15310ffa9e217f53c43fca7885f94f10fea9e217d53c43f8a7885f14f10ffa1e21fe43c43fa87887f10f10ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff19621ff41c43fc83887f50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887d88710fe90e21f521c43f843887fd0310ff20621fd40c43f881887fcc310ff18621fd30c43f861887fc8310ff10621fd20c43f841887fd5210bfaa421fe54842fca9087f55210beaa421fc54842f8a9087fd4e10bfa9c21fe53842fca7087f54e10bea9c21fc53842f8a7087fd0e10ff21c21fd43843f887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff194217d51843fe83087f90610fea0c21fc41843fe63087f8c610fe98c21fc31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fa40843fa81087e50210fe20421ff30843fc61087e8c210fe98421f930843f861087fc8210ff10421fa20843fa41087e48210fe10421ff10843ee21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ffa1a21fe43443fa86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887fd0510ff20a21fd41443f882887fcc510ff18a21fd31443f862887fc8510ff10a21f621443fa42887d48510fe10a21ff40443fc80887e90110fea0221f940443f880887fcc110ff18221fa30443fa60887e4c110fe18221ff20443fc40887e88110fe90221f920443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe438c3fa87187750e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff218c3fc43187f48630fe10c617e508c3fe81187ed0230ff20461fd408c3f881187e10230ff98461fb308c3fea8985fd5130ff2a2617e544c3faa8985f55130fe2a2617c544c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff10a61fd214c3f842987fd0130fda0261fe404c3fa80987f10130fc20261fe304c3bc60987fd5030bfaa061fe540c2fca8187f55030beaa061fc540c2f8a8187fd4430ff288617e510c3faa2185f54430fe28861ff410c3fc82187f50430fe20861fe210c3fa42187f08430bf28061ff400c3fc80187e90030fea0061f9400c3f880187f8c030fd18061fd300c3f26018764c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e41fe53c82fca7907f54f20bea9e41fc53c83fe87907f90f20fea1e41fc43c83fe85907f90b20fea1641fc42c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff18e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320ff20641fd40c83f881907fcc320ff18641fd30c83f861907fd5220bfaa441fe54882fca9107f55220beaa441fc54882f8a9107fd4e20ff29c417e53883faa7105f54e20fe29c41ff43883fc87107f50e20fe21c417d52883fe85107f90a20fea1441fc42883fea3107f94620bf28c41fd51882faa3107f14620ffa0c41fe41883fa83107f10620ff98c41fe31883fe43107f88620fe90c41fc21882fca1107fd0220ff20441fa40883fa81107e50220fe20441ff30883fc61107e8c220fe98441f930883f861107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20ff29a41fd53483f8a6905f14d20ffa1a41fe43483fa86907f10d20ffa1241fe42483fa84907f10920ffa8a417f51483fca2907f54520fe28a417c51483fe82907f90520fea0a41fc41483fe62907f8c520fe98a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241fa40483fa80907e50120fe20241ff30483fc60907e8c120fe98241f930483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8106f950209f2a041fd54082faa8106f550209eaa041fc54082f8a8107fd4c20ff298417e53083bca6105794c20fea98417d53083baa6105754c20fe29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fea2107f94420bf28841f651082eca2107f54420bea8841f551082eaa2107f14420ffa0841fe41083fa82107f10420ff98
  | 2 => 0x7fca420df94841f7290836e52107faa420df54841f6a90836d52107f8a420ffd0841ff21083fd42107f88420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107f4a020de94041fea80837d50107f2a020de54041fe28083ff54886fea910ff95221bf2a443fd54886faa910ff15221be2a443ff53887fca710df94e21fea9c437d53887f8a710df54a21ffa1443fe42887fa8510ff10a21bf28c43ff41887fc8310fd90621fea0c43f541887f88310ffc8621fb90c43ff50887fca110df94221fea84437d50887f8a110ffd5121bfaa243fe54486fca890ff55121beaa243fc54486f8a890ffd0521ff20a43f641487fa8290fd50521fe20a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043be540867ca810ff55021beaa043bd540867aa810ff15021be2a0437e51087fe8210ff90421fea0843fc41087fc4210fd88421fe90843f521087ca4210ffd4021ff280437e50087f4a010de94021fea80437d50087f2a010de54021fe28043ff53d03fca7a05f94f40ef29e815e53d03faa7a05f54f40eea9e815d53d03f8a7a07fd0f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a06fd0740ff20e81fd41d037a83a07f10740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40ef29c815e53903faa7205f54e40eea9c815d53903f8a7207fd0e40dfa1c81fe43903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481fe42903fa85207f10a40ffa8c81fe51902fca3207f54640bea8c81fc51903fe83207f90640fea0c81fc41903fe43207f88640fe90c81fc21902fca1207fd0240dfa0481fb40903fea6a05fd4d40ff29a81fd53503f8a6a05f14d40ffa1a81fe435037c86a07f50d40ffa92817f52503fca4a07f54940fe292817c52503fe84a06fd0940ff21281fd425037a84a07f10940ffa8a817f51503fca2a07f54540fe28a817c51503fe82a06fd0540ff20a81fd415037a82a07f10540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff53103fca6205f94c40fea98817d53103f8a6207fd0c40dfa1881fe43103fa86206f50c40fe21881ff52103fca4205f94840fea90817d52103f8a4207fd0840ff21081fd42103f884207fd4440ff288817e51103faa2205f54440fe28881ff41103fc82207f50440fe20881ff21103fc42207f48440fe108817e50103fe80206fd0040ff20081fa40103fa80206f50040fca0081b940103fea9185fd5230ff2a4617e548c37ca9184f95230feaa4617d548c37aa9184f55230fe2a4617c548c2faa7187fd0e30ff21c61d
  | 3 => 0x4252b92e041000886a0c0046ad6c000000008e4df9ad7a43c9a08004fa00000000706000000000000005414000000000000000000668ce28b0001400050a000ff00048eed895c220d200007300f509dc7248ce09164a32b28004b6000004a5b78fbaed0f30015a22106cde5378004a49a40659a60293000000000919d49211f700000228dc6d50000000f62b14d80000000208400800000000000000040a80b0100220a01a8040040d01280c0060080081c00e0000300101200c1500800811c0a00100003c0c0000040080000204e0140480a0b00dc04801034000028080060000e00a000000040110040380300101e0440401e0580080401801600801001000008018130000180000000a0980a80000c00000009058008000040540880084303a0100d02e00e0040000200600c0080900001400010008008008010000280d000004000168040060240e85f0040040200004a004030120000280300c0180100080100001400800000004100060000640302700600c000010440080180001200c0380102801c008020180c806008002040088110200040600200c0300100f0160200a80200a00406805004020010000000080281202e02801003006008000060020100600a0000000380100c0a8018030f202c088020260600500200200408800024004048030020000001800c0880000e0a0018070060000180280400e0000200401e02807807006008008000320180280504a00805820000010020020020240580305202c0f8000240440000204a0201480001a00c258020080241880000203c0000002c0040002a0080000100000001802800026180010000000000100001000804002018018138010000000f80100c0280000e000008010030060080180d000030008000040000100302000c0000700000c0000601e0100100100a000000110280500d801030000008020020001780b0160000b8000100100580000c01000007002028098060040000082b01801400000002050008090000200184a01003800000004003fea7a0ff94f41bf29e83fd53d06faa7a0ff14f41ffa9683fe52d06fca5a0ff54b41bea9683fc52d07fe85a0efd0b41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4e41ff29c837e53907faa720df54e41fe29c83ff52907fca520df94a41fea94837d52907f8a520ffd0a41ff214837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4d41bfa9a83fe53507faa6a0ff14d41be29a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941dfa1283fe42507fa84a0ef50941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4c41ff298837e53107bca620d794c41fea98837d53107baa620d754c41fe29883ff521
  | 4 => 0x71282001d93dc28447f158a01388603c7343f080b909a6a440e00025b000a4ee08007a8ac3816df000af69da13288f0c0000d0f400000222000000002924e499d13b1f00000051fca000d9c001d1459bd55a505fac920002a32c673b444986d8001322ad00050243a9871038612e92800e8c00963ecc07ce32fa3ecac905b1763fa91b6c0024861108d288220630651b11217d3d51042a47c71039b7d359678be87882abe024034aa000008633354d3a99290001c9bb416a0bc0029c3770e80b1770e8000003b900088a0cb44bcf264bdb57208f09999e3303a5432bba1f5d8927870a6a6e58f262a1e6792f28400c3a7be90974d4c9224000d3001869bc0aecf63587700086c7a31d0001bc1e800543110e73810004f83735eac48499304a28d001d8834000c9ecabbc250c7af7908b16f4592c000000000002916494c000000000002a0000007a96ea2de31f84000d90bca041b8da78c685a7a093ba980b888d694d8405139677b6750815920dd97601bdb46640020e800bcf6080057af02a1de220f0010bb646a2ee0322800b72d8f2af867f80f2eef44d62ec4d91624cad46405a10c61d82db2673c71810c7232d3042fa25c8dbd005823370ad79b900ac9a1df2bc4942f9efb2ae14d4ed2b5e584000c429316284200104ab0d0bd62c76acce0c523f73c6b9849b6000001a18002b20000000068c594000001f46cd29ed1646699228530870c1430a6cf648c0d966ba19641b4fd1810013d1e9eda6dfe015c78a41cd01c021480c028000b932f5c0006e8f059b07ad6e5e53100b800df090729e37dc959c6a6b4000718000cf5ac1fa438001f03800000060ef643e4a0b31c600051c7b4c365caa6529258b3a3aa82e2bcc21d7a0151705e2e1cec9743481340c0f616371170bb5000378b98f13b55b87f0471ce000aea0d15e38a602a74c100156172e7a7209fc9f04fb8e93b604beac1759fdbc04805de0b800a8108ac042773deeb0529a8a076a29ac81de0a58d228001040f045889e43f302d4958002dbb1c1b53c29a04677ce9bc42049b4cf80014caff80ee240481fa6b356640b177285bf5dc0a18004283e665398635001bdbd74680711c25bcca6197034204c24400007707b365a6880ec05cb0000109e94988003b6c3ce1800218278ec29173ed7627b2253e0000010165065cba5d65620001c70e64d000e50e03f68180019e8002a483000000bbc000000491e40007165e7c517c55142908c806c6d0ad8fe000000000003b77b200000226336869e7230bea00000331000e48dcf49678100003690009c4000002a46c5731bd8fd001558006960d700800000000ecd22f9e000003950000017b85de907b03e97509030d16b631701392a971e00f1d15c311b86a6dd8db4f1e019ba3ade0ce4fc8c422257c760bd68a8410f41501224972a9e
  | 5 => 0x281aa8eaf80a7aaf1de04c83601a66181a06ce523000229c71b02cbb2957616ea3bf93d5fe3bbc581010a35c4b0f0c3bd7f6c92525c3ab0c95b8426486823181633d66b20d4c9d4f357204dc6dc797662f604001e44298313f8bda340b40022a14ed108bb5d592d54c480070a4a8001f0622d0e7baaa2b66028900025a250002250c66e1cd12e8005f90fc228b0c21880000000002da879e65589c0f9000228000dd5e3c1cdf0000000c8e10ee5a6910001fd0000000f277800e740036e00000012b4000012d319c5f05e858999d02872400000000e700000008434868ae800000189397476b555af271e39843428c65cc6941204853515001dc2169507e704448b6239a5735e768519e76321839d9d7a3c60c3c09334646161acb000e189e00067cf79570675206a15f94c15f03ab7a5d354a35a3baf1925795dab3529f545ae54acce383120de2c2023dd08000b6d629ee6d6d9e093aa57dbd80016faeb97f0347e71221b1004646ce907f80431e391bd2667b0eb4870ad3983ac6fa3e3e9a0c375856be2dc66c006a4f357e19c2fa5e8f08006f01b317246e75c61479470d1524d83bf22acb4979e90cc200173535f63ed51e23174b48db40f5520019c4288a4000f98a1800b2e3b7da4f800181c9741c8e94eaa22062081bf24e516889b0a22d24140020537a65111e7011c000001987b67acebab919500173bd02a2067cd9ebc1e645785cd8c2584000d3c3a9240bf4e4143060009530b13128a4e486c81ca23021a3980025e8005870f8000005409f40026808f448030004b0e836a6a01bfde88b00000181ad7000384c962f709000000000000016c2d0441000b74003fe8dd9493a000001bb8000009b386315514600e91d6d7cb28060a2af09b85feb197ee9c631cbbd1ae9acb2298a8a4454f895d757ae24d2dab1066182b5669eb1568756811208efcb4c767532540bc501abb014adf87e16db2c06af932c2600007a85d39aa1b192877044fc7c00000081c00088516d720026a7223a400290a56eb80e80074f538002c85f20014a0001080000015a00000000000000000288000002e5c500000061fcca3d000000f6e74462a957e8ab0fe5b040a76253332012fe25ff241c8005b5dd4611ba168bc9d98c10e40ec5e1de2a32752c000000000f32caee6000002166799f85820f800001951d5326000599bcfa6c733980071a642000006563a09bb962a87e8ccfcb296b719d0f28409018308323859c520eb934eece5955193000c262a9a86b0f56790b86d44798c00034dd000052cba836d295a87d1a0f3f44910c460c78926a4db97f4668baffe1c066cdf4b800000d61e433ed8c9b0550e5000401d32e4800000ea21e4a3513c20275d244d1e2d6196000dc5b464866a003
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf400435e53d0010d754f400436e52d0010db54b400427f65900109f596400433e5490010cf55240042de6390010b758e400435e5390010d754e400436e5290010db54a40042f66190010bd586400437a50900109fd95400433e5450010cf551400435e5350010d754d400436e5250010db549400437a50500109fd94400427e65100109f594400427c6510010cf950400433d5410010d794c400435d5310010db948400436d5210010bd98440042f56110010ee500400427d65cc010af99330042bd64cc010cf953300433d54cc010d794f300435d53cc010db94b300436d52cc0109fd96300427d658c010af99230042bd648c010cf952300433d548c010d794e300435d538c010db94a300436d528c010bd98630042f5618c010de942300427f654c010cf951300433d544c010d794d300435d534c010db949300436d524c010de941300427f650c0109f994300427d650c0109f194300433e540c010cf550300435e530c010d754c300436e520c010db54830042f6610c010bd58430043d9300c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200437a50880109fd95200433e5448010cf551200435e5348010d754d200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd59710043b654c4010ed55310043d653c4010f554f100437752c4010f994b100437552c4010f954b100436552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e596100437b5484010ee95210043795484010ee55210043395484010ded4e10043da5384010de54e10043d95384010d654e100437b5284010fa94a10043795284010fa54a10043695284010be586100437a5184010fc946100427f6544010cf951100433d5444010d794d100435d5344010db949100436d5244010bdd95100437765440109dd9510043b65444010ed55110043d65344010f554d10043775244010f994910043755244010f954910043655244010bdd8110043765044010fc88110043f12044010bed95100437b65440109ed95100437b5444010ee95110043795444010ee55110043395444010ded4d10043da5344010de54d10043d95344010d654d100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010fc88510043f12144010
  | 1 => 0x436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf55042042de6310810b758c420435e5310810d754c420436e5210810db54842042f66110810bd58442042fa6010810be580420427f65cc8109f997320427d65cc8109f197320433e54cc810cf553320435e53cc810d754f320436e52cc810db54b320427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320436e528c810db54a320427f654c8109f995320427d654c8109f195320433e544c810cf551320435e534c810d754d320436e524c810db54932042fb604c810be181320427e650c8109f594320427c650c810cf950320433d540c810bd98432042f5610c810be98032042f9600c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410433e54d0410cf553410435e53d0410d754f410436e52d0410db54b410427f65904109f596410433e5490410cf552410435e5390410d754e410436e5290410db54a41042fa6090410be582410427f6550410cf951410433d5450410d794d410435d5350410db949410436d52504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410d794c410435d5310410bb98841042ed6210410db948410436d5210410be98041042f960104109f597310433e54cc410cf553310435e53cc410d754f310436e52cc410db54b310427f658c4109f596310433e548c410cf552310435e538c410d754e310436e528c410db54a31042fa608c410be582310427f654c410cf951310433d544c410d794d310435d534c410db949310436d524c4109fd94310427d650c410af99031042bd640c410cf950310433d540c410d794c310435d530c410bb98831042ed620c410db948310436d520c410be98031042f9600c4109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f596210433e5488410cf552210435e5388410d754e210436e5288410db54a21043765188410be98221042f960884109fd95210433e5448410cf551210435e5348410d754d210436e5248410db549210437651484109fd94210427d6508410af99021042bd6408410cf950210433d5408410b798c21042dd6308410d794c210435d5308410db948210436d5208410f948421042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400433e54d0010cf55340042de63d0010b758
  | 2 => 0x5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109e980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430435e53d0c10d754f43042fa60d0c10be583430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e43042fa6090c10be582430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c430439d4310c10af99352042bd64d4810cf953520433d54d4810b798f52042dd63d4810d794f520435d53d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520435e5394810d754e520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d5494810db152520436f5394810db94e52043ce5394810d394e520436d5394810f354e520434d5394810db14e520436f6494810db992520436d6494810db192520436f6394810db98e520436d6394810db18e520436f4394810db90e520436d4394810db10e520436e6194810db186520436e6094810db182520433e5454810cf551520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810db14d520436f6454810db991520436d6454810db191520436f6354810db98d520436d6354810db18d520436f4354810db90d520436d4354810db10d520436e6154810db185520436e6054810db181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420
  | 3 => 0x110be58d204437b5348110de54d20443eb6248110fad49204437a5248110de14920443e85248110fcd8520442f86148110fc18520443eb2148110fc88520443e92148110fc48520443e121481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420442fa6008110fa48020442fb64c4110be59310442fb63c4110be58f10442fb62c4110be58b10443f221c4110fc48710442f76284110bd58a10443f35084110fc90210443f14084110fc8c210443f13084110fc88210443f12084110b798f54042dd63d5010bb98b54042ed62d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d50109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d62950108f596540433f6395010cf98e540433d6395010cf18e540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cfd95540433f6355010cf98d540433d6355010cf18d540433f6255010cf989540433d6255010cf189540433e6155010cf185540433e6055010cf181540433c1055010af990540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150108f990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427a6015010af99353042bd64d4c10cf953530433d54d4c10bb98b53042ed62d4c109f993530433e64d4c108f993530427d64d4c10cf593530423d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109f983530437a60d4c109f596530433e5494c10cf552530435f5394c109f992530427d6494c109f98a530427d6294c1097596530435f5494c10d7952530439e5494c10c7952530435d5494c10e7552530431d5494c10d7152530435f6494c10d7992530435d6494c10d7192530435f6294c10d798a530435d6294c10d718a530435e6194c10d7186530435e6094c10d7182530433e5454c10cf551530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427f6054c109f581530435f6554c10d7d51530435e5454c10e7951530431e5454c10d7551530439d5454c10c7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e
  | 4 => 0xd99621443775488510dd55221443775388510dd54e21442f56288510dd94a21443745288510fcd8221442f66088510fc182214427c6548510dbd49214436c5248510bed8121442f86048510dd19521442746548510ddd5121443755448510ddd4d21443755348510f9d8921443e75248510dd94921443745248510f914921443645248510f990921443e54248510f98c921443e53248510fcd8121442f46048510fc181214427e6508510af99021442bd6408510b798c21442dd6308510bd98421443e52108510be980214427e65d0110cfd53404433c54d0110b798f40442dd63d0110bd98740442f561d01109f99640442de6390110b758e40442fa6590110de99640442f96490110de95240443785490110f698e40442f96390110f658e40442d96390110de94e40443785390110eed0e40443b94390110be58a404437b5290110de54a40442fa6190110fc88640443f121901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540442f86550110de19540442786550110eed9140443bb5450110de95140443785450110ee15140443385450110bed8d404437a5350110de14d40443ba4350110ee10d40442fb6250110ded4940443795250110eed0940443b94250110fcd8540442f86150110fc18540443bb4150110ee50540443f22150110fc485404427e6510110be98040443b940101109f99730442be64cc110af593304435f53cc110d714f30442f661cc110bd587304427e658c110af99230442bd648c110be996304437a658c110bed9230443ba648c110be59230443b9648c110ae592304437a548c110de15230442f9638c110de94e3044378538c110f690e30443d9438c110be58a304437b528c110de54a30442fa618c110fc88630443f1218c1109fd95304427d654c1109f195304435f534c110d714d30442f7614c110bd18530442f8654c110de1953044278654c110bed9130442f9644c110de9513044378544c110f6d8d30443db534c110de94d3044378534c110f614d3044358534c110f6d0d30443d8434c110bed89304437b524c110de54930443db324c110f64c930443f3614c110be18530443f0614c110f6cc530443d9314c110fc88530443f1214c1109f99430442fa600c110f64c0304427e65c8110dbd4b204436c52c8110bd98720442f561c8110f9487204427e6588110be996204437a6588110bed9220442f96488110ded5220443795488110bed8e20442f96388110ded4e20443795388110be58a204437a5288110de14a20443f36188110be98620443f06188110fc88620443f121881109fd95204427d65481109f195204436f5248110db14920442f76148110bd18520443e52148110be195204437865481109e19520442fb6448110be591204437b5448110de55120442fb6348
  | 5 => 0x534423d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de582534427f6454d109f191534435f6354d109fd89534427c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f58853443796014d109f180534427f65d0d109f997434427d65d0d109f197434433f54d0d10cf15343442fa60d0d10be583434427f6590d109f996434427d6590d109f196434435f5390d10d714e43442fa6090d10be582434427f6550d109f995434427d6550d109f195434433f5450d10cf151434435f5350d10d714d434427f6510d109f994434427d6510d109f194434439d4310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910af99052442bd6414910b798c52442dd6314910db548524427e6414910cf990524423e64149109f590524433d64149108f590524427e6314910d798c524425e63149109f58c524435d63149109758c524436e6214910dd584524427c6114910de580524427c60149109fd97424427e65d09109f597424427c65d0910cf953424433d54d0910be98342442f960d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910bd98642442f56190910be98242442f960909109fd95424427e65509109f595424427c6550910cf951424433d54509109fd94424427e65109109f594424427c6510910cfd50424433c5410910b798c42442dd6310910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910d794f324435d53cc910be98332442f960cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910bd98632442f5618c910be98232442f9608c9109f995324427d654c9109f195324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414427c6550510cfd51414433c5450510bed8141442f860505109f99441442de6310510b758c41442ee6210510bb58841442fa60105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f195314435f534c510d714d31442fb604c510be181314427e650c510af99031442bd640c510bb98831442ed620c510be980314427e65c8510dbd4b214436c52c8510be98321442f960c85109f99621442f66588510d
  | 6 => 0x3da6390210be58e40843d96390210b658e408437a5390210de14e40843bb4390210ee50e40842f96290210ded4a40843795290210be98640843f26190210fc586408433f5450210cf15140842fb6550210ded9540843bb6450210eed51408437a5450210de15140843b85450210ce15140842fb6350210de94d40843785350210ee90d40843b84350210bed89408437b5250210de54940843bb4250210ee50940842f86150210eed0540843b94150210cf950408433d5410210bd98440842f56110210ee50040842be64cc210af593308435f53cc210d714f30842be648c210af592308435e538c210d754e30842f6618c210bd58630842f9658c210de59630842fb648c210ee99230842f9648c210ee59230842b9648c210de9523084378548c210de94e30843da538c210f654e3084378538c210f690e30843d9438c210be58a308437b528c210de54a30842fa618c210fc98630843f1618c210d7d4d308435c534c210bed95308437b654c210bed9130842f9644c210de9513084378544c210f6d8d30843db534c210de94d3084378534c210f614d3084358534c210f6d0d30843d8434c210bed89308437b524c210de54930843db324c210be18530843db314c210f64c5308435e530c210d754c30842f6610c210bd58430843d9300c210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210be59620843796588210bed9220842f96488210ded5220843795488210be58e208437b5388210de54e208437a5288210fa94a20843e95288210de14a20842fa6188210fc98620843f16188210dbd49208436c5248210bed95208437b6548210bed9120842f96448210ded5120843795448210bed8d208437b5348210de54d20843eb6248210fad49208437a5248210de14920843e85248210be18520843eb2148210fa48520842be6408210af59020842de6308210b758c208436e5208210db54820842f66108210bd58420843e92008210bd597108437565c4210ddd4b108437552c4210be597108437965c4210bed9310842f964c4210bed8f10842f963c4210bed8b10842f962c42109f98f544427d63d51109f98b544427d62d5110cfd5254442de6395110b758e544427e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544427d62951109f586544437561951109f58254443796095110cfd91544427f63551109f18d544427f62551109f189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544437960151109f180544427e64d4d109f593534427e62d4d109f58b53442be6494d10af592534435f5394d109f992534433e6494d108f992534427d6494d10cf592
  | 7 => 0x3152109f58c548427e62152109f58854843756115210de98054842be64d4e10af593538427e64d4e10cf993538423e64d4e109f593538433d64d4e108f593538427e62d4e109f58b538437561d4e10de98353842be6494e10af592538435f5394e109f992538433e6494e108f992538427d6494e10cf592538423d6494e109f98a538427d6294e10de982538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cfd53438433c54d0e10d794f438435d53d0e10be98343842f960d0e109fd96438427e6590e109f596438427c6590e10cf952438433d5490e10d7d4e438435c5390e10be98243842f96090e109fd95438427e6550e109f595438427c6550e10cfd51438433c5450e10d7d4d438435c5350e109fd94438427e6510e109f594438427c6510e10cf950438433d5410e10d794c438435d5310e10e750c43842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a10de982528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a10be98342842f960d0a109fd96428427e6590a109f596428427c6590a10be98242842f96090a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a109fd94428427e6510a109f594428427c6510a10b798c42842dd6310a10bd98442842f56110a10be98042842f96010a109f997328427d65cca109f19732842fa60cca10be583328427f658ca109f996328427d658ca109f19632842fa608ca10be582328433e54d0610cf55341842fa60d0610be583418433e5450610cf55141842fb6050610be18141842de6310610b758c41842ee6210610bb58841842f96010610d794f318435d53cc610be98331842f960cc610d794d318435d534c610bed8131842f8604c610af99031842bd640c610bb98831842ed620c610be580318436e52c8610db54b21842fa60c8610be583218436e5248610db54921842fb6048610be18121842be6408610af59021842de6308610b758c21843e52108610be580218433f54d0210cf15340842de63d0210b758f408433e5490210cf55240842de6390210b758e40842f66190210bd58640842f96590210de596408437a5490210ee95240843b95490210de1524084
  | 8 => 0x10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10b798c52c42dd6314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b109fd9642c427e6590b109f59642c427c6590b10db94a42c436d5290b10bd98642c42f56190b109fd9542c427e6550b109f59542c427c6550b10cf95142c433d5450b10db94942c436d5250b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10b798c42c42dd6310b10bd98442c42f56110b10be98042c42f96010b109f99632c427d658cb109f19632c42f6618cb10bd58632c433f54d0710cf15341c433e5490710cf55241c42fa6090710be58241c433f5450710cf15141c433e5410710cf55041c42de6310710b758c41c42ee6210710bb58841c42fa6010710be58041c435f53cc710d714f31c435e538c710d754e31c42fa608c710be58231c435f534c710d714d31c42be640c710af59031c435e530c710d754c31c42ee620c710bb58831c42fa600c710be58031c436f52c8710db14b21c436e5288710db54a21c42fa6088710be58221c43756588710ddd5221c43755488710ddd4e21c43755388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c436f5248710db14921c42f76548710ddd9521c43775448710dd55121c43775348710dd54d21c43e76248710f9d4921c43765248710dd14921c43e45248710d914921c43e64248710f950921c43e63248710bd18121c42be6408710af59021c42de6308710b758c21c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310b798f40c42dd63d0310bd98740c42f561d0310b798e40c42dd6390310cf95140c433d5450310bdd8540c42f46150310ee50040c42be64cc310af59330c435e53cc310d754f30c42f661cc310bd58730c42be648c310af59230c435e534c310d754d30c42f7614c310bd18530c43d9300c310db94b20c436d52c8310bd98720c42f561c8310f948720c436e5248310db54920c42f76148310bd18520c43e52148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f56108310b798f54842dd63d52109f98f548435e63d52109798f548427d63d5210d758f548425d63d52109f98b548427d62d5210dd587548437a60d5210cfd5254842de6395210b758e548427e6395210d798e548425e63952109f58e548435d63952109758e548427e62952109f58a548437a6095210cfd91548427f63552109f18d548427f62552109f189548433d5415210cf990548427e6
  | 9 => 0x54e30082ee628c020bb58a3008376518c020dd546300837a508c0209fd95300833e544c020cf551300835e534c020dd9453008375514c020de941300833e540c020cf550300835e530c020d754c30082ee620c020bb5883008376510c020dd54430083d9300c020cf953200833d54c8020d794f200835d53c8020dd947200837551c8020eb95320083ad54c8020f394f20083cd53c8020f9947200836d51c8020f9547200836551c8020cf952200833d5488020d794e200835d5388020bb58a200836e5288020dd94620083755188020ded5220083ba5488020de55220083b95488020ce55220083da5388020de54e20083d95388020d654e20082f96288020de94a20083ea5288020fc94620083795188020fc546200837151880209fd95200833e5448020cf551200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020eb95120083ad5448020f394d20083cd5348020f9945200836d5148020f954520083655148020bbd81200836e5048020bed95200837b65480209ed95200837b5448020ee95120083795448020ee55120083395448020f694d20083795348020f654d20083595348020bed8920083eb6248020de94920083ea5248020fc94520083795148020fc54520083715148020fac8520083e921480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c42de6315310b758c54c42ee6215310bb58854c433e64153109f98c54c435e63153109798c54c427d6315310d758c54c425d63153109f98854c436e62153109b98854c427d6215310db58854c426d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c42ee6214f10bb58853c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cf95343c433d54d0f10be98343c42f960d0f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f10be98243c42f96090f109fd9543c427e6550f109f59543c427c6550f10cf95143c433d5450f10d794d43c435d5350f109fd9443c427e6510f109f59443c427c6510f10e750c43c42f66110f10bd58443c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b
  | 10 => 0x1083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd946410837551904209fd95410827d65504209f195410833e5450420cf551410835e5350420d754d41083765150420dd54541082fb6050420be181410827f65104209f994410827d6510420cf950410833d5410420b798c41082dd6310420d794c410835d5310420bb98841082ed6210420dd94441083755110420be98041082f960104209fd97310827e65cc4209f597310833e54cc420cf553310835e53cc420d754f310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d3108376514c420dd54531082fb604c420be181310827e650c4209f594310833e540c420cf5503108376510c420dd54431082fa600c420be580310833e54c8420cf553210835e53c8420d754f210836e52c8420dd947210837551c8420be98321082f960c84209f596210833e5488420cf552210835e5388420d754e210837551884209fd95210833e5448420cf551210835e5348420d754d210836e5248420dd94521082be6408420af590210833e5408420cf55021082de6308420b758c210835e5308420d754c21083765108420dd54421083e52108420be98021082f960084209f992500827d64940209f597400833e54d0020cf55340082de63d0020b758f400835e53d0020d754f400837651d0020dd547400827f65900209f596400833e5490020cf55240082de6390020b758e400835e5390020d754e40082ee6290020bb58a40083765190020dd546400837a50900209fd95400833e5450020cf551400835e5350020d754d40083765150020dd545400837a50500209fd94400827e65100209f594400827c6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020dd94440083755110020ee500400827d65cc020af99330082bd64cc020cf953300833d54cc020d754f300837651cc020dd54730082be648c020af592300833e548c020cf552300835e538c020d7
  | 11 => 0x3e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209e98054082be64d4c20af593530833e54d4c20cf55353082f661d4c20bd587530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c20d7d52530835e5494c20e7952530831e5494c20d7552530839d5494c20c7552530835c5494c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7182530833e5454c20cf551530827f6454c209f191530827f6154c209f185530835f6554c20d7d51530835e5454c20e7951530831e5454c20d7551530839d5454c20c7551530835c5454c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d7d85530835e6154c20d7585530835c6154c20d7981530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209fd97430827e65d0c209f597430833e54d0c20cf553430835e53d0c20d754f43082fa60d0c20be583430827f6590c209f996430827d6590c20cf952430833d5490c20d794e430835d5390c20be98243082f96090c209fd95430827d6550c209f195430833e5450c20cf551430835e5350c20d754d430827f6510c209f994430827d6510c20cf950430833d5410c20d794c430835d5310c20e750c430827e64948209f592520827d65d0820cf953420833d54d0820d794f420835d53d08209fd96420827d6590820cf952420833d5490820d794e420835d5390820be98242082f960908209fd95420833e5450820cf551420835e5350820d754d420827f65108209f594420833e5410820cf55042082de6310820b758c420835e5310820d754c42082f66110820bd58442082fa6010820be58042082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420ed95151083365454420dd5515
  | 12 => 0x48520db551214836f5348520f9d8521483e75148520db14521483e45148520d914521483e64148520f950521483e63148520f94c521483eb6048520bb18121483e860485209f99421482be6408520af59021482de6308520b758c21482ee6208520f948421482fa60085209f997404833f54d0120cf15340482de63d0120b758f40482ee62d0120bb58b404827e6590120b798e40482dd6390120be996404837a6590120be592404837a5490120de15240483da6390120be58e40483d96390120b658e40483785390120eed0e40483b94390120be98a40482f96190120ded4640483eb2190120fa486404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec6250120be195404837865501209e19540483bb6450120eed51404837a5450120de15140483b85450120ce15140482fb6350120de14d40483ba4350120ee10d40483eb6250120be18940483e86250120eed0940483b94250120bed85404837b5150120eed0540483b94150120fac8540483e921501209f99440482fa6010120ee50040482be64cc120af593304835f53cc120d714f30482ee62cc120bb58b304827e658c120af99230482bd648c120be996304837a658c120bed9230483ba648c120be59230483b9648c120ae592304837a548c120de15230482f9638c120de14e30483da438c120f650e30482fa628c120be586304837b518c120fac8630483e9218c120d7d4d304835c534c120bbd8930482ec624c120bed9130482f9644c120de9513048378544c120f6d8d30483db534c120de14d30483d8534c120d614d30483db434c120f610d30483eb624c120be18930483e8624c120bed85304837b514c120f6cc530483d9314c120fac8530483e9214c1209f99430482fa600c120f64c030482fb64c8120be59320482f963c8120be58720483eb21c8120fa48720482ed6188120fad4220483ea4088120fa50220483ea3088120fa4c220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020cfd8e540833e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f61550209f185540833f6555020cfd8d540833e6355020cf58d540833c6355020cf989540833c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf99054082
  | 13 => 0xde9513088378544c220f6d8d30883db534c220de94d30883d8534c220f6d0d30883d8434c220be18930882fb614c220de54530883db314c220d794c308835d530c220bb98830882ed620c220f64c030882ed65c8220db597208836d51c8220be597208837965c8220bed9320882f964c8220be58f20882f961c82209f98f544827d63d51209f987544827d61d5120cfd5254482de6395120b758e544827e64951209f98e544835e63951209798e544827d6395120d758e544825d63951209f58a544836d62951209f986544827d61951209f58254483796095120cfd91544827f63551209f18d544827f6255120dbd89544827f61551209f185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f984544827d6115120de580544827e64d4d209f593534827e61d4d209f58753482be6494d20af592534835f5394d20d754c534827e6414d209f590534827e6114d209f584534827e65d0d209f597434827c65d0d20cfd53434833c54d0d20be98343482f960d0d209f996434827d6590d209f196434835f5390d20d714e43482fa6090d20be582434827f6550d209f995434827c6550d20cfd51434833c5450d20d7d4d434835c5350d209f994434827d6510d209f194434839d4310d20bb98843482ed6210d20be98043482f96010d209f997424833f54d0920cf15342482fa60d0920be583424827e65909209f195424833f5450920cf15142482fb6050920be181424827e6510920b798c42482dd6310920bd98442482f56110920be980424827e64d45209f593514827e63d45209f58f51483775194520afd9151482bc6454520b7d8d51482dc6354520af99051482bd6414520b798c51482dd6314520dd544514827e6414520cf990514823e64145209f590514833d64145208f590514827e6314520d798c514825e63145209f58c514835d63145209758c514837960145209f997414827d65d05209f197414833e54d0520cf55341482fa60d0520be583414827e65905209f596414827c6590520cfd52414833c5490520bb98a41482ed6290520be98241482f960905209fd95414827e65505209f195414833e5450520cf551414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520bb98841482ed6210520be98041482f960105209f997314827d65cc5209f19731482fa60cc520be583314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c520be98231482f9608c5209f995314827c654c5209f99721482ee65c8520db997214836f54c8520db553214836f53c8520db14721483eb60c8520bb98321483e860c8520bb58a21483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be181214836f54
  | 14 => 0x90548827e63152209f58c548836d62152209f984548827d6115220de98054882be64d4e20af59353882be6494e20af592538835f5394e209f992538833e6494e208f992538827d6494e20cf592538823d6494e209f986538827d6194e209fd91538827c6454e209fd85538827c6154e20d754c538827f65d0e209f997438827d65d0e20cfd53438833c54d0e20d794f438835d53d0e20be98343882f960d0e209fd96438827e6590e209f596438833e5490e20cf55243882fa6090e20be582438827f6550e209f595438827c6550e20cfd51438833c5450e209fd94438827e6510e209f594438833e5410e20cf550438835e5310e20d754c438839d4310e20be98043882f96010e20cf953428833d54d0a20be98342882f960d0a20cf951428833d5450a20bed8142882f86050a20b798c42882dd6310a20bd98442882f56110a20be580428837751946209f992518827d64946209f98e518827d6394620de982518827f64546209f191518827f63546209f18d51882be6414620af59051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf55341882fa60d0620be583418827f65906209f996418827d6590620be98241882f960906209fd95418827d65506209f195418833e5450620cf551418827f65106209f994418827d6510620b798c41882dd6310620bb98841882ed6210620be98041882f960106209f997318827d65cc620be98331882f960cc6209fd96318827e658c6209f59631882fa608c620be58231883765188620dd54621882fa6088620be58221883765148620dd54521882fb6048620be18121882be6408620af59021882de6308620b758c21883e52108620be580218833f54d0220cf15340882de63d0220b758f408833e5490220cf55240882de6390220b758e40882ee6290220bb58a40882f96590220de596408837a5490220ee95240883b95490220de15240883da6390220be58e40883d96390220b658e408837a5390220eed0e40883b94390220be98a40883ea6290220fa58a40882f96190220de546408833f5450220cf15140882fb6550220ded9540883bb6450220eed51408837a5450220de15140883b85450220ce15140882fb6350220de94d40883ba4350220ee10d40882f86250220eed0940883b94250220bed8540883795150220eed0540883b94150220cf950408833d5410220bb98840882ed6210220ee50040882be64cc220af59330882be648c220af592308835e538c220d754e30882ee628c220bb58a30882fb648c220ee99230882f9648c220ee59230882b9648c220de9523088378548c220de94e30883da538c220f654e30883da438c220f650e30882fa628c220fa98a30883e9628c220be5863088379518c220bed95308837b654c220bed9130882f9644c22
  | 15 => 0xc82de6315320b758c54c82f66115320bd58454c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e6115320dd98454c827661153209f58454c837561153209d58454c83796015320d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c827f6154f209f18553c82be6414f20af59053c835d5314f20bd98453c82f56114f209fd9743c827e65d0f209f59743c833e54d0f20cf55343c82fa60d0f20be58343c827f6590f209f99643c827d6590f20d794e43c835d5390f20be98243c82f96090f209fd9543c827d6550f209f19543c833e5450f20cf55143c835e5350f20d754d43c827f6510f209f99443c827d6510f20e750c43c82ee6210f20bb58843c833f54d0b20cf15342c833e5490b20cf55242c82fa6090b20be58242c833f5450b20cf15142c833e5410b20cf55042c82de6310b20b758c42c82f66110b20bd58442c82fa6010b20be58042c837751947209f99251c827d64947209f98e51c827d63947209fd9151c827c64547209fd8d51c827c6354720af99051c82bd6414720b798c51c82dd6314720dd54451c827f65d07209f99741c827d65d0720cf95341c833d54d07209fd9641c827e65907209f59641c82ee6290720bb58a41c83765190720dd54641c827f65507209f59541c827c6550720cf95141c833d5450720dd94541c83755150720bed8141c82f860507209fd9441c827e65107209f59441c82de6310720b758c41c82ee6210720bb58841c82fa6010720be58041c827e658c7209f59631c8376518c720dd54631c837651c8720dd54721c82fa60c8720be58321c836f54c8720db55321c836d53c8720db94721c83e651c8720f954721c82ee60c8720fa98321c83e960c8720bbd9521c836f6548720dbd5121c836d5448720db54d21c83e76148720f9d4521c836e5148720f914521c83e64148720f950521c83e63148720bb18121c82be6408720af59021c82de6308720b758c21c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320b798f40c82dd63d0320bb98b40c82ed62d0320b798e40c82dd6390320cf95140c833d5450320bbd8940c82ec6250320ee50040c82be64cc320af59330c835e53cc320d754f30c82ee62cc320bb58b30c82be648c320af59230c835e534c320d754d30c82ef624c320bb18930c83d9300c320b798f54882dd63d52209f98f548835e63d52209798f548827d63d5220d758f548825d63d5220db58b548827e61d52209f587548837a60d5220cfd5254882de6395220b758e548827e6395220d798e548825e63952209f58e548835d63952209758e548827e61952209f586548837a6095220cfd91548827f63552209f18d548827f61552209f185548833d5415220cf9
  | 16 => 0xe62944309f58a510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c2fa60d0430be583410c27f65904309f996410c27d6590430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c3765150430dd545410c27f65104309f994410c27d6510430b798c410c2dd6310430bb988410c2ed6210430be980410c2f960104309fd96210c27e65884309f596210c3765188430dd546210c27f65484309f595210c27c6548430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c2be6408430af590210c3e52108430be980210c2f960084309f992500c33e64940308f992500c27d6494030cf592500c23d64940309f597400c33f54d0030cf153400c2dd63d0030de943400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c2f96590030de596400c2796590030be592400c37a5490030ee952400c3b95490030de152400c3da6390030be58e400c3d96390030b658e400c37a5390030eed0e400c3da4390030de54a400c37951900309fd95400c33f5450030cf151400c39e4350030bed95400c37b65500309ed95400c3bb6450030eed51400c37a5450030de151400c3b85450030ce151400c2fb6350030f698d400c3d96350030de94d400c3ba4350030f690d400c39a4350030f650d400c3795250030eed09400c3b94250030de545400c3bb4150030ee505400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c39d4310030be980400c37a5010030ee500400c2be648c030af592300c2fb648c030ee992300c2f9648c030ee592300c2b9648c030de952300c378548c030be58e300c2d9638c030de94e300c3da538c030f690e300c3d9438c030de54a300c379518c0309fd95300c2fb654c030ded95300c27b654c030bed91300c2f9644c030de951300c378544c030bed8d300c37a534c030f694d300c3db434c030f690d300c3d9434c030f610d300c379524c030de545300c3db654c030b6d95300c35b654c030f6d91300c2db644c030f6991300c3d9644c030b6591300c3d8644c030f6d51300c3da544c030d6951300c3d9544c030f6151300c358544c030f6d85300c3da614c030f6585300c3d8614c030f6d45300c3da514c030f6545300c359514c030f6145300c3db414c030f6905300c3d9414c030f6105300c3da214c030f6485300c3d8214c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054
  | 17 => 0x230ee50c408c3d94310230e650c408c2f96210230be584408c33e54cc230cf553308c2f965cc230de597308c2fa64cc230ee993308c2ba64cc230ee593308c2f864cc230ded53308c3ba54cc230de553308c3b954cc230ce553308c2f962cc230be587308c27e61d51309f587544c37960d5130cfd52544c27e64951309f986544c27d61951309f582544c37960951309e582544c33f64551309fd85544c27c61551309fd81544c37b60551309f994544c33d5415130cf990544c27e61151309f584544c27e64d45309f593514c27e62d45309f58b514c3775194530af990514c2bd6414530bb988514c2ed6214530dd544514c27e6414530cf990514c23e64145309f590514c33d64145308f590514c27e6214530db988514c26e62145309f588514c36d62145309b588514c27e65d05309f597414c27c65d0530cf953414c33d54d05309f996414c27d65905309f196414c2de6390530b758e414c2fa6090530be582414c27f65505309f995414c27c6550530cf951414c33d5450530b7d8d414c2dc6350530bed81414c2f860505309f994414c27d65105309f194414c2de6310530b758c414c2ee6210530bb588414c2fa6010530be580414c27e65885309f596214c27c6588530b798e214c2dd6388530be982214c2f960885309fd95214c27e65485309f195214c27e65085309f594214c27c6508530af990214c2bd6408530f9484214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130de997404c27a65d0130ded53404c3bb54d0130de553404c3b854d0130be98f404c3da63d0130b698f404c3d963d0130f6d0f404c2f962d0130eed0b404c3b942d0130be587404c3bb41d0130ee507404c27e6590130cf952404c33d5490130b798e404c2dd6390130e7d0e404c2fa60901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c27e6510130cf950404c33d5410130e7d0c404c3b94010130be994404c37a65101309e994404c2fa6410130ee990404c37b5410130ee950404c3795410130ee550404c3395410130f6d8c404c2fa6310130f618c404c3bb4310130f6d0c404c39b4310130ee50c404c3d84310130be588404c2f96110130af992304c2bd648c130b7992304c39e648c130a7992304c39d648c130b7192304c35f548c130d7552304c2dd628c130b7586304c3db508c130f6d02304c3d8408c1309f987540c27d61d50309f983540c37a60d50309e983540c27d6595030cfd52540c27e61950309f586540c37a6095030cfd91540c27f61550309f185540c33d5415030bd984540c2f561150309f990540c33e64150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a6015030ddd46510c27e64944309f592510c27
  | 18 => 0xcf550438c39d4310e30af993528c2bd64d4a30cf953528c33d54d4a30cf952528c33d5494a30dbd4a528c27e6494a309f592528c27e6194a309f586528c33e5454a30cf551528c27f6454a309f191528c35e4354a30d750d528c27f6154a309f185528c2be6414a30af590528c33e5414a30cf550528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c33e54d0a30cf553428c2de63d0a30b758f428c39d43d0a309fd96428c27e6590a309f596428c33e5490a30cf552428c2fa6090a30be582428c27f6550a309f595428c27c6550a30cf951428c33d5450a30e750d428c2fb6050a30be181428c27f6510a309f994428c27d6510a30cf950428c33d5410a30b798c428c2dd6310a30bd984428c2f56110a30be980428c2f96010a30af993518c2bd64d4630cf953518c33d54d4630cf952518c33d5494630ddd46518c27e64946309f592518c27e62946309f58a518c33e5454630cf551518c27f64546309f191518c35e4354630d750d518c27f62546309f189518c2be6414630af590518c33e5414630cf550518c2ee6214630bb588518c37551146309fd97418c27e65d06309f597418c33e54d0630cf553418c2de63d0630b758f418c39d43d06309fd96418c27e65906309f596418c33e5490630cf552418c2fa6090630be582418c27f65506309f595418c27c6550630cf951418c33d5450630e750d418c2fb6050630be181418c27f65106309f994418c27d6510630cf950418c33d5410630b798c418c2dd6310630bb988418c2ed6210630be980418c2f960106309fd97218c27e65c86309f597218c33e54c8630cf553218c36e52c8630db54b218c2fa60c8630be583218c27f65886309f996218c27d6588630cf952218c33d5488630dd946218c3755188630be982218c2f960886309fd95218c27d65486309f195218c33e5448630cf551218c2df6348630b718d218c36e5248630db549218c3765148630dd545218c27f65086309f994218c27d6508630af990218c2bd6408630cf950218c33d5408630b798c218c2dd6308630f9484218c2fa6008630be580218c33e54d0230cf553408c2de63d0230b758f408c39e43d0230be597408c37965d0230ded53408c3ba54d0230de553408c3b954d0230ce553408c2fa63d0230f698f408c2da63d0230f658f408c3ba43d0230f690f408c3d943d0230ee10f408c2f962d0230eed0b408c3b942d0230be587408c3bb41d0230ee507408c33e5490230cf552408c2de6390230b758e408c39d4390230cf951408c33d5450230e790d408c33e5410230cf550408c2de6310230b758c408c39d4310230ee500408c2f96510230de594408c3ba6410230ded50408c3ba5410230de550408c3b95410230ce550408c2fa6310230f698c408c3d96310230eed0c408c3da431
  | 19 => 0xb211036d52c84409fd96211027e65884409f59621103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102be6408440af59021102de6308440b758c21103e52108440be98021102f96008440d798e501035d6394040cfd0e501033d4394040b798f40102dd63d0040e798f40102bd63d0040e758f401029d63d0040cf94f401033d52d0040cf54740102bd6490040cf95240102de6390040b758e40102f96490040ae592401037a5490040ee95240103da6390040be58e40103d96390040b658e401037a5390040eed0e40103b94390040de54a401037951900409fd9540102bf6550040cfd95401023f6550040afd8d401033e5350040cf549401033d5150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140102fb6350040de94d40103bb4350040ee90d40103b94350040ee10d40103795250040eed0940103ba4250040ee50940103b84250040de54540103bb4150040ee90540103b94150040ee10540103bb6550040aed95401033b6550040eed8d40102bb6350040ee98d40103b96350040ee18d40103bb5350040ee94d401033a5350040ee54d40103b85350040eed8940103ba6250040ee58940103b86250040eed4940103ba5250040ee54940103395250040ee14940103bb6150040ee98540103b96150040ee18540103bb5150040ee94540103b95150040ce54540103b85150040eec8540103ba2150040ee48540103b82150040d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c35d63952309f98a548c27d62952309f986548c27d6195230e758e548c3b86095230cfd8e548c33d6395230c758e548c33f6295230cf98a548c33d6295230cf18a548c33f6195230cf986548c33d6195230cf186548c33e6095230cf182548c33f64552309fd89548c27c62552309fd85548c27c6155230de181548c33f6555230e758d548c3b86055230cfd8d548c33d6355230cfd89548c33e6255230cf589548c33c6255230cfd85548c33e6155230cf585548c33c6155230cf981548c33c6055230ce181548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e5490e30cf552438c2f96090e30b7596438c35d6590e30d7952438c39e5490e30c7952438c39d5490e30d7152438c3da6090e30b7582438c3d96090e30b6582438c33e5450e30cf551438c2fb6050e30be181438c35f6550e30e7d91438c35e5450e30e7951438c31e5450e30e7551438c35c5450e30b7d81438c3db6050e30f6181438c33e5410e30
  | 20 => 0x27e6214540db988515026e62145409f588515036d62145409b588515037960145409f99741502be65d0540cf99741502be63d0540cfd4f41502bd62d0540cfd4b415033c51d0540eed8341502be60d0540ee18341502bd6490540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f86050540af18d415033f5350540afd89415033f5250540edd8541503b75150540cf14541503b45150540eed8141502bc6050540ee18141502b860505409f99441502be6410540b798c41502dd6310540bb98841502ed6210540be980415027e65c85409f597215027c65c8540af99321502bd64c8540eb50b21502fa60c8540be583215027e65885409f596215027c6588540af99221502bd6488540ed50621502fa6088540be582215027f65485409f995215027c6548540af99121502bd6448540eb50921503b541485409f994215027d65085409f19421502be6408540af59021502de6308540b758c21503e52108540be98021502f96008540b798f40502dd63d0140be98f40503da63d0140b698f40503d963d0140ded4f40503ba43d0140be58b40503bb42d0140ee50b40502f961d0140eed0740503b941d0140b798e40502dd6390140af98e405039e6390140a798e405039d6390140cfd4e40502bd6290140af58640503bb5090140d798e541035d6395040d7d4e531027e6294c409f58a531027e6194c409f586531037a6094c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431033e53d0c40e794f431039d53d0c40ee98343102bd60d0c40ee58343102b960d0c409f59643102bd6490c40be582431027f6550c40afd95431033f6550c408fd95431039f6350c40e7d4d431033e5350c40e714d43102bf6050c40ee98143103b96050c40cf95043102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c6354840cfd0d521033d43548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521033e54d0840db94b421036d52d0840be98342102f960d08409f596421027f6550840cf95142102de6310840b758c421036e5210840db54842102f66110840bd58442102fa6010840be580421037751944409f98e511027d63944409f98a511027d62944409fd8d511027c6354440cfd0d511033d43544409fd89511027c6254440b798c51102dd6314440bb98851102ed6214440dd544511033e54d0440dd947411037551d0440be98341102f960d04409f596411027f6550440cf95141102de6310440b758c41102ee6210440bb58841103765110440dd54441102fa6010440be580411027f65c84409f997211027d65c8440db94
  | 21 => 0x5394640ddd46519027e63946409f58e519027e62946409f58a519037a6094640d794d519035d53546409fd8d519027c6354640cfd0d519027f62546409f18951902de6314640b758c519035e5314640d754c51902ee6214640bb58851903755114640d794f419035d53d0640d794e419035d5390640dd94641903755190640be98241902f96090640d794d419035d5350640dd94541903755150640bed8141902f86050640b798c41902dd6310640d794c419035d5310640bb98841902ed6210640be580419027f65c86409f997219027d65c8640d794f219035d53c8640db94b219036d52c8640be98321902f960c86409fd96219027e65886409f596219035e5388640d754e21903765188640dd54621902fa6088640be582219027f65486409f595219027c6548640afd9121902bc6448640d794d219035d5348640db949219036d5248640dd945219037551486409fd94219027e65086409f59421902be6408640af59021902de6308640b758c219035e5308640d754c21903e52108640be98021902f96008640b798f40902dd63d0240d794f409035d53d0240af597409033d65d0240e798f40902bd63d0240e758f409029d63d0240cf94f409039e53d0240c794f409039d53d0240cf54b409033d51d0240be597409037965d0240be98f40903da63d0240b698f40903d963d0240f694f409037953d0240f654f409035953d0240be58b40902f961d02409f98b535027d62d4d409f987535027d61d4d40de583535035f5394d40d754c535027e6214d409f588535027e6114d409f58453502fa60d0d40d7d4e435035c5390d40be98243502f96090d40cfd4e435039f5390d40e714e43502bd6290d40af58643502be6090d40ee98243502ba6090d40ee58243502fb6050d40be181435027e63d49409f58f525027e61d49409f587525036f5294940b798c52502dd6314940db54852502f66114940bd584525027e6314940d798c525025e63149409f58c525035d63149409758c525027e6114940dd984525027661149409f584525037561149409d584525037960149409f99742502be65d0940cf99742502be63d0940cfd4f425033c52d0940af58742503bb60d0940af98342503b860d0940af592425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be18142502bc6350940cfd4d42503af6250940ebd49425033c5250940eb14942502bf6150940eed8142502bc6050940ee18142502b860509409f99442502be6410940b798c42502dd6310940bd98442502f56110940be980425027e63d45409f58f515027e62d45409f58b515033f42d4540cf50b51503775194540b798c51502dd6314540bb98851502ed6214540dd544515027e6314540d798c515025e63145409f58c515035d63145409758c515
  | 22 => 0x7409f98e51d027d63947409f98a51d027d6294740d794d51d035d53547409fd8d51d027c63547409fd8951d027c6254740cfd0951d033d4254740b798c51d02dd6314740d794c51d035d5314740bb98851d02ed6214740dd54451d035e53d0740d754f41d037651d0740dd54741d02fa60d0740be58341d02be63d0740e794f41d033d53d0740e754f41d031d53d0740af58b41d033d52d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740d794e41d035d5390740d794d41d035d5350740afd9541d033f6550740af18d41d039e5350740cf54d41d039d5350740c754d41d02bf6250740cf54941d03b76150740cf94541d02bc6050740b798c41d02dd6310740d794c41d035d5310740bb98841d02ed6210740dd94441d03755110740be98041d02f960107409fd9721d027e65c87409f59721d02be64c8740af59321d035e53c8740d754f21d036e52c8740db54b21d03ad42c87409fd9621d027e65887409f59621d02be6488740af59221d035e5388740d754e21d03765188740dd54621d03b541887409fd9521d027d65487409f19521d02be6448740af59121d035e5348740d754d21d036e5248740db54921d03ad4248740dd94521d03755148740ed50521d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740b798c21d02dd6308740d794c21d035d5308740f948421d02fa6008740be58021d035f5394e409f98a539027d6294e409f986539027d6194e40e759253903d86094e40d7d92539035f6294e40d798a539035d6294e40d718a539035f6194e40d7986539035d6194e40d7186539035c6094e409fd89539027c6254e409fd85539027c6154e40de181539035f6554e40e759153903d86054e40d7591539035f6254e40d7989539035d6254e40d7189539035f6154e40d7985539035d6154e40d7185539035e6054e40d718153903586054e40d754c539035e53d0e40be58343902bd65d0e40cf597439033e53d0e40e794f439031e53d0e40e754f43903ba60d0e40af58343903b960d0e40ae58343902fa6090e40be58243902de63d4a40b758f529035e53d4a40d754f529035e5394a40d754e529036f5294a409f98e529027d6394a409f986529027d6194a40de982529035e5354a40d754d529027f6354a409f18d529033f4354a409fd85529027c6154a40b798c52902dd6314a40d794c529035d5314a40db54852902f66114a40bd584529035e53d0a40d754f429035e5390a40d754e429036e5290a40db54a42902fa6090a40be582429035e5350a40d754d429036e5250a40db54942902fb6050a40be18142902de6310a40b758c429035e5310a40d754c42902f66110a40bd58442902f96010a40b798f51902dd63d4640d794f519035d53d4640d794e519035d
  | 23 => 0xe55250087395494021de152500877b5394021de94e50087da5394021d694e50087eb2194021fc88650087e92194021fc48650087e12194021ded92500877a6494021de59250087786494021ded8e500877a6394021de58e50087786394021de18a500877b4294021de90a50087794294021de10a50087786194021ded06500877a4194021de50650087784194021dec86500877a2194021de486500873e5454021cf551500875e5354021f9485500867f64540219f191500867f63540219f18d500876f2154021dd885500876d2154021dd48550087652154021ded95500877b5454021de95150087ba5454021ce95150087795454021ee55150087395454021de151500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021fac8550087f22154021fa48550087f12154021f8485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877a6254021ded09500877a4254021de50950087784254021de985500877b4154021de90550087794154021de105500877b2154021dac85500877a2154021dc88550087792154021da48550087712154021d848550087782154021af99050086bd6414021cf950500873d5414021b798c50086dd6314021d794c500875d5314021f948450086fa6014021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f40e719253d03d96094f40d719253d035f6294f40d798a53d035d6294f40d718a53d035f6194f40d798653d035d6194f40d718653d035f6094f409fd8953d027c6254f409fd8553d027c6154f40d7d9553d039c6454f40f658153d035e6454f40d7d8953d035e6254f40d758953d035c6254f40d7d8553d035e6154f40d758553d035c6154f40d758153d035d5314f40be98343d02f960d0f40b798f52d02dd63d4b40d794f52d035d53d4b40d794e52d035d5394b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d035e5354b40d754d52d027f6354b409f18d52d027f6154b409f18552d02de6314b40b758c52d035e5314b40d754c52d036d5214b40bd98452d02f56114b40d794f42d035d53d0b40db94b42d036d52d0b40be98342d02f960d0b40af98f42d039e53d0b40cf54f42d039d53d0b40c754f42d033e52d0b40eb94b42d03ad52d0b40af58742d02be60d0b40ee98342d03b960d0b40d794e42d035d5390b40d794d42d035d5350b40afd9542d033f6550b40af18d42d039e5350b40cf54d42d039d5350b40c754d42d03af6250b40cf94942d02bf6150b40af18142d02de6310b40b758c42d035e5310b40d754c42d036e5210b40db54842d02f66110b40bd58442d02fa6010b40be58042d02de63d4740b758f51d035e53d4740d754f51d035e5394740d754e51d03775194
  | 24 => 0x41487e46290521f990a41486f560905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414877465505219d19541487b76450521edd5141487765450521dd15141487b45450521bdd8d41487e76250521bd18941487e46250521b918941487b74250521f990941487b54250521f950941487a54250521bdd81414867e6510521b798c41486dd6310521bb98841486ed6210521bd98441487b54110521be98041486f96010521bbd9221486ed6488521bb58e21487e75188521f990621487e54188521bb582214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121af99050486bd6414121b798c50486dd6314121de540504867e6414121cf990504863e64141219f590504873d64141218f590504867e6314121d798c504865e63141219f58c504875d63141219758c50486fa60d5021be583540867e61d5021dd987540867e60d5021de983540867a60d50219f583540877960d50219e583540867d6595021cfd52540867e60950219f582540863d6595021cf986540873c6195021cfd82540873e6095021cf582540873c6095021cfd91540867f60550219f181540873f6555021cf985540873c6155021cf085540873f6055021cf981540873d6055021cf18154086be6415021cf55054086fa6015021be580540867e6415021cf990540863e64150219f984540877661150219d984540867e6015021de980540867a60150219f580540877960150219e580540867e64944219f592510867d65d0421cf953410873d54d04219fd96410867d6590421cf952410873d5490421bb98a41086ed6290421dd946410867f6550421cf951410873d5450421dd945410867f65104219f994410867d65104219f194410873e5410421cf55041086de6310421b758c41086ee6210421bb58841086fa6010421be580410873e5488421cf55221087775488421ed95221087755488421ed55221087355488421bd58a21086e56288421dd94a21087e652884219fd95210873e5448421cf55121086f76548421ddd9521086776548421ddd5121087b65448421dd55121087b55448421cd55121086f76248421dd94921087e65248421f9d0921087e64248421f950921087e44248421f9d9521086e76548421d9d9521087e76448421f999121087e56448421f919121087e75448421d9d5121087e65448421e995121087e55448421d955121087a55448421c955121087e45448421f9d8121087e66048421f958121087e46048421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021f9487500873e5494021cf55250087e52194021ded42500867e64940219f592500867e63940219f58e500877b5494021de95250087ba5494021ce95250087795494021e
  | 25 => 0x75a5354041de54d50107d95354041d654d50107785354041ded49501077a5254041fa949501076a5254041de54950107e95254041da54950107785254041eed0550107f24154041ee50550107f14154041de991501077b6354041de98d50107796354041de18d501077b6254041de98950107796254041de189501077b4254041de90950107794254041de109501077a6154041ded05501073b4154041de90550107794154041ce50550107784154041b798c50106dd6314041d794c501075d5314041bb98850106ed6214041db948501076d5214041be980501077950140419f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548877661952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221be98054886f96015221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e6015221de980548867a60152219f580548877960152219e580548875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e219fd81538867c6054e21af99053886bd6414e21d754c53886fa6014e21be580538873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542886de6310a21b758c42886f56110a21be98042886f96010a21cfd53418873c54d0621cf952418873d5490621bb98a41886ed6290621bd59641887756590621dd95241887b65490621ed55241887745490621bd58e41886f66290621f998a41887e56290621bd582418873f5450621cf15141886f76550621ddd9541887b76450621edd5141887765450621dd15141887b45450621bdd8d41886f46250621edd0941887b54250621bdd81418873e5410621cf55041886de6310621b758c41886ee6210621bb58841887b54110621be98041886f96010621bd597218877565c8621bdd9321886f564c8621bd583218877b50942219f992508867d64942219f98e508867d63942219fd91508867c64542219fd8d508867c6354221dbc8550886be6414221af59050886de6314221b758c508877950142219f983544867d60d5121cfd52544867e64951219f586544877561951219f982544867d6095121bed8154486f86055121cfd91544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf55054486fa6015121be580544873e6415121dd584544867e6015121de980544867a60151219f580544877960151219e580544867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f99641486f66590521dd99641486f56490521dd95241487745490521bd58e41487e76290521bd98a
  | 26 => 0x14c41b798f52106dd63d4841d794f521075d53d4841be98352106f960d4841d794e521075d5394841dbd4a521067e63948419f58e521067e60948419f582521076f5394841db94e52107ce5394841d394e521076d5394841f354e521074d5394841db14e521076c6494841dbd8e521076e6394841db58e521076c6394841db986521076c6194841dbd82521076e6094841db582521076c6094841d794d521075d53548419fd8d521067c63548419fd81521067c6054841dbd95521076f5354841db94d52107ce5354841d394d521076d5354841f354d521074d5354841db14d521076e6454841dbd8d521076e6354841db58d521076c6354841db985521076c6154841db105521076f6054841db981521076d6054841db18152106de6314841b758c521075e5314841d754c52106ee6214841db54852106fa6014841be580521073e54d0841d794f421075d53d0841db94b421076d52d0841bd98742106f561d08419f596421075e5390841d754e421076d52908419fd95421073e5450841d794d421075d5350841db94942106f66110841bd58442106fa6010841be580421075e53d0441d754f411076e52d0441db54b411079e53d0441cf54f411079d53d0441c754f41107ae52d0441cf54b41107ad52d0441cb54b41106bd6490441cf952411075e5390441d754e411076e5290441db54a41106f56490441dd95241107b65490441f594e41107d55390441f994a41107755290441f954a411076552904419fd95411075e5350441d754d411076e5250441db54941106bf6550441cfd95411063f6550441e794d411073d5350441e754d411071d5350441eb949411073d5250441eb549411072d5250441afd85411073e5150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107d65350441f554d41107e65250441dd54941107e55250441d954941107b74250441ed50941106de63d4041b758f501075e53d4041d754f50106ee62d4041bb58b501076e52d4041db54b501075e5394041d754e501076e5294041db54a501077b50940419f98e501067d63940419f98a501067d6294041ded4e501077a5394041f694e501075a5394041de54e50107d95394041d654e50107785394041ded4a501077a5294041fa94a501076a5294041de54a50107e95294041da54a50107785294041eed0650107f24194041ee50650107f14194041de192501077b6394041de98e50107796394041de18e501077b6294041de98a50107796294041de18a501077b4294041de90a50107794294041de10a50107786194041ded06501077a4194041de506501075e5354041d754d501076e5254041db549501067f63540419f18d501067f62540419f189501073f4154041cf505501077b6554041ded4d501077a5354041f694d5010
  | 27 => 0x419fd8953d067c6254f419fd8153d067c6054f41d754c53d076f5294b419f98e52d067d6394b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41b798c52d06dd6314b41db54852d06fa6014b41be58052d06f661d0b41bd58742d06be61d0b41ed98742d07b561d0b41af58342d06de63d4341b758f50d06de6394341b758e50d077b50943419f98e50d075e63943419798e50d067d6394341d758e50d065d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341cfd0950d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41bb98853906ed6214e41be98053906f96014e41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529076d5214a41be98052906f96014a41bd98642906f56190a41af597419073d65d0641cf54f419073d52d0641bd597419077565d0641bd58b419077b50942419f98e509067d63942419f98a509067d62942419fd8d509067c63542419fd89509067c6254241cfd0550906de6314241b758c50906ee6214241bb588509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506fa6094d41be582535075d5314d419f988535067d6214d419f980535067d6014d419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be18152506de6314941b758c525076d5214941be98052506f960149419f98c525075e63149419798c525067d6314941d758c525065d63149419f980525077a60149419e980525067d6014941de58052506796014941af997425073e65d0941af58f425073f53d0941cf14b42507b761d0941af98742507b461d0941af58342506bd6490941dbd4a425076c5290941bd98642506f56190941bdd8542506f46150941edd8542506bc6150941ed18542506bf6050941bd58b41507b742d0541ed50b41506bd6390541af58a41507b75190541af582415067e63d41419f58f505067e62d41419f58b505073f42d4141cf50b50506de6394141b758e505077b5094141de540505067e63141419f58c505067e62141419f58850506ee62d4c41bb58b53106fa60d4c41be583531075f5394c419f98a531067d6294c419f982531067d6094c41d7192531075f6294c41d798a531075d6294c41d718a531075c6194c41d7d82531075e6094c41d7582531075c6094c419fd89531067c6254c419fd81531067c6054c41d7d95531075e6454c41d7d89531075e6254c41d7589531075c6254c41d7985531075c4154c41d7d81531075e6054c41d7581531075c6054c41b798c531075d5314c41bb98853106ed6214c41be98053106f96
  | 28 => 0x4000000000340030000000000c001001c00200040310050046002400000000040028001000c00100ec0000024000000000000280120004004001000100140030000003000c00400240060024001000000100000070018006000800000200020090004000c0060028003001c0040000001000000200340020018000001c01d003800a000c006000003d000800c007401e000c03700040010058000000c0080134003000800200240000000005000400a00200000014000000400400040420000004002c00200000130014003001000100000220014000000000d009c00000040080008007002400c00900020038000002c00100e0006000400100140000038008000000100480110080007000c0000064001000400e0000000001800c00000040024002003c00000240010000000002800100100360018002000000100100000000007001c005000c012009c008001c001000000a00200040008005008400b001c0020004000000000000000030018003002c00700080030000000000000300100060004000000c044000800400000480018011004400c0004003000000000480010050000001c00c000000000000010008001000c004002c0000000002000001f001000c0050000000001a000400000800000000003000c036001c00b000400000d0003001001500940010000002006400100000000118005001c005000c016000400000140080024001001801f0000001001400c000400000580230000001000c003007400c0004003000000000040010038004007c001000800100080150004002000000e00100210004000002400000700020004001000c0080000002000000700100000008000008000400000150014002000400f00a40050000008001400b00000060004014000400a01f0000003401e000c0030000000000800000000040010006000c0010010006000801400d000300340070018002005c0010000005000002a00240040010000000c000000c00e0004002001000c005c0000030000006c001002402f000400500880020024064001400900500040014006006000100080030010012000000000a0003003400000000170000000000801400000060010000000000300000010004000001400b003800000100050000005002c0070020004001c01100480010034014000002000000250010009006c006000c0140020001001c00000000000004000000000f000002c000c0160004000003801800580000038022000c00100040130000008001c0070000000004c002001000100300010038000000000000040020010000000800a0000000000c00c000001d000400d0006fa60d4f41be58353d075f5394f41be98253d06f96094f419f98a53d067d6294f419f98253d077a6094f419e98253d067d6094f41de58253d06796094f
  | 29 => 0x2000002000c800000d80000064025000801100140200008008001c0050018000000000001b4005002c005002c00000040100020003007c0000008004003800200040010054001001c051000400000040020024000000c0000000008000c007001800300180050020010000c01000cc00100600030044029000800400280000000003000400000000020064009005000a0010000000000000080020114000006001f000c02b00040110000004000000400000040000014000000e000000200100360004032000c004006c0010000004000000e00f8001003801f0014000000000a0010000000001a0064000000401500280120000000000400b0050005001400700140010004010001000000040050080000000400400080010004005000000e000000800000050010000006800a00040110018005002001a00000010008005010c00000040010010002000003d000000900340040010006005402900880070000002001002600b000100bc002000c01800100010004009000401d0038002002400f0058001000000900000060000004002000f000c000000400e00080370000007004c00b000000b0014003028c01500700190000013002400500e802000fc00a003c00800000000000003000000700080000004002000400a002404c00000000014008002400000300030024028000400100040020024022000000200340000000009000401e000000d0000004004800200140010000001007c00e00040000008005000c001000000200900020004009001c012001000200b40220000008000000900080060040017009800300000010004008000001800200020018003003c000001000300080180034016004c00000100000000009003005400000170028010000402d0000001006401f002003400100010008000003c00500c8045001402c00180000004008000c00a0000007000c00000000060028000008c01e000000100000000054000000000000000110000000000001e000000e002400000140050000001000400b0004000000801d0030000000c005003c002001000200000000058023000c0030014035002c009000c0000000000004c019000000100c80310110002000800f000c00100000020024003000009c000800300000000034001000c03000000000010001000400900000000000003000401c0004013000002000100050004008000001900180020038001000c00400800080000007001000e0004033003000c0078001001000c00000040024004001400800400070060001004800c001000c002802e0028000000c002013001d000401e0068000000000000000000000000000400b0000004005806600440020000000002800300ec001002800300b8001000c00000080030024001000c004000000200440010028003001400600
  | 30 => 0x2001d00280a700c4009015000f000000400000010028003000800a00240240008003000801200080080008000018800d000000c004800a0004014000000e00080000010004000c07300100050040001000400c001c00100000000058000003801c00040090004000005001900080010024003000c01a0004005000800400040030020001000000100000020000024003c01300080000014006000000a003c02d005c0010060000001c010001400a000800000180000000003000c0390034045002800e000000003280000028007000000e000c00200080000000000003c00100140020014003002c01400000130014006005c004000800a00000060050003002c00000280000008000000c01800080040000005005400a00000070000010000002300b400800180220000000000c004006c00b003402900040070004006001000c0004011001c03900180180000000000c00f002400d00340020008002002c003005801f0000001001404b000000000280040120001000400100000090054000000400c002000a0028029003400e00200070024006003000300000000020034001c01a00f001500b4003001400000300030004003000c008000401a0030000005c00d0014003000000100300040000001008c0040000000001c003000801900240140014000001801700140260018000000c0220014047001c002000401d00c0002002c01700100010000000001400e00140270008002001001b010802400040110094005003c00b00000040034008000400500040060048009008802900ec00d0074006000c00000000030004002001c00200140000018000000c005003003b000803a0024002000c0040074008004800f00100040010005000c0000000001000400000100090000001002c00200c80000000003000c007002c003003400400100030000000000400400040260000008008000000140020048015004800100580160024000002001b0004000000c0000000008003c01f000c0120030001000800700100000000001000c002001c002002000b002c000000400b0014000001401100000120000000006400d0008018002800000080030018000007c00a00a4000000800c005000f000000d000800100b00010010002000400000040010028003002803f0000001000401300100030000000001c00200b4009000c008000c010002400a00300060004006001c002002800000080010008000000000000000050000003002c000000800100340180008000000800101d4002004003f0020000004800a0008007015400900100070004000000c01500900220004003007c0020004008008c0360000003001000f00700020084021000c0000000005002c00600000220000002000c0000004013002c0130020002002403c0020000001004d00240
  | 31 => 0x14000000d000001a00000000004000000401b002c000002c006002c002001802a0008027002800a004400000040000024000000c00000340000004006000000200000000074000001403e00180040008004000c0010010004000c013014002c00140020000007000c001006c0000014022000c0000000000014000400dc0010004001002400a001800300040030070002001801b000000b0018002004400c0004008001c013004000100180080008009000400100080000010005001000300000040040008000c0000014003003800800c400500040020074011001c00000000000050044000000500000000078010001c002007400d00000000000000000400000040040010000000c007001007a00380000018012001400200000030030000005400500600100000000002000000180060000011003400700040150070000000800000a800100380010000000000c00301200000008003001c003001c000001001000140060090006000000900480130028000006c005004800b00200050048003000c00800000000004001000800c0020004000c000005000800000070010002001400100380080028001000400800080030000013001c00700b8002014800000100050008001000800c0004007002400000040060080000002c0000054015000400000040030000015010c00e012800000640000008005001c00200180010038000002c002006c01e0040041000c0040004003000c00c000c000003000d00b4001000802100000220020008000c000000001600180000010002000c004000000f001c016007400000040010004025001400700100000008006000c0000034001001800000040050034017000c006000800f00700010000005000000200040090028000005c01e0004025000c001001c002001c01d004400400f000500580100024007002c00800040020048000000803f00140000020006003800400240030028000000400000040160094005000000f00040010000022000400a001c00c0000042000000000140000004008000800200000050010024000c01400080000004002004c04600000140000000007801c000000e00180040010003000001c009000f001c000001002b00000000080001000800800000010024000000c0140000000000000000140270018000001c00a00040050004002001800400e400100180010004010003000100400020000002003400200000000010003000c00d0010000000800400c800b002c000005400a002002d000c01e000c0000008007000000200080030000009000000f00040130020004000c00e0024004004c00800c8010009000d002c0030020017000400200180090004009002000b0000003003c01a000000400440010080011000400600440020008005000000100c802e000c0010
  | 32 => 0xb1e86d69bc20151c28e112ad9a01b1523aa5ad8dbe625253261182de278967c80a88169431ba413281a4b991ca26f7889485060c26150b4c1a229c67ba971a6cd06c06112cfc828ab124932a0e088d0b048ea6884588092684149c00000ec56b8afe2c100008ec691e79a40000002776160a12c73919d40001d75acc218e21fc00033c1a2c74b98760000f7c11c00008170c191800000b6600002ee1caf8e42560a10996a9a680007b290fa75295a80bc9f804b50e9a8c91f0063b0594700e464abb40000b063f80290c76aba8cea00018c51e4219a806420cbb49a735bccacaa5b9c8ea5f000000023ce55f64c2a0e9e3d2c5d68aa012b7204496f4a0d87f259213896c2498a68220502c6a3cd29918b29e5298d708000820c056c7209c0049e19820b4878f0e30a767a383ea0f88f020001bb678aa7e8afd22db6e4aca42dc80005d389420001a1e057555e3d41f2a4982930216163c027082a0000000a1768dc0002173000000024800008b60e8492316ccab1187e4db000020a13f039eed18582a0d0000199e000251031a9d5aae993da53f673846a80005a4065c7f99a718a8a94a5365d7c81200604c996fb130000069ed4ba7a5ccb6000025e1dad416000169c1aa22678e24c1c2f91bd80000e94629130ea94e7f415192d66a5a8c439623bd80a2887af08e5aa019c611792a5c06f21b65c700006c90000b678f6e1999672bbca8eda8e4a5e2279afa08c2b882ac00ba00002ca94ad1699adae11563537b2f0800012b20ba6c89d8e3d7c00065518d37320accac50604a3f038e4b91aec7801c12113800000015be97a03ec00021ec00025c44bb15ec5c4911c343a93276b291a4f39ba8a1f9bfe5e88694a539c4c37e997c96504f09bb055a3a09a460000aa614001fa4d5000000009bc3994000000000053525fa28494462c761990002eaaa2885022bc238d7728a7a70ec000b4c1074afda8340001c9473029337bc06c266f03acb33ce3e64621346fd94910000007002c0050000008000800100000080000004000001700000000000004000001a002800c0008002000c004001800d000c002000c0170010001001400600280080000001001800100080150128000001800600f000c001800300300000060015001400a002400e00140010010002000802e000c03b000000100080010014000000c0010000002000800e000400100080130000031000400200340080020000000c0010000000012c00100140000064001000000300000090020001004c0000020024002404500280000018000000000400180000028005001801000380000000007000400b000000100040000004001000000d00380000024004000000e00040000000002000c0000000000002800400080000038003002c00400080220014000000c000000c00200580080004
  | 33 => 0x8c7c48307f80000d3ca5201dca4d419089e1b0038e910b18d082c74b25ac10101ceab4195e6441c929e8db330c0890a3a4847a00000008e45aa250617e47d29d6f8b698266f4cab2311c00000000002fe8000220549006608446b097e091780000001b42a428000a06ae1e1dc1d526e094ec3720ddc4d5a7f218902801a89b3871b5f09b0c022d42e8000537dcf25b4400000022d7307ab802b5000035200007432a346f200004f5a7ce03c8df871a8000803803070fcf163b04000000140285f800056ddb9830885547f824b7aaf2b500a587de000219254e83fa7ca0000000000000023ca3e1000065c00009622e407f080000001bbc5a593e2000000000000006582dfd2aa28160dbac8088340000001fd41cde0047e1400056b228e0000000bb3000032697dc00001408d2a0373591cbf05487ca00006dc0000000bc38000000000000018bf1da000010b8daa28edb500000c3babc17442b2000056c0000921178082d2eca000000000029a638d24341250fecb1c8000556c0000001dde0000000b630cd6896883ea5f8312a2ea947579276a3ae40000002ec85a30bcc59502e200025f0564884c2089af0708c0851ab914c42d6bd03dea69891982269ba83506698bbe0000758695126a007950c09a81ea0c1113a6ff0f7e6d1a3b3bcc800045e8e0eb3d2cd67ce850e29689ba8100a449f9e30c7fb07d400015847218edcaa48b266aa0000114837014a06404a19bfa29a1e863b85b589e208f8415ac3e000091100000007afd0106eb800093fa9f20000d246de40000002d2c000140a000090898d630844997510002881000000073f80cc28f096296d9d123e3a9f4626895c0002be6933072d856a3af9f914607931d0a0e18180a49a9052738bca7ff69e1732c5e00a404b037c2062000118003f00004c9db577ef0000000085047b85f0a319bbd1d3052076706d01ae9f2494e8e32901e98e0000833a7e5df2525449aa53cd129bf4e3f5e680005b6a96569f0de91919f5a7f161e0000107e494a8bd0000eb189a4e2200000000178e427b680004ab02559c30000b44a506858aa3f9ff9efb231da9e0ba09650001506000237c94b16bb3e98cfd0002a0383e8e46a62401ca9909b501e2ae0000137d0000fa0441a93f0f92a7f861800008c4ba23e92470b814d0226c68037646cfe12e181cb731d223879981136edfa4c5930c00022c4a445880b46800008eaa2b00013360001db71ba942e88e8c00b62165c7138388abcc7e20002d844a480000002c143025d11614241e4d3199235f9e0d000035a4e300007d920c8abe000000425a033080005cc1b3281d800069be6540000f43a62d54e913000000000000001eaa0002ed35fc0c0f00011c66990796464e8a825024f6b5d91243a29526b009610a23a28c50a2e0d7ef8000a1e0a8253e8000
  | 34 => 0x322a1aa50000000a73ed280e72e66a02c72c481a9d29dd00008d1a644a1d515d178903a62423667316bdcb22212a0482d609aa18d9b94994c3eb9f0e43f1b5e2fd0e448029d9e72d800001d8ef851113d09860bf644f150316587eaaeaaaff85c0d6a7509630785e7720001f6827d909419e8e7f1d1812a7f280002b89d608298000b7b0d7a7168000000110a0002e7e59022260cb9fab2c792b628300003190d1a416000016804eeaa55a686f18253000000028287566e3000000006b24a8295e7e498f868dadf792f24807d200005898366000242889ac37e00007f47b31b1a293a26e0002660a494f96a178000680a0eeb82c000000024b468e24459e15da00003d4b499128000000023ac0000001c763af8000000000000000005930000884800046f000006fe28a5b107d2adb27bc23751a00001f600002ab13c2045c6061d80b9103bc9889b08909dba032a80009668faa0000000b57920e75d800052080000718000615e8f093c800073793b46ec80009351fee2919d27269db59aca2c7e147814d58e80000000c98000000000018785e5c000000203e000000027154f671e80009ead6ec9741d205ec826291d63ff28804f28e84978819007400004e0702c00069aa9e43c8016028f95c1ab4a1fb874800025b28e61ea1e349a9000040028e38e8254480c882f33b45fa656130f9a013c683c96c54249d69b1315e216329781c6134e8a52dfe015109e000201400000d80001e150000dd99b0a43226a185c9d498f57b758be69c97ee07749b8848a3bba35ab7890989f42661c2e7631e62000157a01a05844a283570002b01814c000ab7082146556e6000292d42fddb42631baa68616f2a5b400051a2aa80632c681036d3e5d7ac2857b895251b1cad10eaed621b97c8720257a85b1a0a8162c167eb5784a5006d78930f6a00002762bc931d04027b700009ab7ce0c386569f8aa54492370090d26cc0d5e8828b5e31d5af42a397ac2541e3c92593c20b1d80eb4ca8f6306aaf2b1d09180c6a5ceabba07e1e10000ab9aa78aca800066180000000d6c0a98000000260200023d80c4000000022111959c246ad800000000000c7800000000008939f228660b1c4d88b7100004864720000b779db16ad21ba4d0180a39713d8a90c92a9b758ed5ae2c5c3320e3071e6d54750db3a0a7a424ac68c017901aa3ab08af8b3988d627b98c653ca9c2509c000000162a2dd000036298168c803588098e1c92a88aa5310000000066480600005d9923c74f91099eaa49ca14a44e66e1b9b7d506441bc1b6a529a10f52596123f092da98e9ee024f81ac3bc63c65dd8620287245c980251b96492003c01bb82f11f8da3c9022a59834e5a95de62ed2e809c189891c702e399721e2a092b98a5b0baa81ca0bc7d31b1913e999a038136e46b036a7e72710a3f
  | 35 => 0x1ee3926000064c82a292d8000974943047d255f000066a44d693a94f000016da674882140c0000000788c00000000ce9978000a95c000000242e000203b1eb2a41000247835b80000002e262d49f9027000008960b867d1900c1e300005c8889a8f40000ad6691ba82577816228764c82c62b242884678a31c298a13058a40004dd18384ae2268ad72cbe7fe1af6aa30c6e7eb184c21884da33fc7fc837866e2c28893b26ac5e000000036d809000019220000000a0889c6a5520433b592ae0320ccc98b0f1800008c867b800000013828d48127000295f7088000248856099200008ebaa5a4a60f3889547877dda63050aa0d200000006c8e4000001dc900000a20002983000000054c8000000000000009c1247108200000000001e0c8c7889c000000000022980002e70220087950f0000bc492126c2a18500024500001cd40000fb9bb89830794951a95300000001b6c584da529ec65080002c480000eb696e80001836f340001c0f39a000014b93f639a955433b8c3f00000008af00002192d241e611651a1157c900400040e2d8a0001bb022d9e886a699444340000770266659aa50e4629e1895084a41668a5863053a98d22f3e379198003b800000005925dd5628a16544c9338000000033c85429108a18000000235e00026fc468841e0002bea0a48841978286d92400001be8488afbaafa0000000800c0006d500005502de410c9f625f897c668f140e27960663db48e700000000001cca38f08ceab6ac563b21d3405ba4a41d4cc2c00029c0459892b5c9590f0000f6832f1f3600027d256e013c3ee1fcc2b9a98784e0000409800024bd61c63e8930b19ab3e6df800000017064c2149e8b3ad40b7080000000000000286f58900009d31e0f80321119940c0500000007a56a825d4800000014789891d057711c1e2150000585abba4b025720000000000126ea6418bb1fda5a83b1a8b857da46a0001c9a0002d4a000217194b80ca810412d6b39c0a41417270001e3b0000000519800000000007408258a8101e6000057a000000063998e00000dae000024c6c500007bd02f60000000944a41954f000031240009f35edea3b0682994a82090da79832ba6c6851046c67aa9d45dfaee4577e22e4942a3b4431a500e8140691e5d964e280009b103c8ba5e70e0108000116aa6200000001bd18f2000000057140009c5000000005340002addb3b80005651246242c0004ca00006f380008b181d5035072a96aa4d8633acb8000086aa6900001d5000023ba16e00000002679c28a0661d65e0d6ba596abe8a41887c0002e0f000087a315c000000186a44a8a170c44a7c9d52237b54a1f41e0a36e6f32e6c207535a8606b4c80d2bfaa9580b08ed0fc6a6aa146bab800098b933512292486e8e102ab61edcb5e92763cfa5b49b4a0818b50c1
  | 36 => 0x18d800011281aa554176089444e48b2652947d8618979a257af10c597071bac32a118c0002d9482922f46768fdca3697621e79e29920a1206be14325372d0e021e53e037800048c8000a9ac9e60808be01688f9c80c1fc67dcaef02a29e39479803a5e58fd26e886269a181b91008376a64aa5424584c20f9827217796b13b4ad3662f2a1a8658aee17b217a000000000000002e2a5d872a9d13000292aac78000065868aa63251600028000b1a7ea6fdc4df1f0000004712541fb27320001d940001b2c00015b28ee62d1230cec002b0732aef141a5b517145389bed3ab869eb3782dc0b38e4c314640ea6791560d2106e234a29ab2f20027a72daa1e8adb209f273c061269628899087e207dc4da9e266299342a2b0bc837883984230c6d0e5a2592325a6ea172efd9b362d61b48564b820a6a6bc90f842fa001735603d84d9acc8e029941af1c34a99a9b27280704251224023416bf6705586a3a604609f9eec62197ecabe40000bf281281b153d80e121898599402a204b3aec84aeb43090e338a5986d9192c04e12e065a601f900a85489b279249a214840f02ec75cc1781e704927019d643b994a800004a066b0000a764000a4f4000a45000050b1aae000042600000005dce20c18784fc8021717271d0da000000076c03f75ad4000baa1614a30201b99288c273e289e895ae4e5215bff42b94984398221b0802331e1863c18a85b87cd008621f515cb1182245daaf225bb8b1689526e2000238573c064c93296183200c5649b0c080002cb242f05aa749800062b1438b4f02049fbd357000000084218c8ad38b60193935c0f02921b8ea35c1619cb55c98b940002d1cb5b20782fb5bd008bde3749f05ea3a988832db000040c1b8e45baef71a4278e6d28f5c34e22bebb7147697b55423539be73f00e5e57ed00430aa1be96cc00075151e800000006388b1800000000000fd60000cdb3d91eee00000008879066906ad6823f9a7e00016cb0002717ae697fc551940497910fe00000001349db67dba7d470657d83a20000a5d400092782cf95ecbbc9bba50439ca4ea8d092f004e930600000005e465803250fbc0000f6f00000000000bbfa1a8aa400000000002a8a4c280000eaab060142e549f11008af18556a2617392ffd01c88d91129a092a669d93ac2ae9c789110b9e070ac6e5ced580b0189072b40d062f1ad3a0f30762b07922441aa6a61eaa8d4697e41406687800061b526bf82109c028cda19da3eaf90d58355a5ee68c95f0735aa460ff000045d2662aea1d61a98da2264f04b6a5f45d488a8b7a46f942254c035308e2128b8025f67419d1b00013e81cadcbe3cb127e6010eac4a325b281f15c4399d5078872bd666f9fd8737014e76f80b80ce89883c1a4465798b4e68980000001e322cbcb354f9000000004f40c5917c00
  | 37 => 0xb21cff38652b4b061cb39c11b1f95f400009b9c2b0001f9a00000000000984ad89b6331c80006ae1f7446a08b267d04503730abe31a62ec19e253000000000001dd6000028a68828507e247520001d6e6034dc0a2700009d68ac27a4ad046a70836a4e27c660e90320795b9d6c11b4c2081f5875a949300000000000b017618b5fbb98aea2c80000000054c8fd800e00000007e7800065ca2f00000000a6ea5fe6d9a43a52e0f1e516aa365c2a5464ce19044900e9cb4503baa138000a954ca2a5aa9313da67f500020a8398a205652176c3a58c717a682349149eba536800000004b44d1a31a5662bacbc6ad0a0001e4845200001b8ab6052a80000002786ad680003b3a566683800080d8000000000000013192a80cacba5225e47a800060824d0256800054ec6800002a523c1290344b27ac041128200010ca34d800000000001d1d2f215aac3600000002ca000053a0000a4912563540e267ed0000000000016711d825c0362782400056aa027a4e4dda9b400000001b3100017b88c100009ee00003f31fa6b92a2cd0001ce08e5400000029aea9a9b688628000880215c8359872ac151fe62716a679291146ed5dcd73b0982a0bc0002785b2d84995d2360808cb281e1666caa06a348742b2b032f5d71d038fc971031d1efa00005fc5a1282e7ae2b4400000008a585687ea18c0482050664041d64b108ec2daa40c21ce8088f1686422622722e22c3a2d080708630eb562821847c5ac9c289a5a654b98249880000bafa51ca87aab00001b8a665809a38a07300002330000000000007260001e980cb14ea00000000002de22b8197439a400063a988e3435bc04e78000b8e0000000000072a5bf86714000000000099e8000a99e92b7e313c866a9e8457ea8a4a739e240f824c818fa558563a9bc0b6876c1a59e701521adc0001f864e41d3327dcc73b9b8000188982894942c4abb19dc12fa88ca3bc1d266b811a67540009ef92cc5aacb0690e29de1ee947a5d2186427a96fe56294d623eace9340c0000000f900001d0d0c383060000000181860f00008d933f107800000004e697185f48000a29a2ae610842853216b0661cc2e56582063de14d0374186389069b865f8d341470826000291c0000000000017cb80e403936800058810440486016b9328238b89a4a4c09fea173a1a09ec86744c6000000006128f980000d9065a62314e9ae48c5d0dd0c9229b26d51c010a4152acd22f5aaf10002b023e1a52875a2418b250c7ea90131a7cf80007b20000000000000017d61d4164488f122aab30bd480024b4000067e67f830a000244817c80008859be26b5ae821d280000e29abea6d06f293e23a57d10de630301560002bae92189de4a595569c814ed8aa8b7097a59858eb10ef4f78dba1fe991c0001fb29152e8e6f748c56b60c34355c0
  | 38 => 0x1b8824c8000339a3764f7116800001c100009c400019fd0b4067294d0f323b62949000086c6ea5f3c000000000000000000000000117076e800000000005054db28cb137003a89b0000058a0002e2046ba4f4a411e74182d9982cbac2a93b21605ba8d113171f97a61a3a4504846eb6faf2c44e1b7a9ea5cfc0000000a995da641e80000002f3a2fa0000962addb0000c5421787e00001fb69e104fe471147092822cc9dea12468716d2b362c764f9905461e91dca54959a21d0550000000085080000002703b758e9019522e4a4380008b4a996a8e2e568ee88de2381a8200015e0901a32672d019cb35000026aa456b3a880a6ee48400cd000098cc000134292e25d03d869a64f06cf8fe0898112039c1d509605dd40698cc68f800000001999b5ca79c0000000000000013740003ae25f300018cd3ac8126000280d25828e77720aaa000214a20d000000000004b48000a5c08900000000a9740da00027de2e6147c54040008ab000045c80000001eb65e300002e540001ec000000017be000025c3cd233c000059838760745dde396306cb085188d52000000065d9d885b780000000000902555254b00000000000adc16669bf800068180005f0819200008db1b2800000018008fed04600022109a410d4223ca80000216412891ec9fddd4cb4008422a591920001d675be1bec2708000000000042980000002e9825300be77a1e9e6a7c00034a00000002bb0034c0007a0ad38a2f8000000000000019e500000000000000246e6ac21692b02dfa25b0d59c567b0ce1a346e862abee7cc0c5458f0000a8469f49010a22da63fba106237e5502c4aed024427a849789135f6921eb588c8600014eb000049e00011980dac0000ad416c000000023becd90002df59e080008472ba49e9985ead9000010b00008a716d8baf096e3d88ec278e08890002960162c18a7599ed69f20000abf800000013840000000000159e7339e0e21c00001cf208a587eaf4b91844c2ea1bc4ac228309c5aa020ed89b25b88c9c1dd8000b5f9c1a1af98e4000087800000009d999032e000005856eb84ee1150286032062a8f66b0b88a454da61283b07d698f812e6b91c093bf1ffe5af04540000b36087000077d223f2a700000002cfa64928fa74684f60002576000205258b824a808693643ca9c80000d8c9678f7526a5ce200026e000007602539bd4b1108f00000f220000b402bda8f5a338c6245600008b0ad2e43b40009a3288faa508ea3a14000000137a5294f101b698c40000000521000000003b29c200001c5a0246a90d008156ae2137268447397952f49e0473b8a2a9de2aa45e09bfd3d28eb425dab56a1c966077b1bfb63408b41830f266ac05c21c7accd3466cc88458d442451e3500000006598ef48c500000001fb5a056c2c6a21912b8f24e80
  | 39 => 0x2e3a017130c37f0512e140000300860c0008678000786c2d42d9aa9c05508976c7449b635443e0002cdabcba5d4000071a00029caaa61163000297a00023a80002d781a3a370881c0000000e401b30cf42fa80000002ef4711824695fcd7c09901f27ee800082c90ac88b149233406ee334919e90fae5c94691a1642478b5a8c3808d027ff4f32d46418914241a010e1a62982226dd18608ce7154629f0000251e9380ea20001d0e1df87c20c9999707b980c4ee99d6af80a3a408260e81e8afc078907c8ac82706d115370ca000015f9e251de099a323969e5ad0fb0b128000a12a154000105a5b1d8b083a1e6428b1860176262a2ff805c072c819558296470b0f249be924ea1805f88e2c5435e91d297fa00405ca4cf53ce9f308a48000593a25200025cc3dd92226e5a8697f49304112010a1245bb76712c32761000000000006aea0866b02955bc1155886e2a7e44ba20e46900000001aa675d1ed23de52e6aa9a79026b4f5a060ad100001ba65ec131c3dfc5c8344e4d607f00f82d60f1248b13ec1a985041ed800000023d4b08a2fcbbb0000150438258e02745dc00000000fb40a70000000000030a000040d1f048268218134c39a1da800022c13300000000ab915c3812a54000026287871c699e84efa6962c8c00029200000000ba1000098d9d0891dc871b8a17001e6a5fc0000000000025287382ea051a6be000000062f5df00ca8000ae59a1a316199464500009bfdfb8314a19d699645a47404445530c07976a85a2cb60c6740295355e000000000000fd2b5e000101674c40000001b2e65ba364594024378792ba201a2a45412b68a3a0000a83598e4d416bd127182a3d655f90000c320001fc800017ae8019a422c380000001b918cea80527c8c029fae4dca3149f800004d80d01b6b3ba8c36552051a79f91f88fa9fa5a68000046681f0153a94c897c9926b212a4821177c3c505661b187433d1592838081ca82e10803b12a102eec00000008848ea40006f28ee4af48f400000bf242124050000000467632a0adc92c058800000021de000240818c101a92b0a4a65198a848400000002a4213380668a115d48530d142f604b5a6b02f86f3c3ce59920be65b1c081399ed400011990000ecc000236287a908e0001cea0002df24339bc3736088e000135813195cc5ee89c95729bcd6f6921a77380007d72d6e84c958800000009721b838a04bc0581091e5d319b6a01c0003830f6500008dc3aa9d9a20ee84c4dda6deb8da01cad1876d5d0cad86c1a4881c4a72aa0f40004eaa34c0eb8a8610d847600016431df09fa43703dc9e68bd0a59eb9019a1ecbaac80004ea02ba5f9e88543107c482612f4504c1250839a8c7b6c0008258e7d15f1cdb6c407a05a69ee4a229da2a83df5692980000001a306e866f800021fc212a2fb6148
  | 40 => 0x2ea69db86c81c5192e6a824103c3acb434eacdc89f82f73180e350001a665fe00005380cd427a4ac6367189268d18b600014427496e3e5d600aa3dc91862b929da29fa99a31a047800008682e7133228796233b4551c29b8124751800084fa9880e495341dd24684d92302000000072e8c55b4780d096b800090f06a049894e54cb0c6c0000ee81ed28fda2fc0006c6179e4262dc649d19e6ac9a8657e74fd416f8016b70290c8e605d22d85439a039d6502d899032595bc197ae869568ee254a1e1a568a02583f010c97d16ed0e9846a9d580007a98000000000070eaa0b0000000a6100000829daa6102c7001613be7b19983a5c80000001fe46ab14493d3800044fa64e0834ebb0000000a05284800015220001836a0fea4c86500007760000b4095a00000000540a96858d8848598c17a00000001456bd80b08cf104d17e62c35f020001b850050000ae52b488b700009b696ac93eaa900001aea611662900024a8000245800019886dfcfe69b32b7e7a280000001ec250d090f00005a6252a17f00003940f2985db818f49b68852cad297980000102186a378b011aad8a08dfc931a33439216a8b83858d00000000cfc000b6e000068e0ef051a96a274c03520c8a68a00026e1456c2aa2bea52200004228a78886352aab60b802e413598ba3ca0d160f186d9a84af1eb6c1e442ae2d2a59782df6a397f4b5580004d28ea9156681ea9e91da33b282b00002b836e04f50001bd16079822750659c37106d800000007b407e888920092022cf0110048c64d004e86729160000b9148d00000f08e8000012b2000166cb34000013e1694a9cd02a2811f847a8124222494bc155557f97b0dc25a618e55e50d949ae81b87ac4936b3b0f2e93b8b82a6619fa8974cf21c21e3e0d71f1a1e9a87141ca6349fd8cbe08ba397a7a1c182e6a1a29b4431f57093a0000000000024d23b9631671403423fda1f910004107fe901e91d8a501e492c6ab5a76090555b6808a1dcac5805a76290f63b1eaac7c988f1abd42229b01cb2419202335d21668e1a08875e80a05be8bfc42408d857f97b6989ab0066883b87781c1000017e8035930d05926f2074268e00000003299a169d78961bc580000001b771ef8000000000067ec00088e40002ec915a8db242ab41a8820000a480001e7a28e52885d588e31ade57472c460e8ca1574388e73091cc0003fa8000000201a31380007538a286a427340000a780002dd231f55bf3225c4a00022ea3f100f66a0ccef00000004e920e257581688d41c58862400028915080d328c22d254cc0a694ca816a3fc0002c78bc200000c911baa3b9c903d180009ee9d620ab242086f2a72000000037c430f8232ce262b9264200a20f693ac581e2610a79c86ec1119a486fad6920b0c1149b382bc61056a4b4814fe7c9d2d858088e9
  | 41 => 0x26b6a6cb2f78895545a69ca9d08143b664de5de8c9ebc04f989ad29ec2dbaace31103f12e581cc3861da446ca47d3ee9bf903f61ccbbf956e40b041871a26b2465add476b88d46a525bc69767a200013526e1cc88090990b8b2c000af689d1000194a0002bfe000184aaa39e8012f1b617ab823e2e82ac60000000463ae9e1489ec436a08a09868df488f9b650001be15bf119c8f898064390fd030400002d8800000000c200005ba1461a0400008e20002a2a4fe0000000070614980000000cca06b80002eea182a0097b40001b0eacd0000389467028ba3b012fea0c8e515d80000ea00000000bac0ac15d0800051d0c184e1883a22f98d60000000000000061d1414972a0f64ff2874a920d88b9ea48a54d48c0021000032ca6f6a34ceb0adf20ea000000070a5b62000247a23fed1688f51e274041505a02a241c325773b517a8703992a73da5e39840d2207e0000b2589c80002cd172a03d276a00000000ce00000000b31000000016e3000000000000000000000035c0960000036a3ae11479524400002f2043b23567d04dd6235c00079087c63ed8c465599d2d670de362cde5526c85cb0573aa800001fe2000000000000389690d5a217239a12080000002206bba9ee66db863284b9c6c49712ee12411108a982684c88000ba82b5800027800969dc600011a62eb00a80001c1733a00002d90000b248e4aa26a83e00018c20002ac02949d1400028a0000154a450000000000fa78040000000000a96541ea3e0b324dc80460001f1887f8000ad98c8aa0a00005b72ae9af505d6ae1002e5090fda46c29d7107085675b481e7fda1e6718900e6d558da3a0e1fa000000000016c02fc5456bcd8e6da68a35a2f68fac82a41ba9f60a743e300b49d2017e69100d127553771929d1c7e3800034b800000000001678d094d7abe279e0cd700009ca1c900001aa91b46b18b681cf87b26f0a5969f0400000007e41639d6367499a891f1cc3a254b0c4e70eec99c888a30444e31f38d326de00002a79eab38500002c859f60e92e620434bb6b1681d474e2a1c539231211614f4395129a750110081b866022b8ef60000000ad51a14a8b59ca0b9a7265151e4e61b9a60b2a14a24e6070f3fa28414fb82cd39e6dd05ab8ce97e3c6b42ab26b08460f5634108fb34fa24b5140000982c8e8aed1c8574a800087602b6580d6c2b23a55653980000000ca40208b5a37bc00004b25906631fdea4340002148000206a0929dc028268a28d82436e2e00007341d717243552526000000032400007c496d033cd60eb9693b07ef40000000ae82b711057466a86089e300b7b8ca000025de0228c8500000001ef1b0289d00006790354176a0829ae2f301091859adb88634701e680acc000b9617d04132e429bd18f485aaa331d000003801ae04d1164a01228903e2
  | 42 => 0x70000000100aa60400000028c35bd800084128d0ac609d9a0e22fa9ed0200619d012a81400071200002e902444060e1b0000f8a000000000023da000295c0001a2e59f800048fa10000000246fbac980001324a1985087bd82f30bf840e4c8558c0440000a7b947200027620000000000060a67300009db1870000102e04a2cae6509b271ae17c0801ea976c32caa1b90000366a14e6d818f699f962200029d012585fe3372cce42d83f05440da070f27cf3d040f00865b6999585740000e4e492a5685a08000671a82900014a0abbd0e8000045e73d01b427902941d040009f884e800087496540b1008a29fc7490000630e1da2fc261e8e126bc389e58c6df23d69a7ac000571a704791fa481a8a36b7c07270392b0c04f8c157c5181a4f1259541385a8ab295bda4622b65cf8eba505c7eeb6f06fe7ac2efc5d91ab26bba30e102139278809034b20b9072f08046f71de48f4a6c812a9df80dc80001fa54409df997834868861ce2ab8a4ecdca47c02a09c722e08238000b5301a0aa1261c00000000530d2c313d6af92ae0704a725270001f08b7fe5dc000000000000003462d4eadd239291818985f3a9593ef9ed88b1c0003f2a9dc72aec8660426a060f0cb03481c6000001b08cb84720000000410800030f8000af201e8ad0000c63a6c1a92b8c50174138866ea8c15692c64a88cabc3cc20c07c7069a83f90067fd2bb6008911639b90a2a1b2f3c20bae18bbfd4b49389d3d67c17872cf1339b76877294806587af99e07571cd236d0a3028ce8f318521788f211366402a317742332a2348ac1aed56a45d8e8c8380ffca984cf8269973ab3da60d23994de48c274050f8e7885d1d9886b990e24c4f7d7e7e95a41484ba3bc91448f90d9e3051e6a7d000c46480b2c374800000028566c70f70a33c498a5d8e73957800008f16e1631c0001d99b904f003dea945ad400028ca80e8db003faa60a9a0420622195297191b34fcad667aa01e0ae8a7ee5222a7044cd11a4170d8e275e768447a7e63c32d422ab822a87c9951194adef6f04b567051b121ab04c79b6e383452597a42c998a66fc7a4274aef8549137c63a0f5eb8882d1a9d924449ea0b68941cc6000109a13891309700b924fea2f637b20e43132cb6a1bace382b21680002a500dbe82500018f00000000b435c440001e5ea5840000000e76b8d1d4d512a742000006e7290966a2c2b32871225300a08f264f8000b4d02be3234484000000000011545fe8000a9b0094026238e000274aa47c6f300000003d8000000000003fc8000b0280000001aca0000338bba00000001533000295800011823c697cd6aa800027725398809c6e74c80266fa06fc51482b273aef264da67288854c7973a0a5c0189e3301b00a6234c8e460b0f5535d8a3749621f82e9922e25c84302fd557e98e579
  | 43 => 0xc625913fe00012f60000000aba00004ed8000a40037c87f61a600002c5b1082500001b360e8a05e0001a6b9d18000496959c6dd21c676f00001fbc00046961568e99b5f85488c4480a5eab5c2f006591c965cc6a3232121d0a540000570150e000000089899062c6d31166440008dc9b4028368b6019250015c27c2a4bc00000005c6b9e1360526aa715e1585a7bf9164aa89e128a0133b1350000647a24992e224621180005ca941c43d199c5958c1f2dbc07a6e724745cc8000bb6ac122f3955a76e2f242d50a4c99c117809b039081080003a617469ecc00021d4b0bb0707cca18ce1090c0d661429b161eccce50001e2e5002ed426d95c8336145cb7e60ae8ad1c0444080c672deb386a55f5eb9a2c6cb658904a518df20c9d9b0000092ea11a10c8b0279e7e1cb4663293f45822da886ca72e0d818a20002ed87982dae00000000002dfb9b280000000000000000000029ea0000000000110869780000002db40001d5d00010f073100007e605b0a558d1d3058f6c46e046000013940a392c2000280a000157200000000000000000000080155d0310d4b6247d9682e100004b714ac6120702957251d00025beae3800047097380000e17b6092809804da2ae29a74a2d204472e1c67acb1fb09109002a8d4824b728000b6829426b895dca20dfbb7578384946182e53000005a9cb7c6c989d08888000a0f2e2a9c088a238aa7f90200c5a0001c406f2ec0852ca71901497aa8bca0c462d10481d20eaf409251450d8b7553f1f0ab330b22aff2b8f0cfa80150e9cd371f8000a8f10a85ba266852197f63b811cc0001ea424848ba41b12e812ac3d684ea30a6f5972ea896270585c5c45e82e0a29985ac23d811e3780e56ace97fe00280009c69f502ca968e8ac1b2b0001ec904602bf3519e22a7d8000548040aa75846240512bca2c8000959271eb3cae0ca5eee1aa25c2d8000155c63240006dd800015d86f827f056e0aba8963ca800013225488e2000046da632b32e57e143007eb10066c0ea01f48e0acc606c96c80002c2600000004e98318000000009580d24538eb377fc2a400025d60488ff00ed000048718de5608dfe00017683e000000001dcc309000075fae2c27680e23bfa902000047c20600003a780000002190b50e47e10180000001c21000128e77f00006d722149a8aa0a00017cb00016ce4cf1d0f000097ea4de49200000001e5000000005b274100009d10b3494d98680679a6c8fe80001ad80000000000bb09a12ae1a3ee9f00544aae9b67a6721b441d915e523800073a54f817d22ff2b5ade6275a3688331a2a43b9c05590834a71c27fc4309db383d1d483479e3a6d3aa5e8b28ebdb8409024b2a89b32d0a08abdccfe460ce20b80857857c8ab495507553cd86e8164179c158a8bc3e6a33e7f719ce7c300001325be08e
  | 44 => 0x2d0bae0cda8f45cf000049985ca0000e0a07d8d3000000007640000200000067400005605ea200000000001e7c39addf69d4d46e9f4e67c077a8ae0fdac0c8729eb2610c0004aa94db0ad00000001e96a628000633c000b39c0007440000078da401f41da0ac3951e74ec95487b8a985b2a92274549a00000e754c7d4e70000c26000256e45f83bea5bd88a4488d42a38000000022205b182149f727a46e688c600024222688000278246d27fc0006e7a25c30198d86ef808e797118969b6112302c927000000070aa89900004de25196b273420da3421514b8c84a639d20945040000075e6060db000000000000c209ec0d1937e35a00c000016cd799dd5f1d90a0657d1a7828d00002331dcb813261439b2b527fcaad43ffab655deceee207cd1c00000001c3a86b66d009e8272404778a96905d99f59b700000000000902800074e6e96000000005c1ffc2bb057b4dac9a5ba407220ffaa2c18a1fae57f400092a57c4249888810f249437a0000709c2fa78a00000000000000014f2b4800021840001b80000b3a030c0002172b20a5f229c9e0a6a124b02dce7fda9f1b725a82dea5aa81e4a731c5c9f81b1b8f00f54acb98eb1030bec8861c649960f7477e999075c47c83339d785292aae43308f41238c7839dd83e3f60a42a4208da71d28447ee533e96e193022e288882c0f4c0a184801b51bf02dd888746119f19f445f668ea52432e9188afe242cb9aabc06c80f9220e15de5ca09f9584401a6589a98a7f67124ce8cfa093894835c000035e278c99e0a60a7a5bbf8992a4a0ec2a22bada2b8b570d1067c80000000d60a8fa9b0a7e92d06e11d360002da4452d190a801a2461986097b0132a47f14ff991adf16611c4fa0b08fc677a8ea00009960001426aa21c8a1f6a1a800011d285000008b7ab7a68300005948000960993a8efdf2e01323100000e866b116320722d929b95e460000000a31df0625784a8b5922b10001c54379e5790000d0c106851418e27b050804ea5400da64c78d2600022f928c96e5a4d174a01f2a6e55bda628ed9d4f2800313b9d88827be2bf25801c421d1087e3501fc40de9a5c24015196a4884e9ee5220aefa4beb6008edbce1576b03821b8cdaa2e95a862c86c087bba4a0122b12b76968a79f42e275139f9d56663c0002bd0b1505c80000b32416000003e0000000115ad5abbe8a16b738000b092a2109016e4ac2815e38d8c5b0002232110a8099c06a4f3378dce00000004c00a701eb800057f28c98a4188299a8b8c721295b9fc0d25a44d7a600000000000d841e22ddc0fcc610747ab9c7270000990aca2000071b9c88000000241100028e488065785dc95e34d0d56c3a3952a37b4d9880b966e0001ec1b9400000002a4e44108606c780ae3998ede2f70000ac427fa00009588fa000027f99c22b010
  | 45 => 0x3fe20c81a86538eca99900323948c125e1961e722ec5000010aa37aae8819da35858d00008be2cdb9c90d9250217ca15606c70371d9214e99169d70e12169032bab2133406180003e89d589529f7e67a0eda5d5000057a800019228321d69c0d733520a522aa498e1d95607f81ec880e2280fb83443531b7b3300373581948cb6ea5356469c3e2a427ae8fc0c7a9310540649990cbbb963e719890c5b5aa588ee1c39acbc51228462483a90c048e329737fc02450650c4801caa6960d2b36790ec6024914ceb668000b522f14aad077a70c9f6c6ba0c0d91b82eeb5413178d3a1c0000293e693266e558a640a0990b30002a2653ba78a770815a0002f109788000ba713b226b86e6923ccc424a0c4214d9e1031840005b25812282e77c20f2927385880c38b168800000000001658942a7da28e00000001e992d200002a69b483ec8000a389152a910c5eb041eb49e80e50b212ef9000211a24ea3a200029b66e195ba9d42dc41bb4000bbd8e63ba68a0f365a39e7d39088a7980008df8000232950a5d6aaaa6ca6a14ae096f057dd060000000054f827a441c728127d83f458088db7e0c0e485130b6984bf8b422a189f28b14085a1f763fa6041821e667cb2af6af7a46c1c81fa2828288070591d984784125fc8c0a36b25c2736603559a13cab7d26d61601d703cf19d8586a6081ee07d867f10d68ba13df73999366a02e958d12a932d42692087aafc27c0b78ba89b805b0ea2881ccda475b0df685799f772f51321570e644afa3b776c9f7a25a8ed0a7fadf626b00fb062189e4a51fda678c5cc96390e2ba2a94483c18fcb3945b443a97ea51205bc4fa91c7b13a0ca4651c309c5652302ad3478158d621701cae097453c8de81df4c40ffaa8c218063f547e465c912208c93c3ea16a99301c3879dac8a748c9800deca54a1f00001458000b849480b1f1d8245a98d283984cc65702129fe160cae80000961091aae7a41c2c66a1600b2e1c4d241a20bc1204b920000438068c47e8c3ab671ad067b221a85f5825000272c78c00007c7aac9b9cab426bf0dd8055e87a9b99cfa4782edebb1800044d0254bc0a60a207075ebc71e08000210e6ca980831018d775c97de0000ea7bca166500017208a800000001b3c00016626a2861c06f878a00000006b49d544d2ec531c424620000c3d00018564e391f29538000bbed2dea4f0ada574400000000000000000000167000017bc85d80000001eac0000c203e78fde94aade800496b75698b240bd0c66012a5195f50b0211d1faa4d8e840443a4a25642a472a8a6aa1bda9be55cc5ee105a3cc720ed86768dbd234a9832827a1f65c08f5d000290900011d608d94649fb0e2e000114ab5600006eb4000460447e000000008c8ff850d666c62e00008e9ee308bfa2f587c1118a1545930000cf69d91e194
  | 46 => 0x782de029cf800053180007df00004728bef8999d2f285000000021e4190800000000003405216af280000000edb73249069ba00009ab9a0069e5f1004c80009e5815f5a18000000171669fda7a4aa1e21b6380008b84000b0f0ebc3231f6a3ade1c872b2586621132e789c8314750e6017a1a862d2810642e58d4abae8c81c5534802210d88139c260002c6a00021e8904a2303f8a6381b3905e00000000001d3a0000dbc95b1a8f13c69f85e280000001378a4b1b564eb80000159b945e38000bb12a9a3368468795800096c0896bb804648241238a8dedfc9c29cc21e45c8ca8eab242cc15681d5e0cea7629a8b3802b00002cb00000000b9f0000ba325f87ccadc8727acc082000000000f3f0000c82a0ec3328b6516c000296214c87e667cdbea180ad7442b428c4b3800074f22a87e800000000000904e5eba071b700c2d5e89efc11f1b10000000202caaf92361798a9200006db4d98c5364de9854bf9ccc640a26a25f1146000072e70300e85c3932d6fca01e0d7831c2ce228821dad908ce000077b8be6890a27a49cac527de23de2b3a5387bf50c04a4078e0aa0314a48de2c8b2235492380009bbe3fd0000cf95dd0beea7b61587178d5c7770986290218833650c87a42ade3891b28000145e13b1086a7808a6613a91207001b65cb1eb97d4a9c47220a94591a86814901d84ef1f964be01367e6c3f210a8f5205d2cca739d18579b1e1302f0000001806a9ce8000a1cd0407f40e533601be681a0000a16080e9832010a8200009d613e0a475ef280f227c5cd000086aaadf088000003998965af821a0af5c980001a97bc61ee822f236a5b82e178b401c4a32d0de0001e8c38201081770e380002eb21d3af0661846a439e8d0a8d812a28ae9b5a67e014a1fc00345db9f206e95e5a66803d05c7a24a7d98fce1ee659708e557079f443859d0a560002e7452f9494b4893d21311bb47e50bf3af3af2a00023f498f0dd488e269400000000000000b5a8000000281800014d39b5011670f4b3a1a48000736869c94cea5b32e09fb2198e040002d7c7940c7f49c26d87bf15f88ec8158afc2f40ac7162c0b5a1ac157ade0000000014e0000000053088ec000bb00994866d85841c2b6a0fe0ff486922f700010963392bcc513939683e260f5e22e165d40d3f30f04af9b3cb3e3aa0f9416ba3ad03d22ee28399a4695aeb4600a9fb5d023be92e932f7f5973699d83306656e243f912fa0a61c727b8893425a1f424e012e21dbae5e00013681ac103e51bd87c69de8102048b4409e14aea2510288f721d426700008e4d70800aa39905989d4bc290a093f00004c4aeac1c955440000b000002bb83d612260508f4400001daae306868810000a3798ee1b780004128f4247783683b15acda8800000002ea42808000993274e10d119b64e2
  | 47 => 0x4d74a7800099694d8a8f58623642e017b3d571670032100024e691c9c5295c2ece26918dca5d0000b3900444bf2aa08c622347f3aebab3084142558572312a811698e020b278148afbecba23cc0000fa145879b8466262d9e15590c3084f29e22b7a7fb59d89b400000000001ebc4c52a9689d8000361970c04c0542b0d14f048a0000acf2f0c5f303070820e7c676edd80a1206071f21c240d9dc33719dd22a300007e0873a000258fa031a5a000016a75100004ba803c02c8f48707673697bc97a8b9a57c6cbdf8b0001e58776a38a0001ade154a3ec26382609c609be729a1b31ff839eb510000000271300027d6185a3c254e26df6052491273079353096f1a7ac000a3300008b140002230000000282a000160f781800079159c837b9e940b014b0a249c114e8a8f12042b2063309e88c89a5bb0e0ae5700493892c88cb8371bba19f0f1cb6b1f70a1c13d4735c52a6d75c364271abc63ce4e431c03c427600047a4d5129e74bb0b3e23c42842bec534a0d43779ece0de0b5cb98072f844237412c82484a11ae6745800019414fb85f1fc0a5ae49aa7fc000804e92835c85106fd248d2869d28ac12ca6aa7818e9b91dfe18ea562ac8a82781507193c297046c96502000298078520aa3e0967a0080266000190a6f9297f9f403da2f880009128fc8a344331b6da7b66f7e0d800000006d6e3bc61b1dea08b0745000053e8bcc0008c1800056d00001cd800021c9790589400000028aa00000000002e0418b908a571800038186620000123
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863964942300421f3a4ca180210f5d2650c0108dce5328600846d72994300421f3a0ca180210f5d0650c0108dce4328600846d7219430042acb82a6180218d552610c010ccaa5308600863554584300432b29ac21802199549610c010cb6ca9806008659654c0300438d2a26018021c6551300c010e94a49806008749524c03004332a94c3100211ddd56188010ccaa4b0c400843e74d94200421eba6ca10021179cf65080108bae7b28400843e74994200421eba4ca10021179ce65080108bae7328400847571594200421f3a0ca100210f5d065080108bce6328400845d73194200421ebacc8100210fdd5640801087eed2a0400843d76950200421fbb2a8100210f5d954080108baeb318400861e5498c200430eaa4c61002117dd56308010c3ca8b18400861d5458c200422fbb4a610021175da5308010c3cc9298400861d6494c200422fbb2a610021175d95308010c3cc8a98400861d6454c2004317324a4100218b5925208010c9cc7290400864d639482004317322a4100218b5915208010c9cc6a90400864d63548200431b2a4c2100218d5526108010caca73084008655539842004332a94c2100218d9516108010c6aa8b08400865653584200432aa9ac210021999496108010ccaa4b0840087155454f100423abb6a588021c995152c4010e4aa8a9620087465354b10043a2a9aa5880211d5da51840108f2edaa4200855973d5210042b4b96a9080218e5965484010c72caaa4200847976d4e100429cba6a7080215a5cb5384010cb2cb29c20087195494e100432cb2aa708021c69515384010e32a8a9c200847976d4a100429cba6a508021565cf5284010cd2cb29420087295494a10043a4a9ca5080219a5955284010e54a8a9420087295454a10043a529aa508021d254d52840108f2ed28c200863765951100431bb2aa88802195d965344010caecaa9a20087155454d100423b3b6a488021595d65244010ccecb29220086676554910043932a2a488021c95515244010e8ca6a9220087455354910043b1382a4880219954b6044010ec2a5102200876152481100423d3b6a888021565cf5444010ad2e5aa2200853975951100431db2ca8880218ed9554440108f4eda9a200853974d4d10042b4b96a688021565d65344010cb6cb29a20087195494d100432db2aa688021c69515344010e32a8a9a200847a76d49100429cba6a488021565cf5244010ad2eb292200866b659491004394aa4a488021d254e5244010cd6caa92200872a545491004394aa2a488021d294d5244010e92a6a92200876271549100431caa6c2880219654f6144010cd2a5b0a200873154d8510043a8a9ec288021d854b61440108f4ed28a2008761529451004398aa44288021d454e2144010ec2a510a20087315448510043a8a9a4288021d85492144010
  | 1 => 0x3104237bb4a4188211b5da520c410c5cc9290620862d649483104237bb2a4188211b5d9520c410c5cc8a90620862d64548310431d2a4c0188218e552600c410cb2a7300620866a529803104334a94c0188218e951600c410c72a8b00620865a53580310432ca9ac0188219a949600c410cd2a4b00620863954982210432ca9cc1108219a54a60884108f6eab04420863954582210432ca9ac1108219a549608841087ce9b28420843d74d94210422f39eca10821175cf65084108f2e0b28420843d75990210421fbaac8108210fdda540841087aed2a0420843f76550210421ebb2a810821175d66308410c3ca9318420861d5498c210422fbaac610821879516308410c3aa8b18420845f7694c210422ebb4a610821879925308410c3ac9298420845f7654c210422ebb2a610821879915308410c3ac8a98420862e649482104316b24a4108219398e5208410c9ac7290420862e645482104316b22a4108219398d5208410c9ac6a904208565715482104333b2a4210821995952108410d4ac89084208726544842104392aa24210821b158d2108410e8ca6908420874553484210431d2a4c0108218e5526008410cb4a73004208659539802104334a94c0108218e9516008410c72a8b00420865a53580210432ca9ac0108219a9496008410cd2a4b0042086e121580210422f39cc928021175ce649401087ce931ca00843d7498e500430f2a4c7a00218755263d0010c3ca8b1e800861d5458f400422fbb4a7a0021175da53d00108beeca9e800845d7654f400432731ca5a00219358e52d0010c9cc6a96800864d6354b400422f39ecb20021175cf65900108baeb31c800861e5498e400430eaa4c72002117dd56390010c3ca8b1c800861d5458e400422fbb4a720021175da53900108beeca9c800845d7654e400432731ca5200219358e5290010c9cc6a94800864d6354a4004332a94c3200218d5516190010ccaa4b0c800865963942400422f39cca20021175ce65100108dce5328800846d72994400422f398ca20021175cc65100108dce4328800846d72194400429cb82a8200219554e6110010ccaa5308800863654584400432aa9ac220021995496110010c76caa00800863965500400438d29a8020021c654d4010010e54a4a00800872952500400421fbb4a9980210f5da54cc01087eecaa6600843d76553300430f324a7980218759253cc010c3cc8a9e600861d6454f3004317324a5980218b59252cc010c5cc8a96600862d6454b300421f3a6cb180210f5d3658c01087aeb324600843f75592300421fbb4a9180210f5da548c01087eecaa4600843d76552300430f324a71802187592538c010c3cc8a9c600861d6454e3004317324a5180218b592528c010c5cc8a94600862d6454a3004332a94c3180219554d618c010ccaa4b0c60
  | 2 => 0xc621021879526310810c3aa9318840845f7558c420430f2a2c6210218755163108108beed298840845d7694c420422fbb2a621021175d95310810c9cc7290840864d63948420432731aa4210219358d52108108eaeb308840863654984420431aaa4c2210219594e6110810caaa7308840866552984420431b2a2c2210218d5516110810caca6b088408655535844204333292c2210219954961108108f2eb300840863a54980420431caa4c0210219694e6010810cb2a7300840866a529804204334a94c0210218e9516010810c72a8b00840865a53580420432ca9ac0210219a9496010810cd2a4b00840843e74997320421eba4cb990210f9d065cc81087ae832e640843e74996320421eba4cb190210f9d0658c81087ae832c640843e74995320421eba4ca990210f9d0654c81087ae832a640847a70195320423cbaec0990218e553604c810cb2a7b02640866952d81320423cba8c0990218e550604c810cb2a6302640866952181320421f3a4ca190210f5d2650c81087ce8328640843d74194320421fbb4a8190210f5da540c81087eecaa0640843d76550320431b2a4c2190218d552610c810c6ca8b086408635545843204333292c21902199549610c810c74a9300640863954980320432d29cc0190219a94a600c810cd2a5300640863a54580320431caa2c0190219694d600c810cb2a6b00640866a525803204334a92c0190218e5526090410cb2a7304820866952982410423dbaac1208218e5516090410cb2a6b04820866952582410422f39eca20821175cf65104108dce5b28820846d72d94410423cb82ca20821175d66310410c3ca9318820861d5498c410422fbaac620821879516310410c3aa8b18820845f7694c410422ebb4a62082117dd953104108baeca98820846d7598841043172a4c4208218b5526210410c9ca7310820864d539884104237baac4208218b9516210410c5aa8b10820864e535884104326a9ac4208211bdda52104108daed290820864e639484104326b1ca4208211bdd952104108daeca90820864e635484104326b1aa4208218e5526010410cb4a73008208659539804104335294c0208219a54a6010410c74a8b00820863954580410432d29ac0208219654d6010410cd4a4b00820866952580410431caa4c1188219654e608c410cd2a5304620847b75582310431caa2c1188219654d608c410cd2a4b04620843e74d94310421eba6ca188211b9cb650c4108dae5b28620847970594310421ebacc8188210fdd5640c41087eed2a0620843d76950310421fbb2a8188210f5d9540c410c3cc9298620861d6494c310430f322a61882187591530c4108daeb310620862e549883104316aa4c4188219394e620c410c9aa7310620846f7558831043172a2c4188218b551620c410c9ca6b10620864d53588
  | 3 => 0x9153d4810c3cc931ea40861d6498f520430f322c7a90218759163d4810c72c9306a4086596398352042973a6a5290214b5d35294810a9ce7a94a40854d73d4a52042a739ea929021535cf5494810a9ce62a4a40854d7315252042973a6a7290214b5d35394810e1ca929ca40870d5494e52043872a2a729021c35515394810a5ce829ca40852d7414e52042a7398c929021535cc6494810acce2324a40856a7019252042973a0c7290214b5d06394810acce231ca40856a7018e52042b538687290215a5c34394810ad4e121ca4085697090e5204386a1887290214b9d06194810a5ae830ca40854e7318652042a6b98c3290214b9d06094810a5ae8304a40854e7318252042a6b98c129021179cc64548108bae6322a40847a70191520421f3a0c6a90210f5d06354810a5ce9b12a40852d74d8952042a739ec4a9021535cf62548108dcedaa2a40854e73d5152042a6b9ea8a90211b9d85454810a9ce62a2a40854d7315152042373b6a6a90214b9d35354810a5ae9a9aa40870e5494d5204386aa4a6a9021c39515354810e1aa8a9aa40846e7614d52042973a0a6a90214b5d05354810ad0e0b22a40854e7319152042a6b98c8a9021599c46454810ad4e0322a4085687058d52042973a0c6a90214b5d06354810acce231aa40856a7018d52042b538686a90215a5c34354810ad4e121aa4085697090d5204386a1886a90214b9d06154810a5ae830aa40854e7318552042a6b98c2a90214b9d06054810a5ae8302a40854e7318152042a6b98c0a90214b9d01054810a5ae8082a40854e7304152042a6b9820a90210f5da541481087eecaa0a40861e5498c520430eaa4c629021879516314810c3aa8b18a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22a6290218b9526214810c5aa9310a40864e539885204326a9cc4290211bdd95214810c5cc8a90a40862d64548520432731aa4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5cc9310a40862d64988520432731cc4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c74c9300a40863964980520432d31cc0290219658e60148108bce732e840845d73997420422f398cba1021175cc65d08108f4e032e840845e73996420422eb9ccb21021179cc65908108bae632c840847671196420423d380cb21021179ce65508108bae732a840845e73195420422eb98caa10211e9c065508108f2ebb02840863954d81420432ca9ec0a10219a54b60508108f2ea302840863954181420432ca98c0a10219a54860508108bce7b28840845d73d94420422f39cca21021175ce65108108eae2b28840847970594420422f398ca21021175cc65108108ece2328840847a70194420422ebac
  | 4 => 0x5ce430aa80852d72185540428f39cc0aa021475ce605501087eecaa0a80861d5498c540430eaa2c62a0218b5526215010c5aa8b10a80861e6498c540430f322c62a0218b9926215010c9cc7310a80864d639885404317322c42a0219398d6215010c9ac6b10a808655639845404332b14c22a0219698e6015010cb2c7300a80866a629805404334b14c02a0218b95262d4c10c5aa9316a60862e5458b5304316aa2c5a98218b99262d4c10c5ac9316a60862e6458b5304316b22c5a98219958a61d4c10c72c9306a60866962983530428f3a6a729821475d35394c10a9ce5a9ca60854d72d4e530423d384c929821539cb5494c10a9ae5aa4a60854e7215253042a6b90a929821569c36494c10ab4e1324a60861d64192530428f3a0c529821475d06294c10aace2314a60855a7018a530428f3a0c329821475d06194c10a9ce430ca60854d72186530428f3a4c129821475d26094c10a3ce9b1aa60851d74d8d53042a7396c6a9821535cb6354c1087ce8312a60843d74189530421f3a6c0a98210f5d36054c108bcedaa2a60854e72d5153042a6b96a8a9821179d85454c10a9ce42a2a60854d7215153042ad386c8a9821569c26454c10c3ac8322a60855870589530428f3a0c4a9821475d06254c10aace2312a60855a70189530428f3a0c2a9821475d06154c10a9ce430aa60854d72185530428f3a4c0a9821475d26054c10a3ce8082a60851d74041530421ebb4a8298210fdd95414c10c3ca9318a60861d5498c530422fbb2a629821879915314c10c3ac8a98a60862e549885304316aa4c4298219354e6214c10c5ca8b10a60862d545885304326a9ac429821879926314c10c3ac9318a60862e649885304316b24c4298219398e6214c10c5cc8b10a60862d64588530432731ac4298218d5926114c10ccac5308a60863a64980530431cb24c0298219a98a6014c10cd2c5300a60846e729974304236b94cba18211e5c165d0c108dce432e860846d72197430423d380cba18211e5d660d0c10c72a9306860865a53983430432ca9cc1a18218e95160d0c10c72a8b06860865a53583430432ca9ac1a18211b9ca6590c108dae532c8608479705964304237390cb218211b5c86590c108f4e032c860847975982430431d2a4c1218218e5526090c10cb2a7304860863a54582430431caa2c1218219694d6090c10cb2a6b04860846e729954304236b94caa18211b9c86550c108dae432a860847a70195430428e39aa8a1821471d15350c108dce5328860846d729944304237390ca218211b5c86510c108ece2328860847a70194430428eb9ca821821475d25310c10a3eeaa18860851d7550c430430fb2a8621821875954310c10c3ca931ea40861d5498f520430f2a2c7a90218755163d4810c3cc929ea40861d6494f520430f322a7a9021875
  | 5 => 0x853875d09404429c3aa84a0221365cc61501109d2e430a80885e172185404431c32e82a02214e1d54150110c70caa0a80886b06150540443d0a1242a02218759353cc110c3ac829e608863a65592304431c3aac9182211e5da548c110c72c92a4608855a73952304423cbb0a9182218e590548c110a74e929c60886396494e304431cb20a718221c6151438c110c72c9a94608847b7654a304429c3a2a5182218e591528c110ab0e6a9460886b1648863044358b224318221b8589218c11087ce9b2a608843d74d953044272b90c2982211e1d5644c1109e0e2b22608847a7695130442ad39ca8982211e9d8544c110c72c82a2608855a75d8d30442cd3a6c6982214e9d2534c110ab4e729a608847a7614d30442ad3b0a698221969d8534c110ab4e829a608865b6414d304432cb20a698221565c8534c1109b4eda1a608855a75d0d304438c2a68698221369d8434c110ab0ea21a60886996410d30442e8b8886982214e1d1524c110ab0e6a92608855875cc930442ac3aa64982212e5d0614c1109d2e430a60885e172185304432c32e6298221561d5314c110cb0ca98a60886d0614c530443e099242982212e5d2600c110cc8a4b0e408856475487204423d3aec910221365cf64881108f6ecaa4408847a75d8e204425cba6c7102211edd95388110a72e829440885597314a20442b93a8c3102215c1d52188110ec0a490c408843f74595204421e3a2ca9022117dcd6548110ac8ea90a408866465485204423c3aac8902211e1d954481108f0eab1a408847a76149204429cba0a490221565cc5248110972e830a40884d973185204433432e42902219c1962148110bc2e510a40886686548520442b83aa42902219c1952148110ec0ea90a408876365485204437032a4290221d81952148110cc0ca90a40886e3644852044370b224290221d8d512148110ec2a890a40886e3634852044370b1a4290221d8d4d2148110ec2a690a40886e1614802044370b144388221b8d8921c4110ba2e720420885b1748c21044370b144108221b8d892084110c9cc7316a80864d6398b540432731ac5aa0219358d62d5010ccac530ea808659639835404334b14c1aa021479cf5495010a3ae7aa4a80852e72d525404296b96a92a0211e9c26395010a74e1b1ca80853a7098e540430eb18c72a021479cc6295010a3ae6314a8085367118a540429d380c52a021479cc6195010a3ae630ca80852e721865404296b90c32a021479ce6095010a3ae7304a80851e73d91540428eb9ec8aa0214b9cb6455010a5ae5b22a80845e73189540422eb98c4aa0211d9c462550108f4e0312a80845e73d81540429d386c6aa0214e9c26355010c3ac631aa80853870589540428f398c4aa021475cc6255010a6ce2312a80853a70189540428f398c2aa021475cc6155010a
  | 6 => 0x24421f3a4c7a92210f5d263d4910c72e0322a48861f64d8d524430e326c6a922187d906354910c38c831aa4886597018d524431c326c0a92219618f60549108deeca90a48861e6498c524430eb24c629221879916314910c3ac8b18a48863664584524431ab22c2292219598d6114910caac6b08a48843e74184524421eba0c2292218e9916014910c72c8b00a48865a63580524432cb1ac0292219c585601491087ce8300a48843d74180524422f39ecba1221175cf65d0910a3ae72a684884d973983424423c3aac1a122117dcd65909108b8e6b2c848845e73196424422eb98cb212211d1d561909108f0eab04848845f73595424422e39acaa12211edc1655091087ced2a2848851d73951424421e3b2a8a1221179cf65109108bae7b28848847571d94424423cb86ca212210f9d065109108bce6328848845d73194424423b388ca212211e9c0651091087aedaa0848861f5458c424430e2a2c6212211d1d56110910c6ea8b08848863454584424423c3aac0212218ed516010910c70a8b00848843e74d97324421eba6cb99221475d253cc910972e9306648843f74596324421e3a2cb192210f9d0658c91087ae832c648843f74595324421e3a2ca99221365ce60d0510c70a8b0682884b974983314432c29ac198a214b5d052c8510a9ae629642885357414a21442aab98a510a215c9d46088510b62e830442885d1731822144296ba0a490a21535cc5248510972e830242884d973181214423a3b2a890a21591c95448510ac8e4a9a428856675d8921442b3394a490a211d9d85248510a6ae829242885557314921442d2ba0a490a21715cc5248510accec29242886667614921443933a0a490a21595d05248510e4ae829242885257414921443a3398a490a21595cc5248510e8ae629242885457314921443b0b80a490a21591d64248510e4ea921242885e17090921442b23aa8490a21c95514248510ac8eb1924288747538c921442f0b846490a21591d53248510b62e830242885d1731812144352b224210a21b158d2108510c3ea8b1e808861c5458f40442ad39ca920221969956390110cb0eab1c808865a5458e404432c2a2c7202211e5da5390110a74e929c80886596394e404423cbb0a7202219658c5390110e30a6a1c808865963d4a404423dbb2a5202214e1d15290110ab0e6a9480886596354a4044368b1c4320221b458d2190110dc2c490c808845e73d95404422eb9ecaa0221395c86150110a74ebb22808859a73d91404429d3a4a8a0221569ce54501108f4ec2a2808853a76151404431d3b0a8a02214e9cc5450110a72e42a2808863854d8d404423d3b4a6a02214e9d253501108f4ec29a808853a7590d404438c29c86a02212e9d84350110a70ea21a80885b17110d404423c3b2a4a02214e1d15250110ab0e6a92808
  | 7 => 0x720421569ce5490210b32e72a481086596598e408432cb2ac72042196dd56390210cb0eab1c810865a5458e408432c2a2c7204211e5da5390210a74e929c81086596394e408432cb18a7204214e5d74390210e30a6a1c810865963d4a408432cb1aa520421b458d6190210a3ce7aa2810843e76151408426cb9ecaa0421569cf6550210b34e7b22810859a73d5140842d8b8ea8a0421569ce54502108f4ec2a281084ba76151408429d3b0a8a04218e9d85450210a74e62a28108539721514084398b88a8a04218e15363502108f4ed29a810853a7494d408423d3b0a6a04214e9d64350210e30a721a81084ba7610d408429c3a886a0421c694c43502108f4eda92810853874549408429c3ae84a04214e1d542502109b2e630a81084e972185408428eb9ca8204210fdd95410210d62c2a00810851e74d4f308430eb26a7984218759053cc210a3ae929c610861e6494e308430f322a7184218e596648c210c72cab24610863b75592308431c3aac9184211e5da548c210c72c92a4610855a73952308431cb20a9184214e9d2538c210c72c929c61085997494e308431cb20a718421565d6438c210e30a8a1c610863964d4a308431cb22a518421ac591618c210a3ce9a9a610845e7614d308425cba6ca984214e9d3654c2108f4ed2a2610855a73951308423d3b0a8984218e590544c210b34e9b1a610859a74d4d30842e8b8ea6984214e9d2534c2108f4ec29a61084da7614d30842ad3b0a698421969d8534c210ab4e829a610865b6414d308432cb20a698421565c8534c210ea2e229a610855a75d0d308438c2a68698421369d8434c210ab0ea21a61086996410d308438d2a086984211e9db524c210ab0e6a92610855875cc9308425cba0c2984213a5c8614c210a3ae9298610845f7654c3084368b0a6018421365cf6488210ab2e7aa4410853974d4e208429cba0a510421565cc52882108dcec292410847a76d5120842acb9ea8904211e9db5348210a72e9a9a41085e171d49208423d3b0a4904214e5d05248210ab2e629241084ea76149208425cba0c290421365cc6148210dc0c290a410846f765482084333292c210421995496108210dc2c2900410861f5458e544432cb84c72a2219698d60951108bce6312a88845d73189544421fbb2a82a221475ce6415110c3ac9a9ca68863970992534431d322c129a210f9d06254d1087ae8312a68845f7654c534428eba4c629a211e5c365d0d108f0eab06868863b54583434431c2a2c1a1a211e5c36590d108f4e032c868847875582434432da9ac121a219614d6090d108dee4b2a868846c72595434428f39ea8a1a21479d35350d108dce4328868846d72194434430f32a8621a21871954310d108e8eab08868869543584434434ca1cc021a211e1d56010d108bce7326a48845d739935
  | 8 => 0x2530c7108beeca98638861d6454c31c432729ac418e219354d620c710cb4a6b0063886595358031c4296ba0a590e21535cc52c8710a6ae829443885557314a21c42373b0a490e214b5d05248710a9ae629243885647255121c42b2392a690e21785c352487108ecec29243885357414921c42aab98a490e21399d85248710b4ae829243885c57314921c42b33b0a490e21999d85248710e4ce829243885657414921c4392ba0a490e21495d05248710e8ce629243885657314921c43a2b98a490e21515cc5248710ec2e029243885647590921c42b23aa8490e21c95514248710bc6e0a124388564758c921c4316b24a410e219358e52087108deeca90438862d6454821c4326b1aa410e21a95912108710d8ac6908438866a5258021c4334a92c010e21b84856008710c3ca8b1e818861d5458f40c4272b90c2a06218759253cc310c3ac8a9e61884e57218530c4332a90c2906219658e60d5210a3ce7aa4a90861f5458e548432d384c72a421965c26395210cb4c7304a90865963982548428f39ec8aa421179cc62552108bae6312a90843f76550548428eb9cc82a421565ce6015210c3ae7326a70863964983538428f3a6a729c21875935394e10c74e1324a70863970992538430e39ac929c218e9926094e10c72c9304a70851e74d8d538421f3a0c4a9c210f5d06254e108beeca98a70851d7498c538429cba4c029c21479cf54d0e10a3ae929e870865a53983438432ca9cc1a1c218ed5160d0e10c70a8b06870851d73952438428f3a6a721c218e9526090e10c72a9304870865b53582438432c29ac121c21479cf5450e1087cec2a2870851e74d4d438422f3b0a6a1c211b9c86510e108dae4328870851d73950438421fbb2a821c21475d25310e108beeca98870851f7550c438428ebaa8621c21879954310e10c38caa18870869943980438422f39cc9a9421175ce64d4a1087ce931ea50843d7498f528429cba4c1a9421565ce60d4a108deeca90a50861e6498c528430eb24c629421879916314a10c3ac8b18a50863664584528431ab22c2294219598d6114a10caac6b08a50863964980528432cb1cc0294219c5866014a108bce7b2e850845d73d97428422f39ccba1421175ce65d0a10a3ae72a685084d973983428422f398cb21421175cc6590a108bce732a850845d73995428428eb9ca8a1421179cf6510a108bae7b28850845e73194428422eb98ca214210f9d265cca1087ae932e65084b974983328421f3a0cb194210f5d0658ca10a3ae72a683084d973983418428eb9ca8a0c218e5506050610a3ae929e63084b974983318428eba4a698c219654c604c610972e830243084d9731812184352b224210c21b158d2108610dc242b00430851e73d53408430faa2c7a04218715163d0210a3ae72a4810861e5498e408430eaa4c
  | 9 => 0xac4a88601071a544c0300838caa26018041d4945300c020ea2a2980601070d5454f20083932a2a390041c955151c8020e8ca6a8e4010745535472008236bb4a510041565cf5488020ae2e3aa440107195494e200838d2a2a710041c655153880208f2ed29440107315494620083a8a9ca310041cc9515188020e62a8a8c40107525354620083a8a9aa3100418bd965448020c5ecaaa2401064f6594d2008327b2aa690041c35515348020ccecb28a40106676554520083932a2a290041c95515148020e8ca6a8a40107455354520083b1382a2900411e9db5448020ab2e7aa2401057171d51200829cbaca8900418ed965448020c76caaa2401065b6594d200838caa4a69004196d955348020e34a8a9a40107195454d200831caa6c490041ca5536248020e92a7b124010673659452008398aa4a290041d454e5148020ce6caa8a4010732545452008398aa2a290041d494d5148020ea2a6a8a40107625254520083b1392a290041d8d895148020e52a990a401074953c8520083b0a8e4290041ca5512148020e92a690a40105657298754c422f398c4aa621175cc625531087eecaa0a98861d5458c54c4316aa2c42a621879916315310c9cc7310a98864d6398854c4317322c42a6219398d6215310c9ac6b10a9886656298454c432d31ac02a6219658d6015310cd4c4b00a9886696258054c42b2b94c3a9e210f9d06254f1087ae8312a78845f7654c53c430eb22a629e219354d6214f10c3ac9318a78862e6498853c4316b24c429e218b9916214f10c5ac8b10a78864e6358853c4332b14c229e218e9916014f10c72c8b00a78866a6258053c4334b12c029e211b9c865d0f108dae432e878863a5458343c431caa2c1a1e211b9c86590f108dae432c878865a5358243c432ca9ac121e211b9c86550f108dae432a878851c7355143c428e3a2a6a1e211b9c86510f108dae4328878861f6550c43c430eb2a8621e21a550d6110f108bce6322a58845d7319152c421f3a0c6a96210f5d06354b108deeca90a58862d6454852c4326b1aa429621879926314b10c3ac9318a58861e6458c52c430eb22c6296218b5926214b10c9ac7310a5886356498452c432ab1cc2296218e9916014b10c72c8b00a58865a6358052c432cb1ac0296219c9856014b108bce632e858845d7319742c422f398cb21621175cc6590b108bee6b2a858845c7359542c422f398caa1621175cc6550b108bce7b28858845d73d9442c422f398ca21621175cc6510b1087ce832c658843d7419632c428eb98a9a0e214b5c854d071087cec2a2838851d7315141c4296b90a8a0e210fdd95410710c3ca8b18838861d5458c41c43172a2c420e218b5516210710c74a8b0083886395458041c428eba0a798e21535c853cc7108bcec29a638851d7414d31c42a6b90a698e218759
  | 10 => 0x65663944410832ab1ca2208419958a5110420cacc6a888210655635444108333312a220841995895110420c74a9300821063954980410832d29cc0208419654e6010420ce4a3300821067151980410831d2a2c0208418e5516010420cb4a6b00821065953580410833928ac0208419c545601042087ce932e621043d74997310821f3a4cb188410f5d2658c42087ce832a621043d74195310831caa6c0988419654f604c420ce2a3b02621063954181310832ca98c0988419c544604c42087ce9328621043d74994310821fbb4a8188410f5da540c42087eecaa0621043d76550310831b324a2188418d592510c420c6cc8a886210635645443108333312a21884199589510c420c74a9300621063954980310832d29cc0188419c946600c420ce2a3300621063a54580310831caa2c0188419694d600c420cb2a6b006210672515803108338a8ac0188418e55260c8420cb2a7306421063954583210832ca9ac1908419c54560c842087aeb320421043f75590210821ebb4a8108410fdd954084208baeb318421061e5498c210830eaa4c61084117dd56308420c3ca8b18421061d5458c210822ebb4a610841879925308420c3ac9298421045f7654c210830f322a610841875915308420c6cc9288421063564944210832b31ca2108419558e5108420c6cc8a88421063564544210832b31aa2108419558d5108420d4ac89084210726544842108392aa24210841b158d2108420e8ca6908421074553484210831d2a4c0108418e5526008420cb4a73004210659539802108338a8cc0108418e9516008420c72a8b00421065a53580210832ca9ac0108419c9456008420dc242b00421061e5498f400830eaa4c7a00418795163d0020c3aa8b1e801045f7694f400822ebb2a7a00419598e51d0020caac728e801065663547400832ab1aa3a0041175d66390020c3ca931c801061d5498e400822fbaac720041879516390020c3aa8b1c801045d7694e400822fbb2a7200418b5516290020cacc728c801065563946400832b31aa3200419558d5190020cccc4a8c801066562546400832cb1ca1200419354e6210020c5ca8b10801064d535884008333312a220041995895110020c76caa00801063965500400838d29a8020041c654d4010020e64a2a00801073151500400821fbb4a9980410f5da54cc02087eecaa6601043d76553300830f322a7980418759153cc020c6cc928e601063564947300831b322a3980418d59151cc02087aeb324601043f75592300821ebb4a9180410fdd9548c020c3cc929c601061d6494e300830f322a71804187591538c020c9aa6b14601063664946300831ab24a3180418d991518c020c6ac8a8c6010666625463008332b12a3180418e592508c020c5aa9310601062d54588300832729ac41804199989510c020cc
  | 11 => 0x823bbaac2210418d9516110820c6aa8b08841065653584420832aa9ac2210418e5526010820cb4a7300841065953980420831d2a2c0210418e5516010820cb4a6b00841065953580420830f2a4c7a88418755263d4420c3ca8b1ea21061d5458f510830f324a7a88418759253d4420c3cc8a9ea21061d6454f510829b3a6a3288414d5d35194420aace7a8ca21055573d4651082ab39ea928841555cf5494420aace62a4a21055573152510829b3a6a7288414d5d35394420e2ca929ca2107155494e510838b2a2a728841c55515394420a6ce829ca2105357414e51082ab398c928841555cc6494420acce4324a21057270192510829b3a0c7288414d5d06394420acce431ca2105727018e51082b938687288415c5c34394420ae4e121ca2105717090e510838aa1887288414d9d06294420a6ae8314a2105567318a51082aab98c5288411d5d84294420aace6214a2105557310a51082b938085288415c5c04294420a6ce8304a2105357418251082ab398c128841555cc60944208bce6322a21045d73191510821f3a0c6a88410f5d063544208ecedaa2a21055673d5151082aab9ea8a88411d9d85454420aace62a2a21055573151510823b3b6a6a88414d9d35354420a6ae9a9aa2107165494d510838aaa4a6a8841c59515354420e2aa8a9aa2104767614d510829b3a0a6a88414d5d05354420ae0e0b22a2105567319151082aab98c8a8841599c86454420ae4e0322a2105707058d510829b3a0c6a88414d5d06354420acce431aa2105727018d51082b938686a88415c5c34354420ae4e121aa2105717090d510838aa1886a88415c9c24254420ae2e1212a2104767610951082ab39884a8841555cc4254420ae4e0212a21057170109510829b3a0c0a88414d5d06054420aace6302a21055573181510829b3a040a88414d5d02054420aace6102a21055573081510821ebb4a8288410fdd95414420c3ca9318a21061d5498c510830f2a2c6288418755163144208baed298a21061e6494c510830eb24a62884117dd95314420c3cc8a98a21061d6454c510831b2a4c2288418d5526114420caca7308a21065553984510823bbb2a2288418d9915114420c6ac8a88a21065663544510832ab1aa228841179ce65d04208bae732e821045e73996410822eb9ccb20841179cc65504208bae632a821063954d81410832ca9ec0a08419c5476050420c72a83028210659531814108338a88c0a0841179cf65104208bae7b28821045e73994410822eb9cca20841175d66310420c3ca9318821061d5498c410822fbaac620841879516310420c3aa8b18821045f7694c410822ebb4a62084117dd953104208baeca98821062e549884108316aa4c4208419394e6210420c9aa7310821062e545884108316aa2c4208419394d6210420c9aa6b108210
  | 12 => 0xaa0419998961d5020cb2c7306a81067161983540828f39ea92a041475cf5495020a6ce3aa4a81053571d52540829d386c72a0414e9c26395020c3ac631ca81051e7318a540828eb98c52a0414d9c46295020a6ae2314a81051e73186540828eb98c32a0414b9c86195020a74e030ca81051e73982540828eb9cc12a041479cf6455020a3ae7b22a81053671d91540829ab8ec8aa041179cc61550208bae630aa81053a70d8d540829d384c6aa0418758c6355020a3ce6312a81051d73189540829b388c4aa0414d5c46255020a70e0b0aa81051e73185540828eb98c2aa0414b9c86155020a74e030aa81051e73981540828eb9cc0aa0410fdd95415020c3aa9318a81061d5458c540831aaa4c22a0418d5516115020c3cc9318a81061e6458c5408326b1cc42a0418d9926115020cacc7308a81065563984540831b322c22a0419598d6115020caac6b08a81066662584540832d31cc02a0419658e6015020ce4c3300a81067161980540831b2a4c3a98418d55261d4c20c6ca8b0ea61063554587530828f3a6a729841475d35394c20aace3a9ca61055571d4e53082ab38ea929841555c75494c20aace22a4a6105557115253082ad386c929841569c26494c20c3ac8324a61051e7418a530828eba0c529841559c46294c20aaae2314a61051e74186530828eba0c329841539c86194c20ab4e030ca61043e74185530821eba0c2a9841179db5454c20aace3aa2a61055571d51530822f3b0a8a9841559c45454c20aaae22a2a61055a70d9153082ad384c8a9841875906454c20a3ce8312a61051d7418953082ab388c4a9841555c46254c20ab0e0b0aa61051e74185530828eba0c2a9841539c86154c20ab4e030aa61051e74981530828eba4c0a9841479d02054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a61065553584530823b38ccba18411d5c665d0c20c72a9306861065a53983430832ca9cc1a18418e95160d0c20c72a8b06861065a53583430832ca9ac1a18411d9c66590c208eae332c861063a54982430831caa4c1218419654e6090c20c74a8b04861063954582430832d29ac1218419654d6090c208ece232a861047571195430828e39aa8a1841471d15350c208ece3328861047571994430828eb9ca821841475d25310c20a3eeaa18861051d7550c430830fb2a8621841875954310c20c72a9304841065953982420823dbaac1210418e5516090820cb2a6b04841045d7598c420830f2a4c6210418755263108208beeab18841061e5458c420830eaa2c621041175da53108208beeca98841047575984420831b2a4c2210418d5526110820caca730884106555398442
  | 13 => 0x6010d209b2e7306849063854583424822f39cc9a8a41175ce64d452087ce931ea29043d7498f514823bbb2a228a41879926314520c3ac9318a29061e6458c514830eb22c628a418e9916014520c72c8b00a29065a63580514832cb1ac028a41475ce54d05209b2e7306829045f73596414822e39acb20a41179cc65905208bae632c829043e76951414828eb9ca8a0a41179cc65105208bae6328829043d76d50414830faa2c620a41871516310520c5ea8b10829062c54588414831daa2c020a418e1516010520972e9306629043f74596314821e3a2cb18a410f9d0658c52087ae832c629052d7414721482a6b98a390a415a9d460c8520b52e830642905c973183214829aba0a310a41555cc5188520a6ae828a429055573145214825cba0c090a41365cc6048520ac8e2aa2429056675d852148296ba0a290a41535cc5148520b4ae828a42905c57314521482b33b0a290a41999d85148520e4ce828a4290565741452148392ba0a290a41495d05148520e8ce628a42905657314521483a2b98a290a41515cc5148520ec2e028a4290564759052148393aa48290a41785c24148520ac8eaa0a42907255450521482b23ac6290a41d1d4e3148520bc2e118a4290564754c521482d4ba0c090a41725cc6048520d4ac890842906c563484214830faa2c7a02418715163d0120ab4e72a4809065a6558e404832c3aac720241969516390120cb0a8b1c80906596314e404838c29a87202419658f5190120d92c790c80906c9634864048370b0a4320241395c46250120a74ebb22809059a73d91404829d3a4a8a0241569ce54501208f4ec2a2809053a76151404831d3b0a8a02414e9cc5450120a72e22a2809063854d8d404823d3b0a6a02414e9d64350120e30a721a80904ba7610d404829c3a886a02416a5c843501209b2e631280904f17118940482f0b88c4a02418e1974250120a70eaa12809063865509404835431284a02414e1d74150120a70eaa0a80907a141485404830eb26a7982418759053cc120c74cab24609063875592304823cbb4a9182418e592548c120ab4e72a4609047976152304831cb20a9182418e590538c120e30a8a1c609063964d463048354b264318241aa591218c120dc2c290c60904e5711893048274392c898241569ce544c1208f4ec2a260906396415130482ad3aec698241669d3634c120ab4ec29a609065a7614d30482ad3a0a69824196d90534c120cb2c829a60905597114d304826d3b68698241569d7434c120e30a9a1a60904da7610d30482ac3a88698241a6590434c120b92e421a60904b9741893048278b88c498241785c4624c120ab0eb98a6090558754c530483e098a42982412e5d2600c120dc2c390e40905c97390220482d4ba461102419598e61d5020caac730ea81065663587540832ab1ac3
  | 14 => 0xc8a9e61904e57118930c832cb1cc1aa441479cf5495220c3ea8b1ca91065a7098e548832cb84c72a4419698e6095220cb2c7304a91051e73d91548822f398c2aa441175cc615522087eecaa0a91051d7399054882acb9cc02a441479d35394e20c3ac9a9ca71063a70992538831cb84c929c41871cd6494e2087ce830aa71043d74185538822fbb2a629c41479cf54d0e20a3ae929e871065a53983438832ca9cc1a1c418ed5160d0e20c70a8b06871051d73952438831d2a4c121c418e5526090e20a3ce7aa2871043e76151438828eb9ca821c410fdd95410e20a3ae9298871051f7550c438828ebaa8621c41879954310e20d3287300871051d73953428826cb9cc1a1441475ce5450a20c72a8302851047776544518822f39ecba0c41175cf65d06208bce732e831045d73997418828eb9ca9a0c41365ce60d0620a3ae72a2831045e73d94418822eb9eca20c410f9d265cc62087ae932e63104b974983318825cba0c090c41365cc6048620d4ac890843106c563484218837090ac010c41479cf54d0220c3ea8b1e811061c5458f408828eb9ca920441879526390220c3aa931c811055a7395240882ccb9ca920441965966390220cb2cab1c811065b7558e408832c3aac720441969516390220cb0a8b1c81104797694e408829d3a4a7204419658e5390220a72eba1c81106c96358a408832cb1aa320441479cf545022087cec2a281104d973d9540882ad39ecaa0441669cf6450220b34e7aa281105a972d5140882ad39ca8a04411e9d85450220974ec2a2811053a76151408831d3b0a8a04414e9cc5450220e52e42a2811053971151408831c2a6c6a04414e9d25350220a74eb21a81104ba7610d408838d29886a0441365cc62502209e2e2312811053874545408829c3aa82a0441475ce541022087eecaa081106a962500408828eba4a71844187992538c220c3cc8a9c611063b75592308831c3aac9184411e5da548c220c72c92a4611055a73952308831cb20a9184414e9d2538c220c72c929c61105997494e30882acbac8718441c6151438c220d52c8b14611063964546308825cba6ca984414e9d3654c2208f4ed2a2611055a73951308823d3b0a8984418e590544c220b34e9b1a611059a74d4d30882e4b96a6984414e9d2534c2209b4ec29a611055a75d0d308838c2a68698441369d8434c220d32c821a611071a5410d308825cba0c4984413c5c4624c220ab0e6a8a611051d7494c3088364b12601844187d516395120cb2e131ca89065a63582544822f398c2aa241175cc615512087eecaa0a89051d73990544830eb26a729a4117dd95314d20c76a8b06869063854583434832da9ac121a419614d6090d20a3ce7aa2869051e74d4d434823b388ca21a411d5c46510d20c3ccaa18869061c6550c4348346a1ac421a41a650e
  | 15 => 0xda76d51300c34cb26a898061369da544c030d36c92a2601855a76951300c32d3b4a898061169da544c030ab0ed2a2601855a74951300c32db24a898061c6d92544c030cb2c92a2601871864951300c2acb8ca898061369d9544c0309b2ecaa2601869b64551300c26d3b0a898061a6590544c030e32a82a260185d271151300c2e8b88a898061569d8544c030cb4ec2a2601855a74151300c38d3a0a89806196d90544c030e34c82a2601865964151300c38cb20a89806186590544c030ea4e22a2601855971151300c3a8b88a898061545c4544c030ab2eb30a601855b75585300c2cd3a0c298061665d0614c030b94e430a60185c972185300c26d3b6a298061569d9514c030ab0eca8a601855874545300c32db22a29806196591514c030ab6e4a8a601875361545300c3a830aa298061369d8514c030b34e828a601859974145300c2e5390a298061725c8514c0309b4eda0a60184d976d05300c2adbae8298061a6593414c030e34a9a0a601855a75905300c2acbac8298061d4546414c030ab6eaa0a601855875505300c34cb228298061c6951414c030ea2a2a0a60184da76105300c26cbb08298061569d4414c030ab2ea20a60185ca72105300c2e4b908298061569d6214c030ab2eb10a601875151885300c26dbb24298061361d9214c030ab2ea90a601875151485300c26d3b04298061365d8214c030ab4ea10a601855975085300c2cd3a04298061665d0214c030f824210a60185657198b54c822f398c2aa641175cc615532087eecaa0a99061d5458c54c831aaa2c22a641879916315320cacc7308a9906556398454c831b322c22a6419598d6115320caac6b08a9906666258454c832d31ac02a6419658d6015320ce4c2b00a9906716158054c821f3a0c2a9e410f5d06154f208beeca98a79061d6454c53c832aa9ac229e418e95160d0f20c72a8b06879065a5358243c832ca9ac121e411d9c46550f208eae232a879051c7355143c828e3a2a6a1e4187d954310f20c3acaa18879068d4358843c828eb98a9a16414d5c454d0b2087cec2a2859051d7315142c829ab88a8a16410fdd95410b20c3ca8b18859061d5458c42c831b2a2c2216418d5516110b20c74a8b0085906395458042c822f398c8a8e41175cc645472087ce831aa39043d7418d51c823bbb2a228e418d5915114720caac6a88a39045f7359541c822e39acaa0e41179cc65507208bae632a839045e73d9441c822eb9eca20e41591c55448720ac8e2a9a43905e170d4521c82733b0a290e41695d05148720b8ae628a43905647550521c8392aa28290e4178dc14148720c6ac928843906556394421c831ab22a210e419558d5108720d4ac890843906c56348421c8338a8ac010e41b84856008720c3ca8b1e819061d5458f40c8272b88c4a06418759253cc320c3a
  | 16 => 0xc25cba0c090861365cc604843087ce9b28421843d74d94210c333b2a4210861995952108430d4ac890842184d973980210c37090ac010861875ce6494030c70e0b24a01851e73d53400c29d386a9a00614b5c854d0030a6ae22a6801861f5458f400c30e2a2c7a00614e5d250d0030c3ca931c801861d5498e400c2b4b90a9200615c5c45490030cb2cb31c801847b7558e400c32cb2ac72006136dd56390030cb6eab1c801865a5458e400c32c2a2c7200611e5da5390030a74e929c80186596394e400c29cbae8720061965964390030cb2c6a94801865963546400c28f39ea8a00614e9c3545003087cec2a2801852d72151400c29ab88a8a006187d964350030cb4e7b2a801859a73d51400c23d3b0a8a00615a5c85450030ae2e22a280184ba76151400c31db28a8a00616a5c85450030b62e22a2801853a76151400c31d3b0a8a00614e9cc5450030e34e62a2801872a72151400c29cb90a8a0061ca5c85450030a52e42a2801873271151400c29cb88a8a0061cc5c45450030a62e22a2801863854d8d400c38c2a4c6a006156dd56350030cb6cab1a80187185458d400c29d3a4a6a00618ed964350030ab2eb21a801865b6590d400c38d3ac86a0061c65d64350030d36cb21a801871b6590d400c32db2a86a0061c61514350030a70e8a92801871a43549400c31db2e84a0061669cf4250030a70eaa12801863b65509400c394a9284a00614e1d15150030e3486a8a801863b65d05400c2cd39e82a00614e1d54150030c76caa0a801873151505400c21fbb2a82006117dd5631003093eeca18801851f7550c400c34ca1cc0200614e5d25010030e3287280801853b75500400c31c32a8020061a698d4010030c76eab24601869973592300c23cbb4a9180618e592548c030c72c82a4601856972152300c2b8b88a9180611e5da538c030a74e929c60186396494e300c34cb24a718061565d6438c030d32c921c60186996450e300c38c2a287180618e591528c030c72c8a8c601843e74d95300c21eba6ca980612e5d3654c030a74e9b2a601863a74d95300c31cba6ca980611edd5644c0308f4ed2a2601863b64951300c23d3b0a8980618e590544c030ad2e42a2601857171151300c25cba6c6980614e9d2534c030b34e929a60185997494d300c26d3b68698061c6153434c030ab2eb21a60186996490d300c2adbaa8698061a6d91434c030e30a8a1a60184da7610d300c34cb208698061c6950434c030b34e9b2a601859974d95300c32cbaeca98061a69d3654c0309b2e9b2a601869974d95300c24cba6ca98061969db654c030ab4e9b2a601871a74d95300c28d3a6ca98061c65d3654c030ab2e3b2a601865975d91300c2acbacc89806156dd5644c0309b6eab22601865b75591300c34dba2c898061369d8644c030d32c832260184
  | 17 => 0x4618e55263102309b2ed21881184bb7650c408c26dbb2862046166dd94310230d36eca18811859b7550c408c34cb2a86204618e5516210230d3286b10811863954584408c34ca1ac2204610fdd954cc230c72cb326611863975993308c31cb2ac9984618e99354cc230976ed2a6611863965953308c23dbb2a9984618e99154cc230976ecaa6611863965553308c29dbb2a9984618edd954cc230876ecaa6611853976553308c31c3b2a9984618e55162cc230c72a8b0e611865963583544c237390c2aa2611b5c8615513087eecaa0a89847776544514c332b12a228a618b9926214530c5ac9310a29862e64588514c316b22c428a61475ce54d0530a72e12a6829846e72196414c236b90cb20a61361c163905309b0e6b04829851d73951414c29cb84a8a0a614d1c554505309b4e1b1a829861d5418d414c26d39ec0a0a618e55060505308dce4328829846d72194414c26c382c620a61361cd601053087ce832c429843d74196214c26c382c710a61361cd608853087ce832a429843d74195214c21f3a0ca10a610f5d06508530ccaca90842986a564484214c26c39ac010a61b84856008530c3ea8b1e809861c5458f404c26d3acc7a0261969d663d0130cb6a931e80986595498f404c26cb94c7a0261365c663d0130cb4cab1e809865a65d0f404c2cc39a85a0261661cd41d0130a3ae72a4809853970952404c30f2a4c720261875526390130c3ccba1c809843e76151404c28eb9ca8202614e5c2541013087eecaa0809861e65d0c404c31d32a8020261965ce6510130b32e72a0809847b76550404c25dbb2a8202618e9955410130b36e6aa0809853b76550404c31dbb2a8202614edcd5410130e36e6aa0809871954d8c404c31caa4c620261569d46310130cb4ca31880987195418c404c2e4b90c620261745c46310130c74cba18809855a75d0c404c32d32e8620261c69d74310130e32eba18809869a65d0c404c38d32e86202612edd94310130a72eaa18809863a6550c404c32d3288620261a69904310130e32a8218809863954588404c26c39ac420261a6d0d6210130c72a8b0880984d873584404c34da1ac220261879d6648c130d30e1324609861e64d52304c30f322a918261a6993508c130d34c9a04609869a64102304c38caa081182619698e60950308dce430aa81846d72185540c21fbb2a82a0618d5516115030cccc5308a81863664584540c333312c22a061995896115030cd2c5300a81867161980540c237390c8a88611b5c8645443087ce8312a21843d74189510c23bbb2a2288618d5915114430ccac4a88a2184d97098f410c26cb9cc1a08611b9c865504308dae432a821846e72d94410c236b96ca20861365c263104309b2e7300821843f74595210c21e3a2ca908610f9d0654843087ae832a421856472545210
  | 18 => 0x155230a5ce430aa91852d72185548c29d380c2aa4618ed8c6055230a72e4302a91853971181548c21fbb2a82a4619658e6015230c72a9306871863a54583438c31caa2c1a1c618e9516090e30c72a8b04871861d65552438c32cb2cc121c61c69526090e30c3ca8b04871871a54582438c32d2a2c121c61a69516090e30c34a8b04871869954582438c32c2a2c121c618e5536050e30c72a8302871845e76951438c28f3b4a8a1c61879da5450e30a3ae52a2871851d71951438c30f2a6c0a1c61565c24354a3087ce830aa51843d74185528c21ebb4a8294610fdd95414a308deeca90a51863654984528c31aaa4c2294618d9516114a30c6aa8b08a51866552584528c30f2a4c7a1461365c263d0a30c3ca8b1e851861f6550f428c31caa4c1214618e5516090a30c3ecaa1a851863954d81428c31caa0c0a1461a650c6050a308ece3b28851847571d94428c30f2a4c621461875526310a30c3ca8b18851861d5458c428c31b2a4c2214618d5526110a30c6ca8b08851863554584428c31caa4c0214618e9516010a30c72a8b0085185597090d518c21f3a0c4a8c610f5d0625463087aed2a0a31843f76550518c3172a4c428c618b5526214630c5ca8b10a31862d54588518c23bbb2a228c61995895114630c3ca931e83184d97098f418c30f2a2c7a0c6187d9543d0630c72a9304831863954582418c30fb2a86a0c618e5536050630c72a8302831869943181418c237396ca20c611b5cb6510630c3ca9318831861d5498c418c30f2a2c620c61875516310630c5ca9310831862d54988418c3172a2c420c618b5516210630c72a9300831863a54580418c31caa2c020c610f9d265c863087ae932e431863954983218c31caa2c190c610f9d2658863087ae932c431863954982218c31caa2c110c610f9d0654863087ae832a431861e54d8d218c24eba0c690c618795063486309b2e031a431856471549218c2b2392a290c610f9d3650863087ae9b28431843e74994218c21eba4ca10c610f5d6640863087eeab20431843f76950218c21ebb4a810c610fdd9540863087aecaa0431861e5498c218c30eaa4c610c61879516308630c3aa8b18431866765484218c332b2a4210c61a95912108630e4ca8908431872554484218c362b1a4210c618e9526008630c72a9300431863a54580218c31caa2c010c61b84856008630c3ca931e811861d5498f408c30eaa2c7a04618e59654d0230c72a931e81187195498f408c32daa4c7a0461a695263d0230cb2a931e81186995498f408c30caa4c7a04619659563d0230e32a8b1e81186395458b408c29cbae85a04618e55161d0230a72eba0e811861e5498e408c30eaa4c720461879516390230c3ca9318811861e5458c408c24fbb286204618e59654102308f6ecaa0811853b76550408c31dbb2a82
  | 19 => 0x8b1c802069a5458e401032cb1ca720081a658d4390040cb2c6a94802065963546401022f39ecaa0081175cf655004093ae7b2a802051e73d95401030f39ecaa0081875cf6550040c3ec729a80204d973d9540102ad39ecaa0081969cf6550040cb2e7b2a802059a73d9140102ccb9ec8a0081669ce5450040b32e72a2802065b6394d401029dbaa86a0081a6d8d4350040974ec21a802071a5310d4010394a9684a00814e5d64250040b34e621280205997310940102d938884a00816c5c44250040e62a3a0a80205397590540102cd39882a0081665cc4150040b54e420a80205a97210540102cd39ecaa0081665cf6550040c72ebb2a802069a73d95401025cb9ecaa0081a65cf6550040932e7b2a802063a76d95401029d39ecaa0081c69cf6550040a34e7b2a802071973d95401029cb96caa00814e5c76550040c72ebb1a80205397598d401029dbaac6a0081a658c6350040974eda9a80204ba7694d401034db1ca6a00814e9da5350040c74ed29a80205387694d401031db1ca6a0081c6d8e5350040e30c729a80205397294d401029cb8ca6a00812e9d95350040d36c6a9a80204ba7614d401038ca98a6a00816a9c85350040b52e429a80205b27114d40102d8b88a6a00814e5d66250040a76eab12802059a7318940102ccb98c4a00816c9c46250040b62e231280204ba76d49401029d3b2a4a00814e1d95250040a70e6a92802063b635494010395b12a4a0081ca1895250040a76e2a9280204ba7614940102cd398a4a0081665cc5250040b64e229280205b171149401029cbacc2a00814edd56150040b34e630a80205997318540102d5390c2a00816a5c86150040974eda8a802053a76545401029c3b2a2a00814e1cd5150040c76c6a8a802053b725454010399b0aa2a0081cc1855150040974ec28a802059a7314540102ccb98a2a00816a9c85150040b52e428a802053a75c85401029cbae42a0081ca54b2150040a74eb10a8020539758854010398a8c42a00812edd92150040970ec90a8020539754854010394a9242a0081cc5452150040974ec10a80204b976085401029d3a842a00814e5d42150040b34e610a80205997308540103d090842a00819658e60d5230d32c6304a9185a972182548c2d8b88c12a461475cf6295230c3ac7b14a91861d6358a548c28eb98c52a4614d9c46295230a6ae2314a91853a7018a548c28eb9ec32a4618758f6195230c3ac6b0ca91851d73186548c297390c32a4614b5c86195230a74e030ca91861d63982548c297390c12a4614b5c86095230a6ce2304a91853571182548c23b388c4aa4611d5c462552308dce430aa91846d72185548c34cb18c0aa4614e9c26255230a70e0b12a91851d73189548c29b388c4aa4614d5c46255230a74e0312a91853a70985548c29c382c2aa461475cc6
  | 20 => 0x963580525033930ac0292819c58560149408bce732e84a045d73997425024f39ccba1281475ce65d0940974e131e84a051d7314b425029ab88a5a12812e1c161d0940b34e7b0684a049e73983425029d3a8c1a1281595c45290940acae229284a043e7518d425028eb98a4a12814d5c45250940b4ae229284a04ba75181425031d3a8c0a12812e9cc6050940c76a630284a04b971181425023bbb2a228a81995895114540c9cc7310a2a064d63988515032731ac428a819358d6214540cb4c6b00a2a0659635805150335312c028a819a58960145408bce732e82a045d73997415024f39ccba0a81475ce65d0540974e131e82a04b87058b415028eb98a3a0a814b5c851d0540b34e7b0682a049e73983415029d3a8c1a0a81595c85190540acae428a82a043e7518d415028eb98a2a0a814b5c85150540b4ae428a82a04ba75181415031d3a8c0a0a812e9cc6050540c76a630282a04b972181415022f398cb90a81175cc65c8540970e0b2642a04b874583215022f398cb10a81175cc6588540970e0b2442a04b874582215022f398ca90a81175cc654854087ceb32242a049c73591215025c382c890a81179cc65085408bae632842a04b8705902150332b2a4210a81a95912108540d8ac690842a04b874580215037090ac010a81a61d263d0140cb4c7a9e80a069a63d0b4050354b1685a0281a698d42d0140d34c7a0e80a06b161d07405034d31a83a0281a61c26390140c3cc7a9c80a059a73d42405034d31ea1202811d9c46254c408eae2312a62046e721855310236b90c2a988117dd95314c40c9aa6b10a62065553584531032d29cc1a18812edd560d0c40c76eab06862063a70d9543102cd386a6a1881279d85350c40c3eca29a862058d7214d43102cab88a6a18814edd56050c40c76cab0286204767118d521023ab88c6a90814e5c34354840c38c6a1aa42045e73185521022eb98c2a90811bdd95214840c9ac6a90a42066552584521026cb9cc1a10819358e5210840c9ac6a908420666525844210332a92c2210819a54a60108408dce431aa22046d7218d511029cb8686a88818718d43544408bce6312a22045d73189511023bbb2a2288819558d5114440ccac4a88a2204d973983411032ab1ca2208819958a5110440caac6a888220665625444110338a8cc02088117dcd65484408b8e6b2a422045e73195211022eb98ca908810f5d7644844093ae632242204b97019121102b238aa490881591c95148440972e830242204d973181211022f39eca10881175cf6508440972e13204220667654842110332b2a4210881a95912108440d8ac690842204b974980211037090ac01088187dd563d0040d32e0b1e802043d7694f401030eb1ca7a00818758d52d0040c3ac6a8e802043d76952401023cbb4a920081665ce5490040d32e
  | 21 => 0x28eba6c529c81475d06294e40aace2314a7205557118a53902ad380c529c81475d36194e40a3ae830ca72054e7218653902a6b90c329c81569c06194e40a9ce4304a72054d7218253902ab388c129c81555c46094e408ece2312a720475711895390237390c2a9c811b5c86154e40d32c8302a72055a7098953902ac382c4a9c81475d06254e40aace2312a7205557118953902ad380c4a9c81569c26154e40ab0e0b0aa72051d7418553902a7390c2a9c81535c86154e40ab4e030aa7205597218153902acb88c0a9c8117dd95314e40cb4a6b06872061d6554f439031cb2cc1a1c81c694e60d0e40c3ca6b06872071a53583439031d29ac1a1c81a694d60d0e40c34a6b06872069953583439032d29ac121c814e5c34354a408bce630aa52045d73185529022ebb4a62948117dd95314a408deeca90a52065653984529032aa9cc2294819594d6114a40caaa6b08a52066552584529032ca9cc1214819654d6090a40cb2a7b02852065953181429032b29cc2214819554e6110a40caca6b08852065553584429032d29ac0214819654d6010a40a72e1a1aa32045e73189519022eb98c4a8c81175da53146408beeca98a32064e539885190326a9cc428c819394d6214640c9aa6b10a320477765445190332b12a228c819654e6090640cb2a6b04832065953d81419032ca98c0a0c819394e6210640c9aa7310832064e535884190326a9ac420c819694d6010640cb2a6b00832045e73997219022eb9ccb90c819654e60c8640cb2a6b06432045e73996219022eb9ccb10c819654e6088640cb2a6b04432045e73195219022eb98ca90c81275cc6448640972e0322432061f6494d219030e324a690c81591c55248640ac8e4a8a432045e73d94219022eb9eca10c81179ce65086408bae7328432045d7598c219022fbaac610c8117dda53086408baed298432061e6494c219030eb24a610c8117dd953086408baeca98432061e6454c219030eb22a610c8199d952108640ccaca90843206a5644842190362b1a4210c81d194d2108640e8aa6908432065a53980219032ca9cc010c819694d6008640cb2a6b0043206e121580219030eb2cc7a04818759563d0240c3eeab1e812061d6394f409024ebb4a7a04818759653d0240a3eed29e812051d7694f409030ebb4a7a0481275d953d0240c3acaa9e812061d6354b409030eb1aa3a04819659663d0240cb2eb31e81206596558f409026dbb4a7a04819659653d0240cb4c6a9e81204db7654f409032cb2aa7a048156dd953d0240cb6eca9e81205597654f409032ca9ac5a04819654d61d02408beeca98a6a065b53582435025d3acc121a818e9d66090d40972e530486a04b9719824350237bb2a429281995496114940cacc7308a4a065563984525032b31ac2292819558d6114940cb4c6b00a4a065
  | 22 => 0xe81559c46294f40aaae2314a7a05597018a53d02acb86c329e81479d06194f40a9ce430ca7a054d7218653d02acb80c329e811d9c46254f408eae2312a7a046e7218553d0236b90c2a9e81a61916054f40a3ce9312a7a051c7458953d028f3a0c4a9e81559c46254f40aaae2312a7a05597018953d028f3a4c2a9e81471d16154f40a3ce830aa7a054e7218553d02a6b90c2a9e81565c06154f408beeca98a7a065a5358343d022f398c2a9681175cc6154b408baed298a5a045f7654c52d0237bb2a4296819594e6114b40caaa7308a5a06565358452d032aa9ac229681995496114b409b2e730685a065a5398342d032d29ac1a16810f5d663d0b40974e131e85a061e6354f42d030fbb2a7a1681c354d52d0b40c3aa6b0e85a049e7398342d030ea9cc1a1681665ce60d0b40c38c6a9a85a061f6554d42d030e3b2a6a1681c354f6250b40c3aa7b0a85a061d5318142d022ebacc62168117dd56310b408baed29885a045f7654c42d032b29cc2216819554e6110b40caca6b0885a06555358442d0333292c221681995496110b40cb4a730085a06595398042d032d29ac0216819654d6010b40cd2a4b0085a045e7318951d022eb98c4a8e81175da53147408beeca98a3a064e5398851d0326a9cc428e819394d6214740c9aa6b10a3a04777654451d0332b12a228e81365ce60d0740cb4a730683a065a5358341d021ebacc7a0e812e9c263d0740c3cc6a9e83a061f7654f41d030ea9ac5a0e81c554d51d074093ce730683a061d5398341d02ccb9cc1a0e818718d5350740c3ecaa9a83a061c7654d41d030ea9ec4a0e81c554f6150740c3aa630283a045d7598c41d022fbaac620e81175da53107408beeca9883a064e5398841d0326a9cc420e819394d6210740c9aa6b1083a06656294441d0332b12a220e819694e6010740cb2a730083a065a5358041d032ca9ac020e819c54560107408bce732e43a045d7399721d030f322a790e818759153c8740e1aa6a1643a045e7399621d022eb9ccb10e81879915388740c3ac8a9c43a07155350621d022f398ca90e81175cc6548740938e6b2243a04b87059121d030f322a690e81875915348740ac8e2a9243a070d5350921d02b2392a290e81c95095148740e2aa6a0a43a07255250521d032d29ec090e812e5d060487409b2e630243a065a5318121d022f39eca10e81175cf65087408bce732843a045d7399421d022ebacc610e8117dd563087408beed29843a045d7694c21d030f324a610e818759253087408beeca9843a045d7654c21d030f322a610e81875915308740cceca90843a06656548421d0352b224210e81b158d2108740e8ca690843a07455348421d032d29cc010e819654e6008740cb4a6b0043a06595358021d037090ac010e81a65906094e40b92e4304a7205d1711825390
  | 23 => 0x94021a74e830ca010d397418650086ad398c328043565cc61940218f2ec20ca010d5a7310650086acb9883280435a9c84194021ad2e420ca010f26544855008792aa242a8043d194d21540218bce7b22a010c5d73d91500861f3a6c6a80430f5d36354021cceec90aa010e64764855008733b2242a804399d8d2154021ec6e090aa010f6070485500863d3b6a8a8043569cf5454021ab2e7aa2a010c7a7615150086ad398a8a8043565cc5454021a74e9a9aa010d3974d4d500878d2a4a6a8043c65525354021e34a8a9aa010f195454d50087952a642a8043ca5532154021e94a790aa010f32548855008798aa442a8043d494e2154021ea2a710aa010d6b7548550087952a242a8043ca5512154021e94a690aa010d737548550087992a242a8043cc5512154021ea4a690aa010f515348550086f1baa42a8043d8dd52154021ec6ca90aa010f635448550087b12a242a8043e89512154021e44a890aa010f615448550087d0aa242a8043c85512154021ec0a890aa010f635348550087b129a42a8043f094d2154021e84a690aa010f615348550087e0a9a42a8043d054d2154021ab4e7b22a010d5973d9150086ad39cc8a8043565ce6454021c72c8322a010d3a74d8d500869cba6c6a80434e9d26354021a72e931aa010e596318d50086b938c84a80435c5c642540218f4ec212a010d5a7310950086acb9884a80435c9c44254021ae2e2212a010d6a7290550086b4b9482a80431e9d84154021ab4e620aa010d597310550086b539082a80435a5c84154021ec6e290aa010f626148550087b1a0a42a8043d89052154021ec28290aa010f604148550087b1b9242a8043d89892154021ec68490aa010f624248550087b0a1242a8043d81092154021ec6ec90aa010f627648550087b0bb242a8043d81d92154021ec6e890aa010f627448550087b0ba242a8043d81d12154021ec6c890aa010f626448550087b0b2242a8043d81912154021ec6e690aa010f627348550087b0b9a42a8043d81cd2154021ec6c690aa010f626348550087b0b1a42a8043d818d2154021a74e810aa010d397408550086acb9842a8043d8484215402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a6280438759153140219ceec908a010ea6644845008752b224228043c95512114021d8cc6908a010ec56348450087a2a9a42280438e9526014021c72a9300a010e5a53980500872ca9cc028043b848660140218f6eca80a010e3a64540500871cb22a0280439698d5014021cb2c6a80a010f612154050086c6b90c929e81655c46494f40d30c8b04a7a054e7219253d02a6b90c929e81559c46494f40aaae2324a7a055970d8a53d028f3a0c529
  | 24 => 0xb00a810e59635805408735312c02a0439c9856015021c5aa93148210c6f7558a4108716aa2c520843175d66310421c3ca93188210e1d5498c410862fbaac620843879516310421c3aa8b188210e2d5498841087172a2c4208438b55162104218f2eb3008210e3a54980410871caa4c0208431edd56010421c74a8b008210e395458041086aab9ea9108435c5c354884218eaed2944210c7676d5121086aab9ea8908435c5c35448421a6aeb2a24210e3765951210871bb2aa890843c99c95448421e48e4aa24210e3554d892108792aa4a490843595d74248421e4aa9a124210f25549092108792aa28490843595d44248421e4aa82124210dc67310921086e2b988490843789c04248421bc2e02124210e6575d9521087333b6ca90843595d36548421acae1b2a4210d657599121086b3baac89084378dc16448421bc0e0b224210de27019121086f0b80c890843399db5448421bc4e1aa24210de170d5121086b33b6a890843999db5448421ec4e1aa24210d6570d5121087b0b86a890843585c35448421acaeb2a24210da5759512108692baca890843a9d965448421e4ecb2a24210d667655121086b23b2a890843c9dd15448421e4ec8aa24210f246455121086b3b82a890843c9dd55448421d4ecaaa24210f27655512108793bb2a890843c99d95448421e4aecaa24210f24765512108793b82a890843c99c15448421e4ae0aa24210f247055121086733b0a890843599d45448421b4ce82a24210f255415121086f1380a890843785c05448421e4aa9b024210d65759812108792aa4c09084359dd56048421b4ee8b024210da4745812108792aa2c09084371dcd6048421b88e6b024210da67418121086d2ba0c090843c95506048421b8ce63024210dc573181210870f2a4c7a80438755263d4021c3ca8b1ea010e1d5458f5008673bb243a8043a999121d4021d4ac890ea010f26544875008792aa243a8043b198d21d4021d8ac690ea010f2554486500869d3a6a1280434e5d35094021ab4e7a84a010d5973d42500862f39cc928043175ce649402187ce931ca010c3d7498e50086ad39ea928043565cf5494021ab4e62a4a010d5973152500869d3a6a7280434e5d35394021e34a929ca010f195494e5008794aa64328043cc5522194021ad6ea90ca010f295448650086b9baa4328043cc5512194021bc6ea90ca010f637548650087b1aa24328043e89512194021ec2a890ca010fa1544865008790aa24328043d8d4d2194021f84a690ca010d5a73d9250086acb9ec928043569ce6494021ab2e7324a010e3964192500869d3a6c7280434e5d36394021a74e931ca010d397498e500872cb18c7280434e9d06294021a72e8314a010d5a7318a50086acb98c5280431e5d84294021ab4e6214a010d597310a50086b938885280435c5c442
  | 25 => 0x5458c548871caa2c02a443879916315221c9cc6b10a910e4d635885488732b14c22a4439698e6015221cb2c7300a910e6962980548871d322c02a4439698d6015221cb2c6b00a910e6962580548863d384c929c431e5c26494e2187ce9304a710c3d74982538862fbb2a629c43875915314e21cb2a6b00a710cd5731854288678b80c2a1443475cc54d0621a72e02a68310c3e76151418868eb98a8a0c434e5c05450621b4ae5aa28310c7676151418865b3b0a8a0c43655cc5450621b62e02a28310cd5731894188678b80c4a0c430fdd95410621c3ca8b188310e1d5458c41887172a2c420c438b5516210621d2ac6a088310ea562504418871d2a2c020c438e5516010621d6282b008310c5e73992508862eb9cc9284430f9d2639422187ae931ca110c7b76540508871cb22a0284439658d50142218bee6b06a890c5c73583544862f39cc12a243175ce6095121cb6c7b02a890e3b64181544872db18c0aa2439618c605512187eecaa0a890d3870550544871caa2c02a243995896115121cb4c7300a890e69629805448738b0cc02a2438e9916015121cb4c6b00a890e59635805448734b12c02a2439c5856015121a3ae62a68290d39701534148672392c720a43599d46290521b8ae63148290de17018a4148672392c120a43475cc5450521a72e02a28290ccd731894148674b80c4a0a431d9d85450521b2ae62a28290db170151414866ab98c4a0a433c5c06250521b8ae63128290de17018941486733a8c4a0a43999d46250521d8ce63128290ce5731894148762b98c4a0a43315cc6250521dc4e03128290ce5701894148770b80c4a0a43385c06250521c68cba128290ea462d09414873232c84a0a43695d24250521c68caa128290e64655094148793b2a84a0a43c91954250521b4ee0a128290ea542d81414874ab1a8220a43a95894110521d6282b008290ea5649062148753b228310a4317dcd64d41218b8e6b26a090c3f7458f504861e3a2c7a82431edd95014121a70e8a80a090e396454050486ac39aa0282439658d5014121c70e0b20a090e1e6498c504870eb24c628243879916314121c3ac8b18a090e5a63983540872d31ac1aa0439658d60d5021cd4c4b06a810e7261583540869d386a92a0434e5c354950218bce7304a810c5d73982540868f398c32a043475cc6195021a74e030ca810d3970186540868f39ec12a043475cf6095021a3ce7304a810d1d73982540871cb00c12a0434e9c36455021a72e1b22a810c5e73d81540862eb9ec0aa043479cc6155021a3ae630aa810d3a70185540869cb80c2aa043479cf6055021a3ae7b02a810d1e73981540868eb9cc0aa0438e580605502187eecaa0a810e3954980540871caa2c02a0438e9926015021cb4c7300a810e6a62980540873930cc02a0438e9916015021cb4c6
  | 26 => 0x34a94c0290839694d6014841cb2a6b00a420e69525805210732a92c3a10839994961108418f2eb3008420e5a539804210735294c0210839a54a60108418f6eab008420e5a53580421072ca9ac0210839a9496010841cd2a4b008420f0d5394b411078729aa5a0883c354d52d044187aed2a48220c757695241107a329aa520883d154d5290441c3ecb29a8220e1f6554d4110717b2ca4a0883c354e5250441c5ecaa928220f0e535494110786a9aa4a0883c99c55250441caecb29a8220e576554d411078b2a2a6a088399d965250441ccecaa928220f265454941107a329aa4a0883d154d5250441e4ce8a928220f27645494110792a9684a08839394e62d4041c9aa7316a020e4e5358b5010726a9ac5a80839398e52d4041c9ac7296a020e4e6354b5010726b1aa5a8083569cf5094041ab2e7a84a020d6a72d4250106b4b96a1280835a9cb5394041ad2e5a9ca020d6a7214e50106b4b90a728083569cf5294041ab2e7a94a020f4a5394a50107a4a9ca528083d294d5294041e92a6a94a020d5a7314a50106acb98a528083c654f4194041e52a5a0ca020f6152906501069dbaa8328083c654d4194041e52a4a0ca020d737550650107b0a9283280834e9d36394041a74e931ca020e596318e501069d3a0c528083569cc6294041ab2e6314a020d727118a501063cbb08528083569cc4294041ae4e2214a020d717110a50106ad398c328083565cc6194041ad4e430ca020d6972186501062f398c4a8083175cc62540418f4eda9aa020d6a72d4d50106b4b96a6a80831e9d85354041ad4e429aa020d697214d501063d3b6a4a8083569cf5254041ab2e7a92a020f4a5394950107a4a9ca4a8083d294d5254041e92a6a92a020c7a7614950106ad398a4a8083565cc5254041e34a7a0aa020f1953d05501079529682a8083ca54b4154041ea2a720aa020f6152905501069dbaa82a8083c694d4154041e32a6a0aa020f2a525055010794a9282a80835cdd54154041ea2a6a0aa020f615250550106ad39cc8a8083565ce6454041a74e9b1aa020d3a7498d501072cb18c6a80834e1d16254041a74e8312a020d5a7318950106acb98c4a80835c9c462540418f4ec212a020d5a7310950106acb9884a80835c9c44254041ae2e2212a020f337150550106ad39882a8083565cc4154041ad4e420aa020d6972105501062ebb4a62808317dd95314041c9ca7310a020e4d53988501072729ac4280839354d62140418daed290a020e4e639485010726b1ca4280831bdd95214041c9cc6a90a020e4d63548501072d29cc0280839654e6014041cd4a5300a020e6952980501063dbb2a0280839698d5014041cb2c6a80a020e6a625405010734b12a0280839958a61d52218f4e131ca910c797098e548862f39cc12a443175ce609522187eecaa0a910e1d
  | 27 => 0xc0100110050024000001003000c00000b00000040040000048014028019000001800400700280640000060028000006004002800000a000012800801600000100100080020020010008000000000400001b003000000000000200300000000088028006002000800c00000000000040060000018008008001000802c006000ab4e1a9ca7a0e5b5358253d071d3a4c129e838e5d26094f418f4e0312a7a0c797018953d062fbb2a629e831bdd95214b41ab4e7a84a1a0e5963d4250d070f3a4c728683875d263943418bce6312a1a0c5d7318950d063dbb2a0286831e9c06254e418f2e0312a720c5f7654c5390726a9ac429c839654d6014e418f4e031aa520c797018d529062f398c0a9483175cc6054a418deeca90a520e4d635485290734a92c029483179cc62542418bae6312a120c7b76540509072cb1aa0284839a5895014241cb6a6b04a6a0c5f7654c535063d384c7a92831e5c263d49418bce7306a4a0c5d739835250637bb2a4292839698e6014941cb2c7300a4a0e5a63580525072cb1ac029283475cc52d0941a72e029684a0d3675187425064eb98c2a12832e5c06150941d4ac5a1682a0e5963d42505063dbb2a028283539cb5394c41a9ae5a9ca620d5a70d4e53106acb86a729883479d06294c41aace2314a620d5a7018a53106acb80c529883539c86194c41a9ae430ca620d5a7018653106acb80c329883479d36094c41a3ce9304a620e5960182531063d380c4a98831e5c06254c41ab4e1322a620d5970991531068e3a2c4a9883479d06254c41aace2312a620d5a7018953106acb80c4a9883479d36054c41a3ce9302a620e5960181531062fbb2a6298839354e6214c41c9aa6b10a620e5953980531072ca9ac0298839694e60d4841cb2a7306a420e5a53583521072ca9ac1a9083539cf5294841a9ae7a94a420d6a70d4a52106b4b86a5290835a9c35394841ad2e1a9ca420d6a7014e52106b4b80a729083539cc6494841a9ae6324a420d6a7019252106b4b80c9290834b9d06394841acce231ca420d6a7018e52106b4b80c729083539cc6194841a9ae630ca420d6a7018652106b4b80c3290834b9d06094841a9ce6304a420d4d7318252106b3388c1290831e9c063548418f2e031aa420c5e73181521062eb98c0a90831b9db5354841ad4e1a9aa420d6970d4d52106373b0a6a90835a9c05354841ad2e029aa420d2c7458d52106973a0c6a9083599c46354841ad4e031aa420d697018d52106a7398c2a9083535cc6154841ad4e030aa420d697018552106a739882a9083535cc4154841a58e8b02a420d2e7418152106a7398c0a9083535cc6054841acce2302a420c5d7694c521062fbb2a6290839394e6214841c9aa7310a420c6f76548521072731aa4290839358d5214841cb4a7300a420e595398052107
  | 28 => 0x16004003800001a01d0018000000000000001400e001000000c000000002000400200c0040008000001010801c000000006001000a0020000010000002004805400e00100580100200000000000044003003000c0000000018000000005003000400001000000080020000060000000004002005c006007000000001c000001800c002000001000000e0020000044002010006002400a003000001400200200380040000000008028004000007000801000000300000000000000020006001001001001c00000100000080060000030004000002003400a000002003400c00400400000020000088004000000008000000000300080200000020038008016015008800000000000000000060010028008000002002000401c00b000000400c000000000c00000b00180040080020010000000000000800000601b0028004006019001802c00e0040058004000000000800400401000480000060280000020010000001800c02c001001000c00e001000000c0000000008000008004002000400000300300280000010018000004002000001003400400900080120020010038008001002001400a000003800c002003006800400800000100700000000050008000000000000400a0000008000004000005000400200000000280040010018004000008000000000a003000000000c0060000004004003007800c0040030150018000001000002800000d000000001401b000801c054000004800000000d0008024002002000800c000000001000800a0000040008004000000800000200100200000020000060000000000000000000a00100800000160020008004004000000001801400200280040060080050044012002000003001200100100200060000000004004000009002000001500000a40000020020000006001003000400c0040000000006002000800400e00100280480220000010000006002003804800000000100040000010018014018004002000000800c005800c00e000001000400a004002800800600d0038014000003004004402200200100000280000010008004000001000000600c002000c00c0000028014012008000002c00c00000780180000000000030000000003800000401c000000000000300700040000000030004018001002800c00a00200000080020000020038002001002800001000500380300020010038000004005004000400200100500000000020000014000019000000c0040000010030002011000000000000100000000060000000010000000000806c0000020000000042001000000c002002005000c006000000000801200200180680040090078004002002001000403e0120010004002000000000800c0020000048000002002800400200c0008000000000001002401400300000a00000000
  | 29 => 0x8000000001001803401e005001800400200000100000000000000000000010001800000e00000600000000050000000006007004800000c000000801c0000080010014008000000001800000500001140260070008004000000006000000600f000800c00000200000200000030060034006000008800c02e009003000002000300200080000010018034008000001000c00c00300000080180010000014006000001800c00000000000040000030010008002012000002000000000a0008000005001800801a00600180000140000000010004002001000000e00100080000000000050018008000000000c0000000070000000000001803000600300280140080000000014000000003000001c00000000000000000018010000001000803c000003003800002000a0010010006003004000c00000000180000040020018008004002000000400c0020000048000000003000800c006003000001000a008000c000013001800c002000000000c00200000080080060010028028004004005801400a010000000800800c004000c0000110050018000019000001c002004006000c0000040038004002002001000003c000001004000000000200000120030000028002006000000c018010007800403a0040000008006001002000000200c0008000000000000802800200000000000060140008000024001003001c03c0050020000000018000002400c00600580000020110000004036000001801001200000000140020180008000008006001800000000400000080080030000000004008006001401200a0000008008000000000802600100400d400000400000000040000088008010007000800c00000200900000020000000018004007000004802a00f001800801400600380000140000008000004005000000c0280010030000004004000803000200d0008014008004000801c00002700000000000010020018000008000001400202c0000078004000000000400400a004800800600000200000060050000004000009000000c014012002000000000a001000401400d00b000000600e001802000200a0018020006000000000c000000000007c00c003002000c00400700280000000000008000008007004806400200000300180040090008034008007000800000200000000000040020130008000008000003000e000002000c008000006000400c000000000801a0030018000024005003801c0000000118038002000000000000c0020020000006000000002400200300200000100000000000002003000000001200e000800c0000150008000002007008004c014006002800801400f000800000000900000180020040030014004003000000000400500280000060040070004000002001803000000200580540020010000000
  | 30 => 0x2200005b2000000000000003a3ce170898c8a2aa6f6421043c53fb2ba94208000012463843f060c20700bc440431c0000050800100e00008438000163350cc2e01c4b32032400000008122e306eb00004e813bc04800000002be400024dc00012908f7112c2cb36b4ac84200f6806a0f9148c400000003bf8000cc800005951cac02a2a266b20e900fcb8a413406845cc31ccb482834cc019d052c1e840000034b2a2ad5205800001e3cda000332d0ae4394d77239c4ac0cc429c0000ba34118e4d00000b60ee800008a84472a2229d2a6400040a8000139430b066cd043ea400000010a829010440018012002000001000200200080080380000048008006004001802c0080050018000000004000000c0160070000018014025000000000000100180000040020028000000000000001c00000100980300000060018038000006000801c000000000000802000300a00140020000000008006001000001800600a0058000000011001003400000000e00040000080010038000004000000800c002000800800800000000040300010000000036001001802c0000060000024004001007800c01e001002800400e002000801c02401f002002c002000002002c0000000018004000007009000400000a0028018000001000000000200200080140280010000020004001000000001400500000000020240090000000011000800800600300080000040000018004010010007003400200e0000024000002000001c0140040080000000000001003c00a0020008004012001003001c0140210060000000000001800c006001000800401a0010010004002002003800000201f000002000a002005000c0040020028000008007000003401000b002803c0020000000004000008001000c008000008000400a011000000801400000000040020010090038008003005000401e0000000008000008001800801c000002003c00000b00100140020000000014000005005800000a005000000805a00000100240000000040000000000007800401c001000000000000000080000000060000024014002002002400a0010000010006000002000c00200600100240180000000000000003002000401e007002800400a002001800000e0040010004006003000000000001500080280000050000010000001001000400200a000000c0080000048000000001000800000200000000280000030000000004006001800c00800c0008018000003000001800a000000000000200700180080080010018000002003001800400a00b001800c0020010018004002007001000800c00100480380040040000008008000008800801a0030000000002000000000001a00900000040060000078004000009000001000200800000000000090020004004000000000400c002
  | 31 => 0x22a83f501f40000432ee4000000000006070000f35a1dc00000000002c30e661a581bf0000000384c00003c00000000000011c468c1660004018a8817d86db46740000ee027a029c000000083a000000002148dd1a2016d2b2911d000000015c40000000ea50596799000000047700001352ac506144450bbcb363830b0aa94e000380c4230aee0003cd2055153b068a63cd2532ad0f70a48dd70000fcab4550490c8092b38280001c9ca4d0000000105cc5a40f63063b3004f257897a0000e7424e40000000793294a9cc00000000000a610000bf10000ec90000fe10000c2b0a90939800000011904ce44ccab830b00000000a0b800077d42d63100000511a6784960000000000009f9c1800000000003af4f0a0000a34067800000003453738f258000ccf000000000000002b169b902c045c27260002dac4ee45e400023e8d6b800000030003712a94cd001603032138e860000d3b37d40000000d41ae9c99110086b6224103f2a585a64700f5880006ff9f0800006700003e8a000066400000005dd21804ae965cfd280000001bdcf579f006d5139c00023787d20d7d2172cecb6fa64000018f8ab947f40000000f2016d400009d06fd4564351000012f000000000000000000000000121f3a14000406a416000000007a0000269466900000000000fc3800015baaa289f38680002938000188600000000000000000000000000000002e4615f31b4bfb1e10f3d9218ff73c640e5a6b8000005d11247fc0bf1c0800040640000000600290410f0000d360000efd00000002e8800000000002b86f29227a00045d400025e40001a8c000000000000d0fce46a445cbf1aba792b5034800020e9cb4000335800021907540000000062cb6831a4acc216cb8e80000002aee0001f8478b0000a71053cdaa8000c5700009e6081862000000002aa80003f42159201c402824400000000d500f4000419249a00000000c2094bb0741df0578000000000043c00000312000463c8dc0000000000000042f605f258070c2bc00001ec49ee9f280002cd220d1c641160fcce9f1ec03db0000715445cfd03f0302a800000016f079c00000000000000234c00000009df471111647e82c005d491f134871615d26a900004a795fd1f1137461d352cf711fe80000000c912b82000266876f2e0800039480001afcd5c20c84793591015bfc40000000000187c4300dbc0003f4686c28068bf000060b36100003440bce3bcc5a744fc000313a3d98ca8c3a000000000000000254d301fe29482a38c1715b90ff1d381b91b646143a4107201b0ff01ed4ea80fb446505b0211170caba42ccec035027be06e851321a83ff0f0267047f0d5707664580e240961f6c67a0000d7b350000011e0b7933c4d763fb1001be0c0000c584e12a0d0bec8888c83c503870000af74838
  | 32 => 0xc0000aa80002c700003eb8efb368800000000003e42000000000045504220000f363dee0002d90000000104217e04fb1c7c000274c7440000cfc47e07430000c8f07e8b6130e4d6e03f09fd47202f816402ee00005da8000401c3b451c3d80f6da74502bb70a9853dcab96276084217d027d02e07393a8478d2b8e474242c42d2bb2c55388c0000000fa7000066000000000dd8000472c000304b0c70000000326c8b88b189e4304ce93312505a462d0be01668b63258981c7144f90000635075c1c00000f788000cd10000000371c00044f113e0366f8cb5f88fe22451580484431205047b1ad0a022b484c036706d84470e340f790d11594de6000093780004fc000008b3c6075902ac7122b8a98e074edfe46380000000c4d420d093b4780001a242d6a7d4bd6015cd4922705602a62000417400012f8f8eae411240eec0002e740000000bcd0e640001bed122000017121648382de81010000000297400014ce00000004cea534000000111a38146fa43847ee479081836bc610000039d800110726bc5ba0768cf02d8cf6ea1e44578b78f37052281b0bd42d22e3477b118cd871fa912016c000f31c492112a085f1bf2891b08850a3fb80672a526c829b030db3b82161fdc9a8092472a1c00be604c0aee250c67f3248a228958f8f8d710363254ca11b9c02e4418b698c4892400000003c689be0bb0599353c0000fd80000000f56000000032f800000000002784266133000017b810408804d400003f000000000b500000a5c0000000000000095d181423b20b03b2c6480409bc0280459c44100000000000000161c8060000f452e209a942587df3cf8000000073500000001db90991ed8ae34640b0110bcd2100487141f681e213791382cfc2af2c5c7febdbc38a3e3412cb8d8aa939a6b4a21c83cc0000e1809fc60f1fcca19130c73111ac0da080e000411ab7280c4fa4064c4bd125c5510000cb51098000396823e1c14f37bffc000453102b27bcb051e54cff0000fd3c1c4fa32d0cdee15d0a0a1e2010c2e0040f45bc4768000e5c00000000000000372c21a1c28512a32c00016a40000e5811f0ce90a70cb49f22d088fb47b465b283906647f8000000000000003d60000000158c00012fc00000011b400001118000000122cdcd00000b520b8cc300000001d706d6432830f124d0e01888af82f6c0000f64bea3f28329264ad1441650a12c4409401a85fb000018b95cab8c9870ee80000000170857238083a12d4a1ada8990d80000f9f0000a76000000007060000000d12248ef9930f4c400ed2b5c800112300010c50000fde20a800000000000f7c00017f8889167c00000000001750a44800038200000001ab800037ac000179cf2fbd8455c0e74a8900000003da4a551760b1a000062f0282f22c194898000000000000000000000
  | 33 => 0xc00000001e580000000000075600040022f00000000000000000000000fecdb300000000000000199cea60000f3504b8c310000041054d02f0000a651da442a1504d750148ace24f6da839a40000000fc80000a0d955c000481264d00000001f6000007701ec00007fb000020033d4f6e279cb2f9b9400016580000988573c66c2ab24f800022807110000000136a3ee24bc48d40ea8161b8c1d40000d0700011ae43103ce044800036e8fad0000fde81c82331f42abe00005ce0f54f67370c0001be40000060f3b010c7c815f0b580000d393f9475544c800048cc40a000086f27480000000a9734a4bc40000418ac28cb603b200000000e40f002242f28d79041c156162a0c0360c85d0524fb225b4f8b150d1f32e5ca3997b0e7c00006ff0000be184e40003e6000034d00001df89050000bda4584b8a434c5ea278c0000634e6d2fa47eb15087f7800094000008b539ecf9186a41d90a5074b0ad44c72d2400013c8a79000000000000000ff8c3f14105dfc704ef600004980a5523200000002f18f12000056f0a3499921e8783028c0001e4000000003e52b744d70220ea0379400034441a1b5a8b670fa80003f0ca7517280001d94bed36ac7893108b028000c861990ee020ac9b03374470000000009180000318348095065d2fa00dd05ecd53249c083c484a680000b37000036c35c8fd7040cef000010df00005c6000013da0cc73315f4b6e80000001c4c7ac2bc44a499b8fd20000afe1cbcc592ddacd20e949c71f36fc609ba7813ff000003a072c0000cde0a680000000aa58000dfa0000d99004400038f06f49d6829b2db2469000032810700000000000470c0002db0198b4f800020ec0000b3221e4368000427ce2119481583f54dfc3f7087b0704c4710e403006bd07c114809c33dc192000000000002cc105105e000034437100003b1d03080010890000000435800025f4000343c1912a80aab3608aed8000e450b0ab7600000000234adc208000030a8129272c00034330773a74b690cf8cda02cac8030d400019c8a0c817119a09610c8427000031780131fbce9b41d2a458e0400000000000ea46a4394d11ea8e000035483e000000000000000252200018ec25e4094fdd0000f80800000048188ce00003c211b80320940f2b104c48900010880000ff9ab40a7f0000000000000024da6ac21303ad2f0c8810000000145400028dc000000000000000000000afd000000000003b20000f4ab83c00000000000000a0a8000584301800000011b23e04cba0f707610000f53000000000001fa871800000008de80007fe15306ec0000ae4991853a23940002cca0002b18000000058d8000a6580007dd0000000000000000002cf3e8823200004a000000000000000000000000000002b5400000000000000000000000025540002a9
  | 34 => 0xa000000000000000000245cee30c680002bac000000106c47387f51c40b3500001b50001037ac7461e000000023f0914387c9258428000000110c00009450000000465afbe294000008b4000000074743d45d1100cf792aba000278800038dc0001d7c00003600000000d421cdd02c03d01d30000f73818c000000000000010588000000000019800008cc405c7bf36800000000ade3df4ba60000ab62d920000000000000000000000d23b38ba80454686251090821f4b21339c8c93ba8ed10c74c5d35c03d00b701e58554ec83a3004243e51d03d48e4929770cc33e0a130438d51036308b21f09d900005403b7ef4d8782e6833e2a9000000000000377000000010dccf300002300854ef4389121513662b827a40cc46d4f7fa8fc30927d80fdb6fa000000026e39e8d240000000000000001f0000000000000000003afee960000ea4000087b8000581000000000000000000fae93d008b8000a9e00010b730140003f12b54000016601c0b77c65c0001bc8d1842b057500010b80000087800028432407c51ca505b00000003d543da292c00027c0b4e00000000000000226c3f21ca00000da400000000000000000000000021ea0000000471000000038590ac84e855e1d4d055800000021160003e6cf7533f900d27000003188efe0000388253c00026290860cb118a3fac7a317e42a3384800004c63d239800002714000299c00000005418000e8844f408ec40011dc6ccb77000119600000012478497800113b1f94c88223249410200030bf000046940000bec0003c14d7847a8000133600011dc00000000002da23cb000037f0000000097c2bab678519237c00000004b6000083935941ae0000000000000000000a10000000000000000011f900000003796000235c613099cd09009c50c000000000007ed000000000000000000edc0000421000016200005b39e9053c3b2c4a195a800000000003a8c3fc34b0c543d2114202f4ab224a00ef3238a0113d8114000014d460c63d229a0aa1c5d11b00004682831186224ce1b2c22e4124e818080007252d709860d8c601440c25d2d4ee700efcf1786f48c52df804e295904c4388854039ca5e000062d000000046e8f271138d8941a4000186477f27b4e3e163052e1284080424b19daf80fbd39e0e4823d476c34a8630286d14d052d22b2ed8f5f024cc1414a4000483049917f0000000020300000000cc82ae34648bb33d08eb423ae4400010f41e789bb25644b00306ffd000000018cc0002ee661a1408000459888e9da800000000000000ad135468f4027af952dee80f16bd1642b5cb2511987d500000000000c46134514f00001d100004420ddefe800000000000000000000015c102d93ac000000104e28c88ff136894280006d300000002d1400013fe0003e681902d1c17748a45a
  | 35 => 0x853ac89d6aaeae283a606783ebec4b36831d82ded1f432a42e31180492000081fb01c67c253118246fc56b0ec05a800002fe3954ea9153867633ec80240548f040820003e300004834989000057e092c0000000f3c80008752134b9c0000c50bc7800031b800000000df0000000000000028740000000959800000000007f10000000088ca4f31a84290a24c524288c8337b45f0230c2fd23eefcb3210f4e414c0000d9c009166a097111a9da3a106a394c042e2c583520000b4c27786c91042cd51548a4647b86ed376410d000000034802454594f8e367a0000d6c01a21c40002dc4000000053e19402dd0000fcd41ad16308bc83e3c58b518cd4e6500004d80fbcd9f00000000000c5fb4e0bdf23548d68000000134000000d4bcf000062c425ccef25880003d0117d07e45e84348c18344cb4cbcfc6a225287ae47185d929a42cac0a034f43781cfa404eff2a1093c844d21c178f1b48b2909122a600000000c080001d61820bc51994488000000030f2000102c0000000b9800004b22124b1e11f91692e4cd5943703b1c0e8af200647943ab0af3bcba46f47b0484000114e356800020dc54d138efcb9d3c32b000000024707802e3cdd33cb0000026832f48a87423f6cd3c1f66bae0a88b0598a2c1031d006f297c5e124280a4800018a2a3a5d61ff000030c000036b22611a3000034187b928a83cb840052f48444bb2af25de243c34226902e8138c96913047d49792a9f00000b5800089400011411c1a0001fa0446000048a000000028a40000000642000013d42748630000000262c4820000dc000000000000ae01894fff80000001f4c12a00000003cccf5c000082527c624c3518a3c48645c0402600013d4ebb259a0d4c0a21fc0bcc0b9296107d03ac6950db4199beb08302b581430de4980395c2fa05f80004350d02000000000002b2a9311d73bdc9001a480000008d1a00008ee13aed7140f00002c3c6433230000000000045e8eba0ef000000005182f251be358caad1dc0d7f346e65e0a3c6582d989a3c3e913a05003f7140c0e605b8e6f00000fb80000001a08000406c9c1000041d80003612dc800000005440000000452c0000000acb38e0000191000013f68920c510fe137000043a503e036c90c2f4c8d632b49f340508533e86757413ebd5800031b22340002bca0000000448051400026c508139f445d833c9833dd8b101e94000436ccc10126c5c000000044dc0000fe800000006f12f50f0b451000000001fb8000490000037831048694084db105a915e1648000000000000003133a6408400002174028e3d228cb6200011570000d980000ad41df0b7caf9c229027895812a501d0000cb424e018f39380001186000000000000007e700000001b7c0000000a7a00007d6000015c4324f89b044ddf151c00000000003c
  | 36 => 0xac4d01000000000000003160d7280004e4000000037280000000ed7000000037580000001198000107535bc000056c00000000002ceeb0698e8eb814680000000f828c780fab232a4736543d41ffd17400010272cc0581ac1800000000001a50000354af92101cdb018966c41a448a607406e105802883690dc20000000092117200805c9000055a8000f51297a1e7013a355000000024189418000000306400000000000346f9e42a51363146dac168000032c0ffe09c04043d40000419e000000000039fc00000008190cec000390c5b128c4b553c4506a0000c040000000000072010f80002d44d931150b231c6c000000000003650c1b6401483b945be072c84b1404f8907c49b416900c3c0dcbd829e0fa0c2685f72604a302bf20003f10b0199b0e042f648ac28e2f3d1520c2ec6a07a209c4f0e0000e3e8b44c5b46ce00a22ccbd22538562289c78c356c3a8bbd4ca73e011b11174c65047000000000064438000000000035b5087000049d2abe00007fca37c300000119cfa11a94000000000000000000000efc000000000002d700003951be60003e1287f418e00045251ef37f3189442c762012c4ae05d0d0530711ca2654da7000008c23409bc1a280003b6e3360000a810000cb300011871c1600029ad033a36d04110d07d104dcfdf0aae8cf3294000000021909d46a4b3a073a2cb90573d3420c18a63502194a491154a870bc44531a40a984478d1602dc0000000000000000046dc00014e000000000000000e5d00000000000db404400a286ec00022c8d731554af8c2c00f50a78d2d0000000000047201a000038046570ab0e3b404c0438000000000029f000036b346224e423c1ad387032126700001a00c75008d111000000037b00002b9031dc30c0000000000020a00000008a73ef0f9bb498000000010502e8767000000000000002a42b600000ec6406901f8cd080b128800003cf0b5000121d0000000000007b000030c1dd474a155813f409841d3c5d140000049f11567bb069c1a30618aa438208f90af89fe2b04637000096f04d4000413ae733d0c0002b230c119ec00033648672ee846cae144af060424f478814a22c0000000120b00006120836ff30000132320800040c41b8418c231051000032800000000000159c0001740000000088e2c3a2e148b8dd12ba319500000000000c9c000000000000001aa000000000001f9800023a0a7c2a880000000b0d80006d01584f7f044400036200000bd06a70000000000060600851de07a434a280c0000000d3203e90350000fa000008e217202c106980000ff4acf2d4018900000000000e0023100000000874000005e000039f163c8e1000018400000003d66f74bd08b6e144074626fc000168d20304cc92215911881920f1cacbb1d1415a73f21126f300011
  | 37 => 0x37b00007a8324d17f3de09a600000002b0cbf43e404dd9b2c00000000000000a9a117c00000000000aaa00014180000000ecf00000001a270318680ee213a8b6f18a8d9100011020001210000000000008523530f942fb00002a3c98d180c00028f8ead3c8800000002442dd0b4abdec71e1af079740c06363f8ac940de600000000002f9000000011f5000104032a11f224d84491b5071d0000ebe26d4000240e22847ec00014ae0d70000000048800016fc0000000000000000000002f20000d7d0344c640000000058448f1fd266847740004540f2600001f00d7801c357c15a8d2407a18349a48000000078c00024fc1e2800122847dc91a0296000259112700004c4000000000000000000da30134c8145ece2a1b180001810b0d2c3812800003e10000caf0098000121d22737d01dc9c11095c7849f9800051e0000e951cf08f64242d6711f092c0da000000000002ce00000c3800026500003ffa80d03ed000317c9bd887400047240000000000196400033940000000000418a00041e834634387b31f804ed000000028840002098fc92bf600045a0ed60000d5e00000a62c208c10798af314d8ce42b6a386c5b804a04a600035b0ad5a7a102eb0f8faf1768a3934e8bb727c45984232e6e0d807f00a4d203ab1e0a000ec5e521b91eb3e5c00019303f927e2f5921b4066068a0002a142eb351c7cd228467e432c2122980ae23dead27aaec05403f8ccc2f5c000018405624b626c00000000000e750000c1b2e38000000020f1b9000016b200000000001c2701ea1f878f1244a593daa7f94520ca400000001d00ae1319800025f80001b889de8000f321af8aae00000000000a9cc5f0749269c000000000000002132ad03d72658e3d9eac0000000b9f0000000307c0004004a93bd6a00000005008000b0fb7880001e08ae525440da931200000000001ed0d4113a40a80e5d20200007c706c47bc0000000000000019bcba10bb4de303b8b913e283e80928cdb06f00000000000000000040b8ebf2da800000006a6000000032f000000000e01dd0840207cee60000000168400009ccf2f0efa9dd39b05cb20d40004214bf9000008f000000041de0003f362682e630bf000000035112304374000059a69b2b0800000000003d050fd000000000006ea0000cbd0000000265c52b07d80003b160000000000000000000003e30000745000000015d8bbd18d0000000008100009660000000000056280000002688f152d3ca620620aec1670136133c6474184c011eb457319cc1a53a0400004c219f3f0704b2ea80000fd00c13130af60000ad9409e93b3e58183000000043a059e00011e80724675084e0000000dc92942000000000005f43eda9280003d26ad68000410000000037cc0000c1600023082e23cd00001ac0000000119943ac1670
  | 38 => 0x1ee826b0000e974240a57274000043b0a6f00004952cc4d0b0d7400022b81c29b4800032dc0000000000428c495bb684229a80c6f00003a72a4a55410f03023d28a1e478113524d40c83078b3c1d78811282415fc2f40a91a786fe0c345ef3bbd010182466620f07f600000e3338899b04fadb9025a97321a0df944e51ac285c4d8a8d841e35840ca44d09f74858698032cf0439ac5fd00002900850154c88c0002f546e900001c300002550000dde10d8a2e0000e4a006cb0780005c11b1c70301e432329a87523360000000000000000002c1c81d1dc8000385081d9a1d04800000001e14000359903925b02d62d6c03629f44404254b270ea6e64000099f42c4d7a8d991b280000000b529b0800000000010b22f791a32a3506418286620d58e353ea05ad46d8be1081101e2fd51301f3cfb502905261e7d0792a36fed0000abd000044fb274ab020204cb00002c6b4349cc80000000000e8e00000000000ab7000000000002e70000926007400008d4822000005b05942b7c5551e732a8da128d44b10738fea2cbc1e503f4e0b37fcc483541032add4bcc193858516fabc7000000010fc34e00dc0000309213011af889b78c63bc30c0f38249bd24a4304800000016e46ce00000001fe0000000000030dcf6642908ab00000000ba8000166816380000001d20000238000000007a7000000000000000000e462434b31b7500003604bfa00000001e1c0001adc8a4375400019687af20a40001e44e421859062198c0001ea8bc2481c3c10d1c9540094f70ab7e59b19540001b6905aa9b8bff1acc522076058600004803df066d422600036dc000162044c314c000454813135ac00039a200000e91a71134fb401b4c160000aaf4238c56072800019ac00000004110000e2e07bcc8536a43af06c0f580000d8646c00000000000189af443ce4b9a00000000000f0324740000a1c0000000fd436b8000000000000010bb00011d61bbc00038c40003ae400025d058780000c4000098c04f0aef2b9c0001abc0000408000000018c000000024beab30934000000000040806e0188d1bc06d80002fbc61103b4671021a8660000fe700011940b2e9c442d83833f0a34c451841b1162509222cc630001199800000b2848bb4000012b0000010470919305081fb130888f30d237325f000000005828000d4d3aacb2d0000000035101f0000c5000008e325a12051ab441a458007fbddc00000bca443dc80af00011cd000055937200002a4400000000003d329ad800005a30d800020540000001110000069a1c98e4f000085839dc00038440000000a8f800000013f495c0000ed6b40007c987647180011802fd868f30c21db46806c21ff400041d06dd2d9a8362dfd0ce2b0e37a373c88401e0dbd21780002c26074000000016f6000000000000009ce2158
  | 39 => 0x49650000bbb000058d12ccc383f560003d1ce61109c53f276d0ba09e10052a2e0003dae5f20000d7a3f4c0000000000000012f80007f400000003fe800012e8a0b03387bd0e380001f2c5888000eb70000a5c25407dea90902d000000e00005e32c250d700000000df5194b6f06c31e990a623a4f5733da9d6000089a0000070b76c398000000000011d900010aa3db48463260a231dc439e2af04d60908f2a0010b4f800000027ce000000000000000000000998135400043b8a2d0000000405e30a0000798211502900000000d500000000000082d0d04604842a2bcf6507a88032aaad6da9500002344a03800000000011d509450ef3e1c0000000000205c00000000001edd198c6f519f37c0f310f2a0b89cd8fbf00000000cfd1bb000062b154c4aa1ddcbad2dccb133f443e913cc00041867322276000304800000000000b4000005fcafa15e40bb31fc0ae1484d3f0000b83292000000008e600001d200004d31168ac03c0400000006b5000000000000003818000000000000008f3192c58a00008ba0000eb042bccbb1944000000061b0000412000088aaaae9ca80004b73a0cf7190900000b6c14700003f5a300db52fac000178266a35a1145319c3d11f0c6542d968fd0824195055010f80000001c600003a503928000ffb000116c24580001f040000f1000000000003278dc51b0009203e44db2c6507b049c11a2d59156000000038c881e8090c761860000000025a37dc00000000002a9e000000000037e00004528000365cbadaef8a1c2b4200000000003840b180b4c0003ec04f748280390f9c84a48b47f20000eca214420a00010b42e6c000149c6dc17b44f1393000000006150222000000000000005b8000000000004ee91651f00000f1310003a01140c433964db233b457a0ef47600000b3a3ad8ed30538000209c0830000cae000000000000a1ab2e956000000000006aa0000000291403c0000000000000039a8000486097700001de000021800000000000ce10000a2b000016b02e6ca200002012c0c46c24483ec3de859d1754fcc35b2ce017809ff38e40001bd8e8d0000a64463432e00003b70000000135a00017aca15141ca6d281c880160c53900000002c5051145b47243af0b9214480001f92fd93b3438b0000000430a0c3175ca63287c1a78000000010091100000000e887233180000137a0000000151000000000007780000b202120cf93f04b57197c99d2ec43ee80000000000b9780fc00007b8628000047d29685340ba4a9b878400012f00002ebc524068914312e51e600002d806f60000f4c00010820000ce4f1d00004a680006ab0fc20002d4c38f171120436342220590a040c94bf70980e2b0000aed1c70ab9943c971128ac15204c26a000048a856875806689d70b56dea41fccb2116c8f222649b6
  | 40 => 0x16f400000010c2000000002d0d4a0f1d131049400016cc0002492cc402b4000000000000003a680000001900000273c3900e490432a48e821d900003b84a1a0000fb9000118c00000000000000000000000000001e800f300000003350ce3000000000003ac12a2000000078a0000d8000002a63d76c51200502c83fd16b1a383dd2440000471cada0000000049005300000000000000000000024247a9000000015ec37e347c6d700001b341141800000f3eb8990ad377497000502830000b4bbcb8f5401ac41900a027923183c8a6b02c51a4c000000000000000001c2c0002c7c9ad0000000261c2beb0840002afca2400000003dbe2bf2f4400028400003d2eafab6988b922d2000405a0002cac64a366ca08000000041c0000262064f026c17a2f2a1b233e60000a4509b0e5000000000003c3504a1252005151417c16444762b244df1598b7d000092a3baa0000000ed410c8bcb11e8075a2f4170000000000000003bb8dda0a040004894f2435ee26301180000000cf780000000000000477c4f80000304039508fad100b3255c0002a749330b2043b0000a9980002850000dbe0ac90b8bfc810b000000000008950000000152c0442eb00001038888bbe01940e4c00000000d0313c7faab6c0f8012e390ac4643d049843a2090b3308b8ff5b11506800000000000cf60000000000027226cc5d2150298200000003978517800000000000000000faa00000001ac60003fe0bc8164c0000000000000000005cd03b000000031109d53eac21c0fe0ec3053600000011b8000000000009b2bbb0ae8073400046889af8000a3b439aa5b13d67de26a8c2900000002d6f16a0e000000000000451c000000108444bc053948c0000000f820000b6d000000025d4b5e0000a4300000000000a74357443500000000000a2200000000000fbb0c7c9f83960000236e3239ae91db10e000000006f51c88000000051622c400033149fa000053d16eef15b98d0f63e20d4e2f747c40ad8fc208f4ff8a2f062108e8c6b2df0bee0264c1a44a01f22230b9e000000030340002c083e4000106e000000000008b72334afb8000578000011b00003b61970d3e80000003e18000406e0004011151000051f35881db928cbb21214b108d04c340540ae61958fe3458800045cc000065c4a3a59c873457c1be2b46d16b4dcc3c433c584b1ec03e09dc08c9e3876843ecf5e00005b400001e03fde6610e52e2017d45e6303899245c40cd328c202252c77a11d48a2000033d000002d1d58c282d486d11808c683dcc364be1e240081ceed00000000000000000011d000067d000069c000000000000003d2cad800000000acc000413c0000000374215c0000000000000000000000000592c23000000000000002686000000000015a439a000039c3f9014f8aa121e0ed
  | 41 => 0x4c52a0000aac0f3d054c044e3f41d86bd36ecb1b403ce33447c42c04e017614a002b18fc86b25b8533362cef908224b8300830743540a3b4f26450000fc7b51400034acd8e25e119c9a3400042de8ed3d8c2d5379a9fb15290243234123023708d14dc8473ad05b4c08d075c250b5d485074c19dd21b37805aa07b41870ea8b0ca140bc100001a400011af000046a2bec00019246148000e8918c4b9943e05dd935e0d306081570ec512b0478cc60000000058a0000000e8b2818fe207f4a2f45f823400000000000fe6303006e40e6000414419600010ba80008970b64ede245400022a08a53ad4e2f1ce000001640002724d8a031c1ac39c919e40584ad8000b4891580003a44bb4ab6299304184c6000117802f892520d03c303b00000240000325c4cd11cc000000109348b039ec57000034703eb37f4000000000000000000e6c000027c97b000000040240000674a8b28a0f2d00000003b04015000000006922c7000041800000001db4e1e309c00024d000000000000000a8240602bfa526a959e690a532c4c783888b811d44000000000000002c22518000419c000473cd1705182d09e6d050ba9c00010ac000000000013e80002cf40000000e30185c2f70c640000000f3a00001090000aa80000a8cc6900002adf208391c0002a28dab8000b62c08e358000000029480003fc71cc28003173f3c172220800034a00874824286348d06032b03d6a1a670f00580001c38ae9000000031c00003ab800000a44090a9519386ac5dc2a5f1e33f860000a2c3911bd00002b1060e00000dc20408700000d223c7c00000cc000000000005a2000270c00000000002c5448c089c500000000024b8ef114b61c223b0af400010921c351530000f250b370f10001129000000000000002708de700003113e5297f0000298194caf50000dc12be6000231c00000006fc0000299000000032fc51d00007dc176c9c82ff82bb00001f4396c63913f853208e40002c000003d6c889a5689d42f40419a46c0001480e150000a512410be49d9905f24f4cfd489905c48bc2bd85480000e9e3229f64e252b4cdaa0970d8c125a22b1f867013dd0b280b1ef6a00009ba000000000000000238a163b1400000002640000f5d17a40001fb000000000001494a9c000054f3e0e81c800000000000731314d6000009203718ff90000d9d0000bab0000000000046b84b053100000000000e0d0001100800079200007c908fcf3c000000000002bd2ed42e000000002dc09760000f6cbacc00026dc0ea0f181c421840000b4f1190d6874d01449a13b64000072058036588ba80000000000bf980000000000fd484f800000000003c1cc770d2c6c133b07763c40685000000033240002ca400000000e2875436a0000bf0173c0004410fb62f8d01db7ec3860838bf7a00e00
  | 42 => 0x5c9ae436500000000c60a800000c2f208c9410000000000095200000000000000200a0000000fc02408000000000027b855013fc2ff34304ec0000000222e000000000000000003dd600000001f82390389c14808609a4000000096b0000000000000000004b52a6cbf841600000000000000000039d80000000b8641f8000018853b038836e02609073900c8b00006abbe4cb6bb4740000000000000091800000003472000000000001300001c1ee2c294c0000000f8d95dc2083334178113c000000046200000000dfe0000000338327c2e43a0000000001f69364343446000000000002dc60000e10b5a1f500000a9c000425ed55800000000007e2461000023c42da06d03a81890ee900000000000000000058e0000e272cf8a0500000000000c7c01dd00c0d64d921fa44ab0000000000021b3370cb900011da221c2b728c6d4cb4c40000000065439000000000000000adf00003a6443c81e0000e5008b00000a30b3400010f2035642812d0b8b240cf30318ab39340c0000378e5f221493245c015d0ed0546bc20a48a8c2a91891ccdf3aa80000b98c030eac000025ed853ee000037a4e793b6cea204200002b660000ad080a1c68e6741e70f30000f14ae902c31ba0e2d20c51e92f88a7b83c44433b103c90d3a844213cd1b00007d0046000011fc38c3428a2c02b05f13558b94383800003dcf063be896a13a600048041aa0ae80000000000000028a2ecc000000050e17150560000000000086ac01c00000005e58000b3c903a49e44b80000000bbc0c9cc8900000000000a8627287503e4f1a144b05df11b510924c42a100008623760f9d44b4179145ccc73b529420000000000000027180001b3c00032681680000000000000019040003f80385000000024fe0000000000000115d366800000011d40000896000104707cc04500002763958b46302caea2a8c33027e49133740c722ad6d270f200000000c200000c870000ed037bd1f61a844333ee85c700011a630c8ce93024000000000000000000480000071cc33073d0ab00005891a7c000000000034bc000000000000000000000f4f1ae025b00008fa9cf8000309049c000000000000002168000000000023280000000bb900010e329dc4054150000000054607dce8a00000003f1607f000082d42cea110000c7d0000fa616b904d03c85048af05fa10300000000c299cd0000342000007740000000143a3bcf7e03a41e79c24000146c0820000000422800000004e01f9073041dab261a1028e2a8400000003643129008317a0003bacb8440c8f5a0000ba51d7450500000000f340002d3400007d40001036425000000000000d63c6642026100000001125165094931f8122b4f43e608403702b36a330000b590000a3d407045727b094097cc34d3c847790a0812d278049b17
  | 43 => 0x3f1c0001d051143d24d333fd105500000000000000090430511443750000000144e9f4000080c00004f000000000000000258c1173e7030caf70f2c9688322423073b2f00a721ec8dcc1d8c95f0000a702a9800043649d2800000000000002218b403a78e191d6cdb62c880000000fac80011053020a183eb6e9a1324ef222e06b13e94c0a03b6bfd309f12a29cc627a27823c107cd4821d8e9c35d00603c3c62e3f585ab0ef8ddc3c8c21f11dec2d000000000000002d9e0a200007b800003570000000000000029f809d400833c3e14b044260000220d06d2998bf233c85cd000000048907cc000000022280000000000000000001d8069000000000000b1000000014b515a000000029ec2591a0515b0ecc0002e550ea01900002b340002bfce87a2a4000000000000000000000000063a00000000000d010a011ca809000000028e8c7941cc00048007d700000003dc09dc38c68040b24708a68c13b000098e929d0781f3876b09f02e523485b883140000000e3a2d020000f603261e7400032985a535a4ff515609ab236509e0000000414e3ca003087826c8f4c0000000000063c248c00046a87c60000c7a8000000334c00000000001398252000000003d8141356103800003241cf48d83ddb02998980000ae400018c800012989194398561ad26f380000fb127a8f02000000000000000000000141600005bc6cd0000c4e439600046700001b30257439ccce00010cd118add20a800001a643723b60b4b4434000001ce8700005e442f055f20bd1ad36be4ca0000b0b45dc0003b089eb000000044280001a7489d254c0000000e4b000031500000000000a51a01400027f11b92fcc56d444c000000055d20a01e41434a95474cb872d7ccd733991d200000000000000162c18e000027e10340002c48e920000f1b45d80003950be51e180f48b384c819e46e6000000015b0f463de63373f6800033080891cb80000000221235105022b4df1000000039885ff2a507071a2c08a00001b73b5400020840000000d8f02940002584bb09a0ca2038740000000f84402c6294880f81929495b00003b92d42169071400000005e2365000000000001f8ca8c000120f3b4800047940000000c993f6000000009cd44540002e4a0000000000000093c0000f09203800002c80002220ab10c0455a0bd80001b286272efc6ee000033310180003dacedf000014c2dce000000122100001a8800083f145641540489faa5c80000000f002b1c9472bf0ceb00000000000ee7013e00000000000000b242b4f05192383ae41bc3f139f8cea26803000000000046434faf6e000312638f8be40003ac400009bcedd23e0b8908e10b92bd6000000000000000001608000000000000003620000fef2bd2000000000030ec0000000000381c00007def
  | 44 => 0x50000000000000000000000000002c00001eb2dea00030940002ff05b60000773000090e0000000000000000000003abc00033280001388000118493014d40000572db846444833694a9300008b2aa9a0000000f18a0002cd2d94d2e36fe85539c4fb7400c1fe36fc92d31e817b96dc2df3db0508117801f22f8d350a591ab3c70c6c48480003e3c000000000000002650000bb00000bb83f148ac8ab4b780aa4df600000000000c264868000217083d00e0e510000225152440132e0de823a86d89110454c0883b79c200000f889b828500003790ba009ec8da2cb06c50000b411aeca0f01f903340d00001204514000103d1c840e10e340750f1aa8a8000000000000031851260000f6233e8d5515a02052b2a000000000044203a30000de13ecc1cc00000003cfefe908dd0c600002c43550000000000000006f80f7ec5b80008b4000000040be00035f055b289426d0020df2210c697000037c2068000017425316ec000429e44a0d4c243142c23627942b00000391c0531b5bfd87ff8
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2538c220a15811954310d20945831c55448520d05749cc5148520d06745cc5148520d05745cc5148520d22745c05148520d21745c05148520d42735c05148520d41735c05148520945831d64148520925841d6314852091a839d85450120a19839d85450120931811d44350120a89831894250120aa1811894250120b20855052150120c19649ce548c1208e1811c9644c12091a849d8534c120a19849d8534c12085987d90534c120951811d4434c120c1875590434c120c89645c8434c120b40854c5214c120a27855912108420a25869512108420a478558d2108420e065458d2108420e055458d2108420a458694d2108420e056494d2108420e056454d2108420e22544856008420e21544856008420e42534856008420e41534856008420945831c95448710925841c95348710d05749cc5248710d06745cc5248710d05745cc5248710d22745c05248710d21745c05248710d42735c05248710d41735c05248710945831d64248710945831d54248710925841d63248710a198494e60d0e10a1a83d5160d0e10a19839526090e10a1a84d4d6090e1081e879954310e10a0d821954310e10c1a7458e539021091a839d85450210a19839d85450210c32765c45450210929821d4435021081f8759353cc21081d87992538c210c19649ce548c21083b87592538c21091a849d8534c210a19849d8534c21085987d90534c210c52765c4534c210949821d4434c210c1875590434c210aa1841852148210ac1831852148210a0d821954310d10c147550d6110d10945831c95448510925841c95348510d05749cc5248510d06745cc5248510d05745cc5248510d22745c05248510d21745c05248510d42735c05248510d41735c05248510945831d64248510960855c24248510924875514248510925841d63248510c1a7458e53901108588758d5290110c187458d529011091a839d85450110a19839d85450110929821d44350110930855c44350110a91831854150110aa1821854150110b20855092150110c19649ce548c11083b87592538c11083887591528c110c19641cd528c1108e1821c5644c11091a849d8534c110a19849d8534c11085987d90534c110949821d4434c110c1875590434c110950855c4434c110c91645c4434c110a9184185314c110ac182185314c110b40854c9214c110b21841492188110b41831492188110a60855912148110a60865512148110a608558d2148110c25645c55208410a2584d952108410a4583d952108410a27855912108410a25869512108410a25865512108410a478558d2108410e065458d2108410e055458d2108410a458694d2108410e056494d2108410a458654d2108410e056454d2108410a61815496008410e22544856008410e21544856008410e42534856008410e41534856008410
  | 1 => 0xb21821855150040899831d92150040838865d52150040918835d52150040c28765492150040c30765452150040ca1764842150040d21754842150040d81734842150040c89635c86095230c91635c46095230c1a545c263d0a30c1a545c263d063081d879506348630c1a545c06348630925841c55248630925841c95148630a2584d952108630a27855912108630a25869512108630a25865512108630e065458d2108630e055458d2108630e22544856008630e21544856008630925821c5545053091b875536310130c4a655c86310130d09545c86310130c52655c46310130d11545c46310130919879974310130c19541cd62101308d1811cd6210130c19541cd61101308c9821cd6110130a89821c2648c130a91811c2648c130925841c95148430a2584d952108430a1a80d5163d0030a0d8215163d0030a158115163d0030a49821516390030a51811516390030c1a7458e5390030c2b655c85450030c33655c45450030c2a765c85450030d0a735c85450030d21729c45450030c32765c45450030d12735c45450030d22725c45450030d21725c45450030a29821536350030a31811536350030919871526350030b09821526350030b11811526350030b09821516350030b11811516350030b09829d64350030b11819d6435003091987d964350030b11811514350030931811d15250030931811d54250030929821d15150030929821d54150030c29645c8548c030c31645c4548c03083b87592538c030c1975592438c030b0982151438c030b1181151438c03083b87590544c030c29645c8544c030c31645c4544c030b0982153434c030b1181153434c030b0982151434c030b1181151434c030899849d9544c03089b87590544c030c91645c4544c030d11545c4544c03085987d90544c03091987990544c030a1986990544c03085b87590544c03091b87590544c030a1b87590544c030c1b87590544c030e11649c4544c030c19645c4544c030c52765c4544c030d12745c4544c030e11645c4544c030d42725c4544c030d41725c4544c030c53645c4544c030d12645c4544c030c51645c4544c030d11645c4544c030c11645c4544c030899849db514c03091a849d9514c030949821d1514c030c1874591514c030b1184185514c030b4182185514c03085a86dd7414c030949821d5414c030c1875591414c030e1164545414c030899841d9214c030858865d5214c030918845d5214c030c5076545214c030cc176484214c030d4175484214c030d8174484214c030945831c55448720925841c55348720945831d54148720a198494e60d0e20a1a83d5160d0e20a19839526090e2081e879954310e20c1a7458e539022091a839d85450220a19839d85450220c2a765c8545022081d87992538c220c19649ce548c22083b8759
  | 2 => 0xcc6048421d05549cc6048421d05545cc6048421e055498d21d4021e065458d21d4021e055458d21d4021b4183d512194021b2184d4d2194021f015494d2194021a25841d92154021a4583d912154021a2584d8d2154021b22841c12154021b21841c12154021b42831c12154021b41831c12154021b4283d512154021b4183d512154021a62861512154021b42831512154021b41831512154021b2284d4d2154021b2184d4d2154021f025494d2154021f015494d2154021f025454d2154021f015454d2154021a62861052154021b42831052154021b41831052154021a62861092154021b42831092154021b41831092154021b23845d92154021b20845d92154021b43835d92154021b40835d92154021b22841d92154021b21841d92154021b42831d92154021b41831d92154021a63865d12154021a60865d12154021b43835d12154021b40835d12154021a62861d12154021a61861d12154021b42831d12154021b41831d12154021b4283d912154021b4183d912154021b42839912154021b41839912154021e21641912154021a63865cd2154021a60865cd2154021b23845cd2154021b20845cd2154021a62861cd2154021a61861cd2154021b22841cd2154021b21841cd2154021b2284d8d2154021b2184d8d2154021b228498d2154021b218498d2154021e416318d2154021d22744842154021d21744842154021d41734842154021a27865512114021e055498d2114021e055458d2114021a478654d2114021e066454d2114021e056454d2114021e21544866014021e41534866014021e22644855014021e21644855014021e42634855014021e41634855014021a89821916094f40a91811916094f40a1a80dd953d0b40a1a80dd953d0740a18805915348740945831c55248740945831c95148740c197494c6048740a4583d952108740a478558d2108740a458694d2108740e056494d2108740a458654d2108740e056454d2108740e42534856008740e41534856008740c89645c86094e40c91645c46094e40a19801925348640945831c55248640945831c95148640a4583d952108640a478558d2108640a458694d2108640e056494d2108640a458654d2108640e056454d2108640e42534856008640e4153485600864089a839d46050940a19839d4605094089a839d46050540a19839d46050540a89821d263d0140a91811d263d0140a89821c26390140a91811c26390140c0f655c85350c40c17655c45350c40a158118d4354840a0d8218d4354440945831c55248440945831c95148440a4583d952108440d09535c85350040d11535c45350040899839db525004091a839d95250040931811cd5250040b09831895250040b21811895250040899839db515004091a839d95150040929821cd5150040b1183185515004
  | 3 => 0x9ab5f6c6f2a840b730c0b0468922193e8a0e54b03650b16979b809808650007e9bd4d8004549ae337bb6800b60000028a8300000000478005004ea92187d9cc656a2d92667c35d1b99c231309b83c8185c6a9b9dc6bd63575428000007800006000c60c90457800000005b800ba0006239003944551a1000d02819d17a9c1da4484000b2800e2b6aad1c967d52c9000c3b4360187da17e638009807b64000000da55800b335b378b60018198968b036f2e1fe8f800000d2000f8d82b90000d5c97fb6f12bb89c80831a9a1256000e0b5c45abb5d8003c33637e3091ac71d1b60030dca8007500069800660007447ee2150b1460000004722c00000a7b4cb0ebcd5298cc216c51eadf6f923aad96ace820eea6f74e39321f338b08eb25b28de4d44eedc12b808d800871860436d898509014f7715b158004d0340030a00040b49d00000051d2445000586723a15d002006be6a00089aad0e6c0946906570358dc1060b80c7c9d6b8ac489022003530034a002f2a310000276003662f93829376d8de4002c8629c7d1000c9c00d7a1e5180071000001a3000001e8002799bbb0007200102c74034060102a00c121000502c05000010240d04c1b0241800001074170203b000030080000c11008020000b120190740000c0307003000060180d018011200b0200000008004040000802c030000508012030000740101452004000080003c000041f0300400800000000101202c01000050080203c0000006018060300003403048000480001c0002c0401c0300c1301406004030000a0b40b0000f008450000100c01000030040302c010080f004190081108c00014020601000c240580c0040001848004000480101c040080103403004020041404801008000200300c0200c4a03c010000200406018040145101801a188355160151218e1801c963905218c5831c96090521cc1739c06250521cc2735c06250521cc1735c06250521a858318b4250521aa18018b4250521c19641cd5014121c187458d5014121b06831c95448421b05831c95448421b22801c95448421b21801c95448421945859cc4248421d05549cc4248421d05545cc4248421961859c04248421d21549c04248421d21545c04248421963805d36548421927845c36548421947835c36548421961859c06448421d42735c35448421d41735c35448421b2280dd15448421b2180dd15448421b22801915448421b2180191544842194583dc15448421b23805d95448421b20805d95448421b22801d95448421b21801d95448421b0683dc15448421b0583dc15448421b06839c15448421b05839c15448421d21701c15448421d21549c05448421d21545c05448421926875516048421924875516048421d0554dcd6048421d05541cd6048421925859d06048421927875506048421945859
  | 4 => 0x4621400000960005b000001080029433a3c00386065898c8009a07064963de8f63134eb1b0800037df9fc0017a150008292ec63119332057dbea2126440c8e13049f35a52862a81ee2aa2e1900a839786fd85228800d5cec6b02d465239a1a24d6248b6e2d1ec9b1743d15ad01930a027bc35f5c2f66b24ed3e3a9c30071b32ab8e04e99e10b6b07920328d604955a4825df284e4e7e5f220a5b753024205a801773cab153b4ed0659480245211cfc2118228afe645b5a40c268356c42044a15760cea5a9d20912ade098cf82c00018d56b862e8b1c86aaaa2a3f97d9e341c4c000e2dd241f472c447697700002d64000016500362952b6c95e2003920032e4f6b0c3014cd00000000124ac530a8dff48448a6b5772001e62e800002488e082b52be94095000dcbe800538000008306ade000ecbf234b588f59aa1c1d842202a198000018f3cb1c000000a73a2f01fb9911b05e85703e6a06c3603a97160c2f06782ba6d1513e820b85a22b84c6e93c331b2000000f686d41de76000c141ca6448c8b0900000002b27e00088800a390cba8e4160006b8b24cc331180099000389a5d4af8c798c16af400000001ca70800bef2c000539e804d0800ddee0d18000006895a82c0d64a6a4a9d2e4c99
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1e03a824022a980907e340058dc006576004b78c20a04c98eca9242a0081411931d95148540103022a8c08e6b108098602551821cd6110130e00b24e4b88a898061c01645c971151300c2813243a2c8a8a601850264875591414c030a08ca0eca8a4298061409939d97215140882823223aac821a609050464e765c45450210a08ca4ecb88a698421409921d56410d30842813243aac821a6088604215645c4434c110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 22
  | 6 => 994
  | 5 => 6049
  | 4 => 4660
  | 3 => 458
  | 2 => 16
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (430+((h/13+packedAt gbK7 (352+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (31634+((h/436+packedAt gbK6 (26838+(h % 436)*11) 11) % 1573)*11) 11
  | 5 => packedAt gbK5 (264554+((h/2478+packedAt gbK5 (229862+(h % 2478)*14) 14) % 8924)*14) 14
  | 4 => packedAt gbK4 (252091+((h/1827+packedAt gbK4 (228340+(h % 1827)*13) 13) % 7959)*14) 14
  | 3 => packedAt gbK3 (29430+((h/195+packedAt gbK3 (27480+(h % 195)*10) 10) % 703)*10) 10
  | 2 => packedAt gbK2 (1171+((h/7+packedAt gbK2 (1136+(h % 7)*5) 5) % 26)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3c78f8e38f1c71c7ee38f1c711c71df9e490f
  | 1 => 0xfc07f7f03ffe07ff8f03f1e07fe07fe3a071f3
  | 2 => 0xfff807ffc0fff81ff1fc01ff81ff81fc438e3c
  | 3 => 0xfffff80000ffffe001fffe0001fffe007c0fc0
  | 4 => 0xffffffffff00000001fffffffe0000007ff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xc070e0a451148a38806183051505145b0e4905
  | 1 => 0x4010100802010001000102020202080001052
  | 2 => 0x8800200024000400204004800480100008228
  | 3 => 0x5112204d348d040925aaa40209934c09740d80
  | 4 => 0xa22444682009a69249d349934c0208127b6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8fefcfce8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36412
namespace PEqualNP.Outside.L_meta_36412
open PEqualNP.Outside.L_meta_36412.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_320 : Interval gbAtlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_352 : Interval gbAtlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_384 : Interval gbAtlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_416 : Interval gbAtlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_448 : Interval gbAtlas 3 448 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 458 := (concat (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192))) (concat (concat (concat bgb_3_224 bgb_3_256) (concat bgb_3_288 bgb_3_320)) (concat (concat bgb_3_352 bgb_3_384) (concat bgb_3_416 bgb_3_448))))
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
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3808 : Interval gbAtlas 4 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3872 : Interval gbAtlas 4 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3904 : Interval gbAtlas 4 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3936 : Interval gbAtlas 4 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3968 : Interval gbAtlas 4 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4000 : Interval gbAtlas 4 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4032 : Interval gbAtlas 4 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4064 : Interval gbAtlas 4 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4096 : Interval gbAtlas 4 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4128 : Interval gbAtlas 4 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4160 : Interval gbAtlas 4 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4192 : Interval gbAtlas 4 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4224 : Interval gbAtlas 4 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4256 : Interval gbAtlas 4 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4288 : Interval gbAtlas 4 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4320 : Interval gbAtlas 4 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4352 : Interval gbAtlas 4 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4384 : Interval gbAtlas 4 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4416 : Interval gbAtlas 4 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4448 : Interval gbAtlas 4 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4480 : Interval gbAtlas 4 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4512 : Interval gbAtlas 4 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4544 : Interval gbAtlas 4 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4576 : Interval gbAtlas 4 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4608 : Interval gbAtlas 4 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4640 : Interval gbAtlas 4 4640 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4660 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))))) (concat (concat (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672)) (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)))) (concat (concat (concat bgb_4_864 bgb_4_896) (concat bgb_4_928 bgb_4_960)) (concat (concat bgb_4_992 bgb_4_1024) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))))) (concat (concat (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696))))) (concat (concat (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824)) (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984)))) (concat (concat (concat bgb_4_2016 bgb_4_2048) (concat bgb_4_2080 (concat bgb_4_2112 bgb_4_2144))) (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 (concat bgb_4_2272 bgb_4_2304))))))) (concat (concat (concat (concat (concat (concat bgb_4_2336 bgb_4_2368) (concat bgb_4_2400 bgb_4_2432)) (concat (concat bgb_4_2464 bgb_4_2496) (concat bgb_4_2528 (concat bgb_4_2560 bgb_4_2592)))) (concat (concat (concat bgb_4_2624 bgb_4_2656) (concat bgb_4_2688 bgb_4_2720)) (concat (concat bgb_4_2752 bgb_4_2784) (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880))))) (concat (concat (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 (concat bgb_4_3136 bgb_4_3168)))) (concat (concat (concat bgb_4_3200 bgb_4_3232) (concat bgb_4_3264 bgb_4_3296)) (concat (concat bgb_4_3328 bgb_4_3360) (concat bgb_4_3392 (concat bgb_4_3424 bgb_4_3456)))))) (concat (concat (concat (concat (concat bgb_4_3488 bgb_4_3520) (concat bgb_4_3552 bgb_4_3584)) (concat (concat bgb_4_3616 bgb_4_3648) (concat bgb_4_3680 (concat bgb_4_3712 bgb_4_3744)))) (concat (concat (concat bgb_4_3776 bgb_4_3808) (concat bgb_4_3840 bgb_4_3872)) (concat (concat bgb_4_3904 bgb_4_3936) (concat bgb_4_3968 (concat bgb_4_4000 bgb_4_4032))))) (concat (concat (concat (concat bgb_4_4064 bgb_4_4096) (concat bgb_4_4128 bgb_4_4160)) (concat (concat bgb_4_4192 bgb_4_4224) (concat bgb_4_4256 (concat bgb_4_4288 bgb_4_4320)))) (concat (concat (concat bgb_4_4352 bgb_4_4384) (concat bgb_4_4416 (concat bgb_4_4448 bgb_4_4480))) (concat (concat bgb_4_4512 bgb_4_4544) (concat bgb_4_4576 (concat bgb_4_4608 bgb_4_4640))))))))
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
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6049 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
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
theorem bgb_6_992 : Interval gbAtlas 6 992 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 994 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 22 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafefcfce8fefefeeafefcfce8fefefeeafefcfce8fefefeeafefcfce8fefefeeafefcfce8fefefeeafefcfce8fefefeeafefcfce8fefefeeafefcfce8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277992680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36412.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.and,[0,5]⟩,⟨.or,[1,7]⟩,⟨.or,[0,2]⟩,⟨.or,[3,4]⟩,⟨.or,[0,10]⟩,⟨.and,[6,11]⟩,⟨.and,[3,4]⟩,⟨.or,[8,13]⟩,⟨.and,[9,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277992680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36412

open PEqualNP.Outside.L_meta_36412 in
theorem PEqualNP.Outside.L_meta_36412 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277992680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
