import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36330.Model
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


end PEqualNP.Outside.L_meta_36330.Model

namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
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

def SBf (j : Nat) : Nat := [6, 6, 7, 8, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36330

namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x20bf43bd43
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (34+((h/1+packedAt s0K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 2 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 3 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa6082046244842014a12c42946214a98186e15
  | 2 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 3 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36330
namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x201404000c341c2003bf43de43bd43dd439d43ee21ec21ef20ed20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe2000064ac8068eaa4878f5250f18a4a1e350e21c6a18438d43c831a86905914520
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x801a0a19875250e0f6550e218319543483054314520
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (156+((h/3+packedAt s1K4 (144+(h % 3)*4) 4) % 14)*5) 5
  | 3 => packedAt s1K3 (224+((h/2+packedAt s1K3 (216+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt s1K2 (155+((h/1+packedAt s1K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffff83ffffff81fffe0ffff83ffffe71f1ff
  | 2 => 0xe0fc1ffc1f83fffe1c1ff0f07fc3c1ffae4e4f
  | 3 => 0xff001fffe003e1ffe01fff007ffc01c1cf8f8c
  | 4 => 0x1ffffffc01ffffe000007ffffe01f00ff0
  | 5 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40080088010000002022011108044444009095
  | 2 => 0x8a312910ca2550960d0c90a2324288b8a6464a
  | 3 => 0x465a5229474a832ae2172a055ca8150d4b8b8c
  | 4 => 0x94a39c429460d5cd5741888867333811f00d60
  | 5 => 0x18c31873187319f19b99ccce06222021fd6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36330
namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x98227000038000bcb8a00b80236090c0e00700033e64d8d160149e1014a000c688892000000048002d1e3152c5000eb126010a25648015005800000000804a0000001000000104003020414089ff43bf43fe43fd43bd43fc43ff42ef42fe42fd42fc42ec42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2810e070d00000000001000a3431640039001a4cc6128894008d0004506732da20bc5c3d8ad14653c188160525a404e5d15274044f171d8d08e4f004448909078fa5f13104680000128da00499c8004c1023cfc944e03400002a918f400411fc00543600000990005880171c0d4f242109dcd41d0c1c0ea2926870362340920e88c00024760345800006f00000f84732000b463001c50a00160cd2a840f8e85a910726124454da8814001e15cb0a12b0f4a66b0983cc0671f8f800001227c5043291b8889a1902000504b0552e190a0c000001b8409c0c520000c80248c45e360001028000060980060100818014841190808099010082000c80838100830180000a03831e8005010506848608820400040181858700826bd4b43d6296873d5490edca521db54a43b7a92876c5250f3ea6a1ebd4943d6292873e5410edca421db54843b6a9e85af43d0b5a87a15b94742b6a86856e5290abca6215754c42b72a085ae5410b9ca6215b54c42e6a98854d5310b5e86216b50c42b7288856d5010a7ca9994f55332cea1e656e548cad8a9195b54e32d7a1c65ad438cadca3195b54232cea1a656e544cad8a89973d4d32d7a1a65ce434cb5a86997350d32c6a1a656c514cadea0994f950329eaa0656e520cabca7a0d754f41b7296836d52d075885a0db94a41b6a94836f52506d8a4a0eb109419f2a6633d54cc6dca598db54b31cea1c636f524c6d8a498cf950319eaa0639d430c6dca418db54831bd2806379500c67ca910cf55221b72a443ae548865ca910eb55221b62a4436f53886daa710ebd0e21d6a1c436e51886daa110db95021b62a0436f53086daa610ebd0c21d6a18436e51087cca210db54021b7294816d529035885205bd4940b6292815e53102baa6205b94840b6a9081ac42102eca2205d544409f2a6613d54cc33a87985b94b30b6a96616e528c2daa5186750d309f2a0613d540c2dca4185b54830bb2886175510c2dca9905b15320b7a9e416d53c835e87906b50f20b728e416d528827ea8904f15120d7aa2416e54482d8a8906b15120962a2416f53482daa6906bd0d20d6a1a416c51483d6a0905b94820b7a96216c52c42dca5085b54a109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8005c0002800014b000c96b80000c8b6cdc98336ac31d543979674d079838309256650497767cf0834288870480aac48e518d0885331009c28044000016a0000180280018208903933608c80002c802a998752d0f0d53d0f42c39515310b0e6454c42c354f4310a2e64946328b191508ca666195132a3592434ca4c6550d32c3d95434cb0c6550d32c350c514cb0d43d4132a358c42d070d5310b41a358c425062e64d4931c350d520c71943540318758e548864d6395221a358e548870e63952218b58e548870d63952218358e548862e64d4e218bd97438862f6550e21c3d4d438864d63150219a580540870d5350c218b992510862c6454021a358c429028d6310840c354c42103244254440c350d52cc22c6454a309358c54c830d5350f208b99251c821d63151208b992544824d6315120a358c544830e63151208b58c544830d63151208358c544822c6454d2099185534822c65d0d208b195434830d5350d208b99352c422c6454a10
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x280c018004000070040900000120008282b8cc8a9885419c76550d3281ae7324a210c0d731915008682b9884a8881035ce6494720818eca9a86905047154d4348206b9cc9a9621035cc6454a10
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (912+((h/16+packedAt s2K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s2K4 (4895+((h/55+packedAt s2K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s2K3 (2420+((h/20+packedAt s2K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s2K2 (505+((h/3+packedAt s2K2 (490+(h % 3)*5) 5) % 22)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf0ffffe0ffc3ffc1f87f87fff0fe0ffe91f33f
  | 1 => 0xff07c3ff0ffc3ffe1f87f8707f0ff0ff6e4ccf
  | 3 => 0xfff803fff0003c7fe007ff807ff000e18f8f0c
  | 4 => 0x3ffffffc07ffff800007fffff01f00ff0
  | 5 => 0xfffffc000000007fffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x12008022008400002008809110120224009115
  | 1 => 0x205104442500500a088308222104a05826444a
  | 3 => 0x4633aa8a63aaa8d6e445d5057aa0668d8b8f0c
  | 4 => 0xca433108a220965555044084cc94c01d00aa0
  | 5 => 0x88c6221ccc3332799e66664e08818811fd6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeee8888eeeeeeaaeeee8888eeeeeeaaeeee8888eeeeeeaaeeee8888eeeeeeaaeeee8888eeeeeeaaeeee8888eeeeeeaaeeee8888eeeeeeaaeeee8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36330
namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0xaa300a89801e2802648702170aac01d0624427001cc2100006812044fa82c6c3000048f00000002000001144a0060034a4700446400b0010404004a003000203040ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe617e52cc3dca5985b94b30bea9661ed52cc2daa59877ccb30f719661dd32cc3da6598734cb30bf28e617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61bf438c37a87185f94a30bea9461ee328c3da65185f94630bea8c61de318c3b863185f94230ef98461fb308c2fea8985f95130beaa2617c544c37e86987790d30dea1a61dd434c33a86985fd4930be29261df324c3dc6498774c930f699261cd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861bf430c37a86185f94830f7290616e520c2faa4187b54830b6a9061ee320c3da64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc85907b50b20f719641ed32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20dfa1a41bd43483dc84907b50920f719241ed32482fea2905f14520f790a41ed21483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20dfa1841bd43082fca4107bd0820f621041ee32083da64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43dc65887b4cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c538437e87086f50e10bfa94217e52842faa5085f14a10f719421ed32842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10dfa1a21bd43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443dc64887b4c910fb20a21f541443ec62887d4c510fb10a21f521443f460887e4c110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810f719021ed32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077c84a0ef10941f719283ed32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420fb8c841f6990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331dfa1e63bd43cc6fca598fb94b31b7296637d52cc7daa598db54b31f719663ed32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c7bc8718ef50e31eea1c639d438c6fca518df54a31ef99463ee328c7ba6518fb4ca31e6994637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c77e8698ef50d31bfa92637c524c7dc6498fb4c931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863bf430c7bc8618ef50c31eea18639d430c6fca418fb94831b7290637d520c7daa418db54831ef99063ee320c7ba6418fb4c831e6990637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1e43bd43c87de8590fb10b21f719643ed32c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21dfa1c43bd43886faa510fb90a21f6a1443ee32887da6510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1a43bd43487de8490fb10921f719243ed32487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c530877e8610ef50c21bf29043ee42087da8410fb8c821f6990437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40f719681ed32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885207b8ca40f6994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940f719281ed32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206fd0c40dea18817e52103dca4205b94840bea9081ed52102daa4206f90840de21081ee32103da64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330dfa1e61de43cc37a87987750f30cea1
  | 2 => 0x1a014020160020bc0000300400c018050420180000001a018018020040080200300000000800002004010030040700301f000034008100161040003406801404804006016fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0f7aa5a1ef14b43dfa8e87be51d0f7aa3a1ef14743dfa8687be50d0f7aa1a1ef14343beaa4873d5490efca721efd0e43efa1c877e5290fdca521db94a43bea9487ed5290edaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1efd4d43cfa9a87bf5250f7ca4a1ef54943de29287bf5150f7ca2a1ef54543de28a87bf5050f7ca0a1ef54143de282877e5410e7ca821df94c43dfa1887de4310f7a8621f750c43bf29087ee5210edca421df54843f6a90876d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210b5a84215f94442bea88857e5010afaa0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a9996fd0f32ef21e65bd43ccbba87996750f32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65bf438cb7a87195f94a32f7a1465ee428cbda85197b10a32ef99465ef328cafca3195f54632bf284657d508cbdea9197b95232f6aa465ec548cadaa7197bd0e32d7a1c65ee438cbda87196b50e32f621c65ef518cbdca3197b54632f628c65ef508cbdca1197b54232f6284657f544cafca8995f55132be2a265bf434cbbc86996f50d32eea1a659d434cbde84997b90932f6a1265ec424cbde6499778c932bfa8a657c514cafea0995f14132f7aa265ee544cbdaa8997b15132f7a9a65cf534cbde86996bd0d32f721a65ce434cbda86996b50d32e6a1a658d434cbd886997bd4532f728a65ed514cbd8a2997bd4132f728265ed504cbd8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca4195b94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41f719683ed32d06fca1a0df54341beaa4837e53906faa720efd0e41dea1c837e52907dca520db94a41bea9483ed52906daa520efd0a41dea1483ee32907da6520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837
  | 3 => 0xa90001e36d001072043660810829d91f4068b88004e4a10300a10da2bd4632100037d330b54041455ea4e2a4001033360001488236d4965b5a3b176e2d716486a2d6c3d449e5424c505db6b5e6878f51f54d62f09e8b91827f4f6946196718e91c460ea058f8e13a009c430da622b044191c4f61c9a894f0467fc0005437e6340b8374e2abc01b4f26a6a831b7067e0fd960000006380029f3627610ea383d28b90d0002908993f245426814ab1c317038c3288c6f0c6c000821b22983081227e604629de41c941bb0000007b11c98f2182882806e088d51a0922028cf055a1655471cf70002228357d1952b600027a420001bd4bb38686d593a800000924bd000000294268595d8a34e583104200177a463ee24ca8b60400d94e016c19400141aed48677c00000180ccc002c76b6d2870329570310c99911fc9e94899656eb084fa3b3c40a1932445004a9b785c1bc174f411f604574ea95e1d402038800258000520675e00010bb4e42ab5cee83a69a6303214c23cbfca723406c2dd742013ec560ba1926dccc4f5a62214ad99e9212f26b4c118b3662042723c21258c0000025e8ac87047634c181d88f2ae9d0f80013840014d28839cd7415b624ecd149024f0946850182d05e6a5b33125b404518a1f4b2b4d852b237c064db29b200a59a9187152cf949b772fc061862ba430b216e8966903b9518ac46a3b04f1a320c4b80123d41e7e4b28730c4b481494718e000172a95ca2cc0000023614ca10f11b6b6cfa00043806d1d20c16c8d94a14b0b61e592a2a184bd15301e5e4c21959671163e0c4b002463412baea4a63186b9845dc8853184c68cc04d0000524851af8002c4928e28e7000c78a00ba4bac903f9105603ac000000000000a80026ea9c0032a47c5500000000089d65a4d10840800107286a857ca336b00015e02c30c6c1512fe3c0c70182cf69830cc280181102c014000070080100000004e0040380c00000003800000058008580080340580f0520080000100a0000000003400800004002000010020340080380001c0080400000600c000000140080480704a00c1b8270000000001300002c0200301e0000100403601c0000d0020200080300202c0100100801002801002064058000040040100000000801801002020018000220100680000602001001000038018180000000401100400013802004000028030060480001501009c010080000180800100200c020160020100600101a0080300b00802805801020000010000000100a0030200040580701205001010008014018040000100080000e05c000120060102400000c0003d0230080080181900c0e800000006068068010000600b00000e0180c80503e0dc0300e0060240280f0240080280700400c02010000020028070020180301e0d00040500201a01c000100
  | 4 => 0x16a32d37a44c001f23b6b980002434caac001f8684894bea8b6508449206c40e040000a857e105399e45f85994aad90641f1859362bece8a285e1da26c0031d2ea601722585b84059cade2242b8be2090000012e1080009a8b90e90005c0e40003ceb180e290270349b5183018c8d2f89a3a29b46422331425d43a285d2100589331e8d401a2c003e01c150005685640021b0003c8bd8771cc2386a2e30ac5e01e23200098400000000000da8003f4000ed0002785b9618004ac664cf8005580009300000000000000000b84b41535bea94688e845a0cd111cf07c29d0825e1244c0000006ea8a586800000bad6c000234000000ff2060014e3630ae6753607e4103bc0004b25acd15d80e6cec24001b74a465000000230be0b99bb4f0c659d80055c78537afb0003713bab5294d541eae0216991663590006f0dc0003509a50ca3f0009f4878ad092000032be2ee6e4349d76b4dc84c080588771978e51e6074cd15a62cc0c130000ea00006928374d90100f034e0d49888a5eaae400000000678d78681b034c5f8006885d93707b21a0014c0002884d1688f5000995452204c0695789f10007f84eb220005801cb4b28200133800000ac40000012ab354e8001ac001899ef2c8000002c56f2025598be336d84661270000007e27c0006c89907d53c464000005040016a96f0009a0b08001ee160001493380012a000070c39479880007997b16a19e9fc58340192db0e0a5b5a0094001fc39400000000154000948000000000024022e00190000392a180000050a554000b4122000000000001c0001a2540000002793ac7508b0dd0002403d32e000c9ccc05a27c0000025151cbdc9d3150843d835ace608450058bd320d786688d0445fd71087358118d705f620d5c4e2470ecda53800002c8b000048482aa14c8851320002a9501aa000928fd1408bd56866000920b4aca4b40000013b368954001d323acdc000f90002257e8e25ce4acfdb3239a1e00500060a00022b18000930f98006e64e40000000a001059cc000000a68000008296b3531466ad9a80f110000d200046e000ae0fb0e8001122300262c9a4b7432e3384a11500
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8538426d6214e10c794d438431d5350e108fd91528423c6454a108f990528423d6414a109798c528425d6314a10d394d328434d534ca10e350d3284399434c210f24c9308423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c54443356115110c7d53534431c54d4d10c7d93534431c64d4d10d3d8b534434c62d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534425e6514d10c7d50534431c5414d10c7990534431d6414d10d3988534434d6214d10d558453443596014d108f997434423c65d0d10c7d4f434431c53d0d108f995434423c6550d10c7d4d434431c5350d10cbd53524432c54d4910d3d4f524434c53d49109b58f524432f43d4910cb50f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524426d6314910cbd0c524432d4314910d9584524426e658c9109b196324432f548c910cb152324434f538c910d314e324426e654c9109b195324432f544c910cb151324434f534c910d314d324438d434c910cd15241442e562905109d1954144354538c510e550e31443c5328c5109d19531442b56488510d914a21442746548510d614e30443d2318c1109e1953044399434c110f24c930443d1314c1109798f540425d63d50109b98b540426d62d50108f596540423d63950108fd8d540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530426e6294c109b58a530425d6594c10c7952530431d5494c10c7992530431d6494c10d398a530434d6294c10c7951530431d5454c10c7991530431d6454c10d3989530434d6254c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423f65d0c108f597430431e53d0c10c754f430423f6550c108f595430431e5350c10c754d430423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d53948109b58e520432f4394810cb50e520432e5454810cb551520434e5354810d354d520426f6354810cbd0d520432d43548108f990520423d64148109798c520425d63148109b988520427661148109bd96320426d658c810cb952320432d548c810d394e320434d538c8109bd95320426d654c810cb951320432d544c810d394d320434d534c810e350d320433554c4010d554f100436552c40109e596100435953840109dd9510043355444010d554d100436552440109ed9510043595344010
  | 1 => 0x831e5350f20c754d43c832c5450b20d354e32c834f534cb20e350d32c823e64947208f59251c82ad64c8720b358f21c825e63152209758c548827661152209d584548823e6494e208f592538823e6414e208f59053882766114e209d584538831e5350e20c754d438832f5410a20b358c428834e534ca20d354d328838d434ca208fd91518823c645462097d8d518825c6354620ab992218823d63d51208f992544826f62551209798c544825d63151208f994544829d6315120c798c544823d6315120c758c544821d6315120cb588544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b988534823e65d0d208f197434823e6550d208f195434831e5350d20c754d434826e6590920cb152424826c6550920cb151424832f548c920cb152324826c654c920cbd51324832c544c920d3d4d324838d434c9209b99721482ad64c8520cb15321482cd63c8520cb151214832c54881209798f540825d63d50209d987540827561d50208f596540823d63950208fd8d540832c62550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c208f992530823d6494c2097596530831e5494c20c7552530831e6494c20c7592530834e6294c209b589530831e5454c20c7551530831e6454c20c7591530834e6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208fd97430823d65d0c20c794f430831d53d0c208fd95430823d6550c20c794d430831d5350c209b597420832d54d0820d354f420826d6510820cb55042082cd6310820d354c420826d658c820cb952320832d548c820d354e320832e544c820cb551320834e534c820d354d320838d434c820cd95251083355494420d594e51083555394420cdd0e51083354394420d98ca51083653294420cd95151083355454420d594d51083555354420cdd0d51083354354420d9d0951083644254420d98c9510836532544209b59621082ae6488420cb552210834d5388420d9546210832d5408420d354c21083655108420cb553200834d53c8020d9547200826f6548020ab191200832d5448020d354d200836551480209ed95200826e62d53109b58b54c425e63953109758e54c426e62953109b58a54c423e6494f108f59253c426e6294f109b58a53c423e6414f108f59053c426e6214f109b58853c431f5350f10c714d43c423e64d4b108f59352c423e6494b108f59252c425e6394b109758e52c434f534cb10d314d32c438d434cb10b958a41c4395438c710f14ca31c42b564887109bd89548426c62552109798c548425d63152109b988548426d62152108f992538423d6494e109b98a538426d6294e108f990538423d6414e109b98
  | 2 => 0x6310840c754c421032d52108409bd96321026d658c840d394e321034d538c8409bd95321026d654c840d394d321034d534c840e350d32103565394440d554e51103665294440d954a51103374394440cd50e51103663294440d94ca51103565354440d554d51103665254440d954951103374354440cd50d51103364254440cd10951103663254440d94c9511023d6590440c754e41102ae6290440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401031d5350040ab189401032d5250040cd545401027b65500409b98b54cc26d62d5330c798e54cc26e62153309b58854cc2cd6290f30c795143cc29f6550f30c7d9543cc32e5494b30cb55252cc38d4394b30cbd0e52cc32d4394b30c750d52cc32e5454b30cb55152cc38d4354b30cbd0d52cc34e4354b30cb50d52cc34d4354b30c350d52cc29d64ccb30c755332cc32e548cb30cb55232cc38d438cb30c755132cc34e524cb30cb95132cc32d544cb30e3d0d32cc38d434cb30b3d9532cc34f654cb30d3d5132cc38e544cb30d355132cc38d544cb30c355132cc31d4394730d34ca51cc29d64cc730b358b31cc26f62552309b189548c26e62152309b588548c27661152309d584548c23f6454a308f191528c38d434ca308fd91518c23c64546309bd89518c26c6254630b6580318c26f62551309b189544c27761551309d185544c26e62151309b588544c29d6490d30b358a434c25c6550d30c7d95434c31c6550d30e6d81434c3986050d30c750f524c23e64149308f590524c29d64cc930b358e324c38d438c930e3d0d324c38d434c930d3d51324c34d544c930f2d81324c3c8604c9308f990514c23d6414530c750c514c26e62145309b588514c34d321453097997314c29d64cc530b358b314c39943cc130f24cb304c26e62d50309b58b540c27661d50309d587540c23d65950308fd8d540c23d63550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30c794d430c32e5494830cb552520c32f4394830cb50e520c32e5454830cb551520c32f4354830cb50d520c26d658c830cb952320c32d548c8309bd95320c32e544c830cb551320c34e534c830e350d320c3365494430cd552510c3665294430d954a510c3374394430cd50e510c3663294430d94ca510c3365454430cd551510c3665254430d9549510c3374354430cd50d510c3663254430d94c9510c25d658c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430b6580310c31d54cc030d354b300c35551cc030dc546300c25f654c030c7551300c34d524c030d5545300c27b654c030dc545300c25e63153209758c54c823e6494f208f59253c823e6414f208f59053c
  | 3 => 0x31d24c9500c75b3154031dc8c5500c7593154031dc4c5500c65e63d53219758f54c863d63953218fd8d54c872c62553219798c54c865d63153218f99353c863d64d4f218f99253c863d6494f21c795253c871d5494f21c799253c871d6494f21d398a53c871e5454f21c755153c871e6454f21c759153c874e6254f218f99053c863d6414f218fd9743c863d65d0f21c794f43c871d53d0f218fd9543c863d6550f21c794d43c871d5350f21cb55342c874d53d0b21cb55042c86cd6310b21d354c42c872e548cb21cb55232c874d538cb21cb95132c872d544cb21d394d32c874d534cb21e350d32c865e63952219758e548869d6395221c798e548863d6395221c758e548861d6395221cb58a548863f63552218f993538863d64d4e218f992538863d6494e218f990538863d6414e219e98053886796014e218fd97438863d65d0e218fd95438863d6550e21c7d4d438871c5350e21cb952428872e5450a21cb952328872d548ca21cb951328872d544ca21d354d328878d434ca21ab593218872e54c8621b358f218865e63951219758e544866d62951218f992534863d6494d219b58a534863e6414d218f590534871f5350d21c714d434866e65d09219b994424872d5410921b358c424866c654c921d3d4d324874c534c921e350d32486e4614c921ab992214863e64141218f590504865e63141219758c504866e62d50219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219b988530867a6014c219e580530871e5350c21c754d430863e64948218f592520865e63948219758e520866d65908219bd95420872c54508219b596320874d538c821b9586320874f534c821e350d320863e64944218f59251086ad64c8421b358f210866f65484219dd95210863f64540218f191500866e6294f409b58a53d031d53d0f40d394d32d034d534cb40e350d32d026e62947409b58a51d029d63d0740ab58b41d026e6294e409b58a539031e5350e40c754d439029d6310a40d394d329034d534ca40e350d329025f63546409718d519026f62546409b18951902ae62906409b988535026d6214d40c7d4d435026d63d4940cbd0f525032d43d49409798c525025d6314940b358c525034e63149409b58c525034d63149409358c525032f4314940cb50c525023e65d0940cb14b425032c52509409b996325026c658c9409b995325026c654c940e350d325023e65d0540a758f41502ad62d0540cb14b415032c5250540cb14a405026e6294c409b58a531034e6294c40d358a531031e6454c40d3989531034d6254c40c754f431031e5350c40d394e521034d53948409b58e521032f4394840cb50e521034e5354840d354d521026f6354840cbd0d521032d43548408f596421031d5390840cb54a421029d
  | 4 => 0xb54842d066f658cb419b59632d074e538cb41d354e32d066f654cb419b59532d074e534cb41d354d32d078d434cb419b98a539066d6294e41c754d439065e6394a419758e52906cd6394a41d398e529066d6394a41d358e529064d6394a41cbd0e529072d4394a419bd8d529072f4354a41cb50d529072e52d0a41cb949429066f658ca419b596329066f654ca419b595329078d434ca41a758f41906ad62d0641cb94b419066e6214d419b588535071f5350d41c714d43506b46150d418f994425069d6310941d3d4d325074c534c941e350d32506ae62905419798c505065d63141419b988505066d62141419b98a531066d6294c41c754f43106b561d0c418fd95421074e534c841d354d321078d434c841a758f41106ad62d04418fd95411067765504419bd89501066c62540419b98b54cc66d62d53319b98854cc66d6215331cb95252cc72d5494b31cbd0e52cc72d4394b31cb95152cc72d5454b31cbd0d52cc72d4354b31cb95232cc72d548cb31cb95132cc72d544cb31e350d32cc66e62d52319b58b548c66e62952319b58a548c6cd6290e31c7d95438c71c6550e31e5d85438c7946150e318f992528c63d6494a31c750d528c69d64cca31e350e328c78f434ca31e350d328c74f544ca31d3551328c7c7614ca31f1185328c69d64cc631b358b318c63f64542318f191508c71d43542319bd89508c66c6254231d34c9508c66e62d51319b58b544c65d63951319b98a544c66d62951318f993524c63d64d4931e350d324c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d6595031c798e540c63e64150319b988540c66d62150319e980540c67960150318f992530c63d6494c318f597430c65d6590c31a7592430c6cd6290c31b5586430c63f6550c31c7951430c69f6550c31c7d95430c72e5494831cb552520c78d4394831cbd0e520c72d4394831c750d520c72e5454831cb551520c78d4354831cbd0d520c74e4354831cb50d520c74d4354831c350d520c69d64cc831c7553320c6d561cc8319b596320c72e548c831cb552320c6cd638c831e350e320c71d544c831d3949320c66f654c831cb951320c72d544c831e3d0d320c78d434c831b3d95320c74f654c831d3d51320c78e544c831d3551320c78d544c831c3551320c71d4394431d34ca510c69d64cc431b358b310c795438c431f14ca310c65f654c4319dd95310c797434c431f18c9310c73a5494031ce552500c7994394031da94a500c7695294031f24ca500c73b4394031ce50e500c76a3294031da4ca500c71d4354031d34c9500c73a5454031ce551500c7994354031da949500c7695254031f24c9500c73b4354031d690d500c7394354031d650d500c7194354031d6cc9500c76a3254031d64c9500c7693254
  | 5 => 0x5050e3f6550c4397d954310f1e5450c43cbd0e5210f2d4394843cbd0d5210f4e4354843cb50d5210f4d4354843c754f43d0b1e5350e42c754d4390b1f5350d42ab1894350a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050b4e6294c42c79915310b4e6254c42c754f4310aad62d0c42c794d4310b1d53d0842ab5924210b4d53908428fd954210b1d53508429bd954210b4d5350842abd954210b2f6550842abd8d4210b8e5350842cb54d4210b8d5350842c354d4210aaf6150842ab1814210b2d4294442cb5095010b1e6395332c795143cca9f6550f32c7d9543ccb1d4394732c750d50cca7661d52329d587548cb2c5450a32cb550428caae64cca32ab593328ca3e64946328f592518ca3f64542328f191508cacd63d5232b9987548cae561d5232cb550548cacd6315232e3d8d438caae64d4632ab593518caae6494632ab592518cb655114632abd91508caac6454232ab990508caad6414232b9984508cae561142329d986544ca756195132a7592434cace6290d3297195434cb1f6550d32c7195434cb8f6250d32e3189434ca6e65d0932b398f424cb8d43d0932e350e424ca6c6550932cb151424cb8d4350932cb550424cace6310932e350c424caae64cc932ab593324cb8d43cc9328f993514ca3d64d4532c750c514cb1d43d41328f990504ca3d64141329d984504ca756114132b358e544cae66195132b9586544cacf6355132cb550544cacd64d4d32b3987534cacd60d4d32e3d4f434ca6e6590d32ab592434cace6590d32d3996434cacd6490d32a3592434cace6190d32b3582434cb8f6350d32e3d4d434cace6550d32b3195434cb8f6450d32e3d51434cb8c5450d32b3185434cacf6050d32e3d95434cb8e6550d32e3595434cb8c6550d32e3d85434cb8e6150d32e3585434cb8c6150d32e3d81434cb8e6050d32e3581434cb8c6050d329b994434caae6410d32b398c434cb8d4310d32ab993514caad64d4532e350f514caae6494532ab592514cb8d4394532e350d514cb8d4314532d9544514cb8d43d4132e350e504caaf6454132ab191504cb8d4354132b9d85504cae46154132ab990504caad6414132e350c504cae66114132b9584504ca6e62d50328f596540ca3e64150329798c540ca6e62150328f992530ca3d6494c328f597430ca3f6550c32c794d430cb2f4394832cb50e520cb1d54cc832cb952320cb2d548c83297d95320cb1d544c832d3949320ca6f654c832cb951320cb2d544c832e350d320ca6e6294f419b58a53d074e6294f41d358a53d071e6454f41d398953d074d6254f41c754f43d071e5350f41d394e52d074d5394b419b58e52d072f4394b41cb50e52d074e5354b41d354d52d066f6354b41cbd0d52d072d4354b41c754e42d072d5290b41a758c42d071d5310b41c
  | 6 => 0x518986a383a80007ec3c66fca5a40aa163525ec1ae0669987ac1640001523f878a868a060001a800000001c1000005a898c9da0001da08075ca3600000000051c0000007ce00038c000a426220004203e80000008dc2e2a1800000098800065c0000008809601aa00046e4640000003340002da6e200043c6f092695816040c3d200000083c00e00a00100300200100000200100100000000000000000300100000100000e00700100000000000001000000000000500000100000a00000200600600100300100e00000100000200000100400300200100500000000100000000200100400000200100000000000000000700200200000300100600000100000800200100400300200000700000300800200000000400300200000201600200000000300100300100000200600000400000000000200000000000400200000500000300000100000000200000000100000400100800400300000200100000100100100300200000300100100000100000000200000400000300000200300100100300200000b00100000100101300000000400000600000200000500400000200000800000300000200100400000100300200b00000200000a00100000200000000000000000000000400100a00b00000200100000100200000700000500500100500100200300000100300000000300000100100500000000300100000000000100400000000700300700000100500000800000000200001100300000100100200200100000300200c00200002000800100200000200500200100300000100100800200000000000500000000200000400100301800000700000800800200700100900000400600500500100202000000000000100200100000000000100100100100600200100200000000100100000100000200200200000100000100a00300200100100000000300100000100000900100100000300500100600200400300000600200200100100000400000800000000300000100000000000000000100100200200500000000500400000000400300100000001600000100000200300101600500100b0010030000000000050010040000060000000010050000010000000019b98a51d0e6d62947439bd8950d0e6c6254343ad98752d0eb561d4b43cb54852d0eae62d4743ab58b51d0eae6294743ab58a51d0f355114743abd8950d0eac6254343ab98850d0ead6214343ad98450d0eb56114343cbd0e5290f2f4354a43ab98a4350ead6290d439b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a758b5350e9e61d4d43a75835350eb66194943ad5865250f2d5214943ab98b5150ead62d4543ab98a5150ead6294543cd5445150eaf6254143ab1895050eb76154143ad1855050eae6214143ab5885050eb66114143ad584
  | 7 => 0xb400000000082c00000030060e0c281e26a0000000000000005d02b05466e614275205000000000099669000094829600000043e6d283600009229035400001218a0007000e606e792504a5c5ce1782dca229c461c9783c800036e3a22a659c8043c45523468669760007564880000001c067841600042e0007c65dc0001026bc7120003029046e80003440000005121dc4947ea3dc0004fc00000000052600000000000027e9a203c0000040008e60009b800000000000000000000000000000031a0000007b22245860006e47881565de1443885d80006341fa83e0000000004f869443215a8762523205b80009a076c00026c25c1f647c0742d28b01d487a4820003e400000025ea3080000060600043a29260200093c0008627a82ba78600000000017000037a25800000000000015e000730a560009300003720586169f06468d468a5766626928185cc00020a000000772000578000000000940000992000000a5093e00000051095a2e820e0000000000002a80000000009a60001062a493297a1a472a000000000026000000000000a584e04f065e00e55853e50ea4892a50c35a09c41400a00857447423a6a69be78485292c0000000000000009080001a20000000000000001620000000000000006740009f82f00000000000461b000080a0000000000000600005e000040e64800000000001e00000000000000000029c9cc0002480f20006ba00003a3ee60c0fe0160000009dc9bc2cc63a58ca6476a0000001360003621ca0006c206a7de0003220000ba8820004a80008cc11c7500006c00000000000000003da1c800091a7624aa9f466a3fa0005b000000094c15c00000072c00058a0001105c21049e60000002ee6587f800000082800000000075e0004601e08ba00036a81400013a2260b81ce12424c0000000009f674c54074442a35800050068000016e9289a42d40000006420000002a00000002660000000000000000001dea2600000039200069c0000003303827bc0001208060009168fc92e9d66b871a77039e22059600000000000000081a0000009de00000056a27600079e6680008be77c24e0ce0a800000000000052e00000000077400000000000000000041c0008e80000000000000007f29e20000000006040005d25626520005360000009d814a00073ca545809b06384dca6056c91843645619e4ec0000000000d60000000007209440000000000000000000000000000ae00000093a00000058400028e9ce96e3ae7b41280fc8120005f417e55400000076e3322de88800049e000000a7200000021200014e3aa000278a1c00002a00000000071e0007d80b00a40000000000000008f200000033800011281c6ae0002ce0000000000000000000008fa00086a5fc206000a240004f600070e80c9e00a03f09c
  | 8 => 0x3440400070c83421c95200000000071400000059a0000009ea94e45c86e84a4788d286c5fa00000064e7340000000001d241200068e00066c0ea68c3b6000956a0861e4d87360961083040003400380000000008488f04ce00010c0002720004d0024000a340000000000e27404b80004a2000a140000007964220002f82c6000380a0aa660008164ca5ca2681fc9425022ca0782863168b47fc34e51a4b43663127b61ba724408a020000000000003a462000000000028aa3a0006f600026400000000046a0007c00000000000000f47be0000cc00049c0000004964460000f89140000000000000000002c21948ca36800000003e0000000000000009703d08c890c85e00057213e2425f80c67d06120004304625b496400089c9ee25a0000000006b04a40343fc00029a968922614250640a1e9027f687800000064c0000005f20000645820a20003d60e457a2823e647065a3746609905f000041e0f02006083846888ce27423c78c3fe69a79053097473800091c10a000044a2a7a607ca0c00024454e9340001f44d40005e68864e814896a0007e67d41b66ec2184000007660009ba8305900003966a000000079800000021a6c650a00013000005c000000000000000000000a440008560b631c7220000000006847c207a0006d85e20005b252c8444ae8408ee00092408e8e223250842c0f634c1d87086c80000300007329aa4926320000000000000000000008e067000000078e0000000005ee00000067c8a60000007e060a9ae79a3d86187e80000000000000003107a08de00000011409e99a26e85400082200022c0006da00016600000000000030608685873e12a0009208d000000023442400046612e1766248020940000000008b65e40000001e4000a007820000004481c62d60000ca45800000045a00009a5140002880000003c29c20002940000000009949620000000000007640000000000006440000000004540008ac79c1f82282be4c6002a748ea75800000044200015400000045e8a80d04e49b60007c44f47da5aa0007460006ca0000002568080ee2ea4286ac0004c447e6be0000005920000000000006f200000067647a0006663940000000000004c000024a134a2037e7b04264848fe0000002e08500004729000006b28f419c000a4e0000000000000000009d22e685a5c8000000020a5e5da3480003ec28000090e8100000006a497e00016c4be00019248600000097c00000048000054a6c436c0008900001748a090600012c00000000000000029e0000000000000000001cc57000000018600004841a5c4000000000196000000000000a3c000000000a46210a0401a0004cc0001b8972938912872000000a689108c4000000a2c0000000000006d64100820009fc23821e88e00000000000000000000063c000
  | 9 => 0x8a200000017a00000032e02c57e0000004687040009d477606226044e7dc00602800000062a0363562e400064a00000032600000020c3e29500007d20000000000005288f66260005ea1e86a862e55e2c039a7160420006640003cea2e00032a85c6aa2c40000003ea0bc000000000324a1a3b20009ac0000001326960221220000000003644d62b600000000023600000000000000000000000000098a7066ee000000980398000440314000000000098a760005ba0000000008da27a73a00072e0000009541586fa000548a0e59888c00000072600080e5bc3e02621ec0000000001988963702700005680006ea00030c0000005247c82020008d883853c000000000000000a4000000000000065400000000010e15000000019a88a0000003289c87e404000000017c32c0000000000000000000000000000006de0004da0003361bc0007604ea3900880008988f80000000000001b20007680004b600089e06800000077a84c0000007b80007e20000d20001f00006980007ca0003180000000000001d600000000006c0703ca2400000004c20000006ce00071c0000000000009a817200011e2160001e200005623e0007ba0000000000000000000000000002fc0000000000de87000044a00000055000048e0003de4b00000000aa55a00000004e7d60000005d40000000000000000000003420000008207aa0d86d031e5d639c5a600087c1381be4bc2083500000003f20000000fa71075a5440000008608643b461a6b48ec2fa0d40001162b88260008428e43b800000000000095e0006cc37618e0007f00000000002988b863e5fe22200000045246c00087e00000035e0000000005a269e00000000000083a2d00dc3860e0308000000230090a6299e0c893600053274e22a0001b445000000000022e2f40006367020004020ac0180005e800000000000000004a00000052a99c6b600082a9f20000005ae5945885420004fa78062c7a237856e40600000007e00000008c0007fe7ee00012600084e9e4a32000a3e5160000009823b051e1680005c049a0006a20000007426e001000060000002e0e800033c0009465600001a60000b20ec0001ea77ea6e0000008aa3f60000008c2000a6c0840005be55c0000000000000001c40000000003cc0000322b253a00000000014066e0007cc0005c62843a63be7782142c8a1038a68267e3d47546561885a433a00090a00054c1fe5a000018c000000a4a0002f60000001808920000007a4000000a522ac94a0006301460000000000000000000000000000000006500008a40009e837c0004908d600000030e6860c448a0000007487ae67a6dc4d2000a6a11a0764e60000009c613c00016a0002d84762ec8240000549ec1ee1c24a04a63ba0000008940004fe7948bc1a00000000145
  | 10 => 0x88433e56674a0008748b29b4a7070a00000000048c1ac27c9fa28c9d03a00005647280007fa0008ae0004340007180002bc00004c00035c5380a600000011814c3609b282e25400089a0002fe6720006d46f400005a00000000008a000000a280000000000000000004c800095c34a1f27f40000000000000000004e24182a24f24b25200be0000726fe9660009ca000000a4c0000000000000000000008c000098e0002ae61000018291e8321e60004de0002aa6280005564ee2f20da59e00005200000000098438e9fe0003f45223bc1900008c63ac00000000058e2b457c00c1d00006f824605e0003c0a1244400000000000044c4380000000000c000000000084600000000000030a0000000002040000000000000000004ac0005060005ac0000005b60001844ba00000000096c0000000005f649800000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x18d4970d51320c686baca899063c250d5294031e12a8994a018f09434ca500c68dbaa86a8063c250e5254031e1286a92a018d4b754c9500c7852a264a8063c25513254031a92e521aa018d517190d500c68cba664a8063545c73254031e1287192a018f0b434c9500c784a1a64a8063465d33154031a92e598aa018f11438c5500c7a099462a8063c4d0d3154031e846498aa018d0d7318954c8706aa2c621643435ce544cb21a1ae929a6590d0f7550d32c8686baa8699643839c96395221c1ae4b1ca910e0d6358a548868cb80a6a1c43435ce5490a21a1ae72a28510d0d739523288686b9ca899443435d5434ca2185aed2a64310d0d7395321887072a2c790c43835516310921a1ae829a6490e0c6550d3248742a18c299243235ce648852189ae7316a810d0d731514208694b80a8a1043075ce649442183ae6322a010c4d7398a51d0286b94a6a1c81235ce6290640c1ce8b18a4a060d7458c5250306b1e86292818358d4314940a1ae629684a050d73149425030732a8699281435cc52d0540c1ac629682a050d731494150286b98a520281435ca5350c40c1ac6a1ca42060d635484210307b2a8699081c150d3294440a2ae6212a220705434c95110246b9cc5208818354e6290440c4cc4a8c822048d731894010306a98c4a0081891895150040a1ae432a869859171181434c2a238aa899261705c4604c930c1a86b10a29860d644c8514c286ba4a69906143dd5434c830c1ecaa1a6418705434ca510c382a1a64a886186551600c430c92a4b00621850d7315142c820eb9cc928e4183d516310a20a1ae929a651048d739922188307392c62a241835c96315120c1ac6b10a89050d7294d434820e3b2a6a1a41451c55350d20a1ae62a4849050d731514248286b98a919241435cc544c920a1ceaa1a649042d761532148286b98a990a418315163c8520a1ae62a2429050d731522048286b98c4aa041435c95350c20c1aa8b18841044d7654c4208286b9ca899041435d2534c820a1eeaa1a641050d7550d3208382a1a6528841515cc4254420e0a86992a21048d739922108217bb2a910841839915388420c4cc8a8c421048d7319120082163b2a890041831915348020c48c8a8a401044d7398b54c4286b90a6a1e21075ce64d4b10a1ae829a658844d731895484286b94a6a1c21075cc6454a10a1ae929a650860f64d8b5344306b22c429a21865916014d10c92c4b00a688651615805344286b90a6a1a218358d4314910a1ae62a2648850d7414d32442873aa8699221431d5434c910c1ccaa1a648860c6550d324428a3aa8718a21511d5328c510c30caa1a6088648654c93044306b22c529821835916254c10a1ae529a860860d6350e5204286b9ca899021435d2534c810a1eeaa1a640850d7550d3204307b2a869902183595434c810
  | 1 => 0x5992c0084070c18cc500378947c1e1c96e686a031a02e211dce0693d801b8d2471d9240f44a8000000021c9a6100000000013a5c006d6fb1c24b50280066b4378007c5a2097916c828930560d000d010640036400be5fb340099560fd72bb2b0e8880000024c420583840e0002294f4004a148007f0b000000000208cc382d80000d554ac8001c5782844bd6b9a8fcc0002691ed866064424e38ac53add0022048580ab6dac6e339e5889e65b24c0484800c8c2553a88ae40152d95c1f4a86802a42f8c8b8ce0007570114c174cad34f85c7aab65060f02c3e8a4629c452303cba298e400915e14026da519ac9e815502c281022b0486a636200002300388002d000991a750011d3636141640000002a000cf179515a730006c92c36115400e00024d0c8531b44e8a10300106001b8d47696010b8030000816211b004180d0181806430a07c16000b8180e05058003400018001203010480404078201405050840a0002800000b010580604000000c02000281e040c00004000383c18130080c02090780c121c0048d729875350e47b92c1a9a87455c66454c42a8ae3312a62160d5358b4310b07b1aa6a108583d955350842c1ceca9a842148d73d854210b06a9ec2a1085235cc6050842c1aa630284214a5711814210b06aa2c62a465459c76550d32a18eaa1a849948d74987534ca47ba2c1a9a65319c66550d32b0ce3b2a869958571d95434cac338ccaa1a65615c66550d32c1aca32a869950e75d85434cb42b08c2a1a6561dc56050d32b08e2b02869950e75181434cac3388c0a1a65615c46050d3291eeca1ea29970543544514cb42a1ec2a8265a150c615413291eeca18a09968543984504cb42a1ac228265435ca5350f41c1ac6a1ca5a0e0d6354842d0707b2a8699683839d16394a41c1ae8b1ca520e0d63d0e5290706b1a8729483435ce52d0a41a1ae72928520e0d6550d3290686b9ca5a0c838358e52d0641a1ae429a86a0d847150d3250646b9cc520a83135cc6254041a1ae5b2a8718e0d43d89508c707b2264a846383595438c831a1aeba1a64
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x51820281044b5825800038c080003a05819d95350842c05535c46050842a05819d16394a41a05819c9639522180d8795163c8621a05819d16314940a05839895190440a05831895150040a05819c9631512080d8715163c852080d879915388420a0583991518842080d871915348020a05831915148020
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
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
  | 6 => packedAt s3K6 (788+((h/14+packedAt s3K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s3K5 (27286+((h/296+packedAt s3K5 (24030+(h % 296)*11) 11) % 1069)*11) 11
  | 4 => packedAt s3K4 (56272+((h/446+packedAt s3K4 (50920+(h % 446)*12) 12) % 2352)*12) 12
  | 3 => packedAt s3K3 (11798+((h/75+packedAt s3K3 (11123+(h % 75)*9) 9) % 273)*9) 9
  | 2 => packedAt s3K2 (860+((h/4+packedAt s3K2 (840+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe3ffff0ff87fff83e1fc3ffe1fc1fff48f27f
  | 1 => 0x3fc1e1ff0ff8787fc7e1fc387e1fe387b74d93
  | 2 => 0x3ffe01fff0007f8ff801ffc07fe003f8c78e1c
  | 4 => 0xc00001ffffff800ffffe00007ffffc00f80fe0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2000010000800000002004800240080001025
  | 1 => 0x41442222500a0814220c41122094116134492
  | 2 => 0xa88cd5446355541ad9116a827540ca72c58e18
  | 4 => 0xa1a919888a44152cad54220459929820e80b40
  | 5 => 0x3131910ecc66664f3799b32711031044fee000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeeea8a8eeeeeaeaeeeea8a8eeeeeaeaeeeea8a8eeeeeaeaeeeea8a8eeeeeaeaeeeea8a8eeeeeaeaeeeea8a8eeeeeaeaeeeea8a8eeeeeaeaeeeea8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36330
namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x921200b800018000287400000006804aac01c4439502504138b368c426180c0112a110160069485001c0184800c803c0108a007c0131e3001c3011040000100000ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x661dc42cc3bea3987794730eea8e61dc51cc3be83987790730eea0e61dc41cc3be43987788730ee90e61dc21cc3be81987790330eea0661dc40cc2fea9185f95230beaa4617c548c2faa7185754e30efa1c61dc438c2fca5185f54a30bf28c617d518c2fca11877cc230fd984617f544c2fca8985f55130be2a261df434c3bc86987750d30ee21a617f524c2f8a49877cc930ef19261dd324c3b864985fd4530be28a61df314c3bc6298774c530ee18a61fb304c3bc609877d5130ef2a2615e544c3baa8987715130ae2a261df524c3bca4987754930ee29261df424c3bc84987750930ee21261df514c3bca2987754530ee28a61df414c3bc82987750530ee20a61df214c3bc42987748530ee10a61df504c3b6a09877d0130ef20261dd404c3b880985fd5030bf2a0617d540c2f8a8185f94c30af29861df430c3b886185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20efa1e41dc43c83dc85907b50b20bf28e417d51c83de43907b48720ef98641dd30c82fea9105f95220beaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53883be87107710e20bea9441ef42883d885105f94620bea8c417e50883be6110774c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483be86907710d20f721241ed42482fea2905f14520f790a41ed21483be6090774c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53083be86107710c20bf29041ef42083d884105f94420fb288417651082faa2107d54420baa88417e50083be6010774c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10efa1e21dc43c42fea5885f94b10bea96217c52c43ec83887d50710fb10e21f521c43be6188774c310bfaa4217e54842faa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10efa1c21dc43842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843be6108774c210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53443be86887710d10bfa92217e52442faa4885f14910fb20a21f541443ec42887d48510ef98221dd30443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10efa1821dc43042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dd0410fa208217e50043be6008774c010fb88021fa10043ea20087e44010
  | 1 => 0xc43906fca520fb94a41b7294837d52907daa520db54a41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0f7d0d41ee21a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d53107be8620f710c41bf290837d52106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998df55331be2a663df43cc7b88798df94b31bea9663df32cc7ba6598df94331bea86637f548c6fca918df55231be2a4637d538c7be8718f710e31bf294637d528c7bc6518f70ca31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31efa1863dc430c6fca418fb94831b7290637d520c7daa418db54831ef19063dc320c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43df43c87b88790fbd0b21f621643ee32c87da6590df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c43df43887b88710df54a21bf28c43f741887e88310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53487bea690d7d4d21bf29a437d53486f8a690f714d21ae29a43df43487b88690fbd0921f621243ee32487da6490fdd0521fa20a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610f7d0c21ee218437e52086fca210fbc8421fb10843ed21087ea4210f948421bf280437d50087bea7a05f94f40bea9e81dc53d03be87a07710f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa72077d0e40ee21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53503be86a07710d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881df43103b886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330efa1e61de43cc3ba87987710f30bf296617d52cc3be6598778cb30ee99661dc32cc2fca3985f54730ef98e61de31cc3ba6398770c730efaa661de54cc2bca9987755330ee2a6615c54cc3bea5987794b30eea9661dc52cc3be85987790b30eea1
  | 2 => 0x4ca000008000080020000200300c014018000020000080000a0000000e000024000000040040100101200001800000000000000000080000000e0100000a000000000000020240000400000005801014008060000040000000200e000008010020000000a000020030010020140080000000002800010010008060020000000100000800001006000000000080000000000000000802002004000010000000780300e00c0280001400002005004010000090000000000100a034008030020040180000601c000000060000000300a0000080000401c02000000004088010020000000100c0380100100001000800000008008020000740100700800001000004000000000040080000000c000000000000000180000000c008000040040500300000000006000000040000000140000000a00400000002008008040000000080000000c000000000040000100a01000005004024008010020000380000000801001004014018000020140080200000000df94b43bea96877e51d0efaa3a1df94343bea8687df52d0fbca5a1f754b43ee29687df51d0fbca3a1f754743ee28e87df50d0fbca1a1f754343aea8687dc50d0efaa921df94e43af29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea8087de5410ebca821e795043efa9087de5210fbaa421f714843efa8887de5110fbaa221f714443efa8087de5010fbaa021d754043ee280877e53d0afaa7a177d0f42ee21e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42efa1c85dc4390afca5216fd0a42f7a14857e5190beca3215d94642bea8c85f55190aeaa3215f94242bea84857f5350bbea6a157d4d42be29a85dc5350ab8a6a177d0d42ee21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310bbe86217710c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665df43ccbb887995f94732bea8e657e50ccafaa1995fd5232bf2a4657d548caf8a9195f54e32efa1c65dc438cafca51977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbb886997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cbbe86197710c32bf29065df320cbdc6419774c832f6990657e510cbeca2195d94432bea8865f5510caeaa2195f94032bea80657e53d06faa7a0f7d0f41ee21e837e52d06faa5a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41efa1c83d
  | 3 => 0x78000b9c21184000aec000f5000768ae1ac2ac00058000000000002555d2000001bc00046ccba8f2e688d65800000000002a41822a0000000003885d1054186540c86527e47c0024a0000000000000000000000254000001240000014c270404000000504c00004c2cd0000c4940d80000000015f000000002d7000b6c4e0000005e400000000318000000000000000008eb8d310000fe0011700028a0000000063a0018014a00000000086000ad40000034a41cfe800000000002830002fc000f158a81cda190106001878df516000000f42e0698002a708800000068146001009ca00049400000000648ca0000000013c8000009600004a000c6c00000000b840027f000000001dc000c7c000000000a0002090007ec0000004c000002ac00000000000364b18000000009f40000000058cd79a00000000000049a89800000264000000000000000003c4e29dc0024e000209188002f82054ba1730e52000000436548b2a4f3ec000a38f0040634000003ba48800000574911110761a0978000fb16c000000002d6b942d8b855c220000000007e4c78000000015e80014c0000000011e8f020203000000000ca000a84db8af2b021400000000bdd450003b20011d966282000000002d2afcd0ab13cc0001380001a1348e80000066d4f29f000000000000000000015300000080a68000000001683da0f533a6900000000000266000000576283a47b053452909370000000000018a000001129c200040c4e8003f81643a0004cc2c89e0b70000a800000280000002df068590198ff3220000718221a4e1489390001a84382105c6148d0006208e9490005a608800000000b0077a350000008a1c663000053aaf000210000000000000014e19c660811c151a000758000000016a80035600161000386311750360ba0011f000000000a100042c0006b0000000000a8c80000016c9be2fcb508e29d5947e04ca494ec000000000000e0aca2f638000a2000430000002340f63f4b3af00000000030d4d8540c71800000001801760e000001b62ee72c0019917a9e80003e000000000000000003e8000028d8230005081bc000aa00096c00000000000002940b88390a18645a0015c8000226b4a18e06080e40000f33a4d52b80025c000879714a000106a060002f95f0c737a00000000000b0c002515d60016d00009e5758300007e3f0000003445e8f61063a2000aba5239a3080021e198000002ed0000b4b68000000009f261380025260000005515c2e64ea80088800000b300000000039800256624000000003c20000b2fa000000000000769f0a7a3361c000000005ac00051000038000b019e000315318000007484aaf300095091acf000000000000dc0014b31a17612400000000000d20001b8000b7000346000480000c2374872ad0000009e8b5
  | 4 => 0x4b5829bc000000000011b8004b24d800000116000f8800000000002d00000007d0000005b1142b45fc0018899f000460f214c2684a4002896047545e06b4d4001580001c82acbc0000007c0002d248ebfc73aa00268644f9d61d06d5090f70000008c800000000000025a22cc00000000a04000b40002b5219cc0007f9702862001f0d88ed2c400000000118484cb1f3490890472412580000000a0000017e1ae0007fc0031e3be870e7000000000002ef0e000000115000000d98000001300000000000000000000190f78253ea69c001b00000008b8002f6000000d3000ba0c605f00071493a6d3e435c0004e1a4a6d7203a0000014000005842095a461364b4338d441064c0000b00073c00000000000021c80c089cea215456af0001a90f2a980015122400014ade0000bd1e800000234c402b0e4b1c981bf152bc5808751b2aad2d13a5380000000000074c71a6b0867a00000000000000000000000000004fc000000a55f2000dc1a800000000000000020000004f00016210c414000000002d43c96e07a13c94c2b0000001507c80022608d5b80047ea64a48000000014397f3ee6a86d99c0000017d8c900000000000000000001e52e8c596ea7300000002a1333442800000590c8000274440000000000003b1150000d800000000000000669fa1aa0018580000047800000018000001d056688449af624c00060000140001258006141898aa051e600000000000000000ac1f0c0c0e8c36182e4e3972534224240375925d52e0452b4000000000a28b1840003b6440fa0322169157a05559ca940d8ee19e25105aa9134724e212051879c00239196000000000000000000056c000002322fa000001b900052c002850001989d9de6261f98286d2aa4bd49aaa162000000002b68117625f000050208000009c9181e0000000080001d40000000000000000058142000400000000017121d5fa018002f5000a896c02428c7a97c000000a08000a4612000c4835000000ec000024604000002dea2108873030000f1a1f26225d32077000000002902bc0000000003c0000005a2c2c5c0014d546aa0001833dc4dc0f80048000000000000069591ba00000000091000000f48001fc36800000000378038003d6000003190000017920f0000011c0001c284000052124394349bb000000f11160000000000000000000000000a54eb8000bc62c000004ba25868800000228570000c60000028e0000010d0004f600c002ee0e2410bb000212000000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530825e6494c20c7951530831d5454c2097191530823e6414c208f590530825e6314c209d98453082756114c2097d97430825d65d0c20c7953430831d54d0c2097d94430825d6510c20c7950430831d5410c209b597420832d54d08209b594420832d5410820cd95251083355494420d594e51083555394420d5d0e51083544394420cd95151083355454420d594d51083555354420d5d0d51083544354420d9d09510836442544209798e500825d639402097597300831e54cc020c7553300835651cc020d5547300825f654c020c7951300831d544c020d59453008355514c020cb553200836551c80209bd95200832d5448020d9545200827b65480209798f54c425d63d53109b98b54c426d62d531097d8d54c425c63553109b98853c426d6214f1097d8d52c425c6354b109798c52c425d6314b10b958a41c436452487109798f548425d63d521097d8d548425c63552109bd89548426c62552109798c548425d63152109b988548426d621521097992538425c6454e1097d97438425d65d0e1097d94438425d6510e10b6580438425e63d4a109758f528423e6414a108f590528425e6314a109758c528425e63d51109758f544425f63551109718d544426f62551109b189544427761551108fd91534423c6454d109bd89534426c6254d10c7d50434431c5410d10b6580434423f64549108f191524425f63549109718d524425e63149109758c52442766590510b958a414427465505109d195214436452485109798f540425d63d50109b98b540426d62d50108f596540431f6395010c718e540425f63550109718d540431f6355010c718d540433461550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530425e6494c10c7951530431d5454c1097191530425f6054c1097581530423e6414c108f590530425e6314c109b988530426d6214c1097d97430425d65d0c10c7953430431d54d0c1097d94430425d6510c10c7950430431d5410c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520434f4394810d310e520432e5454810cb551520434e5354810d354d520434f4354810d310d520423e64148108f590520425e63148109758c520426e62148109d984520427565d0410cd553410436552d04109d59441043355410410d9548410425e63940109758e500425d65cc010c7953300431d54cc010d394b300434d52cc01097d95300431e544c010c7551300434e524c010d3549300433554c4010d954b100427965840109dd9510043355444010d9549100427b6544010
  | 1 => 0xc2d661d5330b558754cc2d960d5330b658054cc31e6415330d658054cc2d960d4b30d354852cc2d66114b30b558452cc2d96014b309799642cc25d6590b30b598642cc2d56190b3097d9542cc25c6550b30b658351cc2ce6214730b358851cc3555114730b658051cc25e65907309759641cc2ce6290730b358a41cc25f65507309719541cc25f65487309719521cc25e65087309759421cc3c52108730c795340cc31e5450330b3d8940cc2cc6250330b5d8540cc2d46150330b398840cc2cd6210330b598440cc2d561103309b988548c26d62152309d984548c2756115230c7953438c25f63551309bd89544c26c62551309dd85544c27461551309718c544c25e65d0d30c7153434c25e6590d3097195434c27661149309d584524c34c524c930b5984324c2d5610c9309b988514c26d6214530d5145314c2ce620c530b3588314c2d9609513097992544c25d6095130d6582544c2cf6255130b3189544c2d76155130b5185544c2db6055130c7990544c2d96094930a7d91524c29c6454930b5d85524c2d46154930b6d81524c34d5214930b5984524c2d5611493097996424c25d6590930c7152424c2d66190930b5586424c25f655093097195424c31c5410930b6980424c2d96010930b6582514c29f6454530a7191514c2cf6254530b3189514c2db6054530b3988514c2cd6214530d5544514c25e659053097596414c31c5490530b398a414c2cd629053097d95414c25c6550530c7150414c2da6010530b6580414c25f654853097195214c25e650853097594214c3c52108530c7153404c25e659013097d95404c25c6550130c7151404c2cf6250130b3189404c2d76150130b5185404c25e6510130b3988404c2cd6210130b5984404c2d56110130e6500404c25e63d503097d8d540c25e63150309b988540c26d62150309d984540c275611503097992530c25d65d0c3097d94430c25d6510c30c7950430c25f654c0309ed95300c35a534c0309798f54c825d63d53209d98754c827561d532097d8d54c825c63553209d98453c82756114f20b958642c825f63547209718d51c825e63d52209758f548825f63552209718d548827761552209d185548825e63152209758c548827661152209d584548825e6494e2097191538825f65d0e2097597438825f6510e209759443882d96010e209798f544825d63d512097d8d544825c63551209bd89544827761551209d185544823f6454d208f19153482776154d209d185534831f5410d20c715043482d96010d209b99642482e561909209b195424825e63145209758c514836451485209798f540825d63d50209d987540827561d50208f596540831f6395020c718e540825f63550209718d540831f6355020c718d540832c62550208f990540825e63150209758c540826e62150209d98
  | 2 => 0x54d0e31b5584328c66e62951319b58a544c65f635513197997434c71c54d0d31b5987434c65e65cc9319798f540c66e62d50319b58b540c66e62150319b588540c67a60150319e580540c65d6510c31c7950430c6d56110c31d3d0e520c74c4394831d3d0d520c74c435483197596320c74d528c831d3548320c6d5610c831d354b310c765528c43197d95310c74d524c4319dd95310c765524c4319798f54c865d63d532197d8d54c865c63553218f99353c863d64d4f21c795043c871d5410f21cb55042c865e63943219758e50c865e63d52219758f548865f63552219718d548863e64d4e218f593538871e5410e21c7550438873554106219798e508865d63942219798f544865d63d51219798e544865d639512197d8d544865c63551219ed815448678605512197993534865d60d4d219798e534865e6514d2197990534874d6214d21d5584534865d6014d2197997434865c65d0d2197994434865c6510d219b99742486e661d0921d314e324866c654c921b9185324867665d0521b998b4148754538c521f18ca3148674654c521b918931487c5324c5218f990504863d64141219798c504865d63141219798f540865d63d50219b98b540867661d502197d8d540865c63550219798c540865d63150219e9805408679601502197596530865e6494c2197582530865c6454c2197d81530865e6314c219b98853086766114c2197d97430865d65d0c2197d94430865d6510c21d354f21087555388421b958a210866f6548421d354d21086776548421d554d21086e76548421d9d9521087665448421d915121087c76348421f118d21087675348421f194d21087655348421f154d21087455348421f1d0d21087c443484219798e500865d6394021d948550086d960d0f40b658043d025e6394b409758e52d02766194b409d58652d025f6354b409718d52d025e63947409758e51d026e62947409b58a51d025f63547409718d51d025e65d0d4097994435034f53d4940d314f525034f43d4940d310f525034f5314940d314c525034f4314940d310c525032c52d0940d5d4f515035453d4540d9d4b515036452d4540d5d0f515035443d4540d5d4c51503545314540d9d4851503645214540d5d0c51503544314540cd14741502d960d0c40b6580431034e5394840d354e521034f4394840d310e521034e5354840d354d521034f4354840d310d52103565394440d554e51103665294440d954a51103574394440d510e51103565354440d554d51103665254440d954951103574354440d510d511032d52d0040cd547401023f6550040cb549401033551500409ed95401039b43500409b98b54cc26d62d53309d98754cc27561d5330c795043cc34d520cb30b598432cc2d5610cb30b398831cc2cd620c730d554431cc2ce62d5330b358b54c
  | 3 => 0x11fa1eeb640c2543c2b1850ae15329c017a443d044069a7f5d6940969002aa595069f25743e0319314d49a4b813d2a4b396da1c1ca07035a860000001d82801800000030300d000050040102403000170000008c0d0540d0001400c1700c25000050042b000080a8000380706c1a00001000170140000000000000280f0280d0340501c0000403034000400200402000120040a0100000804044180340a01c0f004000140b014000d4070000000800034140140000830000030400400801000030d8070000a0001e028140000010c0000c0000001000100501100c0604c0e00800000040240000801010000202114c0a01008008020ac030000800003000050280100014000001740000007008270002a0040201458008000440202008004030100604c000040000000034350d403014000385600002008210004c0a0150040802c0200c030080301c050000600810014000840e0980c00c000840007c290002a0102707c020140a044000781300011000060440e0100b01c03000060043d00800022766194b439d58652d0e6e62947439b58a51d0ed661d4b43b558752d0f4f5294b43b598652d0ed56194b43b398b51d0ecd62d4743b398a51d0ecd6294743d5d4651d0ece6214343b358850d0ed66114343b558450d0e3f6550c4397d954310f1e6495043d35485210ed66114843b55845210eda6014843b65805210ece6214443b35885110f555114443b69805110ed96014443b39885010ecd6214043b59845010ed561140439798e51d0a5d63947429798e50d0a5d6394342975825390a5f6054e42d594e5190b555394642d5d0e5190b544394642d594d5190b555354642d5d0d5190b544354642d9d095190a5e63942429758e5090a5d60d4d42975805350a5e65d0d42979944350a5e63141429758c5050a7661141429d5845050ae561908428fd954210a6f6550842e310d4210a5f63544429718d5110a5e63940429758e5010b1e5410f329d987548ca7561d5232c7953438ca7661951329d586544ca5f635513297997434cb1c54d0d32b398b434ca5e63d50329d987540ca7561d50329d984540ca7561150329e980540ca79601503297594430cb1e5410c32b3588430ca5f654c8329bd95320cb574394432d510e510cb574354432d510d510cb573254432d98c9510cb553254432d94c9510ca5e6394b419758e52d065e63943419758e50d065d6094e4197d81539074e5394a41d354e529074f4394a41d310e529074e5354a41d354d529074f4354a41d310d529076552d06419798e509065d639424197583535065d6014d4197997435065e6510d419798c505065d63141419b988505066d621414197d8d521065c6354841b958a411063f65504419dd95411079443504419798e501065d6394041c795043cc66e62d52319b58b548c71e
  | 4 => 0xcca0361ce92c208e11ea7005a1fb1841ec002f335cb793025900076825aad5ec8bc87aaf212bbc6f97347c840c227b0a2001120ca166000658612e2a408f2e810407c3b0730da0341218549e4895f00025600107ac00002c00000b0008305621318c1d021a9a04ca24022e03888fd5aa7c56e8e4571df0ccaecd39950b29793a25d3ce314ae90248e780cda9147850d769ca3547bd74a52000000732c11ae040720fa48490d7a0ce506448bd99808c559722ac2100752fa120002b4000a24980014f0000009851a00060e000dc09908a7149a8004aca5d4423a032180f980002a72ccb99e30c004f51ba000000002110007953c1d94648b415ad32500200002c2c64d0000521544a4001752064cccf800548000000930000008bab861200037ac22f80000028b412a016baf93a04148508701cbf4148000003fc771400007b4d42d52a2ac4001230001b8002933461b11e90c1561545dabc3a6000002b93ac000acae360c1102118b0425242385d192000000344b0304c62190000000009b000914000001a0158a715f45033181800234881598862fa2e80020e03c3bc950050007b0449a5446b20ad00050a2786c8a81e01c05e8005c47700019a0fc000b7a0517c0003f91f0f4bc532813000000b019644214d4d91d20219c002413ea6c4d48c70002f00000011816d5eb053868211529f54c30c049262ae1e0a8227614a60e71c84aec102c13b15272444038434b453eaa24ea360a402501e6989c8f3054000d993c320b94fb8000000012d930074000d813854e374198000907d80b0005960000029d36478816acd54a41c001a03000016d0370ea001841044e6bf8792dd1227e17e0351c0204000001465a00000042c0000000056838cb52ff59e1f4a520149c25cf80e80009e4df2714609180014528206c002821aa4707509c58a0017b8000001c4000002c2000dc83e39e5c83e2673a49692899919087d7508a4c4754002920a80000013f044954478002b80000026b0000002f09f2f42694380a000068c704a06053cb605f170001331a200085ca31183569913698d4c6000000000f25ad4a800476168001a42a66bcff000000a30000002ec3ec7493724a9b05baf2274888d689000080c490cd43a778df9f451cb0c000683d6000532a9000000000002e809c001920007f14a0000d20001e1585eaa8cec0a40d4620000f4604000832e73688dc5f82e36e00c0000000071cc10dc298670f21ff2b6464e680c1d67b81918a5f45fc32ad80042c8992ee16a0004c000240001050005087a4ed8fc11ab249b03907a35150ac7000000000b1000ac0d604d3229f9478001ac4583225c1ec1013b2d21b4080de00049015c962d6108624f310d4a6924b21fd5a00c452b00382b70e887252c42cc99155942bd3d2725e03f4db22c41601d6623357e684a
  | 5 => 0x13893ae60a044c031441b6000ee86240c2514e077456a298628d2da8c42e2074ee674f8a141c400062281046450001b525eb51858d1000300b10001bc8a40014b4d09bd1c2155d8050e330143cab8260f12cc33d1292e3986f4c38d2000124e108514013c141d75508b85ca6e2228084e9472d25e4922a056c9296f88b30286cc19541fcbe16214d3767e476ab22ee5e10209516c5b90c15e3c60008daaa3a8aac1f81227c0009096746c0012008e21c3e400000022000c78801d8000000a70008984b24d46a5f97d81740020
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1a0300880132c3d1804c017056ab0107320101b0001b090074015000001a00a1380007800600a57ab2000894240198100c0bad54300000000000423800800340313e2800000912b200dce0b0060200030604000024048002003080000003a8ce3a94a5a1e475258652d0ea3396a328e879158b5194743c8aa4b08a421e49525805210f22b12a22888794545601444398ae331686995457210d510ca62b94c3a1a63515c44354831c8ac4b08a690c59701944348662b9cc3a1243315ce62d0521a8ae62a24210d617015121086a2baca690843519d95348421a88eca9a4210d447454d21086a3b82a690843319db4348421a8eeba1a4210d457510d21086a4b8086a9081545c04354440c8aa4b0865986456254431cc30d322c02a661915496114b30c8ac4a88a3986456548421cc2a2b88a499261515c8514c530a18e8a90a49854471548524c322a92c229261851526190930a28e8a88a29854472544514c322b12a228a61831526290530838e8b28429854475484214c322b2a4210a61831506250130c28a830a809868962500404c348b0a8020261861516010d20a8ae628a42905457314921c430c2a2c021a21515cc5248510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x60a40208000906849d9534842184686dd74348421a04845496114930c04745895114530844875952108530a04845952108530
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (24564+((h/267+packedAt s4K5 (21627+(h % 267)*11) 11) % 1406)*11) 11
  | 4 => packedAt s4K4 (32278+((h/260+packedAt s4K4 (29678+(h % 260)*10) 10) % 938)*11) 11
  | 3 => packedAt s4K3 (2870+((h/18+packedAt s4K3 (2744+(h % 18)*7) 7) % 89)*7) 7
  | 2 => packedAt s4K2 (368+((h/2+packedAt s4K2 (360+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff87ffffffffff81e1e1f87ffffffffc063fff
  | 1 => 0xff81f8f07ff0ffe01fe3f8e0f0ff07e39d273
  | 2 => 0xfffe00ff83ff0fffe003ff00ff0ff83c1e39c
  | 3 => 0xf000000fffc000ffffffc0000fff0003fe03e0
  | 5 => 0xfffffff0000000fffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8082010002000020204012221112100204a5
  | 1 => 0xa51245123294549608ca1a84458aa16a18d252
  | 2 => 0x4621492451a845aaca082b2089a8cd0ac16318
  | 3 => 0x64759648a50e66cd6d6c82012ecc86336e03e0
  | 5 => 0x88461800c630887191913449c0000841b5b800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36330
namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x624c00b00013251c0179c00740070001083223cf9e0ca0b0000684aa145090c1a80c8404b5600005482452011a25c015800000da70060b8000000010015808000004001063430504000810408205ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1167000004ea662d158008a2e8080000161c89c3d001f05c8010889280004000009f138009600000000000000cc0017498012c1e1c15c242002840fe1620260ce59421d8dc5f0018ca683230000077511ec009c2a80000003080000000011c0051159603886190d90200001e8000005268000300000000000064000b001149400000000000000000000001a8c80000214007900034dea42400000000000000000000000000025540261c80000002d9b13a354b8000000000000000002380000001ad0e00001f45400030680025260011000398001c004900000000000000650000000003f00000340a80092000000000281213c126200000003718a253642268000082039b45e0002284003c001791a002e1a5461114800e23e001d00054078012000001493c50118507e8f3c0000000060013241001107468000ec00180007400000000000910000000000010c001b000003e0000000001346180002d000c000000000804010000406010000601010000202000240002030000001000080601008000000000000601000040a04008040200018080207010040a0400838000000db94b43b6a96875e52d0f9ca5a1d394b43e6a96875d51d0ebaa1a1d794e43af2a0879e5410ebca421d754443aea80875e53d0abaa7a15794e42aea9c85765190aeaa32157d4d42ae29a855e548cab8a9195794a32aea8c655d508caeca2195d54432af2a0655c540cabca4197394832e721065cd420cbaca2195754432eaa886555510cabaa0195794e41aea9c836e52906daa520d7d4d41ae29a835e53106baa620db94841b6a90837a50106f2a020d795331ae2a6635e52cc6baa198d754e31b7294636d528c6bca898d715131ae29263d7514c6bea098d794c31b7290636d520c6bea790d714f21e719643cc32c879ea790f314f21e7a1e43cc43c879e6390f34c721af29c435d53886daa510f54c621afa9a435c534879c6490f30c921ea98a43cf5348798a690f3d0d21e621a43e751487ce8290f910521e798a43e6314879a6290f94c521e298a435e53086baa610db94821af29c815d53902bea6a05714d40b7a92816c52502eea2a05d14540af298815d53102dca4205b54840bb288817551102bca9985715330af296615d51cc39e43987348730aea9c616f524c2d8a4985795130ae2a261cf524c2b8a4987314930a6292615f514c39e42987348530eda82615e530c2bea7905714f20af29c415d5388398651057d4d20ae29a413e540827aa8105794c20aea9841cc32082eca2105d54420af29e215d53c42dca5885b54b10f290e215e53842baa7085794d10aea9a21e5214427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x23745888002802800094c8c0000ea6000000000680135a00030121c02c000139c00007800001a332890000046c30000edc006e00a80103943154d8f9056001af440000a52e469e30b800008840000000917002d9006a200420000040010600280000800800001009958652d0e556194b43b158652d0f466194b439358652d0f456194b439158652d0e4c625404395584540ca59601503293596420cac56190832d1949510cb466254432d1909510cb4542544329398b535064e62953319318950cc64e62951318799353c868e64d4f21b158753c86c56114f219399743c8654654c5219399743486c56110d21b158c41486e16010521b158e31486c6654c521b119531486c6644c521b119131486c7604c52193189539024e6295330d154521cc26561149309398a544c2556114930b1584524c346611493093584524c345611493091584524c24c65c853093195214c2556114f20b1584328824d650c820c355032082c5610c820d10c95108345534871093189538421c6454d109318953443455348510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4900100c0511cc0400c622b88c4a8087415d2625443290ce932a6290c46759913148622b88c4a9c81115c6629533088ae3314a8986055458432082223b2a690a21411d15348510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s5K5 (912+((h/16+packedAt s5K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s5K4 (4950+((h/55+packedAt s5K4 (4455+(h % 55)*9) 9) % 316)*9) 9
  | 3 => packedAt s5K3 (2420+((h/20+packedAt s5K3 (2280+(h % 20)*7) 7) % 105)*7) 7
  | 2 => packedAt s5K2 (502+((h/3+packedAt s5K2 (490+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff87ff0fffffffc1e1c3e1f83ffffffe064fff
  | 1 => 0xff83ff1e0ff87fe01fc7e3fc3c3fc1f19b273
  | 2 => 0xfffc001ff0ff87ffe007fc003fc3fe1e1c39c
  | 3 => 0xf0000001fff0007fffff800003ffc001fe03e0
  | 4 => 0xfffffffe0000007ffffffffffc000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8104102001000020408048088444880204a5
  | 1 => 0x25108a8246222a4608942a118162a855089252
  | 2 => 0xc62292a48a6c22daca106c82926a334561c318
  | 3 => 0x64772cc914c7336d6dd908052bb32199be03e0
  | 4 => 0x88443000188844319122512630000200d56800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8feeea8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36330
namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x80a00ec72652896a04800b005ca8f860060a2c18141007e49e9c6ed45a83a20899740108470000a5643c3ab4e00b9300f000946c5a0000cc01e72018000001b0d5e00dbe065401a110008001044008b280080000048850e28d8001ffd50077f5401ff95007fd5401df55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc43027fd4803fe52007f54803fc5201ffd0803fe4201ff50803fc42017fcc803fe32017f4c803fc32027fd4401fe51007f54409fc5101ffd0407fe4101ff50407fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0007fe4001ff50007fc40017fcc005df30017f8c005fd3000774c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842000ffd9510005feca8803bfe65440097f32a2000ff59510005faca8803bfc65440097e32a200dffd911006dfec888037fe64440077f322200dff5911006dfac888037fc64440077e322200dffd511006efea888037fe544401bfeaa2200ddf5511006ff8a888033ff63440197fb1a200cff98d10015fcc688033fd63440197eb1a200cff18d10015f8c688033ff5344019ff29a200cff54d10067f8a688033ff4344019ff21a200cff50d10067f88688003ff62440017fb12200bff9891000dfcc488003fd62440017eb12200bff1891000df8c48803bff5244017ff2922000ff5491005ff8a488037ff4244017ff212200dff5091005ff88488033ff3244017ff192200cff4c91005ff8648803bff514400bff28a2000fd94510007faa288003f5514400bfe28a200dffd051002ffc8288037f6414401bfea0a200dfd5051002ff88288033ff314400bff18a200cff4c51002ff8628802fff214400bff10a2000fd88510007fa4288003f5214400bfe10a200effd4110037fca088003fd504400dfe282200dffd0110037fc8088037fa404401bfea02200dfe50110037f88088033ff3044019ef9822006ff8c110067fa6088003dd304400dfe182200bffc8110037fc4088003fd204400dfe1022005ffc411002ff6208801bfe104400dfb0822006ffd9410035feca0801bfe65040097f3282006df99410024fcca0801bfd65040017eb282006df59410004faca0801bfc650400d7e3282006ffd9010035fec80801bfe64040077f3202006ef9901001d7cc80801bfd64040137eb202006ef590100057ac80801bfc640400d7e3202009ffd501004efea808027fe5404013feaa02009df5501004ff8a80801bff630400d7fb182006ff98c10015fcc60801bde63040056f3182006ff58c10045fac60801bdd63040016eb182006ff18c10035f8c608023ff5304011ff2982008ff54c10047f8a608023ff4304011ff2182008ff50c10047f8860801bff620400d7fb102006ff9881000dfcc40801bee6204003773102006ff58810005fac40801bed620400176b102006ff18810035f8c40802bff520400fff2902000ff5481003ff8a408027ff420400fff2102009ff5081003ff88408023ff320400fff1902008ff4c81003ff86408016fe610400bffa882005ff9441002ffaa208017fc510400bffa082005ff9041002ffa8208017fc410400bff9882005ff8c41002ffa6208017fc310400bff9082005ff8841002ffa4208017fc210400d7f3002006ffd4010037fca00801bfd500400dfe2802006ffd0010037fc800801bfd400400dfe2002006ffcc010037be600801bfe300400dfe9802006f74c010037f8600801bff200400dff1002006ff48010037f8400801bff100400dfb8802006ff84010037f4200801bfd100400dfa8802005fe44010
  | 1 => 0x7ff504800dff2824000ff54120037f8a090063ff404800dff2024018ff50120037f8809005fff304802fef9824006ff8c1200bffa6090003dd304800dfe1824001ffc812000ff6409001bfe204800df71024006ff08120037d84090007f8204800bffb2e2005bfd971002ffccb88012fe65c400bfeb2e2000bf5971002ff8cb88016fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb262015bf5931002ff8c988016fc64c402bffaa62015dfd53100affca988057fd54c402bbeaa62015ff1531002ffec788016ff63c400bff31e2002bf98f1002ffac788052fd63c400bfe31e2005bf18f100a7fea788053fe53c4029fea9e2014ff14f100a7fe8788053fe43c4029fea1e2014ff10f1002ffec588016ff62c400bff3162001bf98b1002ffac588002fd62c400bfe3162005bf18b100b7fea58804ffe52c4001fea962013ff14b100affe858804ffe42c402bfea162013ff10b100a7fe658804ffe32c4029fe9962013ff0cb1002ffea388017fe51c400bfb28e2005ff54710007eaa388017fc51c400bffa0e2005ff9071002fec8388017fd41c402bfaa0e2005ff1071002ffe6388017fe31c400bfe98e2005ff0c71002ffe4388017fe21c400bfb10e2005ff48710007ea4388017fc21c402dffa862006ff94310007faa18801bfc50c402bffa062006ff903100affa818801bfc40c4029ff9862014f7cc310037fc6188053fd30c4001ee9862006ff0c31009ffe418801bfe20c4001fe9062006ff08310037fecb0801aff658400dff32c2004bf99610037facb08002fd658400dfe32c2006bf19610037fec90801aff648400dff3242003bf99210037fac90803efd648400dfe3242006bf1921007ffea90803f7f548401fff2a4200fff5521007efaa90803ffc548400dffb1c2006bfd8e10037fcc70800afe638400def31c2002b798e10037fac708046fd638400deeb1c2000b758e10037f8c70801afc6384023ffa9c2011ff94e1008ffaa708047fc5384023ffa1c2011ff90e1008ffa8708047fc438400dffb142006bfd8a10037fcc508006fe628400dfeb142000bf58a10037f8c50801afc6284025ffa942010ff94a10007faa508043fc528401fffa142010ff90a1007ffa8508043fc4284023ff9942010ff8ca1008ffa6508043fc32840197eb0c2012ffd461002ffca308003fd518400bfe28c200fffd061002ffc830803ffd418400bfe20c2011ffcc61002ffc6308047fd318400bfe18c2010ffc861002ffc4308003fd218400bfe10c2006bf98210037fea10801bfe508400dfea842006ff14210037fe810801bfe408400dfd2042006ff5021007ff2810801bfc408400dff9842006f7cc210037fc610801bfd308400dee9842006ff0c210037fe410801bfe208400dfe9042006ff08210037fe210801bf7108400bfd8
  | 2 => 0x300f7baa89807b5d544c03dee2a26000f7d89300efbcc498003dd624c03bee312601ff7d49300efbca498003dd524c03bee292601ef7d09300efbc849807bdd424c03bee2126000f7d8530007bcc298003dd614c001ee30a601ff7d4530007bca298003dd514c03fee28a601ef7d05300f7bc829807bdd414c03dee20a601df7c8530007bc4298003dd214c03bee10a6002f7d8130015bec09800bdb604c03fefa826006f794130007baa09801bdc504c03defa026006f7901300f7ba809801bdc404c03bef9026006f708130037fecb1001aff658800dff32c4004bf99620037facb10002fd658800dfe32c4006bf19620037fec91001aff648800dff3244003bf99220037fac91006efd648800dfe3244006bf192200dffea91006f7f5488037ff2a4401bff552200defaa91006ffc548800dffb1c4006bfd8e20037fcc71000afe638800def31c4002b798e20037fac71006afd638800deeb1c4000b758e20037f8c71001afc6388035ffa9c401aff94e200d7faa71006bfc5388035ffa1c401aff90e200d7fa871006bfc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944006ffd8620037fcc310016fe618800dfeb0c4000bf58620037f8c310073ff5188001ff28c4000ff546200e7f8a31006fff4188037ff20c401bff506200dff8831006bff3188035ff18c401aff4c6200d7f86310007ff2188003ff10c4001ff4862000ff8431001afe608800dffa844006ff94220037faa11001bfc508800dffa044006ff90220037fa811001bfc408800dff9844006f7cc220037fc611001bfd308800dee9844006ff0c220037fe411001bef2088003fd9044006ff08220037f04110003ff65480017fb2a4019ff99520025fcca90003fd65480017eb2a4019ff19520025f8ca90063ff64480317fb224018ff9912001dfcc890063fd64480317eb224018ff1912001df8c890063ff5448031bfaa24018ff951200c7faa8900637d5448031fe2a24017ffd8d200bdfec69005ffe63480057f31a4017ff58d200bdfac69005ffc63480057e31a4017ffd4d200bffca69005ffd534802ffe29a4017ffd0d200bffc869005ffd434802ffe21a4006bfd892000ffea490007fe5248003f72924001ff54920007daa490007fc5248003ffa124001ff9092000fdc8490007fd4248031f6a124001ff1092000ffe6490007fe3248003fe9924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290016fc6148033ffa8a4000ff94520007faa290067fc5148031ffa0a4018ff905200c7fa8290063fc414802fff98a4017ff8c5200bffa629005ffc3148003ff90a4001fbc852000ffc4290007fd2148001f690a4001ff0852000dfec09006
  | 3 => 0xe10a4205fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc604840d7e3024228ffd4121147f8a09089fff404844fff2024227ff5012113ff8809089bff304844def9824226ff8c121137fa609089bfc3048403ff9024201fbc812100ff84090812fd659400dffb24a006bfd9250037fcc92800efe649400dfeb24a025bf59250037f8c92801afc6494009ffaa4a004dfd5250027fca928013fd549404bbeaa4a004ff15250037fec72801aff639400dff31ca002bf98e50037bcc72800ade639400dfeb1ca024bf58e50037bac728002dd639400dfe31ca006bf18e50027fea728013fe5394009fea9ca004ff14e50127fe8728093fe4394049fea1ca024ff10e50037fec52801bfe62940037f314a006ff58a50005fac52801bfc629400d7e314a004ffd4a50027fca528013fd5294009fe294a025ffd0a5011ffc8528097fd4294047fe214a024ffcca5011ffc6528093fd3294047fe194a006ffd8650037fcc328016fe619400dfeb0ca000bf58650037f8c328013ff5194009ff28ca004ff54650027f8a328097ff419404bff20ca025ff5065012ff88328093ff3194049ff18ca024ff4c650127f8632808fff2194001ff10ca000ff4865011ff8432801afe609400dffa84a006dfd4250027f6a12801bfc509400dfc284a006ffd0250037fc812801bfd409400dfe204a006ffcc250037be612801bfe309400dfe984a006ff0c250037fe412801bfc209400d7fb2aa022ffd9150115fec8a808bfe64540077f322a022ff59150115fac8a808bfc64540077e322a004ffd5150026fea8a8013fe5454009feaa2a022df55150027f8a8a8087ff63540437fb1aa021ff98d50015fcc6a8087fd63540437eb1aa021ff18d50015f8c6a8013ff5354009ff29aa004ff54d50027f8a6a8087ff4354043ff21aa021ff50d5010ff886a8003ff62540017fb12a020ff9895000dfcc4a8003fd6254041fe312a001bf18950027fea4a80137f5254009ff292a004ff54950006faa4a8013fc5254045ffa12a020ff90950117fa84a8083fc4254043ff992a020ff8c95010ffa64a8083fc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa005bf18550027fea2a80137f5154009ff28aa004ff54550006faa2a8013fc5154045ffa0aa022ff90550117fa82a808bfc4154043ff98aa021ff8c55010ffa62a8087fc3154041ff90aa000ff88550007fa42a8083fc21540097fb02a004ffd4150027f6a0a801bfe505400dbf282a006ff14150036f8a0a8013f85054045ffa02a006ff90150117fa80a801bfc4054043ff982a021f7cc150037fc60a8087fd305400dfe182a020ffc8150037f840a8003df654c03fef32a6000f7595300ffb8ca9807bdf644c03def322601ef7591300f7b8c89807bdf544c03dafaa2601ef7951
  | 4 => 0x806fc6254409ffa92a204ff94951027faa4a8813fc525445dffa12a22cff90951177fa84a88b3fc425445bff992a22cff8c95116ffa64a88b3fc32544097fb0aa204ffd4551027eea2a8817fe515440bbf28aa205ff1455102ef8a2a8813f4515445dffa0aa205ff90551177fa82a8817fc415445bff98aa205ff8c55116ffa62a8817fc3154459ff90aa205ff08551007fec0a8802ff6054401ff302a200ff58151007f8c0a881afc6054409ffa82a204dfd4151027f8a0a88bbff405445dff202a22eff50151177f880a88b7ff305445bef982a22dff8c15116ffa60a88b7fc3054459ff902a22cff0815102ffecb10816ff658840bff32c4204bf9962102ffacb10802fd658840bfe32c4205bf1962102ffec910816ff648840bff3244203bf9922102ffac9108aafd648840bfe3244205bf19221157fea9108ab7f5488455ff2a4422aff55221156faa9108abfc548840bffb1c4205bfd8e2102ffcc71080afe638840bfeb1c4229bf58e2102ff8c710816fc6388453ffa9c4229ff94e2114ffaa7108a7fc5388453ffa1c4229ff90e2114ffa87108a7fc43884037eb144201ffd4a2100ffca510807fd5288403fe2944201ffd0a2100ffc8510807fd4288403fe2144201ffcca2100ffc6510807fd3288403fe1944205bf9862102ffea310817fe518840bfea8c4205ff1462102ffe8310817fe418840bfea0c4205ff1062102ffe6310817fe318840bfb18c4205ff4c62114fea6310817fc318840bff90c4205fbc862100fee4310817fc218840bfa10c4205ffd822102ffcc11081afe608840bfeb044200bf5822102ff8c1108afff5088457fe284422affd0221157fc81108abfd4088455fe2044229ffcc22114fbe61108a7fe3088453fe9844229ff0c22100ffe4110807fc2088401ffb2a4200bfd9521147fcca90812fe6548401feb2a4200bf59521147f8ca90812fc654844fffb224227bfd912113ffcc89080efe644844ffeb224227bf5912113ff8c89080efc644844fffaa24227dfd512113ffca89089ffd544844fbeaa24227ff15121137fec69089aff6348401efb1a4200b7d8d21137fcc69080afe634844dfeb1a4226bf58d21137f8c69080afc634844dee31a4202b718d21137fea69089bfe534844dfea9a4226ff14d21137fe869089bfe434844dfea1a4226ff10d2102dfec490807ff5248451f7a924201ff9492100ffaa490807fc5248403f62924201ffd092100ffc8490807ee4248403fea124227fb5092100ff88490807ff3248403ff1924201fb8c92100ffa649089bed3248403fe1924201bfd8521147fea290817fe5148401fea8a4205ff1452113ffe8290817fe414844ffea0a4205ff10521137fe6290817fe314844dfb18a4226ff4c521137ea6290817fc3148403ff90a4201fdc852102ffc4290817ee214840bf
  | 5 => 0x20180bc01806ff6554867ffb22a433bfd915219ffcc8a900efe6454867feb22a433bf5915219ff8c8a900efc6454809ffaa2a404dfd5152027fca8a9013fd5454867beaa2a404ff15152197fec6a90caff6354801efb1aa400b7d8d52197fcc6a900afe6354865feb1aa432bf58d52197f8c6a900afc6354865ee31aa402b718d52027fea6a9013fe5354809fea9aa404ff14d52197fe86a90cbfe4354865fea1aa432ff10d5200dfec4a9007ff5254809f7a92a401ff9495200efca4a9007fc5254803be292a401fb1495200ffe84a9007fe4254803fea12a401ff1095200ffe64a9007fe3254803fe992a401ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9016fc6154809ffa8aa404ff1455219ffe82a90cffe4154867fea0aa433ff10552197fe62a90cbfe3154865fe98aa432ff0c55200ffe42a9007fc2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a406bf18152027fea0a90137f5054809fe282a433ffd015219ffc80a90cffd4054867fe202a432ffcc152197be60a90cbfe3054865fe982a432ff0c15200ffe40a9007ef2054803fe102a404bf5965102ffec928816ff649440bff324a203bf9925102ffac9288c6fd649440bfe324a205bf19251027fea9288137f5494409ff2a4a204ff5525118efaa928813fc549440bffb1ca205bfd8e5102ffcc72880afe639440bef31ca202b798e5102ffac7288c2fd639440beeb1ca200b758e5102ff8c728816fc6394409ffa9ca204ff94e51027faa728813fc5394461ffa1ca230ff90e51187fa87288c3fc439440bffb14a205ff98a5100dfcc528817ee629440377314a205ff58a51005fac528817ed629440176b14a205ff18a5102df8c528813ff5294409ff294a204ff54a51027f8a5288c7ff429445fff214a231ff50a5117ff885288c3ff329445fff194a230ff4ca5117ff86528816fe619440bffa8ca205dfd4651027eea328817fc519440bfa28ca205ffd065102ffc8328817fd419440bfe20ca205ffcc65102ffc6328817fd319440bfe18ca205ffc865102ff84328817ff609440bff304a206bf9825102ffac128802fd609440bfe304a204ffd4251027f8a1288c7ff4094463ff204a231ff5025118ff881288c3ff3094461ef984a230ff8c251187fa61288c3fc309445fff904a22fff0825102dfecaa88bbff645445d7fb22a22eff9915101dfcc8a88bbfd645445d7eb22a22eff1915101df8c8a8813ff5454409bfaa2a204ff95151027faa8a88bb7d5454409fe2a2a22dffd8d5116dfec6a88b7fe63544057f31aa22dff58d5116dfac6a88b7fc63544057e31aa204ffd4d51027fca6a8813fd5354409fe29aa22dffd0d5116ffc86a88b7fd435445bfe21aa200ffd8951005fec4a88b3fe62544037f312a200ff58951167f8c4a8
  | 6 => 0xaacd191185fc0004bc00000125c000000624cb4b4cca0db80607814800002cc0009242b12480008bc0f49440005e4000eac000f64d31085038000000c711dcf54000b488acfb8000c041b108075c5649c40000a5464298000000000a0c000114338000000048000e08a20b7c00122c3a0948000afc4809d0c4c9080000c05453a13388945a8000000d986e8c6cd780001a473524439c3b434c2300004744348c05500009cc68908900d0b00bc3004f93fc1492cc4944cce8d314884380cf4a00ad94a00006d041879c00145800028845c08c1cc2d941c2e400054c364000d643d0f00370000af89a038c00021400138c8cc68c768e10001328b90a5c5942a000046127101c5a4dc4d500300687bca510f12f8f254ace712ad2bcf14df89913eca84760ca80006491c13d465800000029c7f54380000004a8000000000019099394000000a49378bdc08904c71c570ed8000000000ddce65404b3c2643909d8ebc110904154e480000008640008351808b465c33c414000a54e31198c00d206b94600014154008712a800082c000ce52b8e54f341f8f3cbbd0346f04e4df400023510000016c0000040182200c00000004000000000010000000080a0040080900601200000003002004028000040080100600200403000000014010060e0000008000120000000500000000002002008000050020080280d020000000020060080900100400c0000000400000807000020008020000080c001000004030010060040280500c0040000100002002000006004030240020080100200200409000008004040050220001881b000000000000000200880000c064020000100000880001803c0181f012030000000140000100000200c060010060300100903a00c0080500e008008110060000081100607c018030020000600400a090078070240200100600602c0380a0000040000500401c0480500c00006000000014028000140200480300203c02804000000000080020100380201406c0100c0020000a00c0020240000200e0040180000201c008000220140600001c0040180201c00c0080f0040180280300a004000030100100180900c0140103100800000800018018008010040000180000000c000020000040100000003000800000014018060200500100100400001804000000010050020400681602000800000000000010000200040000500a01c00803002008020040040280280f00004c0180602c01c030190260000700100202c030000100100080900203002003002020000000040000780000e00800802000000040020100000200500a0080080000e000030000000140100000000000803024074000020160000380002801401003006050028230000000102000003c11800008024008000320000380100a0140380300a00407005002008
  | 7 => 0x3cc211b42c4c7544859d22402c6b0c951a085839486111c96467800143d2e41f062c6a136837ca7c5d940c1b4f600003d4d0cf846101e4cdc6f4001154b00aa542c8894953f0d8c00061525905c0000006690cc46cba83f4bc40000000012c4c7c00ca40a2c67cee835539c0012c80f10146b535c000000b7923c000000bec8688b0000000000cf0cd5354c641f53445dd18c7013dc66cb092f40405c8d9d30c0007f05744c8f4115c090eccfa8a34da4ef8a792a12ecb8c5b947800041c00013caf0c54000379228194001254a4cd1444c1281083085d0000000be4de40000000fc00136000000000000138800000000000000108ca59020000000000000000ae0000098720e14950000348000000ee0000b2c0008fc0006c80009181c800089864410c208f9d34cd7408026cdaca6c00000091c0003889dc0000000007494b40007b0000d1c000a89030000e988187b42f8c8509c000000f790a4de0000e412080700000000011b0001370d34000000000728820184c30784900a688040013c85308908ec4910d4000274000d689780002683987100007942dd398618e950fc8dc458a3133c00144cab4e602546ec9a860c000000b14e8052d0ac0013005ccdfc000000d580008f4ac86fcb70878e843d8dbc0013e50286545b00009b53d1250c780000014302440013d876d3b8b800009b0000000d490c07d12140000014547440003ad3200f851c05095c3b83a8eb0970000e68c8c000000dd00a04c4510000000e4cdf0000001234b0400114c00005c000000000eec000fd92fc3e0e352b1424954c5c0012c0bd4db40007ec0000010502c0000000000e58ea91404081a90e506c240059174000000fc0304000000850ae91780000005204e06380007313186d8000efc920f482d03c14b00ed410094a18e7c2206ac2851bcd40a1c914e28000ec484c6e4dec1d0344698d2800022c00097d1041644f51588f114496c00000000063d0dcd240000000003748d5130ce8ff0fac000078724c909fcee46e0bccfc89e1120abd3353809ad22000129022881483c104000000000350940830534f38bc1070b0cd94f5c498cc921d1384404d4478590270368158280e8815c3f1268504d9119527881c0000010787dc47d4511903251613a4e9c5f01c461ccb0000fc4020b60a04974f104451a8008000708000000e50000000000840ed400000134024d2100013cce24f947c069c00129cb445993094a4bb0b88600c444b0e6c4305787f91d52f03e945cd10d840013e14892e858c0005f4eb8001264690420f68d7cc9c9ecb1c0d12d07d4000ad04a13592000e85f8c893b10947cc8c831d1b8438cf917c0001e9280000620004568000c28340000000000eb40b8f90cb8000a450905e0d71170694000000488b942bd0588548a534927cfecd89135010b68
  | 8 => 0x5bc0002fc000c251fd2040009940000000000004049d4c99324add49ce0cc2c0001ac0012300008294a8a71114d4c0000004682d43ed49000000036d3913e8554000a740010453f4c586a8130aa9184a10fdc034000958ff8ab0000f8c000000f58f04ec80001ecbd89bc4b50a8000ffd20c3dc0011080000005ac00000006ca28190608000ae4dc0c38de8c80508d80bb8dc84a400053d1cc144000000bf80000000000000440005c4a24000000b350b8000f08d3cfe00008f804c000934f80fccedc6bcb1000000092c9f816800000000000048c5c0ac00001fc000fbc0000740000010f4000000b288e0000000000ec06f800000000021c00000000058800023cfb0fd40008749992940012d80a89391acccc1c040d24077c3bc1386cd1512dc9e409cd05364524d00aec6d41811c4c689882100000007e10d805420c0000003c8f7c9f531102d46c328e5c55800073c9108b8000ea4b9cb24b6470400137c8e8d61238af519d025498248f50ce12985803c44fc23831058480cba128527485c0007c4cd0e380dc001374ef06044007fccbc6dcc600000011a419c72c00148c000000448000000a64cac27cf2c000000178000ac528cb6c0d42253acbfc0008e5000db0b504c000000065011d0c8bc8084cc4464824010120ff45b4cd8360f28000000001474b408a0000bf0da03e4000764e1d008fd000103ce4531c79113c1dc000000e781b8000fb4318b580000013852b40000d92a4d447880007a887c14c4ac84400000098099c27800007cf1c0c5124000000000000f18be80b40007a42b40007140002ed0184b893c518bd0dd8384258000e3c00000089c0001d87413bc2f012c98d1f40000000000002c80cd0b400000000090cc1d2e0000000a14d08f0d468680e0470c759048fe418c43d1f142078d2d4f203582b8198771440aa10a0140f7116c2a4161110cfd189288660c1944532c968ba42505289e80004dd26c1008d9054cc0778dd4294684d54d6c0000004ec000a9cca41d512d060000560000000b984251e40000011d0e00c0c2acb54540cecd5c9c14289b86651e10ecb38a61129408be10c4e20bb53b4738454e75304c0803c00000030cc34bf45383213f800110c3cc7d81bc9f0124f30f99470b5c64cb30a80a901340000011e9418b74630118039350c48a8cdcced017c56c55d0bc470188984000ab9004410ef40c8f4ce2c670a08c10d3817000000147d0d035c42cc400ac3b09c90745e8fa00004f000000000074c6354846c40000008492605a10e80006a402907c7ac204a940007b91485491c80003140002f40007a001d168fe820067442800050cf886c11f86280002182e85ec000d2c7e8000808174880b20e907750400014b80000000003f8b180002a875033136c00000000124c4d000057c06428c000000500a
  | 9 => 0xe00000010653c451464000094c0140001e07193309284d91641a0f7486c0b10e025c000000ea00e40009300000008c4a387982600000004e92183fc0000011ec2e08a80000000000000000000000003a4450000c153a8c3cf44fa4b84bacda8335068000000960e180005d4810000000290000c5088c9a47e53c04850f802400083832c7551d8a980007c8000f6c8d0ad4800acc00143400000049c15
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c1002edf7158c1002ede7158c1002edd7158c1002edc7158c1002edf5158c1002ede5158c1002edd5158c1002edc5158c1002edf4158c1002ede4158c1002edd4158c1002edc4158c1002edf2158c1002ede2158c1002edd2158c1002edc2158c10036df7058c10034df7058c10036de7058c10036dd7058c10034dd7058c10036dc7058c10036df5058c10036de5058c10036dd5058c10036dc5058c10036df4058c10036de4058c10036dd4058c10036dc4058c10036df2058c10036de2058c10036dd2058c10036dc2058c10036df1058c10036de1058c10036dd1058c10036dc1058c10004ff7558810024fe7558810024fc7558810004ff745881001cfe7458810004fd745881001cfc74588100067f54588100067d5458810004ff7358810014fe7358810004fd7358810014fc7358810034ff7258810036ef7258810006ef525881003eee525881003eec5258810006ef425881003eee4258810006ed425881003eec4258810006ef325881003eee3258810006ed325881003eec325881002cff715881002cfe715881002cfd715881002cfc715881002eee215881002eec2158810034ff7058810034fe7058810034fd7058810034fc7058810036df3058810036dd3058810036ee2058810036ec2058810036f71058810036f51058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef54588100066f5458810006ee5458810006ed54588100066d5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef715881002eee715881002eed715881002eec715881002eef515881002eee515881002eed515881002eec515881002eef415881002eee415881002eed415881002eec415881002eef315881002eee315881002eed315881002eec3158810036ef7058810036ee7058810036ed7058810036ec7058810036ef5058810036ee5058810036ed5058810036ec5058810036ef4058810036ee4058810036ed4058810036ec4058810036ef3058810036cf3058810036ee3058810036ed3058810036cd3058810036ec3058810036ef1058810036e71058810036ee1058810036ed1058810036e51058810036ec1058810004ff7654810034fe7654810004fd7654810034fc76548100267e65548100067d655481019ebe6454810006bd6454810005df7354810045dc7354810196de6354810006dd635481000eee6254810006ed6254810
  | 1 => 0x94100567c5359410004ff725941000cfe725941000cfc72594100567f52594100067e52594100567c525941002cff715941002cfe715941002cfd715941002cfc715941002e7e515941002e7c5159410034ff7059410034fe7059410034fd7059410034fc70594100367e50594100367c5059410036df3059410036dd3059410036f71059410036f510594100067f74594100047f74594100067e74594100067d74594100047d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067d32594100067c325941002e7f715941002e7e715941002e7d715941002e7c715941002e7f415941002e7e415941002e7d415941002e7c415941002e7f315941002e7e315941002e7d315941002e7c315941002e7f215941002e7e215941002e7d215941002e7c21594100367f70594100367e70594100367d70594100367c70594100367f40594100367e40594100367d40594100367c40594100367f30594100365f30594100367e30594100367d30594100365d30594100367c30594100367f20594100367e20594100367d20594100367c20594100367f10594100367710594100367e10594100367d10594100367510594100367c1059410006bf7559010006be75590100063e7559010006bd75590100063d7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901002ebf715901002ebe715901002ebd715901002ebc715901002ebf515901002ebe515901002ebd515901002ebc515901002ebf315901002ebe315901002ebd315901002ebc315901002ebf215901002ebe215901002ebd215901002ebc2159010036bf7059010036be7059010036bd7059010036bc7059010036bf5059010036be5059010036bd5059010036bc5059010036bf30590100369f3059010036be3059010036bd30590100369d3059010036bc3059010036bf2059010036be2059010036bd2059010036bc2059010036bf1059010036b71059010036be1059010036ba1059010036bd1059010036b5105901002eb91059010036bc1059010006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c100065f5458c10006de5458c10006dd5458c100065d5458c10006dc5458c10006d
  | 2 => 0x35f67094510035f4709451002ef7609451002ff3609451020ff2409451020ff14094510207d73094510034fc76545100067f65545100267c655451002f745154510005fb7054510035f87054510035f47654510026f47654510034f4765451002df7755451002f777554510007776554510026f66554510026f465545100777465545101fdf774545101fdf574545100777754545101f7755454510005f77254510007f37054510035f67054510035f47054510007f0705451002ef7605451002ff360545100777750545101f7f240545101f7f140545101efd73054510005f6768851002ef6768851002df77588510005f5758851002df774885101e5f574885101df7754885101df7554885101d6f763885101d6f5638851005df5728851000ef6628851000ef46288510035f67088510035f4708851002ef7608851002ff360885101dff240885101dff140885101d7d73088510034fc7648510005df7348510065dc7348510006ef624851000eec624851002fe42148510005fb7048510035f87048510035f4764851000ef47648510034f47648510005f77548510005f575485101cdf774485101cdf574485101bf7754485101bf755448510007d773485101b7d473485101b6f763485101b6f5634851002df7724851002fe77248510007e7624851000ef6624851000ef4624851005fe462485101c7e7524851005fe4524851005fe642485101bfe5424851005fe632485101b7e53248510007f37048510035f67048510035f47048510007f0704851002ef7604851002ff360485101bff240485101bff140485101b7d7304851005fe72048510024ff7654110074fd765411002cfc76541100067f65541100267c6554110005f7715411002df47154110007755154110016df764c1101a6de764c110066dd764c110016dc764c110006df654c1100fede654c110006dd654c1100fedc654c1101aedf644c1100f6de644c1101aedd644c1100f6dc644c1101af5f544c1101af5d544c110006df624c1100eede624c110006dd624c1100eedc624c110007d7714c110007d4714c110036df614c110007d6514c110007d5514c1101afd6414c1101afd5414c110007d6214c110007d5214c110035df704c110067db704c110036df604c110037da504c110007d9504c110037da404c1101afd9404c1101a7db104c110037d6104c110037d4104c110037d8104c11000cff764811005cfd764811002cfc7648110006ef624811000eec6248110005f7714811002df47148110007e52148110034ff75594100367f7559410004ff745941001cfe7459410004fd745941001cfc74594100567f54594100067e54594100067d54594100567c5459410004ff7359410014fe7359410004fd7359410014fc73594100567f53594100067e53594100067d535
  | 3 => 0xd7654a10034fc7654a100267e6554a100067d6554a10005df7354a1008ddc7354a10196de6354a10006dd6354a1000eee6254a10006ed6254a10024ff7654610034fc76546100267e65546100067d655461016ede6354610006dd6354610005fb7054610035f8705461000cff7648610034fc7648610005df734861008ddc7348610136de6348610006dd634861000eee6248610006ed6248610005fb7048610035f87048610024fe76d95100767e65d9510065de73d9510005dd73d9510004ff74d951001cfe74d9510004fd74d951001cfc74d95100767f54d95100067d54d9510004ff73d9510014fe73d9510006de73d9510014de73d9510004fd73d9510006dd73d9510004dd73d9510014fc73d95100067e53d95100767c53d951000cfe72d9510004fd72d951000cfc72d95100067e52d95100767c52d951002cfe71d9510034fd71d951002cfc71d95100767f51d9510034fe70d951002cfd70d9510034fc70d95100767f50d9510006df30d95100767c6559510074ff75595100067f7559510004ff745951001cfe7459510004fd745951001cfc74595100767f54595100067d5459510004ff7359510014fe7359510004fd7359510014fc7359510004ff725951000cfe725951000cfc7259510094ff7159510006f771595100b4ff7059510006fb7059510006df305951000cfe76d891005eee62d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d89100067f54d89100067d54d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910006ef32d891005eec32d891002cfe71d8910034fd71d891002cfc71d891005eef21d8910034fe70d891002cfd70d8910034fc70d8910006df30d891005eef20d89100057f75589100757c7558910005bf745891006dbc7458910005df7358910065dc735891005eec6258910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc74589100067f54589100067d5458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc735891005cff7258910006ef725891005eee4258910006ed4258910084ff7158910006f7715891009cff7058910006fb7058910006df3058910004ff7654910004fe7654910004fd7654910004fc7654910005df7354910065dc7354910005f6769451002ef67694510075f57594510026f66594510026f4659451002df77494510215f5749451007777549451020f75549451002fd6739451002fd5739451002fe67294510005f5729451002fe57294510005e57294510
  | 4 => 0x8710226f5634871002fe7724871002fe7624871000ef6624871002ef4624871002fe46248710237e7524871009fe4524871009fe6424871022fe5424871009fe63248710227e53248710035f67048710035f47048710227d7304871009fe72048710024ff765431002cfc76543100267e65543100067d6554310005f7715431002df47154310007755154310016df764c310016dc764c3101a6df654c3100fede654c310006dd654c3101a6dc654c3101a6df644c3100f6de644c31021edd644c3101a6dc644c31021f5f544c31021f5d544c3101a6df624c3100eede624c310006dd624c3101a6dc624c310007d7714c3101a7d4714c310036de614c3101a7d6514c310007d5514c3101a7d6414c31021fd5414c3101a7d6214c310007d5214c310035df704c3100a7db704c310036dd604c310037d6104c310037da104c310037d4104c31000cff764831002cfc764831000eee6248310006ed6248310005f7714831002df47148310007e521483100367f7559610004ff745961001cfe7459610004fd745961001cfc74596100967f54596100067d5459610004ff7359610014fe7359610004fd7359610014fc7359610004ff725961000cfe725961000cfc72596100967f52596100967f5159610034fc70596100367e50596100367c5059610036df3059610036dd3059610036f71059610036f51059610006df7558e10006de7558e10006dd7558e10006dc7558e10006df7458e10006de7458e10006dd7458e10006dc7458e10006df5458e100065f5458e10006de5458e10006dd5458e100065d5458e10006dc5458e10006df7258e10006de7258e10006dd7258e10006dc7258e10006df5258e10006de5258e10006dc5258e10006df4258e10006de4258e10006dd4258e10006dc4258e1008edf7158e101a6de7158e10006dd7158e101a6dc7158e10006df5158e101a6de5158e101a6dc5158e10006df4158e101a6de4158e10006dd4158e101a6dc4158e10006df2158e101a6de2158e101a6dc2158e10036df7058e10036de7058e10036dd7058e10036dc7058e10036df5058e10036de5058e10036dd5058e10036dc5058e10036df4058e10036de4058e10036dd4058e10036dc4058e10036df2058e10036de2058e10036dd2058e10036dc2058e10036df1058e10036de1058e10036dd1058e10036dc1058e10004ff7558a10024fe7558a10024fc7558a10004ff7458a1001cfe7458a10004fd7458a1001cfc7458a100067f5458a100067d5458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a10036ef7258a10086ee5258a10086ee4258a10006ed4258a10086ef2158a10034fc7058a10036df3058a10036dd3058a10036ee2058a10036ec2058a10036f71058a10036f51058a10004ff7654a10034fe7654a10004f
  | 5 => 0x6f56118520004fe7694520004fd769452002cfc76945200067f65945200267c65945200bdde7394520005dd739452000dee7294520005ed7294520004ff7654520004fe7654520004fc765452000dee7254520034ec7648520005ef7548520005ed7548520146ee6548520146ec6548520275ef7448520275ed744852026eef644852026eed644852026f6f544852026f6d5448520007cf7348520267cc7348520266ef6348520266ed634852000def714852000fe77148520007e7614852002eee614852002eec6148520007e46148520267e63148520267e53148520007eb7048520035ee7048520035ec7048520007e8704852000eef604852000feb6048520267cf3048520024ff765412000cfe7654120104fd765412000cfc76541200067f65541200267c6554120005ef725412000dec72541200076d5254120016df764c1200eede764c1200eedd764c120016dc764c120006df654c1200fede654c120006dd654c1200fedc654c12025edf644c1200f6de644c12025edd644c1200f6dc644c12025f5f544c12025f5d544c120007cf724c1200efcc724c120036df624c1200efce524c120007cd524c1200efce424c12025fcd424c120006df614c1201a6dc614c1200efcf214c120007cd214c120035df704c1200bfdb704c120036df604c120037da504c120007d9504c120037da404c12025fd9404c1200efdb204c120037ce204c120037cc204c120037d8204c12002e7f7559710004ff745971001cfe7459710004fd745971001cfc74597100b67f54597100067d5459710004ff7359710014fe7359710004fd7359710014fc7359710004ff725971000cfe725971000cfc7259710034fc715971002e7e515971002e7c51597100b67f5059710006df3059710004ff7558b10024fe7558b10024fc7558b10004ff7458b1001cfe7458b10004fd7458b1001cfc7458b100067f5458b100067d5458b10004ff7358b10006df7358b10004df7358b10014fe7358b10004fd7358b10014fc7358b10006dc7358b10014dc7358b1002eef7258b10006ef5258b1009eec5258b1009eee4258b10006ed4258b1009eee3258b10006ed3258b10034fc7158b1002eee2158b1002eec2158b10006df3058b1009eef2058b10004ff7654b1002cfe7654b10004fd7654b1002cfc7654b10005df7354b100a5dc7354b1002df67154b1002df77654710056f7765471002f77755471002f776554710026f6655471002ef4655471002f746554710255f77454710255f574547100b777545471024f755454710005f77254710035f67054710035f470547100b7775054710247d7305471002df7764871003ef77648710005f77548710005f5754871023df7744871023df5744871022f77544871022f755448710007d77348710227d4734871002ef7634
  | 6 => 0xd5058e20036dc5058e20036df4058e20036de4058e20036dd4058e20036dc4058e20036df2058e20036de2058e20036dd2058e20036dc2058e20036df1058e20036de1058e20036dd1058e20036dc1058e20004ff7558620024fe7558620024fc7558620004ff745862001cfe7458620004fd745862001cfc74586200067f54586200067d5458620004ff7358620014fe7358620004fd7358620014fc7358620036f77158620006f64158620006f5415862005ef6215862005ef52158620034ff7058620034fd7058620034fc7058620036df3058620036dd3058620036ef2058620036ed2058620036f61058620036f4105862002cff7694620034fe7694620004fd76946200d5de7394620005dd7394620186de6394620006dd639462000dee7294620005ed729462002ef66194620006f56194620004ff7654620004fd7654620034fc76546200267e65546200067d655462016ede6354620006dd635462002ef66154620006f56154620024fe76d95200ce7e65d9520004ff74d952001cfe74d9520004fd74d952001cfc74d95200ce7f54d95200067d54d9520004ff73d9520014fe73d9520004fd73d9520014fc73d95200067e53d95200ce7c53d9520034ff72d952000cfe72d9520034fd72d952000cfc72d952011e7f52d952011e7d52d952002cfe71d9520004fd71d95200ce7c51d952000cfd70d95200ce7f50d9520006df30d95200ce7c6559520005df73595200bddc7359520295fb705952011cff75595200067f7559520004ff745952001cfe7459520004fd745952001cfc74595200ce7f54595200067d5459520004ff7359520006df7359520004df7359520014fe7359520004fd7359520014fc7359520006dc7359520014dc7359520104ff7259520006ef7259520004ff715952002cfc7159520294ff7059520006fb7059520006df3059520035ec7654920026ec7654920034ec765492000def755492000f6f75549200076f6554920026ee6554920026ec65549200cf6c655492028def745492028ded74549200cf6f54549202876d5454920007cf735492027fcc7354920005ef7154920007eb7054920035ee7054920035ec7054920007e8705492000eef605492000feb60549200cf6f505492027fcf3054920024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d85200067f54d85200067d54d8520004ff73d8520014fe73d8520004fd73d8520014fc73d8520034fd72d8520086ee42d8520006ed42d8520086f621d8520086f521d8520034fe70d8520034fc70d8520006df30d8520006f7619852005df970985200057f75585200cd7c7558520005bf74585200c5bc7458520005df73585200bddc735852009dfb70585200bdde7318520005dd731852002ef66118520
  | 7 => 0x453016edf605453016fdb60545300ff5f50545301a5df7688530005de7688530005dd76885301a5dc76885301a5df75885300fdde7588530005dd75885301a5dc75885301a5df74885300f5de74885302e5dd74885301a5dc74885302df5f54885302df5d54885300eddd7288530007cf62885300efcc62885301a5de71885301a7d66188530007d561885301a7cf21885300efd721885301a7d42188530035de7088530005dd7088530035dc70885302d6df608853014fdb6088530005df7648530006df7648530004df7648530005de7648530005dd7648530005dc7648530006dc7648530004dc7648530005df75485300fdde7548530005dd75485300fddc75485302cddf74485300f5de74485302cddd74485300f5dc74485302bf5f54485302bf5d54485301a5df72485300efce6248530007cd62485302c7cf52485300efcc52485300efce42485302bfcd42485300eddf7148530007d66148530007d561485300efd721485301a7ce21485301a7cc21485300efd42148530005df7048530035de7048530035dc70485302b6df6048530137db60485300efcf20485302addf7654130015de765413010ddd7654130015dc7654130035df75541300075f65541300ff5c65541302a5df74541300f5de74541302a5dd74541300f5dc74541300ff5f545413029f5d5454130005df72541300edde72541300eddc72541300ff5f52541300075d5254130005df71541301a5dc71541300ff5f51541300075d5154130035df7054130036df605413010fdb60541300ffdb50541300375e50541300375c5054130037d85054130037da2054130037da10541300367f7559620004ff745962001cfe7459620004fd745962001cfc74596200e67f54596200067d5459620004ff7359620014fe7359620004fd7359620014fc73596201067f52596201067d5259620004ff715962002cfc71596200e67f5159620034fe7059620034fc70596200367e50596200367c5059620036df3059620036dd3059620036ef2059620036ed2059620006df7558e20006de7558e20006dd7558e20006dc7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e200065f5458e20006de5458e20006dd5458e200065d5458e20006dc5458e200eedf7258e200eede7258e200eedd7258e200eedc7258e200eedf5258e200eede5258e200eedd5258e200eedc5258e200eedf4258e200eede4258e200eedd4258e200eedc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006dc5158e20006df4158e20006de4158e20006dd4158e20006dc4158e200eedf2158e200eede2158e200eedd2158e200eedc2158e20036df7058e20036de7058e20036dd7058e20036dc7058e20036df5058e20036de5058e20036d
  | 8 => 0xef5e52549300ef5c52549300efcc5254930005df71549301a5dc7154930005df7054930035de7054930035dc70549302b6df6054930197db60549300ff5f50549300efcf20549300fdde75d8530005dd75d85300fddc75d8530006de65d8530006dc65d8530005df74d85300f5de74d8530005dd74d85300f5dc74d8530006df64d8530006dd64d85300075f54d85300075d54d85300edde72d8530005dd72d85300eddc72d8530006df62d8530006dd62d853008edf60d853008fdb60d85300fdde7598530005dd75985301a5dc75985301a5df74985300f5de7498530005dd74985301a5dc74985300075f54985300075d54985300edde7298530005dd72985301a5dc7298530006de6298530006dc62985301a5de71985301a6df6198530007d76198530065dd70985301a7d97098530065d970985302d6df60985300a7db6098530005df75585300075f75585300055f75585300fdde75585300fddc75585300075c75585300fd5c7558530006de6558530006dc6558530005df74585300079f74585300059f74585300f5de7458530005dd74585300f5dc74585300079c74585300f59c7458530006df6458530006dd64585300075f54585300075d5458530005df7258530007cf7258530005cf72585300edde72585300eddc7258530007cc72585300edcc7258530006df6258530006dd6258530007d761585301a6de61585300a5df7058530007db70585300a5db7058530066df6058530067db605853008dde76185300fdde7518530005dd75185301a5dc75185301a5df74185300f5de7418530005dd74185301a5dc74185300075f54185300075d54185300edde72185301a7ce72185300edce7218530005dd72185301a7cd7218530005cd72185301a5dc7218530006de6218530006dc62185301a6df61185301a7d661185301a6dd6118530007d561185302d6df6018530047db60185301a5df7694530005de76945301a6de7694530004de7694530005dd76945301a6dd7694530004dd76945301a5dc769453016ddd75945300075f65945300ff5c65945301a5df74945300f5de749453030ddd74945301a5dc74945300ff5f54945303075d54945300edde72945301a7ce72945300edce7294530005dd72945301a7cd7294530005cd72945301a5dc72945301a5de71945301a75f51945300ffd751945301a7d45194530035de7094530005dd7094530035dc70945302d6df6094530187db6094530005df7654530005de7654530005dd7654530005dc76545301a5df75545302fddf74545300f5de74545302fddd74545300f5dc74545300ff5f54545302f75d5454530005df72545300edde72545300eddc72545302eddf71545300ffd751545301a75e51545301a75c51545300ffd45154530005df7054530035de7054530035dc705
  | 9 => 0xd73d8550014fc73d855000cfe72d8550004fd72d855000cfc72d8550096f651d8550096f551d8550006f741d8550006f441d8550006df30d855010dde7398550005dd7398550105ee7298550005ed7298550006f76198550075f970985500b5fb705855002ef66118550006f561185500347c76545503457f74545503457d745455033e7f645455033e7d64545500057f72545500257f715455002777715455000777615455002e7e615455002e7c61545500077461545500077b70545500357e70545500357c70545500077870545500267f60545500277b60545503375f3054550004fe7688550004fd768855002cfc76885500257e75885500057d7588550004ff7648550004fe7648550004fc76485500257e75485500057d7548550005df734855010ddc7348550006ef624855000eec62485501476f524855032dde76d95300fede65d95300ff5e65d95300fe5e65d95300fedc65d9530005df74d95300f5de74d9530005dd74d95300f5dc74d95300ff5f54d95300075d54d95300edde72d9530005dd72d95300eddc72d95300075e52d95300ff5c52d95301a5de71d9530005dd71d95300ff5c51d9530035de70d9530015dd70d9530126df60d9530127db60d95300ff5f50d9530125df75595300075f65595300fede65595300fedc65595300ff5c6559530005df74595300f5de7459530005dd74595300f5dc74595300ff5f54595300075d5459530005df7259530007cf7259530005cf72595300edde72595300eddc7259530007cc72595300edcc7259530005df71595301a5dc71595302addf7059530007db70595302addb705953010edf605953010fdb60595300edde76d89300fdde75d8930005dd75d89300fddc75d8930005df74d89300f5de74d8930005dd74d89300f5dc74d89300075f54d89300075d54d89300eede62d89300efce62d89300eedc62d8930007cf52d89300efcc52d89300efce42d8930007cd42d89301a5de71d8930005dd71d89300efcc21d8930035de70d8930015dd70d89300d6df60d89300d7db60d89300efcf20d8930005df75589300075f75589300055f75589300fdde75589300fddc75589300075c75589300fd5c7558930005df74589300f5de7458930005dd74589300f5dc74589300075f54589300075d54589300eddf7258930007cf62589300eede62589300eedc62589300efcc62589300eecc6258930005df71589301a5dc71589300efcf2158930325df7058930007db7058930325db70589300bedf60589300bfdb6058930005df7654930006df7654930004df7654930005de7654930005dd7654930005dc7654930006dc7654930004dc76549300eddf755493031ddf74549300f5de745493031ddd74549300f5dc74549300ff5f54549303175d54549300eddf72549300ffcf5254930
  | 10 => 0x8e50006dd4258e50006dc4258e50006df7158e50006de7158e50006dd7158e50006dc7158e500fedf5158e500fede5158e500fedd5158e500fedc5158e50006df4158e50006de4158e50006dd4158e50006dc4158e50006df2158e50006dc2158e50036df7058e50036de7058e50036dd7058e50036dc7058e50036df5058e50036de5058e50036dd5058e50036dc5058e50036df4058e50036de4058e50036dd4058e50036dc4058e50036df2058e50036de2058e50036dd2058e50036dc2058e50036df1058e50036de1058e50036dd1058e50036dc1058e50004ff7458a5001cfe7458a50004fd7458a5001cfc7458a500ce7f5458a500067d5458a50004ff7358a50014fe7358a50004fd7358a50014fc7358a50036ef7258a5011eee5258a500ceed5258a5011eee4258a50006ed4258a50004ff7158a5002cfc7158a5011eef2158a50034fe7058a50034fc7058a500367f5058a500367d5058a50036df3058a50036dd3058a50036ee2058a50036ec2058a50004ff745865001cfe7458650004fd745865001cfc74586500767f54586500067d5458650004ff7358650014fe7358650004fd7358650014fc7358650004ff725865000cfe725865000cfc7258650036f77158650076f65158650076f55158650006f64158650006f54158650034fc70586500367f50586500367d5058650036df3058650036dd3058650036f61058650036f4105865002cff7688650034fe7688650004fd768865014ede6388650006dd638865002ef66188650006f56188650004ff7648650004fd7648650034fc76486500057f75486500257c7548650005df7348650125dc7348650136de6348650006dd634865000eee6248650006ed624865002ef66148650006f5614865000cfe76d8950106ee62d8950034fd75d895000cfc75d8950004ff74d895001cfe74d8950004fd74d895001cfc74d89500e67f54d89500067d54d8950004ff73d8950014fe73d8950004fd73d8950014fc73d8950106ee52d89500e6ed52d8950006ef42d8950106ec42d8950006ef32d8950106ec32d895002cfe71d8950004fd71d8950106ef21d8950024fd70d8950006df30d8950106ef20d8950005df735895010ddc7358950106ec6258950365fb70589500357c765495000e7c76549500347c765495035d7f745495035d7d74549503567f64549503567d64549500075f735495034f5c73549500257f72549500276f72549500076f625495000e7e625495000e7c62549501076c62549500057f71549500077b70549500357e70549500357c70549500077870549500267f60549500277b605495034f5f30549501076f2054950034fd75d8550004ff74d855001cfe74d8550004fd74d855001cfc74d85500967f54d85500067d54d8550004ff73d8550014fe73d8550004f
  | 11 => 0x34fc70595211467f5059521006df3059521166ef205952137dde76d8d21136de76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d2136fcf72d8d21377cc72d8d21007cf52d8d21377cc52d8d21377ce42d8d21007cd42d8d21377d771d8d21377d471d8d21377d721d8d2136fce21d8d2136fcc21d8d21377d421d8d21005dd70d8d21377cf20d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d2136edf72d8d21376de72d8d21376dd72d8d21376dc72d8d21376df52d8d21376de52d8d21376dd52d8d21376dc52d8d21376df42d8d21376de42d8d21376dd42d8d21376dc42d8d21376df71d8d2136ede71d8d21376dd71d8d2136edc71d8d21006df51d8d2136ede51d8d2136edc51d8d21006df41d8d2136ede41d8d21006dd41d8d2136edc41d8d21376df21d8d2136ede21d8d21376dd21d8d2136edc21d8d21006df70d8d21006de70d8d21006dd70d8d21004dd70d8d21006dc70d8d21006df50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21376df20d8d21376de20d8d21376dd20d8d21376dc20d8d2136edf10d8d2136edc10d8d21024ff765452100cfe7654521164fd765452100cfc76545210067f65545210267c6554521006df635452116edc6354521005ef725452100dec725452102fe42154521135dc73d8121006df63d8121006dc63d8121024fe75d8121004fd75d8121024fc75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d81210067f54d81210067d54d8121004ff73d8121006df73d8121014fe73d8121004fd73d8121014fc73d8121006dc73d8121014dc73d812102cfd72d812109eee42d8121006ed42d8121006df30d812109efa20d8121135de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211457c7558121005bf745812113dbc7458121005df7358121135dc7358121006df6358121006dc63581211457e75181210057d751812113dbe7418121005bd7418121135de7318121005dd7318121006df6318121006dc6318121036fa6018121006f96018121126df7558e50126de7558e500fedd7558e50126dc7558e50006df7458e50006de7458e50006dd7458e50006dc7458e500fedf5458e500fe5f5458e500fede5458e500fedd5458e500065d5458e500fedc5458e50006df7258e50006de7258e50006dd7258e50006dc7258e500fedf5258e500fede5258e500fedd5258e500fedc5258e50006df4258e50006de425
  | 12 => 0xf725825100cfe725825100cfc725825102cfc715825102e7f515825102e7d515825102efb7058251076fa5058251006fa4058251006f94058251006df305825102efb105825102ef8105825100cfe76d8951166ee62d895102cfd75d8951004ff74d895101cfe74d8951004fd74d895101cfc74d895115e7f54d89510067d54d8951004ff73d8951014fe73d8951004fd73d8951014fc73d8951166ee52d895115eed52d8951024fd71d8951166ef21d8951034fe70d8951004fd70d895115e7f50d8951006df30d8951005df735895116ddc7358951166ec625895138df7715895102cfd75d8151004ff74d815101cfe74d8151004fd74d815101cfc74d81510b67f54d81510067d54d8151004ff73d8151014fe73d8151004fd73d8151014fc73d815100cfe72d8151004fd72d815100cfc72d81510b6fa50d8151006df30d815116dde7398151005dd7398151006fb6098151175be7418151005bd741815116dde7318151005dd7318151165ee7218151005ed7218151036fa6018151006f9601815102e7f7559621004ff745962101cfe7459621004fd745962101cfc745962115e7f54596210067d5459621004ff7359621014fe7359621004fd7359621014fc73596210067e535962115e7c53596211667f52596211667d525962102cfe715962102cfc715962102e7e515962102e7c5159621004ff7059621034fc705962115e7f5059621006df305962102ef71059621004ff7558221024fe7558221024fc7558221004ff745822101cfe7458221004fd745822101cfc74582210067f54582210067d5458221004ff7358221014fe7358221004fd7358221014fc735822102cfc715822102eef215822102eed215822102efb7058221006fa4058221006f94058221006df305822105efa205822102efb105822102ef81058221024fe76d95211467e65d9521006dc63d952100dee72d952102ded72d95211476f52d9521004ff74d952101cfe74d9521004fd74d952101cfc74d95211467f54d95210067d54d9521004ff73d9521014fe73d9521004fd73d9521014fc73d952102cff72d952102cfd72d9521146ed72d952102ced72d952117e7f52d9521146ef52d952117e7d52d952117eec52d952100cfd71d95211467f51d9521034fe70d9521004fd70d95211467c50d9521006df30d952117eef20d95211467c6559521005df7359521135dc7359521006dc6359521385f7715952117cff75595210067f7559521004ff745952101cfe7459521004fd745952101cfc74595211467f54595210067d5459521004ff7359521006df7359521004df7359521014fe7359521004fd7359521014fc7359521006dc7359521014dc7359521164ff7259521006ef7259521146ef5259521166ec5259521384ff7159521006f77159521004ff7059521
  | 13 => 0x8152005f57118152036fa6018152006f96018152186df7558e51186de7558e51396dd7558e51186dc7558e51006df7458e51006de7458e51006dd7458e51006dc7458e51396df5458e513965f5458e51396de5458e51396dd5458e510065d5458e51396dc5458e51006df7258e51006de7258e51006dd7258e51006dc7258e51396df5258e51396de5258e51396dd5258e51396dc5258e51006df4258e51006de4258e51006dd4258e51006dc4258e5102edf7158e5102ede7158e5102edd7158e5102edc7158e5102edf5158e5102ede5158e5102edd5158e5102edc5158e5102edf4158e5102ede4158e5102edd4158e5102edc4158e5102edf2158e5102ede2158e5102edd2158e5102edc2158e51006df7058e51004df7058e51006de7058e51006dd7058e51006dc7058e51396df5058e51396de5058e51396dd5058e51396dc5058e51006df4058e51006de4058e51006dd4058e51006dc4058e51006df2058e51006dc2058e5102edf1058e5102ede1058e5102edd1058e5102edc1058e51004ff7458a5101cfe7458a51004fd7458a5101cfc7458a511467f5458a510067d5458a51004ff7358a51014fe7358a51004fd7358a51014fc7358a5102eef7258a5117eee5258a51146ed5258a51006ef4258a5117eee4258a51006ed4258a5117eec4258a51006ef3258a5117eee3258a51006ed3258a5117eec3258a5102cfe7158a5102cfc7158a5102eee2158a5102eec2158a51004ff7058a51034fc7058a51006df3058a5117eef2058a5117eec2058a5102ef71058a51146ee7558a51146ed7558a5117eec7558a51006ef7458a51006ee7458a51006ed7458a51006ec7458a51146ef5458a511466f5458a51146ee5458a51146ed5458a510066d5458a51146ec5458a51006ef7358a51006ee7358a51006ed7358a51006ec7358a51146ef5358a51146ee5358a51146ed5358a51146ec5358a51006ef4358a51006ee4358a51006ed4358a51006ec4358a5102eef7158a5102eee7158a5102eec7158a5102eef5158a5102eee5158a5102eed5158a5102eec5158a5102eef4158a5102eee4158a5102eed4158a5102eec4158a5102eef3158a5102eee3158a5102eed3158a5102eec3158a51006ef7058a51006ee7058a51006ed7058a51006ec7058a51146ef5058a51146ee5058a51146ed5058a51146ec5058a51006ef4058a51006ee4058a51006ed4058a51006ec4058a51006ef3058a51006cf3058a51006ee3058a51006ed3058a51006ec3058a5102eef1058a5102ee71058a5102eee1058a5102eed1058a5102eec1058a51004ff745825101cfe7458251004fd745825101cfc74582510767f54582510067d5458251004ff7358251014fe7358251006de7358251014de7358251004fd7358251006dd7358251014fc7358251004f
  | 14 => 0x303301000800400b00800200200105e00200005b00a00200500200401c00300300000200200a01500200a01102a00000600000501000600c00200003e00000000300501000200600800900000500500400000000200d00900500000000e01c00300800000d00800e02200000002602001c3adde76d8d52196de76d8d52014de76d8d52006df64d8d52006de64d8d52006dd64d8d52006dc64d8d523a75f54d8d520075d54d8d523a7cf52d8d5239f5e52d8d5239f5c52d8d5239fcc52d8d52005dd70d8d523a75f50d8d5239fcf20d8d5239edf75d8d52196de75d8d5239edd75d8d5239edc75d8d52006df74d8d52006de74d8d52006dd74d8d52006dc74d8d523a6df54d8d523a65f54d8d523a6de54d8d523a6dd54d8d520065d54d8d523a6dc54d8d5239edf72d8d5239ede72d8d5239edd72d8d5239edc72d8d5239edf52d8d5239ede52d8d5239edd52d8d5239edc52d8d5239edf42d8d5239ede42d8d5239edd42d8d5239edc42d8d52006df71d8d52006de71d8d52006dd71d8d52006dc71d8d523a6df51d8d523a6de51d8d523a6dd51d8d523a6dc51d8d52006df41d8d52006de41d8d52006dd41d8d52006dc41d8d5239edf21d8d5239ede21d8d5239edd21d8d5239edc21d8d52006df70d8d52006de70d8d52006dd70d8d52004dd70d8d52006dc70d8d523a6df50d8d523a6de50d8d523a6dd50d8d523a6dc50d8d52006df40d8d52006de40d8d52006dd40d8d52006dc40d8d5239edf20d8d5239ede20d8d5239edd20d8d5239edc20d8d5202cfe76d8552006df63d8552006dc63d855200cfd75d8552004ff74d855201cfe74d8552004fd74d855201cfc74d855238e7f54d85520067d54d8552004ff73d8552014fe73d8552004fd73d8552014fc73d8552024fd72d855238eef52d8552386ec52d855238ef651d8552386f621d8552034fe70d8552004fd70d855238e7f50d8552006df30d8552386ef20d8552195de7398552005dd7398552006df6398552006dc6398552006f76198552005df7358552195dc7358552006df6358552006dc6358552006df6318552006dc631855202ef66118552006f56118552034fe76d8152195dc73d8152006df63d8152006dc63d815200cfd75d8152004ff74d815201cfe74d8152004fd74d815201cfc74d81523667f54d81520067d54d8152004ff73d8152006df73d8152014fe73d8152004fd73d8152014fc73d8152006dc73d8152014dc73d8152024fd72d815202cfe71d8152004fd71d8152366fa50d8152006df30d8152296fa20d8152195de7398152005dd7398152006df6398152006dc6398152006fb6098152005df7358152195dc7358152006df6358152006dc635815219dbe7418152005bd7418152195de7318152005dd7318152006df6318152006dc6318152005f6711
  | 15 => 0x400300500300300101e00c00d00000100100c00301a00403e01800200001e00000100400100a00d00200100605d01500100302402c00401700300100000900101200200900600100500000000200500700500400000100b00802000803800700200300802602000700001400300100100000400000100b00100400000401002300f00400100202201800400600200002800400100001a02600000700a00200100200001800e01300000700301f00301000b02b01e00100401600800801700004d00102000400b00000e00d00100700000a00300b00002300300000c00000000200c00300703800000500c01302f00500a00100300400400300300200200200600000900000f00800c00300102200100300600400600d00200000000200501800700100400601800900300000000e00200900300101000000100000000000400900100000600e00400300000000400103500200200200900300300000000900001900600a00300600000b00200400700300000402c00200400500000100600000b00301d00000001800000100f00000100100700301800000b00c00000900300101200000100301400600300100000200000101100100900200000000e00001b01b00201401800200000400200000000006200901e00200201c02300700700500302a01800200000700e00100101a00402300600501200202500e00300600200000100301400b00200200100003b01e00005c00100100300701600000900000400601100200200601e00403100800401200000704600004200f00500300100000000100500100000200000000100002401a00000100200000000a02100000400000100501f01800100800000300100400a00801300900b00000400203f00800101400700100100001300100000000800000003e00000a01900900000401200001100000600000200200201203400900100200000300900500c01301400a00100000000301901100100e00000200200200300201400800200100700300c00002b00500f00100000000300000101b00900e00500400c00000000000300100100603500000000001b00f01f00504a00100500500d03b00400000400b00200104800c00600600700d00900b01800002000000000300200000000000600300000100200203700200700100900300000000800702d00001f00b00000100100000c00e01100600304000000301302700a00c00000300e00c02f00000a00000400702900200400101a00200000b02000301000500601c00200300000501600b02500200100b00406300a01001300200e00500700f00102700000703300002500100100200700703500b00301800500000100f00600100500002800d00000900403600e00400b00300000702801500600200e01200300a00900000100900100100102b
  | 16 => 0xbe00036a0f343287293620000ac400001f9c687ae45e000253134e68f00013a50580002689fe4816000000000044c23600817bd17a00743c12900c224a3f41b1c5369490dd9b489827cb0658cf0a248e71b18140a762443d68c0c5ae6814930cbc2b064b0af8ea006e6390fc220097038c1d686fc2801a52dca3941a09324d916dc4ca31244884c890265d2061ee873658149f00007d06460002611272420000221c4a23b22ee93104226901531de80003510949dbc29e0003648d400000004e300005144840c696e8d9a0000000524f387363f718080a49431189d7c82e0310fda10870a43c2728e340000fd29300011be52243a1c2815654941c80a021667c30f1a580ac07f2ac0fdc6447702e900ccd5c6b54e5995c7d600027423b92820be27e8f553be7ec0001da46cc7a507c19ac3f8990355a3a026e0000000db465295046c13bccfa0001dd927808a899369a4150d01574a909e4e58699323a47450438e379981c8d47033dea22521252a000000057408d12f83952e02fa2c41c653024ca4e00438fa801e2f624c05ea72e0001464dd48ad0000c6c00094f10022a82909d8000000000074600018c0fe00003609eac51655c31d94c123056812015bc74601b20b15fcdc404b00006181268c13210ed4a007fc00009a000000008088fcca427d00005c8d361fd21f80008320002a1802c71000000000009c68e622a8cf435e000000261931a4a11cd18904c050d223827448a4ba472000041c2c04561b3c0004fe0d392a49208c41e19cbc43e2302231714f920000f699a53c092505b0adce8e5bb062a198bb8975259244c85801115a9eb0fe4067000099ca6c16f147a358cc43a602ca4c4bd02030001bd42c00ea1a69e543aa91200002505a69960840fe8a148bc21793393280240dc8484c8881a00026c47ca29d01f0b60f7e3533b4077472870e33a9028b5206214f8f851ec50544b0000fb62e43701490abe4e00a89b28ca696d3e61bfc0007883b70978dba0790001360aaa2ee0002750c2049441100000004a61eda18400049221c00007985a5201a2152b41df1881acc0000004048dd437470b14687100003e600000002fe06e1cf98300009c90b1800000031929f22f8c1a58c1e299d8c6296300215f049c19a4e217ac30a6dc46b8000c289bd3a088505880000d7092400050c3179c7c5a20003f89e8506a00028a1cc52a87430e29bf038449f2e817849046550758ced15021e244a48c35a01100600300b01400801100b00000100000000000101c00800b00701200900000f02801100400500600101703c00400000700600400200800c00300000000400f00e03300000400600200300200000000100500900e00c01100301c00400500300200500101400300000200000900000100800500000000400200900e00a01a0070030020
  | 17 => 0x67a1741fc00000011391aa000458990105428544e85644f44b1326215459054c1758d680000d50001898b6c55b0f78494bac1394841548f7867200183d0c5200000014bc0004eb3529c800c061548c800000040800018e0262000000000101e4db3b69c1800000000000007c8742392918c73c95811084fc1ea0003912740e9852c31ea3fca669dc27c95948dc46b0000000b2259c00002304749b8294000058649611d896476095e15b0264856933000000000061d338142c00066800007d43548511160c090a0537081256cd7c9d7091a2e461092918c2404fd2227434a6908c218317d87d119a0b80d8160095832132c846800008e10300004043dd2088380b5400021700006846cc0fd1ed91bc4b71d6045454219f03412ac00094720f8c28530223000000000044c3c68000c0030025e8d012aa0003ef8068000000420263132615e48f9d941865a60971038e1e05b41180008747a73191968bdc00028300012c20003b923642ce25a4888d54b8c0002c3205c000000070931c2849a50d01ded1ee4d92908fc432077c4e6247138a79b1fc800000025537420ac60a7610cc10111a03a533d800000053d0000000b1a836000043484200000020553740bd1ab1b5400089000002b539053c41e000000000017398280002ad3cc0088dee000000139800060325e172441886e15600001886372e7844001a8ec0000ea4f7000000026fc00000000026380560da352245c3422c11230a78cd85ff18d1b450b2357243a4ec97652300003885663de2300594c345d546310f80002f8430000000049c0001f5c2740ff095822c0007b50cd810d0fc6670030abc0007752618000cc86180000bf8df68c300017dc0006f41c1014c94a8a223908cce0a7962c11d7844497f1080dd05da3b737592cc30e2370c89cf83661e613e1ec85d21220931c4cd0e2911418efd0182e231e266c09a5e3125944c65a19c4f21fdc3526f02901a80d3021237395781f437b2c395d804a4b61ac07709ea7d044f8c501540a713f0a1d1743164791e985b275a483969c10e7771029510ee69e91b2257028e29a4b60ff8fe60bc33fa5581c8141216998d1941e11b117440cc9af3df0ee032a378053075cf0e9a237891406083ba0399980d4e26f08916d08ac0d12a7207009e3d42b800a4f067534a6a6f8e4c6ef18b80010c400048100008686931c79de070e36c16800b44b05840b60ca89e04ea2daa04cdc20004da1494e787ff170995020c6a6281133039e7d119b9b6102842300005e10a84951a40fa8afc81f06095c8b500854a11e489469d211c98b890c3c706f21041b22c945703d8d6c0d41c089ec6ce9643509d70c9a5f141680001e41ea0d30f612688032cd8730c2e3600050ef05700a00e7254d3545341f91d9c92257a439149c8c43af2d60f8cd5e6b100025d07
  | 18 => 0xc0800036c8a811607330da08c80000403e30bd00000003fd00000003e028394208b059026b81d50862a5000000000015a38a8fcceac0000e00e90c448043790dcc3fe1240000e9c9062cc4bea0e063a41a129a350aa62b90daa2511921f901a87d8d8a07c33c81b0bda0a338e0d84dda5ad0e8032491e8633cc8014af228e42685a09ce18438ba23c6748c811494a4a5c54727f88b847c1be3e921d800084c03c2528000457396809c0000004af97341689a14b79e889c200000000008046ec12080000006cb1b421e864e67a1700c3494497e454970cf344cb3e707b03043c9196085c7a27c50a282e40000000000b352786e648006045d4704457800086491b3fc19dc1de8162878a1800002a000000061e810126211831e97c09a053925416b44914acc260000000d0cf600000000430fce00013a0ef47da51c2e217500001b61c980008de3ab1ff8a8c22c1c94d986780000000f2800033237d0f109dc00099738ea64481e0004bd93750ce55111ea74c5109e70000000d2e8a52d7230837a00043a9ca8c22284424a60c87a4b41af834c4fe6bd31f1a200002631f611d061883f35d1e400e20002279a1040e98f0e50060f8e00031a1534e5080d4799a009c417e20f09c0278352000217000044800020bc00063f0001ae000092d0b122ac6a80000d20318c1c66100023f4a944654b417053d622811680d8f124ad163a75511416913314c40007112aea1681e60e625aa09cf3c9ad0071a703d09244a280003b600000004740000000000000000694000000000003b4dc8e2839636f00000002dc59208211f47c43ef1480cd00000004d61e08ec83460001df8f4634f30e16bcdb600023b0b150e200013c15c4a3a7d90000000e2800000000011641c1058000019c12a000000038677f0cb80007dc6561348000656000233078c4c46fe09680005c684b3ac82945944f74508b98bbc4403aa27340b40003f6937019a74d42f278cfa634700000012a264f0e900008ee7aa32e015d1a656749d1be03100a10f880012d409a1b705b400029348d146d2ee0001a700011d455701c800008c0004979b092f28114cf8bd81c6744082a4dcfe887f00000548f23e93138940000819000000104c0000002060d72000000046d0ee1f72b4827811e49d000000127a06312b80000007020000cd427006f0001dac0002d208f800136a00000026280000000000000000000000079c00073b0000e553ca000000271c6fc000135a29001012c37d05f44407b33fb1eec61622a1678d6442a7a42f50dc41082a7225a2dce9605f47f269864a0ba117951522c00000005d4a8c000010a78800054000024189368f81122674a7473430295b4130609338800005843047807b879e96009e8ff48b688b44301211e28d1307895004018e2a8039c53899e07d8ac106407d2
  | 19 => 0x272880c62c203800135642a27912bc3146352c19798e903a0000135000048d0000cc80002160000d100187d84ae9a312563920001aa4ec078e4ca8fd800095741002551d286b23e000000000000025b81381f205608ac22e0cc37e811095c7372e726a400000049a89a85540b510c07688e000012900001d20d748700d12d28e1400800116808003a1858b8e2da22527091101b11a511e8000119000114433a45c3e6967cd504140001f20f822733429e3c7442482349a5500020418f9580f6e9c30640be426a5be36825e0a3c41d1af0c80a2092c17b800114600000000000000000250d6d07c5c83590c38000000152261521411c46e12151e83c214b97e506e0d239c1bd80aa2c23aaa3689f843b3c291fc9f01d337196f10040a223a98640d666f486056d1965f5441a0753d008121c9d283466da432206cd141a21e4089435654b3f593b0ea08cf42f8d7013e3411989a7c1f223532f11b13d85b828091345125953ac0e0c3900f02c49ebcb607e51b5825ce0204e00009c899000041a21605aa08a249a0a4b7e7c03b6087099a5f3100a7991184240010e6486c275208007cea24be0851c40d540260350b7d1a479f4278000cda0000000b506fe3901238b580003772f01ea0be400022a05d000048a35d86dcc468251df25c91b679719706f13302b448a8aa4000370198000002e47129c017051800045016850ac9a3098273c1f84130bc883c17e61f000000000025d0d92260b0a00039900009300a84d700009f4718104109d3b61554c421bc00000000000745e43d03008c7918084a03d82dc73018c21117ed0e059629ca43c29663341e80012960c200001c80a858f2ed1dc4f2275200021b4f404d60000ca0a2a1b843c9e100c82ef21280010ae2940000f10b567e24181124e4607749417e0ad654f2f817f8a5a98226a80240784450001f1000066645c0ea905c8dd2f2a25c00073519c03b8e2434b33c1d38b165ca11a26d8f2667e15e23bc0000004a404ccd467001be12a91c465108a126400089c000220498c07e09f1bb82c809b00000000000000000bb0f2831c279841c0005983b10ec4d582ce180a4d901c20b1279f80cd458a2e0122c55028006b1da85b621315e849c2e00910b31014d787e12cf000002453f0381c900027ea000140c7ac87300021ec0009870000000d1a6c04599048adc9b7000119c00096b0f2096c15c0a939e92a09c86c33ea8f18ae8480172836029400022f981800008623c054d2443da18a9f78d6e8fc327201c358196476808c7f638407ba4b80846b447019288c873a21b8c8c4da1133fe92fcba686544da4843ac5992ba90c40003f002f000000008324b80000000002130f48b3a11e000000000021a000000064c2fd481850c7665321fa00e89e23c136f037cd3c3dc16f1a08fb48311830bc0
  | 20 => 0x259c00074f03d2680bb056300a22d528c1d81c5930855c25c07407812f49da1e597091f62e800000001ba56a137126800000042d80002ba0ed384848025e7fe27d80000000bb18880000006bf1e000000004520002764b280003fa986c7ce2a2351000099283a2c700000000000001174a2e0000000000b640ca3fda6a0fcc1931fe0000ee82642e6106c6ec000419853460e516130a208f525643e11558e8a6282d989088129bb0be1ba4b265094ee8e840001c73e18ee41d87662cb80006721364eb03c46666ad2bc0e24dae7b902e95b0ec639c0b50dc81208eb1db21a868a8cc17e134c0001a8493800043204723f13d92ec34c1b293d10880af12b17f4e181c61eca59855686c0001f580000db1c890ccac298b0000e5c2a40b20f991b4f0c5cb024a24cf1839d00017d9240730000082900a6490601884e5679d01c02c400000049f8b2c0ca88d0348000f62401179922000027119f997c06060b2d20de50a400000000000005b10001d00000444088a1144781d913b003cf5c1501fa90702304da000209137894000023e501664820007c12e207635809b06128063a4916452a0000449fbc62601900020ec00033634e9cfc2ee243332989483048e33980003121442ad0afc000109345a64812c2bb0598000f0000036b031c11078a2770c90e1091e44724e072c78b06e2138c5a3860ff18d821e03d36f84a0eb69b029a8a4852c18b3e51a3869291416e05843a84d02068070acc5a00bd1508c5660834d110c3a21cd33a0874000000463a3d44365e74670f4d1f433e390a0202e654801716680009994140000f020003be90a000000020a80000b071b22d2624c8a000036800117e0133641f3c00072709d85310f82b20ab00012e60001ae80c898a4c02fd06486d25fc028a66908e96544a95508f69624ef05c43bc87d2ec91080003ca4ce137c5e20004e8988000071e4628b74d225e24091b38a3e51131d08e0ab20003208000000000000202819e6833ae80010420002209ed000000000000000001e92581f9000089e48814613828a70bd9d5ce2c5772bd97d00009043f1893428c6c63151940e720000c00058fba1eb3728290ae63ae2d1040139c6f923980bc7f050e471820879c884140800128804c0bb15f453248c4f510d400020d00017a42065d70000824bb6092343129c00045300000011340000000000b7a000000177c0003b43bb0000dc864332c00009727dc00000005fe15c45b00000005e400025389da000000207800036a28d2564a82848000000121a65b000000114c0002148000e0e4a026f260000077948580008d015400000000000001630e009a4853386800000000000022ec57c6120001a24cdc0000001a48b462b102094113c237a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaad82dcd640400187aeab9ac8080028fa1473590100051ec28e6b202000e1f5394d640400117d0e29ac8080022f61c53590100051f42ee4b202000a3d85dc9640400187aebb92c808002a7a0f72590100054ec1ee4b202000c3d755c9640400147d0a392c8080028f61472590100045f438a4b2020008bd87149640400b56d02192c808002ad60432590100062fbaceab182000a9e841d5630400153b083aac60800297a167458c100052ec2ce8b182000ace829d1630400159b053a2c60800297a147458c100052ec28e8b182076c5f70d5163040ed8bae1aa2c6081de976165458c100070faa4a8b1820008df8755163040011b90eaa2c60800317e1d5458c100062e43aa8b182000e1f845516304001c3ce8aa2c608003875d15458c103c70f20aa8b182078e1c4155163040ef8bee0aa2c6081df175c15458c103bf0fa02a8b182077e1d4055163040ed4bd0a2a2c608016b5a047258c100456ac08e4b182000a9e84149630400153b08292c60800237a1f4258c100046ec3e84b182000a5e85d0963040014bb0ba12c608003875534258c100070eaa284b182000a5e8510963040014bb0a212c60800f0f9d154588100061eba2a8b1020068ee87d49620400d1dd0fa12c4080029ba17425881000536c2e84b102000e2d54d09620400159d07a12c408002b360f42588100347643a84b102000e2d54509620400d1dd0f992c40801a3b21d325881000567c1aeab102000acc835d5620400155d083aac408002ab61075588100053742ce8b102000a6d859d1620400159d073a2c408002b360e745881000537428e8b102000a6d851d162040edc9e61aa2c4081db934c354588103b733886a8b102076e6510d5162040ef4db0b2a2c4080038bd52545881000567c1aa8b102000acc8355162040015cf02aa2c408016b9205545881000717c22a8b102000e2e745516204001c5ae8aa2c40800393e0d54588100072641aa8b102000e678155162040f1cc902aa2c4081e38b90554588103c71620aa8b102077e2f4055162040efc5a80aa2c4081df93cc154588103bf26982a8b102077e671055162040efcca20aa2c4081da9ba14545881002d73408e6b102007ae5811cd6204001c9ea729ac408002aba10535881000556c20a6b1020008ee87d0d62040011db0fa1ac4080029ba17435881000536c2e86b102000e2d54d0d6204001c5aa8a1ac4080029ba14435881000536c2886b10200687c85dd952040051b907bb2a40801a3b20b76548100046fc1aeca9020028dc835d9520400d0f90eb2aa408003171cd65548100064e39ac8a9020008dd86dcd52040e98bccbb9aa4080031759773548100064f326e6a902000c9d64dcd52040e799cc5b9aa40800237a1d63548100046e43ac6a9020068ec87589520400199ee6b12a408003331cd6254810
  | 1 => 0xf08bb2a48800e2f21176549100046fc1aeca9220028dc835d95244071acea8b94a28800359551729451002e73b02e528a2005de3605ca5144001bc480b94a288003785017294510006e3982e528a2000bb1841c15144001998e7b1242880167960b75485100347a432ea90a20069f0805d521440dd9a8edb9a4288002ec6107048510006e9b98e090a200697487545504400d4e90ca8aa08801adc201515411032c6f43eca98220348dd87d9530440011bf0eb12608800a3721d624c1100052fc2ac4982201fa5c85589304400153f08b12608807aa7211624c1100356b436e29822000bc5821c530440013ad0f28a6088002f160a514c1100356a432a298220009d487485304400d5a90c90a608801af4201214c1101a56c432a09822000f5151541304400d1ed0db8a408801a7921d214811003572432429022006be08048520440070f90bba2ca080030fd5174594100046fc1ae8b2820028dc835d1650400b1e902ba2ca0801a1fa1e54594100061fba4a8b28200687c87551650400187ee8aa2ca0800297e0d54594100052e41aa8b282005a7481551650400d0fd0f29aca0800317dce53594100343e43aa6b28200687e8794965040ed8be61ba2ca081db174c374594103b63b886e8b282076c7510dd165040ef0fb0f3a2ca080030fdd274594100052fc1ae8b282000a5c835d165040014ef02ba2ca080169d20574594100061fc22e8b282000c5f835d165040018b906ba2ca080031de0574594103c63a40ae8b282078c3e415d165040f187882ba2ca081df17cc174594103be2e982e8b282077c77105d165040ef8ea20ba2ca081da1fa1c74594100062fb9ce6b282000a3e841cd650400147b0839aca080021fa1f43594100043ec3e86b282000c3d74d0d65040014dd05a1aca080029b60b43594100061eba286b28200087e8710d65040010fb0e21aca0800297e0d72594100052e41ae4b282000a3e841c9650400147b08392ca080021fa1f42594100043ec3e84b282000c3d74d0965040014bd07a12ca080029760f42594100061eba284b28200087e8710965040010fb0e212ca080169da0432594100053ac0864b282000c3f759d564040ef47b0f3aac8081db87cc275590103b70e984eab202076e37109d564040edc74213aac8081db8d44275590103d71c884eab202000a9f835d5640400153906baac8081e6ade05755901002d5a40aeab202000c3f875d56404001c3f06baac8080038720d75590100071bc0aeab202078e34815d564040f187ce2baac8081e30f1c575590103be1fb82eab202077c3d705d564040efc3e60baac8081df874c175590103bf1b882eab202077e3a105d564040efc6a20baac8081e38e44175590103b51f428eab202000a3e85dcd640400147b0bb9ac8080030f5d7735901000557416e6b202000
  | 2 => 0x15458e1040f0f20aa8b1c2081e1c4155163840efc3e80aa2c7081df875015458e103b52f428a8b1c2000a5f855c963840014b90ab92c708003335c87258e101a56b408e4b1c2000ad5811c9638400153d08292c708002a76105258e100356d400a4b1c2000ad98014963840011bd0fa12c7080023761f4258e100052f42e84b1c2000a5d85d096384001c3aa9a12c708003875514258e100052f42884b1c2000a5d85109638400d5b500212c708002b66004258e100052fc2ae2b1c2000a5c855c5638400153f08b8ac708002a72117158e1000567c12e2b1c2000acc825c563841015b700b8ac708002a7a135158e100054ec26a2b1c2000a5e85d0563840014bb0ba0ac70800f0f9d15458a100061eba2a8b14200087f855cd62840090f90ab9ac50801a3b21d4258a1000716aa284b1420028dc83dd952840011bf06bb2a50800a3720d7654a100343e43acaa9420008dd86dcd52840011bd0eb1aa5080023721d6354a100347643ac4a9420008dd86dcd21840dd1bd0eb1a43081be3721d63486100146f41ee9b2a20008dd83dd365440070ff0eaa6ca880030f5d154d95100052e41aa9b2a207ec5e7355365440011bb0f39eca8800a37e1d73d95100062fc2ae7b2a2000c5c855cf65440018bea8b9eca880031755173d95102d46fc02e7b2a2000c5d7394f65440051bf0f986ca880023761f30d95100046fc1ae8b2a20028dc835d165440011df04ba2ca880063b20974595100047bc0ae8b2a200387c87551654400187ee8aa2ca8800f0f1d154595100043fc2ae6b2a20008bf845cd654400717908b9aca880023be09735951000c76412e6b2a2000c3f745536244007878e8aa6c4880121fa1f75589100043ec26eab1220038be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c4880121f21574589100046fc1ae8b1220028dc835d1624400117d0e3a2c4880030fdd474589100061e3a8e8b12200087e87d5162440090f90faa2c4880030fdd3545891001e1e3a6a8b12207fc5c73d5162440010fd0eaa2c4880021f21d54589100061fba2a8b122003c3c7455162440fd8b8e6aa2c48800a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062faa6e6b122000c5d54dcd62440010ff0ab9ac4880121f21573589100045fc22e6b1220038bc845cd62440011df04b9ac48800237a1c73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100066639ee4b1220038ec875096244007958e8a12c4880038b55142589103ee6639a84b1220008de87cc162440051b90f982c48800317dd730589103e62e3ae60b122000c9f74cc162440f7938e9982c48800a37a0e76549100046ec1ceca92200087f855d9524400117
  | 3 => 0x2b1c4000e1d54105638803b59d0420ac710002b36084158e200356d40082b1c4000ad98010563880051bd07baac3100023760f75586200061fba2a8b0c4003c3c7455161880010ff0ab9ac3100121f21573586200045fc22e6b0c40038bc845cd6188001c6aa920ac31001a3d21d41586200146f41aed28c40008df865ce51880011bf0eb1ca3100023761d63946200ee67392c728c4000cce635ca518800199ac6b94a31001739985729462000672b92c328c40068f48758551880051bd07ba6ca900023760f74d952001c3fc3aa9b2a4003c3e74553654800187ae8aa6ca900029720d54d95200062eb9ca7b2a40008bf845c7654800717908b8eca9000237e0d74595200146e41ae8b2a40008ef825d165480011ef02ba2ca900163d205745952001c3e43aa8b2a4000c3f7455165480fd8b8e6aa2ca9000a37a1f73595200062faa6e6b2a4000c5d54dcd65480010ff0ab9aca900023be0973595200046f438e6b2a4000c5f751cd6548001998e7b92ca9000237a1f30595200146e43e60b2a4074ccc76dcd52480011bf06baec29000a3720d75d852001e1f3a2a9b0a4000c3d745536148001c5aa8a16c2900023de1d611852002c76414ed28a4000c5e73d9651480518d8cab94a2900a31b197754852003476432ea90a406dccc76dcd214800178b0630a429000372dcc7048520034b643aa4a824006a6c86549504800d6d100a92a09000237e1d654c1200146e43aca98240009cc87549304800d5990ca9260900027321d214c12003566432429824006bc880485304803b5b10ca826090003d2549504c1200046fc1ae8b2e20028dc835d165c400b0f90eaa2cb880030fdd1545971001e1e3a2a8b2e20008df835d162c40051b906ba2c5881ff171cf5458b100061fba2a8b162003c3c7455162c40fd8b8e6aa2c58800a37a1f7358b100062faa6e6b162000c5d54dcd62c40db1bd0e39ac5880163ba1f5258b1002d7340ea4b1620058ec8750962c4007958e8a12c5880038b5514258b103ee6639a84b1620058ec874c962c40011bd0f982c58801a3da077654b100046fc1aeca9620028dc835d952c400d2e90ea8aa18820e3721d624c310004ea43a4298620069e48748520c40011bf06ba2cb0800a3720d745961000477c12e8b2c20018ec825d1658400d0f90eaa2cb080030fdd1545961000477c12e6b2c20018ec825cd65840018beeb3aac708002b3e097558e1000566412eab1c2000a9e841d5638400153b083aac70800297a167458e100052ec2ce8b1c2000ace829d1638400159b053a2c70801ab6a027458e104156cc04e8b1c2000a5e851d163840014bb0a3a2c7081de976165458e100070faa4a8b1c20008df8755163840011b90eaa2c70800317e1d5458e100062e43aa8b1c2000e1f845516384001c3ce8aa2c708003875d
  | 4 => 0x14c111a9ce5aa0c29807b479d154185300068eba2a830a6084d4e72550614c001a9ea8b90c2980035355172185301a667b0ae430a6034dc6615c8614c06999ac2b90c29816b33d817218530006e5b02e430a6034dc7105c8614c0011bb0f310c298003335ca621853000666b90c430a6000ad581188614c0013af0eb08c298003715c9611853043de9c02c230a6000c5f549da514c0018baa93b4a29800a3760276945301a66b884ed28a60009db805da514c0018bf0abb4a2980031721576945300062faa2ed28a6000c5d545da514c0019b700bb4a298003175db6594530006a7396cb28a6058d4f545ca514c001a9aa8b94a29816b33d817294530006e5b02e528a6034dc7105ca514c0013b301bb2a29800257e157654530004cfc22eca8a601e99c845d9514c00139f04bb2a298076732097654530004edc02eca8a60349d6819da214c0013b700bb44298003335db62885300ede2412c310a6000ec762586214c10d7a700b0c42980027660376485300062faa6ec90a6000c5d54dd9214c0019b301bb2429800237a1a7648530004afc2aec90a601f95c855d9214c00133f08bb2429807a672117648530004e7c12ec90a60009db805d9214c0018bea83b2429800317550764853000667410ec90a6000ccd821d9214c00199ea43b2429800333148764853000667210ec90a6000ccd421d9214c0019ab023b2429800333884764853000666108ec90a6000ccf201d9214c06939b05baa429800237e1975485300046e432ea90a60349cc87589214c001998ecb124298162d3215624853042de5c02c490a6000cd476985214c001d8cc530a42980daf460261485300ecea43ac290a6000ec562585214c0897a700b0a429807f17ddb6554130034ae43aa4a826000a5c86549504c00d2b90ea8aa09800237e0d74596200146e41ae8b2c40008f7815d1658800b1e902ba2cb1001a1f21d54596200061fba2a8b2c4000c5f759d5638800159f04baac710076b32097558e200054f420eab1c4000a9d841d563880014bd0b3a2c710002976167458e200ed67414e8b1c4000acd829d163880014bd0a3a2c710002976147458e203bd2ec2ca8b1c4000e1f5495163880011bf0eaa2c7100023721d5458e200062fc3aa8b1c4000c5c875516388001c3f08aa2c710003879d15458e200070eba2a8b1c4084e1f425516388109c3a84aa2c7101df87d015458e203bf0ea02a8b1c4076a5e8515163880014bf0ab8ac710002972157158e200054fc22e2b1c4000a9c845c5638800159f04b8ac710076b32097158e200ed67410e2b1c4000acd821c5638800153d09a8ac710002a76135158e200356d400a2b1c4000ad98014563880014bd0ba0ac710002976174158e200070eaa482b1c40008de8710563880011bb0e20ac71000297a144158e200052ec288
  | 5 => 0x80025761375589300062fb06eab126000d5b60dd5624c0018beec3aac498002c7610755893000726310eab126000ccc62dd1624c0012bf0aba2c49807e57215745893000666312e8b1260009d7815d1624c0693a902ba2c49800276e017458930004af43ea8b12601f95c87d51624c111c98c5aa2c49824b56dc35458930004af43aa8b12600095c87551624c03da3ce8aa2c498003475d1545893042726312a8b126091d5b70551624c03b59d0db12c498003531d76258930006adbaee0b126000d5875dc1624c121b96e5b82c49823fb218b7058930004ecc06eca926000c5f54dd9524c0018baa9bb2a4980033660376549300046f434eca92600095f855d9524c00139f04bb2a49800276e0176549300062faa0eca926000c5d541d9524c00199ea43b2a4980031794876549300062e290eca926000ccc521d9524c0018bea03b2a49800333c807654930004e7c12ebb0a601d9cc825d7614c0691bb0e32ec298002a761065d85301a56b408cbb0a60348dd87d93614c0695ad03b26c29807b479d154d85300068eba2a9b0a6000e1d64553614c0691bb0fb16c2980029721562d85300ee66392c5b0a608ed5970d52614c103a3ee8aa4c29807b471d1549853046eacb82a930a6000ccd7298a614c00199ee4314c298002b5604629853000763108c530a608cdd170d86614c03f2bd0fbaac2980025761375585300062fb06eab0a6000d5b60dd5614c0018beeb32ac298003271d2655853000666394cab0a6034ad681995614c0018beea32ac298002a761065585300064e3a0cab0a6000ccc72195614c03d33d0fba2c29800347dd774585300068e3aee8b0a6000d1f85dd1614c001a390bba2c29800327d837458530006cdb06e8b0a600095f855d1614c03f2b90aba2c29800273e0974585300ece6412e8b0a60009db805d1614c00133d0e3a2c29800347dd474585300068e3a8e8b0a601ec9c74d91614c001998e5b22c2980d23721d64585300f64e3a2c8b0a6000ccc72591614c0695a902b22c29800257a1f54585300fcae43ea8b0a6000d1f74d51614c03da38e9aa2c298223531cb545853045eadb86a8b0a600095e87551614c0012b90eaa2c29800347dd154585300f68e3a2a8b0a6000e1d64551614c109a98e4aa2c29822b56dc154585300ece743ee4b0a6000d4f75dc9614c001a98ebb92c29800363dd37258530006c63a6e4b0a6000d4f54dc9614c001a9aa9b92c29800333d837258530006e5b06e4b0a6000ccf761c9614c001a9eea392c298003531d47258530006c7ba0e4b0a6000d8c741c9614c0011bd0fb12c298077331cb62585301a46e43ac4b0a6000a5c85589614c03b998e4b12c29800356dd77058530006ac3aee0b0a6000d9b74dc1614c001b30e9b82c29800372dcb7058530006e4396e0b0a6089dd371dc16
  | 6 => 0x64fba0c6b024200c9c7418d604844d1bb0fb18c090803179d763181210062ebaec63024200c9e74d8c604840193ae9b18c090802b660363181210062f3a8c63024200c5d7518c604840193ce8318c090803275d063181214be66b90c6302426fcd57118c60484015b300318c0908023ee1d60181210fd2f42ce8b1ca000a5d859d1639400159d053a2c728002b360a7458e501252f428e8b1ca000a5d851d1639412d8bf0eaa2c7282571721d5458e503b52fc22a8b1ca01fe1f845516394001c3ce8aa2c728003875d15458e503bf0fa02a8b1ca077e1d4055163940014bf0ab92c72807e972157258e5000666b90e4b1ca000ad6811c963940015ab02392c72800237a1f4258e500046ec3e84b1ca01fa5e85d0963940014bb0ba12c728003875534258e500070eaa284b1ca01fa5e8510963940014bb0a212c72800297e157158e500fd2e42ae2b1ca000a9f845c5639400153908b8ac728002b3e097158e5000566412e2b1ca000ace821c5639400159b0438ac72807e97a174158e500052ec2e82b1ca000e1d5490563940011bd0e20ac7280023761c4158e500fd2f42882b1ca000a5d851056394001c3aa820ac728002b3a084158e5000566c1082b1ca006ada8010563940015b30020ac72800237a1c2158e500046ec3842b1ca003c3e74551629400187ae8aa2c52801a3b21d4258a5000716aa284b14a000c3f745516194007878e8aa2c3280022fe11735865001c5e422e6b0ca0008ef825cd61940031d904b9ac3280038d55241586500347a43a82b0ca0028dc83dd9219400117f08bb2432800e2f21176486500046fc1aec90ca0028dc835d921940011bb0db9a432800237a1d63486500046e43ac690ca0068f487585219400187ee8aa6c4a80029b61742d895000716aa685b12a000ace83d0b62540e78b8edb9aa4a800f0f9d154d85500061eba2a9b0aa000a7585d0761540014eb0a20ec2a80038d55041d855000578c0083b0aa0008f78758461540051bd073b242a80023760e76485500343e432ea90aa000ccc73d89215400b5cd03b1242a800237a1b74d95300f4afc3aa9b2a6000a5f86553654c03da3ce8aa6ca98003475d154d95300052ec34a5b2a600099f845c7654c03d33908b8eca9800237e197459530004e7c12e8b2a601d9cc825d1654c0013af02ba2ca980d2752057459530004edc02e8b2a601e95c87551654c001a3ee8aa2ca98213531c954595304a6adb82a8b2a601d9ce87dc9654c001a9ea9b92ca9800353553725953000667b06e4b2a6000dcb60dc9654c00199eec392ca9800353dd4725953049eadbaee0b2a6000dcb72dc1654c001b90e5b82ca9807b479d154d89300068eba2a9b126000acd86d4b624c03d39f0ea16c498002b3e1942d893000786aa285b12601f95e87dd5624c001c98c5baac49
  | 7 => 0x7481551658840b0fd0f29acb1080317dce53596210146f41eeab0442008dd83dd5608840187ee8aa2c11080f0f1d1545822102c7c43a80b044200e3954501608852f99ae431eca9080a37a0f74d95210046ec1ee9b2a42058ed82dd365484031eb03ba6ca9080e1fe1d54d95210061eba2a9b2a4278c6d72553654840b1db05b9eca9080237e0d74595210146e41ae8b2a42008fb805d1654840d1f100ba2ca9080e1f21d54595210061fba2a8b2a4203c3c7455165484fd8b8e6aa2ca9080a37a1f73595210062faa6e6b2a4200c5d54dcd65484011bb01b9aca9080237a1c73595210046f43e60b2a42028dc87cc165484011bb0f32ec690802a7a1265d8d210054ec24cbb1a42008df8759763484011bb0f326c69080297a1664d8d210052ec2cc9b1a42008df8759363484014bd0a326c6908029761464d8d213fe2f3b6a9b1a427ec5e765536348401c3ec8aa6c6908038719154d8d2136d67436a5b1a4200e4f65d4b63484db78d03a96c6909b6b321942d8d2137e673b285b1a4200e8c6450b6348401e1aa8a16c6909b6f120542d8d2137567416ebb1a426dacd82dd7634840153d093aec690802a761275d8d210062eba8ebb1a4200a5e859d363484014bb0b3a6c69080297a1474d8d210052ec28e9b1a426eace821d363484db59b043a6c690a6e9761654d8d210070faa4a9b1a42008df8755363484011b90eaa6c69080317e1d54d8d210062e43aa9b1a4200e1f845536348401c3ee8aa6c690803871d154d8d214d70fa12a9b1a429ae1d425536348533c3c82aa6c690a678710554d8d214c52f428a9b1a4200a9e84d47634840153b09a8ec69080297a1741d8d210052ec2e83b1a4200c5f545c363484018baa8b86c69080297a1470d8d210052ec28e1b1a4200a9e841c3634840153b08386c6909bab3a0870d8d2136d66c10e1b1a426dad6811c363484dd5ab02386c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c6909bab3a0850d8d2100566c10a1b1a426dad68114363484015ab02286c69080297a1740d8d210052ec2e81b1a4200e1d54d0363484011bd0f206c6908023761e40d8d210070eaa281b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a426eace82103634840159b04206c6909b6b5a0440d8d210056ac0881b1a42008df835d760484051b906baec09080237e0d74d81210146e41ae9b02427fc5c73d53604840187ee8aa6c09080f0f1d154d81213f62e39aa9b024200ad980dcf60484015b30039ec09080f2b1d142d812100716aa285b02427dccc7350b60484051bd0db9ac0909b63721b73581210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210
  | 8 => 0xb392c728802a7a127258e510054ec24e4b1ca205ad6811c963944615ab02392c72880237a1f4258e510046ec3e84b1ca272a5e85d0963944014bb0ba12c728803875534258e510070eaa284b1ca272a5e8510963944014bb0a212c72880317d537058e510062eaa6e0b1ca205ad6819c163944815ab03382c72880297e157058e513952e42ae0b1ca272a5e85d0163944014bb0ba02c728803875534058e510046f43c80b1ca2008dd879016394401c3aa8a02c72880237a1c4058e510046ec3880b1ca272a5e8510163944014bb0a202c728802b3a084058e5100566c1080b1ca205ad68110163944015ab02202c72880237a1c2058e510046ec3840b1ca272a5e8508163944014bb0a102c728802a7a102058e510054ec2040b1ca205ad68108163944015ab02102c7288030f5d15458a5100536c2e84b14a200e2d54d09629440159d07a12c528802b360f4258a5102c7643a84b14a203cac745096294401c5aa8a12c5288163b21d3258a511453742ce8b14a200a6d859d1629440159d073a2c528802b360e7458a5117d37428e8b14a200a6d851d1629440195ae83a2c5289ea9be115458a5114717c22a8b14a200e2e745516294401c5ae8aa2c52880393e0d5458a510072641aa8b14a200e678155162944f1cc902aa2c5289e38b9055458a513c71620aa8b14a278e6710551629440b5cd0239ac5288beb96047358a510047743e86b14a2008ed87d0d62944514dd0ba1ac5288029b6174358a5100716aa686b14a200e2d5450d62944514dd0a21ac5288029b6144358a510056741ce0b14a200acd839c1629440b5cd03382c5288029be157058a5117d37428e0b14a200a6d851c1629440155d08382c528802ab6107058a5100567418e0b14a200acd831c1629440b5cd02382c5288beb96047058a511453742e80b14a200a6d85d016294401c5aa9a02c528802b3a0e4058a5100566c1c80b14a205ae68190162944015cb03202c5288038b5514058a510047743880b14a2008ed8710162944514dd0a202c5288029b6144058a510056741880b14a200acd83101629440b5cd02202c528802b96044058a514e727aa660b14a200e4d54cc162944b5d8e21982c528816b9a063058a5100572c0c60b14a205ae6810c162944015cb02182c52880a37a0f74582510046ec1ee8b04a200c3d7455160944fd8bce6aa2c1288d2b660273582512d56dc02e6b04a2028de83dc960944011bb07b92c1288163e21d40582510071caa280b04a200c3f745536254407878e8aa6c4a880237e0d74d81510146e41ae9b02a200c3f745536054407878e8aa6c0a880237e0d72d81510146e41ae5b02a2008fb8758060544011bf06ba2cb1080a3720d745962102c7a40ae8b2c420587c87551658840187ee8aa2cb1080f0f1d154596210052e41aa8b2c4205a
  | 9 => 0x2000000010000c00181200800c040130000840080301a04c140000140080280000400c0100504c00c0800300003c000000020000000a01c0c00782e05c0000a001000000070060360240000503a0540102f010058020000160180000600a0000180202804c0280d00200c1501700e000018023761e64d8d5252d2ec2cc9b1aa4008df8759363548e74b90caa6c6a91fb179d954d8d520070fb22a9b1aa400e1c6455363548e769904aa6c6a90ca97a1674d8d5252d2ec2ce9b1aa474a5e851d363548e74bb0a3a6c6a91ceb3a0874d8d523a566c10e9b1aa495c5f87553635492d8b90eaa6c6a91d297e1154d8d523a70fc22a9b1aa400e1f745536354801c38e8aa6c6a929387d0954d8d525270ea12a9b1aa474a5e85dc763548e74bb0bb8ec6a9002a7a1371d8d520054ec26e3b1aa473ace82dc763548e959b05b8ec6a91ceb3a0a71d8d5251d66c14e3b1aa400cd7719c763548e94bd0ba0ec6a90029761741d8d520070eaa483b1aa4008de8710763548011bb0e20ec6a91d297a1441d8d520052ec2883b1aa400e1d5410763548e759d0420ec6a9002b360841d8d520056d40083b1aa400ad98010763548018bea8b86c6a90031755170d8d523a52f428e1b1aa473a5d851c3635480153d08386c6a9002a761070d8d5239d67410e1b1aa474acd821c363548015ad02386c6a9002b560470d8d523a52f42e81b1aa400a5d85d036354801c3aa9a06c6a900237a1e40d8d520046ec3c81b1aa400e1d5450363548011bd0e206c6a90023761c40d8d523a52f42881b1aa400a5d8510363548e759d04206c6a9002b360840d8d520056b40881b1aa400ad581103635480787ce8aa6c2a90030f5d154d855200c3ec2ee7b0aa4038be84dcf615480117b09b9ec2a90123b60b73d855251e66b96c730aa4a2c5d7518e615494399ae431cc2a9283395cb61985520046f43ec6b0aa4008de8718d61548011ef0eb08c2a900237e0d74d81520146e41ae9b02a400c3f7455360548fd8b8e6aa6c0a9002b660373d81520056cc00e7b02a4008df835c760548051b906b8ec0a900a37a1b735815239c6e436e6b02a4008de87d8d60548011bd0e31ac0a927f17dd463581524f667b90c6b02a4328dd87d8c605480193ce9b18c0a9003275d363181520056cc06c6302a475c5d7518c605480193ce8318c0a9003275d063181524ee66b90c6302a400ad98018c60548019aec7388c0a90033518e71181520066bb1ae2302a400cd4635c460548011f70eb00c0a91ca97a167458e510052ec2ce8b1ca200ace829d1639440159b053a2c7288c297a147458e510052ec28e8b1ca296c5f87551639452b8b90eaa2c7289ea97e115458e513970fc22a8b1ca200e1e745516394401c3ae8aa2c7289e3879055458e513c70e20aa8b1ca272a5e859c963944014bb
  | 10 => 0x1f08001c09061e69049a080420c9a5980a3c22a8200e483c00000004517a1ef8001920138000002238000000000002720e917389790ba6ea1e9a801fa7983f8929840dd08624c9ea8b391d1f71ed1a8a309d899e17129b14a00001e00629628300000a0000ef8170001748af08f14f00000029ba2b28591f18a9258932790001d01c88972ab0000001698761c905aaaa0000002458b70000002849e0a999f196c8b4a2d0000a784d8218bd0ba8dd96925d1bc10f92085180b9db8b5a810238021c70001ac8001b80508000001c029300000000000000000000000025c90e8149e4aa80002951a9a000920d313494c84f8bb000000095008211a80000253907a2d92b1570f607b2159de17d95180008d10a8000f1a43a9c02f8e00c5aaa92f1899882409ae9dd03e03f162910a1528080500724902d2562a78ada3514313815c1c9a3b039a44811837aa681c20123b93d92183e9dea008878b79b40bf1298000c680010e1040db0001fa9c41080001b91609fc9fea329ce04b88d86681b003a6d9af8000108c10c90030968000ae1f824006584e8a708b23800023e0e1000060a3a00000008c8bf9d585c8250000ec800082237a412a20002710f8a0700019a8000000000e080021f0001d1183a6611700000587680022780da5924d1af19b99729e9cf06c1e1aa41150988cf800226a60a128001340000801359850a90028090000580080001c0040b80100000001006004050010060160141381400a00c068000000040180400000c0380601604c0400600006c0000d00a0000180f000004000060400301380000402c000080000240000100006800005000004018120000480b00200a044008000000280101b01a0040000003200c048020020180400500201c0d80600a000090030000080500001000c04047024010020100080000300100e00c0080800000c0003c0020000680201400c000060060000b81e000008030160040d4008030200082080000c01401801060000048010020000381c000004000010320e80100000c0100182a00401002803000010050000040100000001c0540180000e0080400c042004000150020640c0000160300300400c0700200201201802009008000008020000a40800200001c0082a00a0380302104000c010080621400000202800c00802000098018000080100000200005c0180000c000010000020040300100c0080400000201c0000303203800005050000110130080001400000a0580200d00206001002004004000060020000180404c004000010020200000b006020018030040000080a0220000501300002c0100e0180000480f00014001801030004000030040000c01c0000880100300202c000020020300000b03e028078090020b0078030020180180900e0280480200c018020000000041a800
  | 11 => 0x9b1599ba95502e9c1a4f8e80ab0001c3a19058a9102c23914d14d8de8c328f27f97691180021a14700000000000012b827191a4a8709df9051f00000000001d70001b381a0cd00013e97406c8000dc17c9f31441592978b185f28c80005e12c22a05006a82986f2a494004080013691c93115a80018620a8478002041cd8c723f138a922420d807701b9da95ea9001124c165aae21f982a549e816a1bc9ca9941220d688416d00028c1a403280028d80000025e8e38002430c7a740000ed0579408000cb8ea0000daa5080e82581625f8fe18c00000000012e80004a92390c8000001eb8002adaad2862280000e880008328f8af8718810001c61a70d99981950f0000038922a3725982615e2319a387c9391f50c51e886ba6b86614803b8000a405e85c0028d703a8c09e79d2a489308a818fa069e2993900089a0b1fa0731011f78000212a003b09c80013c8000dc93c14b22013d14a8438f42149cc90b06e1da0510aa9e727091f94ea55a9c9d31790728311620889fb2290d799782697007d22f0002321848aca1c1d48880001540f58000cb07ea0f8002aca8387a889000234a340b980008c044000268a198be28a07c0001a025c1a21b1a5b000091a0d1250938001d0800027910049a6209f8ef05689f246a730648fb0000428758461538f12a7181a470b21bba6380197819c27b92e1870d099c8752819ec09a0a21830f9a38a0e8a30e18f717b8902a518d9008de27186728e1f11b303818d109a6a1c52698ca22999a2680000001dc1a6a4e0000e52212820911352021a1a4b000000205a3a9929418000000002500001999ee00000000000017988b9378d40000cd91d971a4a2948490c2a1d27608e04c1e3a4194121da700bb800236202a261ba1bd0188f280022e046a3380027598b99d9ca16aaa980680b20e1d991e916a6694385593702423d81aa0920c0ec1038100c620486d8da08f92d0ae84711b82909495b9a629d19b218a580d59b78b321216796e01e90215f0ee9ec8000000002440002a620606a09d00016389a87e0fd86117c27a83d0002550638b51949b89a900000002a22e8001bf958a24a841580230001fe00021b1b09be9822258000bc05387100000000000017e0002030000000000778002ac00007a0628792a397096e861a7d27a24e9969d68000000000000cca1e05206900001506f85906215a276a640998829531331d1a5298e98a1760eb21a80026b0000818aa00012606786821c80002da160000ea824a2c290800111106a080942a28c8a01a3699f8318001320000048372898308ba0a397893b15c9b100e1ab0fa85d8fb968a6c16c27894483a0cf0c3a229bf0000002a19618789468f526f0001271500ffa428ff2518000c81aa1ae0421959989c3101a889f9054865000018078163166a8e8e28848fd0
  | 12 => 0x29a1ce9158d205987020f23d1cc1d21f58001720bd80015f966152a101c28000000001fd0e31f391380023c95601400f06b00000029a80a94524f21816510c0571bb164800282a9688a0602478fa0000d624994f97f89901d9c81810a295b2a1009a252780088d923e8f79f200004a13b8c2116127a0b97b04589825b8c029da77224209a520331d38f802096f1cb09610f0fc0e6a57a130000749e58f20a58e621b9c78228002959f683200000016b1b61890be9961759ac29f86e9568a69e2048a2184f1d81751b6a7e0400000e212a0190ed9b01fc0fea170742568001ff02f27f28701f29702e13a8002750000001e600029911b27b0641f4208a6f844a5e10d80027c01d15d80020d95480026700000019f17e85f8542602108001b51db04c8001e01c68561fb8859c4a728002168a88001e51a329e27384b0db8ad0000000002482981462628001ad03593e00f80008a9cb8e599ea2b8d28e78958eb8011031ff9a785b80919081693023116f8b292128b8f39188b60ce9b99338e70c49772988b6aa30739911b4aa08caa8a8c425da648001f88000000000002850b910a0008001499671280000000000001420bc80013a00000018c9be2918001cf91a0158b89148132532079611e912900022f80002a8000002460d491c0df9289f996014912688e8630a4990000000119000177a2712d800292a6903d8c1879a222300c99ea114157a7e85300000002b08391780005b02b8001a12879731f283910d0001aa93f9ada570a08a9985a5f1d78482611c597d07d80012a9428d1a8906d0cc2748688aba8d1199241d40000f0a2085d27da7c80000c2331e324b8b41e104314e25425a028a2303507b9521131888d8a450282630348ee0b111a9a487f8a018b26c8000000550b00e41328a6000131aa905a1eb0418f917f1478000b09129ef0d014c2178b800004100003c80023f8000078000a51dd9a280008680009c052a6d0fca589ee8001ed80000000005800016d80d1180001fd8000d114b8001122a880007f2039f60000ac0d51a50f692ca0a000000199186a678001bda779c11508001f491e1b284e1088001d610289e00009b9070002a5a658001cd26aa510ce000105945a5a8f49b580c9df01787204d0850df21118e09e93f2869231642652938a101229401c99d16b9682051d5080951034136036a3995d24da2c8301e997a9248001ab800214172833a88155a1392f89099329f18782c8001dc9e41801d90220e9a358128f31399201b228b08710901998f1c22619b7069a288d39488002ab8a189da6e00003600
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x31a70034002b0233991d80070001002880000000000000098007801a259ba3002f04b2a7800000058f2c00050c2da3830016999a9f0001802baeae29a2251380868b0d800000000040024000010200414000800040804080804240400040018000000040c0004000800e960d921d154d8d520063160b719c7635480181e8755041d8d5200683551821076354801a195460041d8d520058364a74551639440181d875534258e510068355183d09629440160d939d15458a510060b61d54d0d62944078388755140582214ce832195450b6348551c0e7655142d8d214cec12055450b634853360d921d154d8d21537031cd5450b6048401859756006318121006265d18018c604840160d929d15458e50006315c9811c9639400181d875534258e500060761d541056394001a0d546084158e5000686551801056394001a315460041d855000433e5d86d4b624c03d90f8755142d893000683e195450b624c00144e9718b75589300059164462dd5624c00181f76610755893000683610621d5624c0016459118875589300061321462dd1624c0014c59118b745893000433a60625d1624c00184c85189745893000531644625d1624c0018c48118974589300061318887551624c03f11c985d154589300070318974551624c103514915d1545893000546e4174551624c00184e861d762589300054365075d89624c001519941d7705893000513249541d9524c00141d94148765493000516640521d9524c0014c9901487654930004876508558b614c00184c7221562d853000513a577218a614c0018c77260462985300042766074195614c00188d841c865585300063120472591614c03d41c9759154585300060721d64551614c001c0c72591545853040d8524564551614c00121d942156258530006131c885589614c0019c3805c9611853000507650855da514c0010cf985db6288530004b1a6362586214c00148d94148764853000703551421d9214c0014c491508764853000631609811d9214c0010cd9808476485300061321476589214c0014c69798a61485300ee3121d62585214c0016449558961485300058364a74551638800181d875504158e2000683551821056388001a19546004158e200055225d52541304800782c875514258b10537031cd5450962c400160d929d15458e1053d8664274551638400121d942157258e1000513255721c963840018c5726047258e100060761d54d09638400141d9421573d95100050b25d54509624400782c875514258910537031cd545096244001d2154501729451000664613731c1214400182d7460b4359410006075d183d09650400182d7560b7359010006075d583dc9640400160d929d15458c100060761d54d096304001a0d5460f42588100058364e74551620400182d875534358810
  | 1 => 0x17800f8e143080001200001e88a9128002af95038000001c8a80171800081b2696100020000000001f8000000000000ca1001880000021933200118d20aa86001d22b300280000091c000a00311590802600000000110baa0e841e302ca4a414ad
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc2400121402003d30cd38701000145454b1001822800070044018001902c2322310eab126000c112159118b74589300060890ac88c4ba2c498002845a118887551624c001207548c4ba2a8b126000b01684625d1545893000680922312e8aa2c49800300e8665075d89624c001806ca0e442ac5b0a600090369295dc8629853000508d4bb9302314c2980030149121d64551614c001a02488e4b22a8b0a600080729d94215625853000601b283910ab12c2980020c5a8245421d9214c001a02aa122a10ec90a6000a03690851d962485300060890e4aac4b0a4298002605a425562585214c001206d212ab90e4b1c2000a11295726047258e10
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa28046000004004805b4a97726046298530005005b2244875915458530006005a8550915087648530004204b869095589614853000600487690955896148530004805b4295726047258e10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x1
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124d
  | 16 => 0x124b
  | 17 => 0x124c
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138d
  | 22 => 0x138e
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128c
  | 27 => 0x128d
  | 28 => 0x128e
  | 29 => 0x9cb
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0xa4b
  | 33 => 0xa4c
  | 34 => 0xa4d
  | 35 => 0x134b
  | 36 => 0x134c
  | 37 => 0x134d
  | 38 => 0xb0c
  | 39 => 0xb0d
  | 40 => 0xb0e
  | 41 => 0x140c
  | 42 => 0x140d
  | 43 => 0x140e
  | 44 => 0xbcb
  | 45 => 0xbcc
  | 46 => 0xbcd
  | 47 => 0x14cb
  | 48 => 0x14cc
  | 49 => 0x14cd
  | 50 => 0xd4c
  | 51 => 0xd4d
  | 52 => 0x9ca
  | 53 => 0x9c955
  | 54 => 0xb0954
  | 55 => 0xb0955
  | 56 => 0xb0956
  | 57 => 0x94b15
  | 58 => 0x140954
  | 59 => 0x140955
  | 60 => 0x95415
  | 61 => 0xbc954
  | 62 => 0xbc955
  | 63 => 0x94bd5
  | 64 => 0x14c954
  | 65 => 0x14c955
  | 66 => 0x954d5
  | 67 => 0x9d395
  | 68 => 0xb1394
  | 69 => 0xb1395
  | 70 => 0xb1396
  | 71 => 0x138b15
  | 72 => 0xbd394
  | 73 => 0xbd395
  | 74 => 0x138bd5
  | 75 => 0x9c995
  | 76 => 0xb0994
  | 77 => 0xb0995
  | 78 => 0x98b15
  | 79 => 0xd4994
  | 80 => 0xd4995
  | 81 => 0x98d55
  | 82 => 0x198b
  | 83 => 0xa49d5
  | 84 => 0x9ca55
  | 85 => 0x198c
  | 86 => 0x168b
  | 87 => 0xb09d5
  | 88 => 0xb09d6
  | 89 => 0x9cb15
  | 90 => 0x168a
  | 91 => 0x1409d5
  | 92 => 0x9d415
  | 93 => 0x19cc
  | 94 => 0xbc9d5
  | 95 => 0x9cbd5
  | 96 => 0x14c9d5
  | 97 => 0x9d4d5
  | 98 => 0xd49d5
  | 99 => 0x9cd55
  | 100 => 0x150c
  | 101 => 0x14c
  | 102 => 0xbca54
  | 103 => 0xbca55
  | 104 => 0xa4bd5
  | 105 => 0xd4a54
  | 106 => 0xd4a55
  | 107 => 0xa4d55
  | 108 => 0x150e
  | 109 => 0x15ca
  | 110 => 0x144b
  | 111 => 0x24b
  | 112 => 0x19cb
  | 113 => 0x154e
  | 114 => 0xb4e
  | 115 => 0x1a4b
  | 116 => 0x15ce
  | 117 => 0x5cb
  | 118 => 0x1a89
  | 119 => 0x1049
  | 120 => 0x104a
  | 121 => 0x59d5
  | 122 => 0x1a8a
  | 123 => 0x168d
  | 124 => 0x168e
  | 125 => 0xd0c
  | 126 => 0x104c
  | 127 => 0x1a8c
  | 128 => 0x125394
  | 129 => 0x1049d2
  | 130 => 0x124a14
  | 131 => 0x8c
  | 132 => 0x1049d3
  | 133 => 0xb1514
  | 134 => 0x141394
  | 135 => 0x5394
  | 136 => 0x1a89d3
  | 137 => 0x139254
  | 138 => 0x105394
  | 139 => 0x1a9394
  | 140 => 0x124954
  | 141 => 0x104954
  | 142 => 0x1a8954
  | 143 => 0x1689d3
  | 144 => 0x151294
  | 145 => 0x105514
  | 146 => 0x1a9514
  | 147 => 0x199354
  | 148 => 0x105994
  | 149 => 0x5cd
  | 150 => 0x1a4d
  | 151 => 0x3ca
  | 152 => 0x145a93
  | 153 => 0x1055d2
  | 154 => 0x105453
  | 155 => 0x145053
  | 156 => 0x168b16
  | 157 => 0x3ce
  | 158 => 0x3d296
  | 159 => 0x5d353
  | 160 => 0x154b16
  | 161 => 0x3cb16
  | 162 => 0x5cbd3
  | 163 => 0x15cb16
  | 164 => 0x105a53
  | 165 => 0x1a5053
  | 166 => 0x104d14
  | 167 => 0x10524a1c
  | 168 => 0x104253
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1327
  | 6 => 2541
  | 5 => 1373
  | 4 => 105
  | 3 => 22
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
  | 7 => packedAt gbK7 (53961+((h/442+packedAt gbK7 (49099+(h % 442)*11) 11) % 1752)*12) 12
  | 6 => packedAt gbK6 (132132+((h/847+packedAt gbK6 (121968+(h % 847)*12) 12) % 3050)*13) 13
  | 5 => packedAt gbK5 (86034+((h/457+packedAt gbK5 (81007+(h % 457)*11) 11) % 1648)*12) 12
  | 4 => packedAt gbK4 (7630+((h/35+packedAt gbK4 (7350+(h % 35)*8) 8) % 167)*8) 8
  | 3 => packedAt gbK3 (1817+((h/7+packedAt gbK3 (1782+(h % 7)*5) 5) % 31)*6) 6
  | 2 => packedAt gbK2 (560+((h/2+packedAt gbK2 (552+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0fffc1e0707e0fe03fffffffc52031e064fff
  | 1 => 0xff0e07e007f87f0ffc1e1fe07cad1ce919b273
  | 2 => 0xfff007fff8007ff0001fe1ff8331e0f1e1c39c
  | 3 => 0x7ffffff8000001ffe0003c1ff01fe03e0
  | 4 => 0x7ffffffffffffe0000003fe0001fffc00
  | 5 => 0xfffff800000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1210020100801200442222100001020204a5
  | 1 => 0x6504246022282504980b154168050c69089252
  | 2 => 0xb6a045aca82076a02893519d093160b161c318
  | 3 => 0x40096d737b50400515d990632c1b701be03e0
  | 4 => 0x10810319c4c658c96380000803fa0000d56800
  | 5 => 0xd8c9e001808410818200001043fedadc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36330
namespace PEqualNP.Outside.L_meta_36330
open PEqualNP.Outside.L_meta_36330.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 2 := bs0_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_160 : Interval s2Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 14 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_128 : Interval s3Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_160 : Interval s3Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_224 : Interval s3Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 227 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 bs3_3_224)))
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
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_896 : Interval s3Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_928 : Interval s3Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_992 : Interval s3Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1024 : Interval s3Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1088 : Interval s3Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1120 : Interval s3Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1184 : Interval s3Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1216 : Interval s3Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1280 : Interval s3Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1312 : Interval s3Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 bs3_4_864) (concat bs3_4_896 (concat bs3_4_928 bs3_4_960)))) (concat (concat (concat bs3_4_992 bs3_4_1024) (concat bs3_4_1056 (concat bs3_4_1088 bs3_4_1120))) (concat (concat bs3_4_1152 (concat bs3_4_1184 bs3_4_1216)) (concat bs3_4_1248 (concat bs3_4_1280 bs3_4_1312))))))
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
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_832 : Interval s3Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 890 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat (concat bs3_5_96 bs3_5_128) (concat bs3_5_160 bs3_5_192))) (concat (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)) (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 bs3_5_416)))) (concat (concat (concat bs3_5_448 (concat bs3_5_480 bs3_5_512)) (concat (concat bs3_5_544 bs3_5_576) (concat bs3_5_608 bs3_5_640))) (concat (concat bs3_5_672 (concat bs3_5_704 bs3_5_736)) (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat bs4_4_288 (concat bs4_4_320 bs4_4_352)))) (concat (concat (concat bs4_4_384 (concat bs4_4_416 bs4_4_448)) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544))) (concat (concat bs4_4_576 (concat bs4_4_608 bs4_4_640)) (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 bs4_4_768)))))
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
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 bs4_5_384)))) (concat (concat (concat bs4_5_416 (concat bs4_5_448 bs4_5_480)) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576))) (concat (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)) (concat (concat bs4_5_704 bs4_5_736) (concat bs4_5_768 bs4_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 60 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_160 : Interval s5Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 165 := (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 50 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 6 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 22 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 105 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_1344 : Interval gbAtlas 5 1344 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1373 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)))) (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152))) (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344))))))
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
theorem bgb_6_2528 : Interval gbAtlas 6 2528 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2541 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)))))))
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
theorem bgb_7_1312 : Interval gbAtlas 7 1312 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1327 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)))) (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 34, 42),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 34, 42),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8feeefeeafeeea8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277053608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36330.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.or,[1,2]⟩,⟨.and,[6,7]⟩,⟨.or,[4,5]⟩,⟨.or,[2,4]⟩,⟨.or,[8,9]⟩,⟨.and,[0,11]⟩,⟨.and,[1,10]⟩,⟨.or,[8,13]⟩,⟨.and,[9,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277053608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277053608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36330

open PEqualNP.Outside.L_meta_36330 in
theorem PEqualNP.Outside.L_meta_36330 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277053608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277053608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
