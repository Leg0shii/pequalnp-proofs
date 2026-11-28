import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36777.Model
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


end PEqualNP.Outside.L_meta_36777.Model

namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
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

def SBf (j : Nat) : Nat := [4, 6, 7, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36777

namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
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
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36777
namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40038000600002886d019680008000140480000060bf43bd43ee32ed32f631f531be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa18d434cb2a8698f14c931
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 30)*5) 5
  | 3 => packedAt s1K3 (83+((h/1+packedAt s1K3 (81+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x1fc07ffe01fe07ff03f07f07ff07c07e91e67
  | 3 => 0x1fff80fffe0007fffc007ff83ff8007f1e387
  | 4 => 0xfe00000fffffff80fffff80003fffff83e03f8
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc04102022424008014508b084308530426cab
  | 2 => 0x54aab4c651d48ad2782b45546ad46856a91665
  | 3 => 0xa932656a9491d364bae0866d236d20a731a386
  | 4 => 0x31a3468d19191a46dcb2d408438e72c23c0350
  | 5 => 0xc1c3870e1e1e1c78ef3ce78e720843043fd800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36777
namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xb00112a30074020124c015383d4ad004558c361c0144c480022e38d222c34008321852730a88003ca029f48b0001068401600310048b19300004100dff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x21004d6cac000159611400c938317000d800b0846400013c000038148000000000f8dc015400008c993400b888000061745cbd100000d09000015cf11c51050c9524b4c0006d445940cc3d7c0000ecfc00a800541d8800000000012800400074012004f4c43444a000e800000000000000009c00087800e00d08000150d5851981642ce4680000701001314d2d782800000000000000a44824187d69480c0000020600020c000200140406000a000e0002000a160408000c0006100400093e52d0e7aa921e7d4d439e292873e5410eeca3a15d547429ea9c853e5290aeea2a15d14542af298855d5310b3ca6214f54c42cea98851d5310a7ca4216b948429f2a6653d54ccb3a87995d94732baa8e653f548ca78a9194fd51329e2a2659d434caeea2995d14532bda826578504ca7ca8194f55032b7a92836c525067ca998cf55331b7296636d52cc67ca818cf55031dba1e43b543c876c8590ed10b219f2a4433d54887588510dd946219faa2433c54487588410edd0c21daa18437652087cca410f9d0821db21043b442087c88410e910821f319043e532086bca7a05754f40bb2888175511027ca9984f55330cea1c613e540c27aa8186750c30b7290616d520c2eca2185d544309f2a4413d54882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a29079084209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x30000003904404c13c720500a50418934b4823010086e0021c6550d32c650c504ca956310b21a358c428868d6310821a918943086a66290821a558c42086c56310821e198c42086a56310821e158c42086856310821a919232086a4644c821e150d32086e0604c82199189511030d43548308758e54883265408620
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8404847650d3208740a18c099043415ce5408620
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (826+((h/15+packedAt s2K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s2K4 (2937+((h/33+packedAt s2K4 (2673+(h % 33)*8) 8) % 157)*8) 8
  | 3 => packedAt s2K3 (833+((h/7+packedAt s2K3 (798+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s2K2 (149+((h/1+packedAt s2K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xff81fff01fc0fffe0f81ffe0ffc3e03f678e67
  | 3 => 0xffffffffe000fffff001fffffffc003f87ff87
  | 4 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x530444624488208052925909180529a42c30ab
  | 1 => 0x852cc8a1c919499605b0ab286a4342a9658665
  | 3 => 0xa19114483a2922ab0413452b4a8051282db86
  | 4 => 0x2c51a20912301b4d29640610c7329603d00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06231823ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee00eeaa8800eeaaee00eeaa8800eeaaee00eeaa8800eeaaee00eeaa8800eeaaee00eeaa8800eeaaee00eeaa8800eeaaee00eeaa8800eeaaee00eeaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36777
namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
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
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xe0fff81f81ffffe0f81ffc1ff0f80fffb38ccf
  | 2 => 0xffffffe001ffffff001fffffff000fffc3ff0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126014a690c16315c
  | 1 => 0x4a6450c832930ca05b09650a90d0aa54b284c5
  | 2 => 0x8488a2034524114b04128a552a0144a9415b0a
  | 4 => 0x14d1049260365a729640c219cca58031e80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf38188c608c1ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36777
namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8435e53086faa610f754c21aea98437c53086fca410df94421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ee218617e520c2faa41877cc830ee990617e510c2faa218778c430ee188617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd20421f940843f661087e0c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f480887e50110fd98221f830443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf28463fa508c6f4a118df54231fca846379508c6fea898df95131beaa2637c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef29
  | 2 => 0x2e2a20011f0000006e11218f0f20000000000000000000036000f60b20002b00000400043c8a000172000e68ba000310092310b48ac0021f252000928002f2000000000008c0441ee0fc4cc078180c692c5d800090884a9800000050a82271e20000000020a6b4001d70000000000000000000135234000000110004492410a25c001038004642351f8270002a8da9fd4c47384a842000758001e80006a8861c91c61307d00034e1b8000004065b4aa8003e2588700892f898c980712c676056a093341010da253743e40023d33c1dc000004b40010f0650000007712b000420208000da7cd070000000000022f33e8811502d4586940013432c4791b00010a00000000000000000e612829800000000000000001b2000a721a4ac128f792d000000000000005940000025e6644782f20e000001c71e04a84b000000000e00000006e50e13d0006f8000d2014014000590005cc00002000000580004a0565131a349a260e90e53a07d45e8c83f494433a4e19a8b40000000090c000002126acfb8000000cc0016a0008b8960001ce834e10000009192ea100002180000000011507940288445239910007f0ba0ab0d8000be96040c3f40001e0005c4908000000006e0062d0000ca0001482a47b8381c42b8ab25e1d2000001363666383e99b4be0000021800095098a530000000000025025c000820ba001290000004e0d4800000000001d93d20000000009c844001cb000550071eb390000000000100000011300091400000000000000c00004e40000042e000000c90008e0000000ea000de000000000001c54b846cc19672487d067000000000001473ce000001dc0000006f1e42fc51400000100280000003be000002190000011a137000134001fe4665981a1524925ac0000000001c00237294000000001ac0000007b0000000000000053c000000000000005702e0f8ae93c00031c0000000096c00000274000000000004fc750002ae6d1201194085bc0015b000680d78000000b0fda581a6274b90000000e008000000000c040340300401028020040000c0300800000000000100c0400802000000180100002014060240100400008000000004c03004010180703c000000f00400010000000200809004020040401422008000080401c0100c100000600c0608008018040000008400000090080000813000070000000410050020040203c03000020000d010050040301802000080000300c040080001400004010000002006008020040001c0b00000004040180a00004008000000000002000000100200805000000040d0080000c0000c0502402000090000001c020000a00002024000000300004000010080b0000000007010000040b0240300c090201dbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x10414a5d4480c50000000000016c7102d800000000001bd0006480000030e8492b87f0c402d1c8f82f41c80023c1d0660760c10a6784450cf2760000008e320858000b7000390c98003f04544d00017e000f5189198034dd9772ec3180020c1ec48c618db2967280015e3508a08e0000005b04e25540400000047000001210000420000000020c000d31db10e000e08003bc000c50440006b8ac1ac038278fc98d284384db0003c6535338780000ec000000860000024a3fe7d85a0d50d43f8a30a836e2646b8512445ecc4024318458000000000000018217042c2f04903e93d0a83f498140ea118078000870b313600000000000000001001fe91000000000654e7a3a000000d08310527b4000001da1800011d00074c000003ca7c000214162000b08d11de0d82a00040a13c0011f38c000000d84760009910d124000001d50005900018b0000009300902c00041800000000000000aa00100a3504c1ad002600000000000000074400213308031058eb04056834a5932e1600000000004c0000003237c001e00000000007a08c614000000000002f8000000001c8f51a00400022222e000af83d3621d05e0f3034998488701e81d837a6503a9900a80000087411800000000ce9f217c3f0000a2240504f10fb2fe22c3084b3b41481d1861ba690659693ba441119bf1265e0b80564c2404b70000000045a87c060000000a7050524000000000001594c0b80000013e000001148810c80881a80000068800103000368a18f22047301915c0001cce180041427c46127146000c00a1054820340ca3cc0dc00241360000c080304a000000660006c800000000000000c21a852057800338000420
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x419023e65d0540c714f415031c5350540d614f405031c5390140ab58843102b960d0840cd90d51103344354440cdd09511033542544408f59641103355190440cd54441102b96010440cd547401037151900408fd95401029c6350040cd545401027b6550040b618d401037151500409b98854cc26d62153308f99251cc23d6494730bc58440cc27661152309d584548c2cd6210e308f992528c23d6494a30a7191328c34e524ca30b5185328c29e648c6308f992544c25f63551309ed81544c23e6515130ce153304c31c548c1309b988540c26d62150309d984540c275611503097594430c2cd6210c30a7191320c2d4614c830b6d81320c29e648c430b6582310c2796510030e610c400c2f1611003097d95300c29c644c0309ed95300c2b8644c0309798f54c825d63d53209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20c795153c831d5454f20d6d8153c823e6414f208f59053c833a54cc320ce95030c8359530c3209d984548827561152208f993538823d64d4e209d987538827561d4e20ba580218825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534827b6054d208f990514823d64145209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948209e594300826f65480209ed95200825e63d53109758f54c423e64d4f108f59353c423e6414b108f59052c425e6314b109758c52c423f6454e108f191538423e6494a108f592528425e6394a109758e52842d863502108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110cd58454443396015110c7d53534431c54d4d10d6583534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c52443696014910cd15241442746550510ce15240443b241901109e19540442d86350110ec505404427a65cc110ce153304436852cc110bc9873044338540c110d6d4c3044368520c110da14a20442786548110bc185204423d65950108f990540427661150109e980540423e64d4c108f593530427a60d4c108f990530423d6414c109b988530426d6214c108f993520423d64d48108f990520423d64148109798c520425d63148109e980520433554c40109e596100433954840109dd95100433554440109ed9510043395444010
  | 1 => 0x81581800000101c2800090200413208184802048005e1a000040601000140e004785c14000206c062e050a41203020000621000040e020081c0001020084a06008101c020180c24090615830010709c24069e9825190e796094643d6d0c5050f3a43141438fd954310eb86050c4397d954310ed86050c43cbd0d5210f4e4354843cb50d5210f4d4354843ae18143d0a5f63543429718d50d0aad6210e428f9974350ab86050d429e9805150a7960145429ed815310a786054c42d6d815310b586054c428f5964310b1d5390c42c754c4310aad6210c42c754f4210b4d53908428fd954210b1d53508429bd954210b4d5350842b618143cca3e64947328f59251cca7a60947329e58251cca3f64543328f19150cca7a60d52329e583548ca3e64951329d986544ca7561951329e982544ca7960951329dd85544ca7461551329ed81544ca7860551328f994544cb1d6315132cb588544cb1c5490d3297195434cad86050d32cb152424cb8e43909329b195424cb8d4350932cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb7051141328f596540ca3e64150329798c540ca6e6215032c7553320cb2d548c83297d95320cb1d544c8329bd95320cb2d544c8329ed8153d06786054f41c754c43d06ad6210f41ab588435065e63149419758c525072c5250941ad185425063f65504419dd95411065f63540419718d501075b6354041d618d501073b4154041dc90550107394154041dc505501066e62153319b58854cc6d4614cb319e983548c67960d52319e980548c6796015231ce952508c7395494231ce951508c73954542319bd89544c66c62551319ed81544c67860551318f990524c63d6414931d3149324c66e62150319b588540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863f6454f218f19153c867b6054f219e18153c863e6414f218f59053c867a60152219e580548863e64d4e218f593538867a60d4e219e583538863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544863f6454d218f19153486776154d219ed8153486786054d219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755153087546154c218f990530863d6414c219798c530867a6014c219e580530875553cc4219d594310866f65484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50086ad6210e409798e529025d6394a40ae58
  | 2 => 0x4c844781a20a23c42808229829207625a70598001d12a00000958000800e0026c0125e6f13a21160c78ec0030a6b8002000000000b529ca5ad257998003042d8007c21c001d800000000d01000026014048005a80007222002900009406100000e247000561e4570600006ca78000021800338898009d8009317ca600c002e4b08006494200000000005d328139203f208b99da9f0384d9c83c0be322c61519a000006da32001ca18aae00000198503e0a69a2ba7a2603019e350a2a3a500a9f821aec1710e37330bba341c20e8b32009a3eba156988feb41f274af2962a6b310c1c824641aa079f6a6b2cc5b2e520b2a80347032465b1c588da3d154161101f0e416b32708063e832c1ade62b26852d82e97e7f96417a2849b0e6a2f83489c7703053130279a089036a21fa7188e798cc8127ec4952000e81eb3a9391a002b65e8002c000132c011800001a4002e000000280000f87e33a802b96c85a845d8de6984a6531a5400024a02000ee002be6127a4e14a40a402b1de8ab3600106000e600a5aa32ce0006eae186519d0ac2eac3000568aa8c1f44f8f2bd9ce6c914c40e0bea8a7a93c5e2366b000b12c8929c44608263816848000031882a5c47a66a4800aa1e2002b4002f4000a8b69b000122412006e1086d1ee9aafc9181a3082c190104496e83210001ba15a427b2444d0c61219c5a0001498000188000007f0bca8a2ec02ac1a1cc329169ca2010a52a186a0000026abc990a408800c88f6001d6b733450090952f03aa78c50c40b9be512e20012c001240021ec08d8aca3823078869d4358009d18c222d6a512ec20b80eafe81aaa4a2ca9ba820003c5c0002d23a000000000a5cb2aa9000538000003804040400800002d010040e000102002011b8040e00008407c060201c08000087c0003058180603018000202000380225070040a090b80008041486c2804078503a0001018000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x560d18c2880811004113cb5ce4d55800d40002401c04820880110c14a1c14354843a90e0a1aa421d187054c4310a8c382c62a2658358d6215132b10e0a1a84995187054c43d0706a9ac421e83435cc5250941962e030a84a0d0d74149324c64c39ac1a1081495c84354440a62e1a12a22049873580411030a31aa2a00819418d5150040a1ae929265185897210c400c34821ac220061461cd6015110c62c2b00a888690635054044258ba4c3982212c5d06148110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2080040060a088058d6215132a088054d6210f41910835c34254440a818210d6110030c10735856015110
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (18682+((h/205+packedAt s4K5 (16632+(h % 205)*10) 10) % 984)*11) 11
  | 4 => packedAt s4K4 (16974+((h/138+packedAt s4K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s4K3 (1265+((h/8+packedAt s4K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s4K2 (304+((h/1+packedAt s4K2 (300+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe03ffc07ffff060fff07fe0ffc3ffc031e73fc
  | 1 => 0xffc0fff81ffffff03ff83ff07fc3fffde38c7f
  | 2 => 0xffffffffe07fffffc0003ffffffc3ffe03ff8f
  | 3 => 0xffffff8007ffffffc0007fffc007fc0ff0
  | 5 => 0xffff0000000007ffffffffff80000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2986447145124a02cb424e849c0664310e31bc
  | 1 => 0x42924890c8244250154a12942442a951628455
  | 2 => 0x85089122034884a5408425294aa812a6015a8a
  | 3 => 0x162ca244920e9539a6948108733100c6b40f60
  | 5 => 0x1830c3871c70e7ce38e739ce02222307dbe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee0eee0e8c0e8c0eee0eee0e8c0e8c0eee0eee0e8c0e8c0eee0eee0e8c0e8c0eee0eee0e8c0e8c0eee0eee0e8c0e8c0eee0eee0e8c0e8c0eee0eee0e8c0e8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36777
namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8435e53086faa610f754c21aea98437c53086fca410fb90821f6a1043ef32087d86410df94421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a85205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461df328c3ba65185f94630bea8c61de318c3b863185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ee218617e520c2faa41877cc830ee990617e510c2faa218778c430ee188617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132ef21a65dd434cbdc84997b50932f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0fb94b41b7296837d52d07daa5a0db54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f790e31eea1c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ee42887da8510fbcca21f6194437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef29
  | 2 => 0x7a2041106a9264b20bc259371d0684880000000008500010e4a0149ec15022076837240064710a90f2000001320000001014b000000020000007c0000b31d800000024000000ce9e607a49c388d7102818c11b831e0c05a97f25e79cb92083e8450a50b139a45c281220380006021529057c000004001f46c80014c924ee80044e7dc5f9564c838ce213e2c6738be8f1300018fe98c2029102912411c4f50c1ed014128510a04347e52b1bb000374000162da72c0016b0007e8478ea4260001c146000000cb95b09030cbb9e14c03c82b1310008cc001c20000004886b1468303b0400007acc713616e398d31b34a275c70a5b0188a8b81bd194318e486e1244303f9913a27884489b19686c1f99b3447cc069920c82b07583e27601c2107b0004b800035258940002574120010b80003c000450000009945f0112220880720f0000000019e1260011c8f301031c09a21000568318df3160012a00012a61ceda1f30a6bc3396837c1c0369991340012a9e03263f00003b00a458c08743ac8483309821e8583290e338330ea82647a068d28bb0d008c9fa614388b44c85d1c0334a02662b2740c196429a2303002e46c0b0ac2423641f06814c164810691d4000000d00004488504196f2ca000bf0280006e4d819a116000ed107206060bc0000000009e03a1e881c1911d0be7f0401881040012e84e2564e1009574802747c07e37e7fc001e40d25784f9ee00274d029c30f4538229062167ecd88001a80011a16a000690620000005b0e50000004a8ff0170004c0000b926835800000406400aea1d0f01246401b0000000115c4b4000678000003b81986a1420002a800000000000c20980000000048a000de00049e8c4000dc312000d40001f4000e40002ce000001b64766dc5b169006000c223a4140000011a00010cef0412383f80f8c54bc50d0f00038c6e86da2f27411d2f998486524309a348c0005ea4e29e00113115000880002230e427914267192580ca0b401e084c515548e935011d9054840000010000000802030020000304c00000000100d03409000010840800c01000000240c01c0100c0602401038000000100400000100001d0040b00018000020140100c040900200000040040042c00000000010000b00402028010000c0080309405000010300400c0002c0001809004020642e03c0c0180300406004040140605c020000204800030070040b0140200007000000c4080100001004004020000105003004000341504007000140000100c01000030240300c1705c0100014000140501002405000000081e0340b04c0100c0c030010000400c0800000000000080301c000180003c130000003001014030080101c000300002407004000080700c00bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x78c890de0008dc0001d2a02b8000002f6000b98000000000000047c000999524942103992d000550e0800000000000001b000000166028000c3151012484001a9356000f48f702a34c000aa33e00000000000000000000240400000000048c821194520000023538e000d68004c68441b0251ea6d1310b00ee7d42b91f2c216915a530b0420428ce05a46c001c023c00000000000948000000007301a23039e02d160542c416c9c800000000001aa000635190000720000017c496000a21290001451c10d3f07a81884f000290000002ea344a280021200000000416000ca96e0b200000000000888a98af41c0000006f000000d60c13203a4e904d000970bc8ef0003eca089c0bc0000000000069c4a23f1703fc0005c0002acee1423ca658469f245c4d4298bc3d0460d711312c0005d06214a51c000003be000739b51ec1b00000008c000bb0e40000000022549825c53a480000f0158861b40003a9d847871400258482001068f03de414001f12e2394480fd24a7d8568f904e864ba1
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe43102ad6210c40d394e521034d5394840d394d521034d5354840c754f42102b960d0840c754d421032e5250840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cdd0951103354254440cd54641102b960104408fd95401029c63500409ed9540102d863500409b98854cc26d6215330b618143cc2d96310330e690c40cc26e62152309b588548c27661152309d584548c2cd6210e308f992528c23d6494a30d3949328c2d4614ca308f992544c25f63551309ed81544c26e62151309b588544c23e6515130c758c544c32e6215130cb588544c25e6590d30c7152434c25c6550d30c7151434c2d86050d30ce153304c31c548c1309798c540c26e62150309b588540c27661150309d584540c25d65d0c3097594430c2cd6210c30b5185320c26f62544309b189510c355510c430b6580310c2796510030e610c400c25f654c030a7191300c27b654c030ae191300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20c795153c831d5454f208f99053c823d6414f20d354e42c832e5450b20d354d42c825e63152209758c548827661152209d584548827661d4e209d58753882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d209b195424825e63150209758c540826e62150209d984540827561150208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d639482097d8d510825c6354420d9544210826f65480209ed95200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6414b108f59052c425e6314b109758c52c425e63152109758c548426e62152109b588548426e62d4e109b58b538425e63d4a109758f528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524433454905109d195414436852881109e195204425e63150109758c540426e62150109b588540427661150108f990530423d6414c109b988530426d6214c108f990520423d64148109798c520425d63148109e980520427965840109dd95100427b6544010
  | 1 => 0x18d8020018804220100804740c190143e030000030000982402010205c12120084c10210182c34000100c000c0400800030180c0005020002e0f0481422010182c0001000101a090083012080000438019bd895190e6c6254643d6d0c5050f3a43141438fd954310eb86050c4397d954310ed86050c43cbd0d5210f4e4354843cb50d5210f4d4354843ae18143d0a5f63543429718d50d0a5f63546429718d5190ab86050d42c754f4210b4d53908428fd954210b1d53508429bd954210b4d5350842b618143cca3f64543328f19150cca7a60d52329e583548ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5c6550d32b6181434ca6c6550932e350d424cb564314532d550c514cb664214532d9508514cb673214532d58c8514ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320cad4614c8329bd95320cb2d544c832b9185320cb4e5394b41d354e52d074e5354b41d354d52d071d53d0b41c754d42d072e5250b419798c525065d63149418fd954110677655044197d8d501065c63540419b98854cc66d6215331b518532cc67a60d52319e583548c66e62952319b58a548c71e5450e31b6181438c69d640ca319758e544c66e62951319b58a544c66f62551319b189544c67b60551319e181544c63e64149318f590524c72e6414931cb590524c65e65cc931d314b324c74c524c931b5185324c76452cc531d314a314c66e62150319b588540c67a60150319e580540c65d6590c31b6181430c65d658c831a7590320c65f654c431b3189310c677654c431b9189310c63f64540318f191500c65e63153219758c54c863e6414f218f59053c865e63952219758e54886ad640ca218fd91508863c645422197d8d508865c63542219798e544865d63951219b58a544865f63551219718d544867b60551219e181544865e6394d219bd8953486776154d2197994534875453c8521d314e214865e63d50219758f540867a60d50219e583540863d6595021cb98a540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c21d5185530863e6414c218f590530865e6314c219e98053086796014c219b596420874d5390821b9586420872e5450821d354d420874d53cc8219b59432086ad640c821d554f31087c732cc4219d59431087c4320c4219bd9521086cc63484219dd9521086d46348421ce95250087395494021d694e50087595394021ce95150087395454021d694d50087595354021da90950087694254021ab588439025e6394a409758e529025f63546409718d519026f62546409b189519035853d0140c714e40503586054c40c754
  | 2 => 0x6a1700eaee0010800000268bc26000000007c2f00028a27800310da86000002de00000001fcc709200000a79bc8daa8000000001625800510c093ad42b0127b15622a907d88232000060e8121d20891e790024e8a89282e000200000095000930001114270a5abf8349aa10859b013a7a0913e450c63780e7d1da001eeb7026a52588492e820008d0a43d8fc28b3a3c8b8a584c8a2f4119be5f226ae81e4c1dc9d0b21d1283408897166af0dc1b30a358e29f86a9c054a694e5f8ec81af24011aa12006d800572760021c458008f000000725aada000007c800000ccc10aace1e0acacc442ca7e868b0a980007c7e148a728200158ca9820018888280b10000010400058c4214bf288af980921640001a75800ae21e000008128e51afa9b224243247a000ad292001d4cb00072800c099cc4a463b8f449000022d63e1d80b2d8912e4cb8001680066aea58a8c4c84054a7c2383e36256a8b36c813879a38838328b1fe1c0ce1f9505519e0023a001766b8c24d10aa98007a90e628b0ba2d2b98005d1c07412600000b40fa61118408fe6e17218830178be500ea14a5e8c12071240ac00c299921b9c6cc264c62c6652c023084a8196cd316b21780117a329864ab1a251a68ca686caac430d43c086142788b960830e4128b6908605b2e0019aa7323e2014a63056c781c5a2226d198949a21e94cc0308ad8107398e8287600000a933200000172f62d202002ce39878c180a000a0003268a8ba6800094000c3a6ebb1ac00042052f8642aec88000015e271064b000000e000314b8a60ca03600000c313c34a6244a8600000190009c8ae000000003c471220a96e692aa5693619a66001c8779e20e028001ba868000200800080502018040d0300440000400408350000036001d8001c07130041e1e00078004315004000200830020a2900002000280c022a090480e120b008100301028000f008000e1
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x5c030004000001429101819624000001300e0074802c040d0005420053c40c0200008820800014a1c14354843a90e0a1aa421d887050d424caa83828628a65c150d4214532c2aa830a641962554185320ca86b94a8a1c63869506050e31a1ae82926498d0d741895308722310c2a9843311cd6190821b0ae81906210c9873583421024c39ac020881435d2524ca30c8ca430a651860d63588544c286b90a8a1a61861506050d30a88e4a88621849874580310c2c4b908620061511cd5108420
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x62000840b008050d4214532a09829506050e31a05841886154c21a0584948614ca30a09821506050d30
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
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 814)*11) 11
  | 4 => packedAt s5K4 (16974+((h/138+packedAt s5K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffffc07fff841ff87f87ffff0ffc0233f3fc
  | 1 => 0xf81f87ff83ffffe0ff87f8701ff0fffdcccc7f
  | 2 => 0xffe007fffc1fffff0007ff801fff1ffe0f0f8f
  | 3 => 0x7ffffe007fffff800001fffe007f00ff0
  | 4 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x30c300470841080318098091c70124301151bc
  | 1 => 0x52440889190a00a06882882249104950c4c455
  | 2 => 0xa109551220d4454d0445550492aa12a60b0a8a
  | 3 => 0xc596662452875676b55044091ccc80c7700f60
  | 4 => 0x618443863186798c666664e00880307aea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0eeeae8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36777
namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c180017fd50057f54017f95005fd54015f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52017fd0803fe42017f50803fc42007fcc803fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842000fdc4210027f6210802fff65440177fb2a2000dfd9510004feca8802ffe65440077f32a200bff5951005dfaca8802ffc65440077e32a200bdf1951001cf8ca8802bff64440157fb222000efd91100057ec88802bfe64440057f322200aff59110055fac88802bfc64440057e322200aef1911001578c88802bff5444015bfaa2200aff95110057faa88802b7d5444015fe2a22000ffd8d10005fec688003df63440016fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688003dc63440016e31a200bffd4d1005ffca68802ffd5344017fe29a200affd0d10057fc868802bfd4344015fe21a2000ffd8910005fec488003ef624400177b122009ff9891000dfcc488003fd62440017eb122009ff1891000df8c488003ec624400376312200bffd491004ffca48802ffd5244013fe292200affd091004ffc848802bfd4244013fe2122000ffcc91004ffc6488003fd3244013fe192200bffd4510027fca28802ff65144017fea8a200bfd54510027f8a28802bff4144009ff20a200afd90510057fa828802bf54144009fe20a2000ffcc510027fc6288003fd3144009fe18a2009ffc8510027fc4288003fd2144009fe10a200bffd411005ffca08802ffd5044017fe282200affd0110057fc808802bfd4044015fe2022000ffcc110007fc6088003fd3044001fe1822009ffc8110007fc4088003fa2044001fe9022000fe4811004ff84088013ff1044009fd8822000ff84110007ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013fd640400d7eb202004ff19010025f8c80801bff540400dbfaa02006ff95010037faa80801b7d540400dfe2a02004ffd8c10025fec608013fe63040017f3182004ff58c10005fac608013fc63040097e3182007ffd4c1003ffca60801ffd530400ffe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902006ffd081002ffc840801bfd420400bfe2102000ffcc81002ffc6408003fd320400bfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff08410045fcc00801fff500400fff2802007ff5401003ff8a00801bff400400dff2002006ff50010037f88008003ff3004001ff1802000ff4c010007f86008017ff2004001ff1002000ff4801002ff84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0xbfc5148023ffa0a4011ff9052008ffa8290047fc4148001ff98a4000ff8c520007fa6290003fc3148003ff90a4001ff8852000ffa4290007fc21480037fb024012ffd4120097fca09004bfd5048025fe2824011ffd012008ffc8090047fd4048023fe2024000ffcc120007fc6090003fd3048001fe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2010bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb26200fbf59310027f8c988012fc64c401fffaa6200fdfd531007ffca98803ffd54c401fbeaa6200fff15310027fec788012ff63c4009ff31e2000bf98f10027fac788002fd63c4009fe31e2004bf18f10087fea788043fe53c4021fea9e2010ff14f1007ffe878803ffe43c401ffea1e200fff10f10027fec588012ff62c4009ff3162001bf98b10027fac588002fd62c4009fe3162004bf18b10087fea58803bfe52c4021fea96200eff14b1007ffe858803bfe42c401ffea16200eff10b10007fe658803bfe32c4001fe996200eff0cb10027fea388013fe51c4009fb28e2004ff54710087eaa388013fc51c4009ffa0e2004ff90710027ec8388013fd41c401ffaa0e2004ff10710027fe6388013fe31c4009fe98e2004ff0c710027fe4388013fe21c4009fe90e2004ff08710087fea188043fe50c4021fea862010ff1431007ffe818803ffe40c401ffea06200fff10310007fe6188003fe30c4001fe9862000ff0c310077fe4188003fe20c4001fe906200eff0831006ffecb08036ff658401bff32c2003bf9961006ffacb08036fd658401bfe32c2003bf19610047fec908022ff6484011ff3242002bf99210047fac908022fd6484011fe3242002bf19210047fea9080237f5484011ff2a42008ff55210046faa908023fc5484001ffb1c2000bfd8e10007fcc708002fe6384001feb1c2000bf58e10007f8c708002fc638401bffa9c200dff94e1006ffaa708037fc5384011ffa1c2008ff90e10047fa8708023fc4384001ffb142000bfd8a10067fcc508006fe6284001feb142000bf58a10067f8c508006fc628401bffa94200cff94a1006ffaa508033fc5284011ffa14200cff90a10047fa8508033fc4284001ff994200cff8ca10007fa6508033fc32840157eb0c200dffd4610027fca308037fd5184009fe28c2008ffd0610027fc8308023fd4184009fe20c2000ffcc610027fc6308003fd3184009fe18c200cffc8610027fc4308003fd2184009fe10c2004bf9821006ffea108037fe508401bfea84200dff14210047fe8108023fe4084011fea042008ff10210007fe6108003fe3084001fe9842000ff0c210067fe4108003fe2084001fd1042000ff48210007f24108033fc2084009ff8
  | 2 => 0x300b7fc861805ffd430c02dfe2186016ffd88300affcc418006fe620c001feb106000bf588300b7f8c418006fc620c031ffa906015ff948300c7faa418057fc520c02fffa106015ff908300bffa8418057fc420c02dff9906000f7cc8300affc6418003fd320c001ee9906016ff0c8300b7fec218003fe610c0097f3086000ff58430005fac21805bfc610c031ffa886018ff944300c7faa218063fc510c02fffa086017ff904300bffa821805ffc410c02dff9886000ff8c430007bc6218003fd310c02dfe1886000f70c4300affe4218003fe210c001fe9086015ff084300cdfcc018063ff500c031ff2806018ff540300c7f8a01805fff400c02fff2006017ff500300bff8801805bff300c001ef9806000ff8c030007f46018003fd300c001ee9806000fe4c0300affe4018057fc200c029ffb2c4014bfd96200a7fccb1000efe6588029feb2c4014bf596200a7f8cb1000efc6588027ffb244013bfd922009ffcc91000afe6488027feb244013bf5922009ff8c91000afc6488027ffaa44013dfd522009ffca91004ffd5488027beaa44013ff15220007fec710002ff6388001ff31c4000bf98e20007fac710002fd6388001fe31c4000bf18e200a7fea710053fe5388029fea9c4014ff14e2009ffe871004ffe4388027fea1c4013ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510003ff6188001ff30c4004bf98620007fac310002fd6188001fe30c4014ffd46200a7fca310053fd5188029fe28c4013ffd062009ffc831004ffd4188027fe20c4000ffcc620007fc6310003fd3188001fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310006fe6088029ffa844014ff942200a7faa110053fc5088027ffa044013ff9022009ffa811004ffc4088001ff9844000ff8c220007fa6110003fc3088003ff9044001fbc822000ff64110007fc2088003fc1044012ffd9520095feca9004bfe65480077f32a4012ff59520095faca9004bfc65480077e32a4011ffd912008dfec890047fe64480057f3224011ff5912008dfac890047fc64480057e3224011ffd512008efea890047fe5448023feaa24011df5512008ff8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c69004bff5348025ff29a4012ff54d20097f8a690047ff4348023ff21a4011ff50d2008ff88690006ff6248003ffa924001ff9492000ffaa490007fc5248003ffa124001ff9092000fdc8490007fd4248023f6a124001ff1092000ffe6490007fe3248003fe9924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290012fc6148025ffa8a4012ff94520097faa29004
  | 3 => 0xf2866021ff5433010ff8a19806bff40cc035ff206601aff503300d7f88198083ff20cc041fe106601fffd96300fdfecb1807ffe658c0077f32c601fff596300fdfacb1807ffc658c0077e32c6019ffd92300cdfec918067fe648c0057f3246019ff592300cdfac918067fc648c0057e3246019ffd52300cefea918067fe548c033feaa46019df552300cff8a918072fd638c03fffa9c601fff94e300fffaa71807ffc538c033ffa1c6019ff90e300cffa8718067fc438c001ffb14601eff98a3000dfcc518003fd628c0017eb14601eff18a3000df8c51807fff528c03dff294601fff54a300f7f8a518067ff428c03dff2146019ff50a300f7f88518003ff328c001ef994601eff8ca30007fa6518003dd328c03dfe1946000ffd8630007fcc318012fe618c001feb0c6000bf58630007f8c31807fff518c03fff28c601fff546300fff8a318067ff418c033ff20c6019ff506300cff88318003ff318c001ff18c6000f78c630007fa6318003fc318c001ee18c601effc8630007fc4318003fd218c03dfe10c6017bf982300fffea11807ffe508c03ffea84601fff142300cffe8118067fe408c033fea046019ff10230007fe6118003df308c001fd984601effc82300f7f84118077ff654c03b7fb2a6000dfd9530004feca98077fe654c0077f32a601dff595300edfaca98077fc654c0077e32a601ddf1953001cf8ca98073ff644c0397fb226000efd91300057ec898073fe644c0057f322601cff591300e5fac898073fc644c0057e322601cef1913001578c898073ff544c039bfaa2601cff951300e7faa8980737d544c039fe2a2601dffd4d300effca698077fd534c03bfe29a601cffd0d300e7fc8698073de434c039fea1a601cf750d300e7f88698003ff624c0017fb12601bff9893000dfcc498003fd624c037fe3126001bf189300effea49806ffe524c03bfea92601bff149300e7fe849806ffe424c039fea12601bff10930007fe649806ffe324c001fe992601bff0c930007fec298002ff614c001ff30a6000ff58530007f8c298012fc614c03bffa8a601dff945300effaa298077fc514c039ffa0a601cff905300e7fa8298073fc414c001ff98a6000ff8c530007fa6298003fc314c037ff90a6000ff88530007fa429806ffc214c03bffa82601dff941300effaa098077fc504c039ffa02601cff901300e7fa8098073fc404c001ff9826000fecc130007fc6098003de304c037ff902601bff081300b7feca18062ff650c031ff3286003bf994300c7faca18062fd650c02dfe3286003bf194300b7fec81805eff640c02fff3206002bf990300bffac81805efd640c02dfe3206002bf190300bffea81805f7f540c02fff2a06017ff550300befaa81805ffc540c0357f3186018ffd4c300b7fca618063fd530c02dfe2986017ffd0c
  | 4 => 0x813fc63884097e31c4225ffd4e2112ffca710897fd538844bfe29c4224ffd0e21127fc8710893fd4388449fe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe8510807fe4288403f72144201ff50a21127da8510807fc4288403ff9944201ff8ca2100ffa6510807fc32884097f30c4204ffd4621027fca310813fd5188409fe28c4204ffd0621027fc8310813fd4188409fe20c4204ffcc621027fc6310813fd3188409fe18c4204ffc8621027de4310807f72188409fe10c4204fd08621027fec110813fe60884017f3044204ff58221005fac110813fc608844bffa844225ff9422112ffaa110897fc5088449ffa044224ff90221127fa8110893fc4088403ff9044201ff0822100fd8411088fff65484477fb2a4223ff9952101dfcca9088ffd65484477eb2a4223ff1952101df8ca9088bff64484457fb224222ff99121015fcc89088bfd64484457eb224222ff19121015f8c89088bff5448445bfaa24222ff95121117faa89088b7d5448445fe2a24200ffd8d21005fec690803fe63484017f31a4200ff58d21005fac690803fc63484017e31a4223ffd4d2111ffca69088ffd5348447fe29a4222ffd0d21117fc869088bfd4348445fe21a4204bfd892100ffea490807fe5248403fea924201ff1492100ffe8490807fe4248403fea124201ff1092100ffe6490807fe3248403fe9924201ff0c92100dfec29088fff5148409ff28a4223ff54521027f8a29088bff4148409ff20a4222ff50521027f88290803ff3148409ff18a4200ff4c521027f86290807ff2148403fb90a4204ff88521027dc4290813fc2148409f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090802fc6048447ffa824223ff9412111ffaa09088ffc5048445ffa024222ff90121117fa809088bfc4048403ff9024201ff081210b7fecb98086ff65cc043ff32e6003bf9973010ffacb98086fd65cc02dfe32e6003bf197300b7fec99806aff64cc035ff3266002bf993300d7fac99806afd64cc02dfe3266002bf193300d7fea99806b7f54cc035ff2a6601aff553300d6faa99806bfc54cc043ffa9e6016ff94f3010ffaa79805bfc53cc035ffa1e6016ff90f300d7bc879806bfd43cc035eea1e6016ff10f300b7fec598083fe62cc0037f3166000ff58b30005fac59805bfc62cc0037e3166021ffd4b30107fca598087fd52cc041fe296601affd0b30107fc859806bfd42cc041fe2166016ffccb30107fc6598003fd32cc02dfe1966016ffd8730007fcc398012fe61cc001feb0e6000bf587300b7f8c398087ff51cc043ff28e6021ff5473010ff8a39806bff41cc035ff20e601aff507300d7f8839805bff31cc001ff18e6000ff4c7300b7f86398083ff21cc001ff10e6000ff48730107f84398087ff50cc043f
  | 5 => 0x631027fc8318813fd418c409fe20c6204ffcc631027be6318803f7318c409ff90c6204ff08631027fec118813fe608c4017f3046204ff58231005fac118813fc608c45fffa84622fff9423117ffaa1188bffc508c45dffa04622eff90231177fa81188bbfc408c45bff904622dff08231167feca988b2ff654c459ff32a6203bf99531167faca988b2fd654c459fe32a6203bf1953115ffec8988aeff644c457ff3226202bf9913115ffac8988aefd644c457fe3226202bf1913115ffea8988af7f544c457ff2a2622bff5513115efaa8988affc544c459ffa9a622cff94d31167faa6988b3fc534c457ffa1a622bff90d3115ffa86988affc434c401ffb126200bfd8931157fcc498806fe624c401feb12622aff1893100df8c4988b3ff524c455ff292622cff54931157f8a4988afff424c455ff212622bff50931157f88498803ff324c401ef992622aff8c931007fa6498803dd324c455fe192622cffd4531027fca2988b3fd514c409fe28a622bffd0531027fc82988affd414c409fe20a6200ffcc531007ee6298813fe314c409ef18a622affc8531027f84298803ff604c4017fb026200ff98131007fac098803fc604c4017e302622cffd4131167fca0988b3fd504c459fe282622bffd013115ffc80988affd404c457fe202622affc8131157f84098813ff650c4097fb286204ff9943101dfcca18813fd650c4517eb286204ff19431025f8ca18813ff640c4097fb206204ff99031015fcc818813fd640c44f7eb206204ff19031025f8c81889fff540c44fbfaa06227ff9503113ffaa81889f7d540c44ffe2a06229bf98c31147fea61885bfe530c451fea986216ff14c3113ffe861885bfe430c44fef2186227ff50c3113fba861885bfc430c409ffb106204ff9883100dfcc418813fd620c4017eb106204ff18831025f8c4188a3ff520c44dff2906228ff54831137f8a41889fff420c44dff2106227ff50831137f8841885bff320c44dff1906200ff4c8310b7f86418812fe610c409ffa886204ff94431027faa218813fc510c409ffa086204ff90431027fa8218813fc410c409ff9886204f7cc431027fc6218813f6310c409fe9886204f74c431007ea6218813ff210c44dfb9086204ff08431027e84218813ff600c409ff3006200bf98031027fac018802fd600c409fe3006228ffd4031147fca0188a3fd500c451fe2806227ffd003113ffc801889ffd400c44ffe2006226ffc8031137f84018813ff65884097fb2c4204ff9962101dfccb10813fd658844b7eb2c4204ff19621025f8cb10813ff64884097fb244204ff99221015fcc910813fd64884497eb244204ff19221025f8c910893ff5488449bfaa44224ff95221127faa9108937d5488449fe2a44204ffd8e21025fec710813fe63884017f31c4204ff58e21005fac710
  | 6 => 0x5ff3226402bf99132197fac8990cafd644c865fe3226402bf19132197fea8990cb7f544c865ff2a26432ff55132196faa8990cbfc544c8037fb1a6433ffd4d3219ffca6990cfde534c867fea9a6433f754d3219ff8a6990cbff434c865ff21a6432f790d32197fa86990cbdd434c865fe21a6401bfd893200ffea499007fe524c803f72926401ff5493219fdaa499007fc524c803ffa126401ff9093200fdc8499007fd424c865f6a126401ff1093200ffe6499003ef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003f7614c8017bb0a6400ff98532007fac299003fc614c8097e30a6400fd18532005e8c2990cfff514c867ff28a6433ff5453219ff8a2990cbff414c865ff20a6432ff50532197f88299007ff214c803fe10a6400ffd8132005fec099003fe604c801feb026400ff18132005f8c0990cfff504c867ff2826433ff5413219ff8a0990cbff404c865ff2026432ff50132197f88099007ff204c803fe1026416ffd973118dfecb988c7fe65cc4077f32e6231ff5973118dfacb9885bfc65cc4077e32e6216ffd933114dfec9988a7fe64cc4057f3266229ff5933114dfac99885bfc64cc4057e3266229ffd533114efea9988a7fe54cc453feaa66229df5533114ff8a9988c7ff53cc42dff29e6231ff54f310b7f8a7988a7ff43cc42dff21e6229ff50f310b7f8879885bff62cc461ff3166201bf98b31007fac598802fd62cc42dfe3166201bf18b3118ffea5988c3fe52cc463fea966230ff14b3114ffe85988c3fe42cc453fea166230ff10b310b7fe6598803df32cc461ff1966200ff4cb31007ba659885bfc32cc463ffa8e6204ff9473118ffaa398813fc51cc453ffa0e6204ff9073114ffa8398813fc41cc461ff90e6230fdc8731027f843988c3f421cc42dffb066200ff98331005fcc198803fd60cc4017eb066216ff1833118ffea1988c7fe50cc463fea866231ff1433114ffe81988a7fe40cc453fea066229ff10331187fe41988c3fc20cc409ffb2c6204bfd9631027fccb1880efe658c409bf32c62039f99631027facb188befd658c409beb2c62009f59631027f8cb18812fc658c409ffb246204bfd9231027fcc91880afe648c409feb24622ebf59231027f8c918812fc648c45dffaa4622edfd5231177fca9188bbfd548c45dbeaa4622eff1523115dfac7188bfff538c45fff29c622fff54e3117ff8a7188bbff438c45dff21c622ef790e31177fa87188bbdd438c45dfe21c6204ffd8a31027fcc518806fe628c409feb146200bf58a31027f8c518812fc628c45fffa94622dff94a3117ffaa5188b7fc528c45dffa14622dff90a31177fa85188b7fc428c401ff994622dff8ca31007fa65188b7fc328c4097f30c6204ffd4631027fca318813fd518c409fe28c6204ffd
  | 7 => 0x400000000000200000203001600a00a00200200600401002201000000200200600000400400400000a00400000a00000200200000400000000001e01201e00000400800200000a00000e00201400000000800600200400200401000000c00000400e00000800200200600c00000c00600001201400001200400001600c00000800000001400400202400002a00000600000000401600000000003801000200000c01200001202200001200000002800000600800200800200c00400000000000000200200001200a00600400000001a00000000200c00000600800800603600200000a00603400a02400c00801600400a00000201400400001000600a02802a00200a00400801e00000600600800200a00000200400c00800400003600000800200000600600800000a00000c01e00c00600001600200400001000601601800800000001200000000201800400802202c01c00000000001c00200800400000200402400200600600000001000400000e00000000402e00000000000000000000000201600c00600000001200000e00c00a02201c00000400200400000c00000200a00000a01401e00000600000201000000200000400000a00800201001c00800c00000000400401000200200201601600000a00400c01200200c00a00800a00a00a00a00600000e00200000600201000000000802a01400200400000a00404800200800002e01801400000000000000400000400200200200a00200e00000a01800800004200a00600000400000000200200000000800000000600001800000802803402400600c16ffd97321adfecb990d7fe65cc8077f32e6435ff597321adfacb9905bfc65cc8077e32e6416ffd93321a5fec9990d3fe64cc8057f3266434ff593321a5fac99905bfc64cc8057e3266434ffd53321a6fea9990d3fe54cc869feaa66434df553321a7f8a999006fe63cc86bffa9e6416ff94f321afbca7990d7fd53cc86beea9e6416ff14f321a7fe879905bfe43cc869ef21e6434ff50f321a7ba879905bfc43cc8037eb166401ffd4b3200ffca599007fd52cc803fe2966401ffd0b3200ffc8599007fd42cc803fe2166401ff8cb3200fbc6599007ee32cc803fe1966401f70cb320b7fec399003fe61cc8097f30e6400ff58732005fac39905bfc61cc86bffa8e6435ff947321affaa3990d7fc51cc869ffa0e6434ff907321a7fa83990d3fc41cc803ff90e6401ff087320b7fec199003fe60cc8017f3066400ff58332005fac19905bfc60cc86bffa866435ff943321affaa1990d7fc50cc869ffa066434ff903321a7fa81990d3fc40cc803ff9066401ff0833219ffeca990ceff654c801bfb2a64009fd953219ffcca9900efe654c867feb2a6433bf5953219ff8ca9900efc654c867be32a64039f19532197fec8990caff644c86
  | 8 => 0xef000000000083800150000124424806d0658800002f178d73d58c00001c718a4800000000005c0500000000013dc000c2c32473818029c76969010532c0000017a871c274b48000ec0000000000bcc000000001540cdc000fdc001444a107718200006100006540000000006cc0003c561588c7c16640018b4b601c955d6a9870ba82cd9957c4dc45841f84614c0b286ecf6c810ca8001940a20001360000f915e8000ca408800000131d1c00001ec36d818b75338048e246900018e8118c1cfa40004580006790993f8000000000000000e6c12d1184cd97c97570081d830a60840000000de800000073cdb4cb15209e04b0dd00ec00149118d350c945ccc245047e99ac00000181cc7c534e9802c0018c00010348d16b80d0000d606a58a1138f30001001695884001494000aec000be45c07a8c0470c52937c6fd014000a7183c721544000000a0c0000006b472d3319a8000f0c21000031c000000ae10d0000d64001170751628a15608000ab15b43a9274be882c20d6d94b4a29808000c8c001018e04d895854d984085d4ed2f164509171d9209b98515180000009dcab9024dc800038000081400000000069400000021c0000000012b4000d080013c8000ef8edc0011600000000018484500000000000000003d054c0bca451892341f0ee43786e962c34d8fc9783b47cc2f8000bd47f80000016ac5495710040010944692d1784b64355180000000000000000000950e6113cc991f46f48b82957a4000a2d46cf955c558934d5601013a45582fc4940000000000012ec0000000000001fc11d90cda0000aac0013016b0098c38d740017153540010c40010e894ca9800143800098c00052c001564000000604614a193b43ec4bd98400110000000000000193c0000000003ad0540006440002600000000d40000acb0d66102c001978000a586185bc6686752b81103393f4680a4c3918d088099c53969c0b00011f0e4d5e53480c4b000008a4218f2000000000016c00108c00138c97c00020400000007555124c0000000000012280000012fc00000043563190048c0008cd17548cd8c0004e4d4115cc84094e9400126000001202a00000201a00402200000600002e01400000000000600000200000c01001400c00200000000000000200402803200000600c00000000202001a00000000200401202202a00200a00800e00200200001000000c00400001601200600000201c00001a00000605000000200000200001600200e02a01400200a00000200200000000600203001000a00200000601c00200000801e02c00400000400000200001400e00200a00000400400000600a00600000a00001000200800600000a00c00400000000000804200601600800000c00e00400600000000400202a00400401000a01000401400200002c00
  | 9 => 0x119d688b3c174b1d0a8bb0f60001890384a901896748ed11d7c12f4000000000d9444c4ac57d1d1230f8ca255ec0001c0f8019c8291e47d533c0015a4000d155383200000016214540006b80000000007c807c754de0ae419096d70c17c7fd8ec0008354cd5680000017a00000797ac00035d7280018e47ac000ecd5acd7874c6296c89b4dd4491634d4c000000000b840008211b8499204000fb45c4000ac00003651ed6980000017dc0854e00012796fd75cfe563c91d548d696500000004fccb87e149c37040c30d4e5108af80000004b80010acf194f989c350114b7000137105c059990138fa000000000000182400000000000000000035901d36952800161ced826d8bc000000aa19a4ee029800113000000174c0004d54c8bb4000da4000fc8d907ec000c8013d378df8c30bec69d0dc8504ec6300691e97983947783c9895758ae8df5960001311210f082b848884c9440000000000004e00000009a1264000b4c0000e965400000140c000a5c3b93411110f00c0d504d98281514fcb388580005a8228e003000019649f1834948670cd0f7d1400006c55f54104c0ce47d90f55d0acd2ac1cc6a8d2d0b8a55640cacdd8b44c202d475d434f89860ead47800082490542d2400011b45e4d014e80714247b00017f19100015156f80000000006480010d977c00000000000000000000168136c000eb130d7bc564c2972186800130952c9083e1254000000000de461d5c083d3b9844ce90380018a99346e00000000000018545092bc3dc2bd8ac000000000c0925800167146800000126c0000015a06a00000000018e0000ad5115344000000f0400197584c98507827cd6d21561929ce503e80000008a8c643c00019a0244444e280000000002140014c523c0015a8c5562400049c87d7c8000a946849ace7c001028d70e8c0000013cd0f94d02596c43bcad81291051b1304dec0005e8d8180406084474544c000000000000b909580017f80000014880fc0000000000006089917d093c000001128000000000000000a644a12709217f574876c1a8000000f357880000000f57745502e85803cd54c47c000000d5d0682887bce1c660e64b880001d8001498fb80000003053d58b15bc5951d5814000ac40012e193896093400125c00000000000000000146572c424cec0000000019280001b935d0d4a74000000bc80013f07483089d00012a0a40000fd80000007309e89882c400120c0000000000010e000000066c0000000000013e85fc001770aa4b34ca1058ddd51c0003d53e4000830f78aa91c4be015ce910106201947580000448c985c000000000000add088000514000000000c887a400000063c6f82f50301540002dd2dc6f0e807092397fd5108f80208c0a346251ad6595751900000dcc78000000000000000000000178000
  | 10 => 0xc1116c0007e4bac7f4000000ff41c522c000fc4000f38d040000000016681209c8000a000001840000017680003f4000c3ccd8000560270f4c108000000000000a1c51c0000000017044009f96c11e0a5191c78c000bf92c8000000efd2c11a510c000c58000d4418d724000000000000c4400008d05000094000124994d3c4140714000000000500000000cc52812cc4b598c0d90b40342d8000a0594863400000000000088800037ca381700000015fd6845ad739710af16f58f0001988a893593fc220954440e5cf118c54a126996943cb98cf15348b57ec980000000000724f2c00167cd5425cf4121838c705524000cf8688bfc6000006bc000a8d595380000000000000d0c0014149640006400005b800064d1992a4e9c000000c9c8d4e08000ad02b0b146ac00010d50c000f5800159d6e9420afcf0127cbc4f1cc14cc142828176143000090cfc157855c23c001744fd4d84b9c860478598008000eb40017096e00000000000000000000800000a4000000c5c8840e4000800a780000000000000004540019500016ec0b903c00014c0000000000015c824c0010a4d100011f8000a0800112cfe82c04305dc0008797cd401470b5867d8f4000334f44250b30f758b95f86d46d18a4264af515000057800000112400001800077cf140000000000014d40016042098987f182cc715d5909020cfd37539545c46d5f09bd044ea18dcd355b89389682352888d8000144000d9d99c8f54a458968c6dd3b153c0414609a4bf179085400147c4a520060cb8cc605ecd3c3f07901d12a986458d4481bcf545f0000fbce34dfc5a156d1941489942c888c0000012e83986b07845449317808a00000002392996bd070e4800426892ce7996d3988e46640010a000000000186d8d97b000187c5700000016100000000000014bc0000013280014195cc0007940011a1284cbcfecb517e85b00001686c01e59702e000050c0002541240004f8000000000001474134000eed41ccc80010e50b00000007c4000000001754eb8dc0c0c5745a44709c49ec31507c910ccc015060ac8b780a80002302a8734fa880c9c15913e12e4d2513400000129165d14d6003297941a04c91cd5042a000cebc40827843c0001d400150800195c3e4000bc0520914658000fd16e4591800000c507811fd59828ca3c33c6c89cc00140800041cbf4dac7dc00000179c000b402d17b80300009b0f852f822c00000099904c0640000010cc0011bc5d57792090740016dcd1d39c32d7d91d8a7c374000000000241638ed456d7640000000540000017512b0ea8b68510000000000e38900f98fe0f9cb94000484a80bd00009a800034400128d730f28774b54b6d6493d8788000b804a9364000890000fb03a4e200014400000014f01b00009fc5688bc0
  | 11 => 0x195459d06d4dc9d80000013d1148ff93a11844dd858f3c001404000000e159156b4e2cd2886d17c038c4192cd380251796d00013a89e44c40000017405554ac000000000b247d05413bc0000000000000000000c8001158f68db00018cc000ea4000c48000000e3c8f0000ba47408944040015b0160b2180c4392d5718198f65959458e400013888dd5815d94808980000011c8000000000924e5442129404cb2c8ac9288e01596d51641f45f40b4e84d202ac9f4f70df0760001810000848e740e00012d9918000e6800095d0ec000ab4000e10c68000868000318465678000000001318bd966cc001a4b042a40f86e53c00a0000f24ee80010080007984805f87b43fc2e4000ffd88803c01028480590400068c0000000005b40000000017b4000000000000d98000000c18000abce58bdd33500c29109d2c53ac8b05314b05d9144c90000410ba0b117e0c750fcc4d930f500000000000000000003400900005d0638000000475251154448d484140000013ec764331081878d7c000e308fc428e44dcd04009cb7d31481960d22000000000089c000faca318383d8ce0b5c0000000013241301dd4b96a0348000000ef400000000000065c0000019983f8bb98c95dcb181640f00018f8e880008c4ed01b4000000000cb40007118d5484f5ca9c000650a695546d800138439c000000ec4388dbcc6d0488080000000000000000000007280009d42ed6a420192598157d1dc1ad3900000000000001e842c0290c15e11a8000a855585190bce0c00176c8e80002b40019b0000da8000000970000c348640000000000000003600016cc0000000000016f04d17344f4000000d197e4000e187b94a964c3b08700000000004e84187010c8e705c8001120d580019440018754f400000000000053c36879c0017d40004f00000000000000005242243105e0698ec8d30cd4874ff132000000045d2250840011681e15300007a0001450000000b0800000000000000121c000bbca6cf483a0cf4fcc00000000000091800000062c0000ccdb800
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc20594100267f10594100267710594100267e10594100267d10594100267c10594100b4ff7598c1001cfe7598c10004fd7598c100b4fc7598c100b4ff7498c10014fe7498c10004fd7498c100b4fc7498c100067f5498c100067d5498c10026de7398c100b6de4398c10006dd4398c1000cfe7298c10004fd7298c1000cfc7298c10024fe7198c10024fc7198c10026de3198c10026dc3198c10004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10026df7358c10006de4358c10006dd4358c10004ff7258c1000cfe7258c1000cfc7258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c10026de3158c10026dc3158c100b4ff7058c100dcfd7058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc74588100067f54588100067d5458810004ff73588100b4fc7358810026ef725881002eee4258810006ed425881002eee3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec215881000cff705881000cfd705881002cfc705881002eec2058810026fa1058810026f910588100b4ff76cc810024fe76cc810004fd76cc810024fc76cc8101ae7e65cc8100067d65cc8100b6de63cc810006dd63cc810004ff764c810024fe764c810004fd764c810024fc764c8100057f754c81003d7c754c81019e7e654c8100067d654c810006de634c810006dd634c81000eee624c810006ed624c810005f7714c810025f4714c810004fd76cc01010e7e65cc0100067d65cc010004ff768c010004fd768c0100fe7e658c0100067d658c010006de638c010006dd638c010025f6718c010005f5718c010004ff764c0100057f754c01003d7c754c0100ee7e654c0100067d654c010005bf744c010035bc744c0100b4ff760c010024fe760c010004fd760c010024fc760c0100c67e650c0100067d650c0100b6de630c010006dd630c010025f6710c010005f5710c010064ff7688010024fe768801000cfd7688010024fc76880100a67e65880100067d658801000eee6288010006ed6288010025f67188010005f57188010066fa6088010064ff76480100967e65480100067d6548010066fa6048010025f77644010006f77644010004f776440100077775440101b7747544010026f765440100277665440101b6f56544010027756544010006756544010007b774440101c7b47444010026f764440101c6f564440101c77754440101c7755444010007d77344010007d47344010007e77244010007e47244010025f77044010027f370440101bef66044010027f260440101b7f250440101b7f15044010007f23044010007f13044010
  | 1 => 0xc110006df634c110006dc634c110006ef624c1100deec624c110005f7714c110025f4714c110004fe760c1100067f650c1100c67c650c110006bf640c1100bebc640c110006df630c1100b6dc630c110006ef620c1100aeec620c110007d9300c110074fe76881100067f65881100a67c6588110006bf648811009ebc6488110006df6388110006dc6388110006ef628811000eec6288110005fa7688110076fa76881100077b6588110207786588110007bb64881101ffb864881101ff7b54881101ff795488110007db6388110007d8638811004df97288110007eb628811000efa628811000ef8628811004fe8628811000ee86288110025fa7188110025f87188110207f25188110207f151881101fff241881101fff141881101f7ea21881101f7e8218811000cff764811004cfd7648110024fc76481100067f65481100967c6548110006bf644811008ebc6448110006df6348110006dc6348110006ef624811000eec6248110005f77148110025f47148110025f8764811000ef87648110024f876481100077b65481101ef786548110007bb64481101e7b864481101e77b54481101e7795448110007db6348110007d8634811004dfb7248110007eb7248110007eb624811000efa624811000ef8624811004fe8624811004fea42481101e7e94248110007f37148110025fa7148110025f87148110007f071481101eff251481101eff151481101e7f241481101e7f141481100067f658411006e7c6584110006bf6484110046bc6484110006df6384110006dc6384110006ef6284110066ec6284110025fa7084110026fb6084110025f67684110026f67684110024f676841101ddf775841101ddf575841100077765841101d77465841101bdf774841101bdf57484110007b764841101cfb464841101cf7754841101cf755484110007d76384110007d46384110007e76284110007e46284110025f67084110026f76084110027f36084110007f22084110007f120841100067f74594100047f74594100067e74594100067d74594100047d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067e32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941003e7f70594100067e705941003e7d705941003e7c70594100067f40594100067e40594100067d40594100067c40594100067f20594100067
  | 2 => 0x67c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc635891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df73589100b4fc7358910006dc7358910004dc735891004cff7258910006ef7258910064ff7158910006f77158910074ff7058910006fb7058910005ee761891004eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac64189100076f54189100076d5418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e65118910007e55118910007e64118910007e5411891004fe9701891020eef601891020feb101891020fe810189100b4ff76cc910004fe76cc910004fd76cc9100b4fc76cc9100067f65cc9101ae7c65cc910006bf64cc9101a6bc64cc910006df63cc9100b6dc63cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c91005d7c754c9100067f654c91019e7c654c910006bf644c910196bc644c910006df634c910006dc634c910006ef624c91000eec624c910005f7714c910025f4714c910004fe76cc5100067f65cc51018e7c65cc510006bf64cc51014ebc64cc510006df63cc5100b6dc63cc510006ef62cc510186ec62cc510005fa70cc510005f970cc510004fc764c5100067f654c5101667c654c510006bf644c51015ebc644c510006df634c510006dc634c510006ef624c510156ec624c510027d4314c510005fb704c510005f8704c510027f0104c51000cfc76485100067f654851011e7c6548510006bf6448510116bc6448510006df6348510006dc6348510006ef624851000eec6248510005fb7048510005f87048510024fe76cc1100067f65cc11010e7c65cc110006bf64cc1100d6bc64cc110006df63cc1100b6dc63cc110006ef62cc110106ec62cc110025f671cc110005f571cc110004fe768c1100067f658c1100fe7c658c110006bf648c1100cebc648c110006df638c110006dc638c110006ef628c1100f6ec628c1100b4ff764c110004fd764c110024fc764c1100057f754c11005d7c754c1100067f654c1100ee7c654c110005bf744c110055bc744c110006bf644c1100e6bc644
  | 3 => 0xf7218d10006de7218d10006dd7218d100b6dc7218d10006df5218d10006de5218d10006dd5218d10006dc5218d10006df4218d10006de4218d10006dd4218d10006dc4218d100b6df7118d10216de7118d10006dd7118d100b6dc7118d10006df5118d10216de5118d10006dd5118d10216dc5118d10006df4118d10216de4118d10006dd4118d10216dc4118d10006df2118d10216de2118d10216dc2118d100b6df7018d10006dd7018d10006df5018d10006de5018d10006dd5018d10006dc5018d10006df4018d10006de4018d10006dd4018d10006dc4018d10006df2018d10006dc2018d10216df1018d10006dd1018d10216dc1018d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d89100b4fe73d8910004fd73d8910006ef52d891004eee52d8910006ed52d891004eec52d8910006ef42d891004eee42d8910006ed42d891004eec42d891004eee32d891004eec32d8910024fe71d891004cfd71d8910024fc71d891004eef21d891000cfe70d8910024fd70d891000cfc70d891004eef20d891004dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d89100076f54d89100076d54d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e651d8910007e551d8910007e641d8910007e541d89101f7eb70d89101f7eb10d89101f7e810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d89100066f54d8910006ee54d8910006ed54d89100066d54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d89101f6ee71d8910006ed71d89101f6ec71d8910006ef51d89101f6ee51d8910006ed51d89101f6ec51d8910006ef41d89101f6ee41d8910006ed41d89101f6ec41d89101f6ee31d89101f6ec31d89101f6ef70d891004eee70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d89101f6ef10d89101f6ec10d89100057f755891005d7c75589100067f6558910
  | 4 => 0x8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006dc20d8d1021edf10d8d1021edc10d8d1005d7e7598d100057d7598d100067f6598d100067c6598d10055be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d1004dee7298d10005ed7298d100b4ff7598d1001cfe7598d100b67e7598d1001c7e7598d10004fd7598d100b67d7598d100047d7598d100b4fc7598d100b4ff7498d10014fe7498d100b6be7498d10014be7498d10004fd7498d100b6bd7498d10004bd7498d100b4fc7498d100067f5498d100067d5498d100b4fe7398d10004de7398d1000cfe7298d100b6ee7298d1000cee7298d10004fd7298d100b6ed7298d10004ed7298d1000cfc7298d10004fd7198d100b6f57198d10004fd7098d100b6f97098d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10055bc7458d10006bf6458d10006bc6458d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10006dd6318d100b4ff7518d1001cfe7518d10004fd7518d100b4fc7518d100b4ff7418d10014fe7418d10004fd7418d100b4fc7418d100067f5418d100067d5418d100b6de7318d10006df5318d100b6de5318d10006dd5318d100b6dc5318d10006df4318d100b6de4318d10006dd4318d100b6dc4318d1000cfe7218d10004fd7218d1000cfc7218d10006de3218d100b6dc3218d10024fe7118d10024fc7118d100f4fe7018d100b4fc7018d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d100075d5418d10006de6218d10006dc6218d10007d65118d10007d55118d10007d64118d10007d54118d10217db1018d10217d81018d100b6df7518d10006de7518d10006dd7518d100b6dc7518d100b6df7418d10006de7418d10006dd7418d100b6dc7418d10006df5418d100065f5418d10006de5418d10006dd5418d100065d5418d10006dc5418d100b6d
  | 5 => 0x22e7f10d951005e7d10d951022e7c10d9510055be76d9110056be76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d9110007b771d9110057b471d9110007b651d9110007b551d9110227bb10d9110227b810d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d9110006bf71d9110226be71d9110056bd71d9110226bc71d9110006bf51d9110226be51d9110006bd51d9110226bc51d9110226be31d9110226bc31d9110006bf21d9110226be21d9110226bc21d9110226bf70d9110056be70d9110056bd70d9110056bc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf20d9110006bc20d9110226bf10d9110056bd10d9110226bc10d91100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10006dc32d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075f54d8d100075d54d8d10006de62d8d10006dc62d8d10007d651d8d10007d551d8d10007d641d8d10007d541d8d1021fdb10d8d1021fd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d100065d54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1021ede71d8d10006dd71d8d1021edc71d8d10006df51d8d1021ede51d8d10006dd51d8d1021edc51d8d10006df41d8d1021ede41d8d10006dd41d8d1021edc41d8d10006df21d8d1021ede21d8d1021edc21d8d1021edf70d8d10006dd70d8d10006df50d
  | 6 => 0xe7558a10004fd7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a100067f5458a100067d5458a10004ff7358a100b4fc7358a10006ef7258a10066ee4258a10006ed4258a10066ef2158a10024fc7058a10066ec2058a100b4ff76cca10004fe76cca10004fd76cca100b4fc76cca10006df63cca100b6dc63cca10004ff764ca10004fe764ca10004fd764ca10004fc764ca100057f754ca1006d7c754ca10006df634ca10006dc634ca10005f7714ca10025f4714ca100b6de63cc610006dd63cc610005fa70cc610005f970cc610006de634c610006dd634c610005fb704c610005f8704c61000cff764861000eee6248610006ed6248610005fb7048610005f87048610024fd768c210006de638c210006dd638c210025f6718c210005f5718c2100057f754c21006d7c754c210005bf744c210045bc744c210024fd760c2100b6de630c210006dd630c210025f6710c210005f5710c210007d9300c21000cfe7688210024fd768821000eee6288210006ed6288210025f67188210005f57188210025f9768821000ef97688210024f9768821024f7b548821024f79548821000efa6288210067ea6288210007e9628821000ef86288210025fa7188210007f27188210007f17188210025f871882101f7ea21882101f7e8218821002cff7648210005fb764821002efb76482102477b5448210247795448210007eb724821000efa624821000ef86248210067ea4248210247e94248210025fa7148210025f87148210005f576c4210026f576c4210236f765c4210236f565c421023ef764c421023ef564c421023f7754c421023f7554c4210027f260c4210237f250c4210237f150c421005d7e76d951005e7e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e62d95100067c62d95100077771d951005f7471d95100077641d95100077541d951022f7b10d951022f7810d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d95100067f71d951022e7e71d951005e7d71d951022e7c71d95100067f41d951022e7e41d95100067d41d951022e7c41d951022e7e31d951022e7c31d95100067f21d951022e7e21d951022e7c21d951022e7f70d951005e7e70d951005e7d70d951005e7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067c20d9510
  | 7 => 0x8f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10026df7358f10004ff7258f1000cfe7258f1000cfc7258f10024fc7158f10026de3158f10026dc3158f10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b100b4fc7358b10026ef7258b10024fc7158b10026ee2158b10026ec2158b10076ef2058b10026fa1058b10026f91058b100b4ff76ccb10024fe76ccb10004fd76ccb10024fc76ccb100b6de63ccb10006dd63ccb10004ff764cb10024fe764cb10004fd764cb10024fc764cb100057f754cb100857c754cb10006de634cb10006dd634cb10005f7714cb10025f4714cb100b6de63cc310006dd63cc310025f671cc310005f571cc31021edf638c31021edc638c3100057f754c3100857c754c310005bf744c31007dbc744c310006de634c310006dd634c310005f7714c310025f4714c310216df630c3100b6dc630c31004cfd76883101f6ef628831000eec628831000cff7648310024fc764831000eee6248310006ed6248310005f77148310025f47148310004ff75d8e1001cfe75d8e10004fd75d8e1001cfc75d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e100067f54d8e100067d54d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006f571d8e1021ede31d8e1021edc31d8e10006fa70d8e10004fd7698e10006df6398e100b4ff7598e1001cfe7598e10004fd7598e100b4fc7598e100b4ff7498e10014fe7498e10004fd7498e100b4fc7498e100067f5498e100067d5498e100b6de4398e10006dd4398e1000cfe7298e10004fd7298e1000cfc7298e100057f7558e1006d7c7558e10004ff7558e100067f7558e100047f7558e1001cfe7558e10004fd7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e100067f5458e100067d5458e10006df7358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e10006dd6318e100b4ff7518e1001cfe7518e10004fd7518e100b4fc7518e100b4ff7418e10014fe7418e10004fd7418e100b4fc7418e100067f5418e100067d5418e100b4fe7318e100b6de7318e1000cfe7218e10004fd7218e1000cfc7218e100b6f57118e10216de3118e100b6dc3118e100b6fa7018e10066ee62d8a10004ff75d8a1001cfe75d8a10004fd75d8a1001cfc75d8a10004ff74d8a10014fe74d8a10004fd74d8a10014fc74d8a100067f54d8a100067d54d8a100b4fe73d8a10004fd73d8a10064fd72d8a10006f571d8a101f6ee21d8a101f6ec21d8a10006fa70d8a1000cff7658a10066ec6258a10004ff7558a1001cf
  | 8 => 0x57f7558d200957c7558d20005bf7458d2008dbc7458d20005f77158d20005f47158d20105fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d200067f5458d200067d5458d20006df7358d20006de4358d20006dd4358d200dcff7258d20006ef7258d200deee4258d20006ed4258d20004ff7158d20006f77158d20004f77158d20024fc7158d20006f47158d20024f47158d20104ff7058d20006fb7058d200f4fe7618d20006dd6318d200b4ff7518d2001cfe7518d20004fd7518d200b4fc7518d200b4ff7418d20014fe7418d20004fd7418d200b4fc7418d200067f5418d200067d5418d200b6de7318d200b4ff7218d2000cfe7218d200acfd7218d2000cfc7218d200b6df3218d200aedd3218d20024fe7118d20004fd7118d20004ff75d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d85200b4fe73d8520004fd73d8520066f621d8520066f521d8520024fe70d8520006f7619852004df970985200057f75585200957c7558520005bf745852008dbc7458520005df7358520005dc7358520075fb70585200957e75185200057d7518520026f66118520006f56118520004fe76cc520004fd76cc5200b4fc76cc520006f761cc520026f461cc520004fe768c520004fd768c520024fc768c5200957e758c5200057d758c520006df638c520006dc638c520005fa708c520005f9708c520004ff764c520004fe764c520004fc764c520004fe760c520004fd760c520024fc760c520006df630c5200b6dc630c52000dee720c520005ed720c520006f7610c520026f4610c520005fa700c520005f9700c52000cfe76cc12000cfc76cc120006df63cc1200b6dc63cc12000dee72cc120005ed72cc1200acfe768c120006de638c120006dd638c1200b4ff764c12000cfe764c1200dcfd764c12000cfc764c1200057f754c1200957c754c120005bf744c12008dbc744c120006df634c120006dc634c120005ef724c12000dec724c1200f4fe760c1200b6de630c120006dd630c12025def748812025ded74881202576f54881202576d54881201f6ec618812000dee708812000fea708812000eef608812000feb60881200b4ff7598f1001cfe7598f10004fd7598f100b4fc7598f100b4ff7498f10014fe7498f10004fd7498f100b4fc7498f100067f5498f100067d5498f10026de7398f1000cfe7298f10004fd7298f1000cfc7298f10024fe7198f10026de3198f10026dc3198f10004ff7558f1001cfe7558f10004fd7558f1001cfc755
  | 9 => 0xc7498e200067f5498e200067d5498e200b6de4398e20006dd4398e200b6df3298e20106dd3298e20024fe7198e20004fd7198e20004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e200067f5458e200067d5458e20006df7358e20006de4358e20006dd4358e200dedf3258e200dedd3258e20004ff7158e20024fc7158e20006dd6318e200f5fa7018e200b4ff7518e2001cfe7518e20004fd7518e200b4fc7518e200b4ff7418e20014fe7418e20004fd7418e200b4fc7418e200067f5418e200067d5418e200b4fe7318e200b6de7318e200b6ed7218e20024fe7118e20004fd7118e200f4fe7018e200b6fa7018e2002dfa70d8620006f76198620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620014fe7458620004fd7458620014fc74586200067f54586200067d5458620004ff73586200b4fc7358620006f65158620006f55158620006f64158620006f5415862004ef6215862004ef521586201f6ec2158620024ff70586200a57e75186200057d7518620026f66118620006f56118620065fa70186200b4ff76cc620004fe76cc620004fd76cc62000dee72cc620005ed72cc620026f661cc620006f561cc620187e421cc620024ff768c620004fe768c620004fd768c6200a57e758c6200057d758c620005fa708c620005f9708c620004ff764c620004fd764c620004fc764c620005ef724c62000dec724c620024ff760c620004fe760c620004fd760c620026f6610c620006f5610c6201f7e4210c620005fa700c620005f9700c620266ef6488620266ed64886202676f54886202676d548862000dee718862000fe671886201f7e661886201f6ed6188620007e561886201f7ea7088620005ed70886201f7e9708862000eee608862000fea60886200dcfd76cc22000cff768c22000cfd768c220006de638c220006dd638c22000dee728c220005ed728c220104ff764c2200057f754c2200a57c754c220005bf744c22009dbc744c22000cff760c22000cfd760c2200b6de630c220006dd630c22000dee720c220005ed720c220004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d200f4ff72d8d200f4fd72d8d200f6ee42d8d20006ed42d8d200f6df32d8d200f6dd32d8d20024fe71d8d20004fd71d8d20006df6398d200ddf97098d200b4ff7598d2001cfe7598d20004fd7598d200b4fc7598d200b4ff7498d20014fe7498d20004fd7498d200b4fc7498d200067f5498d200067d5498d200b4fe7398d200b6de4398d20006dd4398d20104fd7298d200b6ed7298d20024fe7198d20004fd7198d200dcfd7098d200b6f97098d20
  | 10 => 0xc830007d7714c830215dc714c830007d4714c830005d4714c830005df704c8300f6de604c8300b6f76198430026f461984300b6f46158430004ff755843001cfe7558430004fd755843001cfc7558430004ff7458430014fe7458430004fd7458430014fc74584300067f54584300067d5458430004ff725843000cfe725843000cfc7258430006df3258430006dd3258430006f65158430006f55158430006f64158430006f541584300b6f731584300b6f43158430004fd768c4300c57e758c4300057d758c430005dd768c430216dd768c4302175e758c4302175d758c4302b6df648c4302b6dd648c4302b75f548c4302b75d548c430005dd728c4300b5de718c430216dd618c430005dd708c43021ede608c430004ff764c4300b6df640c4302aedd640c4302af5f540c4302af5d540c430005dd720c430215de710c4300b7d6710c4300b7d6610c430216dd610c4300b7d5610c430006d5610c4302a7d7210c430217d4210c4300b7da700c430005dd700c4300b7d9700c430005d9700c43021ede600c430024ff76884300b4fe7688430004fd7688430215df73884300b5dc7388430026f66188430006f56188430004ff7648430004fd76484300b4fc7648430005df73484300b5dc734843000eee6248430006ed6248430026f66148430006f561484300b6df64cc03029edd64cc03029f5f54cc03029f5d54cc030005dd72cc030215de71cc030295dd738c03028ede638c0302877b548c03028779548c0300b5f9738c0300b6fa638c0300b7da638c0300b7db328c030007d9328c030007da318c0300b7d8318c030004ff764c0300057f754c0300c57c754c030005bf744c0300bdbc744c030005df764c030006df764c030004df764c0300075f754c0302775c754c0300079f744c03026f9c744c03026edf644c03026edd644c03026f5f544c03026f5d544c030005df724c030215dc714c0300b5df704c03027ede604c0300b5fb764c030006fb764c030004fb764c0300077b754c03027778754c030007bb744c03026fb8744c03026f7b544c03026f79544c0300b5fb734c030007db734c0300b6fa634c0300b7da634c0300b7db314c030007d9314c0300a57e75d8e200057d75d8e20005f671d8e20005f571d8e200adfa70d8e20004ff75d8e2001cfe75d8e200067e75d8e2001c7e75d8e20004fd75d8e200067d75d8e200047d75d8e2001cfc75d8e20004ff74d8e20014fe74d8e20004fd74d8e20014fc74d8e200067f54d8e200067d54d8e20006ed72d8e20024fe71d8e20006f671d8e20024f671d8e20004fd71d8e20006f571d8e20004f571d8e200acfe70d8e20006fa70d8e200dcfd7698e20006df6398e200b4ff7598e2001cfe7598e20004fd7598e200b4fc7598e200b4ff7498e20014fe7498e20004fd7498e200b4f
  | 11 => 0x14fc74d85300067f54d85300067d54d853000cfe72d8530004fd72d853000cfc72d8530006f721d8530006f421d85300ed7e75985300057d75985300067f65985300067c65985300e5be7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300ed7c75585300067f65585300067c6558530005bf74585300e5bc7458530006bf6458530006bc6458530005ef72585300ddec72585300067f65185300067c6518530006bf6418530006bc6418530026f66118530006f56118530004fe76cc5300067f65cc53018e7c65cc530006bf64cc53014ebc64cc5300ed7e758c5300057d758c5300067f658c53017e7c658c530006bf648c530176bc648c530006f7618c530026f4618c530005fa708c530005f9708c530024fc764c5300067f654c5301667c654c530006bf644c53015ebc644c530006f7614c530026f4614c530005fb704c530005f8704c530004fe760c5300067f650c5301467c650c530006bf640c53013ebc640c530007d5310c530004fe7688530004fd7688530024fc76885300067f658853012e7c6588530006bf6488530126bc6488530006ef628853000eec6288530004ff7648530004fe7648530004fc76485300067f654853011e7c6548530006bf6448530116bc64485300067f65cc13010e7c65cc130006bf64cc1300d6bc64cc1300077b65cc1302f77865cc130007bb64cc1302efb864cc1302ef7b54cc1302ef7954cc1300b7da43cc1302efd943cc1300067f658c1300fe7c658c130006bf648c1300cebc648c1300075f658c1302e75c658c13027ddf748c13027ddd748c1300079f648c1302df9c648c1302df5f548c1302df5d548c130006df628c13021edc618c130007db608c13000cff76588300b6ec6258830004ff755883001cfe7558830004fd755883001cfc7558830004ff7458830014fe7458830004fd7458830014fc74588300067f54588300067d545883000cfd73588300aeee5258830006ed52588300aeee4258830006ed42588300b6ef32588300b6ec3258830004ff7158830024fc71588300aeef21588300aeec20588300b5dd76cc83000edd76cc83000cdd76cc8300b6df65cc8302d6dd65cc8300b6df64cc8302cedd64cc8302cf5f54cc8302cf5d54cc8300addd72cc83000ede62cc8300b7ce62cc8300b7cd62cc83000edc62cc830215de71cc8300b7da70cc830005dd70cc8300b7d970cc8300f6de60cc830104ff764c8300057f754c8300c57c754c830005f7714c830005f4714c830005df764c830106df764c8300075f754c8302c75c754c8302c6df654c8302c6dd654c8302bedf644c8302bedd644c8302bf5f544c8302bf5d544c8300b5df724c8300b7cf724c83000ede624c83000edc624c8300afce524c8302c7cd524c8300afce424c8302bfcd424
  | 12 => 0xf74d95300067e74d95300067d74d95300047d74d95300067c74d95300067f73d95300ee7e73d95300ee7d73d95300ee7c73d95300067f43d95300067e43d95300067d43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067f21d95300067c21d95300067f70d95300ee7e70d95300ee7d70d95300ee7c70d95300067f40d95300067e40d95300067d40d95300067c40d95300ee7d30d95300067f20d95300067c20d95300e5be76d91300e6be76d9130014be76d91300073f75d91300073c75d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91300079f73d91300e79c73d9130006be62d9130006bc62d9130006bf75d91300063f75d9130006be75d9130006bd75d9130006bc75d91300063c75d9130006bf73d91300e6be73d91300e6bd73d91300e6bc73d9130006bf53d9130006be53d9130006bd53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130006be32d9130006bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130006bf21d9130006bc21d9130006bf70d91300e6be70d91300e6bd70d91300e6bc70d9130006bf50d9130006be50d9130006bd50d9130006bc50d91300e6bd30d9130006bf20d9130006bc20d913000cfe76d89300067f65d89300067c65d8930006bf64d8930006bc64d89300deee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d893000cfc73d8930006de43d8930006dd43d89300deee32d8930024fe71d8930004fd71d89300deec21d89300deef20d89300057f75589300ed7c75589300067f65589300067c6558930005bf74589300e5bc7458930006bf6458930006bc64589300deec6258930005f77158930005f471589300f4fe76cc9300067f65cc9301ae7c65cc930006bf64cc9301a6bc64cc93000cfc764c9300057f754c9300ed7c754c9300067f654c93019e7c654c930006bf644c930196bc644c930006ef624c93000eec624c9300dfcc324c930005f7714c930005f4714c930005fb704c930005f8704c9300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530
  | 13 => 0x8a30004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a300067f5458a300067d5458a300f6ee4258a30006ed4258a300f6ee3258a30004ff7158a30024fc7158a300f6ec2058a300dcfd76cca30005dd76cca300dedd76cca3033edf65cca3033edd65cca30336df64cca30336dd64cca303375f54cca303375d54cca3000ede62cca3000edc62cca3021dde71cca30005dd70cca3000cff764ca300057f754ca300fd7c754ca3000eee624ca30006ed624ca30005f7714ca30005f4714ca30005fb704ca30005f8704ca300f5df764ca3000edf764ca3000cdf764ca300075f754ca3032f5c754ca3032edf654ca3032edd654ca30326df644ca30326dd644ca303275f544ca303275d544ca30007cf724ca3000ede624ca300f7ce624ca3000ece624ca30007cd624ca3000edc624ca300f7ce524ca3032fcd524ca300f7ce424ca30327cd424ca30007d7714ca3021ddc714ca30007d4714ca30005d4714ca30005df704ca30007db704ca30007d8704ca30006f76198630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc74586300067f54586300067d5458630004ff725863000cfe725863000cfc7258630006df3258630006dd3258630006f65158630006f55158630006f64158630006f54158630006f72158630006f421586300fd7e75186300057d7518630026f66118630006f561186300fd7e758c6300057d758c630026f6618c630006f5618c630005fa708c630005f9708c63021f5e758c63021f5d758c63031edf648c63031edd648c63031f5f548c63031f5d548c630005dd728c63021fd6618c63021edd618c630007d5618c63021fda708c630005dd708c63021fd9708c630024ff764c630026f6614c630006f5614c630005fb704c630005f8704c630005dd760c63021edd760c630316df640c630316dd640c6303175f540c6303175d540c630005dd720c63021fd6710c63021edd610c63030fd7210c63021fd4210c630005dd700c630024ff7688630004fe7688630004fd768863021ddf738863021ddc7388630004ff7648630004fd7648630004fc7648630005df7348630005dc7348630005dd76cc230006dd76cc230306df64cc230306dd64cc2303075f54cc2303075d54cc230005dd72cc23021dde71cc2302ffda50cc2302ffd950cc230005f976cc2300b6f976cc2303077b54cc2303077954cc2300b7da53cc2302ffd953cc2300ed7e76d95300ee7e76d953001c7e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300075e43d95300075d43d95300067e62d95300067c62d95300067f74d95300047
  | 14 => 0x57f7558d2111d7c7558d21185f77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d21006df7358d21154ff7258d21006ef7258d21184ff7158d21006f77158d21184f77158d21004ff7058d21004fc7058d2116cfe7618d21006dd6318d210b4ff7518d2101cfe7518d21004fd7518d210b4fc7518d210b4ff7418d21014fe7418d21004fd7418d210b4fc7418d210067f5418d210067d5418d210b6de7318d21006df5318d210b6dc5318d210b6de4318d21006dd4318d21024ff7218d21024fd7218d210b6df3218d21136dd3218d21136f72118d21136f42118d21004fe7018d21004fd7018d2100cfe76cc52100cfc76cc521006df63cc5210b6dc63cc52100dee72cc521005ed72cc521186f761cc5210b4ff764c52100cfe764c521154fd764c52100cfc764c521006df634c521006dc634c521005ef724c52100dec724c521004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d81210b4fe73d8121004fd73d8121024fd72d8121076fa20d8121006fb60981210057f755812111d7c7558121005bf7458121115bc7458121005df7358121005dc7358121006f96018121004ff751812101cfe7518121004fd751812101cfc7518121004ff7418121014fe7418121004fd7418121014fc74181210067f54181210067d54181210b4fe7318121004fd7318121024fd721812120eee211812120eec211812102ef9201812100cff7658b300b6ec6258b30004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b300067f5458b300067d5458b30006de4358b30006dd4358b30106ee5258b30006ed5258b30106ee4258b30006ed4258b300b6ef3258b300b6ec3258b30004ff7158b30024fc7158b30106ec2158b30106ef2058b300acff764cb300057f754cb3010d7c754cb300b7cc324cb30005f7714cb30005f4714cb3010d7e75987300057d75987300b6f76198730026f461987300b6f46158730004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d5458730004ff725873000cfe725873000cfc72587300b6f731587300b6f4315873010d7e758c7300057d758c7300b7d4314c730024ff76887300b4fe7688730004fd768873000eee6288730006ed6288730004ff7648730004fd76487300b4fc76487300fd7e75d8a300057d75d8a300f6ee62d8a30005f671d8a30005f571d8a3000cff7658a300f6ec625
  | 15 => 0x95098031006fa4098031006f940980310b6fb30980310b6f83098031026fb1098031026f81098031004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc74580310067f54580310067d5458031006de4358031006dd4358031004ff725803100cfe725803100cfc7258031026fb7058031006fa5058031006f95058031006fa4058031006f940580310b6fb30580310b6f83058031026fb1058031026f810580310b4ff7598e2101cfe7598e21004fd7598e210b4fc7598e210b4ff7498e21014fe7498e21004fd7498e210b4fc7498e210067f5498e210067d5498e21026de7398e210b6df3298e21186dd3298e21024fe7198e21024fc7198e21026de3198e21026dc3198e21186f72198e21026f42198e21004fe7098e21004fd7098e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21026df7358e21156ee4258e21006ed4258e21156df3258e21156dd3258e21024fe7158e21024fc7158e21026de3158e21026dc3158e21004ff7058e21004fc7058e21004ff759822101cfe7598221004fd759822101cfc7598221004ff7498221014fe7498221004fd7498221014fc74982210067f54982210067d54982210b4fe7398221004fd7398221024fe7198221026fa7098221066f92098221026fb1098221026f81098221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221006bf7458221004bf7458221014fe7458221004fd7458221014fc7458221006bc7458221014bc74582210067f54582210067d5458221004ff7358221006df7358221004df73582210b4fc7358221006dc7358221004dc735822104eee4258221006ed4258221024fc7158221026fb705822104efa205822104eec2058221026fb1058221026f81058221004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d21006df53d8d21006dc53d8d21006de43d8d21006dd43d8d21024ff72d8d21024fd72d8d2116edf32d8d2116edd32d8d21004fe70d8d21004fd70d8d21006df6398d21155f57198d210b4ff7598d2101cfe7598d21004fd7598d210b4fc7598d210b4ff7498d21014fe7498d21004fd7498d210b4fc7498d210067f5498d210067d5498d210b4fe7398d21184fd7298d210b6ed7298d21154fd7198d210b6f57198d21186f72198d21186f42198d21004fe7098d21004fd7098d21
  | 16 => 0x8931156ec20d89310057f75589311657c7558931156ec625893116cfe76cc931005de76cc93116ede76cc93137edf65cc93137edd65cc931376df64cc931376dd64cc9313775f54cc9313775d54cc931155dd72cc93100ede62cc93100edc62cc931025de71cc931025dc71cc9310b6df61cc931024fc764c9310057f754c9311657c754c931006ef624c93100eec624c931005f7714c931025f4714c931025dc764c93100edc764c931024dc764c9310075f754c93136f5c754c93136edf654c93136edd654c931366df644c931366dd644c9313675f544c9313675d544c931155df724c931007cf724c931007cf624c93100ede624c93100edc624c931157cc624c93100ecc624c931157ce524c93136fcd524c931157ce424c931367cd424c931007d7714c931025de714c931025dc714c931007d4714c931025d4714c931025de73cc531026df63cc53135f7754cc53135f7554cc531025f673cc531026f763cc531027d763cc531186f662cc531186f462cc5310b7d732cc531007d532cc531004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d813100cfe72d8131004fd72d813100cfc72d8131006fb60981310057f75581311657c7558131005bf745813115dbc7458131005ef7258131155ec7258131006f96018131004ff751813101cfe7518131004fd751813101cfc7518131004ff7418131014fe7418131004fd7418131014fc74181310067f54181310067d541813100cfe7218131004fd721813100cfc7218131006df3218131006dd3218131216de3118131216dc3118131004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc74588310067f54588310067d5458831006de4358831006dd4358831026ef7258831136ee5258831006ed5258831136ee4258831006ed42588310b6ef32588310b6ec3258831024fc7158831026f47158831024f47158831026df3158831026dd3158831136f72158831026ee2158831026ec2158831026f42158831004ff7058831004fc7058831136ef2058831184ff764c8310057f754c8311457c754c831186de634c8310b7cc324c831005f7714c831025f4714c831025f7764c431006f7764c431004f7764c43135777544c43135775544c431025f7734c431027d7734c4310b6f6634c431027d6634c4310b7d6534c43134fd5534c431135f6724c431135f4724c431347d6324c4310b7d4324c431004ff759803101cfe7598031004fd759803101cfc7598031004ff7498031014fe7498031004fd7498031014fc74980310067f54980310067d549803100cfe7298031004fd729803100cfc7298031026fa7098031006fa5098031006f
  | 17 => 0x1cfc7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331024fc7358331004ff725833100cfe725833100cfc72583310b6fb30583310b6f830583310067f74596310047f74596310067e74596310067d74596310047d74596310067c745963117e7f735963117e7e73596310067d735963117e7c73596310067f43596310067e43596310067d43596310067c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067d42596310067c42596310067e32596310067c32596310267f71596310267e71596310267d71596310267c71596310267f41596310267e41596310267d41596310267c41596310267f31596310267e31596310267d31596310267c31596310267f21596310267e21596310267d21596310267c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067e40596310067d40596310067c40596310067f20596310067c20596310267f10596310267e10596310267d10596310267c1059631004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a310067f5458a310067d5458a31006de4358a31006dd4358a31026ef7258a3116eee3258a31024fc7158a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a31004fc7058a31154fd76cca311ae7e65cca310067d65cca3100cff764ca310057f754ca3117d7c754ca3119e7e654ca310067d654ca3100eee624ca31006ed624ca3116fcc324ca31005f7714ca31025f4714ca31025f576cc6310b6f576cc6310277665cc6310277565cc63138f7754cc63138f7554cc631027d673cc6310b7d653cc631387d553cc631186f662cc631026f462cc631004ff759823101cfe7598231004fd759823101cfc7598231004ff7498231014fe7498231004fd7498231014fc74982310067f54982310067d549823100cfe7298231004fd729823100cfc7298231026fa7098231006fb4098231006f84098231026fb1098231026f81098231004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231006de4358231006dd4358231004ff725823100cfe725823100cfc7258231026fb7058231006fb4058231006f84058231026fb1058231026f8105823100cfe76d8931156ee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d8931024fd73d8931006ef52d8931156ec52d8931156ee42d8931006ed42d8931156ee32d8931156ef21d8931004fe70d8931004fd70d
  | 18 => 0x64018532006f54018532006f44018532136f72018532136f62018532136f52018532136f420185320067f65d81320067c65d8132006f761d8132006f461d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d8132106dd73d8132006de43d8132006dd43d8132106ee42d8132006ed42d8132024fe71d8132004fd71d8132006fb40d8132006f840d8132106fa20d813219d7e75981320057d75981320067f65981320067c6598132005f67198132005f57198132006f76198132006f46198132006fb60981320057f755813219d7c75581320067f65581320067c6558132005bf7458132195bc7458132005f77158132005f47158132006f76158132006f461581320067f65181320067c6518132006f76118132006f46118132006f96018132004ff751813201cfe7518132004fd751813201cfc7518132004ff7418132014fe7418132004fd7418132014fc74181320067f54181320067d5418132024fe7118132004fd7118132006fb4018132006f840181320aef9201813200cff7658b310b6ec6258b31025f47158b31187e72158b31004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b310067f5458b310067d5458b31024fc7358b31186ee5258b31006ed5258b31186ee4258b31006ed4258b310b6ef3258b310b6ec3258b31186f77158b31186ef2158b31186f72158b31186f42158b31004ff7058b31004fc7058b31186ec2058b31025dd76ccb3100edd76ccb31024dd76ccb310b6df65ccb313aedd65ccb310b6df64ccb313a6dd64ccb313a75f54ccb313a75d54ccb3100ede62ccb310b7ce62ccb310b7cd62ccb3100edc62ccb31025de71ccb310b7d671ccb310b7d571ccb31025dc71ccb31187d721ccb31187d421ccb31134ff764cb310057f754cb3118d7c754cb31185f7714cb31025f4714cb31005df764cb31136df764cb310075f754cb3139f5c754cb3139edf654cb3139edd654cb31396df644cb31396dd644cb313975f544cb313975d544cb310b7cf724cb3100ede624cb3100edc624cb31187ce524cb3139fcd524cb31187ce424cb31397cd424cb31187d7714cb31025de714cb31025dc714cb31007d4714cb31025d4714cb31187d7214cb31187d4214cb310b6fb6098331004ff759833101cfe7598331004fd759833101cfc7598331004ff7498331014fe7498331004fd7498331014fc74983310067f54983310067d5498331024fe739833100cfe7298331004fd729833100cfc7298331006df3298331006dd329833121ede319833121edc31983310b6fb30983310b6f830983310b6f86058331004ff755833101cfe7558331004fd7558331
  | 19 => 0x85320077465d85320067465d8532006f764d8532006f664d8532006f564d8532006f464d85320077754d85320077554d8532187d773d8532007d653d8532007d553d8532007d643d8532007d543d8532187e652d8532007e552d8532187e642d8532007e542d8532007e732d8532187d632d8532187d432d8532187e432d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d85320067754d8532006f654d8532006f554d85320067554d8532006f454d8532186f773d8532186f573d8532006f753d8532006f653d8532006f553d8532006f453d8532006f743d8532006f643d8532006f543d8532006f443d8532186f772d8532186f672d8532186f472d8532186f752d8532186f652d8532186f552d8532186f452d8532186f742d8532186f642d8532186f542d8532186f442d8532186f732d8532186f632d8532186f432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f650d8532006f550d8532006f450d8532006f740d8532006f640d8532006f540d8532006f440d8532186f720d8532186f620d8532186f520d8532186f420d853219d7e75985320057d75985320067f65985320067c6598532006f761985320057f755853219d7c75585320067f65585320067c65585320067f65185320067c6518532026f66118532006f56118532185f67618532006f67618532006f76518532007776518532006776518532006f66518532006f56518532006f46518532007746518532006746518532006f76418532006f66418532006f56418532006f46418532007775418532007755418532137d57318532007d65318532007d55318532007d64318532007d54318532137e65218532007e55218532137e64218532007e54218532007e73218532137d63218532137d43218532137e43218532026f77518532026f67518532026f57518532026f47518532026f77418532026f67418532026f57418532026f47418532006f75418532006775418532006f65418532006f55418532006755418532006f45418532026f77318532026f57318532026d57318532006f75318532006f65318532006f55318532006f45318532006f74318532006f64318532006d64318532006f54318532006d54318532006f44318532026f77218532026f67218532026f47218532136f75218532136f65218532136f55218532136f45218532136f74218532136f64218532136e64218532136f54218532006e54218532136f44218532136f73218532136f63218532136f53218532136f43218532026f77018532026f67018532026f57018532026f47018532006f75018532006f65018532006f55018532006f45018532006f74018532006f
  | 20 => 0x67d545873200cfc73587320b6f731587320b6f43158732156f62158732004ff7058732004fc70587320b6fb6098332004ff759833201cfe7598332004fd759833201cfc7598332004ff7498332014fe7498332004fd7498332014fc74983320067f54983320067d549833200cfe7398332024fe7198332004fd71983320b6fb30983320b6f830983320f6f920983320057f75583321ad7c7558332005bf74583321a5bc74583320b6f86058332004ff75583320067f75583320047f755833201cfe7558332004fd755833201cfc75583320067c755833201c7c7558332004ff7458332006bf7458332004bf7458332014fe7458332004fd7458332014fc7458332006bc7458332014bc74583320067f54583320067d545833200cfc73583320dedc7358332006de4358332006dd4358332004ff7158332024fc71583320b6fb30583320b6f830583320defa20583323dd7e76d953219e7e76d953201c7e76d95320057f74d95320057d74d95320067f64d95320067e64d95320067d64d95320067c64d95323d75f73d95323d75c73d95320075e43d95320075d43d95320076f72d95323d76c72d95323d76e42d95320076d42d95323d75e32d95323d75c32d95323d76c32d95320067f74d95320047f74d95320067e74d95320067d74d95320047d74d95320067c74d95323d67f73d953219e7e73d95323d67d73d95323d67c73d95320067f43d95320067e43d95320067d43d95320067c43d95323d67f72d95323d67e72d95323d67d72d95323d67c72d95323d67f42d95323d67e42d95323d67d42d95323d67c42d95323d67f32d95323d67e32d95323d67d32d95323d67c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d95323d67f21d95323d67e21d95323d67d21d95323d67c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d95323d67f20d95323d67e20d95323d67d20d95323d67c20d95320b5ef75cc9323cded75cc9320076f65cc9323bf6c65cc9320b5ef74cc9323c5ed74cc9323b76f54cc9323b76d54cc93200dee73cc93200fce73cc93200eef63cc93200fcf63cc9320b7ce53cc9323bfcd53cc9320b7ce43cc9323b7cd43cc9320067f65d85320067c65d8532004ff75d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d85320067f54d85320067d54d8532006f751d8532006f651d8532006f551d8532006f451d8532006f741d8532006f641d8532006f541d8532006f441d8532186f621d8532004fe70d8532004fd70d8532006f765d85320077765d85320067765d8532006f665d8532006f565d8532006f465d
  | 21 => 0x40040050020000004002000001400a00100000340000000000000002000000002c000002000001000c003002001400a003001000800a002000001800400200280040020010000010004001002002400000a000000c0040020010000012001000800c00200000000100020060000000000006000800000c006000800800600000380000000000030030000000000001000c001002001800000100000240360000050024008000001001800200000080000040030070038002003001000000400000000040100000000000004004002000000200000000080120000048000000002004801401e002002001800000100000000020020088008004000001000001a0000000004002001001000400000800000000040000000000002001000000400e0060010010008007000000c0000030038038004005000800c0020000000000000001000800000000a0000000000007000800000000000000000000050000004002009000000000400a00080000060020010000004003000801c00c002000001000000a001004800200300200040000100010004006001000800000e005000001800400500080080020010008004006007000002400e0010030004004000001800c000000000801000e002002000800c01000080000000030010014002001001800c0040000028000000000001800400000a00000040000010018004000005000001c01400400080000060010018004006000000800000400400000240040000000000000000000800400a0060038000012000001001c000003000001400a0000010004000006002800000a000000000400200000380040040020008000000002002000000200600000300020000070004012000000000000400000280080040000008000000000001804400000e000001002000600480200020000000000000000000000000200100080040000000008010004004001000400000600000000100040000000006001001800000000200000000000010008008006000003000000600000080000140030000010006003002000001200000680000040050008000000001004000800400200000100040090068004002001000001000000500100000000080000010004000000801000600000080000000040008014000000000800401a000000000000200000000000000020000008010003000000400200200000080060000008004002000001000000000300300100100140008010004000000002000e0010038000000006002802800600000000000100040000010008006000801000000400180000000011ad7e75987320057d75987320b6f76198732026f461987320b6f46158732004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732014fe7458732004fd7458732014fc74587320067f5458732
  | 22 => 0x1a520000002a04f98000000000a0080000000000000000000000e00800300000180040008004000002000800c00400100280040000010020000002004004000800600900080080000020000018000000000000000c0040010000000000005800000c000001000c00800c000000400a0030008018000002007800400200c000800000000d0008000000000001000800600100100280000000008000002000000001000000000080000040020048008000000002801000800200080000000070058000010001000800000000100000000000030010004002003001000c008001002800400e00600000080020000030000000001004801c000000000000000000000380080000000000014008000002800800200500000000020030000004000000000001000600000480000000000000010000007000001000000100200000020030018000000000001000400e00000180040020000000000006000000000400200d000000c000000000000c00000d0000008010004001000400000400000080020020008008000003000001c008001000800000000000000140020040028010000002000800c0120000040000000002000800000000500000680020020000030004006000800c008008000001800e004001004800000a0020004000003000800000400100000000000080020000002003000800c0040070018004008000000801000000400000000000080010008004003001001400000300580040080020008000004000001801800000800300040000000078010002000001800000e00600000080080020000018016002000001800800000000000060000000004006000000001800600000000240000010008000000003000000000400000000240000000000004014000000800000000300080040000010018000000000000000000200400100040020060010004000000000800c002005002001000a001001000000a00600200080000070008000004000000800800c006000001400400200100000000000000008002000000801401000000100100000000000010016004000000c000000000000001800a0008004002000003000000c0010010014000001000801c006001002000c00c00600000000000070010000000000001000400000900000140000020008000000002000000400000a00100040020060008000004000000800000400d000000000e000000000002400100180000000000010004026003002001400600a000800c000000000000000200000100040080000040000022000000001000000500100600000000000008006007001800000000c00100080000000000000006004000800000000100100040020020000008000001000801000a0030010010002002003002800c0000008018012001000001400000100000
  | 23 => 0x3e94470000000beb6d7865c00016830b28cc0000003ef80000002b60002f6043200e2c4800161ebb5000184c1c000013c89d90b249400007a80001e06011c5c0003e2126184080e9f73300b7402800011e0000f06c0b61d9bf19264e10b3a194000b7a244980c00000014e800000036345b861c000001000000041c0005dea59994e0000000000fc8bca353000000000000035e400072b49f0000000000637800000000000000016a6cce00000000000003bd92e9212000123800179c0001431e7141ad541a700009927611a0000155e7c10002c208c40004d79294c90b740002c78000b8358aa80924ac8525b00dc85200000022540009c00a280019960002da973d4b200000033dc00000000020380000004ee89a80009e80002bdc0040c84e316c4000000000000000000000034ed75881d68f9b809a00000a680011700a10002ebc00000005900011b6c9f0449bb11821dd0d2a23c86aa3a311974ce141210a7224885c89f00007f00008830003054a9032d00000000000000f09fec0006f700000007ec45800000001a878e00035b954ea911da1ba0a541e73440bd531e9b623200000007f11dea1b01e2000481000000000051b9a6c0f00003af00013be0000da8000000ce60002f2ccbc6974e497c031400027e06f416c1c255900006420000bf87300001575d914856c600030a80001d6a6a65a8741abac5e19c06500000002cf33d40000000001aecfae000000000000000000000018680000001c8999406254280018f2ca3000281400000000003840000004009ccc00000000000014b4000000375800018e6d10000f8eb9d598b274cfad52000000110464b0001de931c57700010b017c0004b427e19a24406f233643020002599d6469633749e800050600058d850000077f58b108d19e2d45a935800008353d100000002ca0000e49c181d467100000000000000000194000167000072c6c8000193000090d0002d5c8d658f0000000000000512837489000000000004e80940001b980005ff00000000ba8d96f6b2e90e00e30dc8391a88c256b324613763cf4e72fcd9182fa0001eb0322190000000000000000b800000058c5c58de99d06f209591483caa6258e125946a00000000000007872220ef82de58819f800000036d2a80a9508a0005bc80000000002f680015767e50002ad58f80003bb8021b125c846031b800080a0628e68dde55300000005a41a645400000004e70001e240004ec5f6977990c000437a0602c2000000346c00057021f0001b6812865b80000000000000001a865be58c000000005c0000000a060005402cd457a3850001acd6741ee00016606be9c814b9d4ccd671f2bf9f100006a24b682fcd7a4200000000632000409033c000b326fb850da2e45500020ad6929903a4b58415a000000076c0
  | 24 => 0xbae31b10d08c6a3228b281d4aa00026400000001fa1dda9f988e75d00029c9b8a49d0a880001f211e398368130493b00000005dec7400035d93e45f8059b1a400070900023e0b5c4282970000000000035800158c1d80000cf98969a30000001a2a63c27d80000006024d380000000000000000000b2a0000c54000000698951c0000006d923f000000016c800000000045f370c000000000000069000020821e800000000000000000000001fe5ae4000016acc1972c7747a9f0c0005b20000000000584490a6340000003ea000000000000024e8ee80001ee18e555c4424e136400001540a9800079293c00008e000000000000000000000001494a48000000000185a00023e0a84d9ab6a03210d8a5e4ad42e99586d200039a9d20000000003800000043a46f00017ea000000000000043200000009da5cd25e29c56580005c2370948e0000000000d7801e00020780003b600000000004ac0002158800000541800000000062b0000000ab71bc9ac94ea0000000001862d326ca0aa892a6d301f8001076aeb018b0a43c83c500028f8000a1c2aa3281bba00000000004200760002528a9e0000000000ca2b106a380019800002791fe13ce7a93bb34040000d900020500000000000001a949656f38d645220000002a3c0009c76db80005f600020f9df5b900005c928a57b2dda2b794e14da0000000001554000000209400000047900000000854691ce44a2000000311962800028100012a400000034f000000000000000007f3553030900e61a00037e92d85d5000244000000000000004c600000000016000004fe1150000000000000005cb481009c48000b040002ad17fa00014a8d7400000036880000000006ce00000000000f580017a6c9a00000011020000000001afe53e00001800000004a7af84cd000000001a40003c33861231b947a5196000159a00044c00000002f7000000000000000032ac00000026fa2c40009e200017c501eb060000000000000000352ca36ac85a336543d0b85398b3809688d8631369c000d165c9ae1937400053b29ac0001040028001748d8700000002c824400008fc0009260002f75798000000000000000056c19401007623f300018840001d58000000a7400030816f800019b1764000d3700016ccbfaa13428a78593cb175b1000000000066f00005faaef1ce1674d1abbf3ed16a14bc2db5c113690366840002354c820003de800013abe50000000c3e000498000000000000000010820000002e8c000d2465f00015106db00017100000000001d95bc00000000000132000457195c0000000000001424bab31221dc000465630084c5c035e4761df074200014b0001046af93b9800000065f0000528000d86000280d29000061300007e822d4b70d3c000000143800107e00000000006089b40
  | 25 => 0xef8000000000343800000000040480000000a23140000000d5056086f800000038a800000000044e8000000000000000051a3550000000000000000000110c021667800000000000010e50dc81a000200800000048c80000609fb000000187a64060a23380003f2000167d20a0000000000b780002ea000000000000002400000000000cf56a80000002ea1618b4f5170998000b9828586dc000a56129254c838dc7089b3c8000db940f80000006b7000000034848800000018b4b0500000018ce93f28ea3d97eca694fa80485e4000181800000061c63f8000c0e0000002cac00000000000000000002a0a40c000000000000000000022980000f200000000000e00000002e9c0004dd00007f9b884c062818e800059200035ac000000000000000000000000015b400000000000006fb0001d517dc87e67213a0000c0609306a02280000000e0c0000005789f700000000000d186e600015580000009ed0000aec00053b000027000000000000000000000000001be600000000002606860000ea800061456b000000000000006bc00053647b800176c2400df99501482454ac1c44c580db4a334d00006ce11d000000000060c0000b0a29e0000985b7a0001ab0c880007c80000000000b240e290bc000cb6000000000000000023b80000000a0ac6567000000009819c600000000000000000001668000000424308c000c0c00017400000000000000000000300a78c56870737cb1913600002b4250d53e00025880014aebb73dd0fac000000000000000000000000015f60000000000000000000000198e7024ae06c0000341173800000094c36c0000000def00000000000004fb32a4e68000470178c1048900faa8ed4580000002d14fd80000000000000cf3206a411a920001c58b0c000000000000000092257000015a61703c28000e2c00000020f145aa7f4801cb55a400000000000004af3100000000000000000000000000034500000004ea00000000000000000000df56268fe000045c2af187952c000607800040e0005cdabc80004cb26e35c4000306000000099c00036e2f400fa05a2f0000004c00000009c40000001bc00012102b006000003aa00018080016fc000000000082e1d20000001950d8b00000000005200233724eb4c491e71f8523cdcd00032040000003c2249000000025a8db80008f15498000cc80001258a9912200000000000005272c891654428cc6319724a1c0000000000be49a40002bd90200fc0000000000019000000000007341700000000000000000000000000000000000032680000008200002ed0000cda2e180017ce6c11340001a0c10900001140000000000000000c89046800091a3db6f1972c2f65990ad814dab6c541cc31305a003e43a05640009ac571a5a49ca73706f996800081734726d4
  | 26 => 0x40000001983144000a1600000000000000000000ec80003de00003a2000619b3a9116d98000000036870852523d0e205dc26780012408ed00488d5bcc0000001b68000ca26640000178d4e42c2a3800018c5ed93e5732b9643913e95660001040718a929c53ce8000000af32633578000a660000000b2a69e000000000000046f86800000a35b38c2c0000003f7800000000042800000000cc000000107c0004f701b000000000015840009910000000c30b3721217d955294b4e0b7b957c91f0d5856152e9b1676304d6469ec0002ee80004fd2a21b3d8120000000b3c0000c605a800000039700000000003134ba980000015e000000000038215d34b426cd1d0f4a35d3fabc800000000000003962fb000000000000019d62c4000000000038c0001f8c1d201d5b7029c3c60003f3a22800000063309a4c7ad124210000c3a0ce3b794ac916d0b0001a756f06c668180000000000001ed84520000251908000c0e0001e21754d286de17150c62ad0ff90686ea2185c880000009d7000135c0000000001280e0631a444a2c99ae000000000000032925f00000000000001758000000000000000058e327a8881501f62e8875d0c0a9255f94c85f00004de80003a60000000000b1abd44a700d0000cc138d05cd72ea9551594c51a0a4300000000000000000000000c170002ae40000c100000000008e80000000000d2e00001ec000d6364d8000000ddb000288cb26bb346b35b189000000006b80008f300d0000000000176800000025b4ad00017b400065880000000000000000b7e0003cd00015160a538a00006fa00000000019f6a6741c0894000000000000027216561f07dc62000059c8e642be8a700007e1b2c6a36488dc056604800000005a25c20000000bd60005e080009040b72ca04040003fa0000000000ae23060a306a8000253000105800011122a4e1ed2500009750260002c180003420003eb000000076b25580009200000000000e8e66a00000013f48d35f50000000000000000154095500008cd6e47194111ac4f9402900000000008bd0000d980003bc67a17185701b623f072400000039316ac000000323131c0000002340000e540003720000000000000000124ec6c00032106fc837000000000014b62500000000000000000000cdd0882e216860005e38000000df900020347dc6f36ea2270666a200000f9dbd87902a88000000000000000000063302080000000000000000000000000377cae800022d8000e8ccbc0001309a740003d5b5140000000000000b9809105a16840000000000668000655000000000000058fab700009bf0000e3c00092e6930b1da6ca6300030480004040c434e411000000008840008e60000000cdc31c32eac4c000000000000000000053700000000004f580000008ef000000064c000
  | 27 => 0xb06986541621960002c8440c00048e12a80008f00bb344c9d6000000047db2e72407d000000056c5b00001b06000000000091ed5101781d4000000635b69852635b4020000e9e00064780a821e000494800000000037f1da191c0f40002e84000119000000000000000018d00006302c11b2400000024380000640001e325dc0000004b0800000067161400004227b70001ea80000006bf1bb400000000000000000005ac9fc80008270001e657e20002ba800000020524f0000b164d640890551c23a505cb5f59d29471b38b90a321790bc0a7ca26bbc00009f00000000000000eaedaa0000fc012a5e2000000000000059e2f140001d96158a2867600001000002e80002408c9101071d1a916802367752f7006195c0f608e12901b01ca07ba8607a044e322a9f09a442a3d801445be3fc0001ae47400006802830c52c82202a7c0d680000001a7cae60ff00032ec000000000000000095b19c80000a000037ab2700000000000000bee80b00036300000000001ce12fa0000138000dc6b2706800017760002fd262400000000000a000049800021e1b22ba26ad01540987e000034a8000a6800000000006580001d2c0000005a3a558a38b9a302af8143e0005689ee0000cdf17280013063a621325040008ea3b60000d20000344a2305903601c80a607c29285420000c70000000353d7fc6ad1a2b17c000ba60000000a0e0000000000000ade000000000000000004940009166f8111c0a8b120000000000000620b4cc000000588821c0000000000000fb600013f947c000af00000001c1000028000000002811a500000000000000001300000209a1680007954d512a4c6e5421d7022912c9b3000000000035a0001ed06220005ca0000244db81491388f02c440000e792c05e517618291cac1d34b0ff800000041d0001bc20002cb8810066caf594a9b1b1c88812080014b85ac1231d708eeadd00015f44a000000000000000630000001b9e2540002be11f2000000000113c0003a18000000559000262c04a00000000000004cc00007ccea20004cb000161684e27b8000dec0e228ab701a183cb2ab90040003ef225810c5e2bfc0000000c2e0000003240000bc9000350431e00000006751743ec1918158ffe00000013f8000b0100e000075e4a80003020bccd7749584e8000b2f0001e3d8a43b90000001196000135b4100008d100025e400006f4510000000000000150dba0e0900025910f62580001a490ec9404d90a416408ab0000414df40000000d60aaa2af1bb80000000000221ab00005290000000000cb32db8000000bcf00000000a4000000000000010300000012f800004d9cf0a66cd223997614e0c3900008f422cc210002c1d2e884b6fe08580746850800000000000000226c00000000000000003641e9b39da307c92fe232
  | 28 => 0x704ac00006180000000000001344c6a1ac000210c00054a00000000000000000ac4000d650a42ec4000149000301c25cbc200000000000000002ffc00070d66680000000000000000f4c0aa15f8e1d4026992f404ddaf84180000000ada8000000000000558483000000000000000000000005528b247220006850000f3c000000279588046e0002e340005ba00036a01a4b8c30400000000000b51cd98c21cf39f13644dc9b857080017d2a4f0001d414c00000000000000000355811c82418500006187da0000000000000c8d0001fa484473a6df94a169c0003151b75be8a7d033100c000c5d2fd80003c47a40000000000000661b5c00008a56ea98242a40003dd800000000050a28440005c000034255d2000000348800000036c8000000a4800019c147e0163d8899d0a4dd84e680000c20f00000000e84e0a02c00000000000000000e82d3f5adb0040008af0000000e8a000638800081c97357e0e5459a30a3419cfc8f0a512a28710af4a5861211d00002022518000d1e2e11d1000000000033620f5a700003fbacd12180006152d0400000029e089800000061d00018fc00057f80000000006ba321d7400ed1df90082308331f2abb0e9a31247d886d6c200037880000006c40002fa022e5ef000000115a4e40a1339591000000000000000006c20000972a2f15608692f43742fa958c000000000000198448366b325026adb540b000000000000000000000230f3000012c13c0001f898aa000000000000038a16124040000006f52b6c5e66a700020d00003b25618000000a1e1fd80000000000000000000a6100000000000002b31548b6859b4ca35594827ce6780000000cdc06f06e800005e0001cc800017e0838000a60604323b628000214000023d0ae000000000133aa1d0738a382e203c0340445a9abde0c900d40000000000d1122e97f6ba800000045e000000130a00000000000000000000000000b95000000000068c47f0000000b892af800027c0000b584fc000ae80000c394ca27747d0000000c050000000000000000000000000000000000000000002688252000361ac0800056000030f00007eb00008c000000000022806360002c82d3000000015f0e1953600000000003de2a954380003460004149e18a8c9dc587310c000000000364974a000489000000000055124b000000000000000004d36842eb408000031900000006530000000000000132285dad40003a936940006220b68ffc288000499230c63e000658177c5ec0060b70ed40e22fe52a000000043c56800005fe7941311f553e85e1307000000000059f0000000d690081ae1194df16f400015043e85fd80014c8000522b26000000000025080000000be0f991fad8f0000854e989f94e183b1b3ccd4503212843e0000001ff106c0000002da401e04
  | 29 => 0x9e0938b000003d23f424d000008e46a0e3858c00000000000003e462e16a49862bc1c200012460003682389b3264467789f40002ea00a80000000003908b58000bd71060a1116c0841a61600d3800029b8001338cd33aaa2d42685c11e500000000001b78a0134c0000000000000a3d2bc80018066ee1eb0e24dc22b736a9d280001552490edc0002c1000000007268100020b400000023014e92140003fb2ad80000000002f01272b770002c343fa0004f5000122647b0003034000000000000001a0000000000ee400018393fd906000000000128a5ca03f18c55ae8c600000015fc6c70002541b9cb2515201f06d824200000001aa80c4c3800000000002d937877475b00000013a667c47180000000000000000f963200001419bb80000000000000c45446a8997a40000000f74000727000139905e00000000000000000000000000000000000194cdae000000000000000037f4000a9d00000012de2fc0000000000ce1474800000000023c9c7000022a3b808ec63c9b91ed02e00000005dc800000000023913cca4400000010ad5c89db4d71fe8000b2e2840001594000000304130c80551c800121661b33fa8280000001ec8000ad200038091740000000000001b7c9842b200000004a1000000098800055421fc0004b700016c02b40000f609c000000004c000000000000000000000000000000000aba000296d2f60005269c8000000000000008360005a20001534d584ca800000070e0001e5890a0c40000368ebe10854a21a40000000000000000000000175c82c66500000000000fd487b4696e00000000000de800064500000005726b9859800000000001080b235700000007f29365e300004ea00029a2fe8486000000000000019e227a16c0000000000000124cee61780000000002f6198800000013685818d403d000144436450d124883400000050a843889215d0000000000000000000114c00070000017de5f428615e0000000205b7a4d98000000000000000000013b84f0000000000000025c613800000000000012ec0006d200019d4000000000272d4328392d300000004e0000258c00073d0000000000c920000000000000000019db820003d009ccb46ac54cda83c29862d5f1aa8c00022f00000000000005b20000ed4ccc5c816885bc68b3c6b2e00000006f280016a20000b18588000a044b810455583023251e44a1e67e000215428c00039280000000000000fc546826c639b2b0000c0400000000000003500268000ca533a122817a34900000000000cd545000009c00000027bd98a07a21ea2d00001cb000375c000bbe0c49de1abe8030000000118272000000141ca867028a9c0000000000001530a905a0245525a0001ebb5700000002de9eb40006ea0003341a6a6f83c5b36c0007f51a9800051618300016
  | 30 => 0xb0a000000000000000000000000000002824000000091b5ec000c9900037ec0000000000000e0000000029cc00000000037d80009713b3381d6e2000000000000026f00000000009ad0000875a8400044200014620000000c6065425e00000016fa00006380000000000000e757605716fc19980005090ef2b39a3c99205011fc88c6935ea80000009970000000a305af4e600005e000000015349e00000002dcd0b878062c33d8000000000255000000015c853d34243b1c080000008b000000000000006a400000000002d280017f200027500012ce00000000000005fe0000000ceeced0000000e3000000000000000004ed000000025500000006e20000000000472b8125e800000057600034f51c800002b98bc0000000e6abf5bfebe46cd2265adee0b1802a78000972000000000024a5b5b470000000000129c0000005ad0000000000000000000092a000000000000000000002140000002510000c3800000006ca3e0475ad5591676014db5a17b80004248ee013e00000000000000000000000000ac41d98bd000000000008b00000005230000dbea5d00000018caab100000000003f300000000000003ef14b00000003cd80000007d91659569262586233a1188d260d20e9ebccb256a2f493d463a5a420f0e4c0000e85f300017ac00050836e800094d0c98000b6cc6829a8d0800012c00000014f60000001d38000c3000000000000005151ea157a29c5e20b687361bb0e0000000000034a2764ec600000000006feb6563812707a89b7520000000000000022e400060b00021cc00000000000000000000002cf486263f3c500000004e300000000003f7000000195a0003f50f7d44e9d80000000dfa00003fa2a800000000033c4ffc00000000003b800000000000000004c080004ae0003b3a0a17a2000000364dab2e010002b7d2a20001f515746689e66ef1a60dced053f80f204165e736a2cd92700ae0000c9c000000000000000000028500000007ee522000000037c0000000cf0d1000000000005b95e1800000000000000010d60005b68000d847b93248000f3000042a2574ef263b0001f153d20114638001340a4c3d980888120003c11f3c0000000f680000000000000ea4000b3b0000000700000000282c0000000000ba400000000026acc4ad8238f255c5ae6af3758d1c390847565a4447801b833095f08ecad500000000008da64a80000009d20418000000000000294c00000048d1db886e05f1ae00016b0c2c14a000000000000003241cc0002d68000f42acf0000000a0aa003cb85418ec000000000000000044a2fdc84e376690000000000064b8ab97521c35280000248000000372c000dab25119e4dc4a1b1268b719f4562097800093e29a6298e20f8c2f96648000000c003548d8983e66700000010bc9
  | 31 => 0x3e02ac0bb68a40d68cd497e0132ad94e40000000001e48000d9d00000000e400000000000006a4000000000071b0578001bb284461b8000000000309000122800000015ec00096b23a869c27033c39d8da0424aee6888a814f42cc67c00000000001ca00010cc7a703a0000f269e4000000000000000032d16d0b4b0000001556d67000198d31812d2050c940000006a000000000004e20000000ab83fa0000dd222800006f1448b1d0e0800000097e5b780ac000000000000000000000011847887ed4bb135000089a42980000000f326280000000003489df8ffa00032e00ecd8042d111a6692922656d685dc0006274312e3d49c00000000e0c560004c991e951800000020543521aa436800000039f42780000009d56938000000000000000041200000000009e2000702368da4200000003d42348a1000000104c1330000000000c3643384c800000010f000000006e1e6000173c9780001af800000014798f968400022f8000c32182000000067403600000000000000000001ac899f43500017002d8000029813c0000000000000d3e0000ea0f46d07000035c0002e80001131578000000145c33000061aa13400056e60d8001b0000000f8000d4a0000001f0800000000036218b69a9238800000000000000000005017018000a244976089ef84483d8000160487e13b12710c16be0e544b800010200010b80000000ab00026f0b141fb00013a4000b560001134a8000000010e00000005378000000000000343592c0002e3862c4b20000001afd9aa51a000000091c00000000017e46731d800000000b048eaa25a5e6a81e8a7816ec09763e8c30c4cb501978000a962034f89bc134a0000001211c1a5676d8071c00006d55680011ce000000000000046a3e997a94606433a00000000c78089000000000036ba1a04bed2c6d0a2b00000002e93749038af500000006a0d570001c2c5101f100000019480000002130000000000000056a314466a92c03610600000000002360000000000c2e5bd80000002d30c036046569ca35d0eb5af0000000307800082441924dce0c00000000000007cd3ec373000072e00003b800085f0000000c0c37b3ac21f40004d857a0030000aea00000000001f03509ab858a2b21c680017becff0000000cde00044980016fe0001d8800000072800000000008c52ed2b98d9620065fa6f977017526ab51866204f1e38f34000d190000000a460005b61938000466026b1b4000000000000000010d1b50a88218b5c0000000000cfc2030001a040776aa8c2045c0000000870b2c0d1001aa853bc0002288001bfcb2858d0f0531496200029e4000a3c00000018f40006958000000b5d00000000008ff0002308000000000000000012a000000179a00018b00000000000002c24e5242500029257f00000d98
  | 32 => 0x80000ca00a68799a400051e1052bb4a7eda42668000000351627a46c0004331541b78000d530000a244fc00055214400000006c68000000dd30000000e2600033d051c00066d5912b096bc90700037c8f6a0000002e280000000002a340000000eb15581745144af000126a00000005e80006805c39f74000b9f61f91f55f40004cc910400065b5ce05c8982000127b3603440f2000000000090e00000010c8e0600000013fe0242400000ce4c0a000173823ab0307c0cc815830f24da6a092625a41500000000000000000a5a00034a86349640000c234380005e44f9800096000000033e42d200026d8000c428dd6b68000eac49100015f99fc00006e0f786d62a30001b59b0a0000000000a98dd100000000008404180000000ad438289ec00027a00000006e40006550000bf230d000103c0000005a680012b20006f5b5300000003b480006c20001a1800106210b14c80013a200040cab640000002ddb1380005870002d288e0000000000000000000036b01960931298b54000e021410c140000000000409b620002ae2c980006521101168eda988000000000046d0000000fa20000002a7000000000000000000000003058000ae50000000000000442a0181fcc5907505f565a00000010640000004cc00000000000002cfc00000000000000000000000000612c75000000050aa422040d3400000000032f4000cb200018b80000003c608ad17600027b0001146ac707d848000000000012e05cc4991d38000000328000001000042153b97cc00000029e800183800000015949f02481e1257c000bf4639000000054e0000f54e5e00000000003e84ca000000153200046227416ea0000000000000234000067c5c63a400035e815200000000003b40000003319b3608b00000b0f7e1f26e3000141000060d27f844e5a729328680000000000000000000024a73c0000002eeb201b521995f800000000000000000f5c00030780000000000001a687ea0000002f891b800052908dc828ac035b0bb888a00059986c40000000001a09b6613d000000017632e67eb4c01de50427796a810c0000000000000c5700022f00001f900011402b867b107b0c9bc48793a208c8000a360001bfc0008c80000eb0000a385c71a29942db643e08f80003fd382000000088700016e10ea00017580000000004b5348c00000008a8000000000000000000000027a367c0006aa221a2cc33819b6621b9400040c0000000cec0003e8115cd8a0d645f91588de0000000e8c0006b54401f480d42e2438800095c131000000000072330885b1844c196dd800039c3e336500000000002b580013ac31711880008d84866b129e00000000001e7c000b6600005595cec7b497a8a0d60acc00000015920000000000000000000000000000000000010c20004999128f64
  | 33 => 0x20840000000001268016a5f3b8
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xce876dc9204407d9d0edb124088002dc61471481101f6f1b90e29022045c7676d96104408bce6c1b2c20881132d9db648411021e6b3b6c70822016cd67618e104407d9ccedb142088007399d8628411000762318c5082207dc7710dd165040fd0fb0f3a2ca080030fdd274594100061fc22e8b28207ec77105d165040fb0fd0e3a2ca0800317dce73594100051f420e6b282000a3d841cd65040014dd0439aca080029b60873594100043f43e86b28200087d87d0d650400187ae9a1aca080030f5d143594100043f43886b28200087d8710d65040014dd0421aca080029b60843594100051f420e4b282000a3d841c965040014bd06392ca080029760c72594100043f43e84b28200087d87d09650400187ae9a12ca080030f5d142594100043f43884b28200087d8710965040014bd06212ca080029760c42594100043f43864b28200087d870c9650400147d08192ca080028f61032594103e53ac0ce0b28200787e87d0165040010fb0fa02ca080030f5d240594100253b40c80b282000a758190165040010fd0e202ca080021f61c40594100061eba080b282000a5e8310165040014bb06202ca080029ba08405941000536c1080b282004a768110165040014eb02202ca0801e1fa1f20594100043ec3e40b282000a3e84c81650400147b09902ca0800297a0f20594100052ec1e40b282004a768108165040014eb02102ca0800b0f9d15498c100061eba2a93182000e1d5450e63040010ff0ab94c60800e1f2157298c100246e43a86b182000e1d5450d63040091d90ea12c4080038b551425881001c3e42eec990200087f855d932040070f90abb264080c23de05764c8100247a40aec990200087d86dd532040010fd0eb2a64080021f21d654c8100263a38aca9902004cd47198d32040091b90eb1a6408013351c5634c8100247643ac49902000c7665dc532040018eacbb8a64080131d9c5658c0100266b38ac71802000c75655c630040070f90bbb260080761f61b754c0100043f43aca980200787c875953004001878e8b2a60080030f997744c0100061eb2ee89802004c767159430040018eacab8860080131d9c5658801002477c3ac51002000c75655c620040018e8ebbb220080032d1d376440100063bc2eec8802000c7485dd910040018eea9bb220080031d553764401000679286ec8802000cf150dd910040018eeedbaa20080029da1d65440101b53a43aca8802000a778459510040014eb08b2a20080038d1d165440100263bb82ca8802004e7370595100400196eedba220080038d59774440100066bbb6e68802000e5565dcd10040019aeec39a200800395594734401000673bb6e48802000e6565dc910040019ceec3922008003995947244010006e2398e48802000e71658c110040016e70a98220080039c5953044010
  | 1 => 0xec8aa0c4880038b1915418910006673b6c63122000e4f65d8c6244001c98cbb18c488003a3d93631891000746326c63122000e4f54d8c6244001c9aa9b18c488003b25c3631891000476c3cc63122000a6e8598c62440014db0b318c488002aba12631891000556c24c63122000ace8398c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488002b3a186318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d90631891000746320c63122000e4f5418c6244001c9aa8318c488003b25c063189100073232ca23122000ec46394462440015c90ca88c488003b118d511891000752324823122000ec46390462440015c90ca08c488003a919141189100076231a82312200087f855db32440070f90abb664880022fe1176cc9100145e422ed99220018dc835db32440070fd0bbb264880021f617764c9100145f426ec99220008bd84dd932440070fd0b3b264880021f616764c9100043fc2aec992200387c855d9324400117f08bb2648800a2f211764c9100046fc1aec99220008f7815d932440070f90a3b264880123d204764c9100043f436ea9922000c3c64dd532440f58d8c5baa64880021fa1f654c9100043e43eca9922045c7471d95324400187eebb2264880030f1d7644c9102265a38ec899220018de87d8d32440018beebb1a6488003171d7634c91021e6a38ec69922000c5f7518d32440018b8ea31a648810b351c4634c9100b47743ec49922000c6f75d8932440018d8ebb1264880fb391c7624c9100047b436e29922000c7765dc532440018e8cbb8a64880032dd93714c9100065a326e29922000cd463dc532440619c8c5b8a648805b3618e70cc5100b66a188ec98a2045e5431d9531440019b6c638262880033ad8870485100043fc2aec982200387c855d9304400117f08bb2608800a2f211764c11000477c12ec98220018ec825d930441010fd0dbaa60880030f193754c11000636316ea982200087e87d95304408b0f90fb2a60880030f1d3654c1103fc5f436e89822000c3f65dd13044001878cbba260880032b18b744c1100045f43ec898220448bc87d91304400187eebb2260880030f1d7644c1100062fbaec69822000c5c75d8d304400193ee9b1a6088003271d3634c11021e6a38ec69822000c5f7518d30440018b8ea31a608800327dd0634c1100064e3a0c69822000c6f75d8930440018d8ebb1260880032bdd3624c110006563a6c49822000ce462dc5304402d5b10c98060880039a18b658811000754316c91022000ec862d8e2044001d90c431c4088006baa1b6288110006753b6c51022042cd47118d204407d9c8e3b1240880033518f714811022e3c3b6ca9022000e6862d952044089970edb22408810f361db63481102166c3b0c69022001
  | 2 => 0xf65589100061e3a6cab12200087e871956244001878e832ac48800a2fa1b74589100061fb2ee8b122000c3c65dd16244001958c5ba2c4880022fa1f64589100061fbaec8b122000c3c75d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b122000ccc62dcd62440018beca39ac4880031719473589100064fb20e6b122000c9c641cd6244001998c439ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200387e87dd562440010fb09baac4880022fe1175589100145e422eab1220008df835d5624402d1b906baac4880023be0975589100043f438eab1220028be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c48800e1f21574589100046fc1ae8b1220168dc835d162440011df04ba2c4880022fa1c74589100061fba8e8b122000c3c751d162440010fd0faa2c48800e1f21f54589100061fba6a8b122002c3c74d5162440010fd0eaa2c4880021f21d54589100061fba2a8b122002c3c74551624402d1bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317d5373589100062eaa6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c5f541cd62440018baa839ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000cd473dc562440018dcedb28c4880029b613651891000734b86ca31220008ed8799462440014dd0b328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac84594624400159f06b28c488002b320d651891000537430ca3122000c6e7619462440014db08328c48800399604651891000735380ca3122000e6970194624400195cedb20c4880038bd9764189100071632ec83122000e2f85d906244001c590bb20c488003aa5c3641891000476c3cc83122000a6e8599062440014db0b320c488002aba1264189100056741cc83122000acd8399062440011df0eb20c4880029be1564189100053642ac83122000acf83590624400159906b20c4880029ba14641891000536c28c83122000aae86190624400195cec320c4880038bd94641891000716328c83122000e2e851906244001c5b0a320c488003a9604641891000755380c83122000ea97019062440014dd0daa0c4880029b21b5418910006373b6a83122000e2f64d506244001c58c9aa0c4880029ba19541891000536432a83122000c6e765506244001c5
  | 3 => 0x9b122002c3c7455362440015cb03a96c48800e3be1d52d89100053742e85b122000a6d85d0b6244001c5aa9a16c48800a3be1d42d891000716aa285b122000a6d84d97624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc8359762440014db0832ec4880039960465d891000717b2ec9b122000e2c65d936244001c5f0bb26c4880038b21764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000537428c9b122000a6d851936244001c5eca326c4880038b19464d891000717428c9b122000e2d851936244001d4b02326c4880029ba1b54d891000536436a9b122082c6e76d536244001c5ec9aa6c4880038b19354d891000537432a9b122000a6c8655362441038dcecaa6c4880038bd9154d891000716322a9b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000e4f54d8f6244001c9aa9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec48800393d5063d891000726aa0c7b122000e64659476244001d48c920ec488002aba1275d891000556c24ebb122000ace839d7624400159b073aec4880fab9a0475d891000572c08ebb122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce9b122000a6e851d362440014db0a3a6c4880fab9a0474d891000572c08e9b122000e2f549536244001c5f08aa6c4880038bdd154d8910007163a2a9b122000a6e85dcf62440014db0bb9ec488002b960773d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000727a9ca7b1220008ee8714f62440011db0e29ec488002aba1053d891000556c20a7b122000a6e85d0f62440014db0ba1ec4880038b55343d891000716aa287b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b1220008ee87d0762440011db0fa0ec4880029ba1741d891000536c2e83b122000ace83d07624400159b07a0ec4880029be1570d89100053642ae1b122000aaf845c3624400155908b86c488002b3e0d70d89100056641ae1b122000aae84d43624400155b09a86c4880fab9a0450d891000572c08a1b122000a6e85d0362440014db0ba06c4880038b55240d89100047743881b1220098ed8710362440014dd0a206c4880029b61440d891000716aa081b122000ace83103624400159b06206c4880fab9a0440d891000572c0881b12200387e86dd562440018d8c5baac4880021fa1
  | 4 => 0x34400199ee6392c688003391cb7158d100046fc3ac631a2000a5f8558c63440014b90ab18c688002a7e116318d100054e422c631a2000acf8258c634400159904b18c68805a3720d7518d100b46e41ae831a2002c3e74550634400187ae8aa0c68805b17dd75318d100052f42e8631a2000a5d85d0c6344001c3aa9a18c688003875514318d100043fc2ae431a200387c855c863440018bcedb28c688002976136518d100046ec3cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440018bcec328c688002976106518d100072ac08ca31a2000c9e76d906344001c3ecbb20c688003871976418d100070fc2ec831a2000e1c85d9063440011bb0f320c68800297a166418d100052ec2cc831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100052f428c831a2000a5d85190634400193cec320c68800387d946418d100070e328c831a2000e1e851906344001c3b0a320c688003a56046418d100052f436a831a2000a5c86d5063440018bcedaa0c68800387d935418d100070e326a831a2000a5e8655063440014b90caa0c688003179d95418d100070fb22a831a2000e1c6455063440014bd0b310c688002976166218d100054f424c431a2000a9d849886344001ca8cb288c688003a51924118d100b62fbacea31a2000a5e859d063440014bb0b3a0c688002976165418d100070faa4a831a2000e1f845506344001c3ce8aa0c688003875d15418d100052f428a831a2000a5f855c863440014b90ab90c688002b5e057218d102156b40ea431a2000ad581d48634402d1bd0e290c6880023761c5218d100054f420a431a2000a9d8414863440014bd0ba10c688002976174218d100070eaa68431a2042ad681d0863440015ab03a10c688003875514218d100b46f4388431a20008dd8710863440014bd0a210c688002976144218d100b46f43e8231a20008dd87d0463440014bd0ba08c688002976174118d10005674168231a2000acd82d0463440014bf0ab80c688002972157018d100054fc22e031a2000a9c845c0634400153d09a80c688002a76135018d102156b408a031a2000ad58114063440014bd0ba00c688002976174018d100070eaa48031a20168de8710063440011bb0e200c68800297a144018d100052ec288031a2000e1d54100634400159d04200c688002b36084018d102156b4088031a2000ad581100634402d1bd0f900c6880023761f2018d100052f42e4031a2000a5d85c80634400153d09900c688002a76132018d100052fc2a2031a2000a5c85440634400153f08880c688002a72111018d100061fba2a
  | 5 => 0x80029761742d8d100070eaa685b1a2000e1d5450b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b6344087caca3a8ec68800237a1f41d8d100046ec3e83b1a2000a5e85d0763440014bb0ba0ec688002b3a0b41d8d1000566c1683b1a2000a9e84d43634400153b09a86c68800396d4250d8d1021d6b408a1b1a2000ad58114363440014bd0ba06c6880029761740d8d100070eaa481b1a20008de8710363440011bb0e206c68800297a1440d8d100052ec2881b1a2000e1d54103634400159d04206c688002b360840d8d1021d6b40881b1a2000ad58110363440871bd0f906c6880023761f20d8d100052f42e41b1a2000a5d85c83634400153d09906c688002a761320d8d100b62e31aeb31a2000c3e74d9663440018dce5b2cc6880030f9d06598d1000637390cb31a2000c3f655d26344001878caba4c68805b2718d7498d100061f3aec931a2000c3d75d92634400195ce5b24c6880030f9d46498d100061eba8c931a2000cae7219263440018bcebb1cc688003175d76398d100064f3a6c731a2000c9d74d8e634400199ce5b1cc6880031bd957298d100063632ae531a2000caf645ca6344001958c8b94c68800333d8d7298d100b66631ae531a200087f845d6634400187d0aba4c6880030f6157498d1001c3fc3ea931a200087d87d52634400587ce9aa4c6880030f5d35498d1041637396a931a200087f8755263440010fb0eaa4c68800b0f9d15498d100061eba2a931a2081c6e7255263440018dea8b94c6880031b5517298d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400187ecbba2c6880030f1977458d100045f43ec8b1a2000c3f75d916344001878ebb22c6880032b1cb6458d100045f438c8b1a2000c3f751916344001878ea322c6880032b1c86458d1000637b2ee4b1a2000c6c65dc9634400195ec9b92c6880032b1937258d100043ec26eab1a20008bf845d5634400517908baac68800237e0d7558d1000477c12eab1a20018ec825d5634400187eebba2c6880030f1d77458d100061fc2ee8b1a2000c3c85dd163440010ff0aba2c68800e1f2157458d100046fc1ae8b1a20008ef825d163440031d904ba2c6880030fdd47458d100061e3a8e8b1a200087e87d5163440070f90faa2c6880030fdd35458d100161e3a6a8b1a2082c6c72d5163440010fd0eaa2c6880021f21d5458d100061fba2a8b1a2002c3c7455163441038d8e4aa2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000637aa6e4b1a2000c6d54dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c96
  | 6 => 0x70fa9ca7b2220008be8714f644400117b0e29ec888002aba0853d911000556c10a7b222000c3f75dcb644400147d0b396c8880028f61672d91100054f41ce5b222000a9d839cb644400147f0ab96c8880028f21572d91100061fbaae5b222083aba801cb644408957300396c8880022fa1c52d91100045ec38a5b222000a9e8314b644400153b06296c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c8880e2aea0371d91102271b28ea3b2220448be87d43644400117b0fa86c8880038ed4250d91102255b408a1b222000ab581143644408917d0f906c8880022f61f20d91100051f42e41b222000a3d85c83644400153d07906c888002a760f20d91100247cc06e9b1a2000c3f745536344005878e8aa6c688003175d753d8d100056ac0ea7b1a2003c5c7594f63440071bf0ea9ec688002a7a1053d8d100054ec20a7b1a2000ace8214f634400159b0429ec68800297a1743d8d100052ec2e87b1a2000e1d54d0f63440051bf0ea1ec6880038755143d8d100052f42887b1a2000a5d8510f634400159d0421ec688002b360843d8d100052f42865b1a2000a5d850cb634400153d08196c688002a761032d8d100052ec26cbb1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000a5d841976344001cab0232ec68800387d9764d8d100070e32ec9b1a2000e1f85d936344001c390bb26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c68800297a1464d8d100052ec28c9b1a2000e1f651936344001c38ca326c68800387a1464d8d100070ec28c9b1a2000e958119363440014bd0daa6c6880029721b54d8d100070fb26a9b1a2000e1c64d5363440014bd0caa6c6880029721954d8d100070fb22a9b1a2000e1c6455363440014bd0b316c6880029761662d8d100054f424c5b1a2000a9d8498b6344001ca8cb28ec688003a519241d8d100054f424ebb1a2000a9d849d7634400159d053aec688002b360a75d8d100062eba8ebb1a2043ad6811d763440015ab023aec688002b6a0374d8d1021d6cc06e9b1a2000a5e859d363440014bb0b3a6c688002b3a0a74d8d1000566c14e9b1a2000a5e851d363440014bb0a3a6c68810eb5a0474d8d100056ac08e9b1a2000e1f549536344001c3f08aa6c68800387dd154d8d100070e3a2a9b1a2000a5e85dcb63440014bb0bb96c688002b560772d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d100056d400e5b1a2043ad9801cb63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b63440014bd0ba16c68
  | 7 => 0xce82d8d32840879a8e3b1a650810b351c4634ca1021c6fc3ac798c20428de8798d318402d9acc6b8861080021fa1b74d951001c3fc3ec9b2a2000c3d74d9365440010fb0f326ca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca880021fe1d64d95100052fc1ac9b2a2000a5c8359365440014df04b26ca880029b20964d951005c3ec38c9b2a2000c3d74193654400187b0e326ca880038d60464d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d951005d3b436e3b2a2000e34649076544001c68c8a0eca880021f61e74d95100061fc22e9b2a200087e871d3654400187ae83a6ca881169da0474d95100053ac08e9b2a2000a3e849cf654400147b0939eca880029ba0a73d951000536c14e7b2a2000c5d731cf65440010fd0fa1eca880021f61f43d95100061fba687b2a2000c3f7450f65440010fd0e21eca880021f61c43d95100053741087b2a2000a6d8210f654400147d09396ca880028f61272d95100052f41ce5b2a2000a5d839cb654410d4f500396ca881169e60072d95100043f43e85b2a200087d87d0b654400187ee9a16ca880030fdd142d95100043f43885b2a200087d8710b65440014bd06216ca880029760c42d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95101b53d406e3b2a200087e87d0765440010fb0fa0eca8800297a0f41d95100052ec1e83b2a2000a6e82d0765440014db05a0eca881161fa1f40d95100043ec3e81b2a200087e8710365440170fb0e206ca8800297a0c40d95100052ec1881b2a2000a6e8210365440014db04206ca881169da0440d95100053ac0881b2a204587e87c8365440010fb0f906ca880028fa1320d95100051ec2641b2a2000a5e83c8365440014bb07906ca880028fa1b75d91100061f3b6ebb222000a3e861d7644400187cec3aec8880030f9db65d91100045ec3ccbb222000a3e85997644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400117f0eb2ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec8880028fa1865d91100061f3b0cbb222000e3581197644400147d0b316c8880028f61662d91100054f41cc5b222000a9d8398b644401556d0db8ec8880038d19651d91100061f386ebb222000c3c70dd7644400147d0b3aec8880030f5d475d91102255b408ebb222000ab5811d7644410b575003aec888112ae60075d91100051f438ebb222000c3e871d76444001c6d023aec8880038d60475d91100071d400ebb222000e39801d7644400187eebb9ec888212aea0373d91102255cc06e7b222000a3e859cf644400147b0b39ec888002aba0a73d911000556c14e7b222000a3f855cf64440014790ab9ec8880030fdd573d91100
  | 8 => 0xea8ac31000a3d21d41586200263b30aea30c40008f78758461880018eaeab08c31000e1fa1676cc6200043ec2ced98c40048f9869c231880091f30d38063101063be1970886200b66731ae41844000c3f745536348005878e8aa6c6900038b55142d8d200161f3a2a931a4000c3d745526348001c3aa8a1cc69000e1fa1f7558d200043ec26eab1a40008bf845d5634800517908baac6900023de057558d200247a40aeab1a400087e871d5634800517d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f85dd163480018790bba2c6900021fe157458d2001c3e42ae8b1a40008f7815d163480091e902ba2c6900023ee017458d200045f438e8b1a4000c3f751d16348001878ea3a2c6900021fa1f5458d2001c3e43ea8b1a4000c3f74d516348005878e9aa2c6901f71d1c75458d200043f43aa8b1a400087c87551634800187ee8aa2c69000b0f1d15458d203f63a38aa8b1a4002c9c7490d63481139a8e321ac69000a3721d4358d200164e3a286b1a4000e1d5450d63481119a8e2a1ac69000a3b21d4258d2000716aa284b1a4000e8d43509634810f9c8e2a12c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031dd537158d200063aaa6e2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac6900032e1d37058d200046fc3ac631a4000ad48158c634800587ce8aa0c6900030f5d15418d200043fc2ae7b0a400387c855cf61480011ef0eb08c290002b520d61185200247c432e118a400087f855d831480070f90abb062900022fe11760c5200145e422ec18a40048f8865c0314802d9b0c6b8062900133c185700c52000c6fc3ac71824043ad48158e30480011bd0e31a609000237e1d630c1202156a40ac61824002c3e7455263c400187ae8aa4c78800b0f9d15458f100061eba2a8b1e2002c3e7455162c400187ae8aa2c5880021fe15764cb1001c3e42aec99620048f4815d932c40099a8e331a65880123721d634cb1000d66412c69962004cd47158d32c40851bf0eb1e618810e37a1e634c31000c77416ebb1c20008ed82dd7638400587ce8aa4c7080030f5d15498e100070eaa28731c200387e87dd563840010fb09baac7080021fa1c7558e100043fc2ae8b1c200387c855d163840091f100ba2c7080021fa1f5458e1001c3e43ea8b1c200087e8755163840010f90eaa2c70800a3721d4358e100164e3a286b1c2000e1d5450d63840011bf0eb18c70800b0f9d15418e100061eba2a831c20168de83dd762840011bb07baec50800a3b21d4258a1000716aa284b14200087f855db32840070f90abb665080063720d76cca1001c3f42cec994200087d859d932840010ff0abb2650800e1f215764ca1000c6f43ec69942001a
  | 9 => 0x74585300061e32ee8b0a60008be87d91614c00187eebb22c2980030f1d7645853000656396c8b0a60008be87191614c00187eea322c2980030f1d4645853000656390c8b0a6000c6f65dc9614c0018d8cbb92c2980032bd93725853000656326e4b0a60008f787584614c0015c904b08c29805b360c276cc5300043e432eb18a6000c3c645d6314c0010fb0fb2c62980030f9d7648c5300061ebaec918a6000cb8649c2314c001970c8b84629800395d95310c5300043fc2aed10a600387c855da214c00117f08bb4429800a2f211768853001c3f42eec90a600087d85dd9214c00517d09bb242980022f61376485300ee2f3b6cb182601cc9e76d92304c001cb6cbb04609800b0f9d154588300061eba2a8b1060168ec87549620c02d1d90ea12c4180038b55142588300057440284b106000d57751c5320c001aa8ea38a641810b35618714c8300066bb20e29906000cd5641c5320c001aaea838a641800355550714c8302a6e3210e29906000dc5421c5320c085ba50038a641810b74600714c83021e6b300e299060008ef825d5610c0031d904baac21810a3721d325843000e6639264b086042ad4814c9610c02d1e90ea8ac21805ab520d51584300b47a43a82b086016ad483505610c02d9a862bb4621810a75205720c4300b56bc3ac21886000cd787584310c001caea8b08621800395551610c4300066ab92c218860169db865c0310c0879b70cb80621800356e15700c430006ac42ae01886000d9b845c0310c001b3108b80621805b36d91700c4300066cb22e01886000d5b545c0310c001ab2a8b80621805b351cd61884300043fc2aec908600387c855d9210c02d998e6b1242180063d21d61484300b66a39ac29086000bd0814ca300c0018b8ebbb26018003271d3764c0300062faa6ec9806000c5d54dd9300c0018beedbaa601800327ddb744c0300063c3aeec9806000cb874dd9300c0018f6a9bb260180031e553764c0300063dbb6ea9806000cbb76dd1300c0091ed03baec7100023d60775d8e200043ec3cebb1c4000a3d849d763880070ff0ebaec7100021fe1175d8e2001c3f42ee9b1c400087d85dd363880091ed03ba6c7100023d60774d8e200047d406e9b1c400387f87d5363880010fb0faa6c7101f71d9c754d8e200043fc3aa9b1c400087d87553638800187ee8aa6c71000b0f1d154d8e203f63b38aa9b1c4000c76759c763880018eaeb38ec7100031d9d571d8e200063abaae3b1c4000c77545c763880018eaa8b8ec71000b0f9d15498e200061eba2a931c4000e1d5450e638800187ee8aa2c71000b0f1d15458e200146e43a86b1c4002c9c7450d6388001c3aa8a1ac71000237e1d6318e200161f3a2a831c4000c3d74550638800187ee8aa2c31000b0f1d1545862001c3f42ee6b0c400087d85dcd61880071e9
  | 10 => 0xb2a6000a3d84c83654c0014bd07906ca980029760f20d95300051f436ebb226000c3e76dd7644c00147d0c3aec8980030f9d875d91300061f3b6cbb2260008bd87997644c00147d0b32ec8980022fe1d65d91300051f430cbb226000c3e76197644c03953d0db9ec89800347dd773d91300051f42cc5b226000a3d8598b644c00187ae7baec8980030f9c375d91300061e386ebb226000a3e859d7644c00187aea3aec8980028fa1c75d91300061f438ebb226000c3f75dcf644c09b57501b9ec89800387d4e53d91300045f438a7b22601c8bd8714f644c00155d0429ec898002ab60853d91300061fbaee5b226000a3e859cb644c00147b0b396c898072a7a0e72d91300054ec1ce5b226000a3f855cb644c0014790ab96c8980030fdd572d91300045f438a5b2260008bd8714b644c00153d06296c898002a760c52d91300045f43865b22601c8bd870cb644c00147d0a196c8980028f61432d91300051f42ce3b226000a3d859c7644c00147f0ab8ec8980028f21571d91300054fc1ae3b22601ca9c835c7644c00155f04b8ec898002ab20971d91300045f43843b2260008bd87087644c00147d0a10ec8980028f61421d91300054f41843b226000a9d83087644c0015750010ec898002ae60021d913026d4f41ee1b2260008be87d43644c00117b0fa86c8980038ed4250d91300055b408a1b226000ab581143644c00117d0f906c8980022f61f20d91300051f42e41b226000a3d85c83644c00153d07906c898002a760f20d91300061fba2a9b126002c3c74553624c005938e8a1ec4980038755143d89300043f43ecab126000c3c74d95624c0010fd0e32ac4980030f1d065589300061fb2ee8b126000c3c65dd1624c00117d0fb22c4980030fdd764589300061e3aec8b1260008be87191624c00187eea322c4980030f1d464589300063bb2ee2b126000c7465dc5624c00196ec9b8ac4980032d19371589300063bb28e2b126000c74651c5624c00196ec838ac4980032d190715893000672310e2b12600087e86dd5324c001878c9baa64981ee1fa1f654c9303d43e43eca9926000e4c32d95324c00187eebb2264980030f1d7644c93000746196c89926000c7765dc5324c0018e8cbb8a64980032dd93714c9300065a326e29926000c77651c5324c0018e8ca38a64980032dd90714c9300065a320e29926000ce7621c5324c04d9c8c438a64980032e193704c9300065c320e09926000ad583087614c0015e30010ec2980030f9d365985300061f3a0cb30a6000c3f655d2614c001878caba4c2980030f9d764985300061ebaec930a6000c3e75192614c00187aea324c29800e1fa1b75585300043f43ecab0a6000c3c74d95614c0018d8e5b2ac2980021fa1c65585300061e3a0cab0a6000c6c72195614c00517d0dba2c2980030fd97
  | 11 => 0x484010ff0ab80c69080e1f2157018d210045fc22e031a42028bc845c0634842d998c6b96629080b0f9d154d81210061eba2a9b0242008fb8758060484010ff0ab98c09080e1f21573181210161f3a2a8b166000c3d7455162cc001c3aa8a1ac59805a3b21d5258b300b47643a84b166000e2d5450962cc001d1a86a12c5980030fdd15458a300161e3a2a8b1460028ec87509628c001c5aa8a12c51800637e1970cca303d62fbb6ea994607ae4e62dd5328c03759b0db926518006b3e19624ca301866bbb6e29946030ec662dc5328c04d9aeec38a651800355dd4714ca30006aa3a8e29946026ec6621c5328c0879ad0c38a651810f35618714ca300066bb20e29946000cd5641c5328c001aaea838a651800355550714ca3030ee3210e29946000dc5421c5328c001ab6ebb826518003741c4704ca300061fba2a8b0c6002c3c74551618c0871bd0f992c31810eb5205325863001c7a43aa2b0c60028f487505618c0014eb0a10ac318002ad61021586300056ac1842b0c6000af280085618c0098ecc2ba8c3180023de1d61186300063abaac230c6004c76615d6318c0018eaeab0c63180021fa1b74d953001c3fc3ec9b2a6000c3d74d93654c0010fb0f326ca980021fe1d64d95300ec3ec38c9b2a6000c3d74193654c0014dd04326ca980029b60864d95300061ec38c9b2a6000e1d83193654c001c5d04326ca980038b60864d95300070e32487b2a6000d1f7450f654c001c38c8a1eca980028fa1262d95300051ec24c5b2a600087d879d3654c00187f08ba6ca980021fa1c74d95300061eba0e9b2a608aa5e831d3654c0014bb063a6ca980029ba0874d953000536c10e9b2a604ea7a80dcf654c0010fd0fa1eca980021f61f43d95300061fba687b2a6000c3f7450f654c0010fd0e21eca980761f61c43d95300053741087b2a6000a6d8210f654c00147d09396ca980028f61272d95300ed2f41ce5b2a6000a5d839cb654c0010fd0fa16ca980021f61f42d95300061fba685b2a6000c3f7450b654c0010fd0e216ca980021f61c42d95300052f41885b2a6000a5d8310b654c0010fd0e196ca980761f61c32d95300051f42065b2a6000a3d840cb654c0018eae238eca980021fa1f41d95300043ec3e83b2a6000a5e83d07654c0014bb07a0eca980029ba0b41d953000536c1683b2a600087e87107654c0010fb0e20eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca9800297a0c21d95300052ec1843b2a6000a7a80087654c0014f30010eca9813a97a0f70d95300043f43e81b2a600087d87d03654c0010fd0e206ca980761f61c40d95300052f41881b2a6000a5d83103654c0014dd04206ca980029b60840d95300053b40881b2a6000a7581103654c0010fd0f906ca980021f61f20d95300051f42641
  | 12 => 0x8123d20575588310247a40ae8b10627dc7471d51620c40587ce8aa2c4188030f5d154588313f63a38aa8b106289cd47190d620c401c3aa8a1ac418a23351c543588310247643aa4b1062048ec87509620c401c5aa8a12c418803a350d42588310257240a84b106287ce471509620c4018eea9bb262188031d553764c4310b66b29eec9886200cd553dd9310c40187ee8aa4c01880b0f1d154980310247cc3ca130062048f987902600c401c72a9204c01880e1fa1f75580310043ec26eab0062008bf845d5600c40517908baac01880a2fa1f74580310061fbaee8b006200c3c75dd1600c40187f0bba2c0188030f21774580310043fc2ae8b00620387c855d1600c40187eea3a2c0188030f1d474580310043f43ea8b00620387c87d51600c40187ee9aa2c01880b0f1d354580310043f43aa8b00620087c87551600c40187ee8aa2c01880b0f1d154580310164e3a486b006202c9c7450d600c401c3aa8a1ac018802b6201435803101e3c3aca0b0062048f887541600c42d5b106a82c01880b2e1d240580310071caa480b006200e9a43901600c4091f10ea02c01885ab620d40580310161f3a2a931c4200c3d745526388401c5aa8a12c7108021fe15739822101c3e42ae7304420387e87dd560884010fb09baac1108022fe1175582210145e422eab0442008df835d5608842d1b906baac11080a2fa1f74582210061fbaee8b044200c3c75dd1608840187f0bba2c1108030f21774582210043fc2ae8b04420387c855d160884011bf06ba2c11085a3720d74582210061fba8e8b044200c3c751d160884010fd0faa2c11080e1f21f54582210061fba6a8b044202c3c74d5160884010fd0eaa2c1108021f21d54582210061fba2a8b044202c3c7455160884018beebb9ac110803171d773582210064fba6e6b044200c9c74dcd60884018bea9b9ac11080317553735822100667216e6b044200c5f751cd60884018b8ea39ac11080327dd073582210064e3a0e6b044200c5f541cd60884018baa839ac11080b2b1d1425822100716aa284b044200ccf7350960884018baeba9ec690802a761053d8d2100566c10a7b1a42028df8750f634840593ce8a1ec6908038755143d8d210161f3a2a931a4200c3d7455263484070fd0fbaac6908021f6137558d210046fc1aeab1a42008ef825d563484011ef02baac6908021fa1c7558d210043fc2ae8b1a420387c855d163484011ef02ba2c6908023ee017458d210047c402e8b1a420087e87d5163484070f90faa2c690a371ddc75458d210043f43aa8b1a420087c8755163485198eee2aa2c690803171d77358d21006363aee4b1a4200c7775dc563484018e8ebb8ac69080237e1d6318d210052e42ac631a428bad78158c634842d1b906ba8c69080b0f9d15418d210061eba2a831a4200e1d5450c63
  | 13 => 0x55c422c03026402c3e74550604c80187ae8aa0c0990021fe15711813201c3e42ae23026400e3954100604c80587ce8aa2c5988030f5d15458b310b47643aa4b1662168ec8750962cc401c5aa8a12c59880e1fa177058b310043ec2ee0b1662028be84dc162cc40117b09b82c59881275207764cb31006abba8e29966200d54751c532cc40187ee8aa4c19880b0f1d1549833100e67392653066243ad4814ca60cc40187ee8aa2c19880b0f1d154583313f43ec3ce8b2c6200c3f749d1658c5234bd073a2cb188029760e745963100537414e8b2c6200a6d829d1658c40187f08ba2cb189f61fa1c745963100537c12e6b2c6200a6c825cd658c5214ef02b9acb188021fa1f43596310043ec3e86b2c6200c3d74d0d658c40187ae8a1acb188be1fa1c43596310043ec3886b2c6200a6e8210d658c4014db0421acb1880297e0d725963147d2e41ae4b2c6200a3e841c9658c40147b08392cb188be97a0c72596310052ec18e4b2c6200c6d721c9658c4010fd0fa12cb188021f61f42596310061eba684b2c6200c3d74509658c4010fd0e212cb188021f61c42596310052f41884b2c6200a5d83109658c45f0fd0e192cb188021f61c32596310051f42064b2c6200a3d840c9658c40147d09b82cb188028f61370596310052fc1ae0b2c628ea5c835c1658c4094ed02382cb188be9d60470596310043f43e80b2c620087d87d01658c40187ae9202cb188021fa1c40596310043ec3880b2c6200c3d74101658c4014bd06202cb188029760c40596310053741080b2c6200a6d82101658c4094ed02202cb188029d60440596310043f43e40b2c620087d87c81658c40147d09902cb188028f61320596310052f41e40b2c6200a5d83c81658c4094ed02102cb188029d60420596310164f3a286b146200e1d5450d628c4070fd0bb82c5188021f6177058a310145f426e0b1462008bd84dc1628c4010fb0dbaa65189ea1fa1d654ca313dc3e43aca9946200e4c32595328c4098e8e2b2a65188031d997714ca310063ab2ee29946200e3954102608c4015b306204c118802ba60840982310061fba2a8b046202c3c74551608c401c3aa8a1ac118802b620143582310071caa080b046200ad983101608c401d3486202c118802ba60840582310257940880b0462028ef8750b624c401c5aa8a16c4988021fe1570d893101c3e42ae1b1262008bf845c3624c40517908b86c4988031b1d7624c93118672316e2992627ac5c76dd5324c4f5c98c5baa64988b6b3a1b724c93100d67436c499262049d687dc5324c4619a8edb8a64988c3b118b714c9310266a3b0e29926200d57751c5324c401aa8ea38a649889bb1188714c931344ebc3a6598a6204ad4864cb314c461d88c4996629880b0f9d154d81310061eba2a9b0262008fb87580604c4855a902990c098
  | 14 => 0x48254c614c80156d08298c299002ad61053185320072aa98a630a6426ae68214c614c8015cb04298c2990029da1743185320053ac2e8630a6400e3554d0c614c84d5cd05a18c299002b960b431853244d6bc3c8630a6489ad58790c614c913d2ce9218c299227a55d243185320072baa48630a6400e555490c614c929d8c85218c299002b5a0243185320071aaa28630a6488ad78750c614c9115ab0ea18c299003a5e1143185320072baa28630a6400e965450c614c801caaa8a18c299003a555143185320070aaa28630a6493e974250c614c927d8c84a18c29924fa550943185320056a4028630a6400a768510c614c8014eb0a218c29909ab9a08431853200572c108630a6492ae784508614c84dd4f08a10c29921fa99d1421853243f52ba28430a6400e6754508614c801d4ca8a10c29900399551421853200752aa28430a6400e2554508614c90fd8ce6a10c29921fb15cd421853200753a1a8430a6400ec643508614c801d4a86a10c299003b150d421853200742a1a8430a6400ab684d40614c80156b09a80c299002b5a0f50185320056ac1ea030a6426ae682d40614c8015cb05a80c299002b5e0d50185320056a41aa030a64048f687140614c8011eb0e280c2990029da1740185320053ac2e8030a6400ad683d00614c8015ab07a00c29909ab9a0b401853200572c168030a6400e3554900614c801d2c87200c299003a950a40185320056bc1a8030a6400ad483500614c8091ed0e200c2990023d61c40185320053b4288030a6400a7585100614c801c6aa8200c299002b5a0c40185320056ac188030a6400e9643100614c84d5cd04200c299002b9608401853200752a108030a6400a3d84197604c8f78bae632ec0990063760f75d813200c6ec1ee9b026482c5d73d53604c80587ce8aa6c0990030f5d154d813240e2eb9aa9b0264008dd8790f604c801c3aa8a1ec099002b620143d8132016573a285b026400e2d5450b604c80399ae6a16c099003a350d42d81320071caa081b026400ad983103604c801d3486206c099002ba60840d813200754a1081b026400a3d84196604c8018eecb38cc0990031d19671981320063bb2ae33026400c74655c6604c8018ecebb0cc0990031d5d761981320063b3a8c33026400c7575186604c8070fd0dbaac0991ea1f21b75581320043f43ecab026400c3c74d95604c8010fd0e32ac0990028f61065581320061e3a0cab026400c3f65dd1604c801878cbba2c0990031dd9771581320063a32ee2b026400c77651c5604c8018e8ca38ac0990023da1f61581320063bbaec2b026400c7475d85604c80196ee9b0ac0990032d1d361581320047b438c2b026400c7775185604c8018e8ea30ac0990032ddd061581320065a3a0c2b026461cd773185604c80147b08328c0990023ee1d601813200
  | 15 => 0x8aa6c2990038d5d154d85324671ba12a9b0a648ce3542553614c801caea729ec299002ada1053d85320055ac20a7b0a6430ae68214f614c8015cb0429ec2990029da1743d85320053ac2e87b0a6400e3554d0f614c801c6aa8a1ec2990029da1443d85320053ac2887b0a6400e954310f614c8615cd0421ec299002b960843d85320053b42ee1b0a6400a7585dc3614c80156d09b86c299002ad61370d85321856ac1ee1b0a6400ae582dc3614c8014ed0b386c2990029d61670d85320055b426a1b0a6400ab584d43614c8011ed0e286c2990023d61c50d85320053b42e81b0a6400a7585d03614c801c6aa9206c2990023da1c40d85320047ac3881b0a6400a7685103614c8014eb0a206c2990038d55040d85320056b41881b0a6400ad583103614c8615cd04206c299002b960840d85320263a30aeb30a6400a3d84196614c8018ecebb0cc2990031d5d761985320043f43ecab0a640087e87195614c80147b0832ac29927f17dcc65585320051ec20ca30a647bc5d73194614c8011ef0eb08c2990029de1561185320053a42ac230a649ec7676d94614c8014eb09b28c29925f955cf65185324bf33216ca30a64008f587994614c9314ed0b328c2990023de1d65185324ed6bc1aca30a6400ab684194614c80156b08328c2992729da1865185324de3b3b0ca30a6400b3584194614c801c6d08328c2990029d61065185320071ac20ca30a6400a3584194614c935cab06328c29926b955cc65185324d733410ca30a6400e6582194614c935ccc84328c29926b958c865185324d72a190ca30a649ae6432194614c8011eb0f320c2990029da1664185320053ac2cc830a6499ad583990614c8011ef0eb20c2990029de1564185320053a42ac830a6400af380590614c8015e100b20c2990029da1464185320053ac28c830a6400a7686d50614c8014e90daa0c2990029da1954185320053a432a830a6400e3664550614c801c6ac8aa0c299262b5a1a53185320072a32ca630a6497f465294c614c84d5a90ca98c2990039519553185320072bb2c8630a6400e546590c614c84d5a90ca18c29900395d9543185320072a32a8630a6400e976450c614c801e2aa8a18c299003991955218532007a2a9aa430a6400e6765508614c801cc8caa10c299003a9d91421853200792aa28430a6400f8543508614c801cc8cb990c2991f7959cf54185323ef2ab9ea830a6496e6642d50614c801c6ea92a0c299002b5a0e54185320056ac1ca830a6426ae682950614c8015cb052a0c2990038de1154185323f71b3a2a830a647ee3574550614c8fdcace6aa0c2991fb955cd54185324af1ba12a830a6495e6642550614c92bc6a84aa0c299002b5a0c54185320056ac18a830a6426ae682150614c8015cb042a0c29900395d4e531853200573c12a630a6426ae
  | 16 => 0x3583320164e3a286b066400e1d5450d60cc8015b100a1ac1990021fa1b74d953201c3fc3ec9b2a6400c3d74d93654c8010fb0f326ca990030fdd264d95320053b40cc9b2a6400a7581993654c8010ff0eb26ca990030fdd164d95320053bc0ac9b2a6400a7481593654c8014f700b26ca990029e20164d953219c3ec38c9b2a6400c3d74193654c8f54b90ca1eca9900347dd143d95320070e32287b2a6433a6e86dcb654c8f5a9ee7b96ca990034bdd142d95320071632285b2a6400f0d4350b654c80187e85ba6ca990030f50b74d95320043ec3ce9b2a6400c3f749d3654c80187f08ba6ca990021fa1c74d95320061eba0e9b2a64a0a5e831d3654c8f54bb063a6ca991ea9ba0874d953200536c10e9b2a647a87e87d0f654c8010fb0fa1eca990030fdd343d95320061fba287b2a640087e8710f654c8670fb0e21eca990038750c43d95323d53741087b2a6400a6d8210f654c8e74bd0638eca991ea9760c71d95320043f43e83b2a640087d87d07654c8014bd07a0eca990029760f41d95323d53741683b2a6400a6d82d07654c8010fd0e20eca990021f61c41d95322c52f41ee1b2a647aa5d83dc3654c8014ed03386ca990029d60670d95320051fc22e1b2a6400a3c845c3654c8010fd0fa06ca990021f61f40d95320061fba481b2a640087e87103654c8010fb0e206ca990030fdd040d95320052f41881b2a6400a5d83103654c8f54dd04206ca990029b60840d95320053b40881b2a6400a7581103654c8f5c9ec7b2e64990028f61065d85320161f3a2a9b0a6400c3d74553614c8015ab07a8ec299002b960b51d853201c7bc3aa3b0a6400a7685d07614c8014eb0ba0ec29900a3de1d41d85320053b42883b0a6400a7585107614c8070fd0b386c2990021f61670d85320053ac26cbb0a6400ab684197614c80156b0832ec299002cd61065d85320071b420cbb0a6400a7584197614c801c6b0832ec2990028d61065d85324df2ac18cbb0a649be6682197614c801ccb0432ec2990029da1664d85320053ac2cc9b0a6400a7785593614c8014e90ab26c299002bce0164d853200578402c9b0a6400a7685193614c8014eb0a326c2990029da1b54d85320053a436a9b0a6400a7686553614c8014e90caa6c2990038d99154d85320071ab22a9b0a6400e546594f614c93de8ca529ec2990c2b521953d85321856a43287b0a6400e946450f614c801e2aa8a1ec299003d154d52d853200792aa285b0a6400f854350b614c80156d083aec299002ad61075d85320056b418ebb0a6430ad5831d7614c8615cd043aec299002b960875d85320053b42ce9b0a6400a75859d3614c8014ed0a3a6c2990029d61474d85320056b418e9b0a6430ad5831d3614c8615cd043a6c299002b960874d85320071baa4a9b0a6400e3784553614c801c6ce
  | 17 => 0x80000200000100200000100000281b80000600000380000000000080080100000000400080000001080100280000000000400080480700300000080780080300000000f80300580000100000300480580100180200000a00000381380580080380000100100000000080780380000080000080080100080900000000300280180000080000300000400000000580300700080700300381080800400480380180580080700080280180300380000080100280380200580580000280180080100380100800000180000300000700880300080000000000900000500280080180400700580000080400000380800480180300080200000080100f80080000180e80500700000080180080001480400380a80000000100780300100000480300000680100500000280000000480080280080a00000400000000080000380080000400001780100080300180580000180200b80900280381080100680300280100000000000580080400700c80000180d80000280000080800f00b00200580180700000000380900380080000200100500200e00200080900600100980000180c00000980280000600500300900180100b00000100080201b00500100000a00600180000080780480100300000080080b80000000000080000080000280680080000880600180000100180280001880000180180000000000480100080580380001a00100180000100800200080600380000a80100300080280000300200a80280100000180b00180400000080000380500000000200000600580500080480100100280400280300200080680880100000080100000000100680480680000100980d81580000180600080000680000680000000000000d00000500180280002400000100200380400200080480280000000000100580500380100f80200000080080080080001880000100200b80380380500000000000600000600700200200200100300800800300380300280200000200380280000200200000000400100080680a00980100480100280300000000000000001980000080701180980000300280000180701880300080000780000280a8030fdd154983320161e3a2a9306640387e87dd560cc8018b8e7baac1990021f61375583320045fc22eab0664028bc845d560cc8031b906baac199003171cc75583320145f43ee8b066400c3f75dd160cc801878ebba2c199003271cf74583320061fc2ee8b066400c3c85dd160cc8010ff0aba2c19900e1f215745833200c6e41ae8b066400c3f751d160cc801878ea3a2c199003271cc74583320043f43ea8b06640387c87d5160cc80187ee9aa2c19900b0f1d354583324162e39ea8b06640087e8755160cc8010f90eaa2c1990030fdd154583320161e3a2a8b066481c5c7355160cc805938e921ac1990023721d4
  | 18 => 0x81000000087e00000000004fa0003c4862cf1452d308951c9de5fd3668190a660d60ec86b05247ee269a0249ee6903641c541ae4190dd203cb5271b3ac08e4eb200029a8c60f5e87742480004081550001160ee851c2f89a900000000000000974000000000000044a28011dc00000044498f896e00020c00004e82a7000000089a1b42f285dc08c929294010c16c78b15c0da8f5c86d36b1a2ccd85e91c28664fea7c9083a538eba5c349a869090e6a1402076cce0000172028c0001941ac0ee47d800000802883a059136c1dc40006942b0000104a595000000062e2013f68000000000323155c000000142251c4f656c29c1048a3080e2f92404fc69392870e8c32053a2808c10312882013223c4b62b019e8d740e803e339981cb646c3001a084c4836d1f3084d1984e80ca907ca4487408018e0794000018856c17688640fa3200ca10f0e212e4d9271f309000000063511f9a540000000000ce40002e646e000000000000000008980000000000000000000000000000003d20b40002d60f6227c0000000001b5c2ea0000000000e9400000007bc610000399a32c8b600009ba48c7b46d10409dd8f8c2463fb183d28a5fb000000000024a09f9280a7850f227800024a4bc4188000bb0469000201927659927820dc000000092122c46e1dd1fc98e47248ca0001198c308390ad167803417e000000000018e36e000000000000023140002c622e144c4f00000c391a0dce2b50c995208027df1a0924026200a00000000f600000011f48c481b2ac0fdd1686640000e10f1c2f9056800000063f00023d8a9a00000000011c88530001b3c00028c0000000f4a0000001858e1831c00700280a00380100900000c00480000a80000400f80100200000100801880380000200380000380180400880000080880480180200000000000200300080000380480280180980380500200180000100000100180000180000180000400980600300000000a80201380100300580200d00a80081000880280000180000180201080380800180200080100880000000300480000880c00100080000200000000680000100480400180100480100100100d80180100080400480000080900000080a80000200080000080600080000300280080100180700000080000080500180700000100280100180880182e80000080580000180180480080500600580080000100000000001180400000080800180100381180600000500100380080000400100380180102480300300100180080000480000680280580201d80000180100080400000a00000700000081f80000000600000480000000c00000000180200000100080100100101200080080000200101280280080480000180000100f00600000780180000e80000300d00580180000600080100500100100080
  | 19 => 0xb451dc0003d3176d0f226f331109500e84742f862017878539d159020833f47b836104e23c36d00008140390db23b0c6e67e3921530b0c9210571730c366f410893601980000001cbce020003cd1d5800077e14ca06400032400000009381702361ca40f264b41f073400000014520fc0520002259b045be4ea0000aec3546d03ef03d81c42580ff9870b008b621100000b60e110c10dcc3404b38b800110e4be2ba1bb09700000000fbcdfe11c21c9a04b3a0a90001e4ca0e7e033d10e09545be449a04c09c86211691ac24e35e45e90805a67fa000121018c7b82211564d128a12029948dbe0000000485188908000171400000015ca10cf660000001cc926892204a0aace8c06613406d40006a63d407e0000042284950000011f1d11fcc2d03590000e0400030f13923742ca80344900000000d006d800058e00000000012b00000030b70d2c0343a881bd22017b39587d512e5ca2c71cf89c429f00000ec1d44d002e0550f1e2aa0460fe8f7a0004089e5cb7262a47292b844e1792bf9e08a6e6b40bb073c148073039156c6062fd261947874c31f440931442e1403dd946911835a11a05a494845405997a12328a80e124a80262761881b8020c90c233988103c293000197ce980003580aa111c1cc3b5a428c783b102080009ea0fb0348000c50000057a0680000000000000e78577081023c00000000000002e6532000000000000017d80702e400034d07c00003bf3a01f3107862e0531d20baa0b000013c4000000000000071a38f3239ae0ce25ee2d70000a403363c300000000dc1a90d70a5406a3661248d6631d1ea8f2012200000019a521c0003aa1efce723533d68e7c00011d055800120672127280000006130001dc800000004b1504ae200049620a80006230001924ff20001b4855c0003e30000000000491367080c0008701050ab43040000000964bea40000405bd1462e90420c312824861d619306c406d2bd88a8ba226000005f452254615b8e4c2a65f600000007422060001e78000447190163519a7fd42a84e8460000372822823400000019d43726b21782558cb000001402605fe18422300010ea000013978061a00000000006a069843e0000eea00042684c80000000000000000545256800112838c000142805e0001e998cc0407f040007180242b200010f48dc80c198002c0003780d581740365ab3e59a0115c3263511e4816a3ad17124b4ae02d941181491fa00010d0d9c33e3742de824834000039c0278fe2080478145819687649f1a190f651b3299b009183283f10574b664e42c090d83d20be18280581fe38a48793f4ade10306783f8000429273a5507f67c233c89e800076d3dd1ea8aea1d12fa04c000043448f07b86fc94a0b19f0cc0001502b8a080003400000c04ba62f719500009880003ea0000d881
  | 20 => 0x4a227680000000183ec80009f027500019b8cf800000011540008052d421141ba62c2708000bd6000084834ce1e7470000660af454246d23d48fe0000000000000000086039d1bc15c05e920013207e4428b5c0008b0115a1c8000000000037888a0002b3000000032d000000108456e1f019fce0e000452038c00075c3b71358b748380a0842893651f01815950f021400005180000c93b600004a401700000000008b20001830000000349068800069342d1998bf84743b8164c4ae3f40610ee0af05c229e9768f5840b044801425002b2c501d8f9a2bc23520287d63220a593b928029a16d08e00001221870ef06e40001d9026d1782a9001000095039645d1c2c6fa77f1658000eb642e2d19510000000000000000072d0000f19180650000000000032e000101ce9a6193cc050c9600000000000c2a77c0000000e328b700011ccd8c67700007900003db0000ed0f808b300001c06ca1c9446900cb2000017185ac00000032296c51aa53f220088800022000018886880211db827460400022494185b63060000668a762f40220b20f6a4fa1c3976401c9160de1aa03d46b738a07580006fd1f50d9024c0aa00790ec28a228376819c41a315185812051c38e0e39d987ba0cd076000073a00000000012268630000d587660490f380007886052f18830cde0000fe8e251ce000398169800056a00000001165ef2c900000000000261c58d7c0003b984500003683bc1140bac1f343d0b24f8a0000c6027c000000119a3acf2c29526d0d28da848f35515a0a9462d21d0000e500000000c24e8241c0000000000952097800076a00018d092000021b174000113065e47f8dd40006b60e580006d615112a80003e82bd490229873221f0002288862000000000077400000614900000ee43f046032e00000000880be0001ca0000d5c00000000008463a909e0000aec1e31ab8284a225f7000082cbcc78414e9a642d40000d3893400e2a012980000002c518c95ad1365a03db0e5cc102070238ce8f90000118899c00000001c00008c091242f2518d100000a50000ec295000000012741a900000001867652818cf812a55d41d89c4322050315844070421d06412fcdd0426470943466864e06001f0aac0001c580000002ea4ab800000000043080000000003cfa45c00031b2ae2454f786653f7800044c4170e080000000003e0800000000020e800021a00000023a0aaa000132800115800037aa3b526e89a0db9ec4c284593d1800000036c0d081d519e00400004e406c34b3f505fd0d05540e989390dc49d48892682705b50000878fa20a51f093211be3a814e103922841a3428000d46000000231cefa5f3000000022c0003ee8000e9e81849e93cd1e44c90000bbc00053137789f8c8200940e06585061fb44e88e8d724c00e51f1c1e87dc2b68
  | 21 => 0x869511061d0c680007f81e113181008ea000353800000000037c117c6647124a58000ece0001aa89dd1b228d415a22800085d0000b306ec1a31c180005424791cc0000000000000000000000001e96c0fa01f611d800000052f361000082a1bf102998d0a89020000000f2201100000c80002852f2000081000000023bc3ae1af0000268f6e4ac0001d0826c000000090ca2a79c1770000000000000078118683a1bf92f40f000000000008500000000000dd41e62321a1068e7630000ef40000002ce215cea633b19a80012480003720b54ec80000620cc41f00003a59174000000000000046a6b12b10f144521dc0ef85e10e62ce28c89040000003788f38b1611700017f84ba1920f28e8004a66d470000096460b0000000d1a01405600003b05de11087c89e468a208996422232c00021c400021c03f80000003c221e000000006832a075058271a1bd9958b2e55325a800000079b2fd000093c2ae1ef04b908200000008d856894c3ed00010ac7ce0001ec0be0000000000000003f20b1c801b400000011ed06c5f813e00000005830000af85120003ed800000089600018d000000023b04f81a848e0000000d5e24207800000000004260d985ba3c935a800041085912f80000941fc02c000018200024b97200002f20000000ce808d0001fd0e0026d49300000008160000000000000000159c00067816a1dbcb9a5d71b18000d1c000346000075678c00016b40007d82c2915800025e0001d540009281e78000f642960000e6c5bc4b40000000d4064f398870063c00000000004d8000000224000000000000009ae00041a9090b36820000039400029e12b122087c000000088c70c7183898e202da7e93e91738da4749000213c42a79914c242c9d64d40bd00000008d6000000015072a02b1c88000000000000026a7052450000f9e2703dca4d8ad22880000df0d8a44e11ea3a504c35100000007a80001eb80000008440001318fd600047a000000000041610087a222e0001448fee000000025cc8672e00007f8ea465a3ce89fc1a247003880002ce44813980005f811e36d89900009270000fa45d809c4a120900005303130000c1475a47193380b41f9290a3cc0000000000ce0fc24980198840e1a312127a1950fa4fc3ca942057e4f937101850b63cc1f3a1990663b611216b016e7d54058558d3e31325b00dca529490429e40dbc4dd27d98d89042e01691380ba02e713c91c8b1e29b34124cc0582501128fc0b806874339c191c45cb37f1ef8c0606037ca4687963f53eb851c00071c1b709502986100b10a3c86026b1f993340008bf07e091c00065c000198064e000159892c0000000000ec025474e000000000000d0002034000563076a460f0e37a4a18150d9434e1979b74d386a533389a92640f92bf04a414041b2fc995c39c
  | 22 => 0x4000017128491250c0afa318e4c93024080000007c402886ec81e40626e000011c0000960e94ffc0a70cf1bc8b346fa00011681cc5c40d8800000013330f1d5cea06171681fa069a52735594ac0005881bc81141b247802697fc0008ad1a1a2e48580593f2014c06a2c200020c82163af1a4072010e85200000000007e600019100000001e192c400067200006b40002450000cac69220e3b02348fa686a00003a4d2e84e42893d8d763d63880a403da73d05d0000c0267b00f97b0afa22f1511a3c5ea77701522ac9522a41728dc426857c2221cd46c05e737191e80007830000670b8e71d36a80004041e814000011087f23af8bb4276000260a1201e480138117189be119124929c8565172a71cdd19c0003d080003f48150001bb917c4100001928b183331a3187d1a235f3f60f945166250b896e0ebc2e10000e9d12a32340421289844de0df1c444a24e6483214069816e35e23a8ff824c00000000004ca3638000b6e2441b0914cd744ff0741a446de0000000000000000000000057419d2d781f40001c5000246c1104b31c000000004d11a78eb803c23e00021ac2d83d2391a3f0748000271a1704d240423289888de40d49f920d0240fd2b90900a92883000000073c6e90d9886459481d0000f907205bf0000a1855e3291cd000000069b00001b000001d0001fe000000023f00000003df31d00011a092b30317b4e083bb10780051826763d49e807da1d50b08000b786832bc8000000000417800000025c000000000055e00014403145dd000161c586055000020c00000001d1afcb76000000000078e0bf39b03280000000788f6050264800000000000001a1000000000013711f082800008700000001202d28bf929091c0000000c8000017c14740000003b513541c03e843499acb124a33ff96a80000f51e0149846489143f9a74c626fb000000099e77a1ad853920000000013487ec2a63c697240c63f1188a2ec10c0f738180012088023d5a2bc85a8f13da1954f486f64730188b3e91f049846c7f02000ac16880d67ca461037d028185274800052e92e22b82c45282f6319229c6788292ee23ec8a25e13fd8ef800052e4649330a041a81ca9bdc1e64fe0c78c2837a023486a4c486a2663c416d079a1080a40348c049383b419a850e07731e92ecfca48d0001af43a400039d98ec16493c3bc800058078121505083606040001c94a6c84b3ca00007a04323a1a4240000000969030dd6105420033925e52c19ba534ae691d20f2190e885e23d11c2060e31645c12588260000779d887e45d44a79c251521eb2c205245460000cd8f700783910dc000030653e08a80b428871e0af06b898e6e605c142c84e04f36c8b3d1f45a4091a35c000000370a34d20a82e00000000000002f5000000000046c00000005df42c14508c60004aa
  | 23 => 0x22d51a888017580000dc5a10001a780008fe44c92650c0000152a2945f45824231548cd05252290bc4e1c83424fa3e42a44940f89bf0aa25c126d8ab0b286d30ba19f400055f41e92543b44f439f87787543542a58b102024a641801784c20003211974ab412b04100007fc2b100002d09d846d1ec8598d5a00000000002c00001798ffce6854f0b220a07dc22c29c83150d814f072000017242f24289680002d800018a51f00fa1e080000008223f380000004d9000044c0008103961584de60192389658956621354a270d961f744f19342248db1b82544e4e3000ac8000c1a4091668788000000000000000000048380000003774929e9c34c00007580000000000000090000000221800012018606a80009965051b9a1bc00070a00000000008a025299843645b63a2800000065b0a68000a6860e22098bcde0817356150cb3032110b108464a1c30000ad92a66270c017492880003eb22a88c2000000222cca220918a124ca4660900000000005042579e000005cf00022c4c603fd00000008bc0000a810cc00013d0638d1400039c1f100000007693bd800000017c2d38000000000000154042
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x801a15542014318532005a164e54508614c947e0673551421853251f815cd54508614c80162595d0d42185320078155243508614c801e075450d42185320078155143508614c94b6879750d421853252da165d43508614c8016849050d42185320060d61d54100614c801a155460c40185320062561e43100614c801a255460840185320062961d42100614c801a25855084018532006a160d42100614c80181d7361065d8132006865508050f604c903c0d7355142d8132005a22414350b604c801a195460c40d81320068a55182103604c801a898350840d81320050d650659c6604c8014359419571981320050d65275d86604c801435949d461981320040f66074195604c80103e9819774581320050d65065dc5604c80143594194715813200545650751c532cc40184d835c87259631006075d183101658c40182d7460840596310049366032595328c40160d940c9654ca310068655183102608c401a29546084098231006865508050d608c401a195460c40582310068a55182101608c40142d941d7624c93100545650751c5324c535c44621d4714c931527051c55450d620c547c24715514258831517211c543509620c40141c975514358031006865508050d600c4014389755240580310050b25d545096088401c0d54dcd42582210160b21d54509628c001515941d4714ca304d711988751c5328c001c1764550714ca3000721d91421c5328c001d0554508714ca300068360d82193654c00141e96dd143d9530005836486450f654c00142d929db75d913000507a5b75dcf644c00141d939c375d91300050b64a70dd7644c00124e980cb654c9300058365032d95324c00103e981d7644c930004a3a6032d91324c00160d950cb644c9300068a55080509620c001515941d4714c83000705591541c5320c001c8564508714c83000741551421c5320c00191885211700c43000456261545c0310c001c1964551700c43001c0fa6374553638800143a90dd154d8e200050d652759c76388001435949d571d8e200160721d5450d638800141c975514358d200160721d5450d6348149c14715514358d200160b21d545096348147c24715514258d200162321d435096348145c847150d4258d200050725d5450d638400141d939c375d91100050b64a70dd76444143a3281a0075d91100068c605801d7644400161a90dd154d8d100048765285dcb634400181e8755040d8d100068355182103634400121d942157218d100060761d541006344001a0d546084018d100048b65285dcf624400182e8755040d89100068355183103624400103d94a1f654c9100040fa6075d91324400141d941d7634c910005076507518d324400142d941d7624c910006075d183101650400182d7460840594100040f650875953204001c45651cc7244010
  | 1 => 0x4d0000095321e0fe4743984002c15a456496550c8429305800ee7a000006625100000060000000070002c0000c1f910940e3f170006603ab400244e14c00982600d149e3ca14ac5100179040a000008c000d80000ab50904003d182306c1a09801580d1a054b08d091bcf6001d9f4500000200b200000012e0000000624035818026c150987c005400052000023c006a1c28c00763a8013a5b16a989271119b8b400270000017000000002001ccba74001887200280003c000004144890420484650000000091d000e4a40e8100000000000000491b4c66929250000021800000043065200500000908b000b8a8681b8441e832a860449b33a649a9f441f06a000015c00454729c38842780096a0572c4002752aa400000017c2c140007c5e3c5780001000000c03000000c02008000c0402000000100010000f0002008070000804020083c0e080381004150180004020100c00011400c0a02018000801010080401030000141c9755143583320060721d5450d60cc801a1954201435833201c0fa6374593654c80183b7420164d95320040fe6174193654c8f560c9650d42d95320040fe61741d3654c801a0d4360843d953200607dd183103654c80182f7460840d95320068560d84197614c801a258460865d85324de9160d82197614c8016309059154d8532005852595450f614c801a854360843d85320048d652859c3614c8018358755040d85320068555183103614c801a255460840d853200607dcd84195614c80181d7361065185320060d9d984194614c801a264261065185320068560d84194614c801a2682610651853200685a4d84194614c801a15936106518532006855cd84194614c801a269261065185320068964984194614c801a16326106518532006850c984194614c801a243261065185320068961182194614c935a458360865185320050d65e64550614c94f6159399154185320048d26164550614c8014379759154185320058c24164550614c801615941965318532005856506554c614c801615941964318532005856506550c614c8016169655143185320058965065548614c84d6449654d52185320058965065508614c80162696551421853200781d9543508614c801e046550d42185320058965065cc8614c8012579854c5318532006856115314c614c801a455360853185320068955182d0c614c801685929514318532537819095450c614c949a178755143185325268561d5450c614c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x40e00c2a068070050314eaa100a1ac199002a10a064d84194614c801902c9b24c20ca30a64008856a432610651853200444b5219308328c29900340462650751c5324c40140c53aa840286b006200d01989941d4714ca30
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x20080005200b064d926106518532004405ba189941d4714c931004405ba989941d4714ca30
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x4b
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x124d
  | 9 => 0x94b
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124e
  | 14 => 0x138b
  | 15 => 0x138d
  | 16 => 0x138e
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0xcb
  | 22 => 0x4
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x12cd
  | 26 => 0x168d
  | 27 => 0x9cb
  | 28 => 0x9cd
  | 29 => 0x9ce
  | 30 => 0x12cb
  | 31 => 0x12ce
  | 32 => 0x168b
  | 33 => 0x168e
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0x24b
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0x16cd
  | 42 => 0xb4b
  | 43 => 0xb4d
  | 44 => 0xb4e
  | 45 => 0x144b
  | 46 => 0x144d
  | 47 => 0x144e
  | 48 => 0x16cb
  | 49 => 0x16ce
  | 50 => 0xccd
  | 51 => 0xcce
  | 52 => 0x170d
  | 53 => 0x170e
  | 54 => 0x94056
  | 55 => 0x95255
  | 56 => 0x94055
  | 57 => 0x124955
  | 58 => 0x124956
  | 59 => 0x95256
  | 60 => 0x98955
  | 61 => 0x98956
  | 62 => 0x128a
  | 63 => 0x128955
  | 64 => 0x128956
  | 65 => 0x8a
  | 66 => 0xca
  | 67 => 0x12ca
  | 68 => 0x130a
  | 69 => 0x134a
  | 70 => 0x139256
  | 71 => 0x139255
  | 72 => 0x99255
  | 73 => 0x129255
  | 74 => 0x128995
  | 75 => 0x99295
  | 76 => 0x141295
  | 77 => 0x9c0d5
  | 78 => 0x9c0d6
  | 79 => 0x9d2d5
  | 80 => 0x12c0d5
  | 81 => 0x12d695
  | 82 => 0xc9d5
  | 83 => 0x1680d5
  | 84 => 0x240d3
  | 85 => 0x240d5
  | 86 => 0x1440d5
  | 87 => 0xcc0d5
  | 88 => 0xcc0d6
  | 89 => 0x1700d5
  | 90 => 0x1700d6
  | 91 => 0x12c9d5
  | 92 => 0x12c9d6
  | 93 => 0x1689d5
  | 94 => 0x1689d6
  | 95 => 0x1692d6
  | 96 => 0x1692d5
  | 97 => 0x252d3
  | 98 => 0x252d5
  | 99 => 0x1452d5
  | 100 => 0xcd2d5
  | 101 => 0xcd2d6
  | 102 => 0x1712d5
  | 103 => 0x1712d6
  | 104 => 0xb4253
  | 105 => 0xb4256
  | 106 => 0xb4255
  | 107 => 0x16cb55
  | 108 => 0xccb55
  | 109 => 0xccb56
  | 110 => 0x170b55
  | 111 => 0x170b56
  | 112 => 0x16d456
  | 113 => 0x16d455
  | 114 => 0xcd6d5
  | 115 => 0xcd6d6
  | 116 => 0x1716d5
  | 117 => 0x1716d6
  | 118 => 0x170cd5
  | 119 => 0x170cd6
  | 120 => 0xcd715
  | 121 => 0xcd716
  | 122 => 0x17cb
  | 123 => 0x5cb
  | 124 => 0x4956
  | 125 => 0x1a8a
  | 126 => 0x104a
  | 127 => 0x10a
  | 128 => 0x14a
  | 129 => 0x104b
  | 130 => 0x1a8b
  | 131 => 0x95295
  | 132 => 0x940d5
  | 133 => 0x95355
  | 134 => 0x95296
  | 135 => 0xd0a
  | 136 => 0xe8a
  | 137 => 0x178a
  | 138 => 0x9d796
  | 139 => 0x256d3
  | 140 => 0x1056d3
  | 141 => 0x1a96d3
  | 142 => 0x1440d6
  | 143 => 0x1443d6
  | 144 => 0x1456d6
  | 145 => 0x145796
  | 146 => 0x160a
  | 147 => 0xe8253
  | 148 => 0x178253
  | 149 => 0x104253
  | 150 => 0x1a8253
  | 151 => 0x17c253
  | 152 => 0x245d3
  | 153 => 0x24e93
  | 154 => 0x5c253
  | 155 => 0x5d6d3
  | 156 => 0x257d3
  | 157 => 0x25a53
  | 158 => 0x17d6d3
  | 159 => 0x5d453
  | 160 => 0xcd796
  | 161 => 0x134954dd
  | 162 => 0xe8d12
  | 163 => 0x104d12
  | 164 => 0x104e92
  | 165 => 0xd0e92
  | 166 => 0x104e825b
  | 167 => 0x10424e9b
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1645
  | 6 => 3598
  | 5 => 2393
  | 4 => 179
  | 3 => 8
  | 2 => 3
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (67441+((h/548+packedAt gbK7 (60865+(h % 548)*12) 12) % 2389)*12) 12
  | 6 => packedAt gbK6 (188291+((h/1199+packedAt gbK6 (172704+(h % 1199)*13) 13) % 6319)*13) 13
  | 5 => packedAt gbK5 (150751+((h/797+packedAt gbK5 (141187+(h % 797)*12) 12) % 3159)*13) 13
  | 4 => packedAt gbK4 (13061+((h/59+packedAt gbK4 (12530+(h % 59)*9) 9) % 259)*9) 9
  | 3 => packedAt gbK3 (656+((h/2+packedAt gbK3 (648+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt gbK2 (279+((h/1+packedAt gbK2 (276+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f81ffc0ff81fffffe0fff80127d8f3a33f3fc
  | 1 => 0xc0fe07ff07fe0f803ff07fffedb2f1c5cccc7f
  | 2 => 0xfffff80007fff0003fff87fff1c301fe0f0f8f
  | 3 => 0xfffffff80000003ffff8003e03fe07f00ff0
  | 4 => 0xffffffffffffffc00000003ffc0007fff000
  | 5 => 0xff00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x90018c0098014a38e00cc81801487181151bc
  | 1 => 0x480a035102a20d049210552a84b0b140c4c455
  | 2 => 0xb2d568084555a00925ad0255314300ae0b0a8a
  | 3 => 0x10e7b5aad010801239ce20063a035a07700f60
  | 4 => 0x20f9c63ce679ca5c008400183fe80007aea000
  | 5 => 0x3c41003080610c60010844603fffedf0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36777
namespace PEqualNP.Outside.L_meta_36777
open PEqualNP.Outside.L_meta_36777.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 3 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := (concat bs2_5_0 bs2_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 414 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384))))
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
theorem bs4_5_608 : Interval s4Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 616 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 bs4_5_512) (concat bs4_5_544 (concat bs4_5_576 bs4_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
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
theorem bgb_4_160 : Interval gbAtlas 4 160 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 179 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_2368 : Interval gbAtlas 5 2368 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2393 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))))) (concat (concat (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))))) (concat (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)))) (concat (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208))) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)))))))
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
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3598 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)))))) (concat (concat (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))) (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)))))))
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
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1472 : Interval gbAtlas 7 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1645 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0eeeaeee0eeeae8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373984 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36777.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[3,6]⟩,⟨.and,[3,6]⟩,⟨.and,[1,3]⟩,⟨.or,[4,9]⟩,⟨.or,[2,8]⟩,⟨.and,[7,11]⟩,⟨.or,[10,12]⟩,⟨.and,[0,13]⟩,⟨.and,[1,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36777

open PEqualNP.Outside.L_meta_36777 in
theorem PEqualNP.Outside.L_meta_36777 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
