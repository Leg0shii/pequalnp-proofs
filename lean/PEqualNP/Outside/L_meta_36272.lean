import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36272.Model
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


end PEqualNP.Outside.L_meta_36272.Model

namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
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

def SBf (j : Nat) : Nat := [5, 6, 4, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36272

namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
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
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36272
namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x302ce6400291000a29000a35de43dd43bf42bd42df32dd32de31dc31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x80d00aa28a651d540c65aa4205594630
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
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (208+((h/4+packedAt s1K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s1K3 (111+((h/1+packedAt s1K3 (108+(h % 1)*3) 3) % 7)*3) 3
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
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00faaafaaafaa0fa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36272
namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff03ff07ff83fc1ffffffc1fc07fe4ff3cf
  | 1 => 0xf83ffc1fffc1fc3fe1e0f03fe1fff81b2ccfc
  | 3 => 0xf003fffe007ffffc001ff003ffe007ffc30f0f
  | 4 => 0x3ffffff801fffffe00003fffff801fc0ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa200118400880004c0221119402450940451c5
  | 1 => 0x6125228ca4212941520e8a28d209350c92c45c
  | 3 => 0x456b44186d531ad83115a842b540a669c30e0a
  | 4 => 0x8a528921481a54aea54100932992c0316c0ba0
  | 5 => 0xc630e318e639f333999cce031030441fba000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeccaa00eeeeaaaaeeccaa00eeeeaaaaeeccaa00eeeeaaaaeeccaa00eeeeaaaaeeccaa00eeeeaaaaeeccaa00eeeeaaaaeeccaa00eeeeaaaaeeccaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36272
namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fb90821f6a1043ef32087d86410df94421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40bfa9281ef52502dea4a05f14940f6292816c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5987b94b30b7296617d52cc3daa5985b54b30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ee32883da65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53483dc84907b50920bfa8a417c51483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884107b8c820f6990417e51082faa2107b88420f6108417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f460887e4c110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132ef21a65dd434cbdc84997b50932f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f790c31eea18637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719243ed32487ee4290fb88521bfa8
  | 2 => 0x22e18c0e00ba3327a0000000018a958e01480000007b0000002910c1391fa000ae00010c000000000000000011c000000000000cc0fc3c1060720004a0003b25b4bf0000008c4c51f83520011680042266c000000007780006c35c0ac289b746a0002d1c340a000c99a30dc484000000000009680007a0004e80026e4c0000000004a4a480032e000fc9890fe53cf880000000000000000000bc1402b2428001760007047005016a0000019f0842e8000dd3c400000000484000000fe02c48070a201d8100d9000114344000002bc000000000000000000044c56c0013116400129080000000001520005c80000000024ce39320005441b80037e86d1e0000002fc000000000000012f0000b80026100092c2380000000000142000000002240000004b9e40000012c20a0b26800025c00000000000000000698001302c1009ed0000003f1801680000005726a1589180000021c00000000035238a23e6000c100009000000000200000000000000004c8000100b48a800000000cc9ea0980006f9ab302488000000000000010d0002bc1380917a0006900000000000000230000001e043217c970000e400000000000000000000004740013a22e0f85f0810767109c195180000afa4847e098858100ca99c8900000000000000000000001da12a75c002232d65800002f000000e11bb4346f82a8462020000a9eb1fe244378f00000000000000000024a09032150389ee0008c000063000000000000e8000000004ae3c4db09f296000b787b00092800000000718000000007a0000250000000000016c0005d800000000058000004a0fb9ca480478ac0750da630001a22c830c00000444050000003aa000000440000002507a0000000c0000ee234828003680000000000031c00000000338000000360000000000000000000000000000001d04f88c83300038c001f40000000000046c0000000000000000000000974640000b8000ff0e4001006000000000040000080000000000000002008038000020000000100400405002006018028000000040180500000400008000000000010000040100200001c00802002000008000000040000000401404802000004000000000080080100000401004000000068020020040080100000001801000000010000040180300100000004000002000000050000000000101a00800001000000018000040080000800400000804004010008010040080080000400c00800012000040050040080000000c0100200400200400003006000040030040000000000000000800000000000010000000100100000c04800002000000000020000200000a018000000020080000600200000000028010020000020000080300200c00802bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x8900004c00000406000000000003bc000000005ed22000000000c825b0001740007947481000000428000002293f8294481770bc9645b99e2205d00018310a5c4d20001566e4001a71b600019000000000000a80006b433800000000ce8f93582c4aba53000000001d60002e000000000000002490000007c1842a8000000000000000012448a000000003be000000000008380010c000634000000000001e13c4c6008930001ee5e40002c000000000300009507380044a388000d8000588d40a60d032400000000000a29c90000000000040400056a00424000000000000000000000e000b400028246ced9020445b0001e1022001069140c222046076158134b48002a0368000000000000000000000014800000000e780015c000610000001900008b000000001cd00000000000000954a20a0000000000000000000000f0426bc6201e000000000003907600000e3e4000e9000000940000004863cd078fa3a82780023e0001a4c2800000685320cb00012c001fb34c5b800000050000000e525435c0006034a644000003d83d0be8000343d41d10842a000de8ee000000608000fa3ac8219a0d45fc100584c4074e822b28e000598000f8000272370000000000000049cae8000187a4f309c0460000000036a000000ca00000000000476364fd00028c5352f9d3178528ee8000547fd2721e48c0d0b1800000000fb0de000000028a913682c0000033089c0021020628c001431f60d4001250008580019400081cce11f000000001e50b66e8f82321a84fc0000000000c7900019800000000370000001c5000004000000000012880000000000000000000e7000014000001333167bc73000000001328004cc000b3a062a609000000000000000524503a8b317a0000000016a000000000003a23a4508002e014cab01c1248e50e1e326c000ee0001ac000cb000418000e58b9000000a700036000022a172ea000fe88f00000002000000000de000000000472343628f49590700084c000000000010fa2c0000002784149e9350e89a0c40000026000c5ccbe000000000e60000001cc000000003552f0310004ec00000498820c3000000554090003ea8e00000000000000000000584000820000000011100000068000000000000000000000000000056800000106000001871f84d0d50a73ce0008480019a6488b0000000d9208ed10800000000000620a60cf0004391500031e000960000003711798e00044c0010f366000358960000012d11a00010c5516500007c0000000088438
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd431034e5394840d354e521034e5354840d354d521032f4354840cb50d52103686054840cb54a421029d6310840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cdd0d51103354354440cd54641102b960104408fd9540102ac62500409ed9540102e862500409b98b54cc26d62d5330c798e54cc26e62153309b58854cc31e5450f30cb95252cc32d5494b30cb95152cc32d5454b30d390d52cc34d4354b309b988548c26d62152309d984548c2756115230b6580318c26f62551309b189544c27761551309d185544c26e62151309b588544c25c6550d309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c26f62544309b189510c355510c43097d95300c27b654c0309798c54c825d63153208f99053c823d6414f20ba18142c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823e6494e208f59253882cd6310a20d394d32882e4614ca208f992544826f62551209ed81544825e63151209758c544823e6515120c798c544831d6315120cb588544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d209b996424832c54909209b195424832c5450920ba181424833854c8120cb152204825e63150209758c540826e62150209d984540827561150208f990530823d6414c209d98453082756114c209b597420826d6510820b358c420826d658c820b9185320825f63544209718d51083655108420ba58021082796510020ea108400826f6548020ab191200827b6548020ae191200826e62d53109b58b54c425e63953109758e54c426e62953109b58a54c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538426e6294e109b58a538425e63d4a109758f528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d6580534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524433454905109d1954144358538c1109e195304425e63150109758c540426e62150109b588540427661150108f990530423d6414c109b988530426d6214c109e980530423e64148108f590520425e63148109758c520427965840109dd95100427b6544010
  | 1 => 0x1088001215000081c010b8340a57188100c010080410060004410020880000080280c5a0400008080f008240a132a04000010087d6803010080e01038080e0b0400800070182c0c000e00c20080303c00089bd8950d0e6c62543439bd895190e6c62546438fd954310e5f6550c43cbd0d5210f4e4354843cb50d5210f4d435484397d8d5190a5c6354642ced0c5050b394314142dad085050b3a4214142c754f4210b4d53908428fd954210b1d5350842ae1814210a6f6550842d354d4210ae860508429e98354cca7960d5332ba181428ca3f64542328f191508ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5c6550d329b195424cb8d4350932ba181424cb564314532d550c514cb664214532d9508514cb673214532d58c8514ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320cad4614c8329bd95320cb2d544c832b9185320cb1e5350f41d394e52d074d5394b41d394d52d074d5354b41cbd0d52d072d4354b419b988535066d6214d418fd95411067765504419bd89501066c62540419b98854cc66d62153319b98a548c66d6295231a7590328c63f64542318f191508c66f62542319b189508c65d63951319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131d914b314c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c71e63950318f990540c66e62150319b588540c67a60150319e580540c65d6590c31b5586430c71e5450c31cb952520c72d5494831cb951520c72d5454831d390d520c74d4354831d9185520c74d528c831a7590320c65f654c431b3189310c677654c431b9189310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c75a4354031d650d500c65e63153219758c54c863e6414f218f59053c86e4614cb21b958831c87c6320c7219e983548867960d52219798e548865d63952218f990538863d6414e219e98053886796014e21cb95142886e86050a21ab590328865e63951219758e544866d629512197d8d544865c63551219ed81544867860551219798e534866f6254d219dd85534863e6414d218f590534865e6514d21c7990534871d6414d21d3588534866e658c921d314e324866c654c921d314d32486e4614c921d514f214874c53885219798c540865d63150219e980540867960150218f990530863d6414c219b988530867a6014c219e580530866d6590821ba181420866d65cc8219b59432086ad640c8219d59431087c4320c4219bd9521086cc63484219dd9521086d463484218fd91500863c64540219b98a539026d6294e40a758c429025f63546409718d519026f62546409b189519036852d0140cb14a40502b960d0c40c794
  | 2 => 0x448000019a53844000000028aa58f85820a2a000ae0b6c21389919819158241b2ca214b730cb618c702b28d8004f800ac1660f95092a0c2182e609be47b06b6aee0000258800799a225b2c8692a1a9b43830046184001da0c848aa8b088a72c386e022de72aac000705596ab4000ad000a9b1e550ec118d8000725d14a6c2342d2e610074531bc7701485a06b22b640ac47bb309f852200ac3700078800000680010c0000000134c8aeaa52a261ad65f9fcb32ae96a7894858321d4a60006207e43a2a6a208508ba7b2a493302342427094492312141ba8722c699364e90ac41705d92c071d0280fea415ecb88aa38ca3f284030425485a06a1060076391f430810bc9681e8d68a1d67e016a6ac698b1496218a018e7a0188e16e7a99cb5038800d42b8c6848b2710c448266813182f326afac04982c0a02097b36649fa8ca2491ae4078ce23a540f1f63897c6505680a3a468921b1a0331cc4bae800190bf116368006b8005723c172206e2302209e0a8a40031c422cac6800762604004cbd000a20d2000009e80023250cd0007f806003163e800590000026cb82a00000000324a71d200004151b600000b0800000009a000be8f0521accaa4ebb09a129a42a800181321f30a5e96c049723d80000098902f087800000ea000001882297130301409f33a72276a182471800000de00304790b8000008f8f200000a7a440291400146c82d2bdae26a9043a2ba002a81780013afe001229c0003b8823d0942f8a2001789d2bcbe1280018a83ace73800441f2000009b800000840012477a8c6780047000568e603996298360e86689a927822e0000000338cc906000264f09c0026a00256001f01e0340c2820003a2d002080206000640e05010040c060300c64000081c00010000c06010101400080088400060280c0a080e05434000a81c10070305002060003800020c8300c010084422150080c003
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1ca3003403d50000ce0115c04c00040094160122c0508600182001144021820861818654c6050842c92a6302842168943181424cb82a1a8428a65581c14214532c2aa830a641962554185320ca62392c321863435ce5450a21c54a83028510e0d645885348686ba0a6992439114c614c921b0ae81906210ca8725834310254392c020881511c9510c430a1ae929a6510646531853288306b1ac42a241435cc5450920c50a830284905447354421082543a2c010841625cc4210020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x6000402000800d01431c14214532a09839506050a21a058414c614c921a058494c614ca20a09831506050920
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
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (18887+((h/205+packedAt s3K5 (16632+(h % 205)*11) 11) % 1190)*11) 11
  | 4 => packedAt s3K4 (16974+((h/138+packedAt s3K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (304+((h/1+packedAt s3K2 (300+(h % 1)*4) 4) % 12)*4) 4
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
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080eeeeeaeaecec8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36272
namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x158d4a0070000304162400e0a0000300060102304100272e2c49d361d621267969a50548853005499447c800545078048013010000d13c00c00006033c0ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x48ba00000620380c5c66002a64886c2c1a008a58189c240200bc463c94623a7892603254c4005010a4967c56985e7ebe9a04a60000a88e00a0765268009040c2b20a6a428684262ec0360000009e4e1c30aa281600228c3eb6b0006e80087a4caea2825ab84a121400ac44723400b40000741e000e70000469408002000018500123838200000800e0088306006820e0c106013d5490eeca321dd54643cfa9a873e5410eeca221dd54443af29e855d53d0aeca3a15d54742bba8a85745150a7ca9994f55332bb28e657551ccb3a87195dd4532ba28a653e540ca7aa8196750c32bb2886575510caf4a0195e54032af298835d531067ca998cf55331cea1e6375538c76e8718ed50e31bb294639d434c6dea498db14931eba9a63b7434c7ac8698ed50d31eaa1a6395434c7cea498dd14931f22926364524c67ca818cf55031bb288637753c86eaa790edd0f21daa1e437651886eea610dd54c21dba1843b543086eca410f994821f399043e432086eea2a05d14540af298815d53102dca4205b54840bb2888175511027ca9984f55330cea1e617651cc2eaa3986750d309f2a0613d540c2dca4185b54830bb2886175510c3c843905d94620baa8c413f5448278a89057d4d20ae29a417751482e8a2907908520b7294216d528427ea8884f15110
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x938030040a00010d20f0010804801c05004c60c54402c0a0c601af154354432c650d500cb0d4314931a5592434c78543d4931c550c524c7854314931c9d0c524c7464314931c950c524c7454314931c150c524c7175350f21c554d4308665650c821e150c32086e1600c821c550d51cc2646254730d114c214821d6315110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x80806056550c3208740a1ac0190438150c6254730
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
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (2904+((h/33+packedAt s4K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s4K3 (833+((h/7+packedAt s4K3 (798+(h % 7)*5) 5) % 30)*6) 6
  | 2 => packedAt s4K2 (150+((h/1+packedAt s4K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffff81f87ffe0e1fff0ffff8703ffc63f27f
  | 1 => 0xf83f0ffe007c3ff01e1ff1e07f803c1e5ccc67
  | 2 => 0xffc00fffff803fffe01ffe007fffc01f9f0f87
  | 3 => 0xfffffffc3ffffe000007fffffe3e00ff8
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x3082008c1088000202230223181084c401522b
  | 1 => 0x538c991475325a710f0d91456c83294a4ccc65
  | 2 => 0x21162228a018a0962016240a31258090970686
  | 3 => 0xc428cc4144420b2955408110464a3303600950
  | 5 => 0x86308871866333cd9998c99c040c2203faa000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfaeafaeafa80fa80faeafaeafa80fa80faeafaeafa80fa80faeafaeafa80fa80faeafaeafa80fa80faeafaeafa80fa80faeafaeafa80fa80faeafaeafa80fa80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36272
namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43ee42487da8490fd8c521fa98a43f721487dc4290dfd4121be282437f54086fca810df55021be2a0437f53086fca610df54c21be298437e52086fca210fdd0421fa20843ef21087ec4210fb48421fa908437e50086faa010df94f40bea9e81bf43d037a87a05f94b40bea96817e51d02faa3a05f55240bf29c817d53902fca5205f54a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be292817f51503eea2a05dd4540be28a81f451502e8a2a07ed0140df202817e54102fca6205f54c40bf290817d52102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9985f94b30bea96617e51cc2faa3985fd5230bf2a4617d548c2f8a9185f54e30bf294617d528c3bc6518770ca30bf28c617d518c2fca11877cc230fd984617f544c2fca8985f55130be2a2617f524c3dea4985bd4930be29261ec524c2d8a4985fd4530be28a61fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30bf29061ee520c2dca4185f54830f6a90616d520c3bc6418770c830bf28861f6510c2eca2185f54430faa886175510c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7907b8cb20f6996417e51c82faa3907ecc320fc186417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d52883de65107b0ca20bf28c417d51882fca1107e8c220fc98441ef20883f641105fd5120bf2a2417d54482f8a8905fd4d20efa9a415f53482fca6905f54d20be29a41dc53482b8a6907b8c920f6992417f51482f8a2907e8c120fc98241fb20483dc40905fd5020bf2a0417d54082f8a8105fd4c20bf298417d53082f8a6105f94820f799041ec32082fca2105f54420bf28041fb30083f060107bc8020fd10041ed20083f240107a48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec62887d4c510fd20221f940443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0x16000058000000140000400000000000002004020000000000080f00000000801002010000010020080080000803000000000000008090020000280000c0000000601a002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0997ed4132bda82657c504cbf0a0995e14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41bf296837d52d06fca1a0df54341beaa4837e53906faa720efd0e41dea1c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea9883bf431077a8620df94841f7290836e52106faa420fb54841b6a9083be42107788420df94441dfa0883f6411077a8220fd50441daa08837e50107f4a020de94041bea8083f950106f2a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998f790f31eea1e637e52cc6faa598df94331bea86637f548c6fca918df55231be2a4637d538c6fca518df54a31bf28c63f7418c7e88318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898f790d31eea1a637f524c6f8a498fdd0531fa20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb90b21f6a1643f741c87e88390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fd8c621fa98
  | 2 => 0x840000008a0d46000000000000000000000000000000860000014b36200000000000000000000000000010527a7b80000045a0006a22e0a809d188003e40000012d000000001ed00000000000000200000ac0001c0000000000000010e448000688000740000005b3f2000002230f60000d8c30000c86f8f1000378001200b412518000000000fa0a84562e8000791420d40000009c7340012c202388d10003fc91c000ec00014c0c9e0000184520810240000004a000658000003704a400000000000de80018205c8507f200001088002e40002200000000000000000000d70090000011e8310960000e800000000600000000000023a4121b8cfa4124e4ec738582b641c0012f07a8f0001ff3b80000000034e084c70660008a0002391c85180000000000000194000000001732dc068000000007480000025c7a45c8000ce000000000009108e0000ac0000020f00000000000000000ec21601c5380007c000000000003aa000ed80000033c1f00000078c0b00009a00000000070000d31bf1680ec5d89b020568000000000906c13200000000000000794368a50000000000000000000000000744d28ff00055857000000000598fe0000011100000000000000000000000000000000017731e00000000000000bf98d00027c0000035092454a2a2cc835041453303f4c98b01ea718399112ea524e50620d04211f0570000000019c0000000000c2f44a0000002ca000000e80002443ea1700000000000000000000001962c8000002a091841829000590000000005a00000021e000000001121dcc2000000001051f7000000000000000006293f0000010d85e0007245e0bd0e225400000386464000000000011f84743c8bc002010383080000000000000000000001101743740004c9cf0006a40f9780006e4758000788cc000000000011b8000000000021a000774000002040003799a000000001c80000000000040800000000230000670000000002a800000000719c0000000bf235000000000000000009e00000021400000000000000000002d5109d71561c8e600039c00000015000000c31d40007ec9200000046800000314000180002a60002e84848a4dc2e0062246f8a01df000690e9800000000000000020020040000000000c00801000004010000040000480c0020040300400c0080000300000000001004008000020000000200400201000001000000000000000000080000e0140100200000000800000004008040020000680000a0040080700400001801002000018070060000000000c010000000000080380a0020000000300000000805000000000000000080280000000c0200000a020000000000000000000a0040100800e004000000000000180200001002801000000070020000000000000000402
  | 3 => 0x8f8000000008a8000000e40018c14e6bcb89fa0000000c00037800000000000000000000000000000017c3a4000921b8000000003cc0007c94c0000000006400058c001910000006c9422b03301011d0000001b800218098698000003ecc380000084c4d0003e00000000000028c001510000000021800000000000000900ec8fa000000000000007bc300502662b48b0003ac8c8000000002784b16a000000000940ec2800005f1c057c002033e25c000161000000000000003d00000026a46c001760004a82000f08a5890700000000000000000000000000005f063000000000000860000000019d302000fe09329a000d00fc1da148a50901b600000000000920c80000000000000000013c0002f274564000000001ac0292304671cd091e05a34000000420000b60003f0000b5a1d22e1440000041622c0000000000000004000000d180000000017000000000000001f01f90f8003160000000000000041034000000000000001d05b8002c0000000882f27680000028e0ac001f530a00075000006000858000000008987520c00000000000000001c44860000010936c000db9f60000000000043855ca4087000854708f62706ecf5a3b3064c4142072282a89080b4705a4348114240b06387a3d4234e28c91ca000bd800000000002420003589800011804d148463e666c00122000000000000000000000000050c000c8000000e080042853c000003d00000000000023cd500032a0000000016c0000010d004000001b02da001031ec0000000000036a000000000000000003f06c000001c21ba000002002aa66400000000000000b83106c80013935a59d1b0001e0000f20b10000006b8001883dd162340004d00013e15e000000070007f4000a211c000000003586cc0006c0663cc0000000079c00000000000a900044a578000001305500400000040c00000000274001103a03bc0005900000000000396000790000006d00001e0000000000000000069000000000000000000000000000000000000000000000000000000000000018c000bf00064800000000028cb989282270530001b40003c0ee19a000000000440011312b404784420d500049400000000398ef0000000010295d000104a20970000003280033c7891380000086400000000000d580d1948302600000057000000000000000250000501517d0004100016f0020000012626c60800000000000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x53086766114c219e98053086796014c219d594410873554104219bd9521086776548421ad19121086766194f409d58653d02b96010640cdd0c51503354314540dc58051503345190140cd544411023f6550040ad185401027b65500409d98754cc27561d53309dd85548c2746155230b6580328c23f64546308f191518c26e62951309b58a544c26f62551309b189544c27761551309d185544c3696014930da14b304c34c528c1309b98b540c26d62d50309d987540c27561d50308f596540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830da181520c34d528c830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430da54a300c25f654c030b3189300c27b654c030ba189300c369524c0309d98754c827561d53208f99053c823d6414f209d98453c82756114f20ba18132c82e9620c320f28c830c827661d52209d587548823e6414e208f59053882766114e209d58453882e9600ca20f20ca30882e8624c2209798e544825d639512097d8d544825c63551209dd85544827461551209798e534826f6254d209ed81534823e6414d208f59053482766114d209d584534825e6514d20c7990534831d6414d20d358853483566114d20d558453483596014d209b996324834c538c9209b195324834c534c920ba181324827a658c120d614e30483ca328c1209e1953048358534c120ba189304835853c8120d314e204827761550209d185540825e63150209758c540827661150209d584540823e6414c208f590530826e6214c209d98453082756114c209e980530826d65cc8209b59432082e9600c8208fd91510823c64544209e5973008279650c020ba58830083c8320c020ba58a200826f6548020b318d200827b6548020b618d20082eb6548020dad9520083cb6348020ba98d20082e86348020f218d20082c86348020dad4d200836953480209798c54c425d63153109b98854c426d62153109b98b53c426d62d4f108f99253c423d6494f109798f52c425d63d4b109b98b548426d62d52108f990538423d6414e109b988538426d6214e108f993528423d64d4a10cdd5041842f16010610ec10640842f061502108f992544427761551108f994544433960151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c6354910cd1523144274654c510cd151314433854901109e195404433454841109798c540425d63150109b988540426d62150109e980540423e6414c108f590530426e6214c109b58853042766114c108f990520423d64148109798c520425d63148109d594410433554104109e59610042776544010ad191100427b6544010
  | 1 => 0x7800000002d8589c2000000024c0028222000030005900a00290ba2680597e0620e00232000003aa1e1f8006a8fe2419c00000258003b800000002f1720012ca380000152a500000188b40009e000000940a0001d000000003e8110140007002000100000d0180001801000020100101c00000090001000005020010080000c0400403010000000000000044000000001001000010040001405000070140700001014000000102002018070040800808000000040b00001020080000000c060000d04000004010040a00400004050040001c0100404004000040400802030000040100c0500001004000000400004000000340100005003374394643ad9864350e3f6550c4397d954310e766194f429d58653d0b374314542cd50c5150b3642145428fd954210ab461508429bd954210a7661d53329d58754cca7761552329d185548ca3f64546328f191518ca7a60951329e582544ca7761551329d185544ca7b60551329e181544cb6b3214132d68c8504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f990540ca7661150329d584540ca7a60150329e580540ca5f654c832b6181320ca6f654c832ba181320cb365494432cd552510cb365454432cd551510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb6a3254032da4c9500cb566194c41ad587431071e5350c41d394e521074d5394841d394d521074d5354841cbd0d521072d4354841d9185521072d5290841ad58442106b564904418fd9541106776550441add9541107376550441add8d41107965350441e554d41106b46250441e994941107a55250441ad181411075a5394041d654e501076a5294041da54a50107b14194041d694d50107595354041da94950107695254041ec505501073b4354041ce50d501071e6395331c795143cc66e62152319b588548c67a60152319e580548c7355410631b9588418c6f16010631ad993318c66f62551319b189544c67b60551319e181544c6d66190d3197195434c67665d0531cd550414c6d66310531e550c414c6e56210531bc580414c6b664cc5319d987540c65e63150319b988540c66d62150319e980540c67960150318f992530c63d6494c3197d95310c677654c4319e98354c867960d53218f99053c863d6414f219e98053c86796014f21b918542c87375410721b958841c87a642107219798c548865d63152219e980548867960152219e983538867960d4e218f992538863d6494e218f992544867761551218f994544872d62151218f992534863d6494d218fd91534863c6454d219ed8153486786054d21cb152424866c6550921cd1523148674654c521cd151314873454c85219798c540865d63150219b988540867a60150219e580540863e6414c218f59
  | 2 => 0x5d000002dc93800a48002718a0001e3591cb0882000ba0009e199945e2041f0002f8b4000000000057000000007380000000b3000001cc000005aa163d0000000000000b78000000000000978000012000000000000013ab880000000000c6759189b2a8002ca0000600000000861480000000001b24985c6090800228801a0001a8340f8200e04d93e000008a968361c80000000000880845e80081a54002480ca0a532e4001e40022691a6a47a0800000b827a7483e648a2370305821c000b29f00000276662da8e8a68b940669962a2626d048138649ba72268a015800849a2338000000043800000c2001ea00176b0054b200000000aa800162b00000030000001dc6102c080cc7e0240023c001e0ae9f2000763d86a6d9444a80000148001863227e7faf0a90923b002991066e80008800691be7611095930002188680016970bc800a8aa0a60501b80000000000004300000134000002e1027eabc398001ca6071a96a79aea71e60a92e0d9b01098083000728040004c000a4000000000018a9aa2808891bc128e81e80056932698409d166348981b2229608c751588c1ee002ec8e2c4538ac5f2d4488c40028c000006300000000998007b000181f08d0aa97000048007a00000242b4800000d45b800368000001a3f00054000002ac000000e000000f20000000000b3800b180000000842e66e0e40d00000000070000025aab800002f4740005095457800000002299e0011264044002be00146119388d9141a24a001ac4682e239fc94a40002504a1007d026002b42c0005b000000de8b000179c000286a0014b59563294aa121403ab60020204104ba9e20023e00000388f00000000000000007d80076800ae1dea20aea98004f000002ee000004583c001c4ac924428002d8700e98e91000000009c00000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4040a00434e0135002c70c018920044030049508f147400e020f82a9aa4a0883c454d4154041e42a4a0aa020d2472550414c698382a820a63a150d6210531d2286b008298d3270d5041c870ab22c229a419214c604c920a94eb194609064a658ca3048324298c498241329ce6348020c92ea31a401068a7418d2008344ba0c690041b09c46348020d82e231a401064863d4d20082343b2a690041499cb5410610
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2020c09755d06348020c41755c46348020c81745c46348020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (17967+((h/195+packedAt s5K5 (15822+(h % 195)*11) 11) % 1244)*11) 11
  | 4 => packedAt s5K4 (15662+((h/126+packedAt s5K4 (14402+(h % 126)*10) 10) % 605)*10) 10
  | 3 => packedAt s5K3 (1113+((h/7+packedAt s5K3 (1078+(h % 7)*5) 5) % 29)*6) 6
  | 2 => packedAt s5K2 (183+((h/1+packedAt s5K2 (180+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf81ff8f07f1ffe1e3c7f8fc078e07ff867c27f
  | 1 => 0x7fe1ffff801f1fe03f8ff1ffff00703998fc67
  | 2 => 0x7ffe00ffffe01fffc00ffe007fff803e1f0f87
  | 3 => 0x800000ffffffe1fffff000007fffffc7e00ff8
  | 4 => 0xffffff00000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xac41113122a0806141582491821158823c22b
  | 1 => 0x114c60210e4424600c82908769062290885c65
  | 2 => 0x2088b246240650aa400b2412324b01221d0686
  | 3 => 0x511448848100550a920002444944a05c00950
  | 4 => 0x4611800c7098999d324c493800180c0776a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80feecfa80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36272
namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c18001ffd5005fe5401ff55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03fe4300ff50c03fc4301ffd4807fe5201ff54807fc52017fd0801fe42007f50805fc4200ffcc803fe3200ff4c803fc3201ffd4407fe5101ff54407fc51017fd0401fe41007f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0001fe40007f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42000ff50210007f28108017fc4084013ff9842005ff8c21004ffa6108017fc3084001ff9042005ff88210007fa4108017fc2084009ff8842000fdc4210027f62108033ff65440197fb2a2000dfd9510004feca88033fe65440077f32a200cff59510065faca88033fc65440077e32a200cdf1951001cf8ca88003ff64440017fb222000efd91100057ec88802ffe64440057f3222000ff59110005fac88802ffc64440057e3222000ef1911001578c888033ff5444017ff2a2200cff5511005ff8a88802bff63440157fb1a200aff98d1000dfcc68802bfd63440157eb1a200aff18d1000df8c68802bff5344015bfa9a200aff94d10057faa68802b7d5344015fe29a200affd0d10057fc868802bfd4344015fe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e312200cffd4910067fca488033fd5244019fe292200bffd0910007fc8488003fd4244017fe212200affcc910057fc648802bfd3244015fe192200cffd4510027fca288033f65144019fea8a200cfd54510027f8a28802fff4144009ff20a2000ff50510027f8828802bff3144009ff18a200afd8c510057fa628802bf53144009fe18a2000ffc8510027fc4288003fd2144009fe10a200cffd4110067fca088033fd5044019fe282200bffd0110007fc8088003fa4044001fea022000fe5011005ff8808802bff3044015ff182200aff4c110057f86088003ff2044001ff1022000ff48110007f84088013ff1044009fd8822000ff84110007ec2088017ff65040097fb282004ff9941001dfcca08013fd65040117eb282005ff19410025f8ca08017ff64040097fb202004ff99010015fcc808013fd64040017eb202005ff19010025f8c808023ff540400fff2a02008ff5501003ff8a808017ff63040097fb182004ff98c1000dfcc608013fd630400d7eb182005ff18c10025f8c60801bff530400dbfa982006ff94c10037faa60801b7d530400dfe2982006ffd0c10037fc860801bfd430400dfe2182005ffd8810025fec408013fe62040017f3102004ff58810005fac408017fc62040097e3102008ffd4810047fca408023fd5204011fe2902007ffd0810007fc8408003fd420400ffe2102006ffcc810037fc640801bfd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841004dfcc008023ff500400bff2802008ff5401002ff8a00801fff400400bff2002000ff5001002ff8800801bff300400bff1802006ff4c01002ff86008003ff200400bff1002000ff4801002ff84008013ff1004009fb8802005ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0xbfe3208025fe9904012ff0c82002ffec210003fe61080097f3084000ff58420005fac210017fc6108029ffa884014ff944200a7faa210053fc5108027ffa084000ff90420007fa821004ffc4108025ff9884012ff8c420097fa621004bfc3108001ff9084000ff88420007fa4210003fc210802b7f3004014ffd402002ffca010053fd500800bfe2804013ffd002002ffc8010003fd400800bfe2004012ffcc02002ffc601004bfd300800bfe1804000ffc8020007de4010017fe2008001fd1004000ff48020007da4010003f92008009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2011bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262000bf59310027f8c988012fc64c4023ffaa62010ff9531008ffaa988043fc54c4009ffb1e2004bfd8f10027fcc788006fe63c4009feb1e200fbf58f10027f8c788012fc63c401fffa9e200fdfd4f1007ffca78803ffd53c401fbea9e200fff14f1007ffe878803ffe43c401ffea1e200fff10f10027fec588012ff62c4009ff3162000bf98b10027fac588002fd62c4009fe3162004bf18b1008ffea588047fe52c4023fea962011ff14b10087fe8588003fe42c4001fea162010ff10b1007ffe658803ffe32c401ffe996200fff0cb10027fea388013fe51c4009fb28e2004ff5471008feaa388013fc51c4009ffa0e2004ff90710027fa8388013fc41c4009ff98e2004ff8c710027ec6388013fd31c401ffa98e2004ff0c710027fe4388013fe21c4009fe90e2004ff0871008ffea188047fe50c4023fea862011ff14310087fe8188003fe40c4001fea062010ff1031007ffe618803ffe30c401ffe986200fff0c310007fe4188003fe20c4001fe9062000ff0831002ffecb0803aff658401dff32c2003bf99610077facb0803afd658400bfe32c2003bf1961002ffec908002ff648401bff3242002bf99210007fac908002fd648400bfe3242002bf19210077fea908037fe548401dfeaa4200dff1521002ffec708026ff6384013ff31c2001bf98e1004ffac708026fd638400bfe31c2001bf18e1004ffea7080277f5384013ff29c2009ff54e1004efaa708027fc5384013ffa1c2009ff90e1004ffa8708027fc438400bffb142000bfd8a10007fcc508002fe6284001feb142000bf58a1002ff8c508002fc628401dffa94200eff94a10077faa50803bfc528401bffa142000ff90a10007fa8508037fc4284013ff9942009ff8ca1004ffa6508027fc32840157eb0c200effd4610027fca30803bfd5184009fe28c200dffd0610027fc8308003fd4184009fe20c2009ffcc610027fc6308027fd3184009fe18c2000ffc8610027fc4308003fd2184009fe10c2004bf98210077fea108017fe508401dfea842005ff1421006ffe8108017fe4084001fd2
  | 2 => 0x2002ffec710056ff638802bff31c4001bf98e200affac710056fd638800bfe31c4001bf18e200affea7100577f538802bff29c4015ff54e200aefaa710057fc538802bffa1c4015ff90e200affa8710057fc438802f7eb14401bffd4a200dffca51006ffd5288037fe294401affd0a20007fc8510003fd4288035fe2144015ffcca200affc6510057fd328802bfe1944005ffd8620007fcc310012fe6188001feb0c4000bf5862002ff8c31006fff5188037ff28c401bff546200dff8a31006bff4188001ff20c4000ff506200d7f88310057ff318802bff18c4015ff4c6200aff86310003ff2188001ff10c4000ff48620007f8431004afe6088037ffa844005ff942200dffaa110017fc5088035ffa044005ff90220007fa8110017fc408802bff9844005ff8c2200aff46110057fd308802bfc9844005ff0c220007fe4110003ef2088001fd9044019ffd95200cdfeca900037f65480013fb2a4019ff9952001dfcca90067fd65480337eb2a4019ff1952001df8ca900677c65480073e32a4000ffd9120005fec890063fe64480057f3224000ff59120005fac890063fc64480057e3224019ffd51200c7fca890067fd5448031fe2a24017ffd8d200bdfec690003df63480016fb1a4017ff98d2000dfcc69005ffd634802f7eb1a4017ff18d2000df8c69005fdc63480036e31a4017ffd4d200befea69005ffe534802ffea9a4017df54d200bff8a69005fff434802fff21a4017ff50d200bff88690067ff5248033ff2924019fb949200cffaa490067ed5248033fe2924018ffd0920007fc8490003fd4248031fe2124017ffcc9200bffc649005fee324802ffe9924017fb4c9200bff86490003ff61480017fb0a4000ff98520007fac290003fc61480097e30a4019ffd45200cffca290067fd5148033fe28a4018ffd0520007fc8290003fd4148031fe20a4017ffcc5200bffc629005ffd314802ffe18a4000ffc8520007fc4290003fd2148001fe10a4019ffd41200cffca090067fd5048033fe2824018ffd0120007fc8090003fd4048031fe2024017ffcc1200bffc609005ffa304802ffe9824017fe4c1200bff86090003ff2048001fd9024000ff88120007dc4090017ff65080297fb284014ff9942001dfcca10053fd65080297eb284005ff1942001df8ca10017ff64080017fb204013ff99020015fcc810003fd64080017eb204005ff19020015f8c810053ff5408027ff2a04014ff5502009ff8a810017ff63080257fb184012ff98c2000dfcc61004bfd63080257eb184005ff18c2000df8c61004bff5308025bfa984012ff94c20097faa61004b7d5308025fe2984012ffd0c20097fc861004bfd4308025fe2184016bf988200a7fea410053fe5208029fea904014ff1482009ffe8410003fe4208001fea104013ff10820097fe641004
  | 3 => 0xe20c8020ffcc640107fc6320083fd3190041fe18c8000ffc8640007fc4320003fd2190001fe10c8002bf9824010ffea120017fe5090043fea848005ff14240017fe812000bbf4090005fda048005ff10240017f08120083ff309000bff1848020ff4c24002ff8612007fff655003f7fb2a801fff9954001dfccaa007ffd655003f7eb2a801fff1954001df8caa000aff6450005ffaa28002ff951400177ca8a000bfd545003fdeaa28002ff151400f7fec6a007aff635003dff31a8001bf98d400f7fac6a007afd635003dfe31a8001bf18d400f7fea6a007b7f535003dff29a801eff54d400f6faa6a007bfc5350005ffa1a8002efd0d40017fc86a000bfd435003ddea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc625003fffa92801fff949400fffaa4a007ffc5250005ffa128002ff90940017fa84a000bfc425003dff992801eff8c9400f7fa64a007bfc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8004bf185400fffea2a007ffe515003ffea8a801fff14540017fe82a000bfe4150005fea0a8002ff105400f7fe62a007bfe315003dfe98a801eff0c540007fe42a0003fe2150001fe90a8000ff08540015fec0a007fff505003fff282801fff541400fff8a0a000bff4050005fda028002ff901400077c80a000bfc4050005de2028002fe101400f7fe60a007bfe305003dfe982801eff0c1400effecb90076ff65c803bff32e4003bf997200effacb90076fd65c803bfe32e4003bf19720007fec990002ff64c8039ff3264002bf99320007fac990002fd64c8039fe3264002bf193200effea990073fe54c803bfeaa6401cff153200b7fec79005aff63c802dff31e4001bf98f200b7fac79005afd63c802dfe31e4001bf18f200b7fea79005b7f53c802dff29e4016ff54f200b6faa79005bfc53c802dffa1e4016ff90f200b7fa879005bfc43c803bffa96401dff94b200efdca590077fd52c803bf6a96401dff14b200e7fe8590003fe42c8001fea16401cff10b200b7fe659005bfe32c802df71964016ff4cb200b7da659005bfc32c8001ffb0e4000ff98720025fcc390003fd61c80017eb0e4000ff187200effea390077fe51c803bfea8e401dff147200e7fe8390003fe41c8001fea0e401cff107200b7fe639005bfe31c802dfe98e4016ff0c720007fe4390003fe21c8001fe90e4000ff087200effea190077fe50c803bfea86401dff143200e7fe8190003fe40c8001fea06401cff103200b7fe619005bfe30c802dfe9864016ff0c32002ffecb1006eff6588037ff32c4003bf996200dffacb1006efd658800bfe32c4003bf1962002ffec910002ff6488035ff3244002bf99220007fac910002fd648800bfe3244002bf192200dffea91006bfe5488037feaa4401aff152
  | 4 => 0x8a3fd544844ffe2a24226ffd8d21135fec69089bfe63484037f31a4226ff58d21135fac69089bfc63484037e31a4226ffd4d21136fea69089bfe534844dfea9a4226df54d21137f8a69089bff434844dff21a4226ff50d21137f886908a3ff5248451ff2924228ff54921147f8a49089fff4248401ff2124200fb90921007fa8490803ed424844ffe2124226ffcc921137fc649089bfd324844dfe1924228ffd4521027fca2908a3fd5148409fe28a4227ffd0521027fc8290803fd4148409fe20a4226ffcc521027fc629089bf6314844dfe98a4226fd4c521027f86290803ff2148401fb90a4204ff88521027dc4290803ff60484017fb024200ff98121007fac090803fc60484017e3024228ffd4121147fca0908a3fd5048451fe2824227ffd012113ff8809089bff304844dff1824226ff4c121137f86090813ff65084097fb284204ff9942101dfcca10813fd65084497eb284204ff19421025f8ca10813ff64084097fb204204ff99021015fcc810813fd64084017eb204204ff19021025f8c810893ff5408447ff2a04224ff5502111ff8a810813ff63084097fb184204ff98c2100dfcc610813fd63084457eb184204ff18c21025f8c61088bff5308445bfa984222ff94c21117faa61088b7d5308445fe2984222ffd0c21117fc861088bfd4308445fe2184225bf98821127fea410893fe5208449fea904224ff1482111ffe8410803fe4208401fea104223ff10821117fe641088bfe3208445fe9904222ff0c821025fcc210813ff5108409ff2884204ff54421027f8a210813ff4108447fba084204ff90421027fa8210813fc4108409fa2084204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da4210803f52108409ffb004204ff98021005fcc010813fd60084017eb004204ff18021127fea010893fe5008449fea804224ff1402111ffe801088ffc4008445ff9804222ff8c021117fa601088bfc300840bffb2c8021bfd964010ffccb2000efe6590043feb2c8021bf5964002ff8cb2000efc65900057eb248002ffd5240017fca92000bfd5490005fe2a48005ffd8e40105fec720083fe63900037f31c8020ff58e40105fac720017fc63900037e31c8020ffd4e40106fea720083fe5390041fea9c8020df54e40107f8a72000bff4390005ff21c8002ff50e40017f88720017ff6290001ff3148000bf98a40007fac520002fd629000bfe3148021ffd4a4010ffca520087fd5290043fe2948002ffd0a40017fc852000bfd4290005fe2148020ffcca40107fc6520083fd3290041fe1948005ffd8640007fcc320012fe6190001feb0c8000bf5864002ff8c320087ff5190043ff28c8021ff5464010ff8a32000bff4190005ff20c8000ef90640017fa832000bfc4190005d
  | 5 => 0x854117ffea2a0813fe515045ffea8a8204ff14541017fe82a080bf74150409ff20a8204ef90541027f882a0813bc4150405fa20a8202ed10541177fe62a0813fe315045dfe98a8204ff0c541007fec0a0802ff6050401ff3028200ff58141007f8c0a0802fc605045fffa82822fff9414117ffaa0a08bffc5050405ffa028202ff10141177fe60a08bbfe305045dfe982822eff0c14116ffecb908b6ff65c845bff32e4203bf9972116ffacb908b6fd65c845bfe32e4203bf19721007fec990802ff64c8459ff3264202bf99321007fac990802fd64c8459fe3264202bf1932116ffea9908b3fe54c845bfeaa6422cff1532112ffec790896ff63c844bff31e4201bf98f2112ffac790896fd63c844bfe31e4201bf18f2112ffea7908977f53c844bff29e4225ff54f2112efaa790897fc53c844bffa1e4225ff90f2112ffa8790897fc43c845bffa96422dff94b2116ffaa5908b7fc52c8459ffa164200ff90b21007dc8590803fd42c8401f6a16422cff10b2112ffe6590897fe32c844bfe9964225ff0cb2116ffea390813fe51c845bfea8e4204ff14721167fe83908b3f741c8409ff20e4200ff50721027f883908b3f441c844bff98e4204ff8c72112ffa6390813fc31c8401ffb064200ff98321005fcc190803fd60c84017eb064200ff1832116ffea1908b7fe50c845bfea86422dff14321167fe81908b3fc40c844bff9864225ff8c32112ffa6190897fc30c8409ffb2c4204bfd9621027fccb1080efe6588409feb2c422bbf59621027f8cb10812fc6588409ffb244204bfd9221027fcc91080afe6488409feb244200bf59221027f8c910812fc6488457ffaa4422aff9522115ffaa9108abfc5488409ffb1c4204bfd8e21027fcc710806fe6388409feb1c4229bf58e21027f8c710812fc6388453ffa9c4229dfd4e2114ffca7108a7fd5388453bea9c4229ff14e2114ffe87108a7fe4388453fea1c4229ff10e21135fac5108afff5288457ff294422bff54a2115ff8a5108abff4288401ff2144200ff50a21157f885108a7ff3288453ff1944229ff4ca2114ff86510812fe6188409ffa8c4204ff94621027faa310813fc5188409ffa0c4204ff90621027fa8310813fc4188409ff98c4204ff8c621027ec6310813fd3188453fa98c4204ff0c621027fe4310813ef2188401fb90c4204ffd8221027fcc110802fe6088409feb044200bf58221027f8c1108afff5088457ff284422bff5422115ff8a1108abff4088455fe2044229ffcc22114ffc61108a7fd3088453fe1844228ffd9521145feca908a3fe65484077f32a4228ff59521145faca908a3fc65484077e32a4200ffd9121005fec890803bf64484015fb224227ff99121015fcc890803fd64484017eb224227ff19121015f8c890803bc64484055e3224228ffd512113ffca890
  | 6 => 0x77fb2a8433ff9954201dfccaa10cffd65508677eb2a8433ff1954201df8caa100aff6450805ffaa28402ff951420177ca8a100bfd5450867deaa28402ff15142197fec6a10caff6350865ff31a8401bf98d42197fac6a10cafd6350865fe31a8401bf18d42197fea6a10cb7f5350865ff29a8432ff54d42196faa6a10cbfc5350805ffa1a8402efd0d42017fc86a100bfd4350865dea1a8402ff10d42015fec4a10cfff5250867ff2928433ff5494219ff8a4a100bff4250805f7a128402ff909420077c84a100bfc4250805de2128402fb10942197fe64a10cbfe3250865fe9928432ff0c942007fec2a1002ff6150801fbb0a8400bdd8542007fcc2a1003fd6150801fe30a8404bf18542007e8c2a1002f46150867ffa8a8433ff9454219ffaa2a10cffc5150805ffa0a8402ff10542197fe62a10cbfe3150865fe98a8432ff0c542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050867ffa828433ff9414219ffaa0a10cffc5050805ffa028402ff10142197fe60a10cbfe3050865fe9828432ff0c142027fecb20812ff6590409ff32c8203bf99641027facb208c6fd6590409fe32c8204bf19641015fac92080bff5490405ff2a48202ef95241017faa9208c7bd5490405fe2a48204ffd8e41025fec720813fe63904037f31c8204ff58e41185fac720813fc63904097e31c8230ffd4e41186fea7208c3fe5390461fea9c8230df54e41187f8a72080bff4390405dfa1c8202ff90e41017fa87208c3bd4390405fe21c8204ffd8a41027fcc520802fe6290409feb148200bf58a41027f8c5208c7ff5290463ff2948231ff54a4118ff8a52080bff4290405ff2148200ef90a41017fa852080bfc4290405de2148230ffcca41187fc65208c3fd3290461fe1948204bf98641027fea320813fe5190409fea8c8204ff14641027fe8320813bf4190405fba0c8204ff10641027e88320813ff3190409ff18c8204ff4c641027f86320813ff6090409ff3048200bf98241027fac120802fd6090409fe3048231ffd424118ffca1208c7fd5090463fe2848202ffd0241017f8812080bbc4090461ff9848230ff8c241187fa61208c3fc309045fffb2a822fbfd954117ffccaa080efe655045ffeb2a822fbf5954117ff8caa080efc65504097fb228202ffd5141017fca8a080bfd5450405fe2a2822effd8d41175fec6a08bbfe63504037f31a822eff58d41175fac6a08bbfc63504037e31a822effd4d41176fea6a08bbfe535045dfea9a822edf54d41177f8a6a080bff4350405ff21a8202ff50d41017f886a0803ff62504017fb128200ff98941007fac4a0803fc62504017e312822fffd494117ffca4a08bffd525045ffe2928202ffd0941017fc84a080bfd4250405fe212822effcc941177fc64a08bbfd325045dfe1928202bfd
  | 7 => 0x2802600000000402400600400401200000400600e00000c00000000a03200000801e00000000400e00000c00205000a00400000000002e01000400000000800800000e00801200204a00600003400e00600800200a00200000200200e00001e01802c00000e00000601600c00800604800200400401000400200000800000200800000200200400000000800600001e00201a00000a05400200400200a03000200400400401400a00000400400200602c04c00000000000c00200600200a00201000601e00200e02800805800200201400800000801a00600000000000200000000000a00003406000000405200402000000802600200000600000800800600000000e00002400401200000e00001200000c06000200000200600000800000000203401400200807201400400208400600200800a00200800200400201601c00c00600e03c00800e00400c00400600e00000004a01201200800200200002600001200400000c00e04800002200000e02a00200200a00000000e00001202200200000200400003a00600001400e00600001002601000204200400801201600001e01601a00803a00200800000001400603e00200200400000c00602600c00800000001a03a04a00200200001e00000a00800c03c00600000802600403400000201c00601a00800000e00801400a08a00001200000802c00000600400400401200e00200000000000e00804800000a02401005a00002c00802404200200200001c00000404e00000400c00400400201e00a00202a00000000403a02001400002600001200200800802003000004001200000400001c03800a00202800000c00c01401200409801200400a00000200000400601600000001001002c00600600200400c00401a00c00201200c08801401c01c02235ffd96421adfecb210d7fe65908077f32c8435ff596421adfacb210d7fc65908077e32c8402bf59242017fea92100bfe5490805feaa48402ff152421a7fec7210d2ff6390869ff31c8401bf98e421a7fac7210d2fd6390869fe31c8401bf18e421a7fea7210d37f5390869ff29c8434ff54e421a6faa7210d3fc5390805ffa1c8402ff90e42017fa872100bfc43908057f3148435ffd4a421affca5210d7fd529086bfe2948402ffd0a420177e852100bef4290805fe2148402fb10a421a7fe65210d3fe3290869fe9948434ff0ca42007fec321003fe61908097f30c8400ff58642005fac321003fc619086bffa8c8435ff946421affaa3210d7fc5190805ffa0c8402ff106420177883210d3ff3190869ff18c8434ff4c6421a7f86321003ff6090801ff3048400bf98242007fac121002fd6090801fe3048435ffd42421affca1210d7fd509086bfe2848402ffd0242017f881210d3ff3090869ff1848434ff4c2421a7f861210cfff655086
  | 8 => 0x8ca8bf426cc2cbe562c00000041cb09434000bc0000cc862c000ac4000000000f040002ec00012c9dc305510000000001408b740000000000000000007c000000000146c0004bd8083506f0a68000f248bc0004900000010754d800000000000000000154c00000000000028400000000182c0010e80016b94d0001090acc8ecd9958d32434c71800078d94572c0013848e04400014dd67c0017a4ab0154c1448d6fd7a01212d149d1fcf092280000000006f4d19888751718000d54e9cab80009316c000079800138c1bd59976c2e153d4b47ad8ec0000009e40018580019558e8280c240fc9cc758ec86ec6f86c80002cc2157889b8000e054100000011346a9068000000000000f5d6840001c592800129cf7426000000106ca5494ca0532d2686bc84c0017b88cc8218d400125d40000108400000000000000000000000051c318000b20000000a441708743b8b90fb955c4b00008487b8000474e98cdc9e18fd47400083913c0011540000000000c17300000004000003495c41ad1f53dc9581d05a87c4d70e493b10b577d7903b0ef10783fce658910c99247a0a88fb43841b45fca39835249870b2c7644142213e0a6c000f68000000000000000bfd2f054400000173c0018ccf348ad2a40000011840011104a0124000000000000000000000000000f3c000f208f00000000000003e800000189d4ac000000c000014c4fc84640001a400042c00000000139505400056d4e4b44000b298a8e3063cb0510c5d8514000bc4fcd1383908813e818d0c00148780000015840001a000000108c29ca70ed00018114194203ec0000000006b40006e000000109c000001644f6c000afc000130000b70d640011e4700ad4000b68f64000000000000000650001949120000090d2c000ef917c3f00003e40002f80a80016600000000000003b54451411580000017fccfc0013340000012e800156152c0003c8914b500000012185cc0018ac000fa1230f381081586d04580000a0fd0d580007880000000000000616a9695770624908fc0000658a7940cee50bcb55734b7c0000018797c13742114a0300d4527518905ca9473404c2d12d400076810400055579d4fcf2874193d628ce8001361894d34dd425c5380018c000009c000dec000cc40011bcf78a84000e1820800007132847800049c0012c10941d9270259960f318e4000b59119224b4c00000c00000000400400000000400000201e00800802a00000000000000603a00600000800000000000c00c00200001401000c00001e03c04e00002004000400000000402a00800a01800a00000000a01c00800e00000c01401004201201400400600601605201400c00000000000600000600403a01a00000001201a00005e00000000400201200000a0080020000020000020000140140040000000
  | 9 => 0xb92051e98392502286149012551d08b83943811c09697013f50054656d48502b1740bb8690420a500b452c71123c4388346e9350845518e0cea95805ec9b4a61874ddc7d4a10e3ca400dc25195c57896c7843380f814d14c3d12cd8a0fe80041f80b84f418185d34452572457481d4393a03a46ccb408e4681314b10dd04c16747d939d7d5290e38000da45d46947208883980016ed264d1066c0000003ac33c44c37502d42c000000000000310e244b4000f5988150c000000f700000000b07bc73cb8d1612400d80bd8bc9519150093818489745600012dd21c080644f90ae0a9c000000001238278ffc0013d09617787e15e4e517494f11797946302c92092453ad7c40945a4ad03d51e18242bd5c8e60b88715450270000edc3cd1641680007cc000001704b1d8c90b08f8c9d3883884a456455d8d90c56ace283082f1430744000af14a4629554000d480009d4569630ae58b0638bb0e210eccd8c75860604fc590503139021caf937cff859cd243a8238664010e2d34cb9d5d87b0d6c529634c6d6dcebc000144dd95a86b044475ca30364480d78cd0000c09365070a4cc41000594298cccdf05414940000000000017b0dfc6686d8c9436d6a12b090470c8a544039c1e5619544d3d5c0001040000001150000000ec4001710001454000a5cb198f80002e511c1397641d43e1574000295448000cb80017080000000012bcad800091000165c1f40018697e4e002316f06dc188469538000a9038d16845cb304353f80f0654344c04cf85f03a008c0a4670378eac2a961c0000000000001e9800e116109b0af4000a6584c65c2041951dc0c51d4cbc028a80b942b51cc1c80017a8000abd21522cba0000d295e011d9407a88e881962564061ce940000000e0000859568150000ae89a8cc0cb48d524c000000a0d52497c0018f0000a093d8000451298c700000015f4000aac6480000004280000000000005f8b4822d63cc840007e88110240308856e15b45510d935c5353716f487cde80008c56901dc640e1400072c9f41156e893c1497f54f8aecadc0000012953994784cc570e34000b8400000183cac80011a98500000002ac369930000000f1800016c865280a1cca58458b90e12b581cd301fd4a80000000000003700097ad6b43bc00047000143c0001b82a00000000009f97ec000000334d50000890000bd964c00155877ce444040000000012a0000fac0009380012fc0004d59681c0b781ec86948c000000d813c89449fce7c0010285c09f05f54ed7d13fc00030c0009aceb157840cbd58dc23c00000145d0994e8ce400000000086c0006ad3d48147b4760ba87707788617516c89c0634ac191027435837d0647056641e01cc198de0841604e549209295ec2901f06a45c8f8d1043602c4b3c7094d4c7c000620828d0150895467
  | 10 => 0xed31800112d27d1a11b0df48f4da84f8448bec00047c4191915140000000000000011240007a4b0d9640000ac000000000b393ec68566d234c3ced51945dd70c19071ce7904c4b9688ee15fc1017e851933cd085bd534b60bbc9d005815d5cd304dc8c8c06c2d53c4eed6b00184dd47cd8c580c609bc0440016d00010ad144d4cd88000001424a14000ed95d52ed41c000c54f4400083d6800011c8488c680011ed4e10f850926c000dbd86ca48d1c000f1c0000000010100000000000009e8000000000268558000000a2d378ab4000000000000000e1d3b490c000b980000000008c00015f82f4000824000bcc0f46fc48485557c0014f55e9044000e84bf9050dad31c4fc5ac0002357bcc8903c50c98c2180012600004e8dc0e680015ac780a580000001780012c40000008a0b6cd94610f14000b64c449791302540001a80000007f4000a28fbc64cb240009c990003c000000e091280002fd01c7e40000016bd5d000000000077400046cd2099c001198fdc13c000c640880e45a167959489cbb51b58209a4c213a980404099083147076d4b00d0d14d74c1d798000e5d6d80009881b0000804a3d2105d00012a8000aa8c0c0019344108d0d38001768c90d68c580007f94c80002a55515054282d91158e080d258f5549960c8b0000000000000000de4000980000f0c60d034cb00013084e169d8f528ca8d5b0d915200012c93a445575402cf4c4610202c05306b80484316689c45e9354ff06e4c5d3f178400031cc484e4000ea403400169800093417c57d540d0458d1a4fe0790c31458000f94e40000f2d1b8c352e4f4151d81882cf9995074c7297b43247ecef51ad46907d4bc0012d9530e90f106899200000000009a13214810a8000ba40245e4cec001015148755898a3491c6747941616544d0f809649940d43f47d0eb8a74d7c72534800148916d6012f880930c598cf17389257744ed0f0020d9c6c578c00032c6980008a930000059060010d0384d90a01658310f5058d8453c000000ce0000000fa8b80000000000ec0d609ec68c00000159d7cd8c47fd75c6a00007382e800168d27800000000000000188cf840000000009d971c000000c280014b800098485cca00000016a4998000c784c8a240010d56f946190c9700000000004c4d417c95bcf7cf00918584f88f496387f1100a7c79d908b5c05d74434080000095c8dc498898cd4000000f613c00007dc5b9855721485648000e740019586c180c67c0015282000847c9728bdd44cfe58a50dc92d2b81410180000015882b915d7dd5a1174ff400192d87cc10a180000003c44942655001340e83dc00028d5dcaa593920d0e4000c380000cc61807d2ad0d088c4a988469d4cc0c80515910a591cbe8184e891700011d97f801c00c7314c0660b3443cc1996d7140ed358bad
  | 11 => 0xaa006419cbd0000000fd4078b010493bc000efc5b51f08b48fce70118fb0000000b1417518c500000000d5d7e1971080db40016e4245311285760ea1200749564a214917d96156cc0005b06098640004f18142dcdb1180eccda08d80013b8001548e6d0cc51032119d65800136c0018414144ac54d33174c289338894bf0df8be000194d91827d404000dc46d40540983c13cceb43d8cf5340521060589828fa5088504248128db91080008c89400003295b9758354000bc92f45c43f8000dcce8c000315288c98e812200015f0000000a000000000011c400160800024d6205e00002400740016715a4000c80cac00040978020c0000000000000004241110fc870000e4d8d0000948ee80392e0f50a98331650c4cfd8000f9c0002240015700691f8e5956d3e56c5368d0d7f18b4c5054835d00cf
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc6448110005df7348110055dc7348110006ef6248110006ec6248110005f77148110025f47148110004fe76081100067f65081100a67c6508110006bf640811009ebc6408110007e920081100067f65841100767c6584110006bf648411006ebc6484110025fa7084110026fb6084110025f6768411002ef67684110024f6768411002df775841101ddf575841100077765841101d7746584110007b76484110007b4648411002df773841101cdf573841101c77753841101c775538411002df6708411002ef76084110027f3608411002ff24084110007f14084110004ff755901001cfe7559010004fd755901001cfc755901002cff745901002ebf745901003ebe5459010006bd5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d535901003ebf4359010006bd4359010004ff7259010004fc725901003ebf4259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc4159010014ff705901002cfe7059010014fd705901002cfc705901002ebe405901002ebc4059010026fa1059010026f91059010004ff759881001cfe7598810004fd759881001cfc7598810014fe7498810004fd7498810014fc7498810004ff739881000cfe7398810004fd739881000cfc73988100067f53988100067d539881002cfe729881002eee7298810006ee5298810006ed5298810006ee3298810006ed3298810024fe7198810024fc7198810026ee2198810026ec219881002cfe709881002cfc709881002eee209881002eec2098810004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d535881002cff725881002eef7258810006ee5258810006ed5258810006ee3258810006ed3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec21588100b4ff705881002cfe70588100bcfd705881002cfc705881002eee205881002eec2058810004ff769081002cfe7690810004fd769081002cfc7690810006ee6290810006ed6290810004ff765081002cfe7650810004fd765081002cfc7650810016be6450810006bd6450810006ee6250810006ed6250810005f77150810025f4715081006cff765001006efa6050010004fd76c8010004ff76480100057f75480100457c7548010005df7348010035dc734801002df77644010006f77644010004f776440100077775440101bf74754401002ef765440101bef56544010007b77444010007b4744401002ef763440101b6f563440101b77753440101b775534401002df77044010027f3704401002ef6604401002ff2604401002ff22044010007f12044010
  | 1 => 0x891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef7258910004ff7158910006f77158910006f63158910006f53158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006ed6218910004ff751891001cfe7518910004fd751891001cfc7518910014fe7418910004fd7418910014fc7418910004ff731891000cfe7318910004fd731891000cfc73189100067f53189100067d5318910006ee7218910006ef3218910006ec3218910024fe7118910024fc711891002cfe701891002cfc7018910004ff7690910004fe7690910004fd7690910004fc76909100067f65909101ae7c6590910006bf6490910016bc6490910004ff7650910004fe7650910004fd7650910004fc76509100067f655091019e7c6550910006bf6450910016bc6450910005f77150910025f47150910014fc76505100067f655051017e7c6550510006bf6450510016bc6450510027b44150510005fb7050510005f87050510004fe76c85100067f65c851016e7c65c8510006bf64c8510166bc64c8510006ef62c8510006ec62c8510005fa70c8510005f970c8510004fc76485100067f65485101467c6548510005bf744851005dbc7448510006bf644851013ebc6448510006ef6248510006ec6248510027e42148510005fb7048510005f87048510027f01048510084fe76901100067f659011010e7c6590110006bf6490110016bc6490110005fa7690110086fa76901100077b659011020778659011005df97490110007bb6490110016fa6490110016f8649011005fb86490110016b864901101f77b53901101f7795390110025fa7190110025f8719011002efb6190110207f25190110207f151901101ffba41901101ffb841901101f7f231901101f7f13190110014ff765011005cfd7650110024fc76501100067f65501100fe7c6550110006bf6450110016bc6450110005f77150110025f47150110025f87650110016f87650110024f876501100077b65501101ef78655011005dfb7450110007bb7450110007bb6450110016fa6450110016f8645011005fb8645011005fba54501101efb954501101e77b53501101e779535011005fbb43501101e7b94350110007f37150110025fa7150110025f87150110007f071501101eff251501101eff151501101e7f231501101e7f13150110024fe76c81100067f65c81100ee7c65c8110006bf64c81100e6bc64c8110006ef62c8110006ec62c8110025f671c8110005f571c8110004fe76881100067f65881100de7c6588110006bf64881100d6bc6488110004ff7648110004fd7648110024fc76481100057f75481100657c75481100067f65481100ce7c6548110006bf64481100c6b
  | 2 => 0x6bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d91101febe71d9110006bd71d91101febc71d9110006bf51d91101febe51d9110006bd51d91101febc51d9110006bf31d91101febe31d9110006bd31d91101febc31d91101febe21d91101febc21d91101febf70d911005ebe70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d91101febf10d91101febc10d91100057f75591100657c75591100067f65591100067c655911005ebc6459110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c755911005cff7459110006bf7459110004ff735911000cfe7359110004fd735911000cfc73591100067f53591100067d5359110004ff7259110004fc725911006cff7159110006f77159110084ff7059110006fb7059110005be761911005ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100073f53191100073d5319110007b65119110007b55119110007b63119110007b5311911005fb9701911020ebf601911020fbb101911020fb810191100067f65d89100067c65d8910006bf64d8910006bc64d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef32d8910006ec32d8910006f631d8910006f531d89100657e75989100057d75989100067f65989100067c659891005dbe7498910005bd7498910006bf6498910006bc6498910006ef6298910004ff759891001cfe75989100067e759891001c7e7598910004fd75989100067d75989100047d759891001cfc7598910014fe7498910006be7498910014be7498910004fd7498910006bd7498910004bd7498910014fc7498910004ff739891000cfe7398910004fd739891000cfc73989100067f53989100067d5398910004fe7298910004fd7198910006f57198910004fd7098910006f970989100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910055dc7358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735
  | 3 => 0x8419021003cff7650210005fb765021003efb765021002fbb7450210016fa6450210016f8645021006fba5450210237b9545021022f7b535021022f79535021006fbb435021022fb94350210025fa7150210025f871502100057f75482100757c7548210005df734821004ddc734821002fe8204821002df576c4210026f576c421002ef765c4210226f565c421002ef763c421021ef563c421021f7753c421021f7553c421002ff260c42100657e76d95100667e76d951001c7e76d95100067e64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100077771d95100677471d95100077631d95100077531d95102177b10d95102177810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95102167e71d95100667d71d95102167c71d95100067f41d95102167e41d95102167c41d95100067f31d95102167e31d95100067d31d95102167c31d95102167e21d95102167c21d95102167f70d95100667e70d95100667d70d95100667c70d95100067f40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d95102167f10d95100667d10d95102167c10d9510014fe76d91100067f65d91100067c65d911005ebe64d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d911005ebe54d9110006bd54d911005ebc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d911005ebf43d9110006be43d9110006bd43d911005ebc43d9110004fe72d9110004fd72d911005ebf42d911005ebc42d9110024fe71d911005cfd71d9110024fc71d911005ebf41d911002cfe70d9110024fd70d911002cfc70d911005ebf40d911005dbe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100073f53d91100073d53d9110007b651d9110007b551d9110007b631d9110007b531d91101ffbb70d91101ffbb10d91101ffb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110
  | 4 => 0x9210004fd75d921002cfc75d921006cfd74d921002cff73d921000cfe73d9210004fd73d921002cfc73d92100067f53d92100067d53d9210004fe72d921002eee72d9210004ee72d9210004fd72d921002eed72d9210004ed72d921002ef571d92101febe41d92101febc41d921002efa70d9210014ff765921002ebc6459210004ff755921001cfe7559210004fd755921001cfc755921002ebf745921006ebe5459210006bd5459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d535921006ebf4359210006bd4359210004ff7259210004fc725921006ebc425921006ebf415921002cfc705921002ebe405921002ebc405921002cff75d8a1001cfe75d8a10004fd75d8a1002cfc75d8a10014fe74d8a1002ebe74d8a10014be74d8a10004fd74d8a1002ebd74d8a10004bd74d8a1002cfc74d8a1002cff73d8a1000cfe73d8a10004fd73d8a1002cfc73d8a100067f53d8a100067d53d8a1002ef571d8a1002efa70d8a10004fd7698a1002eef6298a10004ff7598a1001cfe7598a10004fd7598a1001cfc7598a10014fe7498a10004fd7498a10014fc7498a10004ff7398a1000cfe7398a10004fd7398a1000cfc7398a100067f5398a100067d5398a10006ee5298a10006ed5298a10006ef4298a10006ec4298a10006ee3298a10006ed3298a1002cfe7098a1002eee2098a1002eec2098a1002eec6258a10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a10014fe7458a10014fc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a1002eef7258a10006ee5258a10006ed5258a10006ef4258a10006ec4258a10006ee3258a10006ed3258a1002cfc7058a1002eee2058a1002eec2058a1002cff7518a1001cfe7518a10004fd7518a1002cfc7518a10014fe7418a10004fd7418a1002cfc7418a1002cff7318a1000cfe7318a10004fd7318a1002cfc7318a100067f5318a100067d5318a10004fe7218a1002eee7218a1002ef57118a1002efa7018a10004ff7690a1002cfe7690a10004fd7690a1002cfc7690a10016be6490a10006bd6490a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a10005f77150a10025f47150a10014ff765061002cfc7650610016be6450610006bd6450610027b44150610005fb705061002df87050610006ee62c8610006ed62c861002dfa70c8610005f970c8610005bf744861006dbc7448610006ee6248610006ed6248610005fb704861002df8704861002df9769021002ef97690210024f97690210016fa649021002fba649021002fb9649021002ef8649021023f7b539021023f795390210025fa719021002ff2719021002ff1719021002df871902101ffba41902101ffb
  | 5 => 0x9fb44150420024fd76c8420026f661c8420006f561c842002dfa70c8420005f970c8420004fd7688420004ff7648420005bf744842009dbc7448420026f66108420006f5610842002dfa7008420005f970084200d4ff765002002eef65c802027eed65c802002eef63c8020276ed63c80202776f53c80202776d53c802002ded70c802002eee60c802002efb638802026ef9638802026f7b538802026f795388020265f9728802025efa628802002fea6288020004ff76480200057f75480200a57c7548020005df7348020095dc734802002def7648020006ef7648020004ef76480200076f754802024f6c754802002eef654802024eed6548020007cf7348020247cc734802002eef6348020246ed63480202476f53480202476d534802002def704802002eee604802024feb504802002fe8504802002fea4048020007e9404802002fea3048020247e93048020005fb7648020006fb7648020004fb76480200077b754802024f787548020007db7348020247d87348020246fb6348020246f963480202477b534802024779534802002dfb724802002feb7248020256fa6248020007ea624802024feb524802024fe85248020007ea4248020007e94248020247ea3248020247e93248020007eb2148020007e92148020004ff755931001cfe7559310004fd755931001cfc7559310026bf7459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d5359310004ff7259310004fc7259310024fc7159310026be4159310026bc4159310086bf4059310026fa1059310026f91059310004ff7598b1001cfe7598b10004fd7598b1001cfc7598b10014fe7498b10004fd7498b10014fc7498b10004ff7398b1000cfe7398b10004fd7398b1000cfc7398b100067f5398b100067d5398b10026ee7298b10024fe7198b10026ee2198b10026ec2198b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10026ef7258b10024fc7158b10026f63158b10006f53158b10026ee2158b10026ec2158b10004ff7690b10024fe7690b10004fd7690b10024fc7690b10006ee6290b10006ed6290b10004ff7650b10024fe7650b10004fd7650b10024fc7650b10006ee6250b10006ed6250b10005f77150b10025f47150b1005cfd76903101febf6490310016bc6490310014ff7650310024fc7650310016be6450310006bd6450310005f77150310025f47150310006ee62c8310006ed62c8310025f671c8310005f571c83100057f754831008d7c7548310005df734831007ddc7348310006ee6248310006ed6248310005f77148310025f4714831002cff75d921001cfe75d
  | 6 => 0xc6388520006f76188520026f46188520005fa7088520005f97088520024fc76485200067f65485201467c6548520005bf74485200c5bc7448520006df6348520136dc6348520006f76148520026f46148520005fb7048520005f87048520004fe76085200067f65085201267c6508520006df6308520116dc6308520007e521085200e4fe76901200067f659012010e7c6590120006df6390120106dc6390120014ff76501200c4fd7650120014fc76501200067f65501200fe7c6550120006bf6450120016bc6450120006df63501200f6dc6350120005ef7250120005ec72501200067f65c81200ee7c65c8120006df63c81200b6dc63c81200077b65c81202af7865c8120255fb73c8120255f973c8120007db63c81202a7d863c81202a77b53c81202a77953c81202afea52c81202afe952c81202a7ea32c81202a7e932c81200067f65881200de7c6588120006df63881200aedc638812002def758812029ded75881200076f65881202976c658812002def738812028ded7388120007cf6388120287cc63881202876f53881202876d5388120007eb608812002fea3088120287e9308812002cff75d902001cfe75d9020004fd75d902002cfc75d902009cfd74d902002cff73d902000cfe73d9020004fd73d902002cfc73d90200067f53d90200067d53d90200e4fe72d902002eee72d9020024fe71d9020004fd71d902009ebc41d902002cfe70d902002efa70d9020014ff765902002ebc6459020004ff755902001cfe7559020004fd755902001cfc755902002ebf745902009ebe5459020006bd5459020004ff735902000cfe7359020004fd735902000cfc73590200067f53590200067d535902009ebf4359020006bd4359020014ff7259020014fd725902009cfc725902009ebc4259020004ff7159020024fc715902009ebf415902002cfe705902002cfc705902002ebe405902002ebc40590200e4ff769082002cfe7690820014fd769082002cfc7690820016be6490820006bd649082002dfa7090820005f970908200e4ff7650820005f77150820005f4715082002ef7619842002ef46198420005bf745842009dbc745842002ef46158420004ff755842001cfe7558420004fd755842001cfc7558420004ff7458420006bf7458420004bf7458420014fe7458420014fc7458420006bc7458420014bc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d5358420006f65158420006f55158420006f63158420006f53158420024ff705842002ef6105842002ef41058420024ff769042002cfe7690420004fd7690420006bf6490420016bc6490420026f66190420006f56190420004ff7650420004fd765042002cfc7650420016be6450420006bd6450420026f66150420006f56150420
  | 7 => 0x91200067d53591200c6bf4359120006bd43591200d4ff7259120006ef7259120004ff7159120006f77159120004f77159120024fc7159120006f47159120024f471591200e4ff7059120006fb70591200bdde76d8d200bede76d8d2000cde76d8d200075f75d8d200075c75d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d20007cf72d8d200bfcc72d8d20007ce52d8d20007cd52d8d20007db70d8d200bfd870d8d20006df75d8d200065f75d8d20006de75d8d20006dd75d8d20006dc75d8d200065c75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d200bede72d8d200bedd72d8d200bedc72d8d20006df52d8d20006de52d8d20006dd52d8d20006dc52d8d20006df42d8d20006dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006dc41d8d20006df70d8d200bede70d8d200bedd70d8d200bedc70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d20006df40d8d20006dc40d8d200bedd20d8d200d4fe76909200067f65909201ae7c6590920006df63909201a6dc6390920014fc76509200067f655092019e7c6550920006bf6450920016bc6450920006df6350920196dc63509200c7ac4250920005f77150920005f47150920005fb7050920005f870509200067f65d85200067c65d8520006df63d8520006dc63d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d8520006f741d8520006f441d852002cfe70d85200cd7e75985200057d75985200067f65985200067c65985200bdde7398520005dd7398520006df6398520006dc6398520006f761985200057f75585200cd7c75585200067f65585200067c6558520005bf74585200c5bc7458520005df73585200bddc7358520006df6358520006dc63585200067f65185200067c6518520006df6318520006dc6318520026f66118520006f56118520004fe7690520004fd7690520024fc76905200067f659052018e7c6590520006bf6490520016bc6490520006df6390520186dc6390520004ff7650520004fe7650520004fc76505200067f655052017e7c6550520006df6350520176dc6350520005ef7250520005ec72505200c7b44150520004fe76c85200067f65c852016e7c65c8520006df63c852012edc63c85200067f658852015e7c6588520006df638852014ed
  | 8 => 0x4ff7458620014fe7458620014fc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d5358620006f65158620006f55158620006f74158620006f44158620006f63158620006f5315862002ef6105862002ef41058620024ff769062002cfe7690620004fd7690620016be6490620006bd6490620004ff7650620004fd765062002cfc76506200d7b44150620026f66188620006f5618862002dfa7088620005f97088620024ff7648620005bf74486200d5bc7448620026f66148620006f56148620005fb704862002df8704862009cff765022002ded76c8220006ed76c822002eef65c82202beed65c822002eef63c82202b6ed63c82202b76f53c82202b76d53c8220005f976c8220006f976c822025dfb73c822025df973c82202b77b53c82202b77953c82200cd7e76d95200ce7e76d952001c7e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200076f72d95200cf6c72d95200076e32d95200076d32d95200077a30d95200077930d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95200ce7e72d95200ce7d72d95200ce7c72d95200067f42d95200067c42d95200067f32d95200067e32d95200067d32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95200067f70d95200ce7e70d95200ce7d70d95200ce7c70d95200067f40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d95200ce7d20d9520014fe76d91200067f65d91200067c65d91200c6be64d9120006dc63d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120004ff73d912000cfe73d9120004fd73d912000cfc73d91200067f53d91200067d53d9120014fe72d91200c4fd72d9120014fc72d91200c6bf42d9120024fe71d9120004fd71d91200c6bc41d91200c4fd70d91200c6bf40d91200057f75591200cd7c75591200067f65591200067c65591200c6bc6459120005df73591200bddc7359120006dc6359120005f77159120005f47159120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c75591200c4ff7459120006bf74591200c6be5459120006bd5459120004ff7359120006df7359120004df735912000cfe7359120004fd735912000cfc7359120006dc735912000cdc73591200067f535
  | 9 => 0x46108540005fa7008540005f9700854002dbf75901402d5bd759014002dbf73901402cdbd73901402c73f53901402c73d53901401febc619014002dbe709014002fba709014002ebf6090140017bb60901400e6be64d9320004ff75d932001cfe75d9320004fd75d932001cfc75d93200e4fd74d9320004ff73d932000cfe73d9320004fd73d932000cfc73d93200067f53d93200067d53d9320006ee72d9320024fe71d9320004fd71d9320006f970d9320014ff76593200e6bc6459320004ff755932001cfe7559320004fd755932001cfc7559320006bf74593200e6be5459320006bd5459320004ff735932000cfe7359320004fd735932000cfc73593200067f53593200067d53593200e6bf4359320006bd43593200e6bc4259320004ff7159320024fc71593200e6bc41593200e6bf4059320014fd7690b20016be6490b20006bd6490b20005fa7090b20005f97090b2009cff7650b200e7ac4250b20005f77150b20005f47150b200ed7e75d87200057d75d87200e5be74d8720005bd74d8720006f76198720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d5358720006f63158720006f53158720026f66118720006f56118720024ff7690720004fe7690720004fd7690720016be6490720006bd6490720004ff7650720004fd7650720004fc7650720005ef7250720005ec72507200e7b44150720024fd76c8720026f661c8720006f561c8720005fa70c8720005f970c8720005bf74487200e5bc7448720026f66108720006f56108720007e52108720005fa7008720005f970087200c4fd7690320014ff7650320014fc7650320016be6450320006bd6450320005ef7250320005ec725032002cff75d922001cfe75d9220004fd75d922002cfc75d92200d4fd74d922002cff73d922000cfe73d9220004fd73d922002cfc73d92200067f53d92200067d53d922002eed72d9220024fe71d922002ef671d9220024f671d9220004fd71d922002ef571d9220004f571d922002efa70d9220014ff765922002ebc6459220004ff755922001cfe7559220004fd755922001cfc755922002ebf74592200d6be5459220006bd5459220004ff735922000cfe7359220004fd735922000cfc73592200067f53592200067d53592200d6bf4359220006bd43592200d6bf4259220004ff7159220024fc71592200d6bc415922002ebe405922002ebc40592200c4fd7690a20014ff7650a2002cfc7650a20016be6450a20006bd6450a20005f77150a20005f47150a20005fb7050a2002df87050a2002ef7619862002ef4619862002ef46158620004ff755862001cfe7558620004fd755862001cfc7558620
  | 10 => 0x8a40006ed5258a400c6ee4258a400c6ed4258a40006ee3258a40006ed3258a40004ff7158a40024fc7158a4002cfc7058a4002eee2058a4002eec2058a4002ef7619864002ef4619864002ef46158640004ff755864001cfe7558640004fd755864001cfc7558640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640004ff7258640004fc7258640006f65158640006f5515864005ef6415864005ef541586401febc4158640006f63158640006f5315864002cfc705864002ef6105864002ef410586402e6bf65906402e6bd65906402debf63906402debd63906402df3f53906402df3d5390640006be6290640015be7190640017b671906401ffb661906401febd6190640007b561906401ffba7090640005bd70906401ffb97090640016be6090640017ba6090640004ff76c864002cfe76c8640004fd76c8640015be74c8640005bd74c8640026f661c8640006f561c8640167b441c8640024ff768864002cfe7688640004fd7688640006ee6288640006ed628864002dfa7088640005f97088640004ff7648640004fd764864002cfc7648640005bf7448640015bc7448640024ff760864002cfe7608640004fd7608640006ee6208640006ed6208640026f66108640006f561086401ffb4410864002dfa7008640005f97008640004ff75d894001cfe75d8940004fd75d894001cfc75d89400d6be54d8940006bd54d8940004ff73d894000cfe73d8940004fd73d894000cfc73d89400067f53d89400067d53d89400d6bf43d8940006bd43d89400d6ee42d89400d6ed42d8940024fe71d8940004fd71d8940006ef62989400c5f970989400057f75589400fd7c7558940005df73589400f5dc7358940005f77158940005f471589400e5fb7058940006ed6218940004ff751894001cfe7518940004fd751894001cfc7518940004ff731894000cfe7318940004fd731894000cfc73189400067f53189400067d531894009eee421894009eed4218940024fe7118940004fd7118940004ff75d854001cfe75d8540004fd75d854001cfc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d8540004fe72d8540004fd72d8540006f751d8540006f451d854006ef641d854006ef541d8540006f631d8540006f531d8540006f7619854005df970985400057f75585400fd7c7558540085fb7058540026f66118540006f56118540004fe76c8540004fd76c8540004fc76c8540006f761c8540026f461c8540004fe7688540004fd7688540024fc7688540005fa7088540005f97088540004ff7648540004fe7648540004fc7648540005bf7448540015bc7448540004fe7608540004fd7608540024fc7608540015be7408540005bd7408540006f76108540026f
  | 11 => 0x13dbe7498121005bd7498121006bf6498121006bc6498121006fb60981210057f75581211457c7558121005bf745812113dbc7458121006bf6458121006bc6458121005df7358121135dc7358121006bf6418121006bc6418121006f9601812102cff751812101cfe7518121004fd751812102cfc7518121014fe7418121004fd741812102cfc741812102cff731812100cfe7318121004fd731812102cfc73181210067f53181210067d5318121004ff755902101cfe7559021004fd755902101cfc7559021026bf745902111ebe5459021006bd5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d535902111ebf4359021006bd435902111cfc725902111ebc4259021024fe7159021024fc7159021026f47159021024f4715902111ef74159021026be4159021026bc4159021026f44159021026b44159021026ef2159021026ed2159021004ff705902102cfc705902111ebf4059021164ff7690821024fe7690821014fd7690821024fc7690821016be6490821006bd6490821166ee6290821025f67190821005f57190821307b44190821164ff7650821166ee6250821005f77150821025f47150821025f77648421006f77648421004f77648421007b7744842111df6744842111df47448421007b4744842111db47448421026f763484212fef563484212ff7753484212ff755348421025f77248421027e772484212f6f66248421027e662484212efe652484212efe5524842102cff759802101cfe7598021004fd759802102cfc7598021014fe7498021004fd749802102cfc749802102cff739802100cfe7398021004fd739802102cfc73980210067f53980210067d539802102efa709802102efa5098021006f9509802102efa3098021006f93098021026fb109802102ef81098021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021014fe7458021014fc7458021004ff735802100cfe7358021004fd735802100cfc73580210067f53580210067d5358021026fb7058021006fa5058021006f95058021006fa3058021006f93058021026fb1058021026f8105802102eef6298a40004ff7598a4001cfe7598a40004fd7598a4001cfc7598a40004ff7398a4000cfe7398a40004fd7398a4000cfc7398a400067f5398a400067d5398a40006ee5298a40006ed5298a400e6ee4298a400e6ed4298a40006ee3298a40006ed3298a40024fe7198a40004fd7198a400e6bc4198a4002cfe7098a4002eee2098a4002eec2098a4002eec6258a40004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a400067f5358a400067d5358a40006ee525
  | 12 => 0xd53d91210063d53d9121006bc53d9121306bf72d912113ebe72d9121006bd72d9121006bf52d9121006be52d9121006bd52d9121006bc52d9121006bf32d9121006be32d9121006bd32d9121006bc32d9121006bf71d9121306be71d9121006bd71d9121306bc71d9121006bf51d9121306be51d9121006bd51d9121306bc51d9121006bf31d9121306be31d9121006bd31d9121306bc31d9121306be21d9121306bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006bf30d9121006be30d9121006bd30d9121006bc30d9121306bf10d9121306bc10d912113ebc6459121004ff755912101cfe7559121004fd755912101cfc755912113cff7459121006bf7459121004ff735912100cfe7359121004fd735912100cfc73591210067f53591210067d5359121154ff7259121006ef7259121164ff7159121006f77159121164f77159121004ff705912102cfc7059121005be761912113ebe7619121004be761912113f3e751912113f3d7519121006bf6519121006be6519121006bd6519121006bc6519121006bf6319121006be6319121006bd6319121006bc63191210073f53191210073d531912113fad721912132ebf6219121007b63119121007b5311912132fae211912132fac2119121154fe7690921006bf6490921016bc6490921005ee7690921156ee769092113ded7490921007af6490921016ee6490921016ec649092113fac6490921016ac64909213276f53909213276d5390921025ee7190921025ec7190921307ae4190921307ac4190921327e63190921327e53190921024fc7650921006bf6450921016bc6450921005f77150921025f47150921025ec7650921016ec7650921024ec765092113def7450921007af7450921007af6450921016ee6450921016ec645092113fac645092113fae545092131fad54509213176f53509213176d535092113faf4350921317ad4350921007e77150921025ee7150921025ec7150921007e47150921317e63150921317e53150921014ff765052113cfd7650521014fc7650521006bf6450521016bc6450521005ef7250521005ec7250521027b44150521006bf64c8521166bc64c8521025ee72c8521026ef62c8521007b764c8521166f664c8521166f464c8521007b464c8521166b464c85212f5f773c85212f5f573c852130f7753c852130f7553c8521025f672c8521026f762c8521027e762c8521007e642c8521007e542c8521006bf64d8121006bc64d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006f631d8121006f531d8121
  | 13 => 0x721006bd6450721005ef7250721005ec7250721165f77150721027b4415072116d7e75d83210057d75d8321165be74d8321005bd74d8321006fb609832102cff759832101cfe7598321004fd759832102cfc7598321014fe7498321004fd749832102cfc749832102cff739832100cfe7398321004fd739832102cfc73983210067f53983210067d539832102efa3098321006f93098321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d5358321006fa3058321006f93058321006f96018321004ff755922101cfe7559221004fd755922101cfc7559221026bf7459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d5359221156bf4259221024fc7159221026be4159221026bc4159221026ef2159221026ed2159221004ff705922102cfc705922113cfd7690a21306bf6490a21016bc6490a21014ff7650a21024fc7650a21016be6450a21006bd6450a21005f77150a21025f47150a21025f576c8621006f576c8621166f664c8621026f464c8621345f773c8621345f573c862133f7753c862133f7553c8621027e672c8621337e652c8621337e552c862102cff759822101cfe7598221004fd759822102cfc7598221014fe7498221004fd749822102cfc749822102cff739822100cfe7398221004fd739822102cfc73982210067f53982210067d539822102efa7098221026fb109822102ef81098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d5358221026f63158221006f53158221026fb7058221026fb1058221026f81058221014fe76d912113ebe64d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d912113ebe54d9121006bd54d912113ebc54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d912113ebf43d9121006be43d9121006bd43d912113ebc43d9121024fd72d912113ebf42d912113cfd71d912113ebf41d912102cfe70d9121004fd70d912113ebf40d912113ebc40d912113dbe76d9121014be76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006bf63d9121006be63d9121006bd63d9121006bc63d91210073f53d91210073d53d9121307af72d9121007b631d9121007b531d9121307ae21d9121307ac21d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d91210063f53d9121006be53d9121006b
  | 14 => 0x6ec32d894102cfe70d8941004fd70d8941006ef629894113df57198941167b44198941165f7715894113fb44158941006ed621894111fb44118941004ff751894101cfe7518941004fd751894101cfc7518941024fd7418941004ff731894100cfe7318941004fd731894100cfc73189410067f53189410067d531894111eee421894111eed4218941006ef3218941006ec321894111ef7411894132ebe411894132ebc411894111ef4411894111eb4411894102cfe7018941004fd7018941087b441d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141024fd74d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d8141004fe72d8141004fd72d8141086fa40d8141005ee7298141005ed729814106fb44198141006fb60981410057f755814117d7c755814105fb4415814103fb44118141006f9601814102cff751814101cfe7518141004fd751814102cfc7518141024fd741814102cff731814100cfe7318141004fd731814102cfc73181410067f53181410067d5318141004fe7218141004fd721814120ebe411814120ebc411814102efa401814103ef94018141166be64d9321167b441d9321004ff75d932101cfe75d9321004fd75d932101cfc75d9321164fd74d9321004ff73d932100cfe73d9321004fd73d932100cfc73d93210067f53d93210067d53d9321006ee72d9321006f571d9321166f741d9321306be41d9321306bc41d9321166f441d9321166b441d932102cfe70d9321004fd70d9321014ff7659321166bc6459321025f47159321167b74159321004ff755932101cfe7559321004fd755932101cfc7559321006bf7459321166be5459321006bd5459321004ff735932100cfe7359321004fd735932100cfc73593210067f53593210067d5359321166bf4359321006bd4359321024fc7259321166bc4259321166f77159321166bf4159321166f74159321166f44159321004ff705932102cfc7059321166bc4059321024fd7690b21016be6490b21006bd6490b21025f67190b21005f57190b21167b44190b21025ed7690b21016ed7690b21024ed7690b21016ee6490b21167ae6490b21007ad6490b21016ec6490b2135f6f5390b2135f6d5390b21025ee7190b21007e67190b21007e57190b21025ec7190b21167e74190b21307ae4190b21307ac4190b21167e44190b21167a44190b2111cff7650b21165f77150b21025f47150b21005ef7650b2111eef7650b21007af7450b21016ee6450b21016ec6450b21167ae5450b21357ad5450b2134f6f5350b2134f6d5350b21167af4350b2134fad4350b21167e77150b21025ee7150b21025ec7150b21007e47150b21025e47150b21167e74150b21167e44150b21014ff7650721014fc7650721016be645
  | 15 => 0x53018542006f43018542006f761d8142006f461d8142004ff75d814201cfe75d8142004fd75d814201cfc75d81420e6be54d8142006bd54d8142004ff73d814200cfe73d8142004fd73d814200cfc73d81420067f53d81420067d53d81420e6bf43d8142006bd43d8142024fe71d8142004fd71d81420e6fa40d8142005f67198142005f57198142006f76198142006f46198142006fb60981420057f755814219d7c7558142005df7358142195dc7358142005f77158142005f47158142006f76158142006f46158142006f76118142006f46118142006f9601814202cff751814201cfe7518142004fd751814202cfc751814202cff731814200cfe7318142004fd731814202cfc73181420067f53181420067d5318142024fe7118142004fd711814202efa401814209ef94018142004ff7598a4101cfe7598a41004fd7598a4101cfc7598a41004ff7398a4100cfe7398a41004fd7398a4100cfc7398a410067f5398a410067d5398a41026ee7298a41166ee4298a41166ed4298a41024fe7198a41166f74198a41026f44198a41026ee2198a41026ec2198a4102cfe7098a41004fd7098a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a4113ebe5458a41006bd5458a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a4113ebf4358a41006bd4358a41026ef7258a4113eee4258a4113eed4258a4113ebc4258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a4102cfc7058a41375bf7590a41375bd7590a4136dbf7390a4136dbd7390a413673f5390a413673d5390a41015be7290a41017ae7290a41307ae6290a41006bd6290a41307ad6290a41307b67190a41305bd7190a41007b57190a41016be6190a41017b66190a41005be7090a4102cff759824101cfe7598241004fd759824102cfc759824102cff739824100cfe7398241004fd739824102cfc73982410067f53982410067d5398241004fe7298241004fd7298241024fe719824102cfc719824102efa709824102efa409824106ef94098241026fb109824102ef81098241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c755824105ebe5458241006bd5458241004ff735824100cfe7358241004fd735824100cfc73582410067f53582410067d535824105ebf4358241006bd4358241004ff7258241004fc7258241024fc7158241026fb705824105efa405824105ebc4058241026fb1058241026f81058241157b441d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941024fd74d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d8941156ee42d8941156ed42d8941006ef32d8941
  | 16 => 0x85420067d53d8542006f751d8542006f651d8542006f551d8542006f451d8542166f641d8542006f731d8542006f631d8542006f531d8542006f431d854202cfe70d8542004fd70d8542006f765d8542006f665d8542006f565d8542006f465d8542167b654d8542007b554d8542006f763d8542006f663d8542006f563d8542006f463d85420077753d85420077553d8542167b743d8542007b543d8542167e772d8542167e742d8542007b642d8542167b442d8542167e442d8542006f775d8542006f675d8542006f575d8542006f475d8542166f774d8542166f674d8542166f474d8542166f754d8542166f654d8542166f554d8542166f454d8542006f773d8542006f673d8542006f573d8542006f473d8542006f753d85420067753d8542006f653d8542006f553d85420067553d8542006f453d8542166f743d8542166f643d8542166f543d8542166f443d8542166f772d8542166f572d8542006f752d8542006f652d8542006f552d8542006f452d8542166f742d8542166f642d8542166f442d8542006f732d8542006f632d8542006f532d8542006f432d8542006f770d8542006f670d8542006f570d8542006f470d8542006f750d8542006f650d8542006f550d8542006f450d8542166f740d8542166f640d8542166f540d8542166f440d8542006f730d8542006f630d8542006f530d8542006f430d8542006f76198542306bf6418542026f66118542006f56118542165f67618542006f67618542006f76518542006f66518542006f56518542006f4651854211fb65418542007b55418542006f76318542006f66318542006f56318542006f4631854200777531854200775531854211fb74318542007b5431854211fe5721854211fe74218542007b6421854211fb4421854211fe44218542026f77518542026f67518542026f57518542026f47518542026f77418542026f67418542026f4741854211ef7541854211ef6541854211eb6541854211ef55418542006b5541854211ef45418542026f77318542026f67318542026f57318542026f47318542006f75318542006775318542006f65318542006f55318542006755318542006f4531854211ef7431854211eb7431854211ef6431854211ef54318542006b5431854211ef44318542026f77218542026f57218542026e57218542006f75218542006f65218542006f55218542006f4521854211ef7421854211ef64218542006b6421854211ef5421854211ef4421854211eb44218542006f73218542006f63218542006f53218542006f43218542026f77018542026f67018542026f57018542026f47018542006f75018542006f65018542006f55018542006f4501854211ef7401854211ef6401854211ef5401854211ef44018542006f73018542006f63018542006f
  | 17 => 0x300200000000400a01b00000300e01000600900000201700000000000000500600300000300000000100800200000400700000400600c00100000000a00400400a00100100800400200503700300000101900000400900001001300000500100300000500000100000500a00601000300000100000200b00000200000000100b00000500100000800301d00000200002c00200300000000e02900900000f00a00600000200101400400000500500b00200000500001b00900800400100900f00101700700000300100101900c00200200500000e00000200e02600200300000100000000200c00100100100d00202c00100000800000000b00a00000400000100000400100001301100000800100800400000200500200500000000000200d00400300700000000500100600000700d00100200000000200000001300b00400100100500300e00b00300303600000700300000000500000000100300200501600000900500100000500100400900201301001a00000800200100200000200000200100000900001900400600000300000200500001900300000100400d00400201200100000300200101200000800000500700b00100000100000700800500000600000000300000100300200900000000b00100000100300300500100200200001800000700000100000300000600100200203400600300800700300000900100100000000e001000007001000000014000000001000023002005005000004167b441d8642006f76198642004ff755864201cfe7558642004fd755864201cfc7558642004ff735864200cfe7358642004fd735864200cfc73586420067f53586420067d535864213ef64158642306bc4158642006f63158642006f53158642004ff705864202cfc7058642026f66118642006f56118642307b44118642006fb609824202cff759824201cfe7598242004fd759824202cfc759824202cff739824200cfe7398242004fd739824202cfc73982420067f53982420067d5398242024fe7198242004fd71982420d6bc419824202efa40982420d6f9409824202efa3098242006f930982420057f75582421ad7c7558242004ff75582420067f75582420047f755824201cfe7558242004fd755824201cfc75582420067c755824201c7c7558242004ff735824200cfe7358242004fd735824200cfc73582420067f53582420067d5358242004ff7158242024fc71582420c6fa4058242006fa3058242006f93058242006f9601824238dbf759094238dbd7590942385bf7390942385bd739094237f3f539094237f3d5390942015be7290942017ae7290942016bf6290942017af6290942004ff75d854201cfe75d8542004fd75d854201cfc75d8542004ff73d854200cfe73d8542004fd73d854200cfc73d85420067f53d
  | 18 => 0x20ad22b14531b44ea8a0c44d16ec9bc67e50694dc08c2290001dc0000b110002a5164c0e505780004be3d00002d5c97436a4258000fcc000000182139a5f3101800080c2810001044966000000015c27a00e00201400200300000600102e00900000600401c00000300101100a00000c00000000800100300101d00300600b00100000000000000400300b00600b00001000000b00000900100000d01000a00100001b00000100100000001600000a00200700600601300600300100000d00002c00c00100700300700100400100100b00000000000400300000a01c00100a00400300600000400001000000000100300000100000100300400102600001d00203800100500301800400000200200100101400d00000a00000c00a00b00200a00600000400000300100100300100d00300100300101800100102600300002900500300701200603600200200000100800000300801d00000200d00802200000000100000101103700600200000000100000000002301000400100a00200400300300000300600000100c00300300100000200000300300100001a01500300500001600400000000100400200200500400500800b01500200100100e00200000f00e00100200200200000100a00200600400001100000300000100300400600400100a01800000800002600000f00201500300000302d00100301e00700100200000000000c00700000100702800300300000200a00000000000700400e00102b00300100300100a00900200200800400100000500a00000201200000200100f01000100000100000000000200800000200700500600000700900100000a00500200100501100101500000401800600b00400903b00300400800c00600100000300101400200700500100400400000200700100200001000604400000600300a00000001000203700203100700e00100003200100000001200000000300300000901200a00000001300000003201100600100101200000200000602301900103801601600100700200100000000b00600400900600101d00c02201200b00400000200300500700c00700800e00000100000300100000700d00200100600e00300000000000300000200400300200500000c00100b00001300c00900500000300100000200400003f01c01c00000000901801300200600600100100000000200600000400c00000900100400200200000700100102902700100002200200000400101800100a00800500001300300100300200800e00800401e00100d00000100400900000300700500100400200000f00000100100100700c00100f00000100000900200400600000b00300000300400400c00200000000100200101300200100300900600800300000100600000601600300200301000900100200000000a000
  | 19 => 0x6b43700014062790001768f344465b4aaf0fec20f040a87488e6db3098e512b66ff018800000000000027610740005980000b2457f16e00d03e074c36795ac1da6b61c41d003ba9c00100ccd0fcb384cf056000001d448030cf6466e36fa06849a32b0002cdc6028d54d396a88c66bd2478000f3a7e448300b80f6000000130800002943529655b850b5618d9427c00003395692c83ae508a6108e245a5c384d8ff27f3000121808872c5c0177d4e63ec5b18f054000002e780008f84ce376077927867c5a885055de15414722a05e80000bfa95c0000000002d100004651358cf00007ba0000e9800075000000000ca6401c000009a878b1510000c282cd1540c34e240000000c5cc9eaed00000000002442f62a6ce2254b00000000000e700000000000000000000000156000000000000000016f050e0004f1000018c8220000650000000589055cd7400026f80000000003b1800000031900000003c8b812218000de28ed000000026685b45d000000000000024b160649f59591b4f7c0005bf00002aa9ed21500007fe8074631f3c5a22c60001f495c425d0002a382980000d00000fa03633f928dc81c0004f901fc9ba547362928501aa2b00010416082d336d21a4000000452901460a37100010dc7b20004e7167816e5ac23f14bca5caf8555a88142a36100025e0ff089b5a98a9502c4d808607f48063c51071f748581ef0000f9c00072152e80007e07bd24a0d24000000196a6a8978391487a2c45c64ee00016580000000a01551468000000239964e00043214c415c323000000126e73126894753a80004d480010307b33a2000112c0002e9ac547369790b88000000a7400029dc6ac7880ee1a6c000b14334800142400000014c165a25b02e2e7d1c01d35161c3c026b484c010752625882f215994a8ad144faa04edab9c0e623c8e3c13534529f97426c837f0ad50e6925426997149648b43c913c6a434d1670ff4568b6048e0f988042c016f0ca05901c50090fe4c96b455cd1fb43da1b02f294f0e348d95739e4048674734f13bc0007ea0001e2800030a3621dd06b60003060000f922900478150cd433e23ba21921c690567ac700000001b11a3503a08b38c0200bcc3bf47f80008a2ad239f800000000000010ccb0029541e8a8564a0004dc90e80008c446388292720003148dccff492231a1358f22000262959c0006751d90244dba4fc2378a7d4e49da1bea2ec56e84a0ada4248dc0433e313340002532b900009308981fbab152064950001784c1449201e80001dc00049780000c04d52860000a920000002934bfa0000d880001fe00031e00000004ab40700000006512fc000161c000000063c0005d700000ec000000000000000097c0ea00005da0003808ef90461b842b06848be73a4650b54c1c7945251b4d49802f1c22c
  | 20 => 0xbace840593e52b087404161e7a31430a8782d590c88f41fa59514404606392f7094807eaaa3d29be16c200055f800000000007880012429c10000d180209080000000000b8a11f94cd1b01e2566800133265838facd030c0005910000c440ba2ed80014c80a200b00001ec2a60000e88044000000184000015c3528000dec0f0000278529c00000016dc4ae1e817700010e4b360000000bee515000000121400000002cd2401451f112b966419b0000ebc00052159000000001280f9a401042835000244856056a1de828140240c00009a49e4354405104c000423449970053235e0002a340007752899d980006e200000004e60001b92c8d32694900017500003310000e24fc008d00002d4286000000199510a5d002987dcec04765120000a766ab3ab84991641022da9fc4fb06e15b62ce8c0871d2d000104620004e916f4c36648518800163618e0002c64aee0001d6000122e0cd00000000008b00001984000000000059400000057e98155c200005380009c22e600000006f400000001e8206000116126c00000000000000002f03d400003ea9e430f800134c0000000000efa9b13c7000000049d00029151ee0001208db81543e900014f4ac479700004b556e04a27f1fbd5324c900000000003b900000012e20000b200010486c94c297380000000839d441c08a934080000003b7035ad5816c0091538d442ea0002b817acd30682000000124e441371a00caf400055c98748908d41442e5972272b2cd12d004ca3f0e824ccfd695517d02b0af80000001c651986f400019040005761c9ae08eb8000599808c0003bc05c23480002ca0002978ac800005a000041000000018c51841662e30000a1213f0449e98000a1340f895930473600018cc71e000000099902822f4c622a8254af4028a724e9692e41800000000002e18628032b293bb9304d1038d3729fed2ea4e84089d156e09ff03e24444b45c41870b6d4b81d21b78eac63c1c41a591785ca19c2fe282421082a4b48b3c29e1f9451a19c3c63dd17e9d4d4a06802a923c400ea1432821bd0bc2092731e89068ad835f265c396a9d0d596608b853a03aa4a530208523e92089c45404ab8fd87e20ad3849eac3d85f243e9bbd2a000028d81b4cee8321e484486ae0620000000000b210821a642167072920000000acb191204000037e216800025c76935a0be07e64ff074812c0009be1f21199340000137800049c5ff4bb215400000000002ac0007cb0000000dcc6530662d2800000000000006e063e0001910d9a17739a00000000001a3800000096b0002124a849920002cd4aca000000000000000048980007060ca559a120f8e0002c20000ef600000000008ea3ed0ef8ea8000159447028c4c6000000014916c4ec00015c44969ac0002bc87b00004b3ad5446a65f0002111716b
  | 21 => 0x2cb000000000009e0000000d722210000000d2c9bd5ae22f40000000ff19eccd00002d19894ce898b55a000118663800019d904e0cf516adec8680000c62d0c0000e81e980005080001559b2901228b566032c44872f47200002ec728043a50821a0000000000000b5a000000000080632bad908e657b2c8023873e2df4dd800000000019e9eed17e2224da80013229f60001a1c00098f1e1aad453c0d52d9aa156a846a0c816447940004f8087114e8cb0c3834c21c90734288f525a47b2eb00e4c8a03500008980003a548a8fd49f416e16e8bf07ac70645f26bc716188321ae807c068c47e803c5d07930001b554c200041c83bcf6a348543a6208765174a90168b501c6537adbc680667076066400011032d1aa00fc00002a8000d247843069ec48f07e312c87080000000002274d8ca0f53c0c493ba6ee5520624a0415a0b513b543e6b706b02a55dc81c3ee071c01680152c169450ab8d07a1e847967024a7a51894600058528a54d062722ead885d400022ca1ec2906031e4080512e9fb4b30fad6f81eb09606449349fd2e591882723b50000af80000000000000d169ec326800127e6360001c0c00098615d800043aa1000006fc000000589a968f0a73c4e82b952bc04239c28a8684401000083400012b5a0800000000034e035ce822c424422e0bb8aa63951d940008650000b901a400026ca3a431a4d71021de8e2600053c80002622af5ad8444dfa93a0000000cde6b5000013000075541f20800009e313200001061ad54ba588eb663f0001068294b17000022883c0b100014b40001bb0000cd5658a9007aa0b000000000009b4fbc000429043d50093447793acdce66018301855a696023a2e185ae8192a688cd67cb5800a84c10f800040a95f92b06705c40000000399350013c00070b38b8000788b922488000000a4124b800096411b52d97f80000a50a8800012a84559e03c8a3416048f80002c425e2ea854800086b03493c4000a6c000800101e00006293e400058b49508f800000006107d8000ae303a0d74b2a0f300022256fa0b22fa00012e09723e40c7c61e6320000000b9a5a200025b013e00000003dc00000000023a91e061249917488c81501929cec93800000000002be8710000afc000000399ac089ceba4358165d33eb4d557191c0f295609a1a242840d1427a2811180001c81aec06c4a414e9138e46000000163024aa760000c556ba0a154913307f80283e11c950b035050d1d686980005210001466b4713f9c503e207713dadc4b900e43faa0bc878b994e112dce7c6661478f94faea4836b03f41a826741ba408288a185c61634ab88a114ba7a8bec0d00c212a96e46950b0849c1b67b65c180b4b0485c10a9234a8a7af57e23682ba2a02f81f5534439c3efad7c4a236b46700002a622351eaabc5c24e50991
  | 22 => 0x9618ec46cb03c000050c283000000082878135607540000002a1903c4d00683618000b7400000000010c44bb00005e80005a70f2a694e0a000592000000000050c800000000000018a00000000001b50238a32230a18531a5b4168291c32a6a410d9948aea33b3eb0ab950ca3a0a30878a7e83119727180000bf00029e81283031b207ecad000003992c042e0330002a3c86a0000000399588a620000000592a63378075cece72400f8208620a391521d9000090b218aa606b40000000e78000ac70002c1485e9d734eade0d427a9429a6f028e80b4bd161482a12135c02f48f20000000160bb20000001ef000033721b298072c33a47110280002c10000a603f87d331201341926f73a48ee00782ac09d800048061e29c2a4ce182bd01600008c09f817f8000a0c00000000000000004b6a9940006a600007282740004cd0000000ad64eb23d0ee600014b2a9c0000000002814fd801a473a8700007e706000004f8968269a5950b415e0000d4ccb22b2000060000000000010c066000000000011927b83181fa000047021e80000004ea1e69ba000000043821d84b8b0618206dcf6e03729b12b45662f22128e6030216b000000162ca0754f8000522453551149d1564be00028784224c8548ac040602c73ab293d396afb2720cfc61856100004183ce00000000014a600058f8940bc431324281010ea63d48c29a8c765c700007b8000789000000062844a22a80014ac0005af2e780000000000f6d61a0005ba060c00094d33c131d202aea000000000000008a1be40000004ff21fca3c0000000000f82aec54b0f8d24c2d20dc90a0b8a1e129a9eb81d6000423a8995125e70000000e440004cb00000000004a0000000000000000000006b200000012880000e88000a4c00000000009620000319df80004da00000013f200017586f0000321000188cc56000510800138605f10a1b1c1300000002ac0f2ab762e0800048c95d0000e28374ac01802e74a9e6c24699429394a0b1158f7d57a79f4010ddc65855f2d7800000000000019b03688544c3a7f06be7c051405a069ea7f2a501bc6365294f88d1171c3d50000000b7eaff1a0acbc902205253145948c000520161c0002722268000b367f02aba1e8c8c000511a54400088f33d0534f3270e0df000119a000468a954a02a0811d22105ce30230ca7cd5ba9384cea3755c8412000299cc34ac61be04255b2642421a4d443e73d000185ce4e6d23260428d5a3ba457a6d85b40c411c05a53a28d7162ade417256e005021800000600000000000002a8800029c0c71460af0f460001bb08185d81c948f13190660000002c40ed67ad2ca2458418000000000000000000000016b2000564a68c0000003d5258d1680003d0238c0004890002a0d6a418b00013a42daaf70daab7c950af0007000044e
  | 23 => 0x400011c80004b0a8a19c108116e0fb135046012e6182798000d08b67283895494e44500029a53881730902651736b654ad15cc49e6d84b9803435472e56f0de06c01380000000b260324d5a8095ec05e0ec0b58724b771ed23e8490271000000160e6ea2aaa1dc0004a00f51e08bde50e38d8720d9861107c8658c2a16700000004640004ea96c060e16f0000000c940001b4800075a46933587801c441908f106cb4847f30598a80002a32a981a8b7c89229caa8d69eb0f37d2234a901d947a941046e9a407e1de145e0760000ae53a67fd000115d3cc79c0000f00edcb930d2156546a439000000130624a56a1824000a170000000cba484372000000000008c9628000316000143481285d47d8268e6000010596a45c027d00027d00002923ea1e353ce94b567000032400055c0000d340003c38000d549194828dd0ef2000124800000031c4acaa316f48f60002d181508b358d03a905227a220023105c99009788a903c13c082845c7a404e00b884956255d0000270a22aba2110bd95aa26035709f913821016c1b792de8fc00a15e159001100010fc03ca6e0cd01745f26f34862cb8000b6837922f0ca8b3f46b28d83b41a50cf9bd4e869305a49e3c7e80000000000ab671c5b71e0ce4c8400b61da0330b0b24f00000008fe3be00f845a000000000163c74e24386c89e062e26da5fc000691000232042600027a8d713dcb951799ac4478000000237c00000000000005c40000e72e8800075d32b069c0002652990000a500002cc8cd800032700000010246795410000000000000000000004755489d4d5200033f81c000026130e2b98e6a53e122a7bc6ea53444ca4f8b026af3f280a813a58f38400000003d1412903432e9eb0000000648a275652130bf25fa3b0a3a03f067d1b412d4132000380073c0004962db20306f27522840bbc900a882482a951808800d998d436c70d0d787c84e89540000b088009bf0000030dc036701c0e848520bb04d9f349f076a00015b54446013e8a6a00e40004c5006d5fc0004b08014914a7d4522108f00b733ed8000d807fe09b9dc4e0856f0138d54c5a0e122900013d05f147c82101781a8049a818000000351800000010018c000055274a0001becf2428259e8e5c2e0b852172bc40008dc0002924afa44b28e009061600022d8bed364ad720f98186d800000021806b094a2a60c240003dc445000000099c0d300009a44244940000000000327095000000043681055e602b0ed80000000be35f80013747c546818000005b236e27780003591eba9d45fc5ae21392d856c7e238b2145730a842562198dda5794cdae5104c32a10d115812c00025f97300000003f097249f659d3369c8022a00000000015648ee0128001360a1b4d093700306b34e78000000a6d52210200003fb00000008d07394a0
  | 24 => 0x5501da2db4f30113324a66063a0002951dd88083a3000244000000003600003fe4a900022b129068e1fd2490bc012358e93dc00042122c09d800000000017b400093b2d8996c0000001841f3906c50f19c85d0bd20000001ff04e000000000004687da00007589e8b5023609084321e90001dc95a001c00017090a04990000d2833a1ac11718dcede5a632a924c68a0000920000d261e63479eb12b84674dba76ca44129289000113c00037e221cab058e4ba000d1d8b8927ea85915a2360001310f722203ac9858eb067315c1e910d08f331600000000003fb96b56d4000032000075040757d206c5347963afa781122b403748db419c8b900000012d4000000016c87c0002ab251c0003b64362a852f656c1f083f80000000001e78000b421fc1340bd04a54869a5000000034f800000029442f8e307e48ae0b900004c417b28f906094400048a00013701ae004200065e4e336088a00006a700025dd1d63a441400008380000388000a4600000011254861221900000f0ca52000283897293d0002e4152a0a42e8800000000034b8000686953000000147cb091bd8fb91060005270000000ae906423052562ad26508955c0b973c600009c076c146aba0fd2000467941420238225e8fa80000000000ec108c0000001d35078a8b0000000a2800044a9b6400052006e000073465e00000000003de4e39cdd4bea512ce00013ca0a600000000000500c98084ac00004c70001010149440a5b80005fb00000010c60003fa215c7de6bc0000001056ab653dad385d2af51dd80012fab182af000000052b317adfc5ee0b017aa99923a5742802810b7207d0c1133c1bc00000026d087060f00000005e20000000ae8a32000000000000034e0000000da00492a200014d691b0d10cd00000003a4058d286882022800135a8130001a18e2019e2d0905d5760f814000005a800012611acffe87456da8f00002d91e3000023a0000608cc898038e1d980000005631e60a6c64c3955052b680748040bc0aa8c040484a29ed15586075b305f4a4a52c000000155044c2f19cb53ee00000019884f0483103a7211103d42c4885870a000000000000083807d0704b06aad00016e0000000000000074eb4c0011e6c98617e54e0ec509c0d900027a470200014520148567b00000000e2a11f0001d3c0000df00022d51ca5dd5940ea4e52ba3332000079c70a00024d8000000445a764000b84338800000028900027e800000051700000000e300000004dc7c4000177822c4503f72a800dca9a00011c92be5ca3af091cc42b0c4a60c695820dd222132c1107321e11f640003e80d4a0fc5862774ef800157c98900027714708945ba868c23400059c83611443112210000f980000000ca4000b3b0e000013ea1cd0bc8e1cc400000002cc502e0000002be41b
  | 25 => 0x36b902ce8cb4b10108ed44aa300490158c7400016619c800039d0002410bb000046d9e9d08250328c0d994e097e48d237935c5ea0001a0c3e854e25c26548a8b8f41d8000cc677f42c81982f80001c30860bea0004d992bcf868e110000000000005758a4d4e200021313d87fc9cc246000138a00004829f0a8c8f80a59238d9c0001360000a82a9e351000000000049180006fe000000070c0003c741680005387bf313167d4761bd58
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5f85dcd62440018b90bb9ac4880021fe15735891001c3e42ae6b1220008bf845cd624400517908b9ac4880023be0973589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200387c87d4d624400187ee9a9ac4881db0f1d353589100062fb9ea6b122001c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b122075c3c7454d62440018bee6a9ac488007171cd53589100066639ee4b122000cb474dc562440e9968e918ac488007351ce315891000c7a43a62b122073cb4744c56244001caaa698ac4880029760c651891000477c3ac43122000acc8358862440038bce6a98c488003175cd531891000476c38643122000e4d530c862440015d300190c48800e1fa1776909100043ec2eed212200087f855da42440070f90abb4848800e1fa1776509100043ec2eeca12200087f855d942440070f90abb2848800237e0d765091000c6e41aeca1220008f7815d942440091e9023b2848810b1d1c765509101fe5a38ec8a1220058f686dc542440018eecbb8a84880031d19771509101665a326e2a122042e3441d95414400956d03b2282880032ed9070505100145e420ec90a2000c3c74d952144085cc843b2a42880022fa1b74485100061fb2ee890a2000c3c65dd1214400117d0fb2242880022f21f64485100071c326cb2022002aba86d924044001974edb2480880ff2d1c764501100063a32ee2a022042c7876d954044005970edba280880ff2e1db64501101fed9ba0e2a02200387e85dd920440010fb0bbb2408800a2fa1376481100045ec26ec902200087f855d920440070f90abb240880022fe1176481100145e422ec90220008df835d920440031b906bb240881ca1fa1b75481100061e326ea902200087e87d9520440850f90fb2a4088003171cf65481100061fbaec89022000c3c75d912044001938e7b22408800317d9773481100062e32ee69022000c9f64dcd2044001938c9b9a4088003331cf624811000666398c490220058f686dc52044001968c9b8a40881279a195200811000755b22401022042c7676d96104407f96cedb24208800b2d9d864841100071a328c908220048f4815d5640400b1790eaa2c808012ad205545901002c5e43a86b20200387e851c964040010fb0a392c80800317dcd539881000e2e39aa731020058ed8794a620400b1db0f194c4080039354e32988100062fb9aa6b102001c5c7354d620400b1d90ea92c4080039354e325881002c7643a64b1020058ed8798a42040591ef02bb284080123d205765081002c5e43ac8a102004cb47159142040099c8e331284080163b21d62508100267238ac4a102000c7475dd910040018eea7bb220080031d54f76440100063bbb6ea8802000cb776dd1100400196eec3a220080034d1d47444010
  | 1 => 0xb07baac8880022fe1175591100047bc0aeab22200087e871d5644400187eebba2c8880030f1d774591100043fc2ae6b22200387c855cd644400117f08b9ac8880023be09735911000476412e6b22200087e87d4d64440070f90fa9ac8880021fa1d53591100043e43aa6b222000c7475dc5644400187cedb28c8880028f60f65191100071cb86ca32220008bd87994644400147d0b328c8880022fe1d65191100055bc0aca3222000a9e83194644400153b06328c8880028fa1865191100061f3b0ca3222000b1d831946444001c3d06328c8880028f60c65191100070ec18ca3222000a1d831946444001c6b02328c8880038e9c065191100071cb80ca32220008bd8798c644400147d0b318c8880028f61663191100055ac0cc632220008bf8758c644400147f0ab18c8880028f215631911000557c12c63222000aac8258c644400147d0a318c8880028f614631911020d5b408c63222000a3e86d4c64440014790da98c8880030f9db53191100051f432a63222000a3c8654c644400187ceca98c8880038798d53191100070eb1aa63222000ab6869446444001c68cb288c888002ad21951191100071a32aa23222000e37658c46444001c68cb188c888002ad21931191100071bb2a623222000e34654c46444001d2ec6988c888003c554d31191100052ec18cbb122001c5e7354f62440018bae6a9ec4880039354c32d891000572c0865b122000ae9800cb6244001caaa698ec4880030f9d365989100061f3a0cb3122000a5d83196624400187ecaba4c4880030f19574989100061f3aec93122000c3d75d92624400187cea324c4880030f5d464989100145f426eb31220008bd84dd662440014bb073acc4880021fe0d75989100061f3ace93122000c3d759d2624400187ceaba4c4880030f5d5749891001c3f42ee7312200087d85dce624400517d09b9cc4880022f613739891001c3fc3ea7312200087d87d4e62440ed87ce9a9cc4880030f5d353989100043fc3aa7312200087d8754e62440eb87ce8a9cc4880030f5d153989100062fb9aa73122001c5c7354e62440070fd0dbaac4880021fa1f65589100061e3a6cab122000c5c73d9562440010fd0e32ac4880030f1d065589100052ec18cab122000c5c73195624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100043ec1eeab1220008bf845d5624400517908baac48800237e0d755891000c6e41aeab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000
  | 2 => 0xc32d95100051f42065b2a2000a3d840cb65440018bee6196ca8810a9da0432d95100053ac0865b2a2000a7a800cb65440014f300196ca880de9ea0371d95100043f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100062fb9e63b2a2000c5f734c765440850fd0fa06ca880021f61f40d95102143f43e61b2a200087d87cc365440018bee7986ca8800317dcd30d95100043f43861b2a200c87d870c3654400147d08186ca880028f61030d95100053741061b2a2000a6d820c365440854ed02186ca880029d60430d95100052ec18cbb222000c3d75d53644400156b03aa6c88800e2fe1d54d911000e2f39aa7b222000c5d7354f644400147d0b21ec8880028f61643d911000c5fc3a87b22200387e859cb64440010fb0b396c8880028f60f65d91100054f418cbb222000a9d83197644400163b0632ec88800387a0c65d91100051ec18cbb222000e1d83197644400143b0632ec8880038d60465d91100051f42cc7b222000a3d8598f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100051f436a7b222000a3c86d4f64440ed87ceda9ec8880028fa1953d91100051e432a7b222075c3e7654f6444001c3cc6a9ec8880038758d53d91100071a32ca3b222073cb6764c76444001e2aa698ec8880030f5d475d91100054f418ebb222000a9d831d7644407f56d023aec888002ad60475d91100051f42ce7b222000a3d859cf644400147d0a39ec8880028f61473d91101fd5b408e7b222000ab5811cf6444001c3ea729ec88800387e0d53d91100070f39aa7b222000e1d7354f644400156b03b96c8880028fa1672d91100051ec2ce5b222000a9e83d4b644400153b07a96c8880022fa1c52d91100045ec38a5b222000a3e85ccb644400147b0b996c8880038754e32d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100070ea9865b22203fab6810cb644400156b02196c888002aea0032d91100055cc0065b222000aae82dc7644400155b05b8ec8880022fa1f51d91100045ec3ea3b2220008be87cc7644400117b0f98ec8880028fa1731d91100051ec2e63b222000e1d53cc76444001c3aa698ec8880028fe1570d91100051e42ae1b2220008be87143644401717b0e286c888002a7a0c50d91100054ec18a1b222000aae82143644400155b04286c8880feada0450d91100055ac08a1b222000a3e85cc3644400147b0b986c8880038754f30d91100070ea9a61b2220008be870c3644401717b0e186c8880028fa1430d91100051ec2861b222000aae820c3644400155b04186c8880feada0430d91100055ac0861b222000c3c64dd564440010fd0fb2ac8880021fa1c65591100052ec18cab22200387e87dd564440010f
  | 3 => 0x210a4078ba48448421480338dcedb2c409005f339db638812000e2f39aa7b204000c5d7354f64080011ef02baac8100123d205755902002c5e43aa8b2040058bc8750d640800117f08baac21000a2f21175584200045fc22e6b0840028bc845cd610800187ee9a9ac2101db0f1d353584200061fba2a6b084075c3c7454d61080038bce6a9ac210003175cd535842002c7a43aa2b084074cb4748c5610800b1e90e98ac2101cf2d1d131584200072aa9a62b084000ae4824c5610800556908b0c8210012ad205645042002c7a43ac2a084002ab484585410805956908b0e42100173c9c161c842011d5a422c21084000c6c75dd92008001998e7bb240100031bd4f764802000636a9eec9004000c6f76dd5200800199eedb9a40100031e1d776480200066c39eec9004000c7b53dd920080018f2a7bb240100031eddb75480200066dbb6e69004000be38150920080017570890a401000317dcd5398b1000e2e39aa73162000c5f7354d62c40038b8e6a9ac5880039554d3158b1002476c3cc521620058f4815d942c40099c8e331285880123b21d6250b100265a38ac8a062001c5e7354f64840018bae6a9ec9080031bd4e72d921000636a9ce5b242000cae419cb648400195883396c9080031bd4d72d921000636a9ae5b2420058bc87551648400b1790ea1ac9081db0f9d353d8a100061eba6a7b142075c3e7454f628400187ae8a9ec508007179cd53d8a100062eb9aa7b142000c5f7354e62840038b8e6a9cc5080163b61e5298a1001e373aca531420058ed8710a62840014db0a214c5080163b61e3298a1000726a9c653142000c5f7354d62840038b8e6a9ac5080163b21d5258a1002c7743e84b142005aea80d0962840014db0a212c5080039354e3258a1002c7643a64b142001ccc734c962840038bce6a98c508003175cd5318a1002c5fc3ac92142000cac749892184001958e8b1243080021fa1b73d951001c3fc3ec7b2a2000c5d73d8f65440010fb0f31eca880028fa1263d95100051ec24c7b2a2000c5f7398f65440010ff0eb1eca880028fe1163d95100051e422c7b2a2000c5f7358f65440014df04b1eca880029b20963d95100643ec38c7b2a2000c5d7318f65440194ed0db8eca8800355dcd31d95100072a31a63b2a2000c3d741d365440ef4f5003a6ca8810a9e60074d95100043ec3ce7b2a2000c5f739cf65440018bf06b9eca880021fa1c73d95100062eb98e7b2a2042a76811cf65440014eb0239eca880021fa1e43d95100043ec3c87b2a2042a768190f65440014eb0321eca880021fa1c43d95100043ec3887b2a2000a3e849cb654400147b09396ca8800297e0d72d95100052e41ae5b2a200087e8710b65440010fb0e216ca880021fa1f32d95100043ec3e65b2a2000c5f738cb65440010fd0e196ca880021f61
  | 4 => 0x3480015a902b26c69005eb3a1b72d8d200072632ca5b1a4000bc88054b634802f5b50db86c69000356dd770d8d200062f396ebb1a4000c5c72dd763480018bae1baec69000297a1675d8d200062eba8ebb1a4000a9e841d7634800153b083aec6901e6b3a0875d8d2000566c10ebb1a4000a5e871d763480018bd0e3aec69000387a1075d8d200070ec20ebb1a4000e4e821d76348001c9b043aec69000297a1674d8d200052ec2ce9b1a4000a5f855d363480014b90aba6c690002b5e0574d8d200056a40ae9b1a4000e1f5495363480915b501b96c69000237a1f52d8d200046ec3ea5b1a4000a9e8414b634800153b08296c69000297a1442d8d200052ec2885b1a4000c5f75dc763480014bd0b38ec6900029761671d8d200052fc2ae3b1a4000a5c855c763480018beeab8ec690002a7e1171d8d200054e422e3b1a4000a9e84d47634800153b09a8ec69000237a1c51d8d200046ec38a3b1a40008de8710763480011bb0e20ec69000297a1441d8d200052ec2883b1a4000ace82107634800159b0420ec690002b6a0041d8d200056cc0083b1a4000c5f75dc3634809159d05b86c69000237a1c50d8d200bc6ec38a1b1a4000a9e84143634800153b08286c690002b3a0850d8d2000566c10a1b1a4000ad68114363480015ab02286c69000297a1740d8d200052ec2e81b1a4000e2c42d9542480018eecbb8a84900031d19771509200066bb1ee2a124000cd463dc542480018eeca38a84900031d19471509200065bb20e2a124023cb4641c542480019aec638a84900033518c71509203c6d2210e2a124000c5f7354f61480038b8e6a9ec290002b960841d852000578c0083b0a4000c5e73d9661480018bce632cc29000317d9573985200062e32ae730a4000c5e75d8e61480018baebb1cc290003179d463985200062eba8c730a400387e86dd561480010fd0fb2ac2900030f1d365585200062e39ecab0a400087e871956148001878e832ac290003171cc65585200061fb2ee8b0a4000c3c65dd161480031bd0db9ac29000317d9773585200062e32ee6b0a40008de87d8d61480018beebb1ac290003171d763585200064fba6c6b0a4000c9c74d8d61480011bd0e31ac29000317dd463585200062e3a8c6b0a4000c9f7418d6148001938e831ac2900023de1d61185200055a422c230a400087f855da41480070f90abb4829000237e0d769052000c6e41aed20a400387e85dd941480010fb0bbb2829000637a0f76505200046ec1eeca0a4000cb4419d94148001968823b282900038d10765505200074a20ec6a0a4000ccc63dc9414800b3d501b9282900033318c72505203c6d2208e4a0a4000c3c74d95214800187ecbba242900030f19774485200064e31ee890a4000c9f74d8d2148001938e9b1a42900032d1d3614852000733b2a4
  | 5 => 0x29d60473d95203f53d400e7b2a4000a79801cf65480010fd0f21eca900021f61e43d95200053b40c87b2a4000a758190f65480010fd0e21eca900021f61c43d952024d3d406e5b2a400087e8710b65480330fb0e216ca900021fa1f32d95200043ec3e65b2a400087e870cb65480330fb0e196ca900028fa1032d95200051ec2065b2a4000a76810cb65480014eb02196ca900029ea0032d95200053cc0065b2a4000a5e839c765480014bb0738eca900028fe1171d95200051e422e3b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a4000a6e8210765480014db0420eca900029ea0041d95200053cc0083b2a400087e87cc765480010fb0f98eca900028fa1331d95200051ec2663b2a4000c5f73cc765480018bee698eca900021fa1c31d95200043ec3863b2a4049a6e82dc365480010fd0fa06ca900021f61f40d95200043f43e61b2a400087d87cc365480018bee7986ca9000317dcd30d95200043f43861b2a401987d870c3654800147d08186ca900028f61030d95200053741061b2a4000a6d820c365480014ed02186ca900029d60430d95200043f43ecab224000c5c73d9564480010fd0e32ac890003171cc65591200062fb2ee6b224000c5c65dcd64480018beea31ac890003171d463591200063bb2ee2b224000c7465dc564480019a8c7b8ac8900031dd9471591200063a328e2b224000cb4641c564480019a8c638ac89000e1fa1f75591200043ec1eeab2240008df835d564480031b906baac8900023de0575591200247a40aeab22400087e871d564480071790eaa2c8901f72d1c5545912000c6f43ee6b224000c5f75dcd64480018b8ebb9ac89000317e1773591200062e42ee6b22400087f855cd64480070f90ab9ac8900023de0573591200247a40ae6b2240008de871cd64480018beea39ac890003171d473591200043f43ea6b22400387c87d4d64480018bee7a9ac890007171cf53591203e63a38ea6b22400087e8754d64480010f90ea9ac89000317dcd535912000e2e39aa6b22407bc747154d64480031790ea1ac8901eb2d1c543591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf71591200063ba9ee2b224000c7553dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89000297a1b75d8d200062f3b6ebb1a4000d4c72dd763480014bd0c3aec690003179d875d8d200062f3b6cbb1a40008dd8799763480014bd0b32ec69000237e1d65d8d200054f420cbb1a4000a9d8419763480014bd0c32ec690003179d865d8d200070f420cbb1a4000e1d841976348001c9b0432ec6900023761e64d8d200052f42cc9b1a4000a5d8599363480011bf0eb26c69000297e1564d8d200052e42ac9b1a4000ad7815936
  | 6 => 0x63aa9eec9084200ce652dd921084019caa5bb242109966da1f74484210065bbb6e89084200cb7761d121084038bce6a9cc010803175cd53980210072ca9a61300420387e87dd560084010fb07baac0108029760c75580210043fc2ae6b00420387c855cd60084010fd0fa9ac01080e1f21f53580210043f43aa6b00420087c8754d60084038bce6a9ac010803175cd535802101e3c3aca0b0042048f88754160084091f10e982c0108039654d30580210057441260b004200c5f7354e62900038b8e6a9cc5200163b61e5298a4001e373aca531480058ed878ca6290001c9aa7194c52000317dcd5358a4000e2e39aa6b1480058ec875496290001c9aa7192c5200163b21d3258a4000e6639a64b148001c5e7354d61900018bae6a9ac3200163d21d515864002c7a43a62b0c8000e55534c5619008317f0cb84832000e1fa1776c86400043ec2eed90c8005cea7058a2190103d48833104320007179cd53d89400062eb9aa7b1280008ef87588625000156b09a8ec2a0002b560c51d854000c7bc3a63b0a8000e55534c761500011ef0eb08c2a00029d21561185400247c432e110a80028bc841d921500010ff0abb042a000e1f21576085400265a30ae810a80048f8865c021500099e0c2b8042a00123da0775d93200047ac0eebb2640038bc8755164c80018bee6a9ac990007171cd535932000c5e43a86b264080da4421c542c80018bee6a9ac390007171cd535872000c7a43a62b0e4000e55534c561c80011ef0eb08c39000e1fa1676907200043ec2ced20e4080da4411c941c81017490890843900133c98570087203e63b38ea7b244001c5e7354f64880018bae6a9ec9101ef1d9c553d92200063ba9ae3b244000c75535c7648800b1790eaa2c9100162f21d435922011e5b320e2a144000cb5641c542880038bce6a9ac310003175cd535862002c7a43aa2b0c4000a758510561880015ab0620ac310002b9608415862002d7940082b0c40058f4874c56188001caaa698ac3100032d10776506200065a20aeca0c4000cb47458521880014bd07326ca900029760e64d95200043f436e7b2a400387f87d8f65480018bae7b1eca900021f61e63d95200043fc3ac7b2a401987d8718f654800147d0831eca900028f61063d95200062eb98c7b2a4000a768118f65480014eb0231eca900031761c63d95200070f420c7b2a4000e1d8418f6548001c9b0431eca9000395a0463d95200072ac08c7b2a4000e598018f65480334dd0db96ca90126daa0372d95200072631c65b2a4000e4c634cb6548001cb0c7186ca90003d28ca30d9520006adb9a61b2a4000c3d741d365480010fb0f39eca9000317e0d73d95200043f438e7b2a4000a3e841cf654800147b0839eca90003175cc73d95203fd37410e7b2a4000a6d821cf65480014ed0239eca9
  | 7 => 0xb6811cf644840156b0239ec89080387d4e53d91210070fc1aa7b224200a9e83d4b644840153b07a96c8908038bd4a52d91210045f438a5b2242278bd8714b644840147d0b996c8908028f61732d91210070ea9c65b2242008be870cb644844f17b0e196c8908028fa1432d91210051ec2865b224200e1d530cb6448401d1a64196c890982ada0432d91210055ac0865b224200aba800cb644840157300196c8909832d9c771d91210045f43ea3b2242008bd87d4764484c1c6ca3a8ec8908022fa1f31d91210045ec3e63b224200a3e85cc7644840147b0b98ec8908038754f31d91210070ea9a63b224200a3f855c364484014790ab86c8908022fa1c50d91210045ec38a1b224200a9e83143644840153b06286c890802aba0850d912100556c10a1b224260ab681143644840156b02286c8908028fa1730d91210051ec2e61b224200e1d53cc36448401c3aa6986c8908022fa1c30d91210045ec3861b224200a3e850c3644840147b0a186c890802aba0830d912100556c1061b224260ab6810c3644840156b02186c8908022fe1175591210047bc0aeab2242008bf845cd64484011df04b9ac8908023de0573591214263bb8ea6b224200c5f7354d64484038b8e6a9ac890a0f1ddc553591210045ec3cca3224200a9e83994644840153b07328c890802ad60665191210045fc3aca3224200ab781594644840117b0f318c8908028fa1663191210051ec2cc63224200ab58198c644840117f0eb18c890802abe0963191210055bc0ac63224200a3e8518c644840147b0a318c890996ada0463191210061f3b6a63224284e3761d4c644840187ceca98c89080387d8d53191210070e31aa63224283e376154c644840156d0d188c890802ada1931191210055a432623224200e97634c46448401e2aa6988c89080aaba1b6490921006573b6c92124260cb471d914248459968c9b8a849080b2b1db7450921306563b6c8a12422cce476dc542484099c8ec38a849098369dd0715092100657b20e4a0a422cab686d932148459d48c92164290812b921942c8521167523228590a4200c5f7354f60484038b8e6a9ec0908039554d31d81213045e436e8b0242008be87d91604840187eebb22c0908030f1d764581210064e39ec8b0242008be87191604840187eea322c0908030f1d464581210064e398c8b024200c9f64dcd6048401938c9b9ac0908023ee1d601812100e2f39aa63024200c5d7354c60484091e902baac8108122f21d54590210255a40aa8b20427dcb471551640850596883b9ac8108023b20973590210247a40ae6b20427acb4415cd64084f98e8e3a9ac8109f38d10753590213de3a38aa6b20427be344154d64084091790ea1ac810812ad20543590213d65a38a86b204260ab481592420840996ce2b2484108031dd4f76484210
  | 8 => 0x4280c2a10029da1730185420053ac2e6030a8423ab684cc0615080156b09980c2a10039554f30185420072aa9a6030a8400ae7824c061508015c904980c2a10123da1c30185420047ac386030a8400a76850c061508014eb0a180c2a108eada1030185420055ac206030a8400ae6820c061508015cb04180c2a100f0f9d554d814201476c16e7b028400c5f7354f60508038b8e6a9ec0a11e3395c861981420047b43ec2b028400c7775d8560508018e8ebb0ac0a100335dcf61581420066a39ec2b0284008f68718560508018eeea30ac0a10031d1d461581420066bb98c2b028400cd47318560508011f70eb00c0a1007179cd53181420062eb9aa63028400c5f7354e62904038b8e6a9cc52080317dcd5358a4100e2e39aa6b1482658bf8758a429045956f0cb8c8520807179cd53982410062eb9aa7304820387e87dd560904010fb07baac1208029760c755824101e1e3aaa8b04820087f855cd60904070f90ab9ac1208023be09735824100476412e6b04820087e87d4d60904070f90fa9ac1208021fa1d53582410043e43aa6b048201c5e7354d60904018bae6a9ac120807179cd53d89410062eb9aa7b128200aad840cb6250401c9aa6196c4a0802b960432d894100574c0065b1282008ef87588625050b5cf02b10c4a08032d10773189410065a20ae63128289e3441d4c6250511c6882a98c4a0a1fa9107321894100666b98643128200e4d530c8625050dd4882190c4a0802ba60032189410043fc2ae0312820387c855c06250401b4883394c0a08036910572981410069a20eeab0282008fb8758060504038bce6a98c0a0803175cd531814102c7d406ebb2642008f980dd764c840196883b9ec9908032d10573d93214271a20ea7b264283e344154f64c850bd4883396c99080e2f21d54593210062fb9aa6b264201c5c7354d64c84031790ea1ac99080e1fa1770593210043ec2ee0b264260ba4845c642c84093c903bb2859098369dd07150b2132ed2208e4a0e4201c5e7354e60c84018bae6a9cc1908039654d30983210062fb9aa6b064201c5c7354d60c84031f10e982c1908039654d30583210047dc3ac0306420387e85dc164884010fb0bb82c9108132d1c56450a2100e2f39aa73044200c5d7354e60884038bce6a9ac110803175cd53582210072aa9a62b044200c3d75d53644840717f0eaa6c8908028fa1643d91210051ec2c87b2242018bf8750f64484010ff0ab86c89080e1f21570d91210054f41ccbb224200a9d83997644840147d0b31ec8908028f61663d91210051f428c7b224200a3d8518f64484ed87ceda9ec8909d70f9d953d91210070fb1aa7b224200e1c6354f64484e796cec98ec890803c554d31d91210061eba8ebb224200a3e859cf644840147b0b39ec8908028fa1473d91210051ec28e7b224260a
  | 9 => 0x70d85420053ac2ee1b0a8400ab584dc361508011ed0e286c2a10023d61c50d85421655b420a1b0a8400ab58414361508015ad06286c2a1002b560c50d854200573410a1b0a8400ae58214361508014ed0b986c2a10029d61730d85420072aa9e61b0a8400e55534c361508011ed0e186c2a10023d61c30d85420053b42861b0a8400a75850c3615085956d08186c2a1002ad61030d85420057341061b0a8400ae5820c361508011ef0eb08c2a10023d61e65185420056b41cca30a8400ad58399461508011ef0eb28c2a10038dd9554185420047ac3cc630a8400a768598c61508014eb0b318c2a10023de1d631854245d73c12c630a8400a768518c61508014eb0a318c2a100395d8d53185420072a31aa630a8400e976350c615091556f0aaa0c2a108f8de1554185423ef1b3aaa830a847de3575550615080156f06aa0c2a1002ad20954185423ef53392a830a847dea572550615084756d09a98c2a1002ad613531854244f1b2a6a630a8400e3554d4c61508015cd05a98c2a1002b960b531854244f1b426a630a8400e3584d4c6150913c6e87a98c2a100399a0b531854200732c16a630a847ce6672d4c61508f9ccae5a98c2a12278d10b531854211d5b424a630a8400ab58494c6150801caea7298c2a108eada1153185424471b2a2a630a8400e355454c6150911c6d08a98c2a10038d61153185420072bc1aa630a847be567354c61508f7caae6a98c2a12238dd0d53185423df33392a630a847be657254c6150911c6884a98c2a108eada1053185420055ac20a630a8400ab78550c615080156b0aa18c2a120aade0d431854211f4bc1a8630a847ae967350c61508f5d2ae6a18c2a10038dd4d43185420071aa9a8630a8400ea78250c615080156904a18c2a1003a920943185423d7533928630a847aea57250c615084756d09a90c2a1002ad61352185420071aaa6a430a8400ad683d4861508015ab07a90c2a108ead21252185420055bc22a430a8423ab4845486150801c6aa8a90c2a108eada1052185420055ac20a430a8400ab785908615080156b0b210c2a1002ad60e42185420071ba9c8430a8400e355390861508cb56d05210c2a108fa9a0a421854230752b948430a8400a7685cc861508014eb0b990c2a108eada1332185420055ac266430a8400ab7848c8615084756909190c2a10039554e32185420055bc226430a8423ab4844c861508091ed0e190c2a10023d61c32185420053b4286430a8400a75850c8615084756d08190c2a1002ad61032185420072aa986430a8400af2800c861508015e300190c2a108eada1350185420055ac26a030a8400e355494061508091ed0e280c2a10023d61c501854211d5b420a030a8400ab5841406150801c6aa8280c2a1002b5a0c50185420056ac18a030a8400ae68214061508015cb
  | 10 => 0x400000200001000e00800200001400200000000000200400c00000000200c00600001000000000400000001e00e02800c00000200200400e00600600400000000000000400000000000000200200200400600600400200000000800000400200400000600400600401200001c00000000003000c00200000000000200601200600400000600800c00e00002000800400400000400400000400000200000000200200000200000a00400200000200200000200c00400000e00200200c00000000000000000400001a00000000400800200a01c00400201600a00201000e00000200e00c01200400400400000001400200001c00000000000000000a00001201600200000200400000401e00400400200000000000000400800200400400200200000003e00200000600e01200000400a00400000401e00200000400000000000000600a00600000800000000200000600600600000c00000e00000000000600a00000000000000c00c00c00400000000200200000e00001603200200600000200000c00a00600000800e00200600000200206202202000a00000000000000600600400001801000a00800002600200201600000400200c00000200200800400800200001800a00000c00600000801800a006006000000008004006018f4874c56190801caaa698ac3210023de1d611864200e2f39aa73048400c5d7354e609080196882b8cc1210039654d309824201c3f43eeab04840087d83dd560908010ff0ab9ac12100e1f215735824201476412e6b04840087e87d4d60908070f90fa9ac1210021fa1d53582420043e43aa6b0484018f8874c16090801cb2a6982c1210023ee1d60182420062fb9aa7b0a8401c5c7354f61508018eaeba8ec2a1002ad61351d854201c7bc3aa3b0a8400ad68314761508015ab0628ec2a10029da1731d85420053ac2e63b0a8400e5553cc761508031ef0e98ec2a10039554d31d85420053b42863b0a8400a75850c761508015ad0732ec2a1002b560e65d85420053b42cc7b0a8400a758598f61508014ed0a31ec2a10029d61463d85420072bb1aa7b0a8400e546354f61508015ad073aec2a1002b560e75d85420063aba8ebb0a842cab6841d7615080156b083aec2a10029da1673d85420053ac2ce7b0a8400a76851cf61508014eb0a39ec2a10b2ada1073d85420055ac20e7b0a8400e575394f6150801caf06a9ec2a100395dcd53d85420072a39aa7b0a8400ad683d4b61508015ab07a96c2a100399d4a52d85421655b420a5b0a8400ab58414b61508014ed0b996c2a10029d61732d85420072aa9c65b0a84008f6870cb61508011eb0e196c2a10029da1432d85420053ac2865b0a842cab6840cb615080156b08196c2a10039554c32d85420076299065b0a8400af2800cb61508015e300196c2a10029da17
  | 11 => 0x3f0000cb40000000004fc0000000013c00000015042fc0014cce54000d2c0012c4ba8f74000000000028000cc0630000000000cc4e9800000000020c470584edc0003592d4000000000e5864d2a8000000000000000000ed80000009595e400096c0000013542ec8fd4b80004b8fc8049230cfc000659514000d5410c0b4424a200004ec1bcfdc0016011f56112d91180000000000000000000014187487d02396080000006003a0000c280000000000013e113c9b4b040850886bc3e800000154472d3080004a535119cbc0000001310468a08adc00000112800090891c00001800000090cbe91c42140000012489800009c89940000003888240015c4c200043a8f004648bc4152e80000000004280e51040014f089800000000000037151c000000555414f2c191054fec000000a6c8ac6a8000fc0d9c188facf3094c0acdd855d4a0ae55b0210d6d0ccdd54110bc84c001568ee8000000000c94ddd3584400a4000ef96bc979048a740000006d0000000bc40000000f470c0000004f80f080cd24dccc102cd2c00010fc12c70418c45c8f81785a0d30e016955dcd58ec89c4e38eec000d01660a115644dc4f531c360e1807d2552743300009e4000001324000b20504fbcac8760aed279398d205d44442908e0b68c7c00139c0010d9510a349e8000000d7034d631374000000020000b7d508b947ec6c858c008a90530df11f0dd0bdc5a9204d3d6d0d891cc40079d6395189147953ac86442d43800049c65c000f99058c39111304bfc1512a544554000110c421240000b50628efcb596a400112000097414d5350d556c0553f00013d800000000015ca955380000dc4740a8c2c000c3c000000fd00000016c400000000000000000000000144c0000000002c0eccde8db82ac3b80000013a000068c7580015a4d60000e484980002d000000146c000ea10b4f481d0ed400045446c4e55987d80003b09300000f81e8000cf8000da80007a440c00159c000000d78001615340000460f512708141f908d300fe80008b8e9c000138b9d21c00000000000000000000000068400000000000200000200200200000400400600a00000400000000200600e00000c00400200400000000800400000a00e00000000600000a00400000c01a01600001000a00a01200800002a00001000600a00a00200000000000000000400000201600000200000000200600a00000201e00400400400600000400400e00000600201801000800000000202800200000000000000800200600200200c07000800000000400001000800800000800200001000a00800c00c00000400000000401000200000a00c00200000c00000000400600401201c00800400a00200000400600801200800800800000400000000002a00a00001400800c01a00000000200200600201000
  | 12 => 0x8000000000000087873c118b70ee0000b856a8e144340008180000008c43c03ec30d22912cb600000006200000016c14bd67cacd57cd1502904c00122c000000734e1c000480001041440b2cc60000a3024839459d2b011c00000150c00000000155c0000000000011b40ecafc0014f8710000764b5c000001570dc11644310dc6b8f455bcd1c00001c000000ea80000003d4bb00000d400000000000000000000080153ce042755e0001524ac0f280001288880005c40000003240002dd48000115c6800008383c4001069494000a780010991e03ac8912bcef4a64000d502a843c8840006e800000000016c00136c32cb1000000000077c11499d4280d838c000000ccca8c000001394c912896200000011bcb7839ca5c3107385284bcd6903c0000000005b8000f68f0c000000000000000000000000000000001284001388650e7c9609e00006393c826c9a89d8000e94d085980000000000000012d06ac000000368000000ad4000e3c0000014892fc000000000000ba55f125929566c8c8f7134c0000000011a942400145000000133c5c16402d94c466947ce900000016d40011494f4104a502840000000000010a00000002c800132c000f7806cca8001210d5c754728000d985bce282500002a00115796349885ac78c038000c592ece70e514700156591c83f43cc0015304d034168cea4a608d9668000d74000e8c1a8590a3cb7528c3b40000000014b086c0000016ac000318000d8c050fa0e78000af0000000bed58d244a98875554cd0f4c000a555cd41c6600013600003f8000000dc46547b4000000000314f54000c840000010f40000000000000006a4000000001468001000000000ae95600a0000000fb137ca7c7450e93d03387ac000f406e0850a140006347a8c0c7b0000000c241a425400060945c00149c000b44000000558d496b13dc000774bb4db06796cc1807b91e9485460000a695d4ead0780010700001dc0003fd4007f8dfd574204b1c308000000cacc9d4c0d0c0000000002f80001f40013a8000e4c000000000778c005d93b80009500000000000011695a8000000ab80001400008a45b400000027c0015e8000aa4000bbd060d4400078807965c000001290380be083000000023029c000000000000e8906cc800005dd40800044d58006856c23c00031cdc8000a44000000000000c6400000140c00000000000000093c62486898c4b00001e53f84ac000000000000000000000001550604000000970184f6c6b0cd8f9160505c87033c2b4000000124dad2340006c4000b480012aca80f810506d4000ce80014b4a2c0000804c074c8441c40006fcb314d0b4cdbd198000000708000e300000000000016b80008a8bcd29cd280010c88cc8f424d5b902021c82d43c000000ca4a38cb88800010c40000fc001218
  | 13 => 0x1fc69c000000bd429800c00000017c0000000007000008a058828c000164a4d454aac000f1c27117c4a16806f5384d945004a89dc000594094cb000000000000000000000000083cc09238e340000013fcfd8228a002415c03446a0e690a42580000b0058e2475c6192e41600015002680000012990e0000919624000000000000000260f3c365320000eb0000000d7c7512f0f94cc8a40ff87c82a40000c84e1018000b005714048d40000010b800111c0e11780010c01b4001188610000c700013d454c8e400000008c0000009b8000000bb9009154000c5cfc520cb8d5b4a8496909d1394ac9241346f840850836c0000000000004514ec00000000000029400116000003400006560c5ec0011dc5f8b54cd53b0c044d507d58803c384e602800002bcf380000013cc000000000000000000a183900000001e0ab4144000000cbd3c4b651592b8000bf40007f4000fb471c154bc87e0000000000000494000e8062c13c3dc0000000016994fd61c000000000640000f7c2e8000001010000c789d54e4208540f1952c26414876c108aa0f3416917000000081d4d8c44001014f9d5a000102c000328000000e440003e48210445f09a53780709003bc910ad101ceb53441100000000001b80002f1208000920000fa800000085d1250ac1ac4f00002c54e1368de40007702d42340001c00600012687e8c88000c18b0c860001381458c3517493914cba0d18848000ce100cf8923d5d061d0240e8b908040015c95200000005fc0001751ec5600015fc8080011acc14c4c000c540000007dc0012f51b922400000000035000000124c6ec00147933400000051892c00056400000148c0005c88e80011080000000006dc000354b3c8d00012600000000010ec00089c0001a0d349b0b140000014c8000000548000000e406d8af40cc5452f8488da55ac0000000000006749bc5d15586c07253a4000f0400000118cebc0000001d82005e497c7988950051e5420001674a58438000bac0000007181c84b51341f11948dcd403492a02e55849fc000000a9c7a087c001181314ff5434000ae00002f4ec000131894800163cf8c720ff0000ce40001b0001074de05511848b1474a1ca0d150404158d4cc50c7448413022cdece0c0016c8b38ad9250000c409cc6cc2b80000007f1370bd847c0000011f83985747d4fb8d6400060c000d38000b88c68000ef0000000000000000000001364f849c033534926c6989f44e8f20be5678000000eb80002200000000000000000000000000000009d00bc510840000000f5c0000000000000002240000000000012b4000f10000d115ec0003d83780313f56d8ca09351900013e800000000000000000109478400108000162c00000135c0000015f4000001328990000d900004c47cc0000000000012dcbf80012
  | 14 => 0xf08000f60000000000000ee55d81d4000000000780e084d9201684740f150b00b8b086455f80001ecd8527d5290840016480003000000000012654a800000000000164c0000003a4000000000538690244044000b294e80002780000000000007fc00000000000169002c0000c4abd4300400000000010d0000cf52e0d80000e841000016b4000000000001220000e6c524000ffc000cf00000000008280006f0000b980000008c0001030b180003e0410ab000000000161863d1007685b00000000000000000000000000000000000000003045f54dc00000025c6e4000001038000490a70000000000944688000000001671490000614000000000000000000000000000928000000000520ed0479498e654d5064f2564514404c0000982e14a4a48811548aa837d21499850cc98000e5c0c037451c0000000000006485680000008b4664bd00000005a4000000f64bf11b10a841ccdc0000005142887e4b349ec3c8000000b4053c0007c50f8c30858088000fe154cb249f00000000000000009ad39069538d0f0000000000df4000000e20001090e100000000000000000009047908ed42c000df8000a280013e45cc5e1115331338c1c00000017125d1a44581cc954000000cecec54640000d00005780000011d0000198000024fa4000e7513000083400116c0000002b0a2400169c0000000007bc000000000000c8c00000000052c00088c0000012c805c000fd4a046b4a880000000013bcfe566435cd047c095d6503d04cc580000b6c00057c2191a09648f0000da044800130c000b800000000016880740000000000010353ece2cdb409c0915940006709851d819453466d6543200008540007305e8fcc001590714c4819d4480000000000009f8000c6c00048c000000000940000af89a11d51fd6292cc67d3b51c00016a0ac4000f590e40004c812000041914
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2200020026830014802b00178aa8011b0291188ca1209a3389a00030aba71ea30e9b970b80228000900a1198132e049533000012800019891c9fac31018e218b05a8963016920c23802f841f2f0d1c10a4138514148000344810028104044848702485010804b8208001095a14000080c2830051625d534c160908018568754c32d85420069454d800cb615080125593a1770d85420068955182d4c6150801a258460b531854200585e4d8454c615080164692e0d53185420048d6548250c6150801a155460f521854211c8d2615454861508018558754c32185420069454d800c8615080183587550501854200685551831406150801a255460850185420069154c824c0615080705c985cd5358241005132497354d6090401a455360432d89410069254d800cb6250401c84415cc321894146f81105530c862504018c97360032189410069254d800c86250401aa041600321894100e1621d534c160c8519c167654d31d91210068554d810cb6448401a195360032d912100685a19534c46448401a148654d311912100629104825cd640840705c985cd53580210069254c824c160084038548754d3158720006856118118f654800145a96dcd30d95200051564676dd7634800184e861cb75d8d200068361182197634800145a96dd770d8d200051564672dd76348001459909cb75d8d2000683611821d76348001c844118c7250520467051d1534c561080018a47420931584200069154c824c5610800705e98dcd63d951000613dcc8258f654400105f985cc63d951000417e61731cf65440018577360432d951000616dcd800cb6544001a158360465d9110005832496354f6444119c167654d31d91100048764e859cb644400181d8754c32d91100068554d810cb6444001a195360032d91100060761d53cc7644400121d9321570d9110006079d9831946444001a169160c651911000685645831946444001a158360465191100068660e701946444001a19835c065191100050765e6354c64440016159198d5319110004872616354c644400141f9758d5319110005832496354c64440016159319651191100058564c6554464440016159319631191100058564c654c464440016169654d31191100069154d810cb6244001a495360032d8910006079d183196624400141d9319574989100050764e75d92624400141d939d464989100050764e759d2624400141d939d5749891001c17a637354e624400181c7460c65589100041766073195624400141d93197745891000417a6065dcd62440038548754d3158910467051d1534c5624400184d8754c32189100069254d800c862440014559319771509100050764c65dd1214400145593197715011000417a6065dcd20440016159319464841100051564c75dd91004001515931d47444010
  | 1 => 0x1e2a24a5800fad801d26292e8600078da9a7ac8f072a8008b29a9580002d320800039da50031800699
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x21800000008000010000a216a0415cc3218941007102e620b00190c4a0803a0153105800c86250401242d4882318e4a0a4000e011d1532093158420
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x4c
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x124c
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124d
  | 14 => 0x124e
  | 15 => 0x138c
  | 16 => 0x138d
  | 17 => 0x138e
  | 18 => 0x8c
  | 19 => 0x8d
  | 20 => 0x8e
  | 21 => 0x128c
  | 22 => 0x150c
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128d
  | 27 => 0x128e
  | 28 => 0x150d
  | 29 => 0x150e
  | 30 => 0xa0c
  | 31 => 0xa0e
  | 32 => 0x130c
  | 33 => 0x130e
  | 34 => 0x20c
  | 35 => 0x20d
  | 36 => 0x20e
  | 37 => 0x154c
  | 38 => 0xb0c
  | 39 => 0xb0d
  | 40 => 0xb0e
  | 41 => 0x140c
  | 42 => 0x140d
  | 43 => 0x140e
  | 44 => 0x154d
  | 45 => 0x154e
  | 46 => 0xb8c
  | 47 => 0xb8e
  | 48 => 0x148c
  | 49 => 0x148e
  | 50 => 0xd0c
  | 51 => 0xd0e
  | 52 => 0x160c
  | 53 => 0x160e
  | 54 => 0x94054
  | 55 => 0x94056
  | 56 => 0x124954
  | 57 => 0x95254
  | 58 => 0x124956
  | 59 => 0x95256
  | 60 => 0xa0954
  | 61 => 0xa0956
  | 62 => 0x130954
  | 63 => 0x130a
  | 64 => 0x130956
  | 65 => 0x10a
  | 66 => 0x134a
  | 67 => 0x139254
  | 68 => 0x139256
  | 69 => 0xa1254
  | 70 => 0xa1256
  | 71 => 0x131254
  | 72 => 0x98094
  | 73 => 0x98096
  | 74 => 0x99514
  | 75 => 0x129514
  | 76 => 0x8994
  | 77 => 0x128094
  | 78 => 0x150094
  | 79 => 0x150096
  | 80 => 0x128994
  | 81 => 0x99294
  | 82 => 0x128996
  | 83 => 0x99296
  | 84 => 0x150994
  | 85 => 0x150996
  | 86 => 0x151294
  | 87 => 0x151296
  | 88 => 0x130a14
  | 89 => 0xa1314
  | 90 => 0xa1316
  | 91 => 0x149314
  | 92 => 0x149316
  | 93 => 0xb0216
  | 94 => 0xb1554
  | 95 => 0xb0214
  | 96 => 0x160a
  | 97 => 0x154b14
  | 98 => 0xd0b14
  | 99 => 0xd0b16
  | 100 => 0x160b14
  | 101 => 0x40a
  | 102 => 0x155416
  | 103 => 0x155414
  | 104 => 0x141554
  | 105 => 0xd1554
  | 106 => 0xd1556
  | 107 => 0x161554
  | 108 => 0x161494
  | 109 => 0x149614
  | 110 => 0x149616
  | 111 => 0x160d14
  | 112 => 0xd1614
  | 113 => 0xd1616
  | 114 => 0x14a
  | 115 => 0xb4d
  | 116 => 0x144d
  | 117 => 0xecd
  | 118 => 0x1a4d
  | 119 => 0x95316
  | 120 => 0x20995
  | 121 => 0x99654
  | 122 => 0xe8a
  | 123 => 0xeca
  | 124 => 0x1a4a
  | 125 => 0x104a
  | 126 => 0x992d6
  | 127 => 0x995d6
  | 128 => 0x21515
  | 129 => 0x150215
  | 130 => 0x18ca
  | 131 => 0xed555
  | 132 => 0x1a5555
  | 133 => 0x21555
  | 134 => 0x3c215
  | 135 => 0x170215
  | 136 => 0xec215
  | 137 => 0x1a4215
  | 138 => 0x194a
  | 139 => 0x21715
  | 140 => 0xecb55
  | 141 => 0xec3c21d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1629
  | 6 => 2981
  | 5 => 1463
  | 4 => 104
  | 3 => 5
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (66789+((h/543+packedAt gbK7 (60273+(h % 543)*12) 12) % 2150)*12) 12
  | 6 => packedAt gbK6 (155004+((h/993+packedAt gbK6 (143088+(h % 993)*12) 12) % 3935)*13) 13
  | 5 => packedAt gbK5 (92161+((h/487+packedAt gbK5 (86317+(h % 487)*12) 12) % 2336)*12) 12
  | 4 => packedAt gbK4 (7518+((h/34+packedAt gbK4 (7280+(h % 34)*7) 7) % 125)*8) 8
  | 3 => packedAt gbK3 (410+((h/1+packedAt gbK3 (405+(h % 1)*5) 5) % 18)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff0f0783fe1fc01e1c03fff0a631f867c27f
  | 1 => 0xf00f007fc3fe1ffffe003c073592e6198fc67
  | 2 => 0xf000fff8003ffe001ffffc007c61cf861f0f87
  | 3 => 0xffffffc000001fffffff8f81f007e00ff8
  | 4 => 0xffffffffffffe00000000ffe0007fff000
  | 5 => 0xffff000000000000000000000ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110e0302805602424604084b100200a823c22b
  | 1 => 0xa123001a40a2091db20328521092660885c65
  | 2 => 0xa0245548002d54048c49580244604b821d0686
  | 3 => 0x840a8956a8000091192a3340b81b005c00950
  | 4 => 0x8088cee65331992e0000c0180ef6000776a000
  | 5 => 0xccf000c062011030010302200ffdfd50000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36272
namespace PEqualNP.Outside.L_meta_36272
open PEqualNP.Outside.L_meta_36272.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
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
theorem bs3_4_384 : Interval s3Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 414 := (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160))) (concat (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)) (concat (concat bs3_4_288 bs3_4_320) (concat bs3_4_352 bs3_4_384))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 616 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 bs3_5_512) (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 22 := bs5_3_0
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
theorem bs5_4_352 : Interval s5Atlas 4 352 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 379 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 586 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 104 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_1440 : Interval gbAtlas 5 1440 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1463 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))))))
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
theorem bgb_6_2976 : Interval gbAtlas 6 2976 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2981 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896))) (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))) (concat (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280))) (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))))) (concat (concat (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))) (concat (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)))) (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))))) (concat (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)))) (concat (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784))) (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)))))))
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
theorem bgb_7_1600 : Interval gbAtlas 7 1600 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1629 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))))) (concat (concat (concat (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960))) (concat (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)) (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)))) (concat (concat (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376))) (concat (concat bgb_7_1408 (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 bgb_7_1600))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80feeefaeafeecfa80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4276943488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36272.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,5]⟩,⟨.and,[2,6]⟩,⟨.or,[4,7]⟩,⟨.and,[1,8]⟩,⟨.and,[4,7]⟩,⟨.and,[2,3]⟩,⟨.or,[9,11]⟩,⟨.or,[5,10]⟩,⟨.or,[3,13]⟩,⟨.and,[0,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276943488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276943488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36272

open PEqualNP.Outside.L_meta_36272 in
theorem PEqualNP.Outside.L_meta_36272 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276943488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276943488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
