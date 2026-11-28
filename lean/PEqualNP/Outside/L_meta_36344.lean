import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36344.Model
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


end PEqualNP.Outside.L_meta_36344.Model

namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 7, 8, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36344

namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x810013dc30bf43be40bd43bc40de30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x270a0a1e610030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => 2*((h/9+packedAt s0K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s0K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fffc0fffffe0c1ffffe0fff07fffe00f3f3fc
  | 2 => 0xc1ffff03f07fffe0f83ff0fff8780fff4c7ccf
  | 3 => 0xfe0ffffc007fffff003fff0fff800fff8f8f0f
  | 4 => 0xfffffff800fffffc0000ffffff003f00ff0
  | 5 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84204628a0101005284e0113008a621811b15c
  | 2 => 0x94448a1904a484a05a1290a54850a4a94454c5
  | 3 => 0x8a914406949094b04252a0a950149528a8b0a
  | 4 => 0x294e20924c0dae729681888ce6658063e00ea0
  | 5 => 0x318c38e38e71cf9ce739ccc0c4460183ff6000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36344
namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
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
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 2 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 3 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 2 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 3 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36344
namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xd7000027c410014000000b7c008000000308000200014a507027fc42fe30ff41bd43fd30fc41ff31fe20fd32fd31fc20fd41fe31fc31fe40fc30fc32fc43fd20ec42fe10ff42fc21ff20fe42ec21ef20ef42ff32ff40ff43fd10ed20bf43fc40fd21fe21ee21ff30fc10fe41fe32ed32fd40fe43fd43ff10ee32fd42ff21
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa800c148780800007000704028186860b8000008811903489080080272aa68003800003850085992a8000190180058a00828c0007810080858083138195000100000c0000020200038001000088a400008083000800000102805b94810d7a18436f53c8278a8905754c42b7a9221af43886daa4185bd4940e721a653c544427aa8084f553309eaa4436d5310adaa7a16b14b439eaa4876d508cadca520db54b31cea1c639d430c75ea5a1dd94430b628a419d434c2dca3a15b14931f3288436d530867ca8185b151209f2a0876e544827ca9996bd0e32b7290616d50086d8a2996bd5120d6a1e416f52c42daa520dbd4132b7294816c54c827aa818dbd4c21b6a94414d5310b3a87985b94a30b729081af43c82dca3194f95031b728c43ae548875ca8214f95330b6a86859d434cadca5a0db94720b728843ad434cb5885a0dbd4941d6aa443ac5250f5ea4a1db54221b6a94813e540cadca810db54a30b6a9a416e52cc27ca910ebd0d209eaa6655c53442dca5084f95331d6210813f54482dea710d794c40b72a2656e520cb9aa6215b54a109eaa6636c52502bca6216bd0d32b6a9683ce5310ad8a4a0db94b31d6a1885ad43482baa6084f55032b6a80857a500c6dca8217350d32b62a2656e5290edca9196b10a40d7a18855f53442dca4105bd4931af29e836d538871a86997ad4120b728885ac54482d8a9195b15221b72a443ad43d0adaa7904f95010b6296216d52102d8a4a1dbd4943972a4436d5210edca9906750f32bb288816d520c67ea8885b54a43baa88816e520c6daa40873d4d32b7294856c54086baa7a0ebd0f42af298219f5350ed8a4886b50e21d6a184375510c2daa7195754c409eaa061ad438cadaa5985b94843bca8063ac42506dea6904b15120
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xa00010200005b04000000000100014908104000001f0016000040000090000001c900d00108499185534828d63151209358c54c822f6550e21c350f504ca4d63952218b993524c68d6310b418758e54886a661d4b439a580540870d4354b30c354c42d062e64947209358c540864d63151208b191528c21d63151208b993538866661951328b992544830d4354831c650d500c62e64946328b58e548870d53108408b99352c430e5454c42c354d43c822c64540218b197434830f6550d32c354f43d0a2c6454d208b58c544830d53d0c428bd97438862c6454232a3592434cb0e6395221a358c421030e6454c42c358c544822e64944218358e548862c6550d20a358e548864c6550d32c9109511022c6454a10a358c429030f5350e21c354d430870c6550d32c398c544830d6395221c354d434828d63109418358c544830d4314532
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x1c080000028338ecaa1a65035ce64d4b10a0ae6212a22040d7399251086063b2a6a1a41035cc645402181ae6322a508505719915310a8238aa6a1a41035ce6494720
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/37+packedAt s2K5 (800+(h % 37)*6) 6) % 50)
  | 4 => 2*((h/90+packedAt s2K4 (4455+(h % 90)*8) 8) % 165)
  | 3 => 2*((h/55+packedAt s2K3 (2280+(h % 55)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s2K2 (490+(h % 10)*4) 4) % 10)
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
end PEqualNP.Outside.L_meta_36344
namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1673c10020000031111c95097478406c00476001416c3ec21bd43fd20ff42fd10ef42fc32fd41ff31fe42fc10fe40fc40ff30fe32fe20fe31fd31fc42ee21fd30ed20ff20fd32fe41ff10fd43fd21fc41ff32fc43fc31fc21fc30fe10bf43ee32ff21fe43fe30ff40fd42fc20ff41ec42fd40fe21ed32ef20ff43
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1880000004862782028380020501818580460e83ac8001000c02830d8000010c820e06801f86013786004a8911840100b5001504870100030404002e8101dbd4943b6a9487ac544827aa9984f55332b72a0436c514cadaa598db14b10b6a86855e53042daa010cf95331cea1863ae5410a7ca9995b14520b7290635f53442daa4185b542329faa2416e544827ca9985b54a10c6a1a656e54886eaa2206bd5120d6aa4436e52082daa0215bd4910b7a82656f524c6daa6904f55243d7a9687ce5310b58a5a1eb50e32b6292873c54442dca9904f550109f2a0872c54482dca8215b54e21e6a9885af434cadaa7905b94442f5a82415d53102dca3a15b542219eaa663af5250f3a87986bd0e32bca80636e52906daa5a0e7d4d43cea1c636e528c2baa6084f95032e7a9a656f525035a86906b50e21e6a1a656e52102dca4085794c40b629283af43482d8a4a05b94843b6a94815e5310b5884a0dd944309faa2216d520427ca8185b54f42baa88616f5348358a4a1eb50f20b728c436d521035885206bd0f20bb288816e52cc35a87a15e94031b7294856c544ca9aa6216b95221aea98856d538ca7aa818ebd0e21d7a1e859d43ccadca9194f952219f2a0216f530879c86995bd4b10cea1a656c54c82d8a8904b95221b7296635c53442daa6215b54a41f3288433d540cabaa7a0db14910b7a9e416e52842dca3905b54a30d6a1a656d5210ed8a910dbd4e219eaa4436c524c6dca5a0cf15120b729487ad430867ca818db94832b72a265af43086dca210eb10840b7294816d52cc2d8a9196750d30b728c65ad4310adaa5105b54831b7a92836e520c2bca7a0cf55030d6216836c54086daa610ebd0c42
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x30420444a05408112508200000004214200000000000100d3409a580540861d6395221c354f43d0b0d43d4132a358c421022e64d4e21a3592434ca2c6454021a358c425060d63952218b992510862f65d0e218bd95438862c6454d208758c544828d6310a408b99352c422c6454a10c3d4d438872442544408b197434822d639522193195434cb0d5310840c350d52cc22e6494720c39915310a2c6550d20c350c514ca2c64542329358e54886646154d208b992518ca8d6310b418b191528c20d6315120c358c544830d5310b4199986544ca4d6315021c354d434822d6315120c358e548864d63151208b992544830e6315120a358c544830e5454c42c354d43c830d4354831c398e548868d6395221c3195434cb0f6550d32c354d430870d53d0c42a998752d0e2e64d49319358c54c83194354031
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xc900400c28238aa6a1a41035ce6494720a0ce3b2a8699505719915310a06b9cc9a9621031d95350d2081ae7324a210c0d731915008682b9884a8881035cc6454a10
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/30+packedAt s3K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/62+packedAt s3K4 (4455+(h % 62)*8) 8) % 165)
  | 3 => 2*((h/34+packedAt s3K3 (2280+(h % 34)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s3K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf0ffffe0ffc3ffc1f87f87fff0fe0ffe91f33f
  | 1 => 0xff07c3ff0ffc3ffe1f87f8707f0ff0ff6e4ccf
  | 2 => 0xfff803fff0003c7fe007ff807ff000e18f8f0c
  | 4 => 0x3ffffffc07ffff800007fffff01f00ff0
  | 5 => 0xfffffc000000007fffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x12008022008400002008809110120224009115
  | 1 => 0x205104442500500a088308222104a05826444a
  | 2 => 0x4633aa8a63aaa8d6e445d5057aa0668d8b8f0c
  | 4 => 0xca433108a220965555044084cc94c01d00aa0
  | 5 => 0x88c6221ccc3332799e66664e08818811fd6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeee8888eeeeeaeaeeee8888eeeeeaeaeeee8888eeeeeaeaeeee8888eeeeeaeaeeee8888eeeeeaeaeeee8888eeeeeaeaeeee8888eeeeeaeaeeee8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36344
namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x63ef42ccbf680a07e4c220bfa8283ef214827ca8197e84010beaa665df53486fca1a15f14532eea9c417e53106fca710df54730bf28c417d544c77e87a17e94032bea8c87fa401037ea88877d4d42bf292217f52502fca3214f55010bea90817d50d0efca9985fd5120bf2a421f741907ea6290efd0040bea9e81be4350eb8a6a15f14f21bea9c417e52cc2fca7087bcc932afa9a437e530cbdea4a1dfd4941bf2a2617e50d0f7e83a06fd0842df208817f54c42f8a710df54f41bf2a665dc324c37c84a177cc030bf29a217e51903da859077d0d43bf28e857d540c77883205fd4e21bf2844376510caf8a8995fd5021be29263bd4310fda8421778cb30bea84837e50d06fca5a1d794c10ef98c63dd314c3f660985fd4f20bf294837e50882fca6215f94842bea9a41fb20482f8a0a15f94f40bca8065f541107e883085f54420bea8443bf4310f7e8320df94230bea9c817c51483dc40905fd5330bfa90217d5090bf681205f94442bfaa265dd4310efaa810fed4141bf290657d52cc7f0a0a0df94841fb108437d53c427aa8197714d21f690e417850506bca7105f15020beaa241de434c2fca3905f14540f7996417d53486dca4085f95230fc206217d510cadaa408770ca31bf28c43ec42ccafca9905fd4c10afa9a85bf4290bdc8590778c531b7294617f54442fca421df94631bf294817f54486fca020df54b40fc200217e5410beaa2197d84110bfaa021df320cafaa9205f54c40fda06217d50ccafaa6087e8c120bf298417d5110afea7085f54b30bea90877d508cafca990df15310be29a21f631486faa7a15f95121ef192617c54cc2fca521df95131beaa6637d538caf8a090fb90842f790041dd300c2fca4185f54a40be2a243df310c6bca6205714d21bea9061dd320cafca821fdc8621bfa9a217c525077c80a07750f30bf29c87f441042faa6215f15210dfa08837d52042fca4085f94f41fda00217e52c42faa9085f94042bfaa6637f54c86faa018df94641be2a6437e540c2faa9186f50441f6a90817751502faa0195f94a30bfa82877c52442f8a8985f15120f790843f541442faa8995f94440bf28c87ee320cafea9105f551109f2a0217d53086faa921f34c832eea9821df308c2f8a2985f94632bf29c837c535077ca8195f94232bfa9421fa300c2fca018df54720fa88021ee21486f8a8185f55220bf29e217c5150afaa520df54640fb88421bd41502baa7105f54630f6192417e50906faa3a17e88020beaa2437d54c82fea8985f948209e2a2217f548cbeca2207bcca21b7a9263de53102d8a4a1db54a30bfaa4617c52842fca410df94f20bea94617d51843ec6218df94a42bfa98417e540cafaa021df14943bf288617d54082f8a7085fd4f10bea8e87ee52102fca121df94321bd280657c524c3ea6218df14c21
  | 1 => 0x802070040500a0741f07009018040240010c001345e594050000700014000040000000006000030044c06410018a805c2c0ec0c09c3e00808088410000200c1407c200440a02efaa70877d0c32ef29c417d53c86fea8195fd4142bea94876f5250fea4210df55010bfaa4217c53882fca518ef10440bfa82437d50c86fca6085f95031bf29a437e530c2f8a098df95021bea88877e50042fca221fe4c120dea1a857e518c2faa2206f55010bfa92637f544c7eca2195f15032bfa9a43f541c42fca790df94040bf28041f641107da84905fd4131dea00817e54442f8a998df94b31bfa9e43dc430cbbc6518df14d42bf2a4417e53882fca0195f54632bb28881f641443de43907754c40bf280617d54886fca918df15220bf29a41f751503b86418df14f20f629263bf41502f8a5887dd0610bea8c41f551102eaa2195d14540fb88021df328caf8a60877cc730bea94217f54c82fea4a1df94043be2a6657f5350afca198df54740f721241ec5250ef8a7885f54341f7294617e51d02fca2087bc8220bea98417f514caf8a0a1f750d30ee988637d5090efaa920f794c10bea9683bf4390ef8a4087b48520bf2a6217f5150efca118dfd5031f7992417e544cbee4290df94c31bfa8a85bf4350afca3985fd5020bf288657d540cafea09977d0e43f6190437c54086fca210df14d21f6900417c54042fea918fe4c030f799465de4310efaa6887b94810fd904417f51482f8a6a0770cb30bf284217f54ccafca1217bd0832ee98e61b541106fca6205f94e42bea88617f514c37a84217b54810be29a413f54442fea610fdcc531bea9621bf40903ee82a0df94021bf2a0217e520c6faa990ef15110be298417f52c42faa620df54910f7a14857e51d0ef8a9185f54732bea9c85ed320cafca8905f54231bfa9c417f52442fca5195fd4d20be2a465f531886fca820df55330bf288837d540c2f8a0a0df94b40bda82837e54082faa518df94240bfa9a83bd540cafca998fe48020fba08217d538c37ca8085fd5221bea9c63fb10442faa020ef90640bea9c836e52103de84a15754c10bea9c43de43cc3f280205f55232f790c437d5010bec83885f95232f6a9461fb308c2f8a918fd14540fca80657c5150efca5086f50740bf29c817d548c6fca820778c130fb98c637d520c6fca420778c932bf28841f631886f8a4a07e8c220f6196417d5490afaa198df54b43f6194437e53086fca7a17ec4210be2a6417c504cbb887197e44010bf298877f524c2f8a818df54f20beaa261ed21087b8a6a17b10832bfa9a817e510c6fea2a07bd4931bea8043df438cadaa4205f54342beaa621ef32086fca3995f54a20bfaa061be41506d8a498df54841bf2a4437d52886f8a910df54642dea1e857e52d06fca1995f15131aea9881df314c2eaa2205f15110ef19
  | 2 => 0xcd050000000013402190ba000240013b0000a0b08801c040cc011481c0680a048002e81e00400000015ac000d0004b80005401004000300c0e86e1786b0103e0002f0900900c09008110080a05000000400506c00003028001781505d21008070041c0055a5f02400c070040000004054400001d244a00345b04d370802c0047f02c090004507807000101f0e302401014001a4010300001c010ec2d000140dc29000021142700004044250740e00c1001809000000000000c001307c0140001c01000020001f00
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb5384354538c5219d58754c82b860505409ed95300c33a4114141dc147405027765484219b988505074f4314943b318d42c825f6355121a7590324c2cc6250c439bd89534865d631501097d8d544ca3d6414810cd147415023d6414f219718d544833551d0040cd145415036a6094a30b3d95320cace644c8329d98454882b46150040e3951320cb1d54d0c329d584540ca796510010d554e511033954940329d9845308678654c120dc946500ca5e63141418f99053c87355410410ae181411066d62951319798e50c87556114d21d594e511026c625513197d95310c67565104109b594420ca5e63d5221d994a511027b6548020d314f4250a7665905109d597410425f6355120b9189318865e63d5010dc181511026c6254f409798e534865e63d52208f590530837341141419e58053c865d63d50109e98053c867b6055110d3548320c65d63150209798c5304274654c5218f992524431e5494c10b318d21482cc624c530ce551500ca5d6394020d314a314c65d63d52208fd9541106e5610cb208f59641102746154d20d354d52102cc6250f309b98a5090e3e6414c20d394e520426c6254c41e3d0f420cb4e5354840b358e320cb376550441b6980324c25e6315021d394b308c27b60551319b98854043c932940329e580530863e6494d109bd8953d023d64d4810cd552510ca3c64549109b98b54042756114f209ed9540103b06050441f20c9304823e6415010cd551510ca6d62d50109bd89544ca5d6394242b318d210863e6414f20bc181411071c63550329718d521063f6454d108fd91524423e6414c219b58a50cc74e5354810ac18141107b341d00109dd95411063d64d4e21c755153042776155130ec90440c427b6055121f14ca510ca3e65151109d984540cae5610ca219758e54486cc63508429b58854843345190140d394e52103c932540329bd89534433551500409758c520423d6414c109b588540434d53948409e596100423f6454d208f992544426d62d5230c714f4350af161103108f592534432e54948109d98754c827465505109dd95310c7355190440cd15141c42f061500409b98854843b36050441da588505073551104409d584548c2ac6250f429b98852042ad640c9209d584540c2d5610c930cd55110042cc63487209b98b530838d544c8329798c54043c532544329b588540c6ea628c120b5584328c65f63548419e181544867a6015021add9541106cc6250d309b588530429d640cb3097d8d52d035a6094e209798e544866e6214c109b18953c423d6494910ce181540433854c41109b596520427a60d50329b98b548c7c4328c621cd553100427661951329e58354cc67561d50329bd89544c73a54940329718d52c426e6215031ae18141d032e5454810cd18554042776154d209798c548834f654c832
  | 1 => 0xa0d008023a2101c9444000b0080802000019052210600600040400c040e060800b0084400010004c082c010041e000510808002380000342f01c0e790f0480005020b478010a06c00120041c1603008006200158040c1108094005d0080004010013886010020c08000000002ca00074080c010081a00000a4020700000a81093010000d00098000001208001308818486800158040102b94100a1a80422020017436002500d5275260365c6354910da988505065d63152208f990530427661150309b588548c26c62551309b98a544c73a54540329e980540ca5e6314810cd505501065f654c030b398e204826d62d5231d954951102cc624c730c755253042b564904419dd95100423d6414f209d984540427a60d53319799453487365494432d694d308825d6314141d9584524c7345490510d314e214863d64d4c109e98354c866e62943319758f528425e63d4a108f993538865c6355121ba98032482f060505109bd95200823f65508428f997415033454505109718d52d033654544329798c548427661d50329758f520433561151109bd89544c27561152209d58754cc334548411097d8d52c423d65950329b997324827761551209b58b530423e64148109bd954210b4d530c821b318d424826c655092097d95320cb3954d0010ab59032c82776155110cb189540cab464440109798f520426d62141418f99352042f060507109e580540ca6c6254d108f191534434d530cb2097d954310f7251540329e980540c6746155130dc546500ca5d63d522197d8d524427960d53219d984548c2ce628c130b3191320ca3d6414c219b988548c27860551318fd954310e6e62d4c109bd89531075a63141419e583540ca766114f208f596540423e64150329d584540826f654c8329e98053082766114c20dc545500ca7960150219ed95100432d54d08329798e5090a6e62d5230d3d4c328876552944409e980530866d650c8218f993530435963141419bd8953c42cc624c4319758c54087565354440cb552520431e5454c1097195434c25d63943219d586544ca5d63152109d98754cc25e63150309798e500826e621502097596530434d530c920cd55341042746155120d354832cc2e5610c920d9949511034e53c8220d554d511026d62942438fd95401026d62d4e1097594430ca3c6454d20d354d520425e6315020ec50740c42766115020d354e520426f6548421ae19110042756114c209e580540c66d6215030b558432cc2b46050441b358c420cbb04110010cb551520426e6215030cdd5041842cd6210c32b3d81320cacc614c8329b98
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x8000c0362980080000000000b82aa264a8865431d1530c920a88e2a9864906305418141c4258bb48220621c25513254032a1ce9a986510ea2721814110698bae83a00210d1d95444010e8264a8aa0196317518141106c4ba06498241a45cc6050441c60a83028288649635885050750b90c0a0883705c4324c120c60c2302a808631651044004349398c0a0883319c6644c832
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8000c11755cc6050441c21755c86050441c81735c86050441
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
  | 2 => 3
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
  | 5 => 2*((h/216+packedAt s4K5 (15822+(h % 216)*10) 10) % 586)
  | 4 => 2*((h/154+packedAt s4K4 (14402+(h % 154)*9) 9) % 379)
  | 3 => 2*((h/21+packedAt s4K3 (1078+(h % 21)*5) 5) % 22)
  | 2 => 2*((h/8+packedAt s4K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf87ffff03e3ffe0f1e3f8ffff1c07ff831f33f
  | 1 => 0x7f83f8ffc03ffff01fc7f1c0fe007ff9ce4c3f
  | 2 => 0x7ffc00ffffc1f1ffe007fe00ffff8e060f8fcc
  | 3 => 0x800000fffffe01fffff80000fffff007f00ff0
  | 5 => 0xffffff00000001ffffffffff00000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x9105011804420030208824650451250109315
  | 1 => 0x1228a1220c98c0700c431088a20a25a0c64c2a
  | 2 => 0x21093244940d02952005a412349308320b854c
  | 3 => 0x652c4892820652a56900024c92c40c5700ab0
  | 5 => 0x4463000e313189cc9926493800300107ad6000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf888f888feeafeeaf888f888feeafeeaf888f888feeafeeaf888f888feeafeeaf888f888feeafeeaf888f888feeafeeaf888f888feeafeeaf888f888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36344
namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc0ef32de32ec32cc32dc32
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4014078e540cb8aa2196355032e4a80654e528cb8ca2197294032
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x3095454032c1551510cb415154032
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | 2 => packedAt s5K2 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt s5K4 (80+(h % 15)*3) 3) % 5)
  | 3 => 2*((h/9+packedAt s5K3 (189+(h % 9)*3) 3) % 7)
  | 2 => 2*((h/1+packedAt s5K2 (114+(h % 1)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffc7f07c7ff0f1c7e3f07fc701ffc33333f
  | 1 => 0x1fe1ff8ff807fff01f8fc7f83f801ffccccc3f
  | 2 => 0x1ffe000ffff878ffe00ff8003fffe3830f0fcc
  | 3 => 0xe000000fffff80fffff000003ffffc03f00ff0
  | 4 => 0xfffffff0000000ffffffffffc0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x424828813009100304120901941144a8111315
  | 1 => 0x84845012019220300884423028828950444c2a
  | 2 => 0x4844992452834155200e90528d24c2190f054c
  | 3 => 0x81996248a50432aa5d2000a5324b1062f00ab0
  | 4 => 0x11118000c62444cc924924c6000c0003aaa000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888feeef888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36344
namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x60005801f00800800890430830030713c2042147007f84001fd20007f54c077f54007fd4003fe4200ff8c807ff41017fcc407fc4001ff90003ff20007fd4801fd52017f0c4077d54007f88403fc42007f48405fe43007f54005ff3000ff0c805fc4301ffd0c01fd3201ff55007fd4101ffd0801fd3101ffd5005fc30007fc4007ff40017fcc807fd4201ff95001fd5101ff50c01fd3001ff90407fc4100ff14801fe30007fd4401fc5100ff94801fe5001ff15001fc10017f94c03ff21007f94407fd40007fd4c01fd10007f14003fc21017f14c01fe31007f88003fc20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xc4204ff14310007fc6290827ff64d4c13ffa98a200ff18532027f8c9280a7ff4388405ff29aa609dfd5352007fea29000bff43d4c01ff108200affc8510007f8c0a90077c52d4803773146039ff50b51007fc438805efd644c0077e326a609ffd525102ff84208013fc4054001ff28a4200ff94531027fac928027f9501407ffe212a62aff90931005fecb18827fc5294475ffa026439ff503510eff8c4a8003f53148413feb1ea409ff98b51005fac710002fd6388403ff9944039df55351007fec1288affe644c409ffa04a004ff90050087f8438800bff534c013fe288a004ffcc250007fca2a880afe65d4c39ffa18a000ff8c550117fe8328012ff6248077ff982a429ff9022104dfccb188f3ff4054801fea8c6009ff99350007f8a310802fd6114003ff2124220ff8ca50007fea29880bfc438c401fe3024225bf59350007fca2a8002ff6348003fb90c4200bf5825103ffca80800bfb308c02fff2a2600dbf59210005fcc3280d3fc4054449ff986a000ff58153027fc400801bfc53040057eb1c6200bf98752007fac2a80bbfc2114409fe2826009ff14b5108ff8a788003ff628c4017fb02a409ffd8f5204ffea9a8813fc20940037f3142008fd90710047fca988003ff5148485fea0ea600ff5463120ff885a9813de6314061beaa0a200bf1855004ffcc5a9803fd658c4077f3244240ff90553007fc4298013fe20c40075f3202000df146500bffac89800adc6348413fe2a6a600ffd4a3000fdc8490077fe4254003fe102a416ff08530017fc87a9833fd4344009ff31ca002ff0c953027f841a8097ff41d4013fe2a0a009ff14c51007fcc0a9002dd6314075ffa0a6425ffd0350005fec29900bff304c805ff98aa609ff95051027fc6108012fc631402bffa1c401cff50450007faca90813be6404003ff9924002ff94f53015f8c6a8013fe4088051f7994422bf750d3101dfcc8a802ffc314405bffb246200ff14620017f88718003fe604c409fe2042001bf58a200b7bc64980a3fe6388463feb24a204ffd4250007fac0a880afc6348003fe1026404ff0c2300dffc8628003fd5294053fea0c4209ffd45501fffcc4a9807ec324c8013fb2a2004ff4c220025fcc110813fd20040017fb02620cdfd5110007f8c2a98cbfe42544037f316a200ff4831004ffea2a8813ff20940817fb22a602ffcc15304dfcca9000bfc308c47dfe206a409ff94c5000ffc64a9002ff62544037eb144229ff15221007fc630800bfc534c009ff324a028ff90e211a7f8c8a8827fd63d44097fb142000bfd9621017b8629888bfc4194009fea002000ff145310d7f88428083fe5294011fea062007df550100f7fe64a8072fd6414027ffb224000ff4cb5000ff8851008bff42940077e3226002ffcc931147fca710803fd3294009ff2024018ffc8630
  | 1 => 0xbfe524c001ff30a402dff952310fff8c8a80bbff201444fbfaa24200ff98530017ee631880afd63d4c01feb12a031ff19251027fcc42804ffc64480077e3226200ff8c6201eff887a9003fd5044043ff29ca004df59410005faca988d7fc2194401ffb02a201ffc8752015f8c6908effe5354813fe30ea008ffd0b1004ffea2280037e5194001fea982020ff10a501a7fa86a88ebfd414c83dfe18aa00effc861000ff884a9027fd5414405fe29c6225ff50750007faca9900bdc324c001fe30a4016ffc8130007fac728827fe64d4c49ff21ea000ffd813216ffea91880efe64d4c85beaa6a60bff18d10005fac588027fd60d4401fea9e203eff50f52007fccb10803ff63944057e31ea034ff991510fefea8a802bfc6244001ffb024200ff48630027fc6090026fe65c402ffeaa2603aff15132017fe86a9803ef624c401ff32e2009ff1535000dfcc51800bfe434c8077f326a200ffd462118ffca928813fd408c009ff31c4037ff08751207fc80a9803fd5144013feb16a632ff989511d7fc8299013ff64140037e310a200ff9462004ff8c3a984efd6448013fe306a200bfd8953027f88090003fd62c4005ef98a6033ff0c55104ffaa628827fe53d4003ff2144002ff94d321d7f8c8990677d548c001feb0aa600bfd8553005dac518002ff624c001ffb02a602bfd8d530bffe849808ffc42d4001ff302a601ff10932007fac69006fff32140017fb2a4018ff14a3004ffca9a8827fd54d4833fea146001ffccb52007fc62900d37f5454445ff20ca004ff1865006ffa8708023f541c4041fe194a036ff0c251025f8c0a9812fc638405bfea146200ffd9531007fea60800bfd534c043ff98ca002ffccb5300ff864a9013fe658801ffe18c202cff14a31027fcc918067ff548c001ff32a6000ffd4620007fccb188b7fd408c409ff082203bffcc552017fa6318002fd6088413fe29ea201bf18a511eff861a9007ff20d4819ff322201fffd9150005fac1a88b77d548c4077e322a400bf58e511e7f8c8a9027fc64d4879ff20aa401bfd892106efea908013fe65840015fb222001bf18b5000ffe6510827fe61d4057fe2026200bf5875004ffea5a8827fc62144097e32c2001ff90920007fac4a9812fe6094017fe21a2009dfd4750007fca290003ff53c40577fb226200ffd8a5113ff88090903fd4154c077e324620aff9891001dfcc928803ff624c001ffb122004ff0c110006faa2a8003ff6154863fea04a203bf19350015f8c6a900efc6494419feb222002ff90d53007fea488013ee6214047fe196a003bf1913209ffcc8900f7fc31d4809fe280203aff59132017fc629880efe6414009fea846031df5525100ff864990f3fd6454813deb26a200bfd813212ffc83a80f3ff4154805ff98a6424ffcc7500057ac9a890bfe40d4c037f3
  | 2 => 0x5010ffe6528013fe204404dfe21a4201ffcc952007fea4988d3ff6454409f6b146002ffcc130017de6499053fc3188009fe1062004df54050167bc651880efc6444013fe28ca000ff59530007d8c4a98277f53d4813fb288a204ffd8a10217f881a9827fe63d4001feb126217ffd013004ff8c628806fe6254009ffb1c401eff10d500bffe8298013fd5084009ff2802004ff98450007faa72880afe6384021ff1962015dfd5220157fe4298803fd520407fff212a609ff58753047faa9880cffc30544797fb22a403bf99250027be6118027ff5254009feb14202eff08051005fec6a8807fb20480017eb2c4012ff0c520027fac310003ff63c4009ff2862005ff8c81004dfcca28013fc6214027fea1a4000ffd952100ffe4290826fe6544073ffa16a200ff54b10027f860a80c7fd42944077f322642bff59131207fac8a9806ee6204001ff32a6200bfd8f1000dfcc498027ff5254413fe306a404bf9825100df8c51884f7f5448001ffb04422eff8c85104ffaa7a8813fc508c003ff9926404ff08130027fcc62806bfe42140057f31a423aff90132027dcc408027fc5394467fe21aa204ff9025004ff8c9a88337d5444001fea8c2000ff4811000dfecaa901ffc41040037e316a63cff9015204ffca42888bff4394013fea90a218ff08630027fea008003ff624c479ffa1aa402ff50d310effe42a8003fd65480017eb2e2000dfd9510007fa64080b7fc648c4057f31a4005ff94810027f8802800afe63d4819fea022000ff94621067fa8488027ff61d4c11fe20e2000ff88630027fc81a8003fc654803ffea1aa02cff08631017fe8699013fc64840137e32c4200ffd4310025f8cb18003fd6354809ff2826001bfd8120087fca588087fe4394001fe9962025ffd0f50007faa4980f3fe645484ffea1a4200bf58a3004ffcc9a8807ef2148013feb1ea000bf5891014ff88110803fe3114013fda82a009ff15250025fcc118813fc6394053feb244202ff8c930005fac1a9802ff6544001feb2e2004fb98a301aff8c528843ff20c4009ff9002004bf18c10005fac7080cbff2154419ffaa2200aff1491004ffea7288cffc6354413fe28ea000bf586500bff88298003fd3144083ff216a619ff9523004dfcca98003ff654c813ffb10a200ff4c851017f8629888bfd4194009deb20a030ff10451005dac428027fc5454801ff18c4204ff18c10027fac728003fd214400ffeaa02004bfd9620027f861080f3fd4154809ff184400fff10e10027ee2008027ff53d4401fa98c4234ff59151137f8629080efc6488403fa10a4202ff14e3006778c88800bde434c057bfaa26207ffd0810005fac628027fe51140013eb282000bf98753007fea50800bff3254c05fe992603bff90d52027f881100c3ff4214409fe308a002f794d300fdfac8a805
  | 3 => 0xc1826005ff0c81004ffca9a9013fc40d4009fc1044003bf99350037fe6208013fd64840017e30a6400ff54a5100ffe4310827f75194433fe20c600fff14e1004ff8a4a80f2fd6454821fe1962034ff50951047fcc988053fc4388019faa0a2000ff98251167f8c518826ff6414401fea8a4002ff4ca311d7f8809901ffe4104013fe2a2a604ff58a3009fda8490083fe429403dfe31aa001bf9895304ffcc628803fe5194005ef98c6211ffcc710027fcc508013fc658c009fe1844031ff5525116dfac918803fd2154001fe98aa034ff50151027fa41080b3fe528c4013e32a2001ff90952047fc83880d37d5454413fe29ea435ff8ca511fff8c4a9803fe60484097e324a004f758e20007f22008003fe31d40017fb2a6022bf592500bffc82980bbfc3214451fe31c4230ffd0051005fec2a90d7ff20944077f3224209bfd9352015fec098027ff64d40097e324401cff50c5004ffea328003fd32d44057f31e2003bf9921017ffe6228803ff53440017eb06a401bf9881013fda8490867fd548c013fea96a203bf99010005fac52880bfc31d4c03ff90c4000fb4852004ffcc3a9013fe64040017eb2a6029ff50e21207fcc8a9827fe52d446fff196a201df94b5204ff8a4a8807f82048001dfb222002ff0c930007f62088027fe51d4001fea8a6202ffcc530007dec4a9813fc50440015eb202039bf59351167fe41188377d5484033ffa146009dfd53531d5fac899003fc604c403ff2126400bf98620027fa8108003fd514846bff294a223ff90b5000df8c4a886ffc3114023ff31e202dff55231097f88690003fd6154863fe20ca204ef5901001df8c8a9813fe6204009fe1824002ff54e30147f86310803fe608c4057e31e2001ffc8520067f48088027ff60d4813fe31ea404ff98a5004ffec1a8813ff3004009df320a040ff1015303ffe8208007ff5248009ffa002009dfd5050007fc4288023ff41c407dfea06a40dff50a10007fec4a8002ff61540017fb1a200aff0851013ffec89080afc6314453bfaa44200bf5963004ffea3a8003fe6154001feb04a209ffd905117ffe6028823ff40c4001ffb2a6011ffcc31004ffec5a9833fe5444001ffa826002bf98e50077f8a5080fb7d54d48097e302a201bf58b5204ffea9a9003fd5154003ffa92422dffd0a3100ff64110037ff5484049ff996a000ff4c610015bcc608012fe6088005ee1946211ff18f1000ffa85a900bfd538c401feb1a4216ff989300affa8710012ff6204001fe90c2000f7d8d52007eca388013de63040037fb1a6404fd5845000fe8431082ffc5344009ffb0ca004bf9805000fde4310833f64144005fe21a6204ff08010027fcc518026fe658c005fe1826237ffc8351005fec0a9827fd54d4405ffa9c6004ffd8810137f86090807fe4288403fe296a400bf588
  | 4 => 0x26fc654c009fe314a002f714d530eff842a809ffe54484097e31ca001ff48620027fa60080affe544c413ffa9aa231ff9065116ffe811880bff308c401fe30a6000b7d8d211b7fe6328807fc5288013feb16a23affd9132007fea088067ff418c02bffaa44000ff4c620017f8a698833fc41440117eb26200aff94910007fc42a80c3fe4014401fe9922000bf59532097f8c69009bfc53484097e3146002df14d53027fe8118093fc31d40137e32e2001fb94b52017f86299003dc63548037f316a604fd44010187fe822889efd644840ffea08201fff50950007faa518027ff601446ffe196a215bf59220015fcc710803ee2148421fe2162004ff99220027f841180037d53d4871ff98ea200ffd8e21017fe869804f7d5448027fea024009dfd5350027f42008013fe404c075bfaa2641fff95150007b8c690827fe60d4411fea0e2029bfd9221007f8a298003ff5384011fe2a62008ff59310027f8c708013fd5088073ff20ea200ff1971003ff8a8080af7d544c403fea124006ff90c10007fac48807ffe6454009ff1042000bf58851197f842a880bfc30d4c13fe29aa002bfd9553007feca88013ff61880057f318a20cbfd91100dff8862800efc64c405bffa0c6206ff94c10007fa6290047fe43c40337eb246013ffd5120007fac528813fe658c019feaa22004ff59410027f8cb10007fc5248005fe21ea609ff15051027f8c710003fc654c0017eb16a239ffd0751007f62108013ee2048019ffa122004bfd9010007fc4308017fc4204023ff29e2018ff94a30187fa822880efe648c413feb10a201bb18931007facb10812ff6504013ffa9ea401ff48520005fac728013fc508405dfe210a202df14f53027bc6098013fc409402ffea0a6004fe9021015ffa80988d3fe5454411fe3262004ff94230027fec808003fd51880056f31c4031ffd025117ffc86288dbff3094463ffa0ca204ff19050007fec4a9807ec214844fbeaa24231bfd9251167f8411889ffd4048401ff32a6417ff15130027f860280d7fe62944057f31a202bff50931077f84308003fd5344083ff90ea600bf58a31017fc65180f3fc40548017e30aa601ff50921007faa090013fa5014013ffa90a002ff0c553007f8c2a80b7fd648c4017f30ea000bd98450027f8cb0806bff2114005ffa9c6204ffd4230017fc65188a3fc4388451fe1844200ff98132017fc86980abfc524c42dfe2126004bf9835304ffea8a807ffd40540097f306a200df5475004ffac9a8803fe3194073ffa06a203bf9931004efea2289037f5454c017eb282001ffd4a211c7fe61a8807fc5248401ffb046201bf98a5113ffea890803fd528c403fe10ea400ff4c5211aff8412887f7d5454005ff29a6002bfd8531017fa6518027fd6314409ffb282004ffc823000ffea510037fe5484005f
  | 5 => 0x4050006f8ca8800bfe538c005ff21c623eff10752017fca718807fc2188065ff902a22dff50631027fea108003ff5348001fe988a000bf58b53027fac918002fd65840057f31aa237ff083510b7fc84980e7fe40d4485fea06a609ff98b5000ffc65a9006fc624c013faa88a215ff9522016ffcc918803f93088069feaa2a204bfd8e1004ffea2288b7fc548c453ff3244200ff5822104ffec5a880bf4318c401faa8e2020ffc8650007f8ca99027ff64d4801fea9aa004ffd8e50027fac71003bfe52840016fb1aa43ebf5935200dfec499007ff2154863fea0ca203bf9935204df8ca8805eff644c01bfe20c200cffd0510127f887a8003fc604c809fe186a006ffcc810025fecb0802fff3044013fe30ea40cffd0110027fa802810bfd42d4c47ff90ea004ff14120025f8c508003ff514c003ff10a402cff10a310a7f8a710006fe628c477ff31aa401fbc8121005fec690813fc6314013ffaa2a202ff0ca3000ffea499003fd604c813fda84a004ffc8210007eca288002fd6344003ff296a404bf9835200ffe4299027fe63d486dff21ca209ff152511b7fca728812fe6084039beaa0a004ff59050007fac29907ffd6454001fea9aa202f7cc13104ffea9a9807fc214800377310a002ffd4d31007fac518802fd618c033ff20c602bffd913110ff86328003ff6354801fc9824000ff9822101dfcc8a9002fc614c009feb1c2001ff14a210bfba869800afe6354009fb8842000ffd8d10007fea690837fd5484003be292a411ffccb1014ffa8110813fc2044005ff98c6009fbd495214efaa910813fe204806bfe214a23cff50d52045fcc20800efc6448445bfaa4a009bf9865100df8c498827fc52140277fb224017ffd91300b7f8c49808bfd4394071ff21ea202bf58e3004ffea828027fe5314401fe304a209ff15351026fca0a804ffe54480137e32a6204bf18152027fe200800bfc328c4017eb1ea02fffcc85100dfcc498813ff6494009fea80a000ff48450027facb18037ff42840013f3282009bfd9353097f8a690002fd61d48017fb0a4002bf98c10027fca088013fe6304009ffb244000ffd962103ffe8608033fc6444053ffaa44200ff54e1004dfcca90827ff5354001fea922009bf19521007fec6900abfc214c401ff32a4004df9941004ffac5a8013fd4088001fe9862004ffd8850057fe40880effc3154809ff2002015df55220057fc6488007fe2148405ff9926000ff14410007fac0a9007fc2148403ffa16a402ff50f53017f886a9802ff654c805fea1aa600dfd4651047fe878800bfc3054c13fe29aa209ff54f52187fe8628803ff604c405fea1a6431ffd9251007faa310813fe40c4003fea14403cdfd51521aff86528803fe6544005fb98a6200ff58530007f8a3880ffff2154c13fea88a002b798c50027fe6118
  | 6 => 0x1ffb2c622cff98a31007f8a3188b7fe418c413ffb18a203bf1905100ffc6490827ff54d40057f31ea22dff10631017bc8698803fd5388009ff3242025ff50b5000ffe4090013fe3004005ff98c6204ff58630027d840900d3fc41544037e312a02bffd513105ffca6880a6fd6488477fe31aa400ff5852014ffca910827ff5314001fea92a000bf5823100ff8a49902bfc4244009ff1862013ff55120027fc81180037d5114409fe2002004ff94150005fac690013fe6414013fe296a002ff4c931017fe65188c6fe6114465fe102a204ffd0210007fa63a8013ef2088057fe20a622aff949311d7fea899027f75154409ff9842000ff4875003dfac808003fc615484dff31a4232ff8c951157fe4098803fd624c009fe206200cffd91100effcc4a8077fe3254013ff320a201ff4c92104dfcca98827fd60d4801fe992a001ff94921007fc6208003ff538841bffa0c2027ff10521007daa490012fc65040015eb20a009ff9885104ffea0a8013ff6114001fea8ca02eff90851007f8a318013fd640404ffeaa24202ffd0e3000ffc4310027fc6414409ff1826001ffd0920005faca88012fc6048401ff18e2004bfd8c1000dd8c4a9827fc64d4c097fb24200bff98d10007fec6a88fbff40d4881beaa2a601ff08621187f88028803fd6048401fea92a201fb0cb5204dfec9a8003fd5348009ffb18203dffcc352027f8ca08002fd6014403ff9024203bf991201f7fe83a900afe63d40077f3226217ff99130006fea6a9017fe4204015fe1922038ffccb51007fc422806bfc2114083ef196a602bf98e2015ffaa898877fe5254001ff2882040ff50153017fe87188b7fe408c409fe1042003bf191510fff882a8003fc6054413ff2a6a628ff14e21007fea710013fc404c0037f310a040ff50953205fac8a9803fe51c4001fe98c421dffc815005ffe6288027fc5254c03f6292a401ff50a21017f8a7a9827fe53d4419ff20a2010ff90b101cffe87a8807ee5248081ffb22a609bf99621017f88699097fd43d4001ff30a6409bf9945104dfccb10003ff6548003fe106a401ffd495204ffea8a98afff424c4037f314a000bf58f100cffa8318027df5354c05ff18a6009ff9505000ffe8490813fe5084009fe2844009ff54750027fac2280e7fd41d4401ffa882000ff54a1004ff8a5a9863fc428c065ff292a202ff54d31137f8c690867fc548c0017eb2a4209ffd4a50017fc87180affc644c401ffa8e2000ff58e2104ff8a628012ff6414009ee1826004ff0c25018ffe8728803fd5348443fe21ca00eff8ca100fffaa8a80effc3054813feb00a209ffd4b5009ffac890003fe514c005af29ea63bff10d52007faca98813fe63840017fb1aa004f758c50027f06118073fd4214001feb1e2004ff18a300fffe84a8013fd6294001fe9942004dfd
  | 7 => 0xa8027fc62d4c09feb10a002ffcc13106ff8a908013fc618c03fff20aa01cff1045007ffc8708027fc64d4017ff9922004fd841100f7fe62a8032fd61840037f312a209bf9961004ff8a728013fd6588013fe29aa400ff9463000ff842990f7ef32d48017eb2a4004ffd8c500c7fc8518002ff6354801ff10ea000ff58d1000ffa6510807fe3288047fe10ea009ff953501effc87a909fff41484017ab08a001fb0c92007ffca70800bff5354c09fd1844004ff58c5018ff88128813fd1004013fe29ea006ff0c41004ff8a9a910bff42d4c2bfe20c4009ff5905104df8ca9000adc635481dfe2142001f78c932026fea12800ebe6414069ff20aa200ffd8553007fe2088002fd63d4813ffb16a000bf586200fdfec8a8003df6348401fb18a4204ff08120197f864a88077e5254823fe18e2001ff4ca2015ffe809881f7f5404003ff9044233ffcc5511d7fca8990c3fd4314401ff28c6200ffd4630007f8cb10827fe53d4801ffb02a402f70cb53005dec49880bfd434c0037e3162000ff18153167fc85188afff414c405ef982a625ff503501cff881a8813ff5088003fe216a409bf99410046fea988013fe619404dff9824200b758c1013ffcc89089fff4048403ff1924009ff98f51007fec298013fe4044003ff2944000ff1451004ffec1a980aff634c4137e32c6204ff9412014ffaa910813dd6304019ffa1a2000ffd853217ff86228827fe5114439ffa10a009bfd935100ffaa490013ff618c061ff208a209ff18051087f8c5880a7fc64884097fb246035ff90a51005fec0908977d54d4055fe1026200ff58d50005fcc22803bfc3284001ffa8c6209ff5935000ffe8510827fd5314001fd1824001bf18953027fa81280fffc2154c13bfaa0a23cdf55152027fe4110003fd3044079fea02a409ffd8f51027fcca08027ff549403fffa02a01effcc15007ffe6308026fe654c801feb1aa204bf1885001df8c890012ff6388009f6b10a002ff0c53000ffa84a908bfd4294003fe102421fffd05501f7fc83a9027fc5294013ffa8ca215ff552201bffc85a8803fd53884017fb162000bf1852000dfcc588003dd314c0077f320a212ff98d2020ff843a980bfc5354c1bff20c2000ffd8550017fc6498803ff5048001fe98ca003bf9915300ffa849905f7f544c003fea924201ff0cb52017fe65180cbfc62544097e3246040ff95153005dec4a9803fe6154803fe292a400df54d52025f8c528027ff5454803fe992400cff50510007faa498807fe5248013feb26a600bfd953109ff882900cfff305447bff98ea434ffd0151015fcc628003fd21940077f3226001ffd0a2000dfcc428803ff62c4013ff30ea600bf986301d7fa8099033fc5444009fe102a010ff98b10025fec6980d3ff41544017eb0ea604ffd962005ffc86880eb7d544c80
  | 8 => 0xf9863118ffa872889ffc5448405ff29a6200fd8c621007faa0980a3ff3088483fe106a600bf596310affc831009ffd4148413fea88a22bff15131027f8c508007dc324c8017eb2c4201ffd093212ffe85a809eff6448413fea9ea01cffd045007ffe6508006fe62d4081fe20aa609bf1953216efea918813fd6584001ef18a6204ffcc050025fcc00800bf4314c401ff28a2026ff90d2100dfcc488003fd6544009feb102042bf59353007fcc2a98fffe5254c69ffa1aa204ff84010005fac40800bfd534c8097e3026409df1445004ffaa9a9812fc64140016eb1c4004ffd8a3004ffcc9a902bfe42440017fb122009ffd8f5019ffc86a88dbfc31944197eb222004ffd923000fde40a9012fe608c03ffea0aa029ffd0221017f6609809bfe5348453ffa0c4204ff1923004ff8c5a8803ec624c401fea8a6000ffd895100dfec4a90e7fd43d4409ff8842034ffd095100ff8849081bfc4304025ff98a4000ff19631025f8c808013fc3004003fe1924031dfd525104ffcc1a90ffff2054c09fe100a004ff1922004ff8c7a8003ff520403dff21aa000bf58a50007fea288002fd6348401fe992a209ff15150027f8c808007fe3288413ffa9ca001fb0ca2108ff887880eaff644c809fe1862013ff905201c7f863a8827ff53548017eb18a204ff902100eff884a8012ff658c009ff30c4040ff55153015f8c6a8802ff65484037fb0a422effc8451017fc65a9803ff52c4013ff290a004ff9863004ffec3a9003fc518401bffa1c201eff94d50067f28088007fc2088409ff9844034ff5055101df8c9a90bffc3014413bfaa6a209ffd4f50027fe811000afc63944075f326a200ff1822102ffe4208057ff4188035ff190a004ff9405017ff88628803fc608c4617eb20a204ff1023004ffaa42800afe6354809fe984203eff9035214ff8831080afc6388401faa8a2004fb5881004ffac3a9083fc2194013feaa0a009ff1515104ffea42880bff534c803e61926410ffc8710017f86498903ff4254c7dffa1ea401bf18b511a5fac8a8802ff6054409fe1044000bf58b50007f8ca88027fc62d40077f322a202ffcc531007fc43280aefd644c405fe21a6000ffd493000ff8649089ffd6448403fea944204ff0c13019ffca6a88affe414c403fe10aa432ff1095104ffca5a9827fd61d4005ff18c6026ffcc5210b7fe42980037e5154485fe20ea602ff14d32017bca7a984fff4148005bf29ea604ff9422004ffec9a880afe6394403ff2944222df55250027f8c3100b7fc408c44fff20a4200bfd853006ffa8308012ff6494025ff9824004ffc8050007fac118827fc60d4c11fea1e2000dfd4550117fca92801ffd4304079ff2a2a409ff5835300ffaa510013ff5014027ffa02403eff5075220ffe41a980efc6454001fe990a000bb588100eff864
  | 9 => 0x80a801012003000010807800008a7500080000080000282180100380202e80080000300c80581181500000180480100000480080001b00e80000b02101f01c00080000001980380100003d00280900080100b00300001380980200380300400e81b0003a100811484a052057fd4188009ffb2c6000ff14520046faa98801ffd4204001bf288a004ff59220015f8c7a9003ff528c4077f3246001bf997521e7fec8a9003fd6254405bf29aa602ff50e3004ffaa5a8007fc4288413ffb0ea001ffcc921007fca3080c3fd4014401fe9882001fb90921007fec690803fd604c413ffaa0a204ffd921000ffaa49904fff4348081ffa0aa608ff50b1000ffca4a9017fc520402bfe2a44000ffd85201e7f882a901fff540402fbeaa2600eff90a10017f865a988ffe32d4003ff2926404bfd922004ffca5a8053fe4388003ff192643cff55152017fe63a9903ff4054c017eb182003af19110207f8c8a9803fd210406dfe21ca217ff50130007fa6388043fc52c4059ff90c6208ffd5310017fe869880efe6488039ff208a000ff4c120017f86318053fe5388061fea10a242ff907530d7f86428027ff5294437ff988a004ff58c101d7fcc8990a7ff6488405ff192a601ffc8152025fcc028812fc6204001fe32a6200ff4871000ffc85a90abfc624c455ff3126236ff98e51007fec6a80fffc2054c09fb308a000ffd4610025f8cb10007f72148433bfaa4602bff901310fdfacb28013fe3044009fe310203aff1053213ff8c890803fe6054413fe290a208bfd9310117faa928013fd6194071fe186a238ff10f51007f8ca9084ffd41480017eb142012fbcc92012ff883a805ffd424c0097e3242001ff0ca21005f8c2a9013fd500406bff90ca227ff90121005fec710803dd534c001fe28a4200bf58f51025f8c7100d2ff645444fffa1a4204f798e20007fcca9080afc63440017fb2e2037ffc8751147fe63108ebfd544c801fea9ca012ff90d200b7f8a49807bfe6354053ff20c4200ff5431019ffe64a8807ff4254847ff906a017ffd513009ff8a89000bfd314c009ffb14a002ff0c132047fec9880d2fd65944077e326a209ff18f5118dfac928813fc40440057e31ea201bf1891000ffe409900bfd438c46ffe216a239ff10751007fa42980b6ff648c463ff324a209ff98353097fca69005ffc644c001fea9aa40dfe5021018ffe85288dbff3294401fe994a200ff8c51018ffc8128807fc4248001fea882009ff980511b7f8c728813fe40540097e302621fffd0d50017fe61a990bff40d4c13feaa6a009ff14550027fec708003ff65c4055fe2126200bfd895000ff865100d3fe4054413df326a233ff98d51217fe83a98affd414c413feb26a414ffcc620027fecb08003fd51c40077f3222004ffd0050017fc8698802ff624c405fe18c6202b
  | 10 => 0x53018002000000003804ad780100400380f00001501280100000500000c8139aeab100000003189983480380780001a00580380300000100080303180d90b13500300000481200181b80980001b80900080c00705880040700980880281700281700102680201605000600000b00000000101280e00000000000001c8090000008138010018030ec0000008018078198030098008000008238000099be002801808a9b00e0040c780384903000280080800d81780100181f00500380000200004900012480080182c00c80000f80980007e00981f84d809a2a80401500300300794f00180305000783c81304300000000a83600480781c038b1780380980000780480400080000000680100380e80100800a00000200080000c80480000080400400000080281502b82580f00083a00280000000001f00201884801380200502d8008c100a00000200603100380081c00380380000300000e81b00100e80100200000000100181080380000683b00502700e05f00000800080000d01183b81501308c80100001d00480500080880300109e00480400580081083d81100202081b13880000380500000000180202c80000209801700a80a0008028028808000060040001cc80001e00a00000080280000401916c00480f80480380000080002a0058000170220013a303580000580000380005600200a81f0098088098108c500028d01b81783a80c8cf00001081e00501500080400300000000000600080180102e80d80000000580f0020110040048c280f00883480100000000080500e05500380688c8162f4000839a8d80000600502a04517300300100083084814b80203f80500a03680100180400680209580000580d0000000162fb80800104d00402700001200000001001400e01100000c0328028000000000108cf00180d8000000000048010008ba8048000bb84181300d00680032900f00481380000100004380480801480004400980480081580680000581500405900180182880000180c00202c01580f80800103300880900200200700182300482801a80580c80080180000902001507780680100500b01f80000a05c2a200701b91f80000500081680201b00000701301082880180080000018a07100e80881100300600100280080e80200080182a80482e80200481301f81480e01b80000500b81980200182500000c00580003380332300500082801980a02b80c00001d80001000f00480100003100180001c00600028080b00485300093380a04980280c81500c80800100200100080483583381e80480100301400880600a01400f84480080080581680002200200000601180000d80080080100001000280103a2b581e80180a02400100a00107300386b01c86900000000380100700285801e00c80d808001800003000021883
  | 11 => 0x100600b00180880080000180098780000200a004800800025811000026846002001803aa28
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7058a30396f631d853204ef4549845001cfc74d8520006bc73593510067c211951004d7e71944502f5df744c5300067c43594103a6f621d8532006f42158450005bd7499521007e9524c12004d7e758c55004ebe535935100cfc72580510f4ff7359530007754119510006b96444010004fd7458f10016dc63d4d2002eee5258810026df1058c50025fa76c41100067f54d9520004fc7158e50004fd764cb51006bc71590500067d65d46300067d65147100067d545835204ef77158753096df30d8d200067f54d8910026fa6018251006f642984500167c7654d52004ff7358351006f541986301feee7618953146de4358e210067d658c4100067f5459410026ed5058850024fe76144100d7cc324c85004d7f74d4550166dc628c53104ef5759845004efb5058351024fc7654a100067f65d8d1004ef75258450006df7458c1004e7c65d4910156f7624c521006ef6218153014dc7358910085ec7254f10024fe7688450084fd72d8b10006be72590100067f54d9631015dc734863001cfc7458630004ff72583511b6de5358e5100cfe7258c501eeee53d8953025ee7048520006f6419863004cff76d46300067f64d95100067f6514520014ff7694631166de72d8d21014fc7358a510dedc4358c50006ed4258a5104edf5458c500067f6554710054fd768861004cfc7158a510b6df2158e20014fe76545310eeec3258352004ff7654f100247c7654550006fb60982510d5ec724c45000cf8764c12004e7f5458353004ff741855304e7d70195100a7da434c2200063d649445001cfc74d8d510067f72d95103bf77548c621006dd638c45001cfc7458231004fd7458d1013ebe64484500067d54185200067f42d9510005df73589510067d651441001cfe74d8910006ef43588500067f30d95100f67f535963001cfc74d8931005f571d4110004ff7418530096ed3258a30006f54158620157e571189310067f541853000cfe7259630004fd761453001cfe74d89530067d5458a100067c4199410096ec3158a30056ef20d891001cfc74d81320067e6419510007764119510004ff7258650004ef7259531146de63d8e21006ec7258d10005f47154951007cc7348520004ff76544100267d505865004f5e639445044fcf52d8d52024dc7654d30005f9708c71001cfe7458753004fd7458851006f960181511e6bc6454910004fd73d9710004ff7458c510067f654c51002eef715881004e7e6519530004ff7358a5001cfc74d855022f775454710014ff7658e2104e7f73994100067d5458e21145de73d9621016dc634c12000cfc73d8930006be62d911004edc5158c50056ec6258910146ef30d893104e7c65d412004e7e7019510004ff725805104ebe5259351024fc7058b510067f3159410006f7765471000df4728c621447cf5218d52
  | 1 => 0x9050006ec70d893104ef554984500067d7359410024fc7058a503776d548852100779401951000cfe7258e10004ff7458b51155ee7299531025f87054e50006df43d8d5201cfe745951001cfe7458a3000cfe7558f52006be5359010006dd4358c500067d651963100cfe7598752006ed4258a10045be74d4710024fe709865004cfe7518532147e7328c62100eee62d4810084ff7688410006be53d9110004ff7458620025f0705451000cff764831017edf3258c51206bc6454d10006df6314521024fc70587520edec7258d50006dc4258c100c6ef2158a3020ede72d8d52024fc764ca10006de54d8d21004fd76146200f6dc32d8d500067d545885144edf51d8d521c5f77159531014fc735822107ede43d85300b6df3258e20026f4109845004cfe76d951004edc5358f52006df7358d21006df735885101cfc7458f10006bc63d911000cfe72d85500f5dc735495001cfc74586202ef5f544c53004ebf5059351004fd70d9631007bb64c41101b6dc639452104e7c65545212757d7014650006ed71d8953026f4105865004e7e76d4550026ec5058a30004ff7258f10014fe7359510004fc7654931006dd73d9621024fc764c6500b7ea424c12004ef55398450006bc7359050027da6344010005bd74d45210067f5458a30014fc73d9520006bf6458910004ff7558630175f671d9621006bd715935104e7571195100f5f97099530406df6518d52066be71d9110016de63d4c1004e7f5458c500b7cc3258930004fd73d8b101a6bc6454510024fc764c45016dbe74d46310067f6548110004ff764c8511c6df3058f510167e63d4d5220f5e32d4d52024ff7059410225f974c4110006bf3259351004fd73d8151006f76154550137d4634c521014ff7658e51026775058450027db734c2200067d54d9710007f270947100b6de5258e20006df63d8552004fd74d8d2004ef75198752004dd73d9621004fd7458e210067d54d8552167e6428c521004ff7459610026ec2058a50006ec7358850004fd74d8152006ef3258810004fd73d8152004ff7458e500267f10594100047f74d9510026f4109865001cfe7459710006bd6494410006dc63181521fcfd76995323b6f531185320067f6599532004ff745952100cfd715881020cdf735953201cfe7458b50236f66194410016f4638c521006ec641893132d7d7594550006f96018231007f12144010004ff7458630006bf6494510005dd73d453100df6724c521004ff764cb510067f5498630005bd74d45100067f545971020edc42d8d52027f010d41100057f754c8500067d54d85300b7cc32d493001cfc74d951004e7e651952104eec5358850005bf7458520005ef724c520006dd6354e5001cfc7498753056ef21d8910004fd75d8532006dc40d8d21004fc7688550007cc724c530026e
  | 2 => 0x157e4724c621006f6439845000dee72d4120014fc7358851026f6209845004e5f5458c50026de4058c50004ff74d81210067c4299410005ef7254d5019e7d5359631014fc75587530b6dd2158e200067d425941001cfc74d8d5200cfe76d895304ebe5059351026df5058e2020ede3258b53026ed405885004cfe76d95202667c10d95102667e5098750004fd7518520004ff74d8910014fd75d8953467cf53d89531efcf30d8953025fa7094650005df7348710024fc70d951004e7f5458b510067d6419510006dd4258c50014fc73d9510007d87054d3000eee62d4a31004fd72d8530026df4058c50026ef50588100057d7588750007e63188521004fd72d8131146de63884502767c5018550005bf7458151005f77154951016de638c62110ede4358e5004cfe75986200075d53d4930027ba64440100057c7558131026f4405845004d7f7354d520c6ee5258a30006f661546500067d6519510006de32d8d10024fc70596311afe4219452101cfe74d81520067c321951004e7f54987521b7d7319463101cfc74d9621026dd5058c1000cec7258f50004fe71d9532004fc7158352014fe7398750026df30586302767c401951000dfa724c22001cfc74d9521006f4325845020f5f75d8d520067c71594100257e7054550006bf74586500076f54d8931005ef724c410004fd7459710026dd1058e20106ef2158a500b6dc32d8930005ed72d8e51006ef42d893104cfe75d8121006ee64d89530067f54d8d2101cfc745891019cfd7654531006ec71d8953136dc43d8d211eeef43d8953006fb609815301cfc74d8e21004fd7458a51006ee71588500067f54d855301cfe7458910085fb7058520006ed6248410007e5314852001cfe74d81530067f745941004efb5058352006ef32d891001cfe74583531beef2058b51006ef6258153006de7458c100067d545845004ebc525935139fce4218d21167d721d8d21005ef72585301dede75d8d52194fd7654521007cf628c5310067f5458a500b5de7254d30006dc635812117ef5311855304c7c7558910025fb764c220005df7354950004fe7654d100267c7059410095cc735492014ebc64885100067d43594100067d5458e5024f75545451000cfe72d95201feec42d8953166df638c521006ef4158850004fc7158f50006bc6458d100047d7459410024fe7058c10014dc7359520095ee7354920004ff745971004f777154550006be65d9110006ef64d893101cfe7458850005dd73182511c6de63d4410006fa4058231016de634c610006df54d8d21004fe76d4b10006df4358c10026ed105881000cfe7258e50026ef7258a500b4ff7258d20004ff7058b53136df31d8d210067e63d95100b6ee32d8930024fe70d8953006f66188450004ff745805104c7f7499410164de7618d2104ebc535
  | 3 => 0x870d911001cfe745963104e7c6514510004ff70595320b6ef20d8930006dd40d8d52147cf3258e210277a50d4130005ef7259531004fd74582211cebe64d44100067f65995311b6dc3258e511dedc6358d52166ee62d8a31026de3058e50006dd634c45001cfe74d8132026bd3059050024fc7058a510067f54d8d5001cfe7459410026ed1058a30015dc735493004c7f7419510004fd7458353006ef6254531006dc7158c50026f630984500267d7099410004fd76d4b10026ee5058810025f67094710106ee5258a50004ff74596310067f3119510024fc7614410005f7714c3100067f4399410006dd64d8d52006df41d8d52024fc7058851007cd43d89311967f5259621004fd7654a310ee7d52596201bef621d855204e7c6594530006bc2159351004fd751853001cfe74d952101cfc7458c51004fd70d89310b4fd764c12004cfc764c7500b6dc5258e20006dd43d8d210067e42d9510024fe7098752026bd70590500067d71d9510007cc638852104eef5358850026b71059010006f96018131004fd76d462004ebf5259351004fc7654b10014ff764c610004ff74d8b101b5de73d8a5100cfe725961011dec724c7500057f754c650026ee1058850004fd74587530067d545963139fd57118d21006fb7058d10006de32d8f1000eef604852000dec724c521006ef624851011fcc324cb50004fe71d815304e7d76d465120f5c32d4d52016dc6354d501df5c6354d5200cfe71d8910146ec30d8931016d4638c52104ef6545845000cfd768c6210a6ed32d89300067f5458b10006dc614c530007d4614c530004ff74d8f10004ff768c450024fc7058650006df7358910006de71d8d52004ff7458d21005dd73d4930156ee42d893104cfc76d4e21006ef62549310067f7559531216be64d4c1007ef631d85300b6df7258e2001cfc74595301eeec53d8953006dd6418d52005f47148310006dc7558c1002eec5258810004fd74d8121004fd73d8520026fa6018151007d7734c62104f3e74d465126fb410d9110004fe765493100cfc75d895000cfc7258c50096ee7358a302667c30d9510006ed42588510057f75585200fdbc7458550015de718c53101cfe7458b531fdee7298153245f57494510005f7714811001cfc7498620057cc324c91035d7f749465016dbe7418231006df70d8d21155ec7259531026be7059010055ec724c5100067f655491016dbe749963104ebc7559050095ec7348520004fd7688650004fd7498753024fe768865000cfd70d8d200267f4059410024fe768c6201beef2158b510267e4059410147e771d893100cfc7258231056fa2058221006f56154650006ee715881026ebf71d9110006f4619455004cfc765411000cfe725941004e7f6454f521eeed75d895304cff7654531036dc5358c10006f44118550
  | 4 => 0x8520005df7354a10005bd741825101cfe74d8131024fc7058f520073f65d9110004fd70987520075d54d8d520075f6354d5201cfc741852001cfc745963120f6f20d4d5220edc75d8d5201cfc74d8151145ef724c621006dd64d8d2100dee72d452020edf6399532005df7154d30056ee4258910006ee7458a30086ef21d8b1019ef63158753004fe7688550006ef6258131024fc764c6100067c7558d100067f6554d10026f77058450004fe76d4530004ff764c8500067c65c41100065f54d8d21006ec7258f50174fe769452104ebf5359050006ed65189310057d7598532006f731584500067e52d9530157e6424c52101cfe7418532026dd7058c10027d963440103afd5434c6210167c63d4d52006de3258e100067d65d4610024fc7058a300076f7254d520067d6554620004ff705885102eec2158810004fd70d89530067554984500067e73d951000eee6254a300067f54d8b10004fd7458c10007b76454510026f7715865002cff7648710005f47154a5104e7e6519520004ff74d8131194fd7699621004ff7458f50006dd7258c10004fd751853201cfc74185520067e74d9510006f57398450135dc735952104e7e7219510006ec6258153004fe7614510026dd4058c1040e7f7654f52024fe70d8532015de73946310067c658c5100067c4319510006ec6298131004fd76d4e100067f4259410026be1059050004fc7654a310067f54d8930005df73549300067d5459532006ed62d4810006f4435845007ddc7354a10024fc705862008edc3158f10005bf7458530006fb7644010004ff72596100067c54d95100263d5059050237775494710024fc7059521076f521d852004ef4515875301cfe74987530267f3059410006f5618c45004ef7545845000dec7254d2021f795444010086f521986200067d54d8950024fd768c710006ef41d8953006ef3258b510067d654c410007bb70d9110004fd72d953000cfe72d8553006df735953204cfd76944103af77544c6214267d6454d5204cfc75582213e57d745445104e3f5059351166dd42d8d21026de5058e2004eef51588503cddd748c531006ef3298752006f76198520006ef625495101cfe7459630004fd72d8550004ff74d8d51006ed6248630004fe7648550024fc7654a3001cfe741855200df6728c52104c7e76d9510014fc7358b500067f6554510004fd7648750006df4158c10027eb624c120086ef2058b10006f970d8f100075d5418d52147e431d8931024f47654510004fd7218553024fc70596200067d5458750004fd7458231004ff7059521026df7058c50004ff7654a310b5ec7259530166dd72d8d2100cfc765495104ef45158450006ec54d8931006df6354d51006ee73588500a7da534c22000cfc76d45210c6ec32d8d2004edf5358f52004fd70d9521067b
  | 5 => 0x4fd74d85530277a654401000df8764c120004fc764c520004fd7458f513b7cc3118931006dc7358b50004fe76485300067d5459620147cf30d89311b4fd73d9531005ed72145200067d5458753145de7318221056f52158620006df634c521166df42d8d21004fd7298630014fe735862004cff7654120136df30d8d2101cfe745875204ef653984500067f5458e5101cfe7418550006df74d8d21006f57498450006fb609822101cfe74986300267d4099410004fc7158f52024fc7558f5004cff76d4e10026f51059410005f77154d51004fc7159530146ed53d893118dbe7418251014fc739875200cfc7258f10006ed415885002dec7254c10006f76194550024fc76484503dd7d749455100eec62d49312667f71d9510005f571d4f1004cfc7558f10006de3258231005ef7254e10005dd739463104f5f7354f5201cfc74d8d20026f77158630007db634c120004fd7498650004fc7654f1018ebc64945101eeef53d89530057f754ca50025fa7014530026ee5058a30006bc64589101375e53d4d2108efa30d81310067f7559520006dc7359521267766194650006f671d97100257c7054750166ee628c41004cfc7558b100f5dc734855010ede5358e50024ff73d95300b6dc3258d20006ed6418931004fd70d8d52006f44198450014dc7358851004fd7458c511eeed30d895301cfc74595320067d54d95100067f54595210067d65195320267d2059410005ef7254120095dc7358520004fc7159630005f4714c11004cfc7158e5104ef75198750005ed72d4521004fc7654910016de634c810004fd71d8d20006bc535901004d7e7194650026de1058c10006de7458c50026ed3058850095cc7348520024fc7654c10004fd745865000cfe72d8d2004e7c6514520006ee6518931164ff72d8d210b6dd7258e20004ff7258d10006de40d8d2101cfe7458750006bc53d9110006dd63d4c100267c5059630006f67458450014fe7358b1000cfc725971005f5e53d4d10004ff74d8d200067f4199410006df4258c500067c7558d20007eb7054920004fe768c550004fd76541100067f65885100067f54595310067d619445045d7f7454f520c6ec5258a30196ee62546300b6df5258e20004fd71d952004ef57694710166dc32d8e21176ee6214410006ef7259532026bd5059010107cc324ca500067f6558d10026fa6018153006df7158c50135de7398121006dc7458c50026dd2058c50006ed54d8931004ff7258c50004fd71d8132006ed40d89530067f65d4521026ef5058a30196ef20595210067c64d9510006ed6248650147e7324c621004fd76d45300b6dc2158e200057e751823101cfe7458f50006ee4158850004fc764c951007777554510006bf6454110004fd74d9530004fd73d95210067d54d8d511b4fe7619531004fd731
  | 6 => 0xf72d952104cfe7518520014fc71d8d1016ebe648c450147d7304c621004ff768c650096de43d8d20167d421d8d211ff6c7254f5204eed525835204edd5258c50026fa6018121006df63d8121006fb70595300067d54d85200267c10594100b6dc7258e20004ff76549302d5fb7058d20006de64d8d52006ef7258b1004e77545845004ef67198750004ff7558c10005fb705451004d7c754cb5130ddd7454d30054fd70d89100077b7054550004fd73d9510007f23144010024fe70d8d5104cff76d4d100067f401951004ebf5159050096ed7358a30146ec63885210067d5458f51026dc4058e20167e4328c6210267e109941004ef8505835303ebf715901015dbe74d45312767e4019510074fe768851007ef531d85300067c6219510024fa76c411000cfc7259630026f6405845004e745158450004ff764865004cfe71d9510005dd7399521026f74058450004ff7158a303267f6454550006ef3258a500067d5458251006bc6499510004ff7058e51004ff7358b50026ec2058850006f5425845017ede6314620004ff764c910014dc7358b5001cfe7458630014fd7218532006bf3159351026dc1058c5004ef4515875004cfe75d852004e7e65d4c1004cfc7558d20004ff725825100cfc7259631004fd7298450004ff7258f5104f5d63944502667e20d95103a4ff764c6210067f5458d2004cff76d4d2004ef75198753097cf32d8d20007f051440100067d54d8151004ff7258e50014fe7358a10006df6318121004fd73d812102eec32588100067d43195100267d3099410006ef32d8b10006ed6254a1004f77615475000df4724c521154fd764c5210067d421951004ebf755935100dec7254d52004fd74d8d520067e43d9510004ff735835239df671d8e21005f47154d51006f5435845001cfc74d953201cfc7458f52006de6418d524167f52d9532007e5318852101cfc7498752026ec405881025f755494510004fd745962004cff76d4f10006ed62d4a30004ff7258c1004e7c65d45310067f65d41300d6ee3258850014ff7158c10006de41d8d5204eec5258b513075f5454d303467d6414650005ef724c620004ff764c810006ec65d89310067d54d8d20006ef725952004e7f545805104e7c655471000eee6288630006ef73588501b6dc3298753006bd735935100feb6054920006dc6518d2109dbe74d4520006df40d8d21006f441d855004cff76d4b10004fe71d952004cfd72d81520b7cc3258132004fd76d4c10024fc76d4e2001cfc74d8d1004cfd7318553004fc7158d2004e7d749941023fb864c4110014fc73d9621006bc325935104efb70583520267c7099410024fd73d8930024fc7654e20026f47058450006f77498450004fd7654d21146ee43d89310057e7598532006dd63d4410026bc7059050005f9708c410
  | 7 => 0x84500067f42195100b6ec52d8930167cc21d8d2126ebe10d9110006de7258c10004ff7648530006ed41d8953006de5458e20165ee72d963104ebc5159351015df7554d30026be1059010006f74258450005f671d4910026ec7058a3020edc20d8d521eedc3158f52014fc7359521026f761c411000cfc72d9510006f74118550005bd74195200067d5498620006bc7359010006ee71d8953004fd768c6200067f54d9531006bf64d4d10006dd70d8d21006f761985301fdee76d89530067c654c5100066d54d893104cff76d4e210067e4259410006ee75d8931006dc63d8152006ed6214410164fd72d8d21105ec724c6501fddd7399532004ff7459530016dc634c1100067d6594631005bd74d4710006f5614c45001cfc745875239ede3218532195ec7258d51026f6709845004e7c6594610024fc7558750006dd4158c10056ec32d891001cfe745962004cfc764cb5104e7c655413020edc72d8d520057d7094551006f94058051015dc7348530006df64d8d52004fd7418552014fe7318520007eb7048520004ff74d963100cfc725953003dbe74d441001cfe7458051025fa7094710006de4258c5036d7f74547502767e5018550267756194650007f17094710006ef3158810026bd5059050026fa76c4110006ed624c85004eef5258b51006be7259050007e87048520006ec3158850065bc745891000dec724c12004e7e74195100067e62d9510004fd76d4d21006f96018251006dd41d8d52466ef51d8953076ee4258a10006bf74589100076d54d8953004fe71d8930006f56194650004ff7359620195ec7254d510067f54596210067f755962104e7f6494450006ef6248710006de4158c100267c305941001cfc74583510067c52d9530006ef6518931005f571d43100c6ec2158a3004f3e74d455004e7e65d4410167d6328c5210f6df30d8d50004fd7654a30005f97014530006bd72d9110006ee5458810027b9644401013dbc7458121026bd30590100067d65548100057c755852004e7f549875000cfe7654521006ef6254950005bd74d4631016f4634c52104e7c72994102667e30d9510025fa708c710027f26144010016de6354e104267f6454d52007bb74440101d6be644c810005f77154a510067f54d8e21006bf644c110146ee30d8931146dc5358e21095dc7359520006be3259050006ee41d895301cfe7458450014fe7398620414fe761953200cfe764c120004ff7458a50006bd72590101fdec7258553007d53148530014fe73d8b10006f47498450026bd7059010016de638c620166dd20d8d21006f661946500165c63d4d520b7da324c120024fe70d8d52004ff7359510006bf73590100067d6514621026dc3058c50006dc7359520006dd7458c50004ff735971000cfc7654521014fe73d8951004fd74987501acf
  | 8 => 0x16f8638c1201dddc7358152004ff7159620006dd6388450106ec3258a501c6dc63d45210b5dc7254d30024fc7058c10004ff7358051156ee624c4100077b65c4110004fc764cb100075f6554d300067d6554c10004df7358b50016de634c65004e7f5458c5100dee718852101cfc7459510007755154110024fc76486102c76d5454920004ff7359520004ff74d8d52006ec62d81530067d41994100067f5458e20007cf73549200067f725941001cfe749875001cfc7458c1004e7f6194551136dc30d8d21006f76198550014fc735875000cfc7558352004fd7614410024fe76d4e20156ec6258931004ff7558b10157cc325853204e7f5458850025f470945101dedc31d8d52146ef32d8e21006df5458e20006ed42d8520015dc7358a31014fe73d8552166dd52d8d21005f970946500067f6558910006dd638c6202cded745492019ede53d8d5104e7c7199410006ec41d8931005ef725855304edc7654d30024fc7058c511feee32d8953015de73d4130007f151c4110004ff735961004ede7558c500067f6594510086ec2158b100067d545881000cfc72d8d51166dc3258a313a6ef6118931024fe7654a10006bd644c850026ef7058850014fe73d8910006f7439845000eee62483102d6de32d813237ded7488521006bf64d4510026dc2058c1004cfd73d81530057f7558930025f8728c120005fb7054650006bf65d9110016fa634c220004ff745941011eef2058b50004fd7458352025fa70d4610004ff7458d10006df7358b500067c545941000cfc7648110006bc3159050024fc70594100067f65996310067c65d8d100076d5354920006df73595300c6ec7358a30024dd73d8930406df631953222f755454710004ff7458a51004fd72d8d50006bd64d4c10005df7348410004fe764c550024fc768c410006f4429845001cfe74d8d51024fc7558b5007ddc734861001cfc74d8d500057f7558530006ef6294531006ec43588100067f6419510007cc7354920024ec7648520006de6418d2100cfd7318532026ec5058850004fd71d895004c7c7558d2004e7f7299410025fb734c120004fd75d8132176ee4258851005dd7398552004fd7654c10016dc63d4d21096ef3258d20006bc73d9110006ed628c410014fc76d4130006bd7159050026fa60182310067e419941004e7f549875334d7d7414650026ec4058a300a6df3158e2019df5719953100dec7254e211fcff7259532006de3258c100075d54d8d2104edc5458c50004fd73d8910016f4638c621006df63d81521067d52d9520007e7724c521006ef5458810004fe764c910006de70d8d21006f9601813200cfe7258251006ec7458850166ee3258a31086fa20d81210067d54586300067f3019510024fe7614630005ef7258d5100cfc7258753006bc7259050026f7305
  | 9 => 0xd6554410004ff7258c5120edf20d8d5201cfe745835204cfc76d493014dbe74d4621026ef72588500067d5458353167c4328c6210067d5498630026ee2058a101aeec32987520073f75d911004eef755885044edc50d8d52087cc324cb10056ef2158221005dd73146310067e53d9510026ef7258a10006ef5458a300267c2099410006df7359521006df635452101cfc745962039cfe768c5210267e7059410004ff73588100067e63195100067d54d95201d5be7419532006ed62146300067d54586201eeec31d89530067f6599510005f7714831000cfc72d81530067f54d9621004ff768c620004fd75d8520176ec6214531085ec724c71001cfe74d8951004fd76d4f10005ed7214621024ed72d8d20006ed4358810006bf7259050004ff7498650006ef7258d20007cd42d8d210067d54d8910004ef725953000cfc7158e21295f574947100febc64541101aeee62946300067f5458221006df63981521edef72595320057f754845004edd5458c500067d5458c50006ec6218553006dd631462000cff768c621007b76494510007f07054510006ef7158a30146cc63885210073c64d951000cfe76d89101ef6f75d8953004ff7458851004ff74d895115ebe644c450006fb6098132007e5728c621006dd634c8101b6df3058e5104efb70580510b7cc324c120006bf7359050006dc7158c10006ed7358850034ff764c71004e3c5159351026df1058e20006f57258450026bf2059050005bd74995100267c5059610004fd74d8f101beec3258b51004fd7459521026bc70590100267e5059630026bc50590500067c63d951000dec7254e20024fc705885001cfe74d96310b6ec21d8930166ef631893104ef45398450006fb7058910004ff7358a51014fe7558b5301cfc7458650136de6348410136ed3258a31004ff7654d10004ff764c950006dc6398152036dc3158c100067e3299410004fd74d9710004fd768855004ef55158351004fd7459510014fc7558b53066bc71d9110006de74d8d520067d6588410004fe769452004ef665545100067c6548110006ef62d4930096ef3158a3010cfe7619530004fe765452008cff7058d10004ff764c620166de42d8d2104cfe75d8d100067f5458d2104d7f7414650005df7359521004ff764855000dfa728c12004cfe75d8910255f57454510006de65d8d21006df6418d52026f52058450177cc324c85124fb4645451001cfe74d8532004fe76d4d200067d5418530005dd73885301feec20d8953146ee53d893100cfc7259610014fc7358351004fd74d8d51026f5509845000cee76d8931014fe7318552006ec62d85530067d72d951004e7e65947103bf75548c621004fd7654b100067c41d951000cfe7258d1004e7f5458b5019edf3059531025dc7054d30014fc7158a310267d5058450
  | 10 => 0x951000dec725412001cfe74582212757c7054451026df4058e20026f43058450016df618c53100eec62885300b7e8724c120006bf2159050014ff7654e5026ebc20d91101df9e7418d5219edc6358d51006bf3059351004ff745952000cfc72d8d5004e7c6554910005f47154e5100cfc72d8553004fd7694620016da634c22004ef55258450026df7358e1008cfd73d8f100077a40d9510004ff7258231006dd7158c500eeec62589500267f505865000cfe7258f50146ed71d8931006df2158c10004ff74d8953006dd63d4e211fedf3258f52194fd76d4621006f772984501ef6e53d89530067e43594102677410d9510006f9601812104f766154451004fd7458f52167ce3258a3104cff76d462004d7c754c85001cfc7458750004ff7158f500066f5458810004ff768875005ef63158630004fe7654910014ff764c310006be3259010417cc32d95320b6dd4258e20026ef1058a300067f5458a31006be32d9110026bc205905024ff2405451001cfc74d8953004fe71d81520267e2059410024ff7058c1004d7d76944500067c319941001cfc7458a31167d7638c5212767c101951004ef7515875200cfe729863000eee6254a10004fd76d4410004ff74d8d21006df65d8d210067d651952001cfe7458a50026ef405881004cfe76887501feef20d89530067e654c810026ee4058810004fc7158353004ff7358a10026f410584502e6fb764c22001cfe74986500067f7558910026ee70588500d6ef21588503a4ff7158d212ef5d544c530466ec50d8953096ee3158a30005ef7258d10006f94058221004fd7654d20025f87054950006df6354d2104f3d74d46510067d5458a30016de634c6200067d54d96314075d7518d5200cff7658a51014fd7158c1001cfc74582210bdbc7458530004fb764401004cfd71d8951096ec4358a30004fd75d8d20006ed7558a30004ff745822104edd5158c50146dc6358e21004ff74d8d102757d7614650005f77154e51004ff735865004f7561944500067f735941004edd535835304f6f62d4d52005fb7054a50004fc7158c50014dc7359521006bf7159050006ef629855320edf21d8d52024fc7654e10026ed2059620007f13144010004ff74987520a6dc4358e20006ed4258810026de2058c50006be705935100cfc7258c5120fcc32d4d20006ee5458a3001cfc74595310067d545971003ebd71590100b5ec7258530157e4324c6210dede4358c50006bf7559010014fe7358251026dc5058c10004ff74d9531146ef7258e21006dd4358e2000dee7214520005dd73d96210067f54595100067d5459410026df2058c101aef52198752004fd74d8552026751059410167cc3298532006ed7458850016f6638c521026ef1058810025f87054550166ef2058a31006bd64d441004efb50583530067
  | 11 => 0x6dd634c62001cfc7458d10014fe73d89500edf970995200067f6599710006f474584503e57f74544510067f65d47100067d74d951001cfe7458c500067f43d9510014fe76d453120ddf73595320f4fd765413004ef4765451004e7e6594621095ee734852004e7c6554510136de43d8d2104d7e758c750006bc3159010006f77158d100065d5458c5005edc32d8d10004ff7558f1020ede52d8d520067f70d95100067d54d8152014fc7358752026ef3058810004fd71d815304ef75398450004fd75d8e210063f65d9110024fd70588100067f54d9532026fb61c4110014fe76d8d20006ef425881001cfc7458c50004fd729875005efa3058231006de5258c10026de3058c50084ff7058910006fb6098121025fa708871000eee624c850006df6354d5000cfd75d8d52006bf644c9101feef21d895321fb874440100067d5498752024fe7018552006fb60981520067d5458b51006dd4358e51146ef43d8931014ff7654e51166cc628c5310067e4219510004fd74185530067f6514530036f63118530004ff7158c50006fb6098231007777554710024fc70588100ecfd76541201adec7254e51006ec62d8131004fd72d9631004fd70d953220eee3258b53006ed624c410004fd72d85533fd7d74d4651027f010481100257c70d4550004fc7654e21026ef5058850096ed4358a30004ff72597103f77541d465107cfe768c5100067f54d89530065f5458e20004ff7259630006ec75d893101cfc74583531eede63d4810016f4634c621006de7158e20006f7419845000cfe7259531005bd74d4531026f53098450006ed6248450024fd769471001cfe7458a3108cff768c410006ec6218131004ff7654d20004ff7498750006f741d85500076d54d893104e7f5458f50006f642584500267e305941002ef62118520014fe76d413000cfe72d9531014fc7359620086ec32d8b100267f2099410156ec42d89310067d54d8d21024fe76d4630014fc7358251014fe735865004cfd72d8d52004fe76d4d211b6df30d9531006ed75d8931166de21d8d21015de73d4a31006f96018153014fc7398650004df7359520024fc7654620006bf3259050006be73590102a77b548c1200adbe74d462001cfe7458f1013ebe6448410006ef3258221004ff74987530067d5458a50006dc54d8d21006dd71d8d5200cfc72595103f77641d4651004fd73d8550006fb70595103d7744154451027e9728c1200047f74594100067e735941000dee728c520024fd75d8d500c7eb218c120006dc74d8d21026de4058e20004fe71d8d2005cff7358d10004fd70d8552004ff705875343d7d74d4d52026f54098450096dc6358d2004d7c754c450006ef7358810026ed1058850006f976c4210026bc2059010005bf745855026fb771d911004ebe52590502767c301
  | 12 => 0xd705881004f3d74d455008dfb7058530004ff7258630004fd7459631026ee4058a302fefa30d8132006f472584500067c6558d10006ed4258a50024fe76d4e101cebc64d4510006be735905004e7e60946500073c65d9110174fe71d96210067c658851004cfe75d8e2120edd21d8d52005ed7298131014fe76d8d51026dd1058c1000cfc7298753014fc73d8152024fc7688410237755494710004ff7058e21216bc64d4d10026ee50588500067c6419510024fe70d8d2104eec5258850005df734863001cbc74589100067d6594410097eb328c1203a7cc32d8532004ff765493104ede5158c5004ef55358450006dc4158c50006df6418d2104e7e6554310004fe7654530006bc64d95100067f6554110024fc764c62044edf50d8d52006dc735891004e7f749941004d7f7154550026bf2059010026bf5059050005ed7298153014fc73d9710026bc5059010004fd764ca10024fe76d4a3000cfc764c52101cfc74d8930004fd75d893004e7e65196210bebc644c110024fc7059621004ef7258f10024fd73d853004e7c6554d10166de20d8d21006ef70d8931004fd70d8d21006ee74d8953004fd7458a310067d54d8d50126fa30d8153005bf7458d100066f5458a30026ec7058810245f7749451026ebc50d911004ef6759845001cfe7458a10006bf64d8910006bd644c810004fd76d4930004fd768c5200073c75d91102d6fa20d813204e7f6054550016de634c310026bd1059050006bf20d911000eee62548101eeec73d895301cfc7459630006dd4358c51004ff7458e2004f3e649445000cfc7258c100067d75d8e21026ef4058a300267f7559630014ff764c110026f7105941000cfe7258c51036df3258c10026df7058e200067f5418550007cf734852004e7f545875220edf32d8d523af75544c621006bd6448450006ed4258a30015dc735413017edf3058c510067d5458b10006ee7458850026ed2058620005ed7088521017d7714c530005df7354910006bc31d911008f5e53d4f10416ef6518953004fd764845000eee62887100c7ea528c120024fd7688710005f671d4110004fc768853005ddc735491004e7d729941001cfc7458051006f4739845008edc32d8f10014fe7358221005ef724c55004ef8505805108ef6319863000dee72146210067c7359410004ff7458351006df639812120edc3258b530067c72594101acfd72d95210b7da324c220004ff735952104e7e76d4d52004ff7654e10147ce43d89310077765545102cdef7454920026f610984500067f54d953001cfc7458d200067f2199410006ed641895304ef45458450005bd74d452004f5c5354d511feee52d89530cdbe74d46300067c42d951004cfc75586200067f54d8131024fc76d4810004ff7159510005f4714c310014fc73d895100cfc7298750
  | 13 => 0x45211feee6254c1025fb4649451040fcf3018953006be75590100067d5459521014fe75987530067f41d951000df8724c120014fe735962101cfc7458b5101cfe7458d2100cfe7258e5104ef47598450006ed4258b10006ef325885004cfc7558d21007d7634c5211adee721825100d7e72d4d52016de6354e510d6ec2158850006bc3059351166ec32d8e210067d6594710016de6354e500057f75486501df5c63d4d5220fcc32d4e21004ff7258353014fc73595102bdef744852004d7f7654750004fd72d953101cfe74d8530024fe76d45100067e53d9520024fe769462010ddc7354a5004ebd525935120eef2058b5304ef6515835104ef6659451001cfe7458231026f61098650006df635855239edf6118d21004fd764ca50146dc3158e21005bd74d4410026ef3058a300067f5418552004fd7654d1004eef5258b50005fb704c6102677771d95100067f5458a51006ef41d89314367d64d4d52006ed72d9631004ff764c550007d5638c6210067c53d951001cfc7458a30024fe70d8d10156dd3258e21466ef50d8953016f6634c52104e7c73195101dded7299532024fc7058d2104e3e75593510067d54d8b100067f5458f10005ef7254d21026dd2058e20007f251c4110026f67198630005dd73d8a5104ef45198752025f8704c61000cfd75588500057d758c5500b5de724c53004eef525885020edc52d8d52004fd7458c5000cee72d9631007e9218c12004e7d7219510025fa7094410004ff7688650006f840d8151004fd73986200057c7558d2007edc3258e10006f6419845005edf31d8d100267e50596101bcff7159521026f670584500067e5359410006dd638c7100257e70547500067f3299410024fc7058f51096ed3158a30005ef7254d100067d54d8930006bf21d9110006dc6358552006bf2159010024fd7614710004fc715962008edf31d8f10005dd73981210067f54d8532065bc745951004f7b6054550026df5058c1004cff7659532006dd43d81310b7cc3288530006dc7358b101f6be64d4810146ec53d893100cfc72d8131006dd6348410005bd741953201cfe7458e2104cfe768c75000eec62549500067e75d8e21005f97094710004fd72d81511aeef2058a51005ef7258f100b6df4258e20006bf75d911004ebc525905000d7e7254f52026fb628c12004edf7558c500076f5418953006f67298450024fc7018520014fe7358a51006dc75d8d21155ee76d8931004ff768c75001cfe745961000cfe72185530067c415941004eec7558850147e731d8931014fe7398450024fc76d4e10196ee62544100b6ee62d8930025f87054610025fa708c4100067f65945200057f755813200cfc7258d1004ef7519845004cff7614630006f5618845000cfc7258e10007e461485201ffad74189530075d5354930026e
  | 14 => 0x2767e3019510006ed42d8930006ef7259530006df639452107edf3158e1001cfc7458b5025ff2409451004cfd73d895304d7c754c650026f63058450036f53118530004ff735845005edc32582311967d5259621006f56118520004fd76d4a10136de53d8d2104ebd51593511aeee5258a51024fe769455001cfe74d951019dde7318151006dd4358f1001cfe7458c5101cfe7459532026ec305881000cfe7258353004fc768c5200067f654c110126df3058f50004fd7458b53006ef625855301cfc7458e21026dc1058e2020edf52d8d52006de75d8d210067f54d855001cfe7458d1000def71485200067d5459531006f573584500067d5458e51006ed6254810167ce42d8d21006f6435845014ebe6488450004ff7458f520067f5459530004fc764c550006bf32590100067d5458051025ed72d8d20004ff7458750006f77358450004fc765453000eec62485100077b7544010026de5058c100bdbe741953004eec5258b5004edc7558c50006bc215905000777655471004cfc761463105ef531586300dddc7348450014fe73589100067e654841027f7b54c42100267f7099410004fc7158a300057d75d8a31006bf32d9110006f6329845004ebe755935101cfc7458450016dc638c5200067d40d9510006dc41d8d21096dc53d8d2019ede6354620024fe70d9521146ed30d8931004fd74d9520076ee42d8520156ee62d8931285fb74c421004cfd715941020f5f63d4d520067c755891004ede535835304ebf5259050406df6218d5200dec724c5200067f545952001cfc74588511ae7f52d952100cfe72d8f101feee75d8953006df7458e20026be50590500067e4319510005bd74182310047d75d8e2104e7c74994100047e76d4550006dc74d8d5204d7f74d4d520057c7558530006df6358121005f671d4b1004e7f6254d52026ec105881020ece3258b5305cfd70d8d101ef6c53d8953026f62058450006be5259010004df735952100cfe72185500067f54d8f100067f54d8d10006de3258e50004fd71d8d50004fd76d4520004ff764ca50016f6638c62104e7d7614650024ff72d8d20025ee705492004ef55458450026de7058c100b6ec3258d2004f7a601465000cfe76d895104e7f549845000cff73d9532006be52d9110004fd74d9621004fd74d8550006ed40d893104e7e7299410004ff7654a3004f7461547502767e2019510026f61058650006dd54d8d21006bd7559010006bd72590500267d1099410014fc73d8151026dc7058c5000eee6288410006f54198450005f671d4d101efcc53d8953006dc5258c10015de731453004e7f5458b53166ec5258a31026ef7258810015de73d4530004fe764cb1019e7f5359631006ec621815304e7c65d4521004fd7654e21006ec64d8953006ef624811000cfc7258f5104cff765
  | 15 => 0xc74d8d21004fd7654630006df63d4d20005ed72d452001cfc74d853204cff7659631006dc71d8d52006f671d8f10024fe7058a3001cfc745971005cfd764c110004ff7058b51014fc755835304e7e655463000eec6254931004ff7158b5300cfc7258450165f7734c521006f47298450006ec5458810005bd74d46210067c4259410006f5329845000675545845000cfe72d85300067d7259410006bd6448410026bf5059010026df7358e2026fb610d9110004fd76d4a3000cfe72d8d50006df4358c5028df57454710004fe7654e210057e75d8a310067e7159410006bc75d9110006bf644851001cfc745875300cff76946210d6ec325885004e7e6519531006bf64d411000eef60549200076f54189313c75f548c5310063f75d91101eeec75d8953007cc628c531146ee6388521006ed6254410024fc7058e50025fa70d45101beef20d8552006dc70d8d52004fd7458b10004fd73d95200b6de4258e20006f6415865000def755492004ef66554710004fd76d4e20025f87048610005bd741822101cfe7458b51006ef62d4531004ff764cb5002fcc324c810026bd1059010004fd709875300df6724c62120fcc3299532004fd72d9710016f8634c12008ef5319863042d7f7454d5204c7e75d8e21004fd7648630166ec2158a31006bc705935102dec724c4100b6cc3258d200067f75595214567d6454f5200cfc71d8910006dc2158c1000eee62484500077551543100b5f9738c120014fc764c310146ef53d893104efb505805104ebd535935100cfc729863003ebc715901033d7d74d45500067f65545310067f5458e10004fd7458a302667e10d9510026ec40588501b6de4358e51006ef3258a510067d5458d2004cfc7558231007f221440100063c64d95100065d54d8d21066bd10d9110167cc32d4a31006dd63d4810024fe764ca10014fc7358650006ef641893104e7d7399410006ed62d4a31025f47094710004ff7458a30004fd76d4e21026dc3058e2004d7c754ca5002eee4258810136de7618d21004fd76146301acfe76195210067f65d4d100067e6219510014fd7558c50006f641986502767f641465000cfe725835104cfc76d4f10006df634c1200067e6154750016de6354e20006fb40d81510b6dd5258e202eedf644c53004cff76541303075d5454d30026771059410006ee641895300cfe76d452104f777154750016de638c410004fc764c950004ff735885104edc5358f510067f5459630006ef4258a30006fa405825104f74515455000cfc72d9631004ff74d85520067d651953101cfe7458650004ff725941004cfe75d8532004fc768c55000cfc72d8f1000eee624865017ede6314410026f420984500263f5059050024fe70596200067f54d8121014fe73d951000cfc764c120004ff74d95323dd7f7494551
  | 16 => 0x951004ef65358450006df634c51016ebe648c41000cfd76146210067f755953004ebe75590500067c5359410024fe70588100eefa2058352026f4105863000cfe7258f10004ff74185320067f5158251014fc7358b10006ee74d893100cfe7298650006f54198650004fd74d89531ffae741895339edc3218532196ec62545311dddc7358552026fa6018221004ff74595100067f545823104cfc75588102667c50d9710007746154550004fd71d9532024fd7318530006ed6288410006dd6354e2001cfe749862004eec51588500047f76544510063d7559010014fe76d8d52197cc324c95104cfe76d95320067e41d95100077865c4110006f67498450005f47154110004fe71d95300067c411951001cfc745962104cfe75d8d200067c2199410026f450984501b67d53d953104cfe76d95310063e75590100067d54d95310267e7099410006dd4358e10006f44158450004ff7059531006ec7458a30026f7209845001cfe74d8151006dc40d8d52016df604c530014fe735835204edc5358c50026f41058620006ef7258f1000cec7258f10125dc7348750026ec3058a30006ef7258c51006df735952004e7e65d4810006ef315885000777659451004e7c65945101c4ff7159531004fd71d89304167d52d95320067f5458650065bc7458d10006bc52d9110004fe7614520004ff7359410004fd74d9532004fd7458630006ed6254a30007cf638852104cfc76d4520014fc73d8550014fc7358a50006ee41d893120edc21d8d522d4ff7058d20167cc32d8a310067d65d462004f5f7354d52006ed72d8e21004ff7459532026dd5058c50005dd73d453001cfc74d8553006bc3259050025f47054510007cf7254d300057f7558d100067c6558910006ed5358810014fc7358051006f54158650006bc65d9110004ef7258d101feec21d8953006dc5458e20004ff74d8151056ec325822101cfc741853204eee545885004ef77558450005df7354a5004eef7258b5004edf5358f510067d545962101cfc7458e20006f43198450026ec1058a30006dd63546200b7d8324c120124ff7059530004fd74587521fdee7298553166cc32d8e21006dc4258c500067f75597100067f54d8552005ef724c61004d7f76544511d6bc644c91004edf7358c51167d4328c5210067d611465004e7c7419510004ff7458752004ff7158f52024fe7059410014fe7358752005df735952004e7f6454750004fc7654d100975e53d4d200f6de53d8d5005edf315823104eee7558850004ff76546300edec7254d50005fb70486100067f43594103d777415445100d7c72d4d520067d54d8e2120cff7359532014fe735835139cfe71d8e2104cfe75d8b1004ebd7559351026f671986200067f65d451005ddc73485100067d549875004eef7258851147d6434c62101cf
  | 17 => 0xdf4728c521005ed7218251076f621d8520004fd765462000cec7259530006ee4358810006bc64d891004e7c6594520026ee2058810004fd7018552006bc5259010004ff7654810004ff7418520006ec7558810006bc21d91101dedf31d8d52006bd64d4810006df43d8d21195f57199521006dc7458e20006de54d8d5200cff7648110006dd74d8d52004ff7654d21005fb7054d50004ff7358b51006ec62581311c4ff7654631156ee32d893105df97098530006dc64d8d52004fd74d95211feec6258953055ec7258d100067d70d9510006ec40d8953006dc6418d2104e7e651951005edf30d8d10006be7359351006bc745951009dbc745852004e7f5458f52167e7208c521004fd75d8b1000cfc7258630006bc7559010166dd71d8d21024fe7654e200067c745941045d7d7454f521feee73d89533ee7d6494551006ec5458a30004fe7654d20005ef724c120004ff74588502677a7094650004fd74d8b101aeee62944104367f64d4d52024fc7654d500067f5498650006f9405823104e7e7199410005df73589101eeef6299532016f5768c62104e7e651971004e7c65d4710014fc7359610004fd7498630006bf7059351004fd74d815304eec5258b530375e53d4c1010ddc7348650017d6718c5310c7e8328c120024fe76548100067d41d9510004ff7458650025fb71440101beee62d46301aeef20d952104d7c75484502667e6094450006ed625463004ef67558450005f571d4910006f72198450006dc6418d52004df735885101cfe74d8550026df30596300c7cc3298132007cd43189310067c6319510026be5059010024fe7598750025fb7644010255f77454510186be641441000cfe76d4120166dc42d8d21026f4109862001cfc74d8910006bf72d9110004fd70d9531006ec4358850006df634c710024fe7058e2004e7e6514631004ff74d8d503f67d64d4651014fe7358b50006dd7458c10085ec7258f1004ebf75590501bcff7654621007e87054920024fc7058e512d6dc32d8132006ed628c450004fd7654e10036dc3258c10004ef7258c51006ed6254a50004ff7458910026dc4058c10067b471d9110006de32d8d51026ef7258a30006be73d9110006ed41d893104d7e719455100cfc7258353005bd74d4620014fe73987520c6ee4258a30004fd7398750004ff7058a3101cfc74d8153006dd6518d210b6de2158e200067c53d9520135de73995210067f655412004eef5458850014fe7398650004ff74d9521004fd764cb5026ebe50d91103b7e43118931025fa7088410156df3258e21006dd70d8d52005ef7254e50006ed70d89530067d6554310026dd30586300067d5498753006ed545881008edf3058f100267d705941017cfe71d963114dbe741822101cfc7459520006ef74d893104cfc7558e200067d545
  | 18 => 0x8724c220054fd7648110006ee54d8953004fd768c650007db704c53004cfc71d9510006df5458c1020eec2158b53466ec51d89530057d74d95100075f5418d21005f970944100267d3059410005df7354b10026ee30588103b7cf30189310067f5418532004fe764c520006df7558c1004eef5258b5304cfc7614621016f6634c621005f671d431000df6728c62104cfc76d4b10026dd4058c500f5dc7358950006de5458c10015dc7354531024fe768c450027796544010006dc65d8d21026de7058e2027774101951004e7e6554620155f5738c521194ff7259521006ed5458a300067f7559631006f73298450006ec6518931004ff74d8e2139fcc321853200cff7648610006ef62981532d7cc32d8132004ff7258f50006dd6314410006dc7558e20014fe7358b51154ff7258d210076f5354920006ed43588501ef6f3254f52004ff71595321ce3d75593510067f54d8d52007d8704c5300063c65d9110006ec70d89530057f754c951014fe73d85201dedc43d8d521eeef31d89533567d64946500267d4059410006bd73d9110016de634c4100077a4019510004ff74d855300eef61885213367f64d45502767f6514610006dd634c61001cfe745885108ddc7354b10026fa6018132006de70d8d52006ed7158a3004cfc76d4d21004fc7648530016de634c85117ede4358c510067c329941001cfc7458f510067d5458221006ed6288630026ef10588500267c4099410006ed7458a300b7eb214c120006f66154620014ff72d9532024fc764865001cfe741852004cfc7614520004bf7458d102667c20d951044edf54d8d52136dc53d8d21006df7258c10026ee705881004cfe75d893139fcf2018d21026de2058e20097db314c1200063c75d91100a6de4358e2019ddc73589510067d5458850006df7358f10004fd7398450146ef71d8931004fd76d493104e7c65d4130006f5615462000cfe72d8d51036df7158c100067f5458d100067d5458b50006bc2159010075ec7254e10006f6769451029f7b544c120005bd74d4630006df4158c50004ff74d8550004fe76d4520005df7358152006dc639855201cfc74d8152004fd7694530004fd739875201cfc74d895101cfe74d8d100067f54d952120eef6318953014fc735962141e7d53d9532004ff74d8152005ed754852004eef7258b51014fc7359410096ed5358a30006ef7458a3039df6768c52104e7e6554610024fc76d4a1004f777154451015dc7354a31024fc70d8d100067d5458d21006f5615463000cfe7258750106ee4258a50014de76d8d52006ec7158a3000cfc7259410026fa60181520067f4159410006bf64d4910024fe76d481044edc51d8d52004fe7614530004fd70d8d51005df73581210067e32d9510005ef7258153006ef64d895304ef45198750004ff764cb10
  | 19 => 0xc520004fd74d8532004fd74595300b6ee42d893029fd9434c12004cff765431004cff76541101475e53d4e21006f66148450006de3258f5100cfe7298753005f771541101adee72d8e51014fc7318552006f66154630004fd74d9531006bd65d9110004fd7654a10004ff70596313267d645455001cfc741855304e7e65144100073c6419510004fd74d8132007746554510014fd768c41000cfc7258e502657e70d4651027f361c4110096dc31d8d20065be76d91100067f541855304e6f5458850006bc3259010097eb324c1200067e52596310067d54d8953005ef7254f100267f505845001cbc74586500067f4319510005ef724c450006bc32d9110004fd76d4910026f8634c220006f970d8b10026bf10590501b6de63946200c6dd32d8d20026ee4058850004ff7558d10096ee4358a3004edf5158c50004fd76d4d10006dd4358d1001cfe74d9532004fd7498450004fd74d8910014fc73d95300067d6594621006f442584501cebc7159351006f7435845000dec725452126ebe70d9110004ff74583530077551d4110014fe76d8d100066d54588100067f31994100bdbe74d453001cfc7458e10006dd75d8d21016de634c850014fe76d8d21026ef405885004e3e755905005cfd768c610026df1058c10014fc7358352006df63985521aeec2158a51006ee70d8953006df41d8d2101cfc7498750004ff764ca1000cf5768c621014fd76146310067d5458a31086ee4258b1004cfe75d8d211eeef3258f5200cfe72595301eeee31d8953024fe70d8e21004ff7158352004fd72d951004ef77158750006dd5458e200267e10594100067d65d4c100b7ea524c120026f570984500067f54d813204ebe5159351006bd7359010005df7354a3104edf7358f500067c4219510226fa614401004cff761462011dfb7059520004ff74d853208cff764c410026de1058c5004ef46554710006ed4258850146ed32d89310067d54d962101cbc74595100067c31d9510014dc7358b10146ec31d893101cfc7459610466ef54d89530175f7554d30004fd72987530067f5458c10006fb7059520024fe7018532026ec7058850026de3058e200067d651962100dec724c621295f77494710176f521185520067f654c910005dd73d4a31026f470984500067c6154550024fc70d8910006df70d8d52036dc4358c1001cfe74d9530026f4109863004edf5358c501ecef7259532014fe735941039dde76d8d21165ee721823105ede63d8d1004cff76d4c100b5dc724c53004ef45198753025dc7654d3000675619445000dec724c6200067d54d953204ef6529845001cfc7458e50006ee64d8931407cc321953201cfc741855000cfe72d8131006dd638c410026ee7058a30086f6219862000cfc7258750006dd4358f52056f6215862001cfe74d895000df
  | 20 => 0x65f54d8d52006ed6248310004fd7018553006bf3159010024fe70d9532004fe7694530006dc4158e20004ff7458c10024fd72d8520005dd7318151006df40d8d52006de40d8d52004fc764ca5100df4764c52126774509451000cfc72d85500067f74d95100067e4159410004fc765452001cfe7458e50005df7348610026ef30588501aeee62d8a5101cfc7458251006dc7458c10025f8704c510006dc7358851006ee5358810004ff7158d201eeed43d89532feef32d81320075c6554d30004fd7418532006df63d4d211b5de7318251006ed74d8931066bd71d9110006ec415881001cfe74d8552006de64d8d21154fd73d8e2120f5e52d8d520057d7419510156ef21d8931006df7358e210067f21d9510015de73885300267f1099410024fc7058c5001cfe7458f510067f65995300b7cc3258d20014fc7654d51005bd741953001cfc74d8950006bc6419510004ff7688630196ec6258951026f750984501ef5f3054f5200777615455004eec655492000cfe7259710004fd75d893120ecf6318953006dd63946200067d5458e20004fd75d8f10006ed6288710006de4158c50026df7358c10006ed624c450026fb624c120027da634c2200267c50596201ff6c7254d520247e7598750006ec7258c5120edd42d8d52004fd76885302667e50d971001cfc74d8f10024fc7654810006dd4358c1004ef45358450026ee2058a50006ec64d893104e7c73994100076d54189530067f5459610026f771586200067f54d89310067d5418550007787054550004ff7258e1004e3c51590503b6ef32185321aeec3258a51007cf724c530005dd708c5310067c4399410006dd7558c1000dee72d4d20025fa701471004cfc7558a3012ebc64d4110004ff7158850014fe73588100167c6354f52017db604c53015ebe644c410007746554710006df6318152166df71d8d213cddf748c531006df74d8d52004fd73d895101cfe74d8d5004e7e7319510025f87054510006f561185520067e658c41013ebc644851006dbe74d4610005df734853004e7c6554110004fd74d89512fdfb70589304075e5218d5200dee728c621006ee70d89310067e5359621004ff7158e50026ee2058a30026f55058450004fe76d4e2100dea728c1200067d5458f500b5cc7254d30005f671d4f10006ed6294410005ef725813132d7d74545500067f7558d202a779548c12004e7d7119510004ff7648630024fe70d963100cfc7259531056ee62d891004ef66594710004ff7558d203d67d6454451004ff7459620004fd769452001cfc74d813104ef761945511ddde73981520067f20d95100065d5458e20004fd74d8151006dd40d8d21004fd74d96310067d65d44102b76f54485202667e70d951008ddc7358b10004fc7654d200067f65d891000d7c7254f52004fe768
  | 21 => 0x4724c521004ff7159630005df7354931156ec20d89310053d74d4651006f671d9631004fd7654810006ed6294630016dc638c521004ff7558810006fb6098151025ec7654920004fc7158850006de321853019ede63d8d510ecff72595200067d651971004e7d74195100066f54d8953026dc3058e10004fd745805108edc6358f101eeec43d8953014fc764c110014fe73d8151004fd72d8d10004ff745953101cfe74d8520045be7499710004ff749845004cfd70d89501b5f6711963104d7e7588550196ef21d8951146ec73d89310067f545891001cfe74d8f100067e52d9510026bf30590500067f41195100067e72d95100067d439941000cfc72582511bdf77159521004fe76d4d1017edc6314521006ee40d8953026ec2058a1004cff76d4910004ff7654b10004fd7458a10004ff72595310067d5458c511dede6354810005bf7458910015de739453001cfc7458b10006f74158450166ec6258a310067d651952104e7c655412001cfe74d9710006bd648c410004ff71583531eecf3258f52004ff7358b10006de32583530065f5458c10014fd71d893101cfc749865007cff7158d10004fd71d89530067f54d8951004fd7459610014fd72d81320057d758c750006bd644c450015dc7354931006bf648c510006ee735881008ede43d8131016dc634c7101aeec6294531005f97014710005df7354130066bd70d9110006df63d4521026f65098450004fd764c450024fc7059610006ef628853001cfc749845004ef46594710006f761985530267f7559620004fd7459520004fd72d8153007eb724c1200066d5458a3001cfe7459520007d9314c12013dbe749952131d7d74944501eedf3058f5200cfc7218550026df4058c10016de63d4e210067d6554630016df6054d301acfe761452100cfc7258e51004fc7159520156ee7618931007e76148520006f771589100a6de5358e20006ef42588500b7d8324c2200067d5458752005bf74595102a7e9428c120166ee628c450007d53188530006df7458c50007d7734c521024fc7058e21005fb704c510014fd70d8930167d6328c621014fe73d9621004fd764c650025f671c41100067f54d8153006ef725891004ef4529845001cfe7458f5200cfc7258351004ff7358910006f5611855004cfe76d9530006bd641441000dee72d8d200067d54d81310a75e53d4e2040eef6219532004ff735862004cff76d4a31136de6348450006ec7258f102657d7094450004ff7418550006ed4258a31004fd7318550157e7204c521024fc7058e1019cfd76d4631006dd4258c10005df73585523a5f77158d2104e7f645445102cfc7158810024fc7058a31026f67198650014fc73d8121015de7354530007e9214c120004fc7158e200067d54d9530026ee3058a30004ff7058d21006bf31d9110
  | 22 => 0xc5210067c74d9510006ec74d8953025f4705471004e7f5458351006ec6298553005ef724c750014fc731855004ef75358450004fd70d9621006ef42d89530067d5458b53006dd43d8d5221ef96444010026f7715845020f5c52d8d52025f87054d50097d8634c12001cfe7458e20005bd741815101cfe74d855300dee7254520006f77398450014fe7359521026bd2059050006f57298450005ed72d9631387d5434c521026f510596100047f7558d20014fc7654531006ef7558810006f77159521025de704c530014fc73588500057e7619510006be72d9110147e7724c6214075c5218d523167d6494450024fc764ca50004fd7614520006ec4158a30196ee52d8951006dc7158e20024fe7654e10026f530584501eeed31d8953006fb6098131006de3258c50004ed72d9631004ff7458b1023f7b54c411004cfe75d81321c6df30d8553026df7058c100267f409941019ede6354410004ff74d81321adf671196210067d5458f10024fc765451001cfe7459531024fd73d9530006df4258c100267e4099410176ee3258851005bd749953104e7f71195101f6bc64d49100067d5459630006ec715881001cfe7458c1000cfd768841001cfc7458e51005bd74997100067d5458a510c6df32d8d20025f87054a500057c7558d10255f5759451004f7661d4651005ef724c51023ff241c4110006f561946200267c2059410004ff74d9520007787544010026dc7058c1000cfe7218530006bf6414510026de4058c10006f56194630004ff7654a1001cfe74d89300067c654c110006dd634c41004cff76d4e20026df7358c50004fd75d8d10006dd6354e510067d54d853204cfd721855204ef75298450014de76d8d210a7db314c22008ddc7348710026dc2058c50006de41d8d21006ed7158850006df6318552005bf7458131006dc6318552006bf64c411001cfc7458b5300cfd71d8d210257e70d45500047f7558d100067d4299410027d9634c220004ff7458b53026f67198450024fe70d855200cfd7694621004fc7694530004fe71d8132004ff74d81530067d4019510025f87054650006df7358d1001cfc7458a51004fd74d8930004ff705962123ff141c4110004fd74d9510006df75d8d21024fc764c850004fd75d8d21005bd7499621026fa6018131026f54058450005ed72d412000cfc7654d5204d7c7548650005bf745812104cfc76d4931004ff76944100067c525963104cfc7648750006ed72d9621006f66194620004fd70d85320067e3259410004fd76d4d20006f761985320067d4159410136dc6358d21005bd74996310f67d5359630004fe7654b100067f32d9510065be749951020edf42d8d5239fd72118d21156ee52d89310067d5158051004fd7458620004ff7058a51006ef40d8953026bf1059010004fd74d8530157e
  | 23 => 0x1d6be644cb513b6f7764c621014de73d9621004ff7458753024fc7059531026be7059050006df73595310267f309941001cfe745835126ebc70d9110006ee7158a3039fcc2118d21006df4358e20004fe71d895000cfc7258f5004edf7358f52004ff7654e20004df7358b10004fd7458d2104eee6554920026ec30588500067f4299410006dd634c85004ef75158450156ec52d89310067f5418520006ef6298131004ff7694630006de74d8d21026dc5058c50004fd7458d201ff6c3254f523776f548852104cff76d4a300067c5359621006f43298450004ff7458a3104eec7654920167cc328c520026dd2058c10006ef70d8953006ed624c851005f47154310004ff7158e200067f5458a10026df2058c50146de63884100b6dc4258e20004ff7558e2100cec7258d10096de63d8d20006bc62d9110004ff715953004e7c65d4510026f440984500067e654c41004e7c65145300067d54595300067d54d8550166dc72d8d21006dd41d8d21016dc6354d51027ea624401004cfc76d4d20004df73589100167e6354f5200cfe76d8930005fb70485100067d5418552006df6358152024ec7654920006ec7558a30024fe7018553006ed42d89530076f6554920024fe70596301afcc324ca510067f5458e2102675505845004e7e65d4310004ff745962104e7f60d455004cfe76d9521006ef4358810004ff7654e210067d54d81211e6be645481000776659471000fe771485200067e761951004ebc535935127f7954c421004e7f7219510006dd6354e10136de63d8d21006de7158c1004cfc7558c102677610d9510016f8764c1200067c3159410006fa405805100d7e7254d520067f65d411004efb7058351026ec105885004cfe75d8530006dd638c62104cff76d4a100077970946502df7b544c220004ff74d971001cfc74d8b10016de6354c10024fe70d96211b6f5319875340f6e5318953004fc7648550004fd76d4a312667f65181510067d654c8100057d7588550006df7358b10024fd70594100067d545952000df4724c6210eeee62d895001cfc7458d210067d54d8d10004ff764c52004ef4515875220edd72d8d52004ff7058f51006dd4158c5004ebd5059351006ed755881004f6d6294450014fe73d95300067f6548510006ef74d895320edd20d8d5220edd75d8d5201cbc7458d1001cfe745962102eec425881008ede4358f1004ef46554510004ff73587520063c6419510006ef32d89512767e1019510025f87048510004fd74d85200067d5498450005dd754c5300057d75d8e21004ff74d8530004fd7648650225fb74c411004e7c65d4d100dedc3158c5001cfe7458e510b7ce32d8930024fc7058630026f61058450025fa709455004cfd71d8d510067d54d8f101eeef30d895300cfd73d9532007775194631005ef724
  | 24 => 0xd751823120dde7618d52006ed42d8121004ff7158b5004ef5515805100dec7258e21004ff7058f5207ede4358e10006ed64d8931006ef62d4931147cc31d89310077551145100b7e8324c120076ee5258a10006ee65d8931004ff764ca5100cff76146210047d74d9510027f0104c110004fd74588101feec3258f52004fe71d8d50136de71d8d210067f2159410004fd749875219fd43154531006bf644c51000c7c7654d52014fe7359610006de32d8d50025ec7054920006f73198450006ef75d89310a6dc5358e2000cff7658b10004ff7458231024fe768c65004e7f62d4d52026bc305905004cff76546100067e64d95100f6de63d8d50006ec7259530006bd7359050005df734855004ef6549845001cfe7458e10006be715901004eed5158850004ff7458f10004fd74595310057f75589102667c70d9510004ff74185523c75d548c53104ebd5259050025fa7014520004fd70185321ae7d52d9521004fc715953204ebc5159050026df7358e50004fd7458e100067f54d8950006de7458e20005df7354810006bf70d9110176ef205885100cfe72586301fd7d73d4d52006bf3159050006bf73d9110005df7358b10006ec6418953006dc63d85522dfd9434c220006ed4258b53026bf70590500067e4119510004ff7688450006f4219845004e7e6519631006df2158c50016fa638c120026dd5058e200047d76944501a6be6454410004ff764c951006dc7258c10006f77458450006bf7259351006f6415845000dee72d4e2104e7f5458352006f7715951004f3d6494450006bd648c450005f970d4610004fd76d46300077465945100eeef20d8950024fc764c51011efa20d8152004fd7458e50005ef72545210067c73d951039ef521185320076d5418931006f6619463000eee62486300067f54d8530006ec535881010e7d53d95300067d5458e1000cfc7258650004fe76d4f10004fd7458f500057e75d8e21125fb7059530006bc6459510026bc1059050035dc7354810005ef724c65000cfe7258753004fe7654930006f5611853001cfe7458a51004fd7298650014ff7658f10014fc73d85520d6ee4258850004fe76945100067f73d9510004ff7358251006ed65d893119cfd7699631014fe735952020eee62d4c10014fc7359710004fd71d95300067c52d9510005dd7394530396f6768c521014fe76d8d5028df77454710024fe7654c100267c5059410076ef2158a1000cfc72d953104e7d7319510024dc764c53004efb7058353006de7558e200267f2059410006dc63581520067f765445101cfc7459410005ef7254d20026ed505881004ef7515875302eef21185200067f6594530005f571d4b10026bf705901000cff7654a51005ed728c520096ee5358a302f5dd744c530006de73d9621025f67054510006f77158d21
  | 25 => 0x8c5024ff1405451004cfc76d453000df5768c62116ebc648c5101eeec30d8953005df735495104e7e65195322d6ec32d8132006ef321852035d7d7494650005bd74d4610006f632584501eecf6218d52026ba1059010084ff76484100057f7558131137d7304c521007e9528c12004cfc7558a3104ebf53593510067f54d9710005ef7254d5204cfc76d4910024fe764c810014fc7398750014fe7358850015de73d89302bded7448520004fd7458e51024fe701852004e7f5458753026de3058e10004fe7654f100ee7f5259620005f97014520006f67358450006ef7259521004ff75586200067f6554521004ff7654530146ef3258e21055ec7254d100067e321951004ebd5159050006bf745951001cbe76d9110005ef7258d500067d54582311ff6d751895304cfc7558e10005df754c53000cfe72987500b6de32d89301dedf30d8d52024fc7058e20004fd7694630016de63d4e20026dc3058c10005ef7254c101eeef73d89530067d745941020edf72d8d5219ddc735495119cff7359531014fc75d8d502adfa768c120006dd43d8530004fd7654f10186bc6414510006bf64d8d102657d7094650166df20d8d21024fe76d8132014fc7358810006dd635481039eec321853200dee7294520156ee624c450024fd7058c10006ef7258d1004eee5258352006ef41588100077541d9510096ef4358a3004cfe75d8f1014ebe6488410026fb6444010027f371440100067d549865000cfc72d9530005f970887100067d6554610006f772584500067f5458e50147d6638c621006f5415845026776509451004ef75498450004ff7259510004fd7418550006ed70d8931004fd7654910206be6454c1010edf3158e5004eed535885000cfe72d8d1000cfc7648310016dc634c51024f7754545100057f7558121005bd74d4530006df64d8d2104e7f545845004e7f545885100cfe7258051016dc634c521026bf30590100edec724c55001cfc74d9531024fe70986200077641d9510024fc7058a100067d4119510024f57694710006bc72d9110004fc7654930006bd644c4100067f65d49100efcc324c950006bc7259351006bf30d9110006dd4358e21024fe70d8951005f7765471000eec6248110026dc1058c10166dd32d8d21004fd75d81210067f659952104e7f7019510004ff7558e201beee62d441004edc5358c51006dd6418d21014fc73d9521017db6054d30006be75d9110014fe73580510267e505962000cfe764c52104f7b60d455000cfc72d81510c6ec4258a30024fc76d45101dedc30d8d52004fd764c81004e7c5158450014fd72d8532004fd759862000f6f7554920405de76d8d52167cc32d8e21006bc74589103b7ce431893104d7f7654f5204eec5458850006f671d9621025fa71c41100267d2099410004ff7558e100057
  | 26 => 0x26df5058c5009dbe74195200267d1059410026ee20588501cebf7159351146df3058e21006dd74d8d21024fe7614620024fc76d4c101ff6f2054d52006be63d91101feee62d895305ddc7358910006ec40d8931245f6711451004ebd75590500267c30994100053d74d455039fd42118d21004fe76d4910005ed7294520015df714c5300c4ff7358d20006df7558e20024fe709875340f6c531895300fe76188521006bd6488450004fd72d8f10004fe71d8d52006ec72595310047d7419510006ec735881004e7e6554810006ef5358810024fe76d4c10014fc7358a10016de638c710014fc73984503f67f64d4651014fe7359620026dd4058e20006dc5458c1004ef67198752006f574584500067d651463100dee72d4521005dd7314530014fe73d9710016de638c450006dd6354410006dc63d8121006ed62884500067d5458f52006dd4358e50156ef20d8931026dd7058e20026dd1058c50006f56118553006bd7259351004ff7159520006bc745865004f767194450006df6354d52006ed745881004cfe75d81310067d5459610024fe7694630004fd7459621024fd75d8950004ff7694620046bc64c41100057c755893000cfe729845000cfe725865040fcc531895301cfe74d952004ebf5159351025de7054d30005f7715431004d7e7588750014fe768c6211b67f53d953100cf4764c521006ec61485201fdec7258153285f974c42100067c21d95102b6ed644852004e7f519875001cfe74582510267c1099410007d9314c2200077940d951019edc32d8d513b7e73118931004ff7648750004ff7558a30014fc7358b51006df7358d20006bf644811004ebd5359050006ed624861001cfe7498752017d7618c53101cfe745881004e7e7499410006de7258c5004cff7659710006ef32d8950026ed5058a300f6fa305835304cfc7558d1030ddf7454d300c7ea428c12000feb6048520026bd20590100077751945311c6de63d4620016dc6354d5215dbc745813100eee62d4a30004ff764c45000cfc7654120004ff74d8520027e9624401004cff7159410004fd764c75001cfe745862000cff7654a5004cfc764c851026ed3058810146ef73d893104d7f70146500077551d43100067f3259410006dc6318121006f4439845044edc54d8d52025fa7014410005df734845000cfe72d95303667d6454750096ec5358a302767c2019510006ef3258a1000eee624c851025f57694710006df7158e20006f6618c450026ed4058810007f35144010004fe7619510006ed73588100067e5259410026f42058450004fd75d8910006de4258c1004ef45198450004fd7458b51004fd73d8950006f7715953104f7b5054e5001cfc74d963104eed54588500dedf3258c50006ef3258352014fc73d89100eeee52d8950006df4158e2004ede525
  | 27 => 0xc3218132024fc7058b5320edf75d8d52075ec724c610006ee54d8931006f970d971001cfc7458f50026ee3058850004ff764c650395f77158931004bf7458650026f74098450146ef31d8931077cc324ca10006dd5458c10007757119510014ff7614631005ef72595300067d65d431004cff7614410166df21d8d21026f64098450024fc705963021f7b54440100075f54d8d520075d5418d2104edf5358c51024fe70d9531004ff7458c5005ede4358d1004e7c70195101ffcc325953204edf7358f51004fe71d8953166de628c53104e7e655441004ebc755935100cfe72d9710097da434c120004fd7398650006ef65d893100cfc72d9710026bc1059010006dd54d8d52004ff74d95300067d5458650004bf745891000775659471004ef465945100067f20195100047d749941004e7e65d463021ff14144010004fd749862004d7c754c951026f720584502667f64946500b6de3258d2001cfe74d893126ebc10d91100057f74d951004e7f5158051065be74d4510006f671d8e21166df32d8d21014fe7358851006ec7458810167cc328c621004fd7688630007d9534c120004ff7558221074ff715891004e7c65146100067d54d8d52006dd6388410006f5429845038f75548c521014fe7358a50006f76198552006ed62d44101edee7618953004fd74d8d10005ed72d4d200267f705941001cfe7459521004fd75d8530004fd764cb1001cfc74583521feee42d89530067e429941000cff7658a31026ee105881004cfd73d8553026de1058e2004e7f54587500067d5458d100075f5418d5200cfc72d8d101cebe7159351004ff7458e51166de52d8d21025ec70485200067f65d453101cfc745952104cfe75d8930006ec6258553006dd6354c10005f97014410006ee74588100067d64d951000eee6254a51004ff7458b50007d7614c53001cfe74d8d201eeef7258f5201cfe741855304f6e6294450006dd63d4e200067f75595100067d654841000cfe76d8950006ef4158a3004edc5358f50005df7358950014fe73d952101cfc7458a500b7c8324c1200257c7054550006bf7458d10004ff7059510006de3258e511eede4358f52004bf7459510024fc705875304cff76d4810026dc7058e20006dd634845000eee6254a50004fd768c7500067c32d95100267f7559410407cf2018d521b6de6394410004fd764ca51006dc70d8d21014fc73d852000cfe72d81510067c654c910004fc764c9102667c40d9510004fd75d813101cfe74d8b10156ee73d8931004ff7558a31004fd7458750004ff74d8931466ec54d8953004fe7654d21014fe76541300067f7654750004fe76d41100167c6354d52004fe76d4a310267f7559610024fc764851020ede21d8d5221ff241440100067c31195100067d54d95211a5bc7458151006f54398450
  | 28 => 0x8c10005f471481101ef6f7254f5204cfe75185300067d73d95100047e7619510004fc7158b500067e725941018ebe649441001cfe745953004eef7258b5301cfc74d9710026be30590500067f6514510026ef2059620007cc7254d30004fd7318552006f6614c450006de6518d21004fd7458e20004fe7688530006dd73d9631004fd74d8e21006ef62d81530067f54d9510024fe70d85531a5be7418151006ef62d855304e7e6514710004ff7654520026de2058c100067e6588410004fd768c55004cfc761453001cfc74d9520027db734c120004fd7654e20146ec43d8931005df734875029fe9424c120006de4158e20006dd634c65041e7f53d953201cfc7418530006df71d8d52015dc7354a30165de7618d21005fb7054550146ee31d893104ede6554d300267e5059410024fd71d8d100067d5418553004fd70d8553167d771d8d21004ff7358221024fd71d8910006ef6214531026ee1058a300057f7558d20014ff764c120005f97094550135dc73581210057c7558910006be3259351024fe768c410006fa4058221004fe76d4930006ee7558a30096ef5358a300067c5259410004ff7058c5104eec52588511bfcc324cb51267745094710004ff72587530057d76d4651006ef54d89310067d619465001cfc7458810005df735852004ef75158750004fd75986300067f54d8d5129f79544c12000dec7254d2113dbe74d452119edf31d8d510067d54185320067f2119510004ff7654910014fe7358450026be205905004e7e6554c1004edc5258c50005ef7254d5101cfe7458b102d6cc32d8132006f721584500067f65d4120004ff7458d2004c7c7558d10005df734851000cfc76d4120006ef745885000cfc72d8d20004ff7498630166ee4258a31026de5058c50024fc7158b101b6de63d8e5117cfe769453142d7d7454d52006ee7558810166de32d8e21006ef7259531006ee4158810007f3705451001cfe74d8d21004ff7558231015de7314631004ff735875032d7f745455004e77549845000cfe7258c10004ff73588500067f31d9510196ec32d895100cfc72185530076c6554920014ff764c52120ede20d8d521c6dc3258f51024fe76d4a1004df67194551014fd7694631004fd7688450026bc305901000eee624c8100067d54d8132155ec7258131006be725935101cfe74d96210067f75595320067d54d85531dede43d8d5226ebc30d9110006ed54d89530067d5458c10035dc7348410004fd7459532004ff745963007ede5358e10006dd7258c50006bd64548100057d7518221026ed4058a300067e54d9510026f45058450006f473584501dede7618d520067f65541300067c65d8910006bf64549100067d54d8153004ff7258450005ef7254e21004ff755891004ef67198753006dd63d46200067f54595322afc
  | 29 => 0x6dd4158e20014fc7398620004fd74d8950004fd73d8552004fd70d8e21176ec21588510067f54d8151024fe7688630005fb7054e500067e74594100067c72d9510026ec205881004e7e65d4610024fe7688410016de634c450004fe764c9500067f3219510066be76d9110004fd7688750086ec6258b100065d54d8d52004fd7458450096ed72d8d2004eee53588501aeee4258a5100cfc729845000dfa724c120034fc7158c10004ff7359621014fd72d9532006bd6454c10004fe764c951006bd644cb51004fd741852000eee628845001cfe7458d203de7e615445120ede42d8d5204d7f7154451006f732584500b5cc724c530006dd65d8d2125f77549451004cfc7558a10014fe71d8d100067f65c411004d7f74d46510167e6354d5204edf5358f50026de3058c10025fa7014620014fc765413000cfe76541200067f54d8d20004ff7058752006f56118532005dd7398152006bf6454d10055f9709852004e7c7219510176ee621463002eee3258810004fd768c4500067c2159410166f7628c521004fd71d815219edc635452104eee5158850004ef7258f501067f52d9520025dc704c5301d6be644c850004ff7458450014fc73185200e63d755905020eee4258b5301cfe74d9531014fc73d8b10006df638c520026f71059610005f7714c11000cfe72d9631006ed62d46301beec62d4531006ee4358850014fe7358750144ef7258d2104cff76596210067f658c51004e7e7399410024fe7098630006de7158c5004e7e6594631006f6725845002ef521185200067d65195300067d65d481015ebc644c510024ff7358c50025f67094510007cd4218d21006ef6218553005ef715492004e7c5058051024fd7218520004fd74d8d5004ef652584500067f5459620025f976c4210004ff7458e2104e7f731951000cfe7258f511b7d431945311df9d7418d52006bf735935104ef65158051006de3298753004ff74582510057f754cb51006f74298450026b51059010004ff7458352004fd74596301c6df3158f51026f61098620026f61058630014fe7359710026f61058620015de73d4930024fc7654950006f43158450006f53258450004fd764c910004fd74d8d21026ed3058a300066d5458850004ff74d9621026f73098450006ef7258d21004fc7158a50006ef7558a30006dc2158c5039ecc32185321b6dc3158e51024fe70d891011cff7059520004fc7654d21005dd73d4130005ef7254e20006bd64544100067c43d9510006bf64545100067d54d8931014fe73d8152005ef724c7103a5f7764c62104ef85058351004fd7418530005df7354a30006ed4158810006dc7258c501eeee43d89532b76d5448520027eb628c12004edf5258c5022ef6615441015dbe7499531006bc2059351447cf531895304f7a6094450036de435
  | 30 => 0xe40d8931004ff72595300dedc3258c50166dc21d8d21167cf20d8d21006bc7259010026dc4058c500067c61d4550005f571d4d100267e3099410006be71590500067c6548510086ee62d8b101aeec6258a51004ff7158a50004ff74d951000d6c7254f52006ef62d8131166df52d8d21006df7258c50006f56148450005f9701462001cfc74d8121006dc41d8d52026f610986300066d54d8953006ef6218131006f64158620024fc764c8101eeef75d8953006ec3158810006ed624c810025f67054710004fc7694520004fd74589101df5f3054d5204ebe5359050005ed72946210f6dc325835300cfc72d85301dede63d8d52006f9601822136d7d745475010e7f53d9530006dd7458e20195ee72181511b4fe761453109ebc6448110006bc3159351014fc735845000cfe72584501ddde7398552097da534c120006ed42d893100eee624861004ebc505935105edc6358d1001cfc7458a10006dc64d8d2104ef77158752004ff7498620006f940582510067d5458910004fd721853001cfc7498630004fd7699710006f64158630004fd74d813104e7c50987501c6f631d85530047f7558910006bf2059351006ed6254a51006ef6418953014fc7358910166dc20d8d210067d1019510005fb7054950076ec3258a10024fe70d893101cfe749845002eec3218520197e42154521004ff764845004e7f5458f51006ec6298153025f476545100057e76d455038fe5428c521054ff7258910024fc765455025ff140945100065d5458c1004e7e65d4620024fe70d951039edf6218d210067d43d951000cfe76d8931167d4328c62100cfd73d8132026dc2058e201b6dc6358e51006dd7558e20104fe7619520024fc7158f1004e7c6554531005ed7218231026f520984500067f54d8520086ee42d812138775544c52100cfe7258231004ff74d89503ee7f6494551004ff7558d21024ff7058810005ed7299531004ff7458810024fe76d4620004ff764c750006ef71d8953006bd75d91100057f7419510006f64198620156ec3258e21006f671d8b10137d4638c521016dc6354d21105ec7254e50006ed74d895338f77548c52104e7465945100067f5458251006df6518d21146ed43d89313b5f671d8a3104f6c525495138777544c521006ef7158850024fc765463001cfe74d8d52004ff7258750016f4764c52101cfc7458850014fe73d8121005df734865007f5e53d4e101b4ff73d95310b6de7258e201b5dc7354a5104ebe5159050006ee4158a30006bd6488410005ed7218151156ee71d89310057c7558121006ec415885000d7c7254d520057e7518221004ff7458f5110edc3258e500267e2099410004ff7654c1000cfc72986501eeee30d8953004fd764c620006bf6458d10006bc64d8d1004cfd70d8d500067e4399410006bf6488510
  | 31 => 0xc521164ff7358d21166df72d8d21015de73d4531016fa634c1200b6ec6258930014fe73d8550006dc6398121004fd7458a50026df2058e2020fcf20d8d52004fd76d481004cfc76d4d10167e6728c621005f970d4510014fe731855004cfc755891004ef4525845000cfc7558752004ff725963104ede5458c500067d769445004e7e651462104cfe7598630004fd7459410024fd72d9520005f9701463014dbe74996213367d64d4550026ec2058a30004ff7558a10005df735453101cfe7418530026dc3058e50006f46154550006bf21593510067d54d8951006dc4158c102b6ef644852000fe671885210a6dc3158e20004fd764c85104cfc7558e21036df3118530006dd7158e2000de4724c621004fd7458b500067f54d8152026fa768c1200075f54d8d21036de5358c10166de3258a314057e76d4d52006ec41d89530067f5458620005dd73182210067d5458351006fb7058d20006f54158630166dc52d8d21006df634c11000cfd73d8532006f67398450006ef7258f50004fd764c850004ff76546200f6dc6358d50095ec7354920007755114710026be2059010005ef7548520026dd305963000cfc7558f52026ec5058810026de7058c500067c62d9510004fd74d893101cfe74d812131d7f749445000cfc721853004ef85058352196ee62d8951006f96018152004ff7258e51005fb7054610026ef7058810006ef7458810004fd73d96210067f5458630007db7054d3004f76619445001cfe74d8e21004fd721855004cff76d4d210067f549862000d7c7654d52026f75058450024fc76486300067f40d951037def74885210267c405941004eef5258851006dd634c310024ff72d952020fcc52d8d52004ff7458a10036dc321853004e7f7419510137d6434c5210eeec32d89500c6ee3258a302667e40d9510005ef7254e51005df7354a5104cfc755863004ef475584500066f54d89310067c325941017edc3158c510057f754c450025fa7014630007e63148520007d9534c220014fe73d952004e7c65d411000cfe72d8153006dd43d8d20004fd745825104cfc764cb5004f77619455126ebe20d9110006dd634c8510067d42d9510096ef32d8d2023f7954c411004f767114650005ed729855301cfc74d85300076f54d8953026ef20586200b6dd3258e20024fd72d8d2019fd73154631005ed72d4e21006dd6394410014fc73d895008ede63d8f1017df671d963100eec62d4930006ed64d8953006bc7458d101dede53d8d5204f775154e512667f6594610006ef40d89310067f7558d10006ee72d963100cff71588100057c755813200eec6248710027ea728c120006f54198620006de7558c10006bf7259010004fd72d8d512eedd644c530005f97088410407cc5218d5227776101951000cec725953101cfc74d8552006e
  | 32 => 0x3600480340560130000000736009007000800a01b005001016800706c000000a000001800019601c0c4002c01e0001da800002e7c00128000004011000800400800a51a90cc02c000000018c000000000004400203a00e080400005b02e004433c0000de011c0000020250034000033001000400009b008803c29000000401c8182005018009011400303080441e40000080024028048002803000071701c0080030010003800853200700080001c00a1001000001a00800000100aa01307681b0000014000800000e01b000800c004004004022400001101c807c0160370198048008016001805400400d025000471e111003806402804500000040e4816003002800400305a805002446d006000000208e006800001b2650000000076001017056806000106780c003400c0600004024047002005cba000900001d823a01300000080b0003004022800804d004812c01002300000240a802100000e001416d001026c00201502381bc01606500280c800000000004380c600d0020014000038001817800e00600d023c00600000800040001c900e8004000039024037c00003401306a0000014002017814e000001000006c06f000008c00a00000d00001b6001033001800c04603100ac4920020010014008004015803400002105280c400c01007580e800200302c0000ca80380db000812401b001026c00c0000300130022001000003c15601e094802c00600925f800c232004025801000206b07f848c00200000581280100550028f9002205f008003802e03d00d8020012004360001c01e000019800000400100c803001000a661007400801d001001003c00900307a804a2c80008084008024027009c0014b30002438000006000024001403a00400981ee02900e804836609400280f4024005000006801000c000020ce7e00110e800000603c006012c08c00a00281840c4003026f65058450004fd70d89512c76f54549200067f6599621006bd705935100cee76d895304edc6554d3004cfd72d855200cfe72d951000cec7258c5104e7e6594410006ed42589100067f5459631014fc7358620006ed4158a30004ff74d893001cfc74d95302df79544c2200067e54594100d6ec425885000cfe725963104f6f6254d52026f43098450026be3059010005f676945100067f6599520014fc7359520004fe76d4931006ec7158850006ec74d8931014fc76d4531196f62158752155ee7298131004fd7458351004fc7158b53024fc7059532004fd745885000eee6248410004fd71d8d5204ef55298450004ff7458e1026ebe30d9110145ee7618931027f271c4210024ff725885000cfe725951000eec62549510067f5458810006ee641893126776509471000dee72946210dedf3158c50026dc5058e20005ed728c62100cfc72d9520387e5424
  | 33 => 0x18004007000a6dc00018c030800801a013011800000410904881306f4003001b7604d6015027800400000d0030648044016007800005000100083cc00001b001004409e000006813c00200a0000068030013024000803001d00001140aa002013006000002106d004801e0a0014000400e011024000818a00200100001d00020028000bb205f00400000da000002007802600100ea17809800000280142d80060008e0c030066000000800a004001800c056000000809804e022009002801400400103c800a01a007a4d001e36a03e8000068009037000000400000c01e006800c00280541205bb107800834e00100f005802801100800305be050004800005a00300080b800000a00180803c40cb0038004008036019827800401c003000000a00500c80a004600000f812400802004e03340bc02001d83ac07400000500040120020390034014024001001000000b00e001803e5d51308638010016000800841600301f008400a002005810410808f4b0000007e00000a80000b40000c2829000a46e000011802c0000248184002003695000008a001000000c00805e0240048000021037004c00002c006011c0ae009001006413c0010028010000002000800c03a030047019801c0010038fa803000a00100e80160db0060004000007005000800200857e001c02000000080000b891e00080b4002004001800400e004000000002c00302a81a8264000000004c3780100000000002000000000003e08a001000c01e00605c014409e047000801c0060010010000028026002800402207600100a00000050000004028000005002c012000004009000607200280b41742ea05d801401200315c806c01801600202ec01600a0af000c01e01d038808800014400101280661af142805001200600000ac168000000003800000d2e8009004e2c5005812c022001001002400200002b029800e0000378ba001000000083bc01c0270a4824c00000000200140020a90018004098026013800c06a0042d1004c0000013b40090004002002018401c1760924c700000040020018000016007005800c00401d80ac002159006000c00001c00e00d8260014001805800c03702900604d000103480b400802c00080ac0b00f2003809000001800282ac09001003d000001801038b000809c00d0080014032068002087401a00200102ac0000b502b801400002400d005c02602a012852801001600b80d0228075007000000000c000001406e0140258014030003044805403000900000000560105bf800013e00d001803c00602006a000c074001057800400003c001000404a051000837006a015000000001600007d00780100011a2814c10a00900c000406403e0108004150000001814404000004c0d5c02001702e844c018000021003c01a00102280fc0100
  | 34 => 0xc070800000a0200100660000000037001801e004011000c02a32703c865800a00b0001bb401000000400a400004d000800000002402492f40b600102f8054002025000824803ea53000006497802400100000480820058040000000004801401000103d80441d2005007003401000c010808801405310000380000280888018006003006801800a00000881e008a009009801c04001f00180603c4113004805c48201a00f000000e1ed00400000f00a8000000c00414001586200960020068004000007000017000000d00b80b0002001000001832205501f808c01805a0192b64004006018800004600c04100140ac0090000028058005012803000010e06a02f000c000001001005a266003859809a023035004005a00200c80000000b2037000c02000025b000806800600112bc00408500c004003601b00101685ca00f002000800601f000000c00200000180b81c80010000004000031003800802c3a7029800404a0520058000000016057001e2d202904183c4072016032801800202d00080100001b3001218400004c001801c00600000a83680060060170000000000234801d034000004802000e1fe202057000a0140ea800c0520010028180004005a8c872400401500a80e400408c002012001402800100141da006003058400000600802bc036014003000000049d001800001608900c002d38412c006800000000200500103b617500f866803e019051800001a0020090044000001008001400803f000802001404c009018400201f0000bf400a00b00d0000046003000800001006d05d005800000300400f400002600c805403a000001805001200a0008044008031000000801209500b004000804c00300080460e000280bc02802d009000000403b00511d0000003001805000202700200000f400102c82540220c001080b002a0141840018056000016800400005c00980c0032149002001400000a09d8034000017013801c0000fb04d804402c07600800003b40a3008000022000c08e000403a026181000002a000000000801800804202e001e1c5005001002200106a002000402000381300f8033002800002200005d801c08205a01c002011a000007850400c057002800439c00007f80d000a0132650000004008000804403c00d00886b43da0070150644000003032800007e00000800dc0ca000018802c03800000000011ec00000a0004018115000806008801e00005ac00200716f00f801400001000000200200be002871a002002800012600a00780a4190066003802c006008004801800c001000811c00c00200800000ac00e000007803404b00000381c8006059801000203f0178675eaa005000001c01e01201100481cc19f0068004004015000803803c094001807005a009000025000000000482e800e0000068
  | 35 => 0x6842e404f00481640582b700600340e000118d01dc4bc03103080440b000002c81b4000003000006c00000000000083bc0a101380380420000db80e427a03709000dc0b25b200282e004c02200302a000029d007010400206c016801404a00000481940dc00d001805400a01b032000004a008005806001e00203e238c040a38015800006818200200a0002004001000009c051007003400c04f07c80041be08329600980000050118000006001006003405622c0398064000002007800001c00301100583c600100006100800010152e80004001005007c0000120028010064c8500000b4000057032001c07002900382e400c161001003c004
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5d7394f654800717908bb2a088003271d363581210046ec1ceca962004aea80105628c0018d8e5b2ac688002ae60021590100356cc00e4b18200387c85dd165040017c70498a20082ca9761664d8d5200657326e4a982000c3d655d351840018deebb12c0988268fa14735905000556c20eab1020008de8758d52040011bb0f320c690a53179d954d8d5247f0fa02a8b182000c3f7455165840130f90aba2c6880132e9c1648841000477c12e7308a000a9d83dc9640400147d08392ca080030fdd1545963015476c36e49882000e2d5450962144014f30020cca080030f5d1541853000566c1882b14600987c855d1624400195cc4ba6a208002b32097558c1020d67410e9b1aa400a5d83d086544001c5ce8aa2c51800297a167458c1002578402e8b08a003c3c745526188119998edb92a6980028fe11651951001e1e3a2a9b02a200a5e8599363484134ed0a20ac2280b23721b735812100667b1ae5a9a40008fb87580604c859998e5b1a6290802ba6004158a300052ec2882b1c40048ef8758a210400117d0e196c8880029760c41d951000476c14eca9e2000acf8259063548011db0f320c4a9802aba0b73590500070eaa287b026200cae74d8b514c40159f06b20c4a99321fa1f51582510061eba2a9b0aa00087f87594658c4018790bba2c3280033358f7254c100047743882b10a000e2d54907624c4992ef0ea8ea0882629ba1464189530052f428e9b1a42038df8750f634840153b0638ac828003330c973185205770fa12a9b1aa49be1d4255163880071d90ea12c428803171d4635812120d6741083b1aa44ddb371dc36444007878e8aa4c3180023b61b7254c100053cc0064b2820008ef875906254c071f10ea02c0288029e60041d951001e1e3a2a8b04624ea788050465440994f500196ca8822717d8e75985320052ec28e9b1a4200ab5810c964140035c90c98c4290802b960440d89310061eba2a830a640087d8710965040010fb0e210ca880268fa1731593510043f43aa8b1a2094c5c735516548001972e0382c9a88271d9c5769445000c76412e7b02a209a6e85d0562140011bf0eb20c69080297a174358c1004d2f42e86b18a0008ed8710562040018becab9ca2980032b1937254d1000536412e6b2820008ef825cf60544010f90eaa2c69000a37a0e71d81520146e41ae8b10a200ccd7358b528c413c6f08aa4c2281321fa1f54582512661eb82c9288a041ace821036354801c3aa920ec6a9012b6a004158c100064e326e6b122009a7685106611400187ce3baec8880030f5d364195100062e3b2a6a926000c3e761976444135d9065b82c690012ae2017559010166e2396e698c42018ec825d931940090f90eaa2cb0800f0f1d154587500256d40082b18a00087d87d0f6544001c986532a64080270fe117419510
  | 1 => 0x90aba2c69000f0f9d1541853204c3f43e8332820008fb805d165484014dd0a3a2c4080268fa1472590500247ac3c83308a000e355450a611400199865bb2640822333dc8735885100566c1083b1a420987c87d5162440018deebb92c6880021fa1c43d95100061fbaee1b2220008dd87d09630400187acaba6a3100030f2177458d100246f43e86b182000a79800c565040031d905bb2a608002ada0432593514b66639286b18a20087d85dd93244001c38e8aa6c6908021f61f43195100056cc0083b1aa400a5e8510363484018b8e632a42880038d205755901000567c1ac83126200d71515c051c40014bd0620cca080038d553435845000cf243a6290a4000c3f745526114007878e8aa6c6880032e59170884101456641ac510e2000ccd721c963040015d30020ec498802b3e0d7158a300146e41ae5b02a200c3f7455363c400159b043a6c6908031bd977254d1001c3e43aa8b2a40048dc8750d63940095e5003a2c2280063ba0a7654d100056bc1ae4b08a08fa6d85951620400147b0b98ac9a88029ba1674588100061fba2a8b2820a5ab4815c164d44011bb0e206c6a900297a0f42594100056dc32629844016ace83dc9634800155d04382c9a880317d97735891000656ba2c5a882000e3954d03605440159b07320c4a98261fe1174994100064e39ec8b122000aae849d7624c401b90e7b82429000f0f9d154588500062fb2ee6a8a6204a7a800c565040014dd0a20ac4080029d61743984500051f420e6b282000c3d74d0e6504001c6aa8a1ac228002b360a7458e200956741882b146000a9e849d763484094f500194ca080021fe15764ca100253d400833282000e2c645536254c0117d0e192c8280029d61741d85500061ebaee4b2020028dc835d921d400187ee92a2ca080038d5534398450025b8402a3a822000a5e8310765440071b90ea1ac7880021fe1d651953203c5fc3ac9a8820008be8714b6444001c5f08aa2c40800f0f1d354589102663bb82c3288a000a75859d2611400199ae7396cb188038e551405825104e1e32ae9a8a4200c3d7450e65040130f90cb84a2a8802b360e7458a304be36392a8b2a6204cda7058c5104001998c7b92a290803330c972185304e726196a8b1a4009c3f845d265041318dcedaa6c49880a3720f76484500247ac3883308a000c3f7455162c40011bb07b92c1a88030f5d15458e5100717aa4a8b1020038be87dd162440014db0a3a2c51806eb66007258c500047743ac49882009a74855d161140014bb0620cca0800f0f1d3545951000557424cbb126200e4c329d76388401998e4b1aa7280063b208764c5200052f428e8b1c408fe1f405516314001878ebba2c4880278de1154584500247b43e82b08a000acd83dd7624c4994f50020eca880032ee1376440100066639ec490a2000
  | 2 => 0x7735491001e1e3a2a9b02420087f87594654c05159d0620ec4988023760e76549100052ec2ce8b1c4000a6d85d036254c0187ee8aa2cb109ceb3a1b638852104d3642ae6b10a04cc78605c2515451dc6e213aac80804ab320d62483100063632ee498a2000a7b805d1650400787ce8aa2c1a8803330cb73582210071a3228232a2000e2e745516204001c58e8aa6c498826972157158c500051f424e5b2a2000c5d545cf65884599a8edb1a62908038b5514258a3159e37ba8c4b02a6018ec825d8514c00187ee8aa2c6908030f1977458d1004f1b38ac9288a00087e87d0d6504001998653b26588003271cd64484500070eaa482b1c4000c3f655d265440014db0a3a2c40800e1f21d545953100c77414ec98aa000c3d655d0654c80117d0e292c808003271cd64548100053cc0065328200087d87d0e6504001d6502b2220080268fa17715905000536c2e86b10200087f8759465480018beea39ac48805af2209534c120005d8c26a28802000a3f84584519400187ee8aa6c4a88029b60864195100070f418c832a2000a9d841d5638800199864b9cc3a90038b55343588100061f432e9a8aa093ccc73509624400159b06386c4988028f61721593510070f29ec9a9a2000aad82dcd641400199ae4392c6280270f1d5644c45000572c1686b08a000acf8350962d4c01c3aa8a1ec6900029b61741588100045ec26ec9922000cb9645c23104001c6aa8a12c228003330c974d8e210247ac34e3a962000a75851d161140099d4e0b10a318002aba1073588101cd1ec2ee4b26a20087d87d0465440071b90ea1ac7a90021f612761951004d1f42e42b26a2008de8718d60484014eb0b392c22800297a0f75596210146f41ceca9620028dc835d9520400187eebba2c688002b9a0440d89310dd2ec28e8b18a0008de871036348401c5aa8a1ac408002b5a0440d8d520056d40083b1aa400a75851d26114025b88e718a42900f73398f7254c100061ebaee6b2020ade4f3255163d480187ae8aa2c7a8a331b9977254c100061eba2853282000e1e53593530400117b09bb2a4880270f1d5644c8500061e32ee8b12200487e85dd261d40014bd0ba0ec6908029de1574584500061eba2a8b182000a7585107615400193ee9b9ac4880031ee1776440100045fc22ec98ca003c3c74553634840187ae920aca080023761e6418d520051ec2cc7b222000a6e82dd5658c4019986438ac690002ab6107558a3000536c2e85b126200a7585d0d61140071f10ea02c128a92b3a0c64189310053cc0065b2a208ca6f82594654c8011bb0f328c6908261f21f5458d2000566c1883b1262018ec825d1654c4994eb023a6ca881073398b7354a301ee6631ee4a9a4200c3f751d163440071d90ea12c5188038ba0864d951000537410e9b2a208fe2f40551628c0130f
  | 3 => 0xca90200087d87d03654400187ee8aa2c318003530ca75d8e210061fba2a8b0ea000e1d54d09630400199864bb264280268fa14305935100c77416e6b04a209c7475585211400156d02192c808002b960473588500063632ee4b1a2000c7b761d5100411fc3a80aa2c6080030fdd15458b500071aaa482b0ca0008ef825d931940011df0eb28c49880e2fa13764c9100052ec18e9b2a2000e398019365440091b90ea1ac7080030f1d46458d100070fb22a831aa44cc7870d9551440014bb06320ca880038d55041185500053ac2864b08a00987c855d9328400187ee8aa2ca90003875504158c5004d3a42ee8b08a000c7775585311400159f04b20c6908028f61432d911000657312e9a8c60008ef8754d6204001c3aa8a1ac7280261fa1c32195100064e326e690a2000a5e83d0a6504001c9ea729ac408002b9a08745845000566c16ebb1a42068dc8758d210401387ccaba6a3080030f5d572590100049ec24ebb14624ca7a801d36544001c3aa9a06c6a90030fdd154d81530051ec20a5b2a6000a5d851c963040011bd0fa12c6280023760e76485500070eaa082b182000a6e82105650400153b06382c9a88033c9c570d97100052fc2ac7a9820038be845db51040091b90eb1a64280038d60475d911004c3f43e8232a2000cb974580608c4010fb09baac68823b1dc4374594100071c3aac88802000c5d65dcd210400155d0839ac428002b960b439845004d3b436cb28a2000e2c64553624c4134bd0b3a2c6280031b9d572d8e2104c3f43e8732820008f787584614c8070ff0eaa6ca991335c1c365545100043f43ecab1a2000aba800c964d44092e90ea8aa0880023be097654d2100c76416ec988a000e3554906618800159b07a12c4280029d614329845000716aa681b126200cac741c963440014db0a320c4988f73398f7254e203351ec2ce0b26a200a6d8510562040095d50039ac4280aa3b61c41d89310061eba2a9b2e2012ace839d1628c02d59d053a2c710003875514358f102671a882c9288a000ccc7358921140014bd07a16ca88002ad21161185500061eba2a8b04a200a5d85109631400193ce8b1ea3100023be09745953039e67390c63024200a3e859cf64440014790ab9ec88828b179db5418d2144727b16a831aa40087e87d5163440019d2c4b8442081372d1db645451000657ba0e4b1a2000a3d850c96404001998653b264a88123ba1f42588100045f438a7b222009a3e85dc164d44014eb0b3a2c2280123d21d41584500052ec2881b1a4200a3e859d76444001c5aa8a12c40822333dc87358b5050f27b16a831a428cacd831c36254c011bd0e31ac2a90021f6137558d200064e39ec8a922003c3c745526194001c6aa8a1cc2280038b5d15458a300052ec2884b18200087e870c965040015d50020ec498a271719
  | 4 => 0x2d400147b0b316c888002aba08715905001c77c3a85b12a609a3e851c164d44010fd0dba0ca8800317dd4735952000716aa684b146009a7685c85611400787ce8aa2c62800e3721d4358e510047dc3ac0304a200e8c32591320415b8dee4aa2ca99003331cd62486100057341687308a000ccc7258d310400187aebb82c9a88038e55140580510053ac2ce6b08a000c3f74d51654400155b09328c49880237e0d7654b100053ac2e85308a000c5f54dcd62c40015cf04b9ac22802697e115458c500062f29aeda982000a5d85d0363485298b8e6aa2c42880f0f9d15458f510062eaa6e6b12200087d87d006544001a98e7b2aa4900269da1432584500265d302e83044200e3554905611400187ee8aa2c5a98268fa17725935114567418e9b1262038f8875016088413878caba4cb188021fe15745951004e1e32ae9a8a20008bf845d950440010fb0fa12ca08003171d473589100061fba2a8b146200e2f64550624c4091b90ea1ac7100021fe1d651952101e1f3a2a9b0a608ca6e851076254d298bce6aa6cb108029b61674d893100716aa082b146095c5c73d5162c400717908bb6a48813a9e201515805144e663b6e6a924016acc8258d30c400187ee9aa2c328003721cb704c5304752f428a8b1820a6ce972d82604c8010fd0faa2ca880030fd9574d453101c5f436e8b1220018ec825d931140010fb0e196ca880030f5d154d96210043ec2ceca9c4200e1f6455363484018d8e4b2a62080269da167498450006a6190eab126000a3e850cb64440091bd0fb1a6388003331cf7258b1046717aa4a9b12a6038ec8750962c40134ed0a194c228002aba107558a3044d66c16e3b1aa48fe1d40551631400159d0420ac62800a1f21576d4d1026c5fc3ec9a8a20008ed829d95344001c6aa920cc228002b9209739845040d36432a8312a600c3d7490665040015b30020ac7100028fa1262d95100043ec2ce3b0264739ce87dcd214800156d02196c88800327993734841000666192e8b1a4000a778150065440091eb0f30c62281335cdd4705451000477c12e8b2a6200eb16448510040011dd0e312c0988031e59570944100056741082b182004aea801cd62040011bd0e20ac7100031bd53725953104d3742ce8b10a0028dc835d165480018dea8b96cb18803331cd62548100055a40aeab202097c6c7255163440090fb0abb0a20800a37a1f7358b1000656b26e4988a00087d87d0a65040011bf0eb28c690802cd612659471021d5b40ee1b222000a3e850c9640400187eebb22c4880030f1d06558d10095e441aa49824039ab6811c164d440117f08bb2a6880269ba1742588500051f42064b2820928bc865d351440130fd0b38ec09900f0f1d1545845000477436e4a9a4266c3d865d35154001c3aa9a12c6280a3b118e31885210046fc1ae
  | 5 => 0x80021fa1f5458d200051ec2064b2820b6a6d859936254d1fc3e80aa2c7100121f21776544100070eaa083b1aa497c6c7255163c400176308382a288003175537358b500061fba2a8b10a203c3e74551628400957100b8ac8280021f61c43195104653742e81b12a60caba86dc3644400153d08392c6080123720f764c6200064fba6c6b024200cae7458b510409b57500196c8880261fa1f421951002476416ec908a000e4c321d563480998f4edb2e208825f1b9c954d963100578c00e9308a08ec6d72d5363480834b90caa6c6a90038bd9154d895301c7643a84b14a28ccaf625d0654c8014db05a18ca880028f61053594100061eba2a9b1a4000a3e840cb6544001e6483200ca880029b60841594100052ec2ce9b1a4200c3d7419365440130fd0fbaac6902b78b50d54d895300c76412eca9a2000c3f7455161140018bccbb9a42080029720d72594100043ec24eda8aa000a6e8210665040070ff0eaa6cb880b33398b734845046537428e9b12a600a6e82d96658c401998e7b1243880023de1d61185530057540083b12a604aba800c964041134bd0a3a6c6a923f0fdc1755901004d1f42864b26a200ccc625c2314c4051b9063b242980030f61d64944500043f43ea8b122000aac825cf644400199865bb265a8803330cb764ca510043fc3aca32c4200e3554906619400187ae8aa6c2a900317dd5634c8500076299064b08a0008f5870ca6114001c68c9208ca880121fa1e535941000716aa482b10208ce2f845536254c134bd0a212c628003ac592314401004d1f428e4b26a200a5d859d1630400187eebb22c6880271d19671d49100046fc1aeca9220008ed871076254c01998e7b92c4880030f5d154987500062fb2ee690a2003c3e7455163040090fd0bbb463a80063b20974595300051f428e6b202000e3554905618c001a98e432aa69800237e0d7458b500061eba2a9b126000e1c645536348401970e9b82ca88002ae60032593510061eba2a9b0a6000a6e82107654400199864bb265288031b1d762581310052f42884b182000ace8650c624c401c5ee8aa6c4988038e615644401044667bb0e4a9a6000ccc7258d31140011dd0e312c2a980237e0d7458b100043ec3e85b2a200087e87d096504001878ebba2c6880029d617425845000746196c89922000acd83103624c4014bb0b326c690ac6976166418d520052f42e86b1c408cc6f54dc963d4151c9865aa6c099012b6a004158e200047b43864b08a000c3d74553658c4011bb0db9a422800e1fe1d54d95210057341686b08a0038df8750f6354809974e0b24620800237e0d764cb100247643a84b10a004b70805455044001d8a64194c2282278715154d8d5247f16a02a8b1460008f787584614c00147b0a192c9a8803a30c9644cb5100666190ec992a28c8ef825d93
  | 6 => 0x4d3b42e86b08a000e38641971044001998c6b8442908023761c41d8d5201e1f3a2a9b2a4000c3d74553654c00147d0dbaec8880023de1d61185200056741ce8b10202a8ec86dc9604c4091b90eb1aa71000237e0d745952004e1f30ae9a8ca200c5f759d563881298b8e6aa2ca908026d6137654710006a6194eb30a6406ad5811c9630400147d0bb9ac8080032e21376440100061eba2a9b2a4200af3805d161140091e90ea0ac3180032b5937254c1001c3e43aa8b2c6200e2d745516204001c5aa8a16c4a9802b5a0c41984500257940082b08a08cc6f54dc9631440117d0e3a2c688002b3a0a7458c1047d3ac02a8b08a000c3d74d5061540015cd0239ac4080030f5d15458e2000557420eab10204dc3f50dd1619400153b0932ec6908271d19671d4d100061fba2a8b2a6404af28010661140134790ab8ac8280023761c40d8d210052f42e82b182000a6d85d076254c01d62c828a200800297a0c74d95100056ac1883308a0a3ad783584614c801c5b04320ca8800e1fe1d54d951000717b22a8312a6008ef825d95304001e6282a00ca880030fdd154d812104e2f32ae628c6203c3e7455361480014bd0b320c6908030f1d3655891021d5c43ac8880208cacd83dc76254c134bd0ba0ac6280123b21972d4d200061fba2a8b2e2000c3f655d26548413c5f08aa2c4280030fe177458d100056ac1882b08a004cda7058c5188001968c838aa0880021f61f421951001e1f3a2a9b0aa400e1d5450363548010fb0e214ca08002b36084158c5000717ba2a9b12a600c3f7455362c407347b0a39ac9a88021f61c41594100061fba6a8b12204cc3f705925114001c5aa8a06c4988030fdd474595100045f438e8b122000a6e82dcf654400787ce8aa2c7100032b1cb6458d1016666396c6a9a42008ef825cc61540134ed0b3a2c228002bc600745845001c5e422eca9a2009c3e655d0654c80187ee8aa2c62880f0f1d1545875300716aa685b126200e36811d764440031b90eb1a64288021fa1c4359410006363aee4b1a20018ee87dc9631440147b09316ca880029d60754185500061fba2a9b02a400acd821056304009974c0ba0c118a678d840641951004d3a42ae4b08a000c3f759d564040014ed023a6ca880028f61272d951004d3742882b10a000c9c7418d60484018ef02ba2ca08012bca0032584500046fc3ac831aa400af180107615409d4e90ca08ca880038b55041d89310062e398cab122004aba80085640400187acaba6a31825f1b1c954595300246f43c64b1c2000ccc32dd3604c8051bd07bb443a80021f61f41d95100070eba2a8b1820008bd84dd953440018beeab1a63280123720f764c81000536c2e84b102009c6e655c8518840117b0fb26a28800e1fe1d54d95200061e42ee8b122000c6c72d9531440011df04bb0a29
  | 7 => 0x77651c550440014eb02196ca880029760f425941000578c0064b08a0028dc835d851480010fb08bb4a2280023b60b74d96310b4e743ee498a6000c6d54dc9654c007878e8aa2cb880028fa1053594100043f43884b28200087f87d90654400147b08196ca880029ba1743588101fe363b6e4a9aa400e2d54d0d6214001878ebb22c488006b3209634c8510257940065308a000e3b805d564040011d90eb1262280029e61440d815100477c12ec9922000a6d82106650411fc6e80aa2c22805af2a0f724c1200062faa6e6b2a424e87c8755160144090f90eaa2cb180023ee1d60181521dd2f42ce9b1aa400acf825d563880091d90eb12a50800a37a0f72582510066639ec4a92a2008ef825ce61940091bd0fa1ac7100030f5d773593510051ec2e42b20a000c6c75dc963480095d50020ac40800237e0d76486500051ec20a7b2a200087d8710e650403947b0a38ac828003330c970d8e210265d382c82882000a9c835cb644400187ae8aa6c2900269ba14745885000666392c698c2000ab9800cb644400187ee8aa2c3a980297a0c64d95100043ec3864b2820048f4865c753440071b90ea1ac6880029b61441d895304d1f42ae0b26a2008df835d9534840187ee8aa2ca908030f5d15458a1000578c0065308a003c3c7455161d480187ee8aa2cb189073318b73549310053742e82b146009a748590561140014db0ba1ac4280023b61c40d893131d1fc2ae2b20a00093d841d5604c8071d90ea12c4880029b60841d95100071a320caa8a2009c7476195514407b998c7b92a6a900e2f211764865000556c20e6b102000acd8210363484011bd0fa12c6080038b55143588500051ec2ee6b202000c3f74d53654400359904b1a6408012b6a007258c100052fc1ae4b282000a6d85d05621400159f06b8ac42800f0f1d15458b100062faa6e6b2a4000c9f64dcd62441438dee5aa2c6908261fa1f42994104a62e39aa8b16a00487e8795165040091d90ea12c508002b360c41588100046ec3882b1c40048f587906618c0015990ca10c69080387d915418d210055cc0064b202039a3d851c964d44091d90ea12c4080270f195749962100657ba0c4b0262008ed829c76054c07878e8aa2c11080a3720d765491000657b26e4a9a2003c3c74551618c03947b0bb9ac8280038b55142d852047e3c402e8b282000e346419651440831b90db9ac0a90029d604325941000536c28e9b126200a3d859cb64440130fd0e214ca080023be097458f100070ec18c832a2000a79801d365440011b90eb1aa40800297a1464d8d210061fba4e8b282000a3e8599764440011db0f320c498802ba60041588100061fba6a8b1a2000c3d7455162d44011df04ba2c6288030fdd154582210046fc1aeca9a40048ec8750962941138bee7aa2ca990063b2087654d200
  | 8 => 0xe0b10a208003175cc73d95100043f43e82b2820018ee87dc9654c401c70c8a00ca88003879d15458c5040667390c6302a4008bf845db53440011dd0fa1ac40800317dd67558c100146f41ee4b06a204aba801c564140090f90eb2aa6080038b55241d89530055cc0062b202000c3c715d5640409bb60e1b22a2882323be09764c8510055d43ac88802000a758510e611415bc5e86aa6c4a98030fdd343d951044d2f42e83b1aa400c3f845d3654400187b0e326ca880022fa1c53590100071aa088232a2089c9f635d0654c801972e8b00c110803275d363d452102d74c00e6b102000c7885dd9100400187ee8aa2c788002b5a0f42984500047743883b12a600a3e8598b644400717d0fba2c3280030f5d154d85320051ec20a6b2c42048f8805d165040095750018ac80823f8bd0154588100052ec1ee5b2a2000c3f7455061548091eb0d38ea7880030f5d7725935100637ba8e4b1a200387c875516544001c3aa820ac7100031759573946310043fc22ed288a0008ed87105628c00147d0bb92c8080030f5d15458d200051ec24c632a2000a76810c865440091b90eb1aa7080022fa1f6458d1000566c1083b1aa4038bc845db534411f87e80ba4ca0800a3b21d624c8510054f420e4b18a000a6e85190624c401958e8312c098a4f331cd42588510070faa4a9b1a42038be87dd16344001d1ec8a18c498a6b365cf60981320061fba6a8b04a20487e85dda21d40010fb09bb2a228a3f0f5c175590101456741881b126200a6c82594654c001c750ab2220080031bd537258f100045fc22ec9922000a9d83dc964140014eb02194ca080032e193705451047d1ec3ceab202000ad4835ca6114001c3f08aa6c690a83179d95418d210053742881b126200a748155165040018becbb9aa0980021fa1d5458d200061fba2a8b06a600ccc7358921940010fd0e32ac4880030fdd143d95100045ec3864b20a000c3d74d0965040015cb02206c4a98261fa1f431951001c3e43aa8b2a600087e870cb654400187ae820aca080033658d70144100061fba2a9b02a2009eb8754a304800159904b8ac6280022fe1171d952000477c12ec9962096ccc7250d6344001c5aa8a12c4280031bd537258d100047643aa6b102000c5f75dcd6244007878e9aa2c6880030f1d47458d1000536c2882b10a000a3e8498f65440018d8e532a62080038b5514258a510051ec206532820008dd8710563040014bd0a20ec6908b2b3209638c7100061ebaee4b20a02cdc472dcd314840156b02382c9a880f0f9d15458b510051f4206532820acc5f75dcd654c80159d0620ac4080031ed5376440100147c432e028a6003c3c74553625440127b083aac69023f1dc4174594100071c3248032a2000a6e859d3624c40199864bb264080033318d72d452147f1a882eab202000c
  | 9 => 0x53549200051ec2e62b20a000a6e85990624c40187ae8a10ca88257171cf545891046f58c0ac88802004aea800c562040053a90e98a4298002b3a0f42588104052e432a831aa400a6f825cd65040011ef0eb08c2a923a97a145458e2051726196a9b1c4200a6e851cd620400787ce8aa2c7280030f5d254d95100061fc22e8b282000e1d5450f63484051bd0fb9ac4880123721d4358c500071caa280b04422cccc72dcd63884130f90abb26488002b360f4258a3004e3d32ae02882000c6c7259553040014ef02aa0c2a822333dcc7258c510052ec2881b1aa4048f587906618800156d02192c82826f930c95458d20156723b6e498a4200a6d85103624c401998e430a62980023de05745951055726196a830a6400e358119065440014e90eaa2c2280028fa1053d951000674b12e028c6000a5d8519363484011bf06ba2c6908030fdd5644c45004d3a42ae6b08a000a6d82dcf654400187eebba2ca880030fdd154d81310046fc1aec908a000c3f7455363548011db05b9ac128803330c9764cb510061eba68632a20008ef825d9538400187eeab2265a88021fa1f43d95100054f420a4b1820008fb87580608c4015a906b92c2281eb8d19151145100045fc3acbb222000c3f745506154c01c986432a64880033318b73545310070eaa687b1a4200d4c72d95534c0031dd053b2a7880270f99574d462057727192a8b16a60987e8710465440095e5003a4c2280269d219511451000566c1ce8b10a088e4f635506254c0147b0a392c8080029761743d8d210046fc1aeca942000a5e85d0363484130fd0b3b265880021f61c43d95100056b41e84b08a0a2e4f63d50624c4011f700ba2ca880028fe1171d951001e1e3a2a8b122000aae82dcd6404001878ebb22c68825f1b9d954d893100536c2e85b12a600a6e821906544001c5ae8aa2c42800237e0d72d81510052ec2e83b1a420987e8710c65440011f70eb00c0a88038b5514258a103f61f432e9a8ca2008dd83dd36588407878e8aa2ca8800f0f9d154d8d2016567436c518a6200e1d5450d631440199ee6392ca9826f87d095458e2000747b228431a4216ace821056388001f826290a6090003331cd6254a510047743ec4b0aa603c3e74553614c8134b90ab92c6280022fa1c64589100051ec2864b20a000c3f7450b65440014db0a326c4989321fe1d65d4310005374168632a20048ec87509628c013878eab2242280030f5d143195100046ec1ce3b02a409c5c655cc514c0130f90aba2c22822333dcc7258f5004e1e32ae932a62038ec8750962d4c018b8e6b2a42080133c1c1615465000656312e9a8a6298c6c72d51654c40147d08292ca080030fdd1549865047f0ea02a8b1c4089a5e851036354801c3ce8aa2c6080030f9db65d9110446663b0e6a924004ada801c963140099d4
  | 10 => 0x32c4200ccc7358952840015cd02206c4a98030f5d671590100247a40eec908a009c3f605d3515400193cc9b9aa408002b360c41d89530046f43882b1820008df835d165484014db0b3a2c4280033358f724c4100966639ac490c60008df835ca619400199ac7b9262280028f613515825100666b1ae5a9c4200e34645c465440010fd0e216ca8823f8d50154584500052f42ce8b1c4000a3e8414b65440130ff0ebaec7108021f61c41994100070e322a831a4200ae7825ce611405978906b9463108123721d634c8100064e3a0e6b122000c6c7219563440014f300208ca88002ab60b735935104d1f42ee6b20a000e1d5450d634400155b0932ec4988038d553425845000567c12eab182000c3d745516384001d1864b2264280023760f72582510071aaa082b08a000a9d84149630400187acaba0ca900029ee0141195100063bbaac2908a000ccc325d9328401387ccaba0ca900030f5d3429941047e1ea02e93282089c5f54dcd621440117f08bb2a4880021fe1d65197100066bb9cc2908a000c3f74551654c5198dec43aac0990030fdd572d91100062e39eca90a2000e2f64553624c40199865bb265280030f5d573590100e51ec2ee4b20a088ccc761c9534c00153d07b92c9a88423ba1c61485200146e41ae8b122000a3d84149650409d4f500190ca8822637e0d764c8510046f43ac6908a000a3d841cd650400199864ba0c29902637a1f6354d210051fc22c328ca0008f7815d165480014bb06208ca880028f21572d91100056b408e4b18a000cac64dc931440018e902ba2ca080032719373549100071aaa685308a00287e87d95534400199865b92c1188268fa17215905000666392c6a9820008ef825d1654c801e1aa8a18c49885b331c9634c6204855dc02eab202000c6d65dc9310400153b093aec69080327593734841000716aa482b10a0038f887501608c4015d30020ec4a98268fa1670593510052ec2883b1a4209a3e850c96414001c9864baec7108030f5d154d951000536c2cc83126200c3d7410665040014db0b98ac4280030fdd154d895300637314ebb146200ae9800c562040354db0a39ac42800297a174258c1000666392c6a9ca20387c8755165484014db0a21ac40800a37a1f73595200061fba2a8b00a200c5c75dcd6244001c6aa820ec2a80029d205401951004d2f42e84b18a0008dd83dda21d40014bb0bb1ea6908031759773548100047743ec4b026200a5d83d0a65040015cb043a2c2280063b2097458d100052ec2cc831a4200ccc329d93254001c6aa820cc2280123e20174595210051ec2ce7b222000a9e831c5641400787ce8aa2c408003530cb755813201e1e3a2a8b1c4200ccd73d8b524c0014bb07a16ca8820273a1f73549200053ac2884b08a096ccc7250d63c400187ae830ea2a804b531cf
  | 11 => 0x40010ff0aba2c4880029d61741185500053cc04a9b2a2000acf835d5628c001c5aa9a06c4a98132e9c1649441000636396caa9a20048df8758f53880014f300190ca8816b339cc621813100637b2ee498a2000ccf73589210400187acaba6a2080034d5d241195100043fc3ac832a20038ef8750b624c40187ee8aa4c31800317d9773549100e55cc00e2b20a000ccd731cd620413d57700b8ac8280038ba0864195100062fbaec6b02420987e8710e65040015e30da8a20080032799373484500061e38eebb222000c3d7455162944091dd0f992c4080029d614429845000656396c898a2000a758195365440015ad0620ac2280030fd977458d104ae2f3b6a9b1a42008bd870cb64440011dd0e20ac40823f8b50154588100061fc2ee8b2a2009c76815da51140014ef02ba2ca080030fe17745865004e3ac0aed288a03dace831076254c134bd0a3a2c62800237a1f635815200556c10e0b26a28ea3e851d564040014eb0a21ac228002b9a08419845000573410e9308a00087c875516344001c38e8aa6c6a90038b553425881000c76412eca9c2000a6e851d1628c0018daa9b92ca988063b209739865004d3bc22a8b08a0048ec82dd9320412b4bd0a320c6a913a9ea0041195101cd1ec28e0b26a200e1f74553634840155b05b9ac8080023be097654f1026d5ac08ebb22208cc6c65dc953440018b8cbb9ac48800297a174158e2001e1e3a2a9b1c42038be84dd9534400957500192c828002b360a6418d210065a3a6e2b2a2000c3e76dd764440010ff0aba2c6880261fe1174195100045ec38a5b222089a5f83594654c8019c8e530a6228003330c8764cb100053cc2e81b02a2048f5815da2114001970e9bb220080029b61740d89310054f418e0b26a28ee35109d5640400195cc9b9262080029ba167458a304ae2e39ea8b2a40009eb87486304800147b08292cb189325de1d51d431001c5f426eca922000a6e85d09628c05999cc5b9a42080038b55041588100061fb2ee8b1220008ee87105628c0010ff0aba2c69000e3be1d42d89300052f4188232a2000ccc325d3604c8011bb0fa12c62800327dd063581210064fb26e690a2002cd476dcd314849b974edb262088002b36084158e200055b42065308a088e4f62550635480159b04386c6908269de11549845004d3b42ce4b08a04dc3d50dd161940018eae8b0ca2280032e59170944100146e41aec90ca000cac7259131040070f90eaa2ca990063b209731855000666196e4b06a60087e8755162440018b8e732a42082338b15154d89530054f420eab182000d3471dd7644400156b02192c9a880387a0c64d951000477c12e8b1ea000ae68210561141698daea314c2a9a7f93d895418d2147f1aa02a9308a000cd7735852114007878e8aa2ca90802b5a0c74984500052f41ecb
  | 12 => 0x123b60b74d8d200043fc24eda8aa000ccc32dd363884134dd0ba1ac4280269da1741984500047743ec4b02a600ccc329d932440011bd0e20ec6a90031b1d47258d1001e1e3a2a8b1e200387c8755165884018f6edbaa200800f0f1d154596311476231a6310a4203c3e74d506154007878e9aa2c3280030fdd1545865044d66c10e1b1aa441ccc72d8d535480187ee8aa2c1a90030fdd474589100071aaa48330c6000c3f7455165440018baa9b9ac588003721cb7054d30144e641ae428c42048dc8750d6304001998643b264a80029de15325845000c76412e8b18a200c6f65dc9634405959d043a6c6908038b55142d89300053cc0042b2820008f4815d165040015cb0420cc228002b560c74984500246fc3ac7a9820008f787584615400156d08192c2280030f5d364d951001c5e422e3b2a4003c3e74550614c0031d904b9cc2280024f61075589300257540082b10a000c6f751c9654c0070ff0eaa6cb108063ba1f7258f500e51ec2ee2b20a000a3f855cb644400559906b1264280123ba1f624871004d3b42e62b08a000a5e851056304001c68e8aa4c2282bf17dd4635815247d2ec2ca8b182000a3f855cf64440014bb06326ca8823a1fa1c745941047537428a8b102009a5e85105631400159b0620ac42802787e115458c50005674328431a4212bc88348630480010fb0fa0aca080029ba1742d893104e1e32ae932a2000a5e85190634851fc6e80aa4c2280269da1743984500056741ce8b10a000a9f835cb6444001c76eab222008003275d163d44100146f41cec90aa000c3d74190654400147d0a392c8080030f5d241195100058ec20caa9a6009a3e851c564140018bee729aca082271799773548100056bc1ae5308a003c3c7455363c40014bf0ab1ea710253171cd5458b1047d3bc02a8b08a000ccc325ca61d4c134ed0a212c22800387e115458c1004d3b42886b08a028cce63dc931880018daa8b96cb18802a7a1265d8d210043ec26eab122000c6e65dc931040032d90ea9aa4900038755241d8d2104c3f4388432a2000a3d849d763884091b907bb262280038b5514258b100243f43ca4b282000ad5831d161140134e90aa0ac2280021f61f419941000666196ec9942000e2d54509629405959d04206c6908123e20174595310043fc2aeca92200087f8755363884011eb0e192c22800a3720c76549300063bba2c3288a08ec7510dd165040134ed0a214c228002ba600415885047f1d082eab202000e1f5495163040834bb0a3a6c6a9002b3a0a7458c5000667b98e4b1e2000a9e83dc964140014db04326ca880038ddd154984500054ec24ca31a4209a6c855c5621400787ce8aa6c099003330ca71d813200656326e4b1a2000a3d8414b65440134ed0a21cc2280129e20174594100046fc1ae430aa000a5d851d163
  | 13 => 0x557416e6b26a203c3c74d53654400147d0939eca880268fa1773593510051ec2ee4b20200387f87553658c401a9864bacc29924f331cd4258b100061eba2a8b10200087d879906544007878e8aa2cb1081237a1f4358c500051ec20eab1a408fc6d7255363480011e902ba2ca900031bdd4625813100666392c6a9c2000e1c64553635491d0fd0e2a2ca080063ba0b74d96310062e3aec6b024202a5e8359753040019b2c6b80a310002b660041d8d210247ac3c8330ca0008dc8758d21140130ff0faa6c710802cb610655492000666196ec990a0008f7815d16348009974c0ba0c1288121f21d655481000566c1686b18a0008be87d91624400147908b8eca880129d21951d41100043ec3aa9b1c4200c9c635d3514842d39904b98a298253179d954d8d2100566c1686b182000e1d54d0d63040015ad063a2c22800a37a0e76549100054ec1ee4b26a209a7685d05611411fc5e80aa2c4280029ba1474d89310d574c00e6b10a000c5f545cf658840187aea38ac8281331d5c1619445002759b8ac88802000c3f655d35144001c5f08aa2c518002b9608749845000666196e830a644ce3710592511400195ae8b16a3180125d21d51543100064f3a6c7a8a42008de87105631400156b02196c8880029ba144158a300045ec38a4b202009a3e8508164d449dae0e032aa2880023b60b735835100c7c432e028a4001acc8258d32140014db0b3a2c518003875514358e210052ec2e82b182003c3c745516348401c3aa8a1ac6280023be09764c4500b4e743ee4a9a6000a5e83d0865440011bf06ba2ca99003c355142d8d210052ec2e81b1aa400c3d7455162140130fd0bba6c7108030f5d15458c501ed36432a9b12a6038bc845c7654c0014bb0bb1ea6900034e1d075440100051ec28e6b202096cce7650f624c4011ef02ba2ca980021fe157654d1000c77416ed18ea000ad980085630400787ce8aa0c290003271cc645891055d73c12c230a64008ed87d0d6214001c3aa8a1ac6080038bd525458a30006c6192e832a643dace831d36254c015cb0420ac2280271d19671d411001e1f3a2a9b0aa60187e87d9552440134bd0a392c628002ae60032590500055ac2065308a000c3f74551654c00156b02192c8081330fd9574181510046f43ec6b0aa416bc8824c5308800187ae8aa6ca99003331cd6254a501466731ee49882000c6d54dc963d414fc9864aa6c099002a76107258c100053742886b102000a748155161140091e90eb0a42280127c20171d49100056741882b10a0008df835d16214413878eab2265a88030f5d154185200061eb86ebb222000e1d5450d639440199ee6392c6880030f5d15458e50005e9c1a428802039a3d85dc164d4401878e9b2ac688003330cb735835200536c1686b2820008dd87105631400717908bb26488
  | 14 => 0xe639d7638840787ce8aa2c70800a37e1d73d96210061e3a8e8b122000cad74d8b514c40159d07a12c4280030fd9574996310061fba2a8b1a2003c3e74553654c8014ed0d208ca880029b61443588500061fba2a9b1aa24ee3840500654400187ee8aa2c1188025da1c65547100061fba681b2a200087d8710b65440015990ca18c498a4b2d5c464195100052f42e87b1a4200c5c73d9562440010fd0fa16ca880021fe1d6519510006e439ee0a9240398bf865d351040014bd0a3a2c6080029b60b43d951044d2f42883b1aa403c3c7455261140071b90ea1ac628803339cd72d962144f0fc22a9b1aa400c6d54dc96314401d62c9a8a20080021fa1f65589100066639ee4b2a4000a7a86900654401387ce2b24a2282778bd0d5458a3001e1f3a2a8b14600087d8710d65040031dd0fb92c688016b960473588100066cb1ae11882000f324190365440010ff0eb28a3880063b2097458f100247643ac4990a08dab9809c564040011f70eb00c0908038bd5254d893104e3632ae428a4000a6d85d05628c0091dd0fa12c4280032d193715411044f0faa4a9b1aa400a5d851d1638800156b08192c2280038b55041d895304c3f438653282000c5c735955204001972c8b80a2080030f5d475d911000c76412e8b1ea000ccc7318521480014bb0a20ac6280030f5d154583510069dba281b2a20268dd86dcd210413bc5a86aa2c5181321fa1f41d951002476416ec90c60048ee87cc9628400559906b1264288123d61e61884500056d40083b1a4200caf74dc96344013878caba6a2988b27320973146310047dc3ac0302a600a6d859d162040014bb0b90ac62800e1f21d54597100071a32483b2a2097c6c7255163144130fd0fa00ca880728f614735905004c3e43ea8b1a200087f845d763884010ff0ab80c2990030fdd154589100045ec38a6b2020048ef8758b52040071b90ea1ac7108028fa1262195100052ec2882b182000af18110360544010fb0e194ca08002b360a7458c100061ebaee6b20a04e87f8759751840051b906ba2c5a80032bdd362581310071a3a2a8b08a000aae84994624c401c3aa8a12c6280b33398b73486300053742e82b10200987e87dd5624400159b053a2c6280270f99574d4630024f8402e3a9a20008df835d1624400717908bb2a4880030fdd573d911000672392c2988a00087e87195634401387ccaba6a208002ab61053588100064f31ae9a882000a5d85d0d63040014bb0ba0ac6280023b61c41588500056641aeab102000acd821036354807968e920ac328003331c9634c6500065cba2c0304a203c3e74d516504001c3aa8a12c60804a7320d721452044e2fb18eab026400e1d54d0d631400787ce8aa6c2a800297a177358e210052ec2ce8b18a000ccc625cf514c409976e2b2220080038d197649451000
  | 15 => 0xca9aa49000387dd154d8d520061e3a0cab12200093d849d6614c80147b09310ca88002abe0973d911000476c16ed18ea000c3f745536348401938e9b9ac48800317dd5634c4500043ec3e86b282000a6e85993624c4015ad02392c6080031b1c8654c5100045ec3ac9a8820008bd870c964040010fb0e190ca880269d21532584500062eaa6e6b2a4200cac74d89604c4091e90eb0a6228002a7a0f72590100b666392c6a9c4000a9d841c96314001998e7b12a4a80123b21d624c81004e9db02e9a8aa0118de87185314c16b4db0b320c4a98031718c7558d200061fb2ae932e2000e1d5450f63548374bb0a392c6280028f211651951004e9b30ae9a8ca200c3f7519162440354db0a3a2c4280063b2097654c100064e39ac890820048ee86dc9534800187ecaba4ca988030f5d074d95100061eba68032a2000ad5811c9631400159f06baac40800237e0d761452000717c22a9b126203c3c74553624c401a98e632aa4900028f614305935146637b96a8b2a6400a3d849cf654409d0f90ea8ac0288030fdd154587520146e41ae430aa000a3e840c865440011f70eb00c110802b560f429845000716aa284b146000ccc325d93294001c3aa9a06c6908038e60064195100071aaa482b0c4000c5f54dcd624400193ee839ac488002b560f42584500047743881b126200ccc72d8d535440155b0839ac4280038b60864d95100056b40881b1a420087d8710765440e759d04320c690a838750954d8d2101e1e3a2a9b026209a3c859c564140091e90ea0ac3280030fd95749962100536c2882b146000c3d74553604c8138f4ec32e2088226b360874d8d524c636396a8b1a20008ee87107624c4010ff0eb28ca98803cc50540d951004c77c32e5a9c42048f487505618800159906b8ac4280022fe1171d95300046fc1aec992204ca7486507654402539906b96a0900029ba1441d8931275b8402a228a2000a6d82d0e65040018bee729acb108034e5d1401951000666396c698e2000c5d54dcd654800147d0c3aec8880030fdd15458f520070f3a2a8b1c40048ec87589520400199864b80c299002b360c40d89530052ec28c831a420093d849d763884014b906b28ca900261fa1c419941039e673b285b1a421ca3d851c964140011dd0e206c4a980237a1c40d8d520043f43882b2820008ed87d0d620400159f04a1ac7a923b8e84275590104fe37b92a8b1a42028de83dd3658852b8bce7aa6cb108028fa1663d91100061f3b0ebb222000a6e8210465440090f90eaa2ca0800317dce73594100064f31ae9a8c4048ab6811d7644412f8dcecaa6c4a98038b55140d895301c6fc3a87b1a4000a9e841d563880010fb0e320ca88002b920973584500062e32ee690a2000a6e85193624c55d8bee6aa2ca99003330c8764c9100246f43c64b182000c5
  | 16 => 0x2d812104d3b42e84b08a0898df835d932d4013878caba4cb8800f0f9d154d89300070eaa286b1ea4018ee87dc9654c0257910690a60902329ba1440d895347e3a882e8b282098c6c72d51654c0011bd0fb1ac0908261f215701853200758b22628802000c9e7458f510407f1d90db92c0a98030fdd1549862000758b24428802000aad849d7624c4018f2a9bb220080030f5d15458a300056dc32a698440028dc835ca611400199ee6b12422800f0f1d15458a310146e41ae8b162000c3d74d516504007878e8aa2c3280123d21971d491000573408e6b10a03dace831036254c0157100b8ac9a88021fa1c41d95100061fba2a830aa0aee1d4255363548091b90eb1aa60822717d537358b500043e43aa8b122000acf825c563140011df0eb20c4988032b1c96454c100070eaa482b18a000e386490365441318d8e5aa2c7880030f5d15458a5000477c12e8b1a200087f855d93244001c9864b2a64080031bdd5624845000578c008230aa000a5d85d0f635482539906baa429023f8b501545885000636310eab126000acd83d0962040011bf06bb243a82631b9cb54d963104d3b42e85308a00087d859d932c411fc7100baac8080038b55142d89314ff16a1aa9b12620487c875516588025998e6b12a5180023b61c40d89531fd3742ce9b12a600e2c745536254c014dd0ba06c4988063be1d72d96310070eaa482b182016b4c8254f524c001c9865baac6900022f61c53d91100146f43ee6b16a000c5d7394f6544001c5aa9a12c4280063ba1f7258f1002c7643ac498820028dc835d952c400155d0829ac4080268fa14735935100666b98e6b10a0008be870c964d4547d886538ec7108032b993724c4500053741686b282000c6d54dc963c400147b08392ca080038de0575590100066a39ac2908a04cc7476d955144001c58c8aa0c4988030f61974d46510056ac0881b1aa400a5d85d0763548011db0f328c4988029b61664d89314cf1a080c832a2000c3f7455161880014db0a39ac4080030f9d165d441000786aa287b126200c5c73d9552440011df04ba2c69080f0f1d15458d100070ec18c9b2a20028de87dcd62144011dd0eb1262280021f61f54d8e2100636aa6e4b1a2088ccf761cd524800193ac9b9a4228003351ce614845044d2f42e81b1aa400e2d545096244001c5aa820ac4280032b1d37258d1000674b12e02882000cb4649da51441198dec53acc2990031ee0174594100051f430cbb222000a74815d1650413fc5e86aa6c4988038ddd154584500070eaa687b1aa428cce63dc9311400155b0438ac82800f0f1d154d8b100064e39ec890a2009c7475585311402d7910498a6090003875514358e1000716aa685b12a6018ec825d953c400187ee8aa6c4a80028f61053d95200070eba2a8b1c4000a76810c965040014d90
  | 17 => 0x2a2000c3e74d9751440014ed02194ca080038b9d154588500061eb2ae832a6000cae7458b518c00187ae8aa6ca988030f9d365995100052f41ee5b2a20018ee829c76054c1347d0b98ac82800f0f9d154d953000c76412ec98ea000ab88458060544011bd0eb1a4208283930c954d8e210071ac08cbb2220008df835ca611407347b0bb9ac9a88028f61263d95100061eba2a930ea4008bf845d921940011df04bb263a80030fdd774589100146e41ae8b2a4200c3d7450d650408399cc5b9aa4080029ba1742588100061fba281b2a2002acc83589320400717908bb263280028f610321951054f26192a830a6400a5d8310565040019cee4b0a62280029ba0864d95101466639ec4a9262b6a6d859d36254c01878ea322c4880022fa1c32590100061fc3aeab20200987e87dd5634412b8b8e7aa2ca908030fdd342d95100055bc0ae0b26a2169cc825d5314c007878e8aa6c6a8a3e976165458e200246e432ea98a60028dc835d9211400157700b8ac9a88029e60041594100061eba2a9b2a40028dc835ca61940093e50fb82a2880031d9db659451000716aa482b1460008ef825d9534800187eeab226428003275d163d462046566c18e9b12a600a76810cb65441654bb0b3a6c6a90023ee1d601813100657b26e498a20008ee87d0d62140051bd0fb9aca90803175d475d8d215862eba8c730aa400a5e859d363485194dd0ba0ec4a9a2393d8f541895300c77416e6b06a200c9f64dcd524400159d05a1ac6280129ea00325941000673b94c2988a03da6d851d36254c014bd0a20ac710002a7a126518d2100567c12e2b1c40008ef825d953440014bd06320ca8800387e115458e200047dc02e8b2a6200e1f5495163880014bb0ba12c6080023ba1c625815350727b1aa831262008bd8799764440014bb0ba12c628003171d77358d200061fbaee7b222000a3e859cb644400187ee8aa2cb1005a7320973d413004e3a3b6eaa8a2000e1d74551631400159b05320c6a90030fd9574d471000716aa284b16a609a3e85dc964140011e902ba2ca980269da1673584500045ec3864b26a2008f4815d16348001998e6b12420823e1f61e74594100064eb26e6a902009a6f845516214001958e4b22622800317dd463581210046f438c6b02a400a6d85107624c4010fb0bba6c71080333dcc72595310070eaa287b0a60008ed829d931540014db043a6ca880030fdd46458d1000476c36e4988a000b7180d9551c400787ce8aa2c6900029b60841195100061fbaac8908a000cac72d91534400199865ba2c6900021fe157654d2000c3e42aeda922000c3f85dd1624400159d05a1ac6080029b61741d89310052ec2883b1aa40087e87d0365440c787d0eb24a2280032b593724c4100069dbaee1b222009c3e655d0654c0051b906bb2a5080038b5514
  | 18 => 0xe0000022860060260100ba02a01c00001800029402a00000000e12800008a03800600c08a0060300c208400001e03001600410411a0006c268c00600036203e07a0323180102560d403c00801800a00022e00000000401601a2b802605828002201803200802a27402400a00004407405000801a01c01a0000ae00408e00e01c02800c00400c0040040607223860620e000406400c00c0040260020a210c0b203a00e0de01400800002804002204200600603c0620040080000120ce01400e0000122ec04205400000f0d54508634852f8d8e4aa2c7a800f0f1d3545825100636b2ee4a982000acd831d3624c413878caba4ca908269da1474984500052ec2e86b1c4000acd82d0d63880010ff09bb2a228a8387d0954d8d210256d40042b182000a3d8508164d445959d0420ec6908022fe1176d49100146e41eeca902000e1d54d0d638800159b07320c498803175537358851014ae43aa6a926000c3f745536354001a98653aec5188030f5d14259410006a6190eab1a4091ab7815d5640402d79104a9a6110003d254d524c1200052ec2e82b1c4000ccf7358952040015b30020ac6280022fa1c6458d100061eba28032a20008dd86dcd520400187ee8aa6c6880030f5d1549875301e1e3a2a9b122000c3d745536154c01c3aa8a06c6908030f61c64195100071caa280b046200e358119365440070ff0eaa6ca988029ba0b439941000637aa6e4b2a6028ccc63dc9314840187ee8aa6c4880269da1474584500065dbb6e88802000a5e8310565040014dd0ba0ec49880e1fe1d54d95300061eba68432a2000e1d5450d63880091d90cbaa42900030fdd154d8e2101e1e3a2a8b0c4009a5e85c856314001c3ec8aa6c6a9003930cb654c91000657b26e4b1a2009c3c655d351c40010fb0e208ca880029b61440d89530046ec1ceca9c428fe37105d56404001998e7b92ca908029d60432195100b5e24126310a6003c3e7455162940014bd0a392c6080030fa1c75d911004c3f42eec992207ea3f855c564d440187ee8aa2c71080237a1c41d8d2101e1e3a2a8b2a6200a9d841d5630402579106a9460900269ba1473588502d667398c4302a600a798094f6548001c3aa820ec690802b360e74588100061eba686b282009a6e85cc562140015ab02206c6908030fdd154d893104d3742886b10a000cac7219163440014db0ba12c5180029ba0b43d95100253d40082b282000a5f8558f538840187ae8208ca880030fd9574d45210047b43865308a004a7486545504400187eebb96c8880028fa1c75d9110006a6190eab026400c6c75189604c4838b8edb1aa6a9003331cb634c5102653d406a2b04a204a7a80085650404d1bb0e20ec690a53171cd54589100056cc0082b182000c6f75589321400187ee8aa2c7a8003331cb6354d500051f424c63
  | 19 => 0x19401e0062040c00240740460000340260000081f205480000400000000604200403204802400002201200201e00a0020020a400200603200001000001a00647401007406a00e00403e00000006a0143580100540000aa0021fa00229000e03224c00205e04805a00200400004a00600c00400c00000202e1ba05a03c0100bc0ca00208a13803c0e60ca00e002002000056052000016b1e00a00803e04c01003012a00005004800000a0005d200001294000e0140a2012006000036e180100ce00205401002602001e00c00000403c00a00009405209804026e08002601e002000000068036a2411c12007e00600200412e00006a00000001400000006a00600c19c22001202207c00807a00213e00800000001400403000033e00011a0000020000020084b006000800600a05204e01c00610406c02000600400000e0d40740900f400404a00e24a02a09c0086ec03a00208600201600603804e18606206000e00600c08000200601006400433c05425009803c00600002600006aea00182120080020020320100023ae0040020d20020080d00020e000e00601600002a0f60da0a600600200201001e00a00601202206401607605200003850000204602800601200007000000e2082240fe02e00401001800201e01481206601e00c0f402403a1a210000000410c0b000000804a03804200a00400000021804a00002603c1661fe01224400001600200606400405809206a75001800009416641205e02e05e0080000320000180340002ae000000a660020760000c00340180100000000f201e00000a01400600002600200403602000200203800006a00849a05403801a0260100003a400001404245c02606a25600000002421000006e02400003204e02c12c32e10a05a0022161a60020d607206200607200003802461000802805e03a01e00000601400001804a01800400200007000007a008002054000dac00048023800001a00000e00600803a13e04003004e00002602a04c07c04600a00002600200000a1ea00407000408200000000202a0000040080240b400403a02802e0002520a408200003a00002a00200007c00000c1f600c0000061fc0f200025a0440280300000129de02400254800200801200201008e02400000208000400000000a0760ea00e0003020e800000000000000200220610e00004e04600000005000e04c0420040120840f80060640022b82760a812803015c17808c0620423cc07c0082e405c03c64a0200040141bc00001402e36801601c00600003c01c00800811436200802a014dbc05201200400600600204a00065800057600400002409000203601e1a405401600200600600c05000000e0060d405e01603600a14800402c0ce00e02000a00204401c27a00204203897001809405e8340f208000202601
  | 20 => 0x3a06a03c12c01201c0420200180040a40f202e01c0520140101f200603602c05800200003201200e05c0008d600833e01606200c0303e22d60c809e21401e00e02400a07207400202a19c00a00624e06402a00218200000e00a002
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc01a195460041d8d520050ba4b655d2658c40187080205745941044433a63635cb534800181d7460f42594100041d65c81500654411341f9359574195320050e640715d5640411184c850c9701853200643610321d5624c02d3c0984c5214c1200058364e74551628c0018b1815c070593510058364e74551621400124d980c8654c91001e0b21d54509628c40182d8755041588500048765285dcd6388401a0e865514218d210060b5d182d0d650411144c955c87258c505c7031cd5450962c400190d840ca75d8e21006835538350962d4c0181d8418c7558d2000683a195450c624c40181e8755041d8d21447031d432591321400142c9259574195300060b61d54105620416fa3381e0175590100060b5d582dcd64d451184e850ca764cb1000686551801056304001a295460041d895300507a4f655d2658840182d8418875589300060b5d582dcd640411184c850c97458d20006130c8875516348001a3141600411951044613a14325d3638851184e831d77258d200050b65075dc96348001a0d840c87558d2000685551831066114001c0c32dd154d8e210068355182d0d6304001a2554608419845000683551821056388001a0d5460f42588100050764e71dd76444001615931d154584502664cdd5841c15144001a295460041588100050b648715d5640401303c985d15458d200064361073195524800182f75e0973d91100060e61d80190654400142d929db75d91100060761d83190654400182d7460b4399410006075d183d0a650400181d875534258c500060e5d1801066504001836861c775d91100068c551801046154001a155460c41584500050765075dcd6348001a0d5460f4258a300060b61d54d0d6204001a0d546084158c5000513a5c32dd5634800181d7560f725935101e0e21d545016088401a0d5460f42588500058364c74553624c401a0d8360864195100068c605801906544001625921d154584500060761d54d096304001a315460041d855044613214325d93284001a0d5460c41d89310068a55180105628c0014399719140195104660bd89841d5604c80781c875514358e2101e0721d5450d63c400181d7460c411951001e0b21d54509624400181f75e0d72d91100050b64a71dd76444001a255460841584504660bd89849d6614c80182d74608641951000683219545086348571c0c73551425891000643610321d5604c80144d970c975d8e2144513255731cd621411184e850ca71d8132006075d583dc96414001a0d54e094358f52006075d1831056504001434915d15458d202758c259415006544001a29546004158850446131ca85dcd638840190d840ca75985320058364e74551620400143a96dd770d9110006310c8815d1634800781f8755143d8d2000589648745526114173c0c725514358d10
  | 1 => 0x2e480808088c0c042c0c0400083802783430004c000004881030017400007c0404ac0c6800142c0400000c0804205c8860010c3c00ec0000001000fc04041ecc0000f0000034182d000c141000400c0a9408000014e8000038040400144a045000000c081303e98dd154d8e210058c64074551611400142d949d572d8e2100583648745536348573c0c725514358f100060761d541056314111c0e650c9741953200607612639d76388401a0d5460841d8d210060b5d182104654400782c875514258b1000683610329d76388401a308020575590100b4d2261535493048001a255460b43584500068355182107635480182d756087159050006075d1831906544001a0d5460c41d895300607a1d541076354911644954c832584505cf039d95450f624c40181d875504158e200064361072195534c001615931d154984504cf0c1c064195514400160d929d15458c500060e5d1801046544173c0c725514358c510068360d82193654400182d7460841594100068c60580193654400182d7560b73590500060ba1d54107624c51360d921d154d8d52004ac66164d451004001c0c325d154d81324650be49655d0654c801a155460f42984500068355183105620400182d7460b4319510006075d1831066504001631901d154984500068555183d096114001838871d5644401000643610321d5634800160d929d15458c105c7031cd54509621440160d929d15458e200068655180105638800181f7460f42d95100050764e76dd7644411381f6361075581320050e64271dd76444001a0d546084158c100068955182d0e6114001c0c325d15458d20006a8593824c5100400182d87608641951000643610329d7628c401c0c325d15418532006a459383485100411381f636127598532006075d5831c5641400181d875504158c100060bdd182d0f6544111c0c750c9644cb515d58ca5a4190065440014389761564440100068c61681591100400184c32e1d54d8e210068a55180107624c40141c9359574195200068655180107634840782f8755142d89300060b612629d7628c401a328690640195100068355182d0d6388007839805d471590500068355183105628c00781c875514358d102750e25d54501601451184c850cb7458d20006075d183d0865440078388755140582310050764c715d564041110ce97e094358f520060b61d54105628c00182e8755041d89530060b5d1821066504001a0d5460b4358c50006075d583dc96404001a0d5460c415885044433261635cb5388401a19546004158c5044613a1432dd36388401a0c8655143189310060b61d54d0d6214153c0e7655142d8d214658364c745536254
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x43088c03a0d941d77258d200050614ec2d02b22200822300e975538250d63d4801a0219122ba2a8b1a4088c031c994a177358e21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4d
  | 8 => 0x138d
  | 9 => 0x6
  | 10 => 0x94b
  | 11 => 0x94c
  | 12 => 0x94d
  | 13 => 0x124d
  | 14 => 0x124b
  | 15 => 0x124c
  | 16 => 0x138b
  | 17 => 0x138c
  | 18 => 0x98c
  | 19 => 0x98d
  | 20 => 0x128c
  | 21 => 0x128d
  | 22 => 0x9cb
  | 23 => 0x9cd
  | 24 => 0x12cb
  | 25 => 0x12cd
  | 26 => 0x14b
  | 27 => 0x14c
  | 28 => 0x14d
  | 29 => 0xa4b
  | 30 => 0xa4c
  | 31 => 0xa4d
  | 32 => 0x134b
  | 33 => 0x134c
  | 34 => 0x134d
  | 35 => 0x198b
  | 36 => 0x198c
  | 37 => 0x198d
  | 38 => 0xb0c
  | 39 => 0xb0d
  | 40 => 0x140c
  | 41 => 0x140d
  | 42 => 0xb4b
  | 43 => 0xb4d
  | 44 => 0x144b
  | 45 => 0x144d
  | 46 => 0x2cb
  | 47 => 0x2cc
  | 48 => 0x2cd
  | 49 => 0x14cd
  | 50 => 0xbcb
  | 51 => 0xbcc
  | 52 => 0xbcd
  | 53 => 0x14cb
  | 54 => 0x14cc
  | 55 => 0x19cb
  | 56 => 0x19cc
  | 57 => 0x19cd
  | 58 => 0xccd
  | 59 => 0xd4c
  | 60 => 0xd4d
  | 61 => 0x1a0c
  | 62 => 0x1a0d
  | 63 => 0xecb
  | 64 => 0xecd
  | 65 => 0x1a4b
  | 66 => 0x1a4d
  | 67 => 0x94055
  | 68 => 0x95395
  | 69 => 0xbd395
  | 70 => 0x14d395
  | 71 => 0x138955
  | 72 => 0x954d5
  | 73 => 0xbc955
  | 74 => 0x94bd5
  | 75 => 0x14c955
  | 76 => 0x14c9
  | 77 => 0x1489
  | 78 => 0x2c9
  | 79 => 0x139255
  | 80 => 0x125395
  | 81 => 0x138bd5
  | 82 => 0x1394d5
  | 83 => 0x9c995
  | 84 => 0x12c995
  | 85 => 0xcb
  | 86 => 0xb0995
  | 87 => 0x98b15
  | 88 => 0xd4995
  | 89 => 0x98d55
  | 90 => 0x168b
  | 91 => 0x9d295
  | 92 => 0x8c
  | 93 => 0xb49d5
  | 94 => 0x9cb55
  | 95 => 0x150c
  | 96 => 0xec9d5
  | 97 => 0x9ced5
  | 98 => 0x14c155
  | 99 => 0x154d5
  | 100 => 0xbca55
  | 101 => 0xa4bd5
  | 102 => 0x19ca55
  | 103 => 0xa59d5
  | 104 => 0x2d355
  | 105 => 0x1342d5
  | 106 => 0x14d355
  | 107 => 0x1354d5
  | 108 => 0xbd995
  | 109 => 0x198bd5
  | 110 => 0x140b15
  | 111 => 0xb1415
  | 112 => 0xb4b15
  | 113 => 0x144b15
  | 114 => 0x154c
  | 115 => 0x24b
  | 116 => 0x16cb
  | 117 => 0xb5415
  | 118 => 0x20c
  | 119 => 0x145415
  | 120 => 0x144b55
  | 121 => 0xb5455
  | 122 => 0xbc2d5
  | 123 => 0xbd4d5
  | 124 => 0x2cbd5
  | 125 => 0x14cbd5
  | 126 => 0x19d4d5
  | 127 => 0x14d9d5
  | 128 => 0x5cb
  | 129 => 0x44c
  | 130 => 0x17cb
  | 131 => 0x164c
  | 132 => 0xecd55
  | 133 => 0xd4ed5
  | 134 => 0x1a4d55
  | 135 => 0xd5a55
  | 136 => 0x3ce
  | 137 => 0x15ce
  | 138 => 0xeda15
  | 139 => 0x1a0ed5
  | 140 => 0x170e
  | 141 => 0x4955
  | 142 => 0x1a89
  | 143 => 0x1049
  | 144 => 0x5995
  | 145 => 0x59d5
  | 146 => 0x289
  | 147 => 0xd0c
  | 148 => 0x104c
  | 149 => 0x1a8c
  | 150 => 0xe8b
  | 151 => 0x104b
  | 152 => 0x1a8b
  | 153 => 0x282d1
  | 154 => 0x1689d3
  | 155 => 0x1049d3
  | 156 => 0x1a89d3
  | 157 => 0x104994
  | 158 => 0x15395
  | 159 => 0x105414
  | 160 => 0x105453
  | 161 => 0x1a9414
  | 162 => 0x1a9453
  | 163 => 0x25453
  | 164 => 0x178b
  | 165 => 0x19c055
  | 166 => 0x150994
  | 167 => 0x105693
  | 168 => 0x1a9693
  | 169 => 0x104253
  | 170 => 0x1a8253
  | 171 => 0x21414
  | 172 => 0x1a57d3
  | 173 => 0x105a14
  | 174 => 0x105a53
  | 175 => 0x5d353
  | 176 => 0x5cbd3
  | 177 => 0x5d053
  | 178 => 0x1a5053
  | 179 => 0x45354
  | 180 => 0x44bd4
  | 181 => 0x45054
  | 182 => 0x1a1054
  | 183 => 0x198059dd
  | 184 => 0x104d14
  | 185 => 0x104e93
  | 186 => 0x2c291
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2191
  | 6 => 5517
  | 5 => 2611
  | 4 => 217
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/27+packedAt gbK8 (1612+(h % 27)*6) 6) % 62)
  | 7 => 2*((h/779+packedAt gbK7 (81067+(h % 779)*12) 12) % 2191)
  | 6 => 2*((h/1839+packedAt gbK6 (264816+(h % 1839)*13) 13) % 5517)
  | 5 => 2*((h/877+packedAt gbK5 (154049+(h % 877)*12) 12) % 2611)
  | 4 => 2*((h/100+packedAt gbK4 (15190+(h % 100)*8) 8) % 217)
  | 3 => 2*((h/8+packedAt gbK3 (405+(h % 8)*3) 3) % 5)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3fff0f070fe1fc07fe3803ffc520c7c33333f
  | 1 => 0xfc380f007f0fe1ff81fc003ffcac7390cccc3f
  | 2 => 0xffc00fff800ffe0001ffffc7033183e30f0fcc
  | 3 => 0xffffff0000001fffff803c1fc03f00ff0
  | 4 => 0xffffffffffffe00000003fe0003fff000
  | 5 => 0xfffff000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40486030101202400ca0828928000424111315
  | 1 => 0x841083002104209301440512d0043190444c2a
  | 2 => 0xea812554800f540514692984193082e10f054c
  | 3 => 0x24aa97aa0000a2992562062c15c02f00ab0
  | 4 => 0x22040cce4cc9992c7000180003fa0003aaa000
  | 5 => 0x3327800c088110304000600083ffeb58000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36344
namespace PEqualNP.Outside.L_meta_36344
open PEqualNP.Outside.L_meta_36344.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 2 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 6 := bs0_4_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := bs2_5_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 22 := bs4_3_0
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
theorem bs4_4_288 : Interval s4Atlas 4 288 91 := block_range (n:=91) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 379 := (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 586 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 7 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 5 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 217 := (concat bgb_4_0 (concat bgb_4_96 bgb_4_192))
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
theorem bgb_5_2592 : Interval gbAtlas 5 2592 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2611 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)) (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 bgb_5_1248)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)) (concat (concat bgb_5_1632 bgb_5_1728) (concat bgb_5_1824 bgb_5_1920))) (concat (concat bgb_5_2016 (concat bgb_5_2112 bgb_5_2208)) (concat (concat bgb_5_2304 bgb_5_2400) (concat bgb_5_2496 bgb_5_2592)))))
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
theorem bgb_6_5472 : Interval gbAtlas 6 5472 45 := block_range (n:=45) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5517 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)) (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 bgb_6_1248)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536)) (concat (concat bgb_6_1632 bgb_6_1728) (concat bgb_6_1824 bgb_6_1920))) (concat (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304)) (concat (concat bgb_6_2400 bgb_6_2496) (concat bgb_6_2592 bgb_6_2688))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976)) (concat (concat bgb_6_3072 bgb_6_3168) (concat bgb_6_3264 bgb_6_3360))) (concat (concat bgb_6_3456 (concat bgb_6_3552 bgb_6_3648)) (concat (concat bgb_6_3744 bgb_6_3840) (concat bgb_6_3936 bgb_6_4032)))) (concat (concat (concat bgb_6_4128 (concat bgb_6_4224 bgb_6_4320)) (concat (concat bgb_6_4416 bgb_6_4512) (concat bgb_6_4608 bgb_6_4704))) (concat (concat (concat bgb_6_4800 bgb_6_4896) (concat bgb_6_4992 bgb_6_5088)) (concat (concat bgb_6_5184 bgb_6_5280) (concat bgb_6_5376 bgb_6_5472))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 79 := block_range (n:=79) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2191 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248)) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536))) (concat (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)) (concat bgb_7_1920 (concat bgb_7_2016 bgb_7_2112)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 34, 42),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 34, 38),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888feeefeeafeeef888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36344.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[1,4]⟩,⟨.and,[1,6]⟩,⟨.or,[0,8]⟩,⟨.and,[2,3]⟩,⟨.and,[5,9]⟩,⟨.or,[1,4]⟩,⟨.and,[0,12]⟩,⟨.or,[7,10]⟩,⟨.or,[11,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36344

open PEqualNP.Outside.L_meta_36344 in
theorem PEqualNP.Outside.L_meta_36344 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
