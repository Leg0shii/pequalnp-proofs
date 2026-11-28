import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36356.Model
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


end PEqualNP.Outside.L_meta_36356.Model

namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
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

def SBf (j : Nat) : Nat := [6, 6, 6, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36356

namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x180120a85be43bc43bf42bd42df32dd32
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x825aa421e350932
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
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (102+((h/2+packedAt s0K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s0K3 (56+((h/1+packedAt s0K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffc0ffffc1fc1ffc1ff07fc3ffc0fd8f33f3
  | 2 => 0xfc0fff03fffe0fe0ffe0ff83fc3fff02f1ccfc
  | 3 => 0xfffffffc1fffffff0000ffffffc3ffff01ff1f
  | 4 => 0xfffffe0000fffffff0003fffc0003fe0fe0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x48644628849284052d093424c0664258871171
  | 2 => 0x19248a19091094a0552854a1442a9608b144b4
  | 3 => 0x208910405221094a0210894a2a8128a300aa0a
  | 4 => 0xb2ca249243a52a739a520843b3100c335a0fc0
  | 5 => 0xc30c38e39c39cf9ce39cee70222230c3edf000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36356
namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x92180280df43dc43bf42bd42df32dd32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x829aa421e350932
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s1K4 (102+((h/2+packedAt s1K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s1K3 (56+((h/1+packedAt s1K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x81fffe07ffc1fc1ffc1ff0fff07fc0fd8e7e73
  | 2 => 0xfe07fff81ffe0fe0ffe0ff0fff83ff02f19f9c
  | 3 => 0xfff83fffffffffff0000fff0ffffffff01e3ff
  | 4 => 0x3fffe0000fffffff0000fffc0003fe03e0
  | 5 => 0xffffc00000000fffffffffff00000003fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa4308231448a44052c85301534264258862e31
  | 2 => 0xc910450c90854a054a4510654a29608b09694
  | 3 => 0x104228821221094a02108aa0894928a301414a
  | 4 => 0x5965b12483ad6e739ad60884ee720c33da03e0
  | 5 => 0x618621c71c318b9ce318ecc8084030c36df800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafafaa0fa00fa00fafafaa0fa00fa00fafafaa0fa00fa00fafafaa0fa00fa00fafafaa0fa00fa00fafafaa0fa00fa00fafafaa0fa00fa00fafafaa0fa00fa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36356
namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x120e6004a32000017df43be43bc43dc439c43bf42bd42df32dd32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x23802030089400aa1800351e5390e5aa421d354843c7290871d5210f1aa421c3548438e29a851c54cca38a8996350932
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20c6550932
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 11
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (156+((h/3+packedAt s2K4 (144+(h % 3)*4) 4) % 12)*5) 5
  | 3 => packedAt s2K3 (309+((h/3+packedAt s2K3 (297+(h % 3)*4) 4) % 15)*5) 5
  | 2 => packedAt s2K2 (39+((h/1+packedAt s2K2 (38+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe0fffe0ffff87f83ff0fe1ff87fe0ffd1cf3cf
  | 1 => 0xff07fff07fff87fc1ff0fe1ff87ff07ee33cf3
  | 3 => 0xfff83fff83fff8ffe000ffe3ff8fff8303cf3c
  | 4 => 0x3ffffc0000ffffff0003fff00003fc0fc0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2810822210908000a5012024809205280c5145
  | 1 => 0x42410441212008140a1042090824a050612492
  | 3 => 0x842228840a4441a94088954255094a03028a28
  | 4 => 0x16b5b129487552ce73aa1103e640631bb40fc0
  | 5 => 0x18c621ce738664f39cccf99044018c63dbf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee88ee88ee88eeeeee88ee88ee88eeeeee88ee88ee88eeeeee88ee88ee88eeeeee88ee88ee88eeeeee88ee88ee88eeeeee88ee88ee88eeeeee88ee88ee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36356
namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21bea98437c53086fca410fbd0821f6210437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5205f94640bea8c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea90817e51102faa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3be86987710d30bfa9261ef524c2dea4985f14930f6292616c524c3be6498774c930bfa8a61f7514c2eea2985f14530fa28a6174514c3be6298774c530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483de84907b10920f719241ed32482fea2905f14520f790a41ed21483f460907e4c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bcc820f6190417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dcc410fa188217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a177d4d42afa9a857c5350bb8a6a15714d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf28885f65110aeca2215f54442faa8885755110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c63df438c7b88718df94a31f7294636e528c6faa518fb54a31b6a94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863df430c7b88618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f6214437e51887ec8310fd50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487de6490fb0c921fb20a43f541487ee4290fb88521bfa8
  | 2 => 0x773521d8001a222648d138000000000c8000007c4541020004909b00031e2cd1da482766e8f98002ca948272662a6000331f00e2190ee00000002800000000000110b40002b06f0d21b61a8001683d60005100000025c00933000000668000001cc0015e1961f0989de000338000001f00000000000092ce88e1254000728391285b91c08246e41507135334928e480e2e62207320b2f863455a5a17a3c80000b000000eb1d93e459c1ba453c62a4000e21f6330000003425bc00000000704001ce426094e987b1785d9158063be33c0005c23c8344994125e0b0d208c1e6540192240007a00000000070c8880042c8fc680000000010f0c12da3c4cf22200098c00147338114000002427984e92c184000ff0000005ec768000008f0be800000000cc8000000008c95c00041cfd9a80aa1f8f000010c918000d5272200001d20000006509e3127200b9ed4600011f15a0123a4000000005d0fa0000000000005b0001400010b0200000894e2c417cff9164b03ac068f7438000000bf36647400164320574000002880012184843e0680010a0003d0fc0c443465c642612a27f4d600000080400000000000ac0003ce6c1039c7000000c5800274608b59bf0a47e933a5b41e978001932568f40007845e1dc0015b0fe010000000005d40023a15e788b189c2ac37c000002986211419428a7a42309f0003fc0005e38c000000000da3640a88a0009107e1420000005c03832408c358b2148000bc94b370990000b10000000b20420269cb49180540c5029e44921447824c000000000000000008b8b60807a8db0421b000c238874b8520001b121c2840000007a000002620009648d130000488000000002dc13000000084aa9ca000000000004580a40004a000840409e121a5f8000002f449cc21a50b01352781f1dc4d101000000000001960686f0002260006c8000000003192a10811a000002342081b80e0000107d8d522e4284fc001ab3ea0005d9000a69007d1ec2e42b52b8561c0000892530ea6bcb000900801018010080000800004000040f000040140401412000010040300400014110000100800030000000000003024020000602c0b05004018100080b0000400c030000400c0500000010000200000c01008010000d00000000010440c024020400400400004000000400007000000580000000008040100100c0001c06010000040300c220000005c040000000c040000100002008000040400002008000000000c1200000004010040b0000102400020070500201000000000080000007004070200000c090040100404018000000e0040000c0004c000040501800014000000102c0700c00024060080600c0000c02008000680005003000000200101405bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x2fe6f8d00000d800037800464000000da42e000000000004dc000003148d46b80028c4545383c40068c0000009240ccd80211e7bc4d8e73b0000000002526548a12d3aa47c518001fa614000c541091c000000003d400000000090002330002551685a38443c001fc000014002423ee00000211120000e60003ba00026074154000000000004f47780047276c000000000000f1b5028000c3830418244da0e30c218819a4d17c224002182cc418c60c70e40000d80730620c00000452000000ea3720000014f000000c09590244252fa5524c0000000007c000380432947e4e803f10a000b884f376000001d412c1743ca603ae30c5816a00000094219000000b80002a48249e0001f20000009939a7941002f37a0005011c050700529c53228842a044000370000004a20d90300031c828a48c935c299018ec1a8074881a606a768000690008941d8c04a050cf7000000000000590002e41383a1c8584158b52800010e9544ba57c209b712422c7f26515c8a847013000210e58f64629383196c000374000671a64e1101ad1d0480e78000c00010d8000ae46c0009a000000078000004b800000000000000000000300007d48212d1b1251a20b4000984468480019800006086000000674a680033e000000000000000013e300958328ba05c710990d62ae1a10a80030c5e03d1
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x5415026f6254c409b189531023f65500409ed95401026f62553309b18954cc29c644cb308f99251cc23d64947309b98a51cc26d62947309b98b548c26d62d5230c758f544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c25e65d0d30b6983434c31f5410d30cbd53524c32c54d4930cbd50524c32c5414930d3d0c524c34c4314930da580524c34c52cc930a7191324c33754d4530cd153514c36752d4530d914b514c3375414530cd150514c3675214530d9148514c3574314530d510c514c35451cc530b6181314c25e63d50309b98b540c26d62d50309b988540c26d62150309d984540c2756115030d354b300c369528c03097d95300c34d524c0309ed95300c369524c03097d8d54c825c63553209d98454c827561153208f99353c823d64d4f209d98753c827561d4f20cb55042c82e56110b20ab19132c825e63d52209758f548823e64d4e208f59353882e9600ca20ba18930883cb324c22097d8d544825c63551209dd85544827461551208fd91534823c6454d209bd8953482776154d209d185534826e65d0920b9584424826e658c9209b19532482ac644c9208f990514823d6414520d914521482e860485209e19530483c9324c1209798f540825d63d50209b98b540825e63150209758c540827661150209d584540825d6594c208fd91530823c6454c20c7d91530831c6454c20d3189530825e6314c209b988530827a6014c209b597320834d53cc8209b594320834d530c820ba580320834d53c8020d654e200826f6548020d354d200827b6548020d654d200825f63553109718d54c426f62553109b18954c426e62153109b58854c423e64d4f108f59353c426e62d4f109b58b53c423e6414b108f59052c425e63d52109758f548426e62d52109b58b548423f6454e108f191538426f6254e109b189538426e6214e109b588538425e6314a109758c528425f63551109718d544426f62551109b189544427b60551108fd91534423c6454d109bd89534426c6254d109dd85534423f64549108f191524425f63549109718d524425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043546154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520435553cc4109d594310433954d00109e594400427965840109dd95100427b6544010
  | 1 => 0x2408380c2c0803c0a0308814620b1e83000020a86826000482806000980412170000000050081028001380402010280c04020003804000380c0000028001c010406c0e030080824150d00002030684418049b98a50d0e6d62943439b98a5190e6d6294643d3d0c5250f2e43149438fd954310eac6250c4397d954310ecc6250c439798e50d0a5d6394342d314f4250b1c53909428fd954210a9c63508429bd954210acc6350842cd90d5110b344354442cdd095110b664254442cd5095110b654254442b958442cca3e64947328f59251cca7661152329d584548ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca7a60d50329e583540ca7661150329d584540ca7a60150329e580540ca5d6510c329b594420cb8c4310832b9584420ca5f654c832a7191320ca6f654c832ab191320cb5b4354032d610d500cb6b4254032da109500cb5b3254032da8c9500cb593254032da4c9500ca6f6254f419b18953d069c6350b419798e50d065d63943419b98a50d066d6294341ad986435071f5310d41d3d4f525074c53d4941d3d4c525074c5314941cb90c525072c4314941d9584525072c52d0941a718d425075b53d4141d614f505076b52d4141da14b505075b5314141d614c505076b5214141da148505073a4314141ce10c505072d52d0441d954a411063f6550441cb54941106776550441d9549411066e62d53319b58b54cc67a60d53319e58354cc66e62d52319b58b548c71f63552319b988548c66d6215231c7550438c72e5494a31cb552528c74f4394a31d310e528c72e5454a31cb551528c65f63551319bd89544c66c62551319ed81544c67860551319b988504c66d62141319bd89540c66c62550319b988540c66d62150319e980540c679601503197594430c63e64944318f592510c65f654c4319dd95310c65e63d53219758f54c867a60d53219e58354c863f6454f218f19153c867a6014f219e58053c86cc6350b21d354c32c86e9600cb219798f548865d63d52218f993538863d64d4e21b958442886e46250621e9d09418865f63551219718d544866f62551219ed81544867860551218fd91534863c6454d219ed8153486786054d219b996424866c6550921b318d424866e65cc921ba58032486746550521e9509414865e63141219758c504863d659502197d8d540865c6355021c7d8d540871c6355021cb189540863e64150219b988540867661150218f993530863d64d4c219b98b530863e6414c218f590530867a6014c219e580530866d65d0821cb553420866d6510821cb55042086e56110821cb553210873554884219bd95210872d54484219dd9521087355448421ae18141d031d5310e40d394e529034d5394a40cb90e529032c4394a40d394d529034d5354a409b988515026d6214540cd14
  | 2 => 0x5d9b086866849c4769869c0868218a862ea2f162259085ea28b4800689a84c902918ee100f4291f80aac459800000e600000b3ade002ca0026e8fa72b98a6000000000000952a985c7801a001acab21e809184b112998e01e81248b2aca184118c8842d41280c718ac019563e8ce310daa2182c31b6c10b04a2349dab82f87c2127a52020ab88c0e0b40921c6407e9281e82a8c4c2b28b2ee478009a3362c8f600000c61d84d8d47a8caa38007d9a6572c0c916a4f00070098838c01c9faaa80093800001f47415e7b18e0a3324b80a500d83ab3a490003caa0851429931a001201493a18322209cc970001d050c9a267996405980be1aa81a86248800004490832aa290c4256658486331400000bf232c583a7500096b06a2a30b1972b816cc230a0c216268001a800b0800c386e0000064800002d600000002daa88366e856150c26e25498000002f20031c6720c5f0700022abc2e400300552be67a98000768f000089c2348dc0009c5d058669fe001d269000a0ab4529bc4fa7eb8a504d14ea02c83e17e6cb34b303e2a02604178c79f01931200000000006604e802e87ca58450ec43946011e8542d84585a0011043000001588e8883fa40000007f1e2a78008880062090bda20a91068900e021945b8e20d000001d6a68e8cb2440013837a362b8cc9326a001c842a52402380f018779ce000b800000c801c00274bd014499ee512ec132b6468a02d82e00000001b4b41ae5800027a9222a78be904ae95a0000000000239a053330000f0b7000288682a800000000002caf0005a000000004a894a58d68b8d05c338791ca6fa5e17862a10e4770c61b32e9b294472482eb02bf878812623f2b09f29c1080603008180012008241c04018000e37040205a050381c02000580014260080000001f00404000080c02060180438000881c000005808020f00008001c0283000000882000010b000000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2874436012c05402400163464c53c05d200850e40030210802cf20165451cd4254442a88e6a12a22168443584420cb8421884a8065585c44254032a30e8992a019528744c9500ca52b94c321a83431d1530cb21c92a6b006590d84735094148706318c4aa043431cd5410821c4aa8b088410d25721454150264b94c1a1a61325c8604c530a18e6aa085906255458442c8292ba0a290a41325cc6048520b10e8992609060c6418953082863a2a6190419254d600c820
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x4000608020d00435c44254032a088454d600cb21a04835516110821a04835516110b20a088454d600c820
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
  | 5 => packedAt s3K5 (18682+((h/205+packedAt s3K5 (16632+(h % 205)*10) 10) % 895)*11) 11
  | 4 => packedAt s3K4 (16974+((h/138+packedAt s3K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s3K3 (1265+((h/8+packedAt s3K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (304+((h/1+packedAt s3K2 (300+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffff03ffffe07e0f87fffff07fffa07fe3f
  | 1 => 0x7c0fffffffffff800ff87c1fffffffc388fff
  | 2 => 0x7ff01ffc07f07ffff0007fe1ff87c07c0f3cc
  | 4 => 0xf80001ffff8007fffffff8001fff8007ff03f0
  | 5 => 0xfffffe00000007ffffffffffe0000007fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x12441411891222016428294a2544a552033615
  | 1 => 0xa092292212248458105482a14a894aa41888ea
  | 2 => 0x530a4d448748aeaab50424ed13d47036c0d34c
  | 4 => 0x622cb089240e3334c69930081c6620c36d03b0
  | 5 => 0x8430c10e3870c5c718e6473180804305b6ec00
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefea8a8c8c88888fefea8a8c8c88888fefea8a8c8c88888fefea8a8c8c88888fefea8a8c8c88888fefea8a8c8c88888fefea8a8c8c88888fefea8a8c8c88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36356
namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xac000420000600016800001382369860406b0bae3a0120e4a34f1f262149c000038054c1889005400b001400a22000004400d000200c0f00a1792280118020800000064b00000000481020c0022a240000c00200ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xad1c0000258fa220008c28000000000000000016000000070001a8008c4b1400000000929064000c148e08f3d18924001a1d8fc212da34b239428d8009a000002e000000000000004c000000090005000080004a002740000218005a880000000003780000832d0006e0c390ec00a23600082160006400300017d0c7c00068001b4b80000944123000000007800872c0000071000bc006d0000000022480140003980000602a00c0000001ac002e000004c790000420000003c2a5e00000000000000000000000000020000cc8b48244629b001587c551f9fd425c00000002c3a0cc38290018c8411028000045260000000001380053000007a0000001460037000540040000000000000000024190080003800000e00000000028a7c14813b87400951d0000068338f13c6a3d8181a89000000000001103e000000000004c800005730824ba00002704e0004194ea000022926780000000002780130003491d084d12802110100800000000000000080c0c030181400010000c02010182408010003c0a01000040002030000a05010000002000000000010000203000040402004f94b439ea8e873e50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e7ea2a1cf141439f2a0873d5390a7ca5214f546429f28485765110aeaa2214f54c429f29085ae5210b6ca2214f54442daa8885355110a7ca0214f953329eaa665ac42cca7ea9194f152329faa2653c544ca7ca8194f55032d62106576510caeaa2195e94032bca80653d53d067ca5a0cf943419eaa4836e52906daa520cfd4d419e29283b75150678a0a0cf95041b7290836d521067ca998cf553319f2a4633d548c6dca518db54a319f2a2633d544c67ca818cf55031b7290636d520c6f4a018de540319faa6433c54c875c8590eb10b21d7aa643ac54c875e8790eb50f21d7a0e43ad41c867ca910cf55221b6a9443b5418867ea890cf15121d721243ac424876a8290ebd5121d62a243af434875a8690f9d4521d7a0a43e6414875a8290f950521d2a0a43e631487ca6290cf950219eaa0436e52086dca5205b54a409ea9c813e529035ca5204b94a40d6a94813d519035e43206b486409f284813d531027ca4204f54440d790881ad211027ca0206e940409f2a6613d54cc27ea9184f152309faa2613c544c2dea4985b14930bba8a6174514c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c835885905d94720baa8e413e548827aa9104fd51209e2a241ac424827ea8104f150209f2a6213d54c42dca5885b54b109faa4213c54843ca43084fd51109e2a2213e540427aa8085794c10aea98216e52042daa4087948410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x882a06a08e80746128e72551b43eed69a16100271291780003401360a99290e2860042dcf16241989b00cc4112eac08332a07804cb9c00200001c6c51600001c1048800180030a0010e082410006040008b98a50d0e6561149438d5845250ea56114943c99845250e2d6114943c95845250e256114943c99495110b266254442a958442cca3561152328b594420caa56110832c9109510cb2842540328b18953d062e62943418b18954cc62c62551318e181544c63a60d5321a958754c86aa60d5321a958454c862c6550f218d19541486a561d0d218b19543486a56490521a999541486a46550521a9d8d41486a46050521a959231486a5644c5219958652902356194a40a958652903266194a408b58652903256194a4089586529022f65c86408bd95219022c6254c40c9545211022c62553308b98b548c2a56110b20c910951c82a561109208b98b540821d63150208d584540822e62d5210c9d51218422e62d5110c955121043455348410
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x14441800031d01480b212b8cc528687485c26254442a42e2212a0194a27099541486123aac898a43281c1644c52184ae2312a6204257118954cc212b8cc5aa461095c662d5110
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
  | 4 => packedAt s4K4 (4950+((h/55+packedAt s4K4 (4455+(h % 55)*9) 9) % 316)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffc1f0fc3ffc3c387fffe1c1c3ffe0ff43f
  | 1 => 0xf0fffe00ffc7ffc03f8f87fe01fc3ff3238cf
  | 2 => 0xff07ffff000787ffc00ff87ffe003c1c3cf0c
  | 3 => 0xf0007fffffff807fffff0007fffffc01fc0ff0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2101044412841000c081288a0444185404d415
  | 1 => 0x42624882a520a44c21485455208982a912284a
  | 2 => 0xa427514a81a944d564409d4749c08b0d434d0c
  | 3 => 0x882210080001220a12000092122000a802a0
  | 5 => 0xc8cc439cce32767bb3e4e66103033231ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfea8fea8fe88fe88fea8fea8fe88fe88fea8fea8fe88fe88fea8fea8fe88fe88fea8fea8fe88fe88fea8fea8fe88fe88fea8fea8fe88fe88fea8fea8fe88fe88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36356
namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc9c08200235aa000b008132f3a006861c912824400ba70000600000001b584cb09201c00a52480051ec0f0342500012aac01154018803e00c2e34002400a00bc00c00002800000700ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1129f08800ee3d342585c6c0e910ae424700068072083cf8662f0292e701c00000002c181244535a8d0800498b400001f00132304e05800004600000002d800001c000bc009400000008a478c4869a2f948e69b000147269151d86aa0248789a0012884e861021b41891469d4a698001684829199c800903c0b09c235212d105600214500e0599d2a0037288e2140d9fc8c1804964c61a2a85d063f1b0089810280ec784a328004012041a8801f2e13c646413a7502013d8ac2a9e03284a2874320900473e9bc90003f188440d3d0e800031b8000026459e4001909950ba0003130004001a0d041681048481030011020100070c8101000000008a83830000800484990100838188858180818b068901078b030800844f94b439f28e873d50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e78a2a1cfd41439f2a0873d5390a7ca5214f946429ea84857a5010af2a0214f54c429f29085ae5210a7ca2216e940429ea8085b95010a72a0214f953329eaa665ac42cca7ea9194f152329faa2653c544ca7ca8194f55032d62106576510caeaa2195e94032bca80656e52906daa520cf54e419f29483ae529065ca520eb54a419f28c833d509067aa620cf948419f28883b6511067aa020cf953319eaa6633f548c678a918cfd51319e2a2636f524c6d8a498ded4131bc282633e540c67aa818db94831b6a90637a500c6f2a018cf953219eaa643ac42c86f4a190de543219f2a4433d548867ea890cf15121d6212433f5408678a810cf54f409f296813e51d027aa9205b94a40b6a94813f5350278a4a04f14540dda82813e54102dca4205b548409f2a6613d54cc27ca9184f55230b7294616d528c27ca8984f551309f2a0613d540c2dca4185b54830bb2886175510c27ea9904f15320d721641ac42c835ea9906b15320d7a1e41ad43c835c83906b10720d7a0641ad40c827ca9104f55220b6a9441b9408827ea8904f15120d721241ac424837280906bd5120d62a241af434835a86906b90520d620a41eb504835e80907a90120d6a0241e9404835280907a8c120f4982413e540827aa8105b948209faa6213c54c43d241884f952109eaa4216e52842daa5084fd51109e2a2213e540427aa8085794c10aea98216e52042daa4087a48010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x38e3808a802250010800000a002e00c0000b040000000106e48b000004c8a006c03b5c747b674014b5480088b0498f2b0a240064e1c00c06bda20464d8000000ab9000192500699ad3e340006200040020004000240c104000008308083008b98a51d0e6960149438e5805250ea96014943ca9805250e2d6014943ca5805250e296014943ca9495010b2a6254042aa58042cca3960152328b594420caa96010832c9109510cb2842540329a58252906396094a41aa582529072a6094a418b58252907296094a418a582529062c6254c418b18954cc62e62d5231aa58042c87284254321aa580424862e62d50218758c540863960150218b18953d022e62947408b18954cc22c62551308d185544c23661d5320a998754c82a960d5320aa58054c822c6550f208b99641c82386550120aa583434822c6550d208b99641482a96010520aa59240482aa6550120aa19540482ab6350120aa18540482a9648c120aa591304822e62d5310cad5120c422e62d5110ca55120043495348010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1805000071812200488000000614b84c528e87485c66254042a42e0212a219429701895310614b80c4aa6630a5c262d5231944e332a809042875591304825038ac8982410a5c262d5110
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
  | 5 => packedAt s5K5 (912+((h/16+packedAt s5K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s5K4 (4895+((h/55+packedAt s5K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s5K3 (2420+((h/20+packedAt s5K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s5K2 (505+((h/3+packedAt s5K2 (490+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff0ffc1f0fc7ffc3c38ff87e3c1c3fff0e343f
  | 1 => 0xfffffe00ff87ffc03f0ffffc01fc3fe33f8cf
  | 2 => 0xff07ffff000787ffc00ff87ffe003c1c3cf0c
  | 3 => 0xf0007fffffff807fffff0007fffffc01fc0ff0
  | 4 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x21614444928c1440e0892c4a24441a55061415
  | 1 => 0x420208822500a00c01105094408980a810e84a
  | 2 => 0xa427514a819544d564089d46a9c08b0d434d0c
  | 3 => 0x882210080001220a22000112122000a802a0
  | 4 => 0xc8cc439cce26767bb3cce66023033231ffb000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88fec8fe88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36356
namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xb004001a1af002100f5724000001300c5500600078000759224c5c03e000001f1c808800000000000000066e82273c0003f4a044a86cedb8036000005a01c2c68706190e8c0166a154b928000005e28a8206ac00624200180a000800006080040000084000c406000410001ffd5005fe54007f55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03bf4300ff90c03fd4300ef50c03fc4301ffd4801fe52007f54807fc52017fd0801fe42007f50805fc4200ffcc803fe3200ff4c803fc3201ffd4401fe51007f54407fc51017fd0401fe41007f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc2101ffd4001fe50007f54007fc50017fd0001fe40007f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42005ff0821002ffe2108017f71084009fd8842000ffd9510005feca88033fe65440077f32a2000ff59510005faca88033fc65440077e32a2000ffd9110005fec88802ffe64440057f3222000ff59110005fac88802ffc64440057e322200cffd511005ffca888003fd5444017fe2a2200affd8d10055fec68802bfe63440037f31a200aff58d10055fac68802bfc63440037e31a200affd4d10056fea68802bfe5344015fea9a200adf54d10057f8a68802bff4344015dfa1a200aff90d10057fa868802bbd4344015fe21a2000ffd8910005fec488003fe62440137f3122000ff58910005fac488003fc62440137e312200cffd4910007fca488003fd5244019fe292200bffd0910007fc8488003fd4244017fe212200affcc910057fc648802bfd3244015fe192200cffd4510027fca288003fd5144009fe28a200bffd0510027fc8288003fd4144009fe20a200affcc510027fc628802bf63144015fe98a200afd4c510027f86288003ff2144009ff10a2000ff48510027f84288033ff504400bff2822000ff5411002ff8a08802fff404400bff2022000ff5011002ff8808802bff304400bff182200afe8c110057fa608802bf9304400bfe1822000ffc811002ffc4088003fd204400bfe1022004ffc4110027f62088017fe104400bfb0822005ffd941002dfeca08017fe65040077f3282005df9941001cfcca08017fd65040017eb282005df59410004faca08017fc650400b7e3282005ffd901002dfec808017fe64040057f3202005ef990100157cc808017fd64040017eb202005ef590100057ac808017fc640400b7e3202008ffd501003ffca808003fd540400ffe2a02005ffd8c1002dfec608017fe63040037f3182005f798c1000dbcc608017fd630400d7eb182005f758c10005bac608017fc630400b7e3182006ffd4c10036fea60801bfe530400dfea982006df54c10037f8a60801bff430400ddfa182006ff90c10037fa860801bbd430400dfe2182005ffd881002dfec408017fe62040137f3102005fb98810005dcc408017fd62040017eb102005fb58810005dac408017fc620400b7e3102008ffd4810007fca408003fd5204011fe2902007ffd0810007fc8408003fd420400ffe2102006ffcc810037fc640801bfd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802004fe44010
  | 1 => 0x7fc5108029ffa084000ff90420007fa8210053fc4108027ff9884013ff8c42009ffa621004ffc3108013ff9084009ff8842004ffa4210027fc210800b7f3004005ffd402002ffca010017fd500800bfe2804005ffd002002ffc8010017fd400800bfe2004005ffcc02002ffc6010017fd300800bfe1804005ffc802002fde4010017fe200800bfd1004005ff4802002fda4010027f92008009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2000bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262000bf59310027f8c988012fc64c4025ffaa62011ff95310007faa988047fc54c4009ffb1e2004bfd8f10027fcc788006fe63c4009feb1e2010bf58f10027f8c788012fc63c4021ffa9e2010dfd4f10087fca788043fd53c4021bea9e2010ff14f10087fe8788043bf43c4021ff21e2010ff50f100877a8788043fc43c4009ffb162004bfd8b10027fcc588026fe62c4009feb162000bf58b10027f8c588012fc62c4025ffa962000ff94b10007faa58804bfc52c4023ffa162000ff90b10007fa8588047fc42c4021ff9962010ff8cb10087fa6588043fc32c4009ffa8e2004ff94710027faa388013fc51c4009ffa0e2004ff90710027fa8388013fc41c4009ff98e2004ff8c710027ec6388013fd31c4021fa98e2004ff0c710027fe4388013fe21c4009fe90e2004ff08710097fea188017fe50c4001fea862005ff1431008ffe8188017fe40c4001fea062005ff10310087fe6188017fe30c4021fe9862005ff0c310007fe4188017fe20c4001fe9062005ff0831002ffecb08016ff658400bff32c2003bf9961002ffacb08002fd658400bfe32c2005bf1961002ffec908016ff648400bff3242002bf9921002ffac908002fd648400bfe3242005bf1921007ffea90803bfe5484001feaa4200eff1521002ffec708016ff638400bff31c2001bf98e1002ffac708036fd638400bfe31c2005bf18e1006ffea7080377f538401bff29c200dff54e1006efaa708037fc538401bffa1c200defd0e1006ffc8708037fd438401bdea1c200dff10e1002ffec508016ff628400bff3142009bf98a1002ffac508002fd628400bfe3142005bf18a1007ffea508003fe5284001fea94200fff14a10077fe8508003fe4284001fea14200eff10a1006ffe6508037fe328401bfe994200dff0ca10055fac30803fff5184009ff28c2000ff54610027f8a30803bff4184009ff20c2000ff50610027f88308037ff3184009ff18c200dff4c610027f86308003ff2184009ff10c2000ff48610027f84308016fe608400bffa842005ff9421002ffaa108017fc508400bffa042005ff9021002ffa8108017fc408400bff9842005ff8c21002ff46108017fd308401bfc9842005ff0c21002ffe4108017fe208400bfe9
  | 2 => 0x2004ffca510003fd5288013fe294401affd0a2004ffc8510003fd4288013fe2144019ffcca2004ffc6510067fd3288013fe1944005ffd862002ffcc310012fe618800bfeb0c4000bf5862002ff8c31006fff5188001ff28c4000ff546200dff8a31006bff4188001ff20c4000ff506200d7f88310067ff3188033ff18c4019ff4c6200cff86310027ff2188001ff10c4000ff4862004ff84310016fe608800bffa844005ff9422002ffaa110017fc508800bffa044005ff9022002ff48110017fd4088001fca044005ff1022002ffe6110017fe308800bfd1844005ff4c2200cff26110017fc308800bff9044005fbc822004ff64110003ff65480017fb2a4018ff9952001dfcca90003fd65480017eb2a4018ff1952001df8ca90003ff64480017fb224017ff99120015fcc890003fd64480017eb224017ff19120015f8c890063ff544802fff2a24000ff551200bff8a89005bff634802d7fb1a4016ff98d2000dfcc69005bfd634802d7eb1a4016ff18d2000df8c69005bff534802dbfa9a4016ff94d200b7faa69005b7d534802dfe29a4016ffd0d200b77e869005bfe434802dfea1a4016ef50d200b7f88690063ff5248031f7a924009ff94920007faa490027fc5248031f62924017ffd092004ffc8490003ee4248001fea124000fb5092004ff8849005bff3248013ff1924016fb8c9200b7fa649005bed3248013fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520025f8c290063ff5148001ff28a4000ff545200c7f8a29005fff4148001ff20a4000ff505200bff8829005bff314802dff18a4016ff4c5200b7f86290027ff2148001f790a4000ff88520007fa4290003ed2148013fe10a4018ffd412002ffca090003fd504800bfe2824017ffd012002ffc8090003fa4048001fea024000fe5012002ff8809005bff304800bff1824016fe8c1200b7fa609005bf9304800bfe1824009ffc812004ff64090017fe204800bf71024005ffd942002dfeca10017fe65080077f3284005ff59420005faca10017fc650800b7e3284005ffd902002dfec810017fe64080057f3204005ef990200157cc810017fd64080017eb204005ef590200057ac810017fc640800b7e3204015ffd50200a7fca810003fd5408029fe2a04005ffd8c2002dfec610017fe63080037f3184005ff58c2009dfac610017fc630800b7e3184013ffd4c2009efea61004ffe5308027fea984013df54c2009ff8a61004fff4308027dfa184013ff90c2009ffa861004fbd4308027fe2184009bf9882004ffea410027fe5208013fea904009ff1482004ffe8410027fe4208013fea104009ff1082004ffe6410027fe3208013fe9904009ff0c82002ffec210017fe61080097f3084005ff58420005fac210017fc610802bffa884000ff94420007faa21005
  | 3 => 0xfaa28020efd5140017fca8a000bfd5450005fe2a28002ef151400fffec6a007eff635003fff31a8001bf98d400fffac6a007efd635003ffe31a8001bf18d400fffea6a007f7f535003fff29a801fff54d400fefaa6a007ffc5350005ffa1a8002efd0d40017fc86a000bfd435003fdea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0026fc6250041ffa928000ff94940007faa4a0083fc5250005ffa128002efd0940017fc84a000bfd4250001dea128002ff109400fffe64a007ffe325003ffe992801fff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0012fc6150041ffa8a8000ff94540007faa2a0083fc5150005ffa0a8002efd0540017fc82a000bfd4150001dea0a8002ff105400fffe62a007ffe315003ffe98a801fff0c540007fe42a0003fe2150001fe90a8000ff08540015fec0a0083ff505000bff2828000ff5414002ff8a0a000bff4050005fda028005ff9014002f7c80a0017fc405000bde2028002fe101400fffe60a0017fe305003ffe9828005ff0c14004ffecb90026ff65c8013ff32e4003bf9972004ffacb90002fd65c8013fe32e4009bf1972004ffec990026ff64c8013ff3264002bf9932004ffac990002fd64c8013fe3264009bf193200f7fea990077fe54c8001feaa6401dff1532004ffec790026ff63c8013ff31e4001bf98f2004ffac790072fd63c8013fe31e4009bf18f200e7fea7900737f53c8039ff29e401cff54f200e6faa790073fc53c8039ffa1e401cefd0f200e7fc8790073fd43c8039dea1e401cff10f2004ffea59007bef52c8013ff2964009ff54b2004ff8a590027ec52c8013ffa164009ff90b2004fdc8590027fd42c8001f6a164009ff10b2004ffe6590027fe32c8013f71964009ff4cb200e7da6590027fc32c8013ffb0e4009ff98720025fcc390027fd61c80017eb0e4009ff187200f7fea390003fe51c8001fea8e401eff147200effe8390003fe41c8001fea0e401dff107200e7fe6390073fe31c8039fe98e401cff0c72004ffe4390027ef21c8013ff10e4009ff48720007da4390027fc21c803dffa864005ff94320007faa190017fc50c803bffa064005ff90320007fa8190017fc40c8039ff9864005ff8c3200e7fa6190017fc30c800bffb2c4005bfd962002ffccb1000efe658800bfeb2c4000bf5962002ff8cb10016fc658800bffb244005bfd922002ffcc91000afe648800bfeb244000bf5922002ff8c910016fc6488037ffaa4401aff95220007faa91006bfc548800bffb1c4005bfd8e2002ffcc710006fe638800bfeb1c4019bf58e2002ff8c710016fc6388033ffa9c4019dfd4e200cffca710067fd5388033bea9c4019ff14e200cffe8710067bf4388033ff21c4019ff50e200cf7a8710067fc438802d7eb14401bffd4a
  | 4 => 0x17fe61940097f30ca005ff58650005fac328017fc6194007ffa8ca003ff9465001ffaa32800ffc519404dffa0ca000ff90650007fa832809bfc419404bff98ca025ff8c65012ffa6328097fc3194001ff90ca000ff88650007fa4328003fc219400b7f304a005ffd425002efea12800ffb509400bfe284a005fe1425002ffe8128017fc409400bff984a005ff8c25002ffa6128017fc309400b7fb2aa000ffd9150005fec8a8093fe64540057f322a000ff59150127f8c8a800afc6454007ffaa2a003ff9515001ffaa8a800ffc5454047ffb1aa023bfd8d5011ffcc6a8006fe6354047feb1aa023bf58d5011ff8c6a8006fc6354007ffa9aa003dfd4d5001ffca6a800ffd5354047bea9aa003ff14d5011ffe86a808fbf4354047ff21aa023ff50d5011f7a86a808ffc4354001ffb12a000bfd8950007fcc4a8003fd6254001fe312a009bf1895001ffea4a800ffe5254007fea92a003ff14950127fe84a8003fe4254001fea12a024ff1095011ffe64a808ffe3254047fe992a023ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8012fc6154007ffa8aa003dfd455001ffca2a800ffd5154001bea8aa003ff14550127fe82a8003fe4154001fea0aa024ff1055011ffe62a808ffe3154047fe98aa023ff0c550007fe42a8003fe2154001fe90aa000ff0855001dfec0a800fff5054007fda82a005ff9415002efca0a8017fc505400bbe282a003fe14150127fe80a8017fc4054047ff982a005ff8c15011ffa60a8017fc305400bffb2c8005bfd964002ffccb2000efe659000bfeb2c8000bf5964002ff8cb20016fc65900057eb248002ffd5240017fca92000bfd5490005fe2a48005ffd8e4002dfec720017fe63900037f31c8005ff58e4010dfac720017fc639000b7e31c8021ffd4e4010efea720087fe5390043fea9c8021df54e4010ff8a72000bff4390005dfa1c8002ff90e40017fa8720087bd4390005fe21c8005ffd8a4002ffcc520026fe629000bfeb148000bf58a4002ff8c52008bff5290001ff2948000ff54a40117f8a52000bff4290005ff2148002ff50a40017f88520087ff3290043ff1948021ff4ca4010ff86520017ff619000bff30c8004bf9864002ffac320002fd619000bfe30c8022ffd4640007fca320003fd5190045fe28c8002ffd0640017fc832000bfd4190005fe20c8021ffcc64010ffc6320087fd3190043fe18c8000ffc8640007fc4320003fd2190001fe10c8005bf9824002ffea120017fe509000bfea848005ff1424002ffe8120017bf4090005fda048005ff1024002ff08120017ff309000bff1848005ff4c24002ff86120003ff65500017fb2a8000dfd9540004fecaa0083fe65500077f32a8000ff59540005facaa0083fc65500077e32a8000df1954001cf8caa0016ff6450005f
  | 5 => 0x8d2100dfcc6908abfd63484557eb1a422aff18d2100df8c6908abff5348455bfa9a422aff94d21157faa6908ab7d5348455fe29a422affd0d211577e86908abfe4348455fea1a422aef50d21157f886908b3ff5248413ff2924200fb94921007faa490803ed5248413fe292422bffd092115fde8490827fe4248401fea124209ff1092115fd884908abff3248413ff192422afb8c921157fa64908abed3248413fe192422cffd4521027fca290803f65148401fea8a4200fd54521027f8a2908afff4148409ff20a4200ff50521027f882908abff3148409ff18a422afd8c521157fa62908abf53148409fe18a4209ffc852104fee4290813fe2148409f710a4200ffd8121005fec090803fe6048401feb024200ff1812102df8c0908b3ff5048459fe282422bffd012115ff880908abff3048455ff182422aff4c121157f86090813ff65084097fb284204ff9942101dfcca108137e65084073f3284204ff59421005faca108137d65084013eb284204ff19421025f8ca10813ff64084097fb204204ff99021015fcc810813fd64084017eb204204ff19021025f8c8108a7ff5408451ff2a04200ff55021147f8a810813ff63084097fb184204ff98c2100dfcc610813fd630844f7eb184204ff18c21025f8c61089fff530844fbfa984227ff94c2113ffaa61089f7d530844ffe2984227ffd0c2113f7e861089ffe430844ffea184227ef50c2113ff88610826fe6208413ffa904209ff9482104ffaa410827fc5208413ffa104209ff9082104ffa8410827fc4208413ff9904209ff8c82104ffa6410827fc32084097f3084204ffd4421027fca210813fd5108409fe2884204ffd0421027fc8210813fd4108409fe2084204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da4210827f52108409ffb004204ff9802102dfcc010813fd60084017eb004204ff1802114ffea0108a7fc5008451ffa004228ff1002113ffe601089ffe300844ffe9804227ff0c02101dfacb28017ff649400bff324a002bf9925002f7cc92800abe649400bfeb24a000bf5925002f7ac928002bd649400bfe324a005bf1925001ffea92800ffe549404dbf2a4a003ff5525001ff8a92800f7c549400bffb1ca005bfd8e5002ffcc728006fe639400bfeb1ca025bf58e5002ff8c728016fc6394007ffa9ca003dfd4e5001ffca72800ffd539404bbea9ca003ff14e5012ffe8728097bf439404bff21ca025ff50e5012f7a8728097fc439400bffb14a005ff98a5004dfcc528017ee629400177314a005ff58a50005fac528017ed629400176b14a005ff18a5001ffea52800ffe5294007fea94a003ff14a50137fe8528003fe4294001fea14a026ff10a5012ffe6528097fe329404bfe994a025ff0ca5002ffec328
  | 6 => 0x1fea8a8204ff14541017fe82a080bf74150409ff20a8204ef90541027f882a0813bc4150405fa20a8233ffcc541027fc62a08cffd3150409fe18a8200ffd8141005fec0a0803fe6050401feb028200ff1814102df8c0a08d3ff5050469fe2828202ffd01410177e80a080bfc4050467ff9828233ff8c14119ffa60a08cffc3050413ffb2e4209bfd972104ffccb9080efe65c8413feb2e4200bf5972104ff8cb90826fc65c8413ffb264209bfd932104ffcc99080afe64c8413feb264200bf5932104ff8c990826fc64c8465ffaa64231ff95321007faa9908c7fc54c8413ffb1e4209bfd8f2104ffcc790806fe63c8413feb1e4230bf58f2104ff8c790826fc63c8461ffa9e4230dfd4f21187fca7908c3fd53c8461bea9e4230ff14f21187fe87908c3bf43c8461ff21e4230ff50f211877a87908c3fc43c8413ffa964209ff94b2104fdca590827fd52c8401f6a964209ff14b2104ffe85908c7ef42c8413ff2164209ff50b2104ff88590827ec42c8413ff9964209ff8cb2104fdc6590827fd32c8461f69964209ff0cb21197fea390813fe51c8401fea8e4204ff1472118ffe8390813fe41c8401fea0e4204ff10721187fe6390813fe31c8461fe98e4204ff0c72104ffec190827fe60c840b7f3064209ff58321005fac190827fc60c8465ffa864232ff1432118ffe81908c7fc40c8461ff9864230ff8c321187fa61908c3fc30c8409ffb2c4204bfd9621027fccb1080efe6588409feb2c4200bf59621027f8cb10812fc6588409ffb244204bfd9221027fcc91080afe6488409feb244200bf59221027f8c910812fc648845fffaa4422eff95221007faa9108bbfc5488409ffb1c4204bfd8e21027fcc710806fe6388409feb1c422dbf58e21027f8c710812fc638845bffa9c422ddfd4e2116ffca7108b7fd538845bbea9c422dff14e2116ffe87108b7bf438845bff21c422dff50e2116f7a87108b7fc43884557eb14422fffd4a2104ffca510803fd5288413fe294422effd0a2104ffc8510803fd4288413fe214422dffcca2104ffc65108b7fd3288413fe1944204bf98621027fea310813fe5188409fb28c4204ff54621007eaa310813fc5188409ffa0c4204ff90621027fa8310813fc4188409ff98c4204ff8c621027ec6310813fd318845bfa98c4204ff0c621027fe4310813ef2188413fb90c4204ffd8221027fcc110816fe6088409feb044200bf58221027f8c1108bfff508845ffe284422effd0221177f881108b7ff308845bff184422dff4c22116ff86110803ff65484017fb2a422cff9952101dfcca90803fd65484017eb2a422cff1952101df8ca90803ff64484017fb22422bff99121015fcc890803fd64484017eb22422bff19121015f8c8908b3ff5448457ff2a24200ff5512115ff8a8908abff63484557fb1a422aff9
  | 7 => 0xa880afc6454401de322a202af1915101ffea8a880ffe5454471bf2a2a203ff5515101ff8a8a880f7c545446fffb1aa237bfd8d511bffcc6a8806fe635446ffeb1aa237bf58d511bff8c6a8806fc6354407ffa9aa203dfd4d5101ffca6a880ffd535446fbea9aa203ff14d511bffe86a88dfbf435446fff21aa237ff50d511bf7a86a88dffc4354401ffb12a200bfd8951007fcc4a8803fd6254401fe312a209bf1895101ffea4a880f7f5254407ff292a203ff54951006faa4a880ffc5254471ffa12a200ff90951007fa84a88e3fc425446fff992a237ff8c9511bffa64a88dffc32544077fb0aa203ffd455101feea2a8813fe5154409bf28aa204ff14551026f8a2a880ff45154471ffa0aa204ff105511bffe62a8813fe315446ffe98aa204ff0c551007fec0a8802ff6054401ff302a200ff58151007f8c0a8816fc6054407ffa82a203dfd415101ff8a0a88e3ff4054471fe202a237ffcc1511bffc60a88dffd305446ffe182a204ffd9641025fecb20813fe65904077f32c8204df9964101cfccb20813fd65904017eb2c8204df59641004facb20813fc65904097e32c8202bf59241017fea9208dbbf5490405ff2a48202ff55241017f8a92080bbc5490409ffb1c8204bfd8e41027fcc720806fe6390409feb1c8235bf58e41027f8c720812fc639046bffa9c8235dfd4e411affca7208d7fd539046bbea9c8235ff14e41017fe872080bbf4390405ff21c8202ff50e411af7a872080bfc4390409ffb148204ff98a4104dfcc520813ee6290401773148204ff58a41005fac520813ed629040176b148204ff18a411b7fea520803fe5290401fea948236ff14a41017fe852080bfe4290405fea148202ff10a411affe65208d7fe329046bfe9948235ff0ca41025fcc320813ff5190409ff28c8204ff54641027f8a320813ff4190409dfa0c8202fdd0641027f88320813f44190409ff98c8204ff8c641027fa6320813fc3190409ffb048204ff9824102dfcc120813fd60904017eb048204ff182411b7fea1208dbfc5090405ffa048202ff102411affe61208d7fe309046bfe9848235ff0c241007fecaa0802ff6550469ff32a8203bf99541007facaa0802fd6550469fe32a8203bf19541025fec8a080bff5450405ff2a28202ff55141017f8a8a08cfff63504677fb1a8233ff98d4100dfcc6a08cffd63504677eb1a8233ff18d4100df8c6a08cfff5350467bfa9a8233ff94d4119ffaa6a08cf7d5350467fe29a8202ffd0d410177e86a080bfe4350405fea1a8233ef50d41017f886a0803ff62504017fb128200ff98941007fac4a0803fc62504137e3128234ffd4941007fca4a0803fd5250469fe2928202ffd0941017fc84a080bfd4250405fe2128233ffcc94119ffc64a08cffd3250467fe1928202bfd85411a7fea2a0813fe515040
  | 8 => 0xf18e421effea7210f77f539087bff29c843dff54e421eefaa7210f7fc5390805ffa1c8402efd0e42017fc872100bfd439087bdea1c8402ff10e4204dfcc521027ff5290813ff2948409ff54a4204ff8a521027ff4290813dfa148402fbd0a4204ff88521027ec4290813ff9948409ff8ca4204ffa6521027fc3290813ffb0c8409ff98642025fcc321027fd61908017eb0c8409ff186421f7fea3210fbfc5190805ffa0c8402ff106421effe63210f7fe319087bfe98c843dff0c64204ffec121027fe609080b7f3048409ff58242005fac121027fc609087dffa84843eff14242017fe812100bfc409087bff984843dff8c2421effa61210f7fc3090801ffb2a8400bfd9542006fecaa10027f6550879ff32a8403bf99542007facaa1002fd6550879fe32a8403bf19542006f8caa100e7c65508137fb228402ffd5142017fca8a100bfd5450805fe2a2843bffd8d421ddfec6a10effe63508037f31a843bff58d421ddfac6a10effc63508037e31a843bffd4d421defea6a10effe5350877fea9a843bdf54d421dff8a6a100bff4350805dfa1a8402ff90d42017fa86a10efbd4350805fe21a8402bfd89421e7fea4a1027fe5250801fea928409ff14942017fe84a100bef4250813ff2128409ef9094204ff884a1027bc4250805f6212843bffcc94204ffc64a10effd3250813fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542025f8c2a10f3ff5150879fe28a8402ffd0542017f882a10efff3150877ff18a843bff4c5421dff862a1003ff60508017fb028400ff98142007fac0a1003fc605080b7e302843cffd41421e7f8a0a100bff4050805dfa028402ff101421dffe60a10effe3050877fe982843bff0c14201dfacb28813ff6494409ff324a202bf99251027fac928802fd6494409fe324a204bf1925101ffea92880ffe5494407feaa4a203ff15251027fec728812ff6394409ff31ca201bf98e51027fac7288e6fd6394409fe31ca204bf18e5101ffea72880f7f5394407ff29ca203ff54e511cefaa72880ffc5394473ffa1ca239efd0e511cffc87288e7fd4394473dea1ca239ff10e51027fec528813fe62944137f314a204ff58a51005fac528813fc6294407ffa94a203ff94a5101ffaa52880ffc5294475ffa14a200ff90a51007fa85288ebfc4294473ff994a239ff8ca511cffa65288e7fc32944097f30ca204ffd4651026fea32880ff75194409fe28ca204fd14651027fe8328813fc4194409ff98ca204ff8c651027fa6328813fc3194409ffb04a204ff9825102dfcc128813fd60944017eb04a204ff1825101ffea12880ffc5094475ffa04a23aff102511cffe61288e7fe3094473fe984a239ff0c251025fecaa8803ff64544017fb22a200efd91510057ec8a88e3fe64544057f322a200ff591511c7f8c8
  | 9 => 0x5ff21aa802ff50d5421f7a86aa00bfc4355001ffb12a800bfd8954007fcc4aa003fd6255001fe312a809bf1895401ffea4aa00ffc5255005ffa12a802ff1095421ffe64aa10ffe3255087fe992a843ff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa012fc6155007ffa8aa803ff14554017fe82aa00bfc4155087ff98aa843ff8c55421ffa62aa10ffc3155001ffb02a800bfd8154007fcc0aa003fd6055001fe302a805bf1815401ffea0aa00ffc5055005ffa02a802ff1015421ffe60aa10ffe3055087fe982a843ff0c15401dfacb29027ff6494813ff324a402bf9925204ffac929002fd6494813fe324a409bf1925201ffea92900ffe5494885bf2a4a403ff5525201ff8a92900f7c5494813ffb1ca409bfd8e5204ffcc729006fe6394813feb1ca441bf58e5204ff8c729026fc6394807ffa9ca403dfd4e5201ffca72900ffd5394883bea9ca403ff14e5220ffe8729107bf4394883ff21ca441ff50e5220f7a8729107fc43948137f314a409ffd4a5204efea52900fef5294813fe294a409fb14a5204ffe8529027fc4294813ff994a409ff8ca5204ffa6529027fc3294813ffb0ca409ff98652025fcc329027fd61948017eb0ca409ff1865201ffea32900ffc5194885ffa0ca442ff1065220ffe6329107fe3194883fe98ca441ff0c65204ffec129027fe609480b7f304a409ff58252005fac129027fc6094807ffa84a403ff14252217fe812910bfc4094883ff984a441ff8c25220ffa6129107fc30948137fb2aa400ffd9152005fec8a9003bf64548015fb22a440ff99152015fcc8a9003fd6454881fe322a402bf1915200778c8a900abc6454807ffaa2a403ff9515201ffaa8a900ffc545487fffb1aa43fbfd8d521fffcc6a9006fe635487ffeb1aa43fbf58d521fff8c6a9006fc6354807ffa9aa403dfd4d5201ffca6a900ffd535487fbea9aa403ff14d521fffe86a90ffbf435487fff21aa43fff50d521ff7a86a90fffc43548077fb12a403ffd495201fdea4a9027fe5254813bf292a409ff1495204ef8a4a900fec5254881ffa12a409ff109521fffe64a9027fe325487ffe992a409ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9012fc6154807ffa8aa403dfd455201ff8a2a9103ff4154881fe20aa43fffcc5521fffc62a90fffd315487ffe18aa400ffd8152005fec0a9003fe6054801feb02a400ff1815202df8c0a900fff5054807fe282a440ffd0152207f880a90ffff305487fff182a43fff4c1521fff860a9027ff65908137fb2c8409ff9964201dfccb21027fd65908017eb2c8409ff1964204df8cb2100afd6490805ffaa4843eefd5242017fca92100bfd5490805fe2a48402ef1524204ffec721026ff6390813ff31c8401bf98e4204ffac7210f6fd6390813fe31c8409b
  | 10 => 0x100180500100180000180600000d00880000000100080380880000202800001100b00000980600180600280401600000300001380682400001500000180000000680600380600000280280680001380080700080080200000000000000000000000000080180200000480180300500200580080000000000280880180880500480500000000180000280100180000400680080480080000c80b80001980680000180f00800001380180000a80100380080400000680500700080000380180080c00200480000000200300000900000080000380300800180180500300680180480000080200000600480080100280000500180280380000900080000700300380080080300000400380180180000000480100280000081980080080780100280000100400200480380580081280780000000080d00680300600a00902080a80200000000180080400000000480480e80780000780080880100400000080000080000000200c80000a80280000182280100b00301680380000081480000680780080000001580080100000d00000200180201280480180600180000001481600301900000180780080000180200100a80180480400000000280780700400901300380080880001e80000180000180080000280180000400580580000100180100600100100000000100580800180280000000000001480780c80180100300100380080000080680f00080000000a80280880080800580000200080200000000000000000480000000080080080100080000880001300601400500000d80001500201101180a80600100080500180a80101400200001100000200080000000080700780300300580000180000200000000901880000700000300302b80080080080b01480900580400180080180100100200700000080000780700000000000400100100580000000180000400300181400200780c00000081f00100380d80400c80080b80000080080a00080000000281480380080000900780000200200580081480080080000101600100100080480000700080200400100000000280201400980b00380080000180180580a00380300080880780480780400200000000000000680080000000180281080000000000100180000000a80080480680380000080180100000680300280080280080300100000b00d00380680080080180101600481180080000b80900000200a00200e80e80000d00680180680180000100080000200980080080783b00d80400aff65550057fb22a802ffd515401f7ea8aa00bfe5455005bf2a2a802ff15154016f8a8aa00bbc5455087ffb1aa843bfd8d5421ffcc6aa006fe6355087feb1aa843bf58d5421ff8c6aa006fc6355007ffa9aa803dfd4d5401ffca6aa00ffd5355087bea9aa803ff14d54017fe86aa00bbf4355
  | 11 => 0xb32a989c4c745e41cd0208f9c6cf196841c64a5ee3b1011ce4678c00001c800007f000149c00043b2409414000740305051082a3d7308a0d4a666b400020885323af305892c66209613013ccdc8382000002487276f0b421b8f321694449518d640000000ee4e924e42bba00c23e62a25710dc0000000b21c400001e8000033cb961a7082800000000003782949e223441d9b4900453d1cb14bc4b658b3f793c09421c423290084c802c2b10b18d3089200a809c2f65f40dc95041620792540f14bbe2874560240b3a77220f89181221230fb92880005b40000bdcda85a726492240001d8252032cddc000000000000087531a95e8a720193c68a10cd23903f497385e074a11880000008123108aa00000000d180000002f544e8ad400067e32a2078af81173d99a3909c8090000d4c79e36a1c784e8222374167849467668b05609e466c27e1939f34c023012e8144c6dc7f735b9af4f0a82d0000ffc28c00035c19643120c01bf815c18e2c8152022800010c1b2112c4f47e52b38c7420434234221c857a33c2cc05780007e40000dc42b200023c0d5c00052c28401e071446100014240007b6427a22800023e0b59c6cc9456c36f1d64e884a922291006385aa2de97ecdf81790d91408b6e6323280ab48e8730390945c0640002ca19246560000000000f384413b58c3ca7632a21280009f401e1bc8000bea0002f585c47564fc20980010c27c711693eca5269b0a10000eca76a02497cc00005d173000014200000013a0e1037603e008807c73545e8b6c0b27091be0b80b124af13f92143c42390f522d002077638f93400a80000001c9057c2ff07f80007e836c213800000035800000000006191f41f680002321f01840000895000000082c16a00994fc9665e61d706900000380001b103440000001374eb46aa0000b10e4c26241d188c2a07c83570048dc60000db8190f7e876000216488c1cc3010df81485961428f48e584183ef05c062e7840001b580761151e21608cb87f0032956c9d28b12819fe884257243c13343c86862e300000008141d600004e633f000135c24249006180009b655c0001b94b0a1d134016b91487112019a9051c70a31a1d741782d42609ec036684c32a8ccce1811200280580000080300680780280300100c01380000e00000101180581080480700000000000080580180080100300180180000700000080380080200080d80280000500600300300000480000200180781680100b80200b00280180180680000780380a00480b00180080580000300080080a80800200180d80200280000080000381500000b00100000580000180400280080000280400000280700b01080d00000380000100080000400080200600080080280000280400f80180380300100580401180680780900100000080200c8070130
  | 12 => 0xc0a000000181c05a00000000000008a30401cc800015b07200d845200034081e843c4c00001dd46f67b900006d8cca0000000d9c00078107705540006b5000036448458c406953869c78e28e0954bc000000022b824c48800016940006f73e2a17c74488c439862d02e0d037a80009a83f500002a40003c60a707082f82263d480c0f3a14f2569838d2c1320f60f7481a1133a3860400064c4530f6c40a42b1d90fc4e8c00016e96187104c300000001e65db1be8000d7c29b000000019286f000033000003f000013449226d34498486b67163531cfccf20000419f549c67fe4540ad032a04c26280005ae3ad1af9cec00002e0de198876278f3900b448102830609e2053c74b2cda01ce064121578ed889c30205415b48d62d313b800100a7c32df8000b720001859148f5c1aa0e2a12842e3ed3609e9414662f4208f080d086a258829ca4018a0ff8ae45da5f23b0a1746941f103f1ea097c897295860060e30a0ab0af111a000150000000062525812d41ca0ba071000000048021181400d443e3e491280006f127000009080000001b64e6c5700001bec60c0f815614d008889c21c2110b866bf37511b8000794418065093c507250065c00000040c9a4c34200031400000000002918f990500d323408188503470841d98f3e0000ae0000bd066f1e81e243a60003bb8b610167522b711c05205810c89754a4a203015852450c2741e59bb01b83a708a17001e806e0fe070019006020791dd05221c37482140002891ce0de02be883000197c0001c10000000eb60000000000de00003d00780e5e09d13c0f010781eb0001b440000612f100005d284604c1c780002360eb000000000045d88540002c1389115cbb82de22684b417016f03580007a64bb0001fcc3381963809af070a4e733b9448a1823b40f90fc6ba1402660b2cb202184441e4cde600004084a88c873920215e400018d0ba1b185d07f9267929c1da5fd2e6a0383203fd00000000a268c30f8000fce5f64188000c6c000234a2e091e37203ba2a8c44753000196c1b475c06d8cc098e0c426997b05764ab30e1c544a682f000035c0007952a80cf902056b33d0e540007eb00008940008b9161101c6360002de0000dfe1f830b88406c000030d80000842960000000dc03290b7094400048e17d000034a27d43f01d02ee31a2ec000092c000000000089e67c0479cad0fa6cb3160001160000000125400013d3898d8839e8512e39edc0000df00010740002a23ff8ab844828117210440001043fa86300001ca00006fcf782fd2fe10144dc856441117439c00041e99cc21e4723af0b8c0b47a122200000480ce00b80603861fb00000008f68af3f508005146633e8146cbe21da32f000070c47f3e9923408a50012b88bca0234143189c84543841238d2c8908a02c984dc3be2
  | 13 => 0x5c93af9fb4c827a31bb9f18b4c5042b780a41d60022cc9b7c00215a2b9a1809340001d19704aa40233e50c600000002c9172000046a0a604046b21f90de94642ec6521d31df8e4a04811621909cc4f92bf86ac622000349000000081817c9f6c8865d3000209c00000000000000000aa0000884000000000000082e4f819a147c27c1af01e109019407327f00349fe2b03738e784ea7ad22884802f0310033000041c74e00016545b80000001b0c61a000070000000000031e80004566ba00022600002ce000095076e0003f1026822c00025b1f800006b10000000edc43c1cc12605f848b38594d50cc08d05e990cf4848230d163472870d36a83087265683711aacbc23c34200584c06569322991c7928b32b08adc1281382ce13d42328261909be02ba0bb2d998ac5fc55419180704025b827905285701301ef201097289934f882811c23d2e2982452246700001c455671913295f4c6e5e7000038c0ac14d0000ce80005d1405061439a00000000000000001fc1fb800069a38c06b48407140da03748167d72a480007c647d23b19a00001d9205165cbf03cc3669328b068ad2fca0b0b402eb25b8d485be65312406e0dda7822030960e527550bf99d80000000000b308b00d43d7a12c3ca4da3b8800062661d0d30d708360000001ab05282401020e6400033500000380006b92d4921c5a000c28a0e1ca1c73100010c451074c00022400004df12600000000000001c700425ea04aa080fcc6400000c4835218434680000007733d58000cdc1a800015d454a55822d80007020e639f118cb585380000a4905c7920189b6c5801670aa0970d146dd216a294b107370a99ed513e1341cf842cc965fe2612160f7c7270c19c38bae13b1b805f86e625900394603fa041214a0dc65c69e00010bc21438d35005e813610600e800106c00038380002b076034b838475088f1790618eac4752af84347b040044b051400020709718348b208800012d023a0001f9867c57400020c80000002f42a41f3ce3454a2950278c7888540012705ac23a3e0a1c01b0515396a16c53a000000016c00059f0a398110ee1483611bd91025a13418f707a82da3b218c04665b111c06ec44e00000b06087066641010c007ca62d00014c8c8403a23d1b38996000186000058e000000172851e6ad12208480000001dd8f840000000958d301d058424601f44ba5591268014b888012b880188da63b00000007a25560d8000007a7f60298b9436a0b33270b280ec5451da076d04a58f21e9bf4ab452240a95d820035600006c43e42c903a96b4e04000000151000000007d1a940006c840d9cf02366671df0da4c403fb06880dd06400005691583340001a89e58c9e3ec3b480000000001978000dcc2b200000000000630001d444a400a1058a9c0007ba339000016c8542888
  | 14 => 0x84bcb5e062170927c6285d44311088b001cb37c8000aaa6a815493d000055700000008cc000336a0307c43091871bc859a06c0000f28f842981ef9e2c3da85c0849ccc00000029f0968fb05301dd15080723080559db49147683220770c664361900a4c16402605f8a5c27e63f33a22f81ea31f1f38588c003150f819e00506b044890b0a741c9407935833239d1af17683ba45f3a800504ce2a308e12c89328bc01501489de3ce3bc914c1f22354268c784468b53130e44bd27b10941e9c1ce35027287d50863bd0cda25104638907511684320c63c002f88bc51e2af08dc13200044580000004ac397022c2ca22823c91cc77060645b8bb08f851d24e9eb09bc2e745496c0cf651643d02d456c8740ea1318d046b63c803a48c46131df8d8400019d12f090ce3a5910059e0cb3421d2f1800049e1d03a40aa8a5000012708245623f63dd80004e05dd1a680d49247f802182dc2fa4ea2670660e0a6bb0b1a0e0f985bb0000a3490c5b62b2801000025f15f9de8acc28239500000f64d80001ce08382f10e30438c9a12700000007de7e31b4000041a4dc0000ea8a783ea1508e811640003a28830000000000120ca6c1361f59fd0dc238e00016e800056a3b60281010850000027100c000099954408c6483c89150d3a7b8000206889288629b97b460639213500005dc34404480000008713eb0c9894a67100411c507c6d03d11decf367633ea14340000000ba800000025628310e8cd65473e2104011851a4099d5c8fc0fc1fe00010485d91aa8000d0a36b2a019990bc00000000010da07033514983de59e0fd21ac0004d93e887d086835400015e069e11e1461c180000000001730d2a3802768f64dd062424983d8a6216033f9388da63430788dbc0007670911f640006b313d8d947e063e12503c800022000000000002fb00780004c657b3fe063d0f60673cc20d10f249100000007aa35a419a0e4d107970000ec088477c000205800082133a98e0dde000000183009e5ff2f281a40684aa3bc074800037a3ee8e5cbde21a00004400006272e7a2789ec54310a1a3cd381240179d600002ea269029800089a3f90fdc06621627e89141246ca3878f040b00931cd998074881125d0a0065088e1ba8f349467000b690045ec2301da86e8094629443a2883cc6a125f89ac0da0b93d509a083c1ae1a4017ccb079e04b8d185de65a24d83dc94c0c50ea8cf41088841b69f84f6438c0c71fec000000000000000066c33e9df40008800000000be000030f1b1d0d06c00001dc06c638b0439b149dc00037a1aa400072206916a0c2864618c82b908e43514a8f1c3ae60f21994b8b44000000152c10c83f19103551743da0b987cc0bc41413089f088e2a614d1a1c9d819e0e39d350fe05c2ba00441fa45c3da1b5c43649740e861c7fc0af45b05b09aa
  | 15 => 0x2890a677418b1d508986cc09495f84786c92b00cdc2826a307d8fe4b645d219916281de60840e14410a46a213318e4bf43e42ef0d98a1650a09c8fa4d2214308c11546728a11d0943d0d200000000000003fa1de212108a1310c9800000000000000002ae20802001380008a70f71d08bac26f0001310a9a5a402a800004a5ab00017dc53811a2a610c00000000000b64d2825000000010541ac10f968c1681e73f8800c422152424859800063100000001bc00036e03348a067009e1b6803423f0f090b858a00000f9e687522c30ef10c82e40001d287a40004eb3e59384000151145800000052d02589a4e9e65600d800000000000011b000000032b8000c2a000000040c3ec00004f89051260fe14f90a90ca3383ee1030e2e00000011801d80000c90000d203ee2909e186480000ff00000000001799f485a485542b9ef4b0e7042df0000db087c00000000007e807811bc7ac5b52689024f144bd24a1a645f000044d868060a2223f60720ffa14b16a9abce501882a79cd0cba1e330c0d0037c22e2b184d4ac83c835394908342761f91944e7486c00012e0dfc4f72070d14f4c30410783585c43b3000000108432c2e1163800002021312f0c5c2133e01dfcaba0b0330a19c25874330b1bacfbe3493a0a168e7a4c84559be8f0e26c415
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe509881002eed509881002eec509881002eef409881002eee409881002eed409881002eec409881002eef309881002eee309881002eed309881002eec309881002eef109881002eee109881002eed109881002eec1098810004ff755881001cfe755881001cfc7558810004ff7458810014fe7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810006bf4358810006bd435881002cff725881002eef7258810006ef5258810006ec5258810006ef4258810006ec4258810006ef3258810006ee3258810006ed3258810006ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec215881002cff705881002cfe705881002cfd705881002cfc705881002eee205881002eec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006af4358810006ee4358810006ed4358810006ad4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002eee505881002eed505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002eee105881002eed105881002eec105881004cff769481002cfe7694810004fd769481002cfc769481001e7e65948100067d6594810216be6494810006bd649481020ede6394810006dd639481004eee6294810006ed629481002dfa7094810005f97094810004ff765481002cfe7654810004fd765481002cfc765481001e7e65548100067d6554810005bf745481003dbc7454810206be6454810006bd64548101fede6354810006dd635481004eee6254810006ed625481004cff769081002cfe7690810004fd769081002cfc76908101f67e65908100067d6590810016be6490810006bd64908101eede6390810006dd639081004eee6290810006ed6290810025f67190810005f57190810004ff765081002cfe7650810004fd765081002cfc76508100057f75508100457c75508101e67e65508100067d6550810016be6450810006bd64508101dede6350810006dd635081004eee6250810006ed6250810
  | 1 => 0x90100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002ebe505901002ebd505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002ebe105901002ebd105901002ebc1059010004ff765501002cfe7655010004fd765501002cfc765501001e7e65550100067d6555010016be6455010006bd645501021ede6355010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c100069e7458c10006dd7458c100069d7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006dc5258c10006df4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002ede5058c1002edd5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ed71058c1002ede1058c1002eda1058c1002edd1058c1002ed51058c10026d91058c1002edc1058c1004eef759881004eee759881004eed759881004eec759881004eef749881004eee749881004eed749881004eec7498810006ef5498810006ee5498810006ed5498810006ec549881004eef739881004eee739881004eed739881004eec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ef4398810006af4398810006ee4398810006ed4398810006ad4398810006ec4398810026ef7198810026ee7198810026ed7198810026ec7198810026ef5198810026ee5198810026ed5198810026ec5198810026ef4198810026ee4198810026ed4198810026ec4198810026ef3198810026ee3198810026ed3198810026ec319881002eef709881002eee709881002eed709881002eec709881002eef509881002ee
  | 2 => 0x67f655411001e7c6554110005f77154110025f47154110014ff765011005cfd7650110024fc76501100057f75501100657c7550110006bf6450110016bc6450110005f77150110025f47150110024fe76c8110024fc76c8110006ef62c811004eec62c8110025f671c8110005f571c811002ff010c811004cff7648110004fd7648110024fc7648110006ef624811004eec6248110005f77148110025f4714811002cff755941002e7f7559410004ff7459410014fe7459410014fc74594100467f54594100067e54594100467c5459410004ff735941000cfe7359410004fd735941000cfc73594100467f53594100067e53594100067d53594100467c5359410006bf4359410006bd4359410004ff725941004cfc72594100467f52594100467c5259410024ff7159410024fe7159410024fd7159410024fc71594100267e51594100267c515941002cff705941002cfe705941002cfd705941002cfc705941002e7e505941002e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100063f43594100067e43594100067d43594100063d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941002e7f705941002e7e705941002e7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e7e105941002e7d105941002e7c1059410004ff755901001cfe755901001cfc755901002cff745901002ebf7459010006bf545901003ebe545901003ebc5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d535901003ebf4359010006be4359010006bd435901003ebc4359010004ff725901004cfc725901003ebf425901003ebc4259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc415901002cff705901002cfe705901002cfd705901002cfc705901002ebe405901002ebc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010004bf7359010006be7359010006bd7359010004bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd535
  | 3 => 0xc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d911005ebf43d9110006bd43d911004cfe72d9110004fd72d911005ebc42d9110024fe71d911002cfd71d9110024fc71d911005ebf41d911002cfe70d9110024fd70d911002cfc70d911005ebf40d91100057f75591100657c755911005ebc6459110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c755911005cff7459110006bf7459110004ff735911000cfe7359110004fd735911000cfc73591100067f53591100067d535911005ebf4359110006bd4359110004ff725911004cfc7259110074ff7159110006f7715911008cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc765511004cfe76d891001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006bf43d8910006bd43d8910024fe71d8910024fc71d8910006f631d8910006f531d891002cfe70d891002cfc70d8910006fa30d8910006f930d8910006ef62989100057f75589100657c7558910005bf745891005dbc7458910005df7358910055dc7358910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006bf4358910006bd4358910006ef7258910006ee3258910006ed3258910004ff7158910006f77158910006f63158910006f53158910004ff7058910006fb7058910006fa3058910006f93058910004fe761891004eee6218910006ed621891004cff7694910004fe7694910004fd769491004cfc76949100067f659491001e7c6594910004ff7654910004fe7654910004fd7654910004fc7654910005bf745491005dbc745491004cff7690910004fe7690910004fd769091004cfc7690910006bf6490910016bc6490910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100657c755091002cfc76545100067f655451001e7c6554510005bf745451005dbc7454510005fb705451002df8705451002cfc7650510006bf6450510016bc6450510005fb705051002df8705051002cfe76c851002cfc76c8510006ef62c851004eec62c851002dfa70c8510005f970c8510027f010c851002cfc7648510006ef624851004eec6248510005fb704851002df8704851001cff7654110064fd7654110024fc7654110
  | 4 => 0x9610006bd4359610004ff725961004cfc725961007e7f515961002cfc705961002e7e505961002e7c5059610004ff75592100067f75592100047f755921001cfe755921001cfc75592100067c755921001c7c755921002ebf7459210006bf5459210076bc5459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210076bf4359210006bd4359210004ff725921004cfc7259210076bf4259210076bf415921002cfc705921002ebe405921002ebc4059210004ff765521002cfe7655210004fd765521002cfc7655210004ff7558a1001cfe7558a1001cfc7558a10004ff7458a10014fe7458a10014fc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a10006bf4358a10006bd4358a1002eef7258a10006ef5258a10006ec5258a10006ee3258a10006ed3258a1002cfc7058a1002efa3058a10006f93058a1002eee2058a1002eec2058a1004cff7694a1002cfe7694a10004fd7694a1002cfc7694a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a10005bf7454a10075bc7454a1004cff7690a1002cfe7690a10004fd7690a1002cfc7690a1004eee6290a10006ed6290a10025f67190a10005f57190a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a100057f7550a1007d7c7550a10016be6450a10006bd6450a1004eee6250a10006ed6250a1001cff765461002cfc765461001e7e65546100067d6554610005bf7454610075bc7454610005fb705461002df87054610014ff765061002cfc7650610016be6450610006bd6450610005fb705061002df8705061004eee62c8610006ed62c861002dfa70c8610005f970c861004cff764861004eee6248610006ed6248610027e42148610005fb704861002df8704861001cfe76d95100667e65d9510014fe74d9510004fd74d9510014fc74d95100067e54d95100667c54d9510004ff73d951000cfe73d9510004fd73d951000cfc73d95100667f53d95100067d53d9510006bf43d9510006bd43d951004cfe72d9510004fd72d95100667c52d9510024fe71d951002cfd71d9510024fc71d95100667f51d951002cfe70d9510024fd70d951002cfc70d95100667f50d95100667c6559510005bf745951005dbc7459510064ff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510014fc7459510006bc7459510014bc7459510004ff735951000cfe7359510004fd735951000cfc73595100667f53595100067d5359510006bf4359510006bd4359510004ff725951004cfc725951007cff7159510006f77159510094ff7059510006fb7059510014fe76d911005ebe64d911001cfe75d9110004fd75d911001cfc75d9110006bf54d911005eb
  | 5 => 0x2cfd705842002eef205842002eed205842002ef6105842002ef41058420024ff769442002cfe7694420004fd76944201d6be6494420006bd6494420026f66194420006f56194420004ff7654420004fd765442002cfc765442001e7e65544200067d6554420005bf74544200a5bc74544201c6be6454420006bd6454420026f66154420006f56154420024ff769042002cfe7690420004fd76904200ad7e75904200057d7590420016be6490420006bd649042004dee7290420005ed7290420004ff7650420004fd765042002cfc7650420016be6450420006bd64504200267f7559710004ff7459710006bf7459710004bf7459710014fe7459710014fc7459710006bc7459710014bc74597100067e54597100967c5459710004ff735971000cfe7359710004fd735971000cfc73597100967f53597100067d5359710006bf4359710006bd4359710004ff725971004cfc72597100967f525971002cfc71597100267e51597100267c51597100967f5059710004ff755931001cfe755931001cfc7559310026bf7459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d535931008ebf4359310006bd4359310004ff725931004cfc725931002cfc7159310026be4159310026bc415931008ebf4059310004ff7655310024fe7655310004fd7655310024fc7655310004ff7558b1001cfe7558b1001cfc7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10006bf4358b10006bd4358b10026ef7258b10006ef4258b10006ec4258b10006ee3258b10006ed3258b1002cfc7158b10026f63158b10006f53158b10026ee2158b10026ec2158b1004cff7694b10024fe7694b10004fd7694b10024fc7694b1004eee6294b10006ed6294b1002dfa7094b10005f97094b10004ff7654b10024fe7654b10004fd7654b10024fc7654b1001e7e6554b100067d6554b10005bf7454b1008dbc7454b1004eee6254b10006ed6254b1004cff7690b10024fe7690b10004fd7690b10024fc7690b10004ff7650b10024fe7650b10004fd7650b10024fc7650b100057f7550b100957c7550b1001cff7654310024fc765431001e7e65543100067d6554310005f77154310025f47154310014ff7650310024fc76503100057f75503100957c7550310016be6450310006bd6450310005f77150310025f4715031004eee62c8310006ed62c8310025f671c8310005f571c831004cff764831004eee6248310006ed6248310005f77148310025f4714831002fe8204831002e7f7559610004ff7459610014fe7459610014fc7459610004ff735961000cfe7359610004fd735961000cfc735961007e7f53596100067d5359610006bf435
  | 6 => 0xb42501200bfea4250120007b942501200bfe94250120007a94250120227ea3250120227e932501200bfbb4150120007b94150120007eb2150120007e9215012002cff755942002e7f7559420004ff7459420014fe7459420014fc7459420004ff735942000cfe7359420004fd735942000cfc73594200ae7f53594200067d5359420006bf4359420006bd435942004cff725942004cfe725942004cfd725942004cfc725942004e7e525942004e7c5259420004ff7159420024fc71594200ae7f515942002cfe705942002cfc705942002e7e505942002e7c5059420004ff75590200067f75590200047f755902001cfe755902001cfc75590200067c755902001c7c755902002cff745902002ebf7459020006bf54590200a6be54590200a6bc5459020004ff735902000cfe7359020004fd735902000cfc73590200067f53590200067d53590200a6bf4359020006be4359020006bd43590200a6bc435902004cff725902004cfe725902004cfd725902004cfc725902004ebe425902004ebc4259020004ff7159020024fc71590200a6bf41590200a6bc415902002cfe705902002cfc705902002ebe405902002ebc405902002eef205902002efa205902002eed205902004ef92059020006bf75590200063f7559020006be7559020006bd7559020006bc75590200063c7559020006bf7359020004bf7359020006be7359020006bd7359020004bd7359020006bc7359020006bf53590200063f5359020006be5359020006bd53590200063d5359020006bc535902004ebf725902004ebe725902004ebd725902004ebc725902004ebf525902004ebe525902004ebd525902004ebc525902004ebf325902004ebe325902004ebd325902004ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006bc5159020006bf3159020006be3159020006bd3159020006bc315902004ebf215902004ebe215902004ebd215902004ebc215902002ebf705902002ebe705902002ebd705902002ebc705902002ebf505902002ebe505902002ebd505902002ebc505902002ebf305902002ebe305902002ebd305902002ebc305902002ebf205902002eaf205902002ebe205902002eba205902002ebd205902002ead205902004eb9205902002ebc205902002ebf105902002ebe105902002ebd105902002ebc1059020004ff765502002cfe7655020004fd765502002cfc7655020016be6455020006bd6455020004ff755842001cfe755842001cfc7558420004ff7458420014fe7458420014fc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d5358420006bf4358420006bd435842002ef77158420006f63158420006f5315842004ef7215842004ef4215842002cff7058420
  | 7 => 0x4520004ff7654520004fe7654520004fc765452001e7e65545200067d6554520005bf74545200bdbc7454520005ef725452004dec72545200c76f5254520005fb705452002df87054520004fe7690520004fd7690520024fc76905200c57e75905200057d7590520006bf6490520016bc649052004dee7290520005ed7290520004ff7650520004fe7650520004fc7650520005ee76c852004eee76c85200c5ee75c852004dec75c8520006ef65c8520006ed65c852004def74c8520005ed74c852018eee64c852018eec64c852004def73c852026ded73c8520266ef63c8520266ed63c85202676f53c85202676d53c8520267af43c8520267ad43c8520026ee61c8520026ec61c852002dee70c852002dec70c852004eef60c852004feb60c8520267ea30c8520267e930c852002cfe768852025ded7288520006f76188520026f4618852002dfa7088520005f9708852004fe8208852002cfc7648520006f76148520026f46148520005fb704852002df8704852002cec76485200c5ee75485200c5ec7548520006ef6548520006ed6548520005ef7448520005ed744852015eee644852015eec644852025def734852025ded7348520256ef6348520256ed63485202576f53485202576d5348520257af4348520257ad434852004def714852004fe77148520007e76148520026ee6148520026ec6148520007e46148520026e46148520007e65148520007e55148520257e63148520257e53148520007eb704852002dee704852002dec7048520007e8704852002de8704852004eef604852004feb6048520257ea3048520257e9304852001cff76541200c4fd765412004cfc76541200067f655412001e7c6554120005ef725412004dec7254120005fa769012002efa76901200bdf97490120016fa6490120016f8649012002dfb739012024df9739012023f7b539012023f7953901200bfbb439012023fb9439012002feb729012004dfa729012002df8729012002fe8729012002efb629012002feb6290120247eb5290120247e852901200bfea42901200bfe9429012023fea329012023fe93290120007eb2190120007e92190120014ff76501200bcfd765012004cfc76501200057f75501200c57c7550120006bf6450120016bc6450120005ef725012004dec7250120007ad425012002fb8405012002fe8205012004df87650120016f8765012004cf876501200077b755012000778755012002dfb745012002fbb7450120007bb6450120016fa6450120016f864501200bfb8645012022fbb54501200bfb85450120235fb7350120235f973501202277b53501202277953501200bfbb4350120227b94350120007eb725012004dfa725012004df87250120007e8725012002efb625012002feb625012022feb525012022fe852501200bfb
  | 8 => 0x4ff7159520024fc71595200c67f51595200f4ff7059520006fb7059520014fe76d91200bebe64d912001cfe75d9120004fd75d912001cfc75d9120006bf54d91200bebc54d9120004ff73d912000cfe73d9120004fd73d912000cfc73d91200067f53d91200067d53d91200bebf43d9120006bd43d912004cfe72d912002cfd72d912004cfc72d91200bebf42d9120024fe71d9120004fd71d91200bebc41d912004cfd70d91200bebf40d91200057f75591200c57c75591200bebc6459120004ff75591200067f75591200047f755912001cfe755912001cfc75591200067c755912001c7c75591200bcff7459120006bf7459120004ff735912000cfe7359120004fd735912000cfc73591200067f53591200067d53591200bebf4359120006bd43591200d4ff7259120006ef7259120004ff7159120024fc71591200ecff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc7655120005ef725512004dec725512002cfc76549200067f655492001e7c6554920005bf74549200bdbc74549200c5ef725492004f6c5254920005fb705492002df87054920005ee769092004eee76909200c5ee759092004dec75909200bded7490920016ee6490920016ec6490920297af54909200bfac549092004def739092028ded73909202876f53909202876d53909200bfaf4390920287ad4390920005ed719092004feb709092002dee709092002dec709092004fe8709092004eef609092004feb6090920287ea3090920287e9309092002cfc76509200057f75509200c57c7550920006bf6450920016bc645092004fac4250920005fb705092002df8705092004fe8205092002dec7650920016ec765092002cec76509200076f75509200c5ee75509200c5ec75509200076c75509200c56c755092004def745092004faf7450920007af6450920016ee6450920016ec64509200bfac645092027def735092027ded73509202776f53509202776d53509200bfaf4350920277ad4350920005ef7150920007eb705092002dee705092002dec7050920007e8705092004eef605092004feb60509200bfaf4050920277ea3050920277e9305092001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d8520006bf43d8520006bd43d8520006ee32d8520006ed32d852002cfe70d852002cfc70d8520006fa30d8520006f930d8520006f761985200057f75585200c57c7558520005bf74585200bdbc7458520005df73585200b5dc73585200c57e75185200057d7518520026f66118520006f56118520004fe7694520004fd7694520024fc76945200067f659452001e7c659452004dee7294520005ed729
  | 9 => 0xc73592200067f53592200067d53592200d6bf4359220006bd43592200d6bf4259220004ff7159220024fc71592200d6bf415922002cfc705922002ebe405922002ebc405922002eef205922002eed2059220004ff765522002cfe7655220004fd765522002cfc765522001cff7654a2002cfc7654a2001e7e6554a200067d6554a20005bf7454a200d5bc7454a20005fb7054a2002df87054a20014ff7650a2002cfc7650a200057f7550a200dd7c7550a20016be6450a20006bd6450a20005fb7050a2002df87050a20004ff755862001cfe755862001cfc7558620004ff7458620014fe7458620014fc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d5358620006bf4358620006bd435862002ef77158620006f63158620006f5315862002cfc705862002efa3058620006f9305862002eef205862002eed205862002ef6105862002ef41058620024ff769462002cfe7694620004fd7694620004ff7654620004fd765462002cfc765462001e7e65546200067d6554620005bf74546200d5bc7454620005fb705462002df87054620024ff769062002cfe7690620004fd76906200dd7e75906200057d759062004dee7290620005ed7290620004ff7650620004fd765062002cfc7650620016be6450620006bd6450620026f66188620006f5618862002dfa7088620005f97088620024ff7648620026f66148620006f5614862004fe42148620005fb704862002df8704862002dfb76502200a6fb76502200077b755022000778755022002fbb745022002fbb6450220016fa645022002ef8645022002fb864502202afbb54502200d7b854502202a5fb73502202a5f9735022029f7b535022029f7953502200d7bb435022029fb9435022004dfa725022004df872502200d7bb4250220007b942502200d7bb4150220007b9415022001cfe76d95200c67e65d952004dee72d952002ded72d95200c76f52d9520014fe74d9520004fd74d9520014fc74d95200067e54d95200c67c54d9520004ff73d952000cfe73d9520004fd73d952000cfc73d95200c67f53d95200067d53d9520006bf43d9520006bd43d952004cfe72d952002cfd72d95200c6ed72d952002ced72d952004cfc72d95200c67f52d95200c6ef52d95200c66f52d95200c6ec52d9520024fe71d9520004fd71d95200c67c51d952004cfd70d95200c67f50d95200c67c6559520005bf74595200bdbc74595200c4ff75595200067f7559520004ff7459520006bf7459520004bf7459520014fe7459520014fc7459520006bc7459520014bc7459520004ff735952000cfe7359520004fd735952000cfc73595200c67f53595200067d5359520006bf4359520006bd43595200dcff7259520006ef72595200c6ef52595200c6ec5259520
  | 10 => 0x9320004ff735932000cfe7359320004fd735932000cfc73593200067f53593200067d53593200eebf4359320006bd435932002cfc725932004ebe425932004ebc4259320004ff7159320024fc71593200eebf405932004efa205932004ef92059320004ff765532004cfe7655320004fd765532004cfc7655320005ef725532004dec725532004def7650b200a6ef7650b200076f7550b200f5ee7550b200f5ec7550b200076c7550b200f56c7550b2004faf7450b2004faf6450b20016ee6450b2004eec6450b2004fac6450b202cdef7350b202cded7350b202c76f5350b202c76d5350b200efaf4350b202c7ad4350b20005ef7150b2002dee7050b2002dec7050b200efaf4050b20004ff755872001cfe755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d5358720006bf4358720006bd435872002cfc725872004eee3258720006ed325872004ef77158720006f74158720006f44158720006f63158720006f5315872004ef7215872004ef42158720024ff769472004cfe7694720004fd769472004dee7294720005ed7294720026f66194720006f56194720004ff7654720004fd765472004cfc765472001e7e65547200067d6554720005bf74547200edbc7454720005ef725472004dec72547200f76f5254720026f66154720006f56154720024ff769072004cfe7690720004fd76907200f57e75907200057d759072004dee7290720005ed7290720004ff7650720004fd765072004cfc765072004dee725072004def7648720006ef76487200f5ee75487200f5ec754872004eef6548720006ed6548720005ef7448720005ed744872015eee644872004eec64487202bdef73487202bded734872004eef63487202b6ed63487202b76f53487202b76d53487202b7af43487202b7ad434872004fe77148720026ee6148720026ec6148720007e65148720007e551487202b7e631487202b7e5314872002dee704872002dec704872001cff765432004cfc765432001e7e65543200067d6554320005ef725432004dec7254320014ff765032004cfc76503200057f75503200f57c7550320016be6450320006bd6450320005ef725032004dec7250320007ad425032002e7f7559620004ff7459620014fe7459620014fc74596200067e54596200de7c5459620004ff735962000cfe7359620004fd735962000cfc73596200de7f53596200067d5359620006bf4359620006bd43596200de7f5259620004ff7159620024fc71596200de7f515962002cfc705962002e7e505962002e7c5059620004ff755922001cfe755922001cfc755922002ebf7459220006bf54592200d6bc5459220004ff735922000cfe7359220004fd735922000cf
  | 11 => 0x7ac6250940005bf7150940007bb705094002dbe705094002dbc7050940007b87050940016bf6050940017bb60509400067f65d85400067c65d854001cfe75d8540004fd75d854001cfc75d854002cfd74d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d8540076bf43d8540006bd43d854004cfe72d8540004fd72d8540076f641d8540076f541d8540006f731d8540006f431d85401057e75985400057d75985400067f65985400067c6598540005ee7298540005ed7298540006f7619854005df970985400057f75585401057c75585400067f65585400067c655854008dfb70585400067f65185400067c6518540026f66118540006f56118540004fe7694540004fd7694540024fc76945400067f659454001e7c6594540015be7494540005bd7494540004ff7654540004fe7654540004fc76545400067f655454001e7c6554540005bf7454540015bc74545401c73c545454002cbc7650540105be7550540105bc75505400073f65505400073c65505402ddbf73505402ddbd73505402d6bf63505402d6bd63505402d73f53505402d73d5350540005bf7250540015bf7150540017b77150540007b76150540026be6150540026bc6150540007b46150540007bb705054002dbe705054002dbc7050540007b87050540016bf6050540017bb6050540004fe76c8540004fd76c854004cfc76c85400067f65c85401967c65c8540015be74c8540005bd74c8540006ef62c854004eec62c854018faf42c854002dfa70c8540005f970c8540004fe7688540004fd7688540024fc76885400067f658854017e7c6588540015be7488540005bd7488540006f76188540026f46188540004ff7648540004fe7648540004fc76485400067f65485401667c6548540015be7448540005bd7448540006ef624854004eec624854015faf4248540006f76148540026f46148540004fe7608540004fd7608540024fc76085401057e75085400057d75085400067f650854014e7c6508540015be7408540005bd740854002dfa7008540005f9700854001cff7654140014fe7654140124fd7654140014fc76541400067f655414001e7c6554140005bf7454140015bc745414002fb8405414004e7f7559720004ff7459720006bf7459720004bf7459720014fe7459720014fc7459720006bc7459720014bc74597200067e54597200f67c5459720004ff735972000cfe7359720004fd735972000cfc73597200f67f53597200067d5359720006bf4359720006bd435972002cfc725972004eec725972002cec72597200f6ef525972004e7e525972004e7c525972004eec5259720004ff7159720024fc71597200f67f515972004eef21597200f67f5059720004ff755932001cfe755932001cfc755932004ebf745
  | 12 => 0xe74d95401367d74d95400063d74d95401367c74d95400067f73d95400047f73d95400067e73d95400067d73d95400047d73d95400067c73d95401367f43d95401363f43d95401367e43d95401367d43d95400063d43d95401367c43d95400067f72d95400067e72d95400067d72d95400067c72d95401367f42d95401367e42d95401367d42d95401367c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95401367f41d95401367e41d95401367d41d95401367c41d95400067f31d95400067e31d95400067d31d95400067c31d95401367f70d954030e7e70d95401367d70d954030e7c70d95401367f40d954030e7e40d954030e7c40d95400067f30d954030e7e30d95400067d30d954030e7c30d954030e7e20d954030e7c20d954030e7e10d954030e7c10d95401067c6559540305fb7059540134ff75595400067f7559540124ff7459540006bf7459540106bf5459540126bc5459540004ff735954000cfe7359540004fd735954000cfc73595401067f53595400067d5359540126bf4359540006bd4359540004ff725954004cfc7259540004ff7159540024fc7159540304ff7059540006fb70595401357e76195401067e76195401347e76195402ff3f74195402f73c74195402fe7f64195401057f73195400057d73195400067f63195400067e63195400067d63195400067c63195402f73f43195400073d43195402f73f42195402f73f41195402f67f60195402f77b40195402ff3e40195402ff3c40195402f77840195400067f65d89400067c65d894001cfe75d8940004fd75d894001cfc75d894002cfd74d8940004ff73d894000cfe73d8940004fd73d894000cfc73d89400067f53d89400067d53d89400d6bf43d8940006bd43d89400d6ee42d89400d6ed42d8940006ef32d8940006ec32d8940024fe71d8940004fd71d89401057e75989400057d75989400067f65989400067c6598940006ef6298940005f67198940005f571989400bdf970989400057f75589401057c75589400067f65589400067c65589400edfb70589400067f65189400067c651894004eee6218940006ed6218940004fe7694940004fd769494004cfc76949400067f659494001e7c6594940015be7494940005bd74949402173c549494002dfa7094940005f97094940004ff7654940004fe7654940004fc76549400067f655494001e7c6554940005bf7454940015bc745494002cbc76509400073f7550940105be7550940105bc75509400073c75509401053c75509400073f65509400073c65509402edbf73509402edbd73509402e6bf63509402e6bd63509402e73f53509402e73d5350940015bf7250940017af7250940007af625094004ebe625094004ebc6250940
  | 13 => 0x96401267f54596401267d5459640004ff735964000cfe7359640004fd735964000cfc73596401167f53596400067d5359640126bf4359640006bd4359640004ff725964004cfc72596401167c5259640004ff7159640024fc71596401167f515964002cfe705964002cfc705964002e7e505964002e7c5059640004ff7558a4001cfe7558a4001cfc7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a400067f5358a400067d5358a400bebf4358a40006bd4358a4002eef7258a40006ef5258a40006ec5258a400beee4258a400beed4258a40006ee3258a40006ed3258a40004ff7158a40024fc7158a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a4004cff7694a4002cfe7694a40004fd7694a4001e7e6594a400067d6594a4002dfa7094a40005f97094a40004ff7654a40004fd7654a4002cfc7654a40005bf7454a40015bc7454a40004ff755864001cfe755864001cfc7558640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d535864005ebf4358640006bd4358640004ff725864004cfc725864002ef7715864005ef6415864005ef54158640006f63158640006f5315864002cfc705864002ebf405864002ebd405864002ef6105864002ef41058640024ff769464002cfe7694640004fd7694640004ff7654640004fd765464002cfc765464001e7e65546400067d6554640005bf7454640015bc745464004cff76c864002cfe76c8640004fd76c864004eee62c8640006ed62c864002dfa70c8640005f970c8640024ff768864002cfe7688640004fd7688640004ff7648640004fd764864002cfc7648640005bf7448640015bc744864004eee6248640006ed6248640024ff760864002cfe7608640004fd76086401157e75086400057d750864002dfa7008640005f9700864001cfe76d95401067e65d9540015be74d954002dbd74d95401073f54d954002cff74d9540014fe74d954002cfd74d9540106bd74d954002cbd74d9540014fc74d95401367f54d9540106bf54d95401063f54d95401367d54d9540136bc54d9540004ff73d954000cfe73d9540004fd73d954000cfc73d95401067f53d95400067e53d95400067d53d95401067c53d9540136bf43d9540006bd43d954004cfe72d9540004fd72d95401067f52d95401067c52d9540024fe71d9540004fd71d95401067f51d95401067c51d9540014fd70d95401067f50d95402f57e76d954001c7e76d95401373e74d95400073d74d95400057f73d95400057d73d95400067f63d95400067e63d95400067d63d95400067c63d95401373f43d95400073d43d95401373f42d95401373f41d95401377b40d954030f3e40d954030f3c40d95401377840d954030e7f74d95401367e74d95401363
  | 14 => 0x4cff76c865002cfe76c8650004fd76c865018ebe64c8650006bd64c865004eee62c8650006ed62c8650024ff768865002cfe7688650004fd7688650176be6488650006bd648865004eee6288650006ed6288650004ff7648650004fd764865002cfc76486500057f754865001d7c754865015ebe6448650006bd644865004eee6248650006ed6248650024ff760865002cfe7608650004fd760865001d7e75086500057d7508650146be6408650006bd640865004eee6208650006ed6208650014fe76d9150126be64d915002cfd75d9150014fc75d9150126be54d9150116bd54d9150004ff73d915000cfe73d9150004fd73d915000cfc73d91501167f53d91500067d53d9150126bf43d9150006bd43d915004cfe72d9150004fd72d9150126bc42d9150024fe71d9150004fd71d9150126bc41d915001cfd70d9150126bf40d9150126bc6459150325fb705915002cfd75d8950014fe74d8950004fd74d8950014fc74d8950004ff73d895000cfe73d8950004fd73d895000cfc73d89500de7f53d89500067d53d8950006bf43d8950006bd43d89500deee52d89500deed52d8950024fe71d8950004fd71d89500de7f51d8950006ef62989500c5f97098950005bf7458950125bc74589500f5fb705895004eee6218950006ed6218950004fe7690950004fd769095004cfc7690950006bf6490950016bc6490950004ff7650950004fe7650950004fc76509500057f755095001d7c755095002cfd75d8550014fe74d8550004fd74d8550014fc74d8550004ff73d855000cfe73d8550004fd73d855000cfc73d855007e7f53d85500067d53d8550006bf43d8550006bd43d855004cfe72d8550004fd72d855007ef651d855007ef551d8550006f76198550065f97098550005bf7458550125bc7458550095fb7058550005ee7218550005ed7218550026f66118550006f5611855002c7c76545500073f74545500073c74545501c67e64545501c67c645455031d7f735455031d7d73545503167f63545503167d63545503173f43545503173d43545500067f625455001d7f715455001f7771545500077761545500267e61545500267c61545500077461545500077b705455002d7e705455002d7c705455000778705455001e7f605455001f7b6054550004fe7690550004fd7690550024fc769055001d7e75905500057d7590550006bf6490550016bc6490550005ee7290550005ed7290550004ff7650550004fe7650550004fc7650550004fe76c8550004fd76c855004cfc76c855004eee62c8550004fe7688550004fd7688550024fc768855001d7e75885500057d7588550007755188550004ff7648550004fe7648550004fc7648550007755148550004fe7608550004fd7608550024fc760855001d7e75085500057d750855002e7f755
  | 15 => 0xc3198a5002eef7098a5002eee7098a5002eed7098a5002eec7098a5002eef5098a5002eee5098a5002eed5098a5002eec5098a5002eef4098a5002eee4098a5002eed4098a5002eec4098a5002eef3098a5002eee3098a5002eed3098a5002eec3098a5002eef1098a5002eee1098a5002eed1098a5002eec1098a50004ff7458a50014fe7458a50014fc7458a50004ff7358a5000cfe7358a50004fd7358a5000cfc7358a500c67f5358a500067d5358a50006bf4358a50006bd4358a5002eef7258a500c6ee5258a500c6ed5258a50006ef4258a50006ec4258a50006ef3258a50006ee3258a50006ed3258a50006ec3258a50004ff7158a50024fc7158a5002cfc7058a5002eee2058a5002eec2058a500c6ee7558a500c6ed7558a500c6ec7558a50006ef7458a50006ee7458a50006ed7458a50006ec7458a500c6ef5458a500c6ee5458a500c6ed5458a500c6ec5458a50006ef7358a50006ee7358a50006ed7358a50006ec7358a500c6ef5358a500c66f5358a500c6ee5358a500c6ed5358a500066d5358a500c6ec5358a50006ef4358a50006af4358a50006ee4358a50006ed4358a50006ad4358a50006ec4358a50006ef7158a50006ee7158a50006ed7158a50006ec7158a500c6ef5158a500c6ee5158a500c6ed5158a500c6ec5158a50006ef4158a50006ec4158a50006ef3158a50006ee3158a50006ed3158a50006ec3158a5002eef7058a5002eee7058a5002eec7058a5002eef5058a5002eee5058a5002eed5058a5002eec5058a5002eef4058a5002eee4058a5002eed4058a5002eec4058a5002eef3058a5002eee3058a5002eed3058a5002eec3058a5002eef1058a5002eee1058a5002eed1058a5002eec1058a5004cff7690a5002cfe7690a50004fd7690a5001d7e7590a500057d7590a50016be6490a50006bd6490a501373c5490a5004eee6290a50006ed6290a50004ff7650a50004fd7650a5002cfc7650a500057f7550a5001d7c7550a50016be6450a50006bd6450a5004eee6250a50006ed6250a50004ff7458650014fe7458650014fc74586500067e54586500667c5458650004ff735865000cfe7358650004fd735865000cfc73586500667f53586500067d5358650006bf4358650006bd4358650004ff725865004cfc725865002ef77158650066f65158650066f55158650006f63158650006f5315865002cfc705865002e7f505865002e7d505865002ef6105865002ef41058650024ff769065002cfe7690650004fd769065001d7e75906500057d7590650016be6490650006bd64906501373c5490650005ee7290650005ed7290650006ee6290650006ed6290650004ff7650650004fd765065002cfc76506500057f755065001d7c7550650016be6450650006bd6450650006ee6250650006ed6250650
  | 16 => 0x9021006bd435902104cfe725902104cfc725902104ebe425902104ebc4259021024fe7159021024fc7159021026be4159021026bc4159021004ff705902102cfc7059021146bf4059021004ff7655021024fe7655021004fd7655021024fc765502101e7e65550210067d6555021004ff755802101cfe755802101cfc7558021004ff7458021014fe7458021014fc7458021004ff735802100cfe7358021004fd735802100cfc73580210067f53580210067d5358021006bf4358021006bd4358021026ef2158021026ed2158021026fb7058021006fa3058021006f9305802104efb205802104ef82058021026fb1058021026f8105802102ebf74592501367e5459250136be54592501363e5459250106bd54592501367c5459250004ff735925000cfe7359250004fd735925000cfc73592501067f53592500067d5359250136bf4359250006be4359250006bd4359250136bc4359250004ff725925004cfc7259250136bf4259250136bc4259250004ff7159250024fc7159250136bf4159250136bc415925002cfe705925002cfc705925002ebe405925002ebc4059250106be7559250106bd7559250136bc75592501363c7559250006bf7359250004bf7359250006be7359250006bd7359250004bd7359250006bc7359250106bf53592501063f5359250106be5359250106bd53592500063d5359250106bc5359250006bf7259250006be7259250006bd7259250006bc7259250106bf5259250106be5259250106bd5259250106bc5259250006bf3259250006be3259250006bd3259250006bc3259250006bf7159250006be7159250006bd7159250006bc7159250106bf5159250106be5159250106bd5159250106bc5159250006bf3159250006be3159250006bd3159250006bc315925002ebf705925002ebe705925002ebc705925002ebf505925002ebe505925002ebd505925002ebc505925002ebf305925002ebe305925002ebd305925002ebc305925002ebf205925002ebe205925002ebd205925002ebc205925002ebf105925002ebe105925002ebd105925002ebc105925004eef7598a5004eee7598a5004eec7598a5004eef7498a5004eee7498a5004eed7498a5004eec7498a500f6ef5498a500f6ee5498a500066e5498a500f6ed5498a500f6ec5498a500f66c5498a5004eef7398a5004eee7398a5004eed7398a5004eec7398a500f6ef5398a500f66f5398a500f6ee5398a500f6ed5398a500066d5398a500f6ec5398a50006ef4398a50006af4398a50006ee4398a50006ed4398a50006ad4398a50006ec4398a5004eef7198a5004eee7198a5004eed7198a5004eec7198a500f6ef5198a500f6ee5198a500f6ed5198a500f6ec5198a50006ef4198a50006ec4198a50006ef3198a50006ee3198a50006ed3198a50006e
  | 17 => 0x32fb54354521007e7725452104df6725452104df47254521007e47254521026f76254521027e76254521167775254521167e65254521007755254521167e55254521007655254521337e74254521337e4425452132fe6325452132fe53254521167775054521014ff765052115cfd765052104cfc7650521006bf6450521016bc6450521005ef725052104dec725052101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006bf43d8121006bd43d8121006ee32d8121006ed32d8121006f631d8121006f531d8121006fb60981210057f75581211657c7558121005bf745812115dbc7458121005df7358121155dc735812115dbe7418121005bd741812102efa6018121006f96018121024ff75594210267f7559421004ff7459421006bf7459421004bf7459421014fe7459421014fc7459421006bc7459421014bc745942114e7f54594210067e545942114e7c5459421004ff735942100cfe7359421004fd735942100cfc735942114e7f53594210067e53594210067d535942114e7c5359421006bf4359421006bd435942104cfe725942104cfc725942104e7e525942104e7c5259421024fe7159421024fc71594210267e51594210267c5159421026ef2159421026f62159421026ed215942104ef52159421004ff705942102cfc705942114e7f505942114e7c50594210067f74594210063f74594210067e74594210067d74594210067c74594210063c74594210067f73594210047f73594210067e73594210067d73594210047d73594210067c73594210067f43594210063f43594210067e43594210067d43594210063d43594210067c435942104e7f725942104e7e725942104e7d725942104e7c725942104e7f425942104e7e425942104e7d425942104e7c425942104e7f325942104e7e325942104e7d325942104e7c32594210267f71594210267e71594210267d71594210267c71594210267f41594210267e41594210267d41594210267c41594210267f31594210267e31594210267d31594210267c31594210267f21594210266f21594210267e21594210267621594210267d21594210266d215942104e7521594210267c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067c40594210067f30594210067e30594210067d30594210067c305942104e7f205942104e7e205942104e7d205942104e7c20594210267f10594210267e10594210267d10594210267c1059421004ff755902101cfe755902101cfc7559021024ff7459021026bf7459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021146bf435
  | 18 => 0xd72d912115eed72d9121024ed72d912115ebf42d912115eef42d912115eec42d912104cfd71d912115ebf41d912102cfe70d9121004fd70d912115ebc40d91210057f75591211657c755912115ebc6459121004ff75591210067f75591210047f755912101cfe755912101cfc75591210067c755912101c7c755912115cff7459121006bf7459121004ff735912100cfe7359121004fd735912100cfc73591210067f53591210067d535912115ebf4359121006bd4359121174ff7259121006ef725912115eef425912115eec425912118cff7159121006f77159121004ff705912102cfc705912115ebf4059121004ff7655121004fe7655121004fd7655121004fc7655121005ef725512104dec7255121005ee769492104eee7694921165ed759492101eee659492101eec659492115dee749492104dec749492137f6e54949211676c549492104def7394921375ed73949211676f539492136f6d539492136faf439492136fad439492104fe77194921025ee7194921025ec719492104fe4719492104eef619492104fe7619492136fe6319492136fe53194921005ed7094921024fc76549210067f655492101e7c6554921005bf745492115dbc745492104f6c5254921005f77154921025f4715492104fe42154921025ec765492101eec7654921024ec765492104def755492104f6f75549210076f655492101eee655492101eec65549211676c6554921007af745492115dee745492115dec7454921007ac745492115dac7454921365ef7354921365ed73549211676f535492135f6d535492135faf435492135fad4354921007e77154921025ee7154921025ec7154921007e4715492104eef615492104fe761549211676f515492135fe6315492135fe53154921005ef7054921024fc76509210057f75509211657c7550921006bf6450921016bc645092115def725092104fac4250921005f77150921025f47150921005f67694521026f67694521165f5759452101ef6659452101ef46594521025f77394521355f57394521167775394521347755394521347b74394521347b54394521027e7729452104df67294521025f47294521027e47294521026f76294521027e76294521167e65294521167e5529452134fe7429452134fe44294521347e63294521347e5329452101cff7654521164fd765452104cfc76545210067f655452101e7c6554521005bf745452115dbc7454521005ef725452104dec72545210076d5254521027745154521027e4215452104df4765452101ef4765452104cf47654521025f7755452102777755452100777655452101ef6655452101ef46554521167746554521007b77454521007b4745452133776545452116774545452133df7735452133df5735452116777535452132f75535452132fb74354521
  | 19 => 0x9621004ff735962100cfe7359621004fd735962100cfc735962117e7f53596210067d5359621006bf4359621006bd435962117e7f5259621024fc71596210267e51596210267c5159621026ef2159621026ed2159621004ff705962102cfc705962117e7f5059621004ff755922101cfe755922101cfc7559221026bf7459221006bf5459221176bc5459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d5359221176bf4359221006bd4359221176bf4259221024fc7159221026be4159221026bc4159221004ff705922102cfc7059221176bf4059221004ff7655221024fe7655221004fd7655221024fc765522101cff7654a21024fc7654a2101e7e6554a210067d6554a21005bf7454a21175bc7454a21005f77154a21025f47154a21014ff7650a21024fc7650a210057f7550a2117d7c7550a21016be6450a21006bd6450a21005f77150a21025f47150a21025f7765462114ef7765462102777755462102777655462101ef66554621026f46554621027746554621007b77454621007b4745462139776545462117f74545462138df7735462138df5735462117f775354621387755354621387b74354621387b5435462104df6725462104df4725462117f77525462100775525462117f775054621004ff755822101cfe755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d5358221006bf4358221006bd4358221024fc7158221026f63158221006f53158221026ef2158221026ed2158221026fb7058221006fa3058221006f93058221026fb1058221026f8105822101cfe76d95211667e65d9521014fe74d9521004fd74d9521014fc74d95210067e54d95211667c54d9521004ff73d952100cfe73d9521004fd73d952100cfc73d95211667f53d95210067d53d9521006bf43d9521006bd43d9521024fd72d95211667f52d952104cfd71d95211667f51d952102cfe70d9521004fd70d95211667c50d95211667c6559521005bf745952115dbc7459521164ff75595210067f7559521004ff7459521006bf7459521004bf7459521014fe7459521014fc7459521006bc7459521014bc7459521004ff735952100cfe7359521004fd735952100cfc73595211667f53595210067d5359521006bf4359521006bd435952117cff7259521006ef7259521194ff7159521006f77159521004ff705952102cfc7059521014fe76d912115ebe64d912104dee72d9121025ed72d912115faf42d912101cfe75d9121004fd75d912101cfc75d9121006bf54d912115ebc54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d912115ebf43d9121006bd43d9121024f
  | 20 => 0x6ef629894115df571989410057f75589411a57c755894118df7715894104eee6218941006ed6218941004fe7694941004fd769494104cfc76949410067f659494101e7c6594941004ff7654941004fe7654941004fc7654941005bf7454941015bc745494101cff7654541014fe76545411c4fd7654541014fc76545410067f655454101e7c6554541005bf7454541015bc7454541027b4415454101cfe75d8141004fd75d814101cfc75d8141024fd74d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d814108ebf43d8141006bd43d814104cfe72d8141004fd72d814108efa40d8141006fb60981410057f75581411a57c7558141005ee7218141005ed721814102efa6018141006f9601814104e7f7559721004ff7459721014fe7459721014fc7459721004ff735972100cfe7359721004fd735972100cfc73597211967f53597210067d5359721006bf4359721006bd4359721024fc725972104e7e525972104e7c52597211967f515972104ef6215972104ef52159721004ff705972102cfc7059721004ff75593210067f75593210047f755932101cfe755932101cfc75593210067c755932101c7c755932104ebf7459321006bf545932118ebc5459321004ff735932100cfe7359321004fd735932100cfc73593210067f53593210067d535932118ebf4359321006bd4359321024fc725932104eec7259321024ec725932118eef425932104ebe425932104ebc425932104eec425932118ebf4159321004ff705932102cfc705932118ebf405932104eef2059321004ff765532104cfe7655321004fd765532104cfc7655321005ef725532104dec725532104def7654b2114eef7654b2104f6f7554b2104f6f6554b2101eee6554b2104eec6554b2104f6c6554b21007af7454b2118dee7454b2118dec7454b21007ac7454b2118dac7454b213a5ef7354b213a5ed7354b211976f5354b2139f6d5354b2139faf4354b2139fad4354b21025ee7154b21025ec7154b211976f5154b21005ef7054b2101cff765472104cfc765472101e7e65547210067d6554721005bf745472118dbc7454721005ef725472104dec72547210076d5254721014ff765072104cfc7650721016be6450721006bd6450721005ef725072104dec7250721004ff755832101cfe755832101cfc7558321004ff7458321014fe7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d5358321006bf4358321006bd4358321024fc725832104eee3258321006ed325832104efb7058321006fb5058321006f85058321006fa3058321006f9305832104efb205832104ef820583210267f7559621004ff7459621014fe7459621014fc74596210067e545962117e7c545
  | 21 => 0xc3258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a4102cfc7058a41006ef7558a41006ee7558a41006ed7558a41006ec7558a4115eee7458a4115eed7458a4115eec7458a4115eef5458a4115eee5458a4115eed5458a4115eec5458a41006ef7358a41006ee7358a41006ed7358a41006ec7358a41006ef5358a410066f5358a41006ee5358a41006ed5358a410066d5358a41006ec5358a4115eef4358a4115eaf4358a4115eee4358a4115eed4358a41006ad4358a4115eec4358a41026ef7158a41026ee7158a41026ec7158a41026ef5158a41026ee5158a41026ed5158a41026ec5158a41026ef4158a41026ee4158a41026ed4158a41026ec4158a41026ef3158a41026ee3158a41026ed3158a41026ec3158a41006ef7058a41006ee7058a41006ed7058a41006ec7058a41006ef5058a41006ec5058a4115eef4058a4115eee4058a4115eed4058a4115eec4058a41006ef3058a41006ee3058a41006ed3058a41006ec3058a41026ef1058a41026ee1058a41026ed1058a41026ec1058a4104cff7694a41024fe7694a41004fd7694a4101e7e6594a410067d6594a41015be7494a41005bd7494a412173c5494a4104eee6294a41006ed6294a41004ff7654a41004fd7654a41024fc7654a4101e7e6554a410067d6554a41005bf7454a41015bc7454a4104eee6254a41006ed6254a41004ff755824101cfe755824101cfc7558241006bf545824105ebc5458241004ff735824100cfe7358241004fd735824100cfc73582410067f53582410067d535824105ebf4358241006bd4358241004ff725824104cfc7258241024fc7158241026bf4158241026bd4158241026fb705824105efa4058241006fa3058241006f93058241026fb1058241026f8105824101cfe76d95411a67e65d9541024ff74d9541024fd74d95411d67f54d95411d67d54d9541004ff73d954100cfe73d9541004fd73d954100cfc73d95411a67f53d95410067d53d95411d6bf43d9541006bd43d954104cfe72d9541004fd72d95411a67c52d9541014fd71d95411a67f51d954102cfe70d9541004fd70d95411a67c50d95411a67c65595413adf771595411d4ff75595410067f75595411c4ff7459541006bf74595411b4bf74595411c67e54595411c67c5459541004ff735954100cfe7359541004fd735954100cfc73595411a67f53595410067d53595411c6bf4359541006bd4359541004ff725954104cfc72595413acff7159541006f77159541004ff705954102cfc705954101cfe75d8941004fd75d894101cfc75d8941024fd74d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d8941176bf43d8941006bd43d8941176ee42d8941176ed42d894102cfe70d8941004fd70d8941176bf40d8941
  | 22 => 0x96411b6bf54596411b63f54596411c67d54596411c6bc5459641004ff735964100cfe7359641004fd735964100cfc73596411b67f53596410067e53596410067d53596411b67c53596411c6bf4359641006bd4359641004ff725964104cfc72596411b67f52596411b67c5259641024fe7159641024fc71596410267e51596410267c5159641004ff705964102cfc70596411b67f50596411b67c50596411c67f74596410063f74596411c67e74596411c67d74596411c67c74596411c63c74596410067f73596410047f73596410067e73596410067d73596410047d73596410067c73596411c67f43596411c63f43596411c67e43596411c67d43596410063d43596411c67c43596410067f72596410067e72596410067d72596410067c72596411c67f42596411c67e42596411c67d42596411c67c42596410067f32596410067e32596410067d32596410067c32596410267f71596410267e71596410267d71596410267c71596410267f41596410267e41596410267d41596410267c41596410267f31596410267e31596410267d31596410267c31596410267f21596410267e21596410267d21596410267c21596410067f70596410067e70596410067d70596410067c70596411c67f40596411c67e40596411c67d40596411c67c40596410067f30596410067e30596410067d30596410067c30596410267f10596410267e10596410267d10596410267c105964104eef7598a4104eee7598a4104eed7598a4104eec7598a4104eef7498a4104eee7498a4104eec7498a4118eef5498a41006af5498a4118eee5498a4118eed5498a4118eec5498a4118eac5498a4104eef7398a4104eee7398a4104eed7398a4104eec7398a41006ef5398a410066f5398a41006ee5398a41006ed5398a410066d5398a41006ec5398a4118eef4398a4118eaf4398a4118eee4398a4118eed4398a41006ad4398a4118eec4398a41026ef7198a41026ee7198a41026ed7198a41026ec7198a41026ef5198a41026ee5198a41026ed5198a41026ec5198a41026ef4198a41026ee4198a41026ed4198a41026ec4198a41026ef3198a41026ee3198a41026ed3198a41026ec3198a4104eef7098a4104eee7098a4104eed7098a4104eec7098a41006ef5098a41006ec5098a4118eef4098a4118eee4098a4118eed4098a4118eec4098a41006ef3098a41006ee3098a41006ed3098a41006ec3098a41026ef1098a41026ee1098a41026ed1098a41026ec1098a41004ff7558a4101cfe7558a4101cfc7558a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a4115ebf4358a41006bd4358a41026ef7258a41006ef5258a41006ec5258a4115eee4258a4115eed4258a41006ef3258a41006ee3258a41006ed3258a41006e
  | 23 => 0x6bf32d9151006be32d9151006bd32d9151006bc32d91511b6bf71d91513debe71d91511b6bd71d91513debc71d91511b6bf51d91513debe51d91513debc51d9151006bf31d91513debe31d9151006bd31d91513debc31d91513debe21d91513debc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d91511b6bf50d91511b6be50d91511b6bd50d91511b6bc50d9151006bf30d9151006be30d9151006bd30d9151006bc30d91513debf10d91513debc10d91511c6bc64591513d5f771591511b5be76191511c6be76191513cf3f75191511c73c75191513cebf65191511c5bf7319151005bd7319151006bf6319151006be6319151006bd6319151006bc63191513c73f53191510073d53191513c73f52191513aebf61191513c7b751191513cf3e51191513cf3c51191513c7b451191513c73f5019151006bf64d8951006bc64d8951024fd75d8951014fe74d8951004fd74d8951014fc74d8951004ff73d895100cfe73d8951004fd73d895100cfc73d895117e7f53d89510067d53d8951006bf43d8951006bd43d895117eee52d895117eed52d8951006ef32d8951006ec32d895102cfe70d8951004fd70d89511c5be7498951005bd7498951006bf6498951006bc6498951006ef6298951165f57198951005fa7098951005f97098951005bf74589511c5bc7458951006bf6458951006bc6458951195f77158951006bf6418951006bc641895104eee6218951006ed62189510247c76549510073f74549511c57e74549511c57c74549510073c74549511c53c74549510073f64549510073c64549513bd7f73549513bd7d73549513b67f63549513b67d63549513b73f43549513b73d435495101d7f725495101f6f72549510076f625495104e7e625495104e7c62549510076c62549510077771549510257e71549510257c715495100774715495101e7f615495101f7761549510057f7054951004fe7690951004fd769095104cfc769095101d7e75909510057d7590951006bf6490951016bc64909511c73c5490951025f67190951005f57190951004ff7650951004fe7650951004fc76509510057f755095101d7c7550951006bf6450951016bc6450951006bf64d8151006bc64d8151024fd75d8151014fe74d8151004fd74d8151014fc74d8151004ff73d815100cfe73d8151004fd73d815100cfc73d81510967f53d81510067d53d8151006bf43d8151006bd43d815104cfe72d8151004fd72d8151096fa50d8151006fb30d8151006f830d81511c5be7498151005bd7498151006bf6498151006bc6498151005ee7298151005ed7298151006fb6098151005bf74581511c5bc7458151006bf6458151006bc6458151006bf6418151006bc641815102efa6018151006f960181510267f75596411b6bf74596411c67f545
  | 24 => 0xf43d8142006bd43d8142024fe71d8142004fd71d81420eefa40d81421e57e75981420057d75981420067f65981420067c6598142006fb60981420057f75581421e57c75581420067f65581420067c65581420067f65181420067c651814202efa6018142006f96018142026bf74592511d6be54592511a6bd5459251004ff735925100cfe7359251004fd735925100cfc73592511a67f53592510067d53592511d6bf4359251006bd4359251004ff725925104cfc72592511d6bc4259251024fe7159251024fc7159251026be4159251026bc4159251004ff705925102cfc70592511d6bf4059251004ff7458a51014fe7458a51014fc7458a51004ff7358a5100cfe7358a51004fd7358a5100cfc7358a511667f5358a510067d5358a51006bf4358a51006bd4358a51026ef7258a51166ee5258a51166ed5258a51006ef4258a51006ec4258a51006ee3258a51006ed3258a51024fc7158a510267f5158a510267d5158a51026ee2158a51026ec2158a51004ff7058a5102cfc7058a5104cff7690a51024fe7690a51004fd7690a51016be6490a51006bd6490a51025f67190a51005f57190a51004ff7650a51004fd7650a51024fc7650a510057f7550a5101d7c7550a51004ff7458251014fe7458251014fc7458251004ff735825100cfe7358251004fd735825100cfc73582510667f53582510067d5358251006bf4358251006bd4358251004ff725825104cfc7258251024fc71582510267f51582510267d5158251026fb7058251066fa5058251006fa3058251006f93058251026fb1058251026f81058251014fe76d915101d7e75d91511c6be64d91511c73e54d9151024fd75d91510247d75d91511c67e54d91511c6be54d91511c63e54d91511b6bd54d91511c67c54d9151004ff73d915100cfe73d9151004fd73d915100cfc73d91511b67f53d91510067d53d91511c6bf43d9151006be43d9151006bd43d91511c6bc43d915104cfe72d9151004fd72d91511c6bf42d91511c6bc42d915101cfd71d91511c6bf41d915102cfe70d9151004fd70d91511c6bf40d91511c6bc40d91511c5be76d9151014be76d91511c73e75d91510073d75d9151005bf73d9151005bd73d9151006bf63d9151006be63d9151006bd63d9151006bc63d91511b73f53d91510073d53d91511b73f52d91511b7b751d91513df3e51d91513df3c51d91511b7b451d91511b73f50d91513debf75d91511c6be75d91511c63e75d91511b6bc75d9151006bf73d9151004bf73d9151006be73d9151006bd73d9151004bd73d9151006bc73d91511b6bf53d91511b63f53d91511b6be53d91511b6bd53d91510063d53d91511b6bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d91511b6bf52d91511b6be52d91511b6bd52d91511b6bc52d9151
  | 25 => 0x95421e67f51d95421e67c51d954202cfe70d9542004fd70d95421e67f50d95421e67c50d95423e57e76d954201c7e76d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95422173f43d95420073d43d95422176f42d95423ff3e42d95423ff3c42d95422176c42d95422173f40d95423fe7f74d95422167e74d95422167d74d95422167c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d95422167f43d95422163f43d95422167e43d95422167d43d95420063d43d95422167c43d95422167f72d95423fe7e72d95422167d72d95423fe7c72d95422167f42d95423fe7e42d95423fe7c42d95420067f32d95423fe7e32d95420067d32d95423fe7c32d95420067f71d95420067e71d95420067d71d95420067c71d95422167f41d95422167e41d95422167d41d95422167c41d95420067f31d95420067e31d95420067d31d95420067c31d95423fe7f21d95423fe7c21d95420067f70d95420067e70d95420067d70d95420067c70d95422167f40d95422167e40d95422167d40d95422167c40d95420067f30d95420067e30d95420067d30d95420067c30d95423fe7f20d95423fe7c20d95421e67c65595423f5ef7259542214ff75595420067f7559542204ff7459542006bf74595421f4bf7459542004ff735954200cfe7359542004fd735954200cfc73595421e67f53595420067d5359542206bf4359542006bd43595423f4ff7259542006ef7259542004ff7159542024fc7159542004ff705954202cfc70595422157e76195421e67e76195422147e76195423ee7f64195423ee3f64195421e57f73195420057d73195420067f63195420067e63195420067d63195420067c63195423e73f43195420073d43195423e67f62195423e76f42195423ef3e42195423ef3c42195423e76c42195423e73f401954201cff7654942014fe7654942204fd7654942014fc76549420067f655494201e7c6554942005bf7454942015bc745494204fac42549420067f65d85420067c65d854201cfe75d8542004fd75d854201cfc75d854204cfd74d8542004ff73d854200cfe73d8542004fd73d854200cfc73d85420067f53d85420067d53d854218ebf43d8542006bd43d854218eef42d854218eec42d854218ef641d854202cfe70d8542004fd70d854218ebf40d85421e57e75985420057d75985420067f65985420067c6598542006f761985420057f75585421e57c75585420067f65585420067c65585420067f65185420067c6518542026f66118542006f561185420067f65d81420067c65d814201cfe75d8142004fd75d814201cfc75d814204cfd74d8142004ff73d814200cfe73d8142004fd73d814200cfc73d81420067f53d81420067d53d81420eeb
  | 26 => 0x3eebf65191523ee3f6519152205bf7319152005bd7319152006bf6319152006be6319152006bd6319152006bc63191524073f53191520073d53191523f6bf6219152407af52191523ef3e52191523ef3c5219152407ac52191524073f5119152006bf64d8552006bc64d855204cfd75d8552014fe74d8552004fd74d8552014fc74d8552004ff73d855200cfe73d8552004fd73d855200cfc73d85521967f53d85520067d53d8552006bf43d8552006bd43d8552196f651d855202cfe70d8552004fd70d8552205be7498552005bd7498552006bf6498552006bc6498552006f76198552005bf7458552205bc7458552006bf6458552006bc6458552006bf6418552006bc6418552026f66118552006f56118552006bf64d8152006bc64d815204cfd75d8152014fe74d8152004fd74d8152014fc74d8152004ff73d815200cfe73d8152004fd73d815200cfc73d81520f67f53d81520067d53d8152006bf43d8152006bd43d81520f6ef52d81520f6ec52d8152024fe71d8152004fd71d81520f67f51d81520f6fa50d8152205be7498152005bd7498152006bf6498152006bc6498152006fb6098152005bf7458152205bc7458152006bf6458152006bc6458152006bf6418152006bc641815202efa6018152006f9601815204e7f75596421f6bf74596422067f54596421f6bf54596421f63f54596422067d5459642206bc5459642004ff735964200cfe7359642004fd735964200cfc73596421f67f53596420067d5359642206bf4359642006bd435964204cfe725964204cfc725964204e7e525964204e7c5259642004ff7159642024fc71596421f67f5159642004ff705964202cfc70596421f67c5059642004ff755864201cfe755864201cfc7558642004ff735864200cfe7358642004fd735864200cfc73586420067f53586420067d535864215ebf4358642006bd435864204cfc725864215eef425864204eec425864204ef7715864215ef64158642006f63158642006f5315864204ef7215864204ef42158642004ff705864202cfc705864204eef2058642004ff755824201cfe755824201cfc7558242006bf54582420bebc5458242004ff735824200cfe7358242004fd735824200cfc73582420067f53582420067d53582420bebf4358242006bd435824204cfc725824204ebf425824204ebd4258242004ff7158242024fc715824204efb70582420befa4058242006fa3058242006f9305824204efb205824204ef8205824201cfe76d95421e67e65d954204cff74d954204cfd74d95422167f54d95422167d54d9542004ff73d954200cfe73d9542004fd73d954200cfc73d95421e67f53d95420067e53d95420067d53d95421e67c53d9542216bf43d9542006bd43d9542014fd72d95421e67f52d9542024fe71d9542004fd71d
  | 27 => 0xa6018154006f9601815404ebf74592522167e5459252216be54592522163e54592521e6bd54592522167c5459252004ff735925200cfe7359252004fd735925200cfc73592521e67f53592520067d5359252216bf4359252006bd435925204cfe725925204cfc725925204ebe425925204ebc4259252004ff7159252024fc7159252216bc4159252004ff705925202cfc7059252216bf4059252004ff7458652014fe7458652014fc74586520067e54586521667c5458652004ff735865200cfe7358652004fd735865200cfc73586521667f53586520067d5358652006bf4358652006bd435865204cfc725865204e7f525865204e7d525865204ef77158652166f65158652006f63158652006f5315865204ef7215865204ef42158652004ff705865202cfc7058652004ff7458252014fe7458252014fc7458252004ff735825200cfe7358252004fd735825200cfc73582520c67f53582520067d5358252006bf4358252006bd435825204cfc72582520c6ef525825204eec5258252004ff7158252024fc715825204eef215825204efb70582520c6fa5058252006fa3058252006f9305825204efb205825204ef82058252014fe76d9152206be64d915204cfd75d9152206be54d91521f6bd54d9152004ff73d915200cfe73d9152004fd73d915200cfc73d91521f67f53d91520067d53d9152206bf43d9152006be43d9152006bd43d9152206bc43d915201cfd72d9152206bf42d9152024fe71d9152004fd71d9152206bf41d9152206bc41d915202cfe70d9152004fd70d9152206bf40d9152206bc40d9152205be76d9152014be76d9152005bf73d9152005bd73d9152006bf63d9152006be63d9152006bd63d9152006bc63d91521f73f53d91520073d53d91521f7af52d91524173e52d91524173c52d91521f7ac52d91521f73f51d9152416bf75d9152206be75d91521f6bc75d9152006bf73d9152004bf73d9152006be73d9152006bd73d9152004bd73d9152006bc73d91521f6bf53d91521f63f53d91521f6be53d91521f6bd53d91520063d53d91521f6bc53d91521f6bf72d9152416be72d91521f6bd72d9152416bc72d91521f6bf52d9152416be52d9152416bc52d9152006bf32d9152416be32d9152006bd32d9152416bc32d9152006bf71d9152006be71d9152006bd71d9152006bc71d91521f6bf51d91521f6be51d91521f6bd51d91521f6bc51d9152006bf31d9152006be31d9152006bd31d9152006bc31d9152416bf21d9152416bc21d9152006bf70d9152006be70d9152006bd70d9152006bc70d91521f6bf50d91521f6be50d91521f6bd50d91521f6bc50d9152006bf30d9152006be30d9152006bd30d9152006bc30d9152416bf20d9152416bc20d9152206bc645915240def72591521f5be7619152206be7619152
  | 28 => 0x40044000007001002c006002000000801400400200080020020018018000000000000c00000100080200120030000014000001000800000a001000000400a00a00000000000150000004036000001000804c000002800000a00600280100020070058000002009000001800a0060010000002003002800400400b00280000040040088004008000000000c0020010118000016006000004400a001000000c000001000003c006003001000407c0040008008008000007002800e0000030030000003005002000800300200080000010000000000000000800401800200a8000000000000001c000002004800400a0090038028000002001800800c0090010000000003000001c00e0000008014000000001800c02200e0028008002003000000000000000980080020050050014004000000000000c006000001c000002000001c02000600000b4002005000800000a0070090018000003000800400e00000200540140120000040008001008000800200100b00b800000100000000000020000014004000008000c000004003000000002e000000402400e008001c00000a000800400000a0020010004009003800c0000040018000002011000000400600500000040040010028004002005001801800800400000000040040000008000000008800400000a000003800000a000802c008001000000000200a00600000000030000018000000001001c00000100500000000020008000000004000000003e000001000000200000d0014000000017800800c01604cfe76d8954014fd75d895401cfd74d8954004ff73d895400cfe73d8954004fd73d895400cfc73d895440e7f53d89540067d53d89543f6bf43d8954006bd43d895440eee52d89543f6ee42d8954006ef32d8954006ec32d8954024fe71d8954004fd71d895402cfe70d8954004fd70d89543fe7f6598954416bf6498954006ef62989543fe7f6518954416bf641895404eee6218954006ed6218954024fe76d8554014fd75d855401cfd74d85543ae7e54d85543ae7c54d8554004ff73d855400cfe73d8554004fd73d855400cfc73d85543d67f53d85540067d53d85543aebf43d8554006bd43d855404cfe72d8554004fd72d85543d6f651d85543aef641d855402cfe70d8554004fd70d85543debf6498554005ee7298554005ed7298554006f761985543debf6418554026f66118554006f5611855402cfe76d8154014fd75d815401cfd74d8154326bf54d8154306bc54d8154004ff73d815400cfe73d8154004fd73d815400cfc73d81543267f53d81540067d53d8154306bf43d8154006bd43d815404cfe72d8154004fd72d8154024fe71d8154004fd71d8154326fa50d8154306fa40d815430e7f6598154005ee7298154005ed7298154006fb609815430e7f651815402ef
  | 29 => 0x1c00401b007000400000c005802000400600200280040060040014008002006800800800b0008000002003003804c000001001000000800200b8004002000000000c00a0040000004004005014800000a00200100000020010010000012008000000400001000000000020050010000000002001800000000000f8008006012003800800400e0000000002009001007401c0000010034002003003800c000000000000400400a00180100100040020000000003000000000800d00d001400000100000040000000008000000003002807400600d0000000000009000000000c000006802c0000000010008008000000800c00c0020008004002005002800401e000002000c0120050028000000000001000001000000a00100000020060010004002000000000400701d80180220050018010000001002002000e0060010020002006001001800600200180340000030080000016001001001c00000b00a000800000300000380160010058010008007001004000e005003801c00200900000000000000088000002000004004400e0040018000000000000801400002a003800003600f002809000000c000000c008002000000800c000000804000200600280000000090070000002001000001c008002000800400000100400100020000008004000001000001c002001003000000e005000000400000300080000160000000030000002000000001e001001800c0000000038080014009001005401c0080030018004007002000000200a00080440020040018000000000002000000200f00080040040030030030000001003001800200900180cc034000000800c00800000600000080000010018000005006000800a002005001800800700000180200000000018006009001000402e009000000000000000380000080000010048000000005000c006000000000400200000080300060010070004016000000801400000200100a400000f00080040020010018000004004001800000e0000038014014003000003400e006000001c01c0020000030000026000000000400e0020004006004005001c000004000800400a001007800c0040010048000018001000800c004001001000000000000480080060020000000002002006000c01c005000000000401900100080020000000010004000002000400600200080080000010000004000008000000000600600d800400a00100000000080000008000000006004005000800000200080180010008000000001002801c004000000800000800a001000000000100000300000040008000002004001002c008013004001c00200000380240060070008000012008001000000400b0008000002000000000400000000d8010004003001800000000500680180100050008000002001000000000000
  | 30 => 0x28010036000001000000800600000140020050000000016003005000000800100100080000020000010014008000000000000200d0018006000015001000201b000800c008000000000800200900a001401200000c8014000000000000c002003003000400200100100000000130038000002005006000000000000300000020060028000000000002004000200d0000004002000000000401e00300680000020000018000000003000003000000300080040020000000018000002002801800600b0000004000000001003c000000000004000400900100080160010000018002003008801800000000080080080040010018026001000800000a0000098008004000008000801200500080400140050000008000006000801801000f00080000020010018004008012003000400c000006000c000000001000c0000020000008012002000801c00200300080000000000048020000006004800c0000000008008000002003000c00200e000001802600301600140040050000018004000000000000200600000000040000010024002000000000801000c00900080000070000000004006004800400c00200c800000400e0048014014000007801c0000060070004000003003000c00200000c8000008003006000001000500c801400a0030098020006001001000800200500000c80160000008000000002000002c0220240028008004008001000c0000150000024024001007001802200c000000000c0000010040000000001800c00400300400000000070000014010001000800800e0090000004016001000000000c0030028004020000001001000000500100040300000010004002000000001c00000e000801c0120020028004034000000000c00001c003802800000000000400080030000000000004004800c000006001802c004004003000000000100100a800c0000010014026008000800c0260070030000000000000800001600500000000000000018004006000000002800200d00000000160030050004000007000802c0100000018014000000002000000a0060018094008005000000000a0000000000000000004800000000e00000400000020000024014002000800400600300000000100020090000002001000000402200b002001c01e0040000010014001000800000e002008800000200700600340040010008000000004000002000c00001b0070000014002004002e00700080040320060000000000018012000400000d0000014028001000000000000b003000800c006003002000000000180000040000058020000001002000c008000004003c0040050080014004000001001400000100a00080040110010050006000001001c01e0100048010020004001000001400a0010020002002000800400801600080
  | 31 => 0xf207c74b06604c4887c6bb8b1282412924960d063f8127e7841d50538800080188c411b8a5e5bf18b65941e52298910e0001f6a13f902c0000dbe000000000000006e394fa000000000000002340b902418000000000009d96d28c3905045f00000000e1c4380c8247090c024a23d063c9ca0848119444001d203a21b602697b2376108c39805182da9b80578154293111161a4800000000002cc957000018d60158c32007004a78ea1da508129c53686b66a424940001d7052d0000672021c866a4a62de165a0000000000195485892f60000000000000000000000829dbc0001dfe0000000100853086400825ef8bee7d500009061b884a294ba9100db000022aa4bf97d06520d9231080005d803b2442064060e000011f8870000255a9449bc030b88ce66c15484e8846c8cc800000013a800000006bca1b00370ef888186424e3a58431f0ffc1020c7654c08242dd08345a980bc00001120000000396a288115807c67c96f684f0682361934629300000011ddc000000000012c60db188e60786204a592aa81a1c5c5348a7081593bc5f116f46958e7644e800000010ba8651abe0001ac09721c040000fa6846107200000006d40000000190c90f8eea1b89614000000005e8be4264800000000000001d960001d948f3995c3278c7474807306d3800000001e20000000686914e29d800004b80000001ba24f0000000020226871b62000112c43d0000000000007d0000000114a22b85a85eb1fd234b9ff822d80000a98000337994a6e280001dc052e2be800014581180000b8a15e21cc39702ee00000000000c7e349235630394b017c1510030800095d21d6446800006488fc000007a00021d41b211283a39bf83de91ea707a360518a48819f900c5e0a2123069bea17ba09e00003ee02900000000bfa7dc9f5e41300004a61e0806fa196000126608680006470b866c7072064e00009551ee000000000000db411d1a140000000000062208b9c12000000000012680001bca6559b248a7194e2d91f0c00021aa74f80000000000000000000022bc8e3800045022ee6e8000054e98da436a2a6000000043c89ae000141e0038b6673616703e39f400000fae0000000036a2a801c80000000000302068407e9b1051a9b9271fa37e00003fa444a1809049742000259e52a800000015b209411328f9867812d001815896348b713e02eb867212f80000001874000169627180005ce081e8ca80004ca80000000000000000000000004081a1600005820001a0c69200000000fbe00006a45611b449549dc632e9f500001f523e9132c7951d0a02a83541778e4c193a45e6c7832634f11b83af160a52515d866a975e48d104e46a03f08e219588ba00008ac86b857900000191a848b900006b7097e0dc8c8c59a8008000006004800000000080000000
  | 32 => 0x2871782042ee00005fc1e6c74794ac1240b9a00022fc63998685a923f603b865852c91420f500005f2024873713b400009ea14a8000000000022014823829b0c0000d8e6b10a26759106a2161ab85bb1c8c000167c6b6076e570161274080006ec097c00002ec12c00000000000000000045787fa0971712000000000007105e783fe29d0000869083839a95921d900000000000720076a000136416712e637c039006c02d4000259691c115a08900003018000067000000000002e5100e0f6000082b86660150000582000033aa3aa01899fc3c0991a372943600000008fe8ce0000000000004282058664898977273500008e401c874d96de16c0000000105400000008281a7449c043000000008d2800050a80000000000000000000000002298000675000034fa16e0000c7a0001e400000000093023a17d03b80000000000000064021ca84e8000585925e60c86c2000000021203ce6c3a336000000000000000001bf6000000080b0e7403c01f8962000062805a2294221e0000ab20001ed474204b81a6800011a00000000000000000038f2148000000069e936282a02a2514800000005840000000698000007f800042a80001a9800037d0f446ea214a0000da80a10000242071e6e6000065d000091188600000a8887b18ee00018a600000ce0002344000000000020c4625226802a1f8c1188000000082e6952570000000042c80003c4929e063173e0001af00001c5035106284929f04000211443b24b24ae0a6e155084400000ae658105c82c17e26cf800000000000001f003b39dec2149a585881bf24d4800000012c488d954e33c00007a1a482327058038da5aa8b2891e00000008901c2834c08146df8abc2df870e000000000003fc24b000000025463560000000119c74025b04609ff600498a273c1e8800004f44bc80007228f087ff800082a8000000000000000000000000422000003181e86120c201b300002280000000222a24500000a31b0400000000b911848d30ade0000eec000000000012d8000000048f800040a800059a1a3845c0000569098a8822346000000000001f0000178c000003c000135643980000000ad6000000000000009121a2a57515a60000e1e6211f744bd24e80000000400962a2a7800043400fc87c917804fa44c396241c0991eb226992c22f00a6600000003850000000000056a812a38e0330407892600004fc6f30aa260711582aa919271da36674903864c605404b480a07781f5a3dd8a9c000003800021040000000000160c263000083e800000022e6000128e000076885e80008c9000000018f0000179a48b00000aa800010f80004f1800000008300000a9a000000028c80000000000711817401102022ae800061e986a0000f0a000051200000000001e160bda000144252236c8ee40d
  | 33 => 0x110000000000070e973c000000000000000000b7c0000000000000000018920389160000256e0000000000000079d0be600000003b9800057c00003c680008a600000a2142c00000006de018a1b1000059309766e1a51600000003b320de42a014200015f63f4808041689d441187265fc962e2f483be81b1da64068f000001d2205b093875c91385ad25c60f18b68000139816fa4c25db800000006fc000000048a80000f6800025d08046421204000000000021220001d840001caa53c80004370ca200022c2000000084ca2d822182a80301baa3ab01f625e23ea7b3000059880008cd183463e000000000002b70a240000a1a000000000000000000000889000006e000032aa2602f580000001d4e000000043e013a2d6a50c78f01a203b1f6c6181a7863109b40000d84179800037f0f986c61e0e31ca02e433211c528a5c002718647b28f9252400000001cfe8a182726e78bb002985ba732000072b0000921000000000007b7180a1af913e2d21a98435987c84b9ea2375876256300704b593aa06b946629518ac2108000000220a15819f400002d28928000751068e010000045b86c632d1c1a05c86ac00015403a91666000022861096c87681a5068021be000244253606048b587168ce95ce000123a3b7044c7ee984a00019405980f7c58e0a60678a2844429dbe00008c8000000015a1eea912a19c3bc89a48eb9f4e44515020ca8fb461880001018a1c10403d015f80002f10000619a3b800000006d908880000000000000043a130e00009aa859a20e00024f8000031873e0c4029e8d720000a3e00000001308ed835a13b642b888e0000b305719f1268d95e84e916c01f8a0a20001b5e5d7000019a877200020f682500000000000004000064819ee3b502f00001ffa11615ae8f6027c22a09ec3b88aae84796360b0894c7b98c8447e14c65e200004e10f2200000007ae914605a90420aea0e43c400346519a0677a8d602ea9ce45ad9efc28d200451c9d9c47da1107d624067df92cc2b31eb8000000000019c028520ee000191e4be97ae1b6000010c934467e0bc685186b074e20f00b013ca7d584de000026c0002064737861e335958842588ba8ec217e6441d189628fb82ad1d40890862c921925c054887a5249f782aa218e00b052880d924070c98c818519821011b127e7076c22a82fc51f0a4e69784ba424a31619c212c5b393a60ba140e7c602e00979a8e6f591ee3c8214e192a21c36d87f47a799f02b9000011c99ec11da5c23cb00009609c824eba05a663800053312de0640b927d700000001b6e00019d675708e0960000054a1fb06c18862414890218f0b6c64d0cec1d6979464600005730e8663fa1868220be000000001ac860e00000000d6800000004b26b3a39c000000092625064898000000000000200004db18
  | 34 => 0xe524b2a12466f00005d10000000000000000000000000000000000000006968000000000005d800000000004911228000106e1b49ad007088b8862002a5c20ab621e1ab4000000000000f43f9013032b1a680000e320000a0434116e03eb00003de0c9a60880005158c788cba00a70ba312359855273391d039f9dba6da81087cd8b720230c683ec89562c111366ca209c39f1b6c360898243f064683d1b8227d00744838d5c1e091340638a1694689588d401061d0114848d88fe8830e226f488ec2a60bf88fd0882631a27c38a8a682f222d2499242051a21c00001e7805708c60f497ce78500001438a72821868c79d9c0e5971d461cca3cc53d0cc27a719be6eb02da7df088c25900001bf92223ed80000001c9c000193a67184d843f890e6b29dd288412903a280001c717008e59ca244795fa16c80002600000872137400000000000bf40000a4049ca296000000052014f8000000057e00003b11d0e6948a5a43a8ac655299045510eba51923228508168679a4142b9947a16792f84a00eb00001fda00e80009069afe0000000881000070c064840c800056413b87ab056c0001bfe0000000000000000000000f2230618080000001c2a58692ac000000029280004808c9287191e400004e0495207a453000000000000001df882d1d420000000000128c7b389da96b00000000ba20001f861d1098438984a60799fb800005500000000000000013e89860000dde48905ac000000000025b689400000d0126c6b300004f79380625800030887880d880003e2177095ca0bc00011d665b8000000037a000000013b08fa000000000023a80c6800000013280001fce94b168c7f500000001c4200000000000000673816272f007e81414303b4188239c177a6839354066100085c13883db06960001c54000202a69898084c5800000000007e40000000045e26e80000000ed600000007ec8eb60000eb80001f84000149800000002d014c44b2251417813143781dda6aa96f000000000000000346000038010984ec1b4c000000057b800005280009188be8000000080f00cc0002144796108600021027101c7200000000001890000130016b80000000ae095b000014b24b606a800043d926e33c83ca660038a0001fa400001e006923a4153a0fc0ad949e00001441f013664a11a7c061000097995048e98eca00019dc0001ed60ce80fa3388c28000225c000000000005322040050000000000000000001576000000000023b252185dc09480000ce0fa20000304000226c8aba4aa56d000017c80000000c5c7e201c4000000091da4cc5ab1672000041c23d060674aa2a2857248c1fa9d0646180007aba10e11200000002404000000000000ba91f1b6800000003e680002e5800200001d00000000000218a2ef91b68fc02822948ada74302b06
  | 35 => 0x1246544a46896385560000ba000016fe5c8174e0001f488f78dcc0000000000000096315520000a1000000006790b1800009ac000248a42000005cc800008980000000b807d300008d39ce0000240a5db0000490800083f80000e5055a000000000010e2000081a000000000000003ff8000677800000008548e080003c100004c425680000c3000009e800002604558000000085a20325944091cd01c08000000000041784800002532000000000017d400022d0000163c00025304c983767918cd4000000071b1d280001070034000059606e448616a805e00000001eb604380007cf80003d180001bb0c6a817a51c000000077324da0000f648f889120000b7a52900003b796f83331a1e0aba5a80000b36000099a0000bba08d11ec38211bc7cf00007ad1c9a00000005e1152000000001f980000000e1807287b051c000000000001e78b8e77a06909438b5c00021a63819e4294b9a2e0000a086599308913a53e0c58b2c1b6a5e43a623e806b074e7ca800000009943c3182413c8f521fa06e8463857c8cf0af206f240075e87d400010ce203a2e000000007b790104fc236e0001d163811f1a0000fec00011245e0000000000920001a8600000002ca80005aa80000000b526cc2520350199c08317ea5ca96e41ab80009670e6200015225c7000022d16d60b880000000688914800091f80002b20c54000079600019e80000000000020e43522226f9169a89623da893065e3f4043400010d25d49d4c0f3224453b86a27c280002e60be27608000240095c0a81ce252fa5082d5881838380001748c160cd108e3ad0f5c5f78afe0450000045899c000000000011de000171800000004321f0800000006ce035600022f8599190e69d82c6697000008d80007b618e44ee8ce43bb8ba884d20983311e6a82285e86f20d4204a02120c08b3e23901e409a830800000005391d1c930000083e000000000002af8a0205608321aa03788689db4929000081800000000000000044457a85cc7138b1e83a06b40001730000000000016220eb96d4420891a0000000934a0e0000118a5a000003fba5020000000604000000009305af800057d00005c09cfa5af00d27e018143a580000179d04670a4fe1d200003ea918c00000009428000088980e06d000000000f88fc8b580000000000109a3ec0000734800001b8612000000009f80000000000000000048e053e0a419b42ce06a00758de4388000000010ca8121a8c83ca3fe00017fc36500007b68b1c6d09090000024a8eb20968ed800064a97e63a516c45a191760001a2c649147871f1c340000aa45fd064c75d100847300008d4a55e40489d212d86aa11989e032f9e64605806a6a287525429a427de9a02000019662d0626688017063b20c616aa4f00078086000189c00000b86c898d40770
  | 36 => 0x17dc935832e5569b6649807ba7791fa83e500000000b064cf00002b080001e500000000fe63bf1d600eb242e0000a6c00024d8000004c3b4a10800018206f10000394000054d0000000000000000000000000758800080900000000000835240c17104a28cf8cb605188d61e0029a0000000105800000010b0000107a000214c00022b00000000075103e8d518fa00c829c4b717fa8ff1db248500000d80d2c57f80005d5800000003360001a3200000000480742000005c5f6a36400000004e812320001f8e682a1f03cd25d07021e224e50ad00f113fc6340194000000041580004e31f6272e22f224ca192374851c2000fc82351e7c8db1e207a29b76042826e0000c943769fe8000000000000000211b2e0000000000000000021dc1cd9bee0001b363910b4e159800000020a693b9c1000000000161fc600004606bb20d862180000000dfa79895547c7000000000000000c62000000000004da109800062e1f3a000012c00024283ee80000000e3427b800064c00003cf857a4fd0000689800000005a01428c120001daa000000057880001e90e100000a5c00024263ab800000000002c914ca3d6112000000008e89a2400000000000f7068f10fa73a000000024541cf1040745000024721e284f81828a78ad88a81ab20a298720ed000000001002b3885c0001eaa0000760000000009c1e6000000001e7169c000156c5b28000702800085b11a600002e606e8000039199a56892da8bc21f819113da00000006531ec400000000000ba400000000000000000000000004d400000001ff06980001fe20001d542cd2126000000000014160198000840097a6a880000521906336000056688bc73c9afa66522de0001cd600017741de029217a859a5d68a561321c5290883aa7d8246e476993e46c8266774000057200008bd8000700987e57085926be1932401921a3c18d90000000079c800000000005c31c9033700000000ddc2ff0e2c38a161893a824e0620000000073e1c01ba66d2800000000000000fa8000000000024be000096a000075c000000045c80009649af60000b9e4a880000001698000000000000000ac8000234a342703000019b03de00000004710000000061092385f80001ebe2521bae00000004e2800000017a83f8a34005904d668d00000000000000203480f92e205b976a00000000000000091a04208620280000000175093e2f3a0ba00022026729b48678074c041010200001388921fa60001faa2960c867e6951a3da8f8280985da2879b84000000047c8000000000089e88dc0000446000000037c8b162049a8822c87b40e11bda00000006fb00000000000000000000016e6000031054190ac00000000002362322000000014966d493900ed80d80000a308998000000000000016ae12b000000000000000000
  | 37 => 0x830992e4201852463d0966000000042f8d0a255206600000004738bec5b893d40001e8400000000001b6036800000001c7045e8b4493c81d895a8bb400012ea846a1f6316239e85801de854000050900009351e9600004141a78cd00000eda0000ff80b6172828498c276a00002a385fc93d9cae00317f6000086c9640000911000000000000000000000000012a800011900003338000000000088522ac0000a2e000141a0000950545886a00008a4429000000000006f500003a98000000051e00008b0023925693d008828b00000000bea0000000000000056083700e30000000049247200000c71e4e11e800000000006ba16da00000009171f6e00014c288a000000004a86dc000056706500d1800025a05c84bf19982dd800000000000000000275800000000000e385c069f93b21790b000000000106183010a921e0000a0c000090c000000000025d200000000001ffc67600000df80003900f165cb9da20000c1413715b83d3117e4409b9660ba55800020e642d8000000208c3ca863400000000001f26000063800000000001aa423e000072d80000c3000089500002e995187d0823e1698f40000000060b23dc000000075b9d34000093a01393dc1d2a29a00024fa61c00000001440000000000020165be80001831d8e2b1216a3d980005c1034e8dd800005389222e200001340000000000011502fa000018089c916a3d680004e4983a00011742e316c26af0000771000038320b866880001bda2944a81f2e0000a0e27f1de608c80003c5034c00000000000798894878610e9bbe77b80007620eaa8bf9cee5400d22920158e5d600001c51c74150800017410bc000156a1e280005798000000000015711fc7ca147406c863e1278154000000065f800000019f6009863692e000000000004788a000af247416d800034e23b462f922004f0aec0001ab053c1ade24b9ff282480000000000374237a00000006ca89a25540c90719000000003f867a800000000be94797e800000003fc1d5a6e4000000019900000f5e6de8ebe00000006b1925213d933200000004da225e0001630000000000000004c700007e080003688d641e49aba1ec990a5df21380a600000000000000000000000005130000000185c0d116e86b88c8e9278000772800000000003bc0000212800076193221f48000437800000000001aea1286489ea80001dac00019fe00000000000a92251000000003e46d7000043900001b4196c0358a80278913c00014a000000005cd949a78a1ec04a08c4400021ba3c70de200005ca00018e034d23ec000000084a832c0000fca9140f6e2d500000001f8a5fe25400001e02000000096d00006a982541048000000104a64d84521c3204036a80008df03e017d800047504423f61d7e0000000000000012900000000000000
  | 38 => 0x8000027e9e9290e8d0e0091bf03679b02000000047f8d0c96f00007e880003d525a48f80132516253a00000000000fda1310306000173a0000000000059000000000000000000000000009be000252600022fa0000000000000041d0c1c00000000000000163034a0ec1ea63f7880a7ce03c255f0a4611703925b720d68b6a238000000066e800000017bc00000004aa172653a91c64460244746802085f0b0208202cc6659c1639ba4560d90000000000088583500001e7a0000c5a334907c00018dc92b9bb20001ebc000000000000001ea08be000000000002ea0000000000061a50400004819c6246c19846649f20273083e319915297719a65d401220001efe00008de3f5203251293c85c397540a9000000000000000000000000000019cc000000051da2826ee000087f000004419a0291185895d92005b19e0000000002991748392112a3d815d67928c1e0e9a3707861216000072c80e00007e606d63d892bc3408000804152697593fa00000001408000408983c503118856e80006f60a0600018ae68a00002fc1f9e63621ea384800087818ba236920a41da0700001408000257c6379624611a23270f98522c6802e8269b9454c96ee01a21060cc84cc26f050c8b38ec00000000000145a7a024384311ee4047011a1c291268a281a000000000001aa80001b7488c000000000003ca167e000250400006ca2bc053a876222600003423f5800000007cc6dc804808aa2c46ad8000000053800006245a786f400016780ae0f42000000070f1b2000000000000000684000087b9190000000000000002c385484c90e5687e83a855914a60001c6e97a9d987c907c2000000000024e0180000077c8594311800000015d0116a43408804c000004705918d5e00000004cc192c00003c03a79d6a380800000000008da800041e00005ae0000000050615c8afc00000008de1d2e4fd9fc48f580005c780000000000236063a7759eb08c789521b5207493187fe66b1d568b209186629db07398802000228c000011e71200000000cc00001cbe3d58374000000000002940cf00008b3000070e0d7a84d80005b6058e684839a0001ca44550d3676d80002f51912000000087d096c00002c8000178a000087200000002d185bc00d80003fc840a63a9fec8e81c840180a6a0000f9600000000e095fc00000007a3000000003986b480004ac946e6200b7000000002130e2e27600005479bfa000032400000008239ac87ed0d2800003801f2800044b800000000005c8800067680002088d1e000161e0001dce978000000000007c79e8248405086910000000015a0000000000066897b03bc88b19b80001e1c54700000000000000036a95900148d7835c49e0f1800000000001e3e35680000c7800010f0000000049854300000002330000230a00023f
  | 39 => 0xa04c2800000007060c280008e1138225199b20001a46165800044314de000156235d875436680005e7000000005580000000000071a401000092810a2000210a3d3a38090ca38600010f04e7124c4dca50000000000000000358841a07b9e362e113022c312ec7a80fc0039984c1518c6e02405fa5df882c5a512ce84317ca00023045c1849c45996903d211649379dde81f842e6a5252a26c14c07c8800075a15b6807199e61e000002619d078b0e9c70003e6000224e00005706a5800077081862d88fcc10b20c826c952448309f653808080001c7a94d00b600002f40000d2a35c23d4733231c20e80000000000000235c6290fe8000000066200003aa049a000000000010d83b1800035e12d487100000000d2691a9fdc64504ca7ef07f64b81018000239200007ce0000000000140200000003ef000082100000000000000204e08780003f197d88ae97b800020527631be044180007308eb225b93f800000004a5000a00000008c00000000101c1d405a42ac1fb610380006f19eec4f587ec19887a03d41ec20e5916800017b0000142800008201d6171457b07ae00000007a5000027f80000000000551800000000000908c8a00000000001dc8000000034e80de0e718c000021ce5aca416803060a0e900523f0851a0000000000000087918a800000000000000121800000000001af0dc6000000000009de00000001078000477000000000006e712620000cfe81d960600011f46f4158000000000001da400000000000000000000011f000000000000001e1e4a214ae00000000001dae91696cc47002006d60000000000037b0000000000013b9bce00011ae2b000000000f3000004f075f11b473b148a4df000046e983636b935c66900008558bcc658800033985ce08b1bc23620000654084693f139633b823c29e1cea000255600000007f418aa3df800050b95a810904967cb13e66931bf45e3862a0000000000000030400007ba000030e92ee87422000000f861a18000000026809897620000000000249613493767b20d9c92d1c665c900001dd00001d78e7a0000942856878e30f80000738bfe21f814c2ab1ec600014f68b0201400019b60000000000000039a049414f0b2037004c624800000168000511981a000000000000000000a1818619680000000365800071580006b580005dd920836f0f8415914a89461f705bc82143be8efe8679cba2198a483b21b16000169291b258646006162bd0000225237439e00962210000000073a00000000000fa00001ae0000000000000000000ca600000004fc80007f8106800007342c5000001b1c60000134a0000000837254200021ae39285261a280000000c2a3cb80005f4934835580008f49af400018e280ea3ee0000ee884c089e3e000002d8000000000002588312006840c1b
  | 40 => 0x8160dc40001eee1210c3c14d2318496a49a00021de000240200020120001c1c000226e87f8d2000013d8412168a00000ca24f07a200007f80b28000000253c2ae0f2600018cc000000096986525109c141ed9b5615a80001c6062e7d10cc86b69a9e448800078900000001a4a000106413914b800000003a112f00000000000000000000004ef80007b4137a00003a200018760000000000000000006f800000000001fde244000000021540001ba400005044c180000000ee026e20da354069c21581349750d0800009dc764800051f8f720000000148a0cc466879a000000078322b67fd1dc040ea3c8555895a723a00200000000c802dc1c89e126578ff40000000583a4b00001ef2000000090aa0ec0000000000000000018b22b5000000000009530000000143a41f800079c000000021163141c1837b8cf4977a1a894d9e56968089c2c21c967920000000186e7818b50511000000014180001644000000000005d654f80008a91ef06169bba0001f140001f760001e445c400004940cfa40a1f468c097aa6139d804d614fc0000e464ff825800011ca2f080001398000610017c00000000001a3056617644681e6e6c200007f595745800c96195225a162894021a15387f924bc40ba4a83f706942fc800081ca4a22528a7e5c2964051387760af88f24308de690400004c8000085e000024109f2000044000000004f41e9a66b872a0000988000000000013ec32c000000000001cba5d85ba988800006f23a300000000000000189a000259a279939e00000006fa20e294e048e4ada5a2421197879709b6153185438f8d4644c036858b0000781197c8d69bb45179df63e300000001d5e4f493868119422000127630d9d30731150878b80002c40a2286d054a1970fce8ef84ce93884e27e50f8a65a992617183e28209c687eb9778973015060a87aa81a802891e01565358e8832a0a7c6ba94548301d6c0350ea08189ad46f8957a75e1fca1e31f928448756000200e54d921c83a9ca865e800015d000097a0322081a4ac952198c56c18124281802010a40e505191674f232027c0c980001ae4264000089d03ec2f706ee7a91dfc1ef8000467898e958846a72ca5da35f00000002314279000085d00005e580004279c4475483e88f017e00b7891600007f29540c005fb87086159d8a36617a47c4036e7bd9bb62d08b0a1d98000151009469c009e282a1680d78c6c39c9fc059d800065100007598b289370d6e5771ef40000000565077a00000006ab952e37a25b287a000001e0c0286b01c078d000081b9e503a68000226000075d800000024ba4ce045040e0e92957254e6c6833e23a0a3a15b813613e00007f2034834710168c68cb846b1dd43fe800000000006cd000000024725450000000198678c9ff000000001eb09
  | 41 => 0x7ef8438397a2c6309207823a95bc4dc167a3a083ea2a31cf44d6886e36b00003cc85980a780008f900004b421bc2f6141c000106689f80002f40cc600000000c5219800004ea4a694d400013e24daa32c7b88ad26408000000179000012a40000aee97880000000000939000000010a62eb135e0000ff67c586dc458a28012b80006229196584179269b01c649f1efa6749a6a4ad085e4a19be61621cb020982f28078000000143e0000000000000079a0d8018700002d780000001de216d15ac00013340000ca05938c5e70b23ba2cf11a462f143c0c013cc1fc039e12308960b108f608e13e45fb111c94408e22742044553110446a96747130d004228f9c767885000012be00003a080220d06cf146c1ce0076476000000000006cc905890f000068e9fac0001800000000073f06e607f00003698cb22f69cc65a08000315974a43180005ee96b0113800000014bc933974c7d2800064f00001452394576800000000002a1a04c1f200000002464736a3106861e66000165465d8280122815e0380ca40001a6e65682308c989f8224952a58980005a20216312223c000247a5029a80000000040288ca74c800002b000009680006548000000000000006de0001766000132e7221a664cd9f063f122467441b3a7a60ae819d8c0c45b217679f819e83080000000000176000000000000001c068bd17c623980005140000000000021398509020e4219f00b053f80001bc134e0000d7e0001b0085016486c99e38000000080c048834500001f10dc8000000048480002909044000000000000000000000073099e7b4a52463d906c5619c223e7a28e0668c642cb9f966e6931e5010630558000064a00005ed01a82738c606d683280d99cf68ae067493424608e322ec000243060309c8627966e0000022000000060615660001ac27a39b147c08a8253411f0744a0be00017684df80006d1882809e80001b3800090d96ba000083603c80000002158000000022405ec6f78000306000000015c449e87dc00018d209e00001c922d4369130c1481b404db800000000000001b0a0e20dc20d48f243d289c468104825978000000164a71a96841f6800028f0000258217200012ba07a86fa6901274418957e1df07908591e1a00000000c3a57a1128000385a39a806828e00009a800003f691625661f593ce58108407fa8f1e2c98ae25cb1c86352000043b9b540001448000000078a800000017b62db800094a115000020ce7fb9cb40000000418000000013780001d3a6cb13402eda5b85f09df46ff00b21969c5802d21520000a8a4f080008e612ae3a00d1a4c10c389199e4c04309ca5d180007a4218400007ee0059fa0000242439b000000002fe000000010897a6808241e00014881f40000000000024d13ac4fa10b84b0155c0000f3a18c8dba0
  | 42 => 0x7c8f3c000000040d0a2809016a23fa800000000005b40000832800088b87de1c49d4a2700000000000060f8f900be067a5f000000000af835b00000000d8a8060ce84ba21c28b89c3661b1572161a2701d1a0ac2d3159e7279e0a86e16027da060813a14ec88e881c399a4ca3bd17cc0001ef8000012422b0bbc1f19f0e31c16562c88000355237202881da517124e000232833283dc32f00000001c208ad238a7d99bdc6a8003095123486a480002eca2ea2a996a06ef00004c6a0a42cea5ce59b0a380001786712922e00000006888a2a2a5953c79682565338000386800000000000840000000000000013c47d9000015d800044400001080b4a3548000924948c0000000373808a4d4000020f0f7420a8e9063394061e10dfe00000008ef000038e8aca270971a8f28000504895e58a00001e99e26000000057c93424fba5ba7cd18ca03d939a2bd800000f9e3055e11e0626000093207e488d0d8c0000a84059958a6710d105870e30000000065c8e6406d8f363149dfa03200000001a9a0001d580000c3400008a2000000021d00000001c9805003d607b00001f624904cf948435a800047a2368815218c62c155816e02743bd855e00012a65c5955e88814e6000188c21d8cfc195800036e0296000000000018e882c9afc0000d4c90b1fd81df800035280ea7cc1ae69271dd87669d9054b19fa3010c4a7499a8214017a04d323c4393a1a047997d67090046000000003f800071e092a89e1cc0000126a5908924226919889915d2709a30889580003750000939923c24da21a52d84a00ab22927979a4e8afa54a25c11fa5e6109438921d28a4000093b0c4c00000000000bca0001c92000000023b83ba00014dc55b800000019649711df03950d1600000000000aea00000006a70b9c00002ce000192e1788000230897246f93ea0001fe60580cf637d87b812f00000000000000000000025ca6991144879959628da05c3ce25ae04980000000000000000055a000005f80000001fc20000864000000000016529660d4e00023c200000000000000000000000000007cc8728000000058e8000000204a58c9a3e1ef068050e15be8f1890a100000023300000000b82682088a95e102689aa23e0001014000000088617402f7a1826010d1296f909c60999423a89cca4ac053689d980611e07043da20b61f808f050000003368dea31397e456802b43c388c0000230c28819a850982d67169c948d60000000197030b257e0001d4861780000000358000000000000004d803f445702d0518103c40c00008201db82fd8cf80019a7248c0000000000017091a20001036069a56000006c02a4173400000005728000000215e2a5000026600005271b8c00000000001ca60310aa00000000000000086c800000000006ab0c8058f97fe4ce80000fc8
  | 43 => 0x37e028650c899619b85fe35d17a200000006df18fc3b095de25394347f314e800010b434c800000000005a384361ba948e532124854391d232ba338302a0d2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xacd83152620410d4db0b29cc408002aba12539881000556c24a73102000e4f8354e620410b4dd0a29cc408002aba10539881000556c20a73102000e2f53d0e6204001c5aa7a1cc4080029ba16439881000536c2c873102084aad8490e6204001c9aa721cc4080039354d439881000747c1a873102000e2f5350e6204001d1ca6a1cc4080038b54d439881000746a9a873102000e0d5350e62040014dd0a21cc4080029b614439881041d57420873102000e1d5350d620400b1dd0fa92c408012b9a04525881002c7743e84b102005aea80109620400b1dd0f992c4080029ba17325881000536c2e64b102000aae84cc9620400155b09992c4080163b21d32588100053742864b102000a6d850c9620400155d08192c408002ab61032588100257340864b102005aea800c9620400155f08baac408002ab211755881002573408eab102000ae5811d562040014df0aba2c4080029b215745881002d75400e8b102000ae9801d16204001c5ea92a2c408002b3a0c545881000566c18a8b102000a6e859cd62040014db0b39ac408002aba12735881000556c24e6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102004ae6811cd62040015cb0239ac408016baa00735881000574c00e6b102086a6d8594d620400155d0929ac408002ab612535881000727c1aa6b102085a6e8514d620400155d0829ac408002ab610535881000717a9e86b102000e2d53d0d62040014dd0b21ac4080029b616435881042556c2486b102000e4d5390d6204001c9aa6a1ac408003a3e0d435881000717a9a86b102000e8e5350d6204001c5aa6a1ac408003a354d435881000706a9a86b102000a6e8510d62040014db0a21ac40820eaba10435881002c3fc3acb2902005cba70592520400b9b4e0b1ca4080031e59570948100065cb22e12902000cd9635c252040139d4c4b84a4080161f21776548100145e426eca9020008bf845d9520400517908bb2a4080161f21d65548100061e3a2caa9020008bd86dd1520407d87ccbba2a4080030f59774548100064f31ee8a902082cae62dd1520400117d0eb22a4080022f21d64548100064fba2c6a902000c9c7458d520400b1d90eb12a4080032bdd16254810006563a2c4a9020058ed825da42040098ece2b2c84080162fe1d64908100266b38ac72102000c75655c6420400196ac8b8c84080033558d719081004e73312e3210200387c85dd9420400b17909bb284080163b20b76508100043fc2aeca10200387c855d942040010fb0dbaa840810b0f99375508100062f31eeaa10207fc6e62dd542040010fd0eb2a84080021f21d655081002c5e43ac8a102000c3f755914204001878eab22840800317dd563508100062e3aac6a1020058ec8758942040018deeab1284080031b1d56250810
  | 1 => 0xd08192ca080028f61032594100253b40864b282000a75810c9650400b4f500192ca080029e600325941002c5f43ea8b202000c3f75d51640400317909b9ac80800327d0d73590100247a40ae6b202001c5e7354d64040018bae6a9ac8080162fa1e43590100051f42c86b202000a3d8590d6404001c3aa721ac8080162f21d43590100064fb9a86b202000e1d5350d640400187eeb3aac808002a7a0c75590100054ec18eab2020848bd879cd640400147d0b39ac8080028f61673590100055bc0ae6b202004ab4815cd640400193f06b9ac8080032de05735901043e5a40ae6b2020838be871cd640400147d0a39ac8080028f61473590100061fb9ea6b202000c3d73d4d640400117d0f29ac8080022f61e53590104351ec2ca6b202000c9d7394d640400193ae6a9ac80800387e0d53590100061fb9aa6b202000e1e7354d640400187ae6a9ac808003875cd53590100060eb9aa6b2020008be8714d640400117b0e29ac8082168fa1453590100255b40ce4b202000a3f855c964040014790ab92c808016aea00725901003d5cc00e4b202004ab681149640400156b02292c8080022fa1f32590100045ec3e64b202000a3e85cc9640400147b0b992c8080022fa1c32590100045ec3864b202000a3e850c9640400147b0a192c808012ada0432590100055ac0864b202005aba800c9640400157300192c8080161f21d655501002c5e43ac8aa02000a9e84dd5630400153b09baac60821a9761e7558c1042f2b884eab182085e5a109d5630410bcaa213aac608233964427558c1045d6dc02eab182005ad8805d563040018bf0ebaac60800396e017558c104372c402eab182086e57105d5630410dcb420baac60821b954417558c104572c882eab182085a5e851d5630400153d083aac608002a76107558c100052f42ee8b182000a5d85dd163040018baebba2c608212a761e7458c100070f3ace8b182000e1d759d16304107d2e213a2c60820fa68427458c1041f4a884e8b182089e99109d163040018baeaba2c608222b5e057458c100256a40ae8b182000c9f875d1630400193eeaba2c608003879d57458c100064ebaae8b182000e1d755d1630400183aeaba2c608003a5e057458c1043f4a40ae8b182084e97105d16304109d3420ba2c608213a54417458c1043f4c882e8b182000a5e851d163040014bb0a3a2c60820ea7a107458c100070faa4a8b1820008de8715163040011bb0e2a2c60800297a177258c100052ec2ee4b182000a9e84dc9630400153b09b92c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608012b5a047258c100356ac08e4b182005ada801c9630400d5b300392c608012b5a045258c100056ac08a4b182005ada8010963040015b300212c6080038bd52549881000567418a93102000
  | 2 => 0xf75589100061fbaee8b122000c3c75dd1624400117b07ba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f85dcd62440018b90bb9ac48800327e1373589100064e426e6b12200087f855cd62440070f90ab9ac4880022fe1173589100145e422e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b12200087e87d4d62440070f90fa9ac4880030fdd353589104861e3a6a6b122000c5f73d4d62440038b8e7a9ac4880021fa1d53589100043e43aa6b122000c3f7454d624411f878e8a9ac48800317dcd535891000e2e39aa6b1220008be87d0d62440051790fa1ac4880030fdd743589104761e3ae86b122000c9f73d0d6244003938e7a1ac4880022fa1d43589100045e43a86b122000c3f7550d624411b878eaa1ac48800327dcd435891000e4e39a86b122000e1d5350d6244003998e7192c4880063b21d325891000e6639a64b122001cd4738c562440031e90e98ac488007351cd315891000e6c39c60b1220018f8874c162440039b0e6982c488003b44c5305891000477c3ac431220028be849d9524400117b093b2a4880022fe1176549100145e422eca9220008df835d952440031b906bb2a48800e1fa1676509100043ec2ceca12200087f855d942440070f90abb2848800237e0d765091000c6e41aeca122000c3c74d9551440139d0c4b8642880031dd9771541100061e3aec8a022009ce4625c720440010ff0abb2408800e1f21576481100045fc22ec90220028bc845d920440011bf06bb240880063720d764811002c7b436e2902200587e87951650400187ee92a2ca080061f21773594100062fa9ae6b2820058f8805cd650400b0fd0f29aca080028fa1253594100051ec24a6b28200587c8754d65040018bee6a9aca08007279cd43594100064eb9a86b282000e1e5350d6504001c3aa6a1aca080030fdd274594100052f418e8b282000a5d831d1650410d0fb0f39aca080028fa1273594100051ec24e6b282000a7b805cd650400b4f100b9aca0800317e0d73594100063dc02e6b282086c78805cd650410b0fd0e39aca080028fa1073594100051ec20e6b282000c3f73d0d650400187ae7a1aca080021fa1e43594100043ec3c86b282084a3d8490d65040018bae721aca08003175cd43594100070fc1a86b282000c3f7350d6504001c3ce6a1aca080030f5cd43594100070eb9a86b282000c1d7350d65040010fd0e21aca080021f61c435941041d1f42086b282005a7a809c9650400147f08b92ca080028f21172594100253b408e4b282008a75811c9650400b4f500212ca080029e60042594100043f43e64b28200087d87cc9650400147d09992ca080028f61332594100043f43864b28200087d870c9650400147
  | 3 => 0xb2084036a3c85592410800187ceab2482100030f5d5649042004e57392c9208402bcae645ca410800195ac8b9482100162f21376504200043fc2aeca08400387c855d9410800517d0fba2cb880030fa1774597103de1ec2ee8b2e20008bd83dd165c400187ea7ba2cb880121fa1e54597100061fba4a8b2e20008bf845cd65c400517908b9acb880023be09735971004c76412e6b2e200487c8754d65c400187ee8a9acb8823f0f1d153597100062fb9aa6b2e20008be87d0d65c40051790fa1acb880022fa1d43597100045e43a86b2e2000e1d5350d65c40091790ea1ac98800327dcd43593100070ea9a86b26207b8bf845d954c4001c3aa6a1ac5880123ba1f4258b1000574c0084b1620048ec874c962c40039a8e698ac5880263ee197094b100045fc22eca9620028bc845d952c40090f90eb2aa5880030f1d16554b100247643ac4a962000cac7458952c40010ff0abb2858800e1f2157650b100267238ac4906200587c8754d65840018bee6a9acb080038754d435961001c3f43eeab242000c3e84dd564840c387b09baac9080021f60f75592100061fa1eeab2420058be87d51648400187eebaa2c9080021fe15735921001c3e42ae6b2420008ef825cd64840131d904b9ac9080021fa1f535921001c3e43ea6b24200087e8754d64840010f90ea9ac9080162f21d43592100061fbaa86b24208dc3c7550d648400193ee6a1ac9080038754d435921030c3fc2aecaa42000e1d5350d628400b1dd0fa92c5080031bdd75258a1000572c08a4b1420058ec874c962840039b0e6982c5080022fe117654a100145e422eca9420098f7865c642840010ff0abb2850800e1f2157650a1002c5e43ac8a142000c3c75591428400b1d90eb1285080031b1d56250a1002e74382c490c2000c3d7495365440030ff0ea9eca88003175cd53d95100070ea9a87b2a20028be87dd1654400117b07ba2ca880030fd4f74595100061fba8e8b2a20008bf845cd654400517908b9aca880023be09735951004c76412e6b2a20008fb805cd65440030f90ea9aca880030fdd1535951047e1e3a2a6b2a2000c5f7354d654400117d0fa1aca8800a2f21f43595100045f43a86b2a20008bc8750d6544001c3aa6a1aca880030f5d754d911000c5fc3a87b222000c9d7350f6444001c3aa6a1ec88800e1fa1f75591100043ec1eeab222000c3f43dd56444001878ebba2c8880021fe15735911001c3e42ae6b2220008ef825cd64440131d904b9ac8880023de0573591100043f43ea6b22200387c87d4d64440010fd0ea9ac8880021f21d535911000c5e43a86b222000c3f7550d644411b878eaa1ac88800327dcd43591100070ea9a86b2220098ee829d954440011db053b2a8880021fe1576551100045fc22ecaa22000e1d5350f6244001da262986c4880021f60
  | 4 => 0x4080c387b09baac8100021f60f75590200061fa1eeab204000a5d831d5640800b17d0faa2c8100030fdd754590200043fc2ae6b20400387c855cd64080131d904b9ac8100021fa1f535902001c3e43ea6b20400087e8754d64080010f90ea9ac810007179cd53590200062eb9aa6b2040058be8790d640800147d0b21ac8100028f61643590200070ea9c86b2040058bc8750d640800187eeaa1ac8102370f1d543590200064fb9a86b204000e1d5350d640801355904a1ac8100028f60f755902030f17906eab204061e3a20dd564080c3c5a41baac8101ff8e48375590202fd1f42ceab204000c3f759d5640800153d063aac810002a760c755902030d1f438eab204000c3e871d56408001c3d063aac8100028f60c75590200070ec18eab204000a1d831d564080fb87ce43aac8101f70f1c875590202fe1fb80eab20405fc3d701d564080bfc5e403aac81017f8e88075590202ff16900eab20407de39201d5640800187eebb9ac8100030f1d773590200061fc2ee6b204000c3c85dcd640810795e41b9ac81020f2e883735902041e56906e6b204094cb920dcd640810917b0f39ac8100028fa1673590200051ec2ce6b204000a3f855cd64080014790ab9ac8100030fdd573590200061e3aae6b204000aaf825cd640801355904b9ac8100030fe1573590200061e42ae6b204000c9f835cd640800195f04b9ac81024f2b209735902042657902e6b204084cba205cd640810995a40b9ac81024f2e481735902041c5f438e6b204000a3e851cd640800147b0a39ac8100028fa1f53590200051e43ea6b204000c3f73d4d640800187ae7a9ac8102178bc83535902042f1d106a6b204085e2d20d4d6408125c7241a9ac8100022fa1e53590200045ec3ca6b204086a3d8594d640800193ae729ac810003275cd53590200051f43aa6b204000a3c8754d6408001c3f06a9ac8100030fdcd53590200070f39aa6b204000c3d7354d6408001c3ae6a9ac810003075cd535902043717902a6b204086e3a2054d640810dc5a40a9ac8102478e48153590200045f438a6b2040008bd8714d640810b47d0a29ac8100028fa1671590200051ec2ce2b204000c3c759c5640801355d0538ac8100028fe1571590200051e42ae2b204000c3c751c5640801355d0428ac810002ab60851590200045f43e62b2040008bd87cc5640800147d0b98ac8100028f61731590200045f43862b2040008bd870c5640800147d0a18ac8100028f614315902004d5741062b204000aad820c5640800b5750018ac810002ae600315902030c3fc2aecaa040058bc875915408001c3aa6a1ac2100163d21d31584200145e426eca8840008bf845d9510800517908bb2a2100022f61b74544200045f43ac8a8840008bc87591510800b1e90eb0aa2100123b60976904201c61f322e
  | 5 => 0x38754d43d952042656b9287b2a4098e2f5250f654800517d0fba2ca900022f60f74595200061fa9ee8b2a4000c3f751d1654800117f08b9aca9000a2f21173595200047bc0ae6b2a40048f4815cd65480030f90ea9aca900030fdd1535952047e1e3a2a6b2a4000c5f7354d654800117d0fa1aca9000a2f21f43595200045f43a86b2a40008bc8750d6548001c3aa6a1aca900030f5d754d912000c5fc3a87b224000c9d7350f6448001c3aa6a1ec89000e1fa1f75591200043ec1eeab224000c3f43dd56448001878ebba2c8900021fe15735912001c3e42ae6b2240008ef825cd64480011ef02b9ac8900123d20573591200043f43ea6b22400387c87d4d64480010fd0ea9ac8900021f21d535912000c5e43a86b224000c3f7550d644811b878eaa1ac89000327dcd43591200070ea9a86b22400087f855d9544800117f08bb2a8900163ba1b72551200061e3a6caa924018c6f72d95524800b3d100b8c84900030f1d764509200c4b743eeaa124042c6c76dd542480f98d8ec3aa84901f74bdd07550920006963aec8a124000d6875dc142480010ff0aba6c29000e1f21574d85200070ea9a87b0a4001cd8734c361480011ef0eb08c2900031bd9572945200145f424eca8a40008bd849d951480090f90eb2aa2900e28f211655452002476414ed20a4000c3e75d924148057958c8b9482900167a20172905200c476c3ecb90a4018c6e75d97214806355908b2e42900c63b21974c85200c4b642ae990a4004cf0615c221480318d8ebb2a42900123b21d654852015d56422ca90a4004ae4815952148057958c9ba242900163b21974485200c4b642ae890a40059e8805d121480095cd0db0a4290002d9614614852002572434a290a4000e676594521480133c90ea8a4290002b9219514852000732b2aa290a40059ea87dc121480017530838242900031bd97725412002cf443a432024000bab844864048001878ebb2280900166b21d425012002d5643284a024045b2c85509404800b75100a12809009b1e1db75501202f63c3b0eaa0240059b8875094048013970eca128090116ce215425012004ed439284a024005ba8875094048013b510ea128090016eaa19425012002dd443284a024002ea8865094048005d56eca1280900276a9d9425012004ed43b284a024002ea8765094048001e570aa128090116eaa15425012022dd442a84a024000f2885509404808b6510aa128090003cadd54250120007943aa84a024097bab83509404812f75306a12809025b6adcd42501204b6d4b9a84a024095f2b53509404812be52a6a128090002eae05425012004e743b642a024000ba984c8540480013d10e90a80900273a1d92150120005d4c2242a02400587c8754d65080018bee6a9aca100038754d435942001c3f43eeab204000c3e84dd56
  | 6 => 0x637b2ce530a8000c6c659ca61500018decab94c2a00031b19572985400267230ae530a8000ce572d8661500c30f90dbaac2a00021fa1f65585400043f438cab0a80008f787584615004d87ce9b2ca2a00030fd95749454001c3e428eca8a80028bc841d95150001878a83b2a2a009b0f1d365545400061fb2ee8a8a8036c3c65dd151500c3878edb2a82a017f0f1d865505400071bb28c2a0a8000ba9821c141500010ff0abb642a000e1f21576c854002476412ed90a802093c855d32150001878caba642a00263e21970c85400063c32ae190a8009ce8625c321500010ff0abb442a000e1f21576885400247a40aed10a8000c3c655d221500070fd0bbb242a00021f617764854002c5e432e890a802093c855d121500070f90b3b042a00021fe15760854001c3e42aec10a800087c865d421500010ff0fb2842a00021f61f65085400247c432e010a8026c3c74d95505000187ecbba2a0a000a2fa1f745972041656396e8b2e4000c3e85dd165c810587b0bba2cb900022f60f74597200061fa9ee8b2e407dcac721d165c80130fd0f2a2cb900030fdd2545972030e36394a8b2e40008bf845cd65c800517908b9acb900163b209735972004c3e43aa6b2e4000c3f7454d65c811f878e8a9acb9000317dcd535972004d36412a6b2e4086c6c7254d65c800117d0fa1acb9000a2f21f435972041e5639686b2e40008be8750d65c80011790ea1acb900038754d43597204265639286b2e40098bc8750d64c800193ee6a1ac9900038754d43593204145fc22ecaa640058ec825d954c80fb2dd0fbaa85901f74bdd07550b2001c3f42ee8b0e400087d85dd161c8001c3aa6a1ac390026b9a0b415872004c7a43a62b0e4001cd4734c561c800117f08bb2a39000a2f211765472002c76412eca8e4038a3c8459551c8001878e8b2aa3900263d21d61547200065a3a2c2a8e4009ce47258551c800b1dd05bb2839007a3b21d654872015d56422ca90e402b8ed86dd121c803d2d90aba243900267921d514872000732b2aa290e40059ac8750940c81356590aa1281900161fa1e54596200061fba4a8b2c400587c8754d65880018bee6a9acb100038754d435962002c5f43ea8b244000c3f75d51648800b1790ea1ac91000327dcd43592200070ea9a86b244000aaf8250d6488001878e8b2aa5100030f1d56450a2001c3f42ee8b0c400087d85dd16188001c3aa6a1ac3100163d21d31586200076898a60b0c40008bf845d9518800517908bb2a3100163e20176546200061e3a2caa8c4005cf070585218800b3710ea128110156ce21542502200bf54b1284a044000c3d7495365480014db052a6ca900029e60254d952002c76c16e7b2a400187f8754f65480018bae6a9eca900029be0953d952043636b92a7b2a4083cad72d0f6548133c5ea5a1eca9
  | 7 => 0x3e7650f6550001a3ee6a1ecaa000387d8d43d95400070e31a87b2a8026a3f875d365500bf87f0eba6caa00028fe0d74d95401351f426e7b2a8061a3d84dcf655000187ce9b9ecaa00030f5d373d95400061f426e7b2a8000c3d84dcf655000187e87b9ecaa00031790f73d95400062ea1ee7b2a800087d879cf655004d47d0939ecaa00028f61273d95401351f422e7b2a8000c3e745cf655000187ae8b9ecaa00030fa1173d95400061ec22e7b2a8000c5f835cf655000187e86b9ecaa009a8fa1073d954030d1ec20e7b2a8000a3f8750f655000147b0ea1ecaa009a8fe0d43d95401370fc1a87b2a8000c3f7350f6550001c3ee6a1ecaa000307dcd43d95400061eb9a87b2a8000e1c7350f65500c347b09b96caa01f70f9d272d95400053b40ce5b2a8000a75819cb65500c347b08396caa01f70f9d072d95401353cc00e5b2a800087e87ccb65500010fb0f996caa009a8fa1332d95400051ec2665b2a800087e870cb65500010fb0e196caa009a8fa1032d95400051ec2065b2a8000a76810cb65500014eb02196caa01869ea0032d95400053cc0065b2a8061a3d84dc765500014dd0538ecaa00029b60a71d954030d1ec20e3b2a800087e87cc765500010fb0f98ecaa009a8fa1331d95400051ec2663b2a800087e870c765500010fb0e18ecaa009a8fa1031d95400051ec2063b2a8000a6e820c765500014db0418ecaa01869ea0031d95400053cc0063b2a802687e87cc365500010fb0f986caa009a8fa1330d95400051ec2661b2a800087f855cd65500011df04b9acaa00263b20973595400047bc0ae6b2a80048f4815cd65500030f90ea9acaa000317dcd535954000c5e43a86b2a8000c9f7350d6550001c3aa6a1acaa00021fe1f63195400062eb9ec632a800087d8798c655000147b09318caa00021fe1d631954000537c12c632a8000a6c8258c65500014ef02b18caa00029d205631954001c3f438c632a800087d8718c65500bd47d08318caa0003175cc63195402fd1e4328632a8026c3e7650c6550001a3ae6a18caa000387d8d43195400070ea9a87b128000aad840cb62500015cb02196c4a0002ba60032d89400063bb2ce33128000c74659c662500018eecab8cc4a00031d195719894000673b12e33128009ce4625c662500010fd0fb2ac4a00021fa1c655894000477c3ac43128026c3e74d9652500c38f4e1b2ca4a00030fd95749494004c7c432e129280028bc841d9525004d878e9b2aa4a00030fd9774549401f61e32ee8a9280059ba80dd152500f927d0fbaa84a01ff0f1db75509403ee1fbb0eaa12807dc3c761d5425000127d0fb2a84a01870f1db65509402fe1e3b0caa128000e2f651894250001a70ebb8284a00034edd470509400070ea9a87b0a8000ab5840c761500015cb0418ec2a0002bc60031d85400
  | 8 => 0xb21ac5280029b6164358a5000726a9c86b14a000e4d5350d6294001d1f06a1ac5282638bd4d4358a504c74729a86b14a000e2d5350d6294131d1aa6a1ac5280038354d4358a500c53742886b14a000a6d8510d62940014df0ab8ac5280029b6147158a5000672b88e2b14a005aea8010562940015d30020ac5280629ba173158a5000536c2e62b14a000aae84cc5629400155b0998ac5280023ba1c3158a5000476c3862b14a018a6e850c562940014db0a18ac528002aba103158a5000556c2062b14a005aea800c562940015d30018ac5280271b9897590a501061f3aac9214a000c3d75592429408587cc9baa85281ff1b98b7550a500061fbaac8a14a020c3c75591429400b1d90eb1285280631b1d56250a5004c77416e8b0ca0008ed82dd16194001c3aa6a1ac3280163d21d31586500061e2a2ed20ca038c3e645d6419404187ceab2483280030f5d5649065000476c34e520ca031cae649ca419400195ac939483282734b152729065000477c32e520ca02bcae645ca419400195ac8b9483280263be1e629065000476c3cc520ca01ec6e7598a41940018daeb314832826f8b152629065000477c3ac520ca0008ed8758a41940318dceab1483280031b5d5629065002c5e426eca0ca000c3f755914194041878eab2283280031bdd662506500f6363acc4a0ca0058ec82dd9219400187cc9baa43280631b1d562486500257240ac490ca0058ed825d8219404d27908ba843280030f991750865004e37312ea10ca020c3e75590219400187aeab2043280631b9d5620865000636baac410ca000c5f7354f645400317f0ea1ec8a8003275cd43d91500070ea9a87b22a000e1d5350f62540011df0eb10c4a8002ab60b649095001c3e428eca12a000e1d5350f61540011ef0eb08c2a81ef0f1db74545503ce1e3b0e8a8aa000b658218551540090f90b3b482a80e30f19175905500061ebaec920aa000caf649ca4154063958c939482a80123ba0a76c85500243e42cec10aa0008bf845d8215400517908bb042a80161f21d53596400062fb9aa6b2c8000c9d7350d6590001c3aa6a1acb200038754d4358a4000637baea4b148000ae581149629000b1d90e992c5200029be096594a400070ea9a86b0c80058f4874c5619006d87ccbba2a3200030f597745464000657ba2c490c80058bd84dcf655000187ea9b9ecaa00030fd5173d95400051ec24a7b2a800187f8754f655000147f08a9ecaa021b0f5d153d95400062eb9aa7b2a80848bd8750f655004147d0aa1ecaa00828f21543d95400064fb9a87b2a8000e1e5350f6550001c3aa6a1ecaa017f0f9d974d954030d9c402e9b2a8000c5d73d8f65500014df04b1ecaa00029b20963d95400053bc0ac7b2a8000a748158f65500410fb0e31ecaa0003175cc63d954030d1e43287b2a805ec
  | 9 => 0x73592500061e3aee6b24a000c3f85dcd64940018790bb9ac9280030fd4f73592501051f42ce6b24a000a3d859cd649400147f0ab9ac9280828f21573592500061e3aae6b24a000c3f855cd64940018790ab9ac92800327e0d73592500061fa9ae6b24a000c9e535cd649400193aa6b9ac92820e2fa1c73592501351f428e6b24a000a3d851cd64940014790ea9ac9282168fe0d53592501070fc1aa6b24a000c3f7354d6494001c3ce6a9ac9280030f5cd53592500070eb9aa6b24a000c1d7354d649400147b0b392c9281f70f1d672592500055b40ce4b24a000ab5819c9649400147f0ab92c9281f70f1d4725925002d5d400e4b24a026ab9801c9649400117d0f992c9280022f61f32592501051f42e64b24a000a3d85cc9649400117d0e192c9280022f61c32592501051f42864b24a000a3d850c9649400156d02192c928002ad604325925002d5d40064b24a000ab9800c9649400147b0b38ac928002aba0a715925000556c14e2b24a000a3f855c5649400117d0f98ac9280022f61f31592501051f42e62b24a000a3d85cc5649400117d0e18ac9280022f61c31592501051f42862b24a000a3d850c5649400155d0418ac928002ab608315925002d5d40062b24a000ab9800c564940bf4dd092a4c52807b8ba125498a5000536c1ca9314a000a6c8454e629410b4df06a9cc52807b93e0d5398a5000537c2e87314a01ea6c85d0e6294001c5ca9a1cc52827f8b1534398a5000717c2e87314a09fe2c85d0e629413fc5ea7a1cc5280038b54f4398a500f53742c87314a000a6d8590e6294001c9aa721cc5280029be154398a500f53642a87314a000e2e5450e629413dc58a8a1cc5280039354d4398a5000717c2a87314a09ee2c8550e6294001d1f06a1cc52827b8bd4d4398a504f74729a87314a000e2d5350e629413dd1aa6a1cc5280038354d4398a500f53742887314a000a6d8510e629413bc58a820cc52807a9ba173198a5000536c2e63314a000aae84cc6629400155b0998cc5280263ba1c3198a5000476c3863314a01ea6e850c662940014db0a18cc528002aba103198a5000556c2063314a005aea800c662940015d30018cc5280038754d4358a5002d7540084b14a000a6d85cc9629400155d09992c528002ab6133258a5002c7643a64b14a000a6d850c9629400155d08192c528002ab6103258a500057340864b14a000ae5810c9629400b5d500192c5280029be157458a5002d75400e8b14a000ae9801d162940314dd0b39ac5280029b6167358a5000557424e6b14a000aad849cd62940314dd0a39ac5280029b6147358a5000557420e6b14a000aad841cd62940015cd0239ac528002b96047358a5002d75400e6b14a000ae9801cd629410b4df06a9ac52806393e0d5358a504cf17a9e86b14a000e2d53d0d62940314dd
  | 10 => 0xb2842008bf845cd650840517908b9aca108263b20973594210243f43ca6b284200a3e8494d650840147b0929aca108121f21d53594210061fba2a6b28428fc3c7454d65084018bee6a9aca108269b20953594210045f43e86b2842028bc87d0d650840117d0ea1aca108022f21d435942100e4f39a86b284200c9d7350d6508401c3ca6a1aca108038754d43594210051ec1ee8b28427be2f21dd165084f7c6c43ba2ca109ef8b48774594214171a90ee8b284279a3e849d1650840187ee93a2ca1080297a0c74594210052ec18e8b28427ba3e871d1650840187d0e3a2ca1080387a0c74594210051ec18e8b284200e1d831d1650840143b063a2ca109f70f9c874594213ee1e390e8b284279c3f711d165084f387ae23a2ca109e78bc8474594213cf1b108e8b284279e2d211d165084fbc6a423a2ca108030fdd373594210061e3a6e6b284200c3f84dcd650840187909b9aca10a331bc8773594214663b10ee6b28428cc6d21dcd65085258ea43b9aca10a2a1f61e73594210051f424e6b284200a3d849cd650840147f08b9aca108028f21173594210061fba2e6b284200c3c745cd65084014df04b9aca108269b20973594210061fc22e6b284200c3c845cd65084018bf06b9aca108031be09735942148e36412e6b28428ac6f215cd65085158ec42b9aca10a2b1b485735942148e3a90ae6b28428c87e871cd650840147d0839aca108028f61073594210051f43e86b284200a3c87d0d650840187ee7a1aca108030f5cf435942144f1790e86b284289e3621d0d6508513c5a43a1aca10a538d48743594210043f43c86b28420087d8790d650850f47b0921aca10803175ce43594210062eb9a86b284200a3e8750d65084014790ea1aca1080387e0d43594210061fb9a86b284200e1e7350d650840187ae6a1aca10803875cd43594210060eb9a86b284287e2f2150d650850fc6c42a1aca10a1f8b485435942149f1a90a86b28420087e8710d65084010fb0e21aca10a268fa1043594210051f424e0b284200a3d849c16508401878e9382ca108269ba0a70594210051fc22e0b284200a3c845c16508401878e8382ca108269ba08405942100536c1080b28420087e87cc165084010fb0f982ca108028fa1330594210051ec2660b28420087e870c165084010fb0e182ca108028fa1030594210051ec2060b284209a6e820c165084014db04182ca108129da0430594210053ac0860b2842048bc8750d640840193ee6a1ac8108038754d43590213dc5fc22ecaa0420487c875955408401c3aa6a1ac0108123e21d30580210061f2a6e6b24a000c3e545cd649404d47d08a9ac92809a8f21153592500062eb9aa6b24a000a3d8590d6494001c3aa721ac9280162f21d43592500051fc2a86b24a000c9f7350d6494001c3aa6a1ac92809a8f217
  | 11 => 0xc84092d90ea92a390a8ecb21152547210145f426eab0642008bd84dd560c8401c3aa6a1ac190826baa0b505832104c7c43a60b064201cd8734c160c84090fd0f2a2cb108030fdd254596210243e43aa6b2c4200c5f7354d65884014df04a9acb108038754d43596210245f43ea8b244200c3f75d51648840956d03aa2c9108122f21d43592210064fb9a86b244200e1d5350d6488401878e8b2aa5108030f1d56450a21024ba43aa4a8c4272b34845495188459ccac4a92a31080a2fa1375582210045ec26eab044200e1d5350d60884091f10e982c110803b44c530582210061eba4a9b2a420187f8754f65484018bae6a9eca908038754d43d95210145f43ee8b2a42008bd83dd1654840187ea7ba2ca908030fdd474595210045fc22e6b2a42028bc845cd65484011df04b9aca908023ee01735952102c7c402e6b2a420187c8754d654840187ee8a9aca90a3f0f1d153595210062fb9aa6b2a42008be87d0d65484051790fa1aca908022fa1d43595210045e43a86b2a4200e1d5350d654840187aebaa6c890802ab60b54d91210055ac0ea9b2242048ed82dcf64485198dae5a9ec890a2b1b5c953d912100c5fc3a87b224200c9d7350f6448401c3aa6a1ec890802abe0943d912143e56b9287b22420387e87dd564484010fb07baac8908030fd0f75591210061e3aee8b22420087f855cd64484070f90ab9ac8908023ee01735912102c7c402e6b22420087e87d4d64484070f90fa9ac8908021fa1d53591210043e43aa6b2242018bc8750d644840187eeaa1ac890a370f1d543591210064fb9a86b224200e1d5350d64484010ff0abb2a8908022fe11765512102477436e4aa242049e4815c25248401878e9b2aa4908034b1d3655492115cd743ee8a92423ecac76dd15248501958ec3a2a4909f74bdd47454921006d23a6e2a924200c3c75d914248401878e9b2aa2908125b21d525452102536432a4a8a4266b2c8454951484096c902a92a2908db2d1db74545213c65a3b0e8a8a42049748754951484138e8eca92a29099acd211525452104eb2392a4a8a4204b64875495148413ac90ea92a290812d9a195254521025b2432a4a8a4203e64865495148407cceeca92a290827599d9525452104eb23b2a4a8a4203e64765495148401e4f08a92a29099ad9a115254521335b2422a4a8a4200f248454951484cd64908a92a290803c9dd15254521007923a2a4a8a42a2b678354951485456cb06a92a290a8759dcd525452150eb2b9aa4a8a42a0f27435495148541e4a86a92a290802d9e0152545210045fc22ebb0242028bc845d76048401c3aa6a1ec090807351cd31d81210047dc3ac030242028be87dd1650840187d0bba2ca109ef0f61774594210045ec1ee8b284200c3f53dd1650840153b063a2ca108121fa1e54594210061fba4a8
  | 12 => 0x802ab6133098a4104c774386131482008ed870c262904014dd0a184c5208029b6143098a4118d57420613148200aad840c262904095cd02184c520802b96043098a410070ea9a86b148204ae68114962904014dd0b992c5208029b6173258a4100556c2664b1482048ec874c962904014dd0a192c5208029b6143258a4100556c2064b148204ae6810c962904015d500192c520802ba6003258a4100557c22eab148204ae6811d562904015cb023aac5208029ba167358a4100536c2ce6b14822baae849cd629040155b0939ac5208029ba147358a4100536c28e6b14822baae841cd629040155b0839ac520812b9a047358a4100572c08e6b148200aea801cd62904015d30039ac520a978bd0f5358a4115d57424a6b148200aad8494d6290401c9f06a9ac520a938bd0d5358a415272721aa6b1482a4e4d4354d629045755d0829ac520802ab6105358a4144d57c1a86b14822be8f8350d6290401c5ea6a1ac520803a394d4358a4100716a9a86b148200e8d5350d6290401c1aa6a1ac520802abe117058a4100556c20e0b148200ce9701c162904095cd02282c520802b96045058a410053742e60b148200a6d85cc1629045755d09982c520802ab6133058a410047743860b1482008ed870c162904014dd0a182c5208029b6143058a4115d5742060b148200aad840c162904095cd02182c520802b96043058a411c61f3a2cb2948200c3d655d2529041395cc4ba4a5208e30f1d16554a411f61f32ee8a948200c3d65dd1529050595cc5ba2a5208123b21d6254a4115e563a2c4a9482098ee82dd560904011db05baac1208038754d43582410247c43a60b04820187f8754f65504018bae6a9ecaa080327dcd43d95410070ea9a87b2a82008bf845cd65504011df04b9acaa08263b20973595410047dc02e6b2a82058f8805cd65504030f90ea9acaa08db0fdd153595410062fb9aa6b2a82008be8750d65504031790ea1acaa080327dcd43595410070ea9a86b2a8200e1d5350f62504011df0eb10c4a08029b60b65949410061fb2ee8a8a8236c3c65dd15150401c3aa6a1ec0a08023ee1d601814104c3e43aa6b2e4200c5f7354d65c8401c3aa6a1acb9080e1fa1f75593213fe36396eab264200c3e84dd564c84ff87b09baac9908021f60f75593210061fa1eeab26427dc6c721d564c841317d0faa2c9908030fdd7545932104d57416a8b26427bcac72d5164c84010ff0ab9ac99080e1f215735932102476412e6b26420087e87d4d64c84070f90fa9ac990a331b1cb53593210043f43aa6b26420087c8754d64c85158d8e4a9ac9908262f21d43593210061fbaa86b26428dc3c7550d64c840193ee6a1ac9908038754d435932104d5641286b264287cac7250d64c84ff0ff0abb2a9908123b20976553213ecd743ee8a96427dd2f751d152
  | 13 => 0x61ebaec9212a27bcb671d9242544131e90cb8c84a890b0f19375509510061fbaec8a12a236c3c75d91425441355d05b2284a88038754d43d81510053cc2861b02a200ae9820c360544015e302186c0a88032bd92729815100656324e5302a200caf645ca6054401958c8b94c0a88173a181729815100674b96c1302a27b8bc86dd1605440117d0fb22c0a88022fa1c64581510047dc3ac0302a200c3f54dcd659040187ea8b9acb208121fa1e53596410051ec24a6b2c820487c8754d659040147f08a9acb2080317dcd53596411b51f42a86b2c8236a3c8550d659040193ae6a1acb208038794d43596410070ea9a86b2c8279a3e87dd1659047187d0fba2cb208028f60f74596411c51e426e6b2c8200c3f74dcd6590401878e9b9acb208030fe1373596410061e426e6b2c8200c3f43dcd65905150fb0f39acb208e28fa1273596410051ec24e6b2c8200a3f845cd659047147908b9acb208030fdd173596410061e3a2e6b2c8200c3f845cd659040187908b9acb2080317e0d73596410061fa1ae6b2c8200c5e435cd65904018ba86b9acb20a321fa1c73596411c51f420e6b2c8200a3d841cd659040147d0ea1acb208028f21d435964144d1fc1a86b2c8238e1f8350d659040187ee6a1acb20803879cd43596410061eb9a86b2c8200e1d7350d659040183ae6a1acb208028f61272596413ee1e3a4e4b2c8200a7a809c965904014f301392cb208028fe1172596413ee1e3a0e4b2c8204a76811c9659046d4eb02392cb208021fa1f32596410043ec3e64b2c8238a3e84cc9659040147b09992cb208021fa1c32596410043ec3864b2c8238a3e840c9659040147b08192cb208129da0432596410053ac0864b2c8200a7a800c965904014f300192cb208028f612705964100537414e0b2c8200a6d829c1659040147f08b82cb208021fa1f30596410043ec3e60b2c8238a3e84cc1659040147b09982cb208021fa1c30596410043ec3860b2c8238a3e840c1659040147b08182cb208029ba08305964100536c1060b2c8204a76810c165904014eb02182cb209e6aba175498a4118f1742ea93148200aad83d52629046355909a9cc5208038bd535398a41547162a6a73148200e2f84d4e6290551c5909a9cc520aa38bd0f5398a4118d57424a73148200aad8494e629040155f08a9cc5208c6ab2115398a4100717aa2a731482a7e2c5454e6290401c5f08a9cc520a9f8b2115398a4100727c1aa731482a7e2f4354e629054fc9c86a9cc520a9f9350d5398a4118d57420a73148200aad8414e629040155d0aa1cc520802ab2154398a4144d57c1a873148231e8f8350e6290401c5ea6a1cc520803a394d4398a4100716a9a873148200e8d5350e6290401c1aa6a1cc520a9b8b1505098a410053742e613148200a6d85cc2629046355d09984c520
  | 14 => 0xc8750d649440193ee6a1ac9288038754d43592510070ea9a86b14a200ae98010962944091d90e992c5288038754d43582510247c43a60b04a200c3e54dcf645440187ca8b9ec8a88e28fa1153d91511c51e422a7b22a200c5f7354f645440147b0b21ec8a88038754e43d915100c5fc3a87b22a200a3f8550f645450f87aeaa1ec8a8803275cd43d91510070ea9a87b22a279c3e765d7645440193ae7b1ec8a8802abe0963d915100556412c7b22a200abb8058f645440157100b1ec8a88e22f61c63d91510064eb98c7b22a27ba3c8654f645451f87ceca9ec8a880347dcd53d91510070fb1aa7b22a200e1c6354f645446d47d0bb9ec8a89ee8f61773d91510061f3aee7b22a200c3e85dcf645440187b0bb9ec8a88030fd4f73d91510064f29ee7b22a200c9d53dcf645440117b0f39ec8a88e28fa1673d91510051ec2ce7b22a238a3e855cf645440187ceab9ec8a88030fa1573d91510061ec2ae7b22a200c9f835cf645440187ea6b9ec8a88da8fa1473d91513dd1ec28e7b22a200a3f8754f645446d47f06a9ec8a88db87e0d53d91510061fb9aa7b22a200e1f7354f645440183ee6a9ec8a88030f5cd53d91510070e39aa7b22a27ba3d85dcb64544fb87ceb396c8a88032bdca72d91510055d404e5b22a200ab9809cb64544f747b0a396c8a89f70f9d472d91511b55ac08e5b22a2008be87ccb645440117b0f996c8a88da8fa1732d91510051ec2e65b22a2008be870cb645440117b0e196c8a88da8fa1432d91510051ec2865b22a27bab6810cb645440156b02196c8a8802aea0032d91510055cc0065b22a2368be87cc7645440117b0f98ec8a88da8fa1731d91510051ec2e63b22a27be94314c764544f747b0bb86c8a8802aba0a70d915100556c14e1b22a27ba3d851c3645440117d0f986c8a88022f61f30d91511b51f42e61b22a200a3d85cc3645440117d0e186c8a88022f61c30d91511b51f42861b22a200a3d850c3645440155d04186c8a8802ab60830d91513dd5b40861b22a200ab5810c3645440193ae7b18c8a88022f61e63191510051ec2cc6322a2008bf8758c645440155f04b18c8a8802ab20963191510055dc02c6322a200ab88058c645440517d0e318c8a88022f61c63191514851f428c6322a200c9d7318c64544f34790ca98c8a8803475cd53191510070fb1aa6322a200e1d5350f62544014db0b996c4a88029b61432d895100572c0865b12a200ae9800cb6254401976c9384c4a88032e19270989510065db22e1312a200cb8645c262544019d6c4b84c4a88273a18970989510045f43ec8b12a2008be8719162544011df0eb10c4a88e24fa1f74549514161e3b6e8a92a27dc3f761d152544fb878ec3a2a4a88024fa1f64549513de1e3b6c8a92a279c3c761915254401a68e9b8aa4a88db0f9d7649095100
  | 15 => 0x4324c2a90022fa1f64585520045f438c8b0aa475c3e7519061548011ef0eb08c2a90038754d43d815229656b96c9302a4aecad72192605495b9d2e5b04c0a920a2f21b74581520045f43ec8b02a4008be8719160548011f70eb00c0a90030fd5373596420061faa2e6b2c840987c8754d659080147f08a9acb2100317dcd53596421f51f42a86b2c8400c9d7350d6590801c3aa6a1acb210038754d435864204c7a43a62b0c8401cd4734c56190801c3aa6a1ac1210263e21d30582420051ec24a7b2a8400c5d7394f65508030ff0ea9ecaa1003175cd53d95420064fb9a87b2a8400e1e5350f6550801c3aa6a1ecaa1003175cf63d95421e43ec38c7b2a8400c5d7318f65508ff4790ca1ecaa11f30f9d943d95420068fb9a87b2a8400e1f6350f6550801c38c6a1ecaa11fecb20943d95420061fa1ee7b2a8400c5e43dcf65508018ba87b9ecaa10021f61e73d95422151f424e7b2a8400a3d849cf65508018bf06b9ecaa10030fd0d73d95422151f420e7b2a847fa3d841cf65508018bae639ecaa110a8fe0d43d95422170fc1a87b2a8400c3f7350f6550801c3ee6a1ecaa100307dcd43d95420061eb9a87b2a8400e1c7350f65508850fd0f996caa10021f61f32d95422151f42665b2a8400a3d84ccb65508ff47b09b8ecaa11fe9ba0a71d954237d36c14e3b2a840087e87cc765508010fb0f98ecaa110a8fa1331d95420051ec2663b2a840087e870c765508010fb0e18ecaa110a8fa1031d95420051ec2063b2a847fa6e820c765508014db0418ecaa10029ea0031d95420053cc0063b2a847fa3d841c365508854db04386caa10021fa1f30d95420043ec3e61b2a8442a3e84cc3655080147b09986caa10021fa1c30d95420043ec3861b2a8442a3e840c3655080147b08186caa11fe9ba0830d954200536c1061b2a8400a76810c365508014eb02186caa10021fe1573595420045fc22e6b2a84008ef825cd65508030f90ea9acaa10fb0fdd153595420062fb9aa6b2a84008be8750d65508031790ea1acaa100327dcd43595420070ea9a86b2a843ec3f645cc65508010ff0fb18caa1003175cf63195420043ec3cc632a8400a3d8498c65508010ff0eb18caa10028fe11631954256537c12c632a840387e8718c65508010fb0e318caa11f28fa1063195420062eb98c632a847da3e8650c65508fb4790ca18caa110b0f9d943195420068eb9a8632a8400e1f6350c65508fb65904a18caa110b0f1d365549420061fb2ee8a92843ec3c65dd15250801c3aa6a1ec2a11bf1b5cb659854255e36b90cb30a84aace572d8661508010fd0fb2ac2a10021fa1c65585420047bc3ac230a8400e1d5350f60509538dae432cc0a11fe1f21b75581420043f43ecab02840087e8719560508f987ce8328c0a10023ee1d60181420062eb9aa6b24a2048b
  | 16 => 0x400000000340000000000018002000000000c00a0000000000000001000000c0060010000014006007002000000000000000000040020000000000002001000800000200080000000000028004000000000001400200100500000000050000000004002000000400000000000000020010008008002000000800000000000200000000050000000000000000000c0000000000000000001000000000000d000000401c3aa6a1ec4aa0029b61732d895400536c2865b12a800aad840cb62550015cb02196c4aa002ba60032d895400477c3ac4312a87fa6f85588625510555f08b10c4aa0038754d43d85543de57b24e530aa8b2c7575d8661550011ef0eb08c2aa1eeade1161185540070ea9a87b02a861c6f659ca6055163972e9b04c0aa0023ee1d601815430d3dc2ac0302a800c3e54dcd649480187ca8b9ac92910a8fa1153592520062eb9aa6b24a4098bc8750d649480147f0aa1ac92900327dcd43592520070ea9a86b24a400e1d5350d61948131e90e98ac329007351cd31586520070ea9a86b04a4098f8874c160948039b0e6982c12900317dcd53d91520051ec2c87b22a400e1d5390f645480317f0ea1ec8a9003275cd43d91520070ea9a87b22a400c9d73d8f645488117b0e31ec8a9003275cc63d91524151e432a7b22a48fc3e7654f6454801a3ee6a9ec8a900387d8d53d91520070e31aa7b22a482b2c8254f645480187ea7b9ec8a90032794f73d91520064ea9ee7b22a4008bd879cf645488147d0b39ec8a90028f61673d91520064fc1ae7b22a400c3f535cf645487d47d0a39ec8a920a8f61473d91521f51fc1aa7b22a43ee1f8354f645480187ee6a9ec8a900387dcd53d91520060fb9aa7b22a400c3d7354f6454801c38e6a9ec8a90fa2fa1f32d91520045ec3e65b22a43ea3e85ccb645480147b0b996c8a920a8f61471d91521f556c10e3b22a4008be87cc7645480117b0f98ec8a90fa8fa1731d91520051ec2e63b22a4008be870c7645480117b0e18ec8a90fa8fa1431d91520051ec2863b22a482aae820c7645480155b0418ec8a9002aea0031d91520055cc0063b22a482a3d85dc3645490555d05386c8a914aab60a70d91520065db84e1b22a4008be87cc3645480117b0f986c8a90fa8fa1730d91520051ec2e61b22a4008be870c3645480117b0e186c8a90fa8fa1430d91520051ec2861b22a482aae820c3645480155b04186c8a9002ada0430d91520055ac0861b22a442c3f655cc645480193ae7b18c8a90022f61e63191520051ec2cc6322a4008bf8758c645480147f0ab18c8a92c2abe0963191520145f438c6322a4008bd8718c645492147d0a318c8a9003275cc63191523ed1f432a6322a47da3c8654c6454801a3ae6a98c8a900387d8d53191523ed96412a6322a400e1d5350f615495f95ae
  | 17 => 0x40000008000000000000000000a004000000000200000000040020000000000000005000800400600100280040020020010004002003000800400000200000040020010000000000001000000000200400100000040000000010000000000000400200400000040020000000004000000000000800000700080040020000000000000000000800000000000080000000050008000000000002001c008002001000000400000080000020000000018000001000000000000000000000000000000004000005001000400200000000040000000000004006000000000000400200080000000000000000000000000000800000a000000800a00200300040020000018008002000000001c0000010008010000000000800000400000180000040000000000002000005000000200000380040000000008008004005000000000a0010028000002002000001000a00100000000080000008000000000001800000000100100000020050000000002000000800c006000001800c0000000000008002000001800000800100000000000050000018006000001000800000100000040040010010014000002000800000800100080000020010000004002001001800c002000001000c00200300000040080000008000006000000000800000000000100040000008000000009000000800200100180000000020030000000003000800c0000000000000000000000000800000100000000060000018000008000002000000000000180100040000008000000002000001c00000a0000008000000000000400800000000040000000000000000002003001400200000100040020000010000000000000003400000000080080000060008004000000002800c006002002000000e000000800c0000060000000000000000000000000000080000020000020004000000001000400400000080000000070008000000003001000000400200200100000000000010000000001800000200000000080020000010008000000001000400000000080000000000008000006004000000000a0040000000000000000000800a000000001800000100080140000000010004000004000800000200200080080000000010000000005000000000400a0018000000003000800800c0000000000002000003000c0020010020010000000000000400000200080040000000020000000002001000000400500000000000030000000000000001800c0000020030000000010000000000a004004000400200000000040040010020030000000000000000000000200080000030008004000002000800c00200100080100000010028000000002000000000000200000000000010018000006004002000000200000100100020020000004000000000000000200000000040000090
  | 18 => 0xf00ba000113e00000019f0db0000000000000004d00000000000001eb000000088f0b122246e88c24000000000000000000104047b30a9428d9000048f16bc00000039a0154e8c0002448000000000000000000000031900000007914599c9404808140e80000002fa00000008e60000000000fa06e9000235c00034d0cd00011e85e3000127c000000000000000059e0000000000000000000000000000000009b8872000210903800000011f800000000000240005232a302681ca3ac07a80011f000040f906d19600000000005ce4390a001c4d120002c50188cee65f0a499bd1d263a2ef0add1c466d1a280000000004060cecc864990f18000000136027141800037200005850525932438000000000000106859c44828a800000000000008dc0347bb16580000002020000a1851800035e8a540000000000dbc0007eb00002dc9f28db48e9784000000418a4300001af349000018e5390438000a78298000017c000000000002c000000196897c5e800041680008c48701d701ec0000002679ea854433d33000006908c400017400000000000000ec60000f81e383d000000000384241210000a2c1fa0000001f704541cd39800008c6553000061800000000000000000000000000b9230a4049da400000023b000000044113f00003f400000000009060000bd800000011f00000000000001d31384fb0000000000076446d47e0000000269000099c0000003c1000000057800000000000000518000d842e02f90d68000000000000000081e3438000e5a00028c80005f20003711a8505025000008d0b220000000000d7c2b43dd04f0000000000000115a00000015a0586000000211400008b00022d0fc03a338516c00003cc23f97681b2000000000000000043380000002fb0001d5000031f00021f800038300009a800000013b8c68ff68390000590ac06492ea800000000000017d4dd400000000000000000000dc00000000001858cb81a600020380000000000000cc41f61d809e0000000063145c0000000e58000f1e3b50b1800062200000000005cc07e10e8a2400000000000002f400015b17ac0007a100000000004e80000000000000000000000000045380000005e20000000000000000129037c000000000080829b00000009422b200012e8dee41800006ec2845fb0000f8474a00000000746a20002f3a2c40002014401dc0718000242800000033900000000008b71be0f24302000000061000066b000000000000015c07d40000002cd800120241d0fe138caf823205c8958df428130c80006a860f000039cdac6642ff000000200080080000060008004000001000000000400b001001400400100100000020010000000000002000000400000000000200000010018000014001000800400000100180000040000000000
  | 19 => 0x113c000186000000000000002800000001e20000000000141241c29600037b000106e000094800000072220b194400027f1228d588ce624000186800000014b9ea40000001ba93600000000001ec400010817596510c0082148027800000038020f0dda3b90001f547043e3000000123600000000000d00e30f4800000029300000009e882108324144a20003a0825449400004794d82aa8ef277000000042d48183045940000001090b7a13d1a793245de7df00009645ee00000003d85240002791b700000000000c480000002f20ff00004c20000ea465c6f100023a8a8a64b000102915626b000000114c822000000000000011c80000005ab27580007445122b3a2505dc00000000000d20001c80b5800000000000000008be3bd83fc0007fe064247c0000000001dd45c80000000000ff87d40001fbd1ac0000001e0ce4e55a30e8000e2025e0000000000000320076400045e000000028a000000000000000000019080f073900019a80000002012354d4000000001b8126786000224400000000008c000072f00006889cc0002750000ee800000018380003d80450000fec0000001aa400000014e00000000000000000000000106890866a0000001b380000001cda048f180000000000cb6000000000000000034b0efc29833605506d00000002c79f980002f844097b000000000000000001d80000000000000304800000019e0b00f38000000000000000000000000000000002f71fa80004fb2c400010dc82e1f400003380000000000000000130800089e1ca02b0000e544b40000000000000000000087c39d00011680000e800023300008ed435944c3aa000372000000000045d80000000a93180aa800000000005f800000000000000006c508a98000003dc00000008b20000001d5c09232205e00000007b500000009a600000004105587a000023fc00038000000000000003e6000000000000006d8000107369800045200003c80006d8000000000000000005d80000006ba1479728c940000af0000000000000000109617500003dc0001f1475800000004f0000000000000258000000000003200000000000000000a9600000021903300000000ac000010d31c800000000002f12411240000000000a703bc11103080000002ec8e50aec243000217c0000003d71a0115e3da0001b98000000000000000000000004040000001a58000c8c187000135c0000000001b30dbc4b600784dc00000018f00003dc44744100000000000000000aa000000000004ca0000000000f30000000000079400010f80000000fa1e9173cbde87b215000000000027022680000000000000000000000000000045c44297cc5d000000000005fe00000000004701770001b480000002e00000ed06124890000000000000099000084f1fc8008a40
  | 20 => 0x3c200010e62703238000a3c8fa0618000972000000000000085b3958634d226ef09c0000b3207516e00000004570960cc8f780003c98000000555000040c0000002960000e4600000000a00000000001f5c7ba0000001c60000392000000073e8d903f83780005ce14fa0643525922c70bb4b6c11b03180010e2000154870496e2621258d10e6e5730668000c5472900008440000002bf8b1002a53e0f9a06007c82629a8e2c86c00000000000000002231d646801ba0000f98000053000000000000015980d000029e000000081000037f00000000000000000fd200032a945800022d486a33800000000014a80000000000000a2841f3d580000000002680464d7801600020e83846850fc17d0fb216717999f8ccc05d0132128e36000000000000060101a9ee400000000004000008480fb80000008de12687580003d30001c3407000000000000002d30020110d9a00003d08680000002d280009080000000abd1108b6000000000081b000000000000000024440000000a3000000061e0ae919424a00006f8000000000000000004a0000000000000000000214000090e00000000000000000000000000435000117a71f0521bb0628000000000000060848504b400038500000004b60002058b0400000005d0000000319000142c26a00000021e051043a00000006c420800000006488d1099978043c0000000ffc23859a3db11c80000001340000ee4000441876c00000026200000007e2000053800029a0000b3400000001380000007d1000000000000000019a00000000038c04d1a000000147c9e26e83d380000008b031a800000000001000001a22a3480000111a79c1b0850c0000450001d9800000000003a80000000001884ab600011b0dec000000000000043854914000009da000123800000091922101405224b319d1cf90080000000000000000000202810079b3af0000c060000001a38f240000001d2842c8c52b918a022055d390800000002942b8000000000000218c000000000000000008e00009490ea8460000000d3c0000001cf400000000006d408e000000000000000043e000000000000000008800000000fac4e80002299f2019c00016b82704665aa000054c00000023e089c73200007322f000031b00009500006b5000000095600023e88600b80000001950000000000140016062336d93a4cd800006d8cf0328633000000000035700000000000000001e140003791979880000000000000095287f13d8d3850e0000250000000000000000000044946982510d85fa44395d10b400045515e51360003659db8cec000000083118000000000000007e30d513f4e6a2990019cc842600000023700000000000000044000000000000000000000040006c42c680011c200000014840000661998784056000000
  | 21 => 0x88000e8600013012b0c7800042999b883c00035a0000a6e4050001610000000000000000000000001200465662739968d8089d0170000bec72c00012740000000be1f9cdf03c0000000007880300000000001310000d791ea2df000000000000006c000000060d0001d740000002bb8d040007a810480011460600001a180000004340ea90f400000980008620000788c10000000000000000084e28817e400000000006e400000023b9a3c0000000001b1c0004f0053000019200000019744f400030983d01180000859d080000000000000fac1ce00000000005a43d6000000000015f23247488f01b7000000000000000000000001fd80010286b328281d8aa219545212989ec21b00010bcd080002d0800000000033c055c0006d000023280000002f289c4000000000000000000000000005e48a502c00000001a00001d58b8463d449800000000000000000000000002188a8e1500000000000000000000000000000000000008770001a6495e61b00000000003f105900000000002f31fb80000001fa8a8000044e3b58000b7e00000003b41420000000000a861e73be80011300000c100000005cd0001a9c77c00000000000000000000c600002c70000a8458439e38e000007e01127a9a680000000000d64000000000081c000000000134800067f184000000000000008ec47a4ad0001f3800020b0000000f16000228029c00058c00000003fc00000000002da49a0d894c00003090000000e8e00009d04ec21c0003110000ab28510000b54eaa00034800004326cf0000f080000002de02f400000000000000542ad0000a100000000001cec99a6970000e4c000000000000000000011f8000000000208800080e0000000000d5482c0001a30b020ae14297b445c1e2000031000000000000000005b5349803400046f154000000000000000000000003f9000000000031f00000000002f500008d800000019a400000000000011740004811e94000000000000000000000000000002634118000d460000c5a0e0000000000000000036700000008760000d58000eec56300000002e20001cd00000000000000000d3000000000f41b4876000077800000006b800000076525700007e00eb11aa1108500000000000e9e0000001a90000000000177c21e0000000c0c29a46612c00000000000001fb0dba37f38e83580000003ef0000642000000000000090f0001530ee600048300000000000000000e2e000000011849e1780001994d286253130e100004320ac18d87ae0000000e58d7200000004e51180002a69d0000000036b80000000000000000be282700014c80005c40000000a1e0000000000b4054a35b800000000000000000008ae2f40000d6000000000000003c600000006fc00000000000005dd0001bb8d6c8d838d1c4800
  | 22 => 0xac0000000e180000000490000ec854019c0000d4c0003e50000cf60004029318000005000185cfea3e000000004e686d000000007200000018fc00000032280008680000000000e2800042c000000000000000000007960cf8f2087a000055960800000000000000004211378fdc0ae2281109e50ff200016600000000001b280006860000000000f9a00033e800091800000600000000003e11fd0d1000033d0000218475000000107e00034d98b4c6e0000001a9400000029d0000000000000000000014800017303d414400000008a2000000000000003129f93ccb3000000013e80000000001b0c1ba00000001500000001fb198c0000000001c04e9200000000000005a22e900000000000001f187624940000f880000000000000b5000000000003120fc000000000039c183800000006b210112c74000008a000016c56c0001e782ec6fd0000c742d04cb0000000000193094000023c0002e08000a1869f000000002e0003df1f14ade0000b60cf904800000012280003060000f14000000000000000013200000000000001d580000740001a490643100001b200000000000000d705f816f42b09d4c5e00024d800000047a1628fa4aa80000000e3882e7dd0000c1400000000000000000d339f971c0000000df80005e20004328c0000000024e000000071e0f200000003ec000000000078a33a800094a25727e1d708d20000000000e068cf424981c0006341e180002440a500005acd1400000015201fc3373f2800000000000000007506744858b8c0004250001e7c0000000cea0c8f1011238100009001f93878eb40000000000000000000190128cc520002eda198000353000000124000000013fc0000003a5800038a2d10091bc8f4c00030c19840004560001db11388ac000000097a69500010ac000000069000000000000000000003e500000003920002e99aec00059c447057c000000000000000000000000000006b8000000000000022200000000000000000e4c3883298e9c0004290b49edcf340000f78000fe64c8000000000000017b1c20e8a6d90000000e2c5ba0000000fee5b20000444000917000000045674d158993898a55e079a454000000000000000000000000000000000000000000000021000000000000000009863cb000168c4cc20024980000000000000000978000000063c0000001bb8000000452000000101e1091119c380000000000000c3800000000000000003651b251ca83e00000000000000000000000000000000000045b000000000000035f80000006d404c88405fa0000fa00000005c8000109800000030f833051a0004008000e086c600000000001a700000000005e900000008860003f68a0cb524ef0000ee84b4000000000000000011780006b06b12d7000000000027c16f851c0002e
  | 23 => 0x9bc79d00000000007502371ecc03e000000000092c38f3a6000000000000000000000002b580ec0007c91a51d38000000000000000000000000000000880000370aea14a0cd84d122c83b16e93b0ece0000000b6491a24600000000000002dc8000f5e0000000930e8800000016749ca00000000003fa55c0001be49708fe01619780000002fe03a400000000000000000002d980000000000000d6cad23c700000000000000000000a883fa3ad80001d82fe19615886d0000032800111460c15a88804585ff1ea2104d500000000000000709406800000019100006a0000000000000101052b000000052c000000000054800000020ac0001792c58e041c25082869c9061a1a525a80011400b3000000041400000007fc90469c260832817e00000000000001d0000000121025c000199c0000000000000eee0000000000000000000000000000000003bc00085d00000000000000000c2c000433360865c00000021380000004f72b800000000000e985f435c5870208000000000198800000000000000000007db0000000ef44df00021e4ac26ad1b880000000000030000c5c44c00020d800055f00000005a068b2fb8e5c1aa7521a115e80de0000e400000000000002380000000000000000041c00000003467280f3000000000042f0f3c00000000004bc0008540770000000000000000000000000000000000002928000000000004237c000000000000062000019814b49ac00000000000007c4253900400052e2cb9abc1621cf22c0000000398000189c0004d900003e4000000068000000000000000000000000001254c704143261d7c5d800000000001584be000181893c00004e8000000000000228455c000000000081e00018b0000e741d41e080003d80000950000a4c32500000000005d6029000040c000000066400000000000010e87d200e09b0a1251c000131c00011a00000000003de16c14ec6f00002fc00004902761200000020738000000000000000000009504cc0002398000000000000000071300003e0878000000000000000000000000000000000000ca0000000000000080b000000000016a1c496980002c600000000008d00001034000000000010c0000002bf00000000002e5800054a00010b870c230000383a068b6800017a9f000000000ef8afc00090400000000005950000b9400000000000008460002d60000000000000213000000000000000008024789a0c000000000000000010a00008f800000024c000000000000000000000000000000c2000000000000001eb08e878000024e07d8b240000000000fbc0000cb00000000000002dc05fc000833000000000000000023dc0000000000000f20000000244c0000001b680000000000001f1c000658272018400000000000003a47bd0002368c
  | 24 => 0x5dc05a9df100e3d5000000013000044b24841080003bfa34800000046a00005a84e21129de40000004618000000000028800000075a00018b00001da16d00000001c42940dcc00005a11d2468daa20500000007dc00038c80000004ce08b19e4d5800000021bc5a47e40000000f0281300d95040b67cb00003c902e000000140800019221f80bc000000000000000044a000117518e81600000003420000fd95c400070c00000000000861b580000006ff0000000000000000000000000000010b8812190000000000000000019342044220000e289a827c000000000000000000002b25b123c8498000000000000117e00000000004da1ed0180000ad44030001cc45bc00000000000000001ef800000018c000012c00000033980000004380e893000007c100019480004ca00002e000000000003811ec08926e80000000e40000000770317000070000000000015489104a200000000005b700000000000001f68b208e88550de8000f9e614000214800000000000000004b1000025c00000000000002a4478293a3a000049200500010687b4000000000000042e22c8f2e461000141c00000000009f4000000000000000041547995f47663d940880000000000000000000000000000000000013c800000048e1939fc000000000000000000000000cac000641000000000023c3fe800000017300000002b84640000000000000476000105e00000000000003660d800000000001f21eb48260000001bd000000005100000001833c480000000000000ae81a80000001b9c000000000000000032a0001bcc00091c00000000000002550e84000000000000000000000000000001050000000eda83500010c00000001750638be000000000000007c300000000001f22e30000000000187000076e000000000000000000000000000003c000000000000898000b5a00037d875c00064f24792c80003e719fa2a42a822622a11140007fa0000000ce26f538aa3f479a47100005b853a02107108507e87e800000000001b20001030000000000000054e8fb00000d8246557000000081c00023514686be00008ba164000000000000062a0001b50000000000000238c0000000198fe00007b2000221800000000000009aa0000000794a0852f4268d4808000031d8000000000000000000000030100000000000000000b0a00000007711ce60500003147b68970000000a026590ab00000000000a080000000000001cb80000002d3a2540008b92eb91a000000004b0e3482000000000000004970000b3cd4400000000000000000000ae4000000000000030a4353758000ea26b200000010800001bb22640000002e199c0406000000054415e54f0000e54b061bc25f96000da0003a980000000000000000a8437d000000000081000000000001ad0
  | 25 => 0x53d3a402f839878d2988000bb015a29980000001b800000000000003088000dc600015300000300000000000a300000000000000000000000000000000000000006df341000005a00000016ec4a64003781cd861e46b0000000ec0455048000057a00020919c86d2806107120518c0000b320f400000000010dc5c40000000000f7e3913ed000000051b03e03000000140001f840002043c38000a52000000000000000010780000000000000000638000000000000000000000008be0000001b68000000000182cdc0000000000013e00000000000004bb00000005b613009f00000003f30000aec0008dd12480000000000678ed000000000002149b41c63ac00c916a1ac000122c0000000001cf0000000000013000000000000005d200000000000000004150000b0c0001de8000000000000000000000000000000000002fe8000fa60b4000164000015b423897400000019a00000000000000000ef000000000000006573b50000000000000000000000000000000000000000000000000000244038e08d194000000070b2920000af60000000000000000000000000000000001b00005340000000d02000000000003c0ad00000000000000000a28a3a76114a000044800013900000000a841280011e440600000000000003021b845803872688c8c0008f900000000ce00000000008583261f918c49fc00015e1e900320000000000a446d13220000000127000000000018009f8bc0000000120800000000031581f44aa1473d1800119a000000113400000000000000007713d114383ba00000000000e61700000000256000000000012200038880000004db00014440005651a3000000000000000012284a0000000000000037280002408a22ea22a07fa00000000002e40001a80ca490c4701ff000000000045c00003146ab1bd000068e7f103a153918200000000000000721220000ede7330001558000000000242511600003b820c0008ee0001a740007ff0001624000705383140cf320000000000ada000000000000000000000000009180380d8000000015580000007950b280000000003240b8400000000000000000000001ee000000000000000006ae0350000ff000013722404620001d78000f6000000006cc0000001a60490000564000000042a0002cb18291907204218eec00055804d9d888c000000000010600000000f4400005937e0ed8348815000000000035d00021a40001b70001df800059f0002184000000000000000000000000000000000000f406aa36300000000000002e280dc000000000000032c00000021f4000313000000000000047200000008840000fa80000000a784b892256e1810000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40141d93e1373594210050764c84dcd65084fb82c821d173594210060b208845cd650856d41d979cd4359421004872617350d650840181f985cd4359421006072617350d6508401c0f925cd43594215cf032497350d6508569c0f215cd43594215a7058857350d6508569c0d215cd43594215cf054857350d650840141d931d270594213ee0ba08749c1650840141d931d070594210050764e54dcd649400141d932177359250134872617354d649400181c985cd53592500058364f85d0e629403d24c9854d4398a5000583a615350e629413d60c9854d4398a5000619615711c5629400141d9315176906503ee0ba08545da419400141d93d5173d95405ae0761d5350f655000141d93a1173d954000507e4d845cf655004d21e98dcd43d954000607a637350f655000181d98dcd43d9540006072197350c655000141f97d8d43195403ed0ba5f65189425000141d9315076545400050764e85dd165c800181e8754d43597205af031c95350d65c80cd6249459551487205af035c95350f654800181e8754d435952000507a5d5350d64480092649859551485203358925165545214817132a98e1542501202168a21b8550940480fb92b872154250120004caa6375509404804dc2876dd542501202fcca26075509404808b32895613215012002c6a25d84485404808b3289561121501200050764e84dd5640800705c985cd535902000507a5d5350d640800181e8760c755902000607a5d831d5640800181e7260c7559020006071c9831d564080c981f7060c7559020106075c1831d56408001a0f2060c755902000686881831d56408001a0d2060c755902000686481831d5640800141d93e1773590200050764c85dcd64080fb82c821d573590200060b208855cd640816b41d979cd5359020004872617354d640800181f985cd5359020006072617354d6408001c0f925cd53590205bf032497354d6408167c0f205cd535902059f068817354d6408167c0d205cd53590205bf064817354d640800141d931d671590203ee0ba08759c5640800141d931d471590200050764e85dd165c400181e8754d43597100050764e84dd5648400141e9754d435921000607a1d5350d654400141e9754d435911000607e1784dcd624400141e9754d43589100050725d5350d624400181e8754d43589100060721d5350d62440034d0974c5305891000e3421d314c1624416741d979cd435941000706e417350d650416bc18905cd43594105ad0765e7354d6404001c17915cd53590105b7052457354d640416741d979d57458c105a705205755d16304001c1b905d57458c105af06241755d1630416bc17105d57458c105af06841755d1630416bc15105d57458c105a706441755d16304001c1575e057458c1059d836565350e620416760d9594d4358810
  | 1 => 0x3b05c0063000f8007d370ec54622b131486644a28723d002150c9127044b61f4406c6c701612c106b219c8ce0c4197536554c1ecfc73000ccd479002006e693d0ad2e3110234d88f2a0593242068c13a1509178a29e4f87804a8462685e404399088072e10450213412490062c0e1268b171d09a04000002800001648a65500641e90528f144a11f80c145a0e94816232997ce2050c001542527888c284008000034001bc009c0000000353a800ae0e00248127c4b2a400273c0000000531dd4600190e91c6d0d000005009928001c4a8b4fe0000001020041090004623898c00014a5000a70800004280c0c454818100c0400340c080cbc1014001070114c30f4007c040000bc9c000c00580c00000c0458046060001804003080100450142c0141d9395373592520062a60b709c3645480181e865cd5319152006072197354c645480190c825cd53191520050764f54dcd659080181e8754d435954200607a197350c655080181c865cd4319542006432097350c655080141f97d8d43195420050764e545cf645440141d93a1573d91511c487a637354f645440181e98dcd53d91513ed0ba57729cb64544018ab7260272d9151006072197354c645440141d93d5373596410050764f84dcd659040141d9321373596415b50765e7350d659047121c985cd435964100607e617350d659040181c985cd43596410058364f84d4e629046328c9854d4398a4100683e615350e629054fa0c9854d4398a410062a611701c1629040181e8754d43595410050764e84dd564c840141e9754d43593215a7031c95350d64c840181e8754d43595215a7035c95350f644840141e9754d4359121334c9a638454951484fb927872115254521004c9a637454951484f3324981d152545210050764e85dd1650840509c985cd435942100607a1d5350d650840181e8760c745942100607a5d831d1650840181e7260c7459421006071c9831d165084eb81f7160c74594211c6075c5831d16508401a0f2160c745942100685885831d16508401a0d2160c745942100685485831d16508
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x31649e40802200028652400008e6007266840008002000ae00520b42412e6a98c8a900280ca22197350c6550801484d0104b9a8632a847da0aa977260272d915100503541393063a2ca10802815a11c9831d16508577c02b8a42c18e8b284200e019c92160c745942100504b4241108b9aca1080300c922617350d6508401807413263a4e0b284200c03a099315176906503ee050ed4c6eaa128090002816a19c9831d5640800140cd00e4c18eab2040bae025c12060c7559020007014e4903063aac810002829a0208855cd640800180649130b9aa6b204000c03a09931d67159020
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x18b00102028000001004809b0288865cd4319542005802b09c92160c7459421005005b1248985cd4359421005005b1a09931d27059421005802b19c92060c7559020005009b0248985cd5359020005009b0a09931d67159020
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
  | 9 => 0x3
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124c
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138c
  | 17 => 0x138d
  | 18 => 0x138e
  | 19 => 0x8c
  | 20 => 0x8d
  | 21 => 0x8e
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128c
  | 26 => 0x128d
  | 27 => 0x128e
  | 28 => 0x150c
  | 29 => 0x150d
  | 30 => 0x150e
  | 31 => 0xa0c
  | 32 => 0xa0e
  | 33 => 0x130c
  | 34 => 0x130e
  | 35 => 0xa4c
  | 36 => 0xa4d
  | 37 => 0x134c
  | 38 => 0x134d
  | 39 => 0x20c
  | 40 => 0x20d
  | 41 => 0x20e
  | 42 => 0xb0c
  | 43 => 0xb0d
  | 44 => 0xb0e
  | 45 => 0x140c
  | 46 => 0x140d
  | 47 => 0x140e
  | 48 => 0x154c
  | 49 => 0x154d
  | 50 => 0x154e
  | 51 => 0xb8c
  | 52 => 0xb8e
  | 53 => 0x148c
  | 54 => 0x148e
  | 55 => 0xbcc
  | 56 => 0xbcd
  | 57 => 0x14cc
  | 58 => 0x14cd
  | 59 => 0xd0c
  | 60 => 0xd0e
  | 61 => 0x160c
  | 62 => 0x160e
  | 63 => 0xd4c
  | 64 => 0xd4d
  | 65 => 0x164c
  | 66 => 0x164d
  | 67 => 0x104c
  | 68 => 0xa0994
  | 69 => 0xa0996
  | 70 => 0x98a14
  | 71 => 0x130994
  | 72 => 0x130996
  | 73 => 0x99314
  | 74 => 0xb0994
  | 75 => 0x98b14
  | 76 => 0x154994
  | 77 => 0x99554
  | 78 => 0xd0994
  | 79 => 0x98d14
  | 80 => 0x160994
  | 81 => 0x99614
  | 82 => 0x160996
  | 83 => 0xa1294
  | 84 => 0x128a14
  | 85 => 0xa1296
  | 86 => 0xb1514
  | 87 => 0x150b14
  | 88 => 0xd1514
  | 89 => 0x150d14
  | 90 => 0xb8a14
  | 91 => 0xa0b94
  | 92 => 0xd0a14
  | 93 => 0xa0d14
  | 94 => 0x14d
  | 95 => 0x749
  | 96 => 0x198d
  | 97 => 0x1949
  | 98 => 0xbca54
  | 99 => 0xa4bd4
  | 100 => 0x180e
  | 101 => 0xbcb14
  | 102 => 0xbcb15
  | 103 => 0xb0bd4
  | 104 => 0x14cb14
  | 105 => 0x14cb15
  | 106 => 0xb14d4
  | 107 => 0xd4b14
  | 108 => 0xb0d54
  | 109 => 0x164b14
  | 110 => 0xb1654
  | 111 => 0x164b15
  | 112 => 0xbd414
  | 113 => 0x140bd4
  | 114 => 0xbd415
  | 115 => 0xd5554
  | 116 => 0x154d54
  | 117 => 0x19cd
  | 118 => 0xd4bd4
  | 119 => 0xbcd54
  | 120 => 0x28e
  | 121 => 0x74a
  | 122 => 0x184e
  | 123 => 0x1a8a
  | 124 => 0x44d
  | 125 => 0x74b
  | 126 => 0x1a0d
  | 127 => 0x194b
  | 128 => 0x40e
  | 129 => 0x188e
  | 130 => 0x1a8b
  | 131 => 0x18c9
  | 132 => 0xe89
  | 133 => 0x1a49
  | 134 => 0xec9
  | 135 => 0xe8a
  | 136 => 0x5854
  | 137 => 0x18ca
  | 138 => 0xeca
  | 139 => 0x5994
  | 140 => 0x1a4a
  | 141 => 0xe8e
  | 142 => 0x18ce
  | 143 => 0xecd
  | 144 => 0x1a4d
  | 145 => 0xecb
  | 146 => 0x1a4b
  | 147 => 0xe8b
  | 148 => 0x18cb
  | 149 => 0xd0a099c
  | 150 => 0xd098a1c
  | 151 => 0xa098d1c
  | 152 => 0xe8996
  | 153 => 0x18c996
  | 154 => 0xa1516
  | 155 => 0x151496
  | 156 => 0x155355
  | 157 => 0x29516
  | 158 => 0xe9516
  | 159 => 0x18d516
  | 160 => 0xd4bcb1c
  | 161 => 0xd4b0bdc
  | 162 => 0xbcb0d5c
  | 163 => 0xbd555
  | 164 => 0xecb15
  | 165 => 0x1a4b15
  | 166 => 0x15555
  | 167 => 0xed555
  | 168 => 0x1a5555
  | 169 => 0x44995
  | 170 => 0x154b15
  | 171 => 0x44b15
  | 172 => 0x45715
  | 173 => 0x150996
  | 174 => 0x40996
  | 175 => 0x40b16
  | 176 => 0x41716
  | 177 => 0x180a16
  | 178 => 0x19cbd5
  | 179 => 0xe8ed1
  | 180 => 0xece92
  | 181 => 0xece91
  | 182 => 0xe8ed2
  | 183 => 0xe8ed3
  | 184 => 0x98455
  | 185 => 0xece93
  | 186 => 0x98a16
  | 187 => 0xb0bd5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2239
  | 6 => 4855
  | 5 => 2338
  | 4 => 171
  | 3 => 20
  | 2 => 7
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 101)*7) 7
  | 7 => packedAt gbK7 (91795+((h/746+packedAt gbK7 (82843+(h % 746)*12) 12) % 2687)*13) 13
  | 6 => packedAt gbK6 (254074+((h/1618+packedAt gbK6 (233040+(h % 1618)*13) 13) % 7049)*14) 14
  | 5 => packedAt gbK5 (148069+((h/779+packedAt gbK5 (137942+(h % 779)*13) 13) % 4967)*13) 13
  | 4 => packedAt gbK4 (12426+((h/57+packedAt gbK4 (11970+(h % 57)*8) 8) % 206)*9) 9
  | 3 => packedAt gbK3 (1650+((h/6+packedAt gbK3 (1620+(h % 6)*5) 5) % 29)*6) 6
  | 2 => packedAt gbK2 (654+((h/2+packedAt gbK2 (644+(h % 2)*5) 5) % 17)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff878387fe0fc3c0703ffff281c1ff0e343f
  | 1 => 0x3e0ff803f83ffffc007fc0fff50e264633f8cf
  | 2 => 0x3ff0fffc003ff0ffff8000f809f03879c3cf0c
  | 3 => 0xc000ffffffc000ffffffff000e003f81fc0ff0
  | 4 => 0xffffffffff00000000000fffc001fff000
  | 5 => 0xffff000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4a5181a0824a89424110164aa080c09b061415
  | 1 => 0x150a1801081512a4022580954106224410e84a
  | 2 => 0x2768aaa40227a8ea970082e061b02869434d0c
  | 3 => 0x8000444a54800011284a28000e001500a802a0
  | 4 => 0x40f773e738cc020c030c418edb4001ffb000
  | 5 => 0x398c004044010020300c30860f6dbff6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36356
namespace PEqualNP.Outside.L_meta_36356
open PEqualNP.Outside.L_meta_36356.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 2 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 6 := bs1_4_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 11 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 9 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bgb_2_0 : Interval gbAtlas 2 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 7 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 20 := bgb_3_0
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
theorem bgb_4_160 : Interval gbAtlas 4 160 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 171 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_2336 : Interval gbAtlas 5 2336 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2338 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))))) (concat (concat (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))))) (concat (concat (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856)) (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)))) (concat (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)))))))
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
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3776 : Interval gbAtlas 6 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3808 : Interval gbAtlas 6 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4855 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)))) (concat (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)))))) (concat (concat (concat (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))))) (concat (concat (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))))))) (concat (concat (concat (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)))) (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))))) (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)))) (concat (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456))) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)))))) (concat (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)))) (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224))))) (concat (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 bgb_6_4352)) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)))) (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832))))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2239 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344))) (concat (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920)))) (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 bgb_7_2048)) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88fefefea8fec8fe88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36356.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[0,4]⟩,⟨.or,[2,4]⟩,⟨.and,[5,8]⟩,⟨.or,[3,9]⟩,⟨.or,[1,10]⟩,⟨.or,[3,7]⟩,⟨.and,[1,10]⟩,⟨.or,[6,13]⟩,⟨.and,[11,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36356

open PEqualNP.Outside.L_meta_36356 in
theorem PEqualNP.Outside.L_meta_36356 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
