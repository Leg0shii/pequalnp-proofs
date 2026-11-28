import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36196.Model
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


end PEqualNP.Outside.L_meta_36196.Model

namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
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

def SBf (j : Nat) : Nat := [4, 7, 6, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36196

namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
def s0K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (5+((h/1+packedAt s0K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 30 s0Pos s0Neg, 0xfcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36196
namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x31e0119b589941c5274f0028800180e40b01005c10c246559f0038480442c02500200041a8400a0c9cd2a0a5521100b49851000131c01811c2046100ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x114c40080000038c9045c9c011d5928d00059442850c13c8c9400b800000001880010004000000001013000a0003c906c49202c002174f40000cc000074012c00a49801788568b1803118d40000000000006400ecdc016c690c004c78bce4001d54fc1800540000f8016400007d3400b40c0000010804254c01840844ad7d49400001115000615c000170000124007000a8e0f13960d8880014e83400000004002a000400000c060000040a00020008120600020604000c141000060400057b5050ef0a0a1d794e42aea9c857a5090af2a1215794c42aea98855e50ccabaa71973d4932ae282655e530cabea6a0d714d41b7a92836c52506f6a0a0de14141af298835d53106dca598db54b319f2a0633d540c6bca790d754f21e6994433e540867aa810d794c21aea9843cd32086f4a010de54021af29e815d53d033e6520674ca409f284815f53502b8a6a067cc840ce990813e5010374a0204f953309eaa661b840cc2baa5185794230cf204619c408c27ea8984f15130b7290616d520c37080187394830aea9061cd520c29aa4185794030ed28061db400c33c80186710030ec2006198400c27ca9904f55320af29e415d53c839a659057d4e20ae29c41b8408827ea8904f15120afa9a415c534839a64905dd4520ba28a41b840482bca6105754c209f2a6213d54c42bca7885754f10dc206213f5444278a88857d4d10ae29a216f52442d8a4886e10010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1e00001400040031600001802420408670aa2000001a00e98089204108600002386055031d24c95008698604c840ca548400c34952d0030c354a400c29a6090030c3548400c3495210030e2948400c3195210030e2548400c3095210030c614c408824c654c920d14c851483185310120e24c8404833051101209358a53c431a5310310
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x40080508754c84048380990a220241425ca5310310
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (826+((h/15+packedAt s1K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s1K4 (2937+((h/33+packedAt s1K4 (2673+(h % 33)*8) 8) % 157)*8) 8
  | 3 => packedAt s1K3 (840+((h/7+packedAt s1K3 (798+(h % 7)*6) 6) % 36)*6) 6
  | 2 => packedAt s1K2 (150+((h/1+packedAt s1K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xe03ffff01fff0383fffff83fff03fe00fcfe7c
  | 2 => 0xffc0fffffffffffc0fc0ffc1ffffffff231fff
  | 3 => 0xffff03ffe07ffffff000fffe1ffc1fffc3e38f
  | 4 => 0x3ffff8003ffffff00001fffe003fc03f0
  | 5 => 0xfffffc00000003ffffffffffe0000003fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x29861811c5121480b2c5380a272132184c6e3c
  | 2 => 0x429221224824411405504a41494644a92114d5
  | 3 => 0x85084a44834892a9502494ac12a91952c2a30a
  | 4 => 0x162cb389120edbce69b606291cf39063f403e0
  | 5 => 0x1830c30e1c70e3738e38e73180c20183bbd800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0f0a0f000faaafaa0f0a0f000faaafaa0f0a0f000faaafaa0f0a0f000faaafaa0f0a0f000faaafaa0f0a0f000faaafaa0f0a0f000faaafaa0f0a0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36196
namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x3a560004ca0200511064003ef42ec42ee32ed32bf41bd41ef21ed21be40bc40ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6420962a26538505069aa790d354c20
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffe07f03fff07fe0ffffff03c0ffe67fe4f
  | 1 => 0xf81ffffffffffff81ff07c0fffffffff988fff
  | 3 => 0xffe07ff8003f07ffe0007ff0ffc00f81e0f38c
  | 4 => 0x7fffffc007ffffff8000fffff001ff03f0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x48850231214a210166029451522444b4233645
  | 1 => 0x12422442441082280890290a2449294888889a
  | 3 => 0x614b6890eda4af5aa18a4f68bea0ae0de0d38c
  | 4 => 0x4594512489063594d32b0240cb32c411750360
  | 5 => 0x861861c70e38c6e71dcc738c0c030861deec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36196
namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x2516440000000aa800282190a800260e0c4212424d000000f23524c7013000000007c3001850ba21e9cb1b00715003a0868048ac8000000004050300b141102043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x881bf311037c62206f4c440de18881bf211037c42206f48440de10881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf29661ee52cc2dca5985f54b30f6a96616d52cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461df328c3ba65185f94630bea8c61bf418c37a8318778c630ee18c617e508c37c81186f10230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea9061df320c3ba64185f94430bea8861bf410c37a8218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ee32883da65105f94620bea8c41bf418837a83107b88620f610c417e508837c81106f10220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53482fea2905f14520dfa0a41bd41483de42907b48520df20241bc40483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ee32083da64105f94420bea8841bf410837a82107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c437c81886f10310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21bf418437a83085f94210df20421bc40843f461087e4c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd414437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7be6498f74c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f719243ed324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40bf296817d52d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539037aa7206f14e40dfa9481be529037aa5206f14a40df99481be329037a65206f0ca40dfa8c81be519037aa3204f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a05f14d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206fd0c40df21881bd431037886205f94840bea9081bf421037c84206f50840de210817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28
  | 2 => 0x250000000000020160000380c000010010010040040000000a00001002004018088110020000000400801c000000040000080000800c00005006040070000000040200301e0000100000e0140001a0000080000301600000000000000040000060240000602200000003004008000020100140200000001c0000100201802801000008068060020000400d0020040500300e0080000d00c00002005008000008060000080080000601c00000000004010030000080500000000c0080200202c00801002000020000000040080100e0000180500001800000000008030000040280100100202c020010080000380000000c0000000c000000070000140100400002c0000001001c02808000000040000080040000600a0180180d006000028010000180380303e0000000200e008018000000140080000a0080300100c010010040000000000500400c03801000000010130000200100000c0000180300200403807000004000030020040a805000004015f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca41977cc832f719065dd320cbda6419734c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83b
  | 3 => 0xaf0003c4000000008a4000004b6000a0a750000012ba611740004d163000000328f02b85797325d58ea6032000374c5c0020254a50c9126d0d6b04c4800000328b22cb348be1129f22ee3bc439fa0001a4b788b24a001441dc5185fd1001d28e46039123514138de0001c02288d81047e001210006128d046a6b4946c18f2d6000000df0cd00009937aaa5a826c0020b46aba800000000000002ad58a9055f00000041ce482e1d0000229243720009598a000000f500000003c00000276000000000003900019920623c571ed0009300018e0dca4c5894e17c8915b0c516ac005b2e8464bf841092000000d382730a0000000009e97c00000000b5c3b2d93a29592231527a93cca8df31e485700fc1a89ec002680000007d8003000017800000034c00000000b54b60005288e58d13c1e40000208433600000000000000002400007203894d20a5f0968dd53e738000335f4000000002101080000000000000000000001130002c03e158000000668a79b30322dce78000cc0002f931000000000000000012d2c90007fcef9f0394000000960569980000042cb6000000000b6c000000000001fb0400000051310000000000000000000000003e00000000564000b9000208a04b6914110000519fe000a1c4e26a150a65021c10ee201240e33d226405b0a1ae688208001cc2bcd299725ca6868b056283fc2887c000c2052aed26e71800111426000b820e5d61e508800000000281bd0000dc000006402a51e94423a000000000001fce92460008a80007d5f64cc5f8ad0008f0f3a372f400186a6c4a454d482912c2204000001560000027f000b3d5a04a386000002b1000700001d455ebfd73800000000002ef2f00018301527e78809956000678fc000000aa17a12c0004416900003862c0000038e24c800d800000000000000a24a12cc0007e53c8f551a000000000000012e06a17267400000000a0103800418000000005b8c38c10000009547580000059400000000000002a24120005e000000000f990f19e91400000638a54ec000398000c18b24e07911b03d0003d00000000000000000626000000170c276c000590028497a800000c0400112000170000002e2000eaa230c40003d21f40a0b4001d30345612595f572000532470e65284c0006180015c00000000000046000418000001bc0000015a4c68047517d00000000000000c7400000238641271505bec0c001f111200000116000a3cc9217254045078281820d4ac83c160c593a09400030cc080013e8780000001ca2c4a8001ca0008c800406000002540000014dafc1ce4313e8432986d400000632000a92430142a8e20000007ed502f3058000000e91068ec1916702468d78a674e41f893af60005ac000003e82180000023e8f8760000000015aad0000000da188140699539c2
  | 4 => 0x1fc272000980004100004f1620000006e0530000012c83406c384180fa0a8000b7000622c6c00145000000f58fd00000004800456354000004747153e22c000ae8000005588b8111ee0008bd720d9202a14002273420149c0003225a400286460c3c000000480010c1870acaf418a600007400009100e000f199608e2f4bd80011cb10ab9154b0000f621c2a8000000000000000030239a001548001e6078000005f2a98a5800000000f78003b4000930000000002c23800044c000000004780020d19200129a9700018ca300000000000140000bdc002cd36e3dd420001a03d8eb85e18086910a334a0b19399094f49f90a80013a9e0858002b61b400000198800000001204f82d99400000010800168000000002d4000000002e600000000000b680019300000000000000c600000051cbc9142e5000000000c8000148632bb18e48132249000610ce18d07c001328005385547f0c41ac285640d2548b4c0006c370000001aa000000000000367654eafd0001c0f080026c9dc1d1ad1c4130002e93d01101c04b4bc3b4fb22d4dc2b0000005a2afd310253eac7cd59d601a5a000000000434d4aa309aadc000000000005205535c6b000000268b8c9793236ca0cae8000008283c2bc566524000000006ec0000049a100bf000000000001f70182140b2e1030889288c25940009d000462000002c32045d40029237eb746d09700066176039076000ba0000000000000014e00177000000000000080ce36c8b87b00000141000000000002de000864000003cc3b88d1a05800000002f000000001fd4206c8000480000014b0002a200000000006000000000005d800000000000000000000805c00055615c5d800290001570144d2c2d38800000000000000b486cf29b1624000e58cb33e4a42e8000d0c1c00000000001610002cc000598000463e400000052000870000e87757104900001800179118a7800000054428ef060000000672060ea1bd0eace000780002a1004618d418c4ec8509a9
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6404823e65101209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948209b59632082e9608c820d314d320823e64944208f59251083365150420cd54541082b860504209b59621082cd6308420ba58021082cd63c80209bd9520083a840480209ed95200823e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6414b108f59052c425e6314b109758c52c433561d5210ce98354843356115210ce980548423e6494e108f592538426e6294e109b58a538423f6454e108f191538423e6494a108f592528425e6394a109758e528423f6454a108f19152842ba60d0610ae18141842b56190210ad584408423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443596014d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414423e6590110c7d4e404431c5390110cbd4a404432c52901108f994404431f5310110c714c404432f5210110cb1484044358538c1109e195304436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad58440042796584010d654e100436952840109dd9510043b240440109ed9510043595344010da54910043b14144010
  | 1 => 0x23d650c640ab98831902ad620c640ae98031902b9600c6408f996219023d65886408f994219023d6508640a798c219029d6308640ae98021902b960086408f99741503375150540c754c43102ae6210c40ab588431029e6310840a758c421032d5210840cd547411023d65904408fd95401027b6550040ae983531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d4840a798c521029d6314840cb54852102b66114840ad58452102ba6014840ae98332102b960cc840ae98232102b9608c8408fd95321023c654c8408f994321023d650c840e34c832102ba60d4440a798c511029d6314440ab98851102ad6214440ae980511023e658c4408f5963110335518c440cd54531102bb604c440ae181311023e650c4408f59431102ae620c440ab58831102ba600c440ae580311023e65884408f59621103355188440cd54521102bb6048440ae181211023e65084408f594211029e6308440a758c21102ba6008440ae580211033a60940409b98b54cc26d62d53308f58654cc23f61553309b98854cc26d6215330cb95252cc32d5494b30cb95152cc32d5454b308f99251cc23d64947308fd9741cc23d65d0730cb94b41cc32d52d07308fd9541cc23d6550730cb94941cc32d5250730ae18141cc34d52cc730d354931cc32e5290330cb54a40cc32e5210330cb54840cc26e62d52309b58b548c23e6494a308f592528c34e524ca308f992518c23d6494630b3588318c2d9600c630b358b308c23d61d51308f992544c23e65151308f584544c23e64145308f590514c26e62145309b588514c23e65d05308f197414c23e65505308f195414c25e65cc5308f996404c23e65101309b988540c26d62150309d984540c27561150308f992530c23d6494c308fd91520c23c6454830b6583320c23e64944308f592510c3365150430cd545410c2b8605043097596310c2cd620c430b6580310c2cd62cc03097d95300c398404c0309ed95300c25e63d53209758f54c823d61953208fd8554c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c831e5454f20c755153c823e6414f208f59053c823e64947208f59251c823f65d07208f59741c831e53d0720c754f41c823f65507208f59541c831e5350720c754d41c82b86050720d354f21c834d5348720c794e40c831d5390320c794c40c831d53103209798f548825d63d52208f993538823d64d4e208f992538823d6494e20d394d328823e64946208f59251882cd6308620ba58021882cd63c82208f587544823e64951208f994544823d61151208f992534823d6494d209b58a534823f6454d208f19153482776154d209d185534823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f195414826e65c85208f99
  | 2 => 0x52149418fd95325063c654c9418f994325063d650c941e34c8325069f6354141a718d50506af6254141ab189505063f65504419dd95411073654504419b98854cc66d62153318fd9152cc63c6454b318fd9150cc63c64543318f982548c63c60552318fd91508c63c64542319bd89508c66c62542319bd89544c66c62551319ed81544c67860551318f990524c63d6414931d3149324c63e64d41318f593504c66e62d50319b58b540c67a60d50319e583540c63d65950318f982540c63c60550318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc43197d95310c74d524c4319dd95310c73a5494031ce552500c76a5294031da54a500c73b6494031ce192500c73b4194031ce506500c63f64540318f191500c73a5454031ce551500c76a5254031da549500c73b6454031ce191500c73b4154031ce505500c75b3154031d64c5500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c874c534cb218fd9150c863c64543218f982548863c60552218f993538863d64d4e218f990538863d6414e219e98053886796014e218fd91508863c645422197d8d508865c635422197d8d544865c63551219ed81544867860551218fd91534863c6454d219ed8153486786054d218f990534863d6414d219b195324874c534c9218f993504863d64d41219798f540865d63d50219e983540867960d50218f596540863e60950218f181540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c84219bd95210874d53484219dd95210873a5494021ce552500875a5394021d654e500873b6494021ce192500873b4194021ce506500863f64540218f191500873a5454021ce551500875a5354021d654d500873b6454021ce191500873b4154021ce505500876b2154021da485500873551d07409b98a539026d6294e40c794d43902ae6210e40ab588439025e6394a409758e529032e5250a40a798c429029d6310a40cd54541902ae62d4e40ab58b53902ba60d4e40c7d4e53902ae6294e40ab58a53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f594329038d320ca40ae983519029e6314640a758c51902ae6214640ab58851902ba60146408f996319023d658c6408f994319
  | 3 => 0x18b304bac0019c0005a83baff4ce0014a0fe2320000014a2e2514c680000301400402803002004000000020100000302401c0080001e000048000060300080000a00800800028008008040020000180000205c00000000004008060000000200f0000000000401200c00004002000008000060900080700600000804018000018010040040000000400800804000000000030000000080000c014008010080000580501a00408800004000008080060000200700600000804014010028010000080000301200007005002000018050040080000a000024008020000000080301001804002000008038010120040380201001c0000200000401000000010010000100000000200001c018000020040300000e00000002004014000070000040180200000001003002000010010020000081b0080080000001c000028020000040000100000001800000018010000080100000100800000012000000028010020140a803002004000020000300000201605002008000008000010000000000500000a3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210ead6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7a60d53329e58354cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3e64946328f592518ca3f64542328f191508ca3d61d51328f983544ca3e64951328f994544cb1d6315132cb588544ca3d61151328f980544cb1c5490d3297195434cacc6250d32cb152424cb8e43909329b195424cacc6350932e350d424ca3e64145328f590514ca7a60145329e580514ca3e64d41328f593504ca3d65950328f586540ca3e60950328fd85540ca3c60550328f990540ca5e63150329b988540cb1d54cc832cb552320cacd638c83297d95320cb1d544c8329bd95320cb2d544c832b3d95320cb4f654c832e3d91320cb8c644c832d3d51320cb8e544c832d3551320cb8d544c832c3551320ca3e64944328f592510cb4d3254432d34ca500ca3f64540328f191500cb1d5310f41ab98843d06ad6210f41a798c42d069d6310b41cb54842d06b561d4f41c754c53d06ae6214f41ab58853d06b56114f41ad58752d069e6314b41a758c52d072d5214b41ad58452d063f654cb418f19532d063e650cb418f59432d078d320cb41a798f50d069d63d4341ab98b50d06ad62d43419b988535066d6214d41c714d43506ae6210d41ab588435065e63149419758c525072c5250941a798c425069d6310941ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506ae6214d41ab58853506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d
  | 4 => 0xdc0000c39a020050005082900000005a1a8002ea146bed0400000000090a2a0007b800000334000000005204043c24610a0000000018400147000000000000005b46bd2c000000ac90811b5f0988d62503d0838002f639400000211000b6c001923aa000a49f70000005082f000348680000467d4e180023c4cc00000052a543885d00019034a2d5ee19824800114581350570b490000281000908c39ab3a6000bc80d0004dcb38000000001700038a3f0602dc0000007619536a000000000004c5251a913c544582651721f8df93c290a24882e72ba0ac1e0000000000028d0000015230b2ae981680a637aacd57000306428dc8943d6001692e015a3957a08f2307b155ad61aa2a53d8000003b8ba0541e87ed140d90545091728f000000f800014a000ce9c808c83c4c0000000000009f2004d8002832fa764000001c6aec000000003113c800000128bb21530c3d4001441123bc798000000007005b0ce30400217000000000e60007057d0f70000f8cfabd37439c002cb0003e91c8000d600109081000a180028b432000001030741d4a58003f01d9380360447510ea295fc368db8b100024183a05604c10c40ce4ba9486bac90005c00015900013ccf30c3c69a400000000710918c71a2910889cf45620c501cc5246f15b21e3487f11e2343e43c000000138970ff8961c86d8002e900094c000000007d80b1a82b40000009300077c000bc000000000004b25c90694f0000cd5a000000000922a3600000630005786c92a94e0000492d01d33236d5292b0000011c0210005480014c00000166194302a5d04ac4532bb80021308e89c381aa0009bc001a05802f80012c21c64000000416000e39c200056d80aac0009b84617f0003a584247538000002761908c0492aa0009512686f3d20000000052222c6581e49204c0e011440360f8a315e6000c889d00c01c6f221000350890000dc000740000000000015f000504000000001d11a8004067743180000a9e8002d300080560ae515418162a4125e05512ab54e89153e9850000e05900051400000000000958b20501a6000000000da000000000003e5368002c20010a000534bf0a68790000008698f000c144a800194a6c4697a00070176834518a9c122730d01705781403e000000971360816305e0fa269240000000014020000000000053000b1c001e741897c000000000005b8003c0000000001ec45d0316c00000000000000860ba800000458290000000000007c00082800000000000189063123340028508029c000000005889f8004ee00092920486810309b05e209800263000000002f22e60c0bc2c3132ae05d9d1000000002880006b8000dc0000007f9b14feb3c6f9385ea000000000f6bb0000000000011d000000000261d80000000011f254000911cb16c194cc0003d4000
  | 5 => 0x4e2498002980584241e9080007bc75af93a043c0708847a108bd839000638752ef28093d819ce4d69d498107186749289ad572a5842025000b64410ae0004b8000a23420000000000006c000000009c8b78004980000c165000000002870005f9831b3614b98bb8000e6000000005040001a800444b28000000883891ba072b88ed119bb0b00005591a15800062855064b5c00ade00000800041000000b70004c8b840000007e44c2c8003ae000240b3000001611b44043b40000000000000000434000000175900651f946000000002b1020554fead50084711f0b500000000000370000000000e4a995684327c000000005ba658d30911c2000000004bc0013e1802185797180000033000000000200000000004ecd393a0007d01d9db000b7cfc837000784790b42ac0002f8ba44cc24002d1000998c987f0002a0002fd0000006e8030002180017c268024002b0000aa16c0000000014f9d609a770312e427a1580d000000000001a5000000f99661ac000f12a9526a84e4800000410000001f600000135000688001da204000000f8000000000002d600047000096000361be00042c0000030800000000000bc00004e496000001140004e55f80059a798c60000000000000000000136000000001342781e2000b192d3364a014000000000000bf0007940029d4660016711d00021c00153000000c5158264000e30005c4000000bd19eb5000000000000000004ae790d18000000015d0000000009480000000117a1c000000002be00087c00000016000002165d0000000000000000027e55e7f80000001e000139154b6000002324368d8b680000098400000000778000003da0007e954540414000000f47e91616932e001271430000014f00019200000224000000938b80a2540b42a200051c00045000a
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x281200180200188e565182500d051d101892608640966454fb7301570d6ca4d2d2e011000080f0004b0e354ea87804200013461cd9116919af0000606041404280080818f00042001000106c1ac6b10a89950d75951320ca873b2a899065431d9544c832a1ee2aa2641950c70551320cb06a9ac421e838358d5210b41c1aa6b10a7a0e0d6354852d0706b2a6419683435c85350d41a1ae629284a0d0c7254c535068c382a629a838354d6214d41a18e6a90a4a0e0d635485250694382a4292830e1c1650c941a18ea99064a0e0d654c83250686ba0a499263435d0534cb21a1ae829a6490d0d7294d4390286b9ca4a1481439cb5394e40c1ea6b14a72050e73d4a5290306b1ea52948143dd5320ca40c1cca990652060d535884310306b1aa4210818354d6214c40c2aa6b08a62060d635485210312a92c2290810d5c4654c840c1aca9906420631511813110318a88c0908818a9486050730a1ae9292651861a5318141c8286ba4a699441435d0534c820a8ae229a641063161980548430c298c0a0a218a1486050510c2aa6b088008625525844004388a9a8288021c85494144010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x92801a00490a809d9544c832a088054d6214d41c09631c1521494180c87595320c941a0880595320c94180e87995320ca40
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 5 => packedAt s3K5 (24564+((h/267+packedAt s3K5 (21627+(h % 267)*11) 11) % 1279)*11) 11
  | 4 => packedAt s3K4 (32538+((h/260+packedAt s3K4 (29678+(h % 260)*11) 11) % 1247)*11) 11
  | 3 => packedAt s3K3 (2870+((h/18+packedAt s3K3 (2744+(h % 18)*7) 7) % 68)*7) 7
  | 2 => packedAt s3K2 (366+((h/2+packedAt s3K2 (360+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe0fffe07fe1f8787fe1fe1ff87f0707d39f793
  | 1 => 0xff07fff87ffffff81fe1fe1ff87ffffec638ff
  | 2 => 0xfff83fff801ff8ffe001ffe3ff807f8307cf1c
  | 4 => 0x3fffffe000fffffe0003ffff8003f80fe0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2a11823114250801660260258091113818d391
  | 1 => 0x40400440200800100820820808242440422026
  | 2 => 0x8622a8920d5241aaa1113542d5024b0b054d18
  | 4 => 0x14b53124490352ccd3541103664b0213a80ec0
  | 5 => 0x18c621c7719c64f71d99d990440c0c63f7b000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8ececc8c8eeeee8e8ececc8c8eeeee8e8ececc8c8eeeee8e8ececc8c8eeeee8e8ececc8c8eeeee8e8ececc8c8eeeee8e8ececc8c8eeeee8e8ececc8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36196
namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x80058000074e3000d2a00416265c000440030f042c1a5121131d507050e3679523527cd195a14920300520000840145600880000000501e148000042000824540ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb81e6410946e82002aae20007c9c32723c587a005052008046b4560a8c2c000002961274b07042b26800224c08a66c169060360c34a2624eaa78182600a80e9a8886b648405aba1a006600be005e389e6a3a5c548a98c2a40024c0007e8e4a3ec476bca084002e040600003028001cac44921412301890a0840f0a34203020000300282030a19a80160891200613851b765110eeaa221de94242bca84855f5350ab8a6a14fd51329e2a2653e540ca7aa8195d94432baa88657a500caf2a0194f943419eaa4835e53906baa720ded4141bc28283b75150776a0a0cf14141dc2828338505067ca820d794c41aea98839f41cc73a8398cf952319eaa4635d538c76a8318ed50531eba8a639f414c7ac8298e750531eaa0a6395414c67ca818cf55031af298633e548867aa910d794e21aea9c43d531887aa6290cf950219eaa0435e53086baa610de94021bca80433d519033e6320674c6409f284813d511033e6220674c4409f28081ba501027ca9984f55330bb28e617551cc27ea8984f151309f2a6413d54c837081104fd51209e2a2415f53482b8a6905dd4520ba28a41b8404827ca9884f55310af29e215d53c437081884fd52109e2a421d5318427ea8884f151109f2a0213d54042bca6085754c10b7290216d52043aa62086e10010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x104862c02000024400c01054ca3093ce34701400100101e40406556114d42a618141cc6b06050631ac181414c6956490531a6181414c6d06050531e4d81414c6946050531e4181414c69060505318e1815488715544c621c554531103305110120c5d513184315544c410d154931042396510010ca54840043913110010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x10040510705513188708b2a6220021c05493110010
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
  | 3 => packedAt s4K3 (833+((h/7+packedAt s4K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s4K2 (150+((h/1+packedAt s4K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7fff03e1ffc3e1f0fff87fe1c0fe0fc79f673
  | 1 => 0xf87fffc01fffffe00f87f8ffe00ffffe46387f
  | 2 => 0xff81ffffe0ffc3fff007ff0ffff0ff0387cf9c
  | 3 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x510c118826284007028981160461225818d631
  | 1 => 0x2211220548522260854248a9208a4ca2422846
  | 2 => 0x10244490028004891004920249209208854298
  | 3 => 0xa5598925101aab32a9d0408d92cc0433680d60
  | 5 => 0xc6610e399ce333dcce6764c1030818c3f7b000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfae8fae8f8c8f8c8fae8fae8f8c8f8c8fae8fae8f8c8f8c8fae8fae8f8c8f8c8fae8fae8f8c8f8c8fae8fae8f8c8f8c8fae8fae8f8c8f8c8fae8fae8f8c8f8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36196
namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xea05100094b832a5008d226859604a500442a93000c9c000003c012380041356602a332300001274f243e0071b4400a1082075cb214042080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x24a98017888f0780159b9f98002723000a0a868019001692a12180072c931611801a891b22800f8c1e80010324292d029509ab1c000018800008001c800e19820525000000002aa5800591100000049d8c939497142801a7920000000b000003ac1f20042a0d8ba61e2ba3ad9d062680108000008e9a22208d28808022042130004885020c78d0e0c08b001800400000000c64a06bd28087795010ebca7a15754f42bd286857950d0af4a1215e54242afa9a855c5350abca51957546329f2a0653d540caeca2195d54432bd2806579500cb3ca8196755032af29065ce520cbaca2195754432eaa886555510cbb4a0197654032af29c835d53906f6a0a0de14141af298835d53106dca420db54841bd2808379501067ca998cf55331bd286637950cc73ca998e755331af29663da50cc7b2a198d754e31ae29263d7514c6bca618d7d4f21ae29e435e53886baa710f54c6219faa2433c54486bea690d714d21ea98a437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53102baa6206e500409f2a0613d540c27ca9904f553209f2a4413d54882bca7105754e20afa9a415c53482bca7885754f109faa2213c544427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2060a04c8e00002c5951510cb155454432d4546500cb195454032d4545500cb1954543319519531487195350040
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt s5K3 (312+((h/2+packedAt s5K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc1ff0f83e1ff1f1f0f0e3fc1c781fc3f23c673
  | 1 => 0xfe3ffffc01ffffe00fffc3fff801fffe3c787f
  | 2 => 0xffc00ffffe1fe1fff00ffc01fffe1fc1c78f9c
  | 3 => 0xfffffe001fffff00001ffffe001f80fe0
  | 4 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x5486989892ca310785862648c48d24ad21c631
  | 1 => 0x88080100440400200210408508104910081846
  | 2 => 0x412222900500249100a881051241284468298
  | 3 => 0x29accc52510655b2aba02225a6598119b80d60
  | 4 => 0x31308863999899dccccd333804610221f76000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8fcecf8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36196
namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x91e1500001b8600000c9f8418991b0a13048700981a868d098b1f1603000000138c12800000158e839d0a800000001181800d978594971a1c8e001c00051400000000079e8019a02080108b8002800200000010121d9100000f01088000000f8016800000000800000701021c0000008005002840000080140024200027fd5007fe54007f55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc43027fd4801fe52007f54809fc5201ffd0801fe42007f50807fc42017fcc805fe32017f4c805fc32027fd44017f5100ff94401fd51005f54403fc5101ffd0403fe41007f50403fc41017fcc405df3100ff8c405fd3100774c403fc31007fc8403fe21007f48403fc21027fd4001fe50005f94001fd50027f140017c5001ffd0001fe40007f50007fc40017fcc005fe30017f4c005fc30007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2c20009fd961005ffccb08012fe6584001feb2c2000bf5961005ff8cb08012fc6584001be32c20049f19610007fec908002ff6484015ff3242003bf99210007fac908002fd6484015fe3242003bf1921005ffea90802bfe5484001feaa4200aff1521004ffec708026ff6384013ff31c2002bf98e1004ffac708026fd6384013fe31c2002bf18e1004ffea708027fe5384013fea9c2009ff14e1004ffe8708027fe4384013fea1c2009ff10e10007fec508002ff6284001ff3142008bf98a10007fac508002fd6284001fe3142008bf18a1005ffea508003fe5284001fea94200bff14a10057fe8508003fe4284001fea14200aff10a1004ffe6508027fe3284013fe9942009ff0ca1000dfac308007ff5184003bfa8c2001ff9461000ffaa3080077d5184003fe28c2001ffd061000ffc8308007fd4184003fe20c2001ffcc61000fbe6308007fe3184003fe98c2001f74c61000ff86308007ff2184003ff10c2001ff4861000ff84308006fe6084017ffa842000ff94210006fca108003fd5084017fe2842000df14210057fe8108003fe4084001fd2042000ff50210007f2810802bfc4084013ff9842009ff8c21004ffa6108027fc3084001ff9042000ff88210007f44108003fd2084001fc9042000ff0821000ffe2108007f71084003fd8842001ff0421000ff02108003ff65440017fb2a2000dfd9510004feca8801ffe65440097f32a2000ff59510005faca8801ffc65440097e32a2000df19510024f8ca88003ff64440017fb222000efd91100057ec88801bfe64440077f3222000ff59110005fac88801bfc64440077e3222000ef1911001d78c88801fff544400dff2a22000ff55110037f8a888017ff634400b7fb1a2005ff98d10015fcc688017fd634400b7eb1a2005ff18d10015f8c688017ff534400bff29a2005ff54d1002ff8a688017ff434400bff21a2005ff50d1002ff88688003ff62440017fb122000ff98910045fcc488003fd62440017eb122000ff18910045f8c48801fff5244001ff2922000ff5491003ff8a48801bff4244001ff2122000ff50910037f88488017ff324400bff1922005ff4c91002ff86488006ff6144003ffa8a2001dfd451000ffca288007fd5144003bea8a2001ff1451000ffe8288007fe4144003fea0a2001ff1051000ffe6288007df3144003ff18a2001ff4c51000fba6288007fc3144003ff90a2001ff8851000ffa4288007fc21440037fb022007ffd4110007fca0880037e5044001fea822007ff14110006f8a08801bff4044001ff2022000fe90110007fa8088003f9404400dfe2022005ffcc11002ffc6088017fd304400bfe1822000ffc8110007fc4088003fa2044001fe9022000fe48110007f84088007ff1044003fd8822001ff84110007ec2088007fc1044003fa0822001fe04110
  | 1 => 0xbfc4088021ff9844010ff8c220087f46110043fd3088021fc9844010ff0c220047fe4110003ef2088011fd9044015ffc42200aff82110003ff65480017fb2a4000dfd9520004feca90053fe65480097f32a4000ff59520005faca90053fc65480097e32a4000df19520024f8ca90003ff64480017fb224013ff9912001dfcc890003fd64480017eb224013ff1912001df8c890053ff5448027ff2a24000ff5512009ff8a89004bff63480257fb1a4000f7d8d20005bec69004bfe63480057f31a4012ff58d20095fac69004bfc63480057e31a4012f718d20015b8c69004bff5348025ff29a4012ff54d20097f8a69004bff4348025ff21a4012ff50d20097f88690053ff5248011ff2924000ff54920047f8a49004fff4248011ff2124000ff50920047f8849004bff3248011ff1924012ff4c920047f86490003ff61480017fb0a4011ff9852000dfcc290003fd6148023fe30a4001bf185200a7fea2900037f5148023ff28a4000ff54520006faa290047fc5148027ffa0a4011ff90520007fa8290047fc4148025ff98a4012f7cc52008ffc629004bfd3148001ee98a4011ff0c520047fe4290003ef2148023ff10a4000ff48520007da4290023fc2148029ffa824000ff94120006fca090003fd5048029fe2824000df1412009ffe8090003fe4048001fea024013ff10120097fe609004bfe3048025fd1824012ff4c120097f2609004bfc3048011ff9024008fec8120007fc4090003ee2048023ff8824011ff04120047feca10022ff6508011ff3284004bf99420047faca10002fd6508011fe3284008bf19420047fec810022ff6408011ff3204003bf99020047fac810002fd6408011fe3204008bf1902007ffea81003bfe5408001feaa0400eff15020047fec610022ff6308011ff3184002bf98c20047fac610036fd6308011fe3184008bf18c2006ffea610037fe530801bfea98400dff14c2006ffe8610037fe430801bfea18400dff10c20045fcc410023ff5208011ff2904008ff54820047f8a410023ff4208011ff2104008ff50820047f88410023ff3208011ff1904008ff4c820047f86410023ff6108011ff3084001bf98420047fac210002fd6108011fe3084001bf1842007ffea2100037f5108019ff2884000ff54420006faa210033fc510801dffa08400cff90420007fa8210033fc410801bff988400df7cc420067fc6210037fd3108001ee988400cff0c420047fe4210023fe2108011fe9084008ff08420085fcc01003fff5008001ff2804000df94020007faa01003ffc5008001be280400effd0020007fc8010003fd400801dfe200400dffcc02006ffc6010037fd300801bfe1804008ffc8020047de4010023fe2008011fd1004008ff48020007da4010023f92008019ff880400cff04020007fecb08002ff6584001bfb
  | 2 => 0x4001ffc82a000ffd4150001dea0a8003ff105400effe62a0077df3150039ff18a801dff4c540007ba62a0073fc3150001ff90a801cff88540007fa42a0073fc21500077fb02801effd4140007fca0a00037e5050001fea82801eff14140006f8a0a000fff4050007fda028003ff901400077c80a000ffc4050007de2028003fe101400effe60a0077fe305003bfe982801dff0c1400e7fe20a0073fc1050011ffb2e4008bfd9720047fccb90012fe65c8011bf32e40049f99720047facb90002fd65c8011beb2e40009f59720047f8cb90022fc65c8011ffb264008bfd9320047fcc99000efe64c8011df3264003af99320047fac990002fd64c8011deb264000af59320047f8c990022fc64c8037ffaa6401aff95320007faa99006bfc54c8011ffb1e4008bfd8f20047fcc79000afe63c8011feb1e4019bf58f20047f8c790022fc63c8033ffa9e4019ff94f200cffaa790067fc53c8033ffa1e4019ff90f200cffa8790067fc43c8011ffa964008ff94b20047faa590023fc52c8011ffa164008ff90b20047fa8590023fc42c8011ff9964008ff8cb20047fa6590023fc32c8011ffb0e4008ff9872000dfcc390023fd61c80017eb0e4008ff1872000df8c39006fff51c8001bfa8e4018ff94720007faa3900037d51c8031fe28e401affd07200c7fc8390003fd41c8031fe20e4019ffcc7200cfbe6390063fe31c8033fe98e4000f74c7200c7f86390023ff21c8011f790e4008ff88720047fa4390003ed21c8011fe10e401bffd4320007fca1900037e50c8001fea86401bff14320006f8a19006bff40c8001ff2064000ff503200d7f88190067ff30c8033ff1864019ff4c3200cff86190063ff10c8031fe0864000ffd9620005fecb1005ffe65880097f32c4000ff59620005facb1005ffc65880097e32c4000ffd9220005fec91005bfe64880077f3244000ff59220005fac91005bfc64880077e3244017ffd52200b7fca910003fd548802dfe2a44010ffd8e20085fec710043fe63880057f31c4010ff58e20085fac710043fc63880057e31c4010ffd4e20087fca710043fd5388021fe29c4010ffd0e20087fc8710043fd4388021fe21c4012bf58a200bffea510023fe5288001fea944008ff14a200b7fe8510023fe4288001fea144008ff10a20087fe6510023fe3288021fe9944008ff0ca20007fec310057fe61880037f30c4000ff58620005fac310057fc61880037e30c4017ffd4620006fea310057fe5188001fea8c4000df546200aff8a31005bff418802bff20c4000ff506200aff88310043ff3188021ef98c4015ff8c620087fa6310003dd318802bfe18c4008ffc86200affc4310003fd2188011fe10c4008bf982200bffea110003fe5088001bf2844000ff542200bff8a1100037c508802dffa044000ff90220007fa811005
  | 3 => 0xe982a027ff0c150137fe20a809bfc1054009bfb20a004df99050026fac8280137c6414009bfb18a004df98c50026fac6280137c6314047bfa18a023df90c5011efa862808f7c4314009bfb10a004df98850026fac4280137c6214049bfa10a000df90850006fa84280937c4214047bf990a023df8c85011efa642808f7c3214009bfb08a004df98450026fac2280027d6114009be308a024dfd0450116fc82280037d4114045be208a023dfcc45011ebe622808b7e3114047be988a000d74c450116f862280037f2114045bf108a000df48450116f842280137e601404b3f300a004de98050126fe80280937c4014047bf980a023df8c05011efa602808f7c3014045bf880a022df04050007fecb20002ff6590043ff32c8004bf99640007facb20002fd6590043fe32c8004bf1964001dfac92000fff5490007ff2a48003ff5524001ff8a920083ff63900417fb1c8020ff98e40015fcc720083fd63900417eb1c8020ff18e40015f8c720083ff5390041ff29c8020ff54e40107f8a72000fff4390007ff21c8003ff50e4001ff88720003ff6290001ff3148008bf98a40007fac520002fd6290001fe3148021ffd4a40007fca520003fd5290043fe2948003ffd0a4001f7e852000ffe4290007fea148000ef50a4001ff88520083ff3290041ff1948020ff4ca40107f86520003ff619003fff30c8001bf98640007fac320002fd619003ffe30c8001bf1864010ffea3200037f519003fff28c8000ff54640006faa32007ffc5190007ffa0c8003ff906400ff7c832000ffd4190007fe20c8003ef10640107fe6320083df319003fff18c8020ff4c640007ba632007ffc3190001ff90c801fff88640007fa432007ffc21900077f3048021ffd4240007fca1200037e5090001fea848021ff14240006f8a12000fff4090007dfa048003fed024001ff8812000ff84090041ff9848020ff8c240107fa6120083fc309003fff884801fff04240007fecaa0002ff6550001bfb2a80009fd95400f7fccaa0012fe6550001feb2a8000bf595400f7f8caa0012fc6550001be32a80049f1954001dfec8a000fff5450007ff2a28003ff5514001ff8a8a0077ff635003b7fb1a801dff98d40015fcc6a0077fd635003b7eb1a801dff18d40015f8c6a0077ff535003bff29a801dff54d400eff8a6a000fff4350007dfa1a8003ff90d4001ffa86a0077bd4350007fe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940045f8c4a007bff5250001ff2928000ff549400f7f8a4a000fff4250007ff2128003ff5094001ff884a0077ff325003bff192801dff4c9400eff864a0003ff61500017fb0a801cff9854000dfcc2a0003fd6150039fe30a8001bf185400f7fea2a00037f5150039ff28a8000ff54540006faa2a0073fc5150007ffa0a8003efd05
  | 4 => 0x96ff639404bff31ca002bf98e5012ffac728096fd639404bfe31ca002bf18e50027fea7280137f5394009ff29ca025df94e50027faa7280977d5394009fe29ca004df14e5012ffe8728097fe439404bfea1ca025ff10e50007fec528003fe62940117f314a000ff58a50005fac528003fc6294009ffa94a004dfd4a50027fca5280037e5294009fea94a000df54a50027f8a5280137c5294055ffa14a000ff90a50007fa85280abfc429404bff994a025ff8ca5012ffa6528097fc3294001ffb0ca029ff9865000dfcc328003fd61940017eb0ca029ff1865000df8c328013ff5194009bfa8ca004ff9465014efca328013fd5194001bea8ca004ff14650026f8a3280abff4194053ff20ca000ff5065014ff88328097ff319404bef98ca029ff8c65012ffa6328003dd3194053fe18ca000ffc865014ffc4328003fd2194053fe10ca004bf98250027fea1280137f5094009fda84a004ff14250027f0a1280abff4094055fe204a025ffcc25012ffc6128097fd309404bfe184a029ffc425014ff821280037f6494055bf324a000df59250156f8c9280977f639404bbf31ca025df58e5012ef8c7280977f439404bbf21ca025df50e5012ef887280037f6294001bf314a000df58a50006f8c5280ab7f4294001bf214a000df50a50156f885280977f329404bbf194a025df4ca5012ef865280037f6194053bf30ca000df58650004fac3280a77c6194055bfa0ca029df90650006fa83280a77c419404bbf98ca025d7cc65014efc63280977d3194001ae98ca029df0c650006fe43280a77e2194001be90ca029df08650024fcc1280ab7f4094055be204a025dfcc25012efc61280977d309404bbe184a029dfc425014ef82128012ff6554001ffb22a000bfd9150147fcc8a800efe6454001feb22a028ff1915001df8c8a8013ff5454009ff2a2a004ff55150027f8a8a809fff635404f7fb1aa027ff98d50015fcc6a809ffd635404f7eb1aa027ff18d50015f8c6a8013ff5354009ff29aa004ff54d50027f8a6a809fff435404fff21aa027ff50d5013ff886a8003ff62540017fb12a000ff98950007fac4a8003fc62540117e312a004ffd4950027fca4a8013fd5254009fe292a028ffd0950007fc84a8003fd4254051fe212a027ffcc95013ffc64a809ffd325404ffe192a000ffd8550005fec2a809bfe61540037f30aa000ff58550137f8c2a8006fc6154009ffa8aa004dfd4550027fca2a8013fd5154001bea8aa004ff14550147fe82a809bfe4154001fea0aa026ff1055013ffe62a809fdf315404dff18aa027ff4c550007ba62a809bfc3154001ff90aa026ff88550007fa42a809bfc21540097fb02a004ffd4150027f6a0a8013fe5054001bf282a004ff14150026f8a0a8013f85054051ffa02a028ff1015013ffe60a809ffe305404ff
  | 5 => 0x453100fbca298807dd514c403aea8a6201f71453100fbe8298807de414c403eea0a6201f71053100fbc4298807d6214c403ee10a6200f7d8131007bcc098803dd604c401ee3026232f7d4131197b8a0988c7df404c463ee2026201f7c413100fb82098823ff65c84117fb2e4208ff99721025fccb90823fd65c84017eb2e4208ff19721045f8cb90823ff64c84117fb264208ff9932101dfcc990823fd64c84017eb264208ff19321045f8c9908c3ff54c845fff2a64200ff5532117ff8a990823ff63c84117fb1e4208ff98f21015fcc790823fd63c845d7eb1e4208ff18f21045f8c7908bbff53c845dff29e422eff54f21177f8a7908bbff43c845dff21e422eff50f21177f88790806fe62c8411ffa964208ff94b21047faa590823fc52c8411ffa164208ff90b21047dc8590823fd42c8401f6a164208ff10b21047fe6590823fe32c8411fe9964208ff0cb2100dfac390807ff51c8403bfa8e4201ff9472100ffaa3908077d51c8403fe28e4201ffd072100ffc8390807fd41c8403fe20e4201ffcc72100fbe6390807fe31c8403fe98e4201f74c72100ff86390807fe21c8403f710e4201fd8872100ff84390807ec21c8411ffb064208ff98321005fcc190823fd60c84017eb064208ff18321187fea1908c3fc50c845fffa06422fff10321177fe61908bbfe30c845dfe986422eff0c32100ffe2190807fc10c8401ffb2a4200bfd952116ffcca90812fe6548401feb2a4200bf5952116ff8ca90812fc6548401ffb224200bfd9121167fcc89080efe6448401feb224200bf59121167f8c89080efc644845bffaa2422cff95121007faa8908b3fc5448457ffb1a422bbfd8d2115ffcc69080afe6348457feb1a422bbf58d2115ff8c69080afc6348457ffa9a422bff94d2115ffaa6908affc5348457ffa1a422bff90d2115ffa86908affc43484037fb12422dffd4921047fca490803fd5248411fe292422cffd0921047fc8490803ee4248401fea124200fb50921047f884908afff3248411ff192422bff4c921047f86490806ff6148403ffa8a4201dfd452100ffca290807fd5148403bea8a4201ff1452100ffe8290807fe4148403fea0a4201ff1052100ffe6290807df3148403ff18a4201fd8c52100ffa6290807dd3148457fa98a4200f54c52100ff86290807ff2148411fb90a4201ff8852100fdc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090802fc604845bffa82422dff14121167fe80908b3fc4048457ff982422bff8c12115ffa60908affc3048403ff8824201ff04121025facb28003ff6494055ff324a003bf99250007fac928002fd6494055fe324a003bf19250027fea9280137f5494009ff2a4a02adf95250027faa9280037d5494009fe2a4a004df1525012ffec728
  | 6 => 0x1ff312a200ff58951007f8c4a8822fc6254409ffa92a204dfd4951027fca4a88037e5254409fea92a200df54951027f8a4a88137c525446dffa12a200ff90951007fa84a88dbfc425446bff992a235ff8c9511affa64a88d7fc32544037fb0aa201ffd4551027eea2a8807fe5154403bf28aa201ff1455100ef8a2a8807f45154403ffa0aa201ff9055100ff882a8807ff3154403ef98aa201ff8c55100ffa62a8807fc3154403ff10aa201ff08551007fec0a8802ff6054401ff302a200ff58151007f8c0a8802fc6054409ffa82a204dfd4151027f8a0a88137c505446dffa02a236ff101511affe60a88d7fe305446bfe982a235ff0c15100ffe20a8807fc1054401bfb22a236df99151006fac8a88db7c645446bbfb1aa235df98d511aefac6a88d77c635446bbfa1aa235df90d511aefa86a88d77c4354401bfb12a200df98951006fac4a88037c625446dbfa12a200df90951006fa84a88db7c425446bbf992a235df8c9511aefa64a88d77c3254403bfb0aa2019fd8551026eec2a88077f4154403bf20aa201df1055100efe62a88075f3154403bf18aa201df4c55100ef862a88077e2154403be10aa200dfd8151006fcc0a88037d6054401be302a2009f181511b6fe80a88db7c405446bbf982a235df8c1511aefa60a88d77c3054403bf882a201df04151007fecaa0802ff6550469ff32a8204bf99541007facaa0802fd6550469fe32a8204bf1954100dfec8a080fff5450407ff2a28203ff5514101ff8a8a08cfff63504677fb1a8233ff98d41015fcc6a08cffd63504677eb1a8233ff18d41015f8c6a08cfff5350467ff29a8233ff54d4119ff8a6a080fff4350407ff21a8203ff50d4101ff886a0803ff62504017fb128200ff98941007fac4a0803fc62504117e3128234ffd4941007fca4a0803fd5250469fe2928203ffd094101f7e84a080ffe4250407fea128200ef5094101ff884a08cfff3250467ff1928233ff4c94119ff864a0806ff6150403ffa8a8201dfd454100ffca2a0807fd5150403bea8a8201ff1454100ffe82a080ff74150403ff20a8201ef9054100ff882a0807bc4150403fa20a8201ffcc54100fbe62a0807fe3150403fe98a8201ff0c54100ffc42a0807fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028200bf181411a7fea0a08d3fc5050407ffa028203efd014101ff880a08cfff3050467ff1828233ff4c14119ff860a0807ff1050403fe0828200f7d9531197bcca98803dd654c465ee32a6200f7d913118fbcc898803dd644c463ee3226232f7d513118fbca898803dd544c463ee2a26200f7d8931007bcc498803dd624c401ee3126232f7d4931007bca498803dd524c465ee2926231f7d0931007bc8498803dd424c463ee2126201f7d853100dbec29880bd7614c403efa8a6201d7d
  | 7 => 0x21023fe5290811fea948408ff14a42047fe8521023bf4290807f7a148408ff10a42047d88521023ff3290811ff1948408ff4ca42047f86521023ff6190811ff30c8401bf98642047fac321002fd6190811fe30c8401bf186421f7fea3210f3fe5190879fe28c8403ffd064201ffc832100ffc419087bff98c843df7cc6421e7fc63210f7fd3190879fe18c8408ff88642047f84321023ff6090811ff3048400bf98242047fac121002fd6090811fe304843effd42421f7f8a12100fff4090807fe204843dffcc2421effc61210f7fd309087bfe184843cffc42421e7f82121003ff65508017fb2a843bff99542025fccaa1003fd65508017eb2a843bff19542025f8caa1022ff6450807ffaa28403ff9514201f7ca8a100ffd5450801deaa28403ff151421d7fec6a10eaff6350875ff31a8402bf98d421d7fac6a10eafd6350875fe31a8402bf18d421d7fea6a10ebfe5350875fea9a843aff14d4201ffe86a100fbf4350807ff21a8403ff50d421d77a86a100ffc43508077fb12843bffd4942047fca4a1003fd5250811fe2928403ffd094201fde84a1023fe4250811df2128408ff109420477884a100fec4250875ff9928408ff8c9421d7fa64a1023fc3250801ffb0a8400bfd85421cffcc2a1006fe6150801feb0a8439ff1854200df8c2a10efff5150873ff28a8439ff1454201ffe82a100fbf4150807ff20a8403ff105421d7fe62a10ebdf3150873ff18a843aff4c5421cff862a10e7fe2150811fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142005f8c0a10efff5050877fe2828403ffd014201ff880a100fbc4050875ff982843aff8c1421d7fa60a10ebfc3050873ff8828439ff04142026fec9a88137e64d4409beb26a204df19351026fec7a88137e63d4409beb1ea204df18f511befe87a88df7e43d446fbea1ea237df10f51026fec5a88137e62d4409beb16a204df18b511c6fe85a88037e42d4401bea16a238df10b511befe65a88df7e32d446fbe996a237df0cb5100cfac3a88077f41d4403bf20ea201df1075100efe63a88075f31d4403bf18ea201df4c75100ef863a88077e21d4403be10ea204dfd8351026fcc1a88027e60d4409beb06a204df183511c6fe81a88e37c40d446fbf986a237df8c3511befa61a88df7c30d4403bf886a201df0435100dfecaa8803ff64544017fb22a236ff9915101dfcc8a8803fd645446dfe322a203bf19151027fea8a88137f5454409ff2a2a236df95151027faa8a88037d5454409fe2a2a204df151511affec6a88d6ff635446bff31aa202bf98d511affac6a88d6fd635446bfe31aa202bf18d51027fea6a88137f5354409ff29aa235df94d51027faa6a88d77d5354409fe29aa204df14d511affe86a88d7fe435446bfea1aa235ff10d51007fec4a8802ff625440
  | 8 => 0xf10554237fe62aa11bdf315508bff18aa846ff4c55422ff862aa117fe215508bfe10aa800ffd8154005fec0aa003fe6055001feb02a800ff18154005f8c0aa013ff5055009fe282a804df1415401ffe80aa00ffc405508dff982a846ff8c154237fa60aa11bfc305508bff882a845ff04154025facb29023ff6494811ff324a403bf99252047fac929002fd6494811fe324a408bf19252027fea929013fe5494809feaa4a404ff15252047fec729022ff6394811ff31ca402bf98e52047fac72910efd6394811fe31ca408bf18e52027fea729013fe5394809fea9ca404ff14e5221ffe872910ffe4394887fea1ca443ff10e52045fcc529023ff5294811bfa94a404fbd4a52047f8a529023ec5294811ffa14a408ff10a52047fe6529023fe3294811fe994a408ff0ca52047fec329023fe61948037f30ca408ff58652005fac329023fc61948037e30ca404ffd4652026fea329013fe5194809fe28ca444ffd0652217fc832910bfc4194887ff98ca443f7cc652217fc632910ffd3194885fe18ca408ff88652047f84329023ff6094811ff304a400bf98252047fac129002fd6094811fe304a404ffd4252027f8a1290137c5094889ffa04a444ff1025221ffe612910ffe3094887fe984a443ff0c252217fe212910bfc10948117fb2aa400ffd9152005fec8a9107fe64548077f322a400ff5915220ff8c8a900efc6454809ffaa2a404dfd5152027fca8a9013fd5454801beaa2a404ff15152207fec6a9102ff6354801efb1aa400b7d8d52207fcc6a900afe6354881feb1aa440bf58d52207f8c6a900afc6354881ee31aa402b718d52027fea6a90137f5354809ff29aa404ff54d52206faa6a9013fc5354881ffa1aa440ff90d52207fa86a9103fc43548097fb12a404ffd4952027dea4a9023fe5254811bf292a408ff14952046f8a4a9013ec5254883ffa12a408ff10952207fe64a9023fe3254881fe992a408ff0c952007fec2a9002ff615487fff30aa401bf98552007fac2a90fffc61548037e30aa404ffd4552026fea2a9013fe5154809fe28aa441ffd05521fffc82a90fffc4154881ff98aa440f7cc5521fffc62a9103fd315487ffe18aa43fff88552047f842a9003ff60548017fb02a400ff98152007fac0a9003fc60548017e302a404ffd4152027f8a0a90137c5054883ffa02a441ff10152207fe60a9103fe3054881fe982a440ff0c1521fffe20a90fffc1054811ffb2c8408bfd9642047fccb21012fe6590811feb2c8400bf59642047f8cb21022fc65908077eb248403ffd524201ffca92100ffd5490807fe2a48408ffd8e42045fec721023fe63908057f31c8408ff58e421edfac721023fc63908117e31c843dffd4e421effca7210f7fd539087bfe29c8403ffd0e4201ffc872100ffd4390807fe21c8408bf98a42047fea5
  | 9 => 0x700100380380180000000000180100100600480a00000280780680580000000480800180180b00000380400480000300080100000080380000680f80180000000000100100480e00000000480080080000200480200100000000c80900300080e80000380300200000a00200000080680280080100300000100300000400101800400080280000480080000080200480000000180100480100080300200180080300900500100080000100000080000180900180000280180200300080f00180180000180180080180000401280380000100580180880080f00800700400000000a80000000600100000080500200180680000580080380400300180080000280300a00000300100000200000200080080880000000100a80900900800080701e00000000180080100780080b00000080000400100080280180000180200100100000200200380480000000000000280100400200300400000200100780600200080000180200180000101580100000b00080300000000380000600700200000080600100180600000000000081000580180081680180000000100000300000780100000180000080380000000080000200a00680200180000080380000082480300000000300c00100000080180000c81000000180000100100a00180080200000b80000080200180080280280280180500480300000b00000680000180000280100180002680000300480280100080100000280080000280000080080300001000080d80780280102100000180200b00680380180200400180000000180000100080000380000400080180c80680180080080300200e00200080000080180301380880000100000400000680000200580000180000200100200000000200300000400900000180000c80180300000480080200100000080400780c80100100a00000400780480100000080580000281b01300280480000280000100000000080380300100000500100000200100100000000100000280000080180280000080080480000000000000680081700380280000000080300080000380580000080700200100eff65550077fb22a803ffd51540277ea8aa00ffe5455007bf2a2a803ff1515401ef8a8aa00fbc545508dffb1aa846bfd8d54237fcc6aa00afe635508dfeb1aa846bf58d54237f8c6aa00afc6355009ffa9aa804ff94d54027faa6aa013fc5355007ffa1aa803ff90d5401ffa86aa00ffc4355001ffb12a800bfd8954007fcc4aa003fd6255001fe312a808bf18954027fea4aa0137f5255009fe292a803ffd095401f7e84aa00ffc425508dff992a846ff8c954237fa64aa11bfc3255001ffb0aa800bfd855422ffcc2aa006fe6155001feb0aa845ff1855400df8c2aa013ff5155009bfa8aa804ff94554027f8a2aa00fff4155007ff20aa803f
  | 10 => 0x1232741d00057800008700034f0000164147e33ec6060005c855c0000000006250da0000003bc2601640000006d80000785036ac29e6914d861d6c60070000002b00001bd00077712137e7e577033d3e206b7162eb45f00000065400047614514140b5aa2345e23176c97290e667071c0001333a776c64a5c01a500070418f08b2d67eb64212b4b21722ab72427134439d5be01a0000000006084d45125e540148a5a410c6232e33f44e10c80c251549545a1c136325e56e05755e25346f1fc0007903787425097640ea2c20cf16d00021c30b4ff30900030d3184e219e5797282cc39f17042b3064d00561fd3b85946cb65a0622dc0003a80005e77897401423722755287334bc64f0000000005390003f020b00026268771a6002473ce2352560002f80df6920907c20007ca7600002ae0f001f0004da5f227b0000000000005ca00043749f2f10000001550000007456c80004cb38563800070e0000007034b10002427127417ea1c665b3af09a7ac66259a0002977870005540000290007ce1802b740500037016e2ca3d27a358800000031f0000000c40000aa2a31ab0003fa7e83f82514c40390007d905b1d000067b5240f46fa0685b876829046731c6ee1e635e25b5ee47300000042c0006020641300d604078a4f60004e97d05ea17b4397007d57920000003ff67742a00012c7ec72a00000078e0000007b40007b87625c67885ed5507a100039a7015937e900024518a2f946e21638c0000000004bb31500045400046b19828f7023a575500079e0000007465d76be52341022f54567a0007841f700008527f4230270984a90f90145554f451a2c60006f90325d436178109334152b36b2046b620e2da2d55270225a12c86652cd00000049662e17e22914f0000004cc53161644062c1ce00000072b0a33d51036c200013d18e79405d29a3531c93e61a44c80000000004ab0004ce00000000063f0000974ea7fd1404ae16806668e2070261190f71110000005d03f906e0005f64f532412a34d2a56814c24e83b43aa00047d29b00000019f3df0005906710000002281cd00007700000016200100200080880180200500000000000300000380180080480180500080a00b80300200000100000080280000000200080200680080200180000600c80180500200000280880200180000000200300380300480000200000700200000080200080001580000000080000300001100000200400180100900200000000080080000101380100080081180080080300280880880d80100000500800300380000a00000700080000000000180580500080400800000000000000480680080000080080080180080100000100280180081900000080000180000400d004800000804000000001000801000801004800000806803000001000000800800
  | 11 => 0x2e80e707d6040007ab7780007bd00000000037c0001d800c6ed0000004000be3f10004845382821ef24b1954990004460885d53081e34cd0005e46e83ac04d54b65d0801b325d64576300071f00f4777ee0ee30273d0bb3a65c231300039408e3160177a004a5677140e307a30f7cb00000057d3671f34dc0005407fa0000093b71b852a0001be4620005221845581f661a4d72140fa2952fb4201f01056d20db0000b65cf0005e328600078377e62600048e14719a43f1936360003a173b70c4c10000003c40001370000002cb0002b306c1240000007580431a073106960c64d33f3b64db3264a35c57f43d67c510b3e16dd7090002224b40000004263306a65a900014c00021a7ba2b61293c02c400012223713e4080006a80dc1160005c93e50000000000000004c35b976b58c4440c30e800000000000000000028b3c900000037700042177200000026d3430003140005102e13a40004357f07b215b3f51266f200000073a77f0000eb0000003991530003ea4870000006db0000005820f11234780005065b421e7934e419b0000000002967d725a0002fc0000000e400019200000038e00000069b52642e2d244852c00000000079c54363a78c00071064c0002ad3cf26a1a83197324a260a5e86dc3f62f455f64e56b70844b63400067526938800000000020c79b15752d00073c48d73600000045700070a7303c700058b0005ff4a06d44ca7e46cc1d97a51974923870c500000000055a62f39c43d4c000000000000022307500000013800544d05c57100023910d0760004f301e0000006f12f30005894e53a90004314040005200000004a408f78d6da5767674687b62050006280d70006d722e00029358165c3486725f34a17ef28e6e27d846109f0006ef62d6584197d63c502e0a97df4ec15c73e6111c52d10387b050b24400058d1a26b762077b55133314369c6bf1760003521d532e62b3ad2723626f333858a2fe5bb1e55134fe31b0006b17f71f94133903310001670c60002920002643c13602597760006f00000000005b550800064857249d0001f800000000000055d0003ef0002ff0000000c017d5d90003913ba0040005e07221366677f52774b37e64277380b900005e0000002097150482f505f00047500007c0004124c70005f90004f16d90000cb05a22c0713893372546c753b00b0000000002ec0005a62270000002e91280001ee00000000000000000038000049400066c7194df5dd29d0f870530a3be3716b920011f7f12b532b20812d0000000005bf3507d407f5175026ab4bd00e00051d10841c3e375f00000034b1651181602de7c837422b7dd7cf4d900076f00000027c0000001f500000045977d3d300053c3d41b62667440007a651b00000000000000030c0002840000006b31ec7a839e0000000000002
  | 12 => 0x4240002bc79f6400005470007c70005dc2aa0006ec66b1e16d36a42181073c310f00063545b08c7507822734585615fc18814b0ae41b44167372f2c15fa0cd70b4076982652e601b7c368c60974337947e0006c503d0545d675c0ff6ce00000061e27a0ef66400023068a0007950002832be2241c20000000000f30f64d30000000b100015100000000037d7a77651ea0825296240000000000003572ea7267c63ab4b03493db4e33c800044c00024e5210114ee3fc0af24c53735443c0a60e269932f54648836e2557180e903503e23660e40a40200016915d6f77b10741a30a41ba6a75ce0007d118d3bf0020336105842416854601143650007e27130004b669a7c01e259b4f80515017be4895af4be18756a1eb2c95d12d756c0006561af1e00b73cd0000000005ac2505996de02136809275d00016f6d540613a35d7cc0002150003e824d0006a96ff75321b48118576918b1ad56d72726717a45300004406a3c62ef50a1df0f50001496831c838346d5c45ef6035345b011d0b800039b00000000000000067c04700000034069544f00000063e0dd56218900000000026100036914e1ed00038d1120001dd2fa0b46500000007343641541865577b975160b4664c50007866cf0000000000ed4360004550d00005a330531255b0006c40b20000002d43a37471152c500000011e7bc7a47db0000004900000007cd0ac12e09967e7560e059d00011354f0282c751100000063003b0003d10000000005b732d2b876e36c51c4b90000000004c973525f0001e86bd31a7fe23b6171cf6a13e95741a62a443800365f63975a5b30fb2ba6537da70f40e0d44290453e71906e03cb00000079100000000000049b00028a00007b64b0003b900a00033500053f10e0000007b526352f7ed2f70004ef37f00048f45138b64925762172329c4cf2f26570004181205b66b82ac3860004633d700065533657f00013f00053d0d200000046a0bd3bd2cf75e1711da64400038104c2d80d85074302a071e4915e90005a545e17369e5f10005d30006ea5a20002f649c67f3977dc67646438a3f300000000000000051f1f21b52db5530000006880001b200032a0006150000000005756a059c20608400010200000000000000001311b5805732dd00054d6c17c92bb5303734714090005f853a0005f56eb68200047a2ce2216e16120000c700000000009c2435fd4161bb0c135845d69d6df0917c40005666bb68d26e02b2330203de1460004325591ac0e54b86ba33b50e3bb3014b57794112a64de72549e5355da0002793473590bc4153936197755194741d204b1c76a27575830603ca15a1fa5875de0006680cc0ba75b61336a4f00a22e21a976154a13900035f69f03107216c0530005420b020a54c1250000a71f10496b40007a22ed17c00003600
  | 13 => 0x1996aa08907361844e00057a16a1007853033d87990185fe6610003950003455927d26903214dd6a50015a86fb30e1fb3b158f4aa22a4f27fb0007c13a061f61b0000005cd74e0a12190300ad1bf32c21d07003c0e12200006a365900028760116b0006273dc0000002b173f0004d50006f51356ae3250006740ce0003b534e2e00500553761d74801e97590003b24832e766f32200006126821337b2c31630a814803735561c40f77441a47b3cc3285db53215277c1096371565ae00000015900069400066927e4454284fc04e1740de0bf60f4e723f1a114d6222a94ad00070d1e45640000c90007f900056079800059633e2b21752760580002253fe5f00001f44822a726f4504225ad7e741f67d14a6d150d7b313c3987801fe0004420004a65eb17835b7fc6cd42d0674430003f27960f27f20ab7115e650c78b68608121f59163b0006636b246503a0106781106af56324828d00000030400000000000000052509b00047010a15e0635c74493e45142b403f11c79a4036d07665861b96847e11e700000000025834602a76a54e0000000527f672c4e059f4d67173072b900079700053615821752e48b0000000000000000001aa0000001817a924020d4346bc0951170001d100000000031000002400020333424974c4fb21100073974f45c00023e74a0004e67b700000075400034200000056f0001cb1270000000000000000000006e300059522677135c0001504f94eb1316806d62940003eb00046c19635a2d00002af1790005f433c0b50941440000000005440004ac6290230001825b17482d344a5180656b00831770000000ec0000d123d0000b339649a24a01248c4fd11a7d35337aa2984c64560001de5561ca4fa0000007072015c306d5f734a4930007f800031d00032947919400001d0002ee0002386c36b55ec15f3823ee6791d36e50005701043f71db09d57e59e72e57b0d50ca3005853d043a02c0007bf0003663920415e113400031100005966e76d50f00013b3a26521836e90000007de2c06e60460000000000fe0004a500009e5d233a5683fd5040003e057702d1ff22d0000005056334af0002465cb0005d800000019d6890004690960000d900000008600000042572d6661d459862a51e20f7ad2706e466a58e08a0250003da1b14d226b2e540c0004982813515fb01508d37a53e3200190fd00068b01c6fe50070674d2520d30791666f41cc3b017f7f319c74b5161c03321bc0003565652bd5a74b740d31e4ed6436472993c272128c7371c323a36f55254977300007e00837548657c3d971d2744bf00d1b77bb00041e0006070007520000002bf42f06f69710600024f5bc60d12f7af54165e2a20000000000a56e72df6c000003400000047f1321b40000000007495ab56904f29f6310000006f8000646720
  | 14 => 0x68f41700618c0000001ae2025970004330005b20006fc3ed77a00000043b0002910427e078f4850000005ba0000000005df2e46fd0002800001b01dc47228528800000033934c2d947c6600006ad4d10002a13ae79d36d00071b0a06146f616169366d00064102f0000000000002f010163d7ae63c2316ca4f723c2fd3844ba2890005a00fc0005bd38f4a700060527800000069625c0000006510001d65cc27d43e1c44520000004970000005c16321910004a85483fb0000003232100003dd3b30002322a826c0001a74470
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x86490110005f97290110037bb4290110007b9429011000dfa719011000df871901100fefb61901100ff7b51901100ff7951901100ffba41901100ffb841901100ffdb31901100ffd9319011001cff765011000cfe76501100e4fd765011000cfc76501100057f755011003d7c75501100067f65501100f67c6550110006bf645011001ebc6450110005f7715011000df471501100077a5050110007785050110037b8405011000df8765011001ef8765011000cf876501100077b75501100077875501100077b65501100077865501100fdfb7450110007bb7450110007bb645011001efa645011001ef86450110037b86450110037bb4350110257b94350110005fb7250110007f3715011000dfa715011000df871501100e7f071501100e6fb61501100e77b51501100e77951501100e7bb41501100e7b941501100e7db31501100e7d9315011000cfe76c811000cfc76c811003d7e75c81100057d75c81100067f65c81100de7c65c8110035be74c8110005bd74c8110006bf64c81100d6bc64c8110006ef62c8110046ec62c811000df671c8110005f571c8110064fe76881100067f65881100be7c6588110006bf64881100b6bc64881100077a5088110007785088110065fa7688110006fa76881100077b6588110007786588110005fb7488110005f97488110007bb6488110007b8648811024efb638811024ef9638811008df97288110046fa6288110046f8628811000dfa718811000df871881100aefb61881100af7b51881100af7951881100afdb31881100afd93188110044ff764811000cfe764811008cfd764811000cfc76481100057f754811003d7c75481100067f65481100a67c6548110006bf644811009ebc6448110005df734811002ddc7348110006ef6248110046ec6248110005f7714811000df471481100077a504811000778504811000df87648110046f8764811000cf876481100077b75481100077875481100077b6548110007786548110005fb7448110005f97448110007bb6448110007b86448110007db7348110247d87348110246fb6348110246f96348110007eb7248110007eb6248110046fa6248110046f86248110007e86248110007f3714811000dfa714811000df8714811008ff0714811008efb614811008f7b514811008f79514811008fdb314811008fd9314811008feb214811008fe921481100acfe76081100067f650811007e7c6508110006bf6408110076bc64081100adfa7008110007e9200811000df6768411000ef6768411000cf6768411023f77758411023f747584110007776584110007746584110007b76484110007b4648411000df6708411000ff2708411000ef7608411000ff3608411023f76508411023f745084110007f24084110007f14084110007f22084110007f12084110
  | 1 => 0x89100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc7358910006ef725891008cff7158910006f7715891008e7f515891008e7d515891008edf315891008edd31589100c4ff7058910006fb70589100acfe76189100067f65189100067c6518910006bf6418910006bc6418910046ee6218910006ed6218910044ff7694910004fe7694910004fd7694910044fc76949100067f65949100267c6594910006bf6494910226bc6494910005fa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100267c6554910006bf645491020ebc6454910005df735491002ddc7354910044ff7690910004fe7690910004fd7690910044fc76909100067f65909101f67c6590910006bf649091001ebc6490910005fa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101de7c6550910006bf645091001ebc6450910114fe769411014e7f65941100267e65941100067d65941100267c6594110006bf6494110156bc649411014ff010941101157e76941100067e76941101147e76941100067f64941100073f64941100063f64941101567e64941100067d64941101567c64941100073c64941101563c64941102867f639411012e7e63941102867d639411012e7c63941100067f629411027e7e62941100067d629411027e7c629411014d7f719411014d7d719411023e7f619411014f5f319411014f5d31941101157e709411014e7f609411014f7b109411023f74109411014f78109411014f701094110024ff765411000cfe7654110134fd765411000cfc76541100067f65541100267c6554110006bf6454110146bc6454110005f7715411000df47154110137f0105411014d7e761411003e7e761411014c7e76141100067f64141100073f64141100063f64141101267e64141100067d64141101267c64141100073c64141101263c64141102767f631411011e7e63141102767d631411011e7c63141100067f621411026e7e62141100067d621411026e7c62141101157f71141101157d711411023e7f61141101175f31141101175d311411014d7e701411003f7a70141101167f60141101177b101411023f741014110117781014110264fe76901100067f659011010e7c65901100febf649011001ebc64901100077a5090110007785090110265fa769011025efa76901100077b65901100077865901100e5f974901100ffbb649011001efa649011001ef86490110037b8649011001eb
  | 2 => 0xffb410d91100ffb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91100febf71d91100febe71d91100febd71d91100febc71d91100febf51d91100fe3f51d91100febe51d91100febd51d91100fe3d51d91100febc51d91100febf31d91100fe9f31d91100febe31d91100febd31d91100fe9d31d91100febc31d91100febf21d91100febe21d91100febd21d91100febc21d91100febf70d9110036be70d91100febd70d9110006bf50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d91100febf10d91100febe10d91100febc10d91100057f755911003d7c75591100067f65591100067c6559110036bc645911028dfb7059110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c75591100fcff7459110006bf7459110004ff7359110014fe7359110004fd7359110014fc7359110004ff7259110044fc72591100e4ff7159110006f771591100e67f51591100e67d51591100e6df31591100e6dd315911028cff7059110006fb70591100fdbe7619110036be76191100fcbe7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c65191100379e73191100379d7319110006bf6319110006be6319110006bd6319110006bc6319110266bf61191102673f51191102673d51191102679f31191102679d3119110267b97019110266bf6019110267bb1019110267b41019110267b81019110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100267c6555110006bf645511001ebc6455110044fe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910006ef32d8910006ec32d89100acff71d891000cfe71d89100acfd71d891000cfc71d89100ae7f51d89100ae7d51d89100aedf31d89100aedd31d89100aeef21d89100aeed21d8910044fe70d8910044fc70d891003d7e75989100057d75989100067f65989100067c6598910035be7498910005bd7498910006bf6498910006bc6498910006ef629891008df970989100057f755891003d7c75589100067f65589100067c6558910005bf7458910035bc7458910006bf6458910006bc6458910005df735891002ddc73589100c5fb7058910004ff755
  | 3 => 0xc70d951003e7f50d95101157e76d95100247e76d95100067e64d95100067c64d95100067f63d95100067e63d95100067d63d95100067c63d951014f5f31d951014f5d31d951014f7b10d951014f7410d951014f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d951014e7f71d951014c7f71d951014e7e71d951014e7d71d951014c7d71d951014e7c71d951014e7f41d951014e7e41d951014e7d41d951014e7c41d951014e7f31d951014e5f31d951014e7e31d951014e7d31d951014e5d31d951014e7c31d951014e7f21d951014e7e21d951014e7d21d951014e7c21d951014e7f70d951003e7e70d95100247e70d951014e7d70d95100247c70d95100067f40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d951014e7f10d951014e7e10d951014e7c10d951003e7c6559510005bf7459510035bc7459510295fb705951014cff75595100067f7559510004ff7459510006bf7459510004bf745951001cfe745951001cfc7459510006bc745951001cbc7459510004ff7359510014fe7359510004fd7359510014fc7359510004ff7259510044fc7259510134ff7159510006f771595101367f51595101367d5159510136df3159510136dd3159510294ff7059510006fb705951003e7c505951014d7e761951003e7e761951014c7e76195100067e64195100067c64195100067f63195100067e63195100067d63195100067c63195101167f61195101175f31195101175d31195101167f60195101177b101951011774101951011778101951001cfe76d91100067f65d91100067c65d9110036be64d9110024fe75d9110004fd75d9110024fc75d9110006bf54d9110036be54d9110036bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d9110036bf43d9110006be43d9110006bd43d9110036bc43d9110044fe72d9110004fd72d9110036bf42d9110036bc42d91100fcff71d911000cfe71d91100fcfd71d911000cfc71d91100fe7f51d91100fe7d51d91100febf41d91100febd41d91100fedf31d91100fedd31d911001cfe70d911000cfd70d911001cfc70d9110036bf40d9110265be76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100ff3f51d91100ff3d51d91100ff9f31d91100ff9d31d91100ffbb70d91100ffbb10d9110
  | 4 => 0x21000df9769021001ef9769021000cf9769021023f7b659021023f78659021001efa6490210057ba6490210007b9649021001ef86490210005f97290210057bb4290210007b9429021000dfa71902100fff27190210007f1719021000df871902100ff7b51902100ff7951902100ffba41902100ffb841902100ffdb31902100ffd9319021028cff76502100057f755021005d7c75502100067f65502100f67c6550210006bf645021001ebc64502100077a5050210007785050210057b8405021028dfb76502102b6fb76502100077b75502100077875502100077b6550210007786550210007bb7450210007bb645021001efa645021001ef86450210057b86450210057bb43502102afb94350210005fb725021000dfa715021000df871502100e77b51502100e77951502100e7bb41502100e7b941502100e7db31502100e7d9315021008cfd76c821005d7e75c82100057d75c82100067f65c82100de7c65c8210055be74c8210005bd74c8210006ef62c8210046ec62c821000cff768821000cfd768821023e7f658821023e7c6588210046ee6288210006ed628821000df67188210005f5718821023f7a508821023f78508821000df97688210046f9768821000cf9768821023f7b658821023f786588210005fb7488210005f974882102a6fb63882102a6f96388210046fa6288210007ea6288210007e96288210046f8628821000dfa71882100aff27188210007f1718821000df871882100af7b51882100af7951882100afdb31882100afd931882100c4ff76482100057f754821005d7c75482100067f65482100a67c6548210005df734821004ddc7348210006ef6248210046ec62482100077a50482100077850482100c5fb7648210006fb76482100077b75482100077875482100077b6548210007786548210005fb7448210005f97448210007db734821029fd8734821029efb634821029ef96348210007eb7248210007eb6248210046fa6248210046f86248210007e8624821000dfa714821000df8714821008f7b514821008f79514821008fdb314821008fd9314821008feb214821008fe9214821000cff760821000cfd7608210044fc760821023e7f650821023e7c6508210046ee6208210006ed620821000df67108210005f57108210007e92008210024fe76d951003e7e65d951001cfe74d9510004fd74d951001cfc74d951003e7f54d95100067e54d951003e7c54d9510004ff73d9510014fe73d9510004fd73d9510014fc73d951003e7f53d95100067e53d95100067d53d951003e7c53d9510044fe72d9510004fd72d951003e7f52d951003e7c52d951014cff71d951000cfe71d951014cfd71d951000cfc71d951014e7f51d951014e7d51d951014edf31d951014edd31d9510024fe70d951000cfd70d9510024f
  | 5 => 0x4fd74d8a1001cfc74d8a10004ff73d8a10014fe73d8a10004fd73d8a10014fc73d8a10006f571d8a100ae7f51d8a100ae7d51d8a100aedf31d8a100aedd31d8a10064fe70d8a10006fa70d8a1008cfd7698a1005d7e7598a100057d7598a100067f6598a100067c6598a10055be7498a10005bd7498a10006ef6298a10044ff7658a100057f7558a1005d7c7558a100067f6558a100067c6558a10005df7358a1004ddc7358a10004ff7558a100067f7558a100047f7558a10024fe7558a10024fc7558a100067c7558a100247c7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10006df7358a10004df7358a10014fe7358a10004fd7358a10014fc7358a10006dc7358a10014dc7358a10006ef7258a1008e7f5158a1008e7d5158a1008edf3158a1008edd3158a1008eef2158a1008eed2158a10044ff7058a10044fd7058a1023e7f6518a1023e7c6518a10046ee6218a10006ed6218a100adfa7018a10044ff7694a10004fe7694a10004fd7694a10044fc7694a100067f6594a100267c6594a10005fa7094a10005f97094a10004ff7654a10004fe7654a10004fd7654a10004fc7654a100067f6554a100267c6554a10005df7354a1004ddc7354a10044ff7690a10004fe7690a10004fd7690a10044fc7690a100067f6590a101f67c6590a10005fa7090a10005f97090a10004ff7650a10004fe7650a10004fd7650a10004fc7650a100067f6550a101de7c6550a10006bf6450a1001ebc6450a10005f77150a1000df47150a1000cff7694210024fe769421000cfd76942100267e65942100067d659421000df67194210005f5719421023e7f769421023e7e769421023e7d769421023e7c769421023e7f64942101567e64942100067d649421023e7c649421023e7f639421012e7e63942102c67d639421023e7c639421023e7f629421027e7e62942100067d629421023e7c629421023f76719421014d7d719421023f75719421000575719421014f5f319421014f5d319421023e7e609421023f77109421014f7b109421023f781094210294ff76542100067f65542100267c655421023e7f761421023d7e761421023e7e761421023e7d761421023e7c76142100247c761421023e7f64142101267e64142100067d641421023e7c641421023e7f631421011e7e63142102be7d631421023e7c631421023e7f621421026e7e62142100067d621421023e7c621421023d7f711421023f7671142101157d711421023f7571142100057571142101175f31142101175d311421023f7a701421023e7e601421023f7710142101177b101421023f78101421000cff769021001cfe769021000cfd769021023e7f659021023e7c659021001ebe6490210006bd649021000df67190210005f5719021023f7a509021023f78509
  | 6 => 0xe64d961023e7c64d961023e7f63d96100067e63d96100067d63d961023e7c63d961023f7571d961014f5f31d961014f5d31d961023d7e70d961023f7a70d96101157a70d961023f7710d961014f7b10d961023f7810d961023e7f74d96100067e74d96100067d74d961023e7c74d961023e7f73d96100067e73d96100067d73d961023e7c73d96100067f43d96100067e43d96100067d43d96100067c43d961023e7f72d96100067e72d96100067d72d961023e7c72d96100067f42d96100067c42d96100067f32d96100067e32d96100067d32d96100067c32d961014e7d71d96100067571d961014e7f41d961014e7e41d961014e7d41d961014e7c41d961014e7f31d961014e5f31d961014e7e31d961014e7d31d961014e5d31d961014e7c31d961014e7f21d961014e7e21d961014e7d21d961014e7c21d961023e7e70d96101147e70d96100067a70d96100067f40d961023e7c40d96100067f30d961023e7e30d96100067d30d961023e7c30d961014e7f10d961023e7c10d9610024ff765961005e7c65596100067f7559610004ff745961001cfe745961001cfc7459610004ff7359610014fe7359610004fd7359610014fc7359610004ff7259610044fc72596101367f51596101367d5159610136df3159610136dd3159610024ff7059610024fd705961000cfc705961005e7c505961023e7e76196100067e641961023e7c641961023e7f63196100067e63196100067d631961023e7c631961023f7571196101175f31196101175d311961023d7e701961023f7a701961014d7a701961023e7e601961023f7710196101177b101961023f78101961023e7f65d921023e7c65d9210056be64d9210265fa70d9210024fe75d9210004fd75d9210024fc75d92100e4fd74d9210004ff73d9210014fe73d9210004fd73d9210014fc73d9210044fe72d9210004fd72d9210056bf42d9210006f571d92100fe7f51d92100fe7d51d92100febe41d92100febc41d92100fedf31d92100fedd31d9210264fe70d9210006fa70d9210056bf40d921001cff76592100057f755921005d7c75592100067f65592100067c6559210056bc6459210004ff75592100067f75592100047f7559210024fe7559210024fc75592100067c75592100247c7559210006bf7459210004ff7359210014fe7359210004fd7359210014fc7359210056bf4359210006bd4359210004ff7259210044fc72592100e67f51592100e67d51592100e6bf41592100e6bd41592100e6df31592100e6dd315921001cff705921001cfd705921000cfc7059210056bc4059210004ff7655210004fe7655210004fd7655210004fc76552100067f65552100267c655521023e7f65d8a1023e7c65d8a10065fa70d8a10024fe75d8a10004fd75d8a10024fc75d8a1001cfe74d8a10
  | 7 => 0x420044fc765042001ebe6450420006bd645042000ef66150420006f56150420006df764c4202f6de764c420006dd764c4202f6dc764c4202f6df654c420196de654c420006dd654c4202f6dc654c4202f6df644c42018ede644c420006dd644c4202f6dc644c420007cf724c4202f7cc724c4200c6de624c420065df714c42006fd7714c420066df614c42000ede614c420067d6614c42000ed6614c420066dd614c4202f7d5614c420006d5614c42000edc614c4200675f514c4200675d514c420067d6214c4202f7d5214c4200aede604c4202f7cf204c4202f7da204c4202f7d9204c4200bcff7694020044fe7694020024fd7694020044fc76940200267e65940200067d6594020045ee7294020005ed729402023e7f769402023e7e769402023e7d769402023e7c769402023e7f64940201567e64940200067d649402023e7c649402023e7f639402012e7e63940202ee7d639402023e7c639402023f6e729402023f6d729402027e7e62940200057d719402014e7e61940200067d619402023e7c61940202ef5f31940200075d319402023d7e709402023e7e609402023f6f209402023f7a209402027f7920940200bcff765402023e7f761402023e7e761402023e7d761402023e7c761402023e7f64140201267e64140200067d641402023e7c641402023e7f631402011e7e63140202e67d631402023e7c631402023f6e721402023f6d721402026e7e62140200057d71140201167e61140200067d611402023e7c61140202e75f31140200075d311402023d7e701402023f7a701402023e7e601402023f6f201402023f7a201402026f7920140202df7b101402023f7810140200b4ff7690020044fe769002001cfd7690020044fc769002001ebe6490020006bd6490020045ee7290020005ed729002023f7850900200b4ff76500200057f755002007d7c7550020007785050020077b84050020045ef7648020006ef7648020004ef76480200076f75480200076c7548020007cf73480202cfcc7348020006ed61480200076f51480200076d51480202cfcf3148020007cd3148020045ef7048020047eb70480202d6ee6048020047ea604802023f6e5048020007ea50480200076a5048020007e9504802023f6c50480202cfeb30480202cfe8304802005e7e65d9610115fa70d9610134fd75d961001cfe74d9610004fd74d961001cfc74d961005e7f54d96100067e54d961005e7c54d9610004ff73d9610014fe73d9610004fd73d9610014fc73d961005e7f53d96100067e53d96100067d53d961005e7c53d9610044fe72d9610004fd72d961005e7f52d961005e7c52d9610006f571d961014e7f51d961014e7e51d961014e7d51d961014e7c51d961014edf31d961014edd31d9610114fe70d9610006fa70d961005e7f50d96100067
  | 8 => 0x67f65881200be7c6588120006df6388120086dc6388120045fa7088120046fb60881200076f65881200076c6588120007cf638812031fcc6388120005ed71881200076f51881200076d518812031fcf3188120007cd3188120045ee7088120046ef6088120047eb608812023f6e508812023f6c508812031fea308812031fe930881200467f7559420004ff745942001cfe745942001cfc745942007e7f5459420004ff7359420014fe7359420004fd7359420014fc735942007e7f53594200067d5359420044ff7259420044fe7259420044fd7259420044fc72594200467e52594200467c5259420004ff715942000cfe715942000cfc715942007e7f5159420006df315942007cfc705942007e7c5059420004ff7559020024fe7559020024fc7559020046bf7459020076be5459020004ff7359020014fe7359020004fd7359020014fc7359020076bf4359020006bd4359020044ff7259020044fe7259020044fd7259020044fc7259020046be4259020046bc4259020004ff715902000cfe715902000cfc7159020076bf4159020006df3159020074fc7059020076bc4059020004ff7655020044fe7655020004fd7655020044fc76550200267e65550200067d655502001ebe6455020006bd6455020004ff7558420024fe7558420024fc7558420004ff745842001cfe745842001cfc7458420004ff7358420014fe7358420004fd7358420014fc735842000cfd7258420046f77158420066f65158420066f64158420066df3158420066f63158420006f53158420046f72158420046f4215842000cff7058420046ef2058420046fa2058420046f92058420066f410584200267f76d442030e7e76d442007e7d76d44200267c76d442030e7f64d44201c67e64d44200067d64d442030e7c64d442030e7f63d44201be7e63d44203167d63d442030e7c63d44200c67e62d44200657d71d44200667f61d442000e7e61d44200667d61d442000e7c61d44200675f31d442023d7e70d44200ae7e60d442030f6f20d442030f7a20d442030f7920d4420004ff7654420004fd7654420044fc76544202fe7f65544200267e65544200067d65544200267c655442000ef66154420006f56154420005fb7054420005f870544200067f76544202fe7e76544200067d76544202fe7c76544202fe7f64544201b67e64544200067d64544202fe7c64544202fe7f63544201ae7e63544203067d63544202fe7c63544200c67e62544200657f715442007f7771544200667f615442000e7e615442006776615442000e7661544200667d61544202ff75615442000675615442000e7c61544200675f31544200077b705442023d7c70544200077870544200057870544200ae7e60544202ff6f20544202ff7a20544202ff792054420004ff7650420004fd765
  | 9 => 0xc654c520006df644c52018ede644c520006dd644c52018edc644c52008ddf714c520097d7714c52008edf614c52000ede614c52000edc614c52008f5f514c52008f5d514c52008fd6214c520007da704c520007d9704c5202f7db204c520005ee76c8520046ee76c85200076f65c85200076c65c8520006ef64c8520006ed64c8520007cf63c852034fcc63c852008ded71c852000eee61c852000eec61c852008f6f51c852008f6d51c852008fcf31c852008fcd31c8520047eb70c8520005ee70c8520047e870c8520046ef60c8520047eb60c852034fea30c852034fe930c852000cfc76485200067f654852016e7c6548520006df634852015edc6348520006f7614852000ef46148520007d53148520005fb7048520005f87048520047e8204852008dec764852000eec764852000cec76485200076f65485200076c6548520006ef6448520006ed6448520007cf6348520347cc6348520045ef7148520047e77148520007e7614852000eee614852000eec614852008fe4614852008f6f514852008f6d514852008fcf314852008fe6314852008fcd3148520347e53148520007c53148520007eb7048520005ec7048520007e87048520046ef6048520047eb6048520347ea3048520347e930485200dcfe76941200067f65941200267e65941200067d65941200267c6594120006df639412012edc63941200057e76941200067e76941200047e76941200067f64941201567e64941200067d64941201567c649412033e7f63941200075f63941200065f639412012e7e639412033e7d639412012e7c639412033f5c639412012e5c63941200057d71941200067f619412014e7e619412014e7c619412033f5f31941200075d31941200076f21941200076d21941200a57e709412033f7a309412033f79309412027f7b2094120024ff76541200a4fd7654120044fc76541200067f65541200267c6554120006df635412013edc6354120005ef7254120045ec72541200057e76141200a67e76141200047e76141200067f64141201267e64141200067d64141201267c64141203267f63141200075f63141200065f631412011e7e63141203267d631412011e7c63141203275c631412011e5c63141200057d71141200067f61141201167e61141201167c61141203275f31141200075d31141200076f21141200076d21141203357e70141200a77a701412032f7b401412032f7840141203277a301412032779301412026f7b20141200d4fe76901200067f659012010e7c659012001ebe6490120006bd6490120006df6390120106dc639012001cff765012009cfd7650120044fc76501200057f75501200a57c75501200067f65501200f67c6550120006bf645012001ebc6450120006df63501200eedc6350120005ef7250120045ec7250120
  | 10 => 0x8d20006dc41d8d20366df21d8d20006de21d8d20366dc21d8d20366df70d8d20096de70d8d20096dd70d8d20096dc70d8d20006df50d8d20006dc50d8d20006df40d8d20006dc40d8d20366df20d8d20096dd20d8d20366dc20d8d20006df10d8d20006dc10d8d20024fc76549200067f65549200267c6554920005df7354920095dc7354920006df6354920206dc63549200476c5254920005fb7054920005f87054920047e8205492001cfc76509200067f65509201de7c6550920006bf645092001ebc6450920006df63509201d6dc6350920005fb7050920005f8705092000cfe76d85200067f65d85200067c65d8520095dc73d8520006df63d8520006dc63d852008ef661d85200067f75d8520024fe75d8520004fd75d8520024fc75d85200067c75d852001cfe74d8520004fd74d852001cfc74d8520004ff73d8520006df73d8520014fe73d8520004fd73d8520014fc73d8520006dc73d8520014dc73d852000cfc72d8520006f741d852008ef441d852008edf31d852008ef621d852000cfe70d8520044fd70d852008ef710d85200057f75585200a57c75585200067f65585200067c6558520005bf745852009dbc7458520005df7358520095dc7358520006df6358520006dc635852008ef461585200267f76d45200057e76d45200a67e76d45200047e76d45200a67d76d45200a57c76d45200267c76d45200247c76d45200067f64d45201c67e64d45200067d64d45201c67c64d452035e7f63d45200075f63d45200065f63d45201be7e63d452035e7d63d45201be7c63d452035f5c63d45201be5c63d452008d7d71d452008e7f61d452000e7e61d452000e7c61d452008f5f31d45200057e70d452035f7a30d452035f7930d452030f7b20d4520004ff7654520004fe7654520004fc76545200067f65545200267e65545200067d65545200267c6554520006df63545201aedc63545200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545200067f64545201b67e64545200067d64545201b67c64545203567f63545200075f63545200065f63545201ae7e63545203567d63545201ae7c63545203575c63545201ae5c635452008d7f71545200a777715452008e7f615452000e7e615452000e7c615452008f5f31545200057c70545203577a30545203577930545202ff7b2054520004ff7650520004fe7650520004fc76505200067f65505201a67c655052001ebe6450520006bd6450520006df635052019edc6350520006df764c520005de764c520006de764c520004de764c520006dd764c520005dc764c520006dc764c520004dc764c520006df654c5200075f654c5200065f654c520196de654c520006dd654c520196dc654c5200075c654c5201965
  | 11 => 0x4ff745952001cfe745952001cfc7459520004ff7359520006df7359520004df7359520014fe7359520004fd7359520014fc7359520006dc7359520014dc73595200bcff7259520006ef7259520004ff715952000cfe715952000cfc71595200a67f5159520006df31595200dcff7059520006fb70595200a67c50595200057e76195200a67e76195200047e76195200067e64195200067c64195200067f63195200067e63195200067d63195200067c63195200075c63195200065c63195200057d71195200067e61195200067c61195200075f311952026e7f60195200077a301952000779301952026f7b201952026f78201952001cfe76d91200067f65d91200067c65d912009ebe64d9120006dc63d9120024fe75d9120004fd75d9120024fc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d9120044fe72d912009cfd72d9120044fc72d912009ebf42d912000cfe71d9120004fd71d912000cfc71d9120006be41d912009ebc41d9120006df31d9120044fd70d912009ebf40d91200057f75591200a57c75591200067f65591200067c655912009ebc6459120005df7359120095dc7359120006dc6359120005f7715912008df47159120004ff75591200067f75591200047f7559120024fe7559120024fc75591200067c75591200247c755912009cff7459120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc735912009ebf4359120006bd43591200b4ff7259120006ef7259120004ff7159120006f77159120004f7715912000cfe715912000cfc7159120006f4715912000cf4715912009ebf4159120006df31591200d4ff7059120006fb705912009ebc4059120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200267c6555120236dc6355120005fb7055120005f87055120095de76d8d20096de76d8d20014de76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d20005dd71d8d20006de61d8d20006dc61d8d20367db70d8d20097d870d8d20367db20d8d20367d820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d20366de72d8d20096dd72d8d20366dc72d8d20006df52d8d20366de52d8d20366dc52d8d20006df42d8d20366de42d8d20366dc42d8d20006df71d8d20006de71d8d20006dd71d8d20004dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dc51d8d20006df41d8d20006de41d
  | 12 => 0xd649422023e7c649422023e7f639422012e7e63942203867d639422023e7c639422023f6e729422023f6d72942200057d719422014e7e61942200067d619422023e7c61942203875f31942200075d319422023f7a309422038779309422027f7b209422007cff765422023e7e761422023e7d761422023e7f64142201267e64142200067d641422023e7c641422023e7f631422011e7e63142203767d631422023e7c631422023f6e721422023f6d72142200057d71142201167e61142200067d611422023e7c61142203775f31142200075d311422023f7a701422037f7b401422023f78401422023f7a301422037779301422026f7b201422001cfe7690220044fd769022001ebe6490220006bd6490220045ee7290220005ed7290220074ff76502200057f75502200bd7c7550220005ed76c8220046ed76c82200476e75c82200476d75c8220047ae74c8220047ad74c8220006ed61c82200076f51c82200076d51c822036fcf31c8220007cd31c8220047ea60c822023f6e50c822023f6c50c8220024fe76d95200a67e65d9520006dc63d952001cfe74d9520004fd74d952001cfc74d95200a67f54d95200067e54d95200a67c54d9520004ff73d9520014fe73d9520004fd73d9520014fc73d95200a67f53d95200067e53d95200067d53d95200a67c53d9520044fe72d95200a4fd72d9520044fc72d95200a67f52d952000cfe71d9520004fd71d952000cfc71d95200a67f51d95200067e51d95200a67c51d9520006df31d9520044fd70d95200a67f50d95200a57e76d95200247e76d95200067e64d95200067c64d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200057d71d95200067e61d95200067c61d95200075f31d95200077a30d95200077930d952027f7b20d952027f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d952027e7e72d95200067d72d952027e7c72d95200067f42d952027e7e42d952027e7c42d95200067f32d952027e7e32d95200067d32d952027e7c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067f31d95200065f31d95200067e31d95200067d31d95200067c31d952027e7f21d95200067e21d952027e7c21d952027e7f70d95200a67e70d95200067d70d95200067f40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d952027e7f20d952027e7c20d95200067f10d95200067c10d95200a67c6559520005df7359520095dc7359520006dc63595200a4ff75595200067f7559520
  | 13 => 0x96200b6be64d9220024fe75d9220004fd75d9220024fc75d92200b4fd74d9220004ff73d9220014fe73d9220004fd73d9220014fc73d9220006ed72d922000cfe71d9220004fd71d922000cfc71d9220006df31d9220006fa70d922001cff76592200b6bc6459220004ff7559220024fe7559220024fc7559220006bf7459220006bf54592200b6bc5459220004ff7359220014fe7359220004fd7359220014fc73592200b6bf4359220006bd43592200b6bf4259220004ff715922000cfe715922000cfc71592200b6bf4159220006df3159220044fc70592200b6bc4059220004ff7655220004fe7655220004fd7655220004fc76552200067f65552200267c6555220005fb7055220005f87055220024ff7654a200267e6554a200067d6554a20005df7354a20085dc7354a20005fb7054a20005f87054a2001cff7650a2001ebe6450a20006bd6450a20005fb7050a20005f87050a200aef661d862000cff76586200aef46158620004ff7558620024fe7558620024fc7558620004ff745862001cfe745862001cfc7458620004ff7358620014fe7358620004fd7358620014fc73586200aedf31586200aef62158620044fc70586200aef410586200267f76d46200be7e76d46200be7d76d46200267c76d46200067f64d46201c67e64d46200067d64d46201c67c64d46203967f63d46201be7e63d46203967d63d46201be7c63d462000e7e61d46200ae7d61d462000e7c61d46200af5f31d462023d7e70d46203977a30d46203977930d462030f7b20d4620004ff7654620004fd7654620004fc76546200067f65546200267e65546200067d65546200267c65546200067f76546200067e76546200067d76546200067c76546200067f64546201b67e64546200067d64546201b67c645462038e7f63546201ae7e635462038e7d63546201ae7c63546200bf77715462000e7e61546200ae7d615462000e7c61546200af5f315462023d7c705462038f7a305462038f7930546202ff7b2054620004ff7650620004fd7650620004fc765062001ebe6450620006bd6450620006df764c620006de764c620006dd764c620006dc764c620006df654c620196de654c620006dd654c620196dc654c620006df644c62018ede644c620006dd644c62018edc644c620007cf724c620007cc724c62008edd624c6200addf714c620087d7714c62000ede614c6200aedd614c62000edc614c6200af5f514c6200af5d514c6200afd6214c620007da704c620007d9704c620066de604c6202f7db204c62000cff764862000ef66148620006f56148620007d53148620005fb7048620005f87048620024fe7694220044fd76942200267e65942200067d6594220045ee7294220005ed729422023e7e769422023e7d769422023e7f64942201567e64942200067
  | 14 => 0x18e9e644c720006dd644c7202f79d644c7200069d644c7202f6dc644c7200c5df714c7200cfd7714c7200c6df614c72000ede614c7200c7d6614c72000ed6614c7200c6dd614c7202f7d5614c720006d5614c72000edc614c7200c75f514c7200c75d514c7200c7cf214c7200c7d6214c7202f7d5214c720045ef7648720066ef76487200476e65487200476d6548720046ef6448720047ae6448720006ed6448720047ad6448720006ad6448720047e7714872000eee614872000eec61487200c76f51487200c76d51487200c7cf31487200c7e631487200c7cd31487203b7e53148720007c53148720005ec70487200a4fd769432027e7f65943200267e65943200067d65943200267c6594320156be6494320006bd649432027d7d76943200067d769432027e7f64943201567e649432027f3e64943201563e64943200067d649432027f3d64943200063d649432027e7c649432027e7f639432012e7e63943203ae7d639432027e7c63943200057d719432014e7e61943200067d619432014e7c61943203af5f31943200075d319432027f6f21943200076d2194320024ff7654320044fc76543200267e65543200067d6554320146be6454320006bd6454320005ef7254320045ec725432026d7d76143200de7d761432026e7f64143201267e641432026f3e64143201263e64143200067d641432026f3d64143200063d641432026e7c641432026e7f631432011e7e63143203a67d631432026e7c63143200057d71143201167e61143200067d61143201167c61143203a75f31143200075d311432026f6f21143200076d21143200df7a701432039f7b101432039f78101432009cfd769032010e7e65903200067d659032001ebe6490320006bd649032000778509032001cff7650320044fc76503200057f75503200dd7c75503200f67e65503200067d655032001ebe6450320006bd6450320005ef7250320045ec72503200077850503200d7b840503200be7e65d96200b5be74d9620005bd74d9620085de73d9620005dd73d96200bcfd75d962001cfe74d9620006be74d962001cbe74d9620004fd74d9620006bd74d9620004bd74d962001cfc74d96200be7f54d9620004ff73d9620014fe73d9620006de73d9620014de73d9620004fd73d9620006dd73d9620004dd73d9620014fc73d96200be7f53d96200067d53d9620006ed72d962027e7e52d962027e7c52d962000cfe71d9620004fd71d962000cfc71d96200be7f51d9620006df31d9620006fa70d9620024ff76596200be7c65596200067f7559620004ff745962001cfe745962001cfc7459620004ff7359620014fe7359620004fd7359620014fc73596200be7f5259620004ff715962000cfe715962000cfc71596200be7f5159620006df3159620044fc70596200be7c505
  | 15 => 0xe7359320006bd7359320006bc7359320006bf5359320006be5359320006bd5359320006bc5359320046bf7259320046be7259320046bd7259320046bc7259320046bf5259320046be5259320046bd5259320046bc5259320046bf3259320046be3259320046bd3259320046bc3259320006bf7159320006be7159320006bd7159320006bc7159320006bf5159320006be5159320006bc5159320006bf31593200069f3159320006be3159320006bd3159320006bc3159320046bf2159320046af2159320046be2159320046bd2159320046bc2159320006bf7059320006bd70593200d6bc7059320006bf5059320006bc5059320006bf3059320006be3059320006bd3059320006bc3059320046bf2059320046be2059320046bd2059320046bc2059320006bf1059320006bc1059320004ff7655320044fe7655320004fd7655320044fc76553200267e65553200067d655532001ebe6455320006bd6455320004ff7558720024fe75587200067e75587200067d7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff7358720014fe7358720004fd7358720014fc7358720046f771587200c6df31587200c6f63158720006f53158720046f72158720046f42158720046fa2058720046f920587200c6f7105872030d7f76d47200267f76d47200247f76d472030e7e76d472030d7d76d47200de7d76d47200047d76d47200267c76d472030e7f64d47201c67e64d472030f3e64d47201c63e64d47200067d64d472030f3d64d47200063d64d472030e7c64d472030e7f63d47201be7e63d47203c67d63d472030e7c63d47200c67f61d472000e7e61d47200c67d61d472000e7c61d47200c75f31d47200c76f21d47200057e70d4720004ff7654720004fd7654720044fc76547202fe7f65547200267e65547200067d65547200267c65547201b6be6454720006bd6454720005fb7054720005f870547202fd7f76547200067f76547200047f76547202fe7e76547202fd7d76547200067d76547200047d76547202fe7c76547202fe7f64547201b67e64547202ff3e64547201b63e64547200067d64547202ff3d64547200063d64547202fe7c64547202fe7f63547201ae7e63547203be7d63547202fe7c63547200df7771547200c67f615472000e7e61547200c67d615472000e7c61547200c75f31547200c76f21547200077b70547200057c7054720007787054720005787054720004ff7650720004fd7650720044fc76507201a67e65507200067d655072001ebe6450720006bd6450720006df764c7202f6de764c720006dd764c7202f6dc764c7202f6df654c720196de654c7202f75e654c7201965e654c720006dd654c7202f75d654c7200065d654c7202f6dc654c7202f6df644c72018ede644c7202f79e644c720
  | 16 => 0x4140157784094140024ff765414001cfe7654140144fd765414001cfc76541400067f65541400267c6554140005bf745414001dbc74541401557e76141400f67e76141401547e761414023e7f64141403de7f631414011e7e63141403de7d631414011e7c63141401273f43141403df3d43141400067f621414026e7c62141400057d71141400067f61141401167e61141401167c61141401273f41141400073d41141403df5f31141400075d31141401557e70141400f77a70141401267f60141401277b401414023f3c40141401277840141401273840141403df7a30141403df7930141400073f65901400073c65901403d5bf73901403d5bd7390140006bf6290140005bd71901400febe61901400febc61901400073f51901400073d51901403cf9f31901400079d319014001dbe709014001fba709014001ebf609014001fbb609014023f3e509014023f3c50901400467f7559720004ff745972001cfe745972001cfc74597200de7f54597200067e54597200de7c5459720004ff7359720014fe7359720004fd7359720014fc73597200de7f53597200067e53597200067d53597200de7c5359720044fc72597200467e52597200467c5259720004ff715972000cfe715972000cfc71597200de7f51597200067e51597200de7c5159720006df31597200de7f50597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067e43597200067d43597200067c43597200467f72597200467e72597200467d72597200467c72597200467f42597200467e42597200467d42597200467c42597200467f32597200467e32597200467d32597200467c32597200067f71597200047f71597200067e71597200067d71597200067c71597200067f41597200067e41597200067c41597200067f31597200065f31597200067e31597200067d31597200067c31597200467f21597200467e21597200467d21597200467c21597200067f70597200067d70597200de7c70597200067f40597200067c40597200067f30597200067e30597200067d30597200067c30597200467f20597200467e20597200467d20597200467c20597200067f10597200067c1059720004ff7559320024fe7559320024fc7559320046bf7459320006bf54593200d6be54593200d6bc5459320004ff7359320014fe7359320004fd7359320014fc73593200d6bf4359320006be4359320006bd43593200d6bc4359320044fc7259320046be4259320046bc4259320004ff715932000cfe715932000cfc71593200d6bf4159320006be41593200d6bc4159320006df3159320046ef21593200d6bf4059320006bf7559320006be7559320006bd7559320006bc7559320006bf7359320006b
  | 17 => 0x57f75585400f57c75585400067f65585400067c65585400e6f4615854025dfb70585400267f76d45400057e76d45400f67e76d45400047e76d45400f67d76d45400f57c76d45400267c76d45400247c76d45400fe7f64d45403fe7f63d45401be7e63d45403fe7d63d45401be7c63d45401c73f43d45403ff3d43d45400067f62d454030e7c62d45400e57d71d45400e67f61d454000e7e61d454000e7c61d45400e73f41d45400e75f31d45400057e70d454028e7f60d45401c77b40d45401c73c40d45401c77840d4540004ff7654540004fe7654540004fc76545400067f65545400267e65545400067d65545400267c65545400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047c76545400fe7f64545403f67f63545401ae7e63545403f67d63545401ae7c63545401b73f43545403f73d43545400067f62545402fe7c62545400e57f71545400f77771545400e67f615454000e7e615454000e7c61545400e73f41545400e75f31545400057c705454028e7f60545401b77b40545401b73c40545401b77840545400e5bc765054000ebc765054000cbc76505400073f65505400073c65505403edbf73505403edbd7350540006bf625054001dbf715054001fb77150540007b7615054000ebe615054000ebc61505400e7b461505400e73f51505400e73d51505400e79f3150540007bb7050540005bc7050540007b8705054001ebf605054001fbb6050540006df764c540006de764c540006dd764c540006dc764c540006df654c5400075f654c5400065f654c540196de654c540006dd654c540196dc654c5400075c654c5401965c654c54018f9e744c5400079d744c5400fedf644c540006df624c5402f6dc624c5400e5df714c5400efd7714c5400e6df614c540007d7614c540006d7614c54000ede614c54000edc614c5400e7d4614c54000ed4614c5400e75f514c5400e75d514c5400e79f414c5400e79d414c5400e7d6214c54028edf604c54018fdb404c54018f9c404c54018fd8404c540004fe76c8540004fd76c8540044fc76c85400067f65c85401867c65c8540046ee62c8540006f761c854000ef461c8540004ff7648540004fe7648540004fc76485400067f654854016e7c6548540007d53148540124fe76941401567f65941400267e65941400067d65941400267c65941400f77b50941401257e76941400067e76941401247e769414023e7f64941403e67f639414012e7e63941403e67d639414012e7c63941401573f43941403e73d43941400067f629414027e7c62941400057d71941400067f619414014e7e619414014e7c61941401573f41941400073d41941403e75f31941400075d31941401257e70941401567f60941401577b409414023f3c409
  | 18 => 0xc40d95401577840d95401567f74d95401567e74d95401567d74d95401567c74d95400067f73d95400067e73d95400067d73d95400067c73d95401567f43d95401567e43d95401567d43d95401567c43d95400067f72d95400067e72d95400067d72d95400067c72d95401567f42d95401567e42d95401567d42d95401567c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d95401567f41d95401567e41d95401567d41d95401567c41d95400067f31d95400065f31d95400067e31d95400067d31d95400067c31d95400067e21d95400067c21d95401567f70d95400f67e70d95401567d70d95401567f40d95401567e40d95401567c40d95400067f30d95400067e30d95400067d30d95400067c30d95400067f10d95400067c10d95400f67c6559540405fb7059540154ff75595400067f7559540144ff7459540006bf7459540004ff7359540014fe7359540004fd7359540014fc7359540004ff7259540044fc7259540004ff715954000cfe715954000cfc71595400f67f5159540006df3159540404ff7059540006fb70595400f67c50595401557e76195400f67e76195401547e76195401267f64195400067f63195400067e63195400067d63195400067c63195401273f43195400073d43195400057d71195400067e61195400067c61195401273f41195400075f31195401267f60195401277b40195401273c40195401277840195400067f65d89400067c65d8940024fe75d8940004fd75d8940024fc75d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400b6bf43d8940006bd43d89400b6ee42d89400b6ed42d894000cfe71d8940004fd71d894000cfc71d89400b6bf41d8940006df31d89400b6bc40d89400f57e75989400057d75989400067f65989400067c6598940006ef629894009df970989400057f75589400f57c75589400067f65589400067c6558940005df73589400eddc7358940005f771589400e5f471589400d5fb70589400067f65189400067c6518940046ee6218940006ed6218940004fe7694940004fd7694940044fc76949400067f65949400267c6594940004ff7654940004fe7654940004fc76549400067f65549400267c6554940005bf745494001dbc7454940005df73549400eddc7354940005fb7054940005f8705494000cfe76d85400067f65d85400067c65d85400e6f661d85400067f75d8540024fe75d8540004fd75d8540024fc75d85400067c75d854000cfc74d8540004ff73d8540014fe73d8540004fd73d8540014fc73d8540044fe72d8540004fd72d85400e6f641d8540056f541d85400e6df31d85400e6f631d8540006f531d85400e6f421d854001cfd70d85400e6f710d8540
  | 19 => 0x46401b73f42546400073d425464010f77715464000e7e61546400fe7d615464000e7c61546400ff3e41546400ff3c41546400ff5f315464023d7c70546402667e60546401b73f40546401b77b40546401b7784054640006df764c640006de764c640006dd764c640006dc764c640006df654c640196de654c640006dd654c640196dc654c6400079f744c64018f9c744c6400e6dd644c6402f6de624c640006dd624c64018f9f424c6400079d424c6400fddf714c640107d7714c64000ede614c6400fedd614c64000edc614c6400ff5f514c6400ff5d514c6400ff9e414c6400ff9c414c6400ffd6214c640266de604c64018f9f404c64018fdb404c64018fd8404c640044ff76c8640004fe76c8640004fd76c864001dbe74c8640005bd74c8640046ee62c8640006ed62c8640007ad42c8640004ff7648640004fd7648640004fc7648640005bf744864001dbc7448640046ee6248640006ed6248640007ad4248640007d5314864001cff7694240024fe769424001cfd76942400267e65942400067d659424001dbe7494240005bd749424010f7b5094240157bb409424023e7f769424023e7e769424023e7d769424023e7c769424023f3e749424023f3d749424023e7f639424012e7e639424041e7d639424023e7c639424027e7e62942400067d62942401573f42942400073d42942400057d719424014e7e61942400067d619424023e7c61942404273e41942401573c419424041f5f31942400075d319424023e7e609424023f3f40942401577b40942401573b409424023f784094240404ff7654240147bb405424023e7f761424023e7e761424023e7d761424023e7c761424023f3e741424023f3d741424023e7f631424011e7e631424040e7d631424023e7c631424026e7e62142400067d62142401273f42142400073d42142400057d71142401167e61142400067d611424023e7c61142404173e41142401273c411424040f5f31142400075d311424023f7a701424023e7e601424023f3f40142401277b401424023f78401424023f7a301424040f793014240024fe76d95400f67e65d9540154ff74d954001cfe74d9540154fd74d954001cfc74d95401567f54d95401567d54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400f67f53d95400067e53d95400067d53d95400f67c53d9540044fe72d9540004fd72d95400f67f52d95400f67c52d954000cfe71d9540004fd71d954000cfc71d95400f67f51d95400067e51d95400f67c51d9540006df31d954001cfd70d95400f67f50d95401257e76d95400247e76d95400067f63d95400067e63d95400067d63d95400067c63d95401573f43d95400073d43d95400057d71d95400067e61d95400067c61d95401573f41d95400075f31d95401577b40d95401573
  | 20 => 0x16f7a604845010e7e65d9640125fa70d9640144fd75d9640006bd74d96401567e54d96401567c54d9640004ff73d9640014fe73d9640004fd73d9640014fc73d9640044fe72d9640004fd72d964010e7f52d9640156bf42d964000cfe71d9640004fd71d964000cfc71d964010e7f51d9640006df31d9640124fe70d9640006fa70d9640024ff765964010e7c65596400067f75596401467f54596401467d5459640004ff7359640014fe7359640004fd7359640014fc7359640004ff7259640044fc7259640146bf4259640004ff715964000cfe715964000cfc715964010e7f5159640006df315964001cfc705964010e7c5059640075fa70d8a4010d7e7598a400057d7598a40006ef6298a40005df7358a40105dc7358a40004ff7558a40024fe7558a40024fc7558a40004ff7358a40006df7358a40004df7358a40014fe7358a40004fd7358a40014fc7358a40006dc7358a40014dc7358a4009eee4258a4009eed4258a40004ff7158a4000cfe7158a4000cfc7158a40006df3158a40046ee6218a40006ed6218a400b5fa7018a40044ff7694a40004fe7694a40004fd7694a4001dbe7494a40005bd7494a40004ff7654a40004fd7654a40004fc7654a400067f6554a400267c6554a40005df7354a40105dc7354a40005fb7054a40005f87054a40044bf7650a40006bf6550a40006bd6550a4043ebf6350a4043ebd6350a4001dbf7250a4001faf7250a40046be6250a40007ae6250a40007ad6250a40046bc6250a400fdbe7150a400fdbc7150a4043f9f3150a40005bf7050a40007bb7050a40007b87050a4001ebe6050a4001fba6050a400fef661d86402b5fa70d864000cff765864001dbc74586400fef461586400ffb64158640004ff7558640024fe7558640024fc7558640004ff7358640014fe7358640004fd7358640014fc7358640004ff7258640044fc7258640036bf4258640006bd42586400febe41586400fef64158640036f541586400febc41586400fedf315864001cfc7058640036bf40586400fef410586400267f76d464010e7e76d464010e7d76d46400267c76d46401c73e74d464010f3d74d46404367f63d46401be7e63d46404367d63d46401be7c63d464030e7e62d46400067d62d46401c73f42d46400073d42d464000e7e61d46400fe7d61d464000e7c61d46400ff3e41d46400ff3c41d46400ff5f31d464023d7e70d46402667e60d46401c73f40d46401c77b40d46401c77840d4640004ff7654640004fd7654640004fc76546400067f65546400267e65546400067d65546400267c6554640005bf745464001dbc74546400067f76546400067e76546400067d76546400067c76546400073f74546401b73c745464042e7f63546401ae7e635464042e7d63546401ae7c63546402fe7e62546400067d625
  | 21 => 0xe21584501167621584501167c21584500067e70584501167c70584500067f40584500067c40584500067f30584500067e30584500067d30584500067c30584501167f10584501167c10584501167410584501a57f765045023d7e76504501a57d765045023d7c76504501157f74504501273e64504501a73d64504504657f735045011d7e73504504657d735045011d7c73504500057f725045026d7c72504501273f42504500073d42504501157f71504501167f61504501177661504501167d61504501a77561504500067561504501277741504501173e41504501173c41504501177441504501175f31504500057f70504500077b70504500057b705045023d7c705045000778705045000578705045014e7e60504501a77a60504501273f40504501975f764c4501975e764c4501975d764c4501975c764c4500075f744c45045f5e744c4500075d744c45045f5c744c4501975f644c4501975e644c4501975d644c4501975c644c4500075f724c4500075e724c4500075d724c4500075c724c4501975f624c4501975e624c4501975d624c4501975c624c45045f5f424c4500075e424c4500075d424c45045f5c424c4501175f714c4501155f714c45011f57714c4501175f614c4501165f614c4501175e614c45011756614c4501175d614c4501165d614c45019755614c45000655614c4501175c614c4501175f414c4501175e414c4501175d414c4501175c414c4501175e214c45011756214c4501175c214c4500075f704c4500075e704c4500075d704c4500075c704c4501975e604c45014e5e604c4501975a604c45045f5f404c45045f5c404c4501175f104c4501175c104c45026d7f76c845023d7e76c84501857d76c845023d7c76c845026d7f74c84501257e74c84500057d74c845026d7c74c845026d7f73c845011d7e73c84504557d73c845026d7c73c84501157e72c845026f6e62c84501876d62c845026f6e42c84500076d42c84501157d71c84501167f61c84501167d61c84501175f31c84501175d31c84501176e21c84501177621c84501176c21c845023d7e70c84500057d70c845014e7e60c84501877a60c845016d7f764845023d7e764845016d7d764845023d7c76484500057f74484501257e74484500057d74484501257c744845044d7f734845011d7e734845044d7d734845011d7c73484501157f724845016f6e624845016f6d62484500076e42484500076d42484501157f71484501167f61484501177661484501167d614845016f7561484500067561484501175f31484501177631484501175d314845044775314845000755314845026f7721484501176e21484501176c21484501177421484500057f70484500077b70484500057b704845023d7c704845000778704845000578704845014e7e6048450
  | 22 => 0x455000e7c765455000c7c76545500067f64545501b67e64545501b67c64545504967f63545501ae7e63545504967d63545501ae7c63545500067f62545502fe7c62545500257f71545500277771545501367f615455000777615455000677615455000e7e615455000e7c61545501377461545501375f31545500077b70545500057c70545500077870545500267f60545500277b6054550004ff7650550004fe7650550004fc7650550006df764c550006de764c550006dd764c550006dc764c55014edf654c550006df644c55018ede644c55018edc644c550006df624c5502f6dc624c550135df714c55013fd7714c550136df614c55000ede614c55000edc614c5501375f514c5501375d514c550137d6214c550296df604c550197db504c5501975c504c550197d8504c550004fe76c8550004fd76c8550044fc76c8550004ff7648550004fe7648550004fc7648550007d531485500067f64941501567e64941501567c649415048e7f639415012e7e639415048e7d639415012e7c63941500067f629415027e7c62941500057d71941500067f619415014e7e619415014e7c619415048f5f31941500075d31941500257e70941500277a70941500267f60941500277b609415026d7f769085023d7e76908501f57d769085023d7c76908501257d749085026d7f739085011d7e73908504857d739085026d7c739085026d7e729085026f6e62908501f76d629085026f3f42908501276f429085026f6c42908501157e71908500057d71908501157c719085047f5f319085023d7e709085026f7a70908500057a70908500057d709085026f79709085000579709085027e7e60908501f77a60908501dd7f765085023d7e76508501dd7d765085023d7c765085026d7f74508501273e64508501df3d64508504757f735085011d7e73508504757d735085011d7c73508501273f435085046f3d43508501257f72508501df6e62508501df6d62508501276f425085026f3e425085026f3c42508501276c42508500057f71508501157e71508501157c71508501273f415085046f5f31508500057f705085023d7c70508501567e60508501df7a60508501273c40508500067f74584500067e74584500067d74584500067c74584500067f73584500067e73584500067d73584500067c73584500067f43584500067e43584500067d43584500067c43584500067f72584500067e72584500067d72584500067c72584500067f42584500067e42584500067d42584500067c42584500067f32584500067e32584500067d32584500067c32584500267f71584500267771584501167f41584501167e41584501167641584501167c41584501167f31584501165f31584501167e31584501167631584501167d31584500067531584501167c31584501167
  | 23 => 0x75e724c6500075d724c6500075c724c6500075f624c6500075e624c6500075d624c6500075c624c6504c75f424c6500075e424c6500075d424c6504c75c424c65014f5f714c65014d5f714c65012f57714c65014f5f614c65014f5e614c65014f5d614c65014e5d614c65014f5c614c65014f5f414c65014f5e414c65014f5d414c65014f5c414c65014f5e214c65014f56214c65014f5c214c6500075f704c6500075e704c6500075d704c6500075c704c6501165e604c6504c75f404c6504c75c404c65014f5f104c65014f5c104c65027d7f76c865023d7e76c86500057d76c865023d7c76c865027d7f74c86501557e74c86500057d74c865027d7c74c865027d7f73c865012d7e73c86504bd7d73c865027d7c73c865014d7e72c865027f6e62c86500076d62c865027f6e42c86500076d42c865014e7d61c865014f5f31c865014f5d31c865014f6e21c865014f7621c865014f6c21c865023d7e70c86500057d70c86500057f764865023d7e76486500057d764865023d7c76486500057f74486501557e74486500057d74486501557c74486504b57f734865012d7e73486504b57d734865012d7c734865014d7f72486500076e62486500076d62486500076e42486500076d424865014e7d614865014f5f314865014f76314865014f5d31486504af75314865000755314865027f77214865014f6e214865014f6c214865014f7421486500057f704865023d7c704865001cfe76d9150146be64d915001cfc75d9150146be54d915010ebd54d9150004ff73d9150014fe73d9150004fd73d9150014fc73d9150044fe72d9150004fd72d9150146bf42d915000cfe71d9150004fd71d915000cfc71d915010e7f51d9150006be41d9150146bc41d9150006df31d9150024fd70d915010e7c50d9150146bf40d9150146bc64591504a5fb705915001cfe74d8950004fd74d895001cfc74d8950004ff73d8950014fe73d8950004fd73d8950014fc73d89500beee52d89500beed52d895000cfe71d8950004fd71d895000cfc71d89500be7f51d8950006df31d89500be7c50d8950145be7498950005bd7498950006ef62989500a5f97098950005df735895013ddc73589500ddfb7058950046ee6218950006ed6218950004fe7690950004fd7690950044fc7690950004ff7650950004fe7650950004fc7650950006bf645095001ebc645095000cfe76d8550136f661d85500067f75d855000cfc75d855000c7c75d855001cfe74d8550004fd74d855001cfc74d8550004ff73d8550014fe73d8550004fd73d8550014fc73d8550044fe72d8550004fd72d85501367f51d8550136f651d855005ef551d8550136df31d8550024fd70d855005e7c50d8550136f710d8550005bf7458550145bc7458550136f4615855049dfb70585501357c765
  | 24 => 0xf7650a5023d7e7650a500057d7650a5023d7c7650a500073f6450a501573c6450a504dd7f7350a5012d7e7350a504dd7d7350a5012d7c7350a501573f4350a504d73d4350a501557f7250a501576f4250a5027f3e4250a5027f3c4250a501576c4250a500057f7150a5014d7e7150a5014d7c7150a501573f4150a504d75f3150a500057f7050a5023d7c7050a501573c4050a501557e74d86500057d74d865023d7c74d865023e7f64d86500067e64d86500067d64d865023e7c64d865023d7f73d865012d7e73d86500057d73d865023d7c73d865023e7f63d86500067e63d86500067d63d865023e7c63d865027d7e72d86500057d72d865023e7f62d86500067e62d86500067d62d865023e7c62d865014d7d71d865014e7e61d865023f7661d865023e7c61d865014f5f31d865023d7e70d865023f7a70d86500057a70d865023f7a60d865014d7f76586500057f74586501557e74586501557c74586500067f64586500067e64586500067d64586500067c64586500057f735865012d7e73586500057d735865012d7c73586500067f63586500067e63586500067d63586500067c63586500057f725865027d7c72586500067f62586500067e62586500067d62586500067c625865023f77615865014e7e615865014e7c615865023f74615865014f5f315865023d7c705865003e7e605865003f7a605865023f7410586500067f74586500067e74586500067d74586500067c74586500067f73586500067e73586500067d73586500067c73586500067f43586500067e43586500067d43586500067c43586500067f72586500067e72586500067d72586500067c72586500067f42586500067e42586500067d42586500067c42586500067f32586500067e32586500067d32586500067c325865014e7f415865014e7e415865014e7c415865014e7f315865014e5f315865014e7e315865014e7d315865014e7c315865014e7e215865014e7c215865003e7e705865014e7c70586500247c70586500067f40586500067c40586500067f30586500067e30586500067d30586500067c305865014e7f105865014e7c105865014e7410586500057f765065023d7e76506500057d765065023d7c765065014d7f74506501573e64506500073d64506504cd7f735065012d7e73506504cd7d735065012d7c73506500057f725065027d7c72506501573f42506500073d425065014d7f715065014e7d615065015777415065014f3e415065014f3c415065014f74415065014f5f31506500057f705065023d7c70506501167e60506501573f40506500075f764c6500075e764c6500075d764c6500075c764c6500075f744c6504c75e744c6500075d744c6504c75c744c6500075f644c6504c75e644c6500075d644c6504c75c644c6500075f724c650
  | 25 => 0xc650044ff76c8650004fe76c8650004fd76c865027d7f75c86500257e75c86500057d75c86500257c75c8650046ee62c8650006ed62c8650004ff7648650004fd7648650004fc76486500057f75486500257e75486500057d75486500257c7548650046ee6248650006ed6248650007d531486501557d74d92501567e64d925023f3e64d92501563e64d925023e7c64d925023d7f73d925012d7e73d92500057d73d925023d7c73d925027d7e72d92500057d72d92501573f42d925014d7e71d92500057d71d925023d7c71d92500075f31d925023d7e70d925023f7a70d92500057a70d925023f7a60d92501557f765925023f3f64592501567e64592501567c645925023f3c64592501563c64592500057f735925012d7e73592500057d735925012d7c73592501573f43592500073d43592500057f725925027d7c72592501573c42592500057f715925014d7e715925014d7c71592501573f41592500075f315925023d7c70592500f67e60592500f77a605925023f3c40592501557e74d8a5023f3e74d8a501553e74d8a500057d74d8a5023f3d74d8a500053d74d8a5023d7c74d8a5023e7f64d8a500067d64d8a5023d7f73d8a5012d7e73d8a5023f5e73d8a5012d5e73d8a500057d73d8a5023f5d73d8a500055d73d8a5023d7c73d8a5023e7f63d8a500067d63d8a5014d7e71d8a500057d71d8a5023d7c71d8a500075f31d8a5023d7e70d8a5023f7a70d8a500057a70d8a5023f7a60d8a500057d7698a501557e7498a5027f3e7498a501553e7498a500057d7498a5027f3d7498a500053d7498a5027d7c7498a5027d7f7398a5012d7e7398a500057d7398a5027d7c7398a5027e7f6298a5023f6f6298a500066f6298a5014d7e7198a500057d7198a5014d7c7198a500075f3198a5026e7e6098a500df7a6098a500057f7458a501557e7458a501557c7458a500067f6458a500067d6458a500057f7358a5012d7e7358a500057d7358a5012d7c7358a500067f6358a500067d6358a5023f6f6258a5027e7e6258a500057f7158a5014d7e7158a5014d7c7158a500075f3158a500a67e6058a500a77a6058a501557e7418a500057d7418a5023d7c7418a5023d7f7318a5012d7e7318a500057d7318a5023d7c7318a5027d7e7218a5023e7f6218a5023f6e6218a5027e7d6218a5023f6d6218a5014d7e7118a500057d7118a5023d7c7118a500075f3118a5023d7e7018a5023f7a7018a500057a7018a5023f7a6018a5027d7f7690a5023d7e7690a500057d7690a5023d7c7690a501573e6490a500073d6490a5027d7f7390a5012d7e7390a504ed7d7390a5027d7c7390a5027d7e7290a5027f3f4290a501576f4290a5027f6c4290a5014d7e7190a500057d7190a5014d7c7190a504e75f3190a5023d7e7090a500057d7090a500057
  | 26 => 0x57d7094a5027f797094a500267e6094a500277a6094a500447f7654a500057f7454a501557e7454a501557c7454a500067d6454a505157f7354a500075f7354a500055f7354a5012d7e7354a505157d7354a5012d7c7354a5050f5c7354a5012d5c7354a5050e7f6354a5050e7d6354a500257f7254a500276f7254a500467e6254a500076e6254a500466e6254a500076d6254a500467c6254a500057f7154a5014d7e7154a5014d7c7154a5050f5f3154a500057f7054a500077b7054a50007787054a500267e6054a500277a6054a50044ff7690a50004fe7690a50004fd7690a5027d7f7590a500257e7590a500057d7590a500257c7590a5001ebe6490a50006bd6490a50004ff7650a50004fd7650a50004fc7650a500057f7550a500257e7550a500057d7550a500257c7550a5001ebc6450a501573e5450a500073d5450a5014ef661d8650505fa70d865000cff76586500257c755865014ef4615865014f7651586500067d7558650004ff745865001cfe745865001cfc745865003e7f54586500067e54586500067d545865003e7c5458650004ff7358650014fe7358650004fd7358650014fc735865003e7f53586500067e53586500067d535865003e7c5358650004ff7258650044fc725865003e7f52586500067e52586500067d525865003e7c525865014e7f515865014e7e515865014ef6515865003ef5515865014e7c515865014edf3158650024fc705865003e7f505865014ef4105865014d7f765465000e7f765465000c7f76546500057f74546501557e74546501557c74546501b67e64546500067d64546501b67c64546504fd7f735465012d7e73546504fd7d735465012d7c73546504f67f63546501ae7e63546504f67d63546501ae7c63546500057f725465027d7c72546502fe7e62546500067d62546500257f715465002777715465000e7e615465014f76615465014e7d615465000775615465000675615465000e7c615465014f5f31546500057f70546500077b70546500077870546500267e60546500277a6054650004ff7650650004fd7650650004fc76506500057f75506500257e75506500057d75506500257c755065001ebe6450650006bd6450650006df764c650006de764c650006dd764c650006dc764c6500075f754c6501975e754c6500075d754c6501975c754c650136dd654c65018ede644c650006dd644c65018edc644c6501975f544c6504c75e544c6500075d544c6501975c544c6502f6de624c650006dd624c6501975f524c6500075e524c6500075d524c6501975c524c65014ddf714c65012fd7714c65000ede614c65014edd614c65000edc614c65014f5f514c65014f5e514c65014f5d514c65014f5c514c65014fd6214c650116de604c6501975f504c650197db504c650197d8504
  | 27 => 0x7424c5212f7d6424c521007c6424c521007d5424c521007c5424c5212f7d4424c521007d7704c521007d6704c521007d5704c521007d4704c52154fd7504c52154fd4504c521547d7404c521547d4404c52116d7e75d81210057d75d8121007d531d8121024fe75d81210067e75d81210247e75d8121004fd75d81210067d75d81210047d75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d8121044fd71d81210c67f51d81210c67d51d81210c6df31d81210c6dd31d8121006fb50d8121006f850d81210c6fa10d8121007d53198121006fb60981210057f755812116d7c7558121005bf7458121165bc7458121005df735812115ddc7358121007d53158121007d53118121006f96018121024fe7518121004fd7518121024fc751812101cfe7418121004fd741812101cfc7418121004ff7318121014fe7318121004fd7318121014fc7318121066ed7218121044fd71181210667f51181210667d5118121066df3118121066dd3118121006fb5018121006f85018121066f91018121156be64d925053dfa70d925001cff76592500257c7559250156bc64592501573e54592501567e5459250156be54592501563e54592500f6bd54592501567c5459250004ff7359250014fe7359250004fd7359250014fc7359250156bf4359250006bd4359250004ff7259250044fc72592500f67f5259250156bc4259250004ff715925000cfe715925000cfc71592500f67f5159250156bf4159250006df3159250024fc7059250156bc40592501557f765525001e7f765525001c7f76552500257f74552500273f745525001e7e64552501573e645525001e3e64552500073d645525001e7c64552505357f735525012d7e73552505357d735525012d7c73552500057f725525027d7c72552501573f42552500057f715525014d7e715525014d7c715525052f5f31552500057f70552500077b70552500077870552500267e60552500277a6055250155be74d8a50005bd74d8a5012dde73d8a50005dd73d8a5007dfa70d8a50155be7498a50005bd7498a50006ef6298a50004ff7458a5001cfe7458a5001cfc7458a500a67f5458a500067d5458a50004ff7358a50014fe7358a50004fd7358a50014fc7358a500a67f5358a500067d5358a500a6ee5258a500a6ed5258a5027e7c5258a50004ff7158a5000cfe7158a5000cfc7158a500a67f5158a50006df3158a50046ee6218a50006ed6218a500bdfa7018a501557e7494a500057d7494a5027d7c7494a5027d7f7394a5012d7e7394a505257d7394a5027d7c7394a500257e7294a500276e7294a5027f6e6294a5027e7d6294a500076d6294a5014d7e7194a500057d7194a5014d7c7194a5051f5f3194a5027f7a7094a50
  | 28 => 0x95212fe7e52595212fe7c52595211fcff7159521006f771595211fe7f51595211fe7d51595211fedf31595211fedd3159521004ff7059521006fb7059521004fb7059521004fc7059521006f87059521004f8705952116e7c505952101cfe76d9121166be64d9121024fe75d9121004fd75d9121024fc75d9121006bf54d9121166bc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d9121166bf43d9121006bd43d912100cfd72d9121166bf42d9121044ff71d9121044fd71d91211e67f51d91211e67d51d91211e6bf41d91211e6bd41d91211e6df31d91211e6dd31d9121004fe70d9121004fd70d9121166bc40d9121166bc645912156def7259121004ff7559121024fe7559121024fc75591211e4ff7459121006bf7459121004ff7359121014fe7359121004fd7359121014fc735912156cff7259121006ef72591211ccff7159121006f771591211ce7f51591211ce7d51591211cedf31591211cedd3159121004ff7059121004fc7059121004ff7655121004fe7655121004fd7655121004fc76551210267e65551210067d6555121024ff765492100cfe76549211fcfd765492100cfc76549210067f65549210267c6554921005df735492115ddc7354921005f7715492100df47154921047e42154921565ee7690921046ee76909211cded749092101eee649092101eec649092100dee719092100dec7190921046ef6190921047e761909211e76f51909211e76d51909211e7cf31909211e7e631909211e7cd319092155fe53190921005ed709092101cff765092100cfe76509211ccfd765092100cfc7650921006bf645092101ebc6450921047ac4250921005f7715092100df4715092100dec765092101eec765092100cec7650921045ef7450921047af7450921007af645092101eee645092101eec6450921167ac6450921167ae5450921007ad5450921167af4350921557ad4350921007e7715092100dee715092100dec71509211cfe47150921046ef6150921047e761509211cf6f51509211cf6d51509211cfaf41509211cfad41509211cfcf31509211cfe631509211cfcd3150921557e53150921005ef7050921167ac405092115fd7764c521016d7764c52115fd4764c521016d4764c521007d7754c52154fd6754c521007d5754c52154fd4754c521007d7654c52154fd6654c521007d5654c52154fd4654c521007d7744c521547d6744c521007d5744c521547d4744c521007d7644c521547d6644c521007d5644c521547d4644c52154fd7544c521547d6544c521007d5544c521547d4544c521007d7724c521007c7724c5212f7d6724c52115fd5724c5212f7d4724c521007c4724c52100fd7624c52100ed7624c52100fc7624c52154fd7524c5212f7d6524c521007d5524c5212f7d4524c521547d
  | 29 => 0x6dc7359721014dc73597211867f53597210067d535972100cfe725972100cfc72597210467e52597210467c52597211fe7f51597211fe7d51597211fedf31597211fedd3159721004ff7059721004fc70597211867c5059721004ff7559321024fe7559321024fc7559321046bf745932117ebe5459321004ff7359321014fe7359321004fd7359321014fc735932117ebf4359321006bd435932100cfe725932100cfc7259321046be4259321046bc42593211ce7f51593211ce7d51593211cebf41593211cebd41593211cedf31593211cedd3159321004ff7059321004fc705932117ebc4059321004ff7655321044fe7655321004fd7655321044fc76553210267e65553210067d655532101ebe6455321006bd6455321045ef7650b21586ef7650b21047af7450b21047af6450b2101eee6450b21046ec6450b21047ac6450b2117fae5450b21007ad5450b2117faf4350b2157fad4350b2100dee7150b2100dec7150b211cf6f5150b211cf6d5150b211cfaf4150b211cfad4150b211cfcf3150b211cfcd3150b21005ef7050b2117fac4050b21024fe7598321004fd7598321024fc759832101cfe7498321004fd749832101cfc7498321004ff7398321014fe7398321004fd7398321014fc739832100cfe7298321046ee729832100cee72983210ae7f51983210ae7d51983210aedf31983210aedd3198321046fa7098321006fa3098321006f93098321046ef2098321046fb2098321046f820983210aef91098321004ff75583210067f75583210047f7558321024fe7558321024fc75583210067c75583210247c7558321004ff745832101cfe745832101cfc7458321004ff7358321006df7358321004df7358321014fe7358321004fd7358321014fc7358321006dc7358321014dc735832100cfc725832108e7f515832108e7d515832108edf315832108edd3158321046fb7058321006fa3058321006f93058321046fb2058321046f8205832108efa1058321024fe76d952116e7e65d952101cfe74d9521004fd74d952101cfc74d9521004ff73d9521014fe73d9521004fd73d9521014fc73d952100cfd72d952116e7f52d9521044ff71d9521044fd71d95212167f51d95212167d51d9521216df31d9521216dd31d9521004fe70d9521004fd70d952116e7c50d952116e7c6559521005bf7459521165bc7459521005df735952115ddc7359521575ef7259521005fb7059521005f87059521214ff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc745952116e7f5459521004ff7359521006df7359521004df7359521014fe7359521004fd7359521014fc7359521006dc7359521014dc735952116e7f53595210067d5359521574ff7259521006ef725
  | 30 => 0xd7490931565de72909312f79f429093118fcf42909312f7cc42909311e5df719093100dde71909311e7d6719093100dd671909311e5dd71909312f7d57190931005d5719093100ddc71909311e6df61909311efd761909311e75f51909311e75d51909311e7cf21909311e7d62190931005de7090931005dd7090931005df7650931005de7650931005dd7650931005dc7650931005df7550931195de7550931005dd7550931195dc75509311e5df745093118f9e64509310079d645093118f9e54509310079d545093156ddf725093118fcf42509312f79e42509312f79c425093118fcc42509311cddf715093100dde715093100ddc71509311cedf61509311d7d761509311cf5f51509311cf5d51509311cf9f41509311cf9d41509311cfd62150931005df7050931005dc705093118f9c4050931195de75d81310075e75d81311955e75d8131005dd75d81310075d75d81310055d75d8131195dc75d813118dde74d8131005dd74d813118ddc74d8131006df64d8131006dd64d81312f5de72d8131005dd72d8131015df71d8131015dd71d81315a6df61d81315b7d761d81315a75f51d81315a75d51d81315a7d621d81315a7da10d81315a7d910d81315addd7698131195de7598131005dd7598131195dc759813118dde7498131005dd749813118ddc74981312f5de7298131005dd7298131006de6298131006dc6298131595dd7198131007d5719813102dd57198131596df619813104fd761981315975f51981315975d5198131597d6219813158dde7098131006df6098131007db6098131005df75581310075f75581310055f7558131195de7558131195dc75581310075c75581311955c7558131005df74581310079f74581310059f745813118dde745813118ddc74581310079c745813118d9c7458131006df6458131006dd6458131005df7258131007cf7258131005cf72581312f5dc7258131007cc7258131005cc72581315addf7158131007d7715813104dd771581315aedf615813102fd761581315af5f51581315af5d51581315afd62158131007db6058131006de60581315a5de7618131195de7518131005dd7518131195dc751813118dde74181310079e741813118d9e7418131005dd74181310079d74181310059d741813118ddc74181312f5de7218131005dd7218131006de6218131006dc6218131015df711813100dde7118131015dd711813100ddc711813158edf611813159fd7611813158f5f511813158f5d511813158fd62118131595de7018131006df6018131007da6018131006dd6018131007d9601813158fda101813158fd910181310467f7559721004ff745972101cfe745972101cfc74597211867f5459721004ff7359721006df7359721004df7359721014fe7359721004fd7359721014fc7359721
  | 31 => 0x5131195de75d8931005dd75d8931195dc75d893118dde74d8931005dd74d893118ddc74d8931015df71d89315efd771d8931015dd71d89315dedf61d89315efd761d89315df5f51d89315df5d51d89315dfcf21d89315dfd621d89315dfcd21d8931005de70d8931005dd70d89315e5dd7698931195de7598931005dd75989312f5dc7598931006de6598931006dc659893118dde7498931005dd74989312f5dc7498931006df6498931006dd64989315c5de72989312f6df6298931007cf62989315d5dd71989312f7d5719893115dd571989315d6df6198931177d761989315d75f51989315d75d51989315d7d62198931005de7098931005dd7098931005df7558931195de7558931195dc7558931005df745893118dde745893118ddc7458931007cf62589312f6de62589315e5df7158931007d77158931175d771589315e6df615893115fd761589315e75f51589315e75d51589315e7d62158931005df7058931005dc70589315ddde7618931195de75189312f75e75189311955e7518931005dd75189312f75d75189310055d75189312f5dc7518931006de6518931006dc651893118dde74189312f79e741893118d9e7418931005dd74189312f79d74189310059d74189312f5dc7418931006df6418931006dd64189315d5de72189312f6df62189312f7ce62189312f6dd6218931007cd6218931015df711893100dde7118931015dd71189312f7d5711893100ddc71189315c6df61189315cfd761189315c75f51189315c75d51189315c7cf21189315c7d621189315c7cd2118931005de70189312f7da7018931005da7018931005dd70189312f7d97018931005d970189312f5df7694931005de7694931005dd76949312f5dc76949311fddd759493118dde7494931005dd74949312f5dc74949315bdde72949312f75f5294931197cf52949312f7cc5294931215df719493100dde7194931217d6719493100dd67194931215dd71949312f7d57194931005d5719493100ddc7194931216df619493121fd761949312175f51949312175d5194931217d62194931005de7094931005dd70949311975c5094931005df7654931006df7654931004df7654931005de7654931005dd7654931005dc7654931006dc7654931004dc7654931215df75549311975e65549310075d6554931005df745493118dde745493118ddc74549311975f54549310075d5454931575df7254931197cf52549312f75e52549312f75c5254931197cc52549311fddf715493100dde715493100ddc71549311fedf6154931207d761549311ff5f51549311ff5d51549311ffd62154931005df7054931005dc70549311975c50549312f5df7690931005de7690931005dd76909312f5dc76909312f5df7590931195de7590931005dd75909312f5dc75909311cdd
  | 32 => 0x4ff73d8141014fe73d8141004fd73d8141014fc73d8141044fe72d8141004fd72d814101cfd71d814128e7f51d814128e7d51d814128edf31d814128edd31d8141006fb50d8141006f850d814125efa40d814128efa10d8141006fb60981410057f75581411a57c755814119dde7318141005dd7318141006f96018141024fe7518141004fd7518141024fc751814100cfd7418141266bd7418141004ff7318141014fe7318141006de7318141014de7318141004fd7318141006dd7318141004dd7318141014fc7318141044fe7218141004fd72181412b6bf4218141006bd421814101cfd71181412667f51181412667d5118141266be4118141266bc4118141266df3118141266dd3118141006fb5018141006f850181412b6bf40181412b6f94018141266f91018141655de76d9531635dd75d9531196de65d95311975e65d95311965e65d9531196dc65d953118dde74d9531005dd74d953118ddc74d95312f5de72d9531005dd72d9531015df71d953100dde71d9531015dd71d953100ddc71d953163edf61d953164fd761d953163f5f51d953163f5d51d953163fd621d9531005de70d9531005dd70d95311975c50d9531645df765953163ddf75595310075f6559531196de6559531196dc65595311975c6559531005df745953118dde745953118ddc7459531005df72595312f5dc72595311975f5259531635df7159531007d771595311bdd77159531636df61595311afd761595316375f51595316375d5159531637d62159531005df7059531005dc70595311975c505953162dde76d9131195de75d9131005dd75d9131195dc75d9131605dd74d913118ede64d913118f9e64d913118edc64d91312f5de72d9131005dd72d9131015df71d913100dde71d9131015dd71d913100ddc71d9131616df61d9131627d761d91316175f51d91316175d51d91316179f41d91316179d41d9131617d621d9131005de70d9131005dd70d913118f9c40d913161ddf7659131005df7559131195de7559131195dc7559131615df74591310079f645913118ede645913118edc645913118f9c6459131005df72591312f5dc725913118f9f4259131605df7159131007d7715913160dd77159131606df615913119fd761591316075f51591316075d51591316079e41591316079c4159131607d62159131005df7059131005dc705913118f9f4059131005df7655131005de7655131005dd7655131005dc76551315fddf75551315f5df74551311979f545513118f5e545513118f5c545513118f9c5455131005df72551312f5dc72551311975f525513118f9f425513122ddf715513100dde715513122ddd715513100ddc715513122edf6155131237d7615513122f5f515513122f5d515513122fd62155131005df7055131005dc70551311975c505
  | 33 => 0xc72181510067f42181510067e42181510067d42181510067c42181510067f32181510067e32181510067d32181510067c321815123e7f71181510247d71181511167f41181511167e41181511167d41181511167c41181511167f31181511165f31181511167e31181511167d31181511165d31181511167c31181511167f21181511167e21181511167d21181511167c21181510067f40181510067b401815123e7c40181510067840181510067f301815123e7e30181510067a30181510067d301815100679301815123e7c30181511167f10181511167d101815111679101815123e7c1018151024fe76d95411a67e65d954122cfd75d954100cff74d954100cfd74d954166e7f54d954166e7d54d9541004ff73d9541014fe73d9541004fd73d9541014fc73d9541044fe72d9541004fd72d954166ebf42d954101cff71d954101cfd71d95415fe7f51d95415fe7d51d95415fedf31d95415fedd31d9541004fe70d9541004fd70d95411a67c50d9541024ff76595411a67c65595415f5bf74595411c5f77159541005fb7059541005f870595415fcff75595410067f75595415f4ff7459541006bf74595411b67e54595411b67c5459541004ff7359541014fe7359541004fd7359541014fc7359541004ff7259541044fc72595411a67f52595411b6bf425954122cff7159541006f7715954122e7f515954122e7d515954122edf3159541004ff7059541006fb7059541004fb7059541004fc7059541006f87059541004f870595411a67c5059541044fe76d894119dde73d8941005dd73d8941024fe75d8941004fd75d8941024fc75d894100cfd74d8941004ff73d8941014fe73d8941006de73d8941014de73d8941004fd73d8941006dd73d8941004dd73d8941014fc73d8941666ee42d8941666ed42d894101cfd71d894156e7f51d894156e7d51d894156edf31d894156edd31d894156eef21d8941004fe70d8941004fd70d8941006ef6298941165f5719894117df771589411a57e75189410057d7518941046ee6218941006ed6218941004fe7694941004fd7694941044fc769494101dbe7494941005bd7494941004ff7654941004fe7654941004fc76549410267e65549410067d6554941005df735494119ddc735494100dbc7650941046bc765094100cbc7650941006bf6550941006bd655094165ebf635094165ebd635094101dbf725094101faf7250941007af6250941046be6250941046bc6250941007ac6250941007b7715094100dbe715094100dbc71509411cfb4715094101ebf615094101fb761509411cf3f51509411cf3d51509411cf9f3150941005bf70509411a57e75d81410057d75d8141024fe75d81410067e75d81410247e75d8141004fd75d81410067d75d81410047d75d8141024fc75d814100cfd74d8141
  | 34 => 0x9511b73c64909512fd7f73909511ad7e73909516857d73909512fd7c73909515657e72909512ff3f42909511b76f42909512ff6c42909511e57f719095100d7e71909511e57d719095100d7c71909511e67f61909511f77761909511e75f31909511e76f21909510057e70909510057d70909510057f76509510057e76509510057d76509510057c76509511e57f74509511b73e64509510073d645095167d7f73509511ad7e735095167d7d73509511ad7c73509511b73f43509516773d435095156d7f72509511b76f42509512ff3e42509512ff3c42509511b76c42509511cd7f715095100d7e715095100d7c71509511ce7f61509511df7761509511cf3f41509511cf5f31509510057f70509510057c70509511b73c40509511b57e74d81510057d74d81511b57c74d81510057f73d81511ad7e73d81510057d73d81511ad7c73d81512fd7e72d81510057d72d81510257f71d81510257d71d81512967f61d815149f7761d81512975f31d81512975d31d81510077b40d81510077840d81510077a30d81510077930d81512977a10d81512977910d81511b57e74981510057d74981511b57c74981510067f64981510067e64981510067d64981510067c64981510057f73981511ad7e73981510057d73981511ad7c73981510067f63981510067e63981510067d63981510067c63981512fd7e72981510057d72981510067f62981510067e62981510067d62981510067c629815100775719815105f77619815114f5f319815114f5d31981511157e70981510067f60981510077b60981510057f74581510073f74581510053f74581511b57e74581511b57c74581510073c74581511b53c74581510057f73581511ad7e73581510057d73581511ad7c73581510057f72581512fd7c725815100777715815103f7761581511375f31581511375d31581510077b60581510067e60581512957e76181511b57e74181510057d74181511b57c74181510067f64181510067e64181510067d64181510067c64181510057f73181511ad7e73181510057d73181511ad7c73181510067f63181510067e63181510067d63181510067c63181512fd7e72181510057d72181510067f62181510067e62181510067d62181510067c62181510257f711815100d7e71181510257d711815100d7c71181511167f61181515077761181511175f31181511175d31181510067f60181510077a60181510067d60181510077960181510077b40181510077840181510077a30181510077930181511177a101815111779101815123e7f74181510067e74181510067d741815123e7c741815123e7f73181510067e73181510067d731815123e7c73181510067f43181510067e43181510067d43181510067c431815123e7f72181510067e72181510067d721815123e7
  | 35 => 0x116df3118151116dd31181515067f5018151506f9501815123e7c5018151006fb4018151006f84018151006fa3018151006f93018151116f910181516a57e76d91511b67e64d91511b73e64d91511b63e64d91511b67c64d91510057f73d91511ad7e73d91510057d73d91511ad7c73d91511b73f43d91510073d43d91512fd7e72d91510057d72d91511b73c42d91510257f71d915100d7e71d91510257d71d915100d7c71d91515f67f61d915169f7761d91515f73f41d91515f73d41d91515f75f31d91515f75d31d91510057e70d91510057d70d91511b73c40d91515fd7f76591515f57f74591510073f64591511b67e64591511b67c64591511b73c64591511b63c64591510057f73591511ad7e73591510057d73591511ad7c73591510057f72591512fd7c72591511b73f425915122d7f71591510077771591510057771591511a777615915122f5f315915122f5d31591510057f70591510077b70591510057b70591510057c70591510077870591510057870591511b57e74d89510057d74d89511b57c74d89510067f64d89510067d64d89510057f73d89511ad7e73d89510057d73d89511ad7c73d89510067f63d89510067d63d89510257f71d89510257d71d89515767f61d89516977761d89515775f31d89515775d31d89515776f21d89515776d21d89510057e70d89510057d70d89511b57e74989510057d74989512fd7c74989512fd7f73989511ad7e73989510057d73989512fd7c73989515bd7e72989512fe7f62989510076f62989512157d71989512ff7571989510057571989512167f61989511877761989512175f31989512175d31989510057e70989510057d70989510057f74589510073f74589510053f74589511b57e74589511b57c74589510073c74589511b53c74589510067f64589510067d64589510057f73589510075f73589510055f73589511ad7e73589510057d73589511ad7c73589510075c73589511ad5c73589510067f63589510067d63589510076f62589512fe7e62589511fd7f715895100777715895100577715895116f7761589511ff5f31589511ff5d31589510057f70589510077b70589510057b70589510057c70589510077870589510057870589515757e76189511b57e74189512ff3e74189511b53e74189510057d74189512ff3d74189510053d74189512fd7c74189512fd7f73189511ad7e73189510057d73189512fd7c73189512157e72189512fe7f62189512ff6e62189512fe7d62189510076d62189510257f711895100d7e71189510257d711895100d7c71189515be7f611895168f7761189515bf5f31189515bf5d31189515bf6f21189515bf6d21189510057e70189510057d70189512fd7f76909510057e76909510057d76909512fd7c76909511cd7d74909510073f649
  | 36 => 0xc715515122f7471551510267f615515102777615515122f5f31551510057f70551510057c7055151044fe76d895100cfd75d89515767d75d895101cfe74d8951004fd74d895101cfc74d89516967f54d89510067d54d8951004ff73d8951014fe73d8951004fd73d8951014fc73d89516967f53d89510067d53d8951696ee52d8951696ed52d89512fe7c52d8951024fd71d8951576df31d8951576dd31d8951576ef21d8951004fe70d8951004fd70d89516967c50d8951006ef629895116df57198951005bf74589511b5bc7458951005df73589511addc7358951185f77158951005fb7058951005f870589511b5be7418951005bd7418951046ee6218951006ed621895100d7e76949512167e769495100c7e76949511b57e74949510057d74949512fd7c74949512fd7f73949511ad7e73949516bd7d73949512fd7c73949510257e72949510276e72949512fe7f62949510076f62949512ff6c629495100d7e71949512177671949512ff75719495100d7c71949510267f61949510277761949512175f31949510057e70949510057d709495100d7c76549510467c765495100c7c76549510057f74549511b57e74549511b57c74549510067f64549516b57f73549510075f73549510055f73549511ad7e73549516b57d73549511ad7c73549516af5c73549511ad5c73549516ae7f63549516ae7d63549510257f72549510276f72549510076f62549510467e62549510467c62549510076c625495100777715495100d7e715495100d7c71549511ff7471549510267f61549510277761549511ff5f31549510057f70549510057c7054951004fe7690951004fd7690951044fc76909512fd7f75909510257e75909510057d75909510257c7590951006bf649095101ebc6490951004ff7650951004fe7650951004fc76509510057f75509510257e75509510057d75509510257c755095101ebe64509511b73e54509510073d545095100cfd75d81512967d75d815101cfe74d8151004fd74d815101cfc74d8151004ff73d8151014fe73d8151004fd73d8151014fc73d8151044fe72d8151004fd72d8151024fd71d8151296df31d8151296dd31d815149efa50d815149e7c50d8151006fb40d8151006f840d8151006fa30d8151006f930d8151296fa10d8151006fb6098151005bf74581511b5bc7458151006f9601815123e7f751815100cfd75181511167d751815101cfe7418151004fd741815101cfc74181515067f54181510067e54181510067d54181515067c5418151004ff7318151014fe7318151004fd7318151014fc73181515067f53181510067e53181510067d53181515067c5318151044fe7218151004fd72181515067f52181510067e52181510067d52181515067c5218151024fd71181511167e51181511167c5118151
  | 37 => 0x81420057f75581421dd7c7558142005df73581421d5dc7358142005f771581421cdf47158142006f96018142024fe7518142004fd7518142024fc7518142044fd7418142004ff7318142014fe7318142004fd7318142014fc731814200cfe7118142004fd711814200cfc7118142006df3118142076f9401814230d7f7690b510257e7690b511f57d7690b510257c7690b5130d7f7390b511bd7e7390b516e57d7390b5130d7c7390b515657e7290b5130f3f4290b511c76f4290b5130f6c4290b511e57f7190b5100d7e7190b511e57d7190b5100d7c7190b511e75f3190b511e76f2190b510057e7090b510057d7090b511dd7f7650b510257e7650b511dd7d7650b510257c7650b511c73e6450b511df3d6450b516dd7f7350b511bd7e7350b516dd7d7350b511bd7c7350b511c73f4350b516d73d4350b5156d7f7250b511c76f4250b5130f3e4250b5130f3c4250b511c76c4250b511cd7f7150b5100d7e7150b5100d7c7150b511cf3f4150b511cf5f3150b510057f7050b510057c7050b511c73c4050b5123e7f74983510067e74983510067d749835123e7c749835123e7f73983510067e73983510067d739835123e7c73983510067f43983510067e43983510067d43983510067c439835123e7f72983510067e72983510067d729835123e7c72983510067f42983510067e42983510067d42983510067c42983510067f32983510067e32983510067d32983510067c329835123e7f719835114e7f419835114e7e419835114e7d419835114e7c419835114e7f319835114e5f319835114e7e319835114e7d319835114e5d319835114e7c319835114e7f219835114e7e219835114e7d219835114e7c219835123e7e70983510267a70983510067f409835123e7c40983510067f309835123e7e30983510067d309835123e7c309835114e7f109835114e7d109835114e79109835123e7c109835101cfe76d91510257e75d915100d7d75d91511b6be64d91511b73e54d915100cfd75d91515f67d75d915100c7d75d91511b67e54d91511b6be54d91511b63e54d915169ebd54d91511b67c54d9151004ff73d9151014fe73d9151004fd73d9151014fc73d91511b6bf43d9151006bd43d9151044fe72d9151004fd72d915169e7f52d91511b6bc42d9151024fd71d91515f6bf41d91515f6df31d91515f6dd31d9151004fe70d9151004fd70d915169e7c50d91511b6bc40d91511b6bc64591516cdf77159151005fb7059151005f8705915100d7c765515101e7c765515100c7c76551510257f74551510273f74551510073f645515101e7e645515101e7c64551511b73c645515101e3c64551516c57f73551511ad7e73551516c57d73551511ad7c73551510057f72551512fd7c72551511b73f425515100777715515100d7e715515100d7
  | 38 => 0x4fd7598242024fc7598242004ff7398242014fe7398242004fd7398242014fc7398242044fe7298242046bf4298242046bd429824200cfe7198242004fd719824200cfc7198242006df3198242046fa7098242006fb5098242006f850982420b6f94098242006fa3098242006f93098242046fb2098242046f82098242004ff75582420067f75582420047f7558242024fe7558242024fc75582420067c75582420247c7558242004ff7358242014fe7358242004fd7358242014fc7358242044fc7258242004ff715824200cfe715824200cfc7158242006df3158242046ef2158242046fb7058242006fb5058242006f8505824209efa4058242006fa3058242006f93058242046fb2058242046f82058242024fe76d95421de7e65d9542044ff74d9542044fd74d95422267f54d95422267d54d9542004ff73d9542014fe73d9542004fd73d9542014fc73d95420067e53d95421de7c53d954201cfd72d95421de7f52d954200cfe71d9542004fd71d954200cfc71d95421de7f51d9542006df31d9542004fe70d9542004fd70d95421de7c50d95421de7c6559542005df73595421d5dc73595426fdef7259542224ff75595420067f755954220cff7459542006bf7459542004ff7359542006df7359542004df7359542014fe7359542004fd7359542014fc7359542006dc7359542014dc73595426fcff7259542006ef7259542004ff715954200cfe715954200cfc71595421de7f5159542006df3159542004ff7059542004fc70595421de7c5059542045bc7655142026bc7655142044bc765514201dbf755514201f3f75551420073f6555142026be6555142026bc65551421df3c65551426f5bf73551426f5bd7355142007af7255142045be7255142045bc7255142007ac725514201ebf625514201faf62551421df3f5255142005bf71551421df3f51551426ef9f3155142005bc70551421df3c5055142024ff765494201cfe765494220cfd765494201cfc76549420067f65549420267c6554942005bf745494201dbc74549420073d5454942005df73549421d5dc7354942047ac425494200cfe76d85421cef661d8542024fe75d8542004fd75d8542024fc75d8542044fd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d854201cfd72d85421cef641d85421cedf31d85421cef621d8542004fe70d8542004fd70d85421cef410d85421cef461585421dd7e75d81420057d75d8142024fe75d81420067e75d81420247e75d8142004fd75d81420067d75d81420047d75d8142024fc75d8142044fd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420d6bf43d8142006bd43d814200cfe71d8142004fd71d814200cfc71d81420d6bf41d8142006df31d81420d6fa40d81420d6bc40d8142006fb609
  | 39 => 0xf71d8d52006de71d8d52006dd71d8d52004dd71d8d52006dc71d8d5270edf51d8d5270e5f51d8d5270ede51d8d5270edd51d8d5270edc51d8d52006df41d8d52006de41d8d52006dc41d8d52706df21d8d52006de21d8d52706dc21d8d52006df70d8d52006de70d8d52006dd70d8d52006dc70d8d5270edf50d8d5270ede50d8d5270edd50d8d5270edc50d8d5270e5c50d8d52006df40d8d52006dc40d8d52706df20d8d52706dc20d8d52006df10d8d52006dc10d8d5200cfe76d8552205dc73d8552006df63d8552006dc63d85521fef661d855230e7f75d8552044fd75d855201cfe74d8552004fd74d855201cfc74d85521867f54d85520067d54d8552004ff73d8552006df73d8552014fe73d8552004fd73d8552014fc73d8552006dc73d8552014dc73d85521867f53d85520067d53d8552024fd72d855230e7e52d855230e7c52d85521fe7f51d85521fef651d85521fedf31d85521fef621d8552004fe70d8552004fd70d85521867c50d8552005bf745855220dbc7458552005df7358552205dc7358552006df6358552006dc63585521fef46158552005fb7058552005f87058552006df63d8152006dc63d8152044fd75d815201cfe74d8152004fd74d815201cfc74d8152004ff73d8152014fe73d8152004fd73d8152014fc73d815200cfe71d8152004fd71d815200cfc71d81520de7f51d8152006df31d81520defa50d81520de7c50d8152006fb10d8152006f810d815220dbe7498152005bd7498152205de7398152005dd7398152006df6398152006dc6398152006fb6098152005df7358152205dc7358152006df6358152006dc6358152006df6318152006dc6318152006f9601815223e7f7518152044fd751815201cfe7418152004fd741815201cfc741815207e7f54181520067d5418152004ff7318152014fe7318152004fd7318152014fc731815207e7f53181520067d531815226e7e521815226e7c521815200cfe7118152004fd711815200cfc711815207e7f5118152006df311815207ef95018152006fb1018152006f810181520467f755964220e7f545964220e7d5459642004ff7359642014fe7359642004fd7359642014fc73596421f67f53596420067d5359642044fe7259642044fc72596420467e52596420467c5259642046bf4259642046bd4259642004ff715964200cfe715964200cfc71596421f67f5159642006df3159642004ff7059642004fc70596421f67c5059642004ff7558642024fe7558642024fc7558642004ff7358642014fe7358642004fd7358642014fc7358642044fe7258642044fc7258642046bf4258642046bd4258642046f771586421e6f641586421e6df31586421e6f63158642006f53158642046f72158642046f42158642004ff7058642004fc7058642024fe7598242
  | 40 => 0x925200cfc71592521de7f5159252226bf4159252006df3159252004ff7059252004fc70592521de7c5059252226bc40592520067d7558652004ff745865201cfe745865201cfc7458652004ff7358652014fe7358652004fd7358652014fc7358652044fe7258652044fc72586520467f52586520467d5258652046f771586522167f5158652216f65158652216df3158652216f63158652006f53158652046f72158652046f42158652004ff7058652004fc705865216e7c505865223e7f759825201cfe7498252004fd749825201cfc7498252004ff7398252014fe7398252004fd7398252014fc7398252044fe72982520467f52982520467d529825200cfe7198252004fd719825200cfc71982520be7f5198252006df3198252046fa70982520bef95098252006fb4098252006f84098252006fa3098252006f93098252046fb2098252046f82098252004ff745825201cfe745825201cfc7458252004ff7358252014fe7358252004fd7358252014fc7358252044fc7258252004ff715825200cfe715825200cfc71582520a67f5158252006df3158252046fb70582520a6fa50582520a67c5058252006fb4058252006f84058252006fa3058252006f93058252046fb2058252046f8205825201cfe76d915220ebe64d9152006dc63d9152044fd75d915220ebe54d91521f6bd54d9152004ff73d9152014fe73d9152004fd73d9152014fc73d9152024fd72d915220ebf42d915200cfe71d9152004fd71d915200cfc71d91521f67f51d9152006be41d915220ebc41d9152006df31d9152004fe70d9152004fd70d91521f67c50d915220ebf40d915220ebc6459152005df7359152205dc7359152006dc6359152725ef72591520457c765515201e7c76551520447c76551520257f74551520273f74551520073f645515201e7e645515201e7c645515220f3c645515271d7f735515271d7d73551527175c63551520076f72551520457e72551520457c72551520076c72551520267f62551520276f625515220f3f42551520057f71551527175f31551520057c7055152205de76d8d52206de76d8d52014de76d8d527075f75d8d522075c75d8d52006df64d8d52006de64d8d52006dd64d8d52006dc64d8d5270f5f54d8d520075d54d8d5270fcf52d8d527075e52d8d527075c52d8d5270fcc52d8d52005dd71d8d52006de61d8d52006dc61d8d5270f5f51d8d5270f5c50d8d52706df75d8d52206de75d8d52206dd75d8d52206dc75d8d52006df74d8d52006de74d8d52006dd74d8d52006dc74d8d5270edf54d8d5270ede54d8d5270edd54d8d5270edc54d8d5270edf72d8d52706de72d8d52206dd72d8d52706dc72d8d5270edf52d8d52706de52d8d52206dd52d8d52706dc52d8d52006df42d8d52706de42d8d52706dc42d8d52006d
  | 41 => 0x10001000000000080050014001000000000080010000000000400000000000004003000c002001800100000000004001000400100000010000000001c001000400300140000018001000c000000800300080020000007002800100040000000000000c0010000002000000100080000000003000c00e000c0010000000000400000040070004000000c00100000040000000000c000000000000100040008000000400000000010004000000400000000000000000000000800040030008000000000200040010000001000800000000010004001001c00100000000000001001400600180000000001001800000040000004005001c00100000000004005000000c001800000000010018000001c0020000000000000100480020000004000000000000010010003001c0060004000000000100080010018000000400300080000020001000400000000030000000000000000040010000008000400100040000008004003c0040004003044fe76d895401cfd75d8954024fd74d8954004ff73d8954014fe73d8954004fd73d8954014fc73d8954726ee52d89546feee42d895400cfe71d8954004fd71d895400cfc71d89547267f51d8954006df31d8954004fe70d8954004fd70d89547267c50d8954006ef6298954005fa7098954005f97098954005df7358954235dc7358954046ee6218954006ed621895400cfe76d855422ef661d85541c67f75d855401cfd75d8554024fd74d85541c67e54d85541c67c54d8554004ff73d8554014fe73d8554004fd73d8554014fc73d8554044fe72d8554004fd72d85546ce7f52d85541c6bf42d855422e7f51d855422ef651d855422ef641d855422edf31d8554004fe70d8554004fd70d85546ce7c50d855422ef46158554005fb7058554005f8705855401cfd75d81544067d75d8154024fd74d8154004ff73d8154014fe73d8154004fd73d8154014fc73d8154044fe72d8154004fd72d815400cfe71d8154004fd71d815400cfc71d81544a67f51d8154006df31d81544a6fa50d81544a67c50d8154406fa40d8154006fb10d8154006f810d8154006fb6098154006f9601815423e7f751815401cfd7518154024fd74181541267e54181541267c5418154004ff7318154014fe7318154004fd7318154014fc7318154044fe7218154004fd721815453e7f5218154126bf421815400cfe7118154004fd711815400cfc711815453e7f5118154006df311815453ef9501815423e7c5018154126f94018154006fb1018154006f81018154046bf7459252226be54592521debd5459252004ff7359252014fe7359252004fd7359252014fc7359252226bf4359252006bd4359252044fe7259252044fc72592520467f52592520467d5259252046be4259252046bc4259252004ff715925200cfe715
  | 42 => 0x300000030000002000000300040010008003000000200100090004000000400300040050008004000000200040000010001000c00000000000000003000000000040020004000000400000040020000000000000200000090000000001c0020020001000000300100060024003000c0000008001000800000140000000001000400000040000008000000400000000020000000000c00600140000024001002400000000010004000000000200000090004002000000000000000000005001c0030008000000c0010000003000000000140000000003000400000000000004000000c00200040000010000000c0000004003000c00000180000000001000000b00080010024000000c0000000000000000000000000000000000800600000020000000000000000000070008006000000000200040000004001c0000008000000c00000000000004009000c000000000100000070000000000000c00240030004002000000400100000008001000800000040000004000000c00000000070000001001c00200000000000001000c0070008003001c008000c00000000000000000000400200140000018000000000100000020000002000000400040010000007002000000000030000000001400100080070000002001000200000000000000000000700000010028001001000600000050000001000000500000010024001001000000000010008001000c007000000000080020000002000000100100050000000000000000040010000005000400000000020000000001800000000000028001001000000000050004009000000000000010030001000000200000010010000001400000080070000003000c003001c0000008000000c0000020000000000200000020000003000000000100000004002000000000000020000003000400100100000000009000400000000080000000000c00000000000008000001000000040010004000000c00100040000000001000c000001c0000004001000000000080000000004002000000000030000004001800000000060004000000000000040000008000000000300200000008002000c0000000000000000100040000000001000c007000000e000000000000000000000000c000000800400180000018002000000000040000004000000c000000000000080010004001000800200000000000000001400300000010008006001400200000000000000000000e00000020000000000c00100040000000003000000100000000008000000c0010000000000000a00180010004003000000000000000004000000c0010000000000000400200030004000000400200080010000001000000000000020000002000800200000040004003000c00000000000000000000400100080000000002000c000000
  | 43 => 0x80020000002000c000000400200000010004001000400000080050000002000c00000040010000000000000000240030004000000000000140000000000000400400000040008000000400000040010000001000c0030000002000000000140000000004000000500080000004004000000000000050000000000000000040000000000000400200140050004000000000000040010004002001800000080010010000000c001000400200180000024000000400100140040008007001c0020008000000000100000000000000000800000240030000001001400300000000000002000000100000000004002000400b0000000000000000040010000008000400000000000004000000800b00000000008000001400200040020000001000400000140020000002000c00200000030004000000000000040040000004000000100080010010004000c000000400000000010004009000000300000000000001000800100040000004000000800a0004001000c00100000040010005000000000000020004004000000000180040004009000000f0000001000000000000000008002002800000000000000002001c0040000000000800300000000014000000400300100050000000000c000000400c00140010004000000c0050000003000c000000c00000140000000001000000100000000000002000c00100000010000001000000100040010004003000c00000000010004000000000100000000004000000800000000030004000000c00000000000000000000800200040000018003001000300000000000000001c002001c004001c0090004007001c00000040040000000000000000000020000000000400500000000004000000400000180010000000000800500000000008001000800000140000000000000000100000000004000001c0000000001000000000000000000000000400400080040010000000c0010010004002400000000000008000000000000000010000000000c001000000200000000004003000400200000010008000001800000000000004000000c001000000100080010010000000000000000000014000000400300040000000004000400000000010000004000800000080000000000001400000040000008001000400100000000008000001400200100000004002000400000000010004007000000000040050004002000c006000000300000030000000000400000000000000000000000b000c00800000010000000000400100000000000001002800200080000000000000400100000040000000000000100000000004001000000000100000008001000000200000000004001000000000040040000000000000000000010008004000400000240000008000001400000040000000001001400
  | 44 => 0x4000000000000080020004000000000000000020008004000400000000070000001000400300000000018001000000000040000000001000000000040050000003000000000000050000001000000000100000008003000000000000000000000000000100000010000000000000100000020008002000000200040000000002000000000100000008000000400300000000010000000400200080000010000000000000000070004000000c0000018000001400400080060004000000000600000040004001001c00000180010004000000000000100030004000000000200000030000000000400000000000000000000c0010004003000000100040010000003000400300000000004000000800600040000010004000800100040000000004000000200000020028002000c00c002c00600040000000002000400100000000000001000800200000000000000000800000140040004000000400d0008000000c00b000000300080010020002000800d000800100180050008004000000200080010000001000800100000000004002000c001000800a00000010000001000c0060004002000400400040070000001000800000040010000004000000000000040000003000800000000000004000000000100080050004000000000000080010004000000800000140010000000001800500000020004000000000000000010000000000000000000030008001000400100080050000000000000100000000000002003800000040060000003000400a00000020008000000800000180000000000000000000000000004000000000100000070010003002400000000010008000001000900180060008003001000300000000000004000c00000000000000003002400300000060010000001000300040010000000000000000000000004001000400000000010000008000000000040020000000000400000000000000006000000100100000008002000400100200000000000000400b00040000004000000000d000000100000000000002000400000000000000006000800000000000004000000000300000030000000000c0000010001000000000040050000000000000000000000000004000400000000000004002000400000000000000001000800200000000000000000000000000030004000001000c00100000004004000400100100000000000000000000000000004003000000000000000004005000400000000010000000000400a00000030000005000000100080010008000000c0000000001000400100000010000001000000200040000000001000000200000000000001001400300080040004001001400100000000008002000000600000000004004000000000080040010001000400000040060004000000400400
  | 45 => 0x20a4fc00000005429406899351268d8a4600011805168000000154c0000d844992c4c00032f60002cc038b00002a3800017b0000000000063700000000000000000000000000000c800002c70c790d44000000000000000000000c7bacd4000355e38800e6847800000000009e1000000000000000000000000000000000000000000000000016e6000369ea30000000016800001b22c9596e449c82a427680006530128ad0a4c800000000000000000000000000005fc0000000000061104d20002ffa9e90000474036cace0000000000071f80000001fac000000051a9b7c49400000000000c2a0000000000000000009f280000701908000000067d0000000192ad022000a8e25dead9800000030445518c92bef2cf8000107200000000000000ddc80000000000d0a16d43ed271a10884343a828fc623a60a00000000000000000c00000000000000000003400100000010004003000800100000050000001000c0000000000000000500140000000000001000000000010000001000000100000000000000000800000100060008000002800100080000024004000400100100010000001000000000100000000000000400a00100000024000000400000040000000000000800000000030008002000400000000000004002000c000001800000000020008002000000000000010000000000c00100180000000004000000300000000000003000000100040000000007000000000040030000004000000c0018008000c00400000000000001000c0010008001000400200000010024000000400300040010000000000000200040000000001000000000100000000007000c00000000000000001000c0020004004000000000000000004006000000100000010000000000400100000010004000000c0020014001000c00100180070010000000000100000020000006000000100000000018005000c002000000100080000000000000000300080010000000002c00100100000000005000400000000000000000000000100000000000002000000000000000000000000c002000400700040060000000001800000140020000002000800000000000000001000400000040040000006000c00000000020000000000000600080010000006000400100040030000007000c00100140040004000001000200000010018000000c000000000000140000000001000000000040000000000000000300000070000001000400300240000008000000400100000050000000000000200140030028001000400e0004002000400000040000000007001c001000400100080000018004001400000000030000002000400000100010000000000400100100000000000001400000000010008001000c000000c003000000200000010018000000000200000
  | 46 => 0x6a235b8000c35800045db43c0002a860000000949800098e160820e00000000000a57814c00000000000f8e000000000000000002bbe93600000002e1242e000000000000002794c9b000000000006892882000000053a00004f1000000024100000000000000000000000000280000302a0001658b0e06f80000000d33b756000000000000000000000000000000014b40000fc00001c12000096400031c6000240e00000002a3000000000000001e165708000000206e00029f2000000000000001a0ae547f19b5a8fc0a5a472b5424c600009ba00000002350925800000002accef1d069899cf2000000000000000000000d1200000c28000b82a970355800000012aa50d80002d71d5a2308000c5b80000000246337800043f00003be9d7821800000000e5a8ee0000000000000030dc6512abe54d800064900000191ee00400000000077a846000000000000000710242800092b000000000004038000000278850e883000000007ee0000441238859520707628000000000000006a80001ee222ba3a61852506505982422c000000000007d60000baf000023e265062b8000000129e0d889140000f1a296197cbe61560b0a065c2530d8e00000000001c7890d000000000000000000000147268c8000000000000000006f2256e000000000000000000ae478b800005b275c000000000000005c08000000000038a1878248abe800000001e10d928509e6000034b2ad480a60001e50000327800000000001d0a00000004bca9ee5860ec20000000c62b3840411eca19000000001ebe71334d0d442954a15800000036d200014e29270000000000000017220000000246800000000000000c2c21700000000b6e62230221f1ac30000091800022ee7ac80000000000707000000000006cc9adc0000000d6aa50400000000001c229ad910c0000f7a00000004b0800000000009d88000198065200034dc000000000000001f2000000025d600035dcd2a80000002e1839a0000852a10c0000000000000049a166200007aa8d803309c7b6d42e11b880bd1802037000038fb336652a67c0001674a3e04fc1f081d48a425c64f6b76a2f00000ceeb32a0000000d4d800097709f400000000000000000000064f88cc0000000d5880000002f9c0000000bec00000000000d08178400017b6000000009c000000000009e6800000000007a500000000000000000000000002cf00000000000a7000008ff000000000000002a624a080000003350489b1be4de00003fc0054805321643e800000000001241e4400013e80002414021800000005ca0003424000000000020d801aa2540000d3c000000019e80000000000da4844cceaa7fa000000000025d800022b65e78e2a60136b6000197a000000019f343873d281e0002ac00002c3a00000009
  | 47 => 0xb52127c00019580002d980000508a248000775ae9200000000000000000000028f96d693b1bb0036300600024b000034883ad8000b8f17deb181682000000000000009bf92e600000000000000000233c0000000000000000000000000000b478000000000054b8000000331811d182e0002ade000000019b198285727eadaba5400000000000196490b0000ccc07e60002748000121600000005c50276000000070db15093a807ca2392ce6af21e00000000068000062f80001fe9ab00000620000009e0000000dc58f7e00023bea7e214edaea60400000000000000000000000000000002796a61000000000000002d720000ea82b3000051b801e00005e800032fccadb4a600000006a38000932800036206a442b23da0000000000000047a800000030ca07925e6d2fb02036d8000bd2179400036c24a20000000121e00000000000000c3a07e80003764000182600027b0dd830d47cf20beba1000075c800001d21c2254800000022d20001cf600028666330000000000000014026a51db84cf80000000000dc880008c88000000144c951250c7bc80000000000000000026d8000a6600000002c52000227c00000000cda5a800035da000294c71d8940a5e800046d9bd20000c460000000b4daa6e2ed000000000000001a30000000000000000000c060001b2e000335a2438d5c8ed8000d53b48a00035720000000000060600000000000d8252e1aba00030faa750000bc6000074c8f3a14f932aa48000092300009cd000000028760000000000000030e8000000000000000000001302000000076700000000000000000000007a4a50883a44a2d6825980004d68c422b88000000000000000000002686000219800000000000abc00000000000000d9482320049d220000000d4e9fca00027f28b78000000000087200000001f6a32f0000b7d9564000000000000008e500000000000000000000035800000000000000000018e400036549168e9453900000000000000000011d8000000086809ca712b53930000021b80f800000000000b0b315600000000000000000000000012180000000000130a9cb9bb6af68000000188cd1c000019c0f58000157e000313c0000000000000028c22e20000000388800000009c029e8000000326e00000000f7000000026286951dd4000000000016f4d2a1d8ccbb800080818bc000000000000000000aa088807b45f28000cce0000000373c0000000b6c002cd670156be7acd6c580292a7306800641244000237aa4b00000000000000000070b800017d00000000000000063c69b000000009848abaa9400000000001a5a5dd00000003410cbf800000000000001e968b413f8bb525b8abe0c34773000032c8000000000024915660000000c49900c1b4b23200000000f895c0b498426bab0
  | 48 => 0x1a68434800000000001888000000000000000007c400000002578252b13a33480000000000000329200014b6179010800026ae640000000000000c30000000000000000000000000000000000000000d7b452651800000032768532fd00000df6000000000000002928000cdc000082ca23448f00006760752c8e8254c772662000006670f0000c3880008ed000000000005c82bcca6b0000b6681ce425000000035f6ae63346bf5800000000000000000db7800000000000000000c90895885f0000dac92c67fa1030a0f0000c7000009f532605418000000000000008c6000135842700000000000dc22ca28918000bc228e66918000d5d80000000000000012400000000000000af7af6c0002eb400000000000000000000085500000000000000000029a800000000000000000ab9291e4b7a530bc7a8ca00000000000080837800220a80008f38a480001ebad4fb3a63fd800023994d440200000000000000000072280006c4800000000000002d2400000000000000bf98aac0001032b39b52e0003238000300cdc4948ad0c28e200011f8c56a8381c20000000000000000000002c78000192e67400002d3349000000009a7a5d04ed857a3e0800088600007b600001aa8000cfb00005758000220971e0001fec3d980000000000000000011c8f8a000000088e0000000000000000000001166d0d314ed3b80000000000000000000034960003042371073873700f8603800080580000000000000057e00003e8680000000000008f8123000000dea0a2570061aef44f48050000000000000009e3000000000000000000000000056b80000001dbe000000000011a400000002da00003330d6cbeb9bee62a00000000000000242a00000000000000db200000002b8200009340d680000002ec681e800047780000000000369000000000000cd2ae6cb830aa3ec19040000aa4c02000072d8000000000000000000002654d4300000002d7c00000000000000a7580000001274b55b3660001f5093300000000000c01000002200000001f5ea270000b84000011c2c163e12484000262041500000000000af81846074000082b8000c29000088c044600000000000000368378480e000000008ca7b689f000027a600033823070000b8d945603d800000000000000000dd216c638e92580000000ab680009e800000000342000085695200000001dfe0001b9ab799c32a17ae980001bbc552b72015a06e20000000bc1965cb50000000000000000000000172c208ab4a000000000000000000000af3800000000009ed9b92000000000028d472b8dcad1000000000ba8b7d05c60000000000000000000006e7000047234987c8000000000009392bd6ab0800030280008a6112ac1c80002e480008fa8000b68269a0348000a361b78d502590
  | 49 => 0xb620000000bc92c3254400004a40cbe19a929a5ae8000000179a00021aca49248805b80000000000000253a000000000000005f480000000000d7600a0000000000021fac67ae1a0003456c0a0000000333ecf3826e0002fd2186a5e433100000001fcc0000000042ab32bba0000860000000000000000000000035671a326800029288b32206a3fa12e0000f9200031fc000000000000005a78000000000000000000000000b918432132000089f8000000000000027a20000000000111a0001f7a6cd800000000000002598000000000000000001f4e0000000a0580007669544b4a800000000000000000b7cb1d29bd057885900003f80000000000000000006ec8000000000000000009da8000c048000000040a00013ca0000314a6e0000114a490000000063c2bb20001a20a3cab74c44aab074705586a780000000000b698000000203a6c127dc000000000011fc0000000000000000000009ba8000000274e68a80001969ffa000308ec5d1a1e4158fac000370600000007168000641815a42991a2000217a0000294c1600000000000000287e0000000ccd24a60000000000360a00000008b200000001252000000000003281de339e0002f2c47d9aa02b6120e67b00002978000cf5000075f04de00003b2c131a38000000088aa93a00026bc7bfb6040f300003f48e982e9126027c813a00000000000000000000048facac73c0000000347e211800000004cc3450000000249e40f8000073000000000000002006000000000000000002cd88e1ab22308000000033e0000000000019cc00000000002a88b46800000000006f6b134032875ebbe31b85b8b1ec2131786cf40000000000000030d22eb2b7200000000000000000000088a313230990f200000005f70000000000056236fab330ff85a600007e280000000000000000061a0000000062a4e8254e6df8000c1b2e2c0000fa89f88ffc000000000235820001ccc7cb9de64faa170aa9821404aa86eb441d5400000000002f1200000000000000c1c0000000000000000000001362dbaae722121c3a000000000008d4000000000000000000000000000000000000000000c9d00000002bba00000008b180000000000c002eae1ba0000072a61a3cc800000003d6de0800062d8000a26000000004820000000272acc40000000d9332220000000cba9fbe6208c6200008f017e00007fd8000dc93224d683202000000018d13bc69980006bb8000dcf800000010ae934000000000000000000dca000007c070c6f10d3add78000dad0f1e6fd000000012f60002f58a5a09eaa19042800000001f02ad200000000000000d011648d10800000000000001dfa0000adca4a800064d87ca0000000000367e000000000000000000c280001a1400009e4722000000027920000000000
  | 50 => 0xe8000a100000000251a0000a700000000000000000029f43999534774800000000000000000d8b110a85e0ce82f100ac2f2000000000000000000000000000022e454e0000000000000000000000000674800071b2972070a0ec00000000002a04000000096280988cf8000000000000000003808000b5902620001508488a76015b9710b810000d47800048d84480002dcc00014540000000000000000021a0000000000000000001dd85d28d9c000305c000000000012b00001ece0000000b27afc8db00000bd5291c000000086d00007bb0000000000016c8000000000072d1e5c00016ce4d30000c492e3a000000000011aa00000002e5000031680000000f4a1dc857cd3d800000019becc9800000000000000000000000047c00006e8800077a1c34a63aedeb888d0214eb6b0b7808bc0000000000348e3a0365e000000000007480fd8b8648c800000036d00001ca0000290695706fe750ad189ca2c86122000064480006d4000000025da000000096b0000000000000003e60000aaa0000000ae00000da000003f898b444ba66c000115a0000000b6b00000002642bf880001c520f6000133400028546dd9d560000000000000005718106ad9fa24b80000000000000000000000000000000049b2a2e00000000000000ae9878a16600001b808dc54800000000892000000061c332e000000000000000001f2c58eb6d8c7680000000000000339889d80000000dd8d218ef439d00004880ee8054a2b449db648000359a000000000000000d5256600000000000000ae3800023d00004b1053800031140000000af600000002d3e87c00000000000000373a6ca00000000000d3b000048d35f2a0c000000000000130000a8a837ab6180009560000000000000000000001672000000000000000000000a06a28e08f00008b1034c00022fe4119b56000000094a8000841a492d9000005d580001830000000111891c80000001ba8000000000032e62c4a424000118ca8399b450008020000000bcf8000000000000000005d200000001e3c68bae500002f9a000168600015420f00d78000251cac929a6395000024783761cb8000a2bad026f18dc040893360000000d458000033b14c00037040001fe600000000003102000245600000000001ac40000000479849c189b6f293d8000c9600000000000cdf8000be4800000010900000000000000000019a60ac8000410311000007ae0000000679800007a9306d6c00007e7000000029e87ad80003430000ccf30642ab83beb70ac2400000000002fe073980000000ed200013b00000000000053c24daa3ebb891246f280006d39f1e00032183f3a24a0000000000199ac41318e88305be61d98e0d0aa42200000000000692d1b216602f00000002f760000000000255600000003170000000000
  | 51 => 0x3148fcaa21237c92fb29618e29a2000000000006480000000000000095d9a0800000007621dba000000058300000000000a77a7c8160209613100000000000a1283a6025008e00026e221e0000000000000025d20002ec850d19b8000031614a1f40172351a000000000000009c08000000000000030ea00000000000000000255064ca406be400000000264115045c9f680000001d2e0001b720e88000000000038480000000000183b4ac98089200001d9600000000000000000000000000000000000000052c0000000000071200027d6000000010300000000afc000335c54a181aa92aed000000000000000ddb235800036f66f4077c00000009a98000c0e800085baeaa32789e841e80009648000347000084da8a47fe00001e30000166800060013e0c8f00001a68eca2bcae1c89012a6000000000015be0000000d1695de7f60000000000000028b400023b2ab2800000000003b100ec00000000000000000000000000008568000c781bce000213e37987c41c8a2aa0000000000150e13c84169579d1400009d807db3780000e9257c0000c0d800000027c00fe8000b79153e066800015720da2dc0000000223a0000000879976aa458000000000000013042b0985e00035e80001a620000d4000001843af0d9e597aa909a222fa6550c6c49f8000000270c0000000000343a482000070e0286820a06cad8000072400008e2b18637880000000000d598e6a0000902527800000026ec142b54c000000000000004b600004e0a1348bf2c74bd3913e4d584f4000000000030f026380000000000000000093c8000000000000000008250a9c0000000000266e000000024c80000002d0600000000000000000000000000000000000d0699800000000000306e0000000151800000000006339bfa00000001f4073c0000000afca79c4f7000000028480001818000000000000000000000000000000000000002e420000000d3a370c54e800000030c63c080000000000c7415b20e81fc400001aa00004b00000ff2000000017800000001c260000000ae50000000000000030a20000000000166c000375c3d500006f5800064680002a59e986052450b97838687d3688000000074d185420c800052300003a720ce94900000000f9a887800000000006eba5f800000008b60000b17af60000140a0000d188f50000cd50000116b1ca0002896000000051187ac0001e0a39fb48c1ff0da2000000000000000000000c930000000146c0000000aeb885418c80000000e62530800078f8cb00000eb80002d3cb1b2aaa00030620002b6e00021e8c3b8000000000000000000002d7a09580000000000000000000000007061afa66f0bfc7e48000936800000000003319c209ee0000103889c2b6a64e000000000000000000000028800064
  | 52 => 0x367000000003a78000000000000000000000000000000074200000002cae000000000000005fdabee484b5fe6be0f940000000c7cb0ac000000000002de339201a000000000000006388000000000000032b83abb61e3962ef21678c001e40000c1580007b1136014080009eb1084563267400000000001e1c0000000cb0af04000000000e0000000149c0000000000000000000001dd80000000814000128a926054c000000002c8dc8b210de43e90000d1a0000c0418d8000000000007a67b7ab96000188a000128e0000000caeb2a8a7216d80000000358000025b9ce25b0800000029be0002c5000005b60000592000000005607803d095160002c02000021600000003970000000000034380000001b7400030e000002ee00000007ec0000000000000015488bc363cc3990dc03d32980000000000000000000003151ef000000000000000a011b600000000b3a858a0001af00000000ac60000ae49b5800031780002a1a0000000000068811b80000000000000000000028e0a0a800057612a47c4800000003ee00000000000000000080e000285a938b0c256189d21ef800000000000000000000000000028a2000000093ba448000344e000000054a8fdaa44987a07e80000001d94b728000000000033089fc10080700000000be2800000000002f92f70c7380000001b42000000000000000000000450960e000329a1911562cd59a400eaa80e00000000000000000000000000000000000b550000000029800009502de00000000000000000000000001ee80008118a8200000008cd207c88b0000000340cbf6b284db900000000000000000000000000000000000113c540800005fa18e00013c8afa878600000003c41b9800026e000000000000000517800068700000000000000084421380007f580be0000b90a1e309e0000ea235f000000000005ffa5188be0000232000000023c63b21e9c000249a8d6800000000000000000000000000035ca6922bd0c7d1d6e2c380000000000c6494ca00000000002e6e0002b4c53f0d5a46394c80002cd0d4600009690000000000068600000000000000000000012a0000027c00000000001b06c9c1e180000000000000000023962100000000000066b16cc24a80000000ae6548a3040000000000349c000264058b8000d5f000000000000000000000000038b8dbc000000000008ac000000000035b253b80000000762a71800078d800057c80005098000482800000000000000000b6200000000000cc390fe00020323860000000000000000000001700000000027201069508000d2b8000000216c000062800004c66758000d3f1e460000f08d88b6a897380000000000d16000049398609bc298a00012665f50e7c000000000000000000000bcd8000000000000000000001832b7380
  | 53 => 0x5e4000000010c400000002f623e60000000000000067280000002148000325e0000000000000000000002640ca68f8800000000000000000418000000000000000c600002bf6599a8dc28280002710000665800000000000000fa20000000cfc32dc0000000000000000000000000000be998c80001da6000000000000000000000a2cb6f4000000060200004f38684000000066a05fe000301ca0bb24e0001daa00000000000000bf000009ff000000020f2c2f232c0000000000023e24f84860000420000000057e000000005eab069ed600006780001f56000000000026ce57300000000f3cd6b800000010a00000ade0000000ae28000000000000000000002bdc000000034b0000000000000000008d506f29b080007710000000000000020220001a6a5d7000000034d62f5142e0000000720800085d800000000003ce00000002e9044c8000458b12e0000000b5680000000000000000000000000001ed4540000000000000002e2abd58000000000000000003b60baa0fd036638e000082d228a00002b4cb184a8afe8b10c6100009ff80004ee00000001efa0012312000000000011600000000000000088111367078000ddf000000008a400016f21ce800000000000002b2e00027520002c7600000000001aec543000000000007430000a96b5fa94382e21e7000000022f60e3b61c8fb102e00035607ea8ea6000104e00003d4a0c8000bc300001959920655800039e00000000000668186400000005600d3852980001e8b6202ce83d800f0000cb00000000000066428aa000105e00000009e000001d40000333a7ee000000055a95760000000000202618207ce40192100000000a8503a4a368148476000000000008ea92da03f8fec0000000000000000031b67be000000000000000000898800000000008a7000000021d47fcb08c31e80004952a6a000000000000000000000000247c00021dc45c800000000000000000000143000000007d80000d7d00002fc18981ad3502000000026c8000008800000033ae000000055502d200034d8abf123800021d6d30800000018d400000001589a3e0000662d8500000000aa800000000000000c6c8000000036e00000000002de2000000000000002a20000d74193000000006310000dba000000000005ad80000002dda14328c6c1d800087c800079d80000001a3c5d08000d758a2a000000000000000003068000000000017a298380000000d8c0000dd477800002c1a93c0000000000007800002ceb2fa3f64c524ae00000000002c3cce400000000f9c000000000000000000000000000066880000000000159000027e000000003ce80710ce760800000000002a004e0000000000003bac69020c00009541d6a6600000ad421e80000
  | 54 => 0xa5380004f500003009d4a24a1edc000000000000000002a823768912000000000030e4d330000000000000000000000000000115688d86da00000000002eb8b27000012800000001716000000063e0aa6902330a0001a34acd800033e032e2e7039c0001cd80000fd000021024db2a1c0000e526a0800051f996e0000000000000052421e28b68bb005416c47ecaaced820f3e00001162390000000000037e8000000000058002c4000000000000003d6800000000006b8000000000004d420185d18000000066e0000000000000000000003aa80000002dbca04ae76d1e8756c5a00008d025aa00000000e58000d049f700002f5000000005318000000000007caa4e2630000000000000000000001464ab5b75a12b80000000c3e00000001fe00000001352000000000000009f625fc000364e0001da22bd8000000000017503bc00000000002d086500000871837200036466b4a3c200000000000000970800000000000000000000173e000000000000000000b5000020a036e00001f5800032b000012980000002a4c0000000187301854b0000aa9000091d000000000005931e429d5800000009cc72006ecaff8000000000000007de00000000000bf861700000000000ad6a138000137a58f80000000000000000000000007788000c180000536000000015e2307800000000000000000000000000027f6000000000000005ce800000000008a49fa84b300006440000bfa000000000006398c8e28886d83b99c484e933fa00017c600000007110f2200027e0000000000000000000a163bc000000016023b71bfe0000000000047c00010480000000000000000000000002d900000000d81800000000000000f2eabd000000000003208000000258e6d190766b600203a68000cb58000000000000000009912fba00017d8a6c1154a9c032aa3eb56ea95348216920860000c8a00012eeb4380000000000000139600028b8000000078e8000428b70a1558000d9c8000000327e80d828a000000000000000000000c2c80003d1b14400018c06a895b8cb7af146d4912cb1a84bc001ac0c25d8000000000000000000000000000000000000000000000000000000009449f126c614680000001ec00000000000000000029dc0000000000000000012bc0000000abb000036000000000000b22800068b0000581120400000000000000a798000d4290d464a069875f800090db03cd8a00000000a9000027ccd0c80003ab30f800000000ea000000000000000000000271800000000000dfc00000003ba8cb800003da000052a000000081a17a00001bb867a251255a000000000000000fee000000000000000000000000195ace498fa07180000a5ad9496701e21af00000000fba1b98000dbb00007da00000000000000091600000008290
  | 55 => 0x9b200004f035881528000dc400000001df22670000dcd2478000000000020a80002a2400000000000000dab0c7600017e628707ec2d49fba30300007c225e204310700000a726a180000000f6000000000002efcc02b5e60000000adaad6a5bf843600000001e580004fca31e6720782ac3000000000009be0000000137469b81b4a228d74000000058e000059a0000aa5800000000000002416092165a0bc8b0ac458c5800000000000a9eba723140000b9620300009fd31380c181b60000000a800000c471f7603a8f900001a1253994c06c2800000017821b28000000136e00000003d70000c5c8000000000000000007480000925128c1ae00008ee80000170000000000016b27aa00000000002e8c000288617c8d484e5210834a18a439398da508163472e0000ce01c42000000000000000000000000000076c000004085bc0001148336000016418d04a88000000000022505b4000272c6e7ae5a6e8000000015a45561d8e000172e00000000000e4600000000000000476aa161738000000000098d8000b6c80000001ebcd5a198e9861e24d840000935a3a462c091c3060b6a0002fc67ef000000000008689dc0da30b3eba68000ab180006cc07b069415bc6f08f88000000000026d000000000b98000526800052c800000000003c48000dcb054e00000000001a0a28020b800032a43cd33e6249860495806a600002a21ab3122257000000000000000000731000085d2300d499b3c234a9f06b29cb27a296ec76780000001d64815b6748bd00009c3a3384ab006258d80000000000000000000000000000000000000004c90cc000369600028ec0000000000000000004600002f4ad8c8000000296e0002ae81ae800000028d010eadfe0000000076000081a8000000000000031523ea93a80000000193029e4f6000023d800000023cc99d800000012f4000000000000d463083ca8730266d490000000090000000000000f86000000000000000000018567800014b8000000000000000004421bb44f982d000028e800031b0a5409ac0eb80000001b2483200000000000000000000023360000000000000000000000000000000000000000005c603e459fa6945ed00000000000ab40000000000000000005c9224800000000000000aad00008a9131633e8000ade00000000000000370217b91a88a0a0f8c6d275a52000000ab9dc80000000c868f7628980826b78000bdf0cfe00000000000000000000000000000001d760001d66000164098eaea64512eda00000000000000b9fa902dd600009ac80006c8000019da994b5b00000000000589800085a0000ba380001c8000031a286898c99aa33c00004d0aebe99f900263180000001610ccb00000003426987a4d207132a2ddf800000000000001af2
  | 56 => 0x4488000000000045414a4d640e90000000000000007a42db400008a2353238e8008bd000023ae0000000cc800000000000000290a0001f300c9022c0001dea000348457bb1188ec0ca404600009800492a181a7ca4c000097300000000000da88000000295c56500000000000371800094b995e000000000009e66e59fc24868000000334800000007800000000000049e00000000000000000000000008488000a13ab160000000d9680000000000653921c99e8758439893a0da317e3a39b6e3c1800000036380000000000000000000000000becdaf05847e6800000000000aa800037d000033980000002b5c00000000000000000000000000000003024000000000000008248524ad234660fc308a0001d9000000001978000000000000000000000000b610000000000000021b62d00998ae8afea0002a08b3829080000000a02800000013ee0000000cc100004611820be2000000000000000000cf68000c1e00000002890d278000000000000016f600000000a996b096f00005d7aa7c00000001dd373800020301550000ae1acf4308a404000000000004ca3cd9f806c71422caf9164c6080000c100000001798000302e0000000b1005000b583c86ca8ee492d265892c8000996899a8c71cfadb70000d200000c7080007e400000000000000000066c80005f90000000000000032d4000000000000000000000000000000000004718000174000000000000000ac400000000000000000000034c813e136b7180000000b4c800000000008b380002059d4cbea0000000000000016760000a52bff809c28a336e88500000002ca6000000025d166a33d80000000000000000094d000080b00000000000000362e1411c58b8a0000d0b0000000000000001880001cde00032d00000000000000068180000000000ac98000000000000000000000d720c98000221ac967178d5800000000000000af4a4a0b321e9223a905000000004b28a502c0000013c00000000000145185a00000000000000b4d00000000000000000068680000000000cfd94faa9d8000537198a00000000002fc48a78000436240a65c827a00001dc0028000000000000000001488000604adfc70b1552a2980000000000b3c000000000000000000000000000008260001f740000ca80000d5400031c80000000dc38000b648eda7d12f6a05000007d3274c5a933766bd8000000000000026b8083b742c9e87269f4839a66619dc00006dc000000052c099e64d0000000315ca8a14eac6426d2000000000010920dd0000000237637c94f60000000000000000000000c600000000000000000000009a20000000000102800000000000000c8f800000000000000000b3f8000000024e258876400000000000000a2f00009db80000000f5000009c22dd000014c89b86fe
  | 57 => 0xa17969d780000000b260000000894000000028e4cbe000000000006438000000320a0001f5c67d9650c8aa55a000218c000294abef8000000257a0000000d3c0000a8c82507a90f287c1800093d000000000009c70168000322edd30000ad8800000000000001c300000000000000073b1dde0000000000000087d800000026dabfd80000000000000000000000000000000ba88000000223200014d61ef04be00000000002fd80961a0c00018fc00000000000a2e0000000000371c000000000011a6000258200000009a1324400001d20001c740000404b20800026280004d2ac140000000da419526701aaa000020a00000000000000d6d0000000000000000000000000000000000022b2462347c000000002a800053b0000bfe03800000b8a0000000000192c031800000000000000000000048a4e20000000215043a34fa000117e00000003289a440000000c66af42ae100004bc270853c000040919f800000000000000000000000000007dbb2cc2608000000264600004dc00000000000000000000073a00000000000000000000000004891a7e7f38000d6a25fa00023069db2fee31b84ba0c8b6247040000000310e8122abc5539fe200000000000000000169c121297600000000000000000277e1d52ea48108daa000361a861000000000000001c7200034e4ddd8000a2c0000b98ae4000000008f9047a0001192000374e0000000000000000000000001a84000000000028cc865366e0068000c21af78d3f8000000071e00026480002a3600000000002914b8ba78eb44800000016eab9a9016ba2af1a06b963c8e1273e000005a000000000000000001eb0000000000000001a8000000024380000000000000000000000000000000058e1b79e66dd11da000000005d80000000000000000000000cdc00000000000000000102c0002aa03c325c800000000000000bf3b29c5ff086e00000000000000bdd000000000000c8169000000000000000000335e8e414f25ad000000000001b58dce0000000bdc80009ce80007ed21d2b98000000027460002a48b3914ce0000000000046a50f0000000000004800004701ecc0002a06b9e050eb0a824a0000000000000000000000002b6c000057000019f07139a7416596c89dda63e000000000000000000938a7f00004a605d800a2cdc93e000000018d28b28000000000000000005bf0000000000083a80004ac80000000db232d80009198bba00000005b7000000027428f2283e7880560d02800000000000000000a09a9bc000008a000093c0001e1e000000000000002ff8000000000081910f000000000000956000000000000009cc00000000000ac08000776833c6dc08b294ca7c60001e22000000000000008ac00008033362000328c0002320000000000000000000000000000
  | 58 => 0x1231c661ab80000002a5ed519a1000000000000000b92a42eb1580000000fb80000bde000000000000004bf36445d5000000000000003598000000075880001632a522b1a6ca2188000ad616560002088326824cddbb6da342000000016940000000000000044980005251dd0000119e00000003ef213a54f00000000b30000000000004e8000000000000000000000d1c80001a28000000000000016420001cd60000d6a00010200000000000065843b0000000000000000000000000222849a0000dded8c000095c9bac00008fe965a7e4497949600009a4000000000012fa000000000008b60000310d310760000000000000d60000000000183e000000000006c0000000000016443e613ae0000000b91105cca5000000020b60000000d559f84000000074a00009a380000002f8400000007c08000000129c0000b760001d3a00000000001e82000252c0002f6800000000001d7a1e6224e2882900000349426fa24c3db8b2c1b1000000000000000000000000021c8f7c000000000000000000864000000000000008f002120000000000000000002fe0002cbc62480000000c5e00000000210000000178c25f000000000000002aacce280009a0297e2b480002a6204a7fd0b16af98000000074e0000000088a668c0b074038c180600025288e800000000b7a0000000bd02da80000000a142e9607b000000000000000000a6c80000000000000038c000258c0000000000189424bb6ee000000000000000000000000000000001fe00001d60000000000317669e80003e800003481a3a00000002e82cce6499f720002342000218a000223ccfbadb60000000000196628d1d00709000000026b05c31984af186723a206f00000d7e1b080000000000000371e4e48a740658000000000000000000000408abbb69c138800000000000000000000000063d920c658000000025a0d31909ac7a0000000000002d80000000000000000073214c400011c40000000000000000000000a080000000000000000000000004ed00000000000000111478c88ee00000000001e3400000008c3849600000000000000cc48000000186e73a90e00ce0000dcc0000000000000000000000000000000000000007ae11be00020d606f01fc95b00007a11b9400000007cc8000a878000000000039231f60001e4e2169ac676f000000036340000000007000000000000000000b2a9e8cc7a8b98ac507b89308000ca0a77400000000000000169b09a00002caa1c0000d420000000000068a000000000000000cca0000ff40000000000277000000006ae000000000000000000000174c000030000008a800000002fa1acc0001ca20001aea000000000000000000000000108e441ac06000306a3a2b4161f6159aca817260000b4800022d400000005efad448b
  | 59 => 0xb8800017133320000000cf216c000000000000000d0000004cb0000000289a0000f162bb8000000000073e15ac3828000a0802100000000000000000000005f0000000000000000df80000000000253e0000b2e00000000001750000000000000000002024dd1a486a5a80c844808ec000208076b15928480e040000000000000000000000002f34000096cc6231f863d00e4000000000000000000000000000000000004d0000000000000002ac850fb4e0225a5f6719139c2ad800000027669b7875c40400000000d3400009c60000000000092c00000000e526fa00034e2000290c0001c1600030b88858b36817b2341f9000000029f60001ce4b9d00000000000ca793440672cc2152231870fb0b4380000000014e063b99180002a0a00026aa605800000000000000000000297468980009aa0000c4000000000000000054000008c0d8000000000000000000002d0000c94b72a942b5ba30f00006fc8000000324050400000000000000000065e000000000000000000000340e5fe800050600000000c9c283800000000003fe80003b180006c60000a788000afe00002c70000000000061ca00831000001db8000000000000000000001196000000034580007920d46d2e00000000d2a00000004ff8000397b54a0000000000000083932dad2689b44c92c6e000000070200000000000d0d8000000069e35a000000000000000274b60338600034f20000000000000085f80000000000000000000007680000000478a11ad1b8000ad900003010000000000000000000000000000000054700000002c4a11b0000000000000000001128000c688000000000000000009c90e6cd5218caa07278a014814e00008580001d7400000000000000000000000008a0714800000000005340000dd896204bf91b8693233073402307438000aadab50000011e00008baade80000000000000000000000000000000d438000d738bf2ced80008b980004c68000c2f80000000000752000000002d816800000000000000000059e8000000264cc0f80c04fc151e00034ea0c21168128891097c000062780000000000cd380000000ad0b7e13ac0000000c92000000000000000000d5c1b02c56096a0000000000000000000000000000000000000031280178000ac000000fe09d4d830000b77a4b80000220147b2c80000000000236c238800000000000000000000000083f800000000000000000c520d040001c940650d8a521822e0000000cf1358cbb314ba5d115e41a327bca2a0000c5980000002918b6080000000000000271408d8000ca42664443a0e6640984a000000000009dc0000000000000000000000000000000000000018d600000006618000cf5800000007a0000000000000001da80001291292000000050c80000000000000000000000
  | 60 => 0x9532fa425c8000dae0000d9a000054c000000000000000ecc00000006fc28ba9728b08d73233ac9c800000023161c900001f50000000018eb8193fc0001e6c00031d6bf78abe0000000da500000000000cd29c84675105200000000000bda6c3800000021a416a146000000003c122226812f96ce58000b1200000002a80d5d0000000000000000004cbadb8ba789f6645950400000003dc00004e7b6026f996aa96b800066c0c2a2900000b0700000001d46af200000001bea00000007d0ae3e2c0b44400000005a20000849aad400009b04eeb58a48a00001b41ef60000000d1a90660000000000377a000000077903fcbb600006fd800084ab5a4a51000047536f000000000001a76000117c3c00000b689e70c3782b85e299b6000067e080000000021ce00013384d500000000000000000075000000002e0065b08e064e2110000000071f17b85949a0271a806e013978e0000aeac478c16000074663a11020000000000000000007320000000000214000020ca000007edd5000050a80006b580003f1b3d233400000002cd219195f4000000000000000000000000000050306240001e125da2b56b262fb4d6997ba0d70000adf8000000232e00008da00000000000000147000000026220000000000000000000003368c32c88000000029885e9b3585f225ea00000005f08000000000000025e836f80b800000002830000000000000000000001f62c4f800018ea7d0cea1d5c036b3422580e4ac241ee600006b23cc0ed4da680006c21b1e0000e82000000000b80000000000000202850223fe0000a68adc14d2a9580768260dc20001afc571a99a00032f4c578f200000400168800000001be0000b8c8afa2dcc9f27061bb9ca60002f6e000000000000000000000000000000000000001c5600013de6679a8ab9900008fc800000032860002b10000000000000002091cbe0000dfe000000000000000000000d6da5b200000000000000a548000000000000029900000000000000000000000002bb8000088451c0d9aa9033c0000000042f000000000000001b000000e1c7f704d089494ac3930000000000000000008240000000269c2a1a074000000000016fa38d8852000083400014ae21d000090c800000000001d080004662fca0002a66000131cd898000cfc800034f998c599000013b2a74a70800000000000e41f000000000011000000033cc00021b25a891d23ec88c43069d843650000000000000025940000000514982c0000000b7e80000000000d4017287822c6600024200002b12b1ca59a00000005770000000107e00003ea0000000000000000011b4000326600000000000000000000073f063e000000000000000001d500001b900000000000037000000005db80000000000000000000000004
  | 61 => 0x303205180400000000ae8000000000008d300000001e2c0000c0e4dfacb4000097065c0000b638000000000000000000000000000314000000000000000b8e243020003b6000000000000320000000000000000032b0237b0c8bfd00000000000b0980000000000740837c00000000001be40001d180001b7a000279800000004130000000148e1c60000bcf1ae200000ee00028f60001ea6000074a0000000d862d7600029b600012d0000000001200007ffa65200011a0000000075aa3c4d9800000001a16a65800027b800000032bc000000000000000000aa20000000aa680000000000734800032e98a61ba92629ab2d20c5883b8000101ed98b04e0000ab0d4c9bde6288000361adaeda625884e3000000000000000000000210000000006d98000d90b4f8000000000000003b3a5ec0002cee8d9862c26a14cc10405c0a49af641100000b1180002418000bcb8a924ba268c0000a6e0000000000000000000008a226be4f180003218000c09b0ec0002dec0000000000138e0001ee400000000000000d1e00000000000000000000000009170b34d9400006da000069c8000b5800006ad2bc05cf00009750e96000000000000004ad800000000000000000000000000035d44c335582f38520721b6cc3d3000000000000000290000000000011740000ef86450be058785dc00000000001b6cda10000c5080000001450b7580001caafb612a80000000000c83084a9fa0000000000000000008a036aa1fc271000029fac8a0000889800071b881e00000000000000000094200000000000000000000031400000000000000267000000000002a9c0000000c00800000011900000000a0b0e4200017885f889ec1c58000000000009480000001f7e00000000000000000097a8741c9a00000004570cea0000000000000000000000380000000000000000000000f72000236a00000f2d7e00000002daa62592dc3131e6a0002ee42e78fd86f71aac000353839db45e0000000000073e000135ecec800000024801a193d600006fa0000000000000016c00000000060c6f000000017620000000000000000000000000000000033e00008207c5800077d00000000000d36aeb2da080006c325e0cf780000000000daf8000000000013eaa0200000006281c603de2af2933851834d8986db38a60456287a000186200000005fc8000076abb642d9474bba8cf20002d308ef111ecc7ad4c0000000000000000034d400000000001f260000346000000000000000000000000000000000006d2000000000009de18f248080000000000000000000032ec77c000086b90d61bf2b4e0000000b5780006029d387d1ae7c72f000000022245a988f24aea60600000000000000000325c0001c020ff80008272f66d6f3714000000000000000002d580000
  | 62 => 0x1a9200000000000000000115e6101206c5f04c2bc40c140000000da9179200036e2000000000029ae0000000000261600000006e2a4e8cb88000000226e0000000d7a80003732a3ac52b040c2717ae6c68d50c849e88598332239900000c6a27290700000001cca00000008b5a9d87a1b65c8581a5e00000000000000229800000029fecb9269889634a200033be000362a0001866000000000033a4d142b1a1191e8e0000000be080000000000000316a00023d041b8000000000000000000002aea0002bfcd4a0000000000000000000000fea0000000473800067080000000000519b0385ab000000000000001246a6a8000000000000030820000000aea0ca0000162c00024fe36c000028480000000000c21010e48e88ce91a8000000000000027a80de0000a13000000000001c2800000000000000000000000025680000002834d6b0000000000000023de80d0000591927067122b800000003e5ab2c3092608dd4018cd710a020002e20340000062e800000000000000000b772d8cc12b5ec00c1f7ca0ea56a009213000022ea2ef80009bd812c000000070ab45c000000000000000002e880452ca0000170a00000000000000000000092d9ac0000000000000008de157074ab38e23a0000d0520a22d50000000000000000000ac2f3a00000000002dd417480000000000000368a0000000000376859f2edc3ebb4a4000000000020048dc9d687f7a13c0000000d2f00000000000a9c8000cdf00000000000000000000000000000000000000000000000000000c6a8cfcaeaab0eda99a5828dae48389000000027f8c1e80000000000c19ac180001a880001f0cd5e30d80002936000000041880007fa983a6d52cfc479000000000000000000d4a80000000d62aab9dca089b3440001734000083600011faa5e0000795800038d09040000000c26000000000000000000d0780007951248a30800000034baac7aa5000000006ce00000001e0e2df10ca0000000000073409780000000000000000017eb5c6000000014d1e588d10000000000000000000000000000000000000000000000a0d8000b249bec4cea1ea5b78ba28fa28142be0ac00c48000a908d5e76480005cc174e0000000000000040daf20000000000000000bb29586ce80000000000c3f0000000160600000000002a64d788000a51a95a9150d5200012566aa2c7c00024460000000000307c28180000c78000000000000002c60003678000042a0000026af880000002f2647c80000000000490a56400001ac0000000000000000000000000000000000000000000000000b518000000214400000000001aa40000000d54815e3d78c367511b400002a2c26e8000b7aa7ec0002cf2000000000000003d58000a4c80000002c640292d6687e01a2000000000000000000b72
  | 63 => 0x8b0b800010e2ce800000000000000000000000000004802d50c8c00005fb828442616704321be039e857600000000001e68087935c0000000bb98000000000087f8000c7e80005210c483f1114e000000000000000002880000000092e80006b21a8c5711d302990000000081251e800093700000002f280000160000286a00000000000000856000020680000a6a32600000003db0000a118b800b50000000000089a000000000006c994880000000000000000013aa0000000000000000033607c725b6aac868e724ab7600000000000a1e00020c600000001f32eec85a800000000000000e100000000000220e1540f18a489a9800037365559f4a7db031c0000ddc72380000000000000320ed08a21c83a0000bd1183881c8516b4a10f6440132265080000000000000247a2ca80000002574b03af5a1ac270a0002e7a00000009bb800000000003e3000000000003780000000000000000000002a84000000000000000000000794b18c0000000000000000015e06ab800026835a200029e02952c448d2a782b0fb72e00000005fa000000024de00000004fe8000000000066b82be6c4169200030fe0000000000000000000000000000000000000000009288000383800059b8000b0280000000000bde80000000c1200007f23f200000000000000000020f80000000000000000000000005dc0000000000000000000001444798800000026e40000000799000000024aa000000036b83d00cca10e003a04ea67000000000006a6800000019ee9c808b4c8528728211ec6bcc00009108000bb28430603374a000000000006900000000000000022a800000000000002266000000000000000002ee000007300002f620000b4400000000000d1a0001a4a00015b65f333f8b7c0000ae200005ae000076a000000000000e780000002520000000000037706a000005ab8000c3423f8000296446c19880001f8e83e90b41e3859cc2d8d22000089800000000002fec4ae00005d6800005c00001f6913000000002a68000385000000000000000000000000000000000000000c421a5c7e50000dde00009eeb6e6aa3000024c0588746a5083f08000d550000000164a00000008ae800000001a60440142000254ac1209e2aaa33e2c9418860000a1800000000001e4000000000001f640000000ce7000000000000002c22460800011a0000a9800000002d0a7d980005b800000230650d11800000000000000130000310ca46a7ce0000000000364a000000000000000000000bbda4a80ba2cba3bb80002d6977e81880008eb229600006680002a469e1800000000005a3800089e00000000000496ac4ea3480007ab00001c6ab060000000000000000000000000000000000000005d6000000000000000000000000000000032005d6124ac798000000
  | 64 => 0xb133c78400005b6800000000001fd00005fa800000000001f7370057b1fd03b821ec0000fe800021d800000006cfb71a7660b140000000cba11380000000192b59254980004200000cff800041a800000000006b5000000000002e20dd6000000000000000000000000000000013cc0002ec4a11243c00002c000006005f68a1433880008c68000000000000028c40000000b9580002d9098000000003af8000cfa325a00000000001d36000016a0000000000000030e2dc600003f20001d800002cde8198000a691ada00036860b0800083b80000002362526012e0001ab22f180009290456cc68d7000000002778000d8e8000000000000010ba0002d70000000046f000063b0000202000047b800000000000000000827826000000003e7a1a60600da6b07a0127e9800003eae664e1a2a20000000a2d99fa0001c7a00015e8658851200001544d200000000000335800000000000000000613800000013f42d5800000000000000000000000066e8b4e00000000002eb06e91cdaa3a8c4a0000000000089a0002328562800062aabec554000000007e2000062ed85800000000002ca20d242a0876acfb0aed72157c1090134000154079b841a00004d8945ae8093ea68a8d3800000000005fb00004309eaa8038636342a64a0000000a2223480000000cee03de00000004f90000477000000000009da00003111f54bea80968d7a3ee00007a841b2dba0002cb035280008228fdc0002dc0ced000000000004a11414000086a2ad137200000000001d2c91300007e900000000000000000021089d60000010000000000005de8a695140000630000262c00000008180092278000043033c200015fc0000000000000000000008b81524000000000035e4179800000020dc89580006f032c4000000000015da00000007039abe0002c8089d1616000363e00504800002d8a96780003bdb0743b7af8cac280009cc800076c8788a16000096880008b000008640000aa7871c849284200006540000000000000000000000000000000000000025f200015aa000321c6e382f04dc15e60001e3000003485ef0c4e4b02cf64d380000002f380001f0400016d20000000000000000000002ba02fa0002fb2a96000000000000001ca473f800000000000000000cf934c038980000000000b960000000000081f800091780005138000048800000000000000000000000033d00000000000000000000000002a1235c0001b1634ba90e000151a281025c55c800000000008f70000395acb600005da0002cc604e2a3400000000000000000000000000000000000817210400300002edac4292f20c00001ea000000000001ea200000000000000000000086c0000000157abf08000bc5ac360000000000000000019a40468b580002bc28e0042c000359e000094
  | 65 => 0x8200000000000000000022831d00000001170000000000000000000000000000000003020000bb8b23000000000007e5800012380008d925866d28000d0fb3145bc08d64932ad80000000c038c7c3f5800000000000001f98000000000000005d000008da0000000309429b266a0000000000000000000000000000c3d8000000111c57f834486712d648b3054000108220b93eca4f882ccc2000025e188400000000000000931800001a0000c8107f600000004b911520000000792b1a80000000000000038f0000000000000000008f580000000000000359600015a89c88fbebd700007ff000000013d0000256211880000000090000219e000000000026a0157a25c0001ad000000000000000000000000000009dc8eec0001cba944034000020aa00000009189efc0001d3e6149034293825a72606d4000000000033aca3580000000000b8780000a3000000000001c0abb458aa23e3ac9a2221980000000000a6a15a2000265c00000000000000000203c0000000000000029d81640001e7c41a00005162500af2b146000000000000000000000a2b00008168000000224442c2c5a0b2377400031de3da80003e008d8a632a8abf5160a1c180000000000000344a000000000000000002ec2785341c87000004c4a186000042e00035b80000df0000161a6d72a7e3ad000000003ec000017400000000000000862000000000004389c14000189cb5e00009b60000b7a0000000276419d1ef4be38e402fd205439cb2ac05c8000000000000000001b38000a2780cc0000000000000000000000000e6eb69000000000000000000a018000000000036a2acc2ec800000000000000fb637b000000001126b3a6ba000000061f80008ab00008d48000744800000000005289dc63ae9ec8000000000000009b700000000bcc00000000000000ca2a10a3b5a5840000000dbf80000000000000000000000009ed0bea00029d2d70b26a0000000d3980001c1000000000000000af049a800000001e80000000000106490780000000000b1e80000000000000000000000000000000000000025a2c6200000007fb8000000100a0003096caa87fe42591fe9fc1e7e000245286080000000806000224214980000000000000000000028088c204427e1ab344501bd4000055a0470db400000000002d00c99000000000007560d0600000000b820105ba318030c000000000004b205e20159eb400000000002874060a6e60000000000000000000000001dfc913890863a8eb0410af0e42f800011f8000000000000000000002d1400e800045180001d10bd650923d287b8000574000045e809a00000000000000501351c54c80000000000000301e51e00005a8027865d04ee4ba99920002cb8000000061ab1c400004f8000000000000466bd107cbe515b4b4
  | 66 => 0xc0000d488000000311a000270486e80000000000000000084580004758000000000000000000910000000000084519e400031cc55d000000000009d100000000000000000065f83927c6069600000000002dd23448f0e00032d80ae800094080000003584000000000000000000000000190a00010f400000000f0b6566b90d424af8d24000000000010dec7893f6000000065d8000000000000005668a112140000a08000243a0000136bcaa0580818cc8d183194000000000000003ca914c000212c00034caa860000409b6769d60000a72800045b9a4e00015ca9ec855200000003c2b2b4c4a8ed0000000042a80c2700000077b937c00031060000000c670000000000000000006b980000a800002c78bae0002b54000263096d3664643310ab50ad6e00002023bf9512909800000000007d6800000000002f9800000000006a980000000000802b4d2000000000001ee4e000000001f78507000000020b04228000000000000027ae000000000020c206297768868000d8d800045e2a982b80a7c98300000ed04440ceb4de997aef09b00000d5e819247d00005d9ae4e81e119c3a1a46e21f0c8400000005f3800098a8000000000000009960cb13a614c2f02a4e2568db1000087280000002e520000000c6e9f9e01c8a4439c116c11380000002c7eae40000a888000151332443429800000c880000000000125c00000000002fa2000317a657191e786ab209870e840000000b83936660f0000000000000000006200000000000000000000001bbe00009ce2652e6ccd3324ab658946b6f956c0000000bc0000000000000000000000000000000000001fe000000004bb119a00005f600000000002fe48ea00000002d5c00008280001e780000000000000000037400000000000000000000000a7269200000000000000000000000016120000af40001848b08353000000000000000000000000000004efb2a60000000536800043680007bb835231900000000000000000000000007e200000000e1e000000000016300baa02a00011ec000000000000004a500007270000000220800028182ef287c0000e442c880007ba12960000000d70331600030ce0002ff22029328000000000000000000000000000000029a000016bc61f0ac80002374000347400020a6089282278990ea25f800041e0000000000000024c00000000000104a00006b6b72355a00000000000cd456eb0c40001ed262c80002f8800015d01669310000416000069c20e027e80000000000000305000003600000000000161c00000008dfb5fc00028620000000000000021c2d1c2a2970474f016289a8218000101c00004b818081e674100000003418b4ea8f400026a40000000000000000028f000000000002552aa885cc000000000000000000000000000044ea6
  | 67 => 0x857819e1b3000000000000e232b23539518a8300007cd84e60000000000000000000003e9a7502db2aba00000000000000b8c800040aa2026c5000000000008968000c4d80005be00000003752000220a000000000026c40000c7000015840a20000a2531f00d2b45400032fa00010b26d9330c000184200000008268000a9e000000013320000ab800001e0b9c00000000000ce8000075780000000f740000000000000000029046838000a67b19808d182a0000000939800028c9e5a00000000000000000000000000000000000000000000002043940a1000580000000000823186c28b1e9a8c093a2000000000019eabee30c06e19438000305e0000000000000031e0000000000000018de05e861e0001baa0000000754a324a4414f823eb68e42916ca00025fe00000000001d4e2f70000730a412cf1800010700000000000000095e00000008559b5e9d00ec0758183400000001e7800000000000002382000000034991ac4c40000a912ac467c81c800000000000000000219603f1390a9700006162f0aa8980005ea95d41af800000000001bd30922d7aed2000000098b80002231fae406984c0000000170800044d000048bb374000000000000005938ba600008187d2000000000000f482da00000000000d6623f2a1200022bc51200000000000000000000032f0cd4888057e8000000000000000000000000000000000000001b188909238000b020000000000010f803400025800c3973617f0aba000000000026cc3bf0000000000000015c8405322cd4f0d90000000000003c60001b4451280000001cc60000e60d5a8ea43ff8a4238c80000000000000247e000000000000000000cec00000008b0800000000000000000000000000000004b48bca02b936842797f800005f082e99c6a618582000000000035d200000000000000b012b300000000000118a9a5800000031ae00000000000000bf700000d90000000196a0001fd40002cec8a9872c8982e349100f262c103c4150971c78e2940a6d246c7e32c0000000005568000000207698d10f800000000002ec0000000006e061000000000001fe4c11800000024d4d848000608a1da223942800007b260d8000ab7000000000009ad13e20000000bccb21e3198fe600008be2c60acec6b0000b89199c94e280ccc42666aceb30697136581df9c0c7068000b7417e04780000a7b0000000000058c80000000000000000091d800005f0000abc00000003088cff189088428ce11782405dc80007619d24a23273c1e6b0a6a5b2a3c877a7e6c950536000036a5aa000000000009deab3c9cd80005a1367c78a00001140000866800000000000000000b048cc00000000000000000000000000000000357e00015a60000000cec000000000000001da40000000000000000013b26
  | 68 => 0x244400036fc9b5800089e80000000000bfc0c7e000000000005100000000253800000019e0000000097b80008e31c4607d1afe0000d645eca5b0984074c000056a31a80000000000503800034780000001df852a800000000000002ce211629ba8238000000000000016140003080000167856380004a0000026a84d61b22a6c3c70000000000000000002a500000000000386800000000000000000000000008e3506b4580000000000a5880007c8800000010180000e08d63a192c05a53618600007c2800058a21e4000000069e1c9edc9a824000000000000006e1000000027c2000000000000006e3000000019503c5000000000000000000000100476b800000015d200000000000a248fe9a64000043c000196837a99da0002a926ee80002bb00007102b68c3c80000000000000000026487280001a56ba5305200000000001c28d1db16c701800090a000009f931ea648000652000077d8000916000030220ac000222e000000000000000001f34614000009a000041684c0d7784b291c00000000000000000027f80000001cac8549308000000000000005c380008a300000000000c76000040e977874997085ea0000b54a72a00000000000000000000036b20fcbd7aaf60001074000000073524e090f8000000000000031540000000000301a000000013d80000000000000000088480000000cae000217200000000000000b171e720001ac2000000000029668bcb0b00bf00005eb00000000000d7c0000ae78000000000000000002fe80000002b4600000000000000648800057aa5be00000000000000000000000000000000000000376662e32360002e5c000000000000002070000000000000000007e825a608eaf7e5ce14dec0d0000000059400001780000000000000000000000000c988f62a8e0000000000000000012d46d88b4a0001b2c524a956000000000000000000dee3d380000000000000000000018fe000000000032ae83529e4bc8abb0b9a00000001fc80000000844800000000000000000000000046b8000000000000000000003210000021a0001c54b850000d2d903c82f28103250ad600000000000000000000000001b24e6814a3da0000000136a00000002c800000001e060000000ac1000000001260001e0cd510f2c5d92cb20001f1a00000000000000000338800000000000000a73800090321620000000374a3ca000000000000000002efe7ceaab80002624a520000190b368adf0000000000000000006f8800000001762970000000000032d231000009bc0000000d4d0000d19130e45280004318b4200014fe3d9181c723155e00017128310000c65834e00033dc45aa39e000000052817b000000000aa0000c2e800016e0bf6125035037a00000001706c69800020400000000
  | 69 => 0x232acce9f0e64732265b40000274076c0000000000000000000004221eae0000000000000000030cc000000003c00003f329c4cd026d40000000000000000027900001a6036e80007172d9e0000000000049e00000000000000b2200000000000000000000000007aa000016b8000000000000000000001326b4b800003400000000000b4e000081300000002e020000000000000000000000002f800000000000000000000000003364bd19ff0ad0000019380e2d2d265634400008bb35be0002d7e00000000000000000000000000000001c0a0000000cb382b683c285cb2a356c000000002e80000002e086e980000000000000000000000000000000000000000000000000d768388b9a0000000000000000000000000000000000000011cc00019fc0002afe948800099c80000001bd801e8a560000000000000096eb492000000000005ba00000000002e160002e305a32eee5db2e8660a21fcd7ba960c1f887ec82248a00000005680ce0bae8000000000000000005df32ca2279fdaa282b9c26214760000000000000000004e4000000000000000000ab2738000084726fc0000000bf32ea07ca056c000000067f908c28e01dece52ae2000246000000000002bc4000346220100009f7af1c00000000002a6849e80000000000cfaad4a1faa8ee00032f25068a66b241c502f4ab8c95f9ed09190766c5904b6000000000014a80000000000000000aabaca7a9b4c690922a00015b080faae0567181e4aa3594c36b39a5ca9c704e10c2ec91b28e0000000a8c0000000022a0000000d7800000002d2200000008cc800000009ae2be80007ba96be6e000000002bf4de0000075c0000000000003a21be0002dd8381aafa0000000000240200000007ed8000000000000017d00001578000000000000000000058000000000000000000000b23a3704cc0000000000016a80002c3000000000000000000106367a9ef8000000000000017320000242db18000000060a6158000ce88000ce30c8c7ca80008e7214699e0000000108600000000002e0c0000000000156e243000000000000001a9040e000000000002e0800000000008a50000000305a20f2cfa00026f272c08889c98000000352c00000007cf80000000000000336aa1b03ac000000000036e000000000000000000366600000008e48414000000000000002e38000000000000013765e00000010800000000000001b34185a63c00000005de80001bd80000000000000070000000000001cce00000000000000a4b9be800002bc73014bc000336c0000000520b12000025460000000000000000000006e080009000a3c0000000000141200000002df80005a68fe400000006f30000000000000000000000a62000141e066085e000366aaca0000573b4b00001bfc00000000003504
  | 70 => 0x8b8bd4800035eb586470abe40000000747800073b80000000000c05000000000000000000aef30a00001e805889e0200034a0ac70f621f480000000000000000038300000000b24000086c1e52b9a6650000000000000000004ad00000000b6000000000000000000000000000005aca800b3280001618000000000023413985608358aca800067380004be02f65100c900001a520003262984a0500000000000000000000000000000b0426900000000811000000000b00002e26000000000000005e9000009a800000000000002d0c0000000000000000036d6d0b800079326a2b67366c000000000021aa3d480008db8000bbea2a000011ba000000095f04ea000079231c8000000000000000000000000000000075b00000000000000021c00000000000f4000000000000572000000006e80000000000000000000002e4cf60beecca0d965a59598000330200000007f000000000e160000000ad780000000000000000062b00000000000000000086f1e040000c56051000000000000000000000255400f800021400000002dee5d49db67b090440000000000000000000002d1800000000001f800000000cee72a8000000000000021c481000000e600000000000000000029e02cc000000000000000000000000000000000000001dc20000000a2fa30a1b91dec0000000d8380000000000a740000000144200001a4bb580004d91a9c00000008148000be18000000000000003b0a37a7162f080000000498000000000000000000000c4c0000ae92ca453d1f14000320688000000000000000000046189a6d018000000000000000000000000000000000026140000000000000000004d400000000000000000000000000000000736000297c00000000000000000000000031708aa274ad5423569d501b0b36adc476d2a7abeb31a0a3213460000000000111200000001a72e820000caa8d182dc000331c5fd34c8000004a6a5b6ca0000000564147c7458000ad10000000000043ba12800000003d2000000016ee1dc000008220cca88000013380000000000000000000000360000000000070e0000000da807b652f861293c000091a0000000000057d800000000000310000000000049000000000a4c0000000ca2226c00014620000b1a1418000c0c32d20001c9649b80002cc80000e28d3000000000000000d13202e000000000000000000000000145c0000000afc00000000000000000007e0a1a6da90e4000230c0000000000000000021a80000afe0000000000000001b2e4c1fb800000000000000000af52d0437400009c0000000036f8000013c000000029f80001049d10b58aea80000000b1a1e9eb0d00000000000000179c00011b20000000c4b2ffc00000000002c940000fde3660000000000000004060002398000
  | 71 => 0x8e8a25e773962464f17c40002eb600000000000000bb3800000000000e1279e97d25c09478000000253cdcc80004048000000241a50b1c6206a0000cfd337a2d9a0d06ba29dabd313200000000000171a00000003bc826c0000000000000000000000001e5e0001116ca00b388e68000d5931fe13f9ddca0080000000000000000000000000000000000000062680000000000000028e000355c000041e00000a80001e7a119800000000007e0800000000000000000000000000002f81a500000000000000066400014680001c040000000d48111000023f4000000000011e84f09c4a0000000000066683d31d47d49f383f51000677800000000003040000945000000000000001ca80002a1078a80000002132000000000000000000000b268000000000000027383b8800000000000e0b3caac2000089c00000002d74000000000000000000000d008000000000000000000000e8c000000000034f4000138a00000005f580000002c5432599e2000277c0000000000000000000000003300000000000000004a19fd280780002b28000000000000012ae12d0478000000000000005a29e74906000000000003d100000000000d45285200004acc3d000000000000003372465244a0dfa28600000000000000000155cb1629827c900005658a3a00000000000000a4d00000000f240000000000000000000000000000be81874000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5c65dcd524400193ec9b9aa4880032719373549100043fc2aed212200487c855da42440018f0cb38484880032ed92709091000c7c432e12122000c78655c242440090fd0bbb284880021f61776509100043fc2aeca12200487c855d9424400117f08bb2848800237e0d76509100146e41aeca1220008f7815d9424401117d0fb2284880061fe1d65941100051fc22cb282202aa3c84596504408f4f1013b4a08811f9c04276941101551f436c928220eac3e76d9250441d3e6021b24a0883a70fdc7649411074e1eb8ec928220e9e1f31d9250441d3c3a63b24a0880021fe1d64941107361f3b0c928220e7f301019250440010ff0eb14a0880028fe1162941101551e422c52822000a5f8358a504404b4b906b14a08811e1f21f655411014e3a38ecaa822024a3e86d9050441d387cedb20a0883ab0fdc764141107561eb8ec828220eae1f31d9050441d5c3a63b20a0883a70f9c364141100071d386c8282200087f8759050441d14f700b20a08820a8fa18641411073e1f3b0c828220e6e3b6019050440010ff0eb10a0880028fe1162141101251e422c42822000a5f8358850440474b906b10a0881ce9ee0162141101571c324a120220e5c7a761424044049c70c828480880038e193659011072e3d3b0cb2022000e386419640440015710ca14808808a1fa1b75501101561e326eaa02202487e87d9540440530f90fb2a80880030fdd764501100061e3aec8a02201fcb471d9140440538f0ed28280880a75c1c650501101163c3b0a0a022024e386414140440558f0edbaa80880035c1c775501101263c3b0eaa022029c7876d9540440458f0ec32a80880038e190655011001e5c3b6e8a02201fdb071dd1404403f970edb22808808a1f21975c81100061e322eb902202987f87d9720440010fb0fb2e40880030f9d365c81102645e432e99022000c3f655d32044001878caba6408807e2fe1f64c81100045ec3ec99022000c3e75d93204400187aebb26408816f1e9d8508811037f1c320a1102205bc7a761962044001c70ca324408808a1fa1b75481100061e326ea902204d87e87d9520440530f90fb2a4088003171cf65481100061fbaec89022000c3c75d912044001938e7b22408800317d9773481100062e32ee69022000c9f64dcd2044001938c9b9a4088003331cf624811000c7b436e29022000cb464dc520440538f0ed282408813f9a18a504811014eb838ca09022022c787614120440cbc70c8282408813f1e1db7548110006b838eea902204dc78761d520440538f0edb2a408808b1e1d8654811000c7c432e890220019f0815d1204403f970edb2240881332e1d864481100071c328c8902206ccd876dcd2044001cd6ca31240880039ad95200811014e3b3b6cb0822004c7676196104403f96cedb24208800f2d9d86484110
  | 1 => 0xf03baac8880021f60775591100062f98eeab222000c5d31dd5644400187eebba2c8880030f1d774591100043fc2ae6b22200487c855cd644400117f08b9ac8880023be09735911004476412e6b222000c7875dc1644410987cedb28c888003879cf65191100070eb9eca32220e7a3f81d9464441cf47b03b28c8883b387cc765191107670e98eca32220ece3970d94644400117b0f328c88839a8fa1665191100045fc3aca32220ebabb8059464441cf47d0c328c88820b0f9d865191100070f398ca3222000e1d7319464441cd47f02328c88839a8f604651911072f0f988ca32220e5e1d3119464441cbc72e0328c8883978ec40651911072f1c080ca32220008bd8798c644400147d0b318c8880028f61663191100055ac0cc632220008bf8758c644400147f0ab18c8880028f215631911000557c12c63222000aac8258c64440010ff0abb2a8880022fe1176551100047dc02ecaa2200387e87d95544400917d0fb22a888002b960432d891000574c0065b122000c3e74d96624400187ce832cc4880030fd9574989100061e32ae93122000c3e75d92624400187aebb24c4880030f9d464989100061eba8c9312200087e87d956244001878e9b2ac488003171cf65589100043f438cab122000c3c7419562440018b8e632ac4881cf1edc065589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd62440090fd0fbaac4880021fe0775589100043ec0eeab122000c5f31dd562440018ba63baac48811e1fa03755891001c5f43ee8b122000c3f75dd16244001878ebba2c4880030fd4774589100061ea8ee8b122000c9f31dd1624400193a63ba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440011bf03b9ac4880023760773589100062fa8ee6b122000c5d51dcd62440010ff0ab9ac4880121f21573589100045fc22e6b1220038bc845cd62440011df04b9ac48800237a1c73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100066639ee4b122000cb474dc562440018f0ebb82c4880023be1d62189100056641ac431220008bf845da524400717908bb4a4880031ed9670949100065c324e129220018f8865c25244001970c8b84a48800e2fa1376549100045ec26eca9220028de839d952440011bb073b2a4880021fe1576549100045fc22eca9220038bc845d952440011bf06bb2a48800a3720d76549100047dc02eca92200887e87d9552440018b8e7b2aa488003271cf64549100062fb2ee6a9220e1
  | 2 => 0xb754821023c3e436ea904200087e87d9520840018b8e7b2a410800317d9773482100062e32ee690420018ee87d89208408fcd0c528241081cf1edd850482100063dbb0ea904200097a87d9520840016e303b2a41080025ea1c654821039e3dbb0ca9042000b718119520840033e102ba241080067aa1f6248210005f0c0ec490420009ea87189208408fcd6ca31241080023be1d620821023e3bb2ae21042047e6b654802084001bc2e290041080030f5d254d95100053cc04a9b2a2000c5d7394f65440050ff0ea9eca8800b179cd53d95100052f418c9b2a2000a5d83193654400147d0931eca880028f61263d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d95100061eba0e9b2a2000a5e831d365440014bb063a6ca880029ea0074d951014d3cc00e9b2a2000c5f739cf65440018bae639eca8800297a0f72d95100052ec1ee5b2a2000a3e849cb654400147b09396ca880a69e60072d95100052f41e85b2a2000a5d83d0b65440010fd0e216ca880021f61c42d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d951014d3b40865b2a2000a75810cb65440014f500196ca880029e60032d951014c3f43e81b2a200087d87d0365440014bd06206ca880029760c40d951014c3f43e61b2a200087d87cc365440470ff0e986ca880a61f21d30d95100051f42061b2a2000a3d840c36544001878cbba2ca8800e2fa1f74595100061fbaee8b2a2000c3f51dd1654400187aa3ba2ca8800327cc774595100064e98ee8b2a2000c3c50dd1654400187eea3a2ca880021fe1573595100045fc22e6b2a20038bc845cd65440011df04b9aca880223b20973595100065c3a6e0b2a2000a5e8319065440014bb06320ca880021f61e63195100051f424c632a2000a3d8498c65441db4f301318ca880021fe1d63195100051fc22c632a2000a3c8458c65440014df04b18ca880029b20963195100061ebaea9b2220028bf8750f64440011bf06b96c88800a3720d72d91104270f98ecbb222084e1d31d976444105c3e6232ec88820b874c465d91100051f42cc7b222000a3d8598f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400187aea3aec88800387d4e53d91100051f42ce5b222000a3d859cb644400153f06b96c888002a720d72d91100fd5cc00e5b2220008be8714b644400117b0e296c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c88807eada0432d91100055ac0865b222000aba800cb644400157300196c8880028fa1730d91100051ec2e61b222000a3f854c364440014790a986c8880022fa1c30d91100345ec3861b222000c3c64dd564440010fd0fb2ac8880021fa1c65591107463db80cab22200487e87dd564440010f
  | 3 => 0x1b2c20f1c7a70d0365840010fb0f986cb080021fe1d30d96107863d38261b2c200087f855cd658408f4f501320cb080021f61e63196100043fc3ac632c20008df835cb64840051b906b96c90811e5ea0375592100043f43ecab24200087e8719564840090fd0fbaac90800317cc775592100062e98eeab24204787e80dd564840010ff0ab9ac9080121f21573592100145e43a86b2420008fa809d954840010ff0abb2a90800e1fa1f655521001d1f426caaa42000c3e74d9662841dd4f501b2cc50811f1e9c36598a100061f3a0cb3142047c7a70196628400187ecaba4c5080030f1957498a1023cbd406eab14200087e87d9562840018b8e7b2ac5080021fa1c6558a100062e398cab142000c5f65dcd62840018b8cbb9ac5080121fa1f7558a100062f98eeab142000c5d31dd5628408f0fd01baac50800a37a1f7358a100062fbaee6b142000c5c75dcd62840018bea3b9ac508003175477358a100043fc2ae6b14200487c855cd62840011bd0e39ac50800317dd47358a100062e3a8e6b142000ad5811cd62840011df0eb10c5080063e61a7094a1023e3db2ce129420038be849d9528400117b093b2a50800a37a0e7654a100046ec1ceca9420008fa809d952840010ff0abb2a50800237e0d7654a100146e41aeca94200887e87d9552840018b8e7b2aa5080229ba0b6554a100062fb2ee6a9420e1c5c65dcd52840010ff0abb485080121f2157690a1000c7cc34e12142047c78659c242840018f0cab8485080121fa177650a100043ec2eeca14200087f855d942840090f90abb2850800237e0d7650a100146e41aeca1420088be87d91428408f4f100b2ca1082521fe1d649421023c3e43ac9284201b87f8758a508408f0f90eb14a10800297e0d629421012d2e41ac52842029c77865c6508408f8e90cb8ca1080a75ce01719421023eb8402e32842047c76605c6508408fae4c0b8ca10811f5c901719421023eb9102e3284200187e87d9550840010ff0eb20a10811e1f21d64142100043fc3ac4284204787c8758850840014bf06b10a10808e9720d62142100263bc32e22842047c74865c4508408f8eec8b88a1080031d591711421023e3bb1ae22842000c75635c4508408f8eec4b88a1080031d5897114210116b9c02e22842047d70805c4508408f8ecc0b88a10811f5c981711421023eb9202e22842047d72205c450840015770ca14810807eec20542902100043f43ecaa0420018be87d9140841d18f6ec282810811f8e190505021077e3dbb0eaa04200097a87d9540840016e303b2a81080025ea1c65502107463dbb0caa042047e386419540840016e30232a81080066ea1f6450210005d8c0ec8a04200087d87d97208400187ce9b2e41083ba9ea0365c82100061fb2ae99042000c3c655d320840031f30dba4410811e1fa1
  | 4 => 0x5080030f90bb8aca100021fe1573590200243e42ae6b2040088bc8750d64080110f90eb2aa8100222f21d645502004476412e6b0840088f4874c561080030fb0bbb2a2100022fe11765442001c5e422eca88400187c8759551080111e90eb0aa21011f1ed947054420004f4c10e0a884001a7481dd9510800147f08bb2a2100da8f21176544200053bc0aeca884004a768758551080094e90eb0aa21011f1d1c161544202ff33902c2a88405fe722058551080bfce240b0aa2100039c58770544200053cc30e0a884000b69821c15108001ce2c2382a21011f1e61870544200063d320e0a884047c78641c1510808f8f6c6382a2100031e58c705442023eb5410e0a884047d69821c1510808fad4c4382a21011f1ed84705442023eb9308e0a88405bc79611c1510808fae2c2382a21016f56cc470544202deac988e0a8840018bc8759141080111e90eb0a8210006b5207764c4202f566412ec9884000ad7815d931080055ad0eb0a621000ab521d614c42000d6bc12c29884001ad5825853108001d8ee4b0a621017bb11c9614c4202f763902c2988405eed22058531080bdda240b0a62100231b9c9659402023d3c402cb2804029e56614c65008001caac298ca01008b1d985711402023cbc402e22804047d70105c450080018eae2b08a01011e9e2016114020006aab8a622804022e56614c45008001caac2988a0101bf1edd850500200066639eec9004000ccf31dd9200808f8dca1bb2401011f1b143764802000637bb6ea9004000c6f761d5200800199eedb9a40100031bddb514802023db5406a29004000c6f765452008001ccac2a8a40100027321d314802000667bb2629004000ec5614c5200809b6d50f282401011f5aa1e504802023eb5bb4a09004000e6b769412008001e96e728240103cfd21ce5048020005b4c0ca09004000e696194120081e7e96632824010003d24c6504802023db5c2aa09004000c3d74953658408f4f5012a6cb080029e60254d96100062eb9ca7b2c200287f8754f65840058bce6a9ecb0811e9ea0264d961078e3d384c9b2c2047e3a4099365841e18f4e0b1ecb0811f0fdd274d961023e1e3a2e9b2c2047c5f739cf658408f8b8e6b9ecb080a69da0643d96100053ac0c87b2c2000a3e849cb658400147b09396cb0811f1bdca72d96100052f41e85b2c2000a5d83d0b658408f0fd0e216cb080021f61c42d961023c3f43865b2c200087d870cb658400147d08196cb080028f61032d961014d3b40865b2c2000a75810cb658408f4f500196cb080029e60032d961023e3b382e3b2c2047c79879c365840018f4e9386cb0811f1e1d270d961023e3db9ce1b2c2000c79739c365840018f4e5386cb0811f1e1ca70d96107963cb8ce1b2c2047e71719c365841e5cb663386cb083cb964c670d96100043ec3e8
  | 5 => 0x3179db654c5200062e3b6ca98a4000a5f81d9531480014bb03b2a629000317dc7654c5200072bb8eca98a4000e5621d9531480454bd01b2a62900a697203654c5200046fc3aca98a40008dc8759531480014bd0c32a6290003179d8654c5200062e3b0ca98a4000b558119531480011bf0eb2262900023721d644c5200052fc2ac898a4032a5c8559131480015af02b226290006b5205644c5200066c3b4e098a4048bd1819c131480bd5b10cb826290003361d9704c5202f5e4412e098a4053bd3815c13148001998c73b64290006b920564c852000c77434e190a4000ad6864c521480015a90c98a429000395d95314852054f2a32a6290a405efc0204c521480018f0cbb8242900031e1947048520006363b6ca90a4000e6461d9521480018d8ec32a42900063b21d6448520006663b6c690a4000ec7864c5214800178d0c98a4290002f12193148520007624326290a4001ec7764c52148003d88ec98a4290003d1d953148520007a232a6290a4000ec7644c52148001d8ac898a4290003f0a013148520007e0c026290a4018ec7604c521480bdf86c098a4290003f04c77048520007e0988e090a400887f8759650480014bf06b2ca0900969720d65941200062e31ced282400087d819da50480018be633b4a09011f1b882769412023e36104ed282400087f8759250480014bf06b24a0900969720d64941200053bc0ac92824029a7481592504804b4bd0db1ca090003179db63941200052ec0ec728240f5c5e70d8e50480530f90cb8ca09000317d8d71941200062e31ae32824029c74615c650480010ff0fb0ca0900969720f61941200063ab8ec32824000a5e864c650480014b90c98ca090003179d9319412026e373b6432824047a6c8648650480018dcec90ca090003d14c5219412023db440243282404fc6c72d9550480018b8c73b0a0900021f60676141200062f98cec2824047c6e209d8504808f8d8413b0a0901369e60364141200043fc3ac82824000a5f8359050480474b906b20a0900029de0564141201153a40ac828240f4e384059050480474bd0db18a090003179db63141200052ec0ec62824066c5e70d8c5048001cb4e1b18a09008a1f21971141200062fb1ae22824000c5c635c450480458e8c2b88a0900021fe1f611412011d2e41ec22824000c7571d8450480014bd0c988a0900029721931141200062f3b2622824000d55714c4504809f8dced908a09011e9b2192114120006373b2422824000d65714845048001e8a62908a0900222fe1d64901200fd5a40ac9202404d87e86dd540480018b8c7baa80900921fa1f655012027c3e43ecaa024000c5f75d8d40480018b8ebb1a809013f1b9db6588120026373b0cb102406ccce76d8e20480038dceca8c4090002b3219318812000e673b263102400887c8754d6
  | 6 => 0x46fc1aebb0a40028dc835d761480014eb023aec2900021fe1574d85200243e42ae9b0a40008df835d361480051b906ba6c29000317dd773d85200062e3aee7b0a4000ad581dcf61480010ff0ab9ec2900121f21573d85200062fba8e7b0a4000c5c751cf61480015ab0239ec2900021fa1f65585200061e3a6cab0a4000c5c73d9561480010fd0e32ac2900030f1d065585200062e398cab0a4000c3f65dd16148001878cbba2c29000a37a1b73585200062fb2ee6b0a4000c5c65dcd61480011bd0fb1ac29000317dd763585200062e3aec6b0a4000c9f74d8d6148001938e9b1ac29000237a1c63585200062fba8c6b0a4000c5c7518d614800193ee831ac290003271d063585200062e31ceda8a4000c5f319db51480018ba633b6a2900031bc8676d45200063690ceda8a404787c809db51480018f4213b6a2900031e44276d45200043fc3ac9a8a400487c8759351480014bf06b26a2900de9720d64d45200053bc0ac9a8a4001a7481593514806f4bd0db1ea290003179db63d45200062e3b6c7a8a4000a5d81d8f51481ef8bae3b1ea29006e1fa1a70d45200062fb1ce1a8a4000c5c639c351480051bd07bb2a2900023760f765452000c3f43ecaa8a400187c8759551480014bf06b2aa2900d69720d65545201ad2f41eeca8a4000a5d83dd951480010fd0d3b2a2900031718e76545200053ac0ceca8a4000c75819d951480018be633b2a2900028fe1176545201b51e422eca8a4000a5f835d9514806b4b906bb2a2900029de0576545200053dc02eca8a4000c5c631d951480090ff023b2a2900121f60476545200062f988eca8a4000c5d311d951480018de423b2a2900031b48476545200063d180eca8a4000c79301d951480018f6403b2a2900031e08076545200063d080eca8a4000c79101d951480010ff0eb22a2900021f21d64545200052fc1ac8a8a4035a5c8359151480014ef02b22a2900069d20564545201ad2f436c6a8a4000c5e76d8d51480018b8edb1aa2900029760763545207b62fb8ec6a8a4000e5771d8d51480018bec6382a2900031718c70545200243f42eeca0a400087d85dd941480051bd07bb282900023760f765052000c5e43ac8a0a4001ab48159141480654bd0bbb2629000297617764c5200046f434ec98a4000ad5819d931480019ab033b2629000317d46764c5200062ea8cec98a4000cd6219d931480014bf0abb262900ca97215764c5200054fc22ec98a4031a9c845d9314800159f04bb26290002b5e05764c52018d4f420ec98a4000a9d841d9314800193d083b2629000327610764c5200146fc08ec98a40028dd811d931480018bea23b2629000317544764c52000667908ec98a4000cd6211d9314800199a423b2629000336600764c5200066d080ec98a4000cd9101d931480654bd0db2a629
  | 7 => 0x7765dc564480018e8cbb8ac8900033518f71591200243f43eeab22400087d81dd564480051bd0fb9ac89000317dd773591200062e3aee6b2240008dd81dcd64480010ff0ab9ac8900121f21573591200047bc0ae6b2240018f4815cd64480011bd0e39ac89000317dd473591200062e3a8e6b2240028bc8750d6448181968e2a1ac8900063da1f71591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf71591200063bc2ee2b224000c7485dc564480019af07b8ac8900033520f71591200063bba8e2b224000c74751c5644800196ee838ac89000335dcc71591200066a398e2b2240008de87cc564480051b90f98ac89000317dd731591207ce2e3ae62b224000cd771cc564480039a8e398ac89000a37a0f76551200046ec1eecaa2400087f855d954480011bf06bb2a89000a3720d76551200047bc0aecaa240018f4815d954480070fd0fb2aa89000e8fa1365551200447d436e0aa24000c7b651c154480018bcedb2ec6900029760765d8d200046ec3ccbb1a4000a5e8599763480011bf0eb2ec69000297a1865d8d200062f3b0cbb1a4000a5d8119763480011bb0f326c69000297a1664d8d200052ec2cc9b1a40008df8759363480014bf0ab26c6900029721564d8d200056bc0ac9b1a4000ad48159363480018becab8ec6900031719571d8d200052f42cc3b1a4000a5d8598763480251bb0e30ec69000297a1461d8d200052ec28c3b1a4000a9e84187634800153b0830ec690003355c461d8d200062eba8ebb1a4000e1f5495363480b35b501b96c69000237a1f42d8d200046ec3e85b1a4000a5e859c763480014bb0b38ec690002a7e1171d8d200054e422e3b1a4000c9f845c7634800193908b8ec69000297a1471d8d200052ec28e3b1a4000a9e841c7634800153b0838ec6901b2b3a0871d8d2000566c10e3b1a4053ada801c763480d95b30038ec69000237a1e51d8d200046ec3ca3b1a40008de8714763480011bb0e28ec69000237a1e41d8d200046ec3c83b1a4000a5e8590763480014bb0b20ec69000237a1c41d8d200046ec3883b1a4000a5e8510763480014bb0a20ec6901b2b3a0841d8d2000566c1083b1a4000ada8010763480015b30020ec6900023761e21d8d200052f42c43b1a4000a5d8588763480014bd0ba06c6900029761740d8d200046f43881b1a40128dd8710363480d91bd0f886c6900023761f10d8d200052f42e21b1a4000a5d85c4363480011bd0e086c69004a3761c10d8d200052f42821b1a4000a5d85043634800153d08086c690002a761010d8d203656741021b1a4000c5c73d9552480011bd0db9aa49000317d97735492070e2e32ee6a9240f88de87d8d52481c31b90fb1aa4900031ed9470549200062e39ecbb0a4000c5c7319761480018b8ea31ec2900029d60775d85200
  | 8 => 0x728eca9000297a0e64d95200052ec1cc9b2a4000a3e8418f654800147b0831eca9000387a1063d95200070ec20c7b2a4000a5d8118f6548001cb30031eca900031718d71d95200052f41cc3b2a4000a5d8398765480290fb0e30eca900028fa1061d95200051ec20c3b2a4000a5e8318765480014bb0630eca900031d5c461d95200052f43663b2a40f9c5e76cc76548001cb0c7186ca9013e9e21930d952027db441261b2a404fa7980dd3654800187ee93a6ca900030f5d074d95200051f420e7b2a4000a3d841cf65480018bae639eca900029ea0073d952027d3cc00e7b2a4000a3e84dcb654800147b09b96ca9000297a0f72d95200052ec1ee5b2a4000a5e83d0b65480014bb07a16ca9000297a0e71d95200052ec1ce3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a404fa6e821c765480014db0438eca900029ea0071d952027d3cc00e3b2a400087e8790765480010fb0f20eca9000297a0e41d95200052ec1c83b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a404fa6e8210765480014db0420eca900029ea0041d95200053cc0083b2a4000a3e84cc7654800147b0998eca9000387a1331d95200070ec2663b2a4000c5d71cc765480458bce198eca900a7171c331d95200043f43c63b2a400087d878c765480010fd0e18eca900021f61c31d95200043ec3c43b2a4000a5e8388765480014bb0710eca9013e1fa1f40d95200043ec3e81b2a4000a5e8310365480014bb06206ca9013e1fa1f30d95200043ec3e61b2a402387f874c3654809f0f90e986ca900028fa1030d95200051ec2061b2a404f87e87c4365480010fb0f886ca9000297a0f10d95200052ec1e21b2a400087e8704365480290fb0e086ca900028fa1010d95200051ec2021b2a4000a5e8304365480014bb06086ca9013e9ba0810d95200062e32ee6b2a40028de87dcd65480018beebb9aca900023760773595200062fa8ee6b2a4000c5c50dcd65480010ff0ab9aca9000237a1c73595200062fba8e6b2a40008de87cc565480051b90f98aca9000297a0e64195200052ec1cc832a4000a798099065480010fb0f318ca900021fe1d63195200051f420c632a4000a3d8418c6548001c3d08318ca900038761063195200052ec08c632a4000e598018c65480018b8c6b88ca9000297a0e61195200052ec1cc232a4000a3e84184654800147b08308ca9000297a0c61195200052ec18c232a4000c757118465480014bd0d988ca900039618e301952026d3c4326032a404db68824c065480010fd0fb2ac890003171cf65591200063a38ecab22400087e8719564480018b8e632ac8900031d1c465591200062fb2ee6b224000c5c65dcd64480018beea31ac890003171d463591200066a388c6b224000c
  | 9 => 0x31487202f6e3bb26290e400cec7764c521c80bde8cca98a439017bd159531487202f763b226290e405ef86644c521c8001d8ac898a439017be1591314872000742b226290e4000e1f3159250c809fc5e42b24a1901370f9c1649432014c3fc32e32864000c3e645c650c800187ac8b8ca1900a71d98571943200063ab8ac32864098e1e644c650c8001c3ac898ca1900a79598531943200072ab0a632864000e2d6448650c8001e8a6290ca1900031b59772543200070f98ac8286404de2f2159050c809f87ce0b20a1900038e9c164143201143fc32e22864000c3e645c450c800187ac8b88a19008b1d985711432039eb8082e22864000c757158450c8117c3cc8988a190003875913114320006aab8a622864022e56614c450c8001caac2988a1900038b5912114320006b2b8a422864000f453148450c808f6d100908a1901971e5d850903201271d320a1206400087d86dd540c805587cc9baa81900aa1fa1d65503201243e43acaa064000c3f7559140c8001878eab2281900032b59372503201263dbb0a0a064024e3a6414140c800717f0eba6cb100030fd4574d962023e1f282e9b2c4047c3c505d3658800717d09b9ecb100022f61373d96200046ec3ce7b2c4000c9e749cf658800193ae939ecb1000a37e1d73d96200064f3a2e7b2c4000c9d745cf65880011bf02b9ecb1000317d4573d962023e2f282e7b2c4047c5c505cf65880050ff0ea9ecb1000b179cd53d96200146fc3e63b2c40008dd87cc765881f593ce998ecb10003275d331d96200065cba4e1b2c400487e85dcf64880010fb0bb9ec9100030fdd754592200145e43a86b2440008bd849d954880051bd073b2a9100023760e765522001c3f43ecaaa44003a3e84d9554880111f30c382a91011f1ed9470552200065cb20e0a1440028de83dd561880011bb07baac3100061fa1f65546201b51f426caa8c4000a3d84d95518806b4bd07b2aa3100029760f655462000c3e43acaa8c4036a3e849d9518800147b093b2a3100d697a0e76546200052ec1ceca8c4000a75819d951880014ef02bb2a3100121fa1776506200043ec2eeca0c40028de831d941880011bb063b283100062f21d64506201952f42eec98c4000a5d85dd931880015ab033b26310002b5e05764c62018d4f420ec98c4000a9d841d931880011bd0fb2a63100023761f654c62018d4f426ca98c4000a9d84d9531880015af02b226310006b5205644c620005e4c00e498c405ead9869c131880019b6ed3826310003721ca704c62024de8c0ce098c405ebc8825c131880a97a702b826310047b1589314862023d3c402cb2844047a7880590508808fc7080b20a11011f1d1857114220006aab8a622844000c3d7495365480018bae729eca900029e60253d95200143fc3aa7b2a4000a5e8394765480014bb
  | 10 => 0xb2640008bd87cc564c800193d0f98ac9900032761f31593207df4790e62b264000a3e858c564c800147b0b18ac99017aa760e31593200455741462b264000aad828c564c800147d0a18ac9900028f61431593200455741062b264000aad820c564c800147d0bb82c9900028f61770593200051fc2ae0b264000a3c855c164c800153f06b82c990002a720d70593200055bc0ae0b264000ab4815c164c800147d0b982c9900028f61730593200051fc2a60b264000a3c854c164c800155f04982c990022ab20930593200d45f43860b2640008bd870c164c800147d0b882c9900028f61710593200054f41e20b264000a9d83c4164c801155d05882c990002ab60b10593200d45f43820b2640008bd8704164c800147d0a082c9900028f61410593200054f41820b264000a9d8304164c801155d04082c990002ab60810593200443e43acaaa640088bc8759154c80bf4eb033aac3901869de0575587200243f42ee8b0e400087d85dd161c80090fd0bb9ac3900021f61773587200447a43a62b0e4000c5f315db51c80018ba62bb6a3901871bc8576d47200063690aeda8e405fc3d7159351c8001c3e62b26a3901878bc8564d47200a43ec34e1a8e4000c3e649c351c800187ac9386a3900061f61776547200443e42eeca8e405f87d8759551c80030f90eb2aa3900032e99370547200063cb28e0a8e4000cba641c151c80090ff03bb2a3900121f60776547200062f98eeca8e4000c5d31dd951c80bf8de43bb2a3900031b48776547200053bc0aeca8e406187f815d951c80018ef02bb2a39000317cc576547200063dc02eca8e4061c3f7159151c8001c6ee2b22a39000387cc564547202ff1790ac8a8e4000e3a64dc151c800187cc8382a3900030f59070547200063cbb0e0a8e4000e3a641c151c80012f30c382a3900031e61870547200063d320e0a8e4000d3a641c151c8001874c8382a3900034e59070547200063c320e0a8e4000c7b631c151c80018f2c6382a3901cf1ed84705472039e3cb08e0a8e4073d5b311c151c80e7ab262382a3901cf5ac84705472039eb4908e0a8e40088bc84dd941c80051bd07bb283900023760f765072000c5e43ac8a0e4001ad481dd931c80015af02bb2639000297e05654c7200052ec0aca98e40fbc5f7159531c8001caee2b2a639017b95885654c7202f72a90aca98e40fbc9f7159131c8001d2ee2b22639000387d45644c7200070ea8ac898e405ee8f2159131c80bdd2c42b22639017ba5485644c7200156b43ac298e4002ad48758531c8001cad0ab0a639000395615614c7202f769102c298e405eed12058531c801195ee2b224390023a9dc5644872000717a8ac890e4000e2d5159121c8001d1e62b224390003a98c564487200074698ac890e4000ea53159121c8001d8f0c98a439017bb1219
  | 11 => 0x50153ca8ca98a42a000e1fe1d659414014c3e432e32828029c74615c650500010ff0fb0ca0a00031d5c7619414023d1e432832828024c3e7650650501178bcec98ca0a000395d85319414014f2a30a63282802ac3c74d95505000187ecbba2a0a03f38e10362141401143e432e22828022c74615c45050001a7080b88a0a00021fe1f61141400063ab8ec22828047a3c86504505005587ceca08a0a00034d5c5411414023d9c402822828098c5e764c45050001aaae2988a0a000395d8531141401172a30a62282808bf18404c4505005587cedb2c80a00ab8ed8365901400261f3b0cb20280038bc865c6405003f968c2b8c80a00028fa1b51901400051e432a3202801fe94614c640500110fd0f2a2cb900030fdd254597200053cc04a8b2e400887e8794d65c80018bee729acb900221f21d53597200162e39aa6b2e4000a5e8394565c80014bb0728acb900030fdd274597200052f41ce8b2e4000a5d839d165c80014f5013a2cb900029e60274597200062fb9ce6b2e4000c5d731cd65c80014bd0738acb900029760e715972004537414e2b2e4000a6d829c565c80014f700b8acb9000297a0c71597200052ec18e2b2e400087e8790565c80010fb0f20acb9000297a0e41597200052ec1c82b2e400087e8710565c80010fb0e20acb9000297a0c41597200052ec1882b2e4008a6e8210565c80014db0420acb900029ea0041597200053cc0082b2e4000a3e84cc565c800147b0998acb9000387a1331597200070ec2662b2e4000c5f71cc565c80010fd0f18acb900021f61e31597202f52ec1c62b2e400087e870c565c80010fb0e18acb9000297e0d70597200052e41ae0b2e400087e87d0165c80010fb0fa02cb9000297a0c40597200052ec1880b2e400087e87cc165c80010fb0f982cb900961fe1d305972011c3e43a60b2e4000a3e840c165c800147b08182cb900021fa1f10597200043ec3e20b2e4000a5e83c4165c80014bb07882cb9006e1fa1c10597200043ec3820b2e4000a3e8404165c800147b08082cb9000297a0c10597200052ec1820b2e4008a6e8204165c80014db04082cb900222fa1f54593200061fbaea8b2640088be8790d64c80111790ea1ac9900028fa1641593200051ec2c82b264000a9e8390564c800153b0720ac990022aba0a41593200061fbaceab264000e1f5394d64c800147d0b38ac9900028f61671593200054f41ce2b264000a9d839c564c801155d0538ac990002ab60a71593200051f428e2b264000a3d851c564c800153d0638ac990002a760c715932004557410e2b26401aaad821c564c80355750038ac990002ae60071593200054f41ca2b264000a9d8394564c801155d0528ac990002ab60a51593200054f418a2b264000a9d8314564c801155d0428ac990002ab60851593200045f43e62
  | 12 => 0xaa8fa1030d95400051ec2061b2a802a87e87c4365500010fb0f886caa000297a0f10d95400052ec1e21b2a800087e87043655003d0fb0e086caa00aa8fa1010d95400052f41821b2a8000a5d8304365500014dd04086caa00029b60810d95400043fc2ae6b2a800087d8798c65500014ed03318caa00029d60663195400043fc3ac632a8000a3c8650c65500014bd07308caa00029760e61195400052f418c232a8000a5d8318465500014dd04308caa00029b60861195400063ab88c232a8002c9e7350f62500cb8f2e032cc4a00021fa1f65589400062e39ecab128000c7471d9562500010fd0e32ac4a0003171cc65589400063a388cab128000c5f65dcd62500018b8cbb9ac4a00031dd9771589400063a32ee2b1280008ef8758862500051bd073b2a4a00023760e76549401561e3a6caa928000c5c73d95525000187ecbba2a4a000317d97735494070e2e32ee6a9280038fa86dc152500018f6ca382a4a00029d60775d85400053ac08ebb0a800087f855cf61500090f90ab9ec2a00021fe1572d85400243e42ae5b0a80008df835cb61500051b906b96c2a000a3de1d31d85400043f43ecab0a800087e8719561501ff8f6e032ac2a00030fd0e76d45400061ea1ceda8a8000c3f419db515000187a833b6a2a000317cc676d45400062e98ceda8a8000c3c409db51500018f4213b6a2a00031e44276d45404a43f434e1a8a800187e87d9551500030f90eb2aa2a00021fa1a76545400053ac0ceca8a8000c75819d951500018be633b2a2a00029de0576545400053dc02eca8a8000c3f431d9515000187a863b2a2a00121fe0476545400243ec08eca8a8000c3f411d9515000187a823b2a2a000317cc476545400062e988eca8a8000c7b401d95150001878803b2a2a00031e10076545400063d080eca8a8000c79101d9515008fa7080382a2a00030f1db65505400071a30ecaa0a8000c3c76195415001517d0c38282a00026760c70505401952f42eec98a8000a5d85dd931500015ab033b262a000297e15764c5401952e42aec98a8000a9f845d9315000159f04bb262a017ab3209764c5400056bc0aec98a8032a5e86d953150001ca8c3b2a62a000297e07654c5400052ec0eca98a80fec5f71d953150001caee3b2a62a000395887654c5400056bc0aca98a8001ad48159531501314bd0c32a62a000395184654c5400054e432e898a80fdb97815d13150181d28c2ba262a0006b5207624c54000d6b436c298a8000e5765d853150001ca8cbb0a62a000ab5a1f614c5400156a43ec298a8000e5785d853150001ca90bb0a62a0002b560b614c54000c77414ed90a800087f855db21500090f90abb642a000237e0d76c85400146e41aed90a800487e85dd921500010fb0bbb242a0003359d931485400066a3b26290a8000e57654c521
  | 13 => 0xe3db08e0908a047d72611c121142058f2c2382422811f5c584704845000638b08e0908a102d5b311c12114205ab26238242280223ba0b73d964000476c16e7b2c8101cb9749c3659008f2f100bacc52000a37a1f7358a400046ec0ee6b1480008de87cc562900051b90f98ac5200023be1d6218a400046fc1aeca9480028dc835d952900110fd0fb2aa5200229ba0b6554a4001c7cc30e0a948047c7b651c1529001117d0fb2a852004e2f61b7050a400052fc1ac5a8c8037a5c8358b51900030fd0fb2aa3200ab0f1d3655464000c3e43acaa8c8000c3d65dd15190001878e93b2a3200029d60676546400053d404eca8c8000a77815d9519000187aedba2a32000297e0d62546401ad2e41ac4a8c8000ad5819d931900015af02bb2632000237e1d624c6400046e43ac498c80018ee829db21900011bf06bb6432000a3720d76c86400243f42eec90c800087d85dd921900011bf06bb2432000a3720d764864000c7643ac490c80039ac87509219001155f0ca12432017bb1989314864000762b126290c8000f85424c5219008f4f100b2ca1200030f59574942400052fc1ac52848025a5c8358a509000167700a14a120263c6d0131942400052fc1ac42848023a5c83588509008f4f100b10a12011f1d18571142404169b20ae22848000d55714c4509000147b0929ecaa0003175ce53d95400053cc04a7b2a800287f8754f655000147b0928ecaa000297a0e51d95400052ec1ca3b2a8000a768198f65500014eb0331ecaa00038718d43d95400052f41cc3b2a8000a5d83987655003d0fb0e30ecaa000297a0c61d95400052ec18c3b2a8000a6e8218765500014db0430ecaa00031d5c461d95407ce2f3b663b2a802aa3e841cf655000147b0839ecaa0003175cc73d95400053d400e7b2a802aa79801cf655000147b09b96caa000297a0f72d95400052ec1ee5b2a802aa7980dcb655005547d09396caa00028f61272d95400043f43865b2a800087d870cb655005547d08196caa00028f61032d95400053b40865b2a8000a75810cb65500014f500196caa00029e60032d95400052f41ce3b2a8000a5d839c7655005547d0838ecaa00028f61071d95400052f418e3b2a8000a5d831c765500014dd0438ecaa00029b60871d95400053d400e3b2a802aa79801c7655005547d0998ecaa00028f61331d95408070f42663b2a8000e1d84cc765500018bae398ecaa00021fa1e31d95400043ec3c63b2a800087e870c765500010fb0e18ecaa00021fa1e21d95400043ec3c43b2a8000a5e8388765500014bb0710ecaa00021fa1c21d95400043ec3843b2a802aa3e84087655000147b0810ecaa000297a0c21d95400052ec1843b2a8000a7a8008765500014f30010ecaa00aa1fa1f30d95400043ec3e61b2a802387f874c3655004b0f90e986caa0
  | 14 => 0x740585411408f2f50fb8282280039c5877050450004bcc36e0a08a000c7986dc141141e38f6c3b8282283c71e587705045078ead98ee0a08a0f1d5931dc14114001ce2c2382822811e5ee18705045023cbcc30e0a08a047d3a841c1411408fa7308382822811f4e990705045023e9cb20e0a08a047d5a831c1411408fab30638282284134ed0870504500069ca10e0a08a047c7b611c1411408fae4c2382822839b1e584705045023eb8b08e0a08a000c71611c141141cda7482382822839b4e1047050450736ad988e0a08a0e6d59311c141142076af02ba26228002d6e01744c450005ac402e8988a089b55819c931141156af02b926228002d6e01724c450005ac402e4988a032a5e861c931140014bb0c392622822ec7a10724c4500058ec20e4988a000b5a801c931140016b300392622808ad5a06424c450005aac0c84988a000b5a8090931140016b30121262280cb95e1d614c4500072b43ac2988a032e55875853114065ca90eb0a622800395e11614c4500072b422c2988a000e55845853114001ca908b0a622800395dd1614c4500072b3a2c2988a000e55745853114001ca8e8b0a622800395e09614c4500072b412c2988a000e55825853114001ca904b0a622800395dc9614c4500072b392c2988a000e55725853114001ca8e4b0a622800395d09614c4500072b212c2988a000e55425853114001ca884b0a622808b95e01614c4500072b402c2988a022e55805853114045ca900b0a622800395d01614c4500072a202c2988a000a5d86dc13114001caac3b82622813ad5606704c4500072ab0ce0988a000a5f865c1311400163f08b82622822ec7211704c450005a7c12e0988a000b4c825c131140af6af02b82622800395585704c45045d8f420e0988a000b1d841c13114001caac2382622813e1fe1970c8450004afc1ae1908a02395c835c321140012f700ba2422811e5e2017448450005b4c0484908a02296c87509211408f8ef0eb0a42280131d21d61484500063bba2c2908a000c757458521140018eee6b0a42280031d5cd614845000733c12c2908a000e648258521140458eee4b0a422808b99dc9614845000733212c2908a000e6542585211408f8e8e0b0a422808f55e1d314845011eaa43a62908a0a9d57764c52114153aaaec98a4228003d1e093148450007a241262908a022d57724c52114045e8ee498a42282a7d1989314845054fa2b1262908a000f46424c52114001e8a8498a42280a795981314845054fa930262908a000e7161dc12114001ea263b8242280025e61b70484500063cc36e0908a0eec7b61dc121141dd8f2c3b8242283bb56cc77048450776ac98ee0908a000e71611c12114001ea262382422811e5ee18704845023cbcc30e0908a047d69821c1211408fad4c4382422811f5a588704845023
  | 15 => 0x93a2c2280d29d60674584506cd3bc0ae8b08a000a78805d1611400187ae83a2c22800297a0c74584500052ec18e8b08a000a6e821d161140014db043a2c2280029ea0074584501153cc00e8b08a000a3e849cd611400147b0939ac22800317dce73584501953ac0ce6b08a000a7a809cd61141db4f30139ac2283e69de0573584500062eb98e6b08a022a7681d0d61140014eb03a1ac22841b8d90743584501153b40c86b08a000a758190d61140454ed02a1ac2284178d90543584501153b40886b08a000a758110d61140014f50021ac2280029e600435845016d3ac0ce4b08a000a3f845c9611400147908b92c22800297e0d72584500052e41ae4b08a030a77815c961140014f100b92c2280028fa1072584500051ec20e4b08a000a5e831c961140014bb06392c2280031b5c872584500053d400e4b08a022a79801c961140014bd07a12c2280029760f42584501153b40e84b08a000a7581d0961140014f501a12c2280029e60342584501153b40c84b08a000a758190961140014f501212c2280029e60242584501153b40a84b08a00087e8710961140010fb0e212c22808a9da0442584500053ac0884b08a022a7681cc961140014eb03992c22808a9da0632584500053ac0c64b08a022a76814c961140010fd0e192c2280021f61c32584500051f42064b08a000a3d840c961140454ed02192c2280029d60432584500053d40064b08a000a79800c9611408f4ed0e98ac2280129d21d31584500053bc2262b08a022a77834c56114045caf0698ac22800395dcd31584500072a39a62b08a000e57434c56114001cac8698ac2280039550d31584500072a21a62b08a000a77824c56114001cae6498ac228003958c931584500072a99262b08a000e54324c5611408f4e90098ac22801e9d606705845023e3c384e0b08a047e70109c161140450fd0fa02c2280021f61f40584501153b40e80b08a000a7581d0161141e3ce021a02c22800297a0c40584500052ec1880b08a022a768110161140014eb02202c22839b8d904405845023e3c38080b08a047e701010161140450fd0f982c2280021f61f30584501153b40e60b08a000a7581cc16114001caa63982c22811e9d20630584500072a98c60b08a047c78708c1611408fce021182c2280021fe1d30584501143e43a60b08a000a77814c161140454e902982c228003954c530584507873808260b08a000a3e840c1611400147b08182c22808a9da0430584500053ac0860b08a000e55310c161140472bd07b9282280025760f72504501149e43a84a08a047c778758541140098e90eb0a82280038de1161504500071a422c2a08a022c77745854114045c6ee8b0a82280031ddcd61504500063ab9ac2a08a000c77725854114001c6e84b0a82280038d509615045023e3a382c2a08a000e3
  | 16 => 0x25865014d3b40884b0ca000a758110961940010fd0e192c3280021f61c32586500051f42064b0ca000a3d840c961940534ed02192c3280029d60432586500053d40064b0ca000a79800c961940530fd0fa02c3280021f61f405865014d3b40e80b0ca000a7581d0161940014bd06202c3280029760c405865014c3f43e60b0ca00087d87cc161940534ed03982c3280029d60730586500043fc3a60b0ca02987c874c161940014ef02982c3280a69d20530586500051f42060b0ca000a3d840c161940018f4c1bb2832811e4f21d645065023e1e3b2c8a0ca02595e83dc941940012bb07b9283280a64f21d42506500062fbb4ec98ca000b55819d931940016b5013b26328002d5e05764c6500062ebb0ec98ca098b1e841d9319400163b083b26328002d6a00764c650845abc0ae898ca107e1e64d9131940016b501b22632841f87191644c650005abc0ac898ca029b5481591319412d6ab03392632825ed5e05724c6500052f430e498ca000a5d861c9319413163d083926328002c7610724c650005ad400e498ca000b59801c931940012bd0fb1263280025761f624c6504c58f426c498ca000b1d84d8931940016b501b126328262c7a12624c6500058ec24c498ca000e4f6298931940536ad033126328002d5606624c65014dab408c498ca000b558118931940016b50031263280a6d5a06424c650005aac0c8498ca050b55819c13194001ab6e13826328002c7e11704c6504c58e422e098ca000b4f825c1319400169904b826328162d5e05704c6504c58f420e098ca000b1d841c13194001ab2e038263281361fe1970c8650004afc1ae190ca02595c835c321940018f4c1bb2432811f1b9da624865000596c24c490ca04796c8758921940532d90ea12432809755e1d314865012eaa43a6290ca000f47824c52194001e890498a43280a755dc9314865014fa3b926290ca000f46624c52194001e8ac498a4328003d19093148650007a2a126290ca022e56604c521940011bf06b96c8a800a3720d72d91500051ec2c83b22a04fc3f655d262540011df0eb10c4a80061f21574d855000c3e42ae7b0aa00187c855cb61540011bf06b96c2a800a3720d72d855000d3a43ec2a8aa000e7361dc151540170fd0c382a2a80039cd8470545500043ec2eeca0aa000a5d85dd931540015ab033b262a800297e15764c5500054fc22ec98aa031a9c845d9315400159f04bb262a817ab3209764c5500056bc0aec98aa0008df835db21540051b906bb642a80121f219719415014e3a30ae3282a000c7571d86505408f2f70d384842811e5e61a709085023eb5314e1210a047d69629c2421409ba768538484281374e50a7090850006ad98ce1210a04f87f865c242140012f70cb84842813f1ee197090850006ad98ae1210a04dd6b215c2421400187ee
  | 17 => 0xca000ec5624c5219400187cc8b8ec92811f1dd8571d92508070f32663b24a047d3a649c3649408fa72c9386c9284274ed0a70d9250006ad98ce1b24a04793c8750d649408f4790ca1ac92809657a0f7259250004aec1ee4b24a100e1c64cc5649408f87ec2ba6c52811f4e98174d8a501561f3a2c9b14a00095f815cf629408f8bec2b9ec52811f5698173d8a5012e2f39ac7b14a047c77615c7629404b2bf0f98ec5280025761f31d8a508068f3a663b14a000d1d74cc762940018f2c9386c52811f5a98a70d8a5023eb4b14e1b14a000d5b319c3629409f87ec4ba4c52813f0f5897498a5027e9790ae9314a04dc3e605d26294001a74c0ba4c52813e9b61f6298a5023e36c3ec5314a047e2e84d8a629408fc5b09b14c52813f8b9d36298a5027f16ba6c5314a047e4e83d8a629408fc9b07b14c5280029b6076298a5023d37406c5314a047e6a80d8a6294201a3ce998cc528003475d33198a5000727b1663314a02ac3e74d9162940014f501b22c52813e1f21d6458a501561e3a2c8b14a04f87c8758d629404b8b8e6b1ac52811f1dd857118a5023eb5314e0314a047d69629c06294001ab663380c5280031e9817690a5023e1f3b2c9214a04d87f865c2429409f27d0fb2285280030fddb6450a500059d406c8a14a047c3c645d3619408f87ee9326c32811f0f1d164d865023c3e432e7b0ca047c5c635cf619408f8bee731ec32811f171cd63d86500051f424c5b0ca000a3d8498b61940018f4c9386c32811f1e19270d865023e3db1ce1b0ca000c79639c361940018f4c5386c32811f5c98670d865023eb8b0ce1b0ca0f2d5b319c361941e5ab263386c3280a61fa1e64586500061fba4c8b0ca029a768199161940530f90eb22c3280ab0f1d164586500052f418c8b0ca000a5d8319161940014f500322c328097179cf635865014c3f43cc6b0ca000c5f7398d61940534ed0331ac3280a61f21d635865012e2e39ac6b0ca000a3e8418d619400147b0831ac328003175cc635865012caf41ee4b0ca00095d83dc9619400147d09b12c3280028f61362586500052f41ec4b0ca000a5d83d8961940530fd0f312c3280028fa1262586500051ec24c4b0ca000c6f7298961940534ed03312c3280a61f21d62586500053d400c4b0ca000c3f749d161940014eb033a2c3280029de0574586500061eba0e8b0ca000a5e831d161940014bb063a2c3280029ea00745865014d3cc00e8b0ca000a3e849cd619400147b0939ac32800317dce73586500053ac0ce6b0ca000a77815cd61940018bae639ac32800297a0f72586500052ec1ee4b0ca000a3e849c9619400147b09392c3280031bdca72586500053ac0ce4b0ca000a77815c961940014f500392c3280a69e60072586500052f41e84b0ca000a5d83d0961940010fd0e212c3280021f61c4
  | 18 => 0x84bd5ad0d3826290802b561a704c52104e6a3b4e098a425ebc6829c1314840178b053826290802b5e19704c5212f56a432e098a4200b57855c131485536a90ab826290802e5e11704c521545ca422e098a4200bc7825c131484bd78904b826290acf351d8704c521545cb420e098a4200b95841c131484bd78d043826290802f1608704c52154eab3aa63b024200d55754c760484090ff0ebaec09080317cc575d81210062e98aebb024200c7b805d760484090fd0bb9ec0908021f61773d81210063cba8a1b024211dc5724c660484573a90e98ac09080355dd5315812154eaa3aa62b024200d97744c56048551b28e898ac09085771dc931581210047dc3ac03024200a788558060484031db05b98c090802ba608501812100578c08a030242028bc8750d649400147f0aa1ac92800a37a0f72592500046ec1ee4b24a100e1e54cc5649400747f0cb22a92811f0f1d964552501c61f326e2aa4a01e87d86dc1549408f2f50fb82a92800f0f9d15458a5000477c3ac4314a04d87f865c25294055878e8b22a52809657a1f7354a507062fbb6e6a94a0e0e4e62dcd52940012bb03b9aa528387179837354a5070ead306e6a94a047c6e7698952940114df0cb12a5280965720f7154a5030e37316e2a94a01487d86dc15294001ab6e7b82a52800356dcc7054a50006ac398e0a94a0028de839da42940011bb073b4852811e5e2017590a500061ebaac9214a04797a80dd542940012bf06baa85280965720d7550a5023cbc402eaa14a00493c87551429400187eecaa285280028fe1175586500051e422eab0ca000c3c54dd161940014f3012a2c3280e21fe1d54586500043ec3ca6b0ca000c5d7394d619406f0ff0ea9ac32800b179cd53586500146f41ee4b0ca0008dd83dc961940014bf06a92c3280029720d52586501b61e326e8a8ca02ac3e74591519400f0fb0db82a32811e5ea1f705465000738b0ee0a8ca000e71611c151940051bd063b283280023760c765065023cbd406eaa0ca036c3e645d5419408f2f100baa83280062f21d64506500061fbaac8a0ca000ad5819d931940015af02bb263280c6a7a10764c6500054ec20ec98ca000c5d76dd531940018beecbaa632842ad5e05754c65083f0f2a2c898ca000ad78159131940035a902b2263280c697e19544c65018f0f322a898ca029b568194931940016ab03292632800257e1d524c650004ae43aa498ca05ee4e62549319400717d093b643280022f61276c86500146f41ced90ca0008dd839db21940031dd053b6432800257e0d75c865012cae41aeb90ca008c6e625d7219408f2f100bae432811e5ea0375486500049fc22ea90ca02a93c845d521940012bf06baa43280965720d75486502fe37312ea90ca00097b805d5219408f2f100baa43280063b21d62486502f763312629
  | 19 => 0x317dd773583210062e3aee6b064200c5f51dcd60c84018baa3b9ac1908021fe1573583210243e42ae6b064200c5f751cd60c84018b8ea39ac19080b361ce30583210447c43a60b064200c78651c1654840717d0fba2ca908030fd4774595210061ea8ee8b2a4200c9f31dd1654840193a63ba2ca908030f14374595210146f43ee6b2a4200c9f74dcd6548401938e9b9aca9080237e0773595210046ec0ee6b2a4200c5f51dcd65484018baa3b9aca908031714373595210045fc22e6b2a42038bc845cd65484011f700b9aca908023e20173595210046f438e6b2a4200c9f741cd6548401938e839aca9080a1f21d53595210162e39aa6b2a4200cbb74dc16548401970e9b82ca9080336dcf70595210066c39ee0b2a4200c7a85dc165484018f6a3b82ca9080336cc770595210066c98ee0b2a4200c7b751c16548401976e8382ca908032e1d070595210066db98e0b2a4200cd8731c1654848f8f70a382ca908031ed5070595210063da98e0b2a4200c79531c165484018f4a4382ca908031e14870595210063da88e0b2a4200cdb311c165484019b262382ca908030f5d754d91210145fc3a87b22420087f855c364484090f90ab86c8908021fe1573591210243e42ae6b2242008fb805cd64484011f100b9ac8908121fa1770591210043ec2ee0b2242008bf845d954484011bf06bb2a89080a3720d76551210047dc02ecaa242008f8805d954484070f90eb2aa89080e8f21165551210053c402caaa24200ad7865d531484bd5a90cbaa6290802f1e09754c5212f5e2412ea98a430ce5665d9531484573a90eb2a6290802e5e11654c521545ca422ca98a42aebc78259531484017a700b2a6290802f4201654c5216266a3b6e898a4200ad7865d131484bd5a90cba262908cf351d9744c521005e3c12e898a425ebc4825d1314855b78f04b22629080ab5e1b724c5212f66a3b6e498a42b8bc687dc931484037890db92629097b719db724c52185ee23b6e498a4200bc584dc9314840178b01b926290aeef1a1c724c5212f6e3438e498a42babc6861c931484bdd8d0c392629097bd1a14724c5212f7a2c28e498a425ef86841c9314840178b08392629097be1610724c521005c2c20e498a425efc2801c9314840178b00392629097bf0600724c521005e0c00e498a42009d78754931484013a90ea926290802f1a1e424c5212f5e243c8498a42acbc68690931484bdd8d0d21262908e6f1612424c521005e2c048498a425ef8442509314840178d0ea126290802f121d424c52100de34328498a4201bc486509314847978f08a12629097be1e11424c521547c33a28498a4200f85745093148401f0ec8a126290aa3e1191424c521547c32a28498a4200f8554509314840178f00a126290aa3e1101424c52154dab42ee098a4200b5585dc1314
  | 20 => 0x6fc08eca9262028dd811d9524c4018bea23b2a4988031754476549310066b108eca926200c5c501d9524c4bd2b90eb2aa498803171d965549312f5a6412caa926313b5781595524c4033ad03ba2a4988027560774549312f4ae43aa8a9262019d6811c1524c4013ab02382a498806752067690931004ebc0aed21262029d6865c6424c4053a90cb8c849897b65d0971909312f6caa12e3212620095f855c2424c4652b90ab848498802756077650931004afc2aeca12623295c855d9424c4013af02bb2849880276e017650931004ec402eca1262008df865d5424c4011b90cbaa849897a6721d64509310064e3b2c8a12625eb8c82591424c62572f02b22849897a6721d5450931194af42ee0a12620095d85dc1424c6236ab033aec0988ca57e1d75d81311bcafc0aebb02623595d815d7604c4018bec2baec09880355d8575d8131006ab10aebb0262318dd87d93604c4015b300314c098c43745c76098131194af43eeab02620095f81dd5604c4012bb03baac09880317d877558131006abb0eeab026200d5621dd5604c46333d0fba2c09880347dd774581310068e3aee8b026200c9f61dd1604c401b2ec3ba2c09880347d4774581310068ea8ee8b026200d9621dd1604c401a3eea3a2c098803471d4745813118e4e3a6c8b0262318dc87591604c401a9eebb92c098803531d77258131006c7ba6e4b026200d8c74dc9604c401b8f03b92c09880371207725813100667b0ee4b026200dc761dc9604c401a9ea3b92c098803535477258131006a7ba8e4b026200d4c751c9604c401b1ee8392c098803631d0725813100667b20e4b026200ccd641c9604c4bdb8d02392c09897b7160472581317de67b08e4b026200dc7611c9604c401a9ea2392c0988035354472581312f6e4c00e4b026200d5775dc5604c401aa8ebb8ac09880365dd37158131006ca3a6e2b026200dc772dc5604c401b88e5b8ac098c3f74dc7605813100666394c0b0262c19d7815d0604c46333f0eba0c09880365e057418131006ca40ae83026200c9f615d0604c401b2ec2ba0c09880347d4574181310068ea8ae83026200d96215d0604c401b3420ba0c0988036644174181310064eba4c43026200c9d74188604c40193ae9b00c098c3af460660181310046fc3ac03026200c9d74580604c40159904b00c09880276e1d601813186de9c0ac030262028de87dcd65c84018bea3b9acb908031754773597210062e286e6b2e42e08de871cd65c84110f90ea9acb9080b171cd53597210043fc2ae6b26420487c855cd64c84111790ea1ac9908121fa1770593210043ec2ee0b2642008df835d954c84051b906bb2a9908221f21d65553210445e43ac8aa642018ee82dce60c84111f30f184c1908121fa1f75583210062f98eeab064200c5d31dd560c84051bd0fb9ac1908
  | 21 => 0x8758862504031790cba4a4a080a37a0e76549410046ec1ceca92820887c8759552504014f100b2aa4a08222f21d65509410055c402caa12824c8be86dc142504090ff0ebaec0a08da1f60575d81410062f98aebb028200c5d315d760504018f700baec0a08121fa1773d81410043ec2ee7b028200c797514360504011f70eb00c0a08029e21560181418cd5dc22c030282018bd84dcc60504011bb0f398c0a0803275d273181410146fc3ae63028200c9d745cc605040193e84b98c0a0bea37e0573181410062fa8ae63028200c5d515cc605040193c82b98c0a080327105731814123e2f282e63028247c5c505cc605040193e80b98c0a0803275cd421814100578c08a030282c19d7815d3654c4033a902ba6ca9880675a0670d953102ceac0ce1b2a6232c5f76d95654c631aaeebb8aca9880257e1570d9131194ae42ae1b226317d9774dc5644c4652bd0bb82c898802576177059131004eac0eecaa262009cf825d9544c4bd39904bb2a89880275e057655131004edc02ecaa262009d8805d9544c46f3af02baec498b0675e0574d893102ceac0ce1b12620095f855c3624c4652b90ab86c49880267e1170d893118cce422e1b1262099d7815c3624c4018baeb32cc498802b360a659893118c6fc3ac9312630bdc571d8a624c4012bf0ab84c4988ca5721570989318b6e3b96e2b12623295e85dc1624c4012bb0bb82c4988de57e0575189311acaec0aea31262fbc5f615d4624c401aaec2ba8c49897b5588575189312f6aa90aea312620095c805d4624c4018baeb328c4988df355c6651893100566c10ca3126315cd571194624c5f793ec2ba0c49880365d8574189310068fa8ae83126200d1d515d0624c4bdb1e42ba0c49897b658857418931006c690ae8312625ed95215d0624c4631bb0fb20c498802b360b641893118e4f3a2c831262009cf87588624c62978f02b10c49880356e167018931006ac42ce031262fbcdb619c0624c401ba6c3380c49880356d467018931006aca8ce0312625edd2219c0624c4bdba243380c49880257e157018931194ae42ae03126200d5b855c0624c401ab10ab80c49880336d9170189310066cb22e031262fbcdb615c0624c401ba6c2b80c49880356d457018931006aca8ae0312625edcb215c0624c4bdba442b80c4988037248570189312f6e890ae031262019d4819da524c4013af02bb4a49880a75a197194931014ea432e32926242d56855c6524c401aab0ab8ca49897b55d4971949312f6aaa92e3292630cd54505c6524c4013ab03bb2a4988033560776549310062fa8eeca926200c5d51dd9524c4019ac43bb2a4988031714376549310046f434eca92620099f845d9524c46333908bb2a49880275e057654931004edc02eca9262009d8805d9524c4018bd0a3b2a498803176147654931014
  | 22 => 0xb10c0a88029720d62181510053dc02c4302a200a3e84188605440147b08310c0a88031b5c8621815123d3d400c4302a20087f87580605440147f08b00c0a88028f2116018151004bdc3ac0302a200b388458060544014f30da00c0a88038ed9040181510071c32080302a200b598310060544016e302200c0a88d65e61e30181510053dc3260302a247c3f749d0605448f878e8ba0c0a891f17dce731815123e2e39ae6302a222a768190c60544014eb03218c0a891e9ea0243181510053cc0486302a200a7b8050c605448f4f100a18c0a891e9ea0043181510053cc0086302a200a5f835c860544014b906b90c0a891f1b1c972181510052f41e84302a200a5d83d08605448f4f501a10c0a88029e603421815123d3d40484302a200a798090860544014f700a10c0a891e9e201421815123c3f43884302a20087d87108605448f4f501990c0a88029e60332181510053dc0264302a247a78804c8605448f0fd0e190c0a88021f61c32181510051f42064302a200a3d840c860544454ed02190c0a88029d604321815123d3d40064302a200a79800c860544014f30fa00c0a88031e61f40181510053cc1e80302a200e3b43d006054401c7287a00c0a88029ea0b40181517453dc0e80302a2e8a7981d0060545e3c7683a00c0a8bc78e507401815178f2d98e80302a2f1e5931d00605448f4f30e200c0a891f8ea10401815123f1d3a080302a247e3974100605448fcb506200c0a88029e60c401815123f2cc1880302a200a598310060544014f504200c0a88038ed0840181510071ca1080302a247a7b81100605448fce502200c0a8b969e604401815123f38c0880302a2e6e3a4110060545cdc7082200c0a8b9b96cc440181517372c98880302a247a79878c060544014f509180c0a891e9e212301815123f2d39c60302a247e59738c060544014f505180c0a8803968ca30181510072c19460302a247a7b818c0605463b4f303180c0a8c7396cc630181518e72c98c60302a200a7b874c060544018f70e980c0a88029ea1130181510053c42260302a247e5b834c06054401cb486980c0a88039650d30181510053c41260302a2eda7b814c060545db4f302980c0a8bc396cc530181517872c98a60302a200c78651c1655063787eebba2caa08023be09735954104476412e6b2a82008fb805cd65504011f100b9acaa08031ea1770595410063da8ee0b2a8200cdb31dc165504019b263b82caa08031edd470595410065dba0e0b2a8247c7b851c165504018f4a8382caa08031e15070595410063da90e0b2a8200cbb421c165504018f6a2382caa080336cc470595410066c988e0b2a82008dd879cf62506355ab0339ec4a080a37e1d73d89417d46fc0ae7b128200c5f515cf62504018baa2b9ec4a08021fe1570d89410243e42ae1b1282008ef
  | 23 => 0x58951006abb0ee6b12a20093f845cd625446d27908b9ac4a88025de057358951004bdc02e6b12a200978805cd6254401a3ee839ac4a8803471d073589511ae2e39ec6b12a25f87c8758d625446b8b8e6b1ac4a897e9b20963589510069bba6e2b12a200d3474dc56254401aaee7b8ac4a8803551cf7158951006abc1ee2b12a200d5483dc56254401acec5b8ac4a88034edd370589510069c3a6e0b12a200d5b73dc16254401ab0e7b82c4a88035cdc77058951006b9b0ee0b12a200d5b31dc16254401ab263b82c4a88034edd070589510069c3a0e0b12a200d5b731c16254401ab0e6382c4a88035cdc4705895123e3dc30e0b12a200c7b641c162544018f2c8382c4a88031ed8c70589510063cb18e0b12a200c7a621c162544018f0c4382c4a88035cd847058951006ad988e0b12a200d59311c162544bf87ec4ba0c4a897f0f589741895130e1fb0ae8312a200d37615d06254401a3e62ba0c4a8803474c574189512fe9790ae8312a200d2d215d062544012df0eb10c4a8802d9e056218951004bbc0aed212a200c3d76d9242544010ff0cb8484a88021f2197090951004bac0eeca12a20095f835d9425446b2b906bb284a88025de057650951004bdc02eca12a200978805d942544bf2790eb2284a88030f1d964509510059bc0ac8a12a200b388059142544010fd0db8284a88021f61b705095100cbb408e0a12a200975811c142544014f30da06c0a8802d660c40d8151005b8c0881b02a23597b874c3605446d878e9b24c0a88030f5d2649815123d3d404c9302a200a7980992605446d87ce8b24c0a891e9e2016498151004bac0ee7302a200a3e8498e605440147b0931cc0a8803175ce639815123d3d404c7302a200a798098e605446b0ff0eb1cc0a88d7179cd639815123d3c402c7302a247a7a8098a605440147f08b14c0a88028f21162981510052fc1ac5302a200a5c8358a60544bf8dce4b14c0a88029ee01629815123d3c402c5302a200a3e8418a605440147b08314c0a88da4fa1f74581510069bb0ee8b02a200d1f31dd16054401a3a63ba2c0a88021fe1973581510049fc22e6b02a23693c845cd60544012df04b9ac0a897e5b2097358151004bbc0ae6b02a200d3774dc56054401a68e9b8ac0a88034e1d360581510061fba4c0b02a200c3c74981605446d0fb0fb20c0a88db0f9d3641815123d3d406c8302a200a7980d9060544014f700b20c0a88030f5d0641815123d3d400c8302a23587d87d8c605446b8bce7b18c0a891e9ea0363181510051f424c6302a200a3d8498c60544014f301318c0a88021f61c63181510062eb98c6302a247a7a8018c60544014f300318c0a880257e0d72181511acae41ae4302a25f87d87d88605448f4f501b10c0a88029e60362181510051fc22c4302a200a3c8458860544014bf06
  | 24 => 0x6a200a5d83d0a60d448f0fd0e214c1a88021f61c429835123c3f43865306a20087d870ca60d440147d08194c1a88028f610329835114d3b40865306a200a75810ca60d448f4f500194c1a88029e60032983510f43ec3e81306a247e3a40d0260d46410fb0f984c1a891f968c330983518fc3fc3a61306a247e58304c260d44030fb0bb9ec8a880a2fe1d43d91510051fc2a87b22a2008df835cb64544051b906b96c8a880e1f21570d91510065c320e0b22a203a3e86d9154544450fd0db82a8a88930f190705515101e1e3a2a9b12a20187d85dcf625440117f08b86c4a880e2f21170d895100477c3ac4312a22287c865c2525446d878e9b22a4a88d657a1f73549517062e3b6e6a92a2e1c5f61dcd52545c3aaec3b9aa4a880355dcf7154951006aa39ee2a92a22287e86dc152544030fb0b3b484a88061f21975909510061ebaec9212a20187e86dd542544030f90cbaa84a880257e0d75509511acae41aeaa12a20493c875514254401878ecaa284a88061f61773d81510053cc2e81b02a200ad98310360544051f70e986c0a88023ee1d60181517953dc2ac0302a200ab8845806054401878a8ba0c0a891e1f21d54181510053dc02a8302a247a788055060544030fb0bb98c0a88121f21573181510062e29ae6302a24787e8794c605448f4f501298c0a88029e602531815123c3e43aa6302a2008df835c860544051b906b90c0a88031b149721815123c3e43aa4302a200a5f8354860544014b906a90c0a88029ee01521815123d3c402a4302a200a7985d0060544015b306200c0a880a3e61e30181510053dc2a60302a23593f8750f645440147f0ca1ec8a880257e0d72d91511acae41ae5b22a201976819c3645440f2eb03386c8a88da8fa1b64591511b61fbb6c8b22a20096f825cd64544bf2d904b9ac8a88025de057359151004bdc02e6b22a200978805cd645463dc68c9b8ac8a88034dd9371591518f69a326e2b22a31ed3742dc56454401c70c9b82c8a88035cdc770591510063cc36e0b22a200d7361dc16454401ab663b82c8a8803564c770591510061e320e0b22a200e38641c16454401ae6e2382c8a891f1ee1870591510069db20e0b22a200c7a641c164544018f0c8382c8a88034e19070591510061c320e0b22a200d3b421c16454401ae6c2382c8a880356cc47059151006ac988e0b22a25f87d87d93625446d87ce9b26c4a88db0f1d164d89510053c402c9b12a25f87d87d8f625446b8bce7b1ec4a881e5d60670d89510049fc22e1b12a23693c845c36254401acec4b8cc4a897f5918971989511b49f43ee8b12a200d3761dd16254401a3e63ba2c4a8803474c774589511b61e3a6c8b12a25f87c87591625446d878e8b22c4a88029e20164589511acaf43ee6b12a200d1f74dcd6254401a38e9b9ac4a88025760773
  | 25 => 0x8011bb0f10ec6a938697a1621d8d520052ec2c43b1aa4e1a5e85dc363549c14bb0bb86c6a9002a7a1270d8d520054ec24e1b1aa400a5f855c363548814b90ab86c6a938697a1740d8d520052ec2e81b1aa4008de8710363548011bb0e206c6a900237a1f10d8d520046ec3e21b1aa4e1a5e85c4363548014bb0b886c6a900237a1c10d8d520046ec3821b1aa4e1a5e8504363548014bb0a086c6a9002a7a1010d8d520054ec2021b1aa4e0ace82043635480159b04086c6a90df171d463d85520046fc1ae9b0aa4028dc835d361548c30f90eaa6c2a9002b560773d85521be2e3a8e7b0aa400ad5811cf61548c30f90ea9ec2a900b171cd53d855200c3f42ce1b0aa4038be849c3615480117b09386c2a900a37a0e70d85520046ec1ce1b0aa40187c855c361548011bf06b86c2a900a3720d70d85520046f43ec6b0aa400c9f74d8d6154801938e9b1ac2a900237a1c63585520064fba0c6b0aa400c9c7418d61548019b6c7b82c2a90033618f70585520066db18e0b0aa400cd8631c16154a438baea31ec0a90029e61410d81520055cc2021b02a400ae982043605480193ce9b1cc0a9003275d363981520064f3a0c7302a400c9d7418e6054801972e9b04c0a900a37a1b73581527046e436e6b02a4008de87d8d60548011bd0e31ac0a908f171d463181520047dc3ac0302a44787c87550605488f0f90ea98c0a90022fe11711815201c5e422e2302a400a7985c40605480157308080c0a9002ba60810181520443e43aa6b2c84088f4874c561908090fd0bb82c3210021f61770586420447cc3c613048400a78854c260908090fd0fbaac1210021f607755824227e3cc06eab04840087f855cd60908090f90ab9ac1210223b20973582420062fbae62b0484f9c5c75cc560908018f6ea282c1210223e21d30582420053c42a60b048408ae8824c1609080147b0929ecaa1003175ce53d95420146f43ee6b2a84008dd81dcd65508018bea3b9acaa10031714373595420043fc2ae6b2a84008de871cd65508018beea39acaa100237a1f31595420146e43e62b2a8400c5c73d95525080187ecbba2a4a10224f21d54549420451e432a8a928408b2c8255152508011bf06baec2a100a3720d75d85420043fc2ae7b0a840487c855cf615080317d09386c2a10021fe1570d85420243e42ae1b0a84008df835c361508051b906b86c2a10121fe1d75d81420043fc0aebb02840487e85dcf60508010fb0bb9ec0a100e3b60b73d81427ce2f3ae63b028400c5d75cc760508011f70eb00c0a10021fe1573181420243e42ae6302840087f865c242d44090f90cb8485a88121fa1b7050b510043ec36e0a16a247c3f749d260d448f878e8ba4c1a891f17dce739835123e2e39ae7306a200a3e849ca60d440147b09394c1a891f1bdca72983510052f41e8530
  | 26 => 0xc000800400000000000040020050010000002004001000400800100d00140020080000000052005009802400a000001000c01a0000020010010004000000000600000b0018012002005001801e0080010038004005006002400000e00180d801201100100200000090008004014000005000800200000e000000600000000040000030048004008004000001c00e00000000000000010018004000000000000c0000010000000014000003000401800200d800c00802500080000060030060078002001000002800c000003800000a00400000040020000000070000000000000000a00000200100000130028000026001006801803601d002003400400300000e000800d0008008000014006000000200000000180000000040010000000009802000000000c0014002008000800400a011000000c0020080000000006000000000800000000700000000010010004000023000800000400000200cc00800a0000014004001001000001a008002802c00400e000000000e0010020030000016002800000801b00800000080060028014000000001803001a000004800001e002012801403e000000000c004004004800400000100a00000000000048000034000004000c006000000002400201a0008000004002000000400c01c000001000600200b801400600600080040000010038028004002002001400000123e3c284e1b12a8008ef8758862550011bf06b96c2aa00a3720d72d855401c3ec2ee7b02a8fac5d75cc760550014f30a086c0aa002ae61010d815400574c1021b02a8008fb8758060552134f70ab00c0aa00237e0d72181540146e41ae4302a800a7985c40605500157308080c0aa002ba60810181540445e43a86b24a400a3f8550d64948c34ef02baac3290029e20175586520447a43a62b0ca447c78501c161948014f30ba04c129002b660c40982520447cc3c61304a400a7b854c260948014f30ba02c129002b660c40582520447c43a60b04a400a3d8590764548051bd07386c8a90023760e70d915223e3c284e1b22a4008dd8799363548015b501326c6a9002b660264d8d520046fc3ac9b1aa4e0a5c8655363548811bb0e30ec6a9003355c461d8d5270d2f428e9b1aa4e0a5d851d363549c159d043a6c6a9386b360874d8d5270c6f43e85b1aa4008dd87d0b63548814bd0b38ec6a90029761671d8d520066bb8ce3b1aa400a9f845c7635480153908b8ec6a900327e1171d8d520064e422e3b1aa400c5f515c763548018b8a0b8ec6a938697a1471d8d527052ec28e3b1aa4008de8790763548011bb0f20ec6a938697a1641d8d520052ec2c83b1aa4008de8710763548011bb0e20ec6a938697a1441d8d520052ec2883b1aa4e0ace82107635480159b0420ec6a9002b6a0041d8d520056cc0083b1aa4e18de878876354
  | 27 => 0x80220000088084000001005001000000200080300000040010058002000002800403000100180440260000000024000000000802800a00e0068000002000000000c024000003001802c001001004c00c0050008018016000000005407e00d0050004000000002000c016000000000803c000001800401a006004800800c00f0008024000000000800000c021004000800800700000040080000038008002001000000c01c01100100bc00400600100040080030038040002000001800000601c001007800400100080040800000028020004000007006400001c0038000008003001000000c016001002c068009000801001000a004002c0000040050020000000004800c000005001806806400e003000801a000005803800001400080080140000058000000008000000800600100080140000000000008018000005001800000000000080200040018024002011000800001000000200200240020040008000005003800400200500000040000000000008000001000001000200700180380000030028028000000004000c00000a002000400e0040008000008004001000c000001000800401800e0000000006000003800401800500000100040000008000008000000000c00600c006000400a000000008c00e000018000402800600000140060240010004032016001802c00200d00080100060050020050006000000002400600100000fc00a000001002c004001001002400600d003000002e002001000c03000e0038010000000000002001600500e005c000001000000801000000100600060070018004000000003800000000000000080000010010018006000000000800200000080000000190020000008001001005800000e009800000000000880080000160078014002002002000000c00000d80180080010020000004000003800000000700500000320050010000008001005803800400100c800800c00000b801c00400000a80000040000038008000002001002c00200900300c402a0000060008002012000005403c002006004801a00000300000020020028004026008002001802a0010058000002001000000c000003002802800600700580000200000058008000000004801401801a003001400400100000480380030058020000006000807c000003000802000a001005800400e001005000400c000000004c00400000080180180010000004012002000000c01401b007003c00000100000000000020000000004002001000000001400d00040000040000054006006002001c0120060008000010001003807c00002a000001800e016000800002400000000340000040008014020030000000000600200000440040010030024010009000000400200000e80040000040028010006001000000c000000000003c00e0
  | 28 => 0x35f04ca0f000097c000000000000064aa55d5a60000012f149be94c0521ce400052062536a4000acc0000000000000000000103e927028a0640000a60000000000de45088dc400000047eae000000002e62bb12523670003138000d670000000d0e00000000000fc8940088fc4d5c0004499ae5b6455f177b5c400095833500000000000000000000c2a0000001266000628370cf18000498800122abe15470cd83e89790278aa1736e372ec1878ff46d4151a3600009ca30913890f63df0000000c828420000000000000073117dae00000000001936cad08e2124d840dd1ac1a3013aade58aa2f16a800058c9989abaa0c5b602f000076500028b0f140002001ca8b288745aa9f8c000043263939857e3595658001aaa1526171d9046a56969b152012c9f465720d92268730001e58000000000304d912b7f1a197f18221e60000e5400095b49e2f0c62cc723f31a9804ada524210e175cc660002d59534c623ec8469c7a1f30003530ea87ef5fc8000562c1d61233640000000003871382ace27c939079812217c00008ee72e5cd30680000456a6b6295c400014f32651fe4c400018190fe0005488b24cde5b46a900006aea3b4380c41016a4452b8000c5c45000007358ce83f000000044c0003c0ac6118a0003f5000042a42600022dc1760740002009a9200061bb8880b231a3a0381c66a1f852fa4fc0007250418cf9c3c28b5ebab1c628561000131896660d000277c0004c5000280ca1e047298970504299f41300000003c24b08000000e4457b8000006000800001a01200000000040090010000012003002003404c029001001c0080010048034000000006800800e000006004800000400000180000010128014004003000801c00600300080b800000a0080014004000004000c00401f01480580120000028000000000000801000200000000180060060008038000004002802404e00500780500000080018014004004004800001400800680040040040000000002000003800400000f0000034000004000001402e00b000800800400000e00140260010010010004002000000c0040120008000000013003803400400200380580000040000000008014002801800a009000000403000000080040180080000000000001000000000c000006800c01003f0000030000009000000c0000100020004008003007805800000e000001401000c0058000000003001800000000600500180300260010000010004002003800000200e800c0660090090030002001001800c00000b000802c000005000806400601100000200040000000028000008003000000c009001000400000300100100000020040010018015001800800800b0028024000007007000400202200d801c0020000048044018000000000006a001000002c0040000028
  | 29 => 0x433975d730df35b9112800071f4862958f6a69b7018b901fe0000000884e087af6fa0c35a9094b4b191e841e1a0340a72c86e14b4448800ba485c62db274030c863c1acc0cec3b704c3108ecc0b86c70d58a6c00003123ad638b615322409c0c0cb46a0b589987a45a01b7cacaaa70002a85a4a75b14b2cc80102a224001847c89216cb93659aaa496011f943101393fa9741a5400064080013dc70d2b0241112a5050a12c3451c0890002d6c00074d00020a059092a1061ea48900564a40b9d76800061f28e491436c0540c01aa607f0190434000caa1fc0000000db80002a1172434531e29f400098300021a121c00047713d597678b3ba8bb80d04b100020bc00069f00000000000000b700000002320000001c52de700025680000003a900006a000059e35680000002818d69a2800000000000000003331aac000000605b2d921a6263382694db07b05fd9275684db44bab46046c8cd581209c88cb601b2268d97e0001f69d30f9400006a98f882a4970002d8c7fc9e9718b7080002bc0f580000000c40a40000aa02a413b90956187fe0ff8e21108aee3540000a0e0000002414b42738373801dad4e4759a0000b5e2a0132293c2a8e23000327ccf676e2ff349c6e40004af826d3124633d024ace44c8e34912508920006c60000000c6e472800053a94a0000a348a46cb52c04e8f98a724fe11b884240400000000000003e400007c2e5d3840eb80000f644c07008586534110000000e137052cb0c38be80053704f1aaf331a374430a3050029d0828a4c14f821b5b3cb7300022380002170000bb176253039aaa0ce667280000170fe4000000000000000023d8e80000d423c90564000000000000153c000000065c000000000000000083161388acdfa00050798ecb620000000000000000468334c0002df0000750000000000000000000000000000000000000000192e165012b487b00004e29f9c2fe15b6d6b3bdb04c6a515979894463d2ea94bd3a86e238889c950e7981cda6b0398e144c0a2f92f493e2151050f202bb4ab0000af20004e2217dc9e9125948af478e4e839328dd94cb0f5de907c0003db45a0000000c2500000000000005d7b7b4b6ec3d0001b140009670002300000af210523e422e0fb09023701e40000000000000ada0d200012f6000478800155a01a11eb66800000053500000bc3554bbac1c88024c0d3a200f8823b5769a80d868cb0002058000a3a0000000000026273a27d94e1462cd0000000b0a00033d000052a0001fd800026f4bc3100000c6d0000b8c36233b3420000000bcd0000c6119ec0430b2aa4280000066000000000000012ecb5a0002bf00000802fc00000019ead7525280006da000357ad300000fa222800007485237695b06b874f48000003d2e2e4029618adae48000208008c5620001d04
  | 30 => 0x9b281306f891e4000b112d999a0404e3200037e92ec7dc06b948805238664e31c01a6000000164c43e9e40002104c040005f6000000033052537f80002420248288b7e99b70c1ee4000000185b52c0000004390214d0c00030a2ac1a7c000000165c0009f120480012a200060db5c929e9d75040a0c0008e612c2a4cf0e2cc1041c3d78cac06759b2472cc2615a84506d23370c699ccbee3c56fe16a40004f300023b579c32d23600000000001cc80009646d900014914a40002328000e184ba0000c6422022700000000000001742f7571c8254dc000167e4164d08000fe0a804b69f34a2e58442ba475338d8500006ac0a600050e830816ece51160000000c120003288c984516f914d1bb000019c1660dca00000034644a4e2038c8fe53b849513280019166a727c35d0000012000043c0009ea1cc23900005822d292f0ab44192f91c744c25db4c20000c703e01b40001122d3c104b440f501025339270b2a4ab6ab90a147ace63a58ae47ae64812808504f27496990424e2493a051add4fba0000000001b020004c3b0800006644168400a8e0001b58000ad60006289c0c0000000000000000a0700013b82ca8c35358cc8000cb52ee800174e8fe1deb83db0cd6446d9ba90bca250c21fb5ad6d503db963c47c0906af94f891e0001818001a7299a0168001cb6ac93dd8b4c1e846653f12bd77c03d418307d4b20000001a6159a49f51e0001a2e0000db0000c2a81353f9ad08247f760c32b14a681046518315aebb80b6338190ecf03d90fdc560a5d00013f4a1c7f463a0000000c162848000e3830850f800095800035c21a800070e5440001a3c0001c6000172aa973d0b7bc000000000063800063513f0001182cc80002f5576000000030240002511f1988c2cc7c900026f5bdc636708b01c2322104cc1fc4450c8d35b00000006eb0000000000be73da0a4400080a00005302266bc3bc02e40000001678001c3e48e3ca9e98ec0377082249000044d430845452a0f11dd0684580da66a2000179230707f00000004f7094946c0002fb4550000f56a8267900000000ad1f3b3f00006ad1d8b12400000000000007ea000000038c9d4000000264123e93655989f17ee00042328b8000e2d69fb4a00009140000000000ca100000000000003ac800078011e2d38000aeae5166024dcec681d56fab75328d054e81a78922d910ba80003020ec3cf0000000d5828e00016ca1335493488cb013f1fd246d6cc0006f0a620698cd12cb271d2d06a5419213556880e62d08fc0000930000000e8a04800000000000165ea2654cf85375d415d1aec00063886303840004f4064d74cb7d00016c0000000351373c0982ca4d880007dc90a0000000000de813dab955a039a12e817d0860005a800dd11edb323e8001c16ab220b80005a200000000003747d3
  | 31 => 0xb0002b8c00043d57d940435e9352c8000000038712b81c97e00000000001afec3f00017c4d7608000015e960807a01fb2804b86e116f00008167c70000a500008f74f924c95400000b80ba48a80000000a480000006faa00d8465d36d22644000bab1ea9a7128000058ea79426a0000f11f08000b880001478000de36c580000004d20000ccc00039f17b802c43800045100010a673203205ec00007071ab24000072f0de0d4c0008714ae8be51b4aea270a06d7486806809c8dac4a353a3b674eec3d20000000aae0000873215a5e50411c822c0005f60eeb6547065a8173081986c80172f10ec2ec80768e14987708b206721419464242fda810dde4ae0e380f000066d0bd1cf12225dc147aa75c58cff66598849b468833c97506f46be4ee93bc12e49b000340cc08b436e28090d1ee1717f8d756160820a78038000cfa71800000000000000000a66b2e0002144000d340c18000000af800017800000000002a580009440001329c423cf18221b02027370003020000ce415d0efcf46c8857f000001e9996fb00f893c71e4c7b684942c535570ca560209f13608e878c8ac1961cd872eba907c8000da492510887256960000001b690ca8ef6931ac8a3e0003c2a0e58aa993601a15408422f16c234d73c57700000001b85f90378e95b629b0125b3843042f200003340003151b124bd688be435506a064e14d54f8cbc1de64551f868836a6ce5bd9aa400051542c80004c0000000225c0000003650000f008645f1a65c00000023410081acc545138a846a20b11e181f40006014000318000000610800000000000000018909e04312285b460b51d4b3f4da244f66dae5861802b0c90000000c2200600000000005c63960cba0000001a14a6ac7700011bc242000000334000051800016701c455800000014840000000000aaa0001b82cac000c6119134ec000d2310b0000d7eb6f1c980002c66c64a680007284892b3b15c44674413e97acb0075a0f2b80879c1625c2264894c4be29fb4182ac1f200000019d200011bb17d260036000394d7b6436503008c00029f5c786c8000e5447b38d15789a800032e59bc000546b2a021856a03e04c89a00003fc27dc68e00000000015c8d885069bd411c4d749a33300005a000033288727860002214a88c1952a0000cc0df700037e52d86770eb998ce145cb000133c636b8b2e78001528d3a000000000000040933e40007e900000000009ae5b8b1048f84b40001af4fa2c9a30eb3d80381bf1e08ff08184f1304b30c0000016402db9440a710000000f100000001c4c00003400000009fe5c90b68074afe4764069cb11364b030db67170cd770fb8000b649730aa90cc8860f03291078bca1f95af9c6928ad00139aadd0221681f30001a1200017d2d65c9a1ee31800000008ba58484605c04c360a268
  | 32 => 0x9d1908f840f0df1094d0203ca7adc8204d3742b987140313b62e15cbe56606411d591e4cb0a22c8c8da7aa5be2bd0286c00079b7a913a0ab4c738ac6780000c8a5ac70a00022d09acce428c46100018c0d9200000000005680002889b5e77b000000032a22a5d50a69b549ad2e12d34684be06b42935b7c24d5e523d40003a12c2ae5cdc6693114a734b5c4035242fc44f40004b2b8217ea0000a980016ae5bb49c800000000000000001b6b770002da0000d2c000000181eb793cfaa9071200038380000000000000001c180003f08904dfe1a6269a7540006394beb3582e69521bf1a0d9746692440000000ce70431d386e8c5d4de19d054c89000031ac25a97246cb8d8b9c9d20360b88dfc6dd43310f00dc5d1000000000000029c80001a0b703d280017d66d30001111c7400059f00000008a900000013eaa9c40e2114000b8331480014d245700000000000000000000f22000284135400000000000000000002a904c40007de01cb53c6541e1223b9300000002171da400080c00000000000001d387a0f3a2c21e580000004620001958000e2715f133948090f30595b8000ab14ff000120e0ee22c8088c0633d1350c8d054b6b5bb000015200007000011242a51fb0000000cd800000015b20002e52a04ece5c54692e2825e12616300000001ea00007bc0003e514380004c473450c8195ba80002c923456da00000000000009da50580015ecc8a27637294e600051200000002ab6f613592bc1c360f1f9136ea653c120ecefe38272717b4fc431e1372d249a2ba230d25540bad5616915f48d2cc42bb1be1774a413798adce0a5fd4ec21ddacc9a96549964b4cd8d3080e3ca9c09a1a7a954388ae022f184d95628948194944942cb3669074b80779634000127a2756ae2fa8000c593dd07703ac37f6291ca5046db942b2aa1740b1e4040a08cfe7c31baac2089615d0ae06700d47b82fd06ed8f04a35c9a5901cac4d69980e0bb23f4715078000088d4f09790c6655965b81dc480063088af40164000156a16d9eeddb388101c92c6b053aac4d88a48d1f829e40a4b210de88892160b4634a0cd284c4727b2984ee8b9141c08f0918c79525a2d5c7cab50002bf067e6b100000000008880001c09a828ce29c28244b4284000000000088700034acb060005c08000f665be6fc000134e00000000017de7896b007f967a1d800000000000000001ec448a0006080b515d0b002cdb484edea170002d39c72cf8484b7217385c723399383da0440002fb8a803bb052b51482058b3cc8f58df417d2ef378146c51122634118561e36398d80b886465ef00014bcb390001cc496e00000026cc000cb400000018380002b8b4351d20104aca231634000184b02887c7bf44c91ac38228a3c700002d42f441e800098068a0001408dee00047924b0d481c
  | 33 => 0x3b6d3b9402b400025eb0a03a48093793774000bc427f02058fcb8964197c0ff677c4e02b601d00000000000000376725815c00000009da2e026e6cc0280bcd3bc4eb1332f440000a15181c901eece800000002fcbd80000b340a87cf4701e51ac6e495d295794cc0882be000085a6a1000000017ae523bf0000566b4a1809a44de24c8659800102a50017835ec7780000000c44000c7600011080000000098625c1cc395e58000c5a1ae16ab77dc4cd7c4880740ae686f274a570000d24597acdca20bd613a3659a14000700b294f8ac2d5c380009342d0307a05c00019e095a8a915c4b809a051c83616b14830c9a7052e000000000000000000000000000000aa800000000000001b01873a808380000003fe12a14b6c3460b81a4b3ec630001bb8846d733370001aca8a60003824d6ed13594030c8260004cf049114a9ed0001f04000a38000000000000026c01296a213e000259955482c00000019be0000001dcc0000003bd0000000588000303855e30218980006c662800032f95b62344e335e941439e6028fbd6e88b3380ada42244906892681c763b300038cd6b03b9360abc07f69db55311f90b465c3de040c6629d96feaaac95477102c30a56241c80679450366000046212d10c3cd345805d8780b02b91d4c6fa8dd1a900010b01b46c20025b988a40002f68000ad11da270cb1cd98000178c0000004bf01ccbe61570e2b764140bfc5939cfc830c3a1171528ebe0005df84b000049917280016c810a1a4aef09ba79b384b954bd2de618331316ce9460002b091f6000666a78d056dbb34b0a4cd3229726da2d849c1da5e995442e26000f200002e45d641ab928c54bdc0002120dcc00017500007b80001339218cbc8a05a3a35d0804fa26a2ad80000007229468b44afa5aeac5134c8fc63f9da85382eb50aa815b5c23158b87c4f5c05b341000000016400038bcb3a96e0ecafe890400063aa74c55c7d248c38018761080001d75b80d4722d863c94eb4110cb41d9ba53b3700b69c1a7c025c892165a7db1058ec93a200036a8001ba086e00036fc9303a22dd02557468de08b229c5ba000000101800000032b89590883925f48ffc5682c31a400b15300194620f2881ea3254623a876000463285e5582e1030412a4300e2500018bc4a60002f097b97a417c0000000fe69380000001ba461f03b0000000ab93c20000000a43000154d9a894745d8000000000000000124400000004e005e3172dc041d802e400002f0517a64271e250561ca46483042d6544bf23907d519278f325800000054c3ab8000b562855f92498a86d6c3d6360032800042392d4006470000248040200005f170ca24020562821000027f2c50000000dd52b1943461471468d0dcc0003de3469d840000006b791a935600034a1a38716db05ca1b9123473e01807
  | 34 => 0x9e800054d99c4c1cac3522956cdf27ce2d183840f00e400000000000000000001a9c87600022e4000000687000159461900000000000001628000c4e254663000000000000020f92c4c6f2f62f9863a384721b3b8000d8f00f942c50204e24091e06cc69702aa20c4d2a743f60000c9a5136320cd11040001da8ce523cc430000000000be50000000ebc158000057d8fa2c7000000000064400014ad64c00001d800000012736b1ba554a9490579fac000298398000169e0003b580008020003621524000a2d2dca8bd5ce9820002eb51e84cd51f2631b9c0001788000fdc27146b16a800003518e36a11d0b6a05d10ac370556206af883f6c9400daaf9c3254f4f3b74c358e050ef83a464a72d47d222c2de4925dcab3db36a141ec8000c94000000193c00052100029ec000e465109f559267ad07ea3c026c12866d00000006dc19d11cd5a8b8d0000000b8c00000012d8408c444c31b3dbf6ae90000b848e2d2961c02a8124d1d6672fd01a89010af38fd7f09fd2029b5d9e6d5b38d80000000004c680013f002e1b080000000001098d188744a40570000bde0d213c15700005b53288000ac8000000148d57a4e300019e8650224000160473a9853329d19286cb13d38a20cf0000000120c5fc00000f28a0470000230008461c1b96c18b0423600000000000000004e42b5800000065e15054268185bc2b7140287e3ae342c054a9913b335cc567fd3a1a5fc9f853d456abd573ec586bc26c88c88b01aa3855620d2d4e10d780000003eb8000c7e00000000014a2bed1769bd13e60000002cc40006f0000000113400059da6e45642dc33f26d8000d082aa06280008794e4af3d4d0b7e36f0000000a00000000000000000005440000005e01a2400087d122327800000039e80000000000a80344552ccf0d8000189e000264a3b095a00000014659b8b99523a0a400006763d0000fb0528536189554432e303800197ad150000001b40b2255d28615aa4351380dbd15e00000aa97146600057580001ea0000cf97fc9f66500003734000cc500021f0000bff6bc9789adc21207e0000c86d930ce80002f06185c824b81ce0000f6000000000000000007580006cc86950ba64000026fcd8e89e000245c00021805b0001150ac607580008ba00000000014460000c58000e42c844f12de8bbe5e72fa89a14980000002258000378000076cdf825e0b0118555e20d6971d5950c92d38b06a40009b54fb1734000c0c1a72204a18000590096c0004ed417021d85ea956a89fe41f057b64bb759776b3556437adb74854000196d4dc54b00024649e49741ed26ec0003ad00000000000000000000f96000000000000020717b000164a3af479800150a996060b6d56a414e0003054a9ac560003724d3ad4a34d00187469ba562065844a44e0002459bd27
  | 35 => 0x3a8062b770180000678902874c00000030c00006050000000000e1200a05d02781d316c94b01daa8a4b80ea99921fa5ceaed80e2c6c4452c91c84430123984574224359c386c0000000000c3ca2c4344e708691c61d11ee800071a0003ac35f800062408329419d839052d0000a8a8bf10e93c157e0000002c6c25ca3440a28680003416b680000006c03aaa31c7222306f28000b3c96a0fe28480000000003625b0e53270eb8903464744b7a580bb40ca0330a65a401de08eb64054e29b0539db592cd5e6beb77981a0000001b6d92287a1ce17200006fb17a80000000750001f7c000591000000135e0005a2985c00074a0002fd9b560000001fa063e84f67191580008df296866c8520000001969cb800020e00000005bd131b12d98e0004d200002827d039581687a6de200022c42c2a266ac88cc00000041b80017e6793000284004e71803d8000d740004ceaab19d400000000018629e667d80002cecd21f505a4cc200033600006940004e7ad180000000000000d6a0000001f812761ad6b4a600000762220a87813c3c924582b0caa0003d11f586f204b5da8415368c92213a9f1b880004300001ac2bc241a235551e3d162e0001aa81f053b239c56cdbc4e616359703be06c8d2d3f6a8b6a18db8f3892338b8f40fb4a314fc991caba5f80208fb011a9d6514a0907c4e2832a0bf49ca0005fe8c90a8454600000000000001f418c8b486950dba54001acb03901c2d5fa00000010bd0082ac63d85dc4920006d6061874800000000000007976dea5380002554fd1ffcefa00033eb6888a600047080002540000002c7c4068ab0df116000036500011541140b30001a4062475108fa98800073a578b810ae0b3a2f51d208400000000ae092636a00007184b20002f4000142c1d50000000b5800062f00015fe90800023195de0000001038ade381000000000077272b0000cce79a32fa9c1a18c466ff949c0001905708d107e60003358368000000318a7fda1e000075000086409170d3445a808e20a50000000d376e396653d84e00478fa400041a1db0f1149c6d000019d4000b4800008787d66ac68f8d00500e5700037c0000b5c69880014f40006cf818000000000030180000000000000b780005a9a2700002db71c2130000b1604e0378940d1626104f4ee0706536800050c22d04a2f7da6a768407b305764878102b6dcd9026d28321d52d2b621c7086dcb4c3566110213166490001828292dcb57c8eac000d3d64c0000f7c3f212f8000f6ca1c195873d7985f440d00000008cc599aedd96463a1670b11512a1b4df031c82219a6ed2981b8cdd71c021a52a8b5e5e3ac19b6c03321fa7bd00c928435b0cc90ec8c5e42a40d664de698161ca3a00061631f08440005d607d960600019318819dab5a00013700007c6242b46d354ce20000
  | 36 => 0x5291ad8ff4eee45c72c80a0440a782db1bd88fe199451aae01beb05000000069a00053786615763201bd848cfa8bd90001c000000000000000c6e00000014e8790000376298c00091c00035190740000001428f7a00000000000001fd4a9a6287a858967f1c54b18ca464129dcc5800035189192e2bfe2bc2e080001ce0d510c554662205faecce4e321657872909c06b0002cd8000a0e29e04950c606d16b893c000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x145697101614c4500051565c40585311400125698585704c45000685e11615c13114001a1484585704c45000691e09615c13114001a4482585704c45000685a11611c13114001a1584584704c45023d1c24174585211408f470905cd61484500058965082585211404566190209614845000598642425852114001645962093148450005c1650824c52114001741902093148450005d0642424c5211408fc618258470484500060e1d2809d9519000103f985db74546400050764c409db5150001c17414c476545400050764c401d951500014359110076545400051c644401d95150001c31414407654540007144c5101d9515008f9185060c70505400059164861d95315000164592184654c5407360e218405c450500015199310171141400054c644405c450501cdc3061101711414023e0d21971504505008f930805c5411414011515259714c45050001d10405c5311414000515e5f614c4505000105f985cc7359720007114c5215db51c8001c453148776547200051664e641c151c8001c1a9399070547200070664e641c151c8001c1b319907054720007064c6641c151c800143a94d8c7054720775942418558531c80bd685938c5644872000781d453159121c8001e05514c56448720007815913148650c8001c3010991711432011515e59714c450c8001c16645c5311432000705591714c450c8001c25645c5211432023e582017148450c8001e05644c52114320006866118018f654800103f985d074d9520006866118018c65480014559118d71195200061560d711846548001c453148676d452000515644639d951480014559118c765452019615605311d95148001468924c076545200051c644201d95148001c6121440765452000515644631c1514806b85581544764c52000711545211d9314800189984600764c52000714545101d93148001cc121440764c520006159d981195314800185476604654c520005a1650864c52148001a4486d953148520004b1261644c521480034c49759131485202f57025d804c521480bd6c0966013148520006b0219804c52148001455919d9319412023e1a202764865048001c46764c5219412000515644635c45048001856865c5311412000615219714c4504808f864865c52114120007119d9314845048001a6182584705442023e1c2017158450080018c487585314802000712ddb739412008001e41614c650480200049564683d0b658400143a949ca70d96100060ea0274d966284001857756047358a1000515e4d625c450841d18737660465502100060ea0274d97208408f86820a1f65482100051564473d95208408f86862a1f654821039e1cdd981195208408fc63655c5200821000417e61731cf6544001c19705cf6519110007065c1731946444001619931906550110
  | 1 => 0x10051564450dd9524c46f85581d44765493100552241511c9604c40158592205741813161c65a63615d0604c401d11514417418131006235d082580604c401439941487059521004e1e5180dc93148401b4395600724c521006d0255801c931484bd384985d1424c5210066121d7450931484bd684965d1424c521006251d9841c131484012559120d52586500050ea52629c3619400105f985cc63586500040fe61741d1619400105f985cc73586500049564683dc9619400105f985d8764c65000456e61701c13194001645962093148650005c1650824c52194001741902093148650005c1652624c5219400103f985d074584500050e241741d1611406525591a0c74584500060b5d1821d1611400105f985cc735845019615605731cd611408f27090607435845019495646831c9611400182d845c872584500049564683d09611408f0789061c425845023c9c24181109611408f27090606325845011495a63434c561140016529010d315845000594640434c56114045256988c9315845000515a5c324c56114001616940c9315845000585650324c56114001652900c9315845000594640324c5611400125591a0c40584500068590583101611408f8587060c405845023e9404183101611408f254984c530584501149564d810c16114001a16844c4305845000685611310c161140016259221161504501158c64084585411408f470905cd61504500051564f72585411400163190d09615045072d0da5f40585411408f87287587705045072f0cdd1611c14114001c339458470504500070c251611c1411408fc3284584705045023f0c611611c1411408fc5283584705045023f1460d611c14114001c334258470504500070c509611c1411400161694a1d614c4500058565287585311400165290a1d614c45076d946428758531141d165390611614c4500059424184585311400145697211614c4501951565c84585311400164692211614c4500059164884585311400165290211614c45011594640845853114001653905d1614c45000594241745853114001652901d1614c4500059464074585311400145797609614c4500051525d82585311400161794609614c450005852518258531140e765390609614c4500059424182585311400145697209614c4501951565c82585311400161694209614c4500058565082585311400165290209614c45011594640825853114001653905c9614c45000594241725853114245256981c9614c45000495660725853114001616941c9614c45000585650725853114001652901c9614c4500059464072585311400145697d09614c4500051565f42585311400165290d09614c4500059464342585311400165290909614c4500059464242585311400125698109614c45000495660425853114
  | 2 => 0x6c3f8002ec000008212c21440dd1310a3dc9f19c6940c9c170f21981d000001f800204ef0008a4448e3c49101c762846a258ae37c8d31c000007a05c650002a0683f3d80a3b43900106000923a4e83f44e25caa018d02b4000003e098db0580034c95220000d82d21c19054a5000a90e8740d404000fc104ec08c2f214bd3d0331bc8f1a07714063264ff2d003078000001007d0e188dc35429114af2c44d424432c0a844c79280be0c84f2d4473486014854278510c437121052e4612740f450ea1f45b290c93843b42c44108240601c330e53989a39c711c85e0c0113e8b732c552c88c359151b4d81e0a2420c3020ce3351229cca430bf0890f1246b0a013008c534516080ee000ac128c41644006c0028cc01f014350002ac001903d388eb24c120d0d741090024bc3e038038f000000000c82249420c5f41c001589b390801cc00380f50005d001010b8000002b000001610d318001680c298003ec270010238cba2600100000000c1094460f0703080d0147f14c7b4000000000364000002c1d40021800000cf2d88b000de02cf90005700000210da000b81b8f300000000b300016000404400010001000010501c1c01069240a00020000a0000004161c010080a000181c001300888000601000b003000000e0c2f8200a06078340217140240406000000e0e000fc0e010002842020800426040500c0021020280a27050d4002e098007801068040142d9414972181510050ea5c64dc1645440143a9719070591510050e648641c16454401c1864cc4705915100706191311c164544018387420164d89510060e1d08059162544014689258c70589510050e650621c16254401d053148574189510060e1d880591425448f85a805ce63981510048e25180d88605440182d845c8621815100686d91831006054401a186460c40181510068c1918110060544012559120d72181510049564683d08605448fa1a7460c401815123e865d183100605440125b9160c401815100496645831006054401a1a4160c401815100686105831006054401a1983d0840181510068660d42100605440123a94a0a30181510051665c328c06054401651910ca30181510049aa4a844c060544016519190d301815123f06141745cc605048f45890545731814100523648415cc605040149990105731814100455644805d4624c401d0751485741893100741545215d0624c40155191216701893100554644855c0624c401d4351485701893100750545215c0624c40155090615719493
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd5004c580202810019cc4480b02c01504d1082c1880302a200c846444160c401815100505140ba3043a2c228002c21a2251611c1411400180c43326202e22828000d0418593101711414072c8614cc8880b88a0a039b03086644405c45050001488d4080b8a6228280e6d04258405c531141400058234349cc8382a390002419a9cc6641c151c8001218d4821322e22864000b08688109917114320
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4010006201a26444160c4018151005401b2185931017114140006010966a0405c53114140
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94c
  | 6 => 0x94d
  | 7 => 0x94e
  | 8 => 0x3
  | 9 => 0x124c
  | 10 => 0x124d
  | 11 => 0x124e
  | 12 => 0x8a
  | 13 => 0x8c
  | 14 => 0x8d
  | 15 => 0x8e
  | 16 => 0x128c
  | 17 => 0x98a
  | 18 => 0x98c
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x128a
  | 22 => 0x128d
  | 23 => 0x128e
  | 24 => 0x150a
  | 25 => 0x150c
  | 26 => 0x150d
  | 27 => 0x150e
  | 28 => 0xa0a
  | 29 => 0xa0c
  | 30 => 0xa0e
  | 31 => 0x130a
  | 32 => 0x130c
  | 33 => 0x130e
  | 34 => 0x14a
  | 35 => 0x14c
  | 36 => 0x14d
  | 37 => 0x134c
  | 38 => 0xa4a
  | 39 => 0xa4c
  | 40 => 0xa4d
  | 41 => 0x134a
  | 42 => 0x134d
  | 43 => 0xb0c
  | 44 => 0xb0d
  | 45 => 0xb0e
  | 46 => 0x154c
  | 47 => 0x154d
  | 48 => 0x154e
  | 49 => 0xb4d
  | 50 => 0xb4e
  | 51 => 0xb8c
  | 52 => 0xb8e
  | 53 => 0xbcc
  | 54 => 0xbcd
  | 55 => 0x19cc
  | 56 => 0x19cd
  | 57 => 0xd0a
  | 58 => 0xd0c
  | 59 => 0xd0e
  | 60 => 0x160a
  | 61 => 0x160c
  | 62 => 0x160e
  | 63 => 0xd4a
  | 64 => 0xd4c
  | 65 => 0xd4d
  | 66 => 0x164a
  | 67 => 0x164c
  | 68 => 0x164d
  | 69 => 0x104a
  | 70 => 0x104c
  | 71 => 0x1
  | 72 => 0x98954
  | 73 => 0x128954
  | 74 => 0xa0954
  | 75 => 0x138d
  | 76 => 0x10a
  | 77 => 0x14b
  | 78 => 0x14954
  | 79 => 0x134b
  | 80 => 0x134954
  | 81 => 0x180a
  | 82 => 0x198a
  | 83 => 0x99254
  | 84 => 0x129254
  | 85 => 0xa1254
  | 86 => 0x4d
  | 87 => 0x15254
  | 88 => 0x135254
  | 89 => 0x98094
  | 90 => 0x99294
  | 91 => 0x14092
  | 92 => 0x14094
  | 93 => 0x134094
  | 94 => 0xb4b
  | 95 => 0xbcb
  | 96 => 0xbc094
  | 97 => 0x19cb
  | 98 => 0x19c094
  | 99 => 0x128994
  | 100 => 0x14994
  | 101 => 0x14995
  | 102 => 0x99354
  | 103 => 0x134994
  | 104 => 0xb0994
  | 105 => 0x154994
  | 106 => 0xbc994
  | 107 => 0x19c994
  | 108 => 0x12cb
  | 109 => 0x151294
  | 110 => 0x15294
  | 111 => 0x15295
  | 112 => 0x135294
  | 113 => 0xbd294
  | 114 => 0x19d294
  | 115 => 0x15512
  | 116 => 0x15514
  | 117 => 0x135514
  | 118 => 0xb1514
  | 119 => 0xbd514
  | 120 => 0x19d514
  | 121 => 0x130a14
  | 122 => 0xa1314
  | 123 => 0x14a14
  | 124 => 0x134a14
  | 125 => 0xa0b94
  | 126 => 0xbca14
  | 127 => 0x19ca14
  | 128 => 0x198d
  | 129 => 0x15314
  | 130 => 0x15312
  | 131 => 0x135314
  | 132 => 0x135312
  | 133 => 0xbd314
  | 134 => 0x19d314
  | 135 => 0xd1314
  | 136 => 0xb0154
  | 137 => 0x14b14
  | 138 => 0x15554
  | 139 => 0xb4155
  | 140 => 0x14b94
  | 141 => 0xd0154
  | 142 => 0x14d14
  | 143 => 0x160154
  | 144 => 0x15614
  | 145 => 0x134a54
  | 146 => 0xbca54
  | 147 => 0x138e
  | 148 => 0x180e
  | 149 => 0xb1354
  | 150 => 0x134b14
  | 151 => 0x135554
  | 152 => 0xb5355
  | 153 => 0x134b94
  | 154 => 0xd1354
  | 155 => 0x134d14
  | 156 => 0x161354
  | 157 => 0x135614
  | 158 => 0xbd354
  | 159 => 0x134bd4
  | 160 => 0x4e
  | 161 => 0xd5354
  | 162 => 0x134d54
  | 163 => 0x165354
  | 164 => 0x135654
  | 165 => 0x105354
  | 166 => 0x135054
  | 167 => 0x10e
  | 168 => 0xb4b15
  | 169 => 0xb4b16
  | 170 => 0xd0b14
  | 171 => 0x160b14
  | 172 => 0x40a
  | 173 => 0x188a
  | 174 => 0x1a0a
  | 175 => 0xd1554
  | 176 => 0x20d
  | 177 => 0xca
  | 178 => 0x12ca
  | 179 => 0x4c
  | 180 => 0x168a
  | 181 => 0x9ca
  | 182 => 0x138c
  | 183 => 0x44a
  | 184 => 0x3ca
  | 185 => 0x20c
  | 186 => 0x15ca
  | 187 => 0x170a
  | 188 => 0xcca
  | 189 => 0x140c
  | 190 => 0x1a8a
  | 191 => 0x194a
  | 192 => 0xe8a
  | 193 => 0x184c
  | 194 => 0x178a
  | 195 => 0x18ca
  | 196 => 0x148c
  | 197 => 0x58a
  | 198 => 0xeca
  | 199 => 0x17ca
  | 200 => 0x1a4a
  | 201 => 0x14cc
  | 202 => 0x5ca
  | 203 => 0xd0b94
  | 204 => 0x140d
  | 205 => 0x14cd
  | 206 => 0xd0bd4
  | 207 => 0xbcd14
  | 208 => 0xbd614
  | 209 => 0x20e
  | 210 => 0x140e
  | 211 => 0x148e
  | 212 => 0x74a
  | 213 => 0xd4bd4
  | 214 => 0xbcd54
  | 215 => 0xbd654
  | 216 => 0xbd054
  | 217 => 0x184e
  | 218 => 0xd19d4
  | 219 => 0x19cd14
  | 220 => 0x19d614
  | 221 => 0x104d14
  | 222 => 0xd1054
  | 223 => 0x1a0d
  | 224 => 0x1a4b
  | 225 => 0x15ce
  | 226 => 0x104d54
  | 227 => 0xd5054
  | 228 => 0x188e
  | 229 => 0x14112
  | 230 => 0x10152
  | 231 => 0x11352
  | 232 => 0x15812
  | 233 => 0x131352
  | 234 => 0x130152
  | 235 => 0x11992
  | 236 => 0x134112
  | 237 => 0x149d2
  | 238 => 0x150152
  | 239 => 0x14055
  | 240 => 0x9c152
  | 241 => 0x180152
  | 242 => 0x15352
  | 243 => 0x1349809c
  | 244 => 0x98155
  | 245 => 0x98154
  | 246 => 0x999d4
  | 247 => 0x98bd4
  | 248 => 0x3ce
  | 249 => 0x16ce
  | 250 => 0x16cd
  | 251 => 0x16cb
  | 252 => 0x128155
  | 253 => 0xa1854
  | 254 => 0x1356d5
  | 255 => 0x15395
  | 256 => 0x16d355
  | 257 => 0x10a16
  | 258 => 0x8152
  | 259 => 0x15854
  | 260 => 0x4155
  | 261 => 0xe8152
  | 262 => 0x18c152
  | 263 => 0x134b55
  | 264 => 0x135854
  | 265 => 0x15355
  | 266 => 0x1359d4
  | 267 => 0x140b14
  | 268 => 0xb0b56
  | 269 => 0x5254
  | 270 => 0x4954
  | 271 => 0x139254
  | 272 => 0x138954
  | 273 => 0x138bd4
  | 274 => 0xd1854
  | 275 => 0xd59d4
  | 276 => 0x21554
  | 277 => 0x2cc
  | 278 => 0x155414
  | 279 => 0x185494
  | 280 => 0x19d4d4
  | 281 => 0x11312
  | 282 => 0x140b55
  | 283 => 0x1a9952
  | 284 => 0x12c152
  | 285 => 0x152d2
  | 286 => 0x19cbd5
  | 287 => 0x168e
  | 288 => 0x9ce
  | 289 => 0x5cb
  | 290 => 0xb5416
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 2047
  | 6 => 7107
  | 5 => 3680
  | 4 => 279
  | 3 => 14
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 105)*8) 8
  | 7 => packedAt gbK7 (83923+((h/682+packedAt gbK7 (75739+(h % 682)*12) 12) % 2702)*12) 12
  | 6 => packedAt gbK6 (374302+((h/2369+packedAt gbK6 (341136+(h % 2369)*14) 14) % 15106)*14) 14
  | 5 => packedAt gbK5 (233058+((h/1226+packedAt gbK5 (217120+(h % 1226)*13) 13) % 4858)*13) 13
  | 4 => packedAt gbK4 (20367+((h/93+packedAt gbK4 (19530+(h % 93)*9) 9) % 335)*10) 10
  | 3 => packedAt gbK3 (1154+((h/4+packedAt gbK3 (1134+(h % 4)*5) 5) % 18)*5) 5
  | 2 => packedAt gbK2 (279+((h/1+packedAt gbK2 (276+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff8f81e070ff80e1e01fe07f0d38f3f23c673
  | 1 => 0xf0ff001ffff07fffe001fffff32c48c63c787f
  | 2 => 0xff0fffe007ff800ffffe0ff80c3070f9c78f9c
  | 3 => 0xffffff800000ffffff0000fc07f01f80fe0
  | 4 => 0xffffffffffff0000000000fff8001fff000
  | 5 => 0xfff0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x118390a4304c846120c92136041831b21c631
  | 1 => 0x90a1000488101229201124a481044844081846
  | 2 => 0x2a024a2005a9008244a40950243010a8468298
  | 3 => 0x808d9557d004412d9959c020cbc06d01b80d60
  | 4 => 0x80ee79966ce65c0106080410efa8001f76000
  | 5 => 0xccc0060180880601018101860fbf7ef6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36196
namespace PEqualNP.Outside.L_meta_36196
open PEqualNP.Outside.L_meta_36196.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 99 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 56 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_768 : Interval s3Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 781 := (concat (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160))) (concat (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)) (concat bs3_4_288 (concat bs3_4_320 bs3_4_352)))) (concat (concat (concat bs3_4_384 (concat bs3_4_416 bs3_4_448)) (concat bs3_4_480 (concat bs3_4_512 bs3_4_544))) (concat (concat bs3_4_576 (concat bs3_4_608 bs3_4_640)) (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 bs3_4_768)))))
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
theorem bs3_5_800 : Interval s3Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 801 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat bs3_5_96 (concat bs3_5_128 bs3_5_160))) (concat (concat bs3_5_192 (concat bs3_5_224 bs3_5_256)) (concat (concat bs3_5_288 bs3_5_320) (concat bs3_5_352 bs3_5_384)))) (concat (concat (concat bs3_5_416 (concat bs3_5_448 bs3_5_480)) (concat bs3_5_512 (concat bs3_5_544 bs3_5_576))) (concat (concat bs3_5_608 (concat bs3_5_640 bs3_5_672)) (concat (concat bs3_5_704 bs3_5_736) (concat bs3_5_768 bs3_5_800)))))
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
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 14 := bgb_3_0
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
theorem bgb_4_256 : Interval gbAtlas 4 256 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 279 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem allgb_5 : Interval gbAtlas 5 0 3680 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864))))) (concat (concat (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))) (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)))))) (concat (concat (concat (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016))) (concat (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 bgb_5_2240)))) (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 bgb_5_2464))) (concat (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592)) (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720))))) (concat (concat (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))) (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)))) (concat (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392))) (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648)))))))
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
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7107 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)))) (concat (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)))))) (concat (concat (concat (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624))))) (concat (concat (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)))) (concat (concat (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520))))))) (concat (concat (concat (concat (concat (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744))) (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968)))) (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 bgb_6_4192))) (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416))))) (concat (concat (concat (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)) (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 bgb_6_4640))) (concat (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736)) (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 bgb_6_4864)))) (concat (concat (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)) (concat (concat bgb_6_4992 bgb_6_5024) (concat bgb_6_5056 bgb_6_5088))) (concat (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)) (concat (concat bgb_6_5216 bgb_6_5248) (concat bgb_6_5280 bgb_6_5312)))))) (concat (concat (concat (concat (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)) (concat (concat bgb_6_5440 bgb_6_5472) (concat bgb_6_5504 bgb_6_5536))) (concat (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632)) (concat (concat bgb_6_5664 bgb_6_5696) (concat bgb_6_5728 bgb_6_5760)))) (concat (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984))) (concat (concat bgb_6_6016 (concat bgb_6_6048 bgb_6_6080)) (concat (concat bgb_6_6112 bgb_6_6144) (concat bgb_6_6176 bgb_6_6208))))) (concat (concat (concat (concat bgb_6_6240 (concat bgb_6_6272 bgb_6_6304)) (concat (concat bgb_6_6336 bgb_6_6368) (concat bgb_6_6400 bgb_6_6432))) (concat (concat bgb_6_6464 (concat bgb_6_6496 bgb_6_6528)) (concat (concat bgb_6_6560 bgb_6_6592) (concat bgb_6_6624 bgb_6_6656)))) (concat (concat (concat bgb_6_6688 (concat bgb_6_6720 bgb_6_6752)) (concat (concat bgb_6_6784 bgb_6_6816) (concat bgb_6_6848 bgb_6_6880))) (concat (concat bgb_6_6912 (concat bgb_6_6944 bgb_6_6976)) (concat (concat bgb_6_7008 bgb_6_7040) (concat bgb_6_7072 bgb_6_7104))))))))
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
theorem bgb_7_2016 : Interval gbAtlas 7 2016 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2047 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 bgb_7_992))))) (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248))) (concat (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 bgb_7_1376)) (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)))) (concat (concat (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))) (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8feeefae8fcecf8c8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074664 * 2 ^ 32 + 4243388616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36196.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,5]⟩,⟨.and,[0,4]⟩,⟨.or,[1,7]⟩,⟨.or,[1,6]⟩,⟨.and,[2,6]⟩,⟨.or,[3,8]⟩,⟨.or,[0,4]⟩,⟨.or,[10,11]⟩,⟨.and,[9,12]⟩,⟨.or,[2,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4243388616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4243388616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36196

open PEqualNP.Outside.L_meta_36196 in
theorem PEqualNP.Outside.L_meta_36196 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4243388616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4243388616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
