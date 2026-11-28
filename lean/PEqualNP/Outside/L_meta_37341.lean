import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37341.Model
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


end PEqualNP.Outside.L_meta_37341.Model

namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
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

def SBf (j : Nat) : Nat := [5, 5, 8, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37341

namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
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
  | 1 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 2 => 0xffffffff81fffffc0fc07ffffff81fff98ff8f
  | 3 => 0xfff81ffffffffffff0007ff03fffffffe0e3ff
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 2 => 0xa85108890c9122940552251992c90a54983685
  | 3 => 0x10a255122122852950284aa4251654a960c15a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831dd03e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1f6f800
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37341
namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
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
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 2 => 0xfff81ffffffffffc0fc07ff03fffffff98e3ff
  | 3 => 0xffffffff81fffffff0007ffffff81fffe0ff8f
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 2 => 0x88524c892091831405582594128e525498a0d5
  | 3 => 0x30a111120d2224a950224a29a5510ca960570a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831f503e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1def800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37341
namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130efa1a61dc434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ee42883da85107bcca20f6194417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107b90820f6a1041ef32083d864105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dcc410fa188217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a177d4d42afa9a857c5350bb8a6a15714d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c63df438c7b88718df94a31f7294636e528c6faa518fb54a31b6a9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f7d0c31ee218637e520c6faa418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21f721643ed42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487de6490fb0c921fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a07b94b40b7296817d52d03daa5a05b54b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0xa44c49c6026c3cc55c3391e11e170282541b28592722b24475c53082002204460ad3588d4000003d006c2a9093ca000901c019e4f816000490000588b838a31076a9709e000fd0004b4108c020e2860ed3194a1345151814d24200000000168001089bb5023d0f08e23f6324301ee1d2499340d74b09e81128e00a5bc68a891944182fa843c85040a87d2c6870708fa130890d88f32365f91c8b93da2cc838a70687c8c227b0004b83b06a41200098800156680e58004885dcb7000000001388002f4000001d2432178000003300005f8f70002154902a46e001229b039c37014017140000268004ce404e3a4c48277c7d87b1fc4f00701c4ee500cd9b918c400000c339e690bb00025a238510000008b40f00047e44c6100b13a18d4b1663664b0001892e46d03ba1e36c148001d9124000001f900004ca70000000009fa2a40a000788d815c8d800000000604e480000051800249234760fb8fc4c4340480951dc614d680000070c640653b426d218eb41e4bd00a7e0c494d2a8572b40000d00018e91c00000000464728be4e66780000006e0007600000057caf000000754000000940000005a128330000332162d4669503344c0d127d2646540000040e22807a1a320264f984b1c60902709c0129707fa084280000000050e60c7788803ea3c9b0e72d20ad1a24201828c36a7205a084001ff19c0000021f0e4658d4000418a44ca0000001754688d2f085c0a004070430b59a14a26e8000f52ce000001be000001441d60000001f0050000d024030140000000010030280204003028310080100005000010500500800008010000a03c04000040000b01c0400000008030400600402014010040e00802018040000b010100000000405014030040b0180200000000000100006c0b01c00040070c00400c0300c000500001801010050280500005000050000502c000480206409034011140e07802000000480600008018000000202000000040200805c030000000802078020240101002000000000300c0000c000000000400008010000f00000010470180200c0000406014040281600801004000080200c0102c0b084000040b0280a0040700c0e0b0000040a0240001400010190240100801000030040300001000240000e018070040904400bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485e
  | 3 => 0x974c595c0248c4000000a2000ba9123c60000000026a218001282d0000139b750a0009c80052678888a7f0900e4298350003c8189254c07d4730a508c7a4a387c2563e46f93a000674002250002f5109bf0984cc3226500c2d80015d2141a0be000108a088e0540d61f90229544449117a6f196544001380b01e4549aa3902a02218a1d00c0840d547a1d0f60661c8000001ae000000ac0193bc834000d6182000b201d2aca5000000496408950692d8000001702e2000c70004f0000001e7000000001b243a0001e000388900cf8005200440014f3a6000001dc0001590c11d0e00002082f3d645cc686c0001cca22124a086cb6a463e29d0001bc2525ec7b1db21c454002690009340028600022c918024b6774e828b2e6440d58362062dd1d0ac178704579792a88a5461fc4648b0000784b21fc000004d610d290081b62ec000000006709e8003d45547e974122001352132fe000fa00000082c0000010663c11825000001321873a88f9251bd00000ccc8000009b4d38000000006a24f1bc7080018638c01ca413b45000050962000000370204bc0013804002074414a2e2c28409a220000000000004cc224001422b67c023a614000000000d0000006d2272081241e8f0310a28002030000008f8003989b8a61650007e0000181640fc4b0002b295c8b1fd296460d183a4be6e05827c0008ecfb1a632e4500002e0000c8378750f44dd3c8aa000001030d208a5f4c89e035e000000002926092b1600000013b0ea1f00293a95314864ce51b532425ca90001744351c0001260000000010016c0000000063000280506164d480039a88c000c51c043c82800000000002330007f8002023de000308001a63743880013e8281300010e854000000000011e1a50002780b16
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x9300c2d4614c0309ed95300c25f63553209718d54c831f6355320c718d54c832c62553208f99353c823d64d4f209d98753c827561d4f208f99053c823d6414f20cb55342c832d5410b20cb55232c82ac644cb20cb55132c832d54c8720b358f21c832d54487209798f548825d63d52208f993538823d64d4e20b318d428825f63546209718d51882ad6408620ab593208826d629512097d8d544825c63551209dd85544827461551208fd91534823c6454d209bd8953482776154d209d185534826e65d09209b994424826e658c9209b19532482ac644c9208f990514823d64145209b99721482cd63c85209798f540825d63d50209b98b540825e63150209758c540827661150209d584540825d6594c208fd91530823c6454c20c7d91530831c6454c20d3189530825e6314c209b988530823e64948208f592520826d6590820d354e420826f6550820b318d420834d53508209b597320834d53cc8209b594320834d530c8209b596210834d5388420ab590210834d5308420ab593200834d53c80209bd95200834d53480209ed95200825f63553109718d54c426f62553109b18954c426e62153109b58854c423e64d4f108f59353c426e62d4f109b58b53c426e6294f109b58a53c425e6394b109758e52c423e6414b108f59052c425e63d52109758f548426e62d52109b58b548426e62952109b58a548423f6454e108f191538426f6254e109b189538426e6214e109b588538423e6494a108f592528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109ed81544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b18953442776154d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524433854c4110d514e104425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043546154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520435553cc4109d594310433954d00109e594400427965840109dd9510042d463440109ed9510042b86444010
  | 1 => 0xc66d6215231c7550438c6cd6210e31cb952528c72d5494a31d3d0e528c74c4394a31cb951528c72d5454a31d394b328c69c644ca31b358b318c65f63551319bd89544c66c62551319ed81544c67860551319b988544c66d62151319b988504c66d62141319bd89540c66c62550319b988540c66d62150319e980540c679601503197594430c6cd6210c31b5584430c69c644c8318f992510c63d6494431b358b310c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c65e63d53219758f54c867a60d53219e58354c865e63153219758c54c863f6454f218f19153c871f6454f21c719153c874c6254f21d354e42c86cc6350b21d354d42c874d53ccb21d354c32c865e63d52219758f548863e64d4e218f59353886ac644ca21b358f218863f64542218f191508865f63551219718d544866f62551219ed81544867860551219b58a534863f6454d218f191534867b6054d219e181534866e65909219b19542486cc63509219b997324866e650c9219798c504865d63141218f596540865f63550219718d540871f6355021c718d540872c62550218f990540866e62150218f993530863d64d4c219b98b530863e6414c218f590530867a6014c219e580530865e63948219758e520866d65d0821cb553420866d6510821cb550420866d658c821cb552320866f654c821ab191320872d544c821cb55321086cd63c84219bd95210872d54484219dd95210872d52d0740cb54941d02b86050740c754c43902ad6210e40d394e529034d5394a40cb90e529032c4394a40d394d529034d5354a40cb94b429029c6350a40ab58841902ad62d02409b988535026d6214d409b988515026d62145408f99741502b860505409bd89531026c6254c40ab58843102b96010c40a718d421025f63544409718d511026f62544409b189511023d6590440ab58841102ad62d00408fd95401027b65500409bd8954cc26c62553309b98854cc26d6215330b358843cc29c644cb308f99251cc23d64947309b98a51cc26d6294730b358b31cc26e62d52309b58b548c26e62952309b58a548c26f62546309b189518c31d63d51308f992544c26e62951309b58a544c27661951309d586544c26f62551309b189544c27761551309d185544c23e651513097997434c31f5410d30b3588434c32f54d4930cb153524c32f5414930cb150524c34f4314930d310c524c34c52cc930a7191324c33754d4530cd153514c36752d4530d914b514c3375414530cd150514c3675214530d9148514c3574314530d510c514c3573214530d54c8514c25e65cc530b358b314c35451cc530d5145314c354518c1309798f540c26e62d50309b58b540c26e62150309b588540c27661150309d584540c25d658c430d354a310c34d520c430d354b300c25f654c030d354
  | 2 => 0x172000000710000000000009a30cb10c437c48c00000000000000000c8008af9cf1e600000000000248000003b0314001993fa738d501d00003c869322082c8f68000fa4001f88d390858049263ba2144d0661fc6b8a991a20e508708524084a4779d0000804d39540c00d48c8c700c0ac4a16d4240e87b9cc0c61441389536a000000a62942303f91121445c2d1e7120000a69a83b27a48e0d00925fc001fa0000001a2091f8000b4a0f3e07e4df8121065d80194804666c3d08934677cd600027a6dca01dc0004f0f98de25c4bc0a0000003a40012812670c3b800000000c280030e0003b0000f04fc0018009814c0f800212398de07209e0002b1034004185703c29201c2086d2c81a02d8bf23c5c08c1242624b4de9133145c81b15c42e000000c000020280040103813038010e001068000040a00404000090180103028030060080f00c0702803034040040b1200b014000000b0200208c12020050001500c4101c1f00425024220003800404000060040204418004280000e004010000900007030000080103c0501c030440407c0d000070000400c030000d0e00400000068070b00a00002004090040b0040203425004010040000403048250340203015098010300000007000000140000005000030441400c1800000000010000702408000050000401803044000000c03407044000100100002174000080e0566f62547439b18951d0e6e62943439b58a50d0e6e62946439b58a5190e6f62542439b1895090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310e5f63547429718d51d0a5e63943429758e50d0aad6210e42d35885350b4c53d0942c714e4250a3f6550842a718d4210a6f6550842b318d4210a3e64947328f59251cca3f64543328f19150cca7661152329d584548cacd6210e32e310e428cacc6350a328f992544ca5f63551329bd89544ca3e6515132cb588544ca6e6590932cb152424ca6c6550932cb151424cacc6350932cb153324cb1c548c9329e983540ca7960d50329b988540ca5d6510c329b597420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320ca6f6254f419b18953d06ad6210f41a718d42d065e63943419758e50d066e62943419b58a50d066e6294e419b58a539066f62542419b189509071f5310d41ab588435074f53d4941d314f525074f5314941d314c525072e4314941cb10c525072c52d0941a718d425075b53d4141d614f505076b52d4141da14b505075b5314141d614c505076b5214141da148505073a4314141ce10c505073b4214141ce508505073a4114141cb54b411063f6550441cb54941106b860504419dd95411066e62d53319b58b54cc67a60d53319e58354cc66e62153319b58854cc66e62d52319b58b548c71f63552319b988548
  | 3 => 0xcf17336c12c829cb0008143d9793127887285f0003e0c9800100001019593c8000191fe3520a86e08e1d63186005516c7fc1711d1e43ec38011338031039b00c4388d78d91ac1083e0180bc27468a062024dc9a14f13025c559a21dc49410146000638f002c13e39c000fd0006d0228db1326c40004e28a6e4cc18c2a221c6905c304058b40b50de838611771b0010ea80032e458e280a39a6acd20ce29c28c8d8d52dc088579ad14e1a8551f63ea2a4221c238e674c89ec2667dced82d1c87c85084617a5ecef1140946e0dd1e532c560bd184170484dd8ff3dc3b0aa8c838c8306f8bc3282040581e334744000a40342c41984716e094070cb2185301813a1400640e0f601a0dc880fa00a4e0ba00002052c000a826a7000008a34a0ecfc1a63b447c2b8262f02b06b91231a454c91670d204ca919f216000360b33a40f4af1e8204334ba9562c21b85d0503925ac4315042833c95838244000700c12b41d00000000084047a1321c3d4000432d82ec001a0052084c096613855c718be0e6150f521a3a850c179d60b02200d861072654a21fb1a6844568a23940000009b000000be0003ae854001390f21d4b00d421082c9b0e80003c4000003642590412c2ba7bc420400b2784e99e34328080006b000278a388b00062c7a0f92d47aca08ca3883a8be800000000c31e64140006e8c914a00000000000000188b40003680003e1e03b40000134258c9d8b021e0003f1f10001950c00031e19c000001040000000000049c9000005005c981c12e20210697e2ca000fe1f400000024000000090661b30000009f0000005bcad92a12260cc41900001740a80
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2800c704f54914800041760000000044008000000e5000004800000062cd31610000000001300000000000086000686081831506350932a52e4218a0a0d18735085050714a90c0a0883831906254f21898eca9a8590d0c7454c32c8706318c4aa043431cd5410821858ecaa26410e0d5458f2108714a90c0a0e81515c84314530a28e8990a29864562147314c322a90c2980618318c6255320a18e6aa0859042c7655132c8306aa2c790e41831906254c20898eca9a841050c7454c3208306b22a6108418359153c8020
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x30020400080c8755163c842180c8755163c872080c87591530842080c8759153c8020
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20138+((h/221+packedAt s2K5 (17928+(h % 221)*10) 10) % 876)*11) 11
  | 4 => packedAt s2K4 (22272+((h/179+packedAt s2K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s2K3 (1273+((h/8+packedAt s2K3 (1225+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s2K2 (244+((h/1+packedAt s2K2 (240+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff81fffff81ffc1ffffff03fffcc7fe3f
  | 1 => 0xfc0fffffffffffe07fe0f81ffffffff388fff
  | 3 => 0xfff01ffe03f83fff8000ffe1ffc3e03c0f3cc
  | 4 => 0xf00001ffffc003fffffff0001fffc003ff03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x22441408c48910805940528a252252a8433615
  | 1 => 0x4092289109124116029205214a44a5511888ea
  | 3 => 0xab0a4da243a457aaa83149ed13ea381bc0d34c
  | 4 => 0xca2cb14492071acd34e560481cb31062ed03b0
  | 5 => 0xc30c1871c386371c7398e7180c02183b6ec00
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37341
namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037c86a06f10d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40bea98817e52103dca4205b94840bea9081ed52102daa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf29661ee52cc2dca5985f54b30f6a96616d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa71877d0e30ee21c617e528c3dca5185b94a30bea9461ed528c2daa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3b886185f94830bea9061df320c3ba64185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ee32083da64105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dd0410fa208217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a177d4d42afa9a857c5350bb8a6a15714d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0fb94b41b7296837d52d07daa5a0db54b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83be43907788720df94a41f7294836e52906faa520fb54a41b6a9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131efa1a63dc434c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031beaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x34c3680d1d81da87c090e62120012525a0ae17cba0000007c04700d0002552902321611038a784de000000a233e000e797644c53c0000010a930641261d09c8bc01038c210550b23900e8410354845e87c237392000001fb2ea9750014e0ac2912c8000009f44f0665020007e241000754cf211000000189ea000000001713ee108e60000f86411625851c0601c10d32c9d8da80c000308001a8000000001d01ac0005d0154d40011796f000600f300f38e7900014a0c498c13800142000001aa00048c14800236120002680b2694290250007b00000011a000000df09273440a970001a0ca0002d6001040000007c40020c000a1c002790004e48896d4a66b0001fc362000288003a8000980004900009600048e0000023f0aa8a81b800156134dc8004602a000000000380001b73564500010f252314c614c0006f49e1ae0f61849b1b34067092d89c0f40004d8004700008d273240000a28bf14695c36a433ae014fa000000000679102c2058e0a4f1867144400026404d1a0e42d48790a15731a5f0578002c69582c0d01f24ed2aa3b1660b82a1c02ee29d4a0000c0924cc0963f06802e1210007742595910c000fd27a214140c40754343dcff9a205e8806a098000001168e939483c002330000acc79e30000005613500035ca913e1ce5f545195112000fc9a14e2000419444fc4cc000000d2000000e1194000c580000000065a622ac00000000000000001fe0001746993d3ce0000015b0004b41f0002d8000000000004dc97807000080480102c030100000001020090001c08002000000240b0040100413010170000e03011000030580000030008000040203c0000000000040100300400000000040205c020000300407004000140001c01000010180000c01000010000301003000040000000000020000240000000038020000000c08008030100301400000050000001402018030000000000000010180100c0d0000c02c000000000800000000580400c0000c0500000000070040000400000000000a0381902c0002c0200c0200c0000c000040a01002000010001200813024080340100803014000000600c060040b00800008050100200000000050000001c0300c030900a014000000100000020000080a0240001c070580300000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485e
  | 3 => 0x978f78b10fc00148a36176240000000000010800023c16d1f1be00000000000000078000000008840020e000000dd800178370002540000013a90512e0010e0650c60054194b00c084528670042d01913f0b485c549380587d800020000000001f52249100014630270ca423c0000002080000044c4616222c13835a4d0000010c9d125441ca10f60544104c8000002483e9eb000089009ad1dc824e21e928e6c8f11bc4a2900c1a89000001441914dc9a4000002fc810000004040011c98408e3300b90242c2b8000000005b8c39891aa97c6019a3ca05111224456000b91a30dc4740c89d000a1845a270004ac0021b0005807623a086a311916830c36000000218000001662ca0007f00000048880a120c800000000000860ee000000201480c90000003c1d3292000140460009146c9280007cc000000005fc3f9e145c000398001bca14df80025c000bc8000720005e81b1d60001a0004c23bc000004d80009d140248000cc80046a9b4d800000097098958000000aa118000000000004f60014b0fd2b46d0a883b1400747110829a8752300006c418000f13a4128db16703e3e85307739c6e88f80016e6740006c2a649c781933daa54002672f66bccb8000ec2f800000000938498002e0001050001d40913e1df2bea10ae27418e69d4000000000027800416590c70d122a000000000000000380000000048a3d0000006e80022e3d0000003487b80000b0101c0f41030e44d14926411e114671414c076cae800462a4c000000000006d800000000000b6000a353800e00088c000003ac92c6085e1fe0fcaf16900021c000742a0670dc0b905a0014584041a3c800000022000000c61281a80009f0006288e20700072d0280351e9dc00000000000000fb0007f44d1f2000001330c444a2b45aa6b33638cc1000000000000004a00cc180090003cc929de0009fc001da000000000f500078109a29000464870002860000000a0002280004c0000f45c026450000b9a150382c000000000394802064ca1e4000000de3346900000061541000000554c91a9008764298000780000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb300c25f654c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63153209758c54c823f6454f208f19153c831f6454f20c719153c834c6254f20d354e42c82cc6350b20d354d42c834d53ccb20d354c32c82ad64c8720d354f21c834d53487209798f548825d63d52208f993538823d64d4e20ab191328823f64546208f19151882cd6308620b358f208825f63551209718d544826f62551209dd85544827461551209b58a534823f6454d208f19153482776154d209d185534826e65909209b19542482cc63509209b997324826e650c9209798c514825d63145209b99721482ad64c85208f596540825f63550209718d540831f6355020c718d540832c62550208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530825e63948209758e520826d65d0820cb553420826d6510820cb550420826d658c820cb552320826f654c820ab191320832d544c8209b596210832d5488420cb55021082cd6308420cb55320082cd63c80209bd95200832d54480209ed95200825e63d53109758f54c426e62d53109b58b54c426e62953109b58a54c423f6454f108f19153c426f6254f109b18953c426e6214f109b58853c423e6494b108f59252c425e6314b109758c52c425f63552109718d548426f62552109b189548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538426e6294e109b58a538425e6394a109758e528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534427b6054d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524435853c4110cd152104425e63d50109758f540426e62d50109b58b540423d6595010cd185540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043586054c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520433554d04109d594410435953cc0109e594300427965840109dd9510042b464440109ed9510042d86344010
  | 1 => 0xc66c62551319ed81544c67860551318f994544c65e65d0d31c7d50434c6cd6210d31cbd53524c72c54d4931cbd50524c72c5414931d3d0c524c74c4314931d314b324c69c644c931ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c7685214131d6d0c504c7584314131d6cc8504c7593214131d68c4504c65e63d50319b98b540c66d62d50319b988540c66d62150319e980540c6796015031d354b310c65f654c431d3549310c6d8604c4319dd95310c65f63553219718d54c871f6355321c718d54c872c62553218f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f21cb55342c872d5410b21cb55232c86ac644cb21cb55132c865e63d52219758f548863e64d4e218f59353886cc6350a21ab593218865f63542219718d508866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534866e65d09219b994424866e658c9219b19532486ac644c9218f990504863d64141219798f540865d63d50219b98b540865e63150219758c540867a60150219e580540865d6594c218fd91530863c6454c21c7d91530871c6454c21d3189530865e6314c219b988530863e64948218f592520866d6590821d354e420866f6550821b318d420874d53508219b597320874d53cc8219b594320874d530c821ab593210874d53c84219bd95210874d53484219dd95210866f6254f409b18953d02ad6210f40a718d42d025e63947409758e51d026e62947409b58a51d02ad62d07409b98a539026d6294e409bd89519026c6254640c7d4c43502ad6210d40d3d4f525034c53d4940d3d4c525034c5314940cb90c525032c4314940cb14b425029c6350940d5d4f515035453d4540d9d4b515036452d4540d5d4c51503545314540d9d4851503645214540cd90c51503344314540cdd08515033542145408f99741502ad62d0540cd14741503345150540cd146405023d6590440cb54a411032d5210440cb54b401023f6550040cb54940102b461500409ed95401026e62d53309b58b54cc27661d53309d58754cc26e62153309b58854cc34d52cc730d354931cc2d8604c7309b98b548c26d62d5230c7d8d548c26e62152309b588548c31d5410e30b3588438c32e5494a30cb552528c34f4394a30d310e528c32e5454a30cb551528c34e52cca30a7191328c2cd620c630b358b308c25f63551309bd89544c26c62551309dd85544c27461551309b988544c26d62151309b988514c26d621453097997314c2d8604c5309bd89540c26c62550309b988540c26d62150309d984540c275611503097594430c2cd6210c30b6580430c29c644c8308fd91510c23c64544309bd89510c26c625443097596310c2cd620c4308f992500c23d6494030b358
  | 2 => 0x5104558899840ba088e10000da64c001b807c000000d100006ce385507404c7f87e262510000000004b0a280000000000049000000e20003de000000a23ca83c6f0a929808c002140000009c000000848a517c0000204e0701707fc000000c6000201090000000017a3a2400000380c2348c81890000000000027882c000000a000000000432000000000000000c83d0006fc00000000000199221c0480010732b8370b795e3e44205c898346240ab80032a000001350a23743a87b1ec000f4816000080000000000000005e000000360000e2000001e30000000000015a0000000042a000001240000000000024c36c000003ee07c488e23920006c000000000001b700054cb200c2b67d0f51c32a02a0de1361d87845a0001c2034798623b00000000000014050000200004010020000000001000000000001400004070880000c0200400008050440000005014010000000400018000080202000010080140101c0402c08010050300000c0200403000000000100402000000081000003000070140200001040000080300001000010140b00001008020000a004000180d030040340001001028010000200000000000740100c010180500400000000000a0040000000000070140e0000b0000000005004040000d01004008030000000006000060000000000000030040101c020000100003000060100200001000010066e62947439b58a51d0e6f62543439b18950d0e6f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310e5e63947429758e51d0a5f63543429718d50d0aad6210e42d35885350b4c53d0942c714e4250a3f6550842a718d4210a6f6550842b318d4210a3f64547328f19151cca3e64943328f59250cca7a60152329e580548cacd6210e32e310e428cacc6350a328f992544ca5f63551329bd89544ca3e6515132cb588544ca6e6590932cb152424ca6c6550932cb151424cacc6350932cb153324cb1c548c9329d987540ca7561d50329b988540ca5d6510c329b597420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320cb1d5310e41ab588439074e5394a41d354e529072e4394a41cb10e529074e5354a41d354d529072e52d0a41a718d42906ad62d06419b988535066d6214d419b988505066d62141419bd89531066c6254c41ab58843106b56110c41a718d42106ad62d04418fd954110677655044197d8d501065c63540419bd89501066c62540419bd8954cc66c62553319b98854cc66d6215331b358843cc69c644cb318f99250cc63d64943319b98a50cc66d62943319b98b548c66d62d52319b98a548c66d62952319bd89508c66c6254231c758f544c63e64951319b98a544c66d62951319e982544c67960951319bd89544
  | 3 => 0x7688d91625c000551743940490c05618e00008814000000a71de00045c9417634c1e0bc82a0005fd0084a1c641c8a9f0124084e692935217ccc03601e418000fd2c41d02d0002da000eaa020006e8000002a8000141eb000000da07936c0000000000000069800286828731db0000006d0001764a8299821ea000e412134e11c008ef220000d71010004283f8c43b2204001120000010d0002fc604000a600077c0002c238474001403ba5689a00700023c000002b2684471ab0001a0000003ea0007c80024a7f0001af000358b714640658400095198000001b23386e4000000002d4001d427e00000000000000000b2408000228000b20b40000035a350000c5000000e81911125a0fc0f200043c2c20000053cdd86523c79c4381e13259c000002e6210998c139628ca88f100015c400b60005ec9f00030a759088a00003ed098d92840003d1411940a4600d7000000000000005ac0713709e010670e90206b1028960005f40014b36a0000001704c12c0006f0d452464000000648000b7030138b88ac000668578880001d8000000001100006040e00000000090000000002c01ac0000021c430739031663f80000000000000183000000b509d0684440009317c598af9ed0000008a0000000004d8000005a49c82e000000230e80a4658a69be0760009d8313364f4000f02d8214e980000000075866000838001fb25a6340000013e830c61c603a108192060006a80008a0003b8658000002f0000cf00025c00000000000cf0001f42e8d898f000000980a10c8000030d50ce3a8fb00000073ce7000000000000ab0006f48c0fc332700c408d000000828000007e4bb87d00016c529783e209c179520dc278b91630ee4108c9232aa090f60393c03b46f9b00a87701593233e0005f98e000014000c200000000000000000d980019a00000069348000c3800160790000000007045200b000000ff0001c8468a407c2560d45398a24e318f41940000f106800000000000410007e800000000000e60003a4000a38722ea000460373c48410499d134000979a00120000008b000000ac2170000000001a34a0000000032e618001800000000000004a0008680000020c18000000000000bd000130001a2000408001fd0003d0eb80000062c8f8000000000005c38a3dcf31ee000000000000007cc0e00000010c00094350000000ae0000fd040c9000028b293a02a0006190b0005c0ae84d000218588d01f000d0b0e
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1d32c83050040000005800890110180100000c600a3cd55700001448000e04008380200601831506350932a92e4218a098d18744c8504c724a90c0988638318c6255321a18e6aa08590c2c7655132c8706320c4a9843131d95350821a18e8a986410e0d6454f2108692b908628a81451cd4214540c4ac428e82a0625521854010324a90c098e61831906254f20898eca9a859050c7454c32c8306b22a790e418318c6255020a18e6aa0841042c765513208306aa2c6108418355163c8020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x458080c8759153c842180c8759153c872080c87551630842080c8755163c8020
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s3K5 (20138+((h/221+packedAt s3K5 (17928+(h % 221)*10) 10) % 963)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 860)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffc0ffffffffff81ffc1ff81fffffffcc78fff
  | 1 => 0xffffff81ffffffe07fe0fffff03ffff38fe3f
  | 2 => 0xfff01ffe03f83fff8000ffe1ffc3e03c0f3cc
  | 4 => 0xf00001ffffc003fffffff0001fffc003ff03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2052148904894100594092a1254462a84384d5
  | 1 => 0x42842810c9121096028a050a4a229551183a2a
  | 2 => 0xab0a4da243a457aaa82989ed13ea381bc0d34c
  | 4 => 0xca2cb14492071acd34ed20481cb31063ad03b0
  | 5 => 0xc30c1871c386371c731ce7180c02182f6ec00
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeec8c8a8a88888eeeec8c8a8a88888eeeec8c8a8a88888eeeec8c8a8a88888eeeec8c8a8a88888eeeec8c8a8a88888eeeec8c8a8a88888eeeec8c8a8a88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37341
namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x140000d1d380000000fd003003032f4a98da20a78f88129011624ac5936c10c0d021dbb85cf56be689d61114f002320c400f1ce401576a55286a5d08074659b20001800000a4438700000091a1428028001940a00180b7a92876c5250eeca221dd54443afa9a855c5350af4a0215e540429faa2653c544ca7ca8194f55032bb2886575510caf4a0195e54032bda82837850506bca620d754c419faa2633c544c6dea498db14931bda826378504c67ca818cf550319f2a6433d54c86f4a190de543219f2a4433d54886bca710d754e21bba8a817451502dca4205b548409f2a6613d54cc2eca3985d547309f2a4613d548c2dca5185b54a309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209faa2213c544427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fff03f07ffff07c1fffc1ff0f01fffd3e333f
  | 1 => 0xfffffc007fffff801f07fffff001fffe23fc3f
  | 2 => 0xe03fffff81f83fffe007fe0ffffe1e03c3cfcc
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x429118849452101d05495095091432a90e1315
  | 1 => 0x8522206928a423820a82a32a9029455220ec2a
  | 2 => 0x499449240d0254a52044d4832a4c181943454c
  | 3 => 0x962892484034a94a5390210cc4b18062b40ab0
  | 5 => 0x1830e38e71c73e739ce739c088c11183fbb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfac8fac8f888f888fac8fac8f888f888fac8fac8f888f888fac8fac8f888f888fac8fac8f888f888fac8fac8f888f888fac8fac8f888f888fac8fac8f888f888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37341
namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x62cc919760000010900b2607c20f2c012aa000000000140150001100009c5396a9942c5a7101a7e8c03e00dcc001244000000002974000001c30021560c034164cf0070f412e3a5d7872035b06786c0140602000030000200060400e0004000080c288b7a92876c5250ef4a021de54043afa9a855c5350aeca2215d544429faa2653c544ca7ca8194f55032bb2886575510caf4a0195e54032bda82837850506dca420db548419f2a6633d54cc6f4a198de543319f2a4633d548c6dca518db54a319faa2433c54486bea690d714d21bda824378504867ca810cf55021bba8a817451502bca6205754c409faa2613c544c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c82eca3905d547209f2a4413d54882bca7105754e209faa2213c544427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (718+((h/13+packedAt s5K5 (640+(h % 13)*6) 6) % 49)*7) 7
  | 4 => packedAt s5K4 (1875+((h/21+packedAt s5K4 (1728+(h % 21)*7) 7) % 92)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffff03f07ffff07c1f07ffff0f01fffd23f33f
  | 1 => 0x1ffffc007fffff801fffc1fff001fffe3e3c3f
  | 2 => 0xe03fffff81f83fffe007fe0ffffe1e03c3cfcc
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 4 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x82a118889454201e05816315091522a920d315
  | 1 => 0x4512206528a213810a4a90aa902855520e2c2a
  | 2 => 0x499449240d0254a52044d483a24c181a43454c
  | 3 => 0x962892484034a94a5390210c4cb18061b40ab0
  | 4 => 0x1830e38e71c73e739ce739c088c11183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888fca8f888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37341
namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54007f55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803fe4200ff50803fc4200ffcc803fe3200ff4c803fc32027fd4401fe51007f54409fc5101ffd0401fe41007f50407fc41017fcc405fe31017f4c405fc3100ffc8403fe2100ff48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40017fcc005fe30017f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842005ff0c21005ffe4108017fe2084017fe9042005ff08210007fe2108003f71084001fd8842000ffd9510005feca880037f65440013fb2a2010ff99510025fcca88003fd65440017eb2a2010ff19510025f8ca880037c65440093e32a2000ffd9110005fec888003bf64440015fb22200fff9911001dfcc888003fd64440017eb22200fff1911001df8c888003bc64440075e3222010ffd511007ffca888003fd544401ffe2a2200effd8d10075fec68803bfe63440057f31a200eff58d10075fac68803bfc63440057e31a200effd4d10077fca68803bfd534401dfe29a200effd0d10077fc868803bfd434401dfe21a200dffd891006dfec488037fe62440037f312200dff5891006dfac488037fc62440037e312200dffd491006ffca488037fd524401bfe292200dffd091006ffc8488037fd424401bfe212200dffcc91006ffc6488037fd324401bfe1922010ffd4510007fca288003fd5144021fe28a200fffd0510007fc8288003fd414401ffe20a200effcc510077fc628803bfd314401dfe18a200dffc851006ffc4288037fd214401bfe10a2010ffd4110007fca088003fd5044021fe282200fffd0110007fc8088003fd404401ffe202200effcc110077fc608803bfd304401dfe182200dffc811006ffc4088037fd204401bfe1022000ffc4110007f62088003fe1044001fb0822005ffd9410005feca0802bfe65040097f3282000df99410024fcca08003fd65040017eb282000df59410004faca08017fc65040097e3282005ffd9010005fec808027fe64040077f3202000ef9901001d7cc808003fd64040017eb202000ef590100057ac808017fc64040077e320200affd501004ffca808003fd5404013fe2a02005ffd8c10045fec608023fe63040057f3182008f798c10015bcc608023fd63040117eb182000f758c10005bac608017fc63040057e3182008ffd4c10047fca608023fd5304011fe2982008ffd0c10047fc8608023fd4304011fe2182005ffd881003dfec40801ffe62040037f3102007fb9881000ddcc40801ffd620400f7eb102000fb58810005dac408017fc62040037e3102007ffd481003ffca40801ffd520400ffe2902007ffd081003ffc840801ffd420400ffe2102007ffcc81003ffc640801ffd320400ffe190200cbf98410057fea20801bfe5104001fea882006ff1441004ffe820801bfe4104001fea082006ff10410047fe620801bfe3104011fe9882006ff0c41003ffe420801bfe210400ffe9082006ff0841005dfcc00802bff500400bff2802000ff5401002ff8a008027ff400400bff2002000ff5001002ff88008023ff300400bff1802008ff4c01002ff8600801fff200400bff1002007ff4801002ff8400801bff1004001fb8802005ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xffc425002fff9928017ff8c9400bffa64a005ffc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf185400cffea2a0003fe5150001fea8a8019ff1454001ffe82a000fbf4150007ff20a8003ff505400077a82a000ffc4150031ff98a8018ff8c5400c7fa62a0063fc315002fff90a8017ff885400bffa42a005ffc21500077fb028019ffd4140007fca0a0003fd5050033fe2828003ffd014001ff680a000ffe4050001df2028003ff1014001f7880a000ff84050031ff9828018ff8c1400c7fa60a0063fc305002fff9028017ff881400bffa40a005ffc205000dffb2e2000bfd97100b7fccb88012fe65c4001feb2e2000bf59710037f8cb88012fc65c400dffb262000bfd93100affcc98800efe64c4001feb262000bf59310037f8c98800efc64c402dffaa62015ff95310007faa988057fc54c400dffb1e2014bfd8f100a7fcc78800afe63c4029feb1e2014bf58f10037f8c78800afc63c4029ffa9e2014ff94f100a7faa788053fc53c4029ffa1e2014ff90f100a7fa8788053fc43c400dffb16200cbfd8b10067fcc588006fe62c4019feb16200cbf58b10037f8c588006fc62c4019ffa96200cff94b10067faa588033fc52c4019ffa16200cff90b10067fa8588033fc42c4019ff996200cff8cb10067fa6588033fc32c402dffa8e2006ff94710007faa38801bfc51c402bffa0e2006ff90710007fa838801bfc41c4029ff98e2006ff8c7100a7fa638801bfc31c4019ff90e2006ff88710067fa438801bfc21c402dffa862000ff94310007faa18805bfc50c402bffa062000ff90310007fa8188057fc40c4029ff9862014ff8c3100a7fa6188053fc30c4019ff906200cff88310067fa4188033fc20c400bffb2c2000bfd961009ffccb08012fe6584001feb2c2000bf5961002ff8cb08012fc658400bffb242000bfd9210097fcc90800efe6484001feb242000bf5921002ff8c90800efc6484027ffaa42012ff95210007faa90804bfc548400bffb1c2011bfd8e1008ffcc70800afe6384023feb1c2011bf58e1002ff8c70800afc6384023ffa9c2011ff94e1008ffaa708047fc5384023ffa1c2011ff90e1008ffa8708047fc438400bffb14200bbfd8a1005ffcc508006fe6284017feb14200bbf58a1002ff8c508006fc6284017ffa94200bff94a1005ffaa50802ffc5284017ffa14200bff90a1005ffa850802ffc4284017ff994200bff8ca1005ffa650802ffc328401b7eb0c2013ffd4610007fca308003fd5184027fe28c2012ffd0610007fc8308003fd4184025fe20c2011ffcc61008ffc6308047fd3184023fe18c200bffc861005ffc430802ffd2184017fe10c2007bf9821009ffea108017fe5084001fea842005ff14210097fe8108017fe4084001fea042005ff1021008ffe6108017fe3084023fe9
  | 2 => 0x50027faa8a8013fc545403dffb1aa01ebfd8d500f7fcc6a800afe635403dfeb1aa01ebf58d500f7f8c6a800afc6354009ffa9aa004ff94d50027faa6a8013fc535403dffa1aa01eff90d500f7fa86a807bfc435403bffb12a01dbfd89500effcc4a8006fe625403bfeb12a01dbf589500eff8c4a8006fc6254009ffa92a004dfd4950027fca4a8013fd525403bbea92a004ff149500effe84a8077fe425403bfea12a01dff109500effe64a8077fe325403bfe992a01dff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8002fc6154009ffa8aa004dfd4550027fca2a8013fd5154001bea8aa004ff145500fffe82a8003fe4154001fea0aa01fff105500f7fe62a807bfe315403dfe98aa01eff0c5500effe42a8077fe215403bfe90aa01dff08550025fec0a8013ff5054009fda82a004ff94150006fca0a8013fc5054009be282a004fe141500fffe80a807ffc405403dff982a01eff8c1500f7fa60a807bfc305403bff902a01dff881500effa40a8077fc205400bffb2c8000bfd96400e7fccb20012fe6590001feb2c8000bf5964002ff8cb20012fc65900077eb248003ffd524001ffca92000ffd5490007fe2a48005ffd8e400ddfec72006ffe63900057f31c801bff58e400ddfac720017fc63900057e31c801bffd4e400dffca72006ffd5390037fe29c8003ffd0e4001ffc872000ffd4390007fe21c8005ffd8a400d5fec52006bfe62900037f314801aff58a400d5fac520017fc62900037e314801affd4a400d7fca52006bfd5290035fe2948003ffd0a4001f7e852000ffe4290007fea14801aef50a4001ff8852006bff3290035ff194801aff4ca400d7f86520017ff6190001ff30c8000bf98640007fac320002fd619000bfe30c801cffd4640007fca320003fd5190039fe28c8003ffd064001ffc8320003be4190007fea0c8003ff1064001f78832006fff3190037ff18c801bff4c6400dff8632006bff2190035ff10c801aff486400d7f8432000efe6090039ffa848005ff94240007faa120017fc5090007ffa048003efd024001ff68120017fc4090007fc204801bffcc24002ffc612006ffd309000bfe184801affc824002ffc412006bfd209000bfe1048000ffd9540005fecaa0067fe65500097f32a8000ff59540005facaa0067fc65500097e32a8003bfd914001ffea8a000ffe5450007feaa28003ff151400c7fec6a0062ff6350031ff31a8002bf98d400c7fac6a0062fd6350031fe31a8002bf18d400c7fea6a0063fe5350031fea9a8018ff14d4001ffe86a000fbf4350007ff21a8003ff50d400c77a86a000ffc435002fffb128017bfd89400bffcc4a0006fe625002ffeb128017bf589400bff8c4a0006fc625002fffa928017ff949400bffaa4a005ffc5250007ffa128003ff9094001ffa84a000
  | 3 => 0xfa0c8203efd064101fee832081bfc4190407fa20c8227ffcc641037fc632089ffd319040dfe18c8226ffc8641037fc432089bfd219040dfe10c8206ffd8241007fcc120802fe6090401feb048200bf58241037f8c1208a3ff5090451fe2848203ffd024101ff8812080fbc409044fff9848227ff8c24113ffa612089ffc309044dff9048226ff88241137fa412089bfc2090401ffb2a8200bfd954112ffccaa0812fe6550401feb2a8200bf5954112ff8caa0812fc65504077fb228203ffd514101ffca8a080ffd5450407fe2a28224ffd8d41125fec6a0893fe63504057f31a8224ff58d41125fac6a0893fc63504057e31a8224ffd4d41127fca6a0893fd5350449fe29a8203ffd0d4101ffc86a080ffd4350407fe21a8223ffd894111dfec4a088ffe62504037f3128223ff5894111dfac4a088ffc62504037e3128223ffd494111ffca4a088ffd5250447fe2928203ffd094101f7e84a080ffe4250407fea128223ef5094101ff884a088fff3250447ff1928223ff4c94111ff864a080eff615044bffa8a8200ff94541007faa2a0897fc5150407ffa0a8203fdd054101ffc82a0803be4150407fe20a8203ef1054101fe882a0893ff3150449ff18a8224ff4c541127f862a088fff2150447ff10a8223ff4854111ff842a0803ff60504017fb028200ff98141007fac0a0803fc60504017e3028225ffd414112ff8a0a080fff4050407dfa028203ff10141127fe60a0893fe3050449fe9828224ff0c14111ffe40a088ffe2050447fe9028223ff08141025facb28017ff6494045ff324a003bf99250007fac928002fd649400bfe324a003bf19250027fea928013fe5494009feaa4a004ff1525002ffec728086ff6394043ff31ca002bf98e5010ffac728086fd639400bfe31ca002bf18e50027fea7280137f5394009ff29ca004ff54e5010efaa728013fc5394043ffa1ca021ff90e5010ffa8728087fc439400bffb14a020bfd8a50107fcc528006fe6294041feb14a020bf58a5002ff8c528006fc6294009ffa94a004ff94a50027faa528013fc5294041ffa14a020ff90a50107fa8528083fc4294041ff994a020ff8ca50107fa6528083fc329400bffb0ca000ff98650005fcc328003fd61940017eb0ca005ff18650027fea328013fe5194001bf28ca004ff54650027f8a3280137c5194045ffa0ca000ff90650007fa832808bfc4194043ff98ca021ff8c65010ffa6328087fc3194041ff90ca020ff88650107fa4328083fc21940097f304a004ffd4250026fea128013fb509400bfe284a004fe14250117fe8128017fc4094043ff984a005ff8c25010ffa6128017fc3094041ff904a005ff88250107fa4128017fc20940097fb2aa000ffd9150005fec8a807ffe64540077f322a000ff591500fff8c8a800efc6454009ffaa2a004ff951
  | 4 => 0x80efc6494409ffaa4a204ff95251027faa928813fc549440dffb1ca22dbfd8e5116ffcc72880afe639445bfeb1ca22dbf58e51037f8c72880afc6394409ffa9ca204ff94e51027faa728813fc539445bffa1ca22dff90e5116ffa87288b7fc439440dffb14a22cbfd8a51167fcc528806fe6294459feb14a22cbf58a51037f8c528806fc6294409ffa94a204dfd4a51027fca528813fd5294459bea94a204ff14a51167fe85288b3fe4294459fea14a22cff10a51167fe65288b3fe3294459fe994a22cff0ca51025fcc328813ff5194409bfa8ca204fdd4651037f8a328813f4519445dffa0ca206ff1065116ffe632881bfe319445bfe98ca206ff0c651167fe432881bfe2194459fe90ca206ff08651037fec128803fe60944017f304a200ff58251005fac12881bfc6094409ffa84a204ff14251026f8a1288bbff409445dfe204a22dffcc25116ffc61288b7fd309445bfe184a22cffc8251167fc41288b3fd2094459fe104a204bfd9551007fec8a8802ff6454457ff322a203bf99151007fac8a88affc64544077e322a204ffd5151027fca8a8813fd5454409fe2a2a22affd8d51155fec6a88abfe63544057f31aa22aff58d51155fac6a88abfc63544057e31aa204ffd4d51026fea6a8813fe5354409fea9aa22adf54d51027f8a6a88abff4354455ff21aa22aff50d51157f886a88a7ff62544537fb12a229ff9895100dfcc4a88a7fd62544537eb12a229ff1895100df8c4a8813ff5254409ff292a204ff54951027f8a4a88a7ff4254453ff212a229ff5095114ff884a88a7ff3254453ff192a229ff4c95114ff864a8812ff6154409ffa8aa204fdd4551027fca2a88037e5154409fe28aa204df14551027e8a2a88afff4154457fe20aa22affcc551157fc62a88abfd3154455fe18aa229ffc855114ffc42a88a7fd2154453fe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151005f8c0a8813ff5054409bfa82a204ff1415115ffe80a88affc4054455ff982a22aff8c151157fa60a88abfc3054453ff902a229ff8815114ffa40a88a7fc205440dffb2c8200bfd9641147fccb20812fe6590401feb2c8200bf59641037f8cb20812fc65904077eb248203ffd524101ffca92080ffd5490407fe2a48206ffd8e4113dfec72089ffe63904057f31c8227ff58e4113dfac72081bfc63904057e31c8227ffd4e4113ffca72089ffd539044ffe29c8203ffd0e4101f7e872080ffe4390407fea1c8227ef50e4101ff8872081bff629044d7fb148226ff98a4100dfcc52089bfd629044d7eb148206ff18a4100df8c52089bff529044dff2948226ff54a41137f8a52080fff4290407ff2148203ff50a4101ff8852089bff329044dff1948226ff4ca41137f8652080efe6190451ffa8c8206ff94641007faa32081bfc5190407f
  | 5 => 0xcac0bcce875011c4380e0ea800000000075406437888409c4807ac920000f1cab8844000988adc2f0ad8000ba8a887909081410a48c47dca544ac78cb4409444446418c00000c020000180000080100000800005000004028020000040280000a02c0080800c0000000000200c0080b0100000a80300a0040000400004801005004010048030040100000400a0000280a00600c01001006000000060560000200700000c0200000e0680000000000401000002000000040060200000102c0400a0050100000000303200804000004018018060060000680301602809815004010068010000140800000601407801000004008000000500180a0000240180302402400000000020010000000140100200201c040000040100c00001001c00804012018020000020040000b00000c0800900c04c0180000c0000101800a010020040000000180300a0180100501c0080180301000402802002000000000000140300e000000010000040000081b000000008000000100000700600c0600700800c000000240200100300a004010040000040181f02e05c000000020040d004004040008010000240182e0040040280005201c0800400800c07000002000020010000000001200a01c0000f00201800010010024000020040000202e002014000030500040380400a00400004000014038010000000880200e0040000500c04c0080001402002801000038020000040080100c00800000000008000000000000240101e00600401000004000020050000900280400a000028020000000880000000c01800000004000090020000580000205c010020000080001500201401803006014000040000440080eff65550077fb22a803ffd51540277ea8aa00ffe5455007bf2a2a803ff1515401ef8a8aa00fbc5455061ffb1aa830bfd8d54187fcc6aa00afe6355061feb1aa830bf58d54187f8c6aa00afc6355009ffa9aa804ff94d54027faa6aa013fc5355007ffa1aa803ff90d5401ffa86aa00ffc435505fffb12a82fbfd895417ffcc4aa006fe625505ffeb12a82fbf5895417ff8c4aa006fc6255009ffa92a804ff94954027faa4aa013fc5255007ffa12a803ff9095401ffa84aa00ffc425505fff992a82fff8c95417ffa64aa0bffc3255001ffb0aa800bfd8554007fcc2aa003fd6155001fe30aa800bf18554027fea2aa013fc5155007ffa0aa803ff10554187fe62aa0c3fe3155061fe98aa830ff0c55417ffe42aa0bffe215505ffe90aa82fff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa002fc6055009ffa82a804ff1415401ffe80aa00ffc4055061ff982a830ff8c154187fa60aa0c3fc305505fff902a82fff8815417ffa40aa0bffc20550097eb2ca206ffd9251177fcc92880efe6494401feb24a200bf59251037f8c928
  | 6 => 0x8d406d0d589dcf34ad07a46d4c2c8710a8ef8f74cb8c810203008480000000004d80000000005c0e78c243189780240009bc000dbc000000804001178548000e700000003f48951f8000000000050000258088afc41400035404516ccd0b50b2438c00030c6d8bd4d940004cceb50007cc6383f11b08d4e2513d08014450921cf98540130ed442c56c0000002c8bacd88fa10106b8e6495836c3c872400062d0f47e48d0d0c904180720d54000000e0c6789e00001b07586fc87430475c3346c8000000bb42210c515c000b6000010400000000000021d2441e82d4035114aa4cf415c000000000dd498cdf80000000010088203c4798ccc79447c00033028c0009ccd08e1835c0008581109f4b7c880000bb8000d8045c81893ca440000012407d40b8244000000000000bf838427c00000128400005ca800000000004185a88f9259294a4cd509149c8925128df4d64c6c9847b0454a78000854f9081400000000000000128000000000000000072c100e1c0000000a8000000000a38000740000000000000000000be4000000e39171024dc84250a00004d0000000000d040000000000000008e81f1019088a5c000ce4000e88530b70f64b1c4fcfb8630980f7c4f0e4cf081b9060810f4460c0000000000010c8000c080008400002a8d2ca506680000000000009e4860d34bec06c780b146a4658d98608000168cf0ff88c0004b40b94068a04000768a34030370e6076ced8accb0cfa50d83e8000ca400000000000000000000000012c000001249274000364760000598000b012983a417c0004e1180764fb00000000905e09a883840c1a03dc000f5caa92701ac0cc000000000ab0b8000112c5a525472860400000000057d2a8000000c9000064000077800110800000000000055c00000120c000000b8c34873c4a8000578fe4000a1046089c000b38190000000000898ee0000594fcc6ec000000324000928d3c60064c6ccfdc000d68000dec7b459026cd5c9c05fc84c2bc03841c2fc21800101c2511fc54cc48248c44b68498bc010846891c2d0e283147ec8787a8960e69288da49e88d8de0ff00fcc0499cab4e10a685f8ba482c9b00011186dcbcc44861c000000000000b10000000710f200007140000001f40000002ac000000000000000000000000000000fb4000618624c780003682c51bcee50dd17cd381a8288514cbc20c1b4eec1511b82643210900005100003400003cc4dc62000078529c78902d1f4000ae40000010f8684000394000000000164000efc388001140000b903508fc00068000000000000000063cf88a091f0000ea02a0e411d800032c2e45392205702e1104000e20000000000000000abca3cc0ca28e54f18f150b4d608b4000188000204000000f6870109c1986b019ceb80004c00000000011a0bd11840
  | 7 => 0x13000000000031cdd800001c4b033cb0443c0c00000006e8000ffc990000470b9c82448c5d89ed290d305b80001e025c23800087c00000000034c000eac0000780000000000000011904f8000c5800088800029c0000000000000002dc770000000000000000a70d8c0e890c0008c8664cf8000ac40008340000000002e80000000000000001bc5e50052a1064ec90b84bc891110f4c000ba093503c0002340001d0000f2c000d750980580f80000007c0000614ebd0e4000f705240c50e91cd2a4a98f043e4ef477c000000e44f3d25ca1c1f813486c5ac0009a01288a82f8000b280006940000011000008dd034000c4c08c610e9cc502c0000a8c000000000000000994744000434000bf00b100ccb0ac8400451058b4c0d0b08c38c300003a91345ec0000483e10b0000000000000000000000b6400104c000000000c540000000000000000000000000003d85e894c3800280000000000000ad1c051c0000851c4000000518bbcf8400000000000044116817921522c9fd1385640006884c87c4000000000000000000000000dcc398358fac0009b80000011c868c520c210403101e44a03f8b89228dd04b46286f40d9048254c34da8000e5ccb40004741590ecbd89d8e040180811511441d8e74a3024c9448689648bc7f0f806909a47d0ec0de4214830000040278c74e6c000ddc4783383083a0000000000c68d911951ec0e4000504998c9907ca2082865c2d8d7c390cc0000e80b74000294120b2121910c938c18940ce0000e48568000a907c80008ac000000eb00002900f45d48cc95caf0670000000f40000000e300000010505847e09506f8900c94bfd1d4000dc4b185344841c86c12045d09d0dfd12085c6c4000574554f9c0001240006ad22400000118cd1858080c4f4000c88000ed03c0000fec0011a4000000000704000550000cdc00107101444c6e4e8458c8e4d28a582b5074948674655200c64fa8a411744d466052c0010bd0d0fd000002cb78f60bc8d84e9400ca7cfe00000a4aa01487d8ca0910588b851540000006e0000a4800002126d078634a74f300006a01dc00079c0007a0428000174708dc00600c8000000f50000098d1470ca64e911d0d002081fc8f0de823cb3c0000005dd2683b83b4000e34528000000000b591600000004043608e0af897c0d4cc80000000000008084a40011e4000001044774ef0a2ce580a0d444ec0006988b87383bc000000fd40012350c10f0cd8458b2c0012640000005b4000000000c280011e0b6c0008f4f0c000011124f100000000002f42a41eca00000001158001085230f000000002ec00000074cfc4000000000ecd0ac0000000000010380000010d51e8000000c00db4db8d10c8ccc42b07fc95411439c000c3c3289189f0a9c9709745c4cd4ad43d0420408800268bf4e0
  | 8 => 0x11484e400111c4900f000081c59c2305ccbdc88cd9cbb003c00017010c3fc000ae00000000002b800124c0000000006440000000000000000000000005c8f94000000ee800119c05449c000000f6c00000001505c46c8a40000000000b506c0007300009ac0000000003ec0004880010687bc83c001198e3d028a18c70e985f48ec000d4d27cd70a60930ac0f28e8d23c000000b48000d20000e00edc000000154000a14000f585f00002281a4000a24224f79278fbcca8e5000014ccfcbe12388b10cd08c2701d4da004c000c40c14af4c84d780009d40000008a01c00003b08640000000000000000004b81c4b34000ec4f54c7c22c9f80003ac648f8cb5400037528cb980000009c4aac000000160000344000008850c11030cec13926114c001210544f24be8560df05b0d1c50d1b4a6c18407cc9c3d51dc6a8aec298b30194000a940004c400000000000000067c118c5c410000000d480006f0210fe8748430f480dc53c0000006bc0000011ac2740002ccc610e00010fc9b47191892504e909413c00071c0005a0001164b5c240000db0ea4bc4fd86b47e892c96c7f8ae8494d24ff40ec69d1a8e7c968f38500c1cdac734d6c16c650fc07f4000fc82600007b9208070000558a0c00000000037c2800001cc074e15054200284a84e2c5bc66d
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881003eef7158810036ee715881003eed7158810036ec7158810006ef5158810036ee5158810036ec5158810006ef4158810036ee4158810036ec4158810006ef3158810036ee3158810006ed3158810036ec315881003eef705881002eee705881003eed705881002eec7058810006ef505881002eee505881002eec5058810006ef405881002eee405881002eec4058810006ef305881002eee3058810006ed305881002eec3058810036ef105881002eee105881002eec10588100b4ff76544100267e65544100067d655441015ebe6454410006bd6454410156de6354410006dd635441014eee6254410006ed62544100acff765041012e7e65504100067d655041001ebe6450410006bd6450410126de6350410006dd635041011eee6250410006ed6250410037b4415041009cff76540100267e65540100067d65540100febe6454010006bd64540100f6de6354010006dd63540100eeee6254010006ed6254010094ff76500100ce7e65500100067d655001001ebe6450010006bd64500100c6de6350010006dd63500100beee6250010006ed625001002fb84050010036f576c401002f7665c401002f7565c401002fb664c401002fb564c401002fd663c401002fd563c401002fe662c401002fe562c401002df570c401002ef660c401002df9768401002ef9768401000cf9768401002f7a658401002f79658401002fba648401002fb9648401002fda638401002fd9638401002fea628401002fe96284010035f97184010036fa618401002ff26184010004ff76440100057f75440100557c75440100867e65440100067d6544010005bf744401004dbc744401007ebe6444010006bd6444010076de6344010006dd634401006eee6244010006ed624401002df77644010006f77644010004f7764401000777754401000774754401002f76654401002f756544010007b77444010007b4744401002fb6644401002fb5644401002fd6634401002fd5634401002fe6624401002fe5624401002df7704401002ef6604401002ff25044010007f1504401018ff3404401002ff04044010035fb7644010006fb7644010004fb76440100077b75440100077875440100377a6544010037796544010007bb7444010007b87444010037ba6444010037b96444010037da6344010037d96344010037ea6244010037e9624401002dfb714401002ff37144010036fa6144010037f26144010037f25144010007f1514401018ff34144010037f04144010
  | 1 => 0x9010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901004ebf7159010036be7159010036bc7159010006bf5159010036be5159010036bc5159010006bf3159010036be3159010006bd3159010036bc3159010006bf2159010036be2159010006bd2159010036bc215901004ebf705901002ebe705901002ebc7059010006bf505901002ebe505901002ebc5059010006bf305901002ebe3059010006bd305901002ebc3059010006bf205901002ebe2059010006bd205901002ebc2059010036bf105901002ebe105901002ebc1059010004ff765501002cfe7655010004fd765501002cfc76550100267e65550100067d655501001ebe6455010006bd6455010186de635501017eee6255010005f77155010035f47155010005fb705501002df8705501002ddf7658c10046df7658c10014df7658c1002edf6558c10006de6558c1002f5e6558c100065e6558c10006dd6558c1002f5d6558c100065d6558c1002edc6558c1002edf6458c10006de6458c1002f9e6458c100069e6458c10006dd6458c1002f9d6458c100069d6458c1002edc6458c1002edf6258c10006de6258c1002fce6258c10006ce6258c10006dd6258c1002edc6258c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10046df7158c10036de7158c10046dd7158c10036dc7158c10006df5158c10036de5158c10036dc5158c10006df4158c10036de4158c10036dc4158c10006df2158c10036de2158c10006dd2158c10036dc2158c10046df7058c1002ede7058c10046dd7058c1002edc7058c10006df5058c1002ede5058c1002edc5058c10006df4058c1002ede4058c1002edc4058c10006df2058c1002ede2058c10006dd2058c1002edc2058c10036df1058c1002ede1058c1002edc1058c1002def765881003eef765881000cef765881002eef6558810006ee655881002f6e65588100066e6558810006ed655881002f6d65588100066d655881002eec655881002eef6458810006ee645881002fae6458810006ae6458810006ed645881002fad6458810006ad645881002eec645881002eef6358810006ee635881002fce6358810006ce6358810006ed635881002fcd6358810006cd635881002eec6358810006ef7558810006ee7558810006ed7558810006ec7558810006e
  | 2 => 0x67d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067d32594100067c32594100567f71594100367e71594100367c71594100067f41594100367e41594100367c41594100067f31594100367e31594100067d31594100367c31594100067f21594100367e21594100067d21594100367c21594100567f705941002e7e705941002e7c70594100067f405941002e7e405941002e7c40594100067f305941002e7e30594100067d305941002e7c30594100067f205941002e7e20594100067d205941002e7c20594100367f105941002e7e105941002e7c1059410024fe75d901002e7e75d90100247e75d9010004fd75d901002e7d75d90100047d75d901002cfc75d901004cfd74d901002cff73d9010014fe73d901002ede73d9010014de73d9010004fd73d901002edd73d9010004dd73d901002cfc73d901002cff72d901000cfe72d901002eee72d901000cee72d9010004fd72d901002eed72d9010004ed72d901002cfc72d9010034fe71d901002ef671d901002cfe70d901002efa70d9010004bd769901002ebf6599010006be659901002f3e65990100063e6599010006bd659901002f3d65990100063d659901002ebc659901002ebf6399010006be639901002f9e63990100069e6399010006bd639901002ebc639901002ebf6299010006be629901002fae6299010006ae6299010006bd629901002ebc6299010036be619901002ebe609901001cff76590100067e65590100067d655901002ebc6459010006de6359010006ee6259010004ff7559010024fe7559010024fc755901002cff745901002ebf7459010006bf545901004ebe545901004ebc5459010004ff7359010014fe7359010004fd7359010014fc735901004ebf4359010006be4359010006bd435901004ebc4359010004ff725901000cfe7259010004fd725901000cfc725901004ebf4259010006be4259010006bd425901004ebc425901001cff7159010034fe715901001cfd7159010034fc7159010036be4159010036bc415901001cff705901002cfe705901001cfd705901002cfc705901002ebe405901002ebc405901002dbf765901004ebf765901001cbf765901002ebf6559010006be655901002f3e65590100063e6559010006bd655901002f3d65590100063d655901002ebc655901002ebf6359010006be635901002f9e63590100069e6359010006bd635901002ebc635901002ebf6259010006be625901002fae6259010006ae6259010006bd625901002ebc6259010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be535
  | 3 => 0xf65905101467c6590510006bf649051001ebc649051001cfc76505100067f655051012e7c6550510006bf645051001ebc6450510005fb7050510005f870505100b4fe76941100067f65941100267c6594110006bf6494110116bc6494110024ff7654110084fd7654110024fc76541100067f65541100267c6554110006bf64541100febc6454110005f77154110005f471541100acfe76901100067f65901100e67c6590110006bf649011001ebc649011001cff765011007cfd765011001cfc76501100067f65501100ce7c6550110006bf645011001ebc6450110005f77150110005f471501100067f65c41100b67c65c4110006bf64c41100aebc64c41100077b65c41100077865c4110007bb64c4110007b864c41100067f658411009e7c6584110006bf6484110096bc648411006df67684110007776584110007746584110007b76484110007b46484110007f36084110054fd75d941001cfe74d941002ebe74d941001cbe74d9410004fd74d941002ebd74d9410004bd74d941002cfc74d941002cff73d9410014fe73d941002ede73d9410014de73d9410004fd73d941002edd73d9410004dd73d941002cfc73d941002cff72d941000cfe72d941002eee72d941000cee72d9410004fd72d941002eed72d9410004ed72d941002cfc72d9410034fe71d941002ef671d941002cfe70d941002efa70d94100047d769941002e7f64994100067e649941002e7c649941002e7f63994100067e639941002f5e63994100065e63994100067d639941002e7c639941002e7f62994100067e629941002f6e62994100066e62994100067d629941002e7c62994100367e619941002e7e6099410024ff765941002e7c6559410006de6359410006ee625941002cff755941002e7f7559410004ff745941001cfe745941001cfc74594100567f54594100067e54594100567c5459410004ff7359410014fe7359410004fd7359410014fc73594100567f53594100067e53594100067d53594100567c5359410004ff725941000cfe7259410004fd725941000cfc72594100567f52594100067e52594100067d52594100567c5259410024ff7159410034fe7159410024fd7159410034fc71594100367e51594100367c5159410024ff705941002cfe7059410024fd705941002cfc705941002e7e505941002e7c505941002d7f76594100567f76594100247f765941002e7f64594100067e645941002e7c645941002e7f63594100067e635941002f5e63594100065e63594100067d635941002e7c635941002e7f62594100067e625941002f6e62594100066e62594100067d625941002e7c62594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e4359410
  | 4 => 0x95100067d62195100067c621951001cfe76d91100067f65d91100067c65d911007ebe64d9110024fe75d9110004fd75d9110024fc75d9110006bf54d911007ebe54d911007ebc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d911007ebf43d9110006be43d9110006bd43d911007ebc43d9110004ff72d911000cfe72d9110004fd72d911000cfc72d911007ebf42d9110006be42d9110006bd42d911007ebc42d9110034fe71d911007cfd71d9110034fc71d911007ebf41d911002cfe70d911007cfd70d911002cfc70d911007ebf40d911007dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d911007ebe71d9110006bd71d9110006bf51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d911007ebe70d9110006bd70d9110006bf50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110006bf20d9110006be20d9110006bd20d9110006bc20d91100057f75591100857c75591100067f65591100067c655911007ebc6459110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c755911007cff7459110006bf7459110004ff7359110014fe7359110004fd7359110014fc7359110004ff725911000cfe7259110004fd725911000cfc7259110094ff7159110006f771591100acff7059110006fb7059110005be761911007ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc6319110006bf6219110006be6219110006bd6219110006bc6219110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100267c6555110006bf645511001ebc645511009cfe76945100067f65945100267c6594510006bf6494510176bc6494510024fc76545100067f65545100267c6554510006bf645451015ebc6454510005fb7054510005f87054510094fe76905100067
  | 5 => 0xcfe7259210004fd725921000cfc7259210096bf415921002ebe405921002ebc4059210004ff765521002cfe7655210004fd765521002cfc7655210005f77155210005f47155210084fd76946100067f65946100267c659461009f775194610024ff765461002cfc76546100267e65546100067d6554610005fb705461002df8705461007cfd7690610006bf649061001ebc649061001cff765061002cfc765061001ebe6450610006bd6450610097b44150610005fb705061002df87050610054ff765421002e7f655421002e7c655421004cff765021002ebf645021002ebc645021002df576c4210006f576c4210005f976c4210036f976c4210024fe76d95100867e65d951001cfe74d9510004fd74d951001cfc74d95100867f54d95100067e54d95100867c54d9510004ff73d9510014fe73d9510004fd73d9510014fc73d95100867f53d95100067e53d95100067d53d95100867c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100867f52d95100067e52d95100067d52d95100867c52d9510034fe71d9510084fd71d9510034fc71d95100867f51d951002cfe70d9510084fd70d951002cfc70d95100867f50d95100857e76d95100247e76d95100067e64d95100067c64d95100067f63d95100067e63d95100067d63d95100067c63d95100067f62d95100067e62d95100067d62d95100067c62d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95100867e71d95100067d71d95100067f41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95100867e70d95100067d70d95100067f40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d95100067f20d95100067e20d95100067d20d95100067c20d95100867c6559510005bf745951007dbc7459510084ff75595100067f7559510004ff7459510006bf7459510004bf745951001cfe745951001cfc7459510006bc745951001cbc7459510004ff7359510014fe7359510004fd7359510014fc7359510004ff725951000cfe7259510004fd725951000cfc725951009cff7159510006f771595100b4ff7059510006fb70595100057e76195100867e76195100047e76195100067e64195100067c64195100067f63195100067e63195100067d63195100067c63195100067f62195100067e621
  | 6 => 0xc74d9710034ff73d9710014fe73d9710004fd73d9710034fc73d9710034ff72d971000cfe72d9710004fd72d9710034fc72d97100b67f52d97100067d52d9710036f671d97100367f51d9710036f970d97100b67c50d9710024ff76597100367c65597100367f7559710004ff745971001cfe745971001cfc7459710004ff7359710014fe7359710004fd7359710014fc73597100b67f53597100067d5359710004ff725971000cfe7259710004fd725971000cfc72597100367e51597100367c51597100b67f5059710024fe75d9310004fd75d9310034fc75d93100acfd74d9310034ff73d9310014fe73d9310004fd73d9310034fc73d93100aebf43d9310006bd43d9310034ff72d931000cfe72d9310004fd72d9310034fc72d9310036f671d9310036bf41d9310036f970d93100aebc40d931001cff7659310036bc6459310004ff7559310024fe7559310024fc7559310036bf7459310004ff7359310014fe7359310004fd7359310014fc7359310004ff725931000cfe7259310004fd725931000cfc72593100aebf4259310006bd4259310036be4159310036bc41593100aebf4059310004ff7655310034fe7655310004fd7655310034fc7655310005fb7055310005f87055310054ff76547100367f65547100367c655471004cff7650710036bf6450710036bc6450710084fd76943100067f65943100267c65943100b77b5094310024ff7654310034fc76543100267e65543100067d6554310005f77154310035f4715431007cfd7690310006bf649031001ebc649031001cff7650310034fc765031001ebe6450310006bd6450310005f77150310035f471503100afb8405031009cfd75d961001cfe74d9610004fd74d961002cfc74d961002cff73d9610014fe73d9610004fd73d961002cfc73d961009e7f53d96100067d53d961002cff72d961000cfe72d9610004fd72d961002cfc72d961002ef571d961009e7c51d961002efa70d961002e7f50d9610024ff765961002e7c655961002e7f7559610004ff745961001cfe745961001cfc7459610004ff7359610014fe7359610004fd7359610014fc7359610004ff725961000cfe7259610004fd725961000cfc725961009e7f52596100067d525961009e7f515961002e7e505961002e7c5059610024fe75d9210004fd75d921002cfc75d9210094fd74d921002cff73d9210014fe73d9210004fd73d921002cfc73d921002cff72d921000cfe72d9210004fd72d921002cfc72d9210096bf42d9210006bd42d921002ef571d9210096bc41d921002efa70d921002ebf40d921001cff765921002ebc6459210004ff7559210024fe7559210024fc755921002ebf7459210004ff7359210014fe7359210004fd7359210014fc7359210096bf4359210006bd4359210004ff7259210
  | 7 => 0x46401cebf63906401cebd63906401c5bf72906401c5bd729064001dbe719064001fb67190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b9709064001ebe609064001fba60906401bcff76542400ffbb4054240024fe76d95400ce7e65d954002cff74d954001cfe74d9540114fd74d954001cfc74d95401167f54d95401167d54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400ce7f53d95400067d53d9540004ff72d954000cfe72d9540004fd72d954000cfc72d95400067e52d95400ce7c52d9540034fe71d9540004fd71d95400ce7c51d954001cfd70d95400ce7f50d95400ce7c6559540005f77159540005f471595401bdfb7059540114ff75595400067f75595400fcff7459540006bf7459540004ff7359540014fe7359540004fd7359540014fc7359540004ff725954000cfe7259540004fd725954000cfc7259540004ff7159540006f77159540004f77159540034fc7159540006f47159540004f471595401bcff7059540006fb7059540024fe75d8540004fd75d8540024fc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d8540006f751d8540006f451d8540096f641d8540096f541d8540006f631d8540006f531d8540006f721d8540006f421d8540006f7619854007df970985400057f75585400cd7c75585400adfb70585400bdee7218540005ed7218540006f56118540024fe7518540004fd7518540034fc7518540034ff7318540014fe7318540004fd7318540034fc731854004ebf4318540006bd4318540034ff721854000cfe7218540036ee721854000cee7218540004fd7218540036ed7218540004ed7218540034fc7218540006f75118540036f45118540036bf4118540036f6411854004ef54118540036f63118540006f53118540006f72118540036f4211854004ebc4018540004fe7694540004fd7694540034fc76945400067f65945400267c659454001dbe7494540005bd7494540004ff7654540004fe7654540004fc76545401b5bf73505401b5bd73505401aebf62505401aebd625054001dbf715054001fb77150540007b76150540036bc6150540007b46150540006b46150540007bb705054002dbc7050540007b87050540005b8705054001ebf605054001fbb60505401a4fe76941400cf7b509414002fb84094140024ff765414001cfe76541400fcfd765414001cfc76541400067f65541400267c6554140005bf745414001dbc74541400ffb8405414002dbf739014019dbd7390140196bf6290140196bd6290140005bd7190140006bc619014002dbe709014002fba709014002ebf609014001fbb60901400b4fd75d971001cfe74d9710004fd74d9710034f
  | 8 => 0x14fe73d8550004fd73d8550014fc73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d855009ef651d855009ef551d8550006f741d8550006f441d8550006f731d8550006f431d8550006f621d8550006f521d8550006f76198550085f97098550005bf74585500fdbc74585500b5fb70585500f5de7318550005dd7318550006f5611855001cfe7418550004fd7418550034fc7418550034ff7318550014fe7318550036de7318550014de7318550004fd7318550036dd7318550004dd7318550034fc7318550034ff721855000cfe7218550004fd7218550034fc72185500567f52185500067d52185500367f5118550036f65118550056f55118550006f74118550036f44118550006f73118550036f43118550036f62118550006f521185500567c50185501ee7f63545501ee7d63545501e57f72545501e57d72545500257f71545500277771545500077761545500367c61545500077461545500077b705455002d7c70545500077870545500267f60545500277b6054550004fe7690550004fd7690550034fc76905500257e75905500057d7590550006bf649055001ebc6490550004ff7650550004fe7650550004fc76505501de7f63941501de7d639415002d7f72941501d57d72941500057d71941500067c619415002d7e709415002f7a709415002e7f60941500277b60941500fcfd75d964002ebd74d964002cff73d9640014fe73d9640004fd73d964002cfc73d964002cff72d964000cfe72d9640004fd72d964002cfc72d9640034fe71d9640004fd71d964002cfe70d964002efa70d9640024ff765964002e7c655964002e7f75596400fe7f54596400fe7d5459640004ff7359640014fe7359640004fd7359640014fc73596400067e53596400e67c5359640004ff725964000cfe7259640004fd725964000cfc72596400e67f52596400067d5259640004ff7159640034fc71596400e67f515964002cfe705964002cfc705964002e7e505964002e7c505964002ef76198640024fe7598640004fd7598640034fc7598640034ff7398640014fe7398640004fd7398640034fc7398640034ff729864000cfe7298640004fd7298640034fc7298640036f641986400aef5419864002cfe709864002cfc709864002ef6109864002ef4109864002ef46158640004ff7558640024fe7558640024fc7558640004ff7358640014fe7358640004fd7358640014fc7358640004ff725864000cfe7258640004fd725864000cfc725864007ebf4258640006bd425864007ef6415864007ef5415864007ebc415864002cfc705864007ebf405864002ef6105864002ef41058640034ff769464002cfe7694640004fd7694640004ff7654640004fd765464002cfc76546400267e65546400067d6554640005bf745464001dbc745
  | 9 => 0xf619054101fb76190541005bd7090541024fe75d8141004fd75d8141024fc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d8141006fb50d8141006f850d81410aefa40d8141006fb30d8141006f830d8141006fa20d8141006f920d8141006fb60981410057f755814112d7c7558141125de7318141005dd7318141006f96018141024fe7518141004fd751814102cfc751814102cff7318141014fe731814102ede7318141014de7318141004fd731814102edd7318141004dd731814102cfc731814102cff721814100cfe7218141004fd721814102cfc721814104ebf4218141006bd4218141006be411814104ebc4118141006fb501814102ef8501814102ebf401814102efa401814104ef94018141006fb301814102ef8301814102efa2018141006f9201814101cff765925002ebc6459250116be54592500cebd5459250004ff7359250014fe7359250004fd7359250014fc7359250116bf4359250006bd4359250004ff725925000cfe7259250004fd725925000cfc7259250006be4259250116bc4259250004ff7159250034fc7159250116bf415925002cfe705925002cfc705925002ebe405925002ebc405925002ef7619865001cfe7498650004fd7498650034fc7498650034ff7398650014fe7398650004fd7398650034fc7398650034ff729865000cfe7298650004fd7298650034fc7298650036f651986500b6f5519865002cfe709865002cfc709865002ef6109865002ef4109865002ef46158650004ff745865001cfe745865001cfc7458650004ff7358650014fe7358650004fd7358650014fc73586500867f53586500067d5358650004ff725865000cfe7258650004fd725865000cfc7258650086f65158650086f551586500867c515865002cfc70586500867f505865002ef6105865002ef410586502057f73946502057d73946501fe7f62946501fe7d62946500257e71946500277671946500077661946500067d61946500077561946500077a70946500057d70946500077970946500267e60946500277a6094650034ff769065002cfe7690650004fd7690650004ff7650650004fd765065002cfc76506500057f75506500257c755065001ebe6450650006bd645065001cfe76d91500febe64d915001cfc75d91500febe54d91500e6bd54d9150004ff73d9150014fe73d9150004fd73d9150014fc73d9150006be43d91500febc43d9150004ff72d915000cfe72d9150004fd72d915000cfc72d91500febf42d9150006bd42d9150034fe71d9150004fd71d91500febc41d9150024fd70d91500febf40d91500febc6459150005f77159150005f471591501f5fb705915001cfe74d8550004fd74d855001cfc74d8550004ff73d8550
  | 10 => 0x815101cfe7418151004fd741815102cfc741815102cff7318151014fe7318151004fd731815102cfc73181510567f53181510067d531815102cff721815100cfe721815102eee721815100cee7218151004fd721815102eed7218151004ed721815102cfc72181510067e51181510567c511815102e7f501815102efa5018151056f95018151006fb401815102ef8401815102efa3018151006f93018151006fb201815102ef8201815115cfd75d9641036bd74d9641034ff73d9641014fe73d9641004fd73d9641034fc73d9641034ff72d964100cfe72d9641004fd72d9641034fc72d9641034fe71d9641036f671d964102cfe70d9641004fd70d9641024ff76596410367c65596410367f755964115e7f545964115e7d5459641004ff7359641014fe7359641004fd7359641014fc73596411467f53596410067d5359641004ff725964100cfe7259641004fd725964100cfc72596410067e52596411467c5259641034fe7159641034fc71596410367e51596410367c5159641004ff705964102cfc70596411467f5059641224ff765464115fb74154641036fb6098241024fe7598241004fd759824102cfc759824102cff7398241014fe7398241004fd739824102cfc739824102cff729824100cfe7298241004fd729824102cfc7298241034fe719824102efa4098241096f94098241036fb109824102ef81098241036f86058241004ff7558241024fe7558241024fc7558241004ff7358241014fe7358241004fd7358241014fc735824107ebf4358241006bd4358241004ff725824100cfe7258241004fd725824100cfc7258241034fc715824107ebf415824107efa405824107ebc4058241036fb1058241036f81058241024fe76d954112e7e65d9541034ff74d9541174fd74d95411767f54d95411767d54d9541004ff73d9541014fe73d9541004fd73d9541014fc73d95410067e53d954112e7c53d9541004ff72d954100cfe72d9541004fd72d954100cfc72d954112e7f52d95410067d52d954101cfd71d954112e7f51d954102cfe70d9541004fd70d954112e7c50d954112e7c6559541225f77159541005fb7059541005f87059541174ff75595410067f755954115cff7459541006bf7459541004ff7359541014fe7359541004fd7359541014fc7359541004ff725954100cfe7259541004fd725954100cfc7259541224ff7159541006f77159541004ff7059541006fb7059541004fb705954102cfc7059541006f87059541004f8705954121cfe769454112f775194541037b44194541024ff765454101cfe765454115cfd765454101cfc76545410067f65545410267c6554541005bf745454101dbc745454115fb44154541216bf6390541216bd6390541035bf729054120dbd7290541035be7190541037b67190541036b
  | 11 => 0x5fb7058554005f87058554006f5611855401cfd7518554024fd7418554034ff7318554014fe7318554004fd7318554034fc7318554034ff721855400cfe7218554004fd7218554034fc7218554036f6511855424ef55118554036f6411855421ef5411855402cfe7018554004fd701855401cfd75d8154024fd74d8154004ff73d8154014fe73d8154004fd73d8154014fc73d8154004ff72d815400cfe72d8154004fd72d815400cfc72d8154034fe71d8154004fd71d81541f6fa50d81541befa40d8154006fb6098154005f77158154005f47158154006f9601815401cfd7518154024fd741815402cff7318154014fe7318154004fd731815402cfc731815402cff721815400cfe7218154004fd721815402cfc7218154034fe7118154004fd711815402efa5018154246f9501815402efa40181541a6f9401815401cff7659251036bc6459251176be545925112ebd5459251004ff7359251014fe7359251004fd7359251014fc7359251006be4359251176bc4359251004ff725925100cfe7259251004fd725925100cfc7259251176bf4259251006bd4259251034fe7159251034fc7159251036be4159251036bc4159251004ff705925102cfc7059251176bf4059251036fb609825101cfe7498251004fd749825102cfc749825102cff7398251014fe7398251004fd739825102cfc739825102cff729825100cfe7298251004fd729825102cfc7298251034fe719825102efa509825109ef95098251036fb109825102ef81098251036f86058251004ff745825101cfe745825101cfc7458251004ff7358251014fe7358251004fd7358251014fc7358251004ff725825100cfe7258251004fd725825100cfc72582510867f52582510067d5258251034fc71582510867f5158251086fa50582510867c5058251036fb1058251036f8105825101cfe76d915115ebe64d915115ebe54d9151146bd54d9151004ff73d9151014fe73d9151004fd73d9151014fc73d915115ebf43d9151006bd43d9151004ff72d915100cfe72d9151004fd72d915100cfc72d9151006be42d915115ebc42d9151024fd71d915115ebf41d915102cfe70d9151004fd70d915115ebc40d915115ebc645915123df77159151005fb7059151005f870591510357f73945512357d739455122e7f629455122e7d62945510357e71945510377671945510367f61945510277761945510057d709455101cfe74d8151004fd74d815101cfc74d8151004ff73d8151014fe73d8151004fd73d8151014fc73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d81510b6fa50d8151006fb40d8151006f840d8151006fa30d8151006f930d8151006fb20d8151006f820d8151006fb6098151005bf745815115dbc745815114dee7218151005ed7218151006f9601
  | 12 => 0x1b00700200000100300100100200700300000005500400101000e00a00201800500000600300d00200d00000500700100100000200000001900000900503500000400104500100800000200d00001000200000500000100b02200000000700300000e01e00400900200500500600000400001300200000203f00b00800100500100e00400000400000600800100300800000000001001e00002d00903300000500000000002e00100000500e00000000400000f00000300f01400700200000200000b00100300700102000b00000900600100000200400700000100300a00500000300901800000101900b00000000c00f00200500400100300900900b00100204c00000000100300200000d00500400200304400500001601000000000200200503401600200300100200a00000100001700000000100100000000800000700b00e00200500800200100000000200400000200200000000000500100000700001300000300300000000001400000e00900200500000000000700400400a00100000500800a00200500100a00400000300100100101c00400600400100101501a00100000302a00301f00100b00000000900100500502d00000200000202500702100400600101200300000d00600300102200200300100200400000200000800000100600500101500400000000100000400000000001401400d00600e00300400000501300200105e01500c00703300200000602700000100002200000103201500200200a00200300000a00700c00000400600401102200100200400200500000600300000000b00000003600000000900200500300d00c01700804000500500600000a00c00300000000100300e00000200200200000900000402400001000000300700700900300002a01d00101700000600300000001c00900601302800700900200400000400b00300100000300500102600100000200400300400102a00002000200600300e00100800100000000100c00000200400200101600100400e00700f00a00001000300f00402c04d00000100100600300000000d05800000200200a00200c00000101700800200401300502a00d00100000000c00200200801e00400000201900200000e00200000200000c00900001800000900000601201e00000900000000a00002300600000d04200100100200400100200400100400001600000a01c00001b00000000700000201a00000600c00000100200000300500600000000600500200000600001700d00100000000100200000800000000200b00200200601cfd75d8554024fd74d8554004ff73d8554014fe73d8554004fd73d8554014fc73d8554004ff72d855400cfe72d8554004fd72d855400cfc72d855423ef651d8554226f641d855402cfe70d8554004fd70d8554006f76198554
  | 13 => 0xbf8f24000000000037886600000017a4000000000000006a0002f28020f9e4b03cd800000000000008cc0001fe0000000000000178991800026f1aa809000071b28f95cc90817510f9b5cbcc47e2e880000005f23588000a900002a703dc02658600001e0000000022000000033a0001b9400018621b00000005ec0000f60000000000000000029a0001c0c020000000000091a00000018c01520000001f640000001a300dc0f843a035091854840f07e06646ce000000108417a0002bc8e8c00000000013300000001fa9f7ca5c2fd07a074c1984cb12916b821637d34091dcc9819e0000b2800021700000005d257c2de02c04f840d000000000026b19f80000000dc0059074c903960f117f4fb82b71c89a1c3b60003de83f40124f33d69fc46945333fd08a07663be2309d0c1a03362e48b745581f61708ff07c81a919480585007ea1ff9b9c2322d613e9088afa44b08813440867861b302c81923d31898230eec0aa08b1face2c3622d60fe4d464970000000dea2023871d6ca9821e03a000067c63115f991c00006f28417a8be60000c51e005020000ab00008982cd307177c0003c53419d20e6838c2000000dfa000000182c68400436f00000002b100000000002de000000042200017d8bc00620002b2800077a1c800007ac8e44492a78f941b653b2681ab465851835f80b002433d006040c234180000007000000003a98d8acc1cf2f09f90a4252937e1224b344763210c705b05a114f8c00ec65ff00000000005a33de0000dee4191020d7c00000000000000001283f295e0e160360001e84230000000056cb3c000403000086a0000d1000038e10f3ed80d0fd26ef3a787bcf5e31b3bc8dacbba4ca0568000c460e33b204c0e5e63e06a9fb000000000000004c00ac00003d80e41823981bd000074900005d07d00701688ea84b87a32528ff400069000002dc5f400000000004980ba0001e300000000a5800000048200019541e01c92a380542100003c8201c00000000012a400002f3918000a702610000d704142b314d8ae005a3ae2c793f0d761f93080e640001fb0bf8000f385690001da8cba000041022807073d020905c7882162340000b8403c14593108704730ce98807244b900009102cc415000000087800015a00005386eb0a00b202286352550000f443ca23a0ae47060d931d800003438a0019e143e429100016240000000001590f88000000000000000000001cc0002b0000000043865e00000000aa1e939080009020fe0000000eda30e0211a589c000019384d810800400503a00600000900600500401c00000000300000600100300700500000200800200400800000300400000000200000600601400200500500000000000000000000200900000100a0020230180000010000030000040090370040130040010
  | 14 => 0x6e42f635e88dc80c06131f9ef8baa53c05e10b4aa648a06e88600a267d1f08fb483805c208847413e63d3d98824f9668234a05c077800038012fc6146e93440000c663ab0000f6500a61d00000001a47392f41360b060da17c0000fc46fe00b8a5c9ec2c31490b9823643f07c1d980ae20e1ea06c0ab82883120d740007e70001970cf44c90ad1efc0000000c616586e275c0310000d4a23f2370f002860c133100008542552ac9e4c69a0cb19113680005c63061f78f700003ba1a5c22a28d000159ce1e1552a91fc09ca00029e80006a40003c200002c00000a31dc800069e2560d30a287f8147183c5f845a1151660000543036898c00066634e88bc34a5273e286ac00012c32f89d4b383190989e340be45400a09e0ac466920d02d011c17c02e936cfdc1173a6172c50814c1e88d2c6b25f43ca800018e26c0000bd0000187000000000000038b800000000000017dc4ca0cf1bc0000e8856f0ac88ece4c77834a800027064d13c8000fa0000000084c00000032790c85c00001c992305541952fd00007500002dc00180000000d39d2c91e20d0eb12c40ee09039c0c486b000000011980002cb00007cc09c5a014996903c21ed1dd9f340000000001abc76e4d60000e740007500248000fda7c322b1d58e3a31e0b180000000000001d846a877735a8e40d9050226003c4dbe32a0c486e8bce2dc37d928497a77a0301878d962bc14b1d4417259b0dc1eac8ea62211106d8eca6ec1778ed029e20f116173844c46f050185c8e27542250a2858e64333f124420057b270813c8022fe00000006d20112e09a10c5014d00010290187ef28a8d20de415e00017140007b00001e94fee67233c1ec8000000000130c2da69100015f800000000016c400000000016489280000000190e2221b30980000000000000000ca46d13770eb060c0f50001dbc00072a00013b4d0a64e3b4911864c06b361155846a000026000000000000000008fa0660bc894c0947d80001b2800000000016cc00000032b1e643226630000000d3055b01d1e2025655738c05a05c61b91139448e285d028e943c54a3f633a04480001620001f0400049e1ce1c3466e36f089800029055036705f40ca2a900000001d600000000000001810000000a080002f68db0628000036000000000005102540003a2167873095e2ea0000c24978000176000003665411e10f8cdc3492979f686ca0002fd8b5cb94000000128000014100f9c1c84033827e97780001644068934a9431d00000004bc6d50000134b8e000000027865c00000003a8c4c4280a29d780002691a21490a645b400001a43200970001674c220000bd94040ec0000000000000000000019c8463df000110cece0002dd8f6c32c760000130804611c39d9adc00033319d8e9c00063a000199047a5aa000003473c7f62
  | 15 => 0x65026048648b2c50da8e4a16f12e981cf3039f18b16f83080a704a13b06802152638d044602833b89ea0b284e400709b43fe4ff0749b903aa02133a8748d9e0880d7981071e6ba06c1fd0db82be0da9be495a4eb2b00e1824815c0979d38aa820504586f021a7401f4809c9320c638e0300e1274501918646f62993be1a4800000000003b401e1270f28a98af42ab000060ceb2729000000000050300000006c000000012383b258d00000007160000001fd4a9647b0000000a6e0003988000e3205a00000007ac65101999c000068e2071b00b4e6b30d50dd89cc3fa0f5178c00000011f000000070c0d2000000000009e12980000b3000000000000023d0bc80007ba150976d0060e83f91f1c62e4ce05415a0ab40002881d189242d40001e08a3c7940fe8ce4a1a17a2c8091c4c82121d900a80006ac03886b074c3e61c29b6435c6f10c9951438279f18596f4e4000000012d8e4843024d82d4dfe0bf3f0a020a4450c3ff110497427e0f20d3cfa25bf262800041880b117070c85650904184848bc1880cc0d44944091212054cc0471e1fd80b8e2043b208185040c0a40001aa05ca7d5000000055c000000000000000000005a800028215d800000012a0000000e0c000000095042847c22b8a78a742b62b593c06023dd05c090831613a29595b48c65410001e3cea66b43a099281f460010e938c55e520050906c4464d73970cc03a234e3ba8488bf21c2000000049412e27c8f040006d60000dd07ce1010011a6cf842da3051a9c0007a40000e10aaa6611690000ce60002d306cc2e400000004fc0c66e227409c42d822b08380000000ec06204286c867638207e80000000f80000432483000000000000016018200007f900001608d60000000000cb0722000047c0000000299b4cf2e3f82a49140ee65a22db9e3823c1d027b93c8e7800028d00000006090001a700900922c6035013200012b049415c7b700003982ce00018f901400000001f1cf8d6035b3bf8a242723c30001a3c00016100000000001a329805407400000001e0400009d00018b400044716203941ae0590001ed0a143ba04780004d43f7000000000000026913b8d780000b59f3840633c266995c4001f11a80fbce3e7e83c482f8c063c80b4821880e38e000151849e7fb31e1ff41ac00019182340006be324882cda43070f70bd42841be12481f4c580931191d1c26866d15a80008f073f13b0a744e01203558de457438d1ea80000ac62b34514fc5fe0d138401509900814048548de666f1d80f3477e4581e60df84104550eb8000d987aa3940000d9246520107b077070534d08a429c00012f9aa48b25ba22887702e60523d3105901c6861c0974800a79600000004960003d0192c1ce4d40d318b89d461834c9f50b044642291ae4a1605024a9b18b6a1e01d78320
  | 16 => 0x400045f333928c0006593cd1b5000000000000605827e6000000000013500000005ee4850778c903a84df00000000000000001c48d4c2940ab9b80b0070a405189422244d10d0b6cd486c71979ac8a0a00012c0000a1c2cc3d6021c0000000000528f8000027a9768862320000127cf8c4f4150146c5aa1760000000edc0003c180006e60000448894a545b914a9df800055d0000000b603d725993788b840335108d85a046c0e298e00000191bd0ac800002600000002f032b31a133c0000000000334830000000144c8800002c20e248fe00008200003b031813b964c000000000000061a0000f400001c000000000000002241569188bb23563e60000000000260907800062f09d896c00000013902148e077d00000002ca53900000000000000000000000000000000000000000019ac00018f2d900009761c40bb9fcc6c23b1147811c0000000710000ae22a7402000020c56327486509646652fc0000000132328000000065302594b000063700015c8d8a5f02ea0aa06224ab263000085e1cb3e51d5c5da22d04e0000ac200000019ec25257600018344f47e037696d8c521c624e00006101092e980003942eb0b892dc14617e00000008261fc188196cbde6cd0000f1cae01c000003c8d1873323482ac9344b52eb94b40000003a69bc00003940001a2459c6b81ef00000000001dc95604623ce2ca8000d4242627386c4c4209a33e09884a25a912d0c08e261f4373030848a1b22f0001cc0c00036208e000037715e8b4cf760fb096946461e7ff2d6830c5f20002c4103000000000003fc74200000006fcd163ec0000d8c00025936804f40f661a1330ff80445dc36d80000000000000cb4e042c22ec16040d068d11088049f600000012d00000002e600007300002a88074cd80000000000000000000000092c4080000638ce233428e14f81e60000000000a500000fc1354e6446a00000000000002af1f4c4d000019090b8e6a6681ee00a06f84603fe17d80001372c395dc6dc4121ad18705440003e40e6c0004040ed081cb326ae2e200000004533af800004a6fa1cb8000a2e0001f9922000024100015345d060132d17200000001201ed8bea467000054412c15d12707dc0000002148000b560003350920b1c6792ba800054656a38a8b9cdb02d92431c9c7e20002888000dc26770001e1c2926c33200e20ee07d209318546da1540db8a6014a4340000f6850a6aa25c00805be79d39d1cdc3760003f180007c02e41280cc803c19225700003ce00039696a086e4482210fb8c4e76c1a39d889de67f164902474a3a430d80acbf872c1e7800000009b0d686f4d8241f00511748724791af048cb2e4dc0d09700f4e6da0c68fc09f03c21f58e0816c23932082ec4fe6a003d1910ad86392d78114b0a16e29a93f80b63c6278921c6504d3
  | 17 => 0x66c8b66053eb800076c44e0000000d000e40cd000000078a28b15d07c47362b70000b8659f13380c0ed631a1da94d80006930e70000b9e00029180005c406e00001fca68000205a0082042863190384cc04d91e914980005251371f5800000000000000005070f18000000000000141872a00035b14c4a880df1a183b819c03f3150560b9a0001c01bd83ea00001e991450e03b1f515008280001a99200d3e4a80000000b160000001ed40000002f580000005e2000057c00043d24c07790025ee3d8873400030430b00006e04450d40000f2430300000004ae5910699be0dd008000006700002731fa1d6015e185280011821c5fe1828a40ea47dd3a5065c8883150000eb4e343cb0a21dec58c75d0000cd47e4001252029889e42c271051c70e07e1798da0bc835707c84cc0720293719e783cc4252af9ea434049d3aa89d021819f1928bb8f5c34508286d027c5422539e2c6ea4fa03c92f84202201f18c30f227b926e8f400806123750178e020001628dfc0001df000109d0000b10629cac9260003ad00000000003a117c48da23a2480e686625d63b408d05186dd30f9f243ba27b2d28ea
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xab581949640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400d56d02192c808002ad604325901002d5d40064b202000ab9800c9640400dc6ca3a8ac8080262fa1f31590100045ec3e62b202000a3e85c85640400147b0b90ac8080178e94350590100051f42e60b202000a3d85cc1640401317d0f902c8080022f61f205901002c3e42eecaa020058bc84dd9540400d1e902bb2a8080163e201765501002c3e43acaaa020058bc8759154040018eacbb8aa8080032d59371550100063cb2ee0aa02000cb964dc1540400bcae20b2ac608017954416558c1002f4d082c8b182006e991059163040018beeb3aac608136b5e057558c100356a40aeab18204cadb805d1630400b5b100ba2c60800387d525458c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c100356b408e4b182008ad5811c9630400b5b500392c608022b66007258c100356b40ca4b182000ad581949630400b5b501212c608002b66024258c100372b28ea2b182000a5e85c8563040014bb0b90ac608017969435058c100054f42640b182000a9d84c81630400bcd420b2ac40801b9a441655881002f53882c8b102005ea510591620400bd8e20b1ac408017b2841635881002f62882c6b102006ec91058d62040975d700baac408016ba201755881025573c0ae8b102006ae4815d16204001c5ea92a2c4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac40801ab9a04735881003d72c08e6b102005aea801cd620400f5d30039ac40800393d4e535881002d75404a6b102000ae98094d620400d5cd0321ac408002b960643588100373328ea2b102000aae84cc5620400155b0998ac4080179a94350588100053742e60b102000a6d85cc1620400dc6882b2a820801aad20564504100375220ac4a082005e3840595400400b57100b228008017a610163500100243e42eec88020038bc84dd910040210fb0dbaa20080030f99375440100062f31eea8802000c6e62dd510040010fd0eb2a200802a1f21d65440100061e3a2ca880200f8bd86dd1100400187ccbba220080030f59774440100064f31ee88802000cae62dd1100400117d0eb2220080262f21d64440100061fbaac88802000c3c7559110040018beeab1a2008003171d563440100064fba2c68802000c9c7458d10040018deeab1220080031b1d5624401000657ba2c48802000cac7458910040018ef0bbb220080031d21776440100065bc26ec8802000cb484dd910040018eeedbaa20080031ddd875440100065bbb6e88802000cb7761d11004001a68ea3a220080031ee1776440100063c42eec8802000cbb84dd9100400197109bb220080031eddb75440100063dbb0ea8802000cbb76dd11004001976ec3a220080034e1d47444010
  | 1 => 0xd0e32ac8880121fa1f75591100061fbaee8b222000c3c75dd164440010ff0ab9ac8880121f21573591100045fc22e6b2220008ef825cd64440031d904b9ac8880023ee0173591100043fc2ae4b22200487c855c9644400117f08b92c88800237e0d72591100146e41ae4b2220008f7815c964440018e8ebb8ac8880031e1d770591100061f3b6ca32220008bd87994644400147d0b328c8880022fe1d65191100051f430ca3222000c3e76194644400117b0f318c8880028fa1663191100051ec2cc63222000ab58198c644400117f0eb18c8880028fe1563191100051e42ac63222000aaf8258c644400155904b18c888002aee0163191100045ec3cc43222000a3e85988644400147b0b310c888002ae60262191100045fc3ac43222000a3f8558864440014790ab10c888002a7e0d62191100054e41ac43222000ab78158864440010ff0abb2a8880022fe1176551100047bc0aecaa220008fb805d954440070fd0fb2aa8880122fa1f64551100063db2ee0a8a2000cb864dc151440018f6ca382a2880032e19070545100063c32ee0a0a2000c78651c14144001976c838282880031dd9771541100065a326e2a822000c77651c55044001968c838aa0880163da1b71501100063a32ee2a022000c74651c5404400196ec838a80880038e19464c41100863b3b6cb0822004c7676196104401f96cedb24208800f2d9d864841100071a328c9082200587e87951650400187ee92a2ca0801a3d205735941002c3f43ca6b282000c5f7394d650400b0f90ea9aca080163e201725941002c3f43ca4b28200587c87549650400187ee93a2ca0801a9d205745941002d3c402e8b282000c5f739cd650400b4f50139aca080029e60273594100053bc0ae6b282006a74815cd650400d4ed0321aca080029d60643594100353b40ce4b282000a75819c965040014f700b92ca080169e201725941002d3d40484b282000a798090965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c9650400d4ed02192ca080029d604325941002d3d40064b282000a79800c9650400147d0998aca080028f61331594100543f43e42b28200087d87c8565040150fd0f982ca080021f61f30594100051f42640b282000a3d84c81650400b17d0faa2c8080030fdd7545901002c7c402e6b2020058be8790d640400b1790ea1ac80801a3d205725901002c5f43c84b2020058bc87509640400bc6e20b2ac8080178e841655901002f1a882cab202006e3910595640400187eeb3aac80801aad205755901002d5c402eab202006ab6819cd640400156b0339ac808002aee01735901002d5c402e6b202000e1f5394d640400b5750129ac808002ae602535901002d5d404e4b202000ab9809c9640400156f02b92c80801aad20572590100355b40ca4b202000
  | 2 => 0xd525961000c5fc3a85b2420058bc8750d64840010ff0ab92c9080121f21572592100046fc1ae4b2420028dc835c9648400b970e0b2283080030f5d254d95100062eb9ca7b2a200287f8754f65440030ff0ea96ca880028fa1263d95100051ec24c7b2a2000a3f8458f654400147908b1eca880029be0963d951000536412c7b2a2000a3e8498b654400147b09316ca880028fe1162d95100051e422c5b2a2000a5f8358b65440014b906b16ca880030f5d074d95100062eb98e7b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000a76810cb65440014eb02196ca880029ea0032d95100053cc0065b2a2000a6e8210765440014db0420eca880028fa1331d95100051ec2663b2a200087e870c765440210fb0e18eca880021fa1f21d95100043ec3e43b2a2000a3e84087654400147b0810eca8800297a0c40d95100052ec1881b2a200087e87cc365440010fb0f986ca880028fa1030d95100051ec2061b2a2000a3e84c83654400147b09906ca880021fa1c20d95100843ec3841b2a2000c3c65dd1654400717d0fba2ca880030fdd774595100061fba8e8b2a200087f855cd654400117f08b9aca8800e2f211735951000477c12e6b2a20018ec825cd65440011ef02b9aca880021fe1572595100045fc22e4b2a20038bc845c965440011bf06b92ca8800a3720d72595100047dc02e4b2a2000cb474dc56544001970e9b82ca880021f61e63195100051f424c632a2000a3d8498c65440014f301318ca880021fe1d63195100051fc22c632a2000a3c8458c65440014df04b18ca880029b20963195100053bc0ac632a200087d87988654400147d09310ca880028f61262195100053ac0cc432a200087f87588654400147f08b10ca880028f21162195100052fc1ac432a2000a5c8358865440014f700b10ca880030f5d754d91100145fc3a87b2220018bf8750b644400147d0b31ec8880028f61663d91100051fc2ac7b222000a3c8558f644400155f04b1ec888002ab20963d91100051f42cc5b222000a3d8598b644400147f0ab16c8880028f21562d91100054fc1ac5b222000a9c8358b644400187aea3aec88800387d4e53d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100055b40865b222000ab5810cb644400157500196c888002ae60032d91100054f418a3b222000a9d83147644400117d0f98ec8880022f61f31d91100051f42863b222000a3d850c7644400147d0b90ec8880028f61721d91100045f43843b22200f8bd87087644400155d04286c888002ab60850d91100051f42e61b222000a3d85cc3644400117d0e186c88803e2f61c30d91100045f43e41b2220008bd87c83644400147d0a106c8880028f61420d91100061e326eab22200087e87d9564440010f
  | 3 => 0x6b2a82008ef825cd65504031d904b9acaa08023ee01735954102c7c402e6b2a82008bf845c965504011bf06b92caa080a3720d72595410047dc02e4b2a82058f8805c965504018f6ea382caa08032edd0705954100679b88e0b2a8200c3f65dd151504015d304286c0a08029ea1730d81410055cc2061b0282018fb8748360504011f70eb00c0a08029e21560181410064fa12e63028200c9c415cc605040b9b100b98c0a081727d01731814102e4ea02e63028205cda205cc605040193ae6a10c0a080e2f61e41181410064eb9c823028200ab98090460504014f50b980c0a0803365cf30181410066cb9a4030282058bc8750d64940011df04b9ac3280063b209735865009c3fc3ac328ca01687f865c2519400187eeab22832801aad205645065000c5fc3a85b22a000cb4641c564540015cb0420ec2a8002ada1331d85500053ac2863b0aa0018f78748761540011ef0eb08c2a8002ad21161185500062fa92e630aa006cd4815cc615400d8bea2b98c2a801b1754573185500366b10ae630aa000c5c505cc61540018bae6a90c2a8002ada1331185500066ab9e6230aa000cd573484615400187aebb2482a80121f61c61941500052ec18c3282a000c7571186505400b0fd0f29acb2000317dce535964002c3e43aa4b2c80008df835c961900051b906b92c3200030f59774546400945fc3ac320c80158bf865c241900050ff0ea9ecaa00162f61372d954000636b94a5b2a8000c74651c5655000117f08b9acaa00023be09735954000c76412e6b2a80008f7815cd655000d1e902b9acaa00021fe1572595400046fc1ae4b2a80028dc835c965500011ef02b92caa001a3d20572595400063bba8e2b2a8000cb7741c565500019e0e3b82caa0002b560c51d85400147bc3a63b0a8000a7685c87615000156b0810ec2a00023de1d61185400053a42ac230a8000caf435c8615000195a86b90c2a001b39205721854003657a0ae430a8006cad415c8615000d9cc62b90c2a00032b101721854000672b926230a8000a7685c8461500019cae5908c2a00030fd95749454002cdc402e928a8015ab687185415000d96d0e30a82a00032ddcc61505400065ab98c2a0a8006ea682185415000dd4b0430a82a004a6ea18705054002e5d430e0a0a8005d9a831c1415000bb330638282a00032ed8870505400065cb10e0a0a8000c3f65dd1505000717b0e30c80a0002ab60861901400065ab88c3202800187f8754b65c400d0f90ea9acb880022fe11725971001c5e422e4b2e20008df835c965c40051b906b92cb8800a2fe1d43d93100043fc2ae6b26200487c855cd64c40011df04b9ac9880063b20973593100345e43a84b262006cb47159140c40050ff0ea9ecb080022fe11735961001c5e422e6b2c20008ef825cd65840031d904b9acb080161f21
  | 4 => 0x971d3000910c39dd0ce2bcb216732a44d0f1c21ba0008f8fe0301388c03b2605883d01302a8100384f3dc2b0539cf2f2848799171d02d04b24805c3506821f2a46a49498f0c046c3305f268484821283f603c828b50aa1f000090350000d68b2042220f38652482d8b58000004652093c00052cfe86a0a0838ef00c38a818c502426e000000003746200013b2d4000f82340128e4090c41f851480808344758148003267aca11121c86acfb82a1442a4360970000704c83800080485800290000582260da7e82600437e5682387e33a649239c33466105f1be4126b91e9ed2702440115840a06c5c8f50006f4760003b4820a603507a5cc6484532e3c8398570008a4959ef000500000000005442d1110000003a80010a6506622a000000000a00007e0c70d80004280021d200000000000000000022d0000000018c000328000003b80749f8711340000020b196571110803a07447e8012ba000b48003e26687680041e254989fc18c900c48d208c6ecba2100f23c074a140964808d07f1f6334a21e346a1848391e13c4744199f218584269360d63852621b34e0889c83f3961448b20d0a82e859a1511a6e03b97c18428ce3805066124e310830c3e0ba882080051248d52ca1bc550de0001a48a9c40a468400000368864f49d42da89c1f0313a448c002201707cc99000078000001430005f8000080400e0084c00004000000982c0780201804088660a80a0280a050160300000006000000200604034008180080e0280008800028101b00201004000000200e0000003806058020700600806000080302e05086000020680200000028000080e0400c0100e038160387202042100060283c12008088080a80204800028020101200006008181d00200004038000080802014010020104603026008021e02808804058140606e0c0040a01a03838000120302c040040984c028020080a1089e0580403800110020202c0001a0200201800020020000c0001205006280080f000028a80402c0f80a138100a800008080206e008020e8023de1d611855400578402c230aa8008fb8758060550015e102b00c0aa01a2f21d42592510046fc1ae4b04a2028dc835c9609440517f0ea1ec8a88032e19070591510056cc1881b02a2028fb874c3605440157509906c0a88029e61420d81510047dc3ac0302a200ab88458060544018dea6b90c0a88031b54d72181510063628ae4302a205ce8805c8605440b8dea0b90c0a88171b541721815102e75182e4302a20487d8794460544018dae5288c0a88029e602511815100674b9260302a200aba84c8060544019d2e5900c0a881a1f21d53596410343f43ca4b2c8200c6f7294965904011df04b9ac1208063b20973582410345ec26e7b2a8200c5d7394f65504030ff0ea96caa08031e19470595410043fc2ae
  | 5 => 0xd296f2282ac0823011631491000430000000eb1c061400150000000cb21313043ca388e3588c8001770d0408000c111e31c001e23aa4a82b08c27c844929541083b8d504436c4402c8412ac38c1302817a5c40f1e129c4cd1297035e0187501902e40c000003b24240000014a6d4c88860228f84e1df3b01880d1823ea92d001531908a0568030846e4e090d2923d0979b027493816a360f61e07294f2cc660001e517681c8e24f4a07e4a52021805e01b8f742e890939ca49a2980680b05e56c710942ae248b40001f26c8779990fa53424000478058000ff0008b8730a80e0731160933fc7390b2433c08ec6180033c828bb09d316000db84345e75c158532aa8e09e8fa3e818c190ce34c2fc000cf2f69147897a41827cf21600608c4449260b8370d998d2be5b84da3f30002896839434190bf820258518001db46e00000000000000000364840000002c3926400022b00039d19a3a162000000272bc7c8cd800000000000b71420000005b04a7a81a0000001b8001720e80e8b18d61026906b80000036cf401f21c1600004a0000008300e340228000df000928001e60000010e1c80ec504001c00461c86880040634cd89832d888cfb0ae1b47b0000000ba9185e0f63783645217d00000000000338735108870bc564ff80026a604
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8006420ea00c00050051364c515c8605440146990145721815100523648415cc605040149990105731814100513648505cc61540014559114173185500052364c405c861500014a5911017218540
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x2
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x124b
  | 12 => 0x138b
  | 13 => 0x94b
  | 14 => 0x94c
  | 15 => 0x94d
  | 16 => 0x94e
  | 17 => 0x124c
  | 18 => 0x124d
  | 19 => 0x124e
  | 20 => 0x138c
  | 21 => 0x138d
  | 22 => 0x138e
  | 23 => 0xa0b
  | 24 => 0xa0c
  | 25 => 0xa0e
  | 26 => 0x130b
  | 27 => 0x130c
  | 28 => 0x130e
  | 29 => 0xa4b
  | 30 => 0xa4c
  | 31 => 0xa4d
  | 32 => 0x134b
  | 33 => 0x134c
  | 34 => 0x134d
  | 35 => 0xb8b
  | 36 => 0xb8c
  | 37 => 0xb8e
  | 38 => 0x148b
  | 39 => 0x148c
  | 40 => 0x148e
  | 41 => 0xbcb
  | 42 => 0xbcc
  | 43 => 0xbcd
  | 44 => 0x14cb
  | 45 => 0x14cc
  | 46 => 0x14cd
  | 47 => 0x104b
  | 48 => 0x104c
  | 49 => 0x94055
  | 50 => 0x130a13
  | 51 => 0xa1314
  | 52 => 0x14d
  | 53 => 0xb8a13
  | 54 => 0xa0b94
  | 55 => 0x198d
  | 56 => 0x131493
  | 57 => 0x149314
  | 58 => 0xa5353
  | 59 => 0x134a54
  | 60 => 0xa4bd3
  | 61 => 0xbca54
  | 62 => 0x180e
  | 63 => 0x14d353
  | 64 => 0x1354d4
  | 65 => 0xb9493
  | 66 => 0x148b94
  | 67 => 0x2cd
  | 68 => 0x19cd
  | 69 => 0x14cbd3
  | 70 => 0xbd4d4
  | 71 => 0x184e
  | 72 => 0x10e
  | 73 => 0x28e
  | 74 => 0x5853
  | 75 => 0x5993
  | 76 => 0x5814
  | 77 => 0x59d4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1195
  | 6 => 2063
  | 5 => 593
  | 4 => 8
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (48593+((h/398+packedAt gbK7 (44215+(h % 398)*11) 11) % 1735)*12) 12
  | 6 => packedAt gbK6 (107268+((h/687+packedAt gbK6 (99024+(h % 687)*12) 12) % 2723)*13) 13
  | 5 => packedAt gbK5 (36957+((h/197+packedAt gbK5 (34987+(h % 197)*10) 10) % 712)*11) 11
  | 4 => packedAt gbK4 (568+((h/2+packedAt gbK4 (560+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f07c07c07ffffc1f007ffff0cc74f8d23f33f
  | 1 => 0xfff8007fffc07ffe0007ffff333888fe3e3c3f
  | 2 => 0x83ffff8007ff83fffff83e00c3c0f0f3c3cfcc
  | 3 => 0x3fffffff80003ffffffc000fc00ff03fc0ff0
  | 4 => 0x3fffffffffffc0000000000ffff0003fff000
  | 5 => 0xfc0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2601c8148158c541905262aa0443438520d315
  | 1 => 0xc93804294a842ab200a495541118883a0e2c2a
  | 2 => 0x214a548044f520d52530380643c050d243454c
  | 3 => 0x4294a94f90084328cac70018bc00ad01b40ab0
  | 4 => 0x3e73e72e72e701083021060efad0003fbb000
  | 5 => 0x70003003003000210c042180faf6feec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37341
namespace PEqualNP.Outside.L_meta_37341
open PEqualNP.Outside.L_meta_37341.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
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
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 bs2_4_224))) (concat (concat (concat bs2_4_256 bs2_4_288) (concat bs2_4_320 bs2_4_352)) (concat (concat bs2_4_384 bs2_4_416) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
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
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 64 := (concat bs5_4_0 bs5_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 40 := (concat bs5_5_0 bs5_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 8 := bgb_4_0
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
theorem bgb_5_576 : Interval gbAtlas 5 576 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 593 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)))))
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
theorem bgb_6_2048 : Interval gbAtlas 6 2048 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2063 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))))))
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
theorem bgb_7_1184 : Interval gbAtlas 7 1184 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1195 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)))) (concat (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888feeefac8fca8f888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074632 * 2 ^ 32 + 4238932104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37341.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,5]⟩,⟨.or,[0,5]⟩,⟨.and,[1,7]⟩,⟨.and,[1,4]⟩,⟨.or,[0,9]⟩,⟨.and,[0,4]⟩,⟨.and,[6,10]⟩,⟨.or,[2,12]⟩,⟨.or,[3,11]⟩,⟨.or,[8,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4238932104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4238932104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37341

open PEqualNP.Outside.L_meta_37341 in
theorem PEqualNP.Outside.L_meta_37341 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4238932104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4238932104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
