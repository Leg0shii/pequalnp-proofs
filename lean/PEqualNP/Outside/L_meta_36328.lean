import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36328.Model
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


end PEqualNP.Outside.L_meta_36328.Model

namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
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

def SBf (j : Nat) : Nat := [6, 6, 7, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36328

namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x13320100100be40bc42df31be42bd41bf41dd31de30bc40dc30bf43bd43
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xb000972948155510c23aa6214b14941
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => 2*((h/11+packedAt s0K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s0K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36328
namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x31000110001dd43bd42bc40de31bf42de43be40dd32de30dc30dc31df32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcab28c6154514ca5aa4204755031
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
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s1K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s1K3 (108+(h % 8)*2) 2) % 4)
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
end PEqualNP.Outside.L_meta_36328
namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1050c108000030010400000b0051450021414c5145ff40fe31fe20fc42ff32fc31fd21fc10ff20fe21ff31ff43ff21dd30ff41de31fd10fe10fc21dc31fc43ff30fd40fd41fc41fd31fe30fd43fc32fd32fc30fe32fe40fd42fc20fe41df30fe43fd20fc40fe42ff10ff42fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x4002142200f811e0000e1a1101a640801704000090230b0204180000014a801200046024400100c8201ec982215c514c2d8a4885b54840aea80635e510c67ca9985794c30ae29a215d53902dea4884f55321bb28841ce520c6baa7105b54831ec984219e540c6dca421d754c42aea9e435d53842dca5985794c20aea84633c54482dca418cfd51209eaa0633e540ca7ca80857d4d109eaa4435c53507b6a0985bd4940bd280635e518c67aa99857d4d41b7294835e5310abaa6207354b309eaa0655f53c42d8a4a05b94b419f2a0635e53c873aa818d654031ed280633e54886bca6205754e309f2a0416d52cc2f2a018d794e10b6a90879e54cc2daa5a0d794e20aea9e835d53082daa520d794730ae29a435f53486eaa2105b548109faa2213d54082bca7204f95321af29e83ce52cc2dca4087354831b7290819d54cc35a84215714f10eca80637651103aca218cf15110baa88813d54042baa6085794c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x5028100c355152cc3495254031c354d4210a58654c110c3551520c71a5454031d2949500c7195454031
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s2K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s2K4 (2484+(h % 51)*7) 7) % 92)
  | 3 => 2*((h/9+packedAt s2K3 (304+(h % 9)*3) 3) % 8)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc7ffff83fe1fff07f0fe1fffc3f81ffe98f39f
  | 1 => 0xf81f0ffc3fff0ff87f0fe1c1fc3ffc1f674cf3
  | 3 => 0xffe00fffc01ff1ff800ffe01ffc01fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffe001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40840088002200009010024480488488081185
  | 1 => 0x82421110940810282106208844124854234432
  | 3 => 0x114aaa218d54835b088b54116a815345858e18
  | 4 => 0x3594cc4a2906a595daa11025b3258189d80bc0
  | 5 => 0x261888733198c9e66ccd993822060211f6e000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36328
namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xc008048000000000000200000200f0400400420030430c0000fc30fc10fc20fc31ff40fc41fe40fe30fd43fc42ff42fc32fc21fd10bf41bc40fe43fe32fd31ff43fe41ff20fd42ff31ff21ff10bd41ff32fe31ff41fc40fd30fc43fd32fe10fe20fe42be40ff30fe21fd40fd41fd20fd21
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x9062408000083810404c81007c00002003880a08192000010004000497a04307000008000180000a80c00000c00104001aa020c08d1000200af29e413e540cabaa6215b94a309faa4216c524427ca820cf152109e2a2619d53d067ea8905b94843af29c416d5210ef2a010d794c429eaa0653e54c42d8a498cf54440baa88815e5310278a0a0dd94440af29821b5511027ca9985754c21b7a92216d520c6daa4204f940409faa2619e531036ca2205b54b41cf29e837a500c6baa7905e94021afa9a436e520c76ea2a0eb54840b7290216d52042baa6205b54b30b7a92635d538827aa3204f950109f2a4635d53d075ca5a0db54a30cea98813d54886b8a690db94b41dd280813e509027aa8084f151109aa8881b5414427aa9904f550319eaa66179500c6bea688734c8329f286833d54c427ca910cf550219eaa4635d530427ca810d794f41d7290813c544836a83884f95031d6a96836e52cc2b8a6885b948409eaa4835e530867ea8884f95320
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x6d001c554d51102346550510c9949511030d544c832c9549511030d5354b41c354d52103165354440
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/35+packedAt s3K5 (704+(h % 35)*6) 6) % 44)
  | 4 => 2*((h/65+packedAt s3K4 (2484+(h % 65)*7) 7) % 92)
  | 3 => 2*((h/9+packedAt s3K3 (304+(h % 9)*3) 3) % 8)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc3ffff81fe1f0f0ff0fe1fffe1fc1c1e99f793
  | 1 => 0xfc1f0ffe3ffffff07f0fe1c0fe1fffff6648ff
  | 2 => 0xffe00fffc01ff1ff800ffe00ffe01fe1878f1c
  | 4 => 0xfffffe001fffff00000ffffe001f80fe0
  | 5 => 0xfffff000000001ffffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4846008c04221001901202466024444c089391
  | 1 => 0x81001110100800202104208802090910224026
  | 2 => 0x188aaa248d548356888b5412b54092c5858d18
  | 4 => 0x32d4cc492906a59b5aa11024d992c089d80ec0
  | 5 => 0x23188871b198c9ec6ccd993811030311f76000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaececc8c8eeeeeaeaececc8c8eeeeeaeaececc8c8eeeeeaeaececc8c8eeeeeaeaececc8c8eeeeeaeaececc8c8eeeeeaeaececc8c8eeeeeaeaececc8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36328
namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1b2411c92091c42901400c002400000afc21ff32ff41fd32fe20ff42fe21fc30fe10fe41ff43fd41fd42fc10fe40fc40fc43fc42ff30fe30fd20ed20fc20fe42fe31ff21ef20fc31fd43fe43fe32fd30fd21fc32ff10ff20fc41ff31fd10fd31ff40fd40
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xf842500005891c0068002003890e4d70302105803e004a310c27ca918cf95331bb28c873e540cbd680905b948109eaa6633e54042baa720de54021b6a94213d548c6bca720dd94432aea98213f544427aa8085b14931bca80656f524c7d6a0905d54432b6a90616e521027aa8185b94a409e2a2217a500cadaa5184f95320ea988636d52902baa610db94a10baa8c87ea304827ca810de94242baa8861795090bd080905794c10bb288817551102bca610cf55021f490221ae54c827ca8187a48210b6a90815e53102baa6207a4c120d6aa6416d52042dca5185b54a20bd280436e520c27aa9905b948209e2a2613f544c2eca2184f55032
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x410002b858440482a8644c120ca15120442c963101209a580524c6aa64d4120
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/21+packedAt s4K5 (672+(h % 21)*6) 6) % 42)
  | 4 => 2*((h/29+packedAt s4K4 (1782+(h % 29)*7) 7) % 66)
  | 3 => 2*((h/9+packedAt s4K3 (228+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fe1fffc1e3ff8e1c71f8fff8e0ffc1e09f4f3
  | 1 => 0xc1fe3e3fe03c7ffe07e3f1c1f00e1ffe76489f
  | 2 => 0x1ffc03fffc07f1ff803fe01fff01fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0001ffffe001f80fe0
  | 5 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4240404404801004004824482224444009431
  | 1 => 0x184888488490b0060321108910448998324886
  | 2 => 0xa484149148094028c802a414a4a05244858518
  | 3 => 0x8192922142012531548002149498089580ac0
  | 5 => 0xb111b0039932649da693493801810311ef6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafac8fac8feeafeeafac8fac8feeafeeafac8fac8feeafeeafac8fac8feeafeeafac8fac8feeafeeafac8fac8feeafeeafac8fac8feeafeeafac8fac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36328
namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1830000030400021800c000f1840951840570c2dd31ff31fd10fd32fc31fe30fd30fd41ff40fc40ff42fc32ff32fc21ff30fd20fc20fe21ff20fd21fc43fe32fe42fe40ff43fc10fc30fd42fe10ff10fe43ff41fd43fc41ff21fe41df31fe31fc42fd40fe20fd31
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1823464100180071312cc3ab000000200088950010080001400000042000c06bca620d754c21ea20a636e520c2bca720d7d4d209f2a06575510c2f2a020cf55220aea9c43d531886baa718db54a40af298213e540c278a890cfd5110bb288653e54883aea298de942429eaa6635e538867aa810f54c521ceaa663d7414c67aa8195754c419e2a2215d53906bca618db54841b7294819e54cc67ea890db94810bd280837a500867aa9905714d209eaa0616d52043aa63885754f10b729083d531442baa6085d94430bca80433e54cc67aa8085d94643bca84853e54c82eaa321de54032af2984375510cabca7887a480209f2a0433e54042f4a0195b54830
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4040028c515131486556114d20a5993514c6c56210531c515131442d16010531
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
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
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s5K5 (672+(h % 28)*6) 6) % 42)
  | 4 => 2*((h/36+packedAt s5K4 (1782+(h % 36)*7) 7) % 66)
  | 3 => 2*((h/9+packedAt s5K3 (228+(h % 9)*3) 3) % 6)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fe0fe3c3e3ff8e3c71f8fc18e0ffe1e1bc4f3
  | 1 => 0xe1ff3fffc03c7ffc07e3f1fff00e0ffe64789f
  | 2 => 0x1ffc03fffc07f1ff803fe01fff00fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0001fffff001f80fe0
  | 4 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x442a044488582100c20582488222a25409c431
  | 1 => 0x8440808048090040120108510444488201886
  | 2 => 0x94821491900940294802a410a4a02944868518
  | 3 => 0x814a922242012561548002549494089700ac0
  | 4 => 0xd118b0033932649ba693493801818111df6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8feecfac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36328
namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5001fd31027f14003fe52007f04001fd21007f88403ff21007f4c009ff5300ffc8007fc4000ff90801fe4100ff8c803fc42007f94005fe5300ff08405fe43007f54803fc5201ff10401fd5100ff08007ff41017f14c01fe20007f90005fc30017fcc409ff51007f50801fd41017fcc805fc43007f44001fd50007fc4007fc54007f84001fe51007f8c401fd4001ffd0c01fd20027fd4809fc51027fd4001fd4301ffd0001fd5401ffd0805fc3101ff95003fc32007f4c805ff30007f54c01fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2001ffcca21037ee210801afe609440b7fb2c6204ff14d50015f8c6aa01bff4090001ffb2a6006fd44010007fa8508007f72148457ff322a005ff94521057fea80801bfd6590009ff29ca200bfd8953087fe6308016fe61884057f31e2000ff5954002ffe4328803fd3250069ffaa44201ffd0921017fe611881aff6404003fe90a4000ff181420bffca69001afe60880037f3102000ffd8953017f8629800fbf429000dff904a000ff58154007fac890017ff658c403ff9026406ff99220005bac608017fc3150401feb1a4206fb58a40027f8a8a8003fd6454405ef29a6001ff8c920017f86118913fe3294429fe29e2002ff50d311d7fea118803ff625440dff31ca000ff54e4000ffe4290002bd6488001ffb02a804bfd8150007ea628801bfe6504009ffa9aa406ffcc210017f8a6a981bfc3084071fe1046205fd10641005fec4aa017fc218c409fe29aa206ff98a3002ffcc91081bfd50900013eb2c6237ffd51310f7fe849800fbf435080dff2062004dfd5250005fec6a809bfe5290003bf292a425ffd494014ffcc4a800fff4090497fe21aa403ffd0943117fea318002ff615500bfe10c2005ff14410007fc82a8017fc628c40dffb146001ffcca20027f8a52881bfc208400dff2846000bf59520077fea48801afc658c005ff1946001ffcc95200df8c4a980ffc409040d7e324203eff94a41007fec8a98177d658c403fe2924003ff90a40007faca9901bfd6404001ff28a600effd451001ffea8a0937ff2050c017fb0aa400df54d5201ffc852080afc635040dbe282a000bfd954102ff8831080efe644840bff20e2006ffd421000ffe4090933fc415480dfe3282000bfd8951037fca08808bff528c001fe9922025ffd4540007fcc09880bfd328c00b7e30a8604f7d4d5302ff86208017fc6390437fe20c4002ef90d4302ffac720816fc6390479ff31a8239ffd023100ffe64a10b7fc4394001fea8c8000ff55132037fca0a0017fd5190401fe9824000bf5954100dfcc4a8003fd5390409ffa8aa800bf58a10015fcc6a801bfc6484057ffa02a004ffd4954237fe872880ffc41508017fb2a8434ffd4e21005feca99013fd5494007de2148202ff10d32037f881200037d5254409be28ca003efd05420e7fea7100dffe654c407fba0a8204ff94950037f04110037ff414400d7e3028604ff9495310ffe831801bfc629400dfeb142003ff152400c7fe8690002bd640403fff32a6003ffd0540035f8c910016ff6590401fea862023ff8c9401b7f8c898803ff6244009ff292a204bf195310affe818804ffe52c4001ffb2a8004ff54550257fea6a101bfd6194005ff29c6003ff95241005fac690003fd5448449ff29a8010ff14e1002ff8a2a0817fe6494407fe2a48200bf58e10007fa4288033fe5344009ffaa2a403ffd0554
  | 1 => 0xbff315400dfe2862000ffd8931005fac11881bff6304091fe28a6404ff54d5202ffc6298803fd42c40017eb2a8400ff54e2101d7cc9100fffc5390463ffaa24205ff5823102ff8c12080bdc4350c097f32a8000ff5061000ffc851081afc628c001fea9c4001bf98941277fea2a18e3fc428c40bff98e2001ff90a20267f880a9003fd3184017ff9022004ff1415321ff8c8a8903ff50904037f314a204ff15152037f88110003fd5188001feb0a8005ff1971017ff8c690823ff320400def1826006bfd9610007faa6a1003fd654c4037e312a802fd0c53102ffcc710803fd6444047ff9028042ffcc551007eaa388007fe425085bfe18ca002ff0c532015f8c68800bfe438c405f79926400efd9110017fe62a9806fe6250c67fe2044200bfd911002ffacb108cffc54884017eb146006bf18e20007fa84a880afe6390001feb1a8403fbd094202ff8820800bfc328c40dfe102a029ff0855000ffc64a1053ff30c400d7f304a003ffd51430dff8a910007ff2150805ff982a606ff0c310027fea0a8017fe63c400dfeb0c6000bf58a401affcc498813ff50544017eb24a010ff90e10217f860a883ffc3284003ff9028404bf19521025fccb1801bfe648c0017eb2a6400ff54a3101ff880a101bfc20c400bfe10e2001bfd893201ff8a8a1003ff6448405fe182a60affd4c100dffca9100cffe5488403ff90a6405ff1452107ff88508007ef204c80bffa8ca205ff8861000ff84099003fe6154c3fffaa26000ff8c62027ff842a9817fc6290485ff982a200bfd89400077aa8a1007ff524800d7fb124004ff14e51007fec6a8003fd439440dff1822004ff9465013ff8a72005ffc63480077e322a005bfd8921037fecb0805bff50c4009ffa94a206bf19010007fa8088003fd62540037e3128206ff59230007fa6528803fd654400bfe18a4206bfd94100fff8a298003fd54440077e322a205ff08551037fa8118012fe6590401fca042005ffd96410cffea290016ff62c4083fe102a206ff58a50277f8a2a1813ff5054c19fe21a202effd0a50005fec6a0007ff424c803fe9924002b798c100c7f8c89001bfe5048005ff9926200ff5523002ffc631093ffc6254c0bfe20a8200ff18532007fac2990f7fe6550401ffb22a203ff5514001ff886a00abfe63540017fb026202bfd8531037fc4108007de324c801fea942005ffd065102df8cb880ebfc508c4037fb2aa404bf99532026fea8a880aff604c009fe2a2a205ff0c551007fec8a9003fc6054407ffaa48205bf18a3101ff886aa016fc6154805fe18a8606ff1421002ffe6318817f631c4001fea1a4006bfd9220035fcc118017fd6388405ffa9a6200f74c931005feca98803ff644807bffa9a8230ff19121027fca8a8816fc6150007ff20c8005bf18554005faca08063ff41480093e3
  | 2 => 0x4002ffccb8808bfc518c06dffa026200ff5813102ff8a288017fc648c401ff30aa032ff14e2100fd884a1003ff6550801fe98aa006bfd9630026fea4a980ffe5450809fe29aa405ffd97101affca498806fe62544017fb1aa401fb9092102ffa838800ffc4290401fea12a025ff14540007facaa181bfd3084007dfa1a8006ff1922028ffe40aa00efe6494409bfa92a229ff1095002ffac928803fa4044035fe29c4000ff98543005facb1013bfc6550c0bfe98e2027ffcc64001d78c888027fe540400bff32c8205ff0c510015fec6a1803fd5350479ff992822aff90d50007fec299013fc5155005fe18c6000ff9062001f788320007ff3248403ff9024036ff15131015fec8a180ffe425047ffe1848235ff90931035fcc108012fc6544001ff10c8024ff0c540017faa698803fd529000bef31ca206ff9022002df8c2a1013fe5454823ffa1c2000ff5952102ff882908c7ff5348401ffb2a4000ff54541297f862aa00bff438c409fda84a002bf98d52037f8a12001bfc6494097fe31aa418fbd092022ff8872881bfe6194001fea8a6206ff9863006ffe8488002ff6050801ffb028204bf99521007fec688002fd6448401ffb0a8647ff99132017fe64a180afe639440bff20c4214ff90f10007fca318017fe3104007fe2a28206ff0c24009ff8658801bfc648c005bf29aa600bf58221037fac60800ffc4050401ff30a8005ff1053101ffa8520002fd658c005fe21c6040ff14241026f8a0a9003fd654c06dfe2026200bf58640005fac48801bfe1004083fe192a24cff1915209ff88588003fe6154801fea146201bf98a1001dfcc92801bfe304800bff28a2002ff90d5301ffe84a0003f93088005fe192a641ff1095101ffa8520803fd2044009fea92a004ff1415102ffecb1081bed620400bff98c8201bb98a40037fec520012fe65c4009ffaa4a001ff94942217fc86a8923ff544c801ff28a8003fed0140037fac52013ffc4254c0b7fb2e2006ffd4240017f060980dbfe544c443ffa146000ef50540157fe60a8017fb104400bee18a6203ff95141267fe80a9013fd549444dfe10c8002ffcc930037fe612000fff4255001ff10aa000bfd852019ffe8110807fe5254801ffb02a605ffd8b10007fcc298017fd658c40dffa044004ff54951035f8c0aa00bff534c001fea024006ff5422000ffca51087bfc414c07fff9848200ff54b10007f2410801bfc2090001feaa24004dfd4d5400ffca51000afd638c40dfe282a000ff98151005fec2a0017fd518842ffe21a4003ef1094002ff8c710817fe21c400dff9046002fecc1301f7f8412081afc639000dff106202bff1915002ff8432081bfc3054007ffa028404ff146500fff8ca9801bfc6190007fc2028000bfd8d42005fac520802ff614c00bfea0c6206ff98a1000ffc84a90a
  | 3 => 0xe1828400bf58241017fc64a9897ff5350061fe2024203ffd0e411d7fea518813fc5254c0bfe18ca200ff595410effca49801bfe400400bfeb1ca202ffd4e30017f6611800ffc4155001fe30aa401bfd8521007fc6328017fc5194401fe9862000bfd95400077aa8a180bfd328c4077fb0a8212ffd461025ffe60a9107fc625440dffb244049ffcc542007fa86a88137c5394007dfa0a8005ff90410007fa650801afc6588007de2048201bf58a2101ff880a181aff658800dff2842004ff1495101d7cc808067fc514800dff9844000df5515300dfcc5200cbff3088401dea1a8006ff5881015ffe86a8003fd529040dbf282a003ff15143197f86110812fc6550861ff2a24205bf1853000ff840a9003fe6050801ffb028606ff0c220005fec4a081afc604c403fe1028403ef95241015fecaa98f3fc5350405fea9a6005ff18e51007fac89805ffc314806ffe32a6202ff14d310effc84980d3ff5088403fe1044206ff18e50007f8c09900bdf324c403fe10c4006ffd4220037dcc52000efe644c48ffe20a6403df95154017fe86a980eff645500dfe1044052ff98d54037fac32001bfc6390023ffa0c2001bf189100f7f8a89800bfd438c401fe30aa606fb9881000df8c49801bbd64880017fb122003ff9514301ffa832000f7c5455009ffa82a422ffd52300affe8788017fe314840dffa002000bf59120037faa008007fc21508077e3226003bf99110036faca0801afc6204001ff302a606ff10130017fca718907fe625440fff290200bff98910025f8ca9914bfc63550037f312a805ffc8631005fac89880fff4055001ff3028600ff4861002fbe6318803fd6054801fe98c8006ffc4010287fcc8a983bff544409bfe3128604fdd4651087fca708016fc6154c6fefa9a6200bfd8153037f0a128017fe4150495ffa828400bfd81210177886a1802ff64480057eb1c6000bfd855301f7e86aa03fff2184087ffa1aa200ff1815301dfac920806fc625440bff20a624fff08153237fe852881bff618c0017eb2c6200bfd954301f7e84a180bfe328c407dfa12822dffcca50007fec2a90137f515403dff2a26000ff94520007faa6080137f5394407fe20a8600ff50e10267fe86a900fff545500bfeb148207ff9081001fe882a0817f63188489ff904a200bf5913202ffaa20809bfc329001fff1942001ffcc93202df8cb18807ff4248005ffa9a8606ff98c1000ff8a4a9127fc5350803be292a402ffd4d3201ffc87200137f5154801ff3024204bf995421c7f8a51880bdc5354c01ffb1a820fff14a10027fea7280a7fc3254001ffb2a8603ff10a40037f880080bbfc4194005fb98c6203bf19132216fca6a8816fc648c47dfe1948209ff1501001ffe80a080bfe314c001bfb2a2003ff90e4102ff8cb18803fd4154077ff2928206ff98e
  | 4 => 0x817fd418840d7e3028200ff4cb10007faa498817fe414840bfe98c4206ff5021001ffa84a0803bd545004dff90c8005ff08410037f8400800ade6394409ffa92a604ffd4e51006faa728803fd2190009ffa92a000ff4c620037bac60801bfe620406ffe2826200bf58630037fca0a8003fd6454801fe992a03bff18941017f8a6a181bff64040057e31a8404ff94a50037fc208800bfc534c005fe1826205ff5822102ffea318807fe524c8093f3282000fd4c710007f8c0908fffe539040dff1842001ff0ca200077c8320017fd6094479ff98a8201fbc8542017f88718803ff634800bffa8e2001fe0812002ffe432081bfe50c4007fea1c8212ffd4a1011ffcc4a000bff314c4017fb2a4214ff94f1001ffc86a1013fe5354065ff21c4203bf99153007feca88043fc4384003fe192a426ff8ca40007fec2a9807fc4288001ffb226400ff55210007fec898002fd6590409fea9ca000bf5954000ff8651080ffd4390001feb126004ffd4553007facaa1013ff5154487ffa0aa206bf18a50067fcc68800bfd534c80dfc1846004ffd4d54037f8812800afe6388059ff214a001ff10952007fa64a880bff304c479ff9828201ff08552035f8c0a9813ff525440bffa0e203cff0c141137f8a520127ff305080b7e32c8247ff1513202ffe831881bfc6388001fea8a6001bf98a41005fec0aa01bfc618c00dbfa84a0009fd9530007f8c2a1007fc3250861ffa024204ff15250015fcc6aa11ffc404c801fb28a2006ff9013002ff8429881bbf4090001ffb2a823bff0814100ffca490803ff6350801fd1022000ff58d54005fec0a90d7fc204c4097f32c8001bf98a3002df8cb1081aff64840a1ffa0aa629ffc855000ff884a1007fd5288403fea944000bf58e200377ac808077fe624c00dfd1844005f78c53127ffe42a9816ff638840bfe90e2002ff54d431f77c852081bfe6294003fea144004bfd855102ff84310803fe414c0017eb1c803dffd4141035fecaa801aff638809bff292860cffcc9101bffea098802ff634840bfe324a241ff8c951187f8a890817ff21c400dffb242029ff8c9500d7fe631000fff4050c49fe31a8002ff94d53017fe6518067ff54480037fb1a6406bfd8810007fa86a8003fd534840dfe2844001ff9092102ffec5188d3fc508845fff31a4201ff8862001ffe8720023fc530400bfe20a2013ff8cb10027f8a0a9093ff32500093f32c6206ffd925001dfcc8a8803fd51484037fb12a452ffcc954015f8c690017ff608842fff31a4021ff1063000ffa8510803fd43c4079fe31a8204ff1495002ffe631092bfc5050803fea928403bf1912020ffe42a881bfe640400bbf32c620effd4d10007faa098003ff624c097ff98aa403ff10540007fec4a1803fd6050c057f31c821effd0130007fac29800bdf3054c93f
  | 5 => 0x9531007faa498006fd6288001fea8a8000bf58a50026f8a0aa01ffc42040037fb024000ff8853002ff84290803fd504400ffe190200dffd0110035fcc118816fc614c8017eb1a4206ff4c220007fa8298807be425080bff28c6204dfd5153007fac2a8003fd40c400bfa28ca204ff55150015f8c6a8812fe658c40b7f30c6006ff14130037fec320003fd634400dff3242006ff5921001ffe80a00afff415400bff28c2019ff9952002ffe20880e7ff428c417ff2122030ff99121007fa849808ffe5250005ff98a600dff15110127fcc6a0003fd6254c01ff18a4006ffd9410017fe60a1816fc6488401ffb2a6406ff8c31002ffcc118817fd6090405fe1828606ff48210025fccb10803ff635480dffa04a005fe4401008ffe8508013fe525500bfe32c8204ff95250025fcca980fbfc529040dff32c8004bf99620007faa688017fb1084001fea126218ff1052002fe84310802fd6188001feb02a206ff59620007faa988083fe428c001feb1a8014ff10f1019ffe871080bfd538c09bfe102860dff19110007faa31806fff438800dfeb1c8002ff14d32217f886a881afc6304001fea8a2000ff591501dff864a0803fd5350001feb026404ff14e50015fcc6a1003fd52040037e312a000ff50810005fac92880bff304c005fe21aa61dff08530037f8c808013ef525480dfe2028021ff15230037f86098017fe2104009feaa2a64effd414300ffc8499017ff310400dff1002028ffd4640026f8a2a980ffe435040dfe2022000ff98154037f8a008003f631484057e31aa000bf5923101ff884a081bfe50900017fb2a4040ffd4a41017fc869881bfc204c00dfe2046002ff0c93102ef8a2a8802fd64884017eb222000afd9110037bcc60800afe639400dfb8802005ff8c510147fea520002fd648c00bfeb246204ffd4550027fca6a880ffc5450007ff2a2a800ff4ca401aff8849892ffe6354803ff9924000ff1852001dfcc898003bc6448403f72924005ff10651037fe4108002fd62c4087ff322a21fffd413001ff880aa00fff54500077f3246000df54a5001ffe8320117ff329440dff3148005fb08521007fec098803fe41940017fb0a8400ff5854209ff8a588003fd215401bff2a22016ffd4b10007f8c0a1817fe6390407df2a28403bf59240024f8ca98003fe315005ffe29a4221ff9523002efca2a881bff648c00dfeb282000ff185430d7fc8710003ff605080bfeb14a205bfd9221025fccaa18fbfe329040bf790c423dff1414102ffcc520802fd6184007ff2a28019ffd4d20005fac32801bbe648800d7fb1a6001fb1495223ffe809901bff300400dfeb1ca04bff90d5202fdc4290897fc6550005ff18c6006ff0c01000ff6411009ffe539000bfe10a8200efd9121007fa831001bff500400bffa0c8200bf59510007da8490
  | 6 => 0x5ef9826203fdd0641007f26090013ff549440dfe32c6005ff18a51007ea631080afc6348495fe32a8400fd8c51015ffe84a8013ff5154877fe292822fff90d21037ec208811bff4094409fea94a005ffd4621027fca2a8007fd524c803ffa944206fbc822000ffea51001bff6284039ffa8c403affd523100ffa6510807fd52484017eb1ca203bf19153006faa8a8857ff42c4009ff294a20cff14d1000ffa6510016fe61944057f31c2006ffc824000ff88490807fc5288403ffa92844bff0c152097fea90801bfc5094001fea824048ff1413201ff884a181bec204807dff9048218ffd0120017fa62980137f5354063fe32a424dff08543007fa8298003fd6250c07fe21c824affd454200ffca490133ff4154801fea14a0009fd9510007fac2aa00bf7314c403fea126406bfd8e1000ffc8490006fe6254c0dff31c2000ff9815216ffe6328013fd5394405ff98a6400ffd8d54017fc86a1802ff6448437ffa0c4002ff0c943037f8cb1001afc6504001fe9062005ff0c63100df8c49880bfe434c065ff29c4203bf19121027faa328017fe5154489ff214a203ffd0d41007faa918807fc52508017eb202006ffcc250287fe84a9803fe6155001fea928202ff14e3001df8c898803ff614c003fe2144203ff10e40037fec708017ff218840dfe184a03bff98941027eea2a880fff4150805ff9826424ff14d40007faa690007ff2154871ff9046204ff94d5202dfcc31881bfe405000bff10a4243ffd0951007faa290012fe650400bfe28c6231ff14121027f8a6aa04fff20c4003fe90c4002ff0c930017f860990b3fc2194047fe312801aff94e20237f8812881bfe4044003ff90c4002ffd0d31027f8a92880ffe425000b7e31ca201ff50921217f8c6a88a7ff2054053fe312a005ff14610007fac4a081bfe408c003ff192a401ff0853202ffacb20817dd639443bfe2126001ff08121037f84128017fd3104055fe31aa005ffd8a4117ffe6290813fd5454491ff32a6405bfd931002ffa8208127fe535080bff20a2006fe902100077a8520003fe418c003ff1944201ff8ca20035f8c520063fc54480017fb1a2000ff50d5202ff86308013fe5494407feaa48047ff9513202f7882a0923ff504c801fea1c4200bfd9530037faa118016ff655440dffa84a003ff90540035f8c918016fe6188001fea1c4000bfd913101f7882a1802fd64840097f32c204eff1414301ff8a8aa03bfe6544017ff2922006ffd023001ffc84aa017fd62c4007feaa48200df5515220ffe40a8816fe6190001eea9a604fffc815301f7e84aa01bfc6284003fe2944005ffd4641017fe62a18abfc435405ffe1824218ff95120025f8caa0806ff62508077f3242020ff94a3001ffa86a1003fd505000dff32c2051ff98954035fcc110823fe4304005ee29a6200ffd
  | 7 => 0xa00137f5294001fea946003efd0e41007faca90007ec324c80bffa082002ff50d30037fc6110002ff634800bfe3046200ff5912100fe8429081bfa208400bff10a2006ff99250035f8c0a887bfc644c00dff1022023ff08540007fc431800fbc41550017eb14a206f70c130007fc42a00c7ff504840dfe2822000ff54940005fec8a8013ff5454001fe9948224ffcc540017fe651880bfe534c40dfe102801dff14930006f8ca88003ff6350001feaa44204bf99541017bc869881bfc508c00bfe28c8200ffd815113ff86320003ff604c80bfe908203dffd4941007fa64a0803fd428c00b7f30c8200fd54510197f88710803ff6150801ff30a8406ff14140007faa91005bff54c4011ff298201aff10e20067fe62880dfff524c40b7fb1e2004ff141541b7fcc898807ec4248001fe98ca03dffd454102ffe420800bff318c001fea0ca005ff19310005fac7208c7fe654846fffa8a6203ff50d41015fec6a9812fc654c005ffa1a8603ff5514202ffec118817fc3190421ff9942002ff4c93103ffc640800fff415040bffa0c4205ff58f10027fea8a981bfc6204005fe18aa652ffcc554037fca1100bfff3048403fe2126400ff58951217fcc6a8802fd65840a3fe102a804ff14550007fc8290017fc4184009ffaa2a206ff18a4024ff8c6a114bff305500d7e31c2004ff14553067fe6088017fc51c400bff3048206ff98e2002ffca38801afc6494001fea182006ff0c110037fe611801bfc6384095ff32a8405bf9865000ff864990b77e53940017fb0a6400ff58d2002ffec120893ff305002ffe29a4000bf58a31007fac899003ff625040dfe1046002ffd0d30037fccb1801bfc3050001ff28c8005ff08510007daa4900b7fe439400ffe2902012ffd4e1000dfcc48801bfc658400dfe1022002ff90d32037fcc32001bfd6584059fe194a019ff19520037dc4090003fd604840dffa84602aff0c5500277ea8aa14bfc305500dfeb1c403cff94d41007f8c098863fe6448059fe214a006ff4c010007fa8290817fc31c40017fb02a205ff9464128ff842aa00fff429000bfeb14624fff98953037f8809000efe644c81dffa822006ff90120287f8c8a981bfd6494001fe98a4203ffd0a41007fec0a9017ff64c400bff32c6204bf9953102ffec52881bff6194077ff90a8205ffd8e21007fc432801aff62840017eb244005bf1925101f7e80a0897ff505000dffb1c4005bf193101affe4298802fd6548401fe30aa83bff8c941035f8c5080137c509440dffb2c4004ffd415402ff8a2a8817fc658840bfeb244206ff18650007fec4aa00afe63544077f322a409ffd0c10007fac6a081bf840900017eb1e2003ff9094302ff8c11080bfe324c4057f31a8201ffd4952037f8c310007ef2054803fe1924200ff59131007f8c2a000afe634800
  | 8 => 0xf1055002ffcc588003f92044001ff28c4004ff54a5100dfcc4a0007fe324c801fd1824006ff102101cff8a91881aff648c00bfe20c8206df99410005fec2a80abff3254051ffa9c8005ff18251007fac6a8803fc6154003fe2926403ef95140005fec09913bff5250c03ffa12a404ff5515200df8c4a1903ff539042fff98a4002ff50d32026fea6a9003fd6354005fe21a6201ffc8521007fa62a0003fe61480097f32a4003ff1094002ffacb88117fc3094409bfa8aa811ff1521000ffaa490013f85054009fe294a000ff1815202f7e8320803fd6244001feb22a600ff50a51006faa928007fe2148003ffa144004dfd495402feca388003fd314400dff102401fffd493002ffe6328803fd4144007ffa1a8400df54550007fec8a8003fd214c05fff29a4205bf18f101cffca9188137f54548077f3262006ff0c230007fa8318002fd630400dfe2824001bf98a50035fecb2007fff514c007ffa0a8600bfd8931017fa6318047fe548400dff2826002ff4c930037fccb1000ffd4150003fea124003ef951430077a84a0803fc614c00b7fb1a6214ffccb10035f8c0a1002ff6254085ff992a200ffd8540007fac0a981bff6394089fe104a203ff10d4123ff8c899003fc6050407feaa2820cff90d10017f8651800fbc405080bffb1e2000ff18154006faa6a8003fd544c40d7e32c8006bf98010247f8ca99017fe6588401fea1a421effd053022ffe6128817fc41c4017fe2122001ffc8152027fea6a8002ff645482dffa9e2005ffd8e51005dac40800bfe5350c05ff992a605ff19221005fac128943fc4154c07ffaa48002ff90e30005faca9881bfd618804bff32a8005ff9825126ffe42a180bfe3250c17fe1922006ffd8810005feca88007ff2088401ffb024205ff0865102ffc6308007f7218842fff9824000ef50e41007fac4aa01afc604c841fe2146006ffc822001ffc86a0016fc62c400bffb244206ff0c12000dfcc58801bfe500400dfe3146023ff0c94001ffc86aa007fc214800bfa18c6201ef10942107f84318003fd6150c0dfea044005ff1055124ffcc6a1012fc6550c01fe9902005ff9822102df8c29002bff520400dfeb146000ff58142017fca698147fc325500b7fb246200bf59543017fea6a9817ff510400dfe1024003fed0240007faa488013fb50540037f3126200ff5091002df8c2a801bbe6404005ef98a6051ff18954007fec2aa077ff214c007fea128000ffd9110027fea6a8833fc63440017eb2e2003ff1095426ff8a4a1877fc624c0057f31a2006bf18e50007f2808801aff63040017fb0a8630ffd0d2126ffcc4a180efe648800bfe20c6205ffd9231017fc6498067ff504800d7e302a406bf19610007fac6a900efe64884017eb2a6000ff98141015f8c6a000fbf4050c07fe21a8428ff14640007fec4
  | 9 => 0x37f3126003bf99150037fc6098003fd6250001fea1a2002bf18d52037fac910003fd61548017eb10204eff9954302ffaa38801bfc40540a3ff90aa800df94650267fcc8a9012fe654400dffb2c8003ff50d4001dfec0a0013fe5454001ffb1aa200ff9813202efea328803fe319000bdf20a8202ffd4e31037be611801bfc6590001ff30a6400bf5964027ffc84a9817fe418400bff20c6220ff14a30037f88188073ff5488007feaa28600bfd8930027faa6a8803bd435080dff204200bff14910007fa6088003fd614802bfe2a62035ff14931026fea0a9803ff6548403ffa926400bf58e50007fec2a8016fc6290405fe21a8603af1912102dfecb1081bff2004009ffa84a200df1953002ff86310803fe3154047fe2928005bf18a5100fb86499012fc6548003773102003ffd514202ffec128813fc5454c0bff28a8200bf58e211eff8caa0807fc5248409bfa82a200bb58a40007da4290013fc5255001fe994a000ff5893102ffca29892ffc315480dfe3182000bfd8d4101ffe84a0806fc6250003ff1924204ffd4a50027fea328012fd6594091ffa8a6400ff5013021ff880a880fbf4055001ffb0a4004ff94e50005fec4a1803fd4148001feaa26015ff95310015fcc6a00dbff424c403f790a40009f5941000ffa649088fbe4250001ffb12a005ff14621017f88698002fd6344001fe98a402effd065002ffec92881afe6090405ffa1c6002f7cc543027f8a2a901bff658c005ff29a6400ffd8d2102dfcc208007ee3248071ff2946204df14d5102ff8c78801bff629400dff1802001fec81200e7f8a310117fe4394409ff2a2a602bf98d21005facb10837ff434400bff18e2000fd4c52102ffcc988017ff6390401de3222005ff98a5107ffca50801bff408401dfe32a2000f750d31037faa108002ff6354489fe194a247ffd0532005fac988007ef20484017eb22603fffcca4100dfec8a1013fc509440b7e31c4200bfd9132005fec0a18d7ff204c4077f3246203ff1064002ffcc91881bfd1004095fe28a8401ff1092001ffe86a000efc6444035fe18c4044ff10a51025facb288b3ff2194001ffb226204bf195400bffc869000efc645480dff8842001ff0c920015fcc608007ff4250805fea9c6200ff54610007fa432800fff4355003ffa92423bffc8141015fcc7108c7ff514845dffa1ca027ffcca40035fcc120002dd6394471ff2146249ff0c542005fec0a081bfd4004005be29aa606ef1014000ffe8510803fd54040077fb2aa804fd14551037f42008017fd518c401ee98a6000dfd9530017be6299003fd5384001fea1ca039ff10231167fc652803ffe4284001feb028208ff10c101b7fe829881bfe6188005ffa1a6405ff98a3102ff8c588006fe628c40dfeb2c6003ef1515402ffca3108c3ff4148401feb0aa62bf
  | 10 => 0x1900003200909882d0018218018b380180002e01886385f80006600114f00780080000280700080d80200090c02b0088040128e480900000400000900280281681483102381180096080080000780780280080236782900480280284e80600000280d00180001080004800300d81b03f80c00301400181c80000000d8c900000603418f83f80980a00080080180e82200507000a32180406480285e00480300006180181900b00e00500b0018293be02801482301b8038b581b02f80302588b8ac80000080600180382100680700380000783480780980001981101400c8008000030dc00c80a80606485b00027080e00580000980a81300288200483f80981300000080080580001201000d00181780b80e80c09280000100200b80580b83100084f00001002380f00a80c80402285081000100000500086e00700880088a80080b80000000000012482e00000880707a80200a05e80300f81280000080201000c1a6000009803264000001015002001bdc80680680202700000000415c01583181b00000601600006680700380000505700000082581601201581180200f80302e80080300500000100f8000010940088028eb8078080040a980682385900b80004a00000000000101880380600300e07900500181780100d0088011a080780280480400000000600080001e9c400301b85a80200c80004180400200828281300e8e901105100f00002000402c00200c8078658468000270000018030000000070018310830140058000380000178199ad80a80a02400800181580280006880380100880000100b01425500004080001a80180680f80301a81180080900000480280100e00506700f80080000481000c00001082407b8090048088062b980000000081d81500100b0c680208c80700e800823044805bac83680985800580281600282101207e0092ef80000080100000600201b03781300a80801880600000180200e00000000283b000806b2b8d28a680005901e80000580000000c814805803b5b80000000f00800000204300080000080000c0178008d500100f80080580405180080201680000002600184780000000803d02c00904881e943077ff204c017ff90a2043ffd015102ff8a29882ffc6244001fe90a8005ff94410007fa4318027ff42040a1ffa02a600bfd9151005fec8a98a7fe42540077f3202004ff54d501aff8c49880ffe5490027ff2162000afd912102ffac988147fe3255005fe29c6203bf99120005fec89800fdf4350c83ff212a220ffc86300f7fcc89801bbe40500a1fe202a605ff98e51037fec720003bd549045ffe21a4206ffd8620035fec8a001bfd20040017fb1aa800ff54f1002ff86298813fe5355001f69924002ff50e3006ffcc88801afc6048447ff90a8005bfd9141037fac70802ffe3244
  | 11 => 0x38a420038000e605b80080800000000208980300000380200281800400102601e00100780100780180600300300408c82702180000500080000182792780100000000f00081401601b1bf00100002981606100016402080080487a00a00000100a00000002700001480000080480080780e83000c00003e83300080100380100000180408080280680082f80780280000705700000181295900080680200f00080580b80280500a14800003300100900180380000000a02480b81e01180802280005282181480100380100000580103880385e81a8008158178019e720800d8018b588300580081300201a00904781080780e96a00102280702880205e00000000002a8278d502d13281a0f58000008000110058010063f300880485302380001500200001caddb8082b81880a801001819001bb480c00001b80e02a85080985c00080005906b80480e80080180603683281300f8000008
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd20d9121004fc7648530014fe7359542034fc7059630026be6555143357eb428c12016d7c7355250005ed75485202f67d619465021ebf41d9151136ec5258a40036fb6348210036ec2058a300767f52d9510014fe73586500067c65d8d1001cfc74d8d500067f65501100067f7558d20197d7304c621037e8728c12001cfc7459631005ef724c120004ff7158e501873d75191210057f754c120024ff7654521005ef7250d20036fa7688110005fb7055120036bd4058640027776155151016bc6350d40004fd7654e20006ed75588100067f6254550014fc73d814111ebd7259220004fd73d8554196dc5358e21005ef724c62000dec7250d2028f6c7255152024fc7559231004fc7650d510067d655493101ebc64505211f6be4258a41004ff73596400067e74d951001ebe6450c10016de634cb10024fe75d8143007f3704c51002edc3158e5103eec3258810024fe755913102edc3158f1002cfc7654e2102cfd74d9541024fe75d9120336bc6150d4002cfc715941002edd4158c100c5ec7448520007f23190110004fd70d9132024fe7558e210efe8424c120006ee745881001dbe7494540004ff7650e502167d735963102e7d51582510077554547102debc20d911000eee6250a51006ef5258a40006bc6418121004fd768c640035bc705054021f3f43551510b67f545971001cfe745862001efa645021001cfe76d9130014fd70d9530004fe7654d1038edf31d8143037db734c12002ef6619462026fac7250d4208ebf41592102067f5059641007af7250d4224ede6350a51004fd76552300067c655913002eec6148520004fe765052002cff769464000cfe76d89402873c4155153014fe73591101f6bd52d912102cff7688650004fd70d9153006f96018142004ff7558a3001cfe7458e50006bd6450810006dc7058e51005fb7050510036ed4058a40004ff7458d2001fb661552410c6be5459120006bd5458a41006ef7259520034fe70d95410067c755913031f3f40552500067e42594103176c505492000cfc72d8d4102cfc76552210057f7550650034fc764ca5017fd6434c5210067e535962101cfe74d8d100367d5058650006bf64d8121005ef7255120024fc7558e40016f4634c521036ee4058a403379e6350e4100cbc7650d4201dbe748c54000dbc765514200cfc72d915316d5e739465002ef7628c52102cfe71d8142004fd72d815300cfe725923000cfe7650120006dc7258e51006df634c521004ff7258e510067f75591300067f655414002ede5158c10034fe705963028eee52d8954006bc65d912100cfe72d953007fe8424821001cfd72d8142004ff7458e200ff5d7319530006dd644c5303d6fa50d815200cfc7258f10035bc7050d40024fc75d89100f6dd4358e4000cfe72d8543006f5624c510075f57594510
  | 1 => 0x8d50006bf7459543006be325901001cfe74d9520006bd5458241006f5618c620034fc7655220004fd70d8d4128fac725514202cfc7158241006be7259010006ef5358a40004ff7648650024fe75d8d42465f7715894102cfd73d8131006bd645523002cfc7654110006dc7458c10007b4715094145e7e53d855302eef415881014e7f5259620024fc7558a10046f7764c71000dee7254d2002cfd72d91210367f70594102d6bf6418540036ed2058620034fd70594102aebc21d9110007e46148520004fd7654d21004fd768c620024fc75d85200067c64d9530346bc41d855422edc7558e51014fe7650130007f151901100067d74596310367f205941001cfd71d8d41036ee105881002cfc7158251014fd75d915321f3c64551510267c655412003eee5258810034fe70d8520024ff7654610004fc7650950436f621d8552004fc7655110034fe768c650016bf7650e410ff3d7419530006f7624c5103957e76d9530007e93248110006be53d9110004fd70d915240ef621d8532004ef7258d1002edc7158c100247c7558d10014fe76d8d21006bd735922001ebc6450d10005fb704c5103b6be54d81422175e535453002ebc71590100067f7558630004ff7059221156dc6358d5002ef6768c5210a6dc5358f101c6ef20d8d21024fe7558a10005fb7250210496f651d85530067f755953121ebe54d915101cfc74589100075f654c5300257c7550d5102cfd73d893137efb764c22002cfc71d9110016f4764c521004ff7559110036bc4059010037b8405011002cfc7159640034fe70588100067d6394650006df7458c1002ef46554710036bc2059220014fc735912001e7c765515115ebf4359540285be74181530c6ed5458a4002d7c765495100cfe72d853036efa20d814229feb424811025edc6358d52006ed5358a40006ec5158a40006be7359220006bf30d9110014fc7359541005bf7459510366fa20d813202cfc715822136eec42d8142006ed6250b10015de739053000eee6254810036bf105901006fb86490110015de7350931026ec6554920004bf7458650014fc73d8910004fd764864027eee32d895308ef541d85401c6ee4258a3106ebf40d9110335bf7150e41086df3158e1000cfc7259250034fe764c810004ff7359641004fd76945300067e72d9530004ff73591101d67f54d8d51024fc75d9110006bf64485101d67f5259631266bf4359542006be65d912100cfe72d8153014ff764c12000cfe725954027eec6258953007e631485200967f5159610004ff7650f10036dc3058e10005ed754c920004ff735865008ebe545921005cfd76481100bfe9328c120006ed62486303157c70551523b6bf41d81420273f7455151004ff7458f10006bd6450e50005ef7050921376fa20d8152037ba644c22002ebf51590101f6b
  | 2 => 0xe7c6254a500247c755891002c7c765495106fb864501100067e4259631006bd72d9110004ff7559121104ff7358d200bedc53d8d20004ff7650d5011dbc7250540005bf74581211f6bd72d91210fd7c755913016d7e7394650007d5434c5214e67d53d9532037eb624c120015dc735053101e7e645515101cfe74d954017edc30d8d21004fd71d8953004fe7650d520267e655512102cfe71d89301cebf425923102e7c5159631036be70592203ae7c10d9530004ff735931000cfc7259210046de4358c1036ebd74d81420057d75185422073f52552412f67e71d951002cdc7650d310063f6519110005bd7418151036df7358e20006bf6458121014fe73d9151286bc415954301cfe74d85200b77750547100067f755954305cff72589100067f6590530007b9415011001ebc6450a1002eef7258a310067e42d9510014fe7358a503176e50549201873e7519121014fd72d8132036ef7258a100267e6554b1023ebe644c81000cfe72d913002ebd7159010024fc755824102fd4634c71002776719465000cfc764c521077775254510006f5615462048e7f54d85520067c73d9510006be4259230004fd73d854001cfd73d9543004ff7259641035f870551201c6ef2058a31036dd1058c1022edc4358e51004fe7655110034fc7059131006ee54588100273f7455250004bf7458d10346bc61551420c6ee7458a4011ebc215922002ff3604c510036be405925001cfe7459520004fd7654d10024fd70d8950007f231501100e67f5359620004fd7650650026be6555142034fe76d81433de7e50d8950004fd7688540036f51058e102167f5359631004ff7059531014fc7358b10016de6350c10004fe7654910024fe7558810006ef725912116e7d70d95300257f7354d52024fe7558e4000777715495102cfc71595320acff7059110006bf64509302c67f6518151036ed30588100079d43509310067f755824101ebc6490520004fd73d812101cbc7458630006be42582410257f7455151016dc6350d2001dbc74541400067d655523102fd7734c51022f5f3054e510067d6554e202167d5359631005dd7318520024ff765954302edf7358f1006dbc7448510006bf6490550014fd75d89530067c62d951002eed315881021ebf4359641004fd75d9110036bf705922001cfe74d85300767f53d95100067f6554d100267c6554a1002cfc7159543036de3058c10004fd7654f10024fc755911002ebe5159010004fd70d853211ebd215922002fd7634c621024fc755922025ede53d8d52006dd634c620006f77159521037eb724821030dbc7055142006be5359220014fe73d8552005df7358910014fe76d8d421667f52d95204d67f52d9532034fc70590100076d52545200057d758c540005f6768c5101773f43552500067f6555110004fd71d
  | 3 => 0xc7258d100fe7c654c1100067c62195300067f20d9510016f4634c51017edf31d8d21006bd6390640265be7498152006dc5258c10034fe7058a40034fc7059543007776594510035ec70549200073d5454e410067c6558530004fe76905300067f6559110005ed7218151006bd6519121006dd7458e51004fd7655221006bf745954223ebc644c9100fe7c54d9530037ea72901102267d52d952102edf3158a315367c50d915202df871501100067e62195100057d754c550006ed6254810004fd71d9130066df31d8d1027cff7259532034fe70d8d51004fe764853002edf31582310247c7558630185be74981211be7c654c510007f15150110035f6705471002efb705825100775545451000cfe725823102ede2158c1002cff7694630036ef5058a4002cfe76d85420257f74552502c57c7054e51006f761985300067c6558d103edfb7059150024ff76595420057f755913002f7451545102debc50d911021dbc74589511debf4259221007787054d5012e7c6559540005bd748854001ebe64506500a4ff7058d1042ebc10d91211f6ae6290640005bd75505401fede4358e41024fc7558a4022edc3258e51004fd74d9521036f7105941002efb105861001cff76503102979c735514302fd7734c62102ef91058b101deec32d8941036ef7058a40005ed72981410bedc31d8d200057d759853002cfd70d911001cfe7459410005bf744855001cfc7458d20006bd6519110004ff7558f10004fd7654e412aebe31d91100057d7598543016bc6350e4101cfe76d915341ebf62191211aeec625893100eee6288640004fd71d8930005ed7298143296df31d8d5422e7d53d9531006bf7459521004fd7654d2001cfe7458a500067e5359641026dc6554d3001fb771505400247e75d814200cfc7259010036bf305922002e7e715963122e7f53d9531006bf7458d212773f515514302eee2158a41034fe76d81322ee7f61195100c5ec745492052e7f51d895402ebf74592312d7b410191101afd7324c52102cff7158810024fc7558640006f5614c640486bc41d9541136ef21d912000cfe72d81510057f7558910417b4211912101cfe74589100057f755893002eec415881002cff7158c10005df754c53021ebf425954142ebf64185420357c7654d50004bf7458630024fe7558a30014fd72d9532005f7715011002cfe71d95420067f6555120014fe73d9120014fc73d8954007af6250941024bf7655241006bf6498121034fe70d8d10034fc7654810034fd74d8d4001e7e6455153034fd71d91100cf6f5454920035be70551404e67f53d953242ebc71d9121014fc7358a50187ad721912121ebe64d9151006bf6550d422367f54d9541006bc63d91210ce7c51d95201bedf53595310267c65549300067f655413000cfe76541200c7af4255120
  | 4 => 0x953001ebc64501100067f21d95300057d7518520005ef7254521014fc735881002cff72d95211f6bf21d9121005f97448210106ec4258a3002cfe71d9530034fc7058e10034fc765451002cfe7654f100075c654c530004ff7654e10034fc7058a4053ebf43d9153004fd72d855401faf7250a4002ef7604c510006fb60981310367f4059410007bb6488110014fe73d815402edf4158e51004fd71d8d540057f7454951006be4359010004ff725925012d7c7558540014fe73d9152004fd72d8530005ef7258d41007ac744852000cfc72d8d54006bc30d912102ede1058e5100cfc72d9110014fd72d913202e7d21594102767c50d9543005f9718c1200257c75886501bede5258e510067f659454031e7c50595400067e5359410346bc61551400f6be64d9130006fb7058d20034fe70d8951036ed705881001cfe74d8550004ff764ca51016dc634c521004fe7654d21004df7359520004fd74d85301e6df31d8d41236bf405925106ebc42d9110016de634c8100a7d4534c7102167c53d8d51006bf64545102dfb56190640006ef725913101f9f7350d4006efa40582411ee7f535925102cfd72d9521006dd6350c100d7da534c220036bc5059220005bd744c54000cfe72d855401dbf72509410767e65d951002cfe71d8153006dd6354e40006de7258c101d67f505963102cff7690650036bd1059010014fc73d815201cfe76d915007eef2158a101a67f5459621014fc7359521036f7715865027dee7218153005bf7150d42024fe75d8543006f5624c7100057f75585402567c5059542004fc764c940024fe75592310067d6554640016de634c5202debf71d91100067d6454e5101cff72d954202cfe71d81543e5fb7058d50035f4709451002cfc7694530034ec764c920015de7388530005dd7388530006ef32d8910024fd71d895105fe862481100367f305941002efb70582210367c505964001ebc6450d210257c7550e50007af7255142005bd748c540006bd7559220004fd768c5200bedf3158d2033e7c6154d500067f2059631034fe7058e50006bf6550d4016e7f31d9530046df3258c10166ef2158a501afd5324c52101ebe64552200767f50d951002cfc7650a31007786548110015de7394630136ee4258a4001faf6250d4202ef66118530004fd76486300edec72585303ae7c30d9530216de63d8d5100ef862481102767e6550c10004ff7458e21186bc54d9121034fc7059621036be30590100067c65d91100367c20594100aefa40d81411aeee62d893128eee62d89540067e73d95102073f5355241014fc73d8554036f61058640004ff725954002eef7258a51006df7358d20024fd72d91520b67c5359710014fc73d9542004ff7058e2110dbc7448630004fc7654d21007b4648c521004fe764c9410cd7c754c120006e
  | 5 => 0x2edd3158a3102cfd73d953101dbc7448640216df3059531006be4259250116dd53d8d5007777505451002cfe71d8d42006bc525901002e7f7559710036fa768c1202067c65905303ee7f51d815402ebe215901002cfc715901001ebe6455130014fd70d893033f5e6354e51007f25148110006df7358d21036ec2058a400257c759065002ef66118540024ff7654120005fb7054610035fa70945200257f7354d50004ff7458b100adfb705854000cfe76d893101cfc74d8d52004fd74d852000774658c5100067f65509300cd7e758c520034fe70d9110034fc70595421b6bf42591310debf43592201bf5f535493101cfc74d89310a6fa30d8131006ef725953201f9f6355143014fc73d85520075d535493020eee62d89510267c65545411adec7258131014fe7359221024fc755822101cfe74d8d520167c7654d52016f6634c5104d4ff7559532004fd73d952002eee2158a51286be6454e2032f765354710017d7714c530187ac405092101dbe744c540004fd7688530006bd6350a4002cfc7158d20004ff7358221014fc73d954002cfd72d81210057f7558d20034ff7058610016de634c640185bc7458121006bf31d91210067d6554540006bf54d9110035f87054510034fe7688640004ff764c64001cfc7458650037b974881100067d70d951011ebc725922002dee715092101e7c64551531fedf3258e41006fb6098151006bf645095050def72595423379f3150e41014fc735964002cfd74d8941024fc7558d210067c71d9530006bd64546201bede5458e5102ef6618c64018e7e65d952101cfc74d9531004fd75d8d410c6ed7458a4002cfc768c5401b6dd4358e410ce7f50d952001cbc745952142fac21d91210267c65549101f6bd71d912102cff715941027eee62d895312ebd5459250006bf7459510004fe765512102f76758c510034ff74d9540006de7258e51187af415092115e7f5459640024fe7558e10036de7058c1001ebe6450e500767e7619510004fd73d8950014fe73596400067c74d9510036f61058650024fc7558e10004ff764c550014fc73d912006ebf43d9110005dd739453002fd7634c710005b97488110034fc7654620016de634c5400057d7550951007777154e510057f7550d51006bd648c620024fe7559110004ff7058d210067f725941002e7c2159410035f87048510006f5614c650016ee634c92011dbc725514001cfe74d8950004fd7650d20426f621d8542006dd634c310136bf42d91200267c6554d21004fe765493100cff764831002ddd73d9531005bf72551433bebc40d894002cfe7655231035be7050d4001ebe6455010014fc735865002cff7690620014fe76d8d100267e6554a3101cfe7458231014fe7358241345bf7155241286be6454c1002cfc7158e51016f8764c1200067c641
  | 6 => 0xe764c940036ec105881031e7e5059540014fc7358a5100eae6250a40007cd324c520034fe7690620336bf6550e410267e6554540015df714c5300179f7450d31004ff764c520036be5059220216dc6358d51034ff73d9130016de6354c101bf5f53d9531077746554510006de32d8d10036f41058640006f56118530004fc7650d201e4fd7650531036ba105901002cfc764ca41004ff70591210257c7550650036ee7058810166ee3258a502157e735495102fd4314c510126df31591300057f7550e50014ff764c110036df30596300067f30d9510006fb609814202eee2158b1002d7c71551510067c20596311bedd5258e5112f3f51551403ffd7534c521004fd75d8141034fc7059532007ad4250521006df634c1200057d7550a50005bd7498132004fe768c520024fe755922002eee41588101acfd764c5210057f754c310014fc7358640004ff7458a5101edc6450d310267c6594520035f4764c5102debe20d9110006df4258c10066f63158630024fd70d8d50014fc7358241007b94350110005bf7055143005fb744811006ef6415864002ef66154640004ff76552100277a6055250006bd6450c10007f3715011001eec6450921036ef4058a40006ee5358a4000df6724c6212debe50d91102e7781019510006ed624864002cfd74d8d4102ebc415931000eec624811002cfc7690530456f631d8543034fd74d9540006bd54d8d40006bc735901001cfc74d89304967f54d85532c67c20d95101f6bd42d9121036de3058e1021cfd765454102dfa714821001ebc645511002cfc71d951002ebf74593101a67f54d895100cfe72586400fe7f51d9530026be655524100cfe72590100367e5059640005ef7250120004fd75d9120004ff73588100073c6519110006ef6250930006bf5459220007e5428c521006bf645012001cfc7459710034fd71d9510006bc621911006df97098540004ff7458e500267c6554130036de4058c1000cfe72d8d4023ebc41d9132034fd73d953000eee624ca40006bf625054002ef710596312467e654c81000cfc72d8d20004fe7655120486be41d95413c6be54d8143004ff7259630006be75d91100ce7c65481100257e75d8d51004ff7358a10004fe764c540036bf7459010014fc73d9151086f531d8530004be7619110006f77158d10006bf3259010036ef3058a404edef7258d4206dbc7458d10004ff755891000edc764c9312debc62906401aeee52d8931024fe76d954202df4728c521004fd73d8151004fd71d9132034ff72d952002eec2158a31286bc6454d105567f54d9543026746594510016f8634c120036ef7258a501bdde7550d31004fd70d9542026bc655514228f3f525514201cfc74d895300cfe72591310067e71d9530014fe735961002eed21582210267e65543100047f7558221
  | 7 => 0xc93102cfc7158e414ddef7259532004ff73591200267c6555230004ff7654f102aebc31d91100067c7558d1002cfc7158c1000cfc72592300067c6558910286bc64591530fd7c75585302c776619465002edc4158e51004fd71d91500efea524c12000cfe72d814100cfd74d8d4202e7e6154550006ec54588100276f6255152065f5738c51026eee32d894316f5f31d95300bdde73185201b6bc40d91311bd7c755813124f9c6350d420067d5358a5101dbc744854000cfe72d91534d6ef20d953200e7e6254951004ff7458c100067c7559110005ef7258530036ef2058e2000cfe725913000cfe7259641004fd75d9121067d4534c510005f7754c710006fb60981323af5c30d9530024fd74d8154385fb7058930006fb609815401cfc74582210276f6254d52004fd73d8941004ff705954100cfd71d9521004fd769065000cfe725961000d7c7655152005ef754852021e7f545964108fbb4350210014fd74d8543006ee755881016f7b30d9530005dd7394520034fc7654a30006ef7258d1002fd4634c62102cfc715952007fea52482100067c7359410026ec765492007eee3258a10446f7764c62102edf7358e512157e735515101cfe7458d10034fc7059410034fe7058e40004ff735954206fbb4290110006dd634ca4102cfd715901001faf62551420067f65945302f67c21d9510226ee62946401adec7259131036be20592200067d54d895302cfe71d8132124ff7359130004fd72d8d51005f571181530067f4059631036f61058610005ef7250520186bc40d912102e7d2159631005ed7218131007d9534c1202167e735963100cfe7258251034fe705925002cff7688640004fd768c540006f56154630035fa708c640006dd634c810066de63d8d1000eee6250810005f7715431011eee62d894016e7e32d9530004ff755931008fb84250210007e870485202573f53551420267e6554d42016df6054d30004ff735952001ebf6250d4200eef6054920004ff7258e4001cfe76d9110024fe75d8141004ff7259131016de6350e5102cfc71592202873c6455153034fd75d855002dec7650921036ee2058a30084ff7158d10034fe7650e1001cfc7459530034fe7650e2042faf72d912100df8764c12002df8765011016e7d73d9530456bd74d85430367c5059410036ef2059620036f51059410036ed5058810004fd74d85320067f40d95100067e53d9510034fc705881001cfc74d8d21014fe76d8d40004ff76509500067f6548510026f66554710136ec2158a400067f7559110004ff75591310057f7454a500275f6355153004ff7459620036bf4058640006bd6455132037bb645021001cff7650130034bd74d894002e7e3159410296de63550102167f3059631036fa2058e10004fd73d8141004ff7259510035f67054510004f
  | 8 => 0x34fd705862002ef661185540767f525865001cfc7458d2102ddc7650d31004ff7258e50004ff764c95001cff7650531186bf4358a41006bc53d91100267c655494001dbf7250a4002cfc715913202edc5158c10006ef7158a402bf76535451014eec6258950005f9708c6201167f515963002cfe7159231286bc6454d21004fd72d9150006be7559010006bc31592200efe8724c120006f77159531006fb7059110005bf7458530016de634ca51024fe755822112d7e7518540004fd765513100cfe72d8131375fb70595202debf6190640006df7258e51024fe7558e41266bc41d9152006bf6450521004ff72592310267e6555010016dc634c51002cfc7159631006bf7458d10035ec765492024f9f3150d42004ff7558a41006bd644c8100fe7f5258e50036fa601815201cfc74d8d20005bf74581310267c655411027eee6254e40034fe70d9542005ef7258543004fd72d813100dfa724c220004ff7654910006be6519110006f96018131006df7359531016dc634c110134ff745912004ebf42590100257e758c55001e7c7655153004ff7650d52004fd74d855000f6f7554920004ff7258251014fd72d8532007e9218c12013ebd43d913002eef7158810014fe73d855415ebc4159640004ff75591321ee7f525954101cfe7459610004fd76551102f57c715525000cfc72d9150036fa6018154004fd71d8d201f6ee4258a4133e7f6554e21035f87190110004ff705963133e7e5159531004ff7654a31006f9601814102eef31588100067f4359410034fc70d8d1030ebc4059120036dc3058e200d6df3158e20004ff7558e20005bf7155142034fc7058a31036ec305881013dde73946400067e64d9530007d7634c510037bb745011002df47154310035fa708c540004fd72d91510067c4259410037e82048110007d5314c3100067e53d952000cfd75d81523ae7c40d95300067f65d85300067c7459410006df735913104efb7650210035f8704c610006ed7558a40036be405901000e7e6254a50006ef625493133d7f7654e511ee7e65d954102ed71058e510067f7559520004fd73d8152005ef725813126cfd74d913201cfc7458c100077b7054d50004bf745891000cfe76d89540057d7550d52024fc7558e2116d7e7354a50096f651d8550034fc76552301a67c5359621005f97094520014fe7358a404ccff73595322457e759853202e7d71594101f6be32d9121004fc764c52001e7e645515242ebe51d9121006bf6458d213167f6554a3000dfa728c120034fe768865018e7f5358a5102df67154f10036df3058630004ff7650a5005eec625891000cfe7258f100067f6550530034fe70d8954014fc73d8542007b4649451011dbc7250d40005df7348630036dd4058c10004ff705954206ebc6459110006df5258c10007d7714
  | 9 => 0xc7458a4021ebf40595410057f754c110007e9524c12000cbf7650a40006ed62546400b777545471006ebc43d9110036bc405921002edd31592312673f4355152015dc7350130005bf74585321d67c5059631007e53148520007f37148110005d57394510504ff7559542004ff7558a310367c5059620024fd73d8953034fc7059210007d7614c53001cfe74d8553007f370545101b6be64d9131004fd70d8d512c67e70d9510014fd74d9543006f9601815102ef81058251187ac6450921006ef7259132006de4258c10006bf64d8d1001cfd75d8154026f465545102167f7359631034fc7058e20006bd75d91210067c65d89102f67c5158650034fc764c640017db604c5300267e6554e40005f5758c51028cff72595420067f6354951014fe735931002e7e315963102df871482100347c765455000cfc72592311bedd73d953100cfe72d915113ede5358e40004fd73d8542004ff7654d410067f7459410004fd70d8542034fc7058a50005dd7318540036df7358e100047f7558d10004fd72d8d102c67f65985500079f735514301cfd75d8d5402dd47150d3105efa20582210367e50594103ae7e30d953000cfc72d8554006dd634c650265bc7458552006bf65509410267e6554d20005bd7550d4245e7c53d8553014fe76545311f6bc4258a41365fb7058d20007f13190110004ff7459521005e972901100067f755822101cfe7458a5154ebc41d8d54004fc7654d10034fe7694620034fe7654c1019ebf40592212f67e31d9510007e9524821017ddc7358121024fc7558d20004fe7650d2002ef71058e51014fd71d953102cfe76d85520c5ac7448520006bf6418121006bc651911002ef7624c52102cfe71d915300eee624ca1000ebc6250a40197d4534c621034fc7059531005bf744ca41004ff7359621005f67118153004fd72d814101ebc6455121004fd7654e40004fd70d8d212567c655093002e7c2159631066dc6358d1000eee6254a30014fe7358a41034fe76d8153006df5358c10006bf51d9121006fb6388110006f76198532006df7359130004ff715922000cfc72d8540034fc7654630285be74d8553026f66554510014fc73d855025ede63d8d5200cfc7258640556bc41d954302cfe71d9132006bd54d8943036bc7059220037f36190110004fe7650d512175c53545310157c7655153014fe73d89411bf5f534c55000cfc72586501e6bd4359231034fd72d952002cfc7650110006dd5458c1012e7f5259250006ed628c640007e92148110014fc73d9130126dc6358d40014fe7358810006dd6354c100075d535413001dbf7350e410267f615515101ef864901100267e6554c1016d7e7355250004ff7459510006bf64505310067f65185300567f54594100067d6554b100eeee32d89303473c415515101cfc74d8552
  | 10 => 0x85533a6fa30d815301ebf60505401b6bf405913102efa105931002cfc7654b1000cfc7259640006bc32d91102e77b10195100047f755863002ebc5159010036ef10588100067e735941001cfe74d953100e7c7654951004fd75d89100073f65d9110036df7358c10037f36150110006ec7158a40156df30d8d5000cfe7258c10006dd7258c1001ef86450110004fc76509510067c4259631007bb7050a4000778705455011eec625894054ddf735954302e7d7159631004ff72591302457c755813228f6f2055152014fc7359010034fc7650a1027f6f2054d521be7c50d953111dbe7250d40126bf435923002eef5158810005f77154110006be43d9121004ff7459630004ff7650d51014fc73d8951006dd7058e510267c6554521004ff7558a10004fd74d8152006de7458c10004fd75d81431b79f4250d3120cfd765452116f5c534c6500067d70596310bede63d8d20036ec5058a400f6bf42d91300267e6054a500debc435922002df7764c71001cfc74d8d511bedc5458e510fe7c5158e5002ef6618c650007ad4350921005bf744851027cfd75d953202df7734c521035fb745011007cff7158910004fe768c5401e6de43d8d410067c42d95105067f52d95420077b658811000cfc72d8d500067f65545102467c50d9532004fd72d814306ebf43582411cebf405923101cfe745822136dfb7059120014fe76d8d5000cfc73d89301773c415525002cfc7654a310273f7455152007d4614c530005bf7448630004fc765453001cbc7458910005f7754c51030ebc40d8142024fc75d8931006ec7358810006bf651912126cff7259132006fb705913000cff73d95320067e725963100cfe72d95201f7b421d9121006f5614c620004fd75d913100cfe76d89430067d72d951000cfc72d8d513ce7d75d815406ebc4258241006df5358e410ecff7258d200067d5458e50004fe7690550024fe755913201cff765061002ef910590101c6df32d8d210257f7354e51024fc75d894301cfe7459531004fd71d95200c6ef4358a4001cfe7458a3102cfc71595400067d545865002cfc7654310004fd74d8d1002df7758c510034fd72d8520006bd43d8940004fd70d8d520367e2059410004fd75d8520036f4105865000cfc72d9131296de43d8d54004ff7058a3121ebc40d915116e7e43d9530125de739454000cfe7259543037d83050130024fe7558a31174ff7559540006bd64505200b57c754c31002d7c76551511f6ef2058a41004ff7159530036f610586201d6dd53d8d5100feb604c920004ff7654d1002edc1058e5102cfc71d891042ebf10d9121006df735953000cfd71d8d21006bc53592200057f7155152006ed6250810024fe7558620036bd705901002ebe415931000cfc7259631075f97098550006bf525901001cfe76d9121136e
  | 11 => 0x2debe10d91104acff7359132036ee2058a4000cfc72d9541006f771591100f6be54591300067c6319510034fc7654a40006be52d911038dfb7059130034fe76552303bebe40d89401f6bc52d9121005f77155231006bd6590640004fd7650d210067f655453102cfe764cb1001ebf62551420076f6554920024fe76d9520014fc73d81213977b30195300067d54d8d5202ef6611852001ebe6450520004ff7159540106ee5258a3031e7c6055151004ff745952002fe7628c521014fd74d894300cfc72d854301cfc74d81212a7ba4250110156de53d8d5030ebf6450a10004fd7650a31004ff764c910006be4259010006bd715922002eee51588101d67f5459631035bc705514042ebe21d91210deed42d8940006ef6288530004ff75592310bfd8634c120034fe7058c10006ef73588102567e6550a3111ebc3259220005df7354931005dd744c9315167d54d9542014fe73582210cd7c7558520004ff7648550014fe73d8950036fb6188110006f561946402073c5055241004ff7558b1000cfe7258e4101cfe74d893002edf2158e5101ebc6490650005ef7250e2117fd7304c52102c7c76551511deef21d894103eee325881001cfc7459531024fe75d9121024fc75d912022edc3058e5100dec7250e211ee7c655053002df47154110034ed72d91200767f54d9510004ff7650a10005bf70509412567c6550910004fd764ca5100dee725452002e7c3159410034fc7058e5002edf7158e51004fd75d8d21036ee5058a40034fe7694630034fe764ca102afbb70d9110004fd74d8d514a5f771591510073f65551400067f65d893001cfd70d8d40226ee4258a51004ff735862005eef20d8910024fc75d9132034fd71d8910004fd7650a1002edc614c530006bf53590101467f51d9150004ff7558241015bc7655143036df5058c100fe7c52d9530007d5314c110005bf745454101cfc7458251024fe7558d21004fe7650910006bf745912002cfc7159120186bc644851000cfe725824100cfe7259531034fe7058e20007f13150110034fc7058a103975f31195302975f3055153004fd764cb1000cfc7258e500067d72596312067c53596410b5fb7058550004ff7558e10026bc7655142006bd6450610014fc73597100067d6554620034fe70d9531006bd6455010014fc7358a1039f5c3019530007b95450110034ff7459010476bc41d8d410067f658853015dbc74585500967f5359610006bd6454c10295de7398554036df2058c10036ec4058810036f862482100c6ef5458a400067f43d951001dbc7454940005df735013002ef6618c520024fc75d9131004fd764ca5002cfc7158a5101cff7650110004ff7654d210267c65945300067d6554e1018e7f51d952100cfe76d895100cff73d913226eec625894300cfc7259410004fd74d
  | 12 => 0xf64551520057f754ca500debf4159220036bf7459220156de63d8d5000cfc7258e40004fd764c6502975c73551531aeef21d893106ebe54d9110185bc7458d2100cfc74d89400c5ee744c92002cfc7688540007b4644c52119eed42d8941006dd6350a51026de6554d30006bf73592203ccff705954001cfe76d9152004fd75d894133e7c6154d5202e7c6154550015df7450d312773f5255143074fd765411031e7c6055153036be105922026eee62d894346ebf42d854316cff7559530034fc765062011ebe5259220037ba748811001efa6490110226ef2058a51024fc75d8d4001cfc74d895002c7d75d8d5120eec6258951004ff7458e5109eee4258b1012e7f52d954001cfc745862002e7f51582510bfda534c12002cfc7654f100c6ef42d9120004ff764c620035dc7054d30034fc7059521036f8634c2204b6bd42d9132004ff715952001cfe7459620007b4615054001ef87650110007af7448520036f41058610286be54d9153004fd70d8554005bf7550e410067c72d95100057d758c6500c6bf40d9120005f5739451000df8724c2200ce7f54d9520007d531885302e67f60195101c6dd32d8d212c67e20d951005fe84248110107e8428c12001cfc7654541004ff7650a51036ef7258a3000cfc72d853000cfe72595100067c65d8530006bf644c110034fe769464001cfc74d8520006be62d911002cff74d9541024fe75d8910004ff7259541004fd71d8940036fa6018142004fd70d91510567c53594103473d5155241004ff7650e51007b7648c5210067c6518530036ec7058810014fe7359541006bf644c510014fe7359121037eb6248210034fe70d95430367f75594100277b6054d5000cfe76d8941006bf6458d101cedd43d8d41005bf7454a4100efa62881100067d65543100267e6554e102167f435963106df974901101cebe648c62001dbf7350d420367e5059620007ad4248640006f96388110004ff7258231004ff7654a4011fac425012031e7f6555220007d8704c53002eed415881010ebc42592303176d6254a50024fe76d95310267c6554140004fd73d81540067e6419530007e77150921346bc6155143004fd74d952002cec76509211e6dc6358d4101cfc74d9532435f77159521014fd74d8143006bd65d91211f6bf32d91210367f505865016e7f32d9530004fd7690550036fb624c12002ff3609451006ebf41d9110346bf6455231004fc765494100eee624854002ef910588100047e7619510004ff7358b10034fc7655210004fc765512040df77158d21004ff7259230004ff76552310357e7054d5000cfd75d8d523d5fb7058950337b47150e410367f5058e5002efb70582311ee7c5059251006bf645013002cfc715922116e7d43d9530004ff70595210257f74551521be7c65595312c67c70d9510
  | 13 => 0x82510f6bc6459130004fd73d814200df6728c521014fe73d9121034fe70d8d54176bc42592503d67f51d81520067f75595320073d54906500067d75d8142415be76d912101e7e6455250005fb7250110015df724c9310267c6554f10005ef7254120004ff7059532004fe7655132014fc7359621004ff7654a10004ff715963001cfc7458d10037e820501201ee7c65505100257c7548650214fd765453109efa20d8121007eb704c920004fd7654a10014fc73d9541006bf65d911023dbc745853201cfe74d8132006dc7258c10034fe7058a5000eee6248640005df735812115ebf42d9150016dc634c55001cbc7458650014fc7654531036de3058e20036ee3058810024fd73d8153216dc53595311767d54d954011eef21591200f6bf4258e40024fe755923002edf5158e5100cfc7259630014fe73d95400075d5394530006f7715891002ede4158e51006bf6450d2101ebc6450e512c67c5058251004fd73d895126eee6250c100067e6319510004ff74588102157c735515100cfd74d9542036dc2058c100067f6454951034fc705964002eec2158a41024fe75582310b7745354710004fd72d9153015de7354530006bd6450d2000cfe72596401b6be5458e4102df47150310006dd6354e1001e7f765525012e7c51d95400debe5459220034fe76d8152006bc7458b10014fd75d8553004ff7458d210757c754c11002edf7358e412aebe71d91100c6be64d912002cfe7158e41004ff7258e10005bf745952102cf8764811021ebe64546202aebf70d911000cfc72596101afcc624c9310057f72551531ddec7258d4102cfe76d85430067c75589103a4ff705953002dfa7190110014fd71d89312973d5355143006bf7459131006ec3158a40004fc7650931036bd3059220006ed624ca50036bf50590100267e6554931006ef4258a500067c435941014eee52d89500057d758c620024fe75586300057f754c650006ec7259131005dd739855002edc7158e51004ff7258650026dc7654d30006ed7358a4002cff73d913102fd67394510035ec764c920034fe7655220006be75d91210077b754c2200bfcf314c920006bd644c620035fa7088640005bd7550e41005bd7418131004fe7650d10077775454510034fe70d8941004ff7058a510067d5458a50024fe7559010004ff72596310079d5450d310057f754c951004fd73d915000cfe72d8154007bb6448110004ff76552203af5e30d9530014fd75d815302cfc7690520036bf2059010004fd7654a41006bd6450b10186be7619121024fe7558a41005df73595200e6ed52d895039e7f631953002cfc768c52006ef541586400063c65d9110007cf634c9200057f7354550004fc7654520004fe764854002e7d5159251034fc70d9110014fd71d91311febd43d913120f6c62549510073
  | 14 => 0xcfd70d8d200057f755812108fbb415021000cfc72d8153006f96348210006bd54d8940004fc7655131036f71059610004fd7694540004ff7654810004ff7654e2102cff768c620004fd73d9110317787054a50004fd74d8931006bf6448110016f6634c7102dfb6619064011ebd52592200767c53d9510036fa60181410067d6555132004fd76552311fedf3058e41034fe7059230005bd749812101cfc74d9530006df6354d21006f77159510005ef714c920004fd74d8910024fc7558231005ed7218153006bf7459541006bd7259010006bd6450e10076f65158650034fe7650810034fc76506100efeb214c1202573c505514202cfe76d853221ebc645915101cfc7458a30286be64d915321ebc6454510007b86488110004fe76545201f6bd32d91212467c655953201cfe7458e51004fd73d855213cff7459130035fa7088540005bf744c640006ec5358a4002e7c315963101cfe74596210057f7154d5202ef67694510004fd71d954302edc2158c1000cfc72d855301efa645011000774654c510006de3258e51004fd74d8950007bb7055140004fd72d8d542973f5355143034fc7059250014fc73d95210067d7259410004bf7458b101a67c6588530004fd71d9153476be41d8d412673f405515202e7e7159410004ff7359410004fe765494102edf1058e510d6ed32d89300ce7f5159520037eb724811017edc6358d21004fd70d913100ebe6250941004ff765512000dee72d9120014dc7358910005df7250d3101ebc6450531006ef6248510004ff755922001fbb6050540024fc75592102ef7610195100057d74946500079d434c540006ef4258a10016dc638c5200067c3259410007b7648c51044ef631d8532006ee43588100debc4159220006bd54d8d42004fd75d913052e7f53d8954006ee7358810024fc75d854302ef6614c640034fd7059010005bf74486401be7e65d95311e6bf43592311b6bc645913102edd2158c100073d5454d4202cfe7158e5124dde7318542046de5358c10036df4058c10015dc7354130006ed624ca100067c6419510036df7058c100067d6555121007b77150e41034fe768c62007feb214821000cfc72d954002ef76094510176bf435925001cfe74d95103ae7e40d9530034fe70d8d41005bf7150d40004fd75d8142016de6354e1002cfe71d9152004fd73d95410c5ee744852000dbc7650d422467e65d95320167c6354d5016e7d32d9530006bf6454910036ed105881000ede624c93109eef2058b10004fc7654d40004ff7458a50007f231881103cefa40d8154005f970185420067f42d9530006dc4058e512f67c31d9510024fd72d8552037eb628c12002cfe7650e21024fe75d853002cfe71d912002fd7734c52100cfe72d911000cfc72d8151035fb7648210006df624c53002efb105
  | 15 => 0xf715913001ebe6450d20016fa634c22018e7c5058a510057f70551530057f7558530036bd4058e4001cfe74d8131004ff7655230004ff7654931004ff76486401aeee32d893101dbc745454102e7d3159410024fe76d953216edf3158e5002f776554710007776154550036bf30590100057f7558131004ff7654d4200c7c7654d52005bf7550d420067f7558d10014fc73d951000faf7450921004fd70d8543035f6708c510006ef3258810004fd7690530024fe75d8520004fd70d8d423cdfb7059540004fc7654910036dc3058e5000cfe72592510067f7559541024fe75d8d2000eee624c810516bf43d954212f3f52551400073d54509510067c43d9510004ff7358a41034fc7654610004ff76505200067f755952102df4714c3102557e751854202e7f41594100757e76d95102c67f659463003eec5258810036bd205922001cfe7458e20004fd74d8d5200cfe76d891033e7f6554e4100cfc75d895002ef6768c510007d9314c220014fc75d8d5002eee215881030ebe4059120034fc7650c1000cfc7259131036bc2059010024fc75d8141034fe7655210006be73d912141fae21191210067f65d913001ebc6450f10004fd73d912102edd4158e51024fe75d913148df77158951007b76454510004fd71d95420fe7f52d95302afb810d91100067f65d8d100c6ec4358a40425f7715912136eef21d81420367e1059410034fc7159310266be54d9152004ff7259531496df53d85530067e5259410006df7558c10006fb609815202dec7150921004fd73d954008fba5450210006be73590104fdbf74595420067f655013011ebe42d8940065f97098530036fa1058a4001cfe74597100067d73d9510014fc735822155ddf7359153455f77159131125de7318540006bd43d814202cff7688630024fe7558d20006bd6550a400267c65551200047f7559110006fb6098141014fc73d915200cfe72d913102cfe71d951002cfe7650f10216de53d8d51004fd764c6401aeef2058d2101cfc7458f1001cfe7459630005bf7454140036f41058620035f47054710007e5424c52101ebc64501200076f7255152066f5315863000cfe72d8d540057d759853202cfc7159251007f15188110035de704c53001ebe645063002df77654710036f610586304bdef725913202cfe71d8d5002ef6615463002cfc76553102167c7359631007ad54509210067c65d8930007777155151005f7714c3101f6bf42d912101e7c76551520367e70594100067e5358650036f7715862000dac7250d42005bf7355241034fd75d8d5002ede5158e51005ef715492020e7d5259621004fd75d8943005dd731815101ebc6450a501ee7f51d954100cfe7258d10004ff73592502ee7f6518550006ed6254a3016e7e5358e5001cfd72d8d420057f7355152014fe7359641
  | 16 => 0x515328eee42d8954014fc735922000df6724c521005bf7454640004fd74d9530004ff7650951014fc73d89402aebc71d9110004fd765521002cbc7650941077745354510004ff76506300075f6354d52005bf745895101cfe7458c1016e7f53d953000eee624861001cfe74d8d50004fd73d8910024fc755913002ebc415925102dde7150d31005f67694510024fc75d8d4200dee728c5200267c65945400073d5454d4001dbf755524102ddc7150d3102ef6618c620016de6354e200167c7654d5001e7c645515202edf3159231007746154550004fd71d8950006bf745865002cfe71596410257e75885504ceef20d8d520057d7588550036dc5058c102f67f70d9510136ec3258a4024edc6358d420067c32d95103767d75d8152005dd739463003efb7648210004fd70d9543186be5458a4101cbc745822100cfc7258e1002cfe76d8553004fe7654d4200778754c220006bc75d911002ebc2159010014fe73d854200cfe725963026dee7298143005bf7458520004ff7559130006dd7458c10006bf645891047ebf42d855402ede3158c10034fc764c61002cfc7690550004ff7459531004fd7690520034fc7058630034fd71d8d1002e7d5158a511f5be72552410067f6555130004fd7688650004fd7650d100067d7459410026bc765514339f5e3019530196de4358e2100cfc7259543015bc7355143014fc7650130024fd73d855302ef66118552006f56118550016bc7650d400067d6554a41036ea1058810036be4059210004fd74d8951454ff715913101cfc7458e511afe4724c5210079f6450d31005df7358950014fc73d91100fe7c51d95300067c74d953000dec725052102cfe71d9532005bf7458151007b8705514002eec2158a5100fe771485200247c7558241015dc734863000fcf734c920014bf7650e41036bf7059010036dc7058c10014fc73582511be7f5259531006bc755901000cfc72d9530146bd54d91500eedf3258e20006bf7459132126de63d8d40006be535901002ebd2159010024fe76d953024ede63d8d42004ff71592300057f75581431f6bf52d912101cbe76d91100276f725495120eee52d8951006ef7258d21014fc7359110005bf7355142006ed435881011cff725912001cfc74d815200cfc72582310067e5459410005dd7398554004fc7648550004fe764c52030fb87050a40266be64d91520ce7c53d952002ebf4158a411c6ee628c640004fd73d9120035f47654510004ff7559230034fe7059620024fc75d8930236be5459251005df735815200cfc72d91202757c755814300cfc7258d102f75e7394650296dc6358d540247c75591100367d3059410004fd70d9532024fc755923015ebc64591502167c435963102cfc768c55012e7f50d9540004ff705925105dec7258d10016f6638c521004f
  | 17 => 0x35bc7655140005bf7155140004fe765494001cbc7458d21004ff7558d20004ff72597100eeec62589300067e641951002ef661546202dfba1090640006ef7358a4006ebc54d9110004ff76552210057d7294650036ee40588102c67e10d9510005bd74181533473d6555241036ed3058a4045ef631d8553036ef7258a40004fd71d91203ae7f65181531aedf3258e2125edc30d8d5200cfe7258e401a6ed52d8951004ff7258f1033f765154f101c7e6428c52115cff74595402767c6550d10006bf63509410067d74d9530004ff7459530006bd64906200efea324c120004ff755912001cfd75d8554004fe7648550014fe7359521286bf42595430267e6094650004fe76885502c67f71d9510034ff705881000cfc725925149e7e51d8d510276f7254a5005df97098520006dc4258c10034ff705941002eec2158b1002ebf74592212167c32596310067e725941026eee42d894302edd5158c10176bf43d954002df7755451000cfc72d9531004fd764c81014eee62d8950004ff735912102eef7258b100257e7550a50034fe70d854202cfe71d8d520267c6555220024fe75d813200feb6048520004fd7650a510067d7359410034fe70d9121006f96018153004fd71d9152004ff7650b10004ff7359521016de634ca410267e6554e20005bf7458d2101cfe76d9120005fa769011002cff72d8d2100dec724c521004fd71d8d520079f6350d4202e7e5159710014fc73595400c6ef4158a400167f7654e5121ebc64545210077865901101ddee729814126dec725854301dbc744ca4102eed2159221006bf6454110036771059410034fc70596100067c72d9530006fb6348110034fd73d91300cd7e751852000cfe72d8d5002cfc764cb1002ede3158e4102ef66118553004ff7358a5006cfd7650110035fa7050a100a6de4358f10006bf53d9121016f8638c120036ee1058a40224ff7559521006ee7558a400067e42d95300fe7e7619530005dd754c530005bf7448540136ee5258a402debc10d9110034fc7650510005f97448110004ff755922102cfc7158e2033e7c515953131e7c6055152004ff7458a1020eee6254640034ff7358c1007fea3248210014fc7358910006bd73d912101ebf6050d4016e7d53d9530034fe70d85320257e7550951004ff76546300073d5450a50014fe73d815111fac4259120004ff765093051e7f54d8953006bf6450d5101cfe7458e10006fb6098153004ff7654940006bf6455121007d87054d3002cfe715963102cfc715964100dee7290520004ff725863002d7e7154951005f9708c520006bf6454d2102f76758c52142ebc51d91210257e754c5500e67f51d895000cfd73d95323ee7f53d815430dbf7050a4002df4715011002e7c415941012f3f5355140004ff75588101dcff72591212873f425
  | 18 => 0xd70d9510004fe765453026eef20d89430067c65d9130006bf21d911002df4714c11001cbe76d9121006ef7458810154ff7359530006bf65d91214c6bd43d9132014fe73596210267e6154e51004fd7654e100eeef20d893001cfc74d8530036f8645021002dfa714811022edf3258e51014fc73586200c6ec4158a400057f7454d52014fe73d9150006df5458c10175bc74486500077b65481100067f65d911012e7c6550130014fe73d8951006be42d9131004df73589100047d75d814202edd1058e51014fe7358b100fe7f50d953001cfc74d8951024fe76d95100bede43d8d2002ebe31590100debc545922024edf3159132036bc5059010006ec7358a40036bd5059220014fe73d9110004fc764c9412167d30596310cf6f515492002cdc764c931005f77148310106ef2158a30006bf31d91101fcff7459131035e87054920006ef32d89412debc30d9110005fa7688110004fd71d953200cfc764c12000cfe7258e500367c5059610005bd7418520006bd73590100a6df3258f1001cfc74d9510086de5358e10036fa10592200067e54d9510386fa30d81321567d5359630007755254710036dd305963002cfe7158e21034fe7654e1002e7d31596312f57f75886501bedc5258e512767e65d95431b79f4050d3110ebe54592301acff7258d210267e6554640024fd74d8d54006df644c53000d7e7255152035f4705451002fd4314c5210067f654c110004bf74595210067e62d9510004ff7058a4101cfc7458a10005f97090620006dc735952002dfa71502100247c755822125edf31d8d52006ed624c8102757e759854301fbb6050d402dfad62906400067d6555131006dd6350e21006bf745891033f5d6354e51005fb70545101279f3150d40036f51059610006bd70d911002ede2158e510f6bf40d91300367d2059410004fd764c6200eedd3258e200067d655481002e7f415963101cfc74588101f4ff74591210eeee42d893028eef20d8954024fc7558a300067f6558d1006ebe54582410247c7558e10014fe7359510006ef4258810006bf64d891002cfc7688530004fe765513128eee6255010016de6350e21024fe75591210067e52d9510027776154951005ef7348520014fe73d9510004fe769052002e7e1059631004ff7059131005f7714c110004fd70d8d5400dfa724c1201f6bc72d912106dbc7459510024fc75d85420267e655452027eee6254c10034fc765081022ede4358e51004fc7654d42004fd764ca41004fd71d8154017cf724c93100cfe72d8550006bd645512001eb86490110024ff7654110036bc1059220004ff764ca10006bf75d91100057f7154d50007af645092101cfe74d89530067f41d95100267f6254d52024fe7558b10004bf74595100c6ee5458a40006df4358c1010ebf415923000df4724c621
  | 19 => 0x63004ebf43590103cebf43d8154006f561946201457e758c640036ec2058a50007d7634c52100cfc72d8154006bc755922002cfe71d8d40206bd54d91512467c654c9100267c6555130017d76150d31014fe73d9521024fc75d8d410067f20d9530004fe7654d2001cfe7458d2000cfe7259530006bd54d814200cfe72d854002cfe7654b10014fe7359010036fb61481100267e655531011ebf215922002cfc7654e41035fa70946400067e52596310757c7558d102557e75d8142006bd64552101bedd5058e5106fb8425011000dee724c52002ef7624c710014fc7359250006dd7258e510067d655461002cfe71d9543004fd72d8550036ed405881005fea524811000dbe7255142004fd73d954201ebc6450d5104ebc4259010036de2058c100067d74d9510006f9601813202ebd5159010014fe76d8d201be7f50595310767c6559510007f0704c51001ebf6150941005ef7258d1002e7c7159410004ff7258d1002e7c41596311bedc654c530004fe7650950004fe7688530006ef525881001cfc74d9521006bc64d8d1002cfc71592502673c4155152006bf315922017fd4534c521036bc3059220016de634c3100057d75905502f67c41d9510067d4634c5102ef74101951002ebf415824112d7c7558d4011ebe4259120024fe755864002ef8105823101eee64509210075f7355153034fc764c810004fd769462020f6f2054951014fe73592201bddc754c9311adf5738c5210267c6555210004ff7558e4002ef6614c650005ed728c52001ebf60551400267f6355153024fc75d8d10036be7059010004fd7690620004ff7648630004ff764c951014fe73d8940035bc7650d4020eef20595210767f5458650036fa6018153107ea528c120006be63191210057f7558d4001cfe74d9521024fe75d81212aebc4158640035f6704c710034fc7654e4002cfc7688550417b7211912102e7f7559621004fd70d9541006dc7558c1002ef6315822111cfd7650120005f771551310057f7558132034dc764c530004fc765053000cfe7258e10005bd7550d4002eb9105901000cfc72d95433167f6554a10006be70d9121005bf75505400077865501101c7e7208c5210147c765515302cfc7159620024fc75d8d21024fc75d8d2000cfc72d9130034fc764c620006dd6350e510067f654c510036de5058c101f6bf20d9121007f25190110006dd6350f10495f77158d5127eef205953200cfd75d855202dbe7150941004fd7650810014fe76d8d522afbb10d9110024fc75d9130026bc765514002cfe71d8943004ff735954001cfc7458e21005fb70486100067c7558e1002df4715523131f3d645525050ebf43d8954006bd75d911001dbe7454e411567f5359630014fe73d891000cfc72595300067e53d9540004fd7694640006bd71d911002cf
  | 20 => 0x34ff73d9530004ff765053021cff74595410367d70594104b6bf42d9132006ef53588101467f515964011fae42d8940006dd634c64001cbe74d85530267e6554610034fc76486300277b60545504d67d52d95320367f75596400bedc6358d20004fc7650910006bc7458910005dd7394640004bd74d8553006bf51d911001ebe6450a31007f2515011002cfe7158810034fe70d8553004fd765463002cfc7159630066df30d8d10005ed721854012d7e758c540004ff7458e10004fd75d8542014fc7359310004fd74d8131034fe768863018e7f53d9521006ed545881045edf30d8553004ff745953202df7764c6210067f6548110005bf7458d100367c1059410156dc32d8d50005f97094640034ff705901000df8724c120004fe764c550006ed6248650006ed53588100ce7c655952000cfe72d915002fe7624c521035f87188110006dd6354e20006f96018143016df6150d3101ebe6455120036751059410035f8704c5100067f6554d21024fc7559010034fc7650a30004fd7650e20004fd74d8930014fc73d95300267f625515236ebe42d8142034fc71597100167c6354e51006bf5459010006bc63d9110024fe755922114cfd765412002eec515881002cfd7158810236bf42d9541004ff75592101b6be644c620006bf6455131004fd72d95310067f755953002e7e4159410035ed72d91200067c7059631006ef644852047cff7159541006be42d9151034fd74d85400067e72d95100067f74596312267f52d952100cfc7258e41006df6350d20007f0715011046ebf40d854301cfd70d9540016bc7650d4200eee624831001cfe7458b1001cfc74596301aedd3258e2102cfe71d9150006de7058e510edf9738c120024fc75d8142374ff7059520006ed6254a4000efa6248110034fc7654e10006bc745822102cfe7650b10034fc765501002ebe415925100777658c510006df7458e51006ef7558a40004ff7358640004fd7650b1014e7d5259620006bc72d91102979f315514302cfc7159621034fc705954101cfe74d95300b4ff70595100a7d6434c710035fa708c6200267e65549410067d6554a3100cfc7258c1002ddc714c931154fd7654130006f9634811001ebc6455310034ff7058c100c6bc6459120034fe7654810014fe73d8540006bf6450910106df32d8d20034fe70d8910036dd30586300165c6354d524bedf31d8943004ff7458a30004ff7650e10036f410586300067f71d953002ef8105822102cfe7159221004fd7694520024fe75d853201dbc744c640004fd74d8552037eb728c1200075f6554d3001dbf75551420047f755891006fbb435011017ede53d8d21004fd72d8d410067f65549100c5bc7458520006bf50d912146ef641d8543006be4259210014fc73595100fe7f5458e50006ed624c640004fd765
  | 21 => 0xf10592202aebe51d91100073d5450d5123dbe749813202edc3158e41006ed7158a401f6bc20d91210267e655523101cfe74d8d2001cfe74d893102fd431545310d5de7394620004fd75d8d42004fc7654940007755154310024fe75d91320067f73d951000c7f7654a5001cfe74d89510073d5454a4101cfc7459621006bf30d9121004ff7558640024fc75d912101ebc6490530006be32d9110007e9524811001cfc7654140004ff7648530006f561185520057d7518540007eb724c1201f6be6290640024fe75d81310077b7054a50007b7644c52102cff769063000def7554920006ed6248610007db7054d301279c6350d40017d7614c9310067f40d953001dbe74d8940006fb6098143004fd7654a40006bf5159220036be20590102567f5159542106ee3258a300067e74d95303157f7654a50006df4258e5116e7c73d953002eef7258a4102ebc4159221014fe7358640004ff7358910004ff7558c10004ff72593100067f654853030fad6250a402debf641814100eef604c920006bd5458e410a7d7324c710004ff745823102df871481100567c5459410034fe76d81540273f74551530ff5f5254d302773c5055143004fd71d894301dbc7454640234ff755954127eee52d8953007e9528c120006bc7459521027777154550006be74d855302d7c7154951014fe76d8d5100777655451000cfc725863001ebe645513200cfc72d8d402767f51d9543006dd634ca51024ff76543100aebf4259310035be705054001cff7650120294fd75d9543005f5754c71015ebf40d91500077b754c120005f7714811001cfe74595302debe70d911002e7e5159621024fe7559120176bf4159250034fe705922002dde714c93103eee425881002f75758c510077775394510006df73595430067e74596310267f6054d505267f54d8d523176f2054a500357e7054550034fc705922101f3f755524100ebf7650a401467f53d91503ae7c20d9530036fa769011016e7f30d953000cfc725971036cff7059120036ef2058620034bc7650540004ff7650650035fa709454002cfc765031000cfc72d8141034fe70d895302cfe71d89100d6df31d8930417ae7219121004fd73d9521024fc75d813212e7c6550110006dd634cb10036de3058e50004fd71d81430067f6454d500757c7558910036ec2058a1001cfc74d8910036be50590102aebf10d91101667d52d952030fba4050a102f77810d951000cfe76545210057d758c52002e7710596312ddbc7050e415167f54d9542014fc73d8540004fd70d8953364ff7058d20004ff725941002e7f75596310367e5059610026bc655514000775539451000d7c7254d5211ebd4259220155de7398550005bd74d85535367f51d9152014fc73d912152e7c50d8954004fd765491002edc3158c100073f6519110
  | 22 => 0x5241214ff73595311fedc5358e41004fd7655220036ef505881000cfc72d8d10007f13188110006df5358e21004fd7650c1001cfc745962001ebe645095102cfc71592312f57c7154a5001cfc745952007ef621d8520024fe75d854201ebc6455131014fe7654130004fd72d9530004ff7654e41006bd6494620007b864481102f67e41d9510046dc4358c10005fb7050610006bd64503100079f6350d40004fd72d8d4011ebe3259220006ef42d893102cfd73d913101cfe74586303b6fa40d814202ebc4159231034fc76486100067f6558910036ef7058810014dc7359520007b7715524116e7c5358e502aebd61906400777571195101bedf53d953142ebc21d912100dec725452100cfc72582512167e535953100dec724c120024fc7558d10006de7458e51006bc73d9121034ff7258810034fc7058c1002ede7158c10196ed32d8931036ec1058a4001cfc74d8131035f6704c51021dbe74181510067d535825131f3e6455250106dd32d8d2000dec72541201bedf5258e51014ff764c610006bc6458d102167c635455033d7f7154e5101cfe74595211b79c6450d31037f361881100267c6555110004ff7158a40005f97094540006be6219110034fe70d95320f6bc644c1100067c6219510004bf7458d210ff5c5154d3026eec21d8943026bc6555143006ed7358810024fc7559221014fe7359620006bf645051001cfe7459532035ee704c9200067c7459631004ff7058e51035f87050610004fd72d9110006bd6550d40005df73541300eeec21d8930186bc6459121007f23148110014fe7359251006ef7558810005fb714c22012e7f515954001dbf7350d400067e74594101b6bc644c510014fe76d8d54036fa6018132024fd71d8d5100cfc72d91510067e5459631004fd75d8d20024fc75d853002e7f2159410004fd70d895100cfc72d85502567c65595420d7db314c220005bf744c9400267c6554531006fb7059510186bf40d9121006df634c550296de53d8d54006be63d91100267c6554d100c6ee4158a40006be53d912102ede7158e51004ff745822102e7f31594102d6bf611911001ebe645061013ebf43d9130006bd74d85531f5be761912101cfe74d8121024fd74d8954006bc64d8d21036bf4058e40036bc4059220004fd73d895401dbe7454d42007d5434c710007e47150921024fe76d954000ef87648110024fc7559121006bd6550d420367c3059410006bc74595100ce7f5458a50346bc41595410077552545100067c75582210067c21d953002fb441505310077471549511bedd7558e5109dfb7058520046dc5358c10016fa634c1203ae7f73d95300057f7255151004fd7650e50006fb7059530176be545925002cfc7655231004fd70d89544a67f52d855400eee6250a31006f561185542773c6555143036b
  | 23 => 0x2eef2158221014fe7358a51036ec3058a4002ef66194640006f77159121004fd72d9131006bf6519110014fc7650531036ed2059620016df614c93120eef21d89511bede7558e5100cfe7259310016ec634c920007747155151004ff7650d212ffeb424821002cfd75d8151034fe70d9510006dc7458e510067d72d9530046dc3258c1011dbe72505400767c54d951015ebf4259640006be715922001c7f7655250067d6434c51000d7c7654d5247ef641d8554006df5358f1002cfe71d8954136ec42d91200257c754c6502467f545953205ef62158620004ff7158e40034fe705901001f3f7555142004fe768c550007d9314c1200cf6c655492000cfc72595401bedd5458e51004fd768c5504febf42d9152024fe7558e200057d758c55001cff7650521006fb7058910004ff735824100cfd73d8132034fe76550100067d6550810014fc735941018e7f545952142fae21d91210ff3e741953002cfc715881031e7c50d8154006bc71592200077b7054550004ff7458a310debf43d8940016df604c5302067f52d9151006ec7458810007e76148520016dc634c120004ef7259131006bd6450a5112f3c65551400073d5450e5002cfc71d8d101bf5f535513101cfe74d8d5101ebe645523002edc5158e51007b7644c51031d7f7655250004fd72d815102cfe71d9520014fe7358910006f631d81210ff5c6554d30014fe7358620036fa6018131006bc75d912106ebe76191100057f725525002e7c105963101ebc645093014cff7259520004fd764ca10004fe7650530007f15148110034dc7654d3001cfd75d8954007bb7050d40034fc7650e5000575758c5101b5be741813116e7f70d95301575c6354d5011ebc42d8940006f56118532006bd6450620004ff72595430c6ef4259120034fe70d95212873f4055153005dd7394540004ff7259210006f5611854301cfd72d9542024fc75d853201cff76591320c6ec5458a40015dc73549310067f65541100247c7558d2000cfe72d954102ebc3159010417af2019121016dc6354d2100cff7648610335bc715514300cbc76551422c67c10d95100767c535865001fbb6055140024ff765953211eee42d894001cbc7458d10004fd75d8930004ff7655132005df7354a30005dd739855201cfd70d8940006f960181522dfb610d911002cfc71591301767f54d95400767f5358251126de43d8d4000cfc72595100bddc7358520266be645481002e7e4159631004fd71d8d40006be75592200063c651911002ef910593100c5ec744c9201ee7c65595410167c6354d52336bc415913100dec724c620004fd72d8543004fd70d9531007f0714811000cfe7259231007d53148530024fc75d8143034f4764c510036ed5058a40336bf6450e210067e705963102cfc7158a41004fd72d8540345bf765
  | 24 => 0xc725911000cfe72596311aeee624c64001cfe74d8d2110edd43d8d400367c40594103176e6254a5002edf7358e21024fc755863001dbe7488540016f6634c521007b7715094102e7f315963101cfe74d8910036ee7058a4001cfc75d9150067d7324c51025ede635481031e7f65552301deec62589410c6bc64481102adbf748864004ebc43590100b67f5259710004ff725964002efb705824100778754c1202167c30596310c6bc41d9120036be3059220034fc7058a30004fd7654a31036bd40596401deee42d8941004fe764c91001cfc74d8532024fe75d8540006f56194630004ff764c94002dfa7188110006bc50d9121004fc764c550014fc73d81420067f21d951001cfc7458b1002d7e7155151197d6434c621004fc7654d41005f5754c5103967f601953002e7f7159410004ff7654b10004ff7558e41006ed6250a314b4ff7459132034fd72d8d200367f105941001edc7650d31014fc73d9150006de4258e51036ed2058e203b5fb7058940006be43d9110036fb628c1200067f31d9510006bf75590100057f7055151005ef754c920015be7355143004ff7650c100075d5454d30004fd74d8d212c67c30d95100067d6554d20556bf42d954354ebf42d8d54034fc7158f100277a6054a5011eef20d8940006fb7058d100bfe9324c120035de7054d3042ebe31d91210ce7f5359520006ec7558a40014fc74d8d40004fc7650d50006bd54d8143166ec4258a500067f655412031f3c5055140034fe70d8d42434ff7159521007b4648c5100267e6554630005df704c9312afb97090640034fe768c64034feb424c12001cfe7458a30006ed745881001ebc6490550004fe76885402767f525954301ebe6450b1001ebf635514340cff7158d2130dbc7050d42005be7619110024fe75d89410fe7c6559530006fb609812100cfd75d91521dfaf2150941136ef2158a40024fc7558e4110ebe54d8d40004fd7688640004fd70d912105eec32d891002cf8765011000fe76150921004fe7655130187af43509210367f75596303d67f53d8152077746594510004ff7359710024fd72d815247ebf40d85540067f65d89100067c6559110007d5324c7100067f72d951001cfc74594100067f7559542024fd71d915111dee721854002e7e51596413ae7e70d9530016de6354e40015df7554d3001ebc6450e21004ff7359610024fe76d954316e7e31d9530005fb704c610266bc64549101b5bc7458931266bc645915201cfe76d9131034fe70d91521d67c5459631004fd72d9510006bd6550e412debe30d911021f3f4255151004fc764c91002ebe6150540007e93248210024fc755891002efb105823113edf31d9130006ef3158a4002efb105822100cfe72d9120035fb7248110006bc53590100257e7550d5202cfd71594100067f74d9510
  | 25 => 0x451000eee6250b10004fd72d9540014bc7655143014ff764c5210067d6555310005bf7355140014fe7650531024fe75d8930006bc32590101773f425525001cfc745951002cfd74d814102cfc7158e5001cfc7458a51036ef4058810004ff7059132006ee5358810006bf7259010024ff76541304eebe54d8943004fd71d95400157c735515302ddc764c931024fc755881002ef4634c62102eed715881002cfe7158a51006bc52d9110015dc7355131036ec7058a400067f7558e1002e7c5159710004ff764ca41014fc7359221004ff765091011fae424854005eee62d891001ebe6450a51014fc73d8154036bd1059220096f551d8550004ff7654e40034fe7690650006de5458c100c6ed4258a4000edc624c931004fe7654540034fc7058d2101cfe74d95322f57f7590650035fb765021002ef6614c620024fc7558c1002cfc715953000ebe6250a40007b4645451000eee624ca50006bf6454521004fd75d8540034fe7650a1038cff70591300073d5454540034fc70d95101d67f52d8d510067f6554d41006be43592203af5f73d9530005bf7550d40024fc75d8131006de7558c10036dd7058c10346be4159541034fc7654c10226ef20d9521004ff7159250015dc735453146df77158d41006bf71592202dfae6290640034fc7058e21236bf40d9541036ef30588100a5fb7058530004fd7650e2102e7e515941001ebe60906402367d54d954100cfc72d814307eec4258a1000df4764c521006f77159131004fc764c540014fc7359520034fe769063002cfc7654a41286bf4059543014fe735921002edd7158c100fd7e7598530004ff745941025dde739855216e7f43d9530024fe7558d101bedd5358e51034fc764c650186be64d9121004fd70d95210067f74d9530024fe75d9110006df7359532006f56118540007d5434c510006df53d8d202cfb8101911016f5c73d95300067e32594101ee7f53d9541006dc735891002ebe415922102edf4158c1001cfe7459510215de73181510f5bc744853002cfc7158a3002ef4634c71030ebc60509414cedf32d8d52036ec205881016f7830d9530004ff7654520034fc7058620004fd74d81513379d6350e41014fc735962001cfc7458e20007b9415021023ebc645913202e7f215963101ebe6450d501afcf204c93102fe421545213b6ef42d81420067f6554530005bf745494028f3d5255142004fd76885500067c42d9530034fc705864018e7c6548530024fc7558a31034fe70d913108dbc744861002cfc7158a4001ebe64906200047f7558e10036de1058c1044df77158931035fa7090620014fc73d89500047f755824100c7c76551520ff5f5054d302f77b10d95100165e6354e51006de5258c10007755154110034fc7654e202debf6590640004ff76553101adee721813100cf
  | 26 => 0x6df7359132024fe7558241024ff76545310c6bf4359120024fd73d91531febf43d91311afe6424c521036d71058c10004ff755822100cfe7259250035ee7048520014fc73d815111ebf3259220016be6350d422debc4058241034fc7158b1002cfc7158a50006ef5158a4031f3e5055140004ff71595430fe7e65d9530006bf72d9110016be6350e41006bc64d8121006f56118520034fe7059640016ec764c92002cfe71d9540004fd7690630035fa704c620004ff7059543014fc73d89410767f51d951045df771595312afb8419011000cfc7258e5100cfe7650521004fd71d81522c77a709465012e7c53d954001ebe6450e100067d6550a3102edc4158c101bdde754c93111ebc425912000cfe7259110014fe7359410327d7534c710006bc6519121004fc7650d52006bc6458910004ff735951005feb2148110226ee5258a51036ef1058a4011ebc525922016c7e76195300067d54d8d51006bf54d9121007cf624c931036ec4058a40005ed72905200257f7254951004fd75d8940026f665945100367c705941006ebe64d911001f9f7350e410267e65548102debf64906301b6bc644c52102ebd4158a41004ff7650550004fd75d8131004ff7459621004fd70d89313ae7c70d95301bedf5058e51336be415913102ebe4159231004fd72d9541007e87054920007d5434c6210367f75596100067c63d951038efa30d8143035ec704c920006bf6450d10004fd70d8553005dd7390530034fe7058a30004ff7654941536bd54d91522175c5358d51004ff725864002f777554710004fd71d81421b6bc42d913100cfe725971001dbc7488640034fe76d8142004ff7654d200067f7559540004ff735962002df87150210034fd73d853001dbf7555143006ef7259120005df7354531107eb218c1201cebf42d8d411afd7324c62102cfc764c31028dee7298154004fd72d9543005bf7458552004fc76509301c6ee3258a310367c5059630024fc75d89410067f6550910007bb649011022edf30d953100cfe725954102eec215881000dec7250120035dc704c53001eec7650921016f4638c521004fc764c951034fc7650e20005ed7298154066fa3058231004fd75d8d4002cfd75d8951005f970905200d6de5358e2017ede63d8d2100cfc7259531006bf32d911000cfe72d9531034fc70d89100fe7f54d953002cfe71d894002eee7158810036ee2058a50005bf7458910004ff7654e20006df2058e5101cfc74d81510267e655462002e7d41594102aebe21d911001cfc745823100cfc765052102efa1058b10007eb6248110004ff7159132006f5628c5100167e6354d5000cfc72d95100073f65551431f6be72d912131d7f7055250026bc655524100cfd73d8532004fe7654d400267c6554a30034fc70592312c67f619465002fd5739
  | 27 => 0xc74595211be7f51d9531024fe75d8142036ef7258810004ff7158d2023ebe5459132034fe70d9151024fc755862028cfd75d95420067d5258650007bb64501102c777109465045edc53d85530c6ed4158a402f67c71d95100367d105941002df4715513108ebc425921012e7e65d9540005f97290110004fd73d9152004fd74d95320067e32d9510006bc7458630006bf7459130005bd74981520175f7554d301deef20d8941004fd7650a500067d6354a50004fd76551211f6bf71d91210167e6354e514cddf73595320057f7558d10004fe765493006fba5450110006f7628c510036fa6018151424ff715912100ebc62509410067d65549410367f755962004ebe5459010035f87048610034fc70596200cf6f5354920024fc75591201f6be20d912102cfc76483100067d71d9510034fc7058650004ff70596410275f7354d50014fc7654130004ff76551310063f65d9110186bc4058a41034fc7650a5013edf3158e40006be63d912141fac2119121186bf43d9121005fb705522027f6c7254d52036bf7459210034fc70592201f7b721d9121006bd70d9121036bd30590100067c40596310076d54549200267e6555132196df3058e210347c7654d500076d535492001cfe745825101cfe76d915100cfe72d8d41336bf6450f10005bf735054018e7c6548510006bd42586402175e53d8d5101cfc74d81322973f4355153027766154e510367e30594104fcff7459542034fc7059641004ff7258241005df7358520004fc765512101cfd71d9541004fd764ca40014fe7359540004fd71d953002ebd315901015ebc645411002cfe71d8d104f6be54d8d423c6fa40d8143007d5324c510004ff765493001cfe7458a1000eec624851001cfc7458a31004ff745865002cfc7650f100267e6055250006ed629464001ebc645095017fd4634c52102e7f10596310067d53d8950006dd6354810006dd7558c102c67c40d95100e67f53d89500067c7558d20006bd6450e201e6de63d8d41006be651912106fbb415011008cff7159110004ff7654d40036ee2058a10037db734c2201f4be7619121034fc765065002e7f715963101fba609064002cfe7159251026f46594510004ff7058e4102ebf71590103ae7e20d9530004ff7650810006df7258c10004ff76550100067d6554630036bc405923001ede6450d31006bf735901001ebc64906301be7f5459531136ee3258a40005bf7448650006f761985403167f6554a400e67f51596201bddc7550d311f5bc7255241034fd75d9150036dc3058e40004fd75d853028eec6258954335bf7650e41006be525901011ebe21592202f67f10d95100267f6154951036be1059010004fd70d8941004fe7650d50034fc7058e5102cfe7158a31004fd74d81323eefa50d8154014fe73d8550024fc7558a41
  | 28 => 0x9010014fe73d814202eec715881002ebe715901002dbc71509411d67f50d8d51006bf7459540064ff7358d10004ff7259530014fe73d9530014fe7359250156df31d8d50034fc7058a41397783019530035fa708c520006bd655094121ebc42d915102ee9105881002edd2158e51004fd73d8550006df4058e5102ef66118543004fd73d95100057f75585202c77610d9510034fe7650c10007e8704c92000cfe72d8d10014fe7359120004fe76505504a6f651d8554004fd70d894301dbe7190640006ef7259542014fe73d814120e7f525962130fae6250a40004fd75d854301ebc645522101ebe6050a4018eed5258a5102cff72d91213f67c50d91500067c64d95103b6bf43d814201cfd73d89431c4ff7358d21006bf73d91100c7af425052023ebf40d91322c7745094510005ef7250521004fc7650520004fd72d815402cfd70d8d1001fb7615094121ebf43d91511afd5324c621005bf745893102ebc415901006dbc7458910006bf745863000def71485200067c7558241006bf644c9100257f745515302ef81058241024fe755913022edf3058e51004fc7655132004ff764c81000efa6248210004fd7654620346bf64552210ce7e65d9520037b9644c220024fe75592100267c65545302c77561946500beed3258a3002ff3608c510034ff755941000cfe764c12001cfc7459610014fc73d8520004ff7458d1000df4724c521024fe75d89400a6df3058f1036ebc42d8142006bc64d891051def7258d52035f6709451001cfe7458e21006ef4258a3000cfe72d85530067f6550510026be655514002cfc7158a3116e7c31d9530004fd71d8153004ff71595421debd4259221004ff73592100147f7654e51006bf6490520024fe76d9541294ff73595430b67f5059710034fc7059251006bd6450630006bd65d9110036ec50588100257c754c951017db6054d300275f7354d52004fd7648650036bf74592302f779709465001cfc745863000eee6254a40006ee7158a40006f53158221004ff7359221006f7715954126faf2150d4230ebf6550a400067d53d815233f747154e5100eec62509302debc70d9110004ff764854002e7e515963142ebf6498542006dc2058e510067e63d951020cff72595210067d6454a50004fd74d8d2002eee31588102dfb410d91100fedd5358e5008ebf43592100257f7254a5015cfd7654140035f4708c5100067e4359410035f870546102167e325963100cfe725863000cfc7650120006f5618c640006bd7559010015de7394530006ef624811001cfd73d81431afe7204c52100cfe72d9540036dd2058c100067d54d8552036ba1059220007db704c5303e6fa50d8153004ff764cb100067d71d9530006f76198542005df744c93124ede43d8d4245cff7159531024fe75593102467f51d953201cf
  | 29 => 0x36f7715863002ede4158c10004fd7650a30036bd2059010036f71058c100c6ee4358a402c67e30d9510024fd70d9150004ff71596202b7d7534c510036be4059220006bf52d911005fea3248110006ef725952100def745092130ebf6450a300067d655522102cfe7158a41014fe73d8121007db634c120006bf64501100257c754ca50006bd645513047df77159541007d47150d3111ebf425922002f77755451053dbf74595433ae7f6598153034fd72d91201e4ff7359131004ff7654a4101ebc64552311f7ac72d91211b79e5450d3101dbf75551400bfcc634c9200c6ed72d9120006ef4358810004ff7654530006bc6498121006dd634c6100067f6454550035dc7654d30006bf64d8d210c5ee74549205067d52d9542036ed1058a4002ff36054510004fe765093002e7c51596210fd7c755893000cfe764c52100777654c51002e7f755964100cfc7259130004fc7654931034fe70d9132004fc7650d1022ede5358e5101cfe74586501aeec20d8931024ff7654140034bc765514049e7c51d8d51005ed7294520014fe73d8152006fb7059540006bc63191213975e73195300067f3259410005ef7259131014ff72d9532035fb74881100267c6554e21006bd6450a3101e7c6455151004ff7259251004ff7654620034fe7654e2002eed5158810004fd764c9100367e50596302f75d73946504f6dd43d8d42006be72d9110006fb70591200067e62d953011dbe7255140004ff73592510ecfd764c12011ebd325922016e7e73d9530005bf7458550006bf7458b10024fe75d913002cfd75d9151004ff7650d20006bc645812101dbf7150540006f76198553004ff74597100267e6554a410567c525941002cfe7654e2102cfd70d89101dfac62509413473f515524102cfe71d8d5402cfc7650a51036ee3058a4003eec425881018e7c50d95210267c6554a400067c75586303167c6054951024fc755931030dbf7650a4006ebf42d911002cfc7694540004ff73582511bede654c5300067f72d9530004ff7458630006df7358910006f5615464002edc2158e513c5fb7058d40004ff764c94100eef6048520035f87055220014fc7358a41007e7724c521107ea328c120006bc7458650016f4764c5100067f655452102e7f5159251014fe73d9130034fc764864001cfe74d815301ebe645081000d7c72551520f5bc7458530007b943502102cfbb1019110006bd64548100067f659452002e7e21594102debf6498540004fe7654d410aebf4059310026bf7655241024fc75d8540036f7715864002cfd72d8d21024fd74d8554004ff71595322c77771d9510005df7050d314aedf32d8d42004ff7158a30006bc7458d1002cfe76d85541b5bc74581311dcfd765052102cfe7158c10004fc765493042ebc31d91210257e7194650004ff755
  | 30 => 0xc70591324967f52d8553005f974881101467f53596400075f6354d50006ed6288640006bd73d9110036df7358e402167e4359631004ff715964002ebf745925101fba6050a40004ff7655110566bd54d915300ef86288110014fe7359520007786588110006ed624831000ebc7650941024fc7558b10034ec764852015e7d54596400267c655451001f9f7350d42186bc43d912100cfc7259310037bb7450210066dc32d8d1001cfe74d8152006bf755922002dfa7150110006bf745912101ebe645062000eec62549310bedf30d8d20037f361481100247c7559130386df31d81323157c7054d52005fb714c120036ee5058810036bd705922000cfc72d8131004fe764c950004fd7688630005f7735471001ebe64552100067f705963111ebf5259220007b8705054000feb60549200067f75589101f5be7250e410057f7548650004fd7650e51006bf70d912102e7d1059631006bc6319110024fe75d8d21004fd7654e2102e7c7159631034bc7650d400067e43d951002ef7608c5100077b705525002cfe71d8d20006bd6450931024fe75d8943004fd7694630036d51058c10036bc405925001cfc7458e5008ef641d854001e7c645525000cfe72d814302cfc7694520004fd7654810006ee7358a4025ddc73581523379c4150d312167c53595310067f655893000cfc7258241006bd4358a411f5bc7250e41016de634c610004ff76546400f6bc41d91300047f755913002ef63158b100067f6598530006bf73d9121006ef7258910034fc764c51001ebc6450910036dd5058c10026ee65549200267e6555131014fc7359641035fb764c22002cfe715962101ebc6450a3001cfe7654140005f9708c64042ebf72d912101dbc744c9400257f7154550005ef724c5210267e6555221004ff7558e21006ef545881002cfc7650e51004fd7654b100c7af42d9120004ff725901000cfd74d8542036dc1058c1016e7c43d95302afba4190110004ff715912002ede3158e210057e7619510004fe764c951004fc765055001cfe74d8532024fe7558f10034fe70d855401cfe745881001cfe74d855202ebd415824102cfe71594102f57c739465002f7465547100eeee62d8930014ff74d954302cff768c640004fd72d855300cfe72d8d2000cf4764c521236be6494620124fd7650130526dd53d8d5202cfe71d8143006fb705952015dbc7448550544ff7559543014fe7358a10036bf74592500076f6254951016f4638c510296de63d8d5400dec725052025f5c6354d52004fe7650d210bfdb314c120004fd7655130006bc53d91210057d75181310247e76d9530004fd75d813200eee6254a1001f3f75551430bdde7394520137af2150a400067d6550c10004fd71d89540067c7259410034fc7058e40014ff764c31000dee72945200267f6054550
  | 31 => 0x8d500cd7c7558d200067f4259410006f761985502573f515514221f3f40551510067f32d95100257e758c6500057f75581410067f65549405567d54d954301dbe7454d40024fe7558c1002cfc764c11000cff7648110004fd765062000cfe7259210004fd7650e10034fd7058c1001cfc74595320debe54d8940024fc75591323167c50595200767c52d9510035fb734c120556bf40d9543006bd6454e200067c7259631015de73d9531006bd64552200067d6554d40004ff7650e21006bd6450650005ed734852002edf7158c100367e40594100c6ed4358a40024fd72d8d5202cfd7158c10346bf645531001cfc7458a50004ff725961002ef76054510064fd764c1100267c6554d41005fb70485102567f5359542004ff74596105467f53d9543014fc7359610016f6638c51000def734c920006ef3258a40006bf75d9121036dc3058c103167c50d81522157c735495101ebe6150e41005df7355131014fc73592100067d54d8553006bc5159220416bf6119121006be42d911000cfc72d9520185bc7459521037e972901104addf735913202cfc7159230004ff764c540004fd72d9130007f13148110004fd75d9132004ff72591105467d53d95430067d6554d4200cfc72595412f67e21d9510034fe70d854302e7d4159631004fd74d953102df87648110024fe75d8d10007e921482100bddc7359520034ff72d9120014fe73d9541004fe765093102cfe71d9130004ff7359010035f4704c71001fb66150e4133e7c51d8553037e8204c1200073d5450d52005df7154d30036ee2058810024fe75d8931266bf40d9152004fd75d8532004ff73592201bedc5058e510c5be74185202dfba7090640036fa20586300267c6554e41166ee5258a50016be6350d40014fc735912100eee624863001dbe7454540006f96018154004fd765531016e7c32d9530006f761985520a7d7304c7100067d6554e40347b47155241035ee7054920006f5618c6502cebf6019110024fe7558a40034fc76485105367f53d915202ede3158f100073c65d911015ebe64d9150466f641d8542034fc7648650036bf4059640004ff7558d1002ebc6150540004fd74d8d50004bf74582210067f6454d520067e5359710006bc62d91100067f6559130005fb744821043fd7534c621006ec755881000cfe7258e5155e7f52d8d5402ede3158e51004ff764ca50006bf53d9110016bc6350d422aebc51d9110007bb70505400367d5058e50004fc76545402c776509451002eee2158a31034fe7059410006df7058e5102cfc7158e4024ede63508101f7af20d9121006ed6448520006bc70d91212167e3059631004ff7158e20006bf6454d10034fc7059230005f970886403473e6555241006dc5458c10026f4765451001cfe7458f10006bf6455110014fe7359710034f
  | 32 => 0xeee6248650014fe73d895404ebc5459010007f070545102d7b61019110004fd73d89401d67c5259631036f51058c10436ef20d8552006f77158d21336bc6150d420067e6219530034fe70d9153007b7649451002cfe71d9110004fd7654640014fc7358a40006bf7459110007d77150d3118d7c75581210067f6558530006df4358e51004ff705923102cfe71d8152006dd634c52016d7c7354a500067f41d9530036fa1059010034fe7654a1002cfc7650e2101cfd71d89410057f705495133d7c7155153005f970885400067d6554520006f960181210047f7558d202567e65508101ee7c50d954100cec7258d102573c6555142005f9708c540216df31d8d5102eec31588102167d435963101cfe76d91322c57d709465000dec725512000e7c6254951034fe70d8943034fe70d8931004fe769453000cfc725964102e7f5158a51004fd75d8931036fa6018121014fd70d913001ebc6450510065dc7358910336bc41d854301cfd73d854307eee5258a10004fe7650951036bc70590100e57e758c620036de3058e40035fa70946200357c7054550024fc75d81210067f6550d10004ff7558231034fe70d8552007f2518811002ef661946300debf41d894002eee614852001dbc7454a4100cfe7258650035ec70485200057d75d81424a6bd74d85543ae7e10d95300067e64d95100067d654c810014fe73d852002efb1058241004ff7650d10004fd71d8d42006bc73d911002ede614c530004fd76550100247e76d951002f75758c5211f6bc32d9121004fd7650910036bd5059010006df638c520036fa60181430067e52d9530006f531d81211ed7c755814101fb67190640004ff764c6502167e53d8d5102edd5158e51006df7358d1031f78705525011ebf72592201a67f505962100cfd73d913202cfc764ca51076f5515865000d7e7254d52036bc10590100073f6455151004fe76945401575f3054d50006dc4258e510275f7354e5154ebf40d8d54004fd768c650004fe769452000cfe76d893053cff74595432167f325963101cfc74d8d10236bf4259251006bf5359220004ff7654a3005df97288110004fd75d8d10004fd71d813201cfc74d8153086f631d853011fac4258940005bd7290640007e9214c12001ebe615524102cfc7650b10024fc7558f1002cfc7158e2102edf2158c1006cff74591100ff5f5454d303f67e50d915000cec7259131006f7619854302ebe415901002edd315823125f5f3054d5201cfc74d952000cfe76d89500077b6590110006f5611855301cfc74d9540036ea1058a4012e7f5359540006bd4358241004ff7655130004ff764ca40004ff7650a3105eef21d89102067f525964114eef20d8950034ff72d8d200076f7254d5200e7f7654a5002cff7159010187ae545092100dbc7255142006de32d
  | 33 => 0xe405923000dbe7250d42006bf6490530004fd73d852002fd7734c710007b76150540006ed624ca4000cfe72d95100067c41d95300267c6594630024fc755913102edf5158c10004fd74d815302cfc7648110004ff7059621034fd73d893002cdd73d95310057f7559110005f77354510076fa505825135dfa768c1204c6bf43d91320277a6094650155dc7358950004ff7358a511cebf40d8d4100eec6288530036bc30590102ddbd7090640036bf20592202175c5359531004ff75586304967f50d855302df7734c51002ebf3159010034fc76546400077b6550110005bd7494540036df7358e50024fc7558e2000cfd70d95200f6bc4158e40006ef7258d201bede5058e51056f7765471028faf2155142016de634c6500067f65545411aeec42d8931004fd74d812128f3f4255152007b95450210126bd4359230034fc70596311be5c654c53001cfe76545411b6bf41d9131006f76198520035f4704c510037e8624821015ebc41d9150006ec5358810024fc75d8940007eb70485202767c6559543034fc7650630004fd7655132005fa7018542034fe70d8d52014fe76d8d410c7af4250d2001ebe6450d52006be65d9110005bf744853001f3f75551402673c6455152007b94290110005ef7354920016de6350f10004fd765512001cbc7458b100067c6598530024fe75d8d400ceed5258a50034fd75d8950014fc73d952009cff705891002cfd75d8d51004ff7258c10016fa638c1200257e7590550004fd75d8121024ff7654541004fd7654c10024fe76d952100cfe725941015ebe54d9150186ed4258a410067f7359410006bf644c521006bf50d91100567f52594100367d405941000cf8764c12018e7c6559521006dd6350810007eb70549200067c62d9530004fc764c950007b4644c510006bc735922016ede5358e50007d4714c93102e7c515964102cff769462000cfd74d814201cfe7458d2121dbc745815100dbc7250d42004fd7654a30024fe75d8d410267e6554d4002ef66118550034fc764ca40004fc7654d2013ede4358e4002dbc765094120dee7218151035fa709052001cfc7458e10004ff7558a4006fb97019110074ff7559510005bf7448610005df7350531016de634c6201bedf5458e51004ff7258e41004fc7655130186bf41d912102cfc7158231004fd74d951001ebc64501300067e54d953007ef521d852021e7d5459641004ff735954140eef20d853200cfd71d91211bd7e7518131014fc7359542006be6319110006df634c51001cfd72d854200cfe72d954317eed3258a31004ff7458620004ff7158a5002cfe71590100167e6354d52006df634c110034fd74d8940014ff72d913200cff74d9542037b8645021048ef651d8552006bf20d9110004ff7650e2016d7e7619530005dd7318542004ff7358a40
  | 34 => 0x602b037002000a00101e804400001205d00844c0008000803401000700080080020020018070000003001045c0240f100f001824096d006008400a048001007400000c11ebe7259220006bf7458221006ed6250a5101cbc7459510036fb6150110136bd42d912023ebe64d9132006f5611854231e7f65552100067f42596310073d54549400b6fa50d8151006de3258c10035f8705051002cfe765522100cfd70d9120034fc705912100cfc765412002eef215922102edc3158e21005f771503102167d325963101ebe6450e201b6be54d9131004fd7650f10004ff76506202567e65d954202df47148310034ff71586103a5fb70595303de7c50d8950006bc6458d21006f76198554034fc7058e41004fd72d8d500067f75595100073f65551425667f52d9153014fe73d954200cfe76d8953006ed6254a10036fa1058810034ec7654920004fc7650d210067f725963111eec425912002df47148110035f8728c120004ff7654c100567f5359410034fc7654a100073f6455153016f6634c621036f81058610004ff765512102ef661185422adbc7150a40014fe73d95202167e6354550014fc7359251004fd70d8552004ff7458251067d7304c51016e7d31d9530094ff715951002cff768c65001cfe7459631034f4765451022edc53d95310067d6555010034fe70d8d210067f65549300067f654c91042ebe71d9121006ec435881001cfc74d85530c6bf4159120034fc764ca1052def7259152036dc4058c100067d6554c104c6df31d9132164ff755952022cff7559531024fe7558910005dd739462002ef66118532186be54d912106dbe76d91100067f42d9510004ff75586201eebd545925102e7e21596310057d758c64045e7d75d855306ebf4258640004fd74d8953015dc7354a30004ff7654540014fe73582511f6be52d9121004ff7650a3002cfe71d8953307ba42502100b77752547101deee62d894102e7c5159410004ff7558d213167e50595200067d54d895101ebe6450310126df30d8d40007d9534c22001faf7250941034fc7650e10006df73595200757c7559110034fd705881002cfe71d895002cff73d953133e7f6554f10007b87050d40004ff745963100eef61509210067c6558930005f9709462001ebe6450931036df1058c10006be73d91101f7ac429052000cfc765452100cfe72d8d5101cff73d9543006bc65d911005ef52158620006bc7259010036f71058e103157f7054a502c67e40d9510405f6768c521006bc7458d212c77410d9510034fc7058a51036bf5059220004fd73d9151036fb619011001cfc74d8550004fc764854002ebf21590100157e73551530067e75d814202cfe76553103379e4150d3101cfe74d81512ddbc70552410357c7054d50004ff765093102cfc7159542004ff7458910036b
  | 35 => 0x10022c0260000030080b7c07400d000806201b000142802400d00980040ce01d016000411a00401906a41d410000d801805e0790d5001810e00400180942080000000004000020055001000001e000004c010058092870001e014000003809c00d1e9804400c000000000c00400e0070c240d40020020070040001003800407e01000000343062af00201581120012ce000802401200080100280010278000010064000006820000203080880fa00f0110034000002005802000000900701d804200d0020004178008000800054a00f9b780b800000b01585a684a072001001000a0025d6000000c000000801000e0000a10094012000006007401000005084bc32c0a501900304980000000a5800800d010800808e3e9001802008806f001007816600313d80ac01001300400ac00003c0040174496004002805001800e004003008201b01d8130002011002805000403c00381bc00a037002833013c01400b0b5800002200a836405200900085e0004026007016005600200f006400400100e012c03c00801a000000c00000280080060000000050014ca7000002401a00103801f801019b00a839403400d02a30cc2644ca01200680400a000000a004204d11f00103a2018003000c00000302003b80e201b0048004000009001016401002500200080f20250018000000000012000c02200702d000000204007f000401c00a0000034000000004003800000100000001020140a481080020b200001d420600400100580820010440090038001303816805005b00080240000190160ca800200009c800003e008031801400400300400140a6001001001c006025004002000004e00000b400c29c0020000000000000000405400c00200340160000018018000009000010000c0001d6009400406401c000c00200b005802405204903385601e601e035801c03200500381b821a092048801003c006005005800c09f005005400200f028804000001801c81540c6033000001000a03e043005012202d000019c23803300f801800e000001806c074005001000804202800c801005a00c007000401e00100200140000000000000db200100080ac00a03c001090c00408d000000405c00400d80100000000050240002015000000c000012007000000000002f000000c001001001001e15e0038018000082004000400801c010000008e0071548020012004028000400402b000810800e012008800003c055004801801a0020102e64120003000001805600900780ec092000017800000012507d802832c00300080340e00ad0008030010116003000000e00500a0050016134016800006e00306d81fc03e04009200042da0c3000809017e000002803c01c16b00e00987f8011049808802003600c8030000001000000401204600700000006790018000
  | 36 => 0x40120d7000001400000c00001001e8000020029c006029000002c0040280028070054006000807034600a000000800e00c002800407000100581fc02800d00302cc006004016800402603f002000095e00d00280e0058044000800806800101300000400de0018000084004008022807c05b05e006c0e26610a300e400400002d801800772e01680241c6007057804400600c00180a80860d0000801c00200d00280200000000a381f811201c00c808c08a069032002401e006001800054003302a80c404000300d800044602400a0000002000004016414400300100c0124003000800000600100c800009c01e022113c05e0230000058000001004806404200701c000000e03404f8000134000052016800216000100000320170080038002061007801015403500001c8000000016038c02600001f00640ac0150020050432006018007400003000b001000002300a813804c0a50048b80e7e00c02880b425200401d803c1ca01200580281b800c00004780d0000023802802a0d700000d0034005000019000a0010f4011c02e14400300d012e011003002806200704b800c4460000160000000000005800000800e0008000026004000000801601400480e804000201800040486ae026803007e0041028014000000003069803200000080243000ad0010018024001002180000a00201e80bc2ee02c00281300541d2007000c01c000002800000400f06c000001201100100804f80e100208180640ad00686f40000110018000004019004002802c000002000c00c000005007c00016e04200001c6006008818400408100a805000a086005003405a02c000853001803602880080ca002014001400823600080f017400002a803001271a00280280b200e001019800000803480a4002006002800400a00401280003f8081001019400600300a80d803a01c02e80cc126002008801001400600080d800a00f01a00b0002009000825003c00705280d800c003002801800000c01500f400aa9f003800400800b00d82481a200d000009800c009006004c23c00100380001280150210004000000009802c15604301000040060720010000000013004002006000000181d00ae006006807c0000040000000116012034000803803a0bd802c01c04c0330014002014023806c10e02a0370020076011003054c00405e000000811c00f001801c04802f0060014000006007003c00200007e80a8254001000007c01c1a000580240f8000000001c00002b004800801c04101f0000026003002806000206800080180300000db801c00c002002813c01c006000000400001301c8024a7000402d800c00200600a002405201100c092800c013007cc2400000a000002c13000500801b4014006003807403205d000000000e055000002c00004600101f4000067
  | 37 => 0x90af8064014000006801c00011700c005c00a007b5e001803800002b803800000208c80000b4022000002403c00802a0058000000000002800c00500889a808e306010824800c0674170150008007000016005c00f00800b400c019001800002e783000005400800000a00200020010000004000003012c4e000000d00380b404e00100400540be003011001c0000410008018000005056003c004001000009409a52000200300180000028710016006000000406a00a02d0170046000015002413c006000000400000202900441b6009001808402c0070018128038040000828c02400f015800008a0280ae802c04c18700002a80da016004001c03e015000000c01000009d00200022d101180000180020000494004003019000000a00200000c000200a0508004044016050000003a00900c801400201411780000140771880168000042002000c008010002005c014002001003401201801401a401602800088e80f4002009000400000300a80280220a8002a08404000901400100501e4003007400018c0110368014003000800c002026047801411600a00000000560010001b5000c005008834002205802180ac066014000000c00c01100881280300060040bf000c042001013001802d00000040700120000b8800e05a011838c01200200202940241e203780080ee04208600c80ac00d332801431e00e03b00fc04202200b80042600e3001001407201b000009801600500600dc0060280130098000044002808407800501800240740010940000b1c0000c58ca00000210010000050020044800001200800e002c28202700800540021b8000a15800200000f8040014004001805c08e10f00e807c014097002801c00000107d000c00601c000000c2da00202b001804a035000802800000000c0134028001008800000000000b044803a1db00680300000010010008002004007002c02a0ec03980100b2018003800c018000010000002802d00f80c802600000300040ae01200101400c003300d816c01c008004801c07003e006001c03201900082bc06c01300080ac01c00000e00045d801000400dc00211b08c80e400a020000004000028a00082640300302c982102e202f00a80b808205b004811c0282a800080b400e002003001400200d02c80d001a10f00302c811600000000c800000100f8084008000004000002a004000002801c010001804400003700c0004000000000804c00201000c00e402604205f803801600b1298030078008010800000c00600f808000804604b0194002004000800000200003982c4000004009000431e00700103b006c043006001009c00000901e01961340028008000001006800400007608e806c16a00200b8038000010006800000e000010804003c000000142c036003007020000e00a000003
  | 38 => 0x1001600403c804c08c26700780e000200309a8004004007000825000802c002006401800200a800801400231e000400600a01200c008c00c00a010003201d0298001a9e047001001000000f0000010000004003006c3dc00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ee87dc9644c4015b300392c7288061fa1f65549400051f428e6b2020b3cd573d866154c014bb0a3a2c6080028f61320d95100045fc22e3b1aa400a3d8498c65440013d10ea92609001a7aa037250d200045ec3ea3b22200487e85dd9214c0050f90eb2aa6900030f1d365485100054ec20e4b1ca2038bc845c7654800d1dd0db92869001297219535493000656396c8b1a20008bf845d954440010fb0fa02cb1891697a147058e5100537428e6b102000c6c72195614c001938e7b22c09091697a147458e510061e32ee890a600087d87c81658c4090f90ab86c4a180a3720d765512002c7c432e128a8000bd1839452044001878cbba2c298016b5a047258e5100566c18e2b148000a6d851d162040051790eb228690002ad60450d912102c6e43ac6a1ca2028be87d914348447958e4b22869001a2f21d6455220005d8c20e0a8a2000c9e645ce518800717908bb4429800a2fa1f6450d510243f42eeca122000c3f65dd1214c001938e839ac4880021f61c43594102ac5f43e41b222003a3f86551439400d2e90ea8aa1880fb2b989729064016e2f39ecb28a600587e8794d65c40010fd0e32ac6880030fdd774589100355d404e6b244000aad841c5629000b9acc2b98c2900038bd5254588100051f42e41b2220038bc845c7655005b4bd0620eca98002f1e09434c621006f0b94a320220008bf845d953484090f90abb26488003171cf65589100054ec26a6b1c8200f495354930480014db0529eca901ca1f21d535825100656326e4b1a200295f8754e514c0030f90ab86c4a88023ee1d60181210061fba8e8b2a20018ee87dc9634400117f08bb442a80022fa1c535901000536c28e6b14800187c865d54354801c70ca32240880163e219744811034dd44224298240048bd84dd9548c40117f08bb286880169d205745963100657326e498c4004c3c7555160904b14f500196ca8820a6ba1f74485200243e42aed10c60008ef825d9434846f4bd0a212c7288028fe1171d95100045fc22e5b02a20087d8710b654400d1d90eb12a40801a37a1f4358c100045f43c84b048258c7476d95514400147b09396ca980163e219708c5200343f43ca8b28201bab9801c5648800193ec9b9ac090802b6a007258e512ad5b408ebb22200695c8754d504c001958e4322c68801a7521d314c3100053cc0065b2a20008fb875806050c031d904bb2868801a6e21d415021042c5e436e8b0242008f7875846150cb14f5003a6ca8800e4f21d5454a412dd5d400e5b2220058bc87591429440147b0b39ec89081a3b21d624ca500071a32ec928a2000c3d75592318800187ae83a6ca880de97215634c6100061f3b6ca3222000a3d8590b64544011df04bb2a68801af4201314c110005e5c1aa5182400087d851d931480070fb0bbb2a918002b96047358a40
  | 1 => 0xd06382cb18802ad60430d9121005f0c10e0a8a20008be8714b644400117b0e29ac91000387d525458c100045fc22eca922000caf741c9644c4017a30728a80880031b197725853000c3ec2eeca942000a6d82993654c001972c9b82a910003171d77358d2000657210ec90a8002ad48358a314400b1b90eb1a87880023de1d61185520043ec3865b2a205ea79801cb654400b1e902bb2a9188030f5d074d95300045fc22eca122000aad841cd62040031790cbaa86a1002ad60754d91100152f41ecaa9a2000e9463191314843155908b1241880034d5d4648c5100045fc22e3b2a6400c3c75d91604840117f08b86c49880e2fa1f7458d100143ec2eeca9c4200a3d851cd648800117f08bb2a5880030f1d474589100347743e64b102026aae841c5629000117f08bb263280021f6177650950005d8c20e098a2000a5d851c163944051790eb2a86a10122f21d64551200045ec20ec98a400487e87dd5608840b5ad03a9ac7880032e591708c6200051f42cc6322420487c855d932840018decbb92c29800e2f21172d81310046fc1aebb0a4000c9f74dcd624400717d09bb264880022fe117654d100347c402ecaa4400087d85dd9414c00b1f10cb8462a0003355cd61946200051e42ae1b224200caf64dc9634400d1d90eb12a5180028f61262195100071c320cb20220008f7875846154c0917d0fb22a8988030f5d475d911042c5fc22eca162000bc9821c1314c0018bee739eca880169da0420596310061ebace9b0aa653ba884485204400153b0732ec8908023de057650d2002c7c432e110a8000c3d76552419400d1790eb22a8080023be09764c9102f72a18eca98a2005cd6615ce51900b1ae6ea382a28801a2f21d6450c1002cba40aeaa12a2068ec87589320400117b0fa8ac9100028fa16621911000637ba8e4b1a200087e87195624c0050fb0bbb2a72080e3ba1f625093016e2f39ac728ca000ce9625c2219000147d09396ca98003179d953945300054f42640b1ca200de172546404400117b0e29ac80801a3ea037650a1001c5f43ee8b0c60018ec825da414c001caeca30a62980030fdd77458d100053cc04a7b2a400587c8759552c400d974e0b24a310003a518c644c51002c6f43ea6b1e200093d84dc553548070f90ab86c8a88021f6177650a10005e8c1ca320220048bc87591544c8b18e8edb2a62881672e1d864481100152e41acaa9a4000e3465191314400147b09396ca880022f61c52590100051f420e0b2c6200c5c75d8d304800717d09b8acb1000e1fa1f65551200c557420a6b1480008fb8758060508017c30438262880161f21d65545400045ec26eca9c4207ae5811cd62040030f90eb2aa4a08021fe15764ca100147a43ac498a2000a3d85cc764440018d8e5b2ac2980b69e60072d95300062e32ae710a6001
  | 2 => 0xd624ca102c63c386caa8a20598be86dc1425040117d0fa8ac9100021f61c42596310061eba4a9b2a200087f855d9544c00b4ed02192ca080022fe11764c9101bd2e42ac898a600487c855da214c0e70fd0db9aa2a80023de05765512003575400e6b148000a3e85cc764440014bb0ba02c7288173518573985540243f42eeca1a200087f855d9524400b5cd0239ac4080030f5d175d81420069abaec918a2000c3f75d91624400147908b8eca8801a3b21d624ca4003575404e2b148000a3e850c364484ab56d02196c8880022fe1d65191210051fc22e3b2a60059d687dc5434c40147b09316ca8801a2f213765081000574c00a2b1480008df835d95448001bc2e498c80880030f1d4745863001c5e422eca8c6000c3d75d53644840dbc6c2b9480880029d60432594100045fc22e5b02620087d87cc7654416387eebba2caa100e2f21170d89310045ec3e63b2242adda8425c241480014db05320ca980030fd0d75d81420045ec38a7b224200c9f741cd624400159d0638ac5200032bdca72d911003675b0ae520220068ec87589420400155b083aac408022b56047258c100243f42eeca0a6000c3c75dd1644400717908b8eca990030f5d475d91210251fc32a8a94820097587196314400d5d50038ac5200fa2fa1f31d91210043fc2ae7b0a80aee5453585319400717908bb2a4880063b2097654d100062f39ecb28a800487e87dd564440074790caa286a880237e0d76509102c43f43e63b2a2018aae84cc56290001878e9b2ac2980030fdd464589100045ec3e63b22200687c875955388001958e9b92c6908021f61776485300061fa96e8b0ca000a3e8598b64440090f90ab86c8908028fa12621951002cbac2ee6a8a2000ab5810cb644400b0f90cbaa84a8802f460e51881100054ec20a4b182000a5d83107654c0adaa8cab9ca28801a2fa1f545901000cd743ee4a1a8400c3d65dd152904014dd0a38ac5200121fe1d75d81420051ec24c7b2a2000c3c751d1608840d3d100baa42900028fa1263195100062fbaee6b122006aba80145648800147b0b318c8880022fe1171d953001c3e43acaaa26200e3864d9640440031790eb2a84a08062fa1f6450950004ddc3ec910220008bd849d9214c04735904ba262a00031bdd77258d100043ec28ec98a8000cac74589219400117b09bb2a6880021fe1d639465000c5ec26eca14a000c3f75d51640410b976c8b80c2a101a3b21d6254a100051f42865b22200087d87c83654c0030f90eb2aa4989572e1db64481102e43f436ea9822001aae82d91425410b97221ba2c5880021fe157650d2016c3f43e81b2a600087e87195624400787ce8aa6c2a90028f61072594102f63a38ecaa8220069b984dc940440098d8ecaa2a4900038e1946488110006563a2c490c207287e87d9530440854b
  | 3 => 0xc990200087f855d9324400b74902a12829080e1f617765521002d5b40864b20200087f855c76348001878c9baa60880062fa1f64509300346f43c64b1820008bf865ca419000147d0a392c80800237e0d7654a1001c5e422eca9a4200acd821c1639440717908bb243280029d21953945100353a432a2a8220069e887485204400117d0e286c8908de97a172058e510043f43ecab1a2000a9e841c963944eb0ff0abb2a7080163da06768c52042e563b6c8a1242008bd84dc56588001aaecab9ca28800a1fa1f6554d210051ec2640b2c6200a3e8498b654410b56f08b08c2a101774d8173945100055ac0864b2020008fb805d95348407179083b2848800a2f6137650f1001c5f43ee8b2a4200eca32d8d204400b5590ca1282908030f1d065589100c4d6422e690a4000aad8414d620400187eea322c0908023be097650f1001c5f420eca9a40068f48758531900011bf06bb264881572bc8774582210045fc22eca8c6000a9d841c9630400d1790eb22a9080161fa1e54596312c62f986eab0c6092d5773dc553944010fb0e21eca880028f61720d91100043fc2ae1b128600a3e8498f6544001878ebba2c4880022fa1f645891003d74c00e6b1020018bd84dd9428400117b0f906c888016b5a067058e510145e43acaa1a80008bd84dd953c400117d0e322c69081a1f21776548100061fbaee8b04420287e87d9553440090fd0bb82c918802a7a0c7159220006d8ba4a310220008bd870cb644400147d0a192c80800327193735891002e6bb02e728a2000a3e84cc7654400117d0e322c4880121f2157650d10007b0a92a290220008bd84dd932440754eb02382cb18803335cd62946400051f420e4b2c6200ad58108163944030fd0fb2aa49800237e0d76549100045ec3e62b244000a7980107654c0010ff0abb44298003355cd61946400062fba8e6b122000ad581101639440717908bb264880030fdd274594100051f428e6b244000a75819c9658c4010fb0bb82c5188121f21570d894100656c16e8b044255cb876d9140440bd0f90fb2a60880036add0704852000573408e6b14800687c87595539000d1ed03bb2a7880030f5d275d81420053741083b2a6000c6c751c9634400355f0ca12432001a3ba1f4258a10006373aac518c8075c7510dd5638400117b083b2a690016ad2056450520034f443aa51824000e5465d85314c0090f90ab86c8990121f21573d85400347a43ac298c4062b6880551524800d6b100a9aa0980063b2097650f1001e563b2a8a124200c3f65dd1614c0b18ba61baac3180030fdd47458d100061fbaea8b244000c3c75dd16344031958e9b2242900035a19572901100054ec20eab18205bcb870d91414400147d09906ca8801b2e9c1648c620005e8c18e2a022000a3e840c965040070fd0fb2aa88801a3b21
  | 4 => 0x44c40117d0e29ac9100121fa1f75582410243f42eeca1260038be87dd1654410b55b04386c8908030f1d47458d1016e3c3b6ea9824000aad841cd62900bb0fd0db8aa6a80021fa1f655913001c5f424ec90aa085ab6811cf64484010fd0fb2ac29821f9519531885300146f43ee6b2a4000c3c75d9130440011df04bb2868801a3721d6354e200243f42eeca142000c3c65dd1654400117d0e186c89081a1f21d655481000567410e0b1ca205ad48650d31c400d5d50018ac5200022fe11764cb100045fc22ed10c6000cd57358461480090f90a3b2a2980030fdd675590100061ebaea9b2220008bd8799464484010ff0abb284880063ea1b705512041e563b0e890a40058dc8758d31480010fd0e32ac29801a7521d314c11000d74412c71022005ad681101639440d0f90eb2aa6080022fa1f6458d210252e432a728a6042a5c8359551480ffca8ca98a42980023ee1d60181530243f43eeab1a4018aae84d4562900015730028ac9100030fd97745494001c5f43ee8b044206cba7059241880098e8ecaa2a28800f2e1d943501100061ebaa87b02840087d870c9650400717d09bb2a69081a3e2017654d210045ec38a5b222000e3465192314400d5b500392c6081d61f21b75585300243e42ae3b1a800087e87d95624c00195d05ba2c1108022fe11764865002e6b30ae728c405fba884485208400159b05a9ac710803e450d3150110004bcc06eaa1ca03eab5811cf64484011f70eb00c0989ca1fe1d53d81520051ec2065b2a20008bf845d9218c0b717d0fa8ec8880028f61262d95300051ec2cc7b22205b8bc86dd1624400117d0e322c09081b3a9817218131326aa3aa629862000d6b655ca40440011ef0eb08c2a80029b6174258a5016c3f43e41b2a6000ae9800c5629015f9d2e5b04c0a10030fdd46458d1000667312e728c80068be87909640400b0f90eb2aa2900031b1c86558d100045f438a7b222000a3d84988654c0018beea39aca900030f1977458d103aeadba8e0a9a605baba80909609047d95cc5ba243200036c5d1518811000c76412ec98ca0058de86dcd544c4010ff0ab86c89901a3ea03764c62001c5e422e3b1aa400a3e859cf644400147f0ab86c8908029760c70596310043f43865b2a200387d85dd954880010fd0fb2ac8880033a5c9601813102c6f43ea6b1c4200c9f64dcd62440018d8ebb92c68816ead60473d91100054f420a4b182075a7b855806054c0d0f90eb2aa7080030fdd254594104145f43ec890a205a8be86dc5435000199ce6b14a3200022fe1171d8d202d65a3b0c8a8a2000a9e839946448401878cbba24288003179cf659452000477c12ecaa26272c5e73194614c0015730139ac91001a3d21d61546300051f42ce5b2220068f686dc5204400147d08392ca080022f6137158e2003476416e
  | 5 => 0x8028f61731d912101c5e422e3b1aa006cea7058a21900011df04bb263280029e60032594100357540684b142000c3f74549619400d1dd0fa92c408002ab6107558a400061e3a6ca90a60058bc87591414800187ee92a2cb1881b6cd8574881100243e42aeca1c2000a6e8510d62040011bf06bb482900030f19774589100061e3a0cab1a203eaae82143644840717d09bb2a71080e2f211764cb102dd5ac08ebb22200087f855c3644c4014bd0a392c608002aba1053588100045f43e62b2440059d681dcd524c401d50c5b2240880022f613765491000e5739284b0c8000a5d851d1639440d5d50039ac4080123ba1f62549310070eaa6a6b1c82068dc865d5314c0018b8ebb9ac48801a3721d6350c100353d40064b282000a3e84c81658c4018d8e5b2ac6880021f61c425941002c3e43acaa946200c9d645ce51880010fd0e20eca980030fd977458d100051ec20e4b2c6200ab88650a40440090fd0fbaac4880061f6177654a300346e41eec9902000a3c855c3644410b97421ba2c588116b56047258e510346e43ac6a9c80028dc835da414800147b0b318c890802f160c6148520006d8ba26310220068bc865d543500b98f0ec32a40880121f21576486300061fbaec8b1a20008ef825d3604c40147b09906ca980171d985758c6400345f43c86b244000cba76d9240440010fd0e216ca88003179d7638c5200365db0ae91022000a5d8510963040054b906b2aa6a10128f21954549400043ec2eeca1a20008f787584615500147d0b39ec89080e2f21171d8d2022d2f428e4b1ca200a3d850c3644840147d0b318c8880021fe157650e100343e432ea98aa000b71858c6404405b4bd0610eca980176c1c541501100047dc3ac030264048de87d8d534840917b09bb2a9880030f5d574d85530061fb2ee890a2000ad48650d31440010fb0bbb2648800e2f21076485400043fc2aeca1a20038bf875d36154c010fd0e32ac888003271cf6458910005b8c2c62902200487e85dd932440b757500196c8880121fa1f7558630034dc402eaa1a8000ab9800cb64440054bd0db1aa6a90121f21576885405a63abaec330aa6028bd84dd943884051b906bb2848800e4f21d54549400243f43eeab1c2000a9d83143644840187eeb3aac910002a76107058e510346e43ac6a9c20028de87dcd62440e78b8ec32a6298002ab6135158a4001c5f420ec98a400087f855da41480014bb0a392c60816f2d1db64545100052ec1843b2a6000c9c64dcd60484010fb0e10eca98022b66007258c100061e3a6cab122000c3c75191624400b5a902b22629801a7a201754c9201bd2f42e80b1ca200b71851c5404400187eebb22608801a5d21d51541102d65a3b0c898a2000c3e645d631880010ff0abb2a6880031b1977258d100055643286a1242008fb805d95
  | 6 => 0x51ec2663b2a20008fb87580605480d1d90cb9a429001a3ba1b72551200346e43ac6a98200187e87d9552440bd0fd0f906ca8800a1fa1f6554d410054ec1cca3224200aae841d562040010fd0e32ac8980161fa1e53596210043fc2aed20c6000a9d831c5648800917d0fb22a8908031719573905300052ec2e40b1ca20087e870c965040018bb07baac318006aba0b6450910004dcc38c91022003aba86d92404407d958e5b22829098f5a1c154549202e63c3b0caa02205e87e87d03654400717d0fba2c588003b1ccb624c510034f543ee0a924005ad48650d318840717908bb2a68800a2fa1f6450d1001c5f426eca9a20038be84dd9524407d55d04186c8908022fa1f64581210345e426eca0c4004a7485586518c0031d904ba6c0988163721d634ca412ad5cc00e5b2220028dc835d9528400117f08b8eca900121fa1f7558d100045ec38a1b224275a7a801cb654c0015d10ca924088002ae60031592200046fc1aeca9a405c87e86dc1545440d6e100a8aa0880022fe1170d89512c53ac08e7b2a2000bc5831c542484018daeab1463200030fdd774586300355d40064b202005de071485204400195ee8392c6880021fa1c42596310249e43aa8a1ca000c3f75591419410517d0db8a86a1003271cc64589100146e41aebb0a400487c855d943480050f90eb2aa6a00033a58970946400053cc0043b2a6006aba800c564880016e30a38a4088002ab60871592200062e3a8e6b12200087e8710d650400d1790eb2284080028f61073594102f53cc00e9b2a2005ad6811c963040011ef0eb08c29801a6e21d41501100051ec2cc43222000c6e625d631900016e30b18a8088003785ca31901100045fc22eca1a4200c7575586318800153d083aac6080122f21d6455130335ca40aa8a1a6200a3e8598f644400147d0939eca880031bd977258d100043fc2aeca9a4000c3d65dd1519004d55d0839ac5200131d1d9525451002d6b40840b1ca20287d85dd953c404d5d30038ac5201ca1fa1b705515302c3e43acaaa442058f8865c2514800187eebba2ca880030f1d46458d100051ec2865b22205bcb476d913144001c72e0328c88800e2f21176486300046fc1aec90ca00087f855c362504014bb0a392c7288030f9d5648c6200356a432629822000ab9800c9640400b1f10cb8482900030f1d764589102d45f436e2aa28000aaf845c56290001938e6322c090a0b2b9c8641812100556c1061b224200acd82d4f634800153d08392c60800a2f6137650e510043fc2ae3b1a80058bc87591428c40d1e90eb0aa3200021fa1c42d95302f53b40ca6b0ca000c5e531d9514c00147d0810eca980121f21573d85200051ec24a6b2c8200fc1324c5204400195cc5ba2a3200022fe1171d8d500061fbaac8a1ca000d38655d2204400117f08bb2a89
  | 7 => 0x5d85109639440717d083b2a2900121f21476549100043fc2ae1b12620087e8794d61940d1b28e2aa286988028f61642592500045ec3cca3222000cac741c96344007970ecaa280880022f61c30d912101c5e422ed10ca000a3c845c7654c00187eea3a2c4880b7171cf65541300043fc2aed10a800487e87dd5644c00147d09906ca9800a2f21171d8d4001c5e422ed10aa0038be87dd1619400d1d90cbaa6490216ada0430d9121006563a2c490c6005ad6811c163944090f90abb4831800e6e21170886400063b3b6cb28a2075a5d831c7654c0018b8cbb9ac4880030fdd474582210045fc3aca3222000c3f75d91435440b3ab07baa628801a3d219754c51001c5f424ec90a600387e87d95544c0017a30638a40880066b2097550d420061fa1eeab048200f3154545404400b4ed02382cb1890b171cd65549311f65a3b6c898a4200a7581081658c40153d08382c7288030f1d065585300053742e62b148000a7581101658c4010fd0e10eca980021f61f40d95300045f438a7b224200a3d850c964040010fd0fb2ac4880021fa1f4059631006b4390ea98240058dc8758d32944090f90ab86c49880b179cd535825102c6e43ac6a1c4200bc9821c1534c0014dd04382cb188028fa1032d95103ae2e3b6ca98a6000e3970d9464440018eaeab0c63280030f5d254d95300243f428ec98a4000a3d8598b64440b7d5041b2240880171dd81758c510355d4422431824085da7741c542484019d2c4b8463200028fa166519110034f5406e4a0a4072c78761d5304800147d0b98ec890a16ada0450d91212f53b40865b2a2026aae841d562900011f70eb00c0a08038b5534258a500043fc2ae7b0a4000a75810cb6544001a76caba440880030f5d764905500345e43ac8aa46004c3e7555360508018eacbb8aa9188062f21170d89410162e39aa7b02a4008be87d916344007938ecaa286988032bdd37258d100345e43ac8a1c40008bf845da214c0010ff0abb2431800e2f21171d9530034f443a429042000a3f855c364440018b8eca9aa4980030f1d4645812102c6e432e89926200d94645ce514410717d0fb1282a02c32e5d360981420043f43887b2a20068bc865d1315000147b0a39ac8080030f1d76458d1000c5f43ec8a122000c3f65dd16244001878e9b2ac6880028f61731592200045f43864b202000c3f65dd150500014db0b98ac52000e2f21170d8951006d43a6e090a4000a3e849cb65440b90fd0db82a4a8802ab6133158a4000477c12ed20a6000b71858c6204406f8b8cbbaa62980021fe1576886300072a31eca98a20068f48758551880071bd0fb1a869000297a144258c100064f39ac928c400087d8710b654c0eb4f50020eca980029e60254d951002cd643a84a0a425ec7876d95204400d1bd0fa9ac6080029b61473588100
  | 8 => 0xabb283182172b1db74485200062fb2ee6b12200196c87551524800187ecaba4a2a00162f21d6450b100043ec3883b2a6005a76819c1658c40717d09b8ac7100022fe11768865002c3e43acaa948204c5c76551534c00b0f90b3b462a801a7a60b744811002c7643ac4a14a2058ec87589428c4010fd0f902cb188066b20b7150d420071a328c928a2000db1748c620440010fb0a3b28498a2f1718f7154d5202e3b30aeb18c4000a9d84c8163945051790ea12c32001a3ba1f42588100045f438a4b20205b8bc87d9121440014bf0ab82c72880a6721d5450d3102c7643ac890a4000c3f749d1658c4ab95ec8b90c2a000a3720d76486500051f42cc7b2242018bd84dd9428c00717908bb2a5880028fa17315922001c5f43ee8b1a42058dc87591314c0070f90eb2aa8908030fd4974d85530043ec2eeca126000c5c7319562440014db0a21ac4080028fa18651911001c5e422ec98ca00087d87c83654400d17d0f212c90801a3b21d6254a400045ec26eca9a4206ab8805d564880014db0420eca980130f9d554d81430061fbaa86b048206ae886549208400d17d0f21ac8080028f61273d951013574c00e6b1480048bd84dd9548840117b0fa8ec890a0b2d1d8644c5210143e42ae3b1aa0008bd849d921540019aae6b0ca3180122fa1f645511001c5f426eca9e2000a6e82990654c0011f70eb00c0a894f6a1917290110005e5c1a43182400487e85dc1628c43135908baa42900030fd9774545412c53d400e5b2a2000c3e7619464440ab95a43ba2c1108062f21d64509310243e42aed20a600493c8755143544b717d0f98ec888002a7a0e65d91211be2e32ae728a6000c5f655ce514c001878c9baac88801a3e201765513103675382c528c8005cb876505404400147b0929ecaa000a1f21d6554d42006cbb22e728a2000aad8414d629000b4ed03392cb188028f61472590100063abaac318c800087d85dd9428c00b8ecc2bac63280028f61673d91100062f41eeab0c6000ad48650d31484edb56e5b8285200023de1d61185402f53b408e7b2a2000ccc764c931480eb8ee21baac70801a2fa1f545922000537414c9b2a6006aba809c5648800bae6c0bac62880028f610705963101e1e3a2a8b0ca075c77655c46054c011ef0eb08c2900121fa14764c5400243f428eca1262059d4815d1324c40187eebb22c09081a9721953541300061e3aee8b04425ec7876d9540440014dd0a39ac5200022fa1c32d91100346e43ac69902005ad681d8d315400d1d905bb24320003171d5634c3100043fc2ae1b22420087d87d03654400b0f90eb2aa98801a1fa1e525941000c3ec2eeca94800487c855d942440073590ea12432001a2f21975505400355d400e2b244000a3e851c56488001c6b02328c888002ab60850d91210047dc3ac0302a800a
  | 9 => 0x3c00f2860180381b00e0ac040381ca0280903802c03c1c0000a42680002c00a04c00009000124010025c84300086800a000068100260640180001000816012012030000010020302013a0000100000200a0cc3b84003002c0080f0000500780d01a0409000f006034140250b600c0300004000c0180306412c0f00600210c0f80d0000a01d00400a010a781d00a1640008601e0a4d200000000c0480100002cb80010260147c824000a002204c00c05c148100400080c82a000008020110020541700a0005f80800f03e0040380000800c0083e0880100004304605c0100a0e400c100001340a40880105a0bc0001c0260900080d0f00001904108a0040b0f90eb2aa9189d7171db6554d300052f428e8b182018cac7458921900011ef0eb08c29916b6cdd071501100043fc2aeca0c60008f787584615080147b0a38ac9100029b6147158a4000536c10e0b2c620487c855da414800147b0b396c88800333dcc7258d1002c7643ac4a1620058dc8758d32c400117b0e29ec8880173a1d9214811000557420e6b1020058dc839da514c00187eebba2c88801a1f21d65550102ee3a3b0ca98a2000c3f751d1618c00d9d4e0b146320003e150d424c5210051ec2cc7b224206ce8605ca605500b9acc2b9ca3180032bdd9424864000d56412c8a1262008bd870c964040051b906bb2a48800a3da1b71551310061e3b2a8a8a80038be87dd162440adaa8ea98a60881572d1c7645011011d57410e2b24400087e871096504001d8ec498c429801a2f21d6450e500051ec2043b2a6000a3d840c965040b18becab98c0a88129da1b659451001e563b286a12420087d85dc1648c40117b083b2a29001a3d21d614c65002c7a40aeca1a400487e85dd9428c08b5ab02382c7288028fa1262195300043ec2eeca122000a3e8498b654c001b56c8b948088002a7a0c50d91210045ec26eca9a82068bc875914384001938e9b9ac4880029d60653d95100061e3aee8b0c603e8be87d4764484e54bd0db2a62980039a18865481100066ab9ec330aa800cac64dc931484019d2e5b04c0aa0121f21570d91312ad5b408e7b222003c3e745536154cb10f90dbaac4880de97215634c5205961fbaee8b2a86068ec865d5214800b1e902bb2a8900032e591709462001c5e422e5b02a2828be86dc55450801c6b0232ec888003331cf725891001c5e422ed10c60018f88758d20440db55904a1ec0a10121f21571d8d200051f420e6b282075a7a80087654c00d5d50028ac5200025de1f658c510006563a6e4b1a200087f855d954440014dd0a3a2c40800317d977354130007e098a42982400687e8794d65040b517d0dba242880021fe15769053002d3b40880b2c62008be8719163440031d904bb2a8988032b98b744c6400065cb22e120c400387c87595544c8090f9
  | 10 => 0x1f10209002c01b9e0020601b80f00e0006983a00e00c010020120000380002a004760000520461b0000840440180301200c0200b00a0400000000600c0b83f00c0001000500000c1703d2c00140303b0020780003800000008824010dcc2f8000485cc0901138e0180780b5ea1e9e78bd02c000078660906942100e0042fc000080020540002b00000c000be0740000003c0d002801803320158180020140000680f0160000780001801001800010000030000000f0010070160100d0520200045484c0080ec052580000841180a32e3740700002c0000f002008004038050081500b01c01c024248d300a000018052760009c0010020080e80812407aa303800a0440408400000c0f801002030538bc000004388110044142200106400c06812002000190004540dc0082900001c010000863687f98f0025341b8040020000e01800239c11014002110000ff69c068008000040a40000902802c1f80000e004190030780000613c1f8004000040000741e80e00e11c0286002a0080580802408c0027c01a0200582c042
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40000210802394172627654e514c001961855ca31901104142b263765092190001c286419572901100064c615748c620440018398719464881100065221d535493048001c146519173945100067060d72946404400143597194648c510006645d18394620440016849650d424c521
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
  | 15 => 0x124b
  | 16 => 0x124c
  | 17 => 0x124d
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
  | 32 => 0x12cb
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xa0b
  | 36 => 0xa0c
  | 37 => 0xa0e
  | 38 => 0x130b
  | 39 => 0x130c
  | 40 => 0x130e
  | 41 => 0xa4b
  | 42 => 0xa4c
  | 43 => 0xa4d
  | 44 => 0x134b
  | 45 => 0x134c
  | 46 => 0x134d
  | 47 => 0xb0c
  | 48 => 0xb0d
  | 49 => 0xb0e
  | 50 => 0x140c
  | 51 => 0x140d
  | 52 => 0x140e
  | 53 => 0xb4b
  | 54 => 0xb4d
  | 55 => 0xb4e
  | 56 => 0x144b
  | 57 => 0x144d
  | 58 => 0x144e
  | 59 => 0xb8b
  | 60 => 0xb8c
  | 61 => 0xb8e
  | 62 => 0x148b
  | 63 => 0x148c
  | 64 => 0x148e
  | 65 => 0xbcb
  | 66 => 0xbcc
  | 67 => 0xbcd
  | 68 => 0x14cb
  | 69 => 0x14cc
  | 70 => 0x14cd
  | 71 => 0xccd
  | 72 => 0xcce
  | 73 => 0xd0c
  | 74 => 0xd0e
  | 75 => 0xd4c
  | 76 => 0xd4d
  | 77 => 0xe8b
  | 78 => 0xe8e
  | 79 => 0xecb
  | 80 => 0xecd
  | 81 => 0x104b
  | 82 => 0x104c
  | 83 => 0x98955
  | 84 => 0xa0953
  | 85 => 0x130a
  | 86 => 0xb4956
  | 87 => 0xbc954
  | 88 => 0x14c9
  | 89 => 0x10a
  | 90 => 0x289
  | 91 => 0x1489
  | 92 => 0x14a
  | 93 => 0x2c9
  | 94 => 0x134a
  | 95 => 0x99255
  | 96 => 0xa1253
  | 97 => 0xd09
  | 98 => 0xd49
  | 99 => 0x1049
  | 100 => 0xb5396
  | 101 => 0xbd394
  | 102 => 0xe8a
  | 103 => 0xeca
  | 104 => 0x104a
  | 105 => 0x9c995
  | 106 => 0x12c995
  | 107 => 0xcb
  | 108 => 0x168b
  | 109 => 0x180b
  | 110 => 0x198b
  | 111 => 0x8c
  | 112 => 0x150c
  | 113 => 0x180c
  | 114 => 0x14c
  | 115 => 0x5c9
  | 116 => 0x198c
  | 117 => 0x17c9
  | 118 => 0x150d
  | 119 => 0x1889
  | 120 => 0x168d
  | 121 => 0x198d
  | 122 => 0x150e
  | 123 => 0x1a09
  | 124 => 0x168e
  | 125 => 0x180e
  | 126 => 0x1a89
  | 127 => 0xb4b16
  | 128 => 0x24b
  | 129 => 0x16cb
  | 130 => 0x28b
  | 131 => 0x40a
  | 132 => 0x184b
  | 133 => 0x160a
  | 134 => 0x19cb
  | 135 => 0xb5416
  | 136 => 0x20c
  | 137 => 0x154c
  | 138 => 0x184c
  | 139 => 0x19cc
  | 140 => 0x154d
  | 141 => 0x16cd
  | 142 => 0x18ca
  | 143 => 0x19cd
  | 144 => 0x194a
  | 145 => 0x154e
  | 146 => 0x16ce
  | 147 => 0x1a4a
  | 148 => 0x184e
  | 149 => 0x18cb
  | 150 => 0x178b
  | 151 => 0x188c
  | 152 => 0x160c
  | 153 => 0x1a4b
  | 154 => 0x17cb
  | 155 => 0x1a0c
  | 156 => 0x164c
  | 157 => 0x170d
  | 158 => 0x15cd
  | 159 => 0x1a8b
  | 160 => 0x194b
  | 161 => 0x1a0d
  | 162 => 0x164d
  | 163 => 0x170e
  | 164 => 0x15ce
  | 165 => 0x188e
  | 166 => 0x160e
  | 167 => 0x1a8c
  | 168 => 0x194c
  | 169 => 0x1a4d
  | 170 => 0x17cd
  | 171 => 0x18ce
  | 172 => 0x178e
  | 173 => 0x94995
  | 174 => 0x94b56
  | 175 => 0x150995
  | 176 => 0x180a13
  | 177 => 0x1a9953
  | 178 => 0x1a9954
  | 179 => 0x16cb56
  | 180 => 0x19cbd4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2263
  | 6 => 5962
  | 5 => 1354
  | 4 => 12
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/761+packedAt gbK7 (83731+(h % 761)*12) 12) % 2263)
  | 6 => 2*((h/1987+packedAt gbK6 (286176+(h % 1987)*13) 13) % 5962)
  | 5 => 2*((h/472+packedAt gbK5 (79886+(h % 472)*11) 11) % 1354)
  | 4 => 2*((h/11+packedAt gbK4 (840+(h % 11)*4) 4) % 12)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf0fffc78387f0fe031c07ff81f14c13e1bc4f3
  | 1 => 0x7f0e03803f87f0fffe00703fff2b0ec864789f
  | 2 => 0x7ff003ffc007ff003fff803fe0cc30f1878f1c
  | 3 => 0x800003fffff800003fffffc000f03f01f80fe0
  | 4 => 0x3ffffffffffc000000000ffc001fff000
  | 5 => 0xfffffc00000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x90121818100b0121104112884a00401209c431
  | 1 => 0x2104208008801048a202211294010648201886
  | 2 => 0x5aa0492a4005aa02149500a5424c10b0868518
  | 3 => 0x82c4ad500004a92a4d0084b02b01700ac0
  | 4 => 0x88113773666cc97000c060108fec001df6000
  | 5 => 0x6cc9e006044088180030080610ffbdec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36328
namespace PEqualNP.Outside.L_meta_36328
open PEqualNP.Outside.L_meta_36328.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 4 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 66 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 42 := bs4_5_0
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
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 6 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 66 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 42 := bs5_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 12 := bgb_4_0
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
theorem bgb_5_1344 : Interval gbAtlas 5 1344 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1354 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat (concat bgb_5_672 bgb_5_768) (concat bgb_5_864 bgb_5_960)) (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 bgb_5_1344))))
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
theorem bgb_6_5472 : Interval gbAtlas 6 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5962 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat (concat bgb_6_672 bgb_6_768) (concat bgb_6_864 bgb_6_960)) (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 bgb_6_1344)))) (concat (concat (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 bgb_6_1728)) (concat (concat bgb_6_1824 bgb_6_1920) (concat bgb_6_2016 bgb_6_2112))) (concat (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 bgb_6_2496)) (concat (concat bgb_6_2592 bgb_6_2688) (concat bgb_6_2784 bgb_6_2880))))) (concat (concat (concat (concat (concat bgb_6_2976 bgb_6_3072) (concat bgb_6_3168 bgb_6_3264)) (concat (concat bgb_6_3360 bgb_6_3456) (concat bgb_6_3552 bgb_6_3648))) (concat (concat (concat bgb_6_3744 bgb_6_3840) (concat bgb_6_3936 bgb_6_4032)) (concat (concat bgb_6_4128 bgb_6_4224) (concat bgb_6_4320 bgb_6_4416)))) (concat (concat (concat (concat bgb_6_4512 bgb_6_4608) (concat bgb_6_4704 bgb_6_4800)) (concat (concat bgb_6_4896 bgb_6_4992) (concat bgb_6_5088 bgb_6_5184))) (concat (concat (concat bgb_6_5280 bgb_6_5376) (concat bgb_6_5472 bgb_6_5568)) (concat (concat bgb_6_5664 bgb_6_5760) (concat bgb_6_5856 bgb_6_5952))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 55 := block_range (n:=55) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2263 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat bgb_7_864 (concat bgb_7_960 bgb_7_1056)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344)) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632))) (concat (concat bgb_7_1728 (concat bgb_7_1824 bgb_7_1920)) (concat bgb_7_2016 (concat bgb_7_2112 bgb_7_2208)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8feeefeeafeecfac8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276943560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36328.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩,⟨.and,[0,2]⟩,⟨.and,[0,5]⟩,⟨.or,[1,8]⟩,⟨.or,[3,9]⟩,⟨.or,[4,6]⟩,⟨.or,[0,2]⟩,⟨.or,[1,7]⟩,⟨.and,[10,12]⟩,⟨.and,[11,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36328

open PEqualNP.Outside.L_meta_36328 in
theorem PEqualNP.Outside.L_meta_36328 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
