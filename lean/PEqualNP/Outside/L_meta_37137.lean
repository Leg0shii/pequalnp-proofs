import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37137.Model
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


end PEqualNP.Outside.L_meta_37137.Model

namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
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

def SBf (j : Nat) : Nat := [6, 5, 7, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37137

namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x19030000000000001408020000000458071a2a048038001e000018000005000bf43de43bd43dd439d43be42bc42de32dc32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x51c001812c4000101440598040c00147552438e292871f5150e38a0a1c754c428faa4651d540ca3aa7a0c7553318eaa2631d531023ea9184755030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x200098086983548ca0c625513186181544c60e62d5230
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (302+((h/5+packedAt s0K4 (272+(h % 5)*6) 6) % 40)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 22)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffff81ffff83fc1fffc1fff83ffe07e79f3f3
  | 2 => 0xe0ffffe0fffffffe07ffe0fffc1fffff9e3c7f
  | 3 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x421888c428905040594c09498129212c28d1b1
  | 2 => 0x882111024122208a0291209224124a50922446
  | 3 => 0x444a22481a440314a8265204ca409505454a98
  | 4 => 0x96b3c4929076b5e734c318c7739c0619f80f60
  | 5 => 0x18c3871ce38739f9c73b9ce063181861ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37137
namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xd830
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (17+((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfff80ff01fff00f83fffffe03e07ff803ff27c
  | 2 => 0x3ffffffffffffffc0fc03ffffffffffc63fff
  | 3 => 0x3ffffffe07fffffff0003fffff81ffff83f8f
  | 4 => 0xfc000fffff8000fffffffc003fffe000ffc3f0
  | 5 => 0xfffff000000000ffffffffffc0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x184a6311c51235380b2cd4e60e433c861af23c
  | 2 => 0xa910a522482450514055412a528e492a4614d5
  | 3 => 0x52614a448348a4aa95029254a5511654b82b0a
  | 4 => 0x63458c89120ec6cce69b181839e58418ed43e0
  | 5 => 0x83860f0e1c70f8f738e3e39f01861860f7bc00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37137
namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc00f8f0200d290000280008800028840090008c27007918e1aa80104874c8700300250800411504ce1b06ad315005800a402c9002e04f28300200208328e080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xaaa8060068006c0000000830165c0000000000000000002c5e000000384e000090000078004cae708c8600621c50323a00120044008858660c004a64348a00009e003c0000ac00a2b40000a68e007a00007c7e005294000056000060480000009a18366a5a200a006e9c04549600001a243e40001000000022002a001e820046b200a4b6768474720000b000982e00000026020000a0148000420e922800010d0601000402110000040007000903020000000e000400000701010201b7a92876c5250f3a8621d7d4d42ae29a853f544ca78a8995b94b41b6a96835f53506b8a6a0dbd4941b6292837b50506f0a0a0d794c41aea98836e52cc6daa598cfd51319e2a2636f524c6d8a498ded4131bc282633e540c67aa818cf952219eaa4435e53886baa710eb95221d6aa443ce538879aa710db94621b6a84436e51087cca210db54021af29e815d53d02bca7205754e40b7294816d52902dca4205b548409f2a6613d54cc27ca9184f55230b7294616d528c2dca4185b54830b728e416d528827ea8904f15120afa9a415c53482eea2905d14520d7aa241ac544839ea6907314d20f3a8a416c51483c8a2905914520f5a82416e52082dea5885b14b10b7294216d52843c843084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087908410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2000a6e40000800c20a31894310f0e5494e21c315053483275414520c915051483475314520d114c51482656508410
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2724+((h/30+packedAt s2K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xff81fff81fffffe07fffff03ff03fffe7f8e3f
  | 1 => 0x3fffffffffffffff81f01fffffffffff88ffff
  | 3 => 0x3ffe03ffe03f81fffe001ffc1ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffe0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x84a42888c48928601652a52125213954338615
  | 1 => 0x110851110912408580a40a464a4642a88838ea
  | 3 => 0xa6149aa243a42b6aaa0a93a913a91c0d70d34c
  | 4 => 0x3459634492074db34d3cc0c21cf38831dd03b0
  | 5 => 0x386183871c3871dc71cf1cf380c210c1eeec00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaacc88cc888888eeaacc88cc888888eeaacc88cc888888eeaacc88cc888888eeaacc88cc888888eeaacc88cc888888eeaacc88cc888888eeaacc88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37137
namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x180700c010240502d444004010a0be43bc43bf42bd42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x83040008e29a852d52d06b0a098cb54840
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (212+((h/4+packedAt s3K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s3K3 (112+((h/1+packedAt s3K3 (108+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffc0ffffc0ff07ffffc0ff83ffe07e7f33f3
  | 1 => 0xffffff07fffffff81f03fffffc1fffff91fc7f
  | 2 => 0xf81ffff81fff07ffe003ff07ffe1ff81e1cf9c
  | 4 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x90c44621448941016524c8498123212c2711b1
  | 1 => 0x21088812091082280a41119224144a50906446
  | 2 => 0x52551240d2284d52a0a26a44cb419505618a98
  | 4 => 0x659a249483b2969cd3c8308772980619da0f60
  | 5 => 0x861c38e71c3ce7e71cf3bce063111861fdf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8e8e8c8c8eaeac8c8e8e8c8c8eaeac8c8e8e8c8c8eaeac8c8e8e8c8c8eaeac8c8e8e8c8c8eaeac8c8e8e8c8c8eaeac8c8e8e8c8c8eaeac8c8e8e8c8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37137
namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xa964018a011d0000d20051be43bc43bf42bd42be41bc41bf40bd40fa20f920fb10f810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x100c109ca80871c5350a3ca720da54810
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ff81f07ff0fe1f07c3c3fc7c0ff07f913673
  | 1 => 0xfffffe007fffffe007ffffff800ffffe1ff87f
  | 2 => 0xf81fffff83ff07fff803fc1ffff0ff81e1cf9c
  | 3 => 0x1ffffffc0007fffffc001fffff0001fe0fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x50d88c4c98a9c607c160e32c6469912d911631
  | 1 => 0x21011021214000600285045080822650066846
  | 2 => 0x124a24840a084a89480269052920c904a18298
  | 3 => 0xa59449284062953294e8021a52cc02195a0d60
  | 5 => 0xc61871ce738ce7dce733b38063088c61fdf000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfcc8fcc8f8c8f8c8fcc8fcc8f8c8f8c8fcc8fcc8f8c8f8c8fcc8fcc8f8c8f8c8fcc8fcc8f8c8f8c8fcc8fcc8f8c8f8c8fcc8fcc8f8c8f8c8fcc8fcc8f8c8f8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37137
namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fd20461f9408c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f480987e50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53482fea2905f14520f790a41ed21483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c43f461887e4c310fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f680087e10010fd18021f930043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198fe94331bd286637d50cc7f2a198de54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f710d31bfa92637c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621fb18c43f531887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487ec6290fd4c521fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087de4210fd88421f690843f521086fca010fe94021bd28
  | 2 => 0x200001f000121000a08f48000ec0e00023c19c6f4baa5d0f6794768003640c4000003d0000000110002080000041034047000000458001302aa0000023f27c0012b0000000c0fa8c21bc040668004e86e0c38ac33205000000000000000002028e4000190007800006845c1e51980014c83c000000e0000001480003c800018334000311604983b8000000000000000025a00124a1a4682b49c0d53f000000000000000eb800000888c6058350000440001365b8ff07e2121fc8700000023c0000000000000252196000000000004d4a78f70000ac88800000000f8a8500070400000170000dd00040a0b80023d00005c6287d4be429480ec2ac4a4931a0000039418000da3cc000002bc0011a859230000d980027651c001e6250000001af01a00000000000000921a40000000000018c000650004da00000000000001008000003582a1230000004a17e3ec779360000001e000000438204021401069082205a48685cfe8c40000006d8ff3de750000a303846d3b80c0eaa00d60000000000017a3a200111869000300778002a0000c9a7d418000d11b6338091490000007ac00000264000378230c21c4178000003500027b1a6000001100007e80013110c9147b00000000073800306590000004e600000104000000001f0114000000000000010f0000002d4e0000084000caa001f000000000000000fb800000000a490020c13800000000000000000000180080080000000400800000000008000000000000500000000803002014010020100040080100200400000004004008000000000000000000000800002014000000020040000500000000000000000008010000000000100000400001000000020000000000380d002000000030000140080400000000803002010000000020000280100e0000100200a004008000000040080100e0000000200000c0100500200000801000018018030000000000200001c0000000600000800008008000050000000000000200c0200000e01400004000000008000020040000200000c020000040000080300000002000000000000010000040280000000c0000a010004000010040080000000200400000002000008020000180000000000000001000018000000020100100000600000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x2f4000000ee00000026000054538730000009e80000000000000000000000000000004205033c000d70004ae0009c800322000002670006a8cb000000a5000000428818000000005146e1dc000000000001e20011d0004d200000000000001039412d200000000000000000000000005e0000009d461800000000fd8912b6000000000000000000038800060800000530000000009e4000000002a4290001ba0000016d0005380020e0007e40000042045c000001d4000ca19715c000000000003a01f8000106040000031400c002372c60014600000094400096516000000000cc27c000000000005893a000000e425052a93518a384fc000f70000002540011916e9046d048000684a12664dc00000000000000002250000007f000000000bc8000000012c000514178001bf000000cf80a000000001740000000000043200114000508000000570000000000029a290000001328a8029800262a8d48b226c390000f5000880002210001a8000740000000005d0b889c23000000470260cc00000104800000001438df0363446c0005100000016b04a0003d28f2a2000cc0002ae8c0000003aa73c000410001c87a0000006f800000000001430000007480000016c11c0024600000000218458068001520000000000000007d2d8c90005f5200370005d8c3000000158001a70000000000031e1005f007092a58000093080000026f49c000000000ca70c000b40000000025419000095800494000301c22b80000000000080c000001f4000000000000ed3e0000000000000015e394000004080009f800000000000000002140011e0002840000000000000000000000000000000000027110e00000000000001241fc000000000000006ec781df4160e8000000507b0b38000000000000011a0011200000041416a7f1122800011d000000f917300000000000000000a304300000000000000a45408340008f80026249617c000000002cd3200000038cbe0000000000000000000000255000000000000000011480043e0005591f3c200000000000261341ed1ae78cff8eb00057c15000000129069b0000000001e20a600000000000698c4800000000b6000000000009823b0448001580000014689e0008d8000000000000021536e2a0000000000e400000000000000001f871832055000000000002a6000289b50000000010f0000010b0004b41b0001ad4f040800000000000b900018e000bfa2f25e000a18004d400000000000434ed00012076c0018d000a4c0028900024c000002160000000000000000000218488701084bc0000000049e3a400063000000000920000000000033a00122000000000000002280000012c00000003067000844000000003f410a70000000ee8003d40000027a0007cc000970660000580000
  | 4 => 0x2ec972590000000021b08a0000018b000584929031f29c9298d20006f0529ca3100000000003c5e0eb0d906c00000000000000000000000000020a0008acbd80007a0000e83c26e0001a9702de0000000000049cd2a61000000e28020000000013300000000000000638001150002700000000000000159000000da0122cc468000000963ed130e22b4724b28000000000013429600083a6b000000001ce000000001540000002d9772d4528f20000004a80026352e9711d8004048490e99045a000c90ba0000000000017e000000000000013b0001180000000039a0001495d278000001b913491c0021300074c000000000000000000000000000000000000b0000000e80003460000000000000000000044000a219b000000001680000000000014479c26a3207c13c40113000000000004c0000000000004800009d000000000272e22e400185398000d88000000000786b1c20c80000019e0001628e00099400000000000e5800000000459f40dc398b11d902c71c000000006ac00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2434c25c6550d30c7152324c29d640c930c7150324c2d5610c930b6980324c29d64cc530c7153314c2da60cc530c7151314c354514c530ce152404c39a43901309e195404c39943501308f596540c23e64150309798c540c27a6015030c7553300c339548c03097d95300c31d544c0309ed95300c339544c0308f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20ba18121c825e63d52209758f548833860552209798c548825d63152208f993538823d64d4e20c7952538831d5494e20d6982538831e5454e20c7551538823e6414e208f590538833954d0220b658c4088339548c220ae1913088339544c220d694d30882ba64c822097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d208f990534823d6414d208f990514823d64145209798c514825d63145209e99740482d963101209e19530482b8644c120ba18930482ba64c81209e983540825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f59053082766114c209d584530827a6014c208f992520823d64948208fd91510823c64544208f992500823d64940209798e500825d63940209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108f99253c423d6494f108fd9152c423c6454b1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b10b658c40c42b8644c310ae99320c425e63152109758c548423f6454e108f191538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6494a108f592528423e64951109ed81544423e65151108f992534423d6494d109e582534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524427b60549109e996204433854881109e19520443385448110ce153104425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530435a6094c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810da181520423e64148108f590520425e63148109758c520426e62148109e980520433954d0010da54b40042796510010b658c400436952100109e5963004339548c010da54a30042b8644c010ce551300435a534c010da549300427965c8010ae993200436952c80109e594200436952080109e596100436952840109dd95100427b6544010ae19110043695244010
  | 1 => 0x65d6314141d698c50507596314141ce90c50507384314141ced0850507394214141ce904505063f6550c4197d8d521065c63548418f59642106ba60908418fd9541106b860504419dd95411067a60d53319e58354cc71c63553319e98054cc6796015331c755343cc6d96010f31a719132cc73a5494331ce55250cc73a5454331ce55150cc71e548ca31c7950328c6d5610ca31c7953318c66f62551319b189544c67b60551319e181544c65e65d0d31b6580434c63e64149318f590524c67a60149319e580524c65e65cc931a7191324c69e648c5318f990504c63d64141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c65d658c831b5584320c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c67a60d53219e58354c865f63553219718d54c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c863e64943218f59250c865e63943219758e50c865e63d52219758f548867b60552219e181548863e64d4e218f593538863e6494e218f592538867a6094e219e582538863f64542218f191508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c715053487556114d21d514e3148674654c521ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c504875853141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219d984530867a6014c219e580530875553884219bd9521086776548421d554d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b2154021da485500865f6354b409718d52d02ba6090b409798e51d025d6394740ae18141d02b96010e40a718d429029e63906408f99743502ba60909408f994425023e65d0540ae181415023d6590c40c754e431031d5310c40ae580431031d53d08408fd95421029c6350840c754d421023d6590440a798e411031d5390440c754c411031d53d0040d654e401023f6550040c754d401027b6550040d654d401027661d53309d58754cc23f6454b308f19152cc29d640cb30b558432cc23e64947308f59251cc29d64cc7309b98b548c26d62d52308f992528c23d6494a308fd91518c23c64546308f992544c23e6515130c758c544c3396015130c715
  | 2 => 0xc42e48d0000e6000bf16e1cc0c43d80027a450d89a53e2768ba800000000298001ba0000000000078d070213963f40016734c000658003ba2cc7d0001da6a8211410005dc000000006e000000000000000001d04a0000650000008a800000000171e41be0900c99a3e80e897000150038001971f20000010038a6b8548af1384305b07c3fe5e491a1801e4d4ec00012c4bc6a0f3410000000002f80c09c8c31e80010180000061416a0a00015c001172f0004000003783bc9f01c00026400020000000d00822a8560000f10004287b1f22566540000007c3143f04f10a0002080000045800186064000c5a142bc6e8018aa0b2048480b8398308529f01c27acdd8770d03a40b92a39e3003706c0de2b823133090688b41702207e0b48ff1880100502002000000100200801004090000600c0a00403004010040d00002000000100504404004020801200c210000503c0d00035000020340201001004090000000c0101c0d020170000002000000000040206403000070000000005048140240001400004030040103c0600c01004040080200c08000050000001000048000000b0140101c050040000000000000040002003018000180d00015018000000601401014000081c00400018000001803004024000000301414024000100101002020000080201008000090040601c0600000008020000200409020020000b0127a6094b439e58252d0e7b60547439e18151d0e3f6550c4397d954310f3b4354043d690d5010f394354043d650d5010e5e63947429758e51d0ab96010e429798e5090a5d6394242d698e5090b596394242ce90e5090b384394242ced0a5090a7a6014d429e5805350b5a6014d42d65805350a3e65d0d42c714f4350b1c5350d42c714e4250aba60909428f5964310ab96010c428fd954210a9c63508429bd954210a7b60544429e1815110a7a60153329e58054cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548cad96010e328fd91518ca3c64546329ed81518ca7860546328f992508ca3d64942328f992544ca5f63551328f994544cb1c548c9329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cad96010c3297d95320ca9c644c8329bd95320cb365494432cd552510cb365454432cd551510cb574354432d510d510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cab96010f419e98252d06796094b41a718d42d067a6094e419e582539075a6094e41d6582539071e53d0e41c794d439071e5390a41ae982429071e5310a41c794f419063e6510d41ae580435063e65d0941a718d425069e63905419798c505
  | 3 => 0x6b0264dcae80002c8050202f1224f05b84535e334b28381740001b904284704d48000002b48c8ec2cc318c10863a80007c17d42e8488100025a000001b90000008900000000050040000274051d12ae0f02d80b14e36ce50a1296778491880c8000000001bc5b40010300066cba2070b400045a000001300005c0001a4671a733a0000007a0000006b800242000650f20002c8000000000000014c0007700010b0003b8fd9a11360007108a0005d804989000000449640b00000013a0006dc000bb3c20f40a14f38c000000be06c138ec8340fe000000001ac1e00002233c4fc001b538400000171000324001e215874c4a1112fe4a42f000000814238003280004700026417c5102b03a46cfea0c1b8254388740002349b00031c000b999914c6fc93901000340221d70ce001010000004140f1b2426000000001aa000c011f37c3307803b2124ec001180000008720f286000c900042a4c47f0bd416000f289f19e0cc000d10000000015900039c640003de28c419d00000000006d000000c78ab23c000701081020a8ae0000006f44c01840c000000000000000012c000000c8000000148fb000000000001e62d8174fc85500001c00028000580609e0350748839ac2a444c1604a000000000002ac7b87a9f7000098001ec02a56c4f02733e0001a9cd3be000ce0000a006c001462442c44b99809a71c0810d0005e8000000000002a000000000a69f3000184000a400039403149000000000003fc030f48003b62d00018a0007a8000001a6000a39400e40000008423a6d000191000720148000ac230a88001b46589307000460d0814e0000001c88800018c830c72a0868000790005c8e1a19356180c69ad0001d42496b2b45a8a40bc000348001ce294000020fb10e000f38002f661c49945096480c61252aa5845f800000144ea80000a00000000388000c983f00010c001fc000510db023100858000000008247e0d90cc610eb1a30007a00000021e000758d80002c0d99f504a3909a1530000010695f1c6000d21fa11e034d81242380200896216a0000000003458cf6800270268c08001d41a8e001f4221f4b78763924c07b80
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x123800102cf5c44482541434c754a34600158260000c0020000038608d465c05350d42c30a730484a15197018d540caa8b8086a8865451d13254432a32e129a8720e1a53982429068c39a8428283469ce4114141a32e031aa998e1654584328c64cb9cc121281265cc6050540c32c6b00a89841d76150324c30a2a2c219261075d854cc530a32e6302a91043876551308828cb98c0aa0219258d5210010870ecaa26008628645493004315322a5900218a1915244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc044008198714e60909428198794e6090a41819861cd4214141819869ce4114141
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83fff81f0ffe3e1f0f878ffe3c0fe0fe41f673
  | 1 => 0xfc3fffe00fffffe00ffff0ffc00ffffc7e387f
  | 2 => 0xffc0fffff07fc3fff007ff0ffff0ff0387cf9c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 4 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa88688c49314620782c189962469225a40d631
  | 1 => 0x1108110224280060050a102840824ca01a2846
  | 2 => 0x8122248014004891004a20289209208854298
  | 3 => 0x52acc492880cab32a9d0088d32cc0433680d60
  | 4 => 0x6330871cce7133dcce674cc0230818c3f7b000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8fce8f8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37137
namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a04000017fd5005fe54017f55005fc54017fd4c05fe53017f54c05fc53007fd0c01fe43007f50c01fc43017fd48057f5200ff94805fd52005f54803fc52007fd0803fe42007f50803fc42007fcc803fe32007f4c803fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84200bffd951005dfeca880037f65440013fb2a200bff99510015fcca8802ffd65440177eb2a200bff19510015f8ca8802f7c65440053e32a2000ffd9110005fec888003bf64440015fb222000ff9911004dfcc888003fd64440017eb222000ff1911004df8c888003bc64440015e322200bffd511005ffca88802ffd5444017fe2a22000ffd8d10005fec688003fe63440117f31a2000ff58d10005fac688003fc63440117e31a200bffd4d1005ffca68802ffd5344017fe29a2000ffd0d10007fc8688003fd4344001fe21a2000ffd8910005fec48802bfe62440037f3122000ff58910005fac48802bfc62440037e312200bffd491005efea48802bfe5244017fea922000df54910057f8a488003ff4244015ff2122000ff50910057f88488003ff3244015ff1922000ff4c910057f8648802fff5144017ff28a200bff5451005ff8a288003ff4144001ff20a2000ff50510007f88288003ff3144001ff18a2000ff4c510007f8628802bff2144001ff10a2000ff48510057f8428802fff5044007ff282200bff5411001ff8a088003ff4044007ff2022000ff5011001ff88088003ff3044007ff1822000ff4c11001ff8608802bff2044007ff1022000fe88110007fa4088003f92044007fe1022000ffc4110007f6208800ffe1044007fb0822003ffd941001dfeca0800ffe65040057f3282003df99410014fcca0800ffd650400d7eb282003df59410004faca0800ffc65040077e3282003ffd901001dfec80800ffe64040137f3202003ef990100057cc80800ffd64040017eb202003ef590100057ac80800ffc64040077e3202006ffd5010037fca80801bfd540400dfe2a02003ffd8c1001dfec60800ffe63040117f3182003f798c10005bcc60800ffd63040017eb182003f758c10005bac60800ffc63040077e3182006ffd4c10037fca60801bfd530400dfe2982000ffd0c10007fc8608003fd4304001fe2182003ffd881001dfec40800ffe62040037f3102003fb9881000ddcc40800ffd62040017eb102003fb58810005dac40800ffc62040077e3102006ffd4810036fea408017fe520400dfea902000df5481002ff8a408003ff420400bff2102000ff5081002ff88408003ff320400bff1902000ff4c81002ff8640801efe610400dffa882004ff94410037faa208013fc5104001ffa082004ff90410007fa8208013fc4104001ff9882004ff8c410007fa6208013fc310400bff9082004ff88410007fa4208013fc21040077f3002003ffd401001ffca00800ffd5004007fe2802003ffd0010007f6800800ffe4004007fea002003ff1001001ff0800800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0x3fe3148001fe98a4000ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb02400fffd412001ffca09003ffd5048007fe2824000ffd0120007f6809000ffe4048001fea024003ff10120007f08090003ff3048007ff1824000fe8c120007fa6090003f93048007fe1824001ffc812000ff6409000ffe2048007f71024003ff0812001fd84090007f82048009ffb2e2007bfd971003ffccb8800afe65c400ffeb2e2007bf59710027f8cb8800afc65c4009ffb262000bfd9310007fcc988026fe64c4001feb262000bf59310027f8c988026fc64c400fffaa62007ff9531003ffaa98801ffc54c4009ffb1e2000bfd8f10007fcc788022fe63c4001feb1e2000bf58f10027f8c788022fc63c400fffa9e2007ff94f1003ffaa78801ffc53c4001ffa1e2000ff90f10007fa8788003fc43c4009ffb162000bfd8b10077fcc588006fe62c4001feb162000bf58b10027f8c588006fc62c400fffa962007dfd4b10077fca58801ffd52c4001bea96200eff14b10007fe858803bfe42c4001fea16200eff10b10007fe658803bfe32c4001fe996200eff0cb1003ffea388013fe51c400ffea8e2004ff14710007fe8388013fe41c4001fea0e2004ff10710007fe6388013fe31c4001fe98e2004ff0c710077fe4388013fe21c4001fe90e2004ff0871003ffea18800ffe50c400ffea862003ff14310007fe8188003fb40c4007ff2062000ff5031001ff88188003f840c4001ff9862003ff8c310007fa618800ffc30c401dff9062003ff88310007fa418800ffc20c4007ffb2c2003bfd961001ffccb0800afe6584007feb2c200dbf5961001ff8cb0800efc6584007ffb242003bfd921001ffcc908026fe6484007feb242000bf5921001ff8c90800efc648401bffaa4200dff9521006ffaa908037fc5484007ffb1c2003bfd8e1001ffcc708022fe6384007feb1c2000bf58e1001ff8c70800efc638401bffa9c200dff94e1006ffaa708037fc5384001ffa1c2000ff90e10007fa8708003fc4384007ffb142003bfd8a1001ffcc508006fe6284007feb142000bf58a1001ff8c50800efc628401bffa94200ddfd4a10067fca508037fd5284001bea94200cff14a10007fe8508033fe4284001fea14200cff10a10007fe6508033fe3284001fe994200cff0ca1005dfac308037ff518401bff28c200dff5461006ff8a308003ff4184001ff20c2000ff50610007f88308003ff3184001ff18c2000ff4c610007f86308033ff2184001ff10c2000ff48610067f8430800efe6084007ffa842003ff9421001ffaa10800ffc5084007ffa042003ff9021001ffa810800ffc4084007ff9842003ff8c21001ffa610800ffc3084007ff9042003ff8821001ff4410800ffd2084001fc9042003ff0821001ffe210800ff71084001fd8
  | 2 => 0x3001ff8c41800efc620c025ffa906012dfd483008ffca41804bfd520c001bea906011ff14830007fe8418047fe420c001fea106011ff10830047fe6418023fe320c011fe9906008ff0c83001ffec21800ffe610c0017f3086003ff58430005fac21800ffc610c025ffa886012ff94430097faa21804bfc510c001ffa086000ff90430007fa8218003fc410c011ff9886008ff8c430047fa6218023fc310c023ff9086000ff88430007fa4218047fc210c0077f3006003ffd403001ffca01800ffd500c007fe2806003ffd003001ffc801800ffd400c007fe2006003ffcc03001fbe601800ffe300c007fd1806003ff4c03001fba6018023f9300c007ff9006003ff0803001ffecb1000eff6588007ff32c4002bf9962001ffacb10042fd6588007fe32c4003bf1962001ffec91000eff6488007ff3244009bf9922001ffac910002fd6488007fe3244003bf19220087fea910043fe5488021feaa44010ff1522001ffec71000eff6388007ff31c4008bf98e2001fbcc710002de6388007feb1c4000bf58e2001fbac710002dd6388007fe31c4003bf18e20087fea710043fe5388021fea9c4010ff14e20007fe8710003fe4388001fea1c4000ff10e2000dfac510007ff5288003bfa944001ff94a2000ffaa5100077d5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944003ffd862001ffcc310002fe6188007feb0c4000bf5862001ff8c310043ff5188021ff28c4010ff54620087f8a310003ff4188001ff20c4000ff50620007f88310003ff3188001ff18c4000ff4c620007f86310007ff2188003ff10c4001ff4862000ff8431000efe6088007ffa844003ff9422001ffaa11000ffc5088007ffa044000fed022001ffc811000ffd4088007fe2044003fe1022001ffe611000ffe3088007fd1844003ff4c220007f2611000ffc3088007ff9044003fbc822000ff6411000ffc2088007fc104400fffd952007dfeca9003ffe65480057f32a400fff5952007dfaca9003ffc65480057e32a4000ffd9120005fec890003fe64480137f3224000ff59120005fac890003fc64480137e322400fffd512007ffca89003ffd544801ffe2a24000ffd8d20005fec690003fe63480117f31a4000ff58d20005fac690003fc63480117e31a400fffd4d2007ffca69003ffd534801ffe29a4000ffd0d20007fc8690003fd4348001fe21a4003bfd892000ffea4900077f5248003ff2924001ff5492000efaa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf1852007ffea29003ffe514801ffea8a400fff14520007fe8290003fe4148001fea0a4000ff10520007fe629000
  | 3 => 0xe2066017ffc833001ff8419800fff658c0077fb2c6003ff99630015fccb1800ffd658c02d7eb2c6003ff1963001df8cb1800fff648c0077fb246003ff9923004dfcc91800ffd648c0017eb246003ff1923001df8c91805bff548c02dff2a46016ff552300b7f8a918052fd638c02dffa9c6008ff94e300b7faa718023fc538c001ffa1c6008ff90e30007fa8718023fc438c007ffb146003ff98a3000dfcc51800ffd628c0017eb146003ff18a3001df8c51805bff528c02dbfa946015ff94a300b7faa5180037d528c02bfe2946000ffd0a300affc8518003fd428c02bfe2146008ffcca300affc6518003fd328c011fe1946003ffd863001ffcc318002fe618c007feb0c6000bf5863001ff8c31805bff518c02dff28c6016ff546300b7f8a318003ff418c001ff20c6000ff50630007f88318023ff318c001ff18c6000ff4c630047f86318057ff218c001ff10c6000ff486300aff8431800efe608c007ffa846003ff9423001ffaa11800ffc508c007ffa046003ff9023001ffa811800ffc408c007ff9846003f7cc230047f6611800fff208c007fe1046014ffd95300a5feca980037f654c0013fb2a6014ff99530015fcca98053fd654c0297eb2a6014ff19530015f8ca980537c654c0053e32a6000ffd9130005fec898003bf644c0015fb226000ff9913004dfcc898003fd644c0017eb226000ff1913004df8c898003bc644c0015e3226014ffd51300a7fca898053fd544c029fe2a26014ffd4d30047fca698053fd534c011fe29a6000ffd0d30047fc8698003de434c001fea1a6000f750d30047f88698003ff624c0017fb126013ff9893000dfcc498003fd624c027fe3126001bf189300a7fea4980537f524c027ff2926014ff54930006faa49804ffc524c001ffa126013ff90930007fa849804ffc424c011ff9926013ff8c93009fbc6498003fd324c011fe1926013f70c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c029ffa8a6014ff945300a7faa298053fc514c001ffa0a6000ff90530007fa8298003fc414c011ff98a6000f7cc530007fc6298003fd314c001ee98a6008ff0c53009ffe4298003fe214c001fe90a6013ff085300a7fea09800ffe504c029fea826003ff14130007fe809800ffe404c001fea026003ff10130047fe6098023fb304c007ff1826003f78c13009ffe409800ffc204c007ffb286003bfd943001ffcca1800afe650c007feb286012bf5943001ff8ca1800efc650c007ffb206003bfd903001ffcc818026fe640c007feb206000bf5903001ff8c81800efc640c025ffaa06012ff95030097faa81804bfc540c0117f3186008ffd4c30047fca618023fd530c011fe2986008ffd0c30047fc8618023fd430c011fe2186003ffd883001ffcc418006fe620c007feb106000bf588
  | 4 => 0x6ffe4250001fea128009ff10940007fe64a006ffe3250001fe992801bff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150039ffa8a801cff945400e7faa2a0073fc5150013ffa0a8000efd0540007fc82a0003fd4150001dea0a8009ff10540007fe62a0003fe3150001fe98a8000ff0c5400dffe42a0003fe2150001fe90a801bff085400e7fea0a000ffe5050039fea828003ff1414004ffe80a0027fb4050007ff2028003ef901400dffe40a000ffc2050007ffb288003bfd944001ffcca2000afe6510007feb28801abf5944001ff8ca2000efc65100137f3208009ffd504004ffca820027be5410013feaa0801aef5504004ff8a82000fff6310007ff3188008bf98c4001fbcc620002de6310007feb188000bf58c4001fbac620002dd6310007fe318801affd4c400d7fca62006bfd5310035fe2988009ffd0c4004ffc8620003be4310013fea188009ff10c4004f78862000fff6210007ff3108001bf9884001ffac420002fd6210007fe3108003bf188400d7fea42006b7f5210033ff290801aff54840006faa420067fc5210013ffa108009efd084004ffc8420027fd4210001dea108009ff10840007fe6420067fe3210001fe9908019ff0c84001ffec22000ffe61100017f3088003ff58440005fac22000ffc6110035ffa88801aff944400d7faa22006bfc5110013ffa088009ff904400077c8220027fd4110013fe2088009ef10440007fe6220003fe3110001fe9888000ff0c4400cffe4220003fe2110001fe9088019ff0844001dfcc02000fff5010007ff2808003ff5404001ff8a02000fff4010007dfa008003ff9004001ff4802000ffd4010007dea008009fe5004001ffe402000ffc2010011ffb2e6008bfd9730047fccb9800afe65cc011feb2e6018bf59730047f8cb98022fc65cc011ffb266008bfd9330047fcc998026fe64cc011feb266000bf59330047f8c998022fc64cc031ffaa66018ff953300c7faa998063fc54cc011ffa9e6008ff94f30047faa798023fc53cc011ffa1e6008ff90f30047bc8798023fd43cc001eea1e6008ff10f30047fec598023fe62cc0037f3166008ff58b30005fac598023fc62cc0037e3166018ffd4b300c6fea59805ffe52cc031fea966000df54b300bff8a598003ff42cc02fff2166000ff50b300bff88598023ff32cc011ff1966017f78cb30047fa6598023fc32cc011ee1966008ffd8730047fcc398002fe61cc011feb0e6000bf58730047f8c398063ff51cc031ff28e6018ff547300c7f8a398003ff41cc001ff20e6000ff50730007f88398023ff31cc011ef98e6008ff8c730047fa6398003dd31cc011fe18e6017ffc8730007fc4398003fd21cc02ffe10e6018ffd433001ffca198063fd50cc007fe2866000ffd033001ffc8198003fd40cc007f
  | 5 => 0x812101df8c090887ff5048443ff2824221ff5412110ff8a090807ff2048403f79024201ff0812104ffecba0026ff65d0013ff32e8002bf9974004efccba000a7e65d0013feb2e8020bf5974004efacba00027d65d0013fe32e8009bf1974004ffea9a0027fe54d0013feaa68009ff1534004ffec7a0027fe63d00117f31e8009ff58f40005fac7a0027fc63d0041ffa9e8020ff94f40107faa7a0083fc53d0013ffa1e8009ff90f4004ffa87a0027fc43d0013ffb168009ff98b4000dfcc5a0027fd62d00017eb168009ff18b4000df8c5a0083ff52d0041bfa96801fff94b40107faa5a00037d52d003ffe2968009ffd0b4004ffc85a0027fd42d0013fe2168000ffccb400fffc65a0003fd32d003ffe1968009ffd874004ffcc3a0002fe61d0013feb0e8000bf5874004ff8c3a0083ff51d0041ff28e8020ff54740107f8a3a0027ff41d0013dfa0e8009ff9074004ffa83a0003bd41d0013fe20e8000ffcc740007fc63a0003fd31d0001fe18e801fffc8740007fc43a0003fd21d003ffe10e8020ffd434001ffca1a0083fd50d0007fe286801fffc834001ff841a000fff65900077fb2c8003ff99640015fccb2000f7e65900053f32c8003ff596400f5facb2000f7d65900013eb2c8003ff1964001df8cb20072fd649003dffaa48009ff952400f77ca92007bfd549003ddeaa48009ff1524001ffec72000ffe63900117f31c8003ff58e40005fac72000ffc639003dffa9c801eff94e400f7faa72007bfc5390013ffa1c8000ff90e400077c8720003fd4390013fe21c8000ef10e4001ffec52000ffe62900037f3148003ff58a40005fac52000ffc62900077e314801effd4a400f6fea520077fe529003dfea948000df54a400eff8a520027ff4290001dfa14801dff90a40007fa8520003bd4290013fe2148000ffcca400effc6520003fd329003bfe1948003ffd864001ffcc320002fe6190007feb0c8000bf5864001ff8c32007bff519003dff28c801eff546400f7f8a320027ff4190001ff20c8000ef90640007fa8320027fc4190001de20c8000ffcc640007fc6320003fd3190001fe18c801dffc8640007fc4320003fd219003bfe10c8003bf9824001ffea12000ffe5090007fea848003ff1424001ffe812000fbf4090013fda048003ffc824001ff84120073ff65500397fb2a801cff99540015fccaa0073fd65500397eb2a801cff19540015f8caa0073ff5450013ff2a2801cff5514004ff8a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc63500117e31a801cffd4d400e7fca6a0073fd5350039fe29a8009ffd0d40007fc86a0003fd4350013fe21a8000ffd8940005fec4a006ffe62500037f3128000ff589400dff8c4a0006fc6250039ffa92801cdfd49400dffca4a0073fd5250001bea92801bff1494004ffe84a0
  | 6 => 0x1ffa186208ff90c31047fa8618823fc430c409ffb106208ff9883100dfcc418823fd620c4017eb106204ff1883100df8c418893ff520c449bfa906223ff94831127faa4188037d520c447fe2906200ffd083111ffc8418803fd420c447fe2106208ffcc831047fc641888fde320c411fe9906208ff0c831047b86418896fe610c449ffa886204ff94431127faa218813fc510c401ffa086204ff90431007fa8218813fc410c411ff9886208f7cc431027fc6218823f6310c411fe9886200f74c431047ea621888fff210c409fe1086204ffd8031047fcc01880efe600c411feb006200bf58031027f8c018893ff500c449ff2806224ff54031127f8a01888fff200c447fe1006204ffd9621115fecb1088bfe65884057f32c4222ff59621115facb10813fc65884057e32c4204ffd9221005fec910803fe64884137f3244200ff59221005fac910813fc64884137e3244222ffd5221117fca91088bfd5488445fe2a44204ffd8e21005fec710803fe63884117f31c4200ff58e21005fac710813fc63884117e31c4222ffd4e21117fca71088bfd5388445fe29c4200ffd0e21007fc8710803fd4388401fe21c4201bf58a2100ffea5108077f5288403ff2944201ff54a2100efaa510807fc5288403ffa144201ff90a2100ffa8510807fc4288403ff9944201ff8ca2100ffa6510807fc32884037f30c4222ffd4621027fca31088bfd5188409fe28c4200ffd0621027fc8310803fd4188409fe20c4200ffcc621027fc6310803f63188401fe98c4200fd4c621027f86310807ff2188403f790c4201fdc8621027f84310807f42188409ffb044200ff9822101dfcc110803fd60884017eb044204ff18221117fea11088bfe5088445fea844222ff1422100ffe4110807fc2088443ffb2a4221bfd952110ffcca9080afe6548443feb2a4221bf5952110ff8ca9080afc6548401ffb224200bfd9121007fcc890826fe6448401feb224200bf59121007f8c890826fc6448443ffaa24221ff9512110ffaa890887fc5448401ffb1a4200bfd8d21007bec690802df6348401ff31a4208bf98d21007fac690802fd6348401fe31a4208bf18d21007b8c690802dc6348443ffa9a4221ff94d2110ffaa690887fc5348401ffa1a4200ff90d21007fa8690803fc43484037fb124201ffd492100efea490807fe5248403fea924201df5492100ff8a490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148443ffa8a4221ff9452110ffaa290887fc5148401ffa0a4200ff90521007fa8290803fc4148401ff98a4200ff8c521007ec6290803fd3148401fa98a4200ff0c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff1
  | 7 => 0x988a7fc52cc401ffa166229ff90b31007fa85988a7fc42cc411ff9966208f7ccb31047fc6598823fd32cc401ee9966208ff0cb31157fea3988abfe51cc455fea8e622aff14731007fe8398803fe41cc401fea0e6200ff1073114ffe43988a7fc21cc411ffb066208ff9833101dfcc198823fd60cc4017eb066208ff18331157fea1988abfe50cc455fea86622aff1433114ffe41988a7fc20cc409ffb2c6225bfd963112ffccb1880afe658c44bbf32c62029f9963112ffacb18896fd658c401beb2c62009f59631027f8cb1880afc658c409ffb246200bfd9231007fcc918826fe648c401df3246200af99231007fac918802fd648c401deb246200af59231027f8c918826fc648c44bffaa46225ff9523112ffaa918897fc548c44f7eb1c6225ffd4e31047fca718897fd538c411fe29c6200ffd0e31047fc8718803fd438c411fe21c6204ffd8a31147fcc518806fe628c401feb146200bf58a31027f8c518806fc628c44bffa946225dfd4a31147fca518897fd528c401bea946228ff14a31007fe85188a3fe428c401fea146228ff10a31047fe65188a3fe328c451ef1946200ff4ca31047f865188a3dc328c4117f30c6225ffd4631027fca318897fd518c409fe28c6200ffd0631027fc8318803fd418c409fe20c6208ffcc631007be6318823f7318c451ff90c6204ff08631027fec118803fe608c4077f3046200ff58231005fac118813fc608c44bffa846225ff9423112ffaa118897fc508c451ff9046228ff0823113ffeca9889eff654c44fff32a6202bf9953113ffaca9889efd654c44ffe32a6202bf19531007fec898802ff644c401ff3226209bf99131007fac898802fd644c401fe3226209bf1913113ffea89889ffe544c44ffeaa26227ff1513113ffea698823fe534c44ffea9a6208ff14d31007fe8698823fe434c401fea1a6208ff10d31007fec498802ff624c44dff3126201bf98931007fac49889bfc624c4037e3126227ffd493113efea49889bfe524c44ffea926200df54931137f8a498803ff424c44dff2126200ff50931137f88498823ff324c401ef9926226ff8c931007fa6498803dd324c411fe1926227ffd453113ffca29889ffd514c44ffe28a6200ffd0531007fc8298803fd414c401fe20a6208ffcc531047ee6298803fe314c401ef18a6226ffc8531137f84298803ff604c4017fb026200ff98131007fac098803fc604c4077e3026227ffd413113ffca09889ffd504c44ffe2826226ffc8131137f84098813ff650c4117fb286208ff99431015fcca18823fd650c4497eb286204ff19431045f8ca18813ff640c4117fb206208ff9903104dfcc818823fd640c4017eb206204ff19031045f8c818893ff540c449ff2a06224ff55031127f8a818822fe630c411ffa986208ff94c31047faa618823fc530c41
  | 8 => 0xfd4641027fca3208b7fd5190409fe28c8209ffd06410077e8320827f74190461ff90c8204ff08641027fec120803fe60904077f3048200ff58241005fac120813fc609045bffa84822dff9424116ffaa1208b7fc5090461ff9048230ff0824117ffecaa08beff6550401bfb2a82009fd954117ffccaa080afe655045ffeb2a822fbf5954117ff8caa080afc655045fbe32a82029f1954117ffea8a0827fe545045fdf2a2822fff5514117f7aa8a0827fc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8208bf18d4117ffea6a08bffe535045ffea9a822fff14d4104ffe86a0803fe4350401df21a8200ff50d4104ff886a0803bc4350401ffb128200bfd8941177fcc4a0806fe6250401feb12822eff1894100df8c4a08bfff525045fbfa92822eff9494117ffaa4a08037d525045dfe2928209ffd09410077e84a08bbfe4250401fea128200ef5094104ff884a0803ff325045dff1928200ff4c941177f864a08bfff515045fff28a822fff5454117ff8a2a0827ff4150413fba0a8200ff905410077c82a08bbff215045dfe10a8200ffd8141005fec0a0803fb60504017db028200ff98141007fac0a0803fc60504077e3028200fe18141005f0c0a08bfff505045fff282822fff5414117ff8a0a08bbff205045dfe1028204ffd944104dfeca20827fe65104057f3288209df99441014fcca20827fd65104597eb288209df59441004faca20813fc65104137e3288209bf9904104ffea820827fe5410413feaa08209ff15041027fec620827fe63104117f3188209ff58c41005fac620813fc6310459ffa98822cff94c41167faa6208b3fc5310413ffa188209ff90c4104ffa8620827fc4310409ffb108209ff9884100dfcc420827fd62104017eb108204ff1884100df8c4208b3ff5210459bfa90822bff94841167faa4208037d5210457fe2908209ffd084104ffc8420827fd4210413fe2108200ffcc84115ffc6420803fd3210457fe190822dbf98441167fea220813fe5110459fea888204ff1444104ffe8220827bf4110409ff2088209fd9044104ffa8220803bd4110413faa08822bffc8441027f84220813ff6010413ff3008203bf9804104ffac020802fd6010409fe300822cffd4041167fca0208b3fd5010459fe280822bffc804115ff84020823ff65cc4117fb2e6208ff99731015fccb98823fd65cc4557eb2e6208ff19731045f8cb98823ff64cc4117fb266208ff9933104dfcc998823fd64cc4017eb266208ff19331045f8c9988abff54cc455ff2a6622aff55331157f8a998823ff53cc411ff29e6208ff54f31047f8a798823ff43cc411ff21e6208ff50f31047f88798823ff62cc411ff3166201bf98b31047fac598802fd62cc411fe3166201bf18b31157fea5988ab7f52cc453ff296622aff54b31006faa5
  | 9 => 0x803fe2166401ff8cb3200fbc6599007ee32cc803fe1966401f70cb32047fec399023fe61cc8017f30e6408ff58732005fac399023fc61cc869ffa8e6434ff947321a7faa3990d3fc51cc803ff90e6401ff08732047fec199023fe60cc8077f3066408ff58332005fac199023fc60cc869ffa866434ff943321a7faa1990d3fc50cc803ff9066401ff0833219ffeca990ceff654c867ff32a6402bf9953219ffaca990cefd654c867fe32a6402bf19532007fec899002ff644c801ff3226409bf99132007fac899002fd644c801fe3226409bf1913219ffea8990cffe544c867feaa26433ff1513200dfec6990cfff534c811ff29a6433ff54d32047f8a699003ff434c811ff21a6400ff50d32047f88699006ff624c803ffa926401dfd493200ffca499007fd524c803bea926401ff1493200ffe8499007fe424c803fea126401ff1093200ffe6499023ef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003fe614c801feb0a6400ff18532005f8c2990cfff514c867ff28a6433ff5453219ff8a299007ff214c803fe10a6400ffd8132005fec099003fe604c801feb026400ff1813201df8c0990cfff504c867ff2826433ff5413219ff8a099007ff204c803fe1026409ffd974104dfecba0827fe65d04057f32e8209ff59741195facba0827fc65d04137e32e8209ffd534104ffca9a0827be54d0413feaa68232ef5534104ff8a9a0827ff63d0413ff31e8208bf98f4104ffac7a0802fd63d0413fe31e8232ffd4f41197fca7a08cbfd53d0465fe29e8209ffd0f4104ffc87a0803be43d0413fea1e8209ff10f4104f7887a0827ff62d0413ff3168201bf98b4104ffac5a0802fd62d0413fe3168201bf18b41197fea5a08cb7f52d0463ff2968232ff54b41006faa5a08c7fc52d0413ffa168209efd0b4104ffc85a0827fd42d0401dea168209ff10b41007fe65a08c7fe32d0401fe9968231ff0cb41197fea3a08cbfe51d0465fea8e8232ff1474118ffe43a08c7fc21d0413ffb068209ff9834101dfcc1a0827fd60d04017eb068209ff18341197fea1a08cbfe50d0465fea868232ff1434118ffe41a08c7fc20d0409ffb2c822dbfd964116ffccb2080afe659045bfeb2c822dbf59641027f8cb2080afc659045f7eb24822dffd524104ffca9208b7fd5490413fe2a48204ffd8e41007fcc720822fe6390401feb1c8200bf58e41027f8c7208b7ff539045bff29c822dff54e4116ff8a720827ff4390401ff21c8200ff50e4104ff88720813ff6290461ff3148201bf98a41007fac520802fd6290409fe3148201bf18a4116ffea5208b77f5290461ff294822dff54a41006faa5208c3fc5290413ffa148230ff90a41007fa8520827fc4290401ff9948230ff8ca41007fa65208c3fc32904137f30c822df
  | 10 => 0xa2218e3fc5110c6fff9088637ff08443047fec021823fe6010c077f3008608ff58043005fac021823fc6010c71ffa808638ff940431c7faa0218e3fc5010c6fff9008637ff08043006fec8a90037e6454801beb22a400df19152006fec6a90037e6354801beb1aa400df18d52006fe86a90037e4354801bea1aa400df10d5200efec4a90067f6254805b7b12a401df9095200ef884a90077e3254803be192a400dfd8552006fcc2a90037d6154801be30aa401dfc855200ef842a90037f6054801bf302a400df58152006f8c0a90077f2054803be102a409ffd974204dfecba1027fe65d08057f32e8409ff597421b5facba1027fc65d08137e32e8401bf9934204ffea9a1027fe54d0813feaa68409ff1534204ffec7a1027fe63d08117f31e8409ff58f42005fac7a1027fc63d086dffa9e8436ff94f421b7faa7a10dbfc53d0813ffa1e8409efd0f4204ffc87a1027fd43d0801dea1e8409ff10f4200dfac5a1007ff52d0803bfa968401ff94b4200ffaa5a10077d52d0803fe2968401ff90b4200f7c85a1007ee42d0803fe2168401ef10b4200ffc65a1007fc32d0813ffb0e8409ff98742005fcc3a1027fd61d08017eb0e8409ff187421b7fea3a10dbfe51d086dfea8e8436ff1474200ffe43a1007fc21d0813ffb068409ff9834201dfcc1a1027fd60d08017eb068409ff183421b7fea1a10dbfe50d086dfea868436ff1434200ffe41a1007fc20d086bffb2a8435bfd95421affccaa100afe655086bfeb2a8435bf595421aff8caa100afc65508037fb228435ffd514204ffca8a10d7fd5450813fe2a28400ffd8d42005fec6a1003fe6350801feb1a8400ff18d42045f8c6a10d7ff535086bff29a8435ff54d421aff8a6a1027ff4350801dfa1a8400ff90d42007fa86a1003bd4350813fe21a8401bfd894200ffea4a10077f5250803ff2928401ff5494200efaa4a1007fc5250803ffa128409fbd094200ffc84a1007be4250803fe2128401ef1094200fd884a1007fe3250803fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542005f8c2a10d7ff515086bff28a8435ff545421aff8a2a1007ff2150803fe10a8400ffd8142005fec0a1003fe6050801feb028400ff1814201df8c0a10d7ff505086bff2828435ff541421aff8a0a1007ff2050803fe1028408ffd9732045fecb99023fe65cc8057f32e6408ff597321a5facb99023fc65cc8117e32e6408ffd9332045fec999023fe64cc8137f3266408ff59332005fac999023fc64cc8117e3266434ffd53321a7fca9990d3fd54cc869fe2a66401bf98f32047fea799023fe53cc811fea9e6408ff14f32047fe8799023fe43cc811fea1e6408ff10f3200dfac599007ff52cc803bfa966401ff94b3200ffaa5990077d52cc803fe2966401ffd0b3200ffc8599007fd42cc
  | 11 => 0x9ff9534304ffaa9a1827fc54d0c7dffa9e8608ff94f431f7faa7a1823fc53d0c13ffb168609ff98b4300dfcc5a1827fd62d0c017eb168609ff18b4300df8c5a18fbff52d0c7dbfa96863dff94b431f7faa5a18f7fc52d0c13ff2168609ff10b431effc65a1823fc32d0c13ffb0e8609ff98743005fcc3a1827fd61d0c017eb0e8609ff187431f7fea3a18fbfe51d0c7dfea8e863eff147431effe43a18f7fc21d0c13ffb068609ff9834301dfcc1a1827fd60d0c017eb068609ff183431f7fea1a18fbfe50d0c7dfea86863eff143431effe41a18f7fc20d0c11ffb2c8608bfd9643047fccb2180afe6590c11feb2c863cbf59643047f8cb21822fc6590c757eb24863cffd524304ffca9218f3fd5490c13fe2a48608bf98e43047fea721823fe5390c11fea9c8608ff14e43047fe8721823bf4390c13efa1c8608ffd8a43047fcc521806fe6290c11feb148600bf58a43047f8c521806fc6290c79ffa94863cdfd4a431dffca5218f3fd5290c77fe294863bff90a4304ff88521823fe3290c11fe1948608ffd8643047fcc321802fe6190c11feb0c8600bf58643047f8c3218f3ff5190c79ff28c863cff546431e7f8a3218efff2190c77fe10c8608ffd8243047fcc12180efe6090c11feb048600bf58243047f8c1218f3ff5090c79ff284863cff542431e7f8a1218efff2090c77fe104863affd95431d5fecaa18037f6550c013fb2a863aff99543015fccaa18ebfd6550c757eb2a863aff19543015f8caa18eb7c6550c053e32a863affd514304ffca8a18ebfd5450c13fe2a2863affd4d43047fca6a18ebfd5350c11fe29a8609ffd0d4304fbe86a1823fe4350c11df21a8600ffd8943005fec4a18e7fe6250c037f3128600ff589431cff8c4a1806fc6250c75ffa92863adfd49431cffca4a18ebfd5250c73fe2928639ff9094304ff884a18e7fe3250c11fe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a18ebff5150c75ff28a863aff545431d7f8a2a18e7ff2150c73fe10a8600ffd8143005fec0a1803fe6050c01feb028600ff1814301df8c0a18ebff5050c75ff282863aff541431d7f8a0a18e7ff2050c73fe1028608ffd9443045feca21823fe6510c057f3288608ff594431c5faca21823fc6510c117e3288609bf9904304ffea821827fe5410c13feaa08609ff15043045fcc621823ff5310c11ff2988608ff54c43047f8a621823ff4310c11dfa188608ff90c43047bc8621823fd4310c11dea188609f750c43047fec421823fe6210c037f3108608ff58843005fac421823fc6210c037e3108638ffd48431c6fea4218dffe5210c71fea908637ff1484304ffc8421827fc4210c11ff1908608ff0c843047fec221823fe6110c017f3088608ff58443005fac221823fc6110c71ffa888638ff944431c7fa
  | 12 => 0x801000401803400002002c03006002800400002400000400000800802c0700000280b00040000080500080f000c0080c40b800401800020404c0000f807800000402c03000402000000401002808002c00801002c03000800c09003400001800006c02401c00800001001002405000800000c00c01c0a000000012c0240300200040a000002c0bc0000380ac02000402801000003007002002000003004002c02802000000400005400c00000000c01000c00402801801000005804c0dc00005002402002000012c0000a004401400801c0180000000c801801400c01c00407000006800403c06800c04400c0080040a003400000800000800c05009401400405800004400003002000c02801c00000c04401c0000040080080500041f807002400005403400c07403c08c00000804c03402402800414011001800806c0000740000000b010001c00000c03c0a006c03000001000800c00007005002c05800000000c00400000000001403c01000400c01c00801400c00003801403004c02402001800402400c00401c00000000005006809401404c01401401000805c02803800400000801c01c0300000040000040f80700a00140b801000000c0040b80080100280a00fc02800401000003c00000007406401402c00c03400c01400c01400000400005003003800000401409c00000400000800000c01c00c00000403008401001009401800000800405001013400000800001401001800c08c01803c02001c14c03c00c02800400004001402c0000380000000140380000000000e800800000000002004406000004c06002804008800402004803800000400000400000000000400000003404004c02001000000800405400401001004400004c09c00000c00400400000801802400800c00000009c14402c00002800400000800c00000000403800400407002000801802c00c01c01002400802000806802400816401401800c0180f002400400802c00003803c01401403c01002c01400400801006009800000003c00409c00c0700c404800400001400402400007400000000400000401405807c0000d801c00003000c03002c0000300040e000000000001000000c00000c08c0bc02401001000002800800400401001001803403c01400808c00804000c08800404403400400809401800000401814802805800009800000004c00800009400005c01805c00800405000400006c02400005006c05000c00000006402c06000001000800405005404000007803c00401801403800000006c01002c01c00400c00001c01000000000000001001c01800401c00401401400801405402408402800800004401401c01c03800403400c01000c13ffb2e8609bfd974304ffccba180afe65d0c13feb2e863ebf5974304ff8cba1826fc65d0c13ffaa6860
  | 13 => 0x501000263c77084c00019c4e123d3000248800048128300d4b9e58543e8c1c000000126800094c5a9004947ca2e6810000774dd08b03021bf00000273e78b6c0000000000270bdaa344c416c001e00039500003ee5a10000000e820e82a78000fea3722a9800079a00041124586822051d98d5ca349241ce9d38b32951372832077e28610f86c40002eb0001e1800048e47c2110944a311a7000000056101f088c7d442613805b0ac896c000000101c4b20001c5cd100004eb979cc586642fb80007d286300000008600000000e6800071e03510080008d311e033400091a1e5074c0001885148f04a069ff1b88000a7446941780608900004a4a7a4adc772000143c1a61c903f9cb859641145c0064f3c8dd2929030de2a0808602411786452901a4879c65708413ed3b2527251969c93855a36025d449056719aa60095c00000016303f674036b1c280004f800113504dc0000db80000000c23b0273ce9e9d1315182518e59414d950483c2830bd9dd851e8d10fa267507e5eb16614cd03235800018005aa166325033ce0686111913c529a71c524a8c82426cb05d00002c667c22395e015c0160000000fa461915f11b400084713d025c1b668609519512bc00025798e488a0324afa90c8541b829f86fc0009e41bf0c4c93037d3bea4803c272c167a6309963fe10b046800069b19ca9992382b61721ef93ca4d63e71860ae20225158000ea27dd0000dd01aa0003080cb4f5a00005a90043040004cf119000041600020ac37499420fa2190b43ec00007301f40000211b4d34e0000000000cfc62e08a89786484de0001b8000061c5089374000000507a5413782172f780000007283c80a346505322ffa0603567e60001be0dde41349f087861c6484c580000005e026c00010fc6ab531a024af48393f6a6c41d23f72ac8b4c14815139e002008000005800c00003400000000803c00006001400400002400004004000000c04c06c00c06800c0c405c0a000c00000000002c0140140100a400400c00400403400c01001c04007800800404000005801812c01c01c02404802c00400000c0a400000007801400c0000000000000000200400000080b40ac01c00001000402802003009c00800802002004401000000c00c00003400000001c00c02c00c00c05800c00400400c02400002401001007002800c01001c00800000001802c01001800007802002802c00000000800c0080040cc00000402c0e400801801c01000000000400000400405000000c02800003802c01000000c00c01009c00001400400000000c01004800001404801800000c00801c00005802002803000400c03000401c0680b000405402000000400001405004002400400800c0a401005c00806406c05409c00805800400000002400801c00c03802806c0080000080040
  | 14 => 0x5b155491009e3a90fb4f143901098a844ce2141dc85d93a652250701a13f60a12a3848c0003820710110cb8000030286c0001960e520e8be00002de1f78d4ea540001db4afa00000000000000c9242055c4027953c5a2883ae1da000000031c1fc00024fd1860000000124b3800019d2138b260004ef8480e660000b7222c0003fa1fa26580009e340224c14584922448000d708f20000c74a36000000000017e0000001dd06467d52ec8c5080e7470a2a2a00002d43ff0190c9868b148843862a00033c127c00053052b01892ca0e41ac8c5cb2e8ea4839b1541422937a14b81965a40801cc04724c235f86f84927962faa74888c48b25f01743c4a1320d99b501a0000c4904046c9c415986340002fb3dd800000008c01a231400047d488000117e7910898000b7c27500000002964080001948b9800028e19a0fca2120000aa8d2063400000012ec1db303822cd7400029600010680002d69fc91f845c4481de543a3c845ea7bccce07a16c215c3f23c342e8de41e24ca1ef97945944504d623585588eb52701f944401d1c88198d987d422a166869a58e44ea93057800010ea8488f27c613ea98914c63c00009d8aa448f3b2814c9a09a148f0b080724aa2dd0f4503a6b300023903846313518338e3464438f8d8455e93a4dd12fcc2895212f8b1836a83e4c28dd48d023a502244ca847bf49c8960cfe76822d800119407600f20d4a26a5d01286a914097413c14780f846f04d8a28a466c900003506160000688ea54bc8673be02a0c6c1af00010805c4000282a24480c7140591b7c5629662db9bd4bdc9a22309b0d2f400000022701de02d00020203665e825e0fac2164d91ad9abc0408542d61b288004d23dc8f48b02221466266cf464a90e5834068e2424951128d0671152c26e00ac27b1a2071009e1972cf0854ac683122e8e38aa07e812e804d26c20b21d9434df40fb06e23645ba591400a0a41b260e3b8063c92872d1b99a2412a73a0a60c453f4412026a1c53262102ea051c9e83cf29e8a4c2de2643a1a3d83cc63a4ae242438e8ce1438ef80000003270b380000000d08ec46ec7b74b981b860471d0002538a486a92771af4eee0d644721987927a41152350a622261cc1e340460b3217935d0a05260061f4406c1b9230095930e9fc4719fe400086a2ff11c902e00028e8000400a3b09aa98400010944111e0cbc92e4fc1f9d14a5874d522a49e08f34728968ddc1ea39281493b85dd151857c01048318280014c83c0000000000013c16b00005a000004c80011ee00000027c516e93b3ed129427c32c00000014303aa3808cacada1c004684b8a287121f7201c40469913fa71c7462920bc86911007444b1188c24aa4802588608d65e2503993418c9a40a41e60c7c0852469bc0d8e31e00021245fa84600004984a88b900002240
  | 15 => 0x57436600003980004da14425b4cb245752aa94097070741b80001f02714611448d3856c1a499040f020e27e070cf9629e3ce1e5d3f229542410f84129ec2af1d4c9ca9d64011c1426612b1608f9c5f806f0ce19400006e700200005e65db0000000000000000059d10e60f44a8a100562e3436853400048700000000000001b2a438d6004624aa79807042300018dd4541fa3d286a50bc1dc09c971c73873d48500013381ef00020a84805d14aa03fce420af1ae80012ba00040980000009560000c30caa2222e317ec6be5f824116186d82ee0ac15cd01e27c3ee256c56e7bd3d50d4938694c484119d4b887f31d95500001730000000a7000042887f83269891fc1e24d549581ab0f587986f23aca51023c8d834b127853e23b2d1a1e4cb439509d93e826e20a2dfa784fdc4562e51c2004884552787586063a70b283283e28a418d9e98d263ad1aa91680003322218665394a41000000010e00000018940003e00000000000000000020ce0c48a29da890c488000000dac0000000001f1400099f023a898c7e4490000a0098a351112163407e7ba06007ac852000000000000019415a00006421c550180000000000000c480002de2b3000021a3d40002628000a574c803312282594c71e644e89614dd8fe46809012a28bf8f0480638a9654bac7e31358d88a0e53c192a5a4fd8a370028928bc296730915dc4de2e812700a022823521997083bc3f504d000134c3e13bf1ba8dcc81e0001d2d42e2e500022b00386f331580010ea0f626326fcd003af03c9fed278a5918322691ce00000928803a09cc121894000054d0000000a800bb15280000000000000a250b29a81cf990c39a01714ba48d3840002ce8e6c6760840000ea016812837f000022e0000001ad028836e3e9a5a8e3200022f800139258849e924ccea00000000010806f748903f81ee4970c611dd35a00037f908400002c21897d11ae80c395a2d92048cf27e89dd46a3b51b5182c47a3f633994448a67c30fa9738e2695945596d4f3e60227ca06ce368254bea08099c11811780a92844ba47c9b84610771164089caac2f03e08688f643b629a9a7509e1062a1a91c1f222c20c83490f458a12b8b2487825b347a25ce8a07446f1ad86da82602b8000a12309053a0b475816800021bc0006c14e70bd45767f635305900e29530cd802d2ae61a3b10a9c3f0000446a808368000061800110a0000d917b0000369330800003e00028c26ad2221ed3411f10fd638600016ac64c000000000026000000000005f20002542334e049ae4ca8000afc9350000000340265285250c2fa05a13f03740002992b0000104e0da47d0954000000405126c00097e31e83f0c1832234391452943780c324bc78410f0739ded45e7390caa194a107cc3ca00005c220327219a8b247730360bbccde0260
  | 16 => 0x47000006383e63718a040006163e692ac6de55b00000000000a03201e6c61e0000001790c2e30005e8001442a4451c170c6021f241c0aacf44669079934470862707a14d00bc4762ac28402a661b2a593201ca3a60bf27f49c23990149ad41c299232da7051a04ea06c09a91642414a28780fb67931500bdc81a3c615682b00008ed4340b7c3d200021c801c3b099a000208524e0011189a80c6a1ff33800014002d13589d790ec9031168000af277525da6bc2a847036c8ca409057c2db174c3b29b6376938d4be732008a8649ee0000ad80000000000c800000004e62110000b5061f0000448c640000002260000000252000130c3681260e880004a04cb86ec0a85de1fd8e20b4a10408880f4da00e341d95107262dc01d020447e9a51291f00884a4015fa7340000000000588d6e0690ab21c0f4e67a14a12cc2369ea506000111800036a800000064f29788943c678e0d32434dfa285131a768f6a0000a50c1059a99111c0c9cab89d5054a1880003db425a8040002a84418d200004654c1a1f000000052d00009ce66201b8b0ca0000020280010be18144fa4b13600b01b38000dd88df1da00003d80000000e500b66053688000cac9f64ee8ccc43400008195ec5040001259eccba0a0904f9b7478815907e828d33000000006b12aa97923a1f5cf948f43ab95205e27e01d08140b1e3c72eb80007ca16b15107d8a721433d41ff0614893000081c84a56b00019747b828e0271e807740002430a687182f61c791544a288108e25ac85048523e144142a0000002834c920000000a2c63293139f25ec17092d09f94b40947c92c19fe000000000000c400024f32300001826760b8a2e800061d4ef11000007310209d6800084d1a812c468c3de27fa504a6c5691f92014e6a101367883486e1ee00015311d019248e85c89d802e0be1ae547e000058800000080b06f17c52fe76911414a40000004b800012908d53a485fc1d81464e283d495a75d3b72258ff478c51826ccbaa8422d118b511e9f40b50df033076b0491c2cb5e6bb4bb9b48b005b23a812742806e4419242d3b690f4141f842ba60d21d02f0d180f024824e02684b622099d087093745a1a7895834f51d1588d502623b1a6e54d22c44be216cb1690c1e282093dc5f61f123a4d9a8ee16009cc3220003fa0ff49a62723040cf49b81053199d08a7c0000000000dd2000000000000062125b90600000004648000fb28364b006a02481ad00015bcf8ea4b47611393fc0d7000294c87a26106221a50d83160001a446f459b00d98a0db00ab2ba9c3003400021719949220001dda3f93684151cf091920a14f0430000e98499000000140a318300800099800025824611ea5463bd259148c8cb44d9ee001481a26a903c5b294b000167cf606151fe16cc70e33c1a280ec0002b83b0a2a8
  | 17 => 0x61e1bf80010aa59639397a826400040883c8cee7663fb9a5c6b40001900000ae80331bb800000002f1638d50000549201a0f430600000024ac00091b37108cce5e78337b23692b42a402197106f684a0bc197c7e00b907701ac9da5281100000e441e44490a980ee0ea14c06c015a8ad2649a140004df0cd000041066003382500000001f18ffc72e62202f82982709b7040000106029d0260cfc00647f162a5b8f4240915aa2ed42c66e51f10d51cc6532ae9c8cbf44342669af0cb08120000000f524db2e685791080593b21e1069400003d80000003534d49a7cc8442b0a901002744ef28a978d0ee40a0a709e44a693439d98e09e4a33022a53c5d2710380052426c3ab0811c3863400007016249ec00000002f8ae42d21340b684228b51de9d5835c07505b9a540007b62f98f908e69630fe9e000c60610c5a718e704c319700003a2021453858400000023500000000000002608c5e0000000e0ced4000000000000000008ea6d40000eb226000014a5574fb80008b2000471102c37807d4a018c149433e20b97703903b74f81a38d8c098154a30401c4623ae0000db800033628794a4a1c4f0198d3469465168000ae02b24e59268f027f3136000065e33643d8000e940004929db00002301079d209c40001c29ef0ca27c8000000080893318f80000b854a00005d40ca2e71c5a3c525046e4909beca320000f98fa0f68000000282cccc00000a000000018500016112d00003f1000039e0003468000e6e331000050822c21b00016ec6861101ed0000000a060001200abe155394800000043f00000000000001e800014ce3d500002285c07541d927d4aa24eb0551538848a2e4801fa94720004ea180caec5fd096061c0000002fc800000000600020580b081044a1bad1fa0000000be000000000000000002ae231867543e5f2039208c85800048ba9a13ce000421800000000028720b038c72450d00007e29814781ec40003a52d022242b84c1000189928e00000021cc8f679d34c1a509e622e1a6145866800008f92580aa7ac15e8000560582308a370e300002220e812080883eb20b8000000000000148400000010702140002de984d0666d7051106800000000000005e85b42e58000cd643600006013c4a450d285e915c0000000be800067b0839a90d5860a3f7a0913a000025c90b514226950a01b44da85212393003ce915000024cfd235c3aaa2c427a5373148c3470043227f1ab8e2ca364b921040003dd00014a800035e0001fc40004cf1c917a40004e92639b6c5cc758175207d44e7854cc9dfc02a7922dca3480001f0352a3210dc8582269eb931a01012210740000003d58dc025e7e400008dce6805119c27c82448531a58818aca19f2f305a4eb626042e10509c0381000074824e38a3e827211fe67d0e716b82e0684
  | 18 => 0xd08b906c43ec0e5806047a2d51e2025240e176a7cc4561501f99748d349065119d1875c70443c1f7d1c21e83100e90f5e74d51ea700b4c6da00004b400021935f14104b83d7062a228000a2522c1a28bbe0000dea944ad49ed0a09f0834683c0ea93d494e4714f423101da4a1000236c0000001060000d4200000000013405c51b2000000080325a148431493208c9d9c11c502000298000000000015fcbb431015c942c0000003cd1ffcb8033017f80001be5681b0000123245e000218115e6f92dc16407de389233099902829639b17243be6d4063858124c8fb43212f52f06790000000b826723c38000b6200026223184687f044c8ef0438984359247c5d803c39f879448a16d04785dc12c2043931de0c0c8884dea96d36496f16b80347601745269d7c0003630000f642626a200011480004b54601b78e4085623a93a10e40730cf14ac3a89be0381dbc0006ad0e08a701220003fe976030844b459913c7b0a3c2cc17f0654a284f58a40e1e874179276013a8be19b869d02a8a314612310386ce4779c34a1846c000000047c9294b8a9948fc000323856871a64b1e59b210d689e0db0000f1e6c2213800
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe61548100077b705481022f78705481022e7e605481022f78405481022f77105481022f7a105481022f75105481004cff76d081001cfe76d0810004fd76d081001cfc76d08101b67e65d08100067d65d081004ebe64d0810006bd64d0810006de63d0810006dd63d081000eee62d0810006ed62d0810227b840d0810004ff765081001cfe7650810004fd765081001cfc76508101ae7e65508100067d655081004ebe6450810006bd6450810006de6350810006dd635081000eee6250810006ed6250810005fb705081001df8705081021fb84050810044ff76cc81001cfe76cc810004fd76cc81001cfc76cc8101a67e65cc8100067d65cc810006be64cc810006bd64cc810046de63cc810006dd63cc81000eee62cc810006ed62cc810004ff764c81001cfe764c810004fd764c81001cfc764c81019e7e654c8100067d654c810006be644c810006bd644c810046de634c810006dd634c81000eee624c810006ed624c810005f7714c810025f4714c810004fd76d04101967e65d04100067d65d041004ebe64d0410006bd64d0410006de63d0410006dd63d041018eee62d0410006ed62d041001df870d0410004ff76504100057f75504100357c755041017e7e65504100067d655041004ebe6450410006bd6450410006de6350410006dd6350410176ee6250410006ed6250410005fb705041001df87050410004fd76cc4101567e65cc4100067d65cc410006be64cc410006bd64cc410046de63cc410006dd63cc41014eee62cc410006ed62cc410004ff764c41013e7e654c4100067d654c410006be644c410006bd644c410046de634c410006dd634c410136ee624c410006ed624c410027d4314c410074ff764841010e7e65484100067d6548410006be6448410006bd6448410005df7348410005dc7348410006de6348410006dd634841000eee6248410006ed624841001df976d0010206f976d00102077a75d00102077975d001001f7a65d001001f7965d001001dfa74d001001fba74d001001efb64d001001fba64d0010206f964d001001fb964d0010006b964d001001fda63d001001fd963d001001efb62d001001fea62d0010006f962d001001fe962d0010006e962d00102177b52d00100077952d0010005f971d001020efa61d001001ff261d0010207bb41d0010007b941d001001dfb7644010006fb7644010004fb76440100077b75440101ff78754401001f7a654401001f796544010007bb7444010205fa7444010205f87444010007b87444010005b8744401001fba644401001fb9644401001fda634401001fd9634401001efb624401001fea6244010006f9624401001fe96244010006e962440101ff7b524401000779524401001dfb714401001ff37144010026fa614401001ff26144010027f251440101fff15144010
  | 1 => 0xc1001cfe7690c10004fd7690c1001cfc7690c101e67e6590c100067d6590c1004ebe6490c10006bd6490c10046de6390c10006dd6390c101deee6290c1001dfa7090c10005f97090c10257b84090c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c100057f7550c100357c7550c101d67e6550c100067d6550c1004ebe6450c10006bd6450c10046de6350c10006dd6350c101ceee6250c10005fb7050c1001df87050c10044ff7610c1001cfe7610c10004fd7610c1001cfc7610c101c67e6510c100067d6510c1004ebe6410c10006bd6410c10046de6310c10006dd6310c101beee6210c1024fb84010c10004ff7558810014fe75588100067e75588100147e7558810004fd75588100067d7558810014fc7558810004ff745881004cfc7458810004ff7358810044fc735881001cff725881001eef725881002e7f5258810006ef52588100066f525881002eee5258810006ed525881002eec525881002eee425881002eec425881002eee325881002eec325881000cff7158810024fe715881000cfd7158810024fc7158810026ee2158810026ec215881001cff705881001cfe705881001cfd705881001cfc705881001ef8405881001eee205881001eec205881001efa1058810006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef7158810026ee7158810026ec7158810006ef5158810026ee5158810006ed5158810026ec5158810026ee4158810026ec4158810026ee3158810026ec315881001eef705881001eee705881001eed705881001eec705881001eef505881001eee505881001eed505881001eec505881001eef405881001eee405881001eed405881001eec405881001ee8405881001eef305881001eee305881001eed305881001eec305881001eef105881001eee105881001eea105881001eed105881001eec105881022d7f76548100067f76548100047f765481022e7e765481022d7d76548100067d76548100047d765481022e7c765481022e7f64548102467e645481022f3e64548100063e64548100067d645481022f3d64548100063d645481022e7c645481022e7f635481023e7e635481022f5e63548100065e63548100067d635481022f5d63548100065d635481022e7c63548102357f72548100376f725481022e7f625481000e7e625481022f6e625481000e6e625481002e7d625481022f6d62548100066d625481000e7c62548100767
  | 2 => 0x1ebf705901001ebe705901001ebd705901001ebc705901001eb8705901001ebf505901001ebe505901001ebd505901001ebc505901001ebf305901001ebe305901001ebd305901001ebc305901001ebf205901001ebe205901001ebd205901001ebc205901001ebf105901001ebe105901001ebd105901001ebc1059010046df7598c10046de7598c10046dd7598c10046dc7598c10046df7498c10046de7498c10046dd7498c10046dc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c10046df7298c10046de7298c10046dd7298c10046dc7298c10006df5298c100065f5298c10006de5298c10006dd5298c10006dc5298c10006de4298c10006dc4298c10026de7198c10026dc7198c10006df5198c10026de5198c10006dd5198c10026dc5198c10026de4198c10026dc4198c10006df2198c10026de2198c10026dc2198c1001edf7098c1001ede7098c1001edd7098c1001edc7098c1001edf5098c1001ede5098c1001edd5098c1001edc5098c1001edf4098c1001ede4098c1001edd4098c1001edc4098c1001edf2098c1001ede2098c1001edd2098c1001edc2098c1001edf1098c1001ede1098c1001edd1098c1001edc1098c10004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c1004cfc7458c1001cff7358c1001edf7358c10006df5358c10006de5358c10006dd5358c10006dc5358c10004ff7258c1000cfe7258c1000cfc7258c100067f5258c10006de3258c10006dc3258c10044ff7158c10024fe7158c10044fd7158c10024fc7158c10026de3158c10026dc3158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c10006dc5258c10006de4258c10006dc4258c10026de7158c10026dc7158c10006df5158c10026de5158c10006dd5158c10026dc5158c10026de4158c10026dc4158c10006df2158c10026de2158c10026dc2158c1001edf7058c1001ede7058c1001edd7058c1001edc7058c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ede1058c1001edd1058c1001edc1058c1004cff76d0c1001cfe76d0c10004fd76d0c1001cfc76d0c101f67e65d0c100067d65d0c1004ebe64d0c10006bd64d0c10046de63d0c10006dd63d0c101eeee62d0c10044ff769
  | 3 => 0xb61c411001ff361c41100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f72594100047f72594100067e72594100067d72594100067c72594100067e42594100067c42594100067e32594100067c32594100367f71594100267e71594100367d71594100267c71594100267e41594100267c41594100267e31594100267c31594100067f21594100267e21594100267c215941001e7f705941001e7e705941001e7d705941001e7c705941001e7f405941001e7e405941001e7d405941001e7c405941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e7e105941001e7d105941001e7c105941004ebf759901004ebe759901004ebd759901004ebc759901004ebf739901004ebe739901004ebd739901004ebc7399010006bf5399010006be5399010006bd5399010006bc539901004ebf729901004ebe729901004ebd729901004ebc7299010006bf52990100063f5299010006be5299010006bd5299010006bc5299010006be3299010006bc3299010026be7199010026bc7199010006bf5199010026be5199010006bd5199010026bc5199010026be3199010026bc3199010006bf2199010026be2199010026bc219901001ebf709901001ebe709901001ebd709901001ebc709901001ebf509901001ebe509901001ebd509901001ebc509901001ebf309901001ebe309901001ebd309901001ebc309901001ebf209901001ebe209901001ebd209901001ebc209901001ebf109901001ebe109901001ebd109901001ebc1099010004ff7559010014fe7559010004fd7559010014fc755901001cff745901001ebf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff7359010044fc7359010004ff725901000cfe725901000cfc72590100067f5259010006be4259010006bc425901004cff7159010024fe715901004cfd7159010024fc7159010026be4159010026bc415901001cff705901001cfe705901001cfd705901001cfc705901001ef8705901001cf8705901001ebe405901001ebc405901001ef84059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd5259010006bc5259010006be3259010006bc3259010026be7159010026bc7159010006bf5159010026be5159010006bd5159010026bc5159010026be3159010026bc3159010006bf2159010026be2159010026bc2159010
  | 4 => 0xc510006bf64cc510006bc64cc510006df63cc510046dc63cc51001dfa70cc510005f970cc510004fe768c51005d7e758c5100057d758c5100067f658c51012e7c658c510005be748c510005bd748c510006bf648c510006bc648c51001cfc764c5100067f654c51013e7c654c510006bf644c510006bc644c510006df634c510046dc634c510005fb704c51001df8704c510004fe760c5100067f650c5101267c650c510006bf640c510006bc640c510064fe76885100067f65885101167c6588510006bf6488510006bc648851001cfc76485100067f654851010e7c6548510006bf6448510006bc6448510005df7348510005dc7348510006ef624851000eec6248510005fb704851001df87048510004fe76d0110024fc76d011005d7e75d01100057d75d01100067f65d01101067c65d0110006bf64d011004ebc64d0110005f671d0110005f571d011004cff7650110004fd765011004cfc76501100067f65501100e67c6550110006bf645011004ebc6450110005f77150110005f47150110004fe76cc110024fc76cc1100067f65cc1100c67c65cc110006bf64cc110006bc64cc110006df63cc110046dc63cc110005f671cc110005f571cc110044ff764c110004fd764c110044fc764c1100057f754c11005d7c754c1100067f654c1100a67c654c110005bf744c110005bc744c110006bf644c110006bc644c110006df634c110046dc634c110005f7714c110005f4714c110005fa768811001efa76881100077b658811027f786588110007bb6488110276fa6488110276f86488110007b86488110006b8648811001fda738811001fd97388110006fb6388110006f96388110055f9728811000efa628811000ef862881100577b5288110057795288110025fa718811001efb618811001ff3618811000cff7648110054fd764811000cfc76481100067f654811007e7c6548110006bf6448110006bc6448110006ef624811000eec6248110005f77148110005f4714811001fe82048110055f8764811000ef8764811000cf876481100077b654811026f786548110007bb6448110266fa6448110266f86448110007b86448110006b86448110006fb6348110006f9634811001dfb724811001feb7248110007eb624811000efa624811000ef86248110057e862481100577b5248110057795248110007f37148110025f87148110007f0714811001efb614811001ff36148110057eb2148110007e921481100067f65c411003e7c65c4110006bf64c4110006bc64c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c411025f7865c4110007bb64c411020efa64c411020ef864c4110007b864c4110006b864c4110025fb72c4110005f972c411025f7b52c41100077952c411001dfa71c411001ef
  | 5 => 0x4ebc6450d10044ff7610d10004fe7610d10004fd7610d10044fc7610d100067f6510d101c67c6510d10006bf6410d1004ebc6410d1001dfa7010d10005f97010d1000cfe76d891005d7c75d89100067f65d89100067c65d8910006bf64d8910006bc64d8910056ee62d8910004ff75d89100067f75d8910014fe75d8910004fd75d8910014fc75d89100067c75d89100147c75d891004cfe74d8910004fd74d8910044fe73d8910004fd73d89100567f52d8910056ec32d8910024fe71d891001cfd71d8910024fc71d8910056ef21d891001cfe70d8910054fd70d891001cfc70d8910056ef20d89100057f755891005d7c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df7358910005dc7358910056ec6258910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891004cfc7458910006bc745891004cbc7458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc7358910054ff7258910006ef72589100567f5258910064ff7158910006f77158910074ff7058910006fb70589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f64549100073f64549100063f64549102467e64549100067d64549102467c64549100073c64549100063c64549100067f635491023e7e63549100067d635491023e7c63549100557f725491005f6f72549100567f625491000e7e62549100567d625491000e7c625491022f76105491004cff76d0910004fe76d0910004fd76d091004cfc76d09100067f65d09101b67c65d0910006bf64d091004ebc64d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101ae7c6550910006bf645091004ebc6450910044ff76cc910004fe76cc910004fd76cc910044fc76cc9100067f65cc9101a67c65cc910006bf64cc910006bc64cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91019e7c654c910006bf644c910006bc644c91001cfe76d051001cfc76d05100067f65d05101967c65d0510006bf64d051004ebc64d051001dfa70d0510005f970d0510004fe76905100067f659051016e7c6590510006bf649051004ebc649051001cfc76505100057f755051005d7c75505100067f655051017e7c6550510006bf645051004ebc6450510005fb705051001df87050510004fe761051005d7e75105100057d75105100067f65105101667c6510510006bf641051004ebc641051001cfe76cc51001cfc76cc5100067f65cc5101567c65c
  | 6 => 0x77159110004ff7059110006fb7059110004fb7059110004fe76191100067f65191100067c651911004ebe6419110006bd6419110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6219110006bc62191100073f5219110287b61019110287b4101911004ebf751911004ebe751911004ebd751911004ebc751911004ebf731911004ebe731911004ebd731911004ebc7319110006bf5319110006be5319110006bd5319110006bc531911004ebf721911004ebe721911004ebd721911004ebc7219110006bf52191100063f5219110006be5219110006bd5219110006bc5219110006be3219110006bc321911004ebf711911004ebd7119110006bf5119110006be5119110006bd5119110006bc5119110006bf2119110006bc211911004ebf701911004ebe701911004ebd701911004ebc7019110006bf5019110286be5019110006bd5019110286bc5019110286be3019110286bc3019110006bf2019110286be2019110286bc2019110286be1019110006bd1019110286bc1019110044fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d1004cfe74d8d10004fd74d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d10006de32d8d10006dc32d8d10024fe71d8d10024fc71d8d1001cfe70d8d1001cfc70d8d1005d7e7598d100057d7598d100067f6598d100067c6598d10005be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1004cfc7458d10006bc7458d1004cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10046de6318d10006dd6318d1004cff76d0d10004fe76d0d10004fd76d0d1004cfc76d0d100067f65d0d101f67c65d0d10006bf64d0d1004ebc64d0d10044ff7690d10004fe7690d10004fd7690d10044fc7690d100067f6590d101e67c6590d10006bf6490d1004ebc6490d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d1005d7c7550d100067f6550d101d67c6550d10006bf6450d10
  | 7 => 0x821000efa624821001ef8624821001fe862482100677b5248210067795248210025f87148210067eb2148210007e9214821001df976c4210026f976c421020efa64c421001ef864c4210025fb72c4210005f972c421029f7b52c42100077952c421001ff271c421005d7e76d951005e7e76d95100147e76d95100057d72d95100067e62d95100067c62d95102977610d95102977410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067e42d95100067c42d95100067e32d95100067c32d95102967f71d951005e7e71d951005e7d71d951005e7c71d95100067f21d95100067c21d95100067f70d95102967e70d951005e7d70d95102967c70d95102967e40d95102967c40d95102967e30d95102967c30d95100067f20d95102967e20d95102967c20d95102967e10d951005e7d10d95102967c10d951004cfe76d91100067f65d91100067c65d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110044fe73d9110004fd73d911000cfe72d9110004fd72d911000cfc72d91100067f52d9110006be42d9110006bc42d9110024fe71d9110024fc71d911001cfe70d911001cfc70d911004cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d91100073f52d911028fb610d911028fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d911028ebf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf21d9110006bc21d9110006bf70d911028ebe70d9110006bd70d911028ebc70d9110006bf50d911028ebe50d9110006bd50d911028ebc50d911028ebe30d911028ebc30d9110006bf20d911028ebe20d911028ebc20d911028ebe10d911028ebc10d911005d7e75991100057d75991100067f65991100067c6599110006bf64991100057f755911005d7c75591100067f65591100067c6559110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110004ff7359110044fc7359110004ff725911000cfe725911000cfc72591100067f5259110004ff7159110006f
  | 8 => 0x14fc755921001ebf7459210004ff7359210044fc7359210004ff725921000cfe725921000cfc72592100067f525921001cfc705921001ebe405921001ebc4059210004ff7558e100067f7558e100047f7558e10014fe7558e10004fd7558e10014fc7558e100067c7558e100147c7558e10004ff7458e10006bf7458e10004bf7458e1004cfc7458e10006bc7458e1004cbc7458e1001edf7358e10004ff7258e1000cfe7258e1000cfc7258e100067f5258e10006de3258e10006dc3258e1001cfc7058e1001ede3058e1001edc3058e1001efa2058e1004cff76d0e1001cfe76d0e10004fd76d0e1001cfc76d0e10044ff7690e1001cfe7690e10004fd7690e1001cfc7690e10256bf6490e1004ebc6490e10046de6390e10006dd6390e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e100057f7550e1006d7c7550e10046de6350e10006dd6350e10044ff7610e1001cfe7610e10004fd7610e1001cfc7610e1024ebf6410e1004ebc6410e1001dfa7010e10005f97010e10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1004cfc7458a10004ff7358a10044fc7358a1001eef7258a100667f5258a10066ef2158a1001cfc7058a1001eee2058a1001eec2058a100067f7654a1022e7e7654a100067d7654a1022e7c7654a1022e7f6454a102467e6454a100067d6454a1022e7c6454a1022e7f6354a1023e7e6354a100067d6354a1022e7c6354a102357f7254a1006f6f7254a1022e7f6254a1000e7e6254a100667d6254a1000e7c6254a100567d6154a1022e7e6054a1022f7a2054a1022f771054a1004cff76d0a1001cfe76d0a10004fd76d0a1001cfc76d0a10226bf64d0a1004ebc64d0a10004ff7650a1001cfe7650a10004fd7650a1001cfc7650a1021ebf6450a1004ebc6450a10044ff76cca1001cfe76cca10004fd76cca1001cfc76cca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca10005f7714ca10005f4714ca1004ebe64d0610006bd64d061001dfa70d0610005f970d061028ebf649061004ebc649061004cff76506100057f755061006d7c755061004ebe6450610006bd6450610005fb705061001df8705061006d7e75106100057d7510610286bf641061004ebc6410610046de63cc610006dd63cc61001dfa70cc610005f970cc61006d7e758c6100057d758c610005be748c610005bd748c610044ff764c610046de634c610006dd634c610005fb704c61001df8704c610007d5310c610054fd768861001df8708861000cff764861001cfc7648610005df7348610005dc734861000eee6248610006ed6248610005fb704861001df8704861001dfb764821002efb7648210266fa644821001ef8644821001efb6348210006f9634821001feb724821001feb624
  | 9 => 0xd75d8b10024fc75d8b1004cfe74d8b10004fd74d8b10044fe73d8b10004fd73d8b10074fd72d8b100767f52d8b10026f671d8b10026ef21d8b10026f970d8b1000cff7658b10005df7358b10005dc7358b10026ec6258b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1004cfc7458b10004ff7358b10006df7358b10004df7358b10044fc7358b10006dc7358b10044dc7358b10026ef7258b100767f5258b1001cfc7158b10026ee2158b10026ec2158b10076ef2058b100067f7654b100067e7654b100067d7654b100067c7654b100067f6454b102467e6454b100067d6454b102467c6454b100067f6354b1023e7e6354b100067d6354b1023e7c6354b100757f7254b1003f6f7254b100767f6254b1000e7e6254b100767d6254b1000e7c6254b100077b7054b10007787054b1004cff76d0b10024fe76d0b10004fd76d0b10024fc76d0b1004ebe64d0b10006bd64d0b10004ff7650b10024fe7650b10004fd7650b10024fc7650b1004ebe6450b10006bd6450b10005fb7050b1001df87050b10044ff76ccb10024fe76ccb10004fd76ccb10024fc76ccb10046de63ccb10006dd63ccb10004ff764cb10024fe764cb10004fd764cb10024fc764cb10046de634cb10006dd634cb10026bf64d0710026bc64d07100057f755071003d7c7550710026bf6450710026bc645071001df87050710026df63cc710026dc63cc710026df634c710026dc634c71002cff7648710005df7348710005dc7348710026ef6248710026ec624871003d7e75d03100057d75d031004ebe64d0310006bd64d0310025f671d0310005f571d0310005f976d031020ef976d031020f7a75d031020f7975d031001dfa74d031020efb64d031020fba64d031020ef964d0310007b964d0310006fb62d0310006f962d03102b77b52d03100077952d031020ff271d0310005f971d031020ff171d031001efa61d031020fbb41d0310007b941d031004cff765031004ebe6450310006bd6450310005f77150310025f4715031001fb84050310005f9761031001ef9761031001fba741031020efb64103102a7bb641031020ef964103102a7b8641031020fba54103102afb9541031001fda731031001fd97310310007ba431031020fb84310310006fb6210310006f962103102af7b521031000779521031020fbb4210310007b94210310005f9711031001ff261103102a7ba41103102a7b84110310046de63cc310006dd63cc310025f671cc310005f571cc310044ff764c3100057f754c31003d7c754c310005bf744c310005bc744c310046de634c310006dd634c310005f7714c310025f4714c31000cff7648310024fc764831000eee6248310006ed6248310005f77148310025f47148310004ff7559210014fe7559210004fd7559210
  | 10 => 0xc12001df8748c12009df9738c120046fa638c120046f8638c12000dfa728c12001df8728c12001efb628c12001feb628c1200af7b528c1200af79528c120005f9718c1200afeb218c120007e9218c120044ff764c12000cfe764c12009cfd764c12000cfc764c1200057f754c12007d7c754c120005bf744c120005bc744c120006df634c120046dc634c120005ef724c12000dec724c12000df8764c120046f8764c12000cf8764c1200077b754c1202bf78754c120007bb744c120265fa744c120265f8744c120007b8744c120005b8744c12001dfb734c12001fdb734c120007db634c120046fa634c120046f8634c120007d8634c120007da434c120007d9434c120007eb724c12000dfa724c12000df8724c12009fe8724c12000de8724c12001efb624c12001feb624c12009f7b524c12009f79524c12009fda324c12009fd8324c120005fb714c120007db314c120007d9314c12009feb214c120007e9214c120024ff75d9310014fe75d9310004fd75d9310024fc75d9310044fe73d9310004fd73d931000cfe72d9310004fd72d9310024fc72d93100067f52d9310026f671d9310026f970d931028ebe40d931028ebc40d9310004fd7699310026bf6499310026bc649931004cff76593100057f755931003d7c7559310026bc6459310004ff75593100067f75593100047f7559310014fe7559310004fd7559310014fc75593100067c75593100147c7559310026bf7459310006be5459310006bd5459310004ff7359310044fc7359310004ff725931000cfe725931000cfc72593100067f525931001cfc7159310026be4159310026bc4159310006fb7059310024ff75d8f10014fe75d8f100267e75d8f100147e75d8f10004fd75d8f100267d75d8f100047d75d8f10024fc75d8f1004cfe74d8f10026be74d8f1004cbe74d8f10004fd74d8f10026bd74d8f10004bd74d8f1000cfe72d8f10004fd72d8f10024fc72d8f100067f52d8f10006de32d8f10006dc32d8f10026f671d8f10026f970d8f10004fd7698f10026df6398f10026dc6398f10044ff7658f10026dc6358f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f1004cfc7458f10026df7358f10004ff7258f1000cfe7258f1000cfc7258f100067f5258f1001cfc7158f10026de3158f10026dc3158f1004cff76d0f10024fe76d0f10004fd76d0f10024fc76d0f10044ff7690f10024fe7690f10004fd7690f10024fc7690f1004ebe6490f10006bd6490f1001dfa7090f10005f97090f10004ff7650f10024fe7650f10004fd7650f10024fc7650f100057f7550f1003d7c7550f10005fb7050f1001df87050f10044ff7610f10024fe7610f10004fd7610f10024fc7610f1004ebe6410f10006bd6410f10024ff75d8b10014fe75d8b10004f
  | 11 => 0x1cfc7018520004fe76d0520004fd76d052004cfc76d052004ebe64d0520006bd64d0520004fe7690520004fd7690520024fc7690520006bf649052004ebc649052000dee7290520005ed729052001dfa7090520005f97090520004ff7650520004fe7650520004fc76505200057f755052007d7c755052004ebe6450520006bd6450520005fb705052001df87050520004fe7610520004fd7610520024fc761052007d7e75105200057d7510520006bf641052004ebc641052000dee7210520005ed721052001dfa7010520005f97010520004fe76cc520004fd76cc520044fc76cc520046de63cc520006dd63cc520006f761cc520006f461cc52001dfa70cc520005f970cc520004fe768c520004fd768c520024fc768c52007d7e758c5200057d758c520005be748c520005bd748c520006df638c520046dc638c52000dee728c520005ed728c52001dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520046de634c520006dd634c520004fe760c520004fd760c520024fc760c520006df630c520046dc630c52000dee720c520005ed720c520006f7610c520026f4610c52001dfa700c520005f9700c52001cec7648520007cf7348520007cc734852000def714852000fe77148520007e76148520026ec6148520007e46148520007e63148520007e53148520007eb704852001dee704852001dec7048520007e8704852000eef604852000feb604852000cfe76d012000cfc76d012007d7e75d01200057d75d0120006bf64d012004ebc64d012000dee72d0120005ed72d012000dfa76d01200fefa76d012000cfa76d01202677a75d01202677975d012001dfa74d0120266fb64d0120007bb64d0120266f964d0120267b864d0120005f973d012000dfa72d01200ffea72d0120267e972d012000df872d012001efb62d012001feb62d01200ff7b52d01200ff7952d0120005f971d0120006f861d0120267bb41d0120007b941d01200ffeb21d0120007e921d012004cff765012000cfe76501200dcfd765012000cfc7650120006bf645012004ebc6450120005ef725012000dec725012001fb840501200edfa761012001efa76101200fdfa741012001fba7410120266fb6410120267ba6410120266f96410120007b96410120267ba54101202c7b9541012001fda7310120005f9731012001fd97310120005d97310120007ba4310120267b8431012000dfa721012001df8721012001efb621012001feb62101200cf7b52101200cf7952101200cfbb42101200cfb94210120005f97110120006f86110120007ba4110120267b841101200cfeb2110120007e9211012000cfe76cc12000cfc76cc120006df63cc120046dc63cc12000dee72cc120005ed72cc12001fe820cc12008dfa768c12001efa768c120265fa748
  | 12 => 0x970d912007d7e75991200057d7599120006bf64991200ddf970991200fdfb7059120004ff7559120014fe7559120004fd7559120014fc7559120006bf7459120004ff7359120044fc73591200dcff7259120006ef72591200de7f52591200de7d5259120004ff7159120024fc71591200fcff7059120006fb705912021ebe405912021ebc40591200ecfe761912004ebe6419120006bd6419120044fe76d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d2004cfe74d8d20004fd74d8d2001cff72d8d2000cfe72d8d2001cfd72d8d2000cfc72d8d200ae7f52d8d200ae7d52d8d200aedf32d8d200aedd32d8d20024fe71d8d20004fd71d8d20006df6398d2009df97098d200057f7558d2007d7c7558d20005bf7458d20005bc7458d20005f77158d20005f47158d200bdfb7058d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d2004cfc7458d20006bc7458d2004cbc7458d20006df7358d2009cff7258d20006ef7258d2009e7f5258d2009e7d5258d2009ede3258d2009edc3258d20004ff7158d20006f77158d20004f77158d20024fc7158d20006f47158d20004f47158d200bcff7058d20006fb7058d200acfe7618d20046de6318d20006dd6318d2004cff76d0d20004fe76d0d20004fd76d0d2004cfc76d0d20044ff7690d20004fe7690d20004fd7690d20044fc7690d20006bf6490d2004ebc6490d2001dfa7090d20005f97090d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d2007d7c7550d20005ef7250d2000dec7250d20005fb7050d2001df87050d20044ff7610d20004fe7610d20004fd7610d20044fc7610d20006bf6410d2004ebc6410d2001dfa7010d20005f97010d20004ff75d8520014fe75d8520004fd75d8520014fc75d852004cfe74d8520004fd74d8520044fe73d8520004fd73d852001cfd72d85200667f52d85200667d52d8520066f621d8520066f521d8520006f76198520055f970985200057f755852007d7c7558520005bf7458520005bc7458520005df7358520005dc7358520075fb705852007d7e75185200057d7518520005be7418520005bd7418520005de7318520005dd7318520006f56118520024ff7518520014fe75185200267e75185200147e7518520004fd75185200267d75185200047d7518520024fc751852004cfe7418520026be741852004cbe7418520004fd7418520026bd7418520004bd7418520044fe7318520026de7318520044de7318520004fd7318520026dd7318520004dd731852001cfd721852002e7f521852002e7d5218520026ef2118520026f6211852002ef5211852001cfe7018520026f97018520
  | 13 => 0x8620076f5219862001cfe709862001efa709862001cfa709862001cfc709862001ef8409862001ef6109862001efa109862001ef41098620004ff75586200067f75586200047f7558620014fe7558620004fd7558620014fc75586200067c75586200147c7558620004ff745862004cfc7458620004ff7358620044fc73586200567f52586200567d525862001ef77158620056f62158620056f5215862001cfc705862001eef205862001eed205862001ef6105862001ef4105862004cff76d062001cfe76d0620004fd76d062004ebe64d0620006bd64d0620006de63d0620006dd63d062001df870d0620024ff769062001cfe7690620004fd7690620006de6390620006dd639062001dfa7090620005f9709062028fb84090620004ff7650620004fd765062001cfc76506200057f75506200857c755062004ebe6450620006bd6450620006de6350620006dd6350620005fb705062001df87050620024ff761062001cfe7610620004fd76106200857e75106200057d7510620006de6310620006dd631062001dfa7010620005f97010620287b84010620044ff76cc62001cfe76cc620004fd76cc620046de63cc620006dd63cc62001dfa70cc620005f970cc620024ff768c62001cfe768c620004fd768c6200857e758c6200057d758c620005be748c620005bd748c620046de638c620006dd638c62001dfa708c620005f9708c620004ff764c620004fd764c62001cfc764c620046de634c620006dd634c620005ef724c62000dec724c62001dfa704c620024ff760c62001cfe760c620004fd760c620046de630c620006dd630c62001dfa700c620005f9700c62001df976d0220276f976d02202777a75d02202777975d022001fba74d022001efb64d0220276f964d0220005f973d022001fda63d022001fd963d022000dfa72d022000df872d02200ff7b52d02200ff7952d0220005f971d0220006fa61d0220277bb41d0220007b941d022001dfb764c220006fb764c2200077b754c2202cf78754c220007bb744c220275fa744c220275f8744c220007b8744c220005b8744c22001fdb734c220046fa634c22001fda634c220046da634c22001fd9634c22001ef8634c220007da434c220007d9434c22000dfa724c22000df8724c22009f7b524c22009f79524c22009fda324c22009fd8324c220005fb714c220007db314c220007d9314c22004cfe76d912007d7e75d91200057d75d9120004ff75d9120014fe75d91200067e75d91200147e75d9120004fd75d91200067d75d91200047d75d9120014fc75d9120006be54d9120006bd54d9120044fe73d9120004fd73d912001cff72d912000cfe72d912001cfd72d912000cfc72d91200ee7f52d91200ee7d52d91200eebf42d91200eebd42d9120024fe71d9120004fd71d91200eef
  | 14 => 0xbe5d5298e200bedc5298e200bedf4298e200bede4298e200bedd4298e200bedc4298e20046df7198e20046de7198e20046dd7198e20046dc7198e20006df5198e20006de5198e20006dd5198e20006dc5198e200bedf2198e200bede2198e200bedd2198e200bedc2198e2001edf7098e2001ede7098e2001eda7098e2001edd7098e2001edc7098e2001edf5098e2001ede5098e2001edd5098e2001edc5098e2001edf4098e2001ede4098e2001edd4098e2001edc4098e2001edf2098e2001ede2098e2001edd2098e2001edc2098e2001edf1098e2001ede1098e2001edd1098e2001edc1098e20004ff7558e200067f7558e200047f7558e20014fe7558e20004fd7558e20014fc7558e200067c7558e200147c7558e20004ff7458e2004cfc7458e2001edf7358e20006df5358e20006de5358e20006dd5358e20006dc5358e2009e7f5258e2009e7d5258e2009edf3258e2009edd3258e20004ff7158e20024fc7158e2001cfe7058e2001cfc7058e2001ede3058e2001edc3058e20006df7558e200065f7558e20006de7558e20006dd7558e20006dc7558e200065c7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e2009edf7258e2009ede7258e2009edd7258e2009edc7258e2009edf5258e2009e5f5258e2009ede5258e2009edd5258e2009e5d5258e2009edc5258e2009edf4258e2009ede4258e2009edd4258e2009edc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006de5158e20006dd5158e20006dc5158e2009edf2158e2009ede2158e2009edd2158e2009edc2158e2001edf7058e2001ede7058e2001edd7058e2001edc7058e2001edf5058e2001ede5058e2001edd5058e2001edc5058e2001edf4058e2001ede4058e2001edd4058e2001edc4058e2001edf2058e2001ede2058e2001edd2058e2001edc2058e2001edf1058e2001ede1058e2001edd1058e2001edc1058e2004cff76d0e2001cfe76d0e20004fd76d0e2001cfc76d0e20046de63d0e20006dd63d0e2001df870d0e20044ff7690e2001cfe7690e20004fd7690e2001cfc7690e20046de6390e20006dd6390e2001dfa7090e20005f97090e20257b84090e20004ff7650e2001cfe7650e20004fd7650e2001cfc7650e200057f7550e200857c7550e20046de6350e20006dd6350e20005fb7050e2001df87050e20044ff7610e2001cfe7610e20004fd7610e2001cfc7610e20046de6310e20006dd6310e2001dfa7010e20005f97010e2024fb84010e20024ff7598620014fe7598620004fd7598620024fc759862004cfe7498620004fd7498620044fe7398620004fd73986200767f52986200767d529862001ef67198620026f6219
  | 15 => 0xf7159030024fc715903001cfe705903001cfc705903001ebe405903001ebc405903001edf305903001edd3059030004ff7558830014fe7558830004fd7558830014fc7558830004ff745883004cfc745883000cfd735883001cff725883001eef725883008e7f5258830046ef3258830046ec3258830004ff7158830024fc715883008eef215883001cfc705883001efa3058830046f9305883001eee205883001eec20588300067f765483022e7e76548300067d765483022e7c765483022e7f64548302467e64548300067d645483022e7c64548300be7e63548302357f72548300976f725483022e7f625483000e7e625483008e7d625483000e7c625483022e7e605483022f5f305483022f7a305483022f5d305483023f79305483004cff76d083001cfe76d0830004fd76d083004ebe64d0830006bd64d0830004ff7650830004fd765083001cfc765083004ebe6450830006bd6450830024ff7598430014fe7598430004fd7598430024fc759843004cfe7498430004fd749843000cfe7298430004fd7298430024fc72984300067f52984300067d529843001cfe719843001ef67198430046f73198430026f4319843001ef6109843001ef41098430004ff7558430014fe7558430004fd7558430014fc7558430004ff745843004cfc7458430004ff725843000cfe725843000cfc72584300067f52584300067d525843001ef77158430046f73158430046f4315843001edf305843001edd305843001ef6105843001ef4105843004cff76d043001cfe76d0430004fd76d043004ebe64d0430006bd64d0430024ff769043001cfe7690430004fd7690430004ff7650430004fd765043001cfc76504300057f75504300957c755043004ebe6450430006bd6450430005fb705043001df87050430024ff761043001cfe7610430004fd76104300957e75104300057d7510430024ff768843001cfe7688430004fd7688430026f66188430006f56188430004ff7648430004fd764843001cfc7648430005df7348430045dc734843000eee6248430006ed6248430006f66148430006f56148430004ff7559220014fe7559220004fd7559220014fc755922001ebf7459220006bf5459220006bc5459220004ff7359220044fc73592200de7f52592200de7d52592200debf42592200debd4259220004ff7159220024fc715922001cfe705922001cfc705922001ef8705922001cf8705922001ebe405922001ebc405922001ef84059220046df7598e20046de7598e20046dd7598e20046dc7598e20046df7498e20046de7498e20046dd7498e20046dc7498e20006df5498e20006de5498e20006dd5498e20006dc5498e20046df7298e20046de7298e20046dd7298e20046dc7298e200bedf5298e200be5f5298e200bede5298e200bedd5298e20
  | 16 => 0x8530004fe76d0530004fd76d053004cfc76d05300067f65d05301967c65d0530006bf64d053004ebc64d0530045de73d0530005dd73d05300079e43d0530004fe7690530004fd7690530024fc76905300067f659053016e7c6590530006bf649053004ebc6490530045de7390530005dd7390530004ff7650530004fe7650530004fc76505300057f75505300a57c75505300067f655053017e7c6550530006bf645053004ebc64505300079e4350530005fb705053001df87050530004fe7610530004fd7610530024fc76105300a57e75105300057d75105300067f65105301667c6510530006bf641053004ebc6410530045de7310530005dd731053001dfa7010530005f97010530005de76cc530046de76cc5300075f65cc5302e75c65cc530045df74cc530005dd74cc5300079f64cc5300079c64cc53009dde72cc530045dc72cc530006df62cc5302e75f52cc5300075d52cc530026dc61cc53001dde70cc53001ddc70cc530046df60cc530047db60cc53001cfe768c5300a57e758c5300057d758c5300067f658c53012e7c658c530005be748c530005bd748c530006bf648c530006bc648c5302dddd738c530006f7618c530026f4618c53001dfa708c530005f9708c53001cfc764c5300067f654c53013e7c654c530006bf644c530006bc644c530006f7614c530006f4614c530005fb704c53001df8704c53001cdc764c5300075f654c5302d75c654c530005df744c530005dd744c5300079f644c5300079c644c53009dde724c53009ddc724c530006df624c5302d75f524c5300075d524c530045df714c530047d7714c530007d7614c530026dc614c530007d4614c530006d4614c530007db704c53001dde704c53001ddc704c530007d8704c530046df604c530047db604c530004fe7688530004fd7688530024fc76885300067f65885301167c6588530006bf6488530006bc6488530045de7388530005dd7388530006ef628853000eec6288530007d53188530004ff7648530004fe7648530004fc76485300067f654853010e7c6548530006bf6448530006bc6448530005df7348530045dc7348530007d53148530044fe76d0130044fc76d01300a57e75d01300057d75d01300067f65d01301067c65d0130006bf64d013004ebc64d0130045de73d0130005dd73d013004cff7650130004fd7650130044fc76501300067f65501300e67c6550130006bf645013004ebc6450130005df7350130045dc735013001fb8405013001fd83050130004ff7559030014fe7559030004fd7559030014fc755903001cff745903001ebf7459030006bf5459030006bc5459030044ff7359030044fe7359030044fd7359030044fc7359030046be4359030046bc4359030004ff725903000cfe725903000cfc72590300067f5259030004f
  | 17 => 0x479f7450d300079f6450d3004ede6450d3004edc6450d300079c6450d3009dde7250d3009ddc7250d302ef5f5250d30005df7150d30007db7050d3001dde7050d3001ddc7050d30007d87050d30046df6050d30047db6050d3000cfe76d89300a57c75d89300067f65d89300067c65d8930006bf64d8930006bc64d8930045de73d893009eee62d893009fce32d8930004ff75d89300067f75d8930014fe75d8930004fd75d8930014fc75d89300067c75d89300147c75d893004cfe74d8930004fd74d893001cfd73d893001cdd73d893000cfc73d893009e7f52d893009ede32d893009eee32d893009edc32d8930024fe71d8930004fd71d893009eec21d8930044fd70d893009eef20d89300057f75589300a57c75589300067f65589300067c6558930005bf7458930005bc7458930006bf6458930006bc645893009eec6258930005f77158930005f471589300067f76549300057e76549300067e76549300047e76549300067d76549300057c76549300067c76549300047c76549300067f64549300073f64549300063f64549302467e64549300067d64549302467c64549300073c64549300063c64549300075f73549300075c73549300075e43549300075d435493009d7f72549300a76f725493009e7f625493000e7e625493000e7c625493009f5e325493009f5c325493023f7b305493022f5e3054930004fe76d0930004fd76d093004cfc76d09300067f65d09301b67c65d0930006bf64d093004ebc64d0930045de73d0930005dd73d09300079d43d0930004ff7650930004fe7650930004fc76509300067f65509301ae7c6550930006bf645093004ebc6450930005df7350930045dc73509300079d435093001cfc764c9300067f654c93019e7c654c930006bf644c930006bc644c93009ddf734c930006ef624c93000eec624c930005fb704c93001df8704c9300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d8530014fe75d8530004fd75d8530014fc75d853004cfe74d8530004fd74d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006f721d8530006f421d85300a57e75985300057d75985300067f65985300067c6598530005be7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300a57c75585300067f65585300067c6558530005bf7458530005bc7458530006bf6458530006bc6458530005ef725853009dec72585300067f65185300067c6518530006bf6418530006bc6418530006f56118530024ff7518530014fe7518530004fd7518530024fc751853004cfe7418530004fd741853000cfe7218530004fd7218530024fc72185300067f52185300067d5218530006de3218530006dc3218530006f72118530026f4211
  | 18 => 0xf70d9130256be70d9130006bd70d9130256bc70d9130006bf50d9130256be50d9130006bd50d9130256bc50d913030ebf30d9130256be30d9130256bc30d9130006bf20d9130256be20d9130256bc20d9130256be10d9130256bc10d91300a57e75991300057d75991300067f65991300067c6599130006bf64991300057f75591300a57c75591300067f65591300067c6559130004ff75591300067f75591300047f7559130014fe7559130004fd7559130014fc75591300067c75591300147c7559130006bf7459130004ff7359130006df7359130004ff725913000cfe725913000cfc72591300067f5259130004ff7159130024fc7159130004ff7059130006fb7059130004fe76191300067f65191300067c651913004ebe6419130006bd6419130005be7619130006be7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c65191300079d7319130006be6219130006bc62191300073f52191300079e32191300079c3219130307bb301913024f9e301913024f9c3019130307b8301913004ebf751913004ebe751913004ebd751913004ebc751913004ebf731913004ebe731913004ebd731913004e9d731913004ebc7319130006bf5319130306be5319130006bd5319130306bc531913004ebf721913004ebe721913004ebd721913004ebc7219130006bf52191300063f5219130006be5219130006bd5219130006bc5219130306bf3219130006be3219130306bc321913004ebf711913004ebe711913004ebd711913004ebc7119130006bf5119130006be5119130006bd5119130006bc5119130306bf3119130306bc3119130006bf2119130006bc211913004ebf701913004ebe701913004ebd701913004ebc7019130006bf501913024ebe5019130006bd501913024ebc5019130306bf301913024ebe3019130006bd301913024ebc3019130006bf201913024ebe201913024ebc201913024ebe101913024ebc101913001cfe76d0d3001cfc76d0d300067f65d0d301f67c65d0d30006bf64d0d3004ebc64d0d3001dfa70d0d30005f970d0d30005de7690d30046de7690d300075f6590d302f75c6590d302fddd7490d300079f6490d3004ede6490d3004edc6490d300079c6490d3004e9c6490d3009dde7290d30045dc7290d302f75f5290d30005dd7190d3001dde7090d3001ddc7090d30046df6090d30047db6090d302579e4090d302579c4090d3001cfc7650d300057f7550d300a57c7550d300067f6550d301d67c6550d30006bf6450d3004ebc6450d300479c4350d30005fb7050d3001df87050d30047d83050d3001ddc7650d3004edc7650d3001cdc7650d300075f7550d302ef5c7550d300075f6550d302ef5c6550d30045df7450d30
  | 19 => 0x630004ff7650630004fd765063001cfc76506300057f75506300b57c755063004ebe6450630006bd6450630005fb705063001df87050630024ff761063001cfe7610630004fd76106300b57e75106300057d751063001dfa7010630005f970106300b57e758c6300057d758c630005be748c630005bd748c630026f6618c630006f5618c63001dfa708c630005f9708c630006f6614c630006f5614c630047d4314c630005fb704c63001df8704c630024ff768863001cfe7688630004fd7688630004ff7648630004fd764863001cfc7648630005df7348630045dc734863000eee6248630006ed62486300a57e76d95300a67e76d95300147e76d95300057d72d95300067e62d95300067c62d95300075e32d95300075c32d953031f7b30d95303175e30d95303175c30d953031f7830d95300067f74d95300067e74d95300067d74d95300067c74d95303167f73d953031e7e73d95300a67d73d953031e7c73d953031e7e43d953031e7c43d95300067f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067e42d95300067c42d953031e7f32d95300067e32d953031e7c32d95300067f71d95300067e71d95300067d71d95300067c71d953031e7f31d953031e7c31d95300067f21d95300067c21d953031e7f70d95303167e70d95300a67d70d95303167c70d95303167e40d95303167c40d953031e7f30d95303167e30d95300a67d30d95303167c30d95300067f20d95303167e20d95303167c20d95303167e10d95303167c10d953004cfe76d91300067f65d91300067c65d9130004ff75d9130014fe75d9130004fd75d9130014fc75d9130006bf54d9130006be54d9130006bd54d9130006bc54d9130044fe73d9130044fc73d913000cfe72d9130004fd72d913000cfc72d91300067f52d9130006be42d9130006bc42d9130024fe71d9130004fd71d913004cbe76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91302579f73d9130006be62d9130006bc62d91300073f52d91300079e32d91300079c32d913030fbb30d91302579e30d91302579c30d913030fb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130256bf73d913030ebe73d9130006bd73d913030ebc73d9130006bf53d913030ebe53d9130006bd53d913030ebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d9130006bc52d913030ebf32d9130006be32d913030ebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d913030ebf31d913030ebc31d9130006bf21d9130006bc21d913030eb
  | 20 => 0x57d751073004ebe6410730006bd6410730045de7310730005dd7310730045df764c730006df764c730005df744c730005dd744c7300bdde724c7300bddc724c730006dd624c7303275f524c7300075d524c730047d7714c730026de614c73001dde704c73001ddc704c730024ff7688730044fe7688730004fd7688730045de7388730005dd7388730026f66188730006f56188730007d53188730004ff7648730004fd7648730044fc7648730005df7348730045dc7348730006f66148730006f56148730007d531487300c57e75d03300057d75d033004ebe64d0330006bd64d0330045de73d0330005dd73d033004cff765033004ebe6450330006bd6450330005df7350330045dc7350330004ff7559230014fe7559230004fd7559230014fc755923001ebf7459230004ff725923000cfe725923000cfc72592300067f5259230004ff7159230024fc715923001cfc705923001ebe405923001ebc405923001edf305923001edd305923004ebe64d0e30006bd64d0e3001dfa70d0e30005f970d0e3004cff7650e300057f7550e300b57c7550e3004ebe6450e30006bd6450e30005fb7050e3001df87050e30004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a3004cfc7458a3001eef7258a300ae7f5258a300aeee5258a30006ed5258a300aeec4258a300aeee3258a30004ff7158a30024fc7158a300aeef2158a3001cfc7058a3001eee2058a3001eec2058a300067f7654a3022e7e7654a300067d7654a3022e7c7654a3022e7f6454a302467e6454a300067d6454a3022e7c6454a3009e7d6354a302357f7254a300b76f7254a3022e7f6254a3000e7e6254a3022f6e6254a3000e6e6254a300ae7d6254a3022f6d6254a300066d6254a3000e7c6254a3022e7e6054a3022f5f3054a3023f7b3054a3022f7a2054a3004cff76d0a3001cfe76d0a30004fd76d0a30226bf64d0a3004ebc64d0a3000eee62d0a30006ed62d0a30004ff7650a30004fd7650a3001cfc7650a3021ebf6450a3004ebc6450a3000cff764ca3000eee624ca30006ed624ca30005fb704ca3001df8704ca30024ff7598630014fe7598630004fd7598630024fc759863004cfe7498630004fd749863000cfe7298630004fd7298630024fc72986300067f52986300067d529863001ef6719863001cfe709863001ef6109863001ef41098630004ff7558630014fe7558630004fd7558630014fc7558630004ff745863004cfc7458630004ff725863000cfe725863000cfc72586300067f52586300067d525863001ef7715863001cfc705863001edf305863001edd305863001efa205863001ef6105863001ef4105863004cff76d063001cfe76d0630004fd76d063004ebe64d0630006bd64d0630024ff769063001cfe7690630004fd769
  | 21 => 0xc7348440006de6348440006dd634844000eee6248440006ed6248440006f66148440006f56148440005fb704844001df87048440004ff75593300067f75593300047f7559330014fe7559330004fd7559330014fc75593300067c75593300147c7559330046bf7459330006be5459330006bd545933001cfc7359330046be4359330046bc4359330004ff725933000cfe725933000cfc72593300067f5259330004ff7159330024fc7159330045df7650f30006df7650f300075f7550f3033f5c7550f300479f7450f3004ede6450f30046dc6450f300bdde7250f300bddc7250f3033f5f5250f30005df7150f3001dde7050f3001ddc7050f30004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3004cfc7458b3001cfc7358b3001cdc7358b30046ef7258b300be7f5258b30046ef3258b300bede3258b30046dc3258b30046ec3258b30004ff7158b30024fc7158b30046df3158b30046fa3058b30046f93058b300beef2058b300067f7654b3023e7e7654b300067d7654b3023e7c7654b3023e7f6454b302467e6454b300067d6454b3023e7c6454b300075f7354b3023f5c7354b3023f5e4354b300075d4354b300bd7f7254b300c76f7254b300be7f6254b3000e7e6254b300be7d6254b3000e7c6254b300bf5e3254b300bf5c3254b3023f5f3154b3004cff76d0b30044fe76d0b30004fd76d0b3004ebe64d0b30006bd64d0b30045de73d0b30005dd73d0b300079d43d0b30004ff7650b30004fd7650b30044fc7650b3004ebe6450b30006bd6450b30005df7350b30045dc7350b300079d4350b30024ff7598730014fe75987300267e75987300147e7598730004fd75987300267d75987300047d7598730024fc759873004cfe7498730026be749873004cbe7498730004fd7498730026bd7498730004bd749873001cfe739873001cde739873000cfe7298730004fd7298730024fc72987300067f52987300067d5298730006de3298730046dc3298730026f67198730026df3198730046f73198730026f43198730004ff7558730014fe7558730004fd7558730014fc7558730004ff745873004cfc745873001cfc7358730004ff725873000cfe725873000cfc72587300067f52587300067d5258730046f77158730046f73158730046f4315873004cff76d0730044fe76d0730004fd76d0730336bf64d073004ebc64d0730045de73d0730005dd73d07303379e43d0730024ff7690730044fe7690730004fd769073004ebe6490730006bd6490730045de7390730005dd7390730004ff7650730004fd7650730044fc76507300057f75507300c57c755073032ebf645073004ebc6450730045de735073032f9e4350730005fb705073001df87050730024ff7610730044fe7610730004fd76107300c57e7510730
  | 22 => 0x484022f6d62548400066d625484000e7c62548400cf3f42548402473c415484022e7e605484022f3f405484022f7a405484022f3d405484024779405484022f7a205484004dbf76508400febf7650840355bf7550840355bd7550840305bc735084004f9e6350840006bd635084004f9d63508400069d635084004dbf725084004faf725084000ebe625084000ebc62508400cf3f52508400cf3d5250840005bc715084021dbf705084021fba7050840007b9705084021ebe605084004fba605084021fba2050840044ff76cc84001cfe76cc840004fd76cc840305bf74cc84004dbc74cc840046de63cc840006dd63cc840004ff764c840004fd764c84001cfc764c840005bf744c84004dbc744c840046de634c840006dd634c840024ff7598440014fe7598440004fd7598440024fc7598440044fe7398440004fd739844000cfe7298440004fd7298440024fc72984400067f52984400067d529844001cfe719844001ef67198440026f65198440006f5519844004ef74198440026f4419844001ef6109844001ef41098440004ff75584400067f75584400047f7558440014fe7558440004fd7558440014fc75584400067c75584400147c755844004ebe5458440006bd5458440004ff7358440044fc7358440006be435844004ebc4358440004ff725844000cfe725844000cfc72584400067f52584400067d525844004ebf4258440006bd425844001ef77158440006f65158440006f5515844004ef7415844004ebc415844004ef4415844001ef8705844001ebf405844001ebd405844001efa205844001ef6105844001ef4105844001ef8105844004dbd7690440006bd7690440004bd769044034dbf759044034dbd7590440305be739044004f9e639044004f9d6390440005bd72904403473f52904400073d529044004dbe719044004fb67190440006bd61904402a7bb709044028dbd709044028fb8709044028ebe609044004fba609044028fb81090440044ff76cc44001cfe76cc440004fd76cc44004dbe74cc440005bd74cc440046de63cc440006dd63cc44001dfa70cc440005f970cc440024ff768c44001cfe768c440004fd768c4400d57e758c4400057d758c44004dbe748c440005bd748c440046de638c440006dd638c440004ff764c440004fd764c44001cfc764c440005bf744c44004dbc744c440046de634c440006dd634c440005fb704c44001df8704c440024ff760c44001cfe760c440004fd760c440305bf740c44004dbc740c440046de630c440006dd630c440024ff768844001cfe7688440004fd7688440005bf748844004dbc7488440006de6388440006dd6388440026f66188440006f5618844001df87088440004ff7648440004fd764844001cfc7648440005bf744844004dbc7448440005df7348440005d
  | 23 => 0x1edf7098c4001ede7098c4001edd7098c4001edc7098c4001edf5098c4001ede5098c4001edd5098c4001edc5098c4001edf4098c4001ede4098c4001edd4098c4001edc4098c4001edf2098c4001ede2098c4001edd2098c4001edc2098c4001edf1098c4001ede1098c4001edd1098c4001edc1098c40004ff7558c400067f7558c400047f7558c40014fe7558c40004fd7558c40014fc7558c400067c7558c400147c7558c4001edf7358c40006df5358c40006de5358c40006dd5358c40006dc5358c4004edf4358c4004ebc4358c4004edc4358c4004e9c4358c40004ff7258c4000cfe7258c4000cfc7258c400067f5258c4004ebf4258c40006de3258c40006dc3258c40004ff7158c40024fc7158c4001ede3058c4001edc3058c4001efa2058c40006df7558c400065f7558c40006de7558c40006dd7558c40006dc7558c400065c7558c4004edf7458c4004ede7458c4004edc7458c4004edf5458c4004ede5458c4004edd5458c4004edc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c400065f5258c40006de5258c40006dd5258c40006dc5258c4004edf4258c4004e9f4258c4004ede4258c4004edd4258c4004edc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dd5158c40006dc5158c4004edf4158c4004ede4158c4004edd4158c4004edc4158c40006df2158c40006dc2158c4001edf7058c4001ede7058c4001edc7058c4001edf5058c4001ede5058c4001edd5058c4001edc5058c4001edf4058c4001ede4058c4001edd4058c4001edc4058c4001edf2058c4001ede2058c4001eda2058c4001edd2058c4001edc2058c4001edf1058c4001ede1058c4001edd1058c4001edc1058c4004dbd7690c40306bd7690c40305bf7590c40365bd7590c4004dbe7390c4004f9e7390c4004ebf6390c4004f9e6390c40306bd6390c4004f9d6390c400069d6390c40005bd7290c4035f3f5290c40005be7190c40255bf7090c40255bd7090c40256be6090c4004fba6090c402579f3090c40004ff7558840014fe7558840004fd7558840014fc755884000cfd7458840004ff7358840044fc735884001cff725884001eef72588400ce7f52588400ceee5258840006ed525884004eef425884004eec4258840004ff7158840024fc71588400ceef215884001cfc705884001eee205884001eec20588400067f765484022e7e76548400067d765484022e7c76548402473e74548400073d74548400fe7e645484023e7e635484022f5e63548400065e63548400067d635484022f5d63548400065d63548400073e43548402473c43548402357f72548400d76f725484022e7f625484000e7e625484022f6e625484000e6e62548400ce7d625
  | 24 => 0xf625494000e7e625494000e7c62549402477b405494022f3e405494001cfc7650940006ef625094000eec6250940005fb705094001df8705094004fb84050940004fe76cc940004fd76cc940044fc76cc940004ff764c940004fe764c940004fc764c940004ff75d8540014fe75d8540004fd75d8540014fc75d8540044fe73d8540004fd73d854000cfe72d8540004fd72d854000cfc72d85400067f52d85400067d52d8540006f761985400057f75585400e57c75585400e57e75185400057d7518540006f56118540024ff7518540014fe75185400267e75185400147e7518540004fd75185400267d75185400047d7518540024fc7518540044fe7318540004fd731854000cfe7218540004fd7218540024fc72185400067f52185400067d5218540206fb4018540286be4018540286bc4018540206f84018540005be76d054004ebe76d0540004be76d054037ebf65d054037ebd65d0540336bc63d0540006bf62d054037f3f52d05400073d52d0540026bc61d054001dbe70d054001dbc70d054004ebf60d054004fbb60d054001cfe7690540375bd7490540006f76190540026f4619054001dfa7090540005f9709054004fb8409054001cfc76505400057f75505400e57c7550540006f76150540006f46150540005fb705054001df8705054001cbc76505400073f755054036f3c755054036ebf655054036ebd655054032ebc6350540006bf625054036f3f52505400073d525054004dbf715054004fb77150540007b76150540026bc6150540007b46150540007bb705054001dbe705054001dbc7050540007b8705054001db8705054004ebf605054004fbb6050540004fe76cc540004fd76cc540044fc76cc540004fe768c540004fd768c540024fc768c5400e57e758c5400057d758c54004dbe748c540005bd748c540004ff764c540004fe764c540004fc764c540004fe760c540004fd760c540024fc760c54004dbe740c540005bd740c54001dfa700c540005f9700c540004fe7688540004fd7688540024fc768854004dbe7488540005bd7488540004ff7648540004fe7648540004fc7648540005df7348540005dc7348540046df7598c40046de7598c40046dd7598c40046dc7598c40046df7498c40046de7498c40046dd7498c40046dc7498c4004edf5498c4004ede5498c4004edd5498c4004edc5498c40046df7298c40046de7298c40046dd7298c40046dc7298c40006df5298c400065f5298c40006de5298c40006dd5298c40006dc5298c4004edf4298c4004ede4298c4004edd4298c4004edc4298c40046df7198c40046de7198c40046dd7198c40046dc7198c40006df5198c40006de5198c40006dd5198c40006dc5198c4004edf4198c4004ede4198c4004edd4198c4004edc4198c40006df2198c40006dc2198c40
  | 25 => 0x864001ef7715864001cfc705864001ebf405864001ebd405864001ef6105864001ef4105864016e7e65906400067d6590640026f66190640006f5619064001dfa7090640005f9709064039dbf759064039dbd759064028f3e659064028f3d659064030dbe7390640005bd72906403973f52906400073d529064004dbe719064028fb66190640006bd619064028fb5619064028fba709064028dbd7090640007b9709064004ebe60906400057f75506400f57c755064017e7e65506400067d6550640006f66150640006f56150640005fb705064001df87050640285bd761064004ebd761064004dbf751064004f3e751064038dbd751064004f3d75106400053d75106402873e65106402873d651064030dbe7310640005bd72106403873f52106400073d521064004fb67110640006bd611064004dbf7010640285bd701064004fba6010640044ff76cc64001cfe76cc640004fd76cc6401567e65cc6400067d65cc64004dbe74cc640005bd74cc640046de63cc640006dd63cc640024ff768c64001cfe768c640004fd768c6400f57e758c6400057d758c64012e7e658c6400067d658c64004dbe748c640005bd748c640004ff764c640004fd764c64001cfc764c64013e7e654c6400067d654c640005bf744c64004dbc744c640046de634c640006dd634c640024ff760c64001cfe760c640004fd760c6401267e650c6400067d650c64030dbf740c64004dbc740c64001dfa700c640005f9700c640024ff768864001cfe7688640004fd76886401167e65886400067d6588640005bf748864004dbc7488640004ff7648640004fd764864001cfc764864010e7e65486400067d6548640005bf744864004dbc7448640005df7348640005dc734864000eee6248640006ed6248640004ff75d8d40014fe75d8d40004fd75d8d40014fc75d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400067f52d8d40024fe71d8d40004fd71d8d40256bf6498d40006df6398d400057f7558d400e57c7558d4024ebf6418d40046de6318d40006dd6318d4001cfe7690d40006df6390d40046dc6390d4001dfa7090d40005f97090d4001cfc7650d400057f7550d400e57c7550d40006df6350d40046dc6350d4004f9c4350d40005fb7050d4001df87050d4004fb84050d4000cfe76d89400deee62d8940004ff75d8940014fe75d8940004fd75d8940014fc75d894001cfd74d894000cfc74d8940044fe73d8940004fd73d89400de7f52d89400deee42d8940024fe71d8940004fd71d894004cfd70d8940276fb40d8940226be40d8940226bc40d8940276f840d89400deef20d89400deec62589400067f76549400067e76549400067d76549400067c76549400073f74549400073c74549400067f635494023e7c63549400dd7f72549400e76f72549400de7
  | 26 => 0x3c73f5290e40005be7190e40257ba7090e40255bd7090e4030fb97090e4004ebe6090e402579f3090e40044ff7650e400057f7550e400f57c7550e401d67e6550e400067d6550e40046de6350e40006dd6350e40005fb7050e4001df87050e4024dbd7610e4004ebd7610e4004dbf7510e403bdbd7510e4024f3e6510e4024f3d6510e4004f9e7310e4024ebf6310e4030ebd6310e40005bd7210e403b73f5210e40005be7110e4004dbf7010e4024dbd7010e4004fba6010e40004ff7558a40014fe7558a400067e7558a400147e7558a40004fd7558a400067d7558a40014fc7558a40004ff7358a40044fc7358a4001eef7258a400ee7f5258a400eeee4258a400eeec3258a40004ff7158a40024fc7158a400eeef2158a4001cfc7058a40266fb4058a4001ef84058a4001eee2058a4001eec2058a4022d7f7654a400067f7654a400047f7654a4022e7e7654a4022d7d7654a400067d7654a400047d7654a4022e7c7654a400073e7454a400073d7454a400de7d6454a4023e7e6354a400067d6354a400073e4354a400073c4354a402357f7254a400f76f7254a4022e7f6254a4000e7e6254a400ee7d6254a4000e7c6254a4022e7e6054a4022f3f4054a402477b4054a40225bd76d0a4004ebd76d0a4004dbf75d0a403adbd75d0a402273e65d0a402273d65d0a4030dbe73d0a40006bd63d0a4000ebe62d0a4000ebc62d0a400ef3f52d0a400ef3d52d0a40005be71d0a4004dbf70d0a40225bd70d0a4004fba60d0a4000cff7650a401ae7e6550a400067d6550a4000eee6250a40006ed6250a40005fb7050a4001df87050a4021dbf7650a4000ebf7650a4000cbf7650a403a5bf7550a403a5bd7550a4021f3e6550a4021f3d6550a4030dbc7350a40006bd6350a4004dbf7250a4004faf7250a4000ebe6250a4021fae6250a4021fad6250a4000ebc6250a400ef3f5250a400ef3d5250a40005bc7150a4021dbf7050a40007bb7050a4021fb87050a4004ebe6050a40044ff76cca4001cfe76cca40004fd76cca401a67e65cca400067d65cca4030dbf74cca4004dbc74cca4000eee62cca40006ed62cca40004ff764ca40004fd764ca4001cfc764ca4019e7e654ca400067d654ca40005bf744ca4004dbc744ca40024ff7598640014fe7598640004fd7598640024fc7598640044fe7398640004fd739864000cfe7298640004fd7298640024fc72986400067f52986400067d529864001ef6719864001cfe709864020efb409864001ef8409864001ef6109864001ef41098640004ff7558640014fe7558640004fd7558640014fc7558640006be5458640006bd5458640004ff7358640044fc7358640006be4358640006bc4358640004ff725864000cfe725864000cfc72586400067f52586400067d5258640006bf4258640006bd425
  | 27 => 0xc72987400067f52987400067d5298740026f67198740026bf419874004ef74198740026f4419874028ebe409874004ebc4098740004ff7558740014fe7558740004fd7558740014fc755874001cfc7458740004ff7358740044fc7358740004ff725874000cfe725874000cfc72587400067f52587400067d525874004ef7715874004ef7415874004ef44158740006fb705874004dbf7650740006bf76507400073f75507403df3c755074004ebf655074004f3e65507403debd655074004f3d65507400063d655074032ebe6350740006bd62507403df3f52507400073d525074004fb77150740026be6150740007bb705074001dbe705074001dbc7050740007b8705074001db87050740044ff76cc74004cfe76cc740004fd76cc7401567e65cc7400067d65cc74001dfa70cc740005f970cc740024ff768c74004cfe768c740004fd768c7401057e758c7400057d758c74012e7e658c7400067d658c74004dbe748c740005bd748c740004ff764c740004fd764c74004cfc764c74013e7e654c7400067d654c740005fb704c74001df8704c740024ff760c74004cfe760c740004fd760c7401267e650c7400067d650c74004dbe740c740005bd740c740024ff768874004cfe7688740004fd76887401167e65887400067d658874004dbe7488740005bd7488740004ff7648740004fd764874004cfc764874010e7e65487400067d6548740005df7348740005dc7348740005fb704874001df870487400f67f74596403d67e74596400067d74596403d67c74596400067f73596400067e73596400067d73596400067c73596403d67f43596403d67c43596400067f72596400047f72596400067e72596400067d72596400067c72596403d67f42596400067e42596403d67c42596400067e32596400067c32596400067f71596400067e71596400067d71596400067c71596403d67f41596403d67c41596400067f21596400067c215964001e7f705964001e7e705964001e7d705964001e7c705964001e7f405964001e7e405964001e7d405964001e7c405964001e7f305964001e7e305964001e7d305964001e7c305964001e7f205964001e7e205964001e7d205964001e7c205964001e7f105964001e7e105964001e7d105964001e7c1059640004ff7558e40014fe7558e40004fd7558e40014fc7558e4001edf7358e40004ff7258e4000cfe7258e4000cfc7258e400067f5258e40006de3258e40006dc3258e40004ff7158e40024fc7158e4001cfc7058e4001ede3058e4001edc3058e401e67e6590e400067d6590e40046de6390e40006dd6390e4001dfa7090e40005f97090e4030dbf7590e403cdbd7590e402573e6590e402573d6590e4004dbe7390e40256bf6390e402579e6390e4030ebd6390e402579d6390e40005bd7290e40
  | 28 => 0xc521046dc630c521145f6710c521007d5310c521007cf6388521007cc6388521025ee7188521027e67188521026ef618852100fe76188521027e63188521007e53188521005ed7088521006df63d8121006dc63d8121004ff75d8121014fe75d8121004fd75d8121014fc75d812104cfe74d8121004fd74d8121044fe73d8121004fd73d81210767f52d81210767d52d8121006fb50d8121006f850d8121076fa20d8121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f755812110d7c7558121005bf7458121005bc7458121005df7358121005dc7358121006df6358121006dc635812110d7e75181210057d7518121006df6318121006dc631812101efa6018121006f9601812104e7f745974004e7e745974004e7d745974004e7c74597400067f73597400067e73597400067d73597400067c735974004e7f435974004e7e435974004e7d435974004e7c43597400067f72597400047f72597400067e72597400067d72597400067c725974004e7f425974004e7e425974004e7d425974004e7c42597400067e32597400067c32597400067f71597400067e71597400067d71597400067c715974004e7f415974004e3f415974004e7e415974004e7d415974004e7c41597400067f21597400067c21597401067f70597403e67e70597400067d70597403e67c705974004e7f405974004e7e40597403e63e405974004e7d405974004e7c405974004e3c40597403e67e30597403e67c30597400067f20597403e67e20597403e67c20597403e67e10597403e67c1059740004ff7558f40014fe7558f40004fd7558f40014fc7558f4001cfc7458f4004edf7358f4004edf4358f4004edc4358f40004ff7258f4000cfe7258f4000cfc7258f400067f5258f40004ff7158f40024fc7158f40004ff7558b40014fe7558b400067e7558b400147e7558b40004fd7558b400067d7558b40014fc7558b4001cfc7458b40004ff7358b40044fc7358b4004eef7258b400fe7f5258b4004eef4258b4004eec4258b40004ff7158b40024fc7158b4004ebf4158b4021ebe4058b4004ebc4058b400feef2058b402457f7654b400067f7654b400047f7654b402467e7654b402457d7654b400067d7654b400047d7654b402467c7654b400073f7454b402473c7454b4023e7e6354b400067d6354b400fd7f7254b401076f7254b400fe7f6254b4000e7e6254b400fe7d6254b4000e7c6254b402473f4154b40044ff76ccb4004cfe76ccb40004fd76ccb401a67e65ccb400067d65ccb40004ff764cb40004fd764cb4004cfc764cb4019e7e654cb400067d654cb40024ff7598740014fe7598740004fd7598740024fc759874001cfe749874001cbe7498740044fe7398740004fd739874000cfe7298740004fd7298740024f
  | 29 => 0x46dc7518d21046df7418d21046de7418d21046dd7418d21046dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d21046df7218d21046de7218d21046dd7218d21046dc7218d2111edf5218d2111e5f5218d2111ede5218d2111edd5218d2111e5d5218d2111edc5218d2111edf4218d2111ede4218d2111edd4218d2111edc4218d21046df7118d21046dd7118d21046d57118d21006df5118d21006de5118d21006dd5118d21006dc5118d2111edf2118d2111ede2118d2111edd2118d2111edc2118d21046df7018d21046de7018d21046dd7018d21046dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d2111edf2018d2111ede2018d2111edd2018d2111edc2018d2104cff76d0d21004fe76d0d21004fd76d0d2104cfc76d0d21006df63d0d21046dc63d0d21044ff7690d21004fe7690d21004fd7690d21044fc7690d21006df6390d21046dc6390d21005f67190d21005f57190d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d2110d7c7550d21006df6350d21046dc6350d21044ff7610d21004fe7610d21004fd7610d21044fc7610d21006df6310d21046dc6310d2100dee7210d21005ed7210d21005f67110d21005f57110d2100cfe76d052100cfc76d0521006bf64d052104ebc64d0521006df63d0521006dc63d052100dee72d0521005ed72d052115cfe7690521006df6390521006dc6390521027e4219052104cff765052100cfe7650521174fd765052100cfc76505210057f755052110d7c7550521006bf645052104ebc6450521006df6350521006dc6350521005ef725052100dec7250521177e42150521005fb7050521005f87050521184fe761052110d7e75105210057d7510521006df6310521006dc631052100cfe76cc52100cfc76cc521006df63cc521046dc63cc52100dee72cc521005ed72cc52111cfe768c52110d7e758c5210057d758c521005be748c521005bd748c521146df638c521046dc638c52111df6768c521006f6768c5213ef76758c52100775758c521007b6748c521007b5748c521135f5738c521147d7638c521046f6638c521046f4638c521007d4638c521046d4638c52100df6728c52100df4728c521026f7628c52114777528c52114775528c521147d6328c521147d4328c521147e7208c521044ff764c52100cfe764c521134fd764c52100cfc764c521006df634c521046dc634c521005ef724c52100dec724c52100df4764c521046f4764c52100cf4764c521007d7734c521007d7634c521046f6634c521046f4634c521007d4634c521007e7724c52100df6724c52100df4724c521137e4724c521136f7624c52113777524c52113775524c521137d7324c521137d5324c521137e7204c521144fe760c521006df630
  | 30 => 0xf7359121005dc735912118df77159121005fb7059121005f87059121004ff75591210067f75591210047f7559121014fe7559121004fd7559121014fc75591210067c75591210147c7559121006bf7459121004ff7359121006df7359121004df7359121044fc7359121006dc7359121044dc7359121174ff7259121006ef72591211767f52591211767d525912118cff7159121006f77159121004ff7059121006fb7059121004fb705912101cfc7059121006f8705912101cf87059121184fe761912110d7e75191210057d751912104ebe6419121006bd6419121044fe76d8d2110d7e75d8d210057d75d8d21004ff75d8d21014fe75d8d210067e75d8d210147e75d8d21004fd75d8d210067d75d8d210047d75d8d21014fc75d8d2104cfe74d8d21004fd74d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21024ff72d8d21144fd72d8d211467f52d8d211467d52d8d21146df32d8d21146dd32d8d2101cfe70d8d21004fd70d8d21044de76d8d210075e75d8d210075d75d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d211475f52d8d211475d52d8d21147d771d8d21147d721d8d21147cc21d8d21147d421d8d21147cf20d8d21006df75d8d21006de75d8d210065e75d8d21006dd75d8d210065d75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21146df72d8d21146de72d8d21146dd72d8d21146dc72d8d21146df52d8d211465f52d8d21146de52d8d21146dd52d8d211465d52d8d21146dc52d8d21146df42d8d21146de42d8d21146dd42d8d21146dc42d8d21146df71d8d21146dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21146df21d8d21146de21d8d21146dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21146df20d8d21146de20d8d21146dd20d8d21146dc20d8d21006df6398d21135f57198d2114df77158d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d2104cfc7458d21006df7358d21134ff7258d21006ef7258d211367f5258d211367d5258d2114cff7158d21006f77158d21004ff7058d2101cfc7058d21144fe7618d21046de6318d21006dd6318d21145de7618d21006de7618d21144de7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d2111f5f5218d2111f5d5218d2111fd57118d2111fd72118d2111fcc2118d2111fd42118d2111fcf2018d21046df7518d21046de7518d21046dd7518d21
  | 31 => 0x8e210267d75d8e210047d75d8e21024fc75d8e2104cfe74d8e21026be74d8e2104cbe74d8e21004fd74d8e21026bd74d8e21004bd74d8e21026ed72d8e211467f52d8e211467d52d8e21146de32d8e21146dc32d8e21024fe71d8e21026f671d8e2101cfe70d8e21004fd70d8e21134fd7698e21026df6398e21026dc6398e21044ff7658e21026dc6358e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e2104cfc7458e21026df7358e211367f5258e211367d5258e21136df3258e21136dd3258e21024fe7158e21024fc7158e21026de3158e21026dc3158e21004ff7058e2101cfc7058e2104cff76d0e21024fe76d0e21004fd76d0e21024fc76d0e21044ff7690e21024fe7690e21004fd7690e21024fc7690e2104ebe6490e21006bd6490e21025f67190e21005f57190e21004ff7650e21024fe7650e21004fd7650e21024fc7650e210057f7550e211157c7550e21005ef7250e2100dec7250e21044ff7610e21024fe7610e21004fd7610e21024fc7610e2104ebe6410e21006bd6410e21025f67110e21005f57110e21174fd76d0621026bf64d0621026bc64d062118cff76506210057f75506211157c7550621026bf6450621026bc6450621005fb7050621005f87050621134fd76cc621026df63cc621026dc63cc621025f5768c621026f5768c62100cf5768c62102776758c62102775758c621027b6748c621027b5748c621046f6638c621027d6638c621027d5638c621026f4638c62100df6728c621027e6728c621027e5728c621025f4728c62114777528c62114775528c621147d6328c621147d4328c62114cff764c621026df634c621026dc634c621027d4314c62114df7764c621006f7764c621027d7734c621027d7634c621046f6634c621046f4634c621027d4634c62100df6724c62100df4724c62113777524c62113775524c621137d7324c621137d5324c621026fb609822101ef860982210057f75582211157c7558221005bf7458221005bc7458221026f86058221004ff75582210067f75582210047f7558221014fe7558221004fd7558221014fc75582210067c75582210147c7558221004ff7458221006bf7458221004bf745822104cfc7458221006bc745822104cbc7458221004ff7358221044fc73582210567f52582210567d5258221024fc7158221056ef2158221056fa2058221026fb1058221026f8105822104cfe76d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121006bf54d9121006bc54d9121044fe73d9121004fd73d9121024ff72d9121184fd72d91211867f52d91211867d52d9121186bf42d9121186bd42d912101cfe70d9121004fd70d9121006bf6499121005de7399121005dd7399121175f571991210057f755912110d7c7559121005d
  | 32 => 0x14fc7558831004ff745883104cfc7458831024ff7258831026ef725883111e7f525883111eee5258831006ed525883111eee4258831046ef325883111ede3258831046dc3258831046ec3258831046df3158831046f63158831046f53158831026ee2158831026ec2158831004ff705883101cfc705883111eef20588310067f765483123e7e76548310067d765483123e7c765483123e7f64548312467e64548310067d645483123e7c64548310075f735483123f5c735483114e7e635483111d7f72548311276f725483111e7f625483100e7e625483111f6e625483100e6e625483111e7d625483123f6d62548310066d625483100e7c625483111f5e325483111f5c32548311467e615483123f5f315483123f76315483123f75315483122e7e605483104cff76d0831024fe76d0831004fd76d083104ebe64d0831006bd64d0831045de73d0831005dd73d0831004ff7650831004fd7650831024fc765083104ebe6450831006bd6450831005df7350831045dc735083100eee6250831006ed6250831004fd76d0431026bf64d0431026bc64d0431004ff76504310057f75504311257c7550431026bf6450431026bc6450431005fb7050431005f87050431025df764c431006df764c431004df764c43111dde724c43111ddc724c431006dd624c4313f75f524c4310075d524c431025df714c431047d7714c431026de614c431027d6614c431004ff75580310067f75580310047f7558031014fe7558031004fd7558031014fc75580310067c75580310147c7558031004ff7458031006bf7458031004bf745803104cfc7458031006bc745803104cbc7458031004ff725803100cfe725803100cfc72580310067f52580310067d5258031006de3258031046dc3258031046df3158031006dd3158031026fb7058031006fa5058031006f95058031046fb3058031046f83058031026fb1058031026f81058031024ff75d9221014fe75d9221004fd75d9221024fc75d9221044fe73d9221004fd73d9221026ed72d92211867f52d92211867d52d9221024fe71d9221026f671d922101cfe70d9221004fd70d9221174fd7699221026bf6499221026bc649922104cff76592210057f75592211157c7559221026bc6459221005fb7059221005f87059221004ff75592210067f75592210047f7559221014fe7559221004fd7559221014fc75592210067c75592210147c7559221026bf7459221006be5459221006bd5459221004ff7359221044fc73592211767f52592211767d5259221176bf4259221176bd4259221024fe7159221024fc7159221026be4159221026bc4159221004ff7059221006fb7059221004fb705922101cfc7059221006f8705922101cf87059221024ff75d8e21014fe75d8e210267e75d8e210147e75d8e21004fd75d
  | 33 => 0xc75d893104cfe74d8931004fd74d89311367f52d8931136ee52d8931006ed52d8931136ec42d8931136ee32d8931044fd71d8931136ef21d893101cfe70d8931004fd70d8931136ec20d8931136ec62589310067f76549310067e76549310067d76549310067c76549310067f64549312467e64549310067d64549312467c64549311357f725493113f6f72549311367f62549310076f62549310066f625493100e7e625493100e7c62549311376c625493100e6c625493123f77315493122e7c6054931004fe76d0931004fd76d093104cfc76d093104ebe64d0931006bd64d0931006ef62d093100eec62d0931004ff7650931004fe7650931004fc765093104ebe6450931006bd6450931005de76cc931046de76cc931144de76cc931135dd72cc93100ede62cc93100edc62cc9311375f52cc9311375d52cc931047d771cc931025de71cc931047d471cc931046df61cc931047d761cc931005dd70cc93100cfc764c931006ef624c93100eec624c931005f7714c931005f4714c931047d4314c931135dc764c93100edc764c93100cdc764c931045df724c931047cf724c931007cf624c93100ede624c93100edc624c931137cc624c9311375f524c9311375d524c931007d7714c931025dc714c931007d4714c931046df614c931047d7614c931005df704c931044fe76d0531044fc76d0531006bf64d053104ebc64d0531045de73d0531005dd73d0531004fe769053104cff7650531004fd7650531044fc76505310057f755053113d7c7550531006bf645053104ebc6450531005df7350531045dc7350531005fb7050531005f87050531004fe761053113d7e75105310057d751053113d7e758c5310057d758c531005be748c531005bd748c531045f6718c531046f7618c5310275e758c5310275d758c5310279e748c5310279d748c531005dd728c531146de628c531146dc628c5313ff5f528c5310075d528c531025de718c531026df618c531047d7618c531005dd708c531004ff75d8131014fe75d8131004fd75d8131014fc75d813104cfe74d8131004fd74d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006fb60981310057f755813113d7c7558131005bf7458131005bc7458131005ef7258131135ec725813101efa6018131006f96018131004ff75590310067f75590310047f7559031014fe7559031004fd7559031014fc75590310067c75590310147c7559031024ff7459031026bf7459031006be5459031006bd5459031044fe7359031044fc7359031046be4359031046bc4359031004ff725903100cfe725903100cfc72590310067f5259031024fe7159031024fc7159031026be4159031026bc4159031004ff705903101cfc7059031004ff7558831014fe7558831004fd7558831
  | 34 => 0x4a310073e6454a310063e6454a310067d6454a310073d6454a310063d6454a312467c6454a310075f7354a310075c7354a311367d6354a311457f7254a3112f6f7254a3100e7e6254a311467d6254a3100e7c6254a311475e3254a311475c3254a3111e7e6154a3123f773154a3122e7e6054a3104cff76d0a31024fe76d0a31004fd76d0a311b67e65d0a310067d65d0a3104ebe64d0a31006bd64d0a31045de73d0a31005dd73d0a31004ff7650a31004fd7650a31024fc7650a311ae7e6550a310067d6550a3104ebe6450a31006bd6450a31005df7350a31045dc7350a3100cff764ca3119e7e654ca310067d654ca31006be644ca31006bd644ca31145df734ca3100eee624ca31006ed624ca31005f7714ca31025f4714ca311967e65d06310067d65d063104ebe64d0631006bd64d06310057f755063112d7c755063117e7e65506310067d655063104ebe6450631006bd6450631005fb7050631005f87050631025dd76cc631046dd76cc6310275e65cc6310275d65cc6310279e64cc6310279d64cc631145de72cc631045dc72cc631006dd62cc6314075f52cc6310075d52cc631027d661cc631027d651cc631407d551cc6310067e65982310067d6598231006be6498231006bd6498231026fb609823101ef860982310067e65582310067d6558231006be6458231006bd6458231026f86058231004ff7558231014fe7558231004fd7558231014fc7558231004ff745823104cfc7458231004ff725823100cfe725823100cfc72582310067f52582310067d5258231006de3258231006dc3258231024fc7158231006df3158231026fb1058231026f8105823104cfe76d9131004ff75d9131014fe75d9131004fd75d9131014fc75d913100cfe72d9131004fd72d913100cfc72d91310067f52d913101cfe70d9131004fd70d9131006bf64991310057f755913113d7c7559131005ef7259131135ec7259131005fb7059131005f87059131004ff75591310067f75591310047f7559131014fe7559131004fd7559131014fc75591310067c75591310147c7559131006bf7459131004ff7359131006df735913132ebe435913132ebc4359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec72591310067f5259131004ff7159131006f77159131004ff7059131006fb7059131004fb705913101cfc7059131006f8705913101cf87059131004fe761913104ebe6419131006bd6419131004fe76d0d31024fc76d0d31006bf64d0d3104ebc64d0d31005f671d0d31005f571d0d3104cfc7650d310057f7550d3113d7c7550d31006bf6450d3104ebc6450d310479c4350d31005f77150d31005f47150d3100cfe76d8931136ee62d8931004ff75d8931014fe75d8931004fd75d8931014f
  | 35 => 0x6bf5199231026be5199231006bd5199231026bc5199231336bf3199231026bc3199231006bf2199231026be2199231026bc219923104ebf709923104ebe709923104ebd709923104ebc7099231006bf5099231006be5099231006bd5099231006bc5099231336bf3099231336bc3099231006bf2099231006bc2099231026bf1099231026bc109923104cff76592310067e65592310067d6559231026bc6459231004ff7559231014fe7559231004fd7559231014fc7559231026bf7459231006bf5459231006be5459231006bd5459231006bc5459231004ff725923100cfe725923100cfc72592310067f5259231006be4259231006bc4259231024fc7159231026be4159231026bc4159231004ff705923101cfc7059231025bf7659231006bf765923104cbf7659231026bf6559231006be65592310273e65592310063e6559231006bd65592310273d65592310063d6559231026bc6559231026bf6259231006be6259231026bc62592310073f52592310079e32592310079c325923132fb73159231027b43159231026bf6059231026bc6059231006bf7559231006be7559231006bd7559231006bc7559231006bf735923132ebe7359231006bd735923132ebc7359231006bf535923132ebe5359231006bd535923132ebc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf52592310063f5259231006be5259231006bd5259231006bc525923132ebf3259231006be325923132ebc3259231026be7159231026bc7159231006bf5159231026be5159231006bd5159231026bc515923132ebf3159231026be3159231026bc3159231006bf2159231026be2159231026bc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006be5059231006bd5059231006bc505923132ebf305923132ebc3059231006bf2059231006bc2059231026bf1059231026bc10592311f67e65d0e310067d65d0e3104ebe64d0e31006bd64d0e31025f671d0e31005f571d0e3104cff7650e310057f7550e3112d7c7550e311d67e6550e310067d6550e3104ebe6450e31006bd6450e31005f77150e31025f47150e3100cff7658a3112d7e7558a310067e6558a310067d6558a31006be6458a31006bd6458a31045dc7358a31026ec6258a31147ce3258a31004ff7558a31014fe7558a310067e7558a310147e7558a31004fd7558a310067d7558a31014fc7558a31004ff7458a3104cfc7458a311467f5258a31146de3258a31146ee3258a31146dc3258a31024fc7158a31026ee2158a31026ec2158a31004ff7058a3101cfc7058a31146ef2058a310057f7654a310067f7654a310047f7654a310067e7654a310057d7654a310067d7654a310047d7654a310067c7654a310067f6454a312467e645
  | 36 => 0xe64d0b31006bd64d0b31004ff7650b31004fd7650b31044fc7650b3104ebe6450b31006bd6450b31045df764cb3111edf764cb3111cdf764cb31047cf724cb3100ede624cb3100edc624cb3114f5f524cb3114f5d524cb31025dc714cb31005df704cb3104ebe64d0731006bd64d0731045de73d0731005dd73d073104cff76507310057f75507311557c755073104ebe6450731006bd6450731005df7350731045dc7350731005fb7050731005f870507311557e75107310057d7510731004ff7558331014fe7558331004fd7558331014fc7558331004ff745833104cfc7458331004ff725833100cfe725833100cfc72583310067f52583310067d5258331046fb7058331006fb5058331006f85058331046fb3058331046f830583310257f765963112e7f76596310147f76596310267f64596310267c64596310057f72596310267f62596310067e62596310267c62596310075e32596310075c325963140f7731596310277431596310267f60596310267c60596310067f74596310067e74596310067d74596310067c745963112e7f735963140e7e73596310067d735963140e7c735963140e7e435963140e7c43596310067f72596310047f72596310067e72596310067d72596310067c72596310067e42596310067c425963140e7f32596310067e325963140e7c325963112e7f71596310267e715963112e7d71596310267c71596310267e41596310267c415963140e7f31596310267e31596310267c31596310067f21596310267e21596310267c21596310067f70596310067e70596310067d70596310067c705963140e7f305963140e7c30596310067f20596310067c20596310267f10596310267c1059631024ff75d9231014fe75d92310267e75d92310147e75d9231004fd75d92310267d75d92310047d75d9231024fc75d9231026dd73d923100cfe72d9231004fd72d9231024fc72d92310067f52d9231026f671d923101cfe70d9231004fd70d9231004fd76992310067e65992310067d6599231026bf6499231026bc6499231004bd7699231026bf6599231006be65992310273e65992310063e6599231006bd65992310273d65992310063d6599231026bc6599231026bf6299231006be6299231026bc62992310073f52992310079e32992310079c3299231337b73199231027b43199231026bf6099231026bc609923104ebf759923104ebe759923104ebd759923104ebc759923104ebf739923104ebe739923104ebd739923104ebc7399231006bf5399231336be5399231006bd5399231336bc539923104ebf729923104ebe729923104ebd729923104ebc7299231006bf52992310063f5299231006be5299231006bd5299231006bc5299231336bf3299231006be3299231336bc3299231026be7199231026bc7199231
  | 37 => 0x8c41014fe7558c41004fd7558c41014fc7558c41026df7358c4104edf4358c4104edc4358c41004ff7258c4100cfe7258c4100cfc7258c410067f5258c41026de3158c41026dc3158c41004ff7058c4101cfc7058c41004ff7558841014fe75588410067e75588410147e7558841004fd75588410067d7558841014fc7558841004ff7358841044fc7358841024ff7258841026ef725884115e7f525884104eef425884104eec425884115eee325884104ebf4158841026ee2158841026ec2158841004ff705884101cfc705884104ebc405884115eef20588412457f76548410067f76548410047f76548412467e76548412457d76548410067d76548410047d76548412467c76548410073f74548412473c745484118e7e645484123e7e63548410067d635484115d7f72548411676f725484115e7f625484100e7e625484115e7d625484100e7c62548411867e61548412473f415484124776415484124775415484122e7e6054841044ff76cc841024fe76cc841004fd76cc8411a67e65cc8410067d65cc841046de63cc841006dd63cc841004ff764c841004fd764c841024fc764c84119e7e654c8410067d654c841046de634c841006dd634c84100eee624c841006ed624c841025bf7650441006bf7650441004bf76504410073f75504414173c7550441026bf65504410273e6550441416bd65504410273d65504410063d655044132ebe6350441006bd62504414173f52504410073d5250441025bf715044104fb77150441026be6150441027b66150441027b65150441417b55150441007bb7050441285bc7050441007b87050441005b87050441004ff7558041014fe7558041004fd7558041014fc7558041004ff7358041044fc7358041004ff725804100cfe725804100cfc72580410067f52580410067d525804104ebf4158041006bd4158041026fb705804104efb405804104ebc405804104ef84058041026fb1058041026f81058041004ff7559331014fe7559331004fd7559331014fc7559331046bf7459331006bf5459331006bc5459331044fc7359331046be4359331046bc4359331004ff725933100cfe725933100cfc72593310067f5259331004ff705933101cfc7059331046df3059331004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3104cfc7458b31046ef7258b3114e7f5258b31046ef3258b31046ec3258b31046f63158b31046f53158b3114eef2158b31004ff7058b3101cfc7058b310067f7654b3123e7e7654b310067d7654b3123e7c7654b3123e7f6454b312467e6454b310067d6454b3123e7c6454b3114d7f7254b311576f7254b3114e7f6254b3100e7e6254b3114e7d6254b3100e7c6254b3114f5f3254b3122e7e6054b3104cff76d0b31044fe76d0b31004fd76d0b3104eb
  | 38 => 0x6f832d814120efb71d8141006fb51d8141006fa51d8141006f951d8141006f851d814120efb41d8141006fa41d814120ef841d8141006fb21d8141006f821d814117d7e75981410057d75981410067f65981410067c6598141006fb60981410057f755814117d7c75581410067f65581410067c65581410067f65181410067c651814128ebf6418141005de7318141005dd731814101efa6018141006f96018141005fa7618141006fa7618141006fb65181410077b65181410067b6518141006fa6518141006f96518141006f86518141007786518141006786518141007b97418141007ba5418141007b95418141007da7318141007d97318141006fb6318141006fa6318141006f96318141006f86318141007ba4318141007b84318141006fb6218141006fa6218141006f96218141006f862181410077b5218141007795218141007bb4218141007b94218141207f34118141007ba4118141207f0411814101efb751814101efa751814101ef9751814101ef8751814101efb741814101efa741814101ef87418141006fb5418141206fa5418141006ba5418141006f95418141006b95418141206f8541814101efb731814101efa731814101eda731814101ef9731814101ed9731814101ef87318141006fb5318141006fa5318141006f95318141006f85318141206fb4318141006fa4318141006ba4318141006f94318141206f84318141006b8431814101efb721814101efa721814101ef9721814101ef87218141006fb52181410067b5218141006fa5218141006f95218141006795218141006f85218141206fb4218141006bb4218141006fa4218141006f94218141006b94218141206f84218141006fb3218141006fa3218141006f93218141006f8321814101efb7118141006fb5118141006fa5118141006f95118141006f85118141206fb4118141006fa4118141006ba4118141006f94118141206f84118141006fb2118141006f8211814104e7f745944104e7e745944104e7d745944104e7c74594410067f73594410067e73594410067d73594410067c735944104e7f435944104e7e435944104e7d435944104e7c43594410067f72594410047f72594410067e72594410067d72594410067c725944104e7f425944104e7e425944104e7d425944104e7c42594410067e32594410067c32594411667f71594410267e71594411667d71594410267c715944104e7f415944104e3f41594410267e415944104e7d41594410267c41594410267e31594410267c31594410067f21594410267e21594410267c21594410067f70594410067e70594410067d70594410067c705944104e7f405944104e7e405944104e7d405944104e7c405944104e3c40594410067f20594410067c20594410267f10594410267c1059441004ff755
  | 39 => 0xe625494100e7c625494124777415494122e7c6054941005be76d094104ebe76d094104dbf75d0941445bd75d09410073f65d094143f3c65d094132dbe73d0941006bf63d0941175bd72d094100ebe62d094100ebc62d09411773f52d09411773d52d0941025be71d094104ebf61d094104fb761d0941005bd70d0941226bc60d094100cfc76509410067f65509411ae7c6550941006ef625094100eec6250941005f77150941005f47150941175bc765094100ebc765094100cbc7650941435bf7550941435bd75509410073f655094142f3c655094132dbc7350941006bf635094104dbf725094104faf7250941007af625094100ebe625094100ebc6250941177ac62509411773f52509411773d5250941007b77150941025bc7150941007b4715094104ebf615094104fb76150941005bf705094121ebc6050941004fe76cc941004fd76cc941044fc76cc9410067f65cc9411a67c65cc94132dbf74cc94104dbc74cc941006ef62cc94100eec62cc941004ff764c941004fe764c941004fc764c9410067f654c94119e7c654c941005bf744c94104dbc744c9410067f659054116e7c659054104df6719054104ef76190541025bf7590541425bd75905410073f659054141f3c659054132dbe7390541005bd729054141f3f52905410073d5290541025be7190541026bf619054104fb76190541005bd70905410067f65d81410067c65d8141004ff75d8141014fe75d8141004fd75d8141014fc75d8141044fe73d8141004fd73d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d8141006fb50d8141006fa50d8141006f950d8141006f850d8141006fb20d8141006f820d8141006fb65d81410077b65d81410067b65d8141006fa65d8141006f965d8141006f865d81410077865d81410067865d8141007bb74d8141007ba54d8141007b954d8141006fb63d8141006fa63d8141006f963d8141006f863d8141007ba43d8141007b843d8141006fb62d8141006fa62d8141006f962d8141006f862d81410077b52d81410077952d8141007bb42d8141007b942d814120ff341d8141007ba41d814120ff041d8141006fb75d8141006fa75d8141006f975d8141006f875d8141006fb74d814120efa74d8141006fb54d814120efa54d8141006f954d814120ef854d8141006fb73d8141006fa73d8141006f973d8141006f873d8141006fb53d8141006fa53d8141006f953d8141006f853d814120efb43d8141006fa43d8141006f943d814120ef843d8141006fb72d8141006fa72d8141006f972d8141006f872d8141006fb52d81410067b52d8141006fa52d8141006f952d81410067952d8141006f852d814120efb42d8141006fa42d8141006f942d814120ef842d8141006fb32d8141006fa32d8141006f932d8141
  | 40 => 0x95410067e62d95410067c62d954146f7741d954146f7441d95410067f74d954146e7e74d954117e7d74d954146e7c74d95410067f73d95410067e73d95410067d73d95410067c73d954146e7f43d954146e7c43d95410067f72d95410067e72d95410067d72d95410047d72d95410067c72d954146e7f42d95410067e42d954146e7c42d95410067e32d95410067c32d954146e7f71d954117e7e71d954117e7d71d954117e7c71d954146e7f41d954117e7d41d954146e7c41d95410067f21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d954146e7f40d954146e7c40d95410067f20d95410067c20d95410067f65d8d410067c65d8d41004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d4100cfe72d8d41004fd72d8d4100cfc72d8d410067f52d8d41006de32d8d41006dc32d8d4101cfe70d8d41004fd70d8d4117d7e7598d410057d7598d410067f6598d410067c6598d41006df6398d41005fa7098d41005f97098d410057f7558d4117d7c7558d410067f6558d410067c6558d41005ef7258d41175ec7258d41005fb7058d41005f87058d410067f6518d410067c6518d41046de6318d41006dd6318d410067f6590d411e67c6590d41006df6390d41046dc6390d41005f67190d41005f57190d4132dbf7590d41465bd7590d410073f6590d4145f3c6590d4104dbe7390d4132ebf6390d410079f6390d4132f9c6390d41005bd7290d4145f3f5290d41025be7190d4132fb67190d4132fb57190d4104ebf6190d4104fb76190d41005bd7090d41256bc6090d41044fc7650d410057f7550d4117d7c7550d410067f6550d411d67c6550d41006df6350d41046dc6350d4104f9c4350d41005f77150d41005f47150d41005be7610d4104ebe7610d4104dbf7510d41455bd7510d410073f6510d4144f3c6510d4132dbe7310d4104f9e7310d4132ebf6310d41005bd7210d4144f3f5210d41025be7110d4104ebf6110d4104fb76110d41005bd7010d4124ebc6010d4100cfe76d894117d7c75d89410067f65d89410067c65d8941176ee62d8941004ff75d89410067f75d8941014fe75d8941004fd75d8941014fc75d89410067c75d89410147c75d8941044fe73d8941004fd73d89411767f52d8941176ee42d8941176ec32d894104cfd71d8941176ef21d894101cfe70d8941004fd70d89410057f755894117d7c75589410067f65589410067c6558941005df7358941005dc7358941176ec6258941005fb7058941005f870589410067f76549410057e76549410067e76549410047e76549410067d76549410057c76549410067c76549410047c76549410073e74549410073d74549410067f635494123e7c63549410073e43549410073c43549411757f725494117f6f72549411767f625494100e7
  | 41 => 0x2473e7454b410073d7454b4123e7e6354b410067d6354b410073e4354b412473c4354b4118d7f7254b411976f7254b4118e7f6254b4100e7e6254b4118e7d6254b4100e7c6254b4118f3f4254b4122e7e6054b4104dbf7650b4115ebf7650b4147dbf7550b4147dbd7550b41335bc7350b41006bd6350b4104faf7250b4100ebe6250b4100ebc6250b4118f3f5250b4118f3d5250b41025bc7150b41005bf7050b4121ebe6050b41044ff76ccb4104cfe76ccb41004fd76ccb41335bf74ccb4104dbc74ccb41004ff764cb41004fd764cb4104cfc764cb41005bf744cb4104dbc744cb41004ff7558341014fe7558341004fd7558341014fc7558341004ff7358341044fc7358341004ff725834100cfe725834100cfc72583410067f52583410067d525834104efb705834104efb405834104ef84058341026df6398e41026dc6398e41026dc6358e41004ff7558e41014fe7558e41004fd7558e41014fc7558e41006df5358e41006dc5358e41004ff7258e4100cfe7258e4100cfc7258e410067f5258e41024fc7158e41026de3158e41026dc3158e41004ff7058e4101cfc7058e41046de6390e41006dd6390e41025f67190e41005f57190e41044ff7650e410057f7550e4116d7c7550e41046de6350e41006dd6350e41005f77150e41025f47150e4100cff7658a41026ec6258a41004ff7558a41014fe7558a41004fd7558a41014fc7558a41004ff7358a41044fc7358a411867f5258a41186ee4258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a4101cfc7058a41186ef2058a410067f7654a410067e7654a410067d7654a410067c7654a410073f7454a410073c7454a411767d6454a4123e7e6354a410067d6354a411857f7254a4116f6f7254a4100e7e6254a411867d6254a4100e7c6254a4115e7e6154a41247774154a4122e7e6054a4100cff7650a4100eee6250a41006ed6250a41005f77150a41025f47150a41044ff76cca41024fe76cca41004fd76cca41046de63cca41006dd63cca41004ff764ca41004fd764ca41024fc764ca41046de634ca41006dd634ca41025bd76d064104ebd76d0641026bf65d0641476bd65d0641336be63d0641006bd62d06414773f52d06410073d52d0641027b661d0641027b651d0641477b551d064128dbe70d0641026fb609824101ef860982410057f755824116d7c7558241026f86058241004ff75582410067f75582410047f7558241014fe7558241004fd7558241014fc75582410067c75582410147c7558241004ff7358241044fc7358241004ff725824100cfe725824100cfc72582410067f52582410067d5258241024fc7158241006bf4158241026fb1058241026f8105824117d7e76d954117e7e76d95410147e76d95410073f74d954117f3c74d95410057d72d
  | 42 => 0xb7058332046fb3058332046f8305833209efa205833204cfe76d9132004ff75d9132014fe75d9132004fd75d9132014fc75d9132006bf54d9132006bc54d9132044ff72d9132044fd72d91321de7f52d91321de7d52d91321debf42d91321debd42d9132024fe71d9132004fd71d913201cfe70d9132004fd70d9132006bf64991321cddd73991320057f755913219d7c75591321eddf7359132004ff75591320067f75591320047f7559132014fe7559132004fd7559132014fc75591320067c75591320147c7559132006bf74591321ecff7359132006df73591321ccff7259132006ef72591321ce7f52591321ce7d5259132004ff7159132024fc7159132004ff705913201cfc70591321dcfe761913204ebe6419132006bd641913200cfe76d0d3200cfc76d0d32006bf64d0d3204ebc64d0d3200dee72d0d32005ed72d0d3204cff7650d3200cfe7650d321ccfd7650d3200cfc7650d320057f7550d3219d7c7550d32006bf6450d3204ebc6450d32005ef7250d3200dec7250d32004ff75d8532014fe75d8532004fd75d8532014fc75d853204cfe74d8532004fd74d8532044fd72d853214e7f52d853214e7d52d853214ef621d853201cfe70d8532004fd70d853219d7e75985320057d7598532005be7498532005bd7498532006f76198532006f56118532024ff7518532014fe7518532004fd7518532024fc751853204cfe7418532004fd7418532026dd7318532044fd721853211e7f521853211e7d521853211ede321853211edc3218532026f6211853211ef5211853201cfe7018532004fd7018532004ff75d8132014fe75d8132004fd75d8132014fc75d813204cfe74d8132004fd74d8132044fd72d81320be7f52d81320be7d52d81320bede32d81320bedc32d8132024fe71d8132004fd71d81320befa20d8132006fb60981320057f755813219d7c7558132005bf7458132005bc7458132005f77158132005f4715813201efa6018132006f96018132004ff7558f410067f7558f410047f7558f41014fe7558f41004fd7558f41014fc7558f410067c7558f410147c7558f4104edf7358f4104edf4358f4104ebc4358f4104edc4358f41004ff7258f4100cfe7258f4100cfc7258f410067f5258f4104ebf4258f41006de3258f41006dc3258f41004ff7058f4101cfc7058f4104dbd7690f41336bd7690f41335bf7590f4148dbd7590f4104f9e7390f4104ebf6390f41336bd6390f41005bd7290f414873f5290f41025be7190f41005bd7090f41256be6090f41004ff7558b41014fe7558b41004fd7558b41014fc7558b41004ff7358b41044fc7358b4104eef7258b4118e7f5258b4104eef4258b4104eec4258b4118eef2158b41004ff7058b4101cfc7058b410067f7654b412467e7654b410067d7654b412467c7654b41
  | 43 => 0xd4204f9f7350d420079f6350d42046be6350d42046bc6350d420079c6350d420469c6350d42007af7250d4200dbe7250d4200dbc7250d421cfac7250d4204ebf6250d4204faf6250d421cf3f5250d421cf3d5250d42005bf7150d4221dbc7050d42004ff75d8542014fe75d8542004fd75d8542014fc75d8542044fe73d8542004fd73d854204cfd72d854218e7f52d854218e7d52d854218ef621d854201cfe70d8542004fd70d8542006f761985420057f75585421ad7c7558542005df7358542005dc7358542005fb7058542005f870585421ad7e75185420057d7518542006f56118542024ff7518542014fe75185420267e75185420147e7518542004fd75185420267d75185420047d7518542024fc7518542026bd7418542044fe7318542004fd731854204cfd721854215e7f521854215e7d5218542026f6211854215ef5211854201cfe7018542004fd70185421ad7e75d81420057d75d8142004ff75d8142014fe75d81420067e75d81420147e75d8142004fd75d81420067d75d81420047d75d8142014fc75d81420febd74d8142044fe73d8142004fd73d814204cfd72d81420fe7f52d81420fe7d52d8142024fe71d8142004fd71d81420fefa20d81421ad7e75981420057d7598142005de7398142005dd7398142006fb609814201efa6018142006f96018142004ff75593320067f75593320047f7559332014fe7559332004fd7559332014fc75593320067c75593320147c7559332046bf745933200cfe735933200cfc7359332046be4359332046bc43593321ce7f52593321ce7d52593321cebf42593321cebd4259332004ff7159332024fc7159332004ff705933201cfc7059332024ff7598732014fe75987320267e75987320147e7598732004fd75987320267d75987320047d7598732024fc759873204cfe7498732026be749873204cbe7498732004fd7498732026bd7498732004bd749873200cfe7398732026de739873200cde7398732024fc73987321467f52987321467d5298732146de3298732046dc3298732026f67198732026df3198732046f73198732026f43198732026f62198732146f5219873201cfe7098732004fd7098732004ff7558732014fe7558732004fd7558732014fc7558732004ff745873204cfc745873200cfc73587321367f52587321367d5258732046f77158732046f73158732046f43158732136f62158732004ff705873201cfc7058732004ff75583320067f75583320047f7558332014fe7558332004fd7558332014fc75583320067c75583320147c7558332004ff7458332006bf7458332004bf745833204cfc7458332006bc745833204cbc745833200cfc735833209e7f525833209e7d525833209ede3258332046dc3258332004ff7158332024fc7158332046df3158332046f
  | 44 => 0x67d61581520077b605815222e7e60581524b57e76181522457e74181520057d74181520067f64181520067d641815223d7e73181520057d73181520067e63181520067c63181520157f721815200d7e72181520157d721815200d7c72181522367f62181524af6f62181520057e71181520057d71181520067e61181520067c611815222d7e701815222e7f601815222f7a601815222e7d601815200779601815222f7a20181524a7792018152004ff7558f420067f7558f420047f7558f42014fe7558f42004fd7558f42014fc7558f420067c7558f420147c7558f4200cfc7458f4204edf7358f4204edf4358f4204edc4358f421ce7f5258f421ce7d5258f421cedf3258f42004ff7158f42024fc7158f42004ff7058f4201cfc7058f4204dbf7650f42006bf7650f420073f7550f4249f3c7550f4204f9f7350f42046be6350f42046bc6350f4200dbe7250f4200dbc7250f421cf3f5250f421cf3d5250f42005bf7150f42225bc7050f42024ff7598742014fe7598742004fd7598742024fc759874200cfe7498742026be749874200cbe7498742024fc7498742044fe7398742004fd73987421867f52987421867d5298742026f67198742026bf419874204ef74198742026f44198742026f62198742186f5219874201cfe7098742004fd709874204ebc4098742004ff75587420067f75587420047f7558742014fe7558742004fd7558742014fc75587420067c75587420147c755874200cfc7458742004ff7358742044fc73587421767f52587421767d525874204ef7715874204ef7415874204ef44158742176f62158742004ff705874201cfc7058742004ff7558342014fe7558342004fd7558342014fc755834200cfc745834204ebc745834200cbc7458342004ff7358342044fc73583420de7f52583420de7d5258342004ff7158342024fc715834204ebf415834204efb705834204efb405834204ebc405834204ef840583420defa2058342044fe76d8d42004ff75d8d42014fe75d8d42004fd75d8d42014fc75d8d42006df53d8d42006dc53d8d4204cfd72d8d421ee7f52d8d421ee7d52d8d421eedf32d8d42024fe71d8d42004fd71d8d4201cfe70d8d42004fd70d8d42006df6398d420057f7558d421ad7c7558d42046de6318d42006dd6318d421bdbe76d0d4204ebe76d0d42046be63d0d42046bc63d0d4200dbe72d0d4200dbc72d0d4204ebf62d0d4204faf62d0d421ef3f52d0d421ef3d52d0d42005bd71d0d4221dbe70d0d4200cfe7690d421cdbd7490d42006df6390d42046dc6390d4200dee7290d42005ed7290d4200cfc7650d420057f7550d421ad7c7550d42006df6350d42046dc6350d42005ef7250d4200dec7250d4200dbc7650d42046bc7650d4200cbc7650d420073f7550d424973c7550d4204dbf735
  | 45 => 0xe7410d520073f6410d522473c6410d521dd7e7310d520075f6310d5223f5c6310d5223f3f4310d5223f5e4310d5223f3d4310d522475d4310d521bd7f7210d5200d7e7210d521bd7d7210d5200d7c7210d521be7f6210d521c76f6210d520057e7110d520057d7110d5222d7e7010d520057d7010d522457e74d85520057d74d85520067f64d85520067d64d855223d7e73d85520057d73d85520067e63d85520067c63d85520157f72d85520157d72d85524ee7f62d85524ff6f62d85524ef7621d85524ef7521d855222d7e70d85520057d70d85524f57d76985522457e74985520057d74985520067e64985520067c649855223d7e73985520057d73985524dd7d72985520076d729855210d6d72985524de7f62985521176f62985524d57e71985520067f619855200777619855222d7e70985520057d70985520057f74585520073f74585520053f74585522457c74585520073c74585520053c74585520067f64585520067d64585520057f73585520075f73585520055f735855223d7c73585520075c73585520055c73585520067e63585520067c63585524f57f72585520076f72585521156f72585524f67f625855210f6f62585520077761585520067e61585520057f70585520077b70585520057b705855222d7c70585520077870585520057870585524ed7e76185522457e74185520073e74185520053e74185520057d74185520073d74185520053d74185520067e64185520067c641855223d7e73185520057d73185520157f721855200d7e72185520157d721855200d7c72185524d67f62185524e76f62185524dd7e71185520067f61185520077661185520067d61185520077561185524d77621185524d775211855222d7e70185520057d70185522457e74d81520073e74d81520053e74d81520057d74d81520073d74d81520053d74d81520067e64d81520067c64d815223d7e73d81520057d73d81520157f72d81520157d72d81524b67f62d81524cf6f62d81520057e71d81520057d71d81520067f61d81520067d61d81524b77a20d81524b77920d81524bd7d76981522457e749815222f3e74981520053e74981520057d749815222f3d74981520053d74981520067f64981520067d649815223d7e739815222f5e73981520055e73981520057d739815222f5d73981520055d73981520067e63981520067c63981524c57d729815222f6d729815207d6d72981522367f62981520876f62981520057e71981520057d71981520067e61981520067c619815222d7e709815222e7f60981520077b60981520057f74581522457c74581520067e64581520067c64581520057f735815223d7c73581524bd7f72581520076f72581520856f72581524be7f625815207f6f62581520057f71581520057c71581520067f6158152
  | 46 => 0x91520057d719915222d7e70991520057d70991520073f64591522467e64591520057f73591520075f73591520055f735915223d7c73591520075c73591520055c73591525557f72591520076f72591521b56f72591525567f62591521af6f62591520057f71591520057c71591520057f705915222d7c705915254d7e76191525457e74191522467f64191522473e64191522467d64191520073d64191520063d641915223d7e73191520057d73191520157f721915200d7e72191520157d721915200d7c72191525367f621915253f6f62191525373f42191525373d42191520057e71191520057d711915222d7e70191520057d70191522457e74d8d520057d74d8d520157f72d8d520157d72d8d5251e7f62d8d5252f6f62d8d5251f5f32d8d5251f5d32d8d520057e71d8d520057d71d8d5222d7e70d8d520057d70d8d525257d7698d522457e7498d520057d7498d520067e6498d520067c6498d525057e7398d5223e7f6398d520075f6398d520065f6398d525157d7298d5223f6d7298d5219d6d7298d525167f6298d521a76f6298d520057e7198d520057d7198d5222d7e7098d520057d7098d520057f7458d520073f7458d520053f7458d522457c7458d520073c7458d520053c7458d520075f6358d5223e7e6358d525257f7258d520076f7258d521a56f7258d525267f6258d5219f6f6258d520057f7158d520057c7158d520057f7058d5222d7c7058d5251d7e7618d522457e7418d520057d7418d520067e6418d520067c6418d525157e7318d5223e7f6318d5223f5e6318d5223e7d6318d520075d6318d520157f7218d5200d7e7218d520157d7218d5200d7c7218d525067f6218d5250f6f6218d525075f3218d525075d3218d520057e7118d520057d7118d5222d7e7018d520057d7018d522457f76d0d520057e76d0d520057d76d0d522457c76d0d520075f63d0d520075c63d0d521ed7f72d0d5200d7e72d0d521ed7d72d0d5200d7c72d0d521ee7f62d0d521f76f62d0d521ef3f42d0d520057e71d0d520057d71d0d5222d7e70d0d520057d70d0d5223d7f7690d520057e7690d520057d7690d5223d7c7690d521cd7d7490d520073f6490d520073c6490d521bd7e7390d5223f3f4390d522475f4390d521dd7f7290d5200d7e7290d521dd7d7290d5200d7c7290d521de7f6290d521e76f6290d520057e7190d520057d7190d5222d7e7090d520057d7090d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d522475f4350d5223f3e4350d521cd7f7250d5200d7e7250d5200d7c7250d521ce7f6250d521d76f6250d520057f7150d520057c7150d520057f7050d5222d7c7050d5223d7f7610d520057e7610d520057d7610d5223d7c7610d521ed7
  | 47 => 0x67f65589430067c65589431ceec62589430067f65d85430067c65d8543004ff75d8543014fe75d8543004fd75d8543014fc75d8543336be43d8543336bc43d854300cfe72d8543004fd72d854300cfc72d85430067f52d854301cfe70d8543004fd70d85431d57e75985430057d75985430067f65985430067c6598543006f761985430057f75585431d57c75585430067f65585430067c6558543005ef72585431cdec7258543005fb7058543005f870585430067f65185430067c6518543006f56118543024ff7518543014fe7518543004fd7518543024fc751854300cfe7218543004fd7218543024fc72185430067f521854301cfe7018543004fd70185430067f65d81430067c65d8143004ff75d8143014fe75d8143004fd75d8143014fc75d814300cfe72d8143004fd72d814300cfc72d81430067f52d8143024fe71d8143004fd71d81431d57e75981430057d75981430067f65981430067c65981431cdee7298143005ed7298143006fb60981430057f75581431d57c75581430067f65581430067c65581430067f65181430067c6518143256bf641814301efa6018143006f96018143004ff7558843014fe7558843004fd7558843014fc7558843046bf4358843046bd4358843044ff7258843046ef72588431be7f525884304eef425884304eec4258843046ef3258843046ec3258843004ff7158843024fc715884304ebf41588431beef2158843004ff705884301cfc705884304ebc4058843024ff7598443014fe7598443004fd7598443024fc759844300cfe7298443004fd7298443024fc72984430067f5298443024fe7198443026f67198443026bf419844304ef74198443026f44198443046f73198443026f4319844301cfe7098443004fd709844304ebc4098443004ff7558443014fe7558443004fd7558443014fc7558443004ff725844300cfe725844300cfc72584430067f5258443046f7715844304ef7415844304ef44158443046f73158443046f43158443004ff705844301cfc7058443004ff7558043014fe7558043004fd7558043014fc7558043046de435804304edd4358043004ff725804300cfe725804300cfc72580430067f5258043004ff7158043024fc715804304ebf4158043046fb7058043006fb5058043006f8505804304efb405804304ebc405804304ef8405804304eb84058043046fb3058043046f8305804323d7e73d91520057d73d91520157f72d91520157d72d915254e7f62d915255f6f62d915254f3f42d915254f3d42d91520057e71d91520057d71d915222d7e70d91520057d70d91525557d76991525357e74991522467f64991520073f64991520063f649915223d7e73991520057d73991525457d72991522476d72991521ad6d72991525467f62991521b76f62991520057e719
  | 48 => 0xc72587430067f525874304ebf425874304ef7715874304ef7415874304ef44158743004ff705874301cfc7058743004ff7558343014fe7558343004fd7558343014fc7558343044fc745834304ede435834304edd4358343004ff725834300cfe725834300cfc72583430067f5258343004ff7158343024fc715834304efb705834304efb405834304ef84058343004ff7558a43014fe7558a43004fd7558a43014fc7558a43044fc7358a43046bf4358a43046bd4358a43046ef7258a431de7f5258a431deee4258a43046ef3258a43046ec3258a43004ff7158a43024fc7158a43004ff7058a4301cfc7058a43024ff7598643014fe75986430267e75986430147e7598643004fd75986430267d75986430047d7598643024fc7598643044fe739864300cfe7298643004fd7298643024fc72986430067f5298643026f67198643046f73198643026f4319864301cfe7098643004fd7098643004ff7558643014fe7558643004fd7558643014fc7558643044fc7358643004ff725864300cfe725864300cfc72586430067f5258643046f77158643046f73158643046f43158643004ff705864301cfc7058643046df3058643004ff75582430067f75582430047f7558243014fe7558243004fd7558243014fc75582430067c75582430147c7558243044fc7358243004ff725824300cfe725824300cfc72582430067f5258243004ff7158243024fc7158243046fb7058243006fa5058243006f95058243046fb3058243046f830582431d57e76d95431d67e76d95430147e76d954356f5f43d95435673e43d95435673c43d954356f5c43d95430057d72d95430067e62d95430067c62d95435667f74d954356e7e74d95431d67d74d954356e7c74d954356e7f73d95435667e73d95431d67d73d95435667c73d954356e7f43d95435667e43d95431d67d43d95435667c43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d954356e7f42d95430067e42d954356e7c42d95435667f32d95430067e32d95435667c32d95430067f71d95430067e71d95430067d71d95430067c71d954356e7f41d954356e7c41d95435667f31d95435667c31d95430067f21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d954356e7f40d954356e7c40d95435667f30d95435667c30d95430067f20d95430067c20d954300cfe76d89431d57c75d89430067f65d89430067c65d89431ceee62d8943004ff75d89430067f75d8943014fe75d8943004fd75d8943014fc75d89430067c75d89430147c75d8943044fd74d894304cfd73d89431ce7f52d89431ceee42d89431ceee32d8943024fe71d8943004fd71d89431ceec21d894301cfe70d8943004fd70d89431ceef20d89430057f75589431d57c7558943
  | 49 => 0x40030000000005000100040080000003000000a0014001001c00500280000000000000c01700040010040007000800a002c00400140000078000000000600040000008000000400a004c00b009c001000000500240020064005002401c0000001000c0010000001000000c000000900300030004003000802e00140020054007000802c0014000001c00600140020008002001c007000800000000020000001000401d000800200080000024002000400100040010004001000000c000c01b0000000000000700100000020002000001d0004011001000000180070000001004400e0018000000001b001000300000030004000000800a00080010034001004000400000000000009001000200240000070001005c001000800700040080008000001c00a000000800100030010003001400f002400100440070004015001002a00340150008003000c0040000005000800200440240000002001c0010068003009c00000100050014007002001300000040000000000c000001800200200120020002000400500080000034001000c006000002a000c009000400600180490000001002400d0020026000c003000000a001c001000000300000000010000000800200540050020001000000000040010018007005c002000000200000020010004003000100340000010003005800f000400000440000038000000802900080040004000000000d002c007004c01b01380030008002008002b000400000040000004002000c02b002800b000800f001400b0004001000c000001000000000020024001003c000001000800400040000000000c01b0000003001001000000000004001000000c00080070020002003400100480000000000004c00200200010000002000c0010064000000000300000050024001000c0090008000000001c000001f0024000002c001002800200800090020000000c00c0010005001400400000020004002001400000080000004002000401a001400000280090000007000c000000000400040000000002001400c0004000000400000100010000005000000a00040040008000000c003000000f00100010000009001801500080010000017004ff7558b43014fe7558b43004fd7558b43014fc7558b43044fc7458b4304eef7258b431ee7f5258b4304eef4258b4304eec4258b431eeee3258b43004ff7158b43024fc7158b43004ff7058b4301cfc7058b43024ff7598743014fe7598743004fd7598743024fc7598743044fe749874300cfe7298743004fd7298743024fc72987430067f5298743026f6719874304ef74198743026f4419874301cfe7098743004fd7098743004ff7558743014fe7558743004fd7558743014fc7558743044fc745874332ebe435874304ebc4358743004ff725874300cfe725874300cf
  | 50 => 0x5001000300000000050009000c0070004001000800d000c02f0004001000800c002800100040010038003000000f000c000002c01b0038014001c000003c0010004000001800300c800100a400400100010000001000400000140000008001000800900100070008000000000f0000023000800d000c00300100000000003000800000040130074005001c0000044001000c00f014001700040010010001000800800f000b00040010008005000000000080130014000001c0080028003001c0000008014000c006002401f0004017000c00100240030008000000000500180010010008001001800000000004000001801d0040000000000f000c00800080050010001004400600380000064006001c00200080000038000001001a00000080000024000000000400010004001005c005000c0030000001000000400040020004000000000500080000000000000400100140070000001006c0060000011002000000080010000000001c013001000100040030010003001c01800040090020001001c00d001800000340000004015000c03d0028005000c0000008003003000400000030004007001000600080000000002000c00b001000200100020000005000801100040030000005000c000004c00000100160000001000800000ac0000014000001c00000000000008004000000100080050004005000400a0020007007c0000008006000c001000c000001000200000040000000006400100000000004001000400000100000014000001400100580020028010001c0000010001006c00c0040001000400d0020001001800000000060010006004400900100180004002000000300180000000010004c000000400200000120058008000400000240040000007000000300200010004003000400000080360020001000c0080068002000c00c00040030064002000400a005c01e000000200040000004013001800000280080004008000400800000050004000001c0070008010006c00c000400d0000001001800000240000008000003000100040180000001000c010000c0040010001001c001001000000000020018019000400c0000000001c02400500020014003000800c000400400100000000003000000e0028004001400300100000024006000c0000008010001001900400050000000000c005002c000002c003000800900040000000000001c0000048000001c00000440000000003004000100700050004000001400100000040018000000000300a0001000c0000000004000000300000000018002001800000100010008017001c004000000500080010000000001401700080000014000000800500cc00000180010030000000000400080000010008001400f0004002000000000300030014000000000000140060008000000
  | 51 => 0x20000001004000300040070050002000c00000040000000003002800b0084000000000100400020000003000c0010074007000000c0000002000001a000c0000000006001c000005c01b00240000010000000000100080060000000001000300000000054005000400700080010010000000400800040030020000000c003000c0050020000010000200140010004000005c0070000003000000000000010004005000c00200040010030001002400e00240000008006000000200000020000005001c000000400b0000000001400000200010008001001c0080030000003c000001c000003400100280000010000000000c001000000040040004018005400800040050018003003c002000000300140020008000000c000000000000240060008008000000c001c00000100000000000000000100440110008004005c000002000100280060050001002c000001400000000000000000000c0060004000000800100240040020006001c00800080030000001001000b0064000000400200180150024000005400c0000005000000800300060000000000c0030000001000000000340020000012000000e001000a0018000000800200b000300140000080000001c00d00140150034006000400b0004000000c002000400300000020008007000800100040000004000000c001001000100000120048000000801c001000700180230020033000c003007c00600100010014002000802500580000004000000c007001800200340030000004000c004001c00000000010008000002c00000000000088001000001900100080024017000400100bc01800040000008006001800200000000050004000000200000000044006002400b001c00c000000f004c00500000000004001001000400240000018016000800100500000010000000c008009c0000008001000001000000000054006000401a0004000002c00400040310000005000000a000000200e40090000000004000b000c0090024000000c005000c0000000001000c0000008011000c0090048001000400d000800000000000014001000c005000000b0008006000800c001c019000800200000050080003002001c0014001001c00e000c00000000140014009001000c00000000004043000c00f000000c0000000000c00000e0002000c0000000002001001f0008005003c009000000b000400900480140008001000000c002c00e000800100040050004033000000300040180004001000800000480000010000000802a0000000000c005000000100080000000004001001f000000600080050008003000800b00080020040011002c000000c00d0000000008400100000010018000002800501580180014000004c001000c000002c00600140020024000008c0000038001000800
  | 52 => 0x900240010004000005c00b005800100180010018005004000800180070000000000c002000c005000800100080020008004001c00a000400400180000040000000c00c00080190024001003c0110064007000c0080008005000000100000010000014000000000000020000019003403000240020018004000c00000e4000001c0410000008001800e001000500040070004006003800300000040000001000c009000c00c000801600000000008001000400a0000002001400d009000100400080000013000001300100090010001007000000080080018001000000900180010000012000000200240020018002000c00200000000004001000c001002c00300040010048012003800800080040000000001800b000400700000010014002001000e0010005002c0020000005001000400000010000000005c00c00000020000000008400000740000000001000800100000000018003002c000001800000800020094000000400e00040160004009001400600140030000000000c00d001c003000000a0000004004000100280230000008000c0110008006000400100580010008001000000000400150004000000800300d80040000000008c0090010000000400a00040010000002000000c0000008001c01100140060008004000000200000030004000000c0000040006003c0000000008001000000080020014001000c02000080030000000002c00800080010000001000c0000008010000000600140010004000000c0020014004001c00200040010004003000c005000401000bc00100000150010014002c00300040040000000000000500040040008000000c002000000a004000000000000004000000000c000000600000000080001000000000280010078001000800000080000034000000000000000000004004000c00e0004000000800d0004010000000500080010014001000000200000040038005000c0130028000000000f0000006000c000000801200240040000004001c0040018004000400100140060048000001400200000000048001005800100040070014013000800100000070000001003c00600100000010008001c00000280060000001000800a002400200140050008006003c00d0030006000000600280080028001001000b00200010000009000c001009801800880000014005001000d00100020088000000c00c0000016005c0020000002000400000300140010009003c0000014005000800200080010014003001c0000000000000400000100000018000000c001009000100000020004006005c013000c0340000003003000300000080000000000401100d80050094002004401700000060008001001c0000048000000c003000400000600000000000000001000000010008000000800f003000000
  | 53 => 0x40003000000300500010008002000000000000070000000001000600080000004001001400000040000044002002c005002c001006c00d003c00d0004017000000e008c0080008004000c000000000000040080000002000000400440000010001000801900300090018015000c0270014001000400200300010020001006002900180070000028001c0050018002001c0000008006000000400080050060001003c000002000700180000004001000c004002c000003c0060010006004000d0000000001000300140030004000000000200000000010012000000a00040100020017000000000100000014000004000c004c00a000c0000008005000001b0000001000400b0000003005400500080020030001006000200080060050039001000a001c002001400001940090018000000000100a40020000004000800b000000000240040040003003c000000c006000400000080090000000002c011006001300080010004002000000100080000000002002400200040060008007001801800000050008005000000200140000018011005c001001000600000010014000001400b002c01200000060058001000c00d0004001005400a00040010024001000c000000800a005c006013c0000014005002000000280040004000000800000040020010002001000500040010050001000000d000000000500000024015002c00c00000000074000000001f000c000001c000000000000e0001003400a000000f0064000000c00b00040020004000001000200000060000005003c01c006c0000050012001c0000040000000c00000000050004014002c0010058009000800d000400300000190004005001400000080010008008000000c004c001005c0030020003000000000000000024003001000400040010004008003c003006800700000030170003000c00000000010000002002c000000400e000800000140050024000000c00000000300008000000800600000110004002000401500040000000007006400b004400f0004007000401700000040018002000800100040000004000001c000001400300740010018006000c0030010001000400900000080020002000c009005c01a000001200b000200000010000002002400a001c00300100000044005000c0000000002000001600040070024003002000c000400100000010000004001000a0024028000000d000800a000400200540030034000000c00700500000000000000801a00000020000004000c002001000c000003000000020014000001c0060038004002800000000050000021001c006000c003000c0000014000000c0000068002000400000100110028002004000c00000030000000001400700180130000001005000000000040044006001400a005c000000400400040
  | 54 => 0xf7a000000000001f480000b980000000041480000000065c5100481191924f61724a35982c337a7c38b67000029320000f4f10aa24ba1c38385800000007f3c71b1eed04644444a6c000009aa28ac42a0aa702ac0000546057d353a1e1c175850c23e080840ad9269094a000000004271a4077b4000200921fa00000000000000022d84b9853700003c6800015a9261c00000000000000000000001d61071a0000a659b8c26643964000071e00004b80000161e2ebe3694aa1000000004a5073e8e412ce43b8097e0d2f0cac00007db85ed02fa6d983a598c500b4649c4980dac2d0c791c8000e98299856a0f66860c0b882338b8f87fb3a840000c9e0d942af22eb07ea000018bc0000bfb8c5f271e3dd46550000257072a8eeb8cf200000000c6d8088043e68d40001afa0fba49b4938124206bc47c83c707e9174e1afc67400000f3460d02578000171801540001fe800000000ea98908289473dc30e80002c34289c7f302ef00000000f6c00003c7a1cbcf0c8e002c743cec04f88651dd207fc0000ae5000066b901c1bbf01dc149c3941d7727b431e4cf58a7618b479780000bc5183032d899c9ba912687678824000000000000fa48000000000000000000000000006ef00002ebc0000b5a887d2e88361c852800000000000000157c000003444ca89d41d4850dc86080e2360a5e042a5114821c41ad8208085e3fc664745c31dea26164fd4f3013182d726104cf79a75185668b0992a0742d0e7ec49238ed827dc716904518263430182ce649e3b1a521f78d4185c1074249dce0e159d412460a100d03392bda1a10d039a9135800000000000015743d1c90780003d0651c0b25958119ce160c00000000000000000000000000000048008591cf26a705bc9395000000201b506350000252434312600000000000019ee18fc1ec803894e61fe00ce8ac18b1e0e0e111c4ad907a3fa26810df3895a028a5cb80a716dd00005fac0f1165404a4443400000000000000099588c32ce600000000000000000000000000000011281d11cb806d60000a62800036307878bc29da61fb81aa4154952212302d6455a91512d5e66447f49c87315011e4dad91ab3e762d0470d8b811f2a18e492c03000a2409a846082672e3c56dc10c001c30ae0044024940e2a9434c48be113839c0117c1cf9e9814be0018849811c313013ac54c91fc3dbc7b6c8b21b130a747ac8aca802a149e419825b9cd834725e40df91bef1b820b3831407ec1f345a983b282bb2aa22714e2505360fa413f8b070e473f923494e720bd31cb81180c471e5d3e0402602b09e400838466c000000000000000c0e000000000000622809d00001fe00000b7b002a6d38000000033647b4400020b739560000edc00000a840000000153f00000000b0a84e1000000180010
  | 55 => 0x3b8281e8320e22000008260000b8303dc316e5144e3300003aca00003249c84000016cc33d8f36121c0000000000000006b0c00016a20000366c0000000208e58fc00000002e4856f000d833f2f266f38000068915e00000ab2800000001c44e8e80002f9875580001a011f9a0000d06800000000000ba690500bf282b8d76196826dc4bdca8205f7087a44e84108f040a226734fda867e3c2872bcbc2159601be5f487ef96c303504528d0404b832f637d0159902330ec6a34b1e80001c5e3bb40000bf6411057b80dc9dcb38f470b430a939c0b544f94000000016a64dc82b619c82a965268e9f998a0ebe3bc40749640298c418060097aa185e6ee8c559c2f1cd45b8400000000aaa2e08dce9e422ac41a9823f800000001bd08581a66123e28708491a3316be3630ddf078a307e82c485a89fa1bca353cd9d145a077235cc0001590086650c0000000006061af89bc90ab000012cc96380003f6400007668f4400007a2c00005e5000000000000000414c0000fef8d8000006b9481a0ca20000000012580001604645800000000000030c0000ebc1d18336c4c2800000007304a9b07ba1df251fc0000000000000000000000132e0000000164e0a1676d80001ff921b05e70d581f9f11cc274c00000002d622e0c0000b7600004a38aec80002ff4188880691e812dc2be48021bb83c4825406160acf00007c24da51f461f047084da59af336f83a784331da70c2868a4dd10da43e4a05ac0001b2e00002168d3102dc1c5c0b688890a9800007e602bd1121000000000000000000000000000000000000000001312000038b000005f2000000000000fae000000000000cd500000f7c9d191fe00000000ffb000000005df0b9118da04b22c2cec597212086704464888ff15ac00009da89f6000036ac8aa9f95364007ac493011b155a7830e778a4d16fc1edcb52850303841a5844c942b3f8c3c70000000002da5f2400000000000000000000000000000000000000ab217c44f4104913321b9023211720c70427c0000000000000ac00000001e2e000089489c318f40000c7b1cdf00006a78c1b17e536c47b101878000000081b0bca0de80722678037e1b9204247970c5d20412c786fa82d588a029e41fd0add80c231cc1d4838919612ac202e04071a49382423ecd8097ba2ada6c3c000000014040f5084a9d22110a6ce00119d7330124b04124919219cc77204011abb3c6240581c91d831d440000fc90000294627409e7951f1760399884e16570398621403686b23b5629d008b0a6b19a04418000171131387fbcd8ca0aa00000438c34147821aa27850169020288619004af800000007e78000080000006c44ebf9c9c330e691c000000033722b28ff4868130525df80000cdc00004e3502d000021a600007dd053c00007a48000107f05f2
  | 56 => 0xc0204000170100006f3400000000eb4658c0000000135c259800000003e340000fde97962a2a107c7899e6f3bd823403950f58069e142814495f028340614bcd0e5e046c01185380000039a000063314f300000000f7a047e2c86350000010d90b14008069c985e39ea78ccfb3111a2fbc1468409a0a740206620000014f2dda4610000185b267a11888a993ab12d031c80cf87aa40a243c03540169000036d0bb3987c3c3a0aacf1c09242d903bf08c691ed3f5e0000db6986b3a666f4876800003b0000001e69ac600003008303187340e42de8381877538ae71082a815f10ca4154c8718abf007c455000005e405606d705ab0f8400002fd4ae20000366a2c0d0079cff033c82f84818000190800000001cc830f4152c0000000000009bc0000ab2093214340001955340000000000ae3178449149ee828318c0756c86d941d3e287638156075e0fb81f688371dfe1e1011ec46117b92d5a37689fd9b4d048274c8a018f481a0a43d8000037c082c7e2000018b419c00000000000033ac00000000fa300000eacca39b5436b47be45c20e22001c5034961800000000c941f9009135a62954c0c02b400004608e1c8aaa0cbc686c0ed1b99027a405cb118000199208ccea800fd16186330a06092211da000015a9c4b1bba5d6000013a900000198a24995800003f5905c8f3f3dc65b041eb983c2e4a212c41d80000cb40f8836f965a0afe2ba07630bea000053784b210eb00001838c3c944415f80a18ad9066c3190000072220bb2f8600000001c13086c0e6901f80001e6e396c0001177179c76b08e31a760ed821cc64f8b1f186a0f80fc513ba142c0000cc200000000009445f0000000000004c38000319e000047201991328015000000001d2a000000010112d940bd400017c2104625c8eb1205f2e780000b210e8e13e2262c1e905e014221c5c610800000003f2897c9e37103073780000db926887b0400013d600004650fe68000000016f9067160902940a8038d827124aa54402fd97d600004cccb1a000028640000eee06180c4e7c5c4fb9256297e0f54505060329c008dc91504383d44000075e94662abc3b3c5b615190000152072a835c000073a0000049d00002c90000000003926c8c000022629283f1449f8d2a37d600000790bed39ca16d4437086004ba5954f5503f709ce33d80001a5133ce0130fc197c4407c3a7cd340000142000000000e7a13be00000000aff30a00000ec39923000000006ab80003df0606c000000030f01c8c950153917b46be424a1fc1367e63102b1200c415e32f04fc05b429660af098310cc11ea36a800004122036211c5d18000152c3204d3f100640f46b9c000020a37e85ae0000118901045ff000006cb2c28188049d0000000048b4da99453250411a10220340000041f05b18e3c13562b0c0fa
  | 57 => 0x499b339106fd4f8c80003bf2054cab711af2d2a29fc0001b7000000000098800000000000e6a00b736b074f0d16800023c419402d2101c372a2df4630800026005a249b59410183e0000f33827e20ea5960e3f9ecc000053f80b38000000000000001dde2d543144833941e120c6f281f709360000820418d824303dc52dc1649dbe09942c2025489780e8c6a000000461000035b80000fc63a1e44c8b0c1d640e08777c7550a2234a450f01bf9a4d000000005e60812000028540f90bb1273a0268b2d907b0f8a6fa03ab073f098647e102a19661b9a0b2c6e984861a6a3a0879419ea3d7a578cc23179f08a86dc4acd000040041078bec8b0a20720000000138504e43b084d791e010120000d361c7d0342744800c84923cb00bd0c0b9cee317c32ccb1611c115c8000065892ce3f7c5028b069d850c7409cc00017ad23227808cb51a45390c3e58ada86e1055037485ad0af7012629604728b99000000000001ebe0000000044e996d000000009b1000000002a807f5092d2790001c4cf04023b4a46708b51ff11a205b9400000dc00000001064887c06303b20328998d2b247bfc000205800005fd071900002a5200006cd1dfa01164c74db18e77078200005e41b59108402404060e7800005ba8d83149c00000000f73800000004eb0c740000341c7ad0e0d80000fe072c0c270560035e0ed418c86cf398c077c3a10df82bac24c418101ce12120fec000020f111e5c3c0c01225402e6524ded0ccf31fa7d503989f311cf82ed05fc8be2347440b80000c37000000000000d5900000000638800000000000000000000002160fe90848000000000000ee30e14192c00012f21d3400009bda02728de00002d68000397255a800016bf18900000000000001ca2b8041f00000582000000006ef00000000000096a2cec0138fb6873b08ee0a58fcb00532d162e34c988c630a4a6f74a579089230e33f848296fd312a527865d95a7231c3328b2487972b6644dcd8fa0492cf8000079a800009b44a5c00005a02b5e5b7800018690000603c5f38000000019a0d1319a31b1c0000d6d997d00003e801349a8f0000000081900001c0e63544d5052f00005614cfe800018d60000000000008a20000000000000000000000000008924684bc38a482f1c79c88ac8ad513e61b18ba90edc16842fb82af1a8b39a266a8efe16e02eb467b412b1ae8059a5d0ccf21fa70d5a5540d4f850228d876c4f1380e117383fa0736129521143948fd5030a018c3094a5907083282744ced794e2051c000069e02221d600000aab8a571a3c07b0b1200002b5c7b080001719228c05c00fb00000ba432dc17d0ac410861a94ccc99dc417449240001ce1000023640001908077c3ea003e12d930e451588ba9c932a9c2908415822d20ca74589488d37032c69e4000158910f
  | 58 => 0x5e000087280003dfa00000001f0b00003508df6128100000000cc99dca012c000001ba0332490832c85b9668173e57383379e1106b2627ccfc88af00000e4c0bd986c3bea0000647185f18200000470909a04d815a4fff03ae27a869dc9cf8e760310231c0000ebb00000000b191f0f000034080000000290a2764c330d6836fc313043d0009023c2ad046b1f7909d26d007aa00000c1000000000786000013749e096f40d787ff0e471ae400002dfc51a8faa00006dd43ae0c262ec43f30000156824121858f2d9b2b3d6200000000000000000007710d850000000090f09f93ca6600033680ef2c9a5328a3e8755161260bc6d6800000000b7c00000000000000000020391fea49b8e6800430f7000009d80df5071281a0e5a800000002ffc66680000000827ce78903c041c6e98000027b2e8017e0c7b87c31c940000ce918e707146928000021400002d34a2d81a529d46ed40001e74247a000000000002644056008a05d31da2000066016260000051096d1d4d242200000000000112a000000008b82bc0000055600000a523a400001c8a0000519497a0000000000009d3076b313a0000ec21bb2393a235cca68000000074640001464389a7e180001be30da05c80cbb00002a8a36283a19b2f208a0930ba404a700000000000031306101b790320d5e3d0a00000000e6121f60d50d678cef00004d040000000000043b0b8a8000000027f0863012c000004409d103740776000106600001f7a66749f48c761d0a729049c168c041626f0f92010804e8000041e8ab7000039f885f9fb0404677f44da958a2f6c0d5477c1a8109f428380000cbf1bd41b4cced85bc000064147860959180c5984db39ea400000000000000025163170000000010e83a9436480000000065c000205900007510bde0000032441d8000142e23a22fd03d0116725e061543411cf6392a0000bd90c4b00000000e1700002560678c00001d223747b14f2d16011e825d585b0176f0c3200003068000205800008cd00000e983bfc0000334000024a000018bc00004b6c0000000000079f0979922223f600001cd81421866583cd850852006c58b40000000000000000001d1f2cfe494025c86fd15be34543d79c513d7451c495c80003a123a64b4913491c1e02b80001314070276a819a97cf29d82e7427b09e4058a4154c43181d224c7c0ccc78c1e0cf000000000f530000792c66181770f5682a4cdc097c239a000000013e61e200000000000000000cec68d8f3c38606c10d211eb01f4c6d846371f8000005bc0000000026bc048c000038217aa4c8c76e8c6200002728d7504b42d3c4a6053893d9141800001b6000008962dad058035f0846000045d095508b44ab486115df0212268c0c6997738ac16e8d5c946700001fa817880002d648065047800000004fc468
  | 59 => 0x193812bce53742e4139e1c28327459d9012014e0c2c000146800000000cdd136c0ac6604403a9f7007980edc0000000000060140001f260000000000013e3167c000098f8a3a20e2000081c000000004a0c0b6023c000026200001ced3140000000006f1356a00006c310df24e66708e0d1cf83c4a79841ca8000210e1314c1880003014138c8079ff71d567020f0196d70b5e0000b7c800000000000d018aeb0b70000000010af00005ccc3ac963e082e0000000000000006480c438000301a000000014280000000000018b2187e7b00f3984142fb64d700000000104a5bf82f710dc3f5a000000000002c4a00009c3002c00000000d1700e70be0533478489210cbe03e89a116ac01fe3a250211de32ae2343cee10f34151c000010d97600fcc5560c7716c51c7c218856899b41f700000a310d721c30205497688a3085248283eb87fa13ac6af49df000030167b70a581c5d000021b40001aac0000000000002441dae29cc4a719521796377c0000d4e0ef87c0094f08493870617000005d70e8e000000004662ff643b8e7d014c00004629062000000007834000000026ec20dc00000003c580000b400d9900001984000024e28b2000000003b421c000000000b9415ec4eb40000ca41d5c08580001d7400005dd905680000ae827a85cc01ad3f7264c86230000000071809dd939a22f200000000000000000000001c28357800000000000000076fc00000001658264400002c30356634041685da17d27b544dd84cd00005e281b71c540d460000000000000be7964000202200006920000000000007a84ab918dc2d6851b405a8eb50ddc4dfc6d4956400004a9c6b18000335e65fc8918e811f5871c45e0813505e07be8f291a322ff02e780000fc22b904cec5170387000000000000f2e000643a88a8000013020000000063e0d5c565cc1815dd0000287cb36801f00002cb89390000335a82c80001a0b19f000fcfb9182e1b1a592000003ef18ca0000c0201b32a8e7550ad880611b40038c0f011161c660d1401a87e11552258c49d8ace1bd21e14b3817462d2c2450e4698d32b9e0f98b46a02500001a80c70000000002e58d10800000007bc0339807a3c864818c9b80000000369d04180e6000035d00f48df9000029500000a8a192e0ec4000000000006d140000c1500000000f3f1cc0132c11b0000141216ba6ed0000000032540000a5480002102040c62818d1107e1d7484d82e50000315c9f09d683d582a44b8d9ce2015e7bd4ca8020723b80a64170800000003d480098000000071ac000000000000000000000021667a4c00000003b387fd4348075027b678d8000206d0000000000000001e96536cbeb986333e674a41c289b900004fe400002e20eae0000afd0000378a3d9cd770f4200007ddc5778540402601d800017b70d
  | 60 => 0x1e654dc3dc9ff41d4607e06c58f39116815b8b880d642faa68f8fe50bdc38d43ab40000e0b14620b985fc000040907cc08df08f03f22651009587f324a400002ea142c147e0000cae153d3750000000010861778000039800f13af02a689c3970c0f3e56fce1b04a8125c505cef7142317ae6350ef9800040767ba82e30807000015c82d4941f14fa00000000b66000015f06f7148b0b1641680e50b712e9c000000006072cee7a5c00000003a340f2000003380b7e3abc2cc8751076000005310c8d1ade499c3490000197c120c000000000001ad4a0b068a02bc217502997e1130445b06c11f23147c79dcb338c80290e6f8403f061206d23b90a5c9e013af2349000015523a9e76f46068cd823e2539cde1822b2310111870a93a1065430244d68f1803620000e961ad416280000fae80ec22540000df285c22dde4ebcec910ed3a7c58648d9877f2fb0508819407161d9275b8a029d2a245c113877a9e3237040c78a491d00000005847f0096c350a55a4b7893c61e460000000000000005eec95189da0000185c2a90000358e000000018ae0000000000000000000538c000121a32de00007fd023800004e08bf88b95250a1d9cdc58e4931347e6c473845e13da79fc7ef1f1500001a448c28abb000034584ae14f90e8870c80000f76247038acca019e6093c0000f4400001bf822f4a1fa055026458800838f200f4478f08511eee0c02219ccfb0cd329ea7230b6900000000000066e88c60000106c2f980002c0a57503a515ef1ada475505215a13f386030dbb183e00002a00a7a1ad51b1e004878f0059072e00000000000048c32acd8f02973eb0502039a99f400bc78980d30bb60902687cf241b0304507bc417fa05d29200000000000000004f24c2b158000000000000182400004cf812500002bec73ec59291bb33d863c04cc03241072250c7810558297c3718f6f9b9e07fe23b04130bd621480000ece98833460597c00010682c7224484f780000000377026e000005fc000048e00000000000000000000aa2000000000000750222415b181f00000000000000032c06abc00012be17ee32607f89a5f03025b7038d16da0fdc1dd07fe000027ce80d80000000291a5ac0466026b00001f38ea90a41109c53e0000000000002f50ae28af139b80000b198000000000b40df08d11f1e31e040200000dcc0ab4aa080f93ed81c3c5e50000000030886ba959f26a4000090c1e9f23e6000000000003746157c0000e6700002c400001f4100000000fea80000000000000003eb000000003ea80000000000000013fd1d2844d0a188a5604524950489901808e6025c408154d112813dc09c90ae2d081e21010097014640f58c2116662aea44d5019208c1b7e0998f9a998541563d0cd8398ff249a5decd54062c288e0f9cfd08c5800e0187c2
  | 61 => 0xdfd978b208053d89778a6c0000625833a0e840c5c2294b7983363df857f8ccd000000005d50a1d00002c442348247000019345ca84d3994608325e340000000000000006b880000000110c87e0e282ca049ac8879c753d0c000046984bd0db00000da39c3a394200006d91e2a021a000000007d11e327ce40000000157000001c180003964000000000000d86826cb499fb600000000000196b342e000000000003cf214fcc45988d04004b883c4a00515927f60304823f1a505d746189b6533b219643218cd72a4a734c3b7000226c2455cc1a84253dac00005f3034c27887d3477f000040ec00002aa00000000431c00000000000000000013ae0000750000001d3365a00000000b5028e4000098806f219d8611c00012373f886fd85ba8d01000000007ad1b72195e771400014aa149c326426c8000000076506e292323730000000000002d4e047c0000ddb03745a7c9531dc71b50267098b96ee00000000000000004bc59d401e1ade23a44de84d9021a05640084ac40893072082cc0ca0aa62a1a33883b916bb3f8a714cbd4974a240265901b180c800962d9026c03c900007940000000038d24a10c820efd000029b4367000000000000b34851e148c5fcc6820f1d370c3d24fe594bd284c78a0ca980fb3d123de8e24071d05f6782c30d80002a0e5d04a42000012ca22681a7000000000000fe399143fe46b982380406000055fcf5b836438123624b03863d243a4e24fa389441b385c20c44a07e2f80785cde3976922c26c245ad8dd03a7a19188cb99971cc6277043795533e527d9483c8cd2253e5288af40bab3f2e01e40eb09a216e436600f7830e1ec271a0ac685e71a566fe0afd8000300628bc87c000000002c9800000001ab0214c00015db18727d900001962000070a8ba980000000477460c9713286a000000009e012bc00000000000326a0000dec890f00001084ac38475061a67ec816845820600b00000008d063407900000172000006885ed8b3f347a00000000000000000003dd8b1500003a0c0000000000072045750265000025c4e65000035ec00008da800036a20000c1d8000000000000000000000051cc9f5931b10485148cff0000000064486569d5900000000ec08d4737060d200359dd82158064453400003c7e7a305f903150e7239c8ebe0fc300005448000000009d40000ef01613000010c0376978f204250e05a28b2d11e452b800003770c944c5800004ae2bfe4cf0c8f80001aac353000006c7110235e4c6c82870e026fc0000048a0b8047b89908f7e0fea48202581aa22c104be0e82805000000000261092929dc6b5cd5283de0000513c1bc07ef226652b10631e0a242c5238ed9a0372082652040780001fb01f006f80a0138b20c9817e0b3c06ce00007f70868216800000001cb10000000000002620
  | 62 => 0x16262a9476b15dc405e041844e143e2a2c1de0a0314c715cc24f4000000005626b8c5a2062428d40000f080cc40000330904a849f00000f8d061800024a600000001ddd000064ccc9d115a000057f4000081c00003f9ce6590ce0000000047c00002f8a000000000000000000098d000010a26f2c0000000139600010400c2a328647a8b630000075a58a8bd418c000000cf0b3e9aa7000000002a0800008a434c852f18d8370a000000000b9000000000000dd900000000000000000000b8c7b700001c680000bb714290000000104f097e29ca06105100dfd4056000005904e235a00000528100916a27f50e6b9d751ed44ee475a1aca19101088f9781e7237e4b2c1e88b571c9e5b24522079202aa2b787ac85c70dae6c9441490032c6a21a47df0edb01a85c7488017ff3b487de06de8dcb0000032834d1b1600c42924a2e800005185830ee80be110022d940000ec32b9261883718f2d1ce80000284113c4132765c000123e14ee00009e38a3613e82f0cfc3914e00005c2cde48000394e080cace116b1e9c44c0e060c5300001acc7b606b02c3e19c0d0285ff0b0a0f100001c7c3b864e0d0270045090e610cbd2147a11527a4473708cd0458787c00000000094390000013ce1efa3030e8d8000000068dc00005bd000000000000000000000000000000269c079845a986a14f061147870c85000051dc2ea85e300007434222166f0822788ccdb94b5175e10d0ea893962e040000e660e7b21040180415028537ee3e3824615d7010e06dc00005fd367a6c7406c0956116077d86c89e4f0d4479e895607e300000e2ca30020900004344ef28000000081888861e4d19d24720f5291d80b3a00007a780000daa31a4a8880001a7605880001cd618160a44ce9834d106c25340001c3f02e80000e9689793ae26c540001bde1fa2000010a87e823c83c5400000001bc861fcdee0000000002a400016061eba43a4862802e31c43ec456992bf3f2019106bf8c733fae00002e18000383a000026785a2323645cc0000f273a5e0deca411a1a00000000cc00000000071ec000000033825cb000003e4000000000000c40140048cc454000000003ae80078000000055cc292010b23ea2c0004902fd10660d59046800023d82a50f070211000034fc0d39a23363670642ec0819000000000328eda0dd63dc4e888c04054e589c0351b100000442059184f131d439a4583059b38c26728c65809431e868642659263214e4e2809f097533620000fc7077911166ca8d3d1974000062d4ff9847a04da3d884ab800035284ce8bda199e11ba12f85328f9c2180389401d1e293ca26604247995a380a3ab0b3d970a1c061e9c6c18220163800008618d5239aa42e8c380ba5157c7724bb40b8a0858070ce53122c254432285481a13162457f05020727028c24d4
  | 63 => 0x93028124a24c1ce7491d4391e0f1c0001b9c0a587c78c8a855b1c024d5ce459ed40000000040a1e3a34507e9820680003ed0000098c8d340bbc03808c81fe7048e2a700000000000000000000fa1325c00002ad0846355c000000000000000000000013593e1a000000006ea2740582cd9200003618000031680002a12502447a04ce0b6e42740001fda1d1e40dc0001eda17125d30de10f5609f820f0be6888e17487a3800000002c3a0e300000000388c00005d7102426c8000000000002c42000089d9bbc2cc000000000dc0141a00000000000349e4fc00001d5e1e1a62a8369137139e6297078f9144236e5cbc0d1963b0b0e34446d196ab3de43d341479d23236c1380d7d834207ec000052880000d722a0c000058e344470ac0000000053a7080ad200721950533807a811a3f2649fc0000b2906de000055080000000000031f80000000562c59b8d4800005ec0b6b0358007a5a640001fdb2542000083a00002ba60d0ca7584d10f180b08a678f812e0a4df4ca6104c077a31b40000063174065c8f181b731d005becc4806dc137c64a40581d410a3251f000000000000000019b99960da80000a968f9700001ae0563800012ba022800000000e7a6af80000877000082d80000347245043845ba0bd2033609fcff09d6018882b140000e87000000000001f4f0000000000015c7333e5b101f68250255000000001e6c000000000000ced1c7a0000c3a082e0000121000006f321e416940000f7b15e44160bb1857538160d284d99f6a2ca42ca8b4d1e1b141655c104b921f000064983609fba00001ea404d8000327e3f680000ff634bc3c940000000000069fc00017793f347958d94000033a25300a8b910e065812c4c63800000000000e5f82ed000050d08a90d2e1428000000010e81fc423bc02680000e404d1800000001f143ee4e751f740fce0dc46f0974f3d00809800000001e222ea800012353e941cdc00000001ac47ef0f371fa400006ec40000000334800007121544000066986f6033d00000000000000020e6000009787c116bc1e64a931986288231a07fc0000249c2a101b9104629563b4800017a0000000002bb8adc0000818cbf7800030b022487458d9f1f6a05501f60c551e56000000020670000468caf28000000000000000a30160e059099300003b340000ae50d2712d666eca4c152e0000395c000038f338e00002908000349681a4c668f6300005c100000a2a3f402cf4d1f80003ba808142bc8ed3000005a00888000000069580000000000008e44b3829a000022189131a5d2a38340072c1b570e9c071c31e000027be72a000014550426000003d993e3a967bcc000115d0000159421c8c420ce46ce400016793c6863780000c0805e47e8c0000034000259e802b85a800005b64da61fec0c14000021b842d
  | 64 => 0x211e0b29054099a4014031c6439a961f0018c028a11c325d232e40000d2100005fc8000000000000000cb4859c000000010070fbf000000000000eef00007e3000005940b6000004ee9b1c32e013503b8000006a66b70a78094b202a00002898d7c0b4208e876287e4138e00001be80003e245c1cd62800036ba0e50d55050e1cb47dc4b7192c414c600000d493c50cee2da80df81493010356cbe988030000590459a12c906f26648a97800034561988ecc998b00000000000000022d0364024d1b7a1cac68c4446120e1f641a2c00005473958000062c86710d1a81189308ff42c361570000001021e63fac12a8e0927e615ac7ea85b200000d84d6101db1d9c66acfbe0bd915b21a6c1341a4c15e612d87af04c7222e6c9c84a00003b505358068206b06660000aad11cb1c0a79d4e0005cb27d07e10614800000008000d7b81c11d984188000065740d45f68de09b361942000009f828b2d2e5f4097b000000000000f35a0890000000000001dc00003b542390665000058440000000000028d0eb816d5000000000000cfc00000e006fd09c1237a59187e580001c22535c0001a8840f200005939cce07ba43d03e305730000619c000029501764e6c00006000000585c000049600003d5c1ba993b00000000f68174713880000000067900007b180001d0615102fb0ad300001b08000104292a529506318000110424c81898ee203ac13cc359486b06c51be2373cb711a53000000002d6190d200a1ff06eb80002786000000000000000000000013982526640ce9c972323fe37acc1388a13740000029917710000049400009b12b284bb83df0000000005f0bac92800a66000056100003a943f90f749da0045c534c51480002c087cd0cca959900000000c169da12ee4095c54392d71a0e085c47880003b463e5039c00003e220000000000000001e00000000015a800004c69f7a2b602528000000002b252200001df800005b7cc461e54000078840649ab30f923798d54889601ba422cd50916d2b840544e1e846a0a0803105c393b600002454000000030c877ecd6b000006da5d24f17105d315a0000000000010f25b4c0000000000014c44bd076f27fe0000000000000000000f9007fe0f0600000000366000000007051979321600004e7000003a244543271c8500007364ee88e920c6e799475903c00ef60e6002d800019f40000c1d16d117fc000000011b9000000003e593d53e3036bd023800000001da000008ac0f60733cb001b87396e7470d7a1c6e25940000e7315f4000000002c99df108b24ca037d0000250c49b0a0395ea00005978000138b2ab81ff484f161609e65bb0000000021785b6c00000002f9c7100f4797df000000000000d1f0000000000005fa0000671080c90f13caa4808000018300007eccdc49dd2062e000
  | 65 => 0xb492e05f411b07c1010e82d50a403e1ca5b009c0b7601bc6458bfb3e805f4480e966e1eb8000000017e32612000000017980ee282fce3808f7242000004b102db00004aac513000000003ad80001e491154500859010d728c246f003392bb382e459885e875805ac04e80000741085082f436d000039b41b44931169125be346431b00003f5c11b4dd58e1d3c3068d87f9156612c00a6cc3700000000000047e80003af67a1c6f00000244000000950f852732241029d9b800bac262442a800026e6511829181fd412635a4a1e8a4b00000000000135d2cb20000fec8f6f0000000054a99e200003bcc0001d0416aa00009821b34163050941d392683f1a2ac0485949b1e641358000000040a455bc15b8bfc3d72280c38000000000000068d000015b400000001bf10000000050280000000389800014a500004ce04a117ca3396469412e17c825d432e82bc1d5d3e8876b416c84bf12da0f6c46f181500006fe800002a622503318e8602cc39886084d088cb400002990000150e0000000000012c600000000793195d12b07d7c96e0b9000001c1400016293192637c4e68e6b40b82a7c1cb00000a0e000052e90f90fc02c7457e80000c8400004d400000980000000000002f461dd83228000102c00001441033044e0abc000156b17be0b80f6b913125e2725c71c0b9b12f65e300599a440e5800001cc8000000023f836213290000000070f0000382853c40ff000000007c9cbb30e53000000008b800000000048446e076d3040000086f1bb300000000e4d8c2e00002694c29058800004f901d30f5f176e4c3c7bb9d8c0e5c56a891f941837f823a88071e3e3c2a747819680000000250027a80001c400000f3100000d30781098e1b213b3e47786f1158e0e1a0efc067979718fe390c41389ee23922bec00012cf13ae23b8ef20cd90000781ce3284b2365876e415287910bde30804390000195c0000db41b1a1b5c305c9a80c92000029144e89f8500000098bb5800030447edc8ac000006ca5ef82c00d923efe22406f1a0980d4e4ee08af0fc70e0c12240a5985d121840a416a047d0f5040e8d7f04bb00000540000000000000000f4d00000000000000014d4000000000c7000000000000ea380002c5c7718b0e0000291419984db8000355a162429c83aa34141324850889700000000bab9d4c1dc24e9412d0bf0233c0000647800000003bac00001170148198d0529f3e1c4659948970388028e4594ffd8acc2a78000000016f82d463f040560000294850500001690418e227c3ca122f405c4c14fba9ca00fac0ba0000000000007ad8bc8850000000ee80000ae200525f1c000057632f47d30000000024fc7a5430d1e4c00005990c9205a6344e41a50268aae00003fec91d80000320778432c182a0e424fbc8fd0f6911365178c4120a
  | 66 => 0x7c00000000000000033ae7028d6c8bf12c8e000072309a93256656cfe71ef735480000a538b693c4027f4576023e01b66da8b7415280000643874b80003baa6fe430982822ef40238000054c00004a7062a2061239828a08a7826e000000008039acd28a8833c2229f062eb6820857099be000033dceae0000103416048c781d432ce0000000000000004d60b8d00000a5041ac000168f00005ff481f80000000000000014a602b414d47b2071310fe626c3ef945f2efe6c5c2ed8f833e183ac496b11b40f48179821d041a3d940ef09c60c4e22360000a25933633f876c850c00000000116c0001baa10ea2a2c38e00001d4c7450de300001f3a435000000000e18216cc5193662f3647080209b5f105076346b5115c11ec2c687150321000011f000000001d4200006e500513d9073c055e83e500007c880b2800020c862cc98a8000000074e07c418fb000077dc64e17d4382c0000000196c0746570c5040c4a20ae63480001b9713e4000000000000000000095b9aa000000c8800000000000000000007e2000000000001d9615fc000026808c003686c005e889861f3e7420c88827600000000ca5000000006638eed00003e380000000018a24746dacc2603cb3e74302887b95ba0000000000000000000813ceb699e803401ba000000000000709079080003d4e6994fd408d4256800006968b911c340000d208ebf075230d9061049724524b35006842a1b2e0000100800001420404689000023062ce0a640f603bde3f38db7a07d37606f4ca8d00bc0a0236d432d9e990652399000000ea03882a6c1298a1a3946000002c1813000017a0205124a3b9a23a400004ba0000330502180003edc00006fb9af200002f600000cde341201fc0001e6d00005c34a7d80000000000000005e1000000003a4917103b21ce8c548c9300004ff00000f662efa291c6aa172808a02db82f49e41081622ac3bd17ab17d68130023800021ba68e000004f838620000e1a93b732a27f941ff00003f321194652827909d05fb4e3c1ac92eaa2bb444c158602dc3190f7214c122062b04e2c121707e60b44c009c4c00005f2c21a80003d7800000000a6127f4461893d15c12a4012d456681bd2b188058e239d150c9e000104e96363a607188daf15a5076c1fc41129fb416a81e784a78ac0176415240000e02000023cc7a514811324357c1210a240e9a165853a89071458797c9550000061850b43da1efb000067fce758a721b667c6c1181d2600001a742e29424323c000033500001f920000ffe92d8320e0b1cc220d5d3a8a0000e4a092a395c10c80001001406a540c0fa8faf35e000007d49ab237fe00003cc00000000756800000000000040800014d90000000000001782ff2000000000003a1c474c526043c2d78635c0000000000053a452c99362cc67a
  | 67 => 0x6983aa094109540d88ea31f081bde70a41420e9c00006980dd080003bce0000227852d416a246c56d87d808622a7484c9c55234e06c0fb9813439765d845c990a83e8650040001ac1000074809c2019d388a81bc000042f3eb216b80000000000000009be0000000022904900f0a3acc00002b891693a620000000000034e02f34a3a89c60b9e52805d08e3117de76887fb84a6348062ec0bc8dd53a0e2a5cdbe8586000049bc04280000000000069f104430da0000000000038080014000097f1fca3eac3848000350e00000001aed29c851e4643000037fc000032e00000f6c37f800000000000000000011073a301a5c3a0000a38e66b680001fe20b2e00009ad00000a7a17343a980001694000043d9efe222849e07c48000125623ac1ab96b7007204543b2121c0dfc0000a7b800027a40100000000009567170000000000006bf00001fe4000063e42b30000000000008d885450000000000000000250479c00008340000000000001f938bc0ae8000000040ca79e02ff0e3b000081fcc401b91361c21aca2b80003a140000b36190a2ce820c0cb987f70dee542864b1a203b0c0c183811839000016486bb08cb37085414a0a837638824af0ddb136702fc48848af90220b3c556c67e9f8f2e761a8489f855700000000000000027484c78006932a302804800628000333082d09ba0000000048ac00003da038a072c0000000030c273c0000f74000000000000000000000000001e0818b600000000000000004f0627914500006068f3e99213f121310c8305d1314c0d103669bac339850ecef4800000000000bf10ded2e4e0000d6f8974180a11000f09aa611be670056e92591c0c5e0000000000000000035d8d8130207a980000d7e000075a8000000018ac733489210353682344c4a410540e3200000000000394a0000b288b9a0174567828f984f2d2846b49a8927c000000006b320c1000000000000000314a0000daa8947000007c0d0e00000000000057a12050376527c00012392f5800006b59c5f15ae6a64e7900001c724f5c00010ef00001a4ceca979e073a614c422000005440878bde8f5b2fb80d2c80518e939782530000153234aa0000d0a94fa1ba8000064a000001981a9029a104b1cbe804800018ed374e18c40001c3c21a4703cb2980002bd25fd490600000bd400006379b4208901f50f3490562dcc00000000b0125ba23140a902c600000000e56974b3e6c5d947499fc30f1a05d49570c4301b2710cd64176d253a513027d940b0d1005c4b2615233dba50846b01d4901064da4b7911f711665910d588cb83bd61b6c10c9c333b1446e07878c142a4e0a785079f62272472a4f74120336762ef410699d02d661a3c000050500004688a229b4f06e66688af0800003ba00005e212a9105e00005dd8000000000004d80b
  | 68 => 0xcf12a7049d87259ae93a060534fad99900d2a58281301f2b148036f0bc417e8411624f0f00117f000000000000000000000010668680100a72f891e1c9a2590000043b0000095823684640e5026a8795c097048b01000000e110000194641c8e038000374a3134000013332120298e88051d3f908250760941b0e4a4ad83551598065e00005dc16f5238a0b906e708780000106000013a713201da800000002c9434f4f8089d500004bf8b2b0000000000000001e22000000000000000000009f099b8a1200007e04edd800026da00010151ec3000039fcaa00000066000002e702ee00003ed0000000008401bfc54280002a740000000051514de1ef0f099ebf11f800001400000000000000000b223f3a1a507a80000013229f08731a893b04646006f09c83b6000007b9973e21a0478cea40000000000000001b8823c200000000f1208e21cf8e008a6600007b84da195d2000021588a384e50a0c0000000000027002ea47c689540a4c04e0d2302a33d9e42f833f83073b3000003cb00000c040000a680000023a0000126800000001098cef08bc292a000000020c500000000e270fec2a6833fcbf4804433ca04d853d03863ebc00005039d90396844f430f11810d5634b0f7016b600005244c2a17642e7235e059a90612afa41a8a8f032b3e2002f8750194b3eac2a886cf046b0e4468bcee01a5a147001e0eb4973827e40f38106152b18601b00c61973701ae424000017b112662680000201d248c7d485b093c00d68300c44504853c5a6440d4107f62a762080b1c031d1412000013b81e302fe74910040c1302f44ef0d3e1a7b323828f4911911d1a18146ccfb8ad80b6c66a0bc1018b356e007471f92002f0c183c6590df201c8570040e8b3a2df83cc46dd9ae23dec71b42910e680a9c82843991add2da046b84c196ff336a3e8812a209a1e586bfc000000034540000e8b8000000033ccb5401cf3e5a000048e8000133e00000001e68379000000000000244e36f895e8a790cd628ec0001e660000000054f0c740000659400000000d0a2130da215b400000000fee0b731846000000004ed000043d4a28000024241cf0000000037883c007de1c82031e36743b0833e3d523b109449b4800c8471c8e019891ce200000000883410e404005003f416da7f785f4111c0dca00000000d9624bc5970269173d26481ed440f128c04387d082ab089106382dbcf9ba0283d3600009939f5c16963e6c8fc93de2f067008e3b0d6130641f4c86500001c380c04fbd936317ca4794668865d1eca000033e00001a947c1c85494c41d66217c62481ed087666f0054000021b430e8f991e9d0b4e2298000000000000a7048b0d231d9600000001f2e0d0e75f4b3c00002aee00000001be4060835e83471938178e382013d0aab3306714837819ce08f03
  | 69 => 0x47f400d01951fae0000bf30000057a000100d83f937a80000000000011b64d3493c9105161a66fcfd594df00000d185da80001b6c13200000000000061bc9fa000028dc0f28fc58a5b1e60755cf32000020760000946800000006fa400000000d6e0000aed184926145c38c8002be39fc00a0000000029da0000000000007a03db400011363418000000011d932260e80b1416032b3662908ce933504900000000000000001b80f1c89ec1f30757ce3c8000000021c04588e9b1fb63ff868e989e372663c82b506ac3fc0809050c9a12085c3864958820811645b3021f204500b842c47c316d41dec03f0e1b89a132fc6a4094d00ed006629f85c9108010945a84adc8c7710c662f4dbd83701f162f3c92d905f00004fb00001cc52854782400000003e5800000820ac6000053fc3ad9a6f00005c50000000000003c506a49a3c38c60b5cc9a000000003f400d51a64390000000001b64143c6508cd60d5c17ba16402208122396c000095d0fd328f6504449920402a7c42149a2a00b04802ae4bb99bd840f000000001be00e30387c05681d530ea3adc0000e122d0a09c026f957e05900990a1005b107b20001048815700005d08000000011f20000e0313e2252425bc998010a2f125d14aab0d1826de14a8d2715592c8a645cda8148302480000ecd99b02190695d051822a000000008d0191a0cc8730d03a954f05b07918cfa80003d7675d80000c3d1d14559ca8c00003ff40000ef400001e0c023ca6e1b691efe4488fb4872b29782abcbd78f2a309445241d9068c145a332069d1ed3382a288c3081a5039f225a4a8d917a1080466100f99f2334a62889fb9f2a1c186a68b758c7b1f4e555095917bf0e5213fca950298212e4dc0c4b87a60e2a0c9ce48207713c4736c67d98bf30c26eb46781b8134b2719c6e19aab203413049ff0de72d0401cc97d02cf31ac439cff5945800000000000000000000000fe808ae3ba676b800015481f880000ac781c00b3e000049c950f184871b00000000213050bc0001d343be8816cec7936536647f0820a8ffd000000001738000269e23880290000087e0000d778cea150c0000eb6069c1ace0000d120efa081e2380588a0ca000026e800015f716e00000e8580002c560f0c3d60f990bf85ae88a08a920942000000000001c2c000000000000a9e1bb000000003598000066b000000003048000091a00000000973000038763b1ca31800000000c4090380002c9e06b8d3680d60a7c53f4b52000025d0000008c1070357432407650ce3205e284c2a18ca725a2163c8c594d52428690d01803c2000065b8abb00000000000000012fd00007f4c00013930f9000008f4800000000c4400000000000000000000001c1c0000000206e000012f0c30201110646774bee825806642638eda8a52378014e0c960
  | 70 => 0x9c911e6603045748b1b000031b0731029400007a588bb000000000000000000000004d540001f94414400005a4992813a42e1485681fc045e52e800000000c66000000019221502785881b1a25341e30f86d09c34295a39c03b31c7239fa4c0c1b400000000669c0cd0000000012087e40e9639440ff4d498000168062109d41f1f00004494a4600000000000000002f62e2e352c78180003b6e3a349969d6b232a2778ee08a8f26f03cf8443911920fc5e7492204de1442530884716fa2af01f6cdea8db832ac1590ae69b0d33be42340b000000f6667e8fdc0f46224e7b4845b9c7e3b52350c3660bd03dd868740000af50f08000000015131fc25dd487f0000092054040000b16000000000001f48000040502970c3814940000dab00000000000000008e80000009c3710699000000000001807006404a4000027500ac81cc00018ce00000718000000000000000f7796980000000073680000000329822b00000000625101e8be02118000000006f92e6c818088110c90000232404304f915460000ddb82450000716c33b000025980bb0f9f9a10078c62c0bf3a057019644acbcc98ca197a03a07c88937279847584c989fe09b66c88b7b17093202229c59087a307d23b98bf01d7a000003dc0000d770000432cc0f000022dc7b940000b05289000006a98cd431e63da081e891719b471dcbd1205019060000dbf80002d020890bd3115b000011700000dc200006ae00000e5413d600c0a6d1bee27683ce893293bd1358248c47d09fb3776160824991c43a508128aea8a1724b449d00000ca93bac00000000d223a4a340c00000003e267ab8191883807ea00001e980002a183e300001a5403bc00009bf18b9000000008c00d0d00002630000000000006a5c00000000000371018f99753ede00000001d270554000000002dd00004220d390000258a442c587808927940df80fb9c271fda7d44b8b0000389e5ee064a86112ac62e3cff50748000029a41a494002b6c0000dc51500102e11b800006051ffe3eb41f40bf333367d143ca9cbd184e1270ff3090119e86194cbc09d83110243451e17ee36ee1ffc78399da3ab00000a4e9bcf33f0165400003e100006754db00b3900006db00c60c47405221146a084ad24ae1b209a9931325f6000012882a1003c7b38000035000007308df100003f044098c7e0148000056f8000143606826f98000048010c241286999524122064f4d430d0b146e2d3c11a189230fa0000000000008180000000000000004c34000200101547c58cdb06ba2662657827e98f52ed4706000018fe00005b90ad5800007f07d8000000000ec424bc8d40d510f8e4500adc0c6708de6d186c40eec1b2a8178eaa9388105879a80da92663be413d0687079c1d520000f638b5c000003484f800001b921f2814f95743c5e
  | 71 => 0x66a8cc1189ff110821c4a02000432726b84d2d934000900ae4809802200000000650000000002efd03d8000251457300001f5000002d38d0a18ec04206018b44117e34b854b00ce078f0af6475cc720f923d461da48ef9d430dd25de0e161c922c60270042b80000000000000000001dbe0000145000037da01d0000011931324890c3f1d35250e0000ebf000016661950000015f00005a381118316000076d0000000040620000000119622200000000000017800000000000000000000c1e99c32b7a37cc1828a93092a00008150000325e249c0000000325a7fc00bb000000006e7cbc913b32e7457e47069a670408176417981b620a24b48000144221f41c407979311000007200001c8320f012889ee1fee19582b210330736014613c0fdf91633bc4703478082ea2ad82eccb3580f6092238b4feb00000aba3688aa187820898044c3c0800005d201f400012e5300419801491ae019dc414ca3484e6400c2a9076a12c01336000038a0db0279618ec77d9c96338c115436b14b12e680000000000009e47ad4436081f08d24cb04ed9a73162e0bdc77500313c24486c73283a503f603f808916ae39c6213cabd190f31625a747e7970304420368be31f05000054cc0000ce10bc443107aa8cdf136869a8bda888d1b8e39745a60068216c5c9900f000000000000859000000000be0a908fb6361032780001c9900001934000000024625e545c0000002ba80b0000000010c8000000017c10b182628805906309407cf0def80001d707b2c1c7126a00762cc44a285672d9e50e490593b10c38115c7a88fd9010800000c987cd329c51344db04a41dca614400000003a020000bf2111f033000007b58bde3ce238e800000002b586e58000002f1fba000077b80002eee0000e07151d09dc8210d1a0ab60cf400003e20d44166c0000721150200002e5c97a9838000052183df921508e81b6468a006e000000000f403cf0000800cc77800000006e340000cf5000039cc6ad134723b400002ee913e00000000051000040e000000001b143d925fd8d4710bb01e0164416f1c74225800009389e8a0f366db859796c7000000007d984e40fda00000d9203a268681f04189d0209ae000091b00003a6e5e9c000000026b64fe00000f9e17f400000000000000060484f380000c8e6134c7c17b3185a0000000105931e21518d6c0b2b000000000000b193142000030211ce3102497c28b88821fe63470dd7958200007818d030fef01e86fcc233a0bc31f46ad8c56187719c8061c0b5062514f60b4c43517ea06a4166901e1e6326ee40f8c2d079029425c00ddca00400002584abd8000117e5cc8a4000b40b941cb49759f4e400e5fb0d1d904d0000000041a98400000708c7910ab304c64cbcdeb9cfc26ea10144d21662080e28e4ad183512a92523cc0c
  | 72 => 0x58abc13984ec866615f833186304315044d15f07a34b6108801e7a57b0a740e45017e1fc90471f7d00003428000000024ea60ac0b7800001a63f8c67c9b90000042800001a583ffe1d8cf5c105e3660000060e000003e23044b50000037fa6ef400003a43b9c4b08f850000031200008ed80001b265b2c69b048d0a3033ac3190453000025489971a7d2b0819a4a5a00003536093c0000dd63218000045c911e35965848cd0835a146600000000312138457cc0000c1b05700f602048a8d16a43dc04569d72369244282a215de3f9863080000000000041b01cf056f104453f08f589bd37344f805a18b58051a2d9ceed8dd8301c6e50827835b29de464cf0e049800000414a13950612140000726800011c63980f9c18b60000000000000003eec0000b350000021e773073a989135a4217000005a33fba00008d81af10c6851d824400000c4200008a1000038067cf43299593000048c0d4500f8000000009b420710000671400001300c5e39bc600134a181c44802fb0a2500004834537101f000000005351c3e0b7247408fa1413228667c4bd2800002cc762495a93cd359c0000ba8000000004a3c3418c0732be1f406461f4b0662687800012d40370385c1620a890cea0000000012700000000ff680003ce000001848cb0171c0000f5780003ace000000019c9014a52ec000035d34d60000000000000004a6c99a0dff0000805405881bc0ba0000000019cf18761be005e9bae00003a9c311823127a245e00001f53000000004ce8000000000008041b3e233e484cc578000214c384c6e6000026964d801b00e0400000000959954c0000000003602d200004a20e6919822a6a1dcc97208c4100c5aa485c9e4503d434c08f3129903044e44c47976c26181d3c40d8c520f26640811e8e4803582c10744000c00000000af91718356867a4638025f26ac31a8b4e005d199c000000018eb2c6209f4bff00003ec20000867854d0000000091a000000000000f598b301b627aa03148dba2b2203340001b02102200004dc127d0000000084b01431a70000000015a018781bec2ef8e272d7c7814faa800038de35f46e40000000060dc5df0e8601185dd06fd88cf0ada0000f8e9fa2002e6cc4b9a9a63000000909ca080813922f187a29bd63f583b649480d7b00000000e9717120bd6758c5339156240811d886681d8161c0a900000f1b0eee000004a8000000072e864100003e5000003589abf000000003b020900d940000000000000004e5c75f000000001730c538000204e000000000002bd605040001eab13d23c90e95800018f800002f60000000000000001729000007e8d9e1b5222127644251987135085974c6e8000000000000001555128c0000d0b1d21292c0000af10fd20a1e490c4208a060afc000002787cf000000000000000101
  | 73 => 0x1e37d8e4c0404000046984c005f531c2400806a99d811aa3930f1a883a1dd06ca43158afa2a6000009698000393c80705c5800027b070940000000040c2e98000080a09a646c8caa0000000000000000d5500000ecc920000000005e84000171c166400000001971362456b4000000012ec0000b669a7800004170e76000000000000000000000000000fad199c0000000000000001774118cd4c000013ca2444a448a4336665450c498ce52ce207407948ad232603d30e6e879d12a252e0e28134c16d080d0cca07d91c203de009686bd14c08218f0d0e291868069000000003f7600000001d3a00001f942cc00b607f43514fd29cf43dd64bfc81589a60dea3a440000d4d35ea20345c400002aba6de0976000027ec7910b41803839ce0000e449b37255e62e0a9890b80c986bac48c936a1f6032240000000182c6f409df8e4e0efc51d0c7282bf3dc41610ec419251f26303cf4e000000006de4dba00001c6e7d9c5b110e40000000036e80eb248257985bc000022c00000558800035a2000000012d51750000028e00001f4a2aa08f794e13be04f4c6b60000000025f4a85871f00281e2ce08067d00004930980823522de46301bd15d02b9600000001f330e665688000000023520a403e60c41000035c0e63800000003c2c000000033a83bb8dd20db70000126c90c956037b63ce056593aa292e00000000000384c35182631a7100006e3883682930000000000011741a4c5cfc000105b2838793800013c200001eb504b1c1e0f425cac00006f6088400006e88c1a2084263c1f50000000065143370000113c00007b90000214644048379fa92e625808a6191182c6e74d8cbe009e233238849af9dd916ee01088fb057003ae7a0463a80c009de058c0f993ed15ce3418d7c0ea82ba2332cbb80f9030662220f9081372d804588212000000003bc80000c3234d266a400009f527207b6477a010032ae199c392091e0fd60e704928be441584d2060e9fc02c5e3ae450da0c000001df4970800000001eb80001ea000ee1cd0000000000006a300001dbc000000001d78314249644e4cac9d4e000031745e4865500002f8c00013ea2394513800000002226000076f1a950f84331c00000003114000049603f0000000000001dff000035407be187b0016616480f000000004b404a99751000017700000000143a44bc00019f00dce0058000084d000050ccc2595e40640000078b10ff17fa3c144bb8c7d040402ad02b20140a601ec48d603f1329e41dc760114c0000453465a842b2cfc000026613022abe1b087bc912d09d87df8dc79b9b2c2033148488a530276000071a8b462610102000000001f8000000a00ba234e87a500001ee60000524c0001e7b000000009e8023b271c41f4000000022fa0000842093e000000000000e302dd25518d8
  | 74 => 0x104e00004b9c34f2018000000008bd825b083a5a6c000045d0f4a2b40f1585163ec671902b41f6b3892214029580000ff21634bae15c600000060ef312e302b822ec64d800002e63bc0aec04002db07a080001d3b1a2e82e0541000037982288927800000004c800000ff92f5c773ceb780000000000059418253cec3a74bf811cf130869b868412de000067845770a5a175a26fca3f103131c65b9cd93141929a254208d502610a20100432095f5393e1d148a588ca20506f4499f8f4039664a580000000078a00001c218480000000015711a4168e192008600001ca24030f250fbb04f00000b96902500d25348d62168a34047fe0b7b82d017726a48cd0204b0d3e6984fab8c282d7a420c77398160e4c03384f18b48000053242071e8403ca6bf4f48209c254851701fe1dba00001424ec99c1f3c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6d8758952040054d90eb12a4081179a1c1625481022f34202c4a902045e6a1058952040018f2edb82a408002cea13705481000734b16e0a902044ab88059342040071df0eb168408113aa10162d081001c7c402eca1020038bc87591420408757100b22840800e3b21d625081001e74382c4a102043ea8405894204001972c9b8284080033a58b705081001c77c3ac599020038ec82dd932040091e902bb2640800e3721d634c81001c7643ac49902000cd563dc532040019cac5b8a640800e2f61176d041001c7c402eda082040cbb405db41040079d0e0b16820800a1f217765041001c5e426eca08202f87d86dd5410411b87cc9baa82080031b98b75504100043f43acaa08200687c8759541040078f0e0b2a82080030fdd564504100061e3aac8a082000c5f7598d41040018b8eb31a820800f361c263504100062fbaac6a082000c5c7558d41040079b0e0b1a82080031bdd56250410006363aac4a082003ce87058941040018f4cbb8282080031e597705041020e5d326e0a082000cb964dc141040019b4c7b8282080033658f705041000675316e0a082000ce962dc141040071bb06bb6620800e3720f764c4100256a40ac69882004ec43158931040018bccbb9a42080031759773484100064f326e69082000c9d64dcd210405199cc5b9a42080031799473484100062eb28e69082000c9e641cd210400193ac839a420808f3398873484100046f43cc690820088dc8798d21040011bd0eb1a42080023721d634841000667b9ac49082000ccc7358921040075770eb26800800f2ee1d64d00102071d3aac9a002040e39755934004001c76a4b2680080039ad4962d00100073542ac5a002000e698558b4004001cd4eab1680080039a5d562d001001e753a2c5a002003eaa7458b4004001d5682b1680080025ee1d52d00100071cb22a5a002000e696254b40040831f70cb8e80080033a58971d001028cddc3a83a002041abb865074004001d52c4a0e80080031e1d776440100063dc2eec8802000c7885dd9100400197709bb220080032e21376440100063da96ec8802000c7b76dd510040a13750fba220080032eddb74440100065dbb0e88802000d3b751d11004001a70ea3a220081426ee187444010284dcc30e88802050d3a651d110040a1a72ca3a220081436698c7444010286ccb18e88802050cbb621d110040a1b54c43a220081436a58874440100069da90e88802054cba611d110040a1b64c23a220080032e1d1624401000735a92c48802000e6a855891004001cd30ab1220080039add56244010007343aac48802000eab7458910040019d4e8b1220080033a1d16244010007543a2c48802000ca87458910040079d6e2b12200800fb8dc56244010004bc43aa48802000c7b765491004001a70e8a9220080039a5895244010
  | 1 => 0x501aa2c608002b66035458c100070faa4a8b182000a5e859c963040014bb0b392c608012b52057258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c100256b408e4b182000ad5811c963040075b500392c608002b66007258c1022d2ec2ca4b182000a5e8590963040014bb0b212c60800eb6a024258c100056cc0484b182000a5e8510963040014bb0a212c608013959475158c100052f42e42b182000a5d85c8563040071bf0eb1e860800f1e9c16590c1001c5fc3ac9218204aab8805924304007974e0b2486080031e5957090c100065cb22e12182008cda635c243040050f90bbb286080021fe157650c100143e42aeca1820038f8805d943040010fb0dbaa86082b70f9937550c105662f31eeaa182000c6e62dd543040010fd0eb2a86080021f21d6550c1001c5e43ac8a182000c3f755914304001878eab22860800e3721d6350c100062fbaac6a182000c5c7558d4304001972c9b8286080033658f7050c1024e5c202ec2182049ab880590430408b0fb0f3aac4081169b60a755881001c7c402eab102046a6f825d562040050fd0bba2c4080021f617745881000c7cc06e8b10200287e85dcd62040010fb0bb9ac40800e3ba1f52588102363743ea4b102046e6840d49620408dcd421a92c40800e3b21d525881001d74402a4b102046e68409d5620408dcd4213aac408002bae01755881001d74402eab102000c6f875d56204001cd700baac4081179a201755881022f34202eab102045e6a105d562040014dd0bba2c4080029b617745881001d75406e8b102005ae980dd16204089d50813a2c40800eba201745881021f54202e8b102000a6e851d162040014db0a3a2c40800ebaa03545881000574c06a8b102000e2f54951620415dd50812a2c408002bae01545881001d74402a8b10207cea84055162040014dd0bb9ac4080029b61773588100257240ae6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102004ae6811cd620400b5cb0239ac40800ebaa00735881002d74c00e6b102000e4f5394d62040075d50129ac408002ba602535881001d7540486b102000ae98090d6204095d508121ac4080029be1543588100053642a86b102000aeb8050d62040075d100a1ac408127aa10043588100273328ea2b102001a6c82dd952040018dee5bb2a40800a1fe0b765481000637c16eca90200287d82dd9520408b8d905bb2a4080029be09765481000637b92eca902045a78805d9520408d0ff04bb2a4080031be09765481022e3c402eca902046c3f729915204001c5ee5322a4081169e20164548102361fb92c8a902000e2f72591520408bc7100b22a40811b17dca635481000727b94c6a902046c5f7258d5204001c9ee4b1aa40800a9ba1d62548102363743ac4a902045
  | 2 => 0x1634811000d74412c69022000ea864d8920440073d10e90a40880133a1d9214811000754322429022004de07148520440a58f4edb2e20881472e9db64c411004e5d3b0c98822000e3b651931044001c70ca32620881532edc864c41100071da90c98822000cb8645cb10440014f10ca9620880071e9d952c41100071c322a58822000c3f749d165041634f700ba2ca0800e9e20174594100062fb9ce6b282003a7a809cd65041614f30139aca082be9ee01725941001d3c402e4b28200087e8790965040010fb0f212ca0800e9ea0242594100053cc0484b28200087e8710965040010fb0e212ca080021fa1e32594100043ec3c64b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282004a76810c965040014eb02192ca0800e9ea0032594100053cc0064b28200687e87c8565040010fb0f90aca0800387d4e539901022d1ec2ca53202000a3e858ca640400147b0b194c8080262fa1c32990100045ec38653202000a3e850ca640400147b0a194c808012ada0432990100055ac08653202003aba800ca640400157300194c8080028fa1721990100051ec2e4332020038f8805d5640400717d0faa2c8080030fdd754590100161f3aca8b2020aecb87095164040071790eaa2c8081f32e1c154590102363c386a4b2020038be87909640400147d0b212c8080028f616425901001d5d40484b202000a3e85109640400147b0a212c8082bb2e1c375590100061fbaceab202003aba809d56404001573013aac808002aee01755901001d5c402eab20207ccb8705d564040075750139ac80812b2e1c273590100051fc2ae6b202000a3c855cd640400757100b9ac8081272e1c073590100070fa9ca6b202003aba8094d64040015730129ac8081132e1c372590100051f42ce4b202000a3d859c9640400757501392c808002ae602725901001d5c402e4b202043cb8705c9640400147d0a392c8080028f61472590102371c386a4b202045a3d85949640400147d0b192c8080028f61632590100045f43864b2020008bd870c9640400147d0a192c8080028f61432590100255b40864b202000ab5810c9640400757500192c808002ae60032590100271b28ea2b202000a3e85c85640400147b0b90ac80800387d525498c1022d2ec2ca53182000a5e8590a63040014bb0b214c60800eb6a024298c100056cc04853182000a5e8510a63040014bb0a214c60800297a172198c100052ec2e4331820038de87d4d63040018beeba9ac60800b179d65358c1001c6e43aa6b1820038de878c963040014bd0b192c608002976163258c100052f42864b182000a5d850c9630400153d08192c608002a76103258c100256b40864b182003ada800c963040018beeb3aac60800297e157458c100052e42ae8b182003ad8805d163040075b
  | 3 => 0xda12200287e85dd942440010fb0bbb284880021fe1576509100143e42aeca1220008bf845d942440011bf06bb284880223720d76509100047dc02eca1220018be87d9142440010ff0abb6648800a1f21576cc9100045fc22ed99220098bc845db32440050fd0bbb264880021f617764c91004c5f426ec99220008bd84dd932440010ff0abb2648800a1f215764c9100045fc22ec99220098bc845d932440011bf06bb264880023de05764c91004e5c322e1a0a20b487e86dd5414411b878c9baa82882ce1fa1f65505102943e43ecaa0a2052c7870d95414400187eebb2282880030f1d7645051028e5c386c8a0a2000c7b65dc141440018f0cbb8282881072e19370505100143e42cec20a202c87c865d44144013878c8ba882880021fe1f651051005c3ec3eca20a2000c3e75d90414400187aebb2082881432e9c064cc5100063c32ae198a2000cb8645c331440050f90b3b462880961f219758c5100043fc3ecb18a200b87d87d96314400187ecb3a462880030f196748c5100061fb2ae918a2000c3c655d2314400117f0fb2462880022f61f648c5100061f3aec918a2000c3d75d92314401317f0e32462880022f61c648c5100061f3a8c918a2000c3d7519231440a1970e032262880032e193704c5102865c380c890a2000c5f65dcd21440018b8cbb9a428800327d9373485100064e326e690a2000c5f651cd21440018b8ca39a428800327d9073485100064e320e690a2023ccc621cd2144001998e7b1242880031e19770485100065c326e090a200287c859db40440010f90cbae80880270f19175d01100043fc3ecba02200087d87d97404400187cebb2680880030f5d764d011004e5a324e3a02200087f855d940440050f90abb280880032dd9071501100466a31ae3982200087f855d930440050f90abb260880022fe11764c11004c5e422ec98220008ef825d930440031d904bb260880021fa1b754c1105943f43eca982206387c87d95304400117d0dba260880030fd97744c1100061e32ee898220008be861d1304400187eca3a260880030f194744c1103045f43ec898220618bc87d91304400187eebb2260880030f1d7644c11030c5f438c898220098bc87191304400187eea32260880030f1d4644c1100063c32ced1022000cba761922044001c76ca32440880038e19464881102874d398c91022050e99731922044001c76a432440880038e54864881102a65d388c9102204eab88458e20440035d104b1c408814b9a083654811001c7b436e29022000c7876d952044001cd0c5b2a4088132aea1b64481100065c3b6c89022000cb8761912044001c76ca32240880038e19464481102865db90c89022050eab721912044001c76a432240880038e54864481102a65c388c89022000eab2119120440031f10eb1a4088132ae21
  | 4 => 0x34400199ee6392c6880021fa1f5258d100143e43ea4b1a2000c3f74d49634416b878e9a92c6880031bdcb5258d1000e36396a4b1a2000ce472dc56344001970e9b82c68800237e1d6318d1000566412c631a200087f855db43440050f90abb686880222f21176d0d100043fc2aed21a200287c855da43440050fd0bbb286880021f6177650d100143f42ceca1a200087d859d943440010ff0abb2868800a1f2157650d1000477c12eca1a20018ec825d943440011f700bb2868800a1f2147650d100043f436eaa1a20adc3c64dd543440010fd0fb2a86880021f21f6550d100445f43ec8a1a2000c3f75d914344001878ebb228688022a7a0f6450d100043fc2aec21a200287c855d843440091f10cb8086880031e1957010d1004e5c322e021a2000c3c75d936244001878ea326c4880029b60b75d891000536c10ebb12200087f855d362440050f90aba6c4880023ee0174d891001c7c402e9b12200087f855cf62440050f90ab9ec48800a1fa1b75589100043f43ecab12200087e87195624400187ecbba2c4880030f19774589100061fb28e8b122000c3c651d1624400117d0fb22c4880030fdd764589100061e3aec8b1220008be87191624400187eea322c4880030f1d464589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100062fb28e6b122000c5c651cd624400193ec839ac48800327190735891000666310e6b12200287e87dd5624400117f08baac4880262f21175589100046fc1aeab1220088dc835d562440011f700baac4880021fa1c755891004c5f43ee8b122000c3f75dd16244001878ebba2c4880030fd4b74589100061ea96e8b122000c3f751d16244001878ea3a2c48802237a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fa96e6b122000c5d52dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001998e7b92c488003351cf71589100063c3aee0b122000cb874dc1624409147d09bb2a4880028f61376549100043f434eca922000a6d829d952440010fb053b2a4880031b60a76549100051fc22eca922048a3c845d952440014bf06bb2a48811e9720d765491000537c12eca922000a7b805d952440010fd0c3b2a48800a1fe0876549100143ec10eca922000c7a201d952440018f2403b2a4881228fa1b64549100061f3b6c8a922000c3c76d91524400187ee5b22a4880038bdcb64549100043fc3ac8a92200087c8759152440014f700b22a4880028fa1864549100061f3b0c8a922000c3c76191524416b87ee4322a4880038bdc864549100043fc3ac6a92200087c8758d524400147f08b1aa4881228f211635491000537c12c6a922001a6c8258d52440010ff0abb6848800a1f21576d091000c5e422e
  | 5 => 0x80028fa1721d91100051ec2e43b2220008be87087644400117b0e10ec8880028fa1421d91100051ec2843b222000a9e83087644400153b0610ec888146aea0021d91100051fc2ae1b222000a3c855c3644400117d0fa86c8880022f61f50d91100045f43e41b2220008bd87c83644400147d0b906c8880028f61720d911004e1e322eb3222000c3e75d92644400187aebb24c8880021fa1f65591100043f438cab22200087d82dd5644400117f08baac8880023ee0175591100061fbaee8b222000c3c75dd164440010fd0fa92c88800a1f21f52591100063dbaee0b222000c7875dc164440018f6a5b82c8880022fe1d64191100051fc2ac83222000a3c85590644400187cedb28c8880028f60b65191100045ec3cca32220008bf87594644400187cec328c8880028f60865191100051f42cc43222000a3d85988644400147d0a310c8880028f61462191100051f436a43222000e1f5394c64440a157500298c888002ae60053191102855d404a43222000ab98094864440a157500290c888002ae60052191100051f42c643222000a3d858c864440a157501190c888002ae602321911004c5f4386432220008bd870c8644400147d0a190c8880028f61432191100055b408643222000ab5810c864440a157500190c888002ae60032191102855d406a23222000ab980d44644400157700a88c888142ae201511911004c5f438a232220008bd87144644400147d0b908c8880028f61721191102855d406423222000ab980c84644401317d0e108c8880022f61c21191100051f428423222000a3d85084644400153d06108c888002a760c21191102855d4004232220098be87d40644400117b0fa80c8880262fa1f20191100045ec3e403222000a3e85c80644400147b0b900c8880028fe1510191100051e42a203222000ad5810cb63440015b300196c6880030fd967498d100061e32ce931a2000c3f655d26344001878caba4c6880030f9d76498d100061ebaec931a2000c3e75192634400187aea324c6880021fa1f6558d1000636396cab1a200087e8719563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c3f651d16344001878ca3a2c6880022fa1f6458d100061fbaec8b1a2000c3c75d916344001958e5b22c6880022fa1c6458d100061fba8c8b1a2000c3c751916344001958e4322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880021f60b7558d100045fc22eab1a20098bc845d563440011df04baac6880063b2097558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637c2ee4b1a2000c6c85dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c96
  | 6 => 0x246e43ac69962009c3e645d740c40f9a7080bae81881462fe1d64d03100061ebaac9a0620549bb8759340c40012f70ea9681881526ee1d41d03100266a38ac6986200287e87dd563840010fb05baac7080022fe117558e1004c5e422eab1c206287e871d5638400187eebba2c7080030f1d77458e100061fba8e8b1c2000c3c751d163840010fd0fa92c70800a1f21f5258e100061fba6a4b1c20b5c3c74d4963840071bd0f192c708002a76103258e100056ac0864b1c2003ada800c963840010ff0abb4870800a1f2157690e1004d4e422c721c200087f855d943840050f90abb2870812a2fe117650e1001c6e43ac6a1c20098bc845d84384013970c8b80870800a1fa177458a100043ec2ee8b1420038fa80dd1628409147d09bb2a5080028f6137654a1000537c12eca94200087f8758d52840010f90eb1aa5080028fe116354a102451e422c6a9420018bc845db42840050fd0bbb285080021f6177650a1000c5ec26eca14200087f855db32840050f90abb665080022fe1176cca1004c5e422ed994200087f855d932840050f90abb265080022fe11764ca1004c5e422ec99420508bf8759341840811f70cb86830800f2e1c164506100061fb22ea20c2009c3c645d4418409957108b1a4108006ba20963482100051f424c5b2a2000a3d8498b65440170fb0e316ca880031b5c862d95100061eba0e9b2a2000c5d731cf65440a54f500396ca880029e60072d95100043f43c85b2a200087d8790b65440a54f501216ca880029e60242d95100043f43885b2a200087d8710b65440010fd0f196ca880021f61e32d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100053b40865b2a2000a75810cb65440a54f500196ca880029e60032d95102943f43e43b2a200087d87c8765440010fd0e10eca8802e1f61c21d95100051f42043b2a2000a3d8408765440014bd0610eca880029760c21d95102953d40043b2a203fa7681dc365440010fd0f906ca880021f61f20d95100051f42641b2a2000a3d84c83654400187aebaa6c88800b0f1d654d91100145fc3aa9b222000a3e8590b644400147b0b216c8880028fa1442d91100051ec2885b222000a3d82d97644400147b0432ec8880028fa1662d91100051ec2cc5b222000a3e8518b644400147b0a316c8880028fa1b52d91100061eba8ebb222000a3e85dcf644400147b0bb9ec88800327dce73d91100070fa9ca7b222000a3e859cb644400147b0b396c8880028fa1472d91100051ec28e5b222051aba801cb644400157300396c8880028fa1632d91100051ec2c65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000ab6810cb644400156b02196c888146aea0032d91100055cc0065b2220008be87147644400117b0e28ec88
  | 7 => 0x3c645d44148099a7080ba882900022f61f64105200061ebaec820a404cda8405c841480091f10cb80829001237a0e76cc5200256a40ac798a4000ad58318731480031f10cb8662900067a20970cc5200247c432e118a40048dc8758d31480095a902b1a62900021fe15760c5200143e42aec18a40008bf845d8314801317908bb062900023761f630c5200247c432e018a404c9b8845c0314800178b0630a4290002b92193148520006e4398e090a4009c3c645d740480f9a7080bae809010e2f61f64d01200061ebaec9a024043da8405cb40480015730830e8090002ae21941d012001d7443243a0240009bb87590404808975704b2080901336610d731012000cf4412e62024000d5b855cc4048001ab10ab98809000372e097310120006e4412e62024003cdb625cc4048007b96c4b98809000356d497310120006aca92e6202404cd9b425cc4048001b3284b98809000372c857310120006ccb9c8620240008f98718440480013730f2088090002ea60a4110120006e4b9a422024000de17148440480c78f0edbaa60900035a1cb754c120264dd43ee89824061cb876dd13048001b50e5ba260901832e1d8744c1200069dba8e89824000d38751d13048001b50e43a260901336660c744c12024e5db10e89824049dab621d13048001a76a43a260900034e548744c120006d5908e8982404cd987490d30480073b10ea1a609004ef2209434c12000cf543ee49824000da874dc930480033d105b8a609000378c87714c1200056c4326298240009e8874853048001b50e890a6090003f04c5214c1200143f43eeab26200087d82dd564c40010fd0e3aac98800b0f1d654593100245e43aa8b26200087e87d4964c40050f90fa92c9880031edd770593100063c3aee0b26200087f825d763c40050ff0fa96c7880021f61f52d8f105ae1f3a6a5b1e2000c3d74d4b63c40015ab02196c7880122fe1d6490f100447dc32e121e200087f855d943c40050f90abb287880023be097650f1000c76412eca1e200087f855d362c40050f90aba6c5880022fe117558b1004c5e422eab1620008df835d562c40111b906baac58800a1fa177358b100043ec2ee6b1620088de87dcd62c40018bd0bb9ac588003176177358b100062fa96e6b162000c5d52dcd62c40014db053b2a5880028fe117654b102451e422eca962000a5f835d952c408f4b906bb2a5880029be097654b102451f420eca962000a3d841d952c40010ff0eb22a5880021f21d6454b100043f43ec6a96200087d87d8d52c409147d09b1aa5880028f6136354b1000537c12c6a962001a6c8258d52c400167509b82a5880021fe1576d0b100143e42aeda16200087f855d942c40050f90abb2858800237e0d7650b100446e41aeca1620048bc8759142c40011bf0eb1e658800237e0d764cb100
  | 8 => 0x80ba88310003179d663106200062ebacc620c4000c5e7558c41880018baeab18831000f369c163106200066cb1ae020c4008cda635c331881038bcc6bac631019b2798e748c62032e4f31ae918c4000c5e7558e31880018baeab1c6310003279d1638c6200064eba2c718c4000cd9635c231880071b907bb2631000e3ea03764c6200043fc2aec98c400287c855d93188027998e4b1a6310012b5205634c6200043fc2aec18c400287c855d831880071bb06bb0631013a6e211700c6200466d31ae018c40008f98798740880a33770ea0e811000eb620f764c22031f2d31eea9844061e9a63dd13088001a76ea3a261100034e1d4744c2203074d318e89844049d99831d13088093b34c63a261101276658c744c2200069da90e89844000d39521d1308809db30e921a6110002b6e19434c2200056dc32629844013bc8824c530880031f301baec8900021f61e75d91200063cb84ebb22400287f875d764480018f2e0baec89011a1fe0975d912022c3ec12ebb224002c3e75953644800517f0eaa6c8900270f19175991202669c202eb3224000c3d75d9264480011bf06baac8900223720d75591200047bc0aeab2240048f4815d5644800117f0eb20c89000a1fa1f7558d200043fc16eab1a400087d82dd5634800117f08baac6900262f2117558d200047bc0aeab1a40048f4815d563480010fd0e3aac6900030fdd77458d200061e3aee8b1a4000c3f52dd1634800187aa5ba2c6900030fdd47458d200061e3a8e8b1a4000c7775dc563480018e8ebb8ac6900032ddd37158d200065a3a6e2b1a4000c7752dc563480018eaa5b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000c77521c563480018eaa438ac690003358c87158d200066a190e2b1a40008df8758c63480015a902b18c6900063e60276d0d200043fc2aed21a400287c855da43480031f10cb84869000a1fa167650d200043ec2ceca1a400087f855d943480050f90abb286900022fe117650d200047bc0aeca1a40048f4815d943480071dd0db9286900063ea1b7050d2004c5e422ec21a404ccb8405d843480031f10cb8086900272e1917010d200043fc2ae7b0a400287c855cf614800117f08b9ec2900262f21173d85200047bc3ac230a4000ad483584614800187ea4ba0c2900030f54974185200065dc02e830a4000cb8805d061480018bea4b98c2900031754973185200266a40ae630a4004cd6215cc61480019aa42b98c29000a1fa1676d05200043ec2ceda0a40048be849db41480031f3013b682901332ed0276d05200043fc2aed20a400287c855da41480091f10cb84829000a1fa1676505200043ec2ceca0a40048bc87591414800956902b22829010f2e1c1645052000c7d436e0a0a4009c
  | 9 => 0x644c53024e4e3b0c898a6000e1c65191314c0011bd0fb12629804f331cb624c53009ea6392a498a6000e5765185314c001ca8ca30a6298003a5d90614c5300074a320c298a6000ad687185314c0099ad0e30a6298002b5608614c5300066b390c298a6000cd472185314c001caea430a629800395548614c5300043fc2aed10a600287c855da214c00117f08bb442980262f21176885300266a3b26310a6000ec7624c6214c0050fd0bbb242980021f617764853004c5f426ec90a60008bd84dd9214c0111b9063b2429818f171cf654853030e4e39ec890a6060c9c73191214c0018becbb9a42980031719773485300064fb26e690a6000c9c64dcd214c0113a90e98a4298003351d931485305943e432eba026009c3c645d7404c0c70ff0fb2e80980021f61f65d01300061f3aec9a026000c3d75d93404c0010ff0abb2809800a1f21576501302545fc22eca026061c9c73d91404c00717d0faa2c8180030fdd754590300143f42ee8b10600087d85dd1620c0014df04bb2a41800e2f21d64508300043fc2ae9308600287c855d2610c0010ff0abb2821800a1f21576504300061e3aac8a086003cb870591410c0511bf06bb24218023351ce614843001c7a43ac290860038f8805d5648800717d0faa2c9100030fdd754592200070faa4a931c4000a9e84146638800153b0828cc71000a1fa1f7558e203162ec1eeab1c406287e871d563880071bd0fa9ac71000317dd75358e200162e3aca6b1c40038dc8754d63880018beea29ac71000297e0b7558e200052ec16eab1c40b6a5e859d563880018beeb3aac71018a97a1c7558e200062f438eab1c4000a5f821d563880014bb043aac71000297a167458e200052ec2ce8b1c4000a5f855d163880014b90aba2c71000eb62017458e2001d6d406a8b1c4000ad980d516388001c3ea92a2c71000297a167158e200052ec2ce2b1c4000a9e849c5638800153b0938ac71000eb6a027158e200052fc2ae2b1c4000a5c855c5638800159f04b8ac710003355c47158e200054f420a2b1c4000a9d8414563880075b50028ac710002b66005158e2001c7c402eda1c40038df8758f43880010ff0abb4871000a1f2157690e200466d31ae121c400087f855d943880050f90abb2871000e3e2017650e205662f31eeaa1c40038dc8758d43880018beeab1a8710003171d56350e200066cb1ee0a1c4049cb8405d843880119b4c6b8087100021fe1574986200143e42ae930c400287e87dd561880071f100bb683100021fe1576906200143e42aed20c400087f855d941880050f90abb2831000e3e20176506200061e3aac8a0c4003cb87059141880018beeb31a8310003171d6635062001e6c384c6a0c4000c5f7558d41880018b8eab1a831000f361c163506200066d31ee0a0c4000cd963dc1418809da70
  | 10 => 0xa926000a74815d9524c0050ff043b2a49800a1f60876549300063d100eca926000c79201d9524c09147d0db22a4980030f9db64549300061e3b6c8a926000c3f72d91524c001c5ee5b22a4980021fe1d64549300043e43ac8a926000a3e86191524c00187cec322a4980030f1d864549302470ec18c8a9260b5c3f72191524c001c5ee4322a49811697a1b73549300062f3b6e6a926000e1c64dcd524c0018bcec39aa4980038719073549302470e32486a92600095c8750d524c08b4b90ca1aa4980021fe1576d09300143e42aeda1260018bc845db424c013938c8b9e8498026a721943d09300143f42eeca12600087d85dd9424c00317d0fb228498187271cf64509300062e32ee6a12600899c8750d424c0135390ca1a8498003271d943509300447cc06ebb0a6000ad583087614c0015e30010ec2980030fd9674985300061e32ce930a6000c3f655d2614c001878caba4c2980030f9d764985300061ebaec930a6000c3e75192614c00187aea324c29800a1fa1b75585303143e436eab0a600087e87d95614c0018d8e5b2ac2980021fa1c655853000636390cab0a6000c3f65dd1614c001878cbba2c2980030fd9474585300061e328e8b0a60008be87d91614c00187eebb22c2980030f1d7645853000656396c8b0a60008be87191614c00187eea322c2980030f1d4645853000656390c8b0a6000c6f65dc9614c0018d8cbb92c2980032bd93725853000656326e4b0a60b6c5d73194614c0011ef0eb08c298002b920961185300043fc2ae830a600287c855d0614c0038dce4a90c2980031b5c952185300046ec3c6430a6000ad5810c8614c0010ff0abb6829800a1f21576d05300245e422eda0a600087f855da414c0050f90abb48298187279cf64905300062e32ae720a600287e85dd9414c0010fb0bbb2829800a1fa1676505300043ec2ceca0a600287c851d9414c013179083b282980021fa1b755053046e1e326eaa0a600087e87d95414c0010f90fb2a829818b1e1c365505300061fbaec8a0a6000c3c75d91414c095970e1b228298003271da4350530256cc38486a0a6000c7b65dc1414c0018f0cbb8282981072e19370505300143e42cec20a600087f855d8414c0050f90abb082980021f219751053004e1e322ea20a600087f87d94414c0010fb0fb2882980030f9d764105300061ebaec820a6009c9c645cc414c001c38ca326629804e3761f62cc5305b43e432eb18a600087d87d96314c09517d0d3a462980030fd96748c5300061e32ce918a60498bc865d2314c00187ecaba462980030f195748c5300045ec3ec918a6000c3e75d92314c00187aebb2462980022f61c648c5300061f3a8c918a6000c3d75192314c093970e032262980032e193704c5303162e3b6ca98a60038dc865d1314c02739904ba2629812b271db
  | 11 => 0x4c00117b0f906c8980028fa1720d91300051ec2e41b226009c3c645d6644c00187cebb24c8980030f5d764991300043f43ecab22600087e87195644c0010fb05baac8980022fe1175591300061fbaee8b226000c3c75dd1644c0010fd0fa92c89800a1f21f52591305b62eb98ca32260008bf87590644c00147f0ab20c8980028f21564191300061f3b6ca3226000a3d82d94644c00117b0f328c8980022fe1d65191300061f3b0ca3226000a3d82194644c001c3ecab98c8980038719573191300051f42cc43226000a3d85988644c00147d0a310c8980028f61462191300051f436a43226000e1c658c8644c00133b0e190c898003871943219130005cac08643226049b9a800c8644c0c1c3ca7a98c8982d7879cf52191305af0eb9ea43226049aba80948644c00157301290c898002a7e0d52191303054e41aa43226049aba80148644c00157300290c8980028fa1632191300051ec2c643226049aba808c8644c00157301190c898182a7a0e51191300054ec1ca23226000abb80544644c09357100a88c8980262fa1c51191300045ec38a23226000a3e85c84644c00147b0b908c898126aea0321191300055cc064232260098be87084644c00117b0e108c8980028fa1421191300051ec28423226060a9e83084644c00153b06108c898126aea0021191300055cc004232260098be87d40644c00117b0fa80c8980028fe1530191300051e42a6032260098be87c80644c00117b0f900c8980028fa1720191300051ec2e403226009a9e86d92434c00193cedb24869800387d946490d300070e328c921a60b687e86dd5434c15b878c9baa86982b3560c37550d305bc3f43ecaa1a606287c87d95434c0c7c3887b2a86980030fdd76450d300061e3aec8a1a604acb870d91434c15b8b8edbaa869818b171db6550d302564e3b6c8a1a6009c9c76191434c001c3eca322869800356dd47050d30256cdba0e0a1a6062c5d73d97624c001c9c65b2ec4982db175cc65d89300061e3aec9b12604ac9d73d93624c001878ea326c498127275cc64d893000536c16ebb126000a6d821d7624c0010ff0aba6c49800a1f21574d89300043fc2ae3b12600287c855c7624c0010fd0fb2ac4980021fa1c65589300061fb2ee8b126000c3c65dd1624c00187eca3a2c4980030f19474589300045f43ec8b126000c3f75d91624c001878ebb22c4980022fa1c64589300061fba8c8b126000c3c75191624c0018eecbb8ac4980031d19771589300065bb26e2b126000cb464dc5624c0018eeca38ac4980031d19471589300065bb20e2b126000cb4641c5624c0019c8c438ac4981228fa1376549300051ec26eca92600087e869d9524c0014db053b2a4980031760e765493000636c14eca926000a3f845d9524c09147908bb2a4980029be0976549300053bc0aec
  | 12 => 0xa1f215765073004e1f322ea20e60668bf8759041cc00187aeab20839805e73209744c73001cec402e898e60178dc8758931cc02f998e4b12639805f531c9524c7300143f42eec90e600087d85dd921cc0071b906bb24398023351ce614873000c7a43ac290e6008cd47358521cc0113a90e98a43980270f99175d03302545fc3ac9a066000c3d7559340cc09317f0eb26871800a1fa177458a300043ec2ee8b1460038ec87549628c0034d905bb2a5180029be097654a300153743ac4a946002a6c87589528c00317908bb685180062f6137650a3001e74382c4994600087f855d2618c0050f90aba4c3180022fe11755863004c5e422eab0c60038f8805d5618c0010ff0abb2831800a1f215765063001c7c402eca0c6003cb870591418c05199cc5b9a43180028fa1262d95300051ec24c5b2a601487d8718b654c0018dae4316ca98002c761032d9530005aac0865b2a6062b5a800cb654c00187ae83a6ca9818e97a0c74d95303152ec18e9b2a6062a7a801d3654c0c74f3003a6ca9818e97a0f72d95303152ec1ee5b2a6000c6d721cb654c0c54f500396ca9818e9e60072d95300043f43c85b2a600087d8790b654c0c54f501216ca980029e60242d95300043f43885b2a600087d8710b654c0010fb0f196ca9818a9ea0371d953031d3cc06e3b2a6000a3e849c7654c00147b0938eca9818e97a0c71d95303152ec18e3b2a600087e87c87654c0010fb0f90eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca9818e97a0c21d95300052ec1843b2a6062a7a80087654c0014f30010eca9818e1fa1f20d95300043ec3e41b2a6000a3e84c83654c00147b09906ca980030f5d754d91300055cc06a9b226002c3c75953644c00517f0eaa6c8980028fa1642d91300051ec2c85b226000a3e8510b644c00147b0a216c8980028f60b65d91300051ec10cbb226000a3e8598b644c00147b0b316c8980028fa1462d91300051ec28c5b226000a3e86d4b644c00133d0e196c898002e560432d9130255cd40065b226000c3d751d7644c095575003aec898186ae60075d913030f0f29ea7b22604aa9d83dcb644c00147d0b396c8980028f61672d91300051f428e5b226000a3d851cb644c09557500396c898186ae60072d91300051f42c65b226000a3d858cb644c00147d0bb8ec8980028f61771d913030d5cc06e3b226000a3e859c7644c00147b0b38ec89812aa760c71d91300045f438a3b2260008bd87147644c00147d0b90ec8980028f61721d91300045f43843b2260008bd87087644c00147d0a10ec8980028f61421d913030d4f41843b226000a9d83087644c0955750010ec898002ae60021d91300051fc2ae1b226000a3c855c3644c0c317d0fa86c8980022f61f50d91302571d286a1b2260618be87c8364
  | 13 => 0x62fb94c6a908000e4f7298d52100010ff0eb1aa4200021f21d63548402470e21ac6a908000c5f8758d52100018b90eb1aa42011b17dc9635484000727b92c6a908048e1f4258d521008bcb440b1aa4200038758e43548400153743ac4a908002a6c8758952100c11790eb1a8420183271cd63508400064e43ac6a108000e1f8558d4210001c390ab1a8420027a3dc963508400070fa92c6a108000e1d5258d4210087d3440b1a84200024f61471508400055dc32e0a10804ebab825c142100010ff0abb6642000a1f21576cc8403064fba2c79908009c9c7458f32100010ff0abb2642000a1f215764c84001c6e43ac69908000c9f7458d3210013938e8b1a642000237e0d72984400446e41ae5308800287e87dd5611011b878e9baac22014b1e1c375584400043ec16eab0880098bc845d56110167878e83aac2202d31e1c075584400043f43ea4b08800287c87d4961100010fd0ea92c2200021f21d52584400163a3aca2b08808de365494561100071e90ea8ac2200038d55151584400061fc2aed2088000c3c855da411000187ea4bb482201532ee01769044028e5c402ed2088000c3d7654a41100a357100b0c82200232798d74cc4400466d31ae198880048bd845da31101038bcc6bac62201972798d748c4400062f3aac71888000c5d7558e311001393ce8b1c6220003275d1638c44001c6e41eec988800087f855d931100050f90abb262200023be09764c44000c76412ec9888000c9f7458d3110013938e8b1a622000f361c1634c4400066cb1ee0988800087f855d831100050f90abb0622000e3760d760c4400043fc2aed108800287c855da211000117b0dba442200021fe1576484400143e42aec90880008df835d921100111b906bb242200023761b73484400046ec30e690880008de8798d21100111b90f31a422000237a1d63484400046e43ac690880038f48758521100050fd0fbaac9980021f60b75593305643f438eab266002c3c7595164cc0111790eaa2c9980021fa1f52593300143e43ea4b2660008bf845d562cc01317908baac59800e3720d7558b300143f42ee2b16600087d85dc562cc00147f08bb2a5981228f2117654b3022d2e41aeca966000a6f825d952cc0010ff0eb22a5980021f21d6454b30004ae43a86a96600087f855db42cc0050f90abb685980021fe157650b300143e42aeca1660038dc835d942cc0031790eb228598023271cd6450b30044ce43a86a16600087f825d661cc00197700ba4c3980032e20174987300143fc3ea530e600087d87d4a61cc16b87ce9a94c3980030f5d352987300043fc3aa530e600087d8754a61cc09187ce8a94c3980030f5d152987300043fc2aeda0e600287c855db41cc00917908bb68398023279cd64907300245ec26eca0e60038de83dd941cc0010ff0abb28398
  | 14 => 0xc855d831500010ff0abb442a000a1f215768854001cdc402e910a80088de839d921500011bb073b242a000a1fa1476485400043ec28ec90a8045a5d8594a631001353d0828cc620002a76105198c400052f42e433188000a5d85c8663100111bd0e10cc6200023761c2198c400052f428433188000a5d85086631001353d0810cc620002a76102198c4001d6d400433188000ad98008663100050fd0fbaac6202b70f1d37558c4056f0e21eeab188062c5d83dd563100010fb05baac6200262f2117558c405be1e3a0eab1880b7e1c431d563100071bd0fa9ac62000317dd75358c4004d4f426a6b188002c5c7594d63100071b90ea9ac620026a72115358c400062fba8a6b18800087e87d4963100050f90fa92c6202d78710f5258c400052f42c64b188000a5d858c9631001353d09192c62000eb6a023258c400052f42864b188000a5d850c9631001353d08192c620002b5a043258c400056ac0864b188003ada800c9631015bc38e9baac6200029760b7558c4056f0fa16eab188062e5a20dd5631016d4bd0b3aac62000317dd67558c4004d4f424eab188000a9d849d5631000153f08baac620026a72117558c403152f438eab188000c5e871d5631016fc38e83aac620002976087558c405bf0fa10eab1880b6e5a201d5631001353909b92c62000297a167258c400052ec2ce4b188009a9e849c9631000153b09392c62000eb6a027258c400056cc04e4b188000a5f855c963100014b90ab92c620026a72117258c400052f428e4b188000a5d851c9631001353d08392c620002a76107258c400056b408e4b188000ad5811c963100075b500392c620002b66007258c400052f43ea4b188000a5c87d49631016bc3e85a92c62011b968835258c4004d4f424a4b188000a9d8494963100075b501292c620002b66025258c4004d4f420a4b188000a9d8414963100075b500292c620002b66005258c400052f42ce2b188000a5d859c5631001353d0938ac62000297e157158c400052e42ae2b188009a9c845c5631000159f04b8ac620002b32097158c4001d6c402e2b188000a9f84545631001353908a8ac620002b6e015158c4001d6c402a2b188009a9e84145631000153b0828ac62000297a172158c400052ec2e42b188009a9e84c85631000153b0990ac62000eb6a032158c400056cc0642b1880008de8708563100011bb0e10ac62000297a142158c400052ec2842b188009a9e84085631000153b0810ac62000eb6a002158c400056cc0042b188000e1f8558e4310001c390ab1c862000387d496390c402574d102c72188000c9d635ca431000127b0b38c862000e3b21d52588402451f426eca908048c3e74dd952100034d905bb2a4200029be0976548400051fc32e8a908048c3c765d1521000163906ba2a4202e2cbe09745484023
  | 15 => 0x838acb200021fa1f21596400043ec3e42b2c800087e8708565900010fb0e10acb201ea8fa1021596400051ec2042b2c8000a5e8308565900014bb0610acb2000e9ea0021596400053cc0042b2c8000a9d840c963900015ab02192c72000eb6a003258e4001e3d382cb21c8000c79655c2439000117b0d38c87200024f6167190e400043ec36eaa1c80b987c87595439008b4db053aac52011a9be097558a400143f42ee6b14800087d85dcd62900050fd0bb8ac5200021f6177158a400061ec26eca94800287f82dd952900050fb05bb2a5200030fd0b7654a400061ea16eca948045c3f40dd9529008b87a81bb2a5200029be097654a4000637c12eca948000c3f769d152900e965b053a2a5200030fdd97454a400058e41ae8a948075b2f825d1529000187eed21aa5200030fdd84354a4030c5fc3ac7a148061c9e7358f4290087d5080b1285201323e61b7050a4030e4e39ac6a1480008bd861c5429000127b0a38a85200030f997744ca400046fc1ae530c80088dc835ca6190005878eb2a2c32000a1fa1773586400043ec2ee6b0c80418fb865c2419000147f0ca948320152aee1970906400043ec36eaa0c800087c8759541900078f0e0b2a832000f3c1c261506400063d32ee0a0c8000c7965dc141900e327f0cba883200024f61975106400049fc12ea20c8009c3e605d44190013a74c0ba883200024f61d52106400051fc32a420c8000c3d75584419000187ccaba663200232798d74cc6400143f42aed18c800087f865d631900010ff0eb2c63200021f61d658c6403d61f3a2cb18c8000c3e655d2319000187acaba4632000f1e9c1650c6400063cb2ae018c80099b8845c031900011bf06bb243200223720d76486400061f32ee890c8000c5e65dcd21900018bacbb9a43200031799473486400062eb28e690c8023cce621cd2190001998e6b12432000237e1d6318d400043fc2ae7b12800287c855cf62500010ff0ab8ec4a000a1f21571d89400051ec26eca928000a6d829d952500014bf06bb2a4a011e9720d765494000537c12eca928000a77815d952500014e902bb2a4a01168fa1b74549400061f3b6e8a928000a3e861d1525000187aec3a2a4a00021fe1576cc9400143e42aed992800087f855cf61500050f90ab9ec2a00023de1d61185400043fc12ea30a8004c3f415d4615000987a82ba8c2a00030f90175185400061e202ea30a800287f87d4861500010fb0fa90c2a00021fe1d52185400043ec3aa430a8000c3e859db415000187b0b3b682a00030fd4a76d05400061f3b2a5a0a8000cf061dc14150089970e1b1282a00024f21d525054022e9c382a4a0a8040eb36018541500073750fb8282a01472edd870505400069dba8e0a0a8000d38751c14150009179093b462a000e6e201748c5400043fc2aec18a800287
  | 16 => 0x3597400062fb9ce6b2e80b5c3f41dc965d000187c81b92cba02d70f10372597403e53d404e4b2e8000a79809c965d017d47f08b92cba00268f21172597400052fc1ae4b2e8000a5c835c965d00010fd0f192cba00021f61e32597400043f43864b2e800087d870c965d001347d08192cba00028f61032597400053b40864b2e8000a75810c965d00f94f500192cba00029e600325974004d1f424e2b2e80bda3d849c565d00014bd0738acba00029760e71597400053dc02e2b2e807ca78805c565d001347d0838acba00828f61071597400043f43e42b2e800087d87c8565d00010fd0e10acba00021f61c215974004d1f42042b2e8000a3d8408565d00014bd0610acba00029760c21597403e53d40042b2e8000a798008565d017947f08b82cba00021fa1f20597400043ec3e40b2e8009a3e84c8165d000147b09902cba01221f61e7558b4024536c14eab1680038bc845d562d00011bf06baac5a00223720d7558b405ad37c12eab16800287e85dcd62d00010fb0bb9ac5a000a1fa177158b400043ec2ee2b16800287f82dd952d00050fb05bb2a5a00031e8837654b400063c906eca968045a3c845d952d0091878e8bb2a5a000297e0d7654b4023d2e41aeca968000a6f825d952d009187908bb2a5a000317e0d7654b400062e41aeca9680b587f825d952d00018df04bb2a5a01230fd057654b400061f202eca968048c3c405d952d000187aedba2a5a000a1fa1773587400043ec2ee6b0e8000c3c75dd941d000187eedbaa83a00028fa1d65507403dd1e43acaa0e8000a3f8259541d001387ee2b2a83a00278ddc565507403e61f382caa0e807cc3c7059541d00f9870e0b2a83a010f2e1c162507400049e43aa4a0e8000a3d8654941d008ba70e0a9283a00032eddb70507400071cb2ee0a0e8000d3b751c141d0001a70ea38283a00038e59470507400063d32ae198e800287e855da31d00010ff0cbac63a00021fe1d658c7400043ec3acb18e8009c3e7459631d000187ccaba463a00030f595748c74004e1f3a2ca18e80608bf865d031d000187acaba063a00270f9d165887400061eb2ae910e80039b8805d221d00011bf06bb243a00223720d76487400062f32ee690e8000c5d65dcd21d00018bcca39a43a00031759473487400063d32ee090e80bba7b805d165900018bee739acb2000e9ea0273596405d53cc04e6b2c8000a3f845cd65900f547908b9acb201ea8fa1272596400051ec24e4b2c800087e8790965900074f501212cb200029e60242596400043f43c64b2c800087d878c965900010fd0e192cb200021f61c32596403d51f42064b2c8000a3d840c965900014ed02192cb200029d604325964001d3d40064b2c8000a79800c965900018eee338acb200028fe1171596403d51e422e2b2c807aa3e841c5659000147b0
  | 17 => 0x1a4200a5f8559363484014b90ab26c690802b6e0164d8d210056c402c9b1a4200a5e8519363484014bb0a326c6908029761e75d8d210052fc14ebb1a4200a5d829d763484018bf0ebaec69080297e0975d8d210052ec12ebb1a4200a5e851d763484018baea3aec69080297a1774d8d210052ec2ee9b1a4200a5e851d363484014bb0a3a6c69080387d5254d8d210072ba8ca3b1a4200a9e84147634840153b0828ec69080297a1770d8d210052ec2ee1b1a4200a9e84dc3634840153b09b86c69080297a1470d8d210052ec28e1b1a4200acd821c3634840153d09a86c690802a761350d8d210045fc22eab1a42098bc845d563484011bf06baac6908023ee017558d2101c7c402eab1a42008df8758c63484014bd0b3b0c690802976167618d210046ec3cca31a42008df87594634840153f08b28c690802a72116518d210056dc02ca31a4200ad88059463484011bb0f320c69080237e1d6418d210052fc2ac831a4200a5c8559063484015b700b20c690802b62016418d210052f428c831a4200a5d851906348401c3ea92a0c69088eb3a0b5118d2100566c16a231a4200a9e84144634840153b08288c690802a7a135018d210054ec26a031a4223ace82140634840159b04280c69080a1fa167690d210043ec2ced21a42088dc835da43484119a8c738c86908063d2197190d210143f42ceca1a420087d859d943484010ff0abb2869080a1f2157650d210046fc1aeca1a42008ef825d943484011f700bb2869080e3e2017650d215662e31eeaa1a42098de87d8d43484018beebb1a8690803171d76350d210446e41aec21a42048ec865c843484119a8c738886908063d2197110d210061e3aec8a0a4200c5f75d8d41484018b8ebb1a829080317dd463505210062e3a8c6a0a4223ccc7218d4148401998c7b92829080336d8f70505210066c31ee0a0a4200cbb641c14148481970c8382829080336d8c70505210066c318e0a0a4200c5e75d8c41484018baebb188290803179d463105210062eba8c620a4200c5f635d631485038b8c6bac629080327d8e748c5213364e31ce918a4200c9f635d231484cb938c6ba46290822b520e768c52140f2a31aeb18a4266e94639d231484cbd28c6ba462908a3331cb634c5210466a3b6e698a4228dc472dcd31484519a8edb1a6290823351d8634c5210456a4326218a420087f855d360484050f90aba6c090802aea1350d81210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d60485819aee231ac090803179d763181210062ebaec63024200c5e7518c60484018baea318c0908023ee1d60181210053c42ac03024200ab884580604841347d0939acba02fe8f6127
  | 18 => 0xc4034d905bb2a4188028fe1176548312451e422eca906247a5c835d9520c4014df04bb2a4188021fe1d64548310043e43ac8a906202a6e87589520c4054d90eb12a41888f93e0d625483111f2641ac4a906200e4f73589520c48fc98e6b12a41891f93cc5625483123f3318ac4a906247e6531589520c4010ff0abb6841880a1f21576d08310043fc2aeca10620287c855d9420c4091790eb228418823271cd64508310043fc2aeda08620287c855db410c4a9976c838282189532e19070504310062fa96ec98862238dc87589310c447998e4b126218813b1885624c4310062fbb2a49886223d4c72549310c401c9ac4a92621880a1fa1f75580310043ec16eab0062008bf845d5600c41317908baac0188030fdd774580310061e3aee8b006200c3f751d1600c401878ea3a2c0188021fa1f52580310143e43ea4b006200c3f74d49600c56b878e9a92c0188021fa1d52580310043e43aa4b006200c3f74549600c491878e8a92c01880b1e1d650580310247c43aa0b00620087f855c364884050f90ab86c9109532e19070592210143f43eeab2442008fb805d564884071f100baac9108021fa1c75592210161e3aca8b2442aecb87095164884091790eaa2c9109f32e1c154592210063dbaee0b244200c7875dc164884018f6a5b82c9108031e54b70592210063dba8e0b244200c78751c164884a9976e8382c9108030fd4974d8e210061ea92e9b1c42048bf87592438849557100b2487108021fe157650e210143e42aeca1c42008fb805d943884071f100bb28710926ae2016410e212a65db20e0a0c4254cb8641c141884a9970c03a2c11080a1fa1f75582210045fc22eab0442098bc845d5608840187eebba2c1108030f1d774582210061fa96e8b044200c3d52dd1608840187eea3a2c1108030f1d474582212a65db80e8b044200c3d75d5364484010ff0ab86c89080a1f21570d91210143f43eeab22420087f82dd564484010fb05baac8908022fe1175591210046fc1aeab2242088dc835d564484011f700baac89080e3e20175591210043f438eab224200c3c75dd164484018beebb9ac890803171d773591210062fa96e6b224200c5d52dcd64484018beea39ac890803171d473591210066639ee4b224200c7b75dc164484018f0ebb82c89080336dcf70591210066c39ee0b224200c7b52dc164484018f2a5b82c8908031edd470591210063c3a8e0b224200cbb741c164484019b6e6382c890803361cc70591210045fc3ac83224200a3c85590644840157100b20c8908021f61e75d8d210143fc3aebb1a4200c5f835d763484010ff04baec6908021f60975d8d210062ebaea7b1a4202c5e7594f63484051bf0ea9ec690803175d453d8d21005a6c14ebb1a4200a9f84597634840153908b2ec690802b6e0165d8d210056c402cbb
  | 19 => 0x31d4877654a312451f424eca946200a3d849d9528c4014db053b2a5188029be097654a310062fc1aeca946200c6f825d9528c4010fd0e3b2a5189228fa107654a310051ec20eca94620087e87d91528c4010fb0fb22a5188028f61a6454a310061fbb4c8a946200c3d76991528c56b87ee5322a5188038bdca6454a312451fc32c8a946200c3f76591528c40187aecb22a5188030fdc96454a3100717b92c8a946200c5d76dcd528c401c3cc9b9aa518803175d87354a310070f320e6a946209c9e645cf428c4091790eb228518997271cd6450a310062f32ee6a14622f87d86dd5418c51b87cc9baa83188961f21d65506310061fbaac8a0c6200c3c75591418c4018f4cbb8283188031e597705063120e5d326e0a0c6200cb964dc1418c4018f4ca38283188031e59470506312065d320e0a0c6200cb9641c1418c4511bf0eb1663188a3339c962cc6310143f42ee8b04620087d85dd1608c4015ab02192c1188123760f75d91310043fc2ae1b22620287c855c3644c4010fb05baac8988023be09755913100c76412eab2262008fb805d5644c4071f100baac8988031bdd77259131006363aee4b226200c6f85dc9644c4018d90bb92c8988031bdd47259131006363a8e4b226200ccf731c9644c4010fd0fa92c89880a1f21f525913100637b96a4b226201c6c72d49644c48d8f0e1a92c8988031edd770591310063c3aee0b226200ceb72dc1644c4019d0e5b82c8988031ed4b70591310063dba8e0b226200c78751c1644c401976e8382c8988033adc8705913100674390e0b2262008bf87590644c40157100b20c8989962f61f64d0d310043fc2ae9b12620287c855d3624c4011f700ba6c49880e3e20174d893101477c3aa5b12620087f855c3624c4050f90ab86c4988022fe1170d893104c5e422e1b126200a6d829d9524c40147f08bb2a4989228f21176549310052fc1aeca926200a6f825d9524c4014f700bb2a4989169e20176549310043fc3ac8a92620087c87591524c4014df04b22a4988069b20964549310053dc02c8a926245a7880591524c4034dd0db12a49880a9ba1f62549310153643ec4a9262018be849db424c4010ff0abb6849880a1f21576d093100d56412c9a126244ab880593424c4031790eb228498806ab209645093121d5c402c8a1262049d4815c3324c4010ff0abb2829880a1f215765053100c76412eca0a6200cbb641c1414c481970c8382829882237219728c53114666312e518a6204dc6215ca314c451c98c4a9462988021fe1574d81310143e42ae9b0262008fb87580604c40157108b00c09880a1fa1f75590310043ec16eab2062ac87e871d5640c405878eb2a2c8188122f21d54590310043f43ea4b20620287c87d49640c40117f08baac4188262f21175588310446e41aeab1062048ec87549620
  | 20 => 0xaac0864b2c6200c3f749d1658c5834ef02b9acb188031bdca72596310253b40ce4b2c627da75819c9658c4014bf06b92cb18a069720d72596310043f43c84b2c620087d87909658c4014f501212cb188029e60242596310043f43884b2c620087d87109658c4010fd0f192cb188961fa1f21596310043ec3e42b2c6200a3e84dc1658c40147b09b82cb188031edc270596310043f43e40b2c620087d87c81658c40147d09902cb188028f61320596310043f43840b2c620087d87081658c4010ff04baec91880a1fe1f52d92310043ec3ea5b246200a3d82996648c409c3e6332cc918813874c665992310051fc12cb3246200a3e8598a648c40147b0b314c918812ada0662992310051ec36a53246200e1e658ca648c40153b0c194c918803879943299231005cac08653246266e1e53d4e648c40153f06a94c91899aa720d52992310051f42c653246200a3d858ca648c40147d0b90cc9188028f617219923104c5f43ea132462008bd87d42648c41317d0f904c9188022f61f20992310051f42e413246200a3d85c82648c40147d0a104c9188028f61420992310245f43ea8b246200c3f75d51648c40587ceb2a2c9188122f21d54592310051f42c84b246200a3d85909648c40157501212c918802ae60242592310051f42884b246200a3d85109648c4050fd0bb82c9188021f61770592310051ec14cab246200a3f82595648c40147d0b312c9188028f61662592310255b40cc4b246200a3d86d49648c40153b0c192c918802e560432592310061fbaceab246200aba809d5648c401573013aac9188028fe1573592310051e42ae6b246200aaf825cd648c40155904b9ac918802aee0173592310055c402e6b246265e1e53d4d648c40147d0b392c9188028f61672592310255b40ce4b246200ab5819c9648c40157501392c918802ae60272592310054fc1ae4b246200a3e851c9648c40147b0a392c9188028fa1632592310051ec2c64b246204e3651d45648c40147d0b90ac9188028f61721592310051f42ee0b246200a3d85dc1648c40147d0b382c9188028f61670592310054ec18e0b246200cb9701c1648c40117d0fa82c9188022f61f50592310045f43e40b2462008bd87c81648c40147d0b902c9188028f61720592310051f42840b246200a3d85081648c40956d02102c918802ad604205923104e5b322e3a1c620087d86dd5438c55b87cc9baa8718ab61fa1d6550e315bc3e43acaa1c6200c3f75591438c401878eab2287188032d5937150e310062fb9ccab146200e4e32595628c40187ceb322c5188030f9d56458a3100536c14eab146200a6f825d5628c4050fd0bba2c5188021f6177458a310143f42ee0b14620087d85dc1628c41317d09b82c5188022f6137058a310143fc16eca94620287d82dd9528c4018ec43bb2a5188
  | 21 => 0x529046050401c72a5208c0a08029ee1541181410053c42a823028200a7a85c8460504014f30b908c0a0902aea1321181410055cc264230282038fa8708460504014f50a108c0a08029e61421181412055d420423028200ab98408460504015b506108c0a0802b660c211814104d1f424e6b2882c3a3d849cd65104018bee739aca20ad70fd0772594415ae1e206e4b2882c2a3f845c9651041347908b92ca2080297e0d72594410052e41ae4b28820087e878c965104010fb0f192ca208021fa1c32594410043ec3864b288209a3e840c9651040147b08192ca208129da0432594410053ac0864b288200a7a800c965104014f300192ca208b21fa1f21594410043ec3e42b288209a3e84dc1651045947b09b82ca209c28fe11705944104d1e422e0b28820087e87c8165104010fb0f902ca208268fa1320594410051ec2640b28820087e8708165104010fb0e102ca209221f61e755884124536c14eab1082098bc845d562104011bf06baac4208223720d75588415ad37c12eab10820287e85dcd62104010fb0bb9ac42080a1fa1770588410043ec2ee0b1082018bd84dc162104050ff05bb2a42080a1f60b76548412451e422eca908248c3c745d952104014bf06bb2a42091e9720d765484100537c12eca908248c3c845d952104018bf06bb2a4208031720d76548415ac3fc12eca908200c6f825d9521049187e82bb2a4209230f10176548410051ec36e8a908200c3d76dd152104091b90eb1a64208030f1d776504410061fc2eeca088200c3c85dd9411040187ea5bb282208132d94776504410065aa8eeca088200c3f76dd5411040147d0eb2a8220a0a8f21d65504410051fc12caa088204c3f715954110413c6ee2b2a82208030f1c165504410049e43aa4a088200a3d86549411040187eeca9282209426ea1f70504410065dbb6e0a088200e3965dc14110401976ec38282208034edd470504410069c3a8e0a088200e39651c141104a19750c38282209432e61870504412a65db28e0a088254d3a651c14110401972ca38282209534e59470504410061cb28e0a088250d9a831c141104a1b330638282208032e98c70504410065cb10e0a088200d3b521c14110401a72a438282209536c98470504412845e43a82b008250ab88050560104091b906baac9988222fa1f54593310061fbaea8b26620287e85dc164cc4010fb0bb82c99880a1fa177458b310043ec2ee8b1662038fa80dd162cc4011f301ba2c59880a1fa177058b310043ec2ee0b1662098be84dc162cc40117b09b82c5988029be097654b3100c5e43ac8a166200c3c7559141cc481974c838283988032e59070507310143f42ee8b06620087d85dd160cc40157509a82c1988961fa1e625963100637b94c4b2c6204a7681989658c409ccc43312cb18802976183259631005
  | 22 => 0xa10c0a08038ed9742181410071c32e843028200e3b655086050401c70caa10c0a0803aad8942181410071db2c823028200e38659046050481c74a9aa0c0a0abaaee1e54181415755cc3ca830282aee3a75950605055dc72eb2a0c0a0802aea0e54181415774d39ca830282aee99739506050401573052a0c0a0952aea0654181412071c2a2a8302827cabb875506050481c770aaa0c0a09f38edd554181413e71c3aaa83028200ab88355060504f9d34e6aa0c0a09f3a65cd54181410055dc12a83028254ab881550605048157509a98c0a0802ae61353181410071d2a4a63028200e5b5394c605040157708a98c0a0902ae21153181412055d420a63028200ab98414c6050401c74a8298c0a092aae61e43181410055dc2c863028200ab98590c6050495d34e7218c0a092ba65ce43181410055cc14863028254aba8190c60504014f70aa18c0a08029e215431814124d5dc38863028249ab98710c60504815770a218c0a0802ae61443181412074d418863028249e9a7310c6050493d32e6218c0a0802ae60843181412a55d408863028240aba84d48605040157309a90c0a08038e95352181410071caa6a43028200e3a84d486050401c7309a90c0a091b8e9d352181412372d39ea43028246e5973d486050401c7487a90c0a08038e10f52181412055d424a43028200ab9849486050401c74a8a90c0a08038e55152181410071d422a43028200e3984548605048bcb4e6a90c0a0917965cd52181410071d21aa43028200e38435486050401cd704a90c0a09179a9c9521814122f34b92a43028240aba84148605040157308290c0a0912aee1f42181412255cc3e843028240abb85d0860504015730ba10c0a0802aea0f42181412274d39e843028244e9973d086050489d54e5a10c0a0913aa5cb42181410071da96843028200e3952d0860504a957503a10c0a08023e61e42181410053d42c843028200a798590860504875770ea10c0a0802aee1542181410055cc2a843028200ab8835086050487d34e6a10c0a090fa65cd421814120755c12843028200e3b525086050401c72a4a10c0a0952ae20542181410055dc26643028240ab884cc860504014f50b190c0a08029e61632181412055d424643028200ab9848c8605040157708990c0a0902ae211321814101c7d4386430282008f9870c860504014f50a190c0a08029e61432181412055d420643028200ab9840c860504015e502190c0a0802bc60432181412055d426a23028200ab984d446050401c72a9a88c0a08038e952511814100739a8ca23028200abb84544605048157108a88c0a08038e55151181412055d420a23028200ab9841446050401c74a8288c0a0952aee1641181410055cc2c823028200aba8390460504a3d34e7208c0a0947a65ce41181410055cc14823028200e3b
  | 23 => 0x905410046fc1ae5b0282088dc835cb605040157309a86c0a080a3ee1d50d81410053d42e41b028200a7985c8360504014f50a106c0a08029e61420d81410053cc16cbb028200e398419760504014f30432ec0a08038e19654d81410053d42cc7b028200a798598f60504014f70ab1ec0a08029e21563d814100575c12c7b028200ae88258f60504014f50b316c0a08029e61662d81410053dc2ac5b028200a788558b60504015b706b16c0a0802b620d62d81410053d428c5b028200a798518b60504014f50da96c0a08029e21b52d81410053d432a5b028200a788654b6050483575083aec0a0802ae61075d814120f1d2a6a9b028200a7a85dcf60504014f30bb9ec0a0802ae61373d81410072da9ca7b028200a7b8550f60504014f10aa1ec0a0907a610d43d81410053d42ce5b028200a79859cb60504015b706b96c0a0802b620d72d81410053d428e5b028200a79851cb605048357508396c0a0802ae61072d814100735c12a5b0282008f98790b60504014f50b216c0a08029e61642d81410053d42c65b028200a79858cb60504011f50e196c0a08023e61c32d81410053d42865b028200a79850cb605048357508196c0a0802ae61032d81410057940865b028200af1810cb60504835750828ec0a0802ae61051d81410053d42e43b028200a7985c8760504011f50e10ec0a08029ea1421d81410053cc2843b028241aba8408760504015730810ec0a0802b6a0c21d81410056cc1843b028203c78605d660504018f4ebb04c0a08031e5d760981410143f436eab02828d87c86dd560504010fd0fb2ac0a08021fa1c65581410062fb2ce63028200c5c659cc60504079b0c1398c0a080317d9573181410062e32ae63028203cd8605cc60504011f70eb00c0a08029ee1560181410053c42ac03028200c7a76d946050401c7709b28c0a08029e60b65181410047cc3cca30282008fb8759460504018f4ec328c0a08038e61065181410053cc10ca3028200e3b655d06050401c70caba0c0a0802aea1a54181410071db2ca83028200e38659506050401c76caaa0c0a08038e19554181410066d3b4e63028200e5b659cc6050401cb0cb398c0a0803369d973181410072db2ae63028200e58655cc60504011f30f318c0a08029ea1663181410053cc2cc630282008fb8758c60504014f70ab18c0a08029e215631814100575c12c63028200ae88258c6050401c76cb218c0a08038e19643181410074c31c863028200aba8610c6050401c76ca218c0a08038e19443181410047cc3cc43028200a7a8598860504014f30b310c0a08023ee1d62181410053dc2ac43028200a788558860504015b706b10c0a0802b620d62181410053d428c43028200a798518860504014f50da90c0a08029e21b52181410053d432a43028200a788654860504015750d
  | 24 => 0xa8200a5e83dd365504014bb07ba6caa0a0a9da0774d954146d1f426e7b2a8200a3d84dcf65504018bae639ecaa0a368fa1072d95410051ec20e5b2a820087d8790b65504014f501216caa08029e60242d95410043f43c65b2a820087d878cb65504010fd0e196caa08021f61c32d954146d1f42065b2a8200a3d840cb65504014ed02196caa08029d60432d95410053d40065b2a8200a79800cb655051b0fd0f90ecaa08021f61f21d95410043f43843b2a822f87d87087655051b47d0810ecaa080297a0c21d95410052ec1843b2a8200a7a8008765504014f30010ecaa08028fe1170d954146d1e422e1b2a828da3e841c3655040147b08386caa080297a0c70d95410052ec18e1b2a820087e87c8365504010fb0f906caa0a368fa1320d95410051ec2641b2a820087e8708365504010fb0e106caa0802a761032d8d410056ac0865b1a8200c7b659c263504018f0cb384c6a08031ed957098d410063c32ae131a820087e87d9563504018d8e5b2ac6a08021fa1c6558d4100636390cab1a8200c6f65dc963504018d8cbb92c6a08031ed977058d410063c32ee0b1a8200c7b651c163504018f0ca382c6a080237e1d6318d4100566412c631a8200e1f65d8e43504011790cb8486a08024fe157090d412565c302e121a820087e86dd543505730fd0fb2a86a0a378710f6550d410061e32cec21a82498bc865c04350493970c0b8086a08029b60b75d894100536c10ebb12820087f855cf62504050f90ab9ec4a08021fe1570d89410143e42ae1b1282018bc845c362504010fd0fb2ac4a08021fa1c65589410062fb2ee6b128200c5c65dcd62504018beca39ac4a080317194735894100666310e6b128200c7b65dc162504018f0cbb82c4a08031ed9470589410063c328e0b128245a7a80dd952504014f301bb2a4a08021fa1a765494100536c14eca928200c6d829d9525040147f08bb2a4a080297e0d765494123d2e41aeca928200a6f825d952504014f700bb2a4a09169e20176549410061ec20eca92820287f821d952504050fb043b2a4a08030fd0876549410061ea10eca928200a3e869d15250401878ed3a2a4a0a1acb60a74549410051e432e8a928200c3c765d1525040163906ba2a4a0a22cbe0974549410061e3b486a928200c3c7610d5250401878cb3b684a09962f61f63d094132e4f39ec7a1282448bc865c34250489970c0b8684a08030f1db655094100716316caa128265c9c73d8d425040117d0db8284a08024f617705094121e5c306e0a1282048bd849db32504010ff0abb664a080a1f21576cc9410047dc02ed99282038f8805db32504050fd0bbb264a08021f617764c94101c7d406ec99282008f980dd93250401878cbba264a0a378dd8765905410051e432a520a82098bc865c2415040127f0ab8482a09472e18170
  | 25 => 0x80127f08b98c0a91224f21173181520062eb98c6302a400a798018c605480127f08b88c0a91224f21171181520043ec3cc2302a400a3d8418460548012f70eb00c0a931edae0960181520143f43eeab1e84ad87e871d563d0801878ebbb287a10021fe1570987420143e42ae130e840287e87dd561d080317908baac1a1003175d753d8d420046fc3ac631a8400a5c8558c63508018b8ebb1a86a12b30f1db7550d425670e31eeaa1a8400d2c72dd5435081153d0db1a86a10021fe1573d85420143e42ae7b0a84008f787584615080987e82ba8c2a10130f505751854200c5ec26ebb028400c3d749d760508050ff0ebaec0a10030f5d175d81420061f202ebb028400c3c405d760508011f70eb00c0a100a1fa1f75593325643f438eab266400c3f525d261cc80187aa4ba4c39900a1fa1f75583320045fc22eab0664098bc845d560cc80187eebba2c1990030f1d774583320061fa96e8b066400c3d52dd160cc80187eea3a2c1990030f1d474583320061ebaea9b22640087f855c3644c8050f90ab86c89900a1fa1f75591320043fc16eab22640087d82dd5644c80117f08baac89900237e0d75591320043f438eab226400c3c75dd1644c8018b8ebb9ac8990022fe1d64191320051e42ac83226400c3c75d91434c8011ef0eb08c29931ab5e0d61185320043fc2ae830a640287c855d0614c8010ff0ab80c29900a1f21570185320045fc22e030a64098bc845c0614c8010ff0aba6c09900a1f21574d813262e6cb9ec130264008fb87580604c8050fd0fbaac7a0ab70f1d37558f410043ec16eab1e82048bc845d563d056f878e83aac7a08021fa1f5258f410143e43ea4b1e8209a9e840c963d04015ab02192c7a0802b66003258f412545fc32e121e820093f855c243d0495974c0b8487a080a1fa177058b410043ec2ee0b168248a3e84dd952d049187ce9bb2a5a08029be097654b412461e3b2e8a968200b1c835d152d058965f04ba2a5a08021fe1d6354b410043e43ac6a9682668bc8758d42d04cd938e6b1a85a090e2f61b7050b410049ec2ee0a168243cba60dc142d04010ff0abb665a080a1f21576ccb410245e422ed996820087f855d932d04050f90abb265a08122f211764cb410446f41ee4b0682008dd83dc960d04018beeba9ac720803171d56350e410143f42ee6b14820087d85dcd629048f4bd073b2a5208029760e7654a4100536c14eca948200a6f825d9529040187aedba2a5208030f9d87454a410246e43ac6994820087d82dd5609040187c81baac1208030f10375582410043f43ea4b04820287c87d4960904010fd0ea92c1208021f21d525824128c5f43e82b048200c3f75d0560904a357501a0ac1208be8fa1b74d95410058f41ee9b2a8200a7a8098b65504014f301316caa08be1f61c62d954100636b90c5b2
  | 26 => 0xa1fe087650d520143ec10eca1aa400c3f421d9435480187a843b286a91224f2117610d522461e322ec21aa44795c835d843548012df04bb086a91234e1017010d522443ec3ec9b0aa448c3e74d9361548014b906b26c2a90024fe1173d85522449e422e7b0aa400c5d7318f61548014ed0231ec2a90030f5d264985520053ac0cc930aa4ced6572d86615480127f08b84c2a91224f21170985520061fb16e8b0aa400d2f62dd1615496b87ec43a2c2a90034bd8874585520043f43ec8b0aa448c3c74d916154891878e8b22c2a90029720d64585520068fba6e6b0aa400d1c74dcd61548018bec5b9ac2a900353d8b73585520068fba0e6b0aa400d1c741cd615499b8bec439ac2a900353d8873585520061e3a4c6b0aa400c5f7398d6154801878e831ac2a900317dcc635855200697ba6e4b0aa400d2c74dc96154801a9ee7b92c2a9003531cf7258552666b3b96c2b0aa400c3c749856154801a76e9b82c2a90034e1d37058552006adb9ee0b0aa400d5873dc16154801ad6e5b82c2a90031ed8b7058552006b5b16e0b0aa400d3b741c16154801a70e8382c2a900356dcc7058552006ac398e0b0aa400d6b721c161548018f6c8382c2a90031e59070585520063d318e0b0aa400c78631c1615488d8f6c4382c2a90035ad8870585520063d308e0b0aa4b5c3f629d06154801a5ec53a0c2a90030fd89741855200697b12e830aa40087d87990615480187ae9320c2a90030f5d064185521a4b7c12e630aa400c3d74d8461549976cb05308c2a90021fe1d61185520051e422c230aa400c3d7458461548014f100b08c2a90025de1d6118552655b3c12c230aa448d2e829d36054891a5b053a6c0a92d70fd8a74d815200697b14e9b02a400d3a209d36054801a72413a6c0a90030fd8974d815200697b12e9b02a400c3e605d36054801878c0ba6c0a90030f5d264d815222c3ec38c9b02a400c3d74193605488b4f500326c0a90d25be0973d815210cb6c14e3b02a44587d87d87605480187ae9b0ec0a90031d9c761d815222d3d406c3b02a400a3c84587605480187ae8b0ec0a91169e20161d81522361fb14e9302a400d2f629d2605488b87ec13a4c0a91170f58274981522361fb12e9302a400d2f625d2605489187ce9b24c0a91230f9d164981520052e41ac9302a446c5f629ce6054801a9ec539cc0a911b17d897398152006a7b12e7302a400c3e7498e60548018bae731cc0a90029e60263981520061f3a0c7302a400c5d7318e605480187ce930cc0a90028f61061981520061f3a0c3302a4c9d6972d82605480187ee9322c0a90021fa1c64581522449f420e2b02a40093d841c560548010fd0fb0ac0a90028f211615815222d3c402c2b02a4c8d6b72d8160548910fb0fb20c0a91230f9d364181520043fc3ac8302a400a5c835906054
  | 27 => 0xe422e1b2a86ada3e841c36550d5947b08386caa1ab297a0c70d954356d2ec18e1b2a8600c79701c36550c010fd0f906caa18021f61f20d954356d1f42641b2a8600a3d84c836550c010fd0e106caa18021f61c20d954300536c16ebb128600a6d821d76250c010ff0ab8ec4a180a1f21571d89430043fc2ae1b12860287c855c36250c010fd0fb2ac4a18021fa1c65589430043f43ecab0a8600c6c72d956150c010fd0e32ac2a18031b1c8655854300637b2ee4b0a8600c6c65dc96150c018f6cbb82c2a18031e19770585430063db28e0b0a8600c78651c16150c95976c8382c2a18023de1d61185430043fc2ae030a860287c855c06150c018dce5b2cc0a18031b9c8659814300637b2ae53028600c6c655ca6050c079d0c0b94c0a18033a5cb60981430143f436eab0286ac87c86dd56050c010fd0fb2ac0a18021fa1c65581435be2eb98ca30286008fb875806050c1317908baac4218223720d75588430143f42ee0b10860087d85dc16210c010ff0ab84c22180a1f21570984432765c206e4b0086b5e3840d496010c111f50fa82c021826aea1350580436b696b96c9322a448a3d87d92645480187b0fb24c8a93570f5cb649915224716b96c9322a448a3e86d91645489187eedb22c8a900317d8b7359152006a7b16e6b22a400d1f641cd64548018bcc839ac8a900317190735915266e2fb10e6b22a400d4f621cd64549a9a5ee9b92c8a900353dcf7259152006a639ee4b22a40093f87590645480163906b20c8a934ecbe0964191522451fc3ac8322a400c3f87590645480107f0eb20c8a900387e0d64191520051e41ac8322a400e1c83590645480143906b20c8a92d68fe09641915200717c12c8322a400a3c81590645480147f00b20c8a90030f9c164191520061eb22e2322a40097b805c4645488b2f100b88c8a90865b60a71d8d520061eba4c931aa400a5d8399263549a5a9ae5b1cc6a911e9761f6398d520062ec3ec731aa4d1c5d72d8e635488fc9ae5b1cc6a91224fa127198d520049ec24e331aa40093f845c2635489127908b84c6a90030fd8b7458d5200697b16e8b1aa400c3e631d16354801878c63a2c6a92d70fd887458d5200697b10e8b1aa447c5f76d8d6354801a38e9b1ac6a90034bdd37258d52006963a6e4b1aa4d0d4f73dc9635480187ae8320c6a90038710c6418d52004afc3ac631aa400b1c8458c635499f69f04b18c6a908a5be097118d52004b7c12eda1aa400c5d76d8f43548012df04bb486a90030f5db6490d520061fbb0c921aa40087e869c643548010fb0d38c86a90021fe197090d520043e432e121aa40096d82dd943548018db05bb286a90021fa1a7650d520049fc22eca1aa40095f835d943548012df04bb286a900317d0c7650d520061f218eca1aa400c3c431d943548018b8863b286a900
  | 28 => 0x6000008800401400100280340020050008010006000002801800200401880080120030018014012000001000004e001001000000600a00100040000000000004002002007003801c003002800001a005002800c00000500a000000000d0010000008000004800800000b000003400000200a00140140000048014002004000002800e00200180000080000000004000007001000800c000001000000200000200080000000008004012004000001000c00000200200020000000058016000000800c018002000005c01e00b00400240000110030000000003006002000000e000800000a001004001000200000600000120080008024008000002001000000500180100020010008000000000002803c00000100080200000000000000000002003800000a0030000000000000003000400200000100180040020000004000000001005c008003000001000200a0000028002000000000c0040000070000000006000001801c00b0000000000001004800001200700500240140000018028000008002001801800300000080080000018004004002007000000600900000140000040008000004002000001001c00500200040000080000000002002000000000e000002001c004003000003400a01400400000000190000038004000000800000800100000140020010060038000014000800c006025019801c0100000048000010000001800800000100b000001a0010020000000001000000400200000180240280000008018018004000800c0000020078034006000000003000400900080080000020000004016000004805400800100000040000030018000002003001801400c00000a800c00e00100b800800a005000005c00a002000800002a00100000000000010018000000000003800800200400000a1fa177058b430043ec2ee0b16860087f855c261d0c050f90ab84c3a18222f21175587430047dc02eab0e86038f8805d561d0c050fd0bb8ac5218021f6177158a430043fc12eb30c8604c3f415d66190c0987a82bacc32180a1fe1f52986430043ec3ea530c860287e87dd56090c010fb05baac1218030f90375582430061e206eab04860087e87d496090c050f90fa92c12180b1e1d650582430447c43aa0b048600a7a8098b6550c014f301316caa18ea1f61c62d954300636b90c5b2a86ada3e841cb6550d5947b08396caa18031b5c872d95430043ec3c85b2a8600a7a8090b6550c014f301216caa18021f61e32d954356d1f426e3b2a86aca3d84dc76550d5b47d0938ecaa18028f61271d95430063ab88e3b2a860087e87c876550c010fb0f90ecaa18021fa1c21d95430043ec3843b2a86ada3e840876550c0147b0810ecaa1ab297a0c21d95430052ec1843b2a8600a7a800876550c014f30010ecaa18028fe1170d954356d1
  | 29 => 0x30000000002000000c0720000000004004001001000400401500000400180010018008008003002800000e007000800000400a003000001200b00200040000020008004000004000000000a0020000004026005004000c002006002800c004005004800800000b001802800000000000040000000000004000000001800c00200000f000000000100000000000030038000000001000000001200000180080120020040000012021001800000801c00100000040030030000004000006802000c000002000000c0020098050004000000000000200300280000120010000008004001000000c0040000020000000003001000c01800f000002c0000020000008000006000805800000000000040080000018028004001000000000a001000000c000005003800000000400300000060120018000000000001800000400a009000800a0080010000000000002001800a003000001c0020060030008004001001001800000000080000000160000008000006002800c0080000040080000003000001400a00100000000020030000000006009000004c010005000000000600000300000020010018000010004002003800a00900000040020090088004002005004000400e001000000400c0010000044000003000000400200a0000000000002002007000600200300040020060008008000015000002400a000001800800e000000800c000001003802800000b0008004000000002800400400300c0010006007002004400000300400000000000000024000003000000801200001600340000000038008000004003000000e01b002000c004001000802c006008009000000600b0000060000003000000c00c000001802c00600c0030000000001002802c00c003006800c012003003800002a0000010000002000009003000000100200040000080008018010003000002800a000000001800600f00000000040030000010004000002001c00a0000028000004002001000000a0010000004002002000800002a00b000000801a010000001000000100080000000020038020006007000000c00c0000018010000000003000c00a002001804000c0030000000004000000800002c00d001000000200500380180000000020010000001003001400000100080000000010010008002003000802c0000010060000000001004001800200000300140140030018004002001006005400001e0000000010000001001001600100080080000000000024000000000001001c000006804c00000e000801800a00000000000020040000008000008000803c00a002001805000c00000b000c000000002000000a0030068030000002002002400a00800600000020070068000002002000801c00200000200100120040010000004000001800401200d00500000
  | 30 => 0x63de1ca2200022607ea9bf0003cc5442097000000025631c00000000000000002bc443ee8719180014b8f0800024c80000004778001c5200000008900000000000000810a826511fa4fdae91612101502c0004480000fe000028e000000086f00000012040004c400001f80004fc05c9d2cdc3243000088077669a16b8bae18d4ec9fb1e2c3845f5000166a000590a4a542e00052133cdc4280c2678000000ce20000001a020000b38001b120000000918000c366962d100e089115311b185e0000881a45d06000316bb88e200001d780000006383ca25053ba00054bbaa08360004feaf800000004348000f9800015e9639aec000037000000000055a0000b0c6f2000324089c9c50c91320000d2b1b036d40007a72e93c0460a31208483c5a128c16cf33b14da9fa06a9a29730f4c37d38fc2daa7a00008dca8c0000000c54000a0600022adb920000003d4588863b0f32c75cfc0005068000c3298b0003b400005cf0001bdc0004783968000000b1c000000197a380081bd1012825e53badf8058e4e6248001abe64356398091b20006c024b5b847b800000015a815900fa7a9e4ca5061c1b11d44bf80000fb09e2000000000000082c231aadc00066516aa3fc00031106d2259aea5ea3de80014520000003b3c0000c2000000000000000000006cae301b38340572c8263700000009143c5248172a0000b2a40cc6a43f56337b4000c0a23098cc0004560000000a6e0006150001478000762a1980000005a03005ae0706000035c0007870000000a9ccbc0001cc000050300037592860000008002001000000400a00c0018000010000001800000200000900040000030028020004004000001400c00100000040000000000000034001001800c01e0000008008004001001000400000f0108014000001007002c000000000000c01800600680000000030000008006005000000c00800500000200020010010004002000003006c00000900000100060000000024010001006000400000400000080040000000030002002000001802c004004000400000600180000020030060004002000000000c0160020010004002000005000000600d000000400401300000000000030000004022008000005c0280060028000012002018805000400000100000260000000010000002000800002201d00e000400000000000000000010000000002006000800800e0150018010008002001000000c0000008004004006001002802a0020000008002000000800800000100000000140030000038000003000002400200b003000000200300780000000010010010012001000000803000000a800000000000280080340000048004002002001802001600900700040000070000014006000001800000000e0000004002001000000400200100400100000000
  | 31 => 0xd2a57cae1400000071a8000ad4a96282adfde7e35909c852d4be0195209cd54225821efa568ee859100007b00000004d0800101a79600034a0000000362800146881f40499785dcc020000001e8a29324624112eab912330ff5a9ebb400000000008b4000000000000006e800000000000000014a200000000000000006aa8000000dae00834594ca00017b8001e7c00004a80011f00006ad00c165e1026b900014aaea376700001948ba38d13ac0000000000000000000000000000000072a0854000000774b314db417f0001d05040d400002b5dc980000000fdd036680000293de8600000002d19140004c8800180c00000038a11ac78217b33d96065cd3f0265cb406b90ea000000057b0a980000000005a631a5a8e00018081044c22df00030b183cd3d4d481683ece7c00036f8d9ef3b2261ee58780001f198918625426448000176000782867400092800000004f600033580000000001060000a3c0005f206a53d80000000001852b990000000000a3220180000000005f99d61022e3800000001c8aee000390c000bc868c22f4000000301bab85c89d70000815a000003460ed417a35401703c125881511f08800a6e3b00027c80000004240ec12d43d10000000d5861c3a81a3d7b05230df800058400026c139d6b65be77e8e5d09a000030258c000ccb4110000ff45107a7a78800095b00000000000006ebb37dd08000000252586084400000012da0000003aac03a93c0002cec0000000000000000da24c620f176600000008c00000000000000f1254f6ba0cb40000000000d31c48aa86ce8821cb8bbf64daa15aee9b45782791bea00023e80008fc4f500000001c23a33ec315434c28942322b400089330225f1a42b534fe378c0000000000000062000000000000002605bb30467e00048c8000e040003ae80000000004f8000196ce451dc228dd00000000000113c000000000046a0005db23b800000000000000004595992604cc4a93000181c4327f3535a8387624ca01180019383f219600000007691869d5d5a200052f266de84ef87a58bcd4742d30003a400000001f8a32108290c0000f05d1c0004aa9b89c4cd261a3ac94000e6a0003474e3ec980000000490d4d451248d5d800077b00f800020e0ffa81187a00067e38443f293d18d8000000a730520000000000000000000076f55f800018c05d34f000000000000032ac000000370000000036254f0000f4a9bb526b00dc8068141d0001b180003ad8721b28b940000000000c531bc2ea03a04ba4872c51a90f5e0d20470ad83702851ded39244a57a1b2c34e660000000157c000257000000060800012a4780000000347dc0c0000001c2c000000000000146e000000000000000073680003e800000003159fa000065aee8000bc91d500000000004e11dc52fcc400001
  | 32 => 0x3cc0000000000000000047309ab1d410e24c07eb794000631327acf4000efa10c000000009a0002e104ac895312824430401e000221136e0006408ce95fa0001d100002442e9000005c0006a7000216800000062b0000000241636b35800080f1388001d1200000000005640002ae09d16d221313393c8fea29e5c135193ec4a04d606d560200070835b97ea5f229f00008d235d703af0800088000000018d89ff468aedcaa89e60a50660c220001cb00000008b54e680011ee00011480003540003ac849c0008cd000393d1bc00027b0becc30f331db100018800024c1140000000282115475290f46e3398000d4a000000000000000000000000000ae0fa000e97d6de81791ae0004280000fb20000000000000000000000000045f589b5a9dc8a2d3f218980685775a8000079000000000001d80005e7000134c38b074800000000000033e00000564590ee80000000002040000d880093b68a622fd00000013a000000000012a4ab838781e000048b000000000069600017281ea9932722df02848ec151988cf68ea61af9351d3ef583592eb81260085c52b300008f94c8000000012e000363c0004132dd9c84c3cd86237914c0d010b38a8001e08ca82149f6cf941873c613b118600067bbd404e40004cf80015142b855eb6c44ca00071180000000000599704000bcc6cb8870000f557858b28bd21213e896a5d885f763f3419d9ab1512cbd486ae0000002a9146626d000000000078b1b20a1054a7e20001c8141016000026b4000bff1340f0d0f82aa0a80b996360fe1eead64000535079880c422a6774d10d8e886d14abaec17e2a052eb33686b64770001bf9e54c7b65997a00007cf0001d4c58c000671a13847800052b8c81540b5d00082f106a00022b977480200000000001563ac000309400000005b00000006200efab380000000001ff0000de40000000000d124cc00000000004578000000ddc08f3ce86e4f133a109bcca8bf0035b341e1edfa00000009f40000bb36d006400049dac3c86a00000000018fa1a0324a181dda85515ab7f896879c3eeb850a2c9c366e174c3168e23961cecfaa3ee3fa11a874c0e07212b4c7aacdd3e3b8c8efe10600032c0000bf26381301d4a0002cc00000009a23e0b6fdb820001fc00004880003b600000006d640c04a80008f60002e1814c140000388913ac3e5c014e588600076b1af59a45b50fe000029068770c8560596b2b0a390548707b15ceaf1de128da434000055c6831908d4800001a0000000000c85364800039ab6c78c2b6452c000000327d9e402a00031a00000003bf37ac0000000000000fa000056ab300000b1e00000000000000001d2400000062e9eeceea7df41bac09e50a4400000011a4000557b490ccc80a16b1f58d2a00000012f4000000688a560fc6cdb56f212850e
  | 33 => 0x80004eaaa7d7c64941a888fc0006ca6f78d080001a11ad03ed28009868f18b096a4091fd1e74c9a60f43baff8d7eeb10000001b168280002d49c086c845f90883320000c60000c6800025c0001c3a2996758145daebda06a33a00000003c6875582ca7527a301c00004934e0800000d830000abd6f036942980800000002c59294890000000000000000001ca065a72704000000132c0000ed9e996fa6b757aa60800001c04780000008bc7128000000c8c29413ccc84f2500000000000000430001b905366f12f714189ba0003061ddc5aa5fd3b600000000000c68000d144d53768eaa257212200ccfa0003e70000000000000031c00000000009b118ebd40001a14ef0cf5643079d9168d42cca1ec00000000002a122ecfe742b0b80007262bc00000000005b700006e2c267ad989c5680000000000202226000000000039e000277dbb2ae83ea15c40c8b2a0000001b020001c40d34c640006858000bc87e7000000000000000028714a67bf00036680003064f02d983625cc000000000000000024e4000a9c0001bd06141f121d0000598bac5f59fa0b5a70505fb780c54df30003d1c00000032f8b9cc18a16740addc7ca25b57b94e97060006b09738a1ca8c37291c94a84fb0000001dd022226b9da81de8211b52100b240041df1e392eeba46fe84458c2f4101435ed9c8aa621098d8ce22794acb5955c4d5c2f8071811067300a22dc70a18543f00011ca08d5323ac02dc00079baa6413a36369836e019a1746e3ac900003277252fd13408b9222ac61b9abde0078e707205690b20000000e997978000ba8e180000000000e8f75c00000007c603e0000bde00071f1ff8f560005c916bc0009de0001299e4e9f96e832916a286d6b6af986040000c80ff0ace61d5e1a26581ab370f78fb568a527000352c00042700000000005080000ce0000c6000000000004b300002940000000000001d160000000001558a234f7a098bf4c1746600017d2b341ac1a6c0b60000000060da40007690a340000000000c5c0000000001795baa65a0e09338ae82d200000006aa1f224c91e55ca5eb6a61b74d44e125100e0cac633d3480001e22000336acfd0acd2365500014722e5257925c0008ea5ce00018085a33fc14b05d800000000000006ea5528e600002cd651a0c81ce4644ee21fd34800008c00003ee65800000008220001450001710aeb7778dbc00007b0000000000d152dca005b72669452afb94b6000000320c5e84e846c308105eec97230001aba0614a21d946fcd330000000b7496b4d936d862054d60d92f00001c368d0000000e1c00022052bc4f729320e1b6eb5e00000010f21147b00f40000725117962497e000079000000000033c9e1800000000026540004da0001bacd5a2de0000000000b2935a000001c00041f268d45c000000
  | 34 => 0xb0128000792134ac641863fb01101f95acc4f02cb8347727c351d83e93d0f382a2bd7d430e786cc29c0cdcc660000ec9db800000023ec000e3c3b910b0cd43910001108a02f12000120169c0007249fd8000e862e0212c00000037b000092a0005838000000000000000100a1450000001b0a000100af85e1a51732e955c00094d36a0001128d3200004f0000b70000360952a92270f1815a06d053de17400b085465cb738d16da9000285490e8e173d8000174d49000169000000000004540000000001cc8000d660002db492014e0b79ba5c9aa8b000000122c8781b0a6698cab28037ac1504a00000003ac0000004c380019327fd53f10640002510000001d0406a000077936000069ba479c062b73f79b9c9b2da80e614fdeae2954392f6c424ca65ab23992c25a648095691fc2f900000000000000001540000ee5000000021e95d63b80010d8000000000019c7a03171b40000000000000098ed605918fd8e8600049baa1cea28f10ed00016b0b63000131826c0000000001e442f000013e481a00d276a82922a23d3df17784640a218411d1ae22ab1a520209a6f150000000000b570002868442a380860000d500000f080000000004df37996200000002fd99709f101d9ae9780e6f19e00012e80001cebc00726968304ad3528c60a39d07ac086f20769800000000076a1b19dce0000001448b02a9a69f10f8a2a44433b9710750c965b790c0cb66b11ca85a9d2a82900020d85b88f00000b6892c7800000000000000000000075600057000004800001b58000000add0003d6400019300001d5dee4fe00039a0b423d638c1964000002000333800067500023407960004db2ec40000000000000dde00050121c4ade85f3090824000c0e5ba0000b600000ad80011c0a1330f800146c0000640000000a7f000000179e9660d6aae959061600019c185a0000000018404e7300037ed0c249e2683065e2000000039fc91c0006c680000000003320c0c0004d100022d85f491c72f0000d860503668f31256d9b32b8d78dea2e15fe9544ec20002f6b21000000000000012a6000000058c0004be02110a800000061fae34000c7306d9590000640000139400000059c8db80001410000001e80ccd6b38df00009d800180015f05b10000000000edb3cba619134e9802b8f24ab244b3b9b319ea6ab5000355ccaa07d7959bc12c43b710eb9c86005202da2d9400024931e15fd106c352bd26b9a6c57276c8950000a1e5353151a84a1d5bb239c224813370bb54474df20000000428eea0ca2f751a6000305825800000000000000000006702914a52e881f22d680000004c484a52660f723124a98b836d6a2833d11c0004030b0400027328a31351f84c2576bad4f300005c8000098a9e51021d99ceaaae7049594816ec03f58d2122094e7708d4c77
  | 35 => 0xe0cd50000001b960002ce86d08d00005b41bcc000000089b80948cd7a609bb296927de39523d02640a11e530143a46b0650a1240000001bfb16982446e04e2ce97a4d295d78858d5ea8655525bdaacf541cf94c183ab462e89be4b14d130001be1b5864700029d800000000000005d60000000001524a80000279c9240000000000d461055aa000000000000037481049300001d3c95807f1f7a718000000658b99d8a0d43000000144c000000000000063d6e50f180007ea5140828e02dd36a91c781cc08b70a89d946a7092701c200a8000530188800062919101b087800026ab778000d9f77f961c0000000002580000cc9295097d8c87546f4178c83a53b1d2376037498a4359ea8ed6a1217112a086e0000000000000449000000051ea6f0003d7027c777000000000020d17515f40000000003b0800008e54e8948a8e3f444da804982ef5005a0392f62101e69a385ea000000000000000000015f8000cae2969e20fc200000000011d09c87500000000de16fc073c0000ae5960000db80003528afcec69d3656800000091147596307880005df20b4000814503a8bc0001dc228aad972c00047e8000000bad000296426eda10de129c82c93e0cf1ee94901245d2b440dc600000000000000000003ad00000004b70000000717000283c0000001c3000050c00000028a800060d3e9827c000000000330c088d2f5682bf05e4a4b2f30000dd00000002dd50e087500000015782640000fcdc020007a51e4d65a87d369a400000dee000368000000000000003020830001910cac0002973714000a2c6c900010ca3ce730800072800000000005589d623032ec00013400021d0000cac000019c0009db2142a21086000000395c29a0003958b216aaef073e80004d400000013251da0c059c33d1d7c19c60e00000001e332e2c1000000038b2a3480e00014eb2754006760003d6800000070b80003b26db0003d34ada00000029a400009e631223191ea564f6abf8e8c6ab184ae2c000b0015e085c0001490f0000000059623880017a0239000000000000020a000082e6a622a36446481ac7702901734e0e2479a255c886730a1f70fdcd2d54db94582ad6b75e3bf0000a894d995f1bd4b1a6d7b8d9448c5b15416513725c578fbb31308ab069d800000000000029b80d2ec777d8a45af800039f8001d18b625842a600009ee2ac05e19dc0002dc3200a0c8cb0000000000f0a2eab9e45ae66f63195d511658878f2678266bcd00029d0ff600004d80017f8a140000379cba72700024bc000cc7000047c370dba79c800000063e39c8001d828e330737fc000b7944307280007b359380015949072429220df8be244fab4918c51a1e3b15ca124b9111b05063cd8a0fd0d11ca000922c0000458f4e4898ba115279a22d36c000028223db64137a0b85e
  | 36 => 0x27292f0d683860d5800063f4a600018429af2130000e480000178000f880002a41c8c04861a0000000bb4000615a5c0c500000000b10000a1b3ab299800012372f8001cac8e45308001b4ec236ed86dc0005850000acc9b8e550b491784a0000000272c00027e47abcd0696000000000126c00000023c99d20005af8000000d596438001ccc4de2f0800137800053dad809880000388988cf000018c9df00007da0001a85062000000141c00064e6388000000000482a145d7669f68cb33044e9da42c00000be7a972405e5498cd7783188400036613e11b55de0f400039c08460000201edc00043d00012099e0bb83ad2324b0680b6bf94897a248100030e405200062614bd83424e6c739d80007a261100019b2000388b4f000038d000000000000044b8000000c8834ca49400025a2adac300000000002dad49400000025283340004ca00014d89a70001bb5cc81e90ca93f468ae39359bbd0000000000127d61aab300007cc11859a0000001296000584800066a43125926d4000000759000076695400000000000004c7147c08a4cb0000000aa451900018acbf8f232cbbb8c000ac91ae116dac6cc85de091c5b0d3105c80002882ba183b86ca1a1b90af991451cc8e35490eccc25fd5c98000e660007168084000b22000000000008503d0000e9014c0568001b7600005f0000536d07000000000004b0c22748b2a0000002f95c1495100020e59fe5ee3319d3000000057380000000000000001d722d10000548e70000547a3080000000001a617427c02ee302ce36e6c12c233800000000000000000000001a340000000000000818000000000154e00013e9cc5ae691f00000000003290003a487b632a0000d39be80005420fa400041a00022a196e58d13705c4a7885d0001cbc9be52b08c80014920a741e91ac0008640290a900000000000000260dad0003bad9529830272485b4895f1702635de6c4e5619eb49460003da81c92fe906000117000053200008ade428c565f8f68fae00000000007c0e6b72d000000024f21a000074e51314fae5d7da00000034097ee4393800b41140b7b4ea278490812d3b822b00000001980e08b080f873b80004b80b52ff176d926a272453711eac00027e0000e52bb571a1b78e247e52e38058e68eba4c7800144a3fe00036c9788dcf42c938c000000000000162e2750000155dbc0000002d9000000022327392ce00073721a9e7816b1538000ae03340000000d6c0004b88d040009f41baaaacef400064930ddd2e2d90d5a2edd6600008d0001d38d7d1970000f920000001e3d8200844972c8000000029080008045020000f700000900000f9c74a00039e80007762c000016f19ca99d3240028edac510e5aba87ae3eb0a30001af00000002b6c462a4710dbad858eb8179b3540f328b03ca8001b
  | 37 => 0x2caccf1c4848166200000031480001b6344000000000052900143a2a7273a346c0001c90000000510ea12e18a880000005b5000174c0000000001e52000661213c3660000ee8001b4af1c2e112a961c27a4988000ac454a53e8955290d3a653a3cd63e49d064800067297314d24e8ddc8a11a49df4dfa0e2000045ca6660000000000000002ab3a6c0000001458000f96000670800000037b0001de5bd86136652228000c8d0001494dbeb8e00000010e662f4e604b168e8dd40e060048400067cb1bc33e3ea2fca4d00002fe0000000b4a0000000000938e8a3b024481f26530aa0055e3285c3d70dd968415a2f9af7c000cef0d80c50c60d934f9836000010a30b9554470615000071168250b3cd82a89a400035e0e39b0e17a0000000f08cd10000001af200014000000000005b89fdd4600000000de94320003a02224f06bd55f413303144e10872eec7a697955c8a50ccec470fda7ad7d8bd96efa15c4cce5b3ff8da1148afb776034dcc400000010380004ff000307cc8cc3b15f16c8bce6931a30000814af24c000000005ff2ec00004c0000565b58947c0001418001c5c1fd485964cb8c0000bb97b031e0006a703945b6703121ae79e4839203bbd21c54d7e6b6205d9da714000000000000000000001ec0000003c30ae638700006bc00037d0000000000dcc2581b553fc03841d96883ae6a400028f400056016e9aa80000006f4a079744db34e080000007670001599d261a23af0e042d04a1367041160c85b4f18001d5e75213c11e94f0af371ba66431278100024e0000343000000143e53865930e911091b52c1524a224dd23aa71cfa447c4538371ad2000710022831cec8570bb2c562c58000237dd1a8be1259b91b560000002e8c77a00078ead84b50f32486b8bd8685b36aa0e8509882700008d8000bca26d80000001fe74a01713f60000548000000000538800000000042f0000a485410000001a5c00031d3c5d36286240d0e3009a2775dcb964000cd47548000000000000130d624e000000000000ac20000000000b6700007d40000000001c4c0004f8000151114c3a007680009c47c80b0b7c4000caf000261400000078a16ac65eaa91ffa90c7326a0274873800017328c06b80005430ab8c2ccd8efe35a97d4000c7a1e92e8100e57957b0001c0a00000000019f66c20000000b4e2d402613b8000062000003036439b00000007c403300011c12d82f800000017de0003d0b2799d45bd729910dc1e03c06faea95206376840000000a7c0003745b080000580efc0003d80000000000000548a98928eb73556b45c000000000000000000001b85b02a2f3533d2a8c000ac51e2813d29ed6f3a50c106667a8233a21d356ce7167b1d9a1a1a525d87a137025d0000001b8c000000030445c000203000019861b38e8001928b7a0
  | 38 => 0x4d432e876895c1079aec07a24d39f081d2c801b013a8406622b06b2000000000066980000000000001c7188c000000000000000011980001580000001d2cc987e60002b3400000070f835800054b0000120000d443f8a011c8ed950ba80000000007328a8000000009f8000000000000379dbf859f6851cf10a41d85851929a4a0a0202066cdb290a7aea82da381c05d91e4566cca000015740000003d814d1a6a2fc6061804000b4a00021d800021a49a800020e2923a70f500000004fb82240000000000000ebe00000000000000003ae00001641f8051990400007619d9945cf400034d128808eea732825c80004415e28000000c78622ab702ac8db000120c0006682fa2a50000686036800038e1830000001004d38000000178c2f17293268d70b264152328e9a7f263c80000007af4a1018da820001bb943ca982901382b699bc2455593b4406c23b1e7846cec4e2701f86edd5abc15341ab8494ef1558954d7ae47f49faba4e0ead848e879196a318000157dc966c7567b41197ca5a2f8b0cd3ea88d715800000019771eb0005768ae131b2543460003872e1c0002c30000000000aa20001a1000055e0001641d5840f37f95a03da0002e4000043cbbd000365855273625b8001a7e0003b200000000001ba0001588f1a0000000000576000325dbf267208400016220000003b180006d84bb37500007197550459abcb5c3d21c2830c29c0b82e7d8820000691bec9e0d20000343cd7c000112859918000009e91953387685e58000000ef90000000000d2200000000001f00000001154e3a30800010460002b721e853017e7819061e5a8cf000177d46200000001cd81eb4b19f37d9c261310000bb5dcc00000010b42f8000000000000048d678b7000000000002b008ba9a553cb1fc94827f0000000000ba765a000000081249316ddb5410d000000000000020e113c00000056fa558000c7c797000002600018ea0b800000013582c4f200004478b24000b8c515b4383843f90b108a000067e00021143ca3260df04e0d823e10000001b78c595859b5cf46e6379e800000069d1030000f8a0003d6139994a1000743cb149c00000028fc66e94504000d49365c9604ba900003f06ac1094000eb70930c581c60006190000ff214375f874d9220007059b31b464ef0ae99ec3d400011a0000000e7104c8c3c0000003cfacb97561d62a0317d89600000022700000002558f640008346d30eb832c90962400000005bf4a80c95e8c00002300e8000000000356c00067f0af0000310b720000b159b000000000000000000003b7c69e2ff3a280008560000000000bc4a8e36010b81b20006140001aa664b03c924c00044d2c025e8bf0b894120788b3c2ad258b820d2e63907700000004ad57d33e80000115983904000000000000068042f7199ed9
  | 39 => 0x2ce211cdcc12500017ec0006921cd00ac0000000000001b380005018000ca40000000001c34e0c000000103a000621000000000074f2f9c00012800000000000000000248000000783b7dc83e000194000000000039b9ec800000000000b400082b61380000003de00016b032200000004e9810f023e6a2493d2c6b76e9e1400000034101989d48b13788000a3a6062190de55c632b72c3b0d2342a1000000075a11d0be80008a448900000014122972668000000d27223a2cc00030e20f39a41a20000000000e1a00000000014c6d0c0000000000e9d000000000000000000000caa810000a3139e67c4412ea427659b493800035000000029755cc2b600023558e4000000000000028528d8c7d380000000172c000b3e0001a500008e92db00010660000002d208ec2e32092c589ac17b0e28001388cc41e1126825e5f66a8800071e0001f32e6c5020002f038580002532b5b1a8000ddd62f3981de4025000000150676e57f94f4e5c20b5a19f084548004b499d06648c40a783a9666ac155d8bbc66c7220000205248c6700038b18e8f1b6cca4211708852082fec0005d91b9ad3cdd835041f8c4d32400007fa745894842722218c15e4b6718b044a008301168000ac230c167000000000048c3af4e5000000006f40000005fc80000000003a381d03dc00043723e8714aa10001e797a6f49286124486636c59e0554840b8f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xd128b90c0000342400e53ca401700c0018c464f09c04001d1c300000e169240000bd4c2c98dd18004c585544896d30e83c1401392c48954114d87c28a8d4cd555c781108b13548908cac0008006800012020a150005070fc7504000160f8b440ed6481004438f46d58845cc17400c910600460200300003e30303000021b180c10010002802c00004023008500607e1f83590645480181f8720d64191520060720e70590645480183b809c164191520050724d645c464548014349159171191520060e201645c4645480103d98dd86490d5200507a4f76192435480141c935087650d52005072517318f615480181c7420d64585520051624d641c161548018397420161185520060e20174587605480181e7420d6498152005072517318c605480181c7620d7454b410040f662761d1529040141e939d87454a410060e183855c2435040181c7620d74549410060e18185dc1425040183860e15709054100586a4f84d94605040162992a1152181410058624d84548605040162b926115218141004a624d85508605040123998950511814100607210835d9521040103c9761952504410050ea5d651c1411040143897594705044100706a0d651c14110401c198359470504410050ee49651c1411040143996d4870504410050e659521c1411040160d92994329923100685995810ca648c44744c97589524c4310049364a859d8634840181c8420d7654b400040fa62405d952d000183870e0965507400040f25d8654941d00018387061952507403e60ea1d65dc141d00014389759470507403e60e201655d221d000181f7620d7454a400040f65f86548419000103f985d874549400050724d761d15250001434915d874549400050d644405d4615000181c7620d74548400060710c8758d521000181c8421d63548400060721c8558d421000183880e1576904400060761c650c8644c00160d92194321913000685195810c8644c001a4582548614c530007111c952185314c001c45520c87158d2000435261215cc6148001c4552485731852000570644825cc4048001d09525097310120004722617348440480019c0874c5214c120005b02593148530480a943a90d9175106102042e25d8094d64040012aa94e0175588100058aa53805d562040012a89460253588100068aa1162dc1520400146b9761562d00103e70a9d17558b400400186b8758952d001028e2ae1d625074004001c2874d4962440100051a25d8558910040a14aa949d162440100070add4745891004001c28751d162440100070aa14745891004001c29851d162440100061a21d625491004001c28745895244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x212800188040180c49900b22e2322a400c0c24480591711915200540b4532b02194c918802815a11d8835d15210001502d10cac08643226000c11261524857318520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x2
  | 5 => 0x4b
  | 6 => 0x4e
  | 7 => 0x138e
  | 8 => 0x4
  | 9 => 0x5
  | 10 => 0x94b
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124e
  | 14 => 0x138b
  | 15 => 0x98e
  | 16 => 0x128e
  | 17 => 0xcb
  | 18 => 0xce
  | 19 => 0x9cb
  | 20 => 0x9ce
  | 21 => 0x12cb
  | 22 => 0x12ce
  | 23 => 0x168b
  | 24 => 0x168e
  | 25 => 0x10b
  | 26 => 0x10e
  | 27 => 0xa0b
  | 28 => 0xa0e
  | 29 => 0x130b
  | 30 => 0x130e
  | 31 => 0x180b
  | 32 => 0x180e
  | 33 => 0xb0e
  | 34 => 0x140e
  | 35 => 0x24b
  | 36 => 0x24e
  | 37 => 0x144e
  | 38 => 0xb4b
  | 39 => 0xb4e
  | 40 => 0x144b
  | 41 => 0x16cb
  | 42 => 0x16ce
  | 43 => 0x28b
  | 44 => 0x28e
  | 45 => 0x148e
  | 46 => 0xb8b
  | 47 => 0xb8e
  | 48 => 0x148b
  | 49 => 0x184b
  | 50 => 0x184e
  | 51 => 0xcce
  | 52 => 0x170e
  | 53 => 0xd0e
  | 54 => 0x188e
  | 55 => 0x58b
  | 56 => 0x58e
  | 57 => 0xe8b
  | 58 => 0xe8e
  | 59 => 0x178b
  | 60 => 0x178e
  | 61 => 0x18cb
  | 62 => 0x18ce
  | 63 => 0x94056
  | 64 => 0x4d
  | 65 => 0x138d
  | 66 => 0x180056
  | 67 => 0xd09
  | 68 => 0x1889
  | 69 => 0xd49
  | 70 => 0x1a09
  | 71 => 0xd4c
  | 72 => 0xd4d
  | 73 => 0x589
  | 74 => 0x1789
  | 75 => 0x138956
  | 76 => 0x98d
  | 77 => 0x98956
  | 78 => 0x128d
  | 79 => 0x128956
  | 80 => 0x289
  | 81 => 0x1489
  | 82 => 0x14c9
  | 83 => 0x139256
  | 84 => 0x10a
  | 85 => 0x11396
  | 86 => 0x181396
  | 87 => 0x9c996
  | 88 => 0x10996
  | 89 => 0x9d296
  | 90 => 0xb49d6
  | 91 => 0x9cb56
  | 92 => 0x16c9d6
  | 93 => 0xe89d6
  | 94 => 0x1789d6
  | 95 => 0x9ce96
  | 96 => 0x10c
  | 97 => 0x130c
  | 98 => 0x17c9
  | 99 => 0x134c
  | 100 => 0xb5696
  | 101 => 0xb8c
  | 102 => 0x184c
  | 103 => 0xe9696
  | 104 => 0x148116
  | 105 => 0x11496
  | 106 => 0x10d16
  | 107 => 0x178116
  | 108 => 0x11796
  | 109 => 0xb8a16
  | 110 => 0xa0b96
  | 111 => 0x184a16
  | 112 => 0x29316
  | 113 => 0x130296
  | 114 => 0x149316
  | 115 => 0x131496
  | 116 => 0x130d16
  | 117 => 0x131896
  | 118 => 0x59316
  | 119 => 0x130596
  | 120 => 0x179316
  | 121 => 0x131796
  | 122 => 0xa4d
  | 123 => 0xb9816
  | 124 => 0x1049
  | 125 => 0x144b16
  | 126 => 0xb4256
  | 127 => 0x144b56
  | 128 => 0x16d456
  | 129 => 0xbcc
  | 130 => 0xb8296
  | 131 => 0x148b96
  | 132 => 0xb9496
  | 133 => 0xd0b96
  | 134 => 0xb8d16
  | 135 => 0x188b96
  | 136 => 0xb9896
  | 137 => 0x58b96
  | 138 => 0xb8596
  | 139 => 0x178b96
  | 140 => 0xb9796
  | 141 => 0x14cd
  | 142 => 0x185496
  | 143 => 0x184d16
  | 144 => 0x179856
  | 145 => 0x185796
  | 146 => 0xe8d16
  | 147 => 0xe9896
  | 148 => 0x14b
  | 149 => 0x8e
  | 150 => 0x198b
  | 151 => 0xa4b
  | 152 => 0x134b
  | 153 => 0x150e
  | 154 => 0x2cb
  | 155 => 0x14cb
  | 156 => 0x20e
  | 157 => 0x19cb
  | 158 => 0xbcb
  | 159 => 0x154e
  | 160 => 0x5cb
  | 161 => 0x3ce
  | 162 => 0x17cb
  | 163 => 0x1a4b
  | 164 => 0xecb
  | 165 => 0x15ce
  | 166 => 0x74b
  | 167 => 0x40e
  | 168 => 0x194b
  | 169 => 0x1a8b
  | 170 => 0x104b
  | 171 => 0x160e
  | 172 => 0x194c
  | 173 => 0x17cd
  | 174 => 0x1949
  | 175 => 0x5516
  | 176 => 0x49d6
  | 177 => 0x5816
  | 178 => 0x14c
  | 179 => 0x2cd
  | 180 => 0x2c9
  | 181 => 0x1a0d
  | 182 => 0x5c9
  | 183 => 0x5cd
  | 184 => 0x11896
  | 185 => 0x74c
  | 186 => 0x1309d6
  | 187 => 0x131816
  | 188 => 0x181316
  | 189 => 0x180b96
  | 190 => 0x181616
  | 191 => 0x180e96
  | 192 => 0x25253
  | 193 => 0x1456d6
  | 194 => 0x29616
  | 195 => 0x28e96
  | 196 => 0x185896
  | 197 => 0x1689d3
  | 198 => 0x25453
  | 199 => 0x9296
  | 200 => 0x151296
  | 201 => 0x150996
  | 202 => 0x21416
  | 203 => 0x20b16
  | 204 => 0x155416
  | 205 => 0x1a0c
  | 206 => 0x154b16
  | 207 => 0x3d716
  | 208 => 0x1715d6
  | 209 => 0x1a57d3
  | 210 => 0x15ccd6
  | 211 => 0x41896
  | 212 => 0x189616
  | 213 => 0x1a9953
  | 214 => 0x160d16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2666
  | 6 => 8400
  | 5 => 3937
  | 4 => 94
  | 3 => 6
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
  | 7 => packedAt gbK7 (109298+((h/888+packedAt gbK7 (98642+(h % 888)*12) 12) % 3200)*13) 13
  | 6 => packedAt gbK6 (442400+((h/2800+packedAt gbK6 (403200+(h % 2800)*14) 14) % 11089)*15) 15
  | 5 => packedAt gbK5 (249339+((h/1312+packedAt gbK5 (232283+(h % 1312)*13) 13) % 5716)*13) 13
  | 4 => packedAt gbK4 (6797+((h/31+packedAt gbK4 (6580+(h % 31)*7) 7) % 113)*8) 8
  | 3 => packedAt gbK3 (494+((h/2+packedAt gbK3 (486+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f0f81f03c1fff8fc03fe03fc39fe44e41f673
  | 1 => 0xfff001ffffe07ff0003fffffcc6407fc7e387f
  | 2 => 0x81fffe003fff83ffffc1ffc03078787387cf9c
  | 3 => 0x1ffffffc00003fffffe00003f807f83f80fe0
  | 4 => 0x1fffffffffffc00000000003fff8003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x330390520c0ca58e41b320958189e44640d631
  | 1 => 0xc43000a451204a1002044b2a042401981a2846
  | 2 => 0x1044a200265900a49481948090582860854298
  | 3 => 0x2199553a8004234b2b3801032b805683680d60
  | 4 => 0x41ee79cf3b9670020c10060c3ef68003f7b000
  | 5 => 0x7800600c0318400c302118303f7f7f7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37137
namespace PEqualNP.Outside.L_meta_37137
open PEqualNP.Outside.L_meta_37137.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
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
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 4 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 4 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 12 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 94 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_3936 : Interval gbAtlas 5 3936 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3937 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)))))) (concat (concat (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)))) (concat (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))))) (concat (concat (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168))) (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296)) (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424)))) (concat (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680))) (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)) (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 bgb_5_3936)))))))
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
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8096 : Interval gbAtlas 6 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8128 : Interval gbAtlas 6 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8160 : Interval gbAtlas 6 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8192 : Interval gbAtlas 6 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8224 : Interval gbAtlas 6 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8256 : Interval gbAtlas 6 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8288 : Interval gbAtlas 6 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8320 : Interval gbAtlas 6 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8352 : Interval gbAtlas 6 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8384 : Interval gbAtlas 6 8384 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8400 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))))) (concat (concat (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))) (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))))) (concat (concat (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360))) (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672)))) (concat (concat (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800)) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928))) (concat (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 bgb_6_5056)) (concat (concat bgb_6_5088 bgb_6_5120) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)))))) (concat (concat (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)) (concat (concat bgb_6_5376 bgb_6_5408) (concat bgb_6_5440 bgb_6_5472))) (concat (concat (concat bgb_6_5504 bgb_6_5536) (concat bgb_6_5568 bgb_6_5600)) (concat (concat bgb_6_5632 bgb_6_5664) (concat bgb_6_5696 bgb_6_5728)))) (concat (concat (concat (concat bgb_6_5760 bgb_6_5792) (concat bgb_6_5824 bgb_6_5856)) (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984))) (concat (concat (concat bgb_6_6016 bgb_6_6048) (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 (concat bgb_6_6240 bgb_6_6272))))))) (concat (concat (concat (concat (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400)) (concat (concat bgb_6_6432 bgb_6_6464) (concat bgb_6_6496 bgb_6_6528))) (concat (concat (concat bgb_6_6560 bgb_6_6592) (concat bgb_6_6624 bgb_6_6656)) (concat (concat bgb_6_6688 bgb_6_6720) (concat bgb_6_6752 bgb_6_6784)))) (concat (concat (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912)) (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040))) (concat (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168)) (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 (concat bgb_6_7296 bgb_6_7328)))))) (concat (concat (concat (concat (concat bgb_6_7360 bgb_6_7392) (concat bgb_6_7424 bgb_6_7456)) (concat (concat bgb_6_7488 bgb_6_7520) (concat bgb_6_7552 bgb_6_7584))) (concat (concat (concat bgb_6_7616 bgb_6_7648) (concat bgb_6_7680 bgb_6_7712)) (concat (concat bgb_6_7744 bgb_6_7776) (concat bgb_6_7808 bgb_6_7840)))) (concat (concat (concat (concat bgb_6_7872 bgb_6_7904) (concat bgb_6_7936 bgb_6_7968)) (concat (concat bgb_6_8000 bgb_6_8032) (concat bgb_6_8064 bgb_6_8096))) (concat (concat (concat bgb_6_8128 bgb_6_8160) (concat bgb_6_8192 bgb_6_8224)) (concat (concat bgb_6_8256 bgb_6_8288) (concat bgb_6_8320 (concat bgb_6_8352 bgb_6_8384)))))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2624 : Interval gbAtlas 7 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2656 : Interval gbAtlas 7 2656 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2666 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)))) (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)))))) (concat (concat (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 (concat bgb_7_1440 bgb_7_1472))) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632)))) (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 (concat bgb_7_1760 bgb_7_1792))) (concat (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)) (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984))))) (concat (concat (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144))) (concat (concat bgb_7_2176 bgb_7_2208) (concat bgb_7_2240 (concat bgb_7_2272 bgb_7_2304)))) (concat (concat (concat bgb_7_2336 bgb_7_2368) (concat bgb_7_2400 (concat bgb_7_2432 bgb_7_2464))) (concat (concat bgb_7_2496 (concat bgb_7_2528 bgb_7_2560)) (concat bgb_7_2592 (concat bgb_7_2624 bgb_7_2656)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8feeafcc8fce8f8c8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813000 * 2 ^ 32 + 4243126472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37137.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,3]⟩,⟨.or,[1,3]⟩,⟨.or,[2,5]⟩,⟨.and,[4,8]⟩,⟨.or,[4,5]⟩,⟨.and,[6,10]⟩,⟨.or,[2,11]⟩,⟨.and,[7,12]⟩,⟨.or,[1,9]⟩,⟨.and,[0,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4243126472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4243126472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37137

open PEqualNP.Outside.L_meta_37137 in
theorem PEqualNP.Outside.L_meta_37137 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4243126472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4243126472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
