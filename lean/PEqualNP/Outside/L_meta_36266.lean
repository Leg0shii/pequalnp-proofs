import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36266.Model
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


end PEqualNP.Outside.L_meta_36266.Model

namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
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

def SBf (j : Nat) : Nat := [6, 6, 7, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36266

namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x3000c05016208120290e0020020000be43bc43bf42bd42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1101808e29a852d52d06b0a098cb54840
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
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (212+((h/4+packedAt s0K4 (192+(h % 4)*5) 5) % 20)*5) 5
  | 3 => packedAt s0K3 (111+((h/1+packedAt s0K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ffc0ffffc0ff07ffffc0ff83ffe07e7f33f3
  | 2 => 0xffffff07fffffff81f03fffffc1fffff91fc7f
  | 3 => 0xf81ffff81fff07ffe003ff07ffe1ff81e1cf9c
  | 4 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x90c44621448941016524c8498123212c2711b1
  | 2 => 0x21088812091082280a41119224144a50906446
  | 3 => 0x52551240d2284d52a0a26a44cb419505618a98
  | 4 => 0x659a249483b2969cd3c8308772980619da0f60
  | 5 => 0x861c38e71c3ce7e71cf3bce063111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36266
namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc018000f10008024a40520000e00c04000b00734000980bf43de43bd43dd439d43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe61a0044823080145a801c28600081e91002298a0208c2747552438fa92871f5150e38a0a1c754f429aa8e851d54ccaaaa39947551328ea9e832d52d063aa998d354b318eaa2631d531025aa4204d544408faa4611d540c29aa4185554430
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4061000855875250e0d62d4543835885050e156114143
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
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
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 27)*6) 6
  | 3 => packedAt s1K3 (602+((h/7+packedAt s1K3 (567+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s1K2 (156+((h/1+packedAt s1K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 2 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 3 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 2 => 0x1212522244a90309434290a252144943294512
  | 3 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36266
namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x100b0b921aa13043488a151844c9f0c3c513103800b3c1d2ab0aa819d2c40e004e840004600129008000000012090060000006c0070013806072c50012c41ccff43fe43fd43fc43ff42bf42fe42ee42fd42bd42ed42ad42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd648238ac784f0a00000262f8800a002a800487c00114ce62108c4b813370001a00118005c280e804527115044d800211807e00001740000001fc184a0c83c047b1b8e0da731a12cbc6132868121f1114c7a753b8ccb4270d91800762d9e00007200004a54000e8f2000b000000039000000000104005222000004c000c8d418050c000001c800002f00140d03527010e87d31924de1c40040ac0e1f1f8a259019e80c170015c3c2d040d8d2660a848000000000e04305800584d1d960006401008100840201038280008080058000800100008089800b8a84010382018004000f0e0a0001870000000a5b94b43b6a96877651d0eeaa3a1db94843b6a90873d5490adaa9214b55242d7a9285af5450b5e86a16b90d42d6a1a85ac4350b5ea6a16b94d42d6a9a85ac5350b5ea2a16b94542d6a8a85ac5150b5ea0a16b94142d6a8285ac5050a7ca8215b94842d6a1085ad42cca7ca9194f55232d6a146576518caeaa3196b509329f2a0653d540cb5a84195794f41aea9e836e52d06daa5a0eb50b41d6a1483ad42506dca420db54841d6a10833e54cc67aa998db94b31b6a9663ad42cc67ca918cf55231b7294636d528c75a8518eb50931d6a1063d5310c67ca990cf55321af29e435d53c875a8590eb50a21d6a12433e540867aa810eb50821b7296816d52d035a85a06b50a40d6a12815e53102baa6205b94840b6a9081ad42102eca2205d54440d6a1661ad428c27ea8984f15130b7a92616c524c35a84985dd4530ba28a613e540c27aa8185b94830b6a9061ad420c2eca2185d544309f2a6413d54c835a85906b50a20d6a12413e540827aa8105794c20aea9841ad42082eca2105d54420d6a1621ad428427ea8884f15110afa9a215c53442dea4885b14910d6a12213e540427aa8085794c10aea98216e52042daa4086b50810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd8a92192098800c801e09078014138f02181605801b000d00110e860b83a11f8015080000129d8019800008800014a19ca00f971a001d0e1a9c029e95849b8080030401850000000a10130c000986801196870b1f17800110800400042093c00004020400000042810024082a99874350aa561d0d42a99875350aa561d4d42a99865350aa56194d42c354c5350a8e63d4542a358f5150a8e6394542a358e5150b255114542a3d8d5050a8c6354142a9d855050aa46154142a398c5050a8d6314142a99845050aa56114142c950a518cb254254632c394d42d070d5350b418b58a54cc62d6494b318bd9542cc62d6550b318b58a548c62d6494a318bd95428c62d6550a31e1509310c70e5350b21c354d42c870e5350840c354d42103254294440c9509511022d62151308b590524c22e65509308b195424c32542d4530c9508514c22d62950308b592520c22f65508308b595420c3254294430c9509510c22d6255020c394d420830d5350820c950a510832542544208b588544422d64149108b995424422c6550910c3d4d424430c53509108b58a540422d64948108bd95420422d6550810c394d420430d5350810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 5 => packedAt s2K5 (810+((h/15+packedAt s2K5 (720+(h % 15)*6) 6) % 60)*7) 7
  | 4 => packedAt s2K4 (3827+((h/43+packedAt s2K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s2K3 (2738+((h/22+packedAt s2K3 (2584+(h % 22)*7) 7) % 90)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffc3fffffff03f07fffff07fffff23f1ff
  | 1 => 0xf83e0ffc1f0f83ffc7f870787f870f0fdd4e93
  | 3 => 0xffc00fffe00ffc3ff8007f807ff80ff0e18f1c
  | 4 => 0xffffff0003fffff80007ffff000fe0fe0
  | 5 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8000040000000000000808800090100001025
  | 1 => 0x128c9488ca152612c348345134822a2e4d4692
  | 3 => 0xa195ad1146aa627558c45d425d504ce2e18b18
  | 4 => 0x85294a22948348a9ad9508046a64e044b60dc0
  | 5 => 0xc6318c3b18cc733e36e66e670c408888fbe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36266
namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x15a4003c0004000980500021738140183a944030e24d9e2001080524468100580260018000240001f009ca94168d50034646024428700000010404011c70404c0003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461bf428c37a851877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea1061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641ee42c837a85907b50b20d6a1641df32c83dc6590774cb20f699641cd32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84907b90920dea1241ed424835a849077cc920f719241dd32483da6490734c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443be6488774c910fb20a21f541443ec62887d4c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810ef99021dd32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21f721443bd42887da8510eb50a21ef99443ee32887ba6510fb4ca21e6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490ef50921ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410efd0821f721043bd42087da8410eb50821ef99043ee32087ba6410fb4c821e6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a852077cca40ee994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea1081df32103ba64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0x800800000800000000000000000c00400000000000800400000000400400000000000000000000000000800400800800400000000000000800800401000000000000c00afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a16f54342de286857d5490a7aa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a85be5350b7aa6a16f14d42dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ef21e65dd43ccbb887996fd0b32dea16657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccb3e85997790b32eea16659d42ccbb8859977d4732ef28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85197b90a32dea1465ed428cb5a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbbc86997750d32ee21a65bf424cbdc84996f50932f6a1265ad424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe849967d0932ef21265ce424cbba84996750932e6a12658d424cbb8849977d4532ef28a65dd514cbb8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0x11480000000000000322ad00033f4ee19c0000062c0000000000000000000000000002dc00076162800000024d0b4100000055800000000000e80000000000000000000000000000001de000001540000000000000000000000000000000e3b470000000020e02c000000000000000011400000000345000000000000000000000043e000000000000000000000000000197000000b3af31d277d06b7600000000000000000001a600000000253000000000562fa0f56ca1e00000000000000d6999000000000ca00005800000000000d54000000000000000000000000062000001248000000009b8000003c8448005d49400007212a0000000000000000177000000000004f0a2d048000000006e8004ce984b2000000000002961b22f8000000e2001aa2024ecc6175941000000000000000000000000080c000002aa520000000d2295a198c00058c43000000000001bc000cc46d800000000000002840000000000074800000000358000000000000000051e00000000000001948005462000016b000000000000006ec000000000002c80000073c580002d2000001f00000000000000000000012000511818000000017e00017e53cf000019e00000000000144000000000000000061c3bc000000000000000051a3acf9000000b98e20a16dc0000000000056c0000054e0000000000000000000000001118000000000030a1dc0014a92a65a0000011f0000000000000000035a43000000d78000000005134b00000000000000de00000000000000130560bc476000000000002e3344000000000000000000000000000000000000000003d06c4002550000006580056a0000000000000000000000000fd8005620000019f0f0000000000002600000000041000000000400000000000000000000000000000000000000000800000000000000800800000000400800000000000000000000400000000400800800000000000800000000800800800000800000000c00000c01000000000001000c00001000000000000400000000000000000400400400000000000000000400400000000000000000000000000000c00000000000000000000000400000400000000000000000000400000000000400800000000000400000000c01400800800400000000000000000400800000400000400000000000000400000000400400000000800000000000000000000000800000000000400000800000000000400000800800000000000000400400000000400400000000000000000000400400400c00000400000000000400400000000400000000000400000000000000400000000000000000400800400000000800400000c00000400000000800000800000000800400000400c00400800000400400000000000c0000000000100040100
  | 4 => 0x80000000000000000850e50000000000000000000000000000238000000000000000000000000000000c040024030c00021800000a68d58000004a1500000000008722b000dc4968003389e45700000012c000000000014200000000000000000000000005b60b800242000000001232a0a70000000000000000000000000212000000001f91a20000000000000000000332000000000000000017905a000001530000013d0006000000000003486400000000000000c5116570001ac0005ec0033716a76802907000000000000000000017800000000000000000000000000000000069413102000218000a480000000000000000000002dd000d98000002b000000000000000000000000016001e0003f80025e00000000000000000c10000000000028000000000000000d40002cf000a90002df0000000029d5fc000000000007d1598000000000002020000000000000000001e200000000000000000199d600000000000000000000000000000014e0007b14f8000000000000041e00000000000000000000007acf08000000000036300000187a730008800000000000000000640000000002420000000000000125800000000000030000000000000000000000000c10000000000000036b2646cc0002b000000002060000000012021e000002691ee0000000000000000000000000e000000016c608b9000bf58e800000000001315da0018d9fd61200000000000d10000000007fc00000022000000000fa00000000000c2cb2800000000000000000000009d000c8c000006ba000fe0005dc000002c1000000000000000000000000000000000000001028000000000000000000000000000000dea2f0006b442b58000b9002288000000ea00000026400000000000002c400000000000000001a700048e000001a800000000000000000000d0046000000000a40000000018e00000000000598a90f55ac3880000000047800000000960000fb0000000000000000000000000001b900000000000000000000780000009896b800000000002a20000014800043630c00000000000000001fa000c00000005f00000038a00000000000b2c00000352000001d0000000000000000008aa5f2100000000036a0000000000000000000000000001560000000000000000024b3026c35cdf00000000000000348744000000000000000022e00000183000458002380003e85500029a1d905800000000000000a800000000000000000000008045a1e70000000021a000000000005740000000000000000000000a9800000000000000000004fc00217252000001b8000000000000000000008a0000008122700000000000000000000000da000000000000900000000000000000000000002da000000000000000000023b000b24d00000000000000
  | 5 => 0x61c000000002a0000000000000000000000000000000000000000000000015d000000000000000000017613e00000000000000000000000000027c5a80004f00000000000000000648c80210000015781831a000000002be0005b800000000000001201b8000000000000000048a0013d80000000000036000000000005940000014b000001a40003da000003174fe2d800000382000000000004f40000007e00000075192001ac80010e0880b80000000000000000118a50c800013800000000ae000241000001448003de000000000000000034d0008f4002f727898c1b800000000000404e884d10a9200039c000000000000000000000000000000001488004680000000032a64c00000000001b200047e00000000000000000000ee001618a90001080000000055c6a000000000000000000000010500000000000000000000000000000024d00000000000000000000e600000000000000000000000000000000000000000000000000000000000016f00000000017a6b0aa00126000000000d800012c0000000000000000000000000a300000000018000000000000001e200000000000998000002f400135000000000000f600062c0000024a0018e0000000000000000000000000000948000000000003f000000c889c00054a418000003ea000000000000018601b00000000000000000000000008580027015e0000000000000000000000980000000000000016e000000f30000000019f2c264e000000000008940e80000014c00000000000000000000015b00062a000b41ea0000000002a000000001fa0000007c1244b4000002fa0000000000000000000000000000001e3000000000002a230000000000000003331248f0000004ac5d40033900000000000000000000ea0000000000027693c00000000000000000000000000000000000000000000000000000004a2480d00014b9186744895f0000004280000069e00000041000de400000000b34000000009f8000003020000000026600000000000000002e10e8368ee8002d400000000564425b12bf2b2180a2984000000000006ac000002a90000000000000000000000000000308003aa000ff000000000000000000000019a000000cb0570000000000000000000198670000000006c25840000000000000236000000000000000000000025e000000003dcb30000005ceaf00008f39800000013000bd4000000000000000006200000230000000000000000000000001e000000000000008691a018000000000000000000000000000091000000000000000000000000072400000000000000000000018d3282de000000005fe000000000000019eaf40000007000000075c001c61020001a0000640000036a0003cc2f0000000000003a0000017db1f15a17d92
  | 6 => 0x7f8bc6420017402533600000367000281778636760016a8003e2c6400000000000000005d8000000000000000000046600000000000000000000000000000000000000000000dc000000000000002720000000000019a00053850000000000000000009f00005000000000032000000d300000000000000830d5000000000000ba07888814a990000006500024e000278840000010e800000c0982a943b600000000000000000000000000000000000000000000000000005a2000003260000011c8000000000000055800000000000614f4a930000009cb4200000000000000624000004da0000015a0000ecb9b680000017cad2000000002f6000000000000000006c00037e001568000000000006f0000000000000000052000000ddc000002e8000000002c4000000000000000028123837c000000000009601000000000000000d7c06800000000000000000000f8004fac3413271000001a88000000000002739c000001ba000000002c747c2e000228000000001cd3ee0000005a0000000000000000000000000d800000058c000672180000e40014c00000000235000001ba80000000044000000000002570000015d80000000000000000000bf8001f8cac000004dc000000000000000000000000000000000000000000001e8000ed0000000000000000000000000001082f800097000000138000000006b60000000000000000000000ab8000002567d8d915e626001a9000000000000004b200000000000000000004b67e09304d000000000000000014335c0000000019e0000000022a0006e4000000006d14d800000000ce9c8000348000000000000024e280000000000000000000000000100000000318000000001ec00000000001160000000014500000000000000000a38000000009b00000006a000000000900000036c1c600000000000c1859800000000002e2000000000000f2000000000042c846800000000000000000000007f000000000ac000b6000045000000729a75d20005e800202000000001b80000000000000000000000950000000000000000000000169a8c0ba00000000000000000644ca31023800000001089a50008c8000010000006f0000000000024600c4d40000000000000000698b40000000d4000000006800000018a000000f28006587651880053c000000000000000000000000000000000000bf0000000007200000024c7a00065e00122083000000002830000004d98f0000000000000000000000000000b00a61f2c40a38b100000000000000000000006de4e8000001180000000000000041000000000000000000000000000000000000000b20001b612e6200004a00087081b11000d7885800000000000000009d42c00060e001670000000000020a0000000022e00000000000000000
  | 7 => 0x1c000000000000000000000007c6380000000033000172000000001d35c00000000000070c00000000000000002200000000066a000000004c80000011d000001288000000011b919000000001e45540000000045a0000000063c00000000000ae4000000000000011200000088a986d2199b28c24de85400000000001038000000000000000046dba000556170050005e4001ab808000000002b7000000000000000000000035c0003296c000000002bd00000000000000a09a30bb0000380000000000000000016cd8038d50e00000025d00000142a26000a84000000009a00000000000104000000000000000e60000000000068c0000000072c000000008e800000000000ee000000000000000000000024a44800000000000000aa0005e000000000286cf00ab2e0000000000000000000000000000000002e21f000000000000002e56da00000000000000001132da7cd890006540000000000000000000000000708000000000000000000000353000000000002e000000000000000000380280004d0006100000000000000000000000000000000000000012e0000000000000028d8a000000000000000006dd9a000000001b9b240007089a2876920002206c000000000000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10d3949328434d524ca10e350932843a94248210f24c9208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58854443356115110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10d5584534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910cd15241442d563905109d19541442b5648c510d514e3144274654c510d914a21443a54288510f14ca21442746548510da14a20443e221881109e19520443a94248110f24c920443e121481109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109758a530431e5454c10c7551530425f6254c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48108f992520423d64948109798e520425d63948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520434e6394810d358e520432e5454810cb551520434e5354810d354d520432e6454810cb591520434e6354810d358d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d525081097d97320425d65cc810c7953320431d54cc810d394b320434d52cc81097d95320425d654c810c7951320431d544c810d3949320434d524c810e3509320433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x82af6550b20cbd9542c832f5350b20e394d42c832d5350b20e354d42c830d5350b20c795332c831d54ccb20e350b32c82ad648cb20cb55232c831e544cb20c755132c838f424cb20e350932c832d544cb20d394d32c82cf654cb20d3d9532c834f544cb20e395132c834d544cb20e355132c830d544cb20cb50a51c834d3294720ab59321c82cd63c872097d8d548825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d20ab59242482cd63909209b195424832f6550920cb195424832f5350920cb54d42483ab6050920ea181424838d42cc920ab59232482cd638c920e3d09324838d424c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324823e64145208f590514825e63145209758c514832d4214520d34c8514826e65c8520ab59321482cd63c8520ea50b20483c932c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320834e524c820e350932083365494420cd55251083565394420d554e51083374294420cd50a51083573294420d54ca51083365454420cd55151083565354420d554d51083374254420cd50951083573254420d54c9510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c432f5250b10cb14942c434f524cb10d314932c438d424cb10b558e41c42b5648c710e950a21c43c5328871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f99
  | 2 => 0x5350840c754d421032e525084097d97321025d65cc840d394b321034d52cc84097d95321025d654c840d3949321034d524c840e350932103565394440d554e51103665294440d954a51103374294440cd50a51103573294440d54ca51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd50951103573254440d54c9511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc23e64947308f59251cc29d64cc730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b3588438c23e6494a308f592528c32e5250a30cb549428c34e524ca30d3549328c38d424ca308fd91518c23c64546309bd89518c26c6254630a7992318c23d62d51308f992544c25f63551309b988544c26d62151308f994544c2ad6215130c758c544c32e62151308f588544c32d62151308b588544c25e6590d30c7152434c25c6550d30c7151434c23e64149308f590524c23e65d09308f197424c23e65509308f195424c31f54cc930c7153324c31f544c930c7151324c34f524c930e3509324c25e65cc530a7593314c31c54cc530b358b314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c31c63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2cd6210c308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d6454830d398d520c34f4354830d310d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c31e54cc830c7553320c34d52cc830c7951320c31d544c830d3949320c38d424c830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430d5cca510c3553294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430cdd09510c3354254430d5cc9510c355325443097596310c29e648c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c82cd6390b20d354e42c831e5350b20c754d42c832e5450b20d354d42c
  | 3 => 0xa21d355132887c7614ca21f118532886ad64c8621b358f218863f64542218f191508865f63542219718d508872d4254221d34c9508865e63d51219758f544865e63951219758e544866d62951218f993534863d64d4d218f992534863d6494d219b58a534878d424c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420866d6590821ab59242086cd6390821d354e42086e561908218fd95420871e5350821c754d420872e5450821d354d42086af6550821cbd95420872f5350821e394d420872d5350821e354d420870d535082197597320871e54cc821c7553320878d42cc8219b59632086ad648c821cb55232086cd638c821b9586320865f654c821c7951320871d544c821e3d09320878d424c821cb551320874e534c821b3d95320874f654c821d3d51320878e544c821d3551320878d544c821c3551320872d4294421d34ca51086ad64c8421b358f21087a54288421f14ca210866f65484219dd9521087a74248421f1cc9210873a5494021ce552500875a5394021d654e50087a94294021f24ca500873b4294021ce50a500875b3294021d64ca500872d4254021d34c9500873a5454021ce551500875a5354021d654d50087a94254021f24c9500873b4254021da90950087394254021da50950087294254021d6cc9500876a3254021d64c950087693254021d24c9500876b2154021dc88550087692154021dc485500865e6394b409758e52d032d52d0b40d394932d034d524cb40e350932d025e63947409758e51d029d63d0740ab58b41d02ad6210e409798e529025d6394a40cb949429032d5250a40d3949329034d524ca40e3509329025f63546409718d519026f62546409b189519029e63906409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940e3509325023e65d0540a758f415031c53d0540ab58b415031c5350540c714e405025d6294c4097d89531023d6590c40c754e431031d5310c40ab588431025e63948409758e521034e5394840d354e521034e6394840d358e521034e5354840d354d521032e6454840d398d521034d6354840cb90d521032c4354840c794f421031d53d0840cb54b421031e
  | 4 => 0xb94942d065f65ccb419759732d074e52ccb41d354b32d065f654cb419759532d074e524cb41d354932d078d424cb419b98a539066d6294e41b358a539074e6294e419758a539074d6294e419358a539065f6254e41c794f439071e5350e419798e529065d6394a41c794f429071d53d0a41c794d429071d5350a41cb549429065f65cca4197597329065f654ca4197595329078d424ca41a758f419071e53d0641ab58b419063e6510d41ab588435065e63149419758c525072f5250941cb14942506b46150941d3d49325074c524c941e3509325069e63905419798c505065d63141419b988505066d62141418fd95431065e63948419758e521072d52d0841ad587421074e524c841d3549321078d424c841a758f41106ad62d04418fd954110677655044197d8d501065c63540419b98b54cc66d62d53318f58a54cc71c63553318fd8954cc66e62153319b58854cc71d54d0f31c755043cc6cd6210f318f99252cc63d6494b31cb95252cc72d5494b31cb99252cc72d6494b31cb95152cc72d5454b31cb99152cc72d6454b31d398d52cc74f4354b31d310d52cc63f65d0b318f59742cc72e52d0b31cb54b42cc63f6550b318f59542cc72e5250b31cb54942cc71e54ccb31c755332cc74d52ccb31c795132cc71d544cb31d394932cc78d424cb319b98a548c66d6295231ab58a548c71d6395231cb98a548c63d6295231cb58a548c62d62952318fd89548c71e5490e31c7951438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e54cca31c7553328c71e544ca31c7551328c74d524ca31e3509328c69d64cc631c7953318c6cd62cc6319758e544c66e62951319b58a544c65e65d0d3197994434c71d5410d31b3588434c63e64149318f590524c72f5250931cb149424c74f524c931d3149324c78d424c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c3197d95430c71c5450c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c63e64944318f592510c69d64cc431b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c871e54ccb21c755332c871e544cb21c755132c878d424cb219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21b358e428872f6550a21cb195428872f5350a21cb54d42887a76150a21e9185428878d42cca21ab592328878f424ca21e3509328874f654ca21d3195328874f544c
  | 5 => 0x50d0b4e6294e42c794f4290b1d53d0a42ab98a4350b1c5350d42ab9884350a9e6390942a758e4250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab58f5250aae61d4942ab5835250a9e63d4542a758f5150a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab56114142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210a7661d53329d58754ccb1c5450f32c755043cca3e64947328f59251cca3f64543328f19150ccacd62d5332b598754ccad561d5332c755054ccacd6215332e3d8942cca9e64d4732a759351cca9e6494732a759251ccb555114732a7d9150cca9c6454332a799050cca9d6414332b598450ccad56114332cb98a548cb2e5450a32abd95428cb2f6550a32c7953328cb1d54cca32cb50a518cb2d42542329d986544ca75619513297997434cace62d0d3297195434cb1c5450d32c7550434cace6210d32ab592424cace63909329b195424cb8f4350932e390d424cb8d4350932e310d424cb2f6550932cb195424cb8f6350932e318d424ca9e648c932a7592324cb8d428c9328f993514ca3d64d4532cb508514cb2d42d41328f990504ca3d64141329d984504ca756114132b358a544cad66195132b5586544cacf6255132c7550544cacd64d4932b3987524cacd60d4932e3d4b424ca5e6590932a7592424cace6590932d3996424cacd6490932a3592424cace6190932b3582424cb8f6250932e3d49424cace6550932b3195424cb8f6450932e3d51424cb8c5450932b3185424cacf6050932e3d95424cb8e6550932e3595424cb8c6550932e3d85424cb8e6150932e3585424cb8c6150932e3d81424cb8e6050932e3581424cb8c605093297994424ca9e6410932b3988424cb8d4210932a7993514ca9d64d4532e350b514ca9e6494532a7592514cb8d4294532e3509514cb8d4214532d5544514cb8d42d4132e350a504ca9f6454132a7191504cb8d4254132b5d85504cad46154132a7990504ca9d6414132e3508504cad66114132b5584504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5d6294f4197d8953d071d5390f41c754c43d06ad6210f419798e52d065d6394b41d394e52d074d5394b41d398e52d074d6394b41d394d52d074d5354b41cb99152d074e6354b41d358d52d072e4354b41cb10d52d071e53d0b41c754f42d072d52d0b41c794d42d071d5350b41c
  | 6 => 0xa1d794627b8990ef14a83d13b818a6ea7a03aa9b9868a38ea82196625125c9871db9ad9f61ed201a4e1072909a49efa118370128b22169998f4a88a769f48441a89508c398313f20fa961bd85d1ae22aa9d09b0f09f29f9023a0811c266a3d0958418eda2102a9c48f21f39e908a9b705211fa84851a62a279fd1d30f30580750dd1319cc1d724116c95e23c8a890a95c87483012608783b01699a156279a0080928305f89a28a26fa51860a488ed0000c8a160cb8d729199d80003626080300909a00000808000004030580040000301f02c014098090080040101006e008018010000240080c00a0180000100a0101903a000040040040120180581100207c0e0000100000200000600c1780702c000170010060100680101e0140e0300080000100000c0cc0200209a004018070000000380003a000028000000680a00203a004020120160100600203602c2e80000002c000000020480880402c0c40c00f00000400824032014010000000b80080700602c0000103601c058010020580080a0020040000a018004000040160100880f000090020000120000000103601c0200700e05c0400201a02000000000070020000160100780d0000000a8000420580000c0060200100802012c0280400c0101c0020040000000101005c0080000002c0500d00c0c80a018014024130000020100001b00400c0501900200c0000200000c098210000141580602e0200080001400401000006014000030020081400000c07c00002002000020030000a81780108a0980200c01a01c010050320040080500a0000300b000024080050040140700000404c0080e0020040100a00c0100200f0100000081700a01c0080701e0180100901005401000000018000260000140681d0000280100101c0a40f80900401000003030000050000280100601a018008030060060c4008070280080600000005c1e81600004000000000008028000260340d00500000005800022010010010600140002d01e010018010080601480a02a0000c00303a0000000400e024048000000140580101400c03802002060000000040080180000c0380500101200c14014000028070120040003b80000a048010019b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c750e5110f1d4354043c754c43d0a5e63947429758e51d0a5f63543429718d50d0aad62d4f42ad98753d0ab561d4f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9f6354342a718d50d0a9e6314342a758c50d0ab66114342ad584
  | 7 => 0xec92f000107a691c01408078548c589792f9a38000001f124380023f9ad01e1b7919a21a6da6f15180d06f000103a0ba0f19b1be87911317aa951bb17124324592e806a0a98fa2a05510a0421f8055a2c8e48f18fc10f80e09e9eb1380fd8f881f04319ba5e86106a90b973a652809378f2a070c70049c30910918391b19da0d39f18cf2758b2a4b8fba869ac85105390e98aa9a96a9a6a1ea2909721a17820e9ee9bc9ca01c95fa3906c08703517f0159dc8a590910296315789095692110216c1d8a79019a34a9d96f00e9a803c0c99551468b812297c83783e9d004124c99c1249800aa1728b380f1b3971a011be0b682c80a8a4a86108246a8b0001ce8002182638000b880012e2921fe0b0a1095ba2717d81a91283389f9bc0d212b24f80996018b12a8000a916921380000b0000001a580007d8001c71670000000001991440268c40ea0fb0c914180016e9140459858fa0b611c89f08203f14484c910974159a5725d1118038e101521c00016b1de1a907f9f79f5a2b28289227620a05699208980018622c1ce06800009821999280507f00026a0001410000000b00001b58000498000798bc97917c21d82c29a15c1aa10323783229904380011a8cca5691a2590f794c0001b08c28951358251420000bf15a84e9ac05716202d12809a84b07e042a5614e1658001810ac8030648002958d4258293210181a9120d242038231a2028200019480002b99e13da3e8a20489010938130b7800265876a1c94ba501d18000e500004a0df953a0929c95f0001e88230669b003b9e410e29c07a97b9850da14da901492301cb1c61df0120000000e080000011b82080008da1e02a0f580008a00000007222480001d0000000000000000001cd1890000cf94c8a68000a00000000010000a08000001258bb8001d625a8002398001e38161c50001398998a829b1180000000000001170000809d49b40e28308310d0a4a14b02025d8000eb0002619b21c8954a890988002320000000000d52781d295b12184720406f8270e41b68e398d1fa1849cf152a3f10199819022f9c09b9a5f0e90000000000000000c4a3b1c40562980058001158de8e98000e586ca7b0002252620001ea0002810cd03a00000001780000000c8000000000001f08000f70ac1571c824f08e2371758000001d803400011e8b72222648fe966a238000f01af1c915a18205ca2898a0540171e123c0d29ab04d1ca9c280000017493a14f8892938000a410b04787096d24c00000010c00026a97f9b8a1b83317d12726b17b0d90658001e792d800150036a07a310eb8ce07013205e8d320310d024a5f85c28c96b80622e8001e31241731230291f00aa9fb2882052140101ba2720ee257972059082a732729612039289328530ba16985a9b90c693c0b126028e0141d9a8413414887
  | 8 => 0x18c100d9b113902d9e68001f5092a1f1c203e22693a8ab1388be9480c5136297a0b17681481d8c194a18e9938328d580028b9e591d1a780019700000018d8002681fc1a4164a702159499af80027e1968dc1479d58001438f41ae8002709ffa4618f0002170ec00009611f1148000de0e18000000000080000619369f71d39a31a00788638d6a00164129819116a149cda0c90699f23b86b14520488609c0882998000b58001a727d89c8138718a704e1cf87e840160a089279d127191506e17619619f8000b906300020e1c10c30948d00830001f68a1a7a96fa5c0001679139dea928f111da021bf8a98020001db17ea1205f00021306b9580ae05b24010c8000ca04f9950941ba9b815594d0088661370000af8240210000be26e04f00000019d00000000c0001a20481c58000f92190002338b32778ff0c001f8001bd0fa884a4d96e1b29fca1f87388b8001472971ec8001458001e28000001daa7ea4995d1e026c2382478aea5580009d00000000fa508001532630000001c79a0800118a298000000c81431ef0e31bf1fb8d48778cda3a8468f8158982a8a82586d17e05a13f8d79778e00bb00022b80002e2208e897717507c8bc25a0041b51e1a068000a60001958dd85014283480018e294120205a1d19a80004b800183a96a7c8001cb8dc9d68839e20000968db12087627f81b1dd1251220a79bba74000212a259a60759c180028f2419fa84097a0efa481e72260b526727727d086a7c23319108fa5b80728c15d80008003f8bf8000fc8002660ff80000000000025880000028d1b30000452748c09cca0626111016898092c80016818c800000105a2300025484c23a00006406880000000b822a1b00001e80000027380000000006292d0000ce8001f980000000000006e8600001628000002689521ab9c98000001ff0f38389238690ada0c0000df28980008b22f10400008c2110001f300000000000000004d9888002698319a98000000b192907100007d0f52151880a302f23280013387718c00000000023680000025980001819400000016da5e0e6a85800000134989a3d80a252a752440588e60460b990da67a3502802fa539a10028528d601a1651c6a6ca7893ea4098b91111607b22e13e0c7a4a9308889dc0001e62450bd000228287011800222a7f21a96a28d8001c38000000000002470001fe900926a49170a4b08f07313112a1511988da9ed9ee1f409e07c24d119000209a8e8000af0001f21a199182605b9931d09a525b1d419e82994e93ca800900620cb0fd1d516193301085985093d08d0a280007800023611799c9e991b0d98f608181b9e828f8e70d18f68c21a2a8392b9aa85793b08120d88c90615ea7106d8851df8000000ba8001e49351098698fe000159197a520ee82e8670ca80014022d8000d1170000
  | 9 => 0x39979a2411e26b8002389ec05d8000000a10278008001b600023e0652948289120000ad2540cc02b0000358ab80000000017884910f18424e8448e210483d86a0000d807b9dda189f884a81c14f2852819b49fd9088110db89da530000678e78742028e81d912c0841d21050d8a341300000b49002879639908000bd800187a2d2989eba3082208ea6d2552642358002179ea8000728b409ba449e085e09303c8859540002428f98a50000001e50c60
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98e0d6358a548c70739ac52a463835cd6295231a1ae52a48718d0d72951438c686b94a999463435ca544ca31a1aeaa126518c1d76953318c686b94a998c638395162cc631c1aa8b108698d0d74149324c742a10c299263235ca648c531a1ae42a28618d1970151430c616b90c8a8063435cf6550a21a1ae9b2a6510e0f635095088707b2264a8443135ca63d512185ae5326a690d2970d4d4208686baca6a10438359542cc821a1aeba126410d4970d513208686baca899043c254d4294021e12a8994a010f09424ca5008695baa84a8043c294d4254021e12a6a12a010d4b754c950087852a264a8043c25513254021a92e7212a010d61719095008784a1664a80434a5d23254021ac2e3192a010f0b424c95008784a1264a80434a5d32154021a92e790aa010f214288550087a099442a8043c8d092154021e866490aa010c4d7298e51d0286b9ca4a1481235ca6390640c1ce8b10a6a060d745885350286b90a7a1a81435c85350d40a1ae429e84a050d7214d425030732a8499281435c853d0540c18a6b1682a050d7214d4150286b90a7202818354d6210c40a1ae529a842050d739494210307b2a8499081c15093294440a4ae421aa220705424c95110246b94c7208818398d5290440c2cc6a8c822048d7218d401030631aa4a00818518d5150040a1ae42a2879842d7299251cc307aa2c421c61435d2524ca3091ae5324631860d63588544c30739ac42a261835cd6215130a1ae42a4869850d72151434c286b90a999261435c8544c930a1ceaa12649841d76153314c286b90a998a618315162cc530a1ae42a2629850d72152304c286b90c6aa061835516210c30a1ae52a2641850d74949320c287baa8499061c15093294430a8ae421aa218705424c9510c246b94c91886107dd9548c430c1cc8a94621861664546310c246b90c898061071d9544c030c18c8a92601861464545300c286b98caa12410b1d95350920a48e2a9a84905a1711814248286ba0ca99241131d9544c920a88e2aa264905c1711813248306b1a8428a41835913214520a1ae7292841050d725513208286ba4a49904143dd5424c820c1ecaa126410705424ca5108382a1264a88418a5516008420c92a6b00421044d7298f54c4216b94c9a9e21435cc5250b10a1ae8292658844d7218d5484216b90c8a9c21435ce5250a10a1ae9292650860f64d8f5244306b22c6292218a5916014910c92c6b00a488661615805244286b90a6a1221435cc5250910a1ae42a2648850d7414932442873aa8499221431d5424c910c1ccaa12648860c6550932442923aa8510a21511d53288510c50caa124088648654c92044306b22c729021835916354810a1ae529a840850d739494204286b94a899021435d2524c810a1eeaa12640850d755093204307b2a849902183595424c810
  | 1 => 0x10e8b2a0f144ad2c9b9a2b542b2506303aa41620000090fad40588400ca001180073680a0000000034005515a4912c75418c0000000004a383b0013ad50011110363120536bd0d0018811630c548dc3d25c00be5286c0abf1989818d96f00c006400138de083f13400af1ea8c00343c234b60020874f6601bb887cb734ae000005004130a670000006b5900000003a00008db00121588e000e978b46ea4c007900801180017179a60024a0800ba0a800121f612e400b0391489471111f186002d160ba613508d9a2f6b14400006400024d21613000864facc3cd71db000e5071b6128324ab7c0056000e400004b12db4350c8001c4f4891ca60000000042a2003cb83f6097c869c5599c40005d800002d0015c00007080100aa00000fe133680000840a32c380632a7800cf000000000000002c2945060000a21000ee2700314d8ae5b000e099331a14ece54b31428f4d05c8a00820040d000000c0a0000c00060082000050000c040301804300b0001404020f00404010502814050000014160102000080080000140103802030780c0c030800804070801c0000028180a000080000000c0083a0091ae5b0a8621c8d721814310e4ab88c0a188743dc94354843a1eeaa1aa421d25719915210ea2b8cc6a908743dd94354843a1ee2a1aa421d0c7050d5210e8bb8a87288878354d6214f4291ae730ea4a148f735835250b06aa2c42a665831954350932a4ce3b2a849948d74987524ca47ba2c1a9265319c66550932b0ce3b2a849958571d95424cac338ccaa1265615c66550932c1aca32a849950e75d85424cb42b08c2a126561dc56050932b08e2b02849950e75181424cac3388c0a1265615c4605093291eeca16a29970542544514cb42a16c2a8265a1508615413291eeca10a09968542984504cb42a12c2282658354d6210f41a1ae529a85a0d0d7394942d0707b2a8499683839d16294e41c1ae8b14a720d0d7294f4390686b94a6a1c83435ca53d0a41a1ae529a8520e0d655093290686b94a7a0c838394d62d0641a1ae629284a0d84715093250646b94c720a83135c86354041a1ae431aa998e0d5458843cc686b94a899663435d2524cb31a1eeaa1265
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xd190cb6000000000004402a000380000000000000501204000490581dd94354843905811c14354843a05819d16294e41a05819cd629523180d8795162cc631a05819d16214d40a058298d5190440a058218d5150040a05819cd621513080d8715162cc53080d87991528c430a0582991518c43080d87191524c030a0582191514c030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
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
  | 5 => packedAt s3K5 (27582+((h/296+packedAt s3K5 (24030+(h % 296)*12) 12) % 3041)*11) 11
  | 4 => packedAt s3K4 (55826+((h/446+packedAt s3K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s3K3 (11856+((h/76+packedAt s3K3 (11172+(h % 76)*9) 9) % 301)*9) 9
  | 2 => packedAt s3K2 (864+((h/4+packedAt s3K2 (840+(h % 4)*6) 6) % 36)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 2 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 4 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 2 => 0x2884954442aa441a9888aa8255412530c28a28
  | 4 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36266
namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x40004818161328a938187005bf43bd43bf42bd42bf41bd41df31f631dd31f531d531be40bc40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x14000000438ac31da37ac40011200045000418ea9e853551d0aaaa718e5d0531caa0a6397434c72a8698e595131caaa26397424c72a8498e54c6408ea98812d521026aa220654c440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x990a158a544c61565d0931855953110305524c440
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (224+((h/4+packedAt s4K4 (208+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s4K3 (457+((h/5+packedAt s4K3 (432+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s4K2 (155+((h/1+packedAt s4K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffc7fff8787ff0ff0c3fe1ffe1c3ff0f8cf1cf
  | 1 => 0x87f8f0ff8070ff1ff0387e3c3e03c7f3cb4933
  | 2 => 0x7ff00ffff80ffe1ffc07fc03ffc07fc738e3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80400008008001000000804400404100001045
  | 1 => 0x3492299115296831321c3228b20a9263494912
  | 2 => 0x41004222200280024440448104900488128228
  | 3 => 0x1434acc454482a559aad1022392b30216c0d80
  | 5 => 0x6626c887666ccc99ef367933903220ca7fe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfaeafaeafae8fae8faeafaeafae8fae8faeafaeafae8fae8faeafaeafae8fae8faeafaeafae8fae8faeafaeafae8fae8faeafaeafae8fae8faeafaeafae8fae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36266
namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x10341540014513980e98909388cf191800100007c02900849a22e1019d100059500580000034d8048808801e187014a0000421c004308200228bff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea10817e51103eca2205d94440bea8881f551102eaa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc37e85986f50b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461bf428c37a85185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a9061bf420c37a84185f94430fb2886176510c2faa2187d54430baa88617e500c3be60187e8c030ee98061f9300c2fea9905f95320df2a6413e54c82faa9906f553209eaa6417c54c82fea7905f94f20bea9e417c53c837e85907b90b20dea1641ed42c835a85907b8cb20f6996417e51c82faa3907bc8720f690e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d528837e85106f50a20bf28c417d51882fca1107e8c220fc98441ef20883f641105fd5120bf2a2417d54482f8a8905fd4d20bf29a417d53482f8a6906fd0920f721241bd42483da84906b50920f719241ed32482fea2905f14520f790a41ed21483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea10417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43ec83887d50710fb18e21f531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910dfa1221bd42443ec82887d50510fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd548caf8a9195f54e32bf29465bf428cb7a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca4196fd0832dea1065df320cbdc6419774c832f6990657e510cbeca2195d94432bea8865f5510caeaa2195f94032fd280657a500cafaa0197e54032bca80657e53d06faa7a0ef90f41de21e837e52d06faa5a0efd0b41dea16837e50d06faa1a0df55241bf29c83de53906bca720df54e41eea9c835d539077e8720ef50e41bf294837d529077e8520ef50a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0ef90d41de21a837f52506f8a4a0efd0941dea1283f7415077c82a0dfd4141be282837e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663df43cc7b88798df94b31bea9663bf42cc77a8598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c77e8518ef50a31bf28c63f7418c7e88318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898f7d0d31ee21a637f524c6f8a498efd0931dea1263df324c7ba6498fdd0531fa20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831dfa1063bd420c6fca218f7cc431fb18863dd310c7ea6218f54c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8590ef50b21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea14437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1243bd42487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410df94421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a85205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a
  | 2 => 0x6a7c332ca000000000fd2ee648000002ba14c000000001440000056e2780000009e9a4e400011642c7b2080002b0070f734ab308d97b5621f16722b3fa8295a99b3aa954001895869d098190000018fb0a12d66a00012f000a1c001190000000004e0007842b000578000000005b00000000c38ab6c00105294a696880005a6000c9d80000007f0000008bd5227f0ec2c85c000000964000100005d457a2a2f020800115000730a31ee05eb08ba2dd39639cf49910fa1c49d0d72e61740001a11c000d480d00054119abf2c048c712c631a4ac000854d6504c39d00003cd2880000000026a6e022aa8002c91be000172312c2339582072762dc00283000000461250009a0d704a03ea408a052000170a986e3a8484f6800000ac80018f0100900a000020980a09800000020a8000081e000020600005010008120001e00064010000000e02006060000000000008010020080000002028060000800800030000580806802018000380000004028020482a008000800c0400a06802010020000c0080004010010000b006000040180002802010120480a008000001803000008040081a020000080201828070160400a030140000800000050320000400002008040180e0d00403000000120080c038060000003800010180583e09800000180781400800018000000a01002020100380e0003e0200a00004018000000600002000020000602020098060480000000008020000e00806000060182607800028080e0000000401004010040000400000020000880006000000120700001010040020000407002018060e8000a80a018077e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190feca321dd94643bea8c87f55190eeaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42df21e85bd43d0b7887a15f94742bea8e857e50d0afaa1a16fd4f42df29e85bd53d0b78a7a16fd4742df28e85bd51d0b78a3a16fd4342df28685bd50d0b78a1a15f552429eaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a16f94d42dea9a85bc5350b7ea4a16bd4942dfa8a85be5150b7aa2a16f14542dfa8285be5050b7aa0a16f14142bf2a0853e5410afca6215f54c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653
  | 3 => 0x46a77c69ad30d804897050404814000002180005a8001c23ad67a11568408d20004c20002084700052c5b0dc13a400730f848e0a40f17f0002a4a28cf000000ffa7758800133aaf4964c4a219a55200000133000000e9a5b55869c23000000000000b01bc0000020954e0b05e00007a00000240530000001a10000000018532a6304488659a8a1691822de33466221194658a12cb000050d1001086000398fc330310002243729c035a582a4b40f50d52547c96aa912fa70d36a254f02e81880000098929256000000ee17a000001068690560013a80039c1c0001aa02a268c99a33f05001a85f000000a6a93536840000000006cd0d8000000008eabb0008f059a5d4306e9300002fca795315434c1201d239434180000001546d896800000b049320b00005c7206540ca3c898002daa20000003e2360d58080c652047aa54320a14c8b13a40000021f3c48980016c2e49ecaf842212b783f94325009c3d8c106c318128003d8440000002e26649200f000b14001f735e3b4ad9584088b50983b370568a4a2e3065f0f808117a3c5119372404e55c9b03c0000001b721c394f984b0003fc8880005470437a6455a000b521242c2954e800000000f311712ca3800000000324d91860f07f146038566b68e69691228ec311671002acee9d752e7280000014e1e80019f2f202c8190d3107a0da05929c000000000980014080022431c681a01f48b0b19fb0387ad1b200000220000da00000163abe15aab8e10985409285fa0f0ee060879bc4b885c0490804c000e4a343803d14aa6f0000007a89f0269240000010873c0000000032d01800000b00002a2252a500000a4020012980023e0740005e0002909b0003f2aa0001d9128639262540000008f06135a000ce8000484fce88001de000fa9c64fc4e0000444528f83381b3ca001508005244707c8b44d826d3c858060b211c1182149cc5411a000a156ca32066544002500004b0ed17610e9186c800080b70a62a34e2678002b6208a71270d60001b4fa005000009329fa040af400000308a082aa5e3bc0dcab08344e9100003c000001421c70b60008318a2ae38c792d45166f424800126854000e83ce058781ef0ea2343c8ae1148e8c59661d28f53d0002024f0001d600051c619341a86f8510320422e4002450003b86027d0683084ca6a006000000005003ecce00027c0011f8000000f87500000098c911593c6374000740009041c80052c2ed1000020e0012b8451c001d3b2d700097d110d20004f5468570000010e1b10c808800155000590df8684e4000352b80fc00126a4f36a000001624cc000000c841c60544a4207e0004a800264ae8532ab51449cdd80029e36ced9683289690f0970005b800197000001430002e0000f20004285700020c2ca2402a0004904d4af0920464591821d14
  | 4 => 0x628ec140010e20be0e4b580009c4869f11b9ac0007f86885a
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xa3048278654c120ea50930483c9324c120ea50b204825e63d50209758f540827661d50209d587540823d65950208fd89540823d62550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb94942083365494420cd55251083565394420d554e51083374294420cd50a51083365454420cd55151083565354420d554d51083374254420cd509510832d54c8020d354f200836551c8020d654e200837151880209bd95200832d5448020d354d200836551480209ed9520083595348020ead09200837151480209798f54c425d63d53108f99353c423d64d4f108f99253c423d6494f108f99252c423d6494b108f99052c423d6414b109798c52c425d6314b10b558e41c42b5648c710d514d31c425e63152109758c548426e62152109b588548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e6494a108f592528423e6414a108f590528425e6314a109758c528432e5250a10cb54942843a942482108f58b544423e64951108f994544423d6215110cd584544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c524423e65d09108f197424423e65509108f19542443345490510b558e41442746550510ad5923144334548c5109d1953144334544c510d514d314427465485109e19520443a94248110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f58a540423f62550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c109d984530423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520434d5394810cb992520432d6494810cb951520432d5454810d394d520434d5354810cb991520432d64548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb549420433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x87395494021d694e50087595394021ced0a50087394294021ce95150087395454021d694d50087595354021ced0950087394254021dac8550087722154021da485500877121540219d98653d02756194f40cb54b42d025e63947409758e51d02b66190e40cb949429032d5250a40a798e419023e65d0d40cbd49425023e65d05408f596431031d5390c40ad986431031d5310c40d394e521034d5394840d394d521034d5354840cb991521032e4354840cb10d521031e53d0840c754f421032d52d0840c794d421031d5350840cb94942103565394440d554e51103665294440d954a51103374294440cd50a51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd509511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401031d5350040cb549401033551500409ed95401027661d53309d58754cc2d56190f308f99252cc23d6494b308f99251cc23d6494730a759331cc26e62152309b588548c27661152309d584548c23e6494a308f592528c32e5250a30cb549428c23f64546308f191518c23d62d51308f992544c23e6515130c758c544c23d6215130c7152434c2d56190d3097195434c23e64149308f590524c27661149309d584524c23e65d09308f197424c23e65509308f195424c29d64cc530c7153314c31c544c530d5145314c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23f62550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d64548308fd97420c23d65d0830cb94b420c32d52d08308fd95420c23d6550830cb949420c32d5250830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430cd951510c3355454430d9949510c3655254430cdd09510c3354254430c7553300c34d52cc030d5547300c369528c03097d95300c31d544c030d3549300c355514c0309ed95300c369524c030cb98a54c823e64d4f208f59353c823e6414f208f59053c82766114f209d58453c832e5450b20abd9542c832f6550b20ab59232c82ad64c87209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e208fd91518823c645462097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d208f990534823d6414d209d98453482756114d20ab592424826c6550920ba181424832f6550920cb19542483ab6050920ea18142482ad648c9209b195324823e64145208f590514825e63145209758c51482ad64c8520ea50
  | 2 => 0x64543329d986544ca7561951328f993514ca3d64d45328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540ca3e64150329d984540ca7561150329e980540ca7960150328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb365494432cd552510cb374294432cd50a510cb365454432cd551510cb374254432cd509510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3b4294032ce50a500cb3a5454032ce551500cb725154032dc545500cb3b4254032ce509500cb5b3254032da8c9500cb593254032da4c9500cab66190f41cb54b42d071e53d0e41c794d439071e53d0a41c754f429071e5350a41c754d429072d5250a41c794f419075553d0641ad986435063e6510d41cbd4942506b46150941a798e415065e63141419758c505066e62141419b588505063f6550c41cb54b42106b561d0841b558e411063f65504419dd95411063d6295331c718d54cc63f6255331c755343cc63e6494b318f59252cc63f65d0b318f59742cc63f6550b318f59542cc63d62952318fd89548c73461552318f992528c63d6494a318fd97428c63d65d0a318fd95428c63d6550a31cd553418c71e54cc631ad993318c66e62951319b58a544c65e65d0d31b5987434c63e64149318f590524c67a60149319e580524c72f5250931cb149424c74c524c931b5185324c67665d0531b598f414c79443d0531e5d0c414c6b664cc531a7992314c63e64141318f590504c66e62141319b588504c65e63d50319d987540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63e64948318f592520c72e5250831cb549420c63e64944318f592510c6d5638c43197d95310c677654c431b5d95310c757654c431d5951310c754544c431d5549310c797424c431e5509310c63f64540318f191500c75531540318f99353c863d64d4f218f99053c863d6414f219e98053c86796014f219798f548865d63d52218f993538863d64d4e218f992538863d6494e21d514d318863f64542218f191508865e63951219758e544863e64d4d218f593534863e6494d218f5925348674654c521d514d31486e4624c5218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219d984530867a6014c219e580530863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420875553884219bd9521086776548421d554d21087a54248421ce952500
  | 3 => 0x1d07e4788984839405c79158080a6d0220f0003d80025712424c00181000000c80a80000012600017aa04f1a493f20e4248ae39a3ac0000031a5d84785a00003d03a480f0001150003b8021392ba55c000e30003de575199e60000013024f0540015da3d2d00000018f1161900010e000000f500000000000254082000ed0000000849e900174328340002d85400025a0941602f000000200ae1ad000300ec0382027e8df0003327b0af80021e0004126f1969cd0d05c132558fb21917642c0007e49a62ca10d72b4620e0aa847401ca980041a5f4a59aa000988298a3428370001dd0e04b8000000aea18002ab0521fd321731ee1f4de0f9068ad135a2547630837875516971009ed1ba818a1842352388420ef4ca068f5800430a14cb25e22cac878a150ba89c000000008980587747c0000000000027c000002e25f0000000000000015b0622fd4c258000af488a3400025c578001d23a10fa631f4518631c036e93858ac0000000f8a9a0004fc001fc4720042397f0000000002422406d0e8000000004a000192470000ce2780009b800448624311f2086000000cc1220008180800400000000000203400008120000000008004000a80100c000000200000004050100008000000020000000400004010000002400014000300002400004010000300c000040200c0600800048000001800014000000040000c0f0080005401004020080707c220100002400008020400101c150240303c160000d018070200405c000040100800000000200000804000030140109c1001800004030140000003000020000002c01000060002000005000020040102803008080000801c000080800000004010040002801000000200001005034040200d064000000400400040000000f048020100000000000000100204005018020040305c010040200c0100801008030000c000040040900c07030000080100c0901c050a4010100100000010330000303009cdd0e5190f574354643ad9864350e6e62141439b5885050e7661141439d5845050ed56190c438fd954310e5f6550c439d98653d0a756194f42ad98643d0ab56190f42c754c43d0a5e63947429758e51d0aad62d4f42ad98753d0ab561d4f42ad98653d0ab56194f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9e6314342a758c50d0ab66114342ad58450d0ab66190d42ad5864350b1c5350d429798c5050a5d63141429d9845050a756114142ab58a5350ab66194d42ad5865350aaf6254d42c754c5350aad60d4942a798e5150a9d6394542cd5445150a9f6354142a718d5050ab76154142ad1855050a9e6314142a758c5050ab66114142ad5845050a3f65508429bd954210b2e54508429d98754cca7561d53328f99251cca3d64947328fd9150cca3c
  | 4 => 0x550000dcc0184538000001145427101e9191bc0000000045e33c000a90000009380001c4304e9675702d46387b000a214f0000004803a1921024ad3f2c65287794cab71e0000000000006c8d716b280a585b828358290868000000810e00021484cb000048e0001f0524d047cd591a3303fc7c1bf2528b0bf2714f4070000b92e84f8278040006cc0017022e6d8002122948a4000e42caac4dd800064630000ea000000281e90b654800000000998000790e407c0027b000000048a6000000641cf0006c00896f000000001bd076638000003ce0014806329a1e8000e73e0008000005460013c1d20000005919c000b0400222000474aa26d268000000fd2ee000dd000000a55520c54a6000699d10d21b84493834e680000000a25440001927271c0001629e000000bc46c0b0d100019a598551304d261cf1297000001010d004e3f0001a45720008a8d924255c979a10281d93a96a48a269051f309a49870a4314a88450a5b000394560004c2000aa9240d6608361cb39c651410f331441d5aa44236014fd8185669542a04e3f082448292306ad80695e27623163a760ac7143380000074cbd8001a48a0369e13e87b90b00036288c002a700082c84800140a7cdc993000234762a03983d056a3733caf81a8003be5a40000048426c00102586118001b50000000023501853844131000844001c21dc97c6202333a1c4d18000006d06d0003922590f0e30000004c000000360b216255a001181083fc000438000005b8001474a2000350004b22c07da102088808828e4d82d0cd0b30004d8999954e0a28000ab000ab0000005127904500014e5d5158d5544ac13a02d000a10331af3ac000d420e45a3800004534c278000002880007f1db54ab09352804a04d45b12c24a055291a54828c4fb97854c5315e03a406a3cea06130c99d0b9d7000a1c73000000800f00a23aa0004a8f5106000a40d6000000000261a8000769220200cc4720c0cab14171c818204d1f9e82920016207310c344221f5000514fe84b52636c5f0df51817c3e1ff06c00c002324feaa89d02b2c29b92317948008925963000270e19e530a8b8940062460c08c17a43600009283078a354eabf4f8764dc29104a9e4cd8603a0000b680020a0009912d0000000001e2b20000027d000abc1792a0000000017232e8e10425d4ee67d0280a20c164a08850002e12b1915520002624a478000618
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x18c00a2c00a30000000499a8868080000160007127a4000000d8203252a000b80038380000eb44030410400010830382a1264a8865c25093254032a52e02928498d4970149324c68b3a6ca98863515c8544c431aa2e02a26218f0552509310c616b90c8a80638519131540319c2e03126290f05535092108790a1242a80438554e6190c40a4ce321aa42060e6354a411030b31aa320881851516190d3083aec2a662984c9731814248270b88c0a1241625cc6050920b42e230284904a8765093048294bae8490041c254f4248020e4684a8a40106145458e414421abb0a918a214a1d54248110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4000905829d3654c431a05821913154031
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
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
  | 6 => packedAt s5K6 (756+((h/14+packedAt s5K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s5K5 (22295+((h/245+packedAt s5K5 (19845+(h % 245)*10) 10) % 971)*11) 11
  | 4 => packedAt s5K4 (29426+((h/237+packedAt s5K4 (27056+(h % 237)*10) 10) % 940)*11) 11
  | 3 => packedAt s5K3 (1530+((h/10+packedAt s5K3 (1470+(h % 10)*6) 6) % 52)*6) 6
  | 2 => packedAt s5K2 (123+((h/1+packedAt s5K2 (120+(h % 1)*3) 3) % 7)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc79fe3fff0f1ff8fc31c7c7ff1c3fe1f04f1cf
  | 1 => 0x7e1fc78ff01c7f1fc1f8f8e1e038fe73b4933
  | 2 => 0xf801ff80fffe07fe3fe00ff01ffc0ff8c38e3c
  | 3 => 0xfffe0000fffff8003ffff0001ffff000fc0fc0
  | 4 => 0xffffffff000000003fffffffe0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40802000100200100000101200408200001045
  | 1 => 0x310c491122248b020c0c8484520924c6194912
  | 2 => 0x80508022444014005120092084900910428228
  | 3 => 0x12041a5488a10124a6552001192a6042ac0d80
  | 4 => 0x245913600ec9a6493b9a4e49c0304194f7e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8feeafae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36266
namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x7019e078d0e8000000901169e94000a089a821d9714899b80919c920480129896040d9c028000191f03059b05001f800b1d038f1980208817958a9a108c138e132006110c8f9006800b80001500001803881e08202060040110106850004081161400001ffd5007fe5401ff55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05fe43017f50c05fc4301ffd48077f5200ff94807fd52005f54803fc52007fd0801bf4200ff90801fd42006f50803fc42017fcc803fe32017f4c803fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50007fd0001fe40007f50001fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x222000efd91100057ec888003fe64440137f3222000ff59110005fac888003fc64440137e3222000ef1911000578c888033ff5444019ff2a2200cff55110067f8a88802fff63440177fb1a200bff98d10015fcc68802ffd63440177eb1a200bff18d10015f8c68802fff5344017bfa9a200bff94d1005ffaa68802f7d5344017fe29a200bffd0d1005ffc868802ffd4344017fe21a2000ffd8910005fec48802bfe62440037f3122000ff58910005fac48802bfc62440037e312200cffd4910066fea48802bfe5244019fea922000df54910057f8a488003ff4244001dfa12200aff90910007fa8488003bd4244015fe212200bffcc910057fc648802ffd3244015fe192200cffd4510027fca288033f65144019fea8a200cfd54510027f8a288003ff4144009ff20a2000fd90510007fa8288003f54144009fe20a200bffcc510027fc628802ff63144017fe98a200bfd4c510027f8628802bff2144009ff10a2000fd88510007fa4288003f52144009fe10a200cffd411002ffca088033fd504400bfe2822000ffd011002ffc8088003fd404400bfe202200bffcc11002ffc608802ffd304400bfe182200affc811002ffc4088003fa2044001fe9022000fe4811002ff84088013ff1044009fd8822005ff8411002fec2088017ff650400b7fb282005ff9941001dfcca080177e65040073f3282005ff59410045faca080177d65040013eb282005ff1941002df8ca08017ff640400b7fb202005ff9901004dfcc808017be64040015f3202005ff59010005fac808017bd64040015eb202005ff1901002df8c808023ff5404011ff2a02008ff55010047f8a808017ff630400b7fb182005ff98c10015fcc608017de63040056f3182005ff58c1003dfac608017dd63040016eb182005ff18c1002df8c60801fff530400fbfa982007ff94c1003ffaa60801f7d530400ffe2982007ffd0c1003ffc860801ffd430400ffe2182005ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd62040017eb102005fb58810005dac408017fc620400b7e3102008ffd4810046fea40801bfe5204011fea902000df54810037f8a408003ff4204001dfa102006ff90810007fa8408003bd420400dfe2102007ffcc810037fc640801ffd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802004fe44010
  | 1 => 0x7fe204800bf71024005ff0812002fd84090007f82048009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2012bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc988026fe64c4009feb262000bf59310027f8c988012fc64c4025ffaa62012ff95310097faa98804bfc54c4009ffb1e2004bfd8f10027fcc78800afe63c4009feb1e2011bf58f10027f8c788012fc63c4023ffa9e2011dfd4f1008ffca788047fd53c4023bea9e2011ff14f1008ffe8788047fe43c4023fea1e2011ff10f10027fec588012ff62c4009ff3162001bf98b10027fac588002fd62c4009fe3162004bf18b10097fea58804b7f52c4021ff2962012ff54b10006faa588043fc52c4001ffa162000efd0b10087fc8588003fd42c4001dea162010ff10b1008ffe6588043fe32c4023fe9962010ff0cb10027fea388013fe51c4009fb28e2004ff54710097eaa388013fc51c4009ffa0e2004ff90710027ec8388013fd41c4001faa0e2004ff10710027fe6388013fe31c4009fb18e2004ff4c71008fea6388013fc31c4009ff90e2004ff88710027ec4388013fd21c4001fa90e2004ff08710097fea188017fe50c4025fea862005ff14310007fe8188017fe40c4001fea062005ff1031008ffe6188017fe30c4023fe9862005ff0c310087fe4188017fe20c4001fe9062005ff0831002ffecb08016ff658400bff32c2003bf9961002ffacb0803efd658400bfe32c2005bf1961002ffec908016ff648400bff3242009bf9921002ffac908002fd648400bfe3242005bf1921007ffea90803ffe548401ffeaa4200fff1521002ffec708016ff638400bff31c2002bf98e1002ffac70803afd638400bfe31c2005bf18e10077fea70803b7f538401dff29c200eff54e10076faa70803bfc538401dffa1c200eff90e10077fa870803bfc438400bffb142005bfd8a1002ffcc508006fe628400bfeb142000bf58a1002ff8c508016fc628401fffa94200fdfd4a1006ffca50803ffd5284001bea94200dff14a10007fe8508003bf428401bff2142000ff50a100077a8508037fc428401dff994200dff8ca10077fa6508037fc32840177eb0c200fffd4610027fca30803ffd5184009fe28c2000ffd0610027fc8308003fd4184009fe20c200effcc610027fc630803bfd3184009fe18c200dffc8610027fc4308003fd2184009fe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfea042005ff1021002ffe6108017fe308400bfe9842005ff0c21002ffe4108017fe208400bfd1042005ff48210007f24108017fc208400bff8842005fdc4210027f62108033ff65440197fb2a2000dfd9510004feca88033fe65440077f32a200cff59510065faca88033fc65440077e32a200cdf1951001cf8ca88003ff64440017fb
  | 2 => 0x40007fa422005ffc211000b7f3008005ffd404002ffca020017fd501000bfe2808005ffd004002f7e8020017fe401000bfd2008005ff5004002f7a8020027f9401000bff9808005ff8c04002ffa6020017fc301000bff9008005ff0804002ffecb10016ff658800bff32c4003bf9962002ffacb1005afd658800bfe32c4005bf1962002ffec910016ff648800bff3244009bf9922002ffac910002fd648800bfe3244005bf192200b7fea91005bfe548802dfeaa44016ff1522002ffec710016ff638800bff31c4002bf98e2002ffac710056fd638800bfe31c4005bf18e200affea7100577f538802bff29c4015ff54e200aefaa710057fc538802bffa1c4015ff90e200affa8710057fc43880037eb144001ffd4a2000efea510007fe5288003fea944001df54a2000ff8a510007ff4288003dfa144001ff90a2000ffa8510007bd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944005ffd862002ffcc310012fe618800bfeb0c4000bf5862002ff8c31005bff518802dff28c4016ff546200b7f8a310003ff4188001ff20c4000ff50620007f88310057ff318802bff18c4015ff4c6200aff86310007ff2188003ff10c4001ff4862000ff84310016fe608800bffa844005ff9422002ffaa110017fc508800bffa044005ff9022002ffa8110017fc408800bff9844005ff8c22002ff46110017fd308802bfc9844005ff0c22002ffe4110017ef2088003fd9044005ff0822002ff04110053ff65480297fb2a4014ff9952001dfcca90053fd65480297eb2a4014ff1952001df8ca90003ff64480017fb224000ff9912004dfcc890003fd64480017eb224000ff1912004df8c890053ff5448029ff2a24014ff551200a7f8a89004fff63480277fb1a4013ff98d20015fcc69004ffd63480277eb1a4013ff18d20015f8c69004fff5348027bfa9a4013ff94d2009ffaa69004f7d5348027fe29a4013ffd0d2009ffc869004ffd4348027fe21a4005bfd892000ffea4900077f5248003ff2924001fb9492000ffaa4900077d5248029f6a924000db5492000ff8a490007ff4248003dfa124001ff9092000fdc8490007fd4248003dea124000fb509200075a8490007fc4248003ff9924001ff8c92000fdc6490007fd3248027f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290012fc6148029ffa8a4014ff945200a7faa290053fc5148001ffa0a4000ff90520007fa8290003fc4148027ff98a4013ff8c52009ffa629004ffc3148003ff90a4001fbc852000ffc4290007fd2148001f690a4001ff0852000dfec090053ff504800bff2824014ff5412002ff8a090003ff404800bff2024000ff5012002ff8809004fff304800bff1824013fe8c12009ffa609004ff9304800bfe1824001ffc812000ff6409001
  | 3 => 0xf28c801fff546400fff8a320027ff4190001ff20c8000ef90640007fa8320027fc4190001de20c801effcc6400f7fc632007bfd319003dfe18c801dffc8640007fc4320003fd219003bfe10c8005bf9824002ffea120017fe509000bfea848005ff1424002ffe8120017bf4090013fda048005ffcc24002ffc6120017fd309000bfe1848005ffc824002ff84120073ff65500397fb2a8000dfd9540004fecaa0073fe65500077f32a801cff595400e5facaa0073fc65500077e32a801cdf1954001cf8caa0073ff5450013ff2a2801cef951400e7faa8a0073bd5450013fe2a2801bffd8d400ddfec6a006ffe63500057f31a801bff58d400ddfac6a006ffc63500057e31a801bffd4d400defea6a006ffe5350037fea9a801bdf54d400dff8a6a0027ff4350037dfa1a801bff90d400dffa86a006fbd4350013fe21a8000ffd8940005fec4a006bfe62500037f3128000ff589400d7f8c4a0006fc6250039ffa92801cdfd49400d7fca4a0073fd5250001bea92801aff1494004ffe84a0003bf4250035ff2128000ff509400077a84a0027fc4250037ff992801aff8c9400dffa64a006bfc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8004bf185400e7fea2a0073fe5150039fea8a801cff1454004ffe82a0003bf4150001ff20a8000ff505400077a82a0027fc4150037ff98a801bff8c5400dffa62a006ffc3150035ff90a8000ff88540007fa42a006bfc2150039ffa828005ff941400e7faa0a0017fc5050013ffa028009fed014002ffc80a0017be4050037ff9828005ff8c1400dffa60a0017fc3050035ff9028005ff0814002ffeca20016ff651000bff3288003bf9944002efcca2000e7e651000bfeb288019bf5944002efaca200027d651000bfe3288005bf1944004dfcc820027ff5410013ff2a08009ff5504004ff8a820017ff631000b7fb188005ff98c40015fcc620017de63100056f3188005ff58c400c5fac620017dd63100016eb188005ff18c4002df8c620063ff5310031bfa988018ff94c400c7faa6200637d5310031fe2988009ffd0c4004ffc8620027fd4310013fe2188005ffd884002ffcc420006fe621000bf73108001bb9884002ffac420002fd621000bf6b108000bb5884002ff8c420016fc6210033ffa908019dfd48400bffca420067fd5210001bea908017ff1484004ffe8420027bf4210013ff2108009ff508400077a8420027fc4210031ff9908017ff8c8400c7fa642005ffc321000bffb088005ff98440025fcc220017f661100017b3088005ff58440005fac220017f561100017ab088005ff184400cffea220067fe5110033fea888019ff1444004ffe8220027fe4110001df2088009ff5044004ff88220027bc4110031ff9888018ff8c4400c7fa6220063fc311002fff9088000ff884
  | 4 => 0x88efd6348447fe31a4202bf18d2111ffea69088f7f5348447ff29a4223ff54d2111efaa69088ffc5348447ffa1a4223ff90d2111ffa869088ffc43484097fb124201ffd492100efea490807fe5248403fea924201df5492100ff8a490807ff4248403dfa124201ff9092100ffa8490807bd4248403fe2124201ffcc92100ffc6490807fd3248403fe1924201bfd8521127fea290813fe5148449fea8a4204ff14521007fe8290813fe4148401fea0a4204ff1052111ffe6290813fe3148447fb18a4223ff4c52111fea6290813fc3148403ff90a4201fdc8521027fc4290813ee2148409fe10a4204fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc604840b7e3024224ffd4121127fca090893fd5048449fe2824223ffcc12111ffc609088ffd3048447fe1824201ffc812100fde4090807fc2048413ffb2e8009bfd974004ffccba000efe65d0013feb2e8022bf5974004ff8cba0026fc65d0013ffaa68009ff9534004f7ca9a0027fd54d0045deaa68009ff1534004ffec7a0026ff63d0013ff31e8002bf98f4004ffac7a0086fd63d0013fe31e8002bf18f4010ffea7a00877f53d0043ff29e8021ff54f4010efaa7a0087fc53d0013ffa1e8009efd0f4004ffc87a0027fd43d0043dea1e8009ff10f4004ffec5a0027fe62d00037f3168009ff58b40005fac5a0027fc62d00037e3168022ffd4b40116fea5a0083fe52d0045fea968000df54b40107f8a5a0027ff42d0013dfa168009ff90b4004ffa85a0003bd42d0013fe2168021ffccb40107fc65a0087fd32d0041fe1968009ffd874004ffcc3a0012fe61d0013feb0e8000bf5874004ff8c3a008bff51d0045ff28e8022ff54740117f8a3a0027ff41d0013dfa0e8009ff9074004ffa83a0003bd41d0013fe20e8021ffcc74010ffc63a0087fd31d0043fe18e8020ffc8740007fc43a0003fd21d0041fe10e8022ffd434002ffca1a008bfd50d000bfe2868021ffcc34002ffc61a0087fd30d000bfe1868020ffc834002ff841a0017ff659000b7fb2c8005ff9964001dfccb20017fd659003f7eb2c8005ff1964002df8cb2006efd649003fffaa48009ff952400fffaa920027fc549000bffb1c8005bfd8e4002ffcc72000afe639000bfeb1c801ebf58e4002ff8c720016fc639003dffa9c801edfd4e400f7fca72007bfd539003dbea9c801eff14e4004ffe872007bfe439003dfea1c8009ff10e4002ffec520017fe62900037f3148005ff58a40005fac520017fc629000b7e314801fffd4a400fefea520077fe529003ffea948000df54a400eff8a520027ff4290001dfa14801dff90a40007fa8520003bd4290013fe214801effcca400effc652007bfd329003bfe1948005ffd864002ffcc320012fe619000bfeb0c8000bf5864002ff8c32007fff519003ff
  | 5 => 0x814102df8c0a08b3ff5050459ff282822cff54141167f8a0a08afff3050457ff182822bff4c14115ff860a08abff2050455fe1028204ffd9441025feca20813fe65104077f3288204ff5944114dfaca20813fc65104097e3288209bf9904104ffea820827fe5410413df2a08209ff5504114f7aa820827fc5410409ffb188204bfd8c41027fcc62080afe6310409feb188228bf58c41027f8c620812fc6310451ffa988228dfd4c41147fca6208a3fd5310451bea988228ff14c4104ffe8620827bf4310413ff2188209ff50c411477a8620827fc4310409ffb108204ff9884100dfcc420813fd62104017eb108204ff18841025f8c4208a7ff5210453bfa908227ff9484114ffaa4208037d521044ffe2908209ffd084104f7e8420827fe4210413fea108200ef5084104ff884208a3ff321044fff1908228ff4c84113ff86420812fe6110409ffa888204ff94441027faa220813fc5110409ffa088204efd0441027fc8220813f64110409fea088204ef5044104fea8220813ff3110409ff1888204fd8c441027fa62208a3f53110409fe1888204ffc8441027f84220813ff6010409ff3008205bf98041027fac020802fd6010409fe3008229ffd404114ffca0208a7fd5010453fe2808228ffcc041147fc60208a3fd3010451fe1808227ffc804113ff84020813ff65884097fb2c4204ff9962101dfccb10813fd658844d7eb2c4204ff19621025f8cb10813ff64884097fb244204ff9922104dfcc910813fd64884017eb244204ff19221025f8c91089bff548844dff2a44226ff55221137f8a910813ff63884097fb1c4204ff98e21015fcc710813fd638844b7eb1c4204ff18e21025f8c710897ff538844bbfa9c4225ff94e2112ffaa7108977d538844bfe29c4225ffd0e2112ffc8710897fd438844bfe21c4201bf58a2100ffea5108077f5288403ff2944201ff54a2100efaa510807fc5288403ffa144201efd0a2100ffc8510807fd4288403dea144201ff10a2100ffe6510807fe3288403fe9944201ff0ca21025fcc310813ff5188409ff28c4204ff54621027f8a310813ff4188409ff20c4204ff50621027f88310813ff3188409ff18c4204fd8c621027fa6310897f53188409fe18c4204ffc8621027de4310807f72188409fe10c4204fd08621027fec110813fe608840b7f3044204ff58221005fac110813fc608844dffa844226ff94221137faa11089bfc508844bff9844225ff8c22112ffa6110897fc3088403ff9044201ff08221127feca90892ff6548449ff32a4203bf99521127faca90892fd6548449fe32a4203bf19521007fec890802ff6448401ff3224209bf99121007fac890802fd6448401fe3224209bf19121127fea890893fe5448449feaa24224ff1512111ffec69088eff6348447ff31a4202bf98d2111ffac690
  | 6 => 0x3ff21e8209ff50f4104ff887a0827ff62d0413ff3168201bf98b4104ffac5a0802fd62d0413fe3168201bf18b41197fea5a08cb7f52d0461ff2968232ff54b41006faa5a08c3fc52d0413ffa168209efd0b4104ffc85a0827fd42d0401dea168209ff10b4118ffe65a08c3fe32d0463fe9968230ff0cb41197fea3a0813fe51d0465fea8e8204ff1474118ffe63a0813fe31d0463fb18e8231ff4c74118fea63a0813fc31d0461ff90e8204ff0874104ffec1a0827fe60d040b7f3068209ff58341005fac1a0827fc60d0465ffa868232ff94341197faa1a08cbfc50d0463ff9868231ff8c34118ffa61a08c7fc30d0461ff9068230ff08341027fecb20812ff6590409ff32c8203bf99641026fccb2080e7e6590409feb2c822fbf59641026facb208027d6590409fe32c8204bf1964115dfac9208bfff5490413ff2a4822fef9524117ffaa9208bfbd5490413fe2a48204ffd8e41025fec720813fe63904057f31c8204f798e41015bcc720813fd639045d7eb1c8204f758e41005bac720813fc63904097e31c822effd4e41176fea7208bbfe539045dfea9c822edf54e41177f8a720827ff439045ddfa1c822eff90e41177fa87208bbbd4390413fe21c8204ffd8a41027fcc520806fe6290409feb148200bf58a41027f8c520812fc629045fffa94822fdfd4a4116ffca5208bffd5290401bea94822dff14a4104ffe8520803bf429045bff2148200ff50a410077a8520827fc429045dff994822dff8ca41177fa65208b7fc32904097f30c8204ffd4641027fca320813fd5190409fe28c8204ffd06410277e8320827f74190409ff98c8204ff8c641027fa6320813fc3190409ff90c8204ff08641027fec120813fe609040b7f3048204ff58241005fac120813fc609045fffa84822fff9424117ffaa1208bffc509045dff984822eff8c241177fa61208bbfc309045bff904822dff08241167fecaa08b2ff6550459ff32a8203bf99541167facaa08b2fd6550459fe32a8203bf19541167fea8a0827fe5450459feaa28209ff1514115ffec6a08aeff6350457ff31a8202bf98d4115ffac6a08aefd6350457fe31a8202bf18d4115ffea6a08af7f5350457ff29a822bff54d4115efaa6a08affc5350413ffa1a822bff90d4115ffa86a0827fc4350401ffb128200bfd8941157fcc4a0806fe6250401feb12822aff1894100df8c4a08b3ff5250459bfa92822aff94941167faa4a08037d5250455fe2928209ffd09410077e84a08abfe4250401fea128200ef5094104ff884a08afff3250455ff192822bff4c941157f864a08b3ff5150409ff28a822cff54541027f8a2a0827ff4150413fba0a8204ff905410277c82a08afff3150409ff18a822bff4c541027f862a08abff2150409fe10a8200ffd8141005fec0a0803fe6050401feb028200ff1
  | 7 => 0xa10d73f53d086bdf29e8435ef54f421ae7aa7a10d7bc53d08035eb168401efd4b4200e7ea5a1007be52d0803dea968401cf54b4200f78a5a1007bf32d0803df1968401ef4cb4200f7865a1027bf61d0801df30e8400ef5874204f78c3a10dbbf51d086ddf28e8436ef547421b778a3a10d7bf31d086bdf18e8435ef4c7421af7863a1007bf21d0803de10e8409efd83420077cc1a1003bd60d0813de3068436efd43421b77ca1a10dbbd50d086dde2868435efcc3421af7c61a10d7bd30d086bde1868401efc834200f7841a10d3ff65508697fb2a8434ff9954201dfccaa10d3fd65508697eb2a8434ff1954201df8caa1006ff6450869ffaa28434efd514204ffca8a10d3be5450869feaa28434ef5514204ff8a8a10d3bc5450867ffb1a8433bfd8d4219ffcc6a100afe6350867feb1a8433bf58d4219ff8c6a100afc6350867ffa9a8433dfd4d4219ffca6a10cffd5350867bea9a8433ff14d4204ffe86a10cfbf4350867ff21a8433ef90d4219ffa86a10cfbd4350813fe21a8433ef10d4200dfec4a1007ff5250803bfa928401ff9494200ffaa4a10077d5250803fe2928401ffd094204fde84a1007fe4250803df2128401ff1094200f7884a1007ec4250803ff9928401ff8c94200ffa64a1007fc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8404bf185421a7fea2a10d3fe5150869fea8a8434ff1454219ffe62a10cffe3150867fe98a8433ff0c54200ffe42a1007fc2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028405bf181421a7fea0a10d3fe5050869fea828434ff1414219ffe60a10cffe3050867fe9828433ff0c14200ffe40a1007ef2050803fe1028434efd95421a77ccaa10d3bd6550869de32a8433efd8d4219f7cc6a10cfbd6350867de31a8433efd4d4219e7ea6a10cfbe5350867dea9a8433cf54d4219f78a6a1007bf62508035fb128400ebd894200f7ea4a10073f5250803df2928401ef5494200e7aa4a1007bc5250803df9928401ef8c94200f7a64a1007bc3250801dfb0a8400ef985420077ac2a1003bc6150869dfa8a8434ef945421a77aa2a10d3bc5150867df98a8433ef8c54219f7a62a10cfbc3150803df90a8401ef085420077ec0a1003be6050801deb028400ef181421a77ea0a10d3be5050869dea828434ef1414219f7e60a10cfbe3050867de9828433ef0c14200f7e40a1007af2050803de1028409ffd974104dfecba0827fe65d04077f32e8209df9974101cfccba0827fd65d04657eb2e8209df59741004facba0827fc65d04137e32e8209ffd534104ffca9a0827fd54d0413fe2a68209ffd8f4104dfec7a0827fe63d04057f31e8209ff58f4118dfac7a0827fc63d04057e31e8231ffd4f4118efea7a08c7fe53d0463fea9e8231df54f4118ff8a7a0827ff43d041
  | 8 => 0x580900001100680280100000000500a00000900000080000080080080380080600080000300900000000000000480100b00280d80100200000980e00500380180800200080280500080400280080280600280080080080300080100780000000a80480200180180000100500380881e81300380300801200a00000000000080280000580000700300000100002b80081380b00b80280500601100400280300000801d00f80000480502280100000000280a80200080400200180080080600180002300100180080000000000000080080600080980000000b00e80000f00180680080580000000800100700000200001700300100080100000000080600280000580001000080000580000200100080700500000000080600181c00100000180480500180401600b83300280a00400181880000a00000100080000480282100b80100b80000000080680200300180000000080080e00000380080000200e00500100580f80880280000100001080100000080000c8010028050037f6454801bf322a400df59152006f8c8a90df7f635486f3fb1aa437df98d521befac6a90de7d635486fbe31aa437dfd0d521befc86a90df7d435486fbe21aa401dfd895200cfec4a900f6f6254803bf212a401df1095200efe64a90077e3254803be992a401df0c952006fec2a90037e6154801beb0aa400df185521befe62a90df7e315486fbe98aa437df0c55200efe42a90077c2154801bfb02a400df98152006fac0a90037c605486fbf982a437df8c1521befa60a90df7c3054803bf902a401dbc815200ef840a9027ff65d08137fb2e8409ff9974201dfccba1027fd65d086d7eb2e8409ff1974204df8cba1006fe64d0813ffaa68436efd534204ffca9a1027be54d0813feaa68436ef5534204ff8a9a1027bc54d0813ffb1e8409bfd8f4204ffcc7a100afe63d0813feb1e8435bf58f4204ff8c7a100afc63d086bffa9e8435dfd4f421affca7a10d7fd53d086bbea9e8435ff14f4204ffe87a1027bf43d0813ff21e8435ef90f4204ffa87a10d7bd43d0813fe21e8409ef10f4200dfac5a1007ff52d0803bfa968401ff94b4200ffaa5a10077d52d0803fe2968401ff90b4200f7c85a1007ee42d0803fe2168401ef10b4200ffe65a1007fe32d0803fe9968401ff0cb4204ffec3a1027fe61d08097f30e8409ff58742005fac3a1027fc61d086dffa8e8436ff947421b7faa3a10dbfc51d086bff98e8435ff8c7421affa63a10d7fc31d0803ff90e8401ff0874204ffec1a1027fe60d080b7f3068409ff58342005fac1a1027fc60d086dffa868436ff943421b7faa1a10dbfc50d086bff9868435ff8c3421affa61a10d7fc30d0803ff9068401ff0834204f7ecba10dbbe65d086ddeb2e8409ef1974204f7ec7a10d7be63d086bdeb1e8409ef18f421af7ea7
  | 9 => 0x700018b00005239c4304420004592a800045100000000000070f5ec0004386242c10d81591e71b05e20000752f400000035a51f12d09d37c0003a26c735030200000055b06e3d900000073c5300003756d36681970006d90632960006f937d6476e23cc0000000004604417001585f568e33b5cd6de3423982ed3a438b15d36f01219975c2f71c215c2a92a12d56f86105fd0cb0000000004d20710007730000004000001c10003c05e51d90006e12680c826d28400000000000000071600031200020d09431a0001f808101c00000027e0002f00006603da0001e80ac7182310005af61f00000000046437128730c0170275713774393cf1a52c23e06a733732843146234b6742a60000000000001873c300060e74435d0192b26820001f53e527756163e00000060a0004584d530d0000310002a04227582105843eb06500042523b04b2c03166fc71f0006d43ef7122d100000052b0005d652c3ec3bf00056373d0000006455e63c51c921c72070a0000006bb6ce2fc05043a35941e5b673a7177241601a82460f73d347a2381f91da44048100038400000314f5520001e93df65951501642a5c12a20f656a2eb10c00001f19a1f719865415026400000480000080500780980100680280080080100f00000100580500180000100000c80400000300580700a00300000000281400080000000800780000780500100080100000000680000600380781700080000080280300000080300080700980000401280600400000580200580880480180480a80000b00700780700001180380000180a80d00000780200380080180000280280180080000100000e80000a00780000480000400600280000000380480500000000080180600280100000380e00000180600d80000001600200080200100000900500000700480100000100100300100280c80380080080700000500000380880180000001d00000200080100280100b00080000480100002600000300780200501680100001880600180100200401b00700000180000000100380300280000000500004600000a80000380000080200a00080000000300401600700100280780700700800f80000e00000000380380080481000700380000280200000901600200d00002900680180080000000900001f80300100000080a00100102780980200080100203680300100300800180800100000b00000000080400000600180401801680680000001000000600b00e00580180000380000100480080f80001380801301400200d00000280200481180100080400080000080180100180380380000080100e80000000001280100080100200780000300881480502c8040038030178028098020018008028070000000040020008008050000030000098020030008038008028008000010008000018
  | 10 => 0x44c7520bc3050af12904c2e315e0ba0000000003f029e43d1a35292a53c21721851196027390f40c70002290ab60f00f2da17b57d6e80004a25c631f1285bb00039608070101375e0145c20004b932504e5456814ac36700022f2994e200022141b3946095046b63172e965a00041842b36e00000000005700006f59000018430800057c2653f363465e1cd6223902b71af3de2af2bd0a200076600047b0003340000006356c86d200005a22e30429c3d61c665c42859838728d00000023300005e2325853555d506009a1a124903926730a3313af52d69b7064c650b0380000003836b400000000026f40400056d0004a86a655053f5da00000044b1d26d02cf3583f12983e707913717400017c54600014926b5eb29f6f20000004724ce70d32428a2cd73676d09c43e4735fb2df0064aa1ce1dd1a22731360510be4cd1486535804362fa08716532054f01872e33250d0006170000005c776825c0000007385a300059145e00063c0002030072f55993b145a6e72bc2db18300000000004d6a36d80000006dc0005332b817d0004d40003c96a51f14b626c00065b00c06d6a91a727966c4d108616a15244951b5a249f4610fb66d1ad34400073e0000005477562377096fd2856ac0260294fa0ef2e71df33d00062d74b5765be0001e01ca6da3951d50c45403e64e03ac2245d319256c3536312660492081050214791e556751427608516472a74803770722a60400000028b47d08a08900061819011074f0000c60005365000da6441d316c00076064a6b562518859a00054847842469624d1024d72455654a94634a05922404c000000046c3330000db2cc40800075d0000224652fb4010004c765265713054e20c5c52160d250c00018272d46f5893b833006a0e555a25b26211a00000017e0005735d17151455084eb53939b3b74ca3ca1f220239d2e24bc2ce48d67649e4684290b449061b1531c01e628e4e85583d765559b19c71014455c2d85873a06053605a136132a2f36b973f0ff4882416a41080006651754a55ea04f19e1de77507a00058c5a800000b4e12112076264130000003ea4f933a03005837b0b70004146150006690705f372b71300014b08d4ad0c90005b028c2c43a91064bd6863ad67e3ff2fe20000016d48942f54d2ff14114a2d400033c07b0615ad54900068d24c0c50dd2286ca63069538c3bb6c43e24e32ae00008261162303a74e7471404370736a04020b50006c35a00002912923cb5fc00076525400059c3d811b00052638d12f6f020e2d60002150a34c30a530b28016f6dd27c18d00013900019100034a15a00000048261c3fd25d4fb20b5ef1130f06971b25ae3294ba3e15e109b08e5cf46e3651380c134d0000b33706160003510000004550000005234974da65d24a4175794c94f213e18f2c60002e635
  | 11 => 0xb4c24cb00000072f0004e54fe3526bc1c431b39700019603c0007720423c711149240e6363f227123421f44e5773a53e327420418066b00019d0354b46b04ed1e22d20002bb0006513496426cd3fa64d6806fa5fe41225a09673119f6fb1c37345370002b32430002c77635cc0eb3362095fa76e3c866a2501c76bf1c816b6ea15f00000043220600000000058a0905e44356505420fa74112b2e50000004435d946752f06b2d04740006c25110842596886d516875f42d0003d149d0000002e102d6294cf18c00048b44a6db13112302508349329546b2d75184e609e32f0000005601b72124f86e663a18e4ab73203e72230e49c05b64954b1224ee5592aa5223ab53d5942253f82f266466e1fb6e30f901b0a70000000000003b518a42e68b34c00047f00062b0005833dc6b11513aa2514f76431b32440ce69419553a18102e27b07e7645b55701274c50002f150f52e04400068941a67c0000000f81267040001790340096ae59e2c30fc60c49435c63d27058e68a6f36a87570fd3721cc23a13301e6f41b11a42ad35b36400053862a73041c6614e748008b58d5a941100034648c2471b80006934ef1932484270d02054065816f70470b209f0d95c837f43c25825264f0ea05401a0a826e70c0456cb1bf0003e81dc0d413f2f900076f71464037a02058b00071b4b300062726a30f55f7216c12f86855c362c5b163805923d75a1e45165ac4d80b154c40a1210001736be28969c26067372c62e61276b74c69803349565f0051d731c54428805f5bf1fa64e68c2260e47544764f020100067d4f623949b4ff02f3624b05e72a34d638a3a776925e56828348571a56e0ed23f5df5de4b81017536af4561ef2ef6145b437300059f74a00a0002786775a61d83805012b44dd00000000000000002800055659739255d4a31320a92ec48f00000034f0a10ee0000e20005056ee2575b96b816962f0003000026284a100045f0006203894873793474bf0005c90f525340c6920922365020cf00032731000014734100060300055310f32e74d3c131d1a90d667a0e87022273685b20003264f51636991122932c95746f61466713191571bd49a6ef4774092bf0aa71c10a2e40b05032b547c69d3be6ab6663ce2a40001f022212049607f00015612e0004f146600006c4bb19b0003813741716463f40000000000970000003935cb36d46d0000007670000000460005e800000000000000001158f00046a4c80002be3400bf0003dd17a0005d84265130002752cb3a610b00000000051e0915db0006130006910000001aa0006080000000bd0000000000d709974900038231e3112ea4df3884ea62100043369a5aa2b66cf0e02ac3bc39f7372303c40004030105f256b2de31576a25f06946952a0006673d04195f40006d65d753e1b534522300036b
  | 12 => 0x57e00000057f0005b84b14d900014e0006ff56f2556191552f60626e00f111444851c48e1d06ad3ed6413db16e4fd40f01d4866d13b007475542335e3215ed6d75d46372ee4464e94c15691760000005c40003fb17842c3b400023e4536481bb43b18667f4a71611256df1eb23572875b6cc0775575ca0cd06703f6781b928645d49850a43f21408870b1f43e95a57192b95dd19463f1240325353566623fe4f30fe3b27742b023c53b61a54374307c04a1ea76121a75941f1db4545c02e013d7055100081ab47552502a4de56211f10d00073b6390935dc2c81b45a721b4d01701154ae00032d52827d6f128120f7114504105196a205528f6561d152157553258864b00000050605d0000dc0766585ba0e90000a44835f622b11e5414be5543910000000005780d326325671e08f1ed0e670e5b74db0646c00000000413ee24e3fc1f670804803b00024b35f1ba50e4f46ed68f4fc3180c366f37857b55155e70367b1ae5936796b24c40ad76c1d45d26840724993f90e31677765bd1ec1547293662724a65965661fd2612dc2181ff17f7250043692fd2135e01a069e2ca33f60153113b2dd5096ba1161cf6834ec5a449161e0b853c10e0ca5f008c14d21e14c0985b335433e0006c91d62ab6bd5243765f774213a4471040000000003f500077127a0004b56720000000e121913c2902d97462690de51a10071d6906f531430672639a00000003d0007700956005ab4a42e81ee6a13850661f35203b93ba63b0003f700011743427f11d0b60e71434070003d40d53a15646870000003135075d05820005276ec0000f200000030300000029a41d6e514200039e00054a0001ac0000000001bc6b70000001070433397351a60006b31fc3635bc4d344d36c0ae4150c200000e00063332b07d2a74af47e40540b4b73223ae5f81e312c6632973c60a62204e45725f157a10330141600069f6700003e460600d6aa00002336a12a44f6e900059d1092d32170000000000000002ba0004450d16fe5e90535ff61d0003090000004207510006c634800024215b02b6c500020a00059538e0000005f93d221d0ec0df0c03996eb63222d13538f72711c0404843bd28200045c0006e400045b22c0004dc0683350bb30729475038629d1894521187455860000005555121fe1660cc44440d3b33f60b91340a064c6757330001b637e1c50002c55ee0006070f30003430015ce24f72329b76247100000000060d01532c7403b651705c5341774570780564cc5e31be4701cb3a83d50362b13383a300016202448a3cd1e13230004b200034e42100051d02c0006
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe105881002eea105881002eed105881002ee51058810026e9105881002eec105881020d7f76548100067f76548100047f765481020e7e765481020d7d76548100067d76548100047d765481020e7c765481020e7f645481022e7e645481020f3e64548100063e64548100067d645481020f3d64548100063d645481020e7c64548102257f73548102257d735481020e7f63548101be7e635481020f5e63548101be5e635481021e7d635481020f5d63548100065d635481020e7c63548102157f72548100476f725481020e7f625481000e7e625481020f6e625481000e6e62548100367d625481020f6d62548100066d625481000e7c62548102067e615481020e7e605481020f6f205481020f6d205481020f77105481020f7a105481020f75105481020779105481004cff76d081002cfe76d0810004fd76d081002cfc76d08101b67e65d08100067d65d08101d6bf64d081004ebe64d0810006bd64d081004ebc64d08101aede63d0810006dd63d081000eee62d0810006ed62d08101d5bf76d081004ebf76d081004cbf76d08101d6be76d08101d5bd76d0810006bd76d0810004bd76d081004ebc76d08101d6bf65d08101b6be65d08101d73e65d08101b63e65d08101febd65d08101d73d65d08100063d65d08101d6bc65d08101d6bf63d08101aebe63d08101d79e63d08101ae9e63d08101f6bd63d08101d79d63d08100069d63d08101d6bc63d08101f73f53d08101f73d53d08101cdbd72d08101d6bf62d081000ebe62d08101d7ae62d081000eae62d0810036bd62d08101d7ad62d0810006ad62d081000ebc62d08100373f52d08100373d52d08101eebe61d08101d6be60d08101d7b710d08101d7ba10d08101d7b510d08101efb910d0810004ff765081002cfe7650810004fd765081002cfc76508101a67e65508100067d65508101cebf645081004ebe6450810006bd645081004ebc645081019ede6350810006dd635081000eee6250810006ed6250810005f77150810025f471508101cdbf7650810006bf7650810004bf76508101cebe76508101cdbd7650810006bd7650810004bd76508101cebc76508101cebf65508101a6be65508101cf3e65508101a63e65508101e6bd65508101cf3d65508100063d65508101cebc65508101cebf635081019ebe63508101cf9e635081019e9e63508101debd63508101cf9d63508100069d63508101cebc63508101df3f53508101df3d53508101d5bf7250810007af72508101cebf625081000ebe62508101cfae625081000eae6250810036bd62508101cfad6250810006ad625081000ebc62508100373f52508100373d5250810007b771508101c7b471508101c6be61508101cebe60508101cfaf20508101cfad20508101cfb710508101cfba10508101cfb510508101c7b91050810
  | 1 => 0x8c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c10006dc5258c10006de4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002ede5058c1002edd5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ed71058c1002ede1058c1002edd1058c1002ed51058c1002edc1058c10004ff755881001cfe75588100067e755881001c7e7558810004fd75588100067d755881001cfc7558810004ff7458810006be7458810006bd745881004cfc7458810004ff7358810014fe7358810004fd7358810014fc73588100067f53588100067d535881002cff725881002eef72588100367f5258810006ef52588100066f5258810036ee5258810006ed5258810036ec5258810036ee4258810036ec4258810006ef3258810036ee3258810006ed3258810036ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec215881002cff705881002cfe705881002cfd705881002cfc705881002eee205881002eec205881002ef7105881002efa105881002ef51058810026f91058810006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002eee505881002eed505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002ee7105881002ee
  | 2 => 0x4ebc759901004ebf739901004ebe739901004ebd739901004ebc7399010006bf53990100063f5399010006be5399010006bd53990100063d5399010006bc539901004ebf729901004ebe729901004ebd7299010004bd729901004ebc7299010006bf52990100063f5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bd3299010006bc3299010026bf7199010026be7199010026bd7199010026bc7199010026bf5199010026be5199010026bd5199010026bc5199010026bf3199010026be3199010026bd3199010026bc3199010026bf2199010026be2199010026bd2199010026bc219901002ebf709901002ebe709901002ebd709901002ebc709901002ebf509901002ebe509901002ebd509901002ebc509901002ebf309901002ebe309901002ebd309901002ebc309901002ebf209901002ebe209901002ebd209901002ebc209901002ebf109901002ebe109901002ebd109901002ebc1099010004ff755901001cfe7559010004fd755901001cfc755901002cff745901002ebf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff7359010014fe7359010004fd7359010014fc73590100067f53590100067d5359010006bf4359010006be4359010006bd4359010006bc4359010004ff725901000cfe725901000cfc72590100067f5259010006be4259010006bc4259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc415901002cff705901002cfe705901002cfd705901002cfc705901002ebe405901002ebc405901002ef7105901002ef51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002ebe505901002ebd505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002eb7105901002ebe105901002ebd105901002eb5105901002ebc1059010006df7558c10006de7558c100065e7558c10006dd755
  | 3 => 0xf7650110004fd7650110024fc76501100057f75501100657c75501100067f65501100e67c6550110006bf645011004ebc6450110005f77150110025f47150110007b54150110005fa768811002efa76881100077b658811024f786588110007bb6488110007b86488110246fb6388110246f963881102477b5388110247795388110055f9728811000efa628811000ef862881100577b5288110057795288110057bb4288110057b9428811002ff37188110025fa718811002df8718811002ff0718811002efb618811002ff3618811024ff2518811024ff15188110007f24188110007f14188110247f23188110247f13188110057f22188110057f1218811000cff7648110054fd7648110024fc76481100067f65481100a67c6548110006bf6448110006bc6448110006ef624811000eec62481100076d5248110007ad4248110005f77148110025f47148110007e5214811002fe8204811002ff01048110025f8764811000ef87648110024f876481100077b654811023f786548110007bb6448110007b86448110236fb6348110236f963481102377b534811023779534811002dfb724811002feb7248110007eb624811000efa624811000ef86248110057e862481100577b5248110057ea524811005779524811023fe95248110007695248110057bb4248110057ea4248110057b94248110007e94248110007a94248110057ea3248110237e93248110007f37148110025fa7148110025f87148110007f0714811002efb614811002ff3614811023ff2514811023ff15148110007f24148110007f14148110237f23148110237f13148110057eb2148110057f22148110007e92148110057f12148110007e121481100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100047f72594100067e72594100067d72594100067c72594100067e42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941002e7f705941002e7e705941002e7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e77105941002e7e105941002e7d105941002e75105941002e7c105941004ebf759901004ebe759901004ebd7599010
  | 4 => 0x9102dfb53150910057af20509101c7bb10509101cfb6105091002cfe76d051002cfc76d05100657e75d05100057d75d05100067f65d05101967c65d0510006bf64d051004ebc64d051002dfa70d0510005f970d0510005f67690510026f67690510025f775905100277675905102d5f575905100277575905100057575905100077765905102bf7465905102a5f57490510007b7649051004ef6649051004ef46490510007b4649051004eb464905102bfb654905102bfb55490510025f77390510027d673905102cdf57390510027d57390510005d573905102c77753905102c77553905102c7b743905102c7b54390510005f572905102bf775290510007755290510007b74290510007b5429051002df6709051002df47090510026f76090510027f360905102b7b640905102b7b4409051002cfc76505100067f65505101667c6550510006bf645051004ebc6450510027b44150510005fb705051002df8705051002df4765051004ef4765051002cf476505102adf775505102adf57550510007776550510297746550510025f77450510027b77450510007b7645051004ef6645051004ef46450510007b464505102a5f773505102a5f5735051029f77535051029f755350510005f77250510297775250510007755250510007b74250510007b54250510007f3705051002df6705051002df47050510007f07050510026f76050510027f36050510005f67688510026f67688510025f7758851028df57588510007776588510287746588510025f77488510005f57488510007b76488510007b46488510025f7738851027df57388510276f76388510276f56388510277775388510277755388510055f5728851000ef6628851000ef46288510057775288510057755288510057b74288510057b54288510027f3708851002df6708851002df47088510027f07088510026f76088510027f3608851002cfc76485100067f65485101267c6548510006bf6448510006bc6448510006ef624851000eec6248510027e42148510005fb704851002df87048510027f0104851002df4764851000ef4764851002cf4764851026df7754851026df57548510007776548510267746548510005f77448510005f57448510007b76448510007b4644851025df7734851025df57348510256f76348510256f56348510257775348510257755348510025f77248510027e77248510007e7624851000ef6624851000ef46248510057e46248510057775248510057755248510057b74248510057b54248510007f3704851002df6704851002df47048510007f07048510026f76048510027f36048510057e72048510024fe76d0110024fc76d01100067f65d01101167c65d0110006bf64d011004ebc64d0110025f671d0110005f571d0110007b541d011004cf
  | 5 => 0x67f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df735891005ddc7358910056ec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891004cfc7458910006bc745891004cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc73589100067f53589100067d5358910054ff7258910006ef72589100567f525891006cff7158910006f77158910006f63158910006f53158910084ff7058910006fb70589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f64549100073f64549100063f645491022e7e64549100067d645491022e7c64549100073c64549100063c64549103057f73549103057d73549102fe7f63549101be7e63549102fe7d63549101be7c63549100557f72549100676f72549100567f625491000e7e62549100567d625491000e7c62549100077671549100077571549102ff7631549102ff7531549100576f20549102077b105491020f76105491004cff76d0910004fe76d0910004fd76d091004cfc76d09100067f65d09101b67c65d0910006bf64d091004ebe64d0910006bd64d091004ebc64d0910025f671d0910005f571d091004ebf76d0910005be76d0910006be76d0910004be76d0910006bd76d0910005bc76d091004ebc76d091004cbc76d09102f6bf65d09100073f65d09100063f65d09101b6be65d09102f6bd65d09101b6bc65d09102f73c65d09101b63c65d09102eebf63d09101aebe63d09102eebd63d09101aebc63d09102ef3f53d09102ef3d53d0910055bd72d0910056bf62d091000ebe62d0910056bd62d091000ebc62d09100573f52d09100573d52d0910007b671d0910007b571d09102f7b651d09102f7b551d09102efb631d09102efb531d09101efbb10d09101d7b610d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101a67c6550910006bf645091004ebe6450910006bd645091004ebc6450910006bf7650910005be7650910006be7650910004be7650910006bd7650910005bc7650910006bc7650910004bc76509102e6bf65509100073f65509100063f65509101a6be65509102e6bd65509101a6bc65509102e73c65509101a63c65509102debf635091019ebe63509102debd635091019ebc63509102df3f53509102df3d5350910055bf7250910007af7250910056bf625091000ebe6250910056bd625091000ebc62509100573f52509100573d5250910007b67150910007b571509102e7b651509102e7b551509102dfb6315
  | 6 => 0xe75991100057d75991100067f65991100067c6599110006bf64991100057f75591100657c75591100067f65591100067c6559110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110014fe7359110004fd7359110014fc73591100067f53591100067d5359110004ff725911000cfe725911000cfc72591100067f5259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911004ebe6419110006bd6419110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100073f53191100073d5319110005bd7219110006be6219110006bc62191100073f5219110007b57119110007b65119110007b55119110007b63119110007b53119110317bb101911030fb6101911030fb41019110317b8101911004ebf751911004ebe751911004ebd751911004ebc751911004ebf731911004ebe731911004ebd731911004ebc7319110006bf53191100063f5319110006be5319110006bd53191100063d5319110006bc531911004ebf721911004ebe721911004ebd7219110004bd721911004ebc7219110006bf52191100063f5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911004ebf711911004ebe711911004ebd711911004eb5711911004ebc7119110006bf5119110316be5119110006bd5119110316bc5119110006bf3119110316be3119110006b63119110006bd3119110006b53119110316bc3119110006bf2119110316be2119110316bc211911004ebf701911004ebe701911004ebd701911004ebc7019110006bf501911030ebe5019110006bd501911030ebc5019110006bf301911030ebe3019110006bd301911030ebc3019110006bf201911030ebe201911030ebc2019110316bf101911030ebe1019110006bd101911030ebc101911000cfe76d89100657c75d89100067f65d89100067c65d8910006bf64d8910006bc64d8910056ee62d8910004ff75d89100067f75d891001cfe75d8910004fd75d891001cfc75d89100067c75d891001c7c75d8910006bf74d891004cfe74d8910004fd74d8910006bc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d89100567f52d8910006ef32d8910056ec32d8910024fe71d891002cfd71d8910024fc71d8910006f631d8910006f531d8910056ef21d891002cfe70d8910024fd70d891002cfc70d8910056ef20d89100057f75589100657c7558910
  | 7 => 0x95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067e42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95103267f71d951032e7e71d95100667d71d951032e7c71d951032e7e41d951032e7c41d95100067f31d951032e7e31d95100067d31d951032e7c31d95100067f21d951032e7e21d951032e7c21d951032e7f70d95103267e70d95100667d70d95103267c70d95103267e40d95103267c40d95100067f30d95103267e30d95100067d30d95103267c30d95100067f20d95103267e20d95103267c20d951032e7f10d95103267e10d95100667d10d95103267c10d951004cfe76d91100067f65d91100067c65d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d9110006bf43d9110006be43d9110006bd43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d91100067f52d9110006be42d9110006bc42d9110024fe71d9110024fc71d911002cfe70d911002cfc70d911004cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100073f53d91100073d53d9110005bd72d9110006be62d9110006bc62d91100073f52d91102b7b771d9110007b651d9110007b551d9110007b631d9110007b531d911031fbb10d91102b7b610d91102b7b410d911031fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91102b6bf71d911031ebe71d9110006bd71d911031ebc71d9110006bf51d911031ebe51d9110006bd51d911031ebc51d9110006bf31d911031ebe31d9110006bd31d911031ebc31d9110006bf21d911031ebe21d911031ebc21d911031ebf70d91102b6be70d9110006bd70d91102b6bc70d9110006bf50d91102b6be50d9110006bd50d91102b6bc50d9110006bf30d91102b6be30d9110006bd30d91102b6bc30d9110006bf20d91102b6be20d91102b6bc20d911031ebf10d91102b6be10d91102b6bc10d91100657
  | 8 => 0x20e7f6454a1022e7e6454a100067d6454a1020e7c6454a1036d7f7354a1036d7d7354a1020e7f6354a101be7e6354a103667d6354a1020e7c6354a102157f7254a1007f6f7254a1020e7f6254a1000e7e6254a1020f6e6254a1000e6e6254a1006e7d6254a1020f6d6254a100066d6254a1000e7c6254a100567d6154a1020e7e6054a1020f6f2054a1020f7a2054a1020f6d2054a1020f771054a102077b1054a1004cff76d0a1002cfe76d0a10004fd76d0a1002cfc76d0a101d6bf64d0a1004ebe64d0a10006bd64d0a1004ebc64d0a1004ebf76d0a101d6be76d0a10006bd76d0a1004ebc76d0a101d6bf65d0a101b6be65d0a1035ebd65d0a101d6bc65d0a101d6bf63d0a101aebe63d0a10356bd63d0a101d6bc63d0a103573f53d0a103573d53d0a101d6bf62d0a1000ebe62d0a1006ebd62d0a1000ebc62d0a1006f3f52d0a1006f3d52d0a101d7ba20d0a101d7b710d0a101efbb10d0a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a101cebf6450a1004ebe6450a10006bd6450a1004ebc6450a1000eee6250a10006ed6250a10005f77150a10025f47150a10006bf7650a101cebe7650a10006bd7650a101cebc7650a101cebf6550a101a6be6550a1034ebd6550a101cebc6550a101cebf6350a1019ebe6350a10346bd6350a101cebc6350a103473f5350a103473d5350a10007af7250a101cebf6250a1000ebe6250a101cfae6250a1000eae6250a1006ebd6250a101cfad6250a10006ad6250a1000ebc6250a1006f3f5250a1006f3d5250a10007b77150a10007b47150a101cfaf2050a101cfba2050a101cfad2050a101cfb71050a101c7bb1050a1007d7e75d06100057d75d061004ebe64d0610006bd64d061002dfa70d0610005f970d061004cff765061004ebe6450610006bd6450610005fb705061002df8705061000cff764861002cfc764861000eee6248610006ed6248610005fb704861002df8704861002dfb7648210036fb764821002efb6348210336f963482103377b534821033779534821002feb724821002feb624821000efa624821002ef8624821002fe8624821006f7b524821006fea524821006f79524821033fe9524821000769524821006fbb424821006fea424821006fb94248210007e94248210007a9424821006fea3248210337e93248210025fa7148210025f8714821006feb2148210007e921482100657e76d95100667e76d951001c7e76d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100057d72d95100067e62d95100067c62d95103277771d95100677471d95100077631d95100077531d951032f7b10d95103277610d95103277410d951032f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d
  | 9 => 0xf52d0b100873d52d0b101efb671d0b10007b571d0b101efb651d0b103c7b551d0b101efb631d0b103bfb531d0b101efb621d0b10004ff7650b10024fe7650b10004fd7650b10024fc7650b101c6bf6450b1004ebe6450b10006bd6450b1004ebc6450b10025f67150b101c7b64150b10006bf7650b101c6be7650b10006bd7650b101c6bc7650b101c6bf6550b101a6be6550b103b6bd6550b101c6bc6550b101c6bf6350b1019ebe6350b103aebd6350b101c6bc6350b103af3f5350b103af3d5350b10007af7250b101c6bf6250b1000ebe6250b10086bd6250b1000ebc6250b100873f5250b100873d5250b101c7b67150b10007b57150b101c7b65150b103b7b55150b101c7b63150b103afb53150b101c7b62150b10087af2050b10025f77650710006f776507103a5f775507103a5f57550710027b77450710027b7645071004ef66450710026f46450710027b4645071039df7735071039df57350710397775350710397755350710005f7725071038f775250710007755250710007b74250710007b5425071002df6705071002df47050710025f77648710036f77648710385f77548710385f57548710005f77448710005f5744871037df7734871037df57348710026f76348710376f56348710377775348710377755348710027e77248710027e7624871000ef66248710026f46248710027e46248710087775248710087755248710087b74248710087b5424871002df6704871002df47048710087e7204871004ebe64d0310006bd64d0310025f671d0310005f571d0310007b541d031004cff76503100057f75503100957c755031004ebe6450310006bd6450310005f77150310025f47150310007b5415031000cff7648310024fc764831000eee6248310006ed62483100076d5248310007ad4248310005f77148310025f47148310007e52148310004ff75592100067f75592100047f755921001cfe7559210004fd755921001cfc75592100067c755921001c7c755921002ebf7459210006be5459210006bd5459210004ff7359210014fe7359210004fd7359210014fc73592100067f53592100067d5359210006bf4359210006bd4359210004ff725921000cfe725921000cfc72592100067f525921002cfc705921002ebe405921002ebc405921002ef7105921002ef51059210004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a1004cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a100067f5358a100067d5358a1002eef7258a1006e7f5258a1006eee5258a10006ed5258a1006eee4258a1006eee3258a10006ed3258a1006eef2158a1002cfc7058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a100067f7654a1020e7e7654a100067d7654a1020e7c7654a10
  | 10 => 0x52009dde7390520005dd739052000dee7290520005ed72905200076d5290520007ad429052002dfa7090520005f97090520004ff7650520004fe7650520004fc765052004ebe6450520006bd645052000dee72505200076d5250520007ad4250520004fe7610520004fd7610520024fc7610520006bf641052004ebc641052000dee7210520005ed72105200076d5210520007ad4210520006f76110520026f4611052002dfa7010520005f9701052002cec76485203f5ef75485203f5ed7548520005ef7448520005ed74485203edef73485203eded73485203e76f53485203e76d534852000def714852000fe77148520007e76148520026ee6148520026ec6148520007e461485203e7e631485203e7e53148520007eb704852002dee704852002dec7048520007e8704852000eef604852000feb60485203e7ea30485203e7e9304852000cfe76d012000cfc76d0120006bf64d012004ebc64d012000dee72d0120005ed72d01200076d52d0120007ad42d012004cff765012000cfe76501200d4fd765012000cfc76501200057f75501200a57c7550120006bf645012004ebc6450120005ef725012000dec72501200076d5250120007ad4250120004ff755931001cfe7559310004fd755931001cfc7559310026bf7459310004ff7359310014fe7359310004fd7359310014fc73593100067f53593100067d5359310004ff725931000cfe725931000cfc72593100067f525931002cfc7159310026be4159310026bc4159310004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b1004cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b100067f5358b100067d5358b10026ef7258b100867f5258b1002cfc7158b10026f63158b10006f53158b10026ee2158b10026ec2158b10086ef2058b10026fa1058b10026f91058b100067f7654b102067e7654b100067d7654b102067c7654b102067f6454b1022e7e6454b100067d6454b102067c6454b103dd7f7354b103dd7d7354b102067f6354b101be7e6354b103ce7d6354b102067c6354b103d57f7254b100976f7254b102067f6254b1000e7e6254b100867d6254b1000e7c6254b10207767154b10007757154b10207764154b10207763154b103cf753154b10207762154b100876f2054b1004cff76d0b10024fe76d0b10004fd76d0b10024fc76d0b101eebf64d0b1004ebe64d0b10006bd64d0b1004ebc64d0b10025f671d0b10005f571d0b101efb641d0b1004ebf76d0b101eebe76d0b10006bd76d0b1004ebc76d0b101eebf65d0b101b6be65d0b103c6bd65d0b101eebc65d0b101eebf63d0b101aebe63d0b103bebd63d0b101eebc63d0b103bf3f53d0b103bf3d53d0b101eebf62d0b1000ebe62d0b10086bd62d0b1000ebc62d0b100873
  | 11 => 0xa76d705492020f6c705492000768705492000f6f605492000e6f605492000f6b605492020f6e405492020f6c405492041f6f305492020f6e305492041f6a305492041f6d305492041f69305492020f6c305492002dec765092004eec765092002cec7650920415ef7550920415ed755092000def745092000faf7450920007af645092004eee645092004eec6450920007ac6450920407af5450920407ae5450920407ad5450920407ac545092040def735092040ded73509203ff6f53509203ff6d53509203ffaf43509203ffae43509203ffad43509203ffac4350920005ef7150920007eb705092002dee705092002dec7050920007e8705092000eef605092000feb60509201cfae40509201cfac40509203ffea30509203ffe93050920007af765092004eaf7650920007ac7650920006ac7650920417af7550920407ae7550920417ad7550920407ac7550920407af6550920407ae6550920407ad6550920407ac655092040faf73509203ffae735092040fad73509203ffac73509203ffaf63509203ffae63509203ffad63509203ffac63509203ffaf53509203ff2f53509203ffae53509203ffad53509203ff2d53509203ffac5350920007af7150920007ae7150920007ad7150920007ac7150920407af5150920407ae5150920407ad5150920407ac51509203ffaf31509203ffae31509203ffad31509203ffac3150920007af7050920007ab70509201cfae7050920007ad70509201cfac7050920007a8705092000faf605092000eaf605092000fab6050920407af50509201cfae5050920407ad50509201cfac50509203ffaf30509201cfae30509203ffaa30509203ffad30509203ffa930509201cfac30509200076d52d8520007ad42d8520004ff75d852001cfe75d8520004fd75d852001cfc75d852004cfe74d8520004fd74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d852002cfd72d852006e7f52d852006e7d52d852006ebf42d852006ebd42d852006ef621d852006ef521d852002cfe70d852002cfc70d85200076d5298520007ad4298520006f76198520055f970985200057f75585200a57c7558520005bf7458520005bc7458520005df735852009ddc73585200076d5258520007ad4258520085fb70585200a57e75185200057d7518520005be7418520005bd741852009dde7318520005dd73185200076d5218520007ad4218520026f66118520006f56118520004fe76d0520004fd76d052004cfc76d05200a57e75d05200057d75d052004ebe64d0520006bd64d052000dee72d0520005ed72d05200076d52d0520007ad42d0520006f761d0520026f461d0520004fe7690520004fd7690520024fc76905200a57e75905200057d7590520006bf649052004ebc649
  | 12 => 0xc745862004cbc7458620004ff7358620014fe7358620004fd7358620014fc73586200067f53586200067d53586200567f52586200567d5258620056bf4258620056bd425862002ef77158620006f65158620006f55158620006f63158620006f53158620056f62158620056f5215862002cff705862002cfd705862002cfc705862002eef205862002eed205862002ef6105862002ef4105862004cff76d062002cfe76d0620004fd76d06200b57e75d06200057d75d062004ebe64d0620006bd64d0620024ff769062002cfe7690620004fd76906200b57e75906200057d75906202b6bf649062004ebc64906200adde7390620005dd7390620026f66190620006f5619062002dfa7090620005f97090620004ff7650620004fd765062002cfc765062004ebe6450620006bd6450620026f66150620006f56150620024ff761062002cfe7610620004fd761062030ebf641062004ebc641062002dfa7010620005f9701062004cfe76d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d912002cff72d912000cfe72d912002cfd72d912000cfc72d91200ee7f52d91200ee7d52d91200eebf42d91200eebd42d9120024fe71d9120004fd71d9120006bf64991200d5f970991200057f75591200a57c7559120005df735912009ddc7359120005f77159120005f47159120105fb7059120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf7459120006be5459120006bd5459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc73591200067f53591200067d5359120006bf4359120006bd43591200d4ff7259120006ef72591200d67f52591200d67d52591200d6bf42591200d6bd4259120004ff7159120006f77159120004f77159120024fc7159120006f47159120024f47159120104ff7059120006fb70591201cebe40591201cebc40591200ecfe76191200a57e75191200057d751912004ebe6419120006bd64191200a76f765492001e6f76549200a76c765492001e6c76549200076f74549200076e74549200076d74549200076c74549200076f64549200076e64549200076d64549200076c64549204276f73549204256f735492041f6e73549204276d73549204256d735492041f6c735492041f6f635492041f6e635492041f6d635492041f6c635492041f6f435492041f6e435492041f6d435492041f6c43549200076f71549200076e71549200076d71549200076c715492041f6f315492041f6e315492041f6d315492041f6c31549200076f70549200076b705492020f6e7054920
  | 13 => 0x8440006f4755844004ef7745844004ef6745844004ef4745844004ef7545844004ef6545844004ef5545844004ef45458440006f77358440006f67358440006f57358440006f47358440006f75358440006775358440006f65358440006f55358440006755358440006f4535844004ef7435844004ef6435844004ef5435844004ef44358440006f77258440006f67258440006f57258440006f47258440006f75258440006775258440006f65258440006f55258440006755258440006f4525844004ef7425844004eb7425844004ef6425844004ef54258440006b5425844004ef44258440006f73258440006f63258440006f53258440006f4325844002ef7705844002ef6705844002ef4705844002ef7505844002ef6505844002ef5505844002ef4505844002ef7405844002eb7405844002ef6405844002ef5405844002eb5405844002ef4405844002ef7305844002ef6305844002ef5305844002ef4305844002ef7205844002ef6205844002ef5205844002ef4205844004dbd7690440316bd7690440004bd76904403173e75904403173d759044004ebf659044004f3e659044042ebd659044004f3d65904400063d65904403179e73904403179d739044004ebf639044004f9e6390440436bd639044004f9d63904400069d63904404373f53904404373d5390440005bd729044004fae6290440006bd629044004fad6290440006ad629044042f3f52904400073d529044004dbe719044004fb6719044004ebf619044004fb66190440316bd619044004fb56190440006b561904402b5bf70904402b5bd70904402b6be609044004fba60904402b7b71090440024ff768844002cfe7688440004fd76884401367e65884400067d6588440315bf748844004dbc748844012ede6388440006dd638844000eee6288440006ed6288440026f66188440006f56188440004ff7648440004fd764844002cfc76484401267e65484400067d6548440005bf744844004dbc744844011ede6348440006dd634844000eee6248440006ed6248440026f66148440006f56148440004ff75592200067f75592200047f755922001cfe7559220004fd755922001cfc75592200067c755922001c7c755922002ebf7459220006be5459220006bd5459220004ff7359220014fe7359220004fd7359220014fc73592200067f53592200067d5359220006bf4359220006bd43592200d67f52592200d67d52592200d6bf42592200d6bd4259220004ff7159220024fc715922002cfe705922002cfc705922002ebe405922002ebc405922002eef205922002eed2059220004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620006bf7458620004bf745862004cfc7458620006b
  | 14 => 0x20f5e63548401be5e635484044e7d635484020f5d63548400065d635484020e7c63548402157f72548400cf6f725484020e7f625484000e7e625484020f6e625484000e6e62548400be7d625484020f6d62548400066d625484000e7c62548400bf3f42548402067e615484020f76615484020f75615484022f3c415484020e7e605484020f3f405484020f7a405484020f3d405484022f79405484020f6f205484004dbf7650840106bf765084004ebf65508401a6be655084004f3e65508401a63e6550840446bd655084004f3d65508400063d655084004ebc655084004ebf635084019ebe635084004f9e635084019e9e635084043ebd635084004f9d63508400069d635084004ebc635084043f3f535084043f3d535084004dbf725084004faf725084004ebf625084000ebe625084004fae625084000eae62508400bebd625084004fad625084000ebc62508400bf3f52508400bf3d5250840315bc71508401c6be615084004fb6615084004fb561508401cdbf70508401cebe605084004fba60508401cfaf2050840026f77598440026f67598440026f57598440026f47598440026f77498440026f67498440026f57498440026f4749844004ef7549844004ef6549844004ef5549844004ef45498440026f77398440026f67398440026f57398440026f47398440006f75398440006775398440006f65398440006f55398440006755398440006f4539844004ef7439844004ef6439844004ef5439844004ef44398440026f77298440026f67298440026f57298440026f47298440006f75298440006775298440006f65298440006f55298440006755298440006f4529844004ef7429844004eb7429844004ef6429844004ef54298440006b5429844004ef44298440006f73298440006f63298440006f53298440006f4329844002ef7709844002ef6709844002ef5709844002ef4709844002ef7509844002ef6509844002ef5509844002ef4509844002ef7409844002ef6409844002ef5409844002ef4409844002ef7309844002ef6309844002ef5309844002ef4309844002ef7209844002ef6209844002ef5209844002ef42098440004ff755844001cfe7558440004fd755844001cfc7558440004ff7358440014fe7358440004fd7358440014fc73584400067f53584400067d5358440004ff725844000cfe725844000cfc72584400067f52584400067d525844004ebf4258440006bd425844002ef77158440006f75158440006f65158440006f55158440006f4515844004ef7415844004ebc415844004ef4415844004eb44158440006f73158440006f63158440006f53158440006f43158440006f72158440006f4215844002ebf405844002ebd405844002ef6105844002ef41058440006f77558440006f67558440006f5755
  | 15 => 0xe7258c40006dd7258c40006dc7258c40006df5258c400065f5258c40006de5258c40006dd5258c40006dc5258c4004edf4258c4004e9f4258c4004ede4258c4004edd4258c4004edc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dd5158c40006dc5158c4004edf4158c4004ede4158c4004edd4158c4004edc4158c4004e9c4158c40006df2158c40006dc2158c4002edf7058c4002ede7058c4002edd7058c4002edc7058c4002edf5058c4002ede5058c4002edd5058c4002edc5058c4002edf4058c4002e9f4058c4002ede4058c4002edd4058c4002e9d4058c4002edc4058c4002edf2058c4002ede2058c4002edd2058c4002edc2058c4002edf1058c4002ede1058c4002edd1058c4002edc1058c40004ff755884001cfe75588400067e755884001c7e7558840004fd75588400067d755884001cfc755884004ebe745884000cfd745884000cbd7458840004ff7358840014fe7358840004fd7358840014fc73588400067f53588400067d535884002cff725884002eef72588400be7f5258840006ef52588400066f52588400beee5258840006ed52588400beec525884004ebf425884004eef425884004eaf425884004eec4258840006ef32588400beee3258840006ed32588400beec3258840004ff7158840024fc715884004ebc41588400beef21588400beec215884002cfc705884002ebf405884002ebd405884002eee205884002eec2058840006ef7558840006ee75588400066e7558840006ed75588400066d7558840006ec755884004eef745884004eee745884004eae745884004eec745884004eef545884004eee545884004eed545884004eec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef53588400066f5358840006ee5358840006ed53588400066d5358840006ec535884004eef435884004eee435884004eed435884004eec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef5158840006ee5158840006ed5158840006ec515884004eef415884004eee415884004eed415884004eec415884004eac4158840006ef3158840006ee3158840006ed3158840006ec315884002eef705884002eee705884002eec705884002eef505884002eee505884002eed505884002eec505884002eef405884002eaf405884002eee405884002eed405884002ead405884002eec405884002eef305884002eee305884002eed305884002eec305884002eef105884002eee105884002eed105884002eec105884020d7f76548400067f76548400047f765484020e7e765484020d7d76548400067d76548400047d765484020e7c76548401067e64548404557f73548404557d735484020e7f63548401be7e6354840
  | 16 => 0x85400067f65185400067c651854030ebf6418540026f66118540006f56118540005be76d054004ebe76d0540004be76d054004dbf75d054004f3e75d0540495bd75d054004f3d75d05400053d75d05400073f65d05404873c65d054004dbf73d054048dbd73d054047f3f53d054047f3d53d0540005bd72d0540006bf62d05404873f52d05400073d52d0540026be61d0540026bc61d054047fb631d054047fb531d054002dbe70d054002dbc70d054004ebf60d054004fbb60d054002cfe76905400e57e75905400057d75905400067f659054017e7c659054046dbd74905400ddde7390540005dd7390540006f76190540026f4619054002dfa7090540005f9709054002cfc76505400067f65505401667c6550540006f76150540026f4615054004fb44150540005fb705054002df8705054002cbc7650540475bf7550540475bd75505400073f655054045f3c655054046dbf735054046dbd73505404673f53505404673d5350540005bf7250540006bf625054045f3f52505400073d525054004dbf715054004fb77150540007b76150540026be6150540026bc6150540007b46150540007bb705054002dbe705054002dbc7050540007b8705054004ebf605054004fbb6050540004fe7688540004fd7688540024fc76885400067f65885401367c658854004dbe7488540005bd7488540004ff7648540004fe7648540004fc76485400067f65485401267c654854004dbe7448540005bd744854004e7f745944004e7e745944004e7d745944004e7c74594400067f73594400047f73594400067e73594400067d73594400047d73594400067c735944004e7f435944004e7e435944004e7d435944004e7c43594400067f72594400047f72594400067e72594400067d72594400067c725944004e7f425944004e3f425944004e7e425944004e7d425944004e7c42594400067f32594400067e32594400067d32594400067c32594400067f71594400067e71594400067d71594400067c715944004e7f415944004e7e415944004e7d415944004e7c415944004e3c41594400067f31594400067e31594400067d31594400067c31594400067f21594400067c215944002e7f705944002e7e705944002e7d705944002e7c705944002e7f405944002e3f405944002e7e405944002e7d405944002e3d405944002e7c405944002e7f305944002e7e305944002e7d305944002e7c305944002e7f205944002e7e205944002e7d205944002e7c205944002e7f105944002e7e105944002e7d105944002e7c1059440006df7558c40006de7558c400065e7558c40006dd7558c400065d7558c40006dc7558c4004edf7458c4004ede7458c4004edd7458c4004edc7458c4004edf5458c4004ede5458c4004edd5458c4004edc5458c40006df7258c40006d
  | 17 => 0xcbc74d8940006be54d8940006bd54d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d8940006bf43d8940006bd43d89400d67f52d89400d6ee42d8940024fe71d8940004fd71d894004cfd70d89401d6be40d89401d6bc40d89400d6ef20d89400057f75589400e57c75589400067f65589400067c6558940005df73589400dddc73589400d6ec6258940005f77158940005f471589400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c76549400073e74549400073d74549404e57f73549404e57d73549404de7f63549401be7e63549404de7d63549401be7c63549404df3f43549404df3d43549400d57f72549400e76f72549400d67f625494000e7e625494000e7c62549402067c615494022f7b405494020f3e40549400d76f2054940005be76d094004ebe76d094004dbf75d09404d5bd75d09404cebf65d09400073f65d09400063f65d09401b6be65d09404cebd65d09401b6bc65d09404cf3c65d09401b63c65d094004dbf73d09404c5bd73d09404bebf63d09401aebe63d09404bebd63d09401aebc63d09404bf3f53d09404bf3d53d09400d5bd72d09400d6bf62d094000ebe62d094000ebc62d09400d73f52d09400d73d52d0940005bd71d09401eebc61d094002dbe70d094002dbc70d094004ebf60d094004fbb60d094002cfc76509400067f65509401a67c6550940006ef625094000eec625094004fac4250940005fb705094002df870509401cebe765094002dbc765094000ebc765094002cbc76509404b5bf75509404b5bd75509404aebf65509400073f65509400063f65509401a6be65509404aebd65509401a6bc65509404af3c65509401a63c65509404a5bf73509404a5bd735094049ebf635094019ebe635094049ebd635094019ebc635094049f3f535094049f3d535094004dbf725094004faf72509400d6bf6250940007af6250940006af625094000ebe625094000ebc62509400d7ac62509400d73f52509400d73d5250940005bf71509401c6bc6150940007bb705094002dbe705094002dbc7050940007b8705094004ebf605094004fbb60509400d7af20509400067f65d85400067c65d8540004ff75d854001cfe75d8540004fd75d854001cfc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854000cfe72d8540004fd72d854000cfc72d85400067f52d85400067d52d8540006bf42d8540006bd42d8540006f631d8540006f531d8540006f721d8540006f421d85400e57e75985400057d75985400067f65985400067c65985402b6bf64985400ddde7398540005dd7398540006f761985400057f75585400e57c75585400067f65585400067c655
  | 18 => 0x55158640006f63158640006f5315864002cfc705864002ebf405864002ebd405864002ef6105864002ef410586400fd7e75906400057d75906400f5de7390640005dd7390640026f66190640006f5619064002dfa7090640005f9709064031f3e759064031f3d75906402b6bf659064050ebd659064031f9e739064031f9d73906402b6bf6390640516bd63906405173f53906405173d5390640005bd7290640006bd629064050f3f52906400073d529064004dbe71906402b6bf61906402b7b6619064031ebd61906402b7b561906402b7ba70906402b5bd709064031fb9709064004ebe60906402b7b71090640024ff7650640026f66150640006f56150640005fb705064002df8705064030dbd761064004ebd761064030ebf6510640506bd651064030ebf63106404febd63106404ff3f53106404ff3d5310640005bd7210640006bd62106405073f52106400073d521064004fb6711064030ebf611064031ebd611064031fb631106404ffb5311064004dbf701064030dbd701064004fba6010640024ff768864002cfe7688640004fd768864031dbf748864004dbc7488640026f66188640006f56188640004ff7648640004fd764864002cfc7648640005bf744864004dbc744864000eee6248640006ed6248640026f66148640006f561486400e57e76d95400e67e76d954001c7e76d95404ef3f74d95400e73c74d95400057f73d95400057d73d95400067f63d95400067e63d95400067d63d95400067c63d95400073f43d95400073d43d95400057d72d95400067e62d95400067c62d95404f77b40d95404ef3e40d95404ef3c40d95404f77840d95404ee7f74d95404f67e74d95400e67d74d95404f67c74d95400067f73d95400047f73d95400067e73d95400067d73d95400047d73d95400067c73d95404f67f43d95400067e43d95400067d43d95404f67c43d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95404f67f42d95400067e42d95404f67c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95404f67f41d95404f67c41d95400067f31d95400067e31d95400067d31d95400067c31d95400067f21d95400067c21d95404f67f70d95404ee7e70d95400e67d70d95404ee7c70d95404f67f40d95404ee7e40d95400e67d40d95404ee7c40d95400067f30d95404ee7e30d95400067d30d95404ee7c30d95400067f20d95404ee7e20d95404ee7c20d95404ee7e10d95404ee7c10d954000cfe76d89400e57c75d89400067f65d89400067c65d89400d6ee62d8940004ff75d89400067f75d894001cfe75d8940004fd75d894001cfc75d89400067c75d894001c7c75d89401d6bf74d894002cfd74d894000cfc74d8940
  | 19 => 0x87400067f52587400067d525874004ebf4258740006bd425874004ef7715874004ef7415874004ef4415874004dbf7650740006bf7650740565bf7550740565bd755074055dbf735074055dbd73507405573f53507405573d5350740005bf7250740006bd625074054f3f52507400073d525074004fb7715074004fb76150740026be6150740026bc615074004fb4615074002dbe705074002dbc7050740024ff768874004cfe7688740004fd768874004dbe7488740005bd7488740004ff7648740004fd764874004cfc764874004dbe7448740005bd7448740004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40006bd7458a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400067f5358a400067d5358a4002eef7258a400ee7f5258a400eeee5258a40006ed5258a400eeee4258a400eeee3258a40006ed3258a40004ff7158a40024fc7158a400eeef2158a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a400067f7654a4020e7e7654a400067d7654a4020e7c7654a400d67d6454a405457f7354a405457d7354a4020e7f6354a401be7e6354a4053e7d6354a4020e7c6354a402157f7254a400ff6f7254a4020e7f6254a4000e7e6254a4020f6e6254a4000e6e6254a400ee7d6254a4020f6d6254a400066d6254a4000e7c6254a402067e6154a4020e7e6054a4020f3f4054a4022f7b4054a4020f6f2054a401d5bd76d0a4004ebd76d0a401d6bf65d0a401b6be65d0a40536bd65d0a401d6bc65d0a401d6bf63d0a401aebe63d0a4052ebd63d0a401d6bc63d0a4052f3f53d0a4052f3d53d0a401d6bf62d0a4000ebe62d0a400eebd62d0a4000ebc62d0a400ef3f52d0a400ef3d52d0a4031dbe71d0a401eebe61d0a4004dbf70d0a401d5bd70d0a4004fba60d0a4000cff7650a4000eee6250a40006ed6250a40005fb7050a4002df87050a401cdbf7650a4000ebf7650a4000cbf7650a401cebf6550a401a6be6550a40526bd6550a401cebc6550a401cebf6350a4019ebe6350a4051ebd6350a401cebc6350a4051f3f5350a4051f3d5350a4004dbf7250a4004faf7250a4000ebe6250a401cfae6250a4000eae6250a400eebd6250a401cfad6250a40006ad6250a4000ebc6250a400ef3f5250a400ef3d5250a4031dbc7150a401c6be6150a401cdbf7050a40007bb7050a401cfb87050a4004ebe6050a401cfaf2050a40004ff75586400067f75586400047f755864001cfe7558640004fd755864001cfc75586400067c755864001c7c7558640004ff7358640014fe7358640004fd7358640014fc73586400067f53586400067d5358640004ff725864000cfe725864000cfc72586400067f52586400067d5258640006bf4258640006bd425864002ef77158640006f65158640006f
  | 20 => 0x6bf7459121004ff7359121014fe7359121004fd7359121014fc73591210067f53591210067d5359121154ff7259121006ef72591211567f52591211567d5259121156bf4259121156bd4259121184ff7159121006f771591211c6be41591211c6bc4159121004ff705912102cfc7059121156ef205912116cfe761912104ebe6419121006bd641912100cfe76d052100cfc76d05211257e75d05210057d75d0521006bf64d052104ebc64d052100dee72d0521005ed72d052104cff765052100cfe7650521154fd765052100cfc7650521006bf645052104ebc6450521005ef725052100dec7250521027e42150521004ff75d812101cfe75d8121004fd75d812101cfc75d812104cfe74d8121004fd74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d8121024fd72d81210867f52d81210867d52d8121086bf42d8121086bd42d8121006f631d8121006f531d8121086fa20d8121006fb60981210057f75581211257c7558121005bf7458121005bc7458121005df735812111ddc73581211257e75181210057d7518121005be7418121005bd741812111dde7318121005dd731812102efa6018121006f96018121004ff7558b4001cfe7558b40004fd7558b4001cfc7558b4004ebe7458b4002cfc7458b4004ebe5458b40006bd5458b40004ff7358b40014fe7358b40004fd7358b40014fc7358b400067f5358b400067d5358b4004ebf4358b40006bd4358b4004eef7258b401067f5258b4004ebf4258b4004eef4258b4004eaf4258b4004eec4258b40004ff7158b40024fc7158b4004ebf4158b401cebe4058b4004ebc4058b40106ef2058b400067f7654b4022e7e7654b400067d7654b4022e7c7654b4022f3e7454b400073d7454b405957f7354b405957d7354b4022e7f6354b401be7e6354b4058e7d6354b401be7c6354b4022f3f4354b4058f3d4354b401057f7254b401176f7254b401067f6254b4000e7e6254b401067d6254b4000e7c6254b401073f4254b402067e6154b4022f3f4154b401076f2054b4004dbf7650b400bebf7650b40585bf7550b40585bd7550b4004ebf6550b401a6be6550b4057ebd6550b4004ebc6550b40575bf7350b40575bd7350b4004ebf6350b4019ebe6350b4056ebd6350b4004ebc6350b4056f3f5350b4056f3d5350b4004faf7250b4004ebf6250b4004faf6250b4000ebe6250b40106bd6250b4000ebc6250b4004fac6250b401073f5250b401073d5250b40005bf7150b401c6be6150b4002dbe7050b4002dbc7050b40107af2050b40004ff755874001cfe7558740004fd755874001cfc755874002cfc7458740004ff7358740014fe7358740004fd7358740014fc73587400067f53587400067d5358740004ff725874000cfe725874000cfc725
  | 21 => 0xe605484113f6f205484104dbf7650841186bf76508415b5bf75508415b5bd755084104ebf65508411a6be65508415aebd655084104ebc65508415a5bf73508415a5bd735084104ebf635084119ebe635084159ebd635084104ebc635084159f3f535084159f3d535084104dbf725084104faf725084104ebf625084100ebe625084113ebd625084100ebc625084113f3f525084113f3d52508411c5bf71508411c6be615084104fb661508411c7b6315084159fb5315084130dbc70508411cebe605084113faf2050841004ff75580410067f75580410047f755804101cfe7558041004fd755804101cfc75580410067c755804101c7c755804104ebe5458041006bd5458041004ff7358041014fe7358041004fd7358041014fc73580410067f53580410067d535804104ebf4358041006bd4358041004ff725804100cfe725804100cfc72580410067f52580410067d525804104ebf4258041006bd4258041026bf4158041026f64158041026bd415804104ef54158041026f63158041006f53158041026fb7058041006fa5058041006f9505804104efb405804104ebc405804104ef84058041006fa3058041006f93058041026fb1058041026f81058041004ff755922101cfe7559221004fd755922101cfc7559221026bf7459221004ff7359221014fe7359221004fd7359221014fc73592210067f53592210067d53592211567f52592211567d5259221156bf4259221156bd4259221024fe7159221024fc7159221026be4159221026bc4159221004ff705922102cfc7059221026f71059221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221006bf7458221004bf745822104cfc7458221006bc745822104cbc7458221004ff7358221014fe7358221004fd7358221014fc73582210067f53582210067d53582210567f52582210567d5258221056bf4258221056bd4258221024fc7158221026f63158221006f53158221026ef2158221026ed2158221026fb7058221056fa2058221026fb1058221026f8105822104cfe76d91211257e75d91210057d75d9121004ff75d912101cfe75d91210067e75d912101c7e75d9121004fd75d91210067d75d91210047d75d912101cfc75d9121006be54d9121006bd54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d91210067f53d91210067d53d9121006bf43d9121006bd43d9121024ff72d9121024fd72d912116e7f52d912116e7d52d912116ebf42d912116ebd42d912102cfe70d9121004fd70d912116eef20d91211257e75991210057d7599121006bf649912111dde7399121005dd7399121155f57199121185f77159121004ff755912101cfe7559121004fd755912101cfc7559121
  | 22 => 0x49411676f72549411567f625494100e7e625494100e7c625494122f7741549412073e415494120e7c60549411576f2054941005be76d094104ebe76d09415e6bf65d09411b6be65d09415e6bd65d09411b6bc65d09415debf63d09411aebe63d09415debd63d09411aebc63d09415df3f53d09415df3d53d0941155bd72d0941156bf62d094100ebe62d094100ebc62d09411573f52d09411573d52d0941025be71d0941025bc71d094104ebf61d094104fb761d0941005bd70d09411d6bc60d0941024fc7650941006ef625094100eec6250941005f77150941025f471509411c6be7650941025bc765094100ebc7650941024bc76509415d6bf65509411a6be65509415d6bd65509411a6bc65509415cebf635094119ebe63509415cebd635094119ebc63509415cf3f53509415cf3d535094104dbf725094104faf7250941156bf6250941007af6250941006af625094100ebe625094100ebc6250941157ac62509411573f52509411573d5250941007b77150941025be7150941025bc7150941007b47150941025b4715094104ebf615094104fb76150941005bf70509411cebc6050941157af2050941004ff75d814101cfe75d8141004fd75d814101cfc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d8141006bf42d8141006bd42d8141006fb60981410057f75581411657c75581411657e75181410057d75181412b6bf641814115dde7318141005dd7318141155ee7218141005ed721814102efa6018141006f96018141004ff755884101cfe7558841004fd755884101cfc755884104ebe745884104ebe5458841006bd5458841004ff7358841014fe7358841004fd7358841014fc73588410067f53588410067d535884104ebf4358841006bd4358841024ff7258841026ef725884113e7f525884113eee5258841006ed525884104ebf425884104eef425884104eaf425884104eec425884113eee3258841006ed3258841024fc7158841026bf4158841026bd4158841026f63158841006f53158841026ee2158841026ec2158841004ff705884102cfc705884104ebc405884113eef20588410067f76548412067e76548410067d76548412067c765484122f3e74548410073d74548411867e64548415c57f73548415c57d73548412067f63548411be7e63548415be7d63548412067c635484122f3f43548415bf3d43548413d57f725484114f6f72548412067f625484100e7e62548412076e625484100e6e625484113e7d62548412076d62548410066d625484100e7c625484113f3f42548412067e61548412073f41548412077641548412073d415484122f7541548412077631548415bf75315484120e7
  | 23 => 0x1567d6454a416457f7354a416457d7354a412067f6354a411be7e6354a412075e6354a411be5e6354a4163e7d6354a412075d6354a410065d6354a412067c6354a4163f3f4354a4163f3d4354a413d57f7254a4117f6f7254a412067f6254a4100e7e6254a4116e7d6254a4100e7c6254a412067e6154a412073f4154a4122f774154a4120e7e6054a4116f6f2054a411edbd76d0a4104ebd76d0a4104dbf75d0a41635bd75d0a411eebf65d0a411b6be65d0a411ef3e65d0a411b63e65d0a4162ebd65d0a411ef3d65d0a410063d65d0a411eebc65d0a4104dbf73d0a41625bd73d0a411eebf63d0a411aebe63d0a411ef9e63d0a411ae9e63d0a4161ebd63d0a411ef9d63d0a410069d63d0a411eebc63d0a4161f3f53d0a4161f3d53d0a411eebf62d0a4100ebe62d0a4116ebd62d0a4100ebc62d0a4116f3f52d0a4116f3d52d0a4104dbf71d0a411edbd71d0a4104fb661d0a412b5be70d0a411d6be60d0a4100cff7650a411a67e6550a410067d6550a4119ede6350a41006dd6350a4100eee6250a41006ed6250a41005f77150a41025f47150a411c5bf7650a4100ebf7650a4100cbf7650a41615bf7550a41615bd7550a411c6bf6550a411a6be6550a411c73e6550a411a63e6550a4160ebd6550a411c73d6550a410063d6550a411c6bc6550a41605bf7350a41605bd7350a411c6bf6350a4119ebe6350a411c79e6350a4119e9e6350a415febd6350a411c79d6350a410069d6350a411c6bc6350a415ff3f5350a415ff3d5350a4104dbf7250a4104faf7250a4100ebe6250a411c7ae6250a4116ebd6250a411c7ad6250a41006ad6250a4100ebc6250a4116f3f5250a4116f3d5250a411c5bf7150a41007b77150a411c7b47150a4104ebe6150a412b5bc7050a411cebe6050a4116faf2050a41004ff755824101cfe7558241004fd755824101cfc7558241006be5458241006bd5458241004ff7358241014fe7358241004fd7358241014fc73582410067f53582410067d5358241006bf4358241006bd4358241004ff725824100cfe725824100cfc72582410067f52582410067d5258241006bf4258241006bd4258241024fc7158241026bf4158241026bd4158241026fb7058241026fb1058241026f8105824100cfe76d8941156ee62d8941004ff75d894101cfe75d8941004fd75d894101cfc75d89411eebf74d8941024fd74d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d89411567f52d8941156ee42d894104cfd71d89411eebe41d89411eebc41d8941156ef21d894102cfe70d8941004fd70d8941156ec62589410067f76549410067e76549410067d76549410067c76549415f57f73549415f57d73549415ee7f63549411be7e63549415ee7d63549411be7c63549411557f725
  | 24 => 0xf52583410067d525834104ebf4258341006bd425834104ef6415834104ef54158341006f63158341006f5315834104efb705834104efb405834104ef8405834117e7f74596416567e74596410067d74596416567c74596410067f73596410047f73596410067e73596410067d73596410047d73596410067c73596416567f43596410067e43596410067d43596416567c43596410067f72596410047f72596410067e72596410067d72596410067c72596416567f42596410067e42596416567c42596410067f32596410067e32596410067d32596410067c32596410267f71596410267e71596410267d71596410267c71596410267f41596410267e41596410267d41596410267c41596410267f31596410267e31596410267d31596410267c31596410267f21596410267e21596410267d21596410267c21596410067f70596410067e70596410067d70596410067c70596416567f40596416567c40596410067f30596410067e30596410067d30596410067c30596410067f20596410067c20596410267f10596410267710596410267e10596410267d10596410267c1059641006df7558e41006de7558e410065e7558e41006dd7558e410065d7558e41006dc7558e41176df7458e41176de7458e41006dd7458e41176dc7458e41006df5458e4164ede5458e41006dd5458e4164edc5458e41006df7258e41006de7258e41006dd7258e41006dc7258e41006df5258e410065f5258e41006de5258e41006dd5258e41006dc5258e4164edf4258e41006de4258e4164edc4258e41026df7158e41026de7158e41026dd7158e41026dc7158e41026df5158e41026de5158e41026dd5158e41026dc5158e41026df4158e4164ed74158e41026de4158e41026dd4158e41026dc4158e41026d44158e41026df2158e41026de2158e41026dd2158e41026dc2158e41006df7058e41006de7058e41006dd7058e41006dc7058e41006df5058e41006de5058e41006dd5058e41006dc5058e4164edf4058e4164edc4058e41006df2058e41006dc2058e41026df1058e41026d71058e41026de1058e41026dd1058e41026dc1058e41004ff7558a4101cfe7558a410067e7558a4101c7e7558a41004fd7558a410067d7558a4101cfc7558a41006bd7458a41006be5458a41006bd5458a41004ff7358a41014fe7358a41004fd7358a41014fc7358a410067f5358a410067d5358a41006bf4358a41006bd4358a41026ef7258a4116e7f5258a4116eee4258a41024fc7158a41026bf4158a41026bd4158a41026ee2158a41026ec2158a41004ff7058a4102cfc7058a4116eef2058a41026f71058a412057f7654a410067f7654a410047f7654a412067e7654a412057d7654a410067d7654a410047d7654a412067c7654a410073e7454a410073d7454a41
  | 25 => 0x81421cebf60181421cfba60181421cebd6018142007b960181421cfaf20181421cfba20181420bfb9201814204e7f745974104e7e745974104e7d745974104e7c74597410067f73597410047f73597410067e73597410067d73597410047d73597410067c735974104e7f435974104e7e435974104e7d435974104e7c43597410067f72597410047f72597410067e72597410067d72597410067c725974104e7f425974104e3f425974104e7e425974104e7d425974104e7c42597410067f32597410067e32597410067d32597410067c32597411967f715974167e7e71597410067d715974167e7c715974104e7f415974104e7e415974167e3e415974104e7d415974104e7c415974104e3c41597410067f315974167e7e31597410067d315974167e7c31597410067f215974167e7e215974167e7c21597410067f70597410067e70597410067d70597410067c705974104e7f405974104e3f405974104e7e405974104e7d405974104e7c40597410067f30597410067e30597410067d30597410067c30597410067f20597410067c205974167e7f105974167e7c1059741004ff7558b4101cfe7558b410067e7558b4101c7e7558b41004fd7558b410067d7558b4101cfc7558b4104ebe7458b41024fc7458b41004ff7358b41014fe7358b41004fd7358b41014fc7358b410067f5358b410067d5358b4104eef7258b411867f5258b4104ebf4258b4104eef4258b4104eaf4258b4104eec4258b41006ef3258b41186ec3258b411c6be4158b4104ebc4158b41006f63158b41006f53158b41186ef2158b41004ff7058b4102cfc7058b4104ebf4058b41186ef2058b4122d7f7654b410067f7654b410047f7654b4122e7e7654b4122d7d7654b410067d7654b410047d7654b4122e7c7654b416757f7354b416757d7354b4122e7f6354b411be7e6354b4166e7d6354b411be7c6354b411857f7254b411976f7254b411867f6254b4100e7e6254b411867d6254b4100e7c6254b411873f4254b4166f763154b4166f753154b4120e7e6054b411876f2054b4104dbf7650b4113ebf7650b4104ebf6550b411a6be6550b4104f3e6550b411a63e6550b41666bd6550b4104f3d6550b410063d6550b4104ebc6550b4104ebf6350b4119ebe6350b4165ebd6350b4104ebc6350b4165f3f5350b4165f3d5350b4104faf7250b4104ebf6250b4100ebe6250b41186bd6250b4100ebc6250b411873f5250b411873d5250b41025be7150b41025bc7150b4165fb63150b4165fb53150b41005bf7050b411cebe6050b41187af2050b41004ff755834101cfe7558341004fd755834101cfc7558341024fc7458341004ff7358341014fe7358341004fd7358341014fc73583410067f53583410067d5358341004ff725834100cfe725834100cfc72583410067
  | 26 => 0x5bd75585421a5bc7558542005bf735854219dbe7358542005bd735854219dbc73585420073f53585420073d5358542007af7258542007af62585421573f52585421573d5258542007b761585421c6be6158542005bf70585421cdbc7058542157af2058542185be76185421c5bf75185421a5be7518542005bd75185421c5bc7518542006bf6518542006bd65185421c5bf731854219dbe7318542005bd73185421c5bc7318542006bf6318542006bd63185420073f53185420073d531854200dbe721854200dbc72185421eebf6218542007af621854213f3f521854213f3d52185421c6bf61185421c7b661185421c6bd6118542007b56118542006b561185421c7b65118542007b551185421c7b63118542007b531185421c7b6211854213fb521185421cdbe7018542005bd701854213faf2018542005bf75d81421a5be75d8142005bd75d81421a5bc75d8142006bf65d8142006bd65d8142005bf73d814219dbe73d8142005bd73d814219dbc73d8142006bf63d8142006bd63d81420073f53d81420073d53d8142007af72d8142106bf62d8142007af62d81421073f52d81421073d52d81421c5be71d8142005bd71d8142006bf61d8142006bd61d8142107af20d8142107ba20d8142107b920d81421cdbf75981421a5be7598142005bd75981421cdbc75981421cdbf739814219dbe7398142005bd73981421cdbc73981420073f53981420073d53981421cfad7298142007af62981420ef3f52981420ef3d52981421c5be7198142005bd7198142006be6198142006bc61981421cdbe70981421cebf6098142007bb60981421cfaf2098142005bf75581420073f75581420053f75581421a5be7558142005bd75581421a5bc75581420073c75581421a53c7558142006bf6558142006bd6558142005bf73581420079f73581420059f735814219dbe7358142005bd735814219dbc73581420079c735814219d9c7358142006bf6358142006bd63581420073f53581420073d5358142007af7258142007af62581420d73f52581420d73d5258142005bf7158142007b77158142005b771581421c5bc7158142007b47158142005b47158142006bf6158142006bd6158142007bb60581421cebe60581420d7af2058142105be76181421cdbf75181421a5be75181421cf3e75181421a53e7518142005bd75181421cf3d75181420053d75181421cdbc75181421cdbf731814219dbe73181421cf9e731814219d9e7318142005bd73181421cf9d73181420059d73181421cdbc73181420073f53181420073d531814200dbe72181421cfad721814200dbc72181421d6bf6218142007af62181420bf3f52181420bf3d52181421c5be71181421cfb67118142005b67118142005bd71181421cfb57118142005b57118142006be6118142006bc611
  | 27 => 0xc75d8542186bd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d854204cfd72d85421867f52d85421867d52d8542006f651d8542006f551d8542006f631d8542006f531d8542186f621d854202cfe70d8542004fd70d8542186ef20d85421a57e75985420057d759854219dde7398542005dd7398542006f76198542026f66118542006f56118542004ff75d814201cfe75d8142004fd75d814201cfc75d8142106bd74d8142006be54d8142006bd54d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d8142006bf43d8142006bd43d814204cfd72d81421067f52d81421067d52d8142024fe71d8142004fd71d8142106fa20d8142006fb60981420057f75581421a57c7558142005df735814219ddc7358142005f77158142005f471581421a57e75181420057d751814219dde7318142005dd7318142005f67118142005f5711814202efa6018142006f9601814200fae76d894204faf75d894204fae75d894204fad75d894204fac75d894268faf65d894268fae65d894268fad65d894268fac65d894204faf73d894204fae73d894204fad73d894204fac73d8942687af63d8942687ae63d8942687ad63d8942687ac63d8942687af53d89426872f53d8942687ae53d8942687ad53d89426872d53d8942687ac53d894204faf71d894204fae71d894204fad71d894204fac71d894268faf51d894268fae51d894268fad51d894268fac51d8942687af31d8942687ae31d8942687ad31d8942687ac31d894204faf70d894204fae70d894204fad70d8942005ad70d894204fac70d894268faf50d894268fae50d894268fad50d894268fac50d8942687af30d8942687ae30d8942687ad30d8942687ac30d8942005bf75d85421a5be75d85420073e75d85421a53e75d8542005bd75d85420073d75d85420053d75d85421a5bc75d8542005bf73d854219dbe73d8542005bd73d854219dbc73d85420073f53d85420073d53d8542186bf62d8542007af62d85421873f52d85421873d52d8542007b651d8542007b551d8542007b631d8542007b531d8542187b621d8542187b521d85421cdbe70d8542005bd70d8542187af20d85421c5bf75985421a5be75985421c73e75985421a53e7598542005bd75985421c73d75985420053d75985421c5bc7598542006bf6598542006bd65985421c5bf739854219dbe73985421c79e739854219d9e7398542005bd73985421c79d73985420059d73985421c5bc7398542006bf6398542006bd63985420073f53985420073d53985421c7ad7298542007af629854216f3f529854216f3d52985421c5be71985421c6bf6198542007b761985421cdbe7098542005bd709854216faf2098542005bf75585421a5be7558542
  | 28 => 0x874204ebc415874204ef4415874204eb44158742156f62158742004ff705874202cfc705874204ebf4058742004ff75583420067f75583420047f755834201cfe7558342004fd755834201cfc75583420067c755834201c7c755834200cfc745834204ebc745834200cbc745834204ebe5458342006bd5458342004ff7358342014fe7358342004fd7358342014fc73583420067f53583420067d535834204ebf4358342006bd43583420d67f52583420d67d525834204eee425834204eed4258342004ff7158342024fc715834204ebf415834204efb705834204efb405834204ebc405834204ef840583420d6fa205834204dbd76987421edbf75987421b5be75987421ef3e75987421b53e7598742005bd75987421ef3d75987420053d75987421edbc759874204ebf6598742006bd65987421edbf73987421adbe73987421ef9e73987421ad9e7398742005bd73987421ef9d73987420059d73987421edbc739874204ebf6398742006bd63987420073f53987420073d53987421c6bd629874216f3f529874216f3d529874204dbe719874204ebf619874204fb7619874204fb461987421efb6219874216fb521987421d5be7098742005bd709874204ebc609874204dbf7658742005bf75587421b5be7558742005bd75587421b5bc7558742005bf73587421adbe7358742005bd73587421adbc73587420073f53587420073d535874200dbe725874200dbc7258742156bd62587421573f52587421573d525874204dbf715874204fb761587421eebe615874204ebc615874204fb4615874204eb46158742157b62158742157b52158742005bf70587421d5bc705874204ebf605874204dbd76983421d5bf75983421b5be7598342005bd75983421d5bc75983421d5bf73983421adbe7398342005bd73983421d5bc73983420073f53983420073d53983421cebd62983420ef3f52983420ef3d52983421edbe7198342005bd7198342006be619834204ebc619834204dbe709834204ebf609834204fbb609834204fb860983421d7ba20983420efb9209834204dbf7658342005bf75583420073f75583420053f75583421b5be7558342005bd75583421b5bc75583420073c75583421b53c755834204ebf6558342006bd6558342005bf73583421adbe7358342005bd73583421adbc735834204ebf6358342006bd63583420073f53583420073d535834200dbe725834200dbc72583420d6bd62583420d73f52583420d73d5258342005bf71583421edbc715834204ebf6158342006bd615834204dbf705834204fbb60583421d6be605834204ebc605834204fb860583420d7ba20583420d7b920583421a57e75d85420057d75d8542004ff75d854201cfe75d85420067e75d854201c7e75d8542004fd75d85420067d75d85420047d75d854201cf
  | 29 => 0x57f705855220d7c70585526df6f20585526d57e761855222d7e74185520057d74185520067f64185520067d64185522057f73185521bd7e73185522075e73185521bd5e73185520057d73185522075d73185520055d73185522057c73185520067f63185520067d631855201d7f721855200d7e721855201d7d721855200d7c72185523d67f62185526cf6f62185526c73f42185526c73d42185522057e71185522067f61185522077661185522067d61185520077561185522077621185526c775211855220d7e70185520057d70185526c76f201855222d7e74d81520057d74d81520067f64d81520067d64d81520057f73d81521bd7e73d81520057d73d81521bd7c73d81520067f63d81520067d63d815201d7f72d81526bf6f72d815201d7d72d81526a67f62d81526bf6f62d81526a73f42d81526a73d42d81522057e71d81520057d71d81520067f61d81520067d61d81526a76f20d81526a77a20d81526a77920d81526ad7d769815222d7e74981520057d74981520067e64981520067c649815220d7f73981521bd7e73981520057d739815220d7c73981520067f63981520067d63981526b57d729815220f6d72981520a56d72981522167f62981520b76f62981526b73f42981526b73d42981522057e71981520057d71981520067e61981520067c619815220d7e709815220e7f60981520077b609815220f6f20981520057f745815222d7c74581520067f64581520067d64581520057f73581521bd7e73581520057d73581521bd7c73581520067f63581520067d63581526ad7f72581520076f72581520b56f72581526ae7f62581520a76f62581526af3f42581526af3d42581520057f71581522057c71581520067f61581520067d61581520077b605815220e7e60581526af6f20581526a57e761815222d7e741815220f3e74181520053e74181520057d741815220f3d74181520053d74181520067e64181520067c641815220d7f73181521bd7e731815220f5e73181521bd5e73181520057d731815220f5d73181520055d731815220d7c73181520067f63181520067d631815201d7f721815200d7e721815201d7d721815220f6d721815200d7c72181522167f621815269f6f62181526973f42181526973d42181522057e711815220f7671181520057671181520057d711815220f7571181520057571181520067e61181520067c611815220d7e701815220e7f601815220f7a601815220e7d601815200779601815220f6f201815220f7a2018152697792018152004ff755874201cfe7558742004fd755874201cfc755874200cfc745874204ebc745874200cbc7458742004ff7358742014fe7358742004fd7358742014fc73587420067f53587420067d53587421567f52587421567d525874204ef7715874204ef7415
  | 30 => 0x100280000000002000400000000040000005000400000200000014005000000200000000000000000c000000000b00000000010012000000b0004004000400000040000000000000c000000000100080000004000002c0030004006000c0000000001000400600000060057f73d91521bd7e73d91520057d73d91521bd7c73d91520067f63d91520067d63d915201d7f72d915201d7d72d915270e7f62d915271f6f62d915270f3f42d915270f3d42d91522057e71d91520057d71d915220d7e70d91520057d70d915270f6f20d91527157d76991526f57e749915222e7f64991520073f64991520063f649915222d7f73991521bd7e73991520057d73991521bd7c73991520067f63991520067d63991527057d729915222f6d72991521a56d72991527067f62991521b76f62991527073f42991527073d42991522057e71991520057d719915220d7e70991520057d70991527076f20991520073f645915222e7e64591520057f73591521bd7e73591520057d73591521bd7c73591520067f63591520067d63591527157f72591520076f72591521b56f72591527167f62591521a76f62591527173f42591527173d42591520057f71591522057c71591520057f705915220d7c70591527176f205915270d7e76191527057e741915222e7f641915222f3e641915222e7d64191520073d641915222d7f73191521bd7e73191520057d73191521bd7c73191520067f63191520067d631915201d7f721915200d7e721915201d7d721915200d7c72191526f67f62191526ff6f62191526f73f42191526f73d42191522057e71191520057d711915220d7e70191520057d70191526f76f201915222d7e74d85520073e74d85520053e74d85520057d74d85520073d74d85520053d74d85520067e64d85520067c64d85520057f73d85521bd7e73d85520057d73d85521bd7c73d85520067f63d85520067d63d855201d7f72d855201d7d72d85526d67f62d85526ef6f62d85526d73f42d85526d73d42d85526d77621d85526d77521d855220d7e70d85520057d70d85526d76f20d85526dd7d769855222d7e74985520057d74985520067f64985520067d64985522057f73985521bd7e73985520057d73985522057c73985520067f63985520067d63985526e57d72985522076d72985521256d72985523d67f62985521376f62985526e73f42985526e73d42985522057e71985522067f619855200777619855220d7e70985520057d70985526e76f20985520057f745855222d7c74585520067e64585520067c64585520057f73585521bd7e73585520057d73585521bd7c73585520067f63585520067d63585526dd7f72585520076f72585521356f72585526de7f62585521276f62585526df3f42585526df3d42585520077761585522067e6158552
  | 31 => 0x4007000800300000080000000000c00500000020008001000c00e0000000000c0010004005000400000080000008003000000000040000040001001800000000030000000000400200140010000005000000000200010020000000c006000000000100060000008000800000000060000006000800000000020004000000000100080000004004001800000080000010001000c0060000000000000100000050008000000c006000c0000008000001000000240030004002000000300080010000008000c0080018000000c00000200000000000001c00000000000018000000000000100000000000000000500240020000000001c014002c00400300000000002000c02900000020000000000c004000000400200000000000000800800040000010006001c0000000000000c001000400100080000018000000400000080000000001002c001000800600000000004009000c0000010000000000000140000004001000400000140040000000000c001001400000000010004003001c003000000000080000008008000c0090008001000c0020004003000000500000090004000000000100000000000000002400000600020018000000c00000040000000005000000c000400000040000000001000400c0004002000000a001c00000180010000000000c0010008004001c001001000000040000000004000400000000030000001000c000001800600040010000000000000000000000004003000800100040000000002000000000000000008002000400000000030000004000400300040040000000001c003000000a00000080008005002400100000010034000000000a000000100380000000001000000200040030000000000000c0004000000c0000000000002000200000000020000000c0050000001003800a00000000000004000400000000000000002002c00000000000008001003400200000010000000001400000000000000004000000000000040038000000000a0000001000c000002800000080020000000000000600000050004000000c0080008006001c001000400600000000000000000800100000050024000000c001000000000000010000000000c0070004001002000000000020000000000400200000050000000001400600040040000008002c00000000090020000000000000380080000007002c000002c00000080010008000001000500080080008004002c00000000000000002000400b00040010000007001c006001800000080060014003000000400100010010000001c0000008000001400800040000000001000c00600040010000008000400000000070010000000c000001400300000000020001001000000000000000003000400300000020014008000400100180000014006000c00300100
  | 32 => 0x10004000000c0000000008000000800180010000003000c0010000000000000000040010004001000c0010014009001000000000000000002000000000080000000009000400200000020020000000400400000010024000000000c0008001000000200480010008000001400100040060000000002800000140000020006001800300340020004000001000e00000030008003000800300000000008004002c00000040000000006001c000000000100000000010000000c0010000010000400100240070000007004c00500080010000000001400300000040000002000000300000030000010000400600000000004003000000100040000018001000000100000000004000000800000040000014005000000200000040008001000000100000050008002000400a00100010004007000800a0008007000c00e004000300140010014003000c006000000b000400b00100000034002000000200000010000000000c0000010001000800d00140030008000000c001001c0000004000000400c0000000000400000000060000002001000100040000000000002000000000050018004000000000080000000000000000100040030004004000c0000018007002000c0018002000c0080000006000400100080000004003003400600000010000000003800000000030004002002400a0004002000000100040020030000000c00500000030000000000c008000000000180020000000000c0000008000000c00300200000008001000000200080030000007000800000000020000007000400400000020000000000000300000010014002000000500300000000003000c001000c00a0014003000000000040000000000001400400000000000005000400200080000000002000000b00080010004002000000500000030004002000c0040018001001400000000010004004000800000040030018000000c00400000000004000000000000000020018000002800200080000000000001000000000010000006000000d000c00200040080008001000c0000010000000000000000020000001000400c0000000001800000000050010004001c0000018004000000900000000018003000c000000800000080000000008002c0050004000000400000100000000008004c0010000005001c00000000010008001000800000000000008001000000100000010008001000000000000010000000000c0000004001000c000000c000000c000000c000001c00200040020010001000400300080000000000001400900000030008003000000100000070000000001c005000000000180000000000000000100000000018000000000000040080000005002401400040000068000001c00200000000000005000c000000800c0014000000800000000000
  | 33 => 0x59a05703699c883d8800084d000000000000000000410800000015ba2e900000000000375840a49d80e8761000010ba4520bd1b5c2b880005d39f705d09e6872da37284818c2000000000000000000000000048c38286ea7628be403800000000000000277e458000f000400000040000004002000400100200090004000000400000000000000006000000200040040010002000000400000000044000000000400000010004000000800300040010004001000c00000080030008013000400600080000004001002400100080010000012001000000180000028003001c0060004000001000400040000014002000c003001400f005c00300080000000000000400000080020000006000400600000070008000000800500140000004001001c002000000000080000004002002400e000000000000020008002000400000080000010001000400300040000000001000800000080090004001000800200000020000000000c0030034000000c00400040010000002000c0000018001001000100000020004001001c0000000004008000100080000000000000000c0000002000000f00280020000002003c0000000000000000200000000000002000400000040000010001000400f00280000028002000800500040060008001000800000040010000003000000100000020000003000c0010000000000c00c00380010000004002c00100040090010000000000e0000004000c0010004000000000100040000004000000400100140010020001000400d000000100040000000002000400000000010000000000800200040040010000000400000000010010003000000000040060020000001c002001400000380000010000000000400000050000005000800000040030008000000000700000040004000001c000000400000000050004001000000100000000004002000c0010004001000c0000008002000400000000010008000000800000140000000000000800100100010000000002c00400000000004000000400100040000008000000000000440020004002000c0140000005000400100200000000009000000200000010000003002400000000010008001001000000000010008000000c00000040020008000006c00000040000010000000000200040040000005001c001000800600000010008004000c00000040010000002001400c0000000000000300040050038000000c004000c000000c002000400000040000000002000400000200010014002000c002000400a000c0040004000002400400000000000003000c0000000001002c00000000000010001000c00100040000004005000c001000000000080070000000003c00200080000000002001c006001801b0004001001c00000000000000006000800100100000030
  | 34 => 0xa7ea34d8cb014600001fa8000000211e10ca320000136443c000000000000000a9800006de8468706182a4746d1a4e606f0000000000001b209e00000007510000202000000000002b10e9000000003f2000080800001bb9f9c516a24e7a1a1d019894104382342000263800003d40dd0d1e2d0230c1da98620000000298a68c26100002ad80000000000000027e8d4800000013fe3138000000088063d89f05afa80e00003b46089d2a2d08dec000283e698000032780005cb8dfe20f80000500d7c00000007e883f4000000000020c8000000000001ca055127a0000ce40000000000152e0001dfc00000000001ee2500860477b8ed40001c58314103002c0cde5e60ba86e5800048f8000000000036080000000000666800000000008c7800000014d49711c8a4228000212000000000009ae80009b9073c75f06b241600004d4800077a00000000000037a7f809480001318000000000036f80002588fce0000000000000000011369888ccc35a00003818d1038f9e4e000036a00000000000000000000016c800000000006aba3829098aaa08920f639600000000a8648f12a2724800023a800030122e04ada2d88c619b800015680000a5800028be0000000000000062480002e49b8e5e080003b606487678b361f89bda0002094270a0c250b80000000ef0680800000000249a500009da80003d9800000004ee3da998c05d021a000051c439146aa2099421dc0c8622b90bc4f1000000023846310aee000000082f800000000000001b4c176000054a0000000056279312ca0000000000000000000006908abc7b691c245c19fc00000004d21c780002310845000000000000000000438831099523d492e00000001dd468b948e000000000000005a41b4e92a81c08061e8c357120c805a30e74388de3cc1ed60002064000093400001926dd00008fb80006811c1211d000000017b08db8c5e00006b8000096a8e39e268878b205dd801e00019f2000000035f8000a2d84f000011fc38da66c24198da7fd00006e40b8e9a8260e000000068700020000b563ba189c000000088707e0803809c0001f5c6f021400000b5e0000000314800001d849288c15466f10bd81478e4e45780000000cc09b893ec00000004ae068000000000000bdc59589a472fa0c6000043401b80007a28248129a7566899e147c8275e11b8ad64d6000000013fa0001c6a31e0bb4000000000011e436a9a6268789600898f00143000097216b60001ee60af19621af9ace9d5032a000291838f00006c680008c710a600000000e1800000016fc000000023b1a000000000000225a70d000000011de0000000a4380000001c3e1c600007f49324000079023d80005398000000009600000002148000000026e00000004c10b0c04fa680812800000009aa3160b68020a23c
  | 35 => 0x9d910ca41a80007bb93c091000000001f9a24da34a4ce9fd88df00000000000054885036b000000023320000bd4000000000000000000cf803b80007b0924200000008ea80009ca000000000004bf800001389320f78e860001f960000000000104400000003c31d8c0001cf000000002cb04a2625a84e4f591266290664047955e0001ee000027248b18000497800000000002c1842c33626fea39a6d80000000000062884495c22ae8e16a44000082a8000000000069300008d514cc0001cf265f158872880002510fba00005b0000000000002d8000000000020f276d000021ea2d600024349718000000000081f094a45684b80d88cce0efa5020301d503b2800099d20507b11ef25ffa76600003f037607b416b000072c9d604670000565800081b00001db800015924c853d8dbc9b385423e7913e9eb926e57ca5cc5e800007c5224a00000000000d44000000000000006a88000000239095300002aa000099d80006cd0e0800000c400027f04aa9af6000135009e8c76000000000013f80000000000271aa2d1b688a7800000000000001f4600000005e6a168961887294e0392567800000000009e89da2133930699a13e288d134a0000000000098a39a8000075916873421da08719ca60c9ca40000000000239600008120000000a30800058d824c71f893c61d0000000000000000001b20000000000096b1b380000000000226c00000000000000000000000000008e00000000187c00004aca03000055ca3067b220e60000000623800000021e00a0237e0000000000193600000000000000a448d9e8f2114000000000001c1021d8000254800000023984f50000396899800000000001aa400014fc8d400000001d000000000000000000000000000000000000000000000000ea4000113810880000e61fa000000005fa87b00000000708289a0000b080fb80000000c440000000000000043a8460000000000000005d21cb000000008240000000168e000152230700003791cf469392c21df87ec0a1a85a3371e980000000000133c801116a37a000000001c8454099000022fa00000001c9800008da534534800000026848048d4218206709e127e416086a420b00000000000000000000004480001c0200000009c3a7f264fa4f6000000000017b291b1e487d027a895a89241a080002388fd6000000000001b2000000017d00000000000000000000000000cd000000016ec0001b54113a6785f1035400021968de8000000209600000007d6924a7be00000000538000000000003d0447800000000000af800027026ae0001f48000000083f00002dc8cc4657a17814400000f221ee95e92f44009c8c000000000000000f8000000020ca35027760000798000000000010fe00e8e7e2680b622f38dee8be2476000029077ea0e89fd
  | 36 => 0x51b3600010f46a6a3d60001b7e9af108c7478dca14f2146000251e2fc000016d087400000006360000866000086d1c3a06514b6a0b8fb080f04ec8019cde8e981a047c265e33c94267ff8000000226a00000000000000000000000028f234a8000000000000000009cf0000000285600000000000c72000160c119a89000800000000e6c8919956000000000000000000d281ac1de42d61c2e67d053e96aa0ac2e601d846489de4b79e02810812c0e9810c09997b87da933403180e4000043c9c413ae000003650d29226240000000219a00003708710000000000000019c01fe000099900000000000000000000000005d010061ad0000000000000000000000000a0c05b600016ea0541b20000000094700006d8800000000004129f4400021f2797143c5b0a07e000110e9f603363290426a32a68a1f1270000000006f5055459d00004e71a5e000287894393f2000001a000000000005fe28da236299255c000000000000000000000000000035c8000000045a00000000000000322800000000789a79f2c000009804180000001b220000c020000fac601000000000009ad0000000000000000000000b9e65a80001b28c3000015ee00013e8000000049400000ae890e8dd22f405e80001b800ac6e9800000009ec8bda300442a04055580007f107141e6a1c200025d427d90c8a3612c600028e2000090000000002560000a0099e000012b081e00000000f1845b800000000000b69f500000a523e21e22000252614080007dc8000000000000000000001300000000000000000000ca660e8f1e2be800000001ba0000ea200004b096e00000000408000000000014942a388c2739809277806160001a4801c000070c9fe00000c640002212776800000004e20000000000000000000000000000000000042880000000000000007e0fe27da0001e9663d284c000000047400001e88b6e2d69cc60e300000000000000172a0000728000117e65c000000005d6000000007c20da87b244c00028ba8bf93ca4bc000028f8be058e912400027380001068000000000016d418da7c800016380001f3c00023a461a00000002670a4800000000f6000000000000000000000000001b45769ccc1b023344ef00007ea9e6e476800000004f407b00000001f3471125280bc93c885c05b84000af20001644000268889f03c4000143a9b11d268209e1a89480000000bc293ba4e462880000001a78681800086b8a9a296966a03880008880aca34c800000000000001d8e0000000000131000024c04091d4609a00001950000000000045604f644b0000000083a08d000046880006aa8b32a2c09cc6b183e60000ba000000000ff12be9d8a10e5df8440998000078811800000000018804a30f80007a71d6a46780009250000537940e00000006c5a0fe614800
  | 37 => 0x3848c02d40621b327180bfc40828764be872e000202461700000001c9e81600006c498ae708800060b0088000056a95d80000000f1231ba1b841180008d60df6000000090d814c3ffa1a230e22008e7270800000000000000a319678802a7bc6e893de52085a225f105249f10400a30ca200022ba000000000002220000000000000069f88662cfa4682331b52000000046d00000000e0e0001c4a5b780000002596741000026b24d6823237060d80002a4983e07505a800000000000000000000000004ca00000005d28000000160e00000003748000000000089700000000000826800011e00000001a9000000000000a828b680005f3800045e00009cc9236469000000001ea000027078f800086d8000000128a000288a0000000000258e00011ee560a91a00013888ba0000000000019ba6b0000000090a0000000000000000000000000658032e000000044c800000000004b80000000171c7778000000000000009e22c699fa1bc94f432f236a000000052c156e000000000000008db000044605aa000000024c0000000213e5ca24ca3a58660000147070180004e792160000a7800000002b98000000000000000004ea02448b7000012600000000000829000000000000000000000000000000000000000000000000000000000000000000043e9a400000000000000000000000000ec090800001718000051800000000006fd92583109554000273400025a200000000000a0a3cf9b243d925ba79f91aa71ea18c0000a4470a8f1618c2466a471f76347257271d257e08a9418a3e003e0b48b4486500009f29f04000178a5810eaa821800047c8f14000000000000000001ff60000000000000000017585dc00000000c400001c2c000222a56287540000000000000021b000000015dc00007cc96c80008bb0000576000000000001d99f5e5df1f8455700007f51466861a2be096835000000000001b58000000091e00000000000550a8b2000038e497242ea1980000000000000000000004cc395800000000006f804426ef95e6659a0d2000000085b246a00000007cc0406000000096d800044088224ae849c000000000000000002208000050063922921a48328391800029c94a64a4000069a9ae89bc000015418381708000a0e8a1a4308acc4c81d705bb861875500b4a4320446560d660000232966a1d62e516d20000000923800000000009b8101c000131878380001b9800074609e000015d689999ba53a9da09ac80000000b4c000210a0000000750a2548de196851d986647390be46d884a732800020580722b80000000086e000058084621fc57909ea00028ae03b244a00000007ee0000000135e000000009a85304dc80000001f0800000005f8000000000004910000000000000000000ea8000000119622a80000001e6229
  | 38 => 0x12da63f8000000000082600008ce0a007b01ea256f80003f78000567287e0ab01b09ee00004050000000166696280000001682669192c81690b600024f2000166200000000001c148ad9616587a12800025f4000094e6220efc3dba9160000000000000097b80004348c9a531952a2c882a845980005e5800086c00000001bb0000031c2a4000059e800000008c600000cc000000000000003200d0c37c000051080000000a4a00000008c895b200000000000000282000021f8180000000043300000000000000000000006c40000000000126200000008bc80000001db200000006c280009a5a8606a81ebe1961c6600017e669e903863c1bd69338000105800043120b0174800075700005ac800063b8000000121a00000000001254363800021c000000002920000656000259c0000000000000079900000000ede4e10bf80000000398264c000000000007e60000000668a632936883c000156a16e951e27391ba3ed8ea87948a226140d4e013000023fa3e0000016c000000092980004269be266d800000000000001dba0000b5c7ce000075e035e96b80000000000000000032d22b20000d5861a878400001145a297a640f800025506ae28912d27201bea5b1a7c289e05e0950146e0000000000000000000006a204f816f07226a4a6064bc92683c38526a188c5450589480440e440001f3ea12841c8bb9bc87b300003b700002f8800000014281a802a4000000051a1baa5800aa40001a7c0000000000000000000002289eb800015a8000090a4da9b2c63580009b2a880713149a52b11300000000000216489b800000010820000000000000000000000000330931a42498994d60f08fd0a3b19de3dd04bc87500005bea14a68a22ea7a4006800000c200000000000000000000040f218a00018705cd05ec88899f09691b6a88383223fc25102e88ada00000000000000000163c5b8800049d0000000196e0001756086082a08f98a805200001c380000000000000211600000001dda49a706000033099ce1b187d60000000000000025180000000980000000011500001b40000000000083500005610f367bc0c680000f44742830200317d21f613461111b6c23e207a6f313da197000000000000b280000000cf433a9d5200000008d18ebe6ab010015600006c394c803f0000a31219e000000009d8f8e0d292cc2f9938c760a27400015d4a048000372278e197800028d0000017a01e058a8ee4a3000000004b4354000038ba484000264600000da0001292978a1ac92a00000001ebc07380005e780008f61788589800000025f200002dc000000020c000000000009448f849451c1a00004586600000000000000008847e01a3a3be288c2898000796800000016f60a89d4e68580003d000005d421804470000000069c0ea072400004
  | 39 => 0x9a380000001fa409288be000260a04880001ba03e86f095bc2ec9e6075d000059300002ef14f00002158000000073695f800014520001390000091400020c46e28000a0722c873da4144da197646e24ba0000000000000085480001b080aa000165498b8000689133086f261e2ec0dc238880009e926d40000000000102614100003db0d20609800044410484db1ad800011fe000000012f800025d8000a3598e618000000000000000000000014dc242000000000002b5031a000000000000001f01d6434d1e6c7098f38895a8f47c790083ee1c840000a2c02316920018000a2617b455f80ce6f1a78a4f380007bf81d20000b160b324640d81ffa20e00005b118140001b101f90dde4991fb451000004dc21366a00000834000069b14c266b0e8200024305ff08dc1d90e40244000047506947d6261656b122c9138ff200011c8000236280721220000d383c9800000000004e90000000165c0000000000000069c03a25339732a098000000000030210d480e99be131000061500008f68000000064c59f20ea00000000000000000000000000005fc16aa24b80000000d6a000017c000000003417c06d100000001f3a0000000512236800006960000000000056e00009b001d000085f80000000d80000129800000007aa95100599d2e60b80000218aa22a59fcc328000086404a800018722be1a541892808664857a785800000a129c0000000000000000004109620000000080e2d20000691800000000000000000a120000000235c00022ac000097a0c300006799c003f4833e949228c000000063480000001a9e283a1f83cd00007ec9e5453a0d845a9257c19122ca07f9d5e19c800000000000000000000000000000005e180001ada88889c0f0201ea2e29af98f20000000000142200027d203d963000000000000000000000033e800034ba44800014ae000058e11408ce8891f120a0878645292241ed8000000000000023fe00011f69380828a4a8000752a33a82a035a00000e680d0240645888e00000000000eee000000000023a000018ec425884e7710000000000000000000000000000020400019d6a3690b400000000000000675180e16912d400000000000000a278e620000fc661f9acc00025d87c90000397800005380000001504000000014a00000000ac048980009bd00003b680000000000744037200024dc000000000014d80001e922850f287f99e9a0000d2c0001fda00000008a5855600000000d38000231000000007165468aae0000230000267e00014e40000000000000000000000000000000000000002983518000000000000013a6134a4967690000000000071924be04c968875627b45a7094c00015029e8000012814368841d1631f08da403000047a0000439981c000000000018e80180000199a8140
  | 40 => 0x16f8000000018400028944ba03062a780000000ab230000005990000705800000000008779b5e0000000000152400025da97f8000000009000000002688c5c00014f200000000000000000000058808860001c4000013b297ea010000000000000007a507b83f8800000008ba0000000032800019d00003d6000090c9f10478880626480000000000000190e72b9b189771bd04808bd0000000000000007d4a5640ba96dc000239200027cc00001fc00000006ea28245db80000001550000000000000005130000774000036a260800012d0000077800000000000a4806605dc91c99e84e392e21bd23860000000a178a803348c561919e7608f08587501bf85d181ac91f19e479d000000024b02bf80009e9800037386e455497e84e51de61b680500000000a0a80004458000000000000000007fb0000a068000000000027e08fc00000000000902000000037aa8843cb99346b2800000000003c6a4ea00000000000000000000000000003e508d4000191800000009fd196c0b180006bf881a000218200000000001cdc000000000015e27ff00000000a6e6120000000000000000006fc9b88000000095180009f38da200017d620307a47138e9c0000bfe902800000003f23d31fac6d69022000000000018fa00028aa00011523040000384271443b89863a1000000000000000000217800000008b800013c28af12e61170000000075600000000000000000241000000000000cd4000000000000001ce000000013600001e408d9000075304125eb0b3c53011ae9780e540f480001f2a05676b805c4d3a62c8981d382c00d229801a0e0000d90000039a70c000097a8000490000000000000000efa00024f009d000060a15086ed00004a080000001a824f19194149000000016b83ac0000000000000023ca000274a723800000000000001dec94f896c0d300003ce8000000000000007be000286a54f00009aa000069280002f2000062c04e600000003340e7063787de39303ac0b3800000020c0000000054d00007b900002268e7a7d29458184163e0001a505f5000000005de000000059095f40710dfc735800029a80fa4c68b7e2a500000000000000063a455073e000276034100005fb20a692d979c00017ae000101e00013a20e90000000000000000000e0a71e3cb07200000000000003447a9bfa4ca9648000030aa3400002da8d6ca21800000026503d18ef2000154848a1c0e5fb800000490b00000000000000084201f40001d7e0001a74000000019d9e3a30a82c452c80000000dc60000000000000000027fc00000001d195780001d2271f00009741bf46c780000000000960089e8e780000050000060a08a60f2838863a54888ca75243a01c238c8000052800077d9c5065c8c3400023408860fa021e17b6366a88e8a1000062f8
  | 41 => 0x5fc42e241a5d6868a73fa7922258000000000000000000e720b8000000000000004ee1bbc9ae1be4173000029980000000000857040e6ad1b4093b2060000000000010a0000000000000003380e2461b8000000000000002106cf00000001b0464ea1d832b15260000000000035823c94da00000007c2800000016220000000461800019e00000001cea6d90000000000000000002fd8c32676020a665a06800015a400014ec41d00000002682000000000000000288000000177a000202c0000000000261200022167c300000001a5c29a1f54000000090b00000000000000000000000000000000674853a8b3800066c1f643f6a1242650b460000000000067c000000028e8000255a43c6df115c3448000000055a0ac156400010ba000139a0000000000000068f1012000240213f00000000000000018a2d2800000015cc5481c5a00014e000000002509fee4eb168406a0ee200003dc0000000000000000018a011280003460000000000066c80003d496ac6a280005f31308095000074f800000024f44c71ae63908000366112e4b7036e000000000023f494880001fd19da2f2965858228a074d216000001e69288f5e69a19860001982000002e7c9800000006f000000003a385923ae02f097d99a813523cc1628000000000000000000781952a0c9fae48807f20001bb8a170000448800041c8000000000067a9a9c7ba11d621509da5b394603fa09783eb9fbe00002282e58000000150a74f0000000000078d000076d9bdc803029e1f404ba701000049b103a0000000000000000000001359af40000b521d8215e789267c1eb02a000000000001800000000000017dc04580006af00000000000000275a00021107c6a744254000035880000bfa7480001e3883719ec7ba993c6f394880000000175141200000440000d26671088c0000000000221a00000003d0a7704538aec0de80000000000000000026093a081b98ba8cf80f28198752000000032300a47e29b86738199c0001878057000062f289c0699f0e678887c2a985080000000a24a8343a790d000016800000000000000038980000000000000279a8388d96000000000021e2000000032200000d200180a980000001c82000229830a00003a323bc0c6141e5b809720000000000000000000009271e56000000018a80000158b9a10900006fb1e7095680009078b2e000000000000009508000718a5824f924b211b10ce6ff09fe5a19462284185800018f85e50000956188a0001fe2000000000008ca0001e7c00000003789e2e7c092520000d7000003ec5c680ba3a608a8000000044d0000000239400017be11880002bc22c000028fe3d398cc00012e4667a2ae000262873899ae07e01181fa28585c188c04039e3098f19dc16319aa000000000000002fd00000000000
  | 42 => 0x227e20d8000000000025900000000000000154426e00004c300005ac10320c9a6dc00000005110d861c2928e36900007ac87883bd80003428000000000029f1ef6a41a50434925942a8138083796f8125a12680d85da0000fdc000000000000000001a3200013283b1800072600000000000000000000000000000000000000000000002f3000029d1b927642532000000070706d872705145d8810e0e5a2805218b1e86827184969fc80000000a0800000000000000000048e27c07e30f509f89e8214814bc16580000000000000111a85a800000016406ed8c4a20b800000000000001c8677d000000026a40001eb000018800000c3a000154e5f789221f080000000000000099a8a88000000000000000000001338000000000011f48f9a330000000095b1d2487a8000000063ca0a1c9600000000001edc000264e49180000000ce284700000000fcc3558fe6000001600023a266980008d5800035b991400028c09b1800058a8f808fa1d0615d03841dd01080de245600001420001cec00008f4430052e0000000000000000011ca1251b8097e1a5a54b124e00025a69fa00f41cd980a7c19c1e2fb800018f995a2028eea000020e0001e2c00000000000ed06a5000035e00000001ca07d9899e01980000000000000000085500008569e461e70c609060000000231a00028cc0000b3800000005b9051a000039e0000000000013000000005e8897e00020b6000000000010ec0000c7a89a287441f82b800000000000856000000088f89be86a800088b0000000007c87d864253f80008e2000000000000000000000000000006d2000077a000000098d12ee0000000023800080a87d41a99eec57b07faa410c6a000000000000007c0000034087ee0f693b028b800000000000000c8478401dc2fa000000015fa0000000000000000000000000ecc850800052880640000000996000084e223800003940000000000195c00000000000000000042a653800022480006231b2800026103730d067f021e65f213b409380d8000000018880007a101585bf9de200000005a8000000024d40000c6659f91bc0000000699000005d95e000004900ce000060819545fca1dc41f06fc19a80003bd00000000000000047200014e257a80009ca8e3a7ab95182770a4000027722971cd20958e644d0a7584f409120b000001cc05881ee9408271238a0001b660000000000000000000001db054c00000004fa80000001f884c49994000000015f173c4141d320000000064069e43718088fb0eb60000000000002c000179200000007760000000262a0000000000000091680005c9934403580003b59b2649313d2742241c000166c00005e837d03ea306800066398ce55d86989d180000000000000000000000000000d52000000075b0dc45f4254a27a
  | 43 => 0x22826a9a70c0000000611000000000000000adc11a17785c083428170046256800056680003e4256809780000000000556a5fc1ff016400000009d0000073218b885b800000008209de0e8047006f81ab019e84b99ee40b800000000000001e5ea498faa00000000000000000000060687dc9a604d896327b2000000000000000b8a12c05ca1f46211c943050094126a04c20900000000000000140a00001cc00000002af8000000178400007805fda59e00000003530000000098e000000031c000044221e800024a01e2a0d80000d160001d204df0b4e00000006f7800011fa8e899700004a68758000000000000000000000000000000000000f000000000000000000000000000000000000173e00000005f68000000000043c9106000113c00018dc5d780009ba2854325800002f062c00024082b4a76c39c8ae8000000000000000000000000000047700000000000000000000000009b78de01d6870c00019982d91e320a2800085c994029c00007e78f7e9b40000000160a1940e2a39411cc39d178e4531dd600000003880000000057e80210da115a52c00000000000c129ef800010783ce0001c520858c9c563800000000000000000222800000009a85f29c3800000005b623fc000060c00000009da1e1e8ec076800000000000a5e3581dca1d322a000004fa7da1fde5c39b780000b8846a24a400000007ab1f2a0000a1892300000a517ba00012880000d1a000005400000008b900a042c80000971646000000000000002a2800010a00000000000000000000021c80001978574092c000178c3319ac0000158c0000f0812780004a516e85c49dc067f80002620000000000000024f89c4803826e8000384800086c80000000baa0001e780001dc21611c9000011b0000252a8cb0296000000010c21a4a06146c00000002fc80000000120194800009f0c925fd0000000197a77f80000000db800020a200013400000000000000000000000000e1a000000000000000d0000000026ac08004ae00020d656d24924749e6a04a8000000000000000000000000000121c7f09af288e80008a9953e077895e00017d849f80001aa8000000082674c000034e80004698d647df8fc436c03d6078802a0000000000173600000000000000159800004f000000000000000544000000053e27aa27f00002809b306441a726ff994875c822e5070e2c0000f0a00009d400000004ea8000000119a0000000000000000000ae9c700005c2000000004040000000004000000024120000000000000000022f00000000479800000000000000f98000000085580000000000000000040a000079103ba6820000000000000001b89dd15a058a16b42b20e6848785e47118c2e00020ae0c580000000000000000054c800012c9c3c00000005b6800
  | 44 => 0x94e80004fb80003e69610284800004112142c70000000000000000000000de600000000000000a1b000000026905a5800000000006cf8000000279025700009748000000000076b11e07431b9899080000001a847d58000000091c00000004de06d6000124834200001e095a60000a88000000000000001b70000000000000022280000000000062e000204e000150682710f808b00001a880008fd852a000000098c00007828a6c61580000000e028f4138a00000000001566000000021a00000000000000000000000005648e520000540000292e7fc06347a82742463930262d9eca000127022b1b1400000004d50000a4a0000000000011900001ec800000008901ea00000000a3200009c60000cc80000000000122a000000000000000000d8c48c836c05581365190000000142c74515c60000402136a10600000006ad80000e2a3f096fa17c3ef0d5458c9b82210245e99e80000000eec084a636a4919f829080008069fb00000c945c9000000002e01d4000000000001cd18ca0001dbe4608000143873a0d9120a00014a4a1408d0000000000000000000000000000000000000000000000070441b28fa00026a23ef80000000000000000000000005231fdc631a9028aa800093080000000000000142a00000000d9a27a000210c6c013223ad05ea0000000000059400000000000000000000000000000001e18629800000026cc4db8000000000000002502d80000426000000015b885e80007598000000000000004ea20000005a5081e0001e8073380000000000000000000027e024e24544a18000000190c0000000000117c9ad82b67179bd200000008d38400000229c39705f06c099d051500486e6874257f000000009f284003903c7187673e923a87c27b046c928075a00008898288000002250100005ce28d230380000000000000000006380008829326545800000000000000d1419a000014b000019b0000000077c0000000091812e00025ec81a916241820140002192000000050f8684488851257a0f5458b9f7c00023f830d8000364800000000006bb00000000000374074a0000000000135a0000bc60b981ae4b20000000000019fa3be5a980001e30ba67b1975c13f800000026ea000000000021cc00015408f9194a6f614989be854e66d233c94c12ae000240c00006ec3861e4200000002c919308fc80003f29df88189ca652a0aac58d000091814fa2ee021402f90a87108000007107023e9dc6000101a36295aa00009ca5cc16d00dd80002399e580000a769018000000064e0000d004e5a5de2918b183f09e280000000311809a1fd98e224e800049c9ac40000000357877297580003f00000000000057f9dc81bd8000000000000000000000000828000040d96060001142632000000003689bc9fe888ba0f800
  | 45 => 0xed800000017aa000000000000006c205d000023d24958000000000000000009b5800092d208ea00079278000009b0000000000000000ed20001ef423904e8a3c000037e00002ee800000000000000000122000000027fa00000005948e920718000000277c0e00e146af80000000ece38e13f650c00001d788d27f1800038d000000000000001594000000026b80008b4980c3928f923e90000000000000000001ef000042104d073000004a9932c0000c741caa47e90e113a09614baa1b86ba5d1033aa371c5431311a0000260400011123871be800018e000011d833680000000000744a45c9c580009701e6622c9f1c36b80000001db0871931e00000009e0812400007620278a7e4e1976a000000011e827247b00005ab98d022f2852a07884232ba2cc2ca912a8eb07aa3af28c866f000e4fc1ae06b6a92c94f1a2000280005b01624441000054e000012080002d524fe3ff0000000228872e82fc64b83ca86e9d3a1519cf896c1d7a000070012a94c492f1cac45b0000000000000020ce64c83fe288000030b0000922226490aa3b422700005c4000049a80000000000a3d8612000016e3d2800000000002940860000000000003448f8800060c00004cca16641999380000000870240000009740000000000000000000000000000000071a15200006c7114800000000001e0675b81d05c89c5c6d5800000024d80000b803de9790000000000000009bb1ab210607c85c61b946be800037500000002258000055c51e92c08610ab80000000755a0023e28bde0000000662800023600000000000148a722022a8fc00002de6d28000613a07009b00006e1000082200000000b9c04e1df20000f0677480001670000000000000000000001f920001f7a0000000000194400015d221a80000001e080000000380133e2e10000000000056b80000001c0a5d9800000018b42958eae04e800059b800055d0afc7668000000000000012968d100000001d62000000067080000002736000109487285980000000000000000000009f108b000000009cc00008faa4701d1291e916048a96480f058b000048d1530083000000000000000bbe00023fa9cf944a0000000000189a9bba02691b976c0000000a351ac880000004d7080247e010a5019ba01a302843811a3400000005031daa5ae9840000037e00000004d580001678c0a000000000021e43329618000000000022de66121320000b7815a0420558046a4ff074e04724d00cb0000000000099000000d580000000000000188227d0000000000056620807f59a1289321fa3e88a84627892a6ce9c566a5800000000000000000000000058480000000614921a1ce30823b86999ab81900000784881c50e00009b09b9e000064a4bf00000000ca8000000000000000000000424969e000000000000
  | 46 => 0xfa8000000000000009661a10417a5740001432000257000000000000000000067a40580006a300009118000000000000000003090000000000042b0c826bc270a2fb0000000000000025560001d1c60d030811305fa1fc27e600000003f60000520000000000000000000000000000000048a682b400026f60000000000268617c80009e01cee0001d5a00000000000ffa61808d618683b08d8000020d1fce1b3a7501f1829c22998ac000277a0001580170000000000000000000000000000000000000000000000000000000000b8a00000000000000000122e5f8932e0000000000000000000003d200004620000066a14c97a000011485780000b3072a00004590918958000064100004be0b28621905c99c80009c1907693790887b3800048200002b3a5ce9310cee00007a01e5800095799c880b800000027ec73500004b101448b080005cb15b608e800063a8000462800086f80007871f8e00000007cd80009b98000000000000000006bf03884510702000000080c0b7641e00004f304dc00000000000b120001b600211aa827e84469f58000988000033980005c109048c5a8ea64280002798000561800000000001cb0fec0001b760001a22000137403f9d1a64680583fd91be3d69366000000032e0000000000000000005449e3609e00009a712d600024160bb20b404d02f6016a4ae0f901aa9548b105fe00007e0800052580009831ad40000000000194c00000000878000000144e33a000000000000000000000000042180000ed941a6a3800038c000000000001ff85ee000000000000005f180009599a5200000003b21780000000096100005bc8000517800085d164e000000000001fa1be800085200007e60000000000000026aa07c8000090800017e0000000015e3cf000000000007b600009088000265a2b08150000000192a0002314000286457022d489417600b406e2420280a5fe8a4c794000069b9ad68f192ea000000056c04806ee9d869b201683f507ae3a68000641800098600000f19c48a4027ba17396a84ef8af46129ad022d97c27648126399919879ea72699492d88a411563ac8fb4587147c7dd043e1320cba0001a44000000000000000000b7c0000b0e423800094303fa00000000000000000000080f999043600000000000000000000000005249caa18380000001f6c00000003c112ce2f11cfc00000000000000463000079c8170000283c000175257100000f8a404000000000000001d7000014c8000000000000000001b3107a0000000918a81659d8c180ec800000000000000000180a03200015a293ea82c6f99ea621316606fba3dc451800084e8c0c263068600000008cd9e8e00011768588ea64f700000001716000000000004860099ab000014462d4041a00000004
  | 47 => 0x68a892631880001528000000000000000000001f1800016c870920b240401a25c319500000a9c000171e00000006ca800000000009d380004278d741579fa65281172668000099100000001b7296d000097089d80580cf67f9102c00025bc0000000920819c8a523240001054000000000000000000000987000000000009f792040f30000000000095b8000000000054d800002d80009fb9376000160210300000000c26000097008800000000560000000000016a200000003878d5a59c11fa000000000025062b780002f000000001aeea0120ee2f6a65633b00000001114000000084a82d600000000000e7800000006b9000068e00000000000480000000000080000ec4000000000000003faa07600026d25d303469b6a0225c82508a10170a000031255c0f780ac800096a000000000003ca9dbc427177251ca0e4509141478aa202a1c904c171000057d88649e306900000000365000000017000000c8e00000000001ac29348a0676623c03018caa00022a45b983ae74d85a00c5249075d800057201e86261eba69600009e782086d090fc044a8709ed80000000b700001a98a39000000000009ce8ec26ba8000833000000000007b50000000000060580007c58000874800055e861e00000007b78000229041400000000001a8600018fca0180006c1800000013ba0001fd000000000001a360001f600000e480000000000272e000236673a10d6216984c00f27ac00000003089d2c2858928000000017d981e00000000001a7600002fa9be17642b4214ea2894b44c297747031adc938a4ac000093e2050000000000000000000000000000000000023a84d3110c514252e2b09e048621cb49468b2600020f400017680000000635248000012780000f8c000000000021a800013f40001c68a2f0000573800000000000001cb837e800000000000000000000000043780000000a8c0000000000000065f800000001b63d58f86130800000000000000000000096e7be800000000000000000293a5160000000000000084f25200ba0000000000014580000000e88000000032600003701ade67d92a000014b87ee918448187a63bf80c800000000000000000000000000b253b80005af1eb49890000000106e3e988b413900000000000000202852a8eba71c800094280000000000000265a000000051e00000002204368033c8541f2217280008f1000000007ce6de88620000606543210423ba25e06f8000000000000000005c523c2000000076225f00001894000276e000263e00000000000128274000028e000073103524ac800000023ce32f8000000000032da2d000012f600000009999c700002518685000003509200000000000000054520f00658000811984606922b89f7235a15d949c6db8f9600000007bf13d800000000000
  | 48 => 0x12189cb091a05f8f709550fe48e300004e0800000016980000000000000083802aa1179dcc1c418240b22442498187a51f8000000031e000000000000002b62810000000000008e88900000238003000000003b81fa82220ac646400000000000a0885860000000440000000000000000000000000000008100001bca000221413780006b486fe35e90340001c6e000228600000000001f4200028ac7f280003c412bc000269a85d99020000b8c000210203a8262547037c9850000000000000005e255880000000000a258000000000000025a000027204711c0805680dc000000080e06380000000000000000000002f48fe0000000000000008b988988ee8cfc98e88327600000000000000016cc000000000009b600000004a7956c60a83008aa0a0c3a280000ef120e00000000000000630000000000000000000499835c000068e68b2304000068864a1ed00be0ddc000142000000001a680000000000000048e4e490a40298000362261a0000d3e00000000000000000023800000007db8000000234c6420000000239a6e928a8a1f1922000000000008940000b66867000014d0000166891e83b0d3c7faa90a000232e000000011d80005728000a109ea80000bfa7520d7616b80802c10df228a226200c8000922800017203a00c10000000000078f000055f2788000000068c145c0cc80008d7954c000259043180007d8a0742f5a20c82ea24804691c61798db24cd8d480b90fb2769a6486cb94be6168f7628705363fe249800000000000000000228a000000070a056c992816a1c487d200026a60001650000032400009e40000000000000000014d000000000000000979800039b80000001d02651a74c0000a7a0001dce9f4078e00022fc12100008b110aa2280b3a274a8a60002914a111806000000000000007de1f280000000000061c5968bac00016141b5000064795f06eb909089c800000022760a68206000250000006bc0000000000000000028a46b880000000470000000002a20524d8a3de383000030f185e9110c7e05e106487f80004f814ca000000091e8000000260200020bc0000000000286800023b6000230a000270211f2846220955826f000061080007d31d9c7e19fbc15c84b600017bc21108f093300004bb000076a173a00000003da00003e0800000000000001e0c6c30000000000000000000000ee400000000000000000000000000000000000000000000000000000db68c200409f18fee89112b400000002e1800040600000000b90515965e03e104ea339ed200014747ad8d0e2e08000267000025988467a799262011cd877a82643df0bb61cc9cc264900002b90000000279c1c70c1e600800059c80007fe253628a80006eb1a186e7000041892ac695912068f89b290e87da21721a636e937a0000e28
  | 49 => 0x40a930e00000421d00000000000000010049ff80000000c90792a0fa39f00000000c485869490063205e7a909b46d40b14232137e5bd2704604850a0791af81c7a2421aa00002bda1308c0949e000287a4e611289bf0ff44a900007771f9090f8a600000a1e42b93160000968812181864482603e709ee000043a6829ce45bc000095400002dd000000000000000ea00000000000290862a8d9c8248bae16400001d2000076524fc0000c6c6dc000077c00002458000000000013c830e5e9005200027966ae810274a2578821000028f0e9407d8000000153a72f01ee0000000000000000027d400000006190000000000000000009a480000ee00009e1800043d80000001bf07cb80005a6a2b4000279402e09c8998a66e2de8ab42db28b833fa5ca52100000769e88000000032c8000000000000000000000f5c00000000001754484000000000000001fb600019cc7cc97a86621c6c0000f72000000031687083b98552881800000002ee061950e64003202baa32a72699c66d217e40fda3120000000a381a1a68318b20001b8c0000000000000027586200000db43c880008eb89a6484881800000000000000000275c000000000000003c923b20000ab081c800045d00000000000000000000005a60000000141890c000214400000000001c362c0a79839d800076e105610d91ac0000000000159000000004aa128433c1c7665919205529400189800061b100a00023760b08f205778dda00000000000000000079e7d3a34865d0c16000254e196981000000005228d4a00000002faa5e4540191c000000099a84c0927800000000000809bb200000007fc800000000007e5000093a0d300f629300000000000000000000000000000000232800000000000b34000000091404e05a3117a034905a00007944c5000000000009510000a0d8cd62810b0a8c989400a38000765806a3ab164a00000000aba56200000000000000129000000013e618ca8de00000009038a3000000000000000000228e0000f325b296d6000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe571058d5204083caa20b1aa40800e9ba1d62548102163743ac4a902041c6d8758952040074d90eb12a4080038ba11625481000716c22c4a902000c6f7358952040018dae6b12a4080069be01625481000d36c02c4a902041e67105895204083cd420b12a40810799441625481020734882c4a9020058bd845db420400317908bb684080163be1d62d081000d57412eda102000c3f535db420400187aa6bb684080eb2ba0976d081000656c12eda102000c3f525db420400187aa4bb684080eb2dc4176d08101d65a882eda102000a3f83597420400147b06b2e84080028fe0965d08100051ec12cba102039c3d725974204075c6e20b2e84080eb8d44165d08100070f42ac7a102000e1d8558f420407393ae4b1e840800387d4963d08100070ea92c7a10203ae971058f4204075d2a20b1e84080eaabe1d62d08100071742ac5a102000e2d8558b4204001c5ea6b1684080038b54d62d08101d753882c5a10203aeaa1058b4204075d4a20b1684080f7aa44162d081000c5ec26eca1020058bc84dd9420400b1d905bb284080123d20576508100263a38acaa1020398bd87591420400b1790eb2284080132d1c564508100266a38ac6a1020058ec8758942040099c8e2b1284080023d61b71508100063ab2ee2a102000cb564dc542040019aac7b8a84080033958b715081000d56416eca102000c3f53dd9420400187aa7bb284080262fe0b765081000657c16eca1020098bd82dd9420407395905bb284080030fd4b76508100061ea96eca102039caf20dd9420407395a41bb28408002abe0976508101c55a40aeca102038cb4715d9420400187ea6bb284080030f54d76508101d45fc12eca102000caf825d9420400187ea4bb284080030f54976508101c65a40aeca102039caf205d9420407395a40bb284080e72dc4176508101ce5a882eca102000a3f83595420400147b06b2a84080028fe0965508100051ec12caa10203ac3f725954204071c68e2b2a84080e78bc8165508101cf16902caa102039e37105954204073c6a20b2a840800387a1563508100070ec2ac6a10203ac9f7258d4204001c3ea4b1a84080038754963508101c74a38ac6a102039e8f2058d4204073d1a40b1a84080e7a5c4163508101cf4a882c6a102000aad86dc9420400195eedb9284080032b5db725081068f1732ee4a102000e2d65dc942041a1d1cc7b928408003a358f725081004d5743ac4a10203acae87589420407395b0eb128408026ab21d62508100071742ac4a102000e2d855894204001c5ea6b1284080038b54d62508101c75238ac4a102001aaf80589420400355b00b1284080e7a9c4162508101cf55082c4a102039ea5105894204071d5220b128408002ad61b71508100065abb6e2a102000e3565dc54204001d2ac7b8a8408003a958b7150810
  | 1 => 0xa21a92c4081eb9a443525881002c7643aa4b1020058ee87cc962040014dd0b992c4080029b617325881002c7643a64b102000a6e854c9620400155d09baac408002ab61375588100056741ceab102000acd839d56204001c9d073aac4080029b60e755881000726c1ceab102000a4d839d56204085cce213aac40810b9a842755881021732884eab10207ae69109d562040018df0ebaac4080029be0d755881020f33882eab102041e6a105d56204083cca20baac4081039a441755881000557420eab102000aad841d562040014dd0bba2c4080029b6177458810007173ace8b102000e2d759d16204075d4e213a2c4080ebaa84274588101d752884e8b10203dea9109d162040095c902ba2c4080032be1d7458810007173aae8b102000e2d755d16204001d4f02ba2c4080e3a920574588101cf53882e8b102039eaa105d16204073d4a20ba2c4080e3aa441745881000537428e8b102000a6d851d16204001c5ea92a2c4080029ba17735881000536c2ee6b102000aae84dcd620400155b09b9ac4080029ba16735881000536c2ce6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102004ae6811cd620400d5cb0239ac408016baa00735881003574c00e6b102000a6f87d4d62040014db0fa9ac4080038b9d3535881000716ba6a6b1020e4e6710d4d62041c9cd421a9ac40839399443535881073f34886a6b1020e6a6d8594d62040014df0ea9ac4080029b61d5358810007173a2a6b102000e2d7454d6204001c9f06a9ac40800393dcd53588100072639aa6b1020e5e4f3154d62041cbc9a62a9ac40839b93cc1535881073726982a6b1020e6e671054d62041cdcd420a9ac40839b99441535881072f34882a6b1020e4a6e8514d62040014dd0b21ac4080029b61643588100257340c86b102000ae58190d62040014dd0a21ac4080029b614435881000d36416eca902000c6f72dd952040010ff07bb2a4080021f60f765481001c3fc16eca902000c6f82dd952040070fb05bb2a4081071b20b76548100061fa16eca902000c3d42dd952040838de41bb2a4081071b483765481000537c12eca902000c6f725d952040010ff06bb2a4080021f60d76548102143fc12eca902000c6f825d952040838de40bb2a4081071b481765481020e3b882eca902041c75105d9520400187ee7322a4080030f5ce645481022d1fc14c8a902000a3d82991520408587ee5322a4080038bdca645481020f17904c8a902041e2d20991520400187ee6b22a4080030f5cd64548100051fc12c8a902042c3f725915204001c5ee4b22a4081078bc81645481020f16902c8a902041e37105915204083c6a20b22a40800317a1d63548100062ec3ac6a902042c5f7258d5204001c9ee4b1aa40810793c81635481020f26902c6a902041
  | 2 => 0x153590107371b882a6b2020e6e351054d64041c947d0a29ac8080030fd4f72590100061ea9ee4b20203acb710dc9640407596a21b92c8080028fa1672590100051ec2ce4b202004ab4815c9640400147d0a392c8080028f61472590100054f41ea4b202000a9d83d496404001c3d07a92c8080028f60f52590100070ec1ea4b202000a1d83d49640400187ee5a92c80810b8dc4352590102171a886a4b2020008be87949640400117b0f292c8081068f61652590100045f438a4b2020008bd87149640400147d0b992c8080028f61732590100045f43c64b2020008bd878c9640400147d0b192c8080028f61632590100070ea9c64b202000a3e854c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c96404001c3aa6192c808012ada0432590100055ac0864b202005aba800c9640400157300192c80839a9761e7558c100052ec14eab1820e4e57109d563041c9caa213aac60800317e1d7558c100052fc12eab1820e5c5f715d563041cb8bae2baac60839b17dc17558c107362eb82eab1820e6e57105d563041cdcaa20baac60839297a147558c100052f42ee8b182000a5d85dd163040095ad03ba2c60801eb56077458c100052f428e8b182000a5d851d16304001c3ea92a2c60800297a177258c100052ec2ee4b182000a5e859c963040014bb0b392c608003175d67258c100054f424e4b182000a9d849c963040014bd0a392c608002976147258c100062eba8e4b182000a9e841c9630400153b08392c608012b5a047258c1003d6ac08e4b182005ada801c9630400f5b300392c60800237a1f5258c100046ec3ea4b182000a5f87d4963040018bd0fa92c6080029761f5258c100062ec3ea4b18200085d87d496304085cae21a92c60810b954435258c1020d2ec2ca4b182000a9e84949630400153b09292c608002a7a105258c100054ec20a4b182000a5e8590963040014bb0b212c60800297a144258c100052ec2884b1820098be84dd5620400117b09baac4081061f61e75588100052ec1ceab102041a6d829d562040854df04baac40800e1fa1774588100043ec2ee8b102000c3e759d1620400187aeb3a2c4080e6ab60a74588100061f3aae8b102000c3d755d1620407555f04ba2c40800e1fa1773588100043ec2ee6b1020098be84dcd620400117b09b9ac40800e1fe1f53588100043ec3ea6b1020eac3e74d4d62040014db05a9ac4080021fe1d535881074e1f3a2a6b102000c5f7354d62040058b8e6a9ac4080029be09535881074727192a6b1020e8e4c3254d620400b1dd0fa92c408002b3a0f525881000566c1ea4b102042c6e87d496204001c5ce9a92c4080038b5d352588100072741ea4b102000a6d83d496204001c9b07a92c4080029360f525881021733886a4b102042e6a10d496204085cc
  | 3 => 0x29022000be38448520440017c30890a4088003e8d912148110007d03224290220edbe38348520441db7c30690a40883b3b8d8d214811076770b1a4290220ecf635348520441d9ec2a690a40880030fdd274594100043ec16e6b2820e4c7710dcd65041c98ea21b9aca0839a1f61e73594100062fc1ae6b28200087f825cd65041cd8ee20b9aca0839b1d44173594107243f438e6b28200087e8790d65040010fb0f21aca080129da0643594100053ac0c86b28200087e8710d65040010fb0e21aca0800297a0f72594100052ec1ee4b282000c5e83dc965040010fb07b92ca080031760f72594100042ec1ee4b282042c7710dc965040858ea21b92ca080028fa1272594100051ec24e4b282000a3e841c9650400147b08392ca080021fa1e42594100043ec3c84b28200087e8710965040010fb0e212ca080021fa1f32594100043ec3e64b28200087e878c965040010fb0f192ca080028fa1232594100051ec2464b282000c5d738c965040010fd0e992ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca08003175cc32594100253b40864b282000a75810c9650400b4f500192ca080029e60032594100051ec16a732020e6a3d8594e6404001c3f06a9cc8080028fe09539901072f0f98aa732020e5e1d3154e64041cdc3e60a9cc80839b874c153990107251f428a73202000c3f535ca640400187aa6b94c8080272be0972990101ce57902e53202039cad205ca640400153d07a94c808002a760f52990100070f41ea53202000a3d83d4a6404001c3b07a94c8080028760f529901075e1fb96a53202000c3d72d4a640401317d0f294c8080022f61e529901020d1ec2ca532020098be8714a640400117b0e294c8080028fa1732990100051ec2e6532020098be878ca640400117b0f194c8080028fa1632990100051ec2c653202000e1d538ca640400147d0a994c8080262fa1c32990100045ec38653202000a3e850ca640400147b0a194c8080038754c32990100255b408653202000ab5810ca640400b57500194c808002ae600329901002c5f43ea8b202000c3f75d51640400787ceb2a2c8080162f21d545901002c5f43c86b202000a3e8590d640400147b0b21ac808012ada06435901002c5e43a86b202000a3e8510d640400147b0a21ac8080062f21372590100052ec1ea4b2020058be87909640400147d0b212c8080028f61642590101d45f43884b202000a3e85109640400147b0a212c8080030fdd675590100051f42ce6b202000a3d859cd640400956d0339ac808002ad60673590100051f428e6b202000a3d851cd640400147b05a9ac8083938dc4353590107271a886a6b2020e6a3d8594d6404001c3f06a9ac8080028fe09535901072f0f98aa6b2020e5e1d3154d64041cdc3e60a9ac80839b874c
  | 4 => 0x1440099aec0b9c828801374d817390510004bac3aa520a2045e346454a4144001aaae6a9482880034d5d74290510006cab9e8520a2000ab48650a4144001a6aeaa148288003655cd4290510006d2b928520a2056cb870d9141440c98e8edb2a828815b2d1db645051004e5a3b0c8a0a2041c74765494144013968eda128288002ad219425051004e5a3b284a0a2000da77250941440adb66e83828288002f860870505100065b3b0c910a2000ba58219221440cbcc843b2a428818fa908764485103263a3b6ca90a2000e6462d9521440012eb0bba242880163d21974485102b65a3b6c890a2000ea462d9121440c3968ec322428815a6de1d41d011002d5a43283a02200087f855d940440070f90abb2808815a2fe1176501107ac3f436eaa02209ec3c64dd540441e90fd0fb2a80881961f21f65501100061fbaec8a022000c3c75d9140440c7968e3b2280880166d21d415011002d5a43282a022005bb08050540440016e30b20c4088002f460e418811000556c10c89022062cb47119120440014dd0ca9240880029b219524811000717b22a49022000e2c645492044083ec020a924088002aba19424811000556432849022000e2f655092044101c58caa1240880e7e8041424811002c7b436e29022000cb464dc5204400b3c90e90a4088016b9219214811002df0402429022065c7876d9520440c7970edb22408818b2e1d86448110005d4c10c89022000e6b8654920440016d50ca924088002da219524811000734432a49022001e6b765492044003cd0eca924088003cad91524811000794322a490220f3b6b8354920441e76d306a9240883cb9ad8d524811079734b1aa49022000f62815492044001ec302a9240881079ad85524811020fb1b0aa490220f2f623154920441e5ec262a924088003aae194248110005d5432849022000ba8865092044001d510ca124088007aadd9424811000f543b2849022000f2b6550920441e3e50caa1240883c3aad8d424811078754b1a8490220f0f2b5350920441e1e52a6a124088003e8a054248110007d0c0a849022039eab615092044073f46c2a1240883c7e8945424811078fd0a8a8490220f0fa23150920441e1f4262a124088003d854b7148110007d0a16e29022000b71851c520440017630838a4088002f460c7148110007b0a90e29022000fa1421c520440016e30b20a4088002f460e4148110005f0c14829022000f61529052044001f428520a4088003d85494148110007d0a128290220059e88748520440099d0ec90a4088013781c5214811002df043a429022004de087485204400b7c50c90a4088016f8219214811000f70432429022001ee3764852044009bc4ec90a4088013781d9214811000f703b24290220efbe38548520441df7c30a90a4088003d8d952148110777b032a4
  | 5 => 0x80038d8c464549100071a988c8a922000e2f2019152440018e8ed38aa488136d960a715491020d3a432e2a922051b67825c5524400317d093b684880021fe1576d091001c3e42aeda1220018bc845db424400117f0eb2684880028fe1564d09101b51e42ac9a1220058f4865c74244013968c8b8e84880030f19676d09100061fa9ceda122000c3d539db424400187ea53b684880030f54a76d09100065b10ceda122000cb5219db4244001974413b684880032e48276d09100051fc2aeda122036a3c855db424400117d0c3b684880030f19476d09101b51f436cba122000c3e76d974244001878edb2e84880028fe0f65d09100051ec1ecba122000a3f82d97424400147b05b2e84883e30f5cb65d091004e5a3b4e3a122000b35859c7424400172b0738e8488026ad21971d091004e5a3b2e3a12200387e85dd942440010fb0bbb284880021fe15765091001c3e42aeca1220008bf845d942440011bf06bb2848800a3720d76509100047bc0aeca1220098bc841d9424400317d0fb2284880062f21d64509100051fc2ac8a122034a3c85591424406947d0bbb284880028f61776509100045f434eca122000c3c659d9424400155b053b284880030fd4e76509100061ea9ceca1220008bd829d9424400195b053b284880030fd4a76509100061ea94eca122000caf209d9424400147f0abb284880d28f21576509100054fc1aeca122033a9c835d9424400155f04bb28488002ade0576509100045f430eca122000c3c651d9424400187ea63b284880030f54c765091004c5fc10eca1220098bd821d9424400187ea43b284880030f54876509100065ac08eca122000cb6511d9424400196aa23b284880032d8c476509100065a988eca122000cb6211d9424400196a423b284880032bc8076509100065d100eca122000cb9201d9424400196c203b284880032d04076509101a51f436caa122000c3e76d954244001878edb2a84880028fe0f65509100051ec1ecaa122000a3f82d95424400147b05b2a84883df0fdcb655091000717906caa122000e2f65dc942441a3c58cbb928488002ada1a71509100065a3b4e2a122000b35859c5424400172b0738a84880e6ad21971509100065a3b2e2a1220f687c865d74144013878c8bae82881921fe1f65d05100043ec3ecba0a2000c3e75d93414400187aebb26828816a5d2197590510004bbc1aeb20a2000975835d641440012ef04bac82880131dd817590510026b9b02eb20a200097787d96414401356d0db2482880032d9db64905100069abaec920a2000d35751924144001c6eca32482880038d1946490510006ab42ae720a2000d55855ce4144001aaecab9c8288003551957390510006cbb22e720a20c9cd6645ce41441939a8c8b9c828800365191739051064e4a322e720a2000d57525ce4
  | 6 => 0x76399263b12200387e86dd562440c90f90dbaac4880021fa1f65589100062e39ecab12200087e8719562440014bb0632ac488003171cc65589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f19474589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac48800327193735891001c3f43eeab12200087d83dd5624400187e85baac4880030f50b75589100045fc22eab1220098bc845d562440011bf06baac48800a3720d75589100043f438eab1220098be87dd1624400187eebba2c4880030f1d774589100061fa96e8b122000c3d52dd1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f85dcd62440018b90bb9ac48800317d4b73589100062ea96e6b122000c9f42dcd624400193a85b9ac4880021fe15735891001c3e42ae6b1220008bf845cd624401317908b9ac4880023be0973589100046f438e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b12200087e87d4d62440070f90fa9ac4880030fdd353589107561e3a6a6b122000c5f73d4d62440058b8e7a9ac4880021fa1d53589100043e43aa6b122000c3f7454d62441d3878e8a9ac48800317dcd53589100162e39aa6b122000ccc73dc96244001968e9b8ac4883e72d1d231589100166a39c62b1220028f4874c56244193968e898ac48800b351cd31589100072aa9a62b122045a3e84dd9524400147b09bb2a4880021fa1a765491000536c14eca92200087f839d952440010fb073b2a4880021f60a765491000636c14eca922000c6f209d9524400147f08bb2a4881168f21176549100052fc1aeca922037a5c835d952440014df04bb2a4880021fa187654910004aec18eca922037a5e831d952440014bb063b2a4880021fe0c76549100062f418eca92200087d831d952440018bb063b2a4880021760c765491001c3fc10eca92200387d821d9524400187e843b2a4880030f50876549100063ac08eca922000c76211d952440018ea423b2a4880031bc8076549100063d100eca922000c79201d9524408b47d0db22a4880030f9db64549100061e3b6c8a922000c3f73d91524400187ae7b22a4880028f60b64549100061fb96c8a922000e2f72d915244001c5e41b22a4880021fe1d64549100043e43ac8a922000a3e86191524400187cec322a4880030f1d8645491000596c10c8a922000c3f73191524400187ae6322a4881168fe08645491022f17410c8a922000a3d82191524408bc5b04322a4880028b608645491075e1fb90c8a922000e2f72191524408bc6b02322a48
  | 7 => 0x1d7354c644400147f04a98c8883a78d9c5531911074f1ab8aa632220eaa3e8514c64440c556d02298c888002ad60453191100061fa9ae43222000c3d535c8644401395f04b90c8880032b88572191100065610ae43222000a9e83d48644400153b07a90c88818aada0752191100055ac0ea43222000e1e83d48644400147b07a90c8880038760f52191100050ec1ea432220ebc3f72d48644400187ae5a90c8880038da0752191100071ac0ea432220ebe3671d4864441d7c6ae3a90c8880262fa1e52191100045ec3ca43222000cad72948644400195ae4a90c8880262fa1c52191100045ec38a43222000a3e85cc8644400147b0b990c88818aada0732191100055ac0e6432220098be878c8644400117b0f190c8880028fa1632191100051ec2c643222000e1d538c8644400195ae5190c8880028fa15321911000656b926432220098be870c8644400117b0e190c8880028fa1432191100051ec28643222000e1d530c864440c556d02190c888002ad604321911030d5d400643222000ab9800c8644401317d0fa88c8880022f61f511911004c5f43e6232220008bd87cc4644400147d0b988c8880028f61731191100070ea9e623222062ab7878c464441f356b0f188c888326ad60e31191107cf4b39c6232220f9e95738c46444001c6ea7188c8880038d54e31191100065ab94623222000e37528c46444001c3aa6988c88818ba50c5311911064d5bc3a6232220c9ab5874c464440c556f06988c88818ba5e0d311911064f4bb9a6232220c9e94734c46444001c6ea6988c888003a594d31191100071aa9a623222000e95534c46444001c2aa6988c8880032d5c931191100071ba92623222000e97324c46444001d2a64988c8880262fa1f21191100045ec3e423222000a3e85c84644400147b0b908c8880028fa1730191100051ec2e603222000e1d53cc064440c556d03980c888002ad60730191100074a98e603222000e1d534c06444001d2a62980c8880262fa1f20191100045ec3e403222000a3e85c80644400147b0b900c8880032b5cb20191100051fc2a203222000a3c8544064440014bb0632ec4880030f1d764d89100061e3a8c9b122000a6d82dd7624400117f08baec4880262f21175d89100052ec18ebb122000a6d821d7624400187eebba6c4880030f1d774d891000556c16e9b12200087f855d362440070f90aba6c4880030fdd474d89100061e3a8e9b122000aad821d362440010ff0ab9ec48800e1f21573d89100045fc22e7b1220098bc845cf62440010fd0fa9ec48800e1f21f53d89107561e3a6a7b122000a6d82d4f62440010f90ea9ec4883a70f1d153d89100162f39aa7b122000c5d7354f62440014df04a9ec4883eb930c953d89107ce5a3a463b1220c9cb4744c762440059a8e698ec4880039554d31d89100
  | 8 => 0x7a96c8880030f5cb52d91100045f43ca5b2220008bd8794b644400117d0e296c8880022f61c52d91100051f42e65b222000a3d85ccb644400117d0f196c8880022f61e32d91100051f42c65b222000a3d858cb6444001c3aa7196c8880028fa1532d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100070ea9865b222063ab6810cb644400156b02196c88815aaea0032d91100055cc0065b222000a3f855c764440014790ab8ec88815a2fa1f51d91100045ec3ea3b2220568be87cc7644400117b0f98ec8880028fa1731d91100051ec2e63b222000e1d53cc76444001c3aa698ec88818fa50c531d91102b45f43e43b2220008bd87c87644400147d0b90ec8880028f61721d91100051f42e61b222000a3d85cc36444001c3aa7986c8880038754d30d911031c5f43e41b2220008bd87c83644400147d0b906c8880028f61720d911004e1e322eb3222000a5d83196644400187cebb24c8880030f5d764991100043f43ecab22200087e8719564440014bb0632ac8880021f60f75591100043ec16eab2220008bf845d5644400187eebba2c8880030f1d774591100043fc2ae6b22200387c855cd644400117f08b9ac8880023be09735911000c76412e6b22200087e87d4d64440070f90fa9ac8880021fa1d53591100043e43aa6b22200087e87d4964440070f90fa92c8880029760f52591100052ec18ca32220f6c7571194644400117f0eb20c8880028fe1564191100051e42ac83222000c3e76d94644400147b07b28c8880028f60b65191100045ec3cca32220008bf87594644400153d06328c888002a760c65191100061f3b0ca3222000b1d831946444001c3d06328c8880028f60c65191100070ec18ca3222000a1d83194644400147b04328c8880038d60465191100045ec3cc63222000a3e8598c644400147b0b318c8880022fe1d63191100051fc2ac63222000a3c8558c644400155f04b18c888002ab20963191100051f428c63222000a3d8518c644400147d0da98c8880028f21b53191100061f3b6a63222000a3e8654c64440014790ca98c8880030f9d953191100070f31aa63222000e1d6354c644400187ecab90c8880030f19572191100051f42cc43222000a3d85988644400147d0a310c8880028f61462191100054f418c43222000a9d83188644400195ae4310c8880028fa1b52191100058ec1ea43222000e37655c46444001c68cab88c8880038d196511911030d5a432a23222000e37658c46444001c68cb188c888186ad21931191100071bb2a623222000e34654c46444001d2ec6988c888003a518d31191100078aa9a623222000a3d82d4c64441d5c6ce3a98c8883ab8d5c7531911074d1ec2ca63222062ab68194c644400156b03298c88800387e0d531911074f0f39aa632220e9e
  | 9 => 0x72d95103253ac08e5b2a2064a7a801cb65440cb4f300396ca880021fa1e42d95100043ec3c85b2a200087e8710b65440010fb0e216ca880021fa1f32d95100043ec3e65b2a2000c5d73ccb65440010fd0f196ca880021f61e32d95100051f42465b2a2000a3d848cb65440018bee7196ca880021f61d32d95100062eb9a65b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000c5f730cb65440cb4ed02196ca880029d60432d95103253d40065b2a2000a79800cb65440c90fd0f98eca880021f61f31d95100051f42663b2a2000a3d84cc765440018bee798eca8800317dcd31d951032f2a18a63b2a206487e87c8765440010fb0f90eca880028fa1321d95100051ec2643b2a206587e87cc365440010fb0f986ca8800317dcf30d95100062fb9a61b2a206587e87c8365440010fb0f906ca880028fa1320d95100051ec2641b2a2000a5d83197644400187aebaa6c888002ad60754d911001e1e3aca9b2220038bf8755364440058bce6a9ec888003175cd53d91100051f42c87b222000a3d8590f644400517f0ea1ec88800b279cd43d91100051f42887b222000a3d8510f64440014bb07a96c8880028fa1642d91100051ec2c85b222000a3e8510b644400147b0a216c8880028f60f65d91100051ec16cbb222000a9e83197644400153b0632ec888002c760c65d91100070f418cbb222000a3d831976444001c3b0632ec8880028760c65d91100051ec10cbb222000e3581197644400147d0b31ec8880028f61663d91100051fc2ac7b222000a3c8558f644400155f04b1ec888002ab20963d91100051f428c7b222000a3d8518f644400147d0da9ec8880028f21b53d91100051f432a7b222000a3c8654f6444001c3cc6a9ec8880038758d53d91100061fb2ae5b222000c3c655cb644400147d0b316c8880028f61662d91100051f428c5b222000a3d8518b644400153d06316c888002a760c62d911000656b90c5b222000a3e86d4b644400163b07a96c8880038d19651d91102b55a432a3b222056ab4864c76444001d28c698ec888003c554d31d91100061eba8ebb222000a9e831d7644400153b063aec88818eada0475d91102b55ac08ebb222000a3e859cf644400147b0b39ec88800327dce73d91100051f428e7b222000a3d851cf64440c756d0239ec88815aad60473d91100051ec16a7b222000e1f8354f6444001c3ce6a9ec888003875cd53d91100051fc12a7b222000a3e859cb644400147b0b396c8880030fd4d72d91100061ea9ae5b222000a3e851cb644400147b0a396c888002a7a0c72d91100054ec18e5b222063ab6811cb64440ad56b02396c88815aaea0072d911031d5cc00e5b222000a9e83d4b644400153b07a96c88800387a0f52d91100051ec1ea5b222000e1d83d4b644400143b
  | 10 => 0xb24200087e87d4d64840070f90fa9ac9080021fa1d53592100043e43aa6b2420058bc8750d64840010fd0fa92c90800e1f21f52592100052ec1ea4b242000a6d82d4d62840018bee6a9ac50800b171cd5358a107f727192a6b1420058ec87549628400b1d90e992c5080069b20b7654a1000537c12eca94200087f8759152840010f90eb22a50800e9ba1d6254a1001d3643ac4a942000c6f7358952840018dae6b12a50810799c416254a1020f32882c4a94200087f855db42840070f90abb685080062f21176d0a100051fc2ac9a142036a3c85593428400147f0abb685080da8f21576d0a1000c5ec26eca14200087f855d942840070f90abb2850800237e0d7650a100146e41aeca1420058bc87591428400147f0ab2285080d28f2156450a1002c7643ac4a142001aac82dd9428400147f0abb285080d28f2157650a100054fc1aeca142033a9c835d9428400155f04bb28508002ab61b7250a1004d5743ac4a142009aac875894284001c5ea6b1285080038b54d6250a101cf53882c4a142039ea5105894284001d4ac5b8a85080032d9d87150a1000752b10e2a142009c3e645d741840c317f0eb2683080030f5d564d061000735c32a49042041e68865492084083ad6eca92410801b9add952482107edb5c1aa490420fdb69835492084083cd6c6a9241083f39a58d524821005734b0aa49042000be3815092084001d570ca1241080e7aa21942482101ced5bb2849042006eab765092084073d56c6a1241083efaa58d42482107df95a9a8490420fbf29535092084001f4702a124108003e8205424821005754b0a8490420059e8874852084015dc2c290a41080021fa1b73d951001c3fc3ec7b2a2000c5d73d8f65440010fb0f31eca880028fa1263d95100051ec24c7b2a2000c5f7398f65440010ff0eb1eca880028fe1163d95100051e422c7b2a2000c5f7358f65440014df04b1eca880029b20963d95100643ec38c7b2a2000c5d7318f65440012bf06b96ca880028fa1262d95100051ec24c5b2a200c87d8718b654400147d08316ca880028f61062d95100052f418c5b2a2000a5d8318b65440018dae4316ca881929d21931d9510006abb9a63b2a2000e54634c7654400187ae83a6ca881969da0474d95103253ac08e9b2a200087d82dcf65440010fb0f39eca8800317dce73d95100062fc1ae7b2a200087f825cf65440010fd0e39eca881969da0473d95103253ac08e7b2a200087e8790f65440010fb0f21eca881969da0643d95100053ac0c87b2a200087e8710f65440010fb0e21eca880028fa1272d95100051ec24e5b2a2000a5f835cb65440014b906b96ca880021fe0d72d95100062fc1ae5b2a200085f835cb65440018b906b96ca880028fa1072d95100051ec20e5b2a2000a5e831cb65440014bb06396ca881969da04
  | 11 => 0x480017530238284900e7e86047050920005d0c08e0a12400087f855d361480070f90aba6c29000237e0d74d85200146e41ae9b0a4000c5f7354f61480058b8e6a9ec29002b5a5c15298520056d4b828530a401496c875496148001a5ee8a92c2900034b1d15258520006a7b9aa4b0a4083d4c735496148021ad6e0a92c2900034bdd54258520406963aa84b0a4000d8f7350961480ffb18e6a12c2900436adc142585200266b30ae630a410096f875486148001a5ce8a90c2900034b5d1521852041ea739aa430a4000d4d73548614800135f0ea10c2902034b9d5421852000696baa8430a407fd8e735086148001b1ae6a10c2900023de1d61185200055a422c230a4000cd5735846148001ccaa4b08c290003a950961185200245f424eda0a4009c3e645d7414800187aeab268290012ad20564d052004e57322e5a0a400096f8754b41480012db0ea9682902034b9d542d052000696baa85a0a400096f8754a41480012db0ea94829020f539cd5290520006a6b9aa520a4041d6a7054a414800335f0ea148290026ab219429052000656bb28520a4080d2e7550a4148001a5aeaa1482901ff639cd4290520006c6b9a8520a4039daa7050a41480091f10cb8482900035a5497090520006d4a12e120a400387e851d941480010fb0a3b282900122f21d64505200255a40ac8a0a4000caf7650941480010ff0abb0829000e1f21576105200046fc1aec20a40028dc835d8414800117b0fb208290013391857210520006373b2a420a4000c6d765484148083ad4e0a908290026ab21942105201ced53828420a40048f8865c04148001ad2a4b8082900036a5097010520004b6c2ee890a40058ec865d1214800178b0630a4290002f260c70485201cc5ec3ec9a024005aac8650b40480012dd0ea9280900025b21d525012002cd643a84a024005aac86509404801395eeca1280900034bdd54250120406963aa84a024005ba88050940480014bb07a92c98800e1fa177458b100043ec2ee8b162000c5f7354d62c40058b8e6a9ac58800b351cd3158b100072aa9a62b162045a3e84dd952c400147b09bb2a5881069da077654b102063b38eeca962000a6f825d952c41ff6cf04b8aa5880062f21176d0b1004e5a322e3a162009cb4765c742c40070fd0bbb285880021f6177650b1000c5ec26eca1620058f681dd942c40091790eb2285880d28fa177650b100051ec2eeca162039ab681dd942c400155f04bb285880e32d1d97150b100255a43284a0e2000da77250941c40012eb0bba2438815a2fe1d64d03102b4dbc3a83a0620059b48750540c400b3c90e90a418800e1fa1f75592100043ec1eeab24200087d82dd5648413b8ee21baac9082771d44375592104ec3f438eab242003c3c75951648400b1790eaa2c9080021fe15735921001c3e42ae6
  | 12 => 0x2ad205641912020d37434e8a924000a6d869d1524806d8d8ed3a2a490106daa027454920005b4c04e8a924000a6f865d152480834d90cba2a490002dae01745492020db4402e8a9240dfc6c761d15248001c5ec9322a49006ada60264549200a4b643ac8a924000b4f83591524810769906b22a490002d9e056454920005b240ac8a924020b6b8059152482052dd0e322a4901065b61c645492000716b20c8a924000b2e84dc5524800165b09b8aa4901069ba1a715492000536c34e2a924026c6c769c552480836d50138aa490002da602715492000537c32e2a924041a6c865c552480016d700b8aa490106da20171549206ce363b0e2a924083b4e831c5524800169b0638aa490106daa007154920005b4c00e2a924003a6f86dc152480838d8edb82a490106daa1f705492000db4436e0a924041d6a76dc15248203ad0edb82a4900035add37054920006b4ba6e0a924000b6b83dc152480016d307b82a4900035adcf7054920006b4b9ee0a924000b6981dc15248001ad6e3b82a4900035a5c770549206a5b5438e0a924041d6a871c152481ad6d50c382a4901079aa18705492020f95420e0a924041f29841c15248001ad4e8382a4900035a1d0705492020db5c18e0a924041f4a831c152480016d306382a490107d260c7054920005a4c18e0a924000d6b731c15248001ad2e6382a490107d8a047054920005b4c08e0a924041f61811c152480016c302382a490202cba14645092000596c28c8a12400096d85dc54248001793063828490002f860470509200d5d4c06eca124080b2e851d9424800165b0a3b284900272ba1c765092000717428eca124000e2d851d94248001c5ea63b284900038b54c76509204059742ee2a124000b2d85dc5424807355d0d38a84900032b1da71509204059742ce2a124000b2d859c542480ff71d0738a8490002e360e71509201cdd5404e2a124000ba9809c542480735590cb8a8490002eae0171509201cdd4402e2a124000cac761c54248001b4ae238a84900e6eaa007150920005d4c00e2a124039cac76dc142480737550fb828490006ea21b70509201ced53b6e0a124000da876dc14248001b56ebb8284900036a5d77050920005d5c1ee0a124000ba983dc14248001b56e7b8284900036a5cf705092000795a9ee0a124000f2953dc1424800175303b8284900036adc77050920006d4b8ee0a124039cac765c1424800165f0ab828490202cb2157050920005c7c1ae0a12407fb8c835c1424800174f02b828490002e92057050920105d5438e0a124039daa871c1424803b7550c38284900e7aaa1870509201cf95428e0a124039f29851c142480737570638284900e7e2a0c7050920005d4c18e0a124039f89831c14248001713063828490003cad4c705092000794a98e0a124039fa2811c142
  | 13 => 0xe4e3a2c69088000caf745892110013958e8b1242200163d21d61484400065bba2c29088009cb47458521100070fd0fbaac9100021f60f75592200061fa16eab244000c3d42dd5648813b8de41baac9102771b48375592204ec3f438eab244003c3c75951648800b1790eaa2c9100021fe15735922001c3e42ae6b24400087e87d4d64880070f90fa9ac9100021fa1d53592200043e43aa6b2440058bc8750d64880070fd0fbaac3100021f60f75586200061fa16eab0c4000c3d42dd561880c98de41baac3101931b48375586200045fc22eab0c40098bc845d561880014bb063aac3100030fdd774586200061e3aee8b0c4000c3f52dd1618800187aa5ba2c31015b2bc8374586202b656906e8b0c4000c3f751d16188001878ea3a2c3100021fe15735862001c3e42ae6b0c40008bf845cd618801317908b9ac3100021fa1f535862001c3e43ea6b0c4000c3f74d4d61881d5878e9a9ac3100021fa1d53586200043e43aa6b0c4000c3f7454d61881d3878e8a9ac31000b179cd53586200062eb9aa6b0c4003c7475945618800b1e90ea8ac3103e72d1d2315862002c7a43a62b0c40c9cb4744c561880059a8e698ac3100039554d315862004e1f322eba0c40618bf87593418800187aeab2683100131d98575906200266b30ae720c4000c7575586418801356908b0c8310003355cd61906200043fc2aeca0c400387c855d941880010ff0abb0831000e1f215761062000536c16a7b22400087f855c764480070f90ab8ec89000e1fa1f75591200043ec1eeab22400087f82dd564480010fb05baac8900030fd0b75591200061ea16eab2240008df835d564480051b906baac8900023de0575591200247a40aeab22400087e871d56448007878eb2a2c8904172d1c6545912001c5e43aa8b2240cfcb47155164480051bd0fb9ac89000317dd773591200062e3aee6b224000c5f85dcd64480018b90bb9ac89000317d4b73591200062ea96e6b224000c9f42dcd644800193a85b9ac8900021fe15735912001c3e42ae6b2240008f7815cd64480091e902b9ac89000237a1c73591200062fba8e6b224000c5c751cd64480010fd0fa9ac89000e1f21f53591200062fb9ea6b224002c5c73d4d64480014db05a9ac89039f1d1c753591200043f43aa6b22400087c8754d64480018bee6a9ac89000b171cd535912072e3a38aa6b224002c9c73d0d6448209968e3a1ac89000a2f21d43591200164e39a86b224103cb47150d64480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eea7b8ac8900031d54f71591200063ba96e2b224000c7552dc5644800196e85b8ac8900031ddd471591200063a3a8e2b224000cb7741c564480019aee638ac890003351cc715912004e1f322ea32240008bf87590644800187aeab20c890
  | 14 => 0x6841c9611000156b08392c220002b5a0c72584400056ac18e4b088005af2801c961100015e300392c220002b5a0f52584400056ac1ea4b088000e5683d4961100014eb07a92c2200039560f52584400052ac1ea4b0880ebe3742d496110085c6e81a92c22010b8d503525844004d5b424a4b088000ab58494961100014ef06a92c22000399e09525844022f1ba12a4b088041e37405496110083c6a80a92c22010799c81525844020f32902a4b088042a7685149611001356d08292c220002ad61052584400055a43a84b088000e37535096110001c6aa6a12c220027a9e0942584400071ba9284b088000e3552509611007356f00a12c2200e6ad60142584401cf5390284b088039ea52050961100014ed0b992c2200029d61732584400053b42c64b088000a75858c9611001356d09192c220002ad61232584400072aa9c64b088000a76854c961100014eb0a992c2200023da1c32584400047ac3864b088000a76850c961100014eb0a192c220026ada1032584400055ac2064b088000e55530c9611000b5e500192c220002bc60032584400061f42aed2088000c3d855da411000193d06bb482200032760d76904400061fa9aed2088000c3d535da411000117f04bb482200030fd49769044004e5b40aed2088009cb5815da411010b47f0eb2c82200028f61d65904400051fc1acb2088000a3d835964110001c3ce6b2c8220003875cd65904400051fc12cb2088009c3e715964110013c6ce2b2c822015b0fdc165904402b61eb82cb2088056e371059641100adc6a20b2c822021aa7e1d63904400054ec3ac72088000e1e8558e4110001c3b0ab1c8220003879d563904400070ebaac72088000e1f5258e411001393ce2b1c8220027a59c563904402b64fb82c72088056c9d7058e41100add2e20b1c822015ba544163904400061eb2ae52088000c9d635ca411000117b0eb1482200032b5c9629044000717a92c52088000cad8758a4110001c5d0ab1482200038b6156290440007173aac52088000e2d7558a4110001d1ce6b148220003a35cd629044000717a9ac52088000e2d5358a4110013d4ce2b14822015b2bdc162904402b656b82c52088056ea71058a41100add4a20b1482200028f61952904400061ebb2a52088000e1d6354a4110001c5ac4a94822018b8d9d561904403171abaac32088062e967358641100c5d2ae6b0c82200038dd4d61904400071aa9ac32088000cb5725864110001c6ea4b0c82200038d54961904402b65bb82c32088056cb570586411000b1eb02bb442200030fdd1658844004e1e3a2cb1088000c9f7458e2110013938e8b1c42200272b1d162884403165bba2c31088009cb474586211000b1d905bb242200163d207764844004e1e3a2ca90880008bd86dd1211000187acbba2422000327dd1634844004
  | 15 => 0xb1a84200029d60b53984407571ba16a730880e6a758594e6110001caf06a9cc220397959cd539844072f2ab9aa73088000a778254e61101d3c6e84a9cc22039b95cc153984407372a982a730880e4a768514e61100015ad07a94c220002b560f52984400072b41ea53088000a7583d4a6110001cab07a94c2200029560f529844075f1ba16a53088041a758594a611001356d09294c220002ad61252984400053bc1aa53088000e678254a611008bc6e84a94c22010799c81529844020f32902a53088042a768514a611001356d08294c220002ad61052984400071ba9a853088000e355350a611001356f04a14c220027a9e0942984400071ba92853088000e355250a6110073d4e40a14c2200e7a948142984400053b42e653088000a7585cca61100014ed0b194c2200029d616329844004d5b424653088000ab5848ca6110001caaa7194c2200029da1532984400053ac2a6530880048f6870ca61100011eb0e194c2200029da1432984400053ac28653088009ab6840ca611000156b08194c2200039554c329844002d79400653088000af1800ca611001317908baac2203e72d107735844004c5e422e6b0880c9cb4415cd61101d5c6883a9ac22000b179cd53584400062eb9aa6b0880e9e344154d61100014bb07a92c2203af8d107525844022f1a20aa4b0880628bc8750961100c556902a12c2200163da1f515844004d5b426a2b0880058f487545611001356908a8ac220002b5a0c51584400056ac18a2b0880058f687cc561100014ed0b98ac2200029d617315844004d5b42662b088000e5553cc5611000b1e90e98ac220026ad21131584400166a39a62b088000e55534c561100014ed0a18ac2200029d61431584400066ab9862b088000a7685c8561100014eb0b90ac220026ada1321584400053b42842b088000a7585085611001356d0810ac220002b5a0c21584400056ac1842b088005af280085611001356d093aac220002ad61275584400055bc22eab088009ab4845d561100015ad063aac220002b560c75584407ce5a3a6e6b088000a76859cd61100014eb0b39ac220026ada1273584400055ac24e6b088000ab7845cd611001356908b9ac2200029da1473584400053ac28e6b088000cd5731cd61100014eb05a9ac2203ab8dd0b53584407271ba06a6b0880e4e3540d4d61101cd4eb0b29ac220002ade11535844004d5a422a6b088000e378454d61101d3c6908a9ac22000395e0d53584400072b39aa6b088000e557354d61100014ef04a9ac2203a78dd0953584407371ba02a6b0880e6e354054d61101cdcae60a9ac22039b954c153584407253b428a6b088009ab484dc961100014ed0b392c2200029d616725844004d5b424e4b088000ab5849c9611001356908b92c2200029da1472584400053ac28e4b088009ab
  | 16 => 0x55884020f16a02eab108009aae841d5621002f55b083aac4200029ba17735884000536c2ee6b108009aae84dcd621002f55b09b9ac4200029ba16735884000536c2ce6b108000a6e851cd62100014db0a39ac420026aba1073588400bd56c20e6b108000ae6811cd62100015cb0239ac420016baa0073588400bd74c00e6b108000a6f87d4d62100014db0fa9ac4203ab8b9d353588407571620ea6b1080e4e2f40d4d62101c9c5a81a9ac42039a9b616535884000557c22a6b108009aac8454d62100014df0ea9ac4200029b61d535884000717c22a6b1080e9e2c8454d62101d3c5ce8a9ac42000393e0d535884000727b9aa6b108000e4c7354d62101d3c5882a9ac42039b8bd01535884073716a02a6b1080e6e4f3054d62101cdc9a60a9ac4203929ba1453588400053742ee2b108000a6d85dc5621001355d09b8ac42005eab613715884004d56424e2b108009aac845c562100014dd0a38ac4200029b614715884004d57420e2b108017aad841c5621000159d0638ac420002b360c715884002d75400e2b108017ae9801c5621001355d09a8ac420002ab613515884000557c22a2b108009aac84545621000159d0628ac420002b360c51588400053742e62b108000a6d85cc5621001355d0998ac420002ab613315884000726a9e62b1080f9ea4418c5621000155f0898ac420026ab211315884000726a9a62b1080c9ea4414c562100014dd0a18ac4200029b61431588400076298862b108001a6c82dd952100018dee5bb2a4200021fe0f76548400043ec1eeca90800387f82dd952100018df05bb2a42000e1f60b765484020e36416eca908045c3f42dd9521000187a85bb2a4201071bc83765484020e36906eca908000a6f825d952100018dee4bb2a4200021fe0d76548400043ec1aeca90804287f825d952100018df04bb2a4201170fd09765484022e1e20aeca908041c3f405d9521008387a80bb2a4201071bc8176548400062f43ac6a908000c5d8758d52100858bee4b1aa42000393dc9635484022f0fa12c6a908045e1c4158d5210083c3e80b1aa42010787501635484020f27902c6a908041e4d2058d52100074dd0eb12a42010b1ba1d625484020e36c3ac4a908003a6c87589521008bc5d08b12a42005f8b611625484000637b9ac4a908000c6d73589521008bc5882b12a4201078bd01625484020f16a02c4a908000a3f83595421000147b06b2a84200028fe0965508400051ec12caa108009c3f725954210013c5ee4b2a84200030f1c565508401ce1fb82caa108039c3d705954210073c5e40b2a84200e78b48165508400070f42ac6a108000e1d8558d421001393ee4b1a8420027a3dc963508400070fa92c6a108000e1d5258d4210001938e2b1a84200e727dc163508401ce4eb82c6a108039e8f2058d4210073d1a4
  | 17 => 0x188009a9c845d563100018bf0ebaac62000387e117558c4074f0e422eab188000a5f825d563101d3c3e84baac6203a7871057558c407362fb82eab1880e6c5d705d563101cdc3e80baac62039b875017558c407252f428eab188000a5e85dc963100014bb0bb92c62000297a167258c400052ec2ce4b188000c5d759c9631001353d09392c62042aa76127258c400052f428e4b188000a5d851c963100018baea392c620026a7a107258c400c54ec20e4b188000ad6811c963100015ab02392c620016b6a007258c400c56cc00e4b1880008de87d4963100011bb0fa92c62000297e1f5258c400062f43ea4b188000a5d87d4963100018bb0fa92c6200021761f5258c4075f0fa16a4b1880ebe1c41d496310085c3e81a92c62010b875035258c4020d2ec2ca4b188009a9e84949631000153b09292c620026a7a105258c400054ec20a4b188000a5e85dc563100014bb0bb8ac620003175d77158c4004d4f426e2b188018a9d84dc563101f3d288338ac620003175d57158c4084d4fc22e2b188009a9c845c56310193d2882b8ac62000297a147158c400052ec28e2b188000cd5711c5631001353d09a8ac620002a76135158c400054fc22a2b188009a9c8454563100011bd0e28ac6200023761c5158c400052f42e42b188000a5d85c85631001353d0990ac620002a76132158c400046f43842b1880008dd8708563100014bd0a10ac620002976142158c4004d4f42042b188000a9d84085631000b5b50010ac620002b66002158c4000c5ec26eab10804187d879d5621006987ae93aac4200029760e755884020d36c14eab1080ebe2f429d5621008b87ce8baac42010a9be09755884022f17a12eab10800387e85dcd62100010fb0bb9ac4200062f613735884001c3fc3ea6b10800087d87d4d621021187ae9a9ac4200029b60b535884075717a16a6b10800087f8754d621020f87ae8a9ac42000317dcd53588400162e39aa6b108000a6f8254d62101d3c5e84a9ac42041b938c9535884083726192a6b1080058ee87d49621000159d07a92c420002b360f52588402163743ea4b1080ebe2e74d49621002fc5ae9a92c42000393a0f525884000536c1ea4b108000e4d83d49621000149b07a92c4203af8b107525884021717a06a4b108042e2d40d49621000b1d90ea92c4200163ba1f32588400053742e64b108000a6d85cc9621000b1d90e992c4200029ba15325884001c3f42ee2b10800087d85dc5621000317b09b8ac420026aba1375588400bd56c26eab108000ace839d5621000159b073aac4203af8b9d275588400072741ceab108000a6d839d56210001c9b073aac4200029360e755884075f1620ceab108042e2f409d56210085c5a813aac4200031be1d755884022f173a2eab108000a6f835d5621008bc5882baac4201078bd017
  | 18 => 0x1caaa698ec2a0002ad61021d85400056ac1843b0a8000af18008761500018bce7b2cc2a0003179cc65985400062fb2ae730a8000c5c655ce61500099a8c2b9cc2a0003355cf619854001c3f436eab0a809d87c86dd561500010fd0fb2ac2a00021fa1c655854087e1eba0ca30a80008f7875846150001878cb3b682a00030fe1676d05400061e42ceda0a8000c3f539db415000187aa73b682a00022f60a76d05400061fa94eda0a8063cb6319db415000196a633b682a024a4f21975d05400049fc1aeba0a800093d835d7415000127f04bae82a033f0f98575d054067e1e30aeba0a8009c3f605d74150013a76c0bae82a00024fe1f65d05400061f3b6cba0a80008bf87d8b415000187aebb1682a00032b5cb62d05400049ec3aa5a0a8000c3e7654b415021f0f90cbac82a00021f61f65905400062f39ecb20a8000c5f655ce41500018b8cab9c82a00133518573905400066ab9ec320a809dc3c76d9541500010ff0abb442a000e1f215768854001c3f42eec90a800087d85dd9215000b1790cba242a00021f60b73594407561fa16e6b2880eac3c41dcd65101c987e81b9aca203930f50373594407343ec3ce6b28810ea3f845cd651001347908b9aca200030fe11735944074e1e422e6b288000c5f835cd65100010ff04b9aca203a70fd09735944074e1e20ae6b2880e6c3f405cd65101cd87a80b9aca203921fa1c73594400052f41ee4b288000a5d83dc965100018bd07b92ca200021f60f72594400062ec1ee4b28800085d83dc965101d787e85b92ca203af0f10772594402161fa06e4b288042c3d40dc9651001347d09392ca204368f612725944004d1f420e4b288019a3d841c965100010fd0f992ca200021f61f32594400043f43c64b28800087d878c9651001347d09192ca200028f61232594400062eb9c64b28800087e874c965100010fd0e192ca200021f61c325944004d1f42064b288000a3d840c965100018bae6192ca200029da0432594400053ac0864b288005a7a800c965100014f300192ca200268fa1371594400cd1ec26e2b28810ca3f845c5651001347908b8aca2000297a0c71594400052ec18e2b28800087e87cc565100010fb0f98aca200268fa1331594400051ec2662b288000c5d73cc565101f3c688318aca200028fe11315944004d1e42262b288000c5d734c56510193c688298aca200021fa1c31594400043ec3862b288000e55310c565100010fd0f90aca200021f61f215944004d1f42642b288000a3d84c8565100010fd0e10aca200021f61c215944004d1f42042b288000a3d8408565100014bd0610aca200029760c215944002d3d40042b288000a798008565101cd4bb0f3aac6200029760a7558c407570fa14eab1880eae1c419d563101c9c3e813aac620393875027558c4085d4fc22eab
  | 19 => 0x317dce32d95400043ec3a65b2a800087e870cb65500010fb0e196caa027a8fa1032d95400051ec2065b2a8000c5f730cb65500014ed02196caa00029d60432d95404ed3d40065b2a8000a79800cb65500014bd0738ecaa00029760e71d95400051fc22e3b2a809ea3c845c7655013d47d0838ecaa02768f61071d95400043f43e63b2a800087d87cc7655013d47d0998ecaa00028f61331d95400062fb9e63b2a8000c5f734c765500010fd0e18ecaa00021f61c31d95400072a98863b2a800087e87c8765500010fb0f90ecaa027a8fa1321d95400051ec2643b2a800087e8708765500010fb0e10ecaa027a8fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa02769ea0021d95400053cc0043b2a809e87e87cc365500010fb0f986caa000317dcf30d95400062fb9a61b2a809e87e87c8365500010fb0f906caa027a8fa1320d95400051ec2641b2a8000a6d82dd7625000317908baec4a00db0f1d075d89400052ec18ebb128000a6d821d76250007878eb2a6c4a0002ab60a54d89401d45e43aa9b12800087f855cf62500070f90ab9ec4a00062f21173d89400043f43ea7b12800387c87d4f6250211878e9a9ec4a00021f21d53d894083e1e3a2a7b128002c5e7354f62500018bae6a9ec4a0002ab60b43d89401d45e43a87b12800087f855c762500070f90ab8ec4a00062f21171d89400043f43ecab128000c5c73d9562500010fd0e32ac4a0003171cc65589400062fb2ee6b128000c5c65dcd62500018eecbb8ac4a00031d19771589400063bb28e2b128000c74651c562500c796ec838ac4a00021fa1a765494000536c14eca92800087f839d952500010fb073b2a4a00031b60a765494000637904eca928000a5f835d9525006f4b906bb2a4a00029be0976549400053bc0aeca928040a74815d9525000187b083b2a4a00021fe0c76549400043ec18eca92800387f821d952500070fb043b2a4a00030fd0876549400061ea10eca928000c6f201d95250001878ed3a2a4a025acb60a745494020d1e432e8a92809ab2f825d152501e947d0db2e84a00028fe0f65d09400051ec1ecba128000a3f82d97425000147b05b2e84a025b0f5cb65d09401ec5e432e3a12803dcb4615c7425013dc5885b2a84a00d28fa1b65509404ee1e3b6caa128000e2c62d95425000147f07b2a84a00028f60f65509400051fc16caa128000a3d82d95425013d87ee5b2a84a027b8bdcb655094000717906caa128000e2f65d894250001c58cbb1284a0006ab21f625094000717c2ec4a128000e2c85d894250001c5ea7b1284a00038b54f625094004d56c06c4a1280618be86dc5425000127b0bb8a84a00e32d187715094000d5d436e0a128000eab62dc14250001d56c438284a00029760f52d85400147bc3a63b0a8002cd6734c7615
  | 20 => 0x36c16a6b1680eae2f42d4d62d00018bee6a9ac5a000b171cd5358b4074f17a12a6b168002c9c7350d62d000155f04a1ac5a000e1fa177158b400043ec2ee2b168041a3e84dd952d008b87ce9bb2a5a00029be097654b4088d97c12e8a9680388bd86dc542d000127b0bb8a85a00029760f525874000657b9284b0e8000caf7258941d000956902b1283a018a2fe19748874001c3f42eec90e800087d85dd921d000b17d09bb243a00eaabe097458a400055a40ae8b148000a6d82d4d62900018bee6a9ac52000b171cd5358a4088727192a6b1480058ec87549629000b1d90e992c5200069b20b7654a4000537c12eca948003a6e8758952900074d90eb12a5200778ba116254a4000716c22c4a948000c6f7358952900018dae6b12a5201078bd016254a4020f16a02c4a948000e2f535894290001c5aa6b1285200e7aa1c16250a4000754b16e0a14800387e87dd561900010fb07baac3200021f60b75586400061f20eeab0c8000c3c41dd561900c987e81baac3201930f50375586400052ec18eab0c800087f855cd61900070f90ab9ac3200023be09735864000c76412e6b0c800087e87d4d61900070f90fa9ac3200021fa1d53586400043e43aa6b0c8002c5e7354d61900018bae6a9ac3200021fa1f525864001c3e43ea4b0c8000a5d83d4961900010fd0ea92c3200021f21d525864031c5f43e84b0c8000c3f75d09619006d878eba12c3200030fdd542586401a61e3aa84b0c8003c7475945619000b1e90ea8ac3200163d21d31586400166a39a62b0c8000e55534c561900098ecc2bac832001335985739064031eca20ae720c8000c757558641900019aae6b0c83200032b5c9629064000716b12a520c8000cad72588419000156f02b1083200034b5c9521064000716b12a420c800087f855da21900070f90abb443200021fe15764864001c3e42aec90c80008df835d921900051b906bb243200163d21d61486400043f436e7b2a800387f87d8f65500018bae7b1ecaa00021f61e63d95400053b40cc7b2a8000a758198f65500010ff0eb1ecaa00721f61c63d95400062eb98c7b2a809da3c8650f6550001c38c6a1ecaa000257e0d72d95400e43ec38c5b2a8000c6d7218b65500010fb05b9ecaa00021f61e73d95400062fc1ae7b2a800087f825cf65500010fd0e39ecaa027a8fa1073d95404ed1ec20e7b2a809d87e8790f65500010fb0f21ecaa00029da0643d95400053ac0c87b2a809ee1c4350f655013d47d09396caa00028f61272d95400052fc1ae5b2a8000a5c835cb65500010ff06b96caa000317e0d72d95400042fc1ae5b2a8000c5c835cb655013d47d08396caa02768f61072d95400043ec3c85b2a800087e87ccb65500010fb0f996caa00021fa1e32d95400043ec3c65b2a809ea3e848cb655000147b09196caa00
  | 21 => 0x8250d62104091d90ea92c420826aba11525884122f172a2a4b108200e2d5454962104091d90e992c420826aba1132588410166a39a62b108200e55534c56210593d2e8698ac420b27a9d0931588410076299262b1082018bd84dc1621048b47d09bb2a4209170f9d3765484100d36416eca908200a6f825d9521062565f04ba2a42080e9ba1d625484101d3643ac4a908245e2e84589521044fc5b08b12a4209178b9d1625484100716ba2c4a908200c6f7358952104018dae6b12a4209178bd0d625484100716a1ac4a908240e2f415895210481c5a82b12a420903998c562548410073298ac4a908200a6f80589521048bc5880b12a42080e1fa1f75580414f61e3a6eab00820087d83dd560104010fb05baac020a7b0fd0b75580417a61e3a0eab008200a5d831d560104014db043aac0209862f21d54580410043fc2ae6b00820387c855cd60104010fd0fa9ac02080e1f21f53580410043f43aa6b00820087c8754d60104058bce6a9ac020803175cd535804130c5e43a86b00820087e87d4960104070f90fa92c0208029760f52580410043f43aa4b00820087c8754960104038dce4a92c0209862f21d42580410061fbaa84b008234c3c7550960104059a8e698ac0208039554d315804164f4ba1a62b008203c7875941601053dc74a9282c0208123e21d50580410071caa2a0b0082048f8874c16010401cb2a6982c020803a650d30580410076898a60b008200a6d82d4d64884070fd0fbaac1108021f60f75582210061fa16eab044200c3d42dd5608840117f08baac1108262f21175582210052ec18eab044200a6d821d5608840187eebba2c1108030f1d774582210061fa96e8b044200c3d52dd1608840187eea3a2c1108030f1d4745822100556c10e8b04420087f855cd60884070f90ab9ac1108022fe11735822104c5e422e6b04420087e87d4d60884070f90fa9ac1108030fdd353582217561e3a6a6b044200a6d82d4d60884010fd0ea9ac1108021f21d53582210061fba2a6b0442e9c3c7454d60884058bce6a9ac110803175cd535822164e5a3a262b044202cd4734c56088401caaa698ac1108021f61e75d912101c3fc3aebb22420087f835d764484f50ff04baec8909021f60975d91210061fa12ebb224200c3d425d764484018de40baec89080f0f9d654d912101c5fc3aa9b22420387e85dcf64484010fb0bb9ec89080e1fe1f53d91210043ec3ea7b22420087f8754f64484010fb0ea9ec89080a2fe1d43d912104e1e322eb3224200c3d75d92644840193ec8b9cc8908272719173991210062fb9aa6b224202c5c7354d644840117f0eb20c8908270f19175d05211c45ec3ec9a0a4200c3d75d9341484018bee6a9ec09080b171cd53d81210166a39a63b024200e55534c760484011f70eb00c090802abe095458b40005
  | 22 => 0x902c72080237a1c2058e410046ec3840b1c8200a5e8508163904014bb0a102c720b26a7a102058e410054ec2040b1c8204ad68108163904015ab02102c7208db0f9d27558a410052ec1ceab148240a6d829d562904f54df04baac5208f6abe097458a4101e1f3aca8b148200aad82951629046d17f0eaa2c52080e1fa177358a410043ec2ee6b14820387f87d4d62904010fb0fa9ac5208021fe1d5358a410062fb9aa6b148202c5c7354d629040155b05a1ac5208d62fe1d4358a4101c3f42ee0b14820087d85dc1629040187b09bb2a5208021fe0f7654a410043ec1eeca94820387f82dd952904070fb05bb2a5208030fd0b7654a410061ea16eca948200c6f20dd952904014df04bb2a5208021fe0d7654a410043ec1aeca948200c6f825d952904018de40bb2a5209031dc417654a410061fbb4e8a9482c2b2d829d1529058d65f04ba2a52080317a1d6354a410062ec3ac6a948200e4f8258d5290401c9904b1aa5209eb17dc96354a4100727b92c6a948314e574158d5290481ca882b1aa52080393c816354a412072b882c6a948200a3f83597429040147b06b2e85208028fe0965d0a410051ec12cba148238c3d72597429047bc6e20b2e852080387a1563d0a410070ec2ac7a148238c9d7258f4290401c3ea4b1e85208038754963d0a411ef4b882c7a148204c747159542904099a8e2b1a85208e3a51056350a410063ab2ee2a148200cd563dc5429040147f06b2a85208028f60d6550a410051fc12caa148200a3d82595429047b87ee4b2a8520b2b8bdc96550a411c71a38acaa148200e2f205954290471c6e20b2a852080387a156350a410070ec2ac6a14823dc9f7258d4290593d1ee4b1a852080387d496350a410070ea92c6a148238e947158d4290401d1e40b1a85208e3a5c416350a410071742ac4a148200e2d855894290401c5ea6b1285208038b54d6250a411c75238ac4a148200aaf805894290471d4e20b1285208038d5977150a410074ab1ee2a148200ea562dc542904ad17d0f2a2c12080f0f1d654582410162f39aa6b048200c5d7354d60904ad17d0fa1ac12080b279cd43582410052ec1ea4b0482568be87d0960904014db05a9ec4a080b179cd53d89410062eb9aa7b12820087f855c362504070f90ab86c4a08062f21170d89410051ec26eca928200a6d829d952504014df04bb2a4a08ea2f21970d094100717a9ec4a128200e2d53d89425040155b01b1284a08126da1f715094100753b16e2a128238cb5761c54250401d4ec438a84a098a2fa1b70509410052ec1ea5b028256c3f645d460504ad93ec8b98c0a095b2bd9172181410047dc3ac03028200aaf8255162104014db05a9ac420bab8bd0b53588410062fb9aa6b108202c5c7354d62105d3c5e84a9ac420c4f938c953588410164e39a86b108200aaf
  | 23 => 0x596410062eb9864b2c8204a76810c965904014eb02192cb208029ea0032596410053cc0064b2c8204a76819c165904af4eb03382cb208028fe1170596416551e422e0b2c82caa3e841c1659040147b08382cb2080297a0c70596410052ec18e0b2c8200a6e821c165904014db04382cb208129da04705964117d3ac08e0b2c820087e87cc165904010fb0f982cb20803175cf30596410253b40c60b2c8200a75818c165904018bae6982cb208021fa1c30596410043ec3860b2c82caa3e840c1659040147b08182cb208029ba08305964100536c1060b2c8204a76810c165904014eb02182cb208021fa1f20596410043ec3e40b2c82caa3e84c81659040147b09902cb208021fa1c20596410043ec3840b2c82caa3e84081659040147b08102cb2080297a0c20596410052ec1840b2c8204a768108165904014eb02102cb20b26a7a127558e410054ec24eab1c8200ace829d5639040159b053aac720b969761e7558e410070f424eab1c8200e1d849d56390401c9d053aac7208029760a7558e4100726c14eab1c8200a4d829d56390401cae833aac720b9f951067558e4173f2b884eab1c8200c5f875d563904014bf04baac720b9717dc57558e4172e2eb8aeab1c8200e57415d563905cbca882baac720b9795c417558e4173d2f428eab1c8316ad7815d16390607d2882ba2c720b27879535458e410256b40ea8b1c8200ad581d5163904015af02aa2c720812b52055458e4167f4a20aa8b1c8200a5e85dc963904014bb0bb92c72080297a167258e410052ec2ce4b1c8200c5d759c9639059353d09392c720802a76127258e410052f428e4b1c8200a5d851c963904018baea392c7208baa7a107258e410054ec20e4b1c8200ccd721c963904095ad02392c7208bab56047258e410056d400e4b1c8200ad9801c963904011bd0fa92c7208023761f5258e410052fc3ea4b1c8200c5e87d4963904014bb0fa92c7208031761f5258e410042ec3ea4b1c8315e5741d4963904f5ca883a92c7209eb95c435258e412052ec2ca4b1c82c9a9e84949639040153b09292c720b26a7a105258e410054ec20a4b1c8200a5e8590963904014bb0b212c720812b5a064258e410056ac0c84b1c8200a5e85dc163904014bb0bb82c720803175d77058e410256b40ce0b1c8258ad5819c163904018baeab82c720802a7e117058e4164d4e422e0b1c8200a5e851c163904014bb0a382c7208baa7a107058e410054ec20e0b1c8200ace821c1639040159b04382c720812b5a047058e411756ac08e0b1c8204ad68194163904015ab03282c72080237a1c5058e410046ec38a0b1c82c9a9e84141639040153b08282c720802b3a085058e4100566c10a0b1c8204ad68114163904015ab02282c72080297a172058e410052ec2e40b1c82c9a9e84c81639040153b09
  | 24 => 0xe82cfe34414c565d059fca86298acba08021fa1f21597410043ec3e42b2e8209a3e84c8565d040147b0990acba08268fa1270597414851ec24e0b2e8209a3e841c165d046547b08382cba080297a0c70597410052ec18e0b2e8200a6e821c165d04014db04382cba0b3e9da0470597410053ac08e0b2e820087e87cc165d04010fb0f982cba0803175cf305974104d1f42460b2e8200a3d848c165d04018bae6982cba08021fa1c30597410043ec3860b2e8209a3e840c165d040147b08182cba08029ba08305974100536c1060b2e82cfa76810c165d04014eb02182cba08021fa1f20597410043ec3e40b2e8209a3e84c8165d040147b09902cba08021fa1c20597410043ec3840b2e8209a3e8408165d040147b08102cba080297a0c20597410052ec1840b2e82cfa768108165d04014eb02102cba09161f61e7558b411a61eba4eab168200a5d839d562d048b4db053aac5a0baf8bd0a7558b4122e1f3a2eab1682eba6f825d562d048bc5e84baac5a080e1fa177358b410043ec2ee6b16820387f87d4d62d04010fb0fa9ac5a08029b60b5358b4175717a16a6b16820087f8754d62d04018bee6a9ac5a080b171cd5358b4100537c12a6b1682e9e2f4254d62d0631c9864a9ac5a08263ba1f3258b417cf53a1462b168202cd6734c562d0401caaa698ac5a0b27a9d093158b410076399262b16820387e85dc162d04010fb0bb82c5a08021fe0f7654b410043ec1eeca96820387f82dd952d04070fb05bb2a5a09170fd0b7654b410061ea16eca968200c6f20dd952d04014df04bb2a5a08021fe0d7654b410043ec1aeca9682eb87f825d952d04018df04bb2a5a09170fd097654b410061f20aeca968245c3c415d952d048b87e80bb2a5a08031bc817654b410051fc1acaa168200a3d8359542d040147f04b2a85a08028f6096550b4104e1fb92caa168209e2f7259542d059f87ce2b2a85a0b3f0f1c56550b4100717902caa1682398bd86dc142d040187acbb8285a08029760f52583410166b39a62b068200e55534c560d062f4ef02ba2cb208021f60b735964173e3b886e6b2c82e587d879cd659059547d0939acb208028f61273596410062fc1ae6b2c820087f825cd65905cb8ee20b9acb20b9e1fa1c73596410043f43c86b2c820087d8790d65904094ed0321acb208029d60643596410052f41ee4b2c8200a5d83dc965904018bd07b92cb208021f60f72596410062ec1ee4b2c820085d83dc965904f58ee21b92cb20b2a8fa1272596410051ec24e4b2c82caa3e841c9659040147b08392cb208021fa1e42596410043f43e64b2c820087d87cc965904010fd0f192cb208021f61e32596416551f42464b2c8200a3d848c965904018bae7192cb208021fa1d32596410043f43864b2c820087d870c9659059547d08192cb208028f61032
  | 25 => 0x801b4ee438ac0a10032dd9471581420065ab28e2b028400cb7631c5605080196ac638ac0a10034dd4c71581420069aa98e2b02843dcb7621c56050801b4ec438ac0a10034dd4871581420069aa90e2b028400cb6601c56050801968c038ac0a100369c8071581420045f43ec2b028400a3d85d856050871968e3b0ac0a10e32d1c561581420049fc1aea302843ac3f625d4605087387ec0ba8c0a10e70f58175181421ce97902ea3028439d2d205d46050801a3d0ab98c0a10034761573181421d64fb12e63028400d1f525cc6050801a3aa4b98c0a10e727d8173181421ce4eb02e63028439d8f205cc6050873b3440b98c0a10e7634817318142006cc902e6302843493f87d4c605080127b0fa98c0a10cf479cf53181420068eb9ea63028400b2d82d4c6050a11a5ce5a98c0a10024fe1d53181420049ec3aa63028433d1e7354c6050801a3ae6a98c0a141f4b9c9531814200cd6c3ec430284d1d2e75d886050801a5aebb10c0a1343639cf6218142006c6b9ec43028400ba980d886050801a6ea7388c0a10034d54e71181421d65bb14e23028400da7629c46050801a6ea5388c0a10034d54a71181421ced3904e23028439da5209c46050801a6ea6b88c0a10034d54d71181421d65bb12e23028400da7625c46050801a6ea4b88c0a10034d54971181421ce5bb02e23028439cb5605c46050873b4e40b88c0a10e76c88171181421ced2902e23028400db1205c4605080117b0f308c0a10030f5d661181420064eb9cc23028400cb571984605080187aea308c0a1003275cc61181420065ab88c230284009bb8758060508010fb05b9acba0bab0fd0b73597410061f20ee6b2e82eac3c41dcd65d05d587e81b9acba0ba61f61e735974167d3b40ce6b2e8200a75819cd65d063747f08b9acba08268f21173597410061fc22e6b2e82e9c3c845cd65d04018bf06b9acba08021fe09735974174e1fa12e6b2e8200c3e415cd65d05d387882b9acba0ba70fd0173597417543f438e6b2e8200a5e83dc965d04014bb07b92cba080317a0f72597410043ec1ee4b2e8200c5d83dc965d04010bb07b92cba0baf0fd0b72597410061f20ee4b2e82ebc3c41dc965d05d787e81b92cba08268fa1272597418d51ec24e4b2e8209a3e841c965d046547b08392cba08021fa1f32597410043ec3e64b2e820087e878c965d04010fb0f192cba08268fa1232597410051ec2464b2e8200c5d738c965d04010fd0e992cba08021fa1c32597410043ec3864b2e8209a3e840c965d040147b08192cba0803175cc325974167d3b40864b2e8200a75810c965d04014f500192cba08029e60032597418cd1fc22e2b2e820087e87cc565d04010fb0f98acba08268fa1331597410051ec2662b2e8200c5d73cc565d040147f0898acba08268f21131597410062eb9a62b2
  | 26 => 0x2cb60b53985420049fc3aa730a840093d8754e6150867a3ce6a9cc2a1003475cd53985420070fb1aa730a842a9ad87d8a61509a3a5cebb14c2a10034b5d76298542686c739ec530a8400d8d73d8a6150801a6aebb0cc2a1003655cf6198542004d7c12eab0a84009af825cd615080165b05a9ac2a100347dcd535854219e8e39aa6b0a84389ae87d89615086917b0fb28c2a10d30f9d765185420055ac0eca30a8400e3651594615080135f04b98c2a10066b209731854219c5ec3ec630a8400ab581d8c615080165b05a98c2a10cf479cd53185420068eb9aa630a8400e1f6354c615080136f0eb08c2a10e2ade1d61185420065bc3ac230a8400ab785584615080156f06b08c2a10038dd4d61185420071aa9ac230a843dab7825846150801d4f04b08c2a14738dd4961185428e71aa92c230a8400ab4805846150a39d4e40b08c2a1002ad61951185420071bb2aa230a8400ab5864c46150871b28e6988c2a1003a5d8d31185420078aa9a6230a8400ba7824c4615080127f0ab80c2a10d24f21570185420065ab0ae030a84009af825d7605080335904baec0a10e62f61f65d81421a61f3aecbb0284009af825cf605080335904b9ec0a10e62f61f63d814219e4e39ac7b028400b2d82d4f60509d5a5ee5a9ec0a100347dcd53d814219e8e39aa7b028400e1f6354f60509d3a5ee4a9ec0a1002ea60362d81421cc5ec3ec3b028400a3d85d87605080165b05a9cc0a10cf479cd53981420068eb9aa7302841a9ad87d8a605080127f0ab8cc0a10d24f21571981421a49f43eeab02840093d83dd56050801a5e41baac0a100267e0d755814219cce41aeab0284009af825d5605080136f02baac0a10e26d20575581421a61e3aecab0284398bc87595605086733d0fb9ac0a100347dd773581420068e3aee6b028400d1f85dcd6050801a390bb9ac0a100347d4b73581420068ea96e6b028400d8f20dcd605080127f0ab9ac0a10d24f2157358142004d7c12e6b0284009b7815cd605087136902b9ac0a100347dd473581420068e3a8e6b028433c9c73d8d60508731790eb1ac0a10cf271cd63581420049f43ea6b02843493c87d4d6050801a3ee7a9ac0a10cf471cf535814200596c16a6b02840093e8754d60508012790ea9ac0a100347dcd535814219e8e39aa6b028400e1f6354d6050801a5eebb92c0a10034b1d77258142006c7b9ee4b028400d8c73dc9605087335d0fb12c0a10034bdd7625814268e963aec4b028400d8f73d8960509a1b18e7b12c0a10034ddd771581420069a3aee2b028400d9773dc56050801b28e7b8ac0a100369dcb71581420069ba9ee2b028400d3553dc56050801b4ec5b8ac0a10034dd4b71581420069aa96e2b028400da720dc56050801a6eea38ac0a10034d1d47158142006cbb98e2b028400d94731c56050
  | 27 => 0xb882e730e84358bf8758e61d086b93ce6b1cc3a10da4fe1f53987420049ec3ea730e8435d1e73d4e61d0801a3ae7a9cc3a10024fe1d53987420049ec3aa730e8435d1e7354e61d0801a3ae6a9cc3a10038758d53987427ce5a30ee6b0e84c9cb4615cd61d09d5c68c3a9ac3a10d7479cd53587420068eb9aa6b0e84e9e346154d61d086ba3ce6a9cc1a1003475cd53983420049fc2ae3306843693c855c660d09e927d0fbaac1a10024f60f75583420061eb16eab06849ed2d62dd560d093d27d0e3aac1a1002c760c755834200596c10eab06843a8bc8759560d080127f0ab9ac1a10da4f21573583421d45e43ac6b068435c9c7358d60d080127d0fa9ac1a10da4f21f53583420049f43aa6b06840093c8754d60d086ba3ce6a9ac1a1003475cd53583420070eb1aa6b06843a8bc8758560d087b968e2b0ac1a10062f61375d85420061eba4ebb0a8400a5d839d761508070ff0ebaec2a10030f5d175d85420043fc1aebb0a8400c3e415d7615080187882baec2a10031bc8175d854201c3f42ee7b0a840087d85dcf615080317b09b9ec2a100e1fe1f53d85420043ec3ea7b0a8508c3d74d4f61508010ff0ea9ec2a10021f61d53d854283e1eba2a7b0a8400c5f7354f61508058b8e6a9ec2a100f1d9d651d854201c7bc3aa3b0a84028f7874c761508059ace698ec2a10039554d31d85420263a30aeb30a8404cd4615ce61508018eaebb0cc2a1003355cf61985420047bc3ac230a84018bd84dd7605087317b0f2a6c0a100f0f9d654d814200c5ec26e7b028508c3d74d4f60508014db05a9ec0a141f0f5d153d81420062fb9aa7b028402c5c7354f605087317b0fa1ec0a100b271cd43d81420047dc3ac03028400d2f855c36250801a590ab86c4a10034bd4d70d894200696a9ae1b128409dab805c3625080127b0f3aec2a1002c760e75d854200596c14ebb0a843493f875d7615080127f06baec2a10030fd8975d85420061f30aebb0a8400c3c615d76150801a5e40baec2a10d24fa1773d85420049ec2ee7b0a84099ad82dcf615086927f0fa9ec2a10024f61f53d854200596c16a7b0a840093f8754f615080127b0ea9ec2a100347dcd53d854219e8e39aa7b0a84d1d2e75d8b6150801a5aebb16c2a10d34d9d651d85421a4dbc3aa3b0a84339b7874c76150867b2ce698ec2a1003c554d31d8542005d3c1263b0a840093f835d6615087b87ec4bacc2a10e34d185759854200697902eb30a8438d37105d6615086987cebb2cc2a10d22fe1d65985420068f42ae730a8400d1d855ce615087b93ec4b9cc2a100347d4973985420068ea92e730a8438d94615ce6150801b1e40b9cc2a10e365c41739854219e4f39ec730a84338bf8758e615086793ce6b1cc2a10d24fe1f53985420049ec3ea730a8433d1e73d4e6150801a3ae7a9cc2a100
  | 28 => 0x258e605480127f08b8cc0a91164f21171981520052ec18c3302a501d6972d8260548010fd0fb22c0a94221f21b73581520049fc22e6b02a44593c845cd60548012df04b9ac0a90025de057358152204ba40ae6b02a44187c8758d60548018bee6b1ac0a90df171cd63581520043f43ec2b02a400a3d84d8560548032f50fb02c0a94835adcb605815222c9fc14e8302a43493d829d0605488587ec53a0c0a90034bd8a741815220e97904e8302a441d2d209d0605486d27f04ba0c0a90d24f60974181522161fb12e8302a400d2f625d0605488387ec0ba0c0a91070f581741815220e97902e8302a441d2d205d060548010fb0f320c0a90030f5d264181520061eba0c8302a50787d865cc60548018bd0cb98c0a90031799173181520062e322e6302a442c5f625cc6054801a9ec4b98c0a900347d0973181520068ea12e6302a441c5f605cc60548838bac0b98c0a910753c81731815220ead102e6302a441d4d205cc6054801ab240b98c0a90de1f61f63181520061f3a6c6302a400c3d74d8c60548018bae7b18c0a94231b9cb63181528fe36b96c6302a400c3e7458c605480187ae8b18c0a90df179cd63181520062eb9ac6302a507c6e7258c6054a3d8dae4b18c0a90031dd8e71181520063ab1ce2302a442c77629c46054801acec5388c0a90034dd0a71181520069aa14e2302a441d67209c46054883aca41388c0a90031d99171181520063a322e2302a400c77635c460548018eac6b88c0a910b1dd897118152006b3b12e2302a400d37425c46054801a6a84b88c0a91071dd81711815220e3ab02e2302a441d67205c46054883ae440b88c0a9107594817118152006b8902e2302a40087d87984605480187ae9308c0a9003175ce61181520063ab8cc2302a400c3d7418460548014bb06308c0a9003175cc61181520063ab88c2302a40097b875806054a3b6d704b00c0a90062f21175587427ce5a20ee6b0e84018bc845cd61d099396882b9ac3a14230f1d353587427571a20ea6b0e8507c3c7454d61d08058bce6a9ac3a1003175cd535874274f1a20aa6b0e840387e87dd560d093d878e9baac1a10021f60f755834200c5e422eab0684f4c3c741d560d08014bb063aac1a10029b60875583421d45e43aa8b06840087f855cd60d08070f90ab9ac1a10062f21173583420043f43ea6b06840387c87d4d60d0a11878e9a9ac1a10021fa1d53583420043e43aa6b068507c3c7454d60d08058bce6a9ac1a1003175cd53583421d45e43a86b06840093f835d661d087187ac4bacc3a132b4b58975987421ee9b882eb30e84368bf8759661d0801a3d0ab9cc3a10034761573987421c64eb12e730e84c9d8d625ce61d0801a3ea4b9cc3a100347549739874264ecbb0ae730e843dd94615ce61d087bb2c42b9cc3a10036548573987421eec
  | 29 => 0x8060032000000000c01600001b000003000300e80040020040000030000002000000801e0000010008002000000800001e01d000000003c002000801401a0040000044014001005000c002019006800001c0000050018000000003803800000b001000800e001000806000800100680140000000000000000005016000000000091cb7c12e7b22a40196c825cf645486f0fb0fb1ec8a91168fa1363d91520062eb9ec7b22a52bd2d72d92645488b47b0fb24c8a90030f61f649915275d1fc16c9322a445a3d82d926454a5587ae5b24c8a91178b5cb64991521bc3fc3ac7322a400a3f8458e645486f8bce6b1cc8a9003175cd639915222e9a20ae3322a445c3f76d9164548012df04b9ac8a90de1f21d635915222d1e422c6b22a400c5f7358d645486f8b8e6b1ac8a94a74bdd372591520049fc3ac8322a528b2f82590645486f0fb0fb18c8a90028f61363191521be2f39ec6322a400c5d73d8c6454a4f65b053a6c2a91164fe0a74d855222e97414e9b0aa43493d829d3615488ba5b053a6c2a90d24b60a74d855275e1fb14e9b0aa400d2f629d36154801a5e413a6c2a90da4fe0974d85521a49ec12e9b0aa400c3f625d36154801a5ec4ba6c2a90030f98574d85520061e30ae9b0aa400d2f205d3615480187ae9326c2a91021f61c64d85520061eba0c9b0aa440a7681193615488b27d09b9ec2a90024f61373d855201cb6c16e7b0aa44087d87d8f615480187ce9b1ec2a90030f5d363d85520062eb9ec7b0aa400c3e7458f615480187ae8b1ec2a900317dcd63d85521be2e39ac7b0aa43787f8758e615486f8bce6b1cc2a9003175cd6398552936b2b96c330aa400c3f7499161548010fd0e322c2a90025be0973585522043e43ac6b0aa400c5f7358d615486f8b8e6b1ac2a91029d205635855292eb3b96c2b0aa44587d87d90615488b87ce9b20c2a90029d60764185520043fc3ac830aa52396f825cc61548032d904b98c2a900317a1973185520062fb22e630aa400c5d645cc6154801a9f04b98c2a90035320973185523d62fb12e630aa400d4f625cc6154801a3e84b98c2a90034750973185522062fb0ae630aa440c5d615cc6154881aac42b98c2a9003554857318552006a7902e630aa43787d87d8c615486f8bce7b18c2a9003175cf63185520053ac0ec630aa437c5e7358c61548018bae6b18c2a90025de1d6118552925b3c12c230aa43696f825d360548830fb0fb26c0a91170f9d364d815291cb7c12e7b02a40196c825cf60548830fb0fb1ec0a90df179cf63d81520062eb9ec7b02a400c5f7358f605486f8b8e6b1ec0a909a5be0971d815220c3ec3ec3b02a400a3d84d8760548818ece3b0ec0a90030f5d264981520053cc04c9302a522c6d72d8e605486f0ff0eb1cc0a90df179cd63981520062eb9ac7302a521c6d7
  | 30 => 0x1c00800e000003001e01d0008004038001000000000a00c002801001e000000000c0000000038008000002000000003800200e004800e00000e001c000000000803c02c001001000001400c0018000000000000001c02200000500500040050000008006004000003801a000000002c0120020010004006003001001008200100c00040040000008000000016001000001200300b8000002003000000000201000000000000040010000000001000000400200b002000c002011000002400a00200180240000000020000000000000001000c004000001401c00d00000200140000010000004006009000000000200600080140000060004006011002000000600100200000000080000004006002004008c016000001003800000300500000400020008018018000000801800200d005801002200400100000860000008020012005002002000600900280540000000000034012000005001c00c0330088020004000000800800400f01080200000030020000000002009801c00001100e003400200c003801c006004008800405e007003000c0160000048014000002001800400400800100140040060048008018004000013c00000000d8000002001005001000200a00f802000c007000001800800c0010000002000001001800600900800000040010060000006001000002c01c000001800001a004003001c0040000018008010001000008c01800a01e80240020150010000000009002000802c00200a000803401700a802000200200200000020020000000006000001001c0000000028000008000000004800e00c002002c04400002f802001001d0038014024000000005801e00200100200000090028004004001005801c00200c000003c01e0000040004026003001000000200500c80540000020010030002009002801001a0050050000000003000000000a005006000c022002005000003a002000002c08600600380040000050000018006006020000401400401300e4012000000800400e0000040010002002001000402c04300180080140010128034030018000002800e0090038000006000000000001c00800080040000030010024006012001009800000900000080000010020000000004000801800600000000040020020018000000000000800c03801300800240040060060000000002003800402600000000080020000028004000002007000800601b0000000014005000004000a000001801400c00c006800c00200300000080000000018014000006002800800a004001804400a0030010018032000001801c0060000038004008001002800c026000003001801c00100400080000000010014000002000000400000700000ac0040000060000020001008000000000300100100020000038004008006000
  | 31 => 0x4005c00800200000040140000000004004000000001c000003001802800e0000048008012000000001400c006007000c004000000000802e001001000000000e000002000200d000804c000000000801c0160010058004004001000000800a002003000802000301400700000000008000002000002001801a004000000401e00000a801803400b010007801c0020010028006000004802c0000040010000002010001001802c00f003800c0020000000000000006000000800200000100080040010078004004000000005405803d0008030008004003801c018000006000c00a0190008034026004001802c0040020068000004000006000402a0000030018000000007800401800a00f80c400a004001000c0080010000000000000002804c002000002806000000200700040060010010008018015000800400200700080340080090008000000000002000c00e005000003c000008001800800e001000000c00200000400600040000018018010000000002c01000800000140020010040040006003002000401c007000800801000600780000020000058000000007003801800600100000000140000010014000002000000400200200000140020070008004008000000800400200c00f8000006010009000801001100180000300040000004020009007000400a001000801c00a00e00080040000040058000004001000005406400000e00000100020018000000000000000801c01300000040000000008008000004006000000c003020800c000003055000400200000280000020000000000010013006003800200900580000000080038008008000002000003a001001007800a002000803001a002000801c006001000000402400300000000620110000000054000003000802000100580580040000020004000011006000800201200080c800e006000000400200600280040020150000018012012005004c006004000000c01800c0000000006000002800c014000000802400000000000a8000000000000c00a00b0000018000002022800800000000000a80080000048000032001000800400000a0020000002000002804400a004000805400000a00000100080250010000036003001000c0000040000004018004004800400e0010018004000006000006802a001008008000e000001800000401300080100100020000000008000000801001000b0058008002011000800c006005002800000200a0020010030003000001001400b000000400c001009000800000a0000004006000000004803c003000800c0380060008014002001010000c00800600080040080000000010000003000001c02a01000080000020300048050000037008801400600000300180180020048064002012002801c00c000008802000400200a001400
  | 32 => 0x2025d82c6155919a0a786042aa82d816f176076b8a34693873e0001b9435d0af84ac83b25b0000057585dc5e380007888da61ca144476500003959e7e6e2000056083562f89544000000017d00380000d880000fe80000bf279307d87b09bac7d798b65e5810828718fc37694f82eb12360c6121c52e060600019d84c2800000000006ca00006ed0000000009e00010de00005ac0000fe227f00007c50000000000047500ac56a9aea1b7000000002ca2dc8a3675b86d2000165a35980002b600005d40000755000029b07240c700003af80007a1800000008b2000000000000000000000744000021480003a080006ef9e3000002f612d943817480005f70cce63180000000000000000031080003b2800018b80006f093c40000ac6000005811800000000cb608a05705a91d2c0001e52352800013b9dd836e0000000126c0000a7e294853076f1cac3400d9e40997b604f810e00018742ed197c0af97147d6936a0001f7c2e100000001ee83d4000000000002359ece23e80000d600000000000000000004400000000e105149cf20000f0e62b800000009f036b80001bb13fc0001cf800011d813507b21a9178a00011622c0912c1f80e4e468200a65500005449f6e51989b6000000007d800003888823ca161800015424fe022e2128d7c5b50000000110e000068a499800050000001a40b12000127c11a894622910240001d5c80b16c238b88580001c1e469089817d9a58000129e0001a80457879800011826e3056018397de68b965e4d386b620a80004899fae07e016636d05de0001628000000008c000000000007e89f485de9b762b2000040180000fd801252211721a996142b6953e0001aaa00001cc44905d86e98000000116833096be76d80001b600003150ffe5b59ae8353122a00018166f6033c319165400011963b99aa02c983b80001a1c6c01c46162828473905443bc931071d021609c96e60e5189c0cd00001d7000000000005728e448150bde176800026b94964850dce01686203b601740000a92000110a07f800041b015600007146e79e142940eb461280004299f5609a00000000c664b220504d59d284d1911e7d29eb057086506bd80005c907882c398d2383100e4bc95f237a0000000048660e800000012b8000000035c80004c6145e6490b502728bea3e90c3437f8e9c4af1140443077226d06240dc082e47f1f0c57f00be1921a042b01bd600016ce0001b406ed9a3a000000053d1e9600012e800000007bf1d420bd000072f9d7e63781123c2129c51683507461be464a87e40538d904c187b4000000000000003668000084941c419800200300a80140000040038000016002001801800e000001009401000c00000000000000000004002002000801400e00600100180200050058058002000001804c00000700
  | 33 => 0xbca10580000000f8c0001f7e3cd0d240ad974e0000ee06c40cbe26f90ac14195be0001d5e75c80002ff80000001b1800009da00000000000000000000052d0c18313948272a9b3c796000047a80003851bc6573175c52000000af0c8a000000062e13840be938c1e000000759a283f4800068316563e408b81fe1698122959c4d2000078f00002eb88fc55d132419396905a99f0a3a48c103748c884ff8000108119e62f8b525c68f1a2a200001ce80004f2159e46880004829b8a00000c63e7096816494c04e614e017a0ba045c000000013c219688026fe800000004043b0800079202e21f58000334109e3858ffc15893522381922644048e0000b9842e8000000000000017ce00014747f8800000016f0622000002e16600000e70000122800000002fe00004bd800023f99b40001c7800000d0182878208300000001a5c42d8eee36704b474300006b7197656996700000dca01808a8000180a5f4800063c0ec4540800000015680001ad247080000001664633800000000001ee00000000000000149832e043a32714860e7843205680000001c725210000156859c000000000004da50780003ef80f022b997269b0b385961854000092040b9f385dd000000000007f0000037980000ba917c774059a00009a03f90632354000010000003f58d0a43d9d1a202054a4be00000001e927a500005bf98ec2e695361c318fa0000a4635a800061b8a0c71918c40001f920bb140800f9e6a102051e79907cc1dfa03c0001bf21a1164633200006a4808a52314d20458a2200000005238000000000000004a614212ea21b0000104002a000094e6759dcc34d9260670000076797b07c70a7268d800000005783ab83e6000196c00004280000ce87d41450000000072e00007168c480000000000194c00003ca5dd80000001b3e751913200013b8000000072700000000154000108431190da30894da55a83ac0001080000000000014a60001a500001ba27a80686000019474e99827319d7800005a800790502998f62000000028c000003d0000000000000000005ac15460000e1e6260b6455c8000000000052d8d1218608147f9891c2c4000064c8000000161c10d0000209000067b00006c81f20782097e000000057a9b263cc01ae2bd12f4124886030007a45931c6c652057a7a78f022ff1fd20c5166a2dd829a44c000059d95f83e50d4017010cc2ee1ac46498c5e00000005be199670f00000000baa4dd800000008647f18b6e103128e13c096e111800075400000e20000710000000000000fe94f24e8a0023d9a0422239b966a914e253099de4178000000161601c0892813000000011d200000004df800071e886a30a80000e291121ce0cee00000c0197800063019fc18d203600016ca7e98adc000144281591160001a701301a722ac9e
  | 34 => 0x1e8246296620000c9228e80000488000562924e26607c665980004a19374000047201007106d2000044617325ff1b8021e0128424025453295f4000000035b83a21710cca43b81305ac97aa5e0800000000003d6000000000002640000000048c5bd00005520d2c31600000fd1d023c48d3c5289c9a0061a441b318105909aca300906034f87fe1c485e46071eb477b1fa82c6198a1d0159a399804a588862c5b4034a13b17061cd128c3fd05944800dbc092061e6d7867203b14404c08f7a014025e08102d60000000000145446610f208d88260001e3a00007ae00000000000000000164470a1a7800000006a59ae600012564320e3c7470a487a002ac0000eb6000000006a852000000006da03d80df97a663080003ce0000000185a70298cc00016720001ae0280000042c80001f880000ef99a474e0000000000000006a0172819a4f685485a200000000c204838000722800015192c625e96fc0001cb24b28c560db990803e087a6f1000000b956e000000000000006ee1a3876c8e026ae034c71590c26f40b2a082869672d96f6464990a0868000610000011f134c3f0160a58800007a99d3c28b8000040800000000924fe80000700f980ca15626fb063069880004fc00003b31b625f41cb400000002d3986a3488b3c00001600000d565c58000000000051b800063282561c881367c2104864680b05311c2e45e03e80a981401d29a1059200005eb8fc6064840e0000000797196000000000001e1217c90d27148494341025040680006228c1c0da11102b48000472195a000000000004d63440c5c00005a221386fc59e167a1ac00004bf00003ae8caa19c0e9816da032000000054003da4f912d66f78bc625d00a2244827c20c928404008e672308c87c793d22b090d67b99f2c0001aba5a7867a3da0b3404b828e125971272405a44f38cfa7ec80b60a715e277f16e03f60000000000080693f627780000001174000154c1b286f200000000000e2a7fd13d426890001ad117a270842220c164e000200639e85a63b6969c303819c00014d04b90fda0a206784eb90087b510f87b88000000000043a106444e1af863d00746648d6464c1a323ee94d87841fba4aa947e4468b4a00018e6000122e0000ad43d710986e1000019b00007e3200c39403dc000143c00015c46a9935415f00006ef00002201d30000000000013dc0001b147fc88f8661000053a00003aa0d28000139603e8b1625812fe54280000000fde2ce800000000007c1970a00000006c3979a0001dac5a2909c000144a285800000000002fb0000000030000016d200017e200001d06c180000d902c054393b06539708578203e39a0f4a34195c00001d2067280001310be654c041400000000001388000056a0001d7600019343548000000000032510920
  | 35 => 0x5bb80000000bbe1cc813c7e70bc22b3800000012d47e2800000015f01490bd23971cd6644898c015000081389ce8149ccc08e8bf6242906222d0e74161000004180000000000777000060a1606601193800011be7e19a6800010342978f8e160034204d00063c01aac5e78b5661d88441ae07c2000177879194b0122042e7658f5400004a26c7090200000000000260109987c0000b9c79993a81708000000000031b09e462a038647196b6508974636900005da08467161da43ef163a4f1936456584c23ea94ea000000000004f4431920680b925e6361b7853387846259a26556108634994346548e0833480fe31e04480280aba6ce1ad40b31fce48313b61919608333032a0ed841e7839cc054613be16085667b410185469b9c7dc06560ec0e620a184526ac8dec42e0068692901c3cb0fea6288f527ff080e03781ec1129402486a0287781ea400012e207080003db8d1871f1c927f80a860029e044ed00001450ece0000ea6422139e1458e8458a93bc73289147ca99006f813385f5956034b863a7801b343a0061c39210a200011a641a0a6a31a8b0a7f40000411800003918266e400000620f1e000071e3dd9c181fb8dea484081a7a684ca00017f22211d6a771146a6350786708152211085b826299fe2d6904e1ff133c66b9e2a7fc177e7d3914a2970e6c0fc988007a05fe26b00000001950000000000000004421870659000065a80000b6925c0000010000000000012c20f49d84000175603394ba0000b9209a9c0e23d13c00969fca680061209d9ad052f02a02bd82dc27a985828785f019a10be4a89eca80802024ca809a6db18e21d78bb6722205e0000d76000000000010a400000000001f3250a10720001e620001c0646b11fa67700000000726360815e7bb0aac06e9fb8000000034e0af23f3846c29e1b1a32c1cd27bd969254a00dc68211e25e902266b20d2a000000000000006000000000000000001b00d50000274000005b90ea50b148a3e880007cf069a0001dc25ea0e420000c1600000007ae0e0e4d11df431887f60001bee7c6947631e90522620000749158840f00004d997b4000119c594800033a836a000138a12000003c600003d119d4000000030100002f300005c419f078080005a0856e579800078e11f66c100006b59b4a54800001b7800000001a813a152478c834800000000000000000800000015706110322000069e000000000002903cc98d6183084000008865898c9e00000005cb139c00000007cf80000001d0e0000ab62901b4c5cf15542141a300be000035519783a411861990cdc78a10423c993e60a500003e2863e5c300001008fae305014c0000e726880000000000000000007f09fb0426847421c81c66078d5a7108f4c76e8586494096653e9cae0481db412609961dd8158000000043b0
  | 36 => 0x11d031d03904e8000021a00001538d20000000032e85427c89c107ac9de85d1151c22d8dba5479264563838c3c500ae7f3167e50c9e6e0308c702e99f001aa123c7e4071c2509ba800009543ce872c07f08e46dd00000681dc605088162751a1e0000000766093e171800000000002b8000016e8828000133a6a2992c789075656e1bf400001ac49207bc0320c6e77f8000727a0665fb8000000131257200006d49bfc000000029c167c2e1982e3c7081e701163465a00000271ffa6d180006ca84703e5856c0eb8cb44d090a82bb9f2403c89ba18a04c6459153234081b851b0e6a7da11807110be018a87900f81b1258f1eea0001b1e5b9173a1c218b40c80c1a0df1a8411d849a5641a6e5039f9a80c063868f9dee4e99f8841d1c840b11c2470a80005f083e272893ca7d490b06c900004168a600a610fa78b800067996ec7ab002c4f8111c06f827e0ce16043ac185e7b90b9e2721c4800000005d4978442506f86b90258611987a605142a279914c48b1eb65ee15de4388d7014290e652420040121df05249af07a38b2071f87a266319d221594626430a7c6ad0bc8338083e44f98387a3061600017302e8879c3688a247fe0aa059712c403a02e60cf86760fa8b626411cd81c584ba2579f7a4ac1882725143057399c675f000079b0e3870300004f78c0c36c851c0000c760570d1e382935a6d701d8525000073403063e20890017000020405b22109e7a0001f803ec8afa6038fe01898a5400004fa000097c0001d642c00d485dc06f6577000000019a81f69ac25ca0b240b496c825b1aa262985e024f085e281000047e1bc8000199e51a0234195000005e86a227b1b7c06d81a233c000044a00005b18f6a38d06aa43f872a3f51bdc05f80005d500006570a98353966c000124c73a8b322a90a261d891881d484ae2a1012673f17f856491c400011e81bb906e0000000127918c3e01d3e47c0f8672080005f91df62a698e838183bc626811476a1d8015908e229291522a98000705879401985b41b8058c00000003101fd811400007b1195678b00000001c6073f8e8e62a9c5455e1bf84c1154e7c1000065880002e212307d19d4a3c5889c16f997a4731c667a10748619018479118e014a004e18d84b85f01ed8806195814b00005a0188c7e11ab673e91b2283835c0dd86e808f155c1eea05c1d30e8846f146038c1b442ab8bda0000b042ad14aa2828c7c56f1336411083a3f2154039916b86db886e4c70a38076864a11b842a5a81aee71719d000012f0173855078685680720b8e79810c4298a04801f879213780004b709f612a181823c1af200005ec00011b60001e784550e607939be65c08000000127847c9d144cc000077e87be117800041f900a0000a20102801656a193e49001e600019163029e187b702d000008da13c8000
  | 37 => 0xc3de120834c1a2a6861e1674a903a65782e44209f546699fbc41d874601c9aae4a48000373041a7b012d855b18862789fc800010402d0800000000000f59dea4eb0cd83241aa84049c5e58e00000d69e0c79404ac2d985cc0000bce7320a2876c04dc17986fe0348df80001b0a3c299ea48e02b22fe800063e0e520000c440000ddc7a708c42f602c201d9b5a3e683a434d00001f4000000000005ec8000668800012f032c5f80de237b82fe09b000000000002e41ce0274843c11f98521e782aa7ef84fe44980004a09ea872004560001290378000049500004e4000018219fa51588621489e541af1ef839d8d4453d8a9c51e83726cd86d627e1e5e094983638e831e2b7949a0d0186c3300fa03761b8235a15b60000db0568000000000000001d160000000000000000003981090b5c8190cf80001ca8430186008a9e5a5718cda4a2800025880003f288c647580002d000000841a0a30c0ed20f798bc0000b6049d974841a92b47d100000000a5824d0a0800000001cf000019a80001b080000001412000000053b00000000000116000075c1f7876294d4811969416b95647e908342c5171e1f00b28651800000000866d3811a52a1e725d898a432b8b742a7800016780004078c280ac0d984db95b024e93802e502464fa9566641941600007a66279b9a40c8d0e22a9028386845c1d819422cc157e4cb8b807cc0fa60d7851214d0ff255783c80cc81e2197088c3aa96ac5748936768966e77c98925aa9ada0c999ba7e78d9661f9c625b61b2e70880001c800940bc85521da9c8646c0e4a4d81a4867113000e7147807e91b47c590d821500206c081703ee01c477e05fa0bb831a1fa811c31f8186566000008c86106c30b7e00019363a90c824908e863d689725e8886600000002488eac00011ca45200007f9013272f0de45eb093237e800005a80005a3800000000004cb0000000000078d9258478000024912244a699c87d01ad815505a00ee9d904f883d06ec16f219f1c081fc84680001e762e300006f48b1a5ca80001a496c4140000076f9be234e834e49199aa00000a800000000000f200000310000000060a80007649d680001b2c78f935c54d0afc73b06667d08b4860c879600000000000144000025c078169600000004db08b08088e5e16410f408b15ac5e800000000eea5da80000000000000014a0001eda245972200000003d21a4c569202454982407bc1e4a7b20f3e7138ca21139fd63d08a022b917424058490146844c6ac0d1403509582d600e61a20f7257b97ca4dc17723a300900001ace5fe824417e05aa000000035f80005cd0000000000000008ce55f0c9a33f8aca4701d5a0001d6c3e101b215c95b461388c05b68000000000011500006b015ae0f0921675813787530f105d00d8658d938e62c89007759c4a041
  | 38 => 0x2cf800002d0000000052a69e80005b30e78029823845419982b58000000000033d1b981db02a430214107618e264b9880c36a0d0803593080000ee41b68e5a74d08cc00009cc00000001df095c1e3114207d0e9a29a03ec000000023b80000000000000099e41e893027a157673d992043c0b6a50515b25cf806c501000000007024ae80000000b961e80eb27da800000012be000099a0000d8000000002f58e7e4538e2027580001a300fc2d78df01ab1ebc7e3805e5f6140a7620cd46fa9c4c25e0a105e4112e3610f0c60685401b019b00190e2c7748cc4009850c1db872e2309bf63e08b061070a905ff976e256843023b102a5b8918e69181b401a8a4c6a71bce79097e61a71a7e7db0c5031290ce6e913ee519018e0000f9e3ec02e863f81dc7ed98d000005ea6859f940000bbc000000044d04fc66b00000001d0400000003d380001388c3c00010042511d12000157a66c98dc00017c44cf96325c9803432600006dc8edc7c3894852900ba2fb800020704b2000000061712443c880006b180001d9800067a055e3fb9122481000039185fc7739c2c0001780000000052b098034300000000000000000000008ba0479d8c12c00000520600000000022f80000000000000000051701d46a2000058b96b400008a2000187234c80006789e8824a91de33c903015716bc2861d1e416160c2ac1b6669699ce5cb824a58680003900ae609900000000000090800071b8098000205a000139a2ec00000000aec1ae800000008e800013b25418a1400000003398d60000000030f83441cc0fc2000000050b84820000000000164064080000000000000000000010a04e1871854e92965fc000010f80000000ec80000d5c67b861426480000d18b2c4dc9c966780bc46621a547538d42023028c4c5973819f98560d81c5020b09860000000000000067d800030e1d062299f8268686fa2478cde58485980000000000061a00000000001de200015940000000000000015f91f448d076857f80240001cb06fc0a8000000007bb80007fb093800000000f319be60084642ea08ea1fd0da02719ea23f70d5840e0000000000058f8a6e1210000000000038d80007791cda5a113d650307580331afe44f000000000003758a5675881a63b191064da13f251c8dde4341db844a8b220a2843600000001f515142ec86f0545916e19d0d9281297ec49b9ade56112ae3cb96ea00012e07eb092c4a9059632b1fde14b90224b3130e000080412a800042a9508000000000017ea0001ca05390352000031200000005618000422974a0628f9200d80007b316a21d414201b503167b58e181af80424ca12685f698da0221b540ea803c1f10a2a49c907c58912a8063124a351854c5ee81ee4e51c680000efa7669bfe63c84cc5c000002548cf60f51ce20001a8
  | 39 => 0xf81ea9d263dd10960ea000077011046d91b700000d7800000001c100001f9800000000004cc91da000026268880000000eb842300002a5800062812625d99252486002800000000fe04d00000df27050cec225800075d1ec67ed163063b92da8181a060000f06260a0625fd1fee760800000000000000000000090e000000037d027471a800064e936200015a204e80e062118e40000c528070b1c57600003218984119850e45711e600000007e820103ea09dc000089437189503f11afc198954a1dd00003f300004598000000000021d8c327510000242000022b001a1948fb447b884c79a1ede6a605582911610000020641e19f400000002f5176c4a015d008f8dc46a386ea01b84d20e807b04bb08486af13aa00014cc79c12fa6109c3036a9b7a74d822019813ba64a0efe00008d00001b1680486947699ca600018482df1bae04307fa28f00006f5197074b941a00007f00ad04a0000177c1d51f98000201e0fb96e800003c03b400006a1800028f80000589ae26d8098e00003a63d00db654401965d60f6070e000059d0c8c000000040f9ee0246070045606b24b480520c10ab83b59f740001c9814f0000193118457a094a7fa82ba27b83621b399942de80000ae04e0000074455580000001c7664ba0143a792d024999802afa0341eb02f06ee85d00ce8b4c00006807ff837851f132266f064400000000bf0000000030c0000000000000000005e202c8000345982c0001eae67e00007768278208032e00e800050e85361a3838413200003848b0c70d0d7a3b50ac400002ae00006e410180000001c3e5e6000069493f4619800035b00000b380006450ebc707127048088dc680824e46e9a9a4650ea24a9894022806e213616ae62390105b70fd03210f5654e081846a0af07048a1a0a493a474c8ef81d917204fa0736000000021f000023615ec0000994000152a413051807c999c000183e3578ff0011970e1c18f706b3111404280001639de64c989aa73b9b560000be814111023a81a76000000000000000000208000119003a80007fd9f6200019440000a2c0001cdc41512c039300003091a5e000000000009bc000083829907a82780d6200012b625c1d0a80e90b4271113a70991aa1f71f2e7ca041201101247c487b62f411b81d391463c100005c10000290800066e1da06df969a458007c05f017654f000000010bc02f1b42389137c4ab021c0000dbe75988ca4889350347008037f016c29d9a2430d800000000005119c324d28bdc00015e47c09f3600002702de14f00ff00080e382c822289285568dc20e683c65aa0b820e083ce79f18905378c96000000056e800051600002cb9d5262b175e1f201d23d1800001312740ed0e8a4791bc07f50f3c0001d08683a0004c3125a6908dd45fa049c08900f67350bba1f78b0800
  | 40 => 0xe480000000000267147000008f645a9fdc451000008509f2000000065b8ff65b7821857e8682139921226a15da4738000000000000011000000ede0000956246800000000000000000000155013d9b3a1dc100c488198e37400d82fd1f264a6028248f994a4c690ae00005ee7bc8a7405411dc00010ca00000000001a3c33f0000000000056000000000000613000075580000609602777800040d8efc66400003fe050209981bc66d8ba46bb017260188221b118c87c60d1a423944c00004ce62c094c0001e98535800005494b2000131e00000000000cc67bf97c669a9c3a59a000026e0e9400000001290c1e000000057517c87af9786000000000000008160000200199a3bc1f5873c00000000000083827a000161e67c8836795853e000000031c80007bd077a2c785740001d2200017182b30ec00000000000155280389fe75004180de80aa7d702a8000092e000139257d800050607e8025803000009b0244162c0640cbc6da80005d309d80b51c8e5e712a01e682e0647800c0738f2a47f927a3f990fc5ef17f638880000f9000032a0000000149e3db0ca60000000000000000009041bd047a5a30b46661950c0000f5e23487ca1d6807a0ff896a811070e000000036500000001382000183c0001436000000027e902c000000024199e42049f3460482800001a1400000000000e540e59bda2a89a2c6a5071a000000003680004bb844463d927e2da0c4c00017d411885d669588bc0f1012a5630ca478189f401e1868455800000000000000dc839f0afe7068330790000007c00000000e001e2830a000042c00000000931b0800001e470085c867301ca30480003019e90729121e69000005ae80005f300000001cba4b380002a088d4000000000000000000c6800505100001fe800000002d51f6073a1bb27d31d8e6ea9a8203293d8000117e000000005e0df600000006998d8c5090dc07d9085a000000076a800047b000000000004a51a12000001c04b000000010565018000000000041c0fec731000000000003870ee800000002378a060000d8a0b79e1c0001e266af86c85371dca3df89b20e014c853b8c2c2a51ed24fb13343bb1c00603149c08781ea5ef816843518942aa19da73d06ae00018082f014480db006209b86c621700005800000309830e38a0302000000022680005839a7c000000065d000080980ee782a038643800000000004d60fb659408f20001a900fc000e11e066e4de97367339d9c60d1f966e804be3d91b2236b1f762b8800021f9b8e19612880159cc200003242220000020822254b9d7a1fb14fe609123a3bd10e01f49f102ba883c1b401382db0a4e3cd83083200b4444804e47878a8c39b8be44c8090c14e187878d18304f30d8e64f029627000003c904ea7ea8b365d900001de126a33582a23eb04
  | 41 => 0x7f6800031680000000e960000000175011843900005398ad00000146000053a6d406e66d61fc4000191865fa040000008400000007d980005e214fc53191ae1e386406e4818063a80000000a8e2af20080001cde00000000000ee25e4800029e800048c8000110000000000005998c600d980000089d4860880006f28806756019e000008e00000040000bf01908ca018094be6f31be850f916c1d09a60338800000009a61f380004d7991c00000002a2a02a0001020000115a77200007ae80003bd8ffa00008740001c365d68c2e0001dd46bd14a044d845a188816418f142600020160000f7c00009a467080004d0105c00000006e19686000057600018ba000117661412de0dd171c000178c00005b000000000001d00000000032380000000b8a3810532259089e03100006cc1e740001e8a71c1afa5e5019838f964a00000000690a120000a3214996fa00000001a6144e40518202ba10dc00010020cd80a47398cb200000000001f3a000000038c80000001b3207793d054119a039605886990b7033913147aa800000c80000000a5a10e18627be820021c000052b9a9e412952c2028c3a00019401c29a347dc9a740
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x142d9219476509100050b64b531d9424400141d93d48765091022e0b609521d94244001c15534c4765091000529e49311d94244001c255248476509100070ad49201d94244001ca12148076509100052964a101d942440010b59804076509100050d654101d9424400149593040765091000529648101d9424400122f9260f655091000487e4d82d954244001834766167150910006251d9839c5424400115593e0975905100050d65c65192414400161593194649051000705192855ce414400154592a15739051000705191855ce414400115598195739051031525a5b645ce4144001c1765191739051000705194645ce414400115598d4973905108af05193525ce4144229c14645cd52905100060d2197550a4144001894865cd42905102b668dd1821c141440018a6766086488510006291c582191204400124d9321952481100062a1d98219120440013499321952481100059264c865492044001a2886191524811020d98259815492044001a28652194248110006a8d848650920440016a296a054248110005c865681509204400178193a0542481101cda8259815092044001aa086605424811020cd8661521c52044001b21845487148110006d060d521c520440733a1985087148110006c8615421c52044001b81835087148110004d8661529052044001b418354a4148110006c8615429052044001b818350a414811032f181db65485204400136195e11214811031f281db6448520440018571060f72594100061544183dc9650400105d93a1d32594100050b64b535ca640400181f7260f52990100060760d72d4a640400121d93a1532990100068554d810ca6404001a1953600329901000685c4183d496404001a151060f52590100060760f72d49640400121d93a1532590100068554d810c96404001a1953600325901000615605751c96304001859805d47258c100041766287d4963040018571061f5258c100061544187d49630400141d939d674588100050764e755d1620400705e98dcd535881000613a1d83d496204001a0e7460f5258810006835d183d496204001a471060f52588100069284183d496204001a451060f52588100069244183d49620425924d93a15325881000691c41839d56204001a4a1060e755881000691441839d56204001a491060e75588100058364e759d1620400160d939d574588100060b61d74d4d620400124e98dcd5358810745916447354d62041d1649901cd53588100050764f525db420400121d93e0965d0810004876635258f420400160d93a1562d08100050b64b53dd9420400141d93d4b76508100050b64b535d9420400141d93d4976508100048b64b83595420400121d93e0965508100058364a8558d420400121d98d4963508100058364e85589420400122d98d4d6250810
  | 1 => 0x68554d810cb6444001a195360032d91100048764c855c7644400181d8754f31d91100048764e85c87644400121d93a1720d911000417e4d82dd564440018557160c651911000487e4d82d94644400181e7660c651911000685a45831946444001a159160c65191100068560d81194644400141d9798d531911000507e5d6354c644400160c9258d53191100050764c655c8644400142d9219572191100048764e85988644400182d855c862191100062360d7218864440016159319571191100058564c6594464440016159319631191100058564c654c464440016159518d311911000585a59534c464440016149654d31191100050b64b535c8644400142d9508572191100052364c215c8644400181f7260f521911000685a4583d486444001a159160f5219110006859c583d486444001a157160f52191100060760d72d486444001a1583a0752191100068560d81d48644400181d8754e32191100060b615728c86444001c0d535ca32191100048764e854c8644400181d8754c32191100068554d810c86444001a195360032191100060761d53cc4644400161593d4a311911097585656534c4644425ba178754d311911096e8561d534c464440016179254d31191100070554d724c4644400161593d49311911000585657324c46444001c85724c931191100048764e85c846444001a155360730191100068561531cc0644400121d93a1720191100060b61572c80644400121d9321510191100050764c75d93624400141d931d464d89100050764c75dd3624400141d931d474d891001c172617354f62440014549754d31d891096f051d1534c762440016479254d31d89100041766073195624400141d9319774589100050764c651d1624400105e9819773589100050764f52dd162440014549754d31589100161521d534c5624425bc147454d315891000417e4d829d9524400105d98a0c765491000613e49831d9524400184c9260c76549100060760f421d9524400181d8350876549101a60b609421d952440018558360476549100061560e211d9524400185583484765491000709509211d9524400184d83c8076549100061660e201d952440018598348076549100070ad09201d95244001c612148076549100050764c76d91524400141d93dcb64549100050764c76191524400182e7660864549100060b1d982191524400182f7360864549100060b5cd821915244001a25828c46454910007055cd311915244001a25824c464549100048b66320191524400141d9319676d09100050764f529db4244001c295248276d091000728485209db424400141d9319476d091000487e4d82d9742441938947660e71d09100050764c659d9424400142d9219676509100050b64b539d9424400141d93d4a76509100050764c651d94244
  | 2 => 0x1a0c4160e755884000683d01839d56210001a0d4060e755884000493a637354d6210001645911cd5358840835926407354d621000124d93a17715884096f81105534c5621000122d92e0d65508400048764f82595421000160d92a156350840004876635258d4210001a174260f52984400058964b5350a611000161593d4942984400049564e854ca61100018558754c32984400069454d800ca611025dc14415cd53584400068510583d49611000125593a1721584400049564e859c96110001a179460f52584400068525183d496110001a174260f525844000685d0183d496110001a154060f52584400058964b53509611000161593d4942584400049564e854c961100018558754c32584400069454d800c961101938968160d76904400050764f525da411000103f9760d659044000607e1e735964110193c16715cd65904400048764f8259641101938967161d639044000507e5d8558e411000181f879d56390440004876635258e411000160d93d4962904400058364e8558a4110001c0e759cd629044064f219c57358a411000142f9754d62904400050de5d53586411000161593d4961904400050764c75dd1618800141d93d4b74586200050764c751d1618800705c985cd53586200051525d534c5618825bc147454d315862064e2521173586418800144d92217735912000417a6352dcd644800706c9760b535912000613dcd82d4d64480018647160b53591200051564f52dc564480018357520564191200048be6164191524800184c7660c71549200065260f73dc1524800194b835cf70549200054a65371dc15248001169989d0705492000652a5d831c1524800194a7460c7054920006521d1831c1524800194983dcc70549200065260d731c15248001962746047054920006581d1811c15248001963736047054920006585cd811c1524800160d93a1476509200048b663531d942480014a4965c47150920006685c5801c54248001529951db7050920006c2e0d53dc14248001d0b7354f70509200054a65771dc142480018a4762057050920006c2a55831c14248001b099560c7050920006c260f531c14248001b098354c7050920006c8d4d811c14248001b2153604705092000625211735846148001c8573509611852067e0d20575593414800706c985d9521052000417e4d82dd5648400705e98dcd63d951000613dcc8258f654400105f985cc63d951000515a5b734c7654400105d98dcc32d951000615dcd810cb654400185b7360032d951000417e4d87c87654400105f9361f20d951000487e4d82d976444001a158360465d9110005832496354f644400141d9319572d91100048764e8598b64440016149654d31d91100048764e859cb644400181d835cb52d91100060761d538cb644400181d8754c32d911
  | 3 => 0x4100683611829d56390401a0e9460a7558e4100683651829d56390401a444160a7558e4100691c41829d56390401a4582d067558e4100513a4b875d56390401855815d47258e41006165d5801c963904018c9726007258e410041766287d4963904018574161f5258e410061510587d4963904018571061f5258e410049364a85dc16390593294946065058e410041765e85c81639046d81e7460e7558a4101c17a637354d629040706d92e0f7654a4100513a5f8258d529040184d872096354a41005926408258d529040124e98dc96354a410048764f82597429040160d92a1563d0a41004876635258f429040122d92e0d6550a410048764f82595429040160d92a156350a41004876635258d429040160d93a156250a410048b66353589429065be074254d31588410253125d324c56210593686944c93158841007115cd315895210629e07434c5625484100417e4d82dd5601040181c7460c75580410060b1d1821d5601040106d9221d535804101c172617354d601040105d9321d52580410051525d534c560104098d0874c530580410050764c75dd1608840142d921d774582210050764f52dd1608840141d931d474582210060bdd5821d1608840182f7460b535822101c172617354d60884014549754d315822196f051d1534c56088401624916116254a4000417e4d82dd5619000705c985cd535864083d132497354d619000105d9321d52586400051525d534c561900018577360432d954000616dcd800cb655000105f9361f21d954000417e4d87c83655006d81c7460c75d894001c172617354f625006d82d82d08765494000487e4d82d97425000122f9260f655094000487e4d82d95425000160d9321762509400048ba6353d89425000141d9321676d05400050b648859db415000141d93d4a76d05400070554d319db415000103c9660d75d05400044764f825d7415000142d929d952d054000607e5183dc9651000181c9460f725944000607d0983dc9651000181c4160f725944000607d0183dc9651000181d4060f72594400041764e874c9651000185573604325944096f05105734c5651000105d93a1f215944000616601751c96310001855756047258c400041766287d49631000181f9461f5258c400060725187d49631000181f4261f5258c400060710587d49631000181f4061f5258c400060750187d49631025bc14415d57158c400041765e85c85631006981d7460e755884000683d09839d5621021182d7460b535884001c17a637354d621000184e8760f525884000683e5183d496210001a0c9460f5258840006839d183d49621020da0d7460f52588400068310583d496210001a0f4060f52588400068350183d49621025f24d93a15325884000683e51839d56210001a0c9460e7558840006839d1839d5621
  | 4 => 0xc0504c0a008050040502c1604801000000bc0000801000010942d000000140d0280100001008000840200000010000080f034040080404c0c0a801028000500102c000180000001010010000704c120000100407000150040000403020010b401008000880f004180040112d98c8274d85520050764f625d3615480141d9318574d855200507652865cc615480145591d91731855200513a5b825cc615480154990209731855299453a63625cc6154801d05424857318552006155cd81d8c6154a0f44c925cd631855200742d09205cc6054801d0942481731815200748d09205c46054801d21424817118152006075d1831846054801855835c46118152977051057354d61d080181c7460c75583420060b1d1821d560d080705c985cd53583420054364a855ce61d080111d98d4973987421c721589215ce61d086b41f9758d539874200607e1d6354e61d0a5dc14615cd53587420044b6488754d60d086d11c985cd53583420060721d6354d60d080181d7460e75d854201c17a637354f61508014579754d31d85428460b5d182d4f605080150d9321570d89420044ba63535c3625080112d92e1d53d85421a447a637354f61508015179754d31d85420054364a855ce615086912f9760b5398542986439cd82d4e615080190d7360b539854200607e1f6354e6150a0f50c925cd531854219d0765f6354c615080161591d8d53185420058964b535846150801a178354d61185420048d6548058461508012959320161185420052c241615c0615080150d9221773581421a44b25d82d4d605080190f7360b5358142986431cd82d4d605080181c87d8d53581420054964b53dc5605080151593d4b71581420054964b531c56050801c176354c71581420054564f521c560508014359518071581420052564c601c560508018347161761581420054364a855cc605080111d98d49731814200742d49205cc6050801d0952481731814298c4be5d82d4c6050a6190e7360b5318142006435cd82d4c605080152592d4e71181420054564f529c4605080152592d4d71181420054564f525c46050801d2352481711814200748549205c4605080103e98905735974100607e5183dc965d040181c9460f725974100607d0983dc965d040181c4160f725974100607d0183dc965d040181d8390772597410041764e874c965d0401855736043259741006165cd800c965d065bc14415cd31597410041764e87c8565d040105d93a1f20597411a6075d1839d562d0401a0f4260e7558b4101c17a637354d62d04014579754d3158b4100591e49534c562d065be074254d3158b4122e0b60942dd952d040122d92e0d6550b410048764f8259542d04018571060f72596410041764e874c965904018597360032596410041764e87c816590401a0e8460a7558e
  | 5 => 0xe000469180005547807f10272d02800000114ce8050000008e8001ec21c5e90c350338000ae31c31d198003b658c899933083fc1f8b818c038001191ee3682f0021085c4d022f1125643d9ca4102e837800050000e31fa0ec000801151642505b9f50760d89415c0ce03c0013947000000164356748b51b81f6000ef9bc00000cc409b1ce000000000001a49c0460525c8f284b28c2480015d41e47c0022b00000000000000354c396c000000dc8970d805c000c23b086c7c872000424000001b2690060000d00ac199410001942d01c08e500f08000e07244189a3cc8b86d80024608c369f60800b46795a204058000002162a02214d42260cc28340001c4dd80016c1f0000133fa144050bf1fc000eb9d112c120688a33583d50994c1ae52c7e8dc0a45080f1083902701d12d43e5d0fc04129206c069510447a5060bb40c0b8480b9020300daa1e41c23cb005913c0004a90d000010e100022c34cdb98c3d88b0e00183240c8b698a0004eca719b0404b8e0962100000001a22280a9131de1c03ac179a33166bcbb8af2ac5e51a1913a602430103156310e2855002340cc9da1c656c3d0d408407c8e000022780e81b21be8b5121c44246f91111e2ca8506b1f71a46a47d182182000b38790b0678b30cd13e0003195f2225acb997c3f25605495343055ca900031e000ea90e0ac1743715e070660d39b106a880f599025e86483000290440038f82fc2cc2e1072446b8189fc00080c3217a09c3c8cd12729e6540a96e1cc6c00012b26e3d03a9f23868749aa2846c388b79343ce3305223c10a14cd680024a18850898266790fa13d00024c4417f07c27426a2504c06800000122804e78d8132468181962782382a1e3000650eb1cd0003b0162042a07b8561703b24280000000045cf50aa15a000139b41d039518857000000000001e6000000000000000018d0004c00011b42e16cdd0004764e80010f464000002153de1dcb49cc00065cbc000000000f11611d26707720d20839000176000480001470101acc300043400000237252000090c81e244800000414000df8241f8770f41210003145822347422c000000008841e9dd03a3b51821c14c490500000e689c96181000694658213124d81c8a73f68d45a84f000738aa0003a81f83313f2883280004a38e7c4cf8613fc3740592a098218030a22941e1011b61045f50397b0288242f8be1d46a85a1a620a12515216262514f680027c295080b10d4000120040302c06008030042801c0000404028060280504c04070070080900005000070080001400020000ac040600302c0104c0300800004090040901c0401c10024000000202c1916c3602008000090000006000040050080003c0900c060300000821004090080e0300900005014000400802c030a82c0140001803004000001d00c0c
  | 6 => 0x65149430001d10583737a4c8b41f30006cc6f2391780007787d04a80000000118000708c3192498809803e0684218000a05d41e08a3f
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x173a7878312300004200c15000899c204441a36000073234a053e0020014805812c187000048022000028e50020028088a4c1f04986640825cc6154801282d172ea9a63b0a840090c69490585701854200492346482c2b80c2a1002909a8d49205cc6050801680d1ea4902e23028400a05a879460f725974100403f52c1c83b92cba0803049876408258d5290401222d112ea9a62b008200a05a879460f725944000502d43ca30fa92c620002a06a1e5183d49621000150350f28c1ceab108000807e9d93e09659044000403f4ecc6a4b1c822000240fa764f5258a4110001207d3b2742ac52088000905e9d93d4961904400051414cb8b0038a8490002815a7a4583194644400140ad3d22c1ea43222000a126809260c765491000700b06a12423b2a48800380983d09201d95244001c20c1a42900eca922000a0368c76608645491000700ae6c1262322a488002c09a3d49201d94244001a023232542ae720a2000a056a0651917390510006028c8cc6a4b9c8288002885a31c5821912044001504d190c322a49022000a8268c652194248110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x4b
  | 7 => 0x4c
  | 8 => 0x4e
  | 9 => 0x5
  | 10 => 0x94b
  | 11 => 0x94c
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124c
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138c
  | 18 => 0x138e
  | 19 => 0x98c
  | 20 => 0x98e
  | 21 => 0x128c
  | 22 => 0x128e
  | 23 => 0x10b
  | 24 => 0x10c
  | 25 => 0x10e
  | 26 => 0xa0b
  | 27 => 0xa0c
  | 28 => 0xa0e
  | 29 => 0x130b
  | 30 => 0x130c
  | 31 => 0x130e
  | 32 => 0x180b
  | 33 => 0x180c
  | 34 => 0x180e
  | 35 => 0xb0c
  | 36 => 0xb0e
  | 37 => 0x140c
  | 38 => 0x140e
  | 39 => 0x28b
  | 40 => 0x28c
  | 41 => 0x28e
  | 42 => 0xb8b
  | 43 => 0xb8c
  | 44 => 0xb8e
  | 45 => 0x148b
  | 46 => 0x148c
  | 47 => 0x148e
  | 48 => 0x184b
  | 49 => 0x184c
  | 50 => 0x184e
  | 51 => 0xd0c
  | 52 => 0xd0e
  | 53 => 0x188c
  | 54 => 0x188e
  | 55 => 0xd4c
  | 56 => 0xd0a
  | 57 => 0xd09
  | 58 => 0x1889
  | 59 => 0xd0054
  | 60 => 0xd0056
  | 61 => 0x188a
  | 62 => 0x188054
  | 63 => 0x188056
  | 64 => 0xd4a
  | 65 => 0xd49
  | 66 => 0x1a09
  | 67 => 0xd4054
  | 68 => 0x4d54
  | 69 => 0xd4d
  | 70 => 0x98954
  | 71 => 0x98956
  | 72 => 0x128954
  | 73 => 0x128956
  | 74 => 0xb0954
  | 75 => 0x94b14
  | 76 => 0xb0956
  | 77 => 0x94b16
  | 78 => 0x140954
  | 79 => 0x95414
  | 80 => 0x140956
  | 81 => 0x95416
  | 82 => 0xb8956
  | 83 => 0xb8954
  | 84 => 0x94b94
  | 85 => 0x94b96
  | 86 => 0x1489
  | 87 => 0x148956
  | 88 => 0x148954
  | 89 => 0x95494
  | 90 => 0x95496
  | 91 => 0xd0954
  | 92 => 0xd0956
  | 93 => 0x188954
  | 94 => 0x188956
  | 95 => 0xd4954
  | 96 => 0x94d54
  | 97 => 0x289
  | 98 => 0x10a
  | 99 => 0x130a
  | 100 => 0x14c9
  | 101 => 0x134a
  | 102 => 0x99254
  | 103 => 0x99256
  | 104 => 0xd1254
  | 105 => 0xd1256
  | 106 => 0x189254
  | 107 => 0x189256
  | 108 => 0xd5254
  | 109 => 0x124d54
  | 110 => 0xb1394
  | 111 => 0x138b14
  | 112 => 0x138b16
  | 113 => 0xb9396
  | 114 => 0xb9394
  | 115 => 0x138b94
  | 116 => 0x138b96
  | 117 => 0xd1394
  | 118 => 0xd1396
  | 119 => 0x189394
  | 120 => 0x189396
  | 121 => 0xd5394
  | 122 => 0x1a0a
  | 123 => 0x138d54
  | 124 => 0xb0994
  | 125 => 0x98b14
  | 126 => 0x98b16
  | 127 => 0xd0994
  | 128 => 0xd0996
  | 129 => 0x98d14
  | 130 => 0x98d16
  | 131 => 0xd4994
  | 132 => 0x98d54
  | 133 => 0x148116
  | 134 => 0x148114
  | 135 => 0xd0114
  | 136 => 0xd0116
  | 137 => 0xd4114
  | 138 => 0x10d54
  | 139 => 0xb8a16
  | 140 => 0xb8a14
  | 141 => 0xa0b94
  | 142 => 0xa0b96
  | 143 => 0x184a14
  | 144 => 0x184a16
  | 145 => 0xa1854
  | 146 => 0xa1856
  | 147 => 0xd0a14
  | 148 => 0xa0d14
  | 149 => 0xd0a16
  | 150 => 0xa0d16
  | 151 => 0x188a14
  | 152 => 0xa1894
  | 153 => 0x188a16
  | 154 => 0xa1896
  | 155 => 0xd4a14
  | 156 => 0xa0d54
  | 157 => 0x1949
  | 158 => 0x134d
  | 159 => 0x29314
  | 160 => 0x29316
  | 161 => 0x149316
  | 162 => 0x149314
  | 163 => 0xd1314
  | 164 => 0xd1316
  | 165 => 0x189314
  | 166 => 0x189316
  | 167 => 0xd5314
  | 168 => 0x130d54
  | 169 => 0xb9816
  | 170 => 0xb9814
  | 171 => 0x180b94
  | 172 => 0x180b96
  | 173 => 0xd1814
  | 174 => 0x180d14
  | 175 => 0xd1816
  | 176 => 0x180d16
  | 177 => 0xd5814
  | 178 => 0x180d54
  | 179 => 0xd0294
  | 180 => 0x28d14
  | 181 => 0xd0296
  | 182 => 0x28d16
  | 183 => 0xd4294
  | 184 => 0x28d54
  | 185 => 0xd0b94
  | 186 => 0xd0b96
  | 187 => 0x188b94
  | 188 => 0x188b96
  | 189 => 0xd4b94
  | 190 => 0xb8d54
  | 191 => 0xd1494
  | 192 => 0x148d14
  | 193 => 0xd1496
  | 194 => 0x148d16
  | 195 => 0x189494
  | 196 => 0x149894
  | 197 => 0x189496
  | 198 => 0x149896
  | 199 => 0xd5494
  | 200 => 0x148d54
  | 201 => 0xb4d
  | 202 => 0xbcd
  | 203 => 0xd1854
  | 204 => 0xd1856
  | 205 => 0xd5854
  | 206 => 0x184d54
  | 207 => 0x104a
  | 208 => 0x188d14
  | 209 => 0x188d16
  | 210 => 0x14b
  | 211 => 0x8e
  | 212 => 0x198b
  | 213 => 0xa4b
  | 214 => 0x134b
  | 215 => 0x150e
  | 216 => 0x2cb
  | 217 => 0x20e
  | 218 => 0x19cb
  | 219 => 0xbcb
  | 220 => 0x14cb
  | 221 => 0x154e
  | 222 => 0x74b
  | 223 => 0x40e
  | 224 => 0x194b
  | 225 => 0x1a8b
  | 226 => 0x104b
  | 227 => 0x160e
  | 228 => 0x1a49
  | 229 => 0xeca
  | 230 => 0xec9
  | 231 => 0x1a4a
  | 232 => 0xec053
  | 233 => 0xecd
  | 234 => 0x1a4d
  | 235 => 0x1a0d
  | 236 => 0xb09895c
  | 237 => 0x9894b1c
  | 238 => 0xb09895e
  | 239 => 0x9894b1e
  | 240 => 0xd09895c
  | 241 => 0xd09895e
  | 242 => 0xd49895c
  | 243 => 0x9894d5c
  | 244 => 0x14d
  | 245 => 0x14a
  | 246 => 0x2c9
  | 247 => 0x95896
  | 248 => 0x94d16
  | 249 => 0x144d
  | 250 => 0xec953
  | 251 => 0xd09925c
  | 252 => 0xd49925c
  | 253 => 0x9924d5c
  | 254 => 0xed253
  | 255 => 0x139416
  | 256 => 0x99556
  | 257 => 0x150996
  | 258 => 0x99616
  | 259 => 0xe8a
  | 260 => 0x18ca
  | 261 => 0x194a
  | 262 => 0xec113
  | 263 => 0xecb
  | 264 => 0x1a4b
  | 265 => 0x11494
  | 266 => 0x10d14
  | 267 => 0x11a94
  | 268 => 0x11496
  | 269 => 0x10d16
  | 270 => 0x11796
  | 271 => 0x749
  | 272 => 0xed313
  | 273 => 0x181896
  | 274 => 0x29896
  | 275 => 0xec293
  | 276 => 0xb4d55
  | 277 => 0x1a0b55
  | 278 => 0x149854
  | 279 => 0x149856
  | 280 => 0xed853
  | 281 => 0x185496
  | 282 => 0x184d16
  | 283 => 0x185796
  | 284 => 0xb8293
  | 285 => 0x9296
  | 286 => 0xcce
  | 287 => 0x15ce
  | 288 => 0x151296
  | 289 => 0xcc996
  | 290 => 0x15c996
  | 291 => 0x170e
  | 292 => 0x21416
  | 293 => 0x155416
  | 294 => 0x154b16
  | 295 => 0x154d16
  | 296 => 0x41896
  | 297 => 0x189616
  | 298 => 0x1a9953
  | 299 => 0x160d16
  | 300 => 0x4ed3
  | 301 => 0xecb55
  | 302 => 0xb4ed5
  | 303 => 0x10ed3
  | 304 => 0xd4d14
  | 305 => 0xd1516
  | 306 => 0x17cb
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1911
  | 6 => 5273
  | 5 => 4148
  | 4 => 573
  | 3 => 35
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 7 => packedAt gbK7 (78351+((h/637+packedAt gbK7 (70707+(h % 637)*12) 12) % 2294)*12) 12
  | 6 => packedAt gbK6 (277702+((h/1757+packedAt gbK6 (253104+(h % 1757)*14) 14) % 9263)*14) 14
  | 5 => packedAt gbK5 (262698+((h/1382+packedAt gbK5 (244732+(h % 1382)*13) 13) % 5475)*14) 14
  | 4 => packedAt gbK4 (42020+((h/191+packedAt gbK4 (40110+(h % 191)*10) 10) % 688)*11) 11
  | 3 => packedAt gbK3 (2901+((h/11+packedAt gbK3 (2835+(h % 11)*6) 6) % 47)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff83ffe18383f0fff8703ff81fc288cf04f1cf
  | 1 => 0xc1fc3c1e03fc3f0e0f803c3fe3cd74b43b4933
  | 2 => 0x1ffc01ffc003ff00fffc03ffc318738c38e3c
  | 3 => 0xfe00001fffffc0000fffffc0003e07c0fc0fc0
  | 4 => 0x1ffffffffff0000000003ff800fff000
  | 5 => 0xffffffe00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2004400000040120010040800000001001045
  | 1 => 0xd0a4284601a411042c80a892c3843494194912
  | 2 => 0x14a8088a4002aa04125002518118128428228
  | 3 => 0x742021134aea80008e4ab38040ae06c0ac0d80
  | 4 => 0x2042021df3533cc9e0030101893bd800f7e000
  | 5 => 0xb9f333c060620881040c2206123feffe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36266
namespace PEqualNP.Outside.L_meta_36266
open PEqualNP.Outside.L_meta_36266.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 68 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 129 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_224 : Interval s3Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 228 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 bs3_3_224)))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 16 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 2 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 30 := bs5_3_0
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 712 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 735 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 (concat bs5_5_384 bs5_5_416)) (concat bs5_5_448 (concat bs5_5_480 bs5_5_512))) (concat (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)) (concat bs5_5_640 (concat bs5_5_672 bs5_5_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 35 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_544 : Interval gbAtlas 4 544 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 573 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)))))
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
theorem bgb_5_4128 : Interval gbAtlas 5 4128 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4148 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))))))) (concat (concat (concat (concat (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176)) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816))) (concat (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072))))) (concat (concat (concat (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)))) (concat (concat (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)) (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840))) (concat (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 bgb_5_3968)) (concat (concat bgb_5_4000 bgb_5_4032) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128))))))))
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
theorem bgb_6_5248 : Interval gbAtlas 6 5248 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5273 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)))))) (concat (concat (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920))))) (concat (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))))))) (concat (concat (concat (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)))) (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072))) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))))) (concat (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712))) (concat (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)))))) (concat (concat (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))) (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))))) (concat (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))) (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))) (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))))))))
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
theorem bgb_7_1888 : Interval gbAtlas 7 1888 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1911 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672))) (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800)) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928))))) (concat (concat (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152))) (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))) (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8feeefaeafeeafae8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4276812520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36266.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.or,[2,5]⟩,⟨.or,[3,7]⟩,⟨.and,[4,8]⟩,⟨.and,[2,3]⟩,⟨.or,[2,9]⟩,⟨.or,[0,10]⟩,⟨.or,[6,8]⟩,⟨.and,[12,13]⟩,⟨.and,[1,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276812520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276812520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36266

open PEqualNP.Outside.L_meta_36266 in
theorem PEqualNP.Outside.L_meta_36266 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276812520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276812520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
