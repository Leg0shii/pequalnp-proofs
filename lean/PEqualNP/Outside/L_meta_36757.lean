import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36757.Model
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


end PEqualNP.Outside.L_meta_36757.Model

namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
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

def SBf (j : Nat) : Nat := [4, 4, 8, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36757

namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
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
end PEqualNP.Outside.L_meta_36757
namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
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
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf80fffffe03ffffffc07e07fffe07ffff23e3f
  | 3 => 0xfe01fffc03fc07ff8007e07ff83f01c33cc
  | 4 => 0xfff0001fffffc0007fffff8007fffc001fc3f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8202142220484880858a48a48a8851544d4d5
  | 2 => 0x5545528c51a929323605485595446aaa922a2a
  | 3 => 0x46a994d694a3b21adeac1466c67d23c0dc334c
  | 4 => 0x64cd1b19193223a367367941079670831b43b0
  | 5 => 0x870e1c1e1e3c3c3c7bc79e79e418430c1fbc00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaa0a0aaa0a0a0aaaaa0a0aaa0a0a0aaaaa0a0aaa0a0a0aaaaa0a0aaa0a0a0aaaaa0a0aaa0a0a0aaaaa0a0aaa0a0a0aaaaa0a0aaa0a0a0aaaaa0a0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36757
namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x843f541087ee6210fd0c421f790843f621087da4210fd48421f2908437e50086faa010df94f40ef29e815e53d02faa7a07754f40aea9e81be43d037887a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f50e40bf294817d529037c85206f10a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81be435037886a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6205f54c40dfa1881bd43102fca4205f54840df21081bc42102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a661be54cc27ca9985f55330deaa6613d54cc2f8a9985f94b30bea96617e51cc2faa3987e90330fca06617f548c2fca9186f952309f2a4617d548c37aa9184f55230be2a4617d538c3bc87187750e30bf294617d528c3bc6518770ca30bf28c617d518c3bc6318770c630bf28461df308c3f661185fd5130bf2a2617d544c2f8a8985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8185f55030be2a0617e530c3bc86187750c30bf290617d520c3bc6418770c830bf288617d510c3bc6218770c430bf28061fa400c3f2801877cc030fd18061dd300c3f26018764c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xc5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a17d94742bb28e857d51d0beaa3a15d54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0997ed4132bda82657c504cbf0a0995e14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cafca7a0df54f41dfa1e83bd43d06fca5a0fb94b41b7296837d52d07daa5a0db54b41df21683bc42d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520efd0a41dea14837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941df21283bc42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883be43107788620df94841bea9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c6faa418df94431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c87ec8390fd50721fb98e43f431c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea9443ee42887da8510fbcca21f6194437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fb90821f6a1043ef32087d86410df94421fb20
  | 2 => 0x5a76c000002d6008000001aa8184619b0002e4480764aa0007001411e6185122045e40c960bb314000002250002a82600033200000260000000e7a2709e1802b00000000000000000000000943ec1689200029e14000000268000002380ba0000025c3e0000000003388d1250720063ec000000000000023206c958288c50f46ec9c2500526601986d3603cd121ee024800a5a752ca00032a3d0d49b0000000ee5d0730000000009b0532740003f0d438e5bcc02624ba760cf13b3c45f00ea0c1d46540002e2663e48a0f13542d840800082000d5805406948742440004bc949230003f0b9800000068001b1000738821462a4000889882fe000ab00e37096d0a1a611a3dc0017a4b03d8109151a67dc0000c16a61524000046000808d70006504c82b2e09c06b1c91bc420cb91c0160001211808816c9e0000007951b02f382000dc81f3fc3b81c0b120c39475800282200000d900060c00000196474fa1514803bc661fc380161248753842acda0bf00017ca01931860000012b3a2520000ad34e0000020123e6b0bc00024e0dc9419a1366040017106263502a2a21259ce186b1146f43410c43e274fca0d3fa0ec000a830e58c7a9ec000000e98000001500007c1e843915a680e05144a88b04c4f8000000b84952b9840222801610d1841200004d3f46f8428000008f800000000414968004822b130800000779228960000004b8433b89c4001f30000002283541293d0b80032c74867800094728be94d2000187f0da2a656ca50ae4f04f4b719224200000253390000398c60d84fcc615f2bc0001800033e238db1a44e63c90a8a62648891a8000009b4d180031c000931440008108100038c5242311a09659137a4d00062c370280722e8509553d03480c17b3ac218549e13ea77cad0b40bc999339ba03827848a0725c0240e000020040901c0700006010000080e02401000010240200400000000400400803004000240801c010100005801000090140000c16020050080600c0100801008000280101801008040001501c010000001804000010040f00400010040000201c010000200c000200e02c0c00005014020240100c020000300003000020080401c020000101c0000406000180080903000020000040100000008020340001025004000040001007004000601d014060040501c0701800004010340b0000300808004060000401c0301c0000c0200401004070180d0080000801004020080000003008020200501c070040000007014010180207c0001811000060000502c010000100010006fca5a1df54b43bf28e877d51d0efca1a1fe94343bd286877d50d0ff2a1a1de54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877
  | 3 => 0x6f00f0000002dd0da6500072c1e0ed220478c815d3cc82cd7000000000d78003c828c410001c44812c9692ee000dfa2e000000a60001784d4001d0452000202230007ac0a91b0b245cbf10f0005412a000340028000b226e598389132b0750598984d60000023f000000b622c2c238c650642a87146394e36e5d89521e0685803c9d920e345140004e80001500007a2f8ac800000001259393647c47f8000006b40000048475c000004be860000003d2000a3a30112000850bd0cc148ae0002e48b400210000820fd80031e000d10000002c0f380f0365b4c88630fe3b031092476000749ea4c685843a694b46a06826e49878c0b1a12860246e8193de6750980044c0001f8003f02107d1302d0338ab80000000000078216089188f80008e8270000001f43d8491345d4020253fe6cc7821a0000040024e3ba90c6c0af398041070cd3529c85200004e8ccd291608e29c000130e891c0021d07c3705c21c1928f11b80841e00073800404448000674723f400000000990000883041084e1793da2953c9221883841d0004ee15c1000000075406a46064884a10174226d4b520a26220c600001be3044f80043276909119000734000db000000001e0000001289f22c49a8000930d200030a5e0001bc03a76388000640003120007200000015400
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x9544c27761551309d185544c23e64149308f590524c23e64145308f590514c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30b6582430c23f64548308f191520c27761548309d185520c29d640c830b6580320c23f64544308f191510c26f62544309b189510c29d640c430b6580310c23e64940308f592500c2796590030b658e400c3994390030e690d400c29d64cc030ae592300c2d9638c03097d95300c27b654c030b6d95300c35b654c030b6d91300c2d9644c030b6189300c2d8614c0309798c54c825d63153208fd9153c823c6454f208f99053c823d6414f208f99251c823d6494720d6d4c30c827661152209d584548823e64d4e208f593538827661d4e209d587538823e6494e208f592538823f64546208f191518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614f204836451881208f596540823e64150208f993530823d64d4c208f990530823d6414c209d98453082756114c20cb552210832d5408420d9544210833954cc0209e5943008339540c020d654c300826f6548020b9185200827b6548020b618d200825e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c435b530c3109b988548426d62152108f993538423d64d4e109b98b538426d62d4e108f992538423d6494e108fd91528423c6454a108f990528423d6414a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104423d65950108f990540423e64d4c108f593530423e6414c108f590530426e6214c109b588530423e64d48108f593520423e64148108f590520425e63148109758c520433554c84109d59421043355408410d9548210433954cc0109e5943004339540c010d654c300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xca3f64542328f191508ca3e64951329d986544ca7561951329e982544ca7960951329dd85544ca7461551329ed81544ca7860551328f994544cb3754d4532cd153514cb375414532cd150514cb673214532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d68c8504ca3d65950328f990540ca5f654c832b6181320ca6f654c832b9185320cab960d0f41cbd0d52d072d4354b41cb54a42d072d5210b419ed8153906786054e41ad58742906ad62d0641b998b419065f63542419718d509063e65d0d41ae583435063e6510941b998b415063d6590c41ad587421063f6550841ab58b411063f65504419dd95411066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc67a60152319e580548c63e6494a318f592528c63f64542318f191508c63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c72f54d4931cb153524c72f5414931cb150524c76452cc531ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c7685214131d68c4504c63d65950318f990540c65f654c431b6181310c677654c431b9189310c73561953218f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f21cd95241c86b5640c721cb58a548863e64d4e218f593538867a60d4e219e583538863e6414e218f590538872e5490a21ab59032886ad64c8621cd553218866d62951219d586544865f63551219718d544867b60551219e181544863f6454d218f191534866f6254d219dd85534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530867b6054c219e181530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b9586420866d650c821ab59032086e5610c8218f992510863d64944219d59641086e56290421e950a41087a642504219d59431086b5640c421b958831086ad64c8421ad59221086e562884219bd9521086776548421b9d9521087676548421b9d9121086e56448421b998d21086e46348421b9181210863f64540218f191500865f63540219718d500871d5390f40c754c43d031d53d0b40ad58742d031d5350b40c754f41d02ad62d0740c754d41d02b960d0e409dd8552902746154a409bd89519026c6254640a758f40902da63d02408f994435023e65d0940ad587425023e65d0540ab58b41502da63d0140ae583431023f6550c408f596421023d6590440a758f401023f65500409ed9540103396095330ce95240cc31d6395230c7952438c29d640ca30a7590318c29d64cc230ce553308c25d63951309e582544c26f62551309b18
  | 2 => 0x840006eb1a9da7e219642d81a0000057800cfaec00098001d60014404180000000003a2fae2000005c2320000000000c28000004842362000e2b482c1c0409ab903caca35ae671208958202a80039a522093e003a498000a9000003440016c0020c002d03e00061006779f813a2842854731c2872f6ae92681000a10b8000664b2f8cc9423b2b05505ae1a8657000002180037ac09fc6b35a0000036a146ca1a003641f104280302a3344a17c0038ca9b2e232c2d3a02d1a5eb780011338dd800441b4db8ce028320f9e0190f0b3aeee69e407ae0bd2744a9a2dc2946706e930ea6780000026000006695645b3cbf1e65e80026858382c0a0ad48c22c8d9c88d2aa6a000000001880098b9c87800db000178007b952001d4000006615853016b93a29e8b4000000027cd48001e8d4e00d2453785886800074ad9f000042d204a8a8048f8009989e2c8e8371eaca1ce22388e5960000a4bf87e00000000000018c0009c71800001a6000006a9dc000846529aa4134b2200468000020e472c63f1929e1fa970085aa5a9a3044e0603fb2a093000031ed9800d0000170ee4e8004baacc928c9b38a00000c188e0018a001fe000008eb0e0000000312b58c04f122d8000d0b16ba98e3d800001680000091aa2b3250e38bcd31bc2415ad7b10962440e174ba1da8f10e148f40324a00000c62b8c506acb06c68000000185fb74cc186609c000292a29d80000040350000000b90200000002206fabebe95031b3a322b2431d01dac46400e93800001969028032b4a502dc0a8925b91e000725c8ba88aa0003a0e4a6e99000599361591248358bc8964c124000003088a00002330e4001ae000000031c07028e0b0874a12df08000148af368cd800c9812dc8ac5db9ec88000000000000a3a0a62272003980029eaa0140201202c1511c0700403008000100c00021004000000100c0000404004110081100001038020040000009004020040100000014010000a0100100401000070080000403000080280102c050000007c05028000640c01403000000040103404028020080b0000000000024000001800021000010040200801048050180d000080100c0440701c0d00c020700001c09030010100701402018020000900400000000500704400040000040b010040100700407010010180400009000010080704c1a052b960d0e43b69834390e776154a439d1855290e6f62546439b1895190eda60d0d43ae5834310e3f6550c4397d954310eb960d0f42cdd0d51d0b3543547429ed815390a786054e42ad5874290ae661d0a4297d8d5090a5c63542428f9974350ab960d0d42b99874250a3d6590c42ad5874210a3f65508429bd954210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518
  | 3 => 0x14a7d2387c9ec29a96728009204cb6800bc0000022e00022001b800000e50003603c00178859182c2266c0de53800e1000819e2953549c046c80006d8ae1e288250c400036000fa00000002ae00034d5800da8d01400000000a62b4002d8419467da9cd700028a2490b0cdf9e84c9a4
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xb0240838060008a43000d02980080010298b8686a8e854a5c34354b4194ae9b2a4210cc4735912108670382c890843295d0634842194ae83024210e155358742d0306a9ac5a0e81265d3654c030990e4b2260184d071591300c24cba0c498061265d0614c030
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 634
  | 4 => 467
  | 3 => 14
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (19228+((h/211+packedAt s2K5 (17118+(h % 211)*10) 10) % 837)*11) 11
  | 4 => packedAt s2K4 (19296+((h/155+packedAt s2K4 (17746+(h % 155)*10) 10) % 617)*10) 10
  | 3 => packedAt s2K3 (706+((h/4+packedAt s2K3 (686+(h % 4)*5) 5) % 22)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffe03fc07fffffc0ffffff80fc1fffcff81ff
  | 1 => 0xc07ffffff80ffffff03f01fffffe0fff31fe3f
  | 3 => 0x7ffffffff01fffffc001fffffff07fc1ffc7
  | 4 => 0xff8003ffffffe03ffffffe000fffff83fe0ff8
  | 5 => 0xfffffc000000003ffffffffff0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x430298c47122448c02cb325982c094e45780db
  | 1 => 0x9524294890e48914b01550aa95520d2930b62d
  | 3 => 0x2a4852912241d2295540a13529a5a052c15b46
  | 4 => 0xc616322448903b269a6c4060e394a03aa0db0
  | 5 => 0x307183c3870e1c3f8e38f9c7c0318c63fde000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaacc00ee888800eeaacc00ee888800eeaacc00ee888800eeaacc00ee888800eeaacc00ee888800eeaacc00ee888800eeaacc00ee888800eeaacc00ee888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36757
namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x100028c01381260016a400400c80be43bc43bf42bd42df32dd32bf41bd41be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1000403009aa8e8558504ca38a6a0cd54440
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
  | 3 => packedAt s3K3 (112+((h/1+packedAt s3K3 (108+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffc0ffffc0ff07ffffc0ff83ffe07e7f33f3
  | 1 => 0xf81fff03ffff07f83f03ff07fc3fff81b1ccfc
  | 2 => 0xfffffffc1fffffffc003ffffffc1ffffc1ff1f
  | 4 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x90c44628848941014b24c8498053212c171171
  | 1 => 0x324c8a1909184b2815615942a4354b04b144b4
  | 2 => 0x4111104052208452808222944a80945140aa0a
  | 4 => 0x659a249243b2969ce6c8308773280619ea0fc0
  | 5 => 0x861c38e39c3ce7e738f3bce062311861fdf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0e8e8e0e0eaeae0e0e8e8e0e0eaeae0e0e8e8e0e0eaeae0e0e8e8e0e0eaeae0e0e8e8e0e0eaeae0e0e8e8e0e0eaeae0e0e8e8e0e0eaeae0e0e8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36757
namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x60000c95008728408588008007be43bc43bf42bd42df32dd32be41bc41de31dc31bf40bd40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc840009ca868554514ca72a020c714d40
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
  | 4 => packedAt s4K4 (212+((h/4+packedAt s4K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffc0ffffc1ff07ff03c1ff87ffe07ef133f3
  | 1 => 0xf81fff03fffe07f83ffffe07f83fff813fccfc
  | 2 => 0xfffffffc1fffffffc003ffffffc1ffffc1ff1f
  | 3 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x90cc46288492c3014b60d0c98273212c711171
  | 1 => 0x32448a19091049281525524288154b041744b4
  | 2 => 0x4111104052210452808225145480945180aa0a
  | 3 => 0x659a249243a5969ce6c8218767280619ea0fc0
  | 5 => 0x861c38e39c39e7e738f3b9e046311861fdf000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xece0ece0e8e0e8e0ece0ece0e8e0e8e0ece0ece0e8e0e8e0ece0ece0e8e0e8e0ece0ece0e8e0e8e0ece0ece0e8e0e8e0ece0ece0e8e0e8e0ece0ece0e8e0e8e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36757
namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x410990060024785540118026405181c341a14e94e9c0090d0022000142e1c9010088f9e18640021600a8000a15800058d80520800c2280046016002081ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc817d519037c83206f10640bf28481bf40903f681205fd4d40efa9a815f53502f8a6a07714d40ae29a817f52502f8a4a06fd0940dea1281df32503ba64a05fd4540be28a81fb405037c80a05f95040bf298817d531037c86206f10c40bf290817d521037e84206f50840ef99081dd32102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9985f94b30bea9661bf42cc37a859877ccb30ee996617e51cc2faa3985fd5230bf2a4617d548c2f8a9185f54e30efa1c61dc438c2fca5185f54a30dfa1461bd428c3be6518774ca30bf28c617d518c3bc6318770c630bf28461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a261bc544c278a8985fd4930be29261bf424c37a849877cc930ee992617f514c2f8a2987ecc130ef182617f540c2fca8185f55030be2a0617e530c3be86187710c30bf290617d520c37e84186f50830ef99061dd320c2fca2185f54430ef18861dc310c2fca01877cc030fd18061dd300c3f260185fd5320bf2a641be54c827ca9905f55320deaa6413d54c82f8a9905fd4f20bf29e41de53c82bca7905f54f20eea9e415d53c82f8a7906fd0b20dea1641df32c83ba65905f94720bea8e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d528837e85106f50a20ef99441dd32882fca3105f54620f710c41ec21882fca1107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41bf424837a849077cc920ee992417f51482f8a2907ec8120f7102417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6107794c20af298417d53083baa6105754c20be298417e520837e84106f50820ef99041dd32082fca2107d94420bb288417d51083eaa2105d54420f710841ec21082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf296217d52c42f8a5886fd0b10dea1621df32c43ba65887d88710fa90e217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c217f52842fca5085f54a10be29421bf428437a850877cca10ee994217d51842fca1087e88210fc90421f710843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4d10efa9a215f53442fca6885f54d10be29a21dc53442b8a6885fd4910f7a92216f52442fca4885f54910be29221ec52442d8a4886fd0910dea1221df32443ba64887d88510fa90a21fa20443f240887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be29021bf420437a840877cc810ee990217e51042fca0087dc4010fd08021f510043f220087c44010
  | 1 => 0xd518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65de434cbba86997710d32dfa1265ee424cb7a84997b50932d6a1265ef324cbbc64995fd4532be28a657f504caf8a09977d5132ef2a265dd544cbb8a89977d4932e7a9265df424cb3e84997790932e721265dd424cb3a84997350932c6a1265dc424cbbea2997794532eea8a65dc514cbbea0997794132eea8265dc504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195794c32bf29065bf420cb7a841977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e837e52d06faa5a0efd0b41dea1683df32d07ba65a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42907be6520f74ca41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0dfd4941be29283bf425077a84a0f7cc941ee99283f7415077c82a0dfd4141be282837e54106fca620df54c41df21883bc43106fca420df54841dfa1083bd42107be6420f74c841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663bf42cc77a8598f7ccb31ee996637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31dfa1463bd428c7be6518f74ca31bf28c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a2637f524c6f8a498efd0931dea1263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31efa1863dc430c6fca418df54831dfa1063bd420c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790efd0b21dea1643df32c87ba6590df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d528877e8510ef50a21ef99443dd32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690efd0921dea1243df32487ba6490fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821dfa1043bd42087be6410f74c821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e817e52d02faa5a06fd0b40dea1681df32d03ba65a05f94740bea8e817d54902fca7205f54e40df21c81bc43902fca5205f54a40dfa1481bd42903be6520774ca40bf28
  | 2 => 0x685b1a51e02f0ca8005b2000001b70000008f24d250000000003f2ab0000bb000000001c440660d0a92e372304f38001b0918e48005a4c1907990506a90000971fe661172f723aad4d21665548a036a010a68100026243e0005180d4400015f83550a89800000000000001e32d45b4f98f715e000f006a00407004010240481800010008020080c0180202028058000080000004008080280200000058120e01c090000001c010221080c0380e00802000040200013806018300100000000000080000600004028060282601800088020100402820010120000006010038180101c000240c0000681a0000e008020200c01000038460000423806028340100000000010000a80a00012000020a002028020000000006008000e0040c80803802068080000003864068000100c0580c048040200200800000020200e0100c0a00805006060261d8020300204018010040000600010000000103e0c83e000020000a0000a020000081a0383811004040060580600014010080880c000000181c0200a00816040260000c00000000020304c04006000480082e00000008280580800000120080000004802028080880a0d8260580e0280001000068317e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621e750c43bf29087ee5210edca421df54843f6a90876d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85be43d0b7a87a16f10f42bf28e857d51d0afca1a15f54342dfa9e85be53d0b7aa7a16f14f42dfa8e85be51d0b7aa3a16f14742dfa8685be50d0b7aa1a16f14342beaa4853d5490afca7217794e42af29c857d5390bbaa7215754e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7c86a16f50d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a16fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42ef298855e5310afaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997790f32eea1e65dc43ccb7e85996f50b32bf28e657d51ccafca1995f54332efaa665de54ccbbaa9997715332efa16659f42ccbbc85997750b32cea1665dc42ccbbea3997794732eea8e65dc51ccbbea1997794332eea8665dc50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195754e32bf29465bf428cbdc85196f50a32f6a1465ad428cbbe65197bcca32bf28c657
  | 3 => 0x38a81310008704b2ad0f83653a800000b9c10ac14ac728d807604a3d43100013e1946f886594000490120009e80b17d3bc5ace613d06800052a8e07c39ccf266000ba171aa0000214922183584855e21b1f8adc6224f46200172288000440000dc47499546800000000470232609ccd38a21a2b6c900005dcc015422a2467fd809fb2907c03f1923e8121409e906e000132f52a42c906845000000000da1f68dc0602e000000de2cb25e49d2b9cb400001339a91d00015caa111881400000520be4001ec0000000029530c0011c993000c11289112d83f43d13f0080006986f24c354221df000b70140003d0a75281320b60e8bf8e9294740a48640dc639090b3442735602fc30e9dc002973029bd512e25b4264440840009e4099d30007b5448900bc8641da872ce6bca28f22a6968da2b45bc044030001681fd4b21153450089000058ae8318002ee000ff0000d6be08ba4a0b20005d22b4a678443800000430003052ac3b5048003d4b19191bb3820000014622cb95061330f06b4340ec0549497b08329e160458194dc50818ad54204186da273a4b4d4c8a40567c88298432e51d301b10fa0000e15915c0012c8a64e857904000000acd4c1551fc5053887016e71c7c00036400000165000001169a21845d8000002aeb7c9d101270284f2074346aec7a0d20006a0618813322fcb4291228224818eb3aa0006780838c0005f18d43c0b5240001540018391a006100730823a29c15f00053c0004c0003143cc000333d646522ac92b4128bf0490e201cceaec2c87152fb096065d47715f37a530b02293ec7f11d8cc4142a4b892b0363e8121150000fc4980043a6244d8d64e49ed1c0362e4b14e02ff6140780083c0ac7f4399793368d88428018e7606a08f340250059dc328228eb1361f2bc4f310d2727d5669e53a8a8cb985054c7744d00033e00070a3d1c641d349d720061453ace3220000001d0285854980018c6cc589180cebb4002d02383d9272e04d8a6d782340347891e0e20123bc2e8ab4169780008d2128bc1c27e0d8b0d3e05f0828917e8003160409b800000000000a853e2014105c6044f0950695989a8e128b4ec50c89800244b3d031b65e41e4f70ca19c84cb704d588bcc94a3e02a300002c82e076d4222219a904fc09c2148cc1100047e13ca20000009ac0000003ec200780051e70d3ea550003213fafb2c4764720d04f0ba40011b5d40a4051350a4974701630004ecc60000726d45624c0aa7dd03800084000f79be18a0003a84c35c91c5c87b56057000000000bf800043000254000000000012e0473549096b1255286851aafa0a2a1813a401d49b57597b16aa7017aa91e26583322513ca495e89d0009841820200083865a140404b0c7a162f40016a21a2e842c0c2b85b06e92480029a280002c7192738bc16f5567
  | 4 => 0x4b46ba8a296b749a2b65de244e405a5643785c18800040887ab13e29a12d969000560ce000486000820dd2f80000015d0006e072a640ae7e92c0bd08c6ac30000000bd0a884e42eb452a03d54e0c8cd22300aab8dfa63460a940007221c00000000304b98ada8c5ae2c0d30542a8008002c200012c0b91f0ee73cc014e45891157800496b84000000001849f0ad00
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c53082766114c209d584530823e64948208f592520825e63948209758e520823d65d0820c794f420831d53d08208fd95420831e5350820c754d420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320838d424c820cd95251083355494420d594e51083555394420cdd0a51083354294420d5cca51083553294420cd95151083355454420d594d51083555354420cdd0951083354254420d5cc951083553254420d9546210837151880209bd95200827b6548020dc545200825e63d53109758f54c423e64d4f108f59353c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c438d424cb109798f548425d63d52108f993538423d64d4e108f992528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10e3509328423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544431f54d4d10c7153534425d62d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d1097588534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910d914a21442746548510bc18121443685288110f888620442786548110bc185204425f63550109718d540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423e64948108f592520425e63948109758e520423e64148108f590520425e63148109758c520427661148109e980520432e5250810cb549420434e524c810d3549320438d424c8109e59610042f161840109dd95100427b6544010bcd9510043736544010ecd9110043b06444010f4d8d10043d06344010f8d8910043e06244010dcd4910043715244010ecd0910043b14244010f4cc910043d13244010
  | 1 => 0x86786054d21e3509324865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530863e64948218f592520865e63948219758e520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420865d65cc821c7953320871d54cc82197d95320871e544c821c7551320878d424c8219bd9521086776548421ce95250087395494021d694e50087595394021ced0a50087394294021d6cca50087593294021ce95150087395454021d694d50087595354021ced0950087394254021d6cc950087593254021dc885500877121540219798e52d025d6394b40cb54b42d034e524cb40d354932d038d424cb40ab588439025e6394a409758e529032d5250a40e3509329025d62d4d4097588535025e63149409758c525031f53d0940c714f425031f5350940c714d425032f5250940ae181425025e65cc94097197325025e654c94097195325038d424c940c714e405031d5310c40ab588431025e63948409758e521032d52d0840ae583421034e524c840d3549321038d424c84097d8d511025c6354440cd54441102b960104408fd95401029c63500409ed95401026e62153309b58854cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc27661d52309d587548c31f5410e30b3588438c23e6494a308f592528c34d524ca30e3509328c23d62d51308f992544c25f63551308f994544c23d62151308f990524c23d64149308f997424c23c65d09308f995424c23c6550930c7d53324c31c54cc930c7d51324c31c544c930d3d49324c38d424c930b6181324c31c548c1309b988540c26d62150309d984540c275611503097594430c31d5410c30b3588430c23e64948308f592520c32e5250830cb549420c34d52cc830b6583320c38d424c8308fd91510c23c6454430d5544310c2d9600c43097d95300c29c644c0309ed95300c25e63d53209758f54c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c831e5350b20c754d42c831e54ccb20c755332c831e544cb20c755132c838d424cb2097d8d548825c63552208fd91538823c6454e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20e3509324825e63d50209758f540827661d50209d587540823d65950208fd89540823d62550208f990540825e63150209758c540827661150209d584540823e64d4c208f59
  | 2 => 0x6550932e3d8d424cb8c6350932a7992324ca9d648c932e350a324cacd6295132b3d89544cad76155132b5185544cadb6055132b6181544cb1d5415132b3593524cb8f52d093297996424ca9d6490932b3996424cb4e6590932b3592424ca8d6490932e3d89424cb8f5250932b3995424cacc6550932e3d91424cb8f5450932e3151424cb8f6550932e3995424cb8d6550932e3195424cb8f6150932e3985424cb8d6150932e3185424cb8f6050932e3981424cb8d6050932e3181424ca5e6510932a7990424cace6210932e3508424cb8d42d4532e350a514ca9f6454532a7191514cb8d4254532b6d81514cad86054532e3508514cb555114532e350b504cb8d4294132a7d91504ca9c6454132e3509504cad76154132b5185504cb8d4214132d6540504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5e6394b419758e52d072d52d0b41d394932d074d524cb41e350932d06ad6210e419798e529065d6394a41cb549429078d424ca419758b535065d6214d419798c525065d6314941c7d4f425071c53d0941c7d4d425071c5350941cbd4942506b4615094197997325065c65cc94197995325065c654c941e3509325071c5390541c754c43106ad6210c419798e521065d6394841cb54b42106b561d0841d3949321074d524c841e3509321063f6550441a718d4110677655044197d8d501065c63540419b98854cc66d62153318f99252cc63d6494b31cb94942cc72d5250b31d354b32cc78d424cb319e983548c67960d5231c7d50438c6cd6210e318f992528c63d6494a31d3549328c78d424ca318f58b544c63e649513197d8d544c63e65151318f588544c63e64149318f590524c63e65d09318f197424c63e65509318f195424c71f54cc931c7153324c71f544c931c7151324c74f524c931e3509324c6d4614c931c7152314c66e62150319b588540c67a60150319e580540c65d6510c31c7550430c6cd6210c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c65f654c431a7191310c677654c4318fd91500c63c64540319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f21c794f42c871d53d0b21c794d42c871d5350b21c795332c871d54ccb21c795132c871d544cb21e350932c865f63552219718d548863f6454e218f191538878d424ca218fd91508863c645422197d8d508865c635422197d8d544865c63551219ed81544867860551218fd91534863c6454d219ed81534
  | 3 => 0x8d4cc94d124a64ff0710000014c000000000002bf34e000869e22ca000ca0001a20012084e32e231359560b09c46b80057c000df0000001e000000000a88000003761cca2800090000000005c69f4310be514764c6a4d4a21080014f276000db9813c06ac479983644f40a1204e6a9d5dad10b8b21748f91580f8ce1bf1785653c2554fc7ec0013e000000000004e011451aa60ae6180005a366424ec1255804289e2b820c2742c9c14303b10999b1e25807f8123708ac002c22325fcaf0fd0002913c90f58600000003000070780000000000000040400c00000000080c0300e0141300000008000680001801010040000901c010000000001010030040504c080081600802000010080000401030000000407c11080080300001c13010000041d00000004000000f04c0901001010050140504803000030140e000000080a0000100c060100100403004090600101c0500006014020040800401024380041403006008000000c0180000c000240000000000000080400000010040000000000000020000400404008020100301406048050000200c100440a00000004010000005c010000209000000010180a00c0502801004060241b01415004000000000c00020000a8010240802000004010180100c040202500400004020001b038090000703c0200800010110d80807003000000201a03c010c00302400008140280006c03a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a71854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c754c43d0a5f63547429718d51d0a5f63543429718d50d0aad62d4f42c754c53d0aad6214f42a7d8d51d0a9c6354742cd54451d0a9f6354342a718d50d0b395014342d398a5390b1e53d0a42c754f4290aae6290d42c714d4350aae6210d42a798e4250a9d6390942ab58a5350aaf6254d42add855350ab46154d42aed815350ab86054d42c754c5350aad63d4942a7d8d5150a9c6354542aed815150ab86054542cd5445150a9f6354142a718d5050ab76154142ad1855050b395014142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210b1c5450f32c755043cca3f64547328f19151cca3f64543328f19150ccacd62d5332c755054ccacd6215332e3d8942cca9f6454732a719151ccb555114732a7d9150cca9c6454332d654050ccb2e6295232cb951428caaf6550a32cbd95428cb1e54cca32c7553328ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca5c6550d32c7151434cb1d5410d32b3988434caad6490932b398e424ca6c6550932e3d0d424cb8e4350932e350d424cb8c4350932cbd95424cb2c
  | 4 => 0x408052e8003bc5b5168700a45f4b9a765823a0c71e72a44a4e4aa30003648a1932f84092d00001662c001a85120007321010e7840c0002ceadd4aae10000008d800000000f52b30000008c1510000ed780000003889b9b00006d53d00013e338000b820e0000002d00075c0020d33ca700b8ca45c748f689e4a873c371aa4e81309504d0d06104107b256770161421d6ae9228664f67c8000e502aabc40000000068001240427006e963156268d0aa049c4e85518506e92c328da160550a61ad4866f1041440006688416b30083d6d0842269181c80111c95c4b000000000f98000000007a9ba454000000000004396a8002b8001562a52f4b80000002cc5609800016e414192470005f8002e842e7692484659c000619fc4644d1178000000e80023d5d630172000000744530941743ecfb1a54424403b1ce048a84001833beb30362230000001fa8300cb98f200000000125027056854c523836200000189448ad92109703870cff8130002a065800000720000000000011b1110005b88b000000ac922179000ba80016946e4d4d198727e00000000000948000005b07dd0921f3d2000e981b000838bb8000ba4e5432804ca000dc8000007b00691a000000002ad502a48000001c01f9360b551c52128000000960000a715e234db0a5518000ea00020000002a8200047c0004f0000f16780010a098000002de5c0aba275943f82f8000000000000051e00158a404164103780040e0896480047c384b887c000b486415a3402d976211000001770b93a00010da394ceb3471823396318a387452816d498004c234c0000000026d4f922000448000384289640003300082417975000000002d02c452c28051182b14fc97403aa796580003e8b0a1a6e5ae0016f80019e000ca800082000000000009dc0012f0008785680000011ce68000004cc0000019aaf440988000aac918c91126411d0201e60a07d02e176a597894a4d04c4f28000002841e9012f019d241c25ac00101891344b78cf96a5a82fd2fa9b3e22c4302621f0718d4800578bbc612b43ba000000075c4710001f43582b81a0000000000000040a000cea91000000000e9000b716e9d527039c3087232c818bd8002a000cf80020605542a05324ca1cb22663de3b5148d4462220939725086993e15f3227a02f000000390e38002ba7e07b8554005d80023438a12c5e8002580000f2854da4d9548d20f4b4c00031000a690e800216000000001380001a8005608f03f8100524780b153394218ed9e6000858620004d25b0781f523a8ed520b44983d1051925ca000fea60000970908000002a545800280ae5321ee126631630081deb1cc780043220d129bd444a20049033d6aa91fadb22e9bd3500e4402880000000093c051cc0809794b89500053863aed44c1e4fd0d835e000750d6000
  | 5 => 0x6d10e20c1b8584150640d237c3511c1e48cc7e2300003793a8f65ce868078d5000a740012e1141593182500078c000003ac000000000ea43035946282001142a80c626466132000314c1049000000480ee000ad54684a404455299a406c10cad81925ab64598110001f4000440ee1b459272408260a48d01b601045ac44fe0000016855c958001ae5204a00625b1
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb920002cd400b448000000007829404c94c45000740cdca09034b00070010c8ced48655134009c012400014c5cf4e4c888fc551d28a92d303818300068241cd914bcf00508e0593c20d0c0e8107d440000accc6c010001104440f8143c6138851898a400088104002830004081040c3002c6c08904240a1045c09104102840143dc94354843a1eeaa1aa421d0f7650d5210e8638a86a9087431c14354843c1aa6b10a7a15147154c5350a8c382a629a85451cd5114542a60e0a88a2a1518735405050a9838aa028285835516215332a28e2aa0869951870550434cb0632a86a1265451c55415132a30e0aa0a89958771595424cac238acaa126562dc16550932b10e0b2a849960d65195424cac5b82c2a1265621c16150932d0ac230a849958771581424cac238ac0a1265a25806050932d1285b02a29968942181514ca8a3a2a228a65c15095114532aa0e0a88a29968542d85504cb42a10c2a8265461d15014132e1284a80a09955071540504ca86b90a6a12838514c6150941c1ccaa1264a0e0d53588431068d386a821c6383d516210e31a1ae42a26498d0e75509324c70a2a0c299263835516210c31e1284994a010f09424c95008686b90a6a12818614c6050940c1ccaa1264a060d53588431028b38ea821c6183d516210e30a1ae42a2649850e75509324c30c2a0c099261835516210c30a1ae4aa26410705424ca5108382a1264a884183d9363d4910c1ac8b18a48850d7214d4244286b98a4a1221435c8544c910a1ae8292648850e7550932442863aa849922183995424c910c18caa12648844d7218d5404216b90c8a9821435ce5250810a1ae929264086a0641891004360318c4880212c1d94244010e42a4a1220084d0764c910043a0a926488021e05093244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x244b38020280080180023580500600403a04815946550932a08805946550932a80805846150932a80815806050932d01421c15114532d01421c55014132a058214c6150941a0a80d516210e31a0582150614c931a098214c6050940a0681d516210e30a0982150604c930a80865093244010c80765093244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 14
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (23623+((h/259+packedAt s5K5 (21033+(h % 259)*10) 10) % 935)*11) 11
  | 4 => packedAt s5K4 (31162+((h/251+packedAt s5K4 (28652+(h % 251)*10) 10) % 995)*11) 11
  | 3 => packedAt s5K3 (4361+((h/28+packedAt s5K3 (4165+(h % 28)*7) 7) % 103)*8) 8
  | 2 => packedAt s5K2 (860+((h/4+packedAt s5K2 (840+(h % 4)*5) 5) % 22)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fffe07fffe1f07ff0ff0ffe1ff81fa39f3f3
  | 1 => 0xfe07fff81fffe1f83ff0ff0ffe1ffe05c67cfc
  | 2 => 0xfff83fffe0ffffffc000fff1ffe3fffe078f1f
  | 3 => 0x3fffff0001ffffff0001fffc0007f80fe0
  | 4 => 0xffffc000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa4308231442420014b013012602484b018b171
  | 1 => 0xc910450c848022815105104a2092c10c254b4
  | 2 => 0x104228820291115280888aa115425146050a0a
  | 3 => 0x5965b124921d559ce6aa0881d9901867680fc0
  | 4 => 0x618621c71ce199e738ccecc811006187b7e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0eee8e8e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36757
namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1000070d01000e81891e801795078a020988848018009c959b9e121180131997040d9d029f9f1a1403059c050000000b1d838f1a880010a094969b200c110e138a8618800f8c86800b9600001280190301081c10202000000a3478a00040861a14000017fd5005fe54017f55005fc54017fd4c05fe53017f54c05fc53007fd0c01fe43007f50c01fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803df3200ff8c803fd3200f74c803fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2002bf99510057faca8802afd6544015fe32a2002bf19510056f8ca8800a7c6544001ffb222000bfd91100077ec888002bf6444001ff3222008bf99110007fac888002fd6444001fe3222008bf1911000778c888002bc6444015ffaa2200aff95110057faa88802bfc5444001ffb1a2000bfd8d10007bec688002df6344001ff31a2007bf98d10007fac688002fd6344001fe31a2007bf18d10007b8c688002dc6344015ffa9a200aff94d10057faa68802bfc5344001ffa1a2000ff90d10007fa8688003fc4344013ffb122009bfd8910007dec488002ef6244013ff3122001bf9891004ffac488026fd6244013fe3122001bf1891004fd8c488006ec6244013ffa922009dfd491004ffca488027fd5244013bea922009ff1491004ffe8488027bf4244013ff2122009ff5091004f7a8488027fc4244013ff9922009f7cc91004ffc6488027fd3244013ee9922009ff0c910057fea28802bfe5144015fea8a200aff14510007fe8288003fe4144001fea0a2000ff10510007fe6288003fe3144001fe98a2000ff0c51004ffe4288027fe2144013fb10a2009ff4851004fea4288027fc2144015ffa82200aff94110057faa08802bfc5044001ffa022000ff90110007fa8088003fc4044001ff9822000ff8c110007fa6088003fc3044013ff9022009ff8811004ff44088027fd2044013fc9022009ff08110007fe2088003fb1044001ff0822000fd84110027feca08012ff6504009ff3282002bf99410026fcca0800a7e6504009feb282004bf59410006faca080027d6504009fe3282002bf19410007fec808002ff6404001ff3202008bf99010007fac808002fd6404001fe3202008bf19010027fea808013fe5404009feaa02004ff15010007fec608002ff6304001ff3182007bf98c10007fac608002fd6304001fe3182007bf18c10027fea608013fe5304009fea982004ff14c10007fe8608003fe4304001fea182000ff10c1001ffec40800eff6204007ff3102001bf9881001ffac40800efd6204007fe3102001bf1881001ffea40800f7f5204007ff2902003ff5481001efaa40800ffc5204007ffa102003efd081001ffc840800ffd4204007dea102003ff1081001ffe640800fdf3204007ff1902003ff4c81001fba640800ffc320400d7f3082004ffd4410027fca208013fd5104009fe2882000ffd0410007fc8208003fd4104001fe2082000ffcc410007fc6208003fd3104001fe1882003ffc841001ffc420800ffd2104007fe1082005bf98010027fea008013fe5004009fea802004ff14010007fe8008003fe4004001fea002000ff10010007fe6008003fe3004001fe9802000ff0c01001ffe400800ffe2004007fe9002003ff08010007fe2008003f71004001ff0802000fe84010007fa2008003f51004001fc8802000fc44010
  | 1 => 0xefe600c01dffa80600eff94030077faa01803bfc500c001ffa006000ff90030007fa8018003fc400c00fff9806007f7cc03003ffc601801ffa300c00ffe9806000f74c03003ff26018037ff200c01bff100600dff4803006ff84018033ff65c40197fb2e200cff99710015fccb88033fd65c40197eb2e200cff19710015f8cb88003ff64c40017fb262000ff99310045fcc988003fd64c40017eb262000ff19310045f8c988033ff54c4019ff2a6200cff55310067f8a988003ff63c40017fb1e2000ff98f1003dfcc788003fd63c40017eb1e2000ff18f1003df8c788033ff53c4019ff29e200cff54f10067f8a788003ff43c4001ff21e2000ff50f10007f8878801bff62c400d7fb162006ff98b1000dfcc58801bfd62c400d7eb162006ff18b1000df8c58801bff52c400dbfa962006ff94b10037faa58801b7d52c400dfe2962006ffd0b100377e858801bfe42c400dfea162006ef50b10037f8858801bff32c400def9962006ff8cb10037fa658801bdd32c400dfe196200cffd4710067fca388033fd51c4019fe28e2000ffd0710007fc8388003fd41c4001fe20e2000ffcc710007fc6388003fd31c4001fe18e2006ffc8710037fc438801bf621c400dfe90e2006fd48710037f84388033ff50c4019ff286200cff54310067f8a188003ff40c4001ff2062000ff50310007f88188003ff30c4001ff1862000ff4c310007f8618801bff20c400dff1062006ff48310037f8418802fff65840177fb2c200bff99610015fccb0802ffd65840177eb2c200bff19610015f8cb08003ff64840017fb242000ff99210045fcc908003fd64840017eb242000ff19210045f8c90802fff5484017ff2a4200bff5521005ff8a908003ff63840017fb1c2000ff98e1003dfcc708003fd63840017eb1c2000ff18e1003df8c70802fff5384017ff29c200bff54e1005ff8a708003ff4384001ff21c2000ff50e10007f88708017ff628400b7fb142005ff98a1000dfcc508017fd628400b7eb142005ff18a1000df8c508017ff528400bbfa942005ff94a1002ffaa5080177d528400bfe2942005ffd0a1002f7e8508017fe428400bfea142005ef50a1002ff88508017ff328400bef9942005ff8ca1002ffa6508017dd328400bfe1942009bf5861005ffea30802ffe5184017fea8c200bff14610007fe8308003fe4184001fea0c2000ff10610007fe6308003fe3184001fe98c2000ff0c61002ffe4308017fe218400bfe90c2005ff0861001dfcc10802fff5084017ff284200bff5421005ff8a108003ff4084001ff2042000ff50210007f88108003ff3084001ff1842000ff4c210007f86108017ff208400bff1042005fe8821002ffa4108017f9208400bfe1042000ffc4210007ee2108003fb1084015ffb2a200abfd9510006feca880027f6544015ff3
  | 2 => 0x30005fcc318003fd618c0017eb0c6000ff18630097fea31804bfe518c025fea8c6012ff14630007fe8318003fe418c001fea0c6000ff1063003ffe6318003fe318c001ef18c6000ff4c63003ff86318003dc318c01fff90c600fff8863007ffa431803ffc218c00f7f3046012ffd4230097fca11804bfd508c025fe2846000ffd0230007fc8118003fd408c001fe2046007ffcc230007be611801ffb308c01fff904600fff8823007ffa411803ffc208c023ffb2a6011bfd9530006feca980027f654c023ff32a6002bf9953008ffaca98046fd654c023fe32a6002bf1953008ef8ca9800a7c654c001ffb226000bfd91300077ec898002bf644c001ff3226008bf99130007fac898002fd644c001fe3226008bf1913000778c898002bc644c023ffaa26011ff9513008ffaa898047fc544c023ffa9a6007ff94d3008ffaa69801ffc534c001ffa1a6007ff90d30007fa869801ffc434c021ffb126010bfd8930087fcc498006fe624c021feb126010bf58930087f8c498006fc624c021ffa926010dfd4930087fca498043fd524c021bea926010ff14930087fe8498043bf424c021ff2126010ff509300877a8498043fc424c00fff9926010f7cc930087fc6498043fd324c021ee9926007ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c023ffa8a6011ff9453008ffaa298047fc514c001ffa0a6000ff90530007fa8298003fc414c00fff98a6000ff8c530007fa629801ffc314c021ff90a6010ff88530087fa4298043fc214c023ffa826011ff9413008ffaa098047fc504c001ffa026000ff90130007fa8098003fc404c00fff9826007fecc130007fc6098003de304c021ff9026010ff88130087fa4098043fc204c00fffb286007bfd943003ffcca1800afe650c00fbf32860029f9943003ffaca1803afd650c00fbeb2860009f5943003ff8ca1801efc650c00fffb206007bfd903003ffcc818022fe640c00ffeb206000bf5903003ff8c81801efc640c01dffaa0600eff95030077faa81803bfc540c00f7f3186007ffd4c3003ffca61801ffd530c00ffe2986007ffd0c3003ffc861801ffd430c00ffe2186007ffd883003dfec41801ffe620c0037f3106007ff5883006dfac41801ffc620c0037e310600dffd483006efea418037fe520c01bfea90600ddf5483006ff8a418037ff420c01bdfa10600dff9083006ffa8418037bd420c01bfe2106007ffcc83003fbe641801ffe320c00ffe990600df74c83003ff8641801fff610c00fff3086000bf9843003ffac218002fd610c00ffe308600effd4430077fca21803bfd510c01dfe2886000ffd0430007fc8218003fd410c001fe2086007ffcc43003ffc6218003de310c00ffe9886007ff0c43003fb86218037ff210c01bff108600dff4843006ff8421803
  | 3 => 0xe3188016ffd4c400b7fca62005bfd531002dfe2988008ffd0c40047fc8620003be4310011fea188008ff10c40047788620023ff62100117fb108008ff9884000dfcc420023fd621002b7eb108008ff1884000df8c420057ff521002bbfa908015ff948400affaa4200577d521002bfe2908008ffd08400477e8420023fe4210011fea108015ef50840047f88420057ff321002bef9908015ff8c8400affa6420057dd321002bfe1908008ffd8440047fcc220002fe6110011feb088000bf58440047f8c22005bff511002dff2888016ff544400b7f8a220023ff4110011ff2088000ef90440047fa8220023fc4110011de2088000ffcc440007fc6220003fd3110001fe1888015ffc84400affc4220057fd211002bfe1088017bf980400b7fea02005bfe501002dfea808016ff14040047fe8020023bf4010011ff2008008fe90040047fa8020003bd4010011fca008015ffc80400affc4020057fd201002bfe1008007ffd973003dfecb9801ffe65cc0057f32e6007ff597300a5facb9801ffc65cc00f7e32e6007ffd933003dfec99801ffe64cc0117f3266007ff59330005fac99801ffc64cc00f7e3266014ffd53300a7fca998053fd54cc029fe2a66007ffd4f3003ffca79801ffd53cc00ffe29e6007ffd0f3003ffc879801ffd43cc00ffe21e6007ffd8b3003dfec59801ffe62cc0037f3166007ff58b3009dfac59801ffc62cc0037e3166013ffd4b3009efea59804ffe52cc027fea966013df54b3009ff8a59804fff42cc027dfa166013ff90b3009ffa859804fbd42cc027fe2166007ffccb3003fbe659801ffe32cc00ffe9966013f74cb3003ff8659801fff61cc00fff30e6000bf9873003ffac398002fd61cc00ffe30e6014ffd47300a7fca398053fd51cc029fe28e6000ffd0730007fc8398003fd41cc001fe20e6007ffcc73003ffc639801ffd31cc00ffe18e6013ffc873009ffc439804ffd21cc027fe10e6014ffd43300a7fca198053fd50cc029fe2866000ffd0330007fc8198003fd40cc001fe2066013ffc833009ffc419804ffd20cc027fe1066012ffd9630095fecb1804bfe658c0057f32c6012ff59630095facb1804bfc658c0057e32c6000ffd9230005fec918003fe648c0117f3246000ff59230005fac918003fc648c0117e3246012ffd5230097fca91804bfd548c025fe2a46010bf58e30097fea71801ffe538c025fea9c6007ff14e30007fe871801ffe438c001fea1c6007ff10e3007ffec51803eff628c01fff3146001bf98a3007ffac51803efd628c01ffe3146001bf18a3007ffea51803f7f528c01fff294600fff54a3007efaa51803ffc528c01fffa14600fefd0a3007ffc851803ffd428c01fdea14600fff10a3003ffe651803fdf328c01fff194600fff4ca3007fba651801ffc328c001ffb0c6000ff986
  | 4 => 0x23fd41d0011fe20e8000ffcc740007fc63a0003fd31d0001fe18e801bffc87400dffc43a006ffd21d0037fe10e801cffd43400e7fca1a0073fd50d0039fe286801bffc83400dffc41a006ffd20d0037fe106801affd96400d5fecb2006bfe65900057f32c801adf99640014fccb2006bfd65900357eb2c8000df59640004facb2006bfc65900057e32c8018bf592400d7fea920023fe5490035df2a4801aff552400d77aa920023fc5490001ffb1c8000ff98e4003dfcc720003fd63900017eb1c8000ff18e400d7fea72006bfe5390035fea9c801aff14e40047fe8720003fe4390001df21c8000ff50e40047f88720003bc439002fffb148017bfd8a400bffcc520006fe629002ffeb148017bf58a400bff8c520006fc629002fffa948017dfd4a400bffca52005ffd529002fbea948017ff14a40047fe852005fbf429002fff2148017ff50a400bf7a8520023fc429002fff9948017f7cca400bffc652005ffd329002fee9948017ff0ca40007fec320003fe61900017f30c8000ff58640005fac320003fc6190035ffa8c801aff946400d7faa32006bfc5190011ffa0c8000ff906400077c8320003fd4190011fe20c8000ef10640007fe6320003fe3190001fe98c8000ff0c6400bffe432005ffe219002ffe90c8017ff08640045fcc12006bff5090035ff284801aff542400d7f8a120023ff4090001dfa048008fed02400bffe412005ffe209002ffe9048017ff082400cffecaa0066ff6550033ff32a8002bf995400cffacaa0066fd6550033fe32a8002bf195400cffea8a0023fe5450033feaa28008ff15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a001efc6350033ffa9a8019ff94d400cffaa6a0067fc5350011ffa1a8000ff90d40007fa86a0023fc4350031ffb128018bfd89400c7fcc4a0006fe6250031feb128018bf589400c7f8c4a0006fc6250031ffa928018dfd49400c7fca4a0063fd5250031bea928018ff14940047fe84a0063bf4250031ff2128018ff509400c77a84a0023fc4250031ff9928018f7cc9400c7fc64a0063fd3250031ee9928018ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150033ffa8a8019ff945400cffaa2a0067fc5150011ffa0a8000ff90540007fa82a0023fc4150001ff98a8000ff8c540007fa62a0003fc3150031ff90a8018ff885400c7fa42a0063fc2150033ffa828019ff941400cffaa0a0067fc5050011ffa028008fed0140007fc80a0003be4050031ff9028018ff881400c7fa40a0063fc2050011ffb288008bfd9440047fcca2000afe6510011feb288016bf59440047f8ca20022fc65100117f3208008ffd5040047fca820023be5410011feaa08016ef55040047f8a820023ff6310011ff3188007bf98c40047fac620002fd6310011f
  | 5 => 0x4d31007fe869881ffe434c401fea1a6207ff10d31107fec498882ff624c441ff3126201bf98931107fac498882fd624c441fe3126201bf18931107fea4988837f524c441ff2926220ff54931106faa498883fc524c441ffa126220efd0931107fc8498883fd424c441dea126220ff1093103ffe6498883df324c441ff1926220ff4c931107ba649881ffc324c443ffa8a6221ff9453110ffaa298887fc514c401ffa0a6200ff90531007fa8298803fc414c40fff98a6207fdcc531007fc6298803de314c441ff90a6220ff88531107fa4298883fc214c401ffb026200bfd8131007fcc098803fd604c401fe3026200bf1813110ffea098887fe504c443fea826221ff14131107fe4098883fe204c441fe9026220ff0813103ffeca1881eff650c40fff3286202bf9943103ffaca1887afd650c40ffe3286207bf1943103ffec81881eff640c40fff3206208bf9903103ffac818802fd640c40ffe3206207bf190310f7fea81887bfe540c43dfeaa0621eff1503103dfcc61881fff530c40fff2986207f794c3103ffaa61887bdd530c40ffe2986207ffd0c31007be861881ffe430c40ffea186207ff10c3103fb8861881fff620c40f7fb106207ff9883100dfcc41881ffd620c43b7eb106207ff1883100df8c418877ff520c43bbfa90621dff948310effaa4188777d520c43bfe290621dffd08310ef7e8418877fe420c43bfea10621def508310eff8841881fff320c40fef9906207ff8c83103ffa6418877dd320c40ffe190621fbf984310f7fea21887bfe510c43dfea88621eff14431007fe8218803fe410c401fea086200ff1043103ffe621881fdf310c40fff1886207fd8c43103ffa6218803dd310c40ffa988621dffc84310effc4218877fd210c43bfe1086207ffd803103ffcc018802fe600c40ffeb006200bf5803103ff8c01887bff500c43dff280621eff540310f7f8a018877ff200c43bff100621dff480310eff84018823ff65d00117fb2e8008ff99740015fccba00237e65d00053f32e8008ff597400e5facba00237d65d00013eb2e8008ff19740045f8cba0023ff54d0011ff2a68008ff55340047f8a9a0023ff63d0011ff31e8007bf98f40047fac7a0002fd63d0011fe31e801cffd4f400e7fca7a0073fd53d0039fe29e8008ffd0f40047fc87a0023fd43d0011fe21e8008ffd8b40045fec5a0023fe62d00037f3168008ff58b400ddfac5a0023fc62d00037e316801bffd4b400defea5a006ffe52d0037fea96801bdf54b400dff8a5a0023ff42d0011dfa168008ff90b40047fa85a006fbd42d0011fe216801bffccb400dfbe65a006ffe32d0037fe996801bf74cb400dff865a0023ff61d0011ff30e8000bf98740047fac3a0002fd61d0011fe30e801cffd47400e7fca3a0073fd51d0039fe28e8008ffd0740047fc83a0
  | 6 => 0x1fea088200ef50441047ea8220897ff211044bff1088225ff4844112ff84220823ff6010411ff3008200bf98041047fac020802fd6010411fe3008226ffd4041137fca02089bfd501044dfe2808225ffc804112ffc4020897fd201044bfe1008207ffd973103dfecb9881ffe65cc4057f32e6207df99731014fccb9881ffd65cc4497eb2e6207df59731004facb9881ffc65cc40f7e32e6207ffd933103dfec99881ffe64cc4117f3266207ff59331005fac99881ffc64cc40f7e3266224ffd5331127fca998893fd54cc449fe2a66207ffd4f3103ffca79881ffd53cc40ffe29e6207ffd0f3103ffc879881ffd43cc40ffe21e6207ffd8b3103dfec59881ffe62cc4037f3166207ff58b3111dfac59881ffc62cc4037e3166223ffd4b3111efea59888ffe52cc447fea966223df54b3111ff8a59888fff42cc447dfa166223ff90b3111ffa859888fbd42cc447fe2166207ffccb3103fbe659881ffe32cc40ffe9966223f74cb3103ff86598893ff51cc449ff28e6224ff54731127f8a398803ff41cc401ff20e6200ff50731007f8839888fff21cc447ff10e6223ff4873111ff8439881fff60cc40fff3066200bf9833103ffac198802fd60cc40ffe3066224ffd4331127fca198893fd50cc449fe2866223ffc833111ffc419888ffd20cc447fe1066222ffd9631115fecb1888bfe658c4057f32c6222df99631014fccb1888bfd658c4457eb2c6200df59631004facb1888bfc658c4057e32c6200ffd9231005fec918803fe648c4117f3246200ff59231005fac918803fc648c4117e3246222ffd5231117fca91888bfd548c445fe2a46220bf58e31117fea71881ffe538c445ef29c6222ff54e31117baa71881ffc538c401ffa1c6200f7d0e3103ffc8718803fd438c40ffe21c6200f710e310fffec51887eff628c43fff3146201bf98a310fffac51887efd628c43ffe3146201bf18a310fffea51887f7f528c43fff294621fff54a310fefaa51887ffc528c43fffa14621fefd0a310fffc851887ffd428c43fdea14621fff10a3103ffe651887fdf328c43fff194621fff4ca310ffba651881ffc328c40f7f30c6222ffd4631117fca31888bfd518c445fe28c6200ffd0631007fc8318803fd418c401fe20c6207ffcc631007be631881ff7318c43fff90c621fff886310fffa431887ffc218c401ffb046200ff98231005fcc118803fd608c4017eb046200ff18231117fea11888bfe508c445fea846222ff142310fffe411887ffe208c43ffe904621fff0823110ffeca98886ff654c443ff32a6202bf9953110ffaca98886fd654c443fe32a6202bf19531007fec898802ff644c401ff3226208bf99131007fac898802fd644c401fe3226208bf1913110ffea898887fe544c443feaa26221ff1513110ffea69881ffe534c443fea9a6207ff1
  | 7 => 0x20823fe5490455feaa48208ff15241007fec720803fe639040f7f31c8200ff58e41005fac720803fc6390455ffa9c822aff94e41157faa7208abfc5390411ffa1c8200ff90e41007fa8720823fc439044fffb148227bfd8a4113ffcc520806fe629044ffeb148227bf58a4113ff8c520806fc629044fffa948227dfd4a4113ffca52089ffd529044fbea948227ff14a41047fe852089fbf429044fff2148227ff50a4113f7a8520823fc429044fff9948227f7cca4113ffc652089ffd329044fee9948227ff0ca41045fcc3208abff5190455ff28c822aff54641157f8a320823ff4190401dfa0c8208fdd064113ffe432089ffe219044ffe90c8227ff08641007fec120803fe60904017f3048200ff58241005fac120803fc6090455ffa84822aff94241157faa1208abfc509044fff9048227ff8824113ffa412089ffc2090453ffb2a8229bfd9541006fecaa08027f6550453ff32a8202bf9954114ffacaa08a6fd6550453fe32a8202bf1954114ef8caa080a7c6550453ffaa28208ff9514114ffaa8a0823fc5450401ffb1a8200bfd8d41007bec6a0802df6350401ff31a8200ff58d41007f8c6a081efc6350401ee31a8200b718d4114ffea6a08a7fe5350453fea9a8229ff14d41047fe86a0803fe4350401fea1a8208ff10d41147fec4a08a2ff6250451ff3128201bf98941147fac4a08a2fd6250451fe3128201bf18941147fea4a08a37f5250451ff2928228ff54941146faa4a08a3fc5250411ffa128228efd0941147fc84a08a3fd4250451dea128208ff10941147fe64a08a3df3250451ff1928228ff4c941147ba64a08a3fc3250453ffa8a8229ff9454114ffaa2a08a7fc5150411ffa0a8208fdd0541007fc82a0803be4150451ff90a8228ff88541147fa42a08a3fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028200bf1814114ffea0a08a7fe5050453fea828229ff14141147fe40a08a3fe2050451fe9028228ff08141047feca20822ff6510411ff3288202bf99441046fcca2080a7e6510411feb288226bf59441046faca208027d6510411fe3288208bf19441045fcc820823ff5410411ff2a08208ff55041047f8a820823ff6310411ff3188207bf98c41047fac620802fd6310411fe3188226ffd4c41137fca62089bfd531044dfe2988208ffd0c41047fc8620823fd4310411fe2188208ffd8841045fec420823fe62104037f3108208ff5884112dfac420823fc62104037e3108225ffd484112efea420897fe521044bfea908225df5484112ff8a420823ff4210411dfa108208ff90841047fa8420897bd4210411fe2108225ffcc84112fbe6420897fe321044bfe9908225f74c84112ff8642089efe611044dffa888226ff94441137faa22089bfc5110411ffa088208efd0441047fc8220823f6411041
  | 8 => 0xf5894317dfac4a18bffc6250c037e312862fffd494317efea4a18bffe5250c5ffea92862fdf5494317ff8a4a1823ff4250c5fdfa12862fff9094317ffa84a18bfbd4250c11fe2128607ffcc94317fbe64a18bffe3250c5ffe992862ff74c94303ff864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a8630ffd4543187fca2a18c3fd5150c61fe28a862fffc854317ffc42a18bffd2150c5ffe10a8600ffd8143005fec0a1803fe6050c01feb028600ff18143005f8c0a18c3ff5050c61ff2828630ff54143187f8a0a18bfff2050c5fff102862fff4814317ff840a181fff6510c0f7fb288607ff99443015fcca2181f7e6510c053f3288607ff59443175faca2181f7d6510c013eb288607ff1944303df8ca21822fe6410c11ffaa08608ff95043047faa821823fc5410c0f7f3188607ffd4c4303ffca62181ffd5310c0ffe2988607ffd0c4303f7e862181ffe4310c0fef2188607ff50c4303f7a8621823dd4310c01cea188607ffd884303dfec42181ffe6210c037f3108607fb9884300ddcc42181ffd6210c5b7eb108607fb58843005dac42181ffc6210c037e310862dffd484316efea4218b7fe5210c5bfea90862ddf5484316ff8a421823ff4210c11dfa108608ff90843047fa84218b7bd4210c11fe2108607ffcc84303fbe642181ffe3210c0ffe990862df74c84303ff8642181fff6110c0fff3088600bf9844303ffac221802fd6110c0ffe308862effd4443177fca2218bbfd5110c5dfe288862dffc844316ffc42218b7fd2110c5bfe1088607ffd804303ffcc021802fe6010c0ffeb008600bf5804303ff8c0218bbff5010c5dff280862eff54043177f8a0218b7ff2010c5bff100862dff4804316ff84021823ff65d04117fb2e8208ff99741015fccba0823fd65d04597eb2e8208ff19741045f8cba0823ff54d0411ff2a68208ff55341047f8a9a0823ff63d0411ff31e8207bf98f41047fac7a0802fd63d0411fe31e822cffd4f41167fca7a08b3fd53d0459fe29e8208ffd0f41047fc87a0823fd43d0411fe21e8208ffd8b41045fec5a0823fe62d04037f3168208ff58b4115dfac5a0823fc62d04037e316822bffd4b4115efea5a08affe52d0457fea96822bdf54b4115ff8a5a0823ff42d0411dfa168208ff90b41047fa85a08afbd42d0411fe216822bffccb4115fbe65a08affe32d0457fe996822bf74cb4115ff865a08b3ff51d0459ff28e822cff54741167f8a3a08afff21d0457ff10e822bff4874115ff843a0823ff60d0411ff3068200bf98341047fac1a0802fd60d0411fe306822cffd4341167fca1a08b3fd50d0459fe286822bffc834115ffc41a08affd20d0457fe106822affd9641155fecb208abfe65904057f32c822aff59641155facb208abfc65904057e32c8228bf59241157fea9
  | 9 => 0x1002c00800c00400003c01000003001800c05005800c00000805407801c07400000000801c01412401002000c00000400c03c00800004007800000c0a400c00c04800001000404803000803802000400c0c800000002804400000c01c00000000006800401001400001800800402801000800800000403c06c00404400001c00c0040000900000500ec00801400400800000809401004400802000c0080100300240280040340b000805400004401001c00000403001800000400000801c02804800005401c00400800401402001803400c00c01800800400000c00011ffb2e8608bfd9743047fccba180afe65d0c11feb2e8634bf59743047f8cba1822fc65d0c11ffaa68608ff95343047faa9a1823fc54d0c69ffa9e8607ff94f431a7faa7a181ffc53d0c11ffb168608bfd8b43047fcc5a1806fe62d0c11feb168633bf58b43047f8c5a1806fc62d0c67ffa968633dfd4b4319ffca5a18cffd52d0c67bea968633ff14b43047fe85a1823bf42d0c11ff2168608ff50b4319f7a85a1823fc42d0c0fff9968633f7ccb4319ffc65a18cffd32d0c67ee9968607ff0cb43047fec3a1823fe61d0c017f30e8608ff58743005fac3a1823fc61d0c69ffa8e8634ff947431a7faa3a18d3fc51d0c67ff90e8633ff8874319ffa43a18cffc21d0c11ffb068608ff98343005fcc1a1823fd60d0c017eb068608ff183431a7fea1a18d3fe50d0c69fea868634ff1434319ffe41a18cffe20d0c67fe9068633ff0834303ffecb2181eff6590c0fff32c8602bf9964303ffacb218cafd6590c0ffe32c8607bf1964317dfac9218cbff5490c11ff2a48632ff55243047f8a92181efe6390c0fffa9c8607ff94e4303ffaa72181ffc5390c0fffa1c8607efd0e43047be872181fff6290c0f7fb148607ff98a4300dfcc52181ffd6290c637eb148607ff18a4300df8c5218c7ff5290c63bfa948631ff94a4318ffaa5218c77d5290c63fe2948608ffd0a4318f7e85218c7fe4290c63fea148631ef50a43047f8852181fff3290c0fef9948607ff8ca4303ffa65218c7dd3290c0ffe1948607ffd864303ffcc321802fe6190c0ffeb0c8600bf5864303ff8c3218cbff5190c65ff28c8632ff54643197f8a3218c7ff2190c63ff10c8631ff4864318ff8432181fff6090c0fff3048600bf9824303ffac121802fd6090c0ffe3048632ffd4243197fca1218cbfd5090c65fe2848631ffc824318ffc41218c7fd2090c63fe1048630ffd9543185fecaa18037f6550c013fb2a8630ff99543015fccaa18c3fd6550c617eb2a8630ff19543015f8caa18c37c6550c053e32a8630ffd5143047fca8a18c3fd5450c11fe2a28630ffd4d4303ffca6a18c3fd5350c0ffe29a8608ffd0d43047be86a181ffe4350c0fdf21a862fffd894317dfec4a18bffe6250c037f312862ff
  | 10 => 0x59c5000000004a80007620302fd800014401641e0000cce0001db10807922fc32c9e780007e23118000e1e6de0000000b1c000000000000008307b81bc00000000000010940000da83f09b82f73ac1dfc00000030980007a6000324206854626a0830e8449866635102f80000003c3000000029e34983b06940000000a640b42d61f4165c3384390000700f5c063000015d07e5d63f31e08f1a0002c08cd0256612185801411001800003400c03405c02007c0441e802400001c00008c01402c00000010003c02000400c00000000401c00401c00000400800402400c00802006007401000006800402004404800000c06800000400412003004000000000002804403804c00801400c00001001405802400c00001415c00003000005c01000802401803019000801800805c05404801000c00002402400000007c09000000002c03404c01400801002400400001000000406800007000801801800000402000001003802400001c00000c00402800402004c00000001402400403004c00c07c05401000001000400003405003400003c04400c04006c02c0d001400c03800403400005000005402804009800000001c00c01c2c400001000402002001400c00000000803000001801c02c00005402c00000802003401c00800000c00800000400003005400001003800802405402000001405002012800400807404000402c01401804c01c02001400000c00403801800000000002004400001009400400000002000007400001000005404c01400401400402c10802c04400000001002c00000c00000405801000011c08001401422c01c00005800017801000400400c01800004402c2080100100100000040040d40201500140ac01808800c0080000180100000100a00080100180240440240000000100ec00806c00000c00809001800401800000008800400018c00403c04000000400c00400008803800001401000400003800802c0000180040440080d003c00001c00001000c00004804800417401802015400c11006009800000002800002001408802001400415c00402000001407c09004800000800000001000c04403402c01c06400c03c02001400000000000400c00002801c00405800000c00c00c00000800004003000800c0000080580180040080100d400006803402c04801002c07000001c02404c09c00000805403800c02000400000802000001c02400404003004402c02c03c0000140f800000403001c07001000400000c0000040000340340000000040000f002000007401c0000540140f803401c00401403409400c01001c0000000ac01400000c04800000400002c0200d01900041540dc00001804c07001000000400003006c01800000000000c0280a801c00c00800c00000400400007c02001400403400000400400c00
  | 11 => 0xfc0900000000fd83ef27d88b400000001f8c801c867c0ea1be87e63f120598b000021a3709318ade7372328000d460211f016b0d521452388b68000427430078488e72900012844824e535b175c4fc0001a78e04d8017d2b50cf42965e73cc8f506340000669a80c9231100012fc0003492571f5c0da0002c21b3c6c849d1579b2c83266910b11d47383cb0001acc00023a000000064a7aa2550ebc0004fd2b29f180005c015c00000006543cb087091461539d96646a600003b00008783ee00020080000000002050c1c3e315e0d8ccee3bc0199ab80006b400000008082711a717f4da2000407a0a0b9a624000138cf52513244155c0006702098d0c05c0000001ac427074012c903c30a5200260a2455a6440388000eea00409f00009c23f82800d0825249132b0578c7200000005f0d5a000000057002216000005c000061d0a380000000003760000000000000000102e00001f17fc00063b12b99687fc26725190542223ec00011e415400022f07cc24859f35f951839e00029d02d0b1a0002b48000000588000000000000024a8000fbe0003ae9a6400069100d0628000578043800013608926a1d203b608b41887400e01ee1f50e940004cb0000978da424e2aa8d68c8475300000000000002a21c74b2642a07a1a5c2943551be0000d826ee0ad8920724000232218400055a00015d8dec00009002bc2d2000000190024e3b902e8ec8d9c47c00000010400dd2e88b482f0000165091c9484050db85d09b05df0cf01502c62eb3dd0cbc1724be2349b90eec68400021248a823313990f4a64239193193c72808600f98bccfe04903a87c426200005180010125f1016855c6d67ce11f0b6108883b00012cca3409408e97cc98652d0d318c48682510bd0e1c5860c4047171cb5c7a82d900e8bb433a0000ea0e7809f384a138b304120001e5c4f80ad0001fc85c20001d3800040e76d114882c0000000a8800038466f3a495901741561e18f947ae0000001fa827e28739c0854cca00000012385245aa0001884e1a386358020867e6870bf897414a4433b79fc44ec4f930e034800081e17a9e683f84892a610e07aa46b33a1f2c00021300000003305733461f50bba37b3b21e80c6853003e0000cc47ff0000dc81020002011f088ac7a724c9f8c0b629c3d99bc80b86111731d7c98a0002711b8000000034d8d5000065c05415b00000000001b503cc21000015384800000c71cc0db60000b5096051a2e525a80a00004733df1154a0c3c636412e09280000000d84bca64a000156c9086520000a3002871e25a167825a22b00013ac7b60000c885dc1ce68f3b7100c0007c400021540000373f780000000003d286684b485033b0f742b04260001d3800069e0000fd081882f000000028c1e72c81dc000037e3209a604540100001aac1e41a831
  | 12 => 0x498d7c4586fe0001f0c9760002108a2cdda18d0a78a20ed85a4142a04c3922a1000217cd420003f39d34f6283342001286643760b788040fc31b2698c8909872c3901534b4e70b11b0bc000015541291441426c54068c501967462588ea90b641f3341be0dc670527b00a433200024b215cb0c0eb0001fe0a6c03216f9478bc66dd16a1cf808a000258000099a2271e08a5057607a38d1b2834050f34a1850c8c2f330202682447163fd93c0b0e6ba2458c08b7866c0cb0898cc855313a9ec01002fe1421dcd0ba0003fba0f86104233f68b9c21068226610dc5344093c80398b762b302195f032840100a8aa4c3204e0000b408d050e0679c7027438b1821914e060000000a94f586e20001f64fb8463147019009083701e0fe44be52b00020ac5ba19b20700008580c93579834f163502611a40f363733d10000eb83f70001f24f482ab1a0800000005937e04949e44bd3e000007222493b4a1186b211016b88f45042603751aa10ea13d07e8b700dc0c70c184dcde20fb07fa11cd984d71b68394f7200000007bd09a23818e800039c79d0708e6800000000009ec5622c60e08da80003a40001af000028041389900000c22cd80006120000df112842e0000600000f901c400007680000000c100000000000d38cd44d06732d180001647561b490c8dfe18c0b70f884dc7de1d7000050c1ab00018810b431f0001aeccdc4a60951524ffa4100000000fe06083ec1c306e277406880001d45250c314b869600007d1f5808421f36b83548de57f1571214c362f438c8fec73e1f431821b82e62120848bc490e3010b20c7065c11f00017a800000023a046016044f0a706f473c3190d517d8f1811423f1f941328083fb04085365db3c9819c1bc4e02311f340003fa00000000001d300002d4f060582db0aa085065f2849ff81b44db28294643c438525487789e85c62d2895829a7630e3827897859a10512b40003d0118823c01211a07c09b0d3868d1030000ac611c11b800000077c11218a4558000000094d0420792d40000a5200000014e4708757372932437600005e80003c80f10a49fd40001950d190580003b527703d831e0782b41a584b61b40ba804cfd000032e8000a662440f6178107a0a63f700010900001d821a0e888010b314101b072b31fa0310204f737996d4f7078137e98f0be07d00dc9a24a2401d2af1efcb7e16536c99b4db861a06ba150e983832909e540e8610013923c78067a3259738b947130640c4cf285a031b147401a55d0501b1c65469f0001ef43ca6b7286116063c7262dc93b0bf06272c01114d4c26b1268e081224b73f980b02148122d98c3837e2fb03320644605792ea8ae85e42c9185165086c04d15a948c72e0002a0068506a3e42ea174000050221111b10de1ac417000022e000433126c6662a20000088a
  | 13 => 0xd46780000000c8e43e0000c340003bd04913a88105cf29103cc0ee6181ec000040052a3128f148fe16235a94200002cd0e60000d2420d08b0f7cab000002312190a200000000009580003810e3c00079815a000072a1ff04b058400049336b03bce9682a0db000088c30500013ccb16142302843caa057b0189c40acc41e0f015c48ce2ed42b00781ea02027f00710c40512a5823419807339400205f047a00013740c04c11f686c80005a13a080600006e80000c4000071538095d4daa7673c409503b208c3fd1a541566b914b098400082d000000037000014f8bf40002813d59b7cabe00026a80000006c300016b4ea426517404d83d455615b84842e423c23e80000007e9000093c0965112df000051e83a1521a140a680e0980eb4da065b3da806caee16d29e84e44d21340710ee84de48127c0f3801642e3a8947cb5260c04e9a2849436f22d07e44f049c1d5a0c8a480000151a0c0005cc1a000e4aa215042c21b084a40740398dc7e46722a7886c00000001a9658fd6358438136424643539c8cf86781f737ba05804609820a1460bd23294219c5c00073500017145a6785020838c4a463200000009f461f3bb80005fe05f2d59b9cfc03173d783144c415900c8ef828858c09e05ece105f502800ec0f64df15321c80000002c921089b42742d8860000000038380005d46550f69c8400082615f80000000003bd00009da7fc1ba0000d7c80017709b45d27a100901b09de5fe06e0c84bc85372189a2002e0ae14895d0bd832c00014a01760004120ced0c66aa2730210af410e0001c7c6c0567000000068a3512a198d43260d300014d43b01262939b34f7843a248014883079f2f10f3000029016700006b818829c21780003060000000c021130af90ec0007b70b60648000000000040cd3a3fd0ee9b18f9e0000fd9cf45645ef3bc03b8efc0a90f8110833a00000005e4db06ac1da0b3ca58680000031860e3c71f391dc00034d0561550de05d93bd8d88c2c33932610b44125f72089d88ea01c82f7102805600005b82288e473f00000001da4cf04b810000036610280007a21b1000017807057d000174c66262a00006946987a600000003d600019b94fc7266eb24c000000e11b00000010e23c400002900008060000fa4dd200040e86bc5600e92148d9441e3ca1ef0ce022a51c09a8ad8f984401018b14c0473a2ca945c65a7842e21170ed44570fc11342b441d1701d3d0164762978b444328533f09f90bb87424209724e4e1053ada1ccb14830187927c352153352000c2d0272268877cf6c43343a18f480004f2869148e247d537a82fc45c706171065cfa45ba17d1b685c80653d69184ecc5913289c8896c56e1a91e3c86067d082072810a03d31696082ec8692ce00006ee22200013a09f80000000bbcbf448220d972c9242140
  | 14 => 0x150400010b3ad116c3963301659d78848055000083105827a0d68de8dcc35e14b9c1000000027a9f6c5880000000e3800000000000006ae5a60808000a7876b16f07f8de81d50c486b80004a000017a0f6800013b8000f640e83971e8c8f67c1000119800024b2b587342002c119b0b1d0d40001c600008382832ec0f5800072d0b891388983b822087148a01840650000000000000001838c4e41f5a19cb0a4d60a0a13c64e0012de92bc0884a81c49ccc62a3a33989d64ff20b81b4125c95663a1c41bbc62457020b8c8c4a07c711187a502a4c000110fc2a8221395098cac05101070e0018670e42e000019c59d04e1f74b603d940188945c60c111d82ccf1c2701d10bd874c829000145057a4800001a1833e44b00004490300000e88df4e361870001d50b826a70000434fb402f1b381888883ff2738ae40000001e10a286067d324d0a74a026333a184c89bc04722f8db8e465eb2a114eca4c07f2a504bcf9446a23716dc3b860a12a942cb7067133080d001e2aa2539da08f00f032815c88a650a0121df46d80b13a2837c97241a070075c16c2112640f98ef25f92a3a1900d22202c79878eaa23435e800023c4a20001d84c9c4c43c48f8428000033c86cc52a4b230b8350892243422836d0444704291824ac400e0d208fc1f24d03dd86405d8545425a0d8e141812f6920c89035634599f8450653133202879e30c41a21649a41b009d97f0a2c3da0a19294c1e1bc26519eccc056141c1b085f26b831c0f20a367321229be47a41fd2e419d4a7c24602b1ac8cd43750050fc043c8050538340e5e6811b80f70f382d901b0c0052635b38c0364ba421d40d8ff031649e16613fc72064333187588b21332e191746880263131dc468c29810c1e1cc9a39b3e897c8b443bf0fd1018c4427d1bc9c440d678a09407d87660fe3058b542187912c49bec5843991ce84b885638a0000a9c4642c82d78000cbc70019400006485f428180000002db01280002906d300000003ea2081fb09e49d21194368000fe81f20341180c5060710200003860000000a806f01a200000000000000001a6800065705e11b44fe22f2da078c00025c000000000000039b05f87ea603000054800086b35292e879a1ba00018004041e839a018465672411a8c600006c91cc0dfc0e400040e001498e35d3470e340000003a520e50ca7653030c580008230000574d881670000eb00000d62a900000000001d009086902c01dd80007527473b001f400063e317207c99c14c402003076e5342f09dc80005833c013c400048c0961960000000000041cf245593e28000a9000015f170891a5310000d1c2d666b2839570bbc40d0001798a2a56d0001c940000000440e590220000e910bc
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x171840101eefa6184010007f26184010004ff76440100057f75440100257c75440100567e65440100067d6544010005bf7444010005bc7444010005df7344010005dc7344010005ef724401001dec7244010005f77644010006f77644010004f776440100077775440101bf7475440101bf766544010007756544010007b77444010007b47444010007d77344010007d47344010007e772440101afe472440101aef762440101aef562440101af7752440101af7552440101afb742440101afb542440101afd732440101afd532440101e5f770440101def660440101bff350440101bff250440101bff150440101bff05044010007f34044010007f24044010007f14044010007f04044010007f33044010007f23044010007f13044010007f030440101aff320440101aff220440101aff120440101aff02044010005fb7644010006fb7644010004fb76440100077b75440101bf7875440101bf7a6544010007796544010007bb7444010007b87444010007db7344010007d87344010007eb72440101afe872440101aefb62440101aef962440101af7b52440101af7952440101afbb42440101afb942440101afdb32440101afd932440101d5fb7144010007f371440101cefa6144010007f261440101bff351440101bff251440101bff151440101bff05144010007f34144010007f24144010007f14144010007f04144010007f33144010007f23144010007f13144010007f031440101aff321440101aff221440101aff121440101aff02144010007f37644010005f37644010006f376440101c7f375440100077375440101bff275440101c7f175440101bff075440101bf7075440101bff365440101bff265440101bf7265440101bff165440100077165440101bff06544010007f37444010007b37444010007f27444010007f17444010007f07444010007b07444010007f36444010007f26444010007f16444010007f064440101bff354440101bff254440101bff154440101bff05444010007f37344010007d37344010007f27344010007f17344010007f07344010007d07344010007f36344010007f26344010007f16344010007f063440101bff353440101bff253440101bff153440101bff05344010007f34344010007f24344010007f14344010007f043440101b7f37244010007e372440101aff272440101b7f172440101aff072440101afe072440101aff362440101aef362440101aff262440101aff162440101aef162440101aff062440101aff352440101af7352440101aff252440101aff152440101af7152440101aff052440101aff342440101afb342440101aff242440101aff142440101afb142440101aff042440101aff332440101afd332440101aff232440101aff132440101afd132440101aff03244010
  | 1 => 0xc101967e6590c100067d6590c1003ede6390c10006dd6390c10004ff7650c10004fe7650c10004fd7650c10004fc7650c100057f7550c100257c7550c101867e6550c100067d6550c10046be6450c10006bd6450c1003ede6350c10006dd6350c1003cff7610c10004fe7610c10004fd7610c1003cfc7610c100257e7510c100057d7510c101767e6510c100067d6510c100079d4310c1001dee7210c10005ed7210c10004fd76d04101667e65d04100067d65d0410004ff7690410044fd76904101567e65904100067d6590410046be6490410006bd6490410005fa7090410005f97090410004ff76504100057f75504100257c755041014e7e65504100067d6550410005df7350410005dc7350410044ff7610410004fd76104100257e75104100057d75104101367e65104100067d6510410046be6410410006bd6410410005fa7010410005f97010410004fd76cc4100257e75cc4100057d75cc4101267e65cc4100067d65cc410004ff768c41003cfd768c4100257e758c4100057d758c4101167e658c4100067d658c41003ede638c410006dd638c410005fa708c410005f9708c410004ff764c41010e7e654c4100067d654c41003cff760c410004fd760c4100f67e650c4100067d650c41003ede630c410006dd630c410005fa700c410005f9700c410004fd76d00100257e75d00100057d75d00100e67e65d00100067d65d0010004ff7690010044fd76900100257e75900100057d75900100d67e65900100067d6590010046be6490010006bd6490010005f67190010005f57190010004ff76500100ce7e65500100067d6550010044ff7610010004fe7610010004fd7610010044fc76100100b67e65100100067d6510010046be6410010006bd6410010005f67110010005f57110010004fd76cc0100a67e65cc0100067d65cc010004ff768c01003cfd768c0100967e658c0100067d658c01003ede638c010006dd638c010005f6718c010005f5718c010004ff764c0100057f754c0100257c754c01008e7e654c0100067d654c010005bf744c010005bc744c01003cff760c010004fe760c010004fd760c01003cfc760c0100257e750c0100057d750c0100767e650c0100067d650c01003ede630c010006dd630c010005f6710c010005f5710c0100667e65c40100067d65c4010036f576c401020f7665c40100077565c4010206f762c4010206f562c40102077752c40102077552c4010207b742c4010207b542c4010207d732c4010207d532c401005e7e65840100067d65840101b5f571840101eef6618401001df9768401002ef9768401000cf976840101ff7a65840100077965840101f6fb62840101f6f962840101f77b52840101f77952840101f7bb42840101f7b942840101f7db32840101f7d932840101b5f971840101b5f
  | 2 => 0x67e42594100067d42594100063d42594100067c42594100067f32594100065f32594100067e32594100067d32594100065d32594100067c32594100267f71594100067e71594100267d71594100267c71594100067f21594100067e21594100067d21594100067c21594100267f70594100067e70594100267d70594100267c70594100067f20594100067e20594100067d20594100067c20594100267c10594100257e75d90100057d75d90100067e65d90100067d65d9010004ff75d9010014fe75d90100067e75d90100147e75d9010004fd75d90100067d75d90100047d75d9010014fc75d901003cfe73d9010004fd73d9010004ff72d901000cfe72d9010004fd72d901000cfc72d90100067f52d90100067d52d9010006bf42d9010006bd42d9010006df32d9010006dd32d9010004fe71d9010006f671d9010004fe70d9010006fa70d9010004fd76990100067e65990100067d6599010006bf6499010044ff76590100067e65590100067d6559010004ff7559010014fe7559010004fd7559010014fc7559010006bf7459010004ff735901003cfc7359010004ff725901000cfe7259010004fd725901000cfc72590100067f52590100067d5259010006bf4259010006bd4259010006df3259010006dd3259010044ff7159010044fd7159010044ff7059010044fd70590100257e75190100057d75190100067e65190100067d6519010046be6419010006bd6419010005de7319010005dd731901001dee7219010005ed72190100257e75d8c100057d75d8c100067e65d8c100067d65d8c10004ff75d8c10014fe75d8c100067e75d8c100147e75d8c10004fd75d8c100067d75d8c100047d75d8c10014fc75d8c10044fe74d8c10004fd74d8c10004ff72d8c1000cfe72d8c10004fd72d8c1000cfc72d8c100067f52d8c100067d52d8c10006bf42d8c10006bd42d8c10006df32d8c10006dd32d8c10004fe71d8c10006f671d8c10004fe70d8c10006fa70d8c10004fd7698c100067e6598c100067d6598c10006df6398c1003cff7658c100067e6558c100067d6558c10004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c10044fc7458c10006df7358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10006bf4258c10006bd4258c10006df3258c10006dd3258c1003cff7158c1003cfd7158c1003cff7058c1003cfd7058c100257e7518c100057d7518c100067e6518c100067d6518c10005be7418c10005bd7418c1003ede6318c10006dd6318c1001dee7218c10005ed7218c10044ff76d0c10004fe76d0c10004fd76d0c10044fc76d0c101a67e65d0c100067d65d0c10046be64d0c10006bd64d0c1003cff7690c10004fe7690c10004fd7690c1003cfc769
  | 3 => 0xc63d0110006ef62d01100deec62d0110005f671d0110005f571d0110004fe76901100557e75901100057d75901100067f65901100d67c6590110006bf6490110046bc6490110006df6390110006dc6390110006ef62901100beec6290110044ff7650110004fd7650110044fc76501100067f65501100ce7c6550110006bf6450110046bc6450110006df6350110006dc6350110006ef62501100c6ec6250110005f77150110005f47150110004fe76101100067f65101100b67c6510110006bf6410110046bc6410110006df6310110006dc6310110006ef62101100aeec6210110007b94010110004fe76cc1100067f65cc1100a67c65cc110006bf64cc110006bc64cc110006df63cc11003edc63cc110006ef62cc11009eec62cc110005f671cc110005f571cc110004fe768c1100067f658c1100967c658c110006bf648c110006bc648c110006df638c11003edc638c110006ef628c11007eec628c11003cff764c110004fd764c11003cfc764c1100057f754c1100557c754c1100067f654c11008e7c654c110005bf744c110005bc744c110006bf644c110006bc644c110006df634c11003edc634c110006ef624c110086ec624c110005f7714c110005f4714c110004fe760c1100557e750c1100057d750c1100067f650c1100767c650c110006bf640c110006bc640c110006df630c11003edc630c110006ef620c11006eec620c110007d9300c1100067f65c41100667c65c4110006bf64c4110006bc64c4110006df63c4110006dc63c4110006ef62c4110036ec62c41100077b65c411022f7865c4110007bb64c4110007b864c4110007db63c4110007d863c41101cdfb72c41101cdf972c4110007eb62c4110227e862c41102277b52c41102277952c4110227bb42c4110227b942c4110227db32c4110227d932c4110227f221c4110227f121c41100067f658411005e7c6584110006bf6484110006bc6484110006df6384110006dc6384110006ef628411002eec628411004df6768411000777658411021f746584110007b76484110007b46484110007d76384110007d463841101ddf772841101ddf57284110007e76284110217e46284110217775284110217755284110217b74284110217b54284110217d73284110217d53284110007f36084110217f22084110217f120841100257f76594100267f76594100147f76594100057f72594100057d72594100067f62594100067e62594100067d62594100067c62594100073f42594100073d42594100075f32594100075d32594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f72594100047f72594100067e72594100067d72594100047d72594100067c72594100067f42594100063f4259410
  | 4 => 0x8910007ac74d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910007cf73d8910007cc73d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e771d891004fe471d8910007eb70d891004fe870d8910006ef75d89100066f75d8910006ee75d8910006ed75d8910006ec75d89100066c75d8910006ef74d8910006af74d8910006ee74d8910006ed74d8910006ec74d8910006ac74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006cf73d8910006ee73d8910006ed73d8910006ec73d8910006cc73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891004eee71d891004eed71d891004eec71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef70d891004eee70d891004eed70d891004eec70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d891004eed10d8910004fe76d05100067f65d05101667c65d0510006bf64d0510046bc64d0510006df63d0510006dc63d0510006ef62d051015eec62d0510005fa70d0510005f970d0510004fe76905100067f65905101567c6590510006bf6490510046bc6490510006df6390510006dc6390510006ef629051013eec6290510044fc76505100057f75505100557c75505100067f655051014e7c6550510006bf6450510046bc6450510005df7350510005dc7350510006df6350510006dc6350510006ef6250510146ec6250510005fb7050510005f87050510004fe76105100557e75105100057d75105100067f65105101367c6510510006bf6410510046bc6410510006df6310510006dc6310510006ef621051012eec6210510007b54110510004fe76cc5100557e75cc5100057d75cc5100067f65cc5101267c65cc510006bf64cc510006bc64cc510006df63cc51003edc63cc510006ef62cc51011eec62cc510005fa70cc510005f970cc510004fe768c5100557e758c5100057d758c5100067f658c5101167c658c510006bf648c510006bc648c510006df638c51003edc638c510006ef628c5100feec628c51003cfc764c5100067f654c51010e7c654c510006bf644c510006bc644c510006df634c51003edc634c510006ef624c510106ec624c510005fb704c510005f8704c510004fe760c5100067f650c5100f67c650c510006bf640c510006bc640c510006df630c51003edc630c510006ef620c5100eeec620c510007d5310c510004fe76d01100557e75d01100057d75d01100067f65d01100e67c65d0110006bf64d0110046bc64d0110006df63d0110006d
  | 5 => 0x4ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1003ede6318d10006dd6318d10006ec6218d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10005df7218d10005dd7218d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d100075f5218d100075d5218d100079f4218d100079d4218d10007d62118d10007d52118d10007da2018d10007d92018d1003edf7518d1003ede7518d1003edd7518d1003edc7518d1003edf7418d1003ede7418d1003edd7418d1003edc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d1003edf7218d1003cdf7218d1003ede7218d1003edd7218d10004dd7218d1003edc7218d10006df5218d100065f5218d10006de5218d10006dd5218d100065d5218d10006dc5218d10006df4218d100069f4218d10006de4218d10006dd4218d100069d4218d10006dc4218d1003edf7118d1003edd7118d10006df5118d10006de5118d10006dd5118d10006dc5118d10006df2118d10006de2118d10006dd2118d10006dc2118d1003edf7018d1003edd7018d10006df5018d10006de5018d10006dd5018d10006dc5018d10006df2018d10006de2018d10006dd2018d10006dc2018d10006dd1018d10044ff76d0d10004fe76d0d10004fd76d0d10044fc76d0d100067f65d0d101a67c65d0d10006bf64d0d10046bc64d0d10006df63d0d1003edc63d0d1019eec62d0d1003cff7690d10004fe7690d10004fd7690d1003cfc7690d100067f6590d101967c6590d10006bf6490d10046bc6490d10006df6390d1003edc6390d1018eec6290d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d100067f6550d101867c6550d10006bf6450d10046bc6450d10006df6350d1003edc6350d1017eec6250d10005f77150d10005f47150d10005fb7050d10005f87050d1003cff7610d10004fe7610d10004fd7610d1003cfc7610d100557e7510d100057d7510d100067f6510d101767c6510d10006bf6410d10046bc6410d10006df6310d1003edc6310d100079d4310d1004dee7210d10005ed7210d1016eec6210d10005f67110d10005f57110d10005fa7010d10005f97010d1004dee76d891004eee76d891000cee76d89100076f75d89100076c75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910007af74d
  | 6 => 0xe2019110006bd2019110006bc2019110006bd101911003cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10006ec62d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10044fe74d8d10004fd74d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10006bf42d8d10006bd42d8d10006df32d8d10006de32d8d10006dd32d8d10006dc32d8d1003cfe71d8d1003cfc71d8d1003cfe70d8d1003cfc70d8d1003cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10005df72d8d10005dd72d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100075f52d8d100075d52d8d100079f42d8d100079d42d8d10007d621d8d10007d521d8d10007da20d8d10007d920d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10004df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df52d8d100065f52d8d10006de52d8d10006dd52d8d100065d52d8d10006dc52d8d10006df42d8d100069f42d8d10006de42d8d10006dd42d8d100069d42d8d10006dc42d8d10006df71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d100557e7598d100057d7598d100067f6598d100067c6598d10005be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d1004dee7298d10005ed7298d10006ec6298d100057f7558d100557c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10006bc6458d10005ef7258d1004dec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d10044fc7458d10006bc7458d10044bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d5258d10006bf4258d10006bd4258d10006df3258d10006dd3258d10
  | 7 => 0x9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d91100069f32d9110006be32d9110006bd32d91100069d32d9110006bc32d9110006bf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf20d9110006be20d9110006bd20d9110006bc20d91100557e75991100057d75991100067f65991100067c6599110006bf6499110005de7399110005dd739911004dee7299110005ed7299110006ec62991100057f75591100557c75591100067f65591100067c6559110005df7359110005dc7359110005ef725911004dec7259110006ec6259110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110004ff7359110006df7359110004df735911003cfc7359110006dc735911003cdc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec72591100067f52591100067d5259110006bf4259110006bd4259110006df3259110006dd3259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c6519110046be6419110006bd6419110006ec6219110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110005bf7219110005bd7219110006bf6219110006be6219110006bd6219110006bc6219110007ac6219110006ac62191100073f52191100073d52191100079f32191100079d3219110007b62119110007b52119110007ba2019110007b92019110046bf7519110046be7519110046bd7519110046bc7519110046bf7319110046be7319110046bd7319110046bc7319110006bf5319110006be5319110006bd5319110006bc5319110046bf7219110044bf7219110046be7219110046bd7219110004bd7219110046bc7219110006bf52191100063f5219110006be5219110006bd52191100063d5219110006bc5219110006bf32191100069f3219110006be3219110006bd32191100069d3219110006bc3219110046bf7119110046bd7119110006bf5119110006be5119110006bd5119110006bc5119110006bf2119110006be2119110006bd2119110006bc2119110046bf7019110046bd7019110006bf5019110006be5019110006bd5019110006bc5019110006bf2019110006b
  | 8 => 0x5f57110210007b9401021003cfd768c21003ede638c210006dd638c210005f6718c210005f5718c2100057f754c21005d7c754c210005bf744c210005bc744c21005d7e750c2100057d750c21003ede630c210006dd630c210005f6710c210005f5710c210007d9300c210005f576c4210006f576c421023ef762c421023ef562c421023f7752c421023f7552c421023fb742c421023fb542c421023fd732c421023fd532c4210237f250c4210237f150c4210005f976c4210006f976c42101edfb72c42101edf972c421023f7b52c421023f7952c421023fbb42c421023fb942c421023fdb32c421023fd932c4210237f251c4210237f151c42100557e76d95100567e76d95100147e76d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100073f42d95100073d42d95100075f32d95100075d32d95100077621d95100077521d95100077a20d95100077920d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100065f32d95100067e32d95100067d32d95100065d32d95100067c32d95100067f71d95100567e71d95100567d71d95100567c71d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95100567e70d95100567d70d95100567c70d95100067f20d95100067e20d95100067d20d95100067c20d95100567d10d9510044fe76d91100067f65d91100067c65d9110006ec62d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d911003cfe73d9110004fd73d9110004ff72d911000cfe72d9110004fd72d911000cfc72d91100067f52d91100067d52d9110006bf42d9110006be42d9110006bd42d9110006bc42d9110006df32d9110006dd32d9110044fe71d9110044fc71d9110044fe70d9110044fc70d9110044be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d91100073f52d91100073d52d91100079f32d91100079d32d9110007b621d9110007b521d9110007ba20d9110007b920d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d
  | 9 => 0xe73d9210006de73d921003cde73d9210004fd73d9210006dd73d9210004dd73d9210004ff72d921000cfe72d9210004fd72d921000cfc72d92100067f52d92100067d52d9210006bf42d9210006bd42d9210006df32d9210006dd32d9210006f571d9210006fa70d9210004fd769921005d7e75992100057d7599210006bf6499210044ff7659210004ff7559210014fe7559210004fd7559210014fc7559210006bf7459210004ff735921003cfc7359210004ff725921000cfe7259210004fd725921000cfc72592100067f52592100067d5259210006bf4259210006bd4259210006df3259210006dd3259210046be6419210006bd6419210004ff75d8e10014fe75d8e10004fd75d8e10014fc75d8e10044fe74d8e10004fd74d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e100067f52d8e100067d52d8e10006bf42d8e10006bd42d8e10006df32d8e10006dd32d8e10006f571d8e10006fa70d8e10004fd7698e10006df6398e1003cff7658e100057f7558e1005d7c7558e10004ff7558e100067f7558e100047f7558e10014fe7558e10004fd7558e10014fc7558e100067c7558e100147c7558e10004ff7458e10044fc7458e10006df7358e10006de5358e10006dd5358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e100067f5258e100067d5258e10006bf4258e10006bd4258e10006df3258e10006dd3258e1005d7e7518e100057d7518e1003ede6318e10006dd6318e10044ff76d0e10004fe76d0e10004fd76d0e10044fc76d0e1003ede63d0e10006dd63d0e1003cff7690e10004fe7690e10004fd7690e1003cfc7690e10004ff7650e10004fe7650e10004fd7650e10004fc7650e100057f7550e1005d7c7550e10005fb7050e10005f87050e1003cff7610e10004fe7610e10004fd7610e1003cfc7610e1005d7e7510e100057d7510e1003ede6310e10006dd6310e100079d4310e1002dee7210e10005ed7210e10005fa7010e10005f97010e10046be64d0610006bd64d0610005fa70d0610005f970d0610006bf6490610046bc6490610044ff76506100057f755061005d7c7550610046be6450610006bd6450610005df7350610005dc7350610005fb7050610005f8705061005d7e75106100057d7510610006bf6410610046bc641061005d7e75cc6100057d75cc61003ede63cc610006dd63cc610005fa70cc610005f970cc61005d7e758c6100057d758c610006df638c61003edc638c61003cff764c61003ede634c610006dd634c610005fb704c610005f8704c610006df630c61003edc630c61005d7e75d02100057d75d0210044fd769021005d7e75902100057d7590210046be6490210006bd6490210005f67190210005f57190210046be6410210006bd6410210005f67110210
  | 10 => 0x9310006bd4259310006df3259310006dd32593100657e75193100057d7519310046be6419310006bd64193100657e75d8f100057d75d8f10005be74d8f10005bd74d8f10004ff75d8f10014fe75d8f100067e75d8f100147e75d8f10004fd75d8f100067d75d8f100047d75d8f10014fc75d8f10044fe74d8f10006be74d8f10044be74d8f10004fd74d8f10006bd74d8f10004bd74d8f10004ff72d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100067f52d8f100067d52d8f10006bf42d8f10006bd42d8f10006df32d8f10006dd32d8f10006f671d8f10006f970d8f10004fd7698f100657e7598f100057d7598f10006df6398f1003cff7658f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f10044fc7458f10006df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10006bf4258f10006bd4258f10006df3258f10006dd3258f1003ede6318f10006dd6318f10044ff76d0f10004fe76d0f10004fd76d0f10044fc76d0f1003cff7690f10004fe7690f10004fd7690f1003cfc7690f10046be6490f10006bd6490f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100057f7550f100657c7550f10005f77150f10005f47150f1003cff7610f10004fe7610f10004fd7610f1003cfc7610f100657e7510f100057d7510f10046be6410f10006bd6410f100079d4310f10035ee7210f10005ed7210f10005f67110f10005f57110f10044fd7690710046be6490710006bd6490710005fa7090710005f970907100057f75507100657c7550710005df7350710005dc73507100657e75107100057d7510710046be6410710006bd6410710007b54110710005fa7010710005f970107100657e75cc7100057d75cc71003cfd768c7100657e758c7100057d758c71003ede638c710006dd638c710005fa708c710005f9708c71003ede630c710006dd630c710007d5310c710005fa700c710005f9700c7100657e75d03100057d75d0310046be64d0310006bd64d0310005f671d0310005f571d03100657e75903100057d7590310006bf6490310046bc6490310044ff7650310046be6450310006bd6450310005f77150310005f47150310006bf6410310046bc641031003ede63cc310006dd63cc310005f671cc310005f571cc310006df638c31003edc638c31003cff764c3100057f754c3100657c754c310005bf744c310005bc744c31003ede634c310006dd634c310005f7714c310005f4714c3100657e750c3100057d750c310006df630c31003edc630c31005d7e75d92100057d75d9210005de73d9210005dd73d9210004ff75d9210014fe75d92100067e75d92100147e75d9210004fd75d92100067d75d92100047d75d9210014fc75d921003cf
  | 11 => 0x67f52584300067d5258430006bf4258430006bd425843003edf3258430006dd325843003ef7715843003ef7315843003edc315843003ef4315843003ed43158430006f62158430006f52158430044ff76d043003cfe76d0430004fd76d04301667e65d04300067d65d0430046be64d0430006bd64d043003dde73d0430005dd73d0430004ff769043003cfe7690430004fd76904301567e65904300067d6590430006f66190430006f56190430005fa7090430005f97090430004ff7650430004fd765043003cfc76504300057f75504300757c755043014e7e65504300067d6550430046be6450430006bd6450430005df735043003ddc7350430006f66150430006f56150430044ff761043003cfe7610430004fd76104300757e75104300057d75104301367e65104300067d651043003ddd768c430006dd768c4302875e758c4300075d758c43003edf658c43003f5e658c430286dd658c43003f5d658c4300065d658c43027ede648c43003edc648c430275df728c430275dd728c43003edf628c43026edd628c43026f5f528c43026f5d528c43026f9f428c43026f9d428c43003dde718c43003fd6718c430006dd618c430005dd708c430266de608c43003fda608c430004fd76d00300757e75d00300057d75d00300e67e65d00300067d65d0030004ff7690030044fd76900300757e75900300057d75900300d67e65900300067d6590030046be6490030006bd649003003dde7390030005dd7390030004ff76500300ce7e65500300067d6550030044ff761003003cfe7610030004fd761003003cfc76100300b67e65100300067d6510030046be6410030006bd641003003dde7310030005dd731003003ddf764c030006df764c030004df764c0300075f754c03025f5c754c03003f5e654c03003f5d654c0300079f744c0300079c744c030255df724c030255dd724c03003edf624c030246dd624c0302475f524c0302475d524c0302479f424c0302479d424c030005dc714c03003ddf704c03003fdb704c03024ede604c03003fda604c030247db204c030247d8204c030004ff75d9310014fe75d9310004fd75d9310014fc75d931003cfe73d9310004fd73d9310004ff72d931000cfe72d9310004fd72d931000cfc72d93100067f52d93100067d52d9310006bf42d9310006bd42d9310006df32d9310006dd32d9310006f671d9310006f970d9310004fd7699310006bf6499310044ff76593100057f75593100657c7559310004ff75593100067f75593100047f7559310014fe7559310004fd7559310014fc75593100067c75593100147c7559310006bf7459310006be5459310006bd5459310004ff735931003cfc7359310004ff725931000cfe7259310004fd725931000cfc72593100067f52593100067d5259310006bf425
  | 12 => 0xc654c530006bf644c530006bc644c530006f7614c530006f4614c53003fd4314c530005fb704c530005f8704c53003fd8304c53003cfe76d013003cfc76d013008d7e75d01300057d75d01300067f65d01300e67c65d0130006bf64d0130046bc64d013003dde73d0130005dd73d0130004fe769013008d7e75901300057d75901300067f65901300d67c6590130006bf6490130046bc6490130044ff7650130004fd765013003cfc76501300067f65501300ce7c6550130006bf6450130046bc6450130005df735013003ddc7350130004fe76101300067f65101300b67c6510130006bf6410130046bc64101300067f658c1300967c658c130006bf648c130006bc648c13003dfa708c13003efb608c1300075f658c1302975c658c1300079f648c1300079c648c13024ddf728c13024ddd728c13028edf628c13028edd628c13028f5f528c13028f5d528c13028f9f428c13028f9d428c130006dc618c13003dde708c13003edf608c13003fdb608c1300067f74594300067e74594300067d74594300067c745943003e7f735943003e7e735943003e7d735943003e7c735943003e7f435943003e7e435943003e7d435943003e7c43594300067f72594300047f72594300067e72594300067d72594300047d72594300067c72594300067f42594300063f42594300067e42594300067d42594300063d42594300067c425943003e7f325943003e5f325943003e7e325943003e7d32594300065d325943003e7c32594300067f71594300067e71594300067d71594300067c715943003e7f315943003e7e315943003e7d315943003e7c315943003e5c31594300067f21594300067e21594300067d21594300067c21594300767f70594300067e70594300767d70594300767c705943003e7f305943003e7e305943003e7d305943003e7c30594300067f20594300067e20594300067d20594300067c2059430004ff7559030014fe7559030004fd7559030014fc755903003ebf745903003cff735903003cfe735903003cfd735903003cfc735903003ebe435903003ebc4359030004ff725903000cfe7259030004fd725903000cfc72590300067f52590300067d5259030006bf4259030006bd425903003edf3259030006dd3259030004ff7159030004fc7159030004ff7598430014fe7598430004fd7598430014fc7598430044fe7498430004fd7498430004ff729843000cfe7298430004fd729843000cfc72984300067f52984300067d5298430006bf4298430006bd429843003edf3298430006dd329843003ef6719843003ef7319843003ef43198430006f62198430006f52198430004ff7558430014fe7558430004fd7558430014fc7558430004ff7458430044fc7458430004ff725843000cfe7258430004fd725843000cfc7258430
  | 13 => 0x9130046bc7219130006bf52191300063f5219130006be5219130006bd52191300063d5219130006bc521913029ebf32191300069f3219130006be3219130006bd32191300069d321913029ebc3219130046bf7119130046be7119130046bd7119130046bc7119130006bf5119130006be5119130006bd5119130006bc511913029ebf311913029ebc3119130006bf2119130006be2119130006bd2119130006bc2119130046bf7019130046bd7019130006bf5019130006be5019130006bd5019130006bc501913029ebf3019130006bd301913029ebc3019130006bf2019130006be2019130006bd2019130006bc2019130004fe76d0d300067f65d0d301a67c65d0d30006bf64d0d30046bc64d0d30005fa70d0d30005f970d0d30044fc7650d300057f7550d3008d7c7550d300067f6550d301867c6550d30006bf6450d30046bc6450d3003f9c4350d30005fb7050d30005f87050d300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d8530014fe75d8530004fd75d8530014fc75d8530044fe74d8530004fd74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006bf42d8530006bd42d8530006df32d8530006dd32d8530006f721d8530006f421d853008d7e75985300057d75985300067f65985300067c6598530005be7498530005bd7498530006bf6498530006bc6498530006f761985300057f755853008d7c75585300067f65585300067c6558530005bf7458530005bc7458530006bf6458530006bc6458530005ef7258530085ec72585300067f65185300067c6518530006bf6418530006bc6418530006f56118530004ff7518530014fe7518530004fd7518530014fc7518530044fe7418530004fd7418530004ff721853000cfe7218530004fd721853000cfc72185300067f52185300067d5218530006bf4218530006bd4218530006df3218530006dd3218530006f72118530006f42118530004fe76d0530004fd76d0530044fc76d05300067f65d05301667c65d0530006bf64d0530046bc64d0530004fe7690530004fd7690530004fc76905300067f65905301567c6590530006bf6490530046bc6490530004ff7650530004fe7650530004fc76505300057f755053008d7c75505300067f655053014e7c6550530006bf6450530046bc6450530005df735053003ddc7350530004fe7610530004fd7610530044fc761053008d7e75105300057d75105300067f65105301367c6510530006bf6410530046bc641053003dde7310530005dd7310530005fa7010530005f9701053008d7e758c5300057d758c5300067f658c5301167c658c530006bf648c530006bc648c530006f7618c530006f4618c530005fa708c530005f9708c5300067f654c53010e7
  | 14 => 0x3cfc73d9130004ff72d913000cfe72d9130004fd72d913000cfc72d91300067f52d91300067d52d9130006bf42d9130006be42d9130006bd42d9130006bc42d9130006df32d9130006dd32d9130004fe71d9130004fd71d9130044be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130005bf72d9130005bd72d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300073f52d91300073d52d91300079f32d91300079d32d91302a7bb30d91302a7b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d91302a6be73d9130006bd73d91302a6bc73d9130006bf53d91302a6be53d9130006bd53d91302a6bc53d9130006bf72d9130004bf72d9130006be72d9130006bd72d9130004bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d91300063d52d9130006bc52d91302a6bf32d91300069f32d9130006be32d9130006bd32d91300069d32d91302a6bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d91302a6bf31d91302a6bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d91302a6bf70d9130006bd70d9130006bf50d9130006be50d9130006bd50d9130006bc50d91302a6bf30d91302a6bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d913008d7e75991300057d75991300067f65991300067c6599130006bf64991300057f755913008d7c75591300067f65591300067c6559130004ff75591300067f75591300047f7559130014fe7559130004fd7559130014fc75591300067c75591300147c7559130006bf7459130004ff7359130006df7359130004ff725913000cfe7259130004fd725913000cfc72591300067f52591300067d5259130006bf4259130006bd4259130006df3259130006dd3259130004ff7159130004fc7159130004ff7059130006fb7059130004fe76191300067f65191300067c6519130046be6419130006bd6419130005be7619130006be7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130005bf7219130005bd7219130006bf6219130006be6219130006bd6219130006bc62191300073f52191300073d52191300079f32191300079d321913029fbb301913029fb83019130046bf7519130046be7519130046bd7519130046bc7519130046bf7319130046be7319130046bd7319130046bc7319130006bf531913029ebe5319130006bd531913029ebc5319130046bf7219130044bf7219130046be7219130046bd7219130004bd721
  | 15 => 0xd7690630004ff7650630004fd7650630004fc76506300057f75506300957c7550630005df735063003ddc7350630044ff7610630004fe7610630004fd76106300957e75106300057d7510630006f66110630006f56110630005fa7010630005f970106300957e758c6300057d758c630006f6618c630006f5618c630005fa708c630005f9708c6302f75e758c6300075d758c6302f6df658c6302f6dd658c63027ede648c63027edc648c6302eddf728c6302eddd728c630266df628c630266dd628c6302675f528c6302675d528c6302679f428c6302679d428c63003dde718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c63003ede608c630006f6614c630006f5614c630005fb704c630005f8704c630005dd760c63003edd760c6302e6df650c6302e6dd650c6302dede640c6302dedc640c63003ddf720c6302d5dd720c6302cedf620c6302cedd620c6302cf5f520c6302cf5d520c6302cf9f420c6302cf9d420c63003fd6710c630006dd610c630005dd700c63003fda600c6300957e75d02300057d75d023003cfd76902300957e75902300057d7590230046be6490230006bd649023003dde7390230005dd739023003cfd7610230046be6410230006bd641023003dde7310230005dd7310230005dd76cc23003edd76cc23003ddf72cc2302c5dd72cc2302bedf62cc2302bedd62cc2302bf5f52cc2302bf5d52cc2302bf9f42cc2302bf9d42cc230005de71cc23003fda60cc2302b7da50cc2302b7d950cc23008d7e76d953008e7e76d95300147e76d95300057f72d95300057d72d95300067f62d95300067e62d95300067d62d95300067c62d95300073f42d95300073d42d95300075f32d95300075d32d95302af7b30d95302af7830d95300067f74d95300067e74d95300067d74d95300067c74d95300067f73d95302ae7e73d953008e7d73d95302ae7c73d95302ae7e43d95302ae7c43d95300067f72d95300047f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300063f42d95300067e42d95300067d42d95300063d42d95300067c42d95302ae7f32d95300065f32d95300067e32d95300067d32d95300065d32d95302ae7c32d95300067f71d95300067e71d95300067d71d95300067c71d95302ae7f31d95302ae7c31d95300067f21d95300067e21d95300067d21d95300067c21d95302ae7f70d953008e7e70d953008e7d70d953008e7c70d95302ae7f30d953008e7d30d95302ae7c30d95300067f20d95300067e20d95300067d20d95300067c20d9530044fe76d91300067f65d91300067c65d9130004ff75d9130014fe75d9130004fd75d9130014fc75d9130006bf54d9130006be54d9130006bd54d9130006bc54d913003cfe73d9130
  | 16 => 0x8730044ff76d073003cfe76d0730004fd76d0730004ff769073003cfe7690730004fd7690730046be6490730006bd6490730005fa7090730005f97090730004ff7650730004fd765073003cfc76507300057f75507300a57c7550730005df735073003ddc7350730044ff761073003cfe7610730004fd76107300a57e75107300057d7510730046be6410730006bd641073003dde7310730005dd73107300a57e75d03300057d75d0330046be64d0330006bd64d033003dde73d0330005dd73d03300a57e75903300057d75903302a6bf6490330046bc6490330044ff7650330046be6450330006bd6450330005df735033003ddc735033029ebf6410330046bc64103300957e75d92300057d75d9230005f671d9230005f571d9230004ff75d9230014fe75d92300067e75d92300147e75d9230004fd75d92300067d75d92300047d75d9230014fc75d9230006dd73d92302a6be43d92302a6bc43d9230004ff72d923000cfe72d9230004fd72d923000cfc72d92300067f52d92300067d52d9230006bf42d9230006bd42d9230006df32d9230006dd32d9230004fe71d9230006f671d9230004f671d9230004fd71d9230006f571d9230004f571d9230006fa70d9230004fd76992300957e75992300057d7599230006bf6499230044ff7659230004ff7559230014fe7559230004fd7559230014fc7559230006bf7459230004ff725923000cfe7259230004fd725923000cfc72592300067f52592300067d5259230006bf4259230006bd4259230006df3259230006dd3259230004ff7159230004fc7159230046be6419230006bd6419230046be64d0e30006bd64d0e30005fa70d0e30005f970d0e30044ff7650e300057f7550e300957c7550e30046be6450e30006bd6450e3003f9c4350e30005fb7050e30005f87050e30006f76198630004ff7598630014fe7598630004fd7598630014fc7598630044fe7498630004fd7498630004ff729863000cfe7298630004fd729863000cfc72986300067f52986300067d5298630006bf4298630006bd4298630006df3298630006dd3298630006f65198630006f55198630006f62198630006f521986300057f75586300957c7558630004ff75586300067f75586300047f7558630014fe7558630004fd7558630014fc75586300067c75586300147c7558630004ff7458630044fc7458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d5258630006bf4258630006bd4258630006df3258630006dd3258630006f65158630006f55158630006f62158630006f521586300957e75186300057d7518630006f56118630044ff76d0630004fe76d0630004fd76d063003dde73d0630005dd73d0630006f661d0630006f561d0630004ff7690630004fe7690630004f
  | 17 => 0x4ff7358440006df7358440004df735844003cfc7358440006dc735844003cdc7358440004ff725844000cfe7258440004fd725844000cfc72584400067f52584400067d5258440046bf4258440006bd4258440006df3258440006dd3258440046f77158440006f65158440006f55158440046f74158440046bc4158440046f44158440046b44158440006f62158440006f52158440045bd7690440006bd7690440335bf7590440335bd759044029dbe739044032dbf729044032dbd7290440046bf6290440326bd62904403273f52904403273d52904403279f32904403279d3290440045be7190440047b67190440006bd6190440005bd709044031ebe6090440047ba609044003cff76cc440044fe76cc440004fd76cc4400b57e75cc4400057d75cc440045be74cc440005bd74cc44003ede63cc440006dd63cc440004ff768c440044fe768c440004fd768c4400b57e758c4400057d758c440045be748c440005bd748c44027f9c438c440006f6618c440006f5618c440005fa708c440005f9708c440004ff764c440004fd764c440044fc764c440005bf744c440045bc744c44003ede634c440006dd634c440006f6614c440006f5614c44003cff760c440044fe760c440004fd760c44029dbf740c440045bc740c44003edc630c44029f9c430c440045bf7650040006bf7650040004bf7650040315bf7550040315bd755004029dbc735004030dbf725004030dbd7250040046bf62500402febd62500402ff3f52500402ff3d52500402ff9f32500402ff9d3250040005bc7150040045bf7050040047bb7050040306be6050040047ba60500402ffbb20500402ffb82050040004ff75593300067f75593300047f7559330014fe7559330004fd7559330014fc75593300067c75593300147c755933003ebf7459330006be5459330006bd545933003cfc735933003ebe435933003ebc4359330004ff725933000cfe7259330004fd725933000cfc72593300067f52593300067d5259330006bf4259330006bd425933003edf3259330006dd3259330004ff7159330004fc7159330004ff7598730014fe75987300067e75987300147e7598730004fd75987300067d75987300047d7598730014fc7598730044fe7498730004fd7498730004ff729873000cfe7298730004fd729873000cfc72987300067f52987300067d5298730006bf4298730006bd429873003edf3298730006dd329873003ef6719873003ef7319873003ef4319873003edc3098730004ff7558730014fe7558730004fd7558730014fc7558730004ff7458730044fc7458730004ff725873000cfe7258730004fd725873000cfc72587300067f52587300067d5258730006bf4258730006bd425873003edf3258730006dd325873003ef7715873003ef7315873003ef4315
  | 18 => 0xf42d8540006bd42d8540006df32d8540006dd32d8540006f761985400057f75585400cd7c7558540005df7358540005dc7358540005ef72585400c5ec72585400cd7e75185400057d7518540006f56118540004ff7518540014fe75185400067e75185400147e7518540004fd75185400067d75185400047d7518540014fc751854003cfe7318540004fd7318540004ff721854000cfe7218540004fd721854000cfc72185400067f52185400067d5218540006bf4218540006bd4218540006df3218540006dd3218540006f76190540006f46190540005fa7090540005f970905400057f75505400cd7c7550540005df7350540005dc7350540006f76150540006f46150540047b44150540005fb7050540005f87050540047b84050540004fe76cc540004fd76cc54003cfc76cc5400cd7e75cc5400057d75cc540004fe768c540004fd768c540004fc768c5400cd7e758c5400057d758c540006df638c54003edc638c540004ff764c540004fe764c540004fc764c540004fe760c540004fd760c54003cfc760c540045be740c540005bd740c540006df630c54003edc630c540005fa700c540005f9700c5400cd7e75901400057d7590140045fa7090140046fb609014035f3e75901400073d759014035ebf659014035ebd65901402a6bc6390140305bf7290140305bd7290140356bf6290140356bd62901403573f52901403573d52901403579f32901403579d3290140006bc6190140045be7090140046bf6090140047bb6090140004ff7558c400067f7558c400047f7558c40014fe7558c40004fd7558c40014fc7558c400067c7558c400147c7558c40046df7358c40006de5358c40006dd5358c40046df4358c40046bc4358c40046dc4358c400469c4358c40004ff7258c4000cfe7258c40004fd7258c4000cfc7258c400067f5258c400067d5258c40046bf4258c40006bd4258c40006df3258c40006dd3258c40004ff7158c40004fc7158c40045bd7690c4029ebd7690c4029dbf7590c4034dbd7590c40045be7390c400479e7390c40046bf6390c4029ebd6390c4029dbf7290c40345bd7290c40046bf6290c4033ebd6290c4033f3f5290c4033f3d5290c4029f9f3290c4033f9d3290c40005be7190c40005bd7090c402a6be6090c40047ba6090c40004ff7598440014fe7598440004fd7598440014fc759844003cfe7398440004fd7398440004ff729844000cfe7298440004fd729844000cfc72984400067f52984400067d5298440046bf4298440006bd4298440006df3298440006dd3298440046f67198440006f65198440006f55198440046f74198440046f44198440006f62198440006f52198440004ff75584400067f75584400047f7558440014fe7558440004fd7558440014fc75584400067c75584400147c7558440
  | 19 => 0x640005fa7090640005f970906403b5bf75906403b5bd75906403af3e65906400073d65906402a5be73906403a5bf72906403a5bd729064031ebf629064031ebd629064031f3f529064031f3d529064031f9f329064031f9d3290640045be7190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b97090640046be60906400057f75506400d57c755064014e7e65506400067d6550640005df7350640005dc7350640006f66150640006f56150640005fb7050640005f87050640005bd7610640046bd7610640045bf75106400473e751064039dbd75106400473d75106400053d75106403973e65106400073d65106402a5be7310640045bf721064038dbd7210640386bf6210640386bd62106403873f52106403873d52106403879f32106403879d3210640047b67110640006bd6110640005bd7010640047ba601064003cff76cc640004fe76cc640004fd76cc6400d57e75cc6400057d75cc6401267e65cc6400067d65cc640045be74cc640005bd74cc640006f661cc640006f561cc640004ff768c640004fe768c640004fd768c6400d57e758c6400057d758c6401167e658c6400067d658c640045be748c640005bd748c64003ede638c640006dd638c6400079c438c640004ff764c640004fd764c640004fc764c64010e7e654c6400067d654c640005bf744c640045bc744c64003cff760c640004fe760c640004fd760c6400f67e650c6400067d650c6402a5bf740c640045bc740c64003ede630c640006dd630c6402a79c430c640006f6610c640006f5610c640005fa700c640005f9700c640005bd76d0240046bd76d0240045bf75d02400473e75d024037dbd75d02400473d75d02400053d75d02403673e65d02400073d65d02402a5be73d0240045bf72d0240375bd72d024036ebf62d024036ebd62d024036f3f52d024036f3d52d024036f9f32d024036f9d32d0240005be71d0240047ba60d0240367ba50d0240367b950d0240004ff75d8d40014fe75d8d40004fd75d8d40014fc75d8d40006df53d8d40006dc53d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400067f52d8d400067d52d8d40006bf42d8d40006bd42d8d40006df32d8d40006dd32d8d40004fe71d8d40004fd71d8d40006df6398d400057f7558d400cd7c7558d400cd7e7518d400057d7518d4003ede6318d40006dd6318d40006df6390d4003edc6390d40005fa7090d40005f97090d4003cfc7650d400057f7550d400cd7c7550d40006df6350d4003edc6350d400479c4350d40005fb7050d40005f87050d40004ff75d8540014fe75d8540004fd75d8540014fc75d854003cfe73d8540004fd73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d85400067f52d85400067d52d8540006b
  | 20 => 0x67e71596400067d71596400067c71596403fe7f41596403fe7c41596400067f21596400067e21596400067d21596400067c21596400d67f70596403fe7e70596400d67d70596400d67c70596403fe7f40596400d67e40596403fe7c40596400067f20596400067e20596400067d20596400067c20596400d57e75d8e400057d75d8e400067e65d8e400067d65d8e40005f671d8e40005f571d8e400067e6598e400067d6598e40006df6398e400067e6558e400067d6558e40004ff7558e40014fe7558e40004fd7558e40014fc7558e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e400067f5258e400067d5258e40006bf4258e40006bd4258e40006df3258e40006dd3258e40004ff7158e40004fc7158e400d57e7518e400057d7518e400067e6518e400067d6518e4003ede6318e40006dd6318e401967e6590e400067d6590e4003ede6390e40006dd6390e40005fa7090e40005f97090e402a5bf7590e403f5bd7590e403ef3e6590e400073d6590e40045be7390e402a79e6390e402a6bd6390e400079d6390e402a5bf7290e403e5bd7290e403debf6290e403debd6290e403df3f5290e403df3d5290e402a79f3290e403df9d3290e40005be7190e402a7ba7090e40005bd7090e402a7b97090e40046be6090e4003cff7650e400057f7550e400d57c7550e401867e6550e400067d6550e4003ede6350e40006dd6350e400479c4350e40005fb7050e40005f87050e40005bd7610e40046bd7610e40045bf7510e400473e7510e403d5bd7510e400473d7510e400053d7510e403cf3e6510e400073d6510e400479e7310e402a6bd6310e40045bf7210e40047ae7210e403c5bd7210e40047ad7210e40005ad7210e403bebf6210e403bebd6210e403bf3f5210e403bf3d5210e402a79f3210e403bf9d3210e40005be7110e40005bd7010e40047ba6010e400d57e75d86400057d75d86400067e65d86400067d65d8640005de73d8640005dd73d86400067e65986400067d6598640006f76198640004ff7598640014fe7598640004fd7598640014fc759864003cfe7398640004fd7398640004ff729864000cfe7298640004fd729864000cfc72986400067f52986400067d5298640006bf4298640006bd4298640006df3298640006dd3298640006f62198640006f521986400067e65586400067d6558640004ff7558640014fe7558640004fd7558640014fc7558640004ff735864003cfc7358640004ff725864000cfe7258640004fd725864000cfc72586400067f52586400067d5258640006bf4258640006bd4258640006df3258640006dd3258640006f62158640006f521586400d57e75186400057d75186400067e65186400067d6518640006f561186401567e65906400067d6590640006f66190640006f5619
  | 21 => 0xe42597400467d42597400063d42597400467c42597400067f32597400065f32597400067e32597400067d32597400065d32597400067c32597400067f71597400067e71597400067d71597400067c71597400467f41597400467e41597400467d41597400467c41597400067f21597400067e21597400067d21597400067c21597400e67f70597400e67e70597400067d70597400e67c70597400467f40597400467e40597400467d40597400467c40597400463c40597400067f20597400067e20597400067d20597400067c2059740004ff7558f40014fe7558f40004fd7558f40014fc7558f40046df7358f40046df4358f40046dc4358f40004ff7258f4000cfe7258f40004fd7258f4000cfc7258f400067f5258f400067d5258f40046bf4258f40006bd4258f40006df3258f40006dd3258f40004ff7158f40004fc7158f40004ff7598740014fe7598740004fd7598740014fc759874003cfe7398740004fd7398740004ff729874000cfe7298740004fd729874000cfc72987400067f52987400067d5298740046bf4298740006bd4298740006df3298740006dd3298740046f67198740046f74198740046f44198740046bc4098740004ff7558740014fe7558740004fd7558740014fc7558740004ff735874003cfc7358740004ff725874000cfe7258740004fd725874000cfc72587400067f52587400067d5258740046bf4258740006bd4258740006df3258740006dd3258740046f77158740046f74158740046f4415874003cff76cc740044fe76cc740004fd76cc7400e57e75cc7400057d75cc7401267e65cc7400067d65cc740004ff768c740044fe768c740004fd768c7400e57e758c7400057d758c7401167e658c7400067d658c74003ede638c740006dd638c740005fa708c740005f9708c740004ff764c740004fd764c740044fc764c74010e7e654c7400067d654c74003cff760c740044fe760c740004fd760c7400f67e650c7400067d650c740045be740c740005bd740c74003ede630c740006dd630c7400d57f76596400d67f76596400147f76596400d73e74596400073d74596400057f72596400057d72596400067f62596400067e62596400067d62596400067c62596400073f42596400073d42596400075f32596400075d32596403ff7b40596403ff7840596400d67f74596403fe7e74596400067d74596403fe7c74596400067f73596400067e73596400067d73596400067c73596403fe7f43596403fe7c43596400067f72596400047f72596400067e72596400067d72596400047d72596400067c72596403fe7f42596400063f42596400067e42596400067d42596400063d42596403fe7c42596400067f32596400065f32596400067e32596400067d32596400065d32596400067c32596400067f7159640
  | 22 => 0x9031004fd7559031014fc75590310067c75590310147c755903103ebf7459031006be5459031006bd545903103cfe735903103cfc735903103edc735903103cdc735903103ebe435903103ebc435903103edc435903103e9c4359031004ff725903100cfe7259031004fd725903100cfc72590310067f52590310067d5259031006bf4259031006bd425903103edf3259031006dd3259031004ff7059031004fc705903103ddd76d0c312dedd76d0c312dddf75d0c3143ddd75d0c3103dde74d0c3103f9e74d0c3103edf64d0c312dedd64d0c312dddf72d0c31435dd72d0c3103edf62d0c3142edd62d0c3142f5f52d0c3142f5d52d0c312df9f42d0c3142f9d42d0c31005dd71d0c3127ede61d0c3103fd661d0c31005de70d0c31004fd76d043103ddc73d0431004ff7690431044fd7690431046be6490431006bd649043103dde7390431005dd7390431004ff76504310057f75504310f57c7550431005df735043103ddc7350431044ff761043103cfe7610431004fd761043103cfc76104310f57e75104310057d7510431046be6410431006bd641043103dde7310431005dd731043103ddf764c431006df764c431004df764c431425df754c431425dd754c4312ddde744c4312dddc744c43141ddf724c43141ddd724c43103edf624c431406dd624c4314075f524c4314075d524c4314079f424c4314079d424c43103ddf714c43103fd7714c431416de614c43103fd6614c43140fd6514c43140fd5514c431407d7214c431407d4214c431005dc704c431004ff7598031014fe7598031004fd7598031014fc7598031044fe7498031004fd7498031004ff729803100cfe7298031004fd729803100cfc72980310067f52980310067d5298031006bf4298031006bd429803103edf3298031006dd329803103efa7098031006fa5098031006f9509803103efb309803103ef83098031006fa2098031006f92098031004ff75580310067f75580310047f7558031014fe7558031004fd7558031014fc75580310067c75580310147c7558031004ff7458031006bf7458031004bf7458031044fc7458031006bc7458031044bc7458031004ff725803100cfe7258031004fd725803100cfc72580310067f52580310067d5258031006bf4258031006bd425803103edf3258031006dd325803103efb7058031006fa5058031006f9505803103efb305803103edc305803103ef8305803103ed83058031006fa2058031006f920580310467f74597400467e74597400467d74597400467c74597400067f73597400067e73597400067d73597400067c73597400467f43597400467e43597400467d43597400467c43597400067f72597400047f72597400067e72597400067d72597400047d72597400067c72597400467f42597400463f42597400467
  | 23 => 0xcfc72582310067f52582310067d5258231006bf4258231006bd4258231006df3258231006dd3258231006fa2058231006f920582311157e75182310057d75182310067e65182310067d6518231006f96018231044fe76d9131004ff75d9131014fe75d9131004fd75d9131014fc75d9131006bf54d9131006bc54d9131004ff72d913100cfe72d9131004fd72d913100cfc72d91310067f52d91310067d52d9131006bf42d9131006bd42d9131006df32d9131006dd32d9131004fe70d9131004fd70d9131006bf64991310057f755913110d7c7559131004ff75591310067f75591310047f7559131014fe7559131004fd7559131014fc75591310067c75591310147c7559131006bf7459131004ff7359131006df7359131004df7359131004ff725913100cfe7259131004fd725913100cfc72591310067f52591310067d5259131006bf4259131006bd4259131006df3259131006dd3259131004ff7159131006f77159131004ff7059131004fc7059131004fe761913110d7e75191310057d7519131046be6419131006bd6419131004fe76d0d31006bf64d0d31046bc64d0d31005f671d0d31005f571d0d31044fc7650d310057f7550d3110d7c7550d31006bf6450d31046bc6450d3103f9c4350d31005f77150d31005f47150d3103cfe76d053103cfc76d0531006bf64d0531046bc64d053103dde73d0531005dd73d0531004fe7690531044ff7650531004fd765053103cfc76505310057f755053110d7c7550531006bf6450531046bc6450531005df735053103ddc7350531004fe761053110d7e75105310057d751053110d7e758c5310057d758c53103df6718c53103ef7618c53144f5e758c5310075d758c53144edf658c53144edd658c53127ede648c53127edc648c531415df728c531415dd728c531446df628c531446dd628c5314475f528c5314475d528c5314479f428c5314479d428c53103dde718c53103edf618c53103fd7618c531004ff75d8131014fe75d8131004fd75d8131014fc75d8131044fe74d8131004fd74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006bf42d8131006bd42d8131006df32d8131006dd32d8131006fb60981310057f755813110d7c7558131005bf7458131005bc7458131005ef7258131105ec725813110d7e75181310057d7518131006f96018131004ff7518131014fe75181310067e75181310147e7518131004fd75181310067d75181310047d7518131014fc7518131044fe7418131004fd7418131004ff721813100cfe7218131004fd721813100cfc72181310067f52181310067d5218131006bf4218131006bd4218131006df3218131006dd3218131006de3118131004ff75590310067f75590310047f7559031014fe755
  | 24 => 0xc7559231006bf7459231006df7359231004ff725923100cfe7259231004fd725923100cfc72592310067f52592310067d5259231006bf4259231006bd4259231006df3259231006dd3259231004ff7059231004fc70592311157e75192310057d75192310067e65192310067d6519231046be6419231006bd64192311a67e65d0e310067d65d0e31046be64d0e31006bd64d0e31005f671d0e31005f571d0e3127edd76d0e3127ddf75d0e314addd75d0e314a75e65d0e310075d65d0e3103dde74d0e3127edf64d0e3127f9e64d0e3127edd64d0e310079d64d0e3127ddf72d0e3149ddd72d0e31496df62d0e31496dd62d0e314975f52d0e314975d52d0e3127f9f42d0e314979d42d0e3127fd671d0e31005dd71d0e3127fd571d0e3103ede61d0e31005de70d0e31044ff7650e310057f7550e311157c7550e311867e6550e310067d6550e31046be6450e31006bd6450e3103f9c4350e31005f77150e31005f47150e31005dd7610e3103edd7610e3103ddf7510e3103f5e7510e3148ddd7510e3103f5d7510e310055d7510e314875e6510e310075d6510e3103f9e7410e3127edf6410e3127edd6410e3103ddf7210e3103fce7210e3147ddd7210e3103fcd7210e31005cd7210e31476df6210e31476dd6210e314775f5210e314775d5210e3127f9f4210e314779d4210e31005dd7110e3103fd66110e31005de7010e311667e65d06310067d65d063103cfd76906311567e65906310067d6590631046be6490631006bd649063103dde7390631005dd73906310057f75506311157c755063114e7e65506310067d6550631005df735063103ddc735063103cfd76106311157e75106310057d75106311367e65106310067d6510631046be6410631006bd641063103dde7310631005dd7310631005dd76cc63103edd76cc63103ddf75cc63103f5e75cc63146ddd75cc63103f5d75cc6310055d75cc6314575e65cc6310075d65cc63127dde74cc63103ddc74cc63103ddf72cc631465dd72cc63145edf62cc63145edd62cc63145f5f52cc63145f5d52cc63145f9f42cc63145f9d42cc63103fd661cc631457d651cc631457d551cc631005de70cc6311157e75d82310057d75d82310067e65d82310067d65d8231005be74d8231005bd74d82310067e65982310067d6598231006fb6098231004ff7598231014fe7598231004fd7598231014fc7598231044fe7498231004fd7498231004ff729823100cfe7298231004fd729823100cfc72982310067f52982310067d5298231006bf4298231006bd4298231006df3298231006dd3298231006fa2098231006f920982310067e65582310067d6558231004ff7558231014fe7558231004fd7558231014fc7558231004ff7458231044fc7458231004ff725823100cfe7258231004fd7258231
  | 25 => 0x9331004ff7059331004fc70593311667e65d07310067d65d0731046be64d0731006bd64d073103dde73d0731005dd73d07311567e65907310067d6590731044ff76507310057f75507311257c755073114e7e65507310067d6550731046be6450731006bd6450731005df735073103ddc73507311257e75107310057d75107311367e65107310067d6510731004ff7598331014fe7598331004fd7598331014fc7598331044fe7498331004fd7498331004ff729833100cfe7298331004fd729833100cfc72983310067f52983310067d5298331006bf4298331006bd429833103edf3298331006dd329833103edc319833103efa709833103efb309833103ef83098331004ff7558331014fe7558331004fd7558331014fc7558331004ff7458331044fc7458331004ff725833100cfe7258331004fd725833100cfc72583310067f52583310067d5258331006bf4258331006bd425833103edf3258331006dd325833103efb705833103efb305833103ef830583311157f76596311167f76596310147f76596311175e73596310075d73596310057f72596310057d72596310067f62596310067e62596310067d62596310067c62596310073f42596310073d42596310075f32596310075d32596314b77731596314b77431596310067f74596310067e74596310067d74596310067c74596311167f73596314b67e73596310067d73596314b67c73596314b67e43596314b67c43596310067f72596310047f72596310067e72596310067d72596310047d72596310067c72596310067f42596310063f42596310067e42596310067d42596310063d42596310067c42596314b67f32596310065f32596310067e32596310067d32596310065d32596314b67c32596311167f71596314b67e71596311167d71596311167c71596314b67f31596311167e31596314b67c31596310067f21596310067e21596310067d21596310067c21596310067f70596310067e70596310067d70596310067c70596314b67f30596314b67c30596310067f20596310067e20596310067d20596310067c20596311157e75d92310057d75d92310067e65d92310067d65d9231005fa70d9231005f970d9231004ff75d9231014fe75d92310067e75d92310147e75d9231004fd75d92310067d75d92310047d75d9231014fc75d9231006dd73d9231004ff72d923100cfe72d9231004fd72d923100cfc72d92310067f52d92310067d52d9231006bf42d9231006bd42d9231006df32d9231006dd32d9231006f671d9231004fe70d9231006fa70d9231004fa70d9231004fd70d9231006f970d9231004f970d9231004fd76992310067e65992310067d6599231006bf6499231044ff76592310067e65592310067d6559231004ff7559231014fe7559231004fd7559231014f
  | 26 => 0x467f40594410467e40594410467d40594410467c40594410463c40594410067f20594410067e20594410067d20594410067c2059441004ff7558c41014fe7558c41004fd7558c41014fc7558c41046df7358c41046df4358c41046dc4358c41004ff7258c4100cfe7258c41004fd7258c4100cfc7258c410067f5258c410067d5258c41046bf4258c41006bd4258c41006df3258c41006dd3258c41004ff7058c41004fc7058c41045bf7650441006bf7650441004bf76504410073f75504414c73c75504410473e65504410473d65504410079f73504410079c73504414d5bf72504414d5bd7250441046bf62504414bebd62504414bf3f52504414bf3d52504414bf9f32504414bf9d3250441045bf7150441047b771504414cebe6150441047b661504414c7b651504414c7b551504414bfb721504414bfb42150441005bc7050441004ff7598041014fe7598041004fd7598041014fc759804103cfe7398041004fd7398041004ff729804100cfe7298041004fd729804100cfc72980410067f52980410067d5298041046bf4298041006bd4298041006df3298041006dd3298041046fa7098041046fb4098041046f84098041006fa2098041006f92098041004ff7558041014fe7558041004fd7558041014fc7558041004ff735804103cfc7358041004ff725804100cfe7258041004fd725804100cfc72580410067f52580410067d5258041046bf4258041006bd4258041006df3258041006dd3258041046fb7058041046fb4058041046bc4058041046f84058041046b84058041006fa2058041006f920580410067f74597310067e74597310067d74597310067c745973103e7f735973103e7e735973103e7d735973103e7c735973103e7f435973103e7e435973103e7d435973103e7c43597310067f72597310047f72597310067e72597310067d72597310047d72597310067c72597310067f42597310063f42597310067e42597310067d42597310063d42597310067c425973103e7f325973103e5f325973103e7e325973103e7d32597310065d325973103e7c32597311267f71597311267e71597310067d71597311267c715973103e7f315973103e7e315973103e7d315973103e7c315973103e5c31597310067f21597310067e21597310067d21597310067c21597310067f70597310067e70597310067d70597310067c705973103e7f305973103e7e305973103e7d305973103e7c30597310067f20597310067e20597310067d20597310067c2059731004ff7559331014fe7559331004fd7559331014fc755933103ebf745933103cfc735933103ebe435933103ebc4359331004ff725933100cfe7259331004fd725933100cfc72593310067f52593310067d5259331006bf4259331006bd425933103edf3259331006dd325
  | 27 => 0xd5118d41006dc5118d412dedf4118d41006dd4118d412dedc4118d41006df2118d41006de2118d41006dd2118d41006dc2118d4103edf7018d4103ede7018d4103edd7018d4103edc7018d41006df5018d41006de5018d41006dd5018d41006dc5018d412dedf4018d412dedc4018d41006df2018d41006de2018d41006dd2018d41006dc2018d410067f6590d411967c6590d41006df6390d4103edc6390d41005f67190d41005f57190d4103cfc7650d410057f7550d4114d7c7550d410067f6550d411867c6550d41006df6350d4103edc6350d410479c4350d41005f77150d41005f47150d410067f65905411567c6590541006df6390541006dc6390541045f67190541046f761905410073f65905414e73c65905410079f63905410079c63905414cdbf72905414cdbd72905414debf62905414debd62905414df3f52905414df3d52905414df9f32905414df9d3290541045be7190541046bf6190541047b761905410067f65d81410067c65d8141006df63d8141006dc63d8141004ff75d8141014fe75d8141004fd75d8141014fc75d814103cfe73d8141004fd73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d8141006bf42d8141006bd42d8141006df32d8141006dd32d8141006fb20d8141006f820d814114d7e75981410057d75981410067f65981410067c6598141005de7398141005dd7398141006df6398141006dc6398141006fb60981410057f755814114d7c75581410067f65581410067c6558141005df7358141005dc7358141006df6358141006dc6358141005ef7258141145ec72581410067f65181410067c6518141006df6318141006dc6318141006f96018141004ff7518141014fe7518141004fd7518141014fc751814103cfe7318141004fd7318141004ff721814100cfe7218141004fd721814100cfc72181410067f52181410067d5218141006bf4218141006bd4218141006df3218141006dd3218141006be4118141006fb2018141006f820181410467f74594410467e74594410467d74594410467c74594410067f73594410067e73594410067d73594410067c73594410467f43594410467e43594410467d43594410467c43594410067f72594410047f72594410067e72594410067d72594410047d72594410067c72594410467f42594410463f42594410467e42594410467d42594410063d42594410467c42594410067f32594410065f32594410067e32594410067d32594410065d32594410067c32594411367f71594410067e71594411367d71594411367c71594410467f41594410467e41594410467d41594410467c41594410067f21594410067e21594410067d21594410067c21594410067f70594410067e70594410067d70594410067c7059441
  | 28 => 0x95410067f20d95410067e20d95410067d20d95410067c20d95410067f65d8d410067c65d8d41004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d41006df53d8d41006de53d8d41006dd53d8d41006dc53d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d410067f52d8d410067d52d8d41006bf42d8d41006bd42d8d41006df32d8d41006de32d8d41006dd32d8d41006dc32d8d41004fe70d8d41004fd70d8d41006df65d8d410075f65d8d410065f65d8d41006de65d8d41006dd65d8d41006dc65d8d410075c65d8d410065c65d8d41005df72d8d41005dd72d8d41006df62d8d41006de62d8d41006dd62d8d41006dc62d8d410075f52d8d410075d52d8d410079f42d8d410079d42d8d4127fd741d8d4127fd441d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d41006df74d8d4127ede74d8d41006df54d8d4127ede54d8d41006dd54d8d4127edc54d8d41006df72d8d41004df72d8d41006de72d8d41006dd72d8d41004dd72d8d41006dc72d8d41006df52d8d410065f52d8d41006de52d8d41006dd52d8d410065d52d8d41006dc52d8d4127edf42d8d410069f42d8d41006de42d8d41006dd42d8d410069d42d8d4127edc42d8d4127edf71d8d41006dd71d8d41006df51d8d41006de51d8d41006dd51d8d41006dc51d8d4127edf41d8d4127edc41d8d41006df21d8d41006de21d8d41006dd21d8d41006dc21d8d41006df70d8d41006de70d8d41006dd70d8d41006dc70d8d41006df50d8d41006de50d8d41006dd50d8d41006dc50d8d4127edf40d8d4127edc40d8d41006df20d8d41006de20d8d41006dd20d8d41006dc20d8d4114d7e7598d410057d7598d410067f6598d410067c6598d41006df6398d410057f7558d4114d7c7558d410067f6558d410067c6558d410067f6518d410067c6518d4103ede6318d41006dd6318d41005de7618d41006de7618d41006df6518d410075f6518d410065f6518d41006de6518d41006dd6518d41006dc6518d410075c6518d410065c6518d41005df7218d41005dd7218d41006df6218d41006de6218d41006dd6218d41006dc6218d410075f5218d410075d5218d410079f4218d410079d4218d412dfd74118d412dfd44118d4103edf7518d4103ede7518d4103edd7518d4103edc7518d4103edf7418d4103ede7418d4103edc7418d41006df5418d412dede5418d41006dd5418d412dedc5418d4103edf7218d4103cdf7218d4103ede7218d4103edd7218d41004dd7218d4103edc7218d41006df5218d410065f5218d41006de5218d41006dd5218d410065d5218d41006dc5218d412dedf4218d410069f4218d41006de4218d41006dd4218d410069d4218d412dedc4218d4103edf7118d4103edd7118d41006df5118d41006de5118d41006d
  | 29 => 0xcfc72583410067f52583410067d5258341046bf4258341006bd4258341006df3258341006dd3258341046fb7058341046fb4058341046f840583411557e75d8e410057d75d8e41005fa70d8e41005f970d8e411557e7598e410057d7598e41006df6398e41004ff7558e41014fe7558e41004fd7558e41014fc7558e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e410067f5258e410067d5258e41006bf4258e41006bd4258e41006df3258e41006dd3258e41004ff7058e41004fc7058e4103ede6318e41006dd6318e4103ede6390e41006dd6390e41005f67190e41005f57190e4103cff7650e410057f7550e411557c7550e4103ede6350e41006dd6350e410479c4350e41005f77150e41005f47150e41005bd76d0641046bd76d0641045bf72d0641505bd72d06414febf62d06414febd62d06414ff3f52d06414ff3d52d06414ff9f32d06414ff9d32d0641047b661d06414f7b651d06414f7b551d0641005be70d0641006fb6098241004ff7598241014fe7598241004fd7598241014fc759824103cfe7398241004fd7398241004ff729824100cfe7298241004fd729824100cfc72982410067f52982410067d5298241006bf4298241006bd4298241006df3298241006dd3298241006fa5098241006f95098241006fa2098241006f920982410057f75582411557c7558241004ff75582410067f75582410047f7558241014fe7558241004fd7558241014fc75582410067c75582410147c7558241004ff735824103cfc7358241004ff725824100cfe7258241004fd725824100cfc72582410067f52582410067d5258241006bf4258241006bd4258241006df3258241006dd3258241006fa5058241006f95058241006fa2058241006f920582411557e75182410057d7518241006f9601824114d7e76d954114e7e76d95410147e76d95410057f72d95410057d72d95410067f62d95410067e62d95410067d62d95410067c62d95410073f42d95410073d42d95410075f32d95410075d32d95414ef7741d95414ef7441d95410067f74d95414ee7e74d954114e7d74d95414ee7c74d95410067f73d95410067e73d95410067d73d95410067c73d95414ee7f43d95414ee7c43d95410067f72d95410047f72d95410067e72d95410067d72d95410047d72d95410067c72d95414ee7f42d95410063f42d95410067e42d95410067d42d95410063d42d95414ee7c42d95410067f32d95410065f32d95410067e32d95410067d32d95410065d32d95410067c32d95414ee7f71d954114e7e71d954114e7d71d954114e7c71d95414ee7f41d954114e7d41d95414ee7c41d95410067f21d95410067e21d95410067d21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d95414ee7f40d95414ee7c40d
  | 30 => 0xe4158843046ed4158843046ec415884303eef315884303eee315884303eed315884303eec315884303ecc3158843006ef7058843006ee7058843006ed7058843006ec7058843006ef5058843006ee5058843006ed5058843006ec5058843046ef4058843046ee4058843046ed4058843046ec4058843046ac405884303eef305884303eee305884303eed305884303eec3058843004ff7598443014fe7598443004fd7598443014fc7598443004ff729844300cfe7298443004fd729844300cfc72984430067f52984430067d5298443046bf4298443006bd429844303edf3298443006dd329844303ef67198443046f74198443046f4419844303ef7319844303ef43198443004fe7098443004fd7098443046bc4098443004ff7558443014fe7558443004fd7558443014fc7558443004ff725844300cfe7258443004fd725844300cfc72584430067f52584430067d5258443046bf4258443006bd425844303edf3258443006dd325844303ef77158443046f74158443046f4415844303ef7315844303edc315844303ef43158443004ff7058443004fc7058443004ff7598043014fe7598043004fd7598043014fc7598043004ff729804300cfe7298043004fd729804300cfc72980430067f52980430067d5298043046bf4298043006bd429804303edf3298043006dd3298043004fe7198043004fd719804303edc319804303efa7098043046fb4098043046f8409804303efb309804303ef83098043004ff7558043014fe7558043004fd7558043014fc7558043004ff725804300cfe7258043004fd725804300cfc72580430067f52580430067d5258043046bf4258043006bd425804303edf3258043006dd3258043004ff7158043004fc715804303efb7058043046fb4058043046bc4058043046f8405804303efb305804303ef83058043004ff7558f410067f7558f410047f7558f41014fe7558f41004fd7558f41014fc7558f410067c7558f410147c7558f41046df7358f41006de5358f41006dd5358f41046df4358f41046dc4358f41004ff7258f4100cfe7258f41004fd7258f4100cfc7258f410067f5258f410067d5258f41046bf4258f41006bd4258f41006df3258f41006dd3258f41004ff7058f41004fc7058f41004ff7598341014fe75983410067e75983410147e7598341004fd75983410067d75983410047d7598341014fc759834103cfe7398341004fd7398341004ff729834100cfe7298341004fd729834100cfc72983410067f52983410067d5298341046bf4298341006bd4298341006df3298341006dd3298341046bc4198341046fa7098341046fb4098341046f84098341004ff7558341014fe7558341004fd7558341014fc7558341004ff735834103cfc7358341004ff725834100cfe7258341004fd7258341
  | 31 => 0x944303e7e735944303e7d735944303e7c735944303e7f435944303e7e435944303e7d435944303e7c43594430067f72594430047f72594430067e72594430067d72594430047d72594430067c72594430467f42594430463f42594430467e42594430467d42594430063d42594430467c425944303e7f325944303e5f325944303e7e325944303e7d32594430065d325944303e7c32594430067f71594430067e71594430067d71594430067c71594430467f41594430467e41594430467d41594430467c415944303e7f315944303e7e315944303e7d315944303e7c315944303e5c31594430067f21594430067e21594430067d21594430067c21594430067f70594430067e70594430067d70594430067c70594430467f40594430467e40594430467d40594430467c40594430463c405944303e7f305944303e7e305944303e7d305944303e7c30594430067f20594430067e20594430067d20594430067c205944303f9f7650c4303d9f7650c430069f7650c435279f7550c430071f7550c435179e7550c435279d7550c435179c7550c435171c7550c4303f9f6550c4303f9e6550c4303f1e6550c4303f9d6550c4303f1d6550c4303f9c6550c4351f9f7250c4351d9f7250c4350f9e7250c4351f9d7250c4351d9d7250c4350f9c7250c4303f9f6250c4303e9f6250c4303f9e6250c4303f8e6250c4303f9d6250c4350e9d6250c4303f8d6250c4303f9c6250c4350f9f5250c4350f1f5250c4350f9e5250c4350f9d5250c4350f1d5250c4350f9c5250c430079f7150c430079e7150c430079d7150c430079c7150c4303f9f6150c4303f9e6150c4303f9d6150c4303f9c6150c435179f5150c435179e5150c435179d5150c435179c5150c4350f9f2150c4350f9e2150c4350f9d2150c4350f9c2150c430079f7050c430079e7050c430079d7050c430079c7050c4303f9f6050c4303f9e6050c4303f9d6050c4303f9c6050c435179f5050c435179e5050c435179d5050c435179c5050c4350f9f2050c4350f9e2050c4350f9d2050c4350f9c2050c43006ef7558843006ee75588430066e7558843006ed75588430066d7558843006ec7558843046ef7458843046ee7458843046ae7458843046ed745884316ead7458843046ec7458843046ef5458843046ee5458843046ed5458843046ec545884303eef735884303eee735884303ece735884303eed735884316ecd735884303eec735884303eef535884303eee535884303eed535884303eec535884303eef435884303eaf435884303eee435884303ece435884303eed435884303ead4358843046cd43588430068d435884303eec4358843006ef7158843006ee7158843006ed7158843006ec7158843006ef5158843006ee5158843006ed5158843006ec5158843046ef4158843046e
  | 32 => 0x73f42d95430073d42d95430075f32d95430075d32d954352e7f74d95435367e74d95431867d74d95435367c74d95435367f73d954352e7e73d95431867d73d954352e7c73d95435367f43d954352e7e43d95431867d43d954352e7c43d95430067f72d95430047f72d95430067e72d95430067d72d95430047d72d95430067c72d95435367f42d95430063f42d95430067e42d95430067d42d95430063d42d95435367c42d954352e7f32d95430065f32d95430067e32d95430067d32d95430065d32d954352e7c32d95430067f71d95430067e71d95430067d71d95430067c71d95435367f41d95435367c41d954352e7f31d954352e7c31d95430067f21d95430067e21d95430067d21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95435367f40d95435367c40d954352e7f30d954352e7c30d95430067f20d95430067e20d95430067d20d95430067c20d95430067f65d85430067c65d8543004ff75d8543014fe75d8543004fd75d8543014fc75d8543004ff72d854300cfe72d8543004fd72d854300cfc72d85430067f52d85430067d52d8543006bf42d8543006bd42d8543006df32d8543006dd32d8543006f721d8543006f421d8543004fe70d8543004fd70d85431857e75985430057d75985430067f65985430067c6598543006f76198543005fa7098543005f970985430057f75585431857c75585430067f65585430067c65585430067f65185430067c6518543006f56118543004ff7518543014fe7518543004fd7518543014fc75185432dedf43185432dedc4318543004ff721854300cfe7218543004fd721854300cfc72185430067f52185430067d5218543006bf4218543006bd4218543006df3218543006dd3218543006f72118543006f42118543004fe7018543004fd70185430067f65d81430067c65d8143004ff75d8143014fe75d8143004fd75d8143014fc75d8143004ff72d814300cfe72d8143004fd72d814300cfc72d81430067f52d81430067d52d8143006bf42d8143006bd42d8143006df32d8143006dd32d8143004fe71d8143004fd71d8143006fb20d8143006f820d81431857e75981430057d75981430067f65981430067c6598143005f67198143005f57198143006fb60981430057f75581431857c75581430067f65581430067c65581430067f65181430067c6518143006f96018143004ff7518143014fe7518143004fd7518143014fc751814329ebe431814329ebc4318143004ff721814300cfe7218143004fd721814300cfc72181430067f52181430067d5218143006bf4218143006bd4218143006df3218143006dd3218143004fe7118143004fd7118143006fb2018143006f820181430467f74594430467e74594430467d74594430467c745944303e7f735
  | 33 => 0xf7558743014fe7558743004fd7558743014fc75587430067c75587430147c755874303cfc7458743004ff725874300cfe7258743004fd725874300cfc72587430067f52587430067d5258743046bf4258743006bd4258743006df3258743006dd3258743046f77158743046f74158743046f44158743004ff7058743004fc7058743004ff7598343014fe75983430067e75983430147e7598343004fd75983430067d75983430047d7598343014fc759834303cfe74983432a6be4398343046bc4398343004ff729834300cfe7298343004fd729834300cfc72983430067f52983430067d5298343046bf4298343006bd4298343006df3298343006dd3298343004fe7198343004fd7198343046fa7098343046fb4098343046f84098343004ff7558343014fe7558343004fd7558343014fc755834303cfc7458343004ff725834300cfe7258343004fd725834300cfc72583430067f52583430067d5258343046bf4258343006bd4258343006df3258343006dd3258343004ff7158343004fc7158343046fb7058343046fb4058343046f84058343004ff7598643014fe75986430067e75986430147e7598643004fd75986430067d75986430047d7598643014fc759864303cfe739864327edf439864303edc4398643004ff729864300cfe7298643004fd729864300cfc72986430067f52986430067d5298643006bf4298643006bd429864303edf3298643006dd329864303ef6719864303ef7319864303ef43198643004fe7098643004fd7098643004ff7558643014fe7558643004fd7558643014fc755864303cfc7358643004ff725864300cfe7258643004fd725864300cfc72586430067f52586430067d5258643006bf4258643006bd425864303edf3258643006dd325864303ef7715864303ef7315864303ef43158643004ff7058643004fc7058643004ff7598243014fe7598243004fd7598243014fc759824303cfe7398243004ff729824300cfe7298243004fd729824300cfc72982430067f52982430067d5298243006bf4298243006bd429824303edf3298243006dd3298243004fe7198243004fd719824303efa709824303efb309824303ef83098243004ff75582430067f75582430047f7558243014fe7558243004fd7558243014fc75582430067c75582430147c755824303cfc7358243004ff725824300cfe7258243004fd725824300cfc72582430067f52582430067d5258243006bf4258243006bd425824303edf3258243006dd3258243004ff7158243004fc715824303efb705824303efb305824303ef830582431857e76d95431867e76d95430147e76d95435375f43d954352f3e43d954352f3c43d95435375c43d95430057f72d95430057d72d95430067f62d95430067e62d95430067d62d95430067c62d9543
  | 34 => 0x25000401400100080040000060010000052060001005c000004004801404a0000070034000015000804800c000000001c006044002801801600a006004400000001f8034022006000002c00800000b800000200400000000000050090004020000000001c000030009002401c000008803c02000c0008028016001001804403a00601e000400a002005000c01000000b00080000030018054014002000804000000c0020020000010003004400000000680040080100150028004002002000001401c000802c01800200f001402000c00200000000140090004004026002800000402b0058000000005006800402201200300640120040068000002001003801c004001011802c0020080028088030005006800000e00a0080044000000004803400e0040000000012007000009400a01100c805c010003006800800000000e8014008000000000c00200000b8008000006000004400000900380280000000010010000000000000000600200a00100100190000004004015005800001402c003800c00c00a000002404a0000018000018004000800000000d0040004002003004801000a01f00400800000030070098000003000000c008005000008000c003000000002200300180a000e005014001000c002000802000e00300b800c02202b0000054002000003800c00000000d0024066000001000007a000000001c00a001000000402e000000001000000000f000400c00801a00000040070030008002000000000c01a02a001000000000400a805c00607000d002c024001005803c00000100b00540000070000018004000001000001200600900140320000000074002006007006c002007004000800600802780200080020000004028014001801c00000b001805001800600000680020000100004004000000000c03001500380180020030018074002024001000401200202e0000002006000800001a0000020044000005001001400204f000804000a00a0010000102001001800800a0090028090000006000000003e002000002801e00500580440100180060004000011007806400a00200000080040060000014006025000000000802000500000080000000008012034003000000a00e004002c00200100080080180160018008008007003816000c000005800001200300000f800a002001000400200000a802801200d01080000080010020004000008000003c0000050000000004003004ff7598743014fe7598743004fd7598743014fc759874303cfe7498743004ff729874300cfe7298743004fd729874300cfc72987430067f52987430067d5298743046bf4298743006bd4298743006df3298743006dd3298743046f67198743046f74198743046f44198743004fe7098743004fd7098743004ff75587430067f75587430047
  | 35 => 0xa014000000000a001005000401e000001008408a06100000540000000048000012003005800800e01e0000014002001000007000e002006803400000301a801c038000004802801c028000807400e00a002004400000300e8018004000000800800200000080380000000000008000004015800c0280070090020012004008805801c00e00c004c00200000d0000006001000000000a00d00080200000030110028000019001004000000000000cc004002007815800a0050088000000000004008005c00a0000038000007002000001c000000004001401f002800000a047000810402e05e009000800200200780180780000168004002005001803c01203e00080840400000020004002023011800400a001000000001c00000080280240200030000014004000800000601b00200100020000000018024001009801c00800400100000540080040000004000005807803c000003800400c00000280080040050050014048000000000800605a00480a0018007000000000002b0000010000000012007000400d006001000a003000805c028004009800000400900200200040180070008022000002000801e01c00200040420050000004006000003800008c00600000b000000100400740000380000130000002000000000002e000800000c00400000080160000000000064000000800c0140030018054004017002800000400f00d000c0120090090008014001002800c00201600100040060130040000030004008001000000c000800000e0cc001000000a02c000000000e00000000000920020048004002029001800400e00000380080d000a00e000c01002a00780340060000010004004003000001000201000500640c60000038000000005005800000000c000807c02a01200680040000080000024000011000000000000200100100020120018030000000006800001800b001801c0000050020060016001000800c01000000e8050038017000800400400000d008401401a00e801400201200880000080010030008036000000007400c0070148004014009000001400e008018000001202e005800000003200100840060080008000004001007800c00200700100380040010008000000000003004800a00100a803800e009000802400202a0040028026014003005c0200110088038000011008000802a00200000080a2015002007007600101500000000000188004010000003000400602b00100c0004000000006c020032008002400e000000000c000005000001400400100180040000090030028002008000008800e004002002400600000280780020050000010056001006002400002100d0008046000002000c0000000080010058012005000003c010001003800600000100100020000010028012004002800c0020380
  | 36 => 0x28014036029000802c00c000000000c01201401680000020000060000006003012807008c003018801802c00a02d002000e004000806000200200780780060000008000006003004803801c01000080040140090000044000000002803c00200f00100d000200f010000000801a006001400e000003800402200300000100020000010004000001007804001000c0010020028001001000005200c000801419c001001000000000d00500080000030010094004004000002003c00000100280000000050000010003000008800a00000700080040040010054000001000000400200b000800400e004003800001c010009001401e000000804c022004007000000a00600180a803000000d807c03a00e000000000e0030018010000004000001c00600800b8000002005001805804400d0018024000001000002401c025000001001600e001004402200000080cc0100080018014006002000000402001200280080100000018000000009010006800400b003002400000f00000c4016025000801c01e013000001002200100080c8004021001001402600000e0004008002004002400200400f8044006014005003001802400900000080000000004002003000004002c00e0050110014007001001001000b0158004000004002000c04a005002005000800a000002400e00b00000140000000010000000011000001c00000900000040020000000074018001004800000a0080028048002003019801406000900000100020000010000000004007000000c0030020060006008006001c03400b0028008012001005800800400500a80500220030000004008027000000001a000000800001200400000180200160000000000005014007c0020000020004006010004801c004003004804c0120040058048000000015800002800d00080000080040000000000088000804000a0020088000000002035800000a007004800800003d000006c0000010008004020000000005000000a02b802001c01300000040020030008014000003000007c00400e0018014014004008000000e0010048018000001000800800400600080000000000050000018004000006800400100380000080010010018002023000001c0060040000000006000000801000000000a00080060050050010004003001000400000d0000068002001000001800600d00080b0000000017000401a000002000800a00400000080080010008024000003001800400c00500180f800000000800000000000010028028004007000c00002d000000800c00800a8000062001000000802c010001000800400d00500000020040008034000002001001402c00001400000320000000000010000001005c05400100100400360000020010004003007800000001b00000380120070048000
  | 37 => 0xda09a82fb5a5854557c817605455eb189025002480004c80a3a3edcb713e749894214084337823132b8db432652fe3d7871d4c8ccfc2abd075108c4a01798cd04218b474094a5643dc5af18b53fe0f110a714d800056d467e41d0bbc428d1280000ca830496ae00012ff1c8145b1074afc484d5f3135465400001dd25780000000b4221b0e8f1ed81a525b48c800005133a30d4200000001a5549a00006a64ed12e238c428a2d6884815f120136801a23eb4a6600003f03140cfd068000021a40003e604b00000000386860b0fdccfb36f8ed0000000002dc0000000000310000054d0f7228a550e0df88aa1d1100d4d354463e5ca1700000003ff40002078a5d3864b0309b8a6d55a8cc83f141430250852000135e0000a8e11396b70000aca587000051309fa4338f232a189a41a30d4119e95931a8c9e214751a70c2557a4b7486753d0e5103cd3ce325929618383542e7c05a3b142a62ed0189392c2e905d0b2935b05190800faa03212f251407c1204c0c12b400182d18ee83ef882b500089607e1275314881c127c0000000466000130c1428f6e00009a1317154c37aceb000002484a443440efc4f130c087e07b469754584620c8461e01d400006985550e205285934000423d11820081390a0848100f94ae0400c761a215352714a59417cd470244dbd526400000010703038257583c0aa53655533b0d07d52bd5440970a68525808a03b048438dc00018c0329599d0f63f014d2114c89558f8ce03c5800046b0b4f09acb6029080000e4d5691dd4e4929848180a1041f54acf0152505bd46301ea44985f903d4e072adc8e8137d69f59d4d132e307df21c8ea4124497f08280cd4b603a527fc5a40094f8b02a05ed32680e30d7542a2c8068057d0d33385c81a02d54021c088d135707b920c0ecc0640bc323f923511705cf3bc4f530fa81c21018aaa3f6c9ce11ad1e557a41574d08bcd2ae0c7e2fb069227a13a617e00001c8400058e00003940d1b2c4c82508541e407000000b90000190c130286001a52e55a73858aff19c507b24bc6f74378cf81a74fa30039608243882d3d60d7e05f858558bc00023e946a0000a1946385d32fac81d00cc0fa11e00001dd8fc644a53e53a04003000807800000000180100020010010004008003000000000000d0010010008001003800001a0040000010030001001000400200000080000180090010074018000000009001000000080080460090070010000002000002800200d00d8050004000000017002000000f0000020008002801c04e00300f80d400200001700040180010088000022005001800001a0040050014022000000000c008007014000000200000d80000020110008020008000008000002400000100000700300020034056008003802c00000f005801c026000008004001601f
  | 38 => 0xb986e719a4c420dd0ff710e04b500009a600013b31f5c4e603a8a4d44b80005968e884ad0b591c1427c3b8c18f000128c0000df11c5825400000003a1cbaf4f00451000000000000002ddd0dd00005cc4c5000000000004030ef23d7482c06c0000000042910c0348333ca635af90080000a8a106400048f840a2f3c2ce229c000000000029054410000a21579846a4d04bdf1a512450be078f58b8edc16101c32834ca0300d69040bc49d0000c3a47f5674557531d1ec8b1d0b4cf883548d7d574869a2784bfe436cc2416205d1122013d24600c331b16600000d16376c6eb55ac000225d3eb0000000000108e2b70be323b13011ff859821ac1a80000dcc3bc05b9463400045f400032d80002e395573b782d853882e13ff0d0351153b800000003fd40002e3551835a0553028000005540000000000000000025a96bf47fc60046992b042ac00000000001e884f53c7042a00000000000dd53be00000000c0805fc0000000dc00000000000000022300000000000084952931d0000457d51200000000224000000000000002ca4e00dfe238c00025703f620496360000afb3024ebf030026038e400013589734bd96b124e4b4100ad53c00010ef340857d242001f1fe400049100001c940001a2c000000037322705042ab40002de800000007af2b6800044312e13060000165d11614c551b29400003bfc000000000055284a54d2000002c02ee25bc00014800003810c693110d74000143a2f1000000010e40000e8200000000000c0759d942b4f5c6c01a7130b21009c0212d28d47584c118ec8d84ef46c700010eb5918b4b30a00002e7800051a505a3a382a43dfc8cc41e12fd178cf1b1b8452c066c35f190098226b48ca06d85164dcd68a562442c0b308f03270f7c574c4903d98bfd4314049000078003a137f47f8b1246c020d0d5458a559161345643f947ececb57141af22115bf2981238483cfe24db00003b4c64e19292340e000000000a100aec4bd4ec55af1ba152f00015d401b000000000004b142400000a9e0260000010c00000001bc466c2a346ece1024740003d0800006e045b2090bc03ea4000323c000558118f39f000000000003ee90603dd0000348c000000000000001e814a4e904c0c5151ca52c00000576578876d1ea54112a703150ce000000013ca00000004e780004f900002af40000000fd4000160213a0ddd224c346459d0182f405d600005621640b540b24bd810cc22b5a10a934434b9c06045d459715fe50d099654dc690180483c059508700000731c4c0002fc460f149c00022f44680344881000048b22408c95260a9200015e756980003b0800000000005a50d4e00015c9389c6ed000102906e800031a00002e149d033d561b10d4b661331281000137a1ab846900003fc27bcdd1547837c1b2ce6f4204f
  | 39 => 0xa404a2c56b46741b51f4d1f2009816e040879c02e00005a74c202dcc98d27f48fc0498e481dcc59640490fa000116001f542351e496339f4885000000000015de0ae018e34d49150a5c0000e751d5000000000015c71f552a40000cef0d2458b0000ac3000097e00000004fbcb98123c5572cf4fbf4f254364d1906508fcfa61d000000d40eca1f613d32500fac00000004d88ef439ed2332f894135a8126c28d8263395855008309bc31694a244494293aac00005a4d3d00005f24d000004598c551b64634302c000160c3b353a0000296d62d3a8c9ba000000006f87520abd4f637508b500015192b9482300008c24c70000006c5bb22d0e2600004ec000140501402112854aa62dd132210e968b4f8c6d1347129701a4a544298d0b53d4c22369d4e943c02b500002810cb004a506c731454cd08328cb682b38cd71ff4fb14ea40003a7847f19040002e4ce8d000010f16988ce3d5560e29284fc00000000cb80b2590c0005a64ce34ac87eb2e0066316e94b50000b6117d4ae70e440000001388528129055553740000b2403740004418c02444108034f02654e8c93b00010a227580003cc4f2d31893dc02ad1e645a4fa51d74b70278d5082dfcb84027134c4e1c5910d4422638783a80d612375894bb94ef08f500012c6000133b387000005680003d8cf99105c0f44454c4a000093c2c7898805ec00057640db53cd2f01ef53d6492955928711f744d0d4c17c00f01448000169503a53680005a9871c0804bde3028443530c0000a88aa51bec63f51940af260cc11373837219d8c1725993fd36547e411b8c610000000000000048c145a00000001f2c27d2e8400025300002054f503d1800008140863f2d5c4098949e3ec0bab41495ca077101500001ab4c600cc0000620525d5ae09dc0004da4000557d65d359c000000080a56d80000000000000000000000000de800000000003ffd6b60000f7b198905910010da27e55f84560a7400003f11cdcdf20000b313e18abc24c142237350bc20d8000056000000005c2202ccd500000000410b5629b0fa257f44d705cc00054cc1a900000002f6c00037800000000e8300000000bb530f00147e92ded02858449603fb05d04b4c99a0f74a144ea83ac47240001b0c2f904fd0b5000090549d0a83297027f1d2cb9a00001fd59c51633f355a9000134557611720130bed00000003e9062c595c0001de8b4d569541003248080db802d15a049a54e405359e485b39680000000a09570000024a13020000da90000000000047738b50e2000068700002c62df08ff1ecc5e526ed3720000379000430600009fe11c46bb58f4000565000058114df00016312c2968300015a11968450425800003b4c271060378460948352f400046295011174f0021c4f855a7842f58c8a6440747744df168c01a05ac3
  | 40 => 0x1db82fa598d4743f2903718687c50880e0d000108800000ae4788e2809285111118c4944809f7000167d48c80000000eb31cb81d407b8366000167a1ded30406d000027502c1462c42b000148417541781c2802f1424b284d447362088f9c0c00e0b0b2ccf30c6954f37651443d155a00d686d32d4400032ecf5203a4b8f0000461380d1574b0d61053f429c08d86b500013e2336482f4160f7a19b853a48304fe3e6c94e28ec03b433c23e000092947e431b588cdf639e84211f488d3453957c00002713214bac04481214a983ca14ec028139cdba4b283da000078a1e84cec23656694468db30000a6a43b400000016a74900e3606a80000001670109c6b400014fc00008d528c16562434df03474902159c1a73f411f04130000000000000000000ef4b8b0000cc62e0cf5747b00510d80d79000138a4ba42c30000000363400000012ec489d02d0000000503c0003d2c00049f500a20e098f00004a400000003104000151cb0e17f40301c2c0000000000000000040f8bfb16e09870e7869912fc3694a6d009281472d1f809310000be400009d94d28a1d0000000000071b51654b42b880b6272d6823ed03cc2f382d105310f830415d7387c5172f04133586512c14ad2a741fc5993adc303138c17a254c03c0b407e32dbc5824f05187515c532284c790523804502ecf8f162557f24643e04c44000000000000012b11e606e22b8000007bc0000e307860b0147f4c785fb29c158b4f412200ae845e17bc4c646b400042840005370397000106420650551fb08b64a88a2d1fccf5c000000000010060000efe2f5400030b954b33381f04bd4c7d10413123160e292780000324c4a735352eb49f0b4900013fc22e800019840001fd110f000007b191961d449c00030e4000264c0002ae43f2171d5871f400000000f374a180003a2800000000004d4000058c0b0415c437d0018d530e9d26127480000000000000115d00000002d3080707e80933210000000121a1b54d8c3b186ee000103900016b504f80002bc55ab33a000048492a927e14e71df12210f94ce4051919800013c356794440810d2800000003fed1c4000158f42708f300009e527a506b05c8f931a04d9035a9634464893532e003f1de08e24eb0c332d78a310c7cafa47f1013450c6771efc1e90ad88c52ecc9e71ae41530c3d32e04a53e81840bfa204535614181ff4f5165921dc50312142d504d51ca027417721642692b64cc93db495b128809a000000002fcf6700013f0000085100000000000afd00003c5000134f16a09971b05419000113a00000004c691080ac91dd0c3813239b493a4d608415889280082d0e3000033a57bd3e9310c68600003e653ad33452ccf3c37b000047bd2393fd88f144f14bb320d2bb13dc15b2c686232e40fce334c3eb4a8c00002a546322dc
  | 41 => 0x4f870000c2b0c2c8604ce000000011f13de45611c1c4de1d5d586444c00044fc85a0c590a03f254d025d12fa000114b363c0000ab89ab349d15600001ca000000047014ba47b83770000000166c0004bb91744fec612207c40d3669579208021b46808b9232d41c0d7857450c09775a613dd3c2126b3fd061b4fcc7de51448c6016c8ee27455bc05a801517e82592b4455226f473533a4080011cadb485ca9a20596af4ce54bc0fd05772b4866b1c112880a4940e295d6b40fa10b93fcc6f323f405c5a451b82a58a26035893f27d8cb401d054e27ec090000117555580000714341473d3700decd101dace741ed4dd0493807c399550c36c01711af49b009f92c247ad1e050c53681fd42a71e0420259bcc7222cc58e48f46a70e6957713ec3b14ccd68101047062bc11471994dc5000050d3b7cd6031c547520b8e3028f04e9129965542241f218951412f2c1641fc88872cbc154215918402e82e636085874e6028e288924d0a602aa1e341371948aab052d1c13ab099f303070d4d553154838f620f402a139b8a392ea558d203421f41e55dc13cc5d84e840cb5450294115cf3944450362e90e80390cdb504741a31a1423945a8f5b00756973370e4226d8c893bf53cf11c81251ea1295333504e40452521710e155628eba50cc2761104f5900d937b5960a721b28bc516d415c0339541056477256ed3432cf169c08e949f462514f3418b5731cc405319cb380d9538346505341bc8ead311d0c101494641c60f34539946e567d57329fca3e31c0581361cac739554b60634b815594cff2aa0353181876048887681e30a8c42a4b0f3120dee55b47e80ab076315685560bd400321b45df495c5b331514430948a823da95322a6d6ad59c876a432919516ac8cf14780fe58b0ffa0658ea8541076932c533f3190ab553c4291330568717d953d30e03af04b85244931061332cfc353606c852fc00000003ed0000f710a747ae26c48a12f8000000000003f04122343ccf700012540000000433453921846ce00015910ec05de00010672040522000116f55b828c23d800000000be496d6421d44ce20040f045664c92243d2b5000027226c82c533d0d0e41987fc5234000478c000352c000453000000006bc3d1d2f700006090aa544a3be8000000055d2be4f2c50e40000000ed8587800031310e91870a9944cc948351471023851df44080613e45689118077d247138200000003f3c00005412a824b800024881eb2a60bc82770c4d000138627084ee563942d00000000000a45263850212e00001b5cf251ef000030640000000eb914f429f23b4b2a073532f0000ad8269c00019d525904a86d43dd841e12e42740cf555837a8ec9560048e38754f71ae14680f7941820c947620112ba533008f30c90844ee47d61c5140c3e0c7d407f80004b5d092
  | 42 => 0x2f184be0000e8645445f70f3877e4e35461210d2bd2ab835b55e055b4850a1134c869b0000f545a205b0000111f12bc84401d83f300009f432bd6b34f7cb942ed8b880cf88d43d44bd952710ff1dbd46652a4b11289ca6b17f93a40000fd93f7c8f94de0f050000d2f58480001254000103116b51e0a2e578c9a526f800000013c2000017013d92190a2499057d4fe1000159830dd1fa52f92250034d85327d09a00000000000dc809140003914936000000021340003a800004e5485353552735074f562c2d4081b7024c46e961853352660000123372c95841dcece3488000402c11144c91d1048122400000003d281c1009c92c0e4874337fd4ec40ece9b1b1031320e4b103df929f00015df22251391350d30383146d43f948f4670d9c00000000794cdf50ec7f800006842be000018280000464c861f108e000000003f30e962d88ab6000034f2e6cad7547c0003f10ade1d20e8544f8771032969b07802864070bf00000961157886e47b4f302f989cf216006e57e56a135004ce2a74efc14040003fad0145aa886355080001d34000532c00035fce97163424700010fb0000da6329d64511e800000015091ced2fb00001d70630c51000012b4adc87c25040004a6800052b021827109473ecc3c050d508c41f14062848370000091659ac8640000c9e2aa53da24a910e15fd2c4422d67800000004cf93a54040ae6194c000329544b06b017531142b74ffc22d3a948e757dd2e71861363440513840c8bd420cc1b300a56b900012b83b1c5632358000332962b328428f1748000499d1460000000116959b3cc849c0000e080000ced3950242150c6e300000000e7d5a4364d0471e2457042bc5300000428465c000041cf21164832427f14f94b94ac552a825d4ce89f0237118815902c83a2c85f42b8b5050b803d1fec23d32b4eaa243096918c89a83c78a5f11ec07f286898c19e4f151e7d173175ce790ee8d9f435448000000004d4c20f4ca8eb500008eb3b10000105806f1bd1152000102c2cb53c627251a340fc6b159314fa59cc00000000002a3c000536cd5d25502070b7c95d4e487b735e0ee700000004b90f41548560318b879109bd60a4e14f102f84d54000126a04a01e1029d5f14b996415744000000014534f84894508eb60000e41000000002052d55ac0000280c7931d2426458004a82e455a2000078e141cc5e085c3862468000341095000000003cac0000048000087800050a00000000d0500000003c184483c740002a445950000a0802b521b22ec00045f0fdc41f92ad24d029641b12db1b780002f491cb130c70115241f617b800032fc96204d109740c506e307cb6e079c1991eec95104c473c49bc0000000f3b02e4000000000000014f05154e13417952e57380bc0000000000000019d00002ab013c33a8d46317
  | 43 => 0x495e40000572146c00055bc000570417d0aaca2414509750fec0000000647000156c3c689492a84d5846d87c94820d721a289d3012115b0c8000000000ef00000000ad059c3238d7309b460844d43632294e532a0155e0000a7539a938936e00004ca47f700009c64c6d22a50105b2000096532f9576355c29a38615db06087ea076c38e29e0f8136c85691ba4a1644c473e3660a0441d8e334578d652aec148534c6fe287d39d4a1cd0144847cd116051a3d0102357f1531237c1d9565d0443a7009b2c5c53e2bdd3d53b3d1f50028ca601c0cd82f6805d3ef03a10e645dd0cfd0e658994ce2bccc1e00089aa12286071401640408874249189c700011a1142c8bc51f026c00000004b6808537e0ad622900001ec5427482565b393102050c955a05794b034a400029dcf2a0788ebd54e0980307032b0f9c1bd59793f100010d700000002a346be000137d27a864d111007e36bc00037e40c454fc3c14dc550a058d63351cc000259c03a30c4cb512092180a780002310000053866018d4000572c4f242645e42c3026120fc6ac522c6fa155088f11154a3541513627b520406c8c344c2467c231c0004490fe939cc7ba49440003a10000000052d0000d8009447562bd472f000167f38142731f68dca12a8f95426017c00011d415bc0004ec80d721987a307cd28e19cc6f809e46a829a56442d60b3229949b539d94ab0bb085740580e032c8b6a00d49271e5c558273416b1460eef3f2023c369497610716954600e9937bcc7b44a95d51c543713bccfee39e0110005089f193000006689e6247d4563d84842498064f42a920315b03ee58d499439ac6ea000096e00005210a2d1680000000152c0223e48e460d2c5cd3828e591ca87191cd13c8067142f0000dc954ed6290f4858f0000a851ec011c11cce3e0000c23400c4130c511ea56708a30000ee114cc2d2389006600014e51e214920000c7a1a90f0c532560c2fb8f170934455540079b000136d0d490b7242c54c000045f1c0cac8286cff11bf0828000113d1ddce9a268099d3850f8005591b70edc00040ac2c2074827b16fc6c956151a559b8ef9377800000000004a700001d1cc04103cc6d482887d2e8c0000e9865f59512bf16d10ec2fe0b451808f2635dcd1e3f9ca731b945412db400013bc000022048d00014dd00011e1000061f08940000000d97042cea943d151555344db00006e4000157045dc000481400004e02494c594893c4800014dce9522b0b9944942872d548e552a15ba11bc3e42670203000000048fd1b139c509f4e04e571f944040d915ed0000bc24818000000000000013fa32dcbff0348a0229210c03e280003bdc43c0288c6636500000000bc74aa82da1e0d1221ef906a2c8445200013d951807aa0000b3a4a3c8d0093c16c033c5f300015303618e72064930
  | 44 => 0x5906440000000000000061d240000032cc00013e4000000103c00011bf58180001ae8e4457b10f538f0f844e414c02c346381d38d6b29e543e46acb27076908a0ff4e2e007806522344bb3ac44fd1e1ccda15e93285138d25044c7ac4f6132b000122b4cc0722000154933e466807dc4d04f4868921e463c37f00000404bfc0000de549e09d7391c15d3384a67136536458fd1c80000aef07452f9121c342464493319249ae5328b631a580000e0d4ea1b3d584442c90a0000593331079d0d848291cfcad30bdc998352950651f4de4373c0000ed000000009780890b7937d4000000121003f421a2fd489d1eac000526cf3f184d02a597c65c00005513678cd4000140718895ad0af019d3e8400016c439010d085d0fe0d7629e915000000000ca036f000000000014885a342bf0dfca382df5283487c7ad47e05a119c9426318c68f1b610f14ebc31d31f000000003260000000000164e0accae4000034c000133d02555b2000062838d4cac5940aa720393d1000093d113c0001d88c5737ec658000135c51e88013bd8767413d5243f1c614386c898473439b3674b4041707272ae8aea199d0b8000000050e01c41cccd6d0000a3f26b12023abc16d02cc7390000c91213d024447899108640003b6433938e11c34d74a9418f884e034d00130b48375884984126c13a34dc2be1d55313492c8c0529cc0639850bb000057824180004664000000000000005a734ec000000000000000005ae15260bcc5e0000160100012d119fcfd645c1000225101f00013c40000eec51f90b13af06ad0d892760cb40005a38add161936a1508bd600000004009046000156716f901e49693ee43a00004a083d80dac9af467c00053bd5d6531165300006d6000052655f8b06078d04d189d5540a0d66d1598df406dc10636e54b7538c14922092c82e80dd30c1488e00006a90c082101978c9b132800040c009601e00000000000211800034e929257e80004d511e900000004064000482ce4f1e2d1b243f136f00000002e249b700006170000f8208e13f41f3cd1f545c00000005a20ec87d14a4c00018a82b119ec23033c8ea13ac821c0a341621e981df3824d3455f45c154446cc37dc00000000871b98a1e3a24000305842541c431755c811a0000cdd0000d7b000038f27600003770b353524bbd168ca0b3bd4f681bd44e111f47ee4af93f529f036d060c00007591454b2542c4de4aa2432506908a0000543cf6f128524334452290a4d525000068e514cf2925340000af48d75aed522040c6f900000000a9529e0000f48281d5bd3014bd13274e7e25e873814d51af424d4c85af4000000011b56e45ad1f286df22ac40345ed520466833424908da037800000010bf3558000403c8b014946a24b7cc98277cf2430d86044330e4e2e5871120e80130ff95aa36
  | 45 => 0xf5d0e058a12413c64000000132d0000000199925e4348b2303eceeb05052ea2f7556600000dc28dd27b517d0d13c7c90930747c2345d4420000dc131590e14b402ff4b054c10e614403cb8235141422f0000000548c00000016924cd49cc000056d3a4cf220c600002d38cfa0cc89811c90382019053c2b09082000000055d14173c804b3541c8ea1c8d50319745fc0000d6f35d45a957343a234000000000c3d171414a303480f1080d7a0618a8452311e800009c300a92d6051c2293d34cd243b809712d01d002f40000ba801917a459a00001670001017291cda20001307352000058e85c6560c7c757ed1d003954b20ed92794d846a149944e00000c9000013962d7450c0e2419752404830bf0000293cb0029240000000ab054a88b1088cacf2f9440b4edd22d3084cd6119d5ac000075c1e649eb464c00025c50d83d9400024102323e68dc613008c31a609bf2eb41cb2c1c664002c000521d3750090000276d25843ccbbe539000000015b845287dd309886843f43941bd8d5b32092af2eec27810b87f1383891239b01f10d15452475d231290c24e205c93e10094010c101360fa4cdb1130c01165031c3e5065b42f803842554cf35984ab32e8290184448c00016860000fef0001513000149d59852c72a24d2610eca0c0000ec80351094000084c5384c5f4010cf04ee8dae000000039a438b447540335695ea00000004f78fae000141510200000000fd225f4000000137e480091e46a80003b54000424472b000000019648210000d640000b7e4234bb742cd3cb4bd055f3d2400011e41600a2139c2bb0000000135f0aa04fa037c3964f84dbf06b52852978a0a27290b200d11ae053c00000000003eac7dc2fd830d2dd85c33dc0efb0000f6b177008d4cdceee502851f4efc01c0490f14203054845009dd36dc00000000004b2c85e0000c8d13a8b9517000005659072001c0002c14aa01c48ded410000038040000b1cec1000000000013603f5c25b00015b400014ad2b3122e0c880000000b8210b4e2224c967c000000000011170b344b11a08eae1e8163c0f6c1ae55c415f3e380002d10a81151147244c13f84870af2000167e331c55c2d4cc6a2cac00054680003fc96ba3af93764c152261e54e2355700d01ad8fd5377c986212903527b0cf11c38323403871a45fd66242404971a808e64a102460368f963000b22592d1d92ad09204ea09e440d01951024c0f29ecfb63c28e9110c8e520f2d52716f035600009554db84153054d39248c2064d6cb4340cc00051600000a6c0000000b1617293320001306217038500007640ee1617573c6cd000006000000002fe4cc500000003f995e10f8441100000002acc2e80000aa4314d5ee4a941f41db0000379d25f45351b9306d10007ec8bf139000000015920000270000000007547
  | 46 => 0xbae00000002b344da240d2f855483c725f0b2c23755280230b1b200d0c80bd87660000d99409c0a35768ac6479c000587c3d6000052a24952d218e8da803149f50a140004f808ad10884ed47cc7fa3b480000000eea51dca0e36380000b8d2f3492510353b96bc0f8d41445d8bcc00005ce01642584b3d0c70f24f8d14704f0031d5dd4e4504225a105d2ba012d432d03d4e807d91b6800000003350dd42b94e880002014dc7452538b3c0cd7c48b08625024000131c000000019338010412e8858c21d148a34c4c794e10e210c1cb010000921430c10a074c57b50dce5820c4de3312c86517a887f1898edb2c249424274bb13e811962244b75397835c59ec9434c992533c2c7a40db14a611b4456202469f0e90299265400046d0510015c4010d655b75308da42cb91dc167d61642b4b4815cd5d00824fe82c54ec02dac18a0954e2b4730ee22d480ac32510bd0bc005f4e502e53d3ce9f0000000000019e0000b3e000000001380000cf0000134800000000001a34fe52f253473ce86423d10e751d053f71724e643510765000104957182413c440000cd81840ed402c4a8151c2968e3f000004f00006930000dad406c0000ea51be35a487a06501c82cdd0483de00000100fb226a50f200000001b8012c0cc0f0e32892b934911483540266000000034b94210000f35000058037600004554eb45aa0dc33f4d26e27b875f000010812b52714ddcaeb134c4c825640000c0452e49a43c2133c2f20b88e680000aed0000f69029877956550210010000437c7f60b70000017840700005ec0bd02371e9d23a00016a23f80000353c000589143c4c940002ea0d6304500000000ba62a7c5f1294c50f2efc34e2fd112f568d39b5034a2b0eb470c1b088704c9c4c95a944244614a2320d08a82b8cc5b53806ec01e49b30001190183000049c094400008ae4f3045453ec44700005db000110a471c00020a800012c8009000067800002eb0000000275567723c80000000bca3230f3e0080000000000035b8311252cee40000d2a0000000409866c45e9680460550b00010a800000000000a970da8b190f7cdd252c4cab2ee0000000000043408862bd093855ec2ef499065749b5609509527f567495235c4fb54bbd4710e703254d986b3000043d106c00028c8d122a40cc003602fd4d480213ca14b810480f6570c60d47d86334c40d1408cc1171b188f74590ccc0ea924256694201f846db31bc00005e492600001fc5814f5a48f0f9e10d905112d920d03f004400011a4000031e3460dc2558c067551905059201bb41580000a0000036ec0002ba461658e4f9059242671f9c47c1c0127e0fd400042d07f0245153e35c00004eac75401c838d3fe400000000000eac00000000004e9d6271854ac00000e0f1b4000000011a20000000000000032f421d0
  | 47 => 0x2d2810903fd27a362c575288125555a1493030800010512bc3ddcb9d2948df300012ed0548fd800003953588a62150000044140001f30c6e388000059a02144f1c0004b714f816dc4cd2ce406b58695472954a2840e139a3d9096c09d40004f6c08b56306af11f8ae13e30c3f0000d881f982d6396c3760f1800c0414ecd000009e30a51651768899581c95741b44cb44b517826647b4272050e33b85f451500004d102444ba144824b40005188c8b2dc87c30354c4f4fb4faf49885604f9d1b534fcfb92c60000000000000000b4000000053fd107368c0583c1cac930b0dda51356644d64d364ab947009a067d3f4507a5621236124833308a8a76097946b2d94dac09e85c82e9cb6c3db10c4371094f4874901498cc6524403d31cb15623a6097b17882432cec99e15b882601191231a7909b29f8bd3330d48244acbba31fc0d94b80cfe2ec886a5aac52329613b03ee08db365806d485407a4278f2f07d44934bc43a030680f90f5077f2fdc72831d4b1408594670438abf32049da5854d09201847003906514d5cd91550d3f90b100000b780004cd875800440002ed4fe448790d63a50f4e36ad01a3ae10ac3e9c000000097243a8bdc4fa80e1410c1bf4f9916121d400036114950000aee0c30fde46f46440001211341cd812ec00001518eda45b061952840000000e5f28ccd4321514f200c925d08b09f1291059d5ac854f19bc9f30000000430800046186ab345456a3628c604a641183d3164a1c255e8137049932e496459a84bc2e1d1091fb406a2cd847521240555358de939355e021404dd5069277096816f3cf463d17a06ff0cbc06322c84a94b78adf073d15c222044d012c4d80000000000000000011712d9003915340005835272262d24f599400050900004e7c4762cc13210e1c4f4305104517847c00ee462f000000000009b43fb412f5730d891c7c6914cc4f0d2fcd0073b753b61d7947b3c9d24707184633ccd1541564683560878400000005174de81b742272d70b6905a0ce600013ec38a8717020c00034b11e4043000052048c108380000000f183b5c2220c20ff028051f419c00e62228d5500003d10000ea62a204593dcd4861d68e702ac82e747145cb03e038426140565a8c7533b8154e415065629bcd5e180cde6008d69a07e444900003401dc15104aad34b0fb0f0932a80000d1c0001cc113b56f8c251c990530000140599950234e04f83fe0bef2c9800839806c523a4992095818b321cdbc4b652ac4e394fe564131934acb5f47484c20fbd44f20f916e2689393013489a556c0002a2cd5f2518e402fa54490000aa3000000049a0b673f743be38b130d32f0e343a88f380000daa1bc4000000133c16d911c128d5f63cd879200011a92e9523b5078000092c000488d0d915f8c460c294ed1d8416611d162a0000
  | 48 => 0xc79e0bc54c60001367176553600004981cf506f03ad0e74c90ac15ab00000000000354498a534488b1fbd2481a9522832283ff053549118dc73a112934954b086f4a604864eb471e294411e59b0650283d16d43e443e304c00020d4c2a3f0952d0b510a4268d65215943123b951b33e24b8a4c386fd5170a2a2fa92a1502cd590000e25378800000596c039fc0b128d00e75378bf20001308000005451bc00012dc0003b591ce00000003290000073014218ac32a22888be44501c71ee035737e9063000042613891c64d38eed266c0004b3489b31645a030f836820005ae0f0c00031dd216000059e257c92b1c3c10d29380f128bc9565520f7d0001057397504a497143d00001e632541de31acde131e03e2360d1db5500a6e4bf094538f46b2072505b55846bf2e5c8a648bc65510c40004464ca911083dc4f150ba29c515a4eecce53aecda106e4e323b50e9200006b041a02cf25283bb20ec5382280e4a0000ed115e466d0f2000000010d302946b700011793ea151d34288f416a8319292d0dc24dc7ce52008550000cc22ac42db23bc00044106314c28a7d57c046527780003a7449e00003bc00000000000db12af8000313800055143a300011c230d418038451835a3cb1f57fcfea00000004eb9550018941200008830000b92000000050fc8cd1d3c7080d0c00019a8000094c4d11e1502e0bf80004350000047c0000000fbd56cc8af32008e434b489226e02950f5528a1394f60073891712580ee3ba40c62c942344fc85eb1e500a4192c1a1560491b3c0964f5a14f0f4b315511bbc9b9339cbd710fc0000d2833713100004b3900500006454f340002cfd0b641cc03121cc25f366c221000040e209c8de398cb085aa538f1f6c89e4e5d647244474a179c8805214af60d3400000dcc3c069044053508781d4046c38e82084ef916218e4000000013b0b744ac34680002bf82ad027ce0613144ff1d6d4a434352500b5ca950c9cb1c005cf5f4d94d213a9cb780000a4c30eccd12b54c2f4ed41ec00000001190a350000000000000027c819f2569637045919e244d4c704549790000d204a50b5b1e9460500000001d1883d481cf9f418879a000000042943cf00000002b2d25621ec00001c40001aa90e54c7ca2c2349289000087601dc33100010c6000000006c56a40000e5c38bd45e4768000446d53a0d9d5a834302e01b48ffe3eece3b375c000000169300012b62ea802e00008b810dca4603c881b54343fa57081880c405ff0001447000008e380800000000000b640000e04a87420d46c06151d31e58000028444b2f9c00022a45084fd800055d538c00011de0e28000010809900000005720a000f354d723ed5b04b50ac42050b0208ec7e24c5c22e25c084518a4e6259442a046a0ceb125053f58812e32fa0e6756c4c882704e77
  | 49 => 0x192160b3dd541f58500003c4c0000000b340000000000136b00000004cb00f70ac016139987451e080003f8c00012b84ba241c1270208f4342c12b3051000f00011bc33d86f050594a51d314c514bc3ae1ffd17e23e0dd6476000010e47320000d611f200e21f1913737f4a250f6535a325ca3d25ac6214e64d1918d82132e1904b579563b0cec1d813ac54a4a74db638488471068ad4281819800001870000cb02cc
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf3152dd11004001f2665ba22008003e44cb744401000578c34e88802037b72859d110040016e30b3a22008002eca127444010005e941ce88802000bd1839d1100406b7c5053a22008002f860a744401000579c32e88802000b73855d1100406f6e10aba22008002f4e0d7444010005e841ae88802000be3825d1100406b7c104ba22008002eca1c7444010006d9438e88802000db3761d11004001d66ec3a22008003ccdd47444010007983a8e88802000f32651d11004001e62ca3a22008002ece087444010005d8c10e88802000fa0721d11004001d66c43a22008003ac588744401000799a90e88802000f31521d11004001f26643a22008003e44c87444010004f943ec88802037b7285d9110040016e30bb2220080027ca1c64440101bdb9428c88802000b71851911004001d62c83222008002f4a0c6444010005e8c18c88802035be28219110040017c304322200800374ddb734401000769bb6e68802000f5375dcd1004001ea0ebb9a2008003d49977344010007a8b2ee68802000f9374dcd1004001f20e9b9a2008002f4e0b7344010005e8c16e68802000fc072dcd1004001da6c5b9a2008003b458b7344010007a9a96e68802000f5152dcd1004001f2685b9a2008003e450b734401000578c34e68802037b72859cd10040016e30b39a2008002eca127344010005d8c24e68802000bd2839cd100406b7c50539a2008002f860a734401000579c32e68802000b73855cd100406f6e10ab9a2008002ece117344010005d8422e68802000be3825cd100406b7c104b9a2008002f4a1c7344010006e9438e68802000dd3761cd1004001da6ec39a2008003d4dd47344010007a83a8e68802000f52651cd1004001ea2ca39a2008003e4dd07344010007c83a0e68802000bd3821cd10040017a30439a2008003f01c8734401000769b10e68802000ed1621cd1004001ea6a439a2008003d45487344010007c9a10e68802000f91421cd10040013e50fb1a20080dedca176344010005b8c2ec688020009f28718d100406f6e50a31a2008002dc6146344010005d9420c68802000bb18418d1004001da2c631a20080d6f8a086344010005f0c10c68802000af38650d10040015e10ca1a2008002dce1543440101bdb842a868802000af28610d10040015e30c21a20080dedca144344010005b8c28868802000f914310d100406b7c50421a2008002f860843440101adf143ee48802035de287dc91004001dc70db9220080d7b821b7244010006f1bb6e48802000ee376dc91004001ec70bb922008003d82177244010007b1baee48802000f6075dc91004001ec4cbb922008003d85977244010007d1c26e48802000fa084dc91004001f46e9b922008003e81d37244010007e1c1ee48802000fc083dc91004001f86e7b922008003f01cf7244010
  | 1 => 0xacbb9220080db7844372440100063b32eec8802000c7475dd910040019c8e5bb220080031de1776440100063a42eec8802000c7752dd910040018eaa5bb220080032dd0b76440100065aa16ec8802000cd732dd910040019aa65bb220080033c943764401000678a86ec8802000c7776dd510040018eeecb2a20080032dddb74440100065bbb0e88802000cd776dcd10040019aeec39a2008003711c8734401000673bb6e48802037b7285d0110040016e30ba0220080dedca164044010005b8c2c808802000b73854c1100406f6e10a9822008002ece113044010005d8422608802037b72850c110040016e30a18220080031e99776440100063c3aeec8802000ce872dd910040018f70bbb220080031e21776440100063da96ec8802000c7952dd9100400197685bb220080032e50b76440100066d996ec8802000cd932dd910040019e4a3bb220080033c54776440100063dbb6ea8802000c7b765951004001976edba220080032edd87444010006d4390e88802000cdb76dcd10040019b6ec39a20080033addb7244010005b9c2a828802037b708550510040017a706a0a2008002f420d41440101bdb9428828802000b7185105100406f6e50b98a2008002dc61731440101bdb942c628802000b71858c5100406f6e10bbb220080035c1d776440100073932eec8802000de072dd910040019e30dbb220080035ce177644010006b842eec8802000cf365dd91004001ae4cbbb220080033c5977644010006b9a96ec8802000d7152dd91004001b6685bb220080036c50b7644010006e9996ec8802000dd132dd9100406b5e50fbb220080033ca1f764401000739c2eec8802000e7085dd910040019e6ebbb220080033c5d77644010007383aeec8802000af382dd910040015e305bb22008003b81cb764401000739a96ec8802000e7152dd91004001d6685bb22008003ac50b764401000769996ec8802000ed132dd9100406f6e50fbaa20080df5ca1f75440101c5b8c36ea8802000d7376dd51004001ce6edbaa20080031cddb7544010005b9c16ea8802000b7182dd51004001ec0e5baa20080039cd8b754401000738b16ea8802000f3342dd51004001e6285baa2008003d4ccb7544010007a8996ea8802000b7287595100406f6e10eb2a20080dedce1965440101c739c32ca8802000d73765951004001ce6ecb2a20080031cdd96544010005b9c12ca8802000b71825951004001ec0e4b2a20080039cd89654401000738b12ca8802000f33425951004001e6284b2a2008003d4cc96544010007a8992ca8802000db376dd11004001d66edba22008003ccdd77444010007983aee88802000f3265dd11004001e62cbba22008002ece0b7444010005d8c16e88802000fa072dd11004001d66c5ba22008003ac58b744401000799a96e88802000
  | 2 => 0xd3258c1000667b9264b182000e8d424c963040015a902992c60800a1fe197518c100043ec3cca3182000c6e7299463040010ff0eb28c6080031b9c96518c100061f32ce83182000c3d659d0630400187ccaba0c6080030f5957418c1003e4f31ae831820008df8758c630400193ae8b18c6080031b9957218c1000636b2ae43182007cce635c8630400199ac6b90c60800a1fa1676d0c100043ec2ceda1820078be849db43040050fd0b3b486080021f6167690c1003c6f41ced218200287c85dd943040050fd0b3b286080021f6167650c100047b40ceca1820008fa809d943040010ff0abb2860800a1f2157650c100143f428eca18200087d851d943040031dd043b286080023b6087650c100043ec36eaa18200087e8759543040010f90eb2a860801e2f21d6450c1003d4e41ac8a1820088dc8758d430401153908b1a860800a1fa167610c100043ec2cec218200287e855d843040010ff0cba886080021fe1d6510c100043ec3aca2182000c6e72594430400f93eeca188608003275d94310c105170f32a862182000e1d6550c43040018dccab9086080031b5957210c10006c6a1ae42182000c79659c24104001972c938482080031e59570904100143e42eeca08202987d86dd541040010fd0eb2a82080121f21d65504100062f32ee6a082000c5d65dcd41040018bcca39a82080031759473504100143f42aec208200087f865d441040010ff0eb2882080021f61d65104100143f42aed988202487f865d731040090ff0eb2e62080021f61d65cc4100143f42eed188200087d85dda310401117d09bb462080022f613768c4100043fc32eb18820a887f87596310412d0fb0eb2c62080033658e708c4100063cb2ce01882000c79655c031040050fd0abb680080721fe1975d00100243fc3acba00200087d8759740040050fd0bbb480080021f617769001003c6f41eed20020008dd83dda40040010ff0cbac800829e1fe1d65900103fc3ec3acb2002000cb5649c640040050fd0b3b080080021f61676100100063ab2ce22002000c75655c440040018eacb38c60080033558e718c0100063ab2ae3180200287c85dd930040230fb0dbaa60080021fa1d654c0100243e43aca9802000c3e65dd1300400187acbba260080030f994744c0100061eb28e8980200287e859d830040010fb0b3b0600800a1fa15760c0100043fc32ea180200087f8759430040010fb0eb2860080063d61a710c0100263cbb2cb0802000e716598610040050f90bbb2200802a1f61b75440101c6b8886ea880200087e8759510040090f90eb2a20080031b1c965440101bf38082ca8802000c3e65dd1100400187acbba220080030f99474440100061eb28e88802000c5e65dcd10040018bacbb9a20080031799473440100062eb28e68802000c6e65dc910040018d
  | 3 => 0x4b28200087e8710965040010fb0e212ca082be8fa1042594100052f41884b282000a5d8310965040018bee5992ca08003175cb32594100070fa1664b282000e1d42cc965040010fd0f192ca080021f61e32594100051f42464b282000a3d848c9650415d4bb07192ca080038b50a325941000716a1264b282000a77814c965040014e902992ca0800393e0932594100062fb9264b282000c5d724c96504001c3e84992ca080039390932594100070ea1264b282000e4d424c96504001c1a84992ca0800395e0532594100072a40a64b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b2820ada5e830c965040714f30138aca080121fa1f21594100043ec3e42b282000a3e84c85650400147b0990aca0800297a0f21594100052ec1e42b28200087e8708565040010fb0e10aca080028fa1021594100051ec2042b282000a5e8308565040014bb0610aca080029ea0021594100053cc0042b282038a75819c165040090fd0f902ca080021f61f20594100051f42640b282000a3d84c8165040014bd07902ca080029760f20594100043f43840b28200087d87081650400147d08102ca080028f61020594100052f41840b282000a5d8308165040014ed02102ca080029d60420594100043fc12ebb20200287e85dcb64040010fb0bb96c80800a1fe1f52d90100043ec3ea5b20200087f8754b64040010fb0ea96c8082b30f9d742d90100061ebae85b2020018bf8750b640415787ceaa16c8080030f5d542d901000e5739285b202000cad7250b64041558bceb996c808003175d732d901054e2f3aa65b202000c5d754cb640400399ce4996c808003335c932d901000746a1265b202000c79759c364040011bf06baac80801e3720d755901000c5e426e4b2020008f8805c964040031790ea12c8080032bdc942590100055c40284b202001cce724c9640400199ae4992c808003a350932590100043ec3cca3202000c6e7299464040010ff0eb28c8080031b9c965190100045fc3ac83202000c5e659cc64040018bacb398c8080031799573190100062eb2ae63202008c9e645cc640400193ac8b98c8080031b995721901000636b2ae43202008cae645c8640400195ac8b90c8080021fe0975d8c100143f42ee5b18200087d85dcb63040050ff0fa96c6080021f61f52d8c100043fc3aa5b18200087d8754b630415987ceba16c6080030f5d742d8c1055e1f3aa85b182000c3d7550b630400395ce4a16c6080032b5c942d8c105562f3ae65b182000c5d75ccb63040031bf0e996c6082a7179d532d8c100062ebaa65b182001cce724cb630400199ae4996c608003a350932d8c100063abace3b1820008bf845d5630401117908baac6080063720f7258c100047a40ae4b182001cae72509630400195ae4a12c6080063721
  | 4 => 0x4400187aebb248088003179d763901100062ebaec72022000c5e7518e40440018baea31c80880031b9d7629011000636baec5202200087f855d940440050f90abb2808800237e0d765011003c6e41aeca0220008ef825d940440031d904bb280880032dd9071501100455c43280202205fea862500404400176102a00808801f3518e71cc1100043fc2aec982200287c855d9304400117f08bb260880222f211764c11000477c12ec98220018ec825d930440010fd0dbaa60881571718f754c11000636316ea98220b187e87d9530440ab0f90fb2a60880022fa1b744c1100061fb2ee89822000c3c65dd130440a9938c7ba260880032b18b744c1100045f430e89822000c3f651d13044001878ca3a2608814f2718c744c11000656310e898220538be87d9130440a91790fb2260880030fdd7644c1100061e3aec898220548be8719130440111790e32260880030fdd4644c1100061e3a8c89822000c5f75d8d30440018b8ebb1a608800327dd3634c1100064e3a6c69822000c6f75d8930440018d8ebb1260880032bdd3624c110006563a6c49822000ce462dc530440019aec638a608800339188714c1100143e42cec182200e87c865d4304400f8b8c6ba860880031b189750c1100043fc3eca182200a87d87d94304400187cebb2060880030f5d7640c1100061f3a8c81822000c3d7519030440018bcebb186088003175d7630c110006373aec41822000c6d75d88304400f5b10c9806088123b2189300c110005e840a601822000ea86219310440158ecedb2c20880032d9db64841100465b3b0c90822000cd676d8e104400f9acec31c2088003b1188638411004e733b6c50822000e7365d8210440010ff0cb92ca080021fa1f62594100243f43cc4b282000a3e84989650400147b09312ca0800297a0e62594100052ec1cc4b282000c6f7298965040050fd0eb12ca080031bdc962594100043f438c4b282000a3e84189650400147b08312ca0800297a0c62594100052ec18c4b2820acc3f76d09650415787eeca12ca080038b989425941000716b1284b2820aac5f76cc965041538beec992ca0800393989325941000726b1264b282000f0d424c9650400187ee93a2ca0800297e0d74594100052e41ae8b282000c5f739cd650400147f08b9aca080028f21173594100043ec3ce4b282000a3e849c9650400147b09392ca0800297a0e72594100052ec1ce4b282000c6f825c965040010fd0e392ca080028fa1072594100051ec20e4b282000a5e831c965040014bb06392ca080030fdcb42594100061eb9684b28200087e8790965040010fb0f212ca082c28f61242594100052f41c84b282000a5d8390965040014f700a12ca080029e201425941000717c1284b282000c3f72509650400187ae4a12ca080038ee0142594100071c4028
  | 5 => 0x80029b61673d891000557424e7b122000aad849cf624400159d0739ec4880029be1573d89100053642ae7b122000aaf845cf624400155908b9ec4880032bdd173d891000567438e7b122000cce871cf6244001c9eea39ec488003931d473d891000747ba0e7b122000e8c741cf6244001c9ea729ec4880029be1543d89100053642a87b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b122000e8d4310f624406b5d501b8ec488002b3a0f51d891000566c1ea3b122000e6751947624406b5cd03b86c488002aba1350d891000556c26a1b122008cb8649c341440010fd0dbaa82882770f193755051000636316eaa0a20b287e87d95414413b0f90fb2a82880030fdd764505100061e3aec8a0a20008de86dcd41440018becbb9a82880031719773505100064fb26e6a0a204fc9c64dcd4144001998c5b9a828800237a1873505100062fb28e6a0a2000c5c651cd414400193ec839a828816f27190735051000666310e6a0a205b8de87d8d414409f1b90fb1a828800317dd763505100062e3aec6a0a204f8de8718d414400f1b90e31a828800317dd463505100062e3a8c6a0a2000c6f75d8941440018d8ebb12828800333dcf62505100066639ec4a0a2000ce862dc14144001976c838282880033a18870505100143e42cec20a202687c865d44144011878c8ba882880031b18975105100043fc3eca20a200a87d87d94414400187cebb2082880030f5d764105100062f3aec620a2000c5d75d8c41440018bcea3188288003175d46310510006373aec420a2000c6d75d8841440115690ca0882880038dd9541105104bf523128220a2000bb08050441440050f90b3b662880021f21975cc51003e2e31aeb98a2000c6c625d731440010ff0fb2e62880021f61f65cc5100061f3aec998a2000c3d75d93314400187cea32662880030f5d464cc5100062f3aec798a2000c5d75d8f31440018dcebb1662880031b5d762cc51003e6c31ce198a200287c859da31440450f90cbac628825b1718d758c51000636312eb18a200087f87d9631440150fb0fb2c62880030f9d7648c5100061ebaec918a2000c3e75192314400187aea3246288003179d7638c5100062ebaec718a2000c6e75d8a31440018daebb14628800336d8c704c51003d6a4326218a2000e57654c43144101d88c49886288002f4201310c5100143e42ceda02200087c865d74044011878c8bae80880031b18975d01100043fc3ecba02200087d87d97404400187cebb2680880030f5d764d01100062f3aec7a022000c5d75d8f40440018bcea31e8088003175d463d0110006373aec5a022000c6d75d8b4044011968c938e808800a1f21676901100d43e432eb202207fc3c645d640440018d8c4bac80880021fe1f65901100543ec3ecb2022000c3e75d924
  | 6 => 0x465a324e221a2007cd4639c4434400f1e90cb8886880027c2017110d100465c324e021a2007cd8639c0434400f1f10cb8086880027c2057010d1000537436ebb122000c6e76dd762440014dd0c3aec4880031b9d875d8910006373b6cbb1220008ed8799762440014dd0b32ec488002aba1265d891000556c24cbb122000ace83997624400159b0732ec4880023be1d65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000537430cbb122000c6e76197624400155d0dba6c4880032b9db74d891000717b2ee9b122000e2c65dd3624400155d0c3a6c4880032b9d874d891000717b28e9b122000e2c651d3624400195cedb26c4880038bd9764d89100071632ec9b122000e2f75d936244001c58ebb26c4880023b61e64d89100053742cc9b122000a6d85993624400155d09326c488002b3a0e64d891000566c1cc9b1220008ef8759362440014df0ab26c4880029b21564d891000567c1ac9b122000acc83593624400155d0c326c4880032b9d864d891000717b28c9b122000e2c651936244001c5eea326c4880038b1d464d891000567436e7b122000cce76dcf6244001c9ecbb9ec4880039319773d8910006c7ba6e7b122000e8f64dcf6244001d18c9b9ec488002b3a1873d8910006673b0e7b122000e4f651cf6244001c98ca39ec488003a3d9073d891000746320e7b122000cce76d8f6244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f6244001c9eebb1ec488003931d763d891000747ba6c7b122000e8c74d8f62440011db0f31ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec488002b3a0e63d891000477c3ac7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000ace8618f624400199cec31ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec48800393dd463d8910007263a8c7b122000e8f7418f6244001d18e831ec488026b9a1b71d89101adf1406e3b122009aea86dc3624406b7c503b86c4880029ba1675d891000557424ebb122000aad849d7624400159d073aec488002b360e75d891000557c22ebb122000aac845d7624400159f06baec488002b320d75d891000537438ebb122000c6e871d76244001c5eebba6c4880038b1d774d89100053742ce9b122000a6d859d3624400155d093a6c488002b3a0e74d891000566c1ce9b122000a6f855d362440014d90aba6c488002b3e0d74d89100056641ae9b122000aae871d3624400195d0e3a6c4880038bdd474d8910007163a8e9b122000e2f54953624400195ee9b9ec48800393dd773d8910007263aee7b122000ccf74dcf6244001d1ee9b9ec48800323dd373d891000666ba6e7b122000e8c74dcf62440014dd0b39ec48
  | 7 => 0xdd8790863440014bd0b210c688002976164218d105a54ec248431a2000ccd72908634400199ae4a10c688003a3e094218d105a64fb928431a20b4e8e72508634400193ae4a10c6882d3a35c94218d1000646b928431a2000e1f525086344001c3aa4a10c68801e37a1c4218d100046ec388431a2000a5e8510863440014bb0a210c6882cea7a104218d1003c6f43ea231a20008dd87d446344001caea3288c68801e37a1f2118d100046ec3e4231a2000a5e85c8463440014bb0b908c688002a7a132118d100054ec264231a20078de8708463440011bb0e108c68800297a142118d100052ec284231a2000a9e84084634400153b08108c688002b6a002118d100056cc004231a2000a9e84d40634400153b09a80c68801e37a1f2018d100046ec3e4031a2000a5e85c8063440014bb0b900c688002a7a132018d100054ec264031a2000ad78148063440015a902900c68801e37a1c2018d100046ec384031a2000a5e8508063440014bb0a100c688002a7a102018d100054ec204031a2000ad68108063440015ab02100c68800297e151018d100052e42a2031a2000a9f84440634400153908880c6880021fe1576d0d100143e42aeda1a20078bc845db43440011df04bb686880063b20976d0d100043fc2aed21a200287c855da434400f1b906bb486880023be097690d1000c76412ed21a200287e85dd943440010fb0bbb286880063ba0b7650d1000476c16eca1a200287e859d943440010fb0b3b286880021fe157650d100143e42aeca1a20008ef825d943440031d904bb2868800a1f2147650d100043f436eaa1a20a6c3c64dd5434414b8b8c7baa86880031b18b7550d100043f43ecaa1a200087c87d95434400f17d0fb2286880030fdd76450d100061e3aec8a1a2007a9e83d9143440111bd0fb1a868800317dd76350d100062e3aec6a1a2008a9e84d8d43440011ed0db8a86880033918b7150d10004f9406e2a1a2000cb7641c543440019aec638a8688003391887150d100047d436e0a1a2000ce862dc143440013e503b8286880032ed907050d100066db18e0a1a2000ce8621c143440050f90b3b086880063b20a7610d100043fc2aec21a200287c855d843440011df04bb086880063b2097610d100043e432ea21a2008c3c645d4434400f8b8c6ba886880031b1897510d100043fc3eca21a200087d87d9443440018dce5b2886880030f9d76410d100061ebaec821a2000cae72d9043440018bcebb188688003175d76310d1000667396c621a2000a9e8650c43440015390ca188688003279d94310d1003e4e3b28621a2000e1f6550c4344145c38caa188688287a31894310d1000476432e421a2000c6f655c843440018d8cab9086880032bd917210d1004656322e421a2000ccf635c8434400f998c6b9086880036350d7210d100
  | 8 => 0xe5b8ac68800237e1d6318d100052fc2ac631a2000a5c8558c634400153f08b18c688002a72116318d1000567c12c631a2000acc8258c63440011bb053b0c688003179db6518d100052ec16ca31a20008dd87994634400153d09328c688002a76126518d1000567414ca31a2000acd8299463440011bf0eb28c688002a7e116518d100054e422ca31a2000acf82594634400159904b28c688003179d86518d100052ec10ca31a2000c9e76d906344001c3ecbb20c688003871976418d100054ec16c831a20008dd8799063440014bd0b320c688002976166418d1000567414c831a2000acd8299063440011bf0eb20c68800297e156418d100052e42ac831a2000acf82590634400159904b20c688003279d86418d100070fb28c831a2000e1c65190634400153b04320c68800237a1b7218d100062fb2ee431a2000c5c65dc8634400193ec9b90c688003271937218d100062fb2ae431a2000c5c655c8634400193ec8b90c688003271917218d100046fc3ec431a2000ccd72d8863440011bb0f310c68800297a166218d100052ec2cc431a2000a9e84988634400153b09310c68800237e1d6218d100052fc2ac431a2000a5c85588634400153f08b10c688002a72116218d100046ec38c431a2000a5e8518863440014bb0a310c688002a7a106218d100054ec20c431a2000ccd721886344001c9eca310c688003931946218d1000747b20c431a2000e8c64188634400199b0e310c68800393a146218d1000726c28c431a2000e8e841886344001d1b08310c688003b16046218d1000764c00c431a2000a5e86d4863440014b90da90c688003179db5218d100070fb26a431a2000e1c64d486344001c9ec5a90c6880039318b5218d100052f432a431a2000a5c8654863440018bceca90c68800387d915218d100070e322a431a2000e4f625486344001c98c4a90c688002a7a1b4218d100054e4368431a2000c9e76d086344001c3ecba10c688003871974218d1000747b168431a2000e8c62d08634400153d0ca10c688002a72194218d100064f3b28431a2000e1f655086344001c38caa10c688003635c94218d1000747b128431a2000e8c6250863440015ad0d108c688003b118a2118d10007623124231a2000bd0804846344001d90c5100c688003f08862018d10007643124031a2000bd0814806344001c3ea92a0c68801e37e097218d1003e67c12e431a20b5c5f72d4863440018bae5a90c68801e37a1e5218d100046ec3ca431a20b6a5d85948634400153d09290c688002a76125218d1000727c12a431a20b6c5f7254863440018bae4a90c68801e37a1c5218d100046ec38a431a20b5a5e85148634400153d08290c688002a76105218d1059e4fb968431a2000c9d72d086344001c3ea5a10c6880038754b4218d1003c6f43c8431a20008
  | 9 => 0x20d8d100046ec3841b1a2000a5e8508363440014bb0a106c688002a7a1020d8d100054ec2041b1a2000ad68108363440015ab02106c68801f1718d7598d1000637396cb31a2000c6e72196634400187ecb3a4c6880030f1967498d1003e4e31ce931a2000c3f655d26344001878caba4c68801f2718d7498d100061f3aec931a2000c3d75d92634400195ce5b24c6880030f9d46498d100061eba8c931a2000cae7219263440018bcebb1cc688003175d76398d100064f3a6c731a2000c9d74d8e634400199ce5b1cc6880031bd957298d100063632ae531a2000caf645ca6344001958c8b94c68800333d8d7298d1003e6631ae531a2000c6e7518a63440018daea314c6880032b9d06298d1000656ba0c531a200287e86dd563440010fd0fb2ac6880031b1cb6558d100043f438cab1a2000c6c72195634400187ecbba2c6880030f1977458d100061fb28e8b1a2000c3c651d1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440031dd0db92c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880031bdd46258d10006363a8c4b1a2000caf741896344001958e8312c6880021f60b7558d100045fc22eab1a20088bc845d563440011bf06baac6880023be097558d1000c76412eab1a2000c3f75dd16344001878ebba2c6880022f60b7458d100061fba8e8b1a2000c3c751d163440018beebb9ac688003171d77358d100064fba6e6b1a2000c9c74dcd63440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc9634400199ee7b92c6880031be177258d100063642ee4b1a2000caf84dc9634400195909b92c68800333e0f7258d100043fc2ae4b1a200287c855c9634400117f08b92c6880222f2117258d100046fc1ae4b1a20008f7815c963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d100143e43ea4b1a2000c3f74d496344175878e9a92c6880031bdcb5258d1000e36396a4b1a200087e8754963440010f90ea92c6880030fdd15258d105ce1e3a2a4b1a2000c6f7254963440038d8e4a92c6880022fa1f4258d100445e43e84b1a2000c3f75d096344159878eba12c6880032bdcb4258d1000e5639684b1a20008be8750963440011790ea12c6880030fdd54258d1055e1e3aa84b1a2000caf725096344003958e4a12c68800237a1f3258d100062fbae64b1a20aac5c75cc9634400193ee9992c6882e3271d33258d1000667b9664b1a2001ccc72cc963440031b90e992c68800317dd53258d1054e2e3aa64b1a2000c9f744c9634416f938e8992c68800333dc93258d1000e6639264b1a2000e8d424c963440019c8
  | 10 => 0xb1a2000a5d8518b634400153d08316c688002a761062d8d1000666b90c5b1a2000e4f6518b6344001c98ca316c688003a3d9062d8d1000746320c5b1a2000ccd8718b6344001c9d0a316c6880039361462d8d1000747420c5b1a2000e8d8418b6344001d8b02316c688003b260062d8d100052f436a5b1a2000a5c86d4b6344001c3ec9a96c6880038719352d8d1000727b16a5b1a2000e4c62d4b63440014bd0ca96c6880029721952d8d100070fb22a5b1a2000e1c6454b6344001c9ec4a96c6880039318952d8d100054f43685b1a2000a9c86d0b6344001c3ecba16c6880038719742d8d1000747b1685b1a2000e8c62d0b634400153d0ca16c688002a721942d8d100070fb2a85b1a2000e1c6550b6344001b1ee4a16c688003a3d8942d8d100074631285b1a2000ec46288763440017a10090ec688003b218a20d8d10007e110c41b1a2000bd08148363440018baea3aec688002b5a0475d8d100056ac08ebb1a2000a5e85dd363440014bb0bba6c688002b560774d8d100056cc06e9b1a2000a5e859d363440014bb0b3a6c68800327dd274d8d1000567414e9b1a2000acd829d36344001c3ea92a6c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c68800333e0972d8d100052f428e5b1a2000a5d851cb634400153d08396c688002a761072d8d100056b408e5b1a2000ad5811cb63440015b500396c688002b660072d8d100062fb96a5b1a2000c5d72d4b63440011bd0f296c6880023761e52d8d100054f424a5b1a2000a9d8494b6344001c9f04a96c68800317dc952d8d100062eb92a5b1a20008de8714b63440011bb0e296c688002a7a1052d8d100054ec20a5b1a2000c9f72d0b634400193ae5a16c68800387d4b42d8d100070ea9685b1a20008de8790b63440011bb0f216c68800297a1642d8d100052ec2c85b1a2000ccf7290b634400199ee4a16c688003a3e0942d8d100064fb9285b1a2000e8f7250b634400191ee4a16c688003275c942d8d100074639285b1a2000e1f5250b6344001c3aa4a16c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c68800297e1571d8d100052e42ae3b1a20008de87d4763440011bb0fa8ec68800395d4651d8d100046f43e43b1a20008dd87c8763440014bd0b90ec6880029761721d8d100054f42643b1a2000a9d84c8763440011bd0e10ec6880023761c21d8d100052f42843b1a2000a5d85087634400153d0810ec688002a761021d8d100056d40043b1a2000ad98008763440014bd0bb86c6880029761770d8d100054f426e1b1a2000a9d84dc3634400153d09a86c688002a761350d8d100072da84a1b1a20008de87c8363440011bb0f906c68800297a1720d8d100052ec2e41b1a2000a9e84c83634400153b09906c68800237a1c
  | 11 => 0x4401117f04b90c8880232be0972191105d61fb96a43222000c3d72d48644401117d0f290c8880022f61e52191105cd1ec2ca43222000a9e83948644400153b07290c8880038be0952191105ce1fb92a43222000c3d72548644401117d0e290c8880022f61c52191105d51f428a43222000a9e83148644400153b06290c8882e327dcb32191100064eb96643222000e1f52cc86444001c3aa5990c8880222fa1e32191100045ec3c643222000a3e858c8644400147b0b190c8882dea760e321911000656b94643222000cad724c86444001d1f04990c8882df27dc932191105bf47392643222000c9d724c8644416fd1ae4990c888003235c932191100070fa92643222000e1d524c8644401117d0e190c8880022f61c32191100051f428643222000a3d850c8644417153d06190c888002a7a0f51191100054ec1ea23222000e3751944644401117d0f908c8880022f61f21191100051f42e423222000a3d85c84644400153d07908c888002a760f21191100055dc02423222000ab880484644401117d0e108c8880022f61c21191100051f428423222000a3d85084644400153d06108c888002a760c21191100055d400423222000ab980084644401117d0fa80c8880022f61f50191100445f43e4032220008bd87c80644400147d0b900c8880028f61720191100054f41e403222000a9d83c80644401117d0e100c8880022f61c20191100051f428403222000a3d85080644400153d06100c888002a760c20191100055b408403222000ab581080644400147f0a880c8880028f21510191100062ebaea7b1a2000ad581d4f63440058b8eb29ec68800a37e1d53d8d1000657b9285b1a2001cac7250b634400199ee5996c68800297a1632d8d100052ec2c65b1a2000a9e848cb634400153b09196c688003a350a32d8d1000c6fc3a65b1a2000ccd724cb6344001d1a84996c68800297a1432d8d100052ec2865b1a2000a9e840cb634400153b08196c6880029760b65d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052ec10cbb1a2000e1f65d936344001c38cbb26c688002a760b64d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c65193634400153b04326c68800317d9772d8d100062e32ee5b1a2000c9f64dcb6344001938c9b96c68800317d9572d8d100062e32ae5b1a2000c9f645cb6344001938c8b96c688003335cb62d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d100052fc2ac5b1a2000a5c8558b634400153f08b16c688002a721162d8d100052f428c5
  | 12 => 0x333e0f72591100066641ee4b22200087f855c964440050f90ab92c8880022fe1172591100046fc1ae4b2220078dc835c964440011f700b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100043f43ea4b22200287c87d4964440018bee7a92c8882d7171cf525911000637b96a4b222001c6c72d4964440010fd0ea92c8880021f21d52591100062fb9aa4b2220b6c5c7354964440018dee4a92c8880071b1c952591100045f43e84b222000c3f75d096444159878eba12c88800327dcf425911059e4e39e84b222000caf72d096444003958e5a12c8880062f21d42591100061fbaa84b2220abc3c75509644400193ee6a12c8882d3271cd425911000657b9284b222001cac7250964440011bd0f992c88801e3721f32591100062fbae64b2220aac5c75cc9644400199ee5992c888007331cb32591100046f43a64b2220008dc874c964440018beea992c8882a7171d5325911000667b9264b222001ccc724c96444001d1a84992c8880033a1cb70591100045fc3ac83222000a3f8559064440014790ab20c888002a7e0d64191100054e41ac83222000aaf82590644400155904b20c8880022f60a76191100061f3b6ca3222000a3d82d94644400117b0f328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100061f3b0ca3222000a3d82194644400117d0db90c8880030fd9772191100061e32ee43222000c3f655c86444001878cab90c8880022fe1f621911000656b96c432220008bd87988644400147d0b310c8880028f61662191100054f41cc43222000a9d83988644400117f0eb10c8880028fe1562191100051e42ac43222000a9f83588644400153906b10c8880022f61c62191100051f428c43222000a3d85188644400153d06310c888002a760c621911000656b90c43222000e2f651886444001c58ca310c8880032b61c621911000717428c43222000e2d851886444001d1d06310c888003a360c621911000752c08c43222000ea980188644400147d0da90c8880028f21b52191100061f3b6a43222000e2f62d486444001c58c5a90c8880028fa1952191100051e432a43222000c3e765486444001c5ec4a90c8880038b18952191100054f436643222000c9e76cc86444001c3ecb990c88800387197321911000747b16643222000e8c62cc864440015390c990c888003279d932191100070fb2a643222000e1c654c86444001b1ae4990c888003a3d89321911000746312643222000ea4628846444001d48c4908c888002ec20121191100055d434403222000ea8628806444001f4443100c888003aa1892019110005d840a403222000e1f5394c64
  | 13 => 0x54ec18e5b222000ab6811cb644400156b02396c888002aea0072d91100055cc00e5b222000c3f72d4b644400187ae5a96c8880022fa1e52d91100045ec3ca5b222000a9e8394b644400153b07296c8880038be0952d91100061fb92a5b222000c3d7254b644400117d0e296c8880022f61c52d91100054f418a5b222000a9d8314b644400193ee5996c888003275cb32d91100070fa9665b222000e1d52ccb644400117d0f196c8880022f61e32d91100051f42c65b222000a3d858cb644400195ee5196c8880032bdc932d911000747c1265b222000c9f724cb6444001d1ee4996c88800323dc932d91100064eb9265b222000e8c724cb6444001c3ea4996c8880038754932d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100051f42ee3b222000a3d85dc7644400153d07b8ec888002a760f71d91100054f41ea3b222000a9d83d476444001c6ea328ec8880022fa1f21d91100045ec3e43b222000a3e85c87644400147b0b90ec888002a7a0f21d91100054ec1e43b2220008be87087644400117b0e10ec8880028fa1421d91100051ec2843b222000a9e83087644400153b0610ec888002aea0021d91100055cc0043b222000a3f855c364440014790ab86c8880022fa1f50d91100045ec3ea1b222000e3b50943644400117d0f906c8880022f61f20d91100051f42e41b222000a3d85c83644400153d07906c888002a760f20d91100045f43841b2220008bd87083644400147d0a106c8880028f61420d91100054f41841b222000a9d83083644400156d02106c888002ad60420d91100461e322eb3222000c6e72d9664440018dce432cc8880030f9d764991100061ebaec93222000cae72d9264440018becb39cc8880031719673991100064fb24e73222008c9c649ce64440018becab9cc8880031719573991100064fb22e73222008c9c645ce64440018decab94c8880031b195729911000657b22e53222008cac645ca64440018dcea314c8880031b5d4629911000667398c53222000ccd7318a64440010fd0fb2ac8880031b1cb65591100043f438cab222000c6c7219564440018becbb9ac8880031719773591100062fb28e6b222000c5c651cd64440018decbb92c8880031b197725911000637ba8c4b222000c6c75189644400199ee6312c888003331cc62591100043ec16eab2220008bf845d564440011bf06baac88801e3720d755911000477c12eab2220018ec825d5644400187eebba2c8880030f1d774591100062fbaee6b222000c5c75dcd644400193ee9b9ac8880023760b73591100062fba8e6b222000c5c751cd644400193ee839ac8880031bdd77259110006363aee4b222000caf74dc9644400199ee7b92c888003331cf725911000637c2ee4b222000c6c85dc9644400195f09b92c888
  | 14 => 0xd424cb6544001c9a84996ca880038350932d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95105dd2f41865b2a2037a7a80dc765440010fd0f90eca880021f61f21d95100051f42643b2a2000a3d84c8765440014bd0790eca880029760f21d95100043f43843b2a200a87d87087654400147d0810eca880028f61021d95100052f41843b2a2000a5d8308765440014f50010eca880029e60021d95101bd3b40ee1b2a200087e87c8365440010fb0f906ca880028fa1320d95100051ec2641b2a2000a5e83c8365440014bb07906ca880021fa1c20d95100543ec3841b2a2000a3e84083654400147b08106ca8800297a0c20d95100052ec1841b2a2000a768108365440014eb02106ca880030f5d754d91100055cc06a9b222002c3c75953644400517f0eaa6c8880032bdcb42d91100051f42c85b222000a3d8590b644400153d07216c888002a760e42d911000c5fc3a85b222000cad7250b644400147d0a216c8880028f61442d91100054f41885b222000a9d8310b644400199ee4996c888007331c932d91100074721265b222000e8d424cb644400147b05b2ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec8880028f60865d91100061fb2ee5b222000c3c65dcb644400187ecab96c8880030f19572d911000656b96c5b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000a3f8558b64440014790ab16c888002a7e0d62d91100054e41ac5b222000a3e8518b644400147b0a316c888002a7a0c62d91100054ec18c5b222000cad7218b6444001c5eca316c8880038b19462d911000656c38c5b222000e2e8518b6444001c5b0a316c888003a3a0c62d911000746c18c5b222000ea58118b6444001d5300316c8880028fa1b52d91100051e436a5b222000e2f62d4b6444001c58c5a96c8880028fa1952d91100051e432a5b222000e2f6254b6444001c58c4a96c888002a7a1b32d91100070fb2e65b222000e1c65ccb6444001d1ec5996c888003a318b32d91100054e43265b222000e1f654cb6444001c38ca996c88800363dc932d911000747b1265b222000e8c624cb6444001d48c510ec888002ec20121d91100075431441b222000fa221883644400176102906c8880030f5d475d91100055d400ebb222000ab9801d7644400147d0bb9ec8880028f61773d91100055ac0ee7b222000ab980dcf644400147d0b39ec8880028f61673d91100064fb9ce7b222000aae829cf644400155b0539ec88800387d4e53d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d911000657c12e5b222000a3e851cb644400147b0a396c888002a7a0c72d911000
  | 15 => 0xab92c7080021fa1f5258e100143e43ea4b1c200087e8754963840010f90ea92c7080030fdd74258e105661e3ae84b1c2000c3f755096384157878eaa12c70800317dd73258e105562e3ae64b1c20018dc874c963840018beea992c7082a7171d53258e1000667b9264b1c2000e8d424c9638400f8bcc6ba8c70800237e1d6318e100062ebaac631c200287e859db43840010fb0b3b687080021fe157690e100143e42aed21c200287e859d943840010fb0b3b287080021fe157650e100143e42aeca1c2007c5e635d443840018baeab18870801f3398d7210e1000666b1ae421c2000d8d435c8438400f1f30d38087080022f61f641061003e2f31aeb98c2000c5d7558f31840011bb0fb1863080232d991711021003e2f31aea1842000c5d7558c308400f9acc6b8861080021fa1b72d95100143fc3ec5b2a2000c6d72d8b65440010fb0f316ca880028fa1262d95100051ec24c5b2a2000a5e8398b65440014bb07316ca880021fe1d62d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d95100543ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b65440018db0e316ca880038ba1062d951000716c20c5b2a2000e4e8318b6544001c9b06316ca880039960462d951000734c00c5b2a2000a3e86d0b654415987ceda16ca880038bd8b42d95100071631685b2a2000a3c8650b654415787ceca16ca880038bd8942d95100071631285b2a2000a5e86ccb65441558bced996ca8800393d8b32d95100072631665b2a2000a5c864cb65441538bcec996ca8800393d8932d95100072631265b2a2000f0d424cb6544001cc8c510eca880039918921d9510005b840243b2a2000e68628836544001ec443106ca880039a18920d9510005b840a41b2a2000c3d741d365440018bae639eca880021f61e72d95100051f424e5b2a2000a3d849cb65440014bd07396ca880029760e72d951000637c12e5b2a200087e871cb654400147d08396ca880028f61072d95100052f418e5b2a2000a5d831cb65441814ed02396ca880029d60472d95105fd3d400e5b2a2000a79801cb654400187ee5a16ca880030f5cb42d95100043f43c85b2a200087d8790b654417d47b09216ca8800297a0e42d95100052ec1c85b2a2000e2f8250b654400187ee4a16ca880030f5c942d95100043f43885b2a200087d8710b654417b47d08216ca8800297a0c42d95100052ec1885b2a2000c5f72ccb65440018bae5996ca8800387d0b32d95100070ea1665b2a200087e878cb65440010fb0f196ca880028fa1232d95100051ec2465b2a20bca5d838cb6544001c5a85196ca880038b50932d951000727c1265b2a2000c5f724cb65440018bae4996ca8800387d0932d95100072721265b2a2000e1
  | 16 => 0x2593105661e3ae84b2620018bc8750964c400187eeaa12c9882af0f1d5425931000657b9284b262000c5f75cc964c41558b8eb992c98800317dd5325931054e2e3aa64b262000e8d424c964c401187cc8ba8c9880022fe1d64193100061ebaac832620088be84dd763c400117b09baec7880021fe0975d8f100061f3ace9b1e2000c3d759d363c400187ceaba6c7880030f5d574d8f100045fc12e9b1e200287e85dcb63c40010fb0bb96c7880222fa1372d8f100045ec26e5b1e200287f87d4b63c40010fb0fa96c7882eb0f9d352d8f100061eba6a5b1e200087f8754b63c40010fb0ea96c7882e70f9d152d8f100061eba2a5b1e20088bf87d0b63c400117b0fa16c7882b30f9d742d8f100061ebae85b1e20008bf8750b63c400117b0ea16c7882af0f9d542d8f100061ebaa85b1e20aac5e75ccb63c40018baeb996c7882e3279d332d8f100064eba665b1e20018df874cb63c41538bcea996c788003175d532d8f105be4f3a265b1e2000c9d744cb63c400199ae4996c788003a350932d8f100065d3a2e1b1e2000cf2715c363c40031b90e992c78800333dc93258f1000746a1264b1e20008df8758c63c40010ff0abb6878800a1f21576d0f100143f42ced21e200087d859da43c40050fd0b3b287880021f6167650f100043fc2aeca1e200287c855d943c401187cc8ba887880030f5d56410f1004657322e421e2000cad645c843c4001b1a86b90878801e3d61a7110f100461f322ea20e2000c3d7559041c4011974c8b80838801f3698d700c7100461f322eba062000c3d7559340c400117b0fb2081880023761f630c31003c6f41eebb2420008dd83dd764840010ff04baec908003179d673d92100062ebace7b242000c5e755cf64840018baeab9ec90800237e0973d92100143f42ee5b24200087d85dcb648400f1bd07b96c9080023760f72d92100143fc3ea5b24200087d87d4b648416b8bce7a96c908003175cf52d92100043fc3aa5b24200087d8754b648416d8bce6a96c908003175cd52d92105661f3ae85b242000c3d75d0b648416793ce7a16c908003275cf42d921000c5fc3a85b2420abc3e7550b648400187aeaa16c9082d3279cd42d92100064eb9a85b242000cad7250b648400f1bf0f996c9080023761f32d92105562f3ae65b242000c5d75ccb64840011bf0e996c9080023761d32d921054e2f3aa65b242000c5d754cb6484001d1a84996c908003359cd71d921000678b8ce1b2420018bc87509648400195ee4a12c908003a350932592100045fc3ac832420088be84dd7638400117b09baec70800637e1d32d8e1000666b9265b1c2000e8d424cb63840015a902996c7080033c5c670d8e100143f43eeab1c200087d82dd563840010fd0e3aac70800b171d65358e100146e43aa6b1c200087f855c963840050f90
  | 17 => 0x286000c77719c5650c00147f08b8aca180028f21171594306152fc1ae2b286007a5c835c5650c0010fd0f90aca180021f61f21594300051f42642b286000a3d84c85650c00f4bd0790aca180029760f215943003d2e41c42b286000a5f83485650c00f4b90690aca180021fa1c21594300043ec3842b286000a3e84085650c00147b0810aca1801e97a0c21594300052ec1842b286000a7a80085650c0014f30010aca183069760e70594300743f43e40b28600087d87c81650c00147d09902ca180028f613205943003d2f41e40b286000a5d83c81650c0010fd0e102ca180021f61c20594300051f42040b286000a3d84081650c00f4bd06102ca180029760c20594300053b40840b286000a7581081650c00f1b906baac8180023e201725903000c5e43a84b206000caf72509640c00157100a12c818003a350932590300143f428e2b20600087d851c5640c0010ff0aba4c21800a1f215749843000746a126530860018f587886610c00117f08baac2180222f211755843003c6e41aeab0860078dc835c9610c16bca863a92c2182db950c5525843059f4a18e84b0860b4e9431509610c00199ee4992c218003a350932584300056a40a64b086007ad483885610c0031e90e90ac21801eb520d215843003e2f39acba086000c5d655cf410c0018f2cb38482180031e59570904300143e42eeca08600087f855d9410c0050f90abb2821813e37e0d76504300043ec36eaa08600087e87595410c0010f90eb2a821801f171cd655043003e4e39ac8a086000c5e65dcd410c0018bacbb9a821801f351ce615043003e6a39ac2a08600287e855d8410c0010ff0cba882180021fe1d65104300043ec3aca2086007cd6715da310c0a14bf0eb2c62180029761d658c4300052fc12cb1886000a5d82596310c0018bee4b2c6218003175c9658c4300070fa12cb1886000e1d42596310c00f8bce2b2c621801f959c5658c4300143f42aeda00601c87f865d7400c01d0ff0eb2e80180021f61d65d00300143f42eed200600087d85dda400c0010ff0cbac801829e1fe1d65900303fc3ec3acb2006007c9e73592400c00f8bce6b2880180031759573100300062e3aeec9806000c5f85dd9300c0018b90bbb2601800237e0b764c0300046ec16ec9806000c5f52dd9300c0018baa5bb2601800327d0b764c0300064ea16ec9806000c5f76dd5300c00193eedba2601800327dd8744c0300068e3a8e898060078de83dd764c40011bb07baec9880062fe1d42d931000656b9285b262000ab88050b64c4001d1a84996c9880033c9c570d93100143f43eeab26200087d82dd564c40010fd0e3aac98800b0f1d654593100145e43aa8b26200087f855c964c40050f90ab92c9880021fa1f52593100143e43ea4b26200087e8754964c40010f90ea92c9880030fdd74
  | 18 => 0xc001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c001958e4322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980023de1d611853000572412c230a600087f855d0614c0050f90aba0c2980072b9c9421853000656b928430a6000e8d424c8614c0015ab07908c298002bc60021185300043fc2aeda0a600287c855db414c0010ff0abb4829800a1f21576905300143f42eeca0a600087d85dd9414c0050fd0b3b282980021f61676505300143e428eca0a60078dc831d9414c0010fd0dbaa82982770f19375505300043f43ecaa0a600087c87d95414c0ab8b8e7b2a82980030fdd764505300061e3aec8a0a6054c9c73d91414c0018becbb9a82980031719773505300064fb26e6a0a604fc9c64dcd414c0050f90b3b082980021fe1576105300143e42aec20a600087c865d4414c011878c8ba882980021fe1f65105300043ec3eca20a6000c3e75d90414c00187aebb2082980232719173105300465c324e020a6008cb8645c0414c0010f90cbac62980021f61f658c5300061f3aec918a6000c3d75d92314c00187cea32462980030f5d4648c5300065c324e118a6000cb8645c2314c0abca863b2a62982c61f21975d01300461e322eba02605587f87d97404c0010fb0fb2e80980030f9d764d01300061ebaec9a026008c9c645cf404c0050f90b3b4809806a1f21975901303fe1e322eb202600087f87d96404c0230fb0fb2c80980030f9d764901300061ebaec9202600087f855d9404c0050f90abb28098153271cf64501300062e32ee6a026055c5e76d96304c0abcb6c1b2c6098153279db648c1300464f3b0c91826000e1c65192304c00187ee93a2ca1831297e0d745943003d2e41ae8b2860b5c5f32dc9650c16b8b863b92ca182da1f61e72594300051f424e4b286000a3d849c9650c00f4bd07392ca1830e9760e725943000637c12e4b2860b6c5f325c9650c16d8b862b92ca182d61fa1c72594300051f420e4b286000a3d841c9650c00f4bd06392ca1803a9760c72594300061fb9684b286000c3d72d09650c167c3e65a12ca182cf870c742594300043f43c84b28600087d87909650c16947b09212ca1801e97a0e42594300052ec1c84b286000a7b80509650c0014f100a12ca180038be0942594300061fb9284b286000c3d72509650c169c3e64a12ca182d38b8c942594305a71699284b2860b4e1c31509650c001c7700a12ca180038e20142594300043f43884b28600087d87109650c16747d08212ca1801e97a0c42594300052ec1884b286007a5f824c9650c00fc9f04992ca1800317dc932594300062eb9264b286000e1f424c9650c001c9c84992ca1800387509325943000726a1264b286000e0d424c9650c0014b902992ca1801e97a0f71594300752ec1ee2b
  | 19 => 0x28fa1b52191300051e436a43226000c3e76d48644c00147d0ca90c8980028f21952191300061f3b2a43226000d2d72548644c0a993ced990c89800387d9732191300070e32e643226000c9e764c8644c001c3eca990c898003871953219130006c6b92643226000e8f624c8644c00173100990c89814f8794f53191300445fc12e43226008caf825c8644c17587ee5a90c8980030f5cb52191300445f43ca432260008bd87948644c17347b0b290c89814ea7a0e52191300054ec1ca43226000cad72948644c00195ae4a90c8980038be0952191305ce1fb92a432260b9e2e72548644c00187ae4a90c8982e78b5c9521913000616b92a432260088be87148644c00117b0e290c8982ea8fa14521913029d4f418a43226000a9d83148644c17193ee5990c898003275cb32191300070fa96643226000e1d52cc8644c01117d0f190c8980022f61e32191300051f42c643226000a3d858c8644c16f53b07190c8980032b5ca321913000656b92643226000abb804c8644c00157100990c89814ea7e09321913029f47c126432260b7c9f724c8644c16fd1ce4990c898003275c932191305bf46b92643226000c8d724c8644c001c3ea4990c8980038754932191300074dc02643226000e98804c8644c0a753d07a88c898002a760f51191300071ba8ca23226000aba80144644c00157300288c8980222fa1f21191300045ec3e423226000a3e85c84644c00147b0b908c89814ea7a0f21191300054ec1e423226000cad72c84644c00195ae4908c8980222fa1c21191300045ec38423226000a3e85084644c00147b0a108c89814ea7a0c21191300054ec18423226000aba80084644c00157300108c8980222fa1f50191300045ec3ea03226000a9f83540644c0a753906a80c8980028fe1530191300051e42a6032260088be87c80644c00117b0f900c8980028fa1720191300051ec2e403226053a9e83c80644c00153b07900c8980032b5ca20191300445f4384032260008bd87080644c00147d0a100c8980028f614201913029d4f418403226000a9d83080644c00195ae4100c898002ada0420191300055ac08403226008cb8649c3434c0010fd0dbaa869829b0f1937550d3062c3f43ecaa1a60a687c87d95434c0abc3887b2a86980030fdd76450d300061e3aec8a1a6007a9e83d91434c001976c83828698003a350932d85300056ac1843b0a6000af180087614c00187ecb3a4c2980030f19674985300061fb2ae930a6000c3c655d2614c00187cebb24c2980030f5d764985300061f3a8c930a6000c3d75192614c0050fd0dbaac2980021fa1f655853000636396cab0a600087e87195614c0018d8e432ac2980030fd9774585300061e32ee8b0a6000c3f651d1614c001878ca3a2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614
  | 20 => 0x1ec28e5b226054a9e831cb644c00153b06396c8980030fdcb52d91300061eb96a5b2260008be8794b644c00117b0f296c898152a7a0e52d91300054ec1ca5b226000e2f8254b644c00187ee4a96c8980030f5c952d91300045f438a5b2260008bd8714b644c0a953d06296c898002a760c52d91300064fb9665b226000c9d72ccb644c001c3ea5996c8980038754b32d91300045f43c65b2260008bd878cb644c00147d0b196c8980028f61632d913000657b9465b226000caf724cb644c0a9d1f04996c89800327dc932d913000747b9265b226000c8f724cb644c00193ae4996c898003a31c932d91300070fa9265b226000e1d524cb644c00147d0bb8ec8980028f61771d91300054ec1ee3b226000a3e859c7644c00147b0b38ec898152a7a0f51d91300054ec1ea3b226000e3751947644c00117d0f90ec8980022f61f21d91300051f42e43b226000a3d85c87644c0a953d0790ec898002a760f21d91300045f43843b2260008bd87087644c00147d0a10ec8980028f61421d91302a54f41843b226000a9d83087644c0015750010ec898002ae60021d91300051fc2ae1b226000a3c855c3644c0a917d0fa86c8980022f61f50d91300071da84a1b2260548be87c83644c00117b0f906c8980028fa1720d91300051ec2e41b226054a9e83c83644c00153b07906c8980022fa1c20d91300045ec3841b226000a3e85083644c00147b0a106c898152a7a0c20d91300054ec1841b226000ab681083644c00156b02106c8980230f19175991300061f3aec93226000c3d75d92644c0010fd0fb2ac8980021fa1c65591300043ec16eab2260008bf845d5644c0011bf06baac8980030fdd774591300061e3aee8b226000c5c75dcd644c0010ff0ab92c89800a1f21572591300045fc22e4b2260008f7815c9644c0011e902b92c8980023ee0172591300043f43ea4b22600287c87d49644c0010fd0ea92c8980021f21d52591300045f43e84b226000c3f75d09644c159878eba12c8980062f21d42591300061fbaa84b2260abc3c75509644c00195ee4a12c89800317dd732591305562e3ae64b2260018dc874c9644c0018beea992c8982a7171d5325913000667b9264b226000e8d424c9644c00117f0eb20c8980028fe1564191300051e42ac832260008bd829d8644c00187cedb28c8980028f60b65191300045ec3cca32260008bf87594644c00187cec328c8980028f60865191300045f436e43226000c3f65dc8644c001878cbb90c8980030fd9572191300061e32ae432260008bf87d88644c00195ae5b10c8980022f61e62191300051f42cc43226000a3d85988644c00117f0eb10c8980028fe1562191300051e42ac43226000ab781588644c00156902b10c8980022f61c62191300051f428c43226000a3d85188644c00195ae4310c8980
  | 21 => 0x624cb654c001c98c4996ca98003c350932d9530005ac40265b2a6000c3d741d3654c0974f501b9eca980021f61e72d95300051f424e5b2a6000a3d849cb654c0ab4bd07396ca980029760e72d953000637c12e5b2a600087e871cb654c00147d08396ca980028f61072d95302ad2f418e5b2a6000a5d831cb654c00187ee5a16ca980030f5cb42d95300043f43c85b2a600087d8790b654c19147b09216ca9815697a0e42d95300052ec1c85b2a6000e2f8250b654c00187ee4a16ca980030f5c942d95300043f43885b2a600087d8710b654c18f47d08216ca9815697a0c42d95300052ec1885b2a6000c5f72ccb654c0018bae5996ca9800387d0b32d95300070ea1665b2a600087e878cb654c0010fb0f196ca980028fa1232d95300051ec2465b2a60c6a5d838cb654c001c5a85196ca980038b50932d95302ad2fc1265b2a6055e4f824cb654c0018bee4996ca98003175c932d95300070fa1265b2a6000e4e424cb654c001c3a84996ca980039350932d953000706a1265b2a6000a5f835c7654c0ab4b906b8eca980031d5c471d95300043f43e43b2a600087d87c87654c00147d0990eca980028f61321d95302ad2f41e43b2a6000a5d83c87654c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c0ab4bd0610eca980029760c21d95300053d40043b2a6000a7980087654c0ab0fd0f906ca980021f61f20d95300051f42641b2a6000a3d84c83654c0ab4bd07906ca980029760f20d95300043f43841b2a601187d87083654c00147d08106ca980028f61020d95302ad2f41841b2a6000a5d83083654c0014ed02106ca980029d60420d95300061ebaea9b226002c3c75953644c00517f0eaa6c8980028fa1642d91300051ec2c85b226000a9d8390b644c00317f0ea16c8980032b5c942d91300051f42885b226000a3d8510b644c00153b06216c89800333dc932d91300074721265b226000e8d424cb644c0050fd0b38ec8980021f61671d91300051ec16cbb226000a3d82197644c00187ecbb96c8980030f19772d91300061fb2ae5b226000c3c655cb644c00195ae5b16c8980028fa1662d91300051ec2cc5b226000a3f8558b644c0014790ab16c898002ade0562d91300055a40ac5b226000a3e8518b644c00147b0a316c8980032b5c862d91300051f436a5b226000a3c86d4b644c00147d0ca96c8980028f21952d91300070fb2e65b226000e1c65ccb644c001c3eca996c8980038719532d9130006c7b9265b226000e8f624cb644c001d18c4996c898002e620132d91300061eba8ebb226000a3e85dcf644c00147b0bb9ec898002ada0773d91300055ac0ee7b226054e1e53d4f644c00147d0b396c8980028f61672d91302a54f41ce5b226000a9d839cb644c00195f04b96c8980028fa1472d9130005
  | 22 => 0xa94c3980021f61d52987305661f3ae8530e6000c3d75d0a61cc15787ceaa14c3980030f5d5429873054e2f3aa6530e6000c5d754ca61cc00199ae4994c398003a3509329873000746a1264b0e600087f855db41cc0050f90abb6839800a1fa1776907300043ec2eed20e600087f855d941cc0050f90abb283980230f99175107300061ebaac820e6008c3e645d740cc0a717f0eb2681980030f5d564d033003e4e39ac8a0660008f681dd7648c0011eb03baec9180021fe0975d92300143f42ee5b24600087d85dcb648c0011ed03b96c9180023d60772d92300143fc3ea5b24600087d87d4b648c0010ff0ea96c9180021f61d52d92305661f3ae85b246000c3d75d0b648c00317f0ea16c9182af0f9d542d92300061ebaa85b246000cad7250b648c1558bceb996c918003175d732d923000c6fc3a65b2460a9c5e754cb648c0018baea996c918003335c932d923000746a1265b246000c76759c7648c0018eaeb38ec918003355ce71d92300063ba94e3b246000c75529c7648c00196e8538ec9180032d50a71d92300066b994e3b246000cd5329c7648c0018eceab8ec9180031d5d571d92300063ba92e3b246000c75525c7648c00196e84b8ec9180032d50971d92300066b992e3b246000cd5325c7648c0019e2e3386c9180062f21d425923000657b9284b246000ccd724c9648c001d1a84992c91800a1fa1471592300043ec28e2b2460008bf87590648c0a917f0eb2687180021fe1574986300143e42ae930c6000e8d424ca618c0051eb0f28cc31800b1d9d6519863000c7ac3c4330c600087d82dd5618c0010ff0ab92c31800a1f21572586300043f43ea4b0c600287c87d49618c0010fd0ea92c3180021f21d52586300061fbae84b0c60acc3c75d09618c00187eeaa12c3182af0f1d5425863000657b9284b0c6001cac72509618c0018beeb992c3182ab171d7325863000667b9664b0c6000c5f754c9618c1538b8ea992c318003a350932586300163a3aca2b0c60028f487545618c0031e90e90ac3180023de1d61186300063abaac230c600287e859db418c0010fb0b3b683180021fe1576906300143e42aed20c600087f855d9418c0050f90abb283180031d5d661106300063abaac220c6000c7575986318c0018eaeab0c631800297e15618c630006acbaae118c6007cda605d8318c0014bf0ab0863180232799173102300043f436e5b2a600287f87d8b654c0018dae5b16ca980021f61e62d95300051f424c5b2a6000a3d8498b654c0010ff0eb16ca980028fe1162d95300051e422c5b2a6000a778158b654c0014e902b16ca980461f61c62d95300051f420c5b2a6000a3d8418b654c0018dae4316ca980028fa1b42d95305661f3b685b2a6000a3c8650b654c15787ceca16ca982c7179db32d953054e2f3b265b2a6000e4f
  | 23 => 0x58c405d70e21ea4b18800087e8754963100010f90ea92c6202e78710d5258c4029c5e43a84b188000c3f755096310157878eaa12c62014ea720d4258c400062fbae64b1880aac5c75cc9631001153909992c6200063721d3258c400062fbaa64b1880a9c5c754c9631001153908992c62000333dc93258c4000746a1264b188000ad8804c9631000127b0b38c86200026e6027190c400049fc2ae12188000e8d424ca61100111eb0f28cc22000b1d9d6519844000c7ac3c43308800287e87dd5611013b878e9baac2202778d10775584400043ec16eab08809dc3f42dd5611001117908baac22000237e0d755844003c6e41aeab0880b2c3c741d56110165c68823aac22000317dd773584400062e3aee6b08804fc9c74dcd611009fd2883b9ac2200023760b735844027e4fa16e6b088000c5f751cd61100018b8ea39ac22016f271d073584402df4a208e6b08800087f855c961100050f90ab92c2200222f21172584400046fc1ae4b0880078dc835c961100010fd0fa92c22000a1f21f52584400062fb9ea4b0880b5c5c73d496110175c6883a92c2200021fa1d52584400043e43aa4b088000c5f73549611016d8b8e6a92c2202e78d10552584400061fbaa84b0880abc3c75509611000193ee6a12c2202d3271cd425844000657b9284b088000ab48150961100011bd0f992c22001e3721f32584400062fbae64b0880aac5c75cc96110171d2883992c22000237a1d32584400046e43a64b088000c5f754c961101538b8ea992c220003a350932584405bf4a20a64b088002c747594561100111e90ea8ac220022ad21151584400455a42442b0880018f48748561100115690890ac220002bc20121584400465b38aed208800093f855c2411000f8bcc6bae622016e37e1d63cc4400062ebaac7988800287e85dda31100010fb0bbb462200031d5d6618c4400063abaac31888007ad48358631100010ff0abb2622000a1f215764c4400464e3a2c69888008cb47458531100010ff0abb0622000a1f215760c44029e4e21aec1888000c3e85dd9401000187b0bbb280200022fe0b76500400045ec16eca008000c3f52dd9401000187aa5bb2802000327ccb76500400064e996eca00800093d851c540100050fd0fbaac9980021f60b755933052e2f996eab2660a587e871d564cc005878eb2a2c99801e2f21d54593300043fc2ae4b26600287c855c964cc0010fd0fa92c99800a1f21f52593300043f43aa4b26600087c8754964cc00187eeba12c9982b30f1d7425933000c5e43a84b266000c3f7550964cc157878eaa12c9980032bdc942593300062fbaa64b2660a9c5c754c964cc001d1a84992c99800a1fe1d75987300043fc12eb30e6096c5f325d661cc0050fd0bb94c3980021f61772987300143fc3ea530e600087d87d4a61cc0010ff0e
  | 24 => 0xc8000e8d424ca61900031eb0f10cc32000a1fa1773586400043ec2ee6b0c8000c6f7254961900038d8e4a92c3200032bdcb425864000667b9264b0c8001ccc724c96190001d1a84992c3200063d21d21586400143fc32ea30c800087d8799461900010ff0eb28c3200023de1d61186400063cb2ce120c8000c79655c24190001c6acab0c83200024fe1570906400043ec36eaa0c800087c8759541900018bccbb9a83200031759773506400062f328e6a0c8000c5d651cd41900019a8e730a8320003351cd61506400465d302ec20c807393f865d4419000127f04ba883200024f60975106400061fb12ea20c8000c3d625d44190001a3e64ba88320003474c975106400461f302ea20c8008d3a605d4419000127b0eb28832000a1fa1676cc6400043ec2ced98c800287e855db31900010ff0cbae63200021fe1d65cc6400043ec3acb98c800287e85dda31900010fb0bbb4632000a1fa16768c6400043ec2ced18c800287e855da31900010ff0cbac63200021fe1d658c6400043ec3acb18c8000b1d8510e319000171b0421c632000a1fa14764c6400043ec28ec98c8000c3e65dd131900050fd0b3b063200021f616760c6400063cb2ce018c8000c79655c0319001137108b8063200030f99576d024037c9fc32eba04800093f825d7409000127b04bae81200030fd8975d02400061eb12eba048000d1f325d74090001a3a64bae81200230f98175d02400469d302eba04800093d87597409000187aecb2e8120003175d753d8d4000657b9285b1a80018df874cb635000199ae4996c6a0003a350932d8d400043fc2ae3b1a800287c855c763500a987ec8ba8c6a000237e1d6318d400052e42ac631a8000c5c75d8d43500010ff0ab9ec2a000a1f21573d854000746a1265b0a80008f78758461500010ff04ba8c2a000a1fa1772185400043ec2ee430a800287f87d4861500010fb0fa90c2a00021fe1d52185400043ec3aa430a80acc3e75d08615000187aeba10c2a02af0f9d542185400061ebaa8430a8000ab88050861501558bceb990c2a0003175d7321854054e2f3aa6430a8000c5d754c8615000399ce4990c2a0003335c9321854000746a126430a800287e851da31500010fb0a3b462a0003179d7638c5400143f428ec98a800087d851d931500010ff0abb062a000a1f215760c54003e4e31ae818a8007cd8635c031500ff87cecbac80a00028f61461901400143f43eeab1880a6c3c74dd5631014dc3887baac6200021f60b7558c405361fa16eab1880088bc845d5631018b878e83aac6203178710c7558c400162e3aca6b1880088dc8754d631001153908a9ac6202e32710f7258c400043fc2ae4b18800287c855c9631001117908b92c6202df2710d7258c400047bc0ae4b1880008f4815c963100010fd0fa92c62000a1f21f52
  | 25 => 0x14b906ba2cb201be9ee0174596400062fb9ce6b2c8000a3f845cd65900ff47908b9acb200021f61e72596403fd1f424e4b2c8000a3d849c965900014bd07392cb200029760e725964000637b94e4b2c8000c6f825c965900010fd0e392cb201fe8fa1072596400051ec20e4b2c8000a5e831c965900014bb06392cb200030fdcb42596400061eb9684b2c800087e8790965900010fb0f212cb203328f61242596400052f41c84b2c8000a5d8390965900014f700a12cb200029e20142596403fd1fc1284b2c807fe2f82509659000187ee4a12cb200030f5c942596400071dc0284b2c8000e388050965900018bee5992cb20003175cb32596400070fa1664b2c8000e1d42cc965900010fd0f192cb200021f61e32596403fd1f42464b2c8000a3d848c965901974bb07192cb200038b50a325964000716a1264b2c8000e4f824c965900018bee4992cb20003175c932596400070fa1264b2c8000e4e424c96590001c3a84992cb2000393509325964000706a1264b2c800087e870c965900010fb0e192cb201fe8fa1032596400051ec2064b2c80caa5e830c965900014bd07b8acb200029760f71596400063bb8ce2b2c8000a3f845c565900ff47908b8acb200021fa1f21596400043ec3e42b2c807fa3e84c85659000147b0990acb2000297a0f21596400052ec1e42b2c800087e8708565900010fb0e10acb201fe8fa1021596400051ec2042b2c8000a5e8308565900014bb0610acb200029ea0021596400053cc0042b2c801a87e87c8165900010fb0f902cb201fe8fa1320596400051ec2640b2c8000a5e83c8165900014bb07902cb200021fa1c20596403fc3ec3840b2c807fa3e84081659000147b08102cb2000297a0c20596400052ec1840b2c8000a768108165900014eb02102cb200031d99671d8e400063ab2ce3b1c8000c76655c763900018eacab8ec720002b5a076398e402a45f43e84b1c8000cad7250963900031b90e992c72000333dc93258e4000746a1264b1c800287e85dc563900010fb0bb8ac7200021f61e6518e400043fc3aca31c80008df8758c6390001c3acab1c87200024f6167190e400049fc2ae121c800087d86dd543901930f90eb2a87201ff8710d6550e403d49fc32ea21c800093f825d4439000127b04ba887200030fd897510e400061eb12ea21c8054d1f325d44390001a3a64ba88720153470c57510e400461f302ea21c8008d3a605d4439000127b0eb2887201df2ba197210e4000656c32e421c8000d2e855c84390001a5b0ab9087200034b9957210e4000696b2ae421c8054d8e835c843900efb1b06b9087201532bd8d7210e402a656b1ae421c8054d8c315c8439001195cc0b9087200236a9817210e400062f32ce7b0c8000c5d659cf61900018bccab9ec3200031759573d86400056b41ec330
  | 26 => 0x3a350932580310056c40264b006202c7875941600c40f1f10ea82c01881eb620d505803103d6c41c40b0062018f887481600c40f5b106902c018802bc20520580310062fb9ce6b2e80bac3f42dc965d017587881b92cba02e61f61e72597400451f424e4b2e80cda3d849c965d00014bd07392cba00029760e725974000637c12e4b2e80b9c3f425c965d017387880b92cba02ea1fa1c72597400451f420e4b2e801ca3d841c965d00014bd06392cba00029760c72597400451fc1284b2e8008e2f8250965d000187ee4a12cba00030f5c942597400051e40284b2e8000c5f72cc965d00018bae5992cba02e387d0b32597400070ea1664b2e80b8e1c40cc965d00010fd0f192cba00021f61e32597400451f42464b2e8000a3d848c965d016f4bb07192cba00038b50a325974000716a1264b2e8000e4f824c965d00018bee4992cba0003175c932597405bf0fa1264b2e80b7e4e424c965d0001c3a84992cba02df93509325974000706a1264b2e80b7e1c404c965d00010fd0e192cba00021f61c32597400451f42064b2e8000a3d840c965d01714bd06192cba000297a0f71597400052ec1ee2b2e8000c77719c565d00010fd0f90acba00021f61f21597400451f42642b2e8000a3d84c8565d00014bd0790acba00029760f21597400043f43842b2e800087d8708565d001147d0810acba00028f61021597400052f41842b2e8000a5d8308565d00014f50010acba00029e60021597403651fc22e0b2e8000a5f835c165d00014b906b82cba00021fa1f20597400043ec3e40b2e8008a3e84c8165d000147b09902cba000297a0f20597400052ec1e40b2e8008a3c8488165d000147f08902cba00228f21120597400e43f43840b2e800087d8708165d001147d08102cba00028f61020597400052f41840b2e8000a5d8308165d00014ed02102cba00029d604205974000c6e43a64b1e8000ccf724c963d0001d1a84992c7a000a1fa177158f400043ec2ee2b1e8000cad7250a61d0001d1a84994c3a000a1fa1773587400043ec2ee6b0e8000e8d424c961d00050fd0abb663a00021fe1975cc7400043fc3acb98e800087d8759731d00050fd0bbb463a00021f617768c7400143f42aed18e800087f865d631d00010ff0eb2c63a00021f61d658c7400461f3a2ca18e80538bf865d031d000187acaba063a006a8fe1974596400058e41ae8b2c800087f865c965900010fd0fb12cb2006a1fa1e62596400052f41cc4b2c8000a5d8398965900018dee5312cb2000a1fa1d625964000637b92c4b2c800087e8718965900014bd06312cb200029760c62596400053b408c4b2c8000a7581189659014f87eeda12cb202af0fdd942596400071731284b2c8000e2d6250965901558beed992cb202a717dd9325964000786a1264b2c8000a5f835d16590
  | 27 => 0x6a1265b0262008fb87580604c4010ff04ba8c09880a1fa1772181310043ec2ee4302620287f87d48604c4010fb0fa90c0988021fe1d52181310043ec3aa430262acc3e75d08604c40187aeba10c098aaf0f9d542181310061ebaa843026201cae72508604c40195ae4a10c098aab179d732181310062ebae6430262a9c5e754c8604c4018baea990c098803a350932181310056a40a643026200c5d758c4604c4050fd0fbaac818a97171cf755903152f0e21eeab20620087d82dd5640c54b8be65baac81881e3720d755903152c3f438eab2062c9c5c731d5640c593c38863aac81880b0f1d6545903103c5e43aa8b206207a9c83551640c40f1b907b92c818acf2710f72590310043fc2ae4b20620287c855c9640c40f1b906b92c818ad32710d72590310047a40ae4b2062008fb805c9640c4011f100b92c8188021fa1f52590310143e43ea4b2062b5c5c73d49640c56bc3887a92c8188021fa1d52590310043e43aa4b2062b6c5c73549640c56dc3886a92c8188030fdd742590315661e3ae84b206207a9c83d09640c567938e7a12c8188062f21d42590310061fbaa84b2062abc3c75509640c40f53906a12c818ad3271cd425903100657b9284b206200ab481509640c4b71b90e992c81880317dd5325903154e2e3aa64b20625ba9c844c9640c401d1a84992c81880257e1571d0c31004aec2ce1a1862009d5819c3430c4010ff0abb6821880a1f21576d04310143f42eed208620087d85dda410c40f93ce6b2482188230f99175104310061ebaac82086200c5e85dd9310c4018bb0bbb2621880237e0b764c4310046ec16ec9886200c5f52dd9310c4018baa5bb2621880327d0b764c4310064ea16ec9886200cd651dd9310c4019aaa3bb2621880257614704c43100746a126530062078f987942600c4031f30f104c01880a1fa1f75580312ae2e39eeab006255e5830dd5600c4010fb05baac01895717ccb75580310045fc22eab0062088bc845d5600c5638b8e63aac018ac7960c075580310061fbaee8b006200c3c75dd1600c4a9938e7ba2c018953a60c374580310045ec16e8b006254c9f32dd1600c40187eea3a2c0188030f1d4745803129e4e398e8b006253e98301d1600c4010ff0ab92c01880a1f21572580310045fc22e4b0062088bc845c9600c4010fd0fa92c01880a1f21f52580310061fba6a4b0062bac3c74d49600c56bcb061a92c0188021fa1d52580310043e43aa4b006200c3f74549600c573878e8a92c018adb960c152580310045f43e84b0062088bc87d09600c40187eeba12c018ab30f1d7425803159f4c18684b0062008be87509600c4011790ea12c0188030fdd5425803155e1e3aa84b0062b4e9830509600c4018beea992c018aa7171d532580310064fba264b0062b7c9c744c9600c40199ee4992c01880
  | 28 => 0x7cc9648c40199ae4992c918803a350932592310143f42ee0b24620087d85dc1648c4010fb0f328c9188021fe1d65192310045fc3ac83246200e1d65593438c4b71bf0cb8e871880257e1571d0e31004aec2ce1a1c620087d86dd5438c54d0fd0eb2a8718b161f21d6550e314b70e21acaa1c629195f865d4438c4012bf04ba88718802576097510e310062fb12ea21c6200c5d625d4438c49fa3e84ba88718803475097510e3103e2f30aea21c6207d56615d4438c49fa3880ba887188025761d6510e3147667432e421c6200ccd865c8438c401a9d0ab908718803536157210e31006a732ae421c6200d4d655c8438c49fb1d08b908718a3b636117210e3127e67b22e421c624fccd645c8438c40f99cc2b90871881f719857210e3127ec6202e421c622987d86dd5418c4450f90eb2a8318a5b171cd65506310062f32ee6a0c6200c5d65dcd418c5510ff0cba883188021fe1d65106314b43ec3aca20c6208c9e645cc418c4018bccabb66318a3657e1975cc631004afc12eb98c620095d825d7318c4018bec4bae63188031758975cc6310068fa12eb98c6200d1d425d7318c40f8bcc2bae631881f5598575cc631004aec3acb98c6200c5d76597318c40187ccb3a6c1188030f59674d82310061f32ae9b046200c3d655d3608c40157509b04c118803a3509329823100c7cc3c41304620287e85dd1608c4010fb0bba2c1188031bdc9525823100e36392a4b046200caf72509608c403958e4a12c11880333dcb325823100746a1264b0462018f887481608c4050ff0cba8c1188021f61e65182310043fc3aca30462008fb87580608c40187aebaa6c8988062fe1d42d913100656b9285b226200ccf724cb644c401d1a84996c8988021fe1570d91310143e42ae1b22620087d82dd5644c40117f08baac89880237e0d75591310061e3aee8b226200c5f75dcd644c4018b8ebb9ac8988023760b73591310043fc2ae4b22620287c855c9644c4011bf06b92c8988023de0572591310047dc02e4b2262008f8805c9644c4010fd0fa92c89880a1f21f52591310062fb9ea4b22620087e87549644c4010f90ea92c89880317dcd52591310061fbae84b2262acc3c75d09644c49f93ee7a12c8988062f21d42591310061fbaa84b2262abc3c75509644c40193ee6a12c8988032bdc942591310046f43e64b226200c5f75cc9644c5558b8eb992c89880237a1d325913100c6e43a64b226200c5f754c9644c5538b8ea992c89880333dc9325913100746a1264b22624fc5f635d4644c40117f0eb20c8988028f21564191310061e3aec8a1a6208c9c645cf414c4050fd0b3b482988021f61676905310043fc2aeca0a620287c855d9414c401878ebb22829893f2719373505314b62f3b2eb18a6296d56715d6314c4010ff0aba6c09880a1f21574d81310074
  | 29 => 0x92cb18803c350932596310061fba4e8b2c6200a5f835d1658c52d4b906ba2cb188028fe1173596310051e422e6b2c628da77815cd658c4010fb0f392cb188028fa1272596310051ec24e4b2c6296a5e839c9658c4014bb07392cb188031be0972596310043f438e4b2c6200a3e841c9658c40147b08392cb18a5a97a0c72596310052ec18e4b2c6200c3f72d09658c40187ae5a12cb188021fa1e42596310043ec3c84b2c62d0a3d84909658c52d4bd07212cb188029760e425963100717c1284b2c6200c3f72509658c40187ae4a12cb188021fa1c42596310043ec3884b2c62cfa3e84109658c52d4bd06212cb188029760c42596310062fb9664b2c6200c5d72cc9658c401c3e85992cb188038750b32596310043f43c64b2c620087d878c9658c40147d09192cb188028f61232596316752ec1c64b2c6200e2d428c9658c401c5a84992cb188029de0532596310053a40a64b2c6296a5f824c9658c52dc9f04992cb1880317dc932596310062eb9264b2c6200e1f424c9658c401c9c84992cb1880387509325963100726a1264b2c6200e0d424c9658c401caf02992cb188039520532596311143f43e42b2c620087d87c85658c40147d0990acb188028f61321596314b52f41e42b2c6200a5d83c85658c4010fd0e10acb18a5a1f61c21596310051f42042b2c6200a3d84085658c52d4bd0610acb188029760c21596310053d40042b2c6200a7980085658c40147d09b82cb188028f61370596310052fc1ae0b2c6296a5c835c1658c4010fd0f902cb188021f61f20596310051f42640b2c6200a3d84c81658c52d4bd07902cb188029760f20596310043f43840b2c620087d87081658c40147d08102cb188028f61020596314b52f41840b2c6200a5d83081658c4014ed02102cb188029d60420596310063d32ce1b246200c79659c3648c4018f4cab86c9188031e59570d92310047d406ebb2462008f980dd7648c4010ff04baec91880a1fa1772d92310043ec2ee5b2462008fa80dcb648c4011f301b96c91880a1fe1f52d92310043ec3ea5b24620087f8754b648c4010fb0ea96c918ab30f9d742d92310061ebae85b2462018bf8750b648c55787ceaa16c9188030f5d542d923100656b9285b2462aac5e75ccb648c4018baeb996c91880637e1d32d923154e2f3aa65b246200c5d754cb648c40199ae4996c918803a350932d92310063d3ace1b246200c79759c3648c4018f6a5386c9188031e54a70d92310065da14e1b246200cb9429c3648c4019b665386c918803364ca70d92310063d3aae1b246200c79755c3648c4019e4e2b86c9188031ed4970d92310063ca92e1b246200cbb425c3648c40197284b86c91880336cc970d92310066c992e1b246200aba80d92648c40157501ba2c9188062f21d425923100657b9284b24624f8de8
  | 30 => 0x804100746a126530082018f98788260104011bf06baac02081e3720d75580415d71c206a4b0082b9e3840549601040195ee4a12c020802ae20142580415c74c20664b008200e8d424c9601056fd3080992c020822ae212205804100c7c43a40b008208ab884481601040187ee93a2cb98ad717ccb72597315ae2e18ee4b2e62b687d879c965cc40147d09392cb988028f612725973103d2f41ce4b2e62d1a5d839c965cc4018df04b92cb98adb17cc972597315b62e18ae4b2e62b587e871c965cc40147d08392cb988028f610725973103d2f418e4b2e6224a5d831c965cc40187ee5a12cb988030f5cb425973159f0f99684b2e62b3e1c31d0965cc4010fd0f212cb988021f61e42597315a51ec2484b2e6207a5e8390965cc4014bb07212cb988038be0942597310061fb9284b2e6200c3d7250965cc569c3e64a12cb98ad38b8c942597315a71699284b2e62b4e1c3150965cc4010fd0e212cb988021f61c425973159d1f42084b2e6207a5e8310965cc4014bb06212cb9881e97e09325973103f27c1264b2e6200c5f724c965cc4018bae4992cb9880387d0932597310072721264b2e6200e1d424c965cc401c9a84992cb988038350932597310052e40a64b2e6200a3f845c565cc40147908b8acb98a2a97e0d71597310043f43e42b2e620087d87c8565cc40147d0990acb988028f613215973103d2f41e42b2e6200a5d83c8565cc40f4b90710acb9880297e0d215973103d2e41a42b2e622487e8708565cc4010fb0e10acb988028fa1021597310051ec2042b2e6207a5e8308565cc4014bb0610acb988029ea0021597310053cc0042b2e6200a3e84dc165cc40147b09b82cb988021fa1f20597310043ec3e40b2e6200a3e84c8165cc40147b09902cb9881e97a0f20597310052ec1e40b2e620087e8708165cc4010fb0e102cb988028fa1020597310051ec2040b2e6207a5e8308165cc4014bb06102cb988029da0420597310053ac0840b2e62018bc8750964cc40195ee4a12c998803a350932593310143f42ee0b26620087d85dc164cc40f8bce6b2e83988031759573d07310043ec36eaa0e629d87e8759541cc5650f90eb2a839881f171cd655073103e4e39ac8a0e6200c5e65dcd41cc4018bacbb9a839889a1fe1975107311243fc3aca20e6200ccd724ca60cc401d1a84994c19880a1fa1774583310043ec2ee8b066200e8d424c960cc4454bf0cb9acb18802c721173596310043fc32e4b2c620087e87d89658c4450fd0f312cb188028fa1262596310051ec24c4b2c6200c6f72989658c4050fd0eb12cb188031bdc962596310043f438c4b2c6200a3e84189658c40147b08312cb188029ea0062596310053cc00c4b2c62acc3f76d09658c55787eeca12cb18aa317ddb325963154e2fbb264b2c6200e4e624c9658c401c9ac49
  | 31 => 0x8200c5c65dcd60504018beca39ac0a08031719473581410046f43ec6b028200c5f75d8d60504018b8ebb1ac0a0803331cb63581410046f438c6b028200c5f7518d60504018b8ea31ac0a0803331c8635814100637b2ee4b028200c6c65dc9605040199ec7b92c0a08033318f72581410047dc3ac03028200ae88258060504010ff0ab98c0a080a1f215731814100e67392643028200ccd724c86050401d1a84990c0a0802ae613201814100578c08403028200c5f739cd65105a947f08b9aca208228f21173594415d61fa16e4b2882bac3c40dc965105730fb0f392ca208228fa12725944169d1ec24e4b288200a5e839c965104014bb07392ca208031be0972594415ce1fa12e4b2882b9c3c405c965105750fd0e392ca208228fa1072594411351ec20e4b288200a5e831c965104014bb06392ca208228fe09425944104717c1284b288200c3f72509651040187ae4a12ca208028f20142594410062fb9664b288200c5d72cc96510571c3e85992ca208038750b32594415c70e20664b28820087e878c965104010fb0f192ca208228fa1232594410051ec2464b2882b7a5d838c96510401c5a85192ca208038b50932594410053bc0a64b288200a74814c96510401c9f04992ca2080317dc932594410062eb9264b2882b7e1f424c9651056fc9c84992ca208038750932594415bf26a1264b288200e0d424c96510401caf02992ca208039520532594415bf0e20264b28820087e870c965104010fb0e192ca208228fa1032594410051ec2064b2882b8a5e830c965105a547b0938aca2089a1fa1f21594410043ec3e42b288208a3e84c85651040147b0990aca2080297a0f21594410052ec1e42b28820087e8708565104010fb0e10aca208228fa1021594410051ec2042b288200a5e8308565104014bb0610aca208029ea0021594410053cc0042b288208a3e84dc1651044d47b09b82ca209ca8fe1170594410451e422e0b288200a5f835c165104014b906b82ca208021fa1f20594410043ec3e40b288208a3e84c81651040147b09902ca2080297a0f20594410052ec1e40b288208a3c84881651040147f08902ca208228f21120594410043f43840b28820087d87081651041147d08102ca208028f61020594410052f41840b288200a5d8308165104014ed02102ca208029d60420594410445e422eab1882018dc874c9631040199ee4992c620803a35093258c410056a40a64b18820287e851c163104010fb0a382c6208030f1d776504410061fc2eeca088200c3c85dd9411040117f05bb282208022f60b76504410061fa96eca088200c3d52dd9411040193e65bb28220803274cb76504410065b28eeca088200cb551dd9411040187eedbaa822080327ddb73504410064fbb0e6a088200d1c751cd41104010ff0ab9cc02080a1f215739
  | 32 => 0x18b8cab90c6a0803335cb6218d410046ec3cc431a8200a5e8598863504014bb0b310c6a080237e1d6218d410052fc2ac431a8200a5c8558863504015b700b10c6a0802b62016218d410046ec38c431a8200a5e8518863504014bb0a310c6a0803335c86218d410052f436a431a8200a5c86d4863504014bd0ca90c6a0802972195218d41006a6b92a431a8200e1f65d086350401c38cba10c6a080387d954218d410070e32a8431a8200d8d725086350401d1ec4a10c6a0802e52054218d412df0f2a6a831a8207ccf825c8635056b8bee5a90c6a0803175cb5218d4103c6f43ca431a82008dd8794863504b753d09290c6a0802a76125218d4100666b94a431a8200ccd725486350401c9f04a90c6a0adb17dc95218d415b727392a431a8200c5d72548635056dc9ae4a90c6a0803135c95218d4103c6f438a431a82008dd8714863504b753d08290c6a0802a76105218d4159e4fb968431a8200c9d72d086350401c3ea5a10c6a08038754b4218d4103c6f43c8431a82008dd8790863504014bd0b210c6a0802976164218d4100666b948431a8200ccd7250863504015af02a10c6a0802b52054218d412df47c128431a82b4c9f725086350569d1ce4a10c6a0803275c94218d415a746b928431a8200c8d725086350401c3ea4a10c6a0803875494218d410074bc0a8431a8200e9481508635040f1bd0fa88c6a08023761f5118d410072ba8ca231a8200a9f8454463504b753908a88c6a080297e154118d410052e42a8231a82078de87c8463504011bb0f908c6a080297a172118d410052ec2e4231a825ba9e84c84635040153b09908c6a0803335ca2118d4103c6f4384231a82008dd8708463504014bd0a108c6a0802976142118d412dd4f4204231a8200a9d84084635040199ae4108c6a0802b6a002118d410056cc004231a825ba9e84d40635040153b09a80c6a0802b5a045018d410056ac08a031a82078de87c8063504011bb0f900c6a080297a172018d410052ec2e4031a825ba9e84c80635040153b09900c6a0803335cb2018d4100666b924031a82078de8708063504011bb0e100c6a080297a142018d410052ec284031a825ba9e84080635040153b08100c6a0802b5a042018d410056ac084031a8207cd4639c643504010fd0dbaa86a0a971718f7550d4164c3f43ecaa1a829de1c43d9543504018beebb1a86a0803171d76350d410066bb18e2a1a829de3761d964150401c38ca31c82a0803a350932d81410055cc2041b028200af18108360504018becb39cc0a08031719673981410062fb2ae73028200c5c655ce60504018bcebb1cc0a0803175d763981410062f3a8c73028200c5d7518e60504050fd0dbaac0a0a761f21b75581410043f43ecab028200c6c72d9560504010fd0e32ac0a08031b1c865581410062fb2ee6b02
  | 33 => 0x335c932d8d4100746a1265b1a8200a5e850cb63504014bb0a196c6a0802a761032d8d410143f42ce1b1a820087d859c363504014bb05b2ec6a08029760865d8d410062fb2ee5b1a8200c5c65dcb63504018becab96c6a08031719572d8d4100666b96c5b1a8200a5e8598b63504014bb0b316c6a080297e1562d8d410052e42ac5b1a8200adb8058b63504015b100b16c6a080297a1462d8d410052ec28c5b1a8200ccd7218b63504014bd0da96c6a08029721b52d8d410052f432a5b1a8200a5c8654b6350401c3ecba16c6a08038719742d8d410070fb2a85b1a8200e1c6550b6350401b1ee4a16c6a0803a3d8942d8d410074631285b1a8200b948150b63504018baea3aec6a080297a1774d8d410052ec2ee9b1a8200ada80dd363504015b301ba6c6a093f8795354d8d410052f42ce5b1a8200a5d859cb635049f53d09396c6a0802a761272d8d4100667c12e5b1a8200a5e851cb63504014bb0a396c6a093ea7a1072d8d410054ec20e5b1a8200c5f72d4b63504018bae5a96c6a080237a1e52d8d410046ec3ca5b1a824fa9e8494b635040153b09296c6a080393e0952d8d410062fb92a5b1a8200c5d7254b63504011bd0e296c6a08023761c52d8d4127d4f420a5b1a8200a9d8414b635040193ee5a16c6a0803275cb42d8d410070fa9685b1a8200e1d52d0b63504011bd0f216c6a08023761e42d8d410052f42c85b1a8200a5d8590b635040199ee5216c6a080333dc942d8d4127f47c1285b1a8200c9f7250b6350401d1ee4a16c6a080323dc942d8d410064eb9285b1a8200e8c7250b6350401c3ea4a16c6a08038754942d8d410052fc2ae3b1a8200a5c855c7635049f1bd0fa8ec6a08023761f51d8d410072ba8ca3b1a824f8de87c8763504011bb0f90ec6a080297a1721d8d410052ec2e43b1a824fa9e84c87635040153b0990ec6a080237a1c21d8d410046ec3843b1a8200a5e8508763504014bb0a10ec6a093ea7a1021d8d410054ec2043b1a8200ada8008763504015b30010ec6a080297a1770d8d410052ec2ee1b1a8200a9d84dc363504014bd0b386c6a08029761670d8d4127d4f426a1b1a8200a9d84d4363504011bd0f906c6a08023761f20d8d410052f42e41b1a8200a5d85c83635049f53d09906c6a0802a761320d8d410046f43841b1a82008dd8708363504014bd0a106c6a08029761420d8d4127d4f42041b1a8200a9d8408363504015ad02106c6a0802b560420d8d4103e2e31aeb31a8200c5e75d8e63504018baebb1cc6a08021fa1f6558d410043f438cab1a82008df8758c63504014bf0ab18c6a0802972156318d410062f3b6ca31a8200a5d82d9463504011bb0f328c6a080237e1d6518d410062f3b0ca31a8200a5d8219463504011bd0db90c6a080317d977218d410062e32ee431a8200c5f655c863504
  | 34 => 0xc3c41304820087d82dd560904010ff0ab92c12080a1f21572582410043f43ea4b04820287c87d4960904010fd0ea92c1208021f21d52582410061fbae84b0482acc3c75d09609040195ee5a12c1208030fdd5425824155e1e3aa84b048200c5f75cc960905558b8eb992c12080317dd5325824154e2e3aa64b048200ccf724c96090403998e4992c120803a350932582410163c3aca0b0482028f88754160904031f10e902c1208023ee1d60182410063cbaac0304820087e86dcb65504050ff0fb16caa08031b5cb62d95410043ec3cc5b2a8200a5e8398b65504014bb07316caa08021fe1d62d95410052fc1ac5b2a8200a5c8358b65504014f700b16caa08029e20162d954114c3ec38c5b2a8200a5e8318b65504014bb06316caa08031b5c862d95415961f3b685b2a82abc3e7650b6550401c5ec4a16caa08038b18942d95410059a40a85b2a8200a5e86ccb65505558bced996caa08029721932d954154e2f3b265b2a8200f0d424cb65505314ed03ba6caa0803175cc73d95410043ec3ce5b2a829da3e849cb655040147b09396caa080297a0e72d95410052ec1ce5b2a8200c6f825cb65504010fd0e396caa0a768fa1072d95410051ec20e5b2a8200a5e831cb65504014bb06396caa08031b5c872d95410061fb9685b2a8200c3d72d0b65504010fd0f216caa08021f61e42d95416bd1ec2485b2a8200a5e8390b65504014bb07216caa0a768fe0942d95414ef17c1285b2a8200c3f7250b655040187ae4a16caa080317dcb32d95410062eb9665b2a8200e1f42ccb6550401c3a85996caa08021fa1e32d95410043ec3c65b2a829da3e848cb655040147b09196caa0b5a9760e32d954100716a1465b2a8200e2d424cb6550401c9f04996caa080317dc932d95410062eb9265b2a8200e1f424cb6550401c9c84996caa08038750932d954100726a1265b2a8200e0d424cb65504010fd0e196caa08021f61c32d95414ed1f42065b2a8200a3d840cb65505ab4bd06196caa0a761fa1f21d95410043ec3e43b2a829da3e84c87655040147b0990ecaa080297a0f21d95410052ec1e43b2a820087e8708765504530fb0e10ecaa0a768fa1021d95410051ec2043b2a8200a5e8308765504014bb0610ecaa08029ea0021d95410053cc0043b2a8200a3f845c3655053b47908b86caa08031e5c070d95410043f43e41b2a820087d87c83655053b47d09906caa08028f61320d95410052f41e41b2a8200a5d83c8365504010fd0e106caa08021f61c20d95414ed1f42041b2a8200a3d8408365504014bd06106caa08029760c20d95410053b40841b2a8200a758108365504018baeba9ec6a080b171d653d8d410146fc3aa7b1a8200caf7250b63504014bd0b196c6a08029761632d8d410054ec2465b1a8200e8d428cb63504031bf0e996c6a0803
  | 35 => 0x50d6210c01d1d02a1ac421803a360543588430074640a86b108600e8f8050d6210c01d1d00a1ac421803a360143588430074640286b108600a6e85dc56210c014db0bb8ac421822aba13715884316d56c26e2b108607ace83dc56210c5b59b07b8ac421803a350f715884303d6641ce2b108600e8d439c56210d1d59f06b8ac42181eb320d715884300746a1ae2b108600a6e851c56210c014db0a38ac421822aba10715884316d56c20e2b108607ace831c56210c5b59b0638ac421803a350c715884300575400e2b108600ae9801c56210c0f59d07a8ac421802b360f515884300746a1ea2b108600e8d439456210c01ccea328ac421802abe11515884304556422a2b108600acf835456210c0f59906a8ac421803a350d515884300746a18a2b108600a6e85dc16210c014db0bb82c421822aba13705884316d56c26e0b108607ace83dc16210c5b59b07b82c421803a350f705884304556424e0b108600e8d439c16210cef55f08b82c421822ab211705884300746a1ae0b108600a6e851c16210c014db0a382c421822aba10705884316d56c20e0b108607ace831c16210c5b59b06382c421803a350c705884300573408e0b108600ae5811c16210c1155d09a82c421802ab613505884300746a1ea0b108600e8d439416210c0155f08a82c421822ab211505884300567c1aa0b108607acc835416210c01d1a86a82c421803a350c505884300746a1265308860087f855c26110c050f90ab84c2218023be09709844300c76412e13088600e8d424c96110c015a902992c22180a1fa1470584430043ec28e0b088600e8d424ca6010c010ff0ab8cc02180a1f215719804300477c12e330086018ec825c66010c0157100a12c021803a350932580430143f428e2b00860087d851c56010c050fd0fbaac7a08021f60b7558f415361fa16eab1e8202c5c7594d63d04111b90ea9ac7a08021fe157258f410143e42ae4b1e820087e87d4963d04050f90fa92c7a08021fa1d5258f410043e43aa4b1e8200c3f7550963d0557878eaa12c7a080317dd73258f415562e3ae64b1e82018dc874c963d04018beea992c7a0aa7171d53258f4100667b9264b1e8200e8d424c963d04050ff0ebacc1a08021fe0975983413fe1fa12eb306820287e85dca60d04010fb0bb94c1a080a1fe1f52983410043ec3ea5306820087f8754a60d04010fb0ea94c1a0aaf0f9d542983410061ebaa853068200cad7250a60d05558bceb994c1a0803175d7329834154e2f3aa653068200c5d754ca60d0401d1a84994c1a0803a3509325834100656b9284b1c82018dc874c9639040199ee4992c720803a35093258e410143f428e0b1c820087d851c163904011bf0eb18c72093e37e1d6390e410043fc2ae7304820287c855ce6090401d1a84994c12080a3e61e509824100c7c
  | 36 => 0xaca21a4297e0d715944303d2e41ae2b28860087e87c856510c010fb0f90aca218228fa1321594430051ec2642b288607a5e83c856510c014bb0790aca2181e9720e21594430052fc1a42b288607a5c834856510c010fd0e10aca218021f61c21594430451f42042b288600a3d840856510c0f4bd0610aca218029760c21594430053d40042b288600a79800856510c1147d09b82ca218ba8f61370594433cd1fc22e0b288608a3c845c16510db14bf06b82ca2181e9720d70594430043f43e40b28860087d87c816510c1147d09902ca218028f613205944303d2f41e40b288600a5d83c816510c1147909102ca218028fe1120594430451e42240b28860087e870816510c010fb0e102ca218228fa1020594430051ec2040b288607a5e830816510c014bb06102ca218029da0420594430053ac0840b288607c9e87dd94310c01c3f0bbb28621803872177650c430064fbaeeca188600c9d75dd94310c01c38ebbb28621802a7e0b7650c430054ec16eca188600c9f72dd94310c0193ae5bb2862180387d4b7650c430070ea96eca1886c9b1e87dd54310d45a3d0fbaa8621a96c7e1b7550c4352d8ec36eaa1886a5d1f76dd54310c01c3eedbaa862180307ddb7550c430058fc16eaa188600b1d82dd54310c01a3ee5baa8621803475cb7550c4352f0fb16eaa1886a5f0e62dd54310c01c3ac5baa8621a97c358b7550c430054ec34e2a1886a2b1e859c54310c0163b0b38a8621803471d67150c43005cd404e2a188600b99809c54310c0153f0cb8a8621802c7e157150c435158e42ae2a188600d1c751c54310c0153b0d3828621a8ac7a167050c430058ec2ce0a188600d1c759c14310c0172d033828621802e56067050c430054fc32e0a188600b1f855c14310d456390ab828621803471d47050c4304557426eab10862daad84dd56210c0f59d07baac4218b6b360f75588435b536c3ceab1086bae2e749d56210c01c5ae93aac421ad7939ce755884300726b9ceab1086b5e2f439d56210d6bc9c873aac421ad78b50e75588435d726a1ceab1086b5e4c319d56210d75c58813aac4218031be1d75588435cf173a2eab108600e2d745d56210d6dc9ce6baac421803935cd75588435b717a1aeab1086b6e4e435d56210d6dc5a86baac421ae79350d75588435b72618aeab1086b9e2c405d56210d6b4dd0a3aac421822aba10755884316d56c20eab108607ace831d56210c5b59b063aac421803a3e1d435884300547c3a86b1086a1e8e8750d6210d47d1b0ea1ac421a8ea361d435884350f4643a86b108600e8f8550d6210c01c1f0aa1ac421803a3a15435884300746c2a86b108600e8c8550d6210c01c190aa1ac421803a3dd54358843007473aa86b108600e0e7550d6210c01d1aeaa1ac421803835d54358843007463aa86b108600e8f81
  | 37 => 0x5430062eb9665b2a8600e1f42ccb6550c01c3a85996caa1a9a1fa1e32d95430043ec3c65b2a86a6a3e848cb6550c0147b09196caa1b729760e32d954300716a1465b2a8600e2d424cb6550d4b4bf04996caa1a9793e0932d95430062fb9265b2a8600c5d724cb6550c01c3e84996caa18039390932d95430070ea1265b2a8600e4d424cb6550c01c1a84996caa180297e0d71d954352d2e41ae3b2a8600c75711c76550c010fd0f90ecaa18021f61f21d95435351f42643b2a8600a3d84c876550d4b4bd0790ecaa18029760f21d95430043f43843b2a860087d870876550d4d47d0810ecaa18028f61021d954352d2f41843b2a8600a5d830876550c014f50010ecaa18029e60021d95430051fc22e1b2a86a6a3c845c36550c018f2e0386caa18021fa1f20d95430043ec3e41b2a86a6a3e84c836550c0147b09906caa1a9697a0f20d95430052ec1e41b2a860087e870836550c010fb0e106caa1a9a8fa1020d95430051ec2041b2a86a5a5e830836550c014bb06106caa18029da0420d95430053ac0841b2a8600e8d424cb6150c0156b0810ec2a1802b560c21d854300578c0043b0a860287e859c36150c010fb0b386c2a18031ed9670985430063c32ce130a8600c7b655c26150c018f0cab84c2a18033cd8570985430043f43ecab0a860087e871956150c011ef0eb08c2a1803a350932185430055ac264230a8600ad583c846150c015e300108c2a18021fe1570185430143e42ae030a8600e8d424cb6050c050fd0b38ec0a18021f61671d81430055cc2041b028600ad9830836050c015e302106c0a18031dd9671981430063a32ce33028600c77655c66050c018e8cab8cc0a18033c5c760981430143f436eab0286a587c86dd56050c010fd0fb2ac0a18021fa1c65581430047dc3ac03028600e8d424c86050c010ff0ab88c0a180a1f21571181430055cc26403028600ad983c806050c015e302100c0a1aeb0fd0b72594435ae2f996e4b2886b5c5c31dc96510d7587881b92ca21ada1f61e72594430451f424e4b2886dba3d849c96510c0f4bd07392ca21b6a9760e725944300637c12e4b2886b9c3f425c96510d6d8be64b92ca21adb170c572594435ce1e202e4b2886b587e871c96510c1147d08392ca218ba8f610725944303d2f418e4b28862ea5d831c96510c1147f04a12ca218238be0942594430061fb9284b288600c3d725096510d69c3e64a12ca21ad38b8c942594435a71699284b2886b4e1c315096510c0147900a12ca2181e97e09325944303f27c1264b288600c5f724c96510c018bae4992ca21adf87d0932594435bf2721264b288600e1d424c96510d6fc9a84992ca218038350932594430052e40a64b2886b7e1c404c96510c0f4bd07b8aca218ba9760f71594430063bb8ce2b2886d9a3f845c56510c1147908b8
  | 38 => 0x8000000c0000008000001400000000030010000000c001000c00000040130004000002800000000000004004000000300656b928530e8600e8d424ca61d0c010ff0ab84c3a180a1f21570987430143f43eeab0e860087d82dd561d0d3b87e85baac3a18021fe1572587430143e42ae4b0e860087e87d4961d0c050f90fa92c3a18021fa1d52587430043e43aa4b0e8600c3f7550961d0d57878eaa12c3a18032bdc942587430062fbae64b0e86aac5c75cc961d0c018beea992c3a1aa7171d5325874300746a1264b0e860287f875d660d0c010ff04bacc1a19ff0fd0975983430143f42ee5306860087d85dca60d0c050ff0fa94c1a18021f61f52983430043fc3aa5306860087d8754a60d0d5787ceaa14c1a18030f5d5429834300656b928530686aac5e75cca60d0c018baeb994c1a1aa7179d532983430062ebaa653068600e8d424ca60d0c0195ee4a12c1a1803a350932583430143f428e2b06860087d851c560d0c050ff0ebacc3218021fe0975986434b62f992eb30c860287e85dca6190c010fb0bb94c32180a1fe1f52986430043ec3ea530c860087f8754a6190c010fb0ea94c321ab30f9d742986430061ebae8530c86abc3e7550a6190c0187aeaa14c321aa7179d532986430062ebaa6530c8600ccd724ca6190c01d1a84994c32180333dc9325864300746a1264b0c860287e851c16190c010fb0a382c321803335c9329824300746a1265304860087f855c66090c050f90ab8cc12180a1fa1f75582430043ec16eab048655c5f32dd56090c010ff0ab92c12180a1f21572582430043f43ea4b04860287c87d496090c010fd0ea92c1218021f21d52582430061fbae84b0486acc3c75d096090c0187eeaa12c121aaf0f1d542582430062fbaa64b0486a9c5c754c96090c0199ee4992c121803a350932582430043f436e5b2a860287f87d8b6550c018dae5b16caa18021f61e62d95430043fc3ac5b2a8600a778158b6550c014e902b16caa18029ee0162d95430053c402c5b2a863087d8718b6550c018dae4316caa1b170f9db42d954352d1e43285b2a86abc3e7650b6550d4b63906a16caa18038bd8942d95430071631285b2a86c9c5e76ccb6550d4d4b90c996caa1aa7179d932d95435358e42265b2a8600e4f624cb6550c01e1a84996caa18021f61e72d95435351f424e5b2a8600a3d849cb6550d4b4bd07396caa18029760e72d954300637c12e5b2a860087e871cb6550d4d47d08396caa1a968f61072d954352d2f418e5b2a86a6a5d831cb6550c018dae4396caa18030fdcb42d95430061eb9685b2a86a587e8790b6550c010fb0f216caa1b768f61242d954352d2f41c85b2a8600a5d8390b6550d4dc5884a16caa1a9a8fe0942d954353717c1285b2a8600c3f7250b6550c0187ae4a16caa180317dcb32d9
  | 39 => 0x240040000005001c00400140000000004004400300000010000004000800100000000000002000000200500000020001000001c000400200000000004000000400100380010004001001c00400080000004000000000000000040000009000000000100000024001000c003000c00c000c00000140070004000000c0020004000000000000000000000004000c00700000070034007000000400000000000003002c0000000000000c0010008001000401a000800b0014007001c00100100070004002000000200040000024008000c004000400000000000004002000c00000000020014000001c001000400b001400100000030024006000800700080000000000000800100080000020000000000000000010000008000000100000080010001000000000140040020003000400f00000000000004001000000080010000003001c0160000007000400200200000008005000001900000060004002001800100000040008001000400000000020004000000000100100000020003003801a000000a000000100000070018001001800000080040010000000c00a000000500280000004002005c0000020001000c00200000020004001001000100100000008000001c002000c000000000300000020008000000000000040030000001000400400000000024004000000200000020004000000000000040050008003000400200000000020002002000200540030008005001400000200000020005003c00a0004002000000100000010028003001800200080010000001001000000040010000004001c0010000001000000500040000000001000c00200000040000002000800c000c0000004001000000100080060000005000c0000000003000c000000c0150000004001c000000400100000040020007000000300200000028001000800000000030000001000c0000000000002400000200010000001000800f000800400000050000003001c0000004001000400600040040008007002c001000400200000010000005002c000000000300180090000000000800100180000000004000800100080000000000000000900040080014003000000400000000000005001c006000000500000000000005000000200000030000007001000a00000080000006001000100240010000002000000100080000014002003400c000c000000c0060020005000c000000000a0000005000000100040000004000000c00000080010068002000c00000000060008000003800000100080000005000000000080030000006000c001000000200000010000003000c002000800a0004000001c003000000300040010010002003c0000008007000800c000400000000020004001000c004000c000001c0010000006002000a000c0050008001000800b0
  | 40 => 0x14004001400100100000014000000000100040000038000000800e00040070000003000c002000400200100080004008000000b000c008000000100040060000002000c005003400000000040014001000400100000000000002000000000040030000004003000200140010014002000800000080010004000000c00000000010000003000800000000080004001001400f00280000000000000800100040000008004000c00000080040000000000000300000000004000000c0000000006002c00a0000000000000300000010004000000800000080020000000000800400000050030005001400600000000000000001c007000c006000c000000400600000000004006002c000000001b0010000002000300080010008000001c000001800100080000024003001c0090000000000400300500050000000000000100000080000009008400400000190008001000000400180000000003000c00000140000008000000400c00000000000001000c0070024003000000000140060000004000000000000030028001000000200200020014002000000200080040018000000000f005c00e00000000004000000000600140050010004001400000000000004000000000200000040018000000000000200060000001000c001003c000001c0010000000000c002000000100000060008009000c000000c000000400a002c0000000000000c001000800a0008002000000300000000000008000000d000000000000040000000000400200000030008002000c0000000000001000200000010000009000000d00380000010001000001c0000004000000e001c000000000200080070018012001000000100000004003000c000000400100080010010002000400300080070004003003800500000000000000002c01300040000000002002c00000080080008002003400200040050000000000c00400040000034001000000a00000060004008001000000000050004000000c00c00000020000000003c0100014003002800d0000001000000200000000000011000400200100040004009000800000100020000004000c0000004000000c007000000000040090018000000c00200040020000000000000600000040014003000c002002c003001c005000c00200380030010001000c0000014001001c000000000000080000000008000800e0004000000000200000010010001000c009000c00800080000000000000000c000800500000010000003000800000100010024008000001c000000100080080040003002000b003800400000010000001000000000000040034003000800200180000000003000000100000000008001000400300000010000000001c0040000000000c0010000000000c0000008003000c000000800000140040000
  | 41 => 0xc0000000000000c000000000000080000064000000000a0054000000c0050018000005000500000050000001001000b000c000000c00700080000004002000c0010044000000c000000c0000030013000c00000000020004000000000000000010014000000400100000010000001000c000000c009000000000080000034001000000000240000000002000800200140050044000000c00300140010000011000800200080050000003004c00b00080020000000000c00a0018006002001200000000038009002400700040130000005000001200500010000001000000000040000004000000000a000400f000000000000040008009000000c0014000000400c000c0050000005002400100200020008007000c00d00200020014003000400000080040008009001000200140000000001000c00000000000008006000800200640000000001000000300100010000001000c00700640020004001000000000040050020000001400000000030018000000400400240000004002000800600080020004004001400c00340040010003000c0020024002000c00e0008000001000500000060000002000800000000000000015000c001001c003000c001001400300ac0030014004002000d00100000004008001400000000010000001000000d000000100040080000008001c000000c0000008004000000900140000008000001800200000010000000007c000000400100000050004009001400200100060004000001000b00000010010000000c00100200000038001000000200040040034001001800100500020000002000c0020000004000000100280020020001000c000002c0000000003002c005001c003000400a0018000001800f002c006000000600000020010000000c004000800000000030004001001000000100000004000000c000000000000040000034001000c000000000000000000000000000000c0008000000c0000000002000800200000020008001000400300040020000000000800000040000008001000000100000000020005001c006001000f00000120000002002401800000000028002000c001000000000040010000002000c000004000000080060000000001800000040020004013001400100080010028002000c000000400400000000004000000000400040020000003000800d000400900200000000000000000100000010014001000c0060000000000c024000c00800000030000003000000100000000014001001c003000000d0008000000000100000060004013000c01600240050008000000801e00000060000000004c000000000200000010048008000400b00040000000004000000a000400100000010018007000400000040140000002000c00000040050044002000c004000800e0004000
  | 42 => 0x8000260c6c6178029a8000894800024f0a663f31ebc3fa00b0365102c0a4800000014b87e5111e5e280000000000a7b2116000231a6bca780000000000008ea7c1044a00000000000b9e0001deaa1b9f8600000000001e0000013d000000000000d1c9131c5c33c83e8221836a56a00003ce16743da9eee3aa000000016780b38f1a87180000000000000000000010e6000000000000005e880001088d6c52c93b60000000671a48c402260890e1aaa3eb80ec0000ef26b5a79a0f003181b809d4562812c6218000a190000237800047b8000000289800008661b883344f716fe79083268259d5e3558748482800081980008248f4a5bd07da0000000000000098826220000000a8e1e0453700008e713f66cb15540e203e456f8002000000073b8e1469200000000dd60000000000000000000008d6a16200018520002598a4b161878f283e8221afa38d131c0baa2144baa69c0001836000113a06f07bc8888628000000021194e20000000000000011d96500001a081520000000000000017126118000000283200019b61da910a0002474a2a80001fa00008a6800e440825a00007de07c190e435000097d000068380000d800002b8000003917c879f25b200001ac00000007d0182e66e91ae00001247ed80006c10c4600000009a2a2e20000000000000003b8000940243e1481c1a000000000024a6000000052a000024629ae1501dc600000004a180009388eae0002264958800000000006d100004e78662000081a0001c905fd10bca320000226800005a80003569568296000000002c60000c263e800000c880005e119ca0000000000168e43393a4088291e654280637997cc0242638425a6a083700001ab9bec0001432000124692880000001c6a6f61ed2000116ea6c149a00016d865f00005de00003180f264999f460000dfe5aa1ac0000088400021b405b80000001960000000000000000020000a5c831e09f81d475200003948000002994e000000073123c400009b8000138a67a0488a82000c7620aca000000095212a86bf08a66fd1c3e3699d207f58b4240d80000fe000000029d00000e2a2a12692000006e2f6294e839000030f203a1532426000000028289f000003b600018662f0899e81b83f40cd95ec19695c60f680008b100000000000000143828980002e51a1a00000005fda3d687b162c00019921f80af2157822c14c8c823a9975ea798aaa73580000002166000030a00000000000cb400012b0000000089b9bb21e892c872e23563b805900002a0c405944e6008000489800063317ce000240e00022440002982499046e8419f1c885919e0b019cca8f80007ab1a144fc286055616f8119221063f800000000006979f38a17000024b2160000000100080000004003001400100080010020004003400a0008004005
  | 43 => 0x1874000000053d1cb4767a1101c000009f0212c0000000321800060e8e2e000000017e80009f280006b28000352800054b000017c00003f886468b28f907e10000000132a8d7a55046da07c0000000000087476384004d20a9a86f130294a00005cd91f44f21faa2a70a247bd215e000233c16700009c9821a000000000011d67d8000091e0da836280009c186b0000038053c25c47650e325e09860000089854e25ca0000d649cf14a200000b401b1d2e8480848000255833080006dfa39255597e231f166647c0fa83f1000014d15183a806c02f4835408a0ca6948a6940000000944205023b257e3b3103e42fa3bc00010142c599100000000000161000028228d2963857890ac26b27e888c9cba657121800005560000512a2484c250c00000001fde63102d257700000001d246f9800000003766059c921fd02e600000000001dd68d19e743a000000000000000000013121aa61300000000000000000087b8000000000000000000000f4271d00008aa1822125236200000000001906805000000019c80000000000167c0000000000032a0000000000113878d9f268c2a11a0000000a4d87287f2800000000001d2a00400024528e589d60d91e6c0001cd82b50af67769a8613796766bc196e0af99a01a59c12000000045d000000000000000000000000082c80000000000761800000000000001bfa0000acc000000000000000000000000000000006740000000000225400012689ae0000832800064e10aa5d31d7400000007ad0000a530bd071e15e437e01f85ab22786ef19ea8628000000000003a0448000169092606c665f8bbc9bd8000000012885c121a2ef98c82171158000294a6cf80006a080003518034a048c3a074a0bc1df0f8c99912a275b888e00000007710000000024a000237000000000000e600000000a11189a36427a696b2704069800092818b8a600000000000000023760000000446a61e0a7a90e0000000000060800019980000ff2273098a0732884000000000000000001a6e8d40000616947e0001d1200022a40000000425242a0c20bfa000228848b105e0001ef8000108a0000e4e1f380fe12e80b878f800043f80000a980006e00e78000000053900000a700007d3a8483e7000000000007fd205400000001dba5785ed8aba000000000000007db1a420000e9a5af9c8007a8eb892924fa31d8caa32384b87269e0e91f9d58270817c9d212b221083fc72c97645568eaa52300009a096e200000004471526229280811480003a49f62563a95e31b9db424b801c83d1030000285203d07b60bb89a846e034088c19ae00000000001da200000000000000658800030182f60000d4450a89161c780005b48b703bc23dc2370156a138f8a947919851924c29d5000000e00001d980007a621686afa4462b425d
  | 44 => 0x4de80000000000000191a000000020880000000d429048000000000000000003e200009fb00004bb29289b82a1a5fa850400000009de03d6000051c2302540106a398000000000029020001542000000000000000001a743be8406091976808622ee61280009c9109a00009121721d4600000003ad05cc0000000000000058894f813d80001b58a4c00024808ec22e48ab914ea7100000000000000255c00000000000000176800088a9ac87f400007410000000000065622fc00000000000272000000000027c64de00006ed9afe00000000000000850970c000000000007849db2186193800000000003c580000000000000000000011d43cc00000000000000000000017e800000007750a9437427b80001aa000012de00000000000000000043881ea1b20000b6ca590a881dc034a01c11224f9a974617a2409670d1400000002d30c0a00000000001f64303163a2fd09280eb90323d8a9860000ba884b800000000009a180000000000000071272f80000000c30930000091ca1880000000000000000000001bd83a400001c4000106e96594de00000001141f6e62f000092d00006ee1fee607958400007a400000004161e941cf80008c5800037c97dc00000001bc934a91a8000187954a083aa1671e8f327dd1596000225e000252c567000000000000000000821916c80da71493b0000a3aa2faa431b4e9a929b833d800059aa374091000000003f02cda81a52d9b480000000000000034d288880380000a69a0000000000000000000000033ba8407781a3a5749a44a84290a880998621316a0000063275f88686db9e72673a2f201000007628000a0400000001ca600000004a810da9651a9c65518b642e800002f85ec3000b1c10592160001ade0000844000000000000008058000000000067b9ff200000000001ce651c000000021c05c113423f68a982498c4e37882e012f8000427a2fe93c0dbe64c1a4c54701887ca000000025aa97f890e00000004fd00004cd8b4a000000000000007b0035e9dfa64e9fd8faa3599a4aa76a0602440d1841c950a96314ce14789a63d99686000000000000004b8000030c922000000000001ed036200000001c6019d81626b600004198fc200001c82c2843084f1ffa000000007285fc5e180004d89322a3500000000000000000000000006d500009ae85b400000000000000a1888320001ed80000f480000000000000000000f2000000000004244e1800069f9d1e000115c000000025525a844400006a99e1a00006500c0a65001d248e25a000000000001931c58a828f7896494fe0000d2e4a000000001de825a9e60000248674016803fb250a324a8f807da4f20522180563133a420222800000003af0a5a0b601960a0000006005bc33010c84f5136a00
  | 45 => 0x215400000006328d304f280000000298765927862e8f7a9a100006f880000000000a3080001269c8400000007b1a9160001bb000019be10511f6000000095c08c252b0000000000023a0000000137e16e800000021d4408000042d0c9e000000061b0000000000000000007c60152241000000000001100000000000000014ea2c885c254300003d38000333800000016e82d79cdca4d00000000000000000000021cc92d8c380001fa66cd800000014e00000000000000061000001900afc06914221180000000250c0001c7c18e23ee00000003280000a31000000029623b19efe32580000000000a7ea2669d59200a570ec000000000000000000265a98a927292f0000000000000008cc000000000000000000cec389a24670a0f2c0001e145b39c440000a2a30f8000000000032a000082884b6a200d604dda04a814800083e21a42e41cf40000c420000480371000039e87965740224000000091700000001abc000000000000007c4a5560001cd060c18f49810abc9b4a6ca0001c72603956e96091fe2d00cc6000000055f80000001ce8000000000029ea9cb15ca000013e962a54228fa1468bd260000003c44a991cc63e00000001418006827a2dd80000000e3611c88d842606a4000149800022dc000290622b04b400009700aa0000000274480825b800009f2000094c758219c266a87a000265e91da4840002690098800023e112e778911602ea1e22808000a6824360000c083b600006a380003088000705800000014faa7281c2000007a364a15067ca4b21978c20a1281ec29a1cc283d92c20000000568179463a00003f280000001f5679e00007de800046b15283858c94110a0423af80000001ebe418a1e08ea01de2f392be7a1000015c0c641040d1e51d1c38000146e3db1d5c000215800016aa77d800000000000000028903000000000005dc000085e80007d0a06822a0000000055800027702dd1a8a0000000840851a2878000a8c06ce4a680009c081901ea9f80000000000025ee0000000a2f05c42d900002ce946c61c25d623500006bd993ea598000a39800039200440000000000000022300006a780000fb012e6ce05e800007202e899f42be97fe00000008728000000000038386564bb80002929b883052586000000012601ba00000005e582f40000c2a2a5935227d11501f8800000007dc8c200000000000000281600000000000000177aa360001e1269f03702c480000000000000049e000000000023e000000000002a2ca8180006da9c5a80494869cc9f2c764a3543328000a7f000026720d8000000076f00003bd8b9ca2d00000000000000087c99e1d0a0001ba61b200004dc8e8400000008c90dfa39b229436d992c0000e6ea3903441d0240a75da8c694c12cc00018e64b9917639a96943f507f071980
  | 46 => 0x257451d800092a80005058000a2c094a58a935600019246f48000000000013909fe13a21fe0a1085200003a600005f8000000065c9f2ea6408b42fd800095b18d086684448158000000169e6d600001e50000041800040405e2000161e0001f0c05b0000120800036900506fba5380000000389058ca2b00000b589dc462861600000001a180003728000000000003080006c507d686a00005bf285432ca0e259703508b8080c1bf8e4a0b2268e3a7905434b032e8cc01f487606a21b088008000508000000033802da115902a000054e000000000005a60000aea573287400025b6000000099084ec15fa2588df2a3a2fc0e065441d7ca4f27942b5800022200001ab274e78d264c4e4924c74a0000224813600000007ac00006fe00000001ab687a1caa00013bc00020d08300000a73822a00009a44af0000000000051091b00001fc2680926068e0b529d28f286c4886e1fbaa28266040a07603240000b6e6eb1a6400005425d1800000000001950000661000000000000001c2000016460000eaca4624346668ac495924322a99180000000000014ae000000000012324fa87b0a75168800000001f626760001640000263a28700006ed22901a48b783371b4c0f097fc26a80000000fbc5120f0640d18aa35a07042278fac2b696c6277a1de0001148905254c1c1800053ca86c0002196000152400014461bf11aa7cda39420b90f8000272809097907cca46c02480325b02220973800088e28a400019b222c800000023d4772a7660000636000154019c0000000189e041000052710ee26e94da1ce20180001f9851112aa000234e000000042b815a86781c60238000327000000027f20000bb8a67800091ba82c012836c87da56616a800062a1cc800000000000a0c00000009b78000000000016b858e00029be76d91860000f3e5f40000000000060a94527ab800000000000000000261a0b881c80002610dd20321b626849d1a9b400007b0800000027884b50b6200010ea57d0b884e81c180000ad8000000000000000000cf00000c68000000000000004e000a69c3041c3c602149468d86000000000000000000000000128e000000001f092400012ac45f0d7e00006180001c4a0000000000241e8e9800068aa82e0001cf800011463188afe0000f1400022f8000019e00023187e3971e48883d086892e215d95f25b81508785869a441095e22423b82c8202200014403a080d0a8885d66bd0bf2470a38646915fa000179e8bc0110000000000000000001d3600018120000000000136c0000000000086c4e4149e000000069708ce983966c04f1d16000004c000000000000000001b9800009744000000925800036d00000000000000000029509907d100000000258000000000000000000c5000000003d60000000160200000000
  | 47 => 0x10b000000019ac7040000876800048414a600000000000000000173e000000064300004658b0484c926e0000000a5180003d510e21da24688b08fe0000121400000000000da24c6a80c38100006dc00003ee0000000000000016c2000000000009c000000005ac00000000000000003a832169844c014266e069c113000000013544fe1b101dd18d65c0800000105d483f8c783cd8f460000574799823800000008c780005d724ca15a9fc666a22d208f15bc8aa800000017d84110000000000000000005519e3a437913c00000004e9894e0000b3498b80007898000000000000000005d480003549a803e619fe44a00007c9236c93e01b20000000008000000000001eb000074d000000007b2000060e41822ea1f10bc62a320e60000000000000000009640000000933a42c00000004eaa58455b00005350000000000000018a6a6f13ae819072237c083483383741b50ce80c48b2c62618fa14a87242e9229621905680ac1f5092a05b8305800074f220a90a1bd475886ea0360a4830b21ce00007422520000700996a0dba0aa83c14c6a551ee40461ae80000000000000057815ac6b100002ed8732000110e7e88000587000000002f295486aa40f27e288d15760000000000000078881e04961ad081c0b66a491f0e23193b80be9c8c66d083e93503425b111be0000d7a91100ae98f28782df842e64611a281694c24ae0ee60001dfc0000000918000058fa956000193a604118c6a5800000000004ad17320000abe000000000000007e58d583cba98e798a74c00024925f099143e7a87c6948268736902e67898b0000246600000001b6800070b25ec2eb11e250f00004d79f060000000886994041692486210856a4f89c6918925288f06dc4e59172208033c1380000000000077c07f257d949086b18f61b48db009325e05f693ce00000005c217a848fa15634f137c0000000000003670c00000cc0f8432280002d5a1d09e58804306a89c0f181a000000000000000000000016fa2c01bb00000001cc60e1800000020c400000000001e5aa3d29cc8e30ed000027f815b090a089a33a00020944ae9cb60001a3600000001fe23f80000000000201a00000000001ae40a09fb40090d50000116a5f1000090080003791f303841582a22a15a0000000a5b0000079000000000000000b84386a3aa000182000009a20000000043a27c00000000000000000000099523c6000000082e80002cb800023580006778eb234000003c28000000203261f9d3a038977212f040e1e18000048a89600027be0000e0c96f967009200008d800001c5002e21c1b5a5f9000018400001d112401f40716a8b800034880005ae07b400027742f712340000ae600000000002074000227079219d83db80000cc9d18288000007f80005fc8000670127e6d580000000
  | 48 => 0x76800000000fbe5a1062e14895789b99c061228000a050d4800018087d200000000792a6c80005a698d84fe846a89a1a2c28680003e3a784969010a48300000000000000000000000004d009d200000008f227227de000000000000002738520000083a000000003940000000000005c0000000000000000006f064b80005758000a1d9e0c75c00000560d76260a7a88ce23847809a188171e505d39ed400026a61e6089c9741b1a7070e400d613c46900000000087600019c4a3b800000027da4c1274694580000001f8c77b863e8c880ea3f71f9269b28d2000226c0bfa8c012b8000000012a00000000650000000176e000180029f178c843000000000008f29e6e00000004208b980fc9f6631798e036c90ca5d9a83a4729b0631aa3e8660000000011de000000048a1d0289c8d80343a9ba67f0d9e000289a000000000023b400013ec4cc24fc1e3a42e078a70a22000000ee1088000000007f18626958254931a7129f20d820000000a2ba7180001bf60001ac600026364a42090916029600005967ce85e6886133438a000084d000000025e20c40000000023e000292a880091a000000098680006ce8000000000000000008e0061c6f794b011b03a0225a5060001b2e0000dc667e000060d29109e7146093705fe0bf0b1e251802c874800000009765478f0848f1ce215908f27b59f148d490d00001df200022d05450000264a3480000000000104600017305fc1af89a5a4c80000ece84c1fa47bb0000000000056a84d800000460018b966258526000000000008147418908000000000000008c80000000027602a80006ff000056c80000000000000000000000ac0df8000000087e57600000000000779800000011640000000000000001aa4cc92c055400019002c68d2400000000001de43dc163661e176c42d9d3800000001f9255e00002743061ab294d9fd47f70d0c7b28000000034803e8f5e51280009de80005f9a1c2000288c00000004249ba28330d8e96e99f0483800095b800000026ea19e25bc0d3800023f00003f20566000000000020a808d02d08da80007b8843e00027d483780006d9800099498ce13c800000000002fe000000000000000ede16780000000000a27938837b00005ea800075a878a0001dfe795a74215f223e060926c52f8be240920a0232a6f8a470f403410a5c25f142e0ca24ee2721a1c53f2720481160c9b11c70733039a55c036280e05780000000970111819080004c915128f300000830000723800000027cc5c42804000080a4f00cde0af000000000000f30df60000ff60d69fc4000000000000006b98000000000000000005538000a0a0368342800088d847c9b900003d70000000145c0000f12a2c815c41a00a0000000000016f05d100001b9196c6ca94366918e1c65d112a
  | 49 => 0x159a00000004a0976213c0e544d6904a4bc20246759e4405da9a4a6288407ea12d89ec9ec40000d7c760800000000005e8162e7dc00001dc8000000000000000007821f5a1e300008e295626748000000115456d11780000000000229800018ec000159420da3d001e237a000000000000000001f7e00008ee4ff800000000000001b2400006bc00000000000000a0810c000019aa7ba800000022e8772107c8e8080e022907893f9ec800008a22c3080870f1dbaa3c13448471b865de8c4c4a217ec0000deea8a80c442c202e58280ce99b19ec89a912075b07023da0cb032b1a300480830064a87e4e11e6a58c9cd20e603e600000003b58ed2294a7fa1ae941c9ac00000001b4600000000f780009311cfe0001e96000000056c115249daa041a3934e71024de7f60a3a000028a0000000000275e0001a54642190400000000000000a3583b0a3702eca7e00005348a120001f9e1ac800013897e073c17980000000893800000000000000000000000038200008b20000000000064f000000000001a5000052e809e0001be400025de00003fe0000ee4a060a8623891dc9b680005c617ca00028ba835800000020b08db8132552000000028e098094d80001b401e70c54000244e00022746a500008ac80008ff84a073504fa97197f800000004a700007df000061c958800000005a30082000160874b12ce0000000000000000000000001404840233604200429ca80007bc800000020824b922049ed80f00000000000000000025cc0000000a1780009c2000003800000001aae0001daa00020e04f09050951098c000000000029e243b14540d7072a7390000705038ca548ff89ee855217423146cc8f1059627927c828cc14a18f00318000000234c1d300007ff125a71213101690dce63a85b6996000071900008611bf20b30698000206c5da800078c296e0b91a3249889d8000000011d26740ce00002d5000000000001cea1522380000a520a188e08fb60000fe6640857aa890c3686c1f5e000155e189006600000000001b2641d0a6c00017a401a1a040000372139a97029d07647700ce24761824000000082604ea0000f0c00021e669d9fe085d1c52222800020a22ba576a17802d8dde03593149c706807dc920625ea40488b0a907739b1e04580009679e10000000000027dc02113e20000000000000059119e600023021e7800093d0000986282a407000000007a00000000000000015880000000000000217219a09b00000df4982a5247fa800008c183c0000000863200a0001d0c50a00009fa80000000f020000000000000085a880613197d400027a425480002b19a3e25700002058000000000000020467a700000000000000000000011d224e29840000000000000000026283cd000000024480000000000000018b0ba0000
  | 50 => 0xf80004d1811c00000003d5829049ea65c49a800000000003d8000000013ee00025b4000273623d000058d130a000018a66c19669250e620000cd68a826d61b4006200010e07f6800021880004a2800099104d400000000002260000159e00000002be209c00000001dd95900261c241f328d85b421f459512841efa99aa09863c35a800012380006bb25a057202ba11e98ae1ad800000012e828c065c46480006e7a2a615ca0da00006ca76e0b18000000000024643ac00005cb02120000000000000000006f8000172037800000001244000087200000008161112943a78c4bd000000000000000000000225c3c8000045016b60001f1e93984ee346800086429a2350008c00024d6504853c03783060088f8657a000000000001230e7c4fa000000022aca209f0869c8e7e0e71b8a451000088780002aa00004670000000000019626b45ca9ce0a4c26aa4c494343ff800000000008680000a0d9eaa6e70000000235c8e6800076b925c2a91a161b60c721818000821051000000002f900000ab8e9644d9e180000e20146268c00000002d41d982bb80001b303eea5805986e5203e5cd09ea00009e08ca917a2ff203050380005bb800000000004e5105c098000072900008f38000a620000000000000001a80001aac0000000000078800000bc0bc000026d00000000000000223a0000000000043a6a9000000000000000000000000006d9f1a00000004bd800093a00008e7a4d2102105657fa08a00008604be23400168000000188e27d8c84281902688b800032b800000000000000000000000066f0a323b50502a46a518000079a00017d64b69e8a96c275200000007f8977c9720000000236400000002cf860237300000000ae28410384000277c0550fbaa2a24f6000000045c1d227591bc84cc8e4486b80009da80006d715eaa7d80008f09c080000000152800000023ec00000000000aae00004fe99226881a09ad461104a200000004cf28b6a3a00006751a685aea450000161a0000000000000039d0af08f88ab400004aa5a91c224c31aee00027a049581a22c0a590472000042180488820db82dca56a39d8000000000000000000000000355000000007d2000000000023d80000f9a8ac00009168000000095a2141aea531000081884d27a9a6c27970b107eca8ce35c09663bb08c83eca7b413f217686626068c38f966190000000000000009a000028da00001dc00000009cba0ee506800000012021a98412000000000000000000b600001d806ad0ba61b980009b3946a4a4813a97e156a84a1064000033a000000000000008b780005329e8000001fa3008000000000000021dc4871f162ba0a380000c0401c8000a77a3c03f90014000132824c8000638800029880000000a64000000000023662310000a03876c5920000a0d000
  | 51 => 0x20a4629000000021c418aa41a6e3807e52480005c685c6a87237e3d10000000000085b1cca5590ad20001b0a429a148000000019999340000000000252e8ef9efa7eb9a607c2972e5fea3882b715f00002282079a99400000000001a0a59785d2000001e1869ae209f176014e00000000000000200242400000001b8c00000000001b5e00000002e30000066045c70c80000b123f4000000000029c6000000036700006eaa5e684f91f8773143a5ee0fd29ea972661f00000000000000000000006be514066c0001fa008297287f0000025b22b464d80000000000000086a58c000005e000009596dc0001d7288900000000c2e5ec0a140000000000000000026f0000194600007fa01500005dd14d60540f4c67909e218998887bf00000001ee6406144c42a044e00013b428b98de0c70b800000ef41df80000000000200800000000000000fd8000070e0001bcc7fa1ea835c800069a964260e166e82b071038026f468800003ed1acc8ed93d600000000a88664000001287a8a9e000270ea8980520000b44667a84600000004f1800000000000000146000000019f8000000201c8a0281c000135c0000000172983e645800000010023960000000000000007f693aa6a22b205ce00018c200000007ee80000000c74a5e000026ca04498b0a2c4cf800000026ec8a28e0a0df0e98922a96879304789b211241098000000195e541053e0000000000000024e80002ae0000000000000009ce00020b4000281e00000007a4859a4030000a8f1bd6a14039e0000000a3c8f52754095600002d41490e1e46a1506000000000021361118cd099a800000000000000000000227a02924083480b9a00013be0000810a34000000010f05fb8ca26da00003320b8e4569a3400019905a58ec848e032c36100000d3212a12180005e225fa000063a9e7831aa3f80003f002a4a000000000073412480004f80000000000085f0cda94703b2a7b80000000f0403280006d400001ee10a400009b600017be0000be80001dde66300005188000000000000018fc00022c68650b5c0001882a54000005c0000a5101ae0000000000000054a800040e80005ac9c962bb00000001b6c8839aa222c0a0800024be96b800056e1c0e29fa73e00000000000e1803f1b825eb27f4000000000026be41ea4420001edc0000000000210800000000000bcc0478594573a12460602520d1a9c800001da8ad93820001e5432fa28c0639b4a00000006010f2a1ff80003ba800000000002800000a7fa69a274040c95d9cc04509eb600000001d19f0299c15c47ba2456130250443f1012a7600000001758a8480000000000000028c00006882179224a74800000003c803026bc14322420000882802000000008b658f253c36b80000000000596a4900000000344000000000dc7f
  | 52 => 0x1640000ae474c08ba8da00008848a706ac18c67962630115010c3290a78000194200000005c0192800000005a49b34853845e00000000000000000000038c09583459b427e2081c000000080a80003d9112674207360e0800000000000000000000000000000009ef081e9518a80662984254d971c000254e000000044d000016199524cb201e0001e40000000000007c27daa37880f1d429dc9c889f4a358540948e06a96cc37a987a32da5f20fe800092b00007e2800034d89c40000ee27ec00006a200864b400002128bd408c80005818cb88b380008cf800017d8f7e3a2800000000009ec000075000000002568000148a216079039c21ba8eb8e8e4bf10040a389f800000000000e8605780005c59da46a415740e4800000000000000000000000000000000001c34000000000002060002890a1600009c4192043180944c617ba08200001770d5e00011da0000000000000033100008200fa4000231274f80000e882aa751200647c8000000000012c8000000000026591906b480000f5000000000000001b0843a267a4a30fdea2380000000000901973ca4e24da00000007771cce79fa63e4ce14b47bd800020498807cd000062d12fe00c164c0001eba95f1bf06c080006cc153c000068a000253404e00000000c1c0000000473800065103202ca00002e4800006e293a28d00000000000326800000011ec6e801d654b8bbaa029532005a12227900000001b0072299484d800000000000636802683c8e565b78000958191260b1c4c00002ac107858a6f088d00000000468000000000004b0288600000009f800009748b0618494680001b840001a700001c6200007c60ee8000896823656e80005e38000303800000000000000000000023a7d4800056ba49c000000095280000000826000000056995a45198dd811686a800021b6898998e71d800017823f0a3d9adc1a3121ea7a00000000000000253e00000004120000637214c000000007c9f9c79a27de00000000a829e400000000000000000000070100008871366000000097c071a01815c2310134c2390000000071c3391d5a97d80000000000000000000000000000f0e00000001a10000441800046098a2000016062f80006dd0e2271f81ee0001976834800062b082a000000000000004b5938c000025c00000006d8000000000000000428000162666707ca7d50bb079180000000b860000184066893e7631c6c1188000a4200002d20daa845147809b84f8000266e4ff00000000e380000000a3f275a52a8000000000087e0000a3780000001cac94800008f9a1444c3a8700000d329eb8bfe1be9bca3df000000011b4136918401383ac82fa9123fe9e7a00000009a000000000000084000073e8000000206a00014887272672000000024892367cf269e693800000000
  | 53 => 0xd1000000009ab035643c80000001fec5ce0baaa32936846214720f3814c4029242080a74033a80000e2a29219c80d418d0cf463c8f1c5c28000000181a00001145701600170094441011566160ac06159bda61513a23b700000001b7647e8ade93402f8a4989ca00027fc0002118087125e4799a7a0000000164800000012501f20de800003961620000000024e0000000000153a19f072c02899e0850234437718ee0000a728b600001d382709c00000000000077480001d5000000002c200019260000d746c380009c78000533000000029e04c2180ca6580009e8800061200000002940000000012b16d6a8c80000000000000267c000000068322869e4191c294299200027d60c526c01608a4019b8c901e01ef0575000065ea6140ac8ebaa10a9b69f10b7c000000039989780000000793800026512b6000131632e80003630000000232800000000000fc65d5145873c961624a85d82ed251259a000008ba7e673b00002ab145a55f002a8639662a6a23d26349a282ac94bc95ea00c6a323fa14d80005779dfa000241c0001b0c4f4a02800016f2156a97c00016a687f00005d424ba000000000000008298000000297e00000000000fd0366000000010d80001d5200023f20001bba44b298c00005300000ec260500008609f760000000628231c4e6800011997146b80000000000000000009da000081e1fd207a000000000000000c80000244a3a90bae5d01ff0276819c0000000000000000000000000000000129600000009268000000138e036a0349699f4aa0f1ee053b83907a9211e9899850445011a7b7a2cc8f90bc8000000071580000001988000000078b00002f2a50800006000000a42a480ff47d7097e000174a0c0124e00012a42c2000016c8d9a00014e60001f90428981c0001a66669967e6e91500000000050f849047f0000a2982de4280a6e24300004068ec47528a7681319781eba91449f000000027647f98000a5080007ef80003be000000007620000000504000000003a800013643720a9277e16603ff000021e0000894000006181c061a8b2a00028244e604207a18e463990c488af8e029d800008fa83b4000271a000000000010d600007e6397800043486a003d8bc03c78a8e000000000000008ec800001da5dc5e6953050280004b2a13882397a668980000d9800000000000001d6617d261631e800030900006591a2e9cc13de3fc1ab87c8867a8449a5a5291b641c6045841d8b820000dba18500000001b92000000010da8fa08118c000009ae000205e00017b234a00005b68000a2f80003bb80006f38f740000bee949985c2f980008ee8000a1300000001d5400000000000fd63848000000000064a8000000273a77610faa8385e4000267e73aa2da8fd94c0a850eca44000000001c6e22b9f580d489000
  | 54 => 0xe3a4b1800000000000001022000000000000007a080000b29be842715668e88e9c61a16046aa0c1200026fc00005a0000000000000009eb00008499ea0872000065a0000787261c968866a6f826fe06d27d800000004a61a62a70113e1060000000000000000009fc09200000000000000029e9e520000dda000060c000000000016f600000000000c10022000011a000000026c642c9db248e88fa94a968a00010e4000000000026dc000229c0000000000108c0001e060e38000000000033480006c8000011f9bfe03e054412900008cc80000001da81faa59a6ef91e465580007c0000000000001338f2400000003bf0000216a75800004d0258064a00000000001dd08dc81745f00d022588000000073c893000000000000000000000000000005ee017800056894d000029dc97a000069e28669cd2a0064780000000000000104c41fa02c00028ec0000a4e8f69fb8797800000000004a7974200000001912976000000000000000001e320001212625000000000005af00002f69e2a00019220000000394000092b803c6df00001ff000073d9df472789bc2ec800037513e46f1800031696640001d9a8921dbe00000000001672000220c430883a4d4000000022f6000135870280006879b1c532083c6de29aa000081800619f60000906975245400015440000000000230459380009980b3286f80000000000a6b00000001a502da8ce6a0e14140000e420000000000000000027760000d3e000000000000006818000000000083a8546458800033f8d268a10c4a0001d14000000079d9e902faa8e242e18905a8a97a3dca6b20cf9d324330dbc3fa95506f7056e0de1a22000000000000006b68000000000000000000000000767000007380001fb00001de00008b98d1202700000000000000241800003dc000145600008fe7079bd089d8a8a000140c0000000100800000017b4000000072f0000000000058905f241c23a46528000761000000013067a38584823122a71526e8000278e6a6091c442116855c80009058ccc2cc091e78780001c2000076b14e825b800000024305df89be50b132ea7c90c41ba087a9e297de9f39370000222640780005ab80000001f827a7800014500002139b220001c4200000006d4a14a3538b3c61da1a60002580a2510068a793aca1c969c3ce8f940000000000003e00025c270b800010f000000016b467ea5022841ba85f19552000243c94c875c4371a92000000014b261047820ae49d116687c800000000000000000254000054800009790000000290097a80002a802b40001d2a62ca1f099980009928000000000004d0aa224500005c39320000000000000000de80000001dc25e713b0642924a1e0955c4b48e5a927a76271783bc000000000026ee0000988a808000000207e0c31
  | 55 => 0x8000000000000000004dd042a00000003e081000001fcc59e91d03198d620000a60052902827f00000000fa60c591c6000189254d00008819e9a91000002349c506fa800066586602f59ea23220000000000076c00000000000a6710f600023002c929f432f285a9be8a16050174837f04b09e1800000000000001d9046f04045880ee833e8b140001776908a28e63922b833523fc0f28e2c8bb29043bfa63472500007219d260000000000000000000009b6000000001b05c916140000a445b209720000000121195a10c8000000000000000000000b3875589e6000000000000004148000000159245780000000000000000098480000000e6833f000000008bc835000003988247aca4d805c8f50000000000003d80000000501869e0000b7a049818c0ea8604099017a67099a200000005259d1c00000003c012fa54880008eb02220000000000119400000002da0000810000035b83be917906a78e0e5c09b00003ec1a10000000073f0d963f380000000000a7c000077b0000000000083f11ea02a08e6000082c00000009890b0e000000022f800000000000000000000000060980000000a0400000008b5800082d85ea8591e8c0000000000000000000000001b1600019da70e9b9a00029982d60d2a00014820000000125800018280003dda9d600000004430000000000000027fe1a4116000000002d180006ca00007030000000000095c92700001fe4314a8a01400b5a78b8bec5661d784f687d45f48a4619484a616a1ecc6e5a7d040e25da24c090219226a827a114c00004a8168800000023348d0800000000000000000000000004c00003078a5600002b899580000a21ca283b21e47c40000000201000003f659280009d7055000002408c99f2a0000c2802680003fb8000000000000002b6000000054592f200026460000a825099e2852120c20001586000219279c000000000001de800000000001ea0000000000000000003b688f0000160ea15800000000000001ff8728000000006f4000139c500a09a0002420000104e25000000001bc0000227e00003e031c29c272b9756a1a0c983a313f200027ee4db988c3a50000a698e729c5a8b896200580000bde7b3800027e9fce6de8000a56a2bc4c98be0370973a41080007da0000000026a3cf11c44698c5600000006cf04cc0000000000021600000009b50000074000000003d25baa2a2a4885800ba13ba0001d4c00003ea000000000006de05a2a1e84e931e2281408452a55a393025e6a680006eb800000000000000000000000000000000000000000000054fa95892080000000d5c87e80003e880005be8d780001a2416b0000000209e8e380005eb82941ae00cc16c1a3ca5a800000016e4000142400000648cb24e0000000000000000000b269e6000036b000000012ae
  | 56 => 0x28662700006b080000001c4e1ee80000001eb858480003a2264067401be48ba390000000000016526e426b644ca1b8000063022518280001c987d326cc0000cf8753a4701c292942c0030413d000000000006350000769a17e000184e2bd1932677070c00000000001d0e00000000510000000000071192dc22a95804239e888438000000276e28d9c8200017220001e4a000180a5e480000001208558162831b20489450000000000000000003a41ca8a288000842a25681d941e00013d87ef04341d7800065c00009001aba5178d4c14b8278a6d000050008da9b880000000f92a86016685723101d800002b3800057b800000000003418d389d411b24952a20463800043d1eda0b712c43e015e605f91e875a00003d68000142947c98ca306000241000000002ac0000000000091e968200000000000ab60001e0a336055c0000000543a43a00000005280a0e56d917e70d80000000000025800000000000000854000000036800007e680009550000000247c9bc82e20f8850694e80000002668000000038f8bc400000000002802466942073784c86019c6851e8000000000000000002b0a0c600000000000000665000022e0000000000009980001f01a58a4b8000a1a8000000157a11c1c2a6a1000025080000000000297830e00000d234215f800006201581e64053a04e1cb811240386ee0000000188800032307506dc8980000073000015fc38f23de0000eb683e875227b13b21d580000000c58370000060c91ba09416e696380009090758553075a000000014e80005c1a24a263805670994f60001e207cf89ee3110000622800000024880000000998800000014ec00000004f30a3c0000a221b100100801e2475e9ace00000006609bc423d8b8a00027821270a284c027e441b0f225d6800054696568c300b24ea186e0000000a4ca7c200000000000000020194c1439ff630d2830809872692e1230470000000007a65b280009a605160000000135800000000000000c5c00017bc24d25fc875a4e41ad00000000c7e8b5021e24da16e72c16ec525083800000000000000000108400026ae1372a341329c005b51fac7f200003a88000000000034e810200000002d399a48cb
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x148f97d894218d100052365c6250863440016c2968862018d105a623611729086344001c0d72d494218d10007035c952508634400148e9650d7210d1000523259435c8434400188c8650d7210d1000703d95435c84344001c0c6550d7210d100052364e76dd3624400148d949db73d891000523a5b74dcf624400188e86dd373d891000703d9774dcf6244001c0c65dd373d891000703dd774dcf6244001c0c75dd373d891000623a1f741cf624400188e8750c43d89100058364e62509650400160d9498932594106f703dd9424c965041bf60d94909325941000703dc9424c96504001c0d72509325941000782e41424c96504001e089050932594100078150b814c96504001e0542205325941000d23e5d424cb64041bdc0e7550932d9010007035d5424cb640400388f8750932d8c106f7039d5424cb6304001c0d7550932d8c10004872616550c4304001c0e6550d7210c1000703595435c84304001c85424cb76440100072250932dd9100400147196d4b76440100076050932dd9100400147195a1f76440100051ca5c75dd9100400147297d4b7644010006a8e0942dd91004001ac3824cb7644010007a050932dd9100400187186ddb754401000718dd872dd5100400147297d8b75440100070cddb42dd51004001c337650b75440100078858942dd51004001c5376ccb754401000714dd932dd51004001e41624cb7544010007c050932dd5100400187087dd9654401000718dd872595100400147297d89654401000698e09625951004001c3376d0965440100070cdd9425951004001e2162509654401000714ddb325951004001c53764c9654401000790589325951004001f01424c965440100070cddb75dd11004001c33765977444010006a8e0962dd11004001b83824cb7444010007a058932dd11004001c3376dd474440100070cdd9651d11004001d20751c87444010006a8609621d110040015309754874440100056425d321d11004001b81824c87444010007a0589321d11004001a916460c6444010006a8591821911004001c5376dd7734401000714dd965dcd1004001ac38258b7344010006e0e0942dcd1004001e816250b734401000714ddb751cd1004001c53765947344010007501d4721cd1004001d80741c87344010006b0609621cd10040015509754873440100056425d421cd1004001b81825087344010007a0589421cd1004001a918458c6344010006b058d8218d10040012e1922194344010006a46194310d1004001b814360843440101ad38a5f86dc9100400156297e17724401000558a5c85dc91004001c6376dd7724401000718dd965dc910040015a297e137244010006a8e1b84dc910040015a297213724401000570a5f83dc91004001ac386e0f7244010006e0e1383dc910040015c29720f7244010
  | 1 => 0x703dd5424c963101bdc0c755093258c4000623a1d424c96110001c0f7550932584406f7031d5424c96110001c0f7550932593306f7031d5424c964cc1bdc0e755093298730007035d5424ca61cc1bdc0e7550932d9230007035d5424cb648c001c85424ca71d923000721509325c7648c001c0f7550932586306f7031d5424c9618c00160d9418932d953000583259424cb654c1bdc0e7650932d953070d83652424cb654c001c0f7250932d9530007035c9424cb654c00142d9219772d913000703d97724cb644c001c0c65dc932d913000703dcb524cb644c001c0f7254932d913000703dd5424c9644c1bdc0c7550932591300050b648655c8644c00182d855c862191300060ba1972548644c00182c865c9521913000703d95724c8644c001c0c655c9321913000523e5f624c8644c001a18652013219130006625c8804c8644c17382d855ca52191300062360d72948644c001c0d7254b32191300060b615728c8644c16f88d835ca32191300062a5c8804c8644c001c0d72d493219130007035c9524c8644c001c8972e013219130007225c8804c8644c00182d855cb21191300062360d72c84644c00182d855c820191300062360d72080644c0018a57260420191305a583652424c9650c001c0f725093259430007035c9424c9650c001e0b90509325943000782241424c9650c001c0f7550932593106f7031d5424c964c400148d9750932d8f106f7039d5424cb63c4001c0d7550932d8f100062361d424cb64841bdc0e7550932d9210007035d5424cb6484001c0f755093258e106f7031d5424c96384001a0d8460c62d95100058364c6250b654400160d9418932d951000583259424cb6544001a0c8650932d95106f7039d9424cb65441c160d9490932d951000703dc9424cb6544001c0d7250932d951000703d97724cb6444001c0c65dc932d911000623dcd829cf6444001c0f72d4932d911000703dc9524cb644400188f84e0f725911000d2325d424c9644400188e8750932591100062321d424c96444001c0f7550932591106f7031d5424c9644400188d835c862191100062361d83188644400188c865c9321911000703d95724c86444001c0c655c9321911000523e5f624c8644400148d971893219110006a8a1a21880644416f88d835ca3219110007035cb524c86444001c0d7254932191100052364864dcb6344001c0f65dc942d8d10007031977250b634400188f7460a74d8d1000703dcb5250b6344001c0f7254942d8d1000623e1383dc9634400148e975093258d100052325d424c9634400388c875093258d1000703dd5424c963441bdc0c755093258d1000523648645c8634400188d845c86218d100062361d84188634400188e865c94218d1000623219725086344001c0f655c94218d1000703195725086344
  | 2 => 0xc0160d95a014358843006832168050d6210c0168691a014358843005a16468050d6210c0160f956014358843005832558050d6210c01a0c852014358843004a3e6143dc56210d4728d9850f715884300683a1543dc56210c01a0d8550f7158843004a3e61431c56210d4728d9850c715884300683a15431c56210c01a0d8550c7158843006a250e801c56210c01a894360071588430078150f519456210c0128e9850d5158843004a3261435456210c0128f9850f705884351ca366143dc16210c01a0e8550f70588430068361543dc16210c0128f9850c705884351ca3661431c16210c01a0e8550c705884300683615431c16210c01a8543a047058843006a150d811c16210c0128e9850d5058843004a3261435416210c01c0f755093258f416f7031d5424c963d05bdc0e755093298341007035d5424ca60d0401c0f7550932582416f7031d5424c9609040160d9318942d954100683219424cb65505bdc0e7650932d954172583652424cb6550401c0f7250932d9541007035c9424cb655040144d9219772d8d4100703d977250b6350401c0c65dc942d8d4100703dcb5250b6350401c0f7254942d8d4100513648655c8635040184d855c86218d4100613a1972548635040184c865c95218d4100703d95725086350401c0c655c94218d4100685194815086350401985722054218d415b61361572948635040188d845ca5218d41007035c952d08635040184d855ca4218d415a6236117290863504018c5722054218d41007035cb525086350401c0d725494218d41007215cb815086350401c85722054218d410061361572084635040188d845c82118d41006325c980084635040184d855cb2018d410062361172c80635056fa0d8350a325944100703dc9424c96510401c0d7250932594410078150b814c96510401e054220532594415a583652424c965cc401c0f725093259731007035c9424c965cc40160d9498932596316f703dd9424c9658c5c760d94909325963100703dc9424c9658c401c0d7250932596310078150b814c9658c401e054220532596316f7039d5424cb648c401c0d7550932d923100722509329c3648c401c89424c970d923100623a1d424c9644c401c0f7550932591316f7031d5424c9644c5bdc0e755093218131007035d5424c8604c40185575205321813103ca3261424c9640c401c0f7550932590316f7031d5424c9640c40148e97509325803100703dd5424c9600c5bdc0c7550932580315be8360d428c965d0001c0f725093259740007035c9424c965d000160d9398942596406f703dd9424c965901c560d94909325964000703dc9424c96590001c0d72509325964000782e41424c96590001e089050932596400060e5d48050861501bdc0e755093218540007035d5424c8615001128c985093258c4
  | 3 => 0x28235114a0009d014001e8000ecc45d03e194b130cc55a800494004b0000000019999430a25dc002dc00001331a4723f8a52cd07000375c800674cb57d09168ee0a97557039328030684c0551d005682e0003706c4983c591240013f320da49c0000146230ec238d36795b27c2f1b5025ec320b5634645819c78038a14bd561d800658005389521540000d00fc004d11600000298c70d4d737ce605d1c5208a25995074b022000000fa2113e109570004a608330c11361038660be54c0d048822ed853502942d6021c0026880358f05ac1339d1f31852204eb638746510f1242e445005997035400000000680400000003407048000203000000e05040000005048140c060400800040301c3e3a0003800070706c18010080c02080001804010001c10010081018020f81c0a00018340208000041815060001015008003e000300802010105800300e0f8180a00008202b0080000000a03402040e00002000480402090006804030002c12110200804020182806020401400010382c00020081c06001480862050086801c0f7550932587436f7031d5424c961d0dbdc0e755093298343007035d5424ca60d0dbdc0e755093298643007035d5424ca6190c01c0f7550932582436f7031d5424c96090d4da0c8650932d95436f7039d9424cb6550c01c0d72d0b32d954373583652424cb6550c01c0f7250932d9543007035c9424cb6550c01c0f72509325944364d07a5f85dd94310d4b41e972177650c4352d07a5c75dd94310c0188d82dcb7650c4300507e5572dd94310c0141e97d4b7650c430050764b76dd54310c0181f76e0b7550c4300607dd982dd54310c0190d82dcb7550c4300507e5972dd54310c0141e9758b7550c4300683e0962dd54310c01a0d8258b7550c4300703dc962dd54310c0191875a027150c43006451d6819c14310dcbc0d745ce7558843007035d1735d56210d6928d97e1d43588430062365f8750d6210c01a0f95e1d4358843006832578750d6210c0160d97e15435884300683e1f8550d6210c01a0d87e15435884364d83a568550d6210c01a0f85a15435884352d83a608550d6210c01a0e9821543588430058365c8550d6210c01a0f8721543588430068361c8550d6210c0128e98dd5435884351ca36637550d6210c0160e989d54358843005832627550d6210d6d60d979d5435884300683e1e7550d6210c01a0d879d5435884300583a617550d6210c0160c985d5435884300703e5d7550d6210c01a0f875d543588430068361d7550d6210c0128e981d5435884351ca36607550d6210d6b60e951d5435884300583a568150d6210c0160d95a054358843006832168150d6210c0168a90a054358843005a26428150d6210c0160f956054358843005832558150d6210c01a0c85205435884300583a568050d621
  | 4 => 0x19c66c001ad9355115098de000e90018b3d9476350e2b5860c4ac5097e3e1055657c441370002c064e06851717935374001180011c7f5040065c686415041151468970d0090312e2c92a2a9a54e87d3842068000000005e0001c016270631580028d0d40c6450c00000fb5316f0014d16d8c5d9360949e4500067c9946c06244c90a0113bd9226cff38c9800051478732b8f460492070bd4f09414c453304e3f410185496004d5a55a5855d419212340053c8f0897a4c459421a25b8c0100a04806e6696d3d4900201848886141a32d0484ec442d8cd3387708589428021f1321d4a912c003c5671f8000018a000c213d6c2fd303dce2050b5000000000000000000004e0d260d4b06d235c4004a4bc00004000001bcab1880000000291881ed79448f26447909c005fd7d1518724c001c40002cd84b4a70018f00000460001705536ccf690d1588fc4a02407cea2e8af174412a0ed0d9015606a548600ac3d01c3a3a08b69955364e5000004e4b917cf93cc004f443000c10015e0016500145224570780f4ac00001733900020c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4a003081a032dcf2000c008e02814000000804500601d2ec12c5baa862180300d97e1f8550d6210c01806cbf0e42a86b108600a8128587215435884300541140c390aa1ac42180320885a428150d6210c0190242d2340286b108600e01195722054218d41007010cab9100990c89800240ca9595435c84304001e01bb284996ea8802000f00dd9424c965440100063012ec12643a2200800348097589321d110040018c04bb04a10e68802000d2025d625087344010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x6
  | 3 => 0x4b
  | 4 => 0x4e
  | 5 => 0x124b
  | 6 => 0x138b
  | 7 => 0x4
  | 8 => 0x5
  | 9 => 0x94b
  | 10 => 0x94e
  | 11 => 0x124e
  | 12 => 0x138e
  | 13 => 0xcb
  | 14 => 0xce
  | 15 => 0x12cb
  | 16 => 0x9cb
  | 17 => 0x9ce
  | 18 => 0x12ce
  | 19 => 0x168b
  | 20 => 0x168e
  | 21 => 0x10b
  | 22 => 0x10e
  | 23 => 0x130b
  | 24 => 0xa0b
  | 25 => 0xa0e
  | 26 => 0x130e
  | 27 => 0x180b
  | 28 => 0x180e
  | 29 => 0x24b
  | 30 => 0x24e
  | 31 => 0x144b
  | 32 => 0xb4b
  | 33 => 0xb4e
  | 34 => 0x144e
  | 35 => 0x16cb
  | 36 => 0x16ce
  | 37 => 0x28b
  | 38 => 0x28e
  | 39 => 0x148b
  | 40 => 0xb8b
  | 41 => 0xb8e
  | 42 => 0x148e
  | 43 => 0x184b
  | 44 => 0x184e
  | 45 => 0x58b
  | 46 => 0x58e
  | 47 => 0xe8b
  | 48 => 0xe8e
  | 49 => 0x178b
  | 50 => 0x178e
  | 51 => 0x18cb
  | 52 => 0x18ce
  | 53 => 0x94053
  | 54 => 0x4953
  | 55 => 0x94056
  | 56 => 0x4956
  | 57 => 0x95393
  | 58 => 0x5253
  | 59 => 0x95253
  | 60 => 0x5393
  | 61 => 0x125393
  | 62 => 0x124053
  | 63 => 0x124056
  | 64 => 0x138053
  | 65 => 0x138056
  | 66 => 0x124953
  | 67 => 0x124956
  | 68 => 0x138953
  | 69 => 0x138956
  | 70 => 0x139256
  | 71 => 0x139253
  | 72 => 0x9c0d3
  | 73 => 0x9d2d3
  | 74 => 0xc9d3
  | 75 => 0x9c0d6
  | 76 => 0x1452d3
  | 77 => 0x1440d3
  | 78 => 0xd453
  | 79 => 0x144d
  | 80 => 0x1440d6
  | 81 => 0x12c9d3
  | 82 => 0x12c9d6
  | 83 => 0x10c
  | 84 => 0x130c
  | 85 => 0x134c
  | 86 => 0x1692d6
  | 87 => 0x1692d3
  | 88 => 0x12d693
  | 89 => 0x252d3
  | 90 => 0x12c253
  | 91 => 0x24d
  | 92 => 0x252d6
  | 93 => 0x12d453
  | 94 => 0x1452d6
  | 95 => 0xa0113
  | 96 => 0xa1313
  | 97 => 0x10a13
  | 98 => 0x10a16
  | 99 => 0x149313
  | 100 => 0x148113
  | 101 => 0x11493
  | 102 => 0x11496
  | 103 => 0x178113
  | 104 => 0x11793
  | 105 => 0x11796
  | 106 => 0x130a13
  | 107 => 0x130a16
  | 108 => 0x181316
  | 109 => 0x181313
  | 110 => 0x131813
  | 111 => 0x131816
  | 112 => 0x29313
  | 113 => 0x130293
  | 114 => 0x29316
  | 115 => 0x130296
  | 116 => 0x131493
  | 117 => 0x149316
  | 118 => 0x131496
  | 119 => 0x59313
  | 120 => 0x130593
  | 121 => 0x59316
  | 122 => 0x130596
  | 123 => 0x179313
  | 124 => 0x131793
  | 125 => 0x179316
  | 126 => 0x131796
  | 127 => 0xa4d
  | 128 => 0xb4253
  | 129 => 0xb4256
  | 130 => 0xb5453
  | 131 => 0x24b53
  | 132 => 0x24b56
  | 133 => 0x18c253
  | 134 => 0x258d3
  | 135 => 0x258d6
  | 136 => 0x144b53
  | 137 => 0x144b56
  | 138 => 0x16d456
  | 139 => 0x16d453
  | 140 => 0x1456d3
  | 141 => 0x1456d6
  | 142 => 0x59453
  | 143 => 0x144593
  | 144 => 0x59456
  | 145 => 0x144596
  | 146 => 0x18d453
  | 147 => 0x1458d3
  | 148 => 0x18d456
  | 149 => 0x1458d6
  | 150 => 0xbcc
  | 151 => 0xb8293
  | 152 => 0xb8296
  | 153 => 0xb9493
  | 154 => 0x28b93
  | 155 => 0x148b93
  | 156 => 0x148b96
  | 157 => 0x14cd
  | 158 => 0x185496
  | 159 => 0x185493
  | 160 => 0x149853
  | 161 => 0xe8593
  | 162 => 0xe8596
  | 163 => 0x58e93
  | 164 => 0x58e96
  | 165 => 0x194c
  | 166 => 0x17cd
  | 167 => 0x198d
  | 168 => 0x19cc
  | 169 => 0xcce
  | 170 => 0x170e
  | 171 => 0xd0e
  | 172 => 0x188e
  | 173 => 0x5716
  | 174 => 0x4cd6
  | 175 => 0x5896
  | 176 => 0x4d16
  | 177 => 0x14c
  | 178 => 0x2cd
  | 179 => 0x188c
  | 180 => 0xd0c
  | 181 => 0x1a0c
  | 182 => 0xd4c
  | 183 => 0xccd
  | 184 => 0x170d
  | 185 => 0xd4d
  | 186 => 0x1a0d
  | 187 => 0x95716
  | 188 => 0x94cd6
  | 189 => 0x95896
  | 190 => 0x94d16
  | 191 => 0x95296
  | 192 => 0x95416
  | 193 => 0xc9d6
  | 194 => 0xd456
  | 195 => 0xccd6
  | 196 => 0xd8d6
  | 197 => 0x5cd
  | 198 => 0x9ccd6
  | 199 => 0x9d896
  | 200 => 0x9cd16
  | 201 => 0x74c
  | 202 => 0x131716
  | 203 => 0x130cd6
  | 204 => 0x130d16
  | 205 => 0x180d16
  | 206 => 0x144cd6
  | 207 => 0x145896
  | 208 => 0x144d16
  | 209 => 0x16ccd6
  | 210 => 0x28b96
  | 211 => 0x28d16
  | 212 => 0x29796
  | 213 => 0xb9716
  | 214 => 0xb8cd6
  | 215 => 0xb8d16
  | 216 => 0x592d6
  | 217 => 0x59496
  | 218 => 0x58cd6
  | 219 => 0x58d16
  | 220 => 0xe8cd6
  | 221 => 0xe8d16
  | 222 => 0xd0cd6
  | 223 => 0xcc04d1e
  | 224 => 0xcc94d1e
  | 225 => 0xcc9cd1e
  | 226 => 0xcd30d1e
  | 227 => 0xcd44d1e
  | 228 => 0xccb8d1e
  | 229 => 0xccd16
  | 230 => 0xcce8d1e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 2166
  | 6 => 5825
  | 5 => 5408
  | 4 => 423
  | 3 => 16
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
  | 7 => packedAt gbK7 (88806+((h/722+packedAt gbK7 (80142+(h % 722)*12) 12) % 2600)*13) 13
  | 6 => packedAt gbK6 (304833+((h/1941+packedAt gbK6 (279600+(h % 1941)*13) 13) % 6991)*14) 14
  | 5 => packedAt gbK5 (344300+((h/1802+packedAt gbK5 (319072+(h % 1802)*14) 14) % 8637)*14) 14
  | 4 => packedAt gbK4 (30879+((h/141+packedAt gbK4 (29610+(h % 141)*9) 9) % 508)*10) 10
  | 3 => packedAt gbK3 (1321+((h/5+packedAt gbK3 (1296+(h % 5)*5) 5) % 26)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff03ffc0ffc0fffc1fffc03fd33f789a39f3f3
  | 1 => 0x1fc0fff03ff07ffe07fffc02cd89fe5c67cfc
  | 2 => 0xfffff00003fff83fff83fffff0e0e0fe078f1f
  | 3 => 0x1fffffffc00003ffffc00003f00ff07f80fe0
  | 4 => 0x1ffffffffffffc0000000003fff0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x320052c044c00a4c08e64095810b388818b171
  | 1 => 0x1014055101510694202a958084580ba0c254b4
  | 2 => 0xc5aaa008222ad02355012a2a30a0c056050a0a
  | 3 => 0x61cf39aae808403b9e5003033b00f507680fc0
  | 4 => 0x81f3ce3cb3bce50104000c0c3ef50007b7e000
  | 5 => 0xf8820030c0308602186230303ffefef8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36757
namespace PEqualNP.Outside.L_meta_36757
open PEqualNP.Outside.L_meta_36757.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 14 := bs2_3_0
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
theorem bs2_4_448 : Interval s2Atlas 4 448 19 := block_range (n:=19) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 467 := (concat (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat (concat bs2_4_96 bs2_4_128) (concat bs2_4_160 bs2_4_192))) (concat (concat (concat bs2_4_224 bs2_4_256) (concat bs2_4_288 bs2_4_320)) (concat (concat bs2_4_352 bs2_4_384) (concat bs2_4_416 bs2_4_448))))
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
theorem bs2_5_608 : Interval s2Atlas 5 608 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 634 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 bs2_5_512) (concat bs2_5_544 (concat bs2_5_576 bs2_5_608)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 14 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 85 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 754 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352)))) (concat (concat (concat bs5_4_384 (concat bs5_4_416 bs5_4_448)) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544))) (concat (concat bs5_4_576 (concat bs5_4_608 bs5_4_640)) (concat bs5_4_672 (concat bs5_4_704 bs5_4_736)))))
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
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 779 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat bs5_5_288 (concat bs5_5_320 bs5_5_352)))) (concat (concat (concat bs5_5_384 (concat bs5_5_416 bs5_5_448)) (concat bs5_5_480 (concat bs5_5_512 bs5_5_544))) (concat (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)) (concat (concat bs5_5_672 bs5_5_704) (concat bs5_5_736 bs5_5_768)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 16 := bgb_3_0
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
theorem bgb_4_416 : Interval gbAtlas 4 416 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 423 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416))))
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
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 5408 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656))))))) (concat (concat (concat (concat (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)))) (concat (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136))) (concat (concat bgb_5_3168 (concat bgb_5_3200 bgb_5_3232)) (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328))))) (concat (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488))) (concat (concat bgb_5_3520 bgb_5_3552) (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)))) (concat (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 (concat bgb_5_3776 bgb_5_3808))) (concat (concat bgb_5_3840 (concat bgb_5_3872 bgb_5_3904)) (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000)))))) (concat (concat (concat (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160))) (concat (concat bgb_5_4192 bgb_5_4224) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320)))) (concat (concat (concat bgb_5_4352 bgb_5_4384) (concat bgb_5_4416 (concat bgb_5_4448 bgb_5_4480))) (concat (concat bgb_5_4512 (concat bgb_5_4544 bgb_5_4576)) (concat bgb_5_4608 (concat bgb_5_4640 bgb_5_4672))))) (concat (concat (concat (concat bgb_5_4704 bgb_5_4736) (concat bgb_5_4768 (concat bgb_5_4800 bgb_5_4832))) (concat (concat bgb_5_4864 (concat bgb_5_4896 bgb_5_4928)) (concat bgb_5_4960 (concat bgb_5_4992 bgb_5_5024)))) (concat (concat (concat bgb_5_5056 bgb_5_5088) (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184))) (concat (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280)) (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376))))))))
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
theorem bgb_6_5824 : Interval gbAtlas 6 5824 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5825 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216))) (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))))) (concat (concat (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568))) (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)))) (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))))) (concat (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)))) (concat (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))))))) (concat (concat (concat (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))) (concat (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424))) (concat (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)))) (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))))) (concat (concat (concat (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))) (concat (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)))) (concat (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))) (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))))) (concat (concat (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))) (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)))) (concat (concat (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536)) (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632))) (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824))))))))
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
theorem bgb_7_2144 : Interval gbAtlas 7 2144 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2166 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856))) (concat (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984)) (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0eeeaece0eee8e8e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36757.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[0,6]⟩,⟨.and,[3,7]⟩,⟨.or,[2,8]⟩,⟨.or,[2,4]⟩,⟨.or,[1,9]⟩,⟨.and,[0,10]⟩,⟨.and,[1,9]⟩,⟨.or,[5,11]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36757

open PEqualNP.Outside.L_meta_36757 in
theorem PEqualNP.Outside.L_meta_36757 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
