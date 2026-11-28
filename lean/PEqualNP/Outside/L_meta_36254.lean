import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36254.Model
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


end PEqualNP.Outside.L_meta_36254.Model

namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
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

def SBf (j : Nat) : Nat := [6, 6, 6, 8, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36254

namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
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
end PEqualNP.Outside.L_meta_36254
namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
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
end PEqualNP.Outside.L_meta_36254
namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa730080408000046001bf42ee42bd42ed42ad42de31dc31df30dd30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xe048206a000c00296aa4858f5350b18a6a16350a31c6a10638d42cc31a84985514530
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4430a19875350a0f6550a3183195424c3054214530
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
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
  | 4 => packedAt s2K4 (156+((h/3+packedAt s2K4 (144+(h % 3)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (224+((h/2+packedAt s2K3 (216+(h % 2)*4) 4) % 14)*4) 4
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff83ffffff81fe0ffffff83ffffe47f1ff
  | 1 => 0xc0fc1ffc1ffc1ffe1ff0e0f07fc3f83fb94e73
  | 3 => 0xff001fffe0ffe1ffe000ff007ffc7fc1c18f9c
  | 4 => 0x1fffff0001ffffff00007fff8001fe0fe0
  | 5 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x441000880008000022010111100489080210a5
  | 1 => 0x92292910ca5130960c9068a22a4150b4994652
  | 3 => 0xa4b5a2146a313aac188ba844ea86685c18b18
  | 4 => 0x2cb2944a943a454d772a1009753203196e0de0
  | 5 => 0x30c3187318c399f199ccdcce06204421f5e000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaee88aa88eeeeaaaaee88aa88eeeeaaaaee88aa88eeeeaaaaee88aa88eeeeaaaaee88aa88eeeeaaaaee88aa88eeeeaaaaee88aa88eeeeaaaaee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36254
namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xc817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c3dca5185b94a30bea9461ed528c2daa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3b886185f94830bea9061df320c3ba64185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5090afea6a177d4d42afa9a857c5350bb8a6a15714d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21
  | 2 => 0xb300001c058768571bc6892f01f22a17cbe1614927a82206b0120012a00022e9f0431fd00022d3989a336000e78a2000724a9a4e44c000002761880307412638c7cc3e07d0f4000e403546e0e857242000000000000ac3e0fd17d2a4271208fc00098540896000000000313a683c0017e37a974000002f20013680018c108e61ef0e80e09f8000288b05b11932c9e8d6a8e0102f92e000022740f30003089b8000da0008bc001773482988e80b38e264f214e00099413a0204a000001a60009a81486234248c000480007702905939a00000000000214000e30920003ca97000000000002e600104000000000ab0000009f400000000000001f64aaa1cba9b93246d8000001121440018c0000000007325c9302793448e9201b8551468a8d984d1408c0faa211a2000949af34e4f80006121c0012b0c1428540dd9a81c88fc9c1c24066ad2f8000e425049800470000000000002ed3b94926096c4da430d2650900003d800069880000048e091a01e00110136000000e2a342e46d50b18d2be2fcc425a2d696455958276944c005c15e180e017f13e3e417050528660d908e338484f80540b07f10e1d92d22413f04b22c350cf07e0da3dcfc80005e888001f21b03a51680039478c0019341a0001595a000000522330f636c0014226e604ca800000394409f10009d41fa8a33a520c8065000a0800000190000c5800378000648002bc0000008a000000fc0000ba000001411ae0840000008079c001312e8804000000000000000c0001a01c100000d0200200003000060001c060000080001c0600004008180040a0040f0ac080000505c0003400004000040001802000090000001400004000200000000004010000501002000000040600001008010080102800000000000101000000040000001c05004000000c000020040e00c0000003014000000000006010070000000c02074050040101c00000000180600c0401c0c01802000000000103800014050000004c0300000010090140000000000000000b0300300c0401c030280201400004000380300c100100000c08008060000602001000020040200427020030940000000008000200700400000000000303801044000180a000010000200801010000440e0300004c0701c0100c00bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857
  | 3 => 0x4e49987637c2b548a3616e419310220008380023e000000000000b63809e91e0348480000000000085a0c4b088cdb8b82580013c9ff000274000000008784794f2002840081d00818ca1a3b0042c01905a0008641614c1187b8000003da070208d2000910001c30000000014a4780007f9c41980000016a0002108d9463a24a90d8911504440000021a4287b1b149e0a83a81e4ae8251d00037052cc29fb000000f12400ce78544a530009c8c892f0009ad440003048111ca6340004c00000000338001084302a8001892065d9158001b2040000bc3ca000cfa242f461c2398f000054000000d4254a022743a4b4760832d0a1946000086000c30002e0370002320000008816e2da4607f0000c84880000020e0010821a000000ec000000a40000000e03143c04629a0a0f5a45204374001280008b8000001e67d0c19df0ee6fc71000000000000000000001c80026405d428b91d60d00008d4e000087800000000aa9442740009200046a9c4d52600000009a9990000000015c00047c000002dea580010c2389fcd60e613006c8a01943e1bc7e83b06c7f9231573a4544ee84a35c3e84f1b41e4000000002b649d250680002cce70f03d22e9349a932ea540006e4a00006580010e3bc0000000068c751672f0090ed8c34f058800000000a00000a94165b066a0a42a6386a823000000000000009b0000000000000000047a000ac8002263d0001a000000000000000000038e100000000000212a48a2a642c67a118a665260001f00000037cf00d008a448eba74194000590bd014a342f0b509c92cea000202000b21710fe0800019a20a550360a505a001458000006c0000001842206380d0001984ba0540e4acdd18a00072c01a114f6001478fb000000000001240000000000089400268180000588a74de00000000000a0cfb833060935290050005eceb1253b43c4001470003d4b01de000001098002ca0009e229000000000060002080004c0000f4000004500980c0ac42e0006b0b420839d030004ce3b8000000001c46780000000142053000574001d534a000000000780000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x5320c26f62544309b189510c25d658c430a7992310c25f654c030a7191300c27b654c0309798f54c825d63d5320cb98a54c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c831e5454f20c755153c834c6254f208f99053c823d6414f20d354e42c832e5450b20b318d42c834d5350b20d354f32c82ad640cb20b318d21c825e63d52209758f548825e63152209758c548827661152209d584548834e5388620d394c21882e96008620d394f208825f63551209718d544827761551209d185544825e63151209758c544823f6454d208f19153482776154d209d185534826c6550920b318d42482e860509209b99732482ad640c9208f990514823d64145209798c514825d63145209b99721482cc6348520b398e204825f63550209718d540825e63150209758c540826e62150209d984540827561150209b98b530823e6414c208f59053082766114c209d584530823e64948208f592520825e63948209758e520825f63544209718d510826d6588420ba580210825e63940209758e500826f65480209ed95200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c426f6254f109b18953c425f6354b109718d52c423e6414b108f59052c425e6314b109758c52c425f63552109718d548425e63152109758c548426e62152109b588548426e62d4e109b58b538423f6454e108f191538425e63d4a109758f528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524433454905109d195414436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520433554c40109e596100436952840109dd95100433554440109ed9510043695244010
  | 1 => 0xc65e65d0d3197994434c6cd6210d318f990524c63d6414931cb990524c72d6414931d3d0c524c74c431493197997324c74c52cc931d3149324c69e648c531d314a314c65e63d50319b988540c66d62150319e980540c679601503197596430c65f6550c3197596320c69d640c8318f992510c63d649443197d95310c6cc624c4319dd95310c63f64540318f191500c65f63553219718d54c865e63153219758c54c863e6414f218f59053c865e63943219758e50c865e63d52219758f548865e63952219758e548863e64d4e218f59353886cc6350a21ab590328863f64542218f191508865f63542219718d508865e63951219758e544866d629512197d8d544865c63551219ed81544867860551219798e534866f6254d2197994534874c53885219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d3189530863e6414c218f590530865e6314c219e98053086796014c219b596420874d5390821cb95142086cc6350821d354d420874d53cc8219b59432086ad640c8219bd9521086cc63484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876a4254021da509500876b3254021da0c9500876b2154021da485500865f6354b409718d52d025e63947409758e51d02ad6210e409798e529025d6394a40a718d429025f63546409718d519026f62546409b189519029e63906408f997415031c53d0540c714d415031c5390140c754e43102ad6210c40d394e521034d5394840d394d521034d5354840c754f421029c6350840c754d421032e5250840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd90d51103344354440cdd09511033542544408f596411029e6390440cd54641103355110440cd547401023f6550040a718d401033551500409ed95401026e62153309b58854cc29d640cb308f99251cc23d6494730b318931cc26e62d52309b58b548c26e62152309b588548c27661152309d584548c2cd6210e308f992528c23d6494a30cb992528c32d6494a30d3d0e528c34c4394a30d394b328c34e524ca30a7992318c34e528c630d3948318c34e52cc2308f992544c25f63551309b988544c26d62151308f994544c31d6315130cb988544c32d621513097996434c31c5490d3097195434c31c5450d30c7152324c25e650c930a7590324c31c540c93097997314c31c54cc530c7151314c2cc624c530c7152304c2ce628c1309798c540c26e62150309b588540c27661150309d584540c25d65d0c3097594430c2cd6210c3097d9
  | 2 => 0x41a000130000000000000000073000000000000bf80040a00000000000000a780000024c001ed42e5e8000002660003d0c4000328220000ee32c00038000665040ae0cc42000023000000000001c6000000630923940017b20e6f4000000000007a9a9330000000e70000000019f0000000000000058800000000278000000007a0000003f24f00000015e000078d1208000000a43425a800000000000c013a07c324000000000000012d000000000312640001b9852bc540329ca26a084000bc00000000153000000001360004a400000000000000001d00000007503a000c98873c0288000000005006d80000000000105000000000f8000000f78000000ec00000000000a9000000000000008010000000000100801000005002000028000060000080400000401001004014010000000000000000000000005010004000040060040000300200c0000200800000003000014020000020180000300000400800002000000020020080180300001c0080100000000800000008000000020000900500200000000002000008010000040400100600001802004008000000020040080000200000802006000008020040000080200200c00000006014000000000000400000000801001000010000040020040080300200000800004000000090000040000101a004000030160040080101000001800000000010000000026f62546439b1895190e6e62942439b58a5090e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0a5f63546429718d5190a5e63942429758e5090b4d6214d42c714f4350b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a3e64947328f59251cca3f64543328f19150cca7a60d52329e583548cacd6210e32b318d428cb8f4350a329d986544ca75619513297d8d544ca5e6590d3297195434ca6c6550932e350d424ca3d6595032c718d540ca3e64150329798c540ca6e621503297597430cb1d54d0c3297594430cb1d5410c32b3588430cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320cb1d5390f41ab58843d074e5394b41d354e52d074e5354b41d354d52d071d53d0b41a718d42d071d5350b41cb94942d071e53d0641ab588435065e63149419758c525069c6350941ad185425069e63905419798c505065d63141419b988505066d621414197d8d521065c63548418fd954110677655044197d8d501065c63540419b98854cc66d6215331b358843cc66e62943319b58a50cc66e62952319b58a548c71d6395231cb98a548c72d6295231c7952438c71e5450e31c7952328c69d640ca31c7950328c71e54cc6319758e544c66e62951319b58a544c66f62551319b189544c67b60551319e181544
  | 3 => 0x58000d20000e000000000001790000000000000049cc880028c0000000009e02800000000000000720000e40b0000000008e1bc2cc81c608300000003511525470075058348768e70dc00000070827000000000cf0000000000000000000000000000f60001e8000000000000007f1490000000000000000000000000218269bb134610b18943464789f8080e03c8e08004120000000038600000000000000001dc1be000000911a8000000fb316464ad8000001143e800000000000000003740004b000000000000000000000000000000126270000000711aa0948e800000000c620e4062d0361112467cc7d00000069c000000007f006969000000000922d6000000000e60002a9d9158688c30004207f400000000080cb8000000009800000000000000102000060000000000000014c568000d3108804ce80016e5d8b60620000000006e0e80000002c20c554b78f31fa570b700027a00400000000000000004265500000028242d0d20417e3c44116023448000000000000000682ac2950908c24a2643f9580844d0758000000000000000014c0000034a7b80d8000f8538d50003ee0000b8bb0223380000005c0000017839a760001e23ca1b4ca9b52e20002b0004043b80009c00040400122000490000780005940000012c0000010f0006b000000000000cf10300023c641f2000000000ab276000ee98e000564d010c26e00000188000000000330005f8000000004b8c191000037890800000360001180000000005b0000d400000000000000000006e40000000031c001a84180000000037e1ac6680000051c000002e000000000286164af8cc17000037800000000000000000000000035c00000000000000e30000007fc0021900030c00000396000000ef0000f4000003242cc40000162358db800006508000c2034280000000000000018f0007c0769ad0002140000039e0000000001226c00000000138540b63b60ac780ff0be82800000000000080000008502b8003200000f80e0004349f1732620000019a000000509c5000000000ad16a000d999c00010c110000000000000000039000006152010001810c20000000021200000196390530001fa37400000000000000028f9000000001740000000009511612000000000000da00042c000c6800000000a68243a4228a5090000860550b93ae0000000028a000001570004bc3f05a2da59c9602800044cf38893140a4e20003c23d82e00022c6e00001417c00000000000000090000002c80000011c118000003be000000003921446310a0640008904c000000000000005a000000000000001d6228544fb0bd0000000000000000000177080000d59f41ae008760643f6000e88d23c8300000000000000008d074000d780000007800102000314ea21121c000000002722e800
  | 4 => 0xd8000002ba000000000000000000000000000000000000000000000001e00030e0005180000025c00000288000b08000680000000010604c0380000000000164236000000003a65f40003f0007983d8000000000c00041e6c400000000000300000007a417a0b1c4000001f53fc6500000025652c000500007e000000364364000000003a42a0000ce818d31003c600000000000000538000001740000000011c00000000000290003845d50a8002505f0002000000000000000066c680000001d88f9170001042500037c608000980003dc000e60006d870000000000000003aa000d8000000220f88003d6274e80fc054054ef1ea0bc0000009f0f200000000000000e38b02906240c8000005c80000000036816800000000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8531240044b0181000c00172960143c63894c02153411c810c260041835516210c32c1ac6b14a918d0d72951438c60ebb4a819463435d0524c931c1cc82946298d0d7418953086263b2a6a1043521cd4254021a52e8192a010d48734855008692b9086a8881451cd4254440c2cc6a8c8220614635454010286ba4a49946183992528c630c1ac6b10a89850d72151434c20ebb0a81926183150624c530c18a9314609850d7418953c82263b2a6a16419294d6008620
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x419080d87990528c53180d87992528c63080d87150624c53080d87152628c130
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
  | 4 => packedAt s3K4 (22451+((h/179+packedAt s3K4 (20482+(h % 179)*11) 11) % 1144)*11) 11
  | 3 => packedAt s3K3 (1265+((h/8+packedAt s3K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x83ffffc0fffe1e0ff87f0ffff87fe07d19f3f3
  | 1 => 0xfc1f87ff0ffffff07f87f0e07f87fffee64c7f
  | 2 => 0xffe007fff07fe3ff8007ff007ff8ff83078f9c
  | 4 => 0x7ffff8003fffff800007fff0003f80fe0
  | 5 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x884300460104200188090123180921180891b1
  | 1 => 0x11040888242800503082104420824a60624446
  | 2 => 0x28895512435106a68445aa094d50950b058a98
  | 4 => 0x72d66624aa1d4b3b5d50881276640633b80f60
  | 5 => 0x43184438cc6193cc6666cc9c04401843d76000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeae8e8c8c8eeeeeaeae8e8c8c8eeeeeaeae8e8c8c8eeeeeaeae8e8c8c8eeeeeaeae8e8c8c8eeeeeaeae8e8c8c8eeeeeaeae8e8c8c8eeeeeaeae8e8c8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36254
namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xd531
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | 3 => packedAt s4K3 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (17+((h/1+packedAt s4K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc3fffe0f0fff0f870ffc3fff0e0ffe0f19f4f3
  | 1 => 0xfc7c3ff00f0ffff80e1fc783f00f0fff96489f
  | 2 => 0xff803ffff00ff0fff01ff803fff00ff0e78f1c
  | 3 => 0x3ffffff000ffffe00003fffff000f80fe0
  | 5 => 0xffffc000000000fffffffffc00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48080220120010010024088902212222009431
  | 1 => 0x91126442a4968898870a4512904a44cc924886
  | 2 => 0x82888a4022801231014902924a02922258518
  | 3 => 0x3253310a8882aaccab420442c94cc044d80ac0
  | 5 => 0x236221ccccccccf6cd9b267081888188ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfaeafaeafac8fac8faeafaeafac8fac8faeafaeafac8fac8faeafaeafac8fac8faeafaeafac8fac8faeafaeafac8fac8faeafaeafac8fac8faeafaeafac8fac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36254
namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681be42d037885a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037c87206f10e40bf29481ee52902dca5205f54a40f6a94816d529037e85206f50a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281be425037884a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6205f54c40df21881bc43102fca4205f54840dfa1081bd42102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9985f94b30bea96617e51cc2faa39877cc730ee98e617f548c2fca9185f55230be2a4617d538c2fca5185f54a30bf28c617d518c2fca11877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a2617f524c2f8a4985fd4530be28a61df314c3ba62987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4187b94830b7290617d520c3daa4185b54830bf28861f6510c2eca2185f54430faa886175510c2fca01877cc030fd18061dd300c3f260185fd5320bf2a641be54c827ca9905f55320deaa6413d54c82f8a9905fd4f20bf29e417d53c82f8a7907bd0b20f621641ee32c83da65905f94720bea8e41ef21c83da43905fd5220bf2a441be548827ca9105f55220deaa4413d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20bf28c417d51882fca1107ed0220fc20441fa30883f261107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41ef42483d884907b8c920f6992417f51482f8a2907bc8520f690a41fb40483f080907e8c120fc98241fb20483dc40905fd5020bf2a0417d54082f8a8105fd4c20bf298417d53082f8a6105f94820bf288417d51082fca0107bc8020fd10041ed20083f240107a48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf28485fa5090af4a1215f54242fca8485795090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41df21e83bc43d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0df14d41df21a83bc43506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083be42107788420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc7be8798f710f31bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c7ee8318fd10631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee8298fd10531fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418df94431ef98863f6310c7ba6218fd4c431ea988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fd8c621fa98c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28
  | 2 => 0x9131b82d43615b1606fc2f8003e04500000014c0086497500080c001f30000006b9cb000000000fb1b400000061000000ea1c0128764df13e0a08b4731030ba8201b0000001809b00a000000000000003b0298b70009a453a3e1842a4b5120000891378000da0013592100089d0d800000680cd1ec1580000017a398000952311be2790f00312e44800000096000128714324248d1580704a53c92f19a5081894a4b80011400831a000d80201949810715d180000ff2503e8000001d214217048084000000001f93204000017839c8ec0022f000000408004047091b80028a000f080013884c42a203f0001150450005509383a0165c4a826135e91859981222594000000000785e12623a088001934d88745508334e7706c2723384040b1bc000048f906a38a6d80a24314054c0002b2c221cf88000f83880790c148578160002740cc3281100000000000000660a2000000001240fa00079c0009f0005201480000028c000002fe0008da4d11600000187256914769e81e2728628d52fc3208b86e15c2d883877368800fd9f62ec60c00133144548b807e0e86acee8f32e6488b78e40486888c80000099503876000000002620008700005e00034cd480026e0012f8511d4968000000263bc001f507e7fc000a54f04f5090d642e3f4961641867bc9e1353160b8b68102985f04501d28e000001970f6130e80d042a4189720b4bc000001400ae8e05ca26000000000001e4374be9d10001d46f24b2928fc1a8642c67a8231a5000364000000000004d9eb2501380219531e6108e000318000000001e892507a05000684430000004285f8002d216c130001e03e4621d5000000000003ae40800000000001399c80005b8002540006280026409e0000013f446000ad146072160000231f82bc4c88c3824c01823c4285387599937a008020240d000080000000c0300c0c0000000000044160000301c000000e00c000101802c0000c00018080000701c1200c000100000c0200002000060080402c0a0080003803008020000006802000000000200006010060000900420004280001904c060500000411000000000000c01030030301900401004030080100003034030040701400044000040900c0202c010180f0101201012000010000001807004070001100c04004040342401008018030040100800000310081e0300002c030040f02c1b004000040a000050042101018094020040200c1c0080600c060180200007000020040500c090001904405008000080400c00018010000000c0303c01004040000d002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877
  | 3 => 0x1ca8d1068f732253c6889849c4943f84837278c3915f0ac0a11800011c7f40027516210000000000000ca159000000002524846b4000002b80003996200039cd98002d605d0500048077cc71771764100000000000000000000000cf8f64b2000001d80d06982d0000007692097901c0008b1e00001100007d0006a8e20e1000440c91ed2ce6586a1e233c930b910b0006c8660341fe580992443cc1040013411a0c8772321a400098a164585ec0001a30c2b400000000000000000000000026a0cc9283191e36a8a44b2550948684d0370e0154d722e47294d08000000724e980903e0648c079164319020182a268c5f22540243c5ea5823e000fd15713a5b1199e439a6b04100036e76cba04700a625288cf1ea974030b807a10c5a0e30f071d388210768ac6594b1b6600d886233a255109f7018148b323d19c2ac37a740000000002f0006a00088f0b23e0e182d49e6e9238004ce9980e1e93ca3a02681b27231caa98500083074a770f41089c00040c7592b1a421a4389226822a3f91aa7646c0349d800078888969430d2000609080006ed049b8000718ef0804b6608000a831009c1f02a422000e78153368e9369ee000380498912ac860001050002213800043e224359234dc0012b8003f80002a0074c6000a68000005a0a08920ce2e824
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1518c23e64951308f994544c31c54cc530c7151314c354514c5309b98b540c26d62d50309d987540c27561d50308f596540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d5547300c369528c03097d95300c355514c0309ed95300c369524c030cb18954c823e64d4f208f59353c823e6414f208f59053c82766114f209d58453c832d54d0b20ab19132c82ac6448720ce181548823e64d4e208f593538823e6414e208f59053882766114e209d584538833954d0220ae191308832e54c8220ae993208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534826e65d0920ba983424826c654c920ab19132482e8604c9208f990514823d64145209798c514825d6314520ab19121482e860485209e99740482ea62d0120ea10b40483ab42101209e19530482b8644c120ba18930482ba64c8120ab992204826e62d50209e983540825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f590530826e6214c209d98453082756114c209e980530823e64948208f592520823f64544208f191510823e64940208f59250082e962880209bd95200827b6548020bad95200836b6548020da95120083685448020dad4d20083695348020da545200825e63d53109758f54c423e64d4f108f59353c423e6494f108f59253c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c4354534c7109b98b548426d62d52108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f992528423d6494a10da149208423e64951108f994544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d5244334548c5109d1953144334544c510d514d314433854881109e19520443385448110da149204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520435553c40109e596100436952840109dd95100435553440109ed9510043695244010
  | 1 => 0xca3e64942328f592508ca3e64951328f994544ca7661d50329d587540ca7a60d50329e583540ca3d65950328f990540ca7661150329d584540ca7a60150329e580540ca5f654c8329bd95320cb365494432cd552510cb365454432cd551510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb6a3254032da4c9500cab66190f419e98252d06796094b419b98a50d066d6294341c794f439071e5350e41c794e42906ba6090a41c794c429071e53d0641d554f41906b66190d418f994435063e65d0941a798e415063f6550c418f59642106ba6090841b558e411063f65504419dd95411071c6355331c755343cc69c644cb31cd185548c73554d0631c7953318c6b664cc6319bd89544c66c62551319ed81544c678605513197997434c6d661d0d318f990524c63d64149319e980524c6796014931a7191324c6d4614c9319d997414c6d663d0531e510f414c7974310531ad993314c69e648c5318f990504c63d64141319b988504c66d62141319798f540c67661d50319b988540c66d62150319e980540c67960150318f992530c63d6494c318fd91520c63c64548318f992510c63d6494431b558e310c65f654c4319dd95310c6d7654c431d5d95310c756544c431d5151310c755524c4318fd91500c63c6454031d54c5500c67a60d53219e58354c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f5925388754534c6218fd91508863c64542218f992544863e65151218f992534863d6494d218fd91534863c6454d219ed8153486786054d21cd1523148674654c521cd1513148754534c5219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219d984530867a6014c219e580530875553884219bd9521086776548421d554d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b2154021da48550086766194f409d58653d02ba6090b409798e51d025d6394740ad986439032e4394a40cb10e529032e52d0a40cb949429029e6390640cb94a419032e5210640cb94b409036952d02408f99743502ba60909408f994425023e65d0540ab98a405023d6590c40ad986431023f65508408f596411029e6390440ba58a401023f65500409ed95401027661d53309d58754cc23f6454b308f19152cc23e64947308f59251cc26e62d52309b58b548c23e6494a308f592528c23f64546308f19
  | 2 => 0x2c316d3a64300c28eb6628a28948d2003982023467a3e050d000090ab0c46b1ce001e63806a0017e89898002feaa30c65000c0a5466112d91906cad02fa948100000000318380026c1fb5a55b58d5000003088e00062a1e1c800000fa0028e0c36000070b580a4d00cc12f096800002b8003a20031ca011e95a20109bc8c236a2346c7abcb4960d891a9c000de906000000497cc6800ba212a32446b8a0d239466978b293e0000e2f000002324922417000adb2cc51b8b8ac0ad21c1d292830d8590e6c299c000000012a000008880000000789520d9f80006000188d5902b31b40ab7823176001da6eb0e1485e0015c0007c001e4d7866db27cce800002f85b8000002e0000000000d30d4003880031800092001049a8009ca589d27ebc9860eaaea11543f278529c80fb7407a5e04096471e82d02c7609e3893600972a1ad8000f43c858a62aae31a80000040000001200d0fe7c9f480ba463a46b6944a8ab200000cbae05ea50c48447f32418868099083b19613b7e001846f9384280000000000aa3daec8239007116e729c72ac23aa8a290b850b927c07a2d9b660000219920009ada11000000c03861215e00350003767fa2cd494e8ba00818cc00000710004ba4068b2a5a18c228d60029037000cf000e386c00118518000000012800bba82d2876a5800b902458a185403cb10408593a909c6732b03a0000020a00000d11d20023c002109a000002d4cda2a168002200059a48002be0016a56326001144c0007d81adab4000000022a600000b7800a8000be884cc07883af48525c00000001d4001b0002c8000ac0012c000c8130aee6806001266900000000000da3380048a9a000000000000000000a8000006080001262089c21900000342b9a9e001aac8a1a378007b9d669a6e00128001ec9e8a60000000000004020080402401000060000101805010010000100004008020081601c000000000000054050340b004140000002c0e00000004050000a01408000020100b0141b0040f0000004401004020800102402000180400200400010000000200015024030080301816000060000a0000a0280004c000000000c02000000040400000028000280b000050880002408004020000000800010010040600c0b00402020120040e08002004000200003c000040000c03078090001500416000010367a6094b439e58252d0e6e62943439b58a50d0f374394643d5d0d5190eb66190d43b55864310e3f6550c4397d954310e766194f429d58653d0a5e63947429758e51d0ab66190e42ce90e5090b384394242ced0a5090b6b42542428f9974350aba60909428f5964310ab66190c42ba5824210a3f65508429bd954210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3f64546328f191518
  | 3 => 0x1dc1b80015382cd2c60000074000e1050002ce500bae7800cfaeab71480008e4f1de7e82000000dca4e0590c000005d056328184c9ea208f8aeb70702fc43a765b032ccb063924a00028e837c7824cce2605c09cd72a411800bd94c250b2568f0ca38a00266dbb80c40eee5b20001a0
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1a70216028009218416006a00001829938c87284858694e6090a41a2ce9b2a6218d4572151310c6a8b80a898863451d1524c431c28c898aa018d267190e529030731ca520c814a9d36548020a92e62a240105617115120082943a2a6900414a1d15148020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 634
  | 4 => 467
  | 3 => 14
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (19228+((h/211+packedAt s5K5 (17118+(h % 211)*10) 10) % 837)*11) 11
  | 4 => packedAt s5K4 (19296+((h/155+packedAt s5K4 (17746+(h % 155)*10) 10) % 617)*10) 10
  | 3 => packedAt s5K3 (706+((h/4+packedAt s5K3 (686+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff83ffc1f1fff1c3c78fe3fc707ff07c19f4f3
  | 1 => 0x7fc7ffe01f1fffc07f1fc7f80707ffce6389f
  | 2 => 0x7ff83fffe01fe3ff801ff8fff807f8307cf1c
  | 3 => 0xf80003fffffe003ffffe000fffff8003f80fe0
  | 4 => 0xfffffc000000003ffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x10a8084442604200c10260941115112808d431
  | 1 => 0x611110882482a00c0290842882222650622886
  | 2 => 0x92082914802500514801290525014909054518
  | 3 => 0x20525221210024a614a4000a4a4a0212b00ac0
  | 4 => 0xc4636039c9c9c93ba749d2400c0c0c63dfb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8fee8fac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36254
namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c180017fd5005fe54017f55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc52007fd0801fe42007f50801fc4200ffcc803fe3200ff4c803fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000dfd9510004feca88027fe65440057f32a2009ff5951004dfaca88027fc65440057e32a2009df19510014f8ca88003ff64440017fb222000efd91100057ec888003fe64440017f3222000ff59110005fac888003fc64440017e3222000ef1911000578c888027ff5444013ff2a22009ff5511004ff8a888023ff63440117fb1a2008ff98d1000dfcc688023fd63440117eb1a2008ff18d1000df8c688023ff5344011bfa9a2008ff94d10047faa6880237d5344011fe29a2008ffd0d10047fc8688023fd4344011fe21a2000ffd8910005fec488003fe624400f7f3122000ff58910005fac488003fc624400f7e3122009ffd491004ffca488027fd5244013fe2922000ffd0910007fc8488003fd4244001fe2122008ffcc910047fc6488023fd3244011fe1922009ffd451001ffca288027f65144013fea8a2009fd5451001ff8a288003ff4144007ff20a2000ff5051001ff88288023ff3144007ff18a2008fd8c510047fa6288023f53144007fe18a2000ffc851001ffc4288003fd2144007fe10a2009ffd4110027fca088027fd5044009fe2822000ffd0110027fc8088003fd4044009fe2022008ffcc110027fc6088023fd3044009fe1822000ffc8110027fc4088003fa2044001fe9022000fe48110027f8408800fff1044007fd8822004ff84110027ec2088013ff65040097fb282004ff99410015fcca080137e65040053f3282004ff59410035faca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010005fcc808013be64040015f3202004ff59010005fac808013bd64040015eb202004ff19010025f8c80801bff540400dff2a02006ff55010037f8a808013ff63040097fb182004ff98c1000dfcc608013de63040036f3182004ff58c1002dfac608013dd63040016eb182004ff18c10025f8c608017ff530400bbfa982005ff94c1002ffaa6080177d530400bfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe620400f7f3102004fb98810005dcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102006ffd4810037fca40801bfd520400dfe2902000ffd0810007fc8408003fd4204001fe2102005ffcc81002ffc6408017fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0x3fc410801dff988400eff8c420077fa621003bfc310800fff9084007ff8842003ffa421001ffc21080097f3004004ffd4020027fca010013fd5008009fe2804004ffd0020027fc8010013fd4008009fe2004004ffcc020027fc6010013fd3008009fe1804004ffc8020027de4010013fe2008009fd1004004ff48020027da401001ff92008007ffb2e2003bfd971001ffccb8800afe65c4007feb2e200dbf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988002fe64c4007feb262000bf5931001ff8c98800efc64c401bffaa6200dff9531006ffaa988037fc54c4007ffb1e2003bfd8f1001ffcc788006fe63c4007feb1e200cbf58f1001ff8c78800efc63c4019ffa9e200cdfd4f10067fca788033fd53c4019bea9e200cff14f10067fe8788033fe43c4019fea1e200cff10f1001ffec58800eff62c4007ff3162007bf98b1001ffac588002fd62c4007fe3162003bf18b1006ffea588037fe52c401bfea96200dff14b10007fe8588003fe42c4001fea162000ff10b10067fe6588033fe32c4019fe996200cff0cb1001ffea38800ffe51c4007fb28e2003ff5471006feaa38800ffc51c4007ffa0e2003ff9071001ffa838800ffc41c4007ff98e2003ff8c71001fec638800ffd31c4019fa98e2003ff0c71001ffe438800ffe21c4007fe90e2003ff0871006ffea188013fe50c401bfea862004ff14310007fe8188013fe40c4001fea062004ff10310067fe6188013fe30c4019fe9862004ff0c310007fe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2002bf99610027facb0802efd6584009fe32c2004bf19610027fec908012ff6484009ff3242000bf99210027fac908002fd6484009fe3242004bf1921005ffea90802ffe5484017feaa4200bff15210027fec708012ff6384009ff31c2001bf98e10027fac70802afd6384009fe31c2004bf18e10057fea70802b7f5384015ff29c200aff54e10056faa70802bfc5384015ffa1c200aff90e10057fa870802bfc4384009ffb142004bfd8a10027fcc50801efe6284009feb142000bf58a10027f8c508012fc6284017ffa94200bff94a1005ffaa50802ffc5284001ffa142000ff90a10007fa8508003fc4284015ff994200aff8ca10057fa650802bfc32840117eb0c200bffd461001ffca30802ffd5184007fe28c2000ffd061001ffc8308003fd4184007fe20c200affcc61001ffc630802bfd3184007fe18c2000ffc861001ffc4308003fd2184007fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fd1042004ff48210007f24108013fc2084009ff8842004fdc421001ff62108027ff65440137fb
  | 2 => 0x20096faa71004bfc5388025ffa1c4012ff90e20097fa871004bfc43880217eb144013ffd4a2003ffca51004ffd528800ffe2944000ffd0a2003ffc8510003fd428800ffe2144012ffcca2003ffc651004bfd328800ffe1944004ffd8620027fcc31000efe6188009feb0c4000bf58620027f8c31004fff5188027ff28c4013ff5462009ff8a310003ff4188001ff20c4000ff50620007f8831004bff3188025ff18c4012ff4c620097f8631001fff2188001ff10c4000ff4862003ff84310012fe6088009ffa844004ff94220027faa110013fc5088009ffa044004ff90220027fa8110013fc4088009ff9844004ff8c220027f46110013fd3088025fc9844004ff0c220027fe4110013ef208800ffd9044011ffd952008dfeca90047fe65480057f32a4011ff5952008dfaca90047fc65480057e32a4000ffd9120005fec890003fe64480017f3224000ff59120005fac890003fc64480017e3224011ffd512008ffca890047fd5448023fe2a24010ffd8d20085fec690043fe63480037f31a4010ff58d20085fac690043fc63480037e31a4010ffd4d20086fea690043fe5348021fea9a4010df54d20087f8a690043ff4348021ff21a4010ff50d20087f88690047ff524800fff2924011fb9492008ffaa490047ed524800ffe2924000ffd0920007de849001ffe4248001fea124007ff10920007d88490043ff324800fff1924010fb8c920087fa6490043ed324800ffe1924000ffd8520005fec290003fe6148001feb0a4000ff1852001df8c290047ff5148023ff28a4011ff5452008ff8a290003ff4148001ff20a4000ff50520007f88290043ff3148021ff18a4010ff4c520087f8629001fff2148001f790a4000ff88520007fa4290003ed214800ffe10a4011ffd4120027fca090047fd5048009fe2824000ffd0120027fc8090003fd4048009fe2024010ffcc120027fc6090043fa3048021fe9824010fe4c120027f8609001fff204800ffd9024004ff88120027dc4090013ff65080097fb284004ff99420015fcca10013fd650801f7eb284004ff19420025f8ca10013ff64080097fb204004ff99020005fcc810013fd64080017eb204004ff19020025f8c81003fff540801fff2a0400fff5502007ff8a810013ff63080097fb184004ff98c2000dfcc610013fd630801d7eb184004ff18c20025f8c61003bff530801dbfa98400eff94c20077faa61003b7d530801dfe298400effd0c20077fc861003bfd430801dfe2184007bf9882003ffea41001ffe520800ffea904007ff1482003ffe841001ffe420800ffea104007ff1082003ffe641001ffe320800ffe9904007ff0c820027fec210013fe61080077f3084004ff58420005fac210013fc610801fffa88400fff9442007ffaa21003ffc5108001ffa084000ff90420007fa821000
  | 3 => 0xeb288004ff19440025f8ca20066fe6410031ffaa08017ff950400c7faa82005ffc5410009ffb188004bfd8c40027fcc620006fe6310009feb188016bf58c40027f8c620012fc631002dffa988016dfd4c400b7fca62005bfd531002dbea988016ff14c400bffe862005bfe431002dfea188017ff10c40027fec420013fe621000f7f3108004ff58840005fac420013fc6210031ffa908018ff948400c7faa420063fc521002fffa108000efd0840007fc8420003fd4210001dea108017ff108400b7fe642005bfe321002dfe9908016ff0c840027fec220013fe61100077f3088004ff58440005fac220013fc6110031ffa888018ff944400c7faa220063fc511002fffa088000ff904400077c8220003fd411002ffe2088000ef104400b7fe622005bfe311002dfe9888016ff0c440007fe4220003fe2110001fe9088000ff08440025fcc020013ff5010009ff2808004ff54040027f8a020013ff4010009dfa008004ff90040027f48020013fd4010009dea008000fe50040027fe6020013fe3010009fe9808004ff0c04003ffecb9001eff65c800fff32e4002bf9972003efccb9000a7e65c800ffeb2e4015bf5972003efacb900027d65c800ffe32e4007bf1972003ffec99001eff64c800fff3264000bf9932003f7cc990002be64c800ffeb264000bf5932003f7ac990002bd64c800ffe3264007bf193200affea990057fe54c802bfeaa64015ff1532003ffec79001eff63c800fff31e4001bf98f2003ffac790052fd63c800ffe31e4007bf18f200a7fea7900537f53c8029ff29e4014ff54f200a6faa790053fc53c8029ffa1e4014ff90f200a7fa8790053fc43c800fffa964007ff94b2003fdca59001ffd52c802bf6a964007ff14b2003ffe8590003ef42c800fff2164007ff50b2003ff8859001fec42c800fff9964007ff8cb2003fdc659001ffd32c8029f69964007ff0cb2003ffec39001ffe61c80077f30e4007ff58720005fac39001ffc61c802bffa8e4015ff947200affaa390057fc51c8001ffa0e4000ff90720007fa8390003fc41c8029ff98e4014ff8c7200a7fa6390053fc31c800fff90e4007fbc872003ffc439001ffd21c8001f690e4007ff087200affea190013fe50c802bfea864004ff14320007fe8190013fe40c8001fea064004ff103200a7fe6190013fe30c8029fe9864004ff0c320027fecb10012ff6588009ff32c4002bf99620027facb1004efd6588009fe32c4004bf19620027fec910012ff6488009ff3244000bf992200277cc910002be6488009feb244000bf592200277ac910002bd6488009fe3244004bf1922009ffea91004ffe5488027feaa44013ff15220027fec710012ff6388009ff31c4001bf98e20027fac71004afd6388009fe31c4004bf18e20097fea71004b7f5388025ff29c4012ff54e
  | 4 => 0x3fe61d00077f30e8000ff58740005fac3a005ffc61d003dffa8e801eff947400f7faa3a007bfc51d002fffa0e8000efd0740007fc83a0003fd41d0001dea0e8017ff107400cffe63a0067fe31d0033fe98e8019ff0c740007fe43a0003fe21d0001fe90e8000ff087400f7fea1a0013fe50d003dfea868004ff143400cffe61a0013fe30d0033fe9868004ff0c340027fecb20012ff6590009ff32c8002bf99640027facb20076fd6590009fe32c8004bf196400d5fac920077ff549003bff2a4801dff552400eff8a920013ff63900097fb1c8004ff98e4000dfcc720013fd63900397eb1c8004ff18e40025f8c720073ff5390039bfa9c801cff94e400e7faa7200737d5390039fe29c801cffd0e400e7fc8720073fd4390039fe21c8004ffd8a40027fcc52001efe6290009f73148000bb98a40027fac520002fd6290009f6b148000bb58a40027f8c520077ff529003bff294801dff54a400eff8a520003ff4290001dfa148000ff90a40007fa8520003bd4290001fe214801cffcca400e7fc6520073fd3290039fe1948004ffd8640027fcc32000efe6190009feb0c8000bf58640027f8c320077ff519003bff28c801dff546400eff8a320003ff4190001ff20c8000ef90640007fa8320003fc4190001de20c801cffcc6400e7fc6320073fd3190039fe18c8000ffc8640007fc4320003fd2190001fe10c8004bf98240027fea120013fe5090009fea848004ff14240027fe8120013bf4090001fda048004ffcc240027fc6120013fd3090009fe184801bffd95400ddfecaa00037f65500013fb2a801bff99540015fccaa006ffd65500377eb2a801bff19540015f8caa006f7c65500053e32a801bffd51400dffca8a006fbe5450037feaa2801bef551400dff8a8a006bff63500357fb1a801aff98d4000dfcc6a006bfd63500357eb1a801aff18d4000df8c6a006bff5350035bfa9a801aff94d400d7faa6a006b7d5350035fe29a801affd0d400d77e86a006bfe4350035fea1a801aef50d400d7f886a0003ff62500017fb128000ff98940007fac4a0003fc625000f7e312801bffd49400dffca4a006ffd5250037fe2928000ffd0940007fc84a0003be4250001fea128000ff109400077884a006bff3250035ff192801aff4c9400d7f864a0003ff61500017fb0a8000ff98540007fac2a0003fc61500077e30a801bffd45400dffca2a006ffd5150037fe28a8000ffd05400077e82a0003fe4150001fea0a8000ef50540007f882a006bff3150035ff18a801aff4c5400d7f862a0003ff2150001ff10a8000ff48540007f842a006fff5050009ff282801bff54140027f8a0a0003ff4050001fda028004ff901400277c80a006bff3050009ff182801aff4c140027f860a0013ff65100097fb288004ff99440015fcca20013fd65100317
  | 5 => 0x5121117fca89088bfd5448445fe2a24221ffd8d2110dfec690887fe63484037f31a4221ff58d2110dfac690887fc63484037e31a4221ffd4d2110efea690887fe5348443fea9a4221df54d2110ff8a690887ff4348443ff21a4221ff50d2110ff8869088bff524840fff2924222ff5492103ff8a490803ff424840fff2124200ff5092103ff88490887ff324840fff1924221ff4c92103ff8649088bff5148407ff28a4222ff5452101ff8a290803ff4148407ff20a4200ff5052101ff88290887ff3148407ff18a4221fd8c52110ffa6290887f53148407fe18a4207ffc852103fee429080ffe2148407f710a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c09088bff5048445ff2824222ff54121117f8a090887ff3048443ff1824221ff4c12110ff8609080fff65084077fb284203ff99421015fcca1080f7e65084053f3284203ff59421105faca1080f7d65084013eb284203ff1942101df8ca1080fff64084077fb204203ff99021005fcc81080fbe64084015f3204203ff59021005fac81080fbd64084015eb204203ff1902101df8c810883ff5408441ff2a04220ff55021107f8a81080fff63084077fb184203ff98c2100dfcc61080fde63084036f3184203ff58c210fdfac61080fdd63084016eb184203ff18c2101df8c61087fff530843fbfa98421fff94c210fffaa61087f7d530843ffe298421fffd0c210fffc861087ffd430843ffe2184207bf9882103ffea41081ffe520840ffea904207ff1482103ffe841081ffe420840ffea104207ff1082103ffe641081ffe320840ffe9904207ff0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084207fd4842101ffec01080ffe60084097f3004203fe98021005f4c01080ffd60084017eb004203fe58021005f2c01080ffc6008441ffa804220ff94021107faa010883fc500843fff980421fff8c0210fffa601087ffc300842fffb2e801ebfd97400f7fccba000afe65d003dfeb2e801ebf597400bff8cba000afc65d003dffaa68017ff953400f77ca9a007bfd54d003ddeaa68017ff153400bffec7a0066ff63d0033ff31e8001bf98f400cffac7a0066fd63d002ffe31e8001bf18f400cffea7a00677f53d0033ff29e8019ff54f400cefaa7a0067fc53d002fffa1e8019efd0f400cffc87a0067fd43d0033dea1e8017ff10f400bffec5a0003fe62d000f7f3168000ff58b40005fac5a005ffc62d003dffa96801eff94b400f7faa5a007bfc52d002fffa168000ff90b400077c85a0003fd42d002ffe2168000ef10b400cffe65a0067fe32d0033fe9968019ff0cb400bffec3a0
  | 6 => 0xfffa108200ff908410077c8420803fd421042ffe2108200ef1084113ffe642089ffe321044ffe9908227ff0c84101dfcc22080fff5110407ff2888203ff5444101ff8a22080fff4110407dfa088203ff9044101fec822080ffd4110407dea088200fd5044101ffe622080ffe3110407fb1888203ff4c44113fea622080ffc3110407ffb008203ff98041025fcc02080ffd60104017eb008203ff18041147fea0208a3fe5010451fea808228ff1404113ffe602089ffe301044ffe9808227ff0c04103ffecb9081eff65c840fff32e4202bf9972103ffacb9089afd65c840ffe32e4207bf1972103ffec99081eff64c840fff3264200bf9932103ffac990802fd64c840ffe3264207bf19321137fea99089bfe54c844dfeaa64226ff1532103ffec79081eff63c840fff31e4201bf98f2103ffac790896fd63c840ffe31e4207bf18f2112ffea7908977f53c844bff29e4225ff54f2112efaa790897fc53c844bffa1e4225ff90f2112ffa8790897fc43c840fffa964207ff94b2103ffaa59081ffc52c840fffa164207ff90b2103ffa859081ffc42c840fff9964207ff8cb2103ffa659081ffc32c844dffa8e4203ff94721137faa39080ffc51c8401ffa0e4203ff90721007fa839080ffc41c844bff98e4203ff8c72112ffa639080ffc31c840fffb064207ff98321025fcc19081ffd60c84017eb064207ff18321137fea19089bfe50c844dfea864226ff1432112ffe6190897fe30c844bfe9864225ff0c32101ffecb1080eff6588407ff32c4202bf9962101ffacb10892fd6588407fe32c4203bf1962101ffec91080eff6488407ff3244200bf9922101ffac910802fd6488407fe3244203bf19221127fea910893fe5488449feaa44224ff1522101ffec71080eff6388407ff31c4201bf98e2101ffac71088efd6388407fe31c4203bf18e2111ffea71088f7f5388447ff29c4223ff54e2111efaa71088ffc5388447ffa1c4223ff90e2111ffa871088ffc43884437eb144224ffd4a2103ffca510893fd528840ffe2944200ffd0a2103ffc8510803fd428840ffe2144223ffcca2103ffc651088ffd328840ffe1944203bf9862101ffea31080ffe5188407fea8c4203ff1462101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fb18c4203ff4c62111fea631080ffc3188407ff90c4203fbc862103fee431080fff6088407ff3044204bf9822101ffac110802fd6088407fe3044224ffd4221127fca110893fd5088449fe2844223ffcc22111ffc611088ffd3088447fe1844222ffd9521115feca9088bfe65484057f32a4222ff59521115faca9088bfc65484057e32a4200ffd9121005fec890803bf64484015fb224200ff99121005fcc890803fd64484017eb224200ff19121005f8c890803bc64484015e3224222ffd
  | 7 => 0xa0803fd60d04017eb068217ff18341177fea1a08bbfe50d045dfea86822eff1434114ffe61a08a7fe30d0453fe9868229ff0c34101ffecb2080eff6590407ff32c8202bf9964101efccb2080a7e6590407feb2c822dbf5964101efacb208027d6590407fe32c8203bf19641155fac9208b7ff549045bff2a4822def9524116ffaa9208b7bd549045bfe2a48203ffd8e4101dfec72080ffe63904037f31c8203f798e4100dbcc72080ffd63904597eb1c8203f758e41005bac72080ffc63904077e31c822cffd4e41166fea7208b3fe5390459fea9c822cdf54e41167f8a7208b3ff4390459dfa1c822cff90e41167fa87208b3bd4390459fe21c8203ffd8a4101ffcc52081efe6290407feb148200bf58a4101ff8c5208b7ff529045bff294822dff54a4116ff8a520803ff4290401ff2148200ef90a41007fa8520803fc4290401de214822cffcca41167fc65208b3fd3290459fe1948203bf9864101ffea32080ffe5190407fea8c8203ff1464101ffe832080fbf4190401fba0c8203ffcc64101ffc632080ffd3190407fe18c8203ffd824101ffcc120812fe6090407feb048200bf5824101ff8c1208b7ff509045bff284822dff5424116ff8a1208b3ff3090459ff184822cff4c241167f861208afff65504577fb2a822bff99541015fccaa08affd65504577eb2a822bff19541015f8caa08afff5450457ff2a2822bff5514115ff8a8a08abff63504557fb1a822aff98d4100dfcc6a08abfd63504557eb1a822aff18d4100df8c6a08abff5350455bfa9a822aff94d41157faa6a08ab7d5350455fe29a822affd0d41157fc86a08abfd4350455fe21a8200ffd8941005fec4a0803fe6250401feb128200ff1894103df8c4a08afff5250457ff292822bff5494115ff8a4a0803ff4250401dfa128200ff90941007fa84a0803bd4250401fe212822affcc941157fc64a08abfd3250455fe192822bffd454101ffca2a08affd5150407fe28a8200ffd0541007ee82a080ffe4150407df20a822affcc54101ffc62a08abfd3150407fe18a8200ffd8141005fec0a0803fe6050401feb028200ff18141025f8c0a08afff5050457ff282822bff5414115ff8a0a08abff3050455ff182822aff4c141157f860a080fff65104077fb288203ff99441015fcca2080ffd65104517eb288203ff1944101df8ca208a6fe6410451ffaa08217ff950411477ca8208a3fd5410451deaa08217ff1504101ffec62080eff6310407ff3188201bf98c4101ffac62089efd6310407fe3188203bf18c4113ffea62089f7f531044fff2988227ff54c4113efaa62089ffc531042fffa188227efd0c4113ffc862089ffd431044fdea188217ff10c4101ffec42080ffe621040f7f3108203ff58841005fac42080ffc6210451ffa908228ff94841147faa4208a3fc521042
  | 8 => 0xf542421aff8a1210d3ff3090869ff1848434ff4c2421a7f861210cfff65508677fb2a8433ff99542015fccaa10cffd65508677eb2a8433ff19542015f8caa10cfff5450867ff2a28433ef9514219ffaa8a10cfbd5450867fe2a28432ffd8d42195fec6a10cbfe63508037f31a8432ff58d42195fac6a10cbfc63508037e31a8432ffd4d42196fea6a10cbfe5350865fea9a8432df54d42197f8a6a10cbff4350865dfa1a8432ff90d42197fa86a10cbbd4350865fe21a8433ffd494203ffca4a10cffd525080ffe2928400ffd0942007de84a101ffe425080fdf2128432ffcc94203ffc64a10cbfd325080ffe1928400ffd8542005fec2a1003fe6150801feb0a8400ff1854201df8c2a10cfff5150867ff28a8433ff5454219ff8a2a10cbff3150865ff18a8432ff4c542197f862a1003ff60508017fb028400ff98142007fac0a1003fc60508097e3028433ffd414219ffca0a10cffd5050867fe2828432ffcc142197fc60a10cbfd3050865fe1828407ffd944203dfeca2101ffe65108057f3288407df99442014fcca2101ffd65108617eb288407df59442004faca2101ffc651080f7e3288431bf99042187fea82105ffe5410861feaa08417ff1504203ffec62101eff631080fff3188401bf98c4203ffac6210befd631080ffe3188407bf18c4217ffea6210bf7f531085fff298842fff54c4217efaa6210bffc531082fffa18842fff90c4217ffa862105ffc431080f7f3108407ffd484203ffca42101ffd521080ffe2908407ffd084203f7e842101ffe421080ff72108407ff5084203f7a8421003ed421080fff9908407ff8c84203ffa642101ffc321080fffb088407ff9844201dfcc22101ffd61108017eb088407ff18442187fea2210c3fe5110861fea888430ff1444217ffe62210bffe311085ffe988842fff0c44203ffec02101ffe60108097f3008407ff58042005fac02101ffc6010861ffa808430ff94042187faa0210c3fc501085fff980842fff8c04217ffa60210bffc301082fffb2e822ebfd9741177fccba080afe65d045dfeb2e822ebf597410bff8cba080afc65d045dffaa68217ff95341177faa9a085ffc54d042fffb1e8229bfd8f4114ffcc7a0806fe63d0453feb1e8229bf58f410bff8c7a0806fc63d0453ffa9e8229dfd4f4114ffca7a08a7fd53d0453bea9e8229ff14f410bffe87a08a7fe43d0453fea1e8217ff10f410bffec5a0803fe62d040f7f3168200ff58b41005fac5a085ffc62d045dffa96822eff94b41177faa5a08bbfc52d042fffa168200efd0b41007fc85a0803fd42d0401dea168217ff10b4114ffe65a08a7fe32d0453fe9968229ff0cb41177fea3a080ffe51d045dfea8e8203ff1474114ffe63a080ffe31d0453fb18e8229ff4c74114fea63a080ffc31d042fffb068200ff98341025fcc1
  | 9 => 0x300101800000100100000300000000701201100302c01800c00300700300000400400400400201500000000001900d00301f00100303b00003300d00100501100300200000101100000000000b00000100a00100200300300202900000400100000300d00200200303300000000000100400000b00600000000000000000000200a00301201500401000000000f00200300100d01200702b02500f00800000205300600700100602d00200700000000000300800200000000300000700101b01100f00003000100001400d00303200000500100f00100000003200900300000401200100100101c00401e00c00d00700600700900000400000100800c00200100000101800800600000200001f00700301600000d00200f00701a01701600e00500101d00000000d01800000500100100600000c00f00100e00900400001c01300105200900200600c01900300000500000501800600200000800000100000000d07f00100100900900300000800003100500200200501200800000500b00201000e00600200100000001a00a0010bffecba10daff65d086dff32e8402bf997421b7facba10dafd65d082ffe32e8402bf197421b7fea9a105ffe54d086ddf2a68436ff553421b77aa9a105ffc54d082fffb1e8431bfd8f4218ffcc7a1006fe63d0863feb1e8431bf58f420bff8c7a1006fc63d0863ffa9e8431dfd4f4218ffca7a10c7fd53d0863bea9e8431ff14f420bffe87a10c7bf43d0863ff21e8431ff50f4218f7a87a105ffc43d086dffa968407ff94b421b7faa5a101ffc52d0863ff9968407ff8cb4218ffa65a101ffc32d082fffb0e8400ff9874201dfcc3a1003fd61d08017eb0e8417ff187421b7fea3a10dbfe51d086dfea8e8436ff1474218ffe63a10c7fe31d0863fe98e8431ff0c7420bffec1a1003fe60d08097f3068400ff58342005fac1a105ffc60d086dffa868436ff943421b7faa1a10dbfc50d0863ff9868431ff8c34218ffa61a10c7fc30d080fffb2c8407bfd964203ffccb2100afe659080ffeb2c8435bf5964203ff8cb2101efc65908657eb248435ffd52421affca9210d7fd549086bfe2a48407ffd8e4203dfec72101ffe63908037f31c8407ff58e421a5fac72101ffc639080f7e31c8434ffd4e421a6fea7210d3fe5390869fea9c8434df54e421a7f8a7210d3ff4390869ff21c8434ff50e421a7f8872101efe629080fffa948407ff94a4203ffaa52101ffc529080fffa148407efd0a42007de852101fff329080fff1948407ff4ca4203ff8652101fff619080fff30c8403bf9864203ffac321002fd619080ffe30c8435ffd46421affca3210d7fd519086bfe28c8434ffcc6421a7fc63210d3fd3190869fe18c8407ffd824203ffcc121012fe609080ffeb048400bf5824203ff8c1210d7ff509086bff2848435f
  | 10 => 0x61d000000000077535a8b5c5f015608f8bd8bd41892d20a00c944f91ed8a9c9347d30001724da23de38680000002940001eac000000000000026c54132e0df48942d40ad08e0ae05c30001f240000002388f58f1e33d00017e82c87021e786c0fdc6df000000000043225008c4ec62054238a3ccaa0552b31a4859c2470b50de40003f80ab9c9d0626d500006c40004280000ab8c7c00000000d093a4d032600000003fc00c01c40001941e480003e2572000000028e0002a794f400044e28907bc2b21c71e19a24df879941610cd09c5860150f4c45827e1fc98c4c4c1fb05013a438076c03a10943cc2200c39e805963d01ad8d84b144c61341b1d03e5f0000186c7b20410000000c886a000013a08be62825a899d00c5e23cb2000a780590c406f800008c16483d83b837b321053c0000003f696846183c51f01018e9a22f3e680283c24351ce15107066cf1b618403f22b51ac8f10f4268209106b08ac5322801ee48ee00001002c00500001100106a02e00001100000100000300f03500000400002500100200f00201100500101e00100000200c00401600500e00401500700300000100b00500001f02200000000200800d00a00b00107c01d01800400c01a00100900200400300600200400200601700000d00501300200101101600000700400100000704a00304800503d00400000000200901a00500100500401400200500001501500100100e00200500600300800300200000000000300800000000000101201b00100102600202500800f00000901600100501000600000700a00000c00200000400000000e00600500602f00a00803a00000300400103a00000a00500000c00300003400200303a00d00300000200401600200000100000000001600203000000100100200200200300000c02400000601400d00500000300000700200001300000500600400000d00f00e02f01500d00401e00200000000901c01700000700100000100600000600700000501500100000c00100000100500300000b00600200800000000004500000100800000d00300c01703400104700100803600400500000100c01800400000400101400103200100f00000a00b00d00100500000100400b01f00e00d02800100100400e00100101100000700000401d00000200700100000b00000f00300200000b00703c00100000100002400101600700000701702801700000300901200000300200000800400a00500400100100403a00000800300100c02200001000402100600100000500300401000500400200100300d01401600000b00100300100800300f00d00100101400300e00100100d00001200100600100102400300100500701201001400001100000000001e00000501000700a00b00700802c03500100200d00200400101e00f00600300
  | 11 => 0xa280e4a0a7c3000018c75a01b2f41cf45f20003b2842c40e53624002501be4853069e600ec75a1121b2c0004f72e413d47940de413189c5fe6683e38adc4ec6e928f0aa05864b905f971c0000013530818c527e526509940005f42691b580001512db9e0d0641c328415ccf963322d18000000525249a1200006712b686583a65280001ce102e68f32ea034ee081b3e912c800059626986000007dc2458eb800013f38818dc3642ee37a80004da706000091485c24d30200004381c93488108bea1f52bf106818c72301888ec01e80730602ccf4661c3891b409105ee21b1f7c4ba69b24788f400036501a80003aa1551dd00000002192b49bac0004c80f48b909420000002044a600002fc8c10a3a5f73770d380007d415c8d9894a53313e800014e2bb15e9e7493e1090f7179c34821326017e00c042f30b0414e6a66703480004ae00024800b4f7c47e00003382de0003e30c080005191e40270a743083311620d9855f10000009980002da95c433c2c5254054007e5cb13d8a10f805eb00003e0ebe65633c0a6400081e16605940003e603320704c66bc3a6084104a636168020c0006d70c600010043444268e640e67ca00011d10820002870c6c2f026938b00009ca00020299a41041a716310d00000001070020000143000000000002341b8bd400000033e80008607f9000000062c7fb00010e0d9c79b0000d149ac30a1c400000006013dc00005a6000000000000045d00010748466b00001c5400000000000001a85df0871f5c4803bd25f87a007409937f15dc820000218846c0c822d27f8a386220b541d98f46965ff0760e68562000220988453c00000002dcfb25091108000faa5ba1999d80eda4ba2860254afe14624d8000b7e0da28f8a747da30733b965c8485643f9137c6482870230c9c8881a2152058505652139990b04c466638d90448b8000046a0248a80000d28bd00000002050000af480b1d31d2495c00008513385cc46c40d1404e4a6120d69ca0cec5cc2a70b643a82260f81afc8868281411210bc27a813591148187431f2a1082723ac0e78b68b6c25b1780e1cbe23fe1ba0000bf680f159185031608b23399f03da0000f90e80c1e03613a8f2c86e0000000d742746de31a181800000041e99185bc7f80db96b49b84150000964fce6fb136078818e2951a90aacd6243b21693f8a9a7b60dd1b508520e4115040076658906093040060022560b08c5806a13c17947aa6a80a10c70f884ee0fd033c0de37716085109c814c2ab930c62840d31d90510207e10e41e14d5c2120ca82e8000250020006439c7fd0001768eae580419976400000003381d4c7e4a90511d446985e92950000cbc16b00002b00920000000000d4400033a8000a480000000c000001a800000000001b900014509465f60001f20f6200022600000
  | 12 => 0x1e273c1561e90f747dd0000a6806662d0001d740002a229f12300a60f42799a74db259d0000000af00003a50000db40fb00014a4d760000478f9cce64d41a9964c5f81fd1d19cc833045910e9af430a79f18c0c84dec6b31c483c82ce82040096a08ca4e7013867504611d41c0c74e1650335b0384afa3be0498af8fc859e2d583f80a46953a00ceccb001133f8c541563fa37a0274a2a7da23f9c4caa678e05191483ac15310d8240b8234a180941c3be5610080a7c3a071d23208f83520ae03080e06dc41e2a88a4000050f24a9d480b86850fc0358c2e00028215d8e3420212a11244104033110efc0007f304904f872600035289bc000000182820038a3fb1d29228e4855e1960a180000000001c640000000000000000000012a0b4e90343000204ced01cc3959419006000097811491c3362ab022007c2922f9847008e4f21968000c164b7381800000000001114ecff42a63979b6cc8a2832e00000ff88274171e9c00016c0bc974c2621843350d7cf182331e0113c9d425f0ce172800011025211bc5781153600bbc5660000a40070cbe4f634d0b106740172de1ea4000000308800000073a0001a9c000312000211800000037d08a40002013981b8494e0000651a64f447e90de8680e3c4b01a68bacc0a4fd2a192f000024f298826c4927873fa8178eb2000000041000000000000002d000025b0000c30000000034803447d3421000dca7e024483b8cb22cf04b8e88f9c50d0000990b62630253036c41448d0360dc49f65383ff83b4bbc0bd1088b481707b41869facaf63b03790da4e9635e0000dcc7d013d1eb815042a70f0001dd0ad450b00000005d200006599e875e80c27d1b987140840000b8068e522000000041631f0000a943b423a000000038821800002a450235400001288c484405d84782ba0000810b7c7c800032800b828239d3b590f49221f73de8000000000000000000075800000000000001501a90e4c2d109016bca5800007f9c8400047237e800057e3d82ea87d8b8439b12111d40007ac000202814c0f91a09798c4830f0310980b5841602f8abcf7e1c22e21d4c0005d70578dac80e0001941fa892e3b52f00260f8a3a93ef1460d065cf00012b40003c11350c9800021f1638e78a80000000035c0f400000004e000009f0001cfc49807e2d305f448828c3171c389ba0773b119b88a2239061819400022b0000d088b627433c80000004ab26215a0aaa804348144432e6e809383dc36680e00010049e033f231a13cffc00000014b48c208640a9c100002dc27100000000000000e900002353190d886c02d80000000d6e43c0ee80b05223c213b8010dda00000017601224eb22a8000d560003838fdc67800026c17909e8285145a064e144da12b08780003341110e508d0000000021c7e475c0918b58dee0b43
  | 13 => 0x11b09b81cc7db12f03c0f144ec2040f486f00e802792a80003aa36e912c00065a35f111d07817237c84d000032200011b80000000000e8444e6b40001df04e447000b1abc7e04c700000000001c12cc0f68e402281ff992105259c1751c3031a1ab086867c46e46900005e85aa40e1949100ac458333f01384961900d5109ca6800033583e80000003948df01147940000000b7278018d097000000029a8dbce583c70001eec00002800000003fc0001550f8481e00000015e4ac00b900001b48b01e3303809898416e0b89654cc23842f1800037e163293969c7d600007e9ab0da649406e9da487c58f1c680004b404c0001b182665aa149948c20c591047121c6f45a21469f884cc3e201205dc2181d91900904eec5b21dc1e340907d00000c403e82f70ed8648d464182dc0e1454268832a080cee668c0de1b880000003d80cac00078b3fb0528d9a1b641512490600fc1f78048a0464700000000007c12d29eb46a200000003ac0000e00a48000f54391000132c79a5a900002a04864733e78a2400040200015b80004483950da000079223300000003350000000bde0890000000b3600022d1c7c0005a00001f30fd813034b8278a340f31251cb8ace49e30700002e061a00004506727823468db4a8c7500be03342c035a019105c3683583290ec485466f05899b40004c50ff9440b086ba000167c9045dd12a8d20a3624823c05f818a3ce0001f982b83cc1a787f05ba73913d00006ec17603e19386d46e01db0000c4a52f0159398b8a5b03cf152801811329c88d0206409003a05899a55402b8c0ce126e40280c242a80000958cdc646609324956859432f4228ec8b240781d58144b5c20917d1c04ef442b0640778e8c0002a5888cd707971c008c020274e08c8734028000000000006e7b50000308de057509e136c8f41210c195f07ec00019717f803c1e03690aa400009a15a016c0004501cc05481a0214000115c0000002ae81fc52e00039d92ec0000003f183bc02a0d33bf07ccc5e04418b9cb49da0004029750e4476400013c442e30b03700010940002719be000000001e92c507c0003c495410244e000310fcd5a76f3b39bfc44a60301088b906a6d8378a12438c6b21ee9dfcf220000000364b9c7723989ef01884bd0000604c7200008b97586807a61c086640000003799a7c7e22f13390fd09aa2ed087961c2d265b1ab11a8dc6778000106442c4991290e58ae852e1641f0821061f000193c8bc2e2102106cd0007b19f000090c3b900016ed08663800003a46c63bb07284a4ade54200000003462e33d999d072407d02e81683960001950bc8e7c0e23a1060824c12c0219fc024a3e93430c9495e3b4373a0844e030609a81acb3220c13f82140000002da18a8a2c7ae00000007164ef052000036a0002b197400005522678000
  | 14 => 0x66cfd05811ea102c84c2fb0f60ea08f82e810d000092c0be06e1808d823ea3ad9d5463c27c09900006ae5470001c20b8c00000017b452c1620001ba81aa27905696300002fd0660a60f0838c01d82a8d2600034390e49f86531e30dd46322511308d9c7dc66415b0000fb000000001c00006510590ff41784421c7a07401a390202029509608134a074461c73641a057830c61541f9a2c4e623c2c299c000039f0bf90e8a3806841b1e18c8600000003d422282f3550000c003a73888cc4a2e46d00017b000014b00001608d67661db92cc00077b0e5068434c36436417707d80001a80b84ee26c32232060b7a1071ee02c0d2c7930001f583ce2710508e38f6474f0268df8d926a130f0668eee6352c59288a8a5130dc10847c611a2e699801b07373101d78b667f13db94dcbe47ef30c97f0d022ba37606b825c05615696f8ba42b83548324a9263a0c7857c68c2e519c1b0822400912707945b613b07395b02da00b411198cb042a30950c4c70c1af0ba8918d72790039000000029b240a13083e5583a09ebc096840068800093828a3268b3412c0e33e8804c0000000000d54d3007936e0760cae63c08c13842cc1e40181de428a20f30405004b068a38e1c609704be2c70fd4e0077d1298628a141bb00019ed01033021115708c01eb0000e5c5fc372075164107283a2b28d2403a62b2b58000b28420412176c0004d90b991e4e284533ce0d700005590001e0429a23f1f99a3872a64020e1b1089a76138b80a45807343aa135c1806650ac0080b3437024c192cb1a52b3b70644bfa788209120cc660b61de06385e64f825a156c7be3d13098e0822c74717600bcdde5480f51fdc29c37f0000ac0c4612d32080f02f674409b80002500000eb948000053f2649828cd800026f05d0d3c0000000000eac6c53fa0834d380003651e54ba215b00f93448f6000000000000079a0001530ed400e209a050538005173864cf4a705000074851052623b0000248232
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7098810026ed7098810026ec7098810026ef5098810026ee5098810026ed5098810026ec5098810026ef4098810026ee4098810026ed4098810026ec4098810026ef3098810026ee3098810026ed3098810026ec3098810026ef1098810026ee1098810026ed1098810026ec1098810004ff7558810014fe7558810004fd7558810014fc7558810004ff74588100bcfc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810024ff7258810026ef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef3258810006ee3258810006ed3258810006ec325881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026fa105881001ef91058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881001eef715881001eee715881001eed715881001eec715881001eef515881001eee515881001eed515881001eec515881001eef415881001eee415881001eed415881001eec415881001eef315881001eee315881001eed315881001eec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef4058810026ee4058810026ed4058810026ec4058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026ee1058810026ea1058810026ed105881001ee91058810026ec10588100bcff76d0810024fe76d0810004fd76d0810024fc76d08101b67e65d08100067d65d08100bebe64d0810006bd64d081018ede63d0810006dd63d081003eee62d0810006ed62d081003cff7690810024fe7690810004fd7690810024fc76908101ae7e65908100067d6590810006be6490810006bd64908101a6de6390810006dd639081003eee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc765081019e7e65508100067d6550810006be6450810006bd6450810196de6350810006dd635081003eee6250810006ed6250810005f7715081001df4715081003cff7610810024fe7610810004fd7610810024fc76108100357e75108100057d75108101867e65108100067d65108100bebe6410810006bd641081017ede6310810006dd631081003eee6210810006ed6210810
  | 1 => 0x9010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315901001ebe315901001ebd315901001ebc315901001ebf215901001ebe215901001ebd215901001ebc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026be1059010026bd1059010026bc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001edf5158c1001ede5158c1001edd5158c1001edc5158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026d71058c10026de1058c10026dd1058c10026d51058c10026dc1058c1003eef759881003eee759881003eed759881003eec759881003eef749881003eee749881003eed749881003eec7498810006ef5498810006ee5498810006ed5498810006ec549881003eef739881003eee739881003eed739881003eec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881001eef719881001eee719881001eed719881001eec719881001eef519881001eee519881001eed519881001eec519881001eef419881001eee419881001eed419881001eec419881001eef319881001eee319881001eed319881001eec3198810026ef7098810026e
  | 2 => 0x67f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c325941001e7f715941001e7e715941001e7d715941001e7c715941001e7f415941001e7e415941001e7d415941001e7c415941001e7f315941001e7e315941001e7d315941001e7c315941001e7f215941001e7e215941001e7d215941001e7c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267710594100267e10594100267d10594100267510594100267c10594100bcff7599010014fe7599010004fd75990100bcfc7599010024fe7499010026be7499010006bf54990100bebe5499010006bd54990100bebc54990100bcff739901000cfe7399010004fd739901000cfc73990100067f53990100067d53990100bebf4399010006be4399010006bd43990100bebc439901003cfe7299010004fd729901001cfe719901001cfc719901001ebe419901001ebc4199010024fe7099010024fc7099010026be4099010026bc40990100bebf7599010006be7599010006bd75990100bebc75990100bebf7399010006be7399010006bd73990100bebc7399010006bf53990100063f5399010006be5399010006bd53990100063d5399010006bc53990100bebf7299010006be7299010006bd72990100bebc7299010006bf5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bd3299010006bc329901001ebf719901001ebe719901001ebd719901001ebc719901001ebf519901001ebe519901001ebd519901001ebc519901001ebf319901001ebe319901001ebd319901001ebc319901001ebf219901001ebe219901001ebd219901001ebc2199010026bf7099010026be7099010026bd7099010026bc7099010026bf5099010026be5099010026bd5099010026bc5099010026bf3099010026be3099010026bd3099010026bc3099010026bf2099010026be2099010026bd2099010026bc2099010026bf1099010026be1099010026bd1099010026bc1099010004ff7559010014fe7559010004fd7559010014fc7559010024ff7459010026bf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d5359010006bf4359010006be4359010006bd4359010006bc4359010004ff725901003cfc725901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc4159010024ff705
  | 3 => 0xf7650910004fe7650910004fd7650910004fc76509100067f655091019e7c6550910006bf6450910006bc645091003cff7610910004fe7610910004fd761091003cfc761091004d7e75109100057d75109100067f65109101867c6510910006bf64109100bebc641091001df67110910005f57110910025fa7010910005f97010910024fe76d05100067f65d05101767c65d0510006bf64d05100bebc64d0510025fa70d0510005f970d0510024fc76505100067f655051015e7c6550510006bf6450510006bc6450510005fb7050510025f8705051001ff01050510024fe76c8510024fc76c85100067f65c85101367c65c8510006bf64c8510006bc64c8510006ef62c851003eec62c8510025fa70c8510005f970c8510024fc76485100067f65485101167c6548510005bf7448510005bc7448510006bf6448510006bc6448510006ef624851003eec6248510005fb7048510025f8704851001cfe76d01100067f65d01100f67c65d0110006bf64d01100bebc64d011001df671d0110005f571d01100bcff7650110004fd765011001cfc76501100057f755011004d7c75501100067f65501100de7c6550110006bf6450110006bc6450110005f7715011001df47150110027f0105011001cfe76c811001cfc76c811004d7e75c81100057d75c81100067f65c81100ae7c65c8110005be74c8110005bd74c8110006bf64c8110006bc64c8110006ef62c811003eec62c811001df671c8110005f571c8110005fa7688110026fa76881100077b65881101d7786588110027ba7488110027b97488110007bb6488110007b864881101cefb63881101cef963881101cf7b53881101cf7953881101ddf9728811003efa628811003ef8628811001dfa7188110025f87188110026fb6188110027f361881101d7f251881101d7f151881101cff231881101cff1318811003cff7648110004fd764811001cfc76481100067f654811008e7c6548110006bf6448110006bc6448110006ef624811003eec6248110005f7714811001df47148110027e8204811001df8764811003ef8764811001cf876481100077b65481101c7786548110007bb6448110007b864481101befb63481101bef963481101bf7b53481101bf795348110025fb7248110027eb7248110007eb624811003efa624811003ef86248110007e862481101c7ea52481101c7e95248110007eb4248110007e842481101bfea32481101bfe93248110007f3714811001dfa714811001df87148110007f07148110026fb6148110027f361481101c7f251481101c7f151481101bff231481101bff13148110007eb2148110007e921481100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c7359410
  | 4 => 0x91100073f53191100073d5319110007b65119110007b55119110007b63119110007b531191101efbb10191101e7b610191101e7b410191101efb810191100bebf7519110006be7519110006bd75191100bebc75191100bebf7319110006be7319110006bd73191100bebc7319110006bf53191100063f5319110006be5319110006bd53191100063d5319110006bc53191100bebf7219110006be7219110006bd72191100bebc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc32191100bebf71191101eebe7119110006bd71191100bebc7119110006bf51191101eebe5119110006bd51191101eebc5119110006bf31191101eebe3119110006b63119110006bd3119110006b531191101eebc31191101eebe21191101eebc21191100bebf70191101e6be7019110006bd70191100bebc7019110006bf50191101e6be5019110006bd50191101e6bc5019110006bf30191101e6be3019110006bd30191101e6bc30191101e6be20191101e6bc20191101eebf10191101e6be1019110006bd10191101e6bc101911003cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910004ff75d8910014fe75d8910004fd75d8910014fc75d89100bcfe74d8910004fd74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef32d8910006ec32d891001cfe71d891001cfc71d8910006f631d8910006f531d8910024fe70d8910024fc70d891004d7e75989100057d75989100067f65989100067c6598910005be7498910005bd7498910006bf6498910006bc6498910006ef62989100057f755891004d7c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df7358910045dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf74589100bcfc7458910006bc7458910004bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef7258910004ff7158910006f77158910006f63158910006f53158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc641891003eee6218910006ed62189100bcff76d0910004fe76d0910004fd76d09100bcfc76d09100067f65d09101b67c65d0910006bf64d09100bebc64d091003cff7690910004fe7690910004fd769091003cfc76909100067f65909101ae7c6590910006bf6490910006bc6490910025fa7090910005f97090910004f
  | 5 => 0x6bf63d9110006be63d9110006bd63d9110006bc63d91100073f53d91100073d53d9110007b651d9110007b551d9110007b631d9110007b531d91101ffbb10d91101f7b610d91101f7b410d91101ffb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101f6bf71d91101febe71d9110006bd71d91101febc71d9110006bf51d91101febe51d9110006bd51d91101febc51d9110006bf31d91101febe31d9110006bd31d91101febc31d91101febe21d91101febc21d91101febf70d91101f6be70d9110006bd70d91101f6bc70d9110006bf50d91101f6be50d9110006bd50d91101f6bc50d9110006bf30d91101f6be30d9110006bd30d91101f6bc30d91101f6be20d91101f6bc20d91101febf10d91101f6be10d91101f6bc10d911004d7e75991100057d75991100067f65991100067c6599110006bf64991100bcff7599110014fe75991100be7e75991100147e7599110004fd75991100be7d75991100047d75991100bcfc75991100bcfe7499110004be74991100bcff739911000cfe7399110004fd739911000cfc73991100067f53991100067d539911003cfe7299110004fd7299110004fd71991100bef57199110006f63199110006f53199110004fd70991100bef970991100057f755911004d7c75591100067f65591100067c6559110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110004ff735911000cfe7359110004fd735911000cfc73591100067f53591100067d5359110004ff725911003cfc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c6519110006bd64191100bcff7519110014fe7519110004fd75191100bcfc75191100bebe7419110006bf54191100bebe5419110006bd54191100bebc54191100bcff731911000cfe7319110004fd731911000cfc73191100067f53191100067d53191100bebf4319110006be4319110006bd43191100bebc431911003cfe7219110004fd721911001cfe711911001cfc7119110006f63119110006f53119110024fe7019110024fc7019110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc631
  | 6 => 0xd76d0a10024fc76d0a1022ebf64d0a100bebc64d0a1003eee62d0a10006ed62d0a1003cff7690a10024fe7690a10004fd7690a10024fc7690a10006be6490a10006bd6490a10025fa7090a10005f97090a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10226bf6450a10226bc6450a10005f77150a1001df47150a1003cff7610a10024fe7610a10004fd7610a10024fc7610a1005d7e7510a100057d7510a100bebe6410a10006bd6410a1003eee6210a10006ed6210a10025fa7010a10005f97010a100bebe64d0610006bd64d0610025fa70d0610005f970d0610006be6450610006bd6450610005fb7050610025f8705061003eee62c8610006ed62c8610025fa70c8610005f970c861003cff7648610005bf7448610005bc744861003eee6248610006ed6248610005fb7048610025f87048610025fb7648210006fb7648210026fb6348210216f963482102177b5348210217795348210027eb7248210027eb624821003efa6248210026f86248210027e8624821021fea524821021fe95248210007eb4248210007e84248210217ea3248210217e9324821001dfa714821001df87148210007eb2148210007e9214821004d7e76d951004e7e76d95100147e76d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95102077771d951004f7471d95100077631d95100077531d951020f7b10d95102077610d95102077410d951020f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d95102067f71d951020e7e71d951004e7d71d951020e7c71d951020e7e41d951020e7c41d95100067f31d951020e7e31d95100067d31d951020e7c31d951020e7e21d951020e7c21d951020e7f70d95102067e70d951004e7d70d95102067c70d95102067e40d95102067c40d95100067f30d95102067e30d95100067d30d95102067c30d95102067e20d95102067c20d951020e7f10d95102067e10d951004e7d10d95102067c10d95100067f65d91100067c65d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d9110006bf43d9110006be43d9110006bd43d9110006bc43d911003cfe72d9110004fd72d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110
  | 7 => 0x93100bcff739931000cfe7399310004fd739931000cfc73993100067f53993100067d539931003cfe7299310004fd7299310024fe719931001ebe419931001ebc419931001ef63199310006f53199310004ff7559310014fe7559310004fd7559310014fc755931001ebf7459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d5359310004ff725931003cfc7259310024fc715931001ebe415931001ebc4159310004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b10006bf7458b10004bf7458b100bcfc7458b10006bc7458b10004bc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b1001eef7258b10024fc7158b1001ef63158b10006f53158b1001eee2158b1001eec2158b1001efa1058b1001ef91058b100bcff76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b100bebe64d0b10006bd64d0b1003cff7690b1001cfe7690b10004fd7690b1001cfc7690b1023ebf6490b1023ebc6490b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b10006be6450b10006bd6450b1003cff7610b1001cfe7610b10004fd7610b1001cfc7610b1006d7e7510b100057d7510b10236bf6410b100bebc6410b1001df67110b10005f57110b100bebe64d0310006bd64d031001df671d0310005f571d03100057f755031006d7c7550310006be6450310006bd6450310005f7715031001df4715031006d7e75c83100057d75c8310005be74c8310005bd74c831003eee62c8310006ed62c831001df671c8310005f571c831003cff764831003eee6248310006ed6248310005f7714831001df471483100bcff7599210014fe7599210004fd75992100bcfc7599210026be74992100bebe5499210006bd54992100bcff739921000cfe7399210004fd739921000cfc73992100067f53992100067d53992100bebf4399210006bd439921003cfe7299210004fd7299210024fe7099210026be4099210026bc4099210004ff75592100067f75592100047f7559210014fe7559210004fd7559210014fc75592100067c75592100147c7559210026bf7459210006be5459210006bd5459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210006bf4359210006bd4359210004ff725921003cfc7259210024fc7059210026be4059210026bc4059210004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a100bcfc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a10026ef7258a10006ee5258a10006ed5258a10006ee3258a10006ed3258a10024fc7058a10026ee2058a10026ec2058a100bcff76d0a10024fe76d0a10004f
  | 8 => 0x5bc7448520006f7614852001ef46148520005fb7048520025f8704852003fe82048520024ec7648520255ef7548520255ed7548520007af7448520005ee7448520005ec7448520007ac7448520005ac744852024def734852024ded73485202476f53485202476d534852003def714852003fe77148520007e7614852001eee614852001eec6148520007e46148520247e63148520247e53148520007eb7048520025ee7048520025ec7048520007e8704852003eef604852003feb6048520247ea3048520247e9304852003cfe76d0120006bf64d01200bebc64d012003dee72d0120005ed72d0120007ac42d01200bcff7650120004fd765012003cfc76501200057f755012008d7c7550120006bf6450120006bc6450120005ef725012003dec7250120007ac4250120027e820501200bcff7599020014fe7599020004fd75990200bcfc7599020024fe7499020026be74990200bebe5499020006bd54990200bcff739902000cfe7399020004fd739902000cfc73990200067f53990200067d53990200bebf4399020006bd439902003cfe729902003cfc729902003ebe429902003ebc429902001cfe7199020004fd7199020024fe7099020024fc7099020026be4099020026bc4099020026ef2099020026ed2099020004ff7559020014fe7559020004fd7559020014fc7559020024ff7459020026bf7459020006be5459020006bd5459020004ff735902000cfe7359020004fd735902000cfc73590200067f53590200067d5359020006bf4359020006bd435902003cff725902003cfe725902003cfd725902003cfc725902003ebe425902003ebc4259020004ff715902001cfc7159020024fe7059020024fc7059020026be4059020026bc4059020004ff7558420014fe7558420004fd7558420014fc7558420004ff7458420006bf7458420004bf74584200bcfc7458420006bc7458420004bc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d5358420026f77158420006f65158420006f55158420006f63158420006f5315842003ef7215842003ef42158420024ff7058420024fd7058420026ef2058420026fa2058420026ed205842003ef92058420026f61058420026f410584200bcff76d0420024fe76d0420004fd76d04200bebe64d0420006bd64d042001cff7690420024fe7690420004fd769042007d7e75904200057d75904201f6bf64904201f6bc6490420075de7390420005dd739042001ef66190420006f56190420004ff7650420004fd7650420024fc7650420006be6450420006bd645042001ef66150420006f5615042001cff7610420024fe7610420004fd76104201e6bf64104200bebc64104200bcff7599310014fe7599310004fd75993100bcfc759931001ebe749
  | 9 => 0xf53191200067d531912003cfe721912003cfc721912001cfe7119120004fd7119120024fe76d0920006bf64d09200bebc64d0920025fa70d0920005f970d0920025ee76d0920006ee76d0920024ee76d09202a5ef75d09202a5ed75d092003dee74d0920006ef64d0920007af64d0920006ed64d0920007ac64d092029fae54d092029fad54d0920285ef73d0920285ed73d09202976f53d09202976d53d0920297af43d0920297ad43d0920005ed71d0920025ee70d0920007ea70d0920025ea70d0920007e970d0920025ec70d092003eef60d092003feb60d092022fae40d092022fac40d0920297ea30d0920297e930d0920024fc7650920006bf6450920006bc645092003fac4250920005fb7050920025f8705092003fe82050920005ee761092003eee761092003def751092003f6e751092028ded751092003f6d75109200056d7510920285ee741092003fae7410920006ef6410920007ae6410920006ed6410920007ad641092003def731092027ded73109202776f53109202776d5310920005ed7110920025ee7010920025ec701092003eef601092003feb6010920277ea3010920277e93010920004ff75d8520014fe75d8520004fd75d8520014fc75d85200bcfe74d8520004fd74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d8520024fe70d8520024fc70d8520006f761985200057f755852008d7c7558520005bf7458520005bc7458520005df7358520085dc735852008d7e75185200057d7518520005be7418520005bd7418520085de7318520005dd731852001ef66118520006f56118520004fe76d0520004fd76d05200bcfc76d05200bebe64d0520006bd64d0520007af42d0520006f761d052001ef461d0520004fe7690520004fd769052001cfc769052008d7e75905200057d7590520006bf6490520006bc6490520085de7390520005dd739052003dee7290520005ed7290520007ac4290520025fa7090520005f97090520004ff7650520004fe7650520004fc7650520006be6450520006bd6450520005ef725052003dec7250520007af4250520004fe7610520004fd761052001cfc7610520006bf64105200bebc641052003dee7210520005ed7210520007ac4210520006f7611052001ef46110520025fa7010520005f97010520005ee76c852003eee76c852003def75c852026ded75c8520005ee74c852003dec74c852003def73c8520265ed73c852025f6f53c852025f6d53c852001eee61c852001eec61c852003feb70c8520025ee70c8520025ec70c852003fe870c852003eef60c852003feb60c852025fea30c852025fe930c8520024fe768852024ded7288520006f7618852001ef46188520025fa7088520005f97088520024fc7648520005bf7448520
  | 10 => 0x9220026bf1059220026be1059220026bd1059220026bc10592200bebe64d0a20006bd64d0a20025fa70d0a20005f970d0a20006be6450a20006bd6450a20005fb7050a20025f87050a20004ff7558620014fe7558620004fd7558620014fc7558620004ff74586200bcfc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d5358620026f77158620006f65158620006f55158620006f63158620006f53158620024fc7058620026ef2058620026ed2058620026f61058620026f410586200bcff76d0620024fe76d0620004fd76d06200bebe64d0620006bd64d062001cff7690620024fe7690620004fd769062009d7e75906200057d7590620006be6490620006bd6490620095de7390620005dd7390620025fa7090620005f97090620004ff7650620004fd7650620024fc7650620006be6450620006bd645062001cff7610620024fe7610620004fd76106200bebe6410620006bd6410620025fa7010620005f97010620006be6488620006bd648862001ef66188620006f56188620025fa7088620005f9708862001cff7648620005bf7448620005bc7448620006be6448620006bd644862001ef66148620006f56148620005fb7048620025f87048620004ff75d9120014fe75d9120004fd75d9120014fc75d9120004ff73d912000cfe73d9120004fd73d912000cfc73d91200067f53d91200067d53d9120006ed72d912001cfe71d9120004fd71d9120006bf64991200bcff7599120014fe7599120004fd75991200bcfc75991200bcfe74991200bebe5499120006bd54991200bcff739912000cfe7399120004fd739912000cfc73991200067f53991200067d53991200bebf4399120006bd4399120004fd72991200beed72991202b6be42991200bebc429912001cfe7199120004fd7199120004fd70991200bef9709912022ebe40991200bebc40991200057f755912008d7c7559120005df7359120085dc7359120005f77159120005f47159120004ff75591200067f75591200047f7559120014fe7559120004fd7559120014fc75591200067c75591200147c7559120006bf7459120006be5459120006bd5459120004ff7359120006df7359120004df735912000cfe7359120004fd735912000cfc7359120006dc735912000cdc73591200067f53591200067d5359120006bf4359120006bd4359120004ff7259120006ef72591202aebe42591202aebc4259120004ff7159120006f77159120004f7715912001cfc7159120006f4715912001cf47159120004ff7059120006fb7059120226be4059120226bc4059120004fe7619120006bd64191200bcff7519120014fe7519120004fd75191200bcfc75191200bebe74191200bcff731912000cfe7319120004fd731912000cfc73191200067
  | 11 => 0x5ef725032003dec72503202afac42503200bcff7599220014fe7599220004fd75992200bcfc7599220026be7499220006bf54992200bebe5499220006bd54992200bebc54992200bcff739922000cfe7399220004fd739922000cfc73992200067f53992200067d53992200bebf4399220006be4399220006bd43992200bebc439922001cfe7199220004fd7199220024fe7099220026be4099220026bc4099220026ef2099220026ed20992200bebf7599220006be7599220006bd75992200bebc75992200bebf7399220006be7399220006bd73992200bebc7399220006bf53992200063f5399220006be5399220006bd53992200063d5399220006bc53992200bebf72992202b6be7299220006bd72992200bebc7299220006bf52992202b6be5299220006bd52992202b6bc5299220006bf32992202b6be3299220006bd32992202b6bc32992200bebf7199220006be7199220006bd71992200bebc7199220006bf5199220006be5199220006bd5199220006bc5199220006bf3199220006be3199220006bd3199220006bc31992202b6bf21992202b6bc2199220026bf7099220026be7099220026bd7099220026bc7099220026bf5099220026be5099220026bd5099220026bc5099220026bf3099220026be3099220026bd3099220026bc3099220026bf2099220026af2099220026be2099220026bd2099220026ad2099220026bc2099220026bf1099220026be1099220026bd1099220026bc1099220004ff7559220014fe7559220004fd7559220014fc7559220026bf7459220006bf5459220006be5459220006bd5459220006bc5459220004ff735922000cfe7359220004fd735922000cfc73592200067f53592200067d5359220006bf4359220006be4359220006bd4359220006bc4359220004ff715922001cfc7159220024fc7059220026be4059220026bc4059220006bf7559220006be7559220006bd7559220006bc7559220006bf7359220006be7359220006bd7359220006bc7359220006bf53592200063f5359220006be5359220006bd53592200063d5359220006bc5359220006bf72592202aebe7259220006bd72592202aebc7259220006bf52592202aebe5259220006bd52592202aebc5259220006bf32592202aebe3259220006bd32592202aebc3259220006bf7159220006be7159220006bd7159220006bc7159220006bf5159220006be5159220006bd5159220006bc5159220006bf3159220006be3159220006bd3159220006bc31592202aebf21592202aebc2159220026bf7059220026be7059220026bd7059220026bc7059220026bf5059220026be5059220026bd5059220026bc5059220026bf3059220026be3059220026bd3059220026bc3059220026bf2059220026be2059220026bd2059220026bc205
  | 12 => 0xe725932003ebd725932003ebc725932003eac725932003ebf525932003ebe525932003ebd525932003ebc525932003ebf325932003ebe325932003ebd325932003ebc3259320006bf7159320006be7159320006bd7159320006bc7159320006bf5159320006be5159320006bd5159320006bc5159320006bf3159320006be3159320006bd3159320006bc315932003ebf215932003ebe215932003ebd215932003ebc2159320006bf7059320226be7059320006bd7059320226bc7059320006bf5059320226be5059320006bd5059320226bc5059320006bf3059320226be3059320006bd3059320226bc305932003ebf205932003ebe205932003ebd205932003ebc2059320226be1059320226bc105932003ded76d0b20006ed76d0b202fdef75d0b202fded75d0b2003f6e65d0b2003f6d65d0b2003fae74d0b2003eef64d0b2003fae64d0b20006ed64d0b2003fad64d0b20006ad64d0b202f7ae54d0b202f7ad54d0b202edef73d0b202eded73d0b202e76f53d0b202e76d53d0b202e7af43d0b202e7ad43d0b20005ed71d0b20025ee70d0b20025ec70d0b2022fae40d0b2022fac40d0b20004ff7558720014fe7558720004fd7558720014fc7558720004ff74587200bcfc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d5358720024fc725872003ef77158720006f63158720006f5315872003ef7215872003ef4215872003efa205872003ef920587200bcff76d072003cfe76d0720004fd76d07201767e65d07200067d65d07200bebe64d0720006bd64d072003dec72d0720007af42d072001cff769072003cfe7690720004fd76907200ad7e75907200057d759072016e7e65907200067d6590720006be6490720006bd64907200a5de7390720005dd739072003dee7290720005ed72907202dfac4290720004ff7650720004fd765072003cfc765072015e7e65507200067d6550720006be6450720006bd6450720005ef725072003dec7250720007af425072001cff761072003cfe7610720004fd76107201467e65107200067d65107200bebe6410720006bd641072003dee7210720005ed72107202d7ac421072003def7648720006ef76487202cdef75487202cded754872003f6e654872003f6d6548720007af7448720005ee7448720005ec7448720007ac7448720005ac744872003fae644872003fad64487202c5ef73487202c5ed73487202bf6f53487202bf6d534872003fe7714872001eee614872001eec61487202bfe631487202bfe53148720025ee7048720025ec70487200f67e65d03200067d65d03200bebe64d0320006bd64d032003dee72d0320005ed72d03202b7ac42d03200057f75503200ad7c75503200de7e65503200067d6550320006be6450320006bd6450320
  | 13 => 0x97200067f43597200067e43597200067d43597200067c435972003e7f725972003e7e725972003e7d725972003e7c725972003e7f425972003e7e425972003e7d425972003e7c425972003e7f325972003e7e325972003e7d325972003e7c32597200067f71597200067e71597200067d71597200067c71597200067f31597200067e31597200067d31597200067c315972003e7f215972003e7e215972003e7d215972003e7c21597200ae7f70597203067e70597200067d70597203067c70597203067e40597203067c40597200067f30597203067e30597200067d30597203067c305972003e7f205972003e7e205972003e7d205972003e7c20597203067e10597203067c10597200bcff7599320014fe7599320004fd75993200bcfc759932003ebe7499320006bf54993200bebe5499320006bd54993200bebc54993200bcff739932000cfe7399320004fd739932000cfc73993200067f53993200067d53993200bebf4399320006be4399320006bd43993200bebc4399320024fe729932003ebe429932003ebc429932001cfe7199320004fd71993200bebf7599320006be7599320006bd75993200bebc75993200bebf7399320006be7399320006bd73993200bebc7399320006bf53993200063f5399320006be5399320006bd53993200063d5399320006bc539932003ebf729932003ebe729932003ebd729932003ebc729932003ebf529932003ebe529932003ebd529932003ebc529932003ebf329932003ebe329932003ebd329932003ebc32993200bebf7199320006be7199320006bd71993200bebc7199320006bf5199320006be5199320006bd5199320006bc5199320006bf3199320006be3199320006bd3199320006bc319932003ebf219932003ebe219932003ebd219932003ebc21993200bebf709932022ebe7099320006bd70993200bebc7099320006bf509932022ebe5099320006bd509932022ebc5099320006bf309932022ebe3099320006bd309932022ebc309932003ebf209932003ebe209932003ebd209932003ebc209932022ebe109932022ebc1099320004ff7559320014fe7559320004fd7559320014fc755932003ebf7459320006bf5459320006be5459320006bd5459320006bc5459320004ff735932000cfe7359320004fd735932000cfc73593200067f53593200067d5359320006bf4359320006be4359320006bd4359320006bc4359320024fc725932003eec7259320024ec725932003ebe425932003ebc425932003eec4259320004ff715932001cfc7159320006bf7559320006be7559320006bd7559320006bc7559320006bf7359320006be7359320006bd7359320006bc7359320006bf53593200063f5359320006be5359320006bd53593200063d5359320006bc535932003ebf725932003eb
  | 14 => 0x26ee2058840026ec205884003cbd76d08400bebf65d084035ebd65d08400bebf63d0840356bd63d08403573f53d08403573d53d084003ebe62d08400bfae62d08400bfad62d084003ebc62d08401edbe71d08400bfba70d084022dbd70d08400bfb970d084022ebe60d08400bfba60d0840004fd7690840225bd74908402b6be6490840004ff7650840225bf7650840006bf7650840004bf7650840226bf655084034ebd6550840226bf6350840346bd63508403473f53508403473d53508400bdbf72508400bfaf725084003ebe625084003ebc62508401edbc7150840225bf7050840226be6050840227ba6050840004ff7558440014fe7558440004fd7558440014fc7558440004ff735844000cfe7358440004fd735844000cfc73584400067f53584400067d5358440004ff725844003cfc7258440006bf4258440006bd4258440026f77158440006f65158440006f551584400bef741584400bef44158440006f63158440006f53158440026bf4058440026bd4058440026f61058440026f41058440004fd76904400c57e75904400057d75904400b5de7390440005dd73904401f5bd76904401eebd7690440004bd76904401ef3e75904401ef3d75904401f6bf659044033ebd65904401ef9e73904401ef9d73904401f6bf6390440336bd63904403373f53904403373d5390440005bd72904402debe62904400bdbe71904401f6bf61904401eebd61904401f5bf70904401f5bd70904401f6be60904401f7ba6090440004ff765044032ebe64504400bebf6510440326bd65104400bebf631044031ebd631044031f3f531044031f3d5310440005bd72104402d6be62104401f5be71104400bfb671104400bebf61104400bfb661104401eebd61104400bfb561104401efb6311044031fb531104400bdbf70104400bfba70104401e5bd70104400bfb970104401e6be60104400bfba601044003cff76c8440024fe76c8440004fd76c84400bdbe74c8440005bd74c844003eee62c8440006ed62c844001cff7688440024fe7688440004fd76884401edbf74884400bdbc748844001ef66188440006f56188440004ff7648440004fd7648440024fc7648440005bf74484400bdbc744844003eee6248440006ed624844001ef66148440006f5614844001cff7608440024fe7608440004fd76084400c57e75084400057d75084400bdbe7408440005bd74084400b5de7308440005dd7308440025fa7008440005f97008440025fb7650040006fb7650040004fb76500400077b7550040317787550040025fb7450040027bb74500400befa6450040027ba645004030f7b535004030f7953500400067f74597200067e74597200067d74597200067c74597200067f73597200047f73597200067e73597200067d73597200047d73597200067c735
  | 15 => 0xc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d854003cfe72d8540004fd72d8540006f631d8540006f531d85400dd7e75985400057d75985400067f65985400067c65985401f6bf64985400d5de7398540005dd7398540006f761985400057f75585400dd7c75585400067f65585400067c65585400067f65185400067c65185401e6bf641854001ef66118540006f56118540004fe76d05400067f65d05401767c65d0540005be76d0540006be76d0540004be76d05403adbf75d05403adbd75d05400073f65d05403a73c65d0540375bf73d0540375bd73d054039f3f53d054039f3d53d05402adbe72d0540006bf62d054001ebe61d054001ebc61d054039fb631d054039fb531d0540025be70d0540025bc70d05400bebf60d0540024fe76905400dd7e75905400057d75905400067f659054016e7c6590540385bd74905400d5de7390540005dd7390540006f7619054001ef46190540025fa7090540005f97090540024fc76505400067f655054015e7c6550540006f7615054001ef46150540005fb7050540025f87050540024bc7650540395bf7550540395bd75505400073f655054038f3c6550540385bf7350540385bd735054037f3f535054037f3d53505402adbc7250540006bf6250540007b77150540007b7615054001ebe615054001ebc6150540007b46150540007bb7050540025be7050540025bc7050540007b87050540004fe76105400067f65105401467c6510540375be7410540004fe76c8540004fd76c854003cfc76c85400067f65c85401367c65c85402adbf74c85402adbc74c8540006f761c854001ef461c8540004fe7688540004fd768854001cfc76885400067f65885401267c6588540005be7488540005bd7488540004ff7648540004fe7648540004fc76485400067f65485401167c6548540005bf7448540005bc7448540004fe7608540004fd760854001cfc76085400dd7e75085400057d75085400067f65085401067c6508540005be7408540005bd74085400d5de7308540005dd7308540006f7610854001ef46108540025fa7008540005f970085400067f65d01400f67c65d0140025be74d0140026bf64d0140024fa76d01400077b65d014036f7865d0140025fa74d0140026fb64d0140027bb64d01400bfba54d014036fb954d01403677b53d01403677953d01400bfbb43d0140367b943d0140007ba42d01400bfb842d01400bfbb41d0140007b941d0140004ff7558840014fe7558840004fd7558840014fc7558840004ff735884000cfe7358840004fd735884000cfc73588400067f53588400067d5358840026ef7258840006ee5258840006ed52588400beef42588400beec4258840006ee3258840006ed3258840004ff715884001cfc7158840
  | 16 => 0x240027e962d02400dd7e76d95400de7e76d95400147e76d95403f73f74d95400df3c74d95400057f73d95400057d73d95400067f63d95400067e63d95400067d63d95400067c63d95400073f43d95400073d43d95403f73e40d95403f73c40d95403f67f74d95400de7e74d95400de7d74d95400de7c74d95400067f73d95400047f73d95400067e73d95400067d73d95400047d73d95400067c73d95400067f43d95400067e43d95400067d43d95400067c43d95400067f72d95400067e72d95400067d72d95400067c72d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067e31d95400067d31d95400067c31d95400067f70d95403f67e70d95400de7d70d95403f67c70d95403f67e40d95400de7d40d95403f67c40d95400067f30d95403f67e30d95400067d30d95403f67c30d95403f67e20d95403f67c20d95403f67e10d95403f67c10d95400067f65d89400067c65d8940004ff75d8940014fe75d8940004fd75d8940014fc75d8940006be54d8940006bd54d8940004ff73d894000cfe73d8940004fd73d894000cfc73d89400067f53d89400067d53d8940006bf43d8940006bd43d894001cfe71d8940004fd71d894022ebe40d894022ebc40d89400dd7e75989400057d75989400067f65989400067c6598940006ef62989400057f75589400dd7c75589400067f65589400067c6558940005df73589400d5dc7358940005f77158940005f471589400067f65189400067c651894003eee6218940006ed6218940004fe76d09400067f65d09401b67c65d0940024fe76909400067f65909401ae7c6590940006ef629094003eec6290940025fa7090940005f97090940024be76909402adbf75909403edbd75909400073f65909403e73c65909402adbf73909403ddbd73909403d73f53909403d73d53909402adbe72909402aebf6290940007af62909402afac6290940005bd719094023ebc6190940025be70909402afba70909402afb97090940025bc7090940024fc76509400067f655094019e7c6550940006ef625094003eec6250940005fb7050940025f87050940004fe76109400dd7e75109400057d75109400067f65109401867c651094003eee6210940007ad4210940005be76109402aebe7610940004be76109402adbf75109402af3e75109403cdbd75109402af3d75109400053d75109400073f65109403c73c65109402adbf73109403bdbd73109403b73f53109403b73d53109402adbe72109402afae72109402aebf62109402afae6210940007ad6210940005bd7110940236bc6110940025be7010940025bc70109400bebf60109400067f65d85400067c65d8540004ff75d8540014fe75d8540004fd75d8540014f
  | 17 => 0x22ebf65d0a40446bd65d0a4022ebf63d0a4043ebd63d0a4043f3f53d0a4043f3d53d0a4003ebe62d0a4022fae62d0a4003eae62d0a4022fad62d0a4003ebc62d0a401fdbe71d0a4022dbd70d0a4003eee6290a40006ed6290a40025fa7090a40005f97090a4003cff7650a4003eee6250a40006ed6250a40005fb7050a40025f87050a4003cbf7650a40226bf6550a40436bd6550a40226bf6350a4042ebd6350a4042f3f5350a4042f3d5350a40007af7250a4003ebe6250a40227ae6250a4003eae6250a40227ad6250a4003ebc6250a401fdbc7150a40225bf7050a40007bb7050a40227b87050a400ed7e7510a400057d7510a4003eee6210a40006ed6210a40004ff7558640014fe7558640004fd7558640014fc7558640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640004ff725864003cfc7258640006bf4258640006bd4258640026f77158640006f65158640006f55158640006f63158640006f53158640026bf4058640026bd4058640026f61058640026f41058640006ee62d0640006ed62d06400ed7e75906400057d75906400e5de7390640005dd7390640006ee6290640006ed629064001ef66190640006f56190640025fa7090640005f970906401ff3e75906401ff3d75906401f6bf6590640426bd65906401ff9e73906401ff9d73906401f6bf639064041ebd639064041f3f539064041f3d5390640005bd72906402debe62906401f7ae6290640006ae62906401f7ad62906401f6bf61906401f7b661906401febd61906401f7b561906401f7ba70906401f5bd70906401ffb9709064001cff7650640006ee6250640006ed625064001ef66150640006f56150640005fb7050640025f87050640006ee6210640006ed62106401e5bd76106401febd76106401e6bf6510640416bd65106401e6bf631064040ebd631064040f3f531064040f3d5310640005bd72106402d6be62106401e7ae6210640006ae62106401e7ad62106401ffb671106401e6bf61106401febd61106401ffb6311064040fb531106401e5bf70106401e5bd701064003cff76c8640024fe76c8640004fd76c8640005be74c8640005bd74c864003eee62c8640006ed62c864001cff7688640024fe7688640004fd76886401fdbf74886401fdbc748864003eee6288640006ed6288640004ff7648640004fd7648640024fc7648640005bf7448640005bc744864003eee6248640006ed624864001cff7608640024fe7608640004fd76086400ed7e75086400057d7508640005be7408640005bd74086400e5de7308640005dd730864003eee6208640006ed6208640025fa7008640005f97008640025f976d02400bef976d0240027ba74d02400bfba54d0240407b954d02403ff7b53d02403ff7953d0240027ea62d
  | 18 => 0xd62507400bfb7715074001ebe615074001ebc6150740025be7050740025bc705074003cff76c87400bcfe76c8740004fd76c87402b5bf74c87400bdbc74c874001cff76887400bcfe7688740004fd76887400bdbe7488740005bd7488740004ff7648740004fd76487400bcfc7648740005bf74487400bdbc744874001cff76087400bcfe7608740004fd76087400f57e75087400057d75087400bdbe7408740005bd74087400cdde7308740005dd7308740025fa7008740005f9700874003eef7598a4003eee7598a4003e6e7598a4003eed7598a4003e6d7598a4003eec7598a4003eef7498a40006ef5498a40006ee5498a40006ed5498a40006ec5498a4003eef7398a4003eee7398a4003eed7398a4003eec7398a40006ef5398a400066f5398a40006ee5398a40006ed5398a400066d5398a40006ec5398a40006ef4398a40006ee4398a40006ed4398a40006ec4398a4003eef7198a4003eee7198a4003eed7198a4003eec7198a40006ef5198a40006ee5198a40006ed5198a40006ec5198a40006ef3198a40006ee3198a40006ed3198a40006ec3198a40026ef7098a40026ee7098a40026ed7098a40026ec7098a40026ef5098a40026ee5098a40026ed5098a40026ec5098a40026ef4098a40026af4098a40026ee4098a40026ed4098a40026ad4098a40026ec4098a40026ef3098a40026ee3098a40026ed3098a40026ec3098a40026ef1098a40026ee1098a40026ed1098a40026ec1098a40004ff7558a40014fe7558a40004fd7558a40014fc7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a400067f5358a400067d5358a40026ef7258a40006ef5258a40006ee5258a40006ed5258a40006ec5258a40006ef3258a40006ee3258a40006ed3258a40006ec3258a40004ff7158a4001cfc7158a40026ee2058a40026ec2058a40006ef7558a40006ee7558a40006ed7558a40006ec7558a40006ed7458a40006ef5458a40006ee5458a40006ed5458a40006ec5458a40006ef7358a40006ee7358a40006ed7358a40006ec7358a40006ef5358a400066f5358a40006ee5358a40006ed5358a400066d5358a40006ec5358a40006ef4358a40006ee4358a40006ed4358a40006ec4358a40006ef7158a40006ee7158a40006ed7158a40006ec7158a40006ef5158a40006ee5158a40006ed5158a40006ec5158a40006ef3158a40006ee3158a40006ed3158a40006ec3158a40026ef7058a40026ee7058a40026ec7058a40026ef5058a40026ee5058a40026ed5058a40026ec5058a40026ef4058a40026ee4058a40026ed4058a40026ec4058a40026ef3058a40026ee3058a40026ed3058a40026ec3058a40026ef1058a40026ee1058a40026ed1058a40026ec1058a4003eee62d0a4022dbd76d0a40006bd76d0a40
  | 19 => 0x8021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb53580210067b5358021006fa5358021006f95358021006795358021006f85358021006fb4358021006fa4358021006f94358021006f8435802103efb725802103efa725802103ef8725802103efb525802103efa525802103ef9525802103ef8525802103efb425802103efa425802103ef9425802103ef8425802103efb325802103efa325802103ef9325802103ef8325802101efb715802101efa715802101ef8715802101efb515802101efa515802101ef9515802101ef8515802101efb415802101efa415802101ef9415802101ef8415802101efb315802101efa315802101ef9315802101ef8315802101efb215802101eeb215802101efa215802101ef9215802101ee9215802101ef821580210beef6298b4003eec6298b400beec6258b40004ff7558b40014fe7558b40004fd7558b40014fc7558b40024fc7458b40006be5458b40006bd5458b40004ff7358b4000cfe7358b40004fd7358b4000cfc7358b400067f5358b400067d5358b40006bf4358b40006bd4358b400beef4258b400beec4258b40004ff7158b4001cfc7158b40226be4058b40226bc4058b40005bd7690b402b6bd7690b402b5bf7590b4049dbd7590b402b5bf7390b40495bd7390b4048f3f5390b4048f3d5390b402b6bd6290b40005bd7190b4023ebe6190b40025be7090b40025bc7090b400bfac4250b40024bd7610b400bdbf7510b400bf3e7510b40485bd7510b400bf3d7510b400053d7510b400bdbf7310b4047dbd7310b404773f5310b404773d5310b400bfae7210b400bfae6210b402b6bd6210b400bfad6210b40005bd7110b40236be6110b40025be7010b400bfba7010b400bfb97010b40025bc7010b400f57e75987400057d75987401f6be64987400cdde7398740005dd73987400bef7619874001ef461987400bef46158740004ff7558740014fe7558740004fd7558740014fc7558740024fc7458740004ff735874000cfe7358740004fd735874000cfc73587400067f53587400067d5358740004ff725874003cfc72587400bef741587400bef44158740024bd76d07400bdbf75d074046dbd75d07400bdbf73d0740465bd73d074045f3f53d074045f3d53d07402b5be72d0740006bd62d074001ebe61d07400bfb661d07400bfb561d074001ebc61d074045fb631d074045fb531d0740025be70d07400bfba70d07400bfb970d0740025bc70d07400f57e75907400057d75907400cdde7390740005dd7390740005bf7650740006bf7650740455bf7550740455bd755074044dbf735074044dbd735074032f3f535074032f3d53507402b5bc7250740006b
  | 20 => 0x6bc7059021006bf5059021006be5059021006bd5059021006bc5059021006bf3059021006be3059021006bd3059021006bc305902103ebf205902103ebe205902103ebd205902103ebc205902101ebf105902101ebe105902101ebd105902101ebc1059021006df7558c21006de7558c210065e7558c21006dd7558c210065d7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2103edf7258c2103ede7258c2103edd7258c2103edc7258c2103edf5258c2103ede5258c2103edd5258c2103edc5258c2103edf4258c2103ede4258c2103edd4258c2103edc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101edf5158c2101ede5158c2101edd5158c2101edc5158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ede2158c2101ed62158c2101edd2158c2103ed52158c2101edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c2103edf2058c2103ede2058c2103edd2058c2103edc2058c2101edf1058c2101ede1058c2101edd1058c2101edc1058c21026fb7598021026fa7598021026f97598021026f87598021026fb7498021026fa7498021026f97498021026f87498021006fb5498021006fa5498021006f95498021006f85498021026fb7398021026fa7398021026f97398021026f87398021006fb53980210067b5398021006fa5398021006f95398021006795398021006f85398021006fb4398021006fa4398021006f94398021006f84398021026fb7298021026fa7298021026f97298021026f8729802103efb529802103efa529802103ef9529802103ef8529802103efb429802103efa429802103ef9429802103ef8429802103efb329802103efa329802103ef9329802103ef83298021026fb7198021026fa7198021026f97198021026f8719802101efb519802101efa519802101ef9519802101ef8519802101efb419802101efa419802101ef9419802101ef8419802101efb319802101efa319802101ef9319802101ef8319802101efb219802101efa219802101ef9219802101ef82198021004ff7558021014fe7558021004fd7558021014fc7558021004ff74580210bcfc7458021004ff735802100cfe7358021004fd735802100cfc73580210067f53580210067d535802101eef215802101eed215802101efb7058021006fb5058021006fa5058021006f95058021006f85058021006fb3058021006fa3058021006f93058021006f8305802103efb205802103ef8205802101efb105802101ef81058021006fb7558021006fa7558021006f97558021006f87558021006fb745
  | 21 => 0xf105942101e7e105942101e7d105942101e7c10594210bcff7599021014fe7599021004fd75990210bcfc759902101cfe749902101ebe7499021006bf54990210bebe5499021006bd54990210bebc54990210bcff739902100cfe7399021004fd739902100cfc73990210067f53990210067d53990210bebf4399021006be4399021006bd43990210bebc439902103cfe729902103cfc729902103ebe429902103ebc429902101cfe719902101cfc719902101ebe419902101ebc4199021024fe7099021004fd70990210bebf7599021006be7599021006bd75990210bebc75990210bebf7399021006be7399021006bd73990210bebc7399021006bf53990210063f5399021006be5399021006bd53990210063d5399021006bc539902103ebf729902103ebe729902103ebd729902103ebc729902103ebf529902103ebe529902103ebd529902103ebc529902103ebf329902103ebe329902103ebd329902103ebc329902101ebf719902101ebe719902101ebd719902101ebc719902101ebf519902101ebe519902101ebd519902101ebc519902101ebf319902101ebe319902101ebd319902101ebc319902101ebf219902101ebe219902101ebd219902101ebc21990210bebf7099021006be7099021006bd70990210bebc7099021006bf5099021006be5099021006bd5099021006bc5099021006bf3099021006be3099021006bd3099021006bc309902103ebf209902103ebe209902103ebd209902103ebc209902101ebf109902101ebe109902101ebd109902101ebc1099021004ff7559021014fe7559021004fd7559021014fc755902101cff745902101ebf7459021006bf5459021006be5459021006bd5459021006bc5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021006bf4359021006be4359021006bd4359021006bc435902103cfe725902103cfc725902103ebe425902103ebc425902101cfe715902101cfc715902101ebe415902101ebc4159021004ff7059021024fc7059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf53590210063f5359021006be5359021006bd53590210063d5359021006bc535902103ebf725902103ebe725902103ebd725902103ebc725902103ebf525902103ebe525902103ebd525902103ebc525902103ebf325902103ebe325902103ebd325902103ebc325902101ebf715902101ebe715902101ebd715902101ebc715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021006be7059021006bd7059021
  | 22 => 0x9121006be7519121006bd75191210bebc75191210bebf7319121006be7319121006bd73191210bebc7319121006bf53191210063f5319121006be5319121006bd53191210063d5319121006bc53191210bebf72191212d6be7219121006bd72191210bebc7219121006bf52191212d6be5219121006bd52191212d6bc5219121006bf32191212d6be3219121006bd32191212d6bc32191210bebf7119121236be7119121006bd71191210bebc7119121006bf5119121236be5119121006bd5119121236bc5119121006bf3119121236be3119121006b63119121006bd3119121006b53119121236bc31191212d6bf2119121236be2119121006bd2119121236bc21191210bebf7019121006be7019121006bd70191210bebc7019121006bf5019121006be5019121006bd5019121006bc5019121006bf3019121006be3019121006bd3019121006bc30191212d6bf20191212d6bc2019121236bf1019121236bc101912101cfe76d0921006bf64d09210bebc64d092101df671d0921005f571d092101cfc7650921006bf6450921006bc6450921005f7715092101df4715092103fe4215092103cfe76d0521006bf64d05210bebc64d052103dee72d0521005ed72d05210bcff7650521004fd765052103cfc7650521006bf6450521006bc6450521005ef725052103dec725052101fe42150521006bf64d8121006bc64d8121004ff75d8121014fe75d8121004fd75d8121014fc75d81210bcfe74d8121004fd74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006f631d8121006f531d8121005be7498121005bd7498121006bf6498121006bc6498121006fb60981210057f75581211157c7558121005bf7458121005bc7458121006bf6458121006bc6458121005df735812110ddc7358121006bf6418121006bc6418121026fa6018121006f960181210067f74594210067e74594210067d74594210067c74594210067f73594210047f73594210067e73594210067d73594210047d73594210067c73594210067f43594210067e43594210067d43594210067c435942103e7f725942103e7e725942103e7d725942103e7c725942103e7f425942103e7e425942103e7d425942103e7c425942103e7f325942103e7e325942103e7d325942103e7c325942101e7f715942101e7e715942101e7d715942101e7c715942101e7f415942101e7e415942101e7d415942101e7c415942101e7f315942101e7e315942101e7d315942101e7c315942101e7f215942101e7e215942101e7d215942101e7c21594210067f70594210067e70594210067d70594210067c70594210067f30594210067e30594210067d30594210067c305942103e7f205942103e7e205942103e7d205942103e7c205942101e7
  | 23 => 0x6be54d9121006bd54d9121006bc54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d9121006bf43d9121006be43d9121006bd43d9121006bc43d9121024fe70d9121004fd70d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006bf63d9121006be63d9121006bd63d9121006bc63d91210073f53d91210073d53d9121007b631d9121007b531d91212dfb721d912123fae21d912123fac21d91212dfb421d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d91210063f53d9121006be53d9121006bd53d91210063d53d9121006bc53d912123ebf72d91212debe72d9121006bd72d91212debc72d9121006bf52d91212debe52d9121006bd52d91212debc52d9121006bf32d91212debe32d9121006bd32d91212debc32d91212debf71d912123ebe71d9121006bd71d912123ebc71d9121006bf51d912123ebe51d9121006bd51d912123ebc51d9121006bf31d912123ebe31d9121006bd31d912123ebc31d91212debf21d912123ebe21d912123ebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006bf30d9121006be30d9121006bd30d9121006bc30d91212debf20d91212debc20d912123ebf10d912123ebc10d9121006bf64991210bcff7599121014fe7599121004fd75991210bcfc75991210bcfe7499121004be74991210bcff739912100cfe7399121004fd739912100cfc73991210067f53991210067d5399121004fd72991210beed7299121004fd71991210bef57199121006f63199121006f53199121024fe7099121004fd7099121004ff7559121014fe7559121004fd7559121014fc7559121006bf7459121004ff735912100cfe7359121004fd735912100cfc73591210067f53591210067d5359121004ff7259121006ef7259121004ff7159121006f77159121004ff7059121024fc7059121004fe7619121006bd64191210bcff7519121014fe7519121004fd75191210bcfc75191210bebe7419121006bf54191210bebe5419121006bd54191210bebc54191210bcff731912100cfe7319121004fd731912100cfc73191210067f53191210067d53191210bebf4319121006be4319121006bd43191210bebc4319121006f63119121006f53119121024fe7019121004fd7019121005be7619121006be7619121004be7619121006bf6519121006be6519121006bd6519121006bc6519121006bf6319121006be6319121006bd6319121006bc63191210073f53191210073d5319121007b63119121007b531191212d7b72119121237ae2119121237ac21191212d7b421191210bebf751
  | 24 => 0xc75580410147c7558041006be5458041006bd5458041004ff735804100cfe7358041004fd735804100cfc73580410067f53580410067d5358041006bf4358041006bd4358041004ff725804103cfc7258041006be4258041006bc425804101ebf415804101ebd415804101ef63158041006f5315804101efb7058041006fa5058041006f950580410befb40580410bef84058041006fa3058041006f9305804101efb105804101ef810580410bcff7599321014fe7599321004fd75993210bcfc759932103ebe74993210bebe5499321006bd54993210bcff739932100cfe7399321004fd739932100cfc73993210067f53993210067d53993210bebf4399321006bd439932101cfe729932103ebe429932103ebc4299321024fe7099321004fd709932103eef2099321004ff7559321014fe7559321004fd7559321014fc755932103ebf7459321006be5459321006bd5459321004ff735932100cfe7359321004fd735932100cfc73593210067f53593210067d5359321006bf4359321006bd435932101cfc725932103ebe425932103ebc4259321004ff7059321024fc70593210bebe64d0721006bd64d072103dee72d0721005ed72d0721006be6450721006bd6450721005ef725072103dec7250721004ff7558321014fe7558321004fd7558321014fc7558321004ff74583210bcfc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d535832101cfc725832103efb7058321006fa3058321006f9305832103efb205832103ef820583210bcff7599221014fe7599221004fd75992210bcfc759922101ebe74992210bcff739922100cfe7399221004fd739922100cfc73992210067f53992210067d539922101cfe719922101ebe419922101ebc419922101ef63199221006f53199221024fe7099221004fd7099221004ff7559221014fe7559221004fd7559221014fc755922101ebf7459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d535922101cfc715922101ebe415922101ebc4159221004ff7059221024fc70592210bebe64d0a21006bd64d0a2101df671d0a21005f571d0a21006be6450a21006bd6450a21005f77150a2101df47150a21004ff75582210067f75582210047f7558221014fe7558221004fd7558221014fc75582210067c75582210147c7558221004ff7458221006bf7458221004bf74582210bcfc7458221006bc7458221004bc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d535822101cfc715822101ef63158221006f5315822101eef215822101eed215822101efb705822101efb105822101ef81058221004ff75d9121014fe75d9121004fd75d9121014fc75d9121006bf54d9121
  | 25 => 0x94151ebd63d094151f3f53d094151f3d53d094103ebe62d094103ebc62d094101dbe71d094101dbc71d09410bebf61d0941005bd70d094122ebc60d094101cfe7690941515bd7490941006ef629094103eec629094101df67190941005f5719094101cfc7650941006ef625094103eec6250941005f7715094101df4715094101cbc765094150ebf655094150ebd6550941506bf6350941506bd63509415073f53509415073d5350941007af7250941007af625094103ebe625094103ebc6250941007ac6250941007b7715094101dbe715094101dbc7150941007b47150941005bf7050941226bc6050941004fe761094115d7e75109410057d75109414fdbe741094101dbe74d054101ebf64d054101df674d054101ef764d054101fb764d05414f6f763d05414f6f563d05414f77753d05414f77553d05410bfb742d0541007b542d0541004ff75d8141014fe75d8141004fd75d8141014fc75d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d814103cfe72d8141004fd72d8141005ee7298141005ed7298141006fb60981410057f755814115d7c75581411f6bf6418141026fa6018141006f96018141004ff7558841014fe7558841004fd7558841014fc7558841006be5458841006bd5458841004ff735884100cfe7358841004fd735884100cfc73588410067f53588410067d5358841006bf4358841006bd435884101eef7258841006ee5258841006ed52588410beef42588410beec4258841006ee3258841006ed325884101ebf415884101ebd415884101ef63158841006f5315884101eee215884101eec2158841004ff7058841024fc7058841004fd769084123dbd76908412d6bd7690841004bd76908412d5bf75908414edbd75908412d5bf73908414e5bd73908414df3f53908414df3d53908410bdbe729084123ebf62908412d6bd629084123dbf719084123dbd719084123ebe619084123fb6619084123fb631908414dfb531908411e5be7090841004ff76508414d6be64508410bdbf75108410bf3e75108414cdbd75108410bf3d75108410053d75108410bdbf73108414c5bd73108414bf3f53108414bf3d531084123dbe72108410bfae72108410bebf62108410bfae62108412d6bd62108410bfad62108410bdbf71108410bfb67110841235bd71108410bfb57110841236be61108410bfb66110841237b631108414bfb531108411e5be701084101df77650441006f77650441004f7765044101df7745044101fb774504410bef6645044101fb664504410bfb654504414b7b554504414adf773504414adf573504414a77753504414a77553504410bfb743504414a7b54350441004ff75580410067f75580410047f7558041014fe7558041004fd7558041014fc75580410067
  | 26 => 0x1edd4158e4101edc4158e4101ed44158e4101edf2158e4101ede2158e4101edd2158e4101edc2158e41006df7058e41006de7058e41006dd7058e41006dc7058e41006df5058e41006de5058e41006dd5058e41006dc5058e4101edf1058e4101ede1058e4101edd1058e4101edc1058e41004ff7558a41014fe7558a41004fd7558a41014fc7558a41006be5458a41006bd5458a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a41006bf4358a41006bd4358a4101eef7258a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a41024fc7058a411b67e65d0a410067d65d0a4118ede63d0a41006dd63d0a411ae7e6590a410067d6590a411a6de6390a41006dd6390a4103eee6290a41006ed6290a4101df67190a41005f57190a412ddbf7590a41565bd7590a4123f3e6590a4123f3d6590a412ddbf7390a4155dbd7390a4123f9e6390a4123f9d6390a415573f5390a415573d5390a4123ebf6290a4123fae6290a412debd6290a4123fad6290a4123fb67190a4123dbd7190a412dfb57190a411f5be7090a4103cff7650a4119e7e6550a410067d6550a41196de6350a41006dd6350a4103eee6250a41006ed6250a41005f77150a4101df47150a4116d7e7510a410057d7510a411867e6510a410067d6510a4117ede6310a41006dd6310a41235bd7610a412debd7610a412ddbf7510a412df3e7510a4154dbd7510a412df3d7510a410053d7510a412373e6510a412373d6510a412ddbf7310a41545bd7310a412379e6310a412379d6310a4153f3f5310a4153f3d5310a412dfae7210a41236bf6210a412debd6210a41235bf7110a41235bd7110a411f5be7010a4101df576d06410bef576d064101f7665d064101f7565d064101fb674d06410bfb654d0641537b554d064101ef763d064101fd663d064152ef563d064101fd563d0641006d563d064152f7753d064152f7553d0641004ff7558241014fe7558241004fd7558241014fc7558241006be5458241006bd5458241004ff735824100cfe7358241004fd735824100cfc73582410067f53582410067d5358241006bf4358241006bd4358241004ff725824103cfc7258241006be4258241006bc425824101ebf415824101ebd415824101efb705824101efb105824101ef81058241004ff75d8941014fe75d8941004fd75d8941014fc75d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d8941006ef32d8941006ec32d8941024fe70d8941004fd70d894123ebf6498941006ef629894115d7e75189410057d7518941236bf641894103eee6218941006ed6218941004fe76d0941005be76d0941006be76d0941004be76d0941526bf65d0941526bd65d094151ebf63d
  | 27 => 0xf715804201cfc715804203efb70580420befb40580420bef84058042006fa3058042006f9305804203efb205804203ef8205804223ebe6498b410beef6298b4103eec6298b410beec6258b41004ff7558b41014fe7558b41004fd7558b41014fc7558b4101cfc7458b41004ff7358b4100cfe7358b41004fd7358b4100cfc7358b410067f5358b410067d5358b410beef4258b410beec4258b41006f63158b41006f53158b41004ff7058b41024fc7058b4101cbd76d0b410bebf65d0b4157ebd65d0b410bebf63d0b41576bd63d0b415773f53d0b415773d53d0b4103ebe62d0b410bfae62d0b410bfad62d0b4103ebc62d0b4101dbe71d0b410bfb671d0b410bfb571d0b4101dbc71d0b41577b631d0b41577b531d0b41005bd70d0b4122ebe60d0b41005bf7650b41006bf7650b4156ebf6550b4156ebd6550b414d6bf6350b414d6bd6350b414d73f5350b414d73d5350b410bfaf7250b4103ebe6250b4103ebc6250b4101dbe7150b4101dbc7150b414d7b63150b414d7b53150b41005bf7050b41226be6050b411e6be6498341005ee7298341005ed72983410befb6098341026f860983410bef86058341004ff7558341014fe7558341004fd7558341014fc755834101cfc7458341004ff735834100cfe7358341004fd735834100cfc73583410067f53583410067d5358341004ff725834103cfc7258341006f63158341006f531583410befb40583410bef8405834116e7f745964116e7e74596410067d745964116e7c74596410067f73596410047f73596410067e73596410067d73596410047d73596410067c73596410067f43596410067e43596410067d43596410067c43596410067f72596410067e72596410067d72596410067c72596410067f32596410067e32596410067d32596410067c325964101e7f715964101e7e715964101e7d715964101e7c715964101e7f415964101e7e415964101e7d415964101e7c415964101e7f315964101e7e315964101e7d315964101e7c315964101e7f215964101e7e215964101e7d215964101e7c21596410067f70596410067e70596410067d70596410067c70596410067f30596410067e30596410067d30596410067c305964101e7f105964101e7e105964101e7d105964101e7c1059641006df7558e41006de7558e410065e7558e41006dd7558e410065d7558e41006dc7558e41166df7458e41166de7458e41006dd7458e41166dc7458e41006df5458e41006de5458e41006dd5458e41006dc5458e41006df7258e41006de7258e41006dd7258e41006dc7258e41006df5258e41006de5258e41006dd5258e41006dc5258e4101edf7158e4101ede7158e4101edd7158e4101edc7158e4101edf5158e4101ede5158e4101edd5158e4101edc5158e4101edf4158e4101ede4158e41
  | 28 => 0x8242006fa3058242006f9305824203efb205824203ef8205824203dbe74d094203ebf64d094203dee74d094203eef64d094203faf64d09420bfae54d094259fad54d09425976f53d09425976d53d09420bfaf43d0942597ad43d0942004ff75d8542014fe75d8542004fd75d8542014fc75d8542004ff73d854200cfe73d8542004fd73d854200cfc73d85420067f53d85420067d53d8542006f651d8542006f551d8542006f631d8542006f531d8542024fe70d8542004fd70d854219d7e75985420057d7598542195de7398542005dd7398542006f7619854223ebf641854201ef66118542006f56118542004ff75d8142014fe75d8142004fd75d8142014fc75d8142006be54d8142006bd54d8142004ff73d814200cfe73d8142004fd73d814200cfc73d81420067f53d81420067d53d8142006bf43d8142006bd43d8142006ef42d81422b6be42d81422b6bc42d814201cfe71d8142004fd71d8142006fb60981420057f755814219d7c7558142005df7358142195dc7358142005f77158142005f47158142026fa6018142006f960181421867f74594420be7e74594421867d74594420be7c74594420067f73594420047f73594420067e73594420067d73594420047d73594420067c73594420be7f43594420067e43594420067d43594420be7c435944203e7f725944203e7e725944203e7d725944203e7c725944203e7f425944203e3f425944203e7e425944203e7d425944203e3d425944203e7c425944203e7f325944203e7e325944203e7d325944203e7c32594420067f71594420067e71594420067d71594420067c71594420be7f41594420be7c41594420067f31594420067e31594420067d31594420067c315944203e7f215944203e7e215944203e7d215944203e7c21594420067f70594420067e70594420067d70594420067c70594420be7f40594420be7c40594420067f30594420067e30594420067d30594420067c305944203e7f205944203e6f205944203e7e205944203e7d205944203e7c205944203def7650842006ef7650842004ef765084203f6e655084203f6d655084203def745084203faf74508420beee645084203fae64508420bfae545084258fad54508425876f53508425876d5350842005ef7050842004ff7558442014fe7558442004fd7558442014fc7558442004ff735844200cfe7358442004fd735844200cfc73584420067f53584420067d535844203ebf425844203ebd425844203ef771584420bef741584420bef44158442006f63158442006f5315844203ef7215844203ef42158442004ff7058442024fc705844203eef2058442004ff7558042014fe7558042004fd7558042014fc7558042004ff735804200cfe7358042004fd735804200cfc73580420067f53580420067d5358042004f
  | 29 => 0x40020000000001400100000000000000000c00700000000000000000400000000000008005000c00000180030000006000000100040030004005000000000000010004000002800000000000000002000c0050004001000c00a001400300080060000000000800000100000028001000400900180000004007000c0000000001000000500040010010000000000000040000004004000c00000080000008000000c0030000001000000100000000004000001c001000c000000c00000100180000002001000100000040000000000000200040000008002000000b00080000000001001c001000c000001400000040010000001000001600080000008001000c0010018000000000000080000000000000000600100000000000000000000300010010007001c0040000000000000000040000000000000000000040000018006000800500000020000005000c0020008000000000000080010034001001000000080050024001000000400080080000001000000000000000004000000c000000c0000014000000c0000008001000000100080000000003000000000000030018000000800000100010000005000c000000400000040010010003001000000080011b57e75987420057d7598742236be649874218dde7398742005dd73987420bef7619874201ef461987420bef46158742004ff7558742014fe7558742004fd7558742014fc755874203cfc7458742004ff735874200cfe7358742004fd735874200cfc73587420067f53587420067d53587420bef741587420bef44158742004ff7058742024fc70587420befb6098342026f860983420057f75583421b57c75583420bef86058342004ff75583420067f75583420047f7558342014fe7558342004fd7558342014fc75583420067c75583420147c755834203cfc7458342006be5458342006bd5458342004ff735834200cfe7358342004fd735834200cfc73583420067f53583420067d5358342006bf4358342006bd43583422aebe42583422aebc4258342004ff715834201cfc71583420befb40583420bef8405834203ded76d0a420beed76d0a4203fae74d0a420bfae54d0a425afad54d0a425a76f53d0a425a76d53d0a42004ff7558642014fe7558642004fd7558642014fc7558642004ff735864200cfe7358642004fd735864200cfc73586420067f53586420067d535864203ebf425864203ebd425864203ef77158642006f63158642006f5315864203ef7215864203ef42158642004ff7058642024fc7058642004ff7558242014fe7558242004fd7558242014fc7558242004ff735824200cfe7358242004fd735824200cfc73582420067f53582420067d5358242006ef425824203eec4258242004ff715824201cfc715824203efb7058242006fb5058242006f8505
  | 30 => 0x4000800000000030008000000000300000000008001000400000080020004002000000100040000008000000c000000c0010004000000400400040020000002000000d0000000000000100000040000000000c00100080000014009000000e0004000001400200100020004000000400000000030000001000000400000020004003000c0000004002000400000000020000000000c0030004005000000300040010000002001c001000800100080010010000000c00300040000008002001000000000050004000001000000000000008002000c0000000000000c0020000001000000000100000004000000400600000000000000000000400000050050002000c0070000001000400b0004002000800000000000000000000c0010008001000400000140030050009000000000000000004001000800700000040010001000400600300000004000000000300000000008000000000000040030000001001000000000010004001000000300080000000001001800000040040004009000c00000200000000002000800000000010004002001000400000000000000000000000000040018002001c000000000200000000004003001000200040000004000001c0010010003000c0030024003000c00000040000000000000400900140000014000000400000000000004003000000100000010014000000c0000010000000c006000800000000000008007000c006000400000000010000000000800300080010004000002000000100000000002000800300080000008005000400000000050004005000400100000000000000000c0040000001001000f00040020004001001000000200000000006002c000001000000000020010004001c005002000000180010000000000000600100000000003000c001000c00e00080000000000000400100280040000007000000100080050000000000000000040000010001000c001000c0010004000000400100000010000002001c000000400000000010010001000800200080020018001000400000180040004001000c00800140000004001000000400040000008001001c0030004000000c0040000012000400300000020000000002c0020000005000c00400080010000001000000000080010000000000c003000c002000000100000000000000000c00100140040014000000000000280010000001000000a00000000000002000000b0000001000000100000080000001000000100000030000000000c003000400100100000000001000c001000400000180010004008000400000100000000003000000400040000020007000c00000040000004003000000000000010000000000c0000010000002c0010004000000000000080000008000000400100080000008000000
  | 31 => 0x100100000000002001400100040000000002000400000000000010002000800100000060008000000800100040000000000001400000000010000000000c0010008000000400000000050018000000800700040050000000000c004000000200000010000004000000000000020010000000400900040020008001002c00000040000000003001400100100000000000000000100000030008008000c00600000020008003000400000040020008001000800000140000008000000000000080000000005000c0090008001000c001000000000000020010000000000700080000000001000000200140020000002000c0010008000000001100000010000002000800000000000004009000400200000000008000000000000000000018000000400000040010010002000c00a00000010004000001c00900100020000000000c000000c009000400000140010004000000000100000000008000000400300040040000001000400100080000000000000000000000010000003000400300180000008001000000600000010000004000000300040020000000002000c0000002000400400000000000000000000000000040000000000c000000800300000040018002000c00200000020004000001c00b0000002000800000080040004000000400000000140000001000000200000000000000001c00100000020000002000000700140010000001000000100180020000002000000200080000004007000000100000010008002000400000000000004000000800000040010004000000c0000008000000c009001c0020008003000000000000000004000001c0000010000000000000100090000002000800000080000024000000c00b00000030004002000c0010004002000400000040000000000000000400000000000000000800000040050000000002000100000030000000000c0020010000000400200100020000000001c0050020004000000000140000004004000800000000050000001000400600000070000001000800300080000000002000000000000000000000000000600000010018004001400000080010000000000800000000010000004000800100100000004003000400100040040010001000400a000c00700000020000001000400000000000000007000000100080020000003001000000100010038000000000c0020001000c00000000050000001000400000100050004008000400000040000000000000000000000060004000000000400080000000001001800b0000004001c00a00000010000000000800200000000000001000000000040010000000001c001000400000440000008000000c00100040000004004000000200000000000001001c00200000010004001000000100040030010001000000
  | 32 => 0x88e9d4c2d980005b2027a15b0e2e809948c8caa1660000000000000092e9a8a7b1a70a39da55000015500a100000000000473237000018da02d00002868000259000000000000000000000000000007440000f14000000000000000000000000262200000008a000000000000000000000016f40b7247a0000000296000088c90706d60d684f3061a36aa302577228830826c888682ea48b09f0559915088980000000b5057d17a20000d5c0df8000017800000010ec630a00a00000000000ab400020de7ce0000000263a35915aa7698000000000000000000fc8000000000000000000000000000000000000008de0c780001b9c806800000000004a0800000000000000000000000000000007dba464000000043f1a0688a0000000147253a8000000000036c8eb6000000000013e284c8a785b1000000000000000000000000000000002720d8e617800000007b2176217418614e49471b1e56400009c6800085723108e4000000000002e800000000000631181200000002ec0000000019e00016c28f5916a0f69086000000000000008138000245000000023da0000000000000003a000000001c608b8702000215600022bc979926685e9b400d8000000000000000fa264d000000011ea00000000001f400002332000000053000000a585c200001601a600002930000000079c6bb000035580002d6000000011020c0000049b80001310000000000000000007d380001b40000000000000000002e50000196857a0001e7642e845e3a22402860a1a4466a0021110b7a57880003d1878400000000008000001c00100000020000001000c000000800300000000000000000000b0000001000000700040010004003000800000000010004001000800a0004005000000000040000010002000000100000060004000000000200080020000001000800000040000010000000800b000400000040000004004001400200200030000000000800800000020010000000000000100020000000000000500300000010002002000400040010018000000000100040000008004000800000040030014000001c0020000006001c00f00040020000000000000900080050004005001c00000080010008001001400100040020014003000000800040000000004000800000000030018001001c0030008002000400200000000000004000001000000000000000000400000000000000000001800000100000020003000400100000070000003000c0050000001000000000000030004000000c001000c00100080110000001000c00000040010000001000000400000030000007000c0000010000000400000080000000000000000200000020004002000400300000080000002000c006000800000040030018000000000200080010008001000c00100
  | 33 => 0x2680000000000738000000000006b32258000000096a93e80001b4c00000e46078000000213a5d894607f41bb0000000057322164d008680000000000000000022c492900000000324000000000000000001c1600001b481c019a80d1fc21cd11dc000000000010f60000000000000000000007d50000000000068d88b000000008b7a2d86c300000001d7c4f6007a1bc800000000000000ab674da2d600000000a91a0873286f67c6073200000008a08000000161003288181a3a5f65170000000000000002720000000000000000002ae00000000000000000020600000000001998684007623d1542201800000011bc6ba8ad249882f872b85660000fc0787000000000000000c3200013f00000f8800000000001f92847000000000000301d64000000014f00e0434000000000000000bf600000006cf177e96891b800002605531a2a0f4000000000005070f9e134800000000000002142000185821c000000006f42689bbc5ca03e82f0800000026088e9073071f0b7c75800005d70000000120a031000024480007a980003db1f744b18000000000057f80000010000000000000025a40000000000227c64a16a400006ae00023842a9000000000008851c6a852883043880000000e1c0000000803a59051600000000000000072438000000000000483800000025680000b10000000000000000000000382800099e9c1c2290000342a45a90a000000000001f1800000000009410000000000035094560000000000061c0001ef000025ea15f800000011726440000381a50870c800066e00004460f6e65f0000693800015700000000000000190e000000000000000000ed827510240001b762500e400ac066c000000000022c600012ec3ed9bfc42d14c8290000065080006350d0e7f0047001d000000000fa00027240000000177028e00027261f3a16e35c928400000008fc1d8660da07e000000000006ac0000b220000000000000022e80000000000334800000000000001a140000000000000000004ec0001672000000000000009cf800046d8f1c4749524011a4aa2e000005a50000000000043e984000000000001f6c0002576092800000000003b81e5c0001d5e19323ac0de937a75c8cea4aa00000000c6400000000000000000181a00000000000000000000000010aa000000079e000000000000000000895000096801e46e000001cb045800026d800000007931992000000000000000000000000000000010ae0001cd000002fe000000000000000000f427b89a2855d1bd088810920c1000000000000001f267c5a4940001e32000117000000002a71d4a39e9b360000d8a0000c1e99a1ffe0000000000000000001ec0001a3843d15b20000000000143800000007a9000000000000000000000000000002008c7800067e23
  | 34 => 0x191000015d8d124ad068c000000000000000000000118939c5dd90fe439800027a1ecc27b800090b9df00001dcc67717e28d4a0a000026c40461fb01da972c48d800000000003c105bc0001c6c16117f2982a61000017b20001d54000051417c8000000000000015ba00024d200025ba2420000507947e4e693903861efc00000000000000000000000021b200000000001852000000091080008200000000153e64b800030100000000de00001a7e00005e667025060000000450a626926232600005a25b5028200008b2000000065300000000000000000087b800000014d676b800007b807c21b8000000000013da57e6730d360e722c80000000748000035199e83a69a1c0001de68cf9a9e2da245884f253a160989a3170c7e8c801fc2eb80885d52380000001636526a4000196a00025de84d0000000000000011245e5186e0000bd61d311c6336a0f6526891a5a480000000000073800000020d024d800073f0000000000005e000000009b8000000000006ce1b196164b805e431a933e00000009ac000000019da47083de00000007bd80003649cc01b600d027880003a78000000000000000000001f9c27d1dc000000000000000000222c000000000024c897080005e4000000000007e9800000000000000000000150a000000024a970c3700e928a4079434f00009d980200000000000259249022fe29e8a0a0002354775800003a9a4400005cc000000065600007c51a1696f800000027445d7a4c6000000000007ca0001ade9cc80344ff1a628a6031e000000000020a638d0000000000080780000000000000120000020720000000000000000004fe00000000000000000089600008e680aa2fc26b800000002d86eb80004b48c2878200965820000766000000000000000000000000000000009c600000000000238000053500008ec80000000000000000089d8ad0000000000000007af0362489185c73d0000000126808826a6865800000014060001c7e00021484761e3459713d29ac966889e00003ba0000000000000026d4000000000000001c680000e88ba4528800042f0000002000000000006e29d78043000000009327b0268a00000b69278000255177c00000003580a9e7178000373987c6ab000000000006b58d347bb0c001cf116c8870092000133c2d5930a0001f2400000000000cf40000d6e407a6f82048f82000119c6bf0832033170a47d80007860a461ac1716000153648b80000000ed2000000000000000000000297000000013da2fe9a1a7088ec40000be60000000000000046d0000000000076a1168000000004904cc955a2b0000000000020b860c25bc5e00c6c15617b897523f80001d0c8771d5c3ae80009230000000000000003ac6061eb68538000228a17200024ce90d800000000004be80000
  | 35 => 0x135261380000d28410000001e58c80001e600000000078726000024f171e804162a7c7800000007286d812745ef800000000001ec05a0360a57c05e9f200c38000000000000022dc0648c6e86e9e101300710404a1c828a8802055800052814968840000000081c000000019a800028e800046e86da00000000001b9409709c09510fee1d19e7c03da4f036a06e872f85d6688237a7e88a8630b800012a154a9000000758868a0000cf29a200009981bda50a800004800000000696000000000000000000000000000053b00006391cf86c40000515000000002800001ea090714cc00019149c70a1000000000000000000163630e00001a9a02e7ed1e5a85423920000c980000a50203a408402192400000008d600000000000000015e00007605ce05b88279730000239e0000aca6e080000000000000000000000000000400000000093e198e000000045326a000026bc00006a41941ab243680004a6041401680004560000000000004b0000000000000008b61658174000000024800000001c8811c94760f90c4e0000ca87a710900001b680000000987000080600000001a0a000000000000000001ab404f800000000000000000000219800000006cc0c14000000000000000000000000000020100000000c402e12340000063000022f46e18a6050f000000000006b48000000011e00000000000000000013a00001e05fd95448ad800016e80009710dac58620cc817092c57b13326d40d761172624861000000000000000000055000000000007d30f28098862c000098665c211a0611a5202e80000000e6e45b964e78b27100001f940000a8a00022747e19aa6597800026d80000000128000102e4e9000033109740000f9c19f9b485d100005f30278713184800004320000bb60230000000000014b8000000000040b24d848c8000062032e021928c36c217e32324b2000000035f08223988000000233c0908d620db9f821280000416264e70d80008d4258476b00006b8000029086822c000003d5110065a23ee0000000000000067200000002570000000000000002dc00008b9000031090b247000000001df653b8000000258e00025f86bc8000000000000000000002482626000007a00000000000000000000000008ce90a47bc927e6c494f600003189d500008a68c9425e9d2a87989f21fb00ce5a703064010c10045076c0001c3056480000000000000000091a904425b800000000000000000000000000015c400000000001cf2000000086f87e200002fc110926a000000000000000001db497680000001c8c1241a6004e08b42510072313217033399060000000000042c0000000000001c00000000000000906a0e03be85f400010109930e5a58480007519a0e18a80001ba80000000
  | 36 => 0x2138000000000011f0f5e0000000000004c38b00000d9063400000000000000000000017f9336000006a4b41f9a000192c48086600000000000000000008ca00008b800000008ab958a45e80009be80007da084a000130600000002e580000000dea00019ca14880007d9908a87c000000000000000ec2000020e00000000000000244000000000000002086000000000000006348000000071c00000000000ca000000000000000000000000000000001d0417a0122000000000001169d0000000000007508000385a02477a97202db254e23a80000000000722833c279800000003aa95700000000000000223c000000004d800070280006fb95c20000000911000049b0c500002054505000000015562be8a822ae000000000004f780008e98000568809000000008bd862462b9e8600000001b880005a3800000000005d90aa25aa8fc69ae800057e0fa87a40000000000000015549700000319800000000a654e80000001c3a000000080180005600000000000051180000000000000243e00018aa0000000000113a0000000000000000000006d709fc00000002c580002b1800000000000001f0e000000000000000b20fd482e800063c000000004284781ff6000049a0000000000000080d9cee0000000487800000007740a600003948000000000000000004ee1b84000008038f12f076203582dd00002120000000000000011449aa12a628083a858c085e0501988000107c78084fc0de18f40000000479800080100006a80000000000000013e400006c8000000093d93120001732000000000015700000dba18e94c600011ca68893a0000014c00001fa87e94080d0255200000000000000433259c8498000000000000000003ff24227c096ca0000df29729fb844c9bdc126000018d92c49ad0c9a54682a800000000000000000000071b800000000000fb000000000008be800000000000000000172000000000001de800015c8bfe000019400000001eaa3568eb9a5e0000000000067894980000000000000000087000000b800000000e3600019c600000c85a80000000220200006ec88e000026500003a9253800000000001cd80000bd8510082a008800010211a000003ce1c3800062a05fa00018fc91809cc0000000000000000016e42cf000000000008c20000000268016998083cd14d01519a3a92b8cf600000000000000381000091e00006c0000082f896a0000900000000000002ac00492cc3b2800000008dc5ae160a20813c098380004dc83f64108406000080c00000007468000000015a22126667ae80004a58000000004200008244d30018000179200000003c0004a56996be0001ba298697d2000000000026e800000007ab259800000008c3064a00000004589c4e0000000000000078e000000000000000000
  | 37 => 0xe00000000001c822f71d7000000002b1000069e0000000000000011140000000000142000000007a2000000000000001a88000226000019fe0000000389882c35ea21852488501c500000000000000000004700003ab8000273800070e272825a051082b98a600000000000dd200024501701fe25a415bc7f215d24f1047690100003f580000001c9a0000f9a3c280006e600006c58f448688b5c014000021504865f18d1461d00008ef806400000000000f3a11326aa4afa1041540000000258a3d7173a0000000762958c0f80000000036c000000000013548268000000000000002ca33286406381c10000000000012043380a880000000000000083498620000000716a6e4000000040e80004d59af053d0000000000088f800031f1f8a0000cbe00000000000c967c69d9c348000000017082a31fba3679b2a000000000000002f4130280f9f3a6258000000000004f1ba68aa00000000dbe0001a984f20000000054c00000006f58000000000000000000001ca23e00dfc16a800070b9a0200018b00001c7018b800086ba2aa7e9000095e8000000156879790b844da1fc00000000000000000045636700006fb00000000ece742000000019b60c99ed24c410685ee9cb800018282d080006301b5674f0b0400008c20000ee600014d804182d679f80000001c945038c2679d1582218800060b21a096b9b7e0002484000024400000006da8f643f480000000d4000000009c780000001f3c8cb12ba1810f2c000187a000269a5f70000902a0e41528000000000000010065da1f7e47c000064000000ef8000000179600000001fc0f6079b00000000c56000002600003c018000000001c1400021769061d9000024e600000005a094ae0000098000000033180002218000000000000002227768000000007e5f680000000fae67da5640000000000000000023e85e28c120000000000000026584b24e280002748000000000089880002629ab80000000021000000008a0731800047684b40000db60b980000000cf839900000001b72832998c9b58a0c400a4406fd1cde2340fb2000000000000005a28000000000000009340001d7a00000007f7894888000006339bce5eb914e36410c200014621e48a2246f934a000073e00000000b79d2e6d49bc400023766fc14bc891972449c8000000030c94b800036580000000000408000000000000000000667a5fc22b00002198c520001a6636e0000000000000019ac000224812c14be05f9c420d1a46e000000000000000000ca600020d800000000d480000001f423fd8000000000000017de79c921c00018e681a80001b791667a6983c000000000002761dc8000125a63811818ca7119f845c6800009922ca90c814a00006fa6908000000000003c000083f905a352000000006920000000000
  | 38 => 0x9800001f880000c1c0000ad8000157a5a325fa6580cc2000000000021bc0000e7000002f0000125a2c9800000000003da1918000000018c8b7e00005400a3053000010dc7752722436000098d999a00000000000000000000051480001d78000000264607e1bc629c800094c16a6897000040f274c0810c160b8a266359800000000000e28000000000001b800000000000000b1c06f994400000003be000000000008d300004e1124c974915491f1954000000000024c28d380000001c74000000069a000062b105000026da0001a50000000000000000000000000000062c8000000000000007780001868181800000014000001dfe18403a4000051e000000000000006618b440000c8010980008a98da06fe00002581ad829b8a54037800048a80000000000000245e0001b2831780005c500b86b399387a799b05fe9a583d4000011001f680502346241b3a4321ed4000000093e8fde094000007d1f980000ea2000051c00023c44ed0000000000000000000000000000162e2a5918049e8314000000000007b400000145868000000226a000000078004743238000000000068c12300cb128a965a20666980006018000000000097380000000000000000000000000000000000088a00025fe000000000000000001daa00001d684d8b4c2ea037c00009e02252222000112e000000000000007cda38e0001f44397000000000001408000000020200015be000000000000000001a5c2860000000040a000000054c268c0001be41428da63f388c807480000000000000000000300008968000519977871e00000000000000000000016840000000000000000020aa0000fca4f50a200000d8c0000cba0000000000135803d174a58126e6893800044f1c96249045488389180000b48000016a837041855f01ae00000007aa80000001a922bc959c3da8a040000d304f18000000000000000000001fa000000004cb800049393246cb228c195000000000000000000000000000024ec000000000e24cc0000000000000000023622c099e40000a7e00000000af18ea000000000019e65ef2244000105c5bb8c4600014ba000219200024f497b99163fa262073716ce0510000000163441380000000ac03d02100981000000000c2210a09800012288e586ca2d917e800000004b7000000014f800018be8ff063e854800012e80000000e98928119039080001fb936802b80007668ea600020c6622a70200000000000000000000026690d283c0d587238b2a96780006fe8000990258078591342b7800048324c432b800000000000000000000000041225dc35d180a0000000598800034a0000000266a2819fc65660000000000089311d045280000000000000000089a000022400000770dfa3df1de22b70b1a00015160001b6687da0520f703e
  | 39 => 0x2480728000162000000e80000000000263209c2b90000000226c5b8103026c00006c6800000023440000d5000020640000000000055a0001ce200000000388000000000064c8e24610996c0000000000000000000000a716c60b4000000000000000000000021e5692058061973600013440000892000000067b0000000000000000007cc00004bf13e63129fe61b0906a32d01f033c00000001e700000b2c00001721a01c526ef80289bc155e57687d254ba4523b78a6c73127060000000860000024100fe0000cb8000000000010220002088686000000004ea2fd0d2a000172a000000000000000000000000009e2508000000000000004225228cd6985800093b8000000000045200006db81b6599000000000000cf8000000000000014e8000000000004da06380007cf800000021f40b9125200002560000000000000062710e40000000383885251c09589da106628f87625f3911c7ca0000823800000000008a29fce9a3800082280000000000000000000000000001cb66320000760000087583e60000000000000000024bc3d88e5400000002a6800082f13d0000054e12da2ee4880f10000212e0000938000242a1b9a47000016783ffa49a332068879a0cb601482740ca90963cf100c0001adc0af80000000000000131a00000006c6000000000002d000006bf800000000000f180000000000000000015a82329d79e1e635806c93f80001f080000000dd6619197478519966ff961c2ea80001ef908825d80005809b900000000000000007000003e3800000000001f2000000000004fb80000000000000000000000005ba000000020b46c18dbc000000032085da94d04ae68b8000983135000023225781d503a194fc03e01cc000265600000000000cbc52d19726fc800062d95628d80000000204a0001ec800000000000000000000000013ce00008f09b8000000008e81149936096800043504bc02f989400016f600000002e28000000000000024da533876e0000000473a6423528c725fb80000000cfc5f5a6d0082269274f9ae6000207c000000096e1930716273a752074a0001a6a3e400000001d6e503000000000000000ff2000102a76e920861698f8000000000000008d9271695c8e840002678000000064fa524495002400002e8000066408e800000020e60000a5a00000009b300000000000000000000010a6000144c0000000000000079b800000009a40000000000072000000008000000000000000000000000450000000000024161fa884c8b6a6762a98fe208d800054f000005700000001e84000000000000006d1000000000002ba0466133a70405091c800026484038fda3f081f2104894a16b863c0a21db800002a616a00008f0064e00000005e91e4a2e684be6431e8a7b58da405213bc130800000
  | 40 => 0x2c05ca00000004fd924200005703dc000010b80005b5a1160000382960800041e8000613000019f0000000000000000000000a9400000000000000000235a000183e461000070a0f6600000004c804d651790b0000035e7df00000000000000046c00013864ea9f480001dca00017ea15900000000a321e393988ce00000000000000000000016ea8a5000000000001058000000000000000000000000695000098526fc000029a87380000000000025000000019845ad00008dd00000000000000000000000000000dc80000efc8c60992000010473b000015b800000000007d7821270480000001e820000716000233073d800000015ca81d991c5f1145a01580005f28c9e4ac000000011d6000000056c049e0b0800014d250e00012bc0000f18000000007500000001948000091c5c411ee06723f600000006fd98047d680000001d7600000005881f469cd8be46468eac21d87400068dd80000000000048a24300002af924876388c648d07c0000023e28b8000000041c7ea800000000004be0000000000000000000000000532961e66f80002f19e62000000034f8b2e000038c00000000000000000000008713640000000237800000000000000000000000e52c80000000048000000024280000002146000000000000000001fae000272a34c80000000982874a65e0000000000086491b006250080005f4000091f800037b000000004c8000000035780004c215d6000000000000000000000000000000021c20002256595800000025a84d080009200da20000000000000054880000000c3e2160000268275a6ee05740001a5a00000000000f7243280001b9053e80e8000000000056b1ca01468394049817c5ed86721a180003aa80000000000346022a5cf03420000000000000069d8c92000065c00000000b18000000000000000003008000000000000006dc00016140f60b0c21c80000000000000000000018728181b8c17419d80001d248100ddc6b2a42c13180000dc87b60000f8432906b81ea089a2c80a760001f580000afc9c2000067c222a7dc946a000000000001aa000253255a90a2000000000000000000000000000054100003ba80000a418d095a80000001aae77c8000889119e42707f665000000000d9a62d0000000053a8fb00000e41eb01f80aa80000c541e91f8c565a0a495b8e44291000000000003f3000061f80006890ee480e05b2000000066a04e462f000000000005d3800000000002a400000000000000000041c80000001c9e00015a08ef0ecc00000000000cd80a800000000000000000000025d00001a0c00000000000000000000000013349a1800000000000001c180000000980000000000005c0a53e59f000000000005bc1b700000dc20900552155800000000000000000000000000000007ac80
  | 41 => 0x4b8000112c00000008578000000000000000007d49eda000214c5e68bc80978e7207200000001dbc83380009cb800033f873690922a087a1ff000027300000000000000000022d454a80005208000000143424ea108266193c3e9800001a164806300001e9a37e3bb23cc00004a600000003939b0e53c00000001fbe000231c000265a5e825b64ae1a268da800000012ac0000000443000000010986be94941ef14225d00000000000000002b80a88000000035662021b622223c83ec11aa384976c4e4a64a3c780007ed800000026c6000000037100000000000000000098c878a000261e3b687227ae1108000000038680000289d4e00000000001d2200000000000000000000000000008e5240e14300004c314a44ca8060000000049609ba0bb9626457000000000000000000000183800022127ef000000000002cd00004bd1baa06a1c687cd000000010f20002016000000000013f442512c217888d800000001a780000000000000198095095b600000000000a48000000000011602c6251420d80007d926647391d842ce0000000000004a8000746000000000005480000000207a9051b4671107500000000000072e68d00005fb1376000000000000006c0800000000004fa80000000000000000053780007a890787020c0e16925d81631548000000018598e800000008f5000000021580001ffa0000000485800000000004f58000734a5ec000000000000007c48ea000000000000e587fc816215f0bb8484800000000008f280005740a16000000000014b63c2000012002b20a482ec8a7a536789a69c4958000998856094f0512000000080a00006f609300001300000134876c8000637800001c00005e7a2cc0369a4034e80000000000000155a0000000106800000000005d9800090494fe6159106494000000011221b58e469580c68000000000000000000000000000007a880a19d800000021e23b20e784c98dcc3c311ac534a36c0000000867000000000000001f7800000005e0823834b84f42a026fe96307040cc128e000000000000000000000000000070f1bc01b11d5239d1ef4607190a0001b9666a800000000002850a70000055e1288000000000000013f21bf00000000000000266e00000001a5013200000000000fbe071238200fa1ac86a898e2de1a0094617f4804800003ba3ea9950af83e51f1c0000000188136274003126e792787e59b081169a4c0001fe80001d025f908005438e2000000000000000000000050b800047a00009af800000000000000ccc0001f5665900006c996ae89c8000034835083e91b25da84f20000ef4000000016da2e866922403bfa26e0000fb817d80000000000000192082c00004d7000063c8000132864275680002990b8c000046e0608000000103600000003df800095798889
  | 42 => 0x1c8026a800000000000000000000000000000000000000302800000024900d7000000019a200f1526000119600000003eb10804a400000cc80000000000085836a00000001c600000000000000000000000003a01f5c66ea1fe7be851800013a2790800000014880001be0000238c233216a5d6122284480000ec000000000005779ba0000026e0f300000000000000000000000000000000000000017b00006a5000085b0ff8000052891a00000c8062800000000001e3e52380000769bb6000148603500007c18aec00000000001d383cc01960001c0634e22528629b24000175290c111659d992a74488c400000000001e9400020f2000050e000000000023b66df0000000000038506ee20e800000020ea223000028e1b6200024b62358fe671009c44911178145911294b1a120960000000000000000000000c062260e5600023e400007e60918000899106e00000009521e9882c85fc00000008b80000000000000000000000c34000000020f80b0803132800000000c20000986023c11e800000007ac00006be5cd0010000166a000000000011984b88000000000084c1cda544000062380dc00000000002748000000033900009ba80002daa0c000000000560000000000000020220000b3a2170cc0000273c20e07420151aa20a787f80000de49a600000000000000000045480000001994000167e8dc80006cb9de81c7a066175000000006460000ab20d3800000000000001d66355000000025e26d9000000003f8000000075b15c0198a250000104a00000005a612f623000005a580001272084504860c54500001ad23e05ea0b7659615ea000206c0000000000162278f000087e19780000808796000090f00001b812c88c126b844a00002f2895c31d10160c2800006909ca00000001f68000000000000000000000cb27fb000062880003bd8612000000067f07a05d69ef80000fd800000000000000000000050c000000000000000000000000017480000000aee35300000000000000000000024ea000000000000002611dc800017aa171a1200000000000164c1b01ea88b99f626aa2204530800088791865b02296451800083b00000001dee9792486815800056d1ae2000000008614da5d300000000000947a5400000f5a0000000000000044100002c48000000000000000008b407e8223800098f18ee00000000000dca000104c00000009b7203200000004dd00000000000000033a16724764a8000000005e0000000000000000001a7a00020682f50000247800000000008b883442fa1c72000000000000009bb8b9c2b68000000000000000008f980007479a7429a8c7061d9624527817074d0e6a33408ee5bb06b60000000070a0ac00022f8411892e00000007511ed80000000000000069f00000000
  | 43 => 0x2c0000227000000000000000000000000000006cc800039f800067e800000000002180000000202c442800012900000000000000000085a00001211d1687a9a903a5224252e08741a89aaa3b5808e64080001231ad000000000000b868d980002f300000001e12000149800016d02c78d780f4938810f80000000000000000000024e8843a5548ac97700000000000000000019e01809834000000000017fe1d480000000000000000046c00000000000000000000012e8000213e2dc92f20000000000000084a00001da0000000088261c00000000000579000000011a80001c90756000000000000000bac4eea41000000000000000000207885e070a000000000000008071e487b382b40fe87fc35f96d22d824ac00024a68c58a004c60000000000085822f2000087e3778000000000000006f80eb8000000000000007dc52b069000000008e6a62c0001abc00018cc6ba00004179a3e576254c0000000718a4be733800036619d603b0000000178c65895f6897a2d20001eee0001dde00007120000000000000000001308c4800000015380dc004072e80000000fc800000000000580000000055609a841d0ace32b00007e000006e49f3292d061e0b300000000a8e99f1e24248800000000000000000000167a46b87ba3740000847800000000000001f2222f8000000210200003d671700000000edc000028a13e000000000007558000000000016485de00000000000000000010800000001fe80006670000059800000000007a38000346824e00000000000ef2000000000000000ad800060e8c3c00016da9408000000000000000004698a4e7980446462852051a000050e8cec000000038f80003030cee82d800000011f23b023b84a483b60029886000000000000004ce80000000000000000002c80000000000000000000000001511d92842978400022c082480001c9800000000000002578444000000020c460917728a88000000000000015188c5000000000000ec800000009d86e680000000000000220a7c000007a0123c3719fda47500006a01edc000000000021246d5000000026d20001bd400012384ec8000360097e0001cd4000000000021860001e3a50f960e3091d7430d800086780000000a0e0000000000039e94680000740000000212a4608000000000000004020001cea4e3805886d231a70800000000000771000000016e685880002cc08a88108000409800000000007daa2ba0698f4c00024f22a48000000000033980004c89aa472d01348641a042278ac24ad9666000000010c000000012ca939000000000000002516000000030c0caa951803200000008ba970400009ec0001e6600026f4188800000000008d193160000000000156c4638000000000035a90a0000000000000003dd8000000196e5ff0000
  | 44 => 0x1d82000000000008ce000249200010de88305080001bc80c70000167800000000009a41f08000000099424880e0000065d80000000000287000000000000000748478800000018780ff80000001a9c793a1c4000000098c102800000000000dee6370000000275814994907b98000000000000000000000000000000000014f200012186750bf073a00000000000000000000000002a10d709528f125c000004b9800000003c200013be69b095a00000000002420673800002b000086e00000000226000000000000000000f58000039a0001be266d0fc40000ba2000000000000008020000000000052100000000bb40001e309d49b3e0000000000210c7810f206280354123881425400000001c500000000678800000000003289bcc3fa80002fc89a6000000000009de53800000001a46149024c8f3a0c2000000044c00c6000000027709620000b8e30600000000fbc6d09018287a4dc53709021a81fe48f899d22baa3884ba8000000000000023aa4c70a4a0a180000002144000000096d10d64fea3d200015fc9d88000000177a58e000084b1210991223000008e45201f0a000085600000000000000383000000003a6020a1062fe00006fa8000877800069c8322000000000008fe832000000000000001a82000238698a058e2101712000000000011a200000003fc1d0e3cd8e82446875a000019864480006ed1aba00000000ce173e7c10fd067080000001014721000000011640000000000000000012b20000f7a000230e00000007b806f07441f9000001e2848a43400000006f480000c08c8600019228d20f928a9000046500000000b527ca800000017c0000000055e0000000000098aa28400000007719aee6570000000000000020fc000131e0000000312000000000007918fdc000000000000000000000000000000000008f0995e512193a00025b2859011200000000001a4a5b304fa5ed12ce00015e6040084600000000000bd202f07fe97a00007de83b81f10000000000085f0000000000000007de000000051b8e3a000000000000000000000255806600000002bf800052989523b1800062911fc77f1c0e00026c054300007d800000000e3298d18928cd89d6000000010d8000000120692e00007690b085c19c2600000004eb8000000166e37d9ac25ada5f071e8f1600001b018215889a893ca000147853880000000000000000000010ac5c99e2a00000000000000000000000000000001c76000000000019f28ae00000000000000000078d80006af800031800008c180007f1238a5fe000000000000000000000000043aa0447b921d0000206252c039255d8b4641801d8975800000004820000000000000025c002c6a3093e724a65c15e0e7c0000000000235c00000000000000000082e00024060000000000
  | 45 => 0x9bc8af800000024e239a00005d58dda12a867038c0000302000000000000000000000000000007e4000139e00008ae10e000019e964600000009d296de2848000000000081184e25109d9e5409dfa2c1800000000000468000000043400000000001966000203c00007f42168000712a44e506000000000000000000000000000000000000000000000000020a20000000000000013a000000025f24558bee06f0000000235e00016860000e02000000000000004b580004daa08287c80003f9042a00000001e787f200012e491280000000e087708000000000000022b40000000000000000000001c180002a60000000000056a1c560828000777000046900000000000000000000000000001a8636180000000000000047e000000000000000000000000000000015600e1800036b8e3800000000001e6a00014fa31d8000000000000000000001ada00000000000000000000000007821c2108e000000000000007008f486b180006d399048e800002c524d4000015200017884bb962c0000f3e63f96501a7000000012aa944800000000007fa8b0e65400f200021100001a32000000089e877e00000009c30464000000000012140001fca26b000000000006c713a600016d8000000000002ce958800061980003d289060000000000166c450000000000001f30000000000000005b0715000000000002978000000122687b23f409f0000000000000000000ed000000000000000000000000000000002e9995a59c00000000a7c00000000000cd400000000001d9627aa7461f580000000000101000040293949289af41f40000000000042685689ab800023e8000000000054498027b1197a3490e5e9a1232e00000007079ab68ee800080c0420912112a0000000430094e000245c3168000938000000000004000000000129e0000af40000c2c0001d40000140a00000000000000155092895b08e291d269410300006f785ee0001d06000234a0002048000110e0000000351062600000009ad800000000006cd169e6c8a5c60000000415036800000002bd8000000000000012fe00016540001c049a080000001082000000000014740000000000000000004920000000873208c8ea00000001b4a96985be0d69f9e00000009480dd4000156e000000000000000000aa00001df450b000000000002719c24519077c00000000000000042879600000003bc000002805ea00000007000e8e000066600026ec2f880000000000000150800020a80000000039963e99c1fac5c600004c512d40000ae20001b8806402660000e8a3c88be005da3a290e0000621000000000000001eea58a11f400000003789ed0000107e20f1af88e6040e956000072f26063d380a804096886b2163a00026de316140405405008501d947902700768800
  | 46 => 0x96680003de00006ec80000000bc072b00000000000000000000000000001a560000000000000000000000000000000108c6150000000000000000006dd0000000000000000002c900000002522000070c16d000000024a8000000000000000000bce00003d472a00007d2800043e00000001e2e8bb2574000000070a8648000151e000000087283ba00004681dd9cfa000186a00000000000000000003605923dc00000000e6099c00016ba20790a8125000000000006d780000000cdc00006d200000002708000937800019a043a00026e2000065e557137854719465ab091604b9fd8000084400007646ea18c68d080aa3ac8000703270e26200008698ee238a80000001cfe000000077823f2600016c7f50000000000000000004d69fb256b980e80806a820d0228541843c044027e34303c44380a52195a37c53980007830c9c9948448462087c5b88cfa0000000479000000027560000ae698b838e509800059d000048680003220000000000002280000000000000075848f8000000000000000007631e5228a087877b249c00011fa00000005090df4000059800000002d78bbc0002090000000000001ac000079067113dc000074e79e97480002234000000000011c400000002cf89b20000000000219a00000008db8000000000000000007f817d400000009150000000000057c800000000001e200000d993463998000000000014180fc000229208c25862641ca61eb80000001ad4730968000000007429370236a3c629d129a82500006ce1db6000060e3e3000000000002b2000081781e63fb1e6440f80008a716000000e8c000250c13c23d075a000000000000b4946c062873a000218e20a00009188000000144461b0db4000000000000009c49e0e0000000000075447f80000000000000000083d04880000f2400015641a1000074c97863798000791000000000000000000000000023e0aba398054800000009c5000000000003410000000050427f9f7083a117c6b025f429881460000aaa37e0000000184486226ce000232829a1dd00000000000047800016a20001a2c0aa80009228f3256393ac3e287d40001fa800000002d3800000004d823f256600000000001eae000000000000001f619de72190845bc929c0000336000115e251a5886c2800000000001e6821a00000000f880000001926000000000000008b08b6e000002e8c2825400008aa43b897834400002d51270000112000021180000b9e5bf800000013e009b144a6e380002350000000000000000000000000000000000000000000000000000000000000000000000000052a01b27498000000000028c00000000000875266c000000000002c400000004db88169c800001ee03bc0000acc9199e50000081000016400000b0a0000e48000000062e095e06
  | 47 => 0xce00000001ffc2898a360001ee854c80005db8000913000090e9dd8113800050d991e000000031100003930fa0000000000000000000000581930400c000083b9b5a75a98600000b6245d1e203eaa4ca00000003a5800000004e66ac000000000004e000004b789663c380000000000000058a000000000021382ac00005e3800063600000000000347000000000005f9800000024d0000000069917d88b39dbe55c800000000001af000043188ec72c80000ae800000007383409b6c000125e0bd03104c3800000008d2000000049d804400000007470ed03ee800025c80002ee9ff81d5995227e000000021941e0274200000000000bfc419252a59115fa000000000000000001f765fc000000017e02d29c34000160c0001ede863190874ea5ac7e3800077495c856104de60b80000001a4800015862999c3e6c1000000000002769eb400000008e70000000144e00000000000000000000000022f00001cf000012da00008bc0f2a0960001fee7bf8f263bb8000345800000006b286a0000000000000019ee00000006b114320000aae0000000384000000000000000000000000066090340000eb00000000356800000008f24158a084b6000000018823d580002e0800045f96bc6118000000000073580005d8272c00000000000000996000000018f66f2800040689e460a8000000000024384dc732241e98f9fdc85509fa000044a4fe0000000000012b00002fa80000000d84000059a0830000000009c6de800000021da0000000000000000000004df0000000198a000000092380009258000550000000000004ec0000915a2867cb04e028b261294018ba0000ed400000000b6919200003745ec12a2596826800015c60000000000000099d105244795ee3a7052c017159e6a580000000000739a40c6f08000000000074a00008780000000000048e800075f98320001e8c0001be80000c220000000000000099f800045680000001ca400000000000000000204c2530002845000000010ce00000000001bac0000000000000000000003d48eb818280008350d4e9d926c2000000094a0000000000000000000000532000000000000000001e9657c0224944081a00003f00000b925bf0000000000058f029400011ec0000000000181479597a626fa6ac029072a3ad0e9052a96a81589f1000000000000000000000000001a000000003e900002b50a247fd077056518ec2201ba47c31ccc32296b00000c902b807863c08000553a3fe4fb000025b18100000f9622980000000abc0000000000000000011de00000009ce1062000215a57a026a00009d091185944f095ce000046a0000000000106c0000000000185000000000fa800000000000001be6000269600000003c1800000000000000000000000000000003210000000000000000
  | 48 => 0xa8400011380000ce8935979c00000000001c6630a929400013609d385904ed802a63e8000000194a39b0bde1710000000022c000109e0000000000000000000000000000973000081b96f816b000000022ac1d98b3600000009d400000000000000136c7b0970e1ae80000f2082654a1b202d681682ca101c67419f40000a56035854265f969a34b00000001e2200017467af800066f1fd200000005ac80000c5800000000000000000194a1e4449a76049f00000689d140001f503ca8000000000076c21d800017c80000424782827062780000000000013913e00012c00000e503e612468ed0bbe2ec966031e800031893960001fd6000000051ea0e200000006128c3a8f78e220000000410000000000009cd089c5cb8ebc14e26f2000118c0000000000000000000000000000085000000000004a1800045d800000000000000334942869a094837634992a43489e1a000000091c995638a1a1e3e180000001eca608000050593fe50a0000000000088b82f28ec0bec4970000814000059483840000000000000000000002f68000000000008400008719a6e06e80000000dfe59080008da0000000000096c000000015d47f31b142cc800030685f0000000028f0000000000000025c8000099e0001c2c74b000040c80005929c6000004ee5dd0d880001bba14d8e4a00000000000000000000000005f8000135e6a380004ea00008cd0000000000000000003418000001a1b03aa000000000008f6000005b80001d718265d400004a00ff40c687a268f20d60001cb0000000043c1df89098f2e000000054b1c1a00017ac5311af6795137e4928d081960000000000000000000001de4043a2085e60000514232493f180c14a9dce000000000000000000b8883e15b8000000000018e2000141019b80005be99900001e929d7224a05399ea000269e00016dc000000000025943ed000078a000006e078c0000000499171c0be88f600015461b511f800006740000000000063842f89b41b3087a00000004d98000000086a4e0988c4e30a3433880000000000000000043a000076810760000000000000000015525f09f2e000223656682f64981ae400000000000000000000000000000000000000000000000003dd00002e603fc00000000001a9a5400ad600009260001c9c3c6800000000000d21a7021b25e00000bc48a38d521351d3000000000000000000000000000000000000000000051f00002ab0b905c880005d0800000002d493009f63afa27e000181699c8000000000066800006538af0712000038780006de00000000fe000000000d3032834000008368000000000016183f455f8de84a2141a66c80000000000000000000000001851822000000000001de00000000000000000132c37c0000000097c7818000000000000000003
  | 49 => 0x9809caa54d000035b000000026f6000255a000039600020744cc05ce81680009b280000360cb00000d1e4ce19ae4d380004ab83880000700000000071906aa0000000000000042d84d010780000000cde00023fa52703a01bf903807f90c43fe9
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xab9800c964040018beeb3aac6082e29761e7558c105b72b884eab1820b6e55109d563040018bf0ebaac6082df17dc57558c105be2eb8aeab1820b8c5f705d563041718bae0baac6082e395c417558c105c72a882eab1820b6a5e851d563040014bd0bba2c608002976177458c1001d6b40ee8b182005ad581dd163040014bd0a3a2c608002976147458c100070faa4a8b182000a5e85dc963040014bb0bb92c608003175d67258c100052f428e4b182000a5d851c963040018baea392c608002a7a107258c100054ec20e4b182003ad6811c9630400b5ab02392c608012b6a007258c1002d6cc00e4b1820008de87d4963040011bb0fa92c608002a7a105258c100054ec20a4b182000e2f5495262041714db0b29cc40800393d4e539881000727c1aa731020bae4f7354e6204175c98e6a9cc4082df93cc553988105bf2698aa731020b8e4f3054e6204171c9a60a9cc4082da9ba1453988100053742c873102000a6d8590e62040075cd0321cc408002b9606439881000537428873102000a6d8510e62040018bee6a9ac408007171cd53588100247743ea4b102000ace83d49620400159b07a92c4080123b21d525881000557420a4b102000aad8414962040091dd0f992c4080029ba17325881000536c2e64b102000e4d538c962040091d90e992c4080029ba14325881000536c2864b102000aae840c9620400155b08192c4080039354c325881001d7340864b102004aea800c9620400159d073aac408002b360e755881000557420eab102000aad841d562040075c902ba2c4080029ba14745881000536c28e8b102000e2f5495162040014dd0b39ac4080029b616735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881001d73408e6b102000ae5811cd62040095d50039ac408002ba60073588105b735086a6b1020b9e6910d4d62041714db0b29ac40800393d4e535881000727c1aa6b102000e4f7354d6204001c98e6a9ac4082df93cc553588105bf2698aa6b1020b8e4f3054d6204171c9a60a9ac4082e39a84153588105bf34882a6b1020b6a6e8514d62040014dd0b21ac4080029b616435881001d7340c86b102000ae58190d62040014dd0a21ac4080029b614435881002477c3ac5a1020048bf87592420400917909bb284080123b20b765081001c7a40aeca102003c747159542040091790eb22840800f351c563508100247643ac4a102000c7565dc5420400196ac9b8a84080033558f715081000672b16e2a10200287e855d8420400917b08bb084080123b60976108100043fc32ea2102017c3e645d442040018bcc6ba8840801f1b98975108100043fc3aca210200087d87594420400187ceab2084080030f5d564108100062f3aac62102000c5d7558c42040018dceab1084080031b5d56210810
  | 1 => 0xaea32640880038e19464881100043fc2aec902200287c855d9204400117f08bb2408805e2f21176481100046fc1aec90220018dc835d9204407dd5041b2240880f72d1c464481100247b436e29022000cb464dc520440838f0edb2a40880ff2e1db64481101ee5c3b0c89022000e38651912044001cd0ca3124088003aad90624811000575436849022000b698510920440017c3022124088002dc6147148110005e8c18e29022003ce876c8520440093d10e90a408800f3a1d92148110005d4422429022003de071485204400187ee93a2ca082db1dc4373594105b63a886e6b2820b887d879cd65040018bee739aca0800317e0d73594105c63b882e6b2820b8c75105cd650416d0fd0e39aca080021fa1e43594100043ec3c86b282003a768190d65040014eb0321aca080021fa1c43594100043ec3886b282000a5e83dc965040014bb07b92ca080028fa1072594100051ec20e4b28200087e87cc965040010fb0f992ca08003175ce32594100043f43864b28200087d870c9650400147d08192ca080028f61032594100062eb9864b282003a76810c965040014eb02192ca080129ea0032594100053cc0064b2820048bc845d6640402f87eebaa4c8080122f21173990100051f42c873202000a3d8590e640400756d0321cc8080122f21172990100be1fbaceb3202000a3e859ce640400147b0b39cc80800eada0673990100055ac0ce732020b8a3d8594e6404001c3ea729cc80800387e0d53990105bf0f98aa732020b7e1d3154e6404171c3e60a9cc8082e3874c153990105b51f428a73202000a9e83d4a640400153b07a94c80805e2fa1c52990100045ec38a53202000a3e85cca640400147b0b994c8080038754e32990100bc5f4386532020008bd870ca640400147d0a194c8080028f61432990100070ea98653202003ab6810ca640400156b02194c808012aea0032990100055cc006532020048be87d51640400187eebaa2c80800b0f9d654590100245e43aa8b2020048be8790d640400147d0b21ac8080028f616435901001d5b40c86b2020048bc8750d640400147d0a21ac8080028f61443590100061fbaceab202000a3e859cd640400147b0b39ac80800eada0673590100055ac0ce6b202000a3e851cd640400147b0a39ac8082e28f61653590100070fa9ca6b202000e1f8354d640416fc3e62a9ac8082df874c553590105c70f982a6b2020b8e1d3054d640416d47d0a29ac80800ead20572590100051f428e4b202000a3d851c9640400153d07a92c808002a760f52590100045f438a4b2020008bd87149640400147d0b992c8080028f61732590100070ea9c64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000e1d530c9640400756d02192c808002ad60432590100255d40064b202000
  | 2 => 0x464989100061eba8c9312200287e86dd562440810f90dbaac4880021fa1f65589100062e39ecab12200087e8719562440014bb0632ac488003171cc65589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f19474589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100043ec1eeab1220008bf845d5624402f17908baac48800237e0d755891000c6e41aeab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f85dcd62440018b90bb9ac4880021fe1573589100143e42ae6b1220008bf845cd624402f17908b9ac4880023be0973589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200287c87d4d624400187ee9a9ac4880030f1d353589100062fb9ea6b122001c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b122000c3c7454d62440018bee6a9ac488007171cd53589100066639ee4b122000cb474dc56244001968e918ac488007351ce315891000c7a43a62b122000cb4744c562440039a8e698ac4880039554d31589100052ec18ca31220bbc797019462440011df0eb10c488002b320d62189100043fc2aeda12200287c855db424400f17908bb684880021fe1576909100143e42aed212203ecba70d9242440071f10cb8484880031e19570909100143f42eeca12200087d85dd942440010ff0abb2848800a1f21576509100046fc1aeca1220018dc835d942440011ef02bb2848805e2f210765091003c5f43ec8a12200287c859d842440010ff0abb0848800a1f21576109100043e432ea2122017c3c645d442440010ff0fb2884880021f61f65109100061f3aec82122000c3d75d9042440091e90cb88848800e3e21970109101f65c386c8a0a203c8be86dd1214400187ecbba242880030f19774485101f45f430e890a2000c3f651d12144001878ca3a2428816a2fa1f64485101f45e43ec890a205b8be87191214402f1790e32242880021fe1576501100143e42aeca02203e8bf845d940441770fd0dbaa80880021fa1f655011020c3e43ecaa022000c3f75d914044001878ebb2280880ff2d1c764501100061fba8c8a022000c3c7519140441770f90cbae40881061fe1f65c81100043ec3ecb902203f8be869d3204400187ecb3a640880030f19674c81101ec5e432e99022000c3f655d32044001878caba640880fe2fe1f64c81100045ec3ec99022000c3e75d93204400187aebb26408805e2fe1c64c81100045ec38c99022000c3e75193204400187
  | 3 => 0x63222001c5e7354c64440018bae6a98c8880028fa1643191100051ec2c863222000ab58190c64440039a8e6988c8880039554d31191105e74ba1a6232220bce94434c4644400187cedb28c8880028f60f65191100045ec3cca32220008bf87594644400153d06328c888002a760c65191100061f3b0ca3222000b1d831946444001c3d06328c8880028f60c65191100070ec18ca3222000a1d831946444001c6b02328c8880022f61e63191100051f42cc63222000a3d8598c644400117f0eb18c8880028fe1563191100051e42ac63222000aaf8258c644400155904b18c8880028fa1463191100051ec28c63222000a3e86d4c64440014790da98c8880030f9db53191100051f432a63222000a3c8654c644400187ceca98c8880038798d53191100070eb1aa63222000e346594464440795690ca88c8880038dd9631191100071a32c62322203cab4864c46444001c6eca988c8880038d19531191100074bb1a623222000e94634c46444001e2aa6988c88805f0fdd675191100051f42ce63222000a3d859cc644407b56d03398c888002ad60673191100051ec2ca63222000e1f5394c644407b56d03298c888002ad60653191100070fc1aa63222000e1e7354c6444001c3ae6a98c8880028fa1453191101ed5b408a63222000ab58114c644400153d07a90c888002a760f52191101ed5b40ea43222000ab581d48644407957501290c888002ae60252191100bc5f438a432220008bd87148644400147d0b990c8880028f61732191101ed5b40e643222000ab581cc86444001c3aa7190c88805e2fa1c32191100045ec38643222000a3e850c8644400147b0a190c8880038754c32191101ed5b408643222000ab5810c8644407957500190c888002ae60032191100bc5f43ea232220008bd87d44644402f17d0f988c8880022f61f31191100051f42e623222000a3d85cc46444001c3aa7988c888002ad60e31191100071ba9c623222000e35538c46444001c3aa6988c8880f7a50c531191101ed5bc1a62322203de97834c46444179d2ee6988c8882f3a51cd31191100071ba9a623222000e96534c46444001c6aa6988c888003a554d31191100070aa9a623222000e97324c46444001d2a64988c8880028fe1570191100051e42ae03222000a3e85cc0644400147b0b980c8880038754f30191101ed5b40e603222000ab581cc06444001d2a63980c8880038754d30191100074a98a603222000a3f8544064440014790a880c8880029760c65d891000e2f39aa7b122000c5d7354f6244001c9aa6196c488002b960432d891000574c0065b122001cd4734c76244001caaa698ec488003b1cc931d89100052ec18cb3122000c3f659d26244001878cb3a4c4880030fd9574989100061e32ae93122000c3e75d92624400187aebb24c4880030f9d
  | 4 => 0x54400147b08196ca8800317dcc32d951020d3b40865b2a2000a75810cb65440814f500196ca880029e60032d95102043f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100062fb9e63b2a2000c5f734c76544083ca86298eca881061fa1f30d95100043ec3e61b2a2000c5f73cc365440018bee6986ca880029760c65d91100061ebaea9b222000ab581d536444005878eb2a6c88800a2fe1d54d911000e2f39aa7b222000c5d7354f644400147d0b21ec8880028f61643d911000c5fc3a87b222000a3e8510f644400147b0a21ec8880028f60f65d91100054f418cbb222000a9d83197644400163b0632ec88800387a0c65d91100051ec18cbb222000e1d83197644400143b0632ec8880038d60465d91100051f42cc7b222000a3d8598f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100051f436a7b222000a3c86d4f644400147d0ca9ec8880028f21953d91100070f31aa7b222000e1d6354f6444001c68cb28ec8880faad21951d91101f55a43263b222000e94634c76444001e2aa698ec8880030f5d475d91100054f418ebb222000a9d831d7644407f56d023aec8880faad60475d91100051f42ce7b222000a3d859cf644400147d0a39ec8880028f61473d91101fd5b408e7b22203eab5811cf6444001c3ea729ec88800387e0d53d91100070f39aa7b222000e1d7354f644400147d0b396c8880028f61672d91101fd5cc00e5b222000a9e83d4b644400153b07a96c8880022fa1c52d91100045ec38a5b222000a3e85ccb644400147b0b996c8880038754e32d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100070ea9865b22203fab6810cb644400156b02196c8880faaea0032d91100055cc0065b22203e8be87d47644400117b0fa8ec8880fa2fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec8880038754f31d91100070ea9a63b22203fe94314c7644400147d0b986c8880028f61730d91100070ea9e61b222000e1d534c3644402f878c8bacc8880029760c65991100061f3aec93222000c3d75d9264440010ff06bacc88800a1fe1f53991100043ec3ea7322200087f8754e64440010fb0ea9cc8880063de1d319911000e6b39a633222000e55534c664440010fd0fb2ac8880021fa1c65591100052ec18cab22200087d83dd5644400117f08baac8880030fdd774591100061e3aee8b22200087f855cd64440050f90ab9ac8880022fe11735911000477c12e6b2220078ec825cd64440010fd0fa9ac88800a1f21f53591100043f43aa6b22200087c8754d64440014bb06328c8880022fe1d64191100051fc2ac83222000a3c85590644402f17908ba8c88805f0fdd754191100bc5e422e
  | 5 => 0xf32bc8074584201e656900e8b0840008bf845cd610802f17908b9ac21001e3b20973584200061fba6a6b084000c3c74d4d610800187ee8a9ac2100030f1d1535842000e2f39aa6b084000c5d7354d61080091e90ea8ac2100032d1d231584200247a43a62b084000cb4744c561080039a8e698ac2100039554d31584201e45fc3ac9a084003c76615d641080079acc2b9c82100031d5d561904200bd5a422c32084000cd573586410807d17d0f3228210007359cd31993100072aa9a6332620008ef825cd64c400f1d904b9ac9880022fe117558b100bc5e422eab162046cb6311d162c400117f08b9ac58805e2f2117358b100061fba6a6b162000c3c74d4d62c400187ee8a9ac5880030f1d15358b100062fb9aa6b162001c5c7354d62c4001968e898ac588007351cd3158b100072aa9a62b1620468bf8759342c408f17f08bb2858811e2fa1e6450b1001c5e43ac8a1620178bc845d842c400187ec8ba8858805f0f1917510b101f45fc3ac9a06203c8be8799140c400155908b164188002ab21162483100245e422e5324200287e87dd564840010fb07baac9081fa1fa1c75592100161e3aca8b2420048bc8755164840010ff0ab9ac90800a1f21573592100043f43ea6b24200287c87d4d64840010fd0ea9ac9080021f21d53592100245e43a86b242000c5f7354d62840038b8e6a9ac5080123b21d5258a1000726a9c64b1420048ec874c962840010ff0abb6850800a1f21576d0a1003c5e422eda1420048ef8758b428408917b0f32485080122fe1d6490a1003c5ec26eca14200087f855d942840050f90abb2850800237e0d7650a1000c6e41aeca142017c3e645d4428400f8dcc4ba885081162fe1d6410a100061ebaac82142000c6d75588428407917f0eb2683080fa2fa1e64506102d657310e890c2000cac7458921840095d50da124108002da6144248210024f443a429042000ba88448520840010fd0db9eca8800a1fe1f63d95100062eb9ec7b2a200087d8798f654400147d0931eca880028f61263d95100062fb9cc7b2a200087f8758f654400147f08b1eca880028f21163d95100062fb9ac7b2a2000a6f8258f65440014d904b1eca880261f61c63d95100062eb98c7b2a2040a74864c76544001aaee698eca880039518d31d95100061eba0e9b2a200087d879cf65440018bee739eca8800317e0d73d95100043f438e7b2a2000c5d731cf65440834ed0239eca881029d60473d95100043f43c87b2a200087d8790f65440834ed0321eca880029d60643d95100043f43887b2a200087d8710f654400147d09396ca880028f61272d95100052fc1ae5b2a2000a5c835cb65440814f500396ca881069e60072d95100043f43e65b2a200087d87ccb65440018bee7196ca880021fa1c32d95100043ec3865b2a2000a3e840cb6
  | 6 => 0x62eb9aa732240048bc845ca64480010ff0ab84c89000a1f215709912003c5e422e1322400087d83dd564480011bf06baac8900063720d75591200047bc0aeab2240038f4815d56448005878eb2a2c8903032d1c654591200145e43aa8b2240bfcb47155164480018beebb9ac890003171d773591200062fc2ee6b224000c5c85dcd64480010ff0ab9ac89000a1f21573591200047bc0ae6b2240038f4815cd64480018beea39ac890003171d473591200043f43ea6b22400287c87d4d64480018bee7a9ac890007171cf53591205ce3a38ea6b22400087e8754d64480010f90ea9ac89000317dcd535912000e2e39aa6b2240b7c747154d6448003938e7a1ac8902fb2d1c7435912000c5e43a86b224001c9c7350d644817b968e2a1ac8900122f61372591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf71591200063ba9ee2b224000c7553dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89001e2f61370591200045fc3ac83224000ab48159064480ab17b0fb2684900127ae1d70d09202b45f438c8a12400096f835d442480012db06ba884900035ae017510920006b4402ea2124007c6f605d4424800fad6c0ba884900035a8c17510920006b4982ea21240048ed87d904248001a5aeb3208490156ea602641092000477c3ac821240009af875904248001a5aeab208490002e920564109202b5d5c02c8212400087f855d361480050f90aba6c29000237e0d74d852000c6e41ae9b0a4000c5f7354f61480038b8e6a9ec29000f3598573185200047bc3ac230a4000ab48458461480019aae6b08c29000e2fa1276d052001d5a40ac9a0a4000b2d8510a4148001b5084b8482900022fa1e645052001c5e43ac8a0a4003ab48159141480093d501b9282900026ba1f42505200043fc2aec20a400287c855d841480011bf06bb082900063720d76105200045ec3ec820a4003ce4615c8414800165b0a21082900036a109701052001e7830ae020a40009ae849db21480093d5013a6429016f6a08374485202365a308e890a4000cb474d85214808f958edba242900123ba1a7448520004d7424e890a40049ea809d1214808d958ec3a242900034bd4c744852000696a98e890a4000da6311d12148001b4a623a2429016b2bd8074485202d6d5b00e890a4000daa301d12148001b52603a24290003691d36148520006d23a0c290a4000bc5831852148001b50e9b8242900036add070485202245ec3ec9a0240049ad8710b404800165b0a21680900021fe1576501200143e42aeca0240008df835d940480031b906bb280901162fa1c645012022cd743884a024000b2d8510940480091790eaa2c8100122f21d43590200045fc22eab0840178bc845d5610802f96b023a2c21
  | 7 => 0xac8259140c800195ac9b9281900122f21175992200245e422e73244000a3e8590e648800147b0b21cc910002ada0643992200055ac0c873244017c3f759d6648800147d0b39cc9100028f61673992200055b40ce73244000ab5819ce648816dc5e41a9cc9102db8b48353992205c51ec2ca73244000e1f5394e6488001c3f06a9cc91030b878c953992206170e192a732440b8e1f3054e6488171c3a60a9cc9102e38bc8153992205c716902a732440b6a3e8514e648800153d07a94c910002a760f52992200051f42e653244000a3d85cca648800147d0b38cc9100028f61671992200054f41ce33244000a9d839c6648802f17d0fa8cc9100022f61f51992200054f418a33244000a9d83146648802f17d0f98cc9100022f61f31992200051f42e633244000a3d85cc66488001c3aa798cc9100038754d319922000557c12633244056aac824c6648800147d0a18cc9100028f61431992200074a9886332440048f8805d5648800917d0faa2c9100030fdd754592200245e43aa8b2440048be8790d648800147d0b21ac9100028f61643592200055b40c86b244000ab58190d64880091790ea1ac9100028fa1443592200051ec2886b244000c3f759d5648800157700baac910012ae20175592200051f42ce6b244000a3d859cd648800156d0339ac910002ad60673592200255d404e6b244000ab9809cd648800147d0a39ac9100028f61473592205c51ec2ca6b244000e1f5394d6488001c3f06a9ac910307878c9535922060f0e192a6b2440b8e1f3054d6488171c3a60a9ac9102da8fa1453592200051fc2ae4b244000a3c855c9648800153f06b92c910002a720d72592200055bc0ae4b244000ab4815c9648800153d07a92c910002a760f52592200051f42e64b244000a3d85cc9648800147d0b38ac9100028f61671592200054f41ce2b244000a9d839c564880095750138ac9100022fa1f51592200045ec3ea2b244000a9e83145648800153b0628ac910012aea0051592200055cc00a2b2440008be87cc5648800117b0f98ac9100028fa1731592200051ec2e62b244000e1d53cc56488001c3aa698ac9100028fa1431592200051ec2862b244000e95310c564880095750018ac910002ae60031592200be5d322e1a144000cb964dc142880038bce6a9ac310003175cd53586200247a43aa2b0c40048f4874c561880039a8e698ac3100039554d31586200061f3acc920c4000c3d75992418800193ce732483100030f9d564906200061ebaac920c4000c9e73592418800193cc8b9c83100032759173906200065cb22e120c4017cba645c0418800117b0dba243100022f618744862023c5f43cc890c40468bc8759121880091db05baec89001e3e60375d912002476c16e7b2240b6c6d72d4f64481718dae4a9ec890007179cd53991200
  | 8 => 0x4b9ac9902db1b1cb53593200062fb9aa6b264001c5c7354d64c81718d8e4a9ac99001e2fa1e43593200051f42c86b264000a3d8590d64c800156d0321ac990002ad606435932003c5e43a86b264000a3e8510d64c800147b0a21ac9900030fdd675593200054f41ceab264000a9d839d564c800f55d053aac990002ab60a75593200055b40ceab264000ab5819d564c800155f04baac99001eab20975593200051f42ce6b264000a3d859cd64c800f55d0539ac990002ab60a73593200055b40ce6b264000ab5819cd64c800155f04b9ac99001eab20973593200051f428e6b264000a3d851cd64c800f55d05a9ac990002ab60b535932061f17416a6b264000e2d82d4d64c8187c58e5a9ac9902ea8f61653593200070fa9ca6b264000e1f8354d64c8001c3ee6a9ac990003871cd53593205d716392a6b2640bae1e3254d64c8175c3864a9ac99030e8fa1453593200051f42ce2b264000a3d859c564c800153d0738ac990002a760e715932003d57414e2b26405bcac729c564c800f55904b8ac99016b2b1c871593200045f43ea2b2640008bd87d4564c800153d0628ac990002a760c515932003d57410a2b264000aad8214564c800117d0f98ac9900022f61f31593200051f42e62b264000a3d85cc564c8001c3aa798ac9900038754d31593200051f42862b264000a3d850c564c800f55d0418ac990002ab60831593200074a98862b264044cac72dc164c800147f0ab82c9900028f21570593200054fc1ae0b264000a9c835c164c8089958e4b82c990002ade0570593200055a40ae0b264000a3e85cc164c800147b0b982c9900038754f30593200070ea9a60b264007aad845db42c80091df0eb26859001eabe1d64d0b2003e57c3ac9a164000e2f5359342c8001c5aa6b26859000a1fa1774587200043ec2ee8b0e4000c5f7354d61c80038b8e6a9ac39001e3d21d315872000e6a39a62b0e4000e55534c561c80091d904bb683900032b5db42d07200143f42aed20e400087f865d641c80010ff0eb2c83900021f61d65907200062f39acb20e4000c3e7599241c800187aeb3248390003279ce64907200061f3aac920e4000c3d7559241c800193ce6b2483900faab20964907200062f32ae720e4000c5d655ce41c800193cc8b9c839000327591739072000656b22e520e40048ec825d941c800195ac9b92839016e6ba1f425072003e37392ca20e403caac8259041c80018dacab90839005f2b99172107202d4d7c30e890e405a9ad861d121c80b5a5cca3a2439016b4b594744872000697a98e890e4000d2d531d121c8001b4c623a24390003694c4744872002556412c9a0640049ac845cb40c802f95cc8b9681900021f61b75503200043e43acaa064000c3f7599140c8001878eb32281900030fdd564503200061e3aac8a064004a
  | 9 => 0x65085400062f39eca10a807ec7a70d94215000187ecb3a042a00030f19674085400061fb2ae810a8000c3c655d021500018becab9842a000317195730854001e6a30ae610a8000cb574d8421500019aae7b0842a00031ed9570085400063c32ae010a8000cf3615c021500fd8f4edb2e80a01fb8ed9365d01400062fb9aa6b108001c5c7354d62100091d90ea92c4200039354e32588400247643a64b108000c3f53dd9421000187aa7bb284200023be09735844003c76412e6b088001c5e7354d61100018bae6a9ac22016e2fa1f42584401ec5e43a84b0880048f48754561100091e90e98ac220007351cd31584400072aa9a62b08803dd94415ce411000187ea6bb482200030f54d76904402dc5fc32e5208805bcae625ca411000117f0cb90822016b2b98972104402b45fc32e990880478bf845d9211002f958e8b12422000e2f611760844001c7cc02ec1088000c7875dd940100018f6a7bb280200031e54f76500400063dbb6eaa008000c3f749d165c80bf4df04ba2cb9001e9b20974597205d43ec3ce6b2e4000c5f739cd65c800f4dd0539acb903169b60a73597200062fc1ae6b2e40bac5e325cd65c81758b864b9acb9030e1fa1c73597200062eb98e6b2e400087e8790d65c80010fb0f21acb900029da0643597200053ac0c86b2e400087e8710d65c80010fb0e21acb900028fa1371597200051ec26e2b2e4007a6e829c565c80b34db0538acb9000297a0c71597200052ec18e2b2e400087e87cc565c80010fb0f98acb900028fa1331597200051ec2662b2e4000c5d73cc565c80018bae698acb900021fa1c31597200043ec3862b2e4000e55310c565c81894df04b82cb900021fa1f30597200043ec3e60b2e4000c5d73cc165c80018bae6982cb9001e2f21175993200be1fbaea932640078bc845ce64c80038bce6a9cc990003175cd53993200051f42c873264000a3d8590e64c800156d0321cc990002ad60643993200be1fbaceb3264000a3e859ce64c800147b0b39cc990002ada0673993200055ac0ce732640baa3d8594e64c8001c3ea729cc99000387e0d53993200070f39aa73264000e1d7354e64c8175c3c64a9cc9902eb870c9539932061d1f428a73264000a3e859c664c800147b0b38cc990002a7a0e71993200054ec1ce332640178be87d4664c800117b0fa8cc990002a7a0c51993200054ec18a332640178be87cc664c800117b0f98cc9900028fa1731993200051ec2e633264000e1d53cc664c8001c3aa698cc9900028fa1431993200051ec28633264000e95310c664c800147f0ab84c9900028f21570993200051f42e613264000a3d85cc264c8001c3aa7984c9900038754d309932002476412eab2640078be87d5164c800187eebaa2c99001eaba0b54593200161f3aca8b2640078bc8755164c80091d9
  | 10 => 0xb2a8000a5f835cb65500014b906b96caa00021fa1f32d95400043ec3e65b2a8000c5f738cb65500010fd0e196caa00021f61c32d95400051f42065b2a8000a3d840cb65500018bee6196caa00029da0432d95400053ac0865b2a807ea7a800cb65500014f300196caa000297a0e71d95400052ec1ce3b2a8000a3f845c7655003747908b8ecaa01d68fa1071d95403f51ec20e3b2a800087e87cc765500010fb0f98ecaa00028fa1331d95400051ec2663b2a8000c5f73cc765500018bee698ecaa00021fa1c31d95400043ec3863b2a8000e55310c765500c547d09b86caa00021fa1f30d95400043ec3e61b2a8000c5f73cc365500018bee6986caa031b0f5d065d89402ac5ec3ca9b128001c5e7354f62500018bae6a9ec4a01562f61f43d89400043f43ecab128000c5c73d9562500010fd0e32ac4a0003171cc65589400062fb2ee6b128000c5c65dcd62500018eecbb8ac4a00031d19771589400063bb28e2b128000c74651c5625007f96ec838ac4a00023be1d62189400063c32ae12128055da8425c242500fd87cedb2c84a00038bd9762909401e45e432e3212800287c859d842500610f90cba884a00021fe1f65109400dc3ec3eca2128000cae765084250001c5ecaa1084a00030f19676109400061fc2cec2128000c3c859d8425000187ea73b084a00030f54e761094022e57414ec2128045caf209d842500f32790cba884a00024fe0d75109400049ec1aea2128055c3f625d442500ab87ac4ba884a00030f18575109400be1fb02ea2128017d3b605d442500aba5e40ba884a00024fe1f65109400061f3b6ca21280009af87588425000195cecb1084a00038bd956210940005d5c02c421280468bc865c442500031ef0e98ec2a0007359cd31d85400072aa9a63b0a8000c5e73d9661500018bce632cc2a000317d9573985400062e32ae730a8003cd4615ce61500019aae7b0cc2a000a1fa1b75585400043f43ecab0a800087e87195615018d87ae8328c2a00023de1d61185400061e32ceda0a8000c3f539db415000187aa73b682a00ff2d8c676d05400065a98ceda0a8000c3e76d9741500ab17b0fb1682a031a1f21975905400043ec3ecb20a8000c5e73d9641500018becab9c82a000317195739054001e6a30ae720a8000cd573d8641500fd878edb2a82a011a2fa1f62505400071bb28c2a0a80048bd849db21500010ff0abb642a000a1f21576c85400046fc1aed90a80018dc835db21500010ff0abb442a000a1f21576885401fc5f434e910a800287e85dd921500010fb0bbb242a005e2f21076485400061fb2ee890a8000c3c65dd1215000187eca3a242a00030f19474485400143e42cec10a80038bc849d821500091f1013b042a00021fe1576085400143e42aec10a800087c865d421500010ff0fb2842a00021f61f
  | 11 => 0x90001c9ee6a9ac520003931cd5358a405c727982a6b1480b8e4d3054d62900014dd0b21ac5200029b6164358a400057340c86b148000ae58190d62900095d50121ac520002ba6024358a400053742886b148000a6d8510d629000155f08b8ac5200029ba147158a4000536c28e2b148000aad841c5629000159d0638ac520002b360c7158a4002575400e2b148000aae84d45629000155b09a8ac520002b3a0c5158a4000566c18a2b148004aea8014562900015d30028ac5200029ba173158a4000536c2e62b148000aae84cc5629000155b0998ac5200039354f3158a4000726a9a62b148000a6e850c562900014db0a18ac520003b14c43158a400257540062b148000ae9800c5629000147f0abb6852001f3a9897090a4000674b16e0a148000dab72dc142900ab87ac8ba8852001f1b9897510a40006373aac42148000c6d7558842900038bce6a9ac320003175cd53586401fc5f43e84b0c805a8bc8750961900091e90ea8ac3200123d21d315864000e6a39a62b0c8000e55534c561900078ecc2bac832000f3598573906401feca20ae720c8000c6e7598a41900018daeb3148320003339ce629064000666b9cc520c8000c6e7558a41900018daeab148320003339cd629064000666b9ac520c8004cea7058a41900018eaeab0c8320003355cd619064000674b12e120c80008bf865ca41900b795cc4b94832016f2b61e62906402df1742cc520c805be2d8598a4190001c5ceb31483200038b5d662906400074739cc520c8000e8d7398a4190001c5ea731483200038b54e62906401f657b84c520c803ecad7098a41900b517f0cb90832016b2b98972106402d65743cc420c805acad8798841900b5c5d0b310832016b8b616621064000717a9cc420c8000e2d539884190001d4ce33108320003a98c662106400075298cc420c803ccaf70988419007995ae131083201562f61a74c864003e57314e990c8007cae625d321900b795cc5ba2432016b2b9887448640006563a2c490c8007c6e625d4219000f95cc53a0432001f2b989740864003e67312e610c8000c6e7558821900018daeab1043200032b9d1620864000656ba2c410c8000cce73588219000199ae6b1043200133a9c1620864003e75312e010c8000ce9625c021900010fd0db9ecaa000a1fe1f63d95400062eb9ec7b2a800087d8798f65500014ed0331ecaa00029d60663d95400043fc3ac7b2a801b87d8718f65500018bae631ecaa01fa8f21943d95400070e31a87b2a800087d879cf65500018bf06b9ecaa00021fa1c73d954063d1f420e7b2a807ea3d841cf65500018bae639ecaa01fa1fa1e43d95400043ec3c87b2a8000a768190f65500014eb0321ecaa00021fa1c43d95400dc3ec3887b2a8079a3e84dcb65500fd47b09b96caa006e8fa1272d95400051ec24e5
  | 12 => 0x8029ea1473580210053cc28e6b004200aba841cd60084015730839ac01081ebaa08735802100574c10e6b004203af2811cd60084015e30239ac01081ebaa0b535802100574c16a6b0042c3e6a82d4d6008401cd305a9ac010ae79ac8753580215cf3490ea6b0042b7a798594d6008401cb6a729ac01080396e0d53580210072d39aa6b004200e597354d6008575cb464a9ac010aeb960c953580215bf2d98aa6b0042b7e593154d600856fcd642a9ac010adf9a48553580215cd3d428a6b004200a7a8590d60084014f30b21ac01080ebca06435802100578c0c86b004200aeb8250d600840f5d104a1ac0108029ea1443580210053cc2886b0042568bc8755162d00018bee6a9ac5a0007171cd5358b402b45e43a86b1680478bf865c642d000127f06ba885a00024f60d7510b400be1fb12ea2168056c3d625d442d000187cc2ba885a015b4bc817510b401f45fc32e221680bccd7615ce61d00079a8c2b9cc3a02f365d05739874023c5fc3ac5a0e80568bc8758941d000917908bb643a00f62fe19748874000717aa4a931480c3a6f87d4e62901874db0fa9cc52030f8b9d35398a405b717a06a731480b6e2d40d4e6290001c9ea729cc520002abe115398a4000556422a731480baa6f8754e62901754db0ea9cc5200038be115398a4000716422a731480bae2e7454e6290001c9f06a9cc5202eb93dcd5398a405d72639aa731480b8e2f4054e6290171c5a80a9cc5202e393cc15398a405c726982a73148000a6e8590e62900014db0b21cc520002b9a064398a4000572c0c873148000a6e8510e62900014db0a21cc520002aba135198a4000556c26a33148000aaf84546629000155908a8cc520002b3a0c5198a4000566c18a33148000a6e85cc662900014db0b98cc520002aba133198a4000556c26633148000e4d53cc6629000155f0898cc520002ab2113198a4000726a9a633148000a6e850c662900014db0a18cc520003b14c43198a400062fb9aa6b148001c5c7354d629000159d07a92c520002b360f5258a400247643aa4b148000aad8414962900014dd0b992c5200029b6173258a4000726a9c64b1480048ec874c962900014dd0a192c5200029b6143258a4000556c2064b148000e4d530c962900015cd02192c520002b96043258a400257540064b148000ace839d5629000159b073aac520002aba107558a4000556c20eab148000a6f855d162900014d90aba2c520002b3e0d7458a400056641ae8b148000ae7815d162900015c902ba2c5200038bd525458a4000575c02a8b148004ae88055162900014dd0b39ac5200029b6167358a4000537428e6b148000a6d851cd629000155d0839ac520002ab6107358a4000573408e6b148000ae5811cd62900095d50039ac520002ba6007358a4000727a9ca6b148000e4f8354d62
  | 13 => 0x70fa9ca6b204200e1f8354d6408575c3c64a9ac810aeb870c953590215bf0f98aa6b2042b7e1d3154d640857347d0a29ac81081eaba0a70590210051fc2ae0b204200a3c855c1640840756902b82c8108022fa1c50590210045ec38a0b204200a9e83141640840153b06282c81081eaba08505902100556c10a0b204203ab681141640840156b02282c8108028fa1730590210051ec2e60b204200e1d53cc16408401c3aa6982c8108022fa1c30590210045ec3860b204200a3e850c1640840147b0a182c81081eaba08305902100556c1060b204203ab6810c1640840156b02182c81080317dd67558c2103d67414eab1842caacd829d5630856f4bb0f3aac610b0f93a0a7558c2100726c14eab1842b9e56219d56308587caa433aac61080317e1d7558c215d62f392eab1842bac5c725d5630856f8bee2baac610adf175c57558c215bf2b10aeab1842bae55215d563085734bd0a3aac61080297a177458c210052ec2ee8b184203ad681dd1630843f5ab03ba2c610b26b3e097458c2103d66412e8b184200a5e851d163084014bb0a3a2c61080eb5a075458c210056ac0ea8b184200e1f5495163084014bd0bb82c610802976177058c210062ebaee0b184200c5d755c1630859159f04b82c61081eb32097058c210052f428e0b184200a5d851c1630840153d08382c610802a76107058c2103d67410e0b18421facd821c163084075ad02382c61087eb56047058c210046f438a0b1842008dd87141630840153d08282c610802a76105058c2103d67410a0b184200acd8214163084075ad02282c610802b56045058c210071daa4a930042b8a798594e6008401cb6a729cc01080396e0d53980215c72d39aa730042b8e597354e6008575cb464a9cc010aeb960c953980215bf2d98aa730042b7e593154e600856d4f50a29cc0108029ea1643980210053cc2c873004203af28190e60084015e30321cc0108029ea1443980210053cc28873004201c5e7354d60084018bae6a9ac01080e3ea1f505802101c7c43aa0b004200aba84141600840157308282c010802b6a0c50580210056cc18a0b004207aea8214160084075e502282c01080e3ea1f30580210053d42e60b004200a7985cc16008401cb2a7982c01080e3e21d30580210072ca9a60b004207ae8824c160084014f50a182c0108029e61430580210055d42060b004200ab9840c1600840f5d504182c01080ebca0430580210055d420eab004200ab9841d560084015b5063aac010802b660c755802103d75410eab004200ae9821d560084075e5023aac010802bc604755802103d75416e8b004200a7b855d160084014f10aba2c01080ebc205745802101d7940ea8b004200af181d516008401c76a92a2c0108029ea1673580210053cc2ce6b004200aeb825cd600840f5d104b9ac010
  | 14 => 0x681cc0644840156b03980c890803a54c730191212d557414603224200aad828c06448401c3aa6980c890803a54c530191210bc5f4386032242008bd870c0644840147d0a180c8908028f61430191212d557410603224200aad820c0644848d56d02180c890802ad604301912123e5a38ec8a12425bcac72d9141484018bee6a9ec090807171cd53d812100e6a39a63b024200e55534c7604840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9c73191604840193ec9b9ac0908032719373581210047dc3ac03024200c3f749d1650856f0fb0f39aca1080317dce73594210062fc1ae6b2842bac5e325cd65085758b864b9aca10ae61fa1c73594210043f43c86b28420087d8790d65084074ed0321aca108029d60643594210043f43886b28420087d8710d650840147d08382ca108028f61070594210052f418e0b284200a5d831c1650840f4dd04382ca108829b608705942101d3b408e0b284220a75811c165084010fd0f982ca108021f61f30594210062eb9e60b284200c5d734c165084010fd0e182ca108021f61c30594210051f42060b284200a3d840c1650840f4dd04182ca108029b608305942101d3b40860b284200a75810c1650840717908bacc81085f0fdd7549902101c5e422e73204200a3e8590e640840147b0b21cc81080eada0643990210043fc2ae1320420287c855c2640840717908b84c81085f0fdd675990210051f42ce73204200a3d859ce640840756d0339cc810802ad60673990215bd1ec2ca73204200e1f5394e6408401c3f06a9cc810aeb878c953990215d70e192a732042b7e1f3154e640856fc3a62a9cc810ae68fa14539902103d57414e13204200a3f855c264084014790ab84c81085e2fa1c50990210045ec38a13204200a9e83142640840153b06284c81081eaba08509902100556c10a13204203ab681142640840156b02284c8108028fa1730990210051ec2e613204200e1d53cc26408401c3aa6984c81085e2fa1c30990210045ec38613204200a3e850c2640840147b0a184c81081eaba08309902100556c10613204203ab6810c2640840156b02184c81080e2fa1f54590210061fbaea8b204203ab681d51640840587ceb2a2c81080e2f21d545902103c76412e6b2042038be8790d640840147d0b21ac8108028f616435902101d5b40c86b2042038bc8750d640840147d0a21ac8108028f61443590210061fbaceab204203ab6819d5640840156b033aac8108028fa1673590210051ec2ce6b204203ab6819cd640840156b0339ac810802abe09735902103d56412e6b204200a3e851cd640840147b0a39ac81081eaba0b535902100556c16a6b2042c3e2e82d4d6408401c5b05a9ac810ade8f616535902100
  | 15 => 0xb996c89096e2fa1f51d91210045ec3ea3b22425b8be87cc7644840117b0f98ec8908028fa1731d91210051ec2e63b224200e1d53cc76448401c3aa698ec89091fa50c531d91210051f42ee1b224200a3d85dc3644848f55b04386c8908022fa1c50d91210045ec38a1b224200a9e83143644840153b06286c89096eaba0850d912100556c10a1b224247ab681143644840156b02286c8908028fa1730d91210051ec2e61b224200e1d53cc36448401c3aa6986c8908022fa1c30d91210045ec3861b224200a3e850c3644840147b0a186c89096eaba0830d912100556c1061b224247ab6810c3644840156b02186c890807179cd53991210062eb9aa732242018f7874c664484039ace698cc8908039554d31991210045fc22eab2242008bf845cd64484011df04b9ac89080317dcd535912100e2e39aa6b2242008bf87590644842f17908ba8c89085e2f21173191210051f42c863224200a3d8590c644840156b03218c890807351cd31191210072aa9a6232242bce97434c46448579d2886988c8908021fe1570191210143e42ae032242008bd87994644840153d07328c890802a760e65191210045fc3aca32242008bd8798c644840147d0b318c8908028f61663191210045fc3ac63224200a3e8518c644840147b0a318c8908030f9db53191210061f3b2a63224200e1f6354c6448401c38c6a98c89096aad21931191210074bb1a623224200e94634c46448401e2aa6988c89085f0fdd675191210051f42ce63224200a3d859cc644848d56d03398c890802ad60673191210051ec2ca63224200e1f5394c644848d56d03298c890802ad60653191210070fc1aa632242cbe1e3254c6448597c3864a98c8908028fa1453191212355b408a63224200ab58114c644840153d07a90c890802a760f52191212355b40ea43224200ab581d48644840147d0b990c8908028f61732191212355b40e643224200ab581cc8644842f17d0fa88c8908022f61f51191210bc5f43e6232242008bd87cc4644840147d0b988c8908028f61731191210070ea9e623224200ab5838c46448401c6ea7188c8908038d54e31191210070ea9a623224200aaf824c464484b555904988c89091ba50c531191212355bc1a623224246e97834c46448579d2ee6988c890af3a51cd31191210071ba9a623224200e96534c46448401c6aa6988c890803a554d31191210070aa9a623224200ea7824c46448401d4904988c890803a5cc931191210074a992623224200aad829c0644840147f0ab80c8908028f21570191212d557414a03224200aad82940644842f17d0e280c8908022f61c50191210054f418a03224200a9d8314064484b555d04280c890802ab60850191212355b408a03224200ab581140644840147d0b980c8908028f61730191210070ea9e603224246ab
  | 16 => 0x181412d45e43aa8b108200c5f7354d62104038b8e6a9ac42096a2f21d435884101c7643aa4b108200e2d545496210401c9aa7192c42080e3b21d325884100e6a39a62b108200e55534c56210401d2e8698ac420803b14c931588410061fa9aed2108200c3d535da421048f96c62bb484208032d4c576908410049fc1aea210820093d835d4421042f87ec4ba8842085f4b98975108412d61eb12ea2108217d2d625d442104b787cc2ba8842085f4d98575108410069b18aea2108200d35315d442104b5a5e40ba8842085f2d95376504410065aaa6eca088200c7753dd941104018eaa7bb2822080a1fa1f75580410043ec1eeab008200a5d831d56010405878eb2a2c0208f22f21d54580410043fc2ae6b00820287c855cd60104010fd0fa9ac02080a1f21f53580410043f43aa6b00820087c8754d60104038bce6a9ac020803175cd53580411e45e43a86b00823c8be87909601047957501212c0208022fa1c42580410051ec2884b00823caba8010960104039a8e698ac0208039554d31580410074ba1a62b008202c78759416010401c74a9282c02080e3e21d505804101c7c43a60b008200e59534c16010401da262982c020807179cd53993210062eb9aa7326420087f855c264c84050f90ab84c99081e2f21d54593210062fb9aa6b264201c5c7354d64c840f1790ea1ac99091e2fe1d64d07212345f43cc8a0e4200c5f7354d60c84038b8e6a9ac19081e3e21d30583210072ca9a60b064201cd6734c66488401caaa698cc91091a2fe1d64d0a2123c5f43cc8a14420287e87dd560884010fb07baac1108022fe1175582210bc5e422eab044200a5d831d5608840187eebba2c1108030f1d7745822100657416e8b044200cad82dd1608840187eea3a2c1108030f1d474582211ee5b188e8b04420087f855cd60884050f90ab9ac1108022fe1173582210bc5e422e6b04420087e87d4d60884050f90fa9ac1108030fdd353582210061e3a6a6b04420087e8754d60884010f90ea9ac1108030fdd153582210061e3a2a6b044201c5e7354d60884018bae6a9ac1108032d1d1315822100e6a39a62b044200e55534c5608840187aebaa6c89080a2fe1d54d91210051f42c87b224200a3d8590f644840317f0ea1ec8908028fa1443d91210051ec2887b224200a9e83997644840153b0732ec8908028fa1663d91210051ec2cc7b224200a3e8518f644840147b0a31ec89080387d8d53d91210070e31aa7b22425bab4864c76448401d28c698ec890803c554d31d91210061eba8ebb224200a3e859cf644840147b0b39ec8908028fa1473d91210051ec28e7b224247ab6811cf64484b756b0239ec89080387d4e53d91210070fc1aa7b2242cce1e3254f6448599c3864a9ec890802a7a0f52d91210054ec1ea5b224200a3e85ccb644840147b0
  | 17 => 0x2c820087e870c165904010fb0e182cb208028fa1030596410051ec2060b2c8200a6e820c165904014db04182cb2080e9da0430596410053ac0860b2c8200c5f759d5639059d53d093aac720802a76127558e4100567414eab1c8200acd829d5639056f4bb0f3aac72080387a127558e410070ec24eab1c8200e4e829d56390401c9b053aac720ae7951067558e410062fc3aeab1c82b7c5f715d5639056f8bae2baac720adf951057558e415cd2f428eab1c8200acf825d1639040159904ba2c720b36b5e057458e415ef4a20ae8b1c8203ad681d5163904015ab03aa2c72080387d525458e416074a20ca8b1c8200ad78155163904075a902aa2c720affa51055458e410052f42ee4b1c8200a5d85dc963904018baeb392c720802a7e117258e415454e422e4b1c8200a5e851c963904014bb0a392c720803175d47258e411654f420e4b1c8200a9d841c963904075ad02392c7208b2b56047258e410056d400e4b1c8200ad9801c963904011bd0fa92c7208023761f5258e410054f420a4b1c8200a9d8414963904014bd0bb82c720802976177058e410062ebaee0b1c8200c5d755c1639040153f08b82c72099aa72117058e410052f428e0b1c8200a5d851c1639045953d08382c720802a76107058e4100567410e0b1c8200acd821c163904075ad02382c7208b2b56047058e410046f438a0b1c82008dd87141639040153d08282c720802a76105058e4100567410a0b1c8200acd8214163904075ad02282c720802b56045058e412dc5f43ca8b148200c5f7354d62904038b8e6a9ac52096e2fa1f4358a410143f42ee0b14820087d85dc162904079ace2b1c852091fa51056390a410066ab1ae32148203c747159542904079a8e2b1a85208031d5977150a410066ab1ee2a14823087f865d442904018bcc6ba885208b61fe1d6510a410062f3aac62148200c5d7558c429048dd2882b188520aa64fe197510a410049ec32ea214820093f835d4429040127b06ba885208034798d7510a410068eb1aea214825bc3f625d442904b787ac4ba8852085f0f9857510a412de97902ea2148200e568558f4190401cab0ab1e832080f359d163d064101f4b3a2c7a0c823e8be879516090405878eb2a2c120807179cd53582410062eb9aa6b04823e8be87d0d609040117d0f212c1208faaea0242582411f45f43884b048200a3d85109609047d57500212c120807179cd53d89410062eb9aa7b128200aad840cb6250401c9aa6196c4a0802b960432d894100574c0065b12820087f855c362504050f90ab86c4a096f0fd91751894100477c3ac4312820287e859db42504010fb0b3b684a08028f61676d09410061f42ceda128200c3d859db425040187ea73b684a08030f54e76d094122c5e432e1a12823d8be86dc1425047d95ec9394c0a08023ee1d6
  | 18 => 0x80587ceb2a6c0a100317dcd53d814200e2e39aa7b0284448bd87d0f605088f96ec838ac0a10023ee1d601814261e1fa16e6b2884c3c3d42dcd65109878de41b9aca212ea1f61e73594420062fb9ce6b2884d3a3f845cd651082f47908b9aca210030fe1173594420061e422e6b288400c5f835cd651097587e84b9aca212eb0f50973594425d62f192e6b2884bac5c325cd65109758de40b9aca2130e1fa1c73594421843f43c86b28840087d8790d65108014ed0321aca210029d60643594420bd1f426e2b288430a3d84dc565109a547f08b8aca2105e8f21171594420052f418e2b288400a5d831c565108010fd0f98aca210021f61f31594420bd1f42662b288400a3d84cc565108018bae798aca210028fe1131594420bd1e42262b288400c5d734c565108014df0498aca2101e9b20931594420043f43862b28840087d870c56510801caa6218aca2105e8fa1270594423c51ec24e0b288407a6e829c165109a34db05382ca2105e8fa1070594421851ec20e0b288400a5e831c165108014bb06382ca2101e9ba08705944218536c10e0b288400a76811c165108014eb02382ca210021fa1f30594420043ec3e60b288400c5d73cc1651082f47d09182ca210028f612305944203d3741460b288400a6d828c165108018bae6982ca210021fa1c30594420043ec3860b288417a3e840c1651080147b08182ca2101e9ba08305944200536c1060b288400a76810c165108014eb02182ca2105f2b953765084200656aa6eca108400c6f53dd942108018daa7bb2842101e3d21d315844200e6a39a62b088400e55534c5611080f5c90498ac22101e3e21d30580420072ca9a60b008400c5f7354d62d04038b8e6a9ac5a0807359cd3158b410072aa9a62b16820287e85dc162d04010fb0bb82c5a08fe2fe1970d0b412245ec36e0a16823ccae649ca60d04039ace698ac1a08039554d31583416853bc0ae8b2c82b787d879cd659059f47d0939acb208028f61273596410062fb9ce6b2c8200c5f835cd65905730fd0e39acb208021fa1e43596410043ec3c86b2c8203a768190d65904014eb0321acb208b61fa1c43596410043ec3886b2c8200a5e83dc965904014bb07b92cb208028fe11725964154d1e422e4b2c822da3e841c9659040147b08392cb208021fa1f32596410043ec3e64b2c8200c5d738c965904010fd0e192cb208021f61c32596410051f42064b2c8200a3d840c965904018bae6192cb2080e9da0432596410053ac0864b2c8200a7a800c965904014f300192cb208028fe11705964133d1e422e0b2c822da3e841c1659040147b08382cb2080297a0c70596410052ec18e0b2c8200a6e821c165904014db04382cb2080e9da04705964116d3ac08e0b2c820087e87cc165904010fb0f982cb20803175cf30596410062eb9a60b
  | 19 => 0x301100080000300200380200500400800480300700280300180000580280200480000180000080000400200080780380700100180080380080000000080300100000000a00100180180000200080500280000080100200000f00780280a80080080000300200280500080300180780081802300080180200100000000a00100500080180280580080080000200280e00080500000800080180280581300100180600300000100100000200600100080000000000600400000380400880280800180100480180101380800980180600e00080000100080300000000000103a00001180080100b00001680780000280f80180200080000000080000080300080080300000580000000000000400380800000300680100000280580000e00080000580880100900480000000000081200980280180300080000000080380380300c01400000080000180500000000300080280080100000080000580580b80000580300080280000000100000200100280200100000600000000080600080000d00200100000580200780080000300080000000000000000501600880100380200100080100100100000200100700380000180000080180000000280080880c80380300f80400100f80000500000480000500380200680000200700380300600000100080700000100080a80000000c00c00000100280080a00400280480080100200200200080000000180080200100000000500080200000000000500000001a80080080100000300700380101380000200480100000180280200000000280301200000480000280000000080f00180180800700500180080680000100301000180400100000400000000080080181100100700700980300100080100080080800100f80000180300000200380480300180000100d80180000500080d00000480380000300080000200480580200200080480100000380380381600280000000080000100000100c00100400600100001a80580180000180180000000c002001805af335d85739874201e6a30ae730e84bcd97415ce61d08038bce6a9ac3a1003175cd53587420043ec1eeab068400a5d831d560d0805878eb2a2c1a11162f21d54583420043fc2ae6b06840287c855cd60d08010fd0fa9ac1a100a1f21f53583420043f43aa6b06840087c8754d60d08038bce6a9ac1a1003175cd535834222c5e43a86b0684078f4874c561908039a8e698ac3210039554d31586420055cc20a0b048400ad983141609080f5d504282c121002bc604505824203c7c43a60b048400e59534c160908018bee6a9ec2a1007171cd53d85420147bc3aa3b0a84018f7874c761508039ace698ec2a10039554d31d854201e3a30aeb30a8403cd4615ce61508018eaebb0cc2a1003355cf61985420047bc3ac230a84448bd87953605
  | 20 => 0x1420fc883a33784181006cc09d175872074d140065c00000051f08351887f10df07a07761982cda03807a94900019380005f431000002ee9b232da27cd5e0000a09a70f1298b18e131862a2dd00004cd4e05570000fd0c2a9e10000b2c7b67751b11ef041e4802f5001cd269591d10d6d0307380650628e620bc0001980d7e7035310a6475c3f93b610f042a00028b8340f0e2cf09b81a8f821b24dd8cfd2c27520679448e6a67b4be96b427014a2f202c00ee35d3ec0868cfe00013d261404e4891450000c860ec1cd011c9ec0003a4800023c7a33bc9a740002690000000ae294a374800057a00000011947e09d028e800035812025b9b2411018f062000003c5602d88af0cea4ce4858000000a253b587480c01fd43f1a900000005190a3000000000021e800015200000010340000000330000000076804406c00007e06645201434fa9da415a000000000000000000000000002210001c5c29c0004bc89d000010d24100000e237400023f07ac00014aa4fc0009ff00012a8b7a01700025b44dc686015a0947560000000d5c4d06264d4000149a64f0002414aa47ae0b02384934a5400000100180b00780280000400000680380300280a01080500a80000080000180000e80080100080300300000080080300100a00580600000d80100280180180300280000080380280200100000080500900200000500100000980180000280080000580000100000400000080300180e80180380100180500180100000380080a00000080582280080000e80180080280580080180300080000180080180280200000300000100080500980080280100400400880080000380980200000300000000980300880080500d00600000000a80080180000000280080000180180000100080680280100000080180000000400200080200280200080200000380000380480000100180080180000080000780000200080000180000000580500400000000e00180780180100000c80000400000000001080102100000d00080000100000700000000280100100b80b00380000100000100a00300080200000180000080080500d80200500580000000080280c00a00100300100000080000000180000500500480000280000200080080480100000380280280000000100080080a00000400080a80700100080300980000080680180a80400100300200100000000180000000000600100c80080080980800200980000180400000200100000200180800000700000280280700100000080000080000000680381200a80080000980280100780100100380080200000080200100280280080400180001180080200080680000080000080380180000780100500000300b00000500180480100980380000300180000000000101080200e80000980080000080100
  | 21 => 0x740001923e280006da3f800000004ac43900026904760003e384650966f93a600b825677639f9a600004de2c11a6837606b000000114a2d93ada36c10627f2db9ed000045e2b99adce2600052b09dca7012646ea6a91aa7ca2091a3c7ee2a541c91984da000000294cce00000e5a3902d84632a80cc8aca19315c24e08ae4f14cf97685cc55528817acc468fb32a8b0400000036f9f0c0002933158240b9c000033a04067850c3cba4ac5be30400013290f83373998fa481c97c3f602cd3ae90100011bc0007152729060f6a42a27610d498200051081592a05fe3628bdd3582f5000246904800000002852780000001e3c10c7df297a458252a024598000d7827815f27443e248405da8d47b46f323d86a814a0f515711d00000000000000a3e6ce2f600008aa9555210000b1200019519f01cc000000000149019d2db00014768471680e04a0888c4988e990e69b8055a5583da5142698c3c00004445488bc02c00044396944f64dd14f27483c40002601eb52cc11f17a256d41e0001c58000a4673e00019280007fd3c401b80485684a9005482a53100008b019c03b000243000011b3f71690d288ba09380008429743109fa40005e853600010a66d504e08c4e720e80e2000098645833b80000000000000de88e68174bf238c1b05d300000011228b9000121400002d0a100007d8000419000000075100000004568d12be00000004642aa24d4b3a18030420bc4782dc4c41cbca1287b444237c08a61a40098bc6c200029b8e282a075f0000000000852000000000075c103101c2549a219a0000f2a00008b028011e6671dc12b8e8874816b18b41c03a84e309d92c888b3bb9ea863440c352a8246482673d928183520bf4410a90a8a91b49d85a40005e3192a181038a030000001264a3611d2328ede84405384c8e341454a204f815258c4850d18e3a2e42930db0e0c59a0da00003a6a6f53502f400003c000210ca8e2482240eb134a54c1e1a1e00006b2181123ce0a50e50f14880000001e994b9130a433ac069850836e28c21f52f04c82121e3878856903084382343a14ed232111458d024032c29a0000001a5400000050a0000d940aa000236888200000000013fc0a242522ec5da2a331d00000000001390000000791000043c00000000000000000002a993ac49c6d90001c24db4a201760fac38002820416e84021bf1bf92c8b3c58a3f39350000000159057400093e42d8e5400011736b1db54926c747405247123073ad1508000a671b025a4a3c1bc40f0d1c4c6a4a154957cbbe5ef4ba9fcc6468a735a27dc0007af08e0194000687457149c0005b92769a2ca885300000b140002b45022471454a3f1e3963c6d438238215249700002d584890c46191511c449e67bd487800024656b2009ceceae4d500018d81b44692f48acc9ae2e
  | 22 => 0xa04948900016a0e0ea04fce3800025ea2ac000075000000000000032300007de00000000006120003e90848bce6f0000000043869f000000042c5621141a48bf002a3e594e8e5232e4700000b001b726d858d3143130bd05d935e000447800044001b4e48ffcbb800000017289ee23d01f80000001471f00000dd4a180798dd52661d500000013243104d3127c00000044d20dc76034248194d504c0004098dd928a72541c1c98158658018914913c0000ee80007103e100010a4ed45de000096c0da5790002498000a3c11909142c88b148c12649c40df20d0a582fe00a1a999451ea29d462944451c59820313485fa2910000000c600000778000130000000000096c2f8000273c0006a14c80550a004fc4798a61318107405258000012d0b280000000002d98000000000000000000094d2cb8b28b2200012e21c02da444000000107800003e80000000001568e79184958185a19910a6c3435a1510688cc212800100aa1207b19911d242b174000042e7de4cb000000030d46a1d0c0007711a81f104c87a02bd86700009371e8a74ce405c20331c884727f00d183200aa00028302a0c28594000021cd1c4e407489e4ac6085000000000000003c80003d847a2e5800000044b0001b740009c2000042000000000024d862e00000024b44521363f1009460638d24f11acc960e225a20082605ff38da3580001df00000000000004f31964a963c12eea3f4ab06d33e80b10ecc3e63f51d851029fc4f5a8e4a2a1b618e800052442819c9010e8043e000070cb0e9e83a518cc58057f3331a4400024300000013a894e00000000002473aa80007d455d00008943d251a0001eacfaa89711b91353c40000000000f049653a800000000001041058000000000000000041f1d994b03f634137e9af400040a003129000007e00022d4ff800000000000000004fb17994180002750de0958a6800000000005a23a300000000000002298eba7b021e86081084af30f80005c27000001c5800008e290998c4d46a01ec131d2f43fe4e69b8c01094c3bf205824a0002390be4000000000266cc841f83e61e9c72e8ee3642200cf4a4f18d93c800063d23b209c18a0000002600c1801c0861bd0cb85a60001494b980000f1a0ac0009bf38ca71000009a0ab17ec6a49a132815900008594b194f00003de000193431c0003870c8039e3aa2a7845445c0001540ca40a29bc0001fe800011844821d0f201280cd201849214c379000c1488314902790ebc4a31840ae93ce9510ff1cb909c1444d580000001b50000b0c00068200000000e096200001753e400029c80007ec77a217a0cc70e81b00000007a400007916200000001ab00006de06227180010be0003ab000000086e00027c40008040000f5d4008d0477976443000000000000003b60989c2c47c0e735592
  | 23 => 0x76cda40fa00024843f8000304a0a809457020114806bc70836c00008da00000026540002eb115265066a0000000000200000000000000038c000162cfae5ee3ff019034092210d9638c160004cd14c80000000000b545164c511f80000000001b197253ca00000002c80008bc00015dca141f71df9ab509286451700000000682701e4901000016980000007e618602b805e52a4140000000a2f0eb13e4fc60002bf000000074709a29848704fa1f6831c00000022d00000000003789a0477a5b440687201fa7a14f829650286520001a14000496000208084e00010f92c40002221be8cac83c5334ee126ca561f529f171846c4fb16706e0000a0b1750000344000011219c0000000e380000000004928000dce35826c8abc000110000264c0000002ca80003ae4904b4022548a72b46991a8cec0001e01e5871e34c1c8a7a824805b2b6831935a6a84c20000dd825d00016580801e0228090800000000007142d066944a8000884000040a6d53d29f81e60c2881a768129277800046010525d8b02470000000120854d3fba104ae800032480002bc00053886040a491d03a08d44e61e44fe93a108a0000001dcca7e24f3138000d54a2223e8000c820000000e008740002b50f640003b14eea4a000050b32607a85b00000000ce00009460000000d9a44012f220c3ca98352806bc00000000000002ae00022600009fc07330e21b40004e625c9579132a7413286a0ade83500811f88d86b62e8232400000000006340007dc36a251d4d663e0001b9083228731e12b4dc47be0ff9df40007e0000104c99a4a91db8650bc294300000010ba97f29da9b4000000000000000000000000013f65e05040000b8e0003e4a6dc86600000000000000004e28ae47746ba00d28acdb83e21e296140007a63881ae40008c70000000000000000000006659900018400000000000000000000000230c6ee30e3dd0350df619b2f6a3e05fe00407f81709981911b58e0c0008bd457854ccbc89449719ac6609b11b98568c689673d6074400000017280001243d51d914087ce6b12baa57ceb242000000000005294da000000086531ca3b12d800000000000000000c58f3c74aa4e47b0000edc99712588500002a7000000000062c0000000e960001bd87c80000000000000bfa00015a86c000000030200011e8784000287cdae60e07d84e4f7669e1778d9122431e0001f5946834e07299b89766b031281b013c13c51b9bb83d67a9202800076a4751ae181467a7280000f40f6c1ee4b80000000000000000024205320e0000a6890d3ed8565426000223000000000000001040001010000000b080002308000000161000150131c14b24520b92f677f22e80e87ba5131e595e81e06284cc9dd02261c60d6a0751e27371389d800008ed3fa84bc79a8cd0000e900008
  | 24 => 0x1890ba4e6c66a1c91914a824ba320002414621951d03743b664708a01e10600ba33c867803e8bf00292ad2b41a40820d7cb5e5c343185ac2e802602a1804b7882c060a8745ce5922229cf14e4a5b0e127654dc1403e68cd937a7a200025dd0d88dc07726e94965bf2b61fac73e61742f010c6325162d01238342000000000122896e2dd9ca9366a443ea13bc4ea8751fa8be84e025846c012c6b20130a3012400066852a8fa09160de13585551d69cb1c224b0ef610a00013fc0000004f68c190ae78600000006d22941808000f6670200000000006b800024d062860704500000000003a0a99133a0000000000df400037ba8452bc4302f800000000000001e287360000002218b9e0b11998c451600003fd98b80000003e8a624f28000000234800083e000242417c9001b80000000000000260400040b21f8d245e433b04b00007729fa372800000031f045800138239d000297c0008ce000000000000000011a10fe00000000000002271b28000e021f9111a0a40000000b9a5ac59200016d176c5e29d644e96f80004da41100004200000000000e420000c20000000a33000024cafa00013e00000000003cc00000000003b380000004143ed1584be600038a1298e9c17e0001cf4c3a1a5000103c0000001231a4022245123c86e91262ee4eaa5744c485a1ee197492e05915b80000008a300005700f68a802f1b44000403406226cf727c810228a472c4920f80000f3e2d42679c3c000000000000078c00014e19204fa49c101800019a4d61da22350846ff0ba8ff50ec6cf401a379322a3d37b0a34b5c65429415449e860d1669fb486e58612b95203e853d20ba98d1f41485168000d661fa000253c75e8ac17f0c9c0004df00027b830e00011980b000000000007391ee00000009451420011cc1bbc00009d000000000046e0000c88fba9f9153117d0d28a219f20d8fb20460c30a6894420c3c184492902832c98038e6832d0000f28a861e114127282de45b18b0730a0ea5a1f8834835ca0a4840e506b46060b725bcd84631028172000000000002dc85c79a38f21600008aa48800000005760708d4432c00050809bcc146e03c99ab8c0012e2298000ec87c013f1d3d43465304c9bf016c0d732b00000000005209fe40004e721d8fb84aa32f29b125548000028180c08b200000000000ec0002fb175457628923f800140e84f4df2084f3a8fe21b297107616200003f800007a17e02e118200051329300420db24c0998000000000000036255600000000004fd42a9e64c0657218283d090220e000000000000043ba3e45bc0d335d800000000008e80000000c00271794ef80b500000000844540000000000a46037838c844927000184d35c00000026700007703c680009ea000539a7600000dc33f1c9084c3be1d38df800026c49ea
  | 25 => 0x1c4915a8513861b0400097207c2118886678156167c0be60f00024e8e302f051625712042cc49c80e11240000960f200005f507526a50e28e200029803e65d205a080849479b0c40cb00001a70b92634c3047102c000064c0d612fa35d4cc3284ef80d45607e519892f0f48a5d4391a8818665f000195c88e8b8408800123c7cf3a11edd05a68323b9b1922a3df0a8800000080b2e02944dd60f90c805f49969b03221250382a0d20e9f088ac0201b91a200008cf3e300000004c2312170429e56735f24c00005d11550c842f213541e80006d080f511a3c80c6632102a2388682001588654bc462203f88252a87b13869ce8d1233a1408f08cca1893f908452807782d483c542e0001a216b00000000001ad40004f83b100000009a30000d3c00048d5028000000000000000020a780000000000044934b803c0000004cf0298ce61b90000b8d36c5aa00e8064dea3990001a103b420752c291c0009b9000000021200030b1f851ce6e6253823146249116380480009421b317c80007d34f7800000021e000000071c0002682224cfa072000000000090620492fc27a7f8109873470c55b00617600000000001e0450c66215001a4bee5831fe03086900af2a70000000000000000058400022e173413e6a6000128400086809da8a0d368400000000a4894b45a00011fe61134b026d18c9c751212cc3562502d198d4e645b201a113841678c0468a143ce04d13090b4098723000000124848343c80000008613149a344703a935180013e609417b000049834d411a4bcab850500015b86f27a50001d9400078500020fd44e5f900000000002541478001386000336a60897c0eb489a5cd0d43714b518480b447800008907a80001a51218f7e0002dc1a00e0e00042800000001dc2a50d5063000045b8d0c5900001aaa41c00000040f808d2ae4930b800007f600001ba5c486215b396a54d0327a81f901f000000048f9be0bf848c01f12202162881799878000671000286c70a4113980964c048000d9800139021d3e707403941660148a7d19646200005e079289c0bd9465330a5e000000030662a38f906cd148f002ba1586806614268f383920000000b443b200050e00013e892a28780001b263800000000000003c580000000000000000bf43f352b8798e8a0001d19280030000200096844c00000013c000000000028c116480707b986c3ec000000278098837c18026187787ff3dc136140291935482e4ce46ac47290b14a47f440a9294dfc1581c983904687ef3a99a64a369111208a5c00000036814045366de2119324d809cc34628540281850190b6c57e6c432d0eb489e5a116b8f8c1a29ce1298408b501ef130067cce80d537098ec5c492317da700b4e98f1630d2c00016a064857c0005d72251564000367081a61c5a479e2f88000000
  | 26 => 0xb3800d4f192a0db65b023e24387ca85c0000d14acc8e600022f80002ab1d008c12820004f6151890ea65258000134e3fa1f21dc800055a0b8a1300008a433614b4ec65d400010c8000809409025cfec727000236400424d00016405421d82bc22582ce86f3aa22d812a5c431f813cf380003850244e5808244213b8b8a63751c29a42f800000028650902443769a9c9c2a1626e1b2c00022d48b877807200025aa3a882000028694711809a037413440007e800016d400000027486300000000de8e7000046715b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1e05534c6621064000615dcd810cb655000185b7360032d95400050764c859d8425000103c9660d75109400060be1f6558842500018aa76e0162109400070554d319db415017544c925cd535844000417e61731cd65c8001615919cd53993200060761d53cc664c800121d9321570993205d583a4b8354d64c800181e8754f3159320006a1609310c564c80018a472205705932000e1521d534c561c800105d93e19759072000417662655ce41c8001d05534c4744872000417e4d86dd540c8185a0c8254d3199220006a44c5800c5648800154993201751092000558644805d44248001949834c175109202ae4a6017599042480ad92b805d56410920006495d4815904248001894845cd61185200054a654425c2414800152995109701052000529259311d12148001d05534c474485200074254d301d12148001d81314c07448520006611d183185214817544c925cd5358420007051d1534c56108179894845cd6190420007051d1534c562c400505e98dcd63d951000613dcc8258f654400105f985cc63d951000515a5b734c7654400105f985cc73d951000615dcd810cb654400185b7360032d95100068560d81197644400160c9258d53d911000585259534c7644400121d93a1672d91100060761d530cb6444001a155360432d91100068654d800cb644400181d8754f31d911000515e5d534c6644400181e7660c651911000685a45831946444001a159160c65191100068560d81194644400141d9798d531911000507e5d6354c644400160c9258d53191100058564c6594464440016159319631191100058564c654c464440016159518d311911000585a59534c464440016149654d3119110005856467354c644400181d8754c32191100068554d810c86444001a195360032191100060761d53cc464440016159594d311911000585657324c4644400121d9321570191100068554d81cc06444001a15854c730191100048764c854406444001a455360432d89100069254d800cb624400141d9319674989100050764c655d2624400141d939d764989100050764e75192624400105d981cc65589100050764c65dd1624400141d93194745891000417a6065dcd62440014549754d315891000e1521d534c56244001c147454d3158910006165c18319462440014599319570909100041764c865d4424400141d9319774485100050764c651d1214400105f9361f65c81100050764c659d3204400141d9319574c81100050764e75d93204400141d939d464c81100058664c6519220440016199319464481100059264c6518920440012689661442481100068554d810ca6404001a195360032990100068554d810c96404001a1953600325901000615605751c96304001859805d47258c10005916447354d6204001649901cd5358810
  | 1 => 0x33071554088479340e3d301a4a8473b1405c811806cbc001d80000000009c7c8c0c800000000000482344800000045299464a00000002d3280000003e270ce2c2c8005200002000025000dc0000001754e0b39000ee00351300016458c47086259c018000021c008d39800b0410000000000000000262900000004b00000001d1d0c6000019908180e94530002d1e0ac0a2fa75041123190007921970544e020d024354b82144104c9ecae13100a02e7a4a8e534833f1c51c05010c8006f4f1246c4f10834802b00120007f0094c062f4d869286c490242a750e088000000001423c22188d6001f8013e0000078da0000000000f000000000001083ea42d914009003294006e42a452600001f40014309a00001031702030005030104030703060008000f0001010007050001090102020007030000000101010500000006191f04002803020b00070200014172617354d60d097584c825cd31594425d691209534c5611080185973600325964100683611829d5639040144e92e1d7558e41006a1104825d16390401855815d47258e41006165d5801c9639040103f9660d7510a4100607e1a635d44290579c166158d7510a410069154d810cb6250401a495360032d894101d3125d324c56210401c15534c576908410064560d315d4421040505c985cd53580410051525d534c560104078d0874c5305804100e1621d534c160c840141d931d774582210050764c751d1608840505c985cd53582210051525d534c56088401c147454d315822166685219534c764484038578754d319912100585654634c46448597a148654d311912165e83209534c464484016159594d31191210078154f824c46448401e05532093119121005a8640824c4644840161595cc931191210068554d81cc06448401a15854c730191215d583a4b8354d640857544e92e1d7558c215d613209755c16308575a488254d30580215d592a4b8354d6008575648925cd53580210069154d810c96290001645911cd5358a40005926407354d6290001ac1316003158a40007039d67398a419000142f9754e6290640005a164e719884190
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x108000360153640824c46448401a024b2a6988e890a400089268c966144248110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4e
  | 7 => 0x3
  | 8 => 0x94c
  | 9 => 0x94e
  | 10 => 0x124c
  | 11 => 0x124e
  | 12 => 0x138c
  | 13 => 0x138e
  | 14 => 0x8c
  | 15 => 0x8e
  | 16 => 0x98c
  | 17 => 0x98e
  | 18 => 0x128c
  | 19 => 0x128e
  | 20 => 0x150c
  | 21 => 0x150e
  | 22 => 0x10c
  | 23 => 0x5
  | 24 => 0x10e
  | 25 => 0x180c
  | 26 => 0xa0c
  | 27 => 0xa0e
  | 28 => 0x130c
  | 29 => 0x130e
  | 30 => 0x180e
  | 31 => 0x20c
  | 32 => 0x20e
  | 33 => 0xb0c
  | 34 => 0xb0e
  | 35 => 0x140c
  | 36 => 0x140e
  | 37 => 0x154c
  | 38 => 0x154e
  | 39 => 0x28c
  | 40 => 0x28e
  | 41 => 0x184c
  | 42 => 0xb8c
  | 43 => 0xb8e
  | 44 => 0x148c
  | 45 => 0x148e
  | 46 => 0x184e
  | 47 => 0x40c
  | 48 => 0x40e
  | 49 => 0x188c
  | 50 => 0xd0c
  | 51 => 0xd0e
  | 52 => 0x160c
  | 53 => 0x160e
  | 54 => 0x188e
  | 55 => 0x98954
  | 56 => 0x98956
  | 57 => 0x128954
  | 58 => 0x128956
  | 59 => 0x94994
  | 60 => 0x289
  | 61 => 0x10a
  | 62 => 0x1489
  | 63 => 0x130a
  | 64 => 0x14c9
  | 65 => 0x134a
  | 66 => 0x99254
  | 67 => 0x99256
  | 68 => 0xd09
  | 69 => 0x1889
  | 70 => 0x40a
  | 71 => 0x160a
  | 72 => 0xb0994
  | 73 => 0x98b14
  | 74 => 0x98b16
  | 75 => 0x154994
  | 76 => 0x99554
  | 77 => 0x99556
  | 78 => 0x40994
  | 79 => 0x98414
  | 80 => 0x99894
  | 81 => 0x98416
  | 82 => 0x188994
  | 83 => 0x188996
  | 84 => 0x99896
  | 85 => 0xa0b
  | 86 => 0x180b
  | 87 => 0xb1514
  | 88 => 0x150b14
  | 89 => 0x150b16
  | 90 => 0x28b
  | 91 => 0x148b
  | 92 => 0x189514
  | 93 => 0x151894
  | 94 => 0x189516
  | 95 => 0x151896
  | 96 => 0xd49
  | 97 => 0xa0114
  | 98 => 0xa0116
  | 99 => 0x28114
  | 100 => 0x28116
  | 101 => 0xb9814
  | 102 => 0x148114
  | 103 => 0x148116
  | 104 => 0xd0114
  | 105 => 0xd0116
  | 106 => 0x188114
  | 107 => 0x188116
  | 108 => 0x180a14
  | 109 => 0x180a16
  | 110 => 0xa1854
  | 111 => 0xb8a14
  | 112 => 0xa0b94
  | 113 => 0xb8a16
  | 114 => 0xa0b96
  | 115 => 0x184a14
  | 116 => 0x184a16
  | 117 => 0xa1856
  | 118 => 0x40a14
  | 119 => 0xa0414
  | 120 => 0x40a16
  | 121 => 0xa0416
  | 122 => 0x160a14
  | 123 => 0xa1614
  | 124 => 0x160a16
  | 125 => 0xa1616
  | 126 => 0x1949
  | 127 => 0x181314
  | 128 => 0x181316
  | 129 => 0x29314
  | 130 => 0x29316
  | 131 => 0x149314
  | 132 => 0x149316
  | 133 => 0xd1314
  | 134 => 0xd1316
  | 135 => 0x189314
  | 136 => 0x189316
  | 137 => 0x180b94
  | 138 => 0x180b96
  | 139 => 0x185814
  | 140 => 0x181854
  | 141 => 0x181856
  | 142 => 0x41814
  | 143 => 0x180414
  | 144 => 0x180416
  | 145 => 0x161814
  | 146 => 0x181614
  | 147 => 0x181616
  | 148 => 0xb8294
  | 149 => 0x28b94
  | 150 => 0xb8296
  | 151 => 0x40294
  | 152 => 0x28414
  | 153 => 0x28416
  | 154 => 0xd1854
  | 155 => 0x160294
  | 156 => 0x29614
  | 157 => 0x29616
  | 158 => 0x184b94
  | 159 => 0xb9894
  | 160 => 0xd0b94
  | 161 => 0xd0b96
  | 162 => 0xb8d14
  | 163 => 0x188b94
  | 164 => 0x188b96
  | 165 => 0x185494
  | 166 => 0x185496
  | 167 => 0x41494
  | 168 => 0x148414
  | 169 => 0x148416
  | 170 => 0x161494
  | 171 => 0x149614
  | 172 => 0x149616
  | 173 => 0xd1856
  | 174 => 0x189854
  | 175 => 0x189856
  | 176 => 0xd0414
  | 177 => 0xd0416
  | 178 => 0x188d14
  | 179 => 0x188d16
  | 180 => 0x189614
  | 181 => 0x189616
  | 182 => 0x1a49
  | 183 => 0xeca
  | 184 => 0xec9
  | 185 => 0x1a4a
  | 186 => 0xecb
  | 187 => 0x14a
  | 188 => 0xb4d
  | 189 => 0xe8a
  | 190 => 0x18ca
  | 191 => 0x104a
  | 192 => 0x194a
  | 193 => 0xeca13
  | 194 => 0xed813
  | 195 => 0x1a4b
  | 196 => 0x151296
  | 197 => 0x150cd6
  | 198 => 0x749
  | 199 => 0xa18d6
  | 200 => 0x21294
  | 201 => 0x21894
  | 202 => 0x20d54
  | 203 => 0xec293
  | 204 => 0xed493
  | 205 => 0x149854
  | 206 => 0x149954
  | 207 => 0x1498d6
  | 208 => 0x149856
  | 209 => 0x40996
  | 210 => 0x41496
  | 211 => 0x41796
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2128
  | 6 => 5045
  | 5 => 2677
  | 4 => 168
  | 3 => 3
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
  | 7 => packedAt gbK7 (87244+((h/709+packedAt gbK7 (78736+(h % 709)*12) 12) % 2554)*13) 13
  | 6 => packedAt gbK6 (265694+((h/1681+packedAt gbK6 (242160+(h % 1681)*14) 14) % 9749)*14) 14
  | 5 => packedAt gbK5 (168647+((h/892+packedAt gbK5 (157943+(h % 892)*12) 12) % 3534)*13) 13
  | 4 => packedAt gbK4 (12208+((h/56+packedAt gbK4 (11760+(h % 56)*8) 8) % 244)*9) 9
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe1e0f07f87fc380fff80fc28c67c19f4f3
  | 1 => 0xf0f01e00ff87f87fc00f03fffcd72590e6389f
  | 2 => 0xff001fff0007ff8ffff003ff031839e307cf1c
  | 3 => 0x1ffffff8000ffffffc0003e03e03f80fe0
  | 4 => 0x1ffffffffff00000000003ffc003fff000
  | 5 => 0xffffe000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110c06020098094082128822800402408d431
  | 1 => 0x90a106005482082a404a112cd0432490622886
  | 2 => 0x2a0248a90004d50492a00a5209180961054518
  | 3 => 0x808413129d50000b254cd00412e03602b00ac0
  | 4 => 0x8089ddcea6766400180601863bdc003dfb000
  | 5 => 0xcccf00180c4044020608806083febfd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36254
namespace PEqualNP.Outside.L_meta_36254
open PEqualNP.Outside.L_meta_36254.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 14 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 19 := block_range (n:=19) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 467 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 634 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_4_160 : Interval gbAtlas 4 160 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 168 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_2656 : Interval gbAtlas 5 2656 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2677 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))))))
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
theorem bgb_6_5024 : Interval gbAtlas 6 5024 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5045 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)))) (concat (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)))))) (concat (concat (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376))) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))))) (concat (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))))))) (concat (concat (concat (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)))) (concat (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104))))) (concat (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264))) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)))) (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584))) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)))))) (concat (concat (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904))) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)))) (concat (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224))) (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))))) (concat (concat (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)))) (concat (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2128 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8feeefaeafee8fac8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36254.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[2,4]⟩,⟨.and,[2,3]⟩,⟨.and,[4,6]⟩,⟨.or,[0,2]⟩,⟨.or,[9,10]⟩,⟨.or,[6,7]⟩,⟨.and,[0,12]⟩,⟨.or,[8,13]⟩,⟨.or,[1,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36254

open PEqualNP.Outside.L_meta_36254 in
theorem PEqualNP.Outside.L_meta_36254 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
