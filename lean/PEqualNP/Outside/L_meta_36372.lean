import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36372.Model
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


end PEqualNP.Outside.L_meta_36372.Model

namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
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

def SBf (j : Nat) : Nat := [6, 6, 7, 8, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36372

namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
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
end PEqualNP.Outside.L_meta_36372
namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x8ee21ec21
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (34+((h/1+packedAt s1K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 2 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 3 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 4 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x6108023084001004404c048c6024621801515c
  | 2 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 3 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 4 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36372
namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc00f8f0200d290000280008800028840090008c27007918e1aa80104874c8700300250800411504ce1b06ad315005800a402c9002e04f28300200208328e080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x70004c92a404006a4a1600845c068200620000680000369838302e286454003e00b4000050001c004e000000888c5a3a2a007c3244a6b080121a0a56726600000000009a000000000000468a34523ca2000000000000000000000000006e7a420c58948e7602a00078001848862010085e9e60ac2400a89000002c009600ae401e0000b67e0022aa00000000000000006c0000b274000014269c00000e0000000009000001020000070003020902050f030000000003000309010607000100cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6e0024a80c010c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
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
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 3 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 1 => 0x88841110902a00283104208884111298324486
  | 3 => 0x144aaa290d548353888b54156a82a545858b18
  | 4 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36372
namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x129e56000005030a880018c843e88000000d30a122cd12528118026607810074000001c000289c00042015162e0001c3600705049080d22001001380008040202107ff43fe43fd43fc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xa61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930f799261ec324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4187bcc830f6190617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ee42c83da85907b10b20f799641ee32c83da65907b0cb20bf28e417d51c83de43907b88720f690e41ec21c83dea9907b95320f6aa641ec54c83dea7907b94f20b729e41ed53c83d8a7905b14f20f7a1e41ee43c83da87907b10f20f7a8e41ee51c83daa3907b14720f7a0e41ee41c83da83907b10720f798e41ee31c83da63907b0c720f7a0641ee40c83da81907b10320f798641ee30c83da61907b0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94416d52883de65107b0ca20bf28c417d51882fca1107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41ef42483dc84907b50920f621241ef32483dc64907b4c920f6192417f51482f8a2907bc8520f710a41ed21483d842907ec8120f710241ef54483dca8907b55120f62a241ef53483dca6905b94d20f6a9a41ec53482d8a6907bd0d20f721a41ed43483d886907bd4520f728a41ed51483d8a2907bd0520f720a41ed41483d882907bcc520f718a41ed31483d862907bd4120f5a8241ef40483dc80907b50120f620241ef30483dc60907b4c120f6182417f54082fca8105f55020be2a0417f53082fca6105f54c20be298417e52082dca4107bcc820f6190417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10f799621ec32c43ec83887d50710fb18e21f531c43de41887b48310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52843dca5085b94a10bea9421ed52842daa5085f14a10f799421ec32842faa3087dcc610fa18c217e50843de41087b48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443de64887b0c910fb20a21f541443ec62887d4c510f790221ed20443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810f799021ec32042fca2087dcc410fa188217e50043de40087b48010fb88021fa10043ea20087e44010
  | 1 => 0xd52907de6520fb0ca41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0ef90d41de21a837f52507dea4a0dbd4941be29283ec52506d8a4a0efd0941dea1283ef32507d864a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420fb94841b7290837d52107daa420db54841f799083ec32106fca220efd0441fb20883bd41107ea8220ed50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31f799663ec32cc7ec8398fd50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31f7294636e528c6faa518fb54a31b6a9463ef328c7d86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7de6498fb0c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418fbcc831f6190637e510c7ec8218fd50431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc8590fb50b21f799643ec32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef42887d88510fbcca21f6194437e51887ec8310fd50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487de6490fb0c921fb20a43f541487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21bea98437c53086fca410fbd0821f621043ef32087d86410df94421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40f799681ec32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40f7294816e52902faa5207b54a40b6a9481ef32903d865205f94640bea8c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c52503de64a07b0c940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081ef32103d864205f94440fb288817651102faa2207d54440baa88817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30f7a96617e52cc2faa5987b14b30f799661ec32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a9461ef328c3d865185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21
  | 2 => 0x4c800200404804010018000290000140680c0100040980100000400801000000020050040a80f01b002018018020020000800000e00405838004024000000000140981000a0000080000000c1100400800c0d00502600c0200100200c0c01507203c020500200000080d000000048090000080680500a0180200400a02c010020040040180a004000000200000100002300e00001000004000000020040080580501200807802010024110000000040080b0000000200a0000040880300a0a80000200003000801002000010010020140b80700201009800000000048000000100380c0020540100101c0340082b0120c80000000400011802002054048030020040180101c0040900000a0001c8060000100000400c0140480801001c000030000280000001a004018020080000001100a0280280000c0080300502802024002002000048010000000000401600004804000000010020020000b0180260000101b0020000380601a00400004006028015f94b43f7296876e52d0efaa5a1fb54b43b6a96877e51d0feca3a1dd94743bea8e87f551d0eeaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442fb28885765110afaa2217d54442baa88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997bd0b32f721665ed42ccbd885995f94732bea8e657e50ccafaa1997bd5332f72a665ed54ccbd8a9997bd0f32f721e65ed43ccbd887997bd4732f728e65ed51ccbd8a3997bd4332f728665ed50ccadaa1997b14332bfaa4657e548cafaa9195f15232bea9c657e528cadca51977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a0657d540caf8a8195f94c32bf29065ef420cbdc84197b50832f621065df320cbdc6419774c832f6990657e510cafaa2195f94032bea8065ef540cbdca8197b55032f62a065ee530cadca6197394c32f7a1865ee430cbda86197b10c32f7a8865ee510cbdaa2197b14432f7a8065ee500cbdaa0195b54032f6280657e53d06faa7a0ef90f41de21e837e52d06faa5a0efd0b41dea1683ef32d07d865a0df94341bea86837d54906fca720df54e41bf294837
  | 3 => 0xf3000260989ae44abe8e02d2000000000ee00039c000000000b04e0003300005a87b000638a62cc2f88a95c9b0504000f81d45243c8bbaff000000e7aa7506a392f2ce3fe704ca16701e9d11e0002aa9087aa320009107a0d1000918ba8b1000000ff095000000001fa622994169423a05f400000500b74f8a0d0ea000001a25d81b143990000b11310004e28ac9c0e24045d15285c198680df2fd5b6000bb00033400155969630bf8002220003991682a4660012d94044c8f97a1344f03d91e935134b8c3e118000860578004921e05e14453438075063000000ea84d61ea990827d2dc959141c838a998000de108204cd8004749a51fa6d00000019000560000000654c6b20001c2370ad4000000000002823b0ce55065807000928e8a554722f56f20a000000b218516c0009c80009e64507800000570028f808a479240000bc0018131735aa400030b0006fc001ce00000015a450004f12e0b960090441a2000000120006000000002bc5106d000000452694de9c304a9f89800903a760830dd4e680178972228b84331ee442184f110258e8d40e2d931828c81847222091729e90de1088e9994ba5e4f905a39217c301ea59e5c07e9cc3bc28184040174058370a21b46b06501a51e238b102663c37c3821e1d09641a1e3342201308004beb9cee10962a045752571a01a81c8ae1107289780043a10c8b91643400000307000000000e90003489609d000000002b160a294002895ac001882da21c000ad2a8000831342ee04216cb40a817c0a07cb205186191ba9540832094a8b1185e0002bb000394ee88214c0007e000000870232a12a26e4f620349800048a43132b540000006200177ac2000b9000153546c702208a4f8814369d22ca6982c2c13265184fafb4d6790071973de484002ed0000001c000618000001a4200000dd8c251a30c002c00002fd4caad5d022400000000000b0a270006a40c00032c4ec4b03500004c0012e000598da913000bd529a7a2b20000023807c0008e0c420ea2864800000000000006280000000041c29c0018b000000002c3166aa8001e500069c1d0000000000009e19c22c008c646c6a80014e57aa582c800000000052df3b2add0b800000000000aa1800d88daa00008c0000485a2021890b0214accdb1014b4000110a40000009f83b4dc00005af0458540348c5000634c900057e0f000247244000a795f2d43bc820005925cd7e0fe2968d0002f6256b34bf285432b80ce8544280b8723192863b047a061fe148fc9da3c2be41ba7935ea91281f6182b4d5730e20a620252933ce4f48804c0f25053d8ab58c9d53521f0526ad6a0bb2c6b5d18a111524a066aac3f8534b61b22742d0fb9241b63dd288eb1f61e8e32e20acc04560272b6ad90aab225a96043208000a040babe0000010900027c00000000
  | 4 => 0x1204a41d15c1f80004200f11211a1a069a2322a73574aeb59699c3b10b0fe8594f8d95eea194e84e000001268005cc4a8f980045e000289ba4260000022421a6c4679871200088d24b3b6465818f1574b7032137000124568335682c8a38716147994f15d1ae14c861bc000000d1a4e1425140018f0007d0b6a7600024c000dc0009b000157000000000002f4354b88140000001180055e7580024f21e2e0001252bc00000000396360000000000013b8000000009980000038c003040e4a5c3f1261a8000020000007f400000006000000000e6000002ca508560ef9565440004d80c4a805400000000981489b33120000013663e0000031b000000c00000001dc2e8f040212d4e19c0204c80f9f530449ca418423ec580026f0007ad832981f400139000302000002092a4a6c76a071ac9fc0000036e00179062306628e3b0d036b400c8921c2c24b016b350528a49e024686c1f8970fa3cc5b8000d60004a000000c7517012040000000c707a0000000005e000b780058a75c003130007100003010a82c20a7033c5ecca8002fe000000005287a0e988700015c002d833ebe02a8000007b4002a901ac68fda
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd51482eb6054520ab99051482ad6414520d9544514826f65505209b195414826e65105209b59441483a541105209b996314826d658c520ab99231482ad648c520d314e314826f654c5209b195314834c530c520ba98031482e9600c5209b996404826e6510120b398c40482cd6310120b998440482e56110120d314f304826e658c1209bd95304826c654c120abd9130482ac644c120d314d30482e7614c120b9185304826e650c120ab99030482ad640c120b998430482e5610c120f24c0304826e62d50209798c540825d63150209b988540827661150209d584540826e62d4c209bd89530823e6414c208f590530826e6214c209d98453082756114c209b98e520826d65cc8209bd94320826d650c820d394c320826f65480209ed95200836a52480209bd8954c426c62553109b98854c426d62153108f99353c423d64d4f109b98b53c426d62d4f109bd8953c426c6254f108f99052c423d6414b10cd15141c42b5648c7109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108fd91538423c6454e109bd89538426c6254e108f990538423d6414e109b988538426d6214e109b98e528426c6354a109bd97328426d65cca109bd94328426d650ca10ba580328425f63551109718d544426f62551109b189544426e62151109b588544426e62d4d109b58b534423f6454d108f191534426f6254d109b18953442776154d108fd91524423c645491097d8d524425c6354910d3d4c324434c530c910ba58032442746550510cd1514144276658c510ad5923144274654c5109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10d3d8a530434c6294c109bd89530426c6254c10c7951530431d5454c10d3d89530434c6254c10d5185530423e6414c108f590530425e6314c109b988530426d6214c109d984530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d53948109b98e520432e5454810cb551520434e5354810d354d520426c63548109bd81520426d60548108f990520423d64148109798c520425d63148109b988520426f65cc8109b597320432e54cc810cb553320434e53cc810d354f320426f650c8109b594320432e540c810cb550320434e530c810d354c320427565cc410cd553310435553cc4109d5943104335540c410d554c310426e62940109b58a500426d65c8010cb953200432d54c8010d394f200434d53c80109bd95200432e5448010cb551200434e5348010d354d200433554c4010d554f100427965840109dd9510043355444010d554d100427b6544010
  | 1 => 0xc26d62947309bd8951cc26c62547309b98b548c26d62d52309b988548c26d62152309d984548c27561152308f992544c26e62951309b58a544c27661951309d586544c26f62551309b189544c27761551309d185544c23e6515130c758c544c31c5490d3097195434c32f54d4930cb153524c32f5414930cb150524c26e65cc930cbd53324c32c54cc9309b994324c32f540c930cb150324c33754d4530cd153514c36752d4530d914b514c36732d4530d90cb514c3375414530cd150514c3675214530d9148514c3673214530d90c8514c35451cc5309b98b540c26d62d50309d987540c27561d50308f596540c23e64150309798c540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c32e54cc830cb553320c2e960cc830cb950320c32d540c830ba580320c3365494430cd552510c3665294430d954a510c3673294430d90ca510c3365454430cd551510c3665254430d9549510c3673254430d90c9510c31d54cc030d5547300c25f654c030c7551300c355514c0309ed95300c3cb324c0309d98454c827561153208f99353c823d64d4f209d98753c827561d4f20cb55042c82e66110b20b958442c834e530cb20ab99021c82ad6408720d954421c82e960d5320cb55054c82e66115320b958454c82e96015320ab99353c82ad64d4f20b998753c82e561d4f20ba58353c82e96014f20d398c53c83696014f209b99743c826d65d0f20b998743c82e561d0f209bd9543c826c6550f20ba58351c82ae6414720ab59051c83655114720ba58051c826f65507209b19541c826e65107209b59441c83a541107209b99631c826d658c720ab99231c82ad648c7209bd9531c826c654c720b398c40c82cd6310320b998440c82e56110320d394f30c82af644c320ab19130c834e534c320b9d8530c82e4614c320ab99030c82ad640c320b998430c82e5610c3209798c548825d63152209d984548827561152208f990538823d6414e209d98453882756114e20d394f328825f63551209718d544827761551209d185544827661151209d584544823f6454d208f191534826f6254d209dd8553482746154d209b188534826e65d09209b195424832c5450920b998442482e561109209b997324834c53cc9209b996324826c654c9208f990514823d6414520d914521482ae6408520ab59021482e96095120b3d8d54482cc6355120b9d8554482e46155120bad81544832d5415120b998454482e56115120ba582534826e6394d209b58253483696094d20abd9153482ac6454d20b9d8553482e46154d20bad81534834e6314d209b997434826d65d0d20d314f43482e661d0d20b9587434826f6550d209b195434834c5310d20ba98043482e96010d20ba58251482af6454520ab19151482cf6354520b318
  | 2 => 0x60548419bd97321066d65cc8419bd94321066d650c841cb54b41106b56490441d954a411063f6550441cb54941106776550441d954941106b76550441cdd9541107365350441e9d8941107a46250441e994941107355250441e954941107255250441e9cc941107a432504419b98a501066d6294041cd505501066e62d53319b58b54cc66e62953319b58a54cc73654507319b98a50cc66d62943319b98b548c66d62d52319b988548c66d6215231cb952528c72d5494a319b582528c72e5454a31cb551528c66f6054a31cb953328c72d54cca31cb950328c72d540ca31cd553318c66e62942319b58a508c66e62951319b58a544c67561951319bd89544c66c62551319ed81544c67860551319b583524c66d60149319b997324c66e650c9318f990504c63d64141319b988504c66d62141319bd89540c66c62550319b988540c66d62150319e980540c67960150318f992510c63d64944319d596410c6d56390431cd151410c6b5648c43197d95310c677654c431f10c9310c66e62940319b58a500c74e530cb219798f548865d63d52218f993538863d64d4e21b9584428874e53cca21cd15141886e46250621e9d09418865e63951219758e544866f62551218f992534863d6494d219bd89534866e65909219b195424866e65cc921d314f32486e661cc9219d19541487345450521e9509414863d6595021cb189540863e64150219b988540867661150218f993530863d64d4c219b98b530863e6414c218f590530867a6014c219e580530866d65d0821cb553420866d6510821cb55042086e56110821cb953320872d54cc8219b594320872e540c821cb550320874e530c821b9584320872d54c8421cd552210866f6548421cb55121086776548421cd551210866f6254f409b18953d02b561d0f409bd8951d026c62547409bd89539026c6254e409dd8553902746154e409b98e529026c6354a409bd97329026d65cca409bd94329026d650ca40ba580329026e62d4d409b58b535023e65d0d40ad587435034f530c940d314c32502e9600c9409b988515026d6214540cd145415034f6294c40d318a531026f6254c409b189531034f6254c40d3189531023d6590c40c754e431031d5310c40d394e521034d53948409b98e521034e5354840d354d521026c63548409bd97321026d65cc840d394f321034d53cc8409bd94321026d650c840d394c321034d530c840d594e51103555394440d994a51103655294440d9cca51103643294440d594d51103555354440d994951103655254440cd90d51103344354440d9cc951103643254440c754f401033551d00408fd95401031d5350040cd545401027b65500409b98a54cc26d62953309d98654cc27561953309bd8954cc26c6255330ba58332cc2e9600cb308f99251cc23d64947309b98a51c
  | 3 => 0x172516000a780020a5615400000092d84000000a1000000078000000008010020000200700e00c0000c00c00003009000004020000000000100200001c0000200c004020020000000080e0000040300303000400000000000008030000040000100000c0100800000c008020320040380100200c00000006020010050020000000300600400000012000000000000080000400000c0100600e0080000000c0000080400200c0280000202c0000000400000802000000008020140100100200201c0080100400000000000004000000080000300002800001802000000058030000000380100a018000010040000180a00401c0680200800c000010080000000a000000028000000080080000400002000000020000080020080100000001c00003004000028020000040000300001800002002000088020040080200000201002000000028050000100040080300c00003804020004000000060040080000200007800004010028010020080000000800c010020000000000000200c0000500600a6d6094b439bd8152d0f665294743d954a51d0f665254743d954951d0e6e62943439b58a50d0eb561d0e439b98a5190e6d62946439b98a5090e6d62942439b5835250e6d60149439b9885050e6d62141439d9845050e756114143ad5874310e3f6550c4397d954310e6f62544439b1895110e6e62940439b58a5010e3f65508429bd954210b374254442d99095110b354254442d95095110a7661d53329d58754cca7661953329d58654ccb2e5450b32b998442ccae56110b328f99251cca3d6494732b398f54ccae661d5332b958754ccb2f5495332b998654ccae56195332b398c54ccae661d0f32b958743ccaae64d4732ab59351ccaae6494732ab59251ccb675194732ab99050ccaad6414332b998450ccae561143329d984548ca7561152329b58a544ca7661951329d586544ca6f62551329d984540ca7561150329e980540ca7960150329b596420ca6d6510832cb550420cae66110832b9584420ca5f654c8329bd95320cace63d5032cb550540cace6315032b9984540cae56115032ba980540cae96015032d398e530ca6d65d0c32b9987430cae561d0c329bd95430cb8d4310c32ab990510caad6414432d9544510caea6014432ba580510caae6414032ab590500cae66114032b9584500ca6f6254f419b18953d071d5310f41d394c32d074d530cb419b98a50d066d62943419bd89539066c6254e41d394c329074d530ca419b98a509066d62942419b98b535066d62d4d41ad986435066e63d49419b583525066e6314941d9584525066d6014941cb14b42506b461509419b997325066c65cc9419b994325066c650c9419798c505065d63141419b988505066d62141419bd89531066c6254c419b98e521066d60948419b18d521066f
  | 4 => 0x5158004c0824000000000000015437e0000006f60eaf400000050001339fa248000001b10b0780e70003a8494001e3000000918000ea0003b8005800000030a42c000000b10008b4001852d80004d15507ea60000000006200029c448c0c85000028114000521fc544000000008280028130e000000160000000011400000000179042528da0003c80012999a00a27c390c1482b80b38a70000005f9c65fabac648002c68e4d0000574000001c20804600c21942a4d00000c40652c3400000000000000000000002af000000e20f50004f4559620003805e2e93ee000e7add000bb50a24e196000130f239000032acf0000003d90d276254970416040004f00034c270c00fa41a000b580060868c0019c000bc17285b000000bf2990001cc000cf0107b82313e256964911a52da0a400000000028a99f40000013b0003b8805081f93422b4631464040796c9c743e57904000000a6c6a000000a395db0603aaf90903206213c430a55d0068671783ae0000000000056400000038000002640000000007d0000000015f0a647c0023c0000000014c00011000064000000000000007c0000001c200119000000130000000009c1750000008d80000000000000000000000001fc00056d1ea85440000f30b519434400000000bb034ae32700055a8c4000000002d2000001361ac5ec000ff800000ad8fc0c200012545000318000e62d15700012c1e13a200131a00374a54ec1000be0000018344a00152ae1000298c100012e000001ca0007bc00273436001108004bc6297990b2ac0000015244e679151261dc1f08f000364a400024741c0000019f1e2000cc0f908e000000001d0b780027a012000bb8f3224b40719b63aa65c0022f0009542a08a6180000002a2f8000492962b80000011a2260b96c26d326a315c8ec53c2155626b1301c441a0731634c18000000430c908239a4557701b16002cc709d0005983c8003c48a544a7f4d051cfb1b020e1541617631a23c002e643a00000000000b28002b40000012200000019c0012800000000000000000002a61126586a94d584000b0a131e81c17c99d11a7a400238150878000dc02665400000292000498000007b0618004ba00000000000aa40f80007a000000003b29183a2185be5f4300000002d13badc4464746f86e5c80017e0fb0000006ca7b554134120005c40017b800372000000000000000009900000000000000444000a20000000016500000084b01000000000000004e52f8000005d4000005987956280018a9a89480000045cd2000000c24d51274f837800000546000000000000000000000055c000000004656d1de59600166aa10000002122200012ca18002e80012b19950c0018280005ebd0968e7000a80000000000000017a000b38002ff06c000d69fd25e00000000000000
  | 5 => 0x1a0000022c000be85b000376000000120000000000000003c002d3000000002430000001d8000000000000040c2a54a00041e138e81321b0b21418004500000027d0003c0002870c4624001303e200000000000000000ff422000000000000005c8bd53e79d3700020c340b997b35c0012b96a26c2e0000000a24e8000ed566a5c000000004cc9aa7e29000046000278000002c149a9c973800000000a11710004093c9af378704c80005ae4a8199202201789618f072000139fe47e00163abf4f00dd4d0355fc914f42660ec000000002360017884300036c0021a37a334e2a8d10e0000004a1ae000002c900083161a745605fc459f200001c1f14155a000442d500005c0000000015800000000000002a7000458000e20c20000000046eb58d1000000000030000000000000014218d778000005387e0001ba000e90c71aca00c8819000001378d20001654e80e26e000ad000000000b00004a285cf6ab716e0009882b1000000007e00000151000000000b4800000768d480000000000000000001290004d275875000000000000000006e0000bb000000000000009255211c000054b40005f60011f0000001ac00000000001570000003dc408e4000c2ccd80045c6a0000000002cc489fb000000d38000000017a8000da174000000000000000000016800000490000e18003a6a4800000000940001c912c1a8000eb0000d0d580000004000000000000640000007d40016f006095413000005c12780000008c4a06c39676d0e19421c420518000f0000000da00015d2dab1000000000000000000008e000000000000000011a15d46a0000026100800000000416001021444c4000000003d60b4000000000015e0000000081d0003ba0011802019840d4987f1406d41107a1642f8002f21f0b51590840b800000288000000c080051e514778a41ca8cc00000000be000000000000000001206f938800000b10efa051ec000000001d2000000fd022000282542dc2e80000038043d488000009d4001f32c80000000007061800000462970001040000000000000000000242242000f524a5b68e8db89b000aad132c64769300013f0009007314000000000265158000000003082b8d98661800012d0000002a800000090540000000002bc000000004
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x262a01b001e34b332e000000000e0000008925601000000c00a5a740850091ab70000d00180003254bd38432000000094987421911f000800036c400020b0f0e526000916c04004651a0000a000000b8000820000203020408102041810218004a4ae32a2859952671d5254ccb13aa2c32a665499d35194732c4ac9a8ca39962554584420cb12aa2c22a0658a5516015032c4ac8a88a21966151580510ca52b94c321a831a5c0650c941a4ceca928220d2476549411069239aa4a088349dc1525044194ced9928220d2775cc94110692ba864a0883495ca5450731a4ae42a28218d3170151410c652ba4c399243491d54250521c4aa8b088410e2554584320872429ac019281495c85150540c52a8b006418561700c9510c312aa2c221641895915108720c4aa8b08a99064a6358053c8312b22a228e41895954110720a4ae22a2849052574145214828639aa82a241491c55415120c4aa8b08a8906445398743482923a2a228a41895915114520a88e6a88a29044c7359441482923aa8220a41895954110520c1cc829c629060c6414d3048322298c298241a2591300c120d82c298060905257215141c432429ac019221495c85450510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x642a08000906839d9525044182686dd73250441a04835516115120c05641cd5114520824875954110520a04835954110520
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
  | 5 => packedAt s3K5 (24564+((h/267+packedAt s3K5 (21627+(h % 267)*11) 11) % 1058)*11) 11
  | 4 => packedAt s3K4 (32538+((h/260+packedAt s3K4 (29678+(h % 260)*11) 11) % 1371)*11) 11
  | 3 => packedAt s3K3 (2870+((h/18+packedAt s3K3 (2744+(h % 18)*7) 7) % 97)*7) 7
  | 2 => packedAt s3K2 (368+((h/2+packedAt s3K2 (360+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffff07fffff81e1c3fffffc3ffffc07f1ff
  | 1 => 0xf07e1ff83f1fffe01fc78783fc707fe3a4e4f
  | 2 => 0xff801fffc01f0fffe007f803ff80783c38f8c
  | 4 => 0xf00001fffffe00ffffff80003ffff803fc0ff0
  | 5 => 0xfffffe00000000ffffffffffc0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x21004011002000002000888884091088009095
  | 1 => 0x425193221942a89610e434511a4225721a464a
  | 2 => 0xa432d54528e549aaf2205d42ae90561ac38b8c
  | 4 => 0xc0a508885280624d454900043124e0216c0d60
  | 5 => 0x8c6110e63098cf199b2666702008443b76000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeaaaaeaea8888fefeaaaaeaea8888fefeaaaaeaea8888fefeaaaaeaea8888fefeaaaaeaea8888fefeaaaaeaea8888fefeaaaaeaea8888fefeaaaaeaea8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36372
namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffc0f0f87fc3c387fffff870383fe0ff64f
  | 1 => 0xc1f87ff00fffffc03f8f0f03f803ffff32487f
  | 2 => 0xfe007ffff00787ffc00ff003fffc03c1c38f8c
  | 3 => 0x7ffffff807fffff00003fffffc01fc0ff0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x485004601109000c0811111a81289054049645
  | 1 => 0x9424c882a64244c214868a2148112aa912481a
  | 2 => 0x4b5512683544d56440ba849d2580b0d438a8c
  | 3 => 0x2942224808011228a920009224a25010ac0560
  | 5 => 0x3184438ccc6667b3364ccce040c06221fb6000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfeaafeaafc88fc88feaafeaafc88fc88feaafeaafc88fc88feaafeaafc88fc88feaafeaafc88fc88feaafeaafc88fc88feaafeaafc88fc88feaafeaafc88fc88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36372
namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa3185f94230fda0461f8408c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f680987e10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f461087e4c210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd18221f930443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xc5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c837e52907dca520db94a41bea9483ed52906daa520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1243ec42487dc6490fb4c921fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f619
  | 2 => 0xbe4da7d41e83e060460401d93d00012ba620c05103da660008500907e000660ee885280001238e62584d0c49152206000680038e129140a72720692698f4066c0192213ca87ce896024a490620002004392580047a5c8a89f93e044c6f97049e194c50ac3b8318be15a356000580ba1ca5b86a2000002e4129f11fc84cb781b44861c81a5b4901c80087a4e6148de12e29869ca99620a8178b68b44640003b1bd3d25d0530000002293580031c4ac86804166308001320764e0a080000067537a29000594520de41a0009482626c6a10e2534ea480ed13535c5d44426c0000d53b15d00077c5b89f3d413920a0708e001110004620006382705c880998ff354390f1a59402058458bd01c9005b13a3e47302400000c0284b1143c00005a8440000a0148002046801b80022c001061eb358561249083dc758ec07c2545552884d4a85a91a1830800006c811102300260051ea70d0c0da15e670438dc3701e07600c4761fca912611a8cc2e0cf136064000a234603d1e1660cc55caf0004709540005b368381161e14c25c42b86f0da751341630aa5d8c604944a854422522167384a04500049c6c26e3027b00a9cd43c6e46b0f126e000ad99f1ae3e0ac97a4980cd2f8f62320000008e1f28b90b98231a3b4000003802c5020000820011f0003622b8f7a602d03ec2b0714220003a9a1000710058c93ce7e0a318624699c6914a1e04450e8cc29a8acbf80000019c7424a3cc2a00421a21e50c61a633a44fcc909a02e52c8d9ed0124746e8aa3a671417a453365712c1771a2640ab0ca32c144218ab0e0540ff8244107dcc21a928a584370623b67048607d3f43f0119064865f4dd0741ce3dc5e20911e4b41d01d35a160232442344f42590700088d1f9b20065a4cf178044614591930001688f2191e67d06a800390550d2a7237c6980013b1dc020132041200c0c1180006c0b000140100900c1c00c000680000000000070d0090000f00002000340201e120060001301c010040b0300000c2d000160080700000008020082e0a4420500508c00038070100800806058000000200c0200c00000010180209c0001003054010140c02800000020000b04c080801309c00018000000700007000010080001c3d00c0200401004020080c00405048270040200003014020000600c0000016000000141509009000000241d0040600c03044020580101402000070141400401004010083900806000150000000402000450381f0441002c030181202800020080040b000020001a01c1200c01000020000000802058030000001820bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121fe94243bd284877d5090ff2a121de54243efa1a87be4350efea4a1fbd4943b7a92877
  | 3 => 0xd78862f63d01c85d3949dc940ef1f48984b89e37e01cdda0a0002440f0003288d4e117309e0f0681d70ee994cc8bb00000000038224000c40141122b40020b00018c0000036a108000003bc0003591c2609a4fe0003960001a00041e20c308210001406682d3922a4012423fa65d092741c64bcea9473c44f12b0c82423381609d0d40005024e000000410000be6dd3200000000062a164b4000db1793ec404298a32ce62c0026a040248000792fc3040c15f0000d8000000000000009546c0011514f000414001310000000000000038800000000840820000005b0002500000010109029081409a461b62e06594214a07c3423945a0408f88c45e0ac5f8f24e2790f981c3228e92f0730003ac0019a2c82850700000000000000000000ff00027c24cd20590c80001f909344000b599500073c0006c1d445c000003a03f4fd800132000e31b300086c0000024481938000000970699490620008514e000975180e91380a91b8001c20004c2270d2
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xb548c26d62d52309b988548c26d62152309d984548c2756115230da982528c2e96210230bc584408c34e52cc230ae993308c26f62551309b189544c27761551309d185544c2da6090d3097195434c2cc6250d30a7590324c2d5610c930b6980324c23e64145308f590514c26e62145309b588514c2cc624c5309e997404c2da6310130e650c404c2e96210130bc584404c2ba64cc130b398a304c27a60d50309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25f654c0309ed95300c27661d53209d58754c823e6414f208f59053c82766114f209d58453c82ad640cb20b958432c823e64947208f59251c82cc63487209798f548825d63d52209798c548825d63152209d984548827561152208f992538823d6494e20c7992538831d6494e20d6982538835a534c220d394f208823e64951208f994544832d62151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb152424826c65509209b997324832c54cc920ab590324832c540c920b958432482ea600c920cb153214832c5448520b318d21483645148520ce15230482ea628c1209e1953048338544c120f20c930482ce63881209798c540825d63150209b988540827661150209d584540826e62d4c208f990530823d6414c209d98453082756114c209e980530825e63940209758e500826f65480209ed95200826e62d53109b58b54c426f6254f109b18953c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c425f6354b109718d52c42f06050710ec50740c42f16110310ec90440c425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538425e63d4a109758f528423f6454a108f191528423e64951109ed81544423e6515110cd584544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524433454905109d1954144338548c1109e1953044338544c110ce153104425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e6214810ce553400435953d00109e59440043595310010cd55310042796584010d654e10042776544010cd551100427b6544010ae19110043595344010
  | 1 => 0xcb365494432cd552510cb365454432cd551510cb674254432d9109510cb663254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500ca7a6094f419e58253d06ac6250f41cb94b41906ac6250d41ad18543506b66190941ab98a415065e63141419758c505066e62141419b588505075a6314141d658c505073b4314141ce50c505076a6214141da588505073a4214141ce108505073a41141419bd89531066c6254c418fd9541106b860504419dd95411067a60d53319e58354cc66f62553319b18954cc66e62943319b58a50cc66e62d52319b58b548c67b60552319e181548c6d5610ca318fd91508c63c64542319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131d9584524c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319b988540c66d62150319e980540c6796015031cb952520c72d5494831cb951520c72d5454831d354a320c765528c43197d95310c6cc624c4319dd95310c765524c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031d68c9500c7583254031d6cc5500c75931540319e98354c867960d53218f99053c863d6414f219e98053c86796014f219798e50c865d63943218f993538863d64d4e218f990538863d6414e219e98053886796014e21cb953328872e540ca21b958432887c4328c621b9189318872e54c86219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d218f990534863d6414d219e98053486796014d2197994534871e6414d21c7590534874d6214d21d5584534875a6014d21d6580534866e65d0921d314f42486e661d0921d314c424866e658c921d314e324866c654c921d314d3248754538c521f18ca3148674654c521ab992214874c53885219b98b540865e63150219758c540867a60150219e580540863e6414c218f590530866e6214c219d984530867a6014c219e580530866d65cc8219b59432086e5610c8218f992510863d64944219bd9521086cc63484219dd95210863f64540218f191500866f6254f409b18953d026e62947409b58a51d02b86050740ab18943902ae62906408f99741502b86050540d6982531031e5350c40ab189431034e5394840d354e521034e5354840d354d521032f4354840cb50d521032d5290840ae58042103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374354440cd50d51103364254440cd109511037060544408f59641102ae6290440cd54641103355110440cd547401023f6550040cd545401027b6550040c798e54cc31e5450f30b318943cc29d640cb30b558432cc2cc624c7309b98
  | 2 => 0x330000007f35c68800130009113c61b3600000001be9a800252a400000172e8001cc000000000062a70b285095002003444614a001042f800000009d3482ba04b80002f27829020000000c8006780070a2e00000350ee0035ae080000000b300047836002c4b89dcbd2c2000007834c1d8a20038c000000039487318549d6de93600000d0baa92838c280074000878008680099800e2b084aae6110a8a00246830ce639e5e8b04695ab4000da0fe0004a0016680932cf1b08f1c4000f2bb800000000034a001f000000002aca9aaa0a246dba8624800000000000000000e91e8031b20006c491688380000000cd000003a29895466142002ce169a40000000000e380000242010000000000000000007680000160000009c800000000000037366e5800d4800db0000017000000000424b13ecb16c6a1c0000a6b58008a32834800e18008b37865800000000029219abe328000014000000002300000060108d90d819350cc9eee73907d8ba822ba00000d82fe88910c880043800a2b7e0037603800001929400000000ae210611b684b140009c932f20008cb21c600000180106bb1ad38d000000002a2390000ba96000001d000baaf60d0000004e0000000000000000000085b0e0029ed788a001aca8000a70c0002205f00000000ea000000008e95c0007001800002b6000002800000000002680f80000248002000015e001ca001d800000620000000000000e837c1607200000000000008e000aa498b2003040002a3a33a00090ac2f81180000224000000000000000c00008cb1ecb8009b0007d0000000000000001d20000000056673ac0025ecfb8054088898089394c8f800948000014e00000a6b5800000001220000001002000020040901800010000040800800000020080100400000000000000c03004090080001002000010280200c0901c0901807000000040100c0000800004000000100c0001806014090000200806000010000000401004010000000010004000100100400000010000001c0100400000000000300c01000010000100c0000405008020000100c040000000800018010000200001004070000100400000020000201000004000000700406000000040300001000000040000000004060000000c010026e62947439b58a51d0e6e62942439b58a5090f3b4394243da98a5090f696294243ae9824350e3f6550c4397d954310e7a6094f429e58253d0aac6250f429798e5090a5d63942428fd954210a6f65508429e98354cca7960d53328f992518ca3d64946328fd91508ca3c64542329d986544ca7561951329bd89544ca7661d50329d587540ca7a60d50329e583540ca3d6595032cb189540ca3e64150329d984540ca7561150329e980540ca796015032cb553420ca6d6510832b358c420ca5f654c8329bd95320
  | 3 => 0x59000e480000000c48120019000000bc148000803e9f80007a00138b4b70001e600000313465c840001ea6a962419bc003a600000002068d800630000000038000721024d2ded5800a300030800000000000000284378c65a80000338c93b01500045194060005e31c6680000000dd0ce001e4001f205800002fc4a000000000010c5d130778000f3544b8f86eac62e000000484485ed8a5a6d2384e800828000000000000001a6000003b1faa0a60c801a470261f80000000a50b60b09e000fc0026eaf0e6a3a58001d40e884e21583daec1b900259829ea183c0000010a000000c2b438ab29f0142680000176002dc8aaae1e3728d18e028001f000b6800001b85bb6a00298eb800000000000000000000522b000a21e2b9000a420c7b0000000000000071440001e20822e1310aa00000000002763a800000000027e3239a0000000000000f400068480b40000000156000da33000970007f8000006ab52640000000000358000000000062caa14c0afa002c00011600000c18002197e9000000256c5800002d80000000000c9898d01467380000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x3400145994433186903d348809c11500500b38128625b1c001708008000280489515cc4254432a50e4a18a0a0d307150c5050724b1ac4282834c9c64214141a54e5208a0a0d48724c5500c7132a2c219443865916014d21ca2c2b00a690e445398742486a33ac6518a43839905388521a48e4a1aa2205317010951102a8b98c0a8881899895190440b10e4a18809868943588404c348a1ac2202610b5d8540c920c48a8b08649060c5418d2148322318a290a41625d0324c120e10a819260905c1710c93048258bb48220621861915344010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1010a808250d611013090987150324c120d00545c4324c120
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
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
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 829)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s5K2 (182+((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe3ffff03c7c7f0f1c7f1fffc70383fc31f64f
  | 1 => 0x1fc1f8ffc07ffff01f8fe381f803fffcce487f
  | 2 => 0x1ffe00ffff8078ffe00ffc01fffc03830f8f8c
  | 3 => 0xe00000ffffff80fffff00001fffffc03f00ff0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42885011808890030411048d412890a8109645
  | 1 => 0x8414212209302030088621108811295046481a
  | 2 => 0x4884b24498194155200b4824d2580a190b8a8c
  | 3 => 0x12944892040128a5520004924a25022b00560
  | 4 => 0x9131800e326264ec9a4c927000c06043ed6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88feeafc88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36372
namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5007fe5401ff55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52007fd0803fe42007f50803fc42017fcc803fe32017f4c803fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50007fd0001fe40007f50001fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842005ff4c210067f26108017fc308400bff9042005ff8821002ffa4108017fc208400bff8842005fdc4210027f6210802fff65440177fb2a200bff9951001dfcca8802ffd65440177eb2a200bff1951001df8ca88003ff64440017fb222000ff99110005fcc888003fd64440017eb222000ff19110005f8c88802fff5444017ff2a2200bff5511005ff8a88802bff63440157fb1a200aff98d10015fcc68802bfd63440157eb1a200aff18d10015f8c68802bff5344015ff29a200aff54d10057f8a68802bff4344015ff21a200aff50d10057f88688003ff62440017fb122009ff9891000dfcc488003fd62440017eb122009ff1891000df8c48802fff5244013ff292200bff5491004ff8a488003ff4244013ff2122000ff5091004ff8848802bff3244013ff192200aff4c91004ff8648802fff5144009ff28a200bfd9451005ffaa28802ff55144009fe28a2000ffd0510027fc8288003f64144001fea0a2000fd50510027f8828802bff3144009ff18a200aff4c510027f86288027ff2144009ff10a2000ff48510027f8428802fff504400bff282200bff5411002ff8a088003ff404400bff2022000ff5011002ff8808802bff304400bff182200afe8c110057fa608802bf9304400bfe1822009ffc811002ffc4088003fd204400bfe1022004ffc4110027f62088017fe104400bfb0822005ffd941002dfeca08017fe65040077f3282005df9941001cfcca08017fd65040117eb282005df59410004faca08017fc650400b7e3282005ffd901002dfec808017fe64040017f3202005ef990100057cc808017fd64040017eb202005ef590100057ac808017fc640400b7e3202008ffd5010047fca808023fd5404011fe2a02005ffd8c1002dfec608017fe63040057f3182005f798c10015bcc608017fd630400f7eb182005f758c10005bac608017fc630400b7e3182007ffd4c1003ffca60801ffd530400ffe2982007ffd0c1003ffc860801ffd430400ffe2182005ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd62040017eb102005fb58810005dac408017fc620400b7e3102008ffd4810037fca408023fd520400dfe2902000ffd0810037fc8408003fd420400dfe2102007ffcc810037fc640801ffd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802004fe44010
  | 1 => 0x2ff6148001ff30a4000ff58520007f8c290012fc6148027ffa8a4013ff9452009ffaa29004ffc5148001ffa0a4000ff90520007fa8290003fc4148025ff98a4012ff8c520097fa629004bfc3148003ff90a4001fbc852000ffc4290007fd2148001f690a4001ff0852000dfec09004fff504800bff2824013ff5412002ff8a090003ff404800bff2024000ff5012002ff8809004bff304800bff1824012fe8c120097fa609004bf9304800bfe1824001ffc812000ff64090017fe204800bf71024005ff0812002fd84090007f82048009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2011bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc988002fe64c4009feb262000bf59310027f8c988012fc64c4023ffaa62011ff9531008ffaa988047fc54c4009ffb1e2004bfd8f10027fcc78800afe63c4009feb1e2010bf58f10027f8c788012fc63c4021ffa9e2010ff94f10087faa788043fc53c4021ffa1e2010ff90f10087fa8788043fc43c4009ffb162004bfd8b10027fcc588006fe62c4009feb162000bf58b10027f8c588012fc62c4023ffa96200fff94b1008ffaa58803ffc52c4001ffa16200fff90b10007fa858803ffc42c4021ff996200fff8cb10087fa658803ffc32c4009ffa8e2004ff94710027eca388013fd51c4023faa8e2004ff14710027fe8388013fe41c4009fb20e2004ff50710007ea8388013fc41c4009ff98e2004ff8c710027fa6388013fc31c4009ff90e2004ff88710027fa4388013fc21c4023ffa862005ff9431008ffaa188017fc50c4001ffa062005ff90310007fa8188017fc40c4021ff9862005ff8c310087fa6188017fc30c401fff9062005ff88310007fa4188017fc20c400bffb2c2005bfd961002ffccb0800efe658400bfeb2c200ebf5961002ff8cb08016fc658400bffb242005bfd921002ffcc908002fe648400bfeb242000bf5921002ff8c908016fc648401dffaa4200eff95210077faa90803bfc548400bffb1c2005bfd8e1002ffcc70800afe638400bfeb1c200cbf58e1002ff8c708016fc6384019ffa9c200cff94e10067faa708033fc5384019ffa1c200cff90e10067fa8708033fc438400bffb142005bfd8a1002ffcc508006fe628400bfeb142000bf58a1002ff8c508016fc628401dffa94200dff94a10077faa508037fc5284001ffa14200dff90a10007fa8508037fc4284019ff994200dff8ca10067fa6508037fc32840157eb0c200effd4610027fca30803bfd5184009fe28c2000ffd0610027fc8308003fd4184009fe20c200cffcc610027fc6308033fd3184009fe18c200dffc8610027fc4308003fd2184009fe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfea042005ff1021002ffe6108017fe308400bfd1
  | 2 => 0x400bffa862005fbd4310031fe2188005ffd884002ffcc420006fe621000bf73108001bb9884002ffac420002fd621000bf6b108000bb5884002ff8c420016fc6210033ffa908016ff948400cffaa42005bfc5210031ffa108016ff90840007fa8420063fc421002fff9908016ff8c8400bffa642005bfc321000bffb088005ff98440025fcc220017f661100017b3088005ff58440005fac220017f561100017ab088005ff184400cffea220067fe5110033fea888019ff144400c7fe8220003fe4110001fea088018ff104400bffe622005ffe311002ffe9888017ff0c4400b7fe4220003fe2110001fe9088016ff0844002dfcc020017ff501000bff2808005ff5404002ff8a020017ff401000bdfa008005ff9004002ff48020017fd401000bdea008000fe5004002ffe6020017fe301000bfe9808005ff0c04002ffe4020017fc201000bffb2c4005bfd962002ffccb1000efe658800bfeb2c4015bf5962002ff8cb10016fc658800bffb244005bfd922002ffcc910002fe648800bfeb244000bf5922002ff8c910016fc648802bffaa44015ff952200affaa910057fc548800bffb1c4005bfd8e2002ffcc71000afe638800bef31c4002b798e2002ffac710052fd638800beeb1c4000b758e2002ff8c710016fc6388029ffa9c4014ff94e200a7faa710053fc5388029ffa1c4014ff90e200a7fa8710053fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944005ffd862002ffcc310012fe618800bfeb0c4000bf5862002ff8c310057ff518802bff28c4015ff546200aff8a310003ff4188001ff20c4000ff50620007f88310053ff3188029ff18c4014ff4c6200a7f86310007ff2188003ff10c4001ff4862000ff84310016fe608800bffa844005ff9422002ffaa110017fc508800bffa044005ff9022002ffa8110017fc408800bff9844005ff8c22002ff46110017fd3088029fc9844005ff0c22002ffe4110017ef2088003fd9044005ff0822002ff0411004fff65480277fb2a4013ff9952001dfcca9004ffd65480277eb2a4013ff1952001df8ca90003ff64480017fb224000ff99120005fcc890003fd64480017eb224000ff19120005f8c89004fff5448027ff2a24013ff5512009ff8a89004bff63480257fb1a4012ff98d20015fcc69004bfd63480257eb1a4012ff18d20015f8c69004bff5348025ff29a4012ff54d20097f8a69004bff4348025ff21a4012ff50d20097f88690016ff6248003ffa924001ff9492000fdca490007fd5248027f6a924001ff1492000ffe8490007fe4248003f72124001ff50920007da8490007fc4248003ff9924012fbcc92000ffc6490007fd3248003fe1924001fb0c920007fec29000
  | 3 => 0xf2868022ff5434002ff8a1a006bff30d000bff186801aff4c34002ff861a0087ff20d000bfe1068005ffd964002dfecb20017fe65900077f32c8005ff59640105facb20017fc659000b7e32c801cbf59240107fea920083fe5490041feaa48020ff1524002ffec720016ff639000bff31c8002bf98e4002ffac72007efd639000bfe31c8005bf18e400fffea72007ffe539003ffea9c801fff14e400fffe872007fbf439003fff21c801fff50e400ff7a872007ffc439000bffb148005ff98a4000dfcc520017fd62900017eb148005ff18a4002df8c520083ff529003dff2948020ff54a400f7f8a520003ff429003dff2148000ff50a400f7f8852007fff329003dff194801fff4ca400f7f86520017ff619000bff30c8004bf9864002ffac320002fd619000bfe30c8020ffd4640107fca320083fd5190041fe28c8000ffd0640007fc8320003fd4190001fe20c801fffcc6400fffc632007ffd319003ffe18c801effc8640007fc4320003fd219003dfe10c8005bf9824002ffea120017fe509000bfea848005ff1424002ffe8120017bf4090001fda048005ffcc24002ffc6120017fd309000bfe1848005ffc824002ff84120077ff655003b7fb2a8000dfd9540004fecaa0077fe65500077f32a801dff595400edfacaa0077fc65500077e32a801ddf1954001cf8caa0077ff545003bff2a2801def951400effaa8a0077bd545003bfe2a2801cffd8d400e5fec6a0073fe63500057f31a801cff58d400e5fac6a0073fc63500057e31a801cffd4d400e7fca6a0073fd5350039fe29a801cffd0d400e7fc86a0073fd4350039fe21a8000ffd8940005fec4a006ffe62500037f3128000ff589400dff8c4a0006fc625003bffa92801bff949400effaa4a006ffc5250001ffa12801bff90940007fa84a006ffc4250039ff992801bff8c9400e7fa64a006ffc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8004bf185400effea2a0077fe515003bfea8a801dff14540007fe82a0003bf4150001ff20a8000ff505400077a82a0003fc4150039ff98a801cff8c5400e7fa62a0073fc3150037ff90a8000ff88540007fa42a006ffc215003bffa828005ff941400effaa0a0017fc5050001ffa028000fed014002ffc80a0017be4050039ff9828005ff8c1400e7fa60a0017fc3050037ff9028005ff0814002ffeca20016ff651000bff3288003bf9944002efcca2000e7e651000bfeb288019bf5944002efaca200027d651000bfe3288005bf194400d5fcc820067ff5410031ff2a08019ff550400c7f8a820017ff631000b7fb188005ff98c40015fcc620017de63100056f3188005ff58c400bdfac620017dd63100016eb188005ff18c4002df8c62005fff531002fff2988017ff54c400bff8a620063ff431002fdfa188017ff90c
  | 4 => 0x807fc5288403ffa144201ff90a2100ffa8510807fc4288403ff9944201ff8ca2100ffa6510807fc32884097f30c4204ffd4621027fca310813f65188409fea8c4226fd54621027f8a310813ff4188409ff20c4204ff50621027f88310813ff3188409ff18c4204fd8c621027fa6310897f53188409fe18c4204ffc8621027de4310807f72188409fe10c4204fd08621027fec110813fe608840b7f3044204ff58221005fac110813fc608844dffa844226ff94221137faa11089bfc508844bff9844225ff8c22112ffa6110897fc3088403ff9044201ff08221127feca90892ff6548449ff32a4203bf99521127faca90892fd6548449fe32a4203bf19521007fec890802ff6448401ff3224200bf99121007fac890802fd6448401fe3224200bf19121127fea890893fe5448449feaa24224ff1512111ffec69088eff6348401efb1a4200b7d8d2111ffcc69080afe6348447feb1a4223bf58d2111ff8c69080afc6348447ee31a4202b718d2111ffea69088ffe5348447fea9a4223ff14d2111ffe869088ffe4348447fea1a4223ff10d21025fec490807ff5248403ff2924201fb9492100ffaa490893ed5248403fe2924201ffd0921007de8490807fe4248403fea124201ff1092100fd88490807ff3248403ff1924201fb8c92100ffa649088fed3248403fe1924201bfd8521127fea290813fe5148449fb28a4224ff54521127eaa290813fc5148401ffa0a4204ff90521007fa8290813fc4148447ff98a4204ff8c52111fec629088ffd3148447fa98a4204ff0c52100ffe4290807f72148409ff10a4204fb88521027f84290813ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff1812102df8c090893ff5048449ff2824224ff54121127f8a09088fff3048447ff1824223ff4c12111ff86090807ff2048403f79024201ff081210c7fecba008aff65d0045ff32e8003bf99740117facba008afd65d0031fe32e8003bf19740117fea9a0063fe54d0045df2a68022ff553401177aa9a0063fc54d0031ffb1e801abfd8f400d7fcc7a000afe63d0035feb1e801abf58f400c7f8c7a000afc63d0035ffa9e801aff94f400d7faa7a006bfc53d0031ffa1e801aff90f400d7fa87a0063fc43d0031ffb168021ff98b4000dfcc5a0003fd62d00017eb168018ff18b4000df8c5a008bff52d0043ff2968022ff54b4010ff8a5a0063ff42d0043ff2168000ff50b400c7f885a006bff32d0043ff196801aff4cb4010ff865a0063ff61d0001ff30e8004bf98740007fac3a0002fd61d0031fe30e8022ffd4740117fca3a008bfd51d0045fe28e8018ffd07400077e83a0003fe41d0001fea0e8000ef507400c7f883a006bff31d0035ff18e801aff4c7400d7f863a0087ff21d0001ff10e8000ff4874010ff843a008bff50d000bf
  | 5 => 0xc641027fa6320813fc3190409ff90c8204ff08641027fec120813fe609040b7f3048204ff58241005fac120813fc6090461ffa848230ff94241187faa1208c3fc509045fff984822fff8c24117ffa61208bffc309045dff904822eff0824116ffecaa08b6ff655045bff32a8203bf9954116ffacaa08b6fd655045bfe32a8203bf1954116ffea8a08b7fe545045bfeaa2822dff15141167fec6a08b2ff6350459ff31a8202bf98d41167fac6a08b2fd6350459fe31a8202bf18d41167fea6a08b3fe5350459fea9a822cff14d41167fe86a08b3bf4350459ff21a822cff50d411677a86a08b3fc4350401ffb128200bfd894115ffcc4a0806fe6250401feb12822bff1894100df8c4a08b7ff5250457ff292822dff5494115ff8a4a0803ff4250457ff2128200ff5094115ff884a08b3ff3250457ff192822cff4c94115ff864a08b7ff5150409ff28a822dff54541027f8a2a0803ff4150401fba0a8204ff905410277c82a08b3ff3150409ff18a822cff4c541027f862a08afff2150409fe10a8200ffd8141005fec0a0803fe6050401feb028200ff1814102df8c0a08b7ff505045bff282822dff5414116ff8a0a08b3ff3050459ff182822cff4c141167f860a08afff2050457fe1028204ffd9441025feca20813fe65104077f3288204ff5944114dfaca20813fc65104097e328822abf9904114ffea820863fe5410453feaa08218ff15041027fec620812ff6310409ff3188202bf98c41027fac6208a2fd6310409fe3188204bf18c41147fea6208a3fe5310451fea988228ff14c410c7fe86208a3fe4310451fea188218ff10c41027fec420813fe62104037f3108204ff58841005fac420813fc62104097e3108229ffd484113ffca4208a7fd521044ffe2908218ffd084113ffc8420803fd4210431fe2108228ffcc84113ffc64208a3fd321044ffe1908204bf98441027fea220813fe5110409fea888204ff14441027fe8220813bf4110409ff2088204fd90441027fa8220813bd4110401faa088204ffcc441027fc6220813fd3110409fe1888204ffc8441027f84220813ff6010409ff3008205bf98041027fac020802fd6010409fe3008229ffd404114ffca0208a7fd5010453fe2808228ffcc041147fc60208a3fd3010451fe1808227ffc804113ff84020813ff65884097fb2c4204ff9962101dfccb10813fd658844d7eb2c4204ff19621025f8cb10813ff64884097fb244204ff99221005fcc910813fd64884017eb244204ff19221025f8c91089bff548844dff2a44226ff55221137f8a910813ff63884097fb1c4204ff98e21015fcc710813fd638844b7eb1c4204ff18e21025f8c710897ff538844bff29c4225ff54e2112ff8a710897ff438844bff21c4225ff50e2112ff88710806fd6288403ffa944201ff94a2100ffaa510
  | 6 => 0x3fe1068434ffd95421a5fecaa10d3fe65508077f32a8434ff595421a5facaa10d3fc65508077e32a8401bfd91421a7fea8a10d3fe5450869feaa28434ff1514219ffec6a10ceff6350867ff31a8402bf98d4219ffac6a10cefd6350867fe31a8402bf18d4219ffea6a10cffe5350867fea9a8433ff14d4219ffe86a10cfbf4350867ff21a8433ff50d4219f7a86a10cffc43508037fb128401ffd494200ffca4a1007fd5250803fe2928401ffd0942007de84a1007fe4250803df2128401ff1094200f7884a1007ec4250803ff9928401ff8c94200ffa64a1007fc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8404bf185421a7fea2a10d3fe5150869fea8a8434ff1454219ffe62a10cffe3150867fe98a8433ff0c54200ffe42a1007fc2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028405bf181421a7fea0a10d3fe5050869fea828434ff1414219ffe60a10cffe3050867fe9828433ff0c14200ffe40a1007ef2050803fe1028418ffd9741195fecba08cbfe65d04077f32e8232ff59741195facba0863fc65d04077e32e8232ffd53410c7fca9a08cbfd54d0431fe2a68218ffd8f41155fec7a08abfe63d04057f31e822aff58f41155fac7a0863fc63d04057e31e822affd4f41157fca7a08abfd53d0455fe29e8218ffd0f411577e87a08abfe43d0455fea1e822aef50f410c7f887a0863ff62d0463ff3168201bf98b41007fac5a0802fd62d0431fe3168201bf18b41197fea5a08c7fe52d0465fea968231ff14b410c7fe85a08c7fe42d0401fea168218ff10b41157fe65a08c7fe32d0455fe9968231ff0cb41197fea3a0813fe51d0465fea8e8204ff14741157fe63a0813fe31d0455fe98e8204ff0c74118ffe43a0813fc21d0431ffb068200ff9834102dfcc1a0803fd60d04017eb068218ff18341197fea1a08cbfe50d0465fea868232ff14341157fe61a08abfe30d0455fe986822aff0c34118ffe41a08c7fc20d0409ffb2c8204bfd9641027fccb2080efe6590409bf32c82039f99641027facb208c2fd6590409beb2c82009f59641027f8cb20812fc65904597eb248230ffd5241187fca9208c3fd5490461fe2a48204ffd8e41025fec720813fe63904057f31c8204ff58e4117dfac720813fc63904097e31c822fffd4e4117ffca7208bffd539045ffe29c822fffd0e4117ffc87208bffd439045ffe21c8204ffd8a41027fcc520806fe6290409f73148201bb98a41027fac520802fd6290409f6b148200bb58a41027f8c520812fc6290461ffa94822eff94a41187faa5208bbfc5290401ffa14822eff90a41007fa85208bbfc429045fff994822eff8ca4117ffa65208bbfc32904097f30c8204ffd4641027fca320813fd5190409fe28c8204ffd06410277e8320803f74190409ff98c8204ff8
  | 7 => 0x400200200403001e02400200000000002000a00000000601200000001e00601003400c00000201a03601400000004400400000a00005000400e00000000800401400001603200000200000601000000400c00200402202c00200800000802a03800200001200000c00000803a00c00200200800400800201000000600c01e01800c04000800a00a00000000001400001200000401603800800c00c00601400000800000000400800001000400401401206200000a00200600202c02601c00401e00e00200600000200802c01400200000a00a00000200000000008a00600000201200400000e00a03c00200c01400a00402000000200000600000400201200c00600001802202001000200400a00400200200000200401000200000200000800402002200801200c01200e0140a000800401400200000200000400400c00800400600003c00201000400c00e00600001002001201000c00400a00402000000200200200c00000201201802200202603600400000a00000000000400000a0000000000a000402600803c00a00000201402c00800200204803c01a00c00001400200406c00601201800001a00400a00e00200600200000002a04600000200800000201e08404604400e02400e00000a00003203600a00000800000400200000a00a00601002400605c01200800200400200000200000803200600401400200001800400800000806a02000c00403600e00000200000003e00202000c00600003e00200000c00600400600a00201a00000000e03800c00000000000800001000200000e01800400000000c00e00401000000200000a00200400402600000200201401200401c00001000200602801200600600000002600e01e00201800001200600203c00200200200005204400401400c02018ffd97421b5fecba10dbfe65d08077f32e8436ff597421b5facba1063fc65d08077e32e8401bf993421b7fea9a1063fe54d086dfeaa68418ff153420c7fec7a10d6ff63d086bff31e8402bf98f421affac7a10d6fd63d0831fe31e8402bf18f421affea7a10d7fe53d086bfea9e8435ff14f420c7fe87a10d7bf43d086bff21e8435ff50f421af7a87a1063fc43d08037eb168401ffd4b4200ffca5a1007fd52d0803fe2968401ff90b4200f7c85a1007ee42d0803fe2168401ef10b4200ffe65a10d7ef32d0803ff1968401ff4cb4200ff865a1007ec32d0831ffb0e8400ff98742025fcc3a1003fd61d08017eb0e8418ff187421b7fea3a10dbfe51d086dfea8e8436ff147421affe63a10d7fe31d086bfe98e8435ff0c74200ffe43a1007ef21d0803fe10e8418ffd8342007fcc1a1016fe60d0801feb068400bf583420c7f8c1a10dbff50d086dff2868436ff543421b7f8a1a10d7ff30d086bff1868435ff4c3421aff861a1007ff20d080
  | 8 => 0xcb880002a4b080007e40000000000014749d00006200001f000184c324ba800000062caf400086c000f95400314ae191000014400000000000189d2e86580002400000004c400136036075d3c09010d1880955439804498000f3c1800000000000016d4000000000fd00002bc0013b95d0000f65824e10ab8001888000e3c00078547d5b035d7ad91c128c78afd74d5d877844d3c559124c4951257a81756b11c57158b0e5cdb80000013040000000016f47c0000000001730d79428c281fc8d5598f040015640017740000000000000013a000000000024c0000006450f000010d240ee096529d298da4ec087484800120885d7900002fccdd8980002b90291ece7c000000000f30200000a300011907dd1640018540002980008ecdc089476c1a00000000016606c57c00011586f400000166d698edcf58f340012840000003300000008cc3c80009f54489758841996dc7204b98ac47c650000d751186dc6ec87136800185d038000bbc0010e80000c0a3c0019197852c40018480016041e4000208c4cd24c483c0f880005b1798facd44f400004107e81f400040c0012883942585fc9211454a800000000042435982c9040000000000000000000000000000000011e400000000175454c65d1998c50700004a8000134a4152000128d2800000000000e0000000f4c7883f80000000000013993240014080000019253ad6c926446c1dc5d800185800000190d87cf1ce74ac057400102c43cad4d095e41ad0000000013cd338f9c1c43a072d658014724a4d46d61c2d0e840001d80000003fc00063c908dad654f600015c98080000000013e8a88000000000f7000152c000fecc3c0001480000000000010d8000000a60000000000000090c0000000000100c9f00010680000018f83f44016400003200000a954c0003c503d308001340000000000000000000000000000000000bdc0000000000019211dd44c00000110d53512c0000005cc3d9684178f98fa06240a0460000d3c00000000098d5752bc00006000070cc300000007a0001644a140017797fc9100000019700017c8000c0892d1c824507436cf2564804d6b538c301505678bcd7a40007153e50d59401156fcb4ccc4700000540c1823963c09ce9000000000000055cba40000018f0cf0000e250a925c07091d2744802944a4000f6916c2102911b400162400000000000013c00000c01400000600200000000400001002a01800201401e00a00000400a01000400000200600800200a00000201400a00200200000800201000e00406c00600000c00e02402600200200000600401600401400e01a00000800a02a01801a00600600402402200801400000000800600402600200600e00000a00600a00200000000400001c00400000802e00200006000000200200a00a01c00000e0
  | 9 => 0x26017000172c000f900010ad1510bc7983a50152587f914c000aa00b50912e08e9758ce4d846d93582e195868c390cb971940c6e93785308454680005ecaa48f828993cdbd62066c8c9634448d1ca700e47fcc5c3481656d8dc40011395bc3e12f08a01080040001b920d7444306c12695583b452458077cd146711c0cb057c4fd6a4735048000c845d4d111840b83a84c97d8000001160be970c3bc00000000045434c0000013280016080004bc0000000000000000013f800000000000123800000000111513c7e00bd2d80b12a40015e00d88045690551d0aeccfc0800002b06557cc0ec5ad695201954d2c6317807f06792ad79d0fd14069400193893587162d1342f80954c89b56103e581d0594acd410cc2ec2a8e9d3901903dc3987ccab171c664000efc790f840004acb7d73cfa456d6658c98d96e127cd003196a0328000c1d618629441588000001230a2c8649acb513d8639210564a20f08cb4fd4980a1c528e3950c2552cc948570bb85a4bf8270d048dc3b8d98cf8c454c4acd5c4011510648bb045015d24548d4708bcb4400037c488c58000000000000f38000b1c59ceec000604bac5497b8000000a394a4cc8af0a08000b7504c0011a479d6287516ec3ac21d430cd4000c115e8000000f1133c0000014f820ced0000e04da0000b988f43f1581728150a5d34430c0000015499057202cd45cebcfe12c11b04707a800169c000464cd822cdf97e41009e0268a0c1c0e64248e616140a5960dd039c44492817c3b008cbd85f15dcd88354db4220388000001424ce94fc000fd88fd80122509593531c374a04a108402341cd05c2d90c8b9c0c49180000291089b0ad17b00006bd0b80000011295f54f41250c1450e4d529500780d70a49300838bfc0e9638b481682e49c5254ba0fbd8b9148b9400089d4146b4a8400080d2a089845861d18c94400121c000e8d51c7d00014d84380006417006a00009ec000ef55ec73026453c5585f9498680b6569003160d570000e50728000001530cc0d48000cec2155a476595d7f47c53e016170888419cc2d2f918800136cc605799301944d509cab58d0d0d2b48ace542dc0f16b8380708e48f456e51f4000231394b84dfc000000a911a98140000018fc000c0400000158d7b40003cd67c4791fc0081f80017ec2d4000384adc888e18a9800153cc248e0741444000344000eb4d200004151940000000000015fc00000132c0000000004dce358dc224000880000000c680009bc71000000088c0007d57d5890d8d3d441c5f53898c027546083d3356c0000001350000f6d3d00016706340000dc5c8ed83689e87189f8000850ea8a657615a870464c6cc0002198756c4f2c6e46b8bc838c1d02ac7b02294d12d47b8a1894c2c94e8204d302f4ff83793180013bd65c000000aa8b5d5093f442
  | 10 => 0x31021174a6d63168c000ccd0a478cc89488500428000b289cc000e154044841e908101800107d6500ac0000015cd8656aca350b57240009a155508c000e40b194e08607381c8d59928fa8be45dd4b86e04c0ca97e899451ca78b6d4203041855680589a85c0a9c110ddc01806c12d37096c4e4f80000044b380015b8589040000c70c214c1944db000084c0011e08a5560000000b2c000b410e08d95d56696a85113c8fe9168ef8000001314bf0c9c490f480000018340000000016d0dcc879968000000ee40000000002a0000cf4e9856031c6c98787a515d860ec588c0007618ec9c8e20e8185048d8e81049846f93dc0009a4140c50d60ded4cca44c8d3214645b4ed4f0c0005057c54dcb691b851481c25026cde04f0d4cca1490b58ae88f01a9024df5524f14ee8000000ea4b20c74610809034000ac428cf8d8d40001e00000008586908b800000000000000000003cb3c998a7400101cce12c895d3fd4bd59482c52d228000a5108555c67cbf59000898cc00148447474c1545a8c0c0f5964040eb9818a289608188212fd5f06d536519cbed1048357a0b04c540d0d395c08c539ce1c6a8000e0c000a017705d01ec940000420dd40007700013b0000b70698b316f10054f016cc4143cac83092b86b18e00011540012494100007580004680009880013f12916f860d9518b4a68e7899cb904e9180df189402c00097000092557c45ccbc0011bd330ea00483353754944415505385e94b578cdc88542f0001764d80b2542c8100000340004ec001578594b341b4be0000b0c585098ef134c000000000000de4b10d191d80000017bc6d00018f46849dc00186c33d1cd0a135cf513a8000000000d6d110a55518000e448307f45e537c00000000000002575090cbd0001544fb0f7d0448c0188fe4e958119495f84d80d4404000dd8130de94e5384000d950600007ac6acc645a141d6887b46684f4bd5794020c7c60177c000824f747540000005980001184e1828c6c0018a0bc0000000544f218a818cfdd2ec000eb0000d9c000000f0087d8e4c3800000000081469ce300009b926176caad17031156d2780000000018680017380017340008697116e8968b80a253a48b46fc9d80000015848295a04d0000fc0000800000749354e894a164cb54c14ff56018bd9097d0914979514e70351010a8000058d22c05c68975c4cc6a4a8c7ec7744a1538bb40018380000006740017485bd740000000000d540013816740000000011ac7bd94d2057dd418fc4950a94084158660ad8e092d10500002e98a53483ec0000000009580cc3d414d26c49c29d4788a93ecbc40f8af8e2d25183093d2342c4b14ec91a0fc910061807c4b0fb80008d0e68d654800c8050000f798412dc1bc01d06523c73d0c57f80fc00c0013110dd3b4b010f96806149e4000
  | 11 => 0x9380641d52e5009120e6d294f191f00780000000000000000010e41210780000000000005081a4000c94c34000000794000001704f55214d7d220000ecd0f580d7e027ce008b15ad178c9060983d6bc4f8a58fb596ce58c8000000000106c0000005b9271434da82c0554d51089844fcd2f4c985184b47443382b51e8534cd00011f8000000ae4e296cc59000130c098ca43d0d900003e8000f280000552a8f5c00050c280138cacffc9c182034076949c5e17685207c89fcd685c4408a7c364b7917c9d432c000d5d11d2180008900000000000010b14d40012b00002782854ec0000740008e592c418000b6178800023c000000eac00011d540b8c4340015b471c000d280381b0000990000000ff0931914abc0000011d425c0010ec7d959d454d340000000006f14b17f006855145837097d0311
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006de4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002ede5058c1002edd5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ede1058c1002eda1058c1002edd1058c10026d91058c1002edc1058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff74588100c4fc7458810004ff7358810014fe7358810004fd7358810014fc735881002cff725881002eef7258810006ef5258810036ee5258810006ed5258810036ec5258810036ee4258810036ec4258810006ef3258810036ee3258810006ed3258810036ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec215881002cff705881002cfe705881002cfd705881002cfc705881002eee205881002eec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002eee505881002eed505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002eee105881002eed105881002eec10588100c4ff76d081002cfe76d0810004fd76d081002cfc76d08101b67e65d08100067d65d08100c6be64d0810006bd64d08101aede63d0810006dd63d081000eee62d0810006ed62d0810004ff765081002cfe7650810004fd765081002cfc76508101a67e65508100067d6550810006be6450810006bd645081019ede6350810006dd635081000eee6250810006ed6250810
  | 1 => 0x901002cfe709901002cfc709901002ebe409901002ebc40990100c6bf7599010006be7599010006bd75990100c6bc75990100c6bf7399010006be7399010006bd73990100c6bc7399010006bf5399010006be5399010006bd5399010006bc53990100c6bf7299010006be7299010006bd72990100c6bc7299010006bf5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bd3299010006bc3299010026bf7199010026be7199010026bd7199010026bc7199010026bf5199010026be5199010026bd5199010026bc5199010026bf3199010026be3199010026bd3199010026bc3199010026bf2199010026be2199010026bd2199010026bc219901002ebf709901002ebe709901002ebd709901002ebc709901002ebf509901002ebe509901002ebd509901002ebc509901002ebf309901002ebe309901002ebd309901002ebc309901002ebf209901002ebe209901002ebd209901002ebc209901002ebf109901002ebe109901002ebd109901002ebc1099010004ff755901001cfe7559010004fd755901001cfc755901002cff745901002ebf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff7359010014fe7359010004fd7359010014fc7359010006bf4359010006be4359010006bd4359010006bc4359010004ff725901000cfe725901000cfc7259010006be4259010006bc4259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc415901002cff705901002cfe705901002cfd705901002cfc705901002ebe405901002ebc405901002ef7105901002ef51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002ebe505901002ebd505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002eb7105901002ebe105901002ebd105901002eb5105901002ebc1059010006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006d
  | 2 => 0x4ff7650910004fe7650910004fd7650910004fc765091002cfe76d0510006bf64d05100c6bc64d051002dfa70d0510005f970d0510005f67690510026f67690510025f775905100277675905101ddf575905100277575905100057575905101d5f574905100c6f664905100c6f46490510027e67290510027e5729051002df6709051002df47090510026f76090510027f360905101cff230905101cff1309051002cfc7650510006bf6450510006bc6450510027b44150510005fb705051002df8705051002df47650510006f4765051002cf476505101c5f775505101c5f57550510025f77450510027b77450510007b764505100c6f664505100c6f46450510007b464505101bfb743505101bfb54350510007f3705051002df6705051002df47050510007f07050510026f76050510027f360505101bff230505101bff1305051002cfc7648510005df7348510055dc7348510006ef624851000eec6248510005fb704851002df87048510024fe76d0110006bf64d01100c6bc64d0110025f671d0110005f571d0110007b541d01100c4ff7650110004fd7650110024fc76501100057f755011005d7c7550110006bf6450110006bc6450110005f77150110025f47150110007b5415011000cff764811004cfd7648110024fc7648110006ef624811000eec6248110005f77148110025f471481100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067e42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941002e7f705941002e7e705941002e7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e77105941002e7e105941002e7d105941002e75105941002e7c10594100c4ff759901001cfe7599010004fd75990100c4fc759901002cfe749901002ebe7499010006bf54990100c6be5499010006bd54990100c6bc54990100c4ff7399010014fe7399010004fd7399010014fc73990100c6bf4399010006be4399010006bd43990100c6bc439901000cfe7299010004fd729901000cfc7299010006be42990100c6bc4299010024fe7199010024fc7199010026be4199010026bc419
  | 3 => 0xe6250a10006ed6250a100c6be64d0610006bd64d061002dfa70d0610005f970d0610006be6450610006bd6450610005fb705061002df8705061000cff764861002cfc7648610005df7348610065dc734861000eee6248610006ed6248610027e42148610005fb704861002df87048610004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110006bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d9110006bf43d9110006bd43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d9110006bf64991100c4ff759911001cfe7599110004fd75991100c4fc75991100c4fe74991100c4ff7399110014fe7399110004fd7399110014fc739911000cfe7299110004fd729911000cfc7299110004fd71991100c6f57199110004fd70991100c6f970991100057f755911005d7c7559110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110014fe7359110004fd7359110014fc7359110004ff725911000cfe725911000cfc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe7619110006bd64191100c4ff751911001cfe7519110004fd75191100c4fc75191100c6be7419110006bf54191100c6bc54191100c4ff7319110014fe7319110004fd7319110014fc73191100c6bf4319110006bd431911000cfe7219110004fd721911000cfc7219110006be42191100c6bc4219110024fe71191100c6f57119110024fc711911002cfe701911002cfc701911000cfe76d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d89100c4fe74d8910004fd74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910024fe71d891002cfd71d8910024fc71d8910006f651d8910006f551d891004eef21d891002cfe70d8910024fd70d891002cfc70d8910006fa30d8910006f930d891004eef20d89100057f755891005d7c7558910005bf7458910005bc7458910005df7358910055dc735891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf74589100c4fc7458910006bc7458910004bc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc735891004cff7258910006ef725891004eee5258910006ed525891006cff7158910006f77158910006f65158910006f5515891007cff7058910006fb7058910006fa3058910006f930589100c4ff76d0910004fe76d0910004fd76d09100c4fc76d0910025f671d0910005f571d0910
  | 4 => 0x9310014fe7399310004fd7399310014fc73993100c6bf4399310006bd439931000cfe7299310004fd729931000cfc729931002cfe7199310026f6719931002cf67199310026be4199310026f64199310026bc4199310004ff755931001cfe7559310004fd755931001cfc7559310026bf7459310004ff7359310014fe7359310004fd7359310014fc7359310006bf4359310006bd4359310004ff725931000cfe725931000cfc725931002cfc7159310026be4159310026bc4159310004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b100c4fc7458b10004ff7358b10006df7358b10004df7358b10014fe7358b10004fd7358b10014fc7358b10006dc7358b10014dc7358b10026ef7258b1007eee5258b10006ed5258b1007eec4258b1007eee3258b10006ed3258b1002cfc7158b10026f65158b10006f55158b10026ee2158b10026ec2158b1007eef2058b100c4ff76d0b10024fe76d0b10004fd76d0b10024fc76d0b1000eee62d0b10006ed62d0b10025f671d0b10005f571d0b10004ff7650b10024fe7650b10004fd7650b10024fc7650b10025f77650710006f776507101edf775507101edf57550710027b77450710027b764507100c6f66450710026f46450710027b464507101e7b743507101e7b5435071002df6705071002df470507100c6be64d0310006bd64d0310025f671d0310005f571d0310007b541d03100057f755031008d7c7550310006be6450310006bd6450310005f77150310025f47150310007b5415031000cff7648310024fc764831000eee6248310006ed6248310005f77148310025f471483100c4ff759921001cfe7599210004fd75992100c4fc759921002ebe74992100c6be5499210006bd54992100c4ff7399210014fe7399210004fd7399210014fc739921000cfe7299210004fd729921000cfc729921002cfe709921002ebe409921002ebc4099210004ff75592100067f75592100047f755921001cfe7559210004fd755921001cfc75592100067c755921001c7c755921002ebf7459210006be5459210006bd5459210004ff7359210014fe7359210004fd7359210014fc7359210004ff725921000cfe725921000cfc725921002cfc705921002ebe405921002ebc405921002ef7105921002ef51059210004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a100c4fc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a1002eef7258a1006eee5258a10006ed5258a1006eee4258a10006ef3258a1006eec3258a1006eef2158a1002cfc7058a1002efa3058a10006f93058a1002eee2058a1002eec2058a100c4ff76d0a1002cfe76d0a10004fd76d0a1002cfc76d0a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a1000ee
  | 5 => 0x10cff7059120006fb70591200f4fe7619120006bd64191200c4ff751912001cfe7519120004fd75191200c4fc75191200c6be7419120006bf54191200c6bc54191200c4ff7319120014fe7319120004fd7319120014fc73191200c6bf4319120006bd431912002cff721912000cfe721912002cfd72191200c6ed721912000cfc72191200c6bf42191200c6ee42191200b6bd4219120006ef32191200b6ec3219120024fe7119120004fd71191200b6ef211912002dec7650920006ec765092002cec7650920215ef7550920215ed755092000def745092000faf7450920007af64509200c6ee64509200c6ec6450920007ac6450920095ee7350920095ec735092020faf435092020fad4350920005ef7150920007eb705092002dee705092002dec7050920007e8705092000eef605092000feb605092020fea305092020fe93050920004ff75d852001cfe75d8520004fd75d852001cfc75d85200c4fe74d8520004fd74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d852002cfd72d852006eee52d8520006ed52d852006ef621d852006ef521d852002cfe70d852002cfc70d8520006fa30d8520006f930d8520006f7619852004df970985200057f755852009d7c7558520005bf7458520005bc7458520005df7358520095dc735852007dfb705852009d7e75185200057d7518520026f66118520006f56118520004fe76d0520004fd76d05200c4fc76d052000dee72d0520005ed72d0520004fe7690520004fd7690520024fc769052009d7e75905200057d7590520006bf6490520006bc649052000dee7290520005ed7290520004ff7650520004fe7650520004fc765052000dee7250520004fe7610520004fd7610520024fc7610520006bf64105200c6bc641052000dee7210520005ed721052002dfa7010520005f9701052002cec7648520205ef7548520205ed75485201feef65485201feed6548520005ef7448520005ed7448520006ee6448520006ec6448520007cf7348520095ee7348520095ec73485201f7cc7348520095cc73485201f6ef63485201f6ed634852000def714852000fe77148520007e76148520026ee6148520026ec6148520007e46148520026e461485201ffe651485201ffe551485201f7e631485201f7e53148520007eb704852002dee704852002dec7048520007e8704852000eef604852000feb60485201f7ea30485201f7e9304852000cfe76d012000cfc76d0120006bf64d01200c6bc64d012000dee72d0120005ed72d01200c4ff765012000cfe76501200dcfd765012000cfc76501200057f755012009d7c7550120006bf6450120006bc6450120005ef725012000dec725012002fb840501200c4ff759931001cfe7599310004fd75993100c4fc7599310026be74993100c4ff739
  | 6 => 0xd7558e20006dc7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e2021edf7258e2021ede7258e2021edd7258e2021edc7258e2021edf5258e2021ede5258e2021edd5258e2021edc5258e2021edf4258e2021ede4258e2021edd4258e2021edc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006de5158e20006dd5158e20006dc5158e2021edf2158e2021ede2158e2021edd2158e2021edc2158e2002edf7058e2002ede7058e2002edd7058e2002edc7058e2002edf5058e2002ede5058e2002edd5058e2002edc5058e2002edf4058e2002ede4058e2002edd4058e2002edc4058e2002edf2058e2002ede2058e2002edd2058e2002edc2058e2002edf1058e2002ede1058e2002edd1058e2002edc1058e20004ff755862001cfe7558620004fd755862001cfc7558620004ff74586200c4fc7458620004ff7358620014fe7358620004fd7358620014fc735862002ef77158620006f65158620006f5515862004ef6215862004ef5215862002cff705862002cfd705862002cfc705862002efa3058620006f9305862002eef205862002eed205862002ef6105862002ef410586200c4ff76d062002cfe76d0620004fd76d06200c6be64d0620006bd64d0620156de63d0620006dd63d0620024ff769062002cfe7690620004fd76906200ad7e75906200057d759062017ede6390620006dd639062000dee7290620005ed7290620026f66190620006f56190620004ff7650620004fd765062002cfc7650620006be6450620006bd6450620166de6350620006dd6350620026f66150620006f56150620024ff761062002cfe7610620004fd7610620146de6310620006dd631062002dfa7010620005f97010620004ff75d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120006bc54d9120004ff73d9120014fe73d9120004fd73d9120014fc73d9120006bf43d9120006bd43d912002cff72d912002cfd72d91200f6bf42d91200f6bd42d9120024fe71d9120004fd71d9120006bf64991200ddf970991200c4ff759912001cfe7599120004fd75991200c4fc75991200c4fe74991200c4ff7399120014fe7399120004fd7399120014fc739912010cfd72991200c6ed72991200c6ee4299120006ef329912010eec3299120024fe7199120004fd719912010eef21991200dcfd70991200c6f970991200057f755912009d7c755912010dfb7059120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120014fe7359120004fd7359120014fc73591200dcff7259120006ef7259120004ff7159120024fc7159120
  | 7 => 0x8440006f67558440006f57558440006f475584400c6f67458440006f754584400c6f65458440006f554584400c6f45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006f55358440006f453584400c6f74358440006b74358440006f64358440006f54358440006b543584400c6f44358440006f77258440006f67258440006f57258440006f47258440006f75258440006f65258440006f55258440006f452584400c6f74258440006f64258440006f542584400c6f44258440006f73258440006f63258440006f53258440006f4325844002ef7705844002ef6705844002ef4705844002ef7505844002ef6505844002ef5505844002ef4505844002ef7405844002eb7405844002ef6405844002ef5405844002eb5405844002ef4405844002ef7305844002ef6305844002ef5305844002ef4305844002ef7205844002ef6205844002ef5205844002ef42058440004fd76904400cd7e75904400057d75904401867e65904400067d659044017ede6390440006dd63904400b5ee7290440005ed7290440176ee6290440006ed6290440026f66190440006f56190440004ff765044016e7e65504400067d6550440236be6450440166de6350440006dd635044015eee6250440006ed6250440026f66150440024ff768844002cfe7688440004fd76884401367e65884400067d658844012ede6388440006dd638844000eee6288440006ed6288440026f66188440006f56188440004ff7648440004fd764844002cfc76484401267e65484400067d6548440005bf74484400c5bc7448440005df73484400bddc734844011ede6348440006dd634844000eee6248440006ed6248440026f66148440006f5614844002dfb7650040006fb7650040004fb76500400077b755004022f78755004002f7a655004002f79655004002dfb745004002fbb74500400c6fa645004002fba645004002fda635004002fd963500400c7bb4350040227b9435004002fea625004002fe962500400c7bb4250040007b9425004002ff2615004002ff161500400c4ff759922001cfe7599220004fd75992200c4fc759922002ebe74992200c6be5499220006bd54992200c4ff7399220014fe7399220004fd7399220014fc73992200c6bf429922010ebd4299220024fe7199220004fd719922002cfe709922002cfc709922002ebe409922002ebc4099220004ff755922001cfe7559220004fd755922001cfc755922002ebf7459220006be5459220006bd5459220004ff7359220014fe7359220004fd7359220014fc73592200debf42592200debd4259220004ff7159220024fc715922002cfe705922002cfc705922002ebe405922002ebc405922002eef205922002eed2059220006df7558e20006de7558e20006d
  | 8 => 0x6bf4358840006bd435884002eef7258840006ef52588400b6ee5258840006ed52588400b6ec52588400c6ef42588400c6ec4258840006ef32588400b6ee3258840006ed32588400b6ec3258840004ff7158840024fc71588400b6ef21588400b6ec215884002cfc705884002eee205884002eec2058840006ef7558840006ee7558840006ed7558840006ec75588400b6ef74588400c6ee7458840006ef54588400c6ee5458840006ed54588400c6ec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec53588400c6ef4358840006af4358840006ee4358840006ed4358840006ad43588400c6ec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef5158840006ee5158840006ed5158840006ec51588400c6ef41588400c6ec4158840006ef3158840006ee3158840006ed3158840006ec315884002eef705884002eee705884002eec705884002eef505884002eee505884002eed505884002eec505884002eef405884002eee405884002eed405884002eec405884002eef305884002eee305884002eed305884002eec305884002eef105884002eee105884002eed105884002eec105884010cff76508401a67e65508400067d655084019ede6350840006dd635084000eee6250840026f77598440026f67598440026f57598440026f47598440026f47498440006f754984400c6f65498440006f554984400c6f45498440026f77398440026f67398440026f57398440026f47398440006f75398440006f65398440006f55398440006f453984400c6f74398440006f64398440006f543984400c6f44398440026f77298440026f67298440026f57298440026f47298440006f75298440006f65298440006f55298440006f452984400c6f74298440006f64298440006f542984400c6f44298440006f73298440006f63298440006f53298440006f4329844002ef7709844002ef6709844002ef5709844002ef4709844002ef7509844002ef6509844002ef5509844002ef4509844002ef7409844002ef6409844002ef5409844002ef4409844002ef7309844002ef6309844002ef5309844002ef4309844002ef7209844002ef6209844002ef5209844002ef42098440004ff755844001cfe7558440004fd755844001cfc7558440004ff7358440014fe7358440004fd7358440014fc7358440006bf4358440006bd4358440004ff725844000cfe725844000cfc725844002ef77158440006f75158440006f65158440006f55158440006f451584400c6f741584400c6f44158440006f73158440006f63158440006f53158440006f43158440006f72158440006f4215844002ebf405844002ebd405844002ef6105844002ef41058440006f7755
  | 9 => 0x77150540007b76150540026be6150540026bc6150540007b46150540007bb705054002dbe705054002dbc7050540007b87050540004fe76105400067f651054014e7c6510540245be7410540007b54110540004fe7688540004fd7688540024fc76885400067f65885401367c6588540005be7488540005bd7488540006f76188540026f46188540004ff7648540004fe7648540004fc76485400067f65485401267c6548540005df73485400e5dc7348540006ef624854000eec6248540006f76148540026f461485400067f65d01401167c65d014002dbe74d014002ebf64d014002cfa76d01400077b65d014023f7865d014002dfa74d014002efb64d014002fbb64d01400c7ba54d014023fb954d01400c7bb41d0140007b941d01400ce7f74594400c67e74594400ce7d74594400c67c74594400067f73594400067e73594400067d73594400067c73594400c67f43594400063f43594400067e43594400067d43594400063d43594400c67c43594400067f72594400067e72594400067d72594400067c72594400c67f42594400067e42594400c67c42594400067f32594400067e32594400067d32594400067c32594400067f71594400067e71594400067d71594400067c71594400c67f41594400c67c41594400067f31594400067e31594400067d31594400067c31594400067f21594400067c215944002e7f705944002e7e705944002e7d705944002e7c705944002e7f405944002e3f405944002e7e405944002e7d405944002e3d405944002e7c405944002e7f305944002e7e305944002e7d305944002e7c305944002e7f205944002e7e205944002e7d205944002e7c205944002e7f105944002e7e105944002e7d105944002e7c1059440006df7558c40006de7558c40006dd7558c40006dc7558c400bedf7458c400c6de7458c400bedd7458c400c6dc7458c40006df5458c400c6de5458c40006dd5458c400c6dc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c40006de5258c40006dd5258c40006dc5258c400c6df4258c40006de4258c400c6dc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dd5158c40006dc5158c400c6df4158c400c6dc4158c40006df2158c40006dc2158c4002edf7058c4002ede7058c4002edd7058c4002edc7058c4002edf5058c4002ede5058c4002edd5058c4002edc5058c4002edf4058c4002ede4058c4002edd4058c4002edc4058c4002edf2058c4002ede2058c4002edd2058c4002edc2058c4002edf1058c4002ede1058c4002edd1058c4002edc1058c40004ff755884001cfe7558840004fd755884001cfc755884000cfd7458840004ff7358840014fe7358840004fd7358840014fc7358840
  | 10 => 0x24028fb954d02400ed7e76d95400ee7e76d954001c7e76d95402873f74d95400ef3c74d95400067f63d95400067e63d95400067d63d95400067c63d95400067e62d95400067c62d95402873e40d95402873c40d95402867f74d95400ee7e74d95400ee7d74d95400ee7c74d95400067f73d95400067e73d95400067d73d95400067c73d95400067f43d95400067e43d95400067d43d95400067c43d95400067f72d95400067e72d95400067d72d95400067c72d95400067e42d95400067c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067e31d95400067d31d95400067c31d95400067f21d95400067c21d95400067f70d95402867e70d95400ee7d70d95402867c70d95402867e40d95400ee7d40d95402867c40d95400067f30d95402867e30d95400067d30d95402867c30d95400067f20d95402867e20d95402867c20d95402867e10d95402867c10d954000cfe76d89400067f65d89400067c65d89400deee62d8940004ff75d894001cfe75d8940004fd75d894001cfc75d894002cfd74d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400deee42d8940006ef32d89400deec32d8940024fe71d8940004fd71d89400deef21d89400deef20d89400057f75589400ed7c75589400067f65589400067c65589400deec62589400f4fe76d09400067f65d09401b67c65d094002cfc76509400067f65509401a67c6550940006ef625094000eec6250940005fb705094002df870509400067f65d85400067c65d8540004ff75d854001cfe75d8540004fd75d854001cfc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d854000cfe72d8540004fd72d854000cfc72d8540006f731d8540006f431d85400ed7e75985400057d75985400067f65985400067c65985400ddee7298540005ed7298540006f761985400057f75585400ed7c75585400067f65585400067c65585400067f65185400067c6518540026f66118540006f56118540004fe76d05400067f65d05401967c65d0540005be76d0540006be76d054027dbf75d054027dbd75d05400073f65d05402773c65d054026ebf63d054026ebd63d0540026be61d0540026bc61d054002dbe70d054002dbc70d05400c6bf60d054002cfe76905400ed7e75905400057d75905400067f65905401867c6590540265bd74905400ddee7290540005ed7290540006f76190540026f4619054002dfa7090540005f9709054002cfc76505400067f655054016e7c6550540006f76150540026f46150540005fb705054002df8705054002cbc765054025dbf755054025dbd75505400073f65505402573c655054024ebf635054024ebd6350540007b
  | 11 => 0x57f75581211257c7558121005bf7458121005bc7458121005df735812111ddc7358121006df6358121006dc6358121006df6318121006dc631812102efa6018121006f9601812100cff7658b400c6ec6258b40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b4002cfc7458b40004ff7358b40014fe7358b40004fd7358b40014fc7358b400c6ef4258b400c6ec4258b40004ff7158b40024fc7158b4010eef2058b400b4ff7650b4000eec6250b401157e75987400057d759874010dee7298740005ed72987400c6f76198740026f461987400c6f46158740004ff755874001cfe7558740004fd755874001cfc755874002cfc7458740004ff7358740014fe7358740004fd7358740014fc7358740004ff725874000cfe725874000cfc72587400c6f741587400c6f4415874002cbd76d07400c5bf75d07402a5bd75d07400c6bf63d074029ebd63d0740026be61d07400c7b661d07400c7b561d0740026bc61d074002dbe70d07400c7ba70d07400c7b970d074002dbc70d07401157e75907400057d759074010dee7290740005ed7290740026f461907400c7b44150740005bf7650740006bf7650740295bf7550740295bd7550740236bf6350740236bd63507400c7b771507400c7b76150740026be6150740026bc61507400c7b4615074002dbe705074002dbc7050740024ff76887400c4fe7688740004fd76887400c5be7488740005bd7488740004ff7648740004fd76487400c4fc7648740005df73487400d5dc734874000eec6248740004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a40006bf4358a40006bd4358a4002eef7258a400f6ee5258a40006ed5258a400f6ee4258a40006ef3258a400f6ec3258a40004ff7158a40024fc7158a400f6ef2158a4002cfc7058a4002eee2058a4002eec2058a400dcfd76d0a4000cff7650a4000eee6250a40006ed6250a40005fb7050a4002df87050a40004ff755864001cfe7558640004fd755864001cfc7558640004ff7358640014fe7358640004fd7358640014fc7358640006bf4358640006bd4358640004ff725864000cfe725864000cfc725864002ef77158640006f65158640006f5515864002ebf405864002ebd405864002ef6105864002ef410586401057e75906400057d75906400f5ee7290640005ed7290640026f66190640006f5619064002dfa7090640005f97090640024ff7650640026f66150640006f56150640005fb705064002df87050640024ff768864002cfe7688640004fd7688640004ff7648640004fd764864002cfc7648640005bf7448640005bc7448640005df73486400fddc734864000eee6248640006ed624864002df976d02400c6f976d024002fba74d02400c7ba54d
  | 12 => 0xd6419121006dc63191210c4ff751912101cfe7519121004fd75191210c4fc75191210c6be74191210c6be5419121006bd54191210c4ff7319121014fe7319121004fd7319121014fc7319121024ff7219121024fd72191210c6bf421912113ebd421912102cfe7019121004fd70191212ddde76d8d2111ede76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d212cfcf72d8d212d7cc72d8d212d7ce52d8d21007cd52d8d212d7cc42d8d212d7d771d8d212d7d471d8d21007d651d8d21007d551d8d212d7d721d8d212cfce21d8d212cfcc21d8d212d7d421d8d212d7cf20d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d212cedf72d8d212d6de72d8d212d6dd72d8d212d6dc72d8d212d6df52d8d212d6de52d8d212d6dd52d8d212d6dc52d8d212d6df42d8d212d6de42d8d212d6dd42d8d212d6dc42d8d212d6df71d8d212cede71d8d212d6dd71d8d212cedc71d8d21006df51d8d212cede51d8d21006dd51d8d212cedc51d8d212cede41d8d212cedc41d8d212d6df21d8d212cede21d8d212d6dd21d8d212cedc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d212d6df20d8d212d6de20d8d212d6dd20d8d212d6dc20d8d212cedf10d8d212cedc10d8d21025ee76d0921006ee76d0921024ee76d09212c5ef75d09212c5ed75d092100dee74d092100fae74d0921006ef64d0921007af64d0921006ed64d0921007ac64d09212bdef73d09212bded73d0921007cf63d09211aeee63d09211aeec63d09212afcc63d09211aecc63d09212afaf43d09212afad43d0921025ee71d0921007e671d0921025e671d0921007e571d0921025ec71d092100eef61d092100fe761d09212b7e651d09212b7e551d09212afe631d09212afe531d0921005ed70d092100cfe76d052100cfc76d0521006bf64d05210c6bc64d0521006df63d0521156dc63d052100dee72d0521005ed72d05210c4ff765052100cfe765052115cfd765052100cfc7650521006bf6450521006bc6450521006df6350521166dc6350521005ef725052100dec7250521027b44150521027e42150521006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d81210c4fe74d8121004fd74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d8121024fd72d812107eee52d8121006ed52d8121006f651d8121006f551d812107efa20d812111dde7398121005dd7398121006df6398121006dc6398121006fb6098121
  | 13 => 0x441007b54250441004ff755804101cfe7558041004fd755804101cfc7558041004ff7358041014fe7358041004fd7358041014fc7358041004ff725804100cfe725804100cfc7258041026bf4158041026f64158041026bd4158041006f54158041026fb7058041006fa5058041006f950580410c6fb40580410c6f84058041006fa3058041006f93058041026fb1058041026f810580410c4ff759922101cfe7599221004fd75992210c4fc7599221026be7499221006bf54992210c6bc54992210c4ff7399221014fe7399221004fd7399221014fc73992210c6bf4399221006bd43992210c6bf429922118ebd4299221024fe7199221024fc7199221026be4199221026bc4199221026ef2199221026ed219922102cfe7099221004fd7099221004ff755922101cfe7559221004fd755922101cfc7559221026bf7459221006bf5459221006bc5459221004ff7359221014fe7359221004fd7359221014fc7359221006bf4359221006bd435922115ebf425922115ebd4259221024fe7159221024fc7159221026be4159221026bc4159221004ff705922102cfc7059221004ff755822101cfe7558221004fd755822101cfc7558221004ff74582210c4fc7458221004ff7358221014fe7358221004fd7358221014fc7358221024fc7158221026f65158221006f55158221026ef2158221026ed2158221026fb7058221006fa3058221006f9305822104efa2058221026fb1058221026f81058221006dc63d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121006be54d9121006bd54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d9121024ff72d9121024fd72d9121006ed72d9121176bf42d9121176bd42d9121176ec42d912102cfe70d9121004fd70d9121176ef20d91211257e75991210057d7599121006bf649912111dde7399121005dd7399121006dc639912115df571991210c4ff759912101cfe75991210c67e759912101c7e7599121004fd75991210c67d75991210047d75991210c4fc75991210c4fe74991210c4ff7399121014fe73991210c6de7399121014de7399121004fd73991210c6dd7399121004dd7399121014fc73991210c6bf4399121006bd439912118cfd72991210c6ed729912115cfd71991210c6f5719912102cfe7099121004fd7099121005df735912111ddc7359121006dc635912118df77159121004ff755912101cfe7559121004fd755912101cfc7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121004fd7359121014fc7359121006dc7359121014dc7359121006bf4359121006bd435912115cff7259121006ef725912115eec425912118cff7159121006f77159121004ff705912102cfc705912115eef2059121174fe7619121006b
  | 14 => 0x6ec5358a41006ef4358a41006ee4358a41006ed4358a41006ec4358a41026ef7158a41026ee7158a41026ec7158a41026ef5158a41026ee5158a41026ed5158a41026ec5158a41026ef4158a41026ee4158a41026ed4158a41026ec4158a41026ef3158a41026ee3158a41026ed3158a41026ec3158a41006ef7058a41006ee7058a41006ed7058a41006ec7058a41006ef5058a41006ee5058a41006ed5058a41006ec5058a41006ef3058a41006ee3058a41006ed3058a41006ec3058a41026ef1058a41026ee1058a41026ed1058a41026ec1058a4115cfd76d0a411b67e65d0a410067d65d0a4100eee62d0a4100cff7650a411a67e6550a410067d6550a4100eee6250a41006ed6250a41005f77150a41025f47150a41025f576d06410c6f576d06410277665d06410277565d0641027b674d06410c7b654d06412ffb554d0641027e662d0641027e562d0641005f570d0641004ff755824101cfe7558241004fd755824101cfc7558241004ff7358241014fe7358241004fd7358241014fc7358241004ff725824100cfe725824100cfc7258241026bf4158241026bd4158241026fb7058241006fa3058241006f93058241026fb1058241026f8105824100cfe76d894115eee62d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941024fd74d8941004ff73d8941014fe73d8941004fd73d8941014fc73d8941006bf43d8941006bd43d894115eee42d8941006ef32d894115eec32d894115eef21d894102cfe70d8941004fd70d8941005df7358941165dc735894115eec6258941174fe76d094100eee62d0941024fc7650941006ef625094100eec625094115fac4250941005f77150941025f47150941025be74d0541026bf64d0541025f674d0541026f764d0541027b764d05410c7b743d05412f7b543d0541005f570d0541004ff75d814101cfe75d8141004fd75d814101cfc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d8141006fb50d8141006f850d8141006fb60981410057f755814116d7c755814116d7e75181410057d7518141165de7318141005dd731814115dee7218141005ed721814102efa6018141006f96018141004ff755884101cfe7558841004fd755884101cfc7558841004ff7358841014fe7358841004fd7358841014fc7358841026ef725884113eee5258841006ed52588410c6ef42588410c6ec425884113eee3258841006ed3258841024fc7158841026ee2158841026ec2158841004ff705884102cfc705884113eef205884118cff7650841025f77650441006f77650441004f77650441025f77450441027b774504410c6f66450441027b664504410c7b654504412efb554504412e7b643504410c7b443504410c7b7425
  | 15 => 0xc75d8542004ff73d8542014fe73d8542004fd73d8542014fc73d8542006bf43d8542006bd43d8542006ef42d854218eec42d854218ef621d854202cfe70d8542004fd70d854218eef20d85421a57e75985420057d7598542006f76198542005df735854219ddc7358542026f66118542006f56118542004ff75d814201cfe75d8142004fd75d814201cfc75d8142004ff73d8142014fe73d8142004fd73d8142014fc73d8142024fe71d8142004fd71d814210efa20d814219dde7398142005dd7398142006fb60981420057f75581421a57c755814202efa6018142006f9601814200cff7658b410c6ec6258b41004ff7558b4101cfe7558b41004fd7558b4101cfc7558b41024fc7458b41004ff7358b41014fe7358b41004fd7358b41014fc7358b41006bf4358b41006bd4358b410c6ef4258b410c6ec4258b4118eef2158b41004ff7058b4102cfc7058b4118eef2058b4113cff7650b410c7ac4250b410c6fb609834102ef860983410c6f86058341004ff755834101cfe7558341004fd755834101cfc7558341024fc7458341004ff7358341014fe7358341004fd7358341014fc7358341004ff725834100cfe725834100cfc72583410c6fb40583410c6f840583411867f74596411867e74596410067d74596411867c74596410067f73596410067e73596410067d73596410067c73596410067f43596410067e43596410067d43596410067c43596410067f72596410067e72596410067d72596410067c72596410067e42596410067c42596410067f32596410067e32596410067d32596410067c32596410267f71596410267e71596410267d71596410267c71596410267f41596410267e41596410267d41596410267c41596410267f31596410267e31596410267d31596410267c31596410267f21596410267e21596410267d21596410267c21596410067f70596410067e70596410067d70596410067c70596410067f30596410067e30596410067d30596410067c30596410067f20596410067c20596410267f10596410267710596410267e10596410267d10596410267c1059641004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a41026ef7258a41006ef5258a41176ee5258a41006ed5258a41176ec5258a41176ee4258a41006ef3258a41176ee3258a41006ed3258a41176ec3258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a4102cfc7058a41176ef2058a41176ec2058a41006ef7558a41006ee7558a41006ed7558a41006ec7558a41006ed7458a41176ec7458a41006ef5458a41006ee5458a41006ed5458a41006ec5458a41006ef7358a41006ee7358a41006ed7358a41006ec7358a41006ef5358a41006ee5358a41006ed5358a41
  | 16 => 0x400100000000000000000000000500000c00000d00500000000800000c00800700002500202600e00100600100102301300201300e00300900000300301b00a00000000200200601701101801c00400000401100200600100402500104100000400001200201100803700100100300200800600500100000e00701200800a01a01200200500e00400400200600000400100000000000200700500200000500000200200900500000000000900100001600200000000400101400c00200000002a00200000600201f03200301c00100f00801100200000002a00000400100400000202f00000001300800d00600201400400700001801000000200f00400000300100900001900c03100000202300300000000200000000200c00100400a00a00100103d00a00000600b00400100a00e00100203300900100d03400e00500500600000001100000200e00600200100000400100100000000d00c00001108e00000000103301600900103300001c00600201000000400f00000000500003a00d00000100300300900200200000800000000000400a00100c06e09401000400401100000e00000600400100501b00400000200100302d00600100000300500200d00001800900001801600001d00301c00000500500000800600000100100f00000100500000101b00000400e00300200000000000000101b00502400b00400209201900500400100d00e01f00400000102400400500b01105400900600000500407600e00001600100400000700300b01500200200200102300c00201400100b00900800700800000000000600700100100001802d00000200501200b00100400001600b00000202200000600200b01000500201b00101100400400100001001d01a00000600100106b00000400001100800000000400200600000100600001900200301c01200f00500105e01a00200400600001d0000010270011b57e75987420057d75987420c6f76198742026f461987420c6f46158742004ff755874201cfe7558742004fd755874201cfc755874200cfc7458742004ff7358742014fe7358742004fd7358742014fc7358742006bf4358742006bd43587420c6f741587420c6f4415874215ef62158742004ff705874202cfc70587420c6fb609834202ef860983420c6f86058342004ff755834201cfe7558342004fd755834201cfc755834200cfc7458342004ff7358342014fe7358342004fd7358342014fc73583420deee4258342006ef32583420deec3258342004ff7158342024fc71583420deef21583420c6fb40583420c6f840583420defa205834200dee74d094200fae74d094200eef64d094200faf64d09421aeee63d09421aeec63d09420c7af43d0942307ad43d0942005ed70d0942004ff75d854201cfe75d8542004fd75d854201cf
  | 17 => 0x40f2a0853c44326507c91aa2370519af83ca5e51e299c4ac22df2c18a144fc5000a787cc5da72d14a09004ce83e152257c15e26f33e1070adc56244da460b8a2d650d8a402360271fd91f487e00000000009f2ac3466a2d81de0003a62750f1c0460bf1e0132c52139383540000004e51564280884220019092291a5578ceca9030f23185880b24c013ca4f8f6a95b0000000000213000000080055d00000007aa6e000002041a4718000163034c5c645084f82d22e542a14d80f89271b88f4c888000156063c19e99014da6150cea9a284ab80d7a77025f16e012a14916a847131a9aa51d0a604b621d3cb800134c948000176884c48f4bf127949400033696b542200012c800820a2621371978a6234d00027d407e51b14915b00006862ee09f0ab093c5409d5c1d6a33000014129850f3fc194c0002f8030274d1e225315da20141c9c403a219079800100100000100400000001000000a00100000101200300000b00200001301200100000100100604700300800500601b00900400a02900000000100801700e01f00101000000100501702800200100c00801900c00000600300000106b02f01e00100200200f00802700200906d00000200800000c00100400b00300100100200000000003100201800000501000401f0000b900101c00000b00c00300100700000e00100900000200c00d00000301300201200102900100c00000301d02a00200900000300500900100500000604200000600000101c00000000900501b00102000d00d00803c01100201e00500000500400b00800100a00000402500000000000202100900301d00200100002800b00300400200105900001700100a00803800101100a00d00100200300101905000000a00300600800100300000100000102600301a0000040110010170160030d500400800000700100001b00000001400000000500400501000000300200600000100200000c01f00a00100000400400000500100101100002d00f00600200500000600a01c00100600200000601b00100000003800000f00000100501e00b00201100001200300f00000000100000000400900503600101c00000000800600101f00400003004101200c06c00e00f00400200100000001801300105300000200000700900100100f00000904300200000b00100800d00100300300000100000800b00300400000500000200100000001f03100000000900101200900002800500700603700000000000100f00b00600c00000400900000700100000200100000b00000901202700100200101c00600000500c00502701f00100700201300000100600600800600d02c00700200e0a700000700000200000200802600000000000101100100b02005602000700200000200000800000500200100101500801d00100500100201
  | 18 => 0x400064e47483f40003392ee9a955a05ba00000009426de4db8e3d5be475000076cc2a23b0000da8d6e466000202044e00004305c0c8800049197e000000000008e0000a054d598d843853756704e08060002890f180000003e50fd50f850c34380014561313e780013cc5c7440838cb609bb1dc07508c225600d9a254e088c00010a88e87550002920000000000231d4da37309592c00008b915790c00008d620b9cb000070d562a56536a0000002490bbe3e148100008740000000000b881200a4000000073d00019d00e058710a8000bea77d04009349a00003281828c6a01c177950c0000000000000dd62ec00021000000000088000a220574f508c135a9ce3591d4cd907b432b1d7885c601367189075616c22884b956a2b44eb95e134284c2631d500008f3170817910a0302248b8c19222316da54049e8904770a2cc842894cd14181b222a4ac2b346de98f4e1800048aa6a04887d130e11a13517200882d7079853488a00000000003c21be1358000dee00000004ed23221a20802c4000933326a59415c079510a4a51ae9f115e025919c6ed4c402f91664290b7a2207249f642ea474fa448a205a08004642432a83fd56060f5180a9c90e18750ba41801047f3509c24fcc2fd1b6860013600038e1f00a7e4970229d342b81970ac054095a04e2bf9a1437a7e10238508bc05bf26c16186349ef0be07455643d40cd98bd3784e9097979147a063210a63098e36741794a466e1c50001998f529fd3d200006824c109ba64452c7662a0a51c5423ad1620d110864e0010a768c5a000319229537c58b31b9da951a6a00002304c0472f541800037635b153000000000035d0dac5e40004008fd03664733080f5945a3774d4224537087000022d0000a6b0ec81512066c601a9784ed800040a9c3cafa5af51b00011323135218e2424278552f9020b9e95310c9f08bc658426425a82d03a138b1a5c4e468e00015d015498e51927acce441d28c9a206f47612da000061ca353018fc441c58d23106e80e28cb38599853a27fa18881eccc47820141e1109a0e134a80007fc9750000ff50c06cc13e90ed1f8657191000048273400006b00007723908000000000383a3e0eb64e44ef9e5895e000000000000086800008008c87bd0fda96ce140002a30c2d45444202d030925a94a00010bcfb877e468a6891da82926aa780c3421f289859c7627f73be18f0a72a382348990bda84600d168c3c48d400018241201dc44b88c54d829355184580002e049d29c80009f035a0000e32967279a09ca8043e2230c24a5a7e224184d04ea0003de2570000000000211c0000004e5a83457c6f833c8b6800089443917f15a48c93d3a1651b216e0792a50e606f631a08a00007c720381cd44a9ae3a70f4801a232411088075c08300017e938c35925515291a4ab1
  | 19 => 0x62880000ed63050308bb86f00000449a0138e19441907193fe4f8261aaf4e0899d44c024881a52731c87dc9d67f5096265000020a00f04208500004f095f879c45032623f8b127931cba2fc5e6a011d7a7c815a4814d88834b50938000197c0003183f201951e800042d00000002ea07e15e86468ea1939d7094666015e80043a03983f7800157089e000000027a9cd0000ba4a644c53bc0e5033e58e0531de47f028f00029600ec0002ec04310080001b90f246a2000000000000050a1731e3000098213b800059200000000011342600001decdcea0726e23ecf448690000fc800052400002d13b845b4570c4133800000000005323031c625080004253dc80004be000348034cf107222b196c4a3428a346096020000047413740008932510e91330a9b05298b8e6408853a0da40000000cf1064cb68e400000000000000000b4ca68a4400011d80004a5000000000067038f00002e40000001edc00021720b20cd4204904548a313667752ea000032a89c00028ec000a4725900000269392241cd8c4059529e9c205ea16334e262d5ac26d000013400000048902e8b540000000de40005c041b9ad83c0a3420219b136836229318e062476f4a7aa88c4c3bb41e00006747d51af883d24c00000003c5568a9d1b188401be92c0a52298ab437b013276400044b2ab90acbac15b4a480014c28c65329bd11880000000edcc4219d23d92a0ee87a83ffa8f82bc0005098ea02f06b02c103749fa3dc54c800021c00041b18700007f93bd0e100004ed1688000000a281d0127011a6ec3c4a5686900bb00007084c25230910f0c10450149a1bc87ca643377214cf9c76e35d89d149666b0a0859156c00000029fcd4c84a1f108a40404a415898ac934000364800000054c13d00006dc0000000050c90a1946c11740004203f48000bd2000000057d0b047c00000000004c247f9a594c445a4f115f0c1c1793d982744ae0cc31408e4e4614b56490500003f60002068a1044c2ca09712aa000295aaa837e00051f99700d6631468176c7ae8d326ca5cc846a1c1cb1c30e262011d817ed4f60e427896b0fe853323500c4e8c00007d071cc0c87b4c52b6c3143df53407e8dba74a074111c17a72e48b27401cc5cb13480000004ab00003e40006aa3288bf15b069a01b264ca086814080c8534e0b61d312e4a880751a8241061803e1089ec103e4cb501ab78ba41132eaa5c0f0c68b1062274f206841b62b70eb002f1caa0709f697211312184087925378d4842c29a09f85741eca772279c802d6146192a2d49b619054b87c42f68614d49e78f1ea5d059042c2e8ab90ff0aa9598a9005810dccca4053e6140cd8852f47080000005cc00000004e221400027a41440ec00016686387420a19a7c73c0002ad95b554e16a000060800000000500015887050000e9
  | 20 => 0xac65c0004311900926000000000000000000017d8904000454000067a05136a12cd35e74900029341ee00012700000000000001ad47f82cd03480004fe0554b880000003885572924fd09221039a6c0daa8f2110dd07444d339c0ac12202953e29eb07bc8df2300d152a41ff19513c8a541a103796f02021283ef273caec9513510e6d19e84f54317b0d8093b2aa22f12f41b900b87b13dc8b0356a4d8c309f8198812cb9a6291ad04f0b4e221033a23cb263ef3728d1cf400d406f07e555097c16921e4a4483520983d49c446752b0d7105aa520e185107c02b94370394d2836611a00ac8b00841a11645250412569aaf8416693552236d41829c47325792ec2b818f844156622f51e02a13982d8358888903a91500027901dc83a3020d555905770931bc0000a663c8a4390d82c73492a70aa687636e00015a8a92504831944e3062ce000105037508c942c6047a501604c916400038d06b43d685025b126d0ee40c2189fa8e4823d02b1ec49be5ef47b8f6cad01f62810aa0cd221e216a68c00a4014032b1944646c4838000b6a0523a21f240001dd1c1155530c22e0200c6cc3264f27a029cfbe86506b94505f21f022098785909dd43f0b64f306633df8b74f5c10902129d847490f2b200740f053e0191c6c89c0d04c0a8200008ec0000000ea064a3d303285c42de00019ece040970000bec00050e22b0d4cb3c85e25e957c4cc57905f906850e3294618d5c772000094999c3b05d036810f0c580e74b08c284b419112ea7dc0000002a10000000000362a67891a8554a722b40000a4245a5a09ec56f1681a900000004220120c6601001c0b3c0307e52fb8fcd2547b80c4045d34000000004482ca9462e10000be20004e11b0c19a8193949d1c9ae4881e085f4ed233e2d20f0952c07e5500a34000935119800014234c000000064c0000000910424a710001a3c9a226c2691d941721ce24c23f45c814c1d48f6431601212521cc89aa06000212c55c8de53a8000dd269e296036948a06e4eb1a446780000150a38d5c000000294cd8271d0000fa907000045ea02d4dc000510133400000004f8fa415200023d000000055140b8978398124404800000093147ca8787cc0000002b749781770ea970c70007f36a927c2b24cc2ec94b8dc61a848897b941400033b0000330000000225400061b365800000000000020080005f30000000d94a124900000e2e8164bc9478e8a0ce00000000001ae000000000000000017c117c9c100000000004a052a0c780000003c58cfc0000000001e68ca882a31f9ce80003dd4491d2c0000000390734ac00164d600000000000fa87595160000d525bc5a800047a80015764ef15911bd0286164560f609762eb000017c3188250b0a7b157400018b00000005f9378800004403908684e40000c000006d14f495
  | 21 => 0x2e08b14a2c76000000007347711d18ea801200036da1b48ee1734a0000066c0003c187f51701b10002b0461aa242a2878c00026849b8000a8e0000e5165c4a46af21b20007b42cc1990a080007e014000cc83c9570002198a1a43856a947c9fc41b5170000fa03d143c11640680c30d214ed0220001b21b6053e83f00006a40000002b90a889cc0000000a440b6a3100022bc83e2b54fd92d000008507f00010ac2e700003c0f888cc346a0380001232dda7a060201f02191b80005561aa00000007fc0000000af682627d0000000000000279490800022f8000ec654d0000e28b3e1854e2a16d4827a142fa53401845453c091c30860c4fe248454091c24aa67cf644a73d509cc992a0f1c319e03c819a25fa76c05a04c38801dc63a23e48fa258d146d92b89904a0a5ea36b163c20c32b4bb836130691b0f50228bae7f6533aaa466a8f00d583ed1ba63a46024b873e3ec0dc054405275f3410d3c2282fa4e4a1a8b9c7813df15a8dfaa0040629f0da66750312a7c5fe03a0d78c64bd01c930f8fa05088ef0659be44f05733acaa14aea32c4df85b4bfc58a2a91fc081e71f2e49f4d21814e26a1a643da2ba549868c9b42fe41d8aacad21960999dd881449d09b1c54640a4c534862477a84e112805486a86f14e98151767c643d22252161e74cc923110e2063610fc04869ba05024f4c8c0dc4c007a4fb20e91011f3521a614000000100e91e43f80b882a34637d9d7556e007000077c1ac9254c20acccf40b350f8f1d1ec72a21a272154a32448995980000004fc84c0000a2f4790428c0e8481f2291800088d27a800000028656b87a09321da2588ef096e35d0000aa4f740000000b000004724ea87e0f281601b09f20000a5010da970c104ea323800065e3834318bdc50239929287b812673329800902e26a70001460ec40000e580011ca6223090000b00000204a1080009d83f5a8508ae67f2db264809425507a02507160e02901310ffc5eb165933cbcc60d27e27cc41044a3871fcc11c8c244717f4cb090123692152d819237127d0f3a69d29aa6e4b6e5a62d70ad92ba09a198204872008b49589445e21543b9a1449cea3950b258873a72b52caa2951c3083180c50f324650ce2b6409e3d00000d953603ee43aaa4401c1bc4a088913c61c150128b092840e409a2ac5467f11db172918a0490000000000000093a9682067d6324826400000031ea12549e9543c38ed00000002670460c4e1b225d00010e851500c80000003580002b000000004be9694d709ed01b8304b4207d567a114eb400030e803c86411d124a414ca40000001da12007d83059c940001b72d116140005be1da9b6897074315b96c8d064060000000000aca416295c0d8acb1ce2104ffa1a041a00000000000e4274800074829e22182aa7f200028683061045130f
  | 22 => 0xc688144ec6bf123166c25a1d3539800078800052720b8076a042548e34b2c1a21d99f8c6687350838f20b104ee1158b706866cd2b388d4cde307001a03c496a803098000c4a4ac4cd890800000000024c08a4000379800000008c0a28000bc40c400010b06085b34388558000000257298cff600003322a828e0000000dd80001b02740b087f211e2af28550b80004069c0400007a40c0ee877c8244a59c000001b50000b280000000000000c5459000025fcf1488a3b22370fb66ac45180014c80b70000170dfca884ef0d003804f00000710a500002089bd400086b3d680011948e70000f2800023c39f1c490720ac0000e9d01411154482f150e6ab4852ab0000a9500000002cc3b23350000e62a600001c1800043300000012c61152ef1f5000082122e11e0f5e0002719f0d2c07280ba8ba000054f1569c0cb520000002b441f081b2d00cb522ea290f3016010e8231c08000ce68a249f869c0000001a49e6c8e2a5e2e9840887a2090bd00000001b6178027136425056d000106287d4f391a0e8071100020143ae0002b81a8c7ee3c033f000079e94439b80000006004db000031c8822298e4c00000000000000005f2337282d58e000000129800096d45b985c18e0004991b851c66c73e58b0400000000015380007bb51b80008d696e1bf00000000000001c985100004710d3907a65d00012d43bc4ec44180f0dae6ea27289c00000004e00000ea45bd24029e48aa0e200000011625f42b29ba128a4704de88d81b621854f166087233327f99f4eda5170c08f8d190a7d0129ddd3fc7d74caaa991485b91bf9fb4f1a6e41b4031558473902e8eb0c9615336788b411e6ef4701d45430767124069470a5810f7a5e0fa27ee00588fd1d65e70000b0c2ae80300011793f466801e8b191160003bf8664000aa100015ac17082b3089d3c21e12a0689f74b32a420928010274a7e4b31f9d0a42030a9196457e51c1801b7cdcc3cd2ff85fc91c1d24cba69413c3bf23f000062a3ed09a9b44156418000000000073b3ab191553079541822e8cee11f29d1af0da42a531f26908f27c13f61aa400054b50e9bf0cc81760c9a3e892c92f5558ce12d68da1941a600d40000000d782b4a5537faafd4800000001008d6600029c07f00000062a8294484e5071670dc144429700000000000001e58000d727141bea29c0004de1161e7128697b28e83a80000003118ffc4a89642e89ed819091417b03b472200000001050ae38e132800113e3e700000000d00001a5814c00024c55e1be800096913d9e7c00026305a8000000a8c2490d58e78000141a624cb431726b25d09c273f0e7967555a7413ed1570d5000048416486f84f71fd00012124892d595240007ab0c318ed1400981c3aa105e80001b00d28f460
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6f8250d65040014d904a1aca080029de0543594100253a40a86b28200087e8710d65040010fb0e21aca080129da0472594100453ac08e4b282004a768190965040014eb03212ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca080129da0432594100053ac0864b282005a7a800c965040014f300192ca080162f21175990100c61fbaea932020058bc845ce64040011df04b9cc8080063b209739901000557c12873202000aac8250e640400b17908b94c8080630fdd6759901000557c12e73202000aac825ce640403117d0e29cc8080022f61c53990100255b408a53202000ab58114a640403117d0e194c8080022f61c32990100051f428653202000a3d850ca640400956d02194c808002ad604329901002d5d400653202000ab9800ca640400b1f100baac8080162fa1f54590100061fbaea8b202003c3e75951640400b1790eaa2c808002a7a0c54590100054ec18a8b2020008ef825cd64040031d904b9ac8080123d205735901002c5f43c86b2020058bc8750d640400155f04a1ac808002ab20943590100255a40a86b202000a3e8510d640400147b0a21ac8080162fa1e42590100255b40c84b202000c3f759d5640400157700baac808016ae20175590100054f418eab202000a9d831d5640400155f04b9ac808002ab20973590100055bc0ae6b202004ab4815cd640400147d0a39ac8080028f61473590100045f438a6b2020008bd8714d640400956d03392c808002ad60672590100255b408a4b202000ab581149640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400956d02192c808002ad604325901002d5d40064b202000ab9800c9640400153d083aac608002a76107558c1000567c12e8b182000acc825d163040c35af02ba2c608012b52057458c100052f428e8b182000a5d851d16304001c3ea92a2c608002b6e015458c1002d6c402a8b1820008de8715163040011bb0e2a2c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608012b5a047258c1003d6ac08e4b182005ada801c9630400f5b300392c608012b5a045258c100056ac08a4b182004ad68190963040015ab03212c6080163ba1f525881002c7643aa4b1020058ee87cc9620400b1d90e992c408012b9a04755881003572c08eab102000e2f54951620400159d062a2c408002b360c545881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881002573408e6b102006ae5811cd620400b5d50039ac40801aba600735881000557420a6b102000aad8414d62040011df0ea1ac4080023b21d43588100053742886b102000a6d8510d620400b17b08bb684080163be1d62d081002c5e426eca1020058ec82dd9420400b1790eb2284080163b21d6250810
  | 1 => 0xf0abb0829000e1f21576105200c656322e420a40048f8865c0414800b1d90cba2429004a7320d74485200247743cc890a4000ccc7399121480095cd0332242900032bdd0644852000666398c890a405b9ce87dcd21480b3998edb9a4290167b1187734852002573436c290a4000b65851852148001b90e7b8242900030f1d764501200061e3a8c8a0240008ef825cd64c40031d904b9ac9880122f21d43593100046fc1aeab1620028dc835d562c40051bd0fb9ac58816637a1c7358b100247643aa4b1620048ec874c962c4005998e6992c588003995495158b1002477c3ac5a162035acc8358b42c40099cce2b16858800237e0d7650b100146e41aeca1620059b48750540c402559906b124188013391c5624831000477c12e732420018ec825ce64840070fd0fbaac9081431dc4375592102863a886eab24205087e871d56484007878eb2a2c9080162f21d54592100043fc2ae6b24200387c855cd64840011df04b9ac9080063b20973592100045fc22eab1420188bc845d5628400b1d90ea92c5080163ba1f3258a103276419260b14200087f855d942840070f90abb285080163b21d6250a100066639ac490c2000c3d75d53644400156b03aa6c888002a760c54d911000c77416e7b2220008ed82dcf644400517f0ea1ec888002ab20943d91100045fc22eab2220008fb805d56444001878ebba2c8880021fe15735911001c3e42ae6b2220008ef825cd64440031d904b9ac8880023de0573591100063c3aee0b2220008bf8759064440014790ab20c8880622f211751911000556412863222063cb57150c64440059b4e6986c48800e1fa1f75589100045fc22eab1220188bc845d562440011bf06baac48800a3720d75589100043f438eab1220188be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac4880021fe15735891001c3e42ae6b1220008bf845cd624403117908b9ac48800237a1c73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891001c7643aa4b122003c747594562440071e90ea8ac4880039954951589100166c39c60b1220028f8874c1624400b1e90cb8e84880021fe15765091001c3e42aeca1220008bf845d942440011bf06bb2848800a3720d76509100263bb02eb20a2004d73605d64144001ae460bac82880035c4c17590510005e8c18e0a0a2005ab48650740440010ff0abb2808800e1f21576501100061e3aec8a022000c3c75191404400b3690ea0a8088016ad219415011002dd840282a0220058f686dc5204400187ee93a2ca0818a9ee01745941002d3c402e8b282000a5e831d165040014bb063a2ca080028fa1073594100051ec20e6b282000
  | 2 => 0xd72584400056a41ae4b088000a76851c961100014eb0a392c220002ade1152584400c55a422a4b0880008f68714961100011eb0e292c220062ada1332584400055ac2664b0880008f6870c961100011eb0e192c2200029da1432584400053ac2864b088018ab6840c9611000156b08192c220016bca00325844000578c0064b08800387e855da41100031dd04bb482200c21fe1975904400062f31aeb2088000c6e625d641100098ecc2bac82200661fe1d65904400043ec3acb2088000c6e7259641100018bceab1c8220003175d5639044000667392c7208802e8ef865ca41100018dccab9482200031b59572904400066731ae52088000ccd635ca41100099ccc2b94822005a3be1d629044000476c3ac52088000c6e7558a41100018daeab1482200031d9d561904400063abaac32088000ce67258641100019cae4b0c82200163d60576884400146e41eec90880058ec82dd9211000b1e903bb2422000237e0d76484400146e41aec9088018c3c7459521100018b8e6b2a42200030f59774484400046ec36e69088000c5e65dcd21100018bacbb9a422016b3398b73484402ce6b30ee690880008de8758d21100011b90eb1a42200032bdd1624844000667b9ac49088000ccc73589211000b1e90eb0a42200032ddd161484400c65a3a2c29088000cd77358521100019a8e6b0a42200031e1d776500400063dc2eeca008000c7885dd940100018f6edbaa80200162f21d54592200062fbaceab1c4000a9e841d5638800153b083aac710002b3e097458e2021d66412e8b1c4000a5e851d163880014bb0a3a2c71000387d525458e200046f438a8b1c40008dd8715163880014bd0a38ac710002976147158e200054f420e2b1c4000a9d841c5638808759d0438ac710002b36087158e2002d6d400e2b1c4014ad9801c5638808759d0428ac710002b36085158e2002c7a43aa2b0c4002cda734c161880018bcc6bac83100131d98575906200062f3aac720c4000c5d7558e418808799ce4b1c83100033398d729062000666b1ae520c4000c757558641880019cae4b0c8310017369c163106200066cb1ae020c4000c3d75d53644800155b05aa6c890002a760c54d912002c76c16e7b2240028bf8750f64480011db0f994c89000e1fa1f75591200045fc22eab22400087e871d56448001878ebba2c8900021fe15735912001c3e42ae6b2240008ef825cd64480011ef02b9ac8900123d20573591200045fc3ac83224000a3c85590644803117908ba8c8900063b209731912000666192e63224000aaf8250c64480c795ae4a18c890002ab61332191200c65a20ae2322400087f855d361480070f90aba6c2900131d98575185200047bc3ac230a4000c757558461480091d9053b482900030f9d764905200061f3a8c920a4000cac645ca41480010f
  | 3 => 0x4b188005ada801c9631002f5b300392c620002b5a045258c400056ac08a4b188000a5e851c563100014bb0a38ac620062a7a107158c400bd4ec20e2b188000ace821c5631000159b0438ac620016b6a007158c400bd6cc00e2b188000ace82145631000159b0428ac62000297a142158c400052ec2842b1880058ee87d49621000b1d90ea92c4200163ba1f32588400c55742664b1080058ec874c9621000155f08baac420062ab211755884000573408eab108000ae5811d56210031c5ca9aa2c420062aba12735884000556c24e6b108000a6e851cd62100014db0a39ac420062aba1073588400b556c20e6b108000ae6811cd62100015cb0239ac420016baa0073588400b574c00e6b108018aae8494d621000155b0929ac420016baa02535884000574c04a6b108018aae8414d621000155b0829ac4200023be1d43588400b47643a86b108000caf8750d62100019590ea1ac420062abe0d43588400c747c1a86b108000e8e5350d6210001d1aa6a1ac42018fa3cc1435884031f4698286b108018aac845c5621000159f06b8ac420002b320d715884000537428e2b108000a6d851c562100011dd0e28ac4200023b61c51588400c55742662b108000aad84cc562100011dd0e18ac4200023b61c31588400053742862b108000a6d850c5621003155d0818ac420002ab610315884002d7540062b108000ae9800c56210031c6ca9aa4c220062ada1053984400055ac20a73088000ae78250e61100015c904a1cc2200123da1c52984400047ac38a530880048f6870ca61100011eb0e194c2200029da1432984400053ac28653088018ab6840ca611000156b08194c220016bca00329844000578c006530880058f687d45611000b1e90ea8ac220062ad211515844000573410a2b088000ae582145611000b1ed0f98ac220062ada13315844002c7a43a62b088000a76850c561100014eb0a18ac220062ada1031584400057341062b088000ae5820c5611000b5e50018ac2200029da1421584400053ac2842b088000ab7845d5611003156908baac220002bce01755844002d78402eab088000ae6821d561100015cb043aac2200638d95354584400c55b424e6b088000ab5849cd61100014ed0a39ac2200029d61473584400c55b420e6b088000ab5841cd61100015cd0439ac220002b9608735844002d79400e6b088000af1801cd611003156d0929ac220002ad612535844002d79404a6b088000af18094d611003156d0829ac220002ad61053584400c55bc0686b088065ab580d0d61100015cf04a1ac220002b920943584400c55bc1a86b088018e978350d6110001d2ca6a1ac220003a554d435844000753c1286b088000ea48250d61100c756f00a1ac22018ead601435844031f4b98286b088063e953050d611003156908b92c220002b5e0
  | 4 => 0x5500014d904a1ecaa00021fa1c43d95400ec3ec3887b2a8000a76819cb65500014eb03396caa00021fa1c32d95400043ec3865b2a8000a3e840cb655000147b08196caa00029da0432d95400053ac0865b2a8050a7a800cb65500014f300196caa00029ba0a71d954000536c14e3b2a804fa3e841c765500a147b0838ecaa00021fa1c31d95400043ec3863b2a8000a3e840c7655000147b0818ecaa00029ba0831d954000536c1063b2a8050a7a800c765500014f30018ecaa00021fa1c21d95400043ec3843b2a8045a3e84dc365500010fd0f986caa00021f61f30d95400051f42661b2a8000a3d84cc365500010fd0fb2ac4a00021fa1c65589400055ac2063b0a8000ae5820c761500015e30018ec2a00031b9cb659854000637390cb30a8000c6f655ca61500018d8cab94c2a001339185729854000672b96c330a800387e86dd561500010fd0fb2ac2a00021fa1c655854035e1eba0ca30a80008f7875846150001878cb3b682a01ae1f21975905400043ec3ecb20a8000c6e72d9641500018decab9482a00031b19572905400267230ae520a8000ce572d8641500018f0cbb8282a01430f1db65505400071bb28c2a0a8000e376550441500010ff0abb442a000e1f21576885400247a40aed10a8000c3c659d22150001878caba442a000e1fa1776485400043ec2eec90a80028de839d921500011bb073b242a0003171cf65485400062fb2ee690a8000c5c65dcd2150001998e7b1242a00063da1f61485400066a39ec290a8050c7a76d9740500a1c76c9b2e80a00628fa1273594403551ec24e6b288005a7a809cd65100d34f30139aca200628fa1073594400cd1ec20e6b288018a3f80d0d65100cb47b01a1aca2018e8f612435944000537c1286b288000a6c8250d651003147f06a1aca2006387e0d43594400070f39a86b288000e1d7350d6510001c5f04a1aca200038b209435944031d1fc0286b288063a3d8050d65100c7c3e60a1aca2018f874c143594403451fc22e4b288018a3c845c965100014ed02392ca200029d60472594400c51f42664b288000a3d84cc965100010fd0e192ca200021f61c32594400c51f42064b288000a3d840c965100014ed02192ca200029d604325944002d3d40064b288000a79800c965100cf47f08b8aca200628f21171594403353dc02e2b288005a78805c565100014dd0438aca200029b60871594400c51f42662b288000a3d84cc565100010fd0e18aca200021f61c31594400c51f42062b288000a3d840c565100014dd0418aca200029b608315944002d3d40062b288000a79800c565100010fd0e10aca200021f61c21594400c54f420eab188017a9d841d56310031c3ca9aa2c62000297a147258c400052ec28e4b188018a9e841c9631002f53b08392c620002b5a047258c400056ac08e
  | 5 => 0x802ae61050d814100578c08a1b0282008fb8758060504014f10ab00c0a08123b21d52588410247643a64b108218cb654dd9411040196aa9bb28220863acd0141580410247c43aa0b008200ae9828c160104091f10e982c0208122f211759922100557c128732442048be87d51648840187eebaa2c910812ada0754592210054ec18a8b2442048bc8750d64884015d305182c1108123e21d305822136666b90c7b2242048ed82dd7644840717f0eaa6c8908123b60b73d91210c61e322eb3224200c3d75d9264484018bcea31cc890803175d463991210c61fa1aeb3224200c3d7550e644840593ce6a1cc89080237e0d75591210146e41aeab2242008fb805d5644840b1f100baac89080a37a1f735912100477c12e6b2242008de871cd6448405938e7a1ac89080a2f21d43591210066639ee4b2242008bf8759064484b7998e4318c8908021fe15701912101c3e42ae032242008dd87997634840153d0932ec690802a761265d8d210046fc3acbb1a42008dd8799363484014bd0b326c6908029761664d8d210046fc3ac9b1a4259acc8654b63484b55a90ca8ec690803d154951d8d210054f424ebb1a4200a9d849d763484018baea3aec69096ab3a0875d8d212cd66c10ebb1a4259ad6811d763484b55ab023aec69096ab3a0b74d8d212cd66c16e9b1a4200a5e859d363484014bb0b3a6c69080387d5254d8d210046f438a9b1a42008dd8715363484014bf0ab86c6908029721570d8d210054fc22e1b1a4200a9c845c363484b559d04386c690966b360870d8d210046f438a1b1a42008dd87143634840153d08286c690802a761050d8d212d567410a1b1a4200acd8214363484b35ad02286c690802b560450d8d2115c76c3ec9a1242048ef87593424846b59906b268490803a318c64d09212dd67436c7a124259cce76d8f42484b3b8ce3b1e8490802d961671d0921024f3c3ae3a124200ccc635c34248401998c7b9282908163b20973d812100732a92a3b0242028de86dcd60484b31b90db9ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b02425bcce7218c60484d999ae4318c0908023ee1d601812100477c12e6b0e80018ec825cd61d000127b0bbb283a000237e0d76487400146e41aec90e80058ec87549629000b1e90ea8ac3200131d98575906400063abaac320c800087f855d921900070f90abb2432000237e0d76486400146e41aec90c8000ccc7358921900095c902b1243200021f61e63d95400043fc3ac7b2a8000a6f8258f65500014d904b1ecaa00029de0563d95400053a40ac7b2a8000a768198b65500014eb03316caa00768fa1273d95400051ec24e7b2a8000a6f8250f6
  | 6 => 0x20060000000c02000005000006018110000020540080202c0000000200000c000030000000180000600405001000030000120000000000600c0080000001001800005008018000000040000080d0020000000501800400000000000118000040000000000401c01800018004000050020040280300000000006002008010000060000000200a0100280a01200402801000028008080000000100100c0000280100e01800006002018000060000180080300001800008002008f78758461508011f70eb00c0a100a37a0f72583410046ec1ee4b068270a77815d165904014f700ba2cb208029e20174596411851f420e6b2c8200a3d841cd65904014df04a1acb208029b20943596410053bc0a86b2c8204a748150d65904610fd0e21acb208021f61c43596410253b408e4b2c8230a75811c965904094ed03212cb208029d60642596410043f43864b2c820087d870c9659040147d08192cb208028f61032596410253b40864b2c8200a75810c965904014f500192cb208029e60032596410253b40ce0b2c826fa75819c1659040147f08b82cb209ba8f21170596411851f420e0b2c8200a3d841c165904014bd06382cb208029760c705964100537410e0b2c8200a6d821c165904094ed02382cb208c29d60470596410043f43e60b2c820087d87cc1659040147d09982cb208028f61330596410053741460b2c8200a6d828c165904094ed03182cb208029d60630596410253b40860b2c8200a75810c165904094ed02102cb208029d604205964100556c26a4b1482048ec8754962904091d90e992c52080b331cd3258a4100557424eab148200aad849d5629040159d073aac520802b360e7558a4102573408eab14822eae5811d5629040159f06ba2c520802b320d7458a410257340ea8b148200ae581d516290401c5ea92a2c520802b3a0c5458a4100566c18a8b148200a6e851cd62904014db0a39ac5208baaba107358a4100556c20e6b148200ccd731cd62904095cd0239ac5208bab96047358a4100575400e6b148200ae9801cd629040155d0829ac520802ab6105358a410257340c86b148200ae58190d629046b1df0ea1ac5209b63b21d4358a410053742886b148200a6d8510d629040159d07382c520802b360e7058a410257340ce0b148200aaf845c162904011dd0e282c5208023b61c5058a4100557420a0b148200aad84141629040159d06282c520802b360c5058a4102573408a0b148200ae58114162904014dd0b982c5208029b6173058a410055742660b148200aad84cc162904011dd0f182c5208023b61e3058a410257340860b148200ae5810c162904019cac5b8a85208063ba0b735824100476c16e6b0482048f8874c16090431b6680b8682a08023be0973d814100c76412e7b0282008df835cb60504051b906b96c0a
  | 7 => 0x1769cc37ec102780070a0018d1410009255680b000578001fb00034cf38a50de000000002360000018044ee782da5a000ce13a2f40005912aaea000000000000000007f9150000006684940c7247b80035400000004000000ef8005b4000000000002e1a2160000000000001e8e080000025cb1c00335382000001b521c000003a2000000cb0000008780037d3ca0012f8ed000e3c9035a000050003180008357f8ae3c61480008800000154a651c4d843818664007181b974b6000002405f60000011900042cfa800000001aab490025f997911030c4c002164ac4e18501e00000000000000000001080d64c41b2690004cc000000009a00023c000669a7000000771480000000000039b000ec8d00c56223a040395000d04a38de066d14e1ba600e48dbc09f494000f42f20000002d10f654b240000017eccc0018773e9e852270564dc88818b11e6f518000000000002f10000000000c306000dd1480005a9359c20000002eb080000000000023a4e8000001b49406f9ee0d0001d595660cbe0001f716e9b5d488d21aa3c002a4032648003a310c2f5cb325590a68002843aa50d12b7171400000000000001c61be07aa6000000000919b20000000003f1a2000000003775aea8010aab636000003a10808b4000fb0106348f0aa6847a84e21400000000386264000110002bebd400000000001688004347356830f12ec40509900000009e0000001580017d56e8d0ba0002180001c06e47e1e9b5367000000000b445e544c416b4f20000001a73818cca80358ac650aaa24f6115679934de829270001ae00000000000bf47b0fc22c7914d9426c03100034034ed99301850cc001172e1338259bb1e22dad280000053c8a5910001a2b7800000648be8000004fa0000000e0000015d8005e0301868f9120561943633f43bc002452340a4d732311cc7400127178974f681d3e43d4001220000000000000000059968472001cc0003d65e4721534dc001aea7f352000002d40000002313e0000014600009099cd6107192b300006d212738258232c2309240476ea5dc1200015032c000e10a0ae800000000008004000000100000000000400002811000000000040040380000100000401002000020038030080000381001a0080000100a0100380e0020040100200800001000000000000020460000080500800400801000010078030020580000400e000000040040000180000000000001000000018040000040000000201c01801002000000050040000c00100200004009000030020040020040200000400000804002018008040100040100202e000030030040000000100c000000060000080180300000002005004000020040000000080001000000800004000008100000140000000200000805004010008010060040200a00a004010
  | 8 => 0x2865ec6d96333407869400000676aa0129dd54c9a9ac8ea3e89dc00154554001c9800024778000000000017285f000c01d200039e00080b5c00000000000000000b3000164c49b6a7533e5c00032d4327d921000000000000000d40018f0000c220c1b800000014000000000000035f59ce48a2800068d1800000000000000b000000153aca05674c0023a342001690000000001d0dc0000011433671c000498003d8bf98e172514e94b2a8574ecc0000c15be1dcfc00d276001c39f30000006db175f80001a80017492c25299000d4d39b1f000000328b62ea1354b0e771a8391f0003044acd19140f80b80000068e1b19c87f56a95169b434100015f80010e6e1610000008095a2e8000000000000004c00000000000000000000a500016e000260b381064ee24c7000000b9d1180000080d10874140150001b1562000d6a4775800195a5227a9d8002a57222495cacd24a5cd9e0ce466cf839abc364e00bb000000001608001141798098c000d6c0000000052c7f0000000005480000000000000000329130006a26e58389b000cf4c533234800000259000c25162530000019d0000000006b137000000510004160001600000000000000000001ce8e91043ac0000000000000000000001b40000f000000000026cb130800000000000000000018a991000001a58000880016c0007540000000000000000000000000013570001c46904353e0000000012a001490004bc1f417aa37028309229d054d344d283000000002415c610800000302000348e315809d121405cce6548b692f40597114a000b581da3d27ea7138af73fe00103bb01b00000500000000055af3000000000000000000880057cb7000000000000bc00033200000000000cfc000000009b0c786019800158000000bbc0009e5d634000000000000fc9523de00097862486408ed1002089883c83e05a00122000252000641591468600020f20693cceaec6f8c8531a20000c15bd37e3a06a00000000061085000000001c5a00512001d7121000000a71622f60004599755847c003ad000a20000000000000012d000e20e8a1b1ba00076000502000000000002d53f00075053c6315d02e6784a00051c7600017169e000001fc24c0011c00936e000772f90000e54595c000399b12db000001c21c6000721188512b414d6580046c3c0ed8f2356af52b944000ae02e35655ebb96a97c40a811192b620c448000000000007e800000000001493a4cdc0000000007c57a105000009b000102001602e90006d14124c0004a8d9b2e42472c001f051a5bcea0006a800000099000000488b14a215403000000dd000000000db000000426054000a60001903d8000007c5bd800000a547c0006e658c001e90000000000013a2f926857000000001a60000000000000087c0000062c784c480
  | 9 => 0x14d09c0000007246a00000000000000449343b20000035e00000000000000000002c352edc0001c70009e0000fa000000000004380000003f1ca00115258000000bf80000000020a11000000002174f8540000004761d500ac4050000898005ba7f4b49c04ccc31bc8cf272874d7ab337606ce28003ac00150b6b526d94cd8001a8710d81982b60019880001e780260e0456555d8b480009c8ab9bc46e971b712c698e51bf8f3740471a91d706000185a641b22e45396c064461c82ae0b000000326108825a80000621656c826176dbc000c326ad61438000000017200022e0017000011831c0039a6041d9111943cc4a0e50001e2001d7b29628000a30003fc414003832980000000010a0006a82000019c56800000c3800
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x400d00038d866427350d65100016899094d4358840005a46425350d61100014c5910c97319120
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
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124c
  | 13 => 0x124b
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138c
  | 17 => 0x138e
  | 18 => 0x98c
  | 19 => 0x98e
  | 20 => 0x128c
  | 21 => 0x128e
  | 22 => 0x10b
  | 23 => 0x10c
  | 24 => 0x5
  | 25 => 0x10e
  | 26 => 0x180c
  | 27 => 0xa0b
  | 28 => 0xa0c
  | 29 => 0xa0e
  | 30 => 0x130b
  | 31 => 0x130c
  | 32 => 0x130e
  | 33 => 0x180b
  | 34 => 0x180e
  | 35 => 0xb0c
  | 36 => 0xb0e
  | 37 => 0x140c
  | 38 => 0x140e
  | 39 => 0x28b
  | 40 => 0x28c
  | 41 => 0x28e
  | 42 => 0x184c
  | 43 => 0xb8b
  | 44 => 0xb8c
  | 45 => 0xb8e
  | 46 => 0x148b
  | 47 => 0x148c
  | 48 => 0x148e
  | 49 => 0x184b
  | 50 => 0x184e
  | 51 => 0xd0c
  | 52 => 0xd0e
  | 53 => 0x188c
  | 54 => 0x188e
  | 55 => 0xb8954
  | 56 => 0x94b96
  | 57 => 0x148954
  | 58 => 0x94b94
  | 59 => 0x95496
  | 60 => 0xb9394
  | 61 => 0x138b96
  | 62 => 0xb0994
  | 63 => 0xb0996
  | 64 => 0x98b16
  | 65 => 0xd0994
  | 66 => 0x98d16
  | 67 => 0x9cb
  | 68 => 0xa0114
  | 69 => 0xa0116
  | 70 => 0xb9814
  | 71 => 0x180a16
  | 72 => 0xa1854
  | 73 => 0xb8a14
  | 74 => 0xb8a16
  | 75 => 0xa0b96
  | 76 => 0xa0b94
  | 77 => 0x184a14
  | 78 => 0x184a16
  | 79 => 0xa1856
  | 80 => 0x1949
  | 81 => 0x181316
  | 82 => 0x180b96
  | 83 => 0x185814
  | 84 => 0x181856
  | 85 => 0x188b14
  | 86 => 0x188b16
  | 87 => 0xb1894
  | 88 => 0xb1896
  | 89 => 0x15ca
  | 90 => 0x144b
  | 91 => 0x24b
  | 92 => 0xb8294
  | 93 => 0xb8296
  | 94 => 0x184b94
  | 95 => 0x185496
  | 96 => 0x188d14
  | 97 => 0x5854
  | 98 => 0x5816
  | 99 => 0xe89
  | 100 => 0x9d253
  | 101 => 0x18c9
  | 102 => 0x11396
  | 103 => 0x11496
  | 104 => 0x11616
  | 105 => 0x109d6
  | 106 => 0x10e96
  | 107 => 0x749
  | 108 => 0x3ca
  | 109 => 0x40c
  | 110 => 0x148116
  | 111 => 0x148956
  | 112 => 0x149856
  | 113 => 0xe8109de
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1629
  | 6 => 2785
  | 5 => 947
  | 4 => 4
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
  | 7 => packedAt gbK7 (66789+((h/543+packedAt gbK7 (60273+(h % 543)*12) 12) % 2150)*12) 12
  | 6 => packedAt gbK6 (144816+((h/928+packedAt gbK6 (133680+(h % 928)*12) 12) % 3343)*13) 13
  | 5 => packedAt gbK5 (59338+((h/315+packedAt gbK5 (55873+(h % 315)*11) 11) % 1512)*11) 11
  | 4 => packedAt gbK4 (284+((h/1+packedAt gbK4 (280+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffff0f0e1fe1fffe1c0380ffc8083fc31f64f
  | 1 => 0x78780f00fe1fe380fe003ffffd474c90ce487f
  | 2 => 0x7f800fff001ffc00ffffc00f027870e30f8f8c
  | 3 => 0x80000fffffe00000fffffff003807f03f00ff0
  | 4 => 0xfffffffffff0000000003ff8003fff000
  | 5 => 0xfffff000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8888603020220486a042884128000124109645
  | 1 => 0x34508300420d2108520112aad043449046481a
  | 2 => 0x5d412551001748127495802c185850e10b8a8c
  | 3 => 0x248aab5400024892a254023802b02b00560
  | 4 => 0x40eccd9989278000c018043ad8003ed6000
  | 5 => 0x66678008110100401030060883f6fed8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36372
namespace PEqualNP.Outside.L_meta_36372
open PEqualNP.Outside.L_meta_36372.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 2 := bs1_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4 := bgb_4_0
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
theorem bgb_5_928 : Interval gbAtlas 5 928 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 947 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)))))
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
theorem bgb_6_2784 : Interval gbAtlas 6 2784 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2785 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88fefefeaafeeafc88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124202 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36372.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.and,[1,5]⟩,⟨.or,[2,7]⟩,⟨.and,[4,8]⟩,⟨.or,[0,9]⟩,⟨.or,[1,2]⟩,⟨.and,[3,11]⟩,⟨.or,[5,6]⟩,⟨.or,[1,13]⟩,⟨.and,[10,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36372

open PEqualNP.Outside.L_meta_36372 in
theorem PEqualNP.Outside.L_meta_36372 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
