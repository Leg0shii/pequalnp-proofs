import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36360.Model
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


end PEqualNP.Outside.L_meta_36360.Model

namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 8, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36360

namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x3000000bf42dd32df32bd42bc43be43
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x25aa421e350932
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
end PEqualNP.Outside.L_meta_36360
namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1030003cf00400014100109c3c40d000000008164014cbc43ff20fd21bf40fc43ff31fc30fd32fe43fe40fe42fc40ff21ff40fe30bd40be43fc10fd41df32fd40fd30ff43ff42fe21fd10dd32ff32fe32fe41fd20ff41bf42ff30fe31bd42fc32be41fd42fe10fc31bc41fe20fc20fc41fc42fc21fd31ff10fd43
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x448104800f82000b0013030001070003848687008405810103879d01008c800107448a0691058f080001000004238b800229828083000206988009800d00011500011d868007218180000206828007001480004f153329eaa4853d529075aa421cf15131cfa12653f544867ea898cfd53309ea94873d54902daa4184f553209f298837a500867aa120cf94e439ea86853c5150b3c87996714d409eaa0657551082baa610cf153109f2a6419d321079a64906b948439f2a6633d540827ca621e790d32ce21e633f54c42baa62167d5332cf298873f544c27ea89967d0b329eaa4653e51106baa6104f55231cf29c833e541033e6420cf94e41b7290613d501067aa421cf54b409faa6655e5390678a2a04f95232af298413d540879a6410d754e41ae29a219d42ccabca61957d4d40b6a9663bb50502bca7214f951209eaa2415d538cb3a64a04f94742af29e433c544c33886184f95231aea98213d548c2dca4084f950209f28c873d5210678a910db94b319e29a853e5410b3ea6a0734cb209e2a24376510827ca810e715132cea12653d5090f388698cf550109f29e855e53c82daa4084f94f40b6a90873d54cc65aa421cf14d40cf992819f544ca7ca3a04794e41aea9e413e5110e7ea0a15b14910ce9968179500867ca8184f15132d6a12659c43ccb9a6510d754f219f28c833f540c79ea4994f952309eaa0613e540cb3886994f952209ea80873d54c86baa7215d944309f2a421b6511067aa9085794c219f2a6436e5210edea4884f55220baa88613f5250278a9985794c42cf994839d539073e65a067153329faa4438d424ca78a818d714d40d7a9285ce424ca7ca8084f151108e29a819d329075a85194fd5110afa9a215e530439a84996710e30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1420b10c20008000100b0201c044068004b98400004061b940c394d5210e1c6355120a3592424ca39601503187588535022d6214d40c310d520c30d524cb40c3988535028c6550932c398d5210e0d6214d40c510d510c28d6294e418718d548824d6214d40a3588535028c61509328798e51d0a8d6210d31a358b54cca2c65509328758a539061c65cc9408d185544828d6210e3087594430c21f65cca418b58854cc30d6294e4187d95329068d6210c30a3995424cb0d6214d408b58a539060d6294e41a3d81424ca3661d5332c398a539070d544cb208718d548428d6210f318b588540c70f544ca218798f544869661d53328798f54c421e6394740d24c9500861c6354041c3549321064d6294e41c3551324821c654c9408718d50d0a8d62153328798f540c70d544c821c310d52cc61e63d5221
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc00001409a06b94c728e81415c8435443081ae531ea98840d7298f54486063b2a899241415c6635484381ae431aa020c0d7218d548424338ccaa1265411c5544c920
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/83+packedAt s1K4 (4455+(h % 83)*8) 8) % 165)
  | 3 => 2*((h/34+packedAt s1K3 (2280+(h % 34)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s1K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 2 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 3 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 2 => 0x212108848148040a0a20841220849414312512
  | 3 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36360
namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x770602b0400c61460810000e00070822d1ff42fe32fe41fd40fd10bc41fe31fc20fe40ff40ff21dd32bc43fc32fd31ff20bf40fc43fe21ff43ff32fc42bd40fd30fc31fe20ff10ff30fc30be41fe42fe10fc21fc41fd21fd20df32ff41fe30fe43fc10be43fd32fc40bf42fd42fd43bd42ff31fd41
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc1c800f020315093000801103801604000303800605d08183000a000001812035800a0204802401240000800100008100000002810080800001820a81002e8080138c800181008a018300b091030180880783810188828bf34cb20b6a90616f52442bca7905754c429e2a2213d521067aa520cf94e439eaa0213c535033a84994f54043cf992819e434ca7ca8215794c218f29c83ad424cb3887185b54b319faa2616e520c27aa9105d94430ce21e659c434c67ea0a14fd52219f2a0613e511067aa1a14f94742ae29a813e54882baa790cf950219e28a815d530867ea8995d544209f29e813e541027aa121c714d40af29865cd424ca7ca7a14f946439eaa4659c434ca7ea818cf552309f29c839e539073aa720e74ca41c6a12653e519073e84996d94441bb288413c54c433ca621cf55240e7212655e5310a78a8996b548439ea84839c54ccb3a85994f55210aea9c853e540cb5ca421ebd49429eaa6639e43ccb3a6420cf54b40ae29a213e548c27aa421cf953219f2a4653c544c278a910cf95231bca80439d32d02bca6104f150319eaa0419f544ca7ea99973d4932b7296633e54c8376a0a0734c9209e28a85ad428cabaa6084f54a439f2a6633f544c79a6410f34ca219eaa4635d539067ca221cf15131bd280435d53c82bca790e74c9409eaa0653e51d033ea6a04f55321ce2a2653d5010678a99967d0b329faa6615e5390a7aa9214f94c43afa9a213e5310678a890cf15330ce218613f525027aa9904fd53109f2a0216d520427aa89067d53329eaa0435e5390678a6a14fd5110aea9c659c43cc67ca8104b54843af298216c52442baa6105d54430ce29a819f32d027ca90857d4d409eaa0616d5210f3e6420cf951209faa2439f32906dca421db94810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x400600000010000100004e9c0046000b8000004000204004000300104000000000100000000d00000208400000087d95329068f60509328758a539070d544cb20a3588434c64d6294e418718d50d0a1e63d5121a3588535030e6214d40a358a539061e63947408b588540c70c43548308718d548428c655093283588535030e6294e41a3592424cb0d524cb408b588535030d6214d408718d548830c4354b318b58854cc2396015031c358a539070f544ca218798f540c62d6294e418b195424ca1c6354041c394d5210f0d524c84187d97329061e63d52218358a539061c654c940c510d510c24d6214d40a3588430c21d6214d40c3551324830d544c8218798f54c421c635512087197325028d6210f3187594430c28d6215332a3185424ca8d6210e308d185544823661d5332a598754cca1e6394742a358b54ccb493254021c398d5210e8e6550932
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x804002402063b2a899241415c66354843a08e2aa2649040d7298f54c4206b90c6aa421035c8635404181ae531ea890c0d7298e51d024338ccaa1265415c84354430
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
  | 5 => 2*((h/23+packedAt s2K5 (800+(h % 23)*6) 6) % 50)
  | 4 => 2*((h/90+packedAt s2K4 (4455+(h % 90)*8) 8) % 165)
  | 3 => 2*((h/62+packedAt s2K3 (2280+(h % 62)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s2K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 3 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 3 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeaaee88eeeeee88eeaaee88eeeeee88eeaaee88eeeeee88eeaaee88eeeeee88eeaaee88eeeeee88eeaaee88eeeeee88eeaaee88eeeeee88eeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36360
namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x30000c1470870990030411c155f0004c0009fc30fc20bd40fc32ff10fe21fc40ff40fd42fe32fd30fe31ff43fe41ff32bc43fc31ff41fc41ff21be43ff42fe42fd32fc10fe43bf40fd10fd41fd31fc43fe10ff31fd20fd43ff30fc21ff20fc42fd40fe30fe20fd21fe40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x217c54042fca9986fd0030ee99661bd51502fca0186f90c41df218857d5190f7887a05fd4e10beaa041f5210877ca321eed4140f7996437d518cadca518df94f40dea0221be31d03788698df55220bf28821f7514c3de42905f15130bfaa041bc31503788720dfd5232b6a908376510c2fca0195f14910dea16817e53842fca7215f14810df284877f53c82faa6107b8cb20bea86877e51d0efea9086f14a43bf284657e530c77e42a06f085409eaa0217e54ccafaa990ef48540bf2a0817f54cc6faa8195f14141deaa041be43d0afea4085f94040fa90a217e538877e85a05f55031df21c65bd54843f480206f95021de21c417e51d0b7c64a05fd4943bf2a263be4250afaa5885f54e209eaa043bf401037e64a04fd5132df21c43ed214837e8621ef10e42bea9a437e54c837aa8085f94c42bea9c43bc43c8378a9985d54420bea9063bc438427ca721ef0c940df21a61bf400837aa021df95043f721085bc53502eaa2215f94b109eaa441be430c2fca220df94910f7908437f52506fea810f7d0e43bea90617d52102faa8985f95130dea06617d5090bee4290ef94c43bf296637c53886fea2985fd4d21de21821f431486faa521ef90b40df21c637e500837a65a05f95230aea98217d53102fea2a1ef90d42bf280217c504c6fca7886fd5130fb18863bf54486fca4215f54e31dea1a813f54cc2fea2a05f14940f690843f940102faa9985fd4d10bf29041bc43ccb7c83a0774c030bfaa665bf408c27ca8105f14d41ee990657f544c37887a0dfd4532fd100417e54486f8a810fbcc921ef98863dd53043be61185fd4d42ef98e61ef4290afaa5105f94630beaa2437d52d02f8a9996f55220dfa9e817d54ccafca621df94210bf29461ee32482fea4986f90c40fa18c43ef524c2faa5087d946329ea8487bd400c3d86590ef105409eaa463bf40c42fca610ef50c43dea0a817f52443ec42885f94d20bfaa641bf52503ee82a0df54e41fb880217e544837c42a05f94732bb288853e54102f8a8106f10c31df98e817d52907de40106fd0441dea84877e51102fca71077cc631ba28a61bd52d02fca190ef55232bfaa621ec324877c86105f94221bf28e61fb409037e81207d88421bea9e43bc43483ec62885f95310df2a4637c54882fea898cf55210be2a2413c54486faa1995fd5221f6a9463bf5210fbca6106f10d10be28a417e544437a8220df54043bea98217e54842fca1997d50521baa8c657d54cc6faa1a15f54021fb884217c51502fca2105f54a319eaa041bf5010ef8a0a1ef90d32fd884217f540c6f8a898ef94f40bea92217d544cb7a84a0fbcca32bea8e816e5210678a8985fd4520bea90217e50d06fca9107dcc610fb90c437e54043daa4186f90e30bf28463bc43087da65907d50441deaa043bc425037c87886f94843
  | 1 => 0xe314c6fca518df94430bf29061bf40442faa7206f50230f729463bf32d02fca7206f50220df21a417e53c837887197ecc230bfaa243be54842fca1185f14d10ef21887bc53d02eca2105f54a40bfa82857d528c2fea6086f10e21bfa9841bf41907de64996f54740bea80853d5010feaa2216f08740df2a4417e53043f260187b0c820bea9687ed4210afaa420dfd45429eaa4617e5090efaa0197b4c832de21885bc54486dea4987d94430f799441f521c437886986f151329f2a021dd314c3be64194f15131df20281bc430c3f640904f95220fda0281ee20482faa3216f14740bea8881bc5190edaa518df15331bea80837c54c86fca6207d84110dfa8281bc4350afca210efd0740bea8443bc31d02fca6105fd51329e2a661bd4210b7ca8085f94a429faa263f510043788718df14d20b6a9021f73148778a421efd0842de196817e510c77aa221cf95231bf28c81bf5110ef8a2997dd0641beaa0217d538c2fca818df95132bea8e41be4150378a021ef15131be28285be5010efaa3105f54743df29681f910042fea7106f90d10bea8463bc43d0b7c84a07b54810beaa043bd53502dca4086f90c21de90e81bd43d02fea8905f54c42b6a9061bf40cc2faa7a0fd54420bea8e617f548c6faa421fd4c510bf280637f54c86fca721df94241bea8e65bf5090fec8290ef50210dfaa2637d54482fca998fd0c610de21881ee52042f8a8195f54420fa98863bd40c837ea2a05f151109eaa4817f5050ef8a7885f54b30bf29087bc52502fca7a15f95032df21e657c540c37886105f55242bf29a43f4514c27aa9197d0c410faa8c65ed21c837aa918ef90f41bea846576518cafca1205fd4f21bf28087be43502fea9985fd5110dea0021ee42c877c8618ef94740be282657e5410b7a62a06f90541df29281dd4310fec8220ef10740dea0e81be43c86f8a610fbd09429e2a265ef21c82faa71977cca329e29a817d500c6faa198db94830fb10e217d544c77e86a06f94443df21a87ee424877c87985f55231be29e417e50106f8a918fb0ca20ef99261bf544cabaa6106f90c32de2a26175510c2fca3106f10e30de21a657c548c2fca8105fd4141fd18061bd53d037ca2a07dcc621df21a433e540c2faa121df14d21bf29a21be5290f7e85217d8c710bf284417c548cafea6905f94642b6292617d52cc6fca9195f94a41de21483bf404c27ca9195fd5030bf280437e50cc67ca810df14e10cf298877d52d06faa221df14543de21e217e521067ea890ef14540bea9c217d534837c43a06f90841bfa9a81be540837aa8186f8cb40fb98c637e5110afca620df94342dfa0a817d518c2faa9905f55030bf29c837e54c86f8a2985f14c10bf28887bc43cc77885a06f10e40be2a063f641886fca5986f50120df21a837c54486faa90877cc030bfaa
  | 2 => 0x8c0118601000000121b0061c0e40e00c00814030020683e09000001000001c069ac168102d800000001600e009f200800058080000c0a0020b026000000046e0285800800002681780000088078022d80400800120000a016178742e0c41b026018842f0ec03876048146e82e039ca7d8ed1301809810110020a8540b82a0180a028040600e070260387e000182780a0191a0103e00016034da03000130060981c1180201016150163e010010045e02602804040302b82000038040f8018020101a001bc000380283800894240003683a008220000a000000100e00812020003d008e30080101401804228320001e0705c01806000745505e26064000400018c01014068000000009036100002a0280e806168000991400014000482d8e2080360186a4e83c0007e4480ca8027120e2000020080a000240804a03006160000706c0502608900098082a834001801d0380081606000040000115e2e8067e01600050288ec000be006fd0220bea9843f6510837a80986f14243dea8c877e52902fea498ef50b41bea9c853d540c3ea63887dcc410bf28865be548c2fea090f78c932beaa2217f548c2fca4086f10d40bf296877d548c2faa3085f15330f790c43dd324c2f8a5886f90a41beaa621bf408437e81905f14542ee98863be31503bc60986f90f31fc900417e548c6faa7906f54940bfa9e213e53d02faa3207dcc531de21e437f538877ca9196f90e40beaa4817c524c77c87a06fd4643de21e617d5490f7e80086f50940bf28c43df4350ef8a5087ecc130bea9a217c54c82eea2987ec8220de218657e52d06fca4195f14943bfa9843bf54cc37e84a05f14941f6a1643bd31d037ca6a06f90e41f6900417e54107be62985f94f21bf280857e530cbdc4290fb8c832de21a43ef20882faa120efd0f40dfa1683f5510c3ba63987948421dfa96817d50d07dca420fb54841bfaa4417e518c77ca8186f50040be282437d53c42f8a8995f94343be2a6217d548cbea8310df94821dfa1c877d54886f8a6105f14e20be29a817e518cb7c87216f90e20dfa94877f504cafca3905f54c41bf29861bd40082fca7a0ef55230de210837e528437ea3a05f95221f629261df32cc37aa521fec41109f298877e5090afaa2217b4c920bf296817d54906bca6086f90e10bf28c87fa10042fca5195f94840df21e41bc43106faa510df54742f6a12437f540cb7e84a0ef90d31af298417e51d02fea5086f90c10f729061bf3150378a5a05f94641bf29487bc43506fea098df14d42bea88653e548c2fea4a07794c10bea88617d50c86f8a9085fd4b10f799041bf4048378a221df95030bfa9a837c53c867ca9086f54843be2a443bd40c43baa6105f54f40fb28885bf535027ea8985f14930bf290637e540877a64a05f54f42df90e81d
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x754ccaad62d4f408f996325031e63153308f593530863d6015131cd90d518ca3d64943329b588540423e6510d31c754c43c863d64948329ed9510043654254442d5185530432d52500308f194434867661d5232c794e439067661149408f992500426d62d5231ad584429066e6215231e9551210863f6510e20ad98452d02b56110c418f990504c675650c410cb10e520c23c6454f21cd54441d036754484219b195324823e64944319e580540c6b76154d409d58652cc23d6494431cd10d510826f65480208fd9153882e5628c4318f19153086796015032e690d300c23e64d4810ae5805110e3e64d4a108f59421503555354420add8552502ae62d4f408f990540834d530cb21cd145404c23e63d5121cb10c524c25d63d53218f992534866c65509218f596540863e6414c20ad984525031c530c940d994a510c33654946329b98b548c67561d50308fd96430c32c52509408fd81540866f65484219798f548863d6414b10cd952510c2b96090c309798f54043643254420c754c430833554884218f99353086e46250521cb150524c23f6550c43ae58051d027661150309b588504c73551d00309b59652043396015330d9549100427661d50208fd9153c433651d00209b588540c74d53548109b58b540c23d6095232d99095110b3654544308f59632d031e53d0020d3189530823d6590c21cd551510833754d4530c7d4c434423f6510c10ad5865290e3e6494b31c794e43042b96010e20cb549400423d658c7408fd95400832e4354a31cd551518ca3e65d0941cb552520c23e65d0d409758c50486756114132e310d320ca6d6294643d354c32082ad6214740ce58354cc23e6590d218f99353c863d6494b318f98e548832e5494810ad98632d032e4394a31cbd4b404c2b96010c308f582540873443944208f18d54842bb6054940d9949510c26d6214e108f59353482ae62144438f992544c71d5454c208f19153c423f6510c20ae58353d025f6355120ae58052d03344394430c714c43442b561109409798f54082b960d4740cb551520423d658c540cb588544866e6215030ad58753d02b56114043ab98a5190f1e5454c10d554c310425e6315020d594d510832e43d4930ab588415023d6494b30c794c431033443544308f592500825e6315010cb553210863e6415010c794e439033643944428f99632d023d60151328f195315031f6454c20a798f40cc35553944209d986544c23e6395210cb951528c67461551209718d524426e62d50309dd85534432e5454830d955121086756115232cd147404c27661d50309d984504cb652154021d394d52043344394632c794c43083364354420cb10f524c23d64141218fd9532502746550521cb90e520c26e62947308fd9153442e5618c9209d98652cc23d6494032c714c315029c6350330
  | 1 => 0x823c65501309d19521442766115021cb10e520423f6454e108f99251cc36653484218f19152c431e6394c43c714e435066e6214e10c754c430431c5390d42abd89515023e64943328f98c5448755530c621d9d4b514c3673254420ae580434432e5250030d914d210863c6315130ab98841d026d650c820d9d95210863f6454b10e910d210863f6454d218f994434ca3d6510e208fd9531d027561150208f582548c73551500208fd91538863e63950109758f520427561d4f208f59740042766115320d954941106b661109408f59052842776155130cd10d518ca5d6594c20ae980315023f6510e108f583544c76451485208fd81548ca6d6295130c794c43d026f62551108f993538873454905218f592500c31e53d00109798f520431f6454c108f99052442b9600c5408f59353882af6254d408fd9153042e5628c710cd90d5110aad628c740ad9845090e7561d52328f992544c23f6590e10c754d400836552cc6318f590538423d60151219d996314423e64947328f594438426f6254d109d984538823c6454e21d354f320823c6454910cd55121086ad6210c42ab98b5190f1e5310c419b988515023c6454d208f19153c82e5618c832c7d92530833651d0030b918542486b56114843ae58053d023d65950208f59251cca3c6454e108f592500432c4394841d314b324c26e62150319b98a544c2b96010d209b988504c67a6014c219b98b53c42b56114b408f99250cc66d62d53319798c52842e662cc5219b58b53c423e6494032c714e435023c654cb409dd85544823c654c7409d9865290e766114c109798c53082ba60144438f18d540423d6494221cb10e528c67661150208f992544ca766114810cb90e521063d64141319758c54042b661148438f596540c2ae628c7409dd95310c67b6054d219e580530873754145308f191538826f6254d209758c528426d62153108f594430433651500308fd9153082786054d219d584530823d6494231c794c430432d52504419d584540c2b96094940cb951520432e5494830cd5445110f2c4354a318fd91534823e65151329d597310423c654c940cd545400c23e6508540ad98632503365150020cdd465190f1e5310f42ad5875290f65520c410c7191530823e6510d309d987530873451505408f596430433551d0020b958a210872d5214b408f59251cc23f6510c308f191534432e43948108f992500c63f6454720ab588515026d6214540d5147314c26f6550842ae9805210f2c52d01308f992500c31d5390c10ad98442d023e6494b309d586544c2ae6214540c794d400823e63151309dd9510042bb6054540cbd49404c27561d5020e990d210871e63d5330cb552528c6b960945408fd9151cc2776154e208f596325023f6055231cd10e5110a3f6510c21c754f40082e661cc9219d98
  | 2 => 0x6590c10ab9885090f354254442d954a510c25f6354910cb10d521063d6414520cb5485210e3d6590c408f59053042ad62d46438f992500863c64544328f191520c6b66114043c719153042b56110b40ae58243cc23d64942328f58154042bb6054d40e9191210863e6494231a7d8d515023e64951219b98854c42b5618c9409d185534832d5494810d954a41106b56114940cdd47404c33643946328f990528423c6454c108fd95411063e64942219b98b530432d54548308f590538823e64d4e108f59353487a642905218f195215026f6255130d914921c431d5454c10a718d404c36732546328f594430823e64d4d21d9549510c32f5294a438f59654042ad6214043e9951210866e62150218f59352842b661d4f408fd9643086b96010e10cd952510836551480208f990504cb6752145309798c50486ac6254d409e980540c63f6550040d354d200823e64141218f597400c23d6508740ae58043cc2b9600c940d394e52042b661d4a438fd9153c82756115032c7192530836551c80208f99353c426e65cc921cb55121087355114540cd10f514c23d6414c21b958a314423f6550842ae582535031e5494c20ab9885010e3c6454c208f18d548823e65087409b189544423c63550208f59052442b561142438fd91520c74d53c8020cb548421063c6454b308f593538863e658c740cd90c514c33443544428fd91524433a54500409758f540432d5214940cb94b400431c538c940ae58352d032e43548309798c530423f6454c21c794c43c866f654c8328f18d540871f6494c10cd951518ca3e6494832c7d4c434836452d45309d984540ca6d62d4c10ad98643506e765484218f590520433742544428f996434c23d6494d219bd89538425c6355120ab189515023d64d4f218f997404c23e658c540cd552518ca3d64d4e10c794d400426d6214c10a718d525031c5310d2097d95310c69e63d01308fd81540425f654c832cb149404c23c6590d21d5545300c35553cc410ab58a315035553c40109d195314427a6015032e510d310c799404c0308f590530831d53d00108f990530865f6550c439b597320823e6510d21cb551528c65e63d5321c7552530423e6415030e948421d02756194a43ab5885090e6e62d4c218f990540872e52d0030cd90f514c2ae6290d428f592500863e6414e109b98a5190e7b654c030ad58632d032f5414930e9509414863e6414c109d58454c826e62d5010d914921442746154e208f98e540823d6590c30ae980325023e64145209b18953842ae628c5408f59353c423e6414b10cb90d520426e6214c10ab58a5190e766115232ab98851d026e6214c208f594430c23e63950218f993530832f54d49308f19151c834d524c0309d984530825d63d50208fd95315032e43548418f593534423d64d4c208f990538
  | 3 => 0x20c0480125c04088000040b018030680702c00030061480e034000080101c0d00e700000609406024860f0010180200400018132383400000000000dc663382a6480107c350240036c000bc000242a00832000000040b03c001c4073002b0680b4d81a0bc9d000c907c000280e01c7c0a47e088de0e000000370124a074520201a0042404c16000d7008e000c0c03c2b00c00000000e8010904301804148dc01c00008f90247801c000390c000061241d0440d02c00020580202b09400048208e40c0703f06c8e02873000060002d0d80c0d45000c010c11c0085208da2090000000c018030940400c3d065af048038880005630004140dc6801c0b07c1202800004990000400006004020485207c010081d1e4020240e008d50717d00c00000080141b15c0600000614020f43aadc000282700000000cc018000100400c0f028000004200001044000340007c07010001802a0a4140063d6494031d554d10043a76448421cb54b400c23d60d5121d354b300c26e62d5331ad584421063d6494321ad185525023e65151218f993538831c6494c10a7d8d525033751501309798c520426d6215030c754c43887356115121cd552510826d6215231c794e4390ae5618cb209718d54442776154d208f99353c832e5494a318f992500823d6590e20c794c43d066d6294730cb153524c33554944308f19151cc23e64d4d208f59643082776548421c714e315023e64d4c109dd95411067661d4f20c754e430831e5390c208f994544c32e43149309b189534423d64943318fd95215036552cc4108f59353c823d6510c21c7552530832c54909218fd96430823d65908418fd9152cc27b6550040a718d5150336545442097d95300c26d62d50109d58754ccb344314530cd153514c27b6548020ad9865290f3554544309d58753083a521085409d185544c27661d4c208fd9532d023e64d4d10ad185535032c4354830d954b100423c6454d21c7952530432d52908419b996324831e5310e21ae5805210f4d5394810cb54b400431e5310c428f59352043645214530c9551210863e6515131cd54451d023e6590d328f996434c63c6548740d594e51082ad62107409758c540823d6414132cd150514c32d5210b4097d8d544423d6590e109758f548873643944309b98852043364354430c795153082ad62144438f990520432c43548108f992508cb1d53500109d584525023d65d00209d584538823d60d5132cd90e510835551cc0309758c520425d6594c109b189544c23d64d4c108fd9521d026e62150108fd9540042ae62105408fd91510ca7665cc5218fd9153c863f65500309e596100423f6590e20cb54b411063e6494321cb949400423f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8f04700400e0511010d100f10b588180002196001000240c34c6b00a9986256548421d021cb80ca21a43491c95114540c4aa4b08a4a051473544515030c29ac021a41895895114740a4eeb21a4210e25625445110f12b16a328c874a5c04354830a4ae229284a0629525805210e52ba4c598a43491c55214940a4ae829a4210f1151501300c252ba4c399243495c4435484194ae530c86a0c1c7359421502923b2a890843895496114843a4ae8292428852671d4a5290f13a92c3294878518c5150130c62a2b00a221d267655121086923aa4210a81495c84354442a4ae428a82a050c735485250292ba0a290a418614d6010d10a62e021aa21852575951210870629cc518a81499cb5194643c4aa4b08a5a052770551210869239aa890843585c05348421c28a730c64a0625625845448784a928098061895496110b40a4aea21a4210d257414921c4312b2a4210a8189589511454094ae331486a160c63149404c2533b48690843895895110740
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x419000a0483549611494082487595210854082686dd64348421906839d95448421a04835952108540c04735895114540
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
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s3K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/288+packedAt s3K5 (21627+(h % 288)*10) 10) % 801)
  | 4 => 2*((h/274+packedAt s3K4 (29678+(h % 274)*10) 10) % 781)
  | 3 => 2*((h/32+packedAt s3K3 (2744+(h % 32)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s3K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffe1fffffff81e1e1ffff87fffffc07f1ff
  | 1 => 0xf07ffe07e3f0ffe01fe3c3ff8e0f07e393e93
  | 2 => 0xff83fff803ff0fffe003fc3ff00ff83c1cf1c
  | 4 => 0xf0003fffffc000ffffffc003ffff0003fe0fe0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1000204100800004040484401281420025025
  | 1 => 0xa251a4432452989610b21629c842a15a192692
  | 2 => 0x4432a8890ca489aab21026a2d204cb0ac18b18
  | 4 => 0x60a511124806224d25248003249602116c0dc0
  | 5 => 0x88c621dc7138ccf1d9d93b3040188c63b7f000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefea8a8eaeaa8a8fefea8a8eaeaa8a8fefea8a8eaeaa8a8fefea8a8eaeaa8a8fefea8a8eaeaa8a8fefea8a8eaeaa8a8fefea8a8eaeaa8a8fefea8a8eaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36360
namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
def s4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x8006521ea43bc87690f621
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2950a21
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*4) 4
  | 3 => packedAt s4K3 (i*15) 15
  | 2 => packedAt s4K2 (i*26) 26
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s4K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt s4K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt s4K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfd99fe39cff07f
  | 1 => 0xfffffffffffffffffffffffd7e1e4fc1f73993
  | 2 => 0xe7fe073fe07ce1c
  | 3 => 0xfbfff83fff80fe0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404220008410025
  | 1 => 0x289509244a2a892
  | 2 => 0x19115069424aa18
  | 3 => 0x60002921000540
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 15 s4Pos s4Neg, 0xfea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36360
namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x440270020c00021400c00009c40943840510c2fd31ff31fd10fd32fc31fe30fd41fd30ff40fc40ff42fc32ff32fc21ff30fd20fc20fe21fc30ff20fc43fe32fe42fe40fd21fc10fd42bf43fe10ff10fe43fc41fd43ff43ff21bd43ff41fe31fc42fd40fe20fe41
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x617d52c42f8a8885fd5130fca80657e54842baa6105f94a31fd88421dd310c6f8a9995f94e10be2a641be540cafca4196fd0e10dea0a817e54cc6fea8995f54e20bf2a2657c52842faa020de54032be29c417e5310fec20885f54443bf29861bf41106f8a4a05fd4d41bf298817e500c7ee8320df54e21be29a417e548c37c85a0fbd0942bea9a417c53886fca5185f54f21be29821bf438877aa8087d54432bb28c856e521037a86a0df14131bea9821be540437e8420f74cb30fda04817c544c2f4a0197bcc9329e2a241f621442f4a018db54840b7290615e53083da65907bc8421bf286877d508cabca6207bd0b21beaa4657d52d037ca9987d90441bea9c837f53843f240106f50e10be28a617e530c6faa9215fd4b10bf284636e52042fca418fe94031f690a41fa20082faa7a0df54c20deaa663bf43443ba87985f54f42bf2a2216e520c6f8a9195f54c41f6a9063ee42483f620887d50710dea1c437d51102fca5205f54843dfa8a877c54c867aa8105f94821be2a043f541107f261085f54742dfa18877e50882faa9205f55131f6a9061bf40102f8a6a0d794c10beaa0637d538c7ca4210df94420be2a2656d520c6faa9907b10921dfa1485f710843daa520df14532bf28c653d540cafea898df54021bf280417e548877a86195f54a20bf288657d51cc3ee6298df94c20f719241bd50d0efca021fed0140fb18c437c51482faa321df95032beaa4417e54087bc8621fd106219eaa6657e5410fbe86a1efd0740fb10e2176510c37a8621df94a41aea9881ee4210adaa520df14931bfa82833e54cc37a86885f94441bfa8a657e540c77ca81077cc930fd184217f53482fca0207e84010bfa82437f53c42fca5217b4c921bfaa6617c53502f8a6a17dd0541be2a661bc51d0e7ea8885f14930bea86657f54843eaa3215f94c10bea8087bd42106fca3907d94420fc982217d528c2faa3215f54720dfa1e21bf438c6faa110fb50920be2a6637d520c2fea8105f94631fb18a21bf42d037e87995f54740df208817f54886fea6085fd4131bb28881bd431037884205f54d10faa8861fa500caf8a9186fd0c40bf29e857f54c42faa0215f952209f2a0217e50086fca7886fd0f20dea00817f54482faa7195f95131de216837e5090bde42907b48020bfa92637d510837c84a16f50f10fba0c437d53102fca5085f14121bea98437d5090bda84215fd4542bf2a6417d53c83be6519774c030df2a663bf419077aa5a1efd4143fd182217c50506fca8184f55010de20c817e52d0efea9186f50e31f7102417d5490efea2985f55321dea82877d52d06eaa2205f14f21fc880213d54cc6fca110cf95020dfa1a61ee520c7d88590ef14343bf284873d5490ef8a9085f943429eaa4437d54c437a87996750d30efa1c87bf43d06fca5a077cc530
  | 1 => 0xf43d02fca1995f55020baa8841bd430877a87186f50a41ef29881bd4210bee4310fe8c030bfa9c43ed52102fca1196f50441de28a87f521c42fca3996f50e42bf29c877e539077aa910df54610dfa9687bd430437ca4a1df55032bea80637f54c87ec6290dd54642df28687bf434caf8a2a1df55332b729483bf43cc77a8719774c530ef98061dd53043ea6310df95330bfaa465f521086fca3186f90d43fba0a437f53c83e88290df54a40bf2a243ee520c37e87985f15131bfaa221bf430c7f480205f54b30bea8687bf430837a84a05f54341bf28e81be42506f8a8085f14f209f2a0637d548c77e8790ef55321de296877d509073a87985f94d10dea8e877f53c86fca710dfd4c20fb880217e53482fca690df14d10fca806379500c6fea0a1ef10a40dea1e637d544827ca8186fd0d31be298437e53106fea2a05fd5032bf29081bf43483da43905f94e20dea1e617d518c2fea610ef55031dfa1c41be52d0fea62886f50f40bea8e65dd531037c83205d544309eaa063f721487be61185f54a10bf29061ee32c837ea6a1fec8120bf288217e510c7f641107bcca32bea8c81f6510cafca8905f551309f2a4437e52c43eca3217790f30fb288613e540cb7e87206f54543dfaa2417e54c43dc85906f50f21dfa1c837e52cc6fea4085f54e42bf29661bd43082fca4105f14810bfa9287dd324c2f8a918f750d30fb98c63be540c7be63987d90510bea8463fa308837a86906f50740dea1c41f9304837a86a05f95232bf284817e54082fca8085fd4520beaa4617d52102eaa2195f54e10df202817d54042fea9107b94810beaa4437e53c82faa5a1df54620bf29021f531c42fca7a05f94842bf28c85f6511037ca990ef15110bf29e837e51d0bf660984f95043eea98417d520c6fea9995f94321bf29c817c52506fca2207794c10bfaa463bd43907f261106fd0d40dfa8e877e5310adaa4086f50e40f6990657d54843de8490ef55330dea18857e54106faa998fb8cb21be282877d544cafca221dfd4132beaa043f551102faa3195f94041bf28461ed42c82faa121dfd4d10bea9c61f940102fea4a05f54a439faa241ee32486fca320df54032fa98a437f52507ba63985f14e10ef19265bc54483de85216f50c31bea9e217e53c86fca610df15221ef99065de53082faa518df54a41f790041f641c42faa890df54910bea9443be415077884a0fbc8720bfa92217f534877e86a0dfd5021fd984617e5410afea818cf95321dea1a657d50cc67aa990fe8c120aea98217e510c37ca3a1df14540df2a6657e544c2fca321df54442de20881f6310c6fca9995f15220bf28683bd54083be6218df94210f790441be548867aa9985f94331bf28e61be42102fca8205f94621bf280613d540c2fca3a1ef94143bea96637e500caf8a0a17d50510be2a
  | 2 => 0xc60080a03808020020000400006d4026000000c80a0100a0080e0000a0180c268360f00200000000021384a0209e00000020620203c030281f80a008920900a00144001a00980e390180393a0180c050140a20800036b4000040000003c15006000221519e010021085e078006a83036800000140d82c238120f80a00004430020400611800000123501a0580a000000003800002010022d80000050160005f9e808070e103c05000028040201000006102960300002816078021d8620f8043e00010800148002a06400000058020122e05810010f0000000080001800060246b8020f8000101c0900009002002ca0400602000001c20686016038418b81580a12866478000404e081a841866100020480009816150080c80c0d01800000c70e8040220000a008963600006800570020000c0e8000981e08800008020200002002000001205a0e80e003b40180403000020400d80002154030872701a0781e0082a0401e0e00d7c5250f3ea6a1dfd4e20dea1e417f524c378a4a1fd4c431beaa061bf415037e86186fd0f42ef98c6376510837e8520efd0842bf28c817d54cc37aa8195fd5320bea9e817d51d0efca990df94e42fb18e217d54907dc4290dfd4d42dfa1a857f54487eaa2105f14f10ef18261dd320cafea6a07d88421dfa1883bf43486f8a818df14c20dea1681dd4310f7e84a07b4cb21beaa221bd4350afca5196f50f41be29a437e5290efca6196f90a40bfa8285f521442eca2196fd0e42bf280217f54042faa2186fd0c32dfa8687de314c6fca2215f14132dea18837d50c86f8a9886f14143dea1861de434c2fca918df94b41bf28843ed32482f8a8905f54841dea1a63be540c3f260186f50d30f729081bf438c37ca2a1df94042dfa1843bd54cca7ca9996fd0c10bf284837d50d0af8a58877ccb30f790c437e521077ea8887d44010bfaa061ed52042f8a2a15f54432bf28c417f5150efea998efd0e32deaa061bf4310b7a8690dfd4a10b6a90617c52442faa4085f15032dfa9287ee529077e8721efd0240dea92877e5210efaa6215f94910dea1e85ee320cafaa690df151219e2a2217d539027ca998fb48421be2a041b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x538432c54909209d984530423e64d4e219d587540ca5e6395121a7593314c2ac62541439d584548c2e765484219d984520425e6314c209b988540c2ae62141439b58a51d0f3a54540318f596540425d6315021c799153043345488510cdd0e5190a3d6414e209d98754c826e62152309d586544ca7965840109b98b540c23d6414d10cbd0d52042766114c218f592518cb365454420cd551100431d53d0f409bd89534426d6214c10d9949510c3645448421d5545300c371518c0309758f520423d63950108f992518ca9d60d4d438f59654083355114543cd50e510829d64ccb30e650d308823d65d0c31f44c5304425d63152109758c5050aae62904408fd8d540836552944408f59352c433a54540329e195304427a6015032c7591530831d5350e428f592524423d6595031c7551300c23d6494d209d58754c823e6494720cb588544832f4394830cd50e510ca3d6494c30ab98b51d0e776154d209e583540cb1d5310840cd50e510c34d5354840c798e54cc31e5454c20d554d511027a6014e21c754f43d066e62152108f99543482e562884219798c505063e64150108f990520423f6550c208f592538866f65480208f990530823f65504418f99053c863e6494e108f590534823d65d0c208fd95430c63d64944219b988540823f6550f21cdd0d510c23d64d4c10c714d434866d6215230d9549310c66e6214530c7991530832f4394810ce50d500c63d63d5120c7592530423f63552218fd91528c2766114f208f99253c823d63550308fd97438867661d50309e580534874e53548108f992520873654544329dd95210866e6214141d9545200831e5350e10e950d210863d65908409ed9510042b66190840ab992214863d64d4e21cd551510ca3d6494e10cb54a421023f6355321e6d0d300c2756115032cb552520c35553c40109798c548832d4394840cbd0d520c71d53d0c40cd909511023d6494e20c754e411027661d50208f590524c3593254032ad592214433543544408f58f544433954540329798f540423d6550e21ad98652d0e766115030cd551510c23f6550c329d58453482e561909209e980534863f65d0c1097d95300c25e6315210d354d200831e5494c209b588514c23d6494d21ced0e500c63e6414d109bd95320cb7251540329e98053c86776550441c754f431063e64d4f21c7992530831d5350e408f990538827960d5031e910b414863f64542329798c540c35b32540329d987548cb354354432cd95251082e661d09218fd95421074d53548109b588540c23d6494b109d9845050e76611503297d954310f3a5494032dc545300c27a6014c21ab1894350a3d6550c20d394e520423e6494e209b99742486e4624c5219dd95100433954940328f592534434d524c0309d19531487725194032ad58652d0e5d6314810
  | 1 => 0xc2ad64c85208f590520435653544208f99251086e662d05218f997415023c65d0d209b58b540423f6454620cb50d520c66d62d4c108f59050486ae6294543d9145214831d5494c108f19743443a743484219d584504cb6765484218f58c54482b461541438f99053c423d6494f209d58453c823d6494a31ad9845050e3d64d4c209e580540ca3f65500408f191524423d6550c10cb553200823d6395020cb54a41103655348421d6cc5500c67661150209d58652d0e5d63152209d984504ca6d6214f109b588540c7355190440cd50e5190b1e5350c219798c540833742946428f993520427a60d50328f596540c33554544208f990540caae6290640cb952520c63f6454d10cd50d510c23c6454d10c7d4d43486b661909429798c52842b761541438f99254483723154031c754d43843595344010dc4c5500c65e6314c109e580530863f6454021d954b100427465485109b988504c63d6414c21cb552520c754534c521c794d430427561150209718d52443555394420cd152414423d6414f20cbd0d529067661150109dd85544c31d5454c108f59253c423c6454d209bd89544c23d6414f109d584538835953840109dd95310c66d6295131ce952500c67665d05218f99053487354354420cd50e511023c6550d1097195434c36652944408f993524c73743544329e580540872e54548309758c528426e6214f10c7551530826e62d53108fd91534831e5494c108fd91518c27661152309d5845050f6532544328f990524c33b4354032da949500c7655294430cb5485250e3e64d4c10ce552500c66d62d50308fd91508c74d5394840da4c9500cb595348020cb548421023d6414a10c7991531032f4354840cd109511023e6515110ad98752d0e5d6594c109b988530867a6014c108fd95430c2af62541439bd954210ab66190a409b588538433654944329b98b540c63e64d4c20c7d95434c2766194b40d554d10042766114930ad185435071e5350c3097596530823e6494f109758f54083354354642d594e510823d6494720c7195434c33654944308f992530c32d5250040c754c411023e6415030cd552510ca6c6255130cd545401023e6415031ce551500c66e6294743ad5845050e5d63d5010cdd0d511032f4394a41c754f43d0b1d53d0040c7951530433943940319b9885050e3d63151108f59743c872d54d0b219e980540c7c9324c120d9951210863d6414c20ced0e500ca3e6494c10ab59321c826c654c920cb50e520c63e6414e218f597430425d63141218f99352c423e6494d10e9d08414871d5350c10ad993218863c64546208f590514c23f6550c10cd552510832d4354830c754d430825f63549109d185544c23d65950329758c540423e6414d209d58652d03565394440c7552530823e65d0d20c794d430827561d50308f99
  | 2 => 0x64d45328f990530423d6494f21ab5885050f3743546429b988530432d43548409e58053c871d5350e208fd9743083394354032d9949511023d6414f21cb952520c36632544329e980530836552d0641da54a500c6e562904419758c505063d64d4532ad98450d0e3e6494d20d654e20082766114142cb95321886ae6290541ab58a5150f674254642c754f4308399434c210c79514310f1d6494c209d58453083665294430cbd0e520c66e62d4c109b988540c799434c110cb548411036a3254032cb50e52906796014e219d984548836753484219b596520423e6414c21d95472008395434c4319b98b54043355114743c754f430432d54480208f592530427b654c030c794d438826d62d50318fd91524426f65484219d587540831f5350d41cb94b419073943940329d987540863e64949109d584524c35553944409b588505071d54cc030d9549100432f43548308f997425032d54948109b189534439943cc130cb54b401023e6494e21ced0d500c799434c120cd54740102e56190b208f997434431e5350e409b588540423d63953218f593520432c6255321ad59221c43645248510c7d4d4350a6c654c9218f99050486b661909418f592530832e5454810da549300c3715154032ad98642d065f654c431d394d521023d6550f21d9549510c2d86050d30a7592434c26e6214c20ad58450d0f65528c4319b98a544c63d6494c21cb50d520432e5454831ab58b4310a3d6395221d594d51103374394420c7591530423e6510941ab98a51d0f6452487108f990504c6746154d20cd18554887652154021cb15321482b664c85219758e544866e6214810d354f200831e53d0c208f590504c63f6550842b958a41c423c64540219d98753083986050d308fd954310f2d5214b43cd951510c2ae6214343ab58a51d0e6d62d5310cdd0e510c39b6050d30d554d510825e63148109b98854042b561d4b439d584540c3374394432cb50e520c23e6494d21cb551520c32d54548319d58454883695254031dc546500ca3d6414e10cd151214425e63141219b588504c67a60d50318f191528c25d63150209798f540823f65d0f219ed95200826d6214d108f191508ca3c6454a1097d95320cae4614c921d954951102766114e209798f520434c534c9219d5845050a3d65d0c30c754e421032e5494810cb94b429063d64141329d984530826e62d5231b95864210a74654c510cd58454442b561d0c418f590538863d6494c319d98652d0f6a52940318f99253c866e6214d10cb50e520431d5350e418fd8d540c27a60150219798c540429d64cc930c799253042ad6214343e350d320ca3f63550109ed95401026d6215210c7d4d435034d52cc0308f590534863c6550d20c754d430872e5250a41cd552510c31d53d0c429d984534832f4394840c795143c
  | 3 => 0x401406000020002b00c04010f1018041083700003004030381500c140340008c0003402004036a800060150481c0040d0080002407048070000003c00024020303c000000002e0000e09024018130003c000270200e04c2b00c0e08800100010045b0141004837004010180307c1a03c092901d02c2e044010040d05800014ae00001020220001201000024210040b0000005c000180005001004450c8021d821084090002d0988f018160003904007010070380200400000000241f0880202c03018000a80a024000240003000050011900005015004061280e010540002b004060b40000810038140001903802028390681e0b400008010a00600800010050003100c0083c0004826000070689003c0b0080f00801014000000b0140000455012390500007c150000410801001b6014120041503408000062ac60018412580705c1b0880000c030000a01c11000001241f0d0250000024818000009798c5050a7661951328f990504ca3e6494c219b58a51d023d64948218f99252c42e562905108f191518c23d64d4f219e580540c67561d4c208f593524c63d65d0e218fd95438865e6315021cd553418874e53948408f9945448278654c1209b988538435551cc0308f992530827561d5232cb50d529063d65d0c328fd91528427661d50329b5885050e3d6494c328f992528c7374354420cd553100426e62947408f995434431f6550f30da54a300c27465505108f990540831e5350c40a7d9543cc26d62d5231ab58b51d0eb66194943c794f430432c54485208f992530c72d54548109b98b540863d6590440ad5865250e6c6550920cdd0e511023e6495110d354e520423e6494c32cd544411023d6414c10c754d401023c64542318f990528435931540318f99053c829d64cc7308f990514c23e
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x180007831001b01008004000000201b1232242a8043525c0534c921a30eaa1a60885517014d31486933a6ca90843625c86050d30a30eaa1a60904d171181434c389a1aa298061585c05448421c48a8b0c849042d761532148312a94c321081c150d3254432c48a8b148288626625464110382a1aa498863075cc6454021992e4302869859171181434c30aa9cc321081c2d0d524c03086aec2a4428851975d0d300c306a9cc520881c450d3154031e1286992a0195197014d43486a2b98a890843c154d4348421
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x905839d36548421a05831912154021
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s5K6 (672+(h % 28)*6) 6) % 42)
  | 5 => 2*((h/287+packedAt s5K5 (19845+(h % 287)*10) 10) % 735)
  | 4 => 2*((h/279+packedAt s5K4 (27056+(h % 279)*10) 10) % 712)
  | 3 => 2*((h/24+packedAt s5K3 (1470+(h % 24)*5) 5) % 30)
  | 2 => 2*((h/1+packedAt s5K2 (120+(h % 1)*1) 1) % 2)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc78fe7fff0f1e3ffc318fc7ff1c387ff08f07f
  | 1 => 0x7f1f878ff01fc71fc1f1f8e1e03f9c7374993
  | 2 => 0xf801ff80fffe007e3fe01ff01ffc01f8c78e1c
  | 3 => 0xfffe0000ffffff803fffe0001ffffe00f80fe0
  | 4 => 0xffffffff000000003fffffffe0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40802000100204000000201200408040001025
  | 1 => 0x312443112224c0a20c090c8452093096134892
  | 2 => 0x90688132446049405520152094981132458a18
  | 3 => 0x200144488810004a252400109224400a80540
  | 4 => 0x244d16600ec992693b9c9a49c0306424fee000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36360
namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc0800008003021c0152a0c2800c0000112000001e144000e0400b060038002e80005c6401001ff0c003fe4100ff0c403ff10025f15007ff43027f15001fe20007f48007fd3201dfd4c05fe5201ff50c09ff5400ff04007fc43007f50009fd51007fd0801ff40007f90009fe5401ffd4c07fc5300ff14407bf4301ef50c01fd10007f10003fe21027f54801fd4200ff08403fe51007f48409ff5200ff10409ff51017f90805fc42017f8c8017d50027f55007ff32027f940017e54017f08007fe53017f14801fd4101df54c07ff31017fc8005fc32007f84007fd3100ff8c409fd50027f14007fd3001ff8c005ff2101ff54c07fe4301ffcc0097f50007fd0409ff50
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x168202ffc812002ff0210803ffd4388069bf20ca805ff596100b7fea4200c3ff6550803fe10a200edfd412009ffca4200abfd505042bbe2a68200ff58910077fca890016fc6584035ff9928022ffd5340135fac69086bfc435005dfe30a8403bf18d1002ffc6108002fd6484053ffb1a8201ff8c610025fccba100bfc525080b7fb244036dfcc25400dfec290867fc4250049bf902a005ff90210077feca90017ff64840017eb08802bffc8341017fa651000bfd5288003fe20a20049f19541017fe41a10ab7f505040fbea9a2020ff08740015fcc4a00577f43950057eb168405ffd961000ff62088003f94010051ff1928201ff4851005ff8a9080c3fc5050803fe98a8235df98a5400dfcc290073fe219006bbe104a802ffc862002ff861200cfff51d0805fea14402adf151410f7fc8720017bd401002fbea9e8027ff5952103ff8a688002fd61d0801bfb2a8015ff107400aff88620003fd21d002bbe31ca802fbc81420cffca4a0017fe504804bbfb1aa001ff90521024f8caa103bfd5148001bea828025dfcc1500aff8842008f7e4154005f62124200ffd0540167fe61a08177d6590003ff20e820cffc41200f7fca7200c7fe41d0801ffa128030ff59542005fac910006f66110003fb20e8209ff4ca1002efaa02000bee42480617fb2a8404bf19520006fca888057ff4110039ff28c8005ff98c40137fe6090806fc61508077f31c8036df4c25402ffec910003fd64440017eb148032ffcc342077faa090007ff514840bfe32c8002ff14a200dff8caa0017fe6284005ff10a8402ff081210aefec12a017fe621005fff21a842fff0c1420a77e862009bff43484013eb04a800ffd912102df8cb2001ffc4344001ffb128000ff484400affe84200027c645400bbe102a015dfd8e540dffea4a000bfe21880013fb2a822bff08341007fec09081fff324400dfe2122005bf192100aefca9a0007ff51d0405fe1924200df99150005fec488037ff3148013bfa9c2007bf58d1017f7a86a107bff319001bfe98a400edf15120007fe8488002fe6488019fe18a4009ff50e10167fcc7a0817fd63900097f32c2000fbd0921177fca2a10d77c329502bfe21e801eef50e40017dca4908db7f319502fff9968035df90a5419ffacba1017fc508800b7e3088005ff992201a6fc632a016fc604844ffeaa24215ff10b4002ff8cb0809bfd3048401beb22a015ffd0b4012efa60a80cffd54d080fdfa1a2000ff98342006faa0880b3fd30d0465fe9868404bf19521005fac1a0807ff414400bfeb242006ff94910005fac1a1003f521440017ab088033ffd534202ffac4200c7fc51d08297eb188000ff1911017ffaa6a100bfe42d0863fe18e8430bf5954214ffcc6a0817bf401002fdfa1e8000ff50a100fffca9200027f6550801fea088002ff0cb42
  | 1 => 0xbff5110003ffa0c2005ff98640187f8a8a10b3fd53d040b7e31c802dff55341197faa7a101fff3044003fe90c2005ff58a10187fea0a1002fe6448003fe28a8205ff58e20007fe85080177e65880093e32e802fff94d4212e7a86a809bbd4348435dfa1a8001ff0c521037f8c4880b3bd43d040fffb1a2029ff94d410f6fea720083fe41d002dfeaa08030df195421977a87a1012fc65440097f32e8205ff4c0400f7fa872002efd65840537fb1a8202fb8c920157fca0a0817fe204800bfe10220009f596201a6fe212a017fc404400b7f3008005ff9424002ffac910006fe6188035feb1a80009fd9521025fccaa088bfe65d00037f30c8019ff90940005fec0a0857fc63d043dfe9948000ff5912013ffca890817fc105003dfea9c8015ff953410a7f8a620017fc628400bfe30c800bffd4a10117faa9a0006fc6150029ff9908000ff58b40047faa8880bffd435080b7fb2c2001ffcc52101dfcc69004ffe42100037f30e8002ff88520087fc6310017fe308800bffa008001ff50610025fccb20017fe639006d3fb1ca815ff1974002ff86090057ff43d006bbf194a82fdfd4d420d7fea6a0077ff219005fff31a8429ef50d41007fa85200d37c1095045ffa8e8007ff4c11006f7a86900cffd50d08013fb2e8015df18a540c7fcc2a00d37c319501bff21a4000bf5912109ff86420017fc1010045feb2e8000bf9911019ffca1a1063fc2150003fea8a4215dfd8a540affe87a1016fc631006dbf31ca82dff9434100ffaa3a08cffd51d081bff29a4001ff145210b7fea820007ff315040bfeb148023df0c550025fcca2009ff55148403fb8824205ffd421000ff863a08c7ff10d082bffb2e8017ff4c34000ffc82a0816fc651002bfe31e8400ffd0110197fa63a109ffd50484657fb1e8414ffd4c400c7fc62a0016ff6484019ff28a4005ffd8a40017dc85a10b7fd50d040bfa0822005ffd42200c7f882a00abfd6550413fc9842027ff9952102efaca2006b7d5350005ff90a8406ff0c910017fa64a1017fc104402bfe30e801aff98d4000dfcc22001bfe424404fbfa824200ffd9110097f84220037fc6348003f610a4202ff5494202dfec4900d77f209501bfd182402ddfd4341015fcc50806bfc53500017e322400dff58d2010ffc85a0047fc548802ffe29e8002ff8c92100ffa62908cf7f50d084bbf98aa024df8c950067f8a290037fd534804bbe98aa001ffcc74115ffc65a0877fc5290065ff98e8401ff4c741015f8c5a000bfe32d08017eb168208ffd511002ffa4108007fd515040fffa9a2000bfd89410aff88220057ff65d082bffb1e820fdfd4e2002ff8a120007ff105042bbe2a68403bf98d4202fd84090007e42148401ff3028403b798c4002ffc8110006fc6148001feb0a8001fdc4141006fca8a00b6fd65d0457ff3
  | 2 => 0x40135fec690827ff53840057f3128221ff0cb40046f8a8880377f534801ffe21c4005bf18640007fac1a0816fc6290067fe2868405ff9411015ff8a5a0803fb4090001fea128203bf98c4002dfecb2000bff4288003fe28a2002ffcca2000ffaa28800bfc428803bfe1948002ff4862014ffa64a08db3d4395029ff9888013ff8c8400aff8c1a086f7c545000bff2024001ffc41100aefec32a00bfb208800bff324202aff549410a7fa62200aaff6550411fea822004bf99520097f86220007fc2184005fe2924202ff14b421b6f8612a003fc64480057f3108001ffcc5100affec7a000bbe42508017eb142000df58a54046fea08806fff54500597eb1e8205ff9434002ff8c42008bfd51d006dbf21ca800bfd8940077f8a89009ffc50484077e31a84009fd954007f7e871000bee3248401fe302422dff1434102efaa110002fc644406dbe98ca805ff59440017fca510003ff4188005fea12400dff50d20007fec0a089bff6348403fe20c2002ff4c9200bffe63a000afc62d042bbe2a08009df54e1000ffa6288007fb108404f7fb2a4222ff54340116fea1a00177e651000bfe30c4006ff8c910097fc822003ffe5388035fe9828007fd4c51004ff8a7080cafd63d081ffc9844005ffc804000ff86288063fe4150003fb28a4217bf58f4002ffcc310017fc5048003ff28e8205ffd42400aff8c7a005ffd31d004ffe32a4232ff90f42017fe429000efe6344001feb068426ff90d2119ffccba109bfc304840bffb2c401fbf596400e7fc632000efc6350443ff1968023df885500d7fe60a00a3fc5250405ffa944004cf9925400ffc43a0807fe214844dfeb1a42009f594400affecba08ab7c655040bff32c8032ff0c34202ef860a80977e435404fff2824205ff0814000dfac3a08b3fc30d0459ff21e8202ff8874204ffe65080abfc50504017fb0a401abfd8d40137faa6908037e5484019ff30a4000ff50620017faa490016fe60d040bfea008005bfd962000fec43a0817dd631004dff29a4205ff58e1000ffea28801bff2044001bfb2a8205df5962002ff821a0002fd621002bfe3068409ff10e10197fca7a10577c54d0047bf882a02cff94f41015f8c4a086fff51500057f3168001ffc434102ffe6020017ee6210055ff2a28201ff9452113ef8a89082bfc4284029bea98802eff8c542017fc6490057ff4310063ff28e8408bf595100dffaa8a0012fc65d0835fe31a801bff59540024fccb1000afd628800bfe1068017ffcc34010ffe41a00bfff635080bffb0c8029ffcc14100fec828800bbc4250803ff20a2029ff54d4112cfec6a8017fc2010001ffa02801fff54a40077f8ca9001fff4344005fe2924009efd0e10007fa8088012fc65d0403ff10a8215ff9534216ffea5a08177d5084001ff302420aff94a1014ffc86a085
  | 3 => 0xf30aa000dfd915014dfac6a0803ed4248001feb224205bf18e200effca52004bfe511004bbf31aa002fbc8520107fe21a000bf82048001beb0ca802ff90a20007fa8320017ff4088003f710a4201ef105410dffca8a00037e549001bf69924004bf995421b6fa872a002ff644402bffb068202ff0ca200d5fac6a0006fc61d0003ff20c2005ff5021014ff8c6a080efe63d082bbf2a08005ff04220026fec0a80037f625400bdf2028007ff90d100f7f887200b7ff50d040ffeb1a201aef50d4002fdac420017fc304401b7fb1a4005ffc40400177885a1002ed621000bfe31c4011ffd522000ffc62a0817ff308403bfe214801effcca4007efaa7100c3fc655082bffb1e8401fd885100f77e8720016fc618800fff29a2032ff50f420a7faa62004bfc511001bfc9824005bfd8e1017f7e86a1002ff6448001ff322402fff8c14202ff861a0017fe638400bfe1042000ff589410aef8c12a09b7f534841fffa9c4005ff102101b6fa652a083fe21d006bbf90ca82affd4141005fcc89085ffe43d0003ffa8c2001ff9451002ff8c520053bd431004bbfa1aa007fe8c11004ffe87080db7d6395005fe9968415ffd0f41037fcc4880cb7f53d080bbea848000ff486400aff8a9a1057fc54d0401ffb0a4000ffd0640005fac48800bfc218805ffe21a8425df50d50166fea7a080bfd424842fff29e8002ffd0942167fa87a0806fe6150001ffa148024dfc8550005f8c890802fe6484005ff9928402ff1094200ffe43a0883fe51d001bff31a400bff55210067fc6290043fc418800ffea9a201bff54540015fcc520017fe5050053bfa9a8205fb88120007fac3a1063fc5150001feb0e800fbf58e20007fcc0a0863ff105000bfe984201cff1464001dfcc6a0067fc325000bff0822031ff9874202ffca020023fe5444001ffb128208ff9951001dfcc690807fc51d0401bfb2a422aff1514103f7a868805ffd53d0005ff292840fff14e200dffaa0a0017fe304800bfb0822002ffc87420fffea5200037e60950077e31a8025df4c95002efccb08007ff2148405fe9924204bf19542167fa65a0803fd4150001bea12a00effd41200077a85a006f7f50500037fb0a8200ff50b41047feca8800efc634845bfea968205ffd021002ffacb2006fff655002dfea888000ffd8540017ee429083afd6548005fea924205efd02400bf7a87a0017fa40100077f31e8000bf59110017faa5a10bffc635080bff1848029ff50d41025f8caa086bfd315002bbe30ca801ff9454102ff0411002bfe42840057f326841affcc54004dfac708067fe3250015fe1942005ff04210006fca910033fc6148017ffaa42034df8865402ffec70800bff52508097e32a801bff9954002ffec620017fd5010003ff90a8200ff58b4102efea020016fc6284049be312a019ffc81
  | 4 => 0xc3ff5150869bf30ca80bff95210017fea490817fe4044001fea108005bfd8c4012efac6a804fff2110065ff31e8407ff50d10017f840a1053fd3210001fe3028202bfd812008ef8a910037fc534805f7eb1a8402ffd4b4213dfaca908137b605404df69924201ff4c6100cffcc4a003bfd65480457eb2e8017ff98f4002ffa81100037f655082fffa9e8016ff5484014f7e86a08177d658400bff904402cbfd8f410aff8c5a0003bf41d002bfe2a68017ff50f400befea7a00037d4154041fe28e8000ff589400077e85a00bbfe6150803ffa0a8220ff0c74002ffe812000bef21d083ffe2a48027fb5492102ffca108003fc6050839fe20c8001ff5461000ffe4288003ef4250801ff3068225df18d5002ff8c708067fc5250003fe28c201dff90a4006ff886900037e544800b7f3042005fdc421002ffe2108017fe6588003de20e8207ff18d100d5fac92000bfe4250801fea122007ff4c91002ff82120002dd6310043ff90e8004bf996201b4fac72a017fc505001bdfa1a400fffd0e2002ff8c720003fd42d0001beb0aa002ffcc92014ffc60a0846fd6588021ff20c4001ffcc610157fea4a08037f6154011fea922002ff109200fffea920057fc65d08057e312200eff9952002ff8811007bff539006dbf184a82aff99541005fec0a100efe63840057f3168200ef507400bffa65a004ffc521002bffb068401bf9874202ffe61100beff6350831ff10a8015ff19741005fac5a00177f5084067ffa868400bfd812103dfec68808f7e315400b7f3048011ffd4620017f64090016fc6588003ff18e8205bf98220057fc6508017fe611000bfe2808022ff54b4002ffacb1000bfe5248039fe10c8001ff0c61002ff8cb10012fc65d005dfe0828402ff0c94202ff84110017ff6110001bf2a28405ff18440017fa42900037d5048035ff21a8003bf98f410d7fe86a000bff4248001ffa0a4002bb9884002ffac6200cefd65d080bfe1828001bf9854200ffc629086efd6550051fe3128205ff5844000ff862a080afc625000bfb3088005bf9834202feac220057fe54d000bfe2822012ff8844018ffc63a109bfd4348441ff30e8005bf18142037f8a48806f7c655003dbea9c802fffd4d420d7fca6a0053fe5310017be2a42005ff0c040126fcc4a8017fd3088031ff28a802dff9974108ffaa910006fd618400bbf182a001bf99341137fc609087bfc5390061ffaa2842cff8c34100ff820a088aff65d0065ff1868405ffd96400077a84a0017ff20840097f32e8002ff08542017fea490017fe204402bbf324a800ffd89100a7fc8620017fc50d0031fe18a80049f99610007fa42a0087fc52d0003fb18a4205ffd884000ffc428806bfd5350051ff902822eff1054202ffeca20057fe541005fbea9a8400ff5052017ff8a6a105efe6410047b
  | 5 => 0x852102ff8a10800afe624400ffc9822029ff0c141147f864a0803fd6048451ff212821cff0c640077fea29004bfe311000bfeb0c8026df54d2113ffeca90817fe65840093e32a4205ff8c04002ff8c90809bfc534841fdea1c4000bfd9121166faa7a087f7c549002bbe21ca82cff14f41187faa0a1057fc41d0801f690a400eff55120006fac12a09ffc544842bbe214a801fd1052113ffea09080bff204844dff31a4201bfd8110017de4090803ff644802bffb168008bfd9510005fac8900bffd315086dbf994a80dff4c120007fa84a0003fd20440077e31e822fff4c142186f8a8a109bf5314841d7fb2a401bffd4140186fea0a10cbfc53d08013eb2c2002ff8c94202ff8c6200bfff31508093f32c8005ff0c21006ffea6900abff5450411fe32a201fffd464002ffe41200037e5448413ff21c2030ff55142006fac4a8047fe5488003fc0822001ff0854100ffca30806ffc545005dfe18a8415ff18742137f8c690807fe2184035fea1a8005ff8c11002df8c708002ff6150005ff2124001ef9054114efaa6a08db3f439500bffa808000ffd0120087f8a31006b7f535000b7fb1c8015df9534201df8c7a1027fe538400bff1868002ff0c920155facaa0807fc4150433fe3128015df9534100ffc6288073fe4190003df20e8200dfd055002ff8ca2009bfc4348405ff9924200bf5862000fe882a08977c4354001dfa128000efd054001dfcc710017fe508802bfe21e8211ff5462000fec6288017fc104802bbe32e8017bfd8f400aff887a10977f3254005ff9028405ff54220017f884908937c4254059ff9968205ffc4220017fe65a10abff655042bfe2168202ff10b4206ffec6900a7fc5350441ff18e802fffcc14202ff46108003f7415040bfeb0c4005ff54210007fe84a0817ff309000bffb142002ff94921024fec0a8003fe6444057ff2968210ff0c620007fac290023ff50440077e31e8025cfd0d500ddfecaa00ceff65d080bff328801effd0e401677e87a08bffd635082bfe2a08014dfd4c4004ffaa70803bff544800bfe1048005dfd4220006fa42a8027bd4384005ff1944004bf995211977e87a1007ff414840bff2008005f798c400cffe42a006bfd3250029fea188002ff085200affec3a0003fd605042bbfb2e8000df95141006fe84a80037c6454005ffa12420fffcc620005fac320057ff42d042d7eb288001ffc4121017fca5a100bbe42d0801dea0a8000fdd052107ffa63100a7fc4350445ffa86800cff1052000ffa8290817fe638800b7fb1c4005bf18840015fec8a10127e6510005fe106841bff5494014ffe64a08377d5348005f62128405ff4c240025fccaa00cbfd63d0851ff2928228ff1094102ffec7100abfc655042bfe316822fffd0d4203efea68807ffd5490011fe2a220049f9925402ffcc520
  | 6 => 0x20b800ab10060181c09401c0001e80001a0b0250b101207c078043f603c168181e8004e680183a3c0020003ae000000340020000bb1804c1bc0c81a04a0f80302701c13c5b80f0020000801d0500090d01e1280180f83033e14c1e80005405c0d00502478c04000000018048030121f8122b98f60840100000002c38003108a8c0980009a7515781000607c0886e00204802004000000000000721fc0280900002c4c0000062e0064c11dc0141080101a07c1b8050083c0000054344ec000000121681280d004044a780600002c1680a00a0922980c008db00900b0220244600400230c0582001600c001bd1ae06c0502900400c11802060070009ea00406c458430080300f0032320080000c004034408091ce0001a801628c7c0082e02206c02000002008000000200000084f04a0080000e01e14c0280301c174018060180201202a04eb580000800e00db900400440c010a00021245d0002b2000071950100005600800603df000501a0240104c006014000060eab500da9e0001340b8030001480100200604c009b601c0700800006e1c8910000000001b0010022285c8450040580b012010008009010080041a89d0000840e8af0280001180300a000500010320042c8cf0cc0580019a0000801512b000bf04800401e00c488790e84540d0000000000503e187fccaa1007ff2184001ffb0a8421ff94b40147f840a0803fd6150869be10ca82dbfd974114ffe86a08bbfe415085bfeb2e8200df5434000dfec490807ff515041fff21c401affd8d400affe83a00b3fd63d0465bea9e8400ff191210bffac7a0016ff6510017fea942024df9095001df8c6900967d63540093e32a8026efd0d2115ffc85a0817fc308804fbe32a4205ffd8e40047fea488017ef2088049be192a002ff90921157faa8a087bfd319000b7e324402bff0cb410fffaa3200177c1054003fe0824215df1065402ffc60a000aff6250803fe086820cff90520007f680a00c7fc10d0803fe20a4205df9964002ffe2120003fd4048001feb028405ff1922000ffa82880a7fd30504017eb0e802effc4142187fca8a10b3ff53d040fff31a2000fd505100affec5a0806ff64504077f31a8222ffd4b4002ffaa1200c3fe505081ffea9c4000ffd814213ffea890843fe51880037e30e8426ffd4d2102efea120037ff3048053ffa9a8205ff90140005fec2a10027d6590065ffa9e8405ff10120147fcc4a0817fe208400b7e3028215ffd874211ef882a8012fe6544031fe30a800dbf58d200f5fac720007fc41d0401ff3224223df1855002ff461100b7ff54d0415fe2942000ff5074000ff8429088f7c215400b7fb142029ff58d4102ffec3100c3fd5150803fe10e8202ff0874202ff84090087fe62d001bffa1a401dff8ca40047faca88016ff614405dfe28a8401fd0
  | 7 => 0xc004c2203200e0d0628a80001f4008020020000001c26a00013b3800003cd0001212064010001020001ac820000997f00202807c2083206c008000030161c800000004490010253500040606f0000204082e016000180030760013f05600a078000080160081400707c9f40388d00c41c008127dc0100a8e000006c008488280100200302a1fc018b9004014310030723e0a609400003c410070289e4218492d40440280000c0240780100000401817002000041c1
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7119120004fd76d0910006f5515844001cfc73d81420c5bf71505402067f63952100067d645412002e7d40594400247c75591210067f53589100057f7550941016e462485100ad7d76982544ce7d72d9521004fd75587420afb743d05414457b705895010efa20d814220776109511012d7c73d0950006ef6250940006ef42d85420067f71d9542006f5315844000ebe615074002e7d50592204273f43509500067f53d85421ae7f20d95420ae7f76951100067d321915010faf21d0b400067d71596200067d4359610006f9305862002cfd74d854027def73509202367c10191502067c20d954000ebc61d07400047f75591200acfc76d052024fe9304852001cfc7358a40004fd7358341006f771591100067c73d95210457c75591100067f50d911011d7c711915002e7c2059620004dd73991210073f745434002f3e40543400063e4219150017e761d09210057c74541101b57c7358a540067d6550620007e870485200063d43596200067d73d95410ae6c54588402367e20191500067c435964002df47050510024fe7519110067e4614852002dbc76505400067e64589500063d43d95401cfe5324851001cdc73589100247c75d81210067c745961002eed20592200067f53d812100cfc74583410067c30d95210067f50991100067553584400c4ff7159110006de5158c400ad7f71586540aeed72191200ae7c40191500067e72d9540006ed624864025ded7348520016ee625084001cfc73587400067f53d91200067c54d85424d67e20d95210067d73596100067c315944002ef73058440007ad42d012002cfd74d894002e7d705962011e7e71596100acfc759912002cfe70991210067c5458a400067f659812118cff7259121007b761505400067f32d97401a67d31d9541006bf649912012d7e73d0950004fd74d8910006ee515884002dfb74500400aeec435884010ebd42992200067f65505400af3f65d07400ae7c6495120316bf635094010ebe64508400076d6248550024fc75d854002ef51058a104d67d20d952102ff16150040006bf4358b4000cfc71d89400073e64191500acfe74d89100ae7e73d974001cfe73586400067f65d85420ae5c5458c400067f53d85200067f5358a400ae3c54191201af7b20952202057d76952200af7a54d0240024fe75591210067c73d95420067f61541404c6f571d91210057d72191501a67f21d954102e7f4059640004fd755921002f7a40541100057f73d95400257d70d85500adbe74487400067d53587420066f53588400af3e54507404d76f20d9521006f6735844049e7f63951211276c4248550024fe75587420047c764855000cfc71d814202dfb76500400aebc64d01101267c21596204f67d63951410aebf43191205076c65d09420067c54d81210aeef43588400067c6518142
  | 1 => 0x51202067c6395240006bd4319110006ec76509200076e5450920004fd7558b411276f215895026faf4350920004fd71992204d67e42d952130f3c655094002cfc7650940004fd75d812102ef77058440006bf74591200ae7d76952401b67c6395110006be42d91100067f6358550004fd75583410ae7860582540ad7c74d95420077950d0140006df5258c40006de7258c40006ef52588400067f76485500067e76951210cfac4250940007ac6450920176ef2158b410067e311915002dee7048520006bf43587400ae7c64951101af7820951200057f7058654004df73589100067e63d95210073f43d91504273d43509500aef741587400067e2119150006bf54d911002f3c40543400ae7f6158254005f771509414c6bf42d91210067f32d95410ae7e545874011e7e61541200ae7f75992100067f651912102f7810541100acfe74d85203f67d6350550006dd635084001cfc73d89400067c4159620004ff76487400057f73d9541004fd73588400067e41594400c6bd4159210024fc75588400067d6550a100ae3c541911002cfe7099220006f6725844001cfc73584400063f43d95420ae7c42d974002ebf64d01401b67e63952200ae7e64951210067c70d952109ebd4219120176f710591210247c7558b4001cfe7358b400067c21d9740005bc7458910005df735812102dec764852011d7e7199150006bd64506200ff7b60d91500057d73591504d67e32d952102e7c705961002cfd7058a100767f60589500ccfd765012002eef2058620006bd43586400067d535834102cfe76d0a10004ff74586200af7654d05410067f70d954100dee71d092116e7c65d05400057d76d05500067c7359610004ff75592203fd7f7350550006f771589100067f20d954002e7c70594400fe7e7459640004fd7358440006f731d85400ae3f43d97400af6f6258a5400cfe71588401b67e6395240004ff7058b41006fa30d89101a57e719825402f7965d0240004fd73591100067c41d95420acff73191213973f50d074002e7f2059620016ef6048520004ff755844002ebe74992100457c75d0110006bd43191201257f725895011f3e41d05500ae7f40582544a57d73951210af3e6458a540ae7f435825402d7e7048550006bd4358b4002cfc76d0a101276f20485500067f21d97400067c65991211167e76541400057d73d95210067c41d95400067f7558b400a6dd7458c400067f43596400ad7e74951411d7e552485101877b60509500076f72541200af3f43951410067c54589100247e76d95401b67e63951410eebe76d09400aebf4399121006ef7558840006ed435884002ebe4099220016ec6250940007777548510024fe75591200477b605855002f7a65d024002ef470584400aebf43191100ae7c4358254004fd72d85400073f4154140004f
  | 2 => 0x67d53591100acfe74991210067e54d8142006fb70591200067c54586401276e425412002ebf4058440006f561484401a77441951210057e76505501ae7c74d95421257c7219150015ee74d09210067d4359640024fe75d81410057c76485500063d43d95410063e41191501bf3f43541101a77641951100aebc541912010cff76508400267f76541100ccff7259120004fd70d912121d7e76d954101cfc739912111e7c71596100057f73d89500aef74258440005ef72501200067f76509501a67d41d9541006ec515884001cfc7319110006f5545844011f7621d05500057c74485502067c20d9740006dc5158c400ae7d72d974002e6f50588400067f53586400077521541101257f74509500de7c74d954002dbe7050740024fc7558740004fd73d89100067f20d974002e5f5058c40024fe75d8940004fd73191210067f75592100057c74541200067c64d89500057f755854002ef860983414ce7c31d952102eee40588401276e3254120006ef72591200047d73d95214efb543d054102ef410586200ae7e64952101867e6550a402e73d53505400067c43d95420067f50d9120006f930d8910146ee42d89410c7b461505402067c61952200067f50d81210c6f710d854002ebc40992200ae7d721915002ede4058c404577750d05210067c43596200067f50d85200de7d74d95400067d63191500af6f4258a5411d7c71991500aefa6450040007e572d052102e7f405962011f747154110005bd744874002e7e40596100ae7e5458b400067d53d91210b67f6019150007e52148110024fe75d8540004ff70591210057f7558542004fd73d85404bebf41d912126fad435092011f744150550004ff745891002ef710592104676c54d09210067c42d9541014fd71d912100cfe7158342024fc75d81210ae7c54992200ae7f75191214cf7631d9521024fe7558840006f73158440007b464d05214bcff7650b410cfaf20509400067f53992200af3c42951420ae7e74d97400aeee42991204876f53d092113d7c75581210053c745414012d7c73d91500067f65d014002e7e70594400247c765414000cfe76481100057f7550b400063f43d95410067f75591100047d75d91200fd7c75486400ae7f6550740014fc72584400af3c6550b400067d4358254006bd435874002f7a4054120004ff735884012d7e73485500067f62541400067c43d95400073d43d91501a67c21d9541014fe7258740024fe75992201257e72191500247c75592200aebf439921050f6d53d09420067f63d95400ae7c71191500067d63d9542006f675584400fc7e76951400067d53588401af7b2095120086f621586200067f735962000cfe71191204f73d43951410aef860583410afb761507400acff73991100057d70d9541004ff755864002cff71d89101a67c619
  | 3 => 0xe73191500067f531912011e7c61543400247c7558910004ff72587400077b705895002df470485100067f70d9542014ff7650a4011e7e2159610006ec6448520004fd73d85200067d6495121006ed32588404267f6350950006bf43d894102edc1058c40006be6450a100ae7d731915023e7f635412002eed105884002e7d10596101a67d619521002edd1058c401bf3d43541102067f6295120007b74148540024fc7558a1002e7c10596100047c76505500077b70585500067d325961002e7e405964011e7c61d85500aebf43991200aeec4258b410ae7d759912102e7550584401a67c41d95411d6f765485100073f4399150176f461585421276e624855018cfd71991210063f64991504acfe76d09410047f7648550037e63248510086f63158620004fd7019121006bf43d81420ad7f7395141006bd43d814213d7e751812102ede2058c4002cfc70d852002fba74d024002ef450584400067c75d8121006ed6250a100067d6550a40067e631485200aef5719911002e7e2059610015ef74509200067d5358a10006bf54d912002e7c40596103873f535074002edc4058c400057f754854034f7b53d024002cfc70992100af3c5450740006bf645011012d7c735055000cfe7158a40004fd73991203757d73543400067f31594400fe7f745964000df674d054102eec40588400ac7f73191503bdbf7350b400067c65591210c6f64158341016bc62d0b400afb970d0b400067f5058910004ff75591200c6f46158540005bc745852010dfb7059120007b941d01400067f20d9541005bf7250740006f5535844002cfe70d85420057d72d85500aeec6258b400067f43596201a67f6295121015f676d05214677771951210ae7c6258a54004fd73d8542004fc76485400aeec54588400057d71d09500063d43d97400ccfd76d0a40006de2158c402af7953500401b57e73582540ae7d73d9740014fe72191202367c30191500057d7598341006bf74589100477b70541100b57c75484400057d72982540af7840582543757f7354340004fd76d0520005bd72d05400067e71d95420067f43d954212e7c635434000ef762d0521036ef20d89100757c75d012000cfe76d85404cf6421d952111e7c615414002e7f3059440006ef53588400067d53d814118ef710d89413de7f6050550006bd43991210067f5058b410aebf63d0b4002e7f6154110006ee43588400ae7f64951401557e7598141004fd75d814202e7f5058a4002ef630584400a6df7458c400073e4219150004ff75d911002dbe70509400aede73991210067f50d8542006bd4399210036ec625891011f7631485500067c20d95410067f43d95400067e4359610006ef725891001cfe739912100cfd72191210067d725944002f7965500400acfe74d81210247c75d81411b67c6395121
  | 4 => 0x89400ae7c549912102dbd76d0740006ee315884015eef2058b411ae7d42d95420067e54d854011d7f74505500c6f661d854023f3f43541200ae7c541911048ded73d09211e7755350510004ff7358b410067d76951212057d769524011e7e315961030f3c75509401a77710d9541006bd43d89411a73c41d9541014f676d052102e7e20596401257e72d05505167f639514202ef530584402367e10191500247c75592100067f65509400ae7c40582540067d649521002ef6505844001cfe73d91200067c43d95410acff759912101cfe73592100067e64585500af7840952400af7b40982540067d615825402cfd7059210006bd439912002ebe40992101267e625411002ef771586200047f73596404ce7e10d95210057f7550740006f4325844002e7f105944019e7e65d0a10004fd71d9120006fa30d85200047d73d954044fe4211812149e7d6395121006ed52588400067f72d954020f7531951100073c7454140007eb70485200c4fd70991100067f72594400067d6358550006ec5358840004fd73583421267c6254140006dc5258c400ae7c43d974018fe441d0921004ff73583410067e43582540ad7c7458a54004fd73d894012e7e6354120006bf43592201a76c21951211af6c42951210067e73582540067d73594400067f7559121004fe76485400afb561d07401857c75581420067e215964000cfc76d0110004ff7558a100aeef4258b401a57c71582540067d43d95420eeef2158a400aebf63d0740006bf4359121006bf43d85400de7d70d95400af3e54d094012e7c635414011e7e76541100067d74596100ae7e42191500057f7259150016ec6250b400ceee42d89400067e54d894102eee20588400ae7e64951201ad7e729825409cff7650b400067d4359620006bd43591210067d73d95212876d32951200ae7e5458440004ff70587420067f5358b4000cfc7458b4100ebc6150540006bf43592100067d6358a540ae7e645825402e7d60543400067f63d915002cf476505104aebd41191210ae7c7695210024fe75586400af3e7495141006f762d0541014fc72991100aeee74588400ae7e7599121004ff73d8540005f571181422067f649521018fe671d092111d7c7159150004fd72d81410ae7c41d97402076e20951200067e32191500aef741584400057d70d0550004fd70d89410af7b60582544ce7e41d9521006f564d05210057e74d855002ff26150040006f761485400af7854d02400aedc5458c400aebc541911002eef7258a400057d73191501177b60991500ae7f73d97400aebe7419120006f561506400ad7e74543400af7875d01400ae7e72191500057d73d95420ae7c541912002eec105884002e7c7059620006ee21588400ae7e60952402067e60952100acfc75991100067f75d81421be7d635411012d5
  | 5 => 0x6dd7258c4023f3d43541200067f30d95210067d43d9540007e870509200ae7d70d9740024fc75d894002dbe70d09401257c7258550006be41d9120016ee6250a40005dd731814102e7e30594400073f64991500067f73d9542024fc75d814102e7d20596100c5bd71d05400067d64951200073d43d89500057d76505500057d71d91501567c65505400ae7c72191500ae7c72d9740024fe7599110006dc7358910006dd7158c4002dec765092002edd2058c400057c76505500ae7f71d97400057f76485500acff76d0a100ae7f6558b404cf6e21d9521017eb60485200afb4415074002dec7050920017ae74d09420073f75507400076f4250950005bf71509400047f7558910006bd641912037f3c7550740016be62d0b400af3f439514202ebc4099210006fa30589100067c71582541af6f20951212067e40d95400057f75581211257e72d915000de671d09210057f70505500067f43d954100eec6148520006ed3258a1002cfc7058840006bf43584400ae5e731915012d7c735095002eef5058840006bd43d854012d7c73591500067d325964002edf5058c400047d735944000ef6614864002e7d50588404157f70585500af3f40952400af3e54d054002eee2058a100b67d745944000ebc61507400067d654844002ebd4058a4015fe720d05210067e21582542057d709522000dec71d09210067d31594400073d415414047f6f50d092111f7661d85500ae7f4259440086f631d89100073d43991500067e73d95420af3e5450b4008f7b60d8950015ee72d05200073e411915000cfe7119110006bd43592201a67c74d954102cfc705864002ead405884001cfc73591204ef7753d054102e9d4058c4002e7f5058640006bf74591100067d64952200af7b75d0240006bf43591200acfc7458a10006fb76500402776c5450920006bf6450120106f621991100067d74d95210067f70d952126f6f5350920014ff7658b410ae7c5458b40006bd435921001cfc735912111d7e71d89500777b7054120007b764d052102e7f5099220016be62d094016d7c7550b4102e7c4059640024fe75d8941104ff76504400267c76541401267d42596200057d70951100acfc76d09102067c10582541a7771058654015ec72501200ad7e74951420067d325825402d7e70d05500ae7c5458740037e652485100af3f4358254004fd7558a100067d73d95420ae7f43d9740004fd75d91200ad7f705825402cfc7058b412057d7695210004ff71588400076f7550920006f5755844002e7c1059640006ee71588400067f53587400067f65d912116e7e65d062002d7f705434011f6421485500ceec6258940014fe725864015ef676d0521014ff764811013d7c751912102e7d10596400067f53991212057d70952400067f5319110024fc7559220014fe76d
  | 6 => 0x465d05410afb661d074018fe651d09210067c31191501ae7e20d95420067e54d8940066f461585200ae7f41594400047f755874002ebe40592101257e7259150004fd75588400057f755011002e7d5058a10004fd73591210067f63991500aebf4319121006ef73588400ad7f76582540ad7e7098254005ed70d09420457e75d91101b67e63951213173d535094000ef661484402067e20d95400ae7f6550b4011d7f715855002e7f705964011f3e41505500057d74d89501267e21596200077654485100067d43d95411ae7e21d95420067c71596200ac7c75992200067f5058b4002ef610586200af7a54d01401267e62d89500067f53d8142005fb70509400c4fd76501100073f43d954100779505011001cfe735844001cfc73d81210067d53586200067e63d9541005bd71d0b4011d7e7158950006df735891002ef5505844002df87050a4012e7e63541400067d63d91502067c40d95400ae7f63582540067e435962002f7a20541400067c54d814211f6e21485500ad7c7454140024fc75589100073f43d89500ae7e64586541157c75587401a67e61951200057d70d95210dd7c75585400cebd42592200067d72d954101cfe7358b411257c72d91500067c62d95410af3f439524009eec52588400ac7c7519121004ff715922002eec30588400057f73d855002cfe7019121007ac64d09210ecfe76d0940005bd74181210ad7c75d0140004fd71d89400067c7359440006bf43d89400047f755911002f7840541404267d6350950014fe725844000df671509100ae7c54992100057d75181411a77810951102067c6395210006ee75588400247e75d91200067f5399210104ff70591100067e43d95420ae7d7019150004fd755911038dbf7350740004ff75d81210057f7158254006bd43591200067e3158254004ff75d89100057f7550a40014fc72592101d7747548510005ef74485200067d64541101ae7e62952100057f744855040d7f73d05501867e74d95424f67f63951410067e43d95400afbb43d01400067f65d81420aef674584400467f605855040d7d73d0550004fd76d0a101cfb743485100067c65981210aef464505100267c7654120107b621d074000cff76506404bcfe761912132ebd63d0940014fc7458342006ec75588401ae7d62952200067d63d95410067e315964002e7e4059620006bd43584400047f73d9540006f930d85201857e759814237f3f5050740006bd6450a10006f721584404ce7f31d95210073c54d91102067f62952101a67c71d95410067e611915000ef461485400ae7d43d974024f6d534852002e7c30596100067e43596400ad7e74952401567e65504400057f731915002cfd72191201c57f73541101557c755894102e7f705961002cbd76d0b40004fd73d91100de7d7654140006ed7358840
  | 7 => 0x96400067c735964002ebc405921012d7e73585501af6e4295120006ee64485200067c75591102776f505092002ede1058c401267c6254340016bd76d0b40004fd75589100af3e64582541a7763195121004fd7558b40004ff7358342016f66248510024fc75587421ae7f74d95420067d64191501267c62589500c7b7105054002e7e10596100067d62d8550004ff73d81210af6c4258a541557c75d81410067f53d894101cfc73d89100047d75d911029f3f4395220005f7714811020f3f43951101157c75507400063d43d954241e7f605095036e7f63543400067f70d954011f766148550006dd5258c4000cfc7158a4012d7c7358550006f732584400067f50587401167c65d01400ae7c5499120024fc75592100073d43d95410067f5358440004fd75d894002eef7258a10006bf4358742135de7318121006bf541912009eef74588400ad7f70952400067f53991200067d53d89100ae7f64951422febd63d05400afad62d0b401a67c619514002dbc70d054002cfc705844012e7e6354110005fb70506400047c7650950007af42485400067f50991212bfb943d014035f3d43952400ae7f7319150004ff73d91200067c32594400067e75d91210067f50191100ad7f7395142024fe7558620006de4258c4000ebe61d054001cfe73583410af3c54d0940006bd43d89402067c30582544e77750d054109eef21191200057d73d9150005f570d05211867c6550941006ef54588400067e42596100057d764855002e7d30594404bebd41d9121006df5458c401276c72541200067f655094115eef20d854202e7c305964021d7e74951100067c54591214ce7f10d952102cfd72d852002e7c10596200ae7c64951211267d3259620066f621d85200aef441587400afac6250b4000ef461487400067e21d95400067d75d91200067f53591210af7441951410077765d05410067f71582540067c659814202cfe76d062015eec42d854201cfc7358620475f575d052102e7d10596204fd7d739514102e7e20596200076d32d9521024fe75d89100ae7f65587400afac4250b411257e76d89500fe7c74596402357e74952200067f65585420067d32d9540007b764505103e76d324855002eb740584401cfb543485100067c10d954202cbc7650540006dc7258c400057f72585501cef563485101a67e619524001cfc73d814102d7c70505500267f76541200af3f4358654006f930589100067d53583422057f76952100057d70951200073d641915009eee325884002dfa74d014002ebe40592202067c10d954002eec2058a400057f7550840006f960181210057f7550910024fe75191200aef840583410c5f970991100067f50191200067e3259610024fe7558b400067e73594400de7e74d954002e7d205964001cfc73d912102e7c40596204e77
  | 8 => 0x1257c72d05502057f70952200057f755012001cfe7358a40006bc64501200ae7f63586540067e30d95211557e75181410057d71191500053f74585500067f655894002df8705064000cfd72d8121024fe75d81210057f75d01101a76421951210aef860583420af3f655074002fbb64d0140014fd71d81210073e42d9150016bc76509400067f21594401257c72d8550006fb60981410067e425825411f7710d85500dd7c75485400067e63582540df7b705414020e7d639511020f3d43951100067e325825402cff70586200067c7558910056ee3258a102ff3f53d05402edbd73505402867f63951200067d311915002ebf405884000779505012002cfc7058620004fd73d81420067e42596400267c76541100073f65d054002ebf74592100067e629915029f3d43952200067c76505500ae765458440024fe755844002dbc7050b400073f7550b404b6bd4219121006be42191100067c72d9540004ff7558910004fd735874002cfe7650a10006f77159121006bd4358742006b743584400aefb40583420aefb4058341006bf5419110086f641586200067f31191500aebe74191213cf3d53d0b4009eee5258840006de5258c40176f621d85420067e6319150006f653584400057c7695121006bf435834102cfc76486402947e76951421a67e71d95410067d7695120177b44150941105fb70591100ad7f7395240006ed64d09210ae7c6158254007b942d01400067e32596400757c75591204ce7f71d9521014fc76d0120006bd43191210ae7e41191500067f53d854032f3f53d09400067c75591200afaf7250b400067d71594400067e31d954202fda63500402057c7398254014fc72d91100076f75485201c57d7354110096f421584400067c54d8540006ec31588400aef4425844014dde73181410067f30191504bef710d9121004fd7358640016f476485101af6e32951201157c7558b400047d73596200acff751912002dbe70d07400ae7e43d97401b67c63951410067f62585500057f7550640004fd71991200af3c5450b400067f64991500ae7f60586540067c54592101a67d74d95412cf3f43541400067f53592201267c725962021c7e76951410fd7c75506400afba70d0b4011e7c31596104ce7d21d95210047d73596400067f53592100fe7f60d915002eee10588404ce7c72d95210ae7e545874202e7e70596400047d70d95210af7860582542067f61951100077541541100067e31d95400ae7c60582540067f63d95424d67f42d9521004fd7558640024fc7558b4002e7f60541100073d435865402ebd405864018def725912131dbd73509402457f73541200067f65d85400075e73191500aef7415874202dbc70d094001cfe73583420067f63d89501ae7e72d9542024fe7558b410ae7c545844002ebc405922002e7c705
  | 9 => 0xc65d89410067f325944012d7c73d05501567e65506200067c659814145f7553d05211b57e7358a540067c715944009ebf7650b40006f960181420067f72596100067e735961012e7e6354340004ff735911002d7f70541101257c72591500073d43d95421a774719512102fba64500400dd797099150007af64d09210057c76d05500eebf42d912002eec70588400ae7f649514100cfc764811012d7c73d89500077531d95210067c70d95420077b65d0140176f441591210073c54d91200067c31582540adbf73d0740006f5725844002cf476485101b57c7358654006ee415884002eed20586200067c735825411e7e6158550386bf63507403a5bd73d07400067f101915001cfe7399220006be41191200ae7c625825400ef764d054111e7e41596100067f73d95412a57f7395220006f76150540006bf435884002e7d2059620004fd75592200af7741586540067c655894102cfd71d89101a67c10d95410067d32d9541004ff7558a4046df773d05212157f73951100ac7f76952201ae7c629514001cfc735891046df573d05214ce7f41d95210057c76509504d76e32d95210067d70d9521004ff73586400067f65589410067c75587400acfc75191211a67d10d954102cfe70d9121006ef71588400ae7e7695140004ff7358a10067e4215812101cfe73d81210067d53d9110006bd435834111f7641d05500067c54591200e6bf41d9110004fd75191100067c73d95400057f75506200067c31596401ae7e629511008d7c75506200067f7159620024fe755922000cfc715912002e7f70596200067c30d95420047f73582540077b70591500afaf43d0942004ff76506200067c64d8550006b54358440014fc74d89400067c5459220024fe75d912002ef71058a100067d5358b412cf3d435414002ef420584404ce7d31d95212067c30d95402957e74951200067f53591200067f65581421b67e6395120006df7158c401267f7259620004fd73592200057f75504400057d73d8950004ff75591100067d639915000eec76485201b67c639514015fe442d05212057d70952100067c6319150056ee4258a101273e425095002eed405884002e7d50586200ad7c74d95400067e31596200067e73596200b57c7550440015f672d0521495ed75d092101cfc73d8520017af74509201b57c7358254014ff71191210067d53991100069e7458c401ae7d32d954202e7e705961002e7f509921002edd4058c4002e7e10596401567e74d95410076d21541201ae7d20d954200df671d09100acff75191101a67d71d95410067e43d95410af78409825402e7d40596101a67e21d9541006f4765051001cfe735884043d7f73d09502067c10d97400ae7e5458341005bf7650b4001cfe7399110014fd70d85200073f43d95420af3c54d05403b73f5350b40
  | 10 => 0x110006bd43d81410067f62541100067f50d85401267c6254110014ff7658b400067e41596400073f43d85500057f75d01202367e30191500063f435944002e7f505922002ef7405844002f3e4054140004fd7519121016bc62509400073d435915002f7a105414050fad43d09420473e74951100aeec4258b400ccfd709912000fb764d05410067d725961000cfe76d85420ae7c5419121005bc744864002e7f50592101ae7e42d9542006bd64191210af3f43982540067f75589102873d43951200067c715964008f3e74952201276e42d0950024fe7558a101267e32596200067f53191211a67e31d95410073f435915002d7c70485500ae7d71191501167f60991500067c6219150004fd75d91100067e42d9540257e551485200067c61d9540004ff735891002cfc765054002ef72058440066f6315891002ef771584401ffe421d81211276c4250950006bf43591101257f72509501a77671951100067f505912124fe531485200ae7c6158654006ef62485400067f6495121004ff7158b40004ff755874002c7d7059610006dc7158c40014fe7650120207781095210006bd4358840006f531586201fef631d81210af3f6550b40066f661d85200ae7c64d095002e7d4059640014fe7299110024fc7558a400067e54d814111e7e61541400057d70d09500adbc744844011f7b10541100073d42541401267e62543401b67c6395142006f764d052111d7c71509501867c65509400057f75581421ae7e32d9542004fe76509100aedc7458c401857c75585424d77771d95210acff76d09100073f74541402457d73541200dd7d70951400067c54d89400067d63d89500acfc751912002e7f505844002efa601814111d7f71505501276e32485500af3e7495142007e7424851026fea305092002cec76485201273c42d09500e6f6215864011d7c71d91500067f65d89410ae7e649825402cfc7650620006f751584401d77454485100af3e645865402d7c705095002e7c305962011f7621585500073e545054000eee61485200df7b60591500057d74d85500067e32d95402873f43951200acff75991200067e31d974012e7c63541200af7854d0140006bc64501100ac7c74596201557c75509410067d70d9541207771095210006f773584400067c7558b404d67c32d95210af7b6098254006bf43d81414cf7710d95210067d75d91102bf7b53d01400ae7f7119150007b77150540004ff71591200047d73d95411cf775348510014fe72d85400065d7558c400067f659814118ef441d89410aef441584402067e60582540247c75d81420057f73591500073f65d0940006f7725844002fea6250040335bd73d09400ae7e71d97400067f65d894001cfc73992101267e6254140006de4158c400057f76d095000ee461485204457f70589500067
  | 11 => 0xe6f631586402067c6395220006ed515884002d7f70541200067d65504402273f43952101257e72505500067f50591200ae7f60982541a57c7158a540067e75d91200053c745855051d7d739514208e7f60d895001cfc7358b41004fd73d81213cebd63d0b400067c30d95410af7b75d01400af2c4295142004fd759922023e7d63541200066d53588400047f73596100073f425434002e7d705944002f3c40541401ae7c72d95420067e5458a100cdbd72d09400067d53d854201cfe73992100073d43982541276f20509500067d5358a4000cfe71d89400aef641991100dd7c75589400067d53d85200067c315962002f7a3054110006de7158c4002cfc70591210073d43d8550006ef31588400067f53587420057d7518121005bf745852026fe93050920006bf6499121004ff75d89410ceee62d894012d7e7359150006ed315884028d7f7395120007af625094011e7f3159610014fe76d8910006bd43591100047d70d954202e7f3059610084ff7258910067e710485200ae7c54587420047d76952200057f7550520016ec624811011e7d3159610004fd73d91211b67e639514011e7f715961000ebc76505400aef6545844002e7e1059620006bf6499110004fe76d0910006ef624811018eef21d89414ce7f21d9521007b541d01100067d53d91200067f75d81211ddf773485100757c7550520004fb7650040004fd75991201a76e2195121004fd75584400067c31d95402357e74952101f5f57350510024fe75587403af3f5050b4002fe962500400de7e76d95400047f765055002eef30588402f73f50d054002edf7058c400067f50d81420ac7c7458254006ed6250a4000cfc71191200057f75581410aef443584400057d71991500ae7c40d97400ae7c74594400067d75d9121024fe755921002fd96350040005bf74589100af7a5450040005bc74581210067e4158254006bf4358a100067c611915002dec704852010eef219912002ef771586400257d70d89500057d735855010eef2058b402067c30d97400acfc75992200cfaf21d094001cfe73592200067d6358254016ef64d094212d7c73d85500057f7550a100267f765414013d7e75d9121006ed75588400c6fa105834111f771048550014fc74587422067e10d9540107e4214874039f3d53d07400067d649511005f7b60d855013e7c65487400067c65d8542004fd72191100acff7399120004fd76509100067c2159440007ad42501200ae7c42594400067f755922002cfe76d81214cf6c72d95210067e64d8950024fe75d81421a67f71d9541006bd43d912102cfa76d01400057d73589501567e76d95410ac7c759921002ef41058640006fb7058910136de63484401267e42596202ce7d6354140146ee62d8941015ee74d09424ce7f72d95211a73e419514100cfe765
  | 12 => 0xd315964002dbe705054021d7e76951410067d31582540057d7518142175f6711814202edf1058c403e73f434855002eef1058840004ff755834100ef6615044002cff72d91200067e41d95400acff75191210ad7f7258a540067f3159640006dd7558c4002e7f1059610015ef71485200067d32d97400af3e74952401a57e7158a5435e7d63952403273f50d0940004ff765091029e7d6395220106fa10d81410067f64541100aede7458c402d57f73541401d7775048510014fc72191102c77b50d01400ceee42583420067c31d95420057f73d91500067c32191500ae7e54588400ae7c415944000cfc72d8520004bc74589100073c54191103657d7395240005bf74486400ae7c76951200067f30582540057f715915024eef63485201ad7c72586540067c54d89410acff759922002e7d40596203273c65d09400057d72d05500ae7e42d974000cfc74d85402057c705865412d7c73991500457c75501101b67e63951100ac7c7654340004ff7558342004fd73d894102cfc7650a100ad7e749514002dbd76d0b40016ee62484404d67f32d952102e7f3059640005bd74485400067c7559121024fc75d81420ceec32d89401a67f74d95410ae6c6258a5432ebf63d09400af7860982541e7b74350510457e552d05210ae7c71d9740037e462485102e6bd63505400aebf60d0940015ee725052002dbc7050740096f62119110036f5215862000cfd72d912100ef4615054002d7e70509500067c62d95400ae7c5458341004fd74d8121006bd64191100077765d05210067e6454110004ff73591200057f75509400067f53583411276f21541200acff76d06201867e65508400067c63d954011f3c41d05500de7d40d9540007e762485100067e72d9541006dd5158c400067d30191500057f74585500067f50d89410047d76952101267e7259620096f651584400067f53d894002e7f205944011d7f714855018fe631d092102dbe74d01400073e41d91500aebf42992200067753584400067d72582540ae74545844002cfe7059220006bd4358a100067c71d95420067f50991200067d53d81210067e32d97400067c6519121015ee72d01200057d72d91500067d53589100067c64485500247c75591100067e21d9740006bf43d91210247e75d9121024fc75d8542016ef60509202067c6095141005be76d0540006f531d89100073f43d952102e7c2059440004fc765052049f6d329512100ef661506400ae7c73191500067f63d95410ac7c74594400073f645915000ebe6150540147ac425094101cfe73591200adbf73d0b400067d7459640005be74485400acfc759912100ef7604851003ddc73589100ae7c64d0550006df7558c40015f472d0521004fd73991210aef74358440007bb70509401157c7550b400063d43594404c6bd42d9121
  | 13 => 0x91200076e54485200afac4250b400067f53d81410af3e64982542e73f53505400acfc75992100ceef21d89400067c54d81410ae7c6358254006f75258440006ee73588400af6c54d09424d67c42d95210067c63d95410057d75981424373d43d09502a57d73952200057f76505500067f63d8550006dd5458c40006ed54588400ae7c54588403e73d43485500067c63d954200ff360485104ce7c21d95210045d73191500ae7f6295142007e741485200aef44158742004fd75d89102febf63d054031dbf735094022d7f7395210006ed62484400ae7c43594400aeef42588401157b7059150006dd634844039ebd63d074002f7a305412011e7d21596100cefa20583422d57d73541400067d5399220004ff725864018fe421991214876d53d09210aebe64d06200aedf4258c400067e63d95401a67e10d954102e7f40594400067c65d85400067d65d0a100057f7558740006bf4358620004ff7359220004ff73d852001cfc7399110006bc42d911000ef461507402067f74d9540006ed3258a400076f62589500067c73596202576c75485200073c54191200067d71596400aebf421912001cfc73d854001cfe7358620357b954d02400063f43d95212057c7198254014fe729921012d7e73d915002fbb74500400067f50191210067f5358840145f5719912124faf43485200ae7c7695110004fd7358620024fc75d9120146ec42591211267d76541200aeed72991211e7b54350510024fc75591210af7441586540073f655054011d7e76d85501af3e4295142014fc72d814100df471481100aef571191100ae7c7599220014fd71191210067c31d97400067f71594400067d635865402eee2058a400047d73582540057d75d91210067c72d954112d7e7350950005ed72d052001cfe73591100ae7f76951211ae7e6258a540ac7c76951210067e71596200067e41d95420067f65181210073f41543400067d76951100067f635915000fe762d05210067e42d9541014fc72586400077741485500067e415962002df8705094001cfe7358910004fd73587420067f50d89400e4fe76191100057d71d89500076f65d094212d7e7358950006ed32d8520004fd751912019f7b60d095013f7b60485504373f43d0950005df73589100047f75592100067f735964050f6f53d0942016ec62485400057d709514245fe532d05211bf793054110005f571d01100067f6518142004ff72583410af3f4395140006f54358440005bf7250540174fd72991213e77531485501257e72991502273d439521012d7c731915012d7e73191502057f70952100073d43d952102ebd40584400ad7e7458a540acff76501100067e32d95410067f315825402dee70509200773e74951200aef840583422067c60951421a67f60951100ae3c42191500077654505100067
  | 14 => 0x4ff71583420047d73d97400067f6558121064ff715891002ef61058640006f7535844002f7410541100073e5450940005be74181210aeec645092002e7f30596200067e72594404d67f20d952102ef86098342024fe75d85203873d53507400067d65d0a400073c42191500247e76d95420057d73586540067f31d954000cfd74d89410057f73d95422957e76d9542024fe7558a401af3c42d954212d7e739915000df7724851002ef6405844002eec50588400ae7e7319150004fd7558a40005f570d054116f7b60d0550096f4515844002e5d5058c400dd7c755054002e6d50588400af78545004001cfc73591100057d73d95410067f64541200e7e42148640004ff73d89412af7b53500400067f74596100053c74589500ae7f76951200ac7f73d974002e77505844013e7e65486400aedd739912111e7c615855002edc5058c4002cfe70592101ae7c20d95420067f30d954019e7e65d0a400ae7f4359440007e571d0921094ff76507400757c75501205173d43951420057f704855049f75319512101cfe731912101cfc73d89410067c54591104ce7d41d95210067c7559220014fe72592100b57e7499150004fd75591200077b75500400063d43d95210067e72596400067f5359110004ff7650a100ac7f7695210006bd43586200ae7f63982540067e70d954100cfe71992200af6e54d094200cfe71d814217dde73181421a77441d95410067f6154120016ec62509410057f7559121006ed32d812124fad43485200067c72596100067e73d9541176f641d854202cfe70d89410af7454d05412057c7058a5400cfe76d011001cfc7358742006ed5358840014ff71d91210057d75981410067f75d81410067e61991504dd7e76d95210067c74d95214d77721d952111f7621541104ce7d71d95210e6bd41d9110014fe72d81410067e70d95210067d30d9521016f462485100067c65d9121004ff75d81410ad7f75d01404073f43d05500067f2119150146ef205912102e7f10596400067d5358640024fe75583420067f65d81210067f65585401b57e73982542f73c65d054002cfe7058620024fc75d91210047f7359620006ef64d09210067f1058254004ff7358a400057f7158a54005bf74484402157d73951100067f50587420cfac62509400ae7b4058254024fc75d89100ae7f6258254006ed32589100057f7559120016bc6250b400067c72594401ae7e62952400067f755912006ddc735852002eee30588400ae3c411915011d7e715095033f3d43951400067e54586200057d7650950007b464505100ad7e74982540af3c65d0b40006f54258440005fb70505400057e74d9521004ff75d9120006bf74591210067c54d91213b6bf6350b401a67c31d954101cfe73d89100aebf60d054002e7e30596102df3c54505400aef9709
  | 15 => 0xf7458550014fc7299210037e442485100047f7559121004ff73d8940004fd7558620006f532584400aebe64d0a100067e715825409eec3258840006f6644851000cfe71d912002eee50588400ae7e769514201cfe739912002ef41058440004ff76484400067d7158254014fc72d8540006fb7059110024fe7559110006bd43583421ae7c62951101867e76d954202cfe70d8910004ff7259110096bf765074001cfc7319121005f772505100067e54d891000fb674d0521004ff735862018ef710587421276f20d89500057d729915002cfc7058a400057d75d912002df476505100fd7c7550a40017e77148520006df7258c4011d7e71d095002ef6205844002e7f6054120006fb609814223f7930541200057f735855002d7e70d09502067e7695210005ef715092000cfd74584400067d31d95420067c65d89400ac7c74d9540066ed2158a100067d31d9540007bb705054000df671d011002df670505100ac7e74d95211867e6550a100067d43594400057c74585501be7f6354110004fd76506200067d654864002ede5058c4002eed3058840036ee62d8910006f6435844002f6c20541200ae7e7695141174ff71591210af6c4295142006bf4358342004ff75d85400067f32191500067d5358b4002e7d5058a4002edd7058c4002cfd72d91200067d62541102067c60951210af3c65d074002ef440584401857e75181422c77865d0140006ef32d89400057f75505400457c755891002e7d30596100ae7461586540057c76d09500067f71596400ae7c76952201a67e61952200067d63591501ae7e6295140135de73991211a77b10951101a67e61951400067c655894002df870505404073d43d055002d7e70d89504ce7c41d952110faf2050b400cdf97099120005f574485100ae7f61951410047d75d91210067c7259640024fe75d85420ae7e41d9740006bf43d89100ae7e5458342096f621584400067c5458a100067e7259610006dc7558c4002eef205922015fe632d05211a67c61951421af6e32951210067f315962002cec765092002e7e305964011e7f41596100ad3c7454340024fc755911011d7d71d05500067f53d91210aef4545844002d7f7054140006f475584400067f5358a100057d7095121005df73585200aeef4158840004fd75d89410067d31596200aedf4158c40127772148550024fe75d912102dbc76509400067c645895000cfc7650941014fc76501201b67c63951200ecfe76191200067c6518121004fd76487400057f71509500067f50583410acff73191200067d73d95400067d53191201fcff705891005f3e749521000cfe71d89100247e76d95210267c76543404d67c20d95211cff230485100ad7f739514002cfc70587420067f31d954219d7e759834234f7953d0240014fc72191202edbf7350540
  | 16 => 0x82540ad7c749825401cfc73588400063d4319150066f710d8520007b870505400065e7558c400de7f6059150004fd73992200057f7058a54005bd71d0940024fe7599120004fd73d91200067f6548540004fd76d06200067c65585420067c325964042d7d73509500aebf43991100ae7c64505500067d31d97400067f50d81410057d759812101cde73991211af6c72951210457c75509100067d30582540eeee3258a4020f7a309511002e7d30596400067d65d06400067e64d85500e6f64158640004ff75d85200067d53587402067e305825401cfc735834111d7e71191500047f7558b401af6f20951420057d75991210067e6399150006f531589100057f73582541af3e42d95420067f50d912100cfc7199120004ff73d8141006f5525844026f6d53509200067c43d9521004fd70d854213d7e75991210067f7359440004fd7359120016be6250b40017eb60509202067c62952400acfc7458620007b7414874000cfc71191100dc7d70d95404cf7421d952115fe652d05211a73e41d95410b57c7550840495ef75d0921006f45258440004ff765052000cfe7158b401ad7e72582540067f30d97400073f75505402867d639512001cfc73d85420057d739915013e7e76d95210ae7f75992202073e40951400af3e74951400067e6459150004ff75d85420ae7f4158254016ec62487400067f73d9540004ff73d89100acfc74589102077a309522011d7e74d05501cff130485100067d65508400057f73589501257e74d09500ae7f62586540ac7c7459610004fd75d8542004fd76484401ef74545051002f3a405434000cfc71992200c7b621d0540004ff7559210005f77150110004ff7258440056ee32d85201e7775350510007f0704851001cfe73d85420057f75487400047f7650950004fd731912011d7e715915001cfe735874002dbe7050b4002e7f50588400067d5319110006bd43d89102df3f5050540006bf64d01100057f72582540ad7c74586540047d73596101a77710951210aebf41191100c7b4415054002ef6705844002ef510592104ef7553d05410067f76505500076f65d092102efa601812100cff76587420073f43d95400067c2119150016be62509400067f10d95420067c639915001cfc73d91200067e71596400067f65d814102cff7058a100055d73191500057e7650950064fd76481101ae7f72d95420c6f621d854001cfc73992200067d71d95405076f50d09421a67e41d954116e7e65d06401ddf5734851011f7631541100ae3f43191503e67f63485502df3c75505400af776158654177e421591212776c7550920006f453584400067f10d954000cfc71583424367f63d09500057e7695121097e4214844028d7d73951200057e74d895002cfc764844033e7d63951400067c3259610006f531d81210073
  | 17 => 0x1257c72505500247e759912100df67150b410073f65509400067f7358254145ee72181410067d53d8142017ae74d0921004ff7158a40006bd439911029f793095220015e672d0521006f4735844002e7d70596100247c75591200dd7e76d95402957e7695142014fe725911000ef76050510056f521d852002ef750584400ae7c41191500aeed72991200067e73d95400067e7258254006bc74589100ae7e5458b4102ef520584400073c745434011e7d765411002e7f5058a100ae5d7319150016ee62486400777b605895049f3f4395121004fd75d912105e7f60d85502067f649522002cff72191202067e70d95400dc7d76952404ce7c71d95210067e30d9542007f370505100ad7f76586540067f65181411f5f773505104577465d05210057e76485500067f72582540067c6518141006f5735844045fb743d05210ae7c42191500067f64951100073c745895015fe672d052102edd5058c401266e62d89500ceef20d894012d7e73d855011f3c415055002cff70592100067c629915002cfc7458b4001cfe73d9121005bf76507400aef461587420067f5358620005bd72d07400067e71d954013d7e7598121176f6615084002e7e30596202067e30d95400067d74596200acff731911002df6704851002e7d50586400047d75991214067f63d05500acff75992100047e76951210067d539921001cfe73191101fdfb70589100073f4358950004fd72992101a67f31d95411ae7d74d95422067f63952200057f755894011f7710505500aebf41992100ae7c76951212576c54485200ae7c655074011f742148550266fa20d81210aef571991210067c70d95410067f63d95210063c54d911002eb540584400067c63d9521036ee325891024f6f5348520014fe7219110006f960181410067f20191500ae7e64951100057f75589100067c755921002d7c70d09500757c75585201af6f21951201267f42596200076d72951201557c75581411267d21596200067c65d814202e7e40594400067f43d95210067f65d094002cff71191100eeee4258a400067f30d954102e7f60541400afb4615074001cfc735834211e7f215961002eee705884048def73d0921266ee32d81210067d639825436e7d63543400ae7f76952200067f5059110004fd75d8141004ff72592100073d43d95401ae7d21d9542006bc41d9120316bd63509400067d735964009eef21588400057f7399150037e7204851014ede63504400af3c40951402ce7f6354140004ff735844000cfc7158840004fd74d852002d7c70d0550006df2158c400ae7f7219150146ec625894102edc7058c4002cfc7059210004ff7648640096f631584400067f75587402367c20191500067c32582540067f31d97400067e74d952102e7d50992201ae7e62951410076f42485500ae7f425
  | 18 => 0xf72d952102f7610541100067d53591210aef64119110005ed70d0921007b870509401cef7634851000cfd70d89100067e61582540067d76952200acfe7499120024fc75d91100047d73d9542006f561506200057e76951400067c65581420aeee64509200057f7650950006bf43d85200067d73596200ae7c4319150006f531586402073e40d95400ae7f42d974025def734852002efb64d0140004ff75591212076f209522002ebd40588400067d30d9542066ef2158a100aefb60983420acff73992200057f7358a54024fc75583421257c729915002e7c10594400ad7c74543400ac7e74d954032f3d53d094045fb543d052149f3d4395121106be64504400067d65d0620386bd63507401276e62d89500247e75d91100073d43589502067e76952200acfc7519110004ff7358b400ae7840582540067f53583420067d30d95401267e76541202e6bf63505400077775505101af6e72951201a67f10d95410067d32594401af6c42d9542004fd73589100073d43582540067d5399121006f775584401ef74755051015df77159121007776158550005bf7150b4001cfc7358b40004fd7558342004ff73d91100057f7550b4147fe551d0921017af64d0942024fe75191210267f76543400073f431915002e7e20594400ae7f6158a5402cfc705922002e7d10594400067c61d9542007af72509404bef441d912102dbe70d0540006f472584400aef461587401a57e7158254004ff7558b400047f73d95420067d625855000cfe7159220014fe76d89410067d6258254006bf4358b411267c62d89500067d43d95210057c74589504beed72d912130f3c54509400067f2158254087e421981210aef976d02400ae7e71191503e67d6348550004fd75d85400aebe74191100067c64541200057f73586540067f65d054002ebf4058a40006ef32588400ad7c745825402e7c40594404367d63d09503173f53509400057d73982540067c65d81410067c6558141004ff73d91210067f215964021d7e749512102f7a4054340005dd731812102eed50588400067f62d85500067e2159440487e531d09211b67e639514202e7f105962027ded735092012d7c734855002cfd71d91102067c629521002eaf405884002e9f4058c400cebf42592200073d4154340006bd43d911022d7d73952103ed7f73485500067f325961002ef430584400e6be76d0540006bd4358b410057d76d09500073c4119150006bd64d0a100073f75509404677654d05210067d63d85500047f7359440006bf64d01200067e43594403fd7d7350550004fd7399110004ff73592100067c765095020f7930951100053f7458950006bf43d91100057f75591100067f10d97400067f65581411a67f61951213af3c7550b40007e761485201ae7f42d9542004fe76505201a67e6195142
  | 19 => 0x941006bd43d8121006de7558c401257d72d0950004ff75d894002f78205412000cff72d91210067d53d8540004fd7299110006bf4358910006bd64d06200067e625825411d7c71d095012e7c635411012d7e73d0550305bf73d05400057f75486401276c62589500af6c6258a543de7f60485500ae7e74594400067f30d954212d7e73d8950006bd43d85204c6ec42d912102dbc70509402077410951100067e30d9541024fc75586402073c40d95404cf7441d95214067d63d05500067e5458a400067c64541102057f73982540067f64951200ae7f43191500047f73d95414afe42119121004fd73d81410067f65d09410ae7f72d97400acff75991100067e31594400067c64585500067d5359220014fe72d9110006fb6098121004ff75588400057f73d95210ae6e54588400ae5e5458c4011d7e71d9150005bf7458121265fb705852011e7c2159610005ed72d0120067e441485200057e74485500ae7c54583420067c61991502877a3095120004ff73d814212d7c7358950006ef62509410067d535921000df674d05210c6bf4159210005f571d09101a77b10952100067f3258254086ed21d891001cfe73191200ae7c7458254006f75458440024fc75d8520006ee5358840006f6425844001cfe73d89413b73d5350b400077741505501a67d21d9541004fd739921043d7d73d095018fe710d0921006bf43d8542004fd75991101577b60505500067e61d9540005be76d09400aedc4258c400057d75d91100af3a54d02400063c54d91200063f4359610005ed72181413457d73951401257e72d85504157b70585500057f75585200073d43191500067f325964010cfd729912009eec2158840004fd7358a4002dbe70d0b40006dc2158c400067e54d85200ad7c76543400aeec42588400067d53d8941006bf4358a4016d7e75983410067c32d9540004fd72d9110004fd75d85201267c3259620006be64506200073c74585502067c70d9540004ff75586200067c4259610004fd71d8142004ff75d81420067d53991201a7762195110024fc7558b410067c54d89101267e62589500067d63d95400067c54586202067e30d97400067d6254340004fe76d05200dd7d7099150007f070505100067f53d89100067f6548740006af43588400057d7598342006f632584403f73f435055012d7e73505500067d535844011d7c71d89502df3c6550540256ef654852018ef62158742146ee62504400057f76d0550006bf43d81210067c65d81210dd7c7654140024fc75583410ad7f7658a540067f65991212067c619524000df47150110006bf43d912000ebe61d07401857c75d81424d67d42d952111f7441485500077571951101ef7750505100067f7359610004fc765091000cfe719912002e7d305962002e7d70596401ae7c32d95424cf6
  | 20 => 0x247e76d95411ad7e725865413d7c75d812100cfc7158b401567e65506400ad7e745865411e7c4159610007af645092030f3f5050940004fd7358b400067f5358b410aeec6258b4101cfc73586400057e76d09501a7763195110004fd755874011f764154110024fe75991210057f75484400c6f431d854002ebf405864002dbc70d0b400eebd42d9120006bd435891000cfc7159220004fd755912101cfe73d8540014fc7258341004fd7650a100067c74596200067f53991100ae7d4319150006ed7158840006f561486400067e6219150016ef61d09212077a309521001cfe73d85200067f21d95400ae7c54991100aebf42191210aef970991100057f755894102eef70588400077561485500067e43d95210067e75d91100067e62d95400067d535912002e7f645414002e7d50992104ce7e21d95210aeee42191200067c2158254107b710507400067e76951100067d30d974000dee76d09210063f43582540067c4259640006f652584400057d73582540073c42d915002ebe74992201ae7f60951200ae7e6458a5402e7d20594401267f21596200057d7358a5402edc2058c4000cfe76d85202076c209512000cfc76501104cf7471d95210067c21596400afb441d094102e7f2059610014fe76d01200af7875d024002edf2058c40004fd731911020e7f63951100067f659814200cff721912118eee76d09210067e54589101273e42d09500aebc4219110014fd7458840006bd43d85420af3c65507401ae7d72d95420075d7319150007af42487400ac7e745944001cfe73d9110016ee62d0941104fd7199110004fd7599121096f431584401ae7f21d95422067e609522019e7c65d09410fd7e761915011e7d415961002f7a6550040007f3704851002e7f70594400067e74596200067d76952100067c75d8142006bc54d91100067d7259640024fc75586203bdbd7350b40006bd4358a402b77875500401257e72585500ae7f41d97400ae7970d974001cfc7358a10004fd7358b410acfe74191214ce7e71d95210047d70d9541006ad435884002eec20588400067e54d812102dbc70d074024eed6348520004ff755874241e7f60d09500067d71d95420063d43596102ff3d53d054011e7c61541200ae7f7019150305bd73d05401277b20541200ad7c74d95411af77219512102cfe709921000ef6615062002e7e70596203f73d43505500a69d7458c4000ff3605051002e7c20596100ae7d71d974002efa3058a100076d42541200ad7e74582540acfe749911002e7f50586200afbb42d01400067e769512028779309512002ef61058440006bd43d91202057c7298254006ed62504402576f504852001cfe73d8142006dd6350440024fc75d89410c6f621583410067e54d85420067c65581214a57f73951211af6f20d954200df4715
  | 21 => 0x674d05410067c76485500e4fe76d05402067f63952400afae62d0b404cf6c21d95210b77b6019150475f775d05210057e76d05500067e73d952102edf4058c4002eef40588404677454d05214676e54d09210067f641915002eec2058a1001cfe735874202e7f625412002cfc7058a100067e32594400067f20582540067d53d894001cfc739912002e7f40596104d76c42d952102ede7058c400067c6558540024fe75583412bf7953d01400af3f65d0b400067f63589500ae7c649521002df976d02400afaf6250b401267d7259620004ff73587400aebc64d012017ede63508400ae7f76952100ae7c64509500073f4358550004ff7558b411267f32596201fefa10d8121004fd7599210467e742d052102e7f20596400067d6258654007b541501103cf3f53d0b40004fd7358a10006f93058a1002e7e64543400acff739912101cfe73591212057f769522002ebf74592201a67f41d95410757e75d91200057f715895001cfe73d81412067c20582540aefb60983410067f6319150004ff73587421157c75487401ae7f32d954238dbd735074039f3f53d07400067e74596100057f74589500af7b40582540067c71d95400057d7095141004ff73d85420067f32d95400067f72d95411cf7553485100afbb41d01400067e70d954245f7753d05210aebf43992200acfc7648740014fd74d85420067f74d952147f6c65d092111d7f72485500067f5058342006ec715884001cfc73191200067c32d95410afb970d07400067e63d95420063d43582540ae7c751912102efa601814202cfe70191101a67e615865402df47648510004ff73591211e7f2305051011e7e61d85502267d639521002e7c2059640004ff7458a1011d7c71589504d67d32d952102c7f705961002cfc70992200067c73d95411177b705434002dbc70505400af3f4358a540ae7c75992100c7e4214854011f7461585500067d30d95410067f7259640006ec73588404ce7c10d952100df774505103de7f60d0550006ef51588400ae3e74d974002cbd76d07400ae7e7458254006df5158c40024fe75d91100aeec4158840175ed729912102cfc74587400067e61d954202cfe7058a100067f53d91101d6f5654851002cbc7650940024fe759921000ebd76d07400067c75d81410047f73d95210067f6559121004bf74589100ae7c4258254096bd41191100aeef4258b414ce7d10d95210aedc4158c4013f3e7495121024fc75591200ae7c5458b410067c32d97400c4fd76d064002ef540584400067c54d91100057d70d9542006ef72591211273c42509500067e73596400063f435964001cfe7358a1002e7c30594401276f21d09504c6ef20d912105d7c7550a1036f3f4354340016ee6250a100aebc41191200ae7c6558b404676f72951210acff7399210004fd7359210
  | 22 => 0x11960ce0b40210090067c54d91200ae7f6358a541267c42596200aede5458c4042d7f7350950006f464485100ae7e43191500ae7e72d97400067f73d9521086ef21d891000fe772485100afb771507400067d635895002cfd71191100073d435855002e7d505921013e7e654844000cff76587400067c72582543b6bd6350b4001cfc73592101ae7c62951411b67e63952100acff76501200067f4359610004fd76486400077771541100067c54d85201157f70591500047d73191500073d42543400247c75587403ed7d734855013e7c65485403f67f63505503c73f50d0b400057d71982540063f43596201e7f1305051002cff71d91103d5bd73d0b404bfe421d9121005fb7050a400ceef21583420af746158654016bc62d09401bf75315411011e7e6154340005dd731814201cfc735922002e7e10594400067e71594401ae7c21d95420067f745962002cfe70d8520004ff764854011f6c21485501ae7c42d95420067d65506400067d53191211af6f2058a5419e7c65d09400ae7c65587402077820952200ae7c73d97400057d73d9540005ed744852011e7d71596100aeee54588400067e62d95410067c42d9540014fc72591100067f71d95400af3c41951410057f72505500057f7258654176f661d8542006bc54d91200067c21d95400057f7558b40024fe75589100cdbf72509400ae7e401915002e7d50584400dd7c7550940004ff75d91211a774219512113d7c75591210ae7f6058a54174fd769912102cfd70586200063d435964002d7e705055000fb77450510014fc725874001cfe73d89400067e42594400067e54586400073c41d915000ebc61d05400067e64541200c6f641d8540006bd43992200afba54d02404ce7e31d9521487ad43d09210ae7c415825401cfc73d91100057d73d85500073f745895002efa305862002cfc70d89100063f43d95400067d72d95400ae7c6495220487af43d092124fea30485205167d6395142335bf73d0940014fe725834136f3d43543400067c4159640106f710587404d67e72d9521106bd41992101ad7c7258254007797099150006bf43586400067d7358254067e6514852002cfc70191100067d61543400b67f745944022779309521023f6d32541200aef6645051002eef7258840096f774584400057f7050950256ed65485200aebf4119121024fc755844000cfc71d91200073f42541401a77710951410047f75592200067f50d891000cfe715912000cee76d09210afba70d0740005dd73991211b57e73586540067c435961002d7e70d85500057d74485500ae7c6550b400073d4358a54005f77448510004fd709912100cfc71d8910135dc735812102f6e205412010cff70591200ae7e6495220007eb70509200067d70d954233e7f63951400067d63d95210ae7f609514000fb
  | 23 => 0x1000b04300021c00101300610c1110140380001ee0460120410340d306d01901200500007b04603100000100100300307e06501c00407f00213a01538211e02c0120af0280050390b501b03c0110e100102d6d500100400d01100302000003211000b00c14a00602002309503601102d00000e00400000a03b00004b00000401201100100000800500b00000300700500209101d01c01b0370020030000020000540190130070020150040010390100053240130150010ff00002c04209f00400000e01003c0000000060ac01001000700200303f00900307801800105601400501500802004b01300700101c0000d700200015201101401d09c11000400c12800000004d00000d0ed00602809b01d0070d600200020f02b00c08619a00001200000302100b0c502100002300300501908800001000006400000b0120010c60ae00a0090cd06c14e00005e09a0b902e3f500602900c00208002603e00b07e00506000102a01900002000504302f04000001b1ba04402402b00302c01500600d00300101a01501300000197301f00500100904a01e37403109c0030000000e202a1140000b60050070000070ab0052f307919d01700201602105900d00c00400200300000003a00400e00000c00200c02c00300e00000003001203800300205e0060030240c105b01300200c00c00b23203200000b05700403401a00500000000d01d0030070f50000fe01302c0be0160021760060070000850160655310350000790030010ea0bc0040020000010010c000110d00301a03c01801301103a0650250000250010000440090851864e809d01700413201313b0092bd00000205501b02500600000101e00a01f00200b00605e00b0002b100108c01e00000000812d00001018f02f00104b0160010000000cf00300000505101d00000300602901e14f01b00600b02716200001600103e00101c00702d00204701501300101400001f02c13900100300200000000200f05407006001b0460dc0000560160030052720300400390080ee04305502a0350010420150000364fc0ae0030000130060580000010000030050100290020030010ea05b0298bf00000f00300100001630f01d0010000251ed02701200200105606a0050316d20aa00400400400000001400001500001802b0252530c900001801800200001000c00203400600900003501f0000060000060010720000fb00a00000000500e0010ed00100d00200a00001b00014800627f00000e0770061d115b00001906800700000255003d1040200000010080000050051e001d10b01200203804800000000200500000000c00100000300301201500001a01d00500e00901000000900001a00307e00815400100025900400000801100100101300604822217f00002901102200601407003402a02900
  | 24 => 0x700001400c00702e0170120e800000401500b02f01400d0010b400000300800100000206300f03c01400200600000100601b05400307701200600500704266b04b0bd00100b02300100000400e00000904f02804d01e00300303101403904e4900070f21f20f20000060b600000204700100200208600004615c00b00801001000200100b0320e101900100300405000000000c1830c107500b03e00005a05900900d1070260b600800201900404800501203300f00400c01a00400049d00000f0060100000cb06100501201e00301b09800000300201502300015100302700803100401005c00f00000700000100104103500800402f0000000000010040cb00105600005100000100400001003000102f04100200017d04201b00c89306b66000703700100221701b00524204900105300100091600a0470e70016540370810010130000d201401923700001f0bc00102007900600001501b00400000000000000100000200300100305c01302a009b4000600e02900901500d01101e00200200307834202900501401c0000007192e700100500007300a00200000301100005700502500000300401101900602700403234602600301403c01c00000000007e00302301305601303201701801102802900500300209e00100e00000101500000400105201b0000010330000000010336b700300100f00005903100001d00400206700700007105a00003009a00600300004814b00000000005700000f01902706401700200400d20a05e00144a00d00700a00100b01405a00000100100612300300000700201500000200100001d00200104a00100000000c00003e02c04200005302600e01d00600600000002b0020570000670e600203400808113c05c00000200d00f00400000002200900000204e08f0310020f40460a201f00100300800200102603607b30c02404566737f01113f02c00003702301f01101600202701001500d00c00500400001e00a02a00c00102000002f0910010005a400b03100200001b03121b00100400000501100008f02d01d00502000000800000100201402600105a00201d22903016900200610d04000013d11100407002004d00900400200000807902002203005b01212705606001801e1c70000020002930010ef0001d200200301d00100403e01400004f00000402701200300002100503825700500106000600600101d00603300004b0190000001300ce00501409b00800101c29300509200a00300100300100809400002000000600a00300c00b6ca02600d02000500102a085027000002
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa75810c365504010fb0e986caa08964f21d43591500043ec2cec90a80a7c3f8750f6550401a3ae7208c8a80031708173191500043f43e61b2a8415a3c848c464540014eb03212cb080166d21d41501100ad1ec3c84322a000c3f7458d625400147908a9ec89009657a0c76d09503de36b96a1b224200c3e621d150500818de40bb4a9100570f1d1435944000557c22a2b1080008de871cd62440014ed03212cb200029b61641588400a54ec26eab188002ae68299121440010fb0bb9ec890803075cd43596400043f438cab024200c5d73984645402b55d0839ac4202970f1d543589106d63ab8ea7b22420487c855d921900090fd0fbaac9100571e15376500400043ec1eeab0e800087d8708464540010fb0e190c8a800317e1d7558c403569dba6e0b22a0aaa5d805d563100011dd0e28ac4200031798f75508400071db22e1322a000c5f7390f65504014bb0632242a8003175cd53191200053ac0cc4b04a815cb47458521100018f0ebbb2802000e3d21d31589100043f438cab224200a3f8650f645402b87ce9a1acb100021fa1d65484404d53741061b2a4200ec9324c1628400187eeba1ac9080021f61c32596102061e3b4a8a12800087d85dcf6444001c5885b2a84a00028fa13315964002c7a432e890a2000c3f601d1625402b56d09992c2200021fe1d63d95420052ec18a9b122000a3d840c56510001caf06a9ac2200031b5c872d954100716316caa128000a6e859cd62100014f300188c8a80021fa1f655894056d3cc04e6b2c2000a6e8290765500010fd0e18acb200029e60054d85200061fb9e87b2a840087e86dcf6548401c2aa6a1ac2200169ea0032594400061eb9e87b2a8000a6e820c4645400147d05208c8a80570f1d06458950006b210eeab024205c7571d4064441c747b0921ecaa0b6f1b5cb53d91210043f43ecab224214a9d841c9631002bc3ae7208c8a80038754d43d85400ae1fa1ae7b2e80aae2d4054d62100014bb063a2cb080021f61f32d974054f4798286b108002ae48258521900010fd0eb2a83100028f209431915002d3d40062b288025a5c83589504402b878e8322a08800f179cf53991210052f418e1b2a8400a5d831536250401c6d03210c8a80121fa1774589100061e32ae83024205a7a809cd65840010fd0ea9ac48805727d0173991215361f3ae87b22400087f855d9424402bc3e86b1ac52a0561f21373582540243fc3ec7b2a8452c75711536448401878a8b9ec8900568fa1332d97400062eb9e61b2e800087e87cc3655000163b062a0c8900029ba0871594400049e43a84a868000a7685cc961100010fb0f20ecaa00029ba1641588400ac3f426e7b2a8000a5d8315364480018bae7108c8a800317dce43d95212043e432e12a28400a3d83153644402b4dd09a9ac42005a1fa1e4359440
  | 1 => 0xb0e21acb082338b95364d09210045fc22eab224000a76810cb65d0157c3e813aac6201031b1da54485200243e43ac8a822015e1f6350d60950010fb07baac9080561fe1575992200043ec3864b04a834b348150f65505550fb00b9acb080562f21173589100ac9fc18e8a828000a5d831536150801c3aa6a1ac5a08038be1543588400061fa18ec90aa00487f875d764480018bd0cb98c8a80578da0641191500049e422e6b12a015e365450d61101d147b0931ecaa11028f61072582540043ec3e64b2c8000c3d43dd941540010fb0f216caa08562f21f43589102043f438a8b24200087f855d3604842b56d0829ac2200c21f61f65181420062fb22e6322a000c9f7458d21100079b0e7182c488057879ce41191505361e3ae86b22200087d8790f654840147908b12c2a83830fdd0655814154e56b9286322401587e84dd562440014dd0538ecaa00030fdd54358b400243f42ceca0a403487c8750f65505198dd053b4a8908570f1d343596200ae1e3aa87324408cc76819da54484090fd0fbaac5a00030fdd474589100051fc22e4b2c800096f825cd64541d147b0921ecaa10561fa1f65d01400043f43ea6b244000e1d5350d62d000127b063a2a0a010e1fa1b75509410ac9f43ee8a828000c5d7354c64440018f2e1186ca908568fe1d43d97400ae0f422e6322a000a3e84ccb655042b0fd0e190c8a820f1d5c750d91210ae1fb9c84322a00087e8715360484010fb0f986caa10029b61673588400052ec18c9b0aa000c7b53dd9401002b0fd0ea9cc9080021f61f649512100536c10c2322a000a3d840c9659002b878cbbb285a00574ed0170951420043fc1ae1b2a8200c3d7350d651002b0f90fb2a43a00030fdd543592200051e42a87b224000a5d8315164440015cd0da1242880021f61f53d91100052ec18a9b0a40ace1f509d1631002b878e9212ca200029d60462991500061e3a8e8b12200087d859db41481330f90dbaac0908561f21f5399220004aec18e8a82200087d8754e64484018bee731ac12a0561fa13735944000c7a40ae9b12201593e84dd52150001ac843baac890a9f171cc54589100043f43864b04a800b398015064440033cd0fa1242880030f5ce42191500043ec06e7b2a424387c8759541900010ff0ea9ec890803175cf63d95420043f43ca9b028400e1d6350c64540472e902b9ac8a80568fa1332582540062eb9cc4322a000a79801d7604848d0fd0dbaa84a00568fa1073594400053cc04a9b028400e1f6350f654840187eeaa1ac4880031e60376509500061fc3a86b2c2000ace8214563100018bee6b1ac52a003178c1731915053e1fc3a87b2a8000c5d73c8464540033cf0eb8e84908024f211764855000536c1063b2a800487c855cf60505498bce7a84c8908121f21776506200053ac0ce5b2a8200
  | 2 => 0xd43d954100476c3862b108000a3c845c565880078bce6a9cc9080028fa1332596100ae1e428e8b12200487c855cf60508014ef0aa12c2200029ba0a415825455d2f428eab18800087c87595219002b878a8b98c888056ab21171588400063ab88e2b04a800c3d435c365504010ff0ea1acb101021f21970951410af1db8686b04a8a9aaf8050d6210153c6aa0a1ac2200030fdd5435911002d1e43284a828034a76810cb65505a1a76e1a1ac8a8002ad610535844000572c08e6b108000e1f7350f655006b4dd0418ecaa100297a0c74596100ad1f42260322a000c3f7350d65901574eb01a9ac22000f331cd32d812101476412e6b242000ce5711c5621000147b0939acb080571b1da54509200043f43ea6b242000c74655c460508492e90eb0a42a80029e60365181210045fc3ac83224000a7980dd760508033cd02b8684908029760c5458620004bcc00e890aa00087d87cc76550001c3aa6a18c88800e2fe1d43d91200043ec3e64b288015a3c8454c64480014db0a18ac4200d78b18a545094002dd840282a022000e8d5350d621015947d0821acb200030f1d3625855000637904ed2a242dff2421d0f6548555c3a80baac620293171cf50589100053cc00ca3028200a5d8508563100012d90ea12a0900038758d4358550004bcc06e7322a000e1e6350c645400147b0839acb080169ea0031596400062eb98c6322a0ace2d50d0d621000187ee8a9ac4880028f61020d95410af1b2a6a8b088000e555350d61100018eae238ecaa10021f61c43d95210061eb9e87b2a8405e3b64543405000147b0e2a6c8880030f61e42191500043f43ea7b028440a7a8098d60950018bee8baac6200021fa1e42596100049e43e86b12a00087e87cc565880010f90ea9ac4880028f61f64991500ae1e2a2e63224000e1d8315364481a5a72e1b24c8a80034d88474585500043ec3aa7b22208ce3654d93414840147d0818acb10002ab61273588400061e2a6e7b2240a9e1d3050d65900014ed02192c12a00356d8173191500043f43ecab0a8414a9d841c563100814f100b0ac12a0030f1d764d012000c7a40ae6b244000c5d73cc3655080117f08baac4880030fd9774581210053cc00a8b0c4015cac425c864440010fd0f212cb200030f1d363585500053cc0484b04a8008bf8759064484011bf06baac4880021fa1c43d95420043fc3ac8322a000e1f8350d6588001c38e6a1ac12a002b9a0875584400061f42ee8b12200087e871cf655080183ee6a1ecaa0002c760c54191100043ec3ce7b2a8000c6f655c8605042b0f90ea98c8908570f9d074d95212043f438eab242035a3d841cf655080147b0939acb2000317e0d735825400537414e2b04a800a3d86904645400117f08baac5080028fe1171596201b68e39a86b14a803c5c73d4d62440010f
  | 3 => 0x6b04a80087e8710f655014b878eaa1ec0a08d61f21d6358a5402c7a43a62b0c4000c3c75d91404402b4f301b2e80a026a9d21931d95210af1a2a286b08800087f855ca648400b4f50020acb100021fa1f50591210051ec2061b2a848cea44119121480014790aa18c89026a9d60774d95210ad1f420e6b04a80087e869d921540014bb062a6c2a00029760c10d95420061e308e8b0aa000a7585cc9611000187ae6a1acb100021f61c31d9542006363aac49088000a798018f65484018eb033b4a890802ba600315884001572412c29088000c3c545cf6444001c3aeb3a2c6200021f61b75506400063dc2eeca00800087d879cf655080717f0ea1ec8880021fe1576484400043ec3863b2a8015c3c74191215400187ae83a6ca9085717a1173191500243e42ae6b168000e1c7350f65504010fb0f21aca2000317601731915000537410e2b2c800087f855d9219002b47d08192ca2031f8b98943d89500061fa1eeca12a015c3f7550c644842d0f90eb2a82200038754d43588400ad57424a6b108000c5f835cd65100018bae6a1acb200571790173191500043e43aa6b242000e2c42d954250401c3d062a6c8880021fa1f32594400060eb9a86b2c2000a3e840c7655000b1ed0f98ac2200029b608315825400536c1483b2a84038bc8750d644800147d08186caa09021fa1e43d954074d1f420e7b2a8440a7a8090d6095001878c43a2c4a80568fa1332191500ad4f426e2b188015c9f435cc644808147b0839ecaa00035908476951210061e43a86b2c4000dc4215cc604843f0fd0e21acb200ba3d61f64d05210051ec2062b2c8015c3c7410965840010fb063b242a80024fe1d64191505552fc02eab18804087e8798d60950018b904b98c8a80568fa13651912102d3d40064b2c80008f6870c9611000b4d90c90aa0900029da1432584400ac3f43ee8b2c400087e87cc765500018bae7b1ecaa000387e0d43d95400061fb9a86b2c4000c6f729c9659000147d09986ca908028f61063191500ae1e43e87b2a803587e8790765508014db0418ecba00025760c74541200062fc1ae6b2c2001ae686d85214802b27d09baac5a00db0fe1d43596400043fc02ebb224200a2e82904645402b83cc8b98c8a80032ddd064485100243f43eeab222000c3f75d0d61d000117d0ea1ac4882970f1d543587400043ec3864b28800087e870c7655002b83e80b98c8a8003875cd43594400043f436e7b2a8415e1c5490563100014f30018ecaa10574b10970951420064fba6e6b1220cae3441884645400187a86bb4a9080568fa1263991500068fb9a86b0ca80487c85dd942840018b8cab98c0a08029b60a71582540043e43aa6b224215c3f87d0f65501378dae4328c090816cea034154340006363aac4a0880038bc84dcd644402b8b886b9ecba00030f5c
  | 4 => 0x15080147d09a86c890802976177258c4054f0f98286b288000a3d8690b6454001b8843b9ac0908121f21573589100059a422c290aa00087e871d561d002b8790fa1eca9088e1f21d63585500043fc02e7b2a8400c5d7318f6550401c3ce6a1acb100569d21971951100af0fc1a87b2e800087c87595418802b8be80b98c8a805717d0573191500061fb9e86b288000c3f845d76448001a3ae7a18c8a800327dcd43591210061e3a6c6b12a01587f87d0f65500018deeab128220003175cd53191210043ec06e7b2a821587c845c36548559c5ea1a1ac420006b960b64d05210ad1f42063b2e8000b368190b645400147b08086caa13474e5c3439915002c7b436e29022005aac86509404802b47d09b18c8a8003171d473589100052ec18e1b2a8200a3e8408365504014eb02310c8a81029ea0261582545655ac0686b088000c5d7358e645400b6d10090aa090016cea0342543401a53b40841b2a82058ec874c96284001c6ea6a1ac2200021fa1a74485500070ea9a87b1282038bc8750d644840147d0939eca908039518d31d95210053b40864322a000c5c305cc64540494dd05b1ec4a80d69ba0810d9542006e210ae73224200e8e5350d621000187a863b284a80029e60271582540053ac2ce6b088000a3e841cf654842b96882b88c8900021fa1c65589410ae0fb9a87b2e800087e8790d6584001c38c6a1eca908561fa1373d952112caf418eda0aa00087d87cc4645402b8f2e1b86caa00561fa1373596100ac3e422e6b2c200087f865cd64540014db0530ecaa00021fe0d7695220125b34168290aa015c9f435cc644415187ce9b24a8880162fa1376487400051f42662b2c40009768795121440010fb0f21ecaa00568f21350191200ad1f424c6b04a800c3d86dd161540010f90ea1eca908024f60c74589500062fc02e6322a035e6462951214400b4d90ca12a0900a23b61f64d09210043ec3e61b2a420093d83dd1625400147d0939acb100561fa1f31d97400053cc06ebb024215c1f435cc64540010fb0f996caa000327dcd43d81210af0e42ce8b188000e2f53d0d6210001c3a87986ca908028f61331594400043ec36e890aa000a758198b65500014eb02392cb080030f9d2769512011c3ec3ec7b0aa000c5f7350f6550001a5c843a2a0900029760c745962012c9ec3e86322a001ae681d8921500018dd043b242a80121f21574d89100043f43e62b28800087e878c365504019c842bb2422008e9da0432596100043ec2ee2b068400a79800c965100010fd0e32242a80121fe1f50d91210051f42c84322202aa3e849cf65504370fb0e31ecaa00029760c70d95210af0fa1ac6b0ca815aac845d5621000187ec63a2a0a00029b60830d95210061fba6c6b0aa015a3e8498664540018bcc7baa42200029da1642584400063dc02e
  | 5 => 0x80031b98b755044055d3bc06a6b088000c5f7358d619500147b09908c8a80021f60276951210a56cc00e4b188015c3c74105658806b47b09b8ecaa11021f21d43582540062fc1ae6b2c800087d859d9414802b47909900c8a80029b60870d95420243f42ee7b22400087c87d9521500010fd0fb2ac2a00031bdca72596100ad1e422e2b288015e1c7350f65d00010fb07bb284a80029d60430d954202c7a43a62b0c8000c5e205cc64540010fd0e2a2c4880021f60375591210243fc3ea7b222000c3d75d0f6448001c6c83880c8a8056ad21151584400ad1f424c5322a000a79801d760508010fb0e986ca908021f61f31596200062e32ae63028400c3d73d0d6590049cc8c490aa0880121f21f50591210062eb9c64322a015a3e8419464485578dae5a98c8903768f61243d95214671a208c890aa00087e87ccb655002b0f90fa98c8908030f1d364541100062eb9a86b2c2000e1d5350c64484011db0f20ac4200021fa1f62585500ae1f422e7b2e8000c3c7454d624400147d0998ecaa00029ba0861991502043e43ecaa128000c9f7350d62440014790ba1ec89005707105731915052e1e3aa86b24400087f8750f654842b0fd09b9acb1005a1f21d65508400068fb9a87b2a42abe2f40d4d62100810fd0f21ac12a056a72115258c400062eb9cc7322a0008ee870c562100010fb0fa9ec89010e1fa1f65505400051ec2661b2a80008f58714961100698ecc3baa82200039908565484400243e42ae6b224000ec9324c162440055cb03b2684908029b61731588400ae2f322e6322a000a75811c36550919a68833a6ca908021fa1e54589100043ec3ea1b22200087e870c9659000153b062a6c8880029d60432594400061fb26e7322a000c3f651d160484010fd0fa82c3a02c28fe1171594400051e40a86322a015a6e85d5162100018b8eab1a84200aa1f61b75504400af4bc1a86b08809aa75811c3654840135b05bb283a00021f61e63d95400051ec0482322a0a6c3e75d0f64440010fd0fb2ac4a08031dc40764855002cf4402e890a4000c9d7350e64484010ff06baec890a9b0f9db43d95420043fc1aebb22200087f855cf605042b878c8b9cc8a83135adcb70589500061fa18eca0aa0a9e375050d6110001c6aa7a1ac22000f179cd53992202053d40484b04a800c5e73194604842b0f90fa1ecaa000317d9573181411b62e39ac6b14a8008f7815cd64481550ff00b9acb0800a2f211755874202c5e43a86b242000a7980dd76050401a76c1ba2c4a805787dcd43d97400043fc1ae1b2a840087f8759150480018beea39ac48800f179cd5319121005e8c18e0a0a2000c5d7390d65880012f700bb684a80561f21176952200053cc06ca3028400a798019460508010fb0fa86c89000347a1173191500ac3f43ea03224252c3d741536
  | 6 => 0x61eb9a87b2a800487f875d7644402b958e8b1242200021fa1c43596100053b40ce4b04a81587c845cf65500010ff0ab9ec0a10021fe1573591200043fc18ec90aa015a748454d611014b87ceaa1ec8900021f61e42596104ce373b6cba12420487e86dd560508018ece2328c0a10029d60472596401ae1e3b6eaa128000c3f7550d648402bc68a9212c2200aa1f61f651814146696214e9b2a4200ec9324c361480018eeeab0a42200030fdcf43d9540004bdc02eca12a00487e85dcf644404b0f90eb1ac8a80568fa0a42191500063b38eca302840097980ddb4254001e6282a828088006b920562484400043f43ea6b2220aac757154c64440014eb02386caa0803275d17558c400ad4f426eab188002ae682d8521500018ee203b282a832f8b10b21191500ad5742664b108001ae481191214800183ee6a1ac12a00393e0d53588400056b408e4b18800093c8750550d002b87884b98c8a8002ce60054d9110294b743ca8a124015c3f7550e64880018bca9b9ac4880561fa1f321915011d3b408c9b0aa000d1e645cc645400187ae7a1ac12a2ae1fa1c73594400059741482322a000a3e840c965900018bf06b9ecaa10561f21170d95410af0fb1a87304a80087d86dd541880090f90ab8ec0a10171b5cb50191205361e3ae86b24200087d8754f6448555c6e80a9ac2200025761e73191500062f082e6322a036c3c8750f65504010fb063b284a80570fdc143191501a53a40ac4b0ca800e0d5350d62100010ff0eb1ecaa02b28fa1043596200043ec2ee4b06820087e8710f655040187ae6a1ecba02970f1d54358b400ac3f43843b2e8015a3e8498c645402b0fd083b242a80028f61273d95214d63a3b6ea90a2000a3d8498a64540010ff0ab9ac5a00025e603764855002d3d40062b2c4000a3e8418f654840159b0438ac62005727dcd43992200052f42c82b18800087c87595211006da38e6a1ac32a0168f61b41543400043ec3842b28800087d80dcf65508090f90aba6c0908031719573181211243ec38c9b12a015c5e545ce6448401c3f06a1ecaa08570fdce41191500051ec2065b2a800087d87d42644842d0f90ea1aca200028f61030d95210064e3a6e6b1220008bd83dd162440014dd0b992c42000317dcd30582540058ec18e8a86800095d831db425400b3c90e90a408800347dcd439915054d1ec2486b28800087d879056588153c3a60a1acb10002abe1175588400ad57c0686b108000c3d7390464540051d904b9ac8880029b60831191500061e310e8a828000c3f8750f65d00090f90ab90c8880029da0642d95400af0fc1a86b04a814a9d84dc56310001878e8b1ac2a80038758d43d89500ad1f42062b04a8abc5d30dcd65840010fb0dbaa85080929ba0871596200ad1fc3084322a0008f7815cd648800187b0dba2c4a
  | 7 => 0x1f8350d658402b47908b92ca200121fa1f75591215361e3ae86b224235a6e82907655086b4dd04386caa10038754d43587400043e43aa7b02840093e87d0d61540010f90cb84a8909021f21d62582540043f43e62b04a800c1f7350f65484018b8cbb9ac090b8e8f61273d95410af1c322e1322a00087d870c965900010ff0ab9ac4880021f61e43582540051f43287322a000e1f6350f6550801c3aa6a1ec8880031b5c872582540043ec3c84b288000c3f7458d61540010fb0f3aec8900028f61032d97400ae1f3a686b2c2015aae8414d62100014dd0418aca20002b9a04735884046637a14ed2a24200e64211d9215400187f0ea1acb100571710573191500043fc1aeb322420087d83dd9415416f47d0821ecaa000f331cd325891072e1fba0cab02840095d839d12154001c3ee6a1ecaa10028f61330d97400043e43aa6b2240a9e1f3050d659002b93e86b98c89085697a117558c400058ec18a9b222000d64215d4604842b56d0998ac2200029ee0173582544d63b3b6cba0a420087e8754d64440010fb0e196cba000297a0c10d95420062ec0ae6322a015a3c84d4c644802bc5ca8a1ac4200121f21f53d81420ac3e438c890aa0008df835d92190001c3aa6a1ac8908063ba1e64485200053b40cc5b2a80aa87d879cd6590157c6a81a9ac2200021fa1d65486400061ebae87b22420487c855d9211006147d0939ecaa10570fe1f43594400243e42ae9b0a4000a7685cc5611002b47908a98c8880121f21f53592100ac5e422eab142000a748550d61100010fd0f98ecaa1003175cd30d95210070ea1a61b2a8015ab6841cd61100018bae6980c8a82669da0470d95215361e3ae87b02420087d8790765508018b8cab9cc8908031e5c130d952101e2f39aa7322420093c8750950500011ef02b9ac8882338b10864485500043f43ecab028200ec42158d211002b87f0fa1acb100038754d43991100ae1e3a482b28800487e859db424416b47d0838ecaa00568fa1331d97400045fc22eca122000a3d840c56588001a3ee6a1ac8a8016f820121481100052ec18c8b12a000ae5821cd61100011f700b9ac8908028f61331596400051e42a8632220d9c6d7254f6448401c3aa6a1ac3a12ee8f21172596400ad1f420c4322a00487c855ca648400153f08a8ac6200571721173191500dcbcc04e9b12a000c5e7319460508010fd0fa9ac5a00028f60054d91200053cc0064b2c801587e87ccb65d00010ff07bb282a80021fe157319121004b643a42a8240b4c3e76dd15050187a76e1a1ac2a8003179cf65991210068eb9a87b12a000e1d749d5631002b8be86b98c8a80028f61332594400056b408a4b188000b398010b64540010fb0e10ac12a2a6ad60143584400043f434eca0aa000c3e421d942540018f301bb242a8002976164158c400
  | 8 => 0xe8326c2a8003475cc41191500062eb9ec7b12a000c5c7558d41100010fd0ea9ac5a00028f61330d95410062e40ae6322a000c3f7350f6550801c3a86986cba0052a76137258c400051ec2064b04a800e358190864541554eb00a9ac2200121f21573992100043fc2ae6b0e800087e871cf655000b1e90eb0a432037bc908543d95210055ac24a6b088015e1e645cc64540694ed03216caa08562f21175191100043ec1eeab12200087d87d9254480014db0a39ac4200571715173991210060fb9a87b2a8200a6e82987655000147d08186caa10030fd9574181210062fb9a86b04a800d1d7350f615400127f08b9ac4a80028da0642191500061eb9a87b2a8400c3f7415161880018de403b284a80921f61f64541200070eb9a86b2c20aba6d80d4d621000187ae7a1acb08057171917319150004bdc02ec90aa0128f68790961100810fd0f212c12a0021f61f31d97400243f43eeab24200087d874c365500010f90ea9ac91000297a142158c400243e43ea0b122000c3c7458d62540071f10e982c4880121fa177458a1000536c10e2b2c8000a6d8290565100014db0418ecaa10028fa1641d91200062eb98c7b2a8000e4d5350d621002bc5ca9aa2c4200028f61263991500052ec28e4b1880a787f8750f655094d87ceda1ecaa08029da06425825441c3fc02ebb2240038ec874c9624402b0fd0ea98c8908121f21f53d81210043f43acaa142000c7953dd9401000133b073a242a00039908565486400243e43ea6b224200c3c8750f6548401b48433a0c09085787e0d43191500062fc1ae7b2a4200c5d73c80645400147b0818ecaa01029e20163582540061ea18ec90aa00487c855cd61d00814f500196caa00029b60810d95420053ac0864b2c800087e8754d648802b47d0998ac12a2338d15064485100067210eec9088000a3f844c864540010fb0f186ca908570fa18745414011db340e8490aa01587c8754e64840010fb0f3aec8908030f61e41191500070ea9a873242000c5f7390f655086b0fd0eb2a85201031d44176952100147ac0eebb224200c5d7354e64440010fb0f21acb200021f61f30d95400055ac2064b088000c3d75d0f644400b1790ea1ac9100028fe1943191500061fba4c8b12a00097980dd942540039c8ec90a40882970f1d543591100043fc1ae1b2a4215a3e840c4645400b2f5013a6c4a80029d614735844000573410e6b088015c3c7450d658802b47909a80c888003275cd43d91200051ec2660b04a80597a809d3615406b65904a1ecaa104e3ba1e415884012cafc3ae6322a000a79800c5651000183ae6a18c8a800297e0d62541106c63ab8aa7b224200c5d7354e64480018bee6b1ac2a80169ea02735962066d9dc02c8322a040a788058960950610fb0e31ecaa10021f61b75484400049e43e86b0aa000e
  | 9 => 0x43d95210052ec18c8b0aa000a5e831d16588001c3ee6a1ac12a29b0f9db43d95210043ec2eec90e8015e2c5450d621002b0fd08bb4a9081ee1fe0175d91102053d40065b2e8000c3d631d1505000b1d90eb1285080021fe0f76485504cd36c10e1b2a423587c8750f65508010fd0e32ac2a0003871cd43d95210a56cc00e2b188000c3d7515364480814f50018ecaa0003175cf53991210064fb9a86b222005a7a801096584119d4e85b2682908031721973191500061fbaa86b0e804087e8715164880010fb0f3aec88800317e0973191500051ec2664b2c800487c87589504402b87ce83a2cb080121fe1f50d912001c6e41aeab122000a3c8559064440010f90ea9ec0908570fe1f43582540061ea1eeca12a00087e870c765508010fb0dbaa43200029e60272582540243e42ae03224215c3f435d6644840b5e50039ac2200021f60e769512100556c20a6b108015a3f8750c645402bc690ba1ac2200121fa1776487400ad5bc1a86b088000d3b74dc162540018bee7a9ac4883321fe01731915000c76c16e7b224200a3d840cb655040717b08b98c88834b0f5c364991500051ec1c84322a0058ec874c9629002b87f0c3a2c4a80021fa1c32594400049fc22ec90aa015a9e841c56310001878823b282a8003475cd43d91500053ac0861b2a420087e87d9521d00035c902b12432000317a0173191500ac3e424ed2a2424087e8790560950090f90ab9ac9080db171cd63586540043ec3886b2c4015c9d879d163100012bf06bb242a80561fe1575992100243fc3ec7b2a8015c3c74d0d658400147d0b216c8880029b61471588400071721640322a01587d80dcf65500494dd04326c4a80029b617325884000572c08eab10800087f8758f65504018b90bb9ac4883261f61d30191500243e43ea6b16800093f845d942540818f4edb2e80a00038754d435834154f4a98286b088000a76811c96590069cc8c32a2429033f4edc143591500ae1fb8687b2a8015e3b4050d609502b0fd08b9aca200028760c54d91100051ec18a9b224015c1f435cf65d015353b0f3a2c6200038754d439922054d1ec2486b2c801587e87084645400127d0ea1ac4a82a78b5414358840004bdc02e6b0aa000a79801d76050401c3aa6a1ac2200021fe0173d954100537410c2322a000c6c76dd5424802bc72e0a1ecba0003ca50950501204663ba0ced2a242ceb398099064540078b8e6a9ac488003171cf65581210ad2f424eab188015c3c74d0f65500690f90eb1ac32a06e5e60274d85500062fb02e6322a015a5f8555163100814f50018ecba00561fa1d53992200053ac0c84b288015e1f4358d60950010ff0ab9ec0908576cd0170d05410062e2a6e6b122000a3e8498f65484090ff0fa84c8908021fe157650a100051f420e1b2a4200a5d85909631002b87c
  | 10 => 0x90a4003c5e7354e64440010ff063b282a80021fa1c54d81410043ec3e64322a040a7a800c960950015ab02292c6200931e1d950501200243f42ee4b06820487c855d921d00018bee6a1ecaa08db171cd63582540ac3fc02ed2a42000e1f8350f655082b47908108c8a80030f98474585500070ea9a87b02820091d831d150500010fb0e10ecaa00021fe1570191210070f39a86b2c8023974815cd62540014bb073a6ca908030fd0f76485500051f42063b2a842593f8750f64540090f90ab9cc9100564fa13755874056556c0686b10800087d8790960951ad96ae3a1ec8908561f21173582540045f43e86b12200087e87cc96095157c3a813aac6200568fa1063991500053741062b2c8000bc9831c121480090ff0fa9ec89080317dd563504400062eb9864322a0c6d3b70d0d62540014ef0ab92c2200568fa1321191500045fc22eab222000a3d840c9658402bc3cc9398c8a80030f21d43582540ae4f422e73224200e1f6350f655042b93ee6a18c8908121f21573591211a43e43ecaa12821587c84dd5644400b1d90ea92c42000317a0573191500043ec3e62b288000a3e8590464481c547d0821ecaa08038754d4358a4037d1f420e1b2a8200e2f5350d621002b8bb08b98c8a8003075ce421915058d1fc22e4b288000acd829056310047cc8c290aa090003171d563484400ad1f42662322a000a7b805c9609500183ae8baac6200038754d439912153c3e43a86b2c80b8d397050e64540014ed0b39ac2200021fe1576506200051ec2660322a000c7661dd542100010fd0ea9ac8908030fe1d43d95210051ec2442322a035c6e62dd542100a50f90eb2a852000317dcf505891002c5e43ac8a142005af2800c9611002556b0839ac220003175cf63d95210053ac0ce4b04a8018bd84dd762504474ed03212cb080c21f61c43d95420070ea9a86b244034a6d829da54484010fb0f21acb100021f60f75592200051fc22e2b2c8015c5d415cc645415987ae1a1acb080021fa1f53587400062eb9ec7b0aa000e1e7350d6584001c3a86986caa08570f5c343d95401b68e39a86b04a800c9d7350f64484090fd0dbaac0a08561fa1f53191210061eba0c9b0aa015c9c645ce64484012f700bb282a829b0f9d743d91210043ec2eec90a800087e8708560950014d904b1ecaa00029d60472594400043ec3861b2a420087f835da548400147d0839acb080562fa1f74589100af1bc2e86b088040a7a800c5609500187ae8326c4a80021fa1c43d95210051ec2063b2e8000a7a8018f6548401c3a86982c12a00317dcd63d91500243e42ae7b024200cb77458521100014f700a1ac12a2aa1f61e73596100043f436ea90a80d7cad72d0f644848d0ff0eb24a9100571b1d9729512000732b12c290aa000c5d73d4264484010fd0f2a6c09080317dcd
  | 11 => 0x504090f90abb283100169da1b71541102051ec20e3b2a8000a3c8454f64441554ef00a9ac22000327dcd43592100053b40cc4b04a80087e87cc5659002b0fb00bb4a9080021fe1571992200053ac28e4b0880a5c3e7550f644400187a863b282a80021fa1c655814200536c1482b2c8000c9d7350f6444001c5ecbb2684908031bc8076485500061fa1ae1b2a4215c3c74151618802b878e82a2c50800f271cf435891001e4e39a86b224200c3d7515364440018bee6b1ac12a003175cc62191500043f43aa6b22400487e86dd560484010fb0f21acb080025de0573591500062eb9e20322a00087e8754d61d002b87f0fa1eca908030fdd0645895054f0e98286b2c20018ef87593424840147b09318c8a80028fa1032d954000536c14c2b04a8a6c3c75d0f6050801878cb3b682a00029e60243582540043f43862b28800087e870c9658400187ec1ba2c4a829b0f1d743591200062ec12e6322a000e1d5350d6448001c3aa6a1ec4a008e1f21d62585500043f43ecab028400e355350d6110001a3ae6a18c8a800317dcf30582540ad3b422a6b088000c3f73d0d609502b87ce9a1ecaa00021f61676d09100043ec3e60322a034a76810c365504014f500196caa08031b608764855000573408eab1080038dc835d92190153c3e60a1acb100030fd0d76952200ad2f42ea8b188000c5d73d8f645400147f08108c8a80029de1543584400ac3e43aa732440abc5d30dcd658800b6e10090aa0880121fe1d75d912154f17a8286b1080158bc845d4644800b1e90ea8ac2200029d61432584400043fc1aebb224015e8f8350d62100014bb062a6c888056aba1031588400070eb1a86b22a0abc5f30dcd65840018bae6a9cc91000347dcd43582544d537410e7b2a4200c3f73d0d6584001b4843ba2c090803a650d3058a100ad3a426a6b088034a3c8650f655042b55d0939ac4200030f19674181210062fc1ae7b2a8015c5f435cf65d0001c3ce6a1aca2005727d0d73991100ad1e426a63222000e1e759d16310001c5aa7a1ac4200021f60f76485500051f42021b2a8400ace821c563100015ab03212c62000e2f21d43591100ae1e3a286b04a800a76851c9611000147b08190c8a814a1fa1f65509410053cc00e7b2a4200a6d821c3655040b1e90eb0a4220056972117558c400043f43c61b2a840087c8754d644406b4d904b1ac52a0021fe1d53d91100043f43865b2a82a6c3e76d0f655014b87ae0a18c8a800a2f61375d85420052ec18a8b224205ab48650740440010f90ea1acb0809e1f61f65d91210051ec2662b2c4015a3e84cc9651000187f0ea18c8a81028f61072d95400053cc0062b2c8015c9f435ce644800147f08b92cb080021fe1d64951100243e42ae2322401587e87dd1658400147b0818ac12a2f28fa12735964000657ba0c8
  | 12 => 0x30fdd254589102043e43a87b2a8000a5d85dc5631002b8ba80b98c8a80db479cd43982540ac3f426eab222000a5e85dc56310001a70e9b82c2a80021fa1c65585420ae2f212e6322a0a5c3c7550d644842b8790fa1aca200568f2116399150006b5ba8e090a400087f8750d651002b87d08b98c8a82ab1b5c9531912021e1eba0a9b12820087d8798f65508018beebb9ac4880169ea0032596100070f418a9b224000a3d841cf65485816d700b1242a80021fe1573992100ad1fc3686322a000e1d7350d65880018bae7980c8a80028fa1330d95400072aa9c86b08800087d870c3655040187eeba1ac8900028f60f64991500ac3e422e6b288000c77655c46050801878843b284a82cb0f21d43594400ad36422a6b10800087e87d4d64480018bae7b1ecaa08038750f30d954002c5e43ac8a0c4000a3c8550f64440810f90fb2a82a00025e60376505500053cc0084b2c2025d1e7350c64541354dd05ba6ca90803475cf439915055717a02a6b108000c6f75589211015987ee1a1acb080561fa1c31d97400147bc3ac9a0a4200a3e84d9764484018b8ebb9ac48800387dcd43d95412049f430e8a828015a3f8350c645400147d0939acb08003175d17558c402063c302e12a2820487c855c664880018bae7986ca908121fa1b75585400af16324a8a124000b398010764540010ff0eb12a0880029d61643584400053b40864b2880a5c3e7650f65508814f100a1ac12a11a9ea003119150006b210aebb2242008ef825cd644802bb5680b8684a10167c20174485100ae2fc1ae7b2e8024b648258521540010ff063b284a80578718d43582540053cc0082b2c400087f855d921d000317908baac5a0ab28fa1043596100043f43e61b2a8200a9f8454963100012bb063b682a82af174c373596400049ec18e8b0aa099a6c864cb654840187aeaa1ec890016b6a007158c400043fc3aa73224200a3e841cd65880010fd0f996caa08028f61a42191500ae1f3a687b2a4200a3e840c3654844b0ff0eb1cc8a80030f5cf43d95210064fb9a86b244000d1f7350f655080147b0998ecaa00038750d30191500070ea9a86b0c808cc6c429da5448401c3aa6a1ac5080028f60242191507451ec24e7b2a8400a79800cb65500015cb043aac2200038d21543584400061fb9a86b28801587c87d4e64840690fd0f21ecaa0b9a8fa1371d954255d37c06a6b108099a6d821cf65484550fb0e21ecaa08025de0573589500070ea9a86b068400e3765d9341485338d8edbaa42900030f5cd43596400059b40c84322a03487c87589619502b0f90f2a2c48800347dcd43d95404d537410e1b2a4200a758190965900014dd04386caa08038718d43d95420062f412e6322a000a778158f6550001c3aa6a1ec0a10964f61f43991500069db00e8b0aa000c5d734c365
  | 13 => 0x70e39a87b2a841587c845d664484018bf06b9ecaa08021f60c76505500043fc3ac5b0aa09ac6e62dd52110001878ebba2c8900029e600215825453e1fc3a87b2a8400a6d821c5651002b47908988c8a8003475ce42191500243e43ea7b028200c3f75d0d64484010ff0ab9ac8908561fa1b75487400051ec20e6b2c8035a3c8650f655082b47d08392c12a0030f9d2769511011c3ec38c9b0aa00087d878c3655080147b0998ecba00163d21971d09106169db8286b0aa00097b805db41540010fb0bba2c4880031720173191500ac9f426ea90e8015aae84cc562100018bae631eca90856ad21152584400045fc3ac83222000c6e7219460504010fb0f216caa02331d10676951210051e422c5b0aa01587e87cc064540071bd0fb9ac4880029760c54592200243e42ae5b028215ab6840c961100014e90aa12c2200029ba1731588400b43f43ec8a824099c7661dd5211000147b0e2a6c8900038760c54d9110004ba43a42a822015e1f6350d629514b878eaa1ec0908029b60831594400051ec24e7b2a8015a7684d4d61100079a8e698ec0908d29d20563586540061e3aec9a022000c3f73d0f6550557c5a81a9ac42000f271cd43d81210243f43eeab224000a7980153605042b53d083aac6200029da1643584400043ec3e65b2a8215e1d7350c64540014dd0a38ac4202fa1f21d62543400ad1e42620322a040a7a8098960950090ff0fa86c8880029d60432d95400062eb9aa732420008df835d9424400b1790cba242a00561fe1f43d95210066cb9ac03024200a3e84cc7655080187e86b86caa10121f21f50591200053642a86b10804087e87989609502b0fd0e188c8a80568fa1061191500043ec3e62b04a800c3d75d5364480090fd0bb9ec8908029760c64d89500061fb9a87b2a803487c86dd5605042b8b880b98c8a811a9ea00321915000696b9084322a000a6e82905651000147b08188c8a80030fdd0644855012c3ec3ec6322a00487c87d4d624402b47d08196cba00021fa1e4359620005e4c18e0a12400487c87d4d61d000187b0e2a6c88806e1f61c43d95400062eb9c86b2c80ab87e871cd6584001c5b05208c8a80570f197765074052e1e3aa86b24201587e87d4e648415355b00a1ac420002b36085158c400043ec3842b2c8000c3c75d91404800183ae6a1acb1026b599cb65d05210061eb9a86b04a80087d83dd5644842b8bf06b98c8a80030f5d543d91210063b408ec90aa015c3f435cc64540018bae7b18c8a800317dcd63591500051ec2661b2a84a9a3d8490d65880010fb07baac888056ab21151588400ae4e3a2c69088000c3e621d1625400187ee7a1eca908021fa1c73582540043f43ea0b12201687e8790965100010ff0eb24a8900925b20973585500043f43886b2c40008ef825cd64440010fb0e188c8a8
  | 14 => 0xd434c36550801878e9b22a0900031704173191500047dc3ac03028200a75810cb65d000147b09996caa00121fa1776485401a51ec20e1b2a8215a3f8610464540010fd0c3b4a8908030f5cd43596104cd3b408e7b2a4200a79800c565880090f90fa9ac9100038ee0143582540053cc00a8b142075a3e841c3655082b87cc9b98c8a80023d61e42584400043f438cab1280a6c3c75d0d6244001c3aa6a1ac9080028f61331582540062fb9c87b2a800087e8759541100018ee213b4a8908029e60273582540053cc00a9b02841587c84dcd65100a50fd0fb2a84a00030fd0e769512100536c14e3b2a800093c8750550500014ed03396caa00570f1d5439921000636c14ed2a242008fb8758060508018bae631ecaa100327dcd4358b400052ec1841b2a820087e87d4164481554db00a9ac4200029da1473584400069dba6e0b0aa0a9e973050d611006d8790ea1ecaa1002a760c54d912012e2f39ec6322a000c3c65dd16048555c6a80a9ac2200562f21175589100043ec3ea7b22420487c855d9424402d0fd0f20aca20003175cf32191500062eb98c2322a024a6e820c565880012df04b9ac2a80028fa1032d9541004dac0eeca168000d3b601d1625400147b0939acb10002b56047258c4009d56c20e6b108000b1d831d150500010f90ea9ec0a08030f5d543d911002c7743ea4b10809ae6462dd5214402b87cec3a2a0a009e1f61f651812102c76432e890a4000b39801086454001c3ac6a1ec8a80021fa1c21596400ae1f322e6322a000e1f8350f654857347b0921ecaa005787d0d63982540243e42ae6b22200087e871d5644800127908b9ac2a8002ab60a41191200052ec18a9b02820087f855c864440010fb06bb4a91015a8fa1370d95400ae2fa12e6322a000e4c634cb65484018bae7188c8a80561fa1376485500043fc02e7b2a801587c841d941540010fd0fb2ac0908570f1d54319121006d2108e8b024200c3c54dcf644402b87eeaa1cc9080028fe1231191500043ec3cc7b2a820087d870c3655082b47d08192c12a00317dcd63589500055ac24e6b08800487c855cc644840b5c90c90a40880038750f30d974000578c0064b088015c9f435ce6488001a76c1ba2c2a80568fa1330d97400049fc22e6b0aa000a74855c961100010fd0e10aca200028fa1332596400053741061b2a8200e6421d9521500053cd04b8682909029ea0021582540043ec3862b2c4000a768118a645402b0f908b9acb100023b61c51588402053d40482b04a815b388454340500010fd0f20acb100021f21d5358b400043ec2ceca122000a79800cb65d00014bb062a2c5200021f21974485500ae1fb00e8a82800097b805cd625402b87e80b98c8a80570fdcd43d97400b51ec20e6b288015a3e849cd651015d87ce9b24a8900570f21f435961000
  | 15 => 0x7a1aca200029ea0073d95210053ac0864b04a800d36411d1504400193ee839ac4880568f21232191500043f436e890aa000a6e82905659000187ee9b1ac4a800317d9573181420061fba6a6b122000c3c8750d65840018bae639ac12a0568fa17541912000c7a40ae6b22400087f855ce648815f4f30139acb100570f1d143596100ad1f420c6322a015e1f8350d651000187ee82a2c4880163ba1f32588400074ca1a60b122000a5d8315162840014f30120ac12a0030f1d162585500052f428e4b188000c9f7350f605082bc590ba1ac4200029ba0831d954000637396ca3028215a3e840c5651002b55f06a1ac4200021f61c63191500061fa1eeca0aa000a6d8290565880078bce6a98c8880028fa1065d91210243e42eec9088015a5c849d563100014bd06386caa08021f61f30d95410ac3e43e86b2c2005aea800c56210081cb060986cba000317dce73582540043f438e7b2a4200c3f75d0d648802b8b886b98c8a80021fa1e54d81410070ea1e61b2a8200a6d820c3655040147d09986caa0852a76107558c400af0f39a86322a00093d83dd161540014bb062a6c0a139e8fa1043d95420043ec1aed2a4200597a801d121540014db0438acb100570f1d24159620006b210aeb322420087e870c560950010fd0e3aac8908570f9d074596200ae1e3a287b2a80029e687d05214800187f08baec88800297a0c70d95210062eb9842322a000c3f749d1658802ba7680b84a8a08038754d43d81210076898a60b122000c3d75d5364440018bd0ab9cc8908028f21943991504cd36c16e9b2a42a9e8d3050d621002b87f0c3a2c2a800387d8d43d95400043ec34e890aa015ab4845d561101554bb0f3aac6202669da0774d95210ad4f420e4b18800087d879cf65484018beeab1a84200038750c43d95400062eb9a86b2c404087c8758d609500147d0da1cc8a80031d60476485500055bc22eab088000c6d725d7644840b5d50039ac4200030f61c54d912071d1ec24c7b2a8200a3d8690764540112f10ea8280880121fa1676509100070ea1e60b04a80087e871cf655040183ae7208c8a82f61f21d61543400ad1f42660b04a81fa3e841cd65900010fb0dbaa85202970f9d943d95410056741482b188000a5d831516448001878ebba2c8880570f1d264585500051ec24c7b2a42008fb8758060484014bb062a6c4a00029ea0031d95420053cc0065b2a8200c3c75191404800187eeba1ac4880028fe1162541100af0f2a6a8b188000c5d734c8645406b4dd0538ecaa10025e60376d05500052f42ee4b18800087d870c565100018becab98c0908039908765487400049e43a86b0aa0a7c3c8750d6590155c3e80baac6200038754d43d91210045f434e890a8000a3d84986645402b8f6c13b4a8a00029d20563d954000556c24a6b108000e1
  | 16 => 0xd952121e1eba0ca3028200c74751d9414400187ae7a1ecaa0aa70f5c143596100062eb9ac6322a0028f68799121440078bce6a9cc8902b38d54343584400043f438eab12203587c86dd560508474ed03b1ec2a80021fe1d43596100071bc2a86b088015c3c74191504802b0f908b9eca908021fa1e41596400055ac2664b0880abc5f30dcd658800193ae9baac6200022f60c745891001572410c890a2000c5f7354d624400187ee7a1acb202e30f5c143d95400061fbae86b222000a3c85d0f64440018bf0bb9ac488056ad21172584404ceb338ecba124200c3f74991615400793ce6a1cc8908028f610735962000536c14e3b2a8405a3d86d0950d0001c3aa6a1ac4880030fd0d70d95410051fc2464322a000a6e851cd621014f0ff0ea1ecaa005787e167458c400073210eec90aa040a3c8650f65500010ff0ea1ac12a0021fa1f63591500061fba6a0b1220d5cad7250f6448401c3ac6a1ec2a80030fdcf43596200062f39eca3024200a3d84ccb65d014d878eba1ec0a08028f21172596100053cc0064b2c2000a3d84cc365484872ed0f2a282880031d5c661991501a43f43acaa0c8000aad840c5621002b47d08190c8a80574760c74541400ac3f424ed2a2420487d80dcd65840818f0c0b84a8a10028fe11639915000536c1062b2c8000e99434c3624414f0ff0ea1ecaa080317d97735812152e1f3b287b2a420087e87d9521500090fd0fbaac48800307dcd43d95421843ec36eaa108000a79800c960950010fb0f98ecaa10029da0430d95420ae4fa1ae73242000a6f855c562100018bae639ecaa1003175cd53991210043ec3ea73224200a75810cb65504014db0520ecaa00021f61e30d95410063ab8aebb224200a76810c965900010f90eb2a85080121fe1f53d912020636902ed2a44000c5e63dd54110119c58a832242900030f5d5439912100c76412e9b0a4000a5e85909631014b87ceaa1ec890b868fa1372d95415bd1f420e7b2a8000c3f75d0d62d00090f90fa9ac8880023d61c32584404d53ac08e7b2a420087e870cb655000187ee93a2cb0808f1e1d950501100243f42ee2b068434a76819cb65504014bb062a2c320057875ce42191500062f398ca3028200c5d734c464540018becab9cc890aa72d5c543191100051f42064b2c2015a9e84dc9631016d47d08396caa00db179cd63982540061ec2ee8b12200087d87cc960950011ed0e292c2200021f61e43d9542006b210aeb3024200d1f7350f655040195ee8b1242200570710973191500ad1f426a03224200d64215c254484014f30018ecaa00024fa1376d05500076898a61b122040c3c76d9541500498dce5b16c2a82970f9d543991210af17c2e86b108000c5d734c365d002b87ce8a1aca200028f21564191200062eb9c86b2c2015c3c74951624400187ae
  | 17 => 0x2a4200a3e84d8f64540079a8e698ac4882aa9be015358840014f3c3ae5a0a4234a3d84dcb65504010fd0f186ca9085747a0c74541400043ec3841b2a820087d87cc565900012dd0f2a242900121f21476485400061eb9e86b2c400093f845d9415404ba3ce6a1ec8a80561fa1c32d97400043f43861b2a820087d8798c645400147b09996caa085787d8d43586540070ea1e60322a000c3f74151628402b8e8ecb8ca8880029d60432596100ae1f3a287b2a801687e87d91504406d8790ea1ecaa00d28f61073d95416a65ab8a87b224200e388050d6095001c5aa6a1ac4200030fe1d43594400ac3f43a60322a00087d87d43644842b878e9322c4a800f179cd5319120005e8c18e090a2023a748158d61540010fd0fa9ac8908030fdcd43596100ad37422a6b1080c8e2e62d0f625400187a86b86ca908021fa1c20d95410063dbb6eaa00800087d83dd562d00011790ea1ac4882970f9d943d95400043ec3865b2a8200a6f8550d62100494d904b1ac4a80021f61c31d97400053cc0063b2e8034a6d82d92544842bc3ce7210c8a808e1f61f62d85505a53dc02e8b2c8034e3764d97415044b2b906bb242a80031761573991210ad1f420e2b04a80087f855d361480090f90abb285080038754d43d891011d3b408e4b2c2000e2e82904645400127d0fa1ac4a80029da04621915062e9db8286b12a00087f8759150440010ff00bacc8908570fe1474589100053741063b2e800087e871d562d00018bae6986caa1266d920532d95210063cc06eca0aa000e99434c3614800147908b12a0880038754d43991200061f308e8a828034c747158560950a587ae8328c0a1003475cd43982542061e3b4a8a0a8015c5e415cc645400147b09992c12a0561fa1176952200043ec2ee8b142000c3d43dd9215402bc58a920ac4200d69ba0830d95420043fc2ae23224000a3d840c765508014f300190c8a80021f61773d91200053b408e1b2a840087d870cb65500010fd0fa82c5a02ae976027558c401af17b26cba1284a9e1f3050d658400b5590ca1680900029ee01715825402c7c402e6b2242a9ab78050d61101550fb0f39aca201021fa1c7559220004bdc02e6b22a000a3d841c3654840147b09988c8a80570f10573191500ae3a3b4a8a0a2040c747695121440014eb0b212c22029b0f1d743587400062eb9e61b2a822a87d8718f655046d0ff0eb1cc12a03a5e21d50501200062f39eca3028400e1d7350d659002b47d03208c8a80030f19474581210043fc1ced2a24200c3f435da54840014eb03216caa00038754d43d9120004aec1ce9b2a42aca9d809d163100010fb0f31eca908021fa1e43596400243f42ceda0a4000e955350d61100014df04b1ecaa00021f61c3158254004ba43a82a8220abc5f30dcd65900010ff0ab96c0a0803590857
  | 18 => 0x4133cc8c3baa42900031d1db75505100061e3a6a6b122000e1d5350f615082bc38a9212c6201021fa1e61582540064e3a0e6b122000e99434c1618800b5b500392c6200029b60a41582540049f43a86b0aa000c3f8750d609500193909b9ac4880028760c54d912012e2f39ac6322a000e1f8350d659006b8d8e4b12c32a0030f1d774589100043fc3ac92a24201ae681991214806b4eb03b24a8908030f61f64991500062eb22e6322a00087e87d4f604842b4f10ca8680a00029d60420d95410043ec1eeab224000a3d840c9651000187ae6a1eca908d68f61070d95420043ec3ce7b2a820093e84ddb42540014db0430cc8a80029e600315825402c76416ec9088000b1d831536448001da262982c3100168f21941541400053ac0ce5b2a80ab87c86dcd61540014bb06386caa10121fe1f63d95210070eb1a87322a09bc6d72197644844f0fb0e31eca908029760c54592100052ec18a9b224200e2c8550d621002b878e9212cb0800e3720d76509100243f42cec90a8005a7486505504415347b0921acb081031dc41769521002c7a40eec9088000a3d840c365504018bce7b28c0a08029da06425944055c3f438e6b2c8025d1e7350f6254001c3aa6a1ec2900021fa1c755911002d3a43242a822000c6d729d764484010fd0db9ecaa08034bc8474589500053741062b04a800e1d5350d64440090ff0fb1ecaa08035908773d95210071ba9e86b08800087e87d41644400187e863b284a800317dcd43d954201e4e39a86b122000d1f7350d62950014db0b21ac4200021fa1c21d95400070ea1a61b2a42ab87e871cd658802bd33013a2c6200030fd8074585501243ec3ec7b12a015c3c7415162441574bf013aac6200925b20973591500045ec36e89088000c3f645ce645402b878e8322c2a800297a0c20d95410053ac0864322a025d1e7350f61540011df04b9ac9080021f21d53587400043fc3aa7b224000c747558521101356c90498eca908029ba0a6158254006b210ae7b2a420487c87d4d64480090f90fa82c8882970f1d543d81420051ec00a9b222015a3c844c8645400b1d90eb1243200021fa1c65581410064fb9a86b2240d3c757119460484018bae7318c8a82fedce0161485500ad4e422a2b188015a3e849cd609508147b0839ac12a0021f61f649511052e1e3aa86b224000c3f7350d60950490f90eb1ac4a8002ce60054d91200062fc1ae6b2c401587c87151624402b47d09108c8a80568fa1331594402343f436eaa0a8012af1801cd611002b8790fa1acb10056ada1273584400ae2e212e6322a00487c87591504800117f08b9ac4880030f50d7695220006d210ae8302423587e8790f655082b4d909a9ac4200578710d43582542043e43ac2b04a815a3e84cc0645402b56d0929ac220233a910864485100ae1e3a687b
  | 19 => 0x63b60b75d91210068eb22e6322a00087e870c5658802b0fd09b9ac12a097179cf63d855055f1ba06a6b08800487f80dcd658404b8bce6b1cc8a82a7874c14359440006b9ba8e090a2000c6c751d942481550fb0f39acb100570fe1f43596100043fc2ae9b12200087e87cc3654840193f09b9ac4880021fe1974485500053b408e4b288000b39801046454081878edb2a84a005727dcd43992100051ec2663b2a8434a76811c36550401878cb3b684a00166b21d42501200059cc00a83224000b2e8290764540494dd0520acb102669da0430d95210053cc00ca3024200ce5721c9611000187a873b4a8908925da1f41485500070fb9a87b2a4200c3c74d4162440014dd0b21ac4200028f61332191500053ac0c84b04a815a3e85d5064440014f3002a2c4880021fa1c30d95426e51f42087b2a4200c9f73d0d62440010fd0e2a6c0a10038798d439915011cb643ac490aa000c9f645ce644842b4ed0baa2c2200163da1f51584400070ea9a863224000c3e411d9415402b0f90fa1acb100561f21176952100ae2ea12e6322a00087d8790f65504010fb0e10ecba00030f50d70d95420ac3e438a9b02420087e87595421017547908b8acb200038754d435862069e3ab88cbb224200c3c611d1505008147b0838ac12a0028f60e41191500147b43ec290a8000c5f815cc64540014dd0a18ac42000e2fe1d43d912154e1fb8286b2c20ace1d509d1631002b87ce8a1eca908031b5ca62991500ae1fb9a86322a04687f87592548406d8b8e72a2c488003a594d43584400051f42665b2a8005ab48650540440015cd0da0a42902ce8f6127359440126373b6e4a824000d64219da54484014bd0a38ac620003475cc421915002e6d302e63024200e1d6350d625402b0fd0d3b4a8908021f61c31596400243e42eec90c8000c5e73196644842bc5d05210c8a800317dce43582540043ec3aa7b22400087e870c3654844b0fb0fb1ec8a80030fdd543591200ae4fa1ae7322422595e839d121540014bb062a6c0908030fdcd43d95210043f436e7b2a80028f581dcf644846b8d8e4b12c12a2b38dd4343584400052f41ce9b2a4200a798095360504018eae33aec8908570f9d064d89500052ec28e2b188000a3d84cc96584183ae6e3b82c2a80121f215735922000596422c490aa000d64219d3654846d0ff0ea1acb2008e1f61f645411002c7643a64b108000c3f75dd16244001c9aa721ac42000317dd563484400ae3d2a6eca008000c3d7350c64540472dd0fa1242a80021f21d43596200055ac0c843222000d3874dc1625402b8790fa1ac12a11b960c130191500045fc22eab0c4000a3f844c4645400147d0818acb200030f1d464501100043ec3a61b2a8400a7980d94605040147b0831eca90b928fa1073d95411a61e3b6eaa0a8002ae686d89214
  | 20 => 0xc01200400403800000000a00604a00000003c11c05a0460020a000000c05001d3760761e400201200208a0000000000160160b806e00000600000000200800002600200000401800602003801208804200800000600202200003806609001e00801a05c00606e0a200600c03c03400a01219200600a09e01203801000000402400000601203600800000001600c1060020780040c80aa03401c04200203002e00200e00804c0e40080041bc14803c0021160ae0060202b81d61800f002c02e0200160000420000660260ca07800400800600004e02a0186f005601c13605800c1e80040280200060060100000060020520080420460164d201000000e00200c09002e0000080160000be00c01606800400001c00a03c044000000060b6400e00000a00208e00400000200a03c01c02c00a0542fc00e00c00400400601800603a00c00001e3aa48000400e0040400560a600230400c19602000a00c03a06c01003200000600203a01610803c06a00001a00001400001e054002a6200001c04402403e00000614e1e005c00803200800002602c0380040000303da07a03803e0240000420087d8704365508010ff0eb1eca908163d21d31584400055bc22a4b08800093c8750d62540010ff00b9eca908561fa1f539922011db240ac490aa015ab780d0d61100010ff0ab9ac9080021f61e41594400062e398cab024200a3d8418e645400193ee6a1ac3a00d21fa1e42d95410ae2fc22e6322a00087e87cc965840014db04186caa1003175cd63982542071db26cba028000e1c6350f655014d878eba1ac5a00063ba1f62485400043fc2ae6b24400087d87cc965840010fd0e086caa10030fdd064585500063c42eeca008000a6d820c565880018bae6188c8a8003871cd43d954000556c2662b10800087f83dd9425400147f00a18c8a80029760c54589100070ea1e61b2a84158bc845d56188001cc84232242a8056ab21152588400053b40865b2a8000a3e84cc3655080187eeaa1ac8908021fe1571d81420056b40c84b18801ba3e849cf65500275d30039ac4200030fd83745855055e3ab8ea63222000c9f7350f60504014d90ab8ac4200021f61e41582540043f43aa6b242000e1d745d5631006b4eb033b4a8908568f61e41191500043f43c87b2a420087d8710d659002b47f06a1aca200029d61731584400043f43ea6b122015a6c865ca54480014f3002a6c4880561fa1f31191500062eb9e62322a00087e869d942540010fb0bba2c3100021fe15735911002c7643ac49088000a758190b65504010fd0f992cb20016ea20142501200061fb9a87b2a820487e85dd161880878dae42a6c890a9b0f1d743592200070e31a87b2a820487e87dd561d00090ff0fa9cc8908030fd9674181210051f40c84322a00087e87d4f60504018d8cab90c0a08
  | 21 => 0x3a1c202609401800000a05202000009e04602a0540b40180622c001200c00a02e00c0340000040060020020000020aa00203200203405e024012a3a05806000201e01000002000800000406a0680b40000007080320c601400800c05c06c01a00000000204601800600004a0300080023f804401600814602407801c00a01206606608e05c04205200000a00e0000dc0000480a826e04c00000005401002601400600002200c01402c00803007693801200028a00200005800000000022606a12c05007200600e00000094a03c01800a01400600a08a00a25200000400008007c00007601600000002006c80c0000740000000840000300820ce01a0b400642600400406003600003e06407805002affa00004a05e00600405000401a00000802a02028e01200803800000a03200000e00611e00a00602c00204400e04a0000120fc01000000000400801000005002a02201400403a13200832801c00e01402801000001e0120460220020d000c0000420b40000360b200200201e0d406a00808214e04800009e00c000006000000a761740ca01207601200e01401a00a0da06845401c00c00007a00007609800002000002c01400600c00201600200008c07003c0020360640000a000000200000405206801c01200201800000200a00a01c3fa00400002600000000006400006801400c0880060000a210402e02000609600000024204000203800400600407e00e00004000029e0080960100060028f600003222601e0043c601600c0281c00280380b200400000809200200e00600648802200a00a0080000a409603202a0040a00100040000000780121b200a00000e00002800004e20e00006606e01e000000036048050000028144036000004002014016000a4003403a02607403600000401c00200a00017603a00001c00806a00000001800c0d80aa00004006604a00203400407802c01000405e06c00c09c0400000520081e606203000200000001a0ca0b619a0f201e0a002201000001002a00003c09401207000000801600001201204a00008606c00c0000240560660a600002e0284b407c02602400e01e04a0020000143360180028740e402609000c02a04204601403a00001200400001407411401600001003c00005a00a04c04206c0040820c00000060280320ea05200a37a01a14601001a03a20e01c0000000081ce01200400203406c00e03800608c00000a02e05600400001200000e06a09800203000605800408600400000406001405a00e01602601c00a28400009c00000800c01a00001200001400829800206001a02203e00600c00000201001601c00605a00005600600819816600000a0120d005c0ae01a00004c01c00013800201a00a00000601a04609c01607401400600001600000000c00000000000c1a001200209
  | 22 => 0xa200401809818e03202e0200021e200000003e00400202e03e00200000e0080540420080360a200000400000018800a0f206404a00400e04200078800400204802600800000204e00403400000406a00000e0800740020a608204a
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2b41c94a0573191500ae07e0d7350f65d0001c15736064219150007035cd82904645400121d93a1365d912100499660211d9215400151990a11731915000459660215d6644840181d8760c54d91100ad07a637350f655000141c9754d4359121006135ce82184645402b41c94609731915000516640825cc645400181e8750f30d954200507a5d5350d61d002b41e94d8173191500ae071d183151624400105f985cc73582540050764c7458d615400181d985ce421915000607a1d5350d624400181e7660c54191100050764c54dcf644402b81c985d17558c4046619609819da544840141d9420173191507650765e7350d658802b81e845cc611915000516a40825cc645400191573a06421915000516640815cc645400181e8758d43589507650765e7350d658402b81e845cc3219150007035ce82904645419782f73a0a41191500050764c74d91504400141e9754d43591200ae0721173c80645400141d93d917399150005076437350f654840181d845cc6319150005466437350e6454197a0e73a0a41191504668310983191215400184d73608311915000513648805cc645400141e9754d4358b40006075d1831936154001266980876548540004cc2614154140441d5c0d7254d4319120006075d183193625400141d948817319150005866407350f654842b81e845ce2119150006075d183153625042b91b6060c745414000516640655cc604840105d9804173191500ad852615350d611002b82e8261e421915046689a0582904645400181f7460c545891000607611738846454001c0d7390b20191500050764e85dd1624400181d73a0642191500ae072117308464540078c8874c9305891000616a01730c8645400181e7660c54191200ae07a117398e645402b41c98dcd43d954000549654219d0604840181d73205431915000507a5d5350d648802b03c9461c21594400ad07a5d5350e648800141d931d153589100060760c621d15050001a248458961485500050e640411d9415400181f8350d70d952100549654215d0604840141d931d364541207650765e7350d659000181d865ce41191500050b249631d1505000123691e12321915000515a44205cc645402b81e845cf30191500060760e611d1505002b81e845cd30191500ac172617354c644842b81e7460c74596200060760d631d1505000181d7460c54d854200607e0d43dd9215400144d92041731915000607dd183191215400181d73a0a41191500ae079d1831d165840078988750d30589100ac872615350c644400181d845cf21191500050764e749da544800181d7560c54d9110006155ce810c8645400141c9754d43d81210ae07a0973908645402b41e94e01731915000459a6021dd5644842b05c985cd43596200ae07e0d7350c645400181d845cc3119150
  | 1 => 0xad07252825cc64540018598020173191500064360e421d15048001465950877648440006155cd81188645400105e9804173191500ac17a637350f655000141d9754d43991210ac17261745d563101d5c157154d4319110005866406350f654842b41e9488173191500050764c75d934048195a1454a064258c400ad07a5d5350c644859583474a064259440006075d583153644802b81c7460c64485500041725d83151624400191973600421915000607e1784dcd62440011669808775581210ac8725185085631002b81c845cd32191500050ba4a611d15050001c1573a06421915000619609811d9215402b41e948c17319150006075cd80904645400145591209731915000706dcc8050d60950019537560c7048510006155cd810c864540014989750d3058910006165cd800c464540011669808773d95210ae07a117398c645400190d73a0a411915078f035c95350f644840141d9315373d91200058925162585215402b41e94841731915000507a5c7350f6550195a1573a064219150006135ce820c4645402b41c94605731915000619615721c9611002b81c7460c645855000515a44305cc645402b81c845cd311915000513a48815cc645402b41c985cd43596100050764e749da544400181573a06421915000607dd183151618802b43a94d4f76500400ad07a53825cc645400145591081731915000459660215d46048447264985896148550006155ce81188645402b81c7460c54586200ae07211738c4645400126595a1b414852046499a6021d9521d01191669808476951210064a5c98010864541d960d9054d435884000516a40815cc64541d960f9054d43588400060d2047458d615400142d92184745855000507650105cc645402b22c9461471588400ae07191839d36548401266980877648550006465cd80104645400184d7360861191500ae071d1839d3654840122e92e1231191500065160c219d3654851990c4260e74d952100607611730c8645400181d9760c54d911000515a44805cc645400181d84dcf305825446459660219da544840181f845cd32191500050b249431d9425400181f8350f76505500ac952615350d611000144d9220573191500ae07a1173cc365d000181d83988745414000594640634c7654840181d865ce42191500ac172617354e64840012659808464485500ae079d9831d1505000181d8350c765095075d866427350d658411984d7260c54d912100570640215cc604840181f8350d70d954100607661739046454001c19435c130d95210ae07a1173cc8645400144e9204173191500060b5ce8290464540011669808573d9521006165cd8018f6548401d0421dcd43d95210ae07a617350c64540014559120173191500050764c7458d625400141d9754d43d911000507a5d5350d6444
  | 2 => 0x402b81e845cc62191500ae07e1973108645400181d8760c54d912000549654211d1604840141d9484173191500ae079d1831936154001a4583084644855000507a5d5350d648400181d8750f301915000507a5c7350d609500143591188745895000459a60215c254484078d0874c5305891000507a5c7350f655040181d8318474541400060761173cc0645400141e971cd43d952100515a44825cc645400105e9815373589100060760f631d1505002b21c9854d431912000515644305cc645400181e8750f30d954165e831528290563101d96179054d4358440006165cd800c8645400181e8750c43d9540765856415350d611002bc0e825ce42191500055165421dcd604840181f845cc21191500050765d5350f64484011659808674d95210ad07a50305cc645400181f8350f7650950656859ce81908645400141f9754d43991210ac172617350d658419782c74a0a41594400049965686d0921440015459508573991210ad072637350d6095119a144160c64485500ae07191831d15048001328985095050120005916542158d2110001c1b73e01435825400507650205cc645400194b7560c7048520006075cc8250c645400105e98081731915065e835ce8290464540015259508774581210060b2087458d625400181d8350c76485500ad072617350d658802b81c7460c64589500ad832615350d621002b81c845ce321915000546642645cc64540015459508573181210ae07d81831d1505000181e8758d4358550006035ce82904645400105d98081731915000607a59831d1505002b81e7460c64d89500ad07a637350d609500181d845ce63191500ad07a5d5350e648402b41d90dcd43d9540005076437350f655080141d9754d43d9120005076437350f655042b41e9420573191500050764c545cf644800741d945cd53191100ad07a637350f654842b81e845cf2119150006075cd80908645400141d931d764d01100ac1e25d8015162440016499018d32d95210ac172617354e648802b81e845cf63191507560761d759d163100015a190085741812100607dd1831916154001865855c471588400ac17a637350f654840144d920c1731915000607e11738c8645402b60e9854d4358840466155c58315364484014399019574181217760761d434c0645400181d9760c54d91200af05a057390464540011669808570d95214658925021191215400141d9798d4319150006075cf8050c645400151b90591731915000507652805cc645400143990108765095000516643655cc604840141e971cd43d95420049966021595219000181f845cd31191500ae0721173c40645400181c8754d43589100064560e411d15044001c1573907101915000507a5b7350f65484014369198874541400050725d5350d6244195c14415ce211915
  | 3 => 0x42a050000c124c3883004000300c1c0402230033c0000c720001800100208804005306014000402078440b020003608050142600320000c020000002004980012130413400010015c3c0603848280b208204a020000014000101002371a804163401810000505004002004010000402034445120000100000460040300810020e2709c00000183006000008c32060101802000a815620501b980002000080a0d0000040150105008030382c083b27800800a12868001d00004000101098000903810000200034100406804103c04004120c09834000100519654215d9211000116598085759812152507e417350d658402b81e845cc63191500ad07a50205cc645402b81c6460c74541100060d5ce81908645402b81f985d17558c4000558640215c2544840181f7460c5458a1000607a1d43cc3655000181d8350e769512100507a5d5350d644842b24c9854d435884012d076417350d658402b41e94209731915000507a5d5350d624402b41e9404173191500ac17a62305cc645400181f865cd43191500ae07a0573904645400181d835ce42191500ad85a615350d61100014349158c74541400ae071d183151628400181e8750f30d952100607e11738c4645419583773a0642191500060761173cc864541195249408674d95210ae07e197310464541199144160e74d95210ac8d251851c9611002b81e845cf31191500050764c545cf64440011659808575d912177d07e417350c645400185a805cc31191500060761173cc4645400181f7460c645895000513a48305cc645402b41e94e05731915000607e0d435c3655080181d835ce411915065f0310973c84645402b81e845cc311915000607e0d435da54881db619909cd4359620787055c55350f644840144e92201731915046689a0981908645400126598085654844000607e0d435da548400181d8350c76505500050d245431d9415
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x9a29e280c824a60000020002008c84929198085759912100504b44408e8b1ac2a800305191600805cc6454001806c99043a2c6b12a0cba03a8b845cc211915000501d45c22e7188c8a8002429a0249431d94254001218d0122a18eca0aa08c98129195085634844046484948ca842bb24220232126a4a60215cf654840180ac1d23310e8a82808c84929198085759812100502d43c22e7190c8a8002506a90877350f65485199024a306108c890aa08ce01a0973606421915000602b0648ac63a2a0a0003015932047458d615400180ac1922a18eca0aa000c1264980201731915000601b07494c23a2a0a0232824a4615721c96110001412d09043a2c6b12a000c0360c9258c745414046700d02b9b05208c8a8232824a4615711c562101198824a30610ce9b2a428c889a92980877648550464a0948ca842b9cc890b2a816a1e117308464541190935253010ee7b2a428c889291980856548440
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x100464106b8aa421dcd43d952100600593688811d1635855000600593684821d16358950006011836809150c7650550
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94b
  | 7 => 0x94c
  | 8 => 0x94e
  | 9 => 0x124c
  | 10 => 0x124b
  | 11 => 0x124e
  | 12 => 0x98a
  | 13 => 0x98c
  | 14 => 0x98e
  | 15 => 0x128c
  | 16 => 0x128a
  | 17 => 0x128e
  | 18 => 0x10a
  | 19 => 0x10b
  | 20 => 0x10c
  | 21 => 0x5
  | 22 => 0x10e
  | 23 => 0x180c
  | 24 => 0xa0a
  | 25 => 0xa0b
  | 26 => 0xa0c
  | 27 => 0xa0e
  | 28 => 0x130a
  | 29 => 0x130b
  | 30 => 0x130c
  | 31 => 0x130e
  | 32 => 0x180a
  | 33 => 0x180b
  | 34 => 0x180e
  | 35 => 0xa4a
  | 36 => 0xa4b
  | 37 => 0xa4c
  | 38 => 0xb0c
  | 39 => 0xb0e
  | 40 => 0xb8b
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x184b
  | 44 => 0x184c
  | 45 => 0x184e
  | 46 => 0xd0a
  | 47 => 0xd0c
  | 48 => 0xd0e
  | 49 => 0x188a
  | 50 => 0x188c
  | 51 => 0x188e
  | 52 => 0x194a
  | 53 => 0x194b
  | 54 => 0x194c
  | 55 => 0xa4954
  | 56 => 0x94a54
  | 57 => 0xb0954
  | 58 => 0xb0956
  | 59 => 0x94b14
  | 60 => 0xb8954
  | 61 => 0xb8956
  | 62 => 0x94b94
  | 63 => 0x150a
  | 64 => 0x1949
  | 65 => 0x194954
  | 66 => 0x95954
  | 67 => 0x74a
  | 68 => 0x195254
  | 69 => 0x125954
  | 70 => 0x749
  | 71 => 0xa4994
  | 72 => 0x98a54
  | 73 => 0xb0994
  | 74 => 0xb0996
  | 75 => 0x98b14
  | 76 => 0x138b
  | 77 => 0xd0994
  | 78 => 0xd0996
  | 79 => 0x98d14
  | 80 => 0x194994
  | 81 => 0x99954
  | 82 => 0x74b
  | 83 => 0x195294
  | 84 => 0x129954
  | 85 => 0xa0114
  | 86 => 0xa0116
  | 87 => 0x180a14
  | 88 => 0x180a16
  | 89 => 0xa4a14
  | 90 => 0xa0a54
  | 91 => 0xb8a16
  | 92 => 0xb8a14
  | 93 => 0xa0b94
  | 94 => 0x184a16
  | 95 => 0x184a14
  | 96 => 0xa1854
  | 97 => 0xd0a16
  | 98 => 0xd0a14
  | 99 => 0xa0d14
  | 100 => 0x188a16
  | 101 => 0x188a14
  | 102 => 0xa1894
  | 103 => 0x194a14
  | 104 => 0xa1954
  | 105 => 0x181314
  | 106 => 0x181316
  | 107 => 0x195314
  | 108 => 0x131954
  | 109 => 0xa5814
  | 110 => 0x180a54
  | 111 => 0xb9816
  | 112 => 0xb9814
  | 113 => 0x180b94
  | 114 => 0x185816
  | 115 => 0x185814
  | 116 => 0x181854
  | 117 => 0xd1816
  | 118 => 0xd1814
  | 119 => 0x180d14
  | 120 => 0x189816
  | 121 => 0x189814
  | 122 => 0x181894
  | 123 => 0x198a
  | 124 => 0xb0a54
  | 125 => 0xa4b14
  | 126 => 0xb8a54
  | 127 => 0xa4b94
  | 128 => 0x184a54
  | 129 => 0xa5854
  | 130 => 0x138e
  | 131 => 0x198b
  | 132 => 0xd0a54
  | 133 => 0xa4d14
  | 134 => 0x188a54
  | 135 => 0xa5894
  | 136 => 0x150e
  | 137 => 0x8a
  | 138 => 0x184b16
  | 139 => 0x184b14
  | 140 => 0xb0d
  | 141 => 0xb1854
  | 142 => 0xb1856
  | 143 => 0x188b16
  | 144 => 0x188b14
  | 145 => 0xb1894
  | 146 => 0xb1896
  | 147 => 0x194b14
  | 148 => 0xb1954
  | 149 => 0x40a
  | 150 => 0x28b
  | 151 => 0x160a
  | 152 => 0x148b
  | 153 => 0x164a
  | 154 => 0x14cb
  | 155 => 0x44a
  | 156 => 0x184b96
  | 157 => 0x184b94
  | 158 => 0x194b94
  | 159 => 0xb9954
  | 160 => 0x188d16
  | 161 => 0x188d14
  | 162 => 0x194d14
  | 163 => 0xd1954
  | 164 => 0x198c
  | 165 => 0xe8e
  | 166 => 0x18ce
  | 167 => 0x74c
  | 168 => 0x130752
  | 169 => 0xe89
  | 170 => 0xec9
  | 171 => 0x1a49
  | 172 => 0x18c9
  | 173 => 0x1249d6
  | 174 => 0x130753
  | 175 => 0x1289d6
  | 176 => 0x11496
  | 177 => 0x11616
  | 178 => 0xe8116
  | 179 => 0x10e96
  | 180 => 0x131816
  | 181 => 0xa1856
  | 182 => 0xa1896
  | 183 => 0xa18d6
  | 184 => 0xe8a16
  | 185 => 0xa0e96
  | 186 => 0x130296
  | 187 => 0x130416
  | 188 => 0x1318d6
  | 189 => 0x4e
  | 190 => 0x8e
  | 191 => 0xb1396
  | 192 => 0xb1516
  | 193 => 0x139256
  | 194 => 0xe9396
  | 195 => 0x18d396
  | 196 => 0x151296
  | 197 => 0xe9516
  | 198 => 0x18d516
  | 199 => 0xe8a53
  | 200 => 0x18ca53
  | 201 => 0x9ce
  | 202 => 0x140d
  | 203 => 0x154d
  | 204 => 0x168e
  | 205 => 0x11816
  | 206 => 0x10a16
  | 207 => 0xe9816
  | 208 => 0x18d816
  | 209 => 0x18ca16
  | 210 => 0x130a16
  | 211 => 0x2cb
  | 212 => 0xe8b
  | 213 => 0xe8a
  | 214 => 0x18cb
  | 215 => 0x18ca
  | 216 => 0xecb
  | 217 => 0xeca
  | 218 => 0x1a4b
  | 219 => 0x1a4a
  | 220 => 0x1658d2
  | 221 => 0x164e92
  | 222 => 0xe9652
  | 223 => 0x18d652
  | 224 => 0x75312
  | 225 => 0xb8416
  | 226 => 0x1958d2
  | 227 => 0x194e92
  | 228 => 0xb98d6
  | 229 => 0x75313
  | 230 => 0xd0296
  | 231 => 0x1958d3
  | 232 => 0x194e93
  | 233 => 0xd18d6
  | 234 => 0xece91
  | 235 => 0xe9249de
  | 236 => 0xe8ed1
  | 237 => 0xe9289de
  | 238 => 0xe89d6
  | 239 => 0xe9696
  | 240 => 0xece93
  | 241 => 0xece92
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 68
  | 7 => 1444
  | 6 => 3924
  | 5 => 2859
  | 4 => 406
  | 3 => 33
  | 2 => 4
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/43+packedAt gbK8 (1768+(h % 43)*7) 7) % 68)
  | 7 => 2*((h/488+packedAt gbK7 (53428+(h % 488)*11) 11) % 1444)
  | 6 => 2*((h/1315+packedAt gbK6 (188352+(h % 1315)*12) 12) % 3924)
  | 5 => 2*((h/1023+packedAt gbK5 (168681+(h % 1023)*12) 12) % 2859)
  | 4 => 2*((h/191+packedAt gbK4 (28420+(h % 191)*9) 9) % 406)
  | 3 => 2*((h/18+packedAt gbK3 (2673+(h % 18)*6) 6) % 33)
  | 2 => 2*((h/8+packedAt gbK2 (368+(h % 8)*2) 2) % 4)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0ffff0c30fe1fff0e0703ffff20307f08f07f
  | 1 => 0xff0f0ff03f0fe381f007fc3c1f51c993374993
  | 2 => 0xff0ffc00ffc01fff8003fe09e0e1cc78e1c
  | 3 => 0xfff000fffff00001ffffffc000e00fe0f80fe0
  | 4 => 0xfffffffffe0000000000fff000fff000
  | 5 => 0xffffff00000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x20121100001004a00201010508001025001025
  | 1 => 0x49058a3011072105901258285610c892134892
  | 2 => 0x809a854400b4809a4b00832c2160a18458a18
  | 3 => 0x92a0008aaaa000104944a28000e00540a80540
  | 4 => 0x108000ef3ccc925c0060308084eb6000fee000
  | 5 => 0xfccecc02088100608180c32318fdbfff000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36360
namespace PEqualNP.Outside.L_meta_36360
open PEqualNP.Outside.L_meta_36360.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := bs1_5_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 56 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 781 := (concat (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 bs3_4_288)) (concat (concat bs3_4_384 bs3_4_480) (concat bs3_4_576 (concat bs3_4_672 bs3_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 801 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 bs3_5_288)) (concat (concat bs3_5_384 bs3_5_480) (concat bs3_5_576 (concat bs3_5_672 bs3_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 1 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 5 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
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
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 712 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 bs5_4_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 63 := block_range (n:=63) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 735 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 bs5_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := bs5_6_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 33 := block_range (n:=33) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 33 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 406 := (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 (concat bgb_4_288 bgb_4_384)))
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
theorem bgb_5_2592 : Interval gbAtlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 75 := block_range (n:=75) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2859 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat (concat bgb_5_672 bgb_5_768) (concat bgb_5_864 bgb_5_960)) (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 bgb_5_1344)))) (concat (concat (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632)) (concat (concat bgb_5_1728 bgb_5_1824) (concat bgb_5_1920 bgb_5_2016))) (concat (concat (concat bgb_5_2112 bgb_5_2208) (concat bgb_5_2304 bgb_5_2400)) (concat (concat bgb_5_2496 bgb_5_2592) (concat bgb_5_2688 bgb_5_2784)))))
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
theorem bgb_6_3840 : Interval gbAtlas 6 3840 84 := block_range (n:=84) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3924 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_2016) (concat bgb_6_2112 (concat bgb_6_2208 bgb_6_2304))) (concat (concat bgb_6_2400 bgb_6_2496) (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784)))) (concat (concat (concat bgb_6_2880 bgb_6_2976) (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264))) (concat (concat bgb_6_3360 (concat bgb_6_3456 bgb_6_3552)) (concat bgb_6_3648 (concat bgb_6_3744 bgb_6_3840))))))
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
theorem bgb_7_1440 : Interval gbAtlas 7 1440 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1444 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672))) (concat (concat (concat bgb_7_768 bgb_7_864) (concat bgb_7_960 bgb_7_1056)) (concat (concat bgb_7_1152 bgb_7_1248) (concat bgb_7_1344 bgb_7_1440))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 68 := block_range (n:=68) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 68 := bgb_8_0
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8fefefea8feeafea8
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
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124200 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36360.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[3,4]⟩,⟨.or,[6,7]⟩,⟨.and,[0,8]⟩,⟨.and,[6,7]⟩,⟨.or,[9,10]⟩,⟨.or,[3,9]⟩,⟨.and,[1,2]⟩,⟨.or,[12,13]⟩,⟨.or,[5,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36360

open PEqualNP.Outside.L_meta_36360 in
theorem PEqualNP.Outside.L_meta_36360 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
